(* invariants:
   - A. a node downstream of an invalid node is invalid
   - B. a node upstream of a valid node is valid (except for Tracking nodes)

   assumptions:
   - 1. in an expression [bind m f], the set of nodes X created during any evaluation of
        [f] is upstream of the result of the evaluation of [f] and any element of
        X is reachable through X by following upstream links
        -> this rules out a lot of weird graphs that could be constructed using mutability,
           and allows a very simple GC algorithm
*)

(* TODO:

   we use type `ex list` for [used_by], this is not very structured and not
   very efficient (cf the calls to `List.filter` to remove an element)
   - we could use a set or a hashtbl?
   - we could unroll `List.filter` on a dedicated list type (typically a node
     will not be used in many contexts so [used_by] should be small)
*)

module Counter = struct
  let gen =
    let x = ref 0 in
    fun () ->
      let v = !x in
      incr x ;
      v
end

module Int_table = Hashtbl.Make (struct
  type t = int

  let hash = Hashtbl.hash

  let equal = Int.equal
end)

type 'a t =
  { desc : 'a desc;
    uid : int;
    tag : string;
    mutable value : 'a option;
    mutable used_by : ex list;
    mutable watchers : ('a -> unit) list
  }

and 'a desc =
  | Return : 'a -> 'a desc
  | Var : { mutable v : 'a } -> 'a desc
  | Gen : { gen : unit -> 'a } -> 'a desc
  | Tracking : { x : 'a t; mutable v : 'a } -> 'a desc
  | Map : { x : 'a t; f : 'a -> 'b } -> 'b desc
  | Map2 : { x : 'a t; y : 'b t; f : 'a -> 'b -> 'c } -> 'c desc
  | Map3 : { x : 'a t; y : 'b t; z : 'c t; f : 'a -> 'b -> 'c -> 'd } -> 'd desc
  | Map_array : { xs : 'a t array; f : 'a array -> 'b } -> 'b desc
  | Bind :
      { m : 'a t;
        f : 'a -> 'b t;
        mutable currently_allocated : (int * int * 'b t) option
      }
      -> 'b desc
  | If :
      { cond : bool t; iftrue : 'a t; iffalse : 'a t; mutable dyn : ex option }
      -> 'a desc

and ex = Ex : 'a t -> ex [@@unboxed]

type undo_info =
  { mutable prev_values : (ex * Obj.t) list;
    mutable prev_used_by : (ex * ex list) list;
    mutable prev_currently_allocated : (ex * Obj.t) list;
    mutable prev_cond : (ex * ex list * ex list * ex option) list;
    mutable prev_vars : (ex * Obj.t) list
  }

let ex node = Ex node

let debug = ref false

let next_debug_info = ref None

let tag : type a. int -> a desc -> string =
  let open Format in
  fun uid desc ->
    if !debug then
      let debug_info =
        match !next_debug_info with
        | None -> ""
        | Some s ->
            next_debug_info := None ;
            asprintf " [%s]" s
      in
      match desc with
      | Return _ -> asprintf "return (%d)%s" uid debug_info
      | Var _ -> asprintf "var (%d)%s" uid debug_info
      | Tracking _ -> asprintf "tracking (%d)%s" uid debug_info
      | Map _ -> asprintf "map (%d)%s" uid debug_info
      | Map2 _ -> asprintf "map2 (%d)%s" uid debug_info
      | Map3 _ -> asprintf "map3 (%d)%s" uid debug_info
      | Map_array _ -> asprintf "map_array (%d)%s" uid debug_info
      | Bind _ -> asprintf "bind (%d)%s" uid debug_info
      | If _ -> asprintf "if (%d)%s" uid debug_info
      | Gen _ -> asprintf "gen (%d)%s" uid debug_info
    else ""

let make desc =
  let uid = Counter.gen () in
  let tag = tag uid desc in
  { desc; uid; tag; value = None; used_by = []; watchers = [] }

let var x = x

let gen x = x

let rec invalidate : type a. ?u:undo_info -> a t -> unit =
 fun ?u node ->
  match node.value with
  | None ->
      (* node is invalid, by invariant A all nodes downstream are already invalid *)
      ()
  | Some _ ->
      (match u with
      | None -> ()
      | Some undo_info -> (
          undo_info.prev_values <-
            (ex node, Obj.repr node.value) :: undo_info.prev_values ;
          match node.desc with
          | Tracking { v; _ } ->
              undo_info.prev_vars <-
                (ex node, Obj.repr v) :: undo_info.prev_vars
          | _ -> ())) ;
      node.value <- None ;
      List.iter (fun (Ex n) -> invalidate ?u n) node.used_by

let add_used_by usee user = usee.used_by <- user :: usee.used_by

let return x = make (Return x)

(* TODO: smart constructors (eg when input is Return ...)*)

let map x f =
  let node = make (Map { x; f }) in
  add_used_by x (ex node) ;
  node

let map2 x y f =
  let node = make (Map2 { x; y; f }) in
  let ex = ex node in
  add_used_by x ex ;
  add_used_by y ex ;
  node

let map3 x y z f =
  let node = make (Map3 { x; y; z; f }) in
  let ex = ex node in
  add_used_by x ex ;
  add_used_by y ex ;
  add_used_by z ex ;
  node

let map_array xs f =
  let node = make (Map_array { xs; f }) in
  let ex = ex node in
  Array.iter (fun x -> add_used_by x ex) xs ;
  node

let bind m f =
  let node = make (Bind { m; f; currently_allocated = None }) in
  add_used_by m (ex node) ;
  node

let if_ cond iftrue iffalse =
  let node = make (If { cond; iftrue; iffalse; dyn = None }) in
  add_used_by cond (ex node) ;
  node

let on_update node f = node.watchers <- f :: node.watchers

let disconnect ?u (low, high, root) =
  let rec loop low hi (Ex node) =
    let uid = node.uid in
    if low < uid && uid < hi then
      match node.desc with
      | Map { x; _ } -> loop low hi (ex x)
      | Map2 { x; y; _ } ->
          loop low hi (ex x) ;
          loop low hi (ex y)
      | Map3 { x; y; z; _ } ->
          loop low hi (ex x) ;
          loop low hi (ex y) ;
          loop low hi (ex z)
      | Map_array { xs; _ } -> Array.iter (fun x -> loop low hi (ex x)) xs
      | Bind { m; currently_allocated; _ } -> (
          match currently_allocated with
          | None -> loop low hi (ex m)
          | Some (_low', _hi', dyn) ->
              (* Nested bind: we have the invariant that [low'; hi'] is included in [low;high].
                 We could recurse on [dyn] using [low';hi'] but that could add useless work
                 to the [u] record. *)
              loop low hi (ex m) ;
              loop low hi (ex dyn))
      | If { cond; dyn; _ } ->
          loop low hi (ex cond) ;
          Option.iter (fun dyn -> loop low hi dyn) dyn
      | Tracking { x; _ } -> loop low hi (ex x)
      | Return _ | Var _ | Gen _ -> ()
    else
      let () =
        (* This [node] is referred to by the body of the [bind] node but
           was created outside. If we undo this call to [disconnect], we
           need to re-establish its neighbourhood. *)
        match u with
        | None -> ()
        | Some undo_info ->
            undo_info.prev_used_by <-
              (ex node, node.used_by) :: undo_info.prev_used_by
      in
      let used_by =
        List.filter
          (fun (Ex node) ->
            let uid = node.uid in
            not (low < uid && uid < hi))
          node.used_by
      in
      node.used_by <- used_by
  in
  loop low high root

let refresh : type a. ?u:undo_info -> a t -> a =
 fun ?u node ->
  let rec loop : type a. ?u:undo_info -> a t -> a =
   fun ?u node ->
    match node.value with
    | Some v -> v
    | None ->
        let v =
          match node.desc with
          | Return v ->
              node.value <- Some v ;
              v
          | Var { v } ->
              node.value <- Some v ;
              v
          | Tracking { x; v = _ } ->
              let v = loop ?u x in
              node.value <- Some v ;
              v
          | Gen { gen } ->
              let v = gen () in
              node.value <- Some v ;
              v
          | Map { x; f } ->
              let x = loop ?u x in
              let v = f x in
              node.value <- Some v ;
              v
          | Map2 { x; y; f } ->
              let x = loop ?u x in
              let y = loop ?u y in
              let v = f x y in
              node.value <- Some v ;
              v
          | Map3 { x; y; z; f } ->
              let x = loop ?u x in
              let y = loop ?u y in
              let z = loop ?u z in
              let v = f x y z in
              node.value <- Some v ;
              v
          | Map_array { xs; f } ->
              let xs = Array.map (fun x -> loop ?u x) xs in
              let v = f xs in
              node.value <- Some v ;
              v
          | Bind ({ m; f; currently_allocated } as bind_state) -> (
              match (m.value, currently_allocated) with
              | (Some _, Some (_, _, dyn)) ->
                  (* [m] has not been invalidated: no need to re-evaluate [f] *)
                  let v = loop ?u dyn in
                  node.value <- Some v ;
                  v
              | (Some _, None) | (None, _) ->
                  (* TODO: should we ensure that [currently_allocated] is never None? *)
                  (match currently_allocated with
                  | None -> ()
                  | Some (low, hi, dyn) ->
                      (match u with
                      | None -> ()
                      | Some undo_info ->
                          undo_info.prev_currently_allocated <-
                            (ex node, Obj.repr currently_allocated)
                            :: undo_info.prev_currently_allocated) ;
                      disconnect ?u (low, hi, Ex dyn)) ;
                  let m = loop ?u m in
                  let low = Counter.gen () in
                  let dyn = f m in
                  (* evaluating [loop ?u dyn] in between the [low;high] ensures that
                     the brackets for sub-binds are included in this interval. *)
                  let v = loop ?u dyn in
                  let high = Counter.gen () in
                  add_used_by dyn (ex node) ;
                  bind_state.currently_allocated <- Some (low, high, dyn) ;

                  node.value <- Some v ;
                  v)
          | If ({ cond; iftrue; iffalse; dyn } as cond_state) -> (
              (match u with
              | None -> ()
              | Some undo_info ->
                  undo_info.prev_cond <-
                    (ex node, iftrue.used_by, iffalse.used_by, dyn)
                    :: undo_info.prev_cond) ;

              (* TODO should we make it so that [dyn] is never [None]? *)
              (match dyn with
              | None -> ()
              | Some (Ex active_branch) ->
                  (* remove [node] from [active_branch.used_by] *)
                  let used_by =
                    List.filter
                      (fun (Ex node') -> node'.uid <> node.uid)
                      active_branch.used_by
                  in
                  active_branch.used_by <- used_by) ;
              let cond = loop ?u cond in
              match cond with
              | true ->
                  cond_state.dyn <- Some (ex iftrue) ;
                  let v = loop ?u iftrue in
                  node.value <- Some v ;
                  add_used_by iftrue (ex node) ;
                  v
              | false ->
                  cond_state.dyn <- Some (ex iffalse) ;
                  let v = loop ?u iffalse in
                  node.value <- Some v ;
                  add_used_by iffalse (ex node) ;
                  v)
        in
        List.iter (fun watcher -> watcher v) node.watchers ;
        v
  in
  loop ?u node

let get ?u node = refresh ?u node

let undo (u : undo_info) =
  ListLabels.iter u.prev_vars ~f:(function (Ex var, v) ->
      (match var.desc with
      | Var payload -> payload.v <- Obj.obj v
      | Tracking payload -> payload.v <- Obj.obj v
      | _ -> assert false)) ;
  List.iter (fun (Ex node, v) -> node.value <- Obj.obj v) u.prev_values ;
  List.iter (fun (Ex node, used_by) -> node.used_by <- used_by) u.prev_used_by ;
  List.iter
    (fun (Ex node, currently_allocated) ->
      match node.desc with
      | Bind payload ->
          payload.currently_allocated <- Obj.obj currently_allocated
      | _ -> assert false)
    u.prev_currently_allocated ;
  List.iter
    (fun (Ex node, iftrue_used_by, iffalse_used_by, dyn) ->
      match node.desc with
      | If payload ->
          payload.iftrue.used_by <- iftrue_used_by ;
          payload.iffalse.used_by <- iffalse_used_by ;
          payload.dyn <- dyn
      | _ -> assert false)
    u.prev_cond

module Var = struct
  type nonrec 'a t = 'a t

  let create v = make (Var { v })

  let create_tracking x =
    let v = get x in
    let res = make (Tracking { x; v }) in
    add_used_by x (ex res) ;
    res

  let peek var =
    match var.desc with
    | Var var -> var.v
    | Tracking var -> var.v
    | _ -> assert false

  let set var x =
    invalidate var ;
    match var.desc with
    | Var var -> var.v <- x
    | Tracking payload ->
        payload.v <- x ;
        var.value <- Some x
    | _ -> assert false

  let set_with_undo var x =
    match var.desc with
    | Var ({ v } as payload) ->
        let u =
          { prev_values = [];
            prev_used_by = [];
            prev_currently_allocated = [];
            prev_cond = [];
            prev_vars = [(ex var, Obj.repr v)]
          }
        in
        payload.v <- x ;
        invalidate ~u var ;
        u
    | Tracking ({ v; x = _ } as payload) ->
        (* code identical to the [Var] case, can't be shared *)
        let u =
          { prev_values = [];
            prev_used_by = [];
            prev_currently_allocated = [];
            prev_cond = [];
            prev_vars = [(ex var, Obj.repr v)]
          }
        in
        payload.v <- x ;
        invalidate ~u var ;
        (* This breaks the property that ancestors of a valid node are valid. It is ok. *)
        var.value <- Some x ;
        u
    | _ -> assert false
end

module Gen = struct
  type nonrec 'a t = 'a t

  let create gen = make (Gen { gen })

  let touch gen_node = invalidate gen_node
end

module Infix = struct
  let ( let* ) = bind

  let ( let+ ) = map

  let ( and+ ) m m' = map2 m m' (fun x y -> (x, y))

  let ( >>= ) m f = bind m f

  let ( >|= ) = map
end

module Internal = struct
  type mode = Backward_only | Full

  module Node_ex = struct
    type t = ex

    let compare (Ex n1) (Ex n2) = Int.compare n1.uid n2.uid

    let equal (Ex n1) (Ex n2) = Int.equal n1.uid n2.uid

    let hash (Ex n) = n.uid
  end

  module Node_set = Set.Make (Node_ex)
  module Node_table = Hashtbl.Make (Node_ex)

  type edge = Dependency of ex | Dynamic of ex

  type graph = edge list Node_table.t

  let set_debug b = debug := b

  let uid (Ex n) = n.uid

  let iter_upstream (Ex n) f =
    match n.desc with
    | Return _ -> ()
    | Var _ -> ()
    | Tracking { x; _ } -> f (ex x)
    | Map { x; _ } -> f (ex x)
    | Map2 { x; y; _ } ->
        f (ex x) ;
        f (ex y)
    | Map3 { x; y; z; _ } ->
        f (ex x) ;
        f (ex y) ;
        f (ex z)
    | Map_array { xs; _ } -> Array.iter (fun x -> f (ex x)) xs
    | Bind { m; _ } -> f (ex m)
    | If { cond; iftrue; iffalse; _ } ->
        f (ex cond) ;
        f (ex iftrue) ;
        f (ex iffalse)
    | Gen _ -> ()
    [@@inline]

  let upstream (Ex n) =
    match n.desc with
    | Return _ -> []
    | Var _ -> []
    | Tracking { x; _ } -> [ex x]
    | Map { x; _ } -> [ex x]
    | Map2 { x; y; _ } -> [ex x; ex y]
    | Map3 { x; y; z; _ } -> [ex x; ex y; ex z]
    | Map_array { xs; _ } -> xs |> Array.to_seq |> Seq.map ex |> List.of_seq
    | Bind { m; _ } -> [ex m]
    | If { cond; iftrue; iffalse; _ } -> [ex cond; ex iftrue; ex iffalse]
    | Gen _ -> []

  let used_by (Ex n) = n.used_by

  let valid (Ex n) = Option.is_some n.value

  let rec list_mem node list =
    match list with
    | [] -> false
    | (Dependency hd | Dynamic hd) :: tl ->
        Node_ex.equal node hd || list_mem node tl

  let add_dependency (graph : graph) src dst =
    match Node_table.find_opt graph src with
    | None -> Node_table.add graph src [Dependency dst]
    | Some dsts ->
        let dsts = if list_mem dst dsts then dsts else Dependency dst :: dsts in
        Node_table.replace graph src dsts

  let add_dynamic (graph : graph) src dst =
    match Node_table.find_opt graph src with
    | None -> Node_table.add graph src [Dynamic dst]
    | Some dsts ->
        let dsts =
          if list_mem dst dsts then
            List.map
              (function
                | (Dependency n | Dynamic n) when Node_ex.equal dst n ->
                    Dynamic n
                | n -> n)
              dsts
          else Dynamic dst :: dsts
        in
        Node_table.replace graph src dsts

  let compute_graph (mode : mode) node =
    let rec loop graph visited (node : ex) =
      if Node_table.mem visited node then ()
      else
        let () = Node_table.add visited node () in
        (* let upstream = upstream node in *)
        iter_upstream node (fun back -> add_dependency graph back node) ;
        let (Ex n) = node in
        (match n.desc with
        | Bind { currently_allocated = Some (_, _, dyn); _ } ->
            let dyn = Ex dyn in
            loop graph visited dyn ;
            add_dynamic graph dyn node
        | If { dyn = Some dyn; _ } ->
            loop graph visited dyn ;
            add_dynamic graph dyn node
        | _ -> ()) ;
        iter_upstream node (fun back -> loop graph visited back) ;
        match mode with
        | Backward_only -> ()
        | Full -> List.iter (fun fwd -> loop graph visited fwd) n.used_by
    in
    let graph = Node_table.create 511 in
    Node_table.add graph node [] ;
    let visited = Node_table.create 17 in
    loop graph visited node ;
    graph

  let to_adjacency_list (graph : edge list Node_table.t) =
    let nodes = Array.of_seq (Node_table.to_seq_keys graph) in
    Array.map (fun node -> (node, Node_table.find graph node)) nodes

  let to_dot ?(name = "export") ~mode node oc =
    let graph = compute_graph mode node in
    let adj = to_adjacency_list graph in
    let fmtr = Format.formatter_of_out_channel oc in
    Format.fprintf fmtr "digraph %s {@." name ;
    Array.iter
      (fun (Ex node, _) ->
        Format.fprintf
          fmtr
          "node_%d [%slabel=\"%s_%d\"];@."
          node.uid
          (if valid (ex node) then "" else "shape = box ")
          node.tag
          node.uid)
      adj ;
    let dynamic_attr =
      {|[ penwidth = 2 fontsize = 28 fontcolor = "black" label = "dyn" ]|}
    in
    Array.iter
      (fun (Ex node, edges) ->
        List.iter
          (function
            | Dependency (Ex node') ->
                Format.fprintf fmtr "node_%d -> node_%d;@." node.uid node'.uid
            | Dynamic (Ex node') ->
                Format.fprintf
                  fmtr
                  "node_%d -> node_%d %s;@."
                  node.uid
                  node'.uid
                  dynamic_attr)
          edges)
      adj ;
    Format.fprintf fmtr "}@." ;
    flush oc

  let copy node =
    let mark = Int_table.create 10 in
    let rec copy : type a. a t -> a t =
     fun node ->
      match Int_table.find_opt mark node.uid with
      | Some (Ex n) -> Obj.magic n
      | None ->
          let stub =
            { desc = copy_desc node.desc;
              uid = node.uid;
              tag = node.tag;
              value = node.value;
              used_by = [];
              watchers = node.watchers
            }
          in
          Int_table.add mark node.uid (ex stub) ;
          stub.used_by <- List.map copy_ex node.used_by ;
          stub
    and copy_ex (Ex n) = Ex (copy n)
    and copy_desc : type a. a desc -> a desc =
     fun desc ->
      match desc with
      | Return x -> Return x
      | Var { v } -> Var { v }
      | Tracking { x; v } -> Tracking { x = copy x; v }
      | Gen _ -> desc
      | Map { x; f } -> Map { x = copy x; f }
      | Map2 { x; y; f } -> Map2 { x = copy x; y = copy y; f }
      | Map3 { x; y; z; f } -> Map3 { x = copy x; y = copy y; z = copy z; f }
      | Map_array { xs; f } -> Map_array { xs = Array.map copy xs; f }
      | Bind { m; f; currently_allocated } ->
          Bind
            { m = copy m;
              f;
              currently_allocated =
                (match currently_allocated with
                | None -> None
                | Some (lo, hi, n) -> Some (lo, hi, copy n))
            }
      | If { cond; iftrue; iffalse; dyn } ->
          If
            { cond = copy cond;
              iftrue = copy iftrue;
              iffalse = copy iffalse;
              dyn = Option.map copy_ex dyn
            }
    in
    copy node

  let equal node1 node2 =
    let mark = Int_table.create 10 in
    let rec equal : type a b. a t -> b t -> bool =
     fun node1 node2 ->
      if Int_table.mem mark node1.uid then true
      else if node1 == Obj.magic node2 then true
      else if not (List.length node1.used_by = List.length node2.used_by) then
        (* assert *) false
      else (
        Int_table.add mark node1.uid () ;
        if not (node1.uid = node2.uid) then (* assert *) false
        else if not (String.equal node1.tag node2.tag) then (* assert *) false
        else if
          not
            (match (node1.desc, node2.desc) with
            | (Return x, Return y) ->
                let c = x == Obj.magic y in
                c
            | (Var { v = x }, Var { v = y }) ->
                let c = x == Obj.magic y in
                c
            | (Tracking { x = x1; v = v1 }, Tracking { x = x2; v = v2 }) ->
                let c = v1 == Obj.magic v2 in
                let c = c && equal x1 x2 in
                c
            | (Gen { gen = f }, Gen { gen = g }) ->
                let c = f == Obj.magic g in
                c
            | (Map p1, Map p2) -> equal p1.x p2.x
            | (Map2 p1, Map2 p2) -> equal p1.x p2.x && equal p1.y p2.y
            | (Map3 p1, Map3 p2) ->
                equal p1.x p2.x && equal p1.y p2.y && equal p1.z p2.z
            | (Bind p1, Bind p2) -> (
                equal p1.m p2.m
                &&
                match (p1.currently_allocated, p2.currently_allocated) with
                | (Some (l1, h1, dyn1), Some (l2, h2, dyn2)) ->
                    let uids = l1 = l2 && h1 = h2 in
                    uids && equal dyn1 dyn2
                | (None, None) -> true
                | _ -> false)
            | (If p1, If p2) -> (
                equal p1.cond p2.cond
                &&
                match (p1.dyn, p2.dyn) with
                | (Some (Ex n1), Some (Ex n2)) -> equal n1 n2
                | (None, None) -> true
                | _ -> false)
            | _ -> false)
        then false
        else
          List.for_all2
            (fun (Ex node1) (Ex node2) -> equal node1 node2)
            node1.used_by
            node2.used_by)
    in
    equal node1 node2

  let add_used_by = add_used_by

  let set_next_debug_info s = next_debug_info := Some s
end
