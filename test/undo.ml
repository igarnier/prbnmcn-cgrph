open Cgraph
open Infix

let () = Internal.set_debug true

(* Testing [undo] with non-tracking variables *)

let input1 = Var.create 0

let input2 = Var.create 1

let input3 = Var.create ~-1

let term =
  let part1 = return "branch " in
  let part2 = return "1" in
  (* let () = Obj.set_field (Obj.repr part1) 2 (Obj.repr "part1") in
   * let () = Obj.set_field (Obj.repr part2) 2 (Obj.repr "part2") in *)
  if_
    (map2 (var input1) (var input2) ( < ))
    (let v3 = var input3 in
     let* _x = v3 in
     (* let () = Obj.set_field (Obj.repr v3) 2 (Obj.repr "v3") in *)
     let nasty = return () in
     (* let () = Obj.set_field (Obj.repr nasty) 2 (Obj.repr "nasty") in *)
     let y = return () in
     let* () = y in
     (* let () = Obj.set_field (Obj.repr y) 2 (Obj.repr "y") in *)
     map3 part1 part2 nasty (fun x y () -> x ^ y))
    (return "branch 2")

let () = assert (Internal.equal term term)

let copy = Internal.copy term

(* let () =
 *   Internal.to_dot
 *     ~name:"term"
 *     ~mode:Internal.Full
 *     (ex term)
 *     (open_out "/tmp/term0.dot")
 *
 * let () =
 *   Internal.to_dot
 *     ~name:"copy"
 *     ~mode:Internal.Full
 *     (ex copy)
 *     (open_out "/tmp/copy0.dot") *)

let () = assert (Internal.equal copy copy)

let () = assert (Internal.equal copy term)

let () = assert (get term = get copy)

(* let () =
 *   Internal.to_dot
 *     ~name:"term"
 *     ~mode:Internal.Full
 *     (ex term)
 *     (open_out "/tmp/term1.dot")
 *
 * let () =
 *   Internal.to_dot
 *     ~name:"term"
 *     ~mode:Internal.Full
 *     (ex copy)
 *     (open_out "/tmp/copy1.dot") *)

(* At this stage, [term] and [copy] are not equal anymore (side-effects performed)
   during [get] *)

let copy = Internal.copy term

let u = Var.set_with_undo input1 2

let () = assert (not (Internal.equal copy term))

let _ = get ~u term

(* let () =
 *   Internal.to_dot
 *     ~name:"term"
 *     ~mode:Internal.Full
 *     (ex term)
 *     (open_out "/tmp/term2.dot")
 *
 * let () =
 *   Internal.to_dot
 *     ~name:"term"
 *     ~mode:Internal.Full
 *     (ex copy)
 *     (open_out "/tmp/copy2.dot") *)

let () = undo u

(* let () =
 *   Internal.to_dot
 *     ~name:"term"
 *     ~mode:Internal.Full
 *     (ex term)
 *     (open_out "/tmp/term3.dot")
 *
 * let () =
 *   Internal.to_dot
 *     ~name:"term"
 *     ~mode:Internal.Full
 *     (ex copy)
 *     (open_out "/tmp/copy3.dot") *)

let () = assert (Internal.equal copy term)

let u = Var.set_with_undo input3 8

let _ = get ~u term

let () = undo u

(* let () =
 *   Internal.to_dot
 *     ~name:"term"
 *     ~mode:Internal.Full
 *     (ex term)
 *     (open_out "/tmp/term4.dot") *)
