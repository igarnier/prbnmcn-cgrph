open Cgraph
open Infix

let () = Internal.set_debug true

let input1 = Var.create 0

let node1 = var input1

let input2 = Var.create_tracking node1

let node2 = var input2

let () = assert (get node1 = get node2)

let () = Var.set input2 1

let () = assert (get node1 = 0)

let () = assert (get node2 = 1)

let () = Var.set input2 2

let () = assert (get node1 = 0)

let () = assert (get node2 = 2)

let () = Var.set input1 42

let () = assert (get node1 = 42)

let () = assert (get node2 = 42)

let () = Var.set input1 43

let () = assert (get node2 = 43)

(* Testing [undo] with tracking variables *)

let input1 = Var.create 0

let input2 = Var.create 1

let input3 = Var.create ~-1

let (tracking1, tracking2, tracking3) =
  let (var1, var2, var3) = (var input1, var input2, var input3) in
  (Var.create_tracking var1, Var.create_tracking var2, Var.create_tracking var3)

let (var1, var2, var3) = (var tracking1, var tracking2, var tracking3)

let term =
  let part1 = return "branch " in
  let part2 = return "1" in
  (* let () = Obj.set_field (Obj.repr part1) 2 (Obj.repr "part1") in
   * let () = Obj.set_field (Obj.repr part2) 2 (Obj.repr "part2") in *)
  if_
    (map2 var1 var2 ( < ))
    (let v3 = var3 in
     let* _x = v3 in
     (* let () = Obj.set_field (Obj.repr v3) 2 (Obj.repr "v3") in *)
     let nasty = return () in
     (* let () = Obj.set_field (Obj.repr nasty) 2 (Obj.repr "nasty") in *)
     let y = return () in
     let* () = y in
     (* let () = Obj.set_field (Obj.repr y) 2 (Obj.repr "y") in *)
     map3 part1 part2 nasty (fun x y () -> x ^ y))
    (return "branch 2")

let _ = get term

let copy = Internal.copy term

let () = assert (Internal.equal term term)

let () = assert (Internal.equal copy copy)

let () = assert (Internal.equal copy term)

let () = assert (get term = get copy)

(* test setting a normal variable feeding through a tracking one *)

let u = Var.set_with_undo input1 2

(* let () = assert (not (Internal.equal copy term)) *)

let _ = get ~u term

let () = undo u

(* let () =
 *   Internal.to_dot
 *     ~name:"term"
 *     ~mode:Internal.Full
 *     (ex copy)
 *     (open_out "/tmp/copy.dot")
 *
 * let () =
 *   Internal.to_dot
 *     ~name:"term"
 *     ~mode:Internal.Full
 *     (ex term)
 *     (open_out "/tmp/term2.dot") *)

let () = assert (Internal.equal copy term)

let u = Var.set_with_undo tracking1 2

(* let () = assert (not (Internal.equal copy term)) *)

let _ = get ~u term

let () = undo u

let () = assert (Internal.equal copy term)

let u = Var.set_with_undo tracking2 (-1)

(* let () = assert (not (Internal.equal copy term)) *)

let _ = get ~u term

let () = undo u

let () = assert (Internal.equal copy term)

let u = Var.set_with_undo tracking3 (-1)

(* let () = assert (not (Internal.equal copy term)) *)

let _ = get ~u term

let () = undo u

let () = assert (Internal.equal copy term)
