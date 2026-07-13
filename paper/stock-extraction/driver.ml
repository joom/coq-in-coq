open Ex_fin

(* A perfectly well-typed OCaml call: the vector is empty, but the length
   index was erased, so OCaml cannot see that (F1 O) is out of bounds. *)
let () =
  let f : int -> int = nth O Nil (F1 O) in
  Printf.printf "got a function back; applying it...\n%!";
  Printf.printf "result: %d\n%!" (f 3)
