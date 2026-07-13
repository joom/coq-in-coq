open Ex_printf

(* The format says "%d". The call site believes it says "%d%s" --- an honest
   refactoring drift, the exact bug type-safe printf exists to rule out.
   OCaml accepts the mismatch, because extraction severed the link between
   the format value and its type: sprintf : 'a1 fmt -> 'a1, with 'a1
   unconstrained by the format's constructors (Fint : __ fmt -> 'x fmt). *)
let report : nat -> str -> str = sprintf (Fint Fstop)

let () =
  Printf.printf "calling report...\n%!";
  let _ = report O Sempty in
  Printf.printf "returned\n%!"
