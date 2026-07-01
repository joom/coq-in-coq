(lang dune 3.17)
(using coq 0.9)
(using menhir 3.0)

(package
 (name coq-in-coq)
 (synopsis "Calculus of Constructions formalized in the Rocq Prover")
 (license LGPL-2.1-or-later)
 (authors "Bruno Barras")
 (depends
  (ocaml (>= 4.14.0))
  (coq (>= "9.0~"))
  (rocq-runtime (>= "9.0~"))
  (menhir (>= 20220210))))
