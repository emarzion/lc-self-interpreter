(lang dune 3.21)
(using rocq 0.11)

(generate_opam_files)

(package
 (name lambda_calc)   ; Your project's OPAM package name
 (synopsis "Some untyped lambda calculus.")
 (depends
   (ocaml (>= 4.14.1))
   (dune (>= 3.21))
   (rocq-prover (>= 9.0.0))
   (rocq-stdlib (>= 9.0.0))
 )
)
