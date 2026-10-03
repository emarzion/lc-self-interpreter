Require Import Extraction.

Require Import LC.Quine.
Require Import LC.Interpreter.

Extraction Language OCaml.

Set Warnings "-extraction-default-directory".

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlNativeString.

Extraction "QuineCode.ml"
  EVAL
  LC.Quine.Quine
  normalize
  print_term.
