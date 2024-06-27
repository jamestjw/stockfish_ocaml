(lang dune 3.15)

(name stockfish_ocaml)

(generate_opam_files true)

(source
 (github jamestjw/stockfish_ocaml))

(authors "see AUTHORS file")

(maintainers "James Tan")

(license GPL-3.0)

(package
 (name stockfish_ocaml)
 (synopsis "A rewrite of Stockfish in OCaml")
 (description "Stockfish is a free and strong UCI chess engine derived from Glaurung 2.1 that analyzes chess positions and computes the optimal moves. This is a rewrite of Stockfish (https://github.com/official-stockfish/Stockfish) in OCaml.")
 (depends
   ocaml
   dune
   integers
   ppx_jane
   ppx_deriving)
 (tags
  (chess-engine uci chess stockfish)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
