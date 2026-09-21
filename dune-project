(lang dune 3.8)
(name radix-sort)
(generate_opam_files true)
(source
 (github thevilledev/ocaml-radix-sort))

(package
 (name radix-sort)
 (synopsis "Fast radix sorting for OCaml arrays")
 (description
  "Stable LSD radix sorts for int, int64, and float arrays, an in-place
American-flag sort for strings, and optional Domain-parallel sorts on OCaml 5.")
 (authors "Ville Vesilehto")
 (maintainers "Ville Vesilehto <ville@vesilehto.fi>")
 (license ISC)
 (depends
  (ocaml (>= 4.11))
  (odoc :with-doc))
 (tags
  (radix sort sorting arrays performance parallel)))
