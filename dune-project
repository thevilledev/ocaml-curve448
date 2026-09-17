(lang dune 3.6)

(name curve448)

(generate_opam_files true)

(source
 (github thevilledev/ocaml-curve448))

(documentation https://github.com/thevilledev/ocaml-curve448/tree/main/docs)

(license "ISC AND MIT")

(authors "Ville Vesilehto <ville@vesilehto.fi>")

(maintainers "Ville Vesilehto <ville@vesilehto.fi>")

(package
 (name curve448)
 (synopsis "X448 and Ed448 (RFC 7748, RFC 8032) for OCaml")
 (description
  "X448 Diffie-Hellman and Ed448/Ed448ph signatures over Curve448, with an \
   API that mirrors mirage-crypto-ec's X25519 and Ed25519 modules so that \
   HPKE, TLS and X.509 code written against those can adopt X448 and Ed448 \
   directly. The default implementation is pure OCaml; an optional C \
   implementation (curve448.c) uses fiat-crypto's verified field arithmetic \
   and is two to three times faster. Both are written to avoid \
   secret-dependent branches and memory access.")
 (tags
  (cryptography x448 ed448 curve448 rfc7748 rfc8032 "elliptic curves"))
 (depends
  (dune
   (>= 3.6.2))
  (ocaml
   (>= 4.14.0))
  (mirage-crypto-rng
   (>= 2.0.1))
  (alcotest
   (and
    :with-test
    (>= 1.7.0)))
  (qcheck-core
   (and
    :with-test
    (>= 0.90)))
  (qcheck-alcotest
   (and
    :with-test
    (>= 0.90)))
  (yojson
   (and
    :with-test
    (>= 2.0.0)))
  (zarith
   (and
    :with-test
    (>= 1.12)))
  (mirage-crypto-ec
   (and
    :with-test
    (>= 2.0.1)))
  (digestif
   (and
    :with-test
    (>= 1.3.1)))
  (kdf
   (and
    :with-test
    (>= 1.1.0)))
  (crowbar
   (and
    :with-test
    (>= 0.2.1)))
  (odoc
   (and
    :with-doc
    (>= 2.1.1)))))
