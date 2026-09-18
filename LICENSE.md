ISC License

Copyright (c) 2026 ocaml-curve448 contributors

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR
OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
PERFORMANCE OF THIS SOFTWARE.

---

## Third-party material

The ISC license above covers the code written for this project. The
following material comes from elsewhere and remains under its own license:

| Material | License | Notice |
| --- | --- | --- |
| `lib/c/native/p448_64.h` (fiat-crypto, verbatim) | MIT | [`licenses/fiat-crypto.txt`](licenses/fiat-crypto.txt) |
| X448 ladder, field wrapper types and point representations in `lib/c/native/` (adapted from BoringSSL) | ISC | [`licenses/boringssl.txt`](licenses/boringssl.txt) |
| Keccak-f[1600] loop structure in `lib/c/native/shake256.h` (adapted from tiny_sha3) | MIT | [`licenses/tiny_sha3.txt`](licenses/tiny_sha3.txt) |
| `test-vectors/wycheproof/` (Project Wycheproof) | Apache-2.0 | [`test-vectors/wycheproof/LICENSE`](test-vectors/wycheproof/LICENSE) |
| RFC 7748, RFC 8032 and RFC 9180 test vectors in `test-vectors/` | IETF Trust Legal Provisions | [`test-vectors/PROVENANCE.md`](test-vectors/PROVENANCE.md) |

All of it is in the C backend (`curve448.c`) or the test data. The pure OCaml
backend (`lib/ocaml/`) and the shared API contain no third-party code.
