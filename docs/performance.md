# Performance

[Documentation](README.md) · [Project home](../README.md)

These measurements are recorded results, not a performance guarantee.

Best of three one-second runs, with OpenSSL 3.6.4 (`openssl speed`) on the
same machine. Apple M1 Pro, macOS, OCaml 5.4.1:

| Operation | `curve448.ocaml` | `curve448.c` | OpenSSL 3.6.4 |
| --- | ---: | ---: | ---: |
| X448 key exchange | 374 µs | 130 µs | 133 µs |
| Ed448 key pair from seed | 139 µs | 60 µs | — |
| Ed448 sign (64-byte message) | 147 µs | 64 µs | 60 µs |
| Ed448 verify (64-byte message) | 520 µs | 203 µs | 141 µs |

AMD Ryzen AI 9 HX PRO 370, Linux, OCaml 5.5.1:

| Operation | `curve448.ocaml` | `curve448.c` | OpenSSL 3.6.4 |
| --- | ---: | ---: | ---: |
| X448 key exchange | 225 µs | 93 µs | 115 µs |
| Ed448 key pair from seed | 87 µs | 43 µs | — |
| Ed448 sign (64-byte message) | 91 µs | 48 µs | 111 µs |
| Ed448 verify (64-byte message) | 328 µs | 152 µs | 121 µs |

On the same machines, mirage-crypto-ec's X25519 takes 30 µs and 21 µs, its
Ed25519 signs in 39 µs and 27 µs, and verifies in 37 µs and 27 µs.

The C backend is close to or faster than OpenSSL except in verification,
which is slower because it is constant-time; OpenSSL uses a variable-time
double-scalar multiplication. Run
`opam exec -- dune exec --profile release bench/bench_curve448_ocaml.exe` (or
`bench_curve448_c.exe`) to measure your machine.

See [testing](testing.md#benchmarks) for benchmark commands.
