# Interoperability

[Documentation](README.md) · [Project home](../README.md)

curve448 is tested against two independent implementations:

- **OpenSSL 3.6.4** through the EVP interface (`EVP_PKEY_derive` for X448;
  `EVP_DigestSign`/`EVP_DigestVerify` with the `instance` and
  `context-string` parameters for Ed448 and Ed448ph). OpenSSL's Curve448 code
  descends from Mike Hamburg's libdecaf.
- **Cloudflare CIRCL v1.6.3** (`dh/x448`, `sign/ed448`), the usual Go choice
  since the standard library has no Curve448.

Both run as small harness processes (`tools/differential/openssl`,
`tools/differential/go`) driven by `tools/differential/differential.ml`, which
generates random and adversarial requests and compares every answer with
curve448's. The driver answers with the pure OCaml backend, and a third
harness answers with the C backend, so each run also compares curve448's two
implementations with each other.

## Results

The two curve448 backends gave the same answer to every request, in the run
below and in a run with `--count 2000 --seed 7` (26,071 requests), so the
curve448 column stands for both. A run with `--count 64 --seed 448` (903
requests):

| Category | Cases | OpenSSL agrees | CIRCL agrees |
| --- | ---: | ---: | ---: |
| `x448/random` | 64 | 64 | 64 |
| `x448/low-order-u` (0, 1, p - 1, p, p + 1) | 5 | 5 | 5 |
| `x448/non-canonical-u` (u + p) | 8 | 8 | 8 |
| `x448/bit-447-u` | 8 | 8 | 8 |
| `x448/edge-u` | 6 | 6 | 6 |
| `x448/edge-scalar` (0, 2^448 - 1, 4L) | 3 | 3 | **2** |
| `x448/wrong-length` | 1 | 1 | 1 |
| `ed448/public` | 66 | 66 | 66 |
| `ed448/sign`, `sign-context`, `ed448ph/sign` | 192 | 192 | 192 |
| `ed448/sign-long-message`, `sign-255-byte-context` | 2 | 2 | 2 |
| `ed448/verify-valid` | 64 | 64 | 64 |
| `ed448/verify-tampered-{signature,message,context,key}` | 256 | 256 | 256 |
| `ed448/verify-other-variant` (Ed448 vs Ed448ph) | 64 | 64 | 64 |
| `ed448/verify-s-plus-l` | 64 | 64 | 64 |
| `ed448/verify-truncated` | 64 | 64 | 64 |
| `ed448/verify-non-canonical-r`, `non-canonical-key`, `x-zero-sign-bit` | 3 | 3 | 3 |
| `ed448/verify-torsion-none` | 1 | 1 | 1 |
| `ed448/verify-torsion-in-key` | 3 | 3 | 3 |
| `ed448/verify-torsion-in-r` | 3 | 3 | **0** |
| `ed448/verify-torsion-in-both` | 9 | 9 | **0** |
| `ed448/verify-small-order-key` | 16 | **8** | 16 |
| `ed448/verify-identity-key` | 1 | **0** | 1 |

All three implementations agree on every honest key, signature and shared
secret, on context strings and Ed448ph, on malleability (S + L), truncated and
tampered signatures, non-canonical encodings, and on every X448 public input,
including low-order, non-canonical and bit-447 u-coordinates. The remaining
22 answers differ in three places. Each is a deliberate behaviour of one
implementation, none affects honestly generated keys and signatures, and the
pinned corpus test (`test/test_vectors.ml`) fails if any of them changes.

### 1. CIRCL does not reject an all-zero X448 output

For the private scalar 4L (four times the group order, which is a valid clamped
X448 scalar) and the base point, X448 yields zero. curve448 and OpenSSL reject
the exchange; CIRCL's `x448.Shared` returns `true` with an all-zero secret,
because it checks the peer's public key against a list of low-order points but
does not check the output. The two checks are equivalent for honest private
keys and differ only for this degenerate private key. RFC 7748, section 6.2,
recommends checking the output, and TLS 1.3 and HPKE require it.

### 2. CIRCL rejects signatures whose R has a small-order component

CIRCL computes [S]B - [k]A (through the 4-isogeny, which discards any torsion
in A), encodes it, and compares the bytes with R. A signature whose R is
[r]B + T for a point T of order 2 or 4 therefore fails. curve448 and OpenSSL
check RFC 8032's cofactored equation [4][S]B = [4]R + [4][k]A, which accepts
it. Such signatures can only be produced deliberately by the signer.

### 3. OpenSSL rejects the encodings of (0, 1) and (0, -1)

OpenSSL decodes points by computing an inverse square root of
(1 - y^2)(1 - d y^2), which fails when y = ±1. The identity (0, 1) and the
point of order two (0, -1) are therefore rejected, both as public keys and as
R. RFC 8032, section 5.2.3, decodes both (x = 0 is a valid root), and so do
curve448 and CIRCL. The other two small-order points, (±1, 0), are accepted by
all three.

## Small-order public keys

edwards448 has four points of small order, and each has one canonical
encoding (57 bytes, hex, little-endian y followed by the sign byte):

| Point | Order | Encoding |
| --- | ---: | --- |
| (0, 1) | 1 | `01` followed by 56 zero bytes |
| (0, -1) | 2 | `fe` `ff` x 27 `fe` `ff` x 27 `00` |
| (1, 0) | 4 | 56 zero bytes then `80` |
| (-1, 0) | 4 | 57 zero bytes |

Under the cofactored equation, a small-order public key A has [4][k]A = 0, so
any R with [4]R = [4][S]B, e.g. R = [S]B, verifies for every message. RFC 8032
permits these keys, key generation never produces them, and OpenSSL (for the
two order-4 points) and CIRCL accept them too. A protocol that needs a
signature to bind a message to an honestly generated key should reject these
four encodings before use.

## Semantics compared with other libraries

| Behaviour | curve448 | OpenSSL 3 | CIRCL | RFC |
| --- | --- | --- | --- | --- |
| X448 u-coordinate >= p | reduced | reduced | reduced | reduce (7748 §5) |
| X448 bit 447 of u | significant | significant | significant | not masked |
| X448 all-zero output | `Low_order` error | error | accepted | check recommended (7748 §6.2) |
| X448 low-order public key | error (zero output) | error | error | — |
| Ed448 non-canonical R or A | rejected | rejected | rejected | rejected (8032 §5.2.3) |
| Ed448 S >= L | rejected | rejected | rejected | rejected (8032 §5.2.7) |
| Ed448 verification equation | cofactored | cofactored | exact R | cofactored, cofactorless allowed |
| Ed448 keys (0, ±1) | accepted | rejected | accepted | accepted |
| Ed448 contexts | 0-255 bytes | 0-255 bytes | 0-255 bytes | 0-255 bytes |
| Ed448ph prehash | SHAKE256(M, 64) | same | same | same |

## Reproducing

```sh
tools/differential/run.sh --count 64 --seed 448
```

The script builds the OpenSSL harness with the system C compiler
(`OPENSSL_PREFIX` selects the installation; OpenSSL 3.2 or later is needed for
the Ed448 `instance` and `context-string` parameters), the CIRCL harness with
Go and the C-backend harness with dune, then runs the driver, which prints a
column for each harness. `--output FILE` writes a corpus in the format of
`test-vectors/differential/openssl-circl.json`. The script is not part of CI:
distribution OpenSSL packages such as Ubuntu 24.04's 3.0 are too old.
