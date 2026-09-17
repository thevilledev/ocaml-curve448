# Usage

[Documentation](README.md) · [Project home](../README.md)

Link `curve448` and `mirage-crypto-rng.unix` in your executable:

```dune
(executable
 (name main)
 (libraries curve448 mirage-crypto-rng.unix))
```

## Key agreement and signatures

The caller initialises the random number generator used for key generation.

```ocaml
(* X448 key agreement, as a TLS 1.3 key share or an HPKE DHKEM would use it. *)
let () =
  Mirage_crypto_rng_unix.use_default ();
  let alice_secret, alice_share = Curve448.X448.gen_key () in
  let bob_secret, bob_share = Curve448.X448.gen_key () in
  match
    ( Curve448.X448.key_exchange alice_secret bob_share,
      Curve448.X448.key_exchange bob_secret alice_share )
  with
  | Ok a, Ok b -> assert (String.equal a b)
  | Error e, _ | _, Error e ->
      (* `Low_order: the peer sent a small-order point; abort the handshake. *)
      Format.eprintf "key exchange failed: %a@." Curve448.pp_error e
```

```ocaml
let () =
  Mirage_crypto_rng_unix.use_default ();
  let priv, pub = Curve448.Ed448.generate () in

  (* Plain Ed448, as used by X.509 certificates and TLS: empty context. *)
  let msg = "attack at dawn" in
  let signature = Curve448.Ed448.sign ~key:priv msg in
  assert (Curve448.Ed448.verify ~key:pub signature ~msg);

  (* A context string (up to 255 bytes) separates signatures by purpose. *)
  let ctx = "example.com/v1/login" in
  let bound = Curve448.Ed448.sign ~ctx ~key:priv msg in
  assert (not (Curve448.Ed448.verify ~key:pub bound ~msg));

  (* Ed448ph signs SHAKE256(msg, 64); the digest may be computed elsewhere. *)
  let digest = Curve448.Ed448ph.prehash msg in
  let ph = Curve448.Ed448ph.sign_prehashed ~key:priv digest in
  assert (Curve448.Ed448ph.verify ~key:pub ph ~msg)
```

Both programs are in [`examples/`](../examples) and run as part of `dune test`.

### Next to mirage-crypto-ec

| mirage-crypto-ec | curve448 |
| --- | --- |
| `X25519 : Dh` | `X448 : Dh` (checked at compile time by the tests) |
| `Ed25519.priv_of_octets`, `pub_of_octets`, `pub_of_priv`, `generate`, `sign ~key`, `verify ~key sig ~msg` | same names and labels in `Ed448`, plus `?ctx` on `sign` and `verify` |
| `error`, `pp_error` | the same polymorphic variant and printed text |

Code that matches on `` `Low_order `` or `` `Not_on_curve `` for X25519 and
Ed25519 handles X448 and Ed448 unchanged. For HPKE, DHKEM(X448) is
`X448.secret_of_octets` on the output of `LabeledExpand(..., "sk", "", 56)`
followed by `key_exchange`; `test/test_vectors.ml` builds it that way and
passes all 32 RFC 9180 X448 vectors. For X.509, an Ed448 key in
SubjectPublicKeyInfo or PKCS #8 (RFC 8410) is the 57-byte string after a fixed
DER prefix, and the tests verify an OpenSSL-generated Ed448 certificate.

## Behaviour

- **X448** accepts all 2^448 public values, reduces u >= p, and does not mask
  bit 447. An all-zero shared secret, which every low-order point produces,
  returns `` `Low_order ``, as TLS 1.3 and HPKE require.
- **Ed448 verification** rejects non-canonical R and A encodings and S >= L,
  then checks the cofactored equation [4][S]B = [4]R + [4][k]A. Signatures are
  deterministic.
- **Small-order Ed448 public keys** are accepted, as RFC 8032 specifies, and
  accept a signature on every message. See
  [interoperability notes](interoperability.md) if your protocol needs
  to reject them.

curve448 agrees with OpenSSL 3.6.4 and CIRCL v1.6.3 on all honest inputs and on
a range of adversarial ones. The three documented differences, each a
deliberate choice by one of the other libraries, are described in
[interoperability notes](interoperability.md).

## API reference

The API reference is in [`lib/curve448.mli`](../lib/curve448.mli).
Generate HTML with `opam exec -- dune build @doc` after installing the
[documentation dependencies](../CONTRIBUTING.md). Open
`_build/default/_doc/_html/curve448/index.html`.
