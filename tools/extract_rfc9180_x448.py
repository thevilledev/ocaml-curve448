#!/usr/bin/env python3
"""Extract the DHKEM(X448, HKDF-SHA512) vectors of RFC 9180 into a KEM corpus.

The KEM part of an HPKE test vector (DeriveKeyPair, Encap/Decap and
AuthEncap/AuthDecap) depends only on the KEM, so every vector with
kem_id = 0x0021 is kept, reduced to the fields the KEM consumes and produces.

Usage:
  curl -O https://raw.githubusercontent.com/cfrg/draft-irtf-cfrg-hpke/5f503c564da00b0687b3de75f1dfbdfc4079ad31/test-vectors.json
  python3 tools/extract_rfc9180_x448.py test-vectors.json test-vectors/rfc9180-dhkem-x448.json
"""

import hashlib
import json
import sys

SOURCE_COMMIT = "5f503c564da00b0687b3de75f1dfbdfc4079ad31"
SOURCE_SHA256 = "61fc662f01996cd06d713dacf5e133167bd309a1f329442d53f1e21a47b3ede6"
SOURCE_URL = (
    "https://raw.githubusercontent.com/cfrg/draft-irtf-cfrg-hpke/"
    + SOURCE_COMMIT
    + "/test-vectors.json"
)
KEM_X448 = 0x0021
FIELDS = (
    "mode", "kem_id", "kdf_id", "aead_id",
    "ikmE", "skEm", "pkEm",
    "ikmR", "skRm", "pkRm",
    "ikmS", "skSm", "pkSm",
    "enc", "shared_secret",
)


def main(argv):
    if len(argv) != 3:
        sys.stderr.write(__doc__)
        return 2
    with open(argv[1], "rb") as handle:
        raw = handle.read()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != SOURCE_SHA256:
        sys.stderr.write("unexpected source digest %s\n" % digest)
        return 1
    vectors = [
        {field: vector[field] for field in FIELDS if field in vector}
        for vector in json.loads(raw)
        if vector["kem_id"] == KEM_X448
    ]
    modes = sorted({v["mode"] for v in vectors})
    if len(vectors) != 32 or modes != [0, 1, 2, 3]:
        sys.stderr.write("expected 32 X448 vectors over modes 0-3\n")
        return 1
    corpus = {
        "source": {"url": SOURCE_URL, "commit": SOURCE_COMMIT, "sha256": SOURCE_SHA256},
        "vectors": vectors,
    }
    with open(argv[2], "w", encoding="ascii") as handle:
        json.dump(corpus, handle, indent=2)
        handle.write("\n")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
