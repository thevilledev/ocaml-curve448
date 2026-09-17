#!/usr/bin/env python3
"""Generate test-vectors/shake256.json with Python's hashlib (OpenSSL).

The message and output lengths straddle the 136-byte SHAKE256 rate so that
padding and multi-block absorb/squeeze paths are covered. The message of
length n is the byte string (7 + 131 k) mod 256 for k = 0 .. n - 1, so only
lengths are stored.

Usage:
  python3 tools/gen_shake256_vectors.py > test-vectors/shake256.json
"""

import hashlib
import json
import platform
import ssl
import sys

MESSAGE_LENGTHS = [0, 1, 3, 57, 64, 114, 135, 136, 137, 200, 271, 272, 273, 1000, 4096]
OUTPUT_LENGTHS = [1, 57, 64, 114, 135, 136, 137, 272, 500]


def message(length):
    return bytes((i * 131 + 7) & 0xFF for i in range(length))


def main():
    vectors = []
    for msg_len in MESSAGE_LENGTHS:
        for out_len in OUTPUT_LENGTHS:
            msg = message(msg_len)
            vectors.append(
                {
                    "message_length": msg_len,
                    "output": hashlib.shake_256(msg).hexdigest(out_len),
                }
            )
    corpus = {
        "source": {
            "generator": "tools/gen_shake256_vectors.py",
            "message": "byte k is (7 + 131 k) mod 256",
            "implementation": "Python %s hashlib, %s" % (platform.python_version(), ssl.OPENSSL_VERSION),
        },
        "vectors": vectors,
    }
    json.dump(corpus, sys.stdout, indent=1)
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
