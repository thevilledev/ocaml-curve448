#!/usr/bin/env python3
"""Extract the X448, Ed448 and Ed448ph test vectors from the RFC text.

The RFCs are immutable documents; the extractor records the SHA-256 digest of
the text it read and fails unless it finds exactly the expected vectors with
the expected lengths.

Usage:
  curl -O https://www.rfc-editor.org/rfc/rfc7748.txt
  curl -O https://www.rfc-editor.org/rfc/rfc8032.txt
  python3 tools/extract_rfc_vectors.py rfc7748.txt rfc8032.txt test-vectors
"""

import hashlib
import json
import os
import re
import sys

HEX_LINE = re.compile(r"^(?:[0-9a-f]{2})+$")
PAGE_FOOTER = re.compile(r"\[Page \d+\]\s*$")
PAGE_HEADER = re.compile(r"^RFC \d{4} .* \d{4}\s*$")


def read_rfc(path):
    with open(path, "rb") as handle:
        raw = handle.read()
    lines = []
    for line in raw.decode("ascii").replace("\f", "\n").split("\n"):
        if PAGE_FOOTER.search(line) or PAGE_HEADER.match(line):
            continue
        lines.append(line.rstrip())
    return lines, hashlib.sha256(raw).hexdigest()


def section(lines, start, end):
    """Lines from the first line equal to [start] up to the next equal to [end]."""
    first = lines.index(start)
    last = lines.index(end, first + 1)
    return lines[first + 1 : last]


def hex_after(lines, index):
    """Concatenate the hex lines following lines[index], skipping blank lines."""
    out = []
    for line in lines[index + 1 :]:
        stripped = line.strip()
        if not stripped:
            continue
        if not HEX_LINE.match(stripped):
            break
        out.append(stripped)
    return "".join(out)


def labelled(lines, label):
    return [hex_after(lines, i) for i, line in enumerate(lines) if line.strip() == label]


def expect(condition, message):
    if not condition:
        sys.stderr.write("extraction failed: %s\n" % message)
        sys.exit(1)


def rfc7748(path):
    lines, digest = read_rfc(path)
    body = section(lines, "5.2.  Test Vectors", "6.  Diffie-Hellman")

    split = next(i for i, l in enumerate(body) if l.strip().startswith("The second type"))
    functions, iterated = body[:split], body[split:]

    x448_start = functions.index("   X448:")
    functions = functions[x448_start:]
    scalars = labelled(functions, "Input scalar:")
    points = labelled(functions, "Input u-coordinate:")
    outputs = labelled(functions, "Output u-coordinate:")
    expect(len(scalars) == len(points) == len(outputs) == 2, "RFC 7748 5.2 X448 vectors")
    function_vectors = [
        {"scalar": k, "u": u, "output": o} for k, u, o in zip(scalars, points, outputs)
    ]

    iterated = iterated[iterated.index("   X448:") :]
    iteration_vectors = []
    for label, count in (
        ("After one iteration:", 1),
        ("After 1,000 iterations:", 1000),
        ("After 1,000,000 iterations:", 1000000),
    ):
        found = labelled(iterated, label)
        expect(len(found) == 1, "RFC 7748 5.2 iterated X448 vector %d" % count)
        iteration_vectors.append({"iterations": count, "output": found[0]})

    dh_section = section(lines, "6.2.  Curve448", "7.  Security Considerations")
    dh = {}
    for key, label in (
        ("alice_private", "Alice's private key, a:"),
        ("alice_public", "Alice's public key, X448(a, 5):"),
        ("bob_private", "Bob's private key, b:"),
        ("bob_public", "Bob's public key, X448(b, 5):"),
        ("shared", "Their shared secret, K:"),
    ):
        found = labelled(dh_section, label)
        expect(len(found) == 1, "RFC 7748 6.2 %s" % key)
        dh[key] = found[0]

    for vector in function_vectors:
        expect(all(len(v) == 112 for v in vector.values()), "X448 lengths")
    expect(all(len(v["output"]) == 112 for v in iteration_vectors), "iterated lengths")
    expect(all(len(v) == 112 for v in dh.values()), "DH lengths")

    return {
        "source": {
            "document": "RFC 7748",
            "url": "https://www.rfc-editor.org/rfc/rfc7748.txt",
            "sha256": digest,
        },
        "x448": function_vectors,
        "x448_iterated": iteration_vectors,
        "x448_dh": dh,
    }


def rfc8032(path):
    lines, digest = read_rfc(path)
    body = section(lines, "7.4.  Test Vectors for Ed448", "8.  Security Considerations")

    starts = [
        i for i, l in enumerate(body) if l.strip().startswith("-----") and l.strip() != "-----"
    ]
    vectors = []
    for n, start in enumerate(starts):
        stop = starts[n + 1] if n + 1 < len(starts) else len(body)
        block = body[start:stop]
        name = block[0].strip()[5:]
        algorithm_index = next(i for i, l in enumerate(block) if l.strip() == "ALGORITHM:")
        algorithm = next(l.strip() for l in block[algorithm_index + 1 :] if l.strip())
        message_index = next(
            i for i, l in enumerate(block) if l.strip().startswith("MESSAGE (length")
        )
        message_length = int(re.search(r"length (\d+) byte", block[message_index]).group(1))
        contexts = labelled(block, "CONTEXT:")
        vector = {
            "name": name,
            "algorithm": algorithm,
            "secret_key": labelled(block, "SECRET KEY:")[0],
            "public_key": labelled(block, "PUBLIC KEY:")[0],
            "message": hex_after(block, message_index),
            "context": contexts[0] if contexts else "",
            "signature": labelled(block, "SIGNATURE:")[0],
        }
        expect(algorithm in ("Ed448", "Ed448ph"), "algorithm of %s" % name)
        expect(len(vector["secret_key"]) == 114, "secret key length of %s" % name)
        expect(len(vector["public_key"]) == 114, "public key length of %s" % name)
        expect(len(vector["message"]) == 2 * message_length, "message length of %s" % name)
        expect(len(vector["signature"]) == 228, "signature length of %s" % name)
        vectors.append(vector)

    expect(sum(v["algorithm"] == "Ed448" for v in vectors) == 9, "nine Ed448 vectors")
    expect(sum(v["algorithm"] == "Ed448ph" for v in vectors) == 2, "two Ed448ph vectors")
    return {
        "source": {
            "document": "RFC 8032",
            "url": "https://www.rfc-editor.org/rfc/rfc8032.txt",
            "sha256": digest,
        },
        "vectors": vectors,
    }


def write(path, data):
    with open(path, "w", encoding="ascii") as handle:
        json.dump(data, handle, indent=2)
        handle.write("\n")


def main(argv):
    if len(argv) != 4:
        sys.stderr.write(__doc__)
        return 2
    write(os.path.join(argv[3], "rfc7748.json"), rfc7748(argv[1]))
    write(os.path.join(argv[3], "rfc8032.json"), rfc8032(argv[2]))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
