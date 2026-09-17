// Command circl-harness answers curve448 differential-test requests with
// Cloudflare CIRCL's dh/x448 and sign/ed448 packages.
//
// Requests and responses are single lines of space-separated fields. Byte
// strings are lowercase hex; "-" is the empty string.
//
//	x448 <scalar> <u>                            -> ok <shared> | err
//	ed448-public <seed>                          -> ok <public> | err
//	ed448-sign <ph> <seed> <ctx> <msg>           -> ok <signature> | err
//	ed448-verify <ph> <public> <ctx> <msg> <sig> -> ok 1 | ok 0
//
// <ph> is 0 for Ed448 and 1 for Ed448ph; for Ed448ph the harness hashes <msg>.
package main

import (
	"bufio"
	"encoding/hex"
	"fmt"
	"os"
	"strings"

	"github.com/cloudflare/circl/dh/x448"
	"github.com/cloudflare/circl/sign/ed448"
)

func decode(fields []string) ([][]byte, error) {
	out := make([][]byte, len(fields))
	for i, f := range fields {
		if f == "-" {
			out[i] = []byte{}
			continue
		}
		b, err := hex.DecodeString(f)
		if err != nil {
			return nil, err
		}
		out[i] = b
	}
	return out, nil
}

func encode(b []byte) string {
	if len(b) == 0 {
		return "-"
	}
	return hex.EncodeToString(b)
}

func prehash(flag string) (bool, error) {
	switch flag {
	case "0":
		return false, nil
	case "1":
		return true, nil
	}
	return false, fmt.Errorf("invalid ph flag %q", flag)
}

func handle(fields []string) (string, error) {
	command, rest := fields[0], fields[1:]
	switch {
	case command == "x448" && len(rest) == 2:
		args, err := decode(rest)
		if err != nil {
			return "", err
		}
		if len(args[0]) != x448.Size || len(args[1]) != x448.Size {
			return "err", nil
		}
		var secret, public, shared x448.Key
		copy(secret[:], args[0])
		copy(public[:], args[1])
		if !x448.Shared(&shared, &secret, &public) {
			return "err", nil
		}
		return "ok " + encode(shared[:]), nil

	case command == "ed448-public" && len(rest) == 1:
		args, err := decode(rest)
		if err != nil {
			return "", err
		}
		if len(args[0]) != ed448.SeedSize {
			return "err", nil
		}
		priv := ed448.NewKeyFromSeed(args[0])
		return "ok " + encode(priv.Public().(ed448.PublicKey)), nil

	case command == "ed448-sign" && len(rest) == 4:
		ph, err := prehash(rest[0])
		if err != nil {
			return "", err
		}
		args, err := decode(rest[1:])
		if err != nil {
			return "", err
		}
		seed, ctx, msg := args[0], args[1], args[2]
		if len(seed) != ed448.SeedSize || len(ctx) > ed448.ContextMaxSize {
			return "err", nil
		}
		priv := ed448.NewKeyFromSeed(seed)
		if ph {
			return "ok " + encode(ed448.SignPh(priv, msg, string(ctx))), nil
		}
		return "ok " + encode(ed448.Sign(priv, msg, string(ctx))), nil

	case command == "ed448-verify" && len(rest) == 5:
		ph, err := prehash(rest[0])
		if err != nil {
			return "", err
		}
		args, err := decode(rest[1:])
		if err != nil {
			return "", err
		}
		pub, ctx, msg, sig := ed448.PublicKey(args[0]), args[1], args[2], args[3]
		var ok bool
		if ph {
			ok = ed448.VerifyPh(pub, msg, sig, string(ctx))
		} else {
			ok = ed448.Verify(pub, msg, sig, string(ctx))
		}
		if ok {
			return "ok 1", nil
		}
		return "ok 0", nil
	}
	return "", fmt.Errorf("malformed request %q", strings.Join(fields, " "))
}

func main() {
	in := bufio.NewScanner(os.Stdin)
	in.Buffer(make([]byte, 1<<20), 1<<24)
	out := bufio.NewWriter(os.Stdout)
	defer out.Flush()
	for in.Scan() {
		fields := strings.Fields(in.Text())
		if len(fields) == 0 {
			continue
		}
		response, err := handle(fields)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(2)
		}
		fmt.Fprintln(out, response)
		out.Flush()
	}
}
