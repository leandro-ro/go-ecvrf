// Copyright (c) 2020 vechain.org.
// Licensed under the MIT license.

package ecvrf

import (
	"crypto/elliptic"
	"errors"
	"hash"
	"math/big"

	"github.com/decred/dcrd/dcrec/secp256k1/v4"
	ethsecp "github.com/ethereum/go-ethereum/crypto/secp256k1"
)

type Point struct {
	X, Y *big.Int
}

type Core struct {
	*Config
	cachedHasher hash.Hash
}

// Q returns prime order of large prime order subgroup.
func (c *Core) Q() *big.Int {
	return c.Curve.Params().N
}

// N return half of length, in octets, of a field element in F, rounded up to the nearest even integer
func (c *Core) N() int {
	return ((c.Curve.Params().P.BitLen()+1)/2 + 7) / 8
}

func (c *Core) getHasher() hash.Hash {
	if c.cachedHasher == nil {
		c.cachedHasher = c.NewHasher()
	} else {
		c.cachedHasher.Reset()
	}
	return c.cachedHasher
}

// Marshal marshals a Point into compressed form specified in section 4.3.6 of ANSI X9.62.
// It's the alias of `point_to_string` specified in [draft-irtf-cfrg-VrfImpl-06 section 5.5](https://tools.ietf.org/id/draft-irtf-cfrg-vrf-06.html#rfc.section.5.5).
func (c *Core) Marshal(pt *Point) []byte {
	return elliptic.MarshalCompressed(c.Curve, pt.X, pt.Y)
}

// Unmarshal unmarshals a compressed Point in the form specified in section 4.3.6 of ANSI X9.62.
// It's the alias of `string_to_point` specified in [draft-irtf-cfrg-VrfImpl-06 section 5.5](https://tools.ietf.org/id/draft-irtf-cfrg-vrf-06.html#rfc.section.5.5).
// This is borrowed from the project https://github.com/google/keytransparency.
func (c *Core) Unmarshal(in []byte) *Point {
	if x, y := c.Decompress(c.Curve, in); x != nil && y != nil {
		return &Point{x, y}
	}
	return nil
}

func (c *Core) ScalarMult(pt *Point, k []byte) *Point {
	// Use ethsecp only for secp256k1
	if c.Curve.Params().Name == "secp256k1" {
		x, y := ethsecp.S256().ScalarMult(pt.X, pt.Y, k)
		return &Point{X: x, Y: y}
	}

	// Fallback: Build-In Curve-Multiplikation
	x, y := c.Curve.ScalarMult(pt.X, pt.Y, k)
	return &Point{X: x, Y: y}
}

func (c *Core) ScalarBaseMult(k []byte) *Point {
	if c.Curve.Params().Name == "secp256k1" {
		x, y := ethsecp.S256().ScalarBaseMult(k)
		return &Point{X: x, Y: y}
	}
	x, y := c.Curve.ScalarBaseMult(k)
	return &Point{X: x, Y: y}
}
func (c *Core) Add(pt1, pt2 *Point) *Point {
	x, y := c.Curve.Add(pt1.X, pt1.Y, pt2.X, pt2.Y)
	return &Point{x, y}
}

func (c *Core) Sub(pt1, pt2 *Point) *Point {
	// pt1 - pt2 = pt1 + invert(pt2),
	// where invert(pt2) = (x2, P - y2)
	x, y := c.Curve.Add(
		pt1.X, pt1.Y,
		pt2.X, new(big.Int).Sub(c.Curve.Params().P, pt2.Y))
	return &Point{x, y}
}

// HashToCurveTryAndIncrement takes in the VRF input `alpha` and converts it to H, using the try_and_increment algorithm.
// See: [draft-irtf-cfrg-VrfImpl-06 section 5.4.1.1](https://tools.ietf.org/id/draft-irtf-cfrg-vrf-06.html#rfc.section.5.4.1.1).
func (c *Core) HashToCurveTryAndIncrement(pk *Point, alpha []byte) (*Point, error) {
	hasher := c.getHasher()
	hash := make([]byte, 1+hasher.Size())
	hash[0] = 2 // compress format

	// step 1: ctr = 0
	ctr := 0

	// step 2: PK_string = point_to_string(Y)
	pkBytes := c.Marshal(pk)

	// step 3 ~ 6
	prefix := []byte{c.SuiteString, 0x01}
	suffix := []byte{0}
	for ; ctr < 256; ctr++ {
		// hash_string = Hash(suite_string || one_string || PK_string || alpha_string || ctr_string)
		suffix[0] = byte(ctr)
		hasher.Reset()
		hasher.Write(prefix)
		hasher.Write(pkBytes)
		hasher.Write(alpha)
		hasher.Write(suffix)
		// apppend right after compress format
		hasher.Sum(hash[1:1])

		// H = arbitrary_string_to_point(hash_string)
		if H := c.Unmarshal(hash); H != nil {
			if c.Cofactor > 1 {
				// If H is not "INVALID" and cofactor > 1, set H = cofactor * H
				H = c.ScalarMult(H, []byte{c.Cofactor})
			}
			return H, nil
		}
	}
	return nil, errors.New("no valid Point found")
}

// See: [draft-irtf-cfrg-VrfImpl-06 section 5.4.3](https://tools.ietf.org/id/draft-irtf-cfrg-vrf-06.html#rfc.section.5.4.3)
func (c *Core) HashPoints(points ...*Point) *big.Int {
	hasher := c.getHasher()
	hasher.Write([]byte{c.SuiteString, 0x2})
	for _, pt := range points {
		hasher.Write(c.Marshal(pt))
	}
	return bits2int(hasher.Sum(nil), c.N()*8)
}

func (c *Core) GammaToHash(gamma *Point) []byte {
	gammaCof := gamma
	if c.Cofactor != 1 {
		gammaCof = c.ScalarMult(gamma, []byte{c.Cofactor})
	}
	hasher := c.getHasher()
	hasher.Write([]byte{c.SuiteString, 0x03})
	hasher.Write(c.Marshal(gammaCof))
	return hasher.Sum(nil)
}

func (c *Core) EncodeProof(gamma *Point, C, S *big.Int) []byte {
	gammaBytes := c.Marshal(gamma)

	cbytes := int2octets(C, c.N())
	sbytes := int2octets(S, (c.Q().BitLen()+7)/8)

	return append(append(gammaBytes, cbytes...), sbytes...)
}

// See: [draft-irtf-cfrg-VrfImpl-06 section 5.4.4](https://tools.ietf.org/id/draft-irtf-cfrg-vrf-06.html#rfc.section.5.4.4)
func (c *Core) DecodeProof(pi []byte) (gamma *Point, C, S *big.Int, err error) {
	var (
		ptlen = (c.Curve.Params().BitSize+7)/8 + 1
		clen  = c.N()
		slen  = (c.Q().BitLen() + 7) / 8
	)
	if len(pi) != ptlen+clen+slen {
		err = errors.New("invalid proof length")
		return
	}

	if gamma = c.Unmarshal(pi[:ptlen]); gamma == nil {
		err = errors.New("invalid Point")
		return
	}

	C = new(big.Int).SetBytes(pi[ptlen : ptlen+clen])
	S = new(big.Int).SetBytes(pi[ptlen+clen:])
	return
}

// rfc6979nonce generates nonce according to [RFC6979](https://tools.ietf.org/html/rfc6979).
func (c *Core) rfc6979nonce(sk *big.Int, m []byte) []byte {
	var (
		q      = c.Q()
		qlen   = q.BitLen()
		rolen  = (qlen + 7) / 8
		hasher = c.getHasher()
	)

	// Step A
	// Process m through the hash function H, yielding:
	// h1 = H(m)
	// (h1 is a sequence of hlen bits).
	hasher.Write(m)
	bx := int2octets(sk, rolen)
	bh := bits2octets(hasher.Sum(nil), q, rolen)

	nonce := secp256k1.NonceRFC6979(bx, bh, nil, nil, 0).Bytes()
	return nonce[:]
}

// https://tools.ietf.org/html/rfc6979#section-2.3.2
func bits2int(in []byte, qlen int) *big.Int {
	out := new(big.Int).SetBytes(in)
	if inlen := len(in) * 8; inlen > qlen {
		return out.Rsh(out, uint(inlen-qlen))
	}
	return out
}

// https://tools.ietf.org/html/rfc6979#section-2.3.3
func int2octets(v *big.Int, rolen int) []byte {
	var (
		out    = v.Bytes()
		outlen = len(out)
	)

	// left pad with zeros if it's too short
	if rolen > outlen {
		out2 := make([]byte, rolen)
		copy(out2[rolen-outlen:], out)
		return out2
	}

	// drop most significant bytes if it's too long
	return out[outlen-rolen:]
}

// https://tools.ietf.org/html/rfc6979#section-2.3.4
func bits2octets(in []byte, q *big.Int, rolen int) []byte {
	z1 := bits2int(in, q.BitLen())
	z2 := new(big.Int).Sub(z1, q)
	if z2.Sign() < 0 {
		return int2octets(z1, rolen)
	}
	return int2octets(z2, rolen)
}
