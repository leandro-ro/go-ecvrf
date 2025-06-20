// Copyright (c) 2020 vechain.org.
// Licensed under the MIT license.

// Package ecvrf is the Elliptic Curve Verifiable Random Function (VRF) library.
package ecvrf

import (
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/sha256"
	"errors"
	"math/big"

	"github.com/decred/dcrd/dcrec/secp256k1/v4"
)

// VRF is the interface that wraps VRF methods.
type VRF interface {
	// Prove constructs a VRF proof `pi` for the given input `alpha`,
	// using the private key `sk`. The hash output is returned as `beta`.
	Prove(sk *ecdsa.PrivateKey, alpha []byte) (beta, pi []byte, err error)

	// Verify checks the proof `pi` of the message `alpha` against the given
	// public key `pk`. The hash output is returned as `beta`.
	Verify(pk *ecdsa.PublicKey, alpha, pi []byte) (beta []byte, err error)

	Eval(sk *ecdsa.PrivateKey, alpha []byte) (beta []byte, err error)
}

var (
	// Secp256k1Sha256Tai is the pre-configured VRF object with secp256k1/SHA256 and hash_to_curve_try_and_increment algorithm.
	Secp256k1Sha256Tai = New(&Config{
		Curve:       secp256k1.S256(),
		SuiteString: 0xfe,
		Cofactor:    0x01,
		NewHasher:   sha256.New,
		Decompress: func(c elliptic.Curve, pk []byte) (x, y *big.Int) {
			var fx, fy secp256k1.FieldVal
			// Reject unsupported public key formats for the given length.
			format := pk[0]
			switch format {
			case secp256k1.PubKeyFormatCompressedEven, secp256k1.PubKeyFormatCompressedOdd:
			default:
				return
			}

			// Parse the x coordinate while ensuring that it is in the allowed
			// range.
			if overflow := fx.SetByteSlice(pk[1:33]); overflow {
				return
			}

			// Attempt to calculate the y coordinate for the given x coordinate such
			// that the result pair is a Point on the secp256k1 curve and the
			// solution with desired oddness is chosen.
			wantOddY := format == secp256k1.PubKeyFormatCompressedOdd
			if !secp256k1.DecompressY(&fx, wantOddY, &fy) {
				return
			}
			fy.Normalize()
			return new(big.Int).SetBytes(fx.Bytes()[:]), new(big.Int).SetBytes(fy.Bytes()[:])
		},
	})
	// P256Sha256Tai is the pre-configured VRF object with P256/SHA256 and hash_to_curve_try_and_increment algorithm.
	P256Sha256Tai = New(&Config{
		Curve:       elliptic.P256(),
		SuiteString: 0x01,
		Cofactor:    0x01,
		NewHasher:   sha256.New,
		Decompress:  elliptic.UnmarshalCompressed,
	})
)

// New creates and initializes a VRF object using customized config.
func New(cfg *Config) VRF {
	return &VrfImpl{Config: *cfg}
}

type VrfImpl struct {
	Config Config
}

// Prove constructs VRF proof following [draft-irtf-cfrg-VrfImpl-06 section 5.1](https://tools.ietf.org/id/draft-irtf-cfrg-vrf-06.html#rfc.section.5.1).
func (v *VrfImpl) Prove(sk *ecdsa.PrivateKey, alpha []byte) (beta, pi []byte, err error) {
	var (
		core = Core{Config: &v.Config}
		q    = core.Q()
	)

	// step 1 is done by the caller.

	// step 2: H = ECVRF_hash_to_curve(suite_string, Y, alpha_string)
	// currently, try_and_increment algorithm is supported
	H, err := core.HashToCurveTryAndIncrement(&Point{sk.X, sk.Y}, alpha)
	if err != nil {
		return
	}

	// step 3: h_string = point_to_string(H)
	hbytes := core.Marshal(H)

	// step 4: Gamma = x * H
	gamma := core.ScalarMult(H, sk.D.Bytes())

	// step 5: k = ECVRF_nonce_generation(SK, h_string)
	// it follows RFC6979
	kbytes := core.rfc6979nonce(sk.D, hbytes)
	k := new(big.Int).SetBytes(kbytes)

	// step 6: c = ECVRF_hash_points(H, Gamma, k*B, k*H)
	kB := core.ScalarBaseMult(kbytes)
	kH := core.ScalarMult(H, kbytes)
	c := core.HashPoints(
		H,
		gamma,
		kB,
		kH)

	// step 7: s = (k + c*x) mod q
	s := new(big.Int).Mul(c, sk.D)
	s.Add(s, k)
	s.Mod(s, q)

	// step 8: encode (gamma, c, s) as pi_string = point_to_string(Gamma) || int_to_string(c, n) || int_to_string(s, qLen)
	pi = core.EncodeProof(gamma, c, s)

	// step 9: Output pi_string
	// here also returns beta
	beta = core.GammaToHash(gamma)
	return
}

func (v *VrfImpl) Eval(sk *ecdsa.PrivateKey, alpha []byte) (beta []byte, err error) {
	core := Core{Config: &v.Config}

	// Step 2: H = ECVRF_hash_to_curve(suite_string, Y, alpha_string)
	H, err := core.HashToCurveTryAndIncrement(&Point{sk.X, sk.Y}, alpha)
	if err != nil {
		return nil, err
	}

	// Step 4: Gamma = x * H
	gamma := core.ScalarMult(H, sk.D.Bytes())

	// Step 9: beta = ECVRF_hash_output(Gamma)
	beta = core.GammaToHash(gamma)
	return beta, nil
}

// Verify checks the correctness of proof following [draft-irtf-cfrg-VrfImpl-06 section 5.3](https://tools.ietf.org/id/draft-irtf-cfrg-vrf-06.html#rfc.section.5.3).
func (v *VrfImpl) Verify(pk *ecdsa.PublicKey, alpha, pi []byte) (beta []byte, err error) {
	core := Core{Config: &v.Config}
	// step 1: D = ECVRF_decode_proof(pi_string)
	gamma, c, s, err := core.DecodeProof(pi)

	// step 2: If D is "INVALID", output "INVALID" and stop
	if err != nil {
		return
	}
	// step 3: (Gamma, c, s) = D

	// step 4: H = ECVRF_hash_to_curve(suite_string, Y, alpha_string)
	H, err := core.HashToCurveTryAndIncrement(&Point{pk.X, pk.Y}, alpha)
	if err != nil {
		return
	}

	// step 5: U = s*B - c*Y
	sB := core.ScalarBaseMult(s.Bytes())
	cY := core.ScalarMult(&Point{pk.X, pk.Y}, c.Bytes())
	U := core.Sub(sB, cY)

	// step 6: V = s*H - c*Gamma
	sH := core.ScalarMult(H, s.Bytes())
	cGamma := core.ScalarMult(gamma, c.Bytes())
	V := core.Sub(sH, cGamma)

	// step 7: c' = ECVRF_hash_points(H, Gamma, U, V)
	derivedC := core.HashPoints(H, gamma, U, V)

	// step 8: If c and c' are equal, output ("VALID", ECVRF_proof_to_hash(pi_string)); else output "INVALID"
	if derivedC.Cmp(c) != 0 {
		err = errors.New("invalid proof")
		return
	}

	beta = core.GammaToHash(gamma)
	return
}
