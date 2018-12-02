# Constantine
# Copyright (c) 2018 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at http://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at http://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

# ############################################################
#
#                 Field arithmetic over Fp
#
# ############################################################

# We assume that p is prime known at compile-time

import
  ./word_types, ./bigints

type
  Fp*[P: static BigInt] = object
    ## P is a prime number
    ## All operations on a field are modulo P
    value: type(P)

  Montgomery*[M: static BigInt] = object
    ## All operations in the Montgomery domain
    ## are modulo M. M **must** be odd
    value: type(M)

# ############################################################
#
#                         Aliases
#
# ############################################################

const
  True = ctrue(Limb)
  False = cfalse(Limb)

template add(a: var Fp, b: Fp, ctl: CTBool[Limb]): CTBool[Limb] =
  add(a.value, b.value, ctl)

template sub(a: var Fp, b: Fp, ctl: CTBool[Limb]): CTBool[Limb] =
  sub(a.value, b.value, ctl)

# ############################################################
#
#                Field arithmetic primitives
#
# ############################################################

func `+`*(a, b: Fp): Fp =
  ## Addition over Fp

  # Non-CT implementation from Stint
  #
  # let b_from_p = p - b    # Don't do a + b directly to avoid overflows
  # if a >= b_from_p:
  #   return a - b_from_p
  # return m - b_from_p + a

  result = a
  var ctl = add(result, b, True)
  ctl = ctl or not sub(result, Fp.P, False)
  sub(result, Fp.P, ctl)

# ############################################################
#
#                Montgomery domain primitives
#
# ############################################################

from bitops import fastLog2
  # This will only be used at compile-time
  # so no constant-time worries (it is constant-time if using the De Bruijn multiplication)

func montyMagic*(M: static BigInt): static Limb =
  ## Returns the Montgomery domain magic number for the input modulus:
  ##   -1/M[0] mod LimbSize
  ## M[0] is the least significant limb of M
  ## M must be odd and greater than 2.

  # Test vectors: https://www.researchgate.net/publication/4107322_Montgomery_modular_multiplication_architecture_for_public_key_cryptosystems
  # on p354
  # Reference C impl: http://www.hackersdelight.org/hdcodetxt/mont64.c.txt

  # ######################################################################
  # Implementation of modular multiplication inverse
  # Assuming 2 positive integers a and m the modulo
  #
  # We are looking for z that solves `az ≡ 1 mod m`
  #
  # References:
  #   - Knuth, The Art of Computer Programming, Vol2 p342
  #   - Menezes, Handbook of Applied Cryptography (HAC), p610
  #     http://cacr.uwaterloo.ca/hac/about/chap14.pdf

  # Starting from the extended GCD formula (Bezout identity),
  # `ax + by = gcd(x,y)` with input x,y and outputs a, b, gcd
  # We assume a and m are coprimes, i.e. gcd is 1, otherwise no inverse
  # `ax + my = 1` <=> `ax + my ≡ 1 mod m` <=> `ax ≡ 1 mod m`

  # For Montgomery magic number, we are in a special case
  # where a = M and m = 2^LimbSize.
  # For a and m to be coprimes, a must be odd.

  # M being a power of 2 greatly simplifies computation:
  #  - https://crypto.stackexchange.com/questions/47493/how-to-determine-the-multiplicative-inverse-modulo-64-or-other-power-of-two
  #  - http://groups.google.com/groups?selm=1994Apr6.093116.27805%40mnemosyne.cs.du.edu
  #  - https://mumble.net/~campbell/2015/01/21/inverse-mod-power-of-two
  #  - https://eprint.iacr.org/2017/411

  # We have the following relation
  # ax ≡ 1 (mod 2^k) <=> ax(2 - ax) ≡ 1 (mod 2^(2k))
  #
  # To get  -1/M0 mod LimbSize
  # we can either negate the resulting x of `ax(2 - ax) ≡ 1 (mod 2^(2k))`
  # or do ax(2 + ax) ≡ 1 (mod 2^(2k))

  const
    M0 = M.limbs[0]
    k = fastLog2(LimbBitSize)

  result = M0                # Start from an inverse of M0 modulo 2, M0 is odd and it's own inverse
  for _ in 0 ..< k:
    result *= 2 + M * result # x' = x(2 + ax) (`+` to avoid negating at the end)