# Constantine
# Copyright (c) 2018-2019    Status Research & Development GmbH
# Copyright (c) 2020-Present Mamy André-Ratsimbazafy
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at http://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at http://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

## ############################################################
##
##              Verkle Trie primitives for Ethereum
##
## ############################################################

import
  ./math/config/[type_ff, curves],
  ./math/arithmetic,
  ./math/elliptic/ec_twistededwards_projective,
  ./math/io/[io_bigints, io_fields],
  ./curves_primitives
  

func mapToBaseField*(dst: var Fp[Banderwagon],p: ECP_TwEdwards_Prj[Fp[Banderwagon]]) =
  ## The mapping chosen for the Banderwagon Curve is x/y
  ## 
  ## This function takes a Banderwagon element & then
  ## computes the x/y value and returns as an Fp element
  ## 
  ## Spec : https://hackmd.io/@6iQDuIePQjyYBqDChYw_jg/BJBNcv9fq#Map-To-Field
  
  var invY: Fp[Banderwagon]
  invY.inv(p.y)             # invY = 1/Y
  dst.prod(p.x, invY)       # dst = (X) * (1/Y)

func mapToScalarField*(res: var Fr[Banderwagon], p: ECP_TwEdwards_Prj[Fp[Banderwagon]]): bool {.discardable.} =
  ## This function takes the x/y value from the above function as Fp element 
  ## and convert that to bytes in Big Endian, 
  ## and then load that to a Fr element
  ## 
  ## Spec : https://hackmd.io/wliPP_RMT4emsucVuCqfHA?view#MapToFieldElement

  var baseField: Fp[Banderwagon]
  var baseFieldBytes: array[32, byte]
  
  baseField.mapToBaseField(p)   # compute the defined mapping

  let check1 = baseFieldBytes.marshalBE(baseField)  # Fp -> bytes
  let check2 = res.unmarshalBE(baseFieldBytes)      # bytes -> Fr

  return check1 and check2