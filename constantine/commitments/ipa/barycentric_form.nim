# Constantine
# Copyright (c) 2018-2019    Status Research & Development GmbH
# Copyright (c) 2020-Present Mamy André-Ratsimbazafy
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at http://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at http://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.
import 
 ../../../constantine/math/config/[type_ff, curves],
 ../../../constantine/math/elliptic/ec_twistededwards_projective,
 ../../../constantine/math/arithmetic/[finite_fields, bigints,bigints_montgomery]

# ############################################################
#
#       Barycentric Form using Precompute Optimisation
#
# ############################################################

# Please refer to https://hackmd.io/mJeCRcawTRqr9BooVpHv5g 
type 
 PrecomputedWeights = object
  barycentricWeights: seq[ECP_TwEdwards_Prj[Fp[Banderwagon]]]
  invertedDomain: seq[ECP_TwEdwards_Prj[Fp[Banderwagon]]]

# The domain size shall always be equal to 256, because this the degree of the polynomial we want to commit to
const
 DOMAIN: uint64 = 256


proc barycentric_weights (element : var uint64) : ECP_TwEdwards_Prj[Fp[Banderwagon]] = 
 if element > DOMAIN:
  echo"The domain is [0,255], and $element is not in the domain"

 var domain_element_Fp: ECP_TwEdwards_Prj[Fp[Banderwagon]]
#  var conv_domain_element_Fp: uint64 = cast[uint64](domain_element_Fp)

 var total : ECP_TwEdwards_Prj[Fp[Banderwagon]]

 total.x.setOne()
 total.y.setOne()
 total.z.setOne()

 for i in uint64(0)..DOMAIN:
  if i == element:
    continue

  var i_Fp: ECP_TwEdwards_Prj[Fp[Banderwagon]] = cast[ECP_TwEdwards_Prj[Fp[Banderwagon]]](i)
  # var conv_i_Fp: uint64 = cast[uint64](i_Fp)
  var temp : ECP_TwEdwards_Prj[Fp[Banderwagon]]
  temp.diff(domain_element_Fp,i_Fp)

  total.x.prod(total.x,temp.x)
  total.y.prod(total.y,temp.y)
  total.z.prod(total.z,temp.z)
  
 return total



func new_precomputed_weights* [PrecomputedWeightsObj: var PrecomputedWeights] () : PrecomputedWeights =
 var midpoint: uint64 = DOMAIN
 var barycentricWeightsInst {.noInit.} : seq[ECP_TwEdwards_Prj[Fp[Banderwagon]]] = newSeq[ECP_TwEdwards_Prj[Fp[Banderwagon]]](midpoint * 2)
 
 for i in uint64(0)..midpoint:
  var weights : ECP_TwEdwards_Prj[Fp[Banderwagon]] = barycentric_weights(i)

  var inverseWeights : ECP_TwEdwards_Prj[Fp[Banderwagon]]

  inverseWeights.x.inv(weights.x)
  inverseWeights.y.inv(weights.y)
  inverseWeights.z.inv(weights.z)


  barycentricWeightsInst[i].x = weights.x
  barycentricWeightsInst[i].y = weights.y
  barycentricWeightsInst[i].z = weights.z

  barycentricWeightsInst[i+midpoint].x = inverseWeights.x
  barycentricWeightsInst[i+midpoint].y = inverseWeights.y
  barycentricWeightsInst[i+midpoint].z = inverseWeights.z

  midpoint = DOMAIN - 1
  var invertedDomain: seq[ECP_TwEdwards_Prj[Fp[Banderwagon]]] = newSeq[ECP_TwEdwards_Prj[Fp[Banderwagon]]](midpoint * 2)

  for i in uint64(0)..DOMAIN:
   var k: ECP_TwEdwards_Prj[Fp[Banderwagon]] = cast[ECP_TwEdwards_Prj[Fp[Banderwagon]]](i)

   k.x.inv(k.x)
   k.y.inv(k.y)
   k.z.inv(k.z)

   var neg_k : ECP_TwEdwards_Prj[Fp[Banderwagon]]

   var zero : ECP_TwEdwards_Prj[Fp[Banderwagon]]

   zero.x.setZero()
   zero.y.setZero()
   zero.z.setZero()

   neg_k.diff(zero, k)

   invertedDomain[i-1].x = k.x
   invertedDomain[i-1].y = k.y
   invertedDomain[i-1].z = k.z

   invertedDomain[(i-1) + midpoint].x = neg_k.x
   invertedDomain[(i-1) + midpoint].y = neg_k.y
   invertedDomain[(i-1) + midpoint].z = neg_k.z
   PrecomputedWeightsObj = {barycentricWeightsInst, invertedDomain}

   return PrecomputedWeightsObj

# func BatchInversion(points : seq[ECP_TwEdwards_Prj[Fp[Banderwagon]]]) : seq[ECP_TwEdwards_Prj[Fp[Banderwagon]]] =
#  var result : array[len(points),ECP_TwEdwards_Prj[Fp[Banderwagon]]]

func compute_barycentric_coefficients* [PrecomputedWeightsObj]( point : ECP_TwEdwards_Prj[Fp[Banderwagon]]): seq[ECP_TwEdwards_Prj[Fp[Banderwagon]]] =
 var lagrangeEval : array[DOMAIN, ECP_TwEdwards_Prj[Fp[Banderwagon]]]

 for i in uint64(0)..DOMAIN:
  var weight = PrecomputedWeightsObj.barycentricWeights[i]
  var i_Fp: ECP_TwEdwards_Prj[Fp[Banderwagon]] = cast[ECP_TwEdwards_Prj[Fp[Banderwagon]]](i)
  
  lagrangeEval[i].diff(point, i_Fp)

  lagrangeEval[i].x.prod(lagrangeEval[i].x,weight.x)
  lagrangeEval[i].y.prod(lagrangeEval[i].y,weight.y)
  lagrangeEval[i].z.prod(lagrangeEval[i].z,weight.z)
  
var totalProd : ECP_TwEdwards_Prj[Fp[Banderwagon]]

totalProd.x.setOne()
totalProd.y.setOne()
totalProd.z.setOne()

for i in uint64(0)..DOMAIN:
 var i_fr {.noInit.} : ECP_TwEdwards_Prj[Fp[Banderwagon]]




   
