import ProximityPrize.SubmissionLower.Z6970H2307OrderLookup
import ProximityPrize.SubmissionLower.Z6970H2307OrderCore
import ProximityPrize.SubmissionLower.Z6970H2307Bands
import ProximityPrize.SubmissionLower.Z6970H2307OrderBand00
import ProximityPrize.SubmissionLower.Bundle6970_36a8fd39217e3575
import ProximityPrize.SubmissionLower.Bundle6970_36a8fd39217e3575
import ProximityPrize.SubmissionLower.Bundle6970_36a8fd39217e3575
import ProximityPrize.SubmissionLower.Bundle6970_d8256c03b5c1e743
import ProximityPrize.SubmissionLower.Bundle6970_d8256c03b5c1e743
import ProximityPrize.SubmissionLower.Bundle6970_d8256c03b5c1e743
import ProximityPrize.SubmissionLower.Bundle6970_d8256c03b5c1e743
import ProximityPrize.SubmissionLower.Bundle6970_d8256c03b5c1e743
import ProximityPrize.SubmissionLower.Bundle6970_bedb8f5433cafeef
import ProximityPrize.SubmissionLower.Bundle6970_bedb8f5433cafeef
import ProximityPrize.SubmissionLower.Bundle6970_bedb8f5433cafeef
import ProximityPrize.SubmissionLower.Bundle6970_bedb8f5433cafeef
import ProximityPrize.SubmissionLower.Bundle6970_bedb8f5433cafeef
import ProximityPrize.SubmissionLower.Bundle6970_03a5a060fb8866f2
import ProximityPrize.SubmissionLower.Bundle6970_03a5a060fb8866f2
import ProximityPrize.SubmissionLower.Bundle6970_03a5a060fb8866f2
import ProximityPrize.SubmissionLower.Bundle6970_03a5a060fb8866f2
import ProximityPrize.SubmissionLower.Bundle6970_03a5a060fb8866f2
import ProximityPrize.SubmissionLower.Bundle6970_03a5a060fb8866f2
import ProximityPrize.SubmissionLower.Bundle6970_5a0db8abbc67ea80
import ProximityPrize.SubmissionLower.Bundle6970_5a0db8abbc67ea80
import ProximityPrize.SubmissionLower.Bundle6970_5a0db8abbc67ea80
import ProximityPrize.SubmissionLower.Bundle6970_5a0db8abbc67ea80
import ProximityPrize.SubmissionLower.Bundle6970_5a0db8abbc67ea80
import ProximityPrize.SubmissionLower.Bundle6970_5a0db8abbc67ea80
import ProximityPrize.SubmissionLower.Bundle6970_5a0db8abbc67ea80
import ProximityPrize.SubmissionLower.Bundle6970_5a0db8abbc67ea80
import ProximityPrize.SubmissionLower.Bundle6970_23ebbbdda2260a1b
import ProximityPrize.SubmissionLower.Bundle6970_23ebbbdda2260a1b
import ProximityPrize.SubmissionLower.Bundle6970_23ebbbdda2260a1b
import ProximityPrize.SubmissionLower.Bundle6970_23ebbbdda2260a1b
import ProximityPrize.SubmissionLower.Bundle6970_23ebbbdda2260a1b
import ProximityPrize.SubmissionLower.Bundle6970_23ebbbdda2260a1b
import ProximityPrize.SubmissionLower.Bundle6970_23ebbbdda2260a1b
import ProximityPrize.SubmissionLower.Bundle6970_23ebbbdda2260a1b
import ProximityPrize.SubmissionLower.Bundle6970_23ebbbdda2260a1b
import ProximityPrize.SubmissionLower.Bundle6970_23ebbbdda2260a1b
import ProximityPrize.SubmissionLower.Bundle6970_23ebbbdda2260a1b
import ProximityPrize.SubmissionLower.Bundle6970_23ebbbdda2260a1b
import ProximityPrize.SubmissionLower.Bundle6970_23ebbbdda2260a1b
import ProximityPrize.SubmissionLower.Bundle6970_23ebbbdda2260a1b

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

open Height2307Bands

theorem thresholds_valid (k : Band) : (thresholds k).all (checked (start k)) = true := by
  fin_cases k
  · exact band0_valid
  · exact band1_valid
  · exact band2_valid
  · exact band3_valid
  · exact band4_valid
  · exact band5_valid
  · exact band6_valid
  · exact band7_valid
  · exact band8_valid
  · exact band9_valid
  · exact band10_valid
  · exact band11_valid
  · exact band12_valid
  · exact band13_valid
  · exact band14_valid
  · exact band15_valid
  · exact band16_valid
  · exact band17_valid
  · exact band18_valid
  · exact band19_valid
  · exact band20_valid
  · exact band21_valid
  · exact band22_valid
  · exact band23_valid
  · exact band24_valid
  · exact band25_valid
  · exact band26_valid
  · exact band27_valid
  · exact band28_valid
  · exact band29_valid
  · exact band30_valid
  · exact band31_valid
  · exact band32_valid
  · exact band33_valid
  · exact band34_valid
  · exact band35_valid
  · exact band36_valid
  · exact band37_valid
  · exact band38_valid
  · exact band39_valid
  · exact band40_valid
  · exact band41_valid

theorem order_valid (k : Band) (x : K1_13.Shape) :
    0<order k x.b x.j ∧
      (order k x.b x.j=1 ∨
        Height2307Inventory.availableMass (start k) x (order k x.b x.j-1) < 21230822871131) :=
  lookup_order_valid (start k) x (thresholds k) (thresholds_valid k)



end Height2307Orders
