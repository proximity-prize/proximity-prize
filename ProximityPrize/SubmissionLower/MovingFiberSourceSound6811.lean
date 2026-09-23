import ProximityPrize.SubmissionLower.MovingFiberRouting6811
import ProximityPrize.SubmissionLower.MovingFiberKernels6811

namespace ProximityPrize.SubmissionLower.Lower80860.SourceSound

open RCN095 RCN223 RCN260 RCN294 LocatorFactorAggregate
open Lower80860.FactorSwitch Lower80860.PowerRoute
open Lower80860.Oracle
open LocatorPhase6800Oracle (Potential)

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem helperPair_regularCountCap_mono_right
    (L₁ Y₁ S₁ L₂ Y₂ S₂ leftY leftR leftZ : ℕ)
    (hL : L₁ ≤ L₂) (hY : Y₁ ≤ Y₂) (hS : S₁ ≤ S₂) :
    AsymmetricHelper.leftRegularCountCap (helperPair L₁ Y₁ S₁ leftY leftR leftZ) ≤
      AsymmetricHelper.leftRegularCountCap (helperPair L₂ Y₂ S₂ leftY leftR leftZ) := by
  let P₁ := helperPair L₁ Y₁ S₁ leftY leftR leftZ
  let P₂ := helperPair L₂ Y₂ S₂ leftY leftR leftZ
  have ha : vectorLE P₁.leftAgreement P₂.leftAgreement := by
    exact ⟨le_rfl, le_rfl, le_rfl⟩
  have hm : vectorLE P₁.mixedCost P₂.mixedCost := by
    refine ⟨?_, ?_, ?_⟩
    · exact Nat.add_le_add (Nat.mul_le_mul_left leftR hL)
        (Nat.mul_le_mul_left leftZ hS)
    · exact Nat.add_le_add (Nat.mul_le_mul_left leftY hL)
        (Nat.mul_le_mul_left leftZ hY)
    · exact Nat.add_le_add (Nat.mul_le_mul_left leftY hS)
        (Nat.mul_le_mul_left leftR hY)
  have hdot : dot P₁.leftAgreement P₁.mixedCost ≤
      dot P₂.leftAgreement P₂.mixedCost := by
    unfold dot
    exact Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul ha.1 hm.1)
        (Nat.mul_le_mul ha.2.1 hm.2.1))
      (Nat.mul_le_mul ha.2.2 hm.2.2)
  have hnum : AsymmetricHelper.leftRegularNumerator P₁ ≤ AsymmetricHelper.leftRegularNumerator P₂ := by
    unfold AsymmetricHelper.leftRegularNumerator
    exact Nat.add_le_add (Nat.mul_le_mul_left (P₁.n - P₁.w) hdot)
      (Nat.mul_le_mul_left ((P₁.errors + 1) * P₁.gap) hm.2.2)
  exact Nat.div_le_div_right hnum

theorem stageCost_le_stageZero (L YS S : ℕ) (p : FlagDegree) (j : ℕ) :
    stageCost L YS S (exactRouteBox p) j ≤
      stageCost L YS S (exactRouteBox p) 0 := by
  apply helperPair_regularCountCap_mono_right
  · simpa only [exactRouteBox, Nat.zero_mul, Nat.sub_zero] using
      Nat.sub_le L (j * total p)
  · simpa only [exactRouteBox, Nat.zero_mul, Nat.sub_zero] using
      Nat.sub_le YS (j * middle p)
  · simpa only [exactRouteBox, Nat.zero_mul, Nat.sub_zero] using
      Nat.sub_le S (j * p.all)

theorem helperPair_gates_of_right_le
    (L₁ Y₁ S₁ L₂ Y₂ S₂ leftY leftR leftZ : ℕ)
    (hL : L₁ ≤ L₂) (hY : Y₁ ≤ Y₂) (hS : S₁ ≤ S₂)
    (hgate : HelperPairGates L₂ Y₂ S₂ leftY leftR leftZ) :
    HelperPairGates L₁ Y₁ S₁ leftY leftR leftZ := by
  rcases hgate with ⟨hr, hy, hs, hz, hmy, hmr, hmz⟩
  refine ⟨hr, hy, hs, hz, ?_, ?_, ?_⟩
  · exact (Nat.add_le_add (Nat.mul_le_mul_left leftR hL)
      (Nat.mul_le_mul_left leftZ hS)).trans_lt hmy
  · exact (Nat.add_le_add (Nat.mul_le_mul_left leftY hL)
      (Nat.mul_le_mul_left leftZ hY)).trans_lt hmr
  · exact (Nat.add_le_add (Nat.mul_le_mul_left leftY hS)
      (Nat.mul_le_mul_left leftR hY)).trans_lt hmz

theorem stageGates_of_stageZero (L YS S : ℕ) (p : FlagDegree) (j : ℕ)
    (hgate : HelperPairGates L YS S (middle p) p.all (total p)) :
    HelperPairGates (L - j * total p) (YS - j * middle p)
      (S - j * p.all) (middle p) p.all (total p) := by
  apply helperPair_gates_of_right_le
  · exact Nat.sub_le _ _
  · exact Nat.sub_le _ _
  · exact Nat.sub_le _ _
  · exact hgate


namespace Phase00
def source : SourceNumbers := ⟨3840000, 88507, 19840, 101393982016661871992662⟩
def potential : Potential := ⟨4473213367672, 231425648505470, 1065606529399036⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 36)
    (hy : middle p ≤ 171) (ht : total p ≤ 10169) :
    stageCost 3840000 88507 19840 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 3840000 88507 19840 (middle p) p.all (total p)) ≤
    4473213367672 * total p + 231425648505470 * middle p + 1065606529399036 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 44826283 9306041 2665721999 4473213367672 231425648505470 1065606529399036
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 44826283
    omega
  · change 131071*(2*p.all-1) ≤ 9306041
    omega
  · change 2*131071*total p+1 ≤ 2665721999
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 36)
    (hy : middle p ≤ 171) (ht : total p ≤ 10169) :
    HelperPairGates 3840000 88507 19840 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  constructor
  · exact hr
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  constructor <;> nlinarith

def sound : PhaseSourceSound where
  source := source
  potential := potential
  stageCost_le := by
    intro p j hr hs hy ht _hj
    exact (stageCost_le_stageZero _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates := by
    intro p j hr hs hy ht _hj
    exact stageGates_of_stageZero _ _ _ p j (stageZero_gates p hr hs hy ht)

noncomputable def kernel (u0 u1 : ProximityPrize.Benchmark.IRSProfile.Index → ProximityPrize.Benchmark.IRSProfile.Field) :
    Lower80860.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 11600778735
  m := 63999
  weighted := by decide
  shape := MovingFiberKernels6811.Source00.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6811.Source00.finrank_gap u0 u1
end Phase00

namespace Phase01
def source : SourceNumbers := ⟨3200000, 44254, 9888, 12841180931961412995338⟩
def potential : Potential := ⟨2232873038237, 146595508392165, 682638591739466⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 36)
    (hy : middle p ≤ 171) (ht : total p ≤ 10169) :
    stageCost 3200000 44254 9888 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 3200000 44254 9888 (middle p) p.all (total p)) ≤
    2232873038237 * total p + 146595508392165 * middle p + 682638591739466 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 44826283 9306041 2665721999 2232873038237 146595508392165 682638591739466
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 44826283
    omega
  · change 131071*(2*p.all-1) ≤ 9306041
    omega
  · change 2*131071*total p+1 ≤ 2665721999
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 36)
    (hy : middle p ≤ 171) (ht : total p ≤ 10169) :
    HelperPairGates 3200000 44254 9888 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  constructor
  · exact hr
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  constructor <;> nlinarith

def sound : PhaseSourceSound where
  source := source
  potential := potential
  stageCost_le := by
    intro p j hr hs hy ht _hj
    exact (stageCost_le_stageZero _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates := by
    intro p j hr hs hy ht _hj
    exact stageGates_of_stageZero _ _ _ p j (stageZero_gates p hr hs hy ht)

noncomputable def kernel (u0 u1 : ProximityPrize.Benchmark.IRSProfile.Index → ProximityPrize.Benchmark.IRSProfile.Field) :
    Lower80860.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 5800480000
  m := 32000
  weighted := by decide
  shape := MovingFiberKernels6811.Source01.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6811.Source01.finrank_gap u0 u1
end Phase01

namespace Phase02
def source : SourceNumbers := ⟨2880000, 44254, 9888, 11204449907338779715338⟩
def potential : Potential := ⟨2232873038237, 138819148113292, 645180630123917⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 36)
    (hy : middle p ≤ 171) (ht : total p ≤ 10169) :
    stageCost 2880000 44254 9888 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 2880000 44254 9888 (middle p) p.all (total p)) ≤
    2232873038237 * total p + 138819148113292 * middle p + 645180630123917 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 44826283 9306041 2665721999 2232873038237 138819148113292 645180630123917
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 44826283
    omega
  · change 131071*(2*p.all-1) ≤ 9306041
    omega
  · change 2*131071*total p+1 ≤ 2665721999
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 36)
    (hy : middle p ≤ 171) (ht : total p ≤ 10169) :
    HelperPairGates 2880000 44254 9888 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  constructor
  · exact hr
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  constructor <;> nlinarith

def sound : PhaseSourceSound where
  source := source
  potential := potential
  stageCost_le := by
    intro p j hr hs hy ht _hj
    exact (stageCost_le_stageZero _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates := by
    intro p j hr hs hy ht _hj
    exact stageGates_of_stageZero _ _ _ p j (stageZero_gates p hr hs hy ht)

noncomputable def kernel (u0 u1 : ProximityPrize.Benchmark.IRSProfile.Index → ProximityPrize.Benchmark.IRSProfile.Field) :
    Lower80860.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 5800480000
  m := 32000
  weighted := by decide
  shape := MovingFiberKernels6811.Source02.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6811.Source02.finrank_gap u0 u1
end Phase02

namespace Phase03
def source : SourceNumbers := ⟨1062000, 22127, 4940, 455657858798922476937⟩
def potential : Potential := ⟨1115968294599, 60195903855219, 278343097903591⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 36)
    (hy : middle p ≤ 171) (ht : total p ≤ 10169) :
    stageCost 1062000 22127 4940 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 1062000 22127 4940 (middle p) p.all (total p)) ≤
    1115968294599 * total p + 60195903855219 * middle p + 278343097903591 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 44826283 9306041 2665721999 1115968294599 60195903855219 278343097903591
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 44826283
    omega
  · change 131071*(2*p.all-1) ≤ 9306041
    omega
  · change 2*131071*total p+1 ≤ 2665721999
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 36)
    (hy : middle p ≤ 171) (ht : total p ≤ 10169) :
    HelperPairGates 1062000 22127 4940 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  constructor
  · exact hr
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  constructor <;> nlinarith

def sound : PhaseSourceSound where
  source := source
  potential := potential
  stageCost_le := by
    intro p j hr hs hy ht _hj
    exact (stageCost_le_stageZero _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates := by
    intro p j hr hs hy ht _hj
    exact stageGates_of_stageZero _ _ _ p j (stageZero_gates p hr hs hy ht)

noncomputable def kernel (u0 u1 : ProximityPrize.Benchmark.IRSProfile.Index → ProximityPrize.Benchmark.IRSProfile.Field) :
    Lower80860.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 2900240000
  m := 16000
  weighted := by decide
  shape := MovingFiberKernels6811.Source03.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6811.Source03.finrank_gap u0 u1
end Phase03

namespace Phase04
def source : SourceNumbers := ⟨531000, 11063, 2470, 28168374562350357398⟩
def potential : Potential := ⟨557971996737, 30097951927610, 139168068374045⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 36)
    (hy : middle p ≤ 171) (ht : total p ≤ 10169) :
    stageCost 531000 11063 2470 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 531000 11063 2470 (middle p) p.all (total p)) ≤
    557971996737 * total p + 30097951927610 * middle p + 139168068374045 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 44826283 9306041 2665721999 557971996737 30097951927610 139168068374045
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 44826283
    omega
  · change 131071*(2*p.all-1) ≤ 9306041
    omega
  · change 2*131071*total p+1 ≤ 2665721999
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 36)
    (hy : middle p ≤ 171) (ht : total p ≤ 10169) :
    HelperPairGates 531000 11063 2470 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  constructor
  · exact hr
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  constructor <;> nlinarith

def sound : PhaseSourceSound where
  source := source
  potential := potential
  stageCost_le := by
    intro p j hr hs hy ht _hj
    exact (stageCost_le_stageZero _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates := by
    intro p j hr hs hy ht _hj
    exact stageGates_of_stageZero _ _ _ p j (stageZero_gates p hr hs hy ht)

noncomputable def kernel (u0 u1 : ProximityPrize.Benchmark.IRSProfile.Index → ProximityPrize.Benchmark.IRSProfile.Field) :
    Lower80860.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 1450120000
  m := 8000
  weighted := by decide
  shape := MovingFiberKernels6811.Source04.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6811.Source04.finrank_gap u0 u1
end Phase04

namespace Phase05
def source : SourceNumbers := ⟨88902, 1382, 308, 8902002865622491⟩
def potential : Potential := ⟨69637444010, 4304454586832, 20026840977296⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 36)
    (hy : middle p ≤ 171) (ht : total p ≤ 10169) :
    stageCost 88902 1382 308 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 88902 1382 308 (middle p) p.all (total p)) ≤
    69637444010 * total p + 4304454586832 * middle p + 20026840977296 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 44826283 9306041 2665721999 69637444010 4304454586832 20026840977296
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 44826283
    omega
  · change 131071*(2*p.all-1) ≤ 9306041
    omega
  · change 2*131071*total p+1 ≤ 2665721999
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 36)
    (hy : middle p ≤ 171) (ht : total p ≤ 10169) :
    HelperPairGates 88902 1382 308 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  constructor
  · exact hr
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  constructor <;> nlinarith

def sound : PhaseSourceSound where
  source := source
  potential := potential
  stageCost_le := by
    intro p j hr hs hy ht _hj
    exact (stageCost_le_stageZero _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates := by
    intro p j hr hs hy ht _hj
    exact stageGates_of_stageZero _ _ _ p j (stageZero_gates p hr hs hy ht)

noncomputable def kernel (u0 u1 : ProximityPrize.Benchmark.IRSProfile.Index → ProximityPrize.Benchmark.IRSProfile.Field) :
    Lower80860.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 181265000
  m := 1000
  weighted := by decide
  shape := MovingFiberKernels6811.Source05.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6811.Source05.finrank_gap u0 u1
end Phase05

namespace Phase06
def source : SourceNumbers := ⟨3640000, 19361, 4267, 1399387463065701121859⟩
def potential : Potential := ⟨969972604916, 118159348699069, 560859245050424⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 36)
    (hy : middle p ≤ 171) (ht : total p ≤ 10169) :
    stageCost 3640000 19361 4267 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 3640000 19361 4267 (middle p) p.all (total p)) ≤
    969972604916 * total p + 118159348699069 * middle p + 560859245050424 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 44826283 9306041 2665721999 969972604916 118159348699069 560859245050424
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 44826283
    omega
  · change 131071*(2*p.all-1) ≤ 9306041
    omega
  · change 2*131071*total p+1 ≤ 2665721999
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 36)
    (hy : middle p ≤ 171) (ht : total p ≤ 10169) :
    HelperPairGates 3640000 19361 4267 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  constructor
  · exact hr
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  constructor <;> nlinarith

def sound : PhaseSourceSound where
  source := source
  potential := potential
  stageCost_le := by
    intro p j hr hs hy ht _hj
    exact (stageCost_le_stageZero _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates := by
    intro p j hr hs hy ht _hj
    exact stageGates_of_stageZero _ _ _ p j (stageZero_gates p hr hs hy ht)

noncomputable def kernel (u0 u1 : ProximityPrize.Benchmark.IRSProfile.Index → ProximityPrize.Benchmark.IRSProfile.Field) :
    Lower80860.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 2537710000
  m := 14000
  weighted := by decide
  shape := MovingFiberKernels6811.Source06.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6811.Source06.finrank_gap u0 u1
end Phase06

end ProximityPrize.SubmissionLower.Lower80860.SourceSound

#print axioms ProximityPrize.SubmissionLower.Lower80860.SourceSound.Phase00.kernel
#print axioms ProximityPrize.SubmissionLower.Lower80860.SourceSound.Phase06.sound
