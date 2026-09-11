import ProximityPrize.SubmissionLower.PartG009


section Compact_Sources80791
/-! Error-80791 phase ingredient, adapted from the promoted shared-product machinery.
No protocol claim is asserted in this module. -/
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Lower80791.SourceSound

open RCN095 RCN223 RCN260 RCN294 LocatorFactorAggregate
open Lower80791.FactorSwitch Lower80791.PowerRoute
open Lower80791.Oracle
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
def source : SourceNumbers := ⟨3840000, 88552, 19840, 134697356174643597939760⟩
def potential : Potential := ⟨3628897375341, 171187529499514, 775430912037326⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 30)
    (hy : middle p ≤ 136) (ht : total p ≤ 6917) :
    stageCost 3840000 88552 19840 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 3840000 88552 19840 (middle p) p.all (total p)) ≤
    3628897375341 * total p + 171187529499514 * middle p + 775430912037326 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 35651313 7733189 1813236215 3628897375341 171187529499514 775430912037326
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 35651313
    omega
  · change 131071*(2*p.all-1) ≤ 7733189
    omega
  · change 2*131071*total p+1 ≤ 1813236215
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 30)
    (hy : middle p ≤ 136) (ht : total p ≤ 6917) :
    HelperPairGates 3840000 88552 19840 (middle p) p.all (total p) := by
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
    Lower80791.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 11606592000
  m := 64000
  weighted := by decide
  shape := Kernels80791.Source00.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80791.Source00.finrank_gap u0 u1
end Phase00

namespace Phase01
def source : SourceNumbers := ⟨3200000, 44276, 9888, 16318384747680689397504⟩
def potential : Potential := ⟨1811474788749, 111245454594449, 506671412872542⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 30)
    (hy : middle p ≤ 136) (ht : total p ≤ 6917) :
    stageCost 3200000 44276 9888 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 3200000 44276 9888 (middle p) p.all (total p)) ≤
    1811474788749 * total p + 111245454594449 * middle p + 506671412872542 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 35651313 7733189 1813236215 1811474788749 111245454594449 506671412872542
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 35651313
    omega
  · change 131071*(2*p.all-1) ≤ 7733189
    omega
  · change 2*131071*total p+1 ≤ 1813236215
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 30)
    (hy : middle p ≤ 136) (ht : total p ≤ 6917) :
    HelperPairGates 3200000 44276 9888 (middle p) p.all (total p) := by
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
    Lower80791.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 5803296000
  m := 32000
  weighted := by decide
  shape := Kernels80791.Source01.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80791.Source01.finrank_gap u0 u1
end Phase01

namespace Phase02
def source : SourceNumbers := ⟨2880000, 44276, 9888, 14331250594091559797504⟩
def potential : Potential := ⟨1811474788749, 104794718144526, 476932423659072⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 30)
    (hy : middle p ≤ 136) (ht : total p ≤ 6917) :
    stageCost 2880000 44276 9888 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 2880000 44276 9888 (middle p) p.all (total p)) ≤
    1811474788749 * total p + 104794718144526 * middle p + 476932423659072 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 35651313 7733189 1813236215 1811474788749 104794718144526 476932423659072
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 35651313
    omega
  · change 131071*(2*p.all-1) ≤ 7733189
    omega
  · change 2*131071*total p+1 ≤ 1813236215
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 30)
    (hy : middle p ≤ 136) (ht : total p ≤ 6917) :
    HelperPairGates 2880000 44276 9888 (middle p) p.all (total p) := by
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
    Lower80791.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 5803296000
  m := 32000
  weighted := by decide
  shape := Kernels80791.Source02.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80791.Source02.finrank_gap u0 u1
end Phase02

namespace Phase03
def source : SourceNumbers := ⟨1062000, 22138, 4940, 599258578713824185407⟩
def potential : Potential := ⟨905365657010, 44758519646416, 203337030821125⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 30)
    (hy : middle p ≤ 136) (ht : total p ≤ 6917) :
    stageCost 1062000 22138 4940 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 1062000 22138 4940 (middle p) p.all (total p)) ≤
    905365657010 * total p + 44758519646416 * middle p + 203337030821125 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 35651313 7733189 1813236215 905365657010 44758519646416 203337030821125
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 35651313
    omega
  · change 131071*(2*p.all-1) ≤ 7733189
    omega
  · change 2*131071*total p+1 ≤ 1813236215
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 30)
    (hy : middle p ≤ 136) (ht : total p ≤ 6917) :
    HelperPairGates 1062000 22138 4940 (middle p) p.all (total p) := by
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
    Lower80791.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 2901648000
  m := 16000
  weighted := by decide
  shape := Kernels80791.Source03.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80791.Source03.finrank_gap u0 u1
end Phase03

namespace Phase04
def source : SourceNumbers := ⟨531000, 11069, 2470, 37145459499482470633⟩
def potential : Potential := ⟨452682828505, 22379259823208, 101668515410563⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 30)
    (hy : middle p ≤ 136) (ht : total p ≤ 6917) :
    stageCost 531000 11069 2470 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 531000 11069 2470 (middle p) p.all (total p)) ≤
    452682828505 * total p + 22379259823208 * middle p + 101668515410563 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 35651313 7733189 1813236215 452682828505 22379259823208 101668515410563
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 35651313
    omega
  · change 131071*(2*p.all-1) ≤ 7733189
    omega
  · change 2*131071*total p+1 ≤ 1813236215
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 30)
    (hy : middle p ≤ 136) (ht : total p ≤ 6917) :
    HelperPairGates 531000 11069 2470 (middle p) p.all (total p) := by
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
    Lower80791.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 1450824000
  m := 8000
  weighted := by decide
  shape := Kernels80791.Source04.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80791.Source04.finrank_gap u0 u1
end Phase04

namespace Phase05
def source : SourceNumbers := ⟨88902, 1383, 308, 11849708316198971⟩
def potential : Potential := ⟨56503053713, 3247974103979, 14799142114737⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 30)
    (hy : middle p ≤ 136) (ht : total p ≤ 6917) :
    stageCost 88902 1383 308 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 88902 1383 308 (middle p) p.all (total p)) ≤
    56503053713 * total p + 3247974103979 * middle p + 14799142114737 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 35651313 7733189 1813236215 56503053713 3247974103979 14799142114737
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 35651313
    omega
  · change 131071*(2*p.all-1) ≤ 7733189
    omega
  · change 2*131071*total p+1 ≤ 1813236215
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 30)
    (hy : middle p ≤ 136) (ht : total p ≤ 6917) :
    HelperPairGates 88902 1383 308 (middle p) p.all (total p) := by
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
    Lower80791.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 181353000
  m := 1000
  weighted := by decide
  shape := Kernels80791.Source05.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80791.Source05.finrank_gap u0 u1
end Phase05

end ProximityPrize.SubmissionLower.Lower80791.SourceSound

end Compact_Sources80791
