import ProximityPrize.SubmissionLower.BoundaryTailRouting
import ProximityPrize.SubmissionLower.BoundaryTailKernels

namespace ProximityPrize.SubmissionLower.Lower80801.SourceSound

open RCN095 RCN223 RCN260 RCN294 LocatorFactorAggregate
open Lower80801.FactorSwitch Lower80801.PowerRoute
open Lower80801.Oracle
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
def source : SourceNumbers := ⟨3840000, 88547, 19840, 130912206172909730640152⟩
def potential : Potential := ⟨3670198945596, 175045551504387, 800501756853143⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 30)
    (hy : middle p ≤ 139) (ht : total p ≤ 7199) :
    stageCost 3840000 88547 19840 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 3840000 88547 19840 (middle p) p.all (total p)) ≤
    3670198945596 * total p + 175045551504387 * middle p + 800501756853143 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 36437739 7733189 1887160259 3670198945596 175045551504387 800501756853143
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 36437739
    omega
  · change 131071*(2*p.all-1) ≤ 7733189
    omega
  · change 2*131071*total p+1 ≤ 1887160259
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 30)
    (hy : middle p ≤ 139) (ht : total p ≤ 7199) :
    HelperPairGates 3840000 88547 19840 (middle p) p.all (total p) := by
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
    Lower80801.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 11605952000
  m := 64000
  weighted := by decide
  shape := Kernels80801.Source00.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80801.Source00.finrank_gap u0 u1
end Phase00

namespace Phase01
def source : SourceNumbers := ⟨3200000, 44273, 9888, 15923153328235812072568⟩
def potential : Potential := ⟨1832049287276, 113173400483686, 521852587885969⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 30)
    (hy : middle p ≤ 139) (ht : total p ≤ 7199) :
    stageCost 3200000 44273 9888 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 3200000 44273 9888 (middle p) p.all (total p)) ≤
    1832049287276 * total p + 113173400483686 * middle p + 521852587885969 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 36437739 7733189 1887160259 1832049287276 113173400483686 521852587885969
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 36437739
    omega
  · change 131071*(2*p.all-1) ≤ 7733189
    omega
  · change 2*131071*total p+1 ≤ 1887160259
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 30)
    (hy : middle p ≤ 139) (ht : total p ≤ 7199) :
    HelperPairGates 3200000 44273 9888 (middle p) p.all (total p) := by
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
    Lower80801.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 5802976000
  m := 32000
  weighted := by decide
  shape := Kernels80801.Source01.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80801.Source01.finrank_gap u0 u1
end Phase01

namespace Phase02
def source : SourceNumbers := ⟨2880000, 44273, 9888, 13975847306980794792568⟩
def potential : Potential := ⟨1832049287276, 106721380866900, 491451545467465⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 30)
    (hy : middle p ≤ 139) (ht : total p ≤ 7199) :
    stageCost 2880000 44273 9888 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 2880000 44273 9888 (middle p) p.all (total p)) ≤
    1832049287276 * total p + 106721380866900 * middle p + 491451545467465 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 36437739 7733189 1887160259 1832049287276 106721380866900 491451545467465
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 36437739
    omega
  · change 131071*(2*p.all-1) ≤ 7733189
    omega
  · change 2*131071*total p+1 ≤ 1887160259
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 30)
    (hy : middle p ≤ 139) (ht : total p ≤ 7199) :
    HelperPairGates 2880000 44273 9888 (middle p) p.all (total p) := by
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
    Lower80801.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 5802976000
  m := 32000
  weighted := by decide
  shape := Kernels80801.Source02.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80801.Source02.finrank_gap u0 u1
end Phase02

namespace Phase03
def source : SourceNumbers := ⟨1062000, 22136, 4940, 582936452425414639575⟩
def potential : Potential := ⟨915634549327, 45719560544166, 209812081162255⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 30)
    (hy : middle p ≤ 139) (ht : total p ≤ 7199) :
    stageCost 1062000 22136 4940 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 1062000 22136 4940 (middle p) p.all (total p)) ≤
    915634549327 * total p + 45719560544166 * middle p + 209812081162255 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 36437739 7733189 1887160259 915634549327 45719560544166 209812081162255
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 36437739
    omega
  · change 131071*(2*p.all-1) ≤ 7733189
    omega
  · change 2*131071*total p+1 ≤ 1887160259
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 30)
    (hy : middle p ≤ 139) (ht : total p ≤ 7199) :
    HelperPairGates 1062000 22136 4940 (middle p) p.all (total p) := by
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
    Lower80801.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 2901488000
  m := 16000
  weighted := by decide
  shape := Kernels80801.Source03.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80801.Source03.finrank_gap u0 u1
end Phase03

namespace Phase04
def source : SourceNumbers := ⟨531000, 11068, 2470, 36125109589474230633⟩
def potential : Potential := ⟨457817274664, 22859780272083, 104906040581128⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 30)
    (hy : middle p ≤ 139) (ht : total p ≤ 7199) :
    stageCost 531000 11068 2470 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 531000 11068 2470 (middle p) p.all (total p)) ≤
    457817274664 * total p + 22859780272083 * middle p + 104906040581128 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 36437739 7733189 1887160259 457817274664 22859780272083 104906040581128
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 36437739
    omega
  · change 131071*(2*p.all-1) ≤ 7733189
    omega
  · change 2*131071*total p+1 ≤ 1887160259
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 30)
    (hy : middle p ≤ 139) (ht : total p ≤ 7199) :
    HelperPairGates 531000 11068 2470 (middle p) p.all (total p) := by
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
    Lower80801.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 1450744000
  m := 8000
  weighted := by decide
  shape := Kernels80801.Source04.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80801.Source04.finrank_gap u0 u1
end Phase04

namespace Phase05
def source : SourceNumbers := ⟨88902, 1383, 308, 11514723228998971⟩
def potential : Potential := ⟨57145825610, 3307984230542, 15250933241027⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 30)
    (hy : middle p ≤ 139) (ht : total p ≤ 7199) :
    stageCost 88902 1383 308 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 88902 1383 308 (middle p) p.all (total p)) ≤
    57145825610 * total p + 3307984230542 * middle p + 15250933241027 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 36437739 7733189 1887160259 57145825610 3307984230542 15250933241027
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 36437739
    omega
  · change 131071*(2*p.all-1) ≤ 7733189
    omega
  · change 2*131071*total p+1 ≤ 1887160259
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 30)
    (hy : middle p ≤ 139) (ht : total p ≤ 7199) :
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
    Lower80801.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 181343000
  m := 1000
  weighted := by decide
  shape := Kernels80801.Source05.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80801.Source05.finrank_gap u0 u1
end Phase05

end ProximityPrize.SubmissionLower.Lower80801.SourceSound
