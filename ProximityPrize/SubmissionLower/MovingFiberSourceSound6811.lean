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
def source : SourceNumbers := ⟨3840000, 88518, 19840, 108584552282495392041818⟩
def potential : Potential := ⟨4248303575247, 216573403547093, 979597711315188⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 35)
    (hy : middle p ≤ 159) (ht : total p ≤ 9275) :
    stageCost 3840000 88518 19840 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 3840000 88518 19840 (middle p) p.all (total p)) ≤
    4248303575247 * total p + 216573403547093 * middle p + 979597711315188 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 41680579 9043899 2431367051 4248303575247 216573403547093 979597711315188
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 41680579
    omega
  · change 131071*(2*p.all-1) ≤ 9043899
    omega
  · change 2*131071*total p+1 ≤ 2431367051
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 35)
    (hy : middle p ≤ 159) (ht : total p ≤ 9275) :
    HelperPairGates 3840000 88518 19840 (middle p) p.all (total p) := by
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
  D := 11602176000
  m := 64000
  weighted := by decide
  shape := MovingFiberKernels6811.Source00.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6811.Source00.finrank_gap u0 u1
end Phase00

namespace Phase01
def source : SourceNumbers := ⟨3200000, 44259, 9888, 13591780916835376840288⟩
def potential : Potential := ⟨2120670172245, 138301398086505, 629063470797534⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 35)
    (hy : middle p ≤ 159) (ht : total p ≤ 9275) :
    stageCost 3200000 44259 9888 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 3200000 44259 9888 (middle p) p.all (total p)) ≤
    2120670172245 * total p + 138301398086505 * middle p + 629063470797534 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 41680579 9043899 2431367051 2120670172245 138301398086505 629063470797534
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 41680579
    omega
  · change 131071*(2*p.all-1) ≤ 9043899
    omega
  · change 2*131071*total p+1 ≤ 2431367051
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 35)
    (hy : middle p ≤ 159) (ht : total p ≤ 9275) :
    HelperPairGates 3200000 44259 9888 (middle p) p.all (total p) := by
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
  D := 5801088000
  m := 32000
  weighted := by decide
  shape := MovingFiberKernels6811.Source01.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6811.Source01.finrank_gap u0 u1
end Phase01

namespace Phase02
def source : SourceNumbers := ⟨2880000, 44259, 9888, 11879410888491090760288⟩
def potential : Potential := ⟨2120670172245, 130746949804972, 594247317012549⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 35)
    (hy : middle p ≤ 159) (ht : total p ≤ 9275) :
    stageCost 2880000 44259 9888 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 2880000 44259 9888 (middle p) p.all (total p)) ≤
    2120670172245 * total p + 130746949804972 * middle p + 594247317012549 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 41680579 9043899 2431367051 2120670172245 130746949804972 594247317012549
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 41680579
    omega
  · change 131071*(2*p.all-1) ≤ 9043899
    omega
  · change 2*131071*total p+1 ≤ 2431367051
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 35)
    (hy : middle p ≤ 159) (ht : total p ≤ 9275) :
    HelperPairGates 2880000 44259 9888 (middle p) p.all (total p) := by
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
  D := 5801088000
  m := 32000
  weighted := by decide
  shape := MovingFiberKernels6811.Source02.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6811.Source02.finrank_gap u0 u1
end Phase02

namespace Phase03
def source : SourceNumbers := ⟨1062000, 22129, 4940, 486656012723084560935⟩
def potential : Potential := ⟨1059888080375, 56424395768278, 255993903460056⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 35)
    (hy : middle p ≤ 159) (ht : total p ≤ 9275) :
    stageCost 1062000 22129 4940 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 1062000 22129 4940 (middle p) p.all (total p)) ≤
    1059888080375 * total p + 56424395768278 * middle p + 255993903460056 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 41680579 9043899 2431367051 1059888080375 56424395768278 255993903460056
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 41680579
    omega
  · change 131071*(2*p.all-1) ≤ 9043899
    omega
  · change 2*131071*total p+1 ≤ 2431367051
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 35)
    (hy : middle p ≤ 159) (ht : total p ≤ 9275) :
    HelperPairGates 1062000 22129 4940 (middle p) p.all (total p) := by
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
  D := 2900544000
  m := 16000
  weighted := by decide
  shape := MovingFiberKernels6811.Source03.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6811.Source03.finrank_gap u0 u1
end Phase03

namespace Phase04
def source : SourceNumbers := ⟨531000, 11064, 2470, 30106196192731244355⟩
def potential : Potential := ⟨529932236362, 28212197884139, 127993778342322⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 35)
    (hy : middle p ≤ 159) (ht : total p ≤ 9275) :
    stageCost 531000 11064 2470 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 531000 11064 2470 (middle p) p.all (total p)) ≤
    529932236362 * total p + 28212197884139 * middle p + 127993778342322 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 41680579 9043899 2431367051 529932236362 28212197884139 127993778342322
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 41680579
    omega
  · change 131071*(2*p.all-1) ≤ 9043899
    omega
  · change 2*131071*total p+1 ≤ 2431367051
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 35)
    (hy : middle p ≤ 159) (ht : total p ≤ 9275) :
    HelperPairGates 531000 11064 2470 (middle p) p.all (total p) := by
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
  D := 1450272000
  m := 8000
  weighted := by decide
  shape := MovingFiberKernels6811.Source04.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6811.Source04.finrank_gap u0 u1
end Phase04

namespace Phase05
def source : SourceNumbers := ⟨88902, 1383, 308, 9538311214518971⟩
def potential : Potential := ⟨66159929185, 4053574205328, 18450170718773⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 35)
    (hy : middle p ≤ 159) (ht : total p ≤ 9275) :
    stageCost 88902 1383 308 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 88902 1383 308 (middle p) p.all (total p)) ≤
    66159929185 * total p + 4053574205328 * middle p + 18450170718773 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 41680579 9043899 2431367051 66159929185 4053574205328 18450170718773
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 41680579
    omega
  · change 131071*(2*p.all-1) ≤ 9043899
    omega
  · change 2*131071*total p+1 ≤ 2431367051
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 35)
    (hy : middle p ≤ 159) (ht : total p ≤ 9275) :
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
    Lower80860.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 181284000
  m := 1000
  weighted := by decide
  shape := MovingFiberKernels6811.Source05.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6811.Source05.finrank_gap u0 u1
end Phase05

namespace Phase06
def source : SourceNumbers := ⟨3640000, 19363, 4267, 1470377603249816254829⟩
def potential : Potential := ⟨921366594613, 113013539884289, 518926361601498⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 35)
    (hy : middle p ≤ 159) (ht : total p ≤ 9275) :
    stageCost 3640000 19363 4267 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 3640000 19363 4267 (middle p) p.all (total p)) ≤
    921366594613 * total p + 113013539884289 * middle p + 518926361601498 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 41680579 9043899 2431367051 921366594613 113013539884289 518926361601498
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 41680579
    omega
  · change 131071*(2*p.all-1) ≤ 9043899
    omega
  · change 2*131071*total p+1 ≤ 2431367051
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 35)
    (hy : middle p ≤ 159) (ht : total p ≤ 9275) :
    HelperPairGates 3640000 19363 4267 (middle p) p.all (total p) := by
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
  D := 2537976000
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
