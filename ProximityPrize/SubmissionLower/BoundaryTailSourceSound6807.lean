import ProximityPrize.SubmissionLower.BoundaryTailRouting6807
import ProximityPrize.SubmissionLower.BoundaryTailKernels80820

namespace ProximityPrize.SubmissionLower.Lower80820.SourceSound

open RCN095 RCN223 RCN260 RCN294 LocatorFactorAggregate
open Lower80820.FactorSwitch Lower80820.PowerRoute
open Lower80820.Oracle
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
def source : SourceNumbers := ⟨3840000, 88537, 19840, 123721060698960702830032⟩
def potential : Potential := ⟨3826877875752, 185672979054174, 854547464018333⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 31)
    (hy : middle p ≤ 146) (ht : total p ≤ 7784) :
    stageCost 3840000 88537 19840 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 3840000 88537 19840 (middle p) p.all (total p)) ≤
    3826877875752 * total p + 185672979054174 * middle p + 854547464018333 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 38272733 7995331 2040513329 3826877875752 185672979054174 854547464018333
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 38272733
    omega
  · change 131071*(2*p.all-1) ≤ 7995331
    omega
  · change 2*131071*total p+1 ≤ 2040513329
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 31)
    (hy : middle p ≤ 146) (ht : total p ≤ 7784) :
    HelperPairGates 3840000 88537 19840 (middle p) p.all (total p) := by
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
    Lower80820.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 11604736000
  m := 64000
  weighted := by decide
  shape := Kernels80820.Source00.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80820.Source00.finrank_gap u0 u1
end Phase00

namespace Phase01
def source : SourceNumbers := ⟨3200000, 44268, 9888, 15172279437860742596828⟩
def potential : Potential := ⟨1910234100596, 119359193790045, 555047483695215⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 31)
    (hy : middle p ≤ 146) (ht : total p ≤ 7784) :
    stageCost 3200000 44268 9888 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 3200000 44268 9888 (middle p) p.all (total p)) ≤
    1910234100596 * total p + 119359193790045 * middle p + 555047483695215 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 38272733 7995331 2040513329 1910234100596 119359193790045 555047483695215
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 38272733
    omega
  · change 131071*(2*p.all-1) ≤ 7995331
    omega
  · change 2*131071*total p+1 ≤ 2040513329
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 31)
    (hy : middle p ≤ 146) (ht : total p ≤ 7784) :
    HelperPairGates 3200000 44268 9888 (middle p) p.all (total p) := by
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
    Lower80820.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 5802368000
  m := 32000
  weighted := by decide
  shape := Kernels80820.Source01.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80820.Source01.finrank_gap u0 u1
end Phase01

namespace Phase02
def source : SourceNumbers := ⟨2880000, 44268, 9888, 13300640195063272516828⟩
def potential : Potential := ⟨1910234100596, 112685939527570, 523103380489379⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 31)
    (hy : middle p ≤ 146) (ht : total p ≤ 7784) :
    stageCost 2880000 44268 9888 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 2880000 44268 9888 (middle p) p.all (total p)) ≤
    1910234100596 * total p + 112685939527570 * middle p + 523103380489379 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 38272733 7995331 2040513329 1910234100596 112685939527570 523103380489379
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 38272733
    omega
  · change 131071*(2*p.all-1) ≤ 7995331
    omega
  · change 2*131071*total p+1 ≤ 2040513329
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 31)
    (hy : middle p ≤ 146) (ht : total p ≤ 7784) :
    HelperPairGates 2880000 44268 9888 (middle p) p.all (total p) := by
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
    Lower80820.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 5802368000
  m := 32000
  weighted := by decide
  shape := Kernels80820.Source02.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80820.Source02.finrank_gap u0 u1
end Phase02

namespace Phase03
def source : SourceNumbers := ⟨1062000, 22134, 4940, 551927092508496951255⟩
def potential : Potential := ⟨954717749008, 48438899067869, 223817718332796⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 31)
    (hy : middle p ≤ 146) (ht : total p ≤ 7784) :
    stageCost 1062000 22134 4940 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 1062000 22134 4940 (middle p) p.all (total p)) ≤
    954717749008 * total p + 48438899067869 * middle p + 223817718332796 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 38272733 7995331 2040513329 954717749008 48438899067869 223817718332796
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 38272733
    omega
  · change 131071*(2*p.all-1) ≤ 7995331
    omega
  · change 2*131071*total p+1 ≤ 2040513329
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 31)
    (hy : middle p ≤ 146) (ht : total p ≤ 7784) :
    HelperPairGates 1062000 22134 4940 (middle p) p.all (total p) := by
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
    Lower80820.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 2901184000
  m := 16000
  weighted := by decide
  shape := Kernels80820.Source03.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80820.Source03.finrank_gap u0 u1
end Phase03

namespace Phase04
def source : SourceNumbers := ⟨531000, 11067, 2470, 34186573997762259332⟩
def potential : Potential := ⟨477358874504, 24219449533935, 111908859166398⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 31)
    (hy : middle p ≤ 146) (ht : total p ≤ 7784) :
    stageCost 531000 11067 2470 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 531000 11067 2470 (middle p) p.all (total p)) ≤
    477358874504 * total p + 24219449533935 * middle p + 111908859166398 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 38272733 7995331 2040513329 477358874504 24219449533935 111908859166398
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 38272733
    omega
  · change 131071*(2*p.all-1) ≤ 7995331
    omega
  · change 2*131071*total p+1 ≤ 2040513329
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 31)
    (hy : middle p ≤ 146) (ht : total p ≤ 7784) :
    HelperPairGates 531000 11067 2470 (middle p) p.all (total p) := by
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
    Lower80820.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 1450592000
  m := 8000
  weighted := by decide
  shape := Kernels80820.Source04.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80820.Source04.finrank_gap u0 u1
end Phase04

namespace Phase05
def source : SourceNumbers := ⟨88902, 1383, 308, 10878251563318971⟩
def potential : Potential := ⟨59587170102, 3493215731957, 16235376583197⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 31)
    (hy : middle p ≤ 146) (ht : total p ≤ 7784) :
    stageCost 88902 1383 308 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 88902 1383 308 (middle p) p.all (total p)) ≤
    59587170102 * total p + 3493215731957 * middle p + 16235376583197 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 38272733 7995331 2040513329 59587170102 3493215731957 16235376583197
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 38272733
    omega
  · change 131071*(2*p.all-1) ≤ 7995331
    omega
  · change 2*131071*total p+1 ≤ 2040513329
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 31)
    (hy : middle p ≤ 146) (ht : total p ≤ 7784) :
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
    Lower80820.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 181324000
  m := 1000
  weighted := by decide
  shape := Kernels80820.Source05.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80820.Source05.finrank_gap u0 u1
end Phase05

namespace Phase06
def source : SourceNumbers := ⟨3640000, 19367, 4267, 1619857769496295783817⟩
def potential : Potential := ⟨829832511503, 98618412919545, 466440665988861⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 31)
    (hy : middle p ≤ 146) (ht : total p ≤ 7784) :
    stageCost 3640000 19367 4267 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 3640000 19367 4267 (middle p) p.all (total p)) ≤
    829832511503 * total p + 98618412919545 * middle p + 466440665988861 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 38272733 7995331 2040513329 829832511503 98618412919545 466440665988861
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 38272733
    omega
  · change 131071*(2*p.all-1) ≤ 7995331
    omega
  · change 2*131071*total p+1 ≤ 2040513329
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 31)
    (hy : middle p ≤ 146) (ht : total p ≤ 7784) :
    HelperPairGates 3640000 19367 4267 (middle p) p.all (total p) := by
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
    Lower80820.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 2538536000
  m := 14000
  weighted := by decide
  shape := Kernels80820.Source06.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80820.Source06.finrank_gap u0 u1
end Phase06

end ProximityPrize.SubmissionLower.Lower80820.SourceSound
