import ProximityPrize.SubmissionLower.BoundaryTailRouting6808
import ProximityPrize.SubmissionLower.BoundaryTailKernels80830

namespace ProximityPrize.SubmissionLower.Lower80840.SourceSound

open RCN095 RCN223 RCN260 RCN294 LocatorFactorAggregate
open Lower80840.FactorSwitch Lower80840.PowerRoute
open Lower80840.Oracle
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
def source : SourceNumbers := ⟨3840000, 88528, 19840, 116152340868634539327888⟩
def potential : Potential := ⟨4030745590214, 200486002112969, 912926409500727⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 33)
    (hy : middle p ≤ 152) (ht : total p ≤ 8483) :
    stageCost 3840000 88528 19840 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 3840000 88528 19840 (middle p) p.all (total p)) ≤
    4030745590214 * total p + 200486002112969 * middle p + 912926409500727 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 39845585 8519615 2223750587 4030745590214 200486002112969 912926409500727
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 39845585
    omega
  · change 131071*(2*p.all-1) ≤ 8519615
    omega
  · change 2*131071*total p+1 ≤ 2223750587
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 33)
    (hy : middle p ≤ 152) (ht : total p ≤ 8483) :
    HelperPairGates 3840000 88528 19840 (middle p) p.all (total p) := by
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
    Lower80840.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 11603456000
  m := 64000
  weighted := by decide
  shape := Kernels80840.Source00.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80840.Source00.finrank_gap u0 u1
end Phase00

namespace Phase01
def source : SourceNumbers := ⟨3200000, 44264, 9888, 14381981301127046791888⟩
def potential : Potential := ⟨2012045783549, 128512023988326, 589543667081150⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 33)
    (hy : middle p ≤ 152) (ht : total p ≤ 8483) :
    stageCost 3200000 44264 9888 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 3200000 44264 9888 (middle p) p.all (total p)) ≤
    2012045783549 * total p + 128512023988326 * middle p + 589543667081150 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 39845585 8519615 2223750587 2012045783549 128512023988326 589543667081150
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 39845585
    omega
  · change 131071*(2*p.all-1) ≤ 8519615
    omega
  · change 2*131071*total p+1 ≤ 2223750587
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 33)
    (hy : middle p ≤ 152) (ht : total p ≤ 8483) :
    HelperPairGates 3200000 44264 9888 (middle p) p.all (total p) := by
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
    Lower80840.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 5801728000
  m := 32000
  weighted := by decide
  shape := Kernels80840.Source01.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80840.Source01.finrank_gap u0 u1
end Phase01

namespace Phase02
def source : SourceNumbers := ⟨2880000, 44264, 9888, 12589981621733099911888⟩
def potential : Potential := ⟨2012045783549, 121398348137662, 556273551498453⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 33)
    (hy : middle p ≤ 152) (ht : total p ≤ 8483) :
    stageCost 2880000 44264 9888 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 2880000 44264 9888 (middle p) p.all (total p)) ≤
    2012045783549 * total p + 121398348137662 * middle p + 556273551498453 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 39845585 8519615 2223750587 2012045783549 121398348137662 556273551498453
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 39845585
    omega
  · change 131071*(2*p.all-1) ≤ 8519615
    omega
  · change 2*131071*total p+1 ≤ 2223750587
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 33)
    (hy : middle p ≤ 152) (ht : total p ≤ 8483) :
    HelperPairGates 2880000 44264 9888 (middle p) p.all (total p) := by
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
    Lower80840.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 5801728000
  m := 32000
  weighted := by decide
  shape := Kernels80840.Source02.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80840.Source02.finrank_gap u0 u1
end Phase02

namespace Phase03
def source : SourceNumbers := ⟨1062000, 22132, 4940, 519289470505939163247⟩
def potential : Potential := ⟨1005607015330, 52272934411383, 238836451717167⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 33)
    (hy : middle p ≤ 152) (ht : total p ≤ 8483) :
    stageCost 1062000 22132 4940 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 1062000 22132 4940 (middle p) p.all (total p)) ≤
    1005607015330 * total p + 52272934411383 * middle p + 238836451717167 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 39845585 8519615 2223750587 1005607015330 52272934411383 238836451717167
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 39845585
    omega
  · change 131071*(2*p.all-1) ≤ 8519615
    omega
  · change 2*131071*total p+1 ≤ 2223750587
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 33)
    (hy : middle p ≤ 152) (ht : total p ≤ 8483) :
    HelperPairGates 1062000 22132 4940 (middle p) p.all (total p) := by
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
    Lower80840.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 2900864000
  m := 16000
  weighted := by decide
  shape := Kernels80840.Source03.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80840.Source03.finrank_gap u0 u1
end Phase03

namespace Phase04
def source : SourceNumbers := ⟨531000, 11066, 2470, 32146246142741674440⟩
def potential : Potential := ⟨502803507665, 26136467205692, 119418225858584⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 33)
    (hy : middle p ≤ 152) (ht : total p ≤ 8483) :
    stageCost 531000 11066 2470 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 531000 11066 2470 (middle p) p.all (total p)) ≤
    502803507665 * total p + 26136467205692 * middle p + 119418225858584 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 39845585 8519615 2223750587 502803507665 26136467205692 119418225858584
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 39845585
    omega
  · change 131071*(2*p.all-1) ≤ 8519615
    omega
  · change 2*131071*total p+1 ≤ 2223750587
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 33)
    (hy : middle p ≤ 152) (ht : total p ≤ 8483) :
    HelperPairGates 531000 11066 2470 (middle p) p.all (total p) := by
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
    Lower80840.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 1450432000
  m := 8000
  weighted := by decide
  shape := Kernels80840.Source04.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80840.Source04.finrank_gap u0 u1
end Phase04

namespace Phase05
def source : SourceNumbers := ⟨88902, 1383, 308, 10208281388918971⟩
def potential : Potential := ⟨62766904066, 3763487064327, 17267939771556⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 33)
    (hy : middle p ≤ 152) (ht : total p ≤ 8483) :
    stageCost 88902 1383 308 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 88902 1383 308 (middle p) p.all (total p)) ≤
    62766904066 * total p + 3763487064327 * middle p + 17267939771556 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 39845585 8519615 2223750587 62766904066 3763487064327 17267939771556
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 39845585
    omega
  · change 131071*(2*p.all-1) ≤ 8519615
    omega
  · change 2*131071*total p+1 ≤ 2223750587
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 33)
    (hy : middle p ≤ 152) (ht : total p ≤ 8483) :
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
    Lower80840.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 181304000
  m := 1000
  weighted := by decide
  shape := Kernels80840.Source05.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80840.Source05.finrank_gap u0 u1
end Phase05

namespace Phase06
def source : SourceNumbers := ⟨3640000, 19365, 4267, 1545113083611437217999⟩
def potential : Potential := ⟨874124737624, 105677393081476, 490813262169523⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 33)
    (hy : middle p ≤ 152) (ht : total p ≤ 8483) :
    stageCost 3640000 19365 4267 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 3640000 19365 4267 (middle p) p.all (total p)) ≤
    874124737624 * total p + 105677393081476 * middle p + 490813262169523 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 39845585 8519615 2223750587 874124737624 105677393081476 490813262169523
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 39845585
    omega
  · change 131071*(2*p.all-1) ≤ 8519615
    omega
  · change 2*131071*total p+1 ≤ 2223750587
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 33)
    (hy : middle p ≤ 152) (ht : total p ≤ 8483) :
    HelperPairGates 3640000 19365 4267 (middle p) p.all (total p) := by
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
    Lower80840.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 2538256000
  m := 14000
  weighted := by decide
  shape := Kernels80840.Source06.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80840.Source06.finrank_gap u0 u1
end Phase06

end ProximityPrize.SubmissionLower.Lower80840.SourceSound
