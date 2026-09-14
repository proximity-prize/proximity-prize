import ProximityPrize.SubmissionLower.BoundaryTailRouting6808
import ProximityPrize.SubmissionLower.BoundaryTailKernels80830

namespace ProximityPrize.SubmissionLower.Lower80830.SourceSound

open RCN095 RCN223 RCN260 RCN294 LocatorFactorAggregate
open Lower80830.FactorSwitch Lower80830.PowerRoute
open Lower80830.Oracle
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
def source : SourceNumbers := ⟨3840000, 88533, 19840, 119936584085811789477372⟩
def potential : Potential := ⟨3928805293203, 192908416399544, 882978169271437⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 32)
    (hy : middle p ≤ 149) (ht : total p ≤ 8121) :
    stageCost 3840000 88533 19840 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 3840000 88533 19840 (middle p) p.all (total p)) ≤
    3928805293203 * total p + 192908416399544 * middle p + 882978169271437 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 39059159 8257473 2128855183 3928805293203 192908416399544 882978169271437
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 39059159
    omega
  · change 131071*(2*p.all-1) ≤ 8257473
    omega
  · change 2*131071*total p+1 ≤ 2128855183
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 32)
    (hy : middle p ≤ 149) (ht : total p ≤ 8121) :
    HelperPairGates 3840000 88533 19840 (middle p) p.all (total p) := by
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
    Lower80830.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 11604096000
  m := 64000
  weighted := by decide
  shape := Kernels80830.Source00.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80830.Source00.finrank_gap u0 u1
end Phase00

namespace Phase01
def source : SourceNumbers := ⟨3200000, 44266, 9888, 14777118577657165926174⟩
def potential : Potential := ⟨1961131177888, 123850171558372, 571914217473899⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 32)
    (hy : middle p ≤ 149) (ht : total p ≤ 8121) :
    stageCost 3200000 44266 9888 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 3200000 44266 9888 (middle p) p.all (total p)) ≤
    1961131177888 * total p + 123850171558372 * middle p + 571914217473899 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 39059159 8257473 2128855183 1961131177888 123850171558372 571914217473899
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 39059159
    omega
  · change 131071*(2*p.all-1) ≤ 8257473
    omega
  · change 2*131071*total p+1 ≤ 2128855183
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 32)
    (hy : middle p ≤ 149) (ht : total p ≤ 8121) :
    HelperPairGates 3200000 44266 9888 (middle p) p.all (total p) := by
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
    Lower80830.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 5802048000
  m := 32000
  weighted := by decide
  shape := Kernels80830.Source01.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80830.Source01.finrank_gap u0 u1
end Phase01

namespace Phase02
def source : SourceNumbers := ⟨2880000, 44266, 9888, 12945300312285541286174⟩
def potential : Potential := ⟨1961131177888, 116956750330952, 539307240039545⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 32)
    (hy : middle p ≤ 149) (ht : total p ≤ 8121) :
    stageCost 2880000 44266 9888 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 2880000 44266 9888 (middle p) p.all (total p)) ≤
    1961131177888 * total p + 116956750330952 * middle p + 539307240039545 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 39059159 8257473 2128855183 1961131177888 116956750330952 539307240039545
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 39059159
    omega
  · change 131071*(2*p.all-1) ≤ 8257473
    omega
  · change 2*131071*total p+1 ≤ 2128855183
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 32)
    (hy : middle p ≤ 149) (ht : total p ≤ 8121) :
    HelperPairGates 2880000 44266 9888 (middle p) p.all (total p) := by
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
    Lower80830.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 5802048000
  m := 32000
  weighted := by decide
  shape := Kernels80830.Source02.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80830.Source02.finrank_gap u0 u1
end Phase02

namespace Phase03
def source : SourceNumbers := ⟨1062000, 22133, 4940, 535607796149921249523⟩
def potential : Potential := ⟨980158001726, 50313306146701, 231136627925442⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 32)
    (hy : middle p ≤ 149) (ht : total p ≤ 8121) :
    stageCost 1062000 22133 4940 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 1062000 22133 4940 (middle p) p.all (total p)) ≤
    980158001726 * total p + 50313306146701 * middle p + 231136627925442 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 39059159 8257473 2128855183 980158001726 50313306146701 231136627925442
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 39059159
    omega
  · change 131071*(2*p.all-1) ≤ 8257473
    omega
  · change 2*131071*total p+1 ≤ 2128855183
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 32)
    (hy : middle p ≤ 149) (ht : total p ≤ 8121) :
    HelperPairGates 1062000 22133 4940 (middle p) p.all (total p) := by
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
    Lower80830.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 2901024000
  m := 16000
  weighted := by decide
  shape := Kernels80830.Source03.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80830.Source03.finrank_gap u0 u1
end Phase03

namespace Phase04
def source : SourceNumbers := ⟨531000, 11066, 2470, 33166390491841354440⟩
def potential : Potential := ⟨490068229893, 25156653073351, 115565537063486⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 32)
    (hy : middle p ≤ 149) (ht : total p ≤ 8121) :
    stageCost 531000 11066 2470 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 531000 11066 2470 (middle p) p.all (total p)) ≤
    490068229893 * total p + 25156653073351 * middle p + 115565537063486 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 39059159 8257473 2128855183 490068229893 25156653073351 115565537063486
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 39059159
    omega
  · change 131071*(2*p.all-1) ≤ 8257473
    omega
  · change 2*131071*total p+1 ≤ 2128855183
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 32)
    (hy : middle p ≤ 149) (ht : total p ≤ 8121) :
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
    Lower80830.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 1450512000
  m := 8000
  weighted := by decide
  shape := Kernels80830.Source04.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80830.Source04.finrank_gap u0 u1
end Phase04

namespace Phase05
def source : SourceNumbers := ⟨88902, 1383, 308, 10543266476118971⟩
def potential : Potential := ⟨61176720648, 3625691597785, 16739732997892⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 32)
    (hy : middle p ≤ 149) (ht : total p ≤ 8121) :
    stageCost 88902 1383 308 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 88902 1383 308 (middle p) p.all (total p)) ≤
    61176720648 * total p + 3625691597785 * middle p + 16739732997892 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 39059159 8257473 2128855183 61176720648 3625691597785 16739732997892
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 39059159
    omega
  · change 131071*(2*p.all-1) ≤ 8257473
    omega
  · change 2*131071*total p+1 ≤ 2128855183
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 32)
    (hy : middle p ≤ 149) (ht : total p ≤ 8121) :
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
    Lower80830.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 181314000
  m := 1000
  weighted := by decide
  shape := Kernels80830.Source05.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80830.Source05.finrank_gap u0 u1
end Phase05

namespace Phase06
def source : SourceNumbers := ⟨3640000, 19366, 4267, 1582484275863798669549⟩
def potential : Potential := ⟨851974900634, 102110724538924, 478459229510881⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 32)
    (hy : middle p ≤ 149) (ht : total p ≤ 8121) :
    stageCost 3640000 19366 4267 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 3640000 19366 4267 (middle p) p.all (total p)) ≤
    851974900634 * total p + 102110724538924 * middle p + 478459229510881 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 39059159 8257473 2128855183 851974900634 102110724538924 478459229510881
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 39059159
    omega
  · change 131071*(2*p.all-1) ≤ 8257473
    omega
  · change 2*131071*total p+1 ≤ 2128855183
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 32)
    (hy : middle p ≤ 149) (ht : total p ≤ 8121) :
    HelperPairGates 3640000 19366 4267 (middle p) p.all (total p) := by
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
    Lower80830.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 2538396000
  m := 14000
  weighted := by decide
  shape := Kernels80830.Source06.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := Kernels80830.Source06.finrank_gap u0 u1
end Phase06

end ProximityPrize.SubmissionLower.Lower80830.SourceSound
