import ProximityPrize.SubmissionLower.LocatorBatchPhase6802

namespace ProximityPrize.SubmissionLower.LocatorPhase6802SourceSound

open RCN095 RCN223 RCN260 RCN294 LocatorFactorAggregate
open LocatorGenericHelperFactorSwitch6802 LocatorGenericPowerRoute6802
open LocatorPhase6802Oracle

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem helperPair_regularCountCap_mono_right
    (L₁ Y₁ S₁ L₂ Y₂ S₂ leftY leftR leftZ : ℕ)
    (hL : L₁ ≤ L₂) (hY : Y₁ ≤ Y₂) (hS : S₁ ≤ S₂) :
    (helperPair L₁ Y₁ S₁ leftY leftR leftZ).regularCountCap ≤
      (helperPair L₂ Y₂ S₂ leftY leftR leftZ).regularCountCap := by
  let P₁ := helperPair L₁ Y₁ S₁ leftY leftR leftZ
  let P₂ := helperPair L₂ Y₂ S₂ leftY leftR leftZ
  have ha : vectorLE P₁.agreement P₂.agreement := by
    refine ⟨?_, ?_, ?_⟩
    · exact max_le_max le_rfl (Nat.add_le_add_left
        (Nat.mul_le_mul_left (2 * 131071) hY) 1)
    · exact max_le_max le_rfl (Nat.mul_le_mul_left 131071
        (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hS) 1))
    · exact max_le_max le_rfl (Nat.add_le_add_right
        (Nat.mul_le_mul_left (2 * 131071) hL) 1)
  have hm : vectorLE P₁.mixedCost P₂.mixedCost := by
    refine ⟨?_, ?_, ?_⟩
    · exact Nat.add_le_add (Nat.mul_le_mul_left leftR hL)
        (Nat.mul_le_mul_left leftZ hS)
    · exact Nat.add_le_add (Nat.mul_le_mul_left leftY hL)
        (Nat.mul_le_mul_left leftZ hY)
    · exact Nat.add_le_add (Nat.mul_le_mul_left leftY hS)
        (Nat.mul_le_mul_left leftR hY)
  have hdot : dot P₁.agreement P₁.mixedCost ≤
      dot P₂.agreement P₂.mixedCost := by
    unfold dot
    exact Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul ha.1 hm.1)
        (Nat.mul_le_mul ha.2.1 hm.2.1))
      (Nat.mul_le_mul ha.2.2 hm.2.2)
  have hnum : P₁.regularNumerator ≤ P₂.regularNumerator := by
    unfold UnequalParameters.regularNumerator
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

private theorem r1200_stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 32)
    (hy : middle p ≤ 149) (ht : total p ≤ 6403) :
    stageCost 300000 6642 1477 (exactRouteBox p) 0 ≤
      r1200Potential.eval p := by
  have hay : 1 + 262142 * middle p ≤ 1741147165 := by omega
  have har : 131071 * (2 * p.all - 1) ≤ 387052663 := by omega
  have haz : 262142 * total p + 1 ≤ 78642600001 := by omega
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero,
    helperPair, UnequalParameters.regularCountCap,
    UnequalParameters.regularNumerator, UnequalParameters.errors,
    UnequalParameters.gap, UnequalParameters.agreement,
    UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
    UnequalParameters.mixedCost, dot, Potential.eval, r1200Potential]
  rw [max_eq_right hay, max_eq_right har, max_eq_right haz]
  norm_num
  omega

private theorem sourceC_stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 32)
    (hy : middle p ≤ 149) (ht : total p ≤ 6403) :
    stageCost 200000 3321 738 (exactRouteBox p) 0 ≤
      sourceCPotential.eval p := by
  have hay : 1 + 262142 * middle p ≤ 870573583 := by omega
  have har : 131071 * (2 * p.all - 1) ≤ 193329725 := by omega
  have haz : 262142 * total p + 1 ≤ 52428400001 := by omega
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero,
    helperPair, UnequalParameters.regularCountCap,
    UnequalParameters.regularNumerator, UnequalParameters.errors,
    UnequalParameters.gap, UnequalParameters.agreement,
    UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
    UnequalParameters.mixedCost, dot, Potential.eval, sourceCPotential]
  rw [max_eq_right hay, max_eq_right har, max_eq_right haz]
  norm_num
  omega

private theorem split500_stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 32)
    (hy : middle p ≤ 149) (ht : total p ≤ 6403) :
    stageCost 82100 1660 370 (exactRouteBox p) 0 ≤
      split500Potential.eval p := by
  have hay : 1 + 262142 * middle p ≤ 435155721 := by omega
  have har : 131071 * (2 * p.all - 1) ≤ 96861469 := by omega
  have haz : 262142 * total p + 1 ≤ 21521858201 := by omega
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero,
    helperPair, UnequalParameters.regularCountCap,
    UnequalParameters.regularNumerator, UnequalParameters.errors,
    UnequalParameters.gap, UnequalParameters.agreement,
    UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
    UnequalParameters.mixedCost, dot, Potential.eval, split500Potential]
  rw [max_eq_right hay, max_eq_right har, max_eq_right haz]
  norm_num
  omega

private theorem split390_stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 32)
    (hy : middle p ≤ 149) (ht : total p ≤ 6403) :
    stageCost 19500 539 120 (exactRouteBox p) 0 ≤
      split390Potential.eval p := by
  have hay : 1 + 262142 * middle p ≤ 141294539 := by omega
  have har : 131071 * (2 * p.all - 1) ≤ 31325969 := by omega
  have haz : 262142 * total p + 1 ≤ 5111769001 := by omega
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero,
    helperPair, UnequalParameters.regularCountCap,
    UnequalParameters.regularNumerator, UnequalParameters.errors,
    UnequalParameters.gap, UnequalParameters.agreement,
    UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
    UnequalParameters.mixedCost, dot, Potential.eval, split390Potential]
  rw [max_eq_right hay, max_eq_right har, max_eq_right haz]
  norm_num
  omega

private theorem r1200_stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 32)
    (hy : middle p ≤ 149) (ht : total p ≤ 6403) :
    HelperPairGates 300000 6642 1477 (middle p) p.all (total p) := by
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

private theorem sourceC_stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 32)
    (hy : middle p ≤ 149) (ht : total p ≤ 6403) :
    HelperPairGates 200000 3321 738 (middle p) p.all (total p) := by
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

private theorem split500_stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 32)
    (hy : middle p ≤ 149) (ht : total p ≤ 6403) :
    HelperPairGates 82100 1660 370 (middle p) p.all (total p) := by
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

private theorem split390_stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 32)
    (hy : middle p ≤ 149) (ht : total p ≤ 6403) :
    HelperPairGates 19500 539 120 (middle p) p.all (total p) := by
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

def r1200Sound : PhaseSourceSound where
  source := sourceR1200
  potential := r1200Potential
  stageCost_le p j hr hs hy ht _ :=
    (stageCost_le_stageZero 300000 6642 1477 p j).trans
      (r1200_stageZero_le p hr (by omega) (by omega) ht)
  stageGates p j hr hs hy ht _ :=
    stageGates_of_stageZero 300000 6642 1477 p j
      (r1200_stageZero_gates p hr (by omega) (by omega) ht)

def sourceCSound : PhaseSourceSound where
  source := sourceC
  potential := sourceCPotential
  stageCost_le p j hr hs hy ht _ :=
    (stageCost_le_stageZero 200000 3321 738 p j).trans
      (sourceC_stageZero_le p hr (by omega) (by omega) ht)
  stageGates p j hr hs hy ht _ :=
    stageGates_of_stageZero 200000 3321 738 p j
      (sourceC_stageZero_gates p hr (by omega) (by omega) ht)

def split500Sound : PhaseSourceSound where
  source := sourceSplit500
  potential := split500Potential
  stageCost_le p j hr hs hy ht _ :=
    (stageCost_le_stageZero 82100 1660 370 p j).trans
      (split500_stageZero_le p hr (by omega) (by omega) ht)
  stageGates p j hr hs hy ht _ :=
    stageGates_of_stageZero 82100 1660 370 p j
      (split500_stageZero_gates p hr (by omega) (by omega) ht)

def split390Sound : PhaseSourceSound where
  source := sourceSplit390
  potential := split390Potential
  stageCost_le p j hr hs hy ht _ :=
    (stageCost_le_stageZero 19500 539 120 p j).trans
      (split390_stageZero_le p hr (by omega) (by omega) ht)
  stageGates p j hr hs hy ht _ :=
    stageGates_of_stageZero 19500 539 120 p j
      (split390_stageZero_gates p hr (by omega) (by omega) ht)

end ProximityPrize.SubmissionLower.LocatorPhase6802SourceSound
