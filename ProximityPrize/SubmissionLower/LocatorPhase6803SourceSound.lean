import ProximityPrize.SubmissionLower.LocatorPhase6803Oracle

/-! Analytic helper-cost and gate bounds for the four 68.03 sources. -/

namespace ProximityPrize.SubmissionLower.LocatorPhase6803SourceSound

open RCN095 RCN260 RCN294 LocatorFactorAggregate
open LocatorPhase6800Oracle (Potential)
open LocatorPhase6803Oracle

set_option autoImplicit false
set_option maxRecDepth 1000000
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
    (hr : 1 ≤ p.all) (hs : p.all ≤ 29)
    (hy : middle p ≤ 135) (ht : total p ≤ 6676) :
    stageCost 328400 6641 1480 (exactRouteBox p) 0 ≤
      r1200Potential.eval p := by
  have hay : 1 + 262142 * middle p ≤ 1740885023 := by omega
  have har : 131071 * (2 * p.all - 1) ≤ 387839089 := by omega
  have haz : 262142 * total p + 1 ≤ 86087432801 := by omega
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
    (hr : 1 ≤ p.all) (hs : p.all ≤ 29)
    (hy : middle p ≤ 135) (ht : total p ≤ 6676) :
    stageCost 82100 1660 370 (exactRouteBox p) 0 ≤
      sourceCPotential.eval p := by
  have hay : 1 + 262142 * middle p ≤ 435155721 := by omega
  have har : 131071 * (2 * p.all - 1) ≤ 96861469 := by omega
  have haz : 262142 * total p + 1 ≤ 21521858201 := by omega
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
    (hr : 1 ≤ p.all) (hs : p.all ≤ 29)
    (hy : middle p ≤ 135) (ht : total p ≤ 6676) :
    stageCost 42000 1383 310 (exactRouteBox p) 0 ≤
      split500Potential.eval p := by
  have hay : 1 + 262142 * middle p ≤ 362542387 := by omega
  have har : 131071 * (2 * p.all - 1) ≤ 81132949 := by omega
  have haz : 262142 * total p + 1 ≤ 11009964001 := by omega
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero,
    helperPair, UnequalParameters.regularCountCap,
    UnequalParameters.regularNumerator, UnequalParameters.errors,
    UnequalParameters.gap, UnequalParameters.agreement,
    UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
    UnequalParameters.mixedCost, dot, Potential.eval, split500Potential]
  rw [max_eq_right hay, max_eq_right har, max_eq_right haz]
  norm_num
  omega

private theorem phase4_stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 29)
    (hy : middle p ≤ 135) (ht : total p ≤ 6676) :
    stageCost 24000 484 106 (exactRouteBox p) 0 ≤
      phase4Potential.eval p := by
  have hay : 1 + 262142 * middle p ≤ 126876729 := by omega
  have har : 131071 * (2 * p.all - 1) ≤ 27655981 := by omega
  have haz : 262142 * total p + 1 ≤ 6291408001 := by omega
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero,
    helperPair, UnequalParameters.regularCountCap,
    UnequalParameters.regularNumerator, UnequalParameters.errors,
    UnequalParameters.gap, UnequalParameters.agreement,
    UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
    UnequalParameters.mixedCost, dot, Potential.eval, phase4Potential]
  rw [max_eq_right hay, max_eq_right har, max_eq_right haz]
  norm_num
  omega

/-- The initial-A helper majorant on the full viable complementary box.  The
historical 68.03 potential was derived assuming the right `(Y,S)=(135,29)`
agreement coordinates dominate; this coefficientwise envelope also covers
left coordinates up to `(153,34)`. -/
theorem initialAHelperCap_le_widePotential (p : FlagDegree)
    (hs : p.all ≤ 34) (hy : middle p ≤ 153) (ht : total p ≤ 6676) :
    (helperPair 130000 135 29 (middle p) p.all (total p)).regularCountCap ≤
      initialAWidePotential.eval p := by
  have hayL : 1 + 262142 * middle p ≤ 40107727 := by omega
  have hayR : 1 + 262142 * 135 ≤ 40107727 := by decide
  have hay : max (1 + 262142 * middle p) (1 + 262142 * 135) ≤
      40107727 := max_le hayL hayR
  have harL : 131071 * (2 * p.all - 1) ≤ 8781757 := by omega
  have harR : 131071 * (2 * 29 - 1) ≤ 8781757 := by decide
  have har : max (131071 * (2 * p.all - 1))
      (131071 * (2 * 29 - 1)) ≤ 8781757 := max_le harL harR
  have hazL : 262142 * total p + 1 ≤ 34078460001 := by omega
  have hazR : 262142 * 130000 + 1 ≤ 34078460001 := by decide
  have haz : max (262142 * total p + 1) (262142 * 130000 + 1) ≤
      34078460001 := max_le hazL hazR
  simp only [helperPair, UnequalParameters.regularCountCap,
    UnequalParameters.regularNumerator, UnequalParameters.errors,
    UnequalParameters.gap, UnequalParameters.agreement,
    UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
    UnequalParameters.mixedCost, dot, Potential.eval, initialAWidePotential]
  apply (Nat.div_le_iff_le_mul (by decide)).2
  calc
    131073 *
          (max (1 + 262142 * middle p) (1 + 262142 * 135) *
                (p.all * 130000 + total p * 29) +
            max (131071 * (2 * p.all - 1)) (131071 * (2 * 29 - 1)) *
                (middle p * 130000 + total p * 135) +
            max (262142 * total p + 1) (262142 * 130000 + 1) *
                (middle p * 29 + p.all * 135)) +
        80782 * 50292 * (middle p * 29 + p.all * 135) ≤
      131073 *
          (40107727 * (p.all * 130000 + total p * 29) +
            8781757 * (middle p * 130000 + total p * 135) +
            34078460001 * (middle p * 29 + p.all * 135)) +
        80782 * 50292 * (middle p * 29 + p.all * 135) := by
          have h₁ := Nat.mul_le_mul_right
            (p.all * 130000 + total p * 29) hay
          have h₂ := Nat.mul_le_mul_right
            (middle p * 130000 + total p * 135) har
          have h₃ := Nat.mul_le_mul_right
            (middle p * 29 + p.all * 135) haz
          exact Nat.add_le_add
            (Nat.mul_le_mul_left 131073
              (Nat.add_le_add (Nat.add_le_add h₁ h₂) h₃)) le_rfl
    _ ≤ (6121183939 * total p + 5551041767050 * middle p +
          25579200875807 * p.all) * 50292 := by
      norm_num
      omega
    _ ≤ (6121183939 * total p + 5551041767050 * middle p +
          25579200875807 * p.all) * 50292 + 50292 - 1 := by omega

private theorem stageZero_gates (L YS S : ℕ) (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 29)
    (hy : middle p ≤ 135) (ht : total p ≤ 6676)
    (hL : 6676 ≤ L) (hY : 135 ≤ YS) (hS : 29 ≤ S)
    (hmY : 135 * L + 6676 * YS < 2130706433)
    (hmR : 135 * S + 29 * YS < 2130706433)
    (hmZ : 29 * L + 6676 * S < 2130706433) :
    HelperPairGates L YS S (middle p) p.all (total p) := by
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

private theorem r1200_stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 29)
    (hy : middle p ≤ 135) (ht : total p ≤ 6676) :
    HelperPairGates 328400 6641 1480 (middle p) p.all (total p) := by
  exact stageZero_gates 328400 6641 1480 p hr hs hy ht
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem sourceC_stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 29)
    (hy : middle p ≤ 135) (ht : total p ≤ 6676) :
    HelperPairGates 82100 1660 370 (middle p) p.all (total p) := by
  exact stageZero_gates 82100 1660 370 p hr hs hy ht
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem split500_stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 29)
    (hy : middle p ≤ 135) (ht : total p ≤ 6676) :
    HelperPairGates 42000 1383 310 (middle p) p.all (total p) := by
  exact stageZero_gates 42000 1383 310 p hr hs hy ht
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem phase4_stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 29)
    (hy : middle p ≤ 135) (ht : total p ≤ 6676) :
    HelperPairGates 24000 484 106 (middle p) p.all (total p) := by
  exact stageZero_gates 24000 484 106 p hr hs hy ht
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

def r1200Sound : PhaseSourceSound where
  source := sourceR1200
  potential := r1200Potential
  stageCost_le p j hr hs hy ht _ :=
    (stageCost_le_stageZero 328400 6641 1480 p j).trans
      (r1200_stageZero_le p hr hs hy ht)
  stageGates p j hr hs hy ht _ :=
    stageGates_of_stageZero 328400 6641 1480 p j
      (r1200_stageZero_gates p hr hs hy ht)

def sourceCSound : PhaseSourceSound where
  source := sourceC
  potential := sourceCPotential
  stageCost_le p j hr hs hy ht _ :=
    (stageCost_le_stageZero 82100 1660 370 p j).trans
      (sourceC_stageZero_le p hr hs hy ht)
  stageGates p j hr hs hy ht _ :=
    stageGates_of_stageZero 82100 1660 370 p j
      (sourceC_stageZero_gates p hr hs hy ht)

def split500Sound : PhaseSourceSound where
  source := sourceSplit500
  potential := split500Potential
  stageCost_le p j hr hs hy ht _ :=
    (stageCost_le_stageZero 42000 1383 310 p j).trans
      (split500_stageZero_le p hr hs hy ht)
  stageGates p j hr hs hy ht _ :=
    stageGates_of_stageZero 42000 1383 310 p j
      (split500_stageZero_gates p hr hs hy ht)

def phase4Sound : PhaseSourceSound where
  source := sourcePhase4
  potential := phase4Potential
  stageCost_le p j hr hs hy ht _ :=
    (stageCost_le_stageZero 24000 484 106 p j).trans
      (phase4_stageZero_le p hr hs hy ht)
  stageGates p j hr hs hy ht _ :=
    stageGates_of_stageZero 24000 484 106 p j
      (phase4_stageZero_gates p hr hs hy ht)

end ProximityPrize.SubmissionLower.LocatorPhase6803SourceSound
