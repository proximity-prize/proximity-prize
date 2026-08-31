import ProximityPrize.SubmissionLower.ContactLegacyAdaptiveBoundary6750Research
import ProximityPrize.SubmissionLower.ContactLegacyHardHArithmetic6750Research

namespace ProximityPrize.SubmissionLower.ContactLegacyAdaptiveArithmetic6750Research

open ProximityPrize.Benchmark
open ContactFactorCaps
open ContactKernelCommonGCD6750Research
open ContactIdentityResidualGlobalFlagResearch
open ContactResidualSupportParametersResearch
open ContactTwoTailParameters6750Research
open ContactTwoTailResidualGeneric6750Research
open ContactRouterCellCosts6750Research
open ContactAnchoredOneFamilySelector6750Research
open ContactAnchoredHardCellSelector6750Research
open ContactOrdinaryHardShell6750Research
open ContactSelectedCount6750Research
open ContactSelectedOldCoreLowQuotients6750Research
open ContactLegacyTwoFactorEasy6750Research
open ContactPureTotalQuotientOrdinary6750Research
open ContactLegacyOldGCountProvider6750Research
open ContactLegacyDirectArithmetic6750Research
open ContactLegacyPureBandReceipt6750Research
open ContactLegacyAdaptiveBasic6750Research
open ContactLegacyAdaptiveBoundary6750Research
open ContactLegacyNonbasicArithmetic6750Research
open ContactLegacyHardHArithmetic6750Research
open ContactRouterUniformCaps6750Research

set_option autoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev GlobalPoly := MvPolynomial (Fin 4) K

theorem factorS_le_YS (P : GlobalPoly) : factorS P ≤ factorYS P := by
  apply (weightedTotalDegree_le_iff residualSWeights P (factorYS P)).mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h ⊢
  simp [factorYS, residualSWeights, residualYSWeights] at h ⊢
  omega

theorem factorYS_le_total (P : GlobalPoly) : factorYS P ≤ factorTotal P := by
  apply (weightedTotalDegree_le_iff residualYSWeights P (factorTotal P)).mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h ⊢
  simp [factorTotal, residualYSWeights, residualTotalWeights] at h ⊢
  omega

theorem factorEquationCost_le_coordinate
    (P : GlobalPoly) (D : Nat) (hD : factorD P ≤ D) :
    factorEquationCost P ≤ coordinateCost D
      (factorTotal P) (factorYS P) (factorS P) := by
  have hm := tightCount_mono_D
    (t := factorPaddedT P) (r := factorPaddedR P) hD
  simpa only [factorEquationCost, coordinateCost, factorPaddedT,
    factorPaddedY, factorPaddedR, paddedT, paddedY, paddedR] using
    Nat.add_le_add_left hm
      (cellRegularCost (factorPaddedT P) (factorPaddedY P)
        (factorPaddedR P))

theorem canonicalH_D_le_nonpure
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (F : CanonicalOldCoreFactorization S)
    (hnonpure : ¬(factorYS F.Q = 0 ∧ factorS F.Q = 0)) :
    factorD (canonicalOldCoreH S) ≤ 8598882 := by
  let H := canonicalOldCoreH S
  have hsy := factorS_le_YS F.Q
  have hqY : 1 ≤ factorYS F.Q := by
    by_contra h
    have hy0 : factorYS F.Q = 0 := by omega
    have hr0 : factorS F.Q = 0 := by omega
    exact hnonpure ⟨hy0, hr0⟩
  have hrel := residualYS_mul_le_contact_add_slope F.Q w (by norm_num [w])
  change w * factorYS F.Q ≤ factorContact F.Q + factorS F.Q at hrel
  have hqContact : 131070 ≤ factorContact F.Q := by
    norm_num [w] at hrel
    omega
  have hc := oldCommonCore_contact_le S
  have hadd := F.contact_add
  change factorContact (oldCommonCore S) = factorContact H + factorContact F.Q at hadd
  change factorContact (oldCommonCore S) ≤ 8729951 at hc
  change max (w + 1) (factorContact H + 1) ≤ 8598882
  apply max_le
  · norm_num [w]
  · omega

theorem ordinaryHard_upstream_le_cap {t y r : Nat}
    (cell : OrdinaryHardCell t y r) :
    upstreamCellCost t y r ≤ upstreamCap := by
  have h0 := ContactUpstreamTAnalytic6750Research.upstreamCellCost_antitone_total
    (y := y) (r := r) cell.2.2.2.2.1
  have h1 := ordinaryHardUpstreamBoundaryReceipt
    ⟨y, Nat.lt_succ_iff.mpr cell.2.1⟩
    ⟨r, Nat.lt_succ_iff.mpr cell.2.2.2.1⟩
    ⟨cell.1, cell.2.1, cell.2.2.1, cell.2.2.2.1,
      Nat.le_refl _, cell.2.2.2.2.1.trans cell.2.2.2.2.2⟩
  exact h0.trans (by simpa using h1)

theorem legacyOldGLedger6750 : LegacyOldGLedger6750 := by
  intro u0 u1 S F gcell
  let H := canonicalOldCoreH S
  let gt := oldCoreTotal S
  let gy := oldCoreYS S
  let gr := oldCoreS S
  let ht := factorTotal H
  let hy := factorYS H
  let hr := factorS H
  let qt := factorTotal F.Q
  let qy := factorYS F.Q
  let qr := factorS F.Q
  have hHdiv : H ∣ oldCommonCore S := ⟨F.Q, F.factor_eq⟩
  have hHcaps := factor_coords_le_of_dvd_oldCore S H hHdiv
  have hhrhy : hr ≤ hy := by simpa only [hr, hy] using factorS_le_YS H
  have hhyht : hy ≤ ht := by simpa only [hy, ht] using factorYS_le_total H
  have hqrqy : qr ≤ qy := by simpa only [qr, qy] using factorS_le_YS F.Q
  have hqyqt : qy ≤ qt := by simpa only [qy, qt] using factorYS_le_total F.Q
  have htadd : gt = ht + qt := by simpa only [gt, ht, qt, H] using F.total_add
  have hyadd : gy = hy + qy := by simpa only [gy, hy, qy, H] using F.ys_add
  have hradd : gr = hr + qr := by simpa only [gr, hr, qr, H] using F.slope_add
  have hgtop : gt ≤ 1699 := by simpa only [gt] using gcell.2.2.2.2.2
  have hgyl : gy ≤ 66 := by simpa only [gy] using gcell.2.1
  have hgrl : gr ≤ 14 := by simpa only [gr] using gcell.2.2.2.1
  have hhtop : ht ≤ 1699 := by omega
  have hhyl : hy ≤ 66 := by omega
  have hhrl : hr ≤ 14 := by omega
  by_cases hHcell : OrdinaryHardCell ht hy hr
  · have hup := ordinaryHard_upstream_le_cap gcell
    have hzero :=
      ContactLegacyHardHArithmetic6750Research.OrdinaryHardCell.canonicalAnchoredCost_le_hardAnchoredCap
        hHcell
    have hzero' :
        ContactCanonicalHighSourceAnchoredCap6750Research.canonicalAnchoredCost
            ht hy hr ≤ hardAnchoredCap := by
      simpa only [ht, hy, hr, H] using hzero
    have hnonzero := canonicalNonzeroCost_le_hardThirdCap S F gcell hHcell
    have hbudget : upstreamCap + hardAnchoredCap + hardThirdCap ≤
        ContactMovingProtocol6750Research.mcaBudget := by
      have hb := Nat.le_of_lt hardTotalCap_lt_mcaBudget
      simpa only [hardTotalCap, ContactMovingSeedless6750Research.mcaBudget,
        ContactMovingProtocol6750Research.mcaBudget] using hb
    simp only [legacyFixedCost6750, canonicalZeroCost6750, H, ht, hy, hr,
      if_pos hHcell]
    have hsum : upstreamCellCost gt gy gr +
        ContactCanonicalHighSourceAnchoredCap6750Research.canonicalAnchoredCost
          ht hy hr + canonicalNonzeroCost6750 S F ≤
          ContactMovingProtocol6750Research.mcaBudget :=
      (Nat.add_le_add (Nat.add_le_add hup hzero') hnonzero).trans hbudget
    simpa only [gt, gy, gr, Nat.add_assoc] using hsum
  · have hzeroDef : canonicalZeroCost6750 S = factorEquationCost H := by
      simp only [canonicalZeroCost6750, H, ht, hy, hr, if_neg hHcell]
    by_cases hpure : qy = 0 ∧ qr = 0
    · have hsameY : hy = gy := by omega
      have hsameR : hr = gr := by omega
      have hqpos : qt ≠ 0 := by
        intro hq0
        apply hHcell
        have hsameT : ht = gt := by omega
        simpa only [hsameT, hsameY, hsameR] using gcell
      have hboundary : OrdinaryHardCell (hardMinT hy hr) hy hr := by
        simpa only [hsameY, hsameR] using
          (show OrdinaryHardCell (hardMinT gy gr) gy gr from
            ⟨gcell.1, gcell.2.1, gcell.2.2.1, gcell.2.2.2.1,
              Nat.le_refl _, gcell.2.2.2.2.1.trans gcell.2.2.2.2.2⟩)
      have hup := ContactUpstreamTAnalytic6750Research.upstreamCellCost_antitone_total
        (y := gy) (r := gr) gcell.2.2.2.2.1
      have hup' : upstreamCellCost gt gy gr ≤
          upstreamCellCost (hardMinT hy hr) hy hr := by
        simpa only [hsameY, hsameR] using hup
      have hDH : factorD H ≤ 8729952 := by
        have hc := hHcaps.1
        simp only [factorD]
        apply max_le
        · norm_num [w]
        · omega
      have hEq := factorEquationCost_le_coordinate H 8729952 hDH
      have hDq : factorD F.Q ≤ pureQD hy hr := by
        simpa only [pureQD, hardQuotientD, w] using hardQuotientD_bound S F
      have hDmono := tightCount_mono_D
        (t := factorTotal F.Q) (r := 1) hDq
      have hq1 : 1 ≤ qt := Nat.one_le_iff_ne_zero.mpr hqpos
      have hQcost : factorRFreeCost F.Q ≤ rfreeCost (pureQD hy hr) qt := by
        unfold factorRFreeCost rfreeCost
        simpa only [qt, max_eq_right hq1] using hDmono
      have hQt : qt ≤ 1699 - ht := by omega
      have hQtmono : rfreeCost (pureQD hy hr) qt ≤
          rfreeCost (pureQD hy hr) (1699 - ht) := by
        unfold rfreeCost
        exact ContactCanonicalHighSourceAnchoredCap6750Research.tightCount_mono_total
          (max_le_max_left 1 hQt)
      have hQcost' : factorRFreeCost F.Q ≤
          rfreeCost (pureQD hy hr) (1699 - ht) := by
        exact hQcost.trans hQtmono
      have hpureCap := pureBoundaryCost_le_budget hboundary hhyht hHcell hhtop
      rw [legacyFixedCost6750, hzeroDef, canonicalNonzeroCost6750,
        if_pos (by simpa only [qy, qr] using hpure),
        if_neg (by simpa only [qt] using hqpos)]
      unfold pureBoundaryCost at hpureCap
      have hsum : upstreamCellCost gt gy gr + factorEquationCost H +
          factorRFreeCost F.Q ≤ ContactMovingSeedless6750Research.mcaBudget :=
        (Nat.add_le_add (Nat.add_le_add hup' hEq) hQcost').trans hpureCap
      simpa only [gt, gy, gr, H, Nat.add_assoc,
        ContactMovingSeedless6750Research.mcaBudget,
        ContactMovingProtocol6750Research.mcaBudget] using hsum
    · have hqY : 1 ≤ qy := by
        by_contra h
        apply hpure
        constructor <;> omega
      have hDH := canonicalH_D_le_nonpure S F
        (by simpa only [qy, qr] using hpure)
      have hEq0 := factorEquationCost_le_coordinate H 8598882 hDH
      have hEq : factorEquationCost H ≤ bCost ht hy hr := by
        simpa only [bCost, ht, hy, hr] using hEq0
      have hthird : canonicalThirdCost6750 S = thirdCost ht hy hr := by
        simp only [canonicalThirdCost6750, H, ht, hy, hr, factorTotal,
          factorYS, factorS, thirdCost]
      rw [legacyFixedCost6750, hzeroDef, canonicalNonzeroCost6750,
        if_neg (by simpa only [qy, qr] using hpure), hthird]
      by_cases hdeg : hr < 2 ∨ hy ≤ hr
      · have hlocal := nonBasicLocalCost_le_budget gcell hhrhy hhyht
          hhtop hhyl hhrl hdeg
        have hlocal' : upstreamCellCost gt gy gr +
            nonBasicEquationCost ht hy hr + nonBasicThirdCost ht hy hr ≤
              ContactMovingProtocol6750Research.mcaBudget := by
          simpa only [gt, gy, gr] using hlocal
        have hEq' : factorEquationCost H ≤ nonBasicEquationCost ht hy hr := by
          simpa only [nonBasicEquationCost, nonBasicPaddedT,
            nonBasicPaddedY, nonBasicPaddedR, nonBasicD, coordinateCost,
            paddedT, paddedY, paddedR, ht, hy, hr] using hEq0
        have hthird' : thirdCost ht hy hr = nonBasicThirdCost ht hy hr := rfl
        have hsum : upstreamCellCost gt gy gr + factorEquationCost H +
            thirdCost ht hy hr ≤ ContactMovingProtocol6750Research.mcaBudget := by
          rw [hthird']
          omega
        simpa only [gt, gy, gr, Nat.add_assoc] using hsum
      · have hr2 : 2 ≤ hr := by omega
        have hry : hr < hy := by omega
        by_cases hdiag : ht = hy
        · have htransport := upstreamCellCost_le_upstreamRMax
            (gt := gt) (gy := gy) (gr := gr)
            (ht := ht + 1) (hy := hy) (hr := hr)
            (by omega) (by omega) (by omega) hgrl
          have hcap := boundaryNonPureCost_le_budget hy hr (by omega) hhrl hr2 hry
          have hcap' : upstreamRMax (hy + 1) hy hr +
              coordinateCost 8598882 hy hy hr + thirdCost hy hy hr ≤
                ContactMovingProtocol6750Research.mcaBudget := by
            simpa only [boundaryNonPureCost,
              ContactMovingSeedless6750Research.mcaBudget,
              ContactMovingProtocol6750Research.mcaBudget] using hcap
          have hEqDiag : factorEquationCost H ≤
              coordinateCost 8598882 hy hy hr := by
            simpa only [hdiag, ht, hy, hr] using hEq0
          rw [hdiag] at htransport
          have hsum : upstreamCellCost gt gy gr + factorEquationCost H +
              thirdCost hy hy hr ≤ ContactMovingProtocol6750Research.mcaBudget :=
            (Nat.add_le_add (Nat.add_le_add htransport hEqDiag)
              (Nat.le_refl _)).trans hcap'
          simpa only [gt, gy, gr, H, hdiag, Nat.add_assoc] using hsum
        · have hy1ht : hy + 1 ≤ ht := by omega
          have htop : ht ≤ easyTop hy hr := by
            unfold easyTop
            split_ifs with hhost
            · have hlt : ht < hardMinT hy hr := by
                by_contra hn
                apply hHcell
                exact ⟨hhost.1, hhost.2.1, hhost.2.2.1, hhost.2.2.2,
                  by omega, hhtop⟩
              omega
            · exact hhtop
          have htransport := upstreamCellCost_le_upstreamRMax
            (gt := gt) (gy := gy) (gr := gr)
            (ht := ht) (hy := hy) (hr := hr)
            (by omega) (by omega) (by omega) hgrl
          have hcap := basicNonPureCost_le_budget hr2 hry hy1ht htop
            (by omega) hhrl
          have hcap' : upstreamRMax ht hy hr +
              coordinateCost 8598882 ht hy hr + thirdCost ht hy hr ≤
                ContactMovingProtocol6750Research.mcaBudget := by
            unfold aCost bCost at hcap
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
              ContactMovingSeedless6750Research.mcaBudget,
              ContactMovingProtocol6750Research.mcaBudget] using hcap
          have hsum : upstreamCellCost gt gy gr + factorEquationCost H +
              thirdCost ht hy hr ≤ ContactMovingProtocol6750Research.mcaBudget :=
            (Nat.add_le_add (Nat.add_le_add htransport hEq0)
              (Nat.le_refl _)).trans hcap'
          simpa only [gt, gy, gr, H, Nat.add_assoc] using hsum

end ProximityPrize.SubmissionLower.ContactLegacyAdaptiveArithmetic6750Research

#print axioms ProximityPrize.SubmissionLower.ContactLegacyAdaptiveArithmetic6750Research.legacyOldGLedger6750
