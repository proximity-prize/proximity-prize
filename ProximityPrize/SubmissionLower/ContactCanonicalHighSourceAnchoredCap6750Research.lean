import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAnchoredHardCellSelector6750Research
import ProximityPrize.SubmissionLower.ContactRouterCellCosts6750Research
import ProximityPrize.SubmissionLower.ContactRouterUniformCaps6750Research
import ProximityPrize.SubmissionLower.ContactIdentityCurveProvider6731Research
import ProximityPrize.SubmissionLower.ContactAnchoredOrdinaryFixedCell6750Research

 







namespace ProximityPrize.SubmissionLower
namespace ContactCanonicalHighSourceAnchoredCap6750Research

open ContactAnchoredOneFamilySelector6750Research
open ContactAnchoredHardCellSelector6750Research
open ContactRouterCellCosts6750Research
open ContactTightSingularLedgerResearch
open ContactTwoTailParameters6750Research
open ContactFlagBezout6543Research
open ContactIdentityCurveProvider6731Research
open ContactAnchoredOrdinaryFixedCell6750Research

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 1000000
set_option maxSynthPendingDepth 1000000

def quotientTotal (t y r : Nat) : Nat := selectedTotal t y r - t
def quotientYS (y : Nat) : Nat := familyYSCap - y
def quotientS (r : Nat) : Nat := familySlopeCap - r

 
def quotientContact (y r : Nat) : Nat := quotientWeightedCut y r

 
def canonicalAnchoredCost (t y r : Nat) : Nat :=
  (cellTightProfile
      ContactTwoTailParameters6750Research.profileA.weightedCap t r).countCap +
    (cellTightProfile (quotientContact y r)
      (quotientTotal t y r) (quotientS r)).countCap +
    (cellRegularCost t y r +
      cellRegularCost (quotientTotal t y r) (quotientYS y) (quotientS r)) / 2

def anchoredChunkStart (k y r : Nat) : Nat := hardMinT y r + 16 * k
def anchoredChunkEnd (k y r : Nat) : Nat :=
  min (hardMaxT y r) (anchoredChunkStart k y r + 15)

 
def canonicalAnchoredChunkCost (k y r : Nat) : Nat :=
  let lo := anchoredChunkStart k y r
  let hi := anchoredChunkEnd k y r
  (cellTightProfile profileA.weightedCap hi r).countCap +
    (cellTightProfile (quotientContact y r)
      (quotientTotal lo y r) (quotientS r)).countCap +
    (cellRegularCost hi y r +
      cellRegularCost (quotientTotal lo y r) (quotientYS y) (quotientS r)) / 2

 


def canonicalAnchoredChunkGridCheck : Bool :=
  (List.range 28).all fun yy ↦
    (List.range 7).all fun rr ↦
      (List.range 50).all fun k ↦
        decide ((hostileMinR (yy + 38) ≤ rr + 8 ∧
            anchoredChunkStart k (yy + 38) (rr + 8) ≤
              hardMaxT (yy + 38) (rr + 8)) →
          canonicalAnchoredChunkCost k (yy + 38) (rr + 8) ≤
            ContactRouterUniformCaps6750Research.hardAnchoredCap)

 
def identityBasisCheck (t y r : Nat) : Prop :=
  (n - w) * (errors + 1) *
      identityCurveDegree unitZFlag (cellA t y) (cellB y r) (cellS r) w ≤
    gap * flagMixed unitZFlag (cellFirstTail t y r) (cellSecondTail t y r) ∧
  (n - w) * (errors + 1) *
      identityCurveDegree unitYZFlag (cellA t y) (cellB y r) (cellS r) w ≤
    gap * flagMixed unitYZFlag (cellFirstTail t y r) (cellSecondTail t y r) ∧
  (n - w) * (errors + 1) *
      identityCurveDegree unitAllFlag (cellA t y) (cellB y r) (cellS r) w ≤
    gap * flagMixed unitAllFlag (cellFirstTail t y r) (cellSecondTail t y r)

theorem HardCell.r_ge_8 {t y r : Nat} (cell : HardCell t y r) : 8 ≤ r := by
  apply (show 8 ≤ hostileMinR y from ?_).trans cell.r_lower
  unfold hostileMinR
  split_ifs <;> omega

 

theorem HardCell.hardMinT_ge_897 {t y r : Nat} (cell : HardCell t y r) :
    897 ≤ hardMinT y r := by
  have hcheck : ∀ (yy : Fin 66), 38 ≤ yy.val →
      ∀ rr : Fin 15, hostileMinR yy.val ≤ rr.val →
        897 ≤ hardMinT yy.val rr.val := by
    decide
  exact hcheck ⟨y, Nat.lt_succ_iff.mpr cell.y_upper⟩ cell.y_lower
    ⟨r, Nat.lt_succ_iff.mpr cell.r_upper⟩ cell.r_lower

theorem HardCell.t_ge_897 {t y r : Nat} (cell : HardCell t y r) : 897 ≤ t :=
  (HardCell.hardMinT_ge_897 cell).trans cell.t_lower

theorem HardCell.left_basic {t y r : Nat} (cell : HardCell t y r) :
    2 ≤ r ∧ r < y ∧ y ≤ t := by
  have hr8 := HardCell.r_ge_8 cell
  have hr14 := cell.r_upper
  have ht897 := HardCell.t_ge_897 cell
  have hy38 := cell.y_lower
  have hy65 := cell.y_upper
  omega

theorem HardCell.quotient_basic {t y r : Nat} (cell : HardCell t y r) :
    2 ≤ quotientS r ∧ quotientS r < quotientYS y ∧
      quotientYS y ≤ quotientTotal t y r := by
  have hr8 := HardCell.r_ge_8 cell
  have hr14 := cell.r_upper
  have hy38 := cell.y_lower
  have hy65 := cell.y_upper
  have hbase : familyBaseTotal ≤ selectedTotal t y r := by
    unfold selectedTotal
    exact Nat.le_add_right _ _
  have hface := cell.selector_inputs.2.1
  have hsub : familyBaseTotal - t ≤ selectedTotal t y r - t :=
    Nat.sub_le_sub_right hbase t
  refine ⟨?_, ?_, ?_⟩
  · unfold quotientS
    norm_num [familySlopeCap]
    omega
  · unfold quotientS quotientYS
    norm_num [familySlopeCap, familyYSCap]
    omega
  · unfold quotientYS quotientTotal
    exact hface.trans hsub

 
theorem HardCell.leftIdentityBasisCheck
    {t y r : Nat} (cell : HardCell t y r) : identityBasisCheck t y r := by
  have hb := HardCell.left_basic cell
  have h := identityBasisBudget_of_basic_cell_analytic t y r
    hb.1 hb.2.1 hb.2.2
  exact ⟨h.zOnly, h.yz, h.all⟩

 
theorem HardCell.rightIdentityBasisCheck
    {t y r : Nat} (cell : HardCell t y r) :
    identityBasisCheck (quotientTotal t y r) (quotientYS y) (quotientS r) := by
  have hb := HardCell.quotient_basic cell
  have h := identityBasisBudget_of_basic_cell_analytic
    (quotientTotal t y r) (quotientYS y) (quotientS r)
    hb.1 hb.2.1 hb.2.2
  exact ⟨h.zOnly, h.yz, h.all⟩

 

structure SingularProfileValidity (P : TightParameters) : Prop where
  one_le_s : 1 ≤ P.s
  s_small : P.s < prime
  one_le_w : 1 ≤ P.w
  w_small : P.w < prime
  contact_room : P.w < P.kappa * P.D
  algebraic_pos : 1 ≤ P.algebraicCap
  implicit_small : P.implicitYCap < prime
  algebraic_small : P.algebraicCap < prime
  mixed_small : 2 * P.implicitYCap * P.algebraicCap < prime
  w_lt_a : P.w < P.a
  a_le_n : P.a ≤ P.n

def singularProfileValidityCheck (P : TightParameters) : Prop :=
  1 ≤ P.s ∧ P.s < prime ∧ 1 ≤ P.w ∧ P.w < prime ∧
    P.w < P.kappa * P.D ∧ 1 ≤ P.algebraicCap ∧
    P.implicitYCap < prime ∧ P.algebraicCap < prime ∧
    2 * P.implicitYCap * P.algebraicCap < prime ∧
    P.w < P.a ∧ P.a ≤ P.n

theorem singularProfileValidity_of_check (P : TightParameters)
    (h : singularProfileValidityCheck P) : SingularProfileValidity P :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2⟩

theorem singularProfileValidity_of_gates (D t r : Nat)
    (gates : OrdinaryCellCombinerGatesD6750 D t r) :
    SingularProfileValidity (cellTightProfile D t r) :=
  ⟨gates.slope_pos, gates.slope_lt_char, gates.w_pos, gates.w_lt_char,
    gates.weighted_nontrivial, gates.algebraic_pos,
    gates.implicitY_lt_char, gates.algebraic_lt_char,
    gates.mixed_lt_char, gates.w_lt_agreements, gates.agreements_le_n⟩

 
theorem HardCell.leftSingularValidity
    {t y r : Nat} (cell : HardCell t y r) :
    SingularProfileValidity
      (cellTightProfile profileA.weightedCap t r) := by
  apply singularProfileValidity_of_gates
  apply combinerGatesD_of_bounds_analytic profileA.weightedCap t r
  · norm_num [profileA, Profile.weightedCap, w,
      ContactTwoTailParameters6750Research.agreements, n, errors]
  · exact Nat.le_refl _
  · exact (HardCell.t_ge_897 cell).trans' (by omega)
  · exact cell.t_le_1692.trans (by omega)
  · exact (HardCell.r_ge_8 cell).trans' (by omega)
  · exact cell.r_upper.trans (by norm_num)

 
theorem HardCell.rightSingularValidity
    {t y r : Nat} (cell : HardCell t y r) :
    SingularProfileValidity
      (cellTightProfile (quotientContact y r)
        (quotientTotal t y r) (quotientS r)) := by
  let D := quotientContact y r
  let qt := quotientTotal t y r
  let qr := quotientS r
  have hDlo : 5797635 ≤ D := by
    simpa only [D, quotientContact] using cell.quotient_caps.2.2.2
  have hDhi : D ≤ 9336558 := by
    simp only [D, quotientContact, quotientWeightedCut]
    norm_num [familyMultiplicity,
      ContactAnchoredOneFamilySelector6750Research.agreements,
      contactSlope, cutWidth,
      ContactTwoTailParameters6750Research.agreements, n, errors]
    have hy := cell.y_lower
    have hr := cell.r_upper
    omega
  have hqtLo : 1 ≤ qt := by
    have hb := HardCell.quotient_basic cell
    simp only [qt]
    omega
  have hqtHi : qt ≤ 1218 := by
    simpa only [qt, quotientTotal] using cell.quotient_caps.1
  have hqrLo : 1 ≤ qr := by
    have hb := HardCell.quotient_basic cell
    simpa only [qr] using hb.1.trans' (show 1 ≤ 2 by omega)
  have hqrHi : qr ≤ 16 := by
    simpa only [qr, quotientS] using cell.quotient_caps.2.2.1
  have hkLo : 1 ≤ 2 * qr - 1 := by omega
  have hkHi : 2 * qr - 1 ≤ 31 := by omega
  have hkD : (2 * qr - 1) * D ≤ 31 * 9336558 :=
    Nat.mul_le_mul hkHi hDhi
  have himp : (cellTightProfile D qt qr).implicitYCap ≤ 2208 := by
    simp only [cellTightProfile,
      ContactTightSingularLedgerResearch.TightParameters.implicitYCap,
      ContactTightSingularLedgerResearch.TightParameters.kappa]
    rw [← Nat.lt_succ_iff]
    apply (Nat.div_lt_iff_lt_mul (by norm_num [w])).mpr
    norm_num [w]
    omega
  have halg : (cellTightProfile D qt qr).algebraicCap ≤ 37758 := by
    simp only [cellTightProfile,
      ContactTightSingularLedgerResearch.TightParameters.algebraicCap,
      ContactTightSingularLedgerResearch.TightParameters.kappa]
    exact (Nat.mul_le_mul hkHi hqtHi).trans (by norm_num)
  have gates : OrdinaryCellCombinerGatesD6750 D qt qr := by
    refine ⟨hqrLo, hqrHi.trans_lt (by norm_num [prime]),
      by norm_num [w], by norm_num [w, prime], ?_, hqtLo.trans ?_, ?_,
      himp.trans_lt (by norm_num [prime]), ?_,
      by norm_num [w, ContactTwoTailParameters6750Research.agreements, n, errors],
      by norm_num [ContactTwoTailParameters6750Research.agreements, n, errors]⟩
    · have hDw : w < D := by
        norm_num [w]
        omega
      nlinarith
    · exact Nat.le_mul_of_pos_left _ hkLo
    · exact (Nat.mul_le_mul hkHi hqtHi).trans_lt (by norm_num [prime])
    · exact (Nat.mul_le_mul (Nat.mul_le_mul_left 2 himp) halg).trans_lt
        (by norm_num [prime])
  exact singularProfileValidity_of_gates D qt qr gates

theorem tightCount_mono_total {D r t₁ t₂ : Nat} (ht : t₁ ≤ t₂) :
    (cellTightProfile D t₁ r).countCap ≤
      (cellTightProfile D t₂ r).countCap := by
  unfold cellTightProfile
  simp only [TightParameters.countCap, TightParameters.tightNumerator,
    TightParameters.coreNumerator, TightParameters.aggregateCost,
    TightParameters.agreement, TightParameters.implicitYCap,
    TightParameters.algebraicCap, TightParameters.kappa,
    TightParameters.errors, TightParameters.gap,
    ContactSingularLedger6600Research.dot]
  gcongr

theorem cellRegularCost_mono_total {t₁ t₂ y r : Nat} (ht : t₁ ≤ t₂) :
    cellRegularCost t₁ y r ≤ cellRegularCost t₂ y r := by
  unfold cellRegularCost cellFixedFlag cellFirstTail cellSecondTail
    cellSupport cellA cellB cellS
  simp only [ContactMovingAgreementCertificate6719Research.support,
    ContactAnchoredDelayedTailProviderAdapter6750Research.reducedResidualAgreementFlag6750,
    ContactAnchoredDelayedTailProviderAdapter6750Research.reducedAgreementDirection6750,
    ContactMovingOuterBudget6719Research.paddedCut,
    ContactMovingPositiveLedger6719Research.surfaceFlag,
    ContactMovingPositiveLedger6719Research.centreFlag,
    ContactMovingPositiveLedger6719Research.directionFlag,
    flagMixed, add_zOnly, add_yz, add_all,
    nsmul_zOnly, nsmul_yz, nsmul_all]
  gcongr

theorem quotientTotal_antitone_on_hard
    {t₁ t₂ y r : Nat} (cell₁ : HardCell t₁ y r)
    (cell₂ : HardCell t₂ y r) (ht : t₁ ≤ t₂) :
    quotientTotal t₂ y r ≤ quotientTotal t₁ y r := by
  have hdef := selectorDeficit_antitone_t (r := r) ht
    cell₂.selector_inputs.1 cell₂.selector_inputs.2.1
  have hselected := selectedTotal_mono_of_deficit (y := y) (r := r)
    cell₂.selector_inputs.2.2 hdef
  unfold quotientTotal
  omega

theorem HardCell.exists_anchoredChunk
    {t y r : Nat} (cell : HardCell t y r) :
    ∃ k : Nat, k < 50 ∧
      HardCell (anchoredChunkStart k y r) y r ∧
      HardCell (anchoredChunkEnd k y r) y r ∧
      anchoredChunkStart k y r ≤ t ∧ t ≤ anchoredChunkEnd k y r := by
  let d := t - hardMinT y r
  let k := d / 16
  have hd : hardMinT y r + d = t := by
    simp only [d]
    exact Nat.add_sub_of_le cell.t_lower
  have hdecomp : 16 * k + d % 16 = d := by
    simpa only [k] using Nat.div_add_mod d 16
  have hmod : d % 16 < 16 := Nat.mod_lt _ (by omega)
  have hmin := HardCell.hardMinT_ge_897 cell
  have htmax := cell.t_le_1692
  have hk : k < 50 := by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 16)).2
    dsimp only [k, d]
    omega
  have hlo : anchoredChunkStart k y r ≤ t := by
    unfold anchoredChunkStart
    omega
  have hlotop : anchoredChunkStart k y r ≤ hardMaxT y r :=
    hlo.trans cell.t_upper
  have hstart : anchoredChunkStart k y r + d % 16 = t := by
    unfold anchoredChunkStart
    omega
  have hthi : t ≤ anchoredChunkEnd k y r := by
    unfold anchoredChunkEnd
    exact (Nat.le_min).2 ⟨cell.t_upper, by omega⟩
  have hlohi : anchoredChunkStart k y r ≤ anchoredChunkEnd k y r := by
    unfold anchoredChunkEnd
    exact (Nat.le_min).2 ⟨hlotop, by omega⟩
  have hminStart : hardMinT y r ≤ anchoredChunkStart k y r := by
    unfold anchoredChunkStart
    omega
  refine ⟨k, hk, ?_, ?_, hlo, hthi⟩
  · exact ⟨cell.y_lower, cell.y_upper, cell.r_lower, cell.r_upper,
      hminStart, hlotop⟩
  · exact ⟨cell.y_lower, cell.y_upper, cell.r_lower, cell.r_upper,
      hminStart.trans hlohi,
      (Nat.min_le_left _ _)⟩

theorem canonicalAnchoredCost_le_chunkCost
    {t y r k : Nat} (cell : HardCell t y r)
    (cellLo : HardCell (anchoredChunkStart k y r) y r)
    (cellHi : HardCell (anchoredChunkEnd k y r) y r)
    (hlo : anchoredChunkStart k y r ≤ t)
    (hhi : t ≤ anchoredChunkEnd k y r) :
    canonicalAnchoredCost t y r ≤ canonicalAnchoredChunkCost k y r := by
  have hq := quotientTotal_antitone_on_hard cellLo cell hlo
  have hleftTight := tightCount_mono_total (D := profileA.weightedCap)
    (r := r) hhi
  have hrightTight := tightCount_mono_total (D := quotientContact y r)
    (r := quotientS r) hq
  have hleftRegular := cellRegularCost_mono_total (y := y) (r := r) hhi
  have hrightRegular := cellRegularCost_mono_total
    (y := quotientYS y) (r := quotientS r) hq
  unfold canonicalAnchoredCost canonicalAnchoredChunkCost
  exact Nat.add_le_add (Nat.add_le_add hleftTight hrightTight)
    (Nat.div_le_div_right (Nat.add_le_add hleftRegular hrightRegular))

 


theorem HardCell.canonicalAnchoredCost_le_hardAnchoredCap
    {t y r : Nat} (cell : HardCell t y r) :
    canonicalAnchoredCost t y r ≤
      ContactRouterUniformCaps6750Research.hardAnchoredCap := by
  have hrlo := HardCell.r_ge_8 cell
  have hyhi := cell.y_upper
  have hrhi := cell.r_upper
  have hyEq : y - 38 + 38 = y := Nat.sub_add_cancel cell.y_lower
  have hrEq : r - 8 + 8 = r := Nat.sub_add_cancel hrlo
  rcases HardCell.exists_anchoredChunk cell with
    ⟨k, hk, cellLo, cellHi, hlo, hhi⟩
  have hgrid : canonicalAnchoredChunkGridCheck = true := by decide
  have hyrow := (List.all_eq_true.mp hgrid) (y - 38)
    (List.mem_range.mpr (by omega))
  have hrrow := (List.all_eq_true.mp hyrow) (r - 8)
    (List.mem_range.mpr (by omega))
  have hchunk := (List.all_eq_true.mp hrrow) k
    (List.mem_range.mpr hk)
  have hchunk' : (hostileMinR y ≤ r ∧
      anchoredChunkStart k y r ≤ hardMaxT y r) →
      canonicalAnchoredChunkCost k y r ≤
        ContactRouterUniformCaps6750Research.hardAnchoredCap := by
    simpa only [hyEq, hrEq] using (of_decide_eq_true hchunk)
  exact (canonicalAnchoredCost_le_chunkCost cell cellLo cellHi hlo hhi).trans
    (hchunk' ⟨cellLo.r_lower, cellLo.t_upper⟩)

end ContactCanonicalHighSourceAnchoredCap6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactCanonicalHighSourceAnchoredCap6750Research.HardCell.canonicalAnchoredCost_le_hardAnchoredCap
