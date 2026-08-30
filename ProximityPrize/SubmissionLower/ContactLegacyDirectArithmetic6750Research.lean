import ProximityPrize.SubmissionLower.ContactLegacyOldGCountProvider6750Research
import ProximityPrize.SubmissionLower.ContactUpstreamTAnalytic6750Research

namespace ProximityPrize.SubmissionLower.ContactLegacyDirectArithmetic6750Research

open ProximityPrize.Benchmark
open ContactFactorCaps
open ContactIdentityResidualGlobalFlagResearch
open ContactResidualSupportParametersResearch
open ContactTwoTailParameters6750Research
open ContactTwoTailResidualGeneric6750Research
open ContactRouterCellCosts6750Research
open ContactAnchoredOneFamilySelector6750Research
open ContactAnchoredHardCellSelector6750Research
open ContactOrdinaryHardShell6750Research
open ContactSelectedCount6750Research
open ContactSelectedCountHighTRepair6750Research
open ContactSelectedOldCoreLowQuotients6750Research
open ContactLegacyTwoFactorEasy6750Research
open ContactLegacyOldGCountProvider6750Research
open ContactTightSingularLedgerResearch
open ContactRecursiveResidualStages6656Research

set_option autoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 300000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

def directPaddedR (r : Nat) : Nat := max 2 r
def directPaddedY (y r : Nat) : Nat := max (directPaddedR r + 1) y
def directPaddedT (t y r : Nat) : Nat := max (directPaddedY y r) t

def directEquationCap (t y r : Nat) : Nat :=
  cellRegularCost (directPaddedT t y r) (directPaddedY y r)
      (directPaddedR r) +
    (cellTightProfile profileA.weightedCap (directPaddedT t y r)
      (directPaddedR r)).countCap

theorem tightCount_mono_D {D₁ D₂ t r : Nat} (hD : D₁ ≤ D₂) :
    (cellTightProfile D₁ t r).countCap ≤
      (cellTightProfile D₂ t r).countCap := by
  unfold cellTightProfile
  simp only [TightParameters.countCap, TightParameters.tightNumerator,
    TightParameters.coreNumerator, TightParameters.aggregateCost,
    TightParameters.agreement, TightParameters.implicitYCap,
    TightParameters.algebraicCap, TightParameters.kappa,
    TightParameters.errors, TightParameters.gap,
    ContactSingularLedger6600Research.dot]
  gcongr

theorem directEquationCap_mono_total {t₁ t₂ y r : Nat} (ht : t₁ ≤ t₂) :
    directEquationCap t₁ y r ≤ directEquationCap t₂ y r := by
  have hp : directPaddedT t₁ y r ≤ directPaddedT t₂ y r := by
    exact max_le_max_left (directPaddedY y r) ht
  unfold directEquationCap
  exact Nat.add_le_add
    (ContactCanonicalHighSourceAnchoredCap6750Research.cellRegularCost_mono_total hp)
    (ContactCanonicalHighSourceAnchoredCap6750Research.tightCount_mono_total hp)

theorem ordinaryReplacementCost_mono_total
    {t₁ t₂ y r : Nat} (ht : t₁ ≤ t₂) :
    ordinaryReplacementCost t₁ y r ≤ ordinaryReplacementCost t₂ y r := by
  unfold ordinaryReplacementCost
  exact Nat.add_le_add
    (ContactCanonicalHighSourceAnchoredCap6750Research.cellRegularCost_mono_total ht)
    (ContactCanonicalHighSourceAnchoredCap6750Research.tightCount_mono_total ht)

theorem directEquationCap_eq_ordinaryReplacementCost
    {t y r : Nat} (hr : 2 ≤ r) (hry : r < y) (hyt : y ≤ t) :
    directEquationCap t y r = ordinaryReplacementCost t y r := by
  simp only [directEquationCap, directPaddedT, directPaddedY, directPaddedR,
    max_eq_right hr, max_eq_right (by omega : r + 1 ≤ y),
    max_eq_right hyt, ordinaryReplacementCost]

theorem factorEquationCost_oldCommonCore_le
    {u₀ u₁ : I → K} (S : SelectedInterpolants6750 u₀ u₁) :
    factorEquationCost (oldCommonCore S) ≤
      directEquationCap (oldCoreTotal S) (oldCoreYS S) (oldCoreS S) := by
  have hc := oldCommonCore_contact_le S
  have hc' : factorContact (oldCommonCore S) ≤ 8548547 := by
    simpa only [factorContact, w] using hc
  have hprofileD : profileA.weightedCap = 8548548 := by
    norm_num [profileA, Profile.weightedCap,
      ContactTwoTailParameters6750Research.agreements, n, errors]
  have hD : factorD (oldCommonCore S) ≤ profileA.weightedCap := by
    rw [hprofileD]
    simp only [factorD]
    apply max_le
    · norm_num [w]
    · omega
  have h := tightCount_mono_D
    (t := factorPaddedT (oldCommonCore S))
    (r := factorPaddedR (oldCommonCore S)) hD
  simpa only [factorEquationCost, directEquationCap,
    factorPaddedT, factorPaddedY, factorPaddedR,
    directPaddedT, directPaddedY, directPaddedR,
    factorTotal, factorYS, factorS, oldCoreTotal, oldCoreYS, oldCoreS]
    using Nat.add_le_add_left h
      (cellRegularCost (factorPaddedT (oldCommonCore S))
        (factorPaddedY (oldCommonCore S))
        (factorPaddedR (oldCommonCore S)))

def directBand (y r : Nat) : Bool :=
  decide (38 ≤ y ∧ y ≤ 65 ∧ hostileMinR y ≤ r ∧ r ≤ 14)

def directTop (y r : Nat) : Nat :=
  if directBand y r then hardMinT y r - 1 else 1659

def directChunkStart (width y k : Nat) : Nat := y + k * width
def directChunkCount (width y r : Nat) : Nat :=
  (directTop y r - y) / width + 1
def directChunkEnd (width y r k : Nat) : Nat :=
  min (directTop y r) (directChunkStart width y k + width - 1)
def directSeparatedCost (width y r k : Nat) : Nat :=
  upstreamCellCost (directChunkStart width y k) y r +
    ordinaryReplacementCost (directChunkEnd width y r k) y r

def directPairOK (width y r : Nat) : Bool :=
  (List.range (directChunkCount width y r)).all fun k ↦
    decide (directSeparatedCost width y r k ≤
      ContactMovingProtocol6750Research.mcaBudget)

def chooseDirectWidth : List Nat → Nat → Nat → Nat
  | [], _, _ => 1
  | width :: widths, y, r =>
      if directPairOK width y r then width else chooseDirectWidth widths y r

def directWidths : List Nat := [4096, 1024, 512, 256, 128, 64, 32, 16, 8, 4, 2]
def directWidth (y r : Nat) : Nat := chooseDirectWidth directWidths y r

theorem directWidth_pos : ∀ (y : Fin 66) (r : Fin 15),
    0 < directWidth y.1 r.1 := by
  intro y r
  simp only [directWidth, directWidths, chooseDirectWidth]
  split_ifs <;> norm_num

theorem directWidth_pairOK : ∀ (y : Fin 66) (r : Fin 15),
    2 ≤ r.1 → r.1 < y.1 → directPairOK (directWidth y.1 r.1) y.1 r.1 = true := by
  decide

theorem directBasicEndpoint
    {t y r : Nat} (hr : 2 ≤ r) (hry : r < y) (hyt : y ≤ t)
    (htop : t ≤ directTop y r) (hycap : y ≤ 65) (hrcap : r ≤ 14) :
    upstreamCellCost t y r + ordinaryReplacementCost t y r ≤
      ContactMovingProtocol6750Research.mcaBudget := by
  let width := directWidth y r
  let k := (t - y) / width
  have hw : 0 < width := directWidth_pos ⟨y, by omega⟩ ⟨r, by omega⟩
  have hk : k < directChunkCount width y r := by
    have hsub : t - y ≤ directTop y r - y := Nat.sub_le_sub_right htop y
    have hdiv := Nat.div_le_div_right hsub (c := width)
    simp only [k, directChunkCount]
    omega
  have hdecomp := Nat.div_add_mod (t - y) width
  have hmod := Nat.mod_lt (t - y) hw
  have heq : y + (t - y) = t := Nat.add_sub_of_le hyt
  have hlo : directChunkStart width y k ≤ t := by
    have hm := Nat.div_mul_le_self (t - y) width
    unfold directChunkStart k
    omega
  have hhi : t ≤ directChunkEnd width y r k := by
    unfold directChunkEnd directChunkStart k
    apply (Nat.le_min).2
    constructor
    · exact htop
    · have hmod' : (t - y) % width ≤ width - 1 := by omega
      have hdecomp' : k * width + (t - y) % width = t - y := by
        simpa only [k, Nat.mul_comm] using hdecomp
      calc
        t = y + (t - y) := heq.symm
        _ = y + (k * width + (t - y) % width) := by rw [hdecomp']
        _ ≤ y + (k * width + (width - 1)) := by omega
        _ = y + k * width + width - 1 := by omega
  have hok := directWidth_pairOK ⟨y, by omega⟩ ⟨r, by omega⟩ hr hry
  change (List.range (directChunkCount width y r)).all
      (fun k ↦ decide (directSeparatedCost width y r k ≤
        ContactMovingProtocol6750Research.mcaBudget)) = true at hok
  have hentry := (List.all_eq_true.mp hok) k (List.mem_range.mpr hk)
  have hcap := of_decide_eq_true hentry
  have hu := ContactUpstreamTAnalytic6750Research.upstreamCellCost_antitone_total
    (y := y) (r := r) hlo
  have he := ordinaryReplacementCost_mono_total (y := y) (r := r) hhi
  unfold directSeparatedCost at hcap
  have hsum : upstreamCellCost t y r + ordinaryReplacementCost t y r ≤
      upstreamCellCost (directChunkStart width y k) y r +
        ordinaryReplacementCost (directChunkEnd width y r k) y r :=
    Nat.add_le_add hu he
  exact hsum.trans hcap

def directDegenerateCap (y r : Nat) : Nat :=
  upstreamCellCost y y r + directEquationCap 1666 y r

theorem directDegenerateReceipt : ∀ (y : Fin 66) (r : Fin 15),
    r.1 ≤ y.1 → (r.1 < 2 ∨ y.1 ≤ r.1) →
    directDegenerateCap y.1 r.1 ≤ ContactMovingProtocol6750Research.mcaBudget := by
  decide

theorem oldCoreS_le_YS
    {u₀ u₁ : I → K} (S : SelectedInterpolants6750 u₀ u₁) :
    oldCoreS S ≤ oldCoreYS S := by
  apply (weightedTotalDegree_le_iff residualSWeights
    (oldCommonCore S) (oldCoreYS S)).mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h ⊢
  simp [oldCoreYS, residualSWeights, residualYSWeights] at h ⊢
  omega

theorem directOldGLedger6750 : DirectOldGLedger6750 := by
  intro u₀ u₁ S hlegacy hnot
  let t := oldCoreTotal S
  let y := oldCoreYS S
  let r := oldCoreS S
  have hry : r ≤ y := by simpa only [r, y] using oldCoreS_le_YS S
  have hyt : y ≤ t := by
    simpa only [y, t] using oldCommonCore_ys_le_total S
  have htcap : t ≤ 1666 := by simpa only [t] using oldCommonCore_total_le S
  have hycap : y ≤ 65 := by simpa only [y] using oldCommonCore_ys_le S
  have hrcap : r ≤ 14 := by simpa only [r] using oldCommonCore_slope_le S
  have heq := factorEquationCost_oldCommonCore_le S
  by_cases hr : 2 ≤ r
  · by_cases hry' : r < y
    · have httop : t ≤ 1659 := by
        rcases hlegacy with ht | hd
        · omega
        · rcases hd with hr' | hy'
          · omega
          · omega
      have htop : t ≤ directTop y r := by
        unfold directTop
        split_ifs with hband
        · have hlt : t < hardMinT y r := by
            by_contra hn
            have hband' : 38 ≤ y ∧ y ≤ 65 ∧
                hostileMinR y ≤ r ∧ r ≤ 14 :=
              of_decide_eq_true (by simpa only [directBand] using hband)
            have hord : OrdinaryHardCell t y r :=
              ⟨hband'.1, hband'.2.1, hband'.2.2.1, hband'.2.2.2,
                by omega, httop⟩
            exact hnot (by simpa only [t, y, r] using hord)
          omega
        · exact httop
      have heq' : factorEquationCost (oldCommonCore S) ≤
          ordinaryReplacementCost t y r := by
        rw [← directEquationCap_eq_ordinaryReplacementCost hr hry' hyt]
        simpa only [t, y, r] using heq
      have hcap := directBasicEndpoint hr hry' hyt htop hycap hrcap
      simpa only [t, y, r] using (Nat.add_le_add_left heq' _).trans hcap
    · have hdeg : r < 2 ∨ y ≤ r := Or.inr (by omega)
      have hu := ContactUpstreamTAnalytic6750Research.upstreamCellCost_antitone_total
        (y := y) (r := r) hyt
      have hem := directEquationCap_mono_total (y := y) (r := r) htcap
      have hcap := directDegenerateReceipt ⟨y, by omega⟩ ⟨r, by omega⟩ hry hdeg
      have hall := Nat.add_le_add hu (heq.trans hem)
      simpa only [directDegenerateCap, t, y, r] using hall.trans hcap
  · have hdeg : r < 2 ∨ y ≤ r := Or.inl (by omega)
    have hu := ContactUpstreamTAnalytic6750Research.upstreamCellCost_antitone_total
      (y := y) (r := r) hyt
    have hem := directEquationCap_mono_total (y := y) (r := r) htcap
    have hcap := directDegenerateReceipt ⟨y, by omega⟩ ⟨r, by omega⟩ hry hdeg
    have hall := Nat.add_le_add hu (heq.trans hem)
    simpa only [directDegenerateCap, t, y, r] using hall.trans hcap

end ProximityPrize.SubmissionLower.ContactLegacyDirectArithmetic6750Research

#print axioms ProximityPrize.SubmissionLower.ContactLegacyDirectArithmetic6750Research.directOldGLedger6750
