import ProximityPrize.SubmissionLower.ContactRegularComponentCover
import ProximityPrize.SubmissionLower.ContactPrimeFlagBudgetFamilyResearch
import ProximityPrize.SubmissionLower.ContactTwoTailResultantProvider6732Research
namespace ProximityPrize.SubmissionLower.ContactAnchoredCongruentCuts6750Research
open scoped Classical BigOperators
open ContactCurveComponents ContactRegularComponentCover
open ContactFlagBezout6543Research ContactPrimeFlagBudgetFamilyResearch
open ContactTwoTailResultantProvider6732Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
variable {K : Type} [Field K]
abbrev Poly3 := MvPolynomial (Fin 3) K
theorem mem_iff_of_sub_mem (P : Ideal (Poly3 (K := K)))
    {A B : Poly3 (K := K)} (h : A - B ∈ P) : A ∈ P ↔ B ∈ P := by
  constructor
  · intro hA
    simpa only [sub_sub_cancel] using P.sub_mem hA h
  · intro hB
    simpa only [sub_add_cancel] using P.add_mem h hB
theorem sub_mem_of_dvd (P : Ideal (Poly3 (K := K)))
    {G A B : Poly3 (K := K)} (hG : G ∈ P) (h : G ∣ A - B) :
    A - B ∈ P := by
  obtain ⟨Q,hQ⟩ := h
  rw [hQ]
  exact P.mul_mem_right Q hG
theorem cutIdeal_eq_of_dvd_sub {G T T' : Poly3 (K := K)}
    (h : G ∣ T - T') : cutIdeal K G T = cutIdeal K G T' := by
  have hG : G ∈ cutIdeal K G T := Ideal.subset_span (by simp)
  have hG' : G ∈ cutIdeal K G T' := Ideal.subset_span (by simp)
  have hT : T ∈ cutIdeal K G T := Ideal.subset_span (by simp)
  have hT' : T' ∈ cutIdeal K G T' := Ideal.subset_span (by simp)
  have hd := sub_mem_of_dvd (cutIdeal K G T) hG h
  have hd' := sub_mem_of_dvd (cutIdeal K G T') hG' h
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro A hA
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hA
    rcases hA with rfl | rfl
    · exact hG'
    · exact (mem_iff_of_sub_mem _ hd').mpr hT'
  · apply Ideal.span_le.mpr
    intro A hA
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hA
    rcases hA with rfl | rfl
    · exact hG
    · exact (mem_iff_of_sub_mem _ hd).mp hT
theorem regularComponents_eq_of_dvd_sub {G T T' H : Poly3 (K := K)}
    (h : G ∣ T - T') :
    regularComponents K G T H = regularComponents K G T' H := by
  classical
  ext P
  simp only [regularComponents,Finset.mem_filter,mem_componentFamily,
    cutIdeal_eq_of_dvd_sub h]
def regularComponentEquiv {G T T' H : Poly3 (K := K)}
    (h : G ∣ T - T') :
    RegularComponent K G T H ≃ RegularComponent K G T' H :=
  Equiv.subtypeEquiv (Equiv.refl _) (fun P => by
    change P ∈ regularComponents K G T H ↔
      P ∈ regularComponents K G T' H
    rw [regularComponents_eq_of_dvd_sub h])
@[simp] theorem regularComponentEquiv_val {G T T' H : Poly3 (K := K)}
    (h : G ∣ T - T') (C : RegularComponent K G T H) :
    (regularComponentEquiv h C).1 = C.1 := rfl
@[simp] theorem regularComponentEquiv_symm_val {G T T' H : Poly3 (K := K)}
    (h : G ∣ T - T') (C : RegularComponent K G T' H) :
    ((regularComponentEquiv h).symm C).1 = C.1 := rfl
def transportedMultiplicity {G T T' H : Poly3 (K := K)}
    (h : G ∣ T - T') (multiplicity : RegularComponent K G T H → ℕ) :
    RegularComponent K G T' H → ℕ :=
  fun C => multiplicity ((regularComponentEquiv h).symm C)

def PrimeFlagBudgetFamily.ofCongruentCut
    {G T T' H : Poly3 (K := K)} {p q : FlagDegree}
    (h : G ∣ T - T')
    (B : PrimeFlagBudgetFamily (G := G) (T := T') (H := H) p q) :
    PrimeFlagBudgetFamily (G := G) (T := T) (H := H) p q where
  zCost C := B.zCost (regularComponentEquiv h C)
  yzCost C := B.yzCost (regularComponentEquiv h C)
  allCost C := B.allCost (regularComponentEquiv h C)
  primeBudget C := by
    change ContactIdentityResidualZeroBudgetTransportResearch.PrimeFlagZeroBudget
      (regularComponentEquiv h C).1 (fun r =>
        r.zOnly * B.zCost (regularComponentEquiv h C) +
          r.yz * B.yzCost (regularComponentEquiv h C) +
          r.all * B.allCost (regularComponentEquiv h C))
    exact B.primeBudget (regularComponentEquiv h C)
  sum_zCost_le := by
    simpa only [(regularComponentEquiv h).sum_comp B.zCost] using B.sum_zCost_le
  sum_yzCost_le := by
    simpa only [(regularComponentEquiv h).sum_comp B.yzCost] using B.sum_yzCost_le
  sum_allCost_le := by
    simpa only [(regularComponentEquiv h).sum_comp B.allCost] using B.sum_allCost_le

theorem weightedCertificate_of_congruentCut
    {G T T' H : Poly3 (K := K)} {surfaceFlag firstTailFlag : FlagDegree}
    (h : G ∣ T - T')
    (B : PrimeFlagBudgetFamily (G := G) (T := T') (H := H)
      surfaceFlag firstTailFlag)
    (multiplicity : RegularComponent K G T H → ℕ)
    (C : RegularComponentWeightedInertiaResultantCertificate B
      (transportedMultiplicity h multiplicity)) :
    RegularComponentWeightedInertiaResultantCertificate
      (PrimeFlagBudgetFamily.ofCongruentCut h B) multiplicity where
  z := by
    have hz := C.z
    dsimp only [transportedMultiplicity] at hz
    rw [← (regularComponentEquiv h).sum_comp] at hz
    simpa only [PrimeFlagBudgetFamily.ofCongruentCut,
      Equiv.symm_apply_apply] using hz
  yz := by
    have hyz := C.yz
    dsimp only [transportedMultiplicity] at hyz
    rw [← (regularComponentEquiv h).sum_comp] at hyz
    simpa only [PrimeFlagBudgetFamily.ofCongruentCut,
      Equiv.symm_apply_apply] using hyz
  all := by
    have hall := C.all
    dsimp only [transportedMultiplicity] at hall
    rw [← (regularComponentEquiv h).sum_comp] at hall
    simpa only [PrimeFlagBudgetFamily.ofCongruentCut,
      Equiv.symm_apply_apply] using hall
end
end ProximityPrize.SubmissionLower.ContactAnchoredCongruentCuts6750Research
