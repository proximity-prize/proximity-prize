import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.I
namespace ProximityPrize.SubmissionLower.ContactCongruentCuts6643Research
open scoped Classical BigOperators
open ContactCurveComponents ContactRegularComponentCover
open ContactFlagBezout6543Research
open ContactResidualSparseComponentAdapterResearch
open ContactIdentityResidualZeroBudgetTransportResearch
open ContactPrimeFlagBudgetFamilyResearch
noncomputable section
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
   RegularComponent K G T H ≃ RegularComponent K G T' H where
 toFun C := ⟨C.1,(regularComponents_eq_of_dvd_sub h) ▸ C.2⟩
 invFun C := ⟨C.1,(regularComponents_eq_of_dvd_sub h).symm ▸ C.2⟩
 left_inv C := by rfl
 right_inv C := by rfl
@[simp] theorem regularComponentEquiv_val {G T T' H : Poly3 (K := K)}
   (h : G ∣ T - T') (C : RegularComponent K G T H) :
   (regularComponentEquiv h C).1 = C.1 := rfl
@[simp] theorem regularComponentEquiv_symm_val {G T T' H : Poly3 (K := K)}
   (h : G ∣ T - T') (C : RegularComponent K G T' H) :
   ((regularComponentEquiv h).symm C).1 = C.1 := rfl
theorem eval_eq_of_sub_mem (P : Ideal (Poly3 (K := K)))
   {A B : Poly3 (K := K)} (h : A - B ∈ P) (v : Fin 3 → K)
   (hv : P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom) :
   MvPolynomial.aeval v A = MvPolynomial.aeval v B := by
 have hz := hv h
 change MvPolynomial.aeval v (A - B) = 0 at hz
 rw [map_sub] at hz
 exact sub_eq_zero.mp hz
theorem finiteZeroSetBound_of_sub_mem (P : Ideal (Poly3 (K := K)))
   {A B : Poly3 (K := K)} {cost : ℕ}
   (h : A - B ∈ P) (hB : FiniteZeroSetBound P B cost) :
   FiniteZeroSetBound P A cost := by
 intro points hpointsP hpointsA
 apply hB points hpointsP
 intro v hv
 rw [← eval_eq_of_sub_mem P h v (hpointsP v hv)]
 exact hpointsA v hv
def PolynomialInFlagMod (P : Ideal (Poly3 (K := K)))
   (r : FlagDegree) (A : Poly3 (K := K)) : Prop :=
 ∃ B,PolynomialInFlag r B ∧ A - B ∈ P
theorem PolynomialInFlagMod.mono {P Q : Ideal (Poly3 (K := K))}
   {r : FlagDegree} {A : Poly3 (K := K)} (hPQ : P ≤ Q)
   (h : PolynomialInFlagMod P r A) : PolynomialInFlagMod Q r A := by
 obtain ⟨B,hB,hAB⟩ := h
 exact ⟨B,hB,hPQ hAB⟩
theorem PolynomialInFlagMod.of_surface_mem
   {P : Ideal (Poly3 (K := K))} {G A : Poly3 (K := K)}
   {r : FlagDegree} (hG : G ∈ P)
   (h : PolynomialInFlagMod (Ideal.span {G}) r A) :
   PolynomialInFlagMod P r A := by
 apply PolynomialInFlagMod.mono (P := Ideal.span {G}) (Q := P) _ h
 apply Ideal.span_le.mpr
 intro B hB
 change B ∈ P
 rcases Set.mem_singleton_iff.mp hB with rfl
 exact hG
theorem PrimeFlagZeroBudget.zero_le_congr
   {P : Ideal (Poly3 (K := K))} {cost : FlagDegree → ℕ}
   (B : PrimeFlagZeroBudget P cost) (r : FlagDegree)
   (A : Poly3 (K := K)) (hA : PolynomialInFlagMod P r A)
   (hproper : A ∉ P) : FiniteZeroSetBound P A (cost r) := by
 obtain ⟨A',hflag,hcongr⟩ := hA
 have hproper' : A' ∉ P := by
   intro hmem
   exact hproper ((mem_iff_of_sub_mem P hcongr).mpr hmem)
 exact finiteZeroSetBound_of_sub_mem P hcongr (B.zero_le r A' hflag hproper')
def PrimeFlagBudgetFamily.ofCongruentCut
   {G T T' H : Poly3 (K := K)} {p q : FlagDegree}
   (h : G ∣ T - T')
   (B : PrimeFlagBudgetFamily (G := G) (T := T') (H := H) p q) :
   PrimeFlagBudgetFamily (G := G) (T := T) (H := H) p q where
 zCost C := B.zCost (regularComponentEquiv h C)
 yzCost C := B.yzCost (regularComponentEquiv h C)
 allCost C := B.allCost (regularComponentEquiv h C)
 primeBudget C := B.primeBudget (regularComponentEquiv h C)
 sum_zCost_le := by
   simpa only [(regularComponentEquiv h).sum_comp B.zCost] using B.sum_zCost_le
 sum_yzCost_le := by
   simpa only [(regularComponentEquiv h).sum_comp B.yzCost] using B.sum_yzCost_le
 sum_allCost_le := by
   simpa only [(regularComponentEquiv h).sum_comp B.allCost] using B.sum_allCost_le
theorem PrimeFlagBudgetFamily.ofCongruentCut_positive
   {G T T' H : Poly3 (K := K)} {p q : FlagDegree}
   (h : G ∣ T - T')
   (B : PrimeFlagBudgetFamily (G := G) (T := T') (H := H) p q)
   (hpos : ∀ C,1 ≤ B.zCost C + B.yzCost C) :
   ∀ C,1 ≤ (PrimeFlagBudgetFamily.ofCongruentCut h B).zCost C +
     (PrimeFlagBudgetFamily.ofCongruentCut h B).yzCost C := by
 intro C
 exact hpos (regularComponentEquiv h C)
theorem PrimeFlagBudgetFamily.ofCongruentCut_z_positive
   {G T T' H : Poly3 (K := K)} {p q : FlagDegree}
   (h : G ∣ T - T')
   (B : PrimeFlagBudgetFamily (G := G) (T := T') (H := H) p q)
   (i : Fin 3)
   (hpos : ∀ C,Transcendental K
     (ActualCurveCoordinateField.coordinate K C.1 i) → 1 ≤ B.zCost C) :
   ∀ C,Transcendental K
     (ActualCurveCoordinateField.coordinate K C.1 i) →
     1 ≤ (PrimeFlagBudgetFamily.ofCongruentCut h B).zCost C := by
 intro C htr
 exact hpos (regularComponentEquiv h C) htr
theorem PrimeFlagBudgetFamily.ofCongruentCut_yz_positive
   {G T T' H : Poly3 (K := K)} {p q : FlagDegree}
   (h : G ∣ T - T')
   (B : PrimeFlagBudgetFamily (G := G) (T := T') (H := H) p q)
   (i : Fin 3)
   (hpos : ∀ C,¬ Transcendental K
     (ActualCurveCoordinateField.coordinate K C.1 i) → 1 ≤ B.yzCost C) :
   ∀ C,¬ Transcendental K
     (ActualCurveCoordinateField.coordinate K C.1 i) →
     1 ≤ (PrimeFlagBudgetFamily.ofCongruentCut h B).yzCost C := by
 intro C htr
 exact hpos (regularComponentEquiv h C) htr
end
end ProximityPrize.SubmissionLower.ContactCongruentCuts6643Research
