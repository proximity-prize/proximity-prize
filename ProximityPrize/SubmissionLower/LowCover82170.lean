import ProximityPrize.SubmissionLower.LowAnchor82170
import ProximityPrize.SubmissionLower.PrimaryRows82170

set_option Elab.async false
namespace LowCover82170
noncomputable section
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open P3 (K I node)
open PrimaryRows82170 (TrueWeightLE)
open K1_13 (Geom embed extend Row shape InBox Fits atJet indexDegree jet OnFactor)
open K1_13_1 (anchorLead anchorLead_ne anchorLead_mul indexDegree_eq eval_anchorLead
  atJet_eq_anchorLead_of_top_zero)
open scoped BigOperators Polynomial
open private coeff_flatten anchorLead_term fits_of_prod from ProximityPrize.SubmissionLower.Fast040

abbrev physicalDegree : ℕ := 133367
abbrev anchorCutoff : ℕ := 90 * 179974 - 1

def SmallFactor (f : Row 4) : Prop :=
  Irreducible f ∧ 0 < (shape f).t ∧ InBox (shape f) ⟨120, 48, 10⟩ ∧
    TrueWeightLE f anchorCutoff
def LowerRow (g : Row 3) : Prop :=
  g ≠ 0 ∧ g.totalDegree ≤ 120 ∧ K1_13.indexDegree g ≤ 48 ∧ TrueWeightLE g anchorCutoff
structure Cover {n : ℕ} (Γ : Finset K) (s : K → K[X])
    (g : Row 3) (f : Fin n → Row 4) : Prop where
  lower : LowerRow g
  factors : ∀ i, SmallFactor (f i)
  different : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)
  fits : Fits (fun i => shape (f i))
  covers : ∀ γ ∈ Γ, K1_13.atJet g (extend (s γ)) = 0 ∨
    ∃ i, K1_13.OnFactor (f i) (extend (s γ))
private theorem trueWeight_iff {n D : ℕ} (P : Row n) :
    TrueWeightLE P D ↔
      ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).weightedTotalDegree
        (fun v => v.elim 1 (fun i => physicalDegree - i.val)) ≤ D := by
  classical
  rw [MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
  constructor
  · intro h u hu
    have hc : (P.coeff u.some).coeff (u none) ≠ 0 := by
      rw [← coeff_flatten, Finsupp.optionElim_some]
      exact MvPolynomial.mem_support_iff.mp hu
    have hm : u.some ∈ P.support :=
      MvPolynomial.mem_support_iff.mpr (fun hz => hc (by simp [hz]))
    have hi := Polynomial.le_natDegree_of_ne_zero hc
    rw [← Finsupp.optionElim_some u, Finsupp.weight_optionElim, one_mul]
    apply (Nat.add_le_add_right hi _).trans
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using h _ hm
  · intro h m hm
    let d := (P.coeff m).natDegree
    have hc : (P.coeff m).coeff d ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hm)
    have hu : m.optionElim d ∈ ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).support :=
      MvPolynomial.mem_support_iff.mpr (by rwa [coeff_flatten])
    have hb := h _ hu
    rw [Finsupp.weight_optionElim, one_mul] at hb
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using hb
private theorem differentialWeight_eq : differentialWeight (d := 3) physicalDegree =
    fun v => v.elim 1 (fun i => physicalDegree - i.val) := by
  funext v
  cases v <;> rfl
section FactorCover
open MvPolynomial UniqueFactorizationMonoid
private theorem lower_of_anchor (P : Row 4) (hP : P ≠ 0)
    (hbox : InBox (shape P) ⟨120, 48, 10⟩) (hw : TrueWeightLE P anchorCutoff) :
    LowerRow (anchorLead P) := by
  refine ⟨anchorLead_ne hP, ?_, ?_, ?_⟩
  · rw [← weightedTotalDegree_one, weightedTotalDegree, Finset.sup_le_iff]
    intro m hm
    obtain ⟨u, hu, _, h⟩ := anchorLead_term P m hm
    have hab := (le_weightedTotalDegree (1 : Fin 4 → ℕ) hu)
    rw [weightedTotalDegree_one] at hab
    exact (h (1 : Fin 4 → ℕ)).trans (hab.trans hbox.1)
  · rw [indexDegree_eq, weightedTotalDegree, Finset.sup_le_iff]
    intro m hm
    obtain ⟨u, hu, _, h⟩ := anchorLead_term P m hm
    have hab := le_weightedTotalDegree (fun i => i.val) hu
    rw [← indexDegree_eq] at hab
    exact (h (fun i => i.val)).trans (hab.trans hbox.2.1)
  · intro m hm
    obtain ⟨u, hu, hc, h⟩ := anchorLead_term P m hm
    have hle := h (fun i => physicalDegree - i.val)
    rw [← hc]
    apply (Nat.add_le_add_left _ _).trans (hw u hu)
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm, Fin.val_castSucc] using hle
private theorem factor_small {P f : Row 4} (hP : P ≠ 0)
    (hbox : InBox (shape P) ⟨120, 48, 10⟩) (hw : TrueWeightLE P anchorCutoff)
    (hf : Irreducible f) (ht : 0 < (shape f).t) (hd : f ∣ P) : SmallFactor f := by
  refine ⟨hf, ht, ⟨?_, ?_, ?_⟩, ?_⟩
  · have h := weightedTotalDegree_le_of_dvd (1 : Fin 4 → ℕ) hd hP
    rw [weightedTotalDegree_one, weightedTotalDegree_one] at h
    exact h.trans hbox.1
  · have h := weightedTotalDegree_le_of_dvd (fun i => i.val) hd hP
    rw [← indexDegree_eq, ← indexDegree_eq] at h
    exact h.trans hbox.2.1
  · have h := weightedTotalDegree_le_of_dvd (Pi.single (3 : Fin 4) 1) hd hP
    simp only [weightedTotalDegree_piSingle] at h
    exact h.trans hbox.2.2
  · let e := MvPolynomial.optionEquivRight Geom (Fin 4)
    have hd' : e.symm f ∣ e.symm P := _root_.map_dvd e.symm hd
    have hP' : e.symm P ≠ 0 := fun h => hP (e.symm.injective (h.trans (map_zero _).symm))
    exact (trueWeight_iff f).mpr
      ((weightedTotalDegree_le_of_dvd _ hd' hP').trans ((trueWeight_iff P).mp hw))
private theorem cover_of_anchor {Γ : Finset K} {s : K → K[X]} (P : Row 4)
    (hP : P ≠ 0) (hbox : InBox (shape P) ⟨120, 48, 10⟩)
    (hw : TrueWeightLE P anchorCutoff)
    (hz : ∀ γ ∈ Γ, atJet P (extend (s γ)) = 0) :
    ∃ (n : ℕ) (g : Row 3) (f : Fin n → Row 4), Cover Γ s g f := by
  classical
  let _ : StrongNormalizationMonoid (Row 4) := UniqueFactorizationMonoid.strongNormalizationMonoid
  let A := normalizedFactors P
  let T := A.toFinset.filter fun q => 0 < (shape q).t
  let n := Fintype.card ↥T
  let e : Fin n ≃ ↥T := (Fintype.equivFin ↥T).symm
  let f : Fin n → Row 4 := fun i => (e i).val
  have hT : ∀ q ∈ T, q ∈ A ∧ 0 < (shape q).t := by
    intro q hq
    simpa [T] using hq
  have hfi (i : Fin n) : f i ∈ A ∧ 0 < (shape (f i)).t := hT _ (e i).property
  have hd : (∏ i, f i) ∣ P := by
    have heq : (∏ i, f i) = ∏ q ∈ T, q := by
      rw [show (∏ i, f i) = ∏ q : ↥T, q.val from e.prod_comp Subtype.val]
      exact Finset.prod_coe_sort T id
    rw [heq]
    exact ((Finset.prod_dvd_prod_of_subset T A.toFinset id (Finset.filter_subset _ _)).trans
      (Multiset.toFinset_prod_dvd_prod A)).trans (prod_normalizedFactors hP).dvd
  refine ⟨n, anchorLead P, f, ⟨lower_of_anchor P hP hbox hw, ?_, ?_,
    fits_of_prod P hP hbox f (fun i => (hfi i).2) hd, ?_⟩⟩
  · intro i
    exact factor_small hP hbox hw (irreducible_of_normalized_factor _ (hfi i).1)
      (hfi i).2 (dvd_of_mem_normalizedFactors (hfi i).1)
  · intro i j hij hassoc
    apply hij
    apply e.injective
    exact Subtype.ext (mem_normalizedFactors_eq_of_associated (hfi i).1 (hfi j).1 hassoc)
  · intro γ hγ
    let S := extend (s γ)
    by_cases hg : atJet (anchorLead P) S = 0
    · exact Or.inl hg
    right
    have hSA : MvPolynomial.eval (jet S) A.prod = 0 := by
      have hdiv := _root_.map_dvd (MvPolynomial.eval (jet S)) (prod_normalizedFactors hP).symm.dvd
      change atJet P S ∣ MvPolynomial.eval (jet S) A.prod at hdiv
      rw [hz γ hγ, zero_dvd_iff] at hdiv
      exact hdiv
    rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hSA
    obtain ⟨q, hq, hqS⟩ := hSA
    have hqlead : atJet (anchorLead q) S ≠ 0 := by
      intro hzero
      obtain ⟨R, hR⟩ := dvd_of_mem_normalizedFactors hq
      apply hg
      rw [hR, anchorLead_mul, atJet, map_mul]
      exact mul_eq_zero_of_left hzero _
    have hqt : 0 < (shape q).t := by
      by_contra! h
      apply hqlead
      rw [← atJet_eq_anchorLead_of_top_zero q S (Nat.eq_zero_of_le_zero h)]
      exact hqS
    have hqT : q ∈ T := Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hq, hqt⟩
    let j := e.symm ⟨q, hqT⟩
    have hj : f j = q := congrArg Subtype.val (e.apply_symm_apply ⟨q, hqT⟩)
    exact ⟨j, by rw [hj, OnFactor, ← eval_anchorLead]; exact ⟨hqS, hqlead⟩⟩
end FactorCover

theorem scalar_degree {cap u del Γ} (M : P1.ModelAt cap u del)
    (F : P1.FamilyAt 179974 M Γ) (hh : M.overhead ≤ 2296) {γ} (hγ : γ ∈ Γ) :
    (F.scalar γ).natDegree ≤ physicalDegree := by
  obtain hz | hdeg := (F.mark γ hγ).scalar_degree
  · simp [hz]
  · change ((F.scalar γ).natDegree : ℤ) ≤ (131072 : ℤ) - 1 + M.overhead at hdeg
    change (F.scalar γ).natDegree ≤ 133367
    omega

/-- Factor cover for every anchored family through overhead 2,296. -/
theorem family_cover {cap u del Γ} (M : P1.ModelAt cap u del)
    (F : P1.FamilyAt 179974 M Γ) (hh : M.overhead ≤ 2296) :
    ∃ (n : ℕ) (g : Row 3) (f : Fin n → Row 4), Cover Γ F.scalar g f := by
  obtain ⟨P, hP, hb, hw, hz⟩ := LowAnchor82170.exists_anchor M.word
  apply cover_of_anchor P hP hb
  · apply (trueWeight_iff P).mpr
    rw [← differentialWeight_eq, ← differentialWeightedDegree]
    exact Nat.le_pred_of_lt hw
  · intro γ hγ
    have mark := F.mark γ hγ
    exact hz _ mark.bad.support (scalar_degree M F hh hγ) mark.bad.agreement mark.scalar_hits

#print axioms family_cover
end
end LowCover82170
