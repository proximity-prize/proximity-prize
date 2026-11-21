import ArkLib.ToMathlib.RingTheory.MvPolynomial.StandardMonomials
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import ProximityPrize.SubmissionLower.Pack_K1_14_2_1Split
set_option Elab.async false
set_option autoImplicit true
section
set_option autoImplicit false
namespace K1_13_6_2_3_3_1
noncomputable section
open MvPolynomial
open scoped MonomialOrder BigOperators
variable {k σ : Type*} [Field k] [Finite σ]
theorem exists_degree_shift (I : Ideal (MvPolynomial σ k)) (g : MvPolynomial σ k) :
    ∃ C : ℕ, ∀ f ∈ I ⊔ Ideal.span {g}, ∃ q : MvPolynomial σ k,
      f - q * g ∈ I ∧ q.totalDegree ≤ f.totalDegree + C := by
  classical
  let := Fintype.ofFinite σ
  let : LinearOrder σ := LinearOrder.lift' _ (Fintype.equivFin σ).injective
  let : WellFoundedGT σ := Finite.to_wellFoundedGT
  let m : MonomialOrder σ := MonomialOrder.degLex
  let J := I ⊔ Ideal.span {g}
  obtain ⟨E, hE⟩ := m.exists_finset_standardExponents_iff J
  have hex (e : E) : ∃ b ∈ J, b ≠ 0 ∧ m.degree b ≤ (e : σ →₀ ℕ) := by
    by_contra! h
    have hs : (e : σ →₀ ℕ) ∈ m.standardExponents J := fun b hb hn => h b hb hn
    exact (hE _).mp hs _ e.property le_rfl
  choose b hb hn he using hex
  let B : Set (MvPolynomial σ k) := Set.range b
  let : Fintype B := (Set.finite_range b).fintype
  have hB (x : B) : (x : MvPolynomial σ k) ∈ J ∧ (x : MvPolynomial σ k) ≠ 0 := by
    obtain ⟨e, h⟩ := x.property
    rw [← h]
    exact ⟨hb e, hn e⟩
  have hrep (x : B) : ∃ q : MvPolynomial σ k, (x : MvPolynomial σ k) - q * g ∈ I := by
    obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp (hB x).1
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hj
    refine ⟨q, ?_⟩
    rw [← hij, mul_comm g q, add_sub_cancel_right]
    exact hi
  choose a ha using hrep
  refine ⟨Finset.univ.sup fun x : B => (a x).totalDegree, ?_⟩
  intro f hf
  obtain ⟨c, r, hfr, hc, hr⟩ :=
    m.div_set (B := B) (fun x hx => m.isUnit_leadingCoeff.mpr (hB ⟨x, hx⟩).2) f
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hfr
  have hsum : ∑ x ∈ c.support, c x • (x : MvPolynomial σ k) ∈ J :=
    J.sum_mem fun x _ => J.smul_mem (c x) (hB x).1
  have hrJ : r ∈ J := by
    convert J.sub_mem hf hsum using 1
    rw [hfr, add_comm, add_sub_cancel_right]
  have hr0 : r = 0 := by
    by_contra hr0
    have hstd : m.degree r ∈ m.standardExponents J := by
      apply (hE _).mpr
      intro e heE hle
      exact hr _ (m.degree_mem_support hr0) (b ⟨e, heE⟩) ⟨⟨e, heE⟩, rfl⟩
        ((he ⟨e, heE⟩).trans hle)
    exact hstd r hrJ hr0 le_rfl
  refine ⟨∑ x ∈ c.support, c x * a x, ?_, ?_⟩
  · rw [Finset.sum_mul, hfr, hr0, add_zero, ← Finset.sum_sub_distrib]
    exact I.sum_mem fun x _ => by
      simpa only [smul_eq_mul, mul_sub, mul_assoc] using I.mul_mem_left (c x) (ha x)
  · apply totalDegree_finsetSum_le
    intro x _
    have hcx : (c x).totalDegree ≤ f.totalDegree := by
      by_cases hx : c x = 0
      · simp [hx]
      have hx' := m.totalDegree_le_of_degree_le
        (fun _ _ h => degree_le_degree_of_degLex_le h) (hc x)
      rw [totalDegree_mul_of_isDomain (hB x).2 hx] at hx'
      omega
    exact (totalDegree_mul _ _).trans
      (Nat.add_le_add hcx (Finset.le_sup (f := fun y : B => (a y).totalDegree) (Finset.mem_univ x)))
end
end K1_13_6_2_3_3_1
end
