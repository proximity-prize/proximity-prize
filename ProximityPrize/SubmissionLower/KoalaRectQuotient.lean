import ProximityPrize.SubmissionLower.UpperBranch5

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace KoalaRect
noncomputable section

open Polynomial MvPolynomial
open K1_14 (FX Equation)
open Cardinal
open private seedView seedView_coeff flatten from ProximityPrize.SubmissionLower.Fast069

/-- Degree in one seed coordinate with the ordinate kept in the coefficient ring. -/
def axisDegree (f : Equation) (z : Fin 2) : ℕ := (seedView f).degreeOf z

theorem axisDegree_le_iff (f : Equation) (z : Fin 2) (u : ℕ) :
    axisDegree f z ≤ u ↔ ∀ i : ℕ, (f.coeff i).degreeOf z ≤ u := by
  unfold axisDegree
  constructor
  · intro h i
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    have hs : d ∈ (seedView f).support := by
      rw [MvPolynomial.mem_support_iff] at hd ⊢
      intro hz
      apply hd
      rw [← seedView_coeff, hz, Polynomial.coeff_zero]
    exact (MvPolynomial.degreeOf_le_iff.mp h) d hs
  · intro h
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp hd)
    apply (MvPolynomial.degreeOf_le_iff.mp (h i)) d
    rwa [MvPolynomial.mem_support_iff, ← seedView_coeff, ← Polynomial.mem_support_iff]

theorem axisDegree_mul {f g : Equation} (hf : f ≠ 0) (hg : g ≠ 0) (z : Fin 2) :
    axisDegree (f * g) z = axisDegree f z + axisDegree g z := by
  unfold axisDegree
  rw [map_mul, MvPolynomial.degreeOf_mul_eq (by simpa using hf) (by simpa using hg)]

theorem axisDegree_pow {f : Equation} (hf : f ≠ 0) (n : ℕ) (z : Fin 2) :
    axisDegree (f ^ n) z = n * axisDegree f z := by
  induction n with
  | zero => simp [axisDegree]
  | succ n ih => rw [pow_succ, axisDegree_mul (pow_ne_zero _ hf) hf, ih, Nat.succ_mul]

private abbrev QuotientSlots (a : ℕ) (u : Fin 2 → ℕ) := Fin a × (∀ z : Fin 2, Fin (u z))

private def quotientExponent {a : ℕ} {u : Fin 2 → ℕ} (k : QuotientSlots a u) :
    Option (Fin 2) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun z => z.elim k.1.val (fun i => (k.2 i).val))

private def quotientSupport (a : ℕ) (u : Fin 2 → ℕ) : Finset (Option (Fin 2) →₀ ℕ) :=
  Finset.univ.image (quotientExponent (a := a) (u := u))

private theorem flatten_mem_quotientSupport {q : Equation} {a : ℕ} {u : Fin 2 → ℕ}
    (hy : q.natDegree < a) (hu : ∀ z, axisDegree q z < u z) :
    flatten q ∈ restrictSupport FX (↑(quotientSupport a u) : Set (Option (Fin 2) →₀ ℕ)) := by
  apply (MvPolynomial.mem_restrictSupport_iff FX).mpr
  intro m hm
  have hc : ((seedView q).coeff m.some).coeff (m none) ≠ 0 := by
    change ((optionEquivRight FX (Fin 2) (flatten q)).coeff m.some).coeff (m none) ≠ 0
    rw [optionEquivRight_coeff_coeff, Finsupp.optionElim_some]
    exact MvPolynomial.mem_support_iff.mp hm
  have hs : m.some ∈ (seedView q).support :=
    MvPolynomial.mem_support_iff.mpr (fun hz => hc (by rw [hz, Polynomial.coeff_zero]))
  have hq : (q.coeff (m none)).coeff m.some ≠ 0 := by rwa [← seedView_coeff]
  have hmY : m none < a := (Polynomial.le_natDegree_of_ne_zero (fun hz => hq (by simp [hz]))).trans_lt hy
  have hmU (z : Fin 2) : m (some z) < u z :=
    (MvPolynomial.le_degreeOf_of_mem_support z hs).trans_lt (hu z)
  let k : QuotientSlots a u := ⟨⟨m none, hmY⟩, fun z => ⟨m (some z), hmU z⟩⟩
  change m ∈ quotientSupport a u
  refine Finset.mem_image.mpr ⟨k, Finset.mem_univ _, ?_⟩
  ext z
  cases z <;> simp [quotientExponent, k]

/-- Dividing by `g` spends the ordinate degree and the two seed degrees independently. -/
theorem rank_rect_multiples_le (C : Submodule FX Equation) {g : Equation} (hg : g ≠ 0)
    {a yspent : ℕ} {U spent : Fin 2 → ℕ} (hyspent : yspent ≤ g.natDegree)
    (hspent : ∀ z, spent z ≤ axisDegree g z)
    (hC : ∀ c ∈ C, c ≠ 0 → c.natDegree < a ∧
      (∀ i z, (c.coeff i).degreeOf z ≤ U z) ∧ g ∣ c) :
    Module.rank FX C ≤ (↑((a - yspent) * (U 0 + 1 - spent 0) * (U 1 + 1 - spent 1)) : Cardinal) := by
  classical
  let u (z : Fin 2) := U z + 1 - spent z
  let S := quotientSupport (a - yspent) u
  let B := restrictSupport FX (↑S : Set (Option (Fin 2) →₀ ℕ))
  let _ : Module.Finite FX B := restrictSupport_finite S.finite_toSet
  let m : B →ₗ[FX] Equation :=
    (LinearMap.mulLeft FX g).comp (flatten.symm.toLinearMap.comp B.subtype)
  have hm : C ≤ LinearMap.range m := by
    intro c hc
    by_cases hn : c = 0
    · rw [hn]
      exact (LinearMap.range m).zero_mem
    · obtain ⟨hY, hU, q, rfl⟩ := hC c hc hn
      have hq : q ≠ 0 := right_ne_zero_of_mul hn
      have hqY : q.natDegree < a - yspent := by
        rw [Polynomial.natDegree_mul hg hq] at hY
        omega
      have hqU (z : Fin 2) : axisDegree q z < u z := by
        have hu := (axisDegree_le_iff (g * q) z (U z)).mpr (fun i => hU i z)
        rw [axisDegree_mul hg hq] at hu
        have hs := hspent z
        dsimp [u]
        omega
      refine ⟨⟨flatten q, flatten_mem_quotientSupport hqY hqU⟩, ?_⟩
      change g * flatten.symm (flatten q) = g * q
      rw [AlgEquiv.symm_apply_apply]
  have hB : Module.finrank FX B ≤ (a - yspent) * (U 0 + 1 - spent 0) * (U 1 + 1 - spent 1) := by
    rw [MvPolynomial.finrank_restrictSupport_finset]
    calc
      S.card ≤ Fintype.card (QuotientSlots (a - yspent) u) := by
        simpa only [S, quotientSupport, Finset.card_univ] using
          (Finset.card_image_le (s := (Finset.univ : Finset (QuotientSlots (a - yspent) u)))
            (f := quotientExponent))
      _ = _ := by
        simp only [QuotientSlots, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin, Fin.prod_univ_two, u]
        rw [Nat.mul_assoc]
  calc
    _ ≤ Module.rank FX (LinearMap.range m) := Submodule.rank_mono hm
    _ ≤ Module.rank FX B := rank_range_le m
    _ ≤ _ := by rw [← Module.finrank_eq_rank]; exact_mod_cast hB

#print axioms axisDegree_pow
#print axioms rank_rect_multiples_le

end
end KoalaRect
