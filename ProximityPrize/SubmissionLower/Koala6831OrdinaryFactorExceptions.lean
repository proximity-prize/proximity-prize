import ProximityPrize.SubmissionLower.Koala6831CarrierExceptions

namespace ProximityPrize.SubmissionLower.Koala6831OrdinaryFactorExceptions

open Koala6831BivariateSeeds
open scoped Classical Polynomial
open MvPolynomial

noncomputable section

set_option autoImplicit false

variable {E : Type*} [Field E]

def point (seed value frobeniusSeed : E) : Fin 3 → E := ![seed, value, frobeniusSeed]

def pack (E : Type*) [Field E] :
    MvPolynomial (Fin 3) E ≃ₐ[E] Polynomial (SeedPolynomial E) :=
  (MvPolynomial.renameEquiv E (Equiv.swap (0 : Fin 3) 1)).trans
    (MvPolynomial.finSuccEquiv E 2)

private theorem pack_X_seed₀ :
    pack E (MvPolynomial.X (0 : Fin 3)) =
      Polynomial.C (MvPolynomial.X (0 : Fin 2)) := by
  change MvPolynomial.finSuccEquiv E 2
    (MvPolynomial.rename (Equiv.swap (0 : Fin 3) 1) (MvPolynomial.X (0 : Fin 3))) = _
  rw [MvPolynomial.rename_X, Equiv.swap_apply_left]
  exact MvPolynomial.finSuccEquiv_X_succ (j := (0 : Fin 2))

private theorem pack_X_value :
    pack E (MvPolynomial.X (1 : Fin 3)) = Polynomial.X := by
  change MvPolynomial.finSuccEquiv E 2
    (MvPolynomial.rename (Equiv.swap (0 : Fin 3) 1) (MvPolynomial.X (1 : Fin 3))) = _
  rw [MvPolynomial.rename_X, Equiv.swap_apply_right, MvPolynomial.finSuccEquiv_X_zero]

private theorem pack_X_seed₁ :
    pack E (MvPolynomial.X (2 : Fin 3)) =
      Polynomial.C (MvPolynomial.X (1 : Fin 2)) := by
  change MvPolynomial.finSuccEquiv E 2
    (MvPolynomial.rename (Equiv.swap (0 : Fin 3) 1) (MvPolynomial.X (2 : Fin 3))) = _
  rw [MvPolynomial.rename_X, show Equiv.swap (0 : Fin 3) 1 2 = 2 by decide]
  exact MvPolynomial.finSuccEquiv_X_succ (j := (1 : Fin 2))

theorem pack_natDegree (F : MvPolynomial (Fin 3) E) :
    (pack E F).natDegree = F.degreeOf (1 : Fin 3) := by
  change (MvPolynomial.finSuccEquiv E 2 (MvPolynomial.rename (Equiv.swap (0 : Fin 3) 1) F)).natDegree = _
  rw [MvPolynomial.natDegree_finSuccEquiv]
  simpa only [Equiv.swap_apply_right] using
    MvPolynomial.degreeOf_rename_of_injective (p := F) (Equiv.swap (0 : Fin 3) 1).injective (1 : Fin 3)

theorem pack_coeff_totalDegree_le (F : MvPolynomial (Fin 3) E) (j : ℕ) :
    ((pack E F).coeff j).totalDegree ≤ F.totalDegree := by
  let G := MvPolynomial.renameEquiv E (Equiv.swap (0 : Fin 3) 1) F
  have hG : G.totalDegree = F.totalDegree := MvPolynomial.totalDegree_renameEquiv _ _
  change ((MvPolynomial.finSuccEquiv E 2 G).coeff j).totalDegree ≤ F.totalDegree
  by_cases h : (MvPolynomial.finSuccEquiv E 2 G).coeff j = 0
  · simp [h]
  · have htotal := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le G j h
    exact (Nat.le_add_right _ _).trans (htotal.trans_eq hG)

theorem pack_derivative (F : MvPolynomial (Fin 3) E) :
    (pack E F).derivative = pack E (MvPolynomial.pderiv (1 : Fin 3) F) := by
  induction F using MvPolynomial.induction_on with
  | C c =>
    simp [pack, MvPolynomial.renameEquiv_apply, MvPolynomial.finSuccEquiv_apply]
  | add F G hF hG =>
    simp [Polynomial.derivative_add, hF, hG]
  | mul_X F i hF =>
    rw [map_mul, Polynomial.derivative_mul, hF, MvPolynomial.pderiv_mul, map_add, map_mul, map_mul]
    fin_cases i <;> simp [pack_X_seed₀, pack_X_value, pack_X_seed₁, MvPolynomial.pderiv_X]

theorem eval_pack (F : MvPolynomial (Fin 3) E) (z₀ value z₁ : E) :
    (pack E F).eval₂ (MvPolynomial.eval (coordinates z₀ z₁)) value =
      MvPolynomial.eval (point z₀ value z₁) F := by
  change (MvPolynomial.finSuccEquiv E 2
    (MvPolynomial.rename (Equiv.swap (0 : Fin 3) 1) F)).eval₂
      (MvPolynomial.eval (coordinates z₀ z₁)) value = _
  rw [Polynomial.eval₂_eq_eval_map, ← MvPolynomial.eval_eq_eval_mv_eval',
    MvPolynomial.eval_rename]
  have hpoint : Fin.cons value (coordinates z₀ z₁) ∘ Equiv.swap (0 : Fin 3) 1 =
      point z₀ value z₁ := by
    funext i
    fin_cases i <;> rfl
  rw [hpoint]

theorem eval_pack_derivative (F : MvPolynomial (Fin 3) E) (z₀ value z₁ : E) :
    (pack E F).derivative.eval₂ (MvPolynomial.eval (coordinates z₀ z₁)) value =
      MvPolynomial.eval (point z₀ value z₁) (MvPolynomial.pderiv (1 : Fin 3) F) := by
  rw [pack_derivative, eval_pack]

theorem pure_seed_card_le {p : ℕ} (F : MvPolynomial (Fin 3) E)
    (hF : F ≠ 0) (hvalueZero : F.degreeOf (1 : Fin 3) = 0) (hchar : F.totalDegree < p)
    (seeds : Finset E) (values : E → E)
    (hroot : ∀ g ∈ seeds, MvPolynomial.eval (point g (values g) (g ^ p)) F = 0) :
    seeds.card ≤ p * F.totalDegree := by
  let G := pack E F
  have hG : G ≠ 0 := fun hz => hF ((pack E).injective (by simpa only [map_zero] using hz))
  have hzero : G.natDegree = 0 := (pack_natDegree F).trans hvalueZero
  have hpacked : G = Polynomial.C (G.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hzero
  have hcoeff : G.coeff 0 ≠ 0 := by
    intro hz
    rw [hpacked, hz, map_zero] at hG
    exact hG rfl
  have hcap : (G.coeff 0).totalDegree ≤ F.totalDegree := pack_coeff_totalDegree_le F 0
  refine (Koala6831CarrierExceptions.seed_card_le_of_total_degree hcoeff
    (hcap.trans_lt hchar) seeds ?_).trans (Nat.mul_le_mul_left p hcap)
  intro g hg
  have he : G.eval₂ (MvPolynomial.eval (coordinates g (g ^ p))) (values g) = 0 :=
    (eval_pack F g (values g) (g ^ p)).trans (hroot g hg)
  conv_lhs at he => rw [hpacked]
  simpa only [Polynomial.eval₂_C] using he

theorem singular_seed_card_le {p : ℕ} [CharP E p] (F : MvPolynomial (Fin 3) E)
    (hirr : Irreducible F) (hvaluePos : 0 < F.degreeOf (1 : Fin 3))
    (hvalueChar : F.degreeOf (1 : Fin 3) < p)
    (hchar : (2 * F.degreeOf (1 : Fin 3) - 1) * F.totalDegree < p)
    (seeds : Finset E) (values : E → E)
    (hroot : ∀ g ∈ seeds, MvPolynomial.eval (point g (values g) (g ^ p)) F = 0)
    (hsing : ∀ g ∈ seeds,
      MvPolynomial.eval (point g (values g) (g ^ p)) (MvPolynomial.pderiv (1 : Fin 3) F) = 0) :
    seeds.card ≤ p * ((2 * F.degreeOf (1 : Fin 3) - 1) * F.totalDegree) := by
  have hpack : Irreducible (pack E F) := (MulEquiv.irreducible_iff (pack E)).mpr hirr
  have hdegree := pack_natDegree F
  apply (Koala6831CarrierExceptions.singular_seed_count (pack E F) hpack
    (hdegree.symm ▸ hvaluePos) (hdegree.symm ▸ hvalueChar)
    F.totalDegree (pack_coeff_totalDegree_le F) (hdegree.symm ▸ hchar) seeds values ?_ ?_).trans
  · rw [hdegree]
  · intro g hg
    rw [eval_pack]
    exact hroot g hg
  · intro g hg
    rw [eval_pack_derivative]
    exact hsing g hg

variable {K : Type*} [Field K]

theorem pure_embedded_seed_card_le {p : ℕ} (φ : K →+* E)
    (F : MvPolynomial (Fin 3) E) (hF : F ≠ 0)
    (hvalueZero : F.degreeOf (1 : Fin 3) = 0) (hchar : F.totalDegree < p)
    (seeds : Finset K) (values : K → E)
    (hroot : ∀ g ∈ seeds, MvPolynomial.eval (point (φ g) (values g) (φ (g ^ p))) F = 0) :
    seeds.card ≤ p * F.totalDegree := by
  rw [← Finset.card_image_of_injective seeds φ.injective]
  refine pure_seed_card_le F hF hvalueZero hchar (seeds.image φ)
    (values ∘ Function.invFun φ) ?_
  intro g hg
  obtain ⟨seed, hseed, rfl⟩ := Finset.mem_image.mp hg
  simpa only [Function.comp_apply, Function.leftInverse_invFun φ.injective seed, ← map_pow]
    using hroot seed hseed

theorem singular_embedded_seed_card_le {p : ℕ} [CharP E p] (φ : K →+* E)
    (F : MvPolynomial (Fin 3) E) (hirr : Irreducible F) (hvaluePos : 0 < F.degreeOf (1 : Fin 3))
    (hvalueChar : F.degreeOf (1 : Fin 3) < p)
    (hchar : (2 * F.degreeOf (1 : Fin 3) - 1) * F.totalDegree < p)
    (seeds : Finset K) (values : K → E)
    (hroot : ∀ g ∈ seeds, MvPolynomial.eval (point (φ g) (values g) (φ (g ^ p))) F = 0)
    (hsing : ∀ g ∈ seeds,
      MvPolynomial.eval (point (φ g) (values g) (φ (g ^ p))) (MvPolynomial.pderiv (1 : Fin 3) F) = 0) :
    seeds.card ≤ p * ((2 * F.degreeOf (1 : Fin 3) - 1) * F.totalDegree) := by
  rw [← Finset.card_image_of_injective seeds φ.injective]
  refine singular_seed_card_le F hirr hvaluePos hvalueChar hchar (seeds.image φ)
    (values ∘ Function.invFun φ) ?_ ?_
  · intro g hg
    obtain ⟨seed, hseed, rfl⟩ := Finset.mem_image.mp hg
    simpa only [Function.comp_apply, Function.leftInverse_invFun φ.injective seed, ← map_pow]
      using hroot seed hseed
  · intro g hg
    obtain ⟨seed, hseed, rfl⟩ := Finset.mem_image.mp hg
    simpa only [Function.comp_apply, Function.leftInverse_invFun φ.injective seed, ← map_pow]
      using hsing seed hseed

end

end ProximityPrize.SubmissionLower.Koala6831OrdinaryFactorExceptions
