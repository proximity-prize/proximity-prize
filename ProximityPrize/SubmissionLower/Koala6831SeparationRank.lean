import ProximityPrize.SubmissionLower.Koala6831SeparationMinors
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace ProximityPrize.SubmissionLower.Koala6831Separation

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F]

abbrev Seeds (R : Type*) [CommSemiring R] := MvPolynomial (Fin 2) R

noncomputable def seedColumns (a b : Seeds F) : Fin 4 → Seeds F := ![a, X 0 * a, b, X 1 * b]

private theorem first_two_independent {a : Seeds F} (ha : a ≠ 0) :
    LinearIndependent F (![a, X 0 * a] : Fin 2 → Seeds F) := by
  refine (LinearIndependent.pair_iff' ha).mpr fun t ht ↦ ?_
  rw [smul_eq_C_mul] at ht
  have he : (C t : Seeds F) = X 0 := mul_right_cancel₀ ha ht
  have hz : t = 0 := by simpa using congrArg (eval (fun _ ↦ 0)) he
  exact (X_ne_zero (R := F) (0 : Fin 2)) (by simpa [hz] using he.symm)

private theorem range_first_two (a : Seeds F) :
    Set.range (![a, X 0 * a] : Fin 2 → Seeds F) = {a, X 0 * a} := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem exists_independent_triple {a b : Seeds F} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ slot : Fin 4, LinearIndependent F (seedColumns a b ∘ slot.succAbove) := by
  have hind := first_two_independent ha
  let W := Submodule.span F (Set.range (![a, X 0 * a] : Fin 2 → Seeds F))
  by_cases hbm : b ∈ W
  · have hb1 : X 1 * b ∉ W := by
      intro hb1
      dsimp only [W] at hbm hb1
      rw [range_first_two] at hbm hb1
      obtain ⟨u, v, h⟩ := Submodule.mem_span_pair.mp hbm
      obtain ⟨s, t, h'⟩ := Submodule.mem_span_pair.mp hb1
      simp only [smul_eq_C_mul] at h h'
      have hL : (C u + C v * X 0) * a = b := by linear_combination h
      have hR : (C s + C t * X 0) * a = X 1 * b := by linear_combination h'
      have he : (X 1 * (C u + C v * X 0) : Seeds F) = C s + C t * X 0 := by
        apply mul_right_cancel₀ ha
        rw [mul_assoc, hL, hR]
      let erase : Seeds F →+* Seeds F :=
        MvPolynomial.eval₂Hom C (fun i ↦ if i = 1 then 0 else X i)
      have hzero : (C s + C t * X 0 : Seeds F) = 0 := by
        have he' := congrArg erase he
        symm
        simpa [erase, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C,
          show (0 : Fin 2) ≠ 1 by decide] using he'
      rw [hzero] at he
      rcases mul_eq_zero.mp he with hx | hh
      · exact (X_ne_zero (R := F) (1 : Fin 2)) hx
      · exact hb (by rw [← hL, hh, zero_mul])
    refine ⟨2, ?_⟩
    have he : seedColumns a b ∘ (2 : Fin 4).succAbove =
        Fin.snoc (![a, X 0 * a] : Fin 2 → Seeds F) (X 1 * b) := by
      funext j
      fin_cases j <;> rfl
    rw [he]
    exact hind.finSnoc hb1
  · refine ⟨3, ?_⟩
    have he : seedColumns a b ∘ (3 : Fin 4).succAbove =
        Fin.snoc (![a, X 0 * a] : Fin 2 → Seeds F) b := by
      funext j
      fin_cases j <;> rfl
    rw [he]
    exact hind.finSnoc hbm

noncomputable def coefficients : Seeds F →ₗ[F] ((Fin 2 →₀ ℕ) → F) :=
  LinearMap.pi fun key ↦ MvPolynomial.lcoeff F key

theorem coefficients_injective : Function.Injective (coefficients (F := F)) := by
  intro f g h
  apply MvPolynomial.ext
  exact fun key ↦ congrFun h key

theorem exists_affine_relation {a b : Seeds F} (v : Fin 4 → F)
    (hv : v ≠ 0) (hs : ∑ j, v j • seedColumns a b j = 0) :
    (v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 ∨ v 3 ≠ 0) ∧
      (C (v 0) + C (v 1) * X 0) * a + (C (v 2) + C (v 3) * X 1) * b = 0 := by
  constructor
  · by_contra! hz
    apply hv
    funext j
    fin_cases j
    · exact hz.1
    · exact hz.2.1
    · exact hz.2.2.1
    · exact hz.2.2.2
  · simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
      seedColumns, Matrix.cons_val_zero, Matrix.cons_val_succ, smul_eq_C_mul] at hs
    change C (v 0) * a + (C (v 1) * (X 0 * a) +
      (C (v 2) * b + C (v 3) * (X 1 * b))) = 0 at hs
    linear_combination hs

end ProximityPrize.SubmissionLower.Koala6831Separation
