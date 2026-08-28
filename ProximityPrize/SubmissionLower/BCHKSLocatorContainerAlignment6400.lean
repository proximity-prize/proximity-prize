import ProximityPrize.SubmissionLower.BCHKSFrobeniusTwoRelations6400
import ProximityPrize.SubmissionLower.BCHKSBridge

/-!
# Fixed error containers force affine Reed--Solomon alignment

This file isolates the geometric finish of the locator-pencil rank-two branch.
Suppose every selected polynomial agrees with the received affine word away
from one fixed coordinate container and a small slope-dependent residual set.
Two anchor slopes then determine an affine polynomial pencil.  Outside the
fixed container and the three residual sets belonging to the anchors and a
third slope, the candidate polynomial and that pencil have the same values.
If that leaves at least `k` coordinates, Reed--Solomon uniqueness makes the
identity global.

The endpoint arithmetic records the useful feature of this argument: an
obstruction of `X`-degree `76772` only needs `49622` roots common to all
slopes.  It does not need an almost-full common error core.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false

variable {F D : Type} [Field F] [DecidableEq F]
variable [Fintype D] [DecidableEq D]

/-- If every candidate polynomial agrees with an affine received word away
from a fixed container `C` and a residual set of size at most `r`, then two
distinct anchor slopes determine the whole polynomial family, provided three
residual sets and the fixed container leave at least `k` coordinates.

This statement deliberately does not assume that `C` consists of errors.
It is merely the set on which the determinant obstruction gives no
information; this is the direction supplied by the locator incidence count.
-/
theorem affine_polynomial_family_of_fixed_error_container
    (α : D ↪ F) (T : Finset F) (P : F → F[X])
    (U₀ U₁ : D → F) (C : Finset D) (R : F → Finset D)
    (k r : ℕ) (z₀ z₁ : F)
    (hz₀ : z₀ ∈ T) (hz₁ : z₁ ∈ T) (hzne : z₀ ≠ z₁)
    (hPdegree : ∀ z ∈ T, (P z).natDegree < k)
    (hRcard : ∀ z ∈ T, (R z).card ≤ r)
    (hagree : ∀ z ∈ T, ∀ i, i ∉ C → i ∉ R z →
      (P z).eval (α i) = U₀ i + z * U₁ i)
    (hroom : k + C.card + 3 * r ≤ Fintype.card D) :
    ∃ p₀ p₁ : F[X], p₀.natDegree < k ∧ p₁.natDegree < k ∧
      ∀ z ∈ T, P z = p₀ + Polynomial.C z * p₁ := by
  classical
  let p₁ : F[X] :=
    Polynomial.C ((z₁ - z₀)⁻¹) * (P z₁ - P z₀)
  let p₀ : F[X] := P z₀ - Polynomial.C z₀ * p₁
  have hscalar : (z₁ - z₀)⁻¹ * (z₁ - z₀) = 1 := by
    rw [inv_mul_cancel₀]
    exact sub_ne_zero.mpr hzne.symm
  have hp₁degree : p₁.natDegree < k := by
    exact (Polynomial.natDegree_C_mul_le _ _).trans_lt
      ((Polynomial.natDegree_sub_le _ _).trans_lt
        (max_lt (hPdegree z₁ hz₁) (hPdegree z₀ hz₀)))
  have hp₀degree : p₀.natDegree < k := by
    exact (Polynomial.natDegree_sub_le _ _).trans_lt
      (max_lt (hPdegree z₀ hz₀)
        ((Polynomial.natDegree_C_mul_le _ _).trans_lt hp₁degree))
  refine ⟨p₀, p₁, hp₀degree, hp₁degree, ?_⟩
  intro z hz
  let Bad : Finset D := C ∪ R z₀ ∪ R z₁ ∪ R z
  let Good : Finset D := Finset.univ \ Bad
  have hBadCard : Bad.card ≤ C.card + 3 * r := by
    have h₀ : (C ∪ R z₀).card ≤ C.card + (R z₀).card :=
      Finset.card_union_le _ _
    have h₁ : (C ∪ R z₀ ∪ R z₁).card ≤
        (C ∪ R z₀).card + (R z₁).card := Finset.card_union_le _ _
    have h₂ : (C ∪ R z₀ ∪ R z₁ ∪ R z).card ≤
        (C ∪ R z₀ ∪ R z₁).card + (R z).card :=
      Finset.card_union_le _ _
    dsimp only [Bad]
    calc
      (C ∪ R z₀ ∪ R z₁ ∪ R z).card
          ≤ C.card + (R z₀).card + (R z₁).card + (R z).card := by
            omega
      _ ≤ C.card + r + r + r := by
            gcongr
            · exact hRcard z₀ hz₀
            · exact hRcard z₁ hz₁
            · exact hRcard z hz
      _ = C.card + 3 * r := by ring
  have hGoodCard : k ≤ Good.card := by
    have hGoodEq : Good.card = Fintype.card D - Bad.card := by
      dsimp only [Good]
      rw [Finset.card_sdiff]
      simp
    rw [hGoodEq]
    omega
  have hGoodAvoid (i : D) (hi : i ∈ Good) :
      i ∉ C ∧ i ∉ R z₀ ∧ i ∉ R z₁ ∧ i ∉ R z := by
    have hiBad : i ∉ Bad := (Finset.mem_sdiff.mp hi).2
    simp only [Bad, Finset.mem_union, not_or] at hiBad
    exact ⟨hiBad.1.1.1, hiBad.1.1.2, hiBad.1.2, hiBad.2⟩
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    (P z) (p₀ + Polynomial.C z * p₁)
    (f := fun i : {i // i ∈ Good} => α i.1)
  · intro i j hij
    exact Subtype.ext (α.injective hij)
  · intro i
    obtain ⟨hiC, hiR₀, hiR₁, hiR⟩ := hGoodAvoid i.1 i.2
    have heval₀ := hagree z₀ hz₀ i.1 hiC hiR₀
    have heval₁ := hagree z₁ hz₁ i.1 hiC hiR₁
    have heval := hagree z hz i.1 hiC hiR
    have hp₁eval : p₁.eval (α i.1) = U₁ i.1 := by
      simp only [p₁, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_sub]
      rw [heval₁, heval₀]
      calc
        (z₁ - z₀)⁻¹ *
            ((U₀ i.1 + z₁ * U₁ i.1) - (U₀ i.1 + z₀ * U₁ i.1)) =
            ((z₁ - z₀)⁻¹ * (z₁ - z₀)) * U₁ i.1 := by ring
        _ = U₁ i.1 := by rw [hscalar, one_mul]
    have hp₀eval : p₀.eval (α i.1) = U₀ i.1 := by
      simp only [p₀, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_C]
      rw [heval₀, hp₁eval]
      ring
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    rw [heval, hp₀eval, hp₁eval]
  · have hright : (p₀ + Polynomial.C z * p₁).natDegree < k :=
      (Polynomial.natDegree_add_le _ _).trans_lt
        (max_lt hp₀degree
          ((Polynomial.natDegree_C_mul_le _ _).trans_lt hp₁degree))
    simpa only [Fintype.card_coe] using
      (max_lt (hPdegree z hz) hright).trans_le hGoodCard

/-- The fixed-container alignment lemma followed by the elementary affine-line
incidence finish.  The conclusion exhibits one chosen agreement set on which
the two received rows themselves agree with the two anchor-derived
polynomials.  In the Reed--Solomon application their evaluation words are
codewords, so this is exactly the contradiction to column-farness (and to the
non-explained clause of an `MCABad` witness). -/
theorem exists_common_pair_agreement_of_fixed_error_container
    (α : D ↪ F) (T : Finset F) (A : F → Finset D) (P : F → F[X])
    (U₀ U₁ : D → F) (C : Finset D) (R : F → Finset D)
    (k r e : ℕ) (z₀ z₁ : F)
    (hz₀ : z₀ ∈ T) (hz₁ : z₁ ∈ T) (hzne : z₀ ≠ z₁)
    (hTcard : e + 1 < T.card)
    (hAcard : ∀ z ∈ T, Fintype.card D - e ≤ (A z).card)
    (hPdegree : ∀ z ∈ T, (P z).natDegree < k)
    (hPagree : ∀ z ∈ T, ∀ i ∈ A z,
      (P z).eval (α i) = U₀ i + z * U₁ i)
    (hRcard : ∀ z ∈ T, (R z).card ≤ r)
    (houtside : ∀ z ∈ T, ∀ i, i ∉ C → i ∉ R z →
      (P z).eval (α i) = U₀ i + z * U₁ i)
    (hroom : k + C.card + 3 * r ≤ Fintype.card D) :
    ∃ p₀ p₁ : F[X], p₀.natDegree < k ∧ p₁.natDegree < k ∧
      ∃ z ∈ T, ∀ i ∈ A z,
        U₀ i = p₀.eval (α i) ∧ U₁ i = p₁.eval (α i) := by
  classical
  obtain ⟨p₀, p₁, hp₀, hp₁, hfamily⟩ :=
    affine_polynomial_family_of_fixed_error_container
      α T P U₀ U₁ C R k r z₀ z₁ hz₀ hz₁ hzne
      hPdegree hRcard houtside hroom
  let U : Fin 2 → D → F := ![U₀, U₁]
  let q : Fin 2 → D → F :=
    ![fun i => p₀.eval (α i), fun i => p₁.eval (α i)]
  have hline : ∀ z ∈ T, ∀ i ∈ A z,
      U 0 i + z * U 1 i = q 0 i + z * q 1 i := by
    intro z hz i hi
    change U₀ i + z * U₁ i =
      p₀.eval (α i) + z * p₁.eval (α i)
    calc
      U₀ i + z * U₁ i = (P z).eval (α i) :=
        (hPagree z hz i hi).symm
      _ = (p₀ + Polynomial.C z * p₁).eval (α i) := by
        rw [hfamily z hz]
      _ = p₀.eval (α i) + z * p₁.eval (α i) := by simp
  obtain ⟨z, hz, hcommon⟩ :=
    exists_common_affine_set U q T A e hTcard hAcard hline
  refine ⟨p₀, p₁, hp₀, hp₁, z, hz, ?_⟩
  intro i hi
  simpa only [U, q, Matrix.cons_val_zero, Matrix.cons_val_one] using
    hcommon i hi

/-- Exact score-64 room calculation for a determinant obstruction of
`X`-degree at most `76772`.  Once at least `49622` roots are common to all
specializations, three residual root sets still leave `k = 131072`
evaluation coordinates. -/
theorem score6400_fixed_container_room
    (c : ℕ) (hlower : 49622 ≤ c) (hupper : c ≤ 76772) :
    131072 + c + 3 * (76772 - c) ≤ 262144 := by
  omega

end ProximityPrize.SubmissionLower
