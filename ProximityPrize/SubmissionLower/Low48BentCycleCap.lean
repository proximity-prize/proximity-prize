import ProximityPrize.SubmissionLower.Low48BentCycle
import ProximityPrize.SubmissionLower.Low48BentSupport
import ProximityPrize.SubmissionLower.Low48Price

set_option autoImplicit false
set_option Elab.async false

namespace Low48BentCycle

noncomputable section

open Low48BentLattice
open K1_13 (Shape InBox Row shape)
open K1_13_6 (GeoField toGeneric)
open K1_13_6_2 (GeoJets5)
open Low48Price (primaryBox taylorLength)
open Low48BentSupport (graph lifted)
open K1_13_6_2_4 (Exponent oldEmbedding old_section_box box5_iff)
open K1_13_6_2_4_1 (Grade unitGrade positiveDiagonal)
open MvPolynomial
open scoped Pointwise

def rawFamily (caps : Fin 5 → Cap) : Family := fun i => {m | Allowed (caps i) m}

def capFamily (caps : Fin 5 → Cap) : Family := fun i => latticePoints (caps i)

instance (caps : Fin 5 → Cap) (i : Fin 5) : Finite (capFamily caps i) :=
  inferInstanceAs (Finite (latticePoints (caps i)))


open private generator_mem_diagonal from ProximityPrize.SubmissionLower.Low48BentCycle

private theorem diagonal_unit (B : Family) (h0 : ∀ i, 0 ∈ B i) (i : Fin 5) :
    diagonalExponents B (unitGrade i) = B i := by
  ext m
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hi : unitGrade i i = 1 := by simp [unitGrade]
    let j : Fin (unitGrade i i) := ⟨0, by omega⟩
    rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
    · exact hu i j
    · intro k _ hk
      exfalso
      apply hk
      exact Fin.ext (by omega : k.val = j.val)
    · simp
    · intro k _ hk
      have hkill : unitGrade i k = 0 := by simp [unitGrade, hk]
      have : IsEmpty (Fin (unitGrade i k)) := by rw [hkill]; infer_instance
      simp
    · simp
  · intro hm
    exact generator_mem_diagonal h0 (⟨i, ⟨m, hm⟩⟩ : Generator B)

private theorem grade_sum (t : Grade) : (∑ i : Fin 5, t i • unitGrade i) = t := by
  ext i
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · simp [unitGrade]
  · intro j _ hj
    simp [unitGrade, Ne.symm hj]
  · simp

private theorem diagonal_sum (B : Family) (s : Finset (Fin 5)) (t : Fin 5 → Grade) :
    diagonalExponents B (∑ i ∈ s, t i) = ∑ i ∈ s, diagonalExponents B (t i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (diagonal_nsmul B 0 0).trans (zero_smul _ _)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, diagonal_add, ih]

def capSum (caps : Fin 5 → Cap) (t : Grade) : Cap :=
  Sum Finset.univ (fun i => Scale (t i) (caps i))

theorem chamber_capSum (caps : Fin 5 → Cap) (h : ∀ i, Chamber (caps i)) (t : Grade) :
    Chamber (capSum caps t) :=
  chamber_sum _ _ (fun i _ => chamber_scale (h i) (t i))

theorem diagonal_cap (caps : Fin 5 → Cap) (h : ∀ i, Chamber (caps i)) (t : Grade) :
    diagonalExponents (capFamily caps) t = latticePoints (capSum caps t) := by
  have h0 (i : Fin 5) : 0 ∈ capFamily caps i := zero_mem (caps i)
  calc
    diagonalExponents (capFamily caps) t =
        ∑ i : Fin 5, diagonalExponents (capFamily caps) (t i • unitGrade i) := by
      conv_lhs => rw [← grade_sum t]
      exact diagonal_sum _ _ _
    _ = ∑ i : Fin 5, latticePoints (Scale (t i) (caps i)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [diagonal_nsmul, diagonal_unit _ h0]
      exact lattice_scale _ (h i) _
    _ = _ := lattice_sum _ _ (fun i _ => chamber_scale (h i) (t i))

private theorem coeff_congr (S T : Set Exponent) [Finite S] [Finite T] (h : S = T) :
    (affineHilbertPolynomial (Ideal.comap (monomialMap GeoField S) ⊥)).coeff 5 =
      (affineHilbertPolynomial (Ideal.comap (monomialMap GeoField T) ⊥)).coeff 5 := by
  subst T
  rfl

theorem ambient_cap (caps : Fin 5 → Cap) (h : ∀ i, Chamber (caps i)) (v : Cap → ℚ)
    (hv : ∀ a, Chamber a →
      (affineHilbertPolynomial (Ideal.comap (monomialMap GeoField (latticePoints a)) ⊥)).coeff 5 =
        v a) :
    32 * mixedDegree (capFamily caps) ⊥ Finset.univ =
      ∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        v (capSum caps (positiveDiagonal J)) := by
  unfold mixedDegree
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [show (2 : ℚ) ^ 5 = 32 by norm_num, ← mul_div_assoc, mul_div_cancel_left₀ _ (by norm_num)]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [coeff_congr _ _ (diagonal_cap caps h _), hv _ (chamber_capSum caps h _)]




theorem old_section {q : Shape} {F : Row 4} (h : InBox (shape F) q) :
    Low48BentSupport.Box (q, 0) (oldEmbedding (toGeneric F)) := by
  intro m hm
  have hb := (box5_iff (a := (q, 0))).mp (old_section_box h) m hm
  simp only [K1_13_6_2_4.Allowed, Fin.sum_univ_four] at hb
  have h0 : m 4 = 0 := Nat.eq_zero_of_le_zero hb.2.2.2
  change m 0 + m 1 + m 2 + m 3 ≤ q.b ∧
    0 * m 0 + 1 * m 1 + 2 * m 2 + 3 * m 3 ≤ q.j ∧ m 3 ≤ q.t ∧ m 4 ≤ 0 at hb
  simpa [Allowed, h0] using hb

end

end Low48BentCycle
