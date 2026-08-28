import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ActualCurveZeroCount

/-!
# Characteristic-free zero counts by an inseparability dichotomy

Research module, deliberately kept off the green submission chain.

For a finite extension in positive characteristic, failure of separability
forces the inseparable degree, hence the total degree, to be at least the
characteristic.  Consequently a point set of cardinality at most the
characteristic is already paid for by any positive coordinate cap on a
nonseparable projection.  If no projection is nonseparable, the existing
separable curve zero-count theorem applies unchanged.
-/

namespace ProximityPrize.SubmissionLower.CharacteristicFreeInseparableDichotomyResearch

open scoped Classical BigOperators
open Field ActualCurveCoordinateField ActualCurveRationalProjection ActualCurveZeroCount

noncomputable section

/-- A finite nonseparable field extension in characteristic `p > 0` has
degree at least `p`. -/
theorem char_le_finrank_of_not_isSeparable
    (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (p : ℕ) [CharP F p] (hp : p ≠ 0)
    (hsep : ¬ Algebra.IsSeparable F E) :
    p ≤ Module.finrank F E := by
  letI : Fact p.Prime := ⟨CharP.char_prime_of_ne_zero F hp⟩
  obtain ⟨n, hn⟩ := finInsepDegree_eq_pow (F := F) (E := E) p
  have hinsep_ne_one : finInsepDegree F E ≠ 1 := by
    intro h
    apply hsep
    rw [← separableClosure.eq_top_iff,
      ← IntermediateField.finrank_eq_one_iff_eq_top]
    exact h
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    subst n
    exact hinsep_ne_one (by simpa using hn)
  have hp_le_insep : p ≤ finInsepDegree F E := by
    rw [hn]
    simpa only [pow_one] using
      Nat.pow_le_pow_right (CharP.char_prime_of_ne_zero F hp).pos
        (Nat.one_le_iff_ne_zero.mpr hn_ne_zero)
  have hinsep_le_finrank : finInsepDegree F E ≤ Module.finrank F E := by
    rw [← Field.finSepDegree_mul_finInsepDegree]
    exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne _))
  exact hp_le_insep.trans hinsep_le_finrank

/-- A nonseparable finite extension of prime total degree is not merely
partly inseparable: its separable degree is one, hence it is purely
inseparable.  This is the structural conclusion available in the exceptional
`degree = p` block of the refined projection ledger. -/
theorem isPurelyInseparable_of_finrank_eq_prime_of_not_isSeparable
    (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (p : ℕ) (hp : p.Prime)
    (hdegree : Module.finrank F E = p)
    (hsep : ¬ Algebra.IsSeparable F E) :
    IsPurelyInseparable F E := by
  have hinsep_ne_one : Field.finInsepDegree F E ≠ 1 := by
    intro hinsep
    exact hsep ((isSeparable_iff_finInsepDegree_eq_one F E).mpr hinsep)
  have hproduct : Field.finSepDegree F E * Field.finInsepDegree F E = p := by
    rw [Field.finSepDegree_mul_finInsepDegree, hdegree]
  have hinsep_dvd : Field.finInsepDegree F E ∣ p :=
    ⟨Field.finSepDegree F E, by simpa only [Nat.mul_comm] using hproduct.symm⟩
  have hinsep_eq : Field.finInsepDegree F E = p :=
    (hp.eq_one_or_self_of_dvd _ hinsep_dvd).resolve_left hinsep_ne_one
  have hsepDegree : Field.finSepDegree F E = 1 := by
    apply Nat.mul_right_cancel hp.pos
    simpa only [hinsep_eq, one_mul] using hproduct
  exact isPurelyInseparable_of_finSepDegree_eq_one hsepDegree

variable (K : Type) [Field K]
variable (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]

/-- The genuinely characteristic-free part of the projection hypothesis. -/
def ProjectionsFinite : Prop :=
  ∀ (i : Fin 3) (hi : Transcendental K (coordinate K P i)),
    letI : Algebra (RatFunc K) (CoordinateField K P) := rationalBaseAlgebra K P i hi
    FiniteDimensional (RatFunc K) (CoordinateField K P)

theorem projectionsFinite_of_finiteSeparable
    (hproj : ProjectionsFiniteSeparable K P) : ProjectionsFinite K P :=
  fun i hi ↦ (hproj i hi).1

variable [IsAlgClosed K]

/-- If one finite coordinate projection is nonseparable, its actual
coordinate degree is at least the positive characteristic. -/
theorem char_le_actualCoordinateDegree_of_not_isSeparable
    (hfinite : ProjectionsFinite K P) (p : ℕ) [CharP K p] (hp : p ≠ 0)
    (i : Fin 3) (hi : Transcendental K (coordinate K P i))
    (hsep :
      letI : Algebra (RatFunc K) (CoordinateField K P) := rationalBaseAlgebra K P i hi
      ¬ Algebra.IsSeparable (RatFunc K) (CoordinateField K P)) :
    p ≤ actualCoordinateDegree K P i := by
  letI : Algebra (RatFunc K) (CoordinateField K P) := rationalBaseAlgebra K P i hi
  letI : FiniteDimensional (RatFunc K) (CoordinateField K P) := hfinite i hi
  rw [actualCoordinateDegree_of_transcendental K P i hi]
  apply char_le_finrank_of_not_isSeparable (RatFunc K) (CoordinateField K P) p
  · exact hp
  · exact hsep

/-- If the full degree of one finite projection is strictly below the
characteristic, that projection is automatically separable.  This is the
contrapositive form used by the global-shear construction. -/
theorem isSeparable_of_actualCoordinateDegree_lt_char
    (hfinite : ProjectionsFinite K P) (p : ℕ) [CharP K p] (hp : p ≠ 0)
    (i : Fin 3) (hi : Transcendental K (coordinate K P i))
    (hdegree : actualCoordinateDegree K P i < p) :
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      rationalBaseAlgebra K P i hi
    Algebra.IsSeparable (RatFunc K) (CoordinateField K P) := by
  letI : Algebra (RatFunc K) (CoordinateField K P) :=
    rationalBaseAlgebra K P i hi
  by_contra hsep
  exact (Nat.not_lt_of_ge
    (char_le_actualCoordinateDegree_of_not_isSeparable
      K P hfinite p hp i hi hsep)) hdegree

/-- A strict *family* degree budget certifies separability on every
transcendental member of that family.  No componentwise resultant gate is
needed: each nonnegative summand is bounded by the common sum. -/
theorem family_coordinate_isSeparable_of_sum_degree_lt_char
    {I : Type} [Fintype I]
    (Q : I → Ideal (MvPolynomial (Fin 3) K)) [∀ i, (Q i).IsPrime]
    (hfinite : ∀ i, ProjectionsFinite K (Q i))
    (p : ℕ) [CharP K p] (hp : p ≠ 0) (j : Fin 3)
    (hsum : (∑ i, actualCoordinateDegree K (Q i) j) < p)
    (i : I) (hi : Transcendental K (coordinate K (Q i) j)) :
    letI : Algebra (RatFunc K) (CoordinateField K (Q i)) :=
      rationalBaseAlgebra K (Q i) j hi
    Algebra.IsSeparable (RatFunc K) (CoordinateField K (Q i)) := by
  apply isSeparable_of_actualCoordinateDegree_lt_char
    K (Q i) (hfinite i) p hp j hi
  exact (Finset.single_le_sum
    (s := Finset.univ)
    (f := fun k : I ↦ actualCoordinateDegree K (Q k) j)
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans_lt hsum

/-- Characteristic-free replacement for `finite_zero_points_le_box` under
the extra hypotheses that the finite point set has at most `p` elements
and every coordinate cap is positive.

The properness and vanishing hypotheses are used only in the all-separable
branch.  In the nonseparable branch, one positive summand of the box cost
is already at least `p`. -/
theorem finite_zero_points_le_box_of_finite_or_inseparable
    (hfinite : ProjectionsFinite K P)
    (p : ℕ) [CharP K p] (hp : p ≠ 0)
    (hnonpoint : ∀ v : Fin 3 → K,
      P ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (F : MvPolynomial (Fin 3) K) (hF : F ∉ P)
    (cap : Fin 3 → ℕ) (hcap : ∀ i, F.degreeOf i ≤ cap i)
    (hcap_pos : ∀ i, 1 ≤ cap i)
    (S : Finset (Fin 3 → K)) (hS_card : S.card ≤ p)
    (hSP : ∀ v ∈ S, P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hSF : ∀ v ∈ S, MvPolynomial.aeval v F = 0) :
    S.card ≤ ∑ i, cap i * actualCoordinateDegree K P i := by
  classical
  by_cases hsep : ∀ (i : Fin 3) (hi : Transcendental K (coordinate K P i)),
      letI : Algebra (RatFunc K) (CoordinateField K P) := rationalBaseAlgebra K P i hi
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P)
  · have hproj : ProjectionsFiniteSeparable K P := fun i hi ↦ ⟨hfinite i hi, hsep i hi⟩
    have hcount := finite_zero_points_le_box K P hproj hnonpoint F hF cap hcap S hSP hSF
    exact_mod_cast hcount
  · push_neg at hsep
    obtain ⟨i, hi, hnotsep⟩ := hsep
    have hp_degree : p ≤ actualCoordinateDegree K P i :=
      char_le_actualCoordinateDegree_of_not_isSeparable K P hfinite p hp i hi hnotsep
    have hdegree_term : actualCoordinateDegree K P i ≤
        cap i * actualCoordinateDegree K P i :=
      Nat.le_mul_of_pos_left _ (hcap_pos i)
    have hterm_sum : cap i * actualCoordinateDegree K P i ≤
        ∑ j, cap j * actualCoordinateDegree K P j :=
      Finset.single_le_sum
        (s := Finset.univ)
        (f := fun j : Fin 3 ↦ cap j * actualCoordinateDegree K P j)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    exact hS_card.trans (hp_degree.trans (hdegree_term.trans hterm_sum))

end

end ProximityPrize.SubmissionLower.CharacteristicFreeInseparableDichotomyResearch
