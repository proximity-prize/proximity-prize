import ProximityPrize.SubmissionLower.BCHKSSyndromeInterpolationDegree6400

/-!
# Lagrange interpolation with polynomial-valued samples

The ordinary `Lagrange.interpolate` interface is field-valued.  Production
locator families instead have values in the challenge polynomial ring.  The
same fixed base-field Lagrange basis works over every base-field algebra; this
file records its evaluation, locator-degree, coefficient-degree, and syndrome
prefix properties.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 600000

/-- Interpolate algebra-valued samples using a Lagrange basis constructed over
the base field. -/
noncomputable def algebraLagrangeInterpolate
    {F A ι : Type} [Field F] [CommRing A] [Algebra F A]
    [DecidableEq ι]
    (s : Finset ι) (v : ι → F) (e : ι → A) : A[X] :=
  ∑ i ∈ s,
    Polynomial.C (e i) *
      (Lagrange.basis s v i).map (algebraMap F A)

@[simp]
theorem algebraLagrangeInterpolate_eval_at_node
    {F A ι : Type} [Field F] [CommRing A] [Algebra F A]
    [DecidableEq ι]
    (s : Finset ι) (v : ι → F) (e : ι → A)
    (hv : Set.InjOn v s) {i : ι} (hi : i ∈ s) :
    (algebraLagrangeInterpolate s v e).eval
        (algebraMap F A (v i)) = e i := by
  classical
  rw [algebraLagrangeInterpolate, Polynomial.eval_finsetSum,
    ← Finset.add_sum_erase _ _ hi]
  simp only [Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_map_apply, Lagrange.eval_basis_self hv hi,
    map_one, mul_one, add_eq_left]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Lagrange.eval_basis_of_ne (Finset.mem_erase.mp hj).1 hi,
    map_zero, mul_zero]

theorem algebraLagrangeInterpolate_natDegree_lt_card
    {F A ι : Type} [Field F] [CommRing A] [Algebra F A]
    [DecidableEq ι]
    (s : Finset ι) (v : ι → F) (e : ι → A)
    (hv : Set.InjOn v s) (hs : s.Nonempty) :
    (algebraLagrangeInterpolate s v e).natDegree < s.card := by
  classical
  rw [algebraLagrangeInterpolate]
  have hsum :
      (∑ i ∈ s, Polynomial.C (e i) *
        (Lagrange.basis s v i).map (algebraMap F A)).natDegree ≤
          s.card - 1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    apply (Polynomial.natDegree_C_mul_le _ _).trans
    apply Polynomial.natDegree_map_le.trans
    exact (Lagrange.natDegree_basis hv hi).le
  exact hsum.trans_lt
    (Nat.sub_lt (Finset.Nonempty.card_pos hs) Nat.one_pos)

/-- Evaluating polynomial-valued samples commutes with interpolation. -/
theorem algebraLagrangeInterpolate_map_eval
    {F ι : Type} [Field F] [DecidableEq ι]
    (s : Finset ι) (v : ι → F) (e : ι → F[X]) (z : F)
    (hv : Set.InjOn v s) (hs : s.Nonempty) :
    (algebraLagrangeInterpolate s v e).map
        (Polynomial.evalRingHom z) =
      Lagrange.interpolate s v (fun i => (e i).eval z) := by
  classical
  let Q := algebraLagrangeInterpolate s v e
  have hQnat : Q.natDegree < s.card := by
    simpa only [Q] using
      algebraLagrangeInterpolate_natDegree_lt_card s v e hv hs
  have hmapNat : (Q.map (Polynomial.evalRingHom z)).natDegree < s.card :=
    Polynomial.natDegree_map_le.trans_lt hQnat
  have hmapDegree : (Q.map (Polynomial.evalRingHom z)).degree <
      (s.card : WithBot ℕ) := by
    by_cases hzero : Q.map (Polynomial.evalRingHom z) = 0
    · simp [hzero]
    · rw [Polynomial.degree_eq_natDegree hzero]
      exact WithBot.coe_lt_coe.mpr hmapNat
  apply Lagrange.eq_interpolate_of_eval_eq
    (fun i => (e i).eval z) hv hmapDegree
  intro i hi
  have hmap := Polynomial.eval_map_apply
    (p := Q) (f := Polynomial.evalRingHom z) (Polynomial.C (v i))
  calc
    (Q.map (Polynomial.evalRingHom z)).eval (v i) =
        (Q.eval (Polynomial.C (v i))).eval z := by
      simpa only [Polynomial.coe_evalRingHom, Polynomial.eval_C] using hmap
    _ = (e i).eval z := by
      rw [show Q.eval (Polynomial.C (v i)) = e i by
        simpa only [Q, Polynomial.C_eq_algebraMap] using
          algebraLagrangeInterpolate_eval_at_node s v e hv hi]

/-- A challenge-degree bound on every sample transfers coefficientwise to
the algebra-valued interpolant. -/
theorem algebraLagrangeInterpolate_coeff_natDegree_le
    {F ι : Type} [Field F] [DecidableEq ι]
    (s : Finset ι) (v : ι → F) (e : ι → F[X]) (S n : ℕ)
    (he : ∀ i ∈ s, (e i).natDegree ≤ S) :
    ((algebraLagrangeInterpolate s v e).coeff n).natDegree ≤ S := by
  classical
  rw [algebraLagrangeInterpolate, Polynomial.finsetSum_coeff]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_map]
  exact (Polynomial.natDegree_mul_C_le _ _).trans (he i hi)

/-- Evaluating the outer variable at a base-field constant does not increase
the challenge degree of bivariate coefficients. -/
theorem eval_C_natDegree_le_of_coeff_natDegree_le
    {F : Type} [Field F] (P : F[X][X]) (S : ℕ)
    (hP : ∀ n, (P.coeff n).natDegree ≤ S) (x : F) :
    (P.eval (Polynomial.C x)).natDegree ≤ S := by
  classical
  rw [Polynomial.eval_eq_sum_range]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro n hn
  calc
    ((P.coeff n) * Polynomial.C x ^ n).natDegree ≤
        (P.coeff n).natDegree + (Polynomial.C x ^ n).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ S + 0 := Nat.add_le_add (hP n) (by simp)
    _ = S := Nat.add_zero S

/-- The barycentric syndrome moment of polynomial-valued samples, with every
base-field weight embedded as a constant challenge polynomial. -/
noncomputable def polynomialSyndromeMoment
    {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (α : ι ↪ F) (e : ι → F[X]) (t : ℕ) : F[X] :=
  ∑ i : ι,
    Polynomial.C
        (α i ^ t / rsBarycentricDenominator α i) * e i

@[simp]
theorem polynomialSyndromeMoment_eval
    {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (α : ι ↪ F) (e : ι → F[X]) (t : ℕ) (z : F) :
    (polynomialSyndromeMoment α e t).eval z =
      rsSyndromeMoment α (fun i => (e i).eval z) t := by
  classical
  rw [polynomialSyndromeMoment, Polynomial.eval_finsetSum,
    rsSyndromeMoment]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  ring

theorem polynomialSyndromeMoment_natDegree_le
    {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (α : ι ↪ F) (e : ι → F[X]) (t S : ℕ)
    (he : ∀ i, (e i).natDegree ≤ S) :
    (polynomialSyndromeMoment α e t).natDegree ≤ S := by
  classical
  rw [polynomialSyndromeMoment]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (Polynomial.natDegree_C_mul_le _ _).trans (he i)

/-- A zero prefix of polynomial-valued syndrome moments removes the same top
locator coefficients as in ordinary field-valued interpolation.  The proof
embeds the challenge polynomial ring into its fraction field and invokes the
checked field-valued theorem there. -/
theorem algebraLagrangeInterpolate_natDegree_lt_card_sub_of_zero_prefix
    {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι]
    (α : ι ↪ F) (e : ι → F[X]) (rows : ℕ)
    (hrows : rows < Fintype.card ι)
    (hmoment : ∀ t, t < rows → polynomialSyndromeMoment α e t = 0) :
    (algebraLagrangeInterpolate Finset.univ
      (fun i : ι => α i) e).natDegree < Fintype.card ι - rows := by
  classical
  let A := F[X]
  let K := FractionRing A
  let ιK : A →+* K := algebraMap A K
  let φ : F →+* K := ιK.comp Polynomial.C
  let αK : ι ↪ K :=
    { toFun := fun i => φ (α i)
      inj' := by
        intro i j hij
        apply α.injective
        apply Polynomial.C_injective
        exact (IsFractionRing.injective A K) hij }
  let eK : ι → K := fun i => ιK (e i)
  let Q : A[X] := algebraLagrangeInterpolate Finset.univ
    (fun i : ι => α i) e
  have hιK : Function.Injective ιK := IsFractionRing.injective A K
  have hcardPos : 0 < Fintype.card ι := by omega
  letI : Nonempty ι := Fintype.card_pos_iff.mp hcardPos
  have hQnat : Q.natDegree < Fintype.card ι := by
    simpa only [Q, Finset.card_univ] using
      algebraLagrangeInterpolate_natDegree_lt_card
        Finset.univ (fun i : ι => α i) e α.injective.injOn
        Finset.univ_nonempty
  have hQmapNat : (Q.map ιK).natDegree < Fintype.card ι :=
    Polynomial.natDegree_map_le.trans_lt hQnat
  have hQmapDegree : (Q.map ιK).degree <
      (Fintype.card ι : WithBot ℕ) := by
    by_cases hzero : Q.map ιK = 0
    · simp [hzero]
    · rw [Polynomial.degree_eq_natDegree hzero]
      exact WithBot.coe_lt_coe.mpr hQmapNat
  have hQmapEval : ∀ i : ι,
      (Q.map ιK).eval (αK i) = eK i := by
    intro i
    change (Q.map ιK).eval (ιK (Polynomial.C (α i))) = ιK (e i)
    rw [Polynomial.eval_map_apply]
    rw [show Q.eval (Polynomial.C (α i)) = e i by
      simpa only [Q, Polynomial.C_eq_algebraMap] using
        algebraLagrangeInterpolate_eval_at_node
          Finset.univ (fun j : ι => α j) e α.injective.injOn
          (Finset.mem_univ i)]
  have hQmapEq : Q.map ιK =
      Lagrange.interpolate Finset.univ (fun i : ι => αK i) eK := by
    apply Lagrange.eq_interpolate_of_eval_eq eK
      (s := Finset.univ) (v := fun i : ι => αK i)
      αK.injective.injOn hQmapDegree
    intro i hi
    exact hQmapEval i
  have hdenominator : ∀ i : ι,
      rsBarycentricDenominator αK i =
        φ (rsBarycentricDenominator α i) := by
    intro i
    rw [rsBarycentricDenominator, rsBarycentricDenominator, map_prod]
    apply Finset.prod_congr rfl
    intro j hj
    change φ (α i) - φ (α j) = φ (α i - α j)
    rw [map_sub]
  have hmomentK : ∀ t, t < rows → rsSyndromeMoment αK eK t = 0 := by
    intro t ht
    have hmapped := congrArg ιK (hmoment t ht)
    rw [map_zero] at hmapped
    rw [rsSyndromeMoment]
    calc
      (∑ i : ι,
          αK i ^ t * eK i / rsBarycentricDenominator αK i) =
          ∑ i : ι, ιK
            (Polynomial.C
              (α i ^ t / rsBarycentricDenominator α i) * e i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hdenominator i]
        change φ (α i) ^ t * ιK (e i) /
            φ (rsBarycentricDenominator α i) =
          ιK (Polynomial.C
            (α i ^ t / rsBarycentricDenominator α i) * e i)
        rw [map_mul]
        change φ (α i) ^ t * ιK (e i) /
            φ (rsBarycentricDenominator α i) =
          φ (α i ^ t / rsBarycentricDenominator α i) * ιK (e i)
        rw [map_div₀, map_pow]
        ring
      _ = ιK (polynomialSyndromeMoment α e t) := by
        rw [polynomialSyndromeMoment, map_sum]
      _ = 0 := hmapped
  have hinterpolate :=
    rsSyndromeInterpolation_natDegree_lt_card_sub_of_zero_prefix
      αK eK rows hrows hmomentK
  rw [← hQmapEq] at hinterpolate
  have hQmapEqDegree : (Q.map ιK).natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hιK Q
  rw [hQmapEqDegree] at hinterpolate
  simpa only [Q] using hinterpolate

end ProximityPrize.SubmissionLower
