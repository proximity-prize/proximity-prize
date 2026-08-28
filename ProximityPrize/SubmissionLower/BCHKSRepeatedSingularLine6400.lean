import ProximityPrize.SubmissionLower.BCHKSAlignmentRepeatedInterface6400
import ProximityPrize.SubmissionLower.BCHKSAgreementRootedTangency6400

/-!
# Repeated affine coordinates produce singular lines

The residual score-64 branch supplies an affine root of the selected factor
whose `Y` derivative vanishes identically.  On every exact section agreeing
at such a coordinate, the chain rule forces the middle-variable (`X`)
partial to vanish as well.  A sufficiently large agreement fibre therefore
promotes that pointwise tangency to an identity along the whole affine
challenge line.  This is the first algebraic input for a ramified blow-up.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

variable {F : Type} [Field F]

/-- Formal derivative of a trivariate polynomial in its middle (`X`)
variable.  The innermost coefficient variable (`Z`) is left untouched. -/
noncomputable def triCoeffDerivativeX (R : F[X][X][Y]) : F[X][X][Y] :=
  R.sum fun j c => Polynomial.monomial j c.derivative

@[simp]
theorem triCoeffDerivativeX_add (R S : F[X][X][Y]) :
    triCoeffDerivativeX (R + S) =
      triCoeffDerivativeX R + triCoeffDerivativeX S := by
  classical
  unfold triCoeffDerivativeX
  apply Polynomial.sum_add_index
  · intro i
    simp
  · intro i a b
    simp

@[simp]
theorem triCoeffDerivativeX_monomial (n : ℕ) (c : F[X][X]) :
    triCoeffDerivativeX (Polynomial.monomial n c) =
      Polynomial.monomial n c.derivative := by
  classical
  simp [triCoeffDerivativeX]

@[simp]
theorem triCoeffDerivativeX_coeff (R : F[X][X][Y]) (j : ℕ) :
    (triCoeffDerivativeX R).coeff j = (R.coeff j).derivative := by
  classical
  induction R using Polynomial.induction_on' with
  | add R S hR hS => simp [hR, hS]
  | monomial n c =>
      by_cases hnj : n = j
      · subst j
        simp
      · simp [Polynomial.coeff_monomial, hnj]

@[simp]
theorem triSpecializeZ_triCoeffDerivativeX (R : F[X][X][Y]) (z : F) :
    triSpecializeZ (triCoeffDerivativeX R) z =
      coeffDerivativeX (triSpecializeZ R z) := by
  induction R using Polynomial.induction_on' with
  | add R S hR hS =>
      calc
        triSpecializeZ (triCoeffDerivativeX (R + S)) z =
            triSpecializeZ (triCoeffDerivativeX R) z +
              triSpecializeZ (triCoeffDerivativeX S) z := by
                simp [triSpecializeZ]
        _ = coeffDerivativeX (triSpecializeZ R z) +
              coeffDerivativeX (triSpecializeZ S z) :=
            congrArg₂ (· + ·) hR hS
        _ = coeffDerivativeX (triSpecializeZ (R + S) z) := by
            simp [triSpecializeZ]
  | monomial n c =>
      rw [triCoeffDerivativeX_monomial]
      unfold triSpecializeZ
      rw [Polynomial.map_monomial, Polynomial.map_monomial,
        coeffDerivativeX_monomial]
      exact congrArg (Polynomial.monomial n)
        (Polynomial.derivative_map c (Polynomial.evalRingHom z)).symm

/-- Evaluation of all three variables is independent of whether `X` or `Z`
is specialized first. -/
theorem biEval_triSpecializeX_eq_eval₂_triSpecializeZ
    (R : F[X][X][Y]) (x z y : F) :
    biEval (triSpecializeX R x) y z =
      Polynomial.eval₂ (Polynomial.evalRingHom x) y
        (triSpecializeZ R z) := by
  induction R using Polynomial.induction_on' with
  | add R S hR hS =>
      calc
        biEval (triSpecializeX (R + S) x) y z =
            biEval (triSpecializeX R x) y z +
              biEval (triSpecializeX S x) y z := by
                simp [biEval, triSpecializeX]
        _ = Polynomial.eval₂ (Polynomial.evalRingHom x) y
              (triSpecializeZ R z) +
            Polynomial.eval₂ (Polynomial.evalRingHom x) y
              (triSpecializeZ S z) := congrArg₂ (· + ·) hR hS
        _ = Polynomial.eval₂ (Polynomial.evalRingHom x) y
              (triSpecializeZ (R + S) z) := by
                simp [triSpecializeZ]
  | monomial n c =>
      simp only [triSpecializeX, triSpecializeZ,
        Polynomial.map_monomial, Polynomial.eval_monomial, biEval,
        Polynomial.eval₂_monomial]
      exact congrArg (fun q : F => q * y ^ n)
        (eval_map_eval_eq_eval_eval_C c x z).symm

/-- Affine substitution in a bivariate polynomial commutes with evaluating
its coefficient variable. -/
theorem eval_affine_specialization_commute_repeated_6400
    (J : F[X][Y]) (a b z : F) :
    (J.eval (Polynomial.C a + Polynomial.X * Polynomial.C b)).eval z =
      (J.map (Polynomial.evalRingHom z)).eval (a + z * b) := by
  rw [mul_comm Polynomial.X (Polynomial.C b), mul_comm z b]
  induction J using Polynomial.induction_on' with
  | add J K hJ hK =>
      simpa using congrArg₂ (· + ·) hJ hK
  | monomial n c =>
      simp [Polynomial.map_monomial, Polynomial.eval_monomial]

/-- Inserting an affine coordinate into the middle partial commutes with
specializing the challenge and evaluating the remaining two variables. -/
theorem directAffineObstruction_triCoeffDerivativeX_eval
    (R : F[X][X][Y]) (x a b z : F) :
    (directAffineObstruction (triCoeffDerivativeX R) x a b).eval z =
      Polynomial.eval₂ (Polynomial.evalRingHom x) (a + z * b)
        (coeffDerivativeX (triSpecializeZ R z)) := by
  rw [directAffineObstruction_eval]
  rw [biEval_triSpecializeX_eq_eval₂_triSpecializeZ]
  rw [triSpecializeZ_triCoeffDerivativeX]

/-- Pointwise repeated-root tangency, expressed as a root of the direct
middle-partial obstruction in the challenge variable. -/
theorem directCoeffXObstruction_root_of_exact_agreement
    (R : F[X][X][Y]) (P : F[X]) (x a b z : F)
    (hExact : triEval R z P = 0)
    (hagree : P.eval x = a + z * b)
    (hY : (triSpecializeX R x).derivative.eval
      (Polynomial.C a + Polynomial.X * Polynomial.C b) = 0) :
    (directAffineObstruction (triCoeffDerivativeX R) x a b).eval z = 0 := by
  rw [directAffineObstruction_triCoeffDerivativeX_eval]
  apply coeffDerivativeX_eval_eq_zero_of_exact_root_of_yDerivative_eq_zero
    (triSpecializeZ R z) P x (a + z * b)
  · simpa only [← triEval_eq_eval_triSpecializeZ] using hExact
  · exact hagree
  · have hpoint := congrArg (fun q : F[X] => q.eval z) hY
    have hcommRaw := biEval_triSpecializeX_eq_eval₂_triSpecializeZ
      R.derivative x z (a + z * b)
    have hcomm :
        biEval ((triSpecializeX R x).derivative) (a + z * b) z =
          Polynomial.eval₂ (Polynomial.evalRingHom x) (a + z * b)
            (triSpecializeZ R z).derivative := by
      simpa [triSpecializeX, triSpecializeZ,
        Polynomial.derivative_map] using hcommRaw
    have haff :
        biEval ((triSpecializeX R x).derivative) (a + z * b) z = 0 := by
      unfold biEval
      rw [← eval_affine_specialization_commute_repeated_6400]
      rw [hY]
      simp
    rw [← hcomm]
    exact haff

/-- The middle partial preserves the selected factor's additive `Y,Z` cap. -/
theorem yzCap_triCoeffDerivativeX
    (R : F[X][X][Y]) (D : ℕ) (hYZ : YZCap R D) :
    YZCap (triCoeffDerivativeX R) D := by
  intro j a hne
  rw [triCoeffDerivativeX_coeff, Polynomial.coeff_derivative] at hne ⊢
  have horig : (R.coeff j).coeff (a + 1) ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hne
    exact hne rfl
  have hcap := hYZ j (a + 1) horig
  have hdeg :
      ((R.coeff j).coeff (a + 1) * (a + 1)).natDegree ≤
        ((R.coeff j).coeff (a + 1)).natDegree := by
    have hscalar : ((a : F[X]) + 1).natDegree = 0 := by
      have heq : ((a : F[X]) + 1) = Polynomial.C ((a : F) + 1) := by
        simp
      calc
        ((a : F[X]) + 1).natDegree =
            (Polynomial.C ((a : F) + 1)).natDegree := congrArg _ heq
        _ = 0 := Polynomial.natDegree_C _
    calc
      ((R.coeff j).coeff (a + 1) * (a + 1)).natDegree ≤
          ((R.coeff j).coeff (a + 1)).natDegree +
            ((a : F[X]) + 1).natDegree :=
        Polynomial.natDegree_mul_le
      _ = ((R.coeff j).coeff (a + 1)).natDegree := by rw [hscalar]; omega
  exact (Nat.add_le_add_right hdeg j).trans hcap

/-- More roots than the additive cap promote pointwise tangency to an
identity along the entire affine challenge line. -/
theorem directCoeffXObstruction_eq_zero_of_many_exact_agreements
    [DecidableEq F]
    (R : F[X][X][Y]) (P : F → F[X]) (T : Finset F)
    (x a b : F) (D : ℕ) (hYZ : YZCap R D)
    (hExact : ∀ z ∈ T, triEval R z (P z) = 0)
    (hagree : ∀ z ∈ T, (P z).eval x = a + z * b)
    (hY : (triSpecializeX R x).derivative.eval
      (Polynomial.C a + Polynomial.X * Polynomial.C b) = 0)
    (hlarge : D < T.card) :
    directAffineObstruction (triCoeffDerivativeX R) x a b = 0 := by
  let G : F[X] :=
    directAffineObstruction (triCoeffDerivativeX R) x a b
  have hroot : ∀ z ∈ T, G.eval z = 0 := by
    intro z hz
    exact directCoeffXObstruction_root_of_exact_agreement
      R (P z) x a b z (hExact z hz) (hagree z hz) hY
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' G T hroot
  exact (directAffineObstruction_natDegree_le
    (triCoeffDerivativeX R) x a b D
      (yzCap_triCoeffDerivativeX R D hYZ)).trans_lt hlarge

/-- The already-known `R=0` and `R_Y=0` identities also force the
challenge-variable partial `R_Z` to vanish along the same affine line. -/
theorem coeffDerivativeZ_affine_identity_of_repeated_affine_identity
    (J : F[X][Y]) (a b : F)
    (hroot : J.eval
      (Polynomial.C a + Polynomial.X * Polynomial.C b) = 0)
    (hY : J.derivative.eval
      (Polynomial.C a + Polynomial.X * Polynomial.C b) = 0) :
    (coeffDerivativeX J).eval
      (Polynomial.C a + Polynomial.X * Polynomial.C b) = 0 := by
  let L : F[X] := Polynomial.C a + Polynomial.X * Polynomial.C b
  have hchain := derivative_eval_eq_coeffDerivativeX_add J L
  have hzero : (J.eval L).derivative = 0 := by rw [hroot]; simp
  rw [hzero, hY] at hchain
  simpa [L] using hchain.symm

/-- Exact arithmetic for the repeated-coordinate incidence extraction. -/
theorem score6400_repeated_base_fiber_numeric
    (t D : ℕ) (hT : 144802557 * D < t) :
    (131413 - 76780) * t >
      131413 * (60199508 * D) := by
  norm_num at hT ⊢
  nlinarith

/-- The same incidence surplus can be spent horizontally instead of on one
very large fibre: at least 54,633 repeated coordinates have more than `D`
agreeing challenges. -/
theorem score6400_many_repeated_fibers_numeric
    (t D : ℕ) (hT : 144802557 * D < t) :
    (131413 - 76780 - 54632) * t >
      (131413 - 54632) * D := by
  norm_num at hT ⊢
  nlinarith

/-- The residual repeated branch contains at least 54,633 distinct singular
affine lines.  This is the simultaneous form of
`exists_repeated_singular_line_base_6400`: instead of spending the incidence
surplus on one huge coordinate fibre, every retained fibre has just enough
roots to promote the middle partial to a polynomial identity. -/
theorem exists_many_repeated_singular_lines_6400
    {I : Type} [Fintype I] [DecidableEq I]
    [DecidableEq F]
    (omega : I ↪ F)
    (U₀ U₁ : I → F)
    (S : Finset F) (A : F → Finset I) (P : ↑S → F[X])
    (R : F[X][X][Y]) (D : ℕ) (Repeat : Finset I)
    (hn : Fintype.card I = 262144)
    (hYZ : YZCap R D)
    (hrow : ∀ z : ↑S, 185364 ≤ (A z.1).card)
    (hagree : ∀ z : ↑S, ∀ i ∈ A z,
      (P z).eval (omega i) = U₀ i + z.1 * U₁ i)
    (hExact : ∀ z : ↑S, triEval R z.1 (P z) = 0)
    (hRepeatCard : Repeat.card = 131413)
    (hRepeat : ∀ i ∈ Repeat,
      directAffineObstruction R (omega i) (U₀ i) (U₁ i) = 0 ∧
      (triSpecializeX R (omega i)).derivative.eval
        (Polynomial.C (U₀ i) +
          Polynomial.X * Polynomial.C (U₁ i)) = 0)
    (hS : 144802557 * D < S.card) :
    ∃ Singular : Finset I,
      Singular ⊆ Repeat ∧
      54633 ≤ Singular.card ∧
      ∀ i ∈ Singular,
        D < (S.filter fun z => i ∈ A z).card ∧
        directAffineObstruction R (omega i) (U₀ i) (U₁ i) = 0 ∧
        (triSpecializeX R (omega i)).derivative.eval
            (Polynomial.C (U₀ i) +
              Polynomial.X * Polynomial.C (U₁ i)) = 0 ∧
        directAffineObstruction (triCoeffDerivativeX R)
            (omega i) (U₀ i) (U₁ i) = 0 ∧
        (coeffDerivativeX (triSpecializeX R (omega i))).eval
            (Polynomial.C (U₀ i) +
              Polynomial.X * Polynomial.C (U₁ i)) = 0 := by
  classical
  let Singular : Finset I := Repeat.filter fun i =>
    D < (S.filter fun z => i ∈ A z).card
  have hSingularCard : 54633 ≤ Singular.card := by
    have hcount := score6400_many_repeated_fibers_numeric S.card D hS
    have hh := many_large_fibers_in_subset Repeat S A
      262144 76780 54632 D hn
      (fun z hz => by simpa using hrow ⟨z, hz⟩)
      (by simpa [hRepeatCard] using hcount)
    simpa [Singular] using hh
  have hSingularSub : Singular ⊆ Repeat := Finset.filter_subset _ _
  let Pfull : F → F[X] := fun z =>
    if hz : z ∈ S then P ⟨z, hz⟩ else 0
  refine ⟨Singular, hSingularSub, hSingularCard, ?_⟩
  intro i hi
  have hiRepeat : i ∈ Repeat := hSingularSub hi
  have hiFiber : D < (S.filter fun z => i ∈ A z).card :=
    (Finset.mem_filter.mp hi).2
  let T : Finset F := S.filter fun z => i ∈ A z
  have hTsub : T ⊆ S := Finset.filter_subset _ _
  have hPexact : ∀ z ∈ T, triEval R z (Pfull z) = 0 := by
    intro z hz
    have hzS := hTsub hz
    simpa [Pfull, hzS] using hExact ⟨z, hzS⟩
  have hPagree : ∀ z ∈ T,
      (Pfull z).eval (omega i) = U₀ i + z * U₁ i := by
    intro z hz
    have hzS := hTsub hz
    have hiA : i ∈ A z := (Finset.mem_filter.mp hz).2
    simpa [Pfull, hzS] using hagree ⟨z, hzS⟩ i hiA
  have hiData := hRepeat i hiRepeat
  have hXzero : directAffineObstruction (triCoeffDerivativeX R)
      (omega i) (U₀ i) (U₁ i) = 0 := by
    apply directCoeffXObstruction_eq_zero_of_many_exact_agreements
      R Pfull T (omega i) (U₀ i) (U₁ i) D hYZ
      hPexact hPagree hiData.2
    simpa [T] using hiFiber
  have hZzero :=
    coeffDerivativeZ_affine_identity_of_repeated_affine_identity
      (triSpecializeX R (omega i)) (U₀ i) (U₁ i)
      hiData.1 hiData.2
  exact ⟨hiFiber, hiData.1, hiData.2, hXzero, hZzero⟩

/-- The residual repeated branch contains a fixed coordinate whose agreement
fibre is larger than `60,199,508 * D`.  On that coordinate the selected
surface and all three first partials vanish identically along the received
affine challenge line. -/
theorem exists_repeated_singular_line_base_6400
    {I : Type} [Fintype I] [DecidableEq I]
    [DecidableEq F]
    (omega : I ↪ F)
    (U₀ U₁ : I → F)
    (S : Finset F) (A : F → Finset I) (P : ↥S → F[X])
    (R : F[X][X][Y]) (D : ℕ) (Repeat : Finset I)
    (hn : Fintype.card I = 262144)
    (hYZ : YZCap R D)
    (hrow : ∀ z : ↥S, 185364 ≤ (A z.1).card)
    (hagree : ∀ z : ↥S, ∀ i ∈ A z,
      (P z).eval (omega i) = U₀ i + z.1 * U₁ i)
    (hExact : ∀ z : ↥S, triEval R z.1 (P z) = 0)
    (hRepeatCard : Repeat.card = 131413)
    (hRepeat : ∀ i ∈ Repeat,
      directAffineObstruction R (omega i) (U₀ i) (U₁ i) = 0 ∧
      (triSpecializeX R (omega i)).derivative.eval
        (Polynomial.C (U₀ i) +
          Polynomial.X * Polynomial.C (U₁ i)) = 0)
    (hS : 144802557 * D < S.card) :
    ∃ i ∈ Repeat,
      60199508 * D < (S.filter fun z => i ∈ A z).card ∧
      directAffineObstruction R (omega i) (U₀ i) (U₁ i) = 0 ∧
      (triSpecializeX R (omega i)).derivative.eval
        (Polynomial.C (U₀ i) +
          Polynomial.X * Polynomial.C (U₁ i)) = 0 ∧
      directAffineObstruction (triCoeffDerivativeX R)
        (omega i) (U₀ i) (U₁ i) = 0 ∧
      (coeffDerivativeX (triSpecializeX R (omega i))).eval
        (Polynomial.C (U₀ i) +
          Polynomial.X * Polynomial.C (U₁ i)) = 0 := by
  classical
  let Large : Finset I := Repeat.filter fun i =>
    60199508 * D < (S.filter fun z => i ∈ A z).card
  have hLargeCard : 1 ≤ Large.card := by
    have hcount := score6400_repeated_base_fiber_numeric S.card D hS
    have hh := many_large_fibers_in_subset Repeat S A
      262144 76780 0 (60199508 * D) hn
      (fun z hz => by simpa using hrow ⟨z, hz⟩)
      (by simpa [hRepeatCard] using hcount)
    simpa [Large] using hh
  obtain ⟨i, hiLarge⟩ := Finset.card_pos.mp (by omega : 0 < Large.card)
  have hiRepeat : i ∈ Repeat := (Finset.mem_filter.mp hiLarge).1
  have hiFiber :
      60199508 * D < (S.filter fun z => i ∈ A z).card :=
    (Finset.mem_filter.mp hiLarge).2
  let T : Finset F := S.filter fun z => i ∈ A z
  let Pfull : F → F[X] := fun z =>
    if hz : z ∈ S then P ⟨z, hz⟩ else 0
  have hTlarge : D < T.card := by
    have hmul : D ≤ 60199508 * D := by nlinarith
    exact hmul.trans_lt (by simpa [T] using hiFiber)
  have hTsub : T ⊆ S := Finset.filter_subset _ _
  have hPexact : ∀ z ∈ T, triEval R z (Pfull z) = 0 := by
    intro z hz
    have hzS := hTsub hz
    simpa [Pfull, hzS] using hExact ⟨z, hzS⟩
  have hPagree : ∀ z ∈ T,
      (Pfull z).eval (omega i) = U₀ i + z * U₁ i := by
    intro z hz
    have hzS := hTsub hz
    have hiA : i ∈ A z := (Finset.mem_filter.mp hz).2
    simpa [Pfull, hzS] using hagree ⟨z, hzS⟩ i hiA
  have hiData := hRepeat i hiRepeat
  have hXzero : directAffineObstruction (triCoeffDerivativeX R)
      (omega i) (U₀ i) (U₁ i) = 0 := by
    apply directCoeffXObstruction_eq_zero_of_many_exact_agreements
      R Pfull T (omega i) (U₀ i) (U₁ i) D hYZ
      hPexact hPagree hiData.2 hTlarge
  have hZzero :=
    coeffDerivativeZ_affine_identity_of_repeated_affine_identity
      (triSpecializeX R (omega i)) (U₀ i) (U₁ i)
      hiData.1 hiData.2
  exact ⟨i, hiRepeat, hiFiber, hiData.1, hiData.2, hXzero, hZzero⟩

end ProximityPrize.SubmissionLower
