import ProximityPrize.SubmissionLower.BCHKSInterpolation6399
import ProximityPrize.SubmissionLower.BCHKSShellDecomposition6400

/-!
# Reusing the accepted interpolant on the score-64 shell

The accepted score-63.99 Guruswami--Sudan interpolant has multiplicity `3733`
and substituted `X`-degree at most `692001141`.  Ten fewer agreement points
therefore do not make the specialization arbitrary: after removing the
`3733`-fold agreement locator, the remaining cofactor has degree below
`37330 = 10 * 3733`.

This is the exact small residual which a shell-specific alignment argument
must exploit.
-/

open scoped BigOperators Classical

noncomputable section

namespace ProximityPrize.SubmissionLower.BCHKSInterpolationShell6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSConcreteGS6399
open BCHKSSubstitutionVanish

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

universe u v

/-- The product of the selected linear agreement factors, each repeated `m`
times. -/
noncomputable def agreementMultiplicityLocator
    {F : Type u} [Field F] {I : Type v} [DecidableEq I]
    (omega : I ↪ F) (A : Finset I) (m : ℕ) : F[X] :=
  (Lagrange.nodal A fun i ↦ omega i) ^ m

@[simp]
theorem agreementMultiplicityLocator_natDegree
    {F : Type u} [Field F] {I : Type v} [DecidableEq I]
    (omega : I ↪ F) (A : Finset I) (m : ℕ) :
    (agreementMultiplicityLocator omega A m).natDegree = m * A.card := by
  simp only [agreementMultiplicityLocator, Polynomial.natDegree_pow,
    Lagrange.natDegree_nodal]

theorem agreementMultiplicityLocator_ne_zero
    {F : Type u} [Field F] {I : Type v} [DecidableEq I]
    (omega : I ↪ F) (A : Finset I) (m : ℕ) :
    agreementMultiplicityLocator omega A m ≠ 0 := by
  exact pow_ne_zero _ Lagrange.nodal_ne_zero

/-- Distinct selected roots with multiplicity at least `m` contribute their
whole powered nodal locator as a divisor. -/
theorem agreementMultiplicityLocator_dvd
    {F : Type u} [Field F] {I : Type v} [DecidableEq I]
    (R : F[X]) (hR : R ≠ 0) (omega : I ↪ F) (A : Finset I) (m : ℕ)
    (hmult : ∀ i ∈ A, m ≤ R.rootMultiplicity (omega i)) :
    agreementMultiplicityLocator omega A m ∣ R := by
  rw [agreementMultiplicityLocator, Lagrange.nodal, ← Finset.prod_pow]
  refine Finset.prod_dvd_of_coprime (fun i _hi j _hj hij ↦ ?_)
    (fun i hi ↦ ?_)
  · exact (Polynomial.pairwise_coprime_X_sub_C omega.injective hij).pow
  · exact (Polynomial.le_rootMultiplicity_iff hR).mp (hmult i hi)

/-- Choose the residual cofactor and retain exact degree accounting. -/
theorem exists_agreementMultiplicityCofactor
    {F : Type u} [Field F] {I : Type v} [DecidableEq I]
    (R : F[X]) (hR : R ≠ 0) (omega : I ↪ F) (A : Finset I) (m : ℕ)
    (hmult : ∀ i ∈ A, m ≤ R.rootMultiplicity (omega i)) :
    ∃ Cof : F[X],
      agreementMultiplicityLocator omega A m * Cof = R ∧
      Cof ≠ 0 ∧ m * A.card + Cof.natDegree = R.natDegree := by
  obtain ⟨Cof, hfactor⟩ :=
    agreementMultiplicityLocator_dvd R hR omega A m hmult
  have hfactor' : agreementMultiplicityLocator omega A m * Cof = R :=
    hfactor.symm
  have hCof : Cof ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hfactor'
    exact hR hfactor'.symm
  have hdegree := congrArg Polynomial.natDegree hfactor'
  rw [Polynomial.natDegree_mul
      (agreementMultiplicityLocator_ne_zero omega A m) hCof,
    agreementMultiplicityLocator_natDegree] at hdegree
  exact ⟨Cof, hfactor', hCof, hdegree⟩

/-- Concrete residual factorization for one specialization of the accepted
interpolant at the score-64 agreement threshold. -/
theorem exists_score6400_shell_residual
    (Q : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (z : IRSProfile.Field) (P : Polynomial IRSProfile.Field)
    (A : Finset IRSProfile.Index)
    (U₀ U₁ : IRSProfile.Index → IRSProfile.Field)
    (hvan : ∀ i ∈ A, ∀ s t h, s + t < 3733 →
      ((((Polynomial.Bivariate.shift Q
        (Polynomial.C (IRSProfile.domain i))
        (Polynomial.C (U₀ i) + Polynomial.X * Polynomial.C (U₁ i))).coeff t).coeff s).coeff h) = 0)
    (hmatch : ∀ i ∈ A,
      Polynomial.eval (IRSProfile.domain i) P = U₀ i + z * U₁ i)
    (hPdegree : P.natDegree ≤ 131071)
    (hcap : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 692001142)
    (hAcard : 185364 ≤ A.card) :
    ∃ Cof : Polynomial IRSProfile.Field,
      agreementMultiplicityLocator IRSProfile.domain A 3733 * Cof =
        triEval Q z P ∧
      (triEval Q z P = 0 ∨
        (Cof ≠ 0 ∧ Cof.natDegree < 37330 ∧
          3733 * A.card + Cof.natDegree = (triEval Q z P).natDegree)) := by
  let R := triEval Q z P
  by_cases hR : R = 0
  · refine ⟨0, ?_, Or.inl ?_⟩
    · simp only [mul_zero, R, hR]
    · exact hR
  · have hmult : ∀ i ∈ A,
        3733 ≤ R.rootMultiplicity (IRSProfile.domain i) := by
      intro i hi
      apply rootMultiplicity_triEval_ge_of_shift_coeff_zero
        Q (IRSProfile.domain i) z
          (Polynomial.C (U₀ i) + Polynomial.X * Polynomial.C (U₁ i))
          P 3733
      · exact hvan i hi
      · rw [hmatch i hi]
        simp
        ring
      · exact hR
    obtain ⟨Cof, hfactor, hCof, hdegree⟩ :=
      exists_agreementMultiplicityCofactor R hR IRSProfile.domain A 3733 hmult
    have hRdegree : R.natDegree ≤ 692001141 := by
      apply triEval_natDegree_le_of_weighted_X_cap Q z P 131071 692001141
      · exact hPdegree
      · intro j a hja
        have := hcap j a hja
        omega
    have hCofDegree : Cof.natDegree < 37330 := by
      omega
    exact ⟨Cof, hfactor, Or.inr ⟨hCof, hCofDegree, hdegree⟩⟩

/-- The accepted interpolation system itself can be reused unchanged at
`185364` agreements.  Every specialization is either identically zero or has
the degree-`<37330` residual described above. -/
theorem exists_bchks_interpolant_with_shell_residual6400
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (S : Finset IRSProfile.Field)
    (A : IRSProfile.Field → Finset IRSProfile.Index)
    (hA : ∀ z ∈ S, 185364 ≤ (A z).card)
    (hcomb : ∀ z ∈ S,
      LinearCode.projectedWord (fun i ↦ U 0 i + z * U 1 i) (A z) ∈
        LinearCode.projectedCodeSubmod IRSProfile.baseCode (A z)) :
    ∃ (P : ↑S → Polynomial IRSProfile.Field)
      (Q : Polynomial (Polynomial (Polynomial IRSProfile.Field))),
      Q ≠ 0 ∧
      (∀ z : ↑S, (P z).natDegree ≤ 131071) ∧
      (∀ z : ↑S, ∀ i ∈ A z,
        Polynomial.eval (IRSProfile.domain i) (P z) = U 0 i + z.1 * U 1 i) ∧
      (∀ z : ↑S, ∃ Cof : Polynomial IRSProfile.Field,
        agreementMultiplicityLocator IRSProfile.domain (A z) 3733 * Cof =
          triEval Q z.1 (P z) ∧
        (triEval Q z.1 (P z) = 0 ∨
          (Cof ≠ 0 ∧ Cof.natDegree < 37330 ∧
            3733 * (A z).card + Cof.natDegree =
              (triEval Q z.1 (P z)).natDegree))) ∧
      (∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
        j < 5280 ∧ a + 131071 * j < 692001142 ∧
          ((Q.coeff j).coeff a).natDegree + j < 13141403) := by
  classical
  have hw : ∀ z : ↑S, ∃ p : Polynomial IRSProfile.Field,
      p.natDegree ≤ 131071 ∧
      ∀ i ∈ A z.1,
        Polynomial.eval (IRSProfile.domain i) p = U 0 i + z.1 * U 1 i := by
    intro z
    have hz := hcomb z.1 z.2
    rw [LinearCode.mem_projectedCodeSubmod_iff] at hz
    obtain ⟨c, hc, hceq⟩ := hz
    change c ∈ ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension at hc
    rw [ReedSolomon.mem_code_iff_exists_polynomial] at hc
    obtain ⟨p, hpdeg, rfl⟩ := hc
    refine ⟨p, ?_, ?_⟩
    · by_cases hp : p = 0
      · simp [hp]
      · have hlt : p.natDegree < IRSProfile.baseDimension :=
          (Polynomial.natDegree_lt_iff_degree_lt hp).2 hpdeg
        norm_num [IRSProfile.baseDimension] at hlt ⊢
        omega
    · intro i hi
      have heq := congrFun hceq ⟨i, hi⟩
      simpa [LinearCode.projectedWord, ReedSolomon.evalOnPoints] using heq.symm
  let P : ↑S → Polynomial IRSProfile.Field := fun z ↦ Classical.choose (hw z)
  have hPdeg : ∀ z : ↑S, (P z).natDegree ≤ 131071 :=
    fun z ↦ (Classical.choose_spec (hw z)).1
  have hPagree : ∀ z : ↑S, ∀ i ∈ A z.1,
      Polynomial.eval (IRSProfile.domain i) (P z) = U 0 i + z.1 * U 1 i :=
    fun z ↦ (Classical.choose_spec (hw z)).2
  obtain ⟨Q, hQ, hvan, hcaps⟩ :=
    BCHKSConcreteGS6399.exists_interpolant IRSProfile.domain (U 0) (U 1)
  refine ⟨P, Q, hQ, hPdeg, hPagree, ?_, ?_⟩
  · intro z
    apply exists_score6400_shell_residual Q z.1 (P z) (A z.1) (U 0) (U 1)
    · intro i hi s t h hs
      have hz := congrArg (fun p : Polynomial IRSProfile.Field ↦ p.coeff h)
        (hvan i s t hs)
      exact hz
    · exact hPagree z
    · exact hPdeg z
    · intro j a hja
      have hc := hcaps j a hja
      norm_num [BCHKSConcreteGS6399.DY, BCHKSConcreteGS6399.DX,
        BCHKSConcreteGS6399.k, BCHKSConcreteGS6399.DZ] at hc
      omega
    · exact hA z.1 z.2
  · intro j a hja
    have hc := hcaps j a hja
    norm_num [BCHKSConcreteGS6399.DY, BCHKSConcreteGS6399.DX,
      BCHKSConcreteGS6399.k, BCHKSConcreteGS6399.DZ] at hc
    exact hc

end ProximityPrize.SubmissionLower.BCHKSInterpolationShell6400
