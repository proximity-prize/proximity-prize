import ProximityPrize.SubmissionLower.BCHKSLocatorHankelPencil6400
import ProximityPrize.SubmissionLower.BCHKSReedSolomonBadWitness6400

/-!
# Error locators as syndrome-Hankel kernel vectors

This is the direct, support-independent syndrome interface for the score-64
column-far branch.  Unlike the sparse-source bridge, its locator belongs to
the base field because all evaluation nodes do.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial
open scoped BigOperators

variable {K : Type} [Field K]

/-- The barycentrically normalized Reed--Solomon syndrome moment. -/
noncomputable def rsSyndromeMoment
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (e : ι → K) (t : ℕ) : K :=
  ∑ i : ι, α i ^ t * e i / rsBarycentricDenominator α i

theorem rsSyndromeMoment_affine
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (e₀ e₁ : ι → K) (z : K) (t : ℕ) :
    rsSyndromeMoment α (fun i => e₀ i + z * e₁ i) t =
      rsSyndromeMoment α e₀ t + z * rsSyndromeMoment α e₁ t := by
  classical
  simp only [rsSyndromeMoment]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The agreement-complement locator is fixed by every coefficient
automorphism which fixes the evaluation nodes. -/
theorem map_rsAgreementLocator
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (sigma : K ≃+* K)
    (hfixed : ∀ i, sigma (α i) = α i) (A : Finset ι) :
    (rsAgreementLocator α A).map sigma.toRingHom =
      rsAgreementLocator α A := by
  simp only [rsAgreementLocator, Lagrange.nodal, Polynomial.map_prod,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  apply Finset.prod_congr rfl
  intro i hi
  rw [show sigma.toRingHom (α i) = α i from hfixed i]

theorem map_rsAgreementLocator_coeff
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (sigma : K ≃+* K)
    (hfixed : ∀ i, sigma (α i) = α i) (A : Finset ι) (j : ℕ) :
    sigma ((rsAgreementLocator α A).coeff j) =
      (rsAgreementLocator α A).coeff j := by
  have hmap := congrArg (fun Q : K[X] => Q.coeff j)
    (map_rsAgreementLocator α sigma hfixed A)
  simpa using hmap

/-- Expanding the error locator by coefficients turns the locator moment
identity into the usual Hankel convolution equation. -/
theorem rs_locator_coeff_syndrome_convolution_eq_zero
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (A : Finset ι) (e : ι → K) (P : K[X])
    (hagree : ∀ i ∈ A, P.eval (α i) = e i)
    (radius t : ℕ)
    (hradius : (rsAgreementLocator α A).natDegree ≤ radius)
    (hdegree : (Finset.univ \ A).card + P.natDegree + t <
      Fintype.card ι - 1) :
    ∑ j : Fin (radius + 1),
        (rsAgreementLocator α A).coeff j.1 *
          rsSyndromeMoment α e (t + j.1) = 0 := by
  classical
  let L := rsAgreementLocator α A
  have hmoment := rs_locator_syndrome_moment_eq_zero
    α A e P hagree t hdegree
  simp only [rsSyndromeMoment]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ i : ι, ∑ j : Fin (radius + 1),
        L.coeff j.1 *
          (α i ^ (t + j.1) * e i / rsBarycentricDenominator α i)) =
        ∑ i : ι,
          α i ^ t * e i * L.eval (α i) /
            rsBarycentricDenominator α i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Polynomial.eval_eq_sum_range'
        (Nat.lt_succ_of_le hradius) (α i)]
      rw [← Fin.sum_univ_eq_sum_range]
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_add]
      ring
    _ = 0 := by
      calc
        (∑ i : ι,
            α i ^ t * e i * L.eval (α i) /
              rsBarycentricDenominator α i) =
            ∑ i : ι, α i ^ t * e i * rsLocatorVector α A i := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [L, rsLocatorVector]
          ring
        _ = 0 := hmoment

/-- The truncated Hankel matrix of syndrome moments. -/
noncomputable def rsSyndromeHankel
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (e : ι → K) (rows radius : ℕ) :
    Matrix (Fin rows) (Fin (radius + 1)) K := fun i j =>
  rsSyndromeMoment α e (i.1 + j.1)

/-- Coefficients of the agreement-complement locator, padded to the declared
error radius. -/
noncomputable def rsLocatorCoefficients
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (A : Finset ι) (radius : ℕ) : Fin (radius + 1) → K :=
  fun j => (rsAgreementLocator α A).coeff j.1

/-- A bounded agreement-complement locator lies in the syndrome-Hankel
kernel. -/
theorem rsLocatorCoefficients_mem_hankel_ker
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (A : Finset ι) (e : ι → K) (P : K[X])
    (hagree : ∀ i ∈ A, P.eval (α i) = e i)
    (rows radius : ℕ)
    (hradius : (rsAgreementLocator α A).natDegree ≤ radius)
    (hdegreeRoom : (Finset.univ \ A).card + P.natDegree + rows ≤
      Fintype.card ι - 1) :
    rsLocatorCoefficients α A radius ∈
      LinearMap.ker (rsSyndromeHankel α e rows radius).mulVecLin := by
  rw [LinearMap.mem_ker]
  funext i
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    rsSyndromeHankel, rsLocatorCoefficients, Pi.zero_apply]
  have hconv := rs_locator_coeff_syndrome_convolution_eq_zero
    α A e P hagree radius i.1 hradius (by omega)
  simpa only [mul_comm, add_comm] using hconv

/-- The padded locator coefficient vector is nonzero because the nodal
locator is monic. -/
theorem rsLocatorCoefficients_ne_zero
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (A : Finset ι) (radius : ℕ)
    (hradius : (rsAgreementLocator α A).natDegree ≤ radius) :
    rsLocatorCoefficients α A radius ≠ 0 := by
  intro hzero
  let d := (rsAgreementLocator α A).natDegree
  have hd : d < radius + 1 := Nat.lt_succ_of_le hradius
  have hcoeff : (rsAgreementLocator α A).coeff d = 1 := by
    have hmonic := Lagrange.nodal_monic
      (s := Finset.univ \ A) (v := fun i => α i)
    simpa only [rsAgreementLocator, Polynomial.Monic,
      Polynomial.leadingCoeff, d] using hmonic
  have hdzero := congrFun hzero (⟨d, hd⟩ : Fin (radius + 1))
  change (rsAgreementLocator α A).coeff d = 0 at hdzero
  rw [hcoeff] at hdzero
  exact one_ne_zero hdzero

/-- A Reed--Solomon agreement witness therefore supplies a nontrivial
Hankel kernel, with no fixed support hypothesis on the received word. -/
theorem rsSyndromeHankel_ker_ne_bot_of_agreement
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (A : Finset ι) (e : ι → K) (P : K[X])
    (hagree : ∀ i ∈ A, P.eval (α i) = e i)
    (rows radius : ℕ)
    (hradius : (rsAgreementLocator α A).natDegree ≤ radius)
    (hdegreeRoom : (Finset.univ \ A).card + P.natDegree + rows ≤
      Fintype.card ι - 1) :
    LinearMap.ker (rsSyndromeHankel α e rows radius).mulVecLin ≠ ⊥ := by
  intro hbot
  have hmem : rsLocatorCoefficients α A radius ∈
      (⊥ : Submodule K (Fin (radius + 1) → K)) := by
    rw [← hbot]
    exact rsLocatorCoefficients_mem_hankel_ker
      α A e P hagree rows radius hradius hdegreeRoom
  exact rsLocatorCoefficients_ne_zero α A radius hradius (by simpa using hmem)

open ProximityPrize.Benchmark
open BCHKSExactSparsification6400

/-- Every concrete score-64 MCA witness supplies a nonzero locator vector
fixed by the sextic Frobenius and lying in the direct syndrome-Hankel kernel.
No translation or common pair support is used. -/
theorem exists_score6400_fixed_locator_of_mcaBad
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field)
    (hbad : MCABad IRSProfile.baseCode f₀ f₁ 185364 z) :
    ∃ locator : Fin (76780 + 1) → IRSProfile.Field,
      locator ≠ 0 ∧
      (∀ j, koalaSexticFrobenius (locator j) = locator j) ∧
      locator ∈ LinearMap.ker
        (rsSyndromeHankel IRSProfile.domain
          (fun i => f₀ i + z * f₁ i)
          locatorOrdinaryRows6400 76780).mulVecLin := by
  classical
  have hbadRS : MCABad
      (ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension)
      f₀ f₁ 185364 z := by
    simpa only [IRSProfile.baseCode] using hbad
  obtain ⟨A, P, hA, hPdegree, hPagree, _hintersects⟩ :=
    exists_rs_polynomial_data_of_mcaBad
      IRSProfile.domain IRSProfile.baseDimension 185364 f₀ f₁ z hbadRS
  have hPnat : P.natDegree ≤ 131071 := by
    by_cases hPzero : P = 0
    · simp [hPzero]
    · have hlt : P.natDegree < IRSProfile.baseDimension :=
        (Polynomial.natDegree_lt_iff_degree_lt hPzero).2 hPdegree
      norm_num [IRSProfile.baseDimension] at hlt ⊢
      omega
  have hAcap : (Finset.univ \ A).card ≤ 76780 := by
    calc
      (Finset.univ \ A).card =
          Fintype.card IRSProfile.Index - A.card := by
        rw [Finset.card_sdiff]
        simp
      _ ≤ Fintype.card IRSProfile.Index - 185364 :=
        Nat.sub_le_sub_left hA _
      _ = 76780 := by norm_num [IRSProfile.Index]
  have hlocator :
      (rsAgreementLocator IRSProfile.domain A).natDegree ≤ 76780 := by
    rw [rsAgreementLocator_natDegree]
    exact hAcap
  let locator := rsLocatorCoefficients IRSProfile.domain A 76780
  have hlocatorNe : locator ≠ 0 :=
    rsLocatorCoefficients_ne_zero IRSProfile.domain A 76780 hlocator
  have hlocatorFixed : ∀ j,
      koalaSexticFrobenius (locator j) = locator j := by
    intro j
    simpa only [locator, rsLocatorCoefficients] using map_rsAgreementLocator_coeff
      IRSProfile.domain koalaSexticFrobenius
      koalaSexticFrobenius_fixed_domain A j.1
  have hdegreeRoom :
      (Finset.univ \ A).card + P.natDegree + locatorOrdinaryRows6400 ≤
        Fintype.card IRSProfile.Index - 1 := by
    norm_num [locatorOrdinaryRows6400, IRSProfile.Index]
    omega
  have hlocatorMem : locator ∈ LinearMap.ker
      (rsSyndromeHankel IRSProfile.domain
        (fun i => f₀ i + z * f₁ i)
        locatorOrdinaryRows6400 76780).mulVecLin := by
    exact rsLocatorCoefficients_mem_hankel_ker
      IRSProfile.domain A (fun i => f₀ i + z * f₁ i) P hPagree
      locatorOrdinaryRows6400 76780 hlocator hdegreeRoom
  exact ⟨locator, hlocatorNe, hlocatorFixed, hlocatorMem⟩

/-- Kernel-only corollary of the fixed-locator witness. -/
theorem score6400_locatorHankel_ker_ne_bot_of_mcaBad
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field)
    (hbad : MCABad IRSProfile.baseCode f₀ f₁ 185364 z) :
    LinearMap.ker
      (rsSyndromeHankel IRSProfile.domain
        (fun i => f₀ i + z * f₁ i)
        locatorOrdinaryRows6400 76780).mulVecLin ≠ ⊥ := by
  obtain ⟨locator, hlocatorNe, _hlocatorFixed, hlocatorMem⟩ :=
    exists_score6400_fixed_locator_of_mcaBad f₀ f₁ z hbad
  intro hbot
  apply hlocatorNe
  have : locator ∈ (⊥ : Submodule IRSProfile.Field
      (Fin (76780 + 1) → IRSProfile.Field)) := by
    rw [← hbot]
    exact hlocatorMem
  simpa using this

end ProximityPrize.SubmissionLower
