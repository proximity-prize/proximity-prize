import ProximityPrize.SubmissionLower.BCHKSFrobeniusMixedStack6400
import Mathlib.LinearAlgebra.Lagrange

/-!
# Reed--Solomon barycentric syndrome moments

This file supplies the concrete upstream input for the mixed source-stack
bridge.  Its first theorem is the standard dual Reed--Solomon identity:
the barycentrically weighted evaluations of a polynomial of degree below
`n - 1 - j` have vanishing `j`-th moment.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

variable {K : Type} [Field K]

/-- The full-domain barycentric denominator at an injective evaluation
point.  We keep the division form used by Lagrange interpolation so that the
syndrome identity has no hidden normalization convention. -/
noncomputable def rsBarycentricDenominator
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (i : ι) : K :=
  ∏ t ∈ (Finset.univ.erase i), (α i - α t)

theorem rsBarycentricDenominator_ne_zero
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (i : ι) : rsBarycentricDenominator α i ≠ 0 := by
  rw [rsBarycentricDenominator, Finset.prod_ne_zero_iff]
  intro t ht
  exact sub_ne_zero.mpr fun heq =>
    (Finset.mem_erase.mp ht).1 (α.injective heq).symm

/-- The locator which vanishes precisely at coordinates outside `A`. -/
noncomputable def rsAgreementLocator
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (A : Finset ι) : K[X] :=
  Lagrange.nodal (Finset.univ \ A) fun i => α i

@[simp]
theorem rsAgreementLocator_natDegree
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (A : Finset ι) :
    (rsAgreementLocator α A).natDegree = (Finset.univ \ A).card := by
  simp only [rsAgreementLocator, Lagrange.natDegree_nodal]

theorem rsAgreementLocator_eval_eq_zero_of_not_mem
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (A : Finset ι) {i : ι} (hi : i ∉ A) :
    (rsAgreementLocator α A).eval (α i) = 0 := by
  apply Lagrange.eval_nodal_at_node
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact hi

theorem rsAgreementLocator_eval_ne_zero_of_mem
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (A : Finset ι) {i : ι} (hi : i ∈ A) :
    (rsAgreementLocator α A).eval (α i) ≠ 0 := by
  apply Lagrange.eval_nodal_not_at_node
  intro t ht heq
  have hit : i = t := α.injective heq
  subst t
  exact (Finset.mem_sdiff.mp ht).2 hi

/-- The locator evaluation divided by the full-domain barycentric
denominator.  This is the eventual nonzero transpose-kernel vector. -/
noncomputable def rsLocatorVector
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (A : Finset ι) (i : ι) : K :=
  (rsAgreementLocator α A).eval (α i) / rsBarycentricDenominator α i

theorem rsLocatorVector_ne_zero_of_mem
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (A : Finset ι) {i : ι} (hi : i ∈ A) :
    rsLocatorVector α A i ≠ 0 :=
  div_ne_zero (rsAgreementLocator_eval_ne_zero_of_mem α A hi)
    (rsBarycentricDenominator_ne_zero α i)

/-- A low-degree polynomial has zero barycentric moments on every finite set
of distinct evaluation points. -/
theorem rs_barycentric_moment_eq_zero
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (P : K[X]) (j : ℕ)
    (hdegree : P.natDegree + j < Fintype.card ι - 1) :
    ∑ i : ι,
        α i ^ j * P.eval (α i) / rsBarycentricDenominator α i = 0 := by
  classical
  by_cases hP : P = 0
  · simp [hP]
  let Q : K[X] := P * (Polynomial.X : Polynomial K) ^ j
  have hQne : Q ≠ 0 := by
    simpa only [Q] using
      mul_ne_zero hP
        (pow_ne_zero j (Polynomial.X_ne_zero : (Polynomial.X : Polynomial K) ≠ 0))
  have hQnat : Q.natDegree < Fintype.card ι - 1 := by
    simpa only [Q, natDegree_mul_X_pow j hP] using hdegree
  have hcard : 1 < Fintype.card ι := by omega
  have hQnatCard : Q.natDegree < Fintype.card ι := by
    exact hQnat.trans (Nat.sub_lt (by omega) Nat.one_pos)
  have hQdegree : Q.degree < (Fintype.card ι : WithBot ℕ) := by
    rw [degree_eq_natDegree hQne]
    exact WithBot.coe_lt_coe.mpr hQnatCard
  have hcoeff : Q.coeff (Fintype.card ι - 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt hQnat
  have hlagrange := Lagrange.coeff_eq_sum
    (s := Finset.univ) (v := fun i : ι => α i)
    α.injective.injOn hQdegree
  have hcoeff' : Q.coeff ((Finset.univ : Finset ι).card - 1) = 0 := by
    simpa only [Finset.card_univ] using hcoeff
  rw [hcoeff'] at hlagrange
  simpa only [Finset.sum_const_zero, Q, eval_mul,
    eval_pow, eval_X, rsBarycentricDenominator, mul_comm] using hlagrange.symm

/-- If `P` agrees with a word `e` on `A`, multiplying by the locator for the
complement replaces `P` by `e` at every evaluation point.  Lagrange's top-
coefficient formula then gives the weighted syndrome equations. -/
theorem rs_locator_syndrome_moment_eq_zero
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (A : Finset ι) (e : ι → K) (P : K[X])
    (hagree : ∀ i ∈ A, P.eval (α i) = e i) (j : ℕ)
    (hdegree : (Finset.univ \ A).card + P.natDegree + j <
      Fintype.card ι - 1) :
    ∑ i : ι, α i ^ j * e i * rsLocatorVector α A i = 0 := by
  classical
  let L := rsAgreementLocator α A
  have hproductDegree : (L * P).natDegree + j < Fintype.card ι - 1 := by
    calc
      (L * P).natDegree + j ≤ (L.natDegree + P.natDegree) + j :=
        Nat.add_le_add_right natDegree_mul_le j
      _ = (Finset.univ \ A).card + P.natDegree + j := by
        rw [show L.natDegree = (Finset.univ \ A).card by
          simp only [L, rsAgreementLocator_natDegree]]
      _ < Fintype.card ι - 1 := hdegree
  have hmoment := rs_barycentric_moment_eq_zero α (L * P) j hproductDegree
  calc
    ∑ i : ι, α i ^ j * e i * rsLocatorVector α A i =
        ∑ i : ι, α i ^ j * (L * P).eval (α i) /
          rsBarycentricDenominator α i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hreplace : L.eval (α i) * P.eval (α i) =
          L.eval (α i) * e i := by
        by_cases hiA : i ∈ A
        · rw [hagree i hiA]
        · rw [show L.eval (α i) = 0 by
            simpa only [L] using
              rsAgreementLocator_eval_eq_zero_of_not_mem α A hiA]
          simp only [zero_mul]
      rw [eval_mul, hreplace]
      simp only [rsLocatorVector]
      ring
    _ = 0 := hmoment

/-- Injectivity of the evaluation map identifies a coordinate support with
its field-valued image without changing cardinality or summation data. -/
noncomputable def rsSupportEquiv
    {ι : Type} [Fintype ι] (α : ι ↪ K) (T : Finset ι) :
    T ≃ T.map α := by
  let f : T → T.map α := fun i =>
    ⟨α i.1, Finset.mem_map_of_mem α i.2⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro i t hit
    apply Subtype.ext
    apply α.injective
    exact congrArg Subtype.val hit
  · intro x
    obtain ⟨i, hiT, hix⟩ := Finset.mem_map.mp x.2
    refine ⟨⟨i, hiT⟩, ?_⟩
    apply Subtype.ext
    exact hix

@[simp]
theorem rsSupportEquiv_apply_val
    {ι : Type} [Fintype ι] (α : ι ↪ K) (T : Finset ι) (i : T) :
    ((rsSupportEquiv α T i : T.map α) : K) = α i.1 := by
  rfl

/-- Restrict the full-domain locator vector to a field-valued source
support. -/
noncomputable def rsLocatorVectorOnSupport
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (A T : Finset ι) : T.map α → K := fun x =>
  rsLocatorVector α A ((rsSupportEquiv α T).symm x).1

@[simp]
theorem rsLocatorVectorOnSupport_apply
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (A T : Finset ι) (i : T) :
    rsLocatorVectorOnSupport α A T (rsSupportEquiv α T i) =
      rsLocatorVector α A i.1 := by
  simp only [rsLocatorVectorOnSupport, Equiv.symm_apply_apply]

theorem rsLocatorVectorOnSupport_ne_zero
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (A T : Finset ι)
    (hintersects : ∃ i, i ∈ A ∧ i ∈ T) :
    rsLocatorVectorOnSupport α A T ≠ 0 := by
  rintro hzero
  obtain ⟨i, hiA, hiT⟩ := hintersects
  have hi := congrFun hzero (rsSupportEquiv α T ⟨i, hiT⟩)
  rw [rsLocatorVectorOnSupport_apply] at hi
  exact rsLocatorVector_ne_zero_of_mem α A hiA hi

/-- A full-domain syndrome identity restricts exactly to the sparse source
support and transports along its injective image in the field. -/
theorem rs_locator_support_moment_eq_zero
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (A T : Finset ι) (e : ι → K)
    (source : K → K) (P : K[X])
    (hsupport : ∀ i ∉ T, e i = 0)
    (hsource : ∀ i ∈ T, source (α i) = e i)
    (hagree : ∀ i ∈ A, P.eval (α i) = e i) (j : ℕ)
    (hdegree : (Finset.univ \ A).card + P.natDegree + j <
      Fintype.card ι - 1) :
    ∑ x : T.map α,
      x.1 ^ j * source x.1 * rsLocatorVectorOnSupport α A T x = 0 := by
  classical
  have hfull := rs_locator_syndrome_moment_eq_zero
    α A e P hagree j hdegree
  have hrestricted :
      ∑ i ∈ T, α i ^ j * e i * rsLocatorVector α A i = 0 := by
    rw [Finset.sum_subset T.subset_univ]
    · simpa using hfull
    · intro i hiuniv hiT
      rw [hsupport i hiT]
      ring
  have hsubtype :
      ∑ i : T, α i.1 ^ j * e i.1 * rsLocatorVector α A i.1 = 0 := by
    calc
      (∑ i : T, α i.1 ^ j * e i.1 * rsLocatorVector α A i.1) =
          ∑ i ∈ T, α i ^ j * e i * rsLocatorVector α A i :=
        Finset.sum_coe_sort T
          (fun i => α i ^ j * e i * rsLocatorVector α A i)
      _ = 0 := hrestricted
  have hequiv :
      (∑ i : T, α i.1 ^ j * e i.1 * rsLocatorVector α A i.1) =
        ∑ x : T.map α,
          x.1 ^ j * source x.1 * rsLocatorVectorOnSupport α A T x := by
    apply Fintype.sum_equiv (rsSupportEquiv α T)
    intro i
    rw [rsSupportEquiv_apply_val, rsLocatorVectorOnSupport_apply,
      hsource i.1 i.2]
  rw [← hequiv]
  exact hsubtype

theorem map_rsBarycentricDenominator
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (sigma : K ≃+* K)
    (hfixed : ∀ i, sigma (α i) = α i) (i : ι) :
    sigma (rsBarycentricDenominator α i) =
      rsBarycentricDenominator α i := by
  simp only [rsBarycentricDenominator, map_prod, map_sub, hfixed]

theorem map_rsAgreementLocator_eval
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (sigma : K ≃+* K)
    (hfixed : ∀ i, sigma (α i) = α i) (A : Finset ι) (i : ι) :
    sigma ((rsAgreementLocator α A).eval (α i)) =
      (rsAgreementLocator α A).eval (α i) := by
  simp only [rsAgreementLocator, Lagrange.eval_nodal, map_prod, map_sub,
    hfixed]

theorem map_rsLocatorVector
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (sigma : K ≃+* K)
    (hfixed : ∀ i, sigma (α i) = α i) (A : Finset ι) (i : ι) :
    sigma (rsLocatorVector α A i) = rsLocatorVector α A i := by
  simp only [rsLocatorVector, div_eq_mul_inv, map_mul, map_inv₀,
    map_rsAgreementLocator_eval α sigma hfixed,
    map_rsBarycentricDenominator α sigma hfixed]

theorem map_rsLocatorVectorOnSupport
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (sigma : K ≃+* K)
    (hfixed : ∀ i, sigma (α i) = α i) (A T : Finset ι)
    (x : T.map α) :
    sigma (rsLocatorVectorOnSupport α A T x) =
      rsLocatorVectorOnSupport α A T x := by
  exact map_rsLocatorVector α sigma hfixed A _

/-- Applying an automorphism to a vanishing moment gives a vanishing moment
for the mapped source, provided the nodes and weights are fixed. -/
theorem mapped_moment_eq_zero
    (sigma : K ≃+* K) (S : Finset K)
    (source target : K → K) (v : S → K) (j : ℕ)
    (hnode : ∀ x : S, sigma x.1 = x.1)
    (htarget : ∀ x : S, sigma (source x.1) = target x.1)
    (hvector : ∀ x : S, sigma (v x) = v x)
    (hmoment : ∑ x : S, x.1 ^ j * source x.1 * v x = 0) :
    ∑ x : S, x.1 ^ j * target x.1 * v x = 0 := by
  have hmapped := congrArg sigma hmoment
  simpa only [map_sum, map_mul, map_pow, map_zero, hnode, htarget,
    hvector] using hmapped

/-- The locator syndrome is stable under any coefficient automorphism which
fixes every evaluation point. -/
theorem rs_locator_support_mapped_moment_eq_zero
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (sigma : K ≃+* K)
    (hfixed : ∀ i, sigma (α i) = α i)
    (A T : Finset ι) (e : ι → K) (source : K → K) (P : K[X])
    (hsupport : ∀ i ∉ T, e i = 0)
    (hsource : ∀ i ∈ T, source (α i) = e i)
    (hagree : ∀ i ∈ A, P.eval (α i) = e i) (j : ℕ)
    (hdegree : (Finset.univ \ A).card + P.natDegree + j <
      Fintype.card ι - 1) :
    ∑ x : T.map α,
      x.1 ^ j * sigma (source x.1) *
        rsLocatorVectorOnSupport α A T x = 0 := by
  apply mapped_moment_eq_zero sigma (T.map α) source
    (fun x => sigma (source x)) (rsLocatorVectorOnSupport α A T) j
  · intro x
    obtain ⟨i, hiT, hix⟩ := Finset.mem_map.mp x.2
    rw [← hix, hfixed i]
  · intro x
    rfl
  · exact map_rsLocatorVectorOnSupport α sigma hfixed A T
  · exact rs_locator_support_moment_eq_zero
      α A T e source P hsupport hsource hagree j hdegree

/-- A sparse Reed--Solomon bad witness supplies the exact nonzero
transpose-kernel input expected by the mixed ordinary/Frobenius stack. -/
theorem mixedStack_transpose_ker_ne_bot_of_rs_locator
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (sigma : K ≃+* K)
    (hfixed : ∀ i, sigma (α i) = α i)
    (A T : Finset ι) (e : ι → K) (source : K → K) (P : K[X])
    (hsupport : ∀ i ∉ T, e i = 0)
    (hsource : ∀ i ∈ T, source (α i) = e i)
    (hagree : ∀ i ∈ A, P.eval (α i) = e i)
    (hintersects : ∃ i, i ∈ A ∧ i ∈ T)
    (c h : ℕ) (hhc : h ≤ c)
    (hdegreeRoom : (Finset.univ \ A).card + P.natDegree + c ≤
      Fintype.card ι - 1) :
    LinearMap.ker
      (mixedStackMatrix (T.map α) source (fun x => sigma (source x)) c h).transpose.mulVecLin ≠
        ⊥ := by
  apply mixedStack_transpose_ker_ne_bot_of_nonzero_moments
    (T.map α) source (fun x => sigma (source x)) c h
    (rsLocatorVectorOnSupport α A T)
  · exact rsLocatorVectorOnSupport_ne_zero α A T hintersects
  · intro j
    apply rs_locator_support_moment_eq_zero
      α A T e source P hsupport hsource hagree (j : ℕ)
    omega
  · intro j
    apply rs_locator_support_mapped_moment_eq_zero
      α sigma hfixed A T e source P hsupport hsource hagree (j : ℕ)
    omega

end ProximityPrize.SubmissionLower
