import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactTranslation

/-!
# Universal specialization for every contact-kernel member

This module packages the parameter-generic front end needed when several
contact interpolants are selected from the same kernel.  It does not choose a
kernel member or instantiate any target arithmetic: every supplied array in
the kernel gives the translated contact divisibilities, and hence universal
specialization zero under the usual agreement and degree hypotheses.
-/

namespace ProximityPrize.SubmissionLower.ContactKernelMemberUniversality

open ProximityPrize.Benchmark
open ContactInterpolation ContactRankKernel ContactTranslation

noncomputable section

variable (K : Type*) [Field K]

/-- Kernel membership is exactly the family of explicit contact equations. -/
theorem block_equations_of_mem_ker
    {I : Type*} [Fintype I]
    (D w L s m : ℕ) (nodes u0 u1 : I → K)
    (theta : CoefficientIndex D w L s → K)
    (htheta : theta ∈ LinearMap.ker
      (constraintMap K D w L s m nodes u0 u1)) :
    ∀ (i : I) (r : Fin m),
      contactJet K (m - r.val)
        ((extractBlock K D w L s (nodes i) (u0 i) (u1 i) r.val theta) :
          Poly K) = 0 := by
  intro i r
  have hzero : constraintMap K D w L s m nodes u0 u1 theta = 0 :=
    LinearMap.mem_ker.mp htheta
  have happ := congrArg
    (fun target : GlobalTarget K I m L s => ((target i r) : Poly K)) hzero
  change contactJet K (m - r.val)
    ((extractBlock K D w L s (nodes i) (u0 i) (u1 i) r.val theta) :
      Poly K) = 0 at happ
  exact happ

/-- Every kernel member has the full translated contact divisibility at every
node.  No nonzero or dimension hypothesis is needed for this statement. -/
theorem translated_contact_of_mem_ker
    {I : Type*} [Fintype I]
    (D w L s m : ℕ) (nodes u0 u1 : I → K)
    (theta : CoefficientIndex D w L s → K)
    (htheta : theta ∈ LinearMap.ker
      (constraintMap K D w L s m nodes u0 u1)) :
    ∀ (i : I) (r : ℕ),
      slopeDifference K ^ (m - r) ∣
        (homogenizedTranslation K (nodes i) (u0 i) (u1 i)
          (reconstruct K D w L s theta)).coeff r := by
  intro i r
  rw [translation_reconstruct_coeff]
  exact all_blocks_divisible_of_equations K D w L s m
    (nodes i) (u0 i) (u1 i) theta
    (block_equations_of_mem_ker K D w L s m nodes u0 u1 theta htheta i) r

/-- The flexible many-root conclusion.  The numerical interface is only the
natural capacity inequality `D ≤ m * support.card`. -/
theorem specialization_eq_zero_of_mem_ker
    [DecidableEq K] {I : Type*} [Fintype I] [DecidableEq I]
    (D w L s m : ℕ) (nodes : I ↪ K) (u0 u1 : I → K)
    (theta : CoefficientIndex D w L s → K)
    (htheta : theta ∈ LinearMap.ker
      (constraintMap K D w L s m nodes u0 u1))
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hD : 0 < D) (hP : P.natDegree ≤ w)
    (hcapacity : D ≤ m * support.card)
    (hvalues : ∀ i ∈ support,
      P.eval (nodes i) = u0 i + gamma * u1 i) :
    specialization K P gamma (reconstruct K D w L s theta) = 0 := by
  apply specialization_eq_zero_of_contact_and_degree K
    (reconstruct K D w L s theta) P gamma nodes u0 u1 support m
  · intro i hi r
    exact translated_contact_of_mem_ker K D w L s m nodes u0 u1 theta
      htheta i r
  · exact hvalues
  · have hdegree := specialization_natDegree_lt K D w L s
      (reconstruct K D w L s theta) P gamma hD
      (reconstruct_mem_globalCoefficientBox K D w L s theta) hP
    exact hdegree.trans_le hcapacity

/-- Standard agreement-count form for profiles with weighted cap `D = m*a`. -/
theorem specialization_eq_zero_of_agreements
    [DecidableEq K] {I : Type*} [Fintype I] [DecidableEq I]
    (D w L s m a : ℕ) (nodes : I ↪ K) (u0 u1 : I → K)
    (theta : CoefficientIndex D w L s → K)
    (htheta : theta ∈ LinearMap.ker
      (constraintMap K D w L s m nodes u0 u1))
    (hD : 0 < D) (hDa : D = m * a)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hP : P.natDegree ≤ w) (hcard : a ≤ support.card)
    (hvalues : ∀ i ∈ support,
      P.eval (nodes i) = u0 i + gamma * u1 i) :
    specialization K P gamma (reconstruct K D w L s theta) = 0 := by
  apply specialization_eq_zero_of_mem_ker K D w L s m nodes u0 u1 theta
    htheta P gamma support hD hP
  · rw [hDa]
    exact Nat.mul_le_mul_left m hcard
  · exact hvalues

/-- A nonzero kernel array reconstructs to a nonzero boxed polynomial, and
that same polynomial vanishes after every admissible specialization. -/
theorem nonzero_kernel_member_universal
    [DecidableEq K] {I : Type*} [Fintype I] [DecidableEq I]
    (D w L s m a : ℕ) (nodes : I ↪ K) (u0 u1 : I → K)
    (theta : CoefficientIndex D w L s → K)
    (htheta0 : theta ≠ 0)
    (htheta : theta ∈ LinearMap.ker
      (constraintMap K D w L s m nodes u0 u1))
    (hD : 0 < D) (hDa : D = m * a) :
    reconstruct K D w L s theta ≠ 0 ∧
      reconstruct K D w L s theta ∈ globalCoefficientBox K D w L s ∧
      ∀ (gamma : K) (P : Polynomial K) (support : Finset I),
        P.natDegree ≤ w → a ≤ support.card →
        (∀ i ∈ support,
          P.eval (nodes i) = u0 i + gamma * u1 i) →
        specialization K P gamma (reconstruct K D w L s theta) = 0 := by
  refine ⟨reconstruct_ne_zero K D w L s theta htheta0,
    reconstruct_mem_globalCoefficientBox K D w L s theta, ?_⟩
  intro gamma P support hP hcard hvalues
  exact specialization_eq_zero_of_agreements K D w L s m a nodes u0 u1
    theta htheta hD hDa P gamma support hP hcard hvalues

end

end ProximityPrize.SubmissionLower.ContactKernelMemberUniversality
