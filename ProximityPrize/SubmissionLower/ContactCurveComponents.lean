import ProximityPrize.Benchmark.TargetLower




/-!
# Actual minimal-prime components of a two-equation affine cut

Model label: gpt-5.

The component family is the finite set of actual minimal prime ideals of
(F,T), not a supplied list with desired properties. Every actual common
point lies on one of them. Krull's height theorem bounds each component's
height by two. A separate explicit chain of three prime kernels proves
that no such component is a single K-valued point of affine three-space.

No mixed intersection bound, field-degree bound, or submission is claimed.
-/

namespace ProximityPrize.SubmissionLower.ContactCurveComponents

noncomputable section

variable (K : Type) [Field K]

abbrev Poly3 := MvPolynomial (Fin 3) K

/-- Freeze the first n coordinates at the given actual point. -/
def freezeCoordinates (v : Fin 3 → K) (n : ℕ) : Poly3 K →ₐ[K] Poly3 K :=
  MvPolynomial.aeval (fun i => if i.val < n then MvPolynomial.C (v i) else MvPolynomial.X i)

def freezeKernel (v : Fin 3 → K) (n : ℕ) : Ideal (Poly3 K) :=
  RingHom.ker (freezeCoordinates K v n).toRingHom

instance freezeKernel_isPrime (v : Fin 3 → K) (n : ℕ) :
    (freezeKernel K v n).IsPrime :=
  RingHom.ker_isPrime (freezeCoordinates K v n).toRingHom

theorem freeze_comp (v : Fin 3 → K) (n m : ℕ) (hnm : n ≤ m) :
    (freezeCoordinates K v m).comp (freezeCoordinates K v n) =
      freezeCoordinates K v m := by
  ext i
  by_cases hi : i.val < n
  · simp [freezeCoordinates, hi, lt_of_lt_of_le hi hnm]
  · simp [freezeCoordinates, hi]

theorem freezeKernel_mono (v : Fin 3 → K) (n m : ℕ) (hnm : n ≤ m) :
    freezeKernel K v n ≤ freezeKernel K v m := by
  intro F hF
  change freezeCoordinates K v n F = 0 at hF
  change freezeCoordinates K v m F = 0
  have h := AlgHom.congr_fun (freeze_comp K v n m hnm) F
  change freezeCoordinates K v m (freezeCoordinates K v n F) =
    freezeCoordinates K v m F at h
  rw [hF, map_zero] at h
  exact h.symm

theorem coordinate_difference_ne_zero (i : Fin 3) (a : K) :
    (MvPolynomial.X i - MvPolynomial.C a : Poly3 K) ≠ 0 := by
  intro h
  have h' := congrArg (MvPolynomial.pderiv i) h
  simp at h'

theorem freezeKernel_lt_succ (v : Fin 3 → K) (n : ℕ) (hn : n < 3) :
    freezeKernel K v n < freezeKernel K v (n + 1) := by
  classical
  let i : Fin 3 := ⟨n, hn⟩
  let F : Poly3 K := MvPolynomial.X i - MvPolynomial.C (v i)
  have hmem : F ∈ freezeKernel K v (n + 1) := by
    change freezeCoordinates K v (n + 1) F = 0
    simp [freezeCoordinates, F, i]
  have hnot : F ∉ freezeKernel K v n := by
    change freezeCoordinates K v n F ≠ 0
    simpa [freezeCoordinates, F, i] using coordinate_difference_ne_zero K i (v i)
  apply lt_of_le_of_ne (freezeKernel_mono K v n (n + 1) (Nat.le_succ n))
  intro heq
  exact hnot (heq.symm ▸ hmem)

/-- The actual affine point kernel. -/
def pointKernel (v : Fin 3 → K) : Ideal (Poly3 K) :=
  RingHom.ker (MvPolynomial.aeval v).toRingHom

instance pointKernel_isPrime (v : Fin 3 → K) : (pointKernel K v).IsPrime :=
  RingHom.ker_isPrime (MvPolynomial.aeval v).toRingHom

theorem freezeKernel_three (v : Fin 3 → K) :
    freezeKernel K v 3 = pointKernel K v := by
  have h : freezeCoordinates K v 3 =
      (Algebra.ofId K (Poly3 K)).comp (MvPolynomial.aeval v) := by
    ext i
    simp [freezeCoordinates]
  apply Ideal.ext
  intro F
  change freezeCoordinates K v 3 F = 0 ↔ MvPolynomial.aeval v F = 0
  rw [h]
  change MvPolynomial.C (MvPolynomial.aeval v F) = 0 ↔ _
  simp

/-- Three explicit strict inclusions of prime kernels force height at
least three at every K-valued point. -/
theorem pointKernel_height_ge_three (v : Fin 3 → K) :
    (3 : ℕ∞) ≤ (pointKernel K v).height := by
  have h01 := Ideal.height_add_one_le_of_lt_of_isPrime
    (freezeKernel_lt_succ K v 0 (by decide))
  have h12 := Ideal.height_add_one_le_of_lt_of_isPrime
    (freezeKernel_lt_succ K v 1 (by decide))
  have h23 := Ideal.height_add_one_le_of_lt_of_isPrime
    (freezeKernel_lt_succ K v 2 (by decide))
  have h1 : (1 : ℕ∞) ≤ (freezeKernel K v 1).height := by
    calc
      1 = (0 : ℕ∞) + 1 := by simp
      _ ≤ (freezeKernel K v 0).height + 1 := by gcongr; exact zero_le
      _ ≤ (freezeKernel K v 1).height := h01
  have h2 : (2 : ℕ∞) ≤ (freezeKernel K v 2).height := by
    calc
      2 = (1 : ℕ∞) + 1 := by norm_num
      _ ≤ (freezeKernel K v 1).height + 1 := by gcongr
      _ ≤ (freezeKernel K v 2).height := h12
  rw [← freezeKernel_three K v]
  calc
    3 = (2 : ℕ∞) + 1 := by norm_num
    _ ≤ (freezeKernel K v 2).height + 1 := by gcongr
    _ ≤ (freezeKernel K v 3).height := h23

def cutIdeal (F T : Poly3 K) : Ideal (Poly3 K) := Ideal.span {F, T}

def componentSet (F T : Poly3 K) : Set (Ideal (Poly3 K)) :=
  (cutIdeal K F T).minimalPrimes

theorem componentSet_finite (F T : Poly3 K) : (componentSet K F T).Finite :=
  Ideal.finite_minimalPrimes_of_isNoetherianRing _ _

def componentFamily (F T : Poly3 K) : Finset (Ideal (Poly3 K)) :=
  (componentSet_finite K F T).toFinset

@[simp] theorem mem_componentFamily (F T : Poly3 K) (P : Ideal (Poly3 K)) :
    P ∈ componentFamily K F T ↔ P ∈ (cutIdeal K F T).minimalPrimes :=
  Set.Finite.mem_toFinset _

theorem component_isPrime (F T : Poly3 K) (P : Ideal (Poly3 K))
    (hP : P ∈ componentFamily K F T) : P.IsPrime :=
  ((mem_componentFamily K F T P).mp hP).isPrime

theorem cutIdeal_le_component (F T : Poly3 K) (P : Ideal (Poly3 K))
    (hP : P ∈ componentFamily K F T) : cutIdeal K F T ≤ P :=
  ((mem_componentFamily K F T P).mp hP).le

theorem component_height_le_two (F T : Poly3 K) (P : Ideal (Poly3 K))
    (hP : P ∈ componentFamily K F T) : P.height ≤ 2 := by
  classical
  have hm : P ∈ (Ideal.span ({F, T} : Finset (Poly3 K))).minimalPrimes := by
    simpa only [Finset.coe_insert, Finset.coe_singleton, cutIdeal] using
      (mem_componentFamily K F T P).mp hP
  have hh := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hm
  have hc : ({F, T} : Finset (Poly3 K)).card ≤ 2 :=
    (Finset.card_insert_le F {T}).trans (by simp)
  exact hh.trans (by exact_mod_cast hc)

/-- Actual common roots are covered by actual minimal primes. -/
theorem exists_component_of_common_point
    (F T : Poly3 K) (v : Fin 3 → K)
    (hF : MvPolynomial.eval v F = 0) (hT : MvPolynomial.eval v T = 0) :
    ∃ P ∈ componentFamily K F T, P ≤ pointKernel K v := by
  have hcut : cutIdeal K F T ≤ pointKernel K v := by
    apply Ideal.span_le.mpr
    intro A hA
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with rfl | rfl
    · exact hF
    · exact hT
  obtain ⟨P, hP, hle⟩ := Ideal.exists_minimalPrimes_le hcut
  exact ⟨P, (mem_componentFamily K F T P).mpr hP, hle⟩

/-- None of the actual two-equation components can collapse to a single
affine K-valued point: its height is at most two, while that point has
height at least three. -/
theorem component_ne_pointKernel
    (F T : Poly3 K) (P : Ideal (Poly3 K))
    (hP : P ∈ componentFamily K F T) (v : Fin 3 → K) :
    P ≠ pointKernel K v := by
  intro heq
  have hle := component_height_le_two K F T P hP
  rw [heq] at hle
  have hbad : (3 : ℕ∞) ≤ 2 := (pointKernel_height_ge_three K v).trans hle
  norm_num at hbad

end

end ProximityPrize.SubmissionLower.ContactCurveComponents

#print axioms ProximityPrize.SubmissionLower.ContactCurveComponents.freeze_comp
#print axioms ProximityPrize.SubmissionLower.ContactCurveComponents.freezeKernel_mono
#print axioms ProximityPrize.SubmissionLower.ContactCurveComponents.freezeKernel_lt_succ
#print axioms ProximityPrize.SubmissionLower.ContactCurveComponents.pointKernel_height_ge_three
#print axioms ProximityPrize.SubmissionLower.ContactCurveComponents.componentSet_finite
#print axioms ProximityPrize.SubmissionLower.ContactCurveComponents.component_isPrime
#print axioms ProximityPrize.SubmissionLower.ContactCurveComponents.cutIdeal_le_component
#print axioms ProximityPrize.SubmissionLower.ContactCurveComponents.component_height_le_two
#print axioms ProximityPrize.SubmissionLower.ContactCurveComponents.exists_component_of_common_point
#print axioms ProximityPrize.SubmissionLower.ContactCurveComponents.component_ne_pointKernel
