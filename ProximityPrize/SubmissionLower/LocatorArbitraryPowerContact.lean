import ProximityPrize.SubmissionLower.LocatorArbitraryPowerAvoidance

/-! Packed from ProximityPrize.SubmissionLower.LocatorArbitraryPowerContact. -/
section PackedLocator_LocatorArbitraryPowerContact

/-!
# Arbitrary-order locator contact and power extraction

This module is the order-independent consumer for
`LocatorArbitraryPowerAvoidance`.  It replaces the explicitly unrolled
second-through-tenth derivative arguments by three reusable facts:

* an `R`-derivative lowers contact order by at most one;
* a nonzero `j`-fold `R`-derivative loses at least `j` times the `R` weight;
* at derivative order `j`, the surviving term of `dR^[j] (F^j * Q)` is
  `j! * Q * (dR F)^j` after specializing on `F = 0`.
-/

namespace ProximityPrize.SubmissionLower.LocatorArbitraryPowerContact

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

variable {K I : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

abbrev P4 (K : Type*) [Field K] := MvPolynomial (Fin 4) K

/-- The `j`-fold derivative in the received-coordinate variable. -/
def iteratePderivR (j : ℕ) (Q : P4 K) : P4 K :=
  (fun H : P4 K => MvPolynomial.pderiv (2 : Fin 4) H)^[j] Q

@[simp] theorem iteratePderivR_zero (Q : P4 K) :
    iteratePderivR 0 Q = Q := rfl

theorem iteratePderivR_succ (j : ℕ) (Q : P4 K) :
    iteratePderivR (j + 1) Q =
      MvPolynomial.pderiv (2 : Fin 4) (iteratePderivR j Q) := by
  simp only [iteratePderivR, Function.iterate_succ_apply']

@[simp] theorem iteratePderivR_zero_poly (j : ℕ) :
    iteratePderivR (K := K) j 0 = 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [iteratePderivR_succ, ih, map_zero]

/-- Contact order falls by at most one at every received-coordinate
derivative, uniformly in the number of iterations. -/
theorem contactAtLeast_iteratePderivR
    (x u0 u1 : K) (m j : ℕ) (Q : P4 K)
    (hQ : ContactOrderBridge.ContactAtLeast K x u0 u1 m Q) :
    ContactOrderBridge.ContactAtLeast K x u0 u1 (m - j)
      (iteratePderivR j Q) := by
  induction j with
  | zero => simpa only [iteratePderivR_zero, Nat.sub_zero] using hQ
  | succ j ih =>
      rw [iteratePderivR_succ]
      have hnext := ContactOrderBridge.contactAtLeast_pderiv_R
        K x u0 u1 (m - j) (iteratePderivR j Q) ih
      simpa only [Nat.sub_sub] using hnext

/-- If a successor iterate is nonzero, its immediate predecessor is nonzero. -/
theorem iteratePderivR_ne_zero_of_succ
    (Q : P4 K) (j : ℕ)
    (hne : iteratePderivR (j + 1) Q ≠ 0) :
    iteratePderivR j Q ≠ 0 := by
  intro hz
  apply hne
  rw [iteratePderivR_succ, hz, map_zero]

/-- A nonzero `j`-fold received-coordinate derivative pays `j` copies of
the received-coordinate weight.  This is the generic replacement for all
manually chained `pderiv_R_weight_add_le` calculations. -/
theorem iteratePderivR_weight_add_le
    (weights : Fin 4 → ℕ) (Q : P4 K) (j : ℕ)
    (hne : iteratePderivR j Q ≠ 0) :
    wt weights (iteratePderivR j Q) + j * weights 2 ≤ wt weights Q := by
  induction j with
  | zero =>
      simp only [iteratePderivR_zero, Nat.zero_mul, Nat.add_zero]
      exact le_rfl
  | succ j ih =>
      have hprev : iteratePderivR j Q ≠ 0 :=
        iteratePderivR_ne_zero_of_succ Q j (by
          simpa only [Nat.succ_eq_add_one] using hne)
      have hstepNe :
          MvPolynomial.pderiv (2 : Fin 4) (iteratePderivR j Q) ≠ 0 := by
        simpa only [Nat.succ_eq_add_one, iteratePderivR_succ] using hne
      have hstep := LocatorContact.pderiv_R_weight_add_le
        weights (iteratePderivR j Q) hstepNe
      calc
        wt weights (iteratePderivR (Nat.succ j) Q) +
              Nat.succ j * weights 2 =
            (wt weights (MvPolynomial.pderiv (2 : Fin 4)
              (iteratePderivR j Q)) + weights 2) + j * weights 2 := by
              simp only [Nat.succ_eq_add_one, iteratePderivR_succ,
                Nat.add_mul, one_mul]
              ac_rfl
        _ ≤ wt weights (iteratePderivR j Q) + j * weights 2 :=
          Nat.add_le_add_right hstep _
        _ ≤ wt weights Q := ih hprev

theorem iteratePderivR_weight_le_sub
    (weights : Fin 4 → ℕ) (Q : P4 K) (j d : ℕ)
    (hne : iteratePderivR j Q ≠ 0)
    (hQ : wt weights Q ≤ d) :
    wt weights (iteratePderivR j Q) ≤ d - j * weights 2 := by
  exact Nat.le_sub_of_add_le
    ((iteratePderivR_weight_add_le weights Q j hne).trans hQ)

section KernelVanishing

variable [Fintype I]
local instance : DecidableEq I := Classical.decEq I

/-- The generic contact/degree vanishing theorem at derivative order `j`.
The capacity hypothesis is exactly the one used by each previously unrolled
fixed-order theorem. -/
theorem specialization_iteratePderivR_eq_zero_of_kernel_low_box
    (j D Dlow w L s m : ℕ) (nodes : I ↪ K) (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
    (hlow : reconstruct K D w L s v.1 ∈
      globalCoefficientBox K Dlow w L s)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hj : 1 ≤ j) (hw : 1 ≤ w) (hP : P.natDegree ≤ w)
    (hcapacity : Dlow ≤ (m - j) * support.card + j * (w - 1))
    (hvalues : ∀ i ∈ support,
      P.eval (nodes i) = u0 i + gamma * u1 i) :
    RCN319.specialization K P gamma
      (iteratePderivR j (reconstruct K D w L s v.1)) = 0 := by
  classical
  cases j with
  | zero => omega
  | succ k =>
      let H := reconstruct K D w L s v.1
      by_contra hne
      have hfinal : iteratePderivR (Nat.succ k) H ≠ 0 := by
        intro hz
        apply hne
        rw [hz, map_zero]
      have hprev : iteratePderivR k H ≠ 0 := by
        apply iteratePderivR_ne_zero_of_succ H k
        simpa only [Nat.succ_eq_add_one] using hfinal
      have hH : H ≠ 0 := by
        intro hz
        apply hfinal
        rw [hz, iteratePderivR_zero_poly]
      have hDlow : 0 < Dlow := by
        obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hH
        have h := (hlow hd).2.2
        omega
      have hHweight : wt (contactWeights w) H ≤ Dlow - 1 :=
        ((mem_flagGlobalCoefficientBox_iff H Dlow w L s hDlow).mp hlow).2.2
      have hprevWeight :
          wt (contactWeights w) (iteratePderivR k H) ≤
            Dlow - 1 - k * (w - 1) := by
        have hbound := iteratePderivR_weight_le_sub
          (contactWeights w) H k (Dlow - 1) hprev hHweight
        change wt (contactWeights w) (iteratePderivR k H) ≤
          Dlow - 1 - k * (w - 1) at hbound
        exact hbound
      have hregular : RCN319.specialization K P gamma
          (MvPolynomial.pderiv (2 : Fin 4) (iteratePderivR k H)) ≠ 0 := by
        simpa only [Nat.succ_eq_add_one, iteratePderivR_succ] using hne
      have hdegree := ContactOrderBridge.specialized_R_derivative_degree K
        (iteratePderivR k H) P gamma w
        (Dlow - 1 - k * (w - 1)) hP hprevWeight hregular
      have hdegreeStrict :
          (RCN122.specialization K P gamma
            (iteratePderivR (Nat.succ k) H)).natDegree <
              (m - Nat.succ k) * support.card := by
        rw [Nat.succ_eq_add_one, iteratePderivR_succ]
        rw [RCN101.specialization_eq_ordinary]
        rw [RCN101.specialization_eq_ordinary] at hdegree
        have hkc : k * (w - 1) ≤ Dlow - 1 := by
          by_contra hnot
          have hlt : Dlow - 1 < k * (w - 1) := Nat.lt_of_not_ge hnot
          have hzero : Dlow - 1 - k * (w - 1) = 0 :=
            Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
          rw [hzero] at hdegree
          have hwOne : w - 1 = 0 := by omega
          rw [hwOne, Nat.mul_zero] at hlt
          omega
        have hsplit :
            (Dlow - 1 - k * (w - 1)) + k * (w - 1) = Dlow - 1 :=
          Nat.sub_add_cancel hkc
        have hwSplit : w - 1 + 1 = w := Nat.sub_add_cancel hw
        simp only [Nat.succ_eq_add_one, Nat.add_mul, one_mul] at hcapacity
        omega
      have hcontact : ∀ i ∈ support, ∀ r : ℕ,
          slopeDifference K ^ (m - Nat.succ k - r) ∣
            (RCN122.homogenizedTranslation K (nodes i) (u0 i) (u1 i)
              (iteratePderivR (Nat.succ k) H)).coeff r := by
        intro i _hi
        apply (ContactOrderBridge.contactAtLeast_iff_block_divisibility
          K (nodes i) (u0 i) (u1 i) (m - Nat.succ k) _).mp
        exact contactAtLeast_iteratePderivR
          (nodes i) (u0 i) (u1 i) m (Nat.succ k) H
          (ContactOrderBridge.contactAtLeast_of_mem_kernel
            K D w L s m nodes u0 u1 v.1 v.2 i)
      have hz := RCN122.specialization_eq_zero_of_contact_and_degree K
        (iteratePderivR (Nat.succ k) H) P gamma nodes u0 u1 support
        (m - Nat.succ k) hcontact hvalues hdegreeStrict
      apply hne
      simpa only [H, RCN101.specialization_eq_ordinary] using hz

end KernelVanishing

/-- Local factorial divisibility criterion, kept here because `CH`'s
corresponding helper is intentionally private. -/
private theorem prime_dvd_factorial_local : ∀ {n p : ℕ},
    p.Prime → (p ∣ n.factorial ↔ p ≤ n)
  | 0, _, hp => iff_of_false hp.not_dvd_one (not_le_of_gt hp.pos)
  | n + 1, p, hp => by
      rw [Nat.factorial_succ, hp.dvd_mul, prime_dvd_factorial_local hp]
      exact ⟨fun h => h.elim (Nat.le_of_dvd (Nat.succ_pos _)) Nat.le_succ_of_le,
        fun h => (_root_.lt_or_eq_of_le h).elim
          (Or.inr ∘ Nat.le_of_lt_succ) fun h => Or.inl <| by rw [h]⟩

/-- A prime characteristic larger than `j` does not annihilate `j!`. -/
theorem factorial_ne_zero_of_lt_char
    (p j : ℕ) [CharP K p] (hp : p.Prime) (hj : j < p) :
    (j.factorial : K) ≠ 0 := by
  intro hz
  have hdvd : p ∣ j.factorial :=
    (CharP.cast_eq_zero_iff K p j.factorial).mp hz
  exact (not_le_of_gt hj) ((prime_dvd_factorial_local hp).mp hdvd)

/-- Generic extraction of the terminal quotient from a `j`th derivative.
After specializing on `F = 0`, `RCN324.iterate_pow_mul_expansion` kills its
error term and leaves `j! * Q * (dR F)^j`. -/
theorem specialization_eq_zero_of_iteratePderivR_power_product
    (j : ℕ) (P : Polynomial K) (gamma : K) (F Q : P4 K)
    (hfactorial : (j.factorial : K) ≠ 0)
    (hFzero : RCN319.specialization K P gamma F = 0)
    (hregular : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hpower : RCN319.specialization K P gamma
      (iteratePderivR j (F ^ j * Q)) = 0) :
    RCN319.specialization K P gamma Q = 0 := by
  obtain ⟨error, herror⟩ := RCN324.iterate_pow_mul_expansion
    (MvPolynomial.pderiv (2 : Fin 4)) F Q j j le_rfl
  have hexpansion :
      iteratePderivR j (F ^ j * Q) =
        (j.descFactorial j : P4 K) * F ^ (j - j) * Q *
            (MvPolynomial.pderiv (2 : Fin 4) F) ^ j +
          F ^ (j - j + 1) * error := by
    simpa only [iteratePderivR] using herror
  rw [hexpansion] at hpower
  have hmul :
      (j.factorial : Polynomial K) *
          RCN319.specialization K P gamma Q *
            (RCN319.specialization K P gamma
              (MvPolynomial.pderiv (2 : Fin 4) F)) ^ j = 0 := by
    simpa only [Nat.descFactorial_self, Nat.sub_self, pow_zero, one_mul, mul_one,
      zero_add, pow_one, map_add, map_mul, map_pow, map_natCast,
      map_one, hFzero, zero_mul, add_zero] using hpower
  have hfactorialPoly : (j.factorial : Polynomial K) ≠ 0 := by
    intro hz
    apply hfactorial
    have heval := congrArg (Polynomial.eval 0) hz
    simpa using heval
  have hcoef :
      (j.factorial : Polynomial K) *
          (RCN319.specialization K P gamma
            (MvPolynomial.pderiv (2 : Fin 4) F)) ^ j ≠ 0 :=
    mul_ne_zero hfactorialPoly (pow_ne_zero j hregular)
  have hmul' :
      ((j.factorial : Polynomial K) *
          (RCN319.specialization K P gamma
            (MvPolynomial.pderiv (2 : Fin 4) F)) ^ j) *
        RCN319.specialization K P gamma Q = 0 := by
    calc
      _ = (j.factorial : Polynomial K) *
          RCN319.specialization K P gamma Q *
            (RCN319.specialization K P gamma
              (MvPolynomial.pderiv (2 : Fin 4) F)) ^ j := by ring
      _ = 0 := hmul
  exact (mul_eq_zero.mp hmul').resolve_left hcoef

end

end ProximityPrize.SubmissionLower.LocatorArbitraryPowerContact
end PackedLocator_LocatorArbitraryPowerContact

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier07 : True := by trivial
end ProximityPrize.SubmissionLower

