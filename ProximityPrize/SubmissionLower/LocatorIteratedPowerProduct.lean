import ProximityPrize.SubmissionLower.LocatorSeventhPowerAvoidance

namespace ProximityPrize.SubmissionLower.LocatorIteratedPowerProduct

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260 RCN319
open LocatorLowQuotient LocatorCoprimeQuotient

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000

variable {K : Type*} [Field K]

/-- Iterated derivative in the residual `R` coordinate. -/
def pderivRIter : ℕ → MvPolynomial (Fin 4) K → MvPolynomial (Fin 4) K
  | 0, H => H
  | n + 1, H => MvPolynomial.pderiv (2 : Fin 4) (pderivRIter n H)

/-- The quotient left after differentiating `F ^ n * Q` exactly `k` times and
factoring the power `F ^ (n-k)`.  Encoding the recurrence once avoids the
large expanded derivative terms previously generated separately for each
order. -/
def powerCofactor (F : MvPolynomial (Fin 4) K) (n : ℕ) :
    ℕ → MvPolynomial (Fin 4) K → MvPolynomial (Fin 4) K
  | 0, Q => Q
  | k + 1, Q =>
      ((n - k : ℕ) : MvPolynomial (Fin 4) K) *
          MvPolynomial.pderiv (2 : Fin 4) F * powerCofactor F n k Q +
        F * MvPolynomial.pderiv (2 : Fin 4) (powerCofactor F n k Q)

theorem pderivRIter_power_factor (F Q : MvPolynomial (Fin 4) K)
    (n k : ℕ) (hk : k ≤ n) :
    pderivRIter k (F ^ n * Q) = F ^ (n - k) * powerCofactor F n k Q := by
  induction k with
  | zero => simp [pderivRIter, powerCofactor]
  | succ k ih =>
      have hklt : k < n := Nat.lt_of_succ_le hk
      have hkle : k ≤ n := Nat.le_of_lt hklt
      have hsub : n - k = (n - (k + 1)) + 1 := by omega
      rw [pderivRIter, ih hkle]
      simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
        powerCofactor]
      rw [hsub, pow_succ]
      push_cast
      ring

theorem map_powerCofactor
    (phi : MvPolynomial (Fin 4) K →+* Polynomial K)
    (F Q : MvPolynomial (Fin 4) K) (n k : ℕ)
    (hF : phi F = 0) :
    phi (powerCofactor F n k Q) =
      (n.descFactorial k : Polynomial K) *
        (phi (MvPolynomial.pderiv (2 : Fin 4) F)) ^ k * phi Q := by
  induction k with
  | zero => simp [powerCofactor]
  | succ k ih =>
      rw [powerCofactor, map_add, map_mul, map_mul, map_mul,
        map_natCast, ih, hF, zero_mul, add_zero, Nat.descFactorial_succ]
      push_cast
      rw [pow_succ]
      ring

theorem map_pderivRIter_power_self
    (phi : MvPolynomial (Fin 4) K →+* Polynomial K)
    (F Q : MvPolynomial (Fin 4) K) (n : ℕ)
    (hF : phi F = 0) :
    phi (pderivRIter n (F ^ n * Q)) =
      (n.factorial : Polynomial K) *
        (phi (MvPolynomial.pderiv (2 : Fin 4) F)) ^ n * phi Q := by
  rw [pderivRIter_power_factor F Q n n (le_refl n), Nat.sub_self, pow_zero,
    one_mul, map_powerCofactor phi F Q n n hF, Nat.descFactorial_self]

theorem specialization_eq_zero_of_pderivRIter_power
    (P : Polynomial K) (gamma : K) (F Q : MvPolynomial (Fin 4) K) (n : ℕ)
    (hfactorial : (n.factorial : K) ≠ 0)
    (hFzero : RCN319.specialization K P gamma F = 0)
    (hregular : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hiter : RCN319.specialization K P gamma
      (pderivRIter n (F ^ n * Q)) = 0) :
    RCN319.specialization K P gamma Q = 0 := by
  have hfactorialPoly : (n.factorial : Polynomial K) ≠ 0 := by
    intro hz
    apply hfactorial
    have heval := congrArg (Polynomial.eval 0) hz
    simpa using heval
  have hmul : (n.factorial : Polynomial K) *
      (RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F)) ^ n *
      RCN319.specialization K P gamma Q = 0 := by
    have hformula := map_pderivRIter_power_self
      (RCN319.specialization K P gamma).toRingHom F Q n hFzero
    have hformula' : RCN319.specialization K P gamma
        (pderivRIter n (F ^ n * Q)) =
        (n.factorial : Polynomial K) *
          (RCN319.specialization K P gamma
            (MvPolynomial.pderiv (2 : Fin 4) F)) ^ n *
          RCN319.specialization K P gamma Q := hformula
    rw [← hformula']
    exact hiter
  have hcoef : (n.factorial : Polynomial K) *
      (RCN319.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F)) ^ n ≠ 0 :=
    mul_ne_zero hfactorialPoly (pow_ne_zero n hregular)
  exact (mul_eq_zero.mp hmul).resolve_left hcoef

theorem pderivRIter_ne_zero_of_le {a b : ℕ}
    (hab : a ≤ b) (H : MvPolynomial (Fin 4) K)
    (h : pderivRIter b H ≠ 0) : pderivRIter a H ≠ 0 := by
  induction b with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      exact h
  | succ b ih =>
      by_cases hab' : a ≤ b
      · apply ih hab'
        intro hz
        apply h
        simp [pderivRIter, hz]
      · have : a = b + 1 := by omega
        subst a
        exact h

theorem pderivRIter_weight_add_le {w : ℕ} (n : ℕ)
    (H : MvPolynomial (Fin 4) K) (h : pderivRIter n H ≠ 0) :
    wt (contactWeights w) (pderivRIter n H) + n * (w - 1) ≤
      wt (contactWeights w) H := by
  induction n with
  | zero => simp [pderivRIter]
  | succ n ih =>
      have hn : pderivRIter n H ≠ 0 :=
        pderivRIter_ne_zero_of_le (Nat.le_succ n) H h
      have hwgt := LocatorContact.pderiv_R_weight_add_le
        (contactWeights w) (pderivRIter n H) h
      have hi := ih hn
      change wt (contactWeights w)
          (MvPolynomial.pderiv (2 : Fin 4) (pderivRIter n H)) + (w - 1) ≤
        wt (contactWeights w) (pderivRIter n H) at hwgt
      simp only [pderivRIter]
      rw [Nat.add_mul, Nat.one_mul]
      omega

theorem contactAtLeast_pderivRIter
    (x u0 u1 : K) (m n : ℕ) (H : MvPolynomial (Fin 4) K)
    (h : ContactOrderBridge.ContactAtLeast K x u0 u1 m H) :
    ContactOrderBridge.ContactAtLeast K x u0 u1 (m - n) (pderivRIter n H) := by
  induction n with
  | zero => simpa [pderivRIter] using h
  | succ n ih =>
      have hs := ContactOrderBridge.contactAtLeast_pderiv_R
        K x u0 u1 (m - n) (pderivRIter n H) ih
      simpa only [pderivRIter, Nat.sub_sub, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hs

section KernelDerivative

variable {I : Type*} [Fintype I]
local instance : DecidableEq I := Classical.decEq I

theorem specialization_pderivRIter_eq_zero_of_kernel_low_box
    (D Dlow w L s m n : ℕ) (hn : 1 ≤ n)
    (nodes : I ↪ K) (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
    (hlow : reconstruct K D w L s v.1 ∈ globalCoefficientBox K Dlow w L s)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hw : 1 ≤ w) (hP : P.natDegree ≤ w)
    (hcapacity : Dlow ≤ (m - n) * support.card + n * (w - 1))
    (hvalues : ∀ i ∈ support, P.eval (nodes i) = u0 i + gamma * u1 i) :
    RCN319.specialization K P gamma
      (pderivRIter n (reconstruct K D w L s v.1)) = 0 := by
  classical
  let H := reconstruct K D w L s v.1
  by_contra hne
  have hdern : pderivRIter n H ≠ 0 := by
    intro hz
    apply hne
    rw [hz, map_zero]
  have hH : H ≠ 0 := by
    have h := pderivRIter_ne_zero_of_le (a := 0) (b := n)
      (Nat.zero_le n) H hdern
    simpa only [pderivRIter] using h
  have hprev : pderivRIter (n - 1) H ≠ 0 :=
    pderivRIter_ne_zero_of_le (Nat.sub_le n 1) H hdern
  have hDlow : 0 < Dlow := by
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hH
    have h := (hlow hd).2.2
    omega
  have hHweight : wt (contactWeights w) H ≤ Dlow - 1 :=
    ((mem_flagGlobalCoefficientBox_iff H Dlow w L s hDlow).mp hlow).2.2
  have hiterWeight := pderivRIter_weight_add_le (w := w) (n - 1) H hprev
  have hprevWeight : wt (contactWeights w) (pderivRIter (n - 1) H) ≤
      Dlow - 1 - (n - 1) * (w - 1) := by omega
  have hsucc : n - 1 + 1 = n := by omega
  have hiterSucc : pderivRIter n H =
      MvPolynomial.pderiv (2 : Fin 4) (pderivRIter (n - 1) H) := by
    rw [← hsucc]
    rfl
  have hne' : RCN122.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) (pderivRIter (n - 1) H)) ≠ 0 := by
    simpa only [← hiterSucc, RCN101.specialization_eq_ordinary] using hne
  have hdegree := ContactOrderBridge.specialized_R_derivative_degree K
    (pderivRIter (n - 1) H) P gamma w
    (Dlow - 1 - (n - 1) * (w - 1)) hP hprevWeight hne'
  have hdegreeStrict :
      (RCN122.specialization K P gamma (pderivRIter n H)).natDegree <
        (m - n) * support.card := by
    rw [hiterSucc, RCN101.specialization_eq_ordinary]
    rw [RCN101.specialization_eq_ordinary] at hdegree
    have hnform : n = (n - 1) + 1 := by omega
    have hnmul : n * (w - 1) =
        (n - 1) * (w - 1) + (w - 1) := by
      calc
        n * (w - 1) = ((n - 1) + 1) * (w - 1) :=
          congrArg (fun t => t * (w - 1)) hnform
        _ = (n - 1) * (w - 1) + (w - 1) := by
          rw [Nat.add_mul, Nat.one_mul]
    omega
  have hcontact : ∀ i ∈ support, ∀ r : ℕ,
      slopeDifference K ^ (m - n - r) ∣
        (RCN122.homogenizedTranslation K (nodes i) (u0 i) (u1 i)
          (pderivRIter n H)).coeff r := by
    intro i _
    apply (ContactOrderBridge.contactAtLeast_iff_block_divisibility
      K (nodes i) (u0 i) (u1 i) (m - n) _).mp
    exact contactAtLeast_pderivRIter (K := K) (nodes i) (u0 i) (u1 i) m n H
      (ContactOrderBridge.contactAtLeast_of_mem_kernel
        K D w L s m nodes u0 u1 v.1 v.2 i)
  have hz := RCN122.specialization_eq_zero_of_contact_and_degree K
    (pderivRIter n H) P gamma nodes u0 u1 support (m - n)
    hcontact hvalues hdegreeStrict
  apply hne
  simpa only [H, RCN101.specialization_eq_ordinary] using hz

end KernelDerivative

end

end ProximityPrize.SubmissionLower.LocatorIteratedPowerProduct
