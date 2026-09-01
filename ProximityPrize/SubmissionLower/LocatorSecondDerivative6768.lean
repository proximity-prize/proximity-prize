import ProximityPrize.SubmissionLower.LocatorFactorSwitch6768

namespace ProximityPrize.SubmissionLower.LocatorSecondDerivative6768

open RCN081 RCN100 RCN119 RCN122 RCN130 RCN156 RCN180 RCN234
open LocatorLowQuotient

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

variable {K I : Type*} [Field K] [Fintype I]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

abbrev Poly4 := MvPolynomial (Fin 4) K

/-- Two `R` derivatives spend two copies of the `R` contact weight. -/
theorem pderiv_R_twice_weight_add_le
    (weights : Fin 4 → Nat) (Q : MvPolynomial (Fin 4) K)
    (hder : MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4) Q) ≠ 0) :
    wt weights (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) Q)) + 2 * weights 2 ≤
      wt weights Q := by
  have hfirst : MvPolynomial.pderiv (2 : Fin 4) Q ≠ 0 := by
    intro hz
    apply hder
    simp only [hz, map_zero]
  have h₁ := LocatorContact.pderiv_R_weight_add_le weights Q hfirst
  have h₂ := LocatorContact.pderiv_R_weight_add_le weights
    (MvPolynomial.pderiv (2 : Fin 4) Q) hder
  omega

/-- Degree of the twice differentiated specialization, retaining the two
copies of the derivative-weight saving. -/
theorem specialized_R_second_derivative_degree
    (Q : MvPolynomial (Fin 4) K) (P : Polynomial K) (gamma : K) (w d : Nat)
    (hw : 1 ≤ w) (hP : P.natDegree ≤ w)
    (hQ : wt (contactWeights w) Q ≤ d)
    (hregular : specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) Q)) ≠ 0) :
    (specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) Q))).natDegree + 2 * w ≤ d + 2 := by
  let Q₁ := MvPolynomial.pderiv (2 : Fin 4) Q
  have hder₂ : MvPolynomial.pderiv (2 : Fin 4) Q₁ ≠ 0 := by
    intro hz
    apply hregular
    rw [hz, map_zero]
  have hder₁ : Q₁ ≠ 0 := by
    intro hz
    apply hder₂
    simp only [hz, map_zero]
  have hdrop := LocatorContact.pderiv_R_weight_add_le
    (contactWeights w) Q hder₁
  change wt (contactWeights w) Q₁ + (w - 1) ≤ wt (contactWeights w) Q at hdrop
  have hQ₁ : wt (contactWeights w) Q₁ ≤ d - (w - 1) := by
    omega
  have hd := ContactOrderBridge.specialized_R_derivative_degree
    K Q₁ P gamma w (d - (w - 1)) hP hQ₁ hregular
  have hwD : w - 1 ≤ d := by omega
  change (specialization K P gamma
    (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4) Q))).natDegree + w ≤
      d - (w - 1) + 1 at hd
  omega

/-- A twice-low kernel polynomial has identically vanishing second
`R`-derivative on every decoded branch. -/
theorem specialization_pderiv_R_twice_eq_zero_of_kernel_low_box
    (D Dlow w L s m : Nat) (nodes : I ↪ K) (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
    (hlow : reconstruct K D w L s v.1 ∈ globalCoefficientBox K Dlow w L s)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hw : 1 ≤ w) (hP : P.natDegree ≤ w)
    (hcapacity : Dlow ≤ (m - 2) * support.card + 2 * (w - 1))
    (hvalues : ∀ i ∈ support, P.eval (nodes i) = u0 i + gamma * u1 i) :
    specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (reconstruct K D w L s v.1))) = 0 := by
  let H := reconstruct K D w L s v.1
  by_contra hne
  have hH : H ≠ 0 := by
    intro hz
    apply hne
    simp only [H, hz, map_zero]
  have hDlow : 0 < Dlow := by
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hH
    have h := (hlow hd).2.2
    omega
  have hcaps := (mem_flagGlobalCoefficientBox_iff H Dlow w L s hDlow).mp hlow
  have hdegree := specialized_R_second_derivative_degree H P gamma w
    (Dlow - 1) hw hP (by simpa only [wt] using hcaps.2.2) hne
  have hdegreeStrict :
      (specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H))).natDegree <
        (m - 2) * support.card := by
    omega
  have hcontact : ∀ i ∈ support, ∀ r : Nat,
      slopeDifference K ^ (m - 2 - r) ∣
        (homogenizedTranslation K (nodes i) (u0 i) (u1 i)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4) H))).coeff r := by
    intro i _
    apply (ContactOrderBridge.contactAtLeast_iff_block_divisibility
      K (nodes i) (u0 i) (u1 i) (m - 2) _).mp
    have h₀ := ContactOrderBridge.contactAtLeast_of_mem_kernel
      K D w L s m nodes u0 u1 v.1 v.2 i
    have h₁ := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) m H h₀
    have h₂ := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 1)
        (MvPolynomial.pderiv (2 : Fin 4) H) h₁
    simpa only [Nat.sub_sub] using h₂
  exact hne (specialization_eq_zero_of_contact_and_degree K
    (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4) H))
    P gamma nodes u0 u1 support (m - 2) hcontact hvalues hdegreeStrict)

/-- On a root of `F`, the second derivative of `F^2 C` keeps exactly the
cross term `2 (F_R)^2 C`. -/
theorem specialization_pderiv_twice_sq_mul
    (F C : MvPolynomial (Fin 4) K) (P : Polynomial K) (gamma : K)
    (hroot : specialization K P gamma F = 0) :
    specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) (F * F * C))) =
      2 * (specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) F)) ^ 2 *
          specialization K P gamma C := by
  simp only [MvPolynomial.pderiv_mul, map_add, map_mul, hroot,
    zero_mul, mul_zero, zero_add, add_zero]
  ring

/-- The repeated-factor arm converts twice-lowness into a genuine root of
the small cofactor. -/
theorem cofactor_specialization_eq_zero
    (F C : MvPolynomial (Fin 4) K) (P : Polynomial K) (gamma : K)
    (htwo : (2 : K) ≠ 0)
    (hroot : specialization K P gamma F = 0)
    (hregular : specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hsecond : specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) (F * F * C))) = 0) :
    specialization K P gamma C = 0 := by
  rw [specialization_pderiv_twice_sq_mul F C P gamma hroot] at hsecond
  have htwoPoly : (2 : Polynomial K) ≠ 0 := by
    intro hz
    apply htwo
    have hc := congrArg (fun Q : Polynomial K ↦ Q.coeff 0) hz
    simpa using hc
  rcases mul_eq_zero.mp hsecond with hleft | hC
  · rcases mul_eq_zero.mp hleft with htwoZero | hsquare
    · exact (htwoPoly htwoZero).elim
    · exact ((pow_ne_zero 2 hregular) hsquare).elim
  · exact hC

end

end ProximityPrize.SubmissionLower.LocatorSecondDerivative6768

#print axioms ProximityPrize.SubmissionLower.LocatorSecondDerivative6768.cofactor_specialization_eq_zero
