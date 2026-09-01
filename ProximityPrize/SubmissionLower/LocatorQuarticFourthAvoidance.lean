import ProximityPrize.SubmissionLower.LocatorTripleCubeAvoidance
import ProximityPrize.SubmissionLower.R3

namespace ProximityPrize.SubmissionLower.LocatorQuarticFourthAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN122 RCN130 RCN156 RCN180 RCN234 RCN260 RCN347

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000

section CubicJet

variable {R A B : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B]

/-- The fourth iterated derivative of `F^4 * Q`, evaluated at a zero of `F`,
has exactly the expected `4!` leading coefficient.  This is the unnormalised
form of the fourth Hasse-jet product identity. -/
theorem evaluated_iterate_four_fourth_product
    (D : Derivation R A A) (value : A →+* B) (F Q : A)
    (hFzero : value F = 0) :
    value (D (D (D (D (F * (F * (F * (F * Q)))))))) =
      (24 : B) * (value (D F)) ^ 4 * value Q := by
  simp only [leibniz_product, map_add, map_mul, hFzero,
    zero_mul, mul_zero, zero_add, add_zero]
  ring

end CubicJet

section NormalizedCubicJet

variable {R A L : Type*} [CommRing R] [CommRing A] [Algebra R A] [Field L]

/-- The characteristic-safe cubic product formula expressed through the
existing normalized `jetCoefficient` API.  The sole required characteristic
hypothesis is invertibility of `4!`. -/
theorem jetCoefficient_four_fourth_product
    (D : Derivation R A A) (value : A →+* L) (F Q : A)
    (htwentyfour : (24 : L) ≠ 0) (hFzero : value F = 0) :
    jetCoefficient D value (F * (F * (F * (F * Q)))) 4 =
      (jetCoefficient D value F 1) ^ 4 * value Q := by
  have hfirst : jetCoefficient D value F 1 = value (D F) := by
    simp [jetCoefficient]
  rw [hfirst]
  change value (D (D (D (D (F * (F * (F * (F * Q)))))))) / (24 : L) =
    (value (D F)) ^ 4 * value Q
  rw [div_eq_iff htwentyfour]
  rw [evaluated_iterate_four_fourth_product D value F Q hFzero]
  ring

end NormalizedCubicJet

section FourthDerivative

variable {K I : Type*} [Field K] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

/-- Three `R` derivatives of a low reconstruction still vanish after
specialization when the interpolation contact budget pays for three lost
orders.  This is the direct fourth-order analogue of
`specialization_pderiv_R2_eq_zero_of_kernel_low_box`. -/
theorem specialization_pderiv_R4_eq_zero_of_kernel_low_box
    (D Dlow w L s m : ℕ) (nodes : I ↪ K) (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
    (hlow : reconstruct K D w L s v.1 ∈ globalCoefficientBox K Dlow w L s)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hw : 1 ≤ w) (hP : P.natDegree ≤ w)
    (hcapacity : Dlow ≤ (m - 4) * support.card + 4 * (w - 1))
    (hvalues : ∀ i ∈ support, P.eval (nodes i) = u0 i + gamma * u1 i) :
    RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (reconstruct K D w L s v.1))))) = 0 := by
  classical
  let H := reconstruct K D w L s v.1
  by_contra hne
  have hder4 : MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H))) ≠ 0 := by
    intro hz
    apply hne
    change RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4) H)))) = 0
    rw [hz, map_zero]
  have hder3 : MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H)) ≠ 0 := by
    intro hz
    exact hder4 (by rw [hz, map_zero])
  have hder2 : MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4) H) ≠ 0 := by
    intro hz
    exact hder3 (by rw [hz, map_zero])
  have hder1 : MvPolynomial.pderiv (2 : Fin 4) H ≠ 0 := by
    intro hz
    exact hder2 (by rw [hz, map_zero])
  have hH : H ≠ 0 := by
    intro hz
    exact hder1 (by rw [hz, map_zero])
  have hDlow : 0 < Dlow := by
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hH
    have h := (hlow hd).2.2
    omega
  have hcaps := (mem_flagGlobalCoefficientBox_iff H Dlow w L s hDlow).mp hlow
  have hweight1 := LocatorContact.pderiv_R_weight_add_le
    (contactWeights w) H hder1
  have hder1weight : wt (contactWeights w)
      (MvPolynomial.pderiv (2 : Fin 4) H) ≤ Dlow - 1 - (w - 1) := by
    change wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4) H) +
      (w - 1) ≤ wt (contactWeights w) H at hweight1
    omega
  have hweight2 := LocatorContact.pderiv_R_weight_add_le
    (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4) H) hder2
  have hder2weight : wt (contactWeights w)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H)) ≤
      Dlow - 1 - 2 * (w - 1) := by
    change wt (contactWeights w)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H)) + (w - 1) ≤
      wt (contactWeights w) (MvPolynomial.pderiv (2 : Fin 4) H) at hweight2
    omega
  have hweight3 := LocatorContact.pderiv_R_weight_add_le
    (contactWeights w)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H)) hder3
  have hder3weight : wt (contactWeights w)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H))) ≤
      Dlow - 1 - 3 * (w - 1) := by
    change wt (contactWeights w)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4) H))) + (w - 1) ≤
      wt (contactWeights w)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H)) at hweight3
    omega
  have hdegree := ContactOrderBridge.specialized_R_derivative_degree K
    (MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) H)))
    P gamma w (Dlow - 1 - 3 * (w - 1)) hP hder3weight hne
  have hdegreeStrict :
      (RCN122.specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (MvPolynomial.pderiv (2 : Fin 4) H))))).natDegree <
        (m - 4) * support.card := by
    rw [RCN101.specialization_eq_ordinary]
    rw [RCN101.specialization_eq_ordinary] at hdegree
    omega
  have hcontact : ∀ i ∈ support, ∀ r : ℕ,
      slopeDifference K ^ (m - 4 - r) ∣
        (RCN122.homogenizedTranslation K (nodes i) (u0 i) (u1 i)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (MvPolynomial.pderiv (2 : Fin 4)
                (MvPolynomial.pderiv (2 : Fin 4) H))))).coeff r := by
    intro i _
    apply (ContactOrderBridge.contactAtLeast_iff_block_divisibility
      K (nodes i) (u0 i) (u1 i) (m - 4) _).mp
    have hfirst := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) m H
      (ContactOrderBridge.contactAtLeast_of_mem_kernel
        K D w L s m nodes u0 u1 v.1 v.2 i)
    have hsecond : ContactOrderBridge.ContactAtLeast K
        (nodes i) (u0 i) (u1 i) (m - 2)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4) H)) := by
      simpa only [Nat.sub_sub] using
        (ContactOrderBridge.contactAtLeast_pderiv_R
          K (nodes i) (u0 i) (u1 i) (m - 1)
          (MvPolynomial.pderiv (2 : Fin 4) H) hfirst)
    have hthird : ContactOrderBridge.ContactAtLeast K
        (nodes i) (u0 i) (u1 i) (m - 3)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (MvPolynomial.pderiv (2 : Fin 4) H))) := by
      simpa only [Nat.sub_sub] using
        (ContactOrderBridge.contactAtLeast_pderiv_R
          K (nodes i) (u0 i) (u1 i) (m - 2)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4) H)) hsecond)
    have hfourth := ContactOrderBridge.contactAtLeast_pderiv_R
      K (nodes i) (u0 i) (u1 i) (m - 3)
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) H))) hthird
    simpa only [Nat.sub_sub] using hfourth
  have hz := RCN122.specialization_eq_zero_of_contact_and_degree K
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4) H))))
    P gamma nodes u0 u1 support (m - 4) hcontact hvalues hdegreeStrict
  apply hne
  simpa only [H, RCN101.specialization_eq_ordinary] using hz

/-- At a regular specialization point of `F`, vanishing of the fourth `R`
derivative of `F^4 * Q` forces the quotient `Q` to vanish. -/
theorem specialization_eq_zero_of_pderiv_R4_fourth_product
    (P : Polynomial K) (gamma : K) (F Q : MvPolynomial (Fin 4) K)
    (htwentyfour : (24 : K) ≠ 0)
    (hFzero : RCN319.specialization K P gamma F = 0)
    (hregular : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hfourth : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (F * (F * (F * (F * Q)))))))) = 0) :
    RCN319.specialization K P gamma Q = 0 := by
  let dR : Derivation K (MvPolynomial (Fin 4) K)
      (MvPolynomial (Fin 4) K) := MvPolynomial.pderiv (2 : Fin 4)
  let ev : MvPolynomial (Fin 4) K →+* Polynomial K :=
    (RCN319.specialization K P gamma).toRingHom
  have hformula := evaluated_iterate_four_fourth_product dR ev F Q hFzero
  change ev (dR (dR (dR (dR (F * (F * (F * (F * Q)))))))) = 0 at hfourth
  rw [hformula] at hfourth
  have htwentyfourPoly : (24 : Polynomial K) ≠ 0 := by
    intro hz
    apply htwentyfour
    have heval := congrArg (Polynomial.eval 0) hz
    simpa using heval
  have hregular' : ev (dR F) ≠ 0 := hregular
  have hcoefficient : (24 : Polynomial K) * (ev (dR F)) ^ 4 ≠ 0 :=
    mul_ne_zero htwentyfourPoly (pow_ne_zero 4 hregular')
  exact (mul_eq_zero.mp hfourth).resolve_left hcoefficient

/-- End-to-end fourth-stage bridge: a low kernel reconstruction equal to
`F^4 * Q` has vanishing quotient at every regular specialization point of
`F`, provided the three-contact capacity inequality holds. -/
theorem specialization_eq_zero_of_kernel_low_box_fourth_product
    (D Dlow w L s m : ℕ) (nodes : I ↪ K) (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
    (hlow : reconstruct K D w L s v.1 ∈ globalCoefficientBox K Dlow w L s)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hw : 1 ≤ w) (hP : P.natDegree ≤ w)
    (hcapacity : Dlow ≤ (m - 4) * support.card + 4 * (w - 1))
    (hvalues : ∀ i ∈ support, P.eval (nodes i) = u0 i + gamma * u1 i)
    (F Q : MvPolynomial (Fin 4) K) (htwentyfour : (24 : K) ≠ 0)
    (hfourthPower : reconstruct K D w L s v.1 = F * (F * (F * (F * Q))))
    (hFzero : RCN319.specialization K P gamma F = 0)
    (hregular : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0) :
    RCN319.specialization K P gamma Q = 0 := by
  apply specialization_eq_zero_of_pderiv_R4_fourth_product P gamma F Q htwentyfour
    hFzero hregular
  rw [← hfourthPower]
  exact specialization_pderiv_R4_eq_zero_of_kernel_low_box
    D Dlow w L s m nodes u0 u1 v hlow P gamma support hw hP hcapacity hvalues

/-- A characteristic-bound wrapper for the cubic quotient detector. -/
theorem specialization_eq_zero_of_pderiv_R4_fourth_product_of_char
    (p : ℕ) [CharP K p] (hchar : 24 < p)
    (P : Polynomial K) (gamma : K) (F Q : MvPolynomial (Fin 4) K)
    (hFzero : RCN319.specialization K P gamma F = 0)
    (hregular : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hfourth : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (F * (F * (F * (F * Q)))))))) = 0) :
    RCN319.specialization K P gamma Q = 0 := by
  apply specialization_eq_zero_of_pderiv_R4_fourth_product P gamma F Q
  · intro htwentyfour
    have hdvd : p ∣ 24 := (CharP.cast_eq_zero_iff K p 24).mp htwentyfour
    exact (Nat.not_le_of_gt hchar) (Nat.le_of_dvd (by decide) hdvd)
  · exact hFzero
  · exact hregular
  · exact hfourth

end FourthDerivative

end

end ProximityPrize.SubmissionLower.LocatorQuarticFourthAvoidance
