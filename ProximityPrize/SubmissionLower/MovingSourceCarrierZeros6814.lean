import ProximityPrize.SubmissionLower.MovingSourceGenericCuts6814

/-! Lift a root in the faithful generic carrier field to a polynomial
identity on the carrier, then transfer it to every regular moving point.
A root in an arbitrary closed-point field is not substituted for this. -/
namespace ProximityPrize.SubmissionLower.MovingSourceCarrierZeros6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
open MvPolynomial RCN136 RCN207 SecondJetCoefficients SecondJetClearedHelper
open SecondJetCarrierDichotomy MovingSourceClearing6814

variable {K E : Type*} [Field K] [Field E]

theorem helper_dvd_of_generic_root
    (P : WholeSpaceCube6814.Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (phi : MvPolynomial (Fin 4) K →+* E)
    (hker : ∀ A, phi A=0 ↔ F ∣ A)
    (s : ℕ) (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hH : phi (2*RCN313.polyH K F)≠0)
    (hroot : ((asS P).map phi).eval (ratio phi F)=0) : F ∣ helper P F s 0 := by
  apply (hker _).mp
  have hh := mapped_helper P F phi s 0 hS hH
  simpa only [Nat.sub_zero,Function.iterate_zero,id_eq,hroot,mul_zero] using hh

theorem simple_root_vanishes (P : Polynomial E) (x : E)
    (h : P.rootMultiplicity x=1) : P.eval x=0 := by
  by_contra hn
  have hz := Polynomial.rootMultiplicity_eq_zero hn
  rw [h] at hz
  omega

theorem movingCut_zero_of_helper_dvd {L : Type*} [Field L]
    (phi : Polynomial K →+* E) (ev : MvPolynomial (Fin 3) E →+* L)
    (P : WholeSpaceCube6814.Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (s : ℕ) (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hdiv : F ∣ helper P F s 0)
    (hF : ev (surfaceMap phi F)=0)
    (hH : ev (surfaceMap phi (2*RCN313.polyH K F))≠0)
    (quadratic A : MvPolynomial (Fin 3) E) (target : E)
    (hM : ev (movingEquation (surfaceMap phi (RCN313.polyH K F))
      (surfaceMap phi (RCN313.polyG K F)) quadratic A target)=0) :
    ev (movingCut phi P s quadratic A target)=0 := by
  let psi := ev.comp (surfaceMap phi)
  let H := surfaceMap phi (RCN313.polyH K F)
  let G := surfaceMap phi (RCN313.polyG K F)
  have hpsiF : psi F=0 := hF
  have hpsiH : psi (2*RCN313.polyH K F)≠0 := hH
  have hz := map_dvd psi hdiv
  rw [hpsiF,zero_dvd_iff] at hz
  have hmapped := mapped_helper P F psi s 0 hS hpsiH
  simp only [Nat.sub_zero,Function.iterate_zero,id_eq] at hmapped
  rw [hmapped] at hz
  have hroot := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero s hpsiH)
  have hden : psi (2*RCN313.polyH K F)=ev (2*H) := by
    simp only [psi,H,RingHom.comp_apply,map_mul,map_ofNat]
  have hHH : ev H≠0 := by
    intro hh
    apply hpsiH
    rw [hden,map_mul,hh,mul_zero]
  have hsigma : ev (2*H)*ratio psi F=ev G := by
    rw [←hden]
    change psi (2*RCN313.polyH K F)*ratio psi F=psi (RCN313.polyG K F)
    unfold ratio
    field_simp
  rw [movingCut_value phi ev P s hS H G quadratic A target (ratio psi F) hHH hM hsigma]
  exact mul_eq_zero_of_right _ hroot

#print axioms helper_dvd_of_generic_root
#print axioms movingCut_zero_of_helper_dvd
end
end ProximityPrize.SubmissionLower.MovingSourceCarrierZeros6814
