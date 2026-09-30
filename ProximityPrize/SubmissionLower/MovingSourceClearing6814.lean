import ProximityPrize.SubmissionLower.WholeSpaceSourceKernel6814
namespace ProximityPrize.SubmissionLower.MovingSourceClearing6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators
open MvPolynomial RCN095 RCN136 RCN207
open SecondJetCoefficients SecondJetClearedHelper

section Polynomial
variable {R : Type*} [CommRing R]

def targetPolynomial (P : Polynomial R) (n : ℕ) (h q : R) : Polynomial R :=
  cleared (P.map Polynomial.C) n (Polynomial.C h) (Polynomial.X-Polynomial.C q)

def inverseSubstitution (h q : R) : Polynomial R →+* Polynomial R :=
  Polynomial.eval₂RingHom Polynomial.C (Polynomial.C h*Polynomial.X+Polynomial.C q)

theorem inverseSubstitution_C (h q a : R) :
    inverseSubstitution h q (Polynomial.C a)=Polynomial.C a := by
  simp [inverseSubstitution]

theorem inverseSubstitution_target (P : Polynomial R) (n : ℕ) (h q : R)
    (hn : P.natDegree ≤ n) :
    inverseSubstitution h q (targetPolynomial P n h q)=(Polynomial.C h)^n*P := by
  have hc : (inverseSubstitution h q).comp Polynomial.C=Polynomial.C := by
    apply RingHom.ext
    intro a
    exact inverseSubstitution_C h q a
  rw [targetPolynomial,map_cleared,Polynomial.map_map,hc]
  simp only [inverseSubstitution_C,map_sub]
  have hx : inverseSubstitution h q Polynomial.X-Polynomial.C q=Polynomial.C h*Polynomial.X := by
    simp [inverseSubstitution]
  rw [hx,cleared_eval (P.map Polynomial.C) n (Polynomial.natDegree_map_le.trans hn)
    (Polynomial.C h) (Polynomial.C h*Polynomial.X) Polynomial.X rfl]
  rw [Polynomial.eval_map,Polynomial.eval₂_C_X]

theorem eval_targetPolynomial {S : Type*} [CommRing S] (f : R →+* S)
    (P : Polynomial R) (n : ℕ) (h q : R) (t : S) :
    Polynomial.eval₂ f t (targetPolynomial P n h q)=
      cleared (P.map f) n (f h) (t-f q) := by
  change (Polynomial.eval₂RingHom f t) (targetPolynomial P n h q)=_
  have hc : (Polynomial.eval₂RingHom f t).comp Polynomial.C=f := by
    apply RingHom.ext
    intro a
    simp
  rw [targetPolynomial,map_cleared,Polynomial.map_map]
  rw [hc]
  simp

end Polynomial

section Surface
variable {K E : Type*} [Field K] [Field E]
local notation "Poly3" => MvPolynomial (Fin 3) E

def coefficients (phi : Polynomial K →+* E) (P : WholeSpaceCube6814.Poly (K := K)) :
    Polynomial Poly3 := (asS P).map (surfaceMap phi)

def movingCut (phi : Polynomial K →+* E) (P : WholeSpaceCube6814.Poly (K := K))
    (s : ℕ) (Q A : Poly3) (target : E) : Poly3 :=
  cleared (coefficients phi P) s (2*A) (MvPolynomial.C target-Q)

theorem twice_linear_flag (A : Poly3) (hA : PolynomialInFlag unitYZFlag A) :
    PolynomialInFlag unitYZFlag (2*A) := by
  intro e he
  have he' : e ∈ ((2 : E) • A).support := by
    simpa only [MvPolynomial.smul_eq_C_mul,map_ofNat] using he
  exact hA e (MvPolynomial.support_smul he')

end Surface
end
end ProximityPrize.SubmissionLower.MovingSourceClearing6814
