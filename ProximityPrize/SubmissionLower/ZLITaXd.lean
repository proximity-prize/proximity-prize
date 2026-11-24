import Mathlib.Algebra.Polynomial.Homogenize
import ProximityPrize.SubmissionLower.ZdjBl5c
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace qh06gse
noncomputable section
open Polynomial Finset
open P5 (K)
open P5_7_1 (TopRow topLift atTop)

open cu (FX aZ Jet kr jz)
open Qv (lX S4)
def numerator (f :Jet) (S:K[X]) :aZ :=
  -(fibreMap S (S4 lX f) +
    MvPolynomial.C (kr S.derivative)*fibreMap S (S4 Polynomial.derivative f))
def denominator (f :Jet) (S:K[X]) :aZ:=2*fibreMap S f.derivative
private def lastPoly (a y v :FX) :MvPolynomial (Fin 4) FX →+* FX[X] :=
  MvPolynomial.eval₂Hom C ![C a,C y,C v,Polynomial.X]
private theorem lastPoly_derivative (a y v :FX) (T:MvPolynomial (Fin 4) FX) :
    (lastPoly a y v T).derivative=lastPoly a y v (MvPolynomial.pderiv 3 T) := by
  classical
  induction T using MvPolynomial.induction_on with
  | C k=>simp [lastPoly]
  | add P Q hP hQ=>simp [map_add,hP,hQ]
  | mul_X P i ih =>
    simp only [map_mul,derivative_mul,ih,MvPolynomial.pderiv_mul,map_add]
    congr 1
    fin_cases i <;> simp [lastPoly,MvPolynomial.pderiv_X]
private theorem eval_lastPoly (T:TopRow) (a :FX) (S:K[X]) (z :K)
    (ha :a=jz z) :
    (lastPoly a (kr S) (kr S.derivative) (topLift T)).eval (kr (hasseDeriv 2 S)) =
      atTop T z S:= by
  subst a
  simp only [atTop,topLift,MvPolynomial.eval₂_eq_eval_map]
  let w:=kr (hasseDeriv 2 S)
  have h: (evalRingHom w).comp (lastPoly (jz z) (kr S) (kr S.derivative)) =
      MvPolynomial.eval ![jz z,kr S,kr S.derivative,w] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lastPoly]
    · intro i
      fin_cases i <;> simp [lastPoly]
  exact RingHom.congr_fun h _
private theorem lastPoly_sum (a y v :FX) (T:MvPolynomial (Fin 4) FX) :
    lastPoly a y v T = ∑ e∈T.support,monomial (e 3) (T.coeff e*a^(e 0)*y^(e 1)*v^(e 2)) := by
  classical
  change MvPolynomial.eval₂ _ _ _ = _
  rw [MvPolynomial.eval₂_eq']
  apply Finset.sum_congr rfl
  intro e _
  rw [Fin.prod_univ_four,← C_mul_X_pow_eq_monomial]
  change C (T.coeff e)*(C a^e 0*C y ^e 1*C v^e 2*Polynomial.X ^e 3)= _
  simp only [map_mul,map_pow]
  ac_rfl
end
end qh06gse
