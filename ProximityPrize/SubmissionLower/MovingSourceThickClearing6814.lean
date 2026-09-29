import ProximityPrize.SubmissionLower.MovingSourceMixedOwnerRouting6814
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! Source contact survives denominator clearing as membership in an
actual primary thickening. Work in its quotient, where the regular
denominators are units and the moving-parameter difference is nilpotent.
No field or reducedness assumption is made on that quotient. -/
namespace ProximityPrize.SubmissionLower.MovingSourceThickClearing6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open Polynomial SecondJetClearedHelper

theorem eval_zero_of_nilpotent_difference
    {R : Type*} [CommRing R] (P : Polynomial R) (x y : R) (d : ℕ)
    (hunit : ∀ j<d, IsUnit (j.factorial : R))
    (hderiv : ∀ j<d, ((Polynomial.derivative)^[j] P).eval x=0)
    (hdiff : (y-x)^d=0) : P.eval y=0 := by
  have hcoeff (j : ℕ) (hj : j<d) : (Polynomial.taylor x P).coeff j=0 := by
    rw [Polynomial.taylor_coeff]
    have he0 := congrFun (Polynomial.factorial_smul_hasseDeriv (R:=R) (k:=j)) P
    change j.factorial • (Polynomial.hasseDeriv j P)=((Polynomial.derivative)^[j] P) at he0
    have he := congrArg (fun Q : Polynomial R => Q.eval x) he0
    simp only [nsmul_eq_mul,Polynomial.eval_mul,Polynomial.eval_natCast,hderiv j hj] at he
    exact (hunit j hj).mul_left_cancel (he.trans (mul_zero _).symm)
  obtain ⟨Q,hQ⟩ := Polynomial.X_pow_dvd_iff.mpr hcoeff
  have he := congrArg (fun Q : Polynomial R => Q.eval (y-x)) hQ
  rw [Polynomial.taylor_eval_sub,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,hdiff,zero_mul] at he
  exact he

theorem unit_mod_thickening
    {R : Type*} [CommRing R] (J : Ideal R) [J.IsMaximal]
    (surface : R) (d : ℕ) (h : R) (hh : h∉J) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {surface} ⊔ J^d) h) := by
  have hu := Ideal.Quotient.isUnit_mk_pow_of_notMem J (n:=d) hh
  have hm := hu.map (Ideal.Quotient.factor (show J^d≤Ideal.span {surface} ⊔ J^d from le_sup_right))
  simpa only [Ideal.Quotient.factor_mk] using hm

/-- The two regular denominators may fail at other points; only their
nonmembership in THIS component prime is needed. All lower source
helpers genuinely lie in the carrier ideal. -/
theorem cleared_mem_primary_of_helpers
    {R : Type*} [CommRing R] (J : Ideal R) [J.IsMaximal]
    (surface H G A B : R) (s d : ℕ) (P : Polynomial R)
    (hdegree : P.natDegree≤s)
    (hH : H∉J) (hA : A∉J) (hM : H*B-A*G∈J)
    (hfact : ∀ j<d, IsUnit (j.factorial : R))
    (hhelpers : ∀ j<d, cleared ((Polynomial.derivative)^[j] P) (s-j) H G∈Ideal.span {surface}) :
    cleared P s A B∈Ideal.span {surface} ⊔ J^d := by
  let I := Ideal.span {surface} ⊔ J^d
  let q := Ideal.Quotient.mk I
  obtain ⟨u,hu⟩ := unit_mod_thickening J surface d H hH
  obtain ⟨v,hv⟩ := unit_mod_thickening J surface d A hA
  change (↑u : R ⧸ I)=q H at hu
  change (↑v : R ⧸ I)=q A at hv
  let x : R ⧸ I := (↑u⁻¹ : R ⧸ I)*q G
  let y : R ⧸ I := (↑v⁻¹ : R ⧸ I)*q B
  have hx : q H*x=q G := by simp [x,←hu,←mul_assoc]
  have hy : q A*y=q B := by simp [y,←hv,←mul_assoc]
  have hh : ∀ j<d, ((Polynomial.derivative)^[j] (P.map q)).eval x=0 := by
    intro j hj
    have hm : cleared ((Polynomial.derivative)^[j] P) (s-j) H G∈I :=
      (show Ideal.span {surface}≤I from le_sup_left) (hhelpers j hj)
    have he : q (cleared ((Polynomial.derivative)^[j] P) (s-j) H G)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hm
    rw [map_cleared] at he
    have hdeg : (((Polynomial.derivative)^[j] P).map q).natDegree≤s-j :=
      Polynomial.natDegree_map_le.trans ((Polynomial.natDegree_iterate_derivative P j).trans
        (Nat.sub_le_sub_right hdegree j))
    rw [cleared_eval _ _ hdeg _ _ x hx,←Polynomial.iterate_derivative_map] at he
    exact ((unit_mod_thickening J surface d H hH).pow (s-j)).mul_left_cancel
      (he.trans (mul_zero _).symm)
  have hdiff : (y-x)^d=0 := by
    have hpow : (H*B-A*G)^d∈I :=
      (show J^d≤I from le_sup_right) (Ideal.pow_mem_pow hM d)
    have he : q (H*B-A*G)^d=0 := by
      rw [←map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hpow
    have hrel : q H*q A*(y-x)=q (H*B-A*G) := by
      rw [map_sub,map_mul,map_mul]
      calc
        _=q H*(q A*y)-q A*(q H*x) := by ring
        _=_ := by rw [hy,hx]
    rw [←hrel,mul_pow] at he
    exact (((unit_mod_thickening J surface d H hH).mul
      (unit_mod_thickening J surface d A hA)).pow d).mul_left_cancel
      (he.trans (mul_zero _).symm)
  have hf (j : ℕ) (hj : j<d) : IsUnit (j.factorial : R ⧸ I) := by
    simpa only [map_natCast] using (hfact j hj).map q
  have hz := eval_zero_of_nilpotent_difference (P.map q) x y d hf hh hdiff
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (cleared P s A B)=0
  rw [map_cleared,cleared_eval _ _ (Polynomial.natDegree_map_le.trans hdegree) _ _ y hy,hz,mul_zero]

#print axioms cleared_mem_primary_of_helpers
end
end ProximityPrize.SubmissionLower.MovingSourceThickClearing6814
