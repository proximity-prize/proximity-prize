import Mathlib.Algebra.MvPolynomial.PDeriv
import ProximityPrize.SubmissionLower.ZRvlzfb
set_option Elab.async false
set_option autoImplicit true
namespace qYzLClc
noncomputable section
open MvPolynomial
variable {σ A F:Type*} [DecidableEq σ] [CommRing A] [Field F]
private def AT (i:σ) (b:σ→A) :
    MvPolynomial σ A →ₐ[A] Polynomial A :=
  aeval fun j=>Polynomial.C (b j)+if j=i then Polynomial.X else 0
private theorem section_deriv (i:σ) (b:σ→A) (q:MvPolynomial σ A) :
    (AT i b q).derivative=AT i b (pderiv i q) := by
  induction q using MvPolynomial.induction_on with
  | C c=>simp [AT]
  | add p q hp hq=>simp only [map_add,hp,hq]
  | mul_X p j hp =>
    rw [map_mul,Polynomial.derivative_mul,hp,Derivation.leibniz,smul_eq_mul,
      smul_eq_mul,map_add,map_mul,map_mul]
    by_cases h:j=i
    · subst j
      simp [AT,add_comm,mul_comm]
    · simp [AT,pderiv_X_of_ne h,h,mul_comm]
private theorem section_eval (i:σ) (b:σ→A) (q:MvPolynomial σ A) (x :A) :
    (AT i b q).eval x=eval (fun j=>b j+if j=i then x else 0) q:= by
  change Polynomial.aeval x (AT i b q)= _
  rw [AT,comp_aeval_apply,aeval_eq_eval]
  congr 2
  funext j
  by_cases h:j=i <;> simp [Polynomial.coe_aeval_eq_eval,h]
local notation "ct" => (PowerSeries.constantCoeff :PowerSeries F →+* F)
theorem lift_plane (i:σ) (b:σ→PowerSeries F) (q:MvPolynomial σ (PowerSeries F))
    (h:eval (ct ∘ b) (map ct q)=0)
    (hd:eval (ct ∘ b) (pderiv i (map ct q))≠0) :
    ∃ t:σ→PowerSeries F,(∀ j,ct (t j)=ct (b j)) ∧
      (∀ j,j≠i→t j=b j)∧eval t q=0:= by
  let p:=AT i b q
  have hred (r :MvPolynomial σ (PowerSeries F)) :
      ((AT i b r).map ct).eval 0=eval (ct ∘ b) (map ct r) := by
    calc
      _=ct ((AT i b r).eval 0) := by
        simpa only [map_zero] using Polynomial.eval_map_apply
          (p:=AT i b r) ct (0:PowerSeries F)
      _ = _:= by
        rw [section_eval]
        simp only [ite_self,add_zero]
        rw [← eval₂_id (g:=b),eval₂_comp_left,RingHom.comp_id,eval₂_eq_eval_map]
  have hp: (p.map ct).eval 0=0:=(hred q).trans h
  have hpd: (p.map ct).derivative.eval 0≠0:= by
    rw [Polynomial.derivative_map,show p.derivative=AT i b (pderiv i q)
      from section_deriv i b q,hred,← pderiv_map]
    exact hd
  obtain ⟨x,hx,hpx⟩:=lift_root p 0 hp hpd
  refine ⟨fun j=>b j+if j=i then x else 0,?_,?_,(section_eval i b q x).symm.trans hpx⟩
  · intro j
    by_cases hj:j=i <;> simp [hj,hx]
  · intro j hj
    simp [hj]
end
end qYzLClc
