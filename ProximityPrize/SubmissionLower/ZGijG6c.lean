import ProximityPrize.SubmissionLower.Zi3GgJd
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qfJaLMa
noncomputable section
open Polynomial Finset

open cu (L)
open P5_7_7 (phys)
open qb0hmCe (cLN)


open qWIOgVd (Chart scaleY scaleY_apply x x_ne)
open scoped Classical WithZero
private theorem eval_change {B:Type*} [Field B] (D:B ≃+* B) (v :B) (hv :v≠0)
    (f :B[X]) (t:B) :
    (changeY D v hv f).eval (v*D t)=D (f.eval t) := by
  change (scaleY v⁻¹ v (inv_mul_cancel₀ hv) (f.map D.toRingHom)).eval _ = _
  rw [scaleY_apply,eval_comp,eval_mul,eval_C,eval_X,← mul_assoc,inv_mul_cancel₀ hv,one_mul]
  exact eval_map_apply (p:=f) D.toRingHom t
private theorem deriv_change {B:Type*} [Field B] (D:B ≃+* B) (v :B) (hv :v≠0)
    (m:B) (f :B[X]) :
    (C m*changeY D v hv f).derivative=C (m*v⁻¹)*changeY D v hv f.derivative := by
  change (C m*scaleY v⁻¹ v (inv_mul_cancel₀ hv) (f.map D.toRingHom)).derivative =
    C (m*v⁻¹)*scaleY v⁻¹ v (inv_mul_cancel₀ hv) (f.derivative.map D.toRingHom)
  rw [derivative_C_mul,scaleY_apply,derivative_comp,derivative_C_mul_X,scaleY_apply,
    derivative_map,map_mul]
  ac_rfl
private theorem cancel_ratio {B:Type*} [Field B] (m a b v :B) (hm:m≠0) :
    (m*a)/((m*v⁻¹)*b)=v*(a/b) := by
  rw [mul_assoc m,mul_div_mul_left _ _ hm,inv_mul_eq_div,div_div_eq_mul_div,mul_comm a v,
    mul_div_assoc]
private theorem layer_repr {E :Type} [Field E] [Algebra L E]
    (e :E →ₐ[L] LaurentSeries L) (j:ℤ) {a :L} (D:Chart a) (s b:ℕ)
    (f :E[X][X]) (hb : ∀ i,(f.coeff i).natDegree≤ cap s b f.natDegree i) :
    (cLN e j (move (algebraMap L E a) s b f.natDegree f)).map phys =
      C (x^(b+f.natDegree*s)) *
        changeY D.changeX (x^s) (pow_ne_zero _ x_ne) ((cLN e j f).map phys) := by
  rw [exp_move]
  exact move_repr a D.changeX D.CJ s b f.natDegree _ (exp_ord_degree e j f)
    (fun i=>(exp_phys_degree e j f i).trans (hb i))
end
end qfJaLMa
