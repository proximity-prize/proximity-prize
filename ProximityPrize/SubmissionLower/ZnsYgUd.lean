import Mathlib.RingTheory.Polynomial.Resultant.Basic
set_option Elab.async false
namespace q0n1P7d
open Polynomial
variable {R M:Type*} [CommRing R] [Field M] (ι:R →+* M) {y :M}
theorem eval_integral (hy :ι.IsIntegralElem y) (g:R[X]) :
    ι.IsIntegralElem (g.eval₂ ι y) := by
  let:Algebra R M:=ι.toAlgebra
  change IsIntegral R y at hy
  change IsIntegral R (g.eval₂ ι y)
  rw [eval₂_eq_sum_range]
  exact IsIntegral.sum _ fun i _=>(ι.isIntegralElem_map (x :=g.coeff i)).mul ι (hy.pow i)
theorem root_integral {g:R[X]} (hg:g.eval₂ ι y=0) (hu:IsUnit g.leadingCoeff) :
    ι.IsIntegralElem y := by
  obtain ⟨u,hu⟩:=hu
  apply RingHom.IsIntegralElem.of_mul_unit (f :=ι) y (ι g.leadingCoeff) (↑u⁻¹)
  · rw [← map_mul,← hu,Units.inv_mul,map_one]
  · rw [mul_comm]
    exact ι.isIntegralElem_leadingCoeff_mul g y hg
private theorem inverse_integral {a b:M} (hb:ι.IsIntegralElem b) {r :R}
    (hr :IsUnit r) (he :a*b=ι r) :ι.IsIntegralElem a⁻¹:= by
  obtain ⟨u,rfl⟩:=hr
  have h:a*(b*ι (↑u⁻¹:R))=1 := by
    rw [← mul_assoc,he,← map_mul,Units.mul_inv,map_one]
  rw [inv_eq_of_mul_eq_one_right h]
  exact hb.mul ι ι.isIntegralElem_map
theorem derivative_inverse {g:R[X]} (hg:g.eval₂ ι y=0)
    (hy :ι.IsIntegralElem y) (hd:0<g.natDegree) (hl:IsUnit g.leadingCoeff)
    (hc:IsUnit g.discr) :ι.IsIntegralElem (g.derivative.eval₂ ι y)⁻¹:= by
  have hr :IsUnit (g.resultant g.derivative g.natDegree (g.natDegree-1)) := by
    rw [resultant_deriv (natDegree_pos_iff_degree_pos.mp hd)]
    exact (((isUnit_one.neg:IsUnit (-1 :R)).pow _).mul hl).mul hc
  obtain ⟨a,b,-,-,hab⟩:=exists_mul_add_mul_eq_C_resultant g g.derivative le_rfl
    (natDegree_derivative_le g) (Or.inl hd.ne')
  have he :=congrArg (eval₂RingHom ι y) hab
  simp only [map_add,map_mul,coe_eval₂RingHom,eval₂_C,hg,zero_mul,zero_add] at he
  exact inverse_integral ι (eval_integral ι hy b) hr he
theorem ref_inverse {g:R[X]} (hg:g.eval₂ ι y=0) (hy :ι.IsIntegralElem y)
    (r :R) (hr :IsUnit (g.eval r)) :ι.IsIntegralElem (y-ι r)⁻¹:= by
  obtain ⟨b,hb⟩:=X_sub_C_dvd_sub_C_eval (p:=g) (a :=r)
  have he :=congrArg (eval₂RingHom ι y) hb
  simp only [map_mul,map_sub,coe_eval₂RingHom,eval₂_X,eval₂_C,hg,zero_sub] at he
  rw [← map_neg] at he
  exact inverse_integral ι (eval_integral ι hy b) hr.neg he.symm
end q0n1P7d
