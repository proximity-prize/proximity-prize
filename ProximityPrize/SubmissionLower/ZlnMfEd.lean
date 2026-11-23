import ProximityPrize.SubmissionLower.Zzjdkoa
import ProximityPrize.SubmissionLower.ZocsBpe
set_option Elab.async false
namespace qJai0ob
noncomputable section
open Polynomial Finset
open cu (L)






open E7 (CurvePlace)
open scoped WithZero
open private adG cTA aMX efc b4s bHf from ProximityPrize.SubmissionLower.Y
variable {E :Type} [Field E]
private def gauss (v :Valuation E ℤᵐ⁰) :Valuation E[X][X] ℤᵐ⁰ :=
  (efc (b4s v)).comap (mapRingHom (algebraMap E[X] (RatFunc E)))
private theorem gaussX (v :Valuation E ℤᵐ⁰) :adG v (Polynomial.X:E[X])=1 := by
  simp [adG,support_X]
private theorem efe (v :Valuation E ℤᵐ⁰) (g:E[X]) :
    gauss v (C g)=adG v g:= by
  change adG (b4s v) ((C g).map (algebraMap E[X] (RatFunc E)))= _
  rw [map_C,cTA,bHf]
private theorem gauss_X (v :Valuation E ℤᵐ⁰) :
    gauss v (Polynomial.X:E[X][X])=1 := by
  change adG (b4s v)
    ((Polynomial.X:E[X][X]).map (algebraMap E[X] (RatFunc E)))= _
  rw [Polynomial.map_X,gaussX]
private theorem coeff_gauss (v :Valuation E ℤᵐ⁰) (f :E[X][X]) (i j:ℕ) :
    v ((f.coeff i).coeff j)≤gauss v f := by
  refine (aMX v _ _).trans ?_
  rw [← bHf]
  change b4s v (algebraMap E[X] (RatFunc E) (f.coeff i)) ≤
    adG (b4s v) (f.map (algebraMap E[X] (RatFunc E)))
  rw [← coeff_map]
  exact aMX _ _ _
private theorem gauss_taylor (v :Valuation E ℤᵐ⁰) {x :E} (hx :v x≤1) {g:E[X]}
    {h:ℤᵐ⁰} (hg : ∀ j,v (g.coeff j)≤h) :adG v (taylor x g)≤h:= by
  let w:=efc v
  have hxc:w (Polynomial.X+C x)≤1 := by
    apply w.map_add_le (gaussX v).le
    change adG v (C x)≤1
    rwa [cTA]
  change w (taylor x g)≤h
  rw [taylor_apply,comp_eq_sum_left,Polynomial.sum_def]
  apply w.map_sum_le
  intro j _
  rw [map_mul,map_pow]
  calc
    w (C (g.coeff j))*w (Polynomial.X+C x)^j≤h*1^j :=
      mul_le_mul' ((cTA v _).le.trans (hg j)) (pow_le_pow_left' hxc _)
    _=h:= by simp
variable [Algebra L E]
private theorem const_bound (v :CurvePlace L E) (x :L) :v.value (algebraMap L E x)≤1 := by
  by_cases hx :x=0
  · simp [hx]
  · exact (v.on_constants x hx).le
private theorem target_bound (v :CurvePlace L E) {u:E} {k :ℕ}
    (hu:v.value u≤WithZero.exp (k :ℤ)) (a b:L) :
    v.value (algebraMap L E a+algebraMap L E b*u)≤WithZero.exp (k :ℤ) := by
  apply v.value.map_add_le
  · exact (const_bound v a).trans (WithZero.one_le_exp_iff.mpr (Int.natCast_nonneg _))
  · rw [map_mul]
    exact (mul_le_mul' (const_bound v b) hu).trans_eq (one_mul _)
end
end qJai0ob
