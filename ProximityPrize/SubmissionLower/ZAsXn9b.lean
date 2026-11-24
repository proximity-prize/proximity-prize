import ProximityPrize.SubmissionLower.Z5cOcra
import ProximityPrize.SubmissionLower.ZSm5aLa
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qoGY3we
noncomputable section
open Polynomial
open cu (L FX)
open P5_7_7 (phys)
open qrezXJe (rootEval)
open q2TwyLa (i5 diff)
open private chain from ProximityPrize.SubmissionLower.Z5cOcra
open private sum_coeff from ProximityPrize.SubmissionLower.Z62SyBc
private theorem reduce_eval (q:i5[X][X]) (y :Series) (P:L[X]) (hy :cc y=phys P) :
    cc (q.eval₂ (bY false) y)=rootEval (q.map reduce) P:= by
  rw [hom_eval₂,finite_reduce,hy,rootEval,eval₂_map]
private theorem differentiated_root (f :i5[X][X]) (P:L[X])
    (h:rootEval (f.map reduce) P=0) :
    -rootEval ((physDiff f).map reduce) P =
      rootEval (f.map reduce).derivative P*phys P.derivative := by
  let q:=f.map reduce
  have ev (g:L[X][X]) :rootEval g P=phys (g.eval P) :=eval₂_hom (f :=phys) _
  have hz :q.eval P=0:=IsFractionRing.injective L[X] FX
    ((ev q).symm.trans (h.trans (map_zero phys).symm))
  have hm: (physDiff f).map reduce=q.sum fun i b=>monomial i b.derivative := by
    apply Polynomial.ext
    intro i
    rw [coeff_map,physDiff,sum_coeff _ (by simp),sum_coeff _ (by simp)]
    change (((f.coeff i).derivative).map PowerSeries.constantCoeff) =
      (q.coeff i).derivative
    dsimp only [q]
    rw [coeff_map,coe_mapRingHom,derivative_map]
  have hc:=chain ((Polynomial.derivative' (R:=L)).restrictScalars ℤ) (RingHom.id L[X]) P q
  simp only [Derivation.restrictScalars_apply,derivative'_apply,RingHom.id_apply,eval₂_id,
    hz,derivative_zero,← eval_monomial,← eval_sum,← hm] at hc
  simp only [ev,← map_neg,← map_mul]
  apply congrArg phys
  linear_combination hc
theorem local_root (f :i5[X][X]) (r :L) (P:L[X])
    (hr :rootEval (f.map reduce) P=0) (hd:rootEval (f.map reduce).derivative P≠0)
    (href :P - C r≠0) :Nonempty (LocalRoot f r P) := by
  let q:=f.map (bY false)
  have hm:q.map cc=(f.map reduce).map phys := by
    dsimp only [q]
    rw [map_map,finite_reduce,map_map]
  have hq: (q.map cc).eval (phys P)=0:= by
    simpa only [hm,eval_map,rootEval] using hr
  have hqd: (q.map cc).derivative.eval (phys P)≠0:= by
    simpa only [hm,derivative_map,eval_map,rootEval] using hd
  obtain ⟨y,hy,hfy⟩:=qYzLClc.lift_root q (phys P) hq hqd
  let d:=f.derivative.eval₂ (bY false) y
  let R:=y-PowerSeries.C (phys (C r))
  let u:=R*d
  have hd0:cc d=rootEval (f.map reduce).derivative P:= by
    dsimp only [d]
    rw [reduce_eval _ _ _ hy,derivative_map]
  have hr0:cc R=phys (P - C r) := by simp [R,hy]
  have hR:cc R≠0:=hr0 ▸ (map_ne_zero_iff phys (IsFractionRing.injective L[X] FX)).2 href
  have hD:cc d≠0:=hd0 ▸ hd
  have hu:cc u≠0:= by
    change cc (R*d)≠0
    rw [map_mul]
    exact mul_ne_zero hR hD
  have unit_of {g:Series} (hg:cc g≠0) :IsUnit g :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hg)
  let log (g:i5[X][X]) := -(g.eval₂ (bY false) y)*u⁻¹
  have hlog (g:i5[X][X]) :log g*R*d = -(g.eval₂ (bY false) y) := by
    change (-(g.eval₂ (bY false) y)*u⁻¹)*R*d= _
    rw [mul_assoc,← show u=R*d from rfl,mul_assoc,PowerSeries.inv_mul_cancel _ hu,mul_one]
  have hres (g:i5[X][X]) :
      cc (log g)*phys (P - C r)*rootEval (f.map reduce).derivative P =
        -rootEval (g.map reduce) P:= by
    simpa only [map_mul,map_neg,hr0,hd0,reduce_eval _ _ _ hy] using congrArg cc (hlog g)
  dsimp only [q] at hfy
  rw [eval_map] at hfy
  refine ⟨⟨y,hfy,hy,unit_of hD,unit_of hR,log (diff f),log (physDiff f),
    hlog _,hlog _,?_,?_⟩⟩
  · rw [seedTangent,← neg_div]
    exact (eq_div_iff hd).mpr (hres _)
  · apply mul_right_cancel₀ hd
    rw [hres,differentiated_root f P hr,mul_comm]
end
end qoGY3we
