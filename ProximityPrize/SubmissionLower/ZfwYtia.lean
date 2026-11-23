import ProximityPrize.SubmissionLower.Z5cOcra
import ProximityPrize.SubmissionLower.Zdj6KNe
set_option Elab.async false
namespace qvOlzpd
noncomputable section
open Polynomial
open cu (L FX)
open P5_7_7 (phys)
open qb0hmCe (cLN)
open q1kuFjb (IntSeries integralSeries residue fWQ power_residue
 small_valuation expansion_coeff)
open qNu3xvc qoCymac
open scoped WithZero
open private chart_root from ProximityPrize.SubmissionLower.Z5cOcra
private def revIf {R:Type*} [Semiring R] (r :Bool) (f :R[X]) :=
 if r then f.reverse else f
private theorem map_revIf {R S:Type*} [Semiring R] [Semiring S]
   (r :Bool) (j:R →+* S) (f :R[X]) (hd: (f.map j).natDegree=f.natDegree) :
   (revIf r f).map j=revIf r (f.map j) := by
 cases r
 · rfl
 · apply Polynomial.ext
   intro i
   simp only [revIf,ite_true,coeff_map,coeff_reverse,hd]
private theorem bnm {R:Type*} [CommRing R] (f :R[X]) (i:ℕ) :
  (Polynomial.X*f.derivative).coeff i=f.coeff i*(i:R) := by
 cases i <;> simp [coeff_X_mul,coeff_derivative]
private theorem fVm {R:Type*} [CommRing R] (f :R[X]) :
   (Polynomial.X*f.derivative).reflect f.natDegree+Polynomial.X*f.reverse.derivative =
     C (f.natDegree :R)*f.reverse := by
 apply Polynomial.ext
 intro i
 simp only [coeff_add,bnm,coeff_reflect,coeff_reverse,coeff_C_mul]
 by_cases hi:i≤f.natDegree
 · rw [revAt_le hi,← mul_add,← Nat.cast_add,Nat.sub_add_cancel hi,mul_comm]
 · rw [revAt_eq_self_of_lt (lt_of_not_ge hi),coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hi)]
   simp
private theorem chart_simple {R T:Type*} [Field R] [Field T] (i:R →+* T)
   (f :R[X]) (hf :f.Separable) (r :Bool) (y :T)
   (hroot : (revIf r f).eval₂ i y=0) : (revIf r f).derivative.eval₂ i y≠0:= by
 cases r
 · exact hf.eval₂_derivative_ne_zero i hroot
 change f.reverse.eval₂ i y=0 at hroot
 change f.reverse.derivative.eval₂ i y≠0
 have hy :y≠0:= by
   rintro rfl
   rw [eval₂_at_zero,coeff_zero_reverse] at hroot
   exact leadingCoeff_ne_zero.mpr hf.ne_zero (i.injective (hroot.trans (map_zero i).symm))
 let:=invertibleOfNonzero (inv_ne_zero hy)
 have hback (g:R[X]) (hg:g.natDegree≤f.natDegree) :
     (g.reflect f.natDegree).eval₂ i y=0↔g.eval₂ i y⁻¹=0:= by
   simpa only [invOf_eq_inv,inv_inv] using
     eval₂_reflect_eq_zero_iff i y⁻¹ f.natDegree g hg
 have hr :f.eval₂ i y⁻¹=0:=(hback f le_rfl).mp hroot
 intro hpolar
 have he :=congrArg (fun g:R[X]=>g.eval₂ i y) (fVm f)
 simp only [eval₂_add,eval₂_mul,hroot,hpolar,mul_zero,add_zero] at he
 have hd: (Polynomial.X*f.derivative).natDegree≤f.natDegree := by
   apply natDegree_le_iff_coeff_eq_zero.mpr
   intro j hj
   rw [bnm,coeff_eq_zero_of_natDegree_lt hj,zero_mul]
 have hz :=(hback _ hd).mp he
 rw [eval₂_mul,eval₂_X] at hz
 exact (hf.eval₂_derivative_ne_zero i hr) ((mul_eq_zero.mp hz).resolve_left (inv_ne_zero hy))
private theorem eval_map₂ {R S T U:Type*}
   [CommRing R] [CommRing S] [CommRing T] [CommRing U]
   (j:R →+* S) (a :R →+* T) (b:S →+* U) (q:T →+* U)
   (h:q.comp a=b.comp j) (x y :T) (f :R[X][X]) :
   q (f.eval₂ (eval₂RingHom a x) y) =
     (f.map (mapRingHom j)).eval₂ (eval₂RingHom b (q x)) (q y) := by
 rw [hom_eval₂,eval₂_map]
 congr 1
 apply RingHom.ext
 intro g
 change q (g.eval₂ a x)=(g.map j).eval₂ b (q x)
 rw [hom_eval₂,eval₂_map,h]
private theorem laurent_sub {E :Type} [Field E] [Algebra L E]
   (a :E →ₐ[L] LaurentSeries L) (c:E)
   (h: (Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (a c)≤1) :
   (Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰)
     (a (c-algebraMap L E ((a c).coeff 0)))<1 := by
 obtain ⟨g,hg⟩:=(LaurentSeries.val_le_one_iff_eq_coe L (a c)).mp h
 have hc:=power_residue _ g hg.symm
 have he :a (c-algebraMap L E ((a c).coeff 0)) =
     ((g-PowerSeries.C (PowerSeries.constantCoeff g) :PowerSeries L) :LaurentSeries L) := by
   rw [map_sub,a.commutes,← hg,PowerSeries.coe_sub,PowerSeries.coe_C,LaurentSeries.algebraMap_apply]
   rw [← hg] at hc
   rw [hc]
 rw [he]
 exact ((small_valuation _).mpr (by rw [map_sub,PowerSeries.constantCoeff_C,sub_self])).trans_lt
   (WithZero.exp_lt_one_iff.mpr (by decide))
private theorem extend_phys {T:Type} [Field T] [Algebra L T] {x :T}
  (hx :Transcendental L x) :
  ∃ s :FX →+* T,s.comp phys=eval₂RingHom (algebraMap L T) x := by
 let e :=eval₂RingHom (algebraMap L T) x
 have he :Function.Injective e :=transcendental_iff_injective.mp hx
 refine ⟨IsFractionRing.lift (K:=FX) he,RingHom.ext ?_⟩
 intro f
 exact IsFractionRing.lift_algebraMap (K:=FX) he f
theorem proof :qoCymac.c3:= by
 classical
 intro E _ _ A S γ hγ hd _ r v hscale hpolar
 obtain ⟨n,hn,hs⟩:=hscale
 let a :=S.atPlace γ hγ
 let w:=(S.place γ).value
 let O:=w.valuationSubring
 let V:=v.val.valuationSubring
 let κ:=IsLocalRing.ResidueField V
 let π:V →+* κ:=IsLocalRing.residue V
 let j:O →+* L:=residue.comp ((a.toRingHom.comp O.subtype).codRestrict IntSeries (fun c =>
   (integralSeries (a c) ((S.value γ hγ c).symm ▸ c.property)).property))
 have hj (c:O) :j c=(a c).coeff 0:=fWQ _
 let i:O →+* V:=((seed A).comp O.subtype).codRestrict V.toSubring (fun c=> by
   change v.val (seed A c)≤1
   rw [hs]
   exact pow_le_one₀ zero_le c.property)
 let cV:L →+* V:=((seed A).comp (algebraMap L E)).codRestrict V.toSubring (fun c=> by
   change v.val (constant A c)≤1
   by_cases hc:c=0
   · simp [hc,constant]
   · exact (v.constants c hc).le)
 let cκ:=π.comp cV
 have hsmall (b:V) :π b=0↔v.val (b:EC A)<1 :=
   (IsLocalRing.residue_eq_zero_iff b).trans v.val.mem_maximalIdeal_iff
 have hres :π.comp i=cκ.comp j:= by
   apply RingHom.ext
   intro c
   change π (i c)=π (cV (j c))
   rw [← sub_eq_zero,← map_sub,hsmall]
   change v.val (seed A (c:E) - seed A (algebraMap L E (j c)))<1
   rw [← map_sub,hs,S.value γ hγ,hj]
   exact pow_lt_one₀ zero_le (laurent_sub a c ((S.value γ hγ c).symm ▸ c.property)) hn.ne'
 let x :V:=⟨amm A,v.base_regular⟩
 let y :V:=⟨jU A r,v.ordinate_regular⟩
 let:Algebra L κ:=cκ.toAlgebra
 by_contra hconst
 have htrans :Transcendental L (π x) := by
   intro ha
   have hi:=isAlgebraic_iff_isIntegral.mp ha
   obtain ⟨c,hc⟩:=minpoly.mem_range_of_degree_eq_one L (π x)
     (IsAlgClosed.degree_eq_one_of_irreducible L (minpoly.irreducible hi))
   apply hconst
   refine ⟨c,(hsmall (x - cV c)).mp ?_⟩
   rw [map_sub,sub_eq_zero]
   exact hc.symm
 obtain ⟨s,hs'⟩:=extend_phys htrans
 change s.comp phys=eval₂RingHom cκ (π x) at hs'
 obtain ⟨F,hF⟩ : ∃ F:O[X][X],F.map (mapRingHom O.subtype)=A.f := by
   have hm:=(mem_map_range (mapRingHom O.subtype) (p:=A.f)).mpr (fun k =>
     (mem_map_range O.subtype).mpr (fun l=>⟨⟨_,(S.regular γ hγ).1 k l⟩,rfl⟩))
   exact hm
 have hFred:F.map (mapRingHom j)=cLN a 0 A.f := by
   apply Polynomial.ext
   intro k
   apply Polynomial.ext
   intro l
   have h:=congrArg (fun f :E[X][X]=>(f.coeff k).coeff l) hF
   simp only [coeff_map,coe_mapRingHom] at h ⊢
   rw [hj,expansion_coeff,← h]
   rfl
 let b:=phys.comp (mapRingHom j)
 let B:=(cLN a 0 A.f).map phys
 have hB:F.map b=B:= by
   change F.map (phys.comp (mapRingHom j))=(cLN a 0 A.f).map phys
   rw [← Polynomial.map_map,hFred]
 have hFd: (F.map (mapRingHom O.subtype)).natDegree=F.natDegree :=
   natDegree_map_eq_of_injective
     (Polynomial.map_injective O.subtype O.subtype_injective) F
 have hAd:A.d=F.natDegree := by
   change A.f.natDegree=F.natDegree
   rw [← hF,hFd]
 have hBd: (F.map b).natDegree=F.natDegree := by
   rw [hB]
   change ((cLN a 0 A.f).map phys).natDegree=F.natDegree
   exact (natDegree_map_eq_of_injective (f :=phys) (IsFractionRing.injective L[X] FX) _).trans
     ((S.degree γ hγ).trans hAd)
 let g:=revIf r F
 have hg:g.map (mapRingHom O.subtype)=chartEq A r :=
   (map_revIf r _ F hFd).trans (congrArg (revIf r) hF)
 have hg' : g.map b=revIf r B :=
   (map_revIf r b F hBd).trans (congrArg (revIf r) hB)
 let ev :=eval₂RingHom (eval₂RingHom i x) y
 have hcoeff :eval₂RingHom (seed A) (amm A)=(a7W A).comp C :=
   Polynomial.ringHom_ext (fun _=>eval₂_C _ _) (eval₂_X _ _)
 have hval (f :O[X][X]) :
     (ev f :EC A)=KM A r (f.map (mapRingHom O.subtype)) := by
   change V.subtype (f.eval₂ (eval₂RingHom i x) y)= _
   rw [eval_map₂ O.subtype i (seed A) V.subtype rfl,show V.subtype x=amm A from rfl,
     hcoeff]
   rfl
 have hred (f :O[X][X]) :π (ev f)=(f.map b).eval₂ s (π y) := by
   change π (f.eval₂ (eval₂RingHom i x) y) =
     (f.map (phys.comp (mapRingHom j))).eval₂ s (π y)
   rw [eval_map₂ j i cκ π hres,← Polynomial.map_map,eval₂_map (f :=phys),hs']
 have hroot : (revIf r B).eval₂ s (π y)=0:= by
   rw [← hg',← hred]
   have hzero :ev g=0:=Subtype.ext (by rw [hval,hg]; exact chart_root A hd r)
   rw [hzero,map_zero]
 have hzero :π (ev g.derivative)=0:=(hsmall _).2 (by
   rw [hval,← derivative_map,hg]
   exact hpolar)
 rw [hred,← derivative_map,hg'] at hzero
 exact (chart_simple s B (S.separable γ hγ) r (π y) hroot) hzero
end
end qvOlzpd
