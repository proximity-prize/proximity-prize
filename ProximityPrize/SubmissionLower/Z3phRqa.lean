import ProximityPrize.SubmissionLower.ZpWrDCd
import ProximityPrize.SubmissionLower.ZKxCNpa
import ProximityPrize.SubmissionLower.ZnsYgUd
import ProximityPrize.SubmissionLower.ZGDv7Ub
import ProximityPrize.SubmissionLower.ZW8Nc6b
set_option Elab.async false
set_option maxHeartbeats 550000
section
set_option backward.isDefEq.respectTransparency false
namespace qrX9S3b
noncomputable section
open Polynomial
open cu (L)
open P5 (p)
open qqV3gre qCtoYwb
open qgpYCte (changeOrdinate changeOrdinate_coeff_top changeOrdinate_degree)
open qb8HqGc (covariance)
open q14iMuc (discr_map discr_scale)
open q0n1P7d (eval_integral)
private theorem derivative_data {R E :Type*} [CommRing R] [Field E] (j:R →+* E)
  (Q:R[X]) (w:E) (hm:Q.Monic) (hw:Q.eval₂ j w=0)
  (hd:0<Q.natDegree) (hc:IsUnit Q.discr) :
  Q.derivative.eval₂ j w≠0∧j.IsIntegralElem (Q.derivative.eval₂ j w)⁻¹:= by
 have hr :IsUnit (Q.resultant Q.derivative Q.natDegree (Q.natDegree-1)) := by
  rw [resultant_deriv (natDegree_pos_iff_degree_pos.mp hd),hm.leadingCoeff,mul_one]
  exact ((isUnit_one.neg:IsUnit (-1 :R)).pow _).mul hc
 obtain ⟨c,e,-,-,he⟩:=exists_mul_add_mul_eq_C_resultant Q Q.derivative le_rfl
  (natDegree_derivative_le Q) (Or.inl hd.ne')
 have h:=congrArg (eval₂RingHom j w) he
 simp only [map_add,map_mul,coe_eval₂RingHom,eval₂_C,hw,zero_mul,zero_add] at h
 obtain ⟨r,hr⟩:=hr
 have ht:Q.derivative.eval₂ j w*(e.eval₂ j w*j (↑r⁻¹:R))=1 := by
  rw [← mul_assoc,h,← hr,← map_mul,Units.mul_inv,map_one]
 refine ⟨fun hz=>one_ne_zero (ht.symm.trans (by rw [hz,zero_mul])),?_⟩
 rw [inv_eq_of_mul_eq_one_right ht]
 exact (eval_integral j ⟨Q,hm,hw⟩ e).mul j j.isIntegralElem_map
private def chartMatrix (a b:tu) :Matrix (Fin 2) (Fin 2) tu := !![-a,b; -1,1]
private theorem cFh {E :Type*} [Field E] (j:tu →+* E)
   (f :tu[X]) (a b:tu) (z :E) (hz :f.eval₂ j z=0) (hb:z - j b≠0) :
   (changeOrdinate f (chartMatrix a b)).eval₂ j ((z-j a)/(z-j b))=0:= by
 let w:=(z-j a)/(z-j b)
 have hw:w*(z-j b)=z-j a :=div_mul_cancel₀ _ hb
 have h : -j a+j b*w=z*(-1+w) := by linear_combination -hw
 change (changeOrdinate f (chartMatrix a b)).eval₂ j w=0
 simp only [changeOrdinate,
   show chartMatrix a b 0 0 = -a from rfl,show chartMatrix a b 0 1=b from rfl,
   show chartMatrix a b 1 0 = -1 from rfl,show chartMatrix a b 1 1=1 from rfl,
   eval₂_finsetSum,eval₂_mul,eval₂_pow,eval₂_add,eval₂_C,eval₂_X,eval₂_neg,eval₂_one,
   map_neg,map_one,one_mul,h,mul_pow]
 rw [eval₂_eq_sum_range] at hz
 calc
   _=(∑ i∈Finset.range (f.natDegree+1),j (f.coeff i)*z^i)*(-1+w)^f.natDegree := by
     rw [Finset.sum_mul]
     refine Finset.sum_congr rfl fun i hi => ?_
     conv_rhs=>rw [← Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)),pow_add]
     ring
   _=0:= by rw [hz,zero_mul]
private theorem local_unit (π:tu) [Fact (Irreducible π)] {a :tu} (ha : ¬ π∣a) :
  IsUnit (algebraMap tu (Local π) a) :=
 IsLocalization.map_units (Local π)
  (⟨a,fun h=>ha (Ideal.mem_span_singleton.mp h)⟩: (primeIdeal π).primeCompl)
private theorem bY (π:tu) [Fact (Irreducible π)] (f :tu[X]) (u v :L)
   (y :EC) (hd:0<f.natDegree) (hp:f.natDegree<p) (huv :u≠v)
   (hy :f.eval₂ (baseIn y) (point y)=0) (hv : ¬ π∣reference f v)
   (hc : ¬ π∣f.discr) :
   ∃ Q: (Local π)[X],Q.Monic∧Q.eval₂ (localIn π y) (ratio y u v)=0 ∧
     0<Q.natDegree∧IsUnit Q.discr := by
 let i:=algebraMap tu (Local π)
 let j:=localIn π y
 have hji:j.comp i=baseIn y := by
   apply RingHom.ext
   intro a
   change algebraMap PhysicalField (Simple y) (algebraMap (Local π) PhysicalField (i a)) =
     algebraMap PhysicalField (Simple y) (algebraMap tu PhysicalField a)
   rw [← IsScalarTower.algebraMap_apply tu (Local π) PhysicalField]
 have hi:Function.Injective i:= fun a b h =>
   baseIn_injective y (by rw [← hji]; exact congrArg j h)
 have hv₀:reference f v≠0:= fun hz=>hv (hz ▸ dvd_zero π)
 have hb:point y - baseIn y (scalar v)≠0:= by
   intro hz
   apply hv₀ (baseIn_injective y ?_)
   rw [map_zero,reference,← eval₂_id,hom_eval₂,RingHom.comp_id,← sub_eq_zero.mp hz]
   exact hy
 let M:=chartMatrix (scalar u) (scalar v)
 let g:=changeOrdinate f M
 have htop: (∑ n∈Finset.range (f.natDegree+1),
     f.coeff n*(M 0 1)^n*(M 1 1)^(f.natDegree-n))=reference f v := by
   rw [reference,eval_eq_sum_range]
   change (∑ n∈Finset.range (f.natDegree+1),
     f.coeff n*(scalar v)^n*(1 :tu)^(f.natDegree-n))= _
   simp only [one_pow,mul_one]
 have hgd:g.natDegree=f.natDegree :=changeOrdinate_degree f M (htop ▸ hv₀)
 have hlead:g.leadingCoeff=reference f v := by
   rw [← coeff_natDegree,hgd,changeOrdinate_coeff_top,htop]
 have hdet:IsUnit M.det:= by
   have hdiff :v-u≠0:=sub_ne_zero.mpr huv.symm
   have he :M.det=scalar (v-u) := by
     rw [show M.det=(-scalar u)*1-scalar v*(-1) from Matrix.det_fin_two_of _ _ _ _]
     simp only [scalar,map_sub]
     ring
   rw [he]
   exact (isUnit_iff_ne_zero.mpr ((map_ne_zero (algebraMap L aQ)).mpr hdiff)).map Polynomial.C
 have hcov :=covariance f M hd hp hdet.ne_zero hgd
 let G:=g.map i
 have hGd:0<G.natDegree :=
   ((natDegree_map_eq_of_injective hi g).trans hgd).symm ▸ hd
 have hGc:IsUnit G.discr := by
   change IsUnit (g.map i).discr
   rw [discr_map i hi g (hgd.symm ▸ hd),hcov,map_mul,map_pow]
   exact ((hdet.map i).pow _).mul (local_unit π hc)
 have hG:IsUnit G.leadingCoeff := by
   change IsUnit (g.map i).leadingCoeff
   rw [leadingCoeff_map_of_injective hi,hlead]
   exact local_unit π hv
 have hroot :G.eval₂ j (ratio y u v)=0:= by
   rw [show G=g.map i from rfl,eval₂_map,hji]
   exact cFh (baseIn y) f (scalar u) (scalar v) (point y) hy hb
 obtain ⟨l,hl⟩:=hG
 let Q:=C (↑l⁻¹:Local π)*G
 have hld: (↑l⁻¹:Local π)≠0:=Units.ne_zero _
 refine ⟨Q,?_,?_,(natDegree_C_mul hld (p:=G)).symm ▸ hGd,?_⟩
 · change (C (↑l⁻¹:Local π)*G).leadingCoeff=1
   rw [leadingCoeff_mul,leadingCoeff_C,← hl,Units.inv_mul]
 · change Q.eval₂ j (ratio y u v)=0
   simp only [Q,eval₂_mul,eval₂_C,hroot,mul_zero]
 · exact (discr_scale _ hld G hGd).symm ▸ (((l⁻¹).isUnit.pow _).mul hGc)
theorem proof :qCtoYwb.c1 := by
 intro π _ f u v y hd hp huv hy h
 let inc:=(Simple y).val.toRingHom
 have hy' : f.eval₂ (baseIn y) (point y)=0:=inc.injective (by
  rw [hom_eval₂,map_zero]
  exact hy)
 have hc : ¬ π∣f.discr := fun h' => h (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h' _) _)
 have hu : ¬ π∣reference f u:= fun h' => h (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h' _) _)
 have hv : ¬ π∣reference f v := fun h' => h (dvd_mul_of_dvd_right h' _)
 obtain ⟨Q,hm,hw,hdeg,hdisc⟩:=bY π f u v y hd hp huv hy' hv hc
 obtain ⟨T,hTm,hTw,-,-⟩:=bY π f v u y hd hp huv.symm hy' hu hc
 have hi: (ratio y u v)⁻¹=ratio y v u:= by rw [ratio,inv_div,ratio]
 obtain ⟨hn,hj⟩:=derivative_data (localIn π y) Q (ratio y u v) hm hw hdeg hdisc
 exact ⟨Q,hm,hw,⟨T,hTm,hi.symm ▸ hTw⟩,hn,hj⟩
end
end qrX9S3b
end
section
set_option backward.isDefEq.respectTransparency false
namespace q0n1P7d
noncomputable section
open Polynomial qqV3gre
open cu (L)
open qxPDCsa (BoundedAt UnitAt finiteRef)
open qziIa4d (seedDerivative)
open qU1uHGd (seedDerivative_coeff)
open q14iMuc (discr_map constant_val_le)
open private discr_val_le from ProximityPrize.SubmissionLower.ZW8Nc6b
open private eval_bound from ProximityPrize.SubmissionLower.ZNiHFkd
open private efc aMX from ProximityPrize.SubmissionLower.Y
open private sum_coeff from ProximityPrize.SubmissionLower.Z62SyBc
open private diff_incl from ProximityPrize.SubmissionLower.ZGDv7Ub
open private cast_le_one from ProximityPrize.SubmissionLower.Z62SyBc
open scoped WithZero
private abbrev Bounded (g:aQ[X]) := ∀ j,seedVal (g.coeff j)≤1
private abbrev incl:GaussRing →+* PhysicalField:=algebraMap _ _
private abbrev constPoly (x :L) :aQ[X] :=C (algebraMap L aQ x)
private theorem coeffField_injective :Function.Injective coeffField :=
 IsFractionRing.injective aQ[X] PhysicalField
private def toGauss (g:aQ[X]) (h:Bounded g) :GaussRing :=
 ⟨coeffField g,gauss_le g h⟩
private theorem discr_unit {G:GaussRing[X]} {f :aQ[X][X]}
  (hm:G.map incl=f.map coeffField) (hd:0<G.natDegree) (hf :0<f.natDegree)
  (h:gauss (coeffField f.discr)=1) :IsUnit G.discr := by
 have hb:=congrArg discr hm
 rw [discr_map _ Subtype.val_injective _ hd,discr_map _ coeffField_injective _ hf] at hb
 exact (Valuation.integer.integers gauss).isUnit_of_one' (hb.symm ▸ h)
private theorem lifted_polynomial {f :aQ[X][X]} (hf : ∀ i,Bounded (f.coeff i)) :
  ∃ G:GaussRing[X],G.map incl=f.map coeffField:= by
 apply (mem_map_rangeS incl).2
 intro i
 refine ⟨toGauss (f.coeff i) (hf i),?_⟩
 change coeffField (f.coeff i)=(f.map coeffField).coeff i
 rw [coeff_map]
private theorem lifted_eval {f :aQ[X][X]} {G:GaussRing[X]}
  (hm:G.map incl=f.map coeffField) (y :EC) :
  G.eval₂ gaussCoeff y=f.eval₂ physicalCoeff y := by
 simpa only [eval₂_map,gaussCoeff,physicalCoeff] using
  congrArg (eval₂ (algebraMap PhysicalField EC) y) hm
private theorem eval_bounded {y :EC} (hy :gaussCoeff.IsIntegralElem y)
  {f :aQ[X][X]} (hf : ∀ i,Bounded (f.coeff i)) :
  gaussCoeff.IsIntegralElem (f.eval₂ physicalCoeff y) := by
 obtain ⟨G,hG⟩:=lifted_polynomial hf
 rw [← lifted_eval hG]
 exact eval_integral gaussCoeff hy G
private theorem value_bounded (g:aQ[X]) (h:Bounded g) :
  gaussCoeff.IsIntegralElem (physicalCoeff g) :=
 gaussCoeff.isIntegralElem_map (x :=toGauss g h)
private theorem seed_bounded {c:aQ} (h:seedVal c≤1) :
  seedVal (LaurentSeries.derivative L c)≤1 := by
 obtain ⟨b,rfl⟩:=(LaurentSeries.val_le_one_iff_eq_coe L c).1 h
 rw [← diff_incl]
 exact (LaurentSeries.val_le_one_iff_eq_coe L _).2 ⟨PowerSeries.derivative b,rfl⟩
private theorem physical_bounded {g:aQ[X]} (h:Bounded g) :Bounded g.derivative := by
 intro j
 rw [coeff_derivative,map_mul,← Nat.cast_succ]
 exact mul_le_one' (h _) (cast_le_one (v :=seedVal) _)
private theorem ref_unit {f :aQ[X][X]} {G:GaussRing[X]}
  (hm:G.map incl=f.map coeffField) (r :L)
  (h:gauss (coeffField (f.eval (constPoly r)))=1) :
  ∃ c:GaussRing,gaussCoeff c=constant r∧IsUnit (G.eval c) := by
 let c:=toGauss (constPoly r) (fun j=> by
  simp only [constPoly,coeff_C]
  split
  · exact constant_val_le r
  · simp)
 refine ⟨c,rfl,(Valuation.integer.integers gauss).isUnit_of_one' ?_⟩
 have hv :incl c=coeffField (constPoly r) :=rfl
 have he :=congrArg (fun g:PhysicalField[X]=>g.eval (incl c)) hm
 rw [eval_map_apply,hv,eval_map_apply] at he
 change gauss (incl (G.eval c))=1
 rw [he]
 exact h
private theorem seed_logs (f :aQ[X][X]) (t:aQ[X]) (u v :L)
   (hf : ∀ i,Bounded (f.coeff i)) (ht:Bounded t) (hd:0<f.natDegree)
   (hl:gauss (coeffField f.leadingCoeff)=1) (hc:gauss (coeffField f.discr)=1)
   (hu:gauss (coeffField (f.eval (constPoly u)))=1)
   (hv :gauss (coeffField (f.eval (constPoly v)))=1) :
   integralLogs gaussCoeff f t u v := by
 intro y hy
 obtain ⟨G,hG⟩:=lifted_polynomial hf
 have hdegree :=congrArg natDegree hG
 rw [natDegree_map_eq_of_injective Subtype.val_injective,
   natDegree_map_eq_of_injective coeffField_injective] at hdegree
 have hdG:0<G.natDegree :=hdegree.symm ▸ hd
 have hlead:=congrArg leadingCoeff hG
 rw [leadingCoeff_map_of_injective Subtype.val_injective,
   leadingCoeff_map_of_injective coeffField_injective] at hlead
 have hlG:IsUnit G.leadingCoeff :=
   (Valuation.integer.integers gauss).isUnit_of_one' (hlead.symm ▸ hl)
 have hyG:G.eval₂ gaussCoeff y=0:=(lifted_eval hG y).trans hy
 have hi:=root_integral gaussCoeff hyG hlG
 have hder :G.derivative.map incl=f.derivative.map coeffField:= by
   rw [← derivative_map,← derivative_map,hG]
 have hInv :=derivative_inverse gaussCoeff hyG hi hdG hlG (discr_unit hG hdG hd hc)
 rw [lifted_eval hder] at hInv
 obtain ⟨a,ha,hau⟩:=ref_unit hG u hu
 obtain ⟨b,hb,hbv⟩:=ref_unit hG v hv
 have hlog:=(ref_inverse gaussCoeff hyG hi a hau).sub gaussCoeff
   (ref_inverse gaussCoeff hyG hi b hbv)
 rw [ha,hb] at hlog
 have hs :=eval_bounded hi (f :=seedDerivative f) (fun i j=> by
   rw [seedDerivative_coeff]
   exact seed_bounded (hf i j))
 have hx :=eval_bounded hi (f :=physicalDerivative f) (fun i=> by
   rw [physicalDerivative,sum_coeff _ (derivative_zero :derivative (0:aQ[X])=0)]
   exact physical_bounded (hf i))
 have htSeed :Bounded (seedDiff t) := fun j=> by
   rw [seedDiff,sum_coeff _ (map_zero _)]
   exact seed_bounded (ht j)
 have s :=(hs.mul gaussCoeff hInv).neg gaussCoeff
 have x :=(hx.mul gaussCoeff hInv).neg gaussCoeff
 unfold logCuts
 dsimp only
 simp only [div_eq_mul_inv]
 exact ⟨(value_bounded t ht).mul gaussCoeff (s.mul gaussCoeff hlog),
   ((value_bounded t.derivative (physical_bounded ht)).mul gaussCoeff
     (s.mul gaussCoeff hlog)).sub gaussCoeff
     ((value_bounded (seedDiff t) htSeed).mul gaussCoeff (x.mul gaussCoeff hlog))⟩
theorem proof :qqV3gre.c2 := by
  intro q Cq z S F V D W A t _ ht γ hγ hg
  dsimp only
  intro hphys
  let hmark :=V.Bp hγ
  let a :=F.atPlace γ hmark
  let w:=(F.place γ).value
  let g:=arcEquation a F.f
  have hw (i j:ℕ) :w ((F.f.coeff i).coeff j)≤1 :=F.integral γ hmark i j
  have transfer {Q:Cq.E[X]} (hQ:BoundedAt w Q 1) :Bounded (Q.map a.toRingHom) := by
    intro j
    rw [coeff_map]
    exact (F.value γ hmark _).symm.le.trans (hQ j)
  have unit {Q:Cq.E[X]} (hQ:BoundedAt w Q 1) (hunit :UnitAt F γ Q.leadingCoeff) :
      gauss (coeffField (Q.map a.toRingHom))=1 :=
    base_unit (gauss_le _ (transfer hQ)) (j:= Q.natDegree) (by
      rw [coeff_map,coeff_natDegree]
      exact (F.value γ hmark _).symm.trans hunit)
  have hf (i:ℕ) :Bounded (g.coeff i) := by
    change Bounded ((F.f.map (mapRingHom a.toRingHom)).coeff i)
    rw [coeff_map,coe_mapRingHom]
    exact transfer (hw i)
  have hφ:=Polynomial.map_injective a.toRingHom a.injective
  have hdeg:0<g.natDegree := by
    change 0<(F.f.map (mapRingHom a.toRingHom)).natDegree
    rw [natDegree_map_eq_of_injective hφ]
    exact F.positive
  have hlead:gauss (coeffField g.leadingCoeff)=1 := by
    change gauss (coeffField (F.f.map (mapRingHom a.toRingHom)).leadingCoeff)=1
    rw [leadingCoeff_map_of_injective hφ,coe_mapRingHom]
    apply unit (hw F.d)
    change w ((F.f.coeff F.d).leadingCoeff)=1
    rw [F.normalized,map_one]
  have hdisc:BoundedAt w F.f.discr 1 := fun j =>
    (aMX w _ j).trans (by
      change efc w F.f.discr≤1
      simpa only [one_pow] using discr_val_le (efc w) F.f F.positive 1
        (fun i=>Finset.sup_le fun k _=>hw i k))
  have hdunit :gauss (coeffField g.discr)=1 := by
    change gauss (coeffField (F.f.map (mapRingHom a.toRingHom)).discr)=1
    rw [discr_map _ hφ _ F.positive,coe_mapRingHom]
    exact unit hdisc hg.1
  have href (i:Fin 2) :BoundedAt w (finiteRef F (A.a i)) 1 :=
    eval_bound (F.place γ) F.f (A.a i) hw
  have hrunit (i:Fin 2) :gauss (coeffField (g.eval (constPoly (A.a i))))=1 := by
    have he :=eval_map_apply (p:=F.f) (mapRingHom a.toRingHom)
      (C (algebraMap L Cq.E (A.a i)))
    have hk :a.toRingHom (algebraMap L Cq.E (A.a i)) =
        algebraMap L aQ (A.a i) :=a.commutes _
    rw [coe_mapRingHom,map_C,hk] at he
    change g.eval (constPoly (A.a i))=(finiteRef F (A.a i)).map a.toRingHom at he
    rw [he]
    exact unit (href i) (hg.2.1 i)
  have ht' : Bounded (t.map a.toRingHom) := by
    apply transfer (ht.bound w 1 ?_)
    intro j
    have hv (Q:Cq.E[X]) (hQ:BoundedAt w Q 1) :efc w Q≤1 :=
      Finset.sup_le fun k _=>hQ k
    apply (aMX w _ j).trans
    change efc w (_ *_ *_)≤1
    rw [map_mul,map_mul]
    exact mul_le_one' (mul_le_one' (hv _ hdisc) (hv _ (href 0))) (hv _ (href 1))
  have hseed :=seed_logs g (t.map a.toRingHom) (A.a 0) (A.a 1)
    hf ht' hdeg hlead hdunit (hrunit 0) (hrunit 1)
  intro y hy
  exact ⟨descend (hphys y hy).1 (hseed y hy).1,descend (hphys y hy).2 (hseed y hy).2⟩
end
end q0n1P7d
end
