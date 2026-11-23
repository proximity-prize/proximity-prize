import ProximityPrize.SubmissionLower.Z62SyBc
import ProximityPrize.SubmissionLower.ZXswmNd
import ProximityPrize.SubmissionLower.Zd8LTIa
import ProximityPrize.SubmissionLower.Z8IF1id
import ProximityPrize.SubmissionLower.ZDI0Pnd
set_option Elab.async false
open _root_ renaming CommRing → za6, Function.Injective → zq4, Nat.sub_le → z7J, Polynomial.X → z7y, Polynomial.coeff_coe → zX3, Polynomial.ext → zXJ, Polynomial.map_C → zrL, Polynomial.map_id → zeh, Polynomial.map_injective → zTo, Polynomial.map_mul → zNl, Polynomial.map_pow → z5m, Polynomial.map_sub → z3A, Polynomial.ringHom_ext → z86, PowerSeries → zpm, PowerSeries.C → zMG, RingHom.id → zz4
set_option maxHeartbeats 500000
section
section
set_option backward.isDefEq.respectTransparency false
namespace qLjY93c
noncomputable section
open Polynomial qps5rle
open cu (L)
open private common_resultant from ProximityPrize.SubmissionLower.ZATKiYa
open private sum_coeff from ProximityPrize.SubmissionLower.Z62SyBc
open private product integralProduct from ProximityPrize.SubmissionLower.ZXswmNd
def cut {R:Type*} [za6 R] (B G:R[X]) :R[X][X] :=
 B.map C+C (z7y:R[X])*G.map C
def det {R:Type*} [za6 R] (F B G:R[X]) (d:ℕ) :R[X] :=
 (F.map C).resultant (cut B G) d d
private theorem cut_map {R E :Type*} [za6 R] [za6 E] (e :R[X] →+* E)
  (B G:R[X]) : (cut B G).map e=B.map (e.comp C)+C (e (z7y:R[X])) *
    G.map (e.comp C) := by
 simp only [cut,Polynomial.map_add,zNl,Polynomial.map_map,zrL]
theorem det_map {R E :Type*} [za6 R] [za6 E] (c:R →+* E)
  (F B G:R[X]) (d:ℕ) :
  (det F B G d).map c=det (F.map c) (B.map c) (G.map c) d:= by
 let e :=mapRingHom c
 have he :e.comp C=C.comp c:=RingHom.ext fun _=>map_C c
 change e (det F B G d)= _
 rw [det,← resultant_map_map _ _ _ _ e,cut_map,map_map,he]
 change _=((F.map c).map C).resultant ((B.map c).map C +
  C (z7y:E[X])*(G.map c).map C) d d
 rw [show e (z7y:R[X])=z7y from map_X c,
  map_map c C F,map_map c C B,map_map c C G]
theorem det_eval {R E :Type*} [za6 R] [za6 E] (c:R →+* E)
   (F B G:R[X]) (d:ℕ) (u:E) :
   (det F B G d).eval₂ c u =
     (F.map c).resultant (B.map c+C u*G.map c) d d:= by
 let e :=eval₂RingHom c u
 have he :e.comp C=c:=eval₂RingHom_comp_C c u
 change e (det F B G d)= _
 rw [det,← resultant_map_map _ _ _ _ e,cut_map,map_map,he]
 rw [show e (z7y:R[X])=u from eval₂_X c u]
theorem det_zero {R E :Type*} [za6 R] [za6 E] (c:R →+* E)
   (F B G:R[X]) {d:ℕ} (hd:d≠0)
   (hF:F.natDegree≤d) (hB:B.natDegree≤d) (hG:G.natDegree≤d) {y u:E}
   (hf :F.eval₂ c y=0) (hg:B.eval₂ c y+u*G.eval₂ c y=0) :
   (det F B G d).eval₂ c u=0:= by
 rw [det_eval]
 exact common_resultant _ _ (natDegree_map_le.trans hF)
   ((natDegree_add_le _ _).trans (max_le (natDegree_map_le.trans hB)
     ((natDegree_C_mul_le _ _).trans (natDegree_map_le.trans hG))))
   hd (zz4 E) y (by simpa [eval₂_id,eval_map] using hf)
   (by simpa [eval₂_id,eval_map] using hg)
theorem coeff_seed (f :SeedSeries[X][X]) (i j:ℕ) :
   ((seedDerivative f).coeff i).coeff j =
     LaurentSeries.derivative L ((f.coeff i).coeff j) := by
 unfold seedDerivative
 rw [sum_coeff _ (by simp [Polynomial.sum_def]),sum_coeff _ (map_zero _)]
theorem degree_seed (f :SeedSeries[X][X]) : (seedDerivative f).natDegree≤f.natDegree := by
 apply natDegree_le_iff_coeff_eq_zero.mpr
 intro i hi
 apply zXJ
 intro j
 simp only [coeff_seed,coeff_eq_zero_of_natDegree_lt hi,coeff_zero,map_zero]
abbrev resultant (f :SeedSeries[X][X]) :SeedSeries[X][X] :=
 det f f.derivative (seedDerivative f) f.natDegree
private theorem det_constant (f :SeedSeries[X][X]) :
  (resultant f).coeff 0=f.resultant f.derivative f.natDegree f.natDegree := by
 rw [show (resultant f).coeff 0=(resultant f).eval₂ (zz4 _) 0 from
  (eval₂_at_zero (zz4 (SeedSeries[X]))).symm,det_eval]
 rw [zeh,zeh,Polynomial.C_0,zero_mul,add_zero]
theorem constant (f :SeedSeries[X][X]) (hf :0<f.natDegree) :
   (resultant f).coeff 0 =
     C ((-1)^(f.natDegree*(f.natDegree - 1)/2))*f.leadingCoeff^2*f.discr := by
 rw [det_constant]
 have hdeg:f.derivative.natDegree≤f.natDegree - 1 :=natDegree_derivative_le f
 nth_rw 2 [show f.natDegree=f.natDegree - 1+1 by omega]
 rw [resultant_add_right_deg _ _ _ _ _ hdeg,coeff_natDegree,
   resultant_deriv (natDegree_pos_iff_degree_pos.mp hf)]
 simp only [map_pow,C_neg,C_1]
 ring
theorem normalized (x :L) (f :SeedSeries[X][X])
    (hx :zq4 (physExpansion x)) (hd:0<f.natDegree)
    (hc: (resultant f).coeff 0≠0) (ht:tameDerivative x f) (i:ℕ) :
    vPhysical (physExpansion x ((resultant f).coeff i)) ≤
      vPhysical (physExpansion x ((resultant f).coeff 0)) := by
  let E :=AlgebraicClosure PhysicalSeries
  let a :=algebraMap PhysicalSeries E
  let c:=a.comp (physExpansion x)
  have hci:zq4 c:=a.injective.comp hx
  let F:=f.map c
  let B:=f.derivative.map c
  let G:=(seedDerivative f).map c
  have hF:F.natDegree=f.natDegree :=natDegree_map_eq_of_injective hci _
  have hB:B.natDegree≤F.natDegree := by
    rw [hF]
    exact natDegree_map_le.trans ((natDegree_derivative_le _).trans (z7J _ _))
  have hG:G.natDegree≤F.natDegree := by
    rw [hF]
    exact natDegree_map_le.trans (degree_seed f)
  have ht' (y :E) (hy :y∈F.roots) :
      B.eval y≠0∧IsIntegral vPhysical.valuationSubring (G.eval y/B.eval y) := by
    have hr :f.eval₂ c y=0:= by
      simpa only [F,eval_map,IsRoot] using isRoot_of_mem_roots hy
    have hb:B.eval y≠0:= by
      intro hb
      have hz :=common_resultant f f.derivative (le_refl _)
        ((natDegree_derivative_le _).trans (z7J _ _)) hd.ne' c y hr
        (by simpa only [B,eval_map] using hb)
      exact (map_ne_zero_iff c hci).mpr hc (det_constant f ▸ hz)
    refine ⟨hb,?_⟩
    have hi:=(ht y hr).neg
    simpa only [neg_neg,evalRoot,B,G,eval_map,c,a,E] using hi
  have hn:F≠0:= by
    intro hz
    rw [hz,natDegree_zero] at hF
    omega
  have hp:=product F B G F.natDegree (IsAlgClosed.splits F) hB hG hn (fun y hy=>(ht' y hy).1)
  have hmap : (resultant f).map c=det F B G F.natDegree := by
    rw [hF,det_map]
  change (det F B G F.natDegree).coeff 0≠0 ∧
    det F B G F.natDegree=C ((det F B G F.natDegree).coeff 0) *
      (F.roots.map fun y=>1+Polynomial.X*C (G.eval y/B.eval y)).prod at hp
  rw [← hmap] at hp
  have he :=congrArg (fun p:E[X]=>p.coeff i) hp.2
  rw [coeff_map,coeff_C_mul,coeff_map] at he
  have h0:c ((resultant f).coeff 0)≠0:=(map_ne_zero_iff c hci).mpr hc
  have hi:IsIntegral vPhysical.valuationSubring
      (c ((resultant f).coeff i)/ c ((resultant f).coeff 0)) := by
    rw [he,mul_div_cancel_left₀ _ h0]
    exact integralProduct F.roots (fun y=>G.eval y/B.eval y) (fun y hy=>(ht' y hy).2) i
  let u:=physExpansion x ((resultant f).coeff i)/physExpansion x ((resultant f).coeff 0)
  let e :=IsScalarTower.toAlgHom vPhysical.valuationSubring PhysicalSeries E
  have hu:e u=c ((resultant f).coeff i)/ c ((resultant f).coeff 0) :=map_div₀ a _ _
  have hv :=(Valuation.valuationSubring.integers vPhysical).isIntegral_iff_v_le_one.mp
    ((isIntegral_algHom_iff e e.injective).mp (hu.symm ▸ hi))
  change vPhysical u≤1 at hv
  rw [show u= _/_ from rfl,map_div₀] at hv
  exact (div_le_iff₀ ((vPhysical.pos_iff).mpr ((map_ne_zero_iff _ hx).mpr hc))).mp hv
    |>.trans_eq (one_mul _)
end
end qLjY93c
end
section
set_option backward.isDefEq.respectTransparency false
namespace qLjY93c
noncomputable section
open Polynomial qps5rle
open cu (L)
open q1kuFjb (IntSeries)
open scoped WithZero
abbrev inc:IntSeries →+* SeedSeries :=Subring.subtype _
abbrev red:IntSeries →+* L:=q1kuFjb.residue
theorem physExpansion_eq (x :L) (P:SeedSeries[X]) :
    physExpansion x P=(((P.taylor (algebraMap L SeedSeries x) :SeedSeries[X]) :
      zpm SeedSeries) :PhysicalSeries) := by
  let e :=(HahnSeries.ofPowerSeries ℤ SeedSeries).comp
    (Polynomial.coeToPowerSeries.ringHom:SeedSeries[X] →+* zpm SeedSeries)
  have hC (b:SeedSeries) :e (C b)=HahnSeries.C b:= by
    change (HahnSeries.ofPowerSeries ℤ SeedSeries) ((C b:SeedSeries[X]) :
      zpm SeedSeries)= _
    rw [Polynomial.coe_C,HahnSeries.ofPowerSeries_C]
  have hX:e (z7y:SeedSeries[X])=HahnSeries.single 1 1 := by
    change (HahnSeries.ofPowerSeries ℤ SeedSeries) ((z7y:SeedSeries[X]) :
      zpm SeedSeries)= _
    rw [Polynomial.coe_X,HahnSeries.ofPowerSeries_X]
  have he :physExpansion x=e.comp (taylorAlgHom (algebraMap L SeedSeries x)).toRingHom:= by
    apply z86
    · intro b
      rw [show physExpansion x (C b)=algebraMap SeedSeries PhysicalSeries b from eval₂_C _ _,
        LaurentSeries.algebraMap_apply]
      change _=e ((C b).taylor (algebraMap L SeedSeries x))
      rw [taylor_C,hC]
    · rw [show physExpansion x z7y =
        HahnSeries.single 1 1+algebraMap L PhysicalSeries x from eval₂_X _ _]
      change _=e ((z7y:SeedSeries[X]).taylor (algebraMap L SeedSeries x))
      rw [taylor_X,map_add,hC,hX]
      congr 1
      change (HahnSeries.ofPowerSeries ℤ SeedSeries) (algebraMap L (zpm SeedSeries) x)= _
      rw [PowerSeries.algebraMap_apply,HahnSeries.ofPowerSeries_C]
  exact congrArg (fun e :SeedSeries[X] →+* PhysicalSeries=>e P) he
private theorem physCoeff (x :L) (P:SeedSeries[X]) (i:ℕ) :
  (physExpansion x P).coeff (i:ℤ)=(P.taylor (algebraMap L SeedSeries x)).coeff i:= by
 rw [physExpansion_eq,LaurentSeries.coeff_coe_powerSeries,zX3]
theorem physExpansion_inj (x :L) :zq4 (physExpansion x) := by
 intro a b h
 apply taylor_injective (algebraMap L SeedSeries x)
 ext i
 rw [← physCoeff x,← physCoeff x,h]
def intCenter (x :L) :IntSeries :=
 LaurentSeries.powerSeriesEquivSubring L (zMG x)
@[simp] theorem inc_center (x :L) :inc (intCenter x)=algebraMap L SeedSeries x := by
  change ((LaurentSeries.powerSeriesEquivSubring L (zMG x) :IntSeries) :
   SeedSeries)= _
  rw [LaurentSeries.powerSeriesEquivSubring_coe_apply,HahnSeries.ofPowerSeries_C,
   LaurentSeries.algebraMap_apply]
@[simp] theorem red_center (x :L) :red (intCenter x)=x := by
  simp [intCenter,red,q1kuFjb.residue]
theorem strip (x :L) (R:IntSeries[X][X])
    (hval : ∀ i,vPhysical (physExpansion x ((R.coeff i).map inc)) ≤
      vPhysical (physExpansion x ((R.coeff 0).map inc))) :
    ∃ (k :ℕ) (T:IntSeries[X][X]),
      R=C ((z7y - C (intCenter x))^k)*T ∧
      inc ((T.coeff 0).eval (intCenter x))=initialAt x ((R.coeff 0).map inc) := by
  let t:=intCenter x
  let D:=((R.coeff 0).map inc).taylor (algebraMap L SeedSeries x)
  let k :=D.natTrailingDegree
  have hv :vPhysical (physExpansion x ((R.coeff 0).map inc))≤WithZero.exp (-(k :ℤ)) := by
    rw [physExpansion_eq]
    exact (LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero SeedSeries (D:zpm SeedSeries)).mpr
      (fun i hi=>(zX3 D i).trans (coeff_eq_zero_of_lt_natTrailingDegree hi))
  have hq (i:ℕ) : (z7y - C t)^k∣R.coeff i:= by
    have hz (j:ℕ) (hj:j<k) : ((R.coeff i).taylor t).coeff j=0:= by
      apply (show zq4 inc from Subtype.val_injective)
      rw [← coeff_map,map_taylor,inc_center,← physCoeff,map_zero]
      exact (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero SeedSeries).mp
        ((hval i).trans hv) _ (by exact_mod_cast hj)
    obtain ⟨Q,hQ⟩:=X_pow_dvd_iff.mpr hz
    refine ⟨Q.taylor (-t),?_⟩
    have he :=congrArg (fun P:IntSeries[X]=>P.taylor (-t)) hQ
    simpa only [taylor_taylor,neg_add_cancel,taylor_zero,taylor_mul,taylor_pow,
      taylor_X,C_neg,sub_eq_add_neg] using he
  obtain ⟨T,hT⟩:=(C_dvd_iff_dvd_coeff ((z7y - C t)^k) R).mpr hq
  refine ⟨k,T,hT,?_⟩
  have h0:R.coeff 0=(z7y - C t)^k*T.coeff 0:= by rw [hT,coeff_C_mul]
  have he :D =z7y ^k*((T.coeff 0).map inc).taylor (algebraMap L SeedSeries x) := by
    dsimp only [D]
    rw [h0,zNl,z5m,z3A,Polynomial.map_X,
      zrL,inc_center,taylor_mul,taylor_pow]
    simp [taylor_apply,sub_comp]
  calc
    inc ((T.coeff 0).eval (intCenter x)) =
        (((T.coeff 0).map inc).taylor (algebraMap L SeedSeries x)).coeff 0:= by
      rw [taylor_coeff_zero,eval_map,← inc_center,eval₂_hom]
    _=D.coeff k := by
      rw [he]
      simpa only [Nat.zero_add] using (coeff_X_pow_mul _ k 0).symm
end
end qLjY93c
end
section
set_option backward.isDefEq.respectTransparency false
namespace qLjY93c
noncomputable section
open Polynomial qps5rle
open qe6nVeb (phys)
open cu (L FX)
open q1kuFjb (IntSeries fWQ Ua liftAt_reduce coeff_liftAt expansion_coeff reduced_pair)
open private eval_at_zero from ProximityPrize.SubmissionLower.ZATKiYa
open scoped WithZero
private abbrev lift (f :SeedSeries[X][X]) (h : ∀ i j,vSeed ((f.coeff i).coeff j)≤1) :=
 Ua (AlgHom.id L SeedSeries) f h
private theorem lift_map (f :SeedSeries[X][X]) (h) : (lift f h).map (mapRingHom inc)=f := by
 apply zXJ
 intro i
 apply zXJ
 intro j
 simp only [coeff_map,coe_mapRingHom]
 exact coeff_liftAt (AlgHom.id L SeedSeries) f h i j
private theorem seed_integral (f :SeedSeries[X][X])
   (h : ∀ i j,vSeed ((f.coeff i).coeff j)≤1) :
   ∀ i j,vSeed (((seedDerivative f).coeff i).coeff j)≤1 := by
 intro i j
 rw [coeff_seed,← WithZero.exp_zero]
 apply (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero L (D:=0)).mpr
 intro n hn
 rw [LaurentSeries.derivative_apply,LaurentSeries.hasseDeriv_coeff,Ring.choose_one_right]
 by_cases h0:n+1=0
 · simp [h0]
 · have hz :=(LaurentSeries.valuation_le_iff_coeff_lt_eq_zero L (D:=0)).mp
     (by simpa only [neg_zero,WithZero.exp_zero] using h i j:vSeed _≤WithZero.exp (-(0:ℤ)))
   rw [hz _ (by simpa only [Nat.cast_one] using (show n+1<0 by omega)),smul_zero]
private theorem seed_reduce (f :SeedSeries[X][X]) (h) :
  (lift (seedDerivative f) h).map (mapRingHom red)=residue f 1 := by
 rw [liftAt_reduce]
 apply zXJ
 intro i
 apply zXJ
 intro j
 simp only [expansion_coeff,AlgHom.id_apply,coeff_seed,LaurentSeries.derivative_apply,
  LaurentSeries.hasseDeriv_coeff,Nat.cast_one,zero_add,Ring.choose_one_right,one_smul]
private theorem residual_unit (a :IntSeries) (ha :red a≠0) :IsUnit a := by
 let e :=LaurentSeries.powerSeriesEquivSubring L
 have hu:IsUnit (e.symm a) :=PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr ha)
 have h:=hu.map e.toRingHom
 change IsUnit (e (e.symm a)) at h
 rwa [RingEquiv.apply_symm_apply] at h
private theorem unit_coeff (a m:IntSeries) (b:SeedSeries) (ha :IsUnit a) (hb:b.coeff 0≠0)
  (he :inc m=inc a*b) :red m≠0:= by
 obtain ⟨a,rfl⟩:=ha
 let c:IntSeries := ↑a⁻¹*m
 have hc:inc c=b:= by
  rw [show c= _ *m from rfl,map_mul,he,← mul_assoc,← map_mul,Units.inv_mul,map_one,one_mul]
 have hm:m=(a :IntSeries)*c:= by simp [c,← mul_assoc]
 rw [hm,map_mul,fWQ c]
 refine mul_ne_zero (isUnit_iff_ne_zero.mp (a.isUnit.map red)) ?_
 change (inc c).coeff 0≠0
 rwa [hc]
private theorem guard (x :L) (f :SeedSeries[X][X]) (F:IntSeries[X][X])
   (hF:F.map (mapRingHom inc)=f) (hd:0<f.natDegree)
   (hl: (leadAt x f).coeff 0≠0) (hb: (initialAt x f.discr).coeff 0≠0)
   (m:IntSeries) (hm:inc m=initialAt x ((resultant f).coeff 0)) :red m≠0:= by
 let l:=F.leadingCoeff.eval (intCenter x)
 have he :inc l=leadAt x f := by
   rw [← hF,leadAt,leadingCoeff_map_of_injective
     (zTo _ Subtype.val_injective),coe_mapRingHom,eval_map,← inc_center,
     eval₂_hom]
 have hlu:IsUnit l:= by
   apply residual_unit
   rw [fWQ l]
   change (inc l).coeff 0≠0
   rwa [he]
 have hl0:leadAt x f≠0:= fun hz=>hl (by simp [hz])
 have hlt: (f.leadingCoeff.taylor (algebraMap L SeedSeries x)).trailingCoeff=leadAt x f :=
   (trailingCoeff_eq_coeff_zero (by simpa only [taylor_coeff_zero,leadAt] using hl0)).trans
     (taylor_coeff_zero _ _)
 let n:=f.natDegree*(f.natDegree - 1)/2
 let s :IntSeries :=(-1)^n
 have hs :IsUnit s :=isUnit_one.neg.pow _
 apply unit_coeff (s*l^2) m (initialAt x f.discr) (hs.mul (hlu.pow 2)) hb
 have hsign: (C ((-1 :SeedSeries)^n)).trailingCoeff=inc s := by
   rw [← reverse_leadingCoeff,reverse_C,leadingCoeff_C]
   symm
   change inc ((-1 :IntSeries)^n)= _
   rw [map_pow,map_neg,map_one]
 rw [hm,initialAt,constant f hd,taylor_mul,taylor_mul,taylor_C,taylor_pow,
   pow_two,trailingCoeff_mul,trailingCoeff_mul,trailingCoeff_mul,hlt]
 change (C ((-1 :SeedSeries)^n)).trailingCoeff*(leadAt x f*leadAt x f) *
   initialAt x f.discr=inc (s*l^2)*initialAt x f.discr
 rw [hsign,map_mul inc,map_pow inc l 2,he,pow_two]
theorem proof :qps5rle.c4 := by
 intro x f hint hlead hdisc ht A
 let F:=lift f hint
 let G:=lift (seedDerivative f) (seed_integral f hint)
 have hF:F.map (mapRingHom inc)=f :=lift_map f hint
 have hG:G.map (mapRingHom inc)=seedDerivative f :=lift_map _ _
 have hr :F.map (mapRingHom red)=residue f 0:=liftAt_reduce _ _ _
 have hg:G.map (mapRingHom red)=residue f 1 :=seed_reduce f _
 have hdF:F.natDegree=f.natDegree := by
   rw [← hF,natDegree_map_eq_of_injective (zTo _ Subtype.val_injective)]
 have hd:0<f.natDegree := by
   by_contra! h
   have hz : (residue f 0).natDegree=0:= by
     rw [← hr]
     exact Nat.eq_zero_of_le_zero (natDegree_map_le.trans (hdF.trans_le h))
   exact A.simple (by rw [eq_C_of_natDegree_eq_zero hz,derivative_C,eval₂_zero])
 have hl0:f.leadingCoeff≠0:= fun hz=>hlead (by simp [leadAt,hz])
 have hb0:f.discr≠0:= fun hz=>hdisc (by simp [initialAt,hz])
 have hc: (resultant f).coeff 0≠0:= by
   rw [constant f hd]
   exact mul_ne_zero (mul_ne_zero (C_ne_zero.mpr (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)))
     (pow_ne_zero _ hl0)) hb0
 let R:=det F F.derivative G f.natDegree
 have hR:R.map (mapRingHom inc)=resultant f := by
   rw [det_map,hF,hG,← derivative_map,hF]
 have hRc (i:ℕ) : (R.coeff i).map inc=(resultant f).coeff i:= by
   simpa only [coeff_map,coe_mapRingHom] using congrArg (fun R:SeedSeries[X][X]=>R.coeff i) hR
 have hval (i:ℕ) :vPhysical (physExpansion x ((R.coeff i).map inc)) ≤
     vPhysical (physExpansion x ((R.coeff 0).map inc)) := by
   rw [hRc,hRc]
   exact normalized x f (physExpansion_inj x) hd hc ht i
 obtain ⟨k,T,hT,hm⟩:=strip x R hval
 have hm' : inc ((T.coeff 0).eval (intCenter x))=initialAt x ((resultant f).coeff 0) := by
   rwa [hRc] at hm
 have hu:=guard x f F hF hd hlead hdisc _ hm'
 let S:=T.map (mapRingHom red)
 have hS:R.map (mapRingHom red)=C ((z7y - C x)^k)*S:= by
   rw [hT]
   simp only [S,zNl,zrL,coe_mapRingHom,z5m,
     z3A,Polynomial.map_X,red_center]
 have hS0: (S.coeff 0).eval x≠0:= by
   intro hz
   apply hu
   change ((T.map (mapRingHom red)).coeff 0).eval x=0 at hz
   rwa [coeff_map,coe_mapRingHom,eval_map,← red_center x,eval₂_hom] at hz
 obtain ⟨P,Q,hQ,hPQ,he⟩:=reduced_pair A.delta
 by_cases hqx :Q.eval x≠0
 · exact ⟨P,Q,hqx,he.symm⟩
 have hpx :P.eval x≠0 :=
   (aeval_ne_zero_of_isCoprime hPQ x).resolve_right hqx
 have hp:P≠0:= fun hz=>hpx (by simp [hz])
 have inj:zq4 phys :=IsFractionRing.injective L[X] FX
 have hδ:A.delta≠0:=he ▸ div_ne_zero
   ((map_ne_zero_iff phys inj).mpr hp) ((map_ne_zero_iff phys inj).mpr hQ)
 have hdegG: (G.map (mapRingHom inc)).natDegree=G.natDegree :=
   natDegree_map_eq_of_injective (zTo _ Subtype.val_injective) G
 have hdf : (residue f 0).natDegree≤f.natDegree :=
   hr ▸ natDegree_map_le.trans hdF.le
 have hdb: (residue f 0).derivative.natDegree≤f.natDegree :=
   (natDegree_derivative_le _).trans ((z7J _ _).trans hdf)
 have hdg: (residue f 1).natDegree≤f.natDegree :=
   hg ▸ natDegree_map_le.trans (hdegG.symm.trans_le (hG.symm ▸ degree_seed f))
 have hz : (R.map (mapRingHom red)).eval₂ phys A.delta⁻¹=0:= by
   rw [det_map,hr,hg,← derivative_map,hr]
   refine det_zero phys _ _ _ hd.ne' hdf hdb hdg A.root ?_
   rw [show (residue f 1).eval₂ phys A.w =
     -(A.delta*(residue f 0).derivative.eval₂ phys A.w) from eq_neg_of_add_eq_zero_left A.zD,
     mul_neg,← mul_assoc,inv_mul_cancel₀ hδ,one_mul,add_neg_cancel]
 rw [hS,eval₂_mul,eval₂_C] at hz
 have hx :phys ((z7y - C x)^k)≠0 :=
   (map_ne_zero_iff phys inj).mpr (pow_ne_zero _ (X_sub_C_ne_zero x))
 have hzero :=(mul_eq_zero.mp hz).resolve_left hx
 rw [← he,inv_div] at hzero
 exact False.elim (hS0 (eval_at_zero S x Q P hpx (not_not.mp hqx) hzero))
end
end qLjY93c
end
end
section
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace q82zwcd
noncomputable section
open Polynomial Finset q20JTGa
open scoped Classical
open P5 (K I)
open P5_7_2 (fO)
open q7F2qKe (wX weakAgreement)
open P5_7_7 (sites index_card ic)
open cu (L)


open private output output_dvd output_degree hit_width quotient_degree reduced_word word_determinant det_ne shifted_width gMz from ProximityPrize.SubmissionLower.ZzCHpGc


open private band_degrees from ProximityPrize.SubmissionLower.ZRqikKa
theorem degree_lt (b:fO) :wX b<weakAgreement:= by
 have h:=(band_degrees b).2
 unfold wX weakAgreement
 omega
private theorem bY {D:ℕ} {w:I→K} {T:Finset K} {s :K→K[X]}
   (R:WordRows D w) (hT:T.Nonempty)
   (ha : ∀ γ∈T,weakAgreement≤(sites w s γ).card)
   (hd : ∀ γ∈T,(s γ).natDegree≤D)
   (hn : ∀ γ∈T,output R.r (s γ)≠0) :Nonempty (WordChart D w T s) := by
 choose P hP using output_dvd R.s s
 choose Q hQ using output_dvd R.r s
 have hP' γ:=(hP γ).symm
 have hQ' γ:=(hQ γ).symm
 have hdeg₀ γ (hγ:γ∈T) :=output_degree R.r R.bound₀ (hd γ hγ)
 have hdeg₁ γ (hγ:γ∈T) :=output_degree R.s R.bound₁ (hd γ hγ)
 have hwidth γ (hγ:γ∈T) :=hit_width (hQ' γ) (hdeg₀ γ hγ) (hn γ hγ)
 have hA:weakAgreement≤R.d₀:= by
   obtain ⟨γ,hγ⟩:=hT
   exact (ha γ hγ).trans (hwidth γ hγ)
 have hA' := hA.trans R.order
 have he₀:=shifted_width hA
 have he₁:=shifted_width hA'
 have hwidth' := R.width.trans (congrArg (· + D) index_card)
 refine ⟨⟨R.r.a,R.s.a,R.r.b,R.s.b,R.d₀-weakAgreement,R.d₁-weakAgreement,
   Nat.sub_le_sub_right R.order _,gMz hA hA' hwidth',Eq.mpr (congrArg (ic D R.r.a R.r.b) he₀) R.bound₀,
   Eq.mpr (congrArg (ic D R.s.a R.s.b) he₁) R.bound₁,
   word_determinant R,wordRows_target R,P,Q,?_,?_,fun γ _=>hP' γ,
   fun γ _=>hQ' γ,?_,?_⟩⟩
 · exact fun γ hγ hz=>hn γ hγ (by rw [← hQ' γ,hz,mul_zero])
 · exact fun γ _=>(reduced_word R (hP' γ) (hQ' γ)).1
 · intro γ hγ
   rw [he₀,he₁]
   exact ⟨hwidth γ hγ,quotient_degree (hQ' γ) (hdeg₀ γ hγ),
     quotient_degree (hP' γ) (hdeg₁ γ hγ)⟩
 · exact fun γ _=>(reduced_word R (hP' γ) (hQ' γ)).2
theorem word_chart {D w s} {T:Finset K} (hs :Set.InjOn s (T:Set K))
   (ha : ∀ γ∈T,weakAgreement≤(sites w s γ).card)
   (hd : ∀ γ∈T,(s γ).natDegree≤D) :
   T.card≤1 ∨ ∃ (U:Finset K),U⊆T∧T.card≤U.card+1∧Nonempty (WordChart D w U s) := by
 by_cases hsmall:T.card≤1
 · exact Or.inl hsmall
 obtain ⟨R⟩:=wordRows D w
 let U:=T.filter fun γ=>output R.r (s γ)≠0
 have hU:U⊆T:=filter_subset _ _
 have hn : ∀ γ∈U,output R.r (s γ)≠0:= fun _ h=>(mem_filter.mp h).2
 have hbad: (T.filter fun γ=>output R.r (s γ)=0).card≤1 := by
   refine card_le_one.mpr fun α ha β hb=>hs (mem_filter.mp ha).1 (mem_filter.mp hb).1 ?_
   have ha' := (mem_filter.mp ha).2
   have hb' := (mem_filter.mp hb).2
   have hra :R.r.a≠0:= by
     intro hz
     have hrb:R.r.b=0:= by simpa only [output,hz,zero_mul,zero_add] using ha'
     exact det_ne R (by simp only [q20JTGa.det,hz,hrb,zero_mul,mul_zero,sub_self])
   have he :=ha'.trans hb'.symm
   unfold output at he
   exact zTo _ (FaithfulSMul.algebraMap_injective K L)
     (mul_left_cancel₀ hra (add_right_cancel he))
 have hsize :T.card≤U.card+1 := by
   have h:=card_filter_add_card_filter_not (s :=T) (fun γ=>output R.r (s γ)≠0)
   simp only [not_not] at h
   exact h.symm.le.trans (Nat.add_le_add_left hbad _)
 have hpos :0<U.card:=Nat.pos_of_ne_zero fun hz =>
   hsmall (by simpa only [hz,zero_add] using hsize)
 exact Or.inr ⟨U,hU,hsize,bY R (card_pos.mp hpos)
   (fun γ hγ=>ha γ (hU hγ)) (fun γ hγ=>hd γ (hU hγ)) hn⟩
end
end q82zwcd
end
section
namespace qCe4xzb
noncomputable section
open Polynomial Finset TrivSqZeroExt
open cu (L FX j9)
open P5 (K)
open P5_7_7 (phys)
open qWIOgVd (x x_ne phys_ne)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet Variation)
open qxPDCsa (References)
open qb0hmCe (CurveModel cLN)
open q1kuFjb (IntSeries Ua mapTwice map_liftAt)
open qJai0ob (Dual pair scalar evalAt seriesJet eval_seriesJet pair_fst pair_snd)
open qps5rle (atArc vSeed residue SiteJet)
open private constant jet_constant from ProximityPrize.SubmissionLower.ZFdiUYb
private theorem eval_physical:eval₂RingHom scalar x=phys := by
 apply z86
 · intro c
   exact eval₂_C _ _
 · exact eval₂_X _ _
private theorem eval_inverted (f :L[X][X]) (y :FX) :
  f.eval₂ (eval₂RingHom scalar x⁻¹) (invertX y)=invertX (f.eval₂ phys y) := by
 change _=invertX.toRingHom (f.eval₂ phys y)
 rw [hom_eval₂,invertX_eval]
 rfl
private theorem residue_atArc {E :Type} [Field E] [Algebra L E]
  (a :E →ₐ[L] LaurentSeries L) (f :E[X][X]) (i:ℤ) :
  residue (atArc a f) i=cLN a i f := by
 apply zXJ fun m=>zXJ fun n => ?_
 simp [atArc,q1kuFjb.expansion_coeff]
theorem chart_jet {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
    {F:Sheet Cq z S} {V:Variation F} {D W:ℕ} (A:References V D W)
    (γ:K) (hγ:γ∈V.marks) (hD: (S γ).natDegree≤D) :
    let a :=F.atPlace γ (V.Bp hγ)
    ∃ i:Fin 2,let G:=atArc a (equation F D (A.b i))
      (∀ m n,vSeed ((G.coeff m).coeff n)≤1) ∧
      ∃ (Q:L[X]) (J:SiteJet G 0),
        x^D *invertX (phys (V.num γ)/phys (V.den γ)) = -(J.delta*(phys Q)^(2 :ℕ)) := by
  let a :=F.atPlace γ (V.Bp hγ)
  let P:=j9 (S γ)
  have hP:P.natDegree≤D:=natDegree_map_le.trans hD
  let P' := P.reflect D
  obtain ⟨i,hi⟩ : ∃ i:Fin 2,P'.coeff 0≠A.b i:= by
    by_cases h:P'.coeff 0=A.b 0
    · exact ⟨1,fun e=>(by decide : (0:Fin 2)≠1) (A.infinity_distinct (h.symm.trans e))⟩
    · exact ⟨0,h⟩
  let b:=A.b i
  let Q:=P' - C b
  have hQ:Q.coeff 0≠0:= by simpa only [Q,coeff_sub,coeff_C_zero,sub_ne_zero] using hi
  let qv :=phys Q
  have hq:qv≠0:=phys_ne (fun hz=>hQ (by simp [hz]))
  have hp' : qv+scalar b=x^D *invertX (phys P) := by
    rw [← reflect_physical _ _ hP]
    simp [qv,Q,P',scalar]
  let w:=weightAt F.f D
  let G:=equation F D b
  have hf (m n:ℕ) :vSeed (a ((F.f.coeff m).coeff n))≤1 :=
    (F.value γ (V.Bp hγ) _).symm.trans_le (F.integral γ (V.Bp hγ) m n)
  let f' := Ua a F.f hf
  let G' := ordinateChart (physicalChart f' w D) F.d (constant b)
  let ι:=IntSeries.subtype
  have hb:ι (constant b)=a (algebraMap L Cq.E b) := by
    change (((LaurentSeries.powerSeriesEquivSubring L) (zMG b) :IntSeries) :
      LaurentSeries L)= _
    rw [LaurentSeries.powerSeriesEquivSubring_coe_apply,a.commutes,
      LaurentSeries.algebraMap_apply,PowerSeries.coe_C]
  have hm:mapTwice ι f' = mapTwice a.toRingHom F.f :=map_liftAt a F.f hf
  have hg:mapTwice ι G' = atArc a G:= by
    change mapTwice ι (ordinateChart (physicalChart f' w D) F.d (constant b))= _
    rw [cFo,hm,hb]
    exact (cFo a.toRingHom F.f w D F.d (algebraMap L Cq.E b)).symm
  have hint (m n:ℕ) :vSeed ((((atArc a G).coeff m).coeff n))≤1 := by
    let c:=(G'.coeff m).coeff n
    have hc: ((atArc a G).coeff m).coeff n=(c:LaurentSeries L) := by
      rw [← hg]
      simp only [mapTwice,coe_mapRingHom,coeff_map,c,ι,Subring.subtype_apply]
    rw [hc]
    obtain ⟨u,hu⟩:=(LaurentSeries.powerSeriesEquivSubring L).surjective c
    exact (LaurentSeries.val_le_one_iff_eq_coe L _).mpr
      ⟨u,(LaurentSeries.powerSeriesEquivSubring_coe_apply L u).symm.trans
        (congrArg Subtype.val hu)⟩
  have hintG (m n:ℕ) :vSeed (a ((G.coeff m).coeff n))≤1 := by
    change vSeed (a.toRingHom ((G.coeff m).coeff n))≤1
    simpa only [atArc,coeff_map,coe_mapRingHom] using hint m n
  have hL:G' = Ua a G hintG:= by
    apply zTo (mapRingHom ι) (zTo _ Subtype.val_injective)
    exact hg.trans (map_liftAt a G hintG).symm
  have hc (j:ℕ) : (f'.coeff j).map ι=(F.f.coeff j).map a.toRingHom:= by
    simpa only [mapTwice,coe_mapRingHom,coeff_map] using
      congrArg (fun g: (LaurentSeries L)[X][X]=>g.coeff j) hm
  have hiι:zq4 ι:=Subtype.val_injective
  have hs (j:ℕ) (hj:j∈f'.support) :j∈F.f.support := by
    have hj' : f'.coeff j≠0:=mem_support_iff.mp hj
    exact mem_support_iff.mpr fun h=>hj' ((Polynomial.map_eq_zero_iff hiι).mp
      ((hc j).trans (by simp [h])))
  have hweight (j:ℕ) (hj:j∈f'.support) : (f'.coeff j).natDegree+j*D ≤w:= by
    have he : (f'.coeff j).natDegree=(F.f.coeff j).natDegree := by
      simpa only [natDegree_map_eq_of_injective hiι,natDegree_map_eq_of_injective a.injective]
        using congrArg natDegree (hc j)
    rw [he]
    exact le_sup (f := fun k=>(F.f.coeff k).natDegree+k*D) (hs j hj)
  have hf' : f'.natDegree≤F.d:= by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    exact notMem_support_iff.mp fun h=>(not_lt_of_ge (le_natDegree_of_mem_supp _ (hs j h))) hj
  let J₀:=(cLN a 0 F.f).eval₂ phys (phys P)
  let J₁:=(cLN a 1 F.f).eval₂ phys (phys P)
  let j:=(cLN a 0 F.f).derivative.eval₂ phys (phys P)
  let I (k :ℤ) :=(cLN a k G).eval₂ phys (1/qv)
  let s :=(cLN a 0 G).derivative.eval₂ phys (1/qv)
  let δ₀:=phys (V.num γ)/phys (V.den γ)
  let δ := -(x^D *invertX δ₀)/qv^(2 :ℕ)
  have hJ:J₀=0:=F.root γ (V.Bp hγ)
  have hj:j≠0:=V.simple γ hγ
  have hδ:J₁+δ₀*j=0:= by
    rw [show δ₀ = -(J₁/j) from V.formula γ hγ,neg_mul,div_mul_cancel₀ _ hj,add_neg_cancel]
  have he (u:FX) :
      pair (I 0) (I 1+u*s)=inl ((1/qv)^F.d*x^w) *
        pair (invertX J₀) (invertX J₁+(-(x⁻¹)^D*qv^(2 :ℕ)*u)*invertX j) := by
    let yJet:=pair qv (-(qv^(2 :ℕ)*u))
    let zJet:=pair (1/qv) u
    have hyz :yJet*zJet=1 := by
      apply TrivSqZeroExt.ext <;>
        simp only [yJet,zJet,fst_mul,DualNumber.snd_mul,pair_fst,pair_snd,fst_one,snd_one] <;>
        field_simp [hq] <;> ring
    have hx : (inl x⁻¹:Dual)*inl x=1 := by
      rw [← inl_mul,inv_mul_cancel₀ x_ne,inl_one]
    have hcoord: (inl x⁻¹:Dual)^D *(yJet+inl (scalar b)) =
        pair (invertX (phys P)) (-(x⁻¹)^D*qv^(2 :ℕ)*u) := by
      rw [inl_pow]
      apply TrivSqZeroExt.ext
      · simp only [fst_mul,fst_inl,fst_add,yJet,pair_fst,hp']
        rw [← mul_assoc,← mul_pow,inv_mul_cancel₀ x_ne,one_pow,one_mul]
      · simp only [DualNumber.snd_mul,yJet,fst_inl,snd_inl,snd_add,pair_snd,
          add_zero,zero_mul]
        ring
    have H :=c2S seriesJet (physicalChart f' w D) F.d (constant b)
      (inl x) yJet zJet hyz ((degree_physicalChart _ _ _).trans hf')
    change evalAt seriesJet (inl x) zJet G' = _ at H
    rw [physical_eval seriesJet f' w D _ _ _ hx hweight,jet_constant,hcoord,hL] at H
    change evalAt seriesJet (inl x) (pair (1/qv) u) (Ua a G hintG) =
      zJet^F.d*((inl x :Dual)^w*evalAt seriesJet (inl x⁻¹)
        (pair (invertX (phys P)) (-(x⁻¹)^D*qv^(2 :ℕ)*u)) f') at H
    rw [eval_seriesJet,show f' = Ua a F.f hf from rfl,eval_seriesJet,
      eval_physical,eval_inverted,eval_inverted,eval_inverted] at H
    change pair (I 0) (I 1+u*s)=zJet^F.d*((inl x :Dual)^w *
      pair (invertX J₀) (invertX J₁+(-(x⁻¹)^D*qv^(2 :ℕ)*u)*invertX j)) at H
    rw [hJ,map_zero,inl_pow] at H
    rw [hJ,map_zero]
    apply TrivSqZeroExt.ext
    · simpa [zJet,fst_mul,fst_pow,pair_fst,fst_inl,mul_assoc] using congrArg fst H
    · simpa only [DualNumber.snd_mul,fst_mul,fst_pow,fst_inl,snd_inl,
        zJet,pair_fst,pair_snd,mul_zero,zero_mul,zero_add,add_zero,mul_assoc] using congrArg snd H
  have hI:I 0=0:= by
    simpa only [pair_fst,fst_mul,fst_inl,hJ,map_zero,mul_zero] using congrArg fst (he 0)
  have hcoeff (u:FX) :
      I 1+u*s=((1/qv)^F.d*x^w) *
        (invertX J₁+(-(x⁻¹)^D*qv^(2 :ℕ)*u)*invertX j) := by
    simpa only [pair_snd,pair_fst,DualNumber.snd_mul,fst_inl,snd_inl,zero_mul,add_zero] using
      congrArg snd (he u)
  have hsimple :s≠0:= by
    have H :s=((1/qv)^F.d*x^w)*(-(x⁻¹)^D*qv^(2 :ℕ)*invertX j) := by
      linear_combination hcoeff 1 - hcoeff 0
    rw [H]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (one_div_ne_zero hq)) (pow_ne_zero _ x_ne))
      (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (inv_ne_zero x_ne)))
        (pow_ne_zero _ hq)) (by simpa only [map_zero] using invertX.injective.ne hj))
  have hvel : -(x⁻¹)^D*qv^(2 :ℕ)*δ=invertX δ₀:= by
    dsimp only [δ]
    have hcancel:qv^(2 :ℕ)*(-(x^D *invertX δ₀)/qv^(2 :ℕ)) = -(x^D *invertX δ₀) := by
      field_simp [hq]
    rw [mul_assoc,hcancel,neg_mul_neg,← mul_assoc,← mul_pow,
      inv_mul_cancel₀ x_ne,one_pow,one_mul]
  have htan:I 1+δ*s=0:= by
    have h:=congrArg invertX hδ
    rw [map_add,map_mul,map_zero] at h
    rw [hcoeff δ,hvel,h,mul_zero]
  refine ⟨i,hint,Q,⟨1/qv,δ,⟨1,Q,by simpa only [← coeff_zero_eq_eval_zero] using hQ,?_⟩,
    ?_,?_,?_⟩,?_⟩
  · change 1/qv=phys 1/phys Q
    rw [map_one]
  · rw [residue_atArc]
    exact hI
  · rw [residue_atArc]
    exact hsimple
  · rw [residue_atArc,residue_atArc]
    exact htan
  · change x^D *invertX δ₀ = -(δ*qv^(2 :ℕ))
    dsimp only [δ]
    rw [div_mul_cancel₀ _ (pow_ne_zero _ hq),neg_neg]
end
end qCe4xzb
end
section
namespace qCe4xzb
noncomputable section
open Polynomial
open cu (L)
open P5 (K p)
open P5_7_7 (phys)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet)
open qxPDCsa (infinityRef)
open qb0hmCe (CurveModel)
open qps5rle (SeedSeries atArc initialAt leadAt tameDerivative vSeed)
open q14iMuc (discr_map initialAt_map coeff_nonzero_of_val_eq)

def c1 :Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
    (F:Sheet Cq z S) (D:ℕ) (b:L),F.d<p →
    (infinityRef F D b).coeff 0≠0 →
    (equation F D b).discr.trailingCoeff=F.f.discr.leadingCoeff
def c2 :Prop :=
  ∀ f :SeedSeries[X][X],0<f.natDegree→f.natDegree<p →
    leadAt 0 f≠0→f.discr≠0→tameDerivative 0 f
theorem of_children (disc:c1) (tame :c2) :qxPDCsa.c5:= by
 intro q Cq z S F V D W A hp _ γ hγ hgood hD
 obtain ⟨i,hint,Q,J,htan⟩:=chart_jet A γ hγ hD
 let b:=A.b i
 let a :=F.atPlace γ (V.Bp hγ)
 let G:=equation F D b
 let g:=atArc a G
 have hmap :=zTo a.toRingHom a.injective
 have ⟨hdeg,hlead⟩:=equation_degree F D b (A.infinity_ne i)
 have hd:g.natDegree=F.d :=
  (natDegree_map_eq_of_injective hmap G).trans hdeg
 have hu (c:Cq.E) (hc: (F.place γ).value c=1) :vSeed (a c)=1 :=
  (F.value γ (V.Bp hγ) c).symm.trans hc
 have hl:leadAt 0 g=a ((infinityRef F D b).coeff 0) := by
  rw [leadAt,map_zero,← coeff_zero_eq_eval_zero]
  change ((G.map (mapRingHom a.toRingHom)).leadingCoeff).coeff 0= _
  rw [leadingCoeff_map_of_injective hmap,coe_mapRingHom,coeff_map,hlead]
  rfl
 have hb: (leadAt 0 g).coeff 0≠0:= by
  rw [hl]
  exact coeff_nonzero_of_val_eq (hu _ (hgood.2.2 i))
 have ha :initialAt 0 g.discr=a F.f.discr.leadingCoeff := by
  change initialAt 0 ((G.map (mapRingHom a.toRingHom)).discr)= _
  rw [discr_map _ hmap _ (hdeg.symm ▸ F.positive)]
  change initialAt 0 (G.discr.map a.toRingHom)= _
  rw [initialAt_map,initialAt,map_zero,taylor_zero,disc F D b hp (A.infinity_ne i)]
 have hdisc: (initialAt 0 g.discr).coeff 0≠0:= by
  rw [ha]
  exact coeff_nonzero_of_val_eq (hu _ hgood.1)
 have ht:=tame g (hd.symm ▸ F.positive) (hd.symm ▸ hp)
  (fun hz=>hb (by simp [hz]))
  (fun hz=>hdisc (by simp [initialAt,hz]))
 have hr :=qLjY93c.proof 0 g hint hb hdisc ht J
 apply degree_of_regular (V.den_ne γ hγ)
 rw [htan]
 obtain ⟨n,d,hd₀,hr⟩:=hr
 refine ⟨-(n*Q^2),d,hd₀,?_⟩
 change -(J.delta*(phys Q)^(2 :ℕ))=phys (-(n*Q^2))/phys d
 change J.delta=phys n/phys d at hr
 rw [hr,map_neg,map_mul,map_pow,div_mul_eq_mul_div₀,neg_div]
end
end qCe4xzb
end
end
