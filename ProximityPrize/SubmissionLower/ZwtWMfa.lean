import ProximityPrize.SubmissionLower.ZQBQYdc
set_option Elab.async false
open _root_ renaming CommRing → za6, Function.Injective → zq4, Function.comp_def → zQM, Multiset → zCZ, Multiset.map_congr → zu2, Multiset.map_cons → z8u, Multiset.map_map → zDN, Multiset.prod_cons → zwb, Polynomial.X → z7y, Polynomial.map_injective → zTo, PowerSeries → zpm, PowerSeries.coeff → z2o, RingHom.congr_fun → zLs
section
namespace qJFdYUc
noncomputable section
open Polynomial q2TwyLa
def line {R:Type*} [za6 R] (a b:R) :R[X][X] :=
 C (z7y - C b)-Polynomial.X*C (C a)
def lines {R:Type*} [za6 R] (s :zCZ (R×R)) :R[X][X] :=
 (s.map fun z=>line z.1 z.2).prod
def rootPoly {R:Type*} [za6 R] (s :zCZ (R×R)) :R[X] :=
 (s.map fun z=>z7y - C z.1).prod
def mapPairs {R S:Type*} (e :R→S) (s :zCZ (R×R)) :zCZ (S×S) :=
 s.map fun z=>(e z.1,e z.2)
theorem map_lines {R S:Type*} [za6 R] [za6 S] (e :R →+* S)
  (s :zCZ (R×R)) : (lines s).map (mapRingHom e)=lines (mapPairs e s) := by
 change mapRingHom (mapRingHom e) (lines s)= _
 simp [lines,mapPairs,line,map_multiset_prod,zDN]
theorem map_rootPoly {R S:Type*} [za6 R] [za6 S] (e :R →+* S)
  (s :zCZ (R×R)) : (rootPoly s).map e=rootPoly (mapPairs e s) := by
 change mapRingHom e (rootPoly s)= _
 simp [rootPoly,mapPairs,map_multiset_prod,zDN]
set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
theorem pencil_product {E :Type} [Field E] (F G:E[X]) (hs :F.Splits)
    (hd:0<F.natDegree) (hG:G.natDegree≤F.natDegree)
    (hp:F.resultant F.derivative F.natDegree (F.natDegree - 1)≠0) :
    qW F G F.natDegree=coeffEmbed
      (F.leadingCoeff*F.resultant F.derivative F.natDegree (F.natDegree - 1)) *
      lines (F.roots.map fun y=>(y,-(G.eval y/F.derivative.eval y))) := by
  let d:=F.natDegree
  let B:=an1 F G
  have q0:F.resultant F.derivative d (d-1)=F.leadingCoeff^(d-1)*(F.roots.map F.derivative.eval).prod :=
    resultant_eq_prod_eval F F.derivative _ (by have :=natDegree_derivative_lt hd.ne'; omega) hs
  have hn (y :E) (hy :y∈F.roots) :F.derivative.eval y≠0:= by
    intro h
    have hz : (0:E)∈F.roots.map F.derivative.eval :=Multiset.mem_map.mpr ⟨y,hy,h⟩
    exact hp (by rw [q0,Multiset.prod_eq_zero_iff.mpr hz,mul_zero])
  have he (y :E) (hy :y∈F.roots) :
      B.eval (coeffEmbed y)=coeffEmbed (F.derivative.eval y) *
        line y (-(G.eval y/F.derivative.eval y)) := by
    have q1 :=congrArg (coeffEmbed:E →+* E[X][X])
      (div_mul_cancel₀ (G.eval y) (hn y hy))
    simp only [B,an1,eval_add,eval_sub,eval_mul,eval_C,eval_X,eval_map,eval₂_hom,line]
    simp only [map_mul,coeffEmbed,RingHom.comp_apply,map_neg,map_sub] at q1 ⊢
    linear_combination -(q1)
  have hi:zq4 (coeffEmbed:E →+* E[X][X]) :=C_injective.comp C_injective
  have hB:B.natDegree≤d:=cutter_degree F G hd le_rfl hG
  have hP:=resultant_eq_prod_eval (F.map coeffEmbed) B d hB (hs.map coeffEmbed)
  rw [natDegree_map_eq_of_injective hi,hs.roots_map coeffEmbed,
    leadingCoeff_map_of_injective hi,zDN] at hP
  change (F.map coeffEmbed).resultant B d d= _
  rw [hP]
  change coeffEmbed F.leadingCoeff^d*(F.roots.map fun y=>B.eval (coeffEmbed y)).prod= _
  have hm: (F.roots.map fun y=>coeffEmbed (F.derivative.eval y)).prod =
      coeffEmbed (F.roots.map F.derivative.eval).prod:= by
    rw [map_multiset_prod,zDN]
    rfl
  have hscalar :F.leadingCoeff^d*(F.roots.map F.derivative.eval).prod =
      F.leadingCoeff*F.resultant F.derivative d (d-1) := by
    rw [q0,← mul_assoc,← pow_succ',Nat.sub_add_cancel hd]
  have hlines :lines (F.roots.map fun y=>(y,-(G.eval y/F.derivative.eval y))) =
      (F.roots.map fun y=>line y (-(G.eval y/F.derivative.eval y))).prod:= by
    rw [lines,zDN]; rfl
  rw [zu2 rfl he,Multiset.prod_map_mul,hm,← mul_assoc,
    ← (coeffEmbed:E →+* E[X][X]).map_pow,← (coeffEmbed:E →+* E[X][X]).map_mul,
    hscalar,hlines]
end
end qJFdYUc
end
section
set_option autoImplicit true
section
namespace qJFdYUc
noncomputable section
open Polynomial q2TwyLa
open scoped WithZero
attribute [local instance] RootData.field
abbrev pO:i5 →+* aQ:=algebraMap _ _
private theorem seedMap_inj:zq4 pO :=
 HahnSeries.ofPowerSeries_injective (Γ:=ℤ)
private abbrev v :Valuation PhysicalField ℤᵐ⁰:=Valued.v
def physSeries :i5[X] →+* zpm aQ :=
 Polynomial.coeToPowerSeries.ringHom.comp (mapRingHom pO)
theorem generic_eq (a :i5[X]) :ek a=((physSeries a :zpm aQ) :PhysicalField) := by
 exact Polynomial.algebraMap_hahnSeries_apply ℤ _
theorem physSeries_coeff (a :i5[X]) (n:ℕ) :
  z2o n (physSeries a)=pO (a.coeff n) := by
 change z2o n ((a.map pO:aQ[X]) :zpm aQ)= _
 rw [Polynomial.coeff_coe,coeff_map]
theorem generic_inj:zq4 ek :=
 (Polynomial.algebraMap_hahnSeries_injective ℤ).comp (zTo _ seedMap_inj)
private theorem physSeries_X:physSeries (z7y:i5[X])=PowerSeries.X:= by
 change (((z7y:i5[X]).map pO:aQ[X]) :zpm aQ)= _
 rw [map_X,Polynomial.coe_X]
theorem physical_dvd (a :i5[X]) (n:ℕ)
  (h:v (ek a/ek ((z7y:i5[X])^n))≤1) :
  (z7y:i5[X])^n∣a := by
 have hx :v (ek ((z7y:i5[X])^n))=WithZero.exp (-(n:ℤ)) := by
  rw [generic_eq,map_pow,physSeries_X,PowerSeries.coe_pow,LaurentSeries.valuation_X_pow]
 have hle :v (ek a)≤WithZero.exp (-(n:ℤ)) := by
  rw [map_div₀,hx,div_le_iff₀ (by simp),one_mul] at h
  exact h
 rw [generic_eq] at hle
 apply X_pow_dvd_iff.mpr
 intro j hj
 apply seedMap_inj
 rw [map_zero,← physSeries_coeff]
 exact LaurentSeries.coeff_zero_of_lt_intValuation aQ hle hj
variable {f :i5[X][X]} (D:RootData f)
def seriesLift:zpm aQ →+* D.place :=
  (D.incl.comp (HahnSeries.ofPowerSeries ℤ aQ)).codRestrict D.place.toSubring fun a =>
    (D.restricts (a :PhysicalField)).mpr ((LaurentSeries.val_le_one_iff_eq_coe aQ _).mpr ⟨a,rfl⟩)
def intoPlace :i5[X] →+* D.place :=(seriesLift D).comp physSeries
theorem subtype_intoPlace :
  D.place.subtype.comp (intoPlace D)=D.incl.comp ek:= by
 exact RingHom.ext fun a=>congrArg D.incl (generic_eq a).symm
theorem intoPlace_inj:zq4 (intoPlace D) := by
 intro a b h
 apply generic_inj
 apply D.incl.injective
 change (D.incl.comp ek) a=(D.incl.comp ek) b
 rw [← subtype_intoPlace D]
 exact congrArg D.place.subtype h
abbrev residue :=IsLocalRing.residue D.place
def seedResidue :i5 →+* IsLocalRing.ResidueField D.place :=
 (residue D).comp ((seriesLift D).comp (PowerSeries.C.comp pO))
theorem seedResidue_inj:zq4 (seedResidue D) :=
 ((residue D).comp ((seriesLift D).comp PowerSeries.C)).injective.comp seedMap_inj
theorem intoPlace_residue :
   (residue D).comp (intoPlace D)=(seedResidue D).comp constantCoeff := by
 apply Polynomial.ringHom_ext
 · intro a
   change residue D (seriesLift D (((C a).map pO:aQ[X]) :zpm aQ)) =
     seedResidue D (constantCoeff (C a))
   rw [map_C,Polynomial.coe_C,constantCoeff_apply,coeff_C_zero]
   rfl
 · change residue D (seriesLift D (physSeries z7y))=seedResidue D (constantCoeff z7y)
   rw [physSeries_X,constantCoeff_apply,coeff_X_zero,map_zero,IsLocalRing.residue_eq_zero_iff,D.place.valuation_lt_one_iff]
   have he : (D.place.valuation.comap D.incl).IsEquiv v := by
     apply Valuation.isEquiv_of_val_le_one
     intro a
     change D.place.valuation (D.incl a)≤1↔v a≤1
     rw [D.place.valuation_le_one_iff,D.restricts]
   change D.place.valuation.comap D.incl (↑(PowerSeries.X:zpm aQ))<1
   apply he.lt_one_iff_lt_one.mpr
   rw [← pow_one (↑(PowerSeries.X:zpm aQ) :PhysicalField),
     LaurentSeries.valuation_X_pow,← WithZero.exp_zero]
   exact WithZero.exp_lt_exp.mpr (by norm_num)
theorem residue_intoPlace (a :i5[X]) :
  residue D (intoPlace D a)=seedResidue D (a.coeff 0) :=
 zLs (intoPlace_residue D) a
end
end qJFdYUc
end
section
namespace qJFdYUc
noncomputable section
open Polynomial q2TwyLa
attribute [local instance] RootData.field
theorem integral_product (f :i5[X][X]) (D:RootData f)
    (hd:0<f.natDegree) (hu:f.leadingCoeff.coeff 0≠0) (hp:polar f≠0) :
    ∃ s :zCZ (D.place×D.place),
      s.card=f.natDegree ∧
      (∀ z∈s,residue D z.1=0→ residue D z.2=0) ∧
      f.map (intoPlace D)=C (intoPlace D f.leadingCoeff)*rootPoly s ∧
      (qW f (diff f) f.natDegree).map (mapRingHom (D.incl.comp ek)) =
        coeffEmbed ((D.incl.comp ek) (f.leadingCoeff*polar f)) *
          (lines s).map (mapRingHom D.place.subtype) := by
  let e :=D.incl.comp ek
  let F:=f.map e
  let G:=(diff f).map e
  let J:=f.map (intoPlace D)
  let i:=D.place.subtype
  have hei:zq4 e :=D.incl.injective.comp generic_inj
  have hJ:J.map i=F:= by
    dsimp only [J,i,F]
    rw [map_map,subtype_intoPlace]
  have hlc:J.leadingCoeff=intoPlace D f.leadingCoeff :=
    leadingCoeff_map_of_injective (intoPlace_inj D) _
  have hunit :IsUnit J.leadingCoeff := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit,hlc,residue_intoPlace]
    exact fun h=>hu (seedResidue_inj D (by rw [h,map_zero]))
  have hInt:D.place.valuation.Integers D.place :=⟨D.place.subtype_injective,
    D.place.valuation_le_one,fun {_} h=>⟨⟨_,(D.place.valuation_le_one_iff _).mp h⟩,rfl⟩⟩
  have q1 (y :D.S) (hy :y∈F.roots) :y∈D.place := by
    have hy0:J.eval₂ i y=0:= by
      rw [← eval_map,hJ]
      exact isRoot_of_mem_roots hy
    have hv :D.place.valuation ((J.leadingCoeff :D.S)*y)≤1 :=
      hInt.isIntegral_iff_v_le_one.mp (i.isIntegralElem_leadingCoeff_mul J y hy0)
    rw [map_mul,(D.place.valuation_eq_one_iff _).mp hunit,one_mul] at hv
    exact (D.place.valuation_le_one_iff y).mp hv
  let b:= fun y :D.S => -(G.eval y/F.derivative.eval y)
  have q2 (y :D.S) (hy :y∈F.roots) :D.place.valuation (b y)≤D.place.valuation y := by
    dsimp only [b,F,G]
    rw [derivative_map,eval_map,eval_map]
    exact D.tame y hy
  let q0 (y : {y // y∈F.roots}) :D.place×D.place :=
    (⟨y,q1 y y.property⟩,⟨b y,(D.place.valuation_le_one_iff _).mp
      ((q2 y y.property).trans (D.place.valuation_le_one ⟨y,q1 y y.property⟩))⟩)
  let s :=F.roots.attach.map q0
  have hs :mapPairs i s=F.roots.map fun y=>(y,b y) := by
    dsimp only [s,mapPairs]
    rw [zDN,← Multiset.attach_map_val' F.roots (fun y=>(y,b y))]
    exact zu2 rfl fun _ _=>rfl
  have hF:F.natDegree=f.natDegree :=natDegree_map_eq_of_injective hei _
  refine ⟨s,?_,?_,?_,?_⟩
  · have hS:F.Splits :=D.splits
    simpa only [s,Multiset.card_map,Multiset.card_attach] using hS.natDegree_eq_card_roots.symm.trans hF
  · intro z hz hzero
    obtain ⟨y,_,rfl⟩:=Multiset.mem_map.mp hz
    obtain ⟨a,ha⟩:=(D.place.valuation_le_iff _ _).mp (q2 y y.property)
    have heq : (q0 y).2=a*(q0 y).1 :=Subtype.ext ha.symm
    rw [heq,map_mul,hzero,mul_zero]
  · apply zTo i D.place.subtype_injective
    rw [hJ,Polynomial.map_mul,map_C,map_rootPoly,hs]
    rw [show i (intoPlace D f.leadingCoeff)=F.leadingCoeff from
      (zLs (subtype_intoPlace D) _).trans (leadingCoeff_map_of_injective hei _).symm]
    simpa only [rootPoly,zDN,zQM,Prod.fst] using D.splits.eq_prod_roots
  · have hpol:F.resultant F.derivative F.natDegree (F.natDegree-1)=e (polar f) := by
      rw [hF]
      dsimp only [F]
      rw [derivative_map,resultant_map_map]
      rfl
    have hh:=pencil_product F G D.splits (hF.symm ▸ hd)
      (natDegree_map_le.trans (hF.symm ▸ diff_degree f))
      (hpol.symm ▸ (map_ne_zero_iff e hei).mpr hp)
    rw [pencil_map,← hF,show f.map (D.incl.comp ek)=F from rfl,
      show (diff f).map (D.incl.comp ek)=G from rfl,hh,map_lines,hs,hpol,
      leadingCoeff_map_of_injective hei]
    simp only [map_mul,b,e]
end
end qJFdYUc
end
end
section
set_option autoImplicit true
section
namespace qJFdYUc
noncomputable section
open Polynomial
theorem roots_monic {R:Type*} [za6 R] (s :zCZ (R×R)) :
 (rootPoly s).Monic:=monic_multiset_prod_of_monic _ _ fun z _=>monic_X_sub_C z.1
theorem roots_degree {R:Type*} [za6 R] [Nontrivial R] (s :zCZ (R×R)) :
  (rootPoly s).natDegree=s.card:= by
 simpa [rootPoly,zDN,zQM] using
  (natDegree_multiset_prod_X_sub_C_eq_card (s.map Prod.fst))
theorem lines_zero {R:Type*} [za6 R] (s :zCZ (R×R)) :
  (lines s).coeff 0=rootPoly (s.map Prod.swap) := by
 change constantCoeff (lines s)= _
 simp [lines,rootPoly,map_multiset_prod,zDN,line,constantCoeff_apply]
private theorem line_edge {R:Type*} [za6 R] [IsDomain R] (a b:R)
   (h:a=0→b=0) :
   line a b≠0∧(line a b).natDegree+(z7y - C a).natTrailingDegree=1 ∧
   (line a b).leadingCoeff=monomial (z7y - C a).natTrailingDegree
     (z7y - C a).trailingCoeff := by
 by_cases ha :a=0
 · rw [h ha,ha]
   simp [line,trailingCoeff,monomial_one_one_eq_X]
 · have hc: (Polynomial.X - C a).coeff 0≠0:= by simp [ha]
   have hf :line a b=C (-C a)*Polynomial.X+C (Polynomial.X - C b) := by
     simp only [line,C_neg]
     ring
   have hn : -(C a :R[X])≠0:= by simp [ha]
   have hl:=leadingCoeff_linear (b:=Polynomial.X - C b) hn
   refine ⟨fun hz=>hn (hl.symm.trans (by rw [← hf,hz,leadingCoeff_zero])),?_,?_⟩
   · rw [hf,natDegree_linear hn,natTrailingDegree_eq_zero.mpr (.inr hc),add_zero]
   · rw [hf,hl,trailingCoeff_eq_coeff_zero hc,natTrailingDegree_eq_zero.mpr (.inr hc)]
     simp
theorem lines_edge {R:Type*} [za6 R] [IsDomain R] (s :zCZ (R×R))
   (h : ∀ z∈s,z.1=0→z.2=0) :
   (lines s).natDegree+(rootPoly s).natTrailingDegree=s.card ∧
   (lines s).leadingCoeff=monomial (rootPoly s).natTrailingDegree (rootPoly s).trailingCoeff := by
 induction s using Multiset.induction_on with
 | empty=>simp [lines,rootPoly,trailingCoeff]
 | cons z s ih =>
   have hS:=ih fun w hw=>h w (Multiset.mem_cons_of_mem hw)
   obtain ⟨hn,hd,hl⟩:=line_edge z.1 z.2 (h z (Multiset.mem_cons_self _ _))
   have hnS:lines s≠0:= by
     rw [← leadingCoeff_ne_zero,hS.2]
     exact fun hz=>(roots_monic s).ne_zero (trailingCoeff_eq_zero.mp ((monomial_eq_zero_iff _ _).mp hz))
   have hP: (z7y - C z.1)≠0:=X_sub_C_ne_zero _
   have hsP:rootPoly s≠0:=(roots_monic s).ne_zero
   have hLine :lines (z ::ₘ s)=line z.1 z.2*lines s := by
     simp only [lines,z8u,zwb]
   have hRoot:rootPoly (z ::ₘ s)=(z7y - C z.1)*rootPoly s := by
     simp only [rootPoly,z8u,zwb]
   rw [hLine,hRoot,natDegree_mul hn hnS,natTrailingDegree_mul hP hsP,
     Multiset.card_cons,leadingCoeff_mul,hl,hS.2,trailingCoeff_mul,monomial_mul_monomial]
   exact ⟨by omega,rfl⟩
theorem map_trailing {R S:Type*} [Semiring R] [Semiring S] (e :R →+* S)
  (he :zq4 e) (P:R[X]) :
  (P.map e).natTrailingDegree=P.natTrailingDegree ∧
  (P.map e).trailingCoeff=e P.trailingCoeff := by
 have q0: (P.map e).natTrailingDegree=P.natTrailingDegree := by
  simp only [natTrailingDegree,trailingDegree,support_map_of_injective P he]
 exact ⟨q0,by rw [trailingCoeff,q0,coeff_map,trailingCoeff]⟩
end
end qJFdYUc
end
section
open RingHom renaming comp_apply→qz0
open Polynomial renaming coe_mapRingHom→qz1,map_injective→qz2,map_mul→qz3
namespace qJFdYUc
noncomputable section
open Polynomial q2TwyLa
attribute [local instance] RootData.field
private theorem strip {f :i5[X][X]} (D:RootData f) (P:i5[X][X][X])
    (Q:D.place[X][X]) (n:ℕ)
    (h:P.map (mapRingHom (D.incl.comp ek)) =
      coeffEmbed ((D.incl.comp ek) ((z7y:i5[X])^n)) *
        Q.map (mapRingHom D.place.subtype)) :
    ∃ T:i5[X][X][X],P=coeffEmbed ((z7y:i5[X])^n)*T ∧
      T.map (mapRingHom (intoPlace D))= Q:= by
  let x :=(z7y:i5[X])^n
  let e :=D.incl.comp ek
  have hne :e x≠0:=(map_ne_zero_iff e (D.incl.injective.comp generic_inj)).mpr
    (pow_ne_zero _ X_ne_zero)
  have hd (i j:ℕ) :x∣(P.coeff i).coeff j:= by
    have he :=congrArg (fun p:D.S[X][X]=>(p.coeff i).coeff j) h
    simp only [coeffEmbed,qz0,coeff_C_mul,coeff_map,qz1] at he
    change D.incl (ek ((P.coeff i).coeff j))=e x*((Q.coeff i).coeff j:D.S) at he
    have hh:D.incl (ek ((P.coeff i).coeff j)/ek x)=((Q.coeff i).coeff j:D.S) := by
      rw [map_div₀]
      apply (div_eq_iff hne).mpr
      rw [mul_comm]
      exact he
    apply physical_dvd
    apply (D.restricts _).mp
    rw [hh]
    exact ((Q.coeff i).coeff j).property
  obtain ⟨T,hT⟩:=(C_dvd_iff_dvd_coeff (C x) P).mpr fun i =>
    (C_dvd_iff_dvd_coeff x (P.coeff i)).mpr (hd i)
  refine ⟨T,hT,?_⟩
  apply qz2 (mapRingHom D.place.subtype)
    (qz2 D.place.subtype D.place.subtype_injective)
  rw [map_map,mapRingHom_comp,subtype_intoPlace]
  rw [hT,qz3] at h
  simp only [coeffEmbed,qz0,map_C,qz1] at h
  exact mul_left_cancel₀ (C_ne_zero.mpr (C_ne_zero.mpr hne)) h
theorem proof :q2TwyLa.c2 := by
  intro f hd hu hp D
  let n:=(polar f).natTrailingDegree
  let x :=(z7y:i5[X])^n
  let d:=f.natDegree
  let e :=D.incl.comp ek
  let r :=residue D
  let k :=seedResidue D
  obtain ⟨s,hs,hz,hF,hP⟩:=integral_product f D hd hu hp
  obtain ⟨p,hp'⟩:=(X_pow_dvd_iff (f :=polar f) (n:=n)).mpr
    (fun _ hj=>coeff_eq_zero_of_lt_natTrailingDegree hj)
  have hp0:p.coeff 0=(polar f).trailingCoeff := by
    calc
      p.coeff 0=(x*p).coeff (0+n) :=(coeff_X_pow_mul p n 0).symm
      _=(polar f).trailingCoeff := by rw [Nat.zero_add,← hp']; rfl
  let q:=f.leadingCoeff*p
  have hq:f.leadingCoeff*polar f=x*q:= by rw [hp']; exact mul_left_comm _ _ _
  let Q:=coeffEmbed (intoPlace D q)*lines s
  have hP' : (qW f (diff f) d).map (mapRingHom e) =
      coeffEmbed (e x)*Q.map (mapRingHom D.place.subtype) := by
    dsimp only [Q]
    rw [hP,hq,map_mul,map_mul,mul_assoc,qz3]
    congr 2
    simp only [coeffEmbed,qz0,map_C,qz1]
    exact congrArg (fun a :D.S=>C (C a)) (zLs (subtype_intoPlace D) q).symm
  obtain ⟨T,hT,hQ⟩:=strip D _ Q n hP'
  have hq0:q.coeff 0=f.leadingCoeff.coeff 0*(polar f).trailingCoeff := by
    dsimp only [q]
    rw [mul_coeff_zero,hp0]
  have h0: (T.coeff 0).map (intoPlace D)=C (intoPlace D q)*rootPoly (s.map Prod.swap) := by
    have h:=congrArg (fun a :D.place[X][X]=>a.coeff 0) hQ
    simpa only [coeff_map,qz1,Q,coeffEmbed,qz0,coeff_C_mul,lines_zero] using h
  refine ⟨⟨T,hT,?_,?_,?_⟩⟩
  · rw [← natDegree_map_eq_of_injective (intoPlace_inj D) (T.coeff 0),h0]
    exact (natDegree_C_mul_le _ _).trans_eq (by rw [roots_degree,Multiset.card_map,hs])
  · have he :=congrArg (fun p:D.place[X]=>r (p.coeff d)) h0
    have hm:=(roots_monic (s.map Prod.swap)).coeff_natDegree
    rw [roots_degree,Multiset.card_map,hs] at hm
    simp only [coeff_map,coeff_C_mul,hm,d,mul_one,r,residue_intoPlace] at he
    exact (seedResidue_inj D) (he.trans (congrArg k hq0))
  · let m:=(centre f).natTrailingDegree
    let a :=f.leadingCoeff.coeff 0
    let b:=(polar f).trailingCoeff
    let t:=mapPairs r s
    have ht:t.card=d:=(Multiset.card_map _ _).trans hs
    have hz' (z :IsLocalRing.ResidueField D.place×IsLocalRing.ResidueField D.place)
        (h:z∈t) :z.1=0→z.2=0:= by
      obtain ⟨w,hw,rfl⟩:=Multiset.mem_map.mp h
      exact hz w hw
    have hU: (centre f).map k=C (k a)*rootPoly t:= by
      have h:=congrArg (mapRingHom r) hF
      simpa only [qz1,map_map,intoPlace_residue D,centre,qz3,map_C,
        map_rootPoly,residue_intoPlace,k,r,a,t] using h
    have ha :k a≠0:=(map_ne_zero_iff k (seedResidue_inj D)).mpr hu
    have hM:=(map_trailing k (seedResidue_inj D) (centre f)).1
    have hB:=(map_trailing k (seedResidue_inj D) (centre f)).2
    rw [hU,natTrailingDegree_mul (C_ne_zero.mpr ha) (roots_monic t).ne_zero,
      natTrailingDegree_C,zero_add] at hM
    have hc0: (C (k a)).trailingCoeff=k a := by simp [trailingCoeff,natTrailingDegree_C]
    rw [hU,trailingCoeff_mul,hc0] at hB
    obtain ⟨hdeg,hcoeff⟩:=lines_edge t hz'
    have hde : (lines t).natDegree=d - m:= by change (rootPoly t).natTrailingDegree=m at hM; omega
    have hR:T.map (mapRingHom (k.comp constantCoeff)) =
        coeffEmbed (k (q.coeff 0))*lines t:= by
      have h:=congrArg (mapRingHom (mapRingHom r)) hQ
      simpa only [qz1,map_map,mapRingHom_comp,intoPlace_residue D,Q,
        qz3,coeffEmbed,qz0,map_C,map_lines,
        residue_intoPlace,k,r,t] using h
    have he :=congrArg (fun p: (IsLocalRing.ResidueField D.place)[X][X]=>p.coeff (d-m)) hR
    apply qz2 k (seedResidue_inj D)
    rw [map_map,map_monomial,map_mul]
    change (T.coeff (d-m)).map (k.comp constantCoeff)=monomial m (k b*k (centre f).trailingCoeff)
    simp only [coeff_map,qz1,coeffEmbed,qz0,coeff_C_mul] at he
    rw [he,← hde,coeff_natDegree,hcoeff,hM,C_mul_monomial,hq0,k.map_mul,← hB]
    congr 1
    ring
end
end qJFdYUc
end
end
