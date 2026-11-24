import ProximityPrize.SubmissionLower.Zy3W3oe
import ProximityPrize.SubmissionLower.Z7Epuse
import ProximityPrize.SubmissionLower.ZGvZzVd
import ProximityPrize.SubmissionLower.Z9a2MVc
import ProximityPrize.SubmissionLower.ZInsGkb
import ProximityPrize.SubmissionLower.ZEPBkvd
import ProximityPrize.SubmissionLower.Z7ee2Qb
import ProximityPrize.SubmissionLower.Z8rcaBc
set_option Elab.async false
open _root_ renaming Fin.sum_univ_eq_sum_range → zdx, Finset.le_sup → zZi, Finset.sup_le → zf9, Function.Injective → zq4, IsFractionRing.injective → zxb, Module.finrank → zsE, MvPolynomial.X → z9v, MvPolynomial.le_degreeOf_of_mem_support → zTo, Nat.add_le_add_left → z3b, Nat.add_le_add_right → zlr, Nat.add_mul → zNE, Nat.le_add_right → z8K, Nat.le_of_lt_succ → zeh, Nat.le_of_mul_le_mul_left → zJC, Nat.lt_succ_of_le → zB1, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Nat.zero_le → zD0
section
set_option autoImplicit true
namespace qt5Na8b
noncomputable section
open Polynomial
open P6 (K p blockLength)
open P6_7_3 (Input degree emz)
open cu (L Equation yq)
open qHEUR1a (Raw embed height threshold)
abbrev quota :ℕ:=179740
abbrev modulus :ℕ:=threshold+1+degree
abbrev slope :ℕ:=13900
abbrev rate :ℕ:=qHEUR1a.rate
def weight (F:Raw) :ℕ :=
  F.support.sup fun i=>(F.coeff i).support.sup fun a =>
    ((F.coeff i).coeff a).natDegree+i*degree
def Zk (x :Input) (f :Equation) (γ:K) :Prop :=
  yq f (x.M.label γ) (x.F.scalar γ)=0
def site (x :Input) (γ:K) :Fin 2→L :=
  let z :=algebraMap K L (x.M.label γ)
  ![z,z^p]
def Sheet (F:Raw) :Prop :=
  Irreducible F∧Irreducible (embed F)∧0<F.natDegree∧F.natDegree≤12 ∧
    0<height F∧height F≤130
theorem scalar_deg (x :Input) {γ:K} (hγ:γ∈x.Γ) :
    (x.F.scalar γ).natDegree≤degree :=
  (P6_7.aic x.F hγ).trans (z3b (emz x).2 _)
theorem multiplier_surplus (v :ℕ) :
    (1001*v+1)*(2*v+1)*(106*degree)<3*(1000*v+1)*(v+1)*modulus := by
  have h:3*(1000*v+1)*(v+1)*modulus =
      (1001*v+1)*(2*v+1)*(106*degree) +
      (0xecbbf0c*v^2+0x35bc9047c*v+14438688) := by
    change 3*(1000*v+1)*(v+1)*9533606=(1001*v+1)*(2*v+1)*14162130+_
    ring
  rw [h]
  exact Nat.lt_add_of_pos_right (by positivity)
def polar (e :ℕ) :ℕ:=(6*e-2)*threshold-3*e^2*degree
def lowNumerator (e :ℕ) :ℕ :=
  (7+6*e)*(quota-degree)+2*e*blockLength+polar e
theorem variation_room {e :ℕ} (he :1≤e) (hE :e≤12) :
    e*degree≤threshold∧e<p∧(2*e-1)*threshold-e^2*degree<p ∧
    3*e^2*degree≤(6*e-2)*threshold∧2*threshold-degree≤polar e ∧
    lowNumerator e+(4*e^2+1)*(quota-degree)≤ slope*(quota-degree) := by
  interval_cases e <;> decide
end
end qt5Na8b
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace qt5Na8b
noncomputable section
open Finset
open Polynomial
open P6 (K p)
open cu (L FX Equation)
open P6_7_3 (Input degree)
open qHEUR1a (Raw embed height threshold)
open qbIP9ia
open Y3 (ek)
open private azZ abn cZx fTI from ProximityPrize.SubmissionLower.BJ
open private rawAt_deg from ProximityPrize.SubmissionLower.Z7Epuse
open private product_coord from ProximityPrize.SubmissionLower.ZGvZzVd
private theorem flat_high_at {F:Raw} (hw:threshold<weight F) :
    threshold<wt degree (flatten F) := by
  by_contra! h
  apply hw.not_ge
  classical
  apply zf9 fun j _=>zf9 fun m hm => ?_
  have hc:exps j ((F.coeff j).coeff m).natDegree m∈(flatten F).support :=
    MvPolynomial.mem_support_iff.mpr (by
      rw [flat_coeff]
      exact leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hm))
  simpa only [exps_x,exps_y] using (wt_term degree hc).trans h
private theorem bPb {n:ℕ} (hn:0<n) {F G H B:Flat}
    (he :H*F=G+MvPolynomial.X amm^n*B) (hw:wt degree G<n)
    (x :Input) {γ:K} (hγ:γ∈x.Γ) (hr :Zk x (embed (flatten.symm F)) γ) :
    Zk x (embed (flatten.symm G)) γ:= by
  let z :=x.M.label γ
  let S:=x.F.scalar γ
  let ev :=azZ (abn z p) S
  have hD:S.natDegree≤degree :=scalar_deg x hγ
  have hF:ev (flatten.symm F)=0 :=
    (zxb L[X] FX) (by rw [cZx,map_zero]; exact hr)
  let E :Flat →+* Polynomial L:=ev.comp flatten.symm.toRingHom
  have hX:E (z9v amm)=Polynomial.X:= by
    change ev (flatten.symm (z9v amm))= _
    rw [← flatten_X,RingEquiv.symm_apply_apply,fTI]
  have hF' : E F=0:=hF
  have hrel :=congrArg E he
  rw [map_mul,map_add,map_mul,map_pow,hX,hF',mul_zero] at hrel
  have hdvd: (Polynomial.X:L[X])^n∣ev (flatten.symm G) :=
    ⟨-ev (flatten.symm B),by rw [mul_neg]; exact eq_neg_of_add_eq_zero_left hrel.symm⟩
  have hzero :ev (flatten.symm G)=0:= by
    by_contra hne
    have hle :=natDegree_le_of_dvd hdvd hne
    rw [natDegree_X_pow] at hle
    exact (rawAt_deg hn (by simpa only [RingEquiv.apply_symm_apply] using hw) _ hD).not_ge hle
  unfold Zk
  rw [← cZx,hzero,map_zero]
private theorem top_count: (∑ j:Fin 15,(j:ℕ)*degree)=105*degree := by
  rw [← sum_mul,zdx (fun j:ℕ=>j)]
  have h: (∑ i∈range 15,i)*2=105*2 :=sum_range_id_mul_two 15
  rw [Nat.eq_of_mul_eq_mul_right (by decide :0<2) h]
theorem emK (x :Input) (T:Finset K) (hT:T⊆x.Γ)
    (F:Raw) (hF:Sheet F) (high:threshold<weight F)
    (hroots : ∀ γ∈T,Zk x (embed F) γ) :
    ∃ g:Equation,g.natDegree≤14∧(embed F).resultant g≠0 ∧
      (∀ (j:ℕ) (i:Fin 2),(g.coeff j).degreeOf i ≤
        (if i=0 then 1001 else 2)*height F) ∧
      ∀ γ∈T,Zk x g γ:= by
  classical
  obtain ⟨hi,_,hpos,hdeg,_,_⟩:=hF
  let f :=flatten F
  let v :=height F
  let a :=1001*v
  let b:=2*v
  let I:=Idx 3 (1000*v) v (fun _=>modulus)
  let J:=Idx 15 a b (fun j=>j*degree)
  let Q:=Idx 1 a b (fun _=>degree)
  let mulF:=LinearMap.mulRight L f
  let cut: (I →₀ L) →ₗ[L] Flat :=(rem modulus).comp (mulF.comp rows)
  let pick (j:J) :Exps :=exps j.1.1 (modulus-1-j.1.2) (seedMon j.2.1 j.2.2)
  let test : (I →₀ L) →ₗ[L] (J→L) :=
    (LinearMap.pi fun j=>MvPolynomial.lcoeff L (pick j)).comp cut
  have hf0 : ¬ z9v amm∣f :=physical_not_dvd hi hpos
  have hinj:zq4 cut:= by
    apply (injective_iff_map_eq_zero cut).mpr
    intro H hz
    have hd:=rem_eq modulus (rows H*f)
    change rem modulus (rows H*f)=0 at hz
    rw [hz,zero_add] at hd
    have hh:=((MvPolynomial.X_prime (R:=L) (i:=amm))).pow_dvd_of_dvd_mul_right modulus hf0 ⟨_,hd⟩
    rw [MvPolynomial.X_pow_eq_monomial,MvPolynomial.monomial_one_dvd_iff_modMonomial_eq_zero] at hh
    apply rows_inj
    rw [map_zero]
    apply MvPolynomial.ext
    intro m
    by_cases hm:m∈(rows H).support
    · have hb:=(mem_coord.mp (rows_support H hm)).2.1
      exact (MvPolynomial.mem_support_iff.mp hm (by
        have he :=congrArg (fun A:Flat=>A.coeff m) hh
        rwa [MvPolynomial.coeff_modMonomial_of_not_le _ (Finsupp.single_le_iff.not.mpr hb.not_ge),
          AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] at he)).elim
    · exact MvPolynomial.notMem_support_iff.mp hm
  have stock (H :I →₀ L) {m:Exps} (hm:m∈(cut H).support) :
      m none<15∧m amm< modulus∧m (seed 0)≤a∧m (seed 1)≤b:= by
    have hh:=rem_support hm
    have hs {t:Exps} (ht:t∈(rows H).support) :=mem_coord.mp (rows_support H ht)
    refine ⟨zB1 (product_coord hh.1 (fun t ht=>zeh (hs ht).1)
      (fun t ht=>(flat_deg ht).1.trans hdeg)),hh.2,?_,?_⟩
    · have he :=product_coord hh.1 (fun t ht=>(hs ht).2.2.1) (fun t ht=>(flat_deg ht).2 0)
      change m (seed 0)≤1001*v
      rw [Nat.succ_mul 1000 v]
      exact he
    · have he :=product_coord hh.1 (fun t ht=>(hs ht).2.2.2) (fun t ht=>(flat_deg ht).2 1)
      change m (seed 1)≤2*v
      rw [two_mul]
      exact he
  have narrow (H :test.ker) :wt degree (cut H.val)< modulus := by
    have hM:0< modulus := by decide
    apply Nat.lt_of_le_pred hM
    apply wt_le
    intro m hm
    obtain ⟨hy,hx,ha,hb⟩:=stock H.val hm
    by_contra! hl
    rw [Nat.pred_eq_sub_one] at hl
    have htop:modulus-1-m amm< m none*degree := by omega
    let j:J :=
      ⟨⟨⟨m none,hy⟩,⟨modulus-1-m amm,htop⟩⟩,
        ⟨m (seed 0),zB1 ha⟩,⟨m (seed 1),zB1 hb⟩⟩
    have hj:pick j=m:= by
      change exps (m none) (modulus-1-(modulus-1-m amm)) _=m
      rw [show modulus-1-(modulus-1-m amm)=m amm by omega]
      exact exps_eta m
    have hz :=congrFun (LinearMap.mem_ker.mp H.property) j
    change (cut H.val).coeff (pick j)=0 at hz
    exact MvPolynomial.mem_support_iff.mp hm (hj ▸ hz)
  have hlarge :zsE L (Q →₀ L)<zsE L test.ker := by
    have hdim:zsE L (J→L)+Module.finrank L (Q →₀ L) <
        zsE L (I →₀ L) := by
      rw [Module.finrank_fintype_fun_eq_card,Module.finrank_finsupp_self,
        Module.finrank_finsupp_self]
      simp only [J,Q,I,idx_card,top_count,sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul,one_mul]
      convert multiplier_surplus v using 1 <;> (try dsimp [a,b]) <;> ring
    have hr :=test.finrank_range_add_finrank_ker
    have ht:=test.range.finrank_le
    omega
  have hex : ∃ H :test.ker,IsCoprime (ek (embed F))
      (ek (embed (flatten.symm (cut H.val)))) := by
    by_contra! hall
    let mulQ: (Q →₀ L) →ₗ[L] Flat :=mulF.comp rows
    have hout (H :test.ker) :cut H.val∈mulQ.range := by
      by_cases hz :cut H.val=0
      · rw [hz]
        exact mulQ.range.zero_mem
      have hdiv :=((ba5.efR hi hpos).isCoprime_or_dvd _).resolve_left (hall H)
      obtain ⟨R,hR⟩:=ba5.efO (hi.isPrimitive hpos.ne') hdiv
      have he :=congrArg flatten hR
      rw [RingEquiv.apply_symm_apply,map_mul] at he
      have hf :f≠0:=(map_ne_zero_iff _ flatten.injective).mpr hi.ne_zero
      have hR0:flatten R≠0:=right_ne_zero_of_mul (he ▸ hz)
      have hwt:wt degree (flatten R)<degree := by
        have hc:=narrow H
        rw [he] at hc
        change wt degree (f*flatten R)< modulus at hc
        have hmul :wt degree (f*flatten R)=wt degree f+wt degree (flatten R) :=
          MvPolynomial.weightedTotalDegree_mul _ _ _ hf hR0
        rw [hmul] at hc
        have hhi:threshold<wt degree f :=flat_high_at high
        have hM:modulus=threshold+1+degree :=rfl
        omega
      have hmem:flatten R∈(@rows 1 a b (fun _=>degree)).range := by
        apply rows_range
        intro m hm
        have hsmall:=(wt_term degree hm).trans_lt hwt
        have hj:m none<1 := by
          by_contra! h
          have ht:=ztf degree h
          omega
        have hd (i:Vars) : (flatten R).degreeOf i≤(cut H.val).degreeOf i :=
          by rw [he,MvPolynomial.degreeOf_mul_eq hf hR0]; exact Nat.le_add_left _ _
        refine mem_coord.mpr ⟨hj,by omega,?_,?_⟩
        · exact (zTo _ hm).trans ((hd _).trans
            (MvPolynomial.degreeOf_le_iff.mpr fun t ht=>(stock H.val ht).2.2.1))
        · exact (zTo _ hm).trans ((hd _).trans
            (MvPolynomial.degreeOf_le_iff.mpr fun t ht=>(stock H.val ht).2.2.2))
      obtain ⟨A,hA⟩:=hmem
      exact ⟨A,by change rows A*f= _; rw [hA,he,mul_comm]⟩
    let out:=(cut.comp test.ker.subtype).codRestrict mulQ.range hout
    have ho:zq4 out:= by
      intro H H' hh
      exact Subtype.ext (hinj (congrArg Subtype.val hh))
    exact hlarge.not_ge ((LinearMap.finrank_le_finrank_of_injective ho).trans mulQ.finrank_range_le)
  obtain ⟨H,hcop⟩:=hex
  let G:=cut H.val
  obtain ⟨he,hcaps⟩:=output_bounds (G:=flatten.symm G) (n:=14) (a :=a) (b:=b)
    (by rw [RingEquiv.apply_symm_apply]
        intro m hm
        obtain ⟨hy,_,ha,hb⟩:=stock H.val hm
        exact ⟨Nat.le_of_lt_succ hy,ha,hb⟩)
  refine ⟨embed (flatten.symm G),he,nonzero_resultant hcop,fun j i => ?_,fun γ hγ => ?_⟩
  · by_cases h:i=0 <;> simpa only [a,b,h,ite_true,ite_false] using hcaps j i
  · apply bPb (by decide :0< modulus) (rem_eq modulus (rows H.val*f)) (narrow H) x (hT hγ)
    simpa only [f,RingEquiv.symm_apply_apply] using hroots γ hγ
end
end qt5Na8b
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 12
namespace qt5Na8b
noncomputable section
open Polynomial Finset UniqueFactorizationMonoid
open P6 (K p)
open P6_7_3 (Input)
open qFOgTpd (Mark eHB)
open qQ9yWTb (Curve Usable)
open qHEUR1a (Raw embed height threshold)
open cu (L Jet Equation yq)
open Qt (gY Qc)
open atc (bri bg3)
open akZ (ajz yE)
open scoped Classical BigOperators
open private c2O from ProximityPrize.SubmissionLower.K
open private lift_factor from ProximityPrize.SubmissionLower.ZEXAOre
def c1 :Prop :=
  ∀ (x :Input) (T:Finset K),T⊆x.Γ →
    ∀ F:Raw,Sheet F→weight F≤threshold →
      (∀ γ∈T,Zk x (embed F) γ) →
      ∀ q:Curve,Irreducible q →
        ((T.filter fun γ=>Usable q (site x γ)).card:ℚ) ≤
          ((slope :ℚ)*(height F:ℚ))*q.totalDegree
def c2 :Prop :=qQ9yWTb.c5
private theorem site_inj (x :Input) :zq4 (site x) := by
  intro a b h
  have hz :=congrFun h 0
  change algebraMap K L (x.M.label a)=algebraMap K L (x.M.label b) at hz
  exact sub_left_inj.mp (FaithfulSMul.algebraMap_injective K L hz)
private theorem root_dvd {x :Input} {f g:Equation} {γ:K} (h:f∣g)
    (hr :Zk x f γ) :Zk x g γ:= by
  obtain ⟨a,rfl⟩:=h
  unfold Zk at *
  unfold yq at *
  rw [eval₂_mul,hr,zero_mul]
private theorem low_count {a v :ℕ} (hv :v≤130)
    (h:3*(a :ℚ)≤10*(slope*(v :ℚ))^2) :a≤ rate*v := by
  have h' : 3*a≤10*slope^2*v*v := by
    have he : (10 :ℚ)*(slope*(v :ℚ))^2=(10*slope^2)*(v :ℚ)*v := by ring
    rw [he] at h
    exact_mod_cast h
  have h'' : 10*slope^2*v*v≤3*(rate*v) := calc
    _≤10*slope^2*130*v :=
      ztf v (zBI _ hv)
    _≤_:= by
      rw [← Nat.mul_assoc]
      exact ztf v (by decide)
  exact zJC (h'.trans h'') (by decide)
private theorem d5P (qv :c1) (u7:c2)
    (x :Input) (T:Finset K) (hT:T⊆x.Γ) {f :Equation}
    (hi:Irreducible f) (hpos :0<f.natDegree) (he :f.natDegree≤12)
    (hu:gY f≤130) (hr : ∀ γ∈T,Zk x f γ) :
    T.card≤f.natDegree+rate*gY f := by
  have hz :zq4 x.M.label := fun _ _ h=>sub_left_inj.mp h
  by_cases hzero :gY f=0
  · have hs :=(Qc f 0).mp hzero.le
    obtain ⟨g,hg,hd,hv,hgraph⟩:=P5_7.native_restriction hi.ne_zero (by decide) hs
    exact (P5_7_7.seed_zero_count (z :=x.M.label) (x.F.distinct.mono hT) hg
      (by simpa only [Nat.mul_zero] using hv) (fun γ hγ=>(hgraph _ _).trans (hr γ hγ))).trans
      (hd.trans (z8K _ _))
  obtain ⟨F,hF,hassoc⟩:=lift_factor hi
  have hirr :=hassoc.symm.irreducible hi
  have hdeg: (embed F).natDegree=f.natDegree :=
    le_antisymm (natDegree_le_of_dvd hassoc.dvd hi.ne_zero)
      (natDegree_le_of_dvd hassoc.dvd' hirr.ne_zero)
  have hs :height F=gY f := by
    have aux {g h:Equation} (hne :h≠0) (hd:g∣h) :gY g≤gY h:= by
      obtain ⟨a,rfl⟩:=hd
      rw [Qt.acG (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne)]
      exact z8K _ _
    exact le_antisymm (aux hi.ne_zero hassoc.dvd) (aux hirr.ne_zero hassoc.dvd')
  have hdeg' : (embed F).natDegree=F.natDegree :=
    natDegree_map_eq_of_injective (MvPolynomial.map_injective _
      (zxb cu.L[X] cu.FX)) F
  have hsheet:Sheet F :=
    ⟨hF,hirr,(hdeg'.symm.trans hdeg) ▸ hpos,(hdeg'.symm.trans hdeg) ▸ he,
      hs ▸ Nat.pos_of_ne_zero hzero,hs ▸ hu⟩
  have hroots : ∀ γ∈T,Zk x (embed F) γ:= fun γ hγ=>root_dvd hassoc.dvd' (hr γ hγ)
  suffices hc:T.card≤ rate*height F by
    rw [hs] at hc
    exact hc.trans (Nat.le_add_left _ _)
  by_cases hw:threshold<weight F
  · obtain ⟨g,hg,hp,hgc,hgr⟩:=emK x T hT F hsheet hw hroots
    have hf :=(Qc _ _).mp (le_refl (height F))
    have hdigit : (12*(1000+1)+14)*height F<p :=
      (zBI _ hsheet.2.2.2.2.2).trans_lt (by decide)
    have hh:=qQ9yWTb.count_resultant (e :=12) (E :=14) (cz :=1000) (ct :=1)
      (hdeg.symm ▸ hpos) (hdeg.symm ▸ he) hg hf hgc hp hdigit hz.injOn hroots hgr
    exact hh.trans (calc
      _=((12*(1000+1)+14)+p*(12*(1+1)+14))*height F:= by ring
      _≤_:=ztf _ (by decide))
  · exact low_count hsheet.2.2.2.2.2
      (u7 T (site x) (site_inj x).injOn _ (by positivity)
        (qv x T hT F hsheet (le_of_not_gt hw) hroots))
theorem of_children (qv :c1) (u7:c2) :qFOgTpd.c1 := by
  intro x G D hD hv hcap
  let slice (f :Jet) :=x.Γ.filter (Mark x f)
  let gH :=D.biUnion slice
  refine ⟨gH,?_,fun f hf γ hγ hm=>mem_biUnion.mpr ⟨f,hf,mem_filter.mpr ⟨hγ,hm⟩⟩⟩
  have hb:ajz D 0≤12 :=(hcap 0).trans_eq (by decide)
  have hu:ajz D 2≤130:=(hcap 2).trans_eq (by decide)
  have hcount (f :Jet) (hf :f∈D) :
      (slice f).card≤yE f 0+rate*yE f 2 := by
    obtain ⟨hi,_,_,hseed,_⟩:=hD.factors f hf
    obtain ⟨hC,hF,hp⟩:=c2O hi (hv f hf) hseed
    have h₀:yE f 0=(f.coeff 0).natDegree := by
      change atc.jetDegree f= _
      exact (congrArg atc.jetDegree hC).symm.trans (bri _)
    have h₂:yE f 2=gY (f.coeff 0) := by
      change atc.gY f= _
      rw [← congrArg atc.gY hC,bg3]
      apply le_antisymm
      · exact zf9 fun j _=>(Qc _ _).mp le_rfl j
      · apply (Qc _ _).mpr
        intro j
        by_cases hj:j∈(f.coeff 0).support
        · exact zZi (f := fun i=>((f.coeff 0).coeff i).totalDegree) hj
        · simp [notMem_support_iff.mp hj]
    rw [h₀,h₂]
    refine d5P qv u7 x (slice f) (filter_subset _ _) hF hp ?_ ?_ ?_
    · exact h₀ ▸ ((single_le_sum (f := fun g=>yE g 0) (fun _ _=>zD0 _) hf).trans hb)
    · exact h₂ ▸ ((single_le_sum (f := fun g=>yE g 2) (fun _ _=>zD0 _) hf).trans hu)
    · intro γ hγ
      have h:=(mem_filter.mp hγ).2
      unfold Mark cu.rD at h
      rw [← hC,eval₂_C] at h
      exact h
  calc
    gH.card ≤ ∑ f∈D,(slice f).card:=card_biUnion_le
    _ ≤ ∑ f∈D,(yE f 0+rate*yE f 2) :=
      sum_le_sum hcount
    _=ajz D 0+rate*ajz D 2 := by
      rw [sum_add_distrib,← mul_sum]
      rfl
    _≤12+rate*130:=Nat.add_le_add hb (zBI _ hu)
    _≤12+rate*130+p*130:=z8K _ _
    _≤eHB:= by decide
end
end qt5Na8b
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qoIv1ye
noncomputable section
open qlc9qed (Bank)
open q84jfie
open aR (ao)
open jA Polynomial
open Finset (range sum_congr)
open scoped BigOperators
open private exponent exponent_none exponent_zero bpQ d5n from ProximityPrize.SubmissionLower.B9
open private sum_coeffs from ProximityPrize.SubmissionLower.ZTFKldb
open private Lh Ac auD column column_mem cGZ finite_ambient b6S box_bounds from ProximityPrize.SubmissionLower.P5_7_1_3_1Proof
open private start start_eq delta columnsAt columns_le width_count from ProximityPrize.SubmissionLower.ZInsGkb
private theorem ds8 (b:Bank) (h U:ℕ) (hU:U≤b.U) :
    Aw b h U (cut b)≤qlc9qed.Aw b (h+delta) b.cut:= by
  have hc:cut b≤b.cut+b.box.j*delta := by cases b <;> decide
  intro F hF
  obtain ⟨hcap,hs,ht⟩:=mem_ambient.mp hF
  refine qlc9qed.mem_ambient.mpr ⟨hcap,hs.trans hU,fun a ha => ?_⟩
  have hw:=ht a ha
  have hg:=(MvPolynomial.le_weightedTotalDegree (fun i:mA=>i.elim 0 (fun _=>1))
    ha).trans hcap.1
  rw [b6S] at hg
  simp only [one_mul] at hg
  have he (i:Fin 3) :131071+(h+delta) - i.val=(131071+h-i.val)+delta := by
    have :=i.isLt
    omega
  rw [sum_coeffs] at hw ⊢
  simp only [he,zNE,Nat.mul_add] at hw ⊢
  dsimp only [delta] at hc ⊢
  omega
private abbrev aiz (b:Bank) (h U:ℕ) :=
  Σ k :Fin (b.box.t+1),Σ j:Fin (b.box.j-2*k.val+1),
    Σ d:Fin (b.box.b-k.val-j.val+1),Fin (columnsAt b h k j d)×Fin (U+1)
private def cLB (b:Bank) (h U:ℕ) (hU:U≤b.U) :aiz b h U ↪ Lh b (h+delta) :=
  .sigmaMap (.refl _) fun k => .sigmaMap (.refl _) fun j => .sigmaMap (.refl _) fun d =>
    .prodMap (Fin.castLEEmb (columns_le b h k j d))
      (Fin.castLEEmb (zlr hU 1))
set_option maxRecDepth 2048 in
private theorem mem_column {b h U} (hU:U≤b.U) (c:aiz b h U) :
    column (cLB b h U hU c)∈Aw b h U (cut b) := by
  classical
  have hc:=(qlc9qed.mem_ambient.mp (column_mem (cLB b h U hU c))).1
  have hs (a :mA →₀ ℕ) (ha :a∈(column (cLB b h U hU c)).support) :
      a=Ac (cLB b h U hU c) :=
    Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ha)
  obtain ⟨k,j,d,x,u⟩:=c
  have ⟨hTJ,hJB,_⟩:=box_bounds b
  have hk :=k.isLt
  have hj:=j.isLt
  have hd:=d.isLt
  let i:=b.box.b - k.val - j.val - d.val
  have hg:i+j.val+k.val+d.val=b.box.b:= by dsimp [i]; omega
  have hw :
      (131071+h)*i+(131071+h-1)*j.val+(131071+h-2)*k.val +
        (j.val+2*k.val)+131071*d.val+d.val*h =
      131071*b.box.b+b.box.b*h:= by
    have h1 :131071+h-1+1=131071+h:= by omega
    have h2 :131071+h-2+2=131071+h:= by omega
    calc
      _=(131071+h)*i+(131071+h-1+1)*j.val+(131071+h-2+2)*k.val +
          (131071+h)*d.val := by ring
      _ = _:= by rw [h1,h2,← Nat.mul_add,← Nat.mul_add,← Nat.mul_add,hg,
        Nat.add_mul,Nat.mul_comm h]
  have he :Ac (cLB b h U hU ⟨k,j,d,x,u⟩)=exponent u.val i j.val k.val :=rfl
  have hxval : @auD b (h+delta) (cLB b h U hU ⟨k,j,d,x,u⟩)=x.val := by
    simp only [auD,cLB,Function.Embedding.sigmaMap,Function.Embedding.refl,
      Function.Embedding.coeFn_mk,Sigma.map_mk,id_eq,Function.Embedding.coe_prodMap,
      Prod.map_fst,Fin.coe_castLEEmb,Fin.val_castLE]
  refine mem_ambient.mpr ⟨hc,MvPolynomial.degreeOf_le_iff.mpr ?_,?_⟩
  · intro a ha
    rw [hs a ha,he,exponent_none]
    exact zeh u.isLt
  · intro a ha
    rw [hs a ha,sum_coeffs,column,MvPolynomial.coeff_monomial,ite_eq_left rfl,
      Polynomial.natDegree_monomial_eq _ one_ne_zero,he,exponent_zero,bpQ,d5n]
    simp only [hxval,Fin.val_zero,Fin.val_one,Fin.val_two,Nat.sub_zero]
    have hx :x.val<start b+131071*d.val+j.val+2*k.val +
        (b.box.j*h+d.val*h) := by
      simpa only [columnsAt,zNE] using x.isLt
    rw [zNE b.box.b b.box.j h]
    have hstart:start b+131071*b.box.b=cut b+1 :=start_eq b
    omega
private theorem column_card (b:Bank) (h U:ℕ) :
    Fintype.card (aiz b h U)=ambientCount b h U:= by
  simp only [aiz,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,
    Nat.mul_comm _ (U+1),← Finset.mul_sum]
  unfold ambientCount
  congr 1
  calc
    _ = ∑ k∈range (b.box.t+1),∑ j∈range (b.box.j-2*k+1),
        ∑ d∈range (b.box.b-k-j+1),columnsAt b h k j d:= by
      rw [← zdx]
      refine sum_congr rfl fun k _ => ?_
      rw [← zdx]
      refine sum_congr rfl fun j _ => ?_
      rw [← zdx]
    _ = _:=width_count b h
theorem proof :q84jfie.c1 := by
  intro r b h _
  let U:=width r b
  have hU:U≤b.U:= by
    change width r b≤b.U
    cases r <;> cases b <;> decide
  let V:=Aw b h U (cut b)
  let:FiniteDimensional ao (qlc9qed.Aw b (h+delta) b.cut) :=finite_ambient b (h+delta)
  let:Module.Finite ao V:=FiniteDimensional.of_injective
    (K:=ao) (V := ↥V) (V₂ := ↥(qlc9qed.Aw b (h+delta) b.cut))
    (Submodule.inclusion (ds8 b h U hU)) (Submodule.inclusion_injective (ds8 b h U hU))
  let v (c:aiz b h U) :V:=⟨column (cLB b h U hU c),mem_column hU c⟩
  have hi:LinearIndependent ao v :=LinearIndependent.of_comp V.subtype
    ((cGZ b (h+delta)).comp _ (cLB b h U hU).injective)
  exact ⟨inferInstance,column_card b h U ▸ hi.fintype_card_le_finrank⟩
end
end qoIv1ye
end
section
set_option autoImplicit true
namespace q1FwQGc
open qlc9qed (Bank)
open qzLARrc (oneDebit windowBudget)
open q84jfie (width)
open q1yhP8b (slope bP5)
open private slope_cheap slope_strong from ProximityPrize.SubmissionLower.ZXfrSsa
open private separable from ProximityPrize.SubmissionLower.Z7ee2Qb
open private bDY from ProximityPrize.SubmissionLower.E2
def c1 :Prop :=qzLARrc.c2
def c2 :Prop :=qzLARrc.c3
private theorem budget (b:Bank) (U:ℕ) (hlo:b.box.b≤U) (hhi:U≤b.U)
    (h:windowBudget b.box b.U≤oneDebit b) :
    windowBudget b.box U≤(U + 1)*b.basePole+b.poleExcess := by
  have hs :slope b.box=b.basePole := by
    cases b
    · exact slope_cheap
    · exact slope_strong
  obtain ⟨d,hd⟩:=Nat.exists_eq_add_of_le hhi
  have hb:oneDebit b=(U + 1)*b.basePole+b.poleExcess+d*b.basePole := by
    unfold oneDebit
    rw [hd,show U + d+1=(U + 1)+d by omega,zNE,Nat.add_right_comm]
  have hw:windowBudget b.box b.U=windowBudget b.box U + d*b.basePole := by
    rw [hd,bP5 _ _ _ hlo,hs]
  rw [hw,hb] at h
  exact Nat.le_of_add_le_add_right h
theorem of_children (h1 :c1) (h2 :c2) :q84jfie.c3:= by
  intro r a Γ s P L V hV hcap
  let:Module.Finite aR.ao V:=hV
  have hlo:a.box.b≤width r a := by cases r <;> cases a <;> decide
  have hhi:width r a≤a.U:= by cases r <;> cases a <;> decide
  have hb:windowBudget a.box a.U≤oneDebit a := by
    cases a
    · exact h2
    · exact qYzmxYc.proof
  exact bDY Γ s P L a.box V _ hV (fun P' L' _ hdeg hsep =>
    hdeg ▸ separable h1 a.box (width r a) _ hlo (budget a _ hlo hhi hb) P' L' V hcap hsep)
end q1FwQGc
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace quQsorc
noncomputable section
open Polynomial Finset
open scoped Classical
open P6 (K dw blockLength)
open P6_7_3 (Input degree)
open qt5Na8b (Sheet Zk site quota weight polar lowNumerator scalar_deg variation_room)
open qHEUR1a (Raw embed height threshold)
open qQ9yWTb (Curve Usable)
open q1kuFjb (AtSite)
open qkgz7gb (UJ Weighted rV ceilDiv)
open P5_7_3_5_2 (Prepared BranchBudget gap)
open cu (L)
open private Sites Sites.mk Cover.n Cover.part Cover.inside Cover.zJ Cover.degree Cover.height Cover.weight single from ProximityPrize.SubmissionLower.ZSZKDCa
open private prepared_count from ProximityPrize.SubmissionLower.ZlPdtnc
def c1 :Prop :=P5_7_3_5_2.c2
def c2 :Prop :=qXmh4Jb.c3
private theorem prepare (x :Input) (T:Finset K) (F:Raw)
    (hF:Sheet F) (hW:weight F≤threshold)
    (hroot : ∀ γ∈T,Zk x (embed F) γ) (q:Curve) (hq:Irreducible q) :
    Nonempty (Prepared q x.M.label x.F.scalar (T.filter fun γ=>Usable q (site x γ))
      degree F.natDegree threshold (height F)) := by
  obtain ⟨Cq,hpole⟩:=q9Dxm8d.proof q hq
  let U:=T.filter fun γ=>Usable q (site x γ)
  change Nonempty (Prepared q x.M.label x.F.scalar U degree F.natDegree threshold (height F))
  by_cases hU:U.Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty.mp hU]
    exact ⟨⟨Cq,0,Fin.elim0,fun j=>j.elim0,by simp,by simp,by simp,fun j=>j.elim0⟩⟩
  let A (γ:K) (h:γ∈U) :AtSite Cq (rV x.M.label γ) :=
    Classical.choice (q5azJba.arc hq Cq (site x γ) (mem_filter.mp h).2)
  let v (γ:K) :=if h:γ∈U then (A γ h).place else (A hU.choose hU.choose_spec).place
  have hv (γ:K) (h:γ∈U) :v γ=(A γ h).place :=dite_eq_left h
  have hi:Set.InjOn v (U:Set K) := by
    intro γ hγ δ hδ heq
    rw [hv γ hγ,hv δ hδ] at heq
    have hz :=congrFun ((A γ hγ).site_eq_of_place (A δ hδ) heq) 0
    change algebraMap K L (x.M.label γ)=algebraMap K L (x.M.label δ) at hz
    exact sub_left_inj.mp ((algebraMap K L).injective hz)
  have hw:Weighted degree threshold (embed F) := by
    refine ⟨F,1,one_ne_zero,by rw [map_one,one_mul],?_⟩
    intro j m hm
    have hj:j∈F.support :=mem_support_iff.mpr fun h=>hm (by simp [h])
    have hs :=MvPolynomial.mem_support_iff.mpr hm
    exact ((zZi (f := fun a=>((F.coeff j).coeff a).natDegree+j*degree) hs).trans
      (zZi (f := fun i=>(F.coeff i).support.sup fun a =>
        ((F.coeff i).coeff a).natDegree+i*degree) hj)).trans hW
  have hd: (embed F).natDegree=F.natDegree :=qVXVW4b.embed_degree F
  have hp: (embed F).IsPrimitive :=hF.2.1.isPrimitive (by
    rw [hd]
    exact Nat.ne_of_gt hF.2.2.1)
  let I:Sites Cq x.M.label U:=Sites.mk A v hv hi
  obtain ⟨R⟩:=single qkLfS5c.proof hq hpole I Subset.rfl hF.2.1 hp hw
    (fun γ hγ=>hroot γ (mem_filter.mp hγ).1)
  exact ⟨⟨Cq,Cover.n R,Cover.part R,Cover.inside R,Cover.zJ R,
    (Cover.degree R).trans_eq hd,Cover.height R,Cover.weight R⟩⟩
private theorem marks (x :Input) (T:Finset K) (hT:T⊆x.Γ) :
    UJ degree x.M.word T x.M.label x.F.scalar := by
  refine ⟨fun _ _ _ _ h=>sub_left_inj.mp h,x.F.distinct.mono hT,
    fun _ hγ=>scalar_deg x (hT hγ),?_,?_⟩
  · intro γ hγ
    let m:=x.F.mark γ (hT hγ)
    exact ⟨m.bad.support,(show quota≤dw by decide).trans m.bad.dw,m.scalar_hits⟩
  · obtain ⟨P⟩:=P6_7_3.poles x
    exact ⟨x.h,(show 0<P6_7_3.lo by decide).trans_le (P6_7_3.emz x).1,
      P.D,fun γ hγ=>P.marks γ (hT hγ)⟩
private theorem uq {b c H ℓ g r :ℕ} (hg:0<g) (hH :1≤H)
    (hr : (b*g+ℓ)+(c+1)*g≤ r*g) :b*H+ceilDiv (H*ℓ) g+c≤ r*H := by
  have hceil:g*ceilDiv (H*ℓ) g≤H*ℓ+g :=
    (Nat.mul_div_le (H*ℓ+g-1) g).trans (Nat.sub_le _ _)
  have hsmall: (c+1)*g≤((c+1)*g)*H := by
    simpa only [Nat.mul_one] using zBI ((c+1)*g) hH
  apply zJC _ hg
  calc
    g*(b*H+ceilDiv (H*ℓ) g+c)=(b*g)*H+g*ceilDiv (H*ℓ) g+g*c:= by ring
    _≤(b*g)*H+(H*ℓ+g)+g*c:=zlr (z3b hceil _) _
    _=(b*g+ℓ)*H+(c+1)*g:= by ring
    _≤(b*g+ℓ)*H+((c+1)*g)*H :=z3b hsmall _
    _=((b*g+ℓ)+(c+1)*g)*H := by ring
    _≤(r*g)*H :=ztf H hr
    _=g*(r*H) := by ring
theorem of_children (local_test :c1) (nonlinear :c2) :qt5Na8b.c1 := by
  intro x T hT F hF hW hroot q hq
  let U:=T.filter fun γ=>Usable q (site x γ)
  let e :=F.natDegree
  let H :=height F
  let g:=gap degree
  have he :1≤e :=hF.2.2.1
  have hE :e≤12 :=hF.2.2.2.1
  obtain ⟨heD,hp,hchar,_,hlin,hroom⟩:=variation_room he hE
  obtain ⟨P⟩:=prepare x T F hF hW hroot q hq
  have hU:U⊆T:=filter_subset _ _
  have hb (j:Fin P.n) :BranchBudget (P.part j) degree (6+2*e) (polar e) := by
    let S:=P.part j
    have hd:S.d≤e :=
      (single_le_sum (fun i _=>zD0 (P.part i).d) (mem_univ j)).trans P.degree
    have hdeg : ∀ γ∈S.marks,(x.F.scalar γ).natDegree≤degree :=
      fun γ hγ=>scalar_deg x (hT (hU (P.inside j hγ)))
    by_cases h:2≤S.d
    · exact nonlinear S degree e threshold (by decide) h hd hp heD hchar (P.weight j) hdeg
    · have h1 :S.d = 1 :=le_antisymm (zeh (Nat.lt_of_not_ge h)) S.positive
      obtain ⟨V,ho,hv⟩ :=
        qOdV5gc.proof S degree threshold (by decide) (by decide) h1 (P.weight j) hdeg
      exact ⟨V,ho.trans (ztf _ (zD0 _)),
        hv.trans (ztf _ hlin)⟩
  have hc:=prepared_count local_test (marks x T hT) hU P (by decide) hp hb
  let ℓ:=2*e*blockLength+polar e
  let rate :=qt5Na8b.slope
  have hroom' : ((1+(6+2*e)+4*e)*g+ℓ)+(4*e*e+1)*g≤ rate*g:= by
    change lowNumerator e+(4*e^2+1)*g≤ rate*g at hroom
    rw [show 1+(6+2*e)+4*e=7+6*e by ring,show 4*e*e=4*e^2 by ring]
    simpa only [lowNumerator,show quota-degree=g by rfl,ℓ,← Nat.add_assoc] using hroom
  have hrate : (1+(6+2*e)+4*e)*H+ceilDiv (H*ℓ) g+4*e*e≤ rate*H :=
    uq (show 0<g by decide) (show 1≤H from hF.2.2.2.2.1) hroom'
  have hnat :U.card≤(rate*H)*q.totalDegree :=hc.trans (ztf _ hrate)
  exact_mod_cast hnat
end
end quQsorc
end
section
set_option autoImplicit true
namespace qENQ6Wb
theorem proof :qt5Na8b.c2 :=qVkUX6a.proof
end qENQ6Wb
end
