import ProximityPrize.SubmissionLower.ZJb37yc
set_option Elab.async false
set_option autoImplicit true
namespace qt5AtZa
noncomputable section
open Polynomial UniqueFactorizationMonoid
open P5 (K p)
open cu (L FX aZ Equation yq j9)
open Y3 (Dg aLS bjn normalize embed constant ek aka)
open ba5 (efR efO egd d09)
open qkgz7gb (Witness Stock FilterOK Weighted LowWeight physicalStock)
open private azZ abn cZx fTI from ProximityPrize.SubmissionLower.BJ
def c1 :Prop :=
  ∀ D e u (w:Witness),FilterOK D e u w →
    ∀ Q:Dg,Q.natDegree≤e→aLS Q u→bjn Q →
      ∃ V:Submodule L Dg,Remainders D e u w Q V
def c2 :Prop :=
  ∀ D M W (s :Stock),0<D→0<M →
    ∀ F:Dg,¬ HeightLE D W F →
      ∀ V:Submodule L Dg,
        (∀ G∈V,HeightLT D M G∧s.fits (embed G)∧F∣G) →
        Module.finrank L V≤physicalStock (M-W-1) D *s.size
private theorem transfer {D M:ℕ} {Q G:Dg} {a :FX} {f :Equation}
    (hM:0<M) (hQ:embed Q=constant a*f) (hG:HeightLT D M G)
    (hc : ∃ H B:Dg,H*Q=G+aka (Polynomial.X ^M)*B)
    (z :K) (S:K[X]) (hS:S.natDegree≤D) (hf :yq f z S=0) :
    yq (embed G) z S=0:= by
  classical
  let t:=abn z p
  have hQzero :azZ t S Q=0:= by
    apply IsFractionRing.injective (Polynomial L) FX
    rw [cZx,map_zero,hQ]
    change (constant a*f).eval₂ (cu.qD z) (cu.kr S)=0
    rw [eval₂_mul,show f.eval₂ (cu.qD z) (cu.kr S)=0 from hf,mul_zero]
  have hdeg: (azZ t S G).natDegree<M:= by
    apply Nat.lt_of_le_pred hM
    change (G.eval₂ (MvPolynomial.eval (C ∘ t)) (j9 S)).natDegree≤M-1
    rw [eval₂_eq_sum,Polynomial.sum_def]
    apply natDegree_sum_le_of_forall_le
    intro j _
    rw [MvPolynomial.eval_eq,Finset.sum_mul]
    apply natDegree_sum_le_of_forall_le
    intro m hm
    rw [show (∏ i∈m.support,(C ∘ t) i^m i)=C (∏ i∈m.support,t i^m i) by
      simp only [Function.comp_apply,map_prod,map_pow]]
    have hpow: ((j9 S)^j).natDegree≤j*D :=
      natDegree_pow_le.trans (Nat.mul_le_mul_left _
        ((natDegree_map_le (f :=algebraMap K L) (p:=S)).trans hS))
    exact (natDegree_mul_le_of_le (natDegree_mul_C_le ((G.coeff j).coeff m) _) hpow).trans
      (Nat.le_pred_of_lt (hG j m (MvPolynomial.mem_support_iff.mp hm)))
  obtain ⟨H,B,hrel⟩:=hc
  have hv :=congrArg (azZ t S) hrel
  rw [map_mul,map_add,map_mul,fTI,hQzero,mul_zero] at hv
  have hdvd: (Polynomial.X:Polynomial L)^M∣azZ t S G :=
    ⟨-azZ t S B,by rw [mul_neg]; exact eq_neg_of_add_eq_zero_left hv.symm⟩
  by_contra hn
  rw [← cZx] at hn
  have hl:=natDegree_le_of_dvd hdvd (fun hz=>hn (by rw [hz,map_zero]))
  rw [natDegree_X_pow] at hl
  exact hdeg.not_ge hl
private theorem weighted_of_dvd {D W:ℕ} {s :Multiset Dg}
    (hs : ∀ F∈s,HeightLE D W F∧Irreducible F∧(embed F).IsPrimitive)
    {q:Equation} (hq:Irreducible q) (hd:q∣embed s.prod) :
    Weighted D W q:= by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.prod_zero,map_one] at hd
    exact (hq.not_isUnit (isUnit_of_dvd_one hd)).elim
  | cons F s ih =>
    rw [Multiset.prod_cons,map_mul] at hd
    rcases hq.prime.dvd_mul.mp hd with hf | ht
    · obtain ⟨hw,hI,hprim⟩:=hs F (Multiset.mem_cons_self _ _)
      have hdpos :0<F.natDegree := by
        by_contra! hn
        have he :=eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hn)
        have he' : embed F=C (MvPolynomial.map (algebraMap (Polynomial L) FX) (F.coeff 0)) :=
          (congrArg embed he).trans (map_C _)
        have hu:IsUnit (embed F) := by
          rw [he']
          exact isUnit_C.mpr (hprim _ ⟨1,by rw [mul_one,← he']⟩)
        exact hq.not_isUnit (isUnit_of_dvd_unit hf hu)
      have hi:Irreducible (embed F) :=
        hprim.irreducible_of_irreducible_map_of_injective (IsFractionRing.injective _ _)
          (efR hI hdpos)
      obtain ⟨c,hc⟩:=hf
      have hcu:=(hi.2 hc).resolve_left hq.not_isUnit
      obtain ⟨s',hs',hcs⟩:=Polynomial.isUnit_iff.mp hcu
      obtain ⟨a,ha,hsa⟩:=MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hs'
      refine ⟨F,a,ha.ne_zero,?_,hw⟩
      rw [hc,← hcs,hsa,constant,RingHom.comp_apply,mul_comm]
    · exact ih (fun F hF=>hs F (Multiset.mem_cons_of_mem hF)) ht
theorem of_children (h1 :c1) (h2 :c2) :qkgz7gb.c1 := by
  classical
  intro D e u w hw T z S hS f hf he hu hr
  have hD:0<D:=hw.1
  have hM:0<w.modulus :=Nat.zero_le _ |>.trans_lt hw.2.2.2.1
  obtain ⟨Q,a,ha,hQ,hQe,hQu,hQ0⟩ :=
    normalize f e u (ne_zero_of_natDegree_gt hf.1) he hu
  obtain ⟨V,hV⟩:=h1 D e u w hw Q hQe hQu hQ0
  have haU:IsUnit (constant a) :=ha.isUnit.map constant
  have hQnz :Q≠0:= fun hz=>(mul_ne_zero haU.ne_zero (ne_zero_of_natDegree_gt hf.1))
    (hQ.symm.trans (by rw [hz,map_zero]))
  let fs :=factors Q
  let lo:=fs.filter (HeightLE D w.weight)
  let hi:=fs.filter fun F => ¬ HeightLE D w.weight F
  have hp:lo+hi=fs :=Multiset.filter_add_not _ _
  obtain ⟨b,hb⟩:=factors_prod hQnz
  change fs.prod*(b:Dg)= Q at hb
  have hpart:Q=lo.prod*(hi.prod*(b:Dg)) := by
    rw [← hb,← hp,Multiset.prod_add,mul_assoc]
  let _:Finite {F:Dg // F∈hi} := hi.finite_toSet.to_subtype
  let _:AddCommGroup V := @Submodule.addCommGroup L Dg _ _ _ V
  let test :Option {F:Dg // F∈hi} → Dg:= fun i=>i.elim 0 Subtype.val
  let bad i:Submodule L V:=(LinearMap.mulLeft L (test i)).range.comap V.subtype
  have hmem (i:Option {F:Dg // F∈hi}) (x :V) :
      x∈bad i↔test i∣x.val := by
    change (∃ b:Dg,test i*b=x.val) ↔ ∃ b:Dg,x.val=test i*b
    exact ⟨fun ⟨b,h⟩=>⟨b,h.symm⟩,fun ⟨b,h⟩=>⟨b,h.symm⟩⟩
  have hbad (i) :bad i ≠ ⊤ := by
    intro htop
    cases i with
    | none =>
      have hpos :=(Nat.zero_le _).trans_lt hV.rank
      have hz (x :V) :x=0 :=
        Subtype.ext (zero_dvd_iff.mp ((hmem none x).mp (htop.symm ▸ Submodule.mem_top)))
      let:Subsingleton V:=⟨fun x y=>(hz x).trans (hz y).symm⟩
      exact (Nat.ne_of_gt hpos) (Module.finrank_eq_zero_of_subsingleton (R:=L) (M:=V))
    | some F =>
      refine hV.rank.not_ge (h2 D w.modulus w.weight (w.stock.cUr u) hD hM F.val
        (Multiset.mem_filter.mp F.property).2 V ?_)
      intro G hG
      exact ⟨hV.height G hG,hV.seed G hG,
        (hmem (some F) ⟨G,hG⟩).mp (htop.symm ▸ Submodule.mem_top)⟩
  obtain ⟨x,hx⟩ :=
    Submodule.exists_forall_notMem_of_forall_ne_top (K:=L) (M:=V) bad hbad
  let G:Dg:=x.val
  have hG0:G≠0:= fun hz=>hx none ((hmem none x).mpr (zero_dvd_iff.mpr hz))
  have hc:IsCoprime (ek (embed hi.prod)) (ek (embed G)) := by
    let φ:=ek.comp embed
    change IsCoprime (φ hi.prod) (ek (embed G))
    rw [map_multiset_prod φ hi]
    refine Multiset.prod_induction (fun H : (FractionRing aZ)[X] =>
      IsCoprime H (ek (embed G))) (hi.map φ) (fun _ _ ha hb=>ha.mul_left hb)
      isCoprime_one_left ?_
    intro H hH
    obtain ⟨F,hF,rfl⟩:=Multiset.mem_map.mp hH
    change IsCoprime (ek (embed F)) (ek (embed G))
    have hFirr :=irreducible_of_factor F (Multiset.mem_filter.mp hF).1
    by_cases hpos :0<F.natDegree
    · exact (efR hFirr hpos).isCoprime_or_dvd _ |>.resolve_right (fun hd =>
        hx (some ⟨F,hF⟩) ((hmem (some ⟨F,hF⟩) x).mpr
          (efO (hFirr.isPrimitive hpos.ne') hd)))
    · have hunit :=egd hFirr.ne_zero (Nat.eq_zero_of_not_pos hpos)
      simpa only [one_mul] using
        (isCoprime_mul_unit_right_left hunit 1 (ek (embed G))).mpr isCoprime_one_left
  let v :=embed (b:Dg)*constant a⁻¹
  have hv :IsUnit v :=(b.isUnit.map embed).mul ((inv_ne_zero ha).isUnit.map constant)
  let high:=embed hi.prod*v
  have hfact :f=embed lo.prod*high:= calc
    f=constant a⁻¹*embed Q:= by
      rw [hQ,← mul_assoc,← map_mul,inv_mul_cancel₀ ha,map_one,one_mul]
    _=embed lo.prod*high:= by
      rw [hpart,map_mul,map_mul]
      dsimp only [high,v]
      ac_rfl
  have hlow:LowWeight D w.weight (embed lo.prod) := by
    apply weighted_of_dvd
    intro F hF
    have hFd:embed F∣f :=
      (map_dvd embed (Multiset.dvd_prod hF)).trans ⟨high,hfact⟩
    obtain ⟨hm,hW⟩:=Multiset.mem_filter.mp hF
    exact ⟨hW,irreducible_of_factor F hm,isPrimitive_of_dvd hf.2.1 hFd⟩
  refine ⟨embed lo.prod,high,embed G,hfact,hlow,
    (map_ne_zero_iff _ Y3.embed_injective).mpr hG0,?_,hV.seed G x.property,?_,?_⟩
  · simpa only [d09] using hV.jU G x.property
  · change IsCoprime (ek (embed hi.prod*v)) (ek (embed G))
    rw [map_mul]
    exact (isCoprime_mul_unit_right_left (hv.map ek) _ _).mpr hc
  · intro γ hγ
    exact transfer hM hQ (hV.height G x.property) (hV.congruence G x.property)
      (z γ) (S γ) (hS γ hγ) (hr γ hγ)
end
end qt5AtZa
