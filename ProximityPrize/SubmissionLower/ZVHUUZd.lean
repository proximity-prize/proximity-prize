import ProximityPrize.SubmissionLower.Z3gZttb
import ProximityPrize.SubmissionLower.AW
import ProximityPrize.SubmissionLower.Z2oJVua
import ProximityPrize.SubmissionLower.ZyrUiId
set_option Elab.async false
section
set_option autoImplicit true
namespace qeUg7Fa
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 0
local notation "r!" z "," p=>asA (v :=z) (by rfl) p
private theorem r1 :total 2725 12=0x1e9c87dd28c0 :=
  r! 0x2928cc16f20,r! 0x2918bad1b00,r! 0x2908b2ee030,r! 0x28f8a679ac0,
  r! 0x28e8a4f95f0,r! 0x28d89f09290,r! 0x28c8a42ccb0,r! 0x28b8a617940,
  r! 0x28a8b08ec80,r! 0x2898b92b720,r! 0x2888cc0fee0,r! 0x2878d9712c0,
  rfl
private theorem r2 :total 2737 12=0x1e0d46e27140 :=
  r! 0x2868f2b71c0,r! 0x285906e5560,r! 0x28492690bf0,r! 0x283942800f0,
  r! 0x28296798f00,r! 0x28198a3f850,r! 0x2809b7e7380,r! 0x27f9df35a50,
  r! 0x27ea1353690,r! 0x27da415e370,r! 0x27ca7be0180,r! 0x27bab1f2ca0,
  rfl
private theorem r3:total 2749 11=0x1b0f83ce5ed0 :=
  r! 0x27aaf1a8900,r! 0x279b2e5c8e0,r! 0x278b76c9280,r! 0x277bb814090,
  r! 0x276c06e72d0,r! 0x275c5062720,r! 0x274ca471e80,r! 0x273cf475a10,
  r! 0x272d4f06200,r! 0x271da5c2d10,r! 0x270e0909850,rfl
theorem amH :total 2725 35=0x57b9528df8d0 :=
  (total_append r1 (total_append r2 r3))
end qeUg7Fa
end
section
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qkOaTje
noncomputable section
open Polynomial Finset
open P5 (K blockLength)
open P5_7 (midAgreement farAgreement)
open aR (af extend)
open oR (qg)
open aF0 (power BJ YM)
open axI (azO aVj)
open baX (cpz aCz mix)
open private OF OF.mk OF.distinct OF.degree bf9 bNu q8ADoQd.rho weights bu7 from ProximityPrize.SubmissionLower.Z2oJVua
abbrev lam (D:ℕ) :ℚ:=((blockLength:ℚ)/midAgreement)*D
abbrev mu (D:ℕ) :ℚ:=((blockLength - D:ℕ) :ℚ)/(midAgreement - D:ℕ)
private theorem ratio_bounds {D m:ℕ} (hlo:131071≤D) (hhi:D ≤135870) (hm:m≤D) :
    q8ADoQd.rho m≤ mu D ∧q8ADoQd.rho m*(max 1 (D-m) :ℕ)≤lam D:= by
  have hmid :D < midAgreement:=hhi.trans_lt (by decide)
  obtain ⟨hm₁,hm₂⟩:=weights hm (hhi.trans_lt (by decide)) (bu7 hlo hhi)
  refine ⟨hm₁.trans ?_,hm₂.trans ?_⟩
  · unfold q8ADoQd.rho mu
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _)
      (by exact_mod_cast Nat.sub_pos_of_lt hmid)
      (by exact_mod_cast Nat.sub_le_sub_right (by decide :midAgreement≤farAgreement) D)
  · apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _)
      (by exact_mod_cast (by decide :0< midAgreement))
      (by exact_mod_cast (by decide :midAgreement≤farAgreement))
private theorem weighted_caps {D m b j:ℕ} (hlo:131071≤D) (hhi:D ≤135870) (hm:m≤D)
    (hb:0<b) (hj:0<j) :
    let t:=max 1 (D-m)
    q8ADoQd.rho m*BJ t b≤ mu D + 2*lam D*((b:ℚ)-1) ∧
    q8ADoQd.rho m*YM t b j≤lam D*(2*(j:ℚ)-1) := by
  let t:=max 1 (D-m)
  obtain ⟨hμ,hLambda⟩:=ratio_bounds hlo hhi hm
  have hρ:0≤q8ADoQd.rho m:= by unfold q8ADoQd.rho; positivity
  have hp: (power t:ℚ)≤2*(t:ℚ) := by
    exact_mod_cast (Nat.sub_le (2*t) 3)
  have hpow:q8ADoQd.rho m*power t≤2*lam D:= by
    have h:=mul_le_mul_of_nonneg_left hp hρ
    linarith only [h,hLambda]
  constructor
  · unfold BJ
    push_cast
    rw [Nat.cast_sub hb,Nat.cast_one,mul_add,mul_one,← mul_assoc]
    exact add_le_add hμ (mul_le_mul_of_nonneg_right hpow (sub_nonneg.mpr (by exact_mod_cast hb)))
  · have hcap: (YM t b j:ℚ)≤(power t:ℚ)*((j:ℚ)-1)+t:= by
      have h:YM t b j≤power t*(j-1)+t:=min_le_right _ _
      exact (Nat.cast_le.mpr h).trans_eq (by push_cast [Nat.cast_sub hj]; rfl)
    calc
      _≤q8ADoQd.rho m*((power t:ℚ)*((j:ℚ)-1)+t) :=mul_le_mul_of_nonneg_left hcap hρ
      _=(q8ADoQd.rho m*power t)*((j:ℚ)-1)+q8ADoQd.rho m*t:= by ring
      _≤(2*lam D)*((j:ℚ)-1)+lam D :=
        add_le_add (mul_le_mul_of_nonneg_right hpow (sub_nonneg.mpr (by exact_mod_cast hj))) hLambda
      _ = _:= by ring
theorem regular_price {D A:ℕ} (hlo:131071≤D) (hhi:D ≤135870) (hA:farAgreement≤A)
    {h u del} {M:P1.FJ h u del} {Γ} (F:P1.bje A M Γ)
    (hdeg : ∀ γ∈Γ,(F.scalar γ).natDegree≤D) {T:Finset K} (hT:T⊆Γ)
    (f :af 2) (hf :Irreducible f) (hj:0<f.degreeOf 1)
    (hreg : ∀ γ∈T,qg 1 f (extend (F.scalar γ))) :
    (T.card:ℚ)≤lam D*(4*(f.totalDegree :ℚ)*f.degreeOf 1-2*(f.degreeOf 1 :ℚ)*f.degreeOf 1-
      f.totalDegree-f.degreeOf 1)+mu D*f.degreeOf 1+1 := by
  classical
  let b:=f.totalDegree
  let j:=f.degreeOf 1
  have hjb:j≤b:=f.degreeOf_le_totalDegree 1
  have hb:0<b:=hj.trans_le hjb
  have hLambda :0≤lam D:= by unfold lam; positivity
  change (T.card:ℚ)≤lam D*(4*(b:ℚ)*j-2*j*j-b-j)+mu D*j+1
  by_cases hsmall:T.card≤1
  · have h₁: (1 :ℚ)≤j:= by exact_mod_cast hj
    have h₂: (j:ℚ)≤b:=Nat.cast_le.mpr hjb
    have hq:0≤4*(b:ℚ)*j-2*j*j-b-j:= by
      rw [show 4*(b:ℚ)*j-2*j*j-b-j =
        (b-j)*(2*j-1)+2*j*(b-1) by ring]
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr h₂) (by linarith only [h₁]))
        (mul_nonneg (by positivity) (by linarith only [h₁,h₂]))
    exact (show (T.card:ℚ)≤1 by exact_mod_cast hsmall).trans
      (le_add_of_nonneg_left (add_nonneg (mul_nonneg hLambda hq) (by unfold mu; positivity)))
  have hw:OF M.word T F.scalar D:= by
    refine OF.mk (F.distinct.mono hT) (fun γ hγ=>hdeg γ (hT hγ)) ?_
    intro γ hγ
    let m:=F.mark γ (hT hγ)
    exact ⟨m.bad.support,hA.trans m.bad.dw,m.scalar_hits⟩
  let sites :=azO M.word T F.scalar
  let t:=max 1 (D-sites.card)
  have hs :sites.card≤D:=bf9 hw (by omega)
  have ht:t≤D:=max_le ((by decide :1≤131071).trans hlo) (Nat.sub_le _ _)
  have htpos :0<t:=(show 1≤t from le_max_left _ _)
  have hsum:D ≤ sites.card+t:= by
    have h:=le_max_right 1 (D-sites.card)
    dsimp only [t]
    omega
  let V:=MvPolynomial.cappedDegreeMixedVolume b j (BJ t b) (YM t b j)
  have ha :0<BJ t b:= by simp [BJ]
  have hv :0<YM t b j:=lt_min ha (htpos.trans_le (Nat.le_add_left _ _))
  have hcount:=bNu hw V (fun i hi=> by
    obtain ⟨cut,hc,he⟩:=cpz f (hhi.trans_lt (by decide)) ht hj le_rfl le_rfl sites hsum M.word i
    exact cz7.a8m (OF.distinct hw) f hf hj hreg ha hv i hi cut hc
      (fun γ hγ=>he _ (OF.degree hw γ hγ) (hreg γ hγ) (fun _ hk=>aVj hγ hk)))
  have hgap: (0:ℚ)<((farAgreement-sites.card:ℕ) :ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt (hhi.trans_lt (by decide)))
  have hratio: (T.card:ℚ)≤q8ADoQd.rho sites.card*V:= by
    unfold q8ADoQd.rho
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hgap).mpr
    rw [mul_comm (T.card:ℚ)]
    exact_mod_cast hcount
  dsimp only [V] at hratio
  have hvle :YM t b j≤BJ t b:=min_le_left _ _
  rw [aCz hjb hvle] at hratio
  obtain ⟨hA',hV⟩:=weighted_caps hlo hhi hs hb hj
  refine hratio.trans ?_
  change q8ADoQd.rho sites.card*mix b j (BJ t b) (YM t b j)≤_
  unfold mix
  calc
    _=(↑(b-j:ℕ) :ℚ)*(q8ADoQd.rho sites.card*YM t b j) +
        j*(q8ADoQd.rho sites.card*BJ t b) := by ring
    _≤(↑(b-j:ℕ) :ℚ)*(lam D*(2*(j:ℚ)-1))+j*(mu D+2*lam D*((b:ℚ)-1)) :=
      add_le_add (mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hA' (Nat.cast_nonneg _))
    _≤_:= by
      rw [Nat.cast_sub hjb]
      linarith only [show (0:ℚ)≤1 by decide]
theorem regular_price' {D A:ℕ} (hlo:131071≤D) (hhi:D ≤135870) (hA:farAgreement≤A)
    {h u del} {M:P1.FJ h u del} {Γ} (F:P1.bje A M Γ)
    (hdeg : ∀ γ∈Γ,(F.scalar γ).natDegree≤D) {T:Finset K} (hT:T⊆Γ)
    (f :af 2) (hf :Irreducible f) (hj:0<f.degreeOf 1)
    (hreg : ∀ γ∈T,qg 1 f (extend (F.scalar γ))) :
    (T.card:ℚ)≤lam D*(4*(f.totalDegree :ℚ)*f.degreeOf 1-2*(f.degreeOf 1 :ℚ)*f.degreeOf 1)+
      mu D*f.degreeOf 1+1 := by
  have h:=regular_price hlo hhi hA F hdeg hT f hf hj hreg
  have hl:0≤lam D*((f.totalDegree :ℚ)+f.degreeOf 1) :=
    mul_nonneg (by unfold lam; positivity) (by positivity)
  have e :lam D*(4*(f.totalDegree :ℚ)*f.degreeOf 1-2*(f.degreeOf 1 :ℚ)*f.degreeOf 1) =
      lam D*(4*(f.totalDegree :ℚ)*f.degreeOf 1-2*(f.degreeOf 1 :ℚ)*f.degreeOf 1-
        f.totalDegree-f.degreeOf 1)+lam D*((f.totalDegree :ℚ)+f.degreeOf 1) := by ring
  linarith only [h,hl,e]
section jX
open aR (ao cK)
open P5 (p)
open MvPolynomial (degreeOf_mul_eq degreeOf_prod_eq sum_weightedTotalDegree_le_of_prod_dvd weightedTotalDegree_one)
open UniqueFactorizationMonoid
open private QI bpk from ProximityPrize.SubmissionLower.BG
open scoped Classical
def phi (B J:ℚ) :ℚ:=if B=0 then 0 else 4*J-2*J*J/B
def ordinatePrice (L m B:ℚ) :ℚ:=4*L*B/10+m
def mixedPrice (L B J:ℚ) :ℚ:=L*phi B J*9/10
theorem phi_nonneg {B J:ℚ} (hJ:0≤J) (hJB:J≤B) :0≤phi B J:= by
  by_cases hz :B=0
  · simp [phi,hz]
  have hp:0<B:=lt_of_le_of_ne (hJ.trans hJB) (Ne.symm hz)
  have hr :=(div_le_one hp).mpr hJB
  rw [phi,ite_eq_right hz,show 4*J-2*J*J/B=J*(4-2*(J/B)) by ring]
  exact mul_nonneg hJ (by linarith only [hr])
private theorem blend {b j B J:ℚ} (hj:0≤j) (hjb:j≤b)
    (hbB:b≤B) (hjJ:j≤J) (hJB:J≤B) :
    4*b*j-2*j*j≤4*B*j/10+phi B J*9/10*b:= by
  have hb:=hj.trans hjb
  have hleft:4*b*j-2*j*j≤4*B*j:= by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hbB) hj,sq_nonneg j]
  have hright:4*b*j-2*j*j≤phi B J*b:= by
    by_cases hz :B=0
    · have hbz :b=0:=le_antisymm (hbB.trans_eq hz) hb
      have hjz :j=0:=le_antisymm (hjb.trans_eq hbz) hj
      simp [phi,hz,hbz,hjz]
    have hp:0<B:=lt_of_le_of_ne (hb.trans hbB) (Ne.symm hz)
    have hfrac:2*(J+j)/B≤4 :=(div_le_iff₀ hp).mpr (by linarith only [hjJ,hJB])
    have hmono:4*j-2*j*j/B≤4*J-2*J*J/B:= by
      apply sub_nonneg.mp
      rw [show (4*J-2*J*J/B)-(4*j-2*j*j/B)=(J-j)*(4-2*(J+j)/B) by ring]
      exact mul_nonneg (sub_nonneg.mpr hjJ) (sub_nonneg.mpr hfrac)
    have hs :b*(2*j*j/B)≤2*j*j:= calc
      _=(b/B)*(2*j*j) := by ring
      _≤1*(2*j*j) :=mul_le_mul_of_nonneg_right ((div_le_one hp).mpr hbB) (by positivity)
      _ = _:=one_mul _
    rw [mul_comm (phi B J) b,phi,ite_eq_right hz]
    exact (show 4*b*j-2*j*j≤b*(4*j-2*j*j/B) by nlinarith only [hs]).trans
      (mul_le_mul_of_nonneg_left hmono hb)
  linarith only [hleft,hright]
theorem price_regular {n L m b j B J:ℚ} (hL:0≤L)
    (hj:0≤j) (hjb:j≤b) (hbB:b≤B) (hjJ:j≤J) (hJB:J≤B)
    (h:n≤L*(4*b*j-2*j*j)+m*j+1) :
    n≤ordinatePrice L m B*j+mixedPrice L B J*b+1 := by
  have h' := mul_le_mul_of_nonneg_left (blend hj hjb hbB hjJ hJB) hL
  unfold ordinatePrice mixedPrice
  nlinarith only [h,h']
theorem cover (q:af 2) {b j:ℕ} (hq:q≠0) (hp:b<p)
    (hb:q.totalDegree≤b) (hj:q.degreeOf 1≤j) :
    ∃ (A:Finset (af 2)) (R:ao[X][X]),
      (∀ f∈A,Irreducible f∧0<f.degreeOf 1) ∧
      (∑ f∈A,f.totalDegree)≤b∧(∑ f∈A,f.degreeOf 1)≤j ∧
      R≠0∧R.natDegree≤b^2 ∧
      ∀ S:ao[X],cK q S=0→R.eval S=0 ∨ ∃ f∈A,qg 1 f S:= by
  classical
  let _:StrongNormalizationMonoid (af 2) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let M:=normalizedFactors q
  let F:=M.toFinset
  let A:=F.filter fun f=>0<f.degreeOf 1
  have hf (f) (hm:f∈F) :Irreducible f :=
    irreducible_of_normalized_factor f (Multiset.mem_toFinset.mp hm)
  have hdvd: (∏ f∈F,f)∣q :=
    (Multiset.toFinset_prod_dvd_prod M).trans (prod_normalizedFactors hq).dvd
  have hcap: (∑ f∈F,f.totalDegree)≤b:= by
    have h:=sum_weightedTotalDegree_le_of_prod_dvd (1 :Fin 2→ℕ) F id hq hdvd
    simp only [id_eq,weightedTotalDegree_one] at h
    exact h.trans hb
  have hA (f) (hm:f∈A) :Irreducible f∧0<f.degreeOf 1 :=
    ⟨hf f (mem_filter.mp hm).1,(mem_filter.mp hm).2⟩
  have hJ: (∑ f∈A,f.degreeOf 1)≤j:= by
    obtain ⟨r,hr⟩:=(prod_dvd_prod_of_subset A F id (filter_subset _ _)).trans hdvd
    have hprod:=prod_ne_zero_iff.mpr fun f hm=>(hA f hm).1.ne_zero
    have hr0:r≠0:= fun hh=>hq (by simp [hr,hh])
    simp only [id_eq] at hr
    rw [hr,degreeOf_mul_eq hprod hr0,degreeOf_prod_eq A (fun f=>f)
      (fun f hm=>(hA f hm).1.ne_zero)] at hj
    exact (Nat.le_add_right _ _).trans hj
  have hspec (f) (hm:f∈F) :=
    bpk f (hf f hm) (le_max_left 2 b) (max_lt (by decide :2<p) hp)
      ((single_le_sum (fun g _=>Nat.zero_le g.totalDegree) hm).trans (hcap.trans (le_max_right 2 b)))
  let R := ∏ f∈F,QI f
  refine ⟨A,R,hA,(sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    (fun f _ _=>Nat.zero_le f.totalDegree)).trans hcap,hJ,
    prod_ne_zero_iff.mpr (fun f hm=>(hspec f hm).1),?_,?_⟩
  · calc
      R.natDegree ≤ ∑ f∈F,(QI f).natDegree :=Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ f∈F,f.totalDegree*(max 2 b-1) :=sum_le_sum fun f hm=>(hspec f hm).2.1
      _≤b*(max 2 b-1) := by rw [← sum_mul]; exact Nat.mul_le_mul_right _ hcap
      _≤b^2 := by
        by_cases hz :b=0
        · simp [hz]
        rw [pow_two]
        exact Nat.mul_le_mul_left _ (by omega)
  · intro S hS
    have hr :MvPolynomial.eval (aR.jet S) M.prod=0:= by
      have hd:=map_dvd (MvPolynomial.eval (aR.jet S)) (prod_normalizedFactors hq).symm.dvd
      change cK q S∣ _ at hd
      rwa [hS,zero_dvd_iff] at hd
    rw [map_multiset_prod,Multiset.prod_eq_zero_iff,Multiset.mem_map] at hr
    obtain ⟨f,hfM,hfS⟩:=hr
    have hfF:f∈F:=Multiset.mem_toFinset.mpr hfM
    rcases (hspec f hfF).2.2 S hfS with hz | ⟨hpos,hreg⟩
    · left
      change evalRingHom S R=0
      rw [show R = ∏ f∈F,QI f from rfl,map_prod]
      exact prod_eq_zero_iff.mpr ⟨f,hfF,hz⟩
    · exact Or.inr ⟨f,mem_filter.mpr ⟨hfF,hpos⟩,hreg⟩
end jX
end
end qkOaTje
end
