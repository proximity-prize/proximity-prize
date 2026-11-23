import ProximityPrize.SubmissionLower.ZoYisee
import ProximityPrize.SubmissionLower.ZzDXtqd
set_option Elab.async false
open _root_ renaming Function.iterate_succ_apply' → zLk, LinearMap.smul_apply → zqa, MvPolynomial.eval → zY9, MvPolynomial.eval_C → z9X, MvPolynomial.weightedTotalDegree_one → zBy, MvPolynomial.weightedTotalDegree_piSingle → z5e, Nat.sub_add_cancel → zxt, Polynomial.C → z1z, Polynomial.X → z7y
section
set_option autoImplicit true
namespace qdWgQqc
noncomputable section
open Polynomial P6_6 P6_6_7 q6t08kb q0TFWAc
open aR (af ao Shape shape cK extend jet)
open Ex (X7)
open oR (separant)
open aeA (view gLc cvh gLd)
open dN (GeoJets bC Ch)
open BO (Ue)
open scoped Polynomial
@[simp] theorem bbM (f :af 3) (S:ao[X]) :cK (lift f) S=cK f S :=
  MvPolynomial.eval_rename _ _ _
private theorem nonzero_iterate (f :af 3) (S:ao[X])
    (h: (view f).natDegree<K1.p) (hn: (view f).map (zY9 (jet S))≠0) :
    ∃ j,cK ((separant^[j]) f) S≠0:= by
  let F:ao[X][X] :=(view f).map (zY9 (jet S))
  have hev (j:ℕ) :cK ((separant^[j]) f) S =
      (derivative^[j] F).eval (jet S (2 :Fin 3)) := by
    rw [cvh]
    congr 1
    induction j with
    | zero=>rfl
    | succ j ih =>
      simp only [zLk]
      change (view (MvPolynomial.pderiv (Fin.last 2) ((separant^[j]) f))).map _ = _
      rw [gLd,← derivative_map,ih]
  let j:=F.natDegree
  have hj:j<K1.p:=natDegree_map_le.trans_lt h
  have hn' : (j.factorial:ao[X])≠0:= by
    rw [← map_natCast (z1z:ao →+* ao[X])]
    exact Polynomial.C_ne_zero.mpr (lB.ahA hj)
  refine ⟨j,?_⟩
  rw [hev,← factorial_smul_hasseDeriv,zqa,nsmul_eq_mul]
  rw [show F.hasseDeriv j=z1z F.leadingCoeff from hasseDeriv_natDegree_eq_C F,
    Polynomial.eval_mul,Polynomial.eval_natCast,Polynomial.eval_C]
  exact mul_ne_zero hn' (leadingCoeff_ne_zero.mpr hn)
private theorem iterate_fits (a :Shape) (f :af 3) (h:fits3 f a) (j:ℕ) :
    fits3 ((separant^[j]) f) a := by
  have hw (w:Fin 3→ℕ) :
      MvPolynomial.weightedTotalDegree w ((separant^[j]) f) ≤
        MvPolynomial.weightedTotalDegree w f := by
    induction j with
    | zero=>exact le_rfl
    | succ j ih =>
      rw [zLk,separant]
      exact (MvPolynomial.weightedTotalDegree_pderiv_le _ _ _).trans ih
  refine ⟨?_,?_,?_⟩
  · simpa only [zBy] using
      (hw 1).trans (by simpa only [zBy] using h.1)
  · simpa only [← Ex.C6] using
      (hw Fin.val).trans (by simpa only [← Ex.C6] using h.2.1)
  · simpa only [z5e] using
      (hw (Pi.single 2 1)).trans
        (by simpa only [z5e] using h.2.2)
theorem select {C R l ell} (h:Input C R l ell) {T:Ideal GeoJets}
    (ht: (ke R).IsMinimalPrime T)
    (hm : ∃ γ∈active C R,T≤Ch (extend (C.s γ))) :
    ∃ g:af 3,fits3 g (body R)∧fits3 (separant g) (body R) ∧
      bC (lift g)∈T∧bC (lift (separant g))∉T:= by
  classical
  let f :=X7 R
  have hR:lift f=R:=lift_anchorLead R h.1.2.2.1
  have hf :fits3 f (body R) := by
    apply (lift_fits _ _).mp
    rw [hR]
    refine ⟨⟨le_max_left _ _,le_rfl,h.1.2.2.1.le⟩,?_⟩
    exact (MvPolynomial.degreeOf_le_iff.mpr fun m hm=> by
      have hw:=MvPolynomial.le_weightedTotalDegree (Fin.val :Fin 4→ℕ) hm
      rw [← Ex.C6,Finsupp.weight_eq_sum,Fin.sum_univ_four] at hw
      simp only [smul_eq_mul,Fin.val_zero,Fin.val_one] at hw
      change m 0*0+m 1*1+m 2*2+m 3*3≤(shape R).j at hw
      change m 2≤(shape R).j/2
      omega)
  have hd: (view f).natDegree<K1.p:= by
    rw [gLc]
    change f.degreeOf (2 :Fin 3)<_
    rw [← MvPolynomial.degreeOf_rename_of_injective (Fin.castSucc_injective 3) (2 :Fin 3)]
    change (lift f).degreeOf 2<_
    rw [hR]
    exact ((MvPolynomial.degreeOf_le_totalDegree _ _).trans
      (h.1.2.1.2.2.1.1.trans (Nat.sub_le _ _))).trans_lt (by decide :4025<K1.p)
  obtain ⟨γ,hγ,hmark⟩:=hm
  have hn:=(Finset.mem_filter.mp (Finset.mem_filter.mp hγ).1).2
  obtain ⟨j,hj⟩:=nonzero_iterate f (extend (C.s γ)) hd hn
  have hex : ∃ k,bC (lift ((separant^[k]) f))∉T:= by
    exact ⟨j,fun hjT=>hj (by simpa only [bbM] using Ue.mp (hmark hjT))⟩
  let k :=Nat.find hex
  have hk :bC (lift ((separant^[k]) f))∉T:=Nat.find_spec hex
  have hr :bC R∈T:=ht.le (Ideal.subset_span (by simp))
  have hk0:0<k := by
    by_contra! hz
    exact hk (by simpa only [Nat.eq_zero_of_le_zero hz,Function.iterate_zero_apply,hR] using hr)
  let g:=(separant^[k-1]) f
  have he :separant g=(separant^[k]) f := by
    conv_rhs=>rw [← zxt (Nat.one_le_of_lt hk0)]
    rw [zLk]
  exact ⟨g,iterate_fits _ _ hf _,he ▸ iterate_fits _ _ hf k,
    not_not.mp (Nat.find_min hex (by omega :k - 1<k)),he ▸ hk⟩
end
end qdWgQqc
end
section
set_option autoImplicit true
namespace qdWgQqc
noncomputable section
open Polynomial
open aR (af ao cK jet)
open oR (separant)
open aeC (bFn)
open lB (ahA)
open private bPp from ProximityPrize.SubmissionLower.BG
open scoped Polynomial
private theorem eval_num (m:ℕ) (f :af 3) {S:ao[X]} (hf :cK f S=0)
    (i:Fin m) (hm:m≤K1.p) :
    cK (num m f i.val) S=cK (den m f) S*hasseDeriv i.val S:= by
  let e :=zY9 (jet S:Fin 3→ao[X])
  change e (num m f i.val)=e (den m f)*_
  unfold num
  split_ifs with hi
  · rw [map_mul,MvPolynomial.eval_X,mul_comm]
    rfl
  · let j:=i.val-3
    let s :=cK (separant f) S
    have hj:j+3=i.val :=zxt (Nat.le_of_not_gt hi)
    have hpad:2*j+1≤2*m - 7:= by
      have hlt:=i.isLt
      omega
    have hpow:=zxt hpad
    have hs : (i.val.factorial:ao)≠0:=ahA (i.isLt.trans_le hm)
    have he :2*(derivative^[j + 1]) (jet S (2 :Fin 3)) =
        z1z (i.val.factorial:ao)*hasseDeriv i.val S:= by
      rw [bPp,hj,← factorial_smul_hasseDeriv,
        zqa,nsmul_eq_mul,Polynomial.C_eq_natCast]
    rw [map_mul,map_mul,z9X,map_pow]
    change z1z ((2 :ao)/(i.val.factorial:ao)) *
      (s^(2*m - 7-(2*j+1))*cK (oR.AR f j) S) =
      e (den m f)*hasseDeriv i.val S
    rw [bFn _ _ hf,← mul_assoc (s^_) (s^_),← pow_add,hpow]
    have hd:e (den m f)=s^(2*m - 7) :=map_pow e _ _
    rw [hd,div_eq_mul_inv,Polynomial.C_mul,map_ofNat]
    calc
      _=s^(2*m - 7)*(z1z ((i.val.factorial:ao)⁻¹) *
          (2*(derivative^[j + 1]) (jet S (2 :Fin 3)))) := by ring
      _ = _:= by rw [he,← mul_assoc (Polynomial.C _) (Polynomial.C _),← Polynomial.C_mul,
        inv_mul_cancel₀ hs,Polynomial.C_1,one_mul]
private theorem ayL (S:ao[X]) :
    (S.map z1z).eval z7y=S:= by
  rw [Polynomial.eval_map]
  have h:Polynomial.eval₂RingHom (z1z:ao →+* ao[X]) z7y=RingHom.id _:= by
    apply Polynomial.ringHom_ext <;> simp
  exact RingHom.congr_fun h S
private theorem cs7 {m:ℕ} {S:ao[X]} (hS:S.natDegree< m) (x :ao) :
    (∑ i:Fin m,(z1z x-Polynomial.X)^i.val*hasseDeriv i.val S) =
      z1z (S.eval x) := by
  let U:=S.map (z1z:ao →+* ao[X])
  let V:=U.taylor (z7y:ao[X])
  have hd:V.natDegree< m:= by
    rw [show V=U.taylor z7y from rfl,natDegree_taylor]
    exact Polynomial.natDegree_map_le.trans_lt hS
  have he :V.eval (z1z x-Polynomial.X)=z1z (S.eval x) := by
    rw [show V=U.taylor z7y from rfl,taylor_eval,sub_add_cancel]
    exact Polynomial.eval_map_apply z1z x
  rw [← he,Polynomial.eval_eq_sum_range' hd,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  change _=((U.taylor z7y).coeff i.val)*_
  rw [taylor_coeff,hasseDeriv_map,ayL,mul_comm]
theorem cNe {m:ℕ} (hm:m≤K1.p) (f :af 3)
    {S:ao[X]} (hd:S.natDegree< m) (hf :cK f S=0)
    (hs :cK (separant f) S≠0) (x y :ao) :
    cK (VA m f x y) S=0↔S.eval x=y := by
  let e :=zY9 (jet S:Fin 3→ao[X])
  change e (VA m f x y)=0↔_
  have evC (a :ao[X]) :e (MvPolynomial.C a)=a :=z9X _
  simp only [VA,map_sub,map_mul,map_sum,evC]
  have hsum :
      (∑ i:Fin m,(z1z x-Polynomial.X)^i.val*e (num m f i.val)) =
        e (den m f)*z1z (S.eval x) := by
    rw [← cs7 hd x,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show e (num m f i.val)=e (den m f)*hasseDeriv i.val S from eval_num m f hf i hm,
      mul_left_comm]
  have hn:e (den m f)≠0:= by
    rw [den,map_pow]
    exact pow_ne_zero _ hs
  rw [hsum,mul_comm (z1z y),← mul_sub,mul_eq_zero,or_iff_right hn,sub_eq_zero,
    Polynomial.C_injective.eq_iff]
end
end qdWgQqc
end
section
set_option autoImplicit true
namespace qdWgQqc
noncomputable section
open Polynomial P6_6 P6_6_7 q6t08kb q0TFWAc
open aR (ao af Shape extend embed)
open oR (separant)
open dN (Ch)
open BO (Ue)
def c1 :Prop :=
  ∀ (a :Shape),1≤a.b→2≤a.j→1≤a.t →
    ∀ (g:af 3),fits3 g a → ∀ x y :ao,
      fits3 (VA bf g x y) (lowerTaylor a)
def c2 :Prop :=
  ∀ (C:Context) R l ell,Input C R l ell →
    ∀ T,(ke R).IsMinimalPrime T →
      (∃ γ∈active C R,T≤Ch (extend (C.s γ))) →
      1≤ curveDegree T (body R)
theorem of_children (h1 :c1) (h2 :c2) :q0TFWAc.c3:= by
  classical
  intro C R l ell h T ht hm
  obtain ⟨g,hg,hs,hgt,hst⟩:=select h ht hm
  refine ⟨⟨lift (separant g),(lift_fits _ _).mpr hs,hst,h2 C R l ell h T ht hm,?_⟩⟩
  have hj:2≤(body R).j:=h.1.2.2.2
  have hb:1≤(body R).b :=
    (show 1≤(body R).j+3 by omega).trans (le_max_right _ _)
  have hz :1≤(body R).t:=Nat.le_div_iff_mul_le (by decide :0<2) |>.mpr hj
  intro i
  refine ⟨lift (VA bf g (embed (P6.node i)) (embed (C.w i))),
    (lift_fits _ _).mpr (h1 _ hb hj hz g hg _ _),?_⟩
  intro γ hγ hmark hsep
  have hΔ:=(Finset.mem_filter.mp (Finset.mem_filter.mp hγ).1).1
  have hd: (extend (C.s γ)).natDegree<bf :=
    Nat.lt_succ_of_le (Polynomial.natDegree_map_le.trans (C.messages.degree γ hΔ))
  have hroot :=(bbM _ _).symm.trans (Ue.mp (hmark hgt))
  rw [bbM] at hsep ⊢
  rw [cNe (by decide :bf≤K1.p) g hd hroot hsep,
    Polynomial.eval_map_apply,embed.injective.eq_iff]
end
end qdWgQqc
end
section
set_option autoImplicit true
namespace qbVMAwc
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
local notation "q!" p "," n "," s "," a "," m "," zs "," hs =>
  reject (cut:=p) (len:=n) (Fy :=s) (adj:=a)
    (value :=m) zs hs rfl rfl rfl (by decide)
local notation "r!" h "," t=>transfer (by decide) t (by decide) (by decide) h
local notation "e" => rfl
local notation "z" => True.intro
private theorem r1 :Cut 2 5 21 60:=q! 0,113,70,3,0x1602a3,[
    0xdd31a,0x767df,0xc7aa],⟨e,e,e,z⟩
private theorem r2 :Cut 6 5 16 62 :=q! 0,127,60,3,0x1609bc,[
    0x8bc74,0x95955,0x3488f,0xab64],⟨e,e,e,e,z⟩
private theorem r3:Cut 8 5 16 65:=q! 0,130,80,3,0x16123b,[
    0xccdc3,0x802da,0x14197,7],⟨e,e,e,e,z⟩
private theorem r4 :Cut 10 5 16 70:=q! 0,134,48,1,0x160de9,[
    0x89ab2,0x675c7,0x4b5d9,0x1f5e1,0x51b6],⟨e,e,e,e,e,z⟩
private theorem r5:Cut 13 5 16 76:=q! 0,138,119,2,0x160f65,[
    0x9fe11,0xa80b8,0x1909c],⟨e,e,e,z⟩
private theorem r6:Cut 15 5 16 82 :=q! 0,143,102,3,0x1605fb,[
    0xf3ea3,0x6582f,0x6f29],⟨e,e,e,z⟩
private theorem r7:Cut 17 5 16 93:=q! 0,151,126,2,0x160fa0,[
    0x85f9f,0xa2825,0x387dc],⟨e,e,e,z⟩
private theorem r8:Cut 19 5 7 104 :=q! 0,202,100,1,0x1617ab,[
    0x84ebf,0x5c0df,0x3d269,0x267b8,0x148df,0x6bfa,
    0x1913],⟨e,e,e,e,e,e,e,z⟩
theorem lane5 (b t:ℕ) (hlo:2≤b) (hhi:b≤19) (ht:1≤t) :
    Test ⟨b,5,t⟩:= by
  interval_cases b
  · exact r! r1,ht
  · exact r! r1,ht
  · exact r! r1,ht
  · exact r! r1,ht
  · exact r! r2,ht
  · exact r! r2,ht
  · exact r! r3,ht
  · exact r! r3,ht
  · exact r! r4,ht
  · exact r! r4,ht
  · exact r! r4,ht
  · exact r! r5,ht
  · exact r! r5,ht
  · exact r! r6,ht
  · exact r! r6,ht
  · exact r! r7,ht
  · exact r! r7,ht
  · exact r! r8,ht
private theorem r9:Cut 2 6 16 64 :=q! 0,123,120,2,0x15d8f7,[
    0xeeb05,0x6edf2],⟨e,e,z⟩
private theorem dz :Cut 4 6 16 69:=q! 0,127,120,2,0x16085f,[
    0xd7a61,0x86ad6,0x2328],⟨e,e,e,z⟩
private theorem dD:Cut 7 6 16 76:=q! 0,132,80,3,0x160129,[
    0xbf5de,0x909a4,0x101a7],⟨e,e,e,z⟩
private theorem dK:Cut 10 6 16 87:=q! 0,140,68,3,0x161038,[
    0x86e96,0x80775,0x51778,0x82b5],⟨e,e,e,e,z⟩
private theorem e8:Cut 13 6 16 99:=q! 0,149,90,3,0x160948,[
    0xb134b,0x9c0a2,0x1355b],⟨e,e,e,z⟩
private theorem gD:Cut 15 6 7 109:=q! 0,189,138,2,0x160c5a,[
    0x845a1,0x5af32,0x5f0ca,0x1ef17,0x37a6],⟨e,e,e,e,e,z⟩
private theorem gx :Cut 16 6 7 132 :=q! 0,202,150,2,0x16181b,[
    0x83d6f,0x59c8a,0x5b0fc,0x26e53,0x1ed3],⟨e,e,e,e,e,z⟩
theorem lane6 (b t:ℕ) (hlo:2≤b) (hhi:b≤16) (ht:1≤t) :
    Test ⟨b,6,t⟩:= by
  interval_cases b
  · exact r! r9,ht
  · exact r! r9,ht
  · exact r! dz,ht
  · exact r! dz,ht
  · exact r! dz,ht
  · exact r! dD,ht
  · exact r! dD,ht
  · exact r! dD,ht
  · exact r! dK,ht
  · exact r! dK,ht
  · exact r! dK,ht
  · exact r! e8,ht
  · exact r! e8,ht
  · exact r! gD,ht
  · exact r! gx,ht
private theorem iu:Cut 3 7 16 84 :=q! 0,132,80,3,0x15fc64,[
    0xbdaef,0x95e37,0xc33e],⟨e,e,e,z⟩
private theorem kD:Cut 6 7 16 98:=q! 0,141,68,3,0x160f5e,[
    0x86300,0x7a851,0x5a875,0x5b98],⟨e,e,e,e,z⟩
private theorem lH :Cut 9 7 7 107:=q! 0,175,105,3,0x160fe9,[
    0x9f70c,0x91738,0x2c2b4,0x3ef1],⟨e,e,e,e,z⟩
private theorem kR:Cut 10 7 7 122 :=q! 0,182,154,2,0x161483,[
    0x84333,0x8ec2e,0x4a5cf,0x3f53],⟨e,e,e,e,z⟩
theorem lane7 (b t:ℕ) (hlo:3≤b) (hhi:b≤10) (ht:1≤t) :
    Test ⟨b,7,t⟩:= by
  interval_cases b
  · exact r! iu,ht
  · exact r! iu,ht
  · exact r! iu,ht
  · exact r! kD,ht
  · exact r! kD,ht
  · exact r! kD,ht
  · exact r! lH,ht
  · exact r! kR,ht
end qbVMAwc
end
