import ProximityPrize.SubmissionLower.ZgYpvbb
import ProximityPrize.SubmissionLower.Z4uiCKc
import ProximityPrize.SubmissionLower.ZzDXtqd
import ProximityPrize.SubmissionLower.ZqENWAd
import ProximityPrize.SubmissionLower.ZV9jLRa
set_option Elab.async false
open _root_ renaming Finset.sup_mono → zRS, Finsupp.add_apply → zSs, Ideal.span → zye, Nat.add_le_add_left → z3b, Nat.div_le_div_right → zf6, Nat.eq_zero_of_le_zero → za7, Nat.le_add_left → zmL, Nat.le_add_right → z8K, Nat.le_div_iff_mul_le → z1g, Nat.mul_le_mul → zcp, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Nat.sub_le_sub_right → zIu, Nat.zero_le → zD0, Polynomial.X → z7y, Polynomial.natDegree_zero → zbf, Submodule.add_mem → zcy, Submodule.sub_mem → zMG
set_option maxHeartbeats 3000000
section
set_option autoImplicit true
namespace qdvNtxc
noncomputable section
open aR (af Shape)
open oR (separant)
open we (cH eT fW vY D7 JZ DO)
open yz (oe F3 S3 bpH ahz)
open P6_6 (bf LN)
open qSCPCwb (Vk avD Uj Bk)
open qeu0RUc (yD avw)
open qgLc7la (FactorBox Gf RY Wa aIn i9
  pN gnI)
open MvPolynomial
open scoped Pointwise
open private cUa bK6 bmt bvn from ProximityPrize.SubmissionLower.BG
open private b8V from ProximityPrize.SubmissionLower.ZgYpvbb
open private cMX from ProximityPrize.SubmissionLower.ZJObpKc
open private aM6 from ProximityPrize.SubmissionLower.Z4uiCKc
private theorem eMx {a :Shape} {f :af 3} {P:Ideal (eT 3)}
    (hP:P∈yD f) (hp: (i9 a f P).IsPrime)
    (hd: (affineHilbertPolynomial (i9 a f P)).natDegree=1)
    (T:Gf a f) (hn:fW (Vk f)∉P) :
    (avD f P).Finite∧((avD f P).ncard:ℚ)≤pN a f P:= by
  let h:T.next∈restrictSupport cH (Wa a) :=T.next_box
  let l:=monomialLift T.next h
  have hmap :monomialMap cH (Wa a) l=T.next:=monomialMap_monomialLift _ _
  have hnext {x :Fin 3→cH} (hx :x∈D7 f P) :
      eval (JZ f x) T.next=0↔eval x (fW (Vk f))=0 :=
    bpH T.next_represents (cMX hP hx) hx.2
  have hl:l∉i9 a f P:= by
    intro hm
    change monomialMap cH (Wa a) l∈F3 f P at hm
    rw [hmap] at hm
    have hret:=Ideal.mem_retainedMinimalPrimes.mp (avw.mp hP).2
    let:P.IsPrime :=hret.1.isPrime
    apply hn
    exact (b8V (f :=f) hret.2 _).mpr fun x hx =>
      (hnext hx).mp (hm _ ⟨x,hx,rfl⟩)
  let J:=i9 a f P ⊔ zye {l}
  obtain ⟨hdim,hbound⟩:=principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hp hl (totalDegree_monomialLift_le_one _ _)
  change (affineHilbertPolynomial J).natDegree≤_ at hdim
  rw [hd] at hdim hbound
  have hzero : (affineHilbertPolynomial J).natDegree=0:=za7 hdim
  have hdeg:affineDegree J≤pN a f P:= by
    rw [pN,affineDegree_of_natDegree_eq_zero hzero,affineDegree,hd]
    simpa [J] using hbound
  obtain ⟨hfinite,hcard⟩ :=
    finite_zeroLocus_and_ncard_le_affineDegree (K:=cH) J hzero
  let m:= fun x=>monomialPoint (Wa a) (JZ f x)
  have hinj:Function.Injective m :=
    (monomialPoint_injective (aIn a)).comp (cUa f)
  have hsubset :m '' avD f P⊆zeroLocus cH J:= by
    rintro _ ⟨x,hx,rfl⟩
    apply mem_zeroLocus_iff_le_ker_aeval.mpr
    apply sup_le
    · apply mem_zeroLocus_iff_le_ker_aeval.mp
      apply (monomialPoint_mem_zeroLocus_comap_iff (aIn a) _ _).mpr
      exact zeroLocus_vanishingIdeal_le _ ⟨x,hx.1,rfl⟩
    · apply (Ideal.span_singleton_le_iff_mem _).mpr
      rw [RingHom.mem_ker,aeval_monomialPoint,hmap]
      exact (hnext hx.1).mpr hx.2
  refine ⟨(hfinite.subset hsubset).of_finite_image hinj.injOn,?_⟩
  rw [← Set.ncard_image_of_injective _ hinj]
  exact (Nat.cast_le.mpr (Set.ncard_le_ncard hsubset hfinite)).trans (hcard.trans hdeg)
private theorem separant_box {a :Shape} {f :af 3} (hf :FactorBox a f) :
    DO (vY (fW (separant f))) a 0:= by
  have hF:DO (vY (fW f)) a 0 :=
    bmt hf.total hf.index hf.top le_rfl (bvn f)
  have hderiv :vY (fW (separant f))=pderiv (2 :Fin 4) (vY (fW f)) := by
    unfold vY fW separant
    rw [show (2 :Fin 4)=(2 :Fin 3).castSucc from rfl,
      pderiv_rename (Fin.castSucc_injective 3),pderiv_map]
  rw [hderiv]
  intro u hu
  rw [MvPolynomial.mem_support_iff,coeff_pderiv] at hu
  have h:=hF _ (MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hu))
  simp only [zSs,Finsupp.single_apply,ite_true] at h
  rcases h with ⟨hb,hj,ht,hh⟩
  exact ⟨by omega,by omega,by omega,hh⟩
private theorem separant_pow_box {a :Shape} {f :af 3} (hf :FactorBox a f) (r :ℕ) :
    DO (vY (fW (separant f))^r) ⟨r*a.b,r*a.j,r*a.t⟩ 0:= by
  classical
  induction r with
  | zero =>
      simp only [pow_zero,DO,support_one,Finset.mem_singleton]
      rintro u rfl
      simp
  | succ r ih =>
      intro u hu
      rw [pow_succ] at hu
      obtain ⟨b,hb,c,hc,rfl⟩:=Finset.mem_add.mp (support_mul _ _ hu)
      obtain ⟨hb₀,hb₁,hb₂,hb₃⟩:=ih b hb
      obtain ⟨hc₀,hc₁,hc₂,hc₃⟩:=separant_box hf c hc
      simp only [zSs,Nat.succ_mul] at *
      exact ⟨by omega,by omega,by omega,by omega⟩
private theorem b0q {a :Shape} {f :af 3} (hf :FactorBox a f) :
    DO (vY (fW (separant f))^(bf-4))
      (RY a) bf := by
  let r :=bf-4
  let s :=bf+2 - 4
  have hrs :r≤ s :=zIu (z8K _ _) _
  have ht:2*a.t≤a.j:= by rw [hf.top_eq]; omega
  have hindex :r*a.t≤(2+s*(a.j+2))/2 := by
    apply (z1g (by decide :0<2)).mpr
    rw [Nat.mul_comm _ 2,mul_left_comm]
    exact (zcp hrs (ht.trans (z8K _ _))).trans (zmL _ _)
  exact bmt
    ((ztf a.b hrs).trans (zmL _ _))
    ((zcp hrs (z8K a.j 2)).trans (zmL _ _))
    (le_min ((zcp hrs (z8K a.t 2)).trans (zmL _ _)) hindex)
    (zD0 _) (separant_pow_box hf r)
private theorem dMX {a :Shape} {N :eT 4}
    (hN :DO N (LN bf a) (bf - 2)) :
    DO N (RY a) bf := by
  have h:bf-4≤bf+2 - 4 :=
    zIu (z8K _ _) _
  have hb:=z3b (ztf a.b h) 1
  have hj:=z3b (ztf (a.j+2) h) 2
  have ht:=min_le_min (z3b (ztf (a.t+2) h) 1)
    (zf6 (c:=2) hj)
  exact bmt hb hj ht (Nat.sub_le _ _) hN
private theorem eval_lastLift {a :Shape} (z :oe) (p:eT 4)
    (h:p∈restrictSupport cH (Wa a)) :
    eval (monomialPoint (Wa a) z) (monomialLift p h)=eval z p:= by
  simpa only [aeval_eq_eval,monomialMap_monomialLift] using aeval_monomialPoint z (monomialLift p h)
private theorem dM0 {a :Shape} {f :af 3} {P:Ideal (eT 3)}
    (hf :FactorBox a f) (T:Gf a f) (hp: (i9 a f P).IsPrime)
    (hd: (affineHilbertPolynomial (i9 a f P)).natDegree=1) :
    ∃ Q:Bk,Q.IsPrime∧(affineHilbertPolynomial Q).natDegree≤1 ∧
      affineDegree Q≤pN a f P ∧
      ∀ y∈D7 f P,Uj f T.numerator y∈zeroLocus cH Q:= by
  let A:=monomialPoint (Wa a) '' S3 f P
  have hA:i9 a f P=vanishingIdeal cH A:= by
    ext p
    constructor
    · intro hm
      rintro _ ⟨z,hz,rfl⟩
      rw [aeval_monomialPoint]
      exact hm z hz
    · intro hm z hz
      have he :=hm _ ⟨z,hz,rfl⟩
      rwa [aeval_monomialPoint] at he
  obtain ⟨d,hdpos,hdegree⟩:=aM6 (i9 a f P) hp hd
  have hone :1≤affineDegree (i9 a f P) := by
    rw [hdegree]
    exact_mod_cast Nat.succ_le_of_lt hdpos
  obtain ⟨D,hD_eq⟩ : ∃ D:eT 4,
      D =vY (fW (separant f))^(bf-4) :=⟨_,rfl⟩
  have hD:D∈restrictSupport cH (Wa a) := by
    change DO D (RY a) bf
    rw [hD_eq]
    exact b0q hf
  let hN (j:Fin aR.bf) :
      T.numerator j∈restrictSupport cH (Wa a) := by
    change DO (T.numerator j) (RY a) bf
    exact dMX (T.coefficient_box j)
  let δ:=monomialLift D hD
  let ν (j:Fin aR.bf) :=monomialLift (T.numerator j) (hN j)
  have hden (z) (hz :z∈A) :eval z δ≠0:= by
    obtain ⟨_,⟨x,hx,rfl⟩,rfl⟩:=hz
    rw [eval_lastLift,hD_eq,map_pow,ahz]
    exact pow_ne_zero _ hx.2
  obtain ⟨Q,hprime,hdim,hb,hz⟩:=bK6 A _ hA hp hd hone δ ν
    (totalDegree_monomialLift_le_one _ _) (fun j=>totalDegree_monomialLift_le_one _ _) hden
  refine ⟨Q,hprime,hdim,hb,fun x hx => ?_⟩
  have hz' := hz (monomialPoint (Wa a) (JZ f x)) ⟨_,⟨x,hx,rfl⟩,rfl⟩
  unfold Uj
  simpa only [ν,δ,eval_lastLift,hD_eq,map_pow,ahz] using hz'
theorem proof :qgLc7la.c2 := by
  intro a f hf T P hP
  obtain ⟨hp,hd⟩:=gnI (a :=a) hf.irreducible hP
  exact ⟨eMx hP hp hd T,fun _=>dM0 hf T hp hd⟩
end
end qdvNtxc
end
section
set_option autoImplicit true
namespace qbVMAwc
set_option Elab.async false
set_option maxRecDepth 4096
set_option quotPrecheck false in
local notation "q!" p "," n "," s "," a "," m "," zs "," hs =>
  reject (cut:=p) (len:=n) (Fy :=s) (adj:=a)
    (value :=m) zs hs (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option quotPrecheck false in
local notation "r!" h "," t=>transfer (by decide +kernel) t (by decide +kernel) (by decide +kernel) h
set_option quotPrecheck false in
local notation "e" => (by decide +kernel)
local notation "z" => True.intro
private theorem r1 :Cut 1 3 21 47:=q! 4,111,39,1,0x16175c,[
    0x2698b,0x8fb9c,0x77cec,0x2d22f,0x631a],⟨e,e,e,e,e,z⟩
private theorem r2 :Cut 2 3 21 48:=q! 24,112,0,1,0x161582,[
    0x266ed,0x2535e,0x24036,0x22d76,0x80c5b,0x419a8,
    0xc230,0x558],⟨e,e,e,e,e,e,e,e,z⟩
private theorem r3:Cut 4 3 21 49:=q! 0,113,84,2,0x161799,[
    0x92ace,0xa49c9,0x29c64,0x69e],⟨e,e,e,e,z⟩
private theorem r4 :Cut 5 3 21 50:=q! 0,114,56,1,0x160c2d,[
    0x921db,0x7c9ac,0x440c7,0xdfdf],⟨e,e,e,e,z⟩
private theorem r5:Cut 7 3 21 52 :=q! 0,115,56,1,0x1613b8,[
    0x90ff4,0x79b3b,0x46f96,0xf8f2,1],⟨e,e,e,e,e,z⟩
private theorem r6:Cut 10 3 21 55:=q! 0,118,56,3,0x160b18,[
    0x8f51a,0x9e5e9,0x2c21b,0x6dfa],⟨e,e,e,e,z⟩
private theorem r7:Cut 12 3 21 57:=q! 0,120,75,3,0x160b6d,[
    0xde167,0x73638,0xf3ce],⟨e,e,e,z⟩
private theorem r8:Cut 14 3 21 60:=q! 0,122,75,3,0x160d97,[
    0xd225d,0x7d206,0x11934],⟨e,e,e,z⟩
private theorem r9:Cut 16 3 21 63:=q! 0,125,90,3,0x1613d1,[
    0x11156c,0x4ada2,0x50c3],⟨e,e,e,z⟩
private theorem dz :Cut 18 3 16 64 :=q! 0,143,68,1,0x1613da,[
    0x8ad7f,0x69bcf,0x4aab1,0x1c0fe,0x5edd],⟨e,e,e,e,e,z⟩
private theorem dD:Cut 19 3 16 66:=q! 0,144,108,2,0x1612de,[
    0x8a48c,0x921d0,0x37493,0xd7ef],⟨e,e,e,e,z⟩
private theorem dK:Cut 20 3 16 69:=q! 0,147,108,2,0x1611cc,[
    0x89b98,0x861d2,0x42890,0xebd2],⟨e,e,e,e,z⟩
private theorem e8:Cut 21 3 16 72 :=q! 0,149,90,3,0x1610d2,[
    0xb7ffb,0x8e536,0x164a6,0x46fb],⟨e,e,e,e,z⟩
private theorem gD:Cut 22 3 16 76:=q! 0,153,95,3,0x1612b5,[
    0xc3ae1,0x8807a,0x12c5e,0x2afc],⟨e,e,e,e,z⟩
private theorem gx :Cut 23 3 16 80:=q! 0,156,114,3,0x160b4c,[
    0xf66f5,0x5f330,0xb127],⟨e,e,e,z⟩
private theorem iu:Cut 24 3 16 88:=q! 0,163,260,1,0x16148c,[
    0x877cb,0x8e1f5,0x4bacc],⟨e,e,e,z⟩
theorem lane3 (b t:ℕ) (hlo:1≤b) (hhi:b≤24) (ht:1≤t) :
    Test ⟨b,3,t⟩:= by
  interval_cases b
  · exact r! r1,ht
  · exact r! r2,ht
  · exact r! r2,ht
  · exact r! r3,ht
  · exact r! r4,ht
  · exact r! r4,ht
  · exact r! r5,ht
  · exact r! r5,ht
  · exact r! r5,ht
  · exact r! r6,ht
  · exact r! r6,ht
  · exact r! r7,ht
  · exact r! r7,ht
  · exact r! r8,ht
  · exact r! r8,ht
  · exact r! r9,ht
  · exact r! r9,ht
  · exact r! dz,ht
  · exact r! dD,ht
  · exact r! dK,ht
  · exact r! e8,ht
  · exact r! gD,ht
  · exact r! gx,ht
  · exact r! iu,ht
end qbVMAwc
end
section
set_option autoImplicit true
namespace qbVMAwc
open P6_6_8 (edge c8J)
theorem proof :P6_6_8_3.c2 := by
  intro v hv hne
  change Test v
  obtain ⟨_,hj,_,_⟩:=c8J hv
  rcases hv with hz | ⟨hv,hb⟩
  · exact (hne hz).elim
  obtain ⟨b,j,t⟩:=v
  obtain ⟨ht,hmin,hmax⟩:=hv
  change b≤edge j at hb
  change j≤7 at hj
  change 1≤t at ht
  change 3*t≤j at hmin
  change j≤3*b at hmax
  have hlo:3≤j:= by omega
  interval_cases j
  · exact lane3 b t (by omega) hb ht
  · exact lane4 b t (by omega) hb ht
  · exact lane5 b t (by omega) hb ht
  · exact lane6 b t (by omega) hb ht
  · exact lane7 b t (by omega) hb ht
end qbVMAwc
end
section
set_option autoImplicit true
namespace qXuDJRd
noncomputable section
open P6_6 (lowerTaylor bf)
open q0TFWAc
open aR (af Shape shape aO)
open Ex (C6)
open oR (Wc)
open yz (aCt)
open dN (GeoJets bC j8)
open Dr
open lB (amo aFf)
open MvPolynomial
open scoped Polynomial BigOperators
open private hasse_zero from ProximityPrize.SubmissionLower.ZX4kd1a
def c1 :Prop :=
  ∀ (f g:GeoJets),f.degreeOf 3=0→ g.degreeOf 3=0 →
    ∀ T,(T=pair f g∨(pair f g).IsMinimalPrime T) →
    ∀ (a :Shape) (n:ℕ),capHilbert T a 1 n=(n+1)*capHilbert T a 0 n
def c2 :Prop :=
  ∀ (f g:GeoJets),f≠0→ g≠0→ IsRelPrime f g →
    f.degreeOf 3=0→ g.degreeOf 3=0 →
    ∀ (a d:Shape) (n:ℕ),
      let x :=(a.scale (2*n)).plus d
      let q:=lowerShape f
      let r :=lowerShape g
      capHilbert (pair f g) a 0 n+lattice (x.plus q)+lattice (x.plus r) ≤
        lattice ((x.plus q).plus r)+lattice x
private theorem aCx {a :Shape} (ha :bF a) (ht:0<a.t) :
    Function.Surjective (capMap a 1) := by
  apply monomialMap_surjective
  obtain ⟨hb,hj⟩:=ha
  intro i
  fin_cases i <;> simp [aCt,Shape.scale] <;> omega
private theorem product_degree {T:Ideal GeoJets} {a :Shape}
    (h : ∀ n,capHilbert T a 1 n=(n+1)*capHilbert T a 0 n)
    (hd: (affineHilbertPolynomial (HW T a 1)).natDegree=2) :
    (affineHilbertPolynomial (HW T a 1)).coeff 2=affineDegree (HW T a 0) := by
  let L:=affineHilbertPolynomial (HW T a 0)
  let P:=affineHilbertPolynomial (HW T a 1)
  have he :P=(z7y+1)*L:= by
    apply Polynomial.eq_of_eventually_atTop_eval_natCast_eq
    filter_upwards [eventually_eval_affineHilbertPolynomial (HW T a 1),
      eventually_eval_affineHilbertPolynomial (HW T a 0)] with n hP hL
    change P.eval (n:ℚ)=((z7y+1)*L).eval (n:ℚ)
    simp only [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    rw [show P.eval (n:ℚ)=(capHilbert T a 1 n:ℚ) from hP,
      show L.eval (n:ℚ)=(capHilbert T a 0 n:ℚ) from hL]
    exact_mod_cast h n
  change P.natDegree=2 at hd
  have hn:L≠0:= by
    intro hz
    rw [he,hz,mul_zero,zbf] at hd
    contradiction
  have hx : (z7y+1 :ℚ[X]).natDegree=1 := by
    simpa only [Polynomial.C_1] using Polynomial.natDegree_X_add_C (1 :ℚ)
  have hdL:L.natDegree=1 := by
    have hnX: (z7y+1 :ℚ[X])≠0:= by
      intro hz
      rw [hz,zbf] at hx
      contradiction
    have hc:=congrArg Polynomial.natDegree he
    rw [hd,Polynomial.natDegree_mul hnX hn,hx] at hc
    omega
  have hlead: (z7y+1 :ℚ[X]).leadingCoeff=1 := by
    simpa only [Polynomial.C_1] using Polynomial.leadingCoeff_X_add_C (1 :ℚ)
  calc
    P.coeff 2=P.leadingCoeff := by rw [Polynomial.leadingCoeff,hd]
    _=L.leadingCoeff := by rw [he,Polynomial.leadingCoeff_mul,hlead,one_mul]
    _=affineDegree (HW T a 0) := by
      change L.leadingCoeff=(L.natDegree.factorial:ℚ)*L.leadingCoeff
      simp [hdL]
private theorem bound_coeff {J:Ideal GeoJets} {a :Shape} {m:ℕ} {c:ℚ}
    (hd: (affineHilbertPolynomial (HW J a 1)).natDegree≤2)
    (h : ∀ n,capHilbert J a 1 n=(n+1)*capHilbert J a 0 n)
    (hc : ∀ n:ℕ,(capHilbert J a 0 n:ℚ)≤2*(m:ℚ)*n+c) :
    (affineHilbertPolynomial (HW J a 1)).coeff 2≤2*(m:ℚ) := by
  let M:ℚ:=2*(m:ℚ)
  let Q:ℚ[X] :=Polynomial.C M*z7y ^2 +
    Polynomial.C (M+c)*z7y+Polynomial.C c
  have hQ:Q.coeff 2=M:= by
    simp [Q]
  change _≤M
  rw [← hQ]
  apply Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le hd
    (show Q.natDegree≤2 from Polynomial.natDegree_quadratic_le)
  filter_upwards [eventually_eval_affineHilbertPolynomial (HW J a 1)] with n hn
  rw [hn]
  change (capHilbert J a 1 n:ℚ)≤Q.eval (n:ℚ)
  rw [h n,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  have he :Q.eval (n:ℚ)=((n:ℚ)+1)*(M*n+c) := by simp [Q]; ring
  rw [he]
  exact mul_le_mul_of_nonneg_left (hc n) (by positivity)
private theorem generic_lower {V:af 4} {p:Shape} (h:lowerFits V p) :
    aO (lowerShape (bC V)) p∧(bC V).degreeOf 3=0:= by
  have hs :=support_map_subset j8 V
  have hd (i:Fin 4) : (bC V).degreeOf i≤V.degreeOf i:= by
    rw [degreeOf_eq_sup,degreeOf_eq_sup]
    exact zRS hs
  have hb: (bC V).totalDegree≤V.totalDegree :=zRS hs
  have hj: (bC V).weightedTotalDegree (fun i=>i.val)≤aR.qE V:= by
    rw [C6,weightedTotalDegree,weightedTotalDegree]
    exact zRS hs
  exact ⟨⟨hb.trans h.1.1,hj.trans h.1.2.1,(hd 2).trans h.2⟩,
    za7 ((hd 3).trans h.1.2.2)⟩
private theorem second_cap (f :GeoJets) :2*(lowerShape f).t≤(lowerShape f).j:= by
  have hd:f.degreeOf 2≤f.weightedTotalDegree (fun i:Fin 4=>i.val)/2 := by
    apply degreeOf_le_iff.mpr
    intro e he
    have hw:=le_weightedTotalDegree (fun i:Fin 4=>i.val) he
    rw [Finsupp.weight_eq_sum] at hw
    have hh:e 2•(2 :Fin 4).val ≤ ∑ i:Fin 4,e i•i.val :=
      Finset.single_le_sum (f := fun i:Fin 4=>e i•i.val) (fun _ _=>zD0 _)
        (Finset.mem_univ (2 :Fin 4))
    have h:=hh.trans hw
    change e 2*2≤_ at h
    omega
  change 2*f.degreeOf 2≤f.weightedTotalDegree (fun i:Fin 4=>i.val)
  omega
private theorem body_chamber {C R l ell} (h:Input C R l ell) :
    bF (body R)∧0<(body R).t:= by
  have hj:=h.1.2.2.2
  change 2≤(shape R).j at hj
  refine ⟨⟨?_,?_⟩,?_⟩
  · exact (z8K _ _).trans (le_max_right _ _)
  · exact Nat.mul_div_le _ _
  · change 0<(shape R).j/2
    omega
private theorem taylor_chamber (p:Shape) :bF (lowerTaylor p)∧0<(lowerTaylor p).t:= by
  let l:=2*bf - 7
  let j:=l*(p.j - 2)+bf - 1
  let t:=min (l*(p.t - 1)+bf - 2) (j/2)
  have hL:4≤bf := by decide
  have hj:2≤j:=(Nat.le_sub_of_add_le (show 2+1≤bf by omega)).trans
    (Nat.le_add_left _ _)
  have hτ:0<l*(p.t - 1)+bf - 2 :=
    Nat.sub_pos_of_lt ((show 2<bf by omega).trans_le (zmL _ _))
  change (j≤ max _ j∧2*t≤j)∧0<t
  refine ⟨⟨le_max_right _ _,?_⟩,lt_min hτ (by omega)⟩
  exact (zBI 2 (min_le_right _ _)).trans (Nat.mul_div_le _ _)
theorem of_children (h1 :c1) (h2 :c2) :q0TFWAc.c1 := by
  classical
  intro C R l ell h S hS a ha
  let p:=body R
  let f :=bC R
  let g:=bC (ajA R)
  let J:=ke R
  have hJ:J=pair f g:=aIc R (ajA R)
  have hg:=nonzero_proper h
  have hn {V:af 4} (hV:V≠0) :bC V≠0:= fun he =>
    hV (aFf (he.trans (map_zero _).symm))
  have hf0:=hn h.1.1.1.ne_zero
  have hg0:=hn hg.1
  have hrel :=amo _ _ h.1.1.1 hg.2
  have hV:aO (shape R) ⟨p.b,p.j,0⟩ :=
    ⟨le_max_left _ _,le_rfl,h.1.2.2.1.le⟩
  have hf :=generic_lower (by simpa only [hasse_zero] using hasse_fits (e :=0) rfl hV)
  have hg' := generic_lower (by simpa only [hasse_zero] using jump_fits h 0)
  have hp:=(body_chamber h).1
  have hapos :bF a∧0<a.t:=ha.elim (fun e=>e ▸ body_chamber h)
    (fun e=>e ▸ taylor_chamber p)
  have hφ:=aCx hapos.1 hapos.2
  have hreg:IsLeftRegular (Ideal.Quotient.mk (⊥ : Ideal GeoJets) f) :=
    aPQ (by infer_instance) (by simpa using hf0)
  have hdimF:dimension (zye {f})≤3:= by
    simpa [bEk] using aCR hreg
  have hdim:dimension J≤2 := by
    rw [hJ]
    exact (aCR (aIT R (ajA R) hrel)).trans
      (by change dimension (zye {f}) - 1≤2; omega)
  obtain ⟨d,c,hcount⟩:=cIp p a (lowerShape f) (lowerShape g) hp hapos.1
    hf.1 hg'.1 (second_cap f) (second_cap g)
  have hupper (n:ℕ) : (capHilbert J a 0 n:ℚ)≤2*(Wc p p a :ℚ)*n+c:= by
    let x :=(a.scale (2*n)).plus d
    have hR: (capHilbert J a 0 n:ℚ)+lattice (x.plus (lowerShape f)) +
        lattice (x.plus (lowerShape g)) ≤
        (lattice ((x.plus (lowerShape f)).plus (lowerShape g)) :ℚ)+lattice x := by
      rw [hJ]
      exact_mod_cast h2 f g hf0 hg0 hrel hf.2 hg'.2 a d n
    linarith only [hR,hcount n]
  have hc:=bound_coeff (m:=Wc p p a)
    ((natDegree_affineHilbertPolynomial_comap_of_surjective _ hφ J).trans_le hdim)
    (h1 f g hf.2 hg'.2 J (Or.inl hJ) a) hupper
  have hcycle :=(cycle_le _ hφ J hdim S hS).trans hc
  have he (T:Ideal GeoJets) (hT:T∈S) :
      (affineHilbertPolynomial (HW T a 1)).coeff 2=2*curveDegree T a := by
    have ht:=aQG hf0 hrel (hS T hT)
    have hd:=(natDegree_affineHilbertPolynomial_comap_of_surjective _ hφ T).trans ht
    rw [product_degree (h1 f g hf.2 hg'.2 T (Or.inr (hJ ▸ hS T hT)) a) hd]
    change affineDegree (HW T a 0)=2*(affineDegree (HW T a 0)/2)
    ring
  have hs : (∑ T∈S,(AN J T:ℚ)*(affineHilbertPolynomial (HW T a 1)).coeff 2) =
      2 * ∑ T∈S,(AN J T:ℚ)*curveDegree T a := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun T hT=> by rw [he T hT]; ring)
  rw [hs] at hcycle
  linarith only [hcycle]
end
end qXuDJRd
end
section
set_option autoImplicit true
namespace qq6Xhde
noncomputable section
open aR (af ao qE)
open oR (separant DU D3 Ev AR)
open P6_6 (bf lowerTaylor)
open qdWgQqc (num VA fits3)
open MvPolynomial
open scoped Polynomial
local notation "W" => weightedTotalDegree
local notation "toW" => mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
local notation "fromW" => mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
private theorem bfH {w:Fin 3→ℕ} {p q:af 3} {b c:ℕ}
    (hp:W w p≤b) (hq:W w q≤ c) :W w (p*q)≤b+c :=
  (weightedTotalDegree_mul_le w p q).trans (Nat.add_le_add hp hq)
private theorem const_mul (w:Fin 3→ℕ) (a :ao[X]) (p:af 3) :
    W w (C a*p)≤W w p:= by
  simpa only [weightedTotalDegree_C,zero_add] using weightedTotalDegree_mul_le w (C a) p
private theorem cast_mul (w:Fin 3→ℕ) (a :ℕ) (p:af 3) :
    W w ((a :af 3)*p)≤W w p:= by
  rw [← map_natCast (C:ao[X] →+* af 3)]
  exact const_mul w _ p
private theorem bPU (w:Fin 3→ℕ) (i:Fin 3) :W w (MvPolynomial.X i:af 3)≤w i :=
  toW (X_mem_restrictWeightedDegree w (w i) i le_rfl)
private theorem pderiv_zero (w:Fin 3→ℕ) (i:Fin 3) (p:af 3)
    (h:W w p<w i) :pderiv i p=0:= by
  apply MvPolynomial.ext
  intro m
  rw [coeff_pderiv]
  have hz :p.coeff (m+Finsupp.single i 1)=0:= by
    by_contra hn
    have hm:=le_weightedTotalDegree w (mem_support_iff.mpr hn)
    rw [map_add,Finsupp.weight_single,one_smul] at hm
    omega
  simp [hz]
private theorem mul_partial (w:Fin 3→ℕ) (i:Fin 3) {p q:af 3} {d δ:ℕ}
    (hp:W w p≤d) (hq:W w q≤w i+δ) :W w (q*pderiv i p)≤d+δ:= by
  by_cases hi:w i≤d
  · have hd:=(weightedTotalDegree_pderiv_le_sub w i p).trans (zIu hp _)
    exact (bfH hq hd).trans (by omega)
  · rw [pderiv_zero w i p (hp.trans_lt (Nat.lt_of_not_ge hi)),mul_zero,weightedTotalDegree_zero]
    exact zD0 _
private theorem coeff_bound (w:Fin 3→ℕ) (p:af 3) :W w (DU p)≤W w p:= by
  classical
  apply zRS
  intro m hm
  obtain ⟨j,hj,hmj⟩:=Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  rwa [Finset.mem_singleton.mp (support_monomial_subset hmj)]
private theorem eyD (w:Fin 3→ℕ) {d δ:ℕ}
    (h01 :w 1≤w 0+δ) (h12 :w 2≤w 1+δ) {p:af 3} (hp:W w p≤d) :
    W w (D3 p)≤d+δ:= by
  unfold D3
  apply toW
  refine zcy _ (zcy _ (fromW ?_) (fromW ?_)) (fromW ?_)
  · exact (coeff_bound w p).trans (hp.trans (z8K _ _))
  · exact mul_partial w 0 hp ((bPU w 1).trans h01)
  · rw [mul_assoc]
    change W w ((↑(2 :ℕ) :af 3)*_)≤_
    exact (cast_mul w 2 _).trans (mul_partial w 1 hp ((bPU w 2).trans h12))
private theorem sep_bound (w:Fin 3→ℕ) {g:af 3} {b:ℕ} (hg:W w g≤b) :
    W w (separant g)≤b - w 2 :=
  (weightedTotalDegree_pderiv_le_sub w 2 g).trans (zIu hg _)
private theorem aFc (w:Fin 3→ℕ) {b d δ:ℕ} {g p:af 3}
    (h01 :w 1≤w 0+δ) (h12 :w 2≤w 1+δ) (hb:w 2≤b)
    (hg:W w g≤b) (hp:W w p≤d) :W w (Ev g p)≤d+(b - w 2)+δ:= by
  unfold Ev
  apply toW
  refine zMG _ (fromW ?_) (fromW ?_)
  · exact (bfH (sep_bound w hg) (eyD w h01 h12 hp)).trans (by omega)
  · have hl:=eyD w h01 h12 hg
    exact (mul_partial w 2 hp (δ:=b - w 2+δ) (hl.trans (by omega))).trans (by omega)
private theorem recurrence_bound (w:Fin 3→ℕ) {b δ:ℕ} {g:af 3}
    (h01 :w 1≤w 0+δ) (h12 :w 2≤w 1+δ) (hb:w 2≤b) (hg:W w g≤b)
    (k :ℕ) :W w (AR g k)≤w 2+(2*k+1)*(b - w 2)+(k+1)*δ:= by
  let s :=b - w 2
  have hs :W w (separant g)≤ s :=sep_bound w hg
  induction k with
  | zero =>
    rw [AR]
    apply toW
    apply Submodule.neg_mem
    apply fromW
    have hl:=eyD w h01 h12 hg
    simpa only [mul_zero,zero_add,one_mul] using hl.trans (show b+δ≤w 2+s+δ by dsimp [s]; omega)
  | succ k ih =>
    rw [AR]
    let p:=AR g k
    change W w p≤w 2+(2*k+1)*s+(k+1)*δ at ih
    change W w (separant g*Ev g p -
      ((2*k+1 :ℕ) :af 3)*p*Ev g (separant g)) ≤
      w 2+(2*(k+1)+1)*s+(k+1+1)*δ
    rw [show w 2+(2*(k+1)+1)*s+(k+1+1)*δ =
      (w 2+(2*k+1)*s+(k+1)*δ)+(2*s+δ) by ring]
    apply toW
    refine zMG _ (fromW ?_) (fromW ?_)
    · have ht:=aFc w h01 h12 hb hg ih
      change W w (Ev g p)≤_+s+δ at ht
      exact (bfH hs ht).trans (by omega)
    · have ht:=aFc w h01 h12 hb hg hs
      change W w (Ev g (separant g))≤ s+s+δ at ht
      exact (bfH ((cast_mul w (2*k+1) p).trans ih) ht).trans (by omega)
private theorem aM7 (w:Fin 3→ℕ) (δ:ℕ) {b m:ℕ} {g:af 3}
    (h01 :w 1≤w 0+δ) (h12 :w 2≤w 1+δ) (hw : ∀ i,w i≤w 2)
    (hb:w 2≤b) (hg:W w g≤b) (hm:4≤ m) (x y :ao) :
    W w (VA m g x y)≤w 2+(2*m - 7)*(b - w 2)+(m-3)*δ:= by
  classical
  let s :=b - w 2
  let l:=2*m - 7
  have hp (n:ℕ) :W w (separant g^n)≤n*s :=
    (weightedTotalDegree_pow_le _ _ _).trans (zBI _ (sep_bound w hg))
  unfold VA
  apply toW
  refine zMG _ (Submodule.sum_mem _ fun i _=>fromW ?_) (fromW ?_)
  · apply (const_mul w _ _).trans
    unfold num
    split_ifs with hi
    · exact (bfH ((bPU w _).trans (hw _)) (hp l)).trans (z8K _ _)
    · let k :=i.val-3
      have hi' := i.isLt
      have hk :2*k+1≤l:= by dsimp [k,l]; omega
      have hδ: (k+1)*δ≤(m-3)*δ:=ztf δ (by dsimp [k]; omega)
      apply (const_mul w _ _).trans
      calc
        _≤(l-(2*k+1))*s+(w 2+(2*k+1)*s+(k+1)*δ) :=
          bfH (hp _) (recurrence_bound w h01 h12 hb hg k)
        _=w 2+(l-(2*k+1)+(2*k+1))*s+(k+1)*δ:= by ring
        _≤w 2+l*s+(m-3)*δ:= by
          rw [Nat.sub_add_cancel hk]
          exact z3b hδ _
  · exact (const_mul w _ _).trans ((hp l).trans (by change l*s≤w 2+l*s+_; omega))
private theorem half_index (p:af 3) :p.degreeOf 2≤qE p/2 := by
  classical
  rw [Ex.C6,degreeOf_eq_sup]
  apply Finset.sup_le
  intro a ha
  rw [z1g (by decide :0<2)]
  exact (Finsupp.apply_smul_le_weight Fin.val a (2 :Fin 3)).trans (le_weightedTotalDegree _ ha)
theorem proof :qdWgQqc.c1 := by
  intro a hb hj ht g hg x y
  generalize hm:bf=m
  have h4 :4≤ m:=hm ▸ (by decide :4≤bf)
  let p:=VA m g x y
  let w:Fin 3→ℕ:=Pi.single 2 1
  have hB:=aM7 1 0 (g:=g) (by simp) (by simp) (fun _=>le_rfl) hb
    (by rw [weightedTotalDegree_one]; exact hg.1) h4 x y
  have hJ:=aM7 Fin.val 1 (g:=g) (by decide) (by decide)
    (fun i=>Nat.le_of_lt_succ i.isLt) hj (by rw [← Ex.C6]; exact hg.2.1) h4 x y
  have hT:=aM7 w 1 (g:=g) (by decide) (by decide) (fun i=> by fin_cases i <;> decide) ht
    (by rw [show w=Pi.single 2 1 from rfl,weightedTotalDegree_piSingle]; exact hg.2.2) h4 x y
  have hb' : p.totalDegree≤1+(2*m - 7)*(a.b - 1) := by
    simpa only [p,weightedTotalDegree_one,Pi.one_apply,mul_zero,add_zero] using hB
  have hj' : qE p≤(2*m - 7)*(a.j - 2)+m - 1 := by
    rw [← Ex.C6,show (2 :Fin 3).val = 2 from rfl,mul_one] at hJ
    exact hJ.trans (by omega)
  have ht' : p.degreeOf 2≤(2*m - 7)*(a.t - 1)+m - 2 := by
    simp only [w,show w 2=1 by decide,weightedTotalDegree_piSingle,mul_one] at hT
    exact hT.trans (by omega)
  unfold fits3 lowerTaylor
  rw [hm]
  exact ⟨hb'.trans (le_max_left _ _),hj',le_min ht' ((half_index p).trans (zf6 hj'))⟩
end
end qq6Xhde
end
