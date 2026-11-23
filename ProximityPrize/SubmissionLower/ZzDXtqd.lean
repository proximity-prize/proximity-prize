import ProximityPrize.SubmissionLower.ZqzGq1b
import ProximityPrize.SubmissionLower.ZUCbske
import ProximityPrize.SubmissionLower.Z3M0Hpe
set_option Elab.async false
open _root_ renaming Fin.castSucc → z1o, Fin.castSucc_injective → zX8, Finset.sum_le_sum → zQk, Finsupp.weight → ztN, Finsupp.weight_apply → zDM, Ideal.Quotient.mkₐ → zvR, Ideal.span → zye, Module.finrank → zsE, Nat.cast_sub → zjK, Nat.mul_le_mul_right → ztf, Polynomial → zM1, Polynomial.C → z1z, Polynomial.coeff_sub → zsl, Polynomial.eval_C → zFf, Polynomial.eval_X → zB5, Polynomial.eval_add → zvF, Polynomial.eval_mul → zbr, Polynomial.eval_sub → zfY
section
set_option autoImplicit true
namespace qt6zjgd
noncomputable section
open aR (Shape)
open dN (GeoField GeoJets)
open vS (g9)
open B8 (Exponent qK)
open agM (a1Z Vw agj)
open ac7 (Sx)
open NU (LJ D0 byT c3l)
open aKL (RM)
open qZqYIua (geoShape)
open MvPolynomial
open private affine_image aWH from ProximityPrize.SubmissionLower.M
private def w1 :Fin 5→ℕ:= fun _=>1
private def w2 :Fin 5→ℕ:=Fin.val
private def w3:Fin 5→ℕ:=Fin.lastCases 2 (fun i:Fin 4=>if i=3 then 1 else 0)
private def w4 :Fin 5→ℕ:=Fin.lastCases 1 (fun _=>0)
private theorem weight_sum (w:Fin 5→ℕ) (m:Exponent) :
    ztN w m = ∑ i:Fin 5,w i*m i:= by
  rw [zDM,Finsupp.sum_fintype m (fun i c=>c•w i)
    (fun i=>zero_smul ℕ (w i))]
  simp only [smul_eq_mul,Nat.mul_comm]
private theorem weight_sum' (w:Fin 5→ℕ) (m:Exponent) :
    ztN w m = ∑ i:Fin 4,w i.castSucc*m i.castSucc+w (Fin.last 4)*m (Fin.last 4) := by
  rw [weight_sum,Fin.sum_univ_castSucc]
private theorem mem_iff (a :Shape×ℕ) (m:Exponent) :
    m∈LJ a↔ztN w1 m≤2*a.1.b∧ztN w2 m≤2*a.1.j ∧
      ztN w3 m≤2*a.1.t∧ztN w4 m≤2*a.2 := by
  change Sx (a.1.scale 2) (2*a.2) m↔_
  simp only [Sx,Shape.scale,weight_sum',w1,w2,w3,w4,
    Fin.lastCases_last,Fin.lastCases_castSucc,Fin.val_last,Fin.val_castSucc,one_mul,
    zero_mul,ite_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true,Finset.sum_const_zero]
  omega
private theorem le_iff (w:Fin 5→ℕ) (g:g9) (c:ℕ) :
    (∀ m∈g.support,ztN w m≤ c)↔weightedTotalDegree w g≤ c :=
  ⟨fun h=>Finset.sup_le h,fun h m hm=>(le_weightedTotalDegree w hm).trans h⟩
private theorem fits (g:g9) (a :Shape×ℕ) :
    g∈restrictSupport GeoField (LJ a) ↔
      weightedTotalDegree w1 g≤2*a.1.b∧weightedTotalDegree w2 g≤2*a.1.j ∧
      weightedTotalDegree w3 g≤2*a.1.t∧weightedTotalDegree w4 g≤2*a.2 := by
  change (g.support :Set _)⊆LJ a↔_
  simp only [Set.subset_def,Finset.mem_coe,mem_iff]
  rw [← le_iff,← le_iff,← le_iff,← le_iff]
  constructor
  · intro h
    exact ⟨fun m hm=>(h m hm).1,fun m hm=>(h m hm).2.1,fun m hm=>(h m hm).2.2.1,
      fun m hm=>(h m hm).2.2.2⟩
  · rintro ⟨h1,h2,h3,h4⟩ m hm
    exact ⟨h1 m hm,h2 m hm,h3 m hm,h4 m hm⟩
theorem embed_ne {g:GeoJets} (hg:g≠0) :qK g≠0 :=
  (rename_injective _ (zX8 4)).ne (by simpa using hg)
private theorem embed_wd (g:GeoJets) (w:Fin 5→ℕ) :
    weightedTotalDegree w (qK g)=weightedTotalDegree (w ∘ z1o) g :=
  weightedTotalDegree_rename_of_injective (zX8 4)
private theorem embed_shape (g:GeoJets) :
    weightedTotalDegree w1 (qK g)=(geoShape g).b ∧
    weightedTotalDegree w2 (qK g)=(geoShape g).j ∧
    weightedTotalDegree w3 (qK g)=(geoShape g).t ∧
    weightedTotalDegree w4 (qK g)=0:= by
  simp only [embed_wd]
  refine ⟨?_,?_,?_,?_⟩
  · have :w1 ∘ z1o=(1 :Fin 4→ℕ) :=rfl
    rw [this,weightedTotalDegree_one]
    rfl
  · exact rfl
  · have :w3 ∘ z1o=Pi.single 3 1 := by
      funext i
      simp [w3,Pi.single_apply]
    rw [this,weightedTotalDegree_piSingle]
    rfl
  · have :w4 ∘ z1o=0:= by
      funext i
      simp [w4]
    rw [this]
    simp [weightedTotalDegree,zDM]
private theorem fits_mul {g:GeoJets} (hg:g≠0) (v :g9) (a :Shape×ℕ) :
    (qK g)^2*v∈restrictSupport GeoField
      (LJ (a.1.plus (geoShape g),a.2)) ↔
      v∈restrictSupport GeoField (LJ a) := by
  by_cases hv :v=0
  · simp [hv]
  have he :=embed_ne hg
  have hm (w:Fin 5→ℕ) :weightedTotalDegree w ((qK g)^2*v) =
      2*weightedTotalDegree w (qK g)+weightedTotalDegree w v := by
    rw [pow_two,weightedTotalDegree_mul _ _ _ (mul_ne_zero he he) hv,
      weightedTotalDegree_mul _ _ _ he he]
    ring
  obtain ⟨e1,e2,e3,e4⟩:=embed_shape g
  rw [fits,fits,hm,hm,hm,hm,e1,e2,e3,e4]
  simp only [Shape.plus]
  omega
private theorem rank_square (g:GeoJets) (hg:g≠0) (a :Shape×ℕ) :
    zsE GeoField ((restrictSupport GeoField
      (LJ (a.1.plus (geoShape g),a.2))).map
      (zvR GeoField (zye {(qK g)^2})).toLinearMap) +
      (LJ a).ncard=(LJ (a.1.plus (geoShape g),a.2)).ncard:= by
  classical
  let d:=(qK g)^2
  let J:Ideal g9:=zye {d}
  let S:=LJ (a.1.plus (geoShape g),a.2)
  let T:=LJ a
  let U:=restrictSupport GeoField S
  let V:=restrictSupport GeoField T
  let π:=(zvR GeoField J).toLinearMap.domRestrict U
  let μ:=((LinearMap.mulLeft GeoField d).domRestrict V).codRestrict U
    (fun v=>(fits_mul hg v.val a).mpr v.property)
  let:Module.Finite GeoField U:=restrictSupport_finite (Set.toFinite S)
  have hμ:Function.Injective μ:= fun x y h =>
    Subtype.ext (mul_left_cancel₀ (pow_ne_zero _ (embed_ne hg)) (congrArg Subtype.val h))
  have hr :LinearMap.range μ=LinearMap.ker π:= by
    ext x
    rw [LinearMap.mem_range,LinearMap.mem_ker]
    change (∃ v,μ v=x)↔Ideal.Quotient.mk J x.val=0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · rintro ⟨v,rfl⟩
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · intro hx
      obtain ⟨v,hv⟩:=Ideal.mem_span_singleton.mp hx
      have hvu:d*v∈U:=hv ▸ x.property
      exact ⟨⟨v,(fits_mul hg v a).mp hvu⟩,Subtype.ext hv.symm⟩
  have hn:=π.finrank_range_add_finrank_ker
  rw [← hr,LinearMap.range_domRestrict,LinearMap.finrank_range_of_inj hμ] at hn
  have fin (W:Set Exponent) [Finite W] :
      zsE GeoField (restrictSupport GeoField W)=W.ncard:= by
    rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport GeoField _),Nat.card_coe_set_eq]
  exact fin T ▸ fin S ▸ hn
theorem proof :qqJLTVc.c1 := by
  intro g B t hg hB n a _ hcap
  have hcap' : (a.1.plus (geoShape g),a.2)=agj (Vw B t) n:= by
    simpa only [a1Z,Nat.add_zero] using hcap
  let J:Ideal g9:=zye {qK g^2}
  let S:=D0 B t
  have h1 :affineHilbertFunction (RM B J t) n =
      zsE GeoField ((restrictSupport GeoField
        (LJ (a.1.plus (geoShape g),a.2))).map
        (zvR GeoField J).toLinearMap) := by
    change zsE GeoField ((restrictTotalDegree S GeoField n).map
      (zvR GeoField (RM B J t)).toLinearMap)= _
    rw [aWH (restrictTotalDegree S GeoField n) (RM B J t) J
      (monomialMap GeoField S) le_rfl (fun _ _ h=>h),
      affine_image S (byT B t) n,c3l B hB t n,← hcap']
  have h2 :=congrArg (fun k :ℕ=>(k :ℚ)) (rank_square g hg a)
  push_cast at h2
  rw [← hcap',h1]
  linarith only [h2]
end
end qt6zjgd
end
section
set_option autoImplicit true
namespace qBcCKJc
noncomputable section
open aR (Shape)
open agM (agj)
open NU (hvol ic aD direction)
open bAn (Oj eqr)
open qqJLTVc (subtractHorizontal horizontalDerivative volumeDerivative)

open private a1R a3C aSW bw4 gwP from ProximityPrize.SubmissionLower.CE
open private BP from ProximityPrize.SubmissionLower.CE
local notation "𝕏" => (Polynomial.X:Polynomial ℚ)
local notation "𝔠" => (Polynomial.C:ℚ →+* Polynomial ℚ)
private def rayE (e x :ℚ×ℚ×ℚ) (s :ℚ) :zM1 ℚ :=
  Oj (R:=zM1 ℚ) z1z
    (𝔠 x.1*𝕏+𝔠 e.1-𝔠 (s/2))
    (𝔠 x.2.1*𝕏+𝔠 e.2.1-𝔠 (2*s))
    (𝔠 x.2.2*𝕏+𝔠 e.2.2 - 𝔠 s)
private theorem rayE_degree (e x :ℚ×ℚ×ℚ) (s :ℚ) : (rayE e x s).natDegree≤4 := by
  unfold rayE Oj
  compute_degree!
private theorem rayE_coeff (e x :ℚ×ℚ×ℚ) (s :ℚ) : (rayE e x s).coeff 4=hvol x/2 := by
  unfold rayE Oj hvol
  compute_degree!
  ring
private theorem rayE_eval (e x :ℚ×ℚ×ℚ) (s n:ℚ) :
    (rayE e x s).eval n=aSW (x.1*n+e.1) (x.2.1*n+e.2.1) (x.2.2*n+e.2.2) s := by
  simp only [rayE,aSW,Oj,zvF,zfY,
    zbr,Polynomial.eval_pow,zFf,zB5,
    Polynomial.eval_ofNat,Polynomial.eval_one,id_eq]
private theorem Ej (p:zM1 ℚ) (h:p.natDegree≤3) :
    p.coeff 3=(p.eval 3-3*p.eval 2 + 3*p.eval 1 - p.eval 0)/6:= by
  conv_rhs=>rw [Polynomial.as_sum_range' p 4 (by omega)]
  simp [Finset.sum_range_succ]
  ring
private theorem ray3 (d x :ℚ×ℚ×ℚ) :
    (rayE (-d) x 0).coeff 3=(rayE 0 x 0).coeff 3 - horizontalDerivative d x/2 := by
  have hD: (rayE 0 x 0 - rayE (-d) x 0).natDegree≤3:= by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [zsl]
    by_cases h4 :N=4
    · subst h4
      rw [rayE_coeff,rayE_coeff,sub_self]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((rayE_degree _ _ _).trans_lt (by omega)),
        Polynomial.coeff_eq_zero_of_natDegree_lt ((rayE_degree _ _ _).trans_lt (by omega)),sub_self]
  have h:=Ej _ hD
  rw [zsl] at h
  simp only [zfY,rayE_eval] at h
  obtain ⟨x1,x2,x3⟩:=x
  obtain ⟨d1,d2,d3⟩:=d
  simp only [aSW,Oj,horizontalDerivative,id_eq,Prod.fst_neg,Prod.snd_neg,
    Prod.fst_zero,Prod.snd_zero] at h ⊢
  linear_combination (-1 :ℚ)*h
private def Jpoly (e :ℚ×ℚ×ℚ) (a :Shape×ℕ) :zM1 ℚ :=
  𝕏*(𝔠 (2*(a.2 :ℚ))*a1R z1z (fun r=>rayE e (ic r a) 0)) +
    a3C z1z (rayE e (ic 0 a)) (rayE e (ic 1 a))
private theorem rayE_shift_eval (e :ℚ×ℚ×ℚ) (a :Shape×ℕ) (r s n:ℚ) :
    (rayE e (ic r a) s).eval n =
      aSW ((a.1.b:ℚ)*n+e.1) ((a.1.j:ℚ)*n+e.2.1) ((a.1.t:ℚ)*n+e.2.2)
        (r*(2*n*(a.2 :ℚ))+s) := by
  rw [rayE_eval]
  unfold aSW
  congr 1 <;> simp [ic,aD,direction,smul_eq_mul] <;> ring
private theorem Jeval (e :ℚ×ℚ×ℚ) (a :Shape×ℕ) (n:ℚ) :
    (Jpoly e a).eval n =
      bw4 ((a.1.b:ℚ)*n+e.1) ((a.1.j:ℚ)*n+e.2.1) ((a.1.t:ℚ)*n+e.2.2)
        (2*n*(a.2 :ℚ)) := by
  simp only [Jpoly,bw4,a1R,a3C,zvF,zfY,
    zbr,zFf,zB5,rayE_shift_eval,id_eq,zero_mul,
    one_mul,add_zero,zero_add]
  ring
private theorem sah (b j f b' j' f' L:ℚ) (N :ℕ) (hb:b=b') (hj:j=j') (hf :f=f')
    (hL: (N :ℚ)=L) :bw4 b j f N=bw4 b' j' f' L:= by
  subst hb hj hf hL
  rfl
theorem proof :qqJLTVc.c2 := by
  intro a d ha
  refine ⟨Jpoly 0 a-Jpoly (-(aD d)) a,?_,?_⟩
  · have hX (p:zM1 ℚ) : (𝕏*p).coeff 4=p.coeff 3:=Polynomial.coeff_X_mul p 3
    simp only [Jpoly,zsl,Polynomial.coeff_add,hX,
      Polynomial.coeff_C_mul,a1R,a3C,rayE_coeff,ray3,volumeDerivative]
    ring
  · intro n hn hch
    rw [eqr _ (BP a ha n),eqr _ hch,zfY,Jeval,Jeval]
    have h1 :=gwP ((agj a n).1.b:ℚ) ((agj a n).1.j:ℚ)
      ((agj a n).1.t:ℚ) (2*(agj a n).2)
    have h2 :=gwP ((subtractHorizontal (agj a n) d).1.b:ℚ)
      ((subtractHorizontal (agj a n) d).1.j:ℚ)
      ((subtractHorizontal (agj a n) d).1.t:ℚ) (2*(subtractHorizontal (agj a n) d).2)
    obtain ⟨hb,hj,ht⟩:=hn
    have hb' : d.b≤n*a.1.b:=hb
    have hj' : d.j≤n*a.1.j:=hj
    have ht' : d.t≤n*a.1.t:=ht
    congr 1
    · refine (h1.trans (sah _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_)).symm <;>
        simp [agj,Shape.scale] <;> ring
    · refine (h2.trans (sah _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_)).symm <;>
        simp [agj,Shape.scale,subtractHorizontal,aD,
          zjK hb',zjK hj',zjK ht'] <;> ring
end
end qBcCKJc
end
section
set_option autoImplicit true
set_option maxRecDepth 4096
namespace qbVMAwc
open aR (Shape)
open P6_6 P6_6_8
open P6_6_8_3 (caps retainedBox layerMass)
open private mass_anti width total from ProximityPrize.SubmissionLower.Zsr715c
open private WC bP5 aEH byM bvX from ProximityPrize.SubmissionLower.E6
open private bSj.aTY from ProximityPrize.SubmissionLower.E6
open private eiI from ProximityPrize.SubmissionLower.E6
open scoped BigOperators
abbrev kd (v :Shape) :Shape :=⟨1,(caps (retainedBox v)).j+1,0⟩
abbrev Test (v :Shape) :Prop :=CompanionTest v (kd v) (sharedOrder v)
abbrev Cut (b j c k :ℕ) :Prop :=CompanionTest ⟨b,j,1⟩ ⟨1,c,0⟩ k
theorem transfer {b j t lo k c:ℕ} (hb:lo≤b) (ht:1≤t)
    (hk :sharedOrder ⟨b,j,1⟩≤k) (hc:c≤(kd ⟨b,j,1⟩).j)
    (h:CompanionTest ⟨lo,j,1⟩ ⟨1,c,0⟩ k) :Test ⟨b,j,t⟩:= by
  change CompanionTest _ _ _
  unfold CompanionTest at h ⊢
  refine (zQk fun d _=>dNb (nZ.zK
    (Q5 (x :=⟨lo,j,1⟩) (y :=⟨b,j,t⟩) ⟨hb,le_rfl,ht⟩ (d+1)) ?_)).trans_lt h
  have hd:=Nat.sub_le_sub_left hk (d+2)
  exact ⟨ztf 1 hd,
    Nat.mul_le_mul hd hc,le_rfl⟩
private theorem homogeneous (x :Shape) :
    Gq x≤AJ.ahC Wk x := by
  unfold Gq AJ.ahC
  split
  next _ =>
    change _≤wV.HY (4025 - x.b+1) (1710 - x.j) (570 - x.t)
    rw [bSj.aTY]
    exact zQk fun _ _=>eiI (min_le_left _ _) le_rfl le_rfl
  next _=>exact le_rfl
private def sample (v r :Shape) (ell cut i:ℕ) :ℕ :=
  let x :=(v.scale (i+1)).plus (r.scale (i+2 - ell))
  if i<cut then q33KzTa.stock x else AJ.ahC Wk x
private theorem euU (v r :Shape) (ell cut i:ℕ) :
    layerMass v r ell i≤ sample v r ell cut i:= by
  rw [layerMass,aUJ]
  unfold sample
  split
  · rw [q33KzTa.stock_eq]
  · apply homogeneous
private def xF (stop Fy adj ell:ℕ) :ℕ→ℕ→List ℕ
  | 0,_=>[]
  | fuel+1,i =>
    if i<stop then
      let endGap:=stop - i
      let step:=min endGap (max 1 (Fy*(if i+2≤ell then adj else 1)/endGap))
      step :: xF stop Fy adj ell fuel (i+step)
    else []
private def blocks (stop Fy adj cut ell:ℕ) :
    ℕ→List ℕ→List (List ℕ×ℕ)
  | _,[]=>[]
  | i,value :: values =>
    let ws :=xF stop Fy adj ell (if i<cut then 6 else 24) i
    (ws,value) :: blocks stop Fy adj cut ell (i+ws.sum) values
private abbrev ki:ℕ:=0x1000000
private theorem round_le {m n:ℕ} (h: (m+(ki - 1))/ki=n) :
    m≤n*ki:= by
  have hd: (m+(ki - 1))/ki<n+1 := by
    rw [h]
    exact Nat.lt_succ_self _
  have hm:=(Nat.div_lt_iff_lt_mul (show 0<ki by decide)).mp hd
  rw [Nat.add_mul,Nat.one_mul] at hm
  change m+0xffffff<n*0x1000000+0x1000000 at hm
  change m≤n*0x1000000
  omega
def ay (v r :Shape) (ell cut start:ℕ) :List (List ℕ×ℕ)→Prop
  | []=>True
  | (ws,value) :: rest =>
    (aEH (sample v r ell cut) start ws+(ki - 1))/ki=value ∧
      ay v r ell cut (start+ws.sum) rest
private theorem bound (v r :Shape) (ell cut:ℕ) (chunks :List (List ℕ×ℕ))
    (start:ℕ) (h:ay v r ell cut start chunks) :
    WC (layerMass v r ell) start (width chunks)≤total chunks*ki:= by
  induction chunks generalizing start with
  | nil=>simp only [width,total,WC,Finset.range_zero,Finset.sum_empty,Nat.zero_mul,le_refl]
  | cons chunk rest ih =>
    obtain ⟨ws,value⟩:=chunk
    rw [width,total,bP5,Nat.add_mul]
    exact Nat.add_le_add
      ((byM (mass_anti v r ell) ws start).trans
        ((bvX (euU v r ell cut) ws start).trans (round_le h.1)))
      (ih _ h.2)
theorem reject {b j c ell cut len Fy adj value :ℕ} (zs :List ℕ)
    (hs :ay ⟨b,j,1⟩ ⟨1,c,0⟩ ell cut 0 (blocks len Fy adj cut ell 0 zs))
    (hlen:width (blocks len Fy adj cut ell 0 zs)=len)
    (hval :zs.sum=value) (hz :layerMass ⟨b,j,1⟩ ⟨1,c,0⟩ ell len=0)
    (hn:value≤0x161831) :Cut b j c ell:= by
  have hn' : value*ki<gG :=
    (ztf ki hn).trans_lt (by decide)
  have hb:=bound _ _ _ _ _ _ hs
  have htotal (i:ℕ) (xs :List ℕ) :
      total (blocks len Fy adj cut ell i xs)=xs.sum:= by
    induction xs generalizing i with
    | nil=>rfl
    | cons v vs ih=>simp only [blocks,total,ih,List.sum_cons]
  rw [hlen,htotal,hval] at hb
  unfold Cut CompanionTest
  simp_rw [← aUJ]
  change (∑ i∈Finset.range ack,layerMass ⟨b,j,1⟩ ⟨1,c,0⟩ ell i)<gG
  rw [FI.aQD _ len (fun i hi =>
    Nat.eq_zero_of_le_zero (((mass_anti _ _ _) hi).trans_eq hz))]
  exact ((Finset.sum_le_sum_of_subset (Finset.range_mono (min_le_right _ _))).trans
    (by simpa only [WC,Nat.zero_add] using hb)).trans_lt hn'
end qbVMAwc
end
section
set_option autoImplicit true
namespace qCfmNSd
open P6_6_8 (edge c8J)
theorem proof :P6_6_8_3.c3:= by
  intro v hv hne
  change dM v
  obtain ⟨_,hj,ht,_⟩:=c8J hv
  rcases hv with hz | ⟨hv,hb⟩
  · exact (hne hz).elim
  obtain ⟨b,j,t⟩:=v
  obtain ⟨hp,hmin,hmax⟩:=hv
  change b≤edge j at hb
  change j≤7 at hj
  change t≤2 at ht
  change 1≤t at hp
  change 3*t≤j at hmin
  change j≤3*b at hmax
  have hlo:3≤j:= by omega
  interval_cases j <;> interval_cases t <;> try omega
  · exact lane3_1 b (by omega) hb
  · exact lane4_1 b (by omega) hb
  · exact lane5_1 b (by omega) hb
  · exact lane6_1 b (by omega) hb
  · exact lane6_2 b (by omega) hb
  · exact lane7_1 b (by omega) hb
  · exact lane7_2 b (by omega) hb
end qCfmNSd
end
