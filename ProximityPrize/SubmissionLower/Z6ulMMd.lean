import ProximityPrize.SubmissionLower.ZfbLZnc
import ProximityPrize.SubmissionLower.Znc9Sbd
import ProximityPrize.SubmissionLower.ZasomWd
import ProximityPrize.SubmissionLower.ZSyXMse
import ProximityPrize.SubmissionLower.ZEPBkvd
set_option Elab.async false
open _root_ renaming Fin.sum_univ_succ → zCS, Fin.sum_univ_three → zCj, Fin.sum_univ_zero → zDT, Finset.sum_le_sum → zQk, Function.Embedding.subtype → zFQ, Function.Injective → zq4, Nat.add_le_add → z9f, Nat.add_le_add_right → zlr, Nat.cast_le → z9h, Nat.cast_mul → z2R, Nat.cast_nonneg → zqJ, Nat.cast_sum → zCt, Nat.mul_le_mul → zcp, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Nat.sub_le_sub_right → zIu, Polynomial.map_injective → zTo, RingHom.id → zz4
section
set_option autoImplicit true
set_option Elab.async false
namespace qPZthme
noncomputable section
open P6 (K)
open P6_7_3 (Input)
open P5_7_7 (phys)
open cu (L FX qD jz)
open scoped Classical WithZero
section weight
open Polynomial hiding expand coeff_expand
open Finset qQ9yWTb qb0hmCe q1kuFjb qGWTmVd
open E7 (Gb)
open private expand coeff_expand c0Q wdeg le_wdeg raw_factor from ProximityPrize.SubmissionLower.ZgKNZbc
private theorem factor_weight {q:Curve} (B:CurveModel q) (a s :ℕ) {F:Raw} (hn:restrict B F≠0) {W:ℕ}
    (hw : ∀ R:Raw,Irreducible R→R∣F→q4Pefpa.load a (a+s) R≤W)
    (g:B.E[X][X]) (hg:Irreducible g) (hd:g∣restrict B F) (i:ℕ) :
    (g.coeff i).natDegree+g.natDegree*a+i*s≤W∨g.coeff i=0:= by
  by_cases he :g.coeff i=0
  · exact Or.inr he
  left
  obtain ⟨R,hr,hrF,hdiv⟩:=raw_factor B F hn g hg hd
  have hR:restrict B R≠0:= by
    obtain ⟨a,ha⟩:=map_dvd (restrict B) hrF
    intro hz
    exact hn (by simp only [ha,hz,zero_mul])
  have hdeg:=(natDegree_le_of_dvd hdiv hR).trans (restrict_degree B R)
  have hle {i j:ℕ} (h: (((restrict B R).coeff i).coeff j)≠0) :
      j+i*s+R.natDegree*a≤W:= by
    rw [restrict_coeff] at h
    obtain ⟨m,hm,hterm⟩:=Finset.exists_ne_zero_of_sum_ne_zero h
    have hk : (((R.coeff i).coeff m).coeff j)≠0:= fun hz=>hterm (by simp [hz])
    have hi:i∈R.support :=mem_support_iff.mpr (fun hz=> by simp [hz] at hm)
    have hload :=hw R hr hrF
    simp only [q4Pefpa.load,Nat.add_sub_cancel_left] at hload
    have hlim:=(le_sup_of_le hi (le_sup (f := fun m =>
      ((R.coeff i).coeff m).natDegree+R.natDegree*a+i*s) hm)).trans hload
    have hj:=le_natDegree_of_ne_zero hk
    omega
  have hW:wdeg s (restrict B R)+R.natDegree*a≤W:= by
    have hz :expand (restrict B R)≠0:=(map_ne_zero_iff _ expand.injective).mpr hR
    unfold wdeg MvPolynomial.weightedTotalDegree
    rw [Finset.sup_add (MvPolynomial.support_nonempty.mpr hz)]
    apply Finset.sup_le
    intro d hd
    rw [c0Q]
    exact hle (by simpa only [coeff_expand] using MvPolynomial.mem_support_iff.mp hd)
  have hy :wdeg s g≤wdeg s (restrict B R) :=
    MvPolynomial.weightedTotalDegree_le_of_dvd _ (map_dvd expand hdiv) (by simpa using hR)
  have hterm :=le_wdeg (s :=s) (leadingCoeff_ne_zero.mpr he)
  have hshift:=ztf a hdeg
  omega
private theorem prepareFactors {q:Curve} (hq:Irreducible q) (B:CurveModel q)
    (hb:Gb L B.E B.seed≤q.totalDegree) (F:Raw) (e a s W:ℕ)
    (hm:Moving F) (he :F.natDegree≤e)
    (hw : ∀ R:Raw,Irreducible R→R∣F→q4Pefpa.load a (a+s) R≤W) :
    Nonempty (Factors B F e a s W) := by
  have hn:=restrict_ne hq B hm
  obtain ⟨S⟩:=factorize hn
  obtain ⟨hs,hh⟩:=factor_heights B hb F hn S
  refine ⟨⟨b5S hn,hs,S.amm,S.monic,S.n,S.f,S.product,S.irreducible,
    S.positive,S.normalized,(S.degree hn).le.trans ((restrict_degree B F).trans he),hh,?_⟩⟩
  intro j i
  apply factor_weight B a s hn hw (S.f j) (S.irreducible j) _ i
  calc
    S.f j ∣ ∏ k,S.f k :=dvd_prod_of_mem S.f (mem_univ j)
    _∣C (C (headScalar (restrict B F))*S.amm) * ∏ k,S.f k :=
      dvd_mul_left _ _
    _∣restrict B F:=S.product.symm.dvd
end weight
open Polynomial q1kuFjb
open qQ9yWTb (Raw Curve embed height Usable)
open qb0hmCe (CurveModel cLN specialize zD)
open qy95ATd (WordChart root site left)
open qH2fULd (Sheet)
open private specialize_phys_ne from ProximityPrize.SubmissionLower.ZyCQ7Ke
private theorem root_restrict {x :Input} {U:Finset K} (J:WordChart x U) (F:Raw) (γ:K)
    (h:root J F γ) :
    specialize (restrictOver (zz4 L) (site x γ) F) (J.P γ) (J.Q γ)=0:= by
  unfold root embed at h
  unfold specialize restrictOver
  rw [eval₂_eq_eval_map] at h ⊢
  simp only [coe_mapRingHom,Polynomial.map_map] at h ⊢
  change _=0 at h
  have hm:phys.comp (MvPolynomial.eval₂Hom (mapRingHom (zz4 L)) (C ∘ site x γ)) =
      (qD (x.M.label γ)).comp (MvPolynomial.map phys) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [qD]
    · intro i
      simp only [RingHom.comp_apply,MvPolynomial.eval₂Hom_X',Function.comp_apply,
        MvPolynomial.map_X,qD,MvPolynomial.eval_X]
      fin_cases i <;>
        simp [site,jz,phys]
  rw [hm]
  exact h
private theorem factor_root {x :Input} {U:Finset K} (J:WordChart x U) {γ:K}
    {q:Curve} {Cq:CurveModel q} (A:AtSite Cq (site x γ))
    {F:Raw} {e a s W:ℕ} (B:Factors Cq F e a s W)
    (hr :root J F γ)
    (hs : ¬ A.place.value (headScalar (restrict Cq F))<1)
    (hp:coeffIntegral A.place.value (C B.amm))
    (hf : ∀ j,coeffIntegral A.place.value (B.f j)) :
    ∃ j,specialize (cLN A.map 0 (B.f j)) (J.P γ) (J.Q γ)=0:= by
  obtain ⟨g,hg,hg'⟩:=integral_restrict A F
  let r :=restrict Cq F
  let c:=headScalar r
  have hc: (Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (A.map c)≤1 := by
    have he :=congrArg (fun f : (LaurentSeries L)[X][X] =>
      (f.coeff r.natDegree).coeff (r.coeff r.natDegree).natDegree) hg
    simp only [mapTwice,coe_mapRingHom,coeff_map,Subring.subtype_apply,coeff_natDegree] at he
    change ((g.coeff r.natDegree).coeff (r.coeff r.natDegree).natDegree :LaurentSeries L) =
      A.map c at he
    rw [← he,LaurentSeries.val_le_one_iff_eq_coe]
    exact ((g.coeff r.natDegree).coeff (r.coeff r.natDegree).natDegree).2.elim
      (fun z hz=>⟨z,hz.2⟩)
  have hs' : (A.map c).coeff 0≠0:= by
    intro h
    obtain ⟨z,hz⟩:=(LaurentSeries.val_le_one_iff_eq_coe L (A.map c)).mp hc
    have hv :=(small_valuation z).mpr ((power_residue _ z hz.symm).symm.trans h)
    exact hs (by rw [A.value,← hz]; exact hv.trans_lt (WithZero.exp_lt_one_iff.mpr (by decide)))
  let d:=integralSeries (A.map c) hc
  let f₀:=Ua A.map (C B.amm) (fun i j=>A.value _ ▸ hp i j)
  let f₁ (k :Fin B.n) :=Ua A.map (B.f k) (fun i j=>A.value _ ▸ hf k i j)
  have hm:mapTwice IntSeries.subtype (C (C d))=mapTwice A.map.toRingHom (C (C c)) := by
    simp only [mapTwice,coe_mapRingHom,map_C]
    rfl
  have hprod:r=C (C c)*C B.amm * ∏ k,B.f k :=
    B.product.trans (congrArg (fun f=>f * ∏ k,B.f k) (map_mul C _ _))
  have he :g=C (C d)*f₀ * ∏ k,f₁ k := by
    apply zTo (mapRingHom IntSeries.subtype)
      (zTo IntSeries.subtype IntSeries.subtype_injective)
    change mapTwice IntSeries.subtype g=mapTwice IntSeries.subtype _
    rw [hg]
    change mapTwice A.map.toRingHom r= _
    rw [hprod]
    simp only [map_mul,map_prod,hm,f₀,f₁,map_liftAt]
  have he' := congrArg (mapTwice residue) he
  rw [hg',map_mul,map_mul,map_prod] at he'
  have h0:mapTwice residue f₀=cLN A.map 0 (C B.amm) :=liftAt_reduce _ _ _
  have h1 (k :Fin B.n) :mapTwice residue (f₁ k)=cLN A.map 0 (B.f k) :=liftAt_reduce _ _ _
  simp only [h0,h1] at he'
  let ev :=eval₂RingHom phys (phys (J.P γ)/phys (J.Q γ))
  have hz :ev (restrictOver (zz4 L) (site x γ) F)=0:=root_restrict J F γ hr
  rw [he',map_mul,map_mul,map_prod,mul_eq_zero] at hz
  have hn:ev (mapTwice residue (C (C d))) *
      ev (cLN A.map 0 (C B.amm))≠0:= by
    refine mul_ne_zero ?_ (specialize_phys_ne A.map B.monic (J.P γ) (J.Q γ))
    simp only [mapTwice,coe_mapRingHom,map_C,ev,coe_eval₂RingHom,eval₂_C]
    rw [fWQ]
    change phys (C ((A.map c).coeff 0))≠0
    exact (map_ne_zero_iff _ (IsFractionRing.injective L[X] FX)).mpr (C_ne_zero.mpr hs')
  obtain ⟨j,_,hj⟩:=Finset.prod_eq_zero_iff.mp (hz.resolve_left hn)
  exact ⟨j,hj⟩
open Finset
private def assembleSheet {x :Input} {U:Finset K} (J:WordChart x U)
    {q:Curve} {Cq:CurveModel q} {M:Finset K} (hM:M⊆U) (γ₀:M)
    (A : ∀ γ:M,AtSite Cq (site x γ.val))
    (hA:zq4 fun γ=>(A γ).place)
    (f :Cq.E[X][X]) (hi:Irreducible f) (hd:0<f.natDegree) (hn:headScalar f=1)
    (N :Finset M) (hN : ∀ γ∈N,coeffIntegral (A γ).place.value f ∧
      ((cLN (A γ).map 0 f).map phys).Separable ∧
      specialize (cLN (A γ).map 0 f) (J.P γ.val) (J.Q γ.val)=0) :Sheet J Cq:= by
  let sub:M ↪ K:=zFQ _
  have hm (γ:K) (hγ:γ∈N.map sub) :γ∈M:= by
    obtain ⟨δ,_,rfl⟩:=mem_map.mp hγ
    exact δ.property
  have hr (γ:K) (hγ:γ∈N.map sub) : (⟨γ,hm γ hγ⟩:M)∈N := by
    obtain ⟨δ,hδ,he⟩:=mem_map.mp hγ
    have h:δ=⟨γ,hm γ hγ⟩:=Subtype.ext he
    exact h ▸ hδ
  let localAt (γ:K) (h:γ∈N.map sub) :=A ⟨γ,hm γ h⟩
  let v (γ:K) :=if h:γ∈M then (A ⟨γ,h⟩).place else (A γ₀).place
  have hv (γ:K) (h:γ∈N.map sub) :v γ=(localAt γ h).place :=dite_eq_left (hm γ h)
  let τ (γ:K) :FX:=if h:γ∈N.map sub then
    zD (localAt γ h).map f (J.P γ) (J.Q γ) else 0
  choose num den hden hred hfrac using fun γ=>reduced_pair (τ γ)
  refine {
    f :=f,irreducible :=hi,positive :=hd,normalized:=hn
    marks :=N.map sub,Bp:= fun γ h=>hM (hm γ h)
    atPlace := fun γ h=>(localAt γ h).map,place :=v
    distinct := ?_,value := ?_,arc := fun γ h=>(localAt γ h).arc
    integral := ?_,root := ?_,separable := ?_,simple := ?_
    num :=num,den:=den,den_ne := fun γ _=>hden γ,reduced:= fun γ _=>hred γ
    formula := ?_ }
  · intro a ha b hb he
    rw [hv a ha,hv b hb] at he
    exact congrArg Subtype.val (hA he)
  · intro γ h c
    rw [hv γ h,(localAt γ h).value c]
  · intro γ h i j
    rw [hv γ h]
    exact (hN _ (hr γ h)).1 i j
  · intro γ h
    exact (hN _ (hr γ h)).2.2
  · intro γ h
    exact (hN _ (hr γ h)).2.1
  · intro γ h
    obtain ⟨_,hs,hz⟩:=hN _ (hr γ h)
    have hz' : ((cLN (localAt γ h).map 0 f).map phys).eval
        (phys (J.P γ)/phys (J.Q γ))=0:= by
      rw [eval_map]
      exact hz
    have hd:=hs.eval₂_derivative_ne_zero (zz4 FX) (by simpa only [eval₂_id] using hz')
    rw [eval₂_id,derivative_map,eval_map] at hd
    exact hd
  · intro γ h
    exact (hfrac γ).trans (dite_eq_left h)
theorem proof :qH2fULd.c1 := by
  intro x U _ J T hT e W hep F hF hdegree hweight hroot q hq
  obtain ⟨Cq,hpole⟩:=q9Dxm8d.proof q hq
  let M:=T.filter fun γ=>Usable q (site x γ)
  by_cases hM:M.Nonempty
  swap
  · refine ⟨⟨Cq,0,Fin.elim0,fun j=>j.elim0,?_,by simp,by simp,fun j=>j.elim0⟩⟩
    change (M \ _).card≤_
    rw [not_nonempty_iff_eq_empty.mp hM]
    simp
  let A (γ:M) :AtSite Cq (site x γ.val) :=
    Classical.choice (qqpP4De.proof hq Cq _ (mem_filter.mp γ.property).2)
  have hinj:zq4 fun γ=>(A γ).place := by
    intro a b h
    have hz :=congrFun (AtSite.site_eq_of_place (A a) (A b) h) 0
    change algebraMap K L (x.M.label a.val)=algebraMap K L (x.M.label b.val) at hz
    exact Subtype.ext (sub_left_inj.mp ((algebraMap K L).injective hz))
  obtain ⟨B⟩:=prepareFactors hq Cq hpole F e (left J) (J.u₁-J.u₀) W hF hdegree hweight
  have hd (j:Fin B.n) : (B.f j).natDegree≤e :=
    (single_le_sum (fun i _=>Nat.zero_le (B.f i).natDegree) (mem_univ j)).trans B.degree
  let d:=headScalar (restrict Cq F)
  let P (γ:M) :=coeffIntegral (A γ).place.value (C B.amm)
  let Fg (j:Fin B.n) (γ:M) :=
    coeffIntegral (A γ).place.value (B.f j)∧((cLN (A γ).map 0 (B.f j)).map phys).Separable
  let E₀:=univ.filter fun γ:M=>(A γ).place.value d<1
  let E₁:=univ.filter fun γ:M => ¬ P γ
  let E₂ (j:Fin B.n) :=univ.filter fun γ:M => ¬ Fg j γ
  let bad:=(E₀∪E₁)∪univ.biUnion E₂
  let N (j:Fin B.n) :=univ.filter fun γ:M=>Fg j γ ∧
    specialize (cLN (A γ).map 0 (B.f j)) (J.P γ.val) (J.Q γ.val)=0
  let part (j:Fin B.n) :=assembleSheet J ((filter_subset _ _).trans hT)
    ⟨hM.choose,hM.choose_spec⟩ A hinj (B.f j) (B.irreducible j) (B.positive j) (B.normalized j)
    (N j) (fun _ h=>and_assoc.mp (mem_filter.mp h).2)
  have hins (j:Fin B.n) : (part j).marks⊆M:= by
    intro γ hγ
    change γ∈(N j).map (zFQ _) at hγ
    obtain ⟨i,_,rfl⟩:=mem_map.mp hγ
    exact i.property
  refine ⟨⟨Cq,B.n,part,hins,?_,B.degree,?_,B.weight⟩⟩
  swap
  · exact (Nat.le_add_left _ _).trans B.height_le
  have hcover :M \ univ.biUnion (fun j=>(part j).marks) ⊆
      bad.map (zFQ _) := by
    intro γ hγ
    obtain ⟨hγ,hn⟩:=mem_sdiff.mp hγ
    let i:M:=⟨γ,hγ⟩
    apply mem_map.mpr
    refine ⟨i,?_,rfl⟩
    by_contra hbad
    have ⟨hs,hp,hf⟩: (¬ (A i).place.value d<1)∧P i ∧ ∀ j,Fg j i:= by
      simpa only [bad,E₀,E₁,E₂,mem_union,mem_biUnion,mem_univ,true_and,
        mem_filter,not_or,not_not,not_exists,and_assoc] using hbad
    obtain ⟨j,hj⟩:=factor_root J (A i) B (hroot γ (mem_filter.mp hγ).1) hs hp (fun j=>(hf j).1)
    have hm:γ∈(part j).marks :=mem_map.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hf j,hj⟩,rfl⟩
    exact hn (mem_biUnion.mpr ⟨j,mem_univ _,hm⟩)
  let H :=height F*q.totalDegree
  have h₀:E₀.card≤H :=(zero_budget univ _ hinj.injOn B.scalar_ne).trans B.scalar_height
  have h₁:E₁.card≤H :=(integral_budget univ _ hinj.injOn (C B.amm)).trans
    ((Nat.le_add_right _ _).trans B.height_le)
  have h₂ : ∑ j,(E₂ j).card≤2*e*H := by
    refine le_trans ?_ (zBI _ ((Nat.le_add_left _ _).trans B.height_le))
    rw [mul_sum]
    exact sum_le_sum fun j _=>(qb2k8ya.proof Cq univ _ A hinj.injOn (B.f j) (B.irreducible j)
      (B.positive j) ((hd j).trans_lt hep) (B.normalized j)).trans (by gcongr; exact hd j)
  have hsum:bad.card≤H+H+2*e*H :=
    (card_union_le _ _).trans (z9f
      ((card_union_le _ _).trans (z9f h₀ h₁)) (card_biUnion_le.trans h₂))
  calc
    _≤bad.card:=(card_le_card hcover).trans_eq (card_map _)
    _≤H+H+2*e*H :=hsum
    _=(2+2*e)*H := by ring
    _≤(7+2*e)*H :=ztf H (by omega)
    _ = _:= by simp [H,Nat.mul_assoc]
end
end qPZthme
end
section
set_option autoImplicit true
namespace qrT6Ada
noncomputable section
open Finset q3rjQGe
open P6_7_1 (Origin introCap bgK)
open cu (Shape)
open pI (weight)
open TD (FP)
open scoped BigOperators
def mixedN (v :Fin 3→ℕ) (s :Shape) (k :Fin 4) :ℕ :=
  ∑ j,v j*mixedCols s k j
theorem mixed_cast (v :Fin 3→ℕ) (s :Shape) (k :Fin 4) :
    kK v s k=(mixedN v s k :ℚ) := by
  simp only [kK,mixedN,zCt,z2R]
abbrev boxN (o:Origin) (k :Fin 4) :=mixedN (introCap o.val) (originShape o) k
private def freeNum (o:Origin) (i:Free) (k :Fin 4) :ℕ :=
  mixedN (bgK (stage i).free) (refShape o) k*(150/((stage i).dI+1))
def survivedNum (o:Origin) (s :bAL) (k :Fin 4) :ℕ :=
  ((List.ofFn (fun i:Free=>freeNum o i k)).take (s.val-1)).foldl min (boxN o k*150)
def memberNum (o:Origin) (s :bAL) (k :Fin 4) :ℕ :=
  min (survivedNum o s k) (initialN k*150)
private theorem free_cast (o:Origin) (i:Free) (k :Fin 4) :
    freeBound o i k=(freeNum o i k :ℚ)/150:= by
  have hm: (150/((stage i).dI+1))*((stage i).dI+1)=150:= by
    fin_cases i <;> decide
  have hp: (0:ℚ)<((stage i).dI.succ:ℕ) := by positivity
  rw [freeBound,← Nat.cast_succ,mixed_cast,freeNum,z2R]
  apply (div_eq_div_iff hp.ne' (by decide : (150:ℚ)≠0)).mpr
  rw [mul_assoc,← z2R,hm,Nat.cast_ofNat]
private theorem box_cast (n:ℕ) : ((n*150:ℕ) :ℚ)/150=(n:ℚ) := by
  rw [z2R,Nat.cast_ofNat,mul_div_cancel_right₀ _ (by decide : (150:ℚ)≠0)]
private theorem fold_cast (L:List ℕ) (n:ℕ) :
    (L.map (fun (m:ℕ)=>(m:ℚ)/150)).foldl min ((n:ℚ)/150) =
      (↑(L.foldl min n) :ℚ)/150:= by
  induction L generalizing n with
  | nil=>rfl
  | cons m L ih =>
    simp only [List.map_cons,List.foldl_cons,min_div_div_right (by decide : (0:ℚ)≤150),
      ← Nat.cast_min,ih]
theorem survived_cast (o:Origin) (s :bAL) (k :Fin 4) :
    survivedBound o s k=(survivedNum o s k :ℚ)/150:= by
  simp only [survivedBound,free_cast,originBox,mixed_cast,survivedNum]
  rw [List.ofFn_comp' (fun i:Free=>freeNum o i k) (fun n=>(n:ℚ)/150),
    ← List.map_take,← box_cast (boxN o k),fold_cast]
theorem member_cast (o:Origin) (s :bAL) (k :Fin 4) :
    memberCap o s k=(memberNum o s k :ℚ)/150:= by
  rw [memberCap,survived_cast,au9,← box_cast (initialN k),
    min_div_div_right (by decide : (0:ℚ)≤150),← Nat.cast_min,memberNum]
def weightedNum (w:Fin 4→ℕ) (o:Origin) (s :bAL) :ℕ :=
  ∑ k,w k*memberNum o s k
theorem weighted_cast (w:Fin 4→ℕ) (o:Origin) (s :bAL) :
    FP (fun k=>(w k :ℚ)) (memberCap o s)=(weightedNum w o s :ℚ)/150:= by
  simp only [FP,member_cast,weightedNum,zCt,z2R,div_eq_mul_inv,sum_mul]
  exact sum_congr rfl fun k _=>(mul_assoc _ _ _).symm
theorem freeDegree_le (o:Origin) (i:Free) :freeDegree o i≤37000000:= by
  change FP (fun k=>(weight (aHp i.castSucc) 0 k :ℚ))
    (memberCap o i.castSucc.succ)≤_
  rw [weighted_cast]
  apply (div_le_iff₀ (by decide : (0:ℚ)<150)).mpr
  have h:weightedNum (weight (aHp i.castSucc) 0) o i.castSucc.succ≤37000000*150:= by
    simp only [weightedNum,zCS,zDT]
    fin_cases o <;> fin_cases i <;> decide
  exact_mod_cast h
end
end qrT6Ada
end
section
set_option autoImplicit true
set_option exponentiation.threshold 160
namespace qrT6Ada
noncomputable section
open P6_7_1 (Origin)
open q3rjQGe
open pI (weight)
open scoped BigOperators
private theorem member_zero (o:Origin) (k :Fin 4) :
    memberCap o 0 k=(boxN o k :ℚ) := by
  have hn:boxN o k≤ initialN k := by
    simp only [mixedN,zCj]
    fin_cases o <;> fin_cases k <;> decide
  change min (originBox o k) (initialBound k)= _
  rw [au9,originBox,mixed_cast]
  exact min_eq_left (Nat.cast_le.mpr hn)
private theorem rankY (B R:ℕ)
    (h:262144*133440*4*B*46300+128704*5*179740≤R*5*179740*46300) :
    max 0 ((262144 :ℚ)*133440/179740*(4*(B:ℚ)/5-1)+128704/46300)≤(R:ℚ) := by
  apply max_le (zqJ _)
  have hq:=(z9h (α:=ℚ)).mpr h
  push_cast at hq
  calc
    _≤(262144 :ℚ)*133440/179740*(4*(B:ℚ)/5)+128704/46300 :=
      add_le_add (mul_le_mul_of_nonneg_left (sub_le_self _ zero_le_one) (by positivity)) le_rfl
    _≤_:= by linear_combination hq/(5*179740*46300)
private theorem rankZ (B J R:ℕ) (hb:0<B) (hr :1≤R)
    (h:262144*133440*16*J*B+(B+1)*(5*179740*B) ≤
      R*(5*179740*B)+262144*133440*10*J*J) :
    max 1 ((262144 :ℚ)*133440/179740*
      (4*(J:ℚ)-(2*J*J+(4*(B:ℚ)/5)*J)/B-1)+B+1)≤(R:ℚ) := by
  apply max_le (by exact_mod_cast hr)
  have hB: (0:ℚ)<B:= by exact_mod_cast hb
  have hq:=(z9h (α:=ℚ)).mpr h
  push_cast at hq
  let V:=4*(J:ℚ)-(2*J*J+(4*(B:ℚ)/5)*J)/B
  calc
    _≤(262144 :ℚ)*133440/179740*V+B+1 :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (sub_le_self _ zero_le_one) (by positivity)) le_rfl) le_rfl
    _≤_:= by
      apply (mul_le_mul_iff_right₀ (show (0:ℚ)<5*179740*(B:ℚ) by positivity)).1
      have hv :5*179740*(B:ℚ)*((262144 :ℚ)*133440/179740*V+B+1) =
        262144*133440*16*J*B+(B+1)*(5*179740*B)-262144*133440*10*J*J:= by
        dsimp [V]
        field_simp [hB.ne']
        ring
      rw [hv]
      linear_combination hq
theorem rank_covered (o:Origin) (k :Fin 4) :rankPrice o k≤ residual o k := by
  have hb:0<boxN o 2 := by simp only [mixedN,zCj]; fin_cases o <;> decide
  have hbQ: (0:ℚ)<(boxN o 2 :ℚ) := by exact_mod_cast hb
  have hJ:5*boxN o 1≤4*boxN o 2 := by
    simp only [mixedN,zCj]
    fin_cases o <;> decide
  have hJQ:=(z9h (α:=ℚ)).mpr hJ
  push_cast at hJQ
  have hj: (boxN o 1 :ℚ)≤(boxN o 2 :ℚ) := by linarith only [hJQ,hbQ]
  have hj' : (boxN o 1 :ℚ)≤(boxN o 2 :ℚ)-4*(boxN o 2 :ℚ)/5/4 := by
    linarith only [hJQ]
  simp only [rankPrice,member_zero,min_eq_left hj,min_eq_left hj',ite_eq_right hbQ.ne',residual]
  fin_cases k
  · exact zqJ _
  · apply rankY
    simp only [mixedN,zCj]
    fin_cases o <;> decide
  · apply rankZ _ _ _ hb
    · fin_cases o <;> decide
    · simp only [mixedN,zCj]
      fin_cases o <;> decide
  · exact zqJ _
private def freeCeil:Fin 4→ℕ := ![0x2115bed6e4,0x2b11f9ff2,0xc694f20e,399040]
private theorem freeN_le (o:Origin) (i:Free) (k :Fin 4) :
    38740117*weight (aHp i.castSucc) 0 k+4640*weight (aHp i.castSucc) 1 k ≤
      residualN o k := by
  apply le_trans (b:=freeCeil k)
  · fin_cases i <;> fin_cases k <;> decide
  · fin_cases o <;> fin_cases k <;> decide
private theorem free_covered (o:Origin) (i:Free) (k :Fin 4) :
    corePrice o i.castSucc.succ k≤a3D o i.castSucc.succ k := by
  have hn:i.castSucc.succ≠termStop:= by
    intro h
    have hv :=congrArg Fin.val h
    change i.val+1=5 at hv
    omega
  simp only [corePrice,Fin.cases_succ,Fin.lastCases_castSucc,a3D,Pi.add_apply,freePart,
    hn,and_false,ite_false,Pi.zero_apply,add_zero,a,b,SS,residual]
  exact_mod_cast freeN_le o i k
private def dualScaled:Fin 4→ℕ := ![8*dualNum0,8*dualNum1,20*dualNum2,0]
private theorem dual_scaled (k :Fin 4) :freeDual k=(dualScaled k :ℚ)/4000:= by
  fin_cases k
  · change (dualNum0:ℚ)/500=((8*dualNum0:ℕ) :ℚ)/4000
    push_cast
    ring
  · change (dualNum1 :ℚ)/500=((8*dualNum1 :ℕ) :ℚ)/4000
    push_cast
    ring
  · change (dualNum2 :ℚ)/200=((20*dualNum2 :ℕ) :ℚ)/4000
    push_cast
    ring
  · exact (zero_div _).symm
private theorem rect_row {zn an bn xn yn rn dn:ℕ}
    (h:4000*(zn+an+1)*xn+125*bn*yn≤4000*rn+dn) :
    ((zn:ℚ)+an+1)*xn+(bn:ℚ)/32*yn≤(rn:ℚ)+(dn:ℚ)/4000:= by
  have hq:=(z9h (α:=ℚ)).mpr h
  push_cast at hq
  linear_combination hq/4000
private theorem rect_covered (o:Origin) (k :Fin 4) :
    corePrice o termStop k≤a3D o termStop k := by
  have hdual:freePart o termStop k=((if o=0 then dualScaled k else 0:ℕ) :ℚ)/4000:= by
    simp only [freePart,and_true]
    by_cases h:o=0
    · simpa only [h,ite_true] using dual_scaled k
    · simp only [h,ite_false,Pi.zero_apply,Nat.cast_zero,zero_div]
  simp only [corePrice,Fin.cases_succ,Fin.lastCases_last,a3D,Pi.add_apply,hdual,
    residual,z,ar,br,axisWeight,SS]
  apply rect_row
  fin_cases o <;> fin_cases k <;> decide
theorem cut_covered (o:Origin) (t:Trial) (k :Fin 4) :
    corePrice o t.succ k≤a3D o t.succ k :=
  Fin.lastCases (rect_covered o k) (fun i=>free_covered o i k) t
end
end qrT6Ada
end
section
set_option autoImplicit true
set_option exponentiation.threshold 160
namespace qrT6Ada
open cu (Shape)
open P6_7_1 (lineFee lastOrigin)
open q3rjQGe (asShape kK mixedCols originShape)
open TD (FP a3x)
open scoped BigOperators
private abbrev bw:ℕ:=0xe73e2dd242d00
private theorem line_cap {b j u:ℕ} (hb:b≤12) (hj:j≤2) (hu:u≤142) :
    lineFee b j u≤bw:= by
  let a :=1+266877*(b - 1)
  let z :=min a (266877*(j - 1)+133440)
  let t:=266877*u
  let m:=u*(2*a*z-z*z)+2*t*(b*z+j*(a-z))
  let n:=u*(2*a+z)+t*(2*b+j)+b*z+j*a+u+b+j
  have ha :a≤2935648 :=
    Nat.add_le_add_left (zBI _ (zIu hb 1)) 1
  have hz :z≤400317:=(min_le_right _ _).trans
    (zlr (zBI _ (zIu hj 1)) 133440)
  have ht:t≤37896534 :=zBI 266877 hu
  have hm:m≤0x40f6b144fa950 :=
    z9f
      (zcp hu ((Nat.sub_le _ _).trans (zcp (zBI 2 ha) hz)))
      (zcp (zBI 2 ht)
        (z9f (zcp hb hz) (zcp hj ((Nat.sub_le _ _).trans ha))))
  have hn₁:=zcp hu (z9f (zBI 2 ha) hz)
  have hn₂:=zcp ht (z9f (zBI 2 hb) hj)
  have hn₃:=z9f (z9f hn₁ hn₂) (zcp hb hz)
  have hn:n≤0x7072884a :=z9f
    (z9f (z9f (z9f hn₃ (zcp hj ha)) hu) hb) hj
  change (164808*(m+n)+46300-1)/46300+b+u+1≤_
  calc
    _≤(164808*(0x40f6b144fa950+0x7072884a)+46300-1)/46300+12+142+1 := by
      refine zlr (z9f (z9f (Nat.div_le_div_right ?_) hb) hu) 1
      exact zIu (zlr (zBI 164808
        (z9f hm hn)) 46300) 1
    _=bw:=rfl
private def upper :Shape :=⟨0,14,2,142⟩
private theorem cols_le {v :Fin 3→ℕ} (hb:v 0≤12) (hj:v 1≤2) (hu:v 2≤142)
    (k :Fin 4) (j:Fin 3) :mixedCols (asShape v) k j≤ mixedCols upper k j:= by
  fin_cases k <;> fin_cases j <;> first
    | exact Nat.zero_le _
    | exact hb.trans (by decide :12≤14)
    | exact hj
    | exact hu
    | exact (Nat.sub_le _ _).trans hb
private theorem credit_nat (j:Fin 3) :
    (∑ k :Fin 4,residualN lastOrigin k*mixedCols upper k j) +
      (if j=1 then bw else 0) ≤
    ∑ k :Fin 4,residualN lastOrigin k*mixedCols (originShape lastOrigin) k j:= by
  have hs :originShape lastOrigin=⟨0,373,69,3188⟩:= by with_unfolding_all rfl
  rw [hs]
  simp only [zCS,zDT,add_zero]
  fin_cases j
  · with_unfolding_all exact (show 0x33ba90fdbf5a≤0x624d9c8456df8 by decide)
  · with_unfolding_all exact (show 0x120c368ca5ff4+bw≤0x1ba19e77c810d8 by decide)
  · with_unfolding_all exact (show 0x2fab10e3f2e≤0x5861cca2d549 by decide)
private theorem line_credit (j:Fin 3) :
    (∑ k :Fin 4,residual lastOrigin k*(mixedCols upper k j:ℚ)) +
      (if j=1 then (bw:ℚ) else 0)≤unit lastOrigin j:= by
  have h:=(z9h (α:=ℚ)).mpr (credit_nat j)
  by_cases hj:j=1 <;>
    simpa only [hj,ite_true,ite_false,Nat.cast_add,zCt,z2R,Nat.cast_zero,
      residual,unit] using h
theorem absorbs :Absorbs := by
  intro v hv _ hj _
  have hb:v 0≤12 :=(hv 0).trans_eq (by with_unfolding_all rfl)
  have hj' : v 1≤2 :=(hv 1).trans_eq (by with_unfolding_all rfl)
  have hu:v 2≤142 :=(hv 2).trans_eq (by with_unfolding_all rfl)
  have hf :=(z9h (α:=ℚ)).mpr (line_cap hb hj' hu)
  have hjQ: (1 :ℚ)≤(v 1 :ℚ) :=Nat.cast_le.mpr (show 1≤v 1 from hj)
  have hm:FP (residual lastOrigin) (kK v (asShape v)) ≤
      FP (residual lastOrigin) (kK v upper) :=
    a3x (fun k=>zqJ (residualN lastOrigin k)) fun k =>
      zQk fun j _=>mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (cols_le hb hj' hu k j)) (zqJ (v j))
  calc
    _≤(bw:ℚ)*(v 1 :ℚ)+FP (residual lastOrigin) (kK v upper) :=
      add_le_add (hf.trans (le_mul_of_one_le_right (zqJ bw) hjQ)) hm
    _ = ∑ j:Fin 3,((∑ k :Fin 4,residual lastOrigin k*(mixedCols upper k j:ℚ)) +
        (if j=1 then (bw:ℚ) else 0))*(v j:ℚ) := by
      rw [dot_mixed]
      simp only [add_mul,Finset.sum_add_distrib,ite_mul,zero_mul,Finset.sum_ite_eq',
        Finset.mem_univ,ite_true,add_comm]
    _≤_:=zQk fun j _=>mul_le_mul_of_nonneg_right (line_credit j) (zqJ _)
end qrT6Ada
end
section
set_option autoImplicit true
namespace qrT6Ada
noncomputable section
open q3rjQGe
def c1 :Prop := ∀ o i,FreeRateOK (freeDegree o i) (a o i) (b o i)
def c2 :Prop := ∀ o,RectRateOK (axisCap o) (planeCap o) (z o) (ar o) (br o)
theorem of_children (h1 :c1) (h2 :c2) :c7:= by
  have hp o (s :bAL) k :corePrice o s k≤a3D o s k := by
    refine Fin.cases ?_ (fun t=>cut_covered o t k) s
    simpa only [corePrice,Fin.cases_zero,a3D,Pi.add_apply,freePart,
      show (0:bAL)≠termStop by decide,and_false,ite_false,Pi.zero_apply,add_zero] using rank_covered o k
  exact ⟨⟨a,b,z,ar,br,h1,h2,fun B =>
    (add_le_add (add_le_add (weakDual B absorbs unit_le hp) le_rfl) le_rfl).trans books_le⟩⟩
end
end qrT6Ada
end
section
set_option autoImplicit true
namespace qQL1kze
open qPQ4nYa (rankBudget originRange_le_sum)
theorem proof :q84jfie.c2 := by
  intro b
  have hb : ∃ p:ℕ→ℕ→Rj.kJ,rankBudget b p≤b.contactRank := by
    cases b
    · exact P5_7_2_3Q1322.proof
    · exact P5_7_2_3Q132.proof
  obtain ⟨p,hp⟩:=hb
  exact (originRange_le_sum b p
    (fun q hq k hk=>qzM5sEd.proof b q k hq hk (p q k))).trans hp
end qQL1kze
end
