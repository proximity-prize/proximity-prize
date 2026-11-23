import ProximityPrize.SubmissionLower.ZLVq30b
import ProximityPrize.SubmissionLower.Z5rjxle
import ProximityPrize.SubmissionLower.ZCEtgbe
import ProximityPrize.SubmissionLower.ZMNCpvb
import ProximityPrize.SubmissionLower.ZsazLcd
import ProximityPrize.SubmissionLower.ZzzlQ7b
import ProximityPrize.SubmissionLower.Zt62ONe
import ProximityPrize.SubmissionLower.ZmJja2a
import ProximityPrize.SubmissionLower.ZnGdvBe
set_option Elab.async false
open _root_ renaming Function.Injective → zq4, Module.finrank → zsE, MvPolynomial.eval → zY9, Nat.add_le_add → z9f, Nat.add_le_add_right → zlr, Nat.mul_le_mul_left → zBI, Polynomial.map_injective → zTo, PowerSeries → zpm, PowerSeries.constantCoeff → zbO
section
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qeHk2sb
noncomputable section
open Polynomial
open P5 (K p)
open qK3TPae (highFee)
open quN7Z4a (physicalWeight)
open cu (L)

open qBd5KZd (j3 sections Allowance pull weight
  integral small avoids bounded roots mass btN pull_irreducible)
open qZcMfNa (resultant_bounded)
open qX9S3Pd (seed_bounds)
open qgcZtNc (markedResultant)
open private qL irred_resultant small_pow pole_le zero_ge from ProximityPrize.SubmissionLower.Zw100fa
open scoped Classical WithZero
theorem amplified (Q:Cu.sQ) [Fact (Irreducible Q)]
    (J:Ideal gT.kM) (T:Finset K) (z :K→K) (s :K→K[X]) (D e H g c W M:ℕ)
    (F:quN7Z4a.Sheet Q J e H T z s) (he3:3≤e) (heP:e<p)
    (hok :P6_7_2_3.NativeOK D e g c W M) (hW:W<physicalWeight D F.root.equation)
    (hz :Set.InjOn z (T:Set K)) (hd : ∀ γ∈T,(s γ).natDegree≤D) :
    ∃ C:qK3TPae.AmplifiedCut T,
      C.ng.sum (fun _ n=>n)<p^C.order*(highFee e g c*H+1) := by
  obtain ⟨C,f,A,hfP,hfI,hfE,hfW,hA,hAway,hfA,hRoots⟩:=qWY4iub.bY F hz
    (qWY4iub.height_le F.bY F.height (seed_bounds Q).2.1)
  have hfW:=hfW D
  let j:=(g+1)*c/(c+1)
  let N :=(g+1)*M
  let B:=j3 D (e+g)+j3 D j
  obtain ⟨_,_,hM,hEM,hSurplus,_⟩:=hok
  have hs :B*(c+1)<N*c:= by
    simpa only [B,N,j3,j,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hSurplus
  obtain ⟨loss,hLower⟩:=qtVXGJd.proof C (fun A=>(qyOEyfe.proof C.E C.curve A).1)
  let r :=N*loss+B+1
  let a :=e*r
  let q:=p^a
  let v :=c*(q*H)+r
  have hq:e*r<q:=Nat.lt_pow_self (by decide :1<p)
  obtain ⟨U,hU,hUAway,hDimU⟩:=hLower v
  let:CharP C.E p:=charP_of_injective_ringHom (algebraMap L C.E).injective p
  let φ:=iterateFrobenius C.E p a
  let A' : Allowance C.E :=q•A
  let f' := pull a f
  let S' := fun t=>(sections C s t).map φ
  have hφ:zq4 φ:=φ.injective
  have hf'E :f'.natDegree=e :=
    (natDegree_map_eq_of_injective (zTo φ hφ) f).trans hfE
  have hf'W:weight D f' = weight D f := by
    change weight D (f.map (mapRingHom φ))=weight D f
    have hmap :zq4 (mapRingHom φ) :=zTo φ hφ
    unfold weight
    rw [support_map_of_injective f hmap]
    apply Finset.sup_congr rfl
    intro i _
    rw [coeff_map,coe_mapRingHom,natDegree_map_eq_of_injective hφ]
  obtain ⟨hf'P,hf'I⟩:=pull_irreducible a f hfP hfI (hfE.symm ▸ heP)
  have hS'd (t:T) : (S' t).natDegree≤D :=
    natDegree_map_le.trans (natDegree_map_le.trans (hd t t.property))
  have hS'i:integral C S' := by
    intro t i
    have hi:small (C.Ia t) 0 ((sections C s t).coeff i) := by
      rw [sections,coeff_map,RingHom.comp_apply]
      by_cases hc: (algebraMap K L) ((s t).coeff i)=0
      · simp [hc,small]
      · simp [small,(C.Ia t).on_constants _ hc]
    dsimp only [S']
    rw [coeff_map]
    simpa only [φ,iterateFrobenius_def,smul_zero] using small_pow _ hi q
  have hA'0:avoids C A' := by
    intro t
    simp [A',hAway t]
  have hf'A:bounded A' f' := by
    intro i k u
    have hi:=small_pow u (hfA i k u) q
    change small u (A' u) (((f.map (mapRingHom φ)).coeff i).coeff k)
    have hu: (A' u:ℤ)=q•(A u:ℤ) := by
      rw [show A' u=q*A u by simp only [A',Finsupp.smul_apply,Nat.nsmul_eq_mul],
        Nat.cast_mul,nsmul_eq_mul]
    rw [coeff_map,coe_mapRingHom,coeff_map,hu]
    exact hi
  have hRoots' : roots C S' q f' := by
    intro t i
    change small (C.Ia t) (-(q:ℤ))
      (((f.map (mapRingHom φ)).eval ((sections C s t).map φ)).coeff i)
    rw [← show mapRingHom φ (sections C s t)=(sections C s t).map φ from rfl,
      eval_map_apply,coe_mapRingHom,coeff_map]
    simpa only [φ,iterateFrobenius_def,Nat.cast_one,smul_neg,nsmul_one] using
      small_pow _ (hRoots t i) q
  have hA'm:mass A' ≤ q*H := by
    simpa only [A',map_nsmul,Nat.nsmul_eq_mul] using zBI q hA
  obtain ⟨hFin,hDim⟩:=qyOEyfe.proof C.E C.curve (U+A')
  have hD:zsE L (btN (U+A'))≤v+q*H+1 := by
    refine hDim.trans ?_
    rw [map_add]
    exact zlr (z9f hU hA'm) 1
  have hRank :B*zsE L (btN (U+A'))<N*zsE L (btN U) := by
    have hm:=(qL hs (q*H) loss :B*(v+q*H+1)+N*loss<N*v)
    exact Nat.lt_of_add_lt_add_right ((zlr (zBI B hD) _).trans_lt
      (hm.trans_le (by rw [← Nat.mul_add]; exact zBI _ hDimU)))
  obtain ⟨b,V,hV,hRow⟩:=qvwhqDa.proof C.E D e g M f' A' U hf'P.ne_zero hf'E.le hEM hf'A
    (qyOEyfe.proof C.E C.curve U).1 hFin
  have hWide :j3 D j*zsE L (btN (U+A'))<zsE L V:= by
    have h:=hRank.trans_le hV
    dsimp only [B] at h
    rw [Nat.add_mul] at h
    omega
  have hHigh:W<weight D f' := by rwa [hf'W,hfW]
  have hMV:M=W+1+j*D:=hM
  have hProper : ∃ G∈V,¬ f' ∣ G:= by
    by_contra! hAll
    exact hWide.not_ge (q5yqMPc.proof C.E D e g W j f' (U+A') V hf'P.ne_zero hf'E hHigh hFin
      (fun G hG=>⟨(hRow G hG).1,hMV ▸ (hRow G hG).2.1,(hRow G hG).2.2.1⟩) hAll)
  obtain ⟨G,hGV,hG⟩:=hProper
  obtain ⟨hGe,hGw,hGa,P,R,hPu,hRu,hEq⟩:=hRow G hGV
  have hRes :=irred_resultant hf'P hf'I hG
  let i:=(f'.resultant G).natDegree
  have hi: (f'.resultant G).coeff i≠0:=leadingCoeff_ne_zero.mpr hRes
  let Aout:=f'.natDegree•(U+A')+G.natDegree•A'
  have hf'pos :0<f'.natDegree :=hf'E.symm ▸ (by omega :0<e)
  have hPoles :=resultant_bounded hf'A hGa i
  have hZeros :=markedResultant C S' D q M b f' G P R A' U hf'pos hS'i hS'd
    hA'0 hUAway hf'A hGa hPu hRu hRoots' hGw hEq i
  refine ⟨⟨C.E,C.curve,a,_,hi,C.Ia,Aout,pole_le hPoles,?_⟩,?_⟩
  · intro t
    have hzq:=zero_ge (C.Ia t) hi (hZeros t)
    have hp:=pole_le hPoles (C.Ia t)
    exact (z9f hzq hp).trans_eq (Nat.add_comm _ _)
  · change mass Aout<q*(highFee e g c*H+1)
    have hmass :mass Aout≤e*(v+q*H)+(e+g)*(q*H) := by
      simp only [Aout,map_add,map_nsmul,Nat.nsmul_eq_mul,hf'E]
      exact z9f (zBI _ (z9f hU hA'm))
        (Nat.mul_le_mul hGe hA'm)
    have heq :e*(v+q*H)+(e+g)*(q*H)=q*(highFee e g c*H)+e*r := by
      dsimp only [v,highFee]
      ring
    rw [heq] at hmass
    exact hmass.trans_lt (by rw [Nat.mul_add,Nat.mul_one]; exact Nat.add_lt_add_left hq _)
theorem proof :qxtWb5a.c1 := by
  intro Q _ J T z s D e H g c W M F _ he3 heP _
  exact amplified Q J T z s D e H g c W M F he3 heP
theorem proof3681 :qwRB2oc.c1 :=proof
end
end qeHk2sb
end
section
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qtW1Uwb
noncomputable section
open Polynomial Finset
open P5 (K p)
open cu (L j9)
open gT (kM)
open DQ (specialize)
open Cu
open E7 (CurveField CurvePlace poleOrder)
open qK3TPae (regular)
open qb0hmCe (CurveModel cLN)
open q1kuFjb (AtSite mapTwice expansion_coeff power_residue)
open quN7Z4a (Sheet physicalWeight)
open qBajpRb (CurveRing incl cls yq equation equation_generic equation_mark)
open qRoCwuc (coord coeff_generic dSG)
open qkgz7gb (rV)
open P5_7_3_5_2 (atPolynomial)
open P5_7_7 (phys)
open qZfVj1b (pivot ChartPlace)
open scoped Classical WithZero
open private dc8 from ProximityPrize.SubmissionLower.Z3EWiUc
attribute [local instance] qZfVj1b.gRK
variable {Q:sQ} [Fact (Irreducible Q)]
private def curve (h:CurveField L (oO Q))
    (hh : ∀ i,(∑ᶠ v :CurvePlace L (oO Q),
      poleOrder v.value (Wt Q i))≤Q.totalDegree) :CurveModel Q where
  E :=oO Q
  seed :=Wt Q
  curve :=h
  equation := by
    ext q
    rw [RingHom.mem_ker]
    change MvPolynomial.aeval (Wt Q) q=0↔q∈auG Q
    rw [dc8,map_eq_zero_iff _
      (IsFractionRing.injective (abz Q) (oO Q)),
      Ideal.Quotient.eq_zero_iff_mem]
  generates := by
    have hm (a :abz Q) :
        algebraMap (abz Q) (oO Q) a ∈
          IntermediateField.adjoin L (Set.range (Wt Q)) := by
      obtain ⟨q,rfl⟩:=Ideal.Quotient.mk_surjective a
      apply IntermediateField.algebra_adjoin_le_adjoin L (Set.range (Wt Q))
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨q,dc8 Q q⟩
    apply top_unique
    intro c _
    obtain ⟨a,b,_,rfl⟩:=IsFractionRing.div_surjective (abz Q) c
    exact div_mem (hm a) (hm b)
  co6:=hh
variable {J:Ideal kM} {e H :ℕ} {T:Finset K}
  {z :K→K} {s :K→K[X]} (S:Sheet Q J e H T z s)
private theorem root_ne :S.root.equation≠0:= by
  intro h
  exact S.root.irreducible.ne_zero (by rw [h,Polynomial.map_zero])
private theorem b5S:S.root.equation.leadingCoeff.leadingCoeff≠0 :=
  leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr (root_ne S))
private theorem head_coeff :
    (S.root.equation.coeff e).coeff (S.root.equation.coeff e).natDegree =
      S.root.equation.leadingCoeff.leadingCoeff := by
  rw [coeff_natDegree]
  exact congrArg (fun i=>(S.root.equation.coeff i).leadingCoeff) S.root.degree.symm
private theorem eLq:coord S (pivot S) =
    (S.bY.scale :oO Q)*S.root.equation.leadingCoeff.leadingCoeff := by
  have h:=congrArg (fun f : (oO Q)[X] =>
    f.coeff (S.root.equation.coeff e).natDegree) (coeff_generic S e)
  simpa only [coeff_map,coeff_C_mul,head_coeff S,pivot,qRoCwuc.coeff] using h
private theorem pivot_ne :coord S (pivot S)≠0:= by
  rw [eLq S]
  exact mul_ne_zero S.bY.scale.ne_zero (b5S S)
private theorem normal_degree : (qZfVj1b.normalize S.root.equation).natDegree=e :=
  (natDegree_C_mul (C_ne_zero.mpr (inv_ne_zero (b5S S)))).trans S.root.degree
private theorem normal_monic :
    (qZfVj1b.normalize S.root.equation).leadingCoeff.leadingCoeff=1 := by
  rw [qZfVj1b.normalize,leadingCoeff_mul,leadingCoeff_C,leadingCoeff_mul,
    leadingCoeff_C,inv_mul_cancel₀ (b5S S)]
private theorem normal_irreducible :Irreducible (qZfVj1b.normalize S.root.equation) := by
  have hi:=(S.root.primitive.irreducible_iff_irreducible_map_fraction_map
    (K:=y7 Q)).mpr S.root.irreducible
  exact (irreducible_isUnit_mul ((inv_ne_zero (b5S S)).isUnit.map (C.comp C))).mpr hi
private theorem normal_weight {D W:ℕ} (hw:physicalWeight D S.root.equation≤W) :
    ∀ i,(qZfVj1b.normalize S.root.equation).coeff i≠0 →
      ((qZfVj1b.normalize S.root.equation).coeff i).natDegree+i*D ≤W:= by
  intro i hi
  simp only [qZfVj1b.normalize,coeff_C_mul] at hi ⊢
  rw [natDegree_C_mul (inv_ne_zero (b5S S))]
  exact (Finset.le_sup (f := fun i=>(S.root.equation.coeff i).natDegree+i*D)
    (mem_support_iff.mpr (right_ne_zero_of_mul hi))).trans hw
private abbrev ringPivot:CurveRing S.bY :=
  ((equation S.bY).coeff e).coeff (S.root.equation.coeff e).natDegree
private theorem normal_generic :
    qZfVj1b.normalize S.root.equation =
      C (C (incl S.bY (ringPivot S))⁻¹)*mapTwice (incl S.bY) (equation S.bY) := by
  have h:=congrArg (fun f : (oO Q)[X][X] =>
    (f.coeff e).coeff (S.root.equation.coeff e).natDegree) (equation_generic S.bY)
  simp only [coeff_map,coe_mapRingHom,coeff_C_mul,head_coeff S] at h
  change qZfVj1b.normalize S.root.equation=C (C (incl S.bY (ringPivot S))⁻¹) *
    (equation S.bY).map (mapRingHom (incl S.bY))
  rw [equation_generic S.bY,show incl S.bY (ringPivot S)= _ from h,
    qZfVj1b.normalize,← mul_assoc,← map_mul,← map_mul]
  congr 2
  rw [mul_inv_rev,mul_assoc,inv_mul_cancel₀ S.bY.scale.ne_zero,mul_one]
private theorem mark_pivot {γ:K} (hγ:γ∈T) :
    yq S.bY (z γ) (S.parameter γ) (S.onBase γ hγ) (ringPivot S) =
      zY9 (S.parameter γ) (pivot S) := by
  have h:=congrArg (fun f :L[X][X] =>
    (f.coeff e).coeff (S.root.equation.coeff e).natDegree) (equation_mark S.bY (S.onBase γ hγ))
  change (yq S.bY (z γ) (S.parameter γ) (S.onBase γ hγ)).toRingHom (ringPivot S)= _
  simpa only [specialize,coeff_map,coe_mapRingHom,pivot,ringPivot] using h
private theorem at_normal {γ:K} {hγ:γ∈T}
    (A:ChartPlace S.bY (S.onBase γ hγ))
    (hp:zY9 (S.parameter γ) (pivot S)≠0) :
    (∀ i j,A.place.value (((qZfVj1b.normalize S.root.equation).coeff i).coeff j)≤1) ∧
    atPolynomial (cLN A.map 0 (qZfVj1b.normalize S.root.equation)) (s γ)=0:= by
  let c:=A.series (ringPivot S)
  have hc:zbO c≠0:= by
    change zbO (A.series (ringPivot S))≠0
    rwa [A.reduce,mark_pivot S hγ]
  let u:=(PowerSeries.isUnit_iff_constantCoeff.mpr hc.isUnit).unit
  have hu: (u:zpm L)=c:=(PowerSeries.isUnit_iff_constantCoeff.mpr hc.isUnit).unit_spec
  let g:=C (C (↑u⁻¹:zpm L))*mapTwice A.series.toRingHom (equation S.bY)
  let ι:zpm L →+* LaurentSeries L:=HahnSeries.ofPowerSeries ℤ L
  have hg (i j:ℕ) :
      ι ((g.coeff i).coeff j)=A.map (((qZfVj1b.normalize S.root.equation).coeff i).coeff j) := by
    have hu' : ι (↑u⁻¹:zpm L)=(A.map (incl S.bY (ringPivot S)))⁻¹:= by
      rw [← A.lift_eq,← show ι c=(c:LaurentSeries L) from rfl,← hu]
      exact Units.val_inv_eq_inv_val (u.map ι.toMonoidHom)
    rw [normal_generic S]
    simp only [g,mapTwice,coe_mapRingHom,coeff_C_mul,coeff_map,map_mul,map_inv₀]
    rw [hu']
    congr 1
    exact A.lift_eq _
  constructor
  · intro i j
    rw [A.value,← hg]
    exact (LaurentSeries.val_le_one_iff_eq_coe L _).mpr ⟨_,rfl⟩
  · have he :cLN A.map 0 (qZfVj1b.normalize S.root.equation) =
        mapTwice zbO g:= by
      ext i j
      rw [expansion_coeff,← hg]
      simp only [mapTwice,coe_mapRingHom,coeff_map]
      exact power_residue _ _ rfl
    have hm:mapTwice zbO
        (mapTwice A.series.toRingHom (equation S.bY)) =
          specialize S.bY.equation (S.parameter γ) := by
      rw [← equation_mark S.bY (S.onBase γ hγ)]
      ext i j
      simp only [mapTwice,coe_mapRingHom,coeff_map]
      change zbO (A.series (((equation S.bY).coeff i).coeff j)) =
        yq S.bY (z γ) (S.parameter γ) (S.onBase γ hγ) (((equation S.bY).coeff i).coeff j)
      exact A.reduce _
    rw [he,show mapTwice zbO g =
      C (C (zbO (↑u⁻¹:zpm L))) *
        specialize S.bY.equation (S.parameter γ) by
      simp only [g,map_mul,mapTwice,coe_mapRingHom,map_C] at *
      rw [hm]]
    unfold atPolynomial
    have hv : (specialize S.bY.equation (S.parameter γ)).eval₂ phys (phys (j9 (s γ)))=0:= by
      calc
        _=phys ((specialize S.bY.equation (S.parameter γ)).eval (j9 (s γ))) := by
          rw [← eval₂_id,hom_eval₂,RingHom.comp_id]
        _=0:= by rw [S.identity γ hγ,map_zero]
    rw [eval₂_mul,hv,mul_zero]
theorem proof :qxtWb5a.c2 := by
  intro Q _ J T z s D e H W S hz he hpe hw
  have hp:Q.totalDegree<p:=(Nat.le_mul_of_pos_right _ he).trans_lt hpe
  obtain ⟨v,hc,hh⟩:=P5_7_1_5Q.c4321 Q hp
  let Cq:=curve hc hh
  let U:=regular Q z T
  have hU:U⊆T:=filter_subset _ _
  let G:=U.filter fun γ=>zY9 (S.parameter γ) (pivot S)≠0
  have hG:G⊆U:=filter_subset _ _
  have hcut: (U \ G).card≤H := by
    have hb:=dSG S hz (pivot S) (pivot_ne S) (U \ G)
      (fun _ hg=>hU (mem_sdiff.mp hg).1) (fun γ hg=> by
        by_contra hn
        exact (mem_sdiff.mp hg).2 (mem_filter.mpr ⟨(mem_sdiff.mp hg).1,hn⟩))
    simpa only [one_mul] using hb.trans (Nat.mul_le_mul_right H (S.bY.degree.2 _ _))
  let lift (γ:K) (hγ:γ∈G) :=
    Classical.choice (quwKLBd.proof S.bY hp hc (z γ) (S.parameter γ) (S.onBase γ (hU (hG hγ))))
  let A (γ:K) (hγ:γ∈G) :AtSite Cq (rV z γ) := by
    let B:=lift γ hγ
    refine ⟨B.map,B.place,B.value,?_⟩
    let b (i:Fin 2) :=B.series (cls S.bY (MvPolynomial.X (Sum.inl i)))
    have hb (i:Fin 2) :B.map (Cq.seed i)=(b i:LaurentSeries L) := by
      rw [B.lift_eq,qBajpRb.incl_cls]
      simp [qBajpRb.ek,Cq,curve]
    have hres (i:Fin 2) :zbO (b i)=rV z γ i:= by
      rw [B.reduce,qBajpRb.atMark_cls,MvPolynomial.eval_X]
      rfl
    exact ⟨b,hb,hres,qyEseja.proof _ hp (S.onSeed γ (hU (hG hγ))) (mem_filter.mp (hG hγ)).2
      B.place B.map B.value b hb hres⟩
  let place (γ:K) :CurvePlace L Cq.E :=if hγ:γ∈G then (A γ hγ).place else v
  have hplace (γ:K) (hγ:γ∈G) :place γ=(A γ hγ).place :=dite_eq_left hγ
  have hd:=normal_degree S
  let F:P5_7_3_5_2.Sheet Cq z s := {
    f :=qZfVj1b.normalize S.root.equation
    irreducible :=normal_irreducible S
    positive :=hd.symm ▸ he
    normalized:=normal_monic S
    marks :=G
    atPlace := fun γ hγ=>(A γ hγ).map
    place :=place
    distinct := by
      intro γ hγ δ hδ hh
      rw [hplace γ hγ,hplace δ hδ] at hh
      exact hz (hU (hG hγ)) (hU (hG hδ))
        ((algebraMap K L).injective (congrFun ((A γ hγ).site_eq_of_place (A δ hδ) hh) 0))
    value := fun γ hγ c=>(congrArg (fun w:CurvePlace L Cq.E=>w.value c) (hplace γ hγ)).trans
      ((A γ hγ).value c)
    arc := fun γ hγ=>(A γ hγ).arc
    integral:= fun γ hγ i j=> by
      exact (congrArg (fun w:CurvePlace L Cq.E =>
        w.value (((qZfVj1b.normalize S.root.equation).coeff i).coeff j)) (hplace γ hγ)).trans_le
          ((at_normal S (hγ:=hU (hG hγ)) (lift γ hγ) (mem_filter.mp hγ).2).1 i j)
    root := fun γ hγ=>(at_normal S (hγ:=hU (hG hγ)) (lift γ hγ) (mem_filter.mp hγ).2).2 }
  exact ⟨Cq,F,hd,P5_7_1_5Q.c4322 S.bY hc S.height,normal_weight S hw,hG,hcut⟩
end
end qtW1Uwb
end
section
set_option autoImplicit true
namespace qDgwMqb
theorem proof :qwRB2oc.c2 :=qtW1Uwb.proof
end qDgwMqb
end
