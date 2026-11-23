import ProximityPrize.SubmissionLower.ZcG5Ygd
import ProximityPrize.SubmissionLower.ZxJP4ta
import ProximityPrize.SubmissionLower.ZAW6pTc
import ProximityPrize.SubmissionLower.Z9HmSkb
import ProximityPrize.SubmissionLower.ZFx6vEd
import ProximityPrize.SubmissionLower.Z29Fskc
import ProximityPrize.SubmissionLower.ZoBS5Pe
import ProximityPrize.SubmissionLower.ZTipoSd
import ProximityPrize.SubmissionLower.ZU4mhUb
import ProximityPrize.SubmissionLower.Z3y0Gja
import ProximityPrize.SubmissionLower.Z34f0bb
import ProximityPrize.SubmissionLower.ZletMPd
import ProximityPrize.SubmissionLower.Z8WzNdb
import ProximityPrize.SubmissionLower.ZYAtnhb
import ProximityPrize.SubmissionLower.ZpRUmmd
import ProximityPrize.SubmissionLower.ZyNqUje
import ProximityPrize.SubmissionLower.ZT9tXQa
import ProximityPrize.SubmissionLower.Z9vlvqb
set_option Elab.async false
section
set_option autoImplicit true
namespace qOrl4se
noncomputable section
open qK9H6va q1jcGec MvPolynomial
open P1_6_1_3 (Target adjacentProduct)
open ank (J5 ao9)
open P1_6_1_3_2 (bind_adjacent_monomial)
open aiW (aOx)
open fP (cF m9 oG Qg)
open private prefixSum prefix_support bind_prefix adjacent_coeff_zero from ProximityPrize.SubmissionLower.ZcG5Ygd
open scoped BigOperators
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
local notation "F" => ZMod P1.p
local notation "Poly" => MvPolynomial (Fin 4) F
def keep {q:ℕ} (e :Target q) :Prop :=
  e.val 0≤16∧e.val.weight m9<56
instance (q:ℕ) :DecidablePred (keep (q:=q)) := fun e =>
  inferInstanceAs (Decidable (e.val 0≤16∧e.val.weight m9<56))
abbrev AdjacentRow (q:ℕ) := {e :Target q // keep e}
def adjacentMatrix (q r :ℕ) :Matrix (AdjacentRow q) (XN q (offset r)) F :=
  fun e m=>(adjacentProduct e.val.val).coeff m.val
theorem rank_le_adjacent {q r :ℕ} (hd:iO q=q)
    (hc: (Vm q (offset r)).toNat=56) :
    (Gy q (offset r)).rank≤(adjacentMatrix q r).rank := by
  classical
  rw [Matrix.rank_eq_finrank_span_row,Matrix.rank_eq_finrank_span_row]
  refine Submodule.finrank_mono (Submodule.span_le.mpr ?_)
  rintro _ ⟨e,rfl⟩
  have hdeg:=e.property.1.trans hd
  have hcut:=e.property.2.trans_eq hc
  let project :Poly →ₗ[F] (XN q (offset r)→F) :=
    LinearMap.pi fun m=>lcoeff F m.val
  have hrow: (Gy q (offset r)).row e=project (J5 e.val) := by
    funext m
    exact (ao9 e.val m.val (e.property.1.trans m.property.1.symm)).symm
  rw [hrow,← bind_prefix]
  let P:Poly :=bind₁ prefixSum (monomial e.val 1)
  change project (bind₁ _ P)∈_
  rw [P.as_sum,map_sum,map_sum]
  refine Submodule.sum_mem _ fun d hd' => ?_
  obtain ⟨hdegree,hweight⟩:=prefix_support e.val d hd'
  rw [bind_adjacent_monomial,map_smul]
  change _•project (adjacentProduct d)∈_
  by_cases ht:d 0≤16
  · exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨⟨⟨d,hdegree.trans hdeg⟩,ht,hweight.trans_lt hcut⟩,rfl⟩)
  · have hz :project (adjacentProduct d)=0:= by
      funext m
      exact adjacent_coeff_zero d m.val (m.property.2.2.2.trans_lt (Nat.lt_of_not_ge ht))
    rw [hz,smul_zero]
    exact Submodule.zero_mem _
private abbrev ax0 (q:ℕ) :=
  Σ t:Fin (q+1),Σ c:Fin (q - t.val+1),Fin (min 17 (aOx t c 56))
private def slot {q:ℕ} (e :AdjacentRow q) :ax0 q:= by
  have hd:=e.val.property
  have ho:=e.property.2
  have ha :=e.property.1
  rw [cF] at hd
  rw [oG] at ho
  refine ⟨⟨e.val.val 0+e.val.val 3,by omega⟩,
    ⟨e.val.val 2,show e.val.val 2<q-(e.val.val 0+e.val.val 3)+1 by omega⟩,
    ⟨e.val.val 0,?_⟩⟩
  change e.val.val 0< min 17 (aOx (e.val.val 0+e.val.val 3) (e.val.val 2) 56)
  unfold aOx
  omega
theorem adjacent_card_le (q:ℕ) :Fintype.card (AdjacentRow q)≤bve q 56:= by
  classical
  have hinj:Function.Injective (slot (q:=q)) := by
    intro e f h
    have ht:=congrArg (fun s :ax0 q=>s.1.val) h
    have hc:=congrArg (fun s :ax0 q=>s.2.1.val) h
    have ha :=congrArg (fun s :ax0 q=>s.2.2.val) h
    change e.val.val 0+e.val.val 3=f.val.val 0+f.val.val 3 at ht
    change e.val.val 2=f.val.val 2 at hc
    change e.val.val 0=f.val.val 0 at ha
    have he :=e.val.property
    have hf :=f.val.property
    rw [cF] at he hf
    apply Subtype.ext
    apply Subtype.ext
    ext j
    fin_cases j
    · exact ha
    · change e.val.val 1=f.val.val 1
      omega
    · exact hc
    · change e.val.val 3=f.val.val 3
      omega
  exact (Fintype.card_le_of_injective _ hinj).trans_eq (by
    simp only [ax0,bve,Qg,Fintype.card_sigma,Fintype.card_fin])
end
end qOrl4se
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qQ76XXb
noncomputable section
open Polynomial aR dN lB
open P6 (K)
open czT (bOc bOG)
open wH (qg)
open Ex (YN aQU)
open private ur bFv bO1 bxU from ProximityPrize.SubmissionLower.AF
open private bD7 cKw from ProximityPrize.SubmissionLower.E5
private theorem fVC (f :af 4) (S:ao[X])
    (ht: (shape f).t<K1.p) (hon :Dd f S) (hs :cK (separant f) S=0) :
    ∃ j,0<j∧j<(shape f).t ∧
      cK ((separant^[j]) f) S=0∧cK (separant ((separant^[j]) f)) S≠0:= by
  classical
  let t:=(shape f).t
  let P:=ur S f
  have hdeg:P.natDegree≤t:=Polynomial.natDegree_map_le.trans_eq (aQU f)
  have hnz : (derivative^[t] P).coeff 0≠0:= by
    rw [coeff_iterate_derivative,Nat.zero_add,Nat.descFactorial_self,nsmul_eq_mul]
    change (t.factorial:ao[X])*P.coeff t≠0
    rw [← map_natCast (Polynomial.C:ao →+* ao[X])]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr
      (ahA ht))
      (by simpa only [P,t,bO1] using hon.2)
  have hc:derivative^[t] P=Polynomial.C ((derivative^[t] P).coeff 0) :=
    eq_C_of_natDegree_le_zero ((natDegree_iterate_derivative _ _).trans
      (by omega :P.natDegree - t≤0))
  have he (k :ℕ) :cK ((separant^[k]) f) S =
      (derivative^[k] P).eval (jet S (3:Fin 4)) := by
    rw [← bFv]
    congr 1
    induction k with
    | zero=>rfl
    | succ k ih =>
      simp only [Function.iterate_succ_apply']
      change (YN (separant ((separant^[k]) f))).map (MvPolynomial.eval (jet S))= _
      rw [bxU,← derivative_map]
      exact congrArg derivative ih
  have hlast :cK ((separant^[t]) f) S≠0:= by
    rw [he,hc,Polynomial.eval_C]
    exact hnz
  have hex : ∃ k,cK ((separant^[k]) f) S≠0:=⟨t,hlast⟩
  let k :=Nat.find hex
  have hk :cK ((separant^[k]) f) S≠0:=Nat.find_spec hex
  have hkt:k≤t:=Nat.find_min' hex hlast
  have hk0:k≠0:= by
    intro h
    apply hk
    simpa only [h,Function.iterate_zero_apply] using hon.1
  have hk1 :k≠1 := by
    intro h
    apply hk
    simpa only [h,Function.iterate_one] using hs
  have hprev :k - 1+1=k := by omega
  refine ⟨k - 1,by omega,by omega,?_,?_⟩
  · exact not_ne_iff.mp (Nat.find_min hex (by omega :k - 1<k))
  · have he' : (separant^[k]) f=separant ((separant^[k - 1]) f) := by
      conv_lhs=>rw [← hprev]
      rw [Function.iterate_succ_apply']
    simpa only [he'] using hk
private theorem dIF (p:Shape) (hp:bF p) (ht:1<p.t) (hb:p.b≤133) :
    aO (bY (aR.bf+4) (bD7 p))
      (bY (P6_6.bf+4) p) := by
  obtain ⟨hjb,htj⟩:=hp
  have hB:1+267352*(p.b - 1 - 1)≤1+266860*(p.b - 1) := by omega
  have hJ:267352*(p.j-3-3)+133676+3 ≤
      266860*(p.j-3)+133430+3:= by omega
  have hT:267352*(p.t - 1 - 1)+133676+1 ≤
      266860*(p.t - 1)+133430+1 := by omega
  exact ⟨max_le_max hB hJ,hJ,min_le_min hT (Nat.div_le_div_right hJ)⟩
private theorem d39 (f :af 4) (hf :P6_6.wm f)
    (ht:1<(shape f).t) {j:ℕ} (hj:0<j) :
    let g:=(separant^[j]) f
    ∃ C:TaylorChart,C.dM (bY (P6_6.bf+4) (shape f).iU) ∧
      ∀ S:ao[X],cK g S=0→qg g S→C.aay S:= by
  dsimp only
  let p:=(shape f).iU
  let q:=bD7 p
  have hp:bF p:=Tn f
  have htp:1<p.t:=ht
  have hpb:p.b≤133:=max_le hf.2.2.1.1 (hf.2.2.1.2.1.trans (by decide :56≤133))
  have hq:bF q:= by
    obtain ⟨hjb,htj⟩:=hp
    change p.j-3≤p.b - 1∧3*(p.t - 1)≤p.j-3
    omega
  have htq:0<q.t:= by
    change 0<p.t - 1
    omega
  obtain ⟨C,hC,hrecover⟩:=d34 ((separant^[j]) f) q (cKw f hj) hq htq
  have hbox :=dIF p hp htp hpb
  have aby {P:GeoJets} (hP:yy P (bY (aR.bf+4) q)) :
      yy P (bY (P6_6.bf+4) p) :=
    ⟨hP.1.trans hbox.1,hP.2.1.trans hbox.2.1,hP.2.2.trans hbox.2.2⟩
  exact ⟨C,⟨aby hC.1,fun i=>aby (hC.2 i)⟩,hrecover⟩
private theorem aCu (f :af 4) :aO (shape f) (shape f).iU :=
  ⟨le_max_left _ _,le_rfl,le_rfl⟩
private theorem bEa {f :af 4} (hf :P6_6.wm f) (j:ℕ)
    (hj:0<j) (hg: (separant^[j]) f≠0) : ¬ f∣(separant^[j]) f := by
  rintro ⟨q,hq⟩
  have hq0:q≠0:= by
    intro hz
    exact hg (by rw [hq,hz,mul_zero])
  have hd:=MvPolynomial.degreeOf_mul_eq (n:=(3:Fin 4)) hf.1.ne_zero hq0
  have h:=bD9 f j
  have ht:0<f.degreeOf 3:=hf.2.1
  change ((separant^[j]) f).degreeOf 3≤f.degreeOf 3 - j at h
  rw [hq,hd] at h
  omega
private theorem eGE {w Γ s} (hm:P6_6.Messages w Γ s) (f :af 4) (hf :P6_6.wm f) (j:ℕ)
    (hj:0<j) (ht:1<(shape f).t)
    (hmarks : ∀ γ∈Γ,cK f (extend (s γ))=0 ∧
      cK ((separant^[j]) f) (extend (s γ))=0 ∧
      qg ((separant^[j]) f) (extend (s γ))) :
    let p:=(shape f).iU
    let h:=bY (P6_6.bf+4) p
    Γ.card≤4*(iH p p h h/32) := by
  classical
  dsimp only
  by_cases hΓ:Γ.Nonempty
  · obtain ⟨γ,hγ⟩:=hΓ
    let g:=(separant^[j]) f
    let p:=(shape f).iU
    let h:=bY (P6_6.bf+4) p
    let d:=iH p p h h/32
    have hg0:g≠0:= by
      intro hz
      exact (hmarks γ hγ).2.2 (by simp [show (separant^[j]) f=0 from hz,cK])
    have hpf :=aCu f
    have hpg:aO (shape g) p:= by
      have hb:=a3t f j
      exact ⟨hb.1.trans hpf.1,hb.2.1.trans hpf.2.1,hb.2.2.trans hpf.2.2⟩
    have hp:=Tn f
    obtain ⟨C,hC,hrecover⟩:=d39 f hf ht hj
    have hdegree :P6_6.gZ≤133671 := by decide
    have hbound:cAp (bC f) (bC g) C d:= by
      intro a b points hpts
      exact (Nat.le_div_iff_mul_le (by decide :0<32)).mpr (by
        rw [Nat.mul_comm]
        exact bOc p h hp (A9 _ _) _ _ _ _
          (abr hpf) (abr hpg) (C.aWC hC a)
          (C.aWC hC b) points (fun y hy=>(hpts y hy).1))
    obtain ⟨B,hcover,hsurfaces,hpos,hsum⟩ :=
      bOG (bC f) (bC g)
        (fun hz=>hf.1.ne_zero (aFf (hz.trans (map_zero _).symm)))
        (fun hz=>hg0 (aFf (hz.trans (map_zero _).symm)))
        (amo f g hf.1 (bEa hf j hj hg0))
        C d hbound Γ s hm.distinct (fun a ha=> by
          obtain ⟨hf',hg',hr⟩:=hmarks a ha
          refine ⟨(hm.degree a ha).trans hdegree,?_,?_,hrecover _ hg' hr⟩
          · rw [afz,hf',map_zero]
          · rw [afz,hg',map_zero])
    exact (Finset.card_le_card hcover).trans
      ((bgc B hm hsurfaces hpos).trans (Nat.mul_le_mul_left 4 hsum))
  · simp [Finset.not_nonempty_iff_eq_empty.mp hΓ]
theorem proof :P6_6_6.c1 := by
  classical
  intro w Γ s hm f hf _helig hmarks
  let t:=(shape f).t
  have hcover (γ:K) (hγ:γ∈Γ) :
      ∃ j,0<j∧j<t ∧
        cK ((separant^[j]) f) (extend (s γ))=0 ∧
        qg ((separant^[j]) f) (extend (s γ)) :=
    fVC f _ (hf.2.2.1.2.2.trans_lt (by decide :16<K1.p))
      (hmarks γ hγ).1 (Classical.not_not.mp (hmarks γ hγ).2)
  by_cases ht:1<t
  · let p:=(shape f).iU
    let h:=bY (P6_6.bf+4) p
    let m:=iH p p h h
    let part (j:Fin t) :=Γ.filter fun γ =>
      0<j.val∧cK ((separant^[j.val]) f) (extend (s γ))=0 ∧
        qg ((separant^[j.val]) f) (extend (s γ))
    have hall:Γ⊆Finset.univ.biUnion part:= by
      intro γ hγ
      obtain ⟨j,hj,hjt,hz,hr⟩:=hcover γ hγ
      exact Finset.mem_biUnion.mpr ⟨⟨j,hjt⟩,Finset.mem_univ _,Finset.mem_filter.mpr
        ⟨hγ,hj,hz,hr⟩⟩
    have hpart (j:Fin t) : (part j).card≤4*(m/32) := by
      by_cases hj:0<j.val
      · have hsub:part j⊆Γ:=Finset.filter_subset _ _
        apply eGE (hm.mono hsub) f hf j.val hj ht
        intro γ hγ
        have hp:=Finset.mem_filter.mp hγ
        exact ⟨(hmarks γ hp.1).1.1,hp.2.2⟩
      · simp [part,hj]
    have hprice :4*t*(m/32)≤ ceilDiv (4*t*m) 32 := by
      unfold ceilDiv
      apply (Nat.le_div_iff_mul_le (by decide :0<32)).mpr
      rw [Nat.mul_assoc]
      exact (Nat.mul_le_mul_left (4*t) (Nat.div_mul_le_self m 32)).trans (by omega)
    have hchart:P6_6_6.rH (shape f)=h:= by
      unfold P6_6_6.rH
      exact ite_eq_right (by omega :t≠1)
    unfold P6_6_6.bwr
    rw [ite_eq_left ht,hchart]
    change Γ.card≤ ceilDiv (4*t*m) 32+t*(shape f).b^2+1
    calc
      Γ.card≤(Finset.univ.biUnion part).card:=Finset.card_le_card hall
      _ ≤ ∑ j:Fin t,(part j).card:=Finset.card_biUnion_le
      _ ≤ ∑ _:Fin t,4*(m/32) :=Finset.sum_le_sum fun j _=>hpart j
      _=4*t*(m/32) := by simp [Nat.mul_comm,Nat.mul_assoc] <;> exact Nat.mul_left_comm _ _ _
      _≤ ceilDiv (4*t*m) 32 :=hprice
      _≤_:= by omega
  · have hempty :Γ = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨γ,hγ⟩
      obtain ⟨j,hj,hjt,_,_⟩:=hcover γ hγ
      omega
    simp [hempty]
end
end qQ76XXb
end
section
set_option autoImplicit true
namespace q8kPhwd
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
local notation "asr" h "," mm "," qq "," nn "," aa "," dd "," bb "," cc =>
  checked (lo:=2900) (m:=mm) (mid :=qq) (n:=nn) (a :=aa) (b:=bb) (c:=cc)
    h rfl (numeric qq nn dd bb rfl rfl) rfl
private theorem r0:bvj 2900 8=(0x7b14c013e40:ℕ) :=numeric 2900 8 0x27c970d8bf 0x7b14c013e40 rfl rfl
private theorem r1 :bvj 2900 16=(0xf47353261b0:ℕ) :=asr r0,8,2908,8,0x7b14c013e40,0x278bb88008,0x795e9312370,0xf47353261b0
private theorem r2 :bvj 2900 24=(0x16c1f478e100:ℕ) :=asr r1,16,2916,8,0xf47353261b0,0x274c211e75,0x77abf467f50,0x16c1f478e100
theorem total0:bvj 2900 32=(0x1e21bbf46f28:ℕ) :=asr r2,24, 2924,8,0x16c1f478e100,0x270a6fdfde,0x75fc77b8e28,0x1e21bbf46f28
end q8kPhwd
end
section
set_option autoImplicit true
namespace q8kPhwd
theorem proof :qwbsesc.c5:= by
  apply of_total (by decide) (by decide)
  have h1 :=checked (lo:=2900) (m:=32) (mid :=2932) (n:=32)
    (a :=0x1e21bbf46f28) (b:=0x1c75b79f84e0) (c:=0x3a977393f408) total0 rfl total1 rfl
  have h2 :=checked (lo:=2900) (m:=64) (mid :=2964) (n:=32)
    (a :=0x3a977393f408) (b:=0x1ad6be780590) (c:=0x556e320bf998) h1 rfl total2 rfl
  have h3:=checked (lo:=2900) (m:=96) (mid :=2996) (n:=32)
    (a :=0x556e320bf998) (b:=0x1944b8370e98) (c:=0x6eb2ea430830) h2 rfl total3 rfl
  have h4 :=checked (lo:=2900) (m:=128) (mid :=3028) (n:=32)
    (a :=0x6eb2ea430830) (b:=0x17c0199d57b0) (c:=0x867303e05fe0) h3 rfl total4 rfl
  have h5:=checked (lo:=2900) (m:=160) (mid :=3060) (n:=32)
    (a :=0x867303e05fe0) (b:=0x16486b276420) (c:=0x9cbb6f07c400) h4 rfl total5 rfl
  have h6:=checked (lo:=2900) (m:=192) (mid :=3092) (n:=32)
    (a :=0x9cbb6f07c400) (b:=0x14ded3095430) (c:=0xb19a42111830) h5 rfl total6 rfl
  have h7:=checked (lo:=2900) (m:=224) (mid :=3124) (n:=32)
    (a :=0xb19a42111830) (b:=0x13832585d3f0) (c:=0xc51d6796ec20) h6 rfl total7 rfl
  have h8:=checked (lo:=2900) (m:=256) (mid :=3156) (n:=32)
    (a :=0xc51d6796ec20) (b:=0x12350840de10) (c:=0xd7526fd7ca30) h7 rfl total8 rfl
  have h9:=checked (lo:=2900) (m:=288) (mid :=3188) (n:=32)
    (a :=0xd7526fd7ca30) (b:=0x10f478c21e20) (c:=0xe846e899e850) h8 rfl total9 rfl
  have Kr :=checked (lo:=2900) (m:=320) (mid :=3220) (n:=32)
    (a :=0xe846e899e850) (b:=0xfbbefad4c00) (c:=0xf802d8473450) h9 rfl total10 rfl
  have h11 :=checked (lo:=2900) (m:=352) (mid :=3252) (n:=32)
    (a :=0xf802d8473450) (b:=0xe9444beeda8) (c:=0x106971d0621f8) Kr rfl total11 rfl
  have h12 :=checked (lo:=2900) (m:=384) (mid :=3284) (n:=23)
    (a :=0x106971d0621f8) (b:=0x9cb928e5908) (c:=0x11062af947b00) h11 rfl total12 rfl
  rw [show 3307-2900=407 by decide,h12]
  exact_mod_cast (show 0x11062af947b00≤24*(0xb597dac2fd5:ℕ) by decide)
end q8kPhwd
end
