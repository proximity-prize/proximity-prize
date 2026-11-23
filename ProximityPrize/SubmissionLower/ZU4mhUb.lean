import ProximityPrize.SubmissionLower.Z29Fskc
import ProximityPrize.SubmissionLower.ZJHC8Rc
import ProximityPrize.SubmissionLower.ZucFfdd
import ProximityPrize.SubmissionLower.ZCqrzHc
import ProximityPrize.SubmissionLower.ZY07HEa
import ProximityPrize.SubmissionLower.ZedfuCc
import ProximityPrize.SubmissionLower.Z2dBXLe
import ProximityPrize.SubmissionLower.ZnczBaa
import ProximityPrize.SubmissionLower.ZpWezjb
import ProximityPrize.SubmissionLower.ZBG70hc
import ProximityPrize.SubmissionLower.ZHCqaAd
set_option Elab.async false
open _root_ renaming Finset.filter_subset → zT0, Finset.mem_univ → zTc, Finset.mul_sum → zxw, Finset.single_le_sum → zfK, Finset.sum_le_sum → zQk, Ideal.span → zye, MvPolynomial.cappedDegreeMixedVolume → zBz, Nat.add_le_add → z9f, Nat.add_sub_assoc → z0U, Nat.cast_nonneg → zqJ, Nat.eq_zero_of_le_zero → za7, Nat.le_add_right → z8K, Nat.mul_le_mul_right → ztf, Nat.zero_le → zD0, Polynomial.map_injective → zTo
section
set_option autoImplicit true
namespace q8kPhwd
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
local notation "asr" h "," mm "," qq "," nn "," aa "," dd "," bb "," cc =>
  checked (lo:=2996) (m:=mm) (mid :=qq) (n:=nn) (a :=aa) (b:=bb) (c:=cc)
    h rfl (numeric qq nn dd bb rfl rfl) rfl
private theorem r0:bvj 2996 8=(0x67656372468:ℕ) :=numeric 2996 8 0x246a079d56 0x67656372468 rfl rfl
private theorem r1 :bvj 2996 16=(0xcd3c59858f0:ℕ) :=asr r0,8,3004,8,0x67656372468,0x24174ab369,0x65d6f613488,0xcd3c59858f0
private theorem r2 :bvj 2996 24=(0x13187ed9f670:ℕ) :=asr r1,16,3012,8,0xcd3c59858f0,0x23c2f2e4b7,0x644b9419d80,0x13187ed9f670
theorem total3:bvj 2996 32=(0x1944b8370e98:ℕ) :=asr r2,24,3020,8,0x13187ed9f670,0x236d47779e,0x62c395d1828,0x1944b8370e98
end q8kPhwd
end
section
set_option autoImplicit true
namespace qowXRPc
theorem proof :q8kxiJa.c2 := by
  intro J boxes hlen hboxes hd S hS
  exact qZqYIua.retain_cycle J boxes hboxes hlen hd S hS
end qowXRPc
end
section
set_option autoImplicit true
namespace qa9c8Dc
theorem proof :qduj6fa.c2 := by
  intro R r q b hR hr hq hb
  rw [mul_comm]
  exact (le_div_iff₀ (by decide : (0:ℚ)<32)).mp
    (qZqYIua.literal_bound R r q b b hR hr hq hb hb)
end qa9c8Dc
end
section
set_option autoImplicit true
namespace qZqYIua
open P6_6 P6_6_7 q90NBie
open aR (af Shape shape aO)
open dN (GeoJets bC kC AX)

open Dr
open lB (bF amo)
open IsLocalRing
private theorem length_of_order {L:Type*} [CommRing L] [IsLocalRing L]
    [IsNoetherianRing L] {A:Ideal L} (hA:A.IsPrime) (hlt:A< maximalIdeal L)
    {x :L} {e :ℕ} (he :x∈maximalIdeal L^e) :
    (e :ℕ∞)≤Module.length L (L ⧸ (A ⊔ zye {x} : Ideal L)) := by
  let m:=maximalIdeal L
  let I (i:ℕ) :Ideal L:=A ⊔ m^i
  have hstep (i:ℕ) :I (i+1)<I i:= by
    refine lt_of_le_of_ne (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.le_succ i)) _) ?_
    intro h
    have hpow:m^i≤A:= by
      apply Submodule.le_of_le_smul_of_le_jacobson_bot (I:=m) (IsNoetherian.noetherian _)
      · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
      · change m^i≤A ⊔ m•m^i
        rw [smul_eq_mul,← pow_succ']
        change m^i≤I (i+1)
        rw [h]
        exact le_sup_right
    exact hlt.not_ge (fun z hz=>hA.mem_of_pow_mem i (hpow (Ideal.pow_mem_pow hz i)))
  have hdegree (i:ℕ) : (i:ℕ∞)≤Order.coheight (I i:Submodule L L) := by
    induction i with
    | zero=>simp
    | succ i ih =>
        rw [Nat.cast_succ]
        exact (add_le_add_left ih 1).trans
          (Order.coheight_add_one_le (show (I (i+1) :Submodule L L)<I i from hstep i))
  rw [Module.length_quotient]
  exact (hdegree e).trans (Order.coheight_anti
    (show A ⊔ zye {x} ≤ I e from sup_le le_sup_left
      (le_sup_right.trans' (Ideal.span_singleton_le_iff_mem _ |>.mpr he))))
theorem curve_weight {z D:Ideal GeoJets} {V:af 4}
    (hz :z.IsPrime) (hV:bC V∉z) (hD: (AX z V).IsMinimalPrime D) :
    genericOrder V D ≤AN (AX z V) D:= by
  let:=hD.isPrime
  let L:=Localization.AtPrime D
  let φ:=algebraMap GeoJets L
  let A:=z.map φ
  have hle :z≤D:=le_sup_left.trans hD.le
  have hdis :Disjoint (D.primeCompl:Set GeoJets) (z :Set GeoJets) := by
    rw [Set.disjoint_left]
    exact fun x hx hz' => hx (hle hz')
  have hA:A.IsPrime :=IsLocalization.isPrime_of_isPrime_disjoint D.primeCompl L z hz hdis
  have hmax :D.map φ=maximalIdeal L:=Localization.AtPrime.map_eq_maximalIdeal
  have hlt:A< maximalIdeal L:= by
    refine lt_of_le_of_ne ((Ideal.map_mono hle).trans hmax.le) (fun he=>hV ?_)
    have hh:A.comap φ=z :=
      IsLocalization.under_map_of_isPrime_disjoint D.primeCompl L hz hdis
    rw [← hh,he]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L D _).mpr
      (hD.le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  have hs :=length_of_order hA hlt (generic_vanishesTo V D)
  apply ENat.natCast_le_natCast.mp
  rw [a9B hD]
  change (genericOrder V D:ℕ∞)≤Module.length L (L ⧸ (AX z V).map φ)
  rw [AX,Ideal.map_sup,Ideal.map_span,Set.image_singleton]
  exact hs
theorem of_literal
    (literal : ∀ (R:af 4) (a q r h:Shape),R≠0 →
      aO (shape R) a→bF q→bF r→bF h →
      tW (zye {bC R}) [q,r,h] ≤
        (wP a q r h:ℚ)/32) :
    q90NBie.c1 := by
  classical
  intro C R G ell cs hp A F h hh
  let q:=cutterBody C ell
  let r :=commonBody C R ell cs
  let J:=kC R G
  let H :=zye {bC R}
  obtain ⟨hq,hr,Hh⟩:=body_chambers hp hh
  have hch:bF h:=⟨Hh.1,Hh.2.1⟩
  have hrel :=amo R G hp.factor.1 hp.proper
  have hR:=P6_6_7_3.agr hp.factor.1.ne_zero
  have hreg:=aPQ Ideal.isPrime_bot (show bC R∉(⊥ : Ideal GeoJets) by simpa using hR)
  have hH :dimension H≤3:= by simpa [H,bEk] using aCR hreg
  have hG:=aIT R G hrel
  have hr' : bF r :=hr
  have hJ:dimension J≤2 := by
    rw [show J=H ⊔ zye {bC G} from aIc R G]
    have hd:dimension (H ⊔ zye {bC G})≤dimension H - 1 :=aCR hG
    exact hd.trans (by omega)
  have hcut:=bau.proof
  have hsum (z :Ideal GeoJets) (hz :z∈uG A ell) :
      (∑ D∈qv F z,(curveOrder F z D:ℚ)*sectionCost h D) ≤
        6*tW z [r,h] := by
    have hs :=(surface_spec hz).1
    have hZ:=aQG hR hrel hs
    let V:=F.first z
    let I:=AX z V
    have hV:=F.proper z hz
    have hregV:=aPQ hs.isPrime hV
    have hI:dimension I≤1 :=(aCR hregV).trans (by omega)
    have hfits :aO (shape V) r :=P6_6_7_3.cDD (F.fits z hz) common_fits
    calc
      _ ≤ ∑ D∈qv F z,6*((AN I D:ℚ)*tW D [h]) := by
        apply zQk
        intro D hd
        have hm:=curve_spec hd
        have :=hs.isPrime
        have heq :=MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one hV hm
        change dimension D + 1=dimension z at heq
        have hdeg:dimension D =1 := by omega
        have hsect :=cyL.proof D h hm.isPrime hdeg hch Hh.2.2
        have hw:=curve_weight hs.isPrime hV hm
        calc
          _≤(AN I D:ℚ)*sectionCost h D :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hw) (zqJ _)
          _≤_:= by
            rw [mul_left_comm]
            exact mul_le_mul_of_nonneg_left hsect (zqJ _)
      _≤6*tW I [h] := by
        rw [← zxw]
        exact mul_le_mul_of_nonneg_left
          (retain_cycle I [h] (by simpa using hch) (by simp) (by simpa using hI) _ (fun _=>curve_spec))
          (by norm_num)
      _≤_:=mul_le_mul_of_nonneg_left
        (hcut z r [h] hr (by simpa using hch) (by simp) (by simp [hZ]) (bC V)
          (bHn hfits) hregV) (by norm_num)
  have hb: (mass F (fun _ D =>sectionCost h D) :ℚ)≤6*tW J [r,h] := by
    push_cast [mass]
    calc
      _ ≤ ∑ z∈uG A ell,6*((AN J z :ℚ)*tW z [r,h]) := by
        apply zQk
        intro z hz
        have hm:=(surface_spec hz).1
        obtain ⟨v,_,hv,hle⟩ :=
          P6_6_7_3.local_weight hp.factor.1 hp.proper hm (ell:=genericOrder G z) le_rfl
        have he :AN J z=v :=
          ENat.natCast_inj.mp ((a9B hm).trans hv)
        simp only [mul_assoc,← zxw]
        rw [← mul_assoc,mul_left_comm]
        apply (mul_le_mul_of_nonneg_right
          (show (genericOrder R z :ℚ)*(genericOrder G z :ℚ)≤AN J z by
            rw [he,mul_comm]; exact_mod_cast hle)
          (Finset.sum_nonneg fun _ _=>mul_nonneg (zqJ _) (zqJ _))).trans
        exact mul_le_mul_of_nonneg_left (hsum z hz) (zqJ _)
      _≤_:= by
        rw [← zxw]
        exact mul_le_mul_of_nonneg_left
          (retain_cycle J [r,h] (by simp [hr',hch]) (by simp) (by simpa using hJ)
            _ (fun _ hz=>(surface_spec hz).1)) (by norm_num)
  have hg:=hcut H q [r,h] hq (by simp [hr',hch]) (by simp) (by simpa using hH)
    _ (bHn hp.H6) hG
  rw [← aIc R G] at hg
  have hfin:=literal R (firstSlot C R cs) q r h hp.factor.1.ne_zero (first_fits hp) hq hr hch
  have hh' := hb.trans (mul_le_mul_of_nonneg_left (hg.trans hfin) (by norm_num : (0:ℚ)≤6))
  have hs : (32 :ℚ)*(mass F (fun _ D =>sectionCost h D) :ℚ) ≤
      6*(wP (firstSlot C R cs) q r h:ℚ) := by linarith only [hh']
  exact_mod_cast hs
end qZqYIua
end
section
set_option autoImplicit true
namespace qZqYIua
theorem proof :q90NBie.c1 :=of_literal literal_bound
end qZqYIua
end
section
set_option autoImplicit true
namespace qp1uNmb
open dN (AX bC)
open Dr (dimension aCR bHn)
theorem proof :qduj6fa.c1 := by
  intro J V p boxes hreg hfit hp hlen hboxes hdim S hS
  have hd:dimension (AX J V)≤boxes.length :=
    (aCR hreg).trans (by omega)
  exact (qZqYIua.retain_cycle (AX J V) boxes hboxes hlen hd S hS).trans
    (bau.proof J p boxes hp hboxes (hlen.trans (by decide)) hdim
      (bC V) (bHn hfit) hreg)
end qp1uNmb
end
section
set_option autoImplicit true
namespace P6_6_5
noncomputable section
open P6 (node)
open P6_6 (Messages m6 gZ)
open aR (af extend qE)
open oR (qg ang Rr)
open ana (aVQ bZ3)
open scoped BigOperators
private def firstCap (v :ℕ) (f :af 2) :ℕ :=
  zBz f.totalDegree (qE f)
    (aNR v) (aUS v)
private theorem d5N {w Γ s v} (h:Messages w Γ s) (hv :v≤ m6.t)
    (f :af 2) (hf :Irreducible f) (hp:0<f.degreeOf 1)
    (hB:f.totalDegree≤O1 v) (hJ:qE f≤ayY v)
    (hreg : ∀ γ∈Γ,qg 1 f (extend (s γ))) :ang w Γ s (firstCap v f) := by
  classical
  obtain ⟨C⟩:=czH.proof f gZ (O1 v) (ayY v)
    (by decide) (by decide) (ebr hv) hB ((bZ3 f).trans hJ)
  refine ⟨Finset.univ.filter (fun i => ∀ γ∈Γ,(s γ).eval (node i)=w i),
    fun _ hi=>(Finset.mem_filter.mp hi).2,?_⟩
  intro i hi
  have hmiss : ∃ γ∈Γ,(s γ).eval (node i)≠w i:= by
    by_contra! hall
    exact hi (Finset.mem_filter.mpr ⟨zTc _,hall⟩)
  have hb:0<aNR v := by simp [aNR]
  have htop:aF0.YM gZ (O1 v) (ayY v) =
      aUS v := by
    unfold aF0.YM aUS
    rw [z0U (show 1≤P6_6.bf by decide)]
    rfl
  have hpositive :0<aUS v := by
    unfold aUS
    rw [z0U (show 1≤P6_6.bf by decide)]
    exact lt_min hb (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left _ _))
  refine (cz7.a8m h.distinct f hf hp hreg hb hpositive i hmiss
    (C.cut (node i) (w i)) (aVQ _ (C.ags _ _) (htop ▸ C.top_bound _ _))
    (fun γ hγ=>C.agrees _ (h.degree γ hγ) (hreg γ hγ) _ _)).trans ?_
  exact Nat.add_le_add_left (ztf _ (bZ3 f)) _
theorem ebI {w Γ s v} (h:Messages w Γ s) (hv :v≤ m6.t)
    {n:ℕ} (f :Fin n→af 2) (hf :bjg v f)
    (hregular : ∀ γ∈Γ,∃ i,qg 1 (f i) (extend (s γ))) :
    ∃ C:Rr w Γ s,Γ⊆C.CF∧C.n≤O1 v ∧
      C.BJ≤bGL v := by
  classical
  let part (i:Fin n) :=Γ.filter fun γ=>qg 1 (f i) (extend (s γ))
  have hsub (i:Fin n) :part i⊆Γ:=zT0 _ _
  have hlocal (i:Fin n) :ang w (part i) s (firstCap v (f i)) := by
    apply d5N (h.mono (hsub i)) hv (f i) (hf.irreducible i) (hf.positive i)
    · exact (zfK (fun j _=>zD0 (f j).totalDegree)
        (zTc i)).trans hf.total
    · exact (zfK (fun j _=>zD0 (qE (f j)))
        (zTc i)).trans hf.index
    · exact fun γ hγ=>(Finset.mem_filter.mp hγ).2
  let C:Rr w Γ s :=⟨n,part,fun i=>firstCap v (f i),hsub,hlocal⟩
  refine ⟨C,?_,?_,?_⟩
  · intro γ hγ
    obtain ⟨i,hi⟩:=hregular γ hγ
    exact Finset.mem_biUnion.mpr ⟨i,zTc _,Finset.mem_filter.mpr ⟨hγ,hi⟩⟩
  · change n≤O1 v
    calc
      n = ∑ _:Fin n,1 := by simp
      _ ≤ ∑ i,(f i).totalDegree :=zQk fun i _ =>
        (Nat.succ_le_of_lt (hf.positive i)).trans (MvPolynomial.degreeOf_le_totalDegree _ _)
      _≤O1 v :=hf.total
  · change (∑ i,firstCap v (f i))≤bGL v
    simp only [firstCap,zBz,Finset.sum_add_distrib,← Finset.sum_mul]
    exact z9f (ztf (aUS v) hf.total)
      (ztf (aNR v-aUS v) hf.index)
end
end P6_6_5
end
section
set_option autoImplicit true
namespace qSCPCwb
noncomputable section
open P6 (I K node)
open P6_6 (Messages)
open P6_6_5 (bfL)
open aR (ao embed extend)
open oR (ang)
open we (cH)
open Polynomial MvPolynomial
open scoped BigOperators
open private bK9 D4 bcP cNe dhJ from ProximityPrize.SubmissionLower.BG
open private b9N from ProximityPrize.SubmissionLower.I
private theorem aUc {w Γ s} (h:Messages w Γ s) {γ:K} (hγ:γ∈Γ) :
    (extend (s γ)).natDegree≤133671 := by
  have hsmall: (s γ).natDegree≤133425:=h.degree γ hγ
  simpa only [Polynomial.natDegree_map] using hsmall.trans (by decide :133425≤133671)
private theorem dMV {w Γ s} (h:Messages w Γ s) :
    Set.InjOn (fun γ=>afs (extend (s γ))) (Γ:Set K) := by
  intro γ hγ δ hδ heq
  apply h.distinct hγ hδ
  apply zTo embed embed.injective
  apply zTo (algebraMap ao cH) (algebraMap ao cH).injective
  rw [← bK9 _ (aUc h hγ),← bK9 _ (aUc h hδ)]
  exact congrArg JC heq
private theorem cM9 {w Γ s} (h:Messages w Γ s) {γ:K} (hγ:γ∈Γ) (i:I) :
    MvPolynomial.eval (afs (extend (s γ))) (D4 w i)=0 ↔
      (s γ).eval (node i)=w i:= by
  rw [D4,cNe,bK9 _ (aUc h hγ),sub_eq_zero]
  unfold bcP
  simp only [RingHom.comp_apply,Polynomial.eval_map_apply]
  exact (algebraMap ao cH).injective.eq_iff.trans embed.injective.eq_iff
private theorem zeroDim_card {w Γ s} (h:Messages w Γ s)
    (Q:Bk) (hdim: (affineHilbertPolynomial Q).natDegree=0)
    (hcurve : ∀ γ∈Γ,afs (extend (s γ))∈zeroLocus cH Q) :
    (Γ.card:ℚ)≤affineDegree Q:= by
  classical
  let A:= fun γ=>afs (extend (s γ))
  have hsub: (↑(Γ.image A) :Set GD)⊆zeroLocus cH Q:= by
    intro a ha
    obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp ha
    exact hcurve γ hγ
  obtain ⟨hfinite,hdegree⟩:=finite_zeroLocus_and_ncard_le_affineDegree (K:=cH) Q hdim
  have hcard:=Set.ncard_le_ncard hsub hfinite
  rw [Set.ncard_coe_finset,Finset.card_image_of_injOn (dMV h)] at hcard
  exact (Nat.cast_le.mpr hcard).trans hdegree
theorem c1x {w Γ s} {d:ℕ} (h:Messages w Γ s)
    (Q:Bk) (hp:Q.IsPrime) (hdim: (affineHilbertPolynomial Q).natDegree≤1)
    (hdegree :affineDegree Q≤(d:ℚ))
    (hcurve : ∀ γ∈Γ,afs (extend (s γ))∈zeroLocus cH Q) :
    ang w Γ s d:= by
  classical
  by_cases hzero : (affineHilbertPolynomial Q).natDegree=0
  · have hcard:=(zeroDim_card h Q hzero hcurve).trans hdegree
    exact ⟨∅,by simp,fun i _=>(Finset.card_filter_le _ _).trans (Nat.cast_le.mp hcard)⟩
  have hone : (affineHilbertPolynomial Q).natDegree=1 := by omega
  apply b9N
  intro i hi
  let cut:=D4 w i
  have hcut:cut∉Q:= by
    obtain ⟨γ,hγ,hmiss⟩:=hi
    exact fun hc=>hmiss ((cM9 h hγ i).mp (hcurve γ hγ cut hc))
  let J:= Q ⊔ zye {cut}
  have hJ:=principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hp hcut (dhJ (bcP (node i)) (bcP (w i)))
  rw [hone] at hJ
  have hjdim:=za7 hJ.1
  have hjdeg:affineDegree J≤affineDegree Q:= by
    rw [affineDegree_of_natDegree_eq_zero hjdim,affineDegree,hone]
    simpa using hJ.2
  refine Nat.cast_le.mp ((zeroDim_card (h.mono (zT0 _ _)) J hjdim ?_).trans
    (hjdeg.trans hdegree))
  intro γ hγ
  obtain ⟨hγ,he⟩:=Finset.mem_filter.mp hγ
  exact mem_zeroLocus_sup_span_singleton_iff.mpr
    ⟨hcurve γ hγ,(cM9 h hγ i).mpr he⟩
theorem dRT {w Γ s} {d:ℕ} (h:Messages w Γ s) (hd:0<d)
    (hc:ang w Γ s d) :Γ.card≤2*d:= by
  have hcount:=bfL h hc
  omega
end
end qSCPCwb
end
section
set_option autoImplicit true
set_option Elab.async false
namespace q7twcKc
noncomputable section
open P6_6 P6_6_7 MvPolynomial
open qAzl5me (Selected MemberCurve Family active chartRow)
open aR (extend)
open dN (kC bC AX Ch)
open rW (kT n8 dimension Yg lA bQ1)
open private cVk from ProximityPrize.SubmissionLower.V
open scoped BigOperators
def bQG (C:Context) (cs :ChartCase C.n) (Sfc:n8) (γ:P6.K)
    (B:kT) :Prop :=
  ∃ i a,Selected C cs Sfc γ i a∧Family C i γ B∧dimension B=1 ∧
    MemberCurve (chartRow C i a) Sfc (lA B) ∧
    lA B≤Ch (extend (C.s γ))
private theorem source_inj {C:Context} {cs :ChartCase C.n} {F:Finset kT}
    {Sfc:kT→n8} {γ:kT→P6.K}
    (h : ∀ B∈F,bQG C cs (Sfc B) (γ B) B) :
    Set.InjOn lA (F:Set kT) := by
  intro B hB B' hB' he
  obtain ⟨i,a,hs,hf,_⟩:=h B hB
  obtain ⟨i',a',hs',hf',_⟩:=h B' hB'
  have hr :bQ1 (C.f i) B' := by
    obtain ⟨r,hg,hs⟩:=hf.1.regular
    exact ⟨r,he ▸ hg,he ▸ hs⟩
  exact cVk bRp.proof bRq.proof
    (C.f i) ⟨hf.1.prime,hf.1.regular⟩ ⟨hf'.1.prime,hr⟩ he
theorem membership_sum {C:Context} {R G ell cs} (h:PairInput C R G ell cs)
    (A:SurfaceAssignment C R G) (F:Finset kT) (rep:kT→P6.K)
    (hF : ∀ B∈F,rep B∈active C R G ell cs A∧bQG C cs (A.aI (rep B)) (rep B) B) :
    ∑ B∈F,((ell*genericOrder R (A.aI (rep B)) :ℕ) :ℚ)*affineDegree B ≤
      (((firstSlot C R cs).b*(cutterBody C ell).b *
        (weightedChart (bf+1) (chartBody C R cs)).b:ℕ) :ℚ) := by
  classical
  let Sfc:=A.aI ∘ rep
  let J:=kC R G
  let b:=(weightedChart (bf+1) (chartBody C R cs)).b
  let wt:= fun B=>ell*genericOrder R (Sfc B)
  have hsub : ∀ B∈F,J.IsMinimalPrime (Sfc B) := by
    intro B hB
    obtain ⟨hm,ho,_⟩:=Finset.mem_filter.mp (hF B hB).1
    exact (A.valid (rep B) hm ho).1
  have hwt (B:kT) (hB:B∈F) :wt B≤Yg J (Sfc B) := by
    have hz :=hsub B hB
    obtain ⟨v,_,hlen,hw⟩:=P6_6_7_3.local_weight h.factor.1 h.proper hz
      (Finset.mem_filter.mp (hF B hB).1).2.2.1
    change dN.oA J (Sfc B) hz.isPrime=(v :ℕ∞) at hlen
    rw [Yg,dite_eq_left hz.isPrime,hlen,ENat.toNat_natCast]
    exact hw
  have hinj:=source_inj (fun B hB=>(hF B hB).2)
  have hd (B:kT) (hB:B∈F) :affineDegree B=affineDegree (lA B) := by
    obtain ⟨_,_,_,hf,hdim,_⟩:=(hF B hB).2
    exact NS.of_children cyx.proof cyy.proof
      cyz.proof B hf.1.prime hf.1.extended_prime hdim hf.1.birational
  have hfiber (z :n8) (hz :J.IsMinimalPrime z) :
      ∑ B∈F.filter (fun B=>Sfc B=z),(wt B:ℚ)*affineDegree B ≤
        (b:ℚ)*((Yg J z :ℚ)*affineDegree z) := by
    let V:=F.filter (fun B=>Sfc B=z)
    let _:=hz.isPrime
    by_cases hV:V.Nonempty
    · obtain ⟨B₀,h₀⟩:=hV
      obtain ⟨h₀F,h₀z⟩:=Finset.mem_filter.mp h₀
      have hsrc :=(hF B₀ h₀F).2
      change bQG C cs (Sfc B₀) _ _ at hsrc
      rw [h₀z] at hsrc
      obtain ⟨i,a,hs,_⟩:=hsrc
      obtain ⟨E,hE,he⟩:=member_equation h hs
      have hcurves (B:kT) (hB:B∈V) :
          bC E∉z∧(AX z E).IsMinimalPrime (lA B) := by
        obtain ⟨hBF,hBz⟩:=Finset.mem_filter.mp hB
        have hsrc :=(hF B hBF).2
        change bQG C cs (Sfc B) _ _ at hsrc
        rw [hBz] at hsrc
        obtain ⟨j,c,hs',_,_,hm,hpoint⟩:=hsrc
        obtain ⟨rfl,rfl⟩:=Selected.unique hs hs'
        exact b85 hm (fun hh=>hs'.regular (BO.Ue.mp (hpoint hh))) he
      have hdeg:=principalCut_sum_affineDegree_minimalPrimes_le (hcurves B₀ h₀).1 hE
      have hVs :V⊆F:=zT0 _ _
      calc
        _ ≤ ∑ B∈V,(Yg J z :ℚ)*affineDegree (lA B) := by
          apply zQk
          intro B hB
          rw [← hd B (hVs hB)]
          apply mul_le_mul_of_nonneg_right _ (affineDegree_nonneg _)
          exact_mod_cast (Finset.mem_filter.mp hB).2 ▸ hwt B (hVs hB)
        _=(Yg J z :ℚ) * ∑ P∈V.image lA,affineDegree P:= by
          rw [zxw,Finset.sum_image (hinj.mono hVs)]
        _≤(Yg J z :ℚ)*((b:ℚ)*affineDegree z) :=
          mul_le_mul_of_nonneg_left ((Finset.sum_le_sum_of_subset_of_nonneg
            (fun P hP=> by
              obtain ⟨B,hB,rfl⟩:=Finset.mem_image.mp hP
              exact Ideal.mem_minimalPrimesFinset.mpr (hcurves B hB).2)
            (fun P _ _=>affineDegree_nonneg P)).trans hdeg) (by positivity)
        _ = _:= by ring
    · change (∑ B∈V,(wt B:ℚ)*affineDegree B)≤_
      rw [Finset.not_nonempty_iff_eq_empty.mp hV,Finset.sum_empty]
      exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (affineDegree_nonneg _))
  calc
    _ = ∑ z∈J.minimalPrimesFinset,∑ B∈F.filter (fun B=>Sfc B=z),
        (wt B:ℚ)*affineDegree B :=
      (Finset.sum_fiberwise_of_maps_to (fun B hB=>Ideal.mem_minimalPrimesFinset.mpr (hsub B hB)) _).symm
    _ ≤ ∑ z∈J.minimalPrimesFinset,(b:ℚ)*((Yg J z :ℚ)*affineDegree z) :=
      zQk fun z hz=>hfiber z (Ideal.mem_minimalPrimesFinset.mp hz)
    _≤(b:ℚ)*((firstSlot C R cs).b*(cutterBody C ell).b) := by
      rw [← zxw]
      exact mul_le_mul_of_nonneg_left (qnODzma.cycle_budget h) (by positivity)
    _ = _:= by push_cast; ring
end
end q7twcKc
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qQCYsrb
open aR (Shape aO)
open P6_6 P6_6_8 q2w4Sxc
open q33KzTa (tu AffineFits block stock_eq)
open AJ (bOw)
open scoped BigOperators
open private bSj.aTY from ProximityPrize.SubmissionLower.E6
open private eiI from ProximityPrize.SubmissionLower.E6
open private WC aEH byM bvX from ProximityPrize.SubmissionLower.E6
open private block_affine from ProximityPrize.SubmissionLower.Z8Nymda
private theorem homogeneous (x :Shape) :Gq x≤AJ.ahC Wk x := by
  by_cases h:x.b≤4025∧x.j≤1710∧x.t≤570
  · have he :wV.HY (4025 - x.b+1) (1710 - x.j) (570 - x.t) =
        AJ.bmI ⟨4025 - x.b,1710 - x.j,570 - x.t⟩:= by
        simp only [wV.HY,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte,
          Nat.add_sub_cancel]
    simp only [Gq,AJ.ahC,ite_eq_left h]
    rw [← he,bSj.aTY]
    exact zQk fun d _=>eiI (min_le_left d _) le_rfl le_rfl
  · simp only [Gq,AJ.ahC,ite_eq_right h,zD0]
private theorem eNI {b p a s :ℕ} {r :Shape} {k :ℕ}
    (h:tu 6 p a s) (hf :AffineFits b 6 p) :
    massBlock ⟨b,6,1⟩ r k 0 p≤a - b*s := by
  have he :=block_affine (b:=b) (by decide :0<6) hf
  rw [h.1,h.2] at he
  apply le_trans _ (show block ⟨b,6,1⟩ 0 p≤a - b*s by omega)
  simp only [massBlock,block,bOw,Nat.zero_add]
  refine zQk fun d _ => ?_
  rw [layerMass,aUJ,stock_eq]
  exact dNb ⟨z8K _ _,z8K _ _,z8K _ _⟩
private def unpack :ℕ→ℕ→List ℕ
  | 0,_=>[]
  | n+1,w=>if w=0 then [] else (w % 256) :: unpack n (w/256)
abbrev upper (v r :Shape) (k d:ℕ) :=
  AJ.ahC Wk (used v r k d)
abbrev Order (b k x y z :ℕ) :=CompanionTest ⟨b,6,1⟩ ⟨x,y,z⟩ k
def Tail (v r :Shape) (k start len cost:ℕ) :Prop :=
  massBlock v r k start len≤ cost
theorem segment {v r :Shape} {k start len cost word:ℕ}
    (hlen: (unpack 8 word).sum=len)
    (hc:aEH (upper v r k) start (unpack 8 word)=cost) :
    Tail v r k start len cost:= by
  have hw:=byM (layer_anti v r k) (unpack 8 word) start
  have hle (d:ℕ) :layerMass v r k d≤upper v r k d:= by
    rw [layerMass,aUJ]
    exact homogeneous _
  have hs :=bvX hle (unpack 8 word) start
  rw [hc] at hs
  rw [← hlen]
  simpa only [Tail,massBlock,bOw,WC] using hw.trans hs
theorem joinTail {v r :Shape} {k start m n a b:ℕ}
    (h:Tail v r k start m a) (g:Tail v r k (start+m) n b) :
    Tail v r k start (m+n) (a+b) := by
  unfold Tail at *
  rw [massBlock_add]
  exact z9f h g
theorem strict {b p a s k n x :ℕ} {r :Shape}
    (base :tu 6 p a s) (hf :AffineFits b 6 p)
    (h:Tail ⟨b,6,1⟩ r k p n x)
    (hz :upper ⟨b,6,1⟩ r k (p+n)=0)
    (hb:a - b*s + x<gG) :
    CompanionTest ⟨b,6,1⟩ r k := by
  apply companion_of_mass (n:=p+n)
  · rw [layerMass,aUJ]
    exact za7 ((homogeneous _).trans_eq hz)
  · rw [mass_eq_block,massBlock_add,Nat.zero_add]
    exact (z9f (eNI base hf) h).trans_lt hb
theorem transport {v w r s :Shape} {k l:ℕ} (hv :aO v w) (hr :aO r s)
    (hl:l≤k) (h:CompanionTest v r k) :CompanionTest w s l:= by
  unfold CompanionTest at *
  apply lt_of_le_of_lt (zQk fun d _=>dNb ?_) h
  obtain ⟨a,b,c⟩:= Q5 hv (d+1)
  obtain ⟨x,y,z⟩:= Q5 hr (d+2 - k)
  have hs :=Nat.sub_le_sub_left hl (d+2)
  exact ⟨z9f a (x.trans (ztf _ hs)),
    z9f b (y.trans (ztf _ hs)),
    z9f c (z.trans (ztf _ hs))⟩
theorem bO4 {b k :ℕ} {r :Shape} (h:CompanionTest ⟨b,6,1⟩ r k) :
    CompanionTest ⟨b,6,2⟩ r k :=
  transport (v :=⟨b,6,1⟩) (w:=⟨b,6,2⟩) (r :=r) (s :=r) (k :=k) (l:=k)
    ⟨le_rfl,le_rfl,Nat.le_succ 1⟩ ⟨le_rfl,le_rfl,le_rfl⟩ le_rfl h
theorem regular {v lo hi:Shape} {k f :ℕ} {iL:Shape}
    (hk :0<k∧k≤132) (ho:CompanionTest v lo k∨k=1)
    (hs :hi.t=1∨2≤lo.t) (ht:3*hi.t≤hi.j)
    (hC:Lw v=iL) (hF:selfFee v hi k false=f)
    (hle :f≤dot iL lo) :Certificate v lo hi:= by
  apply Certificate.regular ⟨hk.1,hk.2,ho⟩ hs ht
  rwa [hF,hC]
end qQCYsrb
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qQCYsrb

open P6_6 P6_6_8 q2w4Sxc
open q33KzTa (tu base_next)
open private g1 g2 g4 from ProximityPrize.SubmissionLower.ZBG70hc
local notation "g!" a "," n "," vx "," vy=>base_next (k :=n) (x :=vx) (y :=vy) a rfl rfl
theorem g24a :tu 6 24 0x8afc75fe8ba 0x831186d0a :=g! g1,8,0x2aada4c8c5f,0x441944c5e
theorem g40a :tu 6 40 0xd632da202d8 0x13e34a9ad6:=g! g2,8,0x23f84049d5e,0x64b67d2be
theorem g67a :tu 6 67 0x139964f0738c 0x2ce700373d:=g! g4,3,0x97cf2d5e8f,0x2eda36c0d
theorem g68a :tu 6 68 0x13cab5908236 0x2de1817709:=g! g67a,1,0x3150a00eaa,0xfa813fcc
theorem g71a :tu 6 71 0x145adc103f91 0x30d1eb38a6:=g! g68a,3,0x90267fbd5b,0x2f069c19d
theorem g75a :tu 6 75 0x15126474ee32 0x34bcc0b60b:=g! g71a,4,0xb78864aea1,0x3ead57d65
end qQCYsrb
end
