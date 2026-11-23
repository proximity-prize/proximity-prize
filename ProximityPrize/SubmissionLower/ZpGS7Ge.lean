import ProximityPrize.SubmissionLower.ZxBy9Fe
import ProximityPrize.SubmissionLower.ZdO7nqb
import ProximityPrize.SubmissionLower.ZfDhrOb
set_option Elab.async false
open _root_ renaming Finset.card_biUnion_le → z1B, Finset.filter_subset → zT0, Finset.single_le_sum → zfK, Finset.sum_le_sum → zQk, Function.Injective → zq4, Ideal → znc, Ideal.Quotient.mk → zVv, Nat.cast_nonneg → zqJ, Nat.pos_of_ne_zero → zOl
set_option maxHeartbeats 1400000
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
namespace qBgaZma
noncomputable section
open P6 (p)
open P6_7_7 (aAT I0)
open P5_7 (FarBand farAgreement)
open P5_7_5 (nV BC aqE)
open akZ (aB5 weightedDegree collect bt8
  aSK cVg caH strip)
open cu gT pI YX XY Polynomial
open qQ (aeH VN a4N bH5 bH6 bH4)
open atc (cN0)
open scoped BigOperators Classical
open private b4x b9B b01 dde cBv b6D b6E from ProximityPrize.SubmissionLower.T
open private ddM ajB from ProximityPrize.SubmissionLower.D7
open private eo1 from ProximityPrize.SubmissionLower.ZdO7nqb
open private ddo from ProximityPrize.SubmissionLower.CR
private structure aeX {h u del} {M:P1.FJ h u del} {Γ} (F:P1.bje farAgreement M Γ)
    (b:FarBand) (G H :tK) where
  components :Finset (znc Ambient)
  DN :aB5 components
  fits :dM components (BC b)
  content:aZ
  content_ne :content≠0
  content_le :content.totalDegree≤(nV b 0).free.shape.U + (nV b 0).moving.shape.U
  Eh : ∀ γ∈Γ,qD (M.label γ) content=0 ∨
    FW G (F.scalar γ)=0∨FW H (F.scalar γ)=0 ∨
      ∃ I∈components,I0 F I γ
private theorem gNf {b:FarBand} (sched:aqE b)
    (empty :b.row.RU.isEmpty=true)
    {h u del} {M:P1.FJ h u del} {Γ} (F:P1.bje farAgreement M Γ)
    {P Q:Jet} (hnc:aeH P Q)
    {A:NO P (nV b 0).free.shape} {B:NO Q (nV b 0).moving.shape}
    (a :aSK A) (b' : aSK B)
    (hrows : ∀ γ∈Γ,rD P (M.label γ) (F.scalar γ)=0 ∧
      rD Q (M.label γ) (F.scalar γ)=0) :
    Nonempty (aeX F b A.equation B.equation) := by
  classical
  let s :=(nV b 0).free.shape
  let t:=(nV b 0).moving.shape
  obtain ⟨gs,gt⟩:=sched.aE7 0 sched.aXU
  have hord (D:Jet) (hD:Irreducible D) (hda :D ∣a.row) (hdb:D ∣b'.row) :
      D.natDegree=0:= by
    by_contra hp
    obtain ⟨G,rfl⟩:=hnc D hD (hda.trans a.row_dvd) (hdb.trans b'.row_dvd)
      (zOl hp)
    exact a.no_fixed G hD hda
  obtain ⟨N,L,T,hL,hT,hproper,hN⟩ :=
    cN0 a.row b'.row a.aPZ b'.aPZ a.primitive hord
  let x :=My N.prod
  let z :=N.prod.natDegree
  have hN0 : ∀ f∈N,f≠0:= fun f hf=>(hN f hf).1.ne_zero
  have hF:=b9B N hN0
  have hAc:oU (C N.prod*L) s :=hL ▸ a.row_caps
  have hBc:oU (C N.prod*T) t:=hT ▸ b'.row_caps
  obtain ⟨hx,hz,hcL⟩:=b4x hF hproper.left_ne hAc
  obtain ⟨hx',hz',hcT⟩:=b4x hF hproper.right_ne hBc
  obtain ⟨S,hgeom,hS,hcover⟩ :=
    bt8 hproper (min_le_right _ _) (min_le_right _ _) hcL hcT
  have hs1 :My (1 :Equation)=0:= by
    rw [← atc.bg3]
    simpa only [C_1,MvPolynomial.totalDegree_one] using atc.bNz (1 :aZ)
  have hseed : (∑ f∈N.toFinset,My f)≤x :=
    b01 My hs1 (fun hf hg=>dde hf hg) N hN0
  have hy : (∑ f∈N.toFinset,f.natDegree)≤z :=
    b01 natDegree natDegree_one (fun hf hg=>natDegree_mul hf hg) N hN0
  obtain ⟨U,hUgeom,hU,hUcover⟩:=collect N.toFinset
    (fun f=>af1 (My f) f.natDegree) (fun f z R=>yq f z R=0)
    (fun f hf=>caH f (hN f (Multiset.mem_toFinset.mp hf)).1
      (hN f (Multiset.mem_toFinset.mp hf)).2
      (((zfK (fun _ _=>Nat.zero_le _) hf).trans hy).trans_lt
        (hz.trans_lt gs.ode.small)))
  refine ⟨{
    components :=S∪U
    DN := ?_
    fits := ?_
    content:=a.content*b'.content
    content_ne :=mul_ne_zero a.content_ne b'.content_ne
    content_le :=(MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add a.content_le b'.content_le)
    Eh := ?_ }⟩
  · intro I hI
    exact (Finset.mem_union.mp hI).elim (hgeom I) (hUgeom I)
  · intro k
    have h:=aZC.ddN s t (r :=1) (m:=1) false k
      (le_min hx hx') (le_min hz hz') gs.ode.jb gt.ode.jb
    rw [ddM] at h
    simp only [BC,empty,ite_true]
    exact (bOC (fun I=>pN I k) _ _).trans
      ((Nat.add_le_add (hS k) ((hU k).trans (eHM _ _ _ hseed hy k))).trans
        (ajB h))
  · intro γ hγ
    obtain ⟨hp,hq⟩:=hrows γ hγ
    rcases a.Eh _ _ hp with h | h | ha
    · exact Or.inl (by rw [map_mul,h,zero_mul])
    · exact Or.inr (Or.inl h)
    rcases b'.Eh _ _ hq with h | h | hb
    · exact Or.inl (by rw [map_mul,h,mul_zero])
    · exact Or.inr (Or.inr (Or.inl h))
    apply Or.inr ∘ Or.inr ∘ Or.inr
    by_cases hzero :yq N.prod (M.label γ) (F.scalar γ)=0
    · obtain ⟨f,hf,hmark⟩:=cBv hzero
      obtain ⟨I,hI,hon⟩:=hUcover f (Multiset.mem_toFinset.mpr hf) _ _ hmark
      exact ⟨I,Finset.mem_union_right _ hI,hon⟩
    · rw [hL,b6D,b6E,mul_eq_zero] at ha
      rw [hT,b6D,b6E,mul_eq_zero] at hb
      obtain ⟨I,hI,hon⟩:=hcover _ _ (ha.resolve_left hzero) (hb.resolve_left hzero)
      exact ⟨I,Finset.mem_union_left _ hI,hon⟩
private theorem eo2 {b:FarBand} (sched:aqE b)
    (hne : ¬ b.row.RU.isEmpty=true)
    {h u del} {M:P1.FJ h u del} {Γ} (F:P1.bje farAgreement M Γ)
    {P Q:Jet} (hQ:Q≠0) (hnc:aeH P Q)
    (hQc:oU Q (nV b 0).moving.shape)
    {A:NO P (nV b 0).free.shape} {B:NO Q (nV b 0).moving.shape}
    (a :aSK A)
    (hrows : ∀ γ∈Γ,rD P (M.label γ) (F.scalar γ)=0 ∧
      rD Q (M.label γ) (F.scalar γ)=0)
    (T8:ℕ→Jet)
    (hlater : ∀ i∈b.row.RU,T8 i≠0∧oU (T8 i) (nV b i).free.shape ∧
      ∀ j r,r≤(nV b i).dI →
        ∀ γ∈Γ,rD (A5 j r (T8 i)) (M.label γ) (F.scalar γ)=0) :
    Nonempty (aeX F b A.equation B.equation) := by
  obtain ⟨D,hD,hcap,hroot⟩:=cVg a
  obtain ⟨S,hG,hFit,hC⟩:=eo1 sched hQ hnc hQc T8
    (fun i hi=>⟨(hlater i hi).1,(hlater i hi).2.1⟩)
    b.row.RU (fun _ hi=>hi) D _ hD hcap
  refine ⟨{
    components :=S
    DN :=hG
    fits := fun k => ?_
    content:=a.content
    content_ne :=a.content_ne
    content_le :=a.content_le.trans (Nat.le_add_right _ _)
    Eh := ?_ }⟩
  · rw [BC,ite_eq_right hne]
    simpa only [weightedDegree,zero_mul,Finset.sum_const_zero,Nat.add_zero] using hFit k (fun _=>0)
  · intro γ hγ
    obtain ⟨hp,hq⟩:=hrows γ hγ
    rcases a.Eh _ _ hp with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (hC _ _
        (fun i hi j r hr=>(hlater i hi).2.2 j r hr γ hγ) hq (hroot _ _ h))))
private theorem finish {h u del} {M:P1.FJ h u del} {Γ} {F:P1.bje farAgreement M Γ}
    {b:FarBand} {G H :tK} (sched:aqE b) (C:aeX F b G H) :
    Nonempty (aAT M F b G H) := by
  classical
  let S:=C.components
  let noSeeds :=S.filter (fun I=>pN I 0=0)
  let constY:=S.filter (fun I=>0<pN I 0 ∧
    ¬ zq4 ((zVv I).comp F7))
  let parents :=S.filter (fun I=>0<pN I 0 ∧
    zq4 ((zVv I).comp F7))
  have hparents (I:znc Ambient) (hi:I∈parents) :xN I:= by
    obtain ⟨hI,ha,hy⟩:=Finset.mem_filter.mp hi
    obtain ⟨hprime,hdim,_,hf⟩:=C.DN I hI
    have hsmall (k :Fin 4) :pN I k<p :=
      (evL hI k).trans_lt ((C.fits k).trans_lt (sched.bq6 k))
    exact ⟨hprime,hdim,hf.Kw,hf.jU,hf.kK,hf.Bo,
      ⟨ha,hsmall 0⟩,hsmall 2,hsmall 3,hy⟩
  have fit_subset {T:Finset (znc Ambient)} (hT:T⊆S) :
      dM T (BC b) :=ecA hT C.fits
  have seed_exists (I:znc Ambient) (hi:I∈noSeeds) :
      ∃ D:VN,D.curve.totalDegree≤pN I 2 ∧
        D.points.card≤pN I 3 ∧ ∀ z R,IZ I z R→D.ow z := by
    obtain ⟨hI,hz⟩:=Finset.mem_filter.mp hi
    obtain ⟨hprime,hdim,_,hf⟩:=C.DN I hI
    exact ddo I hprime hdim hf hz
  let xg (I:znc Ambient) :VN :=
    if hi:I∈noSeeds then Classical.choose (seed_exists I hi) else ⟨1,one_ne_zero,∅⟩
  have hseedImage (I:znc Ambient) (hi:I∈noSeeds) :
      (xg I).curve.totalDegree≤pN I 2 ∧
      (xg I).points.card≤pN I 3 ∧
      ∀ z R,IZ I z R→(xg I).ow z := by
    simpa only [xg,dite_eq_left hi] using Classical.choose_spec (seed_exists I hi)
  let imageCover :=a4N noSeeds xg
  let onY (I:znc Ambient) :=(Γ.filter (I0 F I)).image (fun γ=>kr (F.scalar γ))
  let ordinates :=constY.biUnion onY
  have hy (I:znc Ambient) (hi:I∈constY) : (onY I).card≤pN I 0:= by
    obtain ⟨hI,ha,hy⟩:=Finset.mem_filter.mp hi
    apply le_trans (b:=1) _ ha
    apply Finset.card_le_one.mpr
    intro x hx y hy'
    obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hx
    obtain ⟨δ,hδ,rfl⟩:=Finset.mem_image.mp hy'
    exact eHX (C.DN I hI).1 hy
      (Finset.mem_filter.mp hγ).2 (Finset.mem_filter.mp hδ).2
  refine ⟨{
    parents :=parents
    active :=hparents
    a4E := fun I hi=>(C.DN I (Finset.mem_filter.mp hi).1).2.2.1
    bst:=ecA (zT0 _ _) C.fits
    seed :=imageCover
    acI := ?_
    seed_points := ?_
    ordinates :=ordinates
    ordinate_le := ?_
    content:=C.content
    content_ne :=C.content_ne
    content_le :=C.content_le
    Eh := ?_ }⟩
  · calc
      _ ≤ ∑ I∈noSeeds,(xg I).curve.totalDegree :=bH5 _ _
      _≤ mass noSeeds 2 :=zQk fun I hi=>(hseedImage I hi).1
      _≤_:=fit_subset (zT0 _ _) 2
  · calc
      _ ≤ ∑ I∈noSeeds,(xg I).points.card:=bH6 _ _
      _≤ mass noSeeds 3:=zQk fun I hi=>(hseedImage I hi).2.1
      _≤BC b 3:=fit_subset (zT0 _ _) 3
      _≤_:=sched.bq5
  · calc
      _ ≤ ∑ I∈constY,(onY I).card:=z1B
      _≤ mass constY 0:=zQk hy
      _≤_:=fit_subset (zT0 _ _) 0
  · intro γ hγ
    rcases C.Eh γ hγ with h | h | h | ⟨I,hI,hon⟩
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · by_cases ha :pN I 0=0
      · have hmem:I∈noSeeds :=Finset.mem_filter.mpr ⟨hI,ha⟩
        exact Or.inl (bH4 hmem ((hseedImage I hmem).2.2 _ _ hon))
      · have hpos :=zOl ha
        by_cases hy :zq4 ((zVv I).comp F7)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨I,Finset.mem_filter.mpr ⟨hI,hpos,hy⟩,hon⟩))))
        · exact Or.inr (Or.inl (Finset.mem_biUnion.mpr
            ⟨I,Finset.mem_filter.mpr ⟨hI,hpos,hy⟩,
              Finset.mem_image.mpr ⟨γ,Finset.mem_filter.mpr ⟨hγ,hon⟩,rfl⟩⟩))
theorem proof :P6_7_7.c1 := by
  intro b u del M Γ F sched P Q hP hQ hnc hPc hQc A B hrows T8 hlater
  obtain ⟨a⟩:=strip hP hPc A
  by_cases hempty :b.row.RU.isEmpty=true
  · obtain ⟨tail⟩:=strip hQ hQc B
    obtain ⟨C⟩:=gNf sched hempty F hnc a tail hrows
    exact finish sched C
  · obtain ⟨C⟩:=eo2 (B:=B) sched hempty F hQ hnc hQc a hrows T8 hlater
    exact finish sched C
end
end qBgaZma
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qkV36ld
noncomputable section
open Polynomial
open P6 (K p)
open P5_7 (FarBand InFar farAgreement)
open P5_7_5 (wX ash sheetCut alO lossFee le_ceil_toNat)
open q8ADoQd (curveUnit_nonneg curveUnit_mono)
open P6_7_7 (I0 aHl)
open cu (aZ qD)
open gT (Ambient kM bbt aSf)
open pI (acW by6)
open YY (xg Si by9 aef a9E)
open DQ (Ag)
open axI (c7Q)
open private cag c2p c0U ddj b1I diE from ProximityPrize.SubmissionLower.G
open private ePj co9 from ProximityPrize.SubmissionLower.ZfDhrOb
open private OF OF.mk ceY aaM q8ADoQd.rho small_hi gAN rate_le from ProximityPrize.SubmissionLower.Z2oJVua
open scoped BigOperators Classical
private theorem small_sheet_count {b:FarBand} {h u del} (M:P1.FJ h u del) {Γ}
    (F:P1.bje farAgreement M Γ) (hband:InFar b M.iF) (hq:sheetCut b≠0)
    (T:Finset K) (hT:T⊆Γ) (J:znc kM) (g H :ℕ)
    (hg:0<g) (hgp:g<p) (hcurve :bbt J g H)
    (hmarks : ∀ γ∈T,aSf J (M.label γ) (F.scalar γ)) :
    (T.card:ℚ)≤alO b.row.hi g*H+g:= by
  have hlabel :Set.InjOn M.label (T:Set K) := fun _ _ _ _ h=>sub_left_inj.mp h
  obtain ⟨U,hU,hexc,n,⟨A⟩⟩:=c7Q T M.label F.scalar J g H hg hgp hcurve hlabel hmarks
  let d:=wX b.row.hi
  have hw:OF M.word U F.scalar d:= by
    refine OF.mk (F.distinct.mono (hU.trans hT)) ?_ ?_
    · intro γ hγ
      rcases (F.mark γ (hT (hU hγ))).aic with hz | hm
      · simp [hz]
      · have hd: ((F.scalar γ).natDegree :ℤ)≤(d:ℤ) := by
          change ((F.scalar γ).natDegree :ℤ)≤131071+M.iF at hm
          dsimp only [d,wX,Nat.cast_add,Nat.cast_ofNat]
          have h:=hband.2
          omega
        exact_mod_cast hd
    · intro γ hγ
      let m:=F.mark γ (hT (hU hγ))
      exact ⟨m.bad.support,m.bad.dw,m.scalar_hits⟩
  have hhi:=small_hi hq
  have hh:d≤135870:= by
    change wX b.row.hi≤135870
    rcases hhi with he | he <;> rw [he] <;> decide
  have hregular :=ceY A hw hg (Nat.le_add_right _ _) hh
  have hgQ: (1 :ℚ)≤g:= by exact_mod_cast hg
  have hexcQ: ((T \ U).card:ℚ)≤(Ag g:ℚ)*H := by exact_mod_cast hexc
  calc
    (T.card:ℚ)=((T \ U).card:ℚ)+(U.card:ℚ) := by
      exact_mod_cast (Finset.card_sdiff_add_card_eq_card hU).symm
    _≤(Ag g:ℚ)*H+((2*aaM*d*(Ag g:ℚ)+q8ADoQd.rho d)*H+1) :=
      add_le_add hexcQ hregular
    _=((1+2*aaM*d)*(2*(g:ℚ) - 1)+q8ADoQd.rho d)*H+1 := by
      rw [gAN hg]
      ring
    _≤_:=add_le_add (mul_le_mul_of_nonneg_right (rate_le hhi hg) (zqJ H)) hgQ
private theorem cZQ {h u del} {M:P1.FJ h u del} {Γ} (F:P1.bje farAgreement M Γ)
    {I:znc Ambient} {f :aZ} (hf :xg I=Ideal.span {f}) :
    ∀ z∈(Γ.filter (I0 F I)).image M.label,qD z f=0:= by
  intro z hz
  obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hz
  apply c2p (Finset.mem_filter.mp hγ).2
  rw [hf]
  exact Ideal.mem_span_singleton_self f
private theorem dhW {h u del} (M:P1.FJ h u del) (T:Finset K) :
    (T.image M.label).card=T.card :=
  Finset.card_image_of_injective _ (fun _ _ hab=>sub_left_inj.mp hab)
private theorem cKO {h u del} {M:P1.FJ h u del} {Γ} (F:P1.bje farAgreement M Γ)
    {I:znc Ambient} {f :aZ} (hf :f≠0) (he :xg I=Ideal.span {f})
    (hp:f.totalDegree<p) : (Γ.filter (I0 F I)).card≤(p+1)*f.totalDegree := by
  have h:=ddj f hf hp ((Γ.filter (I0 F I)).image M.label) (cZQ F he)
  rwa [dhW] at h
private theorem seed_le_cost (C:acW) {I:znc Ambient} (hI:I∈C.qv) :
    aef I≤C.cost 0 :=
  zfK (fun _ _=>Nat.zero_le _) hI
private theorem direct_cover {h u del} {M:P1.FJ h u del} {Γ} (F:P1.bje farAgreement M Γ)
    (C:acW) (hp:C.cost 0<p) :
    ((aHl F C).card:ℚ)≤((p+1 :ℕ) :ℚ)*(C.cost 0:ℚ) := by
  have hcount (I:znc Ambient) (hI:I∈C.qv) :
      (Γ.filter (I0 F I)).card≤(p+1)*aef I:= by
    obtain ⟨f,hf,he,_,hd⟩:=GK.proof I (co9 (C.geometric I hI))
    exact (cKO F hf.ne_zero he (hd.trans_lt ((seed_le_cost C hI).trans_lt hp))).trans
      (Nat.mul_le_mul_left _ hd)
  have h: (aHl F C).card≤(p+1)*C.cost 0:= calc
    _ ≤ ∑ I∈C.qv,(Γ.filter (I0 F I)).card:=z1B
    _ ≤ ∑ I∈C.qv,(p+1)*aef I:=zQk hcount
    _ = _:=Finset.mul_sum .. |>.symm
  exact_mod_cast h
private abbrev graphUnit :ℚ:=((p+1 :ℕ) :ℚ)
private abbrev seedRate (b:FarBand) :ℚ:=max (ash b) (graphUnit/(sheetCut b+1 :ℕ))
private theorem large_sheet_rate (b:FarBand) {g:ℕ} (hg:sheetCut b<g) :
    graphUnit≤ seedRate b*(g:ℚ) := by
  let v :ℚ:=((sheetCut b+1 :ℕ) :ℚ)
  have hv :0<v :=Nat.cast_pos.mpr (Nat.succ_pos _)
  have hvg:v≤(g:ℚ) := by
    change ((sheetCut b+1 :ℕ) :ℚ)≤(g:ℚ)
    exact_mod_cast Nat.succ_le_of_lt hg
  calc
    graphUnit=graphUnit/v*v :=(div_mul_cancel₀ _ hv.ne').symm
    _≤graphUnit/v*(g:ℚ) :=mul_le_mul_of_nonneg_left hvg (by positivity)
    _≤_:=mul_le_mul_of_nonneg_right (le_max_right _ _) (zqJ _)
private theorem priced_component {b h u del} {M:P1.FJ h u del} {Γ}
    (F:P1.bje farAgreement M Γ) (hw:InFar b M.iF) (hq:sheetCut b≠0)
    {I:znc Ambient} (geom:by6 I)
    (hD: (aef I:ℚ)≤ash b) (hp:aef I<p) :
    ((Γ.filter (I0 F I)).card:ℚ) ≤
      seedRate b*aef I+alO b.row.hi (sheetCut b)*a9E I+aef I:= by
  let T:=Γ.filter (I0 F I)
  have ha :0≤ seedRate b:=(le_trans (zqJ (α:=ℚ) (aef I)) hD).trans (le_max_left _ _)
  have hr :=curveUnit_nonneg b.row.hi (zOl hq)
  have seed_only (h: (T.card:ℚ)≤ seedRate b*aef I) :
      (T.card:ℚ)≤ seedRate b*aef I +
        alO b.row.hi (sheetCut b)*a9E I+aef I :=
    h.trans ((le_add_of_nonneg_right (mul_nonneg hr (zqJ _))).trans
      (le_add_of_nonneg_right (zqJ _)))
  obtain ⟨f,hf,he,hpos,hd⟩:=GK.proof I (co9 geom)
  by_cases hconst:by9 (xg I)
  · obtain ⟨Q,hQ,heQ⟩:=hconst
    have hdeg:=b1I f hf.ne_zero Q (he.symm.trans heQ)
    obtain ⟨g,hg,hroot,hgD⟩:=ePj I Q (co9 geom) geom.2.2.2.2 hQ heQ
    have hgcap:g≤aef I:=(Nat.le_mul_of_pos_left g (hdeg ▸ hpos)).trans hgD
    by_cases hgq:g≤ sheetCut b
    · have ht:=small_sheet_count M F hw hq T (zT0 _ _) (Si I) g
        (a9E I) hg (hgcap.trans_lt hp) hroot (fun _ hz=>cag (Finset.mem_filter.mp hz).2)
      have hgcapQ: (g:ℚ)≤aef I:= by exact_mod_cast hgcap
      have hheight:=mul_le_mul_of_nonneg_right (curveUnit_mono b.row.hi hgq)
        (zqJ (α:=ℚ) (a9E I))
      exact ht.trans (add_le_add (hheight.trans
        (le_add_of_nonneg_left (mul_nonneg ha (zqJ _)))) hgcapQ)
    · have hc:=cKO F hf.ne_zero he (hd.trans_lt hp)
      rw [hdeg] at hc
      have hcQ: (T.card:ℚ)≤graphUnit*(Q.totalDegree :ℚ) := by exact_mod_cast hc
      have hgDQ: (Q.totalDegree :ℚ)*g≤aef I:= by exact_mod_cast hgD
      apply seed_only
      calc
        _≤graphUnit*(Q.totalDegree :ℚ) :=hcQ
        _≤ seedRate b*g*(Q.totalDegree :ℚ) :=
          mul_le_mul_of_nonneg_right (large_sheet_rate b (lt_of_not_ge hgq)) (zqJ _)
        _=seedRate b*((Q.totalDegree :ℚ)*g) := by ring
        _≤_:=mul_le_mul_of_nonneg_left hgDQ ha
  · have hc:=c0U p f hf (he ▸ hconst) (T.image M.label) (cZQ F he)
    rw [dhW] at hc
    have hcQ: (T.card:ℚ)≤(f.totalDegree :ℚ)^2 := by exact_mod_cast hc
    have hdQ: (f.totalDegree :ℚ)≤aef I:= by exact_mod_cast hd
    apply seed_only
    exact hcQ.trans (by
      rw [pow_two]
      exact mul_le_mul (hdQ.trans (hD.trans (le_max_left _ _))) hdQ (zqJ _) ha)
private theorem discounted_cover {b h u del} {M:P1.FJ h u del} {Γ}
    (F:P1.bje farAgreement M Γ) (hw:InFar b M.iF) (hq:sheetCut b≠0)
    (C:acW) (hD: (C.cost 0:ℚ)≤ash b) (hp:C.cost 0<p) :
    ((aHl F C).card:ℚ) ≤
      seedRate b*(C.cost 0:ℚ)+alO b.row.hi (sheetCut b)*(C.cost 1 :ℚ)+C.cost 0:= by
  have hsum : ∑ I∈C.qv,aef I=C.cost 0:=rfl
  have hsumH : ∑ I∈C.qv,a9E I=C.cost 1 :=rfl
  calc
    _ ≤ ∑ I∈C.qv,((Γ.filter (I0 F I)).card:ℚ) :=diE _ _
    _ ≤ ∑ I∈C.qv,(seedRate b*aef I +
        alO b.row.hi (sheetCut b)*a9E I+aef I) := by
      apply zQk
      intro I hI
      have hn:=seed_le_cost C hI
      have hQ: (aef I:ℚ)≤C.cost 0:= by exact_mod_cast hn
      exact priced_component F hw hq (C.geometric I hI) (hQ.trans hD) (hn.trans_lt hp)
    _ = _:= by simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Nat.cast_sum,hsum,hsumH]
theorem proof :P6_7_7.c3:= by
  intro b u del M Γ F hw hp C hD hH
  have hp' : C.cost 0<p:= by exact_mod_cast hD.trans_lt hp
  by_cases hq:sheetCut b=0
  · have h:=(direct_cover F C hp').trans (mul_le_mul_of_nonneg_left hD (by positivity))
    dsimp only [lossFee]
    rw [ite_eq_left hq]
    exact_mod_cast h.trans (le_ceil_toNat _)
  · have ha :0≤ seedRate b:=((zqJ (α:=ℚ) (C.cost 0)).trans hD).trans (le_max_left _ _)
    have hr :=curveUnit_nonneg b.row.hi (zOl hq)
    have h:=(discounted_cover F hw hq C hD hp').trans (add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hD ha) (mul_le_mul_of_nonneg_left hH hr)) hD)
    dsimp only [lossFee]
    rw [ite_eq_right hq]
    exact_mod_cast h.trans (le_ceil_toNat _)
end
end qkV36ld
end
