import ProximityPrize.SubmissionLower.Zmp13Oc
import ProximityPrize.SubmissionLower.Zf6e2ca
import ProximityPrize.SubmissionLower.ZE36Kga
import ProximityPrize.SubmissionLower.Zn9MhWd
import ProximityPrize.SubmissionLower.Z1zOXFd
import ProximityPrize.SubmissionLower.ZJLBXgd
import ProximityPrize.SubmissionLower.ZPuXYRc
import ProximityPrize.SubmissionLower.ZSyXMse
import ProximityPrize.SubmissionLower.ZrHwqOb
import ProximityPrize.SubmissionLower.ZqY5s9b
import ProximityPrize.SubmissionLower.Z7r9bnb
import ProximityPrize.SubmissionLower.Z8IF1id
import ProximityPrize.SubmissionLower.Z67mtTa
import ProximityPrize.SubmissionLower.Z3phRqa
import ProximityPrize.SubmissionLower.Z4IfEsd
import ProximityPrize.SubmissionLower.ZnTmQ9b
import ProximityPrize.SubmissionLower.ZAZ7Tec
import ProximityPrize.SubmissionLower.Z1qPXJc
import ProximityPrize.SubmissionLower.ZVUr7Ra
import ProximityPrize.SubmissionLower.Zr1PeAc
import ProximityPrize.SubmissionLower.ZxKiVod
set_option Elab.async false
open _root_ renaming Finset → zJe, Finset.card_biUnion_le → z1B, Finset.card_union_le → z2s, Finset.filter_subset → zT0, Finset.range → z4x, Finset.sum_le_sum → zQk, Function.Injective → zq4, Ideal → znc, Ideal.Quotient.mk → zVv, Nat.add_le_add → z9f, Nat.add_le_add_left → z3b, Nat.cast_le → z9h, Nat.cast_nonneg → zqJ, Nat.le_add_right → z8K, Nat.le_of_lt_succ → zeh, Nat.mul_le_mul_left → zBI, PowerSeries.C → zMG
set_option maxHeartbeats 1500000
section
set_option autoImplicit true
namespace qQNoJ5c
noncomputable section

open P5_7 (midAgreement)
open qAxtVye (wX gap alO)
open DQ (Ag)
open axI (c7Q)
open Finset Polynomial
open P5_7 (Qn)
open private OF OF.mk ceY qTOdRca.rho aaM gAN from ProximityPrize.SubmissionLower.Zf6e2ca
open private band_bounds from ProximityPrize.SubmissionLower.Zmp13Oc
theorem persistent_tariff {b cap u del} {M:P1.FJ cap u del} {Γ}
    (F:P1.bje midAgreement M Γ) (hband:Qn b.jX.lo b.jX.hi M.iF) :
    aKd b M F:= by
  intro T hT J g H hg hgLimit hcurve _hseed hmarks
  obtain ⟨U,hU,hexc,n,⟨A⟩⟩:=c7Q T M.label F.scalar J g H hg
    hgLimit hcurve (fun _ _ _ _ h=>sub_left_inj.mp h) hmarks
  let d:=wX b
  have hw:OF M.word U F.scalar d:= by
    refine OF.mk (F.distinct.mono (hU.trans hT)) ?_ ?_
    · intro γ hγ
      have hi:=(P5_7_3.aRe hband).2.trans (band_bounds b).1
      exact (P6_7.aic F (hT (hU hγ))).trans (z3b hi _)
    · intro γ hγ
      let m:=F.mark γ (hT (hU hγ))
      exact ⟨m.bad.support,m.bad.dw,m.scalar_hits⟩
  have hlo:131071≤d:=z8K _ _
  have hhi:d≤135070 :=
    z3b (band_bounds b).2 _
  have hregular :=ceY A hw hg hlo hhi
  have hgQ: (1 :ℚ)≤g:= by exact_mod_cast hg
  have hexcQ: ((T \ U).card:ℚ)≤(Ag g:ℚ)*H := by exact_mod_cast hexc
  calc
    (T.card:ℚ)=((T \ U).card:ℚ)+(U.card:ℚ) := by
      exact_mod_cast (card_sdiff_add_card_eq_card hU).symm
    _≤(Ag g:ℚ)*H +
        ((2*aaM*d*(Ag g:ℚ)+qTOdRca.rho d)*H+1) :=
      add_le_add hexcQ hregular
    _≤(Ag g:ℚ)*H +
        ((2*aaM*d*(Ag g:ℚ)+qTOdRca.rho d)*H+g) :=
      add_le_add le_rfl (add_le_add le_rfl hgQ)
    _=alO b g*H+g:= by
      rw [gAN hg]
      unfold alO gap qTOdRca.rho
      dsimp only [d]
      ring
end
end qQNoJ5c
end
section
set_option autoImplicit true
namespace qQNoJ5c
noncomputable section
open Finset Polynomial
open P5 (K blockLength)
open P5_7 (midAgreement)

open qAxtVye (wX au1)
open baX (mix)
open aF0 (BJ YM)
open private OF OF.mk OF.distinct from ProximityPrize.SubmissionLower.ZogIzOe
open private cSy from ProximityPrize.SubmissionLower.Z6ykYva
open private dmf ePE arV aPh c3W from ProximityPrize.SubmissionLower.ZdSQxye
private abbrev errors :ℕ:=blockLength - midAgreement
open P5_7 (Qn)
open qAxtVye (aBh)
open gT (tK FW)
open pI (abM)
open private eK0 band_bounds from ProximityPrize.SubmissionLower.Zmp13Oc
theorem fixed_tariff {b cap u del} {M:P1.FJ cap u del} {Γ}
    (F:P1.bje midAgreement M Γ) (hband:Qn b.jX.lo b.jX.hi M.iF)
    {B J:ℕ} (guard :aBh B J) {G:tK} (hG:abM G B J)
    {T:zJe K} (hT:T⊆Γ) (hroot : ∀ γ∈T,FW G (F.scalar γ)=0) :
    T.card≤au1 b B J:= by
  classical
  let d:=wX b
  have hdl:131071≤d:=z8K _ _
  have hdu:d≤135070:=z3b (band_bounds b).2 131071
  have hd:d< midAgreement:=hdu.trans_lt (by decide)
  have hw:OF M.word T F.scalar d:= by
    refine OF.mk (F.distinct.mono hT) ?_ ?_
    · intro γ hγ
      have hi:=(P5_7_3.aRe hband).2.trans (band_bounds b).1
      exact (P6_7.aic F (hT hγ)).trans (z3b hi _)
    · intro γ hγ
      let mark :=F.mark γ (hT hγ)
      exact ⟨mark.bad.support,mark.bad.dw,mark.scalar_hits⟩
  let q:=midAgreement - d
  let a :=BJ d B
  let v :=YM d B J
  let β:ℚ:=(errors :ℚ)/q
  let m:=(B-J)*v+J*a
  have hv :v≤a :=min_le_left _ _
  have hβ:0≤β:= by dsimp only [β]; positivity
  have hq:0<q:=Nat.sub_pos_of_lt hd
  have hqR: (0:ℚ)<(q:ℚ) := by exact_mod_cast hq
  unfold au1
  apply le_min
  · have h:=cSy (OF.distinct hw) guard G hG hroot (β*a) (β*v) (by positivity)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hv) hβ) (fun U hU f hf hp hB hJ hreg=> by
        have hc:=ePE (dmf hw hU) (by omega) hd guard.jpos f hf hp hB hJ hreg
        refine hc.trans_eq ?_
        change β *mix f.totalDegree (f.degreeOf 1) a v+1= _
        unfold mix
        ring)
    have he :mix B J (β*a) (β*v)=β *m:= by unfold mix m; push_cast; ring
    rw [he] at h
    let num :=errors*m
    let gX:=(num+(q-1))/q
    have hr :=Nat.mod_add_div (num+(q-1)) q
    have hlt:=Nat.mod_lt (num+(q-1)) hq
    have hn:num≤q*gX:= by dsimp only [gX]; omega
    have hpay :β *m≤(gX:ℚ) := by
      dsimp only [β]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hqR).mpr
      rw [mul_comm (gX:ℚ)]
      exact_mod_cast hn
    change T.card≤gX+B^2
    have hfinal: (T.card:ℚ)≤(gX:ℚ)+(B^2 :ℕ) :=
      h.trans (add_le_add hpay le_rfl)
    exact_mod_cast hfinal
  · let ap:=arV d B
    let vp:=aPh d B J
    have ha :0≤ap:=c3W d B
    have hvp:0≤vp:=le_min ha (by positivity)
    have h:=cSy (OF.distinct hw) guard G hG hroot ap vp hvp (min_le_left _ _)
      (fun U hU=>eK0 (dmf hw hU) hdl hdu guard.jpos)
    let r :=mix B J ap vp
    have hceil:r≤(r.ceil.toNat :ℕ) := by
      have hz :r.ceil≤(r.ceil.toNat :ℤ) :=Int.self_le_toNat _
      have hcast: (r.ceil:ℚ)≤(r.ceil.toNat :ℚ) := by exact_mod_cast hz
      exact Rat.le_ceil.trans hcast
    change T.card≤ r.ceil.toNat+B^2
    have hfinal: (T.card:ℚ)≤(r.ceil.toNat :ℚ)+(B^2 :ℕ) :=
      h.trans (add_le_add hceil le_rfl)
    exact_mod_cast hfinal
end
end qQNoJ5c
end
section
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
namespace qQNoJ5c
noncomputable section
open P5 (p)
open P5_7 (midAgreement)
open qAxtVye (nV RU BC aqE)
open akZ (aB5 weightedDegree cVg strip)
open cu gT pI YX XY Polynomial
open qQ (aeH VN a4N bH5 bH6 bH4)
open scoped BigOperators Classical
open private eo1 from ProximityPrize.SubmissionLower.Z1zOXFd
open private ddo from ProximityPrize.SubmissionLower.CR
private theorem finish {cap u del} {M:P1.FJ cap u del} {Γ} {F:P1.bje midAgreement M Γ}
    {b:P5_7_3.fO} {G H :tK} (sched:aqE b) {S:zJe (znc Ambient)}
    (geom:aB5 S) (fits :dM S (BC b)) (content:aZ)
    (hne :content≠0)
    (hdeg:content.totalDegree≤(nV b 0).free.shape.U + (nV b 0).moving.shape.U)
    (Eh : ∀ γ∈Γ,qD (M.label γ) content=0∨FW G (F.scalar γ)=0 ∨
      ∃ I∈S,I0 F I γ) :
    Nonempty (aAT M F b G H) := by
  classical
  let noSeeds :=S.filter (fun I=>pN I 0=0)
  let constY:=S.filter (fun I=>0<pN I 0 ∧
    ¬ zq4 ((zVv I).comp F7))
  let parents :=S.filter (fun I=>0<pN I 0 ∧
    zq4 ((zVv I).comp F7))
  have hparents (I:znc Ambient) (hi:I∈parents) :xN I:= by
    obtain ⟨hI,ha,hy⟩:=Finset.mem_filter.mp hi
    obtain ⟨hprime,hdim,_,hf⟩:=geom I hI
    have hsmall (k :Fin 4) :pN I k<p :=
      (evL hI k).trans_lt ((fits k).trans_lt (sched.bq6 k))
    exact ⟨hprime,hdim,hf.Kw,hf.jU,hf.kK,hf.Bo,
      ⟨ha,hsmall 0⟩,hsmall 2,hsmall 3,hy⟩
  have fit_subset {T:zJe (znc Ambient)} (hT:T⊆S) :
      dM T (BC b) :=ecA hT fits
  have seed_exists (I:znc Ambient) (hi:I∈noSeeds) :
      ∃ D:VN,D.curve.totalDegree≤pN I 2 ∧
        D.points.card≤pN I 3 ∧ ∀ z R,IZ I z R→D.ow z := by
    obtain ⟨hI,hz⟩:=Finset.mem_filter.mp hi
    obtain ⟨hprime,hdim,_,hf⟩:=geom I hI
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
    exact eHX (geom I hI).1 hy
      (Finset.mem_filter.mp hγ).2 (Finset.mem_filter.mp hδ).2
  refine ⟨{
    parents :=parents
    active :=hparents
    a4E := fun I hi=>(geom I (Finset.mem_filter.mp hi).1).2.2.1
    bst:=ecA (zT0 _ _) fits
    seed :=imageCover
    acI := ?_
    seed_points := ?_
    ordinates :=ordinates
    ordinate_le := ?_
    content:=content
    content_ne :=hne
    content_le :=hdeg
    Eh := ?_ }⟩
  · calc
      _ ≤ ∑ I∈noSeeds,(xg I).curve.totalDegree :=bH5 _ _
      _≤ mass noSeeds 2 :=zQk fun I hi=>(hseedImage I hi).1
      _≤_:=fit_subset (zT0 _ _) 2
  · calc
      _ ≤ ∑ I∈noSeeds,(xg I).points.card:=bH6 _ _
      _≤ mass noSeeds 3:=zQk fun I hi=>(hseedImage I hi).2.1
      _≤_:=fit_subset (zT0 _ _) 3
  · calc
      _ ≤ ∑ I∈constY,(onY I).card:=z1B
      _≤ mass constY 0:=zQk hy
      _≤_:=fit_subset (zT0 _ _) 0
  · intro γ hγ
    rcases Eh γ hγ with h | h | ⟨I,hI,hon⟩
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · by_cases ha :pN I 0=0
      · have hmem:I∈noSeeds :=Finset.mem_filter.mpr ⟨hI,ha⟩
        exact Or.inl (bH4 hmem ((hseedImage I hmem).2.2 _ _ hon))
      · have hpos :=Nat.pos_of_ne_zero ha
        by_cases hy :zq4 ((zVv I).comp F7)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨I,Finset.mem_filter.mpr ⟨hI,hpos,hy⟩,hon⟩))))
        · exact Or.inr (Or.inl (Finset.mem_biUnion.mpr
            ⟨I,Finset.mem_filter.mpr ⟨hI,hpos,hy⟩,
              Finset.mem_image.mpr ⟨γ,Finset.mem_filter.mpr ⟨hγ,hon⟩,rfl⟩⟩))
theorem initial_cover {b cap u del} {M:P1.FJ cap u del} {Γ}
    {F:P1.bje midAgreement M Γ} (sched:aqE b) :
    ∀ P Q:Jet,P≠0→Q≠0→aeH P Q →
    oU P (nV b 0).free.shape→ oU Q (nV b 0).moving.shape →
    ∀ (A:NO P (nV b 0).free.shape) (B:NO Q (nV b 0).moving.shape),
    (∀ γ∈Γ,rD P (M.label γ) (F.scalar γ)=0∧rD Q (M.label γ) (F.scalar γ)=0) →
    ∀ T8:ℕ→Jet,
    (∀ i∈RU b,T8 i≠0∧oU (T8 i) (nV b i).free.shape ∧
      ∀ j a,a≤(nV b i).dI →
        ∀ γ∈Γ,rD (A5 j a (T8 i)) (M.label γ) (F.scalar γ)=0) →
    Nonempty (aAT M F b A.equation B.equation) := by
  intro P Q hP hQ hnc hPc hQc A B hrows T8 hlater
  obtain ⟨a⟩:=strip hP hPc A
  obtain ⟨D,hD,hcap,hroot⟩:=cVg a
  obtain ⟨S,hG,hFit,hC⟩:=eo1 sched hQ hnc hQc T8
    (fun i hi=>⟨(hlater i hi).1,(hlater i hi).2.1⟩)
    (RU b) (fun _ hi=>hi) D _ hD hcap
  refine finish (F:=F) (H :=B.equation) sched hG ?_ a.content a.content_ne
    (a.content_le.trans (z8K _ _)) ?_
  · intro k
    simpa only [BC,weightedDegree,zero_mul,Finset.sum_const_zero,Nat.add_zero]
      using hFit k (fun _=>0)
  · intro γ hγ
    obtain ⟨hp,hq⟩:=hrows γ hγ
    rcases a.Eh _ _ hp with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (hC _ _
        (fun i hi j r hr=>(hlater i hi).2.2 j r hr γ hγ) hq (hroot _ _ h)))
end
end qQNoJ5c
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qQNoJ5c
noncomputable section
open P5 (K p)
open P5_7 (midAgreement Qn)
open P5_7_3 (Pairs)
open P6_7_5 (Source)
open qAxtVye (Process passes Fo aHp SS a5z ash cb1 V8 bDZ HorizontalBand aSz nextIndex FP XM)
open private kG enb from ProximityPrize.SubmissionLower.ZK15T2b
open TD (J2 bfw a3x cK6 bBx cSF)
open cu (vP Jet rD)
open gT (Ambient iJ)
open pI (acW oU)
open scoped Classical BigOperators
structure dmU {b cap u del} {M:P1.FJ cap u del} {Γ}
    (F:P1.bje midAgreement M Γ) {rows :vP}
    {pairs :Pairs b M.iF.toNat rows} (R:Process pairs) (pointFee lossFee :ℕ) where
  loss :zJe K
  point :zJe K
  bsg:loss.card≤lossFee
  point_le :point.card≤pointFee
  Eh : ∀ i≤Fo b,∀ γ∈Γ,∀ I∈R.Hj i,
    I0 F I γ→γ∈point∨γ∈loss
private theorem ePu {b cap u del} {M:P1.FJ cap u del} {Γ}
    {F:P1.bje midAgreement M Γ} {rows :vP} {pairs :Pairs b M.iF.toNat rows}
    (R:Process pairs) (src :Source b M F rows) (i:ℕ) :
    ∃ C:acW,(∀ bw,(C.cost bw:ℚ)≤FP (SS b bw i) (J2 (R.Hj i))) ∧
      ∀ γ∈Γ,(∃ I∈R.Hj i,I0 F I γ) →
        γ∈C.direct ∨ ∃ I∈C.qv,I0 F I γ:= by
  have geom (I:znc Ambient) (hI:I∈R.Hj i) :=
    (R.DN I (R.a4R i (Finset.mem_sdiff.mp hI).1)).1
  have hj: (aHp b i).J≤(aHp b i).B:= by
    by_cases hi:i<Fo b
    · rw [aHp,ite_eq_left hi]
      exact Nat.le_add_left _ _
    · rw [aHp,ite_eq_right hi]
      exact R.sched.bxE.ode.jb
  have an1 (I:znc Ambient) (hI:I∈R.Hj i) :
      ∃ P:Jet,oU P (aHp b i)∧iJ P∉I ∧
        ∀ γ∈Γ,I0 F I γ→ rD P (M.label γ) (F.scalar γ)=0:= by
    obtain ⟨hprev,hlost⟩:=Finset.mem_sdiff.mp hI
    have hf : ¬ passes pairs i I:= fun hp=>hlost (Finset.mem_filter.mpr ⟨hprev,hp⟩)
    by_cases hi:i<Fo b
    · rw [aHp,ite_eq_left hi]
      exact d59 src R.sched pairs (nextIndex i hi) (by simpa only [passes,dite_eq_left hi] using hf)
    · rw [aHp,ite_eq_right hi]
      obtain ⟨P,hP,hproper,hzero⟩:=b2N src (Or.inl rfl) R.sched.bxE.pos
        (by simpa only [passes,dite_eq_right hi] using hf)
      exact ⟨P,hP,hproper,fun γ hγ _=>hzero γ hγ⟩
  obtain ⟨C,hC,hcover⟩:=dN1 (R.Hj i) (aHp b i) hj geom an1
  refine ⟨C,fun bw => ?_,hcover⟩
  rw [← kG]
  exact (z9h (α:=ℚ)).mpr (hC bw)
theorem d6a {b cap u del} {M:P1.FJ cap u del} {Γ} {F:P1.bje midAgreement M Γ}
    {rows :vP} {pairs :Pairs b M.iF.toNat rows} (R:Process pairs)
    (src :Source b M F rows) (hw:Qn b.jX.lo b.jX.hi M.iF)
    (uq:aKd b M F) (gp4 :HorizontalBand b→HorizontalTariff b M F)
    (seed_small:ash b<(p:ℚ)) {a h:ℕ→ℚ} {point loss :ℕ}
    (rate : ∀ i≤Fo b,aSz b (bDZ b i) (a i) (h i))
    (points_le :cb1 b≤(point :ℚ))
    (bsg:XM (Fo b+1) (a5z b a h) (V8 b)+ash b≤(loss :ℚ)) :
    Nonempty (dmU F R point loss) := by
  let n:=Fo b+1
  choose C hcost hcover using ePu R src
  let points :=(z4x n).biUnion fun i=>(C i).direct
  let Hj:=(z4x n).biUnion fun i=>aHl F (C i)
  have next : ∀ i<n,R.Bp (i+1)⊆R.Bp i:= fun i _=>R.eEO i
  have fail : ∀ i<n,R.Hj i⊆R.Bp i \ R.Bp (i+1) := fun _ _=>le_rfl
  have caps : ∀ i<n,∀ k,J2 (R.Bp i) k≤V8 b i k :=
    fun _ hi=>cD4 R src hw (zeh hi)
  have sumD: (∑ i∈z4x n,((C i).cost 0:ℚ))≤ash b :=
    (zQk fun i _=>hcost i 0).trans
      (bBx n (SS b 0) (V8 b) R.Bp R.Hj next fail caps)
  have points_paid : (points.card:ℚ)≤point := by
    have flat : ∀ i<n,∀ k,J2 (R.Bp i) k≤V8 b 0 k :=
      fun i hi k=>(caps i hi k).trans (enb b i k)
    calc
      _ ≤ ∑ i∈z4x n,((C i).cost 2 :ℚ) := by
        exact_mod_cast (z1B :points.card ≤
          ∑ i∈z4x n,(C i).direct.card)
      _ ≤ ∑ i∈z4x n,FP (SS b 2 i) (J2 (R.Hj i)) :=
        zQk fun i _=>hcost i 2
      _≤XM n (SS b 2) (fun _=>V8 b 0) :=
        bBx n (SS b 2) (fun _=>V8 b 0) R.Bp R.Hj next fail flat
      _=cb1 b:=cSF _ _ _
      _≤_:=points_le
  have per_bin (i:ℕ) (hi:i∈z4x n) :
      ((aHl F (C i)).card:ℚ) ≤
        FP (a5z b a h i) (J2 (R.Hj i))+(C i).cost 0:= by
    have hi' := Finset.mem_range.mp hi
    have hr :=rate i (zeh hi')
    have hd: ((C i).cost 0:ℚ)≤ash b :=
      (Finset.single_le_sum (fun j _=>zqJ (α:=ℚ) ((C j).cost 0)) hi).trans sumD
    have hloc: (C i).cost 0≤FP (SS b 0 i) (V8 b i) :=
      (hcost i 0).trans (a3x (fun _=>zqJ _)
        (fun k=>(bfw (Finset.sdiff_subset :R.Hj i⊆R.Bp i) k).trans (caps i hi' k)))
    have hprice :=fTz F uq gp4 hr (C i) (le_min hd hloc)
      ((Nat.cast_lt (α:=ℚ)).mp (hd.trans_lt seed_small))
    calc
      _≤a i*((C i).cost 0:ℚ)+h i*((C i).cost 1 :ℚ)+(C i).cost 0:=hprice
      _≤a i*FP (SS b 0 i) (J2 (R.Hj i)) +
          h i*FP (SS b 1 i) (J2 (R.Hj i))+(C i).cost 0 :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hcost i 0) hr.nonneg)
          (mul_le_mul_of_nonneg_left (hcost i 1) hr.height)) le_rfl
      _ = _:= by rw [cK6]; rfl
  have loss_paid : (Hj.card:ℚ)≤loss := by
    calc
      _ ≤ ∑ i∈z4x n,((aHl F (C i)).card:ℚ) := by
        exact_mod_cast (z1B :Hj.card ≤
          ∑ i∈z4x n,(aHl F (C i)).card)
      _ ≤ ∑ i∈z4x n,(FP (a5z b a h i) (J2 (R.Hj i)) +
          (C i).cost 0) :=zQk per_bin
      _≤XM n (a5z b a h) (V8 b)+ash b:= by
        rw [Finset.sum_add_distrib]
        exact add_le_add (bBx n (a5z b a h) (V8 b) R.Bp R.Hj next fail caps) sumD
      _≤_:=bsg
  refine ⟨⟨Hj,points,(z9h (α:=ℚ)).mp loss_paid,
    (z9h (α:=ℚ)).mp points_paid,?_⟩⟩
  intro i hi γ hγ I hI hm
  have hr :=Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
  rcases hcover i γ hγ ⟨I,hI,hm⟩ with hd | ⟨J,hJ,hj⟩
  · exact Or.inl (Finset.mem_biUnion.mpr ⟨i,hr,hd⟩)
  · exact Or.inr (Finset.mem_biUnion.mpr ⟨i,hr,ez0 hγ hJ hj⟩)
end
end qQNoJ5c
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
namespace qQNoJ5c
noncomputable section
open Polynomial
open P6 (jG K p)
open P5_7 (midAgreement Qn)
open P6_7 (YQ)
open P5_7_3 (fO stages Pairs prefixFee)
open qAxtVye (afa nV arS aU2 a5S Process Fo schedule BC au1 a4f exitFee aBh HorizontalBand lineUnit branchDegree horizontalBase horizontalUnit)
open cu (Jet vP kr qD)
open gT (tK FW kM abX aQ bbt aSf)
open pI (abM)
open qQ (VN zI)
open ac6.Bridge (aQF cbq)
open scoped BigOperators Classical
def c1 :Prop :=
  ∀ (b:fO) u del (M:jG u del) Γ (F:P1.bje midAgreement M Γ),
    HorizontalBand b→Qn b.jX.lo b.jX.hi M.iF→M.shift∉Γ →
    ∀ H,YQ M F H →
    ∀ T⊆Γ,∀ (J:znc kM) d h,0<d→bbt J 1 h →
    Module.finrank aQ (abX J)=d*1→d*1<p →
    (∀ γ∈T,aSf J (M.label γ) (F.scalar γ)) →
    (T.card:ℚ)≤lineUnit b*h+1
def c2 :Prop :=
  ∀ (b:fO) u del (M:jG u del) Γ (F:P1.bje midAgreement M Γ),
    HorizontalBand b→Qn b.jX.lo b.jX.hi M.iF→M.shift∉Γ →
    ∀ H,YQ M F H →
    ∀ T⊆Γ,∀ (J:znc kM) g d h,2≤g→0<d →
    bbt J g h→Module.finrank aQ (abX J)=d*g→d*g<p →
    branchDegree b g<p→(∀ γ∈T,aSf J (M.label γ) (F.scalar γ)) →
    (T.card:ℚ)≤horizontalBase d g*(d*g:ℚ)+horizontalUnit b g*h+g
private def bdZ {cap u del} {M:P1.FJ cap u del} {Γ} (F:P1.bje midAgreement M Γ)
    (G:tK) :zJe K:=Γ.filter fun γ=>FW G (F.scalar γ)=0
private theorem b3r {b cap u del} {M:P1.FJ cap u del} {Γ}
    (F:P1.bje midAgreement M Γ) (hw:Qn b.jX.lo b.jX.hi M.iF) {B J:ℕ}
    (guard :aBh B J) {G:tK} (hcap:abM G B J) :
    (bdZ F G).card≤au1 b B J :=
  fixed_tariff F hw guard hcap (zT0 _ _)
    (fun _ hγ=>(Finset.mem_filter.mp hγ).2)
private def bqg {b cap u del} {M:P1.FJ cap u del} {Γ} (F:P1.bje midAgreement M Γ)
    {rows :vP} {pairs :Pairs b M.iF.toNat rows} (R:Process pairs) :zJe K :=
  Finset.univ.biUnion fun i:afa b =>
    bdZ F (R.fixed i).free.equation∪bdZ F (R.fixed i).moving.equation
private theorem ecR {b cap u del} {M:P1.FJ cap u del} {Γ}
    (F:P1.bje midAgreement M Γ) (hw:Qn b.jX.lo b.jX.hi M.iF)
    {rows :vP} {pairs :Pairs b M.iF.toNat rows} (R:Process pairs) :
    (bqg F R).card≤a4f b:= by
  let jX (i:ℕ) :=
    au1 b (nV b i).free.shape.B (nV b i).free.shape.J +
      au1 b (nV b i).moving.shape.B (nV b i).moving.shape.J
  calc
    _ ≤ ∑ i:afa b,
        (bdZ F (R.fixed i).free.equation∪bdZ F (R.fixed i).moving.equation).card :=
      z1B
    _ ≤ ∑ i:afa b,jX i:= by
      apply zQk
      intro i _
      obtain ⟨ga,gb⟩:=R.sched.aE7 i i.isLt
      exact (z2s _ _).trans (z9f
        (b3r F (b:=b) hw ga.ode (R.fixed i).free.equation_caps)
        (b3r F (b:=b) hw gb.ode (R.fixed i).moving.equation_caps))
    _=a4f b:=Fin.sum_univ_eq_sum_range jX (stages b).length
private theorem mem_fixed {b cap u del} {M:P1.FJ cap u del} {Γ}
    (F:P1.bje midAgreement M Γ) {rows :vP} {pairs :Pairs b M.iF.toNat rows}
    (R:Process pairs) (i:afa b) {γ:K} (hγ:γ∈Γ)
    (hz :FW (R.fixed i).free.equation (F.scalar γ)=0 ∨
      FW (R.fixed i).moving.equation (F.scalar γ)=0) :
    γ∈bqg F R:= by
  refine Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_union.mpr ?_⟩
  exact hz.imp (fun ha=>Finset.mem_filter.mpr ⟨hγ,ha⟩)
    (fun hb=>Finset.mem_filter.mpr ⟨hγ,hb⟩)
private theorem union_le {A B:zJe K} {a b:ℕ} (ha :A.card≤a) (hb:B.card≤b) :
    (A∪B).card≤a+b :=
  (z2s _ _).trans (z9f ha hb)
theorem of_children (h1 :c1) (h2 :c2) :P6_7_5.c1 := by
  classical
  intro b u del M Γ F hw hshift H bY rows src pairs
  let sched:=schedule b
  let zero :afa b:=⟨0,sched.aXU⟩
  let P:=arS pairs zero
  let fixed:=ecO src pairs
  obtain ⟨ga,gb⟩:=sched.aE7 0 sched.aXU
  have hf :=src.shape _ (aU2 zero) _ _ P.free_mem
  have hg:=src.shape _ (a5S zero) _ _ P.moving_mem
  let T8 (i:ℕ) :Jet:=if hi:i<(stages b).length then (arS pairs ⟨i,hi⟩).free else 0
  obtain ⟨initial⟩:=initial_cover (F:=F) sched P.free P.moving P.free_ne P.moving_ne
    P.no_moving hf hg (fixed zero).free (fixed zero).moving (fun γ hγ =>
      ⟨aS3 src (aU2 zero) ga.pos (Nat.sub_le _ _) P.free_mem γ hγ,
        aS3 src (a5S zero) gb.pos (Nat.sub_le _ _) P.moving_mem γ hγ⟩) T8 (by
      intro i hi
      obtain ⟨_,hsize⟩:=sched.brd i hi
      let j:afa b:=⟨i,hsize⟩
      let pair :=arS pairs j
      simp only [T8,dite_eq_left hsize]
      exact ⟨pair.free_ne,src.shape _ (aU2 j) _ _ pair.free_mem,
        fun k a ha=>eo4 src (b:=b) hw (aU2 j) (sched.aE7 i hsize).1
          pair.free_mem k a ha⟩)
  let R:Process pairs :=
    ⟨sched,initial.parents,fixed,fun I hI=>⟨initial.active I hI,initial.a4E I hI⟩,
      initial.bst⟩
  obtain ⟨seed_small,a,h,point,loss,bgt,point_le,bsg,budget⟩:=P5_7_3_3Q5.proof b
  have gp4 (hb:HorizontalBand b) :HorizontalTariff b M F:= by
    intro T hT J g d height _ hd hcurve hlen hp hmarks
    constructor
    · rintro rfl
      exact h1 b u del M Γ F hb hw hshift H bY T hT J d height hd hcurve hlen hp hmarks
    · intro hg hbranch
      exact h2 b u del M Γ F hb hw hshift H bY T hT J g d height hg hd hcurve hlen hp hbranch hmarks
  obtain ⟨arL⟩:=d6a R src hw (persistent_tariff F hw)
    gp4 seed_small bgt point_le bsg
  have rankSub:R.aWI⊆R.parents :=zT0 _ _
  obtain ⟨G,hgcap,hG⟩:=TD.fS7 R.aWI (fun I hI =>
      ⟨(R.DN I (rankSub hI)).1,(Finset.mem_filter.mp hI).2⟩)
    (B:=BC b 2) (J:=BC b 1)
    ((pI.a5I rankSub 1).trans (R.init_mass 1))
    ((pI.a5I rankSub 2).trans (R.init_mass 2))
  let seed :=Γ.filter fun γ=>initial.seed.ow (M.label γ)
  let contents :=Γ.filter fun γ=>qD (M.label γ) initial.content=0
  let ords :=Γ.filter fun γ=>kr (F.scalar γ)∈initial.ordinates
  let rank :=bdZ F G
  have label_inj:zq4 M.label := fun _ _ h=>sub_left_inj.mp h
  have hseed :seed.card≤(p+1)*BC b 2+BC b 3:= by
    have hc:=qQ.aJr (T:=seed) label_inj.injOn initial.seed
      (initial.acI.trans_lt (sched.bq6 2)) (fun _ hγ=>(Finset.mem_filter.mp hγ).2)
    exact hc.trans (z9f (zBI _ initial.acI) initial.seed_points)
  have hcontents :contents.card≤(p+1)*((nV b 0).free.shape.U + (nV b 0).moving.shape.U) := by
    let C:VN :=⟨initial.content,initial.content_ne,∅⟩
    have hc:=qQ.aJr (T:=contents) label_inj.injOn C
      (initial.content_le.trans_lt sched.bDl)
      (fun _ hγ=>Or.inl (Finset.mem_filter.mp hγ).2)
    have hc' : contents.card≤(p+1)*initial.content.totalDegree := by
      simpa only [C,Finset.card_empty,Nat.add_zero] using hc
    exact hc'.trans (zBI _ initial.content_le)
  have hords :ords.card≤BC b 0 :=
    (Finset.card_le_card_of_injOn (fun γ=>kr (F.scalar γ))
      (fun _ hγ=>(Finset.mem_filter.mp hγ).2)
      (fun _ hγ _ hδ h=>F.distinct (Finset.mem_filter.mp hγ).1 (Finset.mem_filter.mp hδ).1
        (qQ.bNe h))).trans initial.ordinate_le
  have hrank :=b3r F (b:=b) hw sched.bK5 hgcap
  have hfixed:=ecR F hw R
  let book :=arL.point∪arL.loss∪seed∪ords∪rank∪bqg F R∪contents
  have hbook :book.card≤prefixFee b:= by
    have hb:=union_le (union_le (union_le (union_le
      (union_le (union_le arL.point_le arL.bsg) hseed) hords) hrank) hfixed) hcontents
    refine hb.trans (le_trans ?_ budget)
    unfold exitFee
    omega
  let toSurface (I : ↥R.final) :zI:=aQF I.1 (R.DN _ (R.a4R _ I.2)).1.prime
  refine ⟨⟨book,hbook,R.final.attach.image toSurface,?_,?_,?_⟩⟩
  · intro q hq
    obtain ⟨I,_,rfl⟩:=Finset.mem_image.mp hq
    have hgeom:=R.DN I.1 (R.a4R _ I.2)
    exact cbq hgeom.1 hgeom.2 (R.kept_clean _ I.2).2
  · intro q hq
    obtain ⟨I,_,rfl⟩:=Finset.mem_image.mp hq
    exact R.terminal I.2
  · intro γ hγ
    by_cases hpaid :γ∈book
    · exact Or.inl hpaid
    right
    have forbid_seed (h:γ∈seed) :False :=hpaid (by simp [book,h])
    have forbid_contents (h:γ∈contents) :False :=hpaid (by simp [book,h])
    have forbid_ords (h:γ∈ords) :False :=hpaid (by simp [book,h])
    have forbid_rank (h:γ∈rank) :False :=hpaid (by simp [book,h])
    have forbid_fixed (h:γ∈bqg F R) :False :=hpaid (by simp [book,h])
    have forbid_loss (h:γ∈arL.point∨γ∈arL.loss) :False :=hpaid (by
      rcases h with h | h <;> simp [book,h])
    rcases initial.Eh γ hγ with hz | ho | hc | ha | hb | ⟨I,hI,hm⟩
    · exact (forbid_seed (Finset.mem_filter.mpr ⟨hγ,hz⟩)).elim
    · exact (forbid_ords (Finset.mem_filter.mpr ⟨hγ,ho⟩)).elim
    · exact (forbid_contents (Finset.mem_filter.mpr ⟨hγ,hc⟩)).elim
    · exact (forbid_fixed (mem_fixed F R zero hγ (Or.inl ha))).elim
    · exact (forbid_fixed (mem_fixed F R zero hγ (Or.inr hb))).elim
    · have hclean:R.Clean I:= fun j =>
        ⟨fun hj=>forbid_fixed (mem_fixed F R j hγ (Or.inl (b3t hm hj))),
          fun hj=>forbid_fixed (mem_fixed F R j hγ (Or.inr (b3t hm hj)))⟩
      have hnotRank :I∉R.aWI:= fun h=>forbid_rank
        (Finset.mem_filter.mpr ⟨hγ,b3t hm (hG I h)⟩)
      have hnotLost : ∀ i≤Fo b,I∉R.Hj i:= fun i hi h =>
        forbid_loss (arL.Eh i hi γ hγ I h hm)
      let J : ↥R.final:=⟨I,R.fXs hI hclean hnotRank hnotLost⟩
      exact ⟨toSurface J,Finset.mem_image_of_mem _ (Finset.mem_attach _ _),eGu _ hm⟩
end
end qQNoJ5c
end
section
set_option autoImplicit true
namespace q77TGPa
theorem proof :q0Nj7Rb.c1 :=qzM5sEd.proof
end q77TGPa
end
section
set_option autoImplicit true
namespace qAMRG7b
open qAxtVye (wX)
open quN7Z4a (OF degree_lt sheet line)
theorem proof :qQNoJ5c.c1 := by
  classical
  intro b u del M Γ F hb hw _ _ _ T hT J d h _ hc hlen _ hm
  obtain ⟨C₀,hC₀,_,⟨S⟩⟩:=sheet (by decide :0<1) hc hlen hm
  let:Fact (Irreducible C₀) :=⟨hC₀⟩
  have hz :Set.InjOn M.label (T:Set P6.K) := fun _ _ _ _ he=>sub_left_inj.mp he
  have hhi:b.jX.hi=b.pricedHi:= by rcases hb with rfl | rfl <;> rfl
  have hdeg:=(P5_7_3.aRe (b:=b) hw).2.trans_eq hhi
  have W:OF T F.scalar M.word (wX b) := by
    refine ⟨F.distinct.mono hT,?_,?_⟩
    · intro γ hγ
      exact (P6_7.aic F (hT hγ)).trans (z3b hdeg _)
    · intro γ hγ
      let m:=F.mark γ (hT hγ)
      exact ⟨m.bad.support,m.bad.dw,m.scalar_hits⟩
  exact line S hz W (degree_lt hb)
end qAMRG7b
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qWEQiwd
noncomputable section
open Polynomial Finset
open P6 (K p)
open cu (L)
open DP (Tj)
open P5_7 (midAgreement Qn)

open qAxtVye (HorizontalBand wX horizontalBase)
open quN7Z4a (OF PoleStarts Z7 Smooth sheet singular_bound physicalWeight
  compressionWidth standardUnit quadraticUnit)
open private variation_count degree_payment high_payment from ProximityPrize.SubmissionLower.ZjobcJd
def c1 :Prop :=quN7Z4a.c1
def c2 :Prop :=quN7Z4a.c2
def c3:Prop :=quN7Z4a.c3
private theorem fixedWord {b cap u del} {M:P1.FJ cap u del} {Γ}
    (F:P1.bje midAgreement M Γ) (hb:HorizontalBand b)
    (hw:Qn b.jX.lo b.jX.hi M.iF) {T:zJe K} (hT:T⊆Γ) :
    OF T F.scalar M.word (wX b) := by
  have hhi:b.jX.hi=b.pricedHi:= by rcases hb with rfl | rfl <;> rfl
  have hw' := hw.2
  rw [hhi] at hw'
  have hdeg:M.iF.toNat≤b.pricedHi:= by omega
  refine ⟨F.distinct.mono hT,fun γ hγ=>(P6_7.aic F (hT hγ)).trans
    (z3b hdeg _),?_⟩
  intro γ hγ
  let m:=F.mark γ (hT hγ)
  exact ⟨m.bad.support,m.bad.dw,m.scalar_hits⟩
private theorem eval_ne {E H :L[X]} {x :L} (h:IsCoprime E H) (hx :H.eval x=0) :
    E.eval x≠0:= by
  intro hf
  obtain ⟨a,b,hab⟩:=h
  have he :=congrArg (fun F:L[X]=>F.eval x) hab
  simp only [eval_add,eval_mul,hf,hx,mul_zero,add_zero,eval_one,zero_ne_one] at he
private theorem poleStarts {b cap u del} {M:P1.FJ cap u del} {Γ}
    (F:P1.bje midAgreement M Γ) (hb:HorizontalBand b)
    (hw:Qn b.jX.lo b.jX.hi M.iF) {T:zJe K} (hT:T⊆Γ)
    {H :L[X]} (hc:P6_7.YQ M F H) :
    Nonempty (PoleStarts T M.label F.scalar) := by
  obtain ⟨D,_,_,hnode,hmarks⟩:=P6_7.bW4 M F H hc
  have hlo:0<b.jX.lo:= by rcases hb with rfl | rfl <;> decide
  have hwpos :0<M.iF.toNat := by
    have hn: (0:ℤ)<b.jX.lo:= by exact_mod_cast hlo
    have :=hw.1
    omega
  have roots (i:Fin 2) : ∃ x,(D.block i).eval x=0:= by
    apply IsAlgClosed.exists_root
    rw [degree_eq_natDegree (D.monic i).ne_zero,D.degree]
    exact_mod_cast hwpos.ne'
  choose x hx using roots
  have hne :x 0≠x 1 := fun h=>eval_ne D.coprime (hx 1) (h ▸ hx 0)
  have hunit (i:Fin 2) :
      (D.offset i).eval (x i)*(D.constant i).eval (x i)≠0:= by
    simpa only [eval_mul] using eval_ne (D.determinant i) (hx i)
  let a (i:Fin 2) :=(D.constant i).eval (x i)
  let b (i:Fin 2) :=(D.slope i).eval (x i)
  let c (i:Fin 2) := -(D.offset i).eval (x i)
  refine ⟨⟨x,?_,?_,a,b,c,fun i=>(mul_ne_zero_iff.mp (hunit i)).2,
    fun i=>neg_ne_zero.mpr (mul_ne_zero_iff.mp (hunit i)).1,?_,?_⟩⟩
  · intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hne h).elim
    · exact (hne h.symm).elim
    · rfl
  · intro i j h
    have hz :=hx i
    rw [h] at hz
    exact hnode i j hz
  · intro γ hγ i
    simpa only [a,b,Tj,eval_add,eval_mul,eval_C] using
      eval_ne ((hmarks γ (hT hγ) i).1) (hx i)
  · intro γ hγ i
    have h:=eval_eq_zero_of_dvd_of_eval_eq_zero ((hmarks γ (hT hγ) i).2) (hx i)
    simp only [Tj,eval_add,eval_mul,eval_C] at h
    dsimp [a,b,c]
    linear_combination h
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :qQNoJ5c.c2 := by
  classical
  intro b u del M Γ F hb hw _ Hblock bY T hT J g d H hg hd hcurve hlen hp hbranch hmarks
  have hgpos :0<g:= by omega
  obtain ⟨C₀,hC₀,hdegree,⟨S⟩⟩:=sheet hgpos hcurve hlen hmarks
  let:Fact (Irreducible C₀) :=⟨hC₀⟩
  have hz :Set.InjOn M.label (T:Set K) := fun _ _ _ _ h=>sub_left_inj.mp h
  have W:=fixedWord F hb hw hT
  by_cases hlow:physicalWeight (wX b) S.root.equation<compressionWidth (wX b) g
  · obtain ⟨starts⟩:=poleStarts F hb hw hT bY
    obtain ⟨P⟩:=h1 b C₀ J T M.label F.scalar M.word g d H S hb hg hdegree hd hp hbranch hlow hz W starts
    let U:=T.filter (fun γ=>Smooth C₀ (Z7 (M.label γ)))
    let V:=T.filter (fun γ => ¬ Smooth C₀ (Z7 (M.label γ)))
    have hU:=variation_count W hb (U:=U) (filter_subset _ _) P
    have he :T \ U=V:= by
      ext γ
      by_cases h:γ∈T <;> simp [U,V,h]
    have hc:T.card=U.card+V.card:= by
      have e :=card_sdiff_add_card_eq_card (filter_subset _ _:U⊆T)
      rw [he,Nat.add_comm] at e
      exact e.symm
    have hdp:=(Nat.le_mul_of_pos_right d hgpos).trans_lt hp
    have hd₀:0<C₀.totalDegree := by rwa [hdegree]
    have hp₀:C₀.totalDegree<p:= by rwa [hdegree]
    have hV:=singular_bound C₀ hC₀ hd₀ hp₀ hz S.onSeed
    rw [hdegree] at hV
    have hV' : (V.card:ℚ)≤(d:ℚ)*(d-1 :ℕ) := by exact_mod_cast hV
    have hsum: (T.card:ℚ)≤horizontalBase d g*(d*g:ℚ)+standardUnit b g*H+g:= by
      have hd' := degree_payment (d:=d) hg
      push_cast at hU
      calc
        _=(U.card:ℚ)+V.card:= by rw [hc,Nat.cast_add]
        _≤_:=add_le_add hU hV'
        _=standardUnit b g*H+((4*g*g*d:ℚ)+(d:ℚ)*(d-1 :ℕ)) :=add_assoc _ _ _
        _≤ standardUnit b g*H+horizontalBase d g*(d*g:ℚ) :=add_le_add le_rfl hd'
        _≤_:= by
          rw [add_comm (standardUnit b g*H)]
          exact le_add_of_nonneg_right (zqJ g)
    change (T.card:ℚ)≤horizontalBase d g*(d*g:ℚ) +
      (if g=2 then min (standardUnit b g) (quadraticUnit b) else standardUnit b g)*H+g
    split_ifs with he
    · subst g
      by_cases huv :standardUnit b 2≤quadraticUnit b
      · rwa [min_eq_left huv]
      · rw [min_eq_right (le_of_not_ge huv)]
        have hq:=h3 b C₀ J T M.label F.scalar M.word d H S hb hdegree hd hp hbranch hlow hz W
        unfold horizontalBase
        have hnon : (0:ℚ)≤(2*(d:ℚ)/3+4*2+8)*(d*2 :ℚ) := by positivity
        linarith only [hq,hnon]
    · exact hsum
  · exact high_payment (h2 b C₀ J T M.label F.scalar M.word g d H S hb hg
      hdegree hd hp (le_of_not_gt hlow) hz W)
end
end qWEQiwd
end
section
set_option autoImplicit true
namespace qqyJ4ma
theorem proof :q0Nj7Rb.c3:=P5_7_2_3Q132.proof
end qqyJ4ma
end
section
set_option autoImplicit true
namespace qhCMeRd
theorem proof :q0Nj7Rb.c7:=qYzmxYc.proof
end qhCMeRd
end
section
set_option autoImplicit true
namespace qbiuGTb
noncomputable section
open Polynomial Finset
open scoped Classical WithZero
open P5 (K)
open cu (L)
open qkgz7gb (PlaneCurve)

open qxPDCsa
open qb0hmCe (CurveModel cLN)
open q1kuFjb


private theorem reduce_coeff {E :Type} [Field E] [Algebra L E]
    (a :E →ₐ[L] LaurentSeries L) (g:E[X]) (j:ℕ) :
    (reduce a g).coeff j=(a (g.coeff j)).coeff 0:= by
  simp only [reduce,expansion_coeff,coeff_C_zero]
private theorem reduce_eval {E :Type} [Field E] [Algebra L E]
    (a :E →ₐ[L] LaurentSeries L) (f :E[X][X])
    (hf : ∀ i j,(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰)
      (a ((f.coeff i).coeff j))≤1) (t:L) :
    reduce a (f.eval (C (algebraMap L E t)))=(cLN a 0 f).eval (C t) := by
  let e :=LaurentSeries.powerSeriesEquivSubring L
  let c:IntSeries :=e (zMG t)
  let g:=Ua a f hf
  have hs : (c:LaurentSeries L)=a (algebraMap L E t) := by
    change ((e (zMG t) :IntSeries) :LaurentSeries L)= _
    rw [LaurentSeries.powerSeriesEquivSubring_coe_apply,a.commutes,
      LaurentSeries.algebraMap_apply,PowerSeries.coe_C]
  have hr :residue c=t:= by
    change PowerSeries.constantCoeff (e.symm (e (zMG t)))=t
    rw [RingEquiv.symm_apply_apply,PowerSeries.constantCoeff_C]
  have hm: (g.eval (C c)).map IntSeries.subtype =
      (f.eval (C (algebraMap L E t))).map a.toRingHom:= by
    change mapRingHom IntSeries.subtype (g.eval (C c)) =
      mapRingHom a.toRingHom (f.eval (C (algebraMap L E t)))
    rw [← eval_map_apply,← eval_map_apply]
    simp only [coe_mapRingHom,map_C]
    change (mapTwice IntSeries.subtype g).eval (C (c:LaurentSeries L)) =
      (mapTwice a.toRingHom f).eval (C (a (algebraMap L E t)))
    rw [hs,map_liftAt]
  have he : (g.eval (C c)).map residue=(cLN a 0 f).eval (C t) := by
    change mapRingHom residue (g.eval (C c))= _
    rw [← eval_map_apply,coe_mapRingHom,map_C,hr]
    change (mapTwice residue g).eval (C t)= _
    rw [mapTwice,coe_mapRingHom,liftAt_reduce]
  rw [← he]
  ext j
  rw [reduce_coeff,coeff_map,fWQ]
  have h:=congrArg (fun p: (LaurentSeries L)[X]=>p.coeff j) hm
  simpa only [coeff_map,Subring.subtype_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using
    congrArg (fun s :LaurentSeries L=>s.coeff 0) h.symm
variable {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
end
end qbiuGTb
end
section
set_option autoImplicit true
namespace qJrpi8b
theorem proof :qCwf1nc.c2 :=
  P5_7_3_5_2.of_children
    (P5_7_3_5_2_1.of_children q5rLXAc.proof qNdtvka.proof qkLfS5c.proof)
    (qziIa4d.of_children qOj34lc.proof qJ69aaa.proof
      (qnyP9Da.of_children q3zqDZc.proof qJQ0Sxd.proof
        qDhaEec.proof)
      qU1uHGd.proof)
    (qrezXJe.of_children
      (qoGY3we.of_children qwQWGra.proof
        (qkjFxXb.of_children q0wio9a.proof qAggnYd.proof)
        (qz2teNe.of_children qlcYNOb.proof qoHmCXd.proof))
      qvghFhc.proof)
    (qxPDCsa.of_children qd4QhDd.proof qU4m8Td.proof qvkfeic.proof
      (qqV3gre.of_children
        (qCtoYwb.of_children qrX9S3b.proof qlbihNe.proof)
        q0n1P7d.proof qklsuQd.proof q4Zbmib.proof)
      (qCe4xzb.of_children qbEWDkb.proof qMWkPHd.proof)
      qC1dA5c.proof qbiuGTb.proof)
end qJrpi8b
end
