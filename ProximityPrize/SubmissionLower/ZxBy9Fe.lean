import ProximityPrize.SubmissionLower.Zc9uAjc
import ProximityPrize.SubmissionLower.Z1G66Gc
import ProximityPrize.SubmissionLower.Z6ykYva
import ProximityPrize.SubmissionLower.ZpYo3sb
set_option Elab.async false
open _root_ renaming Finset → zJe, Finset.card_union_le → z2s, Finset.filter_subset → zT0, Finset.range → z4x, Finset.sum_le_sum → zQk, Nat.add_le_add → z9f, Nat.cast_le → z9h, Nat.le_of_lt_succ → zeh, Nat.mul_le_mul_left → zBI
set_option maxHeartbeats 1500000
section
set_option autoImplicit true
namespace P6_7_7
noncomputable section
open Polynomial
open P6 (K)
open P5_7 (FarBand farAgreement)
open P5_7_5 (nV BC al6)
open cu (FX aZ kr qD)
open gT (Ambient tK IZ FW)
open pI (xN dM acW)
def I0 {h u del} {M:P1.FJ h u del} {Γ}
    (F:P1.bje farAgreement M Γ) (I:Ideal Ambient) (γ:K) :Prop :=
  IZ I (M.label γ) (F.scalar γ)
def aHl {h u del} {M:P1.FJ h u del} {Γ}
    (F:P1.bje farAgreement M Γ) (C:acW) :zJe K:= by
  classical
  exact C.qv.biUnion fun I=>Γ.filter (I0 F I)
structure aAT {h u del} (M:P1.FJ h u del) {Γ} (F:P1.bje farAgreement M Γ)
    (b:FarBand) (freeFixed movingFixed:tK) where
  parents :zJe (Ideal Ambient)
  active : ∀ I∈parents,xN I
  a4E : ∀ I∈parents,I.height=2
  bst:dM parents (BC b)
  seed :qQ.VN
  acI:seed.curve.totalDegree≤BC b 2
  seed_points :seed.points.card≤al6 b
  ordinates :zJe FX
  ordinate_le :ordinates.card≤BC b 0
  content:aZ
  content_ne :content≠0
  content_le :content.totalDegree≤(nV b 0).free.shape.U + (nV b 0).moving.shape.U
  Eh : ∀ γ∈Γ,seed.ow (M.label γ)∨kr (F.scalar γ)∈ordinates ∨
    qD (M.label γ) content=0∨FW freeFixed (F.scalar γ)=0 ∨
    FW movingFixed (F.scalar γ)=0 ∨ ∃ I∈parents,I0 F I γ
end
end P6_7_7
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
namespace P6_7_7
noncomputable section
open Polynomial
open P6 (K p blockLength)
open P6_7 (Source axy)
open P5_7 (Jr InFar farAgreement O2 anM)
open P5_7_5 (am1 afa bQX aU2 a5S arS Process
  nV Fo nextIndex Wx aE6 V8 ar3 agA wX au1)
open cu (vP Jet A5 rD jz)
open gT (Ambient tK aQ FW aNB iJ)
open pI (abM xN dual aaS O9)
open ac2
open ac3
open TD (aBh J2 bfw)
open baX (mix)
open aF0 (BJ YM)
open qUJtx6c (ePE)
open private cDJ ddZ from ProximityPrize.SubmissionLower.ZDyoNob
open private P5_7_5.Process.dha P5_7_5.Process.cWA from ProximityPrize.SubmissionLower.Z1G66Gc
open private cSy from ProximityPrize.SubmissionLower.Z6ykYva
open private degree_guards from ProximityPrize.SubmissionLower.ZEXP3Xa
open scoped BigOperators Classical
theorem aS3 {b h u del} {M:P1.FJ h u del} {Γ} {F:P1.bje farAgreement M Γ}
    {rows :vP} (src :Source b M F rows) {t:P5_7.Bank} (ht:Jr b t)
    (hpos :0<t.shape.m*farAgreement) {P:Jet} {W:ℕ}
    (hW:W≤O2 t.shape) (hP:P∈rows t.shape W) :
    ∀ γ∈Γ,rD P (M.label γ) (F.scalar γ)=0 :=
  src.necessary t ht W (by unfold O2 at hW; omega) P hP
theorem eo4 {b h u del} {M:P1.FJ h u del} {Γ} {F:P1.bje farAgreement M Γ}
    {rows :vP} (src :Source b M F rows) (hw:InFar b M.iF) {t:P5_7.Bank}
    (ht:Jr b t) {r :ℕ} (guard :am1 b.row.hi r t.shape)
    {P:Jet} (hP:P∈rows t.shape (anM M.iF.toNat r t.shape))
    (i:Fin 2) (a :ℕ) (ha :a≤ r) :
    ∀ γ∈Γ,rD (A5 i a P) (M.label γ) (F.scalar γ)=0:= by
  apply aS3 src ht guard.pos _ (src.shift t ht _ _ hP i a)
  exact (Nat.add_le_add_left (zBI _ ha) _).trans (cDJ hw guard)
def ecO {b h u del} {M:P1.FJ h u del} {Γ} {F:P1.bje farAgreement M Γ}
    {rows :vP} (src :Source b M F rows) (pairs :P5_7.Pairs b M.iF.toNat rows)
    (i:afa b) :bQX pairs i :=
  let pair :=arS pairs i
  ⟨Classical.choice (bRI.proof _ _ pair.free_ne
      (src.shape _ (aU2 i) _ _ pair.free_mem)),
    Classical.choice (bRI.proof _ _ pair.moving_ne
      (src.shape _ (a5S i) _ _ pair.moving_mem))⟩
theorem b3t {h u del} {M:P1.FJ h u del} {Γ} {F:P1.bje farAgreement M Γ}
    {I:Ideal Ambient} {G:tK} {γ:K} (hm:I0 F I γ) (hG:aaS G I) :
    gT.FW G (F.scalar γ)=0:= by
  simpa only [pI.d2l] using RingHom.mem_ker.mp (hm hG)
theorem eGu {h u del} {M:P1.FJ h u del} {Γ} {F:P1.bje farAgreement M Γ}
    {I:Ideal Ambient} (hI:I.IsPrime) {γ:K} (hm:I0 F I γ) :
    axy M F (ac6.Bridge.aQF I hI) γ:= by
  intro P hP
  apply RingHom.mem_ker.mpr
  change rD P (M.label γ) (F.scalar γ)=0
  rw [← aNB]
  exact RingHom.mem_ker.mp (hm hP)
private theorem cDK {b h u del} {M:P1.FJ h u del} {Γ} {F:P1.bje farAgreement M Γ}
    {rows :vP} (src :Source b M F rows) (hw:InFar b M.iF)
    {t:P5_7.Bank} (ht:Jr b t) {r :ℕ}
    (guard :am1 b.row.hi r t.shape) (hr :r<p)
    {I:Ideal Ambient} (hactive :xN I) (hv :agA rows t.shape I)
    {P:Jet} (hP:P∈rows t.shape (anM M.iF.toNat r t.shape)) :
    O9 I P (r+1) := by
  classical
  have hn:=src.nested t ht t ht rfl rfl rfl le_rfl
  have hcut:=cDJ hw guard
  by_cases hd:dual I
  · have hc:=ddZ (algebraMap cu.aZ aQ) hn
      (src.shift t ht) hv hcut hP
    rw [← aVL] at hc
    exact dLt hd (cy0.proof I hactive.prime hactive.jet_finite
      hd hactive.jet_lt _ r hr hc)
  · obtain ⟨g,hg,hdeg,he⟩:=aR0.proof I hactive hd
    let _:I.IsPrime :=hactive.prime
    let _: (I.comap qO).IsPrime :=Ideal.IsPrime.comap qO
    let _:CharP cu.FX p:=charP_of_injective_ringHom jz.injective p
    let _:CharP (Tw I) p :=
      charP_of_injective_ringHom ((avd I).comp MvPolynomial.C).injective p
    apply dLB hactive.prime hd
    have hc:=ddZ (avd I) hn (src.shift t ht) hv hcut hP
    change bp3 (I.map (T3 I)) (T3 I (iJ P)) r at hc
    rw [he] at hc ⊢
    exact dXr hg hdeg hr hc
private theorem cYy {b h u del} {M:P1.FJ h u del} {Γ} {F:P1.bje farAgreement M Γ}
    {rows :vP} {pairs :P5_7.Pairs b M.iF.toNat rows} (R:Process pairs)
    (src :Source b M F rows) (hw:InFar b M.iF)
    (i:afa b) (hi:0< i.val) (square :Bool)
    {A:zJe (Ideal Ambient)} (hA:A⊆R.Lc i)
    (hdual:square=true → ∀ I∈A,dual I) (k :Fin 4) :
    J2 A k≤aE6 b i square k := by
  let s :=nV b i
  let pair :=arS pairs i
  obtain ⟨ga,gb⟩:=R.sched.aE7 i i.isLt
  have hr :=R.sched.bN7 _ i.isLt
  have hrpos :=R.sched.bIj (i.val-1) (by unfold Fo; omega)
  have hidx :i.val-1+1=i.val := by omega
  rw [hidx] at hrpos
  exact P5_7_5.cbe s.free.shape s.moving.shape s.dI square pair.free pair.moving
    hrpos hr ga.ode.small gb.ode.small ga.seed_small gb.seed_small ga.ode.jb gb.ode.jb
    pair.free_ne pair.moving_ne
    (src.shape _ (aU2 i) _ _ pair.free_mem)
    (src.shape _ (a5S i) _ _ pair.moving_mem) pair.no_moving
    (R.fixed i).free (R.fixed i).moving A hdual (fun I hI=> by
      obtain ⟨hp,hc,hpass⟩:=Finset.mem_filter.mp (hA hI)
      have hactive :=(R.DN I hp).1
      have htest :=hpass i hi le_rfl
      exact ⟨hactive,htest.2.2,(hc i).1,(hc i).2,
        cDK src hw (aU2 i) ga hr hactive htest.1 pair.free_mem,
        cDK src hw (a5S i) gb hr hactive htest.2.1 pair.moving_mem⟩) k
theorem cD4 {b h u del} {M:P1.FJ h u del} {Γ} {F:P1.bje farAgreement M Γ}
    {rows :vP} {pairs :P5_7.Pairs b M.iF.toNat rows} (R:Process pairs)
    (src :Source b M F rows) (hw:InFar b M.iF)
    {i:ℕ} (hi:i≤Fo b) (k :Fin 4) :J2 (R.Bp i) k≤V8 b i k := by
  induction i with
  | zero =>
    exact (z9h (α:=ℚ)).mpr
      ((pI.a5I ((R.a4R 0).trans (R.bxI 0)) k).trans (R.init_mass k))
  | succ i ih =>
    refine le_min ((bfw (R.cWA (Nat.le_succ i)) k).trans (ih (by omega))) ?_
    let j:=nextIndex i (by omega :i<Fo b)
    exact cYy R src hw j (Nat.succ_pos _) _ (R.a4R (i+1))
      (fun h I hI=>(Finset.mem_filter.mp hI).2 (of_decide_eq_true h)) k
theorem dE4 {b h u del} {M:P1.FJ h u del} {Γ} {F:P1.bje farAgreement M Γ}
    {rows :vP} {pairs :P5_7.Pairs b M.iF.toNat rows} (R:Process pairs)
    (src :Source b M F rows) (hw:InFar b M.iF)
    {i:ℕ} (hi:i≤Fo b) (k :Fin 4) :J2 (R.QV i) k≤V8 b i k := by
  rw [Process.QV,ite_eq_left hi]
  exact cD4 R src hw hi k
theorem c6F {b h u del} {M:P1.FJ h u del} {Γ} {F:P1.bje farAgreement M Γ}
    {rows :vP} {pairs :P5_7.Pairs b M.iF.toNat rows} (R:Process pairs)
    (src :Source b M F rows) (hw:InFar b M.iF)
    (k :Fin 4) :J2 R.aWI k≤ar3 b k := by
  unfold ar3
  by_cases hz :Wx b=0
  · rw [ite_eq_left hz]
    exact (z9h (α:=ℚ)).mpr ((pI.a5I
      ((zT0 _ _:R.aWI⊆R.Lc (Wx b)).trans
        (R.bxI _)) k).trans (R.init_mass k))
  · rw [ite_eq_right hz]
    have hprev :Wx b-1<Wx b:= by omega
    have hsub:R.aWI⊆R.Lc (Wx b) :=zT0 _ _
    have hkeep:R.aWI⊆R.Bp (Wx b-1) := by
      intro I hI
      exact Finset.mem_filter.mpr ⟨R.dha hprev.le (hsub hI),fun h=>(hprev.not_ge h).elim⟩
    have h1 :=(bfw hkeep k).trans
      (cD4 R src hw (hprev.le.trans R.sched.aE8) k)
    have hj:Wx b<b.row.stages.length:= by
      have :=R.sched.aE8
      have :=R.sched.aXU
      unfold Fo at *
      omega
    have h2 :=cYy R src hw ⟨Wx b,hj⟩ (Nat.pos_of_ne_zero hz)
      false hsub (by simp) k
    exact le_min h1 h2
theorem ecU {b h u del} {M:P1.FJ h u del} {Γ}
    (F:P1.bje farAgreement M Γ) (hband:InFar b M.iF)
    {B J:ℕ} (guard :aBh B J) {G:tK} (hG:abM G B J)
    {T:zJe K} (hT:T⊆Γ) (hroot : ∀ γ∈T,FW G (F.scalar γ)=0) :
    T.card≤au1 b.row.hi B J:= by
  classical
  let d:=wX b.row.hi
  have hd:d<farAgreement:=(degree_guards b).2.1
  have hd₀:2≤d:=(by decide :2≤131071).trans (Nat.le_add_right _ _)
  have hdeg (γ) (hγ:γ∈T) : (F.scalar γ).natDegree≤d:= by
    rcases (F.mark γ (hT hγ)).aic with hz | hh
    · simp [hz]
    · change ((F.scalar γ).natDegree :ℤ)≤131071+M.iF at hh
      change (F.scalar γ).natDegree≤131071+b.row.hi
      have hhi:=hband.2
      omega
  let q:=farAgreement - d
  let a :=BJ d B
  let v :=YM d B J
  let β:ℚ:=((blockLength - farAgreement:ℕ) :ℚ)/q
  let m:=(B-J)*v+J*a
  have hβ:0≤β:= by dsimp only [β]; positivity
  have hv :v≤a :=min_le_left _ _
  have h:=cSy (F.distinct.mono hT) guard G hG hroot (β*a) (β*v) (by positivity)
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hv) hβ) (fun U hU f hf hp hB hJ hreg=> by
      have hc:=ePE (F.distinct.mono (hU.trans hT))
        (fun γ hγ=>hdeg γ (hU hγ)) (fun γ hγ =>
          let mark :=F.mark γ (hT (hU hγ))
          ⟨mark.bad.support,mark.bad.dw,mark.scalar_hits⟩)
        hd₀ hd guard.jpos f hf hp hB hJ hreg
      refine hc.trans_eq ?_
      change β *mix f.totalDegree (f.degreeOf 1) a v+1= _
      unfold mix
      ring)
  have he :mix B J (β*a) (β*v)=β*m:= by unfold mix m; push_cast; ring
  rw [he] at h
  let num :=(blockLength - farAgreement)*m
  let gX:=(num+(q-1))/q
  have hq:0<q:=Nat.sub_pos_of_lt hd
  have hqR: (0:ℚ)<(q:ℚ) := by exact_mod_cast hq
  have hr :=Nat.mod_add_div (num+(q-1)) q
  have hlt:=Nat.mod_lt (num+(q-1)) hq
  have hn:num≤q*gX:= by dsimp only [gX]; omega
  have hpay :β*m≤(gX:ℚ) := by
    dsimp only [β]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hqR).mpr
    rw [mul_comm (gX:ℚ)]
    exact_mod_cast hn
  change T.card≤gX+B^2
  have : (T.card:ℚ)≤(gX:ℚ)+(B^2 :ℕ) :=h.trans (add_le_add hpay le_rfl)
  exact_mod_cast this
end
end P6_7_7
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
namespace P6_7_7
noncomputable section
open Polynomial
open P6 (K p jG)
open P6_7 (Source)
open P5_7 (FarBand InFar farAgreement)
open P5_7_5 (aqE Process afa arS nV Fo aU2 a5S BC al6 lowSeedFee lowJetFee contentBudget a4f au1 aEt aEv lossFee pointFee cb1 ash heightLimit V8 SS enb le_ceil_toNat)
open TD (GM J2 FP XM bBx cSF aBh)
open cu (Jet vP A5 rD kr qD)
open gT (tK FW)
open pI (NO abM acW bH7 b6V)
open qQ (VN zI oU aeH)
open ac6.Bridge (aQF cbq)
open scoped BigOperators Classical
def c1 :Prop :=
  ∀ (b:FarBand) u del (M:jG u del) Γ (F:P1.bje farAgreement M Γ),
    aqE b →
    ∀ P Q:Jet,P≠0→Q≠0→aeH P Q →
    oU P (nV b 0).free.shape→ oU Q (nV b 0).moving.shape →
    ∀ (A:NO P (nV b 0).free.shape) (B:NO Q (nV b 0).moving.shape),
    (∀ γ∈Γ,rD P (M.label γ) (F.scalar γ)=0∧rD Q (M.label γ) (F.scalar γ)=0) →
    ∀ T8:ℕ→Jet,
    (∀ i∈b.row.RU,T8 i≠0∧oU (T8 i) (nV b i).free.shape ∧
      ∀ j a,a≤(nV b i).dI →
        ∀ γ∈Γ,rD (A5 j a (T8 i)) (M.label γ) (F.scalar γ)=0) →
    Nonempty (aAT M F b A.equation B.equation)
def c2 :Prop :=
  ∀ (b:FarBand) u del (M:jG u del) Γ (F:P1.bje farAgreement M Γ)
    (rows :vP),Source b M F rows →
    ∀ (pairs :P5_7.Pairs b M.iF.toNat rows) (R:Process pairs) (i:ℕ),
      ∃ C:acW,
        (∀ bw,(C.cost bw:ℚ)≤FP (SS b bw i) (J2 (R.Hj i))) ∧
        ∀ γ∈Γ,(∃ I∈R.Hj i,I0 F I γ) →
          γ∈C.direct ∨ ∃ I∈C.qv,I0 F I γ
def c3:Prop :=
  ∀ (b:FarBand) u del (M:jG u del) Γ (F:P1.bje farAgreement M Γ),
    InFar b M.iF→ash b<p → ∀ C:acW,
      (C.cost 0:ℚ)≤ash b→(C.cost 1 :ℚ)≤heightLimit b →
      (aHl F C).card≤lossFee b
private structure dnD {b u del} {M:jG u del} {Γ}
    {F:P1.bje farAgreement M Γ} {rows :vP}
    {pairs :P5_7.Pairs b M.iF.toNat rows} (R:Process pairs) where
  cut:acW
  acI: (cut.cost 0:ℚ)≤ash b
  height_le : (cut.cost 1 :ℚ)≤heightLimit b
  point_le :cut.direct.card≤pointFee b
  Eh : ∀ i≤Fo b,∀ γ∈Γ,∀ I∈R.Hj i,
    I0 F I γ→γ∈cut.direct∨γ∈aHl F cut
private theorem loss_cover (hcut:c2) {b u del} {M:jG u del} {Γ}
    {F:P1.bje farAgreement M Γ} {rows :vP}
    {pairs :P5_7.Pairs b M.iF.toNat rows} (R:Process pairs)
    (src :Source b M F rows) (hw:InFar b M.iF) :
    Nonempty (dnD (F:=F) R) := by
  let n:=Fo b+1
  choose C hcost hcover using hcut b u del M Γ F rows src pairs R
  let cut:=bH7 (z4x n) C
  have Ya (bw:Fin 3) (hist:ℕ→GM)
      (caps : ∀ i<n,∀ k,J2 (R.QV i) k≤hist i k) :
      (cut.cost bw:ℚ)≤XM n (SS b bw) hist:= by
    calc
      _ ≤ ∑ i∈z4x n,((C i).cost bw:ℚ) := by
        exact_mod_cast b6V (z4x n) C bw
      _ ≤ ∑ i∈z4x n,FP (SS b bw i) (J2 (R.Hj i)) :=
        zQk (fun i _=>hcost i bw)
      _≤_:=bBx n (SS b bw) hist R.QV R.Hj
        (fun _ hi=>R.eEO (zeh hi))
        (fun _ hi=>R.eyg (zeh hi)) caps
  have caps (i:ℕ) (hi:i<n) (k :Fin 4) :
      J2 (R.QV i) k≤V8 b i k :=
    dE4 R src hw (zeh hi) k
  refine ⟨⟨cut,Ya 0 _ caps,Ya 1 _ caps,?_,?_⟩⟩
  · let start:GM :=
      ![(BC b 0:ℚ),(BC b 1 :ℚ),(BC b 2 :ℚ),(al6 b:ℚ)]
    have flat : ∀ i<n,∀ k,J2 (R.QV i) k≤ start k := by
      intro i hi k
      have hc:=(caps i hi k).trans (enb b i k)
      fin_cases k
      · exact hc
      · exact hc
      · exact hc
      · exact hc.trans ((z9h (α:=ℚ)).mpr R.sched.bq5)
    have hp:=Ya 2 (fun _=>start) flat
    rw [cSF] at hp
    exact (z9h (α:=ℚ)).mp
      (hp.trans (le_ceil_toNat (cb1 b)))
  · intro i hi γ hγ I hI hm
    have hr :i∈z4x n:=Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
    rcases hcover i γ hγ ⟨I,hI,hm⟩ with hd | ⟨J,hJ,hj⟩
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨i,hr,hd⟩)
    · exact Or.inr (Finset.mem_biUnion.mpr
        ⟨J,Finset.mem_biUnion.mpr ⟨i,hr,hJ⟩,Finset.mem_filter.mpr ⟨hγ,hj⟩⟩)
private def bdZ {u del} {M:jG u del} {Γ} (F:P1.bje farAgreement M Γ)
    (G:tK) :zJe K:=Γ.filter fun γ=>FW G (F.scalar γ)=0
private theorem b3r {b u del} {M:jG u del} {Γ}
    (F:P1.bje farAgreement M Γ) (hw:InFar b M.iF) {B J:ℕ}
    (guard :aBh B J) {G:tK} (cap:abM G B J) :
    (bdZ F G).card≤au1 b.row.hi B J :=
  ecU F hw guard cap (zT0 _ _)
    (fun _ hγ=>(Finset.mem_filter.mp hγ).2)
private def bqg {b u del} {M:jG u del} {Γ} (F:P1.bje farAgreement M Γ)
    {rows :vP} {pairs :P5_7.Pairs b M.iF.toNat rows} (R:Process pairs) :zJe K :=
  Finset.univ.biUnion fun i:afa b =>
    bdZ F (R.fixed i).free.equation∪bdZ F (R.fixed i).moving.equation
private theorem ecR {b u del} {M:jG u del} {Γ}
    (F:P1.bje farAgreement M Γ) (hw:InFar b M.iF) {rows :vP}
    {pairs :P5_7.Pairs b M.iF.toNat rows} (R:Process pairs) :
    (bqg F R).card≤a4f b:= by
  let jX (i:ℕ) :=
    au1 b.row.hi (nV b i).free.shape.B (nV b i).free.shape.J +
      au1 b.row.hi (nV b i).moving.shape.B (nV b i).moving.shape.J
  calc
    _ ≤ ∑ i:afa b,
        (bdZ F (R.fixed i).free.equation∪bdZ F (R.fixed i).moving.equation).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ i:afa b,jX i:= by
      apply zQk
      intro i _
      obtain ⟨ga,gb⟩:=R.sched.aE7 i i.isLt
      exact (z2s _ _).trans (z9f
        (b3r F hw ga.ode (R.fixed i).free.equation_caps)
        (b3r F hw gb.ode (R.fixed i).moving.equation_caps))
    _ = ∑ i∈z4x b.row.stages.length,jX i :=
      Fin.sum_univ_eq_sum_range jX b.row.stages.length
    _≤_:=R.sched.fixed
private theorem cZ4 {b u del} {M:jG u del} {Γ} (F:P1.bje farAgreement M Γ)
    {rows :vP} {pairs :P5_7.Pairs b M.iF.toNat rows} (R:Process pairs)
    (i:afa b) {γ:K} (hγ:γ∈Γ) (hz :FW (R.fixed i).free.equation (F.scalar γ)=0) :
    γ∈bqg F R :=
  Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ,hz⟩)⟩
private theorem cZ5 {b u del} {M:jG u del} {Γ} (F:P1.bje farAgreement M Γ)
    {rows :vP} {pairs :P5_7.Pairs b M.iF.toNat rows} (R:Process pairs)
    (i:afa b) {γ:K} (hγ:γ∈Γ) (hz :FW (R.fixed i).moving.equation (F.scalar γ)=0) :
    γ∈bqg F R :=
  Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ,hz⟩)⟩
private theorem ajB {n:ℕ} {r :ℚ} (h: (n:ℚ)≤ r) :n≤ r.floor.toNat := by
  have hi: (n:ℤ)≤ r.floor :=Rat.le_floor_iff.mpr (by exact_mod_cast h)
  simpa using Int.toNat_le_toNat hi
private theorem pay_union {A B:zJe K} {a b:ℕ}
    (ha :A.card≤a) (hb:B.card≤b) : (A∪B).card≤a+b :=
  (z2s _ _).trans (z9f ha hb)
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :P6_7.c7:= by
  classical
  intro b u del M Γ F hw _ _ _ rows src pairs
  let sched:=qeA2Kad.proof b
  let zero :afa b:=⟨0,sched.aXU⟩
  let P:=arS pairs zero
  let fixed:=ecO src pairs
  obtain ⟨ga,gb⟩:=sched.aE7 0 sched.aXU
  have hf :=src.shape _ (aU2 zero) _ _ P.free_mem
  have hg:=src.shape _ (a5S zero) _ _ P.moving_mem
  let T8 (i:ℕ) :Jet:=if hi:i<b.row.stages.length then (arS pairs ⟨i,hi⟩).free else 0
  obtain ⟨initial⟩:=h1 b u del M Γ F sched P.free P.moving P.free_ne P.moving_ne
    P.no_moving hf hg (fixed zero).free (fixed zero).moving (fun γ hγ =>
      ⟨aS3 src (aU2 zero) ga.pos (Nat.sub_le _ _) P.free_mem γ hγ,
        aS3 src (a5S zero) gb.pos (Nat.sub_le _ _) P.moving_mem γ hγ⟩) T8 (by
      intro i hi
      obtain ⟨_,hsize⟩:=sched.brd i hi
      let j:afa b:=⟨i,hsize⟩
      let pair :=arS pairs j
      simp only [T8,dite_eq_left hsize]
      exact ⟨pair.free_ne,src.shape _ (aU2 j) _ _ pair.free_mem,
        fun k a ha=>eo4 src hw (aU2 j) (sched.aE7 i hsize).1 pair.free_mem k a ha⟩)
  let R:Process pairs :=
    ⟨sched,initial.parents,fixed,fun I hI=>⟨initial.active I hI,initial.a4E I hI⟩,
      initial.bst⟩
  obtain ⟨arL⟩:=loss_cover h2 R src hw
  obtain ⟨G,hgcap,hG⟩:=TD.fS7 R.aWI (fun _ hI=>R.fTa hI)
    (B:=aEt b) (J:=aEv b) (ajB (c6F R src hw 1))
    (ajB (c6F R src hw 2))
  let seed :=Γ.filter fun γ=>initial.seed.ow (M.label γ)
  let contents :=Γ.filter fun γ=>qD (M.label γ) initial.content=0
  let ords :=Γ.filter fun γ=>kr (F.scalar γ)∈initial.ordinates
  let rank :=bdZ F G
  have label_inj:Function.Injective M.label := fun _ _ h=>sub_left_inj.mp h
  have hseed :seed.card≤lowSeedFee b:= by
    have h:=qQ.aJr (T:=seed) label_inj.injOn initial.seed
      (initial.acI.trans_lt (sched.bq6 2)) (fun _ hγ=>(Finset.mem_filter.mp hγ).2)
    exact h.trans (z9f (zBI _ initial.acI) initial.seed_points)
  have hcontents :contents.card≤ contentBudget b:= by
    let C:VN :=⟨initial.content,initial.content_ne,∅⟩
    have h:=qQ.aJr (T:=contents) label_inj.injOn C
      (initial.content_le.trans_lt sched.bDl)
      (fun _ hγ=>Or.inl (Finset.mem_filter.mp hγ).2)
    have h' : contents.card≤(p+1)*initial.content.totalDegree := by
      simpa only [C,Finset.card_empty,Nat.add_zero] using h
    exact (h'.trans (zBI _ initial.content_le)).trans sched.content
  have hords :ords.card≤BC b 0 :=
    (Finset.card_le_card_of_injOn (fun γ=>kr (F.scalar γ))
      (fun _ hγ=>(Finset.mem_filter.mp hγ).2)
      (fun _ hγ _ hδ h=>F.distinct (Finset.mem_filter.mp hγ).1 (Finset.mem_filter.mp hδ).1
        (qQ.bNe h))).trans initial.ordinate_le
  let qv :=aHl F arL.cut
  let fixedPaid :=bqg F R
  let books :=arL.cut.direct∪qv∪seed∪(ords∪rank)∪fixedPaid∪contents
  have hcurves :qv.card≤lossFee b :=
    h3 b u del M Γ F hw sched.seed_small arL.cut arL.acI arL.height_le
  have hjet: (ords∪rank).card≤lowJetFee b :=
    pay_union hords (b3r F hw sched.bK5 hgcap)
  have hbooks :books.card≤b.row.prefixFee :=
    (pay_union (pay_union (pay_union (pay_union (pay_union arL.point_le hcurves) hseed)
      hjet) (ecR F hw R)) hcontents).trans sched.gH
  have initial_mem (I : ↥R.final) :I.1∈R.parents :=
    R.bxI _ (R.a4R _ (R.bGA I.2))
  let toSurface (I : ↥R.final) :zI:=aQF I.1 (R.DN _ (initial_mem I)).1.prime
  refine ⟨{
    book :=books
    book_bound:=hbooks
    parents :=R.final.attach.image toSurface
    geometric := ?_
    stage_pass := ?_
    terminal_pass := ?_
    Eh := ?_ }⟩
  · intro q hq
    obtain ⟨I,_,rfl⟩:=Finset.mem_image.mp hq
    have hgeom:=R.DN _ (initial_mem I)
    exact cbq hgeom.1 hgeom.2
      ((Finset.mem_filter.mp (R.bGA I.2)).2 sched.aE8)
  · intro q hq s hs hpositive
    obtain ⟨I,_,rfl⟩:=Finset.mem_image.mp hq
    obtain ⟨i,hi,he⟩:=List.mem_iff_getElem.mp hs
    let j:afa b:=⟨i,hi⟩
    have ht:nV b j=s := by
      simpa [j,nV,List.getElem?_eq_getElem hi] using he
    clear he
    subst s
    have htest :=(Finset.mem_filter.mp (R.a4R _ (R.bGA I.2))).2.2
    have hj:0<j.val := by
      by_contra! hbad
      have hz :j.val=0:=Nat.eq_zero_of_le_zero hbad
      have hr : (nV b j).dI=0:= by rw [hz,sched.zero]
      omega
    exact P5_7_5.gxI (R.DN _ (initial_mem I)).1.prime
      (htest j hj (by unfold Fo; dsimp [j]; omega))
  · intro q hq
    obtain ⟨I,_,rfl⟩:=Finset.mem_image.mp hq
    exact (Finset.mem_filter.mp I.2).2
  · intro γ hγ
    by_cases hpaid :γ∈books
    · exact Or.inl hpaid
    right
    simp only [books,Finset.mem_union,not_or] at hpaid
    obtain ⟨⟨⟨⟨⟨hnpoint,hncurve⟩,hnseed⟩,hnords,hnrank⟩,hnfixed⟩,hncontent⟩:=hpaid
    rcases initial.Eh γ hγ with hz | ho | hc | ha | hb | ⟨I,hI,hm⟩
    · exact (hnseed (Finset.mem_filter.mpr ⟨hγ,hz⟩)).elim
    · exact (hnords (Finset.mem_filter.mpr ⟨hγ,ho⟩)).elim
    · exact (hncontent (Finset.mem_filter.mpr ⟨hγ,hc⟩)).elim
    · exact (hnfixed (cZ4 F R zero hγ ha)).elim
    · exact (hnfixed (cZ5 F R zero hγ hb)).elim
    · have hclean:R.Clean I:= fun j =>
        ⟨fun hj=>hnfixed (cZ4 F R j hγ (b3t hm hj)),
          fun hj=>hnfixed (cZ5 F R j hγ (b3t hm hj))⟩
      have hnotRank :I∉R.aWI:= fun h=>hnrank
        (Finset.mem_filter.mpr ⟨hγ,b3t hm (hG I h)⟩)
      have hnotLost : ∀ i≤Fo b,I∉R.Hj i:= fun i hi h =>
        (arL.Eh i hi γ hγ I h hm).elim hnpoint hncurve
      let J : ↥R.final:=⟨I,R.fXs hI hclean hnotRank hnotLost⟩
      exact ⟨toSurface J,Finset.mem_image_of_mem _ (Finset.mem_attach _ _),eGu _ hm⟩
end
end P6_7_7
end
