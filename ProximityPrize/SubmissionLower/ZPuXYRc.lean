import ProximityPrize.SubmissionLower.ZXxMpWa
import ProximityPrize.SubmissionLower.Zm5KYKd
import ProximityPrize.SubmissionLower.ZTzAWec
import ProximityPrize.SubmissionLower.ZE36Kga
import ProximityPrize.SubmissionLower.ZqY5s9b
import ProximityPrize.SubmissionLower.ZpYo3sb
set_option Elab.async false
section
set_option autoImplicit true
namespace P6_7_5
noncomputable section
open P6 (p)
open P5_7 (midAgreement)
open P5_7_3 (Jr aL4 O3 j3 Mq amv stages anM O2 akE Pairs)
open Dt (Bank Ls)
open cu (Shape vP Jet FX)
open gT (alm)
open aBa (cNB)
open Polynomial Finset
open private cSB from ProximityPrize.SubmissionLower.T
open private ee7 eHt eD6 from ProximityPrize.SubmissionLower.Zm5KYKd
private theorem bwO {b cap u del} {M:P1.FJ cap u del} {Γ}
    {F:P1.bje midAgreement M Γ} {rows :vP} (src :Source b M F rows)
    {t:Bank} (ht:Jr b t) (r :ℕ)
    (hw:aL4 M.iF.toNat r t.shape) :
    O3 M.iF.toNat r t.shape 0≤j3 M.iF.toNat t +
      ∑ W∈range (Mq M.iF.toNat r t.shape),
        Module.finrank FX (rows t.shape W) := by
  let h:=M.iF.toNat
  let N :=Mq h r t.shape
  change t.shape.B*(131071-h)<N at hw
  have hN :0<N :=lt_of_le_of_lt (Nat.zero_le _) hw
  have hNt:N≤t.shape.m*midAgreement:=Nat.sub_le _ _
  have hc:N - 1+1=N := by omega
  have hf :=src.ajB t ht (N - 1) (by omega) (by
    intro q hq j _
    rw [hc]
    exact ((Nat.mul_le_mul_right _ hq).trans hw.le).trans (Nat.le_add_right N j))
  unfold O3 amv
  simpa only [hc,zero_mul,Nat.sub_zero] using hf
private theorem bVl {b cap u del} {M:P1.FJ cap u del} {Γ}
    {F:P1.bje midAgreement M Γ} {rows :vP} (src :Source b M F rows)
    {t:Bank} (ht:Jr b t) (r :ℕ)
    (hw:aL4 M.iF.toNat r t.shape)
    (hd:j3 M.iF.toNat t<O3 M.iF.toNat r t.shape 0) :
    ∃ P∈rows t.shape (Mq M.iF.toNat r t.shape - 1),P≠0:= by
  by_contra! hz
  let N :=Mq M.iF.toNat r t.shape
  have hf :=bwO src ht r hw
  have hsum: (∑ W∈range N,Module.finrank FX (rows t.shape W))=0:= by
    apply sum_eq_zero
    intro W hW
    have hle :W≤N - 1 := by have :=mem_range.mp hW; omega
    have hb:rows t.shape W = ⊥ := by
      apply bot_unique
      intro P hP
      exact (Submodule.mem_bot FX).mpr
        (hz P (src.nested t ht t ht rfl rfl rfl le_rfl W _ hle hP))
    rw [hb,finrank_bot]
  change _≤_ + ∑ W∈range N,Module.finrank FX (rows t.shape W) at hf
  omega
private theorem cCz {b cap u del} {M:P1.FJ cap u del} {Γ} {F:P1.bje midAgreement M Γ}
    {rows :vP} (src :Source b M F rows) (hh:0<M.iF.toNat)
    (hk :1≤131071-M.iF.toNat) {t:Bank} (ht:Jr b t) (r :ℕ)
    (hw:aL4 M.iF.toNat r t.shape)
    (hd:j3 M.iF.toNat t<O3 M.iF.toNat r t.shape 1)
    {G P:Jet} (hi:Irreducible G) (hv :0<G.natDegree) (hm:alm G)
    (hP:P≠0) (hdiv :G∣P) {U:ℕ} (hp:U<p)
    (hseed : ∀ j i,((P.coeff j).coeff i).totalDegree≤U) :
    ∃ Q∈rows t.shape (Mq M.iF.toNat r t.shape - 1),¬ G∣Q:= by
  by_contra! hcommon
  let h:=M.iF.toNat
  let N :=Mq h r t.shape
  have hsum:=eD6 rows t.shape h r hk (src.shape t ht) (src.leading t ht) (by
    intro W hW R hR hnR
    apply eHt h N W hh hW hi hv hm hP hdiv hp hseed hnR
    intro i a hshift
    exact hcommon _ (src.nested t ht t ht rfl rfl rfl le_rfl _ _ hshift
      (src.shift t ht W R hR i a)))
  have hf :=bwO src ht r hw
  dsimp only [h] at hsum
  omega
private theorem eJG {b cap u del} {M:P1.FJ cap u del} {Γ}
    {F:P1.bje midAgreement M Γ} {rows :vP} (src :Source b M F rows)
    (hh:0<M.iF.toNat) (hk :1≤131071-M.iF.toNat)
    {s :Ls} (hs :s∈stages b)
    (hwidth :aL4 M.iF.toNat s.dI s.free.shape)
    (hfree :j3 M.iF.toNat s.free<O3 M.iF.toNat s.dI s.free.shape 0)
    (hchar :s.free.shape.U<p)
    (hwidth' : aL4 M.iF.toNat s.dI s.moving.shape)
    (hmoving:j3 M.iF.toNat s.moving<O3 M.iF.toNat s.dI s.moving.shape 1) :
    Nonempty (akE M.iF.toNat rows s) := by
  have hsFree :Jr b s.free :=Or.inr (Or.inl ⟨s,hs,Or.inl rfl⟩)
  have hsMoving:Jr b s.moving:=Or.inr (Or.inl ⟨s,hs,Or.inr rfl⟩)
  obtain ⟨P,hPm,hP⟩:=bVl src hsFree s.dI hwidth hfree
  have hnonzero :=bVl src hsMoving s.dI hwidth'
    (hmoving.trans_le (ee7 _ _ _))
  have hseed (j y :ℕ) : ((P.coeff j).coeff y).totalDegree≤ s.free.shape.U:= by
    by_cases hz : (P.coeff j).coeff y=0
    · simp [hz]
    · exact (src.shape s.free hsFree _ P hPm j y hz).2.2
  obtain ⟨Q,hQm,hQ,havoid⟩:=cNB P hP _ hnonzero (fun G hi hdiv hv hm =>
    cCz src hh hk hsMoving s.dI hwidth' hmoving hi hv hm hP hdiv hchar hseed)
  have hcut (a :Shape) :anM M.iF.toNat s.dI a =
      Mq M.iF.toNat s.dI a - 1 := by
    unfold anM O2 Mq
    omega
  exact ⟨⟨P,Q,hP,hQ,(hcut _).symm ▸ hPm,(hcut _).symm ▸ hQm,
    fun G hi hdiv hdiv' hv=>cSB G (fun hm=>havoid G hi hdiv hv hm hdiv')⟩⟩
theorem bufferedPairs {b cap u del} {M:P1.FJ cap u del} {Γ}
    {F:P1.bje midAgreement M Γ} {rows :vP} (src :Source b M F rows)
    (hh:0<M.iF.toNat) (hk :1≤131071-M.iF.toNat)
    (checks : ∀ s∈stages b,
      let h:=M.iF.toNat
      aL4 h s.dI s.free.shape ∧
      j3 h s.free<O3 h s.dI s.free.shape 0∧s.free.shape.U<p ∧
      aL4 h s.dI s.moving.shape ∧
      j3 h s.moving<O3 h s.dI s.moving.shape 1) :
    Nonempty (Pairs b M.iF.toNat rows) := by
  classical
  exact ⟨fun s hs=>Classical.choice (by
    obtain ⟨hw,hd,hc,hw',hd'⟩:=checks s hs
    exact eJG src hh hk hs hw hd hc hw' hd')⟩
end
end P6_7_5
end
section
set_option autoImplicit true
namespace P6_7_5
noncomputable section
open Polynomial
open P6 (p)
open P5_7 (midAgreement Qn)
open P5_7_3 (Test Lc terminal awI ctc aRe O2 ahs agA bAN)
open cu (vP Jet Equation)
open qQ (zI N5 aLQ wU)

private theorem eHv {b cap u del} {M:P1.FJ cap u del} {Γ} {F:P1.bje midAgreement M Γ}
    {rows :vP} (src :Source b M F rows) (hw:Qn b.jX.lo b.jX.hi M.iF)
    (x :Test b) {q:zI} (hq:N5 q) (hv :agA rows (terminal b).shape q)
    {W} (hW:W<(Lc b x).shape.m*midAgreement) {P:Jet}
    (hP:P∈rows (Lc b x).shape W) :
    wU q P (ahs M.iF.toNat (Lc b x).shape W) := by
  let h:=M.iF.toNat
  let t:=Lc b x
  obtain ⟨ht,hm,hb,hj,hu⟩:=ctc b x
  have hchar :t.shape.m*midAgreement<p:=hm ▸ (awI b).2.2.2.1
  apply baD.proof _ _ _ hq
  · have hd:=Nat.div_le_self (O2 t.shape-W) (2*h)
    change 1+(O2 t.shape-W)/(2*h)<p
    change W<t.shape.m*midAgreement at hW
    unfold O2 at *
    omega
  intro a c hac
  change a+c<1+(O2 t.shape-W)/(2*h) at hac
  have hh:0<h:=(awI b).1.trans_le (aRe hw).1
  have hc:=(Nat.le_div_iff_mul_le (by omega :0<2*h)).mp
    (show a+c≤(O2 t.shape-W)/(2*h) by omega)
  rw [Nat.mul_comm (a+c),Nat.mul_add] at hc
  have top:O2 t.shape=O2 (terminal b).shape :=
    congrArg (fun m=>m*midAgreement - 1) hm
  have hwc:W≤O2 t.shape := by
    change W<t.shape.m*midAgreement at hW
    unfold O2
    omega
  have hw' : W+2*h*a+2*h*c≤O2 (terminal b).shape := by omega
  have ha :=src.shift t ht W P hP 0 a
  have hc' := src.shift t ht _ _ ha 1 c
  exact hv _ (src.nested t ht _ (Or.inl rfl) hm hb hj hu _ _ hw' hc')
theorem gDx {b cap u del} {M:P1.FJ cap u del} {Γ} {F:P1.bje midAgreement M Γ}
    {rows :vP} (src :Source b M F rows) (hw:Qn b.jX.lo b.jX.hi M.iF)
    {qs :Finset zI} (hq : ∀ q∈qs,N5 q)
    (hp : ∀ q∈qs,agA rows (terminal b).shape q) {f :Equation}
    (hf :aLQ qs f) (x :Test b) :
    bAN M.iF.toNat (Lc b x) rows f := by
  have ht:=(ctc b x).1
  refine ⟨src.ajB _ ht,src.shape _ ht,src.leading _ ht,?_⟩
  intro W hW P hP hn
  exact hf.divides_leading P _ hn
    (fun q h=>eHv src hw x (hq q h) (hp q h) hW hP)
end
end P6_7_5
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace P6_7_5
noncomputable section
open Polynomial
open cu (L FX vP j9 triangle)
open DP
open P6 (K I p)
open P5_7 (midAgreement)
open P6_7 (YQ)
open P5_7_3 (fO Jr)
open Dt (Bank)
open agU (ajD ad1 telescope)
open scoped BigOperators Polynomial
open private c4y from ProximityPrize.SubmissionLower.ZdZNCPb
theorem source {b:fO} {cap u del} {M:P1.FJ cap u del} {Γ}
    (F:P1.bje midAgreement M Γ) (H :L[X]) (hH :YQ M F H)
    (hlo:0<M.iF.toNat) (hraw:M.iF.toNat≤131070)
    (checked : ∀ t:Bank,Jr b t →
      ad1 t.shape=t.ad1 ∧
      ajD t.shape.B t.shape.J≤t.poleMoment∧t.shape.B<p) :
    ∃ rows :vP,Source b M F rows := by
  let h:=M.iF.toNat
  have hchar :h<p:=hraw.trans_lt (by decide)
  have hlocal:agU.c1 :=
    aeL.of_children czW.proof aSk.proof
  obtain ⟨D,_,_,hnode,hres⟩:=P6_7.bW4 M F H hH
  obtain ⟨Crt⟩:=atp.dRH D
  let word:I→L:= fun i=>algebraMap K L (M.word i)
  refine ⟨VY Crt word,⟨?_,?_,?_,?_,?_,?_⟩⟩
  · intro t _ t' _ hm hB hJ hU W W' hW
    exact d3q Crt word hm hB hJ hU hW
  · intro t _ W hW P hP γ hγ
    let B:=F.mark γ hγ
    have hdegree : (j9 (F.scalar γ)).natDegree≤131071+h:= by
      rw [j9,Polynomial.natDegree_map]
      exact P6_7.aic F hγ
    refine atp.dPr Crt word hnode _ _ (hres γ hγ) hdegree B.bad.support
      B.bad.dw ?_ t.shape W hW P hP
    intro i hit
    rw [j9,ad0,Polynomial.eval_map,Polynomial.eval₂_hom,B.scalar_hits i hit]
  · intro t _ W P hP j i hne
    exact d3r Crt word hP j i hne
  · intro t _ W P hP hne
    exact atp.eu5 hlo hraw Crt word t.shape W P hP hne
  · intro t _ W P hP i r
    exact atp.d3s Crt word hP i r
  · intro t ht W _ hW
    obtain ⟨hn,hm,hB⟩:=checked t ht
    have hvol:=atp.bT9 (hraw.trans (by decide)) t.shape W hW
    have hcontact :=atp.Yw h word t.shape W
    have hpole :=c4y hlocal hlo hchar Crt word t.shape hB W
    have hsum:=telescope hraw Crt word t.shape W
    have hphys :bga t.shape=triangle t.shape.U*t.ad1 := by
      rw [← hn]
      unfold bga ad1
      rw [Nat.mul_assoc]
    rw [hphys] at hcontact
    have hextra :=Nat.mul_le_mul_left (2*h*(t.shape.U+1)) hm
    change ceG h t.shape W ≤
      (triangle t.shape.U*t.ad1+2*h*(t.shape.U+1)*t.poleMoment) +
        ∑ w∈Finset.range (W+1),Module.finrank FX (VY Crt word t.shape w)
    dsimp only [h] at *
    omega
end
end P6_7_5
end
section
set_option autoImplicit true
namespace P6_7_5
noncomputable section
open Polynomial
open P6 (jG K I)
open P5_7 (Qn midAgreement)
open P6_7 (YQ RegularBound axy)
open P5_7_3 (fO Pairs aKj Lc cV prefixFee awI aRe ctc eqx eiO schedule_paid bands_prices)
open qkgz7gb (UJ wX)
open Dt (Reduced)
open cu (Equation vm yq)
def c1 :Prop :=
  ∀ (b:fO) u del (M:jG u del) Γ (F:P1.bje midAgreement M Γ),
    Qn b.jX.lo b.jX.hi M.iF→M.shift∉Γ →
    ∀ H,YQ M F H →
    ∀ rows,Source b M F rows → ∀ pairs :Pairs b M.iF.toNat rows,
    Nonempty (bkU b M F pairs)
def c2 :Prop :=P5_7_3.c4
def c3:Prop :=
  ∀ (b:fO) (word:I→K) (T:Finset K) (z :K→K) (S:K→K[X]),
    UJ (wX b) word T z S →
    ∀ (i:aKj b) (f :Equation),Reduced f →
      f.natDegree=i.val+1→vm f (cV b i).seedCap →
      (∀ γ∈T,yq f (z γ) (S γ)=0) →
      T.card≤b.schedule.retainedFee
private theorem witnessed_marks {b:fO} {u del} (M:jG u del) {Γ}
    (F:P1.bje midAgreement M Γ) (hw:Qn b.jX.lo b.jX.hi M.iF)
    {H} (hH :YQ M F H) {T:Finset K} (hT:T⊆Γ) :
    UJ (wX b) M.word T M.label F.scalar := by
  have h:=aRe hw
  have hhi:b.jX.hi≤b.pricedHi:= by cases b <;> decide
  obtain ⟨D,_,_,_,hD⟩:=P6_7.bW4 M F H hH
  exact ⟨fun _ _ _ _ eq=>sub_left_inj.mp eq,F.distinct.mono hT,
    fun _ hγ=>(P6_7.aic F (hT hγ)).trans (Nat.add_le_add_left (h.2.trans hhi) _),
    fun γ hγ =>
      let m:=F.mark γ (hT hγ)
      ⟨m.bad.support,m.bad.dw,m.scalar_hits⟩,
    M.iF.toNat,(awI b).1.trans_le h.1,D,fun γ hγ=>hD γ (hT hγ)⟩
private theorem count_row (h1 :c1) (h2 :c2) (h3:c3)
    (b:fO) :RegularBound midAgreement b.jX:= by
  classical
  intro u del M Γ F hw hshift H hH
  obtain ⟨hl,hu⟩:=aRe (b:=b) hw
  obtain ⟨hlo,hhi,htop,_,hwidth⟩:=awI b
  have hh:=hlo.trans_le hl
  have hk :=hu.trans_lt hhi
  obtain ⟨rows,src⟩:=source (b:=b) F H hH hh (Nat.le_of_lt_succ hk) (qpECY2d.proof b)
  obtain ⟨pairs⟩:=bufferedPairs src hh (Nat.sub_pos_of_lt hk) (q4WM8sb.proof b _ hl hu)
  obtain ⟨Q⟩:=h1 b u del M Γ F hw hshift H hH rows src pairs
  let T:=Γ \ Q.book
  have hT:T⊆Γ:=Finset.sdiff_subset
  have hprefix : (Γ \ T).card≤P5_7_3.prefixFee b:= by
    apply (Finset.card_le_card ?_).trans Q.book_bound
    intro γ hγ
    obtain ⟨ha,hn⟩:=Finset.mem_sdiff.mp hγ
    by_contra hm
    exact hn (Finset.mem_sdiff.mpr ⟨ha,hm⟩)
  have hpart:=Finset.card_sdiff_add_card_eq_card hT
  have cover : ∀ γ∈T,∃ q∈Q.parents,axy M F q γ:= fun γ hγ =>
    (Q.Eh γ (hT hγ)).resolve_left (Finset.mem_sdiff.mp hγ).2
  suffices hkept:T.card≤b.schedule.retainedFee from
    (hpart ▸ Nat.add_le_add hprefix hkept).trans (schedule_paid b)
  by_cases hm:T.Nonempty
  · obtain ⟨γ,hγ⟩:=hm
    obtain ⟨q,hq,_⟩:=cover γ hγ
    obtain ⟨f,hf⟩:=czI.proof Q.parents ⟨q,hq⟩ Q.geometric
    have hne :f≠0:=ne_zero_of_natDegree_gt hf.positive
    obtain ⟨i,he,hs⟩:=eiO (b:=b) hf.positive (by
      intro x hE hv
      have trace :=gDx src hw Q.geometric Q.terminal_pass hf x
      obtain ⟨_,ht,hb,_,_⟩:=ctc b x
      have hwidth' : (Lc b x).shape.B*(131071-M.iF.toNat) ≤
          (Lc b x).shape.m*midAgreement:= by
        rw [ht,hb]
        exact (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hl _)).trans hwidth
      exact (h2 b _ hl hu x).not_ge
        (eqx (Nat.mul_pos (by decide) hh) (Nat.sub_pos_of_lt hk)
          x hne trace (ht ▸ htop) hwidth' hE hv))
    apply h3 b M.word T M.label F.scalar (witnessed_marks M F hw hH hT) i f
      ⟨hf.positive,hf.primitive,hf.separable⟩ he hs
    intro η hη
    obtain ⟨q',hq',hon⟩:=cover η hη
    have hz :=RingHom.mem_ker.mp (hon (hf.aiq q' hq'))
    simpa only [coe_eval₂RingHom,eval₂_C,yq] using hz
  · simp [Finset.not_nonempty_iff_eq_empty.mp hm]
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :P6_7.c5:= by
  intro r hr
  rw [← bands_prices] at hr
  obtain ⟨b,_,rfl⟩:=List.mem_map.mp hr
  exact count_row h1 h2 h3 b
end
end P6_7_5
end
section
set_option autoImplicit true
namespace P6_7_1
noncomputable section
open Polynomial
open P6 (K I e9 p dw jG)
open cu (L FX Jet Equation Shape j9 qD ku)
open DP (jF zG ad0 aKF Source Fg complete U4 VY)
open gT (Ambient alm iJ IZ)
open pI (xN oU)
open qQ (zI N5)
open scoped BigOperators Classical
abbrev packetLo:ℕ:=2350
abbrev packetHi:ℕ:=2369
abbrev degree :ℕ:=131071+packetHi
abbrev paidFee :ℕ:=0x4acfb7e61fe3b
abbrev prefixFee :ℕ:=0x2d27e70cf22be2b
abbrev retainedFee :ℕ:=0xf06646491297c1
structure Input where
  u:e9
  del:Finset I
  M:jG u del
  Γ:Finset K
  F:P1.bje dw M Γ
  kA:P5_7.Qn packetLo packetHi M.iF
  noShift:M.shift∉Γ
  H :L[X]
  bY:P6_7.YQ M F H
abbrev Input.h (x :Input) :=x.M.iF.toNat
abbrev Input.word (x :Input) (i:I) :L:=algebraMap K L (x.M.word i)
structure Poles (x :Input) where
  D:jF x.h
  crt:zG D
  first:D.block 0=x.H
  second:D.block 1=x.H.map (frobenius L p)
  offset :D.offset = ![j9 x.M.Q,(j9 x.M.Q).map (frobenius L p)]
  constant:D.constant = ![j9 (x.M.factor*x.M.A₀),
    (j9 (x.M.factor*x.M.A₀)).map (frobenius L p)]
  slope :D.slope = ![j9 (x.M.factor*x.M.A₁),
    (j9 (x.M.factor*x.M.A₁)).map (frobenius L p)]
  nodes : ∀ i j,(D.block i).eval (ad0 j)≠0
  marks : ∀ γ∈x.Γ,aKF D (x.M.label γ) (x.F.scalar γ)
abbrev Poles.rows {x :Input} (P:Poles x) :=VY P.crt x.word
open P5_7_1 (Ls TopRow atTop topLift topConjugate)
def stages :List Ls :=
  [⟨0,⟨83,115,25,1183⟩,⟨812,1131,235,67481⟩⟩,
   ⟨1,⟨83,115,25,1740⟩,⟨880,1226,255,74541⟩⟩,
   ⟨2,⟨121,168,38,1051⟩,⟨982,1368,284,80045⟩⟩,
   ⟨4,⟨106,147,32,2098⟩,⟨1139,1588,330,92690⟩⟩,
   ⟨24,⟨277,384,86,3668⟩,⟨2287,3189,663,290342⟩⟩]
def introductions :List (ℕ×Shape) :=
  [(5,⟨115,159,35,2121⟩),(10,⟨137,190,41,5416⟩),(8,⟨151,210,46,1945⟩),
   (13,⟨200,277,61,2285⟩),(13,⟨158,218,48,5910⟩),(16,⟨200,277,61,3396⟩),
   (20,⟨207,287,63,6661⟩),(20,⟨256,354,81,3002⟩),
   (1,stages[1].free),(4,stages[3].free),
   (24,⟨235,327,71,7518⟩),(24,⟨233,324,70,8257⟩)]
abbrev afa :=Fin stages.length
abbrev Intro:=Fin introductions.length
abbrev Origin :=Fin (introductions.length+1)
abbrev lastOrigin :Origin :=Fin.last _
abbrev anchor :=stages[0].free
def cutoff (s :Shape) :=s.m*dw - 1
def buffer (h r :ℕ) (s :Shape) :=cutoff s - 2*h*r
def seedSpecialize (g:Jet) (z :K) :qQ.IW :=
  g.map (Polynomial.mapRingHom (qD z))
def BaseAvoid (x :Input) (V:Submodule FX Jet) (g:Jet) :Prop :=
  ∀ γ∈x.Γ,seedSpecialize g (x.M.label γ)=0 →
    ∀ Q∈V,seedSpecialize Q (x.M.label γ)=0
structure Pick (x :Input) (P:Poles x) (r :ℕ) (s :Shape) where
  row:Jet
  ne_zero :row≠0
  mem:row∈P.rows s (buffer x.h r s)
  avoids :BaseAvoid x (P.rows s (buffer x.h r s)) row
structure EarlyPicks (x :Input) (P:Poles x) where
  free : ∀ i:afa,Pick x P (stages.get i).dI (stages.get i).free
  moving : ∀ i:afa,Pick x P (stages.get i).dI (stages.get i).moving
  no_moving : ∀ i,qQ.aeH (free i).row (moving i).row
  intro : ∀ i:Intro,Pick x P (introductions.get i).1 (introductions.get i).2
  shared: (intro ⟨8,by decide⟩).row=(free ⟨1,by decide⟩).row ∧
    (intro ⟨9,by decide⟩).row=(free ⟨3,by decide⟩).row
abbrev EarlyPicks.anchorRow {x P} (R:EarlyPicks x P) :=(R.free ⟨0,by decide⟩).row
def TopCaps (h m B J C U:ℕ) (g:TopRow) :Prop :=
  ∀ a∈g.support,
    a 1+a 2+a 3≤B∧a 2+2*a 3≤J∧a 3≤C∧a 0≤U ∧
    (g.coeff a).natDegree+(131071+h)*(a 1+a 2+a 3) ≤
      m*dw-1+(B+J)*h+a 2+2*a 3
structure TopPair (x :Input) where
  cheap:TopRow
  strong:TopRow
  cheap_ne :cheap≠0
  strong_ne :strong≠0
  cheap_caps :TopCaps x.h 64 87 27 12 249 cheap
  strong_caps :TopCaps x.h 120 164 50 19 490 strong
  no_moving : ∀ Q:MvPolynomial (Fin 4) FX,Irreducible Q →
    0<Q.degreeOf 3→Q∣topLift cheap→Q∣topLift strong→Q.degreeOf 0=0
  necessary : ∀ γ∈x.Γ,
    atTop cheap (x.M.label γ) (x.F.scalar γ)=0 ∧
    atTop strong (x.M.label γ) (x.F.scalar γ)=0 ∧
    atTop (topConjugate cheap) (P6.twist (x.M.label γ)) (x.F.scalar γ)=0 ∧
    atTop (topConjugate strong) (P6.twist (x.M.label γ)) (x.F.scalar γ)=0
abbrev wD:=P5_7_1.wD
abbrev bgK:=P5_7_1.bgK
def introCap (i:ℕ) (j:Fin 3) :ℕ :=
  ((introductions.take i).foldl (fun v (r,s)=>min v (bgK s j/(r+1)))
    (bgK anchor j))
def aOm (f :Jet) :Shape :=
  ⟨0,164+19*(wD f 0-1),50+19*(wD f 1-1),490+19*wD f 2⟩
def lineFee (b j u:ℕ) :ℕ :=
  let t:=2*degree-3
  let a :=1+t*(b-1)
  let v :=min a (t*(j-1)+degree)
  let U:=t*u
  let mix :=u*(2*a*v-v*v)+2*U*(b*v+j*(a-v))
  let rest:=u*(2*a+v)+U*(2*b+j)+b*v+j*a+u+b+j
  let q:=P5_7.midAgreement-degree
  (2*(262144-P5_7.midAgreement)*(mix+rest)+q-1)/q+b+u+1
structure OriginCover (x :Input) (P:Poles x) (R:EarlyPicks x P) where
  factors :Finset Jet
  origin :Jet→Origin
  cut:Jet→Jet
  line :Jet→Bool
  lineMarks :Jet→Finset K
  parents :Jet→Finset (Ideal Ambient)
  gH :Finset K
  paid_bound:gH.card≤paidFee
  nested : ∀ i≤ introductions.length,∀ j,
    (∑ f∈factors.filter (fun f=>i≤(origin f).val),wD f j)≤ introCap i j
  proper : ∀ f∈factors,Irreducible f∧f∣R.anchorRow∧alm f ∧ ¬ f∣cut f
  survives : ∀ f∈factors,∀ i:Intro,i.val<(origin f).val →
    ∀ Q∈P.rows (introductions.get i).2 (cutoff (introductions.get i).2),f∣Q
  early_cut : ∀ f∈factors,∀ i:Intro,i.val=(origin f).val →
    let s :=(introductions.get i).2
    cut f∈P.rows s (cutoff s)∧BaseAvoid x (P.rows s (cutoff s)) (cut f)
  shared_cut : ∀ f∈factors,∀ g∈factors,
    (origin f).val< introductions.length→ origin f=origin g→cut f=cut g
  last_cut : ∀ f∈factors,origin f=lastOrigin →
    0<f.natDegree∧oU (cut f)
      (if line f then ⟨0,wD f 0,wD f 1,wD f 2⟩ else aOm f)
  line_pos : ∀ f∈factors,line f=true →
    origin f=lastOrigin∧0<wD f 1∧0<wD f 2∧cut f=f.derivative
  line_bound : ∀ f∈factors,(lineMarks f).card ≤
    if line f then lineFee (wD f 0) (wD f 1) (wD f 2) else 0
  geometric : ∀ f∈factors,∀ q∈parents f,
    xN q∧q.height=2∧iJ f∈q∧iJ (cut f)∈q
  disjoint : ∀ f∈factors,∀ g∈factors,f≠g→Disjoint (parents f) (parents g)
  Eh : ∀ γ∈x.Γ,γ∈gH ∨ ∃ f∈factors,
    γ∈lineMarks f ∨ ∃ q∈parents f,IZ q (x.M.label γ) (x.F.scalar γ)
structure Rectangle where
  m:ℕ
  B:ℕ
  J:ℕ
  z :ℕ
  t:ℕ
def Rectangle.box (s :Rectangle) :Shape :=⟨s.m,s.B,s.J,s.z+s.t⟩
def seedBox (a b:ℕ) :Submodule L Source where
  carrier := {P | ∀ j i d e,a<e 0∨b<e 1→Fg P j i d e=0}
  zero_mem' := by simp [Fg]
  add_mem' := by
    intro P Q hP hQ j i d e he
    have hp:=hP j i d e he
    have hq:=hQ j i d e he
    unfold Fg at hp hq ⊢
    simp [hp,hq]
  smul_mem' := by
    intro c P hP j i d e he
    have hp:=hP j i d e he
    unfold Fg at hp ⊢
    simp [Polynomial.coeff_smul,hp]
def rectComplete {x :Input} (P:Poles x) (s :Rectangle) (W:ℕ) :Submodule L Source :=
  complete P.crt x.word s.box W ⊓ seedBox s.z s.t
def rectBank {x :Input} (P:Poles x) (s :Rectangle) (W:ℕ) :Submodule FX Jet :=
  Submodule.span FX (U4 '' (rectComplete P s W:Set Source))
abbrev rectCut (s :Rectangle) :=cutoff s.box
abbrev terminal:Rectangle :=⟨1500,2093,441,60836,60836⟩
def FullPass {x :Input} (P:Poles x) (q:zI) :Prop :=
  ∀ g∈rectBank P terminal (rectCut terminal),g∈q.asIdeal
def PassFree {x :Input} (P:Poles x) (q:Ideal Ambient) :Prop :=
  ∀ i:afa,0< i.val → ∀ g∈P.rows (stages.get i).free (cutoff (stages.get i).free),
    iJ g∈q
structure Prefix (x :Input) (P:Poles x) (R:EarlyPicks x P) (O:OriginCover x P R) where
  book :Finset K
  book_bound:book.card≤prefixFee
  parents :Finset zI
  geometric : ∀ q∈parents,N5 q
  inherits : ∀ q∈parents,∃ f∈O.factors,∃ I∈O.parents f,
    q.asIdeal=I.comap iJ∧PassFree P I
  terminal_pass : ∀ q∈parents,FullPass P q
  Eh : ∀ γ∈x.Γ,γ∈book ∨ ∃ q∈parents,P6_7.axy x.M x.F q γ
def gw:List (ℕ×ℕ) :=
    [(2998,41985),(2990,44864),(2981,44729),(2973,44609),(2964,44474),(2956,44354),
    (2947,44219),(2939,44099),(2931,43979),(2923,43859),(2914,43724),(2906,43604),
    (2898,43484),(2890,43364),(2882,43244),(2874,43124),(2866,45871),(2856,45711),
    (2847,45567),(2837,45407),(2828,45263),(2819,45119),(2809,44959),(2800,44815),
    (2791,44671),(2782,44527),(2773,44383),(2764,44239),(2754,46834),(2744,46664),
    (2733,46477),(2723,46307),(2712,46120),(2702,45950),(2692,45780),(2682,45610),
    (2672,45440),(2661,47915),(2649,47699),(2637,47483),(2626,47285),(2615,47087),
    (2603,46871),(2592,46673),(2580,49038),(2567,48791),(2554,48544),(2541,48297),
    (2529,48069),(2516,50339),(2501,50039),(2487,49759),(2473,49479),(2459,51659),
    (2443,51323),(2428,51008),(2412,50672),(2395,52711),(2378,52337),(2359,54279),
    (2340,53842),(2320,55703),(2298,57474),(2273,59123),(2245,60836),(2215,60836),
    (2184,60836),(2151,60836),(2116,60836),(2080,60836),(2041,60836),(2001,60836),
    (1959,60836),(1915,60836),(1869,60836),(1821,60836),(1771,60836),(1719,60836),
    (1666,60836),(1610,60836),(1553,60836),(1493,60836),(1432,60836),(1368,60836),
    (1303,60836),(1236,60836),(1167,60836),(1096,60836),(1023,60836),(949,60836),
    (872,60836),(793,60836),(713,60836),(630,60836),(546,60836),(460,60836),
    (371,60836),(281,60836),(189,60836),(95,60836)]
abbrev jJ:=Fin gw.length
abbrev Test:=Option (jJ×Fin 2)
def seedCap (i:jJ) :=min terminal.z (gw.get i).1
def subWidth (i:jJ) :=min terminal.z (gw.get i).2
def Lc:Test→Rectangle
  | none=>terminal
  | some (i,a)=>if a=0 then {terminal with z :=subWidth i}
      else {terminal with t:=subWidth i}
def threshold :Test→ℕ
  | none=>gw.length+1
  | some (i,_)=>i.val+1
def direction :Test→Fin 2
  | none=>1
  | some (_,a)=>a
def apo:Test→ℕ
  | none=>0
  | some (i,_)=>seedCap i+1
def axisDegree (f :Equation) (a :Fin 2) :ℕ :=
  f.support.sup fun j=>(f.coeff j).degreeOf a
def amv (h:ℕ) (s :Rectangle) (q j:ℕ) :=
  s.m*dw+j-q*(131071-h)
def rectVolume (h:ℕ) (s :Rectangle) :ℕ :=
  (s.z+1)*(s.t+1)*ku s.box (amv h s)
def aWs (s :Rectangle) :ℕ :=
  Int.toNat (∑ q∈Finset.range (s.B+1),∑ j∈Finset.range (min q s.J+1),
    ((s.B+s.J-q-min q s.J+2*j:ℕ) :ℤ)*((s.B:ℤ)-2*q+j))
def rectDebit (h:ℕ) (s :Rectangle) :ℕ :=
  (s.z+1)*(s.t+1)*262144*ku s.box (fun q j=>s.m+min q s.J-(q+2*j)) +
    h*aWs s*(s.z+s.t+2)
def rectGain (h:ℕ) (s :Rectangle) (a :Fin 2) (E v :ℕ) :ℕ :=
  let (u,U) :=if a=0 then (s.t,s.z) else (s.z,s.t)
  let width i:=U+1-i*v
  (u+1)*ku s.box fun q j =>
    let g:=(q-j)/E
    let w:=amv h s q j
    (∑ i∈Finset.range g,(width i-width (i+1))*(w-2*h*(j+i))) +
      width g*(w-2*h*(j+g))
structure TerminalSource {x :Input} (P:Poles x) :Prop where
  floor : ∀ t:Test,rectVolume x.h (Lc t)≤ rectDebit x.h (Lc t) +
    ∑ W∈Finset.range (terminal.m*dw),Module.finrank FX (rectBank P (Lc t) W)
  shift : ∀ t:Test,∀ W,∀ g∈rectBank P (Lc t) W,∀ a r,
    cu.A5 a r g∈rectBank P (Lc t) (W+2*x.h*r)
def powerAt (h W:ℕ) :ℕ:=1+(rectCut terminal-W)/(2*h)
def Trace {x :Input} (P:Poles x) (t:Test) (f :Equation) :Prop :=
  ∀ W<terminal.m*dw,∀ g∈rectBank P (Lc t) W,g≠0 →
    f^(powerAt x.h W-g.natDegree)∣g.leadingCoeff
end
end P6_7_1
end
section
set_option autoImplicit true
namespace P6_7_2
open cu (Shape)
open P6_7 (RectTail)
structure b6 where
  hi:ℕ
  terminal:Shape
  dI:ℕ
  paidOrder :ℕ
  ordinateCap:ℕ
  retainedFee :ℕ
def Bs :RectTail→b6
  | .pruned=>⟨2381,⟨3700,5166,1087,178694⟩,22,2,100,0x11e59a8d6924aa8⟩
  | .tailOne=>⟨2392,⟨1500,2093,441,63549⟩,0,0,75,0x701c2279453828⟩
  | .tailTwo=>⟨2399,⟨1500,2093,441,57660⟩,0,0,75,0x65af187e7ef507⟩
  | .tailThree=>⟨2406,⟨1150,1604,338,53870⟩,0,0,75,0x7c00a4827e1b57⟩
abbrev Ls :=Fin 6
abbrev Aux :=Fin 13
def dI:Ls→ℕ := ![0,1,2,4,16,24]
private def freeWidth:RectTail→Ls→ℕ
  | .pruned => ![1139,1647,1029,1999,18884,3570]
  | .tailOne => ![1106,1580,1011,1927,15760,3495]
  | .tailTwo => ![1078,1525,997,1868,13777,3433]
  | .tailThree => ![1052,1475,983,1813,12243,3373]
private def movingWidth:RectTail→Ls→ℕ
  | .pruned => ![58597,64608,69761,80886,146546,237467]
  | .tailOne => ![53047,58422,63298,73452,133849,207445]
  | .tailTwo => ![49008,53928,58576,68013,124465,186885]
  | .tailThree => ![45557,50094,54529,63346,116350,170112]
def free (b:RectTail) (i:Ls) :Shape :=
  ⟨(![83,83,121,106,165,277] :Ls→ℕ) i,
    (![115,115,168,147,229,384] :Ls→ℕ) i,
    (![25,25,38,32,50,86] :Ls→ℕ) i,freeWidth b i⟩
def moving (b:RectTail) (i:Ls) :Shape :=
  ⟨(![812,880,982,1139,2164,2287] :Ls→ℕ) i,
    (![1131,1226,1368,1588,3017,3189] :Ls→ℕ) i,
    (![235,255,284,330,627,663] :Ls→ℕ) i,movingWidth b i⟩
def auxReserve :Aux→ℕ := ![5,6,10,8,13,13,16,20,20,1,4,24,24]
private def auxWidth:RectTail→Aux→ℕ
  | .pruned => ![2029,10309,4965,1888,2229,5452,3275,6236,2929,0,0,7052,7693]
  | .tailOne => ![1961,8625,4656,1846,2186,5135,3185,5934,2873,0,0,6721,7298]
  | .tailTwo => ![1906,7552,4417,1810,2150,4888,3110,5695,2826,0,0,6457,6985]
  | .tailThree => ![1854,6719,4202,1776,2115,4665,3040,5475,2781,0,0,6214,6699]
def auxiliary (b:RectTail) (i:Aux) :Shape :=
  if i=9 then free b 1 else if i=10 then free b 3 else
    ⟨(![115,103,137,151,200,158,200,207,256,0,0,235,233] :Aux→ℕ) i,
      (![159,143,190,210,277,218,277,287,354,0,0,327,324] :Aux→ℕ) i,
      (![35,31,41,46,61,48,61,63,81,0,0,71,70] :Aux→ℕ) i,auxWidth b i⟩
def cheapWidth:RectTail→ℕ
  | .pruned=>251
  | .tailOne=>252
  | .tailTwo=>252
  | .tailThree=>253
def strongWidth:RectTail→ℕ
  | .pruned=>500
  | .tailOne=>510
  | .tailTwo=>516
  | .tailThree=>523
abbrev jJ (b:RectTail) :=Fin (Bs b).ordinateCap
private def gradeCode :RectTail→ℕ
  | .pruned=>0xae81aba06072ae81aba060e1ae81aba0614fae81aba061baae81aba06223ae81aba0628aae81aba062eeae81aba06351ae81aba063b0ae81aba0640eae81aba06469ae81aba064c2ae81aba06519ae81aba0656eae81aba065c0ae81aba06610ae81aba0665dae81aba066a9ae81aba066f2ae81aba06738ae81aba0677dae81aba067bfae81aba067ffae81aba0683dae81aba06878ae81aba068b1ae81aba068e8ae81aba0691cae81aba0694fae81aba0697fae81aba069acae81aba069d89ab26ba069fa923eeba06a158e83eba06a2d8d26eba06a43891b2ba06a58877beba06a6b85d32ba06a7e84146ba06a9084f56ba06aa2831ceba06ab3812feba06ac381efeba06ad37feb2ba06ae27dea6ba06af27e8b6ba06b007c73eba06b0f7d116ba06b1d7daeeba06b2b7b7deba06b397c0ceba06b4679c6eba06b537a52aba06b607ade6ba06b6d7880eba06b7979096ba06b8679876ba06b92771daba06b9e7798aba06baa78096ba06bb578846ba06bc17601eba06bcc766feba06bd776e7eba06be37755eba06bee74bbaba06bf87526eba06c0375922ba06c0e75f3aba06c187355eba06c2373b4eba06c2d7413eba06c377472eba06c4174db6ba06c4c721b6ba06c557277eba06c5f72d46ba06c697327aba06c7273842ba06c7c70beeba06c86710feba06c8f7160eba06c9871b1eba06ca1720beba06cab725ceba06cb46f7e6ba06cbd6fcd2ba06cc6701beba06ccf706aaba06cd870b0aba06ce070ff6ba06ce9714e2ba06cf26e5deba06cfb6ea1eba06d036eee6ba06d0c6f326ba06d146f766ba06d1c6fc2eba06d257006eba06d2d
  | .tailOne=>0x3e0f4f83d0633e0f4f83d0c43e0f4f83d1233e0f4f83d17f3e0f4f83d1d83e0f4f83d22e3e0f4f83d2823e0f4f83d2d33e0f4f83d3223e0f4f83d36e3e0f4f83d3b73e0f4f83d3fd3e0f4f83d4413e0f4f83d4823e0f4f83d4c13e0f4f83d4fd3e0f4f83d5363e0f4f83d56d3e0f4f83d5a03e0f4f83d5d23e0f4f83d60032d20f83d6282ed84f83d63e2dd24f83d6512cb4cf83d6622b880f83d6722a4ccf83d6812aa7cf83d68f295b4f83d69d29ac8f83d6aa29fdcf83d6b72897cf83d6c328dfcf83d6cf2770cf83d6db27aa4f83d6e527e98f83d6f02828cf83d6fb26a64f83d70626dd4f83d710270ecf83d719274b4f83d72425b14f83d72d25e08f83d736260fcf83d73f26444f83d74926738f83d75226a2cf83d75b24f8cf83d7642520cf83d76c2548cf83d7742570cf83d77c259dcf83d78525c5cf83d78d25f2cf83d796242e4f83d79d24544f83d7a524758f83d7ac249b8f83d7b424bccf83d7bb24e2cf83d7c32508cf83d7cb252ecf83d7d323594f83d7da2378cf83d7e123984f83d7e823b34f83d7ee23d2cf83d7f523f24f83d7fc2411cf83d80324314f83d80a2450cf83d81124704f83d818248fcf83d81f22a58f83d82622bf0f83d82c
  | .tailTwo=>0x384f0e13c05a384f0e13c0b2384f0e13c108384f0e13c15b384f0e13c1ac384f0e13c1fb384f0e13c247384f0e13c290384f0e13c2d7384f0e13c31c384f0e13c35f384f0e13c39f384f0e13c3dc384f0e13c417384f0e13c450384f0e13c486384f0e13c4ba384f0e13c4ec384f0e13c51b384f0e13c547384f0e13c572384f0e13c59a384f0e13c5bf2ed7ce13c5da2c804e13c5ee2b870e13c6002a76ce13c6102957ce13c61f29b64e13c62d287f4e13c63a28d3ce13c64727930e13c65427d7ce13c65f2822ce13c66b26c9ce13c676270bce13c681274dce13c68c25e40e13c696261d8e13c6a026570e13c6aa26908e13c6b42514ce13c6bd25464e13c6c6257d4e13c6d025aece13c6d924278e13c6e224518e13c6ea2480ce13c6f324aace13c6fb24da0e13c70425040e13c70c2368ce13c7142390ce13c71c23b8ce13c72423dbce13c72b2403ce13c733242bce13c73b244ece13c7422476ce13c74a22c54e13c75122e68e13c7582307ce13c75f23290e13c766234a4e13c76d236b8e13c774238cce13c77b23ae0e13c78223d40e13c78a220c4e13c79022274e13c7962246ce13c79d2261ce13c7a3227cce13c7a9229c4e13c7b022b74e13c7b6
  | .tailThree=>0x349b8d26e06e349b8d26e0d9349b8d26e142349b8d26e1a7349b8d26e20a349b8d26e26a349b8d26e2c6349b8d26e320349b8d26e377349b8d26e3cb349b8d26e41c349b8d26e469349b8d26e4b5349b8d26e4fd349b8d26e542349b8d26e584349b8d26e5c3349b8d26e5ff349b8d26e639349b8d26e66f25b04d26e68d24804d26e6a2233b4d26e6b523948d26e6c62232cd26e6d6227dcd26e6e52106cd26e6f321494d26e7011fc7cd26e70f1ffdcd26e71b2033cd26e727206e4d26e7341ed40d26e7401f02cd26e74b1f318d26e7561f604d26e7611f8f0d26e76c1ddfcd26e7771e03cd26e7801e2bcd26e78a1e53cd26e7941e77cd26e79d1e9fcd26e7a71ec7cd26e7b11d00cd26e7bb1d1ecd26e7c31d408d26e7cc1d5e8d26e7d41d804d26e7dd1da20d26e7e61dc00d26e7ee1de1cd26e7f71e038d26e8001c22cd26e8091c3b4d26e8101c574d26e8181c6fcd26e81f1c8bcd26e8271ca44d26e82e1cc04d26e8361cd8cd26e83d1cf4cd26e8451d10cd26e84d1d2ccd26e8551d48cd26e85d1d64cd26e8651b5ecd26e86b1b758d26e8721b890d26e8781b9fcd26e87f1bb34d26e8851bca0d26e88c1be0cd26e8931bf44d26e8991c0b0d26e8a0
def seedCap {b:RectTail} (i:jJ b) :ℕ :=
  (gradeCode b >>> (48*i.val)) % 4096
structure sk where
  z :ℕ
  t:ℕ
def full (b:RectTail) :sk :=⟨(Bs b).terminal.U,(Bs b).terminal.U⟩
def Lc {b:RectTail} (i:jJ b) (kd:Fin 2) :sk :=
  let g:=gradeCode b >>> (48*i.val)
  let a :=(g >>> 12) % 262144
  let d:=(g >>> 30) % 262144
  if kd=0 then ⟨d,a⟩ else ⟨a,d⟩
end P6_7_2
end
