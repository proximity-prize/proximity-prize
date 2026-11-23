import ProximityPrize.SubmissionLower.A
import ProximityPrize.SubmissionLower.B7
import ProximityPrize.SubmissionLower.D8
import ProximityPrize.SubmissionLower.ZEXP3Xa
import ProximityPrize.SubmissionLower.D9
import ProximityPrize.SubmissionLower.B6
import ProximityPrize.SubmissionLower.D3
import ProximityPrize.SubmissionLower.P6Defs
set_option Elab.async false
section
set_option autoImplicit true
section
namespace aas
noncomputable section
open Polynomial MvPolynomial

open cu (FX)

abbrev box (a b:ℕ) :=restrictBidegree (Fin 2) FX a b
abbrev aJ7 (a b:ℕ) :=bidegreeExponents (Fin 2) a b
end
end aas
end
section
namespace aas
noncomputable section
open Polynomial Finset MvPolynomial ProximityPrize.Benchmark
open scoped BigOperators
open P1 (K I node)


open private closedPoint from ProximityPrize.SubmissionLower.Z3EWiUc
abbrev point (a b:ℕ) (z :K→K) (S:K→K[X]) (γ:K) :=
 monomialPoint (aJ7 a b) (closedPoint (z γ) (S γ))
private def common (word:I→K) (U:Finset K) (S:K→K[X]) :Finset I:= by
 classical
 exact univ.filter fun j => ∀ γ∈U,(S γ).eval (node j)=word j
end
end aas
end
section
namespace baZ
noncomputable section


open cu (L FX)


open Polynomial MvPolynomial ProximityPrize.Benchmark
open scoped BigOperators
private abbrev center :FX:=algebraMap L[X] FX Polynomial.X
end
end baZ
end
end
section
set_option autoImplicit true
section
namespace I3
open P2 (K gJ)
structure dqk where
 loss :ℕ
 point :ℕ
 lowSeed :ℕ
 lowJet:ℕ
 fixedODE :ℕ
 content:ℕ
def DH :gJ→dqk
 | .h2366=>⟨0xe6b3eaec27b59e,116861997479,876521492288411,0x56be1fb3444b08,36093253508147,0xa1fdd7428d118⟩
 | .Yl=>⟨0xd7da5bf8c88f0f,120121004910,829961295151253,0x4de879ce710c0c,38156335697557,0xc1c5cf330d31a⟩
 | .l0=>⟨0xc6b4a89f175fc7,109202204960,799694610111234,0x485e6ef27fade1,38162053248458,0xaaaba8a2b00ec⟩
 | .kP=>⟨0xbc7c9b9657031f,104699174824,770778792970012,0x433817ba838782,38167770799362,0xa15a01828a7d0⟩
 | .kQ=>⟨0xa5ba4c54fdb8f8,97123092498,722456501538907,0x3b18e334b1c1cb,38170629574814,0x8e58a8d23dde6⟩
 | .sK=>⟨0x9cb474b0b21856,93759998288,701000287653402,0x37a9848876641b,38173488350263,0x879f6e6222c34⟩
 | .kV=>⟨0x94bd4cafbb617f,90729212514,681214547626267,0x34959ba46895ec,38179205901170,0x81f63f920bf0e⟩
 | .kY=>⟨0x87404a1f4947c2,85195986838,645116119073289,0x2f308330a8a181,38184923452070,0x78ccafa1e700c⟩
 | .k6=>⟨0x758eb498217dff,83000086975,662025405704944,0x31c479e61e3971,0xf2c595875ec,0x47b26231210ba⟩
 | .l6=>⟨0x5e4b20e28b35c9,69011616860,669088697639264,0x317453bda290fd,20449002605676,0x5a87db516cf96⟩
 | .lR=>⟨0x5983f69b1fa65f,66032709527,644707023796535,0x2df5a9db6692cd,20450533209213,0x57533981600d0⟩
 | .l7=>⟨0x558b7831bf250a,63238370539,621976647446251,0x2ad19314510d11,20452063812747,0x5476965154836⟩
 | .l8=>⟨0x51f9a34669c6b7,60755120886,601353539775450,0x280f3de3a3e9b1,20453594416286,0x51e2f7f14a202⟩
 | .l9=>⟨0x4e84c65cce1f0e,58467108221,582209142378665,0x2594081cdb76ce,20455125019829,0x4f8cfd5140b56⟩
 | .mj=>⟨0x4b9e28b8080ee5,56373526110,564581807971278,9954786551412656,20457420925133,0x4d6b98b1381ea⟩
 | .m7=>⟨0x472aaf21fc6be2,53546576365,540325845824095,9125660097229378,20458186226900,0x4a8ce1b12c8ca⟩
 | .nT=>⟨0x45d57c0c17186e,52658248135,532742661592927,8874696388329827,20459716830439,0x49ab408128ff0⟩
 | .n6=>⟨0x439cbe4dc4f079,50970254110,518285818376782,8404625238494599,20459869890795,0x4801aa61224b4⟩
 | .pA=>⟨0x3b853ec4c81753,40999001950,509967540456296,8290466690667268,0xa412293d4cb,0x3a9ab650ec436⟩
 | .qk=>⟨0x39728e0660aa1c,39735374243,496535567039145,7860731024967260,0xa4154d94007,0x38ec2a30e57ba⟩
 | .q8=>⟨0x379a1a2f6154c2,38629285775,484531166942327,7486267955628802,0xa41b45d2563,974868506867322⟩
 | .rq=>⟨0x34fe7b6ef44fd9,36645832014,463064299533725,6840117752241147,0xa424b2d6711,931142149428774⟩
 | .rC=>⟨0x2ffea917c48294,33932729865,433219494399691,5988634705221924,0xa42e1fda8c4,875181275646198⟩
 | .rN=>⟨0x2c32fc093909bf,31629138521,407570050254289,5302914379007106,0xa43dd58c0f0,830440701945066⟩
 | .rQ=>⟨0x275e48b17d4d87,28528772410,372306858653812,0xfb9c1fc0456d9,0xa44d8b3d91a,772383213031434⟩
 | .sY=>⟨0x2538de09cc6080,28080568800,355171717494870,0xe8fe110b23201,0xdbd1bc63251,637861062320844⟩
 | .s4=>⟨8211310618036248,21985174892,311688260461006,0xb1f1c7bb415a3,0xdd8f62edb28,552858659842848⟩
 | .s5=>⟨5779605417970943,12314607552,0xee2be809b958,0x7df0528da7cac,6697446031395,513713321237400⟩
 | .tI=>⟨5436736669042317,11736765360,0xe4b3000919da,0x74359e988b66f,6698445270597,492892057964352⟩
 | .s6=>⟨5241607407812057,11402680968,0xdf16cf08c0fd,0x6ea462987d7fa,6700943368600,480723593519778⟩
 | .tT=>⟨4808048251602143,10648967184,0xd25a7b07fa7c,0x62768f8ab1e4c,6703441466602,454901562246132⟩
 | .s7=>⟨0xc7502b3d30722,7490920973,0xd2908e0a77a5,0x625b531ead610,3531207081657,309090928848210⟩
 | .sJ=>⟨0xa5cb1b9af72be,6025297867,0xb0511707dd41,0x44ff90ff37330,3536466905213,282086355503694⟩
 | .tv=>⟨0x82cdf0c1351dd,4421538731,0x882efd053a65,724019902369272,3540543268468,0xe1ed17038ed2⟩
 | .uH=>⟨0x4a422f35fa09b,1753633570,0x7be5c104169b,600049872150299,776330431965,0x7af82001efc0⟩
 | .lZ=>⟨614847196277551,636562212,95856221147901,0xf56e7b7c9fc9,316305083107,76703300917566⟩
 | .om=>⟨0xf647043590b5,289460748,68753635351992,74267057961282,170921398682,43014701489592⟩
 | .wS=>⟨690577758626885,16792623,0xede8701079c,7526287483595,9222203107,8782771920948⟩
 | .vX=>⟨623583651015993,12641632,0xca10b00c3ae,5699400605080,9653236886,8307624386166⟩
 | .vg=>⟨43982042210628,665546,2475880882196,124630598996,366856679,888504582978⟩
 | .wI=>⟨19521532348308,168462,1163365714284,27841155795,212139586,568898617878⟩
 | .vW=>⟨18370950873948,147204,0xf414000810,23193953813,218022042,556114379274⟩
 | .wO=>⟨0xfa96e003f24,126954,933249418956,18816293570,223645947,543330140670⟩
 | .wQ=>⟨2627161033122,18700,485801067512,7907570234,14372295,202417111230⟩
structure ala (b:gJ) where
 loss :Finset K
 point :Finset K
 lowSeed :Finset K
 lowJet:Finset K
 fixedODE :Finset K
 content:Finset K
 bsg:loss.card≤(DH b).loss
 point_le :point.card≤(DH b).point
 lowSeed_le :lowSeed.card≤(DH b).lowSeed
 lowJet_le :lowJet.card≤(DH b).lowJet
 fixedODE_le :fixedODE.card≤(DH b).fixedODE
 content_le :content.card≤(DH b).content
noncomputable def ala.union {b} (B:ala b) :Finset K:= by
 classical exact B.loss∪B.point∪B.lowSeed∪B.lowJet∪B.fixedODE∪B.content
end I3
end
section
namespace I3
open P2 (dw)
abbrev wX:=Dt.wX
abbrev Er :=Dt.Er
def gap (hi:ℕ) :=dw - wX hi
def scale (hi:ℕ) :=dw*gap hi
end I3
end
section
namespace I3
noncomputable section
open Polynomial
open P2 (jG mJ K p node twist)
open cu (L j9)

open scoped BigOperators
def YQ {u del} (M:jG u del) {Γ} (F:mJ M Γ)
    (H :L[X]) :Prop :=
  let σ:=frobenius L p
  let H' := H.map σ
  H.Monic∧H.natDegree=M.iF.toNat∧H∣j9 M.E ∧
  H'.Monic∧H'.natDegree=M.iF.toNat∧H' ∣ j9 (M.E.map twist) ∧
  IsCoprime H H' ∧
  (∀ i,H.eval (algebraMap K L (node i))≠0∧H'.eval (algebraMap K L (node i))≠0) ∧
  IsCoprime (j9 (M.Q*M.factor*M.A₀)) H ∧
  IsCoprime ((j9 (M.Q*M.factor*M.A₀)).map σ) H' ∧
  ∀ γ∈Γ,
    let z :=algebraMap K L (M.label γ)
    let D:=j9 (M.factor*M.wK γ)
    let S:=j9 (F.scalar γ)
    IsCoprime D H∧IsCoprime (D.map σ) H' ∧
    H∣D *S+C z*j9 M.Q ∧
    H' ∣ D.map σ*S+C (z^p)*(j9 M.Q).map σ
abbrev Reduced:=Dt.Reduced
abbrev apb:=Dt.apb
end
end I3
end
end
section
open _root_ renaming Finset.range→aU,Finset.sum_add_distrib→ oj,Finset.sum_congr→lJ,Finset.sum_le_sum→nX,Finset.sum_sub_distrib→ oy,Int.natCast_nonneg→ oY,Module.finrank→ oD,Nat.le_div_iff_mul_le→ ox,Nat.le_of_lt_succ→ oZ,Nat.lt_succ_iff→ oz,Nat.mul_le_mul_left→nI,Nat.mul_le_mul_right→pz,Nat.sub_add_cancel→pC,Nat.succ_pos→ ov,P5_7.FarBand→nq,P5_7.farAgreement→cy,P5_7.terminal→lV,P5_7.threshold→lI,Polynomial.coeff_natDegree→ oq,cu.Shape→c9,cu.slots→lz,mul_le_mul_of_nonneg_left→ oK
section
set_option autoImplicit true
namespace P5_7
noncomputable section
open Polynomial

open cu (Equation vm)

open Qt (gY Qc)
theorem aRe {b:nq} {w:ℤ} (hw:InFar b w) :
  b.row.lo≤w.toNat∧w.toNat≤b.row.hi:= by
 obtain ⟨hl,hh⟩:=hw
 omega
theorem ctc (b:nq) (x :Test b) :
   Jr b (Lc b x)∧(Lc b x).shape.m=(lV b).shape.m ∧
   (Lc b x).shape.B=(lV b).shape.B∧(Lc b x).shape.J=(lV b).shape.J ∧
   (Lc b x).shape.U≤(lV b).shape.U:= by
 cases x with
 | none=>exact ⟨Or.inl rfl,rfl,rfl,rfl,le_rfl⟩
 | some i=>exact ⟨Or.inr (Or.inr ⟨i,rfl⟩),rfl,rfl,rfl,grade_slots b i⟩
theorem eiO {b:nq} {f :Equation} (hp:0<f.natDegree)
   (reject : ∀ x :Test b,lI b x≤f.natDegree →
     apo b x≤gY f→False) :
   ∃ i:aKj b,f.natDegree=i.val+1∧vm f (cV b i).seedCap:= by
 have he :f.natDegree≤b.row.gw.length:= by
   by_contra! hlo
   exact reject none hlo (Nat.zero_le _)
 let i:aKj b:=⟨f.natDegree-1,by omega⟩
 have hidx :f.natDegree=i.val+1 := by dsimp [i]; omega
 refine ⟨i,hidx,(Qc _ _).mp ?_⟩
 by_contra! hlow
 exact reject (some i) hidx.ge hlow
end
end P5_7
end
section
set_option autoImplicit true
namespace P5_7
noncomputable section
open Finset Polynomial MvPolynomial
open cu (ku Equation FX Jet triangle vm)
open qQ (oU)
open Qt (aH3 gY bg4)
open baY (Bp)
open private bKE from ProximityPrize.SubmissionLower.D8
open private cer cTX from ProximityPrize.SubmissionLower.D8
open private ddI from ProximityPrize.SubmissionLower.A1
open private bGH Wb from ProximityPrize.SubmissionLower.A0
def aT2 (h:ℕ) (s :c9) (E v W:ℕ) :ℕ :=
  ku s fun q j =>
    if q*(131071-h)≤W+j then
      Bp s.U v ((q-j)/E) (ahs h s W - j)
    else 0
private def b4O (h:ℕ) (s :c9) (E v W j:ℕ) :ℕ :=
 let r :=ahs h s W - j
 (aH3 (131071-h) s.B W j - r*E)*lz s.U (r*v)
private theorem cJb (h:ℕ) (s :c9) (E v W:ℕ)
  (hk :0<131071-h) (he :0<E) :
  (∑ j∈aU (s.J+1),b4O h s E v W j)=aT2 h s E v W:= by
 rw [aT2,← ddI]
 apply lJ rfl
 intro j _
 exact cTX _ _ _ _ _ _ _ _ hk he
set_option backward.isDefEq.respectTransparency false in
theorem boi (h:ℕ) (s :c9) (E v W:ℕ) (V:Submodule FX Jet)
    {f :Equation} (hf :f≠0) (hE :E≤f.natDegree) (hv :v≤gY f)
    (hk :0<131071-h) (he :0<E)
    (hcaps : ∀ P∈V,oU P s)
    (hlead : ∀ P∈V,P≠0 →
      (P.leadingCoeff.natDegree+P.natDegree)*(131071-h)≤W+P.natDegree)
    (hdvd : ∀ P∈V,P≠0→f^(ahs h s W-P.natDegree)∣P.leadingCoeff) :
    oD FX V≤aT2 h s E v W:= by
  have hrow {P:Jet} (hP:P∈V) (hn:P≠0) :
      P.leadingCoeff.natDegree+P.natDegree≤ s.B∧P.natDegree≤ s.J ∧
      vm P.leadingCoeff s.U:= by
    have ha : (P.coeff P.natDegree).coeff P.leadingCoeff.natDegree≠0:= by
      rw [oq,oq]
      exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn)
    obtain ⟨hB,hJ,_⟩:=hcaps P hP _ _ ha
    refine ⟨hB,hJ,fun i => ?_⟩
    by_cases hi:P.leadingCoeff.coeff i=0
    · simp [hi]
    · rw [← oq] at hi ⊢
      exact (hcaps P hP _ _ hi).2.2
  rw [← cJb h s E v W hk he]
  refine bGH (F:=FX) (A:=Equation) V (b4O h s E v W)
    (s.J+1) ?_ ?_
  · intro j
    let r :=ahs h s W - j
    apply cer _ (g:=f^r) (pow_ne_zero r hf)
    · rw [Polynomial.natDegree_pow]
      exact nI _ hE
    · rw [bg4 hf]
      exact nI _ hv
    · rintro c ⟨⟨P,hP⟩,rfl⟩ hc
      change P.coeff j≠0 at hc
      obtain ⟨hpV,hd⟩:=Wb.mp hP
      have hn:P≠0:= by
        intro hz
        exact hc (by simp [hz])
      have hj:P.natDegree=j :=
        le_antisymm (oZ ((natDegree_lt_iff_degree_lt hn).2 hd))
          (le_natDegree_of_ne_zero hc)
      obtain ⟨hB,_,hseed⟩:=hrow hpV hn
      have hwidth :=hlead P hpV hn
      have hdiv :=hdvd P hpV hn
      rw [hj] at hB hwidth hdiv
      change (P.coeff j).natDegree<_∧vm (P.coeff j) _∧_∣P.coeff j
      rw [← hj,oq,hj]
      refine ⟨?_,hseed,hdiv⟩
      have hd:=(ox hk).2 hwidth
      unfold aH3
      omega
  · intro P hp
    by_cases hn:P=0
    · simp [hn]
    · exact (natDegree_lt_iff_degree_lt hn).1 (Nat.lt_succ_of_le (hrow hp hn).2.1)
theorem bDM (h:ℕ) (s :c9) (E v :ℕ) (hh:0<2*h) (hk :1≤131071-h) :
    (∑ W∈aU (s.m*cy),aT2 h s E v W)+ZN h s E v =
      triangle s.U*ku s (fun q j=>s.m*cy+j-q*(131071-h)) := by
  have hswap (F:ℕ→ℕ→ℕ→ℕ) :
      (∑ W∈aU (s.m*cy),ku s (F W)) =
        ku s (fun q j => ∑ W∈aU (s.m*cy),F W q j) := by
    unfold ku
    rw [sum_comm]
    apply lJ rfl
    intro q _
    rw [sum_comm]
  simp only [aT2,ZN]
  rw [hswap]
  simp only [ku,← oj,mul_sum]
  apply lJ rfl
  intro q _
  apply lJ rfl
  intro j hj
  have hjq:j≤q:=(oZ (mem_range.mp hj)).trans (min_le_left _ _)
  have hq:q≤q*(131071-h) := by simpa using nI q hk
  exact bKE (s.m*cy) (2*h) (q*(131071-h)) j s.U v ((q-j)/E)
    (hjq.trans hq) hh
theorem eqx {b:nq} {h:ℕ} (hh:0<2*h) (hk :0<131071-h)
   (x :Test b) {rows f} (hf :f≠0) (ht:bAN h (Lc b x) rows f)
   (htop:0<(Lc b x).shape.m*cy)
   (hwidth : (Lc b x).shape.B*(131071-h)≤(Lc b x).shape.m*cy)
   (hE :lI b x≤f.natDegree) (hv :apo b x≤gY f) :
   ZN h (Lc b x).shape (lI b x) (apo b x)≤j3 h (Lc b x) := by
 have he :0<lI b x := by cases x <;> exact ov _
 let t:=Lc b x
 let top:=t.shape.m*cy
 have htopPos :0<top:=htop
 have hbWidth:t.shape.B*(131071-h)≤top:=hwidth
 have htopSub:top-1+1=top:= by omega
 have hraw : ∀ q≤t.shape.B,∀ j≤ min q t.shape.J,
     q*(131071-h)≤top-1+1+j:= by
   intro q hq j _
   rw [htopSub]
   exact (pz _ hq).trans (hbWidth.trans (by omega :top≤top+j))
 have hmin:=ht.ajB (top-1) (show top-1<top by omega) hraw
 change triangle t.shape.U*ku t.shape (fun q j=>top-1+1+j-q*(131071-h)) ≤
   j3 h t + ∑ W∈aU (top-1+1),oD FX (rows t.shape W) at hmin
 rw [htopSub] at hmin
 have hmax : (∑ W∈aU top,oD FX (rows t.shape W)) ≤
     ∑ W∈aU top,aT2 h t.shape (lI b x) (apo b x) W:= by
   apply nX
   intro W hW
   exact boi h t.shape _ _ W _ hf hE hv hk he
     (ht.shape W) (ht.leading W) (ht.divides W (mem_range.mp hW))
 have htotal:=bDM h t.shape (lI b x) (apo b x) hh hk
 change (∑ W∈aU top,aT2 h t.shape (lI b x) (apo b x) W) +
   ZN h t.shape (lI b x) (apo b x) =
   triangle t.shape.U*ku t.shape (fun q j=>top+j-q*(131071-h)) at htotal
 change ZN h t.shape (lI b x) (apo b x)≤j3 h t
 omega
end
end P5_7
end
section
set_option autoImplicit true
namespace P5_7
noncomputable section
open Polynomial
open P5 (K I)


def c6:Prop :=
  ∀ (b:nq) h,b.row.lo≤h→h≤b.row.hi → ∀ x :Test b,
    j3 h (Lc b x)<ZN h (Lc b x).shape (lI b x) (apo b x)
def c7:Prop :=
  ∀ (D e H rate :ℕ),NativeGuard D e rate →
    ∀ (word:I→K) (T:Finset K) (z :K→K) (S:K→K[X]),
      Set.InjOn z (T:Set K)→Set.InjOn S (T:Set K) →
      (∀ γ∈T,(S γ).natDegree≤D) →
      (∀ γ∈T,∃ lg:Finset I,cy≤lg.card ∧
        ∀ i∈lg,(S γ).eval (P5.node i)=word i) →
      ∀ g:OneSeedEquation,g≠0→ g.natDegree≤e→NativeSeedBound g H →
      (∀ γ∈T,atNative g (z γ) (S γ)=0)→T.card≤nativeFee D e H rate
end
end P5_7
end
section
set_option autoImplicit true
namespace P5_7_6
open Finset cu P5_7
open Y2 (Tb)
open private deJ crN diagonal from ProximityPrize.SubmissionLower.D9
def width (s :c9) (h q j t:ℕ) :ℤ :=
 (s.m*cy :ℕ)+(j:ℤ)-(131071-(h:ℤ))*q - 2*(h:ℤ)*t
private theorem biL (s :c9) (h q j t:ℕ) (hh:h≤131071) :
   (↑(s.m*cy+j-q*(131071-h)-2*h*t:ℕ) :ℤ)=max 0 (width s h q j t) := by
 rw [Nat.sub_sub]
 have hd: (↑(131071-h:ℕ) :ℤ)=131071 - h:=Nat.cast_sub hh
 have he : (↑(s.m*cy+j:ℕ) :ℤ)-(↑(q*(131071-h)+2*h*t:ℕ) :ℤ) =
     width s h q j t:= by
   simp only [width,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,hd]
   ring
 generalize s.m*cy+j=x at *
 generalize q*(131071-h)+2*h*t=y at *
 by_cases hxy :y≤x
 · rw [Int.ofNat_sub hxy,he,max_eq_right (by omega)]
 · have hz :x-y=0:=Nat.sub_eq_zero_of_le (by omega)
   rw [hz,Int.ofNat_zero,max_eq_left (by omega)]
def O3 (s :c9) (E v :ℕ) (f :ℕ→ℕ→ℕ→ℤ) :ℤ :=
  ∑ q∈aU (s.B+1),∑ j∈aU (min q s.J+1),
    let g:=(q-j)/E
    let c:= fun a=>lz s.U (a*v)
    (∑ a∈aU g,((c a - c (a+1) :ℕ) :ℤ)*f q j (j+a)) +
      (c g:ℤ)*f q j (j+g)
theorem gain_eq (s :c9) (h E v :ℕ) (hh:h≤131071) :
  (ZN h s E v :ℤ)=O3 s E v (fun q j t=>max 0 (width s h q j t)) := by
 simp only [ZN,ku,O3,Nat.cast_sum,Nat.cast_add,Nat.cast_mul,biL _ _ _ _ _ hh]
theorem gain_le (s :c9) (E v :ℕ) {f g:ℕ→ℕ→ℕ→ℤ}
   (hf : ∀ q j t,f q j t≤g q j t) :O3 s E v f≤O3 s E v g:= by
 unfold O3
 apply nX
 intro q _
 apply nX
 intro j _
 dsimp only
 apply add_le_add
 · exact nX fun a _=>oK (hf _ _ _) (oY _)
 · exact oK (hf _ _ _) (oY _)
theorem gain_add (s :c9) (E v :ℕ) (f g:ℕ→ℕ→ℕ→ℤ) :
  O3 s E v (fun q j t=>f q j t+g q j t)=O3 s E v f+O3 s E v g:= by
 unfold O3
 rw [← oj]
 apply lJ rfl
 intro q _
 rw [← oj]
 apply lJ rfl
 intro j _
 simp only [mul_add,oj]
 ring
def phase (s :c9) (E v d:ℕ) (f :ℕ→ℕ→ℕ→ℤ) :ℤ :=
  ∑ t∈aU (s.J+Tb s E v),∑ a∈Ico (t-s.J) (min t (Tb s E v-1)+1),
    (lz s.U ((a+d)*v) :ℤ) * ∑ q∈Ico (t-a+E*(a+d)) (s.B+1),f q (t-a) t
private theorem eNa (s :c9) (E v q j:ℕ) (f :ℕ→ℕ→ℕ→ℤ)
    (he :0<E) (hq:q≤ s.B) (hj:j≤q) :
    let c:= fun a=>lz s.U (a*v)
    let g:=(q-j)/E
    let w:= fun d a=>(c (a+d) :ℤ)*f q j (j+a)
    (∑ a∈aU g,((c a - c (a+1) :ℕ) :ℤ)*f q j (j+a))+c g*f q j (j+g) =
      (∑ a∈aU (Tb s E v),if j+E*(a+0)≤q then w 0 a else 0) -
      (∑ a∈aU (Tb s E v),if j+E*(a+1)≤q then w 1 a else 0) := by
  dsimp only
  let g:=(q-j)/E
  let w:= fun d a=>(lz s.U ((a+d)*v) :ℤ)*f q j (j+a)
  have hs (a :ℕ) :
      (↑(lz s.U (a*v) - lz s.U ((a+1)*v) :ℕ) :ℤ) =
        (lz s.U (a*v) :ℤ) - lz s.U ((a+1)*v) :=
    Int.ofNat_sub (deJ _ (pz v (by omega)))
  simp only [hs,sub_mul,oy]
  change (∑ a∈aU g,w 0 a)-(∑ a∈aU g,w 1 a)+w 0 g= _
  rw [sub_add_eq_add_sub,← sum_range_succ]
  have hz (d a :ℕ) (ha :Tb s E v≤a) (hg:a+d≤g) :w d a=0:= by
    have hcap:g≤ s.B/E :=Nat.div_le_div_right (by omega)
    unfold Tb at ha
    split at ha
    · omega
    · rename_i hv
      have hlarge :s.U/v<a+d:= by omega
      have hout:s.U<(a+d)*v := by
        by_contra! hm
        exact (not_le_of_gt hlarge) ((ox (Nat.pos_of_ne_zero hv)).2 hm)
      simp [w,lz ,Nat.not_le_of_lt hout]
  have hdiv (a d:ℕ) :j+E*(a+d)≤q↔a+d≤g:= by
    rw [ox he,Nat.mul_comm (a+d) E]
    omega
  rw [crN (g+1) _ (fun a ha hb=>hz 0 a ha (by omega)),
    crN g _ (fun a ha hb=>hz 1 a ha (by omega))]
  have hzero (a :ℕ) :j+E*a≤q↔a≤g:= by simpa using hdiv a 0
  simp only [hzero,Nat.add_zero,oz ,Nat.add_one_le_iff,w]
private def bty (s :c9) (E v d:ℕ) (f :ℕ→ℕ→ℕ→ℤ) :ℤ :=
 ∑ q∈aU (s.B+1),∑ j∈aU (s.J+1),∑ a∈aU (Tb s E v),
   if j+E*(a+d)≤q then (lz s.U ((a+d)*v) :ℤ)*f q j (j+a) else 0
private theorem c30 (s :c9) (E v d q:ℕ) (f :ℕ→ℕ→ℕ→ℤ) :
   (∑ j∈aU (min q s.J+1),∑ a∈aU (Tb s E v),
     if j+E*(a+d)≤q then (lz s.U ((a+d)*v) :ℤ)*f q j (j+a) else 0) =
   ∑ j∈aU (s.J+1),∑ a∈aU (Tb s E v),
     if j+E*(a+d)≤q then (lz s.U ((a+d)*v) :ℤ)*f q j (j+a) else 0:= by
 apply sum_subset (range_mono (Nat.succ_le_succ (min_le_right _ _)))
 intro j hj hnot
 simp only [mem_range,oz ,le_min_iff] at hj hnot
 apply sum_eq_zero
 intro a _
 rw [ite_eq_right (by omega)]
private theorem c3Z (s :c9) (E v d:ℕ) (f :ℕ→ℕ→ℕ→ℤ) :
   bty s E v d f=phase s E v d f := by
 have hR:Tb s E v-1+1=Tb s E v := by
   apply pC
   unfold Tb
   split
   · exact ov _
   · exact le_min (ov _) (ov _)
 unfold bty phase
 rw [sum_comm]
 conv_lhs =>
   enter [2,j]
   rw [sum_comm]
 conv_lhs =>
   rw [← hR]
   rw [diagonal]
 rw [Nat.add_assoc,hR]
 apply lJ rfl
 intro t _
 apply lJ rfl
 intro a ha
 have hta :t-a+a=t:=pC (by have :=(mem_Ico.mp ha).2; omega)
 rw [mul_sum,← sum_filter]
 have hf : (aU (s.B+1)).filter (fun q=>t-a+E*(a+d)≤q) =
     Ico (t-a+E*(a+d)) (s.B+1) := by
   ext q
   simp only [mem_range,mem_filter,mem_Ico]
   tauto
 rw [hf,hta]
theorem gain_phases (s :c9) (E v :ℕ) (f :ℕ→ℕ→ℕ→ℤ)
  (he :0<E) :O3 s E v f=phase s E v 0 f - phase s E v 1 f := by
 rw [← c3Z s E v 0 f,← c3Z s E v 1 f]
 unfold O3 bty
 rw [← oy]
 apply lJ rfl
 intro q hq
 rw [← c30 s E v 0 q,← c30 s E v 1 q,← oy]
 apply lJ rfl
 intro j hj
 rw [mem_range,oz] at hq hj
 exact eNa s E v q j f he hq (hj.trans (min_le_left _ _))
end P5_7_6
end
end
