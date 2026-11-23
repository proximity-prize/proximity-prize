import ProximityPrize.SubmissionLower.ZbbSEle
import ProximityPrize.SubmissionLower.ZlfuKwd
import Mathlib.Data.Nat.Basic
import ProximityPrize.SubmissionLower.CmpCSum
import ProximityPrize.SubmissionLower.DT
import ProximityPrize.SubmissionLower.Z3BnLje
import ProximityPrize.SubmissionLower.ZPSk6xb
import ProximityPrize.SubmissionLower.ZQpU10d
import ProximityPrize.SubmissionLower.ZCuFj9c
import ProximityPrize.SubmissionLower.ZlyD2pd
import ProximityPrize.SubmissionLower.Zw0beKa
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.CD
import ProximityPrize.SubmissionLower.DG
import ProximityPrize.SubmissionLower.E2
import ProximityPrize.SubmissionLower.E4
import ProximityPrize.SubmissionLower.P6Defs
import ProximityPrize.SubmissionLower.Z2fdgla
import ProximityPrize.SubmissionLower.ZYswgKc
import ProximityPrize.SubmissionLower.Z409zke
import ProximityPrize.SubmissionLower.ZBRA0Kc
import ProximityPrize.SubmissionLower.ZCvigsb
import ProximityPrize.SubmissionLower.ZPfxqxd
import ProximityPrize.SubmissionLower.ZSWmOqa
import ProximityPrize.SubmissionLower.ZV6zyia
import ProximityPrize.SubmissionLower.ZZMyKHc
import ProximityPrize.SubmissionLower.ZaQt7ib
import ProximityPrize.SubmissionLower.Z7iuxgb
import ProximityPrize.SubmissionLower.ZXxMpWa
import ProximityPrize.SubmissionLower.ZPuXYRc
import ProximityPrize.SubmissionLower.Z1LucWb
set_option Elab.async false
section
section
set_option autoImplicit true
namespace qHo4MUb
open qqf9uAa (GradeSigns)
theorem proof :qqf9uAa.c7:= by
  intro b hlo hhi
  cases b
  case s7 =>
    exact ⟨ordinary3100,GradeSigns.append (GradeSigns.append grades3100A grades3100B) grades3100C⟩
  case sJ =>
    exact ⟨ordinary3200,GradeSigns.append (GradeSigns.append grades3200A grades3200B) grades3200C⟩
  case tv =>
    exact ⟨ordinary3400,GradeSigns.append grades3400A grades3400B⟩
  case uH=>exact ((Nat.not_lt_of_ge (by decide)) hhi).elim
  all_goals exact ((Nat.not_le_of_lt (by decide)) hlo).elim
end qHo4MUb
end
end
section
set_option autoImplicit true
namespace qSE9geb
theorem proof :P6_7_4.c1 :=qcsMxUc.proof
end qSE9geb
end
section
set_option autoImplicit true
namespace q57tTRd
theorem proof :P6_7_4.c2 :=qCgnalc.proof
end q57tTRd
end
section
set_option autoImplicit true
namespace qnUL4ue
open private guards from ProximityPrize.SubmissionLower.Zqb2cFb
theorem proof :P6_7_4.c5:= by
  intro b hb h12 h hl hu x
  apply qMHqmcc.checked (x :=x) hl (hu.trans (guards b).2.1.le)
  by_cases h4 :b.val<4
  · exact qd4jtSc.proof b hb h4 x
  by_cases h6:b.val<6
  · exact q3UL7Tb.proof b (by omega) h6 x
  by_cases h8:b.val<8
  · exact qyV6B3d.proof b (by omega) h8 x
  by_cases Kr :b.val<10
  · exact qgVOTOa.proof b (by omega) Kr x
  exact qJrKOKe.proof b (by omega) h12 x
end qnUL4ue
end
section
set_option autoImplicit true
namespace q3u9Tnc
noncomputable section
open Polynomial
open P6 (K)
open P5_7_2 (jX row seedCap)
open cu (Equation vm yq)
open qe6nVeb (SeedPlane immersedMarks Witness gap switch highRate numerator constantFee
  lowNumerator weightOK filterOK band_guards checked_grade ceil_bounds charge_mix)
def c1 :Prop :=
  ∀ (J:Input) (U:Finset K),U⊆J.CF → ∀ (B:DualWord J U)
    (e u:ℕ) (x :Witness),weightOK J.D e (switch J.D e u x)→filterOK J.D e u x →
    ∀ (f :Equation),Dt.Reduced f→f.natDegree=e→vm f u →
      (∀ γ∈U,yq f (J.model.label γ) (J.family.scalar γ)=0) →
      ∃ T⊆U,∃ s≤u,(U \ T).card≤ s*highRate e u x+e ∧
        Nonempty (LowSheets B T e (u-s) (switch J.D e u x))
def c2 :Prop :=
  ∀ (J:Input) (U:Finset K) (B:DualWord J U) (T:Finset K),T⊆U→U⊆J.CF →
    ∀ e h W,weightOK J.D e W→LowSheets B T e h W →
      ∀ q:SeedPlane,Irreducible q →
        gap J.D *(immersedMarks q (dcQ J) T).card ≤
          (h*numerator J.D e W+constantFee e*gap J.D)*q.totalDegree
def c3:Prop :=qe6nVeb.c4
private theorem injective_seeds (J:Input) :Function.Injective (dcQ J) := by
  intro γ η h
  have hz :=congrArg (fun w:Fin 2→cu.L=>w 0) h
  change algebraMap K cu.L (J.model.label γ) =
    algebraMap K cu.L (J.model.label η) at hz
  exact sub_left_inj.mp ((algebraMap K cu.L).injective hz)
private theorem count_low (h2 :c2) (h3:c3) {J U} (B:DualWord J U)
    {T e h W} (hT:T⊆U) (hU:U⊆J.CF) (hw:weightOK J.D e W)
    (sheets :LowSheets B T e h W) :
    3*gap J.D^2*T.card≤10*lowNumerator J.D e W h^2 := by
  let q:=gap J.D
  let a :=h*numerator J.D e W+constantFee e*q
  let b:=(a+q-1)/q
  have hq:0<q:=Nat.sub_pos_of_lt J.degree_hi
  obtain ⟨hlo,hhi⟩:=ceil_bounds a q hq
  have hb:0<b:= by
    have hp:0<a := by
      have he :0<e := by have :=hw.2.1; omega
      have hf :0<constantFee e :=Nat.mul_pos (by decide) (pow_pos he 2)
      exact (Nat.mul_pos hf hq).trans_le (Nat.le_add_left _ _)
    apply Nat.pos_of_ne_zero
    intro hz
    change a≤q*b at hlo
    simp [hz] at hlo
    omega
  have hc:=h3 _ T (injective_seeds J).injOn b hb (fun Q hQ=> by
    apply Nat.le_of_mul_le_mul_left _ hq
    calc
      q*(immersedMarks Q (dcQ J) T).card≤a*Q.totalDegree :=
        h2 J U B T hT hU e h W hw sheets Q hQ
      _≤(q*b)*Q.totalDegree :=Nat.mul_le_mul_right _ hlo
      _=q*(b*Q.totalDegree) := by ring)
  have hcost:q*b≤lowNumerator J.D e W h:= by
    exact hhi.trans_eq (by simp only [a,lowNumerator,q,Nat.add_mul,Nat.one_mul,Nat.add_assoc])
  calc
    _=q^2*(3*T.card) := by dsimp only [q]; ring
    _≤q^2*(10*b^2) :=Nat.mul_le_mul_left _ hc
    _=10*(q*b)^2 := by ring
    _≤_:=Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hcost 2)
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :P6_7_4.c6:= by
  intro b _ words del M Γ F hwin hshift H hH i f hf he h3e hpos hs T hT hr
  let D:=131071+(jX b).hi
  let e :=i.val+1
  let u:=seedCap b i
  obtain ⟨hlo,hDlo,hDhi⟩:=band_guards b
  have huw:0< u:=hpos.trans_le ((Qt.Qc _ _).mpr hs)
  obtain ⟨x,hw,hx,hfee⟩:=checked_grade b i (he ▸ h3e) huw
  let J:Input :=
    { words :=words,deleted:=del,model :=M,CF:=Γ,family :=F
      shift_not_mem:=hshift,block :=H,bY:=hH
      positive_height:= by have h:=hwin.1; omega
      D:=D,degree_lo:=hDlo,degree_hi:=hDhi
      degree := fun γ hγ=> by
        have hh:P1.FJ.iF M≤((jX b).hi:ℤ) :=hwin.2
        have hd: (P1.FJ.iF M).toNat≤(jX b).hi:= by omega
        exact (P6_7.aic F hγ).trans (Nat.add_le_add_left hd _) }
  obtain ⟨hcap,hfee₀,hfee₁⟩:=hfee
  rcases dual_word J T hT with hsmall | ⟨U,hU,houtside,⟨B⟩⟩
  · exact hsmall.trans ((Nat.le_add_left 1 e).trans hcap)
  obtain ⟨V,hV,s,hspent,hpaid,⟨sheets⟩⟩ :=
    h1 J U (hU.trans hT) B e u x hw hx f hf he hs (fun γ hγ=>hr γ (hU hγ))
  have hlow:=count_low h2 h3 B hV (hU.trans hT) hw sheets
  let W:=switch D e u x
  let den:=3*gap D^2
  let r :=highRate e u x
  let cap:=(row b).Z1-(e+1)
  have hm:den*(s*r)+10*lowNumerator D e W (u-s)^2≤den*cap :=
    charge_mix (a :=(constantFee e+1)*gap D) (b:=numerator D e W) huw hspent
      (by simpa only [lowNumerator,Nat.zero_mul,Nat.zero_add] using hfee₀) hfee₁
  have htotal:s*r+V.card≤ cap:= by
    apply Nat.le_of_mul_le_mul_left _ (show 0<den from
      Nat.mul_pos (by decide) (pow_pos (Nat.sub_pos_of_lt hDhi) _))
    rw [Nat.mul_add]
    exact (Nat.add_le_add (Nat.le_refl _) hlow).trans hm
  have hpart:=Finset.card_sdiff_add_card_eq_card hV
  have hpart' := Finset.card_sdiff_add_card_eq_card hU
  change (U \ V).card≤ s*r+e at hpaid
  dsimp only [cap] at htotal
  omega
end
end q3u9Tnc
end
section
set_option autoImplicit true
namespace q8kD5ec
theorem proof :P6_7_5.c2 :=
  qqf9uAa.of_children qWKyASa.proof qNKxb0a.proof q5HD6ae.proof
    qaYBFeb.proof q65qCJc.proof qsX8Fva.proof qHo4MUb.proof
end q8kD5ec
end
section
set_option autoImplicit true
namespace qCwf1nc
noncomputable section
open Polynomial Finset qkgz7gb
open P5 (K)
open P5_7_3 (cV)
open Dt (Reduced)
open cu (aZ yq)
open private cN9 from ProximityPrize.SubmissionLower.BJ
open private eLM from ProximityPrize.SubmissionLower.ZIbuJkc
open scoped Classical
def c1 :Prop :=qkgz7gb.c1
def c2 :Prop :=qkgz7gb.c2
def c3:Prop :=qkgz7gb.c4
private theorem restrictMarks {D word T z S} (m:UJ D word T z S)
    {U:Finset K} (hU:U⊆T) :UJ D word U z S:= by
  obtain ⟨h,hh,P,hP⟩:=m.poles
  exact ⟨m.Kw.mono hU,m.sections.mono hU,fun γ hg=>m.degree γ (hU hg),
    fun γ hg=>m.dw γ (hU hg),h,hh,P,fun γ hg=>hP γ (hU hg)⟩
theorem of_children (cut:c1) (smooth:c2) (singular :c3) :P6_7_5.c3:= by
  intro b word T z S m i f hf he hu hr
  obtain ⟨w,hw,hc,hB,hp,hfee⟩:=ready b i
  obtain ⟨low,high,G,hprod,hlo,_,hGd,hGs,hcop,hGr⟩ :=
    cut _ _ _ w hw T z S m.degree f hf he.le hu hr
  have hf₀:=ne_zero_of_natDegree_gt hf.1
  have dl:low∣f :=⟨high,hprod⟩
  have dh:high∣f :=⟨low,hprod.trans (mul_comm _ _)⟩
  obtain ⟨hls,hhs⟩:=cN9 hf₀ hu hprod
  have hlp:=isPrimitive_of_dvd hf.2.1 dl
  let gH :=T.filter fun γ=>yq high (z γ) (S γ)=0
  let Bp:=T \ gH
  have hpaid :gH⊆T:=filter_subset _ _
  have hkept:Bp⊆T:=sdiff_subset
  have roots (γ:K) (hγ:γ∈Bp) :yq low (z γ) (S γ)=0:= by
    have hv :=hr γ (hkept hγ)
    rw [hprod,yq,eval₂_mul] at hv
    exact (mul_eq_zero.mp hv).resolve_right fun h =>
      (mem_sdiff.mp hγ).2 (mem_filter.mpr ⟨hkept hγ,h⟩)
  have hhigh:=ePy (w.stock.cUr (cV b i).seedCap) (isPrimitive_of_dvd hf.2.1 dh)
    ((natDegree_le_of_dvd dh hf₀).trans he.le) hGd hhs hGs hcop hw.2.2.2.2.2
    gH z S (m.Kw.mono hpaid) (fun _ hγ=>(mem_filter.mp hγ).2) (fun γ hγ=>hGr γ (hpaid hγ))
  have hlow:Bp.card≤planeFee (smoothRate (wX b) (i.val+1) (cV b i).seedCap w.weight w.stock) := by
    by_cases hzero :low.natDegree=0
    · have hempty :=eq_empty_iff_forall_notMem.mpr fun γ hγ =>
        no_constant_root hlp hzero _ _ (roots γ hγ)
      simp [hempty]
    let ι:=algebraMap aZ (FractionRing aZ)
    have hsep: (f.map ι).Separable :=hf.2.2
    have hlr :Reduced low:=⟨Nat.pos_of_ne_zero hzero,hlp,hsep.of_dvd (Polynomial.map_dvd ι dl)⟩
    have ml:=restrictMarks m hkept
    exact eLM qCexLpd.proof singular ml.Kw hB hp
      (smooth _ _ _ _ _ hc word Bp z S ml low hlr
        ((natDegree_le_of_dvd dl hf₀).trans he.le) hls hlo roots)
  have hb:=Nat.add_le_add hlow hhigh
  rw [card_sdiff_add_card_eq_card hpaid,Nat.add_comm] at hb
  exact hb.trans hfee
end
end qCwf1nc
end
section
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace q67mtTa
open P6 (dw)
open P6_7_3 (Test lo hi gw terminal Lc j3)
open cu (FX triangle ku)
open DP (c69 ceG bga azS VY)
open agU (ad1 arY)
open private c4y from ProximityPrize.SubmissionLower.Zq1cNdd
open qZyoMPc (aP4)
open private auf bcT from ProximityPrize.SubmissionLower.A2
open private profile slice from ProximityPrize.SubmissionLower.ZgEngac
private theorem node_rank (u:ℕ) :ad1 { P5_7_1.terminal with U:=u } = 0xf8eab0e80000:= by
  let s := { P5_7_1.terminal with U:=u }
  have he :=czX.dei s (by decide :2*619≤2100) (by decide :2100+619≤2927+1)
  have hnum :262144*czX.a8x (2100-2*619) 619=6*0xf8eab0e80000:=rfl
  change 6*ad1 s= _ at he
  rw [show 262144*czX.a8x (s.m-2*s.J) s.J= _ from hnum] at he
  change ad1 s= _
  omega
private theorem scaled_terminal (u:ℕ) :
    aP4 2927 619 u=2880*(((u:ℤ)+1)*0x1cccacb1996 - 0x47c4a7d1ca8f0) := by
  simp only [aP4,auf,profile,slice,bcT,
    Nat.reduceAdd,Nat.reduceSub,Nat.cast_ofNat]
  ring
private theorem pole_terminal (u:ℕ) (hu:2927≤u) :
    let s := { P5_7_1.terminal with U:=u }
    P5_7_4.poleRank s≤triangle u*arY s+((u+1)*0x1cccacb1996 - 0x47c4a7d1ca8f0) := by
  let s := { P5_7_1.terminal with U:=u }
  have h:0x47c4a7d1ca8f0≤(u+1)*0x1cccacb1996 :=
    (by decide :0x47c4a7d1ca8f0≤(2927+1)*0x1cccacb1996).trans
      (Nat.mul_le_mul_right _ (Nat.succ_le_succ hu))
  refine qZyoMPc.bound s _ (by decide :619≤2927) hu ?_
  change aP4 2927 619 u≤2880*(↑((u+1)*0x1cccacb1996 - 0x47c4a7d1ca8f0) :ℤ)
  simp only [scaled_terminal,Nat.cast_sub h,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,
    le_refl]
private theorem grade_widths : ∀ g∈gw,2927≤g.2 := by
  rw [gw,List.forall_mem_append]
  constructor
  · repeat' refine List.forall_mem_cons.mpr ⟨by decide,?_⟩
    simp
  · intro g hg
    obtain ⟨_,_,rfl⟩:=List.mem_map.mp hg
    exact (by decide :2927≤185000)
private theorem tested_width (t:Test) :2927≤(Lc t).U:= by
  cases t with
  | none=>decide
  | some i =>
    exact le_min (grade_widths _ (List.get_mem _ _)) (by decide :2927≤185000)
theorem proof :P6_7_3.c1 := by
  intro x P t
  let h:=x.h
  let s :=Lc t
  let W:=s.m*dw-1
  have hs : { P5_7_1.terminal with U:=s.U } = s := by
    cases t <;> rfl
  obtain ⟨hl,hh⟩:=P6_7_3.emz x
  change lo≤h at hl
  change h≤hi at hh
  have hpos :0<h:=(by decide :0<lo).trans_le hl
  have hhi:h≤131070:=hh.trans (by decide)
  have hchar :h<K1.p:=hhi.trans_lt (by decide)
  obtain ⟨hm,hb,hj,_⟩:=P6_7_3.ctc t
  change s.m=2100 at hm
  change s.B=2927 at hb
  change s.J=619 at hj
  have hJ:s.J≤ s.B:= by rw [hj,hb]; decide
  have hU:s.B≤ s.U:=hb ▸ tested_width t
  have hB:s.B<K1.p:= by rw [hb]; decide
  have hW:W+1=s.m*dw:= by
    change s.m*dw-1+1=s.m*dw
    rw [hm]
    decide
  have hw:c69 h s W:= by
    intro q hq j _
    rw [hW,hm]
    apply Nat.le_trans (Nat.mul_le_mul hq (show 131071-h≤131071-lo by omega))
    rw [hb]
    exact Nat.le_trans (by decide :2927*(131071-lo)≤2100*dw) (Nat.le_add_right _ _)
  have hlocal:=qQCEOid.of_children qcsMxUc.proof qCgnalc.proof
  have hvol:=atp.bT9 (hhi.trans (by decide)) s W hw
  have hcontact :=atp.Yw h x.word s W
  have hpole :=c4y hlocal hpos hchar P.crt x.word s hJ hU hB W
  have hsum:=agU.telescope hhi P.crt x.word s W
  have hn:=node_rank s.U
  rw [hs] at hn
  have hphys :bga s=triangle s.U*0xf8eab0e80000:= by
    rw [← hn]
    unfold bga ad1
    rw [Nat.mul_assoc]
  rw [hphys] at hcontact
  have he :=pole_terminal s.U (tested_width t)
  dsimp only at he
  rw [hs] at he
  have hcap:=Nat.mul_le_mul_left (2*h) he
  rw [Nat.mul_add] at hcap
  have hcredit :2*h*(triangle s.U*arY s)=azS h s := by
    unfold arY azS
    ac_rfl
  rw [hcredit] at hcap
  change triangle s.U*ku s (fun q j=>s.m*dw+j-q*(131071-h)) ≤
    j3 h s + ∑ w∈Finset.range (s.m*dw),Module.finrank FX (VY P.crt x.word s w)
  have hv :ceG h s W =
      triangle s.U*ku s (fun q j=>s.m*dw+j-q*(131071-h)) := by
    unfold ceG
    rw [hW]
  rw [← hv,← hW]
  unfold j3
  omega
end q67mtTa
end
section
set_option autoImplicit true
namespace qFOgTpd
noncomputable section
open Polynomial
open P6 (K)
open P6_7_3
open cu (FX Jet L kr rD)
open DP (Source complete U4)
open pI (oU)
open akZ (btm)
abbrev last :=introductions.length
abbrev Intro:=Fin last
abbrev shape (i:Intro) :=(introductions.get i).2
abbrev dI (i:Intro) :=(introductions.get i).1
abbrev anchorRow {x :Input} {P:Poles x} (pick :Picks x.h P.rows) :=
  (pick.main ⟨0,by decide⟩).free
def Mark (x :Input) (f :Jet) (γ:K) :Prop :=
  rD f (x.M.label γ) (x.F.scalar γ)=0
structure Reference (x :Input) (P:Poles x) where
  raw:Source
  mem:raw∈complete P.crt x.word anchor.free (cutoff anchor.free)
  nonzero :U4 raw≠0
abbrev fixedContentFee :ℕ:=0x5c2981324afa
abbrev eHB:ℕ:=0xad5a910ff12
abbrev akj:ℕ:=0x471c0984879
abbrev projectionFee :ℕ:=0x4012119408aef
abbrev LineRow :=MvPolynomial (Fin 3) FX
def LineCaps (f :Jet) (g:LineRow) :Prop :=
  ∀ e∈g.support,e 1+e 2≤wD f 0∧e 2≤wD f 1∧e 0≤wD f 2
def LineRoot (x :Input) (g:LineRow) (γ:K) :Prop :=
  ∃ z :L,
    let v := ![algebraMap L FX z,kr (x.F.scalar γ),kr (x.F.scalar γ).derivative]
    MvPolynomial.eval v g=0∧MvPolynomial.eval v (MvPolynomial.pderiv 2 g)≠0
structure LastCut (x :Input) (S:Finset K) (f :Jet) where
  cut:Jet
  proper : ¬ f∣cut
  line :Bool
  row:LineRow
  caps :oU cut (if line then btm f else aOm f)
  separant:line=true→cut=f.derivative
  line_caps :line=true→LineCaps f row
  line_pos :line=true→0<wD f 2
  Eh : ∀ γ∈x.Γ,Mark x f γ →
    γ∈S∨Mark x cut γ∨(line=true∧LineRoot x row γ)
end
end qFOgTpd
end
section
set_option autoImplicit true
namespace qUrGXob
noncomputable section
open P6 (K p blockLength)
open P5_7 (midAgreement)
open P5_7_1 (Ls)
open qehP9ee (a3D asShape mixedCols kK MovingBox)
open P6_7_3 (Input Picks afa IntroIndex OriginCover introductions movingOrder stages cutoff terminal degree bgK introCap wD lineFee)
open cu (vP Jet Shape)
open gT (Ambient IZ iJ)
open pI (acW NO dual aaS pN weight)
open TD (GM J2 FP bCb bf7)
open scoped Classical BigOperators
abbrev Trial:=Fin 12
abbrev bAL:=Fin 13
abbrev moveStart:bAL:=8
abbrev au1 :ℕ:=0x684f0415973bd
abbrev pointFee :ℕ:=0x1922823d71
abbrev projectionFee :ℕ:=0x4cd5bb4d
abbrev dualFee :ℕ:=0x311510d3de338b1
abbrev stage (i:afa) :Ls :=stages.get i
def movingStage (i:Fin movingOrder.length) :afa :=
  ⟨movingOrder.get i,by fin_cases i <;> decide⟩
inductive TrialKind
  | free (i:afa)
  | moving (i:afa)
  | terminal
def trialKind (t:Trial) :TrialKind :=
  ([1,2,3,4,5,6,7].map (fun i:Fin 8=>TrialKind.free i) ++
    List.ofFn (fun i=>TrialKind.moving (movingStage i)) ++ [TrialKind.terminal]).get t
def aHp (t:Trial) :Shape :=
  match trialKind t with
  | .free i=>(stage i).free
  | .moving i=>a3D (stage i)
  | .terminal=>terminal
def inBank (rows :vP) (s :Shape) (I:Ideal Ambient) :Prop :=
  ∀ G∈rows s (cutoff s),iJ G∈I
def passes {h rows} (pick :Picks h rows) (t:Trial) (I:Ideal Ambient) :Prop :=
  match trialKind t with
  | .free i=>inBank rows (stage i).free I
  | .moving i=>inBank rows (stage i).free I∧inBank rows (stage i).moving I ∧
    aFX.aTw (pick.main i).free (pick.main i).moving I
  | .terminal=>inBank rows terminal I
structure bQX {h rows} (pick :Picks h rows) where
  free : ∀ i,NO (pick.main i).free (stage i).free
  moving : ∀ i,NO (pick.main i).moving (stage i).moving
def clean {h rows} {pick :Picks h rows} (R:bQX pick) (I:Ideal Ambient) :Prop :=
  ∀ j:Fin movingOrder.length,
    ¬ aaS (R.free (movingStage j)).equation I ∧
    ¬ aaS (R.moving (movingStage j)).equation I
def QV {x rows} {pick :Picks x.h rows} (R:bQX pick)
    {anchorRow :Jet} (O:OriginCover x anchorRow) (f :Jet) (s :bAL) :
    Finset (Ideal Ambient) :=
  (O.parents f).filter fun I=>clean R I∧(0<s.val→dual I) ∧
    ∀ t:Trial,t.val+1<s.val→passes pick t I
def stopped {x rows} {pick :Picks x.h rows} (R:bQX pick)
    {anchorRow :Jet} (O:OriginCover x anchorRow) (f :Jet) :bAL→Finset (Ideal Ambient) :=
  Fin.cases ((QV R O f 0).filter fun I => ¬ dual I)
    (fun t=>(QV R O f t.succ).filter fun I => ¬ passes pick t I)
def final {x rows} {pick :Picks x.h rows} (R:bQX pick)
    {anchorRow :Jet} (O:OriginCover x anchorRow) (f :Jet) :Finset (Ideal Ambient) :=
  (O.parents f).filter fun I=>clean R I∧dual I ∧ ∀ t,passes pick t I
abbrev onMark (x :Input) (I:Ideal Ambient) (γ:K) :Prop :=
  IZ I (x.M.label γ) (x.F.scalar γ)
def rankMarks (x :Input) (S:Finset (Ideal Ambient)) :Finset K :=
  x.Γ.filter fun γ => ∃ I∈S,onMark x I γ
def onCurves (x :Input) (C:acW) :Finset K :=
  x.Γ.filter fun γ => ∃ I∈C.qv,onMark x I γ
def originShape (o:IntroIndex) :Shape :=
  if h:o.val< introductions.length then (introductions.get ⟨_,h⟩).2
  else
    let v :=introCap o.val
    ⟨0,164+19*(v 0-1),50+19*(v 1-1),3037+19*v 2⟩
def originBox (o:IntroIndex) :GM:=kK (introCap o.val) (originShape o)
def resourceBill (v :IntroIndex→Fin 3→ℚ) :ℚ :=
  ∑ i:IntroIndex,∑ j:Fin 3,
    let old:=((List.ofFn v).take i.val).foldl (fun a w=>max a (w j)) 0
    (max (v i j) old - old)*introCap i.val j
abbrev lastOrigin :IntroIndex :=⟨introductions.length,Nat.lt_succ_self _⟩
def initialBound (k :Fin 4) :ℚ :=
  let v :=introCap lastOrigin.val
  resourceBill (fun o j=>mixedCols (originShape o) k j) +
    (![v 0,v 2,2*v 0*v 2,v 2*v 2] :Fin 4→ℕ) k
def bAW (s :bAL) :GM :=
  ((List.ofFn fun j=>stage (movingStage j)).take (s.val-moveStart.val)).foldl
    (fun a v=>bCb a (bf7 v.free v.moving v.dI true)) initialBound
def refShape (o:IntroIndex) :Shape :=
  asShape fun j=>max (introCap o.val j) (bgK (originShape o) j)
def freeBound (o:IntroIndex) (i:afa) :GM :=
  fun k=>kK (bgK (stage i).free) (refShape o) k/((stage i).dI+1 :ℚ)
def preMoving (o:IntroIndex) :GM:= fun k =>
  let v :=([1,2,3,4,5,6,7] :List (Fin 8)).foldl
    (fun a i=>min a (freeBound o i k)) (originBox o k)
  if o=lastOrigin then v*(∑ j,introCap o.val j:ℕ) else v
def MemberFits (o:IntroIndex) (t:Trial) (v :Fin 4→ℕ) :Prop :=
  (∀ k,((v k :ℕ) :ℚ)≤ min (originBox o k) (bAW t.succ k)) ∧
  ∀ j:Trial,j.val<t.val →
    match trialKind j with
    | .free i => ∀ k,((v k :ℕ) :ℚ)≤freeBound o i k
    | .moving i=>MovingBox (stage i) v
    | .terminal=>True
structure aAU where
  factors :Finset Jet
  origin :Jet→ IntroIndex
  line :Jet→Bool
  stops :Jet→bAL→GM
  nonneg : ∀ f∈factors,∀ s k,0≤ stops f s k
  spend_order : ∀ f∈factors,wD f 1≤wD f 0
  line_ok : ∀ f∈factors,line f=true →
    origin f=lastOrigin∧0<wD f 1∧0<wD f 2
  nested : ∀ i:IntroIndex,∀ j,
    (∑ f∈factors.filter (fun f=>i.val≤(origin f).val),wD f j)≤ introCap i.val j
  initial : ∀ f∈factors,∀ k,(∑ s :bAL,stops f s k) ≤
    kK (wD f) (if line f then asShape (wD f) else originShape (origin f)) k
  V8 : ∀ s k,(∑ f∈factors,∑ j:bAL,if s≤j then stops f j k else 0)≤bAW s k
  prefree : ∀ o k,(∑ f∈factors.filter (fun f=>origin f=o),
    ∑ j:bAL,if moveStart≤j then stops f j k else 0)≤preMoving o k
structure Geometry {x rows} {pick :Picks x.h rows} (R:bQX pick)
    {anchorRow :Jet} (O:OriginCover x anchorRow) :Prop where
  spend_order : ∀ f∈O.factors,wD f 1≤wD f 0
  line_ok : ∀ f∈O.factors,O.line f=true→O.origin f=lastOrigin
  initial : ∀ f∈O.factors,∀ k,(∑ s :bAL,J2 (stopped R O f s) k) ≤
    kK (wD f) (if O.line f then asShape (wD f) else originShape (O.origin f)) k
  V8 : ∀ s k,(∑ f∈O.factors,J2 (QV R O f s) k)≤bAW s k
  prefree : ∀ o k,(∑ f∈O.factors.filter (fun f=>O.origin f=o),
    J2 (QV R O f moveStart) k)≤preMoving o k
  rank : ∀ f∈O.factors,∀ I∈stopped R O f 0,∀ k,
    (pN I k :ℚ)≤ min (originBox (O.origin f) k) (initialBound k)
  member : ∀ f∈O.factors,∀ t:Trial,∀ I∈QV R O f t.succ,
    MemberFits (O.origin f) t (pN I)
def SS (bw:Fin 3) (t:Trial) :GM:= fun k=>weight (aHp t) bw k
def projectionBound:ℚ :=
  TD.XM 12 (fun n=>if h:n<12 then SS 0 ⟨n,h⟩ else 0)
    (fun n=>if h:n<12 then bAW (Fin.succ ⟨n,h⟩) else 0)
def rankPrice (o:IntroIndex) :GM :=
  let B:=min (originBox o 2) (initialBound 2)
  let J:=min (min (originBox o 1) (initialBound 1)) B
  let lam:=(blockLength:ℚ)/midAgreement
  let μ:=((blockLength-degree :ℕ) :ℚ)/(midAgreement-degree :ℕ)
  let φ:=if B=0 then 0 else 4*J-2*J*J/B
  ![0,4*lam*degree*B/10+μ,lam*degree*φ*9/10+B+1,0]
abbrev graphRate (g:ℕ) :ℚ:=((p+1 :ℕ) :ℚ)/g
abbrev gap:ℕ:=midAgreement-degree
def persistentRate (g:ℕ) :ℚ :=
  let a :=1+2*(blockLength:ℚ)/midAgreement*degree
  (2*(g:ℚ)-1)*a+((blockLength-degree :ℕ) :ℚ)/gap
def nativeRate (e g c W:ℕ) :ℚ :=
  max (e*(c+1)+e+g:ℕ)
    ((7+6*e :ℕ)+((2*e+1)*blockLength+(6*e-2)*W-3*e*e*degree :ℕ)/(gap:ℚ))
def NativeOK (e g c W M:ℕ) :Prop :=
  let E :=e+g
  let L:=(g+1)*c
  let j:=L/(c+1)
  0<c∧e*degree≤W∧M=W+1+j*degree∧E*degree<M ∧
    (c+1)*(degree*E*(E+1)/2+degree*j*(j+1)/2)<L*M ∧
    (2*e-1)*W-e*e*degree<p
def aSz (d a b:ℚ) :Prop :=
  0≤d∧d<(p:ℚ)∧max d (graphRate 55)≤a∧0≤b ∧
    ∀ e :ℕ,0<e→a<graphRate e →
      (1-a/graphRate e)*persistentRate e≤b ∨
      (e=1∧(1-a/graphRate e)*(1+3*(blockLength:ℚ)/gap)≤b) ∨
      (e=2∧16≤a ∧
        (13+8*(blockLength:ℚ)/gap)*(graphRate e-a)/(graphRate e-16)≤b) ∨
      (3≤e ∧ ∃ g c W M,NativeOK e g c W M ∧
        let a₀:=d/(3*(e :ℚ))+4*e+8
        a₀≤a∧nativeRate e g c W*(graphRate e-a)/(graphRate e-a₀)≤b)
def stopPrice (a b:IntroIndex→Trial→ℚ) (o:IntroIndex) (s :bAL) :GM :=
  Fin.cases (rankPrice o)
    (fun t k=>a o t*SS 0 t k+b o t*SS 1 t k) s
def lineCharge (f :Jet) (line :Bool) :ℚ :=
  ((if line then lineFee (wD f 0) (wD f 1) (wD f 2) else 0:ℕ) :ℚ)
structure cL where
  d:IntroIndex→Trial→ℚ
  a :IntroIndex→Trial→ℚ
  b:IntroIndex→Trial→ℚ
  bgt : ∀ o t,aSz (d o t) (a o t) (b o t)
  directional : ∀ o t v,0<v 0→MemberFits o t v →
    min projectionBound (FP (SS 0 t) (fun k=>v k))≤d o t
  projection :projectionBound≤(projectionFee :ℚ)
  bills : ∀ B:aAU,
    (∑ f∈B.factors,∑ t:Trial,FP (SS 0 t) (B.stops f t.succ))≤projectionBound ∧
    (∑ f∈B.factors,∑ t:Trial,FP (SS 2 t) (B.stops f t.succ))≤(pointFee :ℚ) ∧
    (∑ f∈B.factors,(lineCharge f (B.line f) +
      ∑ s :bAL,FP (stopPrice a b (B.origin f) s) (B.stops f s)))≤(dualFee :ℚ)
end
end qUrGXob
end
