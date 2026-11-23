import ProximityPrize.SubmissionLower.ZE36Kga
import ProximityPrize.SubmissionLower.ZQGI7be
import ProximityPrize.SubmissionLower.ZHNB5Ae
import ProximityPrize.SubmissionLower.Z3ozsyb
import ProximityPrize.SubmissionLower.Zm2Uhnd
import ProximityPrize.SubmissionLower.Zybrlmc
import ProximityPrize.SubmissionLower.Zqby9gc
set_option Elab.async false
open _root_ renaming Finset → zJe, IsFractionRing.injective → zxb, MvPolynomial.constantCoeff → zuE, MvPolynomial.eval → zY9, MvPolynomial.eval_C → z9X, Nat.pos_of_ne_zero → zOl, Nat.zero_le → zD0
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace qAFIJ5c
noncomputable section
open Polynomial q7IA62d
open P6 (K p jG)
open P6_7_4 (wordLift)
open q6nKpZc (Input TopPair)
open P5_7_2 (A fO row)
open cu (L j9 jz)
open DP (ad0 Z7)
open aR (jet cK)
open jA (jK mA kS qV ED jW bC)
open Rk (JX aPU a04 c6X)
open private residue marked_residue specialize_pole raw_cut evaluated_degree from ProximityPrize.SubmissionLower.ZHNB5Ae
open private d2J from ProximityPrize.SubmissionLower.S
open private conjugate conjugate_caps efL σF_seed eval_conjugate conjugate_noMoving from ProximityPrize.SubmissionLower.ZQIEUqa
def yq {u del} {M:jG u del} {Γ} (F:P1.bje A M Γ)
    (i:Fin 2) (γ:K) :jK →ₗ[L] kS :=
  ((MvPolynomial.aeval (ED (jz (M.label γ)^(p^i.val))
    (jW (j9 (F.scalar γ))))).toLinearMap.restrictScalars L).comp
    acZ.Bu
theorem atMark_apply {u del M Γ} (F:P1.bje A M Γ) (i:Fin 2) (γ:K)
    (P:jK) :yq (u:=u) (del:=del) F i γ P =
    zY9 (ED (jz (M.label γ)^(p^i.val))
      (jW (j9 (F.scalar γ)))) (bC P) :=rfl
theorem source_zero {b u del M Γ F} (x : @Input b u del M Γ F)
    (hh:0<M.iF.toNat) {e :Bool} {γ:K} (hγ:γ∈Γ)
    {W:ℕ} (hW:W≤ cutoff (profile b e)) :
    source x.crt (wordLift M) (profile b e) W≤LinearMap.ker (yq F 0 γ) := by
  intro P hP
  let t:=profile b e
  let h:=M.iF.toNat
  let r :=t.shape.B+t.shape.J
  let H :=x.D.block 0
  let z :=Z7 (M.label γ) 0
  let S:=j9 (F.scalar γ)
  let res :=residue x.crt z
  let mark :=F.mark γ hγ
  have hs :res.natDegree≤h:=(natDegree_C_mul_le _ _).trans
    (natDegree_map_le.trans (oneNumerator_small x.crt hh).le)
  have hS:S.natDegree≤131071+h:=(natDegree_map _).trans_le (P6_7.aic F hγ)
  obtain ⟨hz,T,hT⟩:=marked_residue x.crt (x.residues γ hγ)
  change S - res=H*T at hT
  have hST:S=H*T+res :=sub_eq_iff_eq_add.mp hT
  have hTd:T.natDegree≤131071 := by
    by_cases he :T=0
    · simp [he]
    have hd:=(natDegree_sub_le S res).trans (max_le hS (hs.trans (Nat.le_add_left _ _)))
    rw [hT,natDegree_mul (x.D.monic 0).ne_zero he,x.D.degree 0] at hd
    omega
  simp only [source,Submodule.mem_inf] at hP
  obtain ⟨Q,hQ⟩:=specialize_pole x.crt r P z hz (mem_poleSpace.mp hP.2.2)
  have hraw:a04 W Q:=raw_cut hs (mem_ambient.mp hP.1).2.2.2.2 hQ
  have hphys : ∀ i,P∈ays t (ad0 i) (wordLift M i) := by
    simpa only [amm,Submodule.mem_iInf] using hP.2.1
  have hc:=c6X t.shape.m M.word H res z r P Q (x.units 0)
    (fun i=>bsz.mp (hphys i)) hQ
  have hpos :0<t.shape.m:= by
    unfold t profile P5_7_2.topDonors
    cases e <;> simp <;> split <;> decide
  have hlt: (cK Q T).natDegree<t.shape.m*mark.bad.support.card:= by
    have hv :=Nat.mul_le_mul_left t.shape.m mark.bad.dw
    have hp:=Nat.mul_pos hpos (show 0<A by decide)
    change W≤t.shape.m*A - 1 at hW
    exact (evaluated_degree hraw hTd).trans_lt (by omega)
  have hzero :=wT.aHG mark.bad.support ad0
    ((algebraMap K1.K L).injective.comp K1.node.injective) t.shape.m (cK Q T)
    (fun i hi=>hc i T (by
      rw [← hST]
      change (j9 (F.scalar γ)).eval (ad0 i)=wordLift M i
      rw [j9,ad0,eval_map,eval₂_hom,mark.scalar_hits i hi]
      rfl)) hlt
  have he :=congrArg (zY9 (jet T)) hQ
  change cK (aPU H res z P) T= _ at he
  rw [aPU,d2J,← hST,map_mul,z9X,show
    zY9 (jet T) Q=cK Q T from rfl,hzero,mul_zero] at he
  let v :mA→ L[X] := fun i=>i.elim (C z) (jet S)
  have hcomp: (zY9 (jet S)).comp (JX (C z))=zY9 v := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [JX]
    · intro i
      cases i <;> simp [JX,v]
  change (zY9 (jet S)).comp (JX (C z)) P=0 at he
  rw [hcomp] at he
  apply LinearMap.mem_ker.mpr
  rw [atMark_apply,Fin.val_zero,pow_zero,pow_one]
  have hv :qV ∘ v=ED (jz (M.label γ)) (jW S) := by
    funext i
    cases i <;> rfl
  rw [← hv,bC,← MvPolynomial.map_eval,he,map_zero]
theorem pair_of_first {b:fO} {u del M Γ} (F:P1.bje A M Γ)
    (P Q:jK) (hp:P≠0) (hq:Q≠0)
    (hcap : ∀ e :Bool,CapsCut (row b).declaredHi (profile b e) (cutoff (profile b e))
      (if e then Q else P))
    (hz : ∀ e :Bool,∀ γ∈Γ,yq (u:=u) (del:=del) F 0 γ (if e then Q else P)=0)
    (hm:NoMovingTop P Q) :Nonempty (TopPair M F b) := by
  let R (e :Bool) :=if e then Q else P
  have hR (e :Bool) :R e≠0:= by cases e <;> assumption
  let pair :Fin 2→Bool→jK := ![R,fun e=>conjugate (R e)]
  refine ⟨⟨pair,?_,fun _=>rfl,?_,?_,?_⟩⟩
  · intro i e
    fin_cases i
    · exact hR e
    · exact fun h=>hR e (conjugate.injective (h.trans conjugate.map_zero.symm))
  · intro i e
    fin_cases i
    · exact hcap e
    · exact conjugate_caps (hcap e)
  · intro i e γ hγ
    have hv :=hz e γ hγ
    rw [atMark_apply] at hv
    fin_cases i
    · exact hv
    · have hS: (j9 (F.scalar γ)).map (frobenius L p)=j9 (F.scalar γ) := by
        rw [← cu.dio]
        exact congrArg j9 (F.mark γ hγ).scalar_fixed
      rw [Fin.val_zero,pow_zero,pow_one] at hv
      change zY9 (ED (jz (M.label γ)^(p^(1 :Fin 2).val))
        (jW (j9 (F.scalar γ)))) (bC (conjugate (R e)))=0
      rw [efL,Fin.val_one,pow_one]
      exact eval_conjugate (σF_seed _) hS hv
  · intro i
    fin_cases i
    · exact hm
    · exact conjugate_noMoving hm
end
end qAFIJ5c
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qAFIJ5c
noncomputable section
open Polynomial q7IA62d
open P6 (K p)
open P6_7_4 (wordLift)
open q6nKpZc (Input)
open P5_7_2 (row)
open cu (L)
open jA (jK gY bC)
open private source_rank band_bounds choose_nonzero from ProximityPrize.SubmissionLower.ZYEj7Fd
def c1 :Prop :=q7IA62d.c2
def c2 :Prop :=q7IA62d.c3
def c3:Prop :=q7IA62d.c6
private theorem necessary_zero {b u del M Γ F} (x : @Input b u del M Γ F)
    (hh:0<M.iF.toNat) (hd:M.iF.toNat≤(row b).declaredHi)
    {e :Bool} {γ:K} (hγ:γ∈Γ) :
    necessary x.crt (wordLift M) (profile b e)≤LinearMap.ker (yq F 0 γ) := by
  apply Submodule.span_le.mpr
  rintro Q ⟨W,a,P,hP,hW,rfl⟩
  have hc:=q3hrY0a.proof b e _ hh hd x.D x.units x.crt (wordLift M) W a hW P hP
  have hz :=LinearMap.mem_ker.mp (source_zero x hh hγ hW hc)
  rw [atMark_apply,Yd,bC,map_mul,MvPolynomial.map_C,
    map_mul,z9X] at hz
  apply LinearMap.mem_ker.mpr
  rw [atMark_apply]
  exact (mul_eq_zero.mp hz).resolve_left
    ((map_ne_zero_iff _ (zxb (Polynomial L) jA.iP)).mpr
      (pow_ne_zero _ (x.D.monic 0).ne_zero))
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :q6nKpZc.c1 := by
  intro b _ u del M Γ F x
  let h:=M.iF.toNat
  let word:=wordLift M
  let t:=profile b true
  let N :=necessary x.crt word t
  have hlo:=x.vo.1
  have hhi:=x.vo.2
  have hb:=band_bounds b
  have hh:0<h:= by dsimp only [h]; omega
  have hd:h≤(row b).declaredHi:= by dsimp only [h]; omega
  have hs (e :Bool) :=source_rank qK9VCOd.proof h1 h2 b e hh hd x.crt word
  obtain ⟨P,hP,hPn⟩:=choose_nonzero _ (hs false)
  obtain ⟨S,hS,hSn⟩:=choose_nonzero (source x.crt word t (cutoff t))
    ((Nat.succ_le_succ (zD0 _)).trans (hs true))
  obtain ⟨Q,hQ,hQn,hav⟩:=gpj N
    ⟨S,source_le_necessary le_rfl hS,hSn⟩ hPn
  have hn (e :Bool) : (if e then Q else P)∈necessary x.crt word (profile b e) := by
    cases e
    · exact source_le_necessary le_rfl hP
    · exact hQ
  have hcaps (e :Bool) :=mem_ambient.mp (necessary_le_ambient (hn e))
  apply pair_of_first F P Q hPn hQn
    (fun e=>caps_mono hd (hcaps e))
    (fun e γ hγ=>LinearMap.mem_ker.mp (necessary_zero x hh hd hγ (hn e)))
  intro f hf ht hfp hfq
  by_contra hm
  have hQseed :gY (bC Q)≤t.shape.U:= by
    have sup_eq :=MvPolynomial.support_map_of_injective Q
      (zxb (Polynomial L) jA.iP)
    have hseed :=(hcaps true).2.2.2.1
    change gY Q≤t.shape.U at hseed
    simpa only [gY,MvPolynomial.degreeOf_eq_sup,bC,sup_eq] using hseed
  have hfs :gY f<p:= by
    have hfdeg:=MvPolynomial.weightedTotalDegree_le_of_dvd
      (Pi.single (none :jA.mA) 1) hfq (acZ.agr hQn)
    simp only [MvPolynomial.weightedTotalDegree_piSingle] at hfdeg
    exact (hfdeg.trans hQseed).trans_lt hb.2.2
  have hpowers (W:ℕ) (hW:W≤ cutoff t) (R:jK)
      (hR:R∈source x.crt word t W) :
        f^(1+(cutoff t-W)/(3*h))∣bC R :=
    forced_power hf (zOl hm) hfs (hav f hf hfp hfq) hW hR
  have hup:=h3 b h hh hd x.D x.units x.crt word f ht hpowers
  exact Nat.not_succ_le_self _ ((hs true).trans hup)
end
end qAFIJ5c
end
section
set_option autoImplicit true
namespace qCReOzb
noncomputable section
open Polynomial Finset
open scoped Classical
open P6 (K p jG)
open q6nKpZc (Input I0)
open qzVScmb (last Origin LineRow LineCaps aOm)
open P5_7_2 (fO A stages)
open q7F2qKe (nV origins originBudget originCutter fibreShape BC)
open cu (L FX Jet rD kr)
open gT (Ambient iJ)
open pI (xN oU dM)

open akZ (yE ajz btm)
abbrev anchor {b u del M Γ F} (x : @Input b u del M Γ F) (h:nV b 0∈stages b) :=
  (x.donors.staged _ h).free.jet
def Mark {u del} {M:jG u del} {Γ} (F:P1.bje A M Γ) (f :Jet) (γ:K) :Prop :=
  rD f (M.label γ) (F.scalar γ)=0
structure Origins {b u del M Γ F} (x : @Input b u del M Γ F) (D:zJe Jet) where
  origin :Jet→Origin b
  cut:ℕ→Jet
  tail : ∀ i≤last b,∀ j,
    ajz (D.filter fun f=>i≤(origin f).val) j≤originBudget b i j
  proper : ∀ f∈D,(origin f).val<last b →
    oU (cut (origin f)) (originCutter b (origin f)) ∧ ¬ f∣cut (origin f)
  zero : ∀ i<last b,∀ γ∈Γ,Mark F (cut i) γ
def LineRoot {u del} {M:jG u del} {Γ} (F:P1.bje A M Γ)
    (g:LineRow) (γ:K) :Prop :=
  ∃ z :L,
    let v := ![algebraMap L FX z,kr (F.scalar γ),kr (F.scalar γ).derivative]
    zY9 v g=0∧zY9 v (MvPolynomial.pderiv 2 g)≠0
structure LastCut {u del} {M:jG u del} {Γ} (F:P1.bje A M Γ)
    (b:fO) (gH :zJe K) (f :Jet) where
  cut:Jet
  line :Bool
  row:LineRow
  proper : ¬ f∣cut
  caps :oU cut (if line then btm f else aOm b f)
  separant:line=true→cut=f.derivative
  line_caps :line=true→LineCaps f row
  line_pos :line=true→0<yE f 2
  Eh : ∀ γ∈Γ,Mark F f γ →
    γ∈gH∨Mark F cut γ∨(line=true∧LineRoot F row γ)
structure Parents {u del} {M:jG u del} {Γ} (F:P1.bje A M Γ)
    (b:fO) (D:ℕ→zJe Jet) (cut:ℕ→Jet→Jet)
    (rescue :ℕ→Jet→Bool) where
  Bp:ℕ→Jet→zJe (Ideal Ambient)
  gH :zJe K
  paid_bound:gH.card≤(p+1)*BC b 2+BC b 3+BC b 0
  geom : ∀ o∈origins b,∀ f,f∈D o → ∀ q∈Bp o f,
    xN q∧q.height=2∧iJ f∈q∧iJ (cut o f)∈q
  unique : ∀ o∈origins b,∀ f,f∈D o → ∀ i∈origins b,∀ g,g∈D i → ∀ q∈Bp o f,q∈Bp i g→ o=i∧f=g
  local_mass : ∀ o∈origins b,∀ f,f∈D o →
    dM (Bp o f) (fun k=>q7F2qKe.kK (yE f) (fibreShape b o (rescue o f)) k)
  total_mass : ∀ k,(∑ o∈origins b,∑ f∈D o,pI.mass (Bp o f) k)≤BC b k
  Eh : ∀ o∈origins b,∀ f,f∈D o → ∀ γ∈Γ,Mark F f γ→Mark F (cut o f) γ →
    γ∈gH ∨ ∃ i∈origins b,∃ g∈D i,∃ q∈Bp i g,I0 F q γ
end
end qCReOzb
end
section
set_option autoImplicit true
namespace qJkiHnb
open P5_7_2 (fO)
open q7F2qKe (origins stops afterFree)
open qB9xHGe (line_paid rank_paid)
open q5oHm3d (dqs projection_paid)
open private budget_paid make_receipt from ProximityPrize.SubmissionLower.ZrU0ida
def c1 :Prop := ∀ (b:fO),2≤b.val→b.val<7 →
  ∀ o∈origins b,∀ j∈stops b,afterFree b<j→dqs b o j
def c2 :Prop := ∀ (b:fO),7≤b.val→b.val<12 →
  ∀ o∈origins b,∀ j∈stops b,afterFree b<j→dqs b o j
def c3:Prop := ∀ (b:fO),12≤b.val →
  ∀ o∈origins b,∀ j∈stops b,afterFree b<j→dqs b o j
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :q6nKpZc.c5:= by
  intro b hb
  have hbill:=budget_paid b
  refine make_receipt hbill.1 hbill.2 ?_ (line_paid b) (rank_paid b)
  intro o ho j hj hp
  by_cases he :j≤afterFree b
  · exact qoK3iCb.proof b o ho j hj hp he
  have hl:=lt_of_not_ge he
  have hr :dqs b o j:= by
    by_cases h7:b.val<7
    · exact h1 b hb h7 o ho j hj hl
    by_cases h12 :b.val<12
    · exact h2 b (by omega) h12 o ho j hj hl
    · exact h3 b (by omega) o ho j hj hl
  obtain ⟨dm,a,h,hproj,hrate,hpaid⟩:=hr
  exact ⟨⟨dm,a,h,hrate,fun _ hx=>projection_paid hproj hx,hpaid⟩⟩
end qJkiHnb
end
section
set_option autoImplicit true
namespace qWSs1Id
theorem proof :qjA4dna.c1 :=
  qcuqT2c.of_children
    qNqPG5b.proof qbY56ta.proof qGA3mAd.proof
end qWSs1Id
end
section
set_option autoImplicit true
namespace quXc69a
theorem proof :qjA4dna.c2 :=
  qkA2Qzc.proof
end quXc69a
end
section
set_option autoImplicit true
namespace P6_7_1
noncomputable section
open Polynomial
open P6 (K gJ)
open cu (Equation yq)

def c1 :Prop := ∀ (x :Input) (P:Poles x),Nonempty (EarlyPicks x P)
def c2 :Prop := ∀ x :Input,Nonempty (TopPair x)
def c3:Prop :=
  ∀ (x :Input) (P:Poles x) (R:EarlyPicks x P),TopPair x →
    Nonempty (OriginCover x P R)
def c4 :Prop := ∀ (x :Input) (P:Poles x),TerminalSource P
def c5:Prop :=
  ∀ (x :Input) (P:Poles x) (R:EarlyPicks x P) (O:OriginCover x P R),
    TerminalSource P→Nonempty (Prefix x P R O)
def c6:Prop :=
  ∀ (x :Input) (P:Poles x) (t:Test) (f :Equation),
    f≠0→threshold t≤f.natDegree→apo t≤axisDegree f (direction t) →
    TerminalSource P→Trace P t f →
    rectGain x.h (Lc t) (direction t) (threshold t) (apo t)≤ rectDebit x.h (Lc t)
def c7:Prop :=
  ∀ h,packetLo≤h→h≤packetHi → ∀ t:Test,
    rectDebit h (Lc t)< rectGain h (Lc t) (direction t) (threshold t) (apo t)
def c8:Prop :=
  ∀ (x :Input) (T:zJe K),T⊆x.Γ → ∀ (i:jJ) (g:P5_7.OneSeedEquation),
    g≠0→ g.natDegree≤ i.val+1→P5_7.NativeSeedBound g (seedCap i+P6.p*seedCap i) →
    (∀ γ∈T,P5_7.atNative g (x.M.label γ) (x.F.scalar γ)=0)→T.card≤ retainedFee
private theorem eiO {f :Equation} (hp:0<f.natDegree)
    (reject : ∀ t:Test,threshold t≤f.natDegree →
      apo t≤axisDegree f (direction t)→False) :
    ∃ i:jJ,f.natDegree=i.val+1 ∧ ∀ a :Fin 2,axisDegree f a≤ seedCap i:= by
  have he :f.natDegree≤gw.length:= by
    by_contra! hl
    exact reject none hl (zD0 _)
  let i:jJ:=⟨f.natDegree-1,by omega⟩
  have hi:f.natDegree=i.val+1 := by dsimp [i]; omega
  refine ⟨i,hi,fun a => ?_⟩
  by_contra! h
  exact reject (some (i,a)) hi.ge h
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) (h6:c6)
    (h7:c7) (h8:c8) :P6_7.c1 := by
  classical
  intro u del M Γ F hw hshift H hH
  have hband:P5_7.Qn packetLo packetHi M.iF :=
    ⟨(by decide : (packetLo:ℤ)≤2355).trans hw.1,
      hw.2.trans (by decide : (2359:ℤ)≤packetHi)⟩
  let x :Input :=⟨u,del,M,Γ,F,hband,hshift,H,hH⟩
  obtain ⟨P⟩:=poles x
  obtain ⟨R⟩:=h1 x P
  obtain ⟨top⟩:=h2 x
  obtain ⟨O⟩:=h3 x P R top
  have src :=h4 x P
  obtain ⟨Q⟩:=h5 x P R O src
  let T:=x.Γ \ Q.book
  have hT:T⊆x.Γ:=Finset.sdiff_subset
  have hb: (x.Γ \ T).card≤prefixFee := by
    apply (Finset.card_le_card ?_).trans Q.book_bound
    intro γ hγ
    obtain ⟨hg,hn⟩:=Finset.mem_sdiff.mp hγ
    by_contra hm
    exact hn (Finset.mem_sdiff.mpr ⟨hg,hm⟩)
  have cover : ∀ γ∈T,∃ q∈Q.parents,P6_7.axy x.M x.F q γ :=
    fun γ hγ=>(Q.Eh γ (hT hγ)).resolve_left (Finset.mem_sdiff.mp hγ).2
  have hkept:T.card≤ retainedFee := by
    by_cases hm:T.Nonempty
    · obtain ⟨γ,hγ⟩:=hm
      obtain ⟨q,hq,_⟩:=cover γ hγ
      obtain ⟨f,hf⟩:=czI.proof Q.parents ⟨q,hq⟩ Q.geometric
      have hn:f≠0:= by
        intro hz
        have hp:=hf.positive
        simp only [hz,natDegree_zero,lt_self_iff_false] at hp
      obtain ⟨hl,hu⟩:=heights x
      obtain ⟨i,he,hseed⟩:=eiO hf.positive (fun t hE hv =>
        (h7 x.h hl hu t).not_ge
          (h6 x P t f hn hE hv src (gDx src t Q.geometric Q.terminal_pass hf)))
      obtain ⟨g,hg,hge,hgs,hgraph⟩:=native_restriction hn (seedCap_lt i) (hseed 0) (hseed 1)
      apply h8 x T hT i g hg (hge.trans he.le) hgs
      intro η hη
      rw [hgraph]
      obtain ⟨q',hq',hon⟩:=cover η hη
      have hz :=RingHom.mem_ker.mp (hon (hf.aiq q' hq'))
      simpa only [coe_eval₂RingHom,eval₂_C,yq] using hz
    · rw [Finset.not_nonempty_iff_eq_empty.mp hm]
      exact zD0 _
  change x.Γ.card≤gJ.rectTight.regular
  rw [← Finset.card_sdiff_add_card_eq_card hT]
  exact (Nat.add_le_add hb hkept).trans (by decide)
end
end P6_7_1
end
section
set_option autoImplicit true
namespace qcOrJya
noncomputable section
open Finset Polynomial
open P6 (blockLength dw)
open P5_7 (farAgreement)
open P6_7_1 (Input degree heights)
open gT (tK FW)
open pI (abM)
open aF0 (power BJ YM)
open baX (mix)
open private cSy from ProximityPrize.SubmissionLower.Z6ykYva
open scoped Classical
theorem fixed_marks (x :Input) (G:tK) (hG:abM G 115 25) :
    (x.Γ.filter fun γ=>FW G (x.F.scalar γ)=0).card ≤
      3*((115-25)*YM degree 115 25+25*BJ degree 115)+115^2 := by
  let T:=x.Γ.filter fun γ=>FW G (x.F.scalar γ)=0
  let a :=BJ degree 115
  let v :=YM degree 115 25
  let β:ℚ:=((blockLength-farAgreement:ℕ) :ℚ)/((farAgreement-degree :ℕ) :ℚ)
  have hβ:0≤β:= by dsimp only [β]; positivity
  have hv : (v :ℚ)≤a := by exact_mod_cast (min_le_left a (power degree*(25-1)+degree))
  have hT:T⊆x.Γ:=filter_subset _ _
  have h:=cSy (x.F.distinct.mono hT) ⟨by decide,by decide,by decide,by decide⟩
    G hG (fun γ hγ=>(mem_filter.mp hγ).2) (β*a) (β*v) (by positivity)
    (mul_le_mul_of_nonneg_left hv hβ) (fun U hU f hf hp hb hj hr=> by
      have hc:=qUJtx6c.ePE (x.F.distinct.mono (hU.trans hT))
        (fun γ hγ=>(P6_7.aic x.F (hT (hU hγ))).trans
          (Nat.add_le_add_left (heights x).2 _))
        (w:=x.M.word) (fun γ hγ =>
          let m:=x.F.mark γ (hT (hU hγ))
          ⟨m.bad.support,(by decide :farAgreement≤dw).trans m.bad.dw,m.scalar_hits⟩)
        (d:=degree) (by decide) (by decide) (by decide) f hf hp hb hj hr
      refine hc.trans_eq ?_
      change β *mix f.totalDegree (f.degreeOf 1) a v+1= _
      unfold mix
      ring)
  have hβ₃:β≤3:= by
    change (82365:ℚ)/46339≤3
    apply (div_le_iff₀ (by decide : (0:ℚ)<46339)).mpr
    exact_mod_cast (show 82365≤3*46339 from by decide)
  have h' : (T.card:ℚ)≤((3*((115-25)*v+25*a)+115^2 :ℕ) :ℚ) := calc
    _≤ mix 115 25 (β*a) (β*v)+(115^2 :ℕ) :=h
    _≤ mix 115 25 (3*a) (3*v)+(115^2 :ℕ) := by unfold mix; gcongr
    _ = _:= by unfold mix; push_cast; ring
  exact_mod_cast h'
end
end qcOrJya
end
section
set_option autoImplicit true
namespace qy95ATd
noncomputable section
open Polynomial Finset
open qQ9yWTb (Raw embed height Moving)
open P5 (K)
open P6_7_3 (Input)
open cu (aZ FX qD)
open Qt (gY Qc)
open scoped Classical
open qVXVW4b (constant_height embed_degree)
open private height_mul degree_pos from ProximityPrize.SubmissionLower.ZGCzLxb
private def Classified {x :Input} {U:zJe K} (J:WordChart x U)
    (P:ℕ→Prop) (f :Raw) :Prop :=
  f≠0 ∧ ∀ q:Raw,Irreducible q→q∣f →
    (0<q.natDegree∧0<height q)∧P (weight J q)
private theorem unit_classified {x :Input} {U:zJe K} {J:WordChart x U}
    {P:ℕ→Prop} {f :Raw} (h:IsUnit f) :Classified J P f :=
  ⟨h.ne_zero,fun _ hq hd=>(hq.not_isUnit (isUnit_of_dvd_unit hd h)).elim⟩
private theorem Classified.moving {x :Input} {U:zJe K} {J:WordChart x U}
    {P:ℕ→Prop} {f :Raw} (h:Classified J P f) :Moving f :=
  ⟨h.1,fun q hq hd=>(h.2 q hq hd).1⟩
private theorem factor_resources {x :Input} {U:zJe K} (J:WordChart x U)
    {q i:Raw} (hq:Irreducible q) (hi:Irreducible i) (hd:q∣i) :
    q.natDegree=i.natDegree∧height q=height i∧weight J q=weight J i:= by
  obtain ⟨r,hr⟩:=hd
  have hu:=(hi.isUnit_or_isUnit hr).resolve_left hq.not_isUnit
  obtain ⟨b,hb,he⟩:=Polynomial.isUnit_iff.mp hu
  obtain ⟨a,ha,ha'⟩:=MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hb
  obtain ⟨l,hl,hl'⟩:=Polynomial.isUnit_iff.mp ha
  have hC: (C l:cu.L[X])≠0:=C_ne_zero.mpr hl.ne_zero
  have hr' : r=Y3.aka (C l) := by rw [← he,ha',← hl']; rfl
  have hh:height r=0:= by
    change gY (Y3.embed r)=0
    rw [hr',Y3.b1t,constant_height]
  have hdeg:i.natDegree=q.natDegree := by
    rw [hr,natDegree_mul hq.ne_zero hu.ne_zero,natDegree_eq_zero_of_isUnit hu,add_zero]
  refine ⟨hdeg.symm,by rw [hr,height_mul hq.ne_zero hu.ne_zero,hh,add_zero],?_⟩
  have hc (j:ℕ) (m:Fin 2 →₀ ℕ) :
      ((i.coeff j).coeff m)=((q.coeff j).coeff m)*C l:= by
    rw [hr,← he,ha',← hl',mul_comm q,coeff_C_mul,MvPolynomial.coeff_C_mul,mul_comm]
  have hsupport (j:ℕ) : (i.coeff j).support=(q.coeff j).support := by
    ext m
    simp only [MvPolynomial.mem_support_iff,hc,mul_ne_zero_iff]
    exact ⟨And.left,fun h=>⟨h,hC⟩⟩
  have houter :i.support=q.support := by
    ext j
    simp only [Polynomial.mem_support_iff,← MvPolynomial.support_nonempty,hsupport]
  unfold weight q4Pefpa.load
  rw [houter,hdeg]
  refine sup_congr rfl fun j _ => ?_
  rw [hsupport]
  refine sup_congr rfl fun m hm => ?_
  rw [hc,natDegree_mul (MvPolynomial.mem_support_iff.mp hm) hC,natDegree_C,add_zero]
private theorem add_factor {x :Input} {U:zJe K} {J:WordChart x U}
    {P:ℕ→Prop} {f i:Raw} (hf :Classified J P f) (hi:Irreducible i)
    (hd:0< i.natDegree) (hh:0<height i) (hw:P (weight J i)) :
    Classified J P (i*f) := by
  refine ⟨mul_ne_zero hi.ne_zero hf.1,?_⟩
  intro q hq hqf
  rcases hq.prime.dvd_mul.mp hqf with hqi | hqf'
  · obtain ⟨hd',hh',hw'⟩:=factor_resources J hq hi hqi
    rw [hd',hh',hw']
    exact ⟨⟨hd,hh⟩,hw⟩
  · exact hf.2 q hq hqf'
private theorem partition {x :Input} {U:zJe K} (J:WordChart x U) (W:ℕ)
    (r :Raw) (hr :r≠0) (hp: (embed r).IsPrimitive) :
    ∃ F Q B:Raw,r=F*Q*B∧Classified J (W < ·) F∧Classified J (· ≤ W) Q∧B≠0∧height B=0:= by
  have h0:height (1 :Raw)=0:= by
    change gY (embed 1)=0
    simpa only [map_one] using constant_height 1
  revert hr hp
  induction r using WfDvdMonoid.induction_on_irreducible with
  | zero=>exact fun h _=>(h rfl).elim
  | unit f hf =>
    intro _ _
    exact ⟨f,1,1,by simp,unit_classified hf,unit_classified isUnit_one,one_ne_zero,h0⟩
  | mul a i ha hi ih =>
    intro _ hp
    have hpa : (embed a).IsPrimitive :=isPrimitive_of_dvd hp (map_dvd embed (dvd_mul_left a i))
    obtain ⟨F,Q,B,h,hF,hQ,hB,hhB⟩:=ih ha hpa
    by_cases hs :height i=0
    · exact ⟨F,Q,i*B,by rw [h]; ring,hF,hQ,mul_ne_zero hi.ne_zero hB,
        by rw [height_mul hi.ne_zero hB,hs,hhB,add_zero]⟩
    have hh:0<height i:=zOl hs
    have hd:=degree_pos hp (dvd_mul_right i a) hh
    by_cases hw:W<weight J i
    · refine ⟨i*F,Q,B,by rw [h]; ring,?_,hQ,hB,hhB⟩
      exact add_factor hF hi hd hh hw
    · refine ⟨F,i*Q,B,by rw [h]; ring,hF,?_,hB,hhB⟩
      exact add_factor hQ hi hd hh (Nat.le_of_not_gt hw)
private def value {x :Input} {U:zJe K} (J:WordChart x U) (γ:K) :Raw →+* FX :=
  (eval₂RingHom (qD (x.M.label γ)) (P5_7_7.dualValue J γ)).comp embed
private theorem ecU {x :Input} {U T:zJe K} (J:WordChart x U)
    (hj:Set.InjOn (P5_7_7.dualValue J) (T:Set K))
    {B:Raw} (hB:B≠0) (hh:height B=0) (hr : ∀ γ∈T,root J B γ) :
    T.card≤B.natDegree := by
  let b:=embed B
  let q:=b.map zuE
  have hc (j:ℕ) :b.coeff j=MvPolynomial.C (zuE (b.coeff j)) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero
      ((Qc b 0).mp hh.le j))
  have he (φ:aZ →+* FX) (hφ : ∀ a,φ (MvPolynomial.C a)=a) :
      b.map φ=q:= by
    ext j
    simp only [q,coeff_map]
    change φ (b.coeff j)= _
    exact (congrArg φ (hc j)).trans (hφ _)
  have hq:q≠0:= fun hz=> by
    apply hB
    apply Y3.embed_injective
    change b=Y3.embed 0
    rw [map_zero]
    apply Polynomial.ext
    intro j
    have h:=congrArg (fun p:FX[X]=>p.coeff j) hz
    simp only [q,coeff_map,coeff_zero] at h
    rw [hc j,h,map_zero,coeff_zero]
  refine (P5_7_7.countRoots T _ hj q hq ?_).trans (natDegree_map_le.trans (embed_degree B).le)
  intro γ hγ
  rw [← he (qD (x.M.label γ)) (fun a=>z9X a),eval_map]
  exact hr γ hγ
theorem allocate {x :Input} {T U:zJe K} {e u W:ℕ} (hU:U⊆T)
    (hcard:T.card≤U.card+1) (J:WordChart x U)
    (hj:Set.InjOn (P5_7_7.dualValue J) (U:Set K))
    (r :Raw) (hp: (embed r).IsPrimitive) (he :r.natDegree≤e) (hs :height r≤u)
    (hr : ∀ γ∈U,root J r γ) :Nonempty (SplitData x T e u W) := by
  have hn:r≠0:= fun h=>hp.ne_zero (h.symm ▸ map_zero embed)
  obtain ⟨F,Q,B,h,hF,hQ,hB,hhB⟩:=partition J W r hn hp
  have hd:=he
  rw [h,natDegree_mul (mul_ne_zero hF.1 hQ.1) hB,natDegree_mul hF.1 hQ.1] at hd
  rw [h,height_mul (mul_ne_zero hF.1 hQ.1) hB,height_mul hF.1 hQ.1,hhB,add_zero] at hs
  let H :=U.filter fun γ=>root J F γ
  let N :=U \ H
  let G:=N.filter fun γ=>root J Q γ
  let E :=N \ G
  have hH :H⊆U:=filter_subset _ _
  have hN :N⊆U:=sdiff_subset
  have hG:G⊆N :=filter_subset _ _
  have hE :E⊆N :=sdiff_subset
  have hroot : ∀ γ∈E,root J B γ:= by
    intro γ hγ
    have hz :value J γ r=0:=hr γ (hN (hE hγ))
    rw [h,map_mul,map_mul] at hz
    have hnf :value J γ F≠0 :=
      fun hf=>(mem_sdiff.mp (hE hγ)).2 (mem_filter.mpr ⟨hN (hE hγ),hf⟩)
    have hnq:value J γ Q≠0 :=
      fun hq=>(mem_sdiff.mp hγ).2 (mem_filter.mpr ⟨hE hγ,hq⟩)
    exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero hnf hnq)
  have hcount:=ecU J (hj.mono (hE.trans hN)) hB hhB hroot
  have h₀:N.card+H.card=U.card:=card_sdiff_add_card_eq_card hH
  have h₁:E.card+G.card=N.card:=card_sdiff_add_card_eq_card hG
  exact ⟨⟨U,hU,J,H,G,hH,hG.trans hN,by omega,F,Q,hF.moving,hQ.moving,by omega,by omega,
    hs,fun q hq hd=>(hF.2 q hq hd).2,fun q hq hd=>(hQ.2 q hq hd).2,fun _ hγ=>(mem_filter.mp hγ).2,fun _ hγ=>(mem_filter.mp hγ).2⟩⟩
end
end qy95ATd
end
section
set_option autoImplicit true
set_option maxRecDepth 2048
set_option maxHeartbeats 1400000
namespace qy95ATd
open P5 (p)
open P6_7_3 (gw aKj cV)
open qQ9yWTb (Witness)
private def witness (e u:ℕ) (pair :ℕ×ℕ) :Witness :=
  let (g,ct) :=pair
  let E :=e+g
  let cz :=((p-1)/u-E)/e-1
  let m:=(g+1)*(cz*u+1)*(ct*u+1)
  let d:=((cz+1)*u+1)*((ct+1)*u+1)
  let j:=m/d
  let W:=max (e*width)
    (max (d*(width*E*(E+1)/2+width*j*(j+1)/2)/m-j*width) (E*width-j*width))
  ⟨g,cz,ct,j,W⟩
private def rows :List (ℕ×ℕ) :=
  [(0,0),(0,0),(0,1),(0,1),(0,1),(0,1),(0,1),(0,2),(4,1),(5,1),
   (5,1),(6,1),(7,1),(10,1),(16,1),(8,2),(8,2),(10,2),(13,2),(17,2),
   (24,2),(13,3),(16,3),(20,3),(25,3),(34,3),(21,4),(25,4),(31,4),(39,4),
   (46,4),(33,5),(40,5),(49,5),(61,5),(43,6),(51,6),(63,6),(74,6),(55,7),
   (65,7),(80,7),(59,8),(68,8),(79,8),(97,8),(71,9),(80,9),(92,9),(108,9),
   (115,9),(89,10),(98,10),(108,10),(120,10),(132,10),(135,10),(101,11),(105,11),(108,11),
   (111,11),(112,11),(112,11),(110,11),(154,10),(147,10),(131,10),(119,10),(156,9),(129,9),
   (108,9),(124,8),(149,7),(98,7),(97,6),(84,5),(62,4),(42,2)]
private def af (e u:ℕ) (w:Witness) :Prop :=
  u≤3611∧(e≤2∨(Good e u w∧gu e u w))
private def ay :ℕ→List (ℕ×ℕ)→List (ℕ×ℕ)→Prop
  | _,[],_=>True
  | _,_ :: _,[]=>False
  | e,(u,_) :: gs,r :: rs =>
    af e u (witness e u r)∧ay (e+1) gs rs
private theorem check_cons {e u a gs r rs}
    (h:af e u (witness e u r)) (rest:ay (e+1) gs rs) :
    ay e ((u,a)::gs) (r::rs) :=
  ⟨h,rest⟩
private instance rowDecidable (e u:ℕ) (w:Witness) :Decidable (af e u w) := by
  unfold af Good gu
  infer_instance
private theorem checked :ay 1 gw rows := by
  repeat' first | exact True.intro | refine check_cons (by decide) ?_
private theorem get_checked {e gs rs} (h:ay e gs rs) (i:Fin gs.length) :
    (gs.get i).1≤3611∧(e+i.val≤2 ∨
      ∃ w,Good (e+i.val) (gs.get i).1 w∧gu (e+i.val) (gs.get i).1 w) := by
  induction gs generalizing e rs with
  | nil=>exact i.elim0
  | cons t gs ih =>
    rcases t with ⟨u,a⟩
    cases rs with
    | nil=>exact h.elim
    | cons r rs =>
      refine Fin.cases ?_ (fun j => ?_) i
      · change u≤3611∧(e≤2 ∨ ∃ w,Good e u w∧gu e u w)
        exact ⟨h.1.1,h.1.2.imp_right (fun hw=>⟨_,hw⟩)⟩
      · change (gs.get j).1≤3611∧(e+(j.val+1)≤2 ∨
          ∃ w,Good (e+(j.val+1)) (gs.get j).1 w∧gu (e+(j.val+1)) (gs.get j).1 w)
        rw [← Nat.add_assoc,Nat.add_right_comm]
        exact ih h.2 j
theorem bHu (i:aKj) :
    (cV i).1≤3611∧(i.val+1≤2 ∨
      ∃ w,Good (i.val+1) (cV i).1 w∧gu (i.val+1) (cV i).1 w) := by
  simpa only [Nat.add_comm 1] using get_checked checked i
end qy95ATd
end
