import ProximityPrize.SubmissionLower.FrontCore82258Model
import ProximityPrize.SubmissionLower.HighBankCore

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

namespace HighCore82258
noncomputable section

open Polynomial
open P1 (K I p node twist)
open FrontCore82258 (AnchorModel AnchoredFamily AdjacentChart effectiveHeight)
open K1_14 (L FX Seeds Equation Shape Jet Banks SeedBound liftPoly graphEval atX atMark
  jetAt triangle slots shapeSum)
open K1_14_1
open P1_7_1 (groupedPoleMoment nodeRows telescope)
open scoped BigOperators Polynomial
open private pole_bound from ProximityPrize.SubmissionLower.UpperBranch1

def InBand (b:Band) (w:ℤ):Prop:=(start b:ℤ)≤w ∧ w≤(finish b:ℤ)
theorem window_nat {b : Band} {w : ℤ} (hw : InBand b w) :
    start b≤w.toNat ∧ w.toNat≤finish b:=by
  unfold InBand at hw
  omega

theorem height_guards (b : Band) : 0 < start b ∧ finish b ≤ heightCap := by
  cases b <;> decide

def fullCutoff (s:Shape):=s.m*agreement - 1
def buffered (h r:ℕ) (s:Shape):=fullCutoff s - 2*h*r
def RankFloor (h : ℕ) (t : Bank) (rows : Banks) : Prop :=
  ∀ W < t.shape.m * agreement,
    (∀ q≤t.shape.B, ∀ j≤ min q t.shape.J,q*(131071-h)≤W+1+j) →
    triangle t.shape.U * shapeSum t.shape (fun q j => W+1+j - q*(131071-h)) ≤
      debit h t + ∑ w ∈ Finset.range (W+1),Module.finrank FX (rows t.shape w)
structure Source (b : Band) {u del} (M : AnchorModel u del) {Γ}
    (F:AnchoredFamily M Γ) (rows:Banks):Prop where
  nested : ∀ t, Listed b t → ∀ t', Listed b t' →
    t.shape.m=t'.shape.m→t.shape.B=t'.shape.B→t.shape.J=t'.shape.J →
    t.shape.U≤t'.shape.U → ∀ W W', W≤W' → rows t.shape W≤ rows t'.shape W'
  necessary : ∀ t, Listed b t → ∀ W < t.shape.m * agreement, ∀ P ∈ rows t.shape W,
    ∀ γ ∈ Γ,jetAt P (M.label γ) (F.scalar γ)=0
  shape : ∀ t,Listed b t → ∀ W, ∀ P ∈ rows t.shape W,K1_14_3.RowCaps P t.shape
  leading : ∀ t,Listed b t→K1_14_3.LeadingFilter (effectiveHeight M).toNat rows t.shape
  shift : ∀ t,Listed b t→K1_14_3.SeedShift (effectiveHeight M).toNat rows t.shape
  floor_bound : ∀ t,Listed b t→RankFloor (effectiveHeight M).toNat t rows
structure BufferedPair (h : ℕ) (rows : Banks) (s : Stage) where
  free:Jet
  moving:Jet
  free_ne:free≠0
  moving_ne:moving≠0
  free_mem:free ∈ rows s.free.shape (buffered h s.reserve s.free.shape)
  moving_mem:moving ∈ rows s.moving.shape (buffered h s.reserve s.moving.shape)
  no_moving:K1_14_3.NoMovingCommon free moving
abbrev Pairs (b : Band) (h : ℕ) (rows : Banks) :=
  ∀ s ∈ stages b,BufferedPair h rows s

def SourceExists : Prop :=
  ∀ (b : Band) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b (effectiveHeight M)→M.shift ∉ Γ → ∀ H,AdjacentChart M F H →
    ∃ rows:Banks,Source b M F rows

def crtWord {u del} (M : AnchorModel u del) : I → L :=
  fun i => algebraMap K L (M.word i)

structure ChartSource (b : Band) {u del} (M : AnchorModel u del) {Γ}
    (F:AnchoredFamily M Γ) where
  poles:PoleData (effectiveHeight M).toNat
  crt:CRTLift poles
  node_avoids : ∀ i k,(poles.block i).eval (nodeL k)≠0
  residues : ∀ γ ∈ Γ,MarkResidues poles (M.label γ) (F.scalar γ)
  source:Source b M F (evaluated crt (crtWord M))

abbrev ChartSource.rows {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    (C:ChartSource b M F):Banks :=
  evaluated C.crt (crtWord M)

def CRTSourceExists : Prop :=
  ∀ (b : Band) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b (effectiveHeight M)→M.shift ∉ Γ → ∀ H,AdjacentChart M F H →
    Nonempty (ChartSource b M F)

theorem source_for_crt
    (hnodes : ∀ (b:Band) (t:Bank),Listed b t→nodeRows t.shape=t.nodeRows)
    (hmoment : ∀ (b : Band) (t : Bank), Listed b t →
      groupedPoleMoment t.shape.B t.shape.J≤t.poleMoment ∧ t.shape.B < K1.p) :
    CRTSourceExists:=by
  intro b u del M Γ F hband _ H hH
  have hlocal:=P1_7_1_1.of_children P1_7_1_1_1.proof P1_7_1_1_2.proof
  let h:=(effectiveHeight M).toNat
  have hg:=height_guards b
  obtain ⟨hl,hu⟩:=window_nat hband
  have hlo:0 < h:=hg.1.trans_le hl
  have hhi:h≤heightCap:=hu.trans hg.2
  have hraw:h≤131070:=hhi.trans (by decide)
  have hchar:h < K1.p:=hhi.trans_lt (by decide)
  obtain ⟨D,_,hnode,hres⟩:=FrontCore82258.chart_poles M F H hH
  obtain ⟨Crt⟩:=P0_10_1.crt_lift D
  let word:=crtWord M
  refine ⟨⟨D,Crt,hnode,hres,⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
  · intro t _ t' _ hm hB hJ hU W W' hW
    exact evaluated_mono Crt word hm hB hJ hU hW
  · intro t _ W hW P hP γ hγ
    let B:=F.mark γ hγ
    have hdegree : (liftPoly (F.scalar γ)).natDegree ≤ 131071 + h := by
      rw [liftPoly,Polynomial.natDegree_map]
      rcases B.scalar_degree with hzero | hd
      · simp [hzero]
      · change ((F.scalar γ).natDegree : ℤ) ≤ 131071 + M.overhead at hd
        dsimp [h]
        have heff := FrontCore82258.overhead_le_effective M
        omega
    refine P0_10_1.contact_vanish Crt word hnode (M.label γ) (F.scalar γ) (hres γ hγ) hdegree B.bad.support
      B.bad.agreement ?_ t.shape W hW P hP
    intro i hit
    rw [liftPoly,nodeL,Polynomial.eval_map,Polynomial.eval₂_hom]
    exact congrArg (algebraMap K L) (B.scalar_hits i hit)
  · intro t _ W P hP j i hne
    exact evaluated_shape Crt word hP j i hne
  · intro t _ W P hP hne
    exact P0_10_1.leading_bound hlo hraw Crt word t.shape W P hP hne
  · intro t _ W P hP i r
    exact P0_10_1.evaluated_shift Crt word hP i r
  · intro t ht W _ hW
    obtain ⟨hm,hB⟩:=hmoment b t ht
    have hvol:=P0_10_1.ambient_bound (hraw.trans (by decide)) t.shape W hW
    have hcontact:=P0_10_1.physical_bound h word t.shape W
    have hpole:=pole_bound hlocal hlo hchar Crt word t.shape hB W
    have hsum:=telescope hraw Crt word t.shape W
    have hphys : physicalDebit t.shape = triangle t.shape.U * t.nodeRows := by
      rw [← hnodes b t ht]
      unfold physicalDebit nodeRows
      rw [Nat.mul_assoc]
    rw [hphys] at hcontact
    have hextra:=Nat.mul_le_mul_left (2*h*(t.shape.U+1)) hm
    change rawVolumeAt h t.shape W ≤
      (triangle t.shape.U * t.nodeRows + 2*h*(t.shape.U+1)*t.poleMoment) +
        ∑ w ∈ Finset.range (W+1),Module.finrank FX (evaluated Crt word t.shape w)
    omega

theorem source
    (hnodes : ∀ b t,Listed b t→nodeRows t.shape=t.nodeRows)
    (hmoment : ∀ b t, Listed b t →
      groupedPoleMoment t.shape.B t.shape.J≤t.poleMoment ∧ t.shape.B < K1.p) :
    SourceExists:=by
  intro b u del M Γ F hw hshift H hH
  obtain ⟨C⟩:=source_for_crt hnodes hmoment b u del M Γ F hw hshift H hH
  exact ⟨C.rows,C.source⟩

#print axioms source_for_crt
#print axioms source
end
end HighCore82258
