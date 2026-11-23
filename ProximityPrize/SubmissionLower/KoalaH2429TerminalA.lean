import ProximityPrize.SubmissionLower.KoalaH2429TerminalAArithmetic
import ProximityPrize.SubmissionLower.KoalaH2429BankResize
import ProximityPrize.SubmissionLower.KoalaH2430TerminalBank
import ProximityPrize.SubmissionLower.KoalaRectBridgeCore
import ProximityPrize.SubmissionLower.KoalaRectQuotient
import ProximityPrize.SubmissionLower.HighCore82258Source
import ProximityPrize.SubmissionLower.TwoTerminal

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace KoalaH2429TerminalA
noncomputable section

open Polynomial Finset
open HighCore82258 (agreement crtWord)
open FrontCore82258 (AnchorModel)
open K1_14 (Equation SeedBound)
open K1_14_1 (PoleData CRTLift evaluated)
open K1_14_3 (Parent ProjectedProduct Surface)
open KoalaH2429Banks (terminal)
open KoalaRect (axisDegree rectSlots rectGain rectDebit rectLoss seedBound_of_axis)

abbrev TerminalPass {u del} (M : AnchorModel u del) {D : PoleData 2429}
    (crt : CRTLift D) (qs : Finset Surface) : Prop :=
  ∀ q ∈ qs, ∀ P ∈ evaluated crt (crtWord M) terminal.shape
    (terminal.shape.m * agreement - 1), P ∈ q.asIdeal

private theorem bank_ok : P3_7_1.BankOK terminal :=
  KoalaH2429Banks.resize_ok KoalaH2430Terminal.terminal_ok 438444

private theorem reject {u del} (M : AnchorModel u del) {D : PoleData 2429}
    (crt : CRTLift D) {qs : Finset Surface} (hgeo : ∀ q ∈ qs, Parent q)
    (hpass : TerminalPass M crt qs) {f : Equation} (hprod : ProjectedProduct qs f)
    {E : ℕ} (hE : E ≤ f.natDegree) (he : 0 < E)
    (U d : Fin 2 → ℕ) (hbox : U 0 + U 1 ≤ terminal.shape.U)
    (hslots : ∀ r, rectSlots U (axisDegree f) r ≤ rectSlots U d r)
    (hstrict : rectDebit 2429 terminal.nodeRows terminal.poleMoment U <
        rectGain agreement 2429 terminal.shape E U d) : False := by
  have hf : f ≠ 0 := by
    intro hz
    have hp := hprod.positive
    simp [hz] at hp
  exact (not_le_of_gt hstrict) (rectLoss (h := 2429) (by decide) (by decide) (by decide)
    crt (crtWord M) agreement terminal.shape U d (by decide) (by decide) hbox
    bank_ok.moment.2 (by decide) bank_ok.nodes.le bank_ok.moment.1
    he hgeo hpass hf hE hprod hslots)

theorem grade_lt_23 {u del} (M : AnchorModel u del) {D : PoleData 2429}
    (crt : CRTLift D) {qs : Finset Surface} (hgeo : ∀ q ∈ qs, Parent q)
    (hpass : TerminalPass M crt qs) {f : Equation} (hprod : ProjectedProduct qs f) :
    f.natDegree < 23 := by
  by_contra! he
  let W := rectWitness 23
  refine reject M crt hgeo hpass hprod he (by decide) W.U W.order
    (witness_guards (by decide : 0 < 23) (by decide)).2 ?_
    (rect_bounds (by decide : 0 < 23) (by decide))
  intro r
  have h0 : W.order 0 = 0 := by decide
  have h1 : W.order 1 = 0 := by decide
  simp only [rectSlots, h0, h1, Nat.mul_zero, Nat.sub_zero]
  exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)

theorem paid_degrees {u del} (M : AnchorModel u del) {D : PoleData 2429}
    (crt : CRTLift D) {qs : Finset Surface} (hgeo : ∀ q ∈ qs, Parent q)
    (hpass : TerminalPass M crt qs) {f : Equation} (hprod : ProjectedProduct qs f) :
    f.natDegree < 23 ∧ axisDegree f 0 + axisDegree f 1 ≤ paidCap f.natDegree := by
  have hE := grade_lt_23 M crt hgeo hpass hprod
  have he := hprod.positive
  obtain ⟨hside,hbox⟩ := witness_guards he hE.le
  obtain ⟨hlo,hhi,hsum⟩ := witness_order he hE
  exact ⟨hE, KoalaTwoTerminal.oriented_axis_cap (actual := axisDegree f)
    hside hlo hhi hsum hbox (rect_bounds he hE.le)
    (reject M crt hgeo hpass hprod le_rfl he)⟩

theorem seed_bound {u del} (M : AnchorModel u del) {D : PoleData 2429}
    (crt : CRTLift D) {qs : Finset Surface} (hgeo : ∀ q ∈ qs, Parent q)
    (hpass : TerminalPass M crt qs) {f : Equation} (hprod : ProjectedProduct qs f) :
    f.natDegree < 23 ∧ SeedBound f 476 := by
  obtain ⟨hdegree,haxis⟩ := paid_degrees M crt hgeo hpass hprod
  exact ⟨hdegree, seedBound_of_axis (haxis.trans (paidCap_le hprod.positive hdegree))⟩

theorem hard_seed_bound {f : Equation} (he : f.natDegree = 16 ∨ f.natDegree = 17)
    (haxis : axisDegree f 0 + axisDegree f 1 ≤ paidCap f.natDegree) :
    SeedBound f 474 := by
  apply seedBound_of_axis
  rcases he with he | he
  · rw [he, paidCap16] at haxis
    omega
  · rw [he, paidCap17] at haxis
    omega

end
end KoalaH2429TerminalA
