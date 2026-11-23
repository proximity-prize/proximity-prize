-- Ported from public PR657, e07f14a81dfe2cf1bda985e67040ad4d31fe81ab, KoalaRectTerminal.lean.
import ProximityPrize.SubmissionLower.KoalaRectBridgeCore
import ProximityPrize.SubmissionLower.Pr657Rect2435Receipts
import ProximityPrize.SubmissionLower.HighCore82258Family
import ProximityPrize.SubmissionLower.HighCore82258RectangleOrder

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false

open FrontCore82258 (effectiveHeight)

namespace KoalaRect
noncomputable section
open Polynomial Finset HighCore82258
open Pr657Rect2435Receipts (rectWitness paidCap witness_guards paid_order)
open K1_14 (Equation)
open K1_14_3 (ProjectedProduct)
open Pr657Rect2435Axes

private theorem reject_shape {u del Γ} {M : AnchorModel u del} {F : AnchoredFamily M Γ}
    (hbank:P3_7_1.BankOK (terminal .h2367)) (hw:InBand .h2367 (effectiveHeight M)) (C:ChartSource .h2367 M F)
    {pairs:Pairs .h2367 (effectiveHeight M).toNat C.rows}
    (Q:PrefixInventory .h2367 M F pairs) {f:Equation} (hf:Reduced f)
    (hprod:ProjectedProduct Q.parents f) {E:ℕ} (hE:E≤f.natDegree) (he:0 < E)
    (U d:Fin 2→ℕ) (hbox:U 0+U 1≤(terminal .h2367).shape.U)
    (hslots : ∀ r,rectSlots U (axisDegree f) r≤ rectSlots U d r)
    (hstrict : rectDebit (effectiveHeight M).toNat (terminal .h2367).nodeRows (terminal .h2367).poleMoment U <
        rectGain agreement (effectiveHeight M).toNat (terminal .h2367).shape E U d):False:=by
  let h:=(effectiveHeight M).toNat
  let t:=terminal .h2367
  obtain ⟨hl,hu⟩:=window_nat hw
  have hl' : 2431≤h:=hl
  have hu' : h≤2695:=hu
  have hpos:0 < h:=lt_of_lt_of_le (by decide:0 < 2431) hl'
  have hraw:h≤131070:=hu'.trans (by decide)
  have hchar:h < K1.p:=hu'.trans_lt (by decide)
  obtain ⟨_,_,hA,hsmall,hwidth⟩:=terminal_guards .h2367
  have hwid : t.shape.B*(131071-h) ≤ t.shape.m*agreement :=
    (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hl _)).trans hwidth
  have hne : f ≠ 0 := by
    intro hz
    have hp:=hf.1
    simp [hz] at hp
  have hcut := rectLoss (h := h) hpos hraw hchar
    C.crt (crtWord M) agreement t.shape U d hA hsmall hbox hbank.moment.2 hwid
    hbank.nodes.le hbank.moment.1 he Q.geometric Q.terminal_pass hne hE hprod hslots
  exact (not_le_of_gt hstrict) hcut

theorem paid_degrees {u del Γ} {M : AnchorModel u del} {F : AnchoredFamily M Γ}
    (hbank:P3_7_1.BankOK (terminal .h2367)) (hw:InBand .h2367 (effectiveHeight M)) (C:ChartSource .h2367 M F)
    {pairs:Pairs .h2367 (effectiveHeight M).toNat C.rows}
    (Q:PrefixInventory .h2367 M F pairs) {f:Equation} (hf:Reduced f)
    (hprod:ProjectedProduct Q.parents f) :
    f.natDegree < 23 ∧ axisDegree f 0+axisDegree f 1≤paidCap f.natDegree:=by
  obtain ⟨hl,hu⟩:=window_nat hw
  have hraw:(effectiveHeight M).toNat < 131071:=hu.trans_lt (by decide)
  have he:1≤f.natDegree:=hf.1
  have hfull : f.natDegree < 23 := by
    by_contra! h
    let T:=rectWitness 23
    refine reject_shape hbank hw C Q hf hprod h (by decide) T.U T.order
      (witness_guards (by decide:1≤23) (by decide)).2 ?_
      (Pr657Rect2435Receipts.rect_bounds hl hraw (by decide:1≤23) (by decide))
    intro r
    have h0:T.order 0=0:=by decide
    have h1:T.order 1=0:=by decide
    simp only [rectSlots,h0,h1,Nat.mul_zero,Nat.sub_zero]
    exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  refine ⟨hfull, ?_⟩
  by_contra! hv
  let E:=f.natDegree
  let T:=rectWitness E
  obtain ⟨hside,hbox⟩:=witness_guards he hfull.le
  obtain ⟨hlo,hhi,hsum⟩:=paid_order he hfull
  have hcost:=Pr657Rect2435Receipts.rect_bounds hl hraw he hfull.le
  have hdegree : T.order 0 + T.order 1 ≤ axisDegree f 0 + axisDegree f 1 := by
    rw [hsum]
    exact hv
  by_cases hor:axisDegree f 0≤axisDegree f 1
  · refine reject_shape hbank hw C Q hf hprod (le_refl E) he T.U T.order hbox ?_ hcost
    intro r
    exact oriented_rect_capacity_le hside hor hlo hhi hdegree
  · have hbox' : swap T.U 0 + swap T.U 1 ≤ (terminal .h2367).shape.U := by
      change T.U 1 + T.U 0 ≤ (terminal .h2367).shape.U
      rw [Nat.add_comm (T.U 1) (T.U 0)]
      exact hbox
    exact reject_shape hbank hw C Q hf hprod (le_refl E) he (swap T.U) (swap T.order) hbox'
      (fun r => slots_reversed r hside (Nat.le_of_not_ge hor) hlo hhi hdegree)
      (Pr657Rect2435Receipts.rect_bounds_swap hl hraw he hfull.le)

#print axioms paid_degrees
end
end KoalaRect
