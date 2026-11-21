import ProximityPrize.SubmissionLower.Rect52TerminalReceipts1
import ProximityPrize.SubmissionLower.Rect52TerminalReceipts4
import ProximityPrize.SubmissionLower.Rect52TerminalReceipts7
import ProximityPrize.SubmissionLower.Rect52TerminalReceipts10
import ProximityPrize.SubmissionLower.Rect52TerminalReceipts13
import ProximityPrize.SubmissionLower.Rect52TerminalReceipts16
import ProximityPrize.SubmissionLower.Rect52TerminalReceipts19
import ProximityPrize.SubmissionLower.Rect52TerminalReceipts22
import ProximityPrize.SubmissionLower.Rect52TerminalReceiptsStock
import ProximityPrize.SubmissionLower.Rect52TerminalLoss
import ProximityPrize.SubmissionLower.Rect52Prefix

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 1400000

namespace Rect52TerminalProof

noncomputable section

open K1 (I)
open K1_14 K1_14_1 Polynomial Finset
open K1_14_3 (RowCaps Surface Parent ProjectedProduct)
open P1_7_1 (nodeRows groupedPoleMoment)
open Rect52Terminal
open Rect52Prefix (AnchorModel AnchoredFamily)
export Rect52Terminal (cap)
open scoped BigOperators

theorem rectangle_checks {e : ℕ} (he : 1 ≤ e ∧ e ≤ 22) :
    0 < rectangleSurplus 2391 e (long e) (short e) ((cap e+1)/2) ((cap e+2)/2) ∧
      rectangleSurplus 2391 e (long e) (short e) ((cap e+1)/2) ((cap e+2)/2) ≤
        rectangleSurplus 2392 e (long e) (short e) ((cap e+1)/2) ((cap e+2)/2) := by
  obtain ⟨hlo,hhi⟩ := he
  interval_cases e
  · exact rectangleCheck1
  · exact rectangleCheck2
  · exact rectangleCheck3
  · exact rectangleCheck4
  · exact rectangleCheck5
  · exact rectangleCheck6
  · exact rectangleCheck7
  · exact rectangleCheck8
  · exact rectangleCheck9
  · exact rectangleCheck10
  · exact rectangleCheck11
  · exact rectangleCheck12
  · exact rectangleCheck13
  · exact rectangleCheck14
  · exact rectangleCheck15
  · exact rectangleCheck16
  · exact rectangleCheck17
  · exact rectangleCheck18
  · exact rectangleCheck19
  · exact rectangleCheck20
  · exact rectangleCheck21
  · exact rectangleCheck22


theorem rect_strict {h e : ℕ} (hl : 2391 ≤ h) (hu : h ≤ 2451) (he : 1 ≤ e ∧ e ≤ 22) :
    rectangleDebit h (long e) (short e) <
      Rect52Terminal.jointGain h bank.shape e (Rect52Terminal.slots (long e) (short e) ((cap e+1)/2) ((cap e+2)/2)) :=
  rectangle_strict_of_first_difference hl (by omega) (rectangle_checks he).1 (rectangle_checks he).2

theorem rect_excludes {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    {e : ℕ} {f : Equation} (hl : 2391 ≤ h) (hu : h ≤ 2451) (he : 1 ≤ e ∧ e ≤ 22)
    (hf : f ≠ 0) (hE : e ≤ f.natDegree)
    (hnodes : nodeRows bank.shape = bank.nodeRows)
    (hmoment : groupedPoleMoment bank.shape.B bank.shape.J ≤ bank.poleMoment)
    (hcap : ∀ W, ∀ P ∈ evaluated Crt word bank.shape W, RowCaps P bank.shape)
    (hlead : ∀ W, ∀ P ∈ evaluated Crt word bank.shape W, P ≠ 0 →
      (P.leadingCoeff.natDegree+P.natDegree)*(131071-h) ≤ W+P.natDegree)
    (hdvd : ∀ W < bank.shape.m*High52.agreement, ∀ P ∈ evaluated Crt word bank.shape W, P ≠ 0 →
      f^(High52.contactPower h bank.shape W-P.natDegree) ∣ P.leadingCoeff) :
    Rect51Rank.coordDegree f (some 0) + Rect51Rank.coordDegree f (some 1) ≤ cap e := by
  by_contra! hseed
  have hshort : short e ≤ bank.shape.U := by unfold short; split_ifs <;> decide
  have htotal : long e + short e ≤ bank.shape.U := by
    unfold long
    omega
  have horient : short e ≤ long e := by unfold long short; split_ifs <;> decide
  exact (not_le_of_gt (rect_strict hl hu he))
    (rectangle_loss_of_bank Crt word hl hu (by omega) htotal horient hf hE hseed
      hnodes hmoment hcap hlead hdvd)

theorem stock_reject {h : ℕ} (hl : 2391 ≤ h) (hu : h ≤ 2451) :
    High52.debit h bank < High52.jointGain h bank.shape 23 0 := by
  have hL := High52TerminalArithmetic.blockSurplus_eq bank 2391 23 0 (by decide) (by decide) (by decide)
  have hR := High52TerminalArithmetic.blockSurplus_eq bank 2392 23 0 (by decide) (by decide) (by decide)
  have ⟨hp, hr⟩ := stockCheck23
  rw [hL] at hp
  rw [hL,hR] at hr
  exact High52TerminalArithmetic.strict_of_first_difference hl (by omega)
    (by omega) (by
      change High52TerminalArithmetic.surplus 2391 bank 23 0 ≤
        High52TerminalArithmetic.surplus 2392 bank 23 0
      omega)

theorem stock_trace_loss {h e v : ℕ} {rows : Banks} {f : Equation}
    (hl : 2391 ≤ h) (hu : h ≤ 2451) (he : 0 < e)
    (hf : f ≠ 0) (hE : e ≤ f.natDegree) (hV : v ≤ K1_14_4.seedDegree f)
    (trace : High52.TerminalTrace h bank rows f) :
    High52.jointGain h bank.shape e v ≤ High52.debit h bank := by
  let T := bank.shape.m * High52.agreement
  have hT : T-1+1 = T := by decide
  have hfloor := trace.floor_bound (T-1) (by decide) (by
    intro q hq j _
    rw [hT]
    exact (Nat.mul_le_mul hq (Nat.sub_le_sub_left hl _)).trans
      ((show bank.shape.B * (131071-2391) ≤ T by decide).trans (Nat.le_add_right _ _)))
  rw [hT] at hfloor
  exact stock_loss hl hu he hf hE hV hfloor trace.shape trace.leading trace.divides

theorem stock_rejects_degree {h : ℕ} {rows : Banks} {f : Equation}
    (hl : 2391 ≤ h) (hu : h ≤ 2451) (hf : f ≠ 0)
    (trace : High52.TerminalTrace h bank rows f) : f.natDegree ≤ 22 := by
  by_contra! hE
  exact (not_le_of_gt (stock_reject hl hu))
    (stock_trace_loss hl hu (by decide) hf hE (Nat.zero_le _) trace)

private theorem trace_from_prefix {h : ℕ} {rows : Banks} {f : Equation}
    (ht : Rect52Prefix.TerminalTrace h (Rect52Prefix.terminal .h2391) rows f) :
    High52.TerminalTrace h bank rows f :=
  ⟨ht.floor_bound, ht.shape, ht.leading, ht.divides⟩

theorem prefix_rect_bounds {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (src : Rect52Prefix.Source .h2391 M F
      (evaluated Crt (fun i => algebraMap P1.K L (M.word i))))
    (hw : Rect52Prefix.InBand .h2391 M.overhead)
    {qs : Finset Surface} (hq : ∀ q ∈ qs, Parent q)
    (hp : ∀ q ∈ qs, Rect52Prefix.BankPass
      (evaluated Crt (fun i => algebraMap P1.K L (M.word i)))
      (Rect52Prefix.terminal .h2391).shape q)
    {f : Equation} (hf : ProjectedProduct qs f) (hn : f ≠ 0) {e : ℕ}
    (he : 1 ≤ e ∧ e ≤ 22) (hE : e ≤ f.natDegree) :
    Rect51Rank.coordDegree f (some 0) + Rect51Rank.coordDegree f (some 1) ≤ cap e := by
  have ht := trace_from_prefix (Rect52Prefix.trace_of_full src hw hq hp hf none)
  have ⟨hl,hu⟩ := Rect52Prefix.window_nat hw
  exact rect_excludes Crt (fun i => algebraMap P1.K L (M.word i))
    hl hu he hn hE Rect52Prefix.terminal_nodes Rect52Prefix.terminal_moment
    ht.shape ht.leading ht.divides

/-- Apply the terminal tests to a projected product in the prefix's actual CRT source. -/
theorem prefix_bounds {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (src : Rect52Prefix.Source .h2391 M F
      (evaluated Crt (fun i => algebraMap P1.K L (M.word i))))
    (hw : Rect52Prefix.InBand .h2391 M.overhead)
    {qs : Finset Surface} (hq : ∀ q ∈ qs, Parent q)
    (hp : ∀ q ∈ qs, Rect52Prefix.BankPass
      (evaluated Crt (fun i => algebraMap P1.K L (M.word i)))
      (Rect52Prefix.terminal .h2391).shape q)
    {f : Equation} (hf : ProjectedProduct qs f) (hn : f ≠ 0) :
    f.natDegree ≤ 22 ∧
      ∀ e, 1 ≤ e → e ≤ f.natDegree → Rect51Rank.coordDegree f (some 0) + Rect51Rank.coordDegree f (some 1) ≤ cap e := by
  have ht := trace_from_prefix (Rect52Prefix.trace_of_full src hw hq hp hf none)
  have ⟨hl,hu⟩ := Rect52Prefix.window_nat hw
  have hdeg := stock_rejects_degree hl hu hn ht
  refine ⟨hdeg, fun e he hE => ?_⟩
  exact prefix_rect_bounds Crt src hw hq hp hf hn ⟨he, hE.trans hdeg⟩ hE

#print axioms rect_excludes
#print axioms stock_rejects_degree
#print axioms prefix_bounds
end
end Rect52TerminalProof
