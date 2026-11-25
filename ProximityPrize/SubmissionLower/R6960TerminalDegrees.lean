import Mathlib.Data.Nat.Basic
import ProximityPrize.SubmissionLower.FrontCore82258Model
import ProximityPrize.SubmissionLower.HighCore82258TerminalArithmetic
import ProximityPrize.SubmissionLower.KoalaRectPosition
import ProximityPrize.SubmissionLower.R6960MainGeometryUnion
import ProximityPrize.SubmissionLower.R6960TerminalReceipts

-- merged module HighCore82258RectangleOrder
section Merged_HighCore82258RectangleOrder

namespace HighCore82258

private theorem transfer_capacity {x y d : ℕ} (hxy : y ≤ x) :
    (x + d) * (y - d) ≤ x * y := by
  by_cases hdy : d ≤ y
  · calc
      (x + d) * (y - d) = x * (y - d) + d * (y - d) := Nat.add_mul ..
      _ ≤ x * (y - d) + d * x :=
        Nat.add_le_add_left (Nat.mul_le_mul_left d (Nat.le_trans (Nat.sub_le y d) hxy)) _
      _ = x * y := by rw [Nat.mul_comm d x, ← Nat.mul_add, Nat.sub_add_cancel hdy]
  · simp [Nat.sub_eq_zero_of_le (by omega : y ≤ d)]

/-- When the smaller degree lies on the longer side, the balanced degree test
    dominates the remaining rectangle at each power of the polynomial. -/
theorem oriented_rect_capacity_le {u w a b lo hi r : ℕ}
    (hsides : w ≤ u) (hdegrees : a ≤ b)
    (hlohi : lo ≤ hi) (hbalanced : hi ≤ lo + 1) (hsum : lo + hi ≤ a + b) :
    (u + 1 - r * a) * (w + 1 - r * b) ≤
      (u + 1 - r * lo) * (w + 1 - r * hi) := by
  by_cases ha : lo ≤ a
  · have hb : hi ≤ b := by omega
    exact Nat.mul_le_mul
      (Nat.sub_le_sub_left (Nat.mul_le_mul_left r ha) _)
      (Nat.sub_le_sub_left (Nat.mul_le_mul_left r hb) _)
  by_cases hshort : w + 1 ≤ r * b
  · simp [Nat.sub_eq_zero_of_le hshort]
  have hb : hi ≤ b := by omega
  have hhi_prod := Nat.mul_le_mul_left r hb
  have hlo_prod := Nat.mul_le_mul_left r hlohi
  have ha_prod := Nat.mul_le_mul_left r (show a ≤ lo by omega)
  have hx := Nat.mul_le_mul_left r (show hi + (lo - a) ≤ b by omega)
  rw [Nat.mul_add] at hx
  let x := u + 1 - r * lo
  let y := w + 1 - r * hi
  let d := r * (lo - a)
  have hl : u + 1 - r * a = x + d := by
    dsimp [x, d]
    rw [Nat.mul_sub_left_distrib]
    omega
  have hr : w + 1 - r * b ≤ y - d := by
    dsimp [y, d]
    omega
  have hyx : y ≤ x := by
    dsimp [x, y]
    omega
  rw [hl]
  exact Nat.le_trans (Nat.mul_le_mul_left _ hr) (transfer_capacity hyx)

#print axioms oriented_rect_capacity_le

end HighCore82258

end Merged_HighCore82258RectangleOrder

-- merged module KoalaRectAxes
section Merged_KoalaRectAxes

namespace KoalaRectAxes

open KoalaRect (area rectDebit rectGain rectSlots)
open K1_14 (Shape)

def swap (u : Fin 2 → ℕ) : Fin 2 → ℕ := ![u 1, u 0]

@[simp] theorem swap_zero (u : Fin 2 → ℕ) : swap u 0 = u 1 := rfl
@[simp] theorem swap_one (u : Fin 2 → ℕ) : swap u 1 = u 0 := rfl

theorem slots_swap (u d : Fin 2 → ℕ) (r : ℕ) :
    rectSlots (swap u) (swap d) r = rectSlots u d r := by
  simp only [rectSlots, swap_zero, swap_one]
  exact Nat.mul_comm _ _

theorem debit_swap (h nodes moment : ℕ) (u : Fin 2 → ℕ) :
    rectDebit h nodes moment (swap u) = rectDebit h nodes moment u := by
  simp only [rectDebit, area, swap_zero, swap_one]
  ring

theorem gain_swap (A h : ℕ) (s : Shape) (E : ℕ) (u d : Fin 2 → ℕ) :
    rectGain A h s E (swap u) (swap d) = rectGain A h s E u d := by
  simp only [rectGain, slots_swap]

theorem slots_reversed {u d actual : Fin 2 → ℕ} (r : ℕ)
    (hsides : u 1 ≤ u 0) (hdegree : actual 1 ≤ actual 0)
    (horder : d 0 ≤ d 1) (hbalanced : d 1 ≤ d 0 + 1)
    (hsum : d 0 + d 1 ≤ actual 0 + actual 1) :
    rectSlots (swap u) actual r ≤ rectSlots (swap u) (swap d) r := by
  have h := HighCore82258.oriented_rect_capacity_le (r := r) hsides hdegree horder hbalanced
    (by omega : d 0 + d 1 ≤ actual 1 + actual 0)
  simpa only [rectSlots, swap_zero, swap_one, Nat.mul_comm] using h


#print axioms slots_reversed

end KoalaRectAxes

end Merged_KoalaRectAxes

-- merged module R6960TerminalDegrees
section Merged_R6960TerminalDegrees
noncomputable section
set_option Elab.async false
namespace Lower6960.TerminalDegrees
open Polynomial Finset
open K1_14 (Equation L atMark jetAt)
open K1_14_1 (PoleData CRTLift nodeL MarkResidues)
open K1_14_3 (Surface Parent ProjectedProduct)
open KoalaRect (axisDegree rectGain rectDebit rectSlots)
open KoalaRectAxes (swap)
open RescueGeometry (Model Family SurfacePass OnSurface terminalShape word)
open TerminalReceipts (terminalBank witness bank_checked positive)
private theorem reject {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : K1.I→L)
    (lo : 2402≤h) (hi : h≤33619) {S : Finset Surface}
    (parents : ∀ q∈S,Parent q ∧ SurfacePass Crt w q)
    {f : Equation} (product : ProjectedProduct S f) (i : Fin 49)
    (e : max 1 i.val≤f.natDegree) (U d : Fin 2→ℕ)
    (box : U 0+U 1≤terminalShape.U)
    (gain : rectDebit h terminalBank.nodeRows terminalBank.poleMoment U <
      rectGain 179798 h terminalShape (max 1 i.val) U d)
    (slots : ∀ r,rectSlots U (axisDegree f) r≤rectSlots U d r) : False := by
  have width : terminalShape.B*(131071-h)≤terminalShape.m*179798 :=
    (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left lo 131071)).trans (by decide +kernel)
  have fn : f≠0 := fun zero => by have := product.positive; simp [zero] at this
  exact (not_le_of_gt gain) (KoalaRect.rectLoss (h:=h) (by omega) (by omega)
    (lt_of_le_of_lt hi (by decide)) Crt w 179798 terminalShape U d (by decide) (by decide)
    box bank_checked.moment.2 width bank_checked.nodes.le bank_checked.moment.1 (by omega)
    (fun q hq=>(parents q hq).1) (fun q hq=>(parents q hq).2) fn e product slots)
private theorem box_guard (i : Fin 49) : (witness i.val).U 0+(witness i.val).U 1≤terminalShape.U := by
  fin_cases i <;> decide +kernel
private theorem one_sided : ∀ i : Fin 49, 0 < i.val → (witness i.val).order 0 = 0 := by decide +kernel
theorem degrees {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : K1.I→L)
    (lo : 2402≤h) (hi : h≤33619) {S : Finset Surface}
    (parents : ∀ q∈S,Parent q ∧ SurfacePass Crt w q) {f : Equation} (product : ProjectedProduct S f) :
    f.natDegree<48 ∧ axisDegree f 0+axisDegree f 1≤2400 ∧
    ∀ j : Fin 2,axisDegree f j<(witness f.natDegree).order 1 := by
  have ne := product.positive
  have rule (i : Fin 49) (e : max 1 i.val≤f.natDegree) :
      ¬(∀ r,rectSlots (witness i.val).U (axisDegree f) r≤
        rectSlots (witness i.val).U (witness i.val).order r) :=
    reject Crt w lo hi parents product i e _ _ (box_guard i) (positive lo hi i)
  have rev (i : Fin 49) (e : max 1 i.val≤f.natDegree) :
      ¬(∀ r,rectSlots (swap (witness i.val).U) (axisDegree f) r≤
        rectSlots (swap (witness i.val).U) (swap (witness i.val).order) r) := by
    apply reject Crt w lo hi parents product i e
    · simpa [Nat.add_comm] using box_guard i
    · rw [KoalaRectAxes.debit_swap,KoalaRectAxes.gain_swap]
      exact positive lo hi i
  have grade : f.natDegree<48 := by
    by_contra! bad
    apply rule 48 (by simpa using bad)
    intro r
    change (_+1-r*axisDegree f 0)*(_+1-r*axisDegree f 1) ≤ (_+1-r*0)*(_+1-r*0)
    simp only [Nat.mul_zero,Nat.sub_zero]
    exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  refine ⟨grade,?_,?_⟩
  · by_contra! large
    let t:=witness 0
    have guards : t.U 1≤t.U 0 ∧ t.order 0≤t.order 1 ∧ t.order 1≤t.order 0+1 ∧ t.order 0+t.order 1=2401 := by decide
    have deg : t.order 0+t.order 1≤axisDegree f 0+axisDegree f 1 := by omega
    by_cases axis : axisDegree f 0≤axisDegree f 1
    · apply rule 0 (by change 1 ≤ f.natDegree; omega)
      exact fun r=>HighCore82258.oriented_rect_capacity_le guards.1 axis guards.2.1 guards.2.2.1 deg
    · apply rev 0 (by change 1 ≤ f.natDegree; omega)
      exact fun r=>KoalaRectAxes.slots_reversed r guards.1 (by omega) guards.2.1 guards.2.2.1 deg
  · let i : Fin 49 := ⟨f.natDegree,by omega⟩
    let t:=witness f.natDegree
    have reach : max 1 i.val ≤ f.natDegree := max_le ne le_rfl
    have z0 : t.order 0=0 := one_sided i ne
    intro j
    by_contra! bad
    fin_cases j
    · apply rev i reach
      intro r
      apply Nat.mul_le_mul (Nat.sub_le_sub_left (Nat.mul_le_mul_left r bad) _)
      change _≤_+1-r*t.order 0
      rw [z0,Nat.mul_zero,Nat.sub_zero]; exact Nat.sub_le _ _
    · apply rule i reach
      intro r
      apply Nat.mul_le_mul _ (Nat.sub_le_sub_left (Nat.mul_le_mul_left r bad) _)
      change _≤_+1-r*t.order 0
      rw [z0,Nat.mul_zero,Nat.sub_zero]; exact Nat.sub_le _ _
theorem retained_equation {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (lo : 2402≤M.overhead.toNat)
    (hi : M.overhead.toNat≤33619) (regular : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    Γ.card≤MainGeometry.prefixCap ∨
      ∃ (paid : Finset K1.K) (f : Equation), paid.card≤MainGeometry.prefixCap ∧
        f.IsPrimitive ∧ (f.map (algebraMap K1_14.Seeds K1_14_2.SeedField)).Separable ∧
        0<f.natDegree ∧ f.natDegree<48 ∧ axisDegree f 0+axisDegree f 1≤2400 ∧
        (∀ j : Fin 2,axisDegree f j<(witness f.natDegree).order 1) ∧
        ∀ γ∈Γ, γ∉paid → atMark f (M.label γ) (F.scalar γ)=0 := by
  classical
  obtain ⟨paid,S,cap,geom,prod,cover⟩ := MainGeometry.combined_prefix F Crt lo hi regular residues
  by_cases has : S.Nonempty
  · obtain ⟨f,p⟩ := prod has
    obtain ⟨size,total,axis⟩ := degrees Crt (word M) lo hi geom p
    refine Or.inr ⟨paid,f,cap,p.primitive,p.separable,p.positive,size,total,axis,?_⟩
    intro γ hg outside
    obtain ⟨q,hq,on⟩ := (cover γ hg).resolve_left outside
    simpa only [jetAt,eval₂_C,coe_eval₂RingHom,atMark] using on _ (p.vanishes q hq)
  · apply Or.inl
    apply le_trans (Finset.card_le_card (s:=Γ) (t:=paid) ?_) cap
    intro γ hg
    exact (cover γ hg).resolve_right (fun ⟨q,hq,_⟩=>has ⟨q,hq⟩)
#print axioms degrees
#print axioms retained_equation
end Lower6960.TerminalDegrees

end
end Merged_R6960TerminalDegrees
