import ProximityPrize.SubmissionLower.R6960MainGeometryUnion
import ProximityPrize.SubmissionLower.R6960TerminalReceipts
import ProximityPrize.SubmissionLower.KoalaRectAxes

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
    (lo : 2339≤h) (hi : h≤33561) {S : Finset Surface}
    (parents : ∀ q∈S,Parent q ∧ SurfacePass Crt w q)
    {f : Equation} (product : ProjectedProduct S f) (i : Fin 49)
    (e : max 1 i.val≤f.natDegree) (U d : Fin 2→ℕ)
    (box : U 0+U 1≤terminalShape.U)
    (gain : rectDebit h terminalBank.nodeRows terminalBank.poleMoment U <
      rectGain 179827 h terminalShape (max 1 i.val) U d)
    (slots : ∀ r,rectSlots U (axisDegree f) r≤rectSlots U d r) : False := by
  have width : terminalShape.B*(131071-h)≤terminalShape.m*179827 :=
    (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left lo 131071)).trans (by decide +kernel)
  have fn : f≠0 := fun zero => by have := product.positive; simp [zero] at this
  exact (not_le_of_gt gain) (KoalaRect.rectLoss (h:=h) (by omega) (by omega)
    (lt_of_le_of_lt hi (by decide)) Crt w 179827 terminalShape U d (by decide) (by decide)
    box bank_checked.moment.2 width bank_checked.nodes.le bank_checked.moment.1 (by omega)
    (fun q hq=>(parents q hq).1) (fun q hq=>(parents q hq).2) fn e product slots)

private theorem box_guard (i : Fin 49) : (witness i.val).U 0+(witness i.val).U 1≤terminalShape.U := by
  fin_cases i <;> decide +kernel
private theorem one_sided : ∀ i : Fin 49, 0 < i.val → (witness i.val).order 0 = 0 := by decide +kernel

/-- The concrete terminal bounds the degree of the *whole* projected product.
The paired witness bounds the sum of the two seed degrees. At each positive
grade use the indicated witness in both orientations for the sharper bound. -/
theorem degrees {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : K1.I→L)
    (lo : 2339≤h) (hi : h≤33561) {S : Finset Surface}
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

/-- Every unpaid original mark is a root of this same degree-bounded
equation. If the prefix has no surviving surfaces, its own cap suffices. -/
theorem retained_equation {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (lo : 2339≤M.overhead.toNat)
    (hi : M.overhead.toNat≤33561) (regular : ∀ j i,(D.block j).eval (nodeL i)≠0)
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
