import ProximityPrize.SubmissionLower.R6966ProofFarRetained
import ProximityPrize.SubmissionLower.R6966ProofFarPrefix
import ProximityPrize.SubmissionLower.R6966ProofFarPoleChart
import ProximityPrize.SubmissionLower.R6960TerminalDegrees

set_option Elab.async false

namespace Research6966.FarTerminalCount
open Polynomial Finset
open K1 (K)
open K1_14 (Equation L atMark jetAt)
open K1_14_1 (PoleData CRTLift nodeL MarkResidues)
open K1_14_3 (Surface Parent ProjectedProduct)
open KoalaRect (axisDegree rectGain rectDebit rectSlots)
open KoalaRectAxes (swap)
open Lower6960
open FarRescueGeometry (Model Family SurfacePass terminalShape word)
open FarTerminalReceipts (terminalBank witness bank_checked positive)
open scoped Polynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

private theorem reject {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : K1.I→L)
    (lo : 2500≤h) (hi : h≤33677) {S : Finset Surface}
    (parents : ∀ q∈S, Parent q ∧ SurfacePass Crt w q)
    {f : Equation} (product : ProjectedProduct S f) (e : ℕ)
    (ep : 0<e) (en : e≤f.natDegree) (U d : Fin 2→ℕ)
    (box : U 0+U 1≤terminalShape.U)
    (gain : rectDebit h terminalBank.nodeRows terminalBank.poleMoment U <
      rectGain 179769 h terminalShape e U d)
    (slots : ∀ r,rectSlots U (axisDegree f) r≤rectSlots U d r) : False := by
  have width : terminalShape.B*(131071-h)≤terminalShape.m*179769 :=
    (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left lo 131071)).trans (by decide +kernel)
  exact (not_le_of_gt gain) (KoalaRect.rectLoss (h:=h) (by omega) (by omega)
    (lt_of_le_of_lt hi (by decide)) Crt w 179769 terminalShape U d (by decide) (by decide)
    box bank_checked.moment.2 width bank_checked.nodes.le bank_checked.moment.1 ep
    (fun q hq=>(parents q hq).1) (fun q hq=>(parents q hq).2.original)
    product.primitive.ne_zero en product slots)

private theorem box_guard (i : Fin 41) : (witness i.val).U 0+(witness i.val).U 1≤terminalShape.U := by
  fin_cases i <;> decide +kernel

private theorem one_sided (i : Fin 41) : (witness i.val).order 0=0 := by
  fin_cases i <;> decide +kernel

theorem degrees {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : K1.I→L)
    (lo : 2500≤h) (hi : h≤33677) {S : Finset Surface}
    (parents : ∀ q∈S, Parent q ∧ SurfacePass Crt w q) {f : Equation} (product : ProjectedProduct S f) :
    f.natDegree<40 ∧ ∀ j : Fin 2, axisDegree f j<(witness f.natDegree).order 1 := by
  have rule (i : Fin 41) (ip : 0 < i.val) (e : i.val≤f.natDegree) :
      ¬(∀ r,rectSlots (witness i.val).U (axisDegree f) r≤
        rectSlots (witness i.val).U (witness i.val).order r) :=
    reject Crt w lo hi parents product i.val ip e _ _ (box_guard i) (positive lo hi i ip)
  have rev (i : Fin 41) (ip : 0 < i.val) (e : i.val≤f.natDegree) :
      ¬(∀ r,rectSlots (swap (witness i.val).U) (axisDegree f) r≤
        rectSlots (swap (witness i.val).U) (swap (witness i.val).order) r) := by
    apply reject Crt w lo hi parents product i.val ip e
    · simpa [Nat.add_comm] using box_guard i
    · rw [KoalaRectAxes.debit_swap,KoalaRectAxes.gain_swap]
      exact positive lo hi i ip
  have grade : f.natDegree<40 := by
    by_contra! big
    apply rule 40 (by decide) (by simpa using big)
    intro r
    change (_+1-r*axisDegree f 0)*(_+1-r*axisDegree f 1) ≤ (_+1-r*0)*(_+1-r*0)
    simp only [Nat.mul_zero,Nat.sub_zero]
    exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  refine ⟨grade,?_⟩
  let i : Fin 41 := ⟨f.natDegree,by omega⟩
  let t:=witness f.natDegree
  have ip : 0 < i.val := product.positive
  have z0 : t.order 0=0 := one_sided i
  intro j
  by_contra! bad
  fin_cases j
  · apply rev i ip le_rfl
    intro r
    apply Nat.mul_le_mul (Nat.sub_le_sub_left (Nat.mul_le_mul_left r bad) _)
    change _≤_+1-r*t.order 0
    rw [z0,Nat.mul_zero,Nat.sub_zero]; exact Nat.sub_le _ _
  · apply rule i ip le_rfl
    intro r
    apply Nat.mul_le_mul _ (Nat.sub_le_sub_left (Nat.mul_le_mul_left r bad) _)
    change _≤_+1-r*t.order 0
    rw [z0,Nat.mul_zero,Nat.sub_zero]; exact Nat.sub_le _ _

/-- The unchanged far-bank producer and its far-band terminal price
give the count for the actual family at every height 2500 through 33677. -/
theorem count {u deleted} (M : P1.ModelAt 33677 u deleted) {Γ : Finset K} (F : P1.FamilyAt 179769 M Γ)
    (lo : 2500≤M.overhead) (hi : M.overhead≤33677) :
    Γ.card≤274790602290452470 := by
  classical
  have hlo : 2500≤M.overhead.toNat := by omega
  have hhi : M.overhead.toNat≤33677 := by omega
  obtain ⟨D,⟨Crt⟩,regular,residues⟩ := FarPoleChart.of_family M F
  obtain ⟨paid,S,fee,geom,prod,cover⟩ := FarMainGeometry.combined_prefix F Crt hlo hhi regular residues
  by_cases surfaces : S.Nonempty
  · obtain ⟨f,project⟩ := prod surfaces
    obtain ⟨grade,axes⟩ := degrees Crt (word M) hlo hhi geom project
    let T := Γ\paid
    have sub : T⊆Γ := sdiff_subset
    have words : RetainedShortening.Word 179769 164748 M.word F.scalar T := by
      refine ⟨F.distinct.mono sub,?_,?_⟩
      · intro γ hγ
        rcases (F.mark γ (sub hγ)).scalar_degree with zero|degree
        · simp [zero]
        · change ((F.scalar γ).natDegree:ℤ)≤131071+M.overhead at degree
          omega
      · intro γ hγ
        let mark:=F.mark γ (sub hγ)
        exact ⟨mark.bad.support,mark.bad.agreement,mark.scalar_hits⟩
    have remain := FarRetained.count words M.label (FarRescueGeometry.label_injective M) f
      project.positive grade project.separable axes (by
        intro γ hγ
        obtain ⟨mem,out⟩ := mem_sdiff.mp hγ
        obtain ⟨q,hq,on⟩ := (cover γ mem).resolve_left out
        simpa only [jetAt,eval₂_C,coe_eval₂RingHom,atMark] using on _ (project.vanishes q hq))
    have sizes := card_sdiff_add_card_inter Γ paid
    have left : (Γ∩paid).card≤paid.card := card_le_card inter_subset_right
    change T.card+(Γ∩paid).card=Γ.card at sizes
    have final := Nat.add_le_add remain (left.trans fee)
    rw [sizes] at final
    exact final.trans (by decide +kernel)
  · have contain : Γ⊆paid := by
      intro γ hγ
      exact (cover γ hγ).resolve_right (fun ⟨q,hq,_⟩=>surfaces ⟨q,hq⟩)
    exact (card_le_card contain).trans (fee.trans (by decide +kernel))

#print axioms degrees
#print axioms count
end Research6966.FarTerminalCount
