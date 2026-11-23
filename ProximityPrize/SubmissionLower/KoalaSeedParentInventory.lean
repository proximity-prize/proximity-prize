import ProximityPrize.SubmissionLower.HighCore82258ScheduleData

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false

open FrontCore82258 (effectiveHeight)

namespace HighCore82258_3
noncomputable section
open HighCore82258 (AnchorModel AnchoredFamily InBand Source CurveTariff PrefixBooks fees gradedLoss start)
open K1_14 (Banks)
open scoped Classical

structure SeedParentInventory (b : HighCore82258.Band) {u del}
    (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ) {rows : Banks}
    (pairs : HighCore82258.Pairs b (effectiveHeight M).toNat rows)
    extends HighCore82258.GradedInventory b M F pairs where
  loss_seed_paid : inventory.books.loss.card + inventory.books.lowSeed.card ≤
    gradedLoss b equation.natDegree + initialE b

def SeedParentC3 : Prop :=
  ∀ (b : HighCore82258.Band) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b (effectiveHeight M) → M.shift ∉ Γ → ∀ H, HighCore82258.AdjacentChart M F H →
    ((start b) < 7773 → CurveTariff b M F) →
    ∀ rows, Source b M F rows → ∀ pairs : HighCore82258.Pairs b (effectiveHeight M).toNat rows,
    Nonempty (SeedParentInventory b M F pairs)

def seedParentPrefix (b : HighCore82258.Band) (e : ℕ) : ℕ :=
  gradedLoss b e + (fees b).point + initialE b + (fees b).lowJet +
    (fees b).fixedODE + (fees b).content

theorem SeedParentInventory.card_books {b u del} {M : AnchorModel u del} {Γ}
    {F : AnchoredFamily M Γ} {rows : Banks} {pairs : HighCore82258.Pairs b (effectiveHeight M).toNat rows}
    (I : SeedParentInventory b M F pairs) :
    I.inventory.books.union.card ≤ seedParentPrefix b I.equation.natDegree := by
  let B := I.inventory.books
  have h := I.loss_seed_paid
  have hcap := Finset.card_union_le B.loss B.lowSeed
  have e : B.union = (B.loss ∪ B.lowSeed) ∪ B.point ∪ B.lowJet ∪ B.fixedODE ∪ B.content := by
    ext γ
    simp only [PrefixBooks.union,Finset.mem_union]
    tauto
  rw [e]
  unfold seedParentPrefix
  have hp := B.point_le
  have hj := B.lowJet_le
  have hf := B.fixedODE_le
  have hc := B.content_le
  have h₁ := Finset.card_union_le (B.loss ∪ B.lowSeed) B.point
  have h₂ := Finset.card_union_le ((B.loss ∪ B.lowSeed) ∪ B.point) B.lowJet
  have h₃ := Finset.card_union_le (((B.loss ∪ B.lowSeed) ∪ B.point) ∪ B.lowJet) B.fixedODE
  have h₄ := Finset.card_union_le ((((B.loss ∪ B.lowSeed) ∪ B.point) ∪ B.lowJet) ∪ B.fixedODE) B.content
  change B.loss.card + B.lowSeed.card ≤ _ at h
  omega

#print axioms SeedParentInventory.card_books

end
end HighCore82258_3
