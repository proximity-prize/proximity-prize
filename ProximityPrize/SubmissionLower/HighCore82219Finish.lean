import ProximityPrize.SubmissionLower.HighCore82219PrefixGeometry
import ProximityPrize.SubmissionLower.HighCore82219Ledger
import ProximityPrize.SubmissionLower.HighCore82219Regular
import ProximityPrize.SubmissionLower.HighCore82268Finish

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000


namespace HighCore82219

theorem prefix_inventory : c3 :=
  HighCore82219_3.of_children HighCore82219_3_1.proof HighCore82219_3_2.proof
    schedule loss_ledger

theorem intermediate_high {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hl : 2405 ≤ M.overhead) (hu : M.overhead ≤ 2526) :
    Γ.card ≤ 269280325386559022 :=
  first_high_of_prefix_and_retained prefix_inventory tangent_count M F hl hu

def asFarModel {u del} (M : AnchorModel u del) : HighCore82268.AnchorModel u del :=
  { M with height_bound := M.height_bound.trans (by decide) }

def asFarFamily {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ) :
    HighCore82268.AnchoredFamily (asFarModel M) Γ where
  scalar := F.scalar
  distinct := F.distinct
  mark γ hγ := by
    let m := F.mark γ hγ
    let B : P1.BadMarkAt HighCore82268.agreement u γ :=
      { m.bad with agreement := (by decide : HighCore82268.agreement ≤ agreement).trans m.bad.agreement }
    exact ⟨B, m.avoids_deleted, m.scalar_fixed, m.scalar_degree, m.scalar_hits, m.pole_unit, m.identity⟩

theorem ordinary_high {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hl : 2405 ≤ M.overhead) (hu : M.overhead ≤ (heightCap : ℤ)) :
    Γ.card ≤ 269280325386559022 := by
  by_cases hwindow : M.overhead ≤ 2526
  · exact intermediate_high M F hl hwindow
  have hf : 2527 ≤ (asFarModel M).overhead := by
    change 2527 ≤ M.overhead
    omega
  have ht : (asFarModel M).overhead ≤ (HighCore82268.heightCap : ℤ) := by
    change M.overhead ≤ 33463
    change M.overhead ≤ 33365 at hu
    omega
  exact (HighCore82268.ordinary_high_from2527 (asFarModel M) (asFarFamily M F) hf ht).trans (by decide)

#print axioms ordinary_high
#print axioms intermediate_high
end HighCore82219
