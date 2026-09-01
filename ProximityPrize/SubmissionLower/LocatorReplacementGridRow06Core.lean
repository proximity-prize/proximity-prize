import ProximityPrize.SubmissionLower.LocatorReplacementGridRow05

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

/-- A rectangular coarse-Y/coarse-T part of a slope-row receipt. -/
def RowTileReceipt (ri : Fin 18) (ylo yhi tlo thi : ℕ) : Prop :=
  ∀ (cy : Fin 22), ylo ≤ cy.val → cy.val < yhi →
    ∀ (ct : Fin 22), tlo ≤ ct.val → ct.val < thi →
      let coarse : CoarseCell := (ri, cy, ct)
      HardCoarse coarse →
        ∀ (yi ti : Fin 4),
          ((fineBoxAt coarse yi ti).valid ∧ ¬ Fits (fineBoxAt coarse yi ti)) →
            ∀ ui : Fin 4, (unitBoxAt coarse yi ti ui).valid →
              (unitBoxAt coarse yi ti ui).ordinaryFits ∨
                ∀ pi : Fin 4, (pointBoxAt coarse yi ti ui pi).valid →
                  (pointBoxAt coarse yi ti ui pi).ordinaryFits

instance (ri : Fin 18) (ylo yhi tlo thi : ℕ) :
    Decidable (RowTileReceipt ri ylo yhi tlo thi) := by
  unfold RowTileReceipt
  infer_instance

/-- A receipt for one fixed coarse-Y cell and a half-open range of coarse-T
cells.  Unlike `RowTileReceipt`, its decision procedure does not enumerate
the other twenty values of `Fin 22`. -/
def FixedYReceipt (ri : Fin 18) (cy : Fin 22) (tlo thi : ℕ) : Prop :=
  ∀ (ct : Fin 22), tlo ≤ ct.val → ct.val < thi →
    let coarse : CoarseCell := (ri, cy, ct)
    HardCoarse coarse →
      ∀ (yi ti : Fin 4),
        ((fineBoxAt coarse yi ti).valid ∧ ¬ Fits (fineBoxAt coarse yi ti)) →
          ∀ ui : Fin 4, (unitBoxAt coarse yi ti ui).valid →
            (unitBoxAt coarse yi ti ui).ordinaryFits ∨
              ∀ pi : Fin 4, (pointBoxAt coarse yi ti ui pi).valid →
                (pointBoxAt coarse yi ti ui pi).ordinaryFits

instance (ri : Fin 18) (cy : Fin 22) (tlo thi : ℕ) :
    Decidable (FixedYReceipt ri cy tlo thi) := by
  unfold FixedYReceipt
  infer_instance

/-- Adapt a fixed-Y receipt to the existing singleton-Y tile interface. -/
theorem fixedYReceipt_to_rowTile (ri : Fin 18) (cy : Fin 22) (tlo thi : ℕ)
    (h : FixedYReceipt ri cy tlo thi) :
    RowTileReceipt ri cy.val (cy.val + 1) tlo thi := by
  intro cy' hylo hyhi ct htlo hthi
  have hcy : cy' = cy := by
    apply Fin.ext
    omega
  subst cy'
  exact h ct htlo hthi

/-- Adapt a full-total-range fixed-Y receipt to the existing singleton-Y band
interface. -/
theorem fixedYReceipt_to_rowBand (ri : Fin 18) (cy : Fin 22)
    (h : FixedYReceipt ri cy 0 22) :
    RowBandReceipt ri cy.val (cy.val + 1) := by
  intro cy' hylo hyhi ct
  have hcy : cy' = cy := by
    apply Fin.ext
    omega
  subst cy'
  exact h ct (Nat.zero_le _) ct.isLt

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
