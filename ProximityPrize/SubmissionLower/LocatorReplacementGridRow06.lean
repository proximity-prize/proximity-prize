import ProximityPrize.SubmissionLower.LocatorReplacementGridRow05

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_06_band_00 : RowBandReceipt 6 0 3 := by decide +kernel

theorem receipt_row_06_band_01 : RowBandReceipt 6 3 4 := by decide +kernel

theorem receipt_row_06_band_02 : RowBandReceipt 6 4 5 := by decide +kernel

theorem receipt_row_06_band_03 : RowBandReceipt 6 5 6 := by decide +kernel

theorem receipt_row_06_band_04 : RowBandReceipt 6 6 7 := by decide +kernel

theorem receipt_row_06_band_05 : RowBandReceipt 6 7 8 := by decide +kernel

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

theorem receipt_row_06_band_06_t_00 : RowTileReceipt 6 8 9 0 4 := by decide +kernel

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

theorem receipt_row_06_band_06_t_01 : RowTileReceipt 6 8 9 4 8 := by decide +kernel

theorem receipt_row_06_band_06_t_02 : RowTileReceipt 6 8 9 8 12 := by decide +kernel

theorem receipt_row_06_band_06_t_03 : RowTileReceipt 6 8 9 12 16 := by decide +kernel

theorem receipt_row_06_band_06_t_04 : RowTileReceipt 6 8 9 16 20 := by decide +kernel

theorem receipt_row_06_band_06_t_05 : RowTileReceipt 6 8 9 20 22 := by decide +kernel

theorem receipt_row_06_band_06 : RowBandReceipt 6 8 9 := by
  intro cy hylo hyhi ct
  by_cases h₀ : ct.val < 4
  · exact receipt_row_06_band_06_t_00 cy hylo hyhi ct (Nat.zero_le _) h₀
  by_cases h₁ : ct.val < 8
  · exact receipt_row_06_band_06_t_01 cy hylo hyhi ct (by omega) h₁
  by_cases h₂ : ct.val < 12
  · exact receipt_row_06_band_06_t_02 cy hylo hyhi ct (by omega) h₂
  by_cases h₃ : ct.val < 16
  · exact receipt_row_06_band_06_t_03 cy hylo hyhi ct (by omega) h₃
  by_cases h₄ : ct.val < 20
  · exact receipt_row_06_band_06_t_04 cy hylo hyhi ct (by omega) h₄
  · exact receipt_row_06_band_06_t_05 cy hylo hyhi ct (by omega) (by omega)

theorem receipt_row_06_band_07 : RowBandReceipt 6 9 10 := by decide +kernel

theorem receipt_row_06_band_08 : RowBandReceipt 6 10 11 := by decide +kernel

theorem receipt_row_06_band_09 : RowBandReceipt 6 11 12 := by decide +kernel

theorem receipt_row_06_band_10 : RowBandReceipt 6 12 13 := by decide +kernel

theorem receipt_row_06_band_11 : RowBandReceipt 6 13 14 := by decide +kernel

theorem receipt_row_06_band_12 : RowBandReceipt 6 14 22 := by decide +kernel

theorem receipt_row_06 : RowReceipt 6 := by
  intro cy
  by_cases h₀ : cy.val < 3
  · exact receipt_row_06_band_00 cy (Nat.zero_le _) h₀
  by_cases h_4 : cy.val < 4
  · exact receipt_row_06_band_01 cy (by omega) h_4
  by_cases h_5 : cy.val < 5
  · exact receipt_row_06_band_02 cy (by omega) h_5
  by_cases h_6 : cy.val < 6
  · exact receipt_row_06_band_03 cy (by omega) h_6
  by_cases h_7 : cy.val < 7
  · exact receipt_row_06_band_04 cy (by omega) h_7
  by_cases h_8 : cy.val < 8
  · exact receipt_row_06_band_05 cy (by omega) h_8
  by_cases h_9 : cy.val < 9
  · exact receipt_row_06_band_06 cy (by omega) h_9
  by_cases h_10 : cy.val < 10
  · exact receipt_row_06_band_07 cy (by omega) h_10
  by_cases h_11 : cy.val < 11
  · exact receipt_row_06_band_08 cy (by omega) h_11
  by_cases h_12 : cy.val < 12
  · exact receipt_row_06_band_09 cy (by omega) h_12
  by_cases h_13 : cy.val < 13
  · exact receipt_row_06_band_10 cy (by omega) h_13
  by_cases h_14 : cy.val < 14
  · exact receipt_row_06_band_11 cy (by omega) h_14
  · exact receipt_row_06_band_12 cy (by omega) (by omega)

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
