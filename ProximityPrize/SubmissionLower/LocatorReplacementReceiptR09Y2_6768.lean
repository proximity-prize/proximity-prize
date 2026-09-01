import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y40_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y41_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y42_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y43_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y44_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y45_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y46_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y47_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y48_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y49_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y50_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y51_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y52_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y53_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y54_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y55_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y56_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y57_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y58_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y59_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y2:
    ∀ y:Fin 79,40≤y.val→y.val<60→∀ b:Fin 160,
      Receipt ((⟨8,by decide⟩:Fin 17),y,b):=by
  intro y hLower hUpper b
  by_cases h41 : y.val < 41
  · have hy : y = (⟨40, by decide⟩ : Fin 79) := by
      exact Fin.eq_of_val_eq (by simp; omega)
    subst y
    exact receipt_r09_y40 b
  by_cases h42 : y.val < 42
  · have hy : y = (⟨41, by decide⟩ : Fin 79) := by
      exact Fin.eq_of_val_eq (by simp; omega)
    subst y
    exact receipt_r09_y41 b
  by_cases h43 : y.val < 43
  · have hy : y = (⟨42, by decide⟩ : Fin 79) := by
      exact Fin.eq_of_val_eq (by simp; omega)
    subst y
    exact receipt_r09_y42 b
  by_cases h44 : y.val < 44
  · have hy : y = (⟨43, by decide⟩ : Fin 79) := by
      exact Fin.eq_of_val_eq (by simp; omega)
    subst y
    exact receipt_r09_y43 b
  by_cases h45 : y.val < 45
  · have hy : y = (⟨44, by decide⟩ : Fin 79) := by
      exact Fin.eq_of_val_eq (by simp; omega)
    subst y
    exact receipt_r09_y44 b
  by_cases h46 : y.val < 46
  · have hy : y = (⟨45, by decide⟩ : Fin 79) := by
      exact Fin.eq_of_val_eq (by simp; omega)
    subst y
    exact receipt_r09_y45 b
  by_cases h47 : y.val < 47
  · have hy : y = (⟨46, by decide⟩ : Fin 79) := by
      exact Fin.eq_of_val_eq (by simp; omega)
    subst y
    exact receipt_r09_y46 b
  by_cases h48 : y.val < 48
  · have hy : y = (⟨47, by decide⟩ : Fin 79) := by
      exact Fin.eq_of_val_eq (by simp; omega)
    subst y
    exact receipt_r09_y47 b
  by_cases h49 : y.val < 49
  · have hy : y = (⟨48, by decide⟩ : Fin 79) := by
      exact Fin.eq_of_val_eq (by simp; omega)
    subst y
    exact receipt_r09_y48 b
  by_cases h50 : y.val < 50
  · have hy : y = (⟨49, by decide⟩ : Fin 79) := by
      exact Fin.eq_of_val_eq (by simp; omega)
    subst y
    exact receipt_r09_y49 b
  by_cases h51 : y.val < 51
  · have hy : y = (⟨50, by decide⟩ : Fin 79) := by
      exact Fin.eq_of_val_eq (by simp; omega)
    subst y
    exact receipt_r09_y50 b
  by_cases h52 : y.val < 52
  · have hy : y = (⟨51, by decide⟩ : Fin 79) := by
      exact Fin.eq_of_val_eq (by simp; omega)
    subst y
    exact receipt_r09_y51 b
  by_cases h53 : y.val < 53
  · have hy : y = (⟨52, by decide⟩ : Fin 79) := by
      exact Fin.eq_of_val_eq (by simp; omega)
    subst y
    exact receipt_r09_y52 b
  by_cases h54 : y.val < 54
  · have hy : y = (⟨53, by decide⟩ : Fin 79) := by
      exact Fin.eq_of_val_eq (by simp; omega)
    subst y
    exact receipt_r09_y53 b
  by_cases h55 : y.val < 55
  · have hy : y = (⟨54, by decide⟩ : Fin 79) := by
      exact Fin.eq_of_val_eq (by simp; omega)
    subst y
    exact receipt_r09_y54 b
  by_cases h56 : y.val < 56
  · have hy : y = (⟨55, by decide⟩ : Fin 79) := by
      exact Fin.eq_of_val_eq (by simp; omega)
    subst y
    exact receipt_r09_y55 b
  by_cases h57 : y.val < 57
  · have hy : y = (⟨56, by decide⟩ : Fin 79) := by
      exact Fin.eq_of_val_eq (by simp; omega)
    subst y
    exact receipt_r09_y56 b
  by_cases h58 : y.val < 58
  · have hy : y = (⟨57, by decide⟩ : Fin 79) := by
      exact Fin.eq_of_val_eq (by simp; omega)
    subst y
    exact receipt_r09_y57 b
  by_cases h59 : y.val < 59
  · have hy : y = (⟨58, by decide⟩ : Fin 79) := by
      exact Fin.eq_of_val_eq (by simp; omega)
    subst y
    exact receipt_r09_y58 b
  have hy : y = (⟨59, by decide⟩ : Fin 79) := by
    exact Fin.eq_of_val_eq (by simp; omega)
  subst y
  exact receipt_r09_y59 b
end ProximityPrize.SubmissionLower.LocatorReplacementData
