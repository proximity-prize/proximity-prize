import ProximityPrize.SubmissionLower.H2429TerminalCount
import ProximityPrize.SubmissionLower.H2429AffineInventory
import ProximityPrize.SubmissionLower.KoalaH2429TerminalAArithmetic

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace H2429TerminalBudget
open H2429TerminalCount (rootFee)
open H2429AffineInventory (fee)
open H2429AffinePrefixBill (gradeOf)
open KoalaH2429PrefixNumbers
open KoalaH2429TerminalA (paidCap)
open KoalaTwoSectionPrice (singleCut)

abbrev cap : ℕ := 273115485059352112

private def prefixFee : FeeGrade → ℕ
  | .base => 112245003727003867
  | .sixteen => 110137247564328697
  | .seventeen => 110008766155250744

private theorem prefix_eq (e : ℕ) : fee e = prefixFee (gradeOf e) := by
  unfold fee
  cases gradeOf e <;>
    simp only [prefixFee,fullPrefix_base,fullPrefix_sixteen,fullPrefix_seventeen,low_seed_exact.1]

theorem prefix_le (e : ℕ) : fee e ≤ 116000000000000000 := by
  rw [prefix_eq]
  cases gradeOf e <;> decide

theorem compress_width {e : ℕ} (he : ¬ singleCut e) : paidCap e ≤ 448 := by
  unfold singleCut at he
  have h₁ : 7 ≤ e := by omega
  have h₂ : e ≤ 21 := by omega
  interval_cases e <;> decide

private def Checked (e v : ℕ) : Prop :=
  ∀ a : Fin (v+1), prefixFee (gradeOf e) + rootFee e a (v-a) ≤ cap

private instance (e v : ℕ) : Decidable (Checked e v) :=
  inferInstanceAs (Decidable (∀ a : Fin (v+1), prefixFee (gradeOf e) + rootFee e a (v-a) ≤ cap))

private theorem budget_of_check {e v a b : ℕ} (h : Checked e v) (hv : a+b=v) :
    fee e + rootFee e a b ≤ cap := by
  rw [prefix_eq]
  let j : Fin (v+1) := ⟨a,by omega⟩
  simpa only [j, show v-a=b by omega] using h j

private theorem pay1 : Checked 1 (paidCap 1) := by decide +kernel
private theorem pay2 : Checked 2 (paidCap 2) := by decide +kernel
private theorem pay3 : Checked 3 (paidCap 3) := by decide +kernel
private theorem pay4 : Checked 4 (paidCap 4) := by decide +kernel
private theorem pay5 : Checked 5 (paidCap 5) := by decide +kernel
private theorem pay6 : Checked 6 (paidCap 6) := by decide +kernel
private theorem pay7 : Checked 7 (paidCap 7) := by decide +kernel
private theorem pay8 : Checked 8 (paidCap 8) := by decide +kernel
private theorem pay9 : Checked 9 (paidCap 9) := by decide +kernel
private theorem pay10 : Checked 10 (paidCap 10) := by decide +kernel
private theorem pay11 : Checked 11 (paidCap 11) := by decide +kernel
private theorem pay12 : Checked 12 (paidCap 12) := by decide +kernel
private theorem pay13 : Checked 13 (paidCap 13) := by decide +kernel
private theorem pay14 : Checked 14 (paidCap 14) := by decide +kernel
private theorem pay15 : Checked 15 (paidCap 15) := by decide +kernel
private theorem pay18 : Checked 18 (paidCap 18) := by decide +kernel
private theorem pay19 : Checked 19 (paidCap 19) := by decide +kernel
private theorem pay20 : Checked 20 (paidCap 20) := by decide +kernel
private theorem pay21 : Checked 21 (paidCap 21) := by decide +kernel
private theorem pay22 : Checked 22 (paidCap 22) := by decide +kernel

theorem ordinary {e a b : ℕ} (he : 0 < e) (he' : e < 23) (h₁ : e ≠ 16) (h₂ : e ≠ 17)
    (hv : a+b = paidCap e) : fee e + rootFee e a b ≤ cap := by
  apply budget_of_check ?_ hv
  interval_cases e
  · exact pay1
  · exact pay2
  · exact pay3
  · exact pay4
  · exact pay5
  · exact pay6
  · exact pay7
  · exact pay8
  · exact pay9
  · exact pay10
  · exact pay11
  · exact pay12
  · exact pay13
  · exact pay14
  · exact pay15
  · exact (h₁ rfl).elim
  · exact (h₂ rfl).elim
  · exact pay18
  · exact pay19
  · exact pay20
  · exact pay21
  · exact pay22

private theorem hard16 : Checked 16 380 := by decide +kernel
private theorem hard17 : Checked 17 369 := by decide +kernel

theorem from_wider_bank {e a b : ℕ} (he : e=16 ∨ e=17)
    (hv : a+b = if e=16 then 380 else 369) : fee e + rootFee e a b ≤ cap := by
  rcases he with rfl | rfl
  · exact budget_of_check hard16 hv
  · exact budget_of_check hard17 hv

theorem from_split {e : ℕ} (he : e=16 ∨ e=17) :
    fee e + (if e=16 then 160676000000000000 else 161350000000000000) ≤ cap := by
  rw [prefix_eq]
  rcases he with rfl | rfl <;> decide

end H2429TerminalBudget
