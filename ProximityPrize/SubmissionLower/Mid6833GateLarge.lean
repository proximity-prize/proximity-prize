/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Koala6831OrdinaryIncidence
import ProximityPrize.SubmissionLower.Koala6831QuotientBoxes
import Mathlib.Tactic
namespace Frontier6969.LargeTable
open ProximityPrize.SubmissionLower.Koala6831OrdinaryIncidence
open ProximityPrize.SubmissionLower.Koala6831Quotient
set_option maxRecDepth 65000
set_option maxHeartbeats 5000000

def profiles : Fin 11 → ℕ × ℕ × ℕ := ![(9,12,85),(14,19,82),(9,12,33),(6,8,22),(4,5,19),(4,5,14),(4,5,13),(3,4,17),(3,4,15),(3,4,14),(3,4,14)]
def cutoff (c : Fin 11) := if c.val < 1 then 16223 else 12168

theorem dimension (c : Fin 11) (δ : ℕ) (larger : cutoff c ≤ δ) :
    let (m,y,L) := profiles c
    ordinaryColumns (m*179740-131071-δ) 131071 (y-1) (L-(c.val+2)) +
      262144*(ordinaryColumns m 1 (m-1) L - ordinaryColumns (m-1) 1 (m-2) (L-(c.val+2))) <
      ordinaryColumns (m*179740) 131071 y L := by
  have h : let (m,y,L) := profiles c
           ordinaryColumns (m*179740-131071-cutoff c) 131071 (y-1) (L-(c.val+2)) +
            262144*(ordinaryColumns m 1 (m-1) L - ordinaryColumns (m-1) 1 (m-2) (L-(c.val+2))) <
            ordinaryColumns (m*179740) 131071 y L := by
    fin_cases c <;> decide +kernel
  cases he : profiles c with
  | mk m caps =>
    obtain ⟨y,L⟩ := caps
    simp only [he] at h ⊢
    exact lt_of_le_of_lt (Nat.add_le_add_right (ordinaryColumns_mono_cutoff _ _ _ (Nat.sub_le_sub_left larger _)) _) h

theorem price (c : Fin 11) (δ : ℕ) (h : cutoff c ≤ δ) :
    let (_,y,L) := profiles c
    ordinaryPrice 2130706433 262144 131071 179740 82404 y (L+(c.val+1)*y)
      + 10*2130706433*(262144+1) + (33735-δ+1)*6*(2130706433+1) ≤ 103791747798885716 := by
  have htable : let (_,y,L) := profiles c
                ordinaryPrice 2130706433 262144 131071 179740 82404 y (L+(c.val+1)*y)
                  + 10*2130706433*(262144+1) + (33735-cutoff c+1)*6*(2130706433+1) ≤ 103791747798885716 := by
    fin_cases c <;> decide +kernel
  cases he : profiles c with
  | mk m caps =>
    obtain ⟨y,L⟩ := caps
    simp only [he] at htable ⊢
    apply le_trans _ htable
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le_sub_left h _) _))) _

theorem shape (c : Fin 11) :
    let (m,y,L) := profiles c
    2≤m ∧ 1≤y ∧ c.val+2≤L ∧ y≤19 ∧ L+(c.val+1)*y≤185 ∧ y≤L+(c.val+1)*y := by
  fin_cases c <;> decide +kernel

#print axioms price
#print axioms dimension
#print axioms shape
end Frontier6969.LargeTable
