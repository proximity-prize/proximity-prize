import ProximityPrize.SubmissionLower.PrimaryTaperRankData
import ProximityPrize.SubmissionLower.Wide50EulerPrimaryBlock

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Wide50EulerPrimary
open K1_13 (Geom)
open K1_13_2 K1_13_2_3 TaperBudget
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
open private fees saved_by_fees fees_le_baseline sumRange_fin sumRange_eq
  from ProximityPrize.SubmissionLower.PrimaryTaperBudget
open private baseline_budget_on sum_add_pointwise_eq from ProximityPrize.SubmissionLower.Fast022
open private sum_checked from ProximityPrize.SubmissionLower.PrimaryTaperRankData
open private sum_embed_le from ProximityPrize.SubmissionLower.Fast068

abbrev localRank : ℕ := 343902284076178

private def inWindow (i : BlockIndex) : Prop :=
  3514 ≤ i.1.val ∧ i.1.val < 3594 ∧ 77 ≤ i.2.val ∧ i.2.val < 121

private instance (i : BlockIndex) : Decidable (inWindow i) := by
  unfold inWindow
  infer_instance

private def windowPower (t j : ℕ) : Powers :=
  ⟨819 - 2*t - 4*(12+j), 275 - 2*t - 9*j/2, 0⟩

private def alternate (i : BlockIndex) : ℕ :=
  TaperNormalize.bound (cap i.1.val) i
    (windowPower (i.1.val - 3514) (i.2.val - 77)).expand

private def gain (i : BlockIndex) : ℕ :=
  if inWindow i then
    min (baseline i) (TaperNormalize.bound (cap i.1.val) i (power i)) - alternate i
  else 0

private def window : Fin 80 × Fin 44 ↪ BlockIndex where
  toFun x := (⟨3514 + x.1.val, by omega⟩, ⟨77 + x.2.val, by omega⟩)
  inj' := by
    intro x y h
    apply Prod.ext <;> apply Fin.ext
    · have h₁ := congrArg (fun i : BlockIndex => i.1.val) h
      change 3514 + x.1.val = 3514 + y.1.val at h₁
      omega
    · have h₂ := congrArg (fun i : BlockIndex => i.2.val) h
      change 77 + x.2.val = 77 + y.2.val at h₂
      omega

private def numericCell (t j : ℕ) : ℕ :=
  if ht : t < 80 then if hj : j < 44 then
    let i := window (⟨t,ht⟩,⟨j,hj⟩)
    let k := cap i.1.val
    let v := valuePower k i.1.val i.2.val
    let p := windowPower t j
    min (twoFactorBound 1650 i 0 0) (twoFactorBound k i v 0) -
      twoFactorBound k i p.value p.top
  else 0 else 0

private theorem cell_eq (t : Fin 80) (j : Fin 44) :
    numericCell t.val j.val = gain (window (t,j)) := by
  have hw : inWindow (window (t,j)) := by
    unfold inWindow
    change 3514 ≤ 3514 + t.val ∧ 3514 + t.val < 3594 ∧
      77 ≤ 77 + j.val ∧ 77 + j.val < 121
    omega
  have ht : (window (t,j)).1.val - 3514 = t.val := by
    change 3514 + t.val - 3514 = t.val
    omega
  have hj : (window (t,j)).2.val - 77 = j.val := by
    change 77 + j.val - 77 = j.val
    omega
  have hzero : (Powers.expand ⟨0,0,0⟩) = (fun _ : Fin 11 => 0) := by
    funext j
    fin_cases j <;> rfl
  simp only [numericCell, t.isLt, j.isLt, dite_true, gain, hw, ite_true, alternate,
    ht, hj, twoFactorBound_eq, power, windowPower, hzero, old_bound_eq, baseline]

private def row (t : ℕ) : ℕ := sumRange (numericCell t) 44

private def rowTotals : Fin 80 → ℕ :=
  ![21821534, 21505240, 21188447, 20871239, 20553702, 20235923, 19917990, 19599992,
    19282022, 18964176, 18646550, 18329243, 18012358, 17695996, 17380258, 17065248,
    16751070, 16437828, 16125626, 15814571, 15504770, 15196328, 14889354, 14583957,
    14280245, 13978328, 13678317, 13380324, 13084459, 12790835, 12499567, 12210767,
    11924550, 11641032, 11360329, 11082557, 10807833, 10536277, 10268006, 10003139,
    9741798, 9484103, 9229933, 8979410, 8732478, 8489230, 8249607, 8013640,
    7781387, 7552787, 7327955, 7106769, 6889341, 6675606, 6465643, 6259386,
    6056853, 5858091, 5663030, 5471770, 5284184, 5100368, 4920250, 4743895,
    4571228, 4402257, 4237015, 4075425, 3917572, 3763322, 3612758, 3465798,
    3322495, 3182765, 3046604, 2914034, 2784968, 2659478, 2537423, 2418871]

set_option maxHeartbeats 0 in
private theorem row_checked (t : Fin 80) : row t.val = rowTotals t := by
  fin_cases t <;> decide +kernel

private theorem window_gain : 854889514 ≤ ∑ i : BlockIndex, gain i := by
  have h : (∑ x : Fin 80 × Fin 44, gain (window x)) = 854889514 := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    calc
      _ = ∑ t : Fin 80, row t.val := by
        apply Finset.sum_congr rfl
        intro t _
        rw [row, sumRange_fin]
        apply Finset.sum_congr rfl
        intro j _
        exact (cell_eq t j).symm
      _ = ∑ t : Fin 80, rowTotals t := Finset.sum_congr rfl fun t _ => row_checked t
      _ = 854889514 := by decide
  exact h ▸ sum_embed_le window gain

private def charged (p₁ p₂ p₃ : BlockIndex → Powers) (i : BlockIndex) : ℕ :=
  if inWindow i then min (fees p₁ p₂ p₃ i) (alternate i)
  else fees p₁ p₂ p₃ i

private theorem charged_add_gain (p₁ p₂ p₃ : BlockIndex → Powers) (i : BlockIndex) :
    charged p₁ p₂ p₃ i + gain i = fees p₁ p₂ p₃ i := by
  by_cases hi : inWindow i
  · have hg : ¬ i.1.val < 3514 := by unfold inWindow at hi; omega
    simp only [charged, gain, ite_eq_left hi, fees, ite_eq_right hg]
    omega
  · simp [charged, gain, hi]

/-- The alternate residual powers reduce the compact primary rank at every site. -/
theorem node_rank (x y : Geom) :
    Module.finrank Geom
      (LinearMap.range ((localConstraintAt 3000 x y).domRestrict
        (TaperNormalize.space cap))) ≤ localRank := by
  classical
  obtain ⟨p₁, hp₁⟩ := K1_13_2_3_4.proof
  obtain ⟨p₂, hp₂⟩ := K1_13_2_3_5.proof
  obtain ⟨p₃, hp₃⟩ := K1_13_2_3_6.proof
  have h₂ := K1_13_2_2_2.proof
  have h₃ := K1_13_2_2_3.proof
  have h₄ := K1_13_2_2_4.proof
  have h₅ := K1_13_2_2_5.proof
  have hBlock := K1_13_2_2.of_children K1_13_2_2_1.proof h₂ h₃ h₄ h₅
  have hold (i : BlockIndex) :
      Module.finrank Geom (LinearMap.range (TaperNormalize.originBlock (cap i.1.val) i)) ≤
        fees p₁ p₂ p₃ i := by
    have ho := Submodule.finrank_mono (TaperNormalize.range_le_old (cap i.1.val) i)
    unfold fees
    split
    · exact ho.trans (hBlock i _)
    · exact le_min (ho.trans (hBlock i _))
        (TaperNormalize.origin_block_rank_bound _ h₂ h₃ h₄ h₅ i _)
  have hr := TaperNormalize.rank_le_of_blocks cap_antitone x y (charged p₁ p₂ p₃) (fun i => by
    unfold charged
    split
    · exact le_min (hold i) (TaperNormalize.origin_block_rank_bound _ h₂ h₃ h₄ h₅ i _)
    · exact hold i)
  have ht := baseline_budget_on (Finset.univ : Finset BlockIndex) baseline_low
    K1_13_2_3_1.proof K1_13_2_3_2.proof K1_13_2_3_3.proof
  have hsumGain : (∑ i, charged p₁ p₂ p₃ i) + (∑ i, gain i) = ∑ i, fees p₁ p₂ p₃ i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => charged_add_gain p₁ p₂ p₃ i
  have htail : 396610034658 ≤ ∑ i : BlockIndex, tailSaving i := by
    have h := fastSavings_le (J := 600) (by decide)
    rw [← sumChunk_eq_fastSavings, sum_checked] at h
    exact h
  have hsave := saved_by_fees p₁ p₂ p₃
  have hsum := sum_add_pointwise_eq Finset.univ (fees p₁ p₂ p₃)
    (fun i => baseline i - fees p₁ p₂ p₃ i) baseline
    (fun i _ => Nat.add_sub_of_le (fees_le_baseline p₁ p₂ p₃ i))
  have hgain := window_gain
  unfold localRank
  omega

#print axioms node_rank
end Wide50EulerPrimary
