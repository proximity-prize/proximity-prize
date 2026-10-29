import ProximityPrize.SubmissionBinaryLower.P64C7Slice

/-!
# Integer choices for the two single-line bounds

Using `d` in place of `d-q*mu` absorbs rounding and includes the zero-defect
case. Each side costs at most `5*C*h^2*d` after clearing `2*N` denominators.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C7Parameters

def negativeParameter (h d μ : ℕ) : ℕ := 4 * h * d / μ + 1

def positiveParameter (h q d μ : ℕ) : ℕ := 2 * h * d / (h - μ) + 2 * q * h + 1

lemma negative_above (h d μ : ℕ) (hμ : 0 < μ) :
    4 * h * d < μ * negativeParameter h d μ := by
  exact Nat.lt_mul_div_succ _ hμ

lemma positive_above (h q d μ : ℕ) (hμ : μ < h) :
    2 * h * d < (h - μ) * positiveParameter h q d μ := by
  have hh := Nat.lt_mul_div_succ (2 * h * d) (Nat.sub_pos_of_lt hμ)
  exact hh.trans_le (Nat.mul_le_mul_left _ (by unfold positiveParameter; omega))

lemma positive_weight (h q d μ : ℕ) : q * (2 * h) < positiveParameter h q d μ := by
  calc q * (2 * h) = 2 * q * h := by ring
    _ ≤ 2 * h * d / (h - μ) + 2 * q * h := Nat.le_add_left _ _
    _ < positiveParameter h q d μ := Nat.lt_succ_self _

theorem negative_leading (h q d μ : ℕ) (hh : 0 < h) (hμ : 0 < μ) (hμh : μ ≤ h) :
    P64C7Scale.quadraticCost h q d μ (negativeParameter h d μ) (2 * h) <
      h * (2 * h - μ) * negativeParameter h d μ := by
  have he := negative_above h d μ hμ
  have hm := Nat.sub_add_cancel hμh
  have hu : 2 * h - μ + μ = 2 * h := Nat.sub_add_cancel (by omega)
  have hq : d - q * μ ≤ d := Nat.sub_le _ _
  have hdiff : P64C7Scale.quadraticCost h q d μ (negativeParameter h d μ) (2 * h) +
      h * μ * negativeParameter h d μ =
      h * (2 * h - μ) * negativeParameter h d μ + 4 * h * h * (d - q * μ) := by
    unfold P64C7Scale.quadraticCost
    nlinarith only [congrArg (fun t : ℕ => 2 * h * t * negativeParameter h d μ) hm,
      congrArg (fun t : ℕ => h * t * negativeParameter h d μ) hu]
  have heh := Nat.mul_lt_mul_of_pos_left he hh
  have hqh := Nat.mul_le_mul_left (4 * h * h) hq
  nlinarith

theorem positive_leading (h q d μ : ℕ) (hh : 0 < h) (hμ : μ < h) :
    P64C6Scale.quadraticCost q d (positiveParameter h q d μ) (2 * h) μ <
      6 * (h : ℤ) * (h + μ) * positiveParameter h q d μ := by
  have he : 2 * (h : ℤ) * d < ((h : ℤ) - μ) * positiveParameter h q d μ := by
    have hn := positive_above h q d μ hμ
    zify [hμ.le] at hn
    exact hn
  have hm := mul_lt_mul_of_pos_left he (show 0 < 6 * (h : ℤ) by positivity)
  unfold P64C6Scale.quadraticCost
  push_cast
  have hp : (0 : ℤ) ≤ 12 * h ^ 2 * q * μ := by positivity
  nlinarith

theorem negative_numerical (h d μ : ℕ) (hμh : μ ≤ h) (hd : 1 ≤ d) :
    μ * negativeParameter h d μ ≤ 5 * h * d := by
  have he := Nat.mul_div_le (4 * h * d) μ
  have hm := Nat.mul_le_mul_left h hd
  unfold negativeParameter
  rw [Nat.mul_add, Nat.mul_one]
  nlinarith only [he, hm, hμh]

theorem positive_numerical (h q d μ : ℕ) (hqh : q * h ≤ d) (hd : 1 ≤ d) :
    (h - μ) * positiveParameter h q d μ ≤ 5 * h * d := by
  have he := Nat.mul_div_le (2 * h * d) (h - μ)
  have ht : h - μ ≤ h := Nat.sub_le _ _
  have hm := Nat.mul_le_mul ht hqh
  have hd' := Nat.mul_le_mul_left h hd
  unfold positiveParameter
  nlinarith

end P64C7Parameters
end ProximityPrize.SubmissionBinaryLower
