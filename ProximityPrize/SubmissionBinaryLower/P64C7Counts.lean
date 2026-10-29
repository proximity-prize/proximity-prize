import ProximityPrize.SubmissionBinaryLower.P64C7Rank

/-!
# A polynomial upper bound for the bounded-pole rank

The leading terms are `s(h-mu)e + (d-q*mu)s²`. The lower-order terms are
bounded without evaluating a coefficient box or dividing a large sum.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C7Counts

open P64Found P64C7 P64C7Boxes P64C7Rank Module

lemma broad_split (s h q e : ℕ) :
    (broadBox s h q e).card =
      (∑ b ∈ Finset.range s, s * (e + q * s + 1 - q * b)) + (inputBox s h q e).card := by
  rw [broadBox, card_input, Nat.add_comm h s, Finset.sum_range_add, card_input]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  rw [Nat.mul_add]
  omega

theorem broad_budget (s h q d e : ℕ) :
    (broadBox s h q e).card ≤ (multiplesBox s q d e).card +
      (inputBox s h q e).card + s * s * d := by
  have ht : ∀ b ∈ Finset.range s, s * (e + q * s + 1 - q * b) ≤
      s * (e + q * s + 1 - (d + q * b)) + s * d := by
    intro b _
    calc _ ≤ s * ((e + q * s + 1 - (d + q * b)) + d) :=
        Nat.mul_le_mul_left s (by omega)
      _ = _ := by ring
  have hs := Finset.sum_le_sum ht
  rw [Finset.sum_add_distrib, ← card_multiples] at hs
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hs
  rw [broad_split]
  nlinarith

lemma input_upper (s h q e : ℕ) : (inputBox s h q e).card ≤ s * h * (e + 1) := by
  rw [card_input]
  calc _ ≤ ∑ _ ∈ Finset.range h, s * (e + 1) :=
        Finset.sum_le_sum fun _ _ => Nat.mul_le_mul_left s (Nat.sub_le _ _)
    _ = _ := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

lemma card_tri_sum (s : ℕ) : (tri s).card = ∑ i ∈ Finset.range s, (i + 1) := by
  have hh := Finset.sum_range_succ' (fun i : ℕ => i) s
  simp only [add_zero] at hh
  rw [card_tri, ← hh, Finset.sum_range_id, Nat.add_sub_cancel, Nat.mul_comm s (s + 1)]

lemma triangle_gap_lower (s μ : ℕ) (hμ : μ ≤ s) :
    μ * (s - μ) ≤ (tri s).card - (tri (s - μ)).card := by
  let t := s - μ
  have he : t + μ = s := Nat.sub_add_cancel hμ
  have hc : (tri s).card = (tri t).card + ∑ i ∈ Finset.range μ, (t + i + 1) := by
    conv_lhs => rw [← he, card_tri_sum, Finset.sum_range_add]
    rw [card_tri_sum]
  have hl : μ * t ≤ ∑ i ∈ Finset.range μ, (t + i + 1) := by
    calc μ * t = ∑ _ ∈ Finset.range μ, t := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => by omega
  change μ * t ≤ (tri s).card - (tri t).card
  omega

theorem lifted_lower_coarse (Λ : Finset (ℕ × ℕ)) (s μ ν q e : ℕ)
    (hμ : μ ≤ s) (hν : ν ≤ s) (hΛ : ∀ p ∈ Λ, p.2 < ν)
    (hcard : (tri s).card - (tri (s - μ)).card ≤ Λ.card) :
    μ * (s - μ) * (e + q * (s - ν)) ≤ (lifted Λ q (e + q * s)).card := by
  have hbase := lifted_lower Λ q (e + q * s) ν hΛ
  have hsize := (triangle_gap_lower s μ hμ).trans hcard
  have he : q * (s - ν) + q * ν = q * s := by rw [← Nat.mul_add, Nat.sub_add_cancel hν]
  have hm := Nat.mul_le_mul_left q (Nat.sub_le ν 1)
  have hw : e + q * (s - ν) ≤ e + q * s + 1 - q * (ν - 1) := by omega
  exact (Nat.mul_le_mul hsize hw).trans hbase

def upper (s h q d μ ν e : ℕ) : ℕ :=
  s * (h - μ) * e + (d - q * μ) * s * s +
    s * (h + q * μ * ν + q * μ * μ) + μ * μ * e

lemma upper_algebra (s h q d μ ν e r : ℕ) (hμh : μ ≤ h) (hμs : μ ≤ s)
    (hνs : ν ≤ s) (hqd : q * μ ≤ d)
    (hb : r + μ * (s - μ) * (e + q * (s - ν)) ≤ s * h * (e + 1) + s * s * d) :
    r ≤ upper s h q d μ ν e := by
  have he : (upper s h q d μ ν e : ℤ) + (μ * (s - μ) * (e + q * (s - ν)) : ℕ) =
      (s * h * (e + 1) + s * s * d : ℕ) + (q : ℤ) * μ * μ * ν := by
    unfold upper
    push_cast
    rw [Nat.cast_sub hμh, Nat.cast_sub hqd, Nat.cast_sub hμs, Nat.cast_sub hνs]
    push_cast
    ring
  have hb' : (r : ℤ) + (μ * (s - μ) * (e + q * (s - ν)) : ℕ) ≤
      (s * h * (e + 1) + s * s * d : ℕ) := by exact_mod_cast hb
  have hn : (0 : ℤ) ≤ (q : ℤ) * μ * μ * ν := by positivity
  have hr : (r : ℤ) ≤ upper s h q d μ ν e := by omega
  exact_mod_cast hr

variable {F : Type*} [Field F]

noncomputable local instance : CommRing (Polynomial F) := Polynomial.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial F)) := Polynomial.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial (Polynomial F))) := Polynomial.commRing

local notation "Tri" => Polynomial (Polynomial (Polynomial F))

/-- The leading-coefficient form of DLT, with an explicit finite remainder. -/
theorem rank_upper (S : Tri) (s μ ν h q d e : ℕ) (R'' : Polynomial (Polynomial F))
    (hS : OrdAtLeast μ S)
    (hS0 : S.map (Polynomial.constantCoeff (R := Polynomial F)) = Polynomial.X ^ ν * R'')
    (hu : R''.coeff 0 ≠ 0) (hY : S.natDegree ≤ h) (hW : WtLE 0 q 1 d S)
    (hμh : μ ≤ h) (hμs : μ ≤ s) (hνs : ν ≤ s) (hqd : q * μ ≤ d) :
    finrank F (LinearMap.range (phi S s h q e)) ≤ upper s h q d μ ν e := by
  obtain ⟨Λ, hΛ, hcard, hrank⟩ := rank_bound S s μ ν h q d e R'' hS hS0 hu hY hW
  have hΛν : ∀ p ∈ Λ, p.2 < ν := fun p hp =>
    lt_of_lt_of_le (hΛ p hp).2 (Nat.min_le_left _ _)
  have hl := lifted_lower_coarse Λ s μ ν q e hμs hνs hΛν hcard
  have hb := broad_budget s h q d e
  have hi := input_upper s h q e
  apply upper_algebra s h q d μ ν e _ hμh hμs hνs hqd
  omega

end P64C7Counts
end ProximityPrize.SubmissionBinaryLower
