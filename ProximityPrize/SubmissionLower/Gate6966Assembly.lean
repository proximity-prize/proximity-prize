import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import ProximityPrize.SubmissionLower.Gate6966Tally
set_option Elab.async false

-- merged module Gate6966Combine
section Merged_Gate6966Combine

set_option autoImplicit false

namespace Gate6966Combine

open Finset

theorem class_zero (r e m g : ℕ) (he : 1 ≤ e) (hO : r ≤ m + g) :
    ((r : ℚ)) ^ 2 ≤ (g : ℚ) ^ 2 + (m : ℚ) * g + (r : ℚ) * e * m := by
  have he' : (1 : ℚ) ≤ e := by exact_mod_cast he
  have hO' : (r : ℚ) ≤ m + g := by exact_mod_cast hO
  have hm : (0 : ℚ) ≤ m := Nat.cast_nonneg _
  have hg : (0 : ℚ) ≤ g := Nat.cast_nonneg _
  have hr : (0 : ℚ) ≤ r := Nat.cast_nonneg _
  by_cases hmr : (r : ℚ) ≤ m
  · nlinarith [mul_nonneg hr (mul_nonneg hm (sub_nonneg.mpr he')), mul_nonneg hg hg, mul_nonneg hm hg]
  · push_neg at hmr
    have h1 : (r : ℚ) - m ≤ g := by linarith
    nlinarith [mul_nonneg hr (mul_nonneg hm (sub_nonneg.mpr he')), mul_nonneg hg hg, mul_nonneg hm hg,
      mul_nonneg (sub_nonneg.mpr h1) (add_nonneg hm hg)]

variable {ι : Type*}

theorem combine (s : Finset ι) (μ e m g : ι → ℕ) (ρ c v : ℚ)
    (Tgg Tmg Tem Teg Tee : ℚ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hv : 0 ≤ v)
    (hclass : ∀ i ∈ s, ρ ^ 2 ≤ (1 - c) * ((g i : ℚ) * g i) + (m i : ℚ) * g i + ρ * ((e i : ℚ) * m i) +
      c * ρ * ((e i : ℚ) * g i) + v * ρ ^ 2 * ((e i : ℚ) * ((e i : ℚ) - 1)))
    (hρ : 0 ≤ ρ)
    (hgg : ∑ i ∈ s, (μ i : ℚ) * ((g i : ℚ) * g i) ≤ Tgg)
    (hmg : ∑ i ∈ s, (μ i : ℚ) * ((m i : ℚ) * g i) ≤ Tmg)
    (hem : ∑ i ∈ s, (μ i : ℚ) * ((e i : ℚ) * m i) ≤ Tem)
    (heg : ∑ i ∈ s, (μ i : ℚ) * ((e i : ℚ) * g i) ≤ Teg)
    (hee : ∑ i ∈ s, (μ i : ℚ) * ((e i : ℚ) * ((e i : ℚ) - 1)) ≤ Tee) :
    ρ ^ 2 * (∑ i ∈ s, (μ i : ℚ)) ≤
      (1 - c) * Tgg + Tmg + ρ * Tem + c * ρ * Teg + v * ρ ^ 2 * Tee := by
  have hsum : ∑ i ∈ s, (μ i : ℚ) * ρ ^ 2 ≤
      ∑ i ∈ s, (μ i : ℚ) * ((1 - c) * ((g i : ℚ) * g i) + (m i : ℚ) * g i + ρ * ((e i : ℚ) * m i) +
        c * ρ * ((e i : ℚ) * g i) + v * ρ ^ 2 * ((e i : ℚ) * ((e i : ℚ) - 1))) :=
    Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hclass i hi) (Nat.cast_nonneg _)
  have hexp : ∑ i ∈ s, (μ i : ℚ) * ((1 - c) * ((g i : ℚ) * g i) + (m i : ℚ) * g i +
        ρ * ((e i : ℚ) * m i) + c * ρ * ((e i : ℚ) * g i) +
        v * ρ ^ 2 * ((e i : ℚ) * ((e i : ℚ) - 1))) =
      (1 - c) * ∑ i ∈ s, (μ i : ℚ) * ((g i : ℚ) * g i) + ∑ i ∈ s, (μ i : ℚ) * ((m i : ℚ) * g i) +
        ρ * ∑ i ∈ s, (μ i : ℚ) * ((e i : ℚ) * m i) + c * ρ * ∑ i ∈ s, (μ i : ℚ) * ((e i : ℚ) * g i) +
        v * ρ ^ 2 * ∑ i ∈ s, (μ i : ℚ) * ((e i : ℚ) * ((e i : ℚ) - 1)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hl : ∑ i ∈ s, (μ i : ℚ) * ρ ^ 2 = ρ ^ 2 * ∑ i ∈ s, (μ i : ℚ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hl, hexp] at hsum
  have h1 : (1 - c) * ∑ i ∈ s, (μ i : ℚ) * ((g i : ℚ) * g i) ≤ (1 - c) * Tgg :=
    mul_le_mul_of_nonneg_left hgg (by linarith)
  have h3 : ρ * ∑ i ∈ s, (μ i : ℚ) * ((e i : ℚ) * m i) ≤ ρ * Tem := mul_le_mul_of_nonneg_left hem hρ
  have h4 : c * ρ * ∑ i ∈ s, (μ i : ℚ) * ((e i : ℚ) * g i) ≤ c * ρ * Teg :=
    mul_le_mul_of_nonneg_left heg (mul_nonneg hc0 hρ)
  have h5 : v * ρ ^ 2 * ∑ i ∈ s, (μ i : ℚ) * ((e i : ℚ) * ((e i : ℚ) - 1)) ≤ v * ρ ^ 2 * Tee :=
    mul_le_mul_of_nonneg_left hee (mul_nonneg hv (sq_nonneg ρ))
  linarith

theorem combine_zero (s : Finset ι) (μ e m g : ι → ℕ) (r : ℕ) (Tgg Tmg Tem : ℚ)
    (he : ∀ i ∈ s, 1 ≤ e i) (hO : ∀ i ∈ s, r ≤ m i + g i)
    (hgg : ∑ i ∈ s, (μ i : ℚ) * ((g i : ℚ) * g i) ≤ Tgg)
    (hmg : ∑ i ∈ s, (μ i : ℚ) * ((m i : ℚ) * g i) ≤ Tmg)
    (hem : ∑ i ∈ s, (μ i : ℚ) * ((e i : ℚ) * m i) ≤ Tem) :
    (r : ℚ) ^ 2 * (∑ i ∈ s, (μ i : ℚ)) ≤ Tgg + Tmg + r * Tem := by
  have h := combine s μ e m g (r : ℚ) 0 0 Tgg Tmg Tem
    (∑ i ∈ s, (μ i : ℚ) * ((e i : ℚ) * g i)) (∑ i ∈ s, (μ i : ℚ) * ((e i : ℚ) * ((e i : ℚ) - 1)))
    le_rfl zero_le_one le_rfl
    (fun i hi => by
      have := class_zero r (e i) (m i) (g i) (he i hi) (hO i hi)
      nlinarith [this])
    (Nat.cast_nonneg _) hgg hmg hem le_rfl le_rfl
  simpa using h

end Gate6966Combine

end Merged_Gate6966Combine

-- merged module Gate6966Assembly
section Merged_Gate6966Assembly

set_option autoImplicit false

namespace Gate6966Assembly

open Finset

theorem sum_by_surface {β ι : Type*} [DecidableEq ι] (F : Finset β) (surf : β → ι) (c : β → ℕ)
    (w : ι → ℚ) :
    ∑ b ∈ F, w (surf b) * (c b : ℚ) =
      ∑ P ∈ F.image surf, w P * ((∑ b ∈ F.filter (fun b => surf b = P), c b : ℕ) : ℚ) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := surf) (fun b hb => Finset.mem_image_of_mem surf hb)]
  apply Finset.sum_congr rfl
  intro P _
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [(Finset.mem_filter.mp hb).2]

theorem conv {β ι : Type*} [DecidableEq ι] (F : Finset β) (surf : β → ι) (c : β → ℕ) (w : ι → ℚ) {T : ℚ}
    (h : ∑ b ∈ F, w (surf b) * (c b : ℚ) ≤ T) :
    ∑ P ∈ F.image surf, ((∑ b ∈ F.filter (fun b => surf b = P), c b : ℕ) : ℚ) * w P ≤ T := by
  rw [sum_by_surface] at h
  simpa only [mul_comm] using h

theorem combine_branches {β ι : Type*} [DecidableEq ι] (F : Finset β) (surf : β → ι) (c : β → ℕ)
    (e m g : ι → ℕ) (ρ cc v : ℚ) (Tgg Tmg Tem Teg Tee : ℚ) (hc0 : 0 ≤ cc) (hc1 : cc ≤ 1) (hv : 0 ≤ v)
    (hρ : 0 ≤ ρ)
    (hclass : ∀ b ∈ F, ρ ^ 2 ≤ (1 - cc) * ((g (surf b) : ℚ) * g (surf b)) + (m (surf b) : ℚ) * g (surf b) +
      ρ * ((e (surf b) : ℚ) * m (surf b)) + cc * ρ * ((e (surf b) : ℚ) * g (surf b)) +
      v * ρ ^ 2 * ((e (surf b) : ℚ) * ((e (surf b) : ℚ) - 1)))
    (hgg : ∑ b ∈ F, ((g (surf b) : ℚ) * g (surf b)) * (c b : ℚ) ≤ Tgg)
    (hmg : ∑ b ∈ F, ((m (surf b) : ℚ) * g (surf b)) * (c b : ℚ) ≤ Tmg)
    (hem : ∑ b ∈ F, ((e (surf b) : ℚ) * m (surf b)) * (c b : ℚ) ≤ Tem)
    (heg : ∑ b ∈ F, ((e (surf b) : ℚ) * g (surf b)) * (c b : ℚ) ≤ Teg)
    (hee : ∑ b ∈ F, ((e (surf b) : ℚ) * ((e (surf b) : ℚ) - 1)) * (c b : ℚ) ≤ Tee) :
    ρ ^ 2 * (∑ b ∈ F, (c b : ℚ)) ≤
      (1 - cc) * Tgg + Tmg + ρ * Tem + cc * ρ * Teg + v * ρ ^ 2 * Tee := by
  classical
  let S := F.image surf
  let μ : ι → ℕ := fun P => ∑ b ∈ F.filter (fun b => surf b = P), c b
  have hsum1 : ∑ b ∈ F, (c b : ℚ) = ∑ P ∈ S, (μ P : ℚ) := by
    have := sum_by_surface F surf c (fun _ => 1)
    simp only [one_mul] at this
    rw [this]
  have h := Gate6966Combine.combine S μ e m g ρ cc v Tgg Tmg Tem Teg Tee hc0 hc1 hv
    (fun P hP => by
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hP
      exact hclass b hb)
    hρ
    (conv F surf c (fun P => (g P : ℚ) * g P) hgg)
    (conv F surf c (fun P => (m P : ℚ) * g P) hmg)
    (conv F surf c (fun P => (e P : ℚ) * m P) hem)
    (conv F surf c (fun P => (e P : ℚ) * g P) heg)
    (conv F surf c (fun P => (e P : ℚ) * ((e P : ℚ) - 1)) hee)
  rw [hsum1]
  exact h

end Gate6966Assembly

end Merged_Gate6966Assembly
