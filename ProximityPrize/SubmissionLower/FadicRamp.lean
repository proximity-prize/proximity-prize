import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
set_option Elab.async false

namespace FadicRamp

open Finset
open scoped BigOperators

def degree (theta q : ℕ) : ℕ := (theta - 26*q) / 25

private theorem degree_bounds {theta q : ℕ} (h : 26*q ≤ theta) :
    26*q + 25*degree theta q ≤ theta ∧ theta < 26*q + 25*degree theta q + 25 := by
  unfold degree
  omega

private theorem residue {theta q d : ℕ}
    (hl : 26*q + 25*d ≤ theta) (hu : theta < 26*q + 25*d + 25) :
    (theta+d) % 26 < 25 := by omega

/-- The descending degree sequence omits exactly one residue class modulo 26. -/
theorem sum_ramp (theta L N : ℕ) (hn : L < N) (ht : 26*(N-1) ≤ theta)
    (f : ℕ → ℕ) :
    ∑ q ∈ Ico L N, f (degree theta q) =
      ∑ d ∈ (Icc (degree theta (N-1)) (degree theta L)).filter
        (fun d => (theta+d) % 26 ≠ 25), f d := by
  obtain ⟨hl₀,hu₀⟩ := degree_bounds (q := L) (show 26*L ≤ theta by omega)
  obtain ⟨hl₁,hu₁⟩ := degree_bounds ht
  apply Finset.sum_bij (fun q _ => degree theta q)
  · intro q hq
    obtain ⟨hlo,hhi⟩ := mem_Ico.mp hq
    obtain ⟨hl,hu⟩ := degree_bounds (q := q) (show 26*q ≤ theta by omega)
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_,?_⟩, (ne_of_lt (residue hl hu))⟩ <;> omega
  · intro q hq r hr he
    have hq' := mem_Ico.mp hq
    have hr' := mem_Ico.mp hr
    obtain ⟨hql,hqu⟩ := degree_bounds (q := q) (show 26*q ≤ theta by omega)
    obtain ⟨hrl,hru⟩ := degree_bounds (q := r) (show 26*r ≤ theta by omega)
    omega
  · intro d hd
    obtain ⟨hr,hm⟩ := mem_filter.mp hd
    obtain ⟨hlo,hhi⟩ := mem_Icc.mp hr
    let q := (theta - 25*d) / 26
    have hq : 26*q ≤ theta - 25*d ∧ theta - 25*d < 26*q+26 := by
      dsimp only [q]
      omega
    refine ⟨q,mem_Ico.mpr ⟨?_,?_⟩,?_⟩
    · omega
    · omega
    · unfold degree
      omega
  · intro q hq
    rfl

/-- A direct interval sum and one strided sum replace the filter. -/
theorem sum_remove_residue (theta a b : ℕ) (f : ℕ → ℕ) :
    (∑ d ∈ (Icc a b).filter (fun d => (theta+d) % 26 ≠ 25), f d) =
      (∑ d ∈ Icc a b, f d) -
        (∑ k ∈ range (if a + (25-(theta+a)%26) ≤ b
                             then (b-(a+(25-(theta+a)%26)))/26+1 else 0),
          f (a+(25-(theta+a)%26)+26*k)) := by
  let first := a+(25-(theta+a)%26)
  have hfirst : (theta+first) % 26 = 25 := by dsimp only [first]; omega
  have hstride :
      ∑ k ∈ range (if first ≤ b then (b-first)/26+1 else 0), f (first+26*k) =
        ∑ d ∈ (Icc a b).filter (fun d => (theta+d) % 26 = 25), f d := by
    apply Finset.sum_bij (fun k _ => first+26*k)
    · intro k hk
      have hk' := mem_range.mp hk
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_,?_⟩, ?_⟩
      · dsimp only [first]; omega
      · split at hk' <;> omega
      · omega
    · intro k _ l _ h
      omega
    · intro d hd
      obtain ⟨hr,hrmod⟩ := mem_filter.mp hd
      obtain ⟨hlo,hhi⟩ := mem_Icc.mp hr
      have hfd : first ≤ d := by dsimp only [first] at *; omega
      refine ⟨(d-first)/26,mem_range.mpr ?_,?_⟩
      · rw [ite_eq_left (hfd.trans hhi)]; omega
      · omega
    · intro k _
      rfl
  change _ = _ - ∑ k ∈ range (if first ≤ b then (b-first)/26+1 else 0), f (first+26*k)
  rw [hstride]
  have h := Finset.sum_filter_add_sum_filter_not (Icc a b)
    (fun d => (theta+d)%26 = 25) f
  exact Nat.eq_sub_of_add_eq' h

def admissible (B theta : ℕ) : ℕ := min (B+1) (theta/26+1)

def rise (B J theta : ℕ) : ℕ := min (admissible B theta) (min J (theta/51+1))

def flatEnd (B J theta : ℕ) : ℕ :=
  if 51*J ≤ theta then min (admissible B theta) ((theta-25*J)/26+1) else rise B J theta

def term (theta J : ℕ) (f : ℕ → ℕ) (q : ℕ) : ℕ :=
  if 26*q ≤ theta then f (min J (min q (degree theta q))) else 0

theorem sum_windows (B J theta : ℕ) (f : ℕ → ℕ) :
    let N := admissible B theta
    let R := rise B J theta
    let F := flatEnd B J theta
    (∑ q ∈ range (B+1), term theta J f q) =
      (∑ q ∈ range R, f q) + (F-R)*f J +
        (∑ q ∈ Ico F N, f (degree theta q)) := by
  dsimp only
  let N := admissible B theta
  let R := rise B J theta
  let F := flatEnd B J theta
  let s := term theta J f
  have hN : N ≤ B+1 := min_le_left _ _
  have hR : R ≤ N := min_le_left _ _
  have hNlarge : N ≤ theta/26+1 := min_le_right _ _
  have hRsmall : R ≤ min J (theta/51+1) := min_le_right _ _
  have hNR : 51*J ≤ theta → R = min N J := by
    intro h
    unfold R rise
    rw [min_eq_left (by omega : J ≤ theta/51+1)]
  have hNF : 51*J ≤ theta → F = min N ((theta-25*J)/26+1) := by
    intro h
    unfold F flatEnd
    exact ite_eq_left h
  have hRF : ¬ 51*J ≤ theta → F = R := by
    intro h
    unfold F flatEnd
    exact ite_eq_right h
  have hF : R ≤ F ∧ F ≤ N := by
    by_cases h : 51*J ≤ theta
    · rw [hNF h,hNR h]
      exact ⟨min_le_min_left _ (by omega), min_le_left _ _⟩
    · rw [hRF h]
      exact ⟨le_rfl,hR⟩
  have tail : ∑ q ∈ Ico N (B+1), s q = 0 := by
    apply sum_eq_zero
    intro q hq
    have hq' := mem_Ico.mp hq
    have hqa : theta/26+1 ≤ q := by
      have hm : min (B+1) (theta/26+1) ≤ q := hq'.1
      exact (min_le_iff.mp hm).resolve_left (by omega)
    exact ite_eq_right (show ¬ 26*q ≤ theta by omega)
  have rising : ∑ q ∈ range R, s q = ∑ q ∈ range R, f q := by
    apply sum_congr rfl
    intro q hq
    have hq' := mem_range.mp hq
    have hqN : q < N := hq'.trans_le hR
    have hqJ := hq'.trans_le (hRsmall.trans (min_le_left _ _))
    have hqT := hq'.trans_le (hRsmall.trans (min_le_right _ _))
    have hd : q ≤ degree theta q := by unfold degree; omega
    simp only [s,term,ite_eq_left (show 26*q ≤ theta by omega),
      min_eq_left hd,min_eq_right hqJ.le]
  have flat : ∑ q ∈ Ico R F, s q = (F-R)*f J := by
    calc
      _ = ∑ q ∈ Ico R F, f J := by
        apply sum_congr rfl
        intro q hq
        obtain ⟨hqR,hqF⟩ := mem_Ico.mp hq
        have ht : 51*J ≤ theta := by by_contra! h; have := hRF (by omega); omega
        have hqN : q < N := hqF.trans_le hF.2
        have hj : J ≤ q := by
          rw [hNR ht] at hqR
          exact (min_le_iff.mp hqR).resolve_left (by omega)
        have hlim : q < (theta-25*J)/26+1 := hqF.trans_le (by rw [hNF ht]; exact min_le_right _ _)
        have hd : J ≤ degree theta q := by unfold degree; omega
        simp only [s,term,ite_eq_left (show 26*q ≤ theta by omega),min_eq_left (le_min hj hd)]
      _ = _ := by
        rw [sum_const,Nat.card_Ico]
        exact nsmul_eq_mul _ _
  have falling : ∑ q ∈ Ico F N, s q = ∑ q ∈ Ico F N, f (degree theta q) := by
    apply sum_congr rfl
    intro q hq
    obtain ⟨hqF,hqN⟩ := mem_Ico.mp hq
    have hqr := degree_bounds (q := q) (show 26*q ≤ theta by omega)
    have hd : degree theta q ≤ q ∧ degree theta q ≤ J := by
      by_cases ht : 51*J ≤ theta
      · rw [hNF ht] at hqF
        have hd := (min_le_iff.mp hqF).resolve_left (by omega)
        omega
      · rw [hRF ht] at hqF
        have hm : min N (min J (theta/51+1)) ≤ q := hqF
        have hs := (min_le_iff.mp ((min_le_iff.mp hm).resolve_left (by omega)))
        rcases hs with hs | hs <;> omega
    simp only [s,term,ite_eq_left (show 26*q ≤ theta by omega),
      min_eq_right hd.1,min_eq_right hd.2]
  change (∑ q ∈ range (B+1), s q) = _
  rw [← sum_range_add_sum_Ico s hN,tail,add_zero,
      ← sum_range_add_sum_Ico s hF.2,
      ← sum_range_add_sum_Ico s hF.1,rising,flat,falling]

end FadicRamp
