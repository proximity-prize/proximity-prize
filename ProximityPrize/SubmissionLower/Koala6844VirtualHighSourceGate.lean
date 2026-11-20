import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import ProximityPrize.SubmissionLower.Koala6844VirtualHighSource
import ProximityPrize.SubmissionLower.Koala6844VirtualHighBounds


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Polynomial
open scoped BigOperators Classical

noncomputable section

set_option autoImplicit false

variable {K : Type} [Field K]

theorem twice_finrank_globalBox (D w y b c : ℕ) (hd : y*w ≤ D) :
    2 * (Module.finrank K (globalBox K D w y b c) : ℤ) =
      (y+1)*(b+1)*(c+1)*(2*D-(y : ℤ)*w) := by
  rw [finrank_globalBox]
  have hle (j : Fin (y+1)) : w*j.val ≤ D := by
    rw [Nat.mul_comm w]
    exact (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ j.isLt)).trans hd
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_sub (hle _), Nat.cast_add, Nat.cast_one]
  simp_rw [← Finset.sum_mul]
  have s : (∑ j : Fin (y+1), (j.val : ℤ)) * 2 = (y+1)*y := by
    have h : (∑ j : Fin (y+1), j.val) * 2 = (y+1)*y := by
      have hsum : (∑ j : Fin (y+1), j.val) = ∑ j ∈ Finset.range (y+1), j :=
        Fin.sum_univ_eq_sum_range (fun j : ℕ => j) (y+1)
      rw [hsum, Finset.sum_range_id_mul_two, Nat.add_sub_cancel]
    exact_mod_cast h
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin,
    Nat.cast_add, Nat.cast_one]
  calc
    _ = ((y+1)*2*D - (w : ℤ)*((∑ j : Fin (y+1), (j.val : ℤ))*2))*(b+1)*(c+1) := by ring
    _ = _ := by rw [s]; ring

theorem sourceShape_rank_identity (shape : SourceShape)
    (hshape : shape = primary ∨ shape = roomSource ∨ shape = adaptive) :
    virtualRankSix shape.virtualOrder shape.valueCap shape.seedCap =
      6 * virtualRankPerDegree shape := by
  rcases hshape with rfl | rfl | rfl <;>
    norm_num [virtualRankSix, virtualRankPerDegree, primary, roomSource, adaptive]

theorem source_margin (shape : SourceShape)
    (hshape : shape = primary ∨ shape = roomSource ∨ shape = adaptive)
    (n d D w : ℕ) (a : ℤ)
    (hn : n ≤ 262144) (hD : (D : ℤ) = cutoff shape d)
    (hw : (w : ℤ) = normalizedDegree d a) (hfull : shape.valueCap * w ≤ D) :
    3 * twiceGap shape d a ≤
      6 * (Module.finrank K
        (globalBox K D w shape.valueCap shape.seedCap shape.seedCap) : ℤ) -
        sourceRankBudgetSix n d d shape.ordinaryOrder shape.virtualOrder shape.valueCap shape.seedCap := by
  let y := shape.valueCap
  let b := shape.seedCap
  let m := shape.ordinaryOrder
  have hr : 6 * (Module.finrank K (globalBox K D w y b b) : ℤ) =
      3*((y+1)*(b+1)*(b+1)*(2*cutoff shape d-(y : ℤ)*normalizedDegree d a)) := by
    calc
      _ = 3*(2*(Module.finrank K (globalBox K D w y b b) : ℤ)) := by ring
      _ = _ := by rw [twice_finrank_globalBox D w y b b hfull, hD, hw]
  have hm : 0 ≤ ordinaryRankSix m b := by unfold ordinaryRankSix; positivity
  have ho : (n : ℤ)*ordinaryRankSix m b ≤ 262144*ordinaryRankSix m b :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hm
  rw [hr, sourceRankBudgetSix, sourceShape_rank_identity shape hshape]
  unfold twiceGap
  change 3*((y+1)*(b+1)^2*(2*cutoff shape d-(y : ℤ)*normalizedDegree d a) -
    262144*(m : ℤ)*(m+1)*(b+1)^2 - 4*d*virtualRankPerDegree shape) ≤ _
  unfold ordinaryRankSix at ho ⊢
  nlinarith only [ho]

theorem exists_centered_source_of_arithmetic
    {I : Type} (nodes : Finset I) (x u : I → K)
    (d0 d1 : Polynomial K) (A0 A1 : Fin 2 → Polynomial K) (B0 B1 : Polynomial K)
    (hs0 : d0.Splits) (hs1 : d1.Splits) (hd0 : d0 ≠ 0) (hd1 : d1 ≠ 0)
    (hc0 : IsCoprime (A0 0) d0) (hc1 : IsCoprime (A1 0) d1)
    (hdeg : d1.natDegree = d0.natDegree) (hcard : nodes.card ≤ 262144)
    (shape : SourceShape) (hshape : shape = primary ∨ shape = roomSource ∨ shape = adaptive)
    (D w : ℕ) (a perContent : ℤ)
    (hD : (D : ℤ) = cutoff shape d0.natDegree)
    (hw : (w : ℤ) = normalizedDegree d0.natDegree a)
    (passes : Passes shape d0.natDegree a perContent) :
    ∃ F : globalBox K D w shape.valueCap shape.seedCap shape.seedCap, F ≠ 0 ∧
      (∀ i ∈ nodes, MvPolynomial.finSuccEquiv K 3 F.val ∈
        ordinaryIdeal (x i) (u i) ^ shape.ordinaryOrder) ∧
      MvPolynomial.finSuccEquiv K 3 F.val ∈
        divisorIdeal d0 (virtualEquation A0 B0 1) ^ shape.virtualOrder ∧
      MvPolynomial.finSuccEquiv K 3 F.val ∈
        divisorIdeal d1 (virtualEquation A1 B1 2) ^ shape.virtualOrder := by
  have hfull : shape.valueCap * w ≤ D := by
    have h := passes.1.le
    rw [← hD, ← hw] at h
    exact_mod_cast h
  have h := source_margin (K := K) shape hshape nodes.card d0.natDegree D w a hcard hD hw hfull
  have gate : sourceRankBudgetSix nodes.card d0.natDegree d1.natDegree shape.ordinaryOrder
      shape.virtualOrder shape.valueCap shape.seedCap <
      6 * Module.finrank K (globalBox K D w shape.valueCap shape.seedCap shape.seedCap) := by
    rw [hdeg]
    have hp := passes.2.1
    omega
  have hcaps : shape.ordinaryOrder ≤ shape.valueCap ∧ shape.virtualOrder ≤ shape.valueCap ∧
      shape.virtualOrder ≤ shape.seedCap := by
    rcases hshape with rfl | rfl | rfl <;> decide
  exact exists_centered_source_of_split_gate nodes x u d0 d1 A0 A1 B0 B1
    hs0 hs1 hd0 hd1 hc0 hc1 D w _ _ _ _ hcaps.1 hcaps.2.1 hcaps.2.2 gate

theorem exists_centered_sourceSpace_of_arithmetic
    {I : Type} (nodes : Finset I) (x u : I → K)
    (d0 d1 : Polynomial K) (A0 A1 : Fin 2 → Polynomial K) (B0 B1 : Polynomial K)
    (hs0 : d0.Splits) (hs1 : d1.Splits) (hd0 : d0 ≠ 0) (hd1 : d1 ≠ 0)
    (hc0 : IsCoprime (A0 0) d0) (hc1 : IsCoprime (A1 0) d1)
    (hdeg : d1.natDegree = d0.natDegree) (hcard : nodes.card ≤ 262144)
    (shape : SourceShape) (hshape : shape = primary ∨ shape = roomSource ∨ shape = adaptive)
    (D w : ℕ) (a perContent : ℤ)
    (hD : (D : ℤ) = cutoff shape d0.natDegree)
    (hw : (w : ℤ) = normalizedDegree d0.natDegree a)
    (passes : Passes shape d0.natDegree a perContent) :
    ∃ S : Submodule K (globalBox K D w shape.valueCap shape.seedCap shape.seedCap),
      perContent * d0.natDegree ≤ (Module.finrank K S : ℤ) ∧
      ∀ F ∈ S,
      (∀ i ∈ nodes, MvPolynomial.finSuccEquiv K 3 F.val ∈
        ordinaryIdeal (x i) (u i) ^ shape.ordinaryOrder) ∧
      MvPolynomial.finSuccEquiv K 3 F.val ∈
        divisorIdeal d0 (virtualEquation A0 B0 1) ^ shape.virtualOrder ∧
      MvPolynomial.finSuccEquiv K 3 F.val ∈
        divisorIdeal d1 (virtualEquation A1 B1 2) ^ shape.virtualOrder := by
  have hfull : shape.valueCap * w ≤ D := by
    have h := passes.1.le
    rw [← hD, ← hw] at h
    exact_mod_cast h
  have h := source_margin (K := K) shape hshape nodes.card d0.natDegree D w a hcard hD hw hfull
  have hcaps : shape.ordinaryOrder ≤ shape.valueCap ∧ shape.virtualOrder ≤ shape.valueCap ∧
      shape.virtualOrder ≤ shape.seedCap := by
    rcases hshape with rfl | rfl | rfl <;> decide
  obtain ⟨S, hS, hcontact⟩ := exists_centered_sourceSpace_of_split nodes x u d0 d1 A0 A1 B0 B1
    hs0 hs1 hd0 hd1 hc0 hc1 D w _ _ _ _ hcaps.1 hcaps.2.1 hcaps.2.2
  rw [hdeg] at hS
  refine ⟨S, ?_, hcontact⟩
  have passesMargin := passes.2.2
  linarith only [h, hS, passesMargin]

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
