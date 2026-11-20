/- Released under the Apache License, Version 2.0. -/
import ProximityPrize.SubmissionLower.Koala6844ActiveGerm
import Mathlib.RingTheory.EuclideanDomain

namespace ProximityPrize.SubmissionLower.NormalizedContent
open Polynomial Koala6844Normalization
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {K I : Type} [Field K] [DecidableEq K] [DecidableEq I]
variable {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K} {w A errors excess : ℕ}

local instance : GCDMonoid (Polynomial K) := EuclideanDomain.gcdMonoid _

def overlap (data : CenteredVirtualData x nodes σ w A errors excess) : ℕ :=
  (GCDMonoid.gcd data.d1 (data.d0.map σ.toRingHom)).natDegree

theorem overlap_le_content (data : CenteredVirtualData x nodes σ w A errors excess) :
    overlap data ≤ data.d0.natDegree :=
  (Polynomial.natDegree_le_of_dvd (gcd_dvd_left _ _) data.d1_ne).trans_eq data.degree_content

/-- Cancel the part of the second content outside its overlap with the conjugate first content.
It vanishes at none of the retained evaluation points. -/
theorem reduce (data : CenteredVirtualData x nodes σ w A errors excess) :
    ∃ (words : K → Polynomial K) (received : I → K),
      Set.InjOn words (↑data.seeds : Set K) ∧
      (∀ g ∈ data.seeds, (words g).natDegree ≤ w + overlap data - affineDegree data.A0) ∧
      (∀ g ∈ data.seeds, A ≤ (nodes.filter fun i => (words g).eval (x i) = received i).card) := by
  classical
  let b := data.d0.map σ.toRingHom
  let G := GCDMonoid.gcd data.d1 b
  let H := data.d1 / G
  let J := b / G
  have hG : G ≠ 0 := gcd_ne_zero_of_left data.d1_ne
  have hH : G * H = data.d1 :=
    EuclideanDomain.mul_div_cancel' hG (gcd_dvd_left _ _)
  have hJ : G * J = b :=
    EuclideanDomain.mul_div_cancel' hG (gcd_dvd_right _ _)
  have hn : H ≠ 0 := by
    intro h
    exact data.d1_ne (by rw [← hH, h, mul_zero])
  have hc : IsCoprime H J := isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hG
  have divides (g : K) (hg : g ∈ data.seeds) : H ∣ data.normalized g := by
    apply hc.dvd_of_dvd_mul_left
    refine ⟨(data.normalized g).map σ.toRingHom, ?_⟩
    apply mul_left_cancel₀ hG
    rw [← mul_assoc, hJ, ← mul_assoc, hH]
    exact (data.homogeneous g hg).symm
  let words (g : K) := data.normalized g / H
  have product (g : K) (hg : g ∈ data.seeds) : H * words g = data.normalized g :=
    EuclideanDomain.mul_div_cancel' hn (divides g hg)
  have hdegree : overlap data + H.natDegree = data.d0.natDegree := by
    change G.natDegree + H.natDegree = data.d0.natDegree
    rw [← natDegree_mul hG hn, hH, data.degree_content]
  refine ⟨words, fun i => data.fixedWord i / H.eval (x i), ?_, ?_, ?_⟩
  · intro g hg k hk eqn
    apply Koala6844ActiveGerm.normalized_injOn data hg hk
    rw [← product g hg, ← product k hk, eqn]
  · intro g hg
    by_cases hz : words g = 0
    · simp [hz]
    · have hprod := congrArg Polynomial.natDegree (product g hg)
      rw [natDegree_mul hn hz] at hprod
      have hbound := data.normalized_degree g hg
      omega
  · intro g hg
    apply (data.normalized_agreements g hg).trans
    apply Finset.card_le_card
    intro i hi
    obtain ⟨hmem, hvalue⟩ := Finset.mem_filter.mp hi
    have hunit : H.eval (x i) ≠ 0 := by
      intro he
      have hbad := data.content1_off_domain i hmem
      exact hbad (by rw [← hH, eval_mul, he, mul_zero])
    refine Finset.mem_filter.mpr ⟨hmem, (eq_div_iff hunit).mpr ?_⟩
    rw [mul_comm, ← eval_mul, product g hg]
    exact hvalue

#print axioms reduce
end
end ProximityPrize.SubmissionLower.NormalizedContent
