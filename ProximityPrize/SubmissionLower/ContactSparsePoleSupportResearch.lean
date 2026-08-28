import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactLocalPoleBound
import ProximityPrize.SubmissionLower.ContactFactorCaps

/-!
# Support-sensitive local pole bound (research)

The coordinate-box theorem first replaces every monomial by the coordinatewise
maximum exponent.  This module keeps the actual support through the local
valuation step.  The remaining global theorem is then a tropical/intersection
budget for the resulting support functions across all component places.
-/

namespace ProximityPrize.SubmissionLower.ContactSparsePoleSupportResearch

open scoped Classical BigOperators WithZero
open ContactLocalPoleBound

noncomputable section

variable {K L σ : Type*} [Field K] [Field L] [Fintype σ]

local instance : DecidableEq K := Classical.decEq K

/-- The pole weight of one exponent vector at a valuation. -/
def exponentPoleWeight
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (x : σ → L) (d : σ →₀ ℕ) : ℤ :=
  ∑ i, (d i : ℤ) * poleOrder v (x i)

/-- The signed tropical weight of one exponent vector. -/
def exponentValuationWeight
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (x : σ → L) (d : σ →₀ ℕ) : ℤ :=
  ∑ i, (d i : ℤ) * (v (x i)).log

/-- The usual tropical support function, normalized by an explicit zero
term. -/
def exponentSetValuationWeight
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (x : σ → L) (E : Finset (σ →₀ ℕ)) : ℤ :=
  (insert (0 : ℤ) (E.image (exponentValuationWeight v x))).max'
    ⟨0, Finset.mem_insert_self (0 : ℤ) _⟩

/-- An anti-blocking lattice support: every coordinatewise smaller exponent
is retained.  The target interpolation and agreement polytopes have this
property. -/
def ExponentSetDownwardClosed (E : Finset (σ →₀ ℕ)) : Prop :=
  ∀ d ∈ E, ∀ e : σ →₀ ℕ, e ≤ d → e ∈ E

/-- The pole support function of a finite exponent set, with an explicit zero
term.  The zero term makes it total for the empty set and records
nonnegativity. -/
def exponentSetPoleWeight
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (x : σ → L) (E : Finset (σ →₀ ℕ)) : ℤ :=
  (insert (0 : ℤ) (E.image (exponentPoleWeight v x))).max'
    ⟨0, Finset.mem_insert_self (0 : ℤ) _⟩

/-- The exact support function of a polynomial. -/
def supportPoleWeight
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (x : σ → L) (F : MvPolynomial σ K) : ℤ :=
  exponentSetPoleWeight v x F.support

theorem supportPoleWeight_nonneg
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (x : σ → L) (F : MvPolynomial σ K) :
    0 ≤ supportPoleWeight v x F := by
  unfold supportPoleWeight exponentSetPoleWeight
  exact Finset.le_max' _ _ (Finset.mem_insert_self (0 : ℤ) _)

theorem exponentPoleWeight_le_supportPoleWeight
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (x : σ → L) (F : MvPolynomial σ K)
    (d : σ →₀ ℕ) (hd : d ∈ F.support) :
    exponentPoleWeight v x d ≤ supportPoleWeight v x F := by
  unfold supportPoleWeight exponentSetPoleWeight
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨d, hd, rfl⟩)

theorem exponentSetPoleWeight_mono
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (x : σ → L) {E D : Finset (σ →₀ ℕ)} (hED : E ⊆ D) :
    exponentSetPoleWeight v x E ≤ exponentSetPoleWeight v x D := by
  unfold exponentSetPoleWeight
  apply Finset.max'_le
  intro z hz
  obtain rfl | hz := Finset.mem_insert.mp hz
  · exact Finset.le_max' _ _ (Finset.mem_insert_self (0 : ℤ) _)
  · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hz
    apply Finset.le_max'
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨d, hED hd, rfl⟩)

theorem supportPoleWeight_le_exponentSetPoleWeight
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (x : σ → L) (F : MvPolynomial σ K) (E : Finset (σ →₀ ℕ))
    (hFE : F.support ⊆ E) :
    supportPoleWeight v x F ≤ exponentSetPoleWeight v x E :=
  exponentSetPoleWeight_mono v x hFE

theorem exponentValuationWeight_le_exponentPoleWeight
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (x : σ → L) (d : σ →₀ ℕ) :
    exponentValuationWeight v x d ≤ exponentPoleWeight v x d := by
  unfold exponentValuationWeight exponentPoleWeight poleOrder
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (le_max_right _ _)
    (Int.natCast_nonneg _)

/-- Delete precisely the coordinates whose values have negative valuation
weight. -/
def poleTruncation
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (x : σ → L) (d : σ →₀ ℕ) : σ →₀ ℕ := by
  classical
  exact d.filter (fun i ↦ 0 ≤ (v (x i)).log)

theorem poleTruncation_le
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (x : σ → L) (d : σ →₀ ℕ) : poleTruncation v x d ≤ d := by
  intro i
  simp only [poleTruncation, Finsupp.filter_apply]
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

theorem exponentValuationWeight_poleTruncation
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (x : σ → L) (d : σ →₀ ℕ) :
    exponentValuationWeight v x (poleTruncation v x d) =
      exponentPoleWeight v x d := by
  classical
  unfold exponentValuationWeight exponentPoleWeight poleOrder
  apply Finset.sum_congr rfl
  intro i _
  simp only [poleTruncation, Finsupp.filter_apply]
  by_cases h : 0 ≤ (v (x i)).log
  · rw [if_pos h, max_eq_right h]
  · have hle : (v (x i)).log ≤ 0 := le_of_not_ge h
    rw [if_neg h, max_eq_left hle]
    simp

/-- On a downward-closed exponent set, using coordinate pole parts loses
nothing: it is exactly the ordinary signed tropical support function. -/
theorem exponentSetPoleWeight_eq_valuationWeight_of_downwardClosed
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (x : σ → L) (E : Finset (σ →₀ ℕ))
    (hdown : ExponentSetDownwardClosed E) :
    exponentSetPoleWeight v x E = exponentSetValuationWeight v x E := by
  classical
  apply le_antisymm
  · unfold exponentSetPoleWeight exponentSetValuationWeight
    apply Finset.max'_le
    intro z hz
    obtain rfl | hz := Finset.mem_insert.mp hz
    · exact Finset.le_max' _ _ (Finset.mem_insert_self (0 : ℤ) _)
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hz
      let e := poleTruncation v x d
      have he : e ∈ E := hdown d hd e (poleTruncation_le v x d)
      rw [← exponentValuationWeight_poleTruncation v x d]
      apply Finset.le_max'
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨e, he, rfl⟩)
  · unfold exponentSetPoleWeight exponentSetValuationWeight
    apply Finset.max'_le
    intro z hz
    obtain rfl | hz := Finset.mem_insert.mp hz
    · exact Finset.le_max' _ _ (Finset.mem_insert_self (0 : ℤ) _)
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hz
      exact (exponentValuationWeight_le_exponentPoleWeight v x d).trans
        (Finset.le_max' _ _ (Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨d, hd, rfl⟩)))

/-- Natural weights obtained from the nonnegative coordinate pole orders. -/
def naturalPoleWeights
    (v : Valuation L (WithZero (Multiplicative ℤ))) (x : σ → L) : σ → ℕ :=
  fun i ↦ (poleOrder v (x i)).toNat

theorem naturalPoleWeights_cast
    (v : Valuation L (WithZero (Multiplicative ℤ))) (x : σ → L) (i : σ) :
    ((naturalPoleWeights v x i : ℕ) : ℤ) = poleOrder v (x i) := by
  unfold naturalPoleWeights
  exact Int.toNat_of_nonneg (by
    unfold poleOrder
    exact le_max_left _ _)

theorem exponentPoleWeight_eq_naturalWeight
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (x : σ → L) (d : σ →₀ ℕ) :
    exponentPoleWeight v x d =
      (Finsupp.weight (naturalPoleWeights v x) d : ℕ) := by
  unfold exponentPoleWeight
  rw [Finsupp.weight_apply]
  rw [Finsupp.sum_fintype d
    (fun i n ↦ n • naturalPoleWeights v x i) (fun _ ↦ zero_nsmul _)]
  simp only [nsmul_eq_mul]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [naturalPoleWeights_cast]

theorem supportPoleWeight_le_weightedTotalDegree_naturalPole
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (x : σ → L) (F : MvPolynomial σ K) :
    supportPoleWeight v x F ≤
      (MvPolynomial.weightedTotalDegree (naturalPoleWeights v x) F : ℕ) := by
  classical
  unfold supportPoleWeight exponentSetPoleWeight
  apply Finset.max'_le
  intro z hz
  obtain rfl | hz := Finset.mem_insert.mp hz
  · exact Int.natCast_nonneg _
  · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hz
    rw [exponentPoleWeight_eq_naturalWeight]
    exact_mod_cast MvPolynomial.le_weightedTotalDegree (naturalPoleWeights v x) hd

/-- One actual supported monomial is bounded by the exponential of the
support function. -/
theorem valuation_monomial_le_exp_support
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (coeff : K →+* L) (hcoeff : ∀ c : K, v (coeff c) ≤ 1)
    (x : σ → L) (F : MvPolynomial σ K)
    (d : σ →₀ ℕ) (hd : d ∈ F.support) (c : K) :
    v (MvPolynomial.eval₂Hom coeff x (MvPolynomial.monomial d c)) ≤
      WithZero.exp (supportPoleWeight v x F) := by
  classical
  apply WithZero.le_exp_of_log_le
  calc
    (v (MvPolynomial.eval₂Hom coeff x
        (MvPolynomial.monomial d c))).log ≤
        poleOrder v (MvPolynomial.eval₂Hom coeff x
          (MvPolynomial.monomial d c)) :=
      le_max_right _ _
    _ ≤ exponentPoleWeight v x d := by
      by_cases hc : c = 0
      · subst c
        simp [exponentPoleWeight, poleOrder]
        positivity
      · have hmono := poleOrder_eval_le_box v coeff hcoeff x
          (fun i ↦ d i) (MvPolynomial.monomial d c) (fun i ↦ by
            rw [MvPolynomial.degreeOf_monomial_eq d i hc])
        simpa only [exponentPoleWeight] using hmono
    _ ≤ supportPoleWeight v x F :=
      exponentPoleWeight_le_supportPoleWeight v x F d hd

/-- Multiplicative form of the exact Newton-support evaluation bound. -/
theorem valuation_eval_le_exp_support
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (coeff : K →+* L) (hcoeff : ∀ c : K, v (coeff c) ≤ 1)
    (x : σ → L) (F : MvPolynomial σ K) :
    v (MvPolynomial.eval₂Hom coeff x F) ≤
      WithZero.exp (supportPoleWeight v x F) := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum F, map_sum]
  apply v.map_sum_le
  intro d hd
  exact valuation_monomial_le_exp_support v coeff hcoeff x F d hd
    (F.coeff d)

/-- Multiplicative support bound after enlarging the actual polynomial
support to a prescribed finite exponent set. -/
theorem valuation_eval_le_exp_exponentSet
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (coeff : K →+* L) (hcoeff : ∀ c : K, v (coeff c) ≤ 1)
    (x : σ → L) (E : Finset (σ →₀ ℕ)) (F : MvPolynomial σ K)
    (hFE : F.support ⊆ E) :
    v (MvPolynomial.eval₂Hom coeff x F) ≤
      WithZero.exp (exponentSetPoleWeight v x E) := by
  exact (valuation_eval_le_exp_support v coeff hcoeff x F).trans
    ((WithZero.exp_le_exp).2
      (supportPoleWeight_le_exponentSetPoleWeight v x F E hFE))

/-- Exact local Newton-support pole bound.  Unlike the box theorem, this
retains the maximum of the actual exponent weights. -/
theorem poleOrder_eval_le_support
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (coeff : K →+* L) (hcoeff : ∀ c : K, v (coeff c) ≤ 1)
    (x : σ → L) (F : MvPolynomial σ K) :
    poleOrder v (MvPolynomial.eval₂Hom coeff x F) ≤
      supportPoleWeight v x F := by
  classical
  have heval := valuation_eval_le_exp_support v coeff hcoeff x F
  have hone : (1 : WithZero (Multiplicative ℤ)) ≤
      WithZero.exp (supportPoleWeight v x F) := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    exact supportPoleWeight_nonneg v x F
  have hmax : max 1 (v (MvPolynomial.eval₂Hom coeff x F)) ≤
      WithZero.exp (supportPoleWeight v x F) := max_le hone heval
  have hleft0 : max 1 (v (MvPolynomial.eval₂Hom coeff x F)) ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le (le_max_left _ _))
  have hlog := (WithZero.log_le_log hleft0 WithZero.exp_ne_zero).2 hmax
  rw [log_max_one, WithZero.log_exp] at hlog
  simpa only [poleOrder] using hlog

/-- Finite weighted form of the exact local support bound. -/
theorem weighted_poleOrder_eval_le_exponentSet
    {τ : Type*} (S : Finset τ) (weight : τ → ℕ)
    (v : τ → Valuation L (WithZero (Multiplicative ℤ)))
    (coeff : K →+* L)
    (hcoeff : ∀ t ∈ S, ∀ c : K, v t (coeff c) ≤ 1)
    (x : σ → L) (E : Finset (σ →₀ ℕ)) (F : MvPolynomial σ K)
    (hFE : F.support ⊆ E) :
    (∑ t ∈ S, (weight t : ℤ) *
      poleOrder (v t) (MvPolynomial.eval₂Hom coeff x F)) ≤
      ∑ t ∈ S, (weight t : ℤ) * exponentSetPoleWeight (v t) x E := by
  classical
  apply Finset.sum_le_sum
  intro t ht
  apply mul_le_mul_of_nonneg_left _ (Int.natCast_nonneg _)
  exact (poleOrder_eval_le_support (v t) coeff (hcoeff t ht) x F).trans
    (supportPoleWeight_le_exponentSetPoleWeight (v t) x F E hFE)

end

end ProximityPrize.SubmissionLower.ContactSparsePoleSupportResearch

#print axioms ProximityPrize.SubmissionLower.ContactSparsePoleSupportResearch.poleOrder_eval_le_support
