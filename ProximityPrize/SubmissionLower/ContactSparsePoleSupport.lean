import ProximityPrize.SubmissionLower.ContactLocalPoleBound
import ProximityPrize.SubmissionLower.ContactFactorCaps

namespace ProximityPrize.SubmissionLower.ContactSparsePoleSupport

open scoped Classical BigOperators WithZero
open ContactLocalPoleBound

noncomputable section

variable {K L σ : Type*} [Field K] [Field L] [Fintype σ]

local instance : DecidableEq K := Classical.decEq K

def exponentPoleWeight
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (x : σ → L) (d : σ →₀ ℕ) : ℤ :=
  ∑ i, (d i : ℤ) * poleOrder v (x i)

def exponentValuationWeight
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (x : σ → L) (d : σ →₀ ℕ) : ℤ :=
  ∑ i, (d i : ℤ) * (v (x i)).log

def ExponentSetDownwardClosed (E : Finset (σ →₀ ℕ)) : Prop :=
  ∀ d ∈ E, ∀ e : σ →₀ ℕ, e ≤ d → e ∈ E

def exponentSetPoleWeight
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (x : σ → L) (E : Finset (σ →₀ ℕ)) : ℤ :=
  (insert (0 : ℤ) (E.image (exponentPoleWeight v x))).max'
    ⟨0, Finset.mem_insert_self (0 : ℤ) _⟩

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

end ProximityPrize.SubmissionLower.ContactSparsePoleSupport
