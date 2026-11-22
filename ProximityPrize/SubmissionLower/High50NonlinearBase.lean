import ProximityPrize.SubmissionLower.UpperBranch4

set_option Elab.async false

namespace High50Nonlinear

open Finset
open K1_14_2 (Ambient)
open P1_7_4 (Mass dotQ massQ massQ_mono massQ_split weightedBill bill_bound)

/-- Subtract the mass already used at the rank exit from both available bounds. -/
def remainder (stop : ℕ) (history : ℕ → Mass) (entry used : Mass) (i : ℕ) (k : Fin 4) : ℚ :=
  if i < stop then history i k - used k else min (history i k) (entry k - used k)

theorem bill_after_exit (n stop : ℕ) (w history : ℕ → Mass) (entry : Mass)
    (live lost : ℕ → Finset (Ideal Ambient)) (E S : Finset (Ideal Ambient))
    (next : ∀ i < n, live (i+1) ⊆ live i)
    (fail : ∀ i < n, lost i ⊆ live i \ live (i+1))
    (cap : ∀ i < n, ∀ k, massQ (live i) k ≤ history i k)
    (early : ∀ i < stop, S ⊆ live i)
    (late : ∀ i ≥ stop, i < n → live i ⊆ E \ S)
    (disjoint : ∀ i < n, Disjoint (lost i) S)
    (subset : S ⊆ E) (entry_cap : ∀ k, massQ E k ≤ entry k) :
    (∑ i ∈ range n, dotQ (w i) (massQ (lost i))) ≤
      weightedBill n w (remainder stop history entry (massQ S)) := by
  let l := fun i => live i \ S
  refine bill_bound n w _ l lost ?_ ?_ ?_
  · intro i hi
    exact fun I hI => mem_sdiff.mpr ⟨next i hi (mem_sdiff.mp hI).1, (mem_sdiff.mp hI).2⟩
  · intro i hi I hI
    obtain ⟨hm,hn⟩ := mem_sdiff.mp (fail i hi hI)
    have he := Finset.disjoint_left.mp (disjoint i hi) hI
    exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hm,he⟩,fun h => hn (mem_sdiff.mp h).1⟩
  · intro i hi k
    by_cases ht : i < stop
    · rw [remainder, ite_eq_left ht]
      have h := massQ_split (early i ht) k
      change massQ (live i \ S) k ≤ _
      linarith only [h,cap i hi k]
    · rw [remainder, ite_eq_right ht]
      refine le_min (le_trans (massQ_mono sdiff_subset k) (cap i hi k)) ?_
      have h := massQ_split subset k
      have hl := massQ_mono ((sdiff_subset : l i ⊆ live i).trans (late i (by omega) hi)) k
      linarith only [h,hl,entry_cap k]

/-- The polynomial bound keeps the actual values of both degrees. -/
theorem fixed_fee_quadratic (L μ : ℚ) (hL : 0 ≤ L) (hμ : 0 ≤ μ)
    {B J : ℕ} (hJB : J ≤ B) :
    let a := μ + 2*L*(B-1 : ℕ)
    let v := min a (L*(2*J-1 : ℕ))
    ((((B-J : ℕ) : ℚ)*v + J*a).ceil.toNat + B^2 : ℕ) ≤
      (4*L*B*J + μ*J - 2*L*J^2 + B^2+1 : ℚ) := by
  dsimp only
  let a := μ + 2*L*(B-1 : ℕ)
  let v := min a (L*(2*J-1 : ℕ))
  let q : ℚ := ((B-J : ℕ) : ℚ)*v + J*a
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hv : 0 ≤ v := le_min ha (by positivity)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hj0 : (0 : ℚ) ≤ J := Nat.cast_nonneg _
  have hqceil : 0 ≤ q.ceil := by
    have h : (0 : ℚ) ≤ (q.ceil : ℚ) := hq.trans Rat.le_ceil
    exact_mod_cast h
  have hc : ((q.ceil.toNat : ℕ) : ℚ) ≤ q + 1 := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hqceil]
    exact Rat.ceil_lt.le
  have hva : v ≤ 2*L*J := by
    have hd : ((2*J-1 : ℕ) : ℚ) ≤ 2*J := by exact_mod_cast Nat.sub_le (2*J) 1
    exact (min_le_right _ _).trans (by nlinarith only [mul_le_mul_of_nonneg_left hd hL])
  have haa : a ≤ μ + 2*L*B := by
    have hd : ((B-1 : ℕ) : ℚ) ≤ B := by exact_mod_cast Nat.sub_le B 1
    dsimp [a]
    nlinarith only [mul_le_mul_of_nonneg_left hd hL]
  have hfirst : ((B-J : ℕ) : ℚ)*v ≤ ((B : ℚ)-J)*(2*L*J) := by
    rw [Nat.cast_sub hJB]
    exact mul_le_mul_of_nonneg_left hva (sub_nonneg.mpr (by exact_mod_cast hJB))
  have hsecond := mul_le_mul_of_nonneg_left haa hj0
  have hq' : q ≤ 4*L*B*J + μ*J - 2*L*J^2 := by
    dsimp [q]
    linarith only [hfirst,hsecond]
  change ((q.ceil.toNat + B^2 : ℕ) : ℚ) ≤ _
  push_cast
  linarith only [hq',hc]

def charge (L μ c b j B J : ℚ) : ℚ := c + 1 + B^2-b*B+(4*L*B+μ-j)*J-2*L*J^2

theorem charge_over_range {L μ c b j B J B₀ B₁ J₀ J₁ P₀ P₁ cap : ℚ}
    (hL : 0 ≤ L) (hB₀ : B₀ ≤ B) (hB₁ : B ≤ B₁) (hJ₀ : J₀ ≤ J) (hJ₁ : J ≤ J₁)
    (hl : (4*L*B₀+μ-j-4*L*P₀)*(if 4*L*B₀+μ-j-4*L*P₀ ≤ 0 then J₀-P₀ else J₁-P₀) ≤ 0)
    (hr : (4*L*B₁+μ-j-4*L*P₁)*(if 4*L*B₁+μ-j-4*L*P₁ ≤ 0 then J₀-P₁ else J₁-P₁) ≤ 0)
    (hc₀ : charge L μ c b j B₀ P₀ ≤ cap) (hc₁ : charge L μ c b j B₁ P₁ ≤ cap) :
    charge L μ c b j B J ≤ cap := by
  have endpoint {x P : ℚ}
      (hp : (4*L*x+μ-j-4*L*P)*(if 4*L*x+μ-j-4*L*P ≤ 0 then J₀-P else J₁-P) ≤ 0) :
      charge L μ c b j x J ≤ charge L μ c b j x P := by
    let w := 4*L*x+μ-j-4*L*P
    have hw : w*(J-P) ≤ 0 := by
      by_cases hn : w ≤ 0
      · have h := mul_le_mul_of_nonpos_left (sub_le_sub_right hJ₀ P) hn
        exact h.trans (by simpa only [w, ite_eq_left hn] using hp)
      · have h := mul_le_mul_of_nonneg_left (sub_le_sub_right hJ₁ P) (le_of_not_ge hn)
        exact h.trans (by simpa only [w, ite_eq_right hn] using hp)
    unfold charge
    dsimp [w] at hw
    nlinarith only [hw, mul_nonneg hL (sq_nonneg (J-P))]
  have h₀ := (endpoint hl).trans hc₀
  have h₁ := (endpoint hr).trans hc₁
  have hdir := mul_nonneg (sub_nonneg.mpr hB₀) (sub_nonneg.mpr hB₁)
  rcases eq_or_lt_of_le (hB₀.trans hB₁) with h | h
  · have eq : B = B₀ := le_antisymm (hB₁.trans_eq h.symm) hB₀
    rwa [eq]
  · have ha := mul_le_mul_of_nonneg_left h₀ (sub_nonneg.mpr hB₁)
    have hb := mul_le_mul_of_nonneg_left h₁ (sub_nonneg.mpr hB₀)
    have hh : (B₁-B₀)*charge L μ c b j B J ≤ (B₁-B₀)*cap := by
      have hd := mul_nonneg hdir (sub_nonneg.mpr h.le)
      unfold charge at *
      nlinarith only [ha,hb,hd]
    exact le_of_mul_le_mul_left hh (sub_pos.mpr h)


end High50Nonlinear
