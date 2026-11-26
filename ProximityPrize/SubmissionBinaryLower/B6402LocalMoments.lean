import ProximityPrize.SubmissionBinaryLower.B6402Moments
import Mathlib.Algebra.BigOperators.Intervals

/-! Closed local grade sums for the normal-form basis, including the j≥2 tail. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402LocalMoments
open B6401ContactKerD B6401QuotInterp B6402FilteredJets
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000

def tri (n : ℕ) := (Finset.range n).biUnion fun a => (Finset.range (n-a)).image fun b => (a,b)

private theorem even_sum (n : ℕ) : (∑ i ∈ Finset.range n,2*i)=n*(n-1) := by
  rw [←Finset.mul_sum,mul_comm,Finset.sum_range_id_mul_two]

private theorem cubic (n : ℕ) :
    3*(∑ a ∈ Finset.range n, ∑ b ∈ Finset.range (n-a),2*b)+n=n^3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_add_right,Nat.sub_zero,even_sum (n+1),Nat.add_sub_cancel]
    nlinarith only [ih]

theorem tri_sum (n j : ℕ) :
    (∑ p ∈ tri n,(j+2*p.2))=j*(n*(n+1)/2)+(n^3-n)/3 := by
  rw [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,show (tri n).card=n*(n+1)/2 from card_tri n,mul_comm _ j]
  congr 1
  unfold tri
  rw [Finset.sum_biUnion]
  · trans ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range (n-a),2*b
    · apply Finset.sum_congr rfl; intro a _
      rw [Finset.sum_image (by intro x _ y _ h; exact (Prod.mk.inj h).2)]
    · have hc := cubic n; omega
  · intro a _ b _ h
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    rintro u huv hv
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp huv
    obtain ⟨r,_,e⟩ := Finset.mem_image.mp hv
    exact h (Prod.mk.inj e).1.symm

def basic (q n : ℕ) := q*(n*(n+1)/2)+(n^3-n)/3
def high (q n k : ℕ) := n*(k*(q+2)+k*(k-1)/2)+k*(n*(n-1))

theorem high_sum (q n endJ : ℕ) :
    (∑ j ∈ Finset.Ico 2 endJ,∑ b ∈ Finset.range n,(q+j+2*b))=high q n (endJ-2) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul,even_sum]
  simp [high,Finset.sum_const,smul_eq_mul,←Finset.mul_sum,Finset.sum_range_id]
  <;> ring_nf
  rw [← Finset.mul_sum,Finset.sum_range_id]

def localMoment (m s : ℕ) :=
  ∑ q ∈ Finset.range (min (s+1) m),
    let n:=m-q
    basic q n + (if q+1≤s then basic (q+1) n else 0) +
      (if q+2≤s then high q n (s-q+1-2) else 0)

/-- Decompose the local basis into the two triangular parts and rectangular higher-slope parts. -/
theorem local_moment (m s : ℕ) : (∑ i : LocalBasisIdx m s,localWeight i.1)=localMoment m s := by
  rw [Finset.sum_coe_sort]
  unfold localBasisFinset localMoment
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro q hq
    have hq_lt : q < min (s + 1) m := Finset.mem_range.mp hq
    let mq := m - q
    let tri := (Finset.range mq).biUnion fun a => (Finset.range (mq - a)).image fun b => (a, b)
    let S0 := tri.image fun ab => (q, 0, ab.1, ab.2)
    let S1 := if q + 1 ≤ s then tri.image fun ab => (q, 1, ab.1, ab.2) else ∅
    let S2 := if q + 2 ≤ s then
        (Finset.Ico 2 (s - q + 1)).biUnion fun j => (Finset.range mq).image fun b => (q, j, 0, b)
      else ∅
    have hd01 : Disjoint S0 S1 := by
      rw [Finset.disjoint_left]; intro x hx0 hx1
      simp only [S0, Finset.mem_image] at hx0; rcases hx0 with ⟨_, _, rfl⟩
      dsimp [S1] at hx1; split_ifs at hx1 with h
      · simp only [Finset.mem_image] at hx1; rcases hx1 with ⟨_, _, h'⟩; simp at h'
      · simp at hx1
    have hd012 : Disjoint (S0 ∪ S1) S2 := by
      rw [Finset.disjoint_left]; intro x hx01 hx2
      dsimp [S2] at hx2; split_ifs at hx2 with h
      · simp only [Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_image] at hx2
        rcases hx2 with ⟨j, hj, _, _, rfl⟩
        rcases Finset.mem_union.mp hx01 with hx0 | hx1
        · simp only [S0, Finset.mem_image] at hx0; rcases hx0 with ⟨_, _, h'⟩
          have : j = 0 := (Prod.mk.inj (Prod.mk.inj h').2).1.symm; omega
        · dsimp [S1] at hx1; split_ifs at hx1 with h1
          · simp only [Finset.mem_image] at hx1; rcases hx1 with ⟨_, _, h'⟩
            have : j = 1 := (Prod.mk.inj (Prod.mk.inj h').2).1.symm; omega
          · simp at hx1
      · simp at hx2
    change (∑ x ∈ S0 ∪ S1 ∪ S2,localWeight x)=_
    rw [Finset.sum_union hd012,Finset.sum_union hd01]
    have small (j : ℕ) : (∑ e ∈ tri.image (fun ab => (q,j,ab.1,ab.2)),localWeight e)=basic (q+j) mq := by
      rw [Finset.sum_image]
      · exact tri_sum mq (q+j)
      · intro a _ b _ e
        exact Prod.ext (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj e).2).2).1
                       (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj e).2).2).2
    have hc0 : (∑ e ∈ S0,localWeight e)=basic q mq := by simpa [S0] using small 0
    have hc1 : (∑ e ∈ S1,localWeight e)=if q+1≤s then basic (q+1) mq else 0 := by
      dsimp [S1]; split_ifs <;> simp [small]
    have hc2 : (∑ e ∈ S2,localWeight e)=if q+2≤s then high q mq (s-q+1-2) else 0 := by
      dsimp [S2]; split_ifs with hk
      · rw [Finset.sum_biUnion]
        · trans ∑ j ∈ Finset.Ico 2 (s-q+1),∑ b ∈ Finset.range mq,(q+j+2*b)
          · apply Finset.sum_congr rfl; intro j _
            rw [Finset.sum_image (by intro a _ b _ h; exact (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2).2)]
            rfl
          · exact high_sum _ _ _
        · intro j1 _ j2 _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]; intro x hx1 hx2
          simp only [Finset.mem_image] at hx1 hx2
          rcases hx1 with ⟨_, _, rfl⟩; rcases hx2 with ⟨_, _, h'⟩
          exact hne (Prod.mk.inj (Prod.mk.inj h').2).1.symm
      · simp
    rw [hc0,hc1,hc2]
  · intro q1 _ q2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]; intro x hx1 hx2
    have hq1 : x.1 = q1 := by
      rcases Finset.mem_union.mp hx1 with h01 | h2
      · rcases Finset.mem_union.mp h01 with h0 | h1
        · simp only [Finset.mem_image] at h0; rcases h0 with ⟨_, _, rfl⟩; rfl
        · split_ifs at h1 <;> [skip; simp at h1]
          simp only [Finset.mem_image] at h1; rcases h1 with ⟨_, _, rfl⟩; rfl
      · split_ifs at h2 <;> [skip; simp at h2]
        simp only [Finset.mem_biUnion, Finset.mem_image] at h2; rcases h2 with ⟨_, _, _, _, rfl⟩; rfl
    have hq2 : x.1 = q2 := by
      rcases Finset.mem_union.mp hx2 with h01 | h2
      · rcases Finset.mem_union.mp h01 with h0 | h1
        · simp only [Finset.mem_image] at h0; rcases h0 with ⟨_, _, rfl⟩; rfl
        · split_ifs at h1 <;> [skip; simp at h1]
          simp only [Finset.mem_image] at h1; rcases h1 with ⟨_, _, rfl⟩; rfl
      · split_ifs at h2 <;> [skip; simp at h2]
        simp only [Finset.mem_biUnion, Finset.mem_image] at h2; rcases h2 with ⟨_, _, _, _, rfl⟩; rfl
    exact hne (hq1.symm.trans hq2)


#print axioms local_moment
end ProximityPrize.SubmissionBinaryLower.B6402LocalMoments
