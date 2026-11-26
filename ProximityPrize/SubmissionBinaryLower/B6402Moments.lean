import ProximityPrize.SubmissionBinaryLower.B6402CombinedInterpolation

/-! The exact dimension of a graded seed-coordinate space, with explicit
conditions excluding natural-subtraction truncation. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402Moments
open B6401ContactKerD B6401QuotInterp B6402SeedCoordinates B6402QuotientSpace
open B6402PrimarySystem B6402FilteredJets
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2200000

theorem widths {α : Type*} [Fintype α] (v : α → ℕ) (q T : ℕ)
    (cap : ∀ a,q*v a≤T+1) :
    Fintype.card (Indices (fun a => T+1-q*v a)) + q*(∑ a,v a) =
      Fintype.card α*(T+1) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  calc _ = ∑ _ : α, (T+1) :=
          Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (cap i))
       _ = _ := by simp

def globalSlope (w W s : ℕ) :=
  ∑ k ∈ Finset.range (s+1), ∑ r ∈ Finset.range 2,
    if k+r≤s ∧ k*(w-1)+r*w≤W then
      let rem := W-(k*(w-1)+r*w)
      let n := rem/(2*w)
      k*((n+1)*(rem/2+1)-w*n*(n+1)/2)
    else 0

/-- Group the slope exponent by its outer parity block as in PR 694. -/
theorem slope_sum (wY W s : ℕ) (hwY : 0<wY) :
    (∑ e ∈ kerDIdxFinset wY W s,e.1) = globalSlope wY W s := by
  unfold kerDIdxFinset globalSlope
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_biUnion]
    · apply Finset.sum_congr rfl; intro r _
      by_cases hkr : k + r ≤ s
      · simp only [hkr, ↓reduceIte, true_and]
        by_cases hcost : k * (wY - 1) + r * wY ≤ W
        · simp only [hcost, ↓reduceIte]
          rw [Finset.sum_biUnion]
          · trans ∑ b ∈ Finset.range ((W - (k * (wY - 1) + r * wY)) / (2 * wY) + 1),
                k * ((W - (k * (wY - 1) + r * wY) - 2 * b * wY) / 2 + 1)
            · apply Finset.sum_congr rfl; intro b _
              rw [Finset.sum_image]
              · simp [Finset.sum_const, smul_eq_mul, mul_comm]
              · intro a1 _ a2 _ h; exact (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2).2
            · rw [←Finset.mul_sum, sum_parity_block_eq wY (W-(k*(wY-1)+r*wY)) hwY]
          · intro b1 _ b2 _ hne
            dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro x hx1 hx2
            simp only [Finset.mem_image] at hx1 hx2
            rcases hx1 with ⟨_, _, rfl⟩; rcases hx2 with ⟨_, _, h⟩
            exact hne (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2).1.symm
        · simp [hcost]
      · simp [hkr]
    · intro r1 _ r2 _ hne
      dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro x hx1 hx2
      split_ifs at hx1 <;> [skip; simp at hx1; simp at hx1]
      split_ifs at hx2 <;> [skip; simp at hx2; simp at hx2]
      simp only [Finset.mem_biUnion, Finset.mem_image] at hx1 hx2
      rcases hx1 with ⟨_, _, _, _, rfl⟩; rcases hx2 with ⟨_, _, _, _, h⟩
      exact hne (Prod.mk.inj (Prod.mk.inj h).2).1.symm
  · intro k1 _ k2 _ hne
    dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro x hx1 hx2
    simp only [Finset.mem_biUnion] at hx1 hx2
    rcases hx1 with ⟨r1, _, hx1⟩; rcases hx2 with ⟨r2, _, hx2⟩
    split_ifs at hx1 <;> [skip; simp at hx1; simp at hx1]
    split_ifs at hx2 <;> [skip; simp at hx2; simp at hx2]
    simp only [Finset.mem_biUnion, Finset.mem_image] at hx1 hx2
    rcases hx1 with ⟨_, _, _, _, rfl⟩; rcases hx2 with ⟨_, _, _, _, h⟩
    exact hne (Prod.mk.inj h).1.symm

theorem global_moment (w W s : ℕ) (hw : 0<w) :
    (∑ e : KerDIdx w W s,grade e.1)=yWeightSumClosed w W s+globalSlope w W s := by
  rw [Finset.sum_coe_sort]
  simp only [grade,Finset.sum_add_distrib]
  rw [←yWeightSum_eq_closed w W s hw,←slope_sum w W s hw]
  simp only [yWeightSum,Finset.sum_add_distrib]

theorem global_grade_le (w W s : ℕ) (hw : 1<w) (e : KerDIdx w W s) :
    grade e.1 ≤ W/(w-1) := by
  rcases e with ⟨⟨k,r,b,a⟩,he⟩
  have bound := ((mem_kerDIdxFinset_iff w W s (by omega) k r b a).mp he).2.2
  apply (Nat.le_div_iff_mul_le (by omega : 0<w-1)).mpr
  change (2*b+r+k)*(w-1)≤W
  have h := Nat.mul_le_mul_left (2*b+r) (Nat.sub_le w 1)
  nlinarith only [h,bound]

theorem local_grade_le (m s : ℕ) (e : LocalBasisIdx m s) : localWeight e.1 ≤ s+2*m := by
  rcases e with ⟨⟨u,j,a,b⟩,he⟩
  have h := (mem_localBasisFinset_iff m s u j a b).mp he
  change u+j+2*b≤s+2*m; omega

theorem global_dim (w W s q T : ℕ) (hw : 1<w) (hcap : q*(W/(w-1))≤T+1) :
    Fintype.card (Slots w W s q T) + q*(∑ e : KerDIdx w W s,grade e.1) =
      varsKerDExact w W s*(T+1) := by
  have h := widths (fun e : KerDIdx w W s => grade e.1) q T
    (fun e => (Nat.mul_le_mul_left q (global_grade_le w W s hw e)).trans hcap)
  rwa [card_kerDIdx _ _ _ (by omega)] at h

theorem local_dim (m s q T : ℕ) (hc : q*(s+2*m)≤T+1) :
    Fintype.card (Seeds m s q T) + q*(∑ e : LocalBasisIdx m s,localWeight e.1) = rankKerD m s*(T+1) := by
  have h := widths (fun e : LocalBasisIdx m s => localWeight e.1) q T
    (fun e => (Nat.mul_le_mul_left q (local_grade_le m s e)).trans hc)
  rwa [card_localBasisIdx] at h

#print axioms global_dim
#print axioms local_dim
end ProximityPrize.SubmissionBinaryLower.B6402Moments
