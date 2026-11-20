import ProximityPrize.SubmissionLower.Front6921
import ProximityPrize.SubmissionLower.Hi6921Fast007
import ProximityPrize.SubmissionLower.Hi6921Fast023
import ProximityPrize.SubmissionLower.Hi6921Fast029
import ProximityPrize.SubmissionLower.Pack_K1_14_2_1Split
set_option Elab.async false

/- 69.25 specialization of the high-overhead proof in PR 627. -/
section High_K1_14_2_1Split
set_option autoImplicit true
set_option maxSynthPendingDepth 8

namespace H21_2_1

noncomputable section

open K21 H21 H21_2 Polynomial Finset

export _root_.K1_14_2_1 (c1)

export _root_.K1_14_2_1 (c2)

open private last_cutoffs from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Split

open private sum_rank_le from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Split

private theorem source_floor {u del} {M : AnchorModel u del} {Γ}
    {F : AnchoredFamily M Γ} {rows : Banks} (src : JetSource M F rows)
    {s : Shape} (hs : s ∈ scheduled M.overhead) (r : ℕ)
    (hw : s.B * (131071 - M.overhead.toNat) < cutoffCount M.overhead.toNat r s) :
    rawVolume M.overhead.toNat r s ≤ sourceDebit M.overhead.toNat s +
      ∑ W ∈ range (cutoffCount M.overhead.toNat r s), Module.finrank FX (rows s W) := by
  let N := cutoffCount M.overhead.toNat r s
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hw
  have hNt : N ≤ s.m * 180169 := Nat.sub_le _ _
  have hc : N - 1 + 1 = N := by omega
  have h := src.floor_bound s hs (N - 1) (by omega) (by
    intro q hq j _
    rw [hc]
    exact ((Nat.mul_le_mul_right _ hq).trans hw.le).trans (Nat.le_add_right N j))
  change triangle s.U * shapeSum s (fun q j => N + j - q * (131071 - M.overhead.toNat)) ≤
    sourceDebit M.overhead.toNat s + ∑ W ∈ range N, Module.finrank FX (rows s W)
  simpa only [hc] using h

private theorem bank_nonzero {u del} {M : AnchorModel u del} {Γ}
    {F : AnchoredFamily M Γ} {rows : Banks} (src : JetSource M F rows)
    {s : Shape} (hs : s ∈ scheduled M.overhead) (r : ℕ)
    (hw : s.B * (131071 - M.overhead.toNat) < cutoffCount M.overhead.toNat r s)
    (hd : sourceDebit M.overhead.toNat s < rawVolume M.overhead.toNat r s) :
    ∃ P ∈ rows s (cutoffCount M.overhead.toNat r s - 1), P ≠ 0 := by
  by_contra! hz
  have hf := source_floor src hs r hw
  have hsum : (∑ W ∈ range (cutoffCount M.overhead.toNat r s),
      Module.finrank FX (rows s W)) = 0 := by
    apply sum_eq_zero
    intro W hW
    have hle : W ≤ cutoffCount M.overhead.toNat r s - 1 := by
      have := mem_range.mp hW
      omega
    have hb : rows s W = ⊥ := by
      apply bot_unique
      intro P hP
      exact (Submodule.mem_bot FX).mpr
        (hz P (src.nested s hs s hs rfl rfl rfl le_rfl W _ hle hP))
    rw [hb, finrank_bot]
  omega

-- Keep the height and cutoff count symbolic when checking the degree of the power.
open private split_row_degree_from_shifts from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Split

private theorem avoids_one {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : JetSource M F rows) (power : c1) (rankBound : c2)
    (hh : 0 < M.overhead.toNat) {s : Shape} (hs : s ∈ scheduled M.overhead) (r : ℕ)
    (hw : s.B * (131071 - M.overhead.toNat) < cutoffCount M.overhead.toNat r s)
    (hd : sourceDebit M.overhead.toNat s + movingCeiling M.overhead.toNat s <
      rawVolume M.overhead.toNat r s)
    {G P : Jet} (hi : Irreducible G) (hv : 0 < G.natDegree) (hm : UsesSeed G)
    (hP : P ≠ 0) (hdiv : G ∣ P) {U : ℕ} (hp : U < p)
    (hseed : ∀ j i, ((P.coeff j).coeff i).totalDegree ≤ U) :
    ∃ Q ∈ rows s (cutoffCount M.overhead.toNat r s - 1), ¬ G ∣ Q := by
  by_contra! hcommon
  let h := M.overhead.toNat
  let N := cutoffCount h r s
  have hsum := sum_rank_le rankBound rows s h N hh (fun W P hP => src.shape s hs W P hP) (by
    intro W hW R hR hnR
    apply split_row_degree_from_shifts power h N W hh hW hi hv hm hP hdiv hp hseed hnR
    intro i a hshift
    exact hcommon _ (src.nested s hs s hs rfl rfl rfl le_rfl _ _ hshift
      (src.shift s hs W R hR i a)))
  have hf := source_floor src hs r hw
  change _ ≤ _ + ∑ W ∈ range N, Module.finrank FX (rows s W) at hf
  change _ + movingCeiling h s < _ at hd
  omega

end
end H21_2_1
end High_K1_14_2_1Split
