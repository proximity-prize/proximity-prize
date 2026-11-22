import ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic
set_option autoImplicit true
section
set_option maxSynthPendingDepth 8
namespace K1_14_2_1
noncomputable section
open K1 K1_14 K1_14_2 Polynomial Finset
def c1 : Prop :=
  ∀ (G P R : Jet) (U e : ℕ),
    Irreducible G → 0 < G.natDegree → UsesSeed G →
    P ≠ 0 → G ∣ P → U < p →
    (∀ j i, ((P.coeff j).coeff i).totalDegree ≤ U) →
    (∀ (i : Fin 2) (r : ℕ), r < e → G ∣ seedHasse i r R) →
    G ^ e ∣ R
def c2 : Prop :=
  ∀ (s : Shape) (V : Submodule FX Jet) (k : ℕ),
    (∀ P ∈ V, RowCaps s P) →
    (∀ P ∈ V, P ≠ 0 → k ≤ P.natDegree) →
    Module.finrank FX V ≤ triangle s.U * shapeSum s (fun _ j => if k ≤ j then 1 else 0)
private theorem last_cutoffs (d N j : ℕ) (hd : 0 < d) :
    (∑ W ∈ range N, if 1 + (N - 1 - W) / d ≤ j then 1 else 0) ≤ d * j := by
  have hfilter : (range N).filter (fun W => 1 + (N - 1 - W) / d ≤ j) =
      Ico (N - d * j) N := by
    ext W
    simp only [mem_filter, mem_range, mem_Ico]
    by_cases hW : W < N
    · have ht : 1 + (N - 1 - W) / d ≤ j ↔ ¬ j ≤ (N - 1 - W) / d := by omega
      rw [ht, Nat.le_div_iff_mul_le hd, Nat.mul_comm j d]
      omega
    · simp [hW]
  rw [← card_filter, hfilter, Nat.card_Ico]
  omega
private theorem sum_rank_le (rankBound : c2) (rows : Banks) (s : Shape) (h N : ℕ)
    (hh : 0 < h) (hcaps : ∀ W, ∀ P ∈ rows s W, RowCaps s P)
    (hpower : ∀ W < N, ∀ P ∈ rows s W, P ≠ 0 →
      1 + (N - 1 - W) / (2 * h) ≤ P.natDegree) :
    (∑ W ∈ range N, Module.finrank FX (rows s W)) ≤ movingCeiling h s := by
  calc
    _ ≤ ∑ W ∈ range N, triangle s.U * shapeSum s
          (fun _ j => if 1 + (N - 1 - W) / (2 * h) ≤ j then 1 else 0) := by
      exact sum_le_sum (fun W hW => rankBound s (rows s W) _ (hcaps W) (hpower W (mem_range.mp hW)))
    _ = triangle s.U * shapeSum s
          (fun _ j => ∑ W ∈ range N, if 1 + (N - 1 - W) / (2 * h) ≤ j then 1 else 0) := by
      unfold shapeSum
      rw [← mul_sum, sum_comm]
      congr 1
      exact sum_congr rfl (fun _ _ => sum_comm)
    _ ≤ movingCeiling h s := by
      unfold movingCeiling shapeSum
      exact Nat.mul_le_mul_left _ (sum_le_sum fun _ _ =>
        sum_le_sum fun j _ => last_cutoffs (2 * h) N j (by omega))
private theorem source_floor {u del} {M : AnchorModel u del} {Γ}
    {F : AnchoredFamily M Γ} {rows : Banks} (src : JetSource M F rows)
    {s : Shape} (hs : s ∈ scheduled M.overhead) (r : ℕ)
    (hw : s.B * (131071 - M.overhead.toNat) < cutoffCount M.overhead.toNat r s) :
    rawVolume M.overhead.toNat r s ≤ sourceDebit M.overhead.toNat s +
      ∑ W ∈ range (cutoffCount M.overhead.toNat r s), Module.finrank FX (rows s W) := by
  let N := cutoffCount M.overhead.toNat r s
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hw
  have hNt : N ≤ s.m * 180265 := Nat.sub_le _ _
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
private theorem split_row_degree_from_shifts (power : c1) (h N W : ℕ) (hh : 0 < h)
    (hW : W < N) {G P R : Jet} (hi : Irreducible G) (hv : 0 < G.natDegree)
    (hm : UsesSeed G) (hP : P ≠ 0) (hdiv : G ∣ P) {U : ℕ} (hp : U < p)
    (hseed : ∀ j i, ((P.coeff j).coeff i).totalDegree ≤ U) (hnR : R ≠ 0)
    (commonShift : ∀ (i : Fin 2) a, W + 2 * h * a ≤ N - 1 → G ∣ seedHasse i a R) :
    1 + (N - 1 - W) / (2 * h) ≤ R.natDegree := by
  let e := 1 + (N - 1 - W) / (2 * h)
  have hpower : G ^ e ∣ R := power G P R U e hi hv hm hP hdiv hp hseed (by
    intro i a ha
    have hle : a ≤ (N - 1 - W) / (2 * h) := by dsimp [e] at ha; omega
    have ht := (Nat.le_div_iff_mul_le (by omega : 0 < 2 * h)).mp hle
    have hshift : W + 2 * h * a ≤ N - 1 := by rw [Nat.mul_comm a] at ht; omega
    exact commonShift i a hshift)
  have hdegree := Polynomial.natDegree_le_of_dvd hpower hnR
  rw [Polynomial.natDegree_pow] at hdegree
  exact (Nat.le_mul_of_pos_right e hv).trans hdegree
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
end K1_14_2_1
end
