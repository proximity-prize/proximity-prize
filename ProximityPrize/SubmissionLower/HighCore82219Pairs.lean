import ProximityPrize.SubmissionLower.HighCore82219Source
import ProximityPrize.SubmissionLower.HighCore82219StageReceipts

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

section
namespace HighCore82219
noncomputable section
open FrontCore82219 (AnchorModel AnchoredFamily)
open P1 (p)
open K1_14 (Shape Banks Jet FX triangle shapeSum seedHasse)
open K1_14_2 (UsesSeed)
open K1_14_2_1 (exists_layered)
open Polynomial Finset
open private fixed_of_no_seed from ProximityPrize.SubmissionLower.Fast051
open private eligible cutoff_finrank_le cutoff_total from ProximityPrize.SubmissionLower.UpperBranch2
private theorem source_floor {b u del} {M : AnchorModel u del} {Γ}
    {F : AnchoredFamily M Γ} {rows : Banks} (src : Source b M F rows)
    {t : Bank} (ht : Listed b t) (r : ℕ)
    (hw : WidthGuard M.overhead.toNat r t.shape) :
    gain M.overhead.toNat r t.shape 0 ≤ debit M.overhead.toNat t +
      ∑ W ∈ range (cutoffCount M.overhead.toNat r t.shape),
        Module.finrank FX (rows t.shape W) := by
  let h := M.overhead.toNat
  let N := cutoffCount h r t.shape
  change t.shape.B * (131071-h) < N at hw
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hw
  have hNt : N ≤ t.shape.m * agreement := Nat.sub_le _ _
  have hc : N - 1 + 1 = N := by omega
  have hf := src.floor_bound t ht (N - 1) (by omega) (by
    intro q hq j _
    rw [hc]
    exact ((Nat.mul_le_mul_right _ hq).trans hw.le).trans (Nat.le_add_right N j))
  unfold gain rawWidth
  simpa only [hc, zero_mul, Nat.sub_zero] using hf
private theorem bank_nonzero {b u del} {M : AnchorModel u del} {Γ}
    {F : AnchoredFamily M Γ} {rows : Banks} (src : Source b M F rows)
    {t : Bank} (ht : Listed b t) (r : ℕ)
    (hw : WidthGuard M.overhead.toNat r t.shape)
    (hd : debit M.overhead.toNat t < gain M.overhead.toNat r t.shape 0) :
    ∃ P ∈ rows t.shape (cutoffCount M.overhead.toNat r t.shape - 1), P ≠ 0 := by
  by_contra! hz
  let N := cutoffCount M.overhead.toNat r t.shape
  have hf := source_floor src ht r hw
  have hsum : (∑ W ∈ range N, Module.finrank FX (rows t.shape W)) = 0 := by
    apply sum_eq_zero
    intro W hW
    have hle : W ≤ N - 1 := by have := mem_range.mp hW; omega
    have hb : rows t.shape W = ⊥ := by
      apply bot_unique
      intro P hP
      exact (Submodule.mem_bot FX).mpr
        (hz P (src.nested t ht t ht rfl rfl rfl le_rfl W _ hle hP))
    rw [hb, finrank_bot]
  change _ ≤ _ + ∑ W ∈ range N, Module.finrank FX (rows t.shape W) at hf
  omega
private theorem gain_le_raw (h r : ℕ) (s : Shape) :
    gain h r s 1 ≤ gain h r s 0 := by
  unfold gain shapeSum
  simp only [zero_mul, Nat.sub_zero]
  exact Nat.mul_le_mul_left _ (sum_le_sum fun _ _ => sum_le_sum fun _ _ => Nat.sub_le _ _)
private theorem order_from_shifts (h N W : ℕ) (hh : 0 < h) (hW : W < N)
    {G P R : Jet} (hi : Irreducible G) (hv : 0 < G.natDegree)
    (hm : UsesSeed G) (hP : P ≠ 0) (hdiv : G ∣ P) {U : ℕ} (hp : U < p)
    (hseed : ∀ j i, ((P.coeff j).coeff i).totalDegree ≤ U) (hnR : R ≠ 0)
    (commonShift : ∀ (i : Fin 2) a, W + 2*h*a ≤ N-1 → G ∣ seedHasse i a R) :
    N ≤ W + 2*h*R.natDegree := by
  let e := 1 + (N - 1 - W) / (2*h)
  have hpower : G ^ e ∣ R :=
    K1_14_2_1_1.proof G P R U e hi hv hm hP hdiv hp hseed (by
      intro i a ha
      have hle : a ≤ (N - 1 - W) / (2*h) := by dsimp [e] at ha; omega
      have ht := (Nat.le_div_iff_mul_le (by omega : 0 < 2*h)).mp hle
      rw [Nat.mul_comm a] at ht
      exact commonShift i a (by omega))
  have hdegree := Polynomial.natDegree_le_of_dvd hpower hnR
  rw [Polynomial.natDegree_pow] at hdegree
  have he : e ≤ R.natDegree := (Nat.le_mul_of_pos_right e hv).trans hdegree
  have hdiv' : (N - 1 - W) / (2*h) < R.natDegree := by dsimp [e] at he; omega
  have ht := (Nat.div_lt_iff_lt_mul (by omega : 0 < 2*h)).mp hdiv'
  rw [Nat.mul_comm R.natDegree] at ht
  omega
private theorem moving_rank_bound (rows : Banks) (s : Shape) (h r : ℕ)
    (hk : 1 ≤ 131071-h)
    (hcaps : ∀ W, ∀ P ∈ rows s W, K1_14_3.RowCaps P s)
    (hlead : K1_14_3.LeadingFilter h rows s)
    (horder : ∀ W < cutoffCount h r s, ∀ P ∈ rows s W, P ≠ 0 →
      cutoffCount h r s ≤ W + 2*h*P.natDegree) :
    (∑ W ∈ range (cutoffCount h r s), Module.finrank FX (rows s W)) + gain h r s 1 ≤
      gain h r s 0 := by
  let N := cutoffCount h r s
  have hsum : (∑ W ∈ range N, Module.finrank FX (rows s W)) ≤
      triangle s.U * (∑ W ∈ range N, shapeSum s (fun q j =>
        if eligible h N W q j then 1 else 0)) := by
    rw [mul_sum]
    exact sum_le_sum (fun W hW =>
      cutoff_finrank_le s h N W _ (hcaps W) (hlead W) (horder W (mem_range.mp hW)))
  have heq := congrArg (triangle s.U * ·) (cutoff_total s h N hk)
  rw [Nat.mul_add] at heq
  unfold gain rawWidth
  simp only [one_mul, zero_mul, Nat.sub_zero]
  exact (Nat.add_le_add_right hsum _).trans_eq heq
private theorem avoids_one {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : Source b M F rows) (hh : 0 < M.overhead.toNat)
    (hk : 1 ≤ 131071-M.overhead.toNat) {t : Bank} (ht : Listed b t) (r : ℕ)
    (hw : WidthGuard M.overhead.toNat r t.shape)
    (hd : debit M.overhead.toNat t < gain M.overhead.toNat r t.shape 1)
    {G P : Jet} (hi : Irreducible G) (hv : 0 < G.natDegree) (hm : UsesSeed G)
    (hP : P ≠ 0) (hdiv : G ∣ P) {U : ℕ} (hp : U < p)
    (hseed : ∀ j i, ((P.coeff j).coeff i).totalDegree ≤ U) :
    ∃ Q ∈ rows t.shape (cutoffCount M.overhead.toNat r t.shape - 1), ¬ G ∣ Q := by
  by_contra! hcommon
  let h := M.overhead.toNat
  let N := cutoffCount h r t.shape
  have hsum := moving_rank_bound rows t.shape h r hk (src.shape t ht) (src.leading t ht) (by
    intro W hW R hR hnR
    apply order_from_shifts h N W hh hW hi hv hm hP hdiv hp hseed hnR
    intro i a hshift
    exact hcommon _ (src.nested t ht t ht rfl rfl rfl le_rfl _ _ hshift
      (src.shift t ht W R hR i a)))
  have hf := source_floor src ht r hw
  dsimp only [h] at hsum
  omega
theorem pair_of_tests {b u del} {M : AnchorModel u del} {Γ}
    {F : AnchoredFamily M Γ} {rows : Banks} (src : Source b M F rows)
    (hh : 0 < M.overhead.toNat) (hk : 1 ≤ 131071 - M.overhead.toNat)
    {s : Stage} (hs : s ∈ stages b)
    (hwidth : WidthGuard M.overhead.toNat s.reserve s.free.shape)
    (hfree : debit M.overhead.toNat s.free < gain M.overhead.toNat s.reserve s.free.shape 0)
    (hchar : s.free.shape.U < p)
    (hwidth' : WidthGuard M.overhead.toNat s.reserve s.moving.shape)
    (hmoving : debit M.overhead.toNat s.moving < gain M.overhead.toNat s.reserve s.moving.shape 1) :
    Nonempty (BufferedPair M.overhead.toNat rows s) := by
  have hsFree : Listed b s.free := Or.inr (Or.inl ⟨s, hs, Or.inl rfl⟩)
  have hsMoving : Listed b s.moving := Or.inr (Or.inl ⟨s, hs, Or.inr rfl⟩)
  obtain ⟨P, hPm, hP⟩ := bank_nonzero src hsFree s.reserve hwidth hfree
  have hnonzero := bank_nonzero src hsMoving s.reserve hwidth'
    (hmoving.trans_le (gain_le_raw _ _ _))
  have hseed (j y : ℕ) : ((P.coeff j).coeff y).totalDegree ≤ s.free.shape.U := by
    by_cases hz : (P.coeff j).coeff y = 0
    · simp [hz]
    · exact (src.shape s.free hsFree _ P hPm j y hz).2.2
  obtain ⟨Q, hQm, hQ, havoid⟩ := exists_layered P hP _ hnonzero (fun G hi hdiv hv hm =>
    avoids_one src hh hk hsMoving s.reserve hwidth' hmoving hi hv hm hP hdiv hchar hseed)
  have hcut (a : Shape) : buffered M.overhead.toNat s.reserve a =
      cutoffCount M.overhead.toNat s.reserve a - 1 := by
    unfold buffered fullCutoff cutoffCount
    omega
  exact ⟨⟨P, Q, hP, hQ, (hcut _).symm ▸ hPm, (hcut _).symm ▸ hQm,
    fun G hi hdiv hdiv' hv => fixed_of_no_seed G (fun hm => havoid G hi hdiv hv hm hdiv')⟩⟩
end
end HighCore82219
end


namespace HighCore82219
open FrontCore82219 (AnchorModel AnchoredFamily)
open K1_14 (Banks)

theorem buffered_pairs (b : Band) {u del} (M : AnchorModel u del) {Γ}
    (F : AnchoredFamily M Γ) (hb : InBand b M.overhead) {rows : Banks} (src : Source b M F rows) :
    Nonempty (Pairs b M.overhead.toNat rows) := by
  classical
  obtain ⟨hl,hu⟩ := window_nat hb
  obtain ⟨h0,hmax⟩ := height_guards b
  have hh : 0 < M.overhead.toNat := h0.trans_le hl
  have hbnd : M.overhead.toNat ≤ heightCap := hu.trans hmax
  have hu' : M.overhead.toNat ≤ 131070 := hbnd.trans (by decide)
  refine ⟨fun s hs => Classical.choice ?_⟩
  obtain ⟨⟨wf,sf,cf⟩,⟨wm,sm,cm⟩⟩ :=
    HighCore82219Stages.stage_bounds b hs hl (hu'.trans (by decide))
  exact pair_of_tests src hh (by omega) hs wf sf cf wm sm

#print axioms buffered_pairs
end HighCore82219
