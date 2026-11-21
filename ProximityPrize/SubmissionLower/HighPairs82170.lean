import ProximityPrize.SubmissionLower.HighFamilyBase82170
import ProximityPrize.SubmissionLower.GoldBranch7N2
set_option Elab.async false
set_option autoImplicit true
section
namespace HighFamily82170_2
open Front82170 (agreement)
open K1_14 (Shape triangle shapeSum)
def cutoffCount (h r : ℕ) (s : Shape) : ℕ :=
  s.m * agreement - 2 * h * r
def rawWidth (h r : ℕ) (s : Shape) (q j : ℕ) : ℕ :=
  cutoffCount h r s + j - q * (131071 - h)
def WidthGuard (h r : ℕ) (s : Shape) : Prop :=
  s.B * (131071 - h) < cutoffCount h r s
def gain (h r : ℕ) (s : Shape) (mode : ℕ) : ℕ :=
  triangle s.U * shapeSum s (fun q j => rawWidth h r s q j - mode * (2 * h * j))
end HighFamily82170_2
end
section
namespace HighFamily82170_2
noncomputable section
open Front82170 (HighBand AnchorModel AnchoredFamily agreement p)
open HighFamily82170 (Bank Stage InBand BufferedPair Source Listed stages buffered fullCutoff debit)
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
end HighFamily82170_2
end

section
namespace HighFamily82170_2
open Front82170 (HighBand agreement p)
open HighFamily82170 (Stage stages window_nat terminal_guards)
open K1_14 (Shape)
private theorem agreement_cast : (agreement : ℤ) = 179974 := rfl
private def origin (s : Shape) (r : ℕ) (h : ℤ) : ℤ := (s.m : ℤ)*agreement - 2*h*r
def worstWidth (s : Shape) (r : ℕ) (h : ℤ) : ℤ :=
  origin s r h - (131071-h)*s.B
private theorem width_of_pos (s : Shape) (r h : ℕ) (hh : h ≤ 131071)
    (hw : 0 < worstWidth s r h) : WidthGuard h r s := by
  have hn : 0 ≤ (131071-(h : ℤ))*(s.B : ℤ) := by
    exact mul_nonneg (sub_nonneg.mpr (Int.ofNat_le.mpr hh)) (Int.natCast_nonneg _)
  unfold worstWidth origin at hw
  have hbuf : 2*h*r ≤ s.m*agreement := by
    have hz : 2*(h : ℤ)*r ≤ (s.m : ℤ)*agreement := by nlinarith only [hn, hw]
    exact_mod_cast hz
  unfold WidthGuard cutoffCount
  apply Int.ofNat_lt.mp
  push_cast [Nat.cast_sub hh, Nat.cast_sub hbuf]
  rw [agreement_cast] at hw
  nlinarith only [hw]

private def Guard (lo r : ℕ) (s : Shape) : Prop :=
  0 < worstWidth s r lo ∧ 2*r ≤ s.B ∧ s.U < p
private instance (lo r : ℕ) (s : Shape) : Decidable (Guard lo r s) := by
  unfold Guard
  infer_instance
private theorem row_guards (b : HighBand) {s : Stage} (hs : s ∈ stages b) :
    Guard (Front82170.row b).lo s.reserve s.free.shape ∧ Guard (Front82170.row b).lo s.reserve s.moving.shape := by
  have cert : (stages b).all (fun t => decide (Guard (Front82170.row b).lo t.reserve t.free.shape ∧
      Guard (Front82170.row b).lo t.reserve t.moving.shape)) = true := by cases b <;> decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp cert s hs)
private theorem width {s : Shape} {r lo h : ℕ} (hl : lo ≤ h) (hh : h ≤ 131071)
    (g : Guard lo r s) : WidthGuard h r s := by
  have hx : 0 ≤ (h : ℤ)-lo := sub_nonneg.mpr (Int.ofNat_le.mpr hl)
  have hw : 0 ≤ (s.B : ℤ)-2*r := by
    have hz := Int.ofNat_le.mpr g.2.1
    push_cast at hz
    exact sub_nonneg.mpr hz
  apply width_of_pos _ _ _ hh
  have he : worstWidth s r h = worstWidth s r lo + ((h : ℤ)-lo)*((s.B : ℤ)-2*r) := by
    unfold worstWidth origin
    ring
  rw [he]
  exact add_pos_of_pos_of_nonneg g.1 (mul_nonneg hx hw)
theorem proof : HighFamily82170.c2 := by
  classical
  intro b u del M Γ F hb _ rows src
  obtain ⟨hlo, hhi⟩ := window_nat hb
  have hh := (terminal_guards b).1.trans_le hlo
  have hup := hhi.trans (terminal_guards b).2.1
  have hu : M.overhead.toNat ≤ 131071 := hup.trans (by decide)
  have hk : 1 ≤ 131071-M.overhead.toNat := by omega
  refine ⟨fun s hs => Classical.choice ?_⟩
  obtain ⟨fg,mg⟩ := row_guards b hs
  obtain ⟨hf,hm⟩ := HighBanks82170.stage_surpluses b s hs hlo hu
  exact pair_of_tests src hh hk hs (width hlo hu fg) hf fg.2.2 (width hlo hu mg) hm
theorem terminal : HighFamily82170.c4 := by
  intro b h hl hu x
  exact HighTerminal82170.terminal_surpluses b x hl ((hu.trans (terminal_guards b).2.1).trans_lt (by decide))
end HighFamily82170_2
end
