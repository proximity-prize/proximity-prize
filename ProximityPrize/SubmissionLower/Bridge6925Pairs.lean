import ProximityPrize.SubmissionLower.PoleReceipts
import ProximityPrize.SubmissionLower.Bridge6925Defs
import ProximityPrize.SubmissionLower.Fast076
import ProximityPrize.SubmissionLower.Pack_K1_14_2_1Split
set_option Elab.async false
section PackSource_P0_10_2Arithmetic
set_option autoImplicit true
namespace P0_10_2

open P0 (agreement)
open K1_14 (Shape triangle shapeSum)
open K1_14_2_1 (movingCeiling)
open Finset
open private twice_sum_linear nodeRow nodeCost debit_eq from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic

def cutoffCount (h r : ℕ) (s : Shape) : ℕ :=
  s.m * agreement - 2 * h * r

def rawWidth (h r : ℕ) (s : Shape) (q j : ℕ) : ℕ :=
  cutoffCount h r s + j - q * (131071 - h)

def rawVolume (h r : ℕ) (s : Shape) : ℕ :=
  triangle s.U * shapeSum s (rawWidth h r s)

private def baseRow (s : Shape) (q : ℕ) : ℤ :=
  (((min q s.J : ℕ) : ℤ) + 1) *
    (2 * ((s.m : ℤ) * agreement - (q : ℤ) * 131071) + min q s.J)

private def slopeRow (s : Shape) (r mode q : ℕ) : ℤ :=
  (((min q s.J : ℕ) : ℤ) + 1) *
    (2 * ((q : ℤ) - 2 * r) - 2 * mode * min q s.J)

private def widthBase (s : Shape) : ℤ :=
  ∑ q ∈ range (s.B + 1), baseRow s q

private def widthSlope (s : Shape) (r mode : ℕ) : ℤ :=
  ∑ q ∈ range (s.B + 1), slopeRow s r mode q

private theorem width_cast (h r : ℕ) (s : Shape) (q j : ℕ)
    (hh : h ≤ 131071) (hq : q ≤ s.B)
    (hw : s.B * (131071 - h) < cutoffCount h r s) :
    (rawWidth h r s q j : ℤ) =
      (s.m : ℤ) * agreement - 2 * (h : ℤ) * r + j - (q : ℤ) * (131071 - h) := by
  have hq' := (Nat.mul_le_mul_right (131071 - h) hq).trans hw.le
  have hbuf : 2 * h * r ≤ s.m * agreement := by unfold cutoffCount at hw; omega
  unfold rawWidth cutoffCount at *
  rw [Nat.cast_sub (by omega : q * (131071 - h) ≤ s.m * agreement - 2 * h * r + j)]
  push_cast [Nat.cast_sub hh, Nat.cast_sub hbuf]
  rfl

private theorem volume_eq (h r mode : ℕ) (s : Shape) (hh : h ≤ 131071)
    (hw : s.B * (131071 - h) < cutoffCount h r s) :
    2 * ((rawVolume h r s : ℤ) - mode * (movingCeiling h s : ℤ)) =
      (triangle s.U : ℤ) * (widthBase s + h * widthSlope s r mode) := by
  calc
    _ = (triangle s.U : ℤ) * ∑ q ∈ range (s.B + 1), 2 *
          ∑ j ∈ range (min q s.J + 1), ((rawWidth h r s q j : ℤ) - mode * (2 * h * j)) := by
      unfold rawVolume movingCeiling shapeSum
      push_cast [Nat.cast_sum]
      simp only [sum_sub_distrib, ← mul_sum, mul_sub]
      ring
    _ = (triangle s.U : ℤ) * (widthBase s + h * widthSlope s r mode) := by
      unfold widthBase widthSlope baseRow slopeRow
      congr 1
      rw [mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro q hqr
      have hq : q ≤ s.B := Nat.le_of_lt_succ (mem_range.mp hqr)
      simp_rw [width_cast h r s q _ hh hq hw]
      let a : ℤ := (s.m : ℤ) * agreement - 2 * (h : ℤ) * r - (q : ℤ) * (131071 - h)
      let b : ℤ := 1 - 2 * (h : ℤ) * mode
      have hrow : ∀ j : ℕ,
          (s.m : ℤ) * agreement - 2 * (h : ℤ) * r + j - (q : ℤ) * (131071 - h) -
            mode * (2 * (h : ℤ) * j) = a + b * j := by
        intro j
        dsimp [a, b]
        ring
      simp_rw [hrow]
      rw [twice_sum_linear]
      push_cast
      dsimp [a, b]
      ring


private def worstBase (s : Shape) : ℤ := (s.m : ℤ) * agreement - (s.B : ℤ) * 131071
private def worstSlope (s : Shape) (r : ℕ) : ℤ := (s.B : ℤ) - 2 * r

private def surplusBase (s : Shape) : ℤ := (triangle s.U : ℤ) * widthBase s - 2 * nodeCost s
private def surplusSlope (s : Shape) (r mode : ℕ) : ℤ :=
  (triangle s.U : ℤ) * widthSlope s r mode - 2 * (2 * BankDebit.extra s : ℕ)

/-- The width guard and twice the source-rank surplus at both endpoints. -/
def Certificate (s : Shape) (r mode lo hi : ℕ) : Prop :=
  0 < worstBase s + lo * worstSlope s r ∧
  0 < worstBase s + hi * worstSlope s r ∧
  0 < surplusBase s + lo * surplusSlope s r mode ∧
  0 < surplusBase s + hi * surplusSlope s r mode

/-- The two signed width coefficients and the unscaled node and pole debits. -/
def rowStats (s : Shape) (r mode q : ℕ) : ℤ × ℤ × ℕ × ℕ :=
  (baseRow s q, slopeRow s r mode q, nodeRow (min q s.J + 1) (s.m + min q s.J - q),
    (min q s.J + 1) * ((s.B + s.J - q) * (s.B - q)))

theorem certificate_of_stats {s : Shape} {r mode lo hi : ℕ} {a b : ℤ} {c d pole : ℕ}
    (hs : (∑ q ∈ range (s.B + 1), rowStats s r mode q) = (a, b, c, d))
    (hp : BankDebit.extra s = pole)
    (hc : 0 < worstBase s + lo * worstSlope s r ∧
      0 < worstBase s + hi * worstSlope s r ∧
      0 < (triangle s.U : ℤ) * (a + lo * b)
        - 2 * ((triangle s.U * 262144 * c : ℕ) : ℤ) - 2 * lo * ((2 * pole : ℕ) : ℤ) ∧
      0 < (triangle s.U : ℤ) * (a + hi * b)
        - 2 * ((triangle s.U * 262144 * c : ℕ) : ℤ) - 2 * hi * ((2 * pole : ℕ) : ℤ)) :
    Certificate s r mode lo hi := by
  have ha : widthBase s = a := by
    simpa only [Prod.fst_sum, widthBase, rowStats] using congrArg Prod.fst hs
  have hb : widthSlope s r mode = b := by
    simpa only [Prod.fst_sum, Prod.snd_sum, widthSlope, rowStats] using
      congrArg (fun t => t.2.1) hs
  have hn : nodeCost s = triangle s.U * 262144 * c := by
    unfold nodeCost
    congr 1
    simpa only [Prod.fst_sum, Prod.snd_sum, rowStats] using congrArg (fun t => t.2.2.1) hs
  unfold Certificate surplusBase surplusSlope
  rw [ha, hb, hn, hp]
  exact ⟨hc.1, hc.2.1, by linarith only [hc.2.2.1], by linarith only [hc.2.2.2]⟩

private theorem affine_positive {a b h lo hi : ℤ} (hlo : lo ≤ h) (hhi : h ≤ hi)
    (ha : 0 < a + lo * b) (hb : 0 < a + hi * b) : 0 < a + h * b := by
  by_cases hb0 : 0 ≤ b
  · nlinarith only [ha, mul_nonneg (sub_nonneg.mpr hlo) hb0]
  · nlinarith only [hb, mul_nonneg (sub_nonneg.mpr hhi) (neg_nonneg.mpr (le_of_not_ge hb0))]

theorem test {h r mode lo hi : ℕ} {s : Shape} (hlo : lo ≤ h) (hhi : h ≤ hi)
    (hh : h ≤ 131071) (hc : Certificate s r mode lo hi) :
    s.B * (131071 - h) < cutoffCount h r s ∧
      BankDebit.debit h s + mode * movingCeiling h s < rawVolume h r s := by
  have hloI : (lo : ℤ) ≤ (h : ℤ) := by exact_mod_cast hlo
  have hhiI : (h : ℤ) ≤ (hi : ℤ) := by exact_mod_cast hhi
  obtain ⟨ha, hb, hc, hd⟩ := hc
  have hw := affine_positive hloI hhiI ha hb
  unfold worstBase worstSlope at hw
  have hpos : (s.B : ℤ) * (131071 - (h : ℤ)) <
      (s.m : ℤ) * agreement - 2 * (h : ℤ) * r := by nlinarith only [hw]
  have hbuf : 2 * h * r ≤ s.m * agreement := by
    have hn : 0 ≤ (s.B : ℤ) * (131071 - (h : ℤ)) := by
      exact mul_nonneg (Int.natCast_nonneg _) (by omega)
    have ht : 2 * (h : ℤ) * r ≤ (s.m : ℤ) * agreement := by linarith only [hpos, hn]
    exact_mod_cast ht
  have hwidth : s.B * (131071 - h) < cutoffCount h r s := by
    unfold cutoffCount
    have ht : ((s.B * (131071 - h) : ℕ) : ℤ) <
        ((s.m * agreement - 2 * h * r : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hh, Nat.cast_sub hbuf]
      exact hpos
    exact_mod_cast ht
  have hs := affine_positive hloI hhiI hc hd
  have heq := volume_eq h r mode s hh hwidth
  unfold surplusBase surplusSlope at hs
  push_cast at hs
  refine ⟨hwidth, ?_⟩
  have ht : ((BankDebit.debit h s + mode * movingCeiling h s : ℕ) : ℤ) <
      (rawVolume h r s : ℤ) := by
    unfold BankDebit.debit
    change ((K1_14_1.physicalDebit s + 2*h*BankDebit.extra s + _ : ℕ) : ℤ) < _
    rw [show K1_14_1.physicalDebit s = nodeCost s from by
      simpa [K1_14.sourceDebit, K1_14_1.physicalDebit] using debit_eq s 0]
    push_cast
    nlinarith only [hs, heq]
  exact_mod_cast ht

end P0_10_2
end PackSource_P0_10_2Arithmetic
section PackSource_P0_10_2Certs
set_option autoImplicit true
namespace P0_10_2

open Finset P0_10

private def evaluate {α : Type} [AddMonoid α] (f : ℕ → α) : ℕ → α
  | 0 => 0
  | n + 1 => evaluate f n + f n

private theorem evaluate_eq {α : Type} [AddCommMonoid α] (f : ℕ → α) (n : ℕ) :
    evaluate f n = ∑ q ∈ range n, f q := by
  induction n with
  | zero => simp [evaluate]
  | succ n ih => rw [evaluate, sum_range_succ, ih]

private theorem checked_append {α : Type} [AddCommMonoid α] {f : ℕ → α}
    {a b n : ℕ} {x y z : α}
    (ha : evaluate f a = x) (hb : evaluate (fun q => f (a + q)) b = y)
    (hn : a + b = n) (hz : x + y = z) : evaluate f n = z := by
  rw [← hn, ← hz]
  have h := sum_range_add f a b
  simp only [← evaluate_eq] at h
  exact h.trans (congrArg₂ (· + ·) ha hb)

section

set_option maxRecDepth 8000

-- The four columns are width intercept, width slope, node count and pole count.
-- Each check sums at most 32 grades, after the inner sums have been proved symbolically.

private theorem bridgeFree0 : Certificate ⟨57,79,17,1160⟩ 0 0 2385 3554 := by
  apply certificate_of_stats (a := 11722948800) (b := 112128) (c := 22818) (d := 2957112)
  · rw [← evaluate_eq]
    change evaluate (rowStats ⟨57,79,17,1160⟩ 0 0) 80 = _
    decide +kernel
  · exact PoleReceipts.debit_79_17_1160
  · decide +kernel

private theorem bridgeMoving0 : Certificate ⟨191,265,55,6963⟩ 0 1 2385 3554 := by
  apply certificate_of_stats (a := 408593174752) (b := 2481360) (c := 789656) (d := 342764940)
  · rw [← evaluate_eq]
    change evaluate (rowStats ⟨191,265,55,6963⟩ 0 1) 266 = _
    decide +kernel
  · exact PoleReceipts.debit_265_55_6963
  · decide +kernel

private theorem bridgeFree5 : Certificate ⟨96,133,29,1557⟩ 6 0 2385 3554 := by
  apply certificate_of_stats (a := 54932445850) (b := 440500) (c := 106475) (d := 23311260)
  · rw [← evaluate_eq]
    change evaluate (rowStats ⟨96,133,29,1557⟩ 6 0) 134 = _
    decide +kernel
  · exact PoleReceipts.debit_133_29_1557
  · decide +kernel

private theorem bridgeMoving5 : Certificate ⟨316,439,92,10562⟩ 6 1 2385 3554 := by
  apply certificate_of_stats (a := 1849514760136) (b := 10350900) (c := 3569960) (d := 2580710382)
  · rw [← evaluate_eq]
    change evaluate (rowStats ⟨316,439,92,10562⟩ 6 1) 440 = _
    decide +kernel
  · exact PoleReceipts.debit_439_92_10562
  · decide +kernel

private theorem lateFree : Certificate ⟨216,299,66,3130⟩ 25 0 2385 3554 := by
  apply certificate_of_stats (a := 616432771576) (b := 4125190) (c := 1190657) (d := 587245620)
  · rw [← evaluate_eq]
    change evaluate (rowStats ⟨216,299,66,3130⟩ 25 0) 300 = _
    decide +kernel
  · exact PoleReceipts.debit_299_66_3130
  · decide +kernel

private theorem lateMoving : Certificate ⟨641,890,185,25837⟩ 25 1 2385 3554 := by
  apply certificate_of_stats (a := 15230407200542) (b := 77725680) (c := 29370826) (d := 42940216990)
  · rw [← evaluate_eq]
    change evaluate (rowStats ⟨641,890,185,25837⟩ 25 1) 891 = _
    decide +kernel
  · exact PoleReceipts.debit_890_185_25837
  · decide +kernel


end
theorem stage_tests {w : ℤ} (hlo : 2385 ≤ w) (hhi : w ≤ 3554) (i : Fin 3) :
    let h := w.toNat
    let r := reserve i
    let s := freeShape w i
    let s' := movingShape w i
    (s.B * (131071 - h) < cutoffCount h r s ∧
      BankDebit.debit h s < rawVolume h r s) ∧
    (s'.B * (131071 - h) < cutoffCount h r s' ∧
      BankDebit.debit h s' + K1_14_2_1.movingCeiling h s' < rawVolume h r s') ∧
    s.U < P0.p := by
  dsimp only
  have hh : w.toNat ≤ 131071 := by omega
  have hb : w ≤ 3554 := hhi
  have hl : 2385 ≤ w.toNat := by omega
  have hu : w.toNat ≤ 3554 := by omega
  simp only [freeShape, movingShape, ite_eq_left hb]
  fin_cases i <;> simp only [reserve, Matrix.cons_val_zero', Matrix.cons_val_succ']
  · exact ⟨by simpa only [zero_mul, add_zero] using test hl hu hh bridgeFree0,
        by simpa only [one_mul] using test hl hu hh bridgeMoving0, by decide⟩
  · exact ⟨by simpa only [zero_mul, add_zero] using test hl hu hh bridgeFree5,
        by simpa only [one_mul] using test hl hu hh bridgeMoving5, by decide⟩
  · exact ⟨by simpa only [zero_mul, add_zero] using test hl hu hh lateFree,
        by simpa only [one_mul] using test hl hu hh lateMoving, by decide⟩
end P0_10_2
end PackSource_P0_10_2Certs
section PackSource_P0_10_2Proof
set_option autoImplicit true
set_option maxSynthPendingDepth 8

namespace P0_10_2

noncomputable section

open P0 (AnchorModel AnchoredFamily agreement)
open P0_10
open K1_14 (Shape Banks Jet FX triangle shapeSum seedHasse)
open K1_14_2 (UsesSeed)
open K1_14_2_1 (exists_layered movingCeiling)
open Polynomial Finset
open private sum_rank_le from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Split
open private fixed_of_no_seed from ProximityPrize.SubmissionLower.Fast051

private theorem source_floor {u del} {M : AnchorModel u del} {Γ}
    {F : AnchoredFamily M Γ} {rows : Banks} (src : JetSource M F rows)
    {s : Shape} (hs : s ∈ scheduled M.overhead) (r : ℕ)
    (hw : s.B * (131071 - M.overhead.toNat) < cutoffCount M.overhead.toNat r s) :
    rawVolume M.overhead.toNat r s ≤ BankDebit.debit M.overhead.toNat s +
      ∑ W ∈ range (cutoffCount M.overhead.toNat r s), Module.finrank FX (rows s W) := by
  let N := cutoffCount M.overhead.toNat r s
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hw
  have hNt : N ≤ s.m * agreement := Nat.sub_le _ _
  have hc : N - 1 + 1 = N := by omega
  have h := src.floor_bound s hs (N - 1) (by omega) (by
    intro q hq j _
    rw [hc]
    exact ((Nat.mul_le_mul_right _ hq).trans hw.le).trans (Nat.le_add_right N j))
  change triangle s.U * shapeSum s (fun q j => N + j - q * (131071 - M.overhead.toNat)) ≤
    BankDebit.debit M.overhead.toNat s + ∑ W ∈ range N, Module.finrank FX (rows s W)
  simpa only [hc] using h

private theorem bank_nonzero {u del} {M : AnchorModel u del} {Γ}
    {F : AnchoredFamily M Γ} {rows : Banks} (src : JetSource M F rows)
    {s : Shape} (hs : s ∈ scheduled M.overhead) (r : ℕ)
    (hw : s.B * (131071 - M.overhead.toNat) < cutoffCount M.overhead.toNat r s)
    (hd : BankDebit.debit M.overhead.toNat s < rawVolume M.overhead.toNat r s) :
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
private theorem split_row_degree_from_shifts (power : K1_14_2_1.c1) (h N W : ℕ) (hh : 0 < h)
    (hW : W < N) {G P R : Jet} (hi : Irreducible G) (hv : 0 < G.natDegree)
    (hm : UsesSeed G) (hP : P ≠ 0) (hdiv : G ∣ P) {U : ℕ} (hp : U < P0.p)
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
    {rows : Banks} (src : JetSource M F rows) (power : K1_14_2_1.c1) (rankBound : K1_14_2_1.c2)
    (hh : 0 < M.overhead.toNat) {s : Shape} (hs : s ∈ scheduled M.overhead) (r : ℕ)
    (hw : s.B * (131071 - M.overhead.toNat) < cutoffCount M.overhead.toNat r s)
    (hd : BankDebit.debit M.overhead.toNat s + movingCeiling M.overhead.toNat s <
      rawVolume M.overhead.toNat r s)
    {G P : Jet} (hi : Irreducible G) (hv : 0 < G.natDegree) (hm : UsesSeed G)
    (hP : P ≠ 0) (hdiv : G ∣ P) {U : ℕ} (hp : U < P0.p)
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

theorem proof : P0_10.c2 := by
  classical
  intro u del M Γ F hlo hhi rows src
  have hlo' : 2385 ≤ M.overhead := hlo
  have hhi' : M.overhead ≤ 3554 := hhi
  have hh : 0 < M.overhead.toNat := by omega
  have hpairs (i : Fin 3) : Nonempty (BufferedPair M.overhead rows i) := by
    let s := freeShape M.overhead i
    let s' := movingShape M.overhead i
    let r := reserve i
    have hs : s ∈ scheduled M.overhead := by
      fin_cases i <;> simp [s, scheduled]
    have hs' : s' ∈ scheduled M.overhead := by
      fin_cases i <;> simp [s', scheduled]
    obtain ⟨⟨hwidth, hfree⟩, ⟨hwidth', hmoving⟩, hchar⟩ := stage_tests hlo' hhi' i
    obtain ⟨P, hPm, hP⟩ := bank_nonzero src hs r hwidth hfree
    have hnonzero := bank_nonzero src hs' r hwidth'
      (lt_of_le_of_lt (Nat.le_add_right _ _) hmoving)
    have hseed (j y : ℕ) : ((P.coeff j).coeff y).totalDegree ≤ s.U := by
      by_cases hz : (P.coeff j).coeff y = 0
      · simp [hz]
      · exact (src.shape s hs _ P hPm j y hz).2.2
    obtain ⟨Q, hQm, hQ, havoid⟩ := exists_layered P hP _ hnonzero (fun G hi hdiv hv hm =>
      avoids_one src K1_14_2_1_1.proof K1_14_2_1_2.proof hh hs' r hwidth' hmoving
        hi hv hm hP hdiv hchar hseed)
    have hcut (a : Shape) : reserveCutoff M.overhead a i = cutoffCount M.overhead.toNat r a - 1 := by
      unfold reserveCutoff fullCutoff cutoffCount
      dsimp only [r]
      omega
    exact ⟨⟨P, Q, hP, hQ, (hcut _).symm ▸ hPm, (hcut _).symm ▸ hQm,
      fun G hi hdiv hdiv' hv => fixed_of_no_seed G (fun hm => havoid G hi hdiv hv hm hdiv')⟩⟩
  exact ⟨fun i => Classical.choice (hpairs i)⟩

end
end P0_10_2
end PackSource_P0_10_2Proof
