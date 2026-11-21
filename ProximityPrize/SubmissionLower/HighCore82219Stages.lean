import ProximityPrize.SubmissionLower.HighCore82219Data
import ProximityPrize.SubmissionLower.GoldBranch7N2

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

section
namespace HighCore82219Stages
open Finset
open P3 (p)
open HighCore82219 (agreement cutoffCount rawWidth WidthGuard gain)
open HighCore82219 (Bank debit)
open K1_14 (Shape shapeSum triangle)
open private twice_sum_linear from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic
open private row rising level sum_rising sum_level tailSum tailSum_eq from ProximityPrize.SubmissionLower.SilverBase
private theorem agreement_cast : (agreement : ℤ) = 179915 := rfl
def cut (s : Shape) (r lo mode : ℕ) : ℕ :=
  min (s.B+1) ((cutoffCount lo r s - 1 - (2*lo*mode-1)*s.J) / (131071-lo) + 1)
private def tailLength (s : Shape) (r lo mode q : ℕ) : ℕ :=
  min (min q s.J+1) ((rawWidth lo r s q 0 - 1) / (2*lo*mode-1) + 1)
private def support (s : Shape) (r lo mode q : ℕ) : ℕ :=
  if q < cut s r lo mode then min q s.J+1 else tailLength s r lo mode q
private def total (s : Shape) (r lo mode : ℕ) (x y z : ℤ) : ℤ :=
  let k := cut s r lo mode
  rising x y z s.J + level x y z s.J (k-s.J) +
    6*tailSum (fun q => row x y z q (tailLength s r lo mode q)) k (s.B+1-k)
private theorem total_eq (s : Shape) (r lo mode : ℕ) (x y z : ℤ)
    (hj : s.J ≤ cut s r lo mode) :
    total s r lo mode x y z = 6*(∑ q ∈ range (s.B+1), row x y z q (support s r lo mode q)) := by
  let k := cut s r lo mode
  let f := fun q => row x y z q (support s r lo mode q)
  have hk : k ≤ s.B+1 := min_le_left _ _
  have hsplit := sum_range_add f k (s.B+1-k)
  have hprefix := sum_range_add f s.J (k-s.J)
  rw [Nat.add_sub_of_le hk] at hsplit
  rw [Nat.add_sub_of_le hj] at hprefix
  change _ = 6*(∑ q ∈ range (s.B+1), f q)
  rw [hsplit, hprefix, mul_add, mul_add]
  have hfirst : (∑ q ∈ range s.J, f q) = ∑ q ∈ range s.J, row x y z q (q+1) := by
    apply sum_congr rfl
    intro q hq
    have hq' := mem_range.mp hq
    simp only [f, support, ite_eq_left (hq'.trans_le hj), min_eq_left hq'.le]
  have hmiddle : (∑ i ∈ range (k-s.J), f (s.J+i)) =
      ∑ i ∈ range (k-s.J), row x y z (s.J+i) (s.J+1) := by
    apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    have hlt : s.J+i < cut s r lo mode := by change s.J+i < k; omega
    simp only [f, support, ite_eq_left hlt, min_eq_right (Nat.le_add_right _ _)]
  have hlast : (∑ i ∈ range (s.B+1-k), f (k+i)) =
      ∑ i ∈ range (s.B+1-k), row x y z (k+i) (tailLength s r lo mode (k+i)) := by
    apply sum_congr rfl
    intro i _
    have hge : cut s r lo mode ≤ k+i := Nat.le_add_right k i
    simp only [f, support, ite_eq_right (not_lt_of_ge hge)]
  rw [hfirst, hmiddle, hlast, sum_rising, sum_level]
  dsimp only [total]
  rw [tailSum_eq]
private def origin (s : Shape) (r : ℕ) (h : ℤ) : ℤ := (s.m : ℤ)*agreement - 2*h*r
private def signedWidth (s : Shape) (r : ℕ) (h : ℤ) (mode q j : ℕ) : ℤ :=
  origin s r h - (131071-h)*q + (1-2*h*mode)*j
private def leftTotal (s : Shape) (r lo mode : ℕ) : ℤ :=
  total s r lo mode (2*origin s r lo) (-2*(131071-(lo : ℤ))) (1-2*(lo : ℤ)*mode)
private def slopeTotal (s : Shape) (r lo mode : ℕ) : ℤ :=
  total s r lo mode (-4*(r : ℤ)) 2 (-2*(mode : ℤ))
private theorem signed_le (s : Shape) (r h mode q j : ℕ) (hh : h ≤ 131071) :
    signedWidth s r h mode q j ≤ ((rawWidth h r s q j - mode*(2*h*j) : ℕ) : ℤ) := by
  have cast_sub_le (a b : ℕ) : (a : ℤ)-b ≤ ((a-b : ℕ) : ℤ) := by omega
  have hcut := cast_sub_le (s.m*agreement) (2*h*r)
  have hraw := cast_sub_le (cutoffCount h r s+j) (q*(131071-h))
  have hloss := cast_sub_le (rawWidth h r s q j) (mode*(2*h*j))
  change _ ≤ (cutoffCount h r s : ℤ) at hcut
  change _ ≤ (rawWidth h r s q j : ℤ) at hraw
  push_cast [Nat.cast_sub hh] at hcut hraw hloss
  unfold signedWidth origin
  rw [agreement_cast]
  nlinarith only [hcut, hraw, hloss]
private theorem row_affine (s : Shape) (r lo h mode q n : ℕ) :
    row (2*origin s r lo) (-2*(131071-(lo : ℤ))) (1-2*(lo : ℤ)*mode) q n +
      ((h : ℤ)-lo)*row (-4*(r : ℤ)) 2 (-2*(mode : ℤ)) q n =
    2*(∑ j ∈ range n, signedWidth s r h mode q j) := by
  change _ = 2*(∑ j ∈ range n, (origin s r h - (131071-(h : ℤ))*q + (1-2*(h : ℤ)*mode)*j))
  rw [twice_sum_linear]
  unfold row origin
  ring
private theorem support_le (s : Shape) (r lo h mode : ℕ) (hh : h ≤ 131071)
    (hj : s.J ≤ cut s r lo mode) :
    leftTotal s r lo mode + ((h : ℤ)-lo)*slopeTotal s r lo mode ≤
      12*(shapeSum s (fun q j => rawWidth h r s q j - mode*(2*h*j)) : ℤ) := by
  let f := fun q => row (2*origin s r lo) (-2*(131071-(lo : ℤ))) (1-2*(lo : ℤ)*mode) q
    (support s r lo mode q)
  let g := fun q => row (-4*(r : ℤ)) 2 (-2*(mode : ℤ)) q (support s r lo mode q)
  have hsum : (∑ q ∈ range (s.B+1), f q) + ((h : ℤ)-lo)*(∑ q ∈ range (s.B+1), g q) ≤
      2*(shapeSum s (fun q j => rawWidth h r s q j - mode*(2*h*j)) : ℤ) := by
    unfold shapeSum
    push_cast [Nat.cast_sum]
    rw [mul_sum, ← sum_add_distrib, mul_sum]
    apply sum_le_sum
    intro q _
    rw [show f q + ((h : ℤ)-lo)*g q = _ from row_affine s r lo h mode q (support s r lo mode q)]
    have hsub : range (support s r lo mode q) ⊆ range (min q s.J+1) := by
      apply range_mono
      unfold support
      split
      · rfl
      · exact min_le_left _ _
    apply mul_le_mul_of_nonneg_left _ (by decide : (0 : ℤ) ≤ 2)
    calc
      _ ≤ ∑ j ∈ range (support s r lo mode q), ((rawWidth h r s q j - mode*(2*h*j) : ℕ) : ℤ) :=
        sum_le_sum fun j _ => signed_le s r h mode q j hh
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Int.natCast_nonneg _)
  unfold leftTotal slopeTotal
  rw [total_eq _ _ _ _ _ _ _ hj, total_eq _ _ _ _ _ _ _ hj]
  have hz := mul_le_mul_of_nonneg_left hsum (by decide : (0 : ℤ) ≤ 6)
  dsimp only [f, g] at hz
  nlinarith only [hz]
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
def leftSurplus (t : Bank) (r lo mode : ℕ) : ℤ :=
  (triangle t.shape.U : ℤ)*leftTotal t.shape r lo mode - 12*(debit lo t : ℤ)
def slopeSurplus (t : Bank) (r lo mode : ℕ) : ℤ :=
  (triangle t.shape.U : ℤ)*slopeTotal t.shape r lo mode - 24*((t.shape.U : ℤ)+1)*t.poleMoment
structure BankCertificate (lo r mode : ℕ) (t : Bank) : Prop where
  full_prefix : t.shape.J ≤ cut t.shape r lo mode
  width_left : 0 < worstWidth t.shape r lo
  width_slope : 2*r ≤ t.shape.B
  surplus_left : 0 < leftSurplus t r lo mode
  surplus_slope : 0 ≤ slopeSurplus t r lo mode
  seed_cap : t.shape.U < p
theorem checked {lo r mode : ℕ} {t : Bank} {k w z d : ℕ}
    (hcut : cut t.shape r lo mode = k) (hw : worstWidth t.shape r lo = (w : ℤ))
    (hz : leftSurplus t r lo mode = (z : ℤ))
    (hd : slopeSurplus t r lo mode = (d : ℤ))
    (hj : t.shape.J ≤ k) (hw' : 0 < w) (hs : 2*r ≤ t.shape.B)
    (hz' : 0 < z) (hc : t.shape.U < p) : BankCertificate lo r mode t :=
  ⟨hcut.symm ▸ hj, hw.symm ▸ Int.ofNat_lt.mpr hw', hs,
    hz.symm ▸ Int.ofNat_lt.mpr hz', hd.symm ▸ Int.natCast_nonneg _, hc⟩
theorem of_certificate {lo h r mode : ℕ} {t : Bank} (hl : lo ≤ h) (hh : h ≤ 131071)
    (cert : BankCertificate lo r mode t) :
    WidthGuard h r t.shape ∧ debit h t < gain h r t.shape mode ∧ t.shape.U < p := by
  have hx : 0 ≤ (h : ℤ)-lo := sub_nonneg.mpr (Int.ofNat_le.mpr hl)
  have hw : 0 ≤ (t.shape.B : ℤ)-2*r := by
    have h := Int.ofNat_le.mpr cert.width_slope
    push_cast at h
    exact sub_nonneg.mpr h
  have he : worstWidth t.shape r h =
      worstWidth t.shape r lo + ((h : ℤ)-lo)*((t.shape.B : ℤ)-2*r) := by
    unfold worstWidth origin
    ring
  have hw' := add_pos_of_pos_of_nonneg cert.width_left (mul_nonneg hx hw)
  refine ⟨width_of_pos _ _ _ hh (he.symm ▸ hw'), ?_, cert.seed_cap⟩
  have hz := add_pos_of_pos_of_nonneg cert.surplus_left (mul_nonneg hx cert.surplus_slope)
  have hs := mul_le_mul_of_nonneg_left (support_le _ _ _ _ _ hh cert.full_prefix)
    (Int.natCast_nonneg (triangle t.shape.U))
  unfold leftSurplus slopeSurplus at hz
  unfold gain
  simp only [HighCore82219.debit, P1_7.debit] at hz ⊢
  apply Int.ofNat_lt.mp
  push_cast at hz ⊢
  nlinarith only [hz, hs]
end HighCore82219Stages
end
