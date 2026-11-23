import ProximityPrize.SubmissionLower.GoldBranch7N4
import ProximityPrize.SubmissionLower.SilverBase
set_option Elab.async false
set_option autoImplicit true
section
namespace P3_7_2
open P3 (agreement)
open K1_14 (Shape triangle shapeSum)
def cutoffCount (h r : ℕ) (s : Shape) : ℕ :=
  s.m * agreement - 2 * h * r
def rawWidth (h r : ℕ) (s : Shape) (q j : ℕ) : ℕ :=
  cutoffCount h r s + j - q * (131071 - h)
end P3_7_2
end
section
namespace P3_7_2
open Finset
open P3 (agreement p)
open P3_7 (Bank debit)
open K1_14 (Shape shapeSum triangle)
open private twice_sum_linear from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic
open private row rising level   tailSum  from ProximityPrize.SubmissionLower.SilverBase
def cut (s : Shape) (r lo mode : ℕ) : ℕ :=
  min (s.B+1) ((cutoffCount lo r s - 1 - (2*lo*mode-1)*s.J) / (131071-lo) + 1)
private def tailLength (s : Shape) (r lo mode q : ℕ) : ℕ :=
  min (min q s.J+1) ((rawWidth lo r s q 0 - 1) / (2*lo*mode-1) + 1)
private def total (s : Shape) (r lo mode : ℕ) (x y z : ℤ) : ℤ :=
  let k := cut s r lo mode
  rising x y z s.J + level x y z s.J (k-s.J) +
    6*tailSum (fun q => row x y z q (tailLength s r lo mode q)) k (s.B+1-k)
private def origin (s : Shape) (r : ℕ) (h : ℤ) : ℤ := (s.m : ℤ)*agreement - 2*h*r
private def leftTotal (s : Shape) (r lo mode : ℕ) : ℤ :=
  total s r lo mode (2*origin s r lo) (-2*(131071-(lo : ℤ))) (1-2*(lo : ℤ)*mode)
private def slopeTotal (s : Shape) (r lo mode : ℕ) : ℤ :=
  total s r lo mode (-4*(r : ℤ)) 2 (-2*(mode : ℤ))
def worstWidth (s : Shape) (r : ℕ) (h : ℤ) : ℤ :=
  origin s r h - (131071-h)*s.B
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
end P3_7_2
end
section
namespace P3_7_2
open P3 (HighBand)
open P3_7 (Stage stages)
local notation "bank!" kk "," ww "," zz "," dd =>
  checked (k := kk) (w := ww) (z := zz) (d := dd)
    rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide)
end P3_7_2
end
