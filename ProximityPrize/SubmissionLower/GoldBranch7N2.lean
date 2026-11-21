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
def WidthGuard (h r : ℕ) (s : Shape) : Prop :=
  s.B * (131071 - h) < cutoffCount h r s
def gain (h r : ℕ) (s : Shape) (mode : ℕ) : ℕ :=
  triangle s.U * shapeSum s (fun q j => rawWidth h r s q j - mode * (2 * h * j))
end P3_7_2
end
section
namespace P3_7_2
open Finset
open P3 (agreement p)
open P3_7 (Bank debit)
open K1_14 (Shape shapeSum triangle)
open private twice_sum_linear from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic
open private row rising level sum_rising sum_level tailSum tailSum_eq from ProximityPrize.SubmissionLower.SilverBase
private theorem agreement_cast : (agreement : ℤ) = 179983 := rfl
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
  simp only [P3_7.debit, P1_7.debit] at hz ⊢
  apply Int.ofNat_lt.mp
  push_cast at hz ⊢
  nlinarith only [hz, hs]
end P3_7_2
end
section
namespace P3_7_2
open P3 (HighBand)
open P3_7 (Stage stages)
private def Checks (lo : ℕ) (ss : List Stage) : Prop :=
  ∀ s ∈ ss, BankCertificate lo s.reserve 0 s.free ∧ BankCertificate lo s.reserve 1 s.moving
private theorem nil {lo : ℕ} : Checks lo [] :=
  fun _ hs => (List.not_mem_nil hs).elim
private theorem cons {lo : ℕ} {s : Stage} {ss : List Stage}
    (hf : BankCertificate lo s.reserve 0 s.free) (hm : BankCertificate lo s.reserve 1 s.moving)
    (ht : Checks lo ss) : Checks lo (s :: ss) :=
  List.forall_mem_cons.mpr ⟨⟨hf, hm⟩, ht⟩
local notation "bank!" kk "," ww "," zz "," dd =>
  checked (k := kk) (w := ww) (z := zz) (d := dd)
    rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide)
set_option maxHeartbeats 4000000 in
theorem certificates (b : HighBand) : Checks b.row.lo (stages b) := by
  cases b with
  | h2274 =>
    rw [stages, HighBand.row]
    refine cons (bank! 106,155023,0x2d6d8028b0,0x777b784258) (bank! 498,344194,0x1b7f5a9b6378,0x171787ee2faf10) ?_
    refine cons (bank! 112,97625,0x2bcf16c970,0xbfef2eefc8) (bank! 494,314885,0xb948b380234,0x213fda5b67a3c4) ?_
    refine cons (bank! 126,89749,0x40a48e38d8,0x108232b7638) (bank! 543,427486,0x1d57a7169838,0x31ea5b9daf9cc8) ?_
    refine cons (bank! 138,159484,0x41cc3484c0,0x1670ea60a60) (bank! 595,436051,0x78a5464721f0,0x485bfb1ff2372c) ?_
    refine cons (bank! 148,126847,0x18abc05070,0x1f30e6abe10) (bank! 670,490810,0x7232591cdd44,0x6a328d84882fa8) ?_
    refine cons (bank! 160,196582,0xae15105c00,0x2983e026d00) (bank! 723,499375,0x11917b95ee024,0x943dd9621eaef4) ?_
    refine cons (bank! 159,140848,0x8c39b89a08,0x3e63be29988) (bank! 812,550806,0x1dd787193c280,0xd96a1a9c25a5b8) ?_
    refine cons (bank! 198,139097,0x14b39dc3088,0xa1c0e14e070) (bank! 924,557176,0x1fe1f2897b418,0x22f591973ae99b8) ?_
    refine cons (bank! 271,248727,0x1b89815e378,0x1e82a49a14fc) (bank! 1205,745683,0x9fd575f02d870,0x7bbbc8018f247e0) ?_
    refine cons (bank! 328,277505,0xd9a6f84db88,0x2db57d01eae0) (bank! 1426,889747,0xae812f3bb6ae0,0xcc31b472eb55990) ?_
    refine cons (bank! 325,276642,0x5ecbfadd1c8,0x7407dec5f568) (bank! 1757,1117792,0x20010261a5c294,0x21eb1ea7d863213c) ?_
    refine cons (bank! 363,205513,0x55f948ccd4c, 0x1d35890b7c5e8) (bank! 2033,1221256,0x3ad2bdda195798,0x54b77e29ce7892f0) ?_
    refine cons (bank! 348,139463,0x1215621b6640,0x86b44e4aa89680) (bank! 1685,977484,0xbf16dbaaef0b0,0x9d50fc957741b0b8) ?_
    refine cons (bank! 616,456705,0x268c5e0d97b0,0x8b0b967833c00) (bank! 3042,1806260,0x1ac227dea0a6ccc, 0x28edeadd77f78cf40) ?_
    refine cons (bank! 943,693278,0x274d4aabc0524,0x2d3a566eb28a6c) (bank! 4693,2884182,0x8b1756ff208ccf0,0x10fde3a09f34a61190) ?_
    refine cons (bank! 1384,882803,0xd12a457b98c98,0x1cc027e4a9aef94) (bank! 7322,4557449,0x52bdc2f34dcf1d8,0xa44ed4915f33c5ff00) ?_
    exact nil
  | h2294 =>
    rw [stages, HighBand.row]
    refine cons (bank! 102,132282,0x1bd259f9a0,0x6ed6aa9430) (bank! 489,382063,0x1c7c882fd2d0,0x11bd6c3c7cb760) ?_
    refine cons (bank! 109,126170,0x3853f4970,0xaf6e1067e8) (bank! 479,276587,0x7412bc492b0,0x18cf06f8494cf8) ?_
    refine cons (bank! 120,144899,0xc313b89b8,0xf5fd0dc284) (bank! 535,388584,0x10e56eebc850,0x25c81976c95128) ?_
    refine cons (bank! 131,163628,0x3295b4e648,0x15561c22410) (bank! 571,298805,0x27d1b9789e18,0x36672f16eb2e6c) ?_
    refine cons (bank! 142,182357,0x4722c22a40,0x1cf1c68ce60) (bank! 608,389009,0x23bd64df680,0x4c728310189ed8) ?_
    refine cons (bank! 151,98674,0xada9986ac0,0x27c7afeb768) (bank! 724,436084,0xeb41d74001c8,0x76c0e7569b77e0) ?_
    refine cons (bank! 150,222863,0x41ca05d834,0x3e80456c2d8) (bank! 791,571398,0x9acb9c136a40,0xa8317217113040) ?_
    refine cons (bank! 198,142637,0x4bbb562640,0x909d00c6b00) (bank! 966,566152,0x47296195e84e4,0x1d8f97555caa0d4) ?_
    refine cons (bank! 227,160219,0x218bba38f60,0x2c8654eb6340) (bank! 1180,748934,0x13d052998ca30,0x6023f57e2e3fa90) ?_
    refine cons (bank! 307,287897,0x8a446eba2c0,0x27ecfb7d1020) (bank! 1320,760484,0xb773c3e17f118,0x9176b6c51c2b7b4) ?_
    refine cons (bank! 295,185846,0xcaed63470,0x9870f2f51640) (bank! 1546,966583,0x10085007e899c8,0x16304b4fcfd28ae8) ?_
    refine cons (bank! 363,211473,0xaf7114ccc10,0x195ff33763350) (bank! 2029,1235895,0x127ded8e061740,0x44e8586ffe98dfc0) ?_
    refine cons (bank! 342,197693,0x77edde6c6d0,0x7c3a801381be30) (bank! 1692,1008300,0x28de042813ca28,0x6749d8d72504d674) ?_
    refine cons (bank! 387,314639,0xdda601806c, 0x9ac9711d3576b8) (bank! 1719,845899,0xcb4d7877cc90,0x1719a15ab7141f358) ?_
    refine cons (bank! 741,568190,0x9f45f19ec9c0,0x8831011597fe0) (bank! 3123,1873177,0x5c1aec67dee5ac, 0x231c87cc6e5af6ed4) ?_
    refine cons (bank! 884,567452,0x212782c508100,0x2ae9a33c929580) (bank! 4817,2896404,0x3dedcec508b4434,0xf2b2556ace6893e1c) ?_
    refine cons (bank! 1073,799098,0x4950805cc9380,0x6ba170e70e8480) (bank! 5782,3421264,0x874ee779f4f5998,0x263eba2f67975f1598) ?_
    refine cons (bank! 1444,1097695,0x5d49b639dcb0,0x19da8c343b0bfe0) (bank! 7607,4378831,0x24c90aea789f0038,0x96c9c0cbe2269ac690) ?_
    exact nil
  | h7773 =>
    rw [stages, HighBand.row]
    refine cons (bank! 16,130343,0x9ead4bb0,39067056) (bank! 29,147316,0xa4eebff58,0x1d4ed9a8) ?_
    refine cons (bank! 30,172909,0x6143f05e0,0xd5e5da0) (bank! 54,273468,0x9243aa8650,0x11f852ac0) ?_
    refine cons (bank! 48,246686,0x344dd4d8b8,0x5c1ee518) (bank! 90,467660,0x63fc3505f80,0x9f40923c0) ?_
    refine cons (bank! 76,316272,0x1f5d0ff3818,0x2eeb83a88) (bank! 142,637805,0x44bd52a34490,0x5d909c030c) ?_
    exact nil
end P3_7_2
end
