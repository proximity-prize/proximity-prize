import ProximityPrize.SubmissionLower.HighCore82258Data
import ProximityPrize.SubmissionLower.GoldBranch7N4
import ProximityPrize.SubmissionLower.SilverBase
import ProximityPrize.SubmissionLower.HighCore82258Source
import ProximityPrize.SubmissionLower.GoldBranch7
import ProximityPrize.SubmissionLower.HighCore82258Terminal

-- merged module HighCore82258Stages
section Merged_HighCore82258Stages
set_option autoImplicit true
set_option maxRecDepth 18000

section
namespace HighCore82258Stages
open Finset
open P3 (p)
open HighCore82258 (agreement cutoffCount rawWidth WidthGuard gain)
open HighCore82258 (Bank debit)
open K1_14 (Shape shapeSum triangle)
open private twice_sum_linear from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic
open private row rising level sum_rising sum_level tailSum tailSum_eq from ProximityPrize.SubmissionLower.SilverBase
private theorem agreement_cast : (agreement : ℤ) = 179886 := rfl
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
  simp only [HighCore82258.debit, P1_7.debit] at hz ⊢
  apply Int.ofNat_lt.mp
  push_cast at hz ⊢
  nlinarith only [hz, hs]
end HighCore82258Stages
end
end Merged_HighCore82258Stages

-- merged module HighCore82258StageReceipts
section Merged_HighCore82258StageReceipts
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82258Stages

open HighCore82258
open K1_14 (Shape)
open P3 (p)

private def Checks (lo : ℕ) (ss : List Stage) : Prop :=
  ∀ s ∈ ss, BankCertificate lo s.reserve 0 s.free ∧ BankCertificate lo s.reserve 1 s.moving
private theorem nil {lo : ℕ} : Checks lo [] := fun _ hs => (List.not_mem_nil hs).elim
private theorem cons {lo : ℕ} {s : Stage} {ss : List Stage}
    (hf : BankCertificate lo s.reserve 0 s.free)
    (hm : BankCertificate lo s.reserve 1 s.moving)
    (ht : Checks lo ss) : Checks lo (s::ss) :=
  List.forall_mem_cons.mpr ⟨⟨hf, hm⟩, ht⟩
set_option quotPrecheck false

local notation "bank!" kk "," ww "," zz "," dd =>
  checked (k := kk) (w := ww) (z := zz) (d := dd)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem certificates (b : Band) : Checks (start b) (stages b) := by
  cases b with
  | h2367 =>
    rw [stages]
    refine cons (bank! 106,162351,0x20ef589c40,0x7bad3e36c8) (bank! 607,386726,0x490e5bb019bc,0x50a5eaa0057db0) ?_
    refine cons (bank! 116,130155,0x16e4293354,0xbef02c57d8) (bank! 605,459326,0x7d6894a3f60c,0x7137d8c720c5a0) ?_
    refine cons (bank! 128,200417,0x5c3a768750,0x118d47335d8) (bank! 705,540590,0x304602695a60,0xbaa66a480e9db8) ?_
    refine cons (bank! 138,168221,0x29eba4fe14,0x192c82feb88) (bank! 683,230726,0x59a49a00f040,0xfb304ba224cee0) ?_
    refine cons (bank! 149,187254,0xa834a92ae8,0x23377db1a00) (bank! 729,372571,0xf92356de5480,0x166b8886a72b900) ?_
    refine cons (bank! 162,128859,0xf4a24e2498,0x30728dabb70) (bank! 891,700628,0x1bed12c4e5730,0x236fd5a55b08e68) ?_
    refine cons (bank! 176,116865,0x1125c6979e0,0x58814b322a0) (bank! 950,706650,0x3ebea8323310c,0x3c74ab52126b820) ?_
    refine cons (bank! 198,150103,0xdc56dcdf88,0xcbf901a5660) (bank! 1200,907396,0xacbc9bfc8ce90,0x948bf249e7d3de0) ?_
    refine cons (bank! 238,191549,0x214d03d17c4,0x489ceb48fb90) (bank! 1406,663472,0x320fe88476d10,0x1dd373b1fc7b0080) ?_
    refine cons (bank! 248,193149,0x476e17c1170,0xc6bcf0e8228) (bank! 1099,770075,0x61cadc94218d8,0x846f7bfd0475a6c) ?_
    refine cons (bank! 348,230961,0xc2b969342f8,0x4e83dfd741d4) (bank! 1806,602557,0x2393c2a89116c,0x45c5c2272d839e88) ?_
    refine cons (bank! 363,221916,0x13c8544943e8,0x33712240cdb08) (bank! 2023,482183,0x3fdcca9c6216d0,0x14d0b866bf57842a0) ?_
    refine cons (bank! 479,412956,0x2bfba7d88f08,0x1614c95048b38) (bank! 2224,839081,0x616619301dcda0,0x11d9f687047038f20) ?_
    refine cons (bank! 523,265750,0x6ad4770e8de0,0x59f9a402df920) (bank! 3124,830432,0xd198c6d2a9ea34,0x4bc4ebbc97b77fd14) ?_
    refine cons (bank! 832,485303,0x28d5d4e161530,0x2a2045a47994d8) (bank! 4833,1071161,0x6390c24daae7030,0x28ace08958f6057038) ?_
    refine cons (bank! 693,185656,0x7a422d080410,0x14481628d952a08) (bank! 3826,788982,0x297036ab61bfc6c,0x393aed856f240ffbec) ?_
    refine cons (bank! 1127,162708,0x257f9bf6d7690,0xc374d592dade00) (bank! 6619,522261,0x202ac1755461d688,0xc04d8b35a55552dc70) ?_
    exact nil
  | h2395 =>
    rw [stages]
    refine cons (bank! 102,149643,0x120ae359a0,0x411fa80f30) (bank! 489,466257,0xfd57570fb90,0xde9ee59c70758) ?_
    refine cons (bank! 109,144256,0x374eeb2bf0,0x673dc63448) (bank! 479,358798,0x4829c474f280,0x125049ac08c840) ?_
    refine cons (bank! 120,164387,0x31ad37dca0,0x9a59ee56f0) (bank! 535,479741,0x6dd66152350,0x1d22a475fe9f80) ?_
    refine cons (bank! 131,184518,0x45a7355a20,0xe1a14eba10) (bank! 571,395910,0x807fc0b8740,0x2aaf7b23ace09c) ?_
    refine cons (bank! 142,204649,0x7c184b9b00,0x13f4bef8700) (bank! 608,491965,0x475b049a9aa8,0x3d13efa2a2ba68) ?_
    refine cons (bank! 151,122078,0x51526ed020,0x1bbfe38b568) (bank! 725,558722,0xd29d79c7f6c,0x66d65f48a54788) ?_
    refine cons (bank! 150,245541,0x5f43c99aa4,0x2861ef827d8) (bank! 791,704868,0x6977eed2ed90,0x951555e4b9eefc) ?_
    refine cons (bank! 198,171697,0xf306f350e8,0x6de71223ae0) (bank! 966,728056,0x26562d995e1b4,0x1b00b0b4dad5bc0) ?_
    refine cons (bank! 227,191356,0x383e7e43700,0x1f3787a02a30) (bank! 1181,944929,0x41645551ed248,0x59bf0f55e1df1c8) ?_
    refine cons (bank! 307,331800,0x36df16d19d4,0x2321bc5321fc) (bank! 1321,979836,0x8f201c51e1100,0x8a798e73aa9e470) ?_
    refine cons (bank! 295,224814,0x28b5c7576c0,0x75257e460388) (bank! 1547,1221912,0x16e51ce694312c,0x15a7fd0622eb61fc) ?_
    refine cons (bank! 363,258272,0xf196889bc20,0x14aba25bd4a60) (bank! 2030,1570724,0x26d000ce3eb90c,0x44b866bce5ab7188) ?_
    refine cons (bank! 342,238929,0x5a7f94d0ab0,0x1ba86f5afd0b00) (bank! 1692,1282968,0x2d4ec0dee9a000,0x6300a6f3c8b53800) ?_
    refine cons (bank! 387,360660,0x9b8733e9578,0x30fb975b86cc30) (bank! 1720,1122741,0x1ba8f9524af258,0x147e9eeb3dd45cb90) ?_
    refine cons (bank! 741,669336,0x10b27cd68a920,0x84297fd979658) (bank! 3124,2386299,0xb683806d5d938,0x23e48582a4a1d5b98) ?_
    refine cons (bank! 884,680145,0xf0aed3d7465c,0x29bdc7b8f52178) (bank! 4819,3689082,0x8e76f03e82f1720,0xfb3d41bbfa2b552d0) ?_
    refine cons (bank! 1073,935044,0x7bd50719eddc0,0x6a293c91fdd840) (bank! 5784,4371490,0x4e20b0b3a6c41c0,0x27c859ce5723e66800) ?_
    refine cons (bank! 1444,1280487,0x15a10b287d3164,0x19d91dac5545d98) (bank! 7611,5627712,0x125d41128f26c300,0x9d8015d61153361108) ?_
    exact nil
  | h7773 =>
    rw [stages]
    refine cons (bank! 16,129276,0x91b38d0,0x2b3a4f0) (bank! 29,145376,0x6b5df5e0,0x22d5a6a0) ?_
    refine cons (bank! 30,170872,0xc84f4e18,0xee1a738) (bank! 54,269782,0x33b81f4c,0x14f083b48) ?_
    refine cons (bank! 48,243388,0xa6f64cdc,0x66957bc4) (bank! 90,461452,0x4108a6fa00,0xba22184a0) ?_
    refine cons (bank! 76,311034,0x254912c820,0x3570486a8) (bank! 142,628008,0x1864c9d3718,0x6e86722fcc) ?_
    exact nil

theorem stage_bounds (b : Band) {s : Stage} (hs : s ∈ stages b)
    {h : ℕ} (hl : start b ≤ h) (hh : h ≤ 131071) :
    (WidthGuard h s.reserve s.free.shape ∧
      debit h s.free < gain h s.reserve s.free.shape 0 ∧ s.free.shape.U < p) ∧
    (WidthGuard h s.reserve s.moving.shape ∧
      debit h s.moving < gain h s.reserve s.moving.shape 1 ∧ s.moving.shape.U < p) := by
  obtain ⟨hf,hm⟩ := certificates b s hs
  exact ⟨of_certificate hl hh hf, of_certificate hl hh hm⟩

#print axioms stage_bounds
end HighCore82258Stages
end Merged_HighCore82258StageReceipts

-- merged module HighCore82258Pairs
section Merged_HighCore82258Pairs
set_option autoImplicit true
set_option maxRecDepth 18000

section
namespace HighCore82258
noncomputable section
open FrontCore82258 (AnchorModel AnchoredFamily)
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
end HighCore82258
end


namespace HighCore82258
open FrontCore82258 (AnchorModel AnchoredFamily)
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
    HighCore82258Stages.stage_bounds b hs hl (hu'.trans (by decide))
  exact pair_of_tests src hh (by omega) hs wf sf cf wm sm

#print axioms buffered_pairs
end HighCore82258
end Merged_HighCore82258Pairs

-- merged module HighFamilyBase82180
section Merged_HighFamilyBase82180
set_option autoImplicit true
end Merged_HighFamilyBase82180

set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82258
export P1 (K I p node twist blockLength)
export FrontCore82258 (AnchorModel AnchoredFamily AdjacentChart)
abbrev t : ℕ := blockLength - agreement

theorem degree_at_height {u D Γ} (M : AnchorModel u D) (F : AnchoredFamily M Γ)
    (γ : K) (hγ : γ ∈ Γ) : (F.scalar γ).natDegree ≤ P1.k - 1 + M.overhead.toNat := by
  rcases (F.mark γ hγ).scalar_degree with h | h
  · simp [h]
  · change (F.scalar γ).natDegree ≤ P1.k - 1 + (P1.ModelAt.overhead M).toNat
    omega

def prefixFee (b : Band) : ℕ :=
  let f := fees b
  f.loss + f.point + f.lowSeed + f.lowJet + f.fixedODE + f.content

end HighCore82258
section
namespace HighCore82258
open HighCore82258 (Band agreement p blockLength)
abbrev degreeAt := P1_7.degreeAt
abbrev quotientOrder := P1_7.quotientOrder
def gap (hi : ℕ) := agreement - degreeAt hi
def scale (hi : ℕ) := agreement * gap hi
def muNum (hi : ℕ) := agreement * (blockLength - degreeAt hi)
def lambdaNum (hi : ℕ) := blockLength * gap hi
abbrev ceilRatio := P1_7.ceilRatio
abbrev singularDegree := P1_7.singularDegree
abbrev singularFee := P1_7.singularFee
def persistentFee (lo hi e v : ℕ) : ℕ :=
  let t := lambdaNum hi * quotientOrder lo
  let a := muNum hi + 2 * t * (e - 1)
  let b := 2 * hi * muNum hi + 2 * t * v
  ceilRatio (e * b^2 + 2 * v * a * b) ((scale hi)^2) + e
def properFee (lo hi e v : ℕ) : ℕ :=
  let bc := quotientOrder lo + 1
  let ac := 1 + bc * (e - 1)
  let cc := bc * v + 2 * hi
  let bn := lambdaNum hi * quotientOrder lo
  let an := muNum hi + bn * (e - 1)
  let cn := bn * v + 2 * hi * muNum hi
  ceilRatio (e * cc * cn +
    v * (cn * ((2*e-2)*bc + ac) + cc * ((2*e-2)*bn + an)) +
    v^2 * ((ac - 2*bc) * bn + an * bc)) (scale hi)
def flatFee (hi v : ℕ) : ℕ := ceilRatio (HighCore82258.t * (p+1) * v) (gap hi)
def tangentFee (lo hi e v : ℕ) : ℕ := properFee lo hi e v + flatFee hi v + e
def wholePrice (lo hi e v : ℕ) : ℕ :=
  if v = 0 then e else singularFee e v +
    if e ≤ 2 then persistentFee lo hi e v else tangentFee lo hi e v
structure GradeOK (lo hi fullU cap e : ℕ) (g : Grade) : Prop where
  sub : g.slots ≤ fullU
  separant : singularDegree e g.seedCap < p
  flat : e * degreeAt hi + g.seedCap < p
  fee : wholePrice lo hi e g.seedCap ≤ cap
def AllGrades (lo hi fullU cap : ℕ) : ℕ → List Grade → Prop
  | _, [] => True
  | e, g :: gs => GradeOK lo hi fullU cap e g ∧ AllGrades lo hi fullU cap (e+1) gs
theorem get_grade {lo hi fullU cap : ℕ} (gs : List Grade) (e : ℕ)
    (hall : AllGrades lo hi fullU cap e gs) (i : Fin gs.length) :
    GradeOK lo hi fullU cap (i.val + e) (gs.get i) := by
  induction gs generalizing e with
  | nil => exact Fin.elim0 i
  | cons g gs ih =>
    rcases i with ⟨_ | j, hj⟩
    · change GradeOK lo hi fullU cap (0+e) g
      simpa only [Nat.zero_add] using hall.1
    · have h := ih (e+1) hall.2 ⟨j, by simpa using hj⟩
      simpa only [List.get_cons_succ, Nat.succ_add, Nat.add_succ] using h
theorem sheets_le_price (lo hi e v : ℕ) : e ≤ wholePrice lo hi e v := by
  unfold wholePrice
  split
  · exact le_rfl
  · split
    · dsimp only [persistentFee]
      omega
    · unfold tangentFee
      omega
end HighCore82258
end
section
namespace HighCore82258
open HighCore82258 (K Band)
structure PrefixBooks (b : Band) where
  loss : Finset K
  point : Finset K
  lowSeed : Finset K
  lowJet : Finset K
  fixedODE : Finset K
  content : Finset K
  loss_le : loss.card ≤ (fees b).loss
  point_le : point.card ≤ (fees b).point
  lowSeed_le : lowSeed.card ≤ (fees b).lowSeed
  lowJet_le : lowJet.card ≤ (fees b).lowJet
  fixedODE_le : fixedODE.card ≤ (fees b).fixedODE
  content_le : content.card ≤ (fees b).content
noncomputable def PrefixBooks.union {b} (B : PrefixBooks b) : Finset K := by
  classical exact B.loss ∪ B.point ∪ B.lowSeed ∪ B.lowJet ∪ B.fixedODE ∪ B.content
private theorem union_le {A B : Finset K} {a b : ℕ} (ha : A.card ≤ a) (hb : B.card ≤ b) :
    (A ∪ B).card ≤ a+b := (Finset.card_union_le _ _).trans (Nat.add_le_add ha hb)
theorem PrefixBooks.card_union {b} (B : PrefixBooks b) : B.union.card ≤ (prefixFee b) := by
  exact union_le (union_le (union_le (union_le (union_le B.loss_le B.point_le)
    B.lowSeed_le) B.lowJet_le) B.fixedODE_le) B.content_le
end HighCore82258
end
section
namespace HighCore82258
noncomputable section
open Polynomial
open HighCore82258 (Band AnchorModel AnchoredFamily K p node twist agreement)
open K1_14 (L FX Seeds Equation Shape Jet Banks SeedBound liftPoly graphEval atX atMark
  jetAt triangle slots shapeSum)
open K1_14_3 (Surface Parent)
open scoped BigOperators
def BankPass (rows : Banks) (s : Shape) (q : Surface) : Prop :=
  ∀ P ∈ rows s (fullCutoff s), P ∈ q.asIdeal
def PairPass {h rows s} (pair : BufferedPair h rows s) (q : Surface) : Prop :=
  BankPass rows s.free.shape q ∧ BankPass rows s.moving.shape q ∧
    K1_14_3R.compatible pair.free pair.moving q
def MarkOn {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (q : Surface) (γ : K) : Prop :=
  q.asIdeal ≤ RingHom.ker
    (eval₂RingHom (eval₂RingHom (graphEval (M.label γ)) (atX (F.scalar γ)))
      (atX (F.scalar γ).derivative))
structure PrefixInventory (b : Band) {u del} (M : AnchorModel u del) {Γ}
    (F : AnchoredFamily M Γ) {rows : Banks} (pairs : Pairs b M.overhead.toNat rows) where
  books : PrefixBooks b
  parents : Finset Surface
  geometric : ∀ q ∈ parents, Parent q
  stage_pass : ∀ q ∈ parents, ∀ s (hs : s ∈ stages b), 0 < s.reserve →
    PairPass (pairs s hs) q
  terminal_pass : ∀ q ∈ parents, BankPass rows (terminal b).shape q
  covers : ∀ γ ∈ Γ, γ ∈ books.union ∨ ∃ q ∈ parents, MarkOn M F q γ
def curveUnit (hi g : ℕ) : ℚ :=
  let d := degreeAt hi
  (2*(g : ℚ)-1) * (1 + 2*((HighCore82258.blockLength : ℚ)/agreement)*d) +
    ((HighCore82258.blockLength - d : ℕ) : ℚ) / gap hi
def CurveTariff (b : Band) {u del} (M : AnchorModel u del) {Γ}
    (F : AnchoredFamily M Γ) : Prop :=
  ∀ T ⊆ Γ, ∀ J g H, 0 < g → g ≤ 80 →
    K1_14_2.SmallRootCurve J g H →
    Module.finrank K1_14_2.SeedField (K1_14_2.RootSeedSection J) < p →
    (∀ γ ∈ T, K1_14_2.OnRoot J (M.label γ) (F.scalar γ)) →
    (T.card : ℚ) ≤ curveUnit (finish b) g * H + g
def contactPower (h : ℕ) (s : Shape) (W : ℕ) := 1 + (fullCutoff s - W)/(2*h)
structure TerminalTrace (h : ℕ) (t : Bank) (rows : Banks) (f : Equation) : Prop where
  floor_bound : RankFloor h t rows
  shape : ∀ W, ∀ P ∈ rows t.shape W, K1_14_3.RowCaps P t.shape
  leading : K1_14_3.LeadingFilter h rows t.shape
  divides : ∀ W < t.shape.m * agreement, ∀ P ∈ rows t.shape W, P ≠ 0 →
    f ^ (contactPower h t.shape W - P.natDegree) ∣ P.leadingCoeff
abbrev Reduced := P1_7.Reduced
abbrev regularRoot := P1_7.regularRoot
def RegularCount {u del} (M : AnchorModel u del) {Γ}
    (F : AnchoredFamily M Γ) (f : Equation) (fee : ℕ) : Prop :=
  ∀ T ⊆ Γ, (∀ γ ∈ T, regularRoot f (M.label γ) (F.scalar γ)) → T.card ≤ fee
end
end HighCore82258
end
section
namespace HighCore82258
open HighCore82258 (Band agreement p)
theorem grades_checked (b : Band) :
    AllGrades (start b) (finish b) (terminal b).shape.U (retainedCap b) 1 (grades b) := by
  cases b <;>
    repeat' refine And.intro (GradeOK.mk (by decide) (by decide) (by decide) (by decide +kernel)) ?_
  all_goals trivial
theorem grade_checked (b : Band) (i : Fin (grades b).length) :
    GradeOK (start b) (finish b) (terminal b).shape.U (retainedCap b) (i.val+1) ((grades b).get i) :=
  get_grade _ _ (grades_checked b) i
theorem terminal_guards (b : Band) :
    0 < (start b) ∧ (finish b) ≤ 33443 ∧ 0 < (terminal b).shape.m * agreement ∧
    (terminal b).shape.m * agreement < p ∧
    (terminal b).shape.B * (131071-(start b)) ≤ (terminal b).shape.m*agreement := by
  cases b <;> decide +kernel
end HighCore82258
end
section
namespace HighCore82258
noncomputable section
open HighCore82258 (K I node p agreement blockLength AnchorModel AnchoredFamily)
open K1_14_2_4 (taylorPower ordinateBound)
open P1_7_3 (persistentNodes hits_persistent section_bounds regular_chart persistent_taylor)
open Finset Polynomial ProximityPrize.Benchmark
structure FixedWord (w : I → K) (U : Finset K) (s : K → K[X]) (d : ℕ) : Prop where
  distinct : Set.InjOn s (U : Set K)
  degree : ∀ γ ∈ U, (s γ).natDegree ≤ d
  hits : ∀ γ ∈ U, ∃ B : Finset I, agreement ≤ B.card ∧ ∀ i ∈ B, (s γ).eval (node i) = w i
theorem persistent_card_le {w U s d} (hw : FixedWord w U s d) (hU : 1 < U.card) :
    (persistentNodes w U s).card ≤ d := by
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hU
  let P := s a - s b
  have hp : P ≠ 0 := sub_ne_zero.mpr fun eq => hab (hw.distinct ha hb eq)
  refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective P hp _ ?_).trans
    ((natDegree_sub_le _ _).trans (max_le (hw.degree a ha) (hw.degree b hb)))
  intro i hi
  change ((s a) - (s b)).eval (node i) = 0
  rw [Polynomial.eval_sub, hits_persistent ha hi, hits_persistent hb hi, sub_self]
theorem section_incidence {w U s d} (hw : FixedWord w U s d) (D : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ U, (s γ).eval (node i) ≠ w i) →
      (U.filter fun γ => (s γ).eval (node i) = w i).card ≤ D) :
    (agreement - (persistentNodes w U s).card) * U.card ≤
      (blockLength - (persistentNodes w U s).card) * D := by
  classical
  let sites := persistentNodes w U s
  let nodes : Finset I := univ \ sites
  let hits (γ : K) := nodes.filter fun i => (s γ).eval (node i) = w i
  let occ (i : I) := U.filter fun γ => (s γ).eval (node i) = w i
  have hhit (γ : K) (hγ : γ ∈ U) : agreement - sites.card ≤ (hits γ).card := by
    obtain ⟨B, hB, hvals⟩ := hw.hits γ hγ
    let good : Finset I := univ.filter fun i => (s γ).eval (node i) = w i
    have hgood : agreement ≤ good.card :=
      hB.trans (card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _, hvals i hi⟩)
    have hZG : sites ⊆ good := fun i hi => mem_filter.mpr ⟨mem_univ _, hits_persistent hγ hi⟩
    have heq : hits γ = good \ sites := by
      ext i
      simp only [hits, nodes, good, mem_filter, mem_sdiff, mem_univ, true_and]
      exact and_comm
    rw [heq, card_sdiff_of_subset hZG]
    exact Nat.sub_le_sub_right hgood _
  have hnodes : nodes.card = blockLength - sites.card := by
    rw [card_sdiff_of_subset (subset_univ sites), card_univ, IRSProfile.card_index]
  calc
    _ = ∑ γ ∈ U, (agreement - sites.card) := by rw [sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ γ ∈ U, (hits γ).card := sum_le_sum hhit
    _ = ∑ i ∈ nodes, (occ i).card := by simp only [hits, occ, card_filter]; rw [sum_comm]
    _ ≤ ∑ _i ∈ nodes, D := by
      apply sum_le_sum
      intro i hi
      apply hsection i
      by_contra! h
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, h⟩)
    _ = _ := by rw [sum_const, smul_eq_mul, hnodes]
private def rho (s : ℕ) : ℚ :=
  ((blockLength - s : ℕ) : ℚ) / ((agreement - s : ℕ) : ℚ)
private abbrev density : ℚ := (blockLength : ℚ) / agreement
private theorem weights {s d : ℕ} (hs : s ≤ d) (hd : d < agreement)
    (haux : rho d ≤ density * d) :
    rho s ≤ rho d ∧ rho s * (max 1 (d-s) : ℕ) ≤ density * d := by
  have hAN : agreement ≤ blockLength := by decide
  have hsA := hs.trans_lt hd
  have hdN := hd.le.trans hAN
  have hsN := hs.trans hdN
  have hAs : (0 : ℚ) < (agreement : ℚ) - s := sub_pos.mpr (by exact_mod_cast hsA)
  have hAd : (0 : ℚ) < (agreement : ℚ) - d := sub_pos.mpr (by exact_mod_cast hd)
  have hmain : rho s ≤ rho d := by
    unfold rho
    rw [Nat.cast_sub hsN, Nat.cast_sub hsA.le, Nat.cast_sub hdN, Nat.cast_sub hd.le]
    apply (div_le_div_iff₀ hAs hAd).mpr
    have h := mul_nonneg (sub_nonneg.mpr (show (s : ℚ) ≤ d by exact_mod_cast hs))
      (sub_nonneg.mpr (show (agreement : ℚ) ≤ blockLength by exact_mod_cast hAN))
    nlinarith only [h]
  refine ⟨hmain, ?_⟩
  by_cases heq : s = d
  · subst s
    simpa using haux
  have hpos : 1 ≤ d - s := by omega
  rw [max_eq_right hpos]
  have hden : (0 : ℚ) < (agreement : ℚ) := by exact_mod_cast (by decide : 0 < agreement)
  have hfrac : ((d-s : ℕ) : ℚ) / ((agreement-s : ℕ) : ℚ) ≤ (d : ℚ) / agreement := by
    rw [Nat.cast_sub hs, Nat.cast_sub hsA.le]
    apply (div_le_div_iff₀ hAs hden).mpr
    have h := mul_nonneg (Nat.cast_nonneg s : (0 : ℚ) ≤ s) hAd.le
    nlinarith only [h]
  calc
    _ = ((blockLength-s : ℕ) : ℚ) * (((d-s : ℕ) : ℚ) / ((agreement-s : ℕ) : ℚ)) := by
      unfold rho
      ring
    _ ≤ (blockLength : ℚ) * ((d : ℚ) / agreement) :=
      mul_le_mul (by exact_mod_cast Nat.sub_le blockLength s) hfrac (by positivity) (by positivity)
    _ = density * d := by ring
private theorem rho_at_endpoint {d : ℕ} (hl : 131071 ≤ d) (hh : d ≤ 164514) :
    rho d ≤ density * d := by
  have hdA : d < agreement := hh.trans_lt (by decide)
  have hdN : d ≤ blockLength := hh.trans (by decide)
  have hrho : rho d ≤ 17 := by
    unfold rho
    have hp : (0 : ℚ) < ((agreement - d : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hdA
    apply (div_le_iff₀ hp).mpr
    rw [Nat.cast_sub hdN, Nat.cast_sub hdA.le]
    change (262144 : ℚ) - d ≤ 17 * ((179886 : ℚ) - d)
    have hQ : (d : ℚ) ≤ 164514 := by exact_mod_cast hh
    linarith only [hQ]
  have hDensity : 1 ≤ density := by
    apply (le_div_iff₀ (show (0 : ℚ) < (agreement : ℚ) by positivity)).mpr
    rw [one_mul]
    exact_mod_cast (by decide : agreement ≤ blockLength)
  exact hrho.trans (calc
    (17 : ℚ) ≤ (d : ℚ) := by exact_mod_cast (show 17 ≤ d by omega)
    _ = 1 * (d : ℚ) := (one_mul _).symm
    _ ≤ density * d := mul_le_mul_of_nonneg_right hDensity (Nat.cast_nonneg _))
private theorem taylorPower_cast {g : ℕ} (hg : 0 < g) :
    (taylorPower g : ℚ) = 2 * (g : ℚ) - 1 := by
  unfold taylorPower
  rw [Nat.cast_sub (by omega)]
  push_cast
  rfl
private theorem regular_count {n g H d : ℕ} {U : Finset K} {s : K → Polynomial K} {w}
    (A : K1_14_2_4.RegularChart U s g H n) (hw : FixedWord w U s d)
    (hg : 0 < g) (hl : 131071 ≤ d) (hh : d ≤ 164514) :
    (U.card : ℚ) ≤ (2 * density * d * (taylorPower g : ℚ) + rho d) * H + 1 := by
  have hbound : 0 ≤ (2 * density * d * (taylorPower g : ℚ) + rho d) * (H : ℚ) := by
    unfold rho
    positivity
  by_cases hc : U.card ≤ 1
  · have h : (U.card : ℚ) ≤ 1 := by exact_mod_cast hc
    linarith only [h, hbound]
  let sites := persistentNodes w U s
  let t := max 1 (d-sites.card)
  have hd : d < agreement := hh.trans_lt (by decide)
  have hs : sites.card ≤ d := persistent_card_le hw (by omega)
  have ht : 0 < t := (by decide : 0 < 1).trans_le (le_max_left _ _)
  have htp : t < p := (max_le (by omega : 1 ≤ d) (Nat.sub_le _ _)).trans_lt
    (hh.trans_lt (by decide))
  have hdt : d ≤ sites.card + t := by
    have h := le_max_right 1 (d-sites.card)
    omega
  obtain ⟨C, hreconstruct⟩ := persistent_taylor sites w hdt htp hg A.equation A.equation_degree
  let D := taylorPower t * (g * H) + ordinateBound t g * H
  have hsection := section_bounds (w := w) A ht hw.distinct C fun γ hγ =>
    hreconstruct _ _ (hw.degree γ hγ) (fun _ hi => hits_persistent hγ hi) (A.root γ hγ) (A.simple γ hγ)
  have hinc : ((agreement - sites.card : ℕ) : ℚ) * U.card ≤ ((blockLength - sites.card : ℕ) : ℚ) * D := by
    exact_mod_cast section_incidence hw D hsection
  have hden : (0 : ℚ) < ((agreement - sites.card : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt hd)
  have hcard : (U.card : ℚ) ≤ rho sites.card * (D : ℚ) := by
    rw [rho, div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).mpr
    calc
      _ = ((agreement - sites.card : ℕ) : ℚ) * U.card := mul_comm _ _
      _ ≤ _ := hinc
  obtain ⟨hρ, hρt⟩ := weights hs hd (rho_at_endpoint hl hh)
  have hρb : rho sites.card * (taylorPower t : ℚ) ≤ 2 * density * d := by
    have hb : (taylorPower t : ℚ) ≤ 2 * (t : ℚ) := by
      exact_mod_cast (Nat.sub_le (2*t) 1 : taylorPower t ≤ 2*t)
    have hρ0 : 0 ≤ rho sites.card := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have h := mul_le_mul_of_nonneg_left hb hρ0
    nlinarith only [h, hρt]
  have hsum : g + (g - 1) = taylorPower g := by unfold taylorPower; omega
  have hD : D = (taylorPower t * taylorPower g + 1) * H := by
    rw [← hsum]
    dsimp [D, ordinateBound]
    ring
  refine hcard.trans (le_add_of_le_of_nonneg ?_ zero_le_one)
  calc
    _ = (rho sites.card * (taylorPower t : ℚ) * (taylorPower g : ℚ) + rho sites.card) * H := by
      rw [hD]
      push_cast
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_right hρb (Nat.cast_nonneg _)) hρ) (Nat.cast_nonneg _)
theorem persistent_curve {b : HighCore82258.Band} {u del} (M : AnchorModel u del)
    {Γ} (F : AnchoredFamily M Γ) (hband : InBand b M.overhead) : CurveTariff b M F := by
  intro T hT J g H hg hgLimit hcurve _hseed hmarks
  have hlabel : Set.InjOn M.label (T : Set K) := by
    intro γ _ η _ h
    exact sub_left_inj.mp h
  obtain ⟨U, hU, hexc, n, ⟨A⟩⟩ := regular_chart T M.label F.scalar J g H hg
    (hgLimit.trans_lt (by decide)) hcurve hlabel hmarks
  let d := degreeAt (finish b)
  have hw : FixedWord M.word U F.scalar d := by
    refine ⟨F.distinct.mono (hU.trans hT), ?_, ?_⟩
    · intro γ hγ
      rcases (F.mark γ (hT (hU hγ))).scalar_degree with hz | hm
      · simp [hz]
      · have hd : ((F.scalar γ).natDegree : ℤ) ≤ (d : ℤ) := by
          change ((F.scalar γ).natDegree : ℤ) ≤ 131071 + M.overhead at hm
          dsimp [d, degreeAt, P1_7.degreeAt]
          have h := hband.2
          omega
        exact_mod_cast hd
    · intro γ hγ
      let m := F.mark γ (hT (hU hγ))
      exact ⟨m.bad.support, m.bad.agreement, m.scalar_hits⟩
  have hlo : 131071 ≤ d := Nat.le_add_right _ _
  have hhi : d ≤ 164514 := by
    have h := (HighCore82258.terminal_guards b).2.1
    dsimp [d, degreeAt, P1_7.degreeAt]
    omega
  have hregular := regular_count A hw hg hlo hhi
  have hgQ : (1 : ℚ) ≤ g := by exact_mod_cast hg
  have hexcQ : ((T \ U).card : ℚ) ≤ (taylorPower g : ℚ) * H := by exact_mod_cast hexc
  calc
    (T.card : ℚ) = ((T \ U).card : ℚ) + (U.card : ℚ) := by
      exact_mod_cast (card_sdiff_add_card_eq_card hU).symm
    _ ≤ (taylorPower g : ℚ) * H + ((2 * density * d * (taylorPower g : ℚ) + rho d) * H + 1) :=
      add_le_add hexcQ hregular
    _ ≤ (taylorPower g : ℚ) * H + ((2 * density * d * (taylorPower g : ℚ) + rho d) * H + g) :=
      add_le_add le_rfl (add_le_add le_rfl hgQ)
    _ = curveUnit (finish b) g * H + g := by
      rw [taylorPower_cast hg]
      unfold curveUnit gap rho
      dsimp only [d]
      ring
end
end HighCore82258
end
section
namespace HighCore82258
noncomputable section
open Polynomial Finset MvPolynomial ProximityPrize.Benchmark
open scoped BigOperators
open HighCore82258 (K I node agreement blockLength)
open K1_14 (FX)
open K1_14_6 (Biform ClosedField rootPoint)
open P1_7_7 (point slice slice_subset slice_on point_injective boxMap BoxRing
  localOrd localSeed ShortCharts WeightedCut CurveScale)
open private zero_dim_count common common_agrees from ProximityPrize.SubmissionLower.UpperBranch7
open private card_le_sum_cover from ProximityPrize.SubmissionLower.Fast055
open private eval_extend extend_mem from ProximityPrize.SubmissionLower.Fast055
private theorem common_bound {word T S d} (hword : FixedWord word T S d)
    {U : Finset K} (hU : U ⊆ T) (hsize : 1 < U.card) :
    (common word U S).card ≤ d := by
  obtain ⟨γ, hγ, η, hη, hne⟩ := one_lt_card.mp hsize
  let P := S γ - S η
  have hp : P ≠ 0 := sub_ne_zero.mpr fun he => hne (hword.distinct (hU hγ) (hU hη) he)
  refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective
    P hp _ ?_).trans ((natDegree_sub_le _ _).trans (max_le (hword.degree γ (hU hγ))
      (hword.degree η (hU hη))))
  intro j hj
  change ((S γ) - (S η)).eval (node j) = 0
  rw [Polynomial.eval_sub, common_agrees hγ hj, common_agrees hη hj, sub_self]
private theorem residual_incidence {word T S d} (hword : FixedWord word T S d)
    {U : Finset K} (hU : U ⊆ T) (cap : ℚ)
    (hcap : ∀ j ∉ common word U S, ((U.filter fun γ => (S γ).eval (node j) = word j).card : ℚ) ≤ cap) :
    ((agreement - (common word U S).card : ℕ) : ℚ) * U.card ≤
      ((blockLength - (common word U S).card : ℕ) : ℚ) * cap := by
  classical
  let sites := common word U S
  let J : Finset I := univ \ sites
  let rel (γ : K) (j : I) := (S γ).eval (node j) = word j
  have hJ : J.card = blockLength - sites.card := by
    rw [card_sdiff_of_subset (subset_univ sites), card_univ, IRSProfile.card_index]
  have hrows (γ : K) (hγ : γ ∈ U) :
      ((agreement - sites.card : ℕ) : ℚ) ≤ (J.bipartiteAbove rel γ).card := by
    obtain ⟨H, hH, heval⟩ := hword.hits γ (hU hγ)
    have hcover : H \ sites ⊆ J.bipartiteAbove rel γ := fun j hj =>
      mem_filter.mpr
        ⟨mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp hj).2⟩, heval j (mem_sdiff.mp hj).1⟩
    exact_mod_cast (Nat.sub_le_sub_right hH sites.card).trans
      ((le_card_sdiff _ _).trans (card_le_card hcover))
  have hcols (j : I) (hj : j ∈ J) :
      ((U.bipartiteBelow rel j).card : ℚ) ≤ cap := hcap j (mem_sdiff.mp hj).2
  have he := card_nsmul_le_card_nsmul rel hrows hcols
  rw [nsmul_eq_mul, nsmul_eq_mul, hJ, mul_comm (U.card : ℚ)] at he
  exact he
structure Invoice (d w e v a b D : ℕ) : Prop where
  scale_pos : 0 < D
  ordinate : D ≤ a
  seed : D ≤ b
  degree : d < agreement
  fits : ∀ s ≤ d, D * (blockLength-s) * localOrd d w e s ≤ (agreement-s) * a ∧
    D * (blockLength-s) * localSeed d w v s ≤ (agreement-s) * b
private theorem count_step {d w e v a b D : ℕ} (hInv : Invoice d w e v a b D)
    (hcut : WeightedCut) {word T z S} (hword : FixedWord word T S d)
    (hchart : ShortCharts d w e v word T z S)
    {U : Finset K} (hU : U ⊆ T) (hsize : 1 < U.card) (P : Ideal (BoxRing a b))
    (hP : P.IsPrime) (hbase : RingHom.ker (boxMap a b) ≤ P)
    (hdim : 0 < (affineHilbertPolynomial P).natDegree)
    (hpoints : ∀ γ ∈ U, point a b z S γ ∈ zeroLocus ClosedField P)
    {c : ℚ} (hc : 0 < c)
    (hchildren : ∀ (V : Finset K), V ⊆ U → ∀ (Q : Ideal (BoxRing a b)), Q.IsPrime →
      RingHom.ker (boxMap a b) ≤ Q →
      (affineHilbertPolynomial Q).natDegree + 1 = (affineHilbertPolynomial P).natDegree →
      (∀ γ ∈ V, point a b z S γ ∈ zeroLocus ClosedField Q) →
      c * V.card ≤ affineDegree Q) :
    (D : ℚ) * c * U.card ≤ affineDegree P := by
  classical
  let sites := common word U S
  let s := sites.card
  let r := D * (blockLength-s)
  let t := agreement-s
  have hs : s ≤ d := common_bound hword hU hsize
  have ht : 0 < t := Nat.sub_pos_of_lt (hs.trans_lt hInv.degree)
  have hn : 0 < blockLength-s :=
    Nat.sub_pos_of_lt (hs.trans_lt (hInv.degree.trans (by decide)))
  have hr : 0 < r := Nat.mul_pos hInv.scale_pos hn
  have ha := hInv.scale_pos.trans_le hInv.ordinate
  have hb := hInv.scale_pos.trans_le hInv.seed
  let : P.IsPrime := hP
  obtain ⟨cut, hcut_box, hcut_eval⟩ := hchart U hU sites hs
    (fun _ hγ _ hj => common_agrees hγ hj)
  let ι := algebraMap FX ClosedField
  have hsection (j : I) (hj : j ∉ sites) :
      (r : ℚ) * (c * ((U.filter fun γ => (S γ).eval (node j) = word j).card : ℚ)) ≤
        (t : ℚ) * affineDegree P := by
    let V := U.filter fun γ => (S γ).eval (node j) = word j
    obtain ⟨q, hq⟩ := bidegreeMap_surjective (R := ClosedField) ha hb (MvPolynomial.map ι (cut j))
    have heval (γ : K) (hγ : γ ∈ U) :
        aeval (point a b z S γ) q = 0 ↔ (S γ).eval (node j) = word j := by
      rw [point, aeval_monomialPoint, ← bidegreeMap_eq_monomialMap, hq]
      change MvPolynomial.eval (ι ∘ rootPoint (z γ) (S γ)) (MvPolynomial.map ι (cut j)) = 0 ↔ _
      rw [eval_extend, ← map_zero ι, ι.injective.eq_iff]
      exact hcut_eval γ hγ j
    have hproper : q ∉ P := by
      intro hqP
      apply hj
      exact mem_filter.mpr ⟨mem_univ _, fun γ hγ => (heval γ hγ).mp (hpoints γ hγ q hqP)⟩
    let Qs := (P ⊔ Ideal.span {q}).minimalPrimesFinset
    have hdeg : (r : ℚ) * (∑ Q ∈ Qs, affineDegree Q) ≤ (t : ℚ) * affineDegree P :=
      hcut a b _ _ r t ha hb hr ht (hInv.fits s hs).1 (hInv.fits s hs).2
        P hP hbase hdim q hproper (by rw [hq]; exact extend_mem (hcut_box j))
    have hcover : V.card ≤ ∑ Q ∈ Qs, (slice z S V Q).card := by
      apply card_le_sum_cover
      intro γ hγ
      obtain ⟨hγU, hv⟩ := mem_filter.mp hγ
      have hγP : point a b z S γ ∈ zeroLocus ClosedField (P ⊔ Ideal.span {q}) :=
        mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hpoints γ hγU, (heval γ hγU).mpr hv⟩
      obtain ⟨Q, hQ, hγQ⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus _ 1 _ hγP (by simp)
      exact ⟨Q, Ideal.mem_minimalPrimesFinset.mpr (Ideal.mem_retainedMinimalPrimes.mp hQ).1,
        mem_filter.mpr ⟨hγ, hγQ⟩⟩
    have hparts (Q : Ideal (BoxRing a b)) (hQ : Q ∈ Qs) :
        c * ((slice z S V Q).card : ℚ) ≤ affineDegree Q := by
      have hmin := Ideal.mem_minimalPrimesFinset.mp hQ
      exact hchildren _ ((slice_subset Q).trans (filter_subset _ _)) Q hmin.isPrime
        (hbase.trans (le_sup_left.trans hmin.le))
        (principalCut_natDegree_affineHilbertPolynomial_add_one hproper hmin)
        (fun _ hγ => slice_on Q hγ)
    have hcoverQ : (V.card : ℚ) ≤ ∑ Q ∈ Qs, ((slice z S V Q).card : ℚ) := by
      exact_mod_cast hcover
    have hsum : c * (V.card : ℚ) ≤ ∑ Q ∈ Qs, affineDegree Q := by
      refine (mul_le_mul_of_nonneg_left hcoverQ hc.le).trans ?_
      rw [mul_sum]
      exact sum_le_sum hparts
    exact (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg r)).trans hdeg
  let cap : ℚ := (t : ℚ) * affineDegree P / ((r : ℚ) * c)
  have hrc : 0 < (r : ℚ) * c := mul_pos (Nat.cast_pos.mpr hr) hc
  have hinc := residual_incidence hword hU cap (fun j hj => by
    apply (le_div_iff₀ hrc).mpr
    calc
      _ = (r : ℚ) * (c * ((U.filter fun γ => (S γ).eval (node j) = word j).card : ℚ)) := by ring
      _ ≤ _ := hsection j hj)
  change (t : ℚ) * U.card ≤ ((blockLength-s : ℕ) : ℚ) * cap at hinc
  have hnQ : (0 : ℚ) < ((blockLength-s : ℕ) : ℚ) := Nat.cast_pos.mpr hn
  have htQ : (0 : ℚ) < (t : ℚ) := Nat.cast_pos.mpr ht
  apply le_of_mul_le_mul_left _ (mul_pos hnQ htQ)
  calc
    _ = ((r : ℚ) * c) * ((t : ℚ) * U.card) := by simp only [r, Nat.cast_mul]; ring
    _ ≤ ((r : ℚ) * c) * (((blockLength-s : ℕ) : ℚ) * cap) :=
      mul_le_mul_of_nonneg_left hinc hrc.le
    _ = _ := by dsimp only [cap]; field_simp [hrc.ne']
theorem count_cover {d w e v a b D : ℕ} (hInv : Invoice d w e v a b D)
    (hcut : WeightedCut) (hscale : CurveScale) {word T z S} (hword : FixedWord word T S d)
    (hchart : ShortCharts d w e v word T z S) (hz : Set.InjOn z (T : Set K))
    (Ps : Finset (Ideal (BoxRing a b)))
    (hPs : ∀ P ∈ Ps, P.IsPrime ∧ RingHom.ker (boxMap a b) ≤ P ∧
      (affineHilbertPolynomial P).natDegree = 2)
    (hcover : ∀ γ ∈ T, ∃ P ∈ Ps, point a b z S γ ∈ zeroLocus ClosedField P) :
    (D : ℚ)^2 * T.card ≤ (∑ P ∈ Ps, affineDegree P) + (D : ℚ)^2 * Ps.card := by
  classical
  have hinj := point_injective (hInv.scale_pos.trans_le hInv.ordinate)
    (hInv.scale_pos.trans_le hInv.seed) (S := S) hz
  have curve {U : Finset K} (hU : U ⊆ T) (P : Ideal (BoxRing a b))
      (hP : P.IsPrime) (hbase : RingHom.ker (boxMap a b) ≤ P)
      (hdim : (affineHilbertPolynomial P).natDegree = 1)
      (hpoints : ∀ γ ∈ U, point a b z S γ ∈ zeroLocus ClosedField P) :
      (D : ℚ) * U.card ≤ affineDegree P := by
    by_cases hsize : 1 < U.card
    · simpa only [mul_one] using
        count_step hInv hcut hword hchart hU hsize P hP hbase (by omega) hpoints
          (by norm_num : (0 : ℚ) < 1) (fun V hv Q _ _ hdimQ hpointQ => by
            rw [one_mul]
            exact zero_dim_count (hv.trans hU) hinj Q (by omega) hpointQ)
    · have hu : (U.card : ℚ) ≤ 1 := by exact_mod_cast (show U.card ≤ 1 by omega)
      calc
        _ ≤ (D : ℚ) * 1 := mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg D)
        _ ≤ affineDegree P := by
          rw [mul_one]
          exact hscale a b D hInv.scale_pos hInv.ordinate hInv.seed P hP hbase hdim
  have surface (P : Ideal (BoxRing a b)) (hP : P ∈ Ps) :
      (D : ℚ)^2 * ((slice z S T P).card : ℚ) ≤ affineDegree P + (D : ℚ)^2 := by
    obtain ⟨hp, hk, hd⟩ := hPs P hP
    by_cases hsize : 1 < (slice z S T P).card
    · rw [pow_two]
      exact (count_step hInv hcut hword hchart (slice_subset P) hsize P hp hk (by omega)
        (fun _ hγ => slice_on P hγ) (Nat.cast_pos.mpr hInv.scale_pos)
        (fun V hv Q hQ hQk hQd hQV => curve (hv.trans (slice_subset P)) Q hQ hQk (by omega) hQV)).trans
          (le_add_of_nonneg_right (by positivity))
    · have hu : ((slice z S T P).card : ℚ) ≤ 1 := by
        exact_mod_cast (show (slice z S T P).card ≤ 1 by omega)
      calc
        _ ≤ (D : ℚ)^2 * 1 := mul_le_mul_of_nonneg_left hu (by positivity)
        _ ≤ _ := by rw [mul_one]; exact le_add_of_nonneg_left (affineDegree_nonneg P)
  have hsum : T.card ≤ ∑ P ∈ Ps, (slice z S T P).card := by
    apply card_le_sum_cover
    intro γ hγ
    obtain ⟨P, hP, hγP⟩ := hcover γ hγ
    exact ⟨P, hP, mem_filter.mpr ⟨hγ, hγP⟩⟩
  have hsumQ : (T.card : ℚ) ≤ ∑ P ∈ Ps, ((slice z S T P).card : ℚ) := by exact_mod_cast hsum
  calc
    _ ≤ (D : ℚ)^2 * ∑ P ∈ Ps, ((slice z S T P).card : ℚ) :=
      mul_le_mul_of_nonneg_left hsumQ (by positivity)
    _ ≤ ∑ P ∈ Ps, (affineDegree P + (D : ℚ)^2) := by
      rw [mul_sum]
      exact sum_le_sum surface
    _ = _ := by rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_comm (Ps.card : ℚ)]
end
end HighCore82258
end
section
namespace HighCore82258
noncomputable section
open Polynomial
open HighCore82258 (Band AnchorModel AnchoredFamily agreement p)
open K1_14 (Banks Jet Equation SeedBound)
open K1_14_3 (Surface Parent ProjectedProduct OrderAt)
open K1_14_4 (seedDegree seedDegree_le_iff)
theorem tested_spec (b : Band) (x : Test b) :
    Listed b (tested b x) ∧ (tested b x).shape.m = (terminal b).shape.m ∧
    (tested b x).shape.B = (terminal b).shape.B ∧ (tested b x).shape.J = (terminal b).shape.J ∧
    (tested b x).shape.U ≤ (terminal b).shape.U := by
  cases x with
  | none => exact ⟨Or.inl rfl, rfl, rfl, rfl, le_rfl⟩
  | some i => exact ⟨Or.inr (Or.inr ⟨i, rfl⟩), rfl, rfl, rfl, (grade_checked b i).sub⟩
private theorem order_of_full {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : Source b M F rows) (hw : InBand b M.overhead)
    (x : Test b) {q : Surface} (hq : Parent q) (hv : BankPass rows (terminal b).shape q)
    {W} (hW : W < (tested b x).shape.m * agreement) {P : Jet}
    (hP : P ∈ rows (tested b x).shape W) :
    OrderAt q P (contactPower M.overhead.toNat (tested b x).shape W) := by
  let h := M.overhead.toNat
  let t := tested b x
  obtain ⟨ht, hm, hb, hj, hu⟩ := tested_spec b x
  have hchar : t.shape.m * agreement < p := hm ▸ (terminal_guards b).2.2.2.1
  apply K1_14_3R_1.proof _ _ _ hq
  · have hd := Nat.div_le_self (fullCutoff t.shape - W) (2*h)
    change 1 + (fullCutoff t.shape - W)/(2*h) < p
    change W < t.shape.m * agreement at hW
    unfold fullCutoff at *
    omega
  intro a c hac
  change a + c < 1 + (fullCutoff t.shape - W)/(2*h) at hac
  have hh : 0 < h := (terminal_guards b).1.trans_le (window_nat hw).1
  have hc := (Nat.le_div_iff_mul_le (by omega : 0 < 2*h)).mp
    (show a+c ≤ (fullCutoff t.shape - W)/(2*h) by omega)
  rw [Nat.mul_comm (a+c), Nat.mul_add] at hc
  have top : fullCutoff t.shape = fullCutoff (terminal b).shape :=
    congrArg (fun m => m * agreement - 1) hm
  have hwc : W ≤ fullCutoff t.shape := by
    change W < t.shape.m * agreement at hW
    unfold fullCutoff
    omega
  have hw' : W + 2*h*a + 2*h*c ≤ fullCutoff (terminal b).shape := by omega
  have ha := src.shift t ht W P hP 0 a
  have hc' := src.shift t ht _ _ ha 1 c
  exact hv _ (src.nested t ht _ (Or.inl rfl) hm hb hj hu _ _ hw' hc')
theorem trace_of_full {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : Source b M F rows) (hw : InBand b M.overhead)
    {qs : Finset Surface} (hq : ∀ q ∈ qs, Parent q)
    (hp : ∀ q ∈ qs, BankPass rows (terminal b).shape q) {f : Equation}
    (hf : ProjectedProduct qs f) (x : Test b) :
    TerminalTrace M.overhead.toNat (tested b x) rows f := by
  have ht := (tested_spec b x).1
  refine ⟨src.floor_bound _ ht, src.shape _ ht, src.leading _ ht, ?_⟩
  intro W hW P hP hn
  exact hf.divides_leading P _ hn
    (fun q h => order_of_full src hw x (hq q h) (hp q h) hW hP)
theorem grade_of_rejections {b : Band} {f : Equation} (hp : 0 < f.natDegree)
    (reject : ∀ x : Test b, threshold b x ≤ f.natDegree →
      seedThreshold b x ≤ seedDegree f → False) :
    ∃ i : GradeIndex b, f.natDegree = i.val+1 ∧ SeedBound f ((grades b).get i).seedCap := by
  have he : f.natDegree ≤ (grades b).length := by
    by_contra! hlo
    exact reject none hlo (Nat.zero_le _)
  let i : GradeIndex b := ⟨f.natDegree-1, by omega⟩
  have hidx : f.natDegree = i.val+1 := by dsimp [i]; omega
  refine ⟨i, hidx, (seedDegree_le_iff _ _).mp ?_⟩
  by_contra! hlow
  exact reject (some i) hidx.ge hlow
end
end HighCore82258
end
section
namespace HighCore82258
open HighCore82258 (Band agreement blockLength)
open P1_7_7 (localOrd localSeed)
open private coordinate_bounds from ProximityPrize.SubmissionLower.UpperBranch7
def ordinateFee (lo hi e : ℕ) := muNum hi + 2 * (lambdaNum hi * quotientOrder lo) * (e - 1)
def seedFee (lo hi v : ℕ) := 2 * hi * muNum hi + 2 * (lambdaNum hi * quotientOrder lo) * v
theorem band_invoice {b : Band} {w : ℕ} (hwlo : (start b) ≤ w) (hwhi : w ≤ (finish b))
    (e v : ℕ) :
    Invoice (131071+w) w e v (ordinateFee (start b) (finish b) e) (seedFee (start b) (finish b) v)
      (scale (finish b)) := by
  obtain ⟨hlo, hhi, _, _, _⟩ := terminal_guards b
  have hdhi : degreeAt (finish b) < agreement := by
    change 131071 + (finish b) < 179886
    omega
  have hd : 131071+w < agreement := (Nat.add_le_add_left hwhi _).trans_lt hdhi
  have hA : agreement ≤ blockLength := by decide
  have hD : 0 < scale (finish b) := Nat.mul_pos (by decide) (Nat.sub_pos_of_lt hdhi)
  have hm : scale (finish b) ≤ muNum (finish b) :=
    Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hA _)
  have hpos : 1 ≤ 2*(finish b) := by omega
  refine ⟨hD, hm.trans (Nat.le_add_right _ _), ?_, hd, ?_⟩
  · exact hm.trans ((by
      simpa only [one_mul] using Nat.mul_le_mul_right (muNum (finish b)) hpos :
      muNum (finish b) ≤ 2*(finish b)*muNum (finish b)).trans (Nat.le_add_right _ _))
  · intro s hs
    have hord : (131071+w) - 2*w ≤ quotientOrder (start b) := by
      unfold quotientOrder P1_7.quotientOrder
      omega
    exact coordinate_bounds hA (Nat.add_le_add_left hwhi _) hdhi hwhi hord hs
theorem fee_of_bound {lo hi e v count : ℕ} (hD : 0 < scale hi)
    (hcount : ((scale hi : ℕ) : ℚ)^2 * count ≤
      ((e * (seedFee lo hi v)^2 + 2*v*(ordinateFee lo hi e)*(seedFee lo hi v) : ℕ) : ℚ) +
        ((scale hi : ℕ) : ℚ)^2 * e) :
    count ≤ persistentFee lo hi e v := by
  let D := (scale hi)^2
  let num := e * (seedFee lo hi v)^2 + 2*v*(ordinateFee lo hi e)*(seedFee lo hi v)
  have hd : 0 < D := pow_pos hD _
  have h : D * count ≤ num + D * e := by exact_mod_cast hcount
  have hmul : (count-e) * D ≤ num := by
    rw [Nat.sub_mul, Nat.mul_comm count, Nat.mul_comm e]
    omega
  have hdiv := (Nat.le_div_iff_mul_le hd).mpr (hmul.trans (Nat.le_add_right num (D-1)))
  change count ≤ (num + (D-1)) / D + e
  omega
end HighCore82258
end
section
namespace HighCore82258
noncomputable section
open Polynomial MvPolynomial
open HighCore82258 (AnchorModel AnchoredFamily Band I K agreement node p)
open K1_14 (Equation FX L SeedBound seedEmbedding liftPoly)
open K1_14_1 (PoleData CRTLift MarkResidues seedPair)
open P1_7_7 (CRTChart poleProduct sheet_cover curve_scale_of_cut)
open scoped BigOperators
theorem persistent_count {b : Band} {u del} (M : AnchorModel u del)
    {Γ} (F : AnchoredFamily M Γ) (hband : InBand b M.overhead)
    {H} (hH : AdjacentChart M F H) (i : GradeIndex b) {f : Equation}
    (hf : Reduced f) (hseed : SeedBound f ((grades b).get i).seedCap) :
    RegularCount M F f (persistentFee (start b) (finish b) f.natDegree ((grades b).get i).seedCap) := by
  intro T hT hroots
  let w := M.overhead.toNat
  let d := 131071 + w
  let e := f.natDegree
  let v := ((grades b).get i).seedCap
  obtain ⟨hwlo, hwhi⟩ := window_nat hband
  obtain ⟨hlo, hhi, _, _, _⟩ := terminal_guards b
  have hw : 0 < w := hlo.trans_le hwlo
  have h2w : 2 * w ≤ d := by dsimp only [d]; omega
  have hInv := band_invoice hwlo hwhi e v
  have hdp : d < p := hInv.degree.trans (by decide)
  have hword : FixedWord M.word T F.scalar d := by
    refine ⟨F.distinct.mono hT, ?_, ?_⟩
    · intro γ hγ
      rcases (F.mark γ (hT hγ)).scalar_degree with hz | hdeg
      · simp only [hz, natDegree_zero, Nat.zero_le]
      · change ((F.scalar γ).natDegree : ℤ) ≤ 131072 - 1 + M.overhead at hdeg
        have hd' : ((F.scalar γ).natDegree : ℤ) ≤ 131071 + (w : ℤ) := by
          dsimp only [w]
          omega
        exact_mod_cast hd'
    · intro γ hγ
      let mark := F.mark γ (hT hγ)
      exact ⟨mark.bad.support, mark.bad.agreement, mark.scalar_hits⟩
  have hz : Set.InjOn M.label (T : Set K) := fun _ _ _ _ h => sub_left_inj.mp h
  obtain ⟨CRT, hCRT⟩ := FrontCore82258.crt_chart M F H hw hH
  obtain ⟨hmonic, hdeg, hcenter, hnodes⟩ :=
    FrontCore82258.pole_data (M := M) (F := F) hH
  have hchart := P1_7_7_2.proof d w e v hw h2w hdp (poleProduct H) hmonic hdeg hcenter hnodes
    f hf.1 le_rfl hseed T M.label F.scalar M.word hword.degree hroots CRT
    (fun γ hγ => hCRT γ (hT hγ))
  obtain ⟨Ps, hPs, hcard, hsum, hcover⟩ := sheet_cover
    (hInv.scale_pos.trans_le hInv.ordinate) (hInv.scale_pos.trans_le hInv.seed)
    f hf.1 (show f.natDegree ≤ e from le_rfl) hseed T M.label F.scalar hroots
  have hcount := count_cover hInv P1_7_7_3.proof (curve_scale_of_cut P1_7_7_3.proof) hword hchart hz Ps hPs hcover
  apply fee_of_bound hInv.scale_pos
  refine hcount.trans (add_le_add hsum ?_)
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcard) (by positivity)
end
end HighCore82258
end
section
namespace HighCore82258
noncomputable section
open Finset Polynomial MvPolynomial
open HighCore82258 (agreement)
open K1_14 (Shape shapeSum Banks Equation FX Jet slots triangle SeedBound)
open K1_14_3 (RowCaps)
open K1_14_4 (gradeWidth seedDegree seedDegree_pow)
open P1_7_5 (kept)
open private position_sum from ProximityPrize.SubmissionLower.UpperBranch5
open private rank_joint_multiples_le gradeCapacity_eq from ProximityPrize.SubmissionLower.UpperBranch5
open private shapeSum_swap from ProximityPrize.SubmissionLower.Fast072
open private finrank_le_grades mem_filtered from ProximityPrize.SubmissionLower.Fast069
def cutoffCapacity (h : ℕ) (s : Shape) (E v W : ℕ) : ℕ :=
  shapeSum s fun q j =>
    if q*(131071-h) ≤ W+j then
      kept s.U v ((q-j)/E) (contactPower h s W - j)
    else 0
private def gradeCapacity (h : ℕ) (s : Shape) (E v W j : ℕ) : ℕ :=
  let r := contactPower h s W - j
  (gradeWidth (131071-h) s.B W j - r*E) * slots s.U (r*v)
private theorem cutoffCapacity_eq (h : ℕ) (s : Shape) (E v W : ℕ)
    (hk : 0 < 131071-h) (he : 0 < E) :
    (∑ j ∈ range (s.J+1), gradeCapacity h s E v W j) = cutoffCapacity h s E v W := by
  rw [cutoffCapacity, ← shapeSum_swap]
  apply sum_congr rfl
  intro j _
  exact gradeCapacity_eq _ _ _ _ _ _ _ _ hk he
set_option backward.isDefEq.respectTransparency false in
theorem cutoff_finrank_le (h : ℕ) (s : Shape) (E v W : ℕ) (V : Submodule FX Jet)
    {f : Equation} (hf : f ≠ 0) (hE : E ≤ f.natDegree) (hv : v ≤ seedDegree f)
    (hk : 0 < 131071-h) (he : 0 < E)
    (hcaps : ∀ P ∈ V, RowCaps P s)
    (hlead : ∀ P ∈ V, P ≠ 0 →
      (P.leadingCoeff.natDegree + P.natDegree) * (131071-h) ≤ W + P.natDegree)
    (hdvd : ∀ P ∈ V, P ≠ 0 → f ^ (contactPower h s W - P.natDegree) ∣ P.leadingCoeff) :
    Module.finrank FX V ≤ cutoffCapacity h s E v W := by
  have hrow {P : Jet} (hP : P ∈ V) (hn : P ≠ 0) :
      P.leadingCoeff.natDegree + P.natDegree ≤ s.B ∧ P.natDegree ≤ s.J ∧
      SeedBound P.leadingCoeff s.U := by
    have ha : (P.coeff P.natDegree).coeff P.leadingCoeff.natDegree ≠ 0 := by
      rw [coeff_natDegree, coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn)
    obtain ⟨hB, hJ, _⟩ := hcaps P hP _ _ ha
    refine ⟨hB, hJ, fun i => ?_⟩
    by_cases hi : P.leadingCoeff.coeff i = 0
    · simp [hi]
    · rw [← coeff_natDegree] at hi ⊢
      exact (hcaps P hP _ _ hi).2.2
  rw [← cutoffCapacity_eq h s E v W hk he]
  refine finrank_le_grades (F := FX) (A := Equation) V (gradeCapacity h s E v W)
    (s.J+1) ?_ ?_
  · intro j
    let r := contactPower h s W - j
    apply rank_joint_multiples_le _ (g := f^r) (pow_ne_zero r hf)
    · rw [Polynomial.natDegree_pow]
      exact Nat.mul_le_mul_left _ hE
    · rw [seedDegree_pow hf]
      exact Nat.mul_le_mul_left _ hv
    · rintro c ⟨⟨P, hP⟩, rfl⟩ hc
      change P.coeff j ≠ 0 at hc
      obtain ⟨hpV, hd⟩ := mem_filtered.mp hP
      have hn : P ≠ 0 := by
        intro hz
        exact hc (by simp [hz])
      have hj : P.natDegree = j :=
        le_antisymm (Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt hn).2 hd))
          (le_natDegree_of_ne_zero hc)
      obtain ⟨hB, _, hseed⟩ := hrow hpV hn
      have hwidth := hlead P hpV hn
      have hdiv := hdvd P hpV hn
      rw [hj] at hB hwidth hdiv
      change (P.coeff j).natDegree < _ ∧ SeedBound (P.coeff j) _ ∧ _ ∣ P.coeff j
      rw [← hj, coeff_natDegree, hj]
      refine ⟨?_, hseed, hdiv⟩
      have hd := (Nat.le_div_iff_mul_le hk).2 hwidth
      unfold gradeWidth
      omega
  · intro P hp
    by_cases hn : P = 0
    · simp [hn]
    · exact (natDegree_lt_iff_degree_lt hn).1 (Nat.lt_succ_of_le (hrow hp hn).2.1)
theorem cutoff_total (h : ℕ) (s : Shape) (E v : ℕ) (hh : 0 < 2*h) (hk : 1 ≤ 131071-h) :
    (∑ W ∈ range (s.m*agreement), cutoffCapacity h s E v W) + jointGain h s E v =
      triangle s.U * shapeSum s (fun q j => s.m*agreement+j-q*(131071-h)) := by
  have hswap (F : ℕ → ℕ → ℕ → ℕ) :
      (∑ W ∈ range (s.m*agreement), shapeSum s (F W)) =
        shapeSum s (fun q j => ∑ W ∈ range (s.m*agreement), F W q j) := by
    unfold shapeSum
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    rw [sum_comm]
  simp only [cutoffCapacity, jointGain]
  rw [hswap]
  simp only [shapeSum, ← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro j hj
  have hjq : j ≤ q := (Nat.le_of_lt_succ (mem_range.mp hj)).trans (min_le_left _ _)
  have hq : q ≤ q*(131071-h) := by simpa using Nat.mul_le_mul_left q hk
  exact position_sum (s.m*agreement) (2*h) (q*(131071-h)) j s.U v ((q-j)/E)
    (hjq.trans hq) hh
private theorem trace_rank_le {h E v W : ℕ} {t : Bank}
    {rows : K1_14.Banks} {f : K1_14.Equation} (ht : TerminalTrace h t rows f)
    (hne : f ≠ 0) (hE : E ≤ f.natDegree) (hv : v ≤ K1_14_4.seedDegree f)
    (hk : 0 < 131071 - h) (he : 0 < E) (hW : W < t.shape.m * agreement) :
    Module.finrank FX (rows t.shape W) ≤ cutoffCapacity h t.shape E v W :=
  cutoff_finrank_le h t.shape E v W (rows t.shape W) (f := f) hne hE hv hk he
    (fun P hP => ht.shape W P hP)
    (fun P hP hn => ht.leading W P hP hn)
    (fun P hP hn => ht.divides W hW P hP hn)
theorem joint_loss {b : HighCore82258.Band} {h : ℕ} (hl : (start b) ≤ h) (hu : h ≤ (finish b))
    (x : Test b) {rows f} (hf : Reduced f) (ht : TerminalTrace h (tested b x) rows f)
    (hE : threshold b x ≤ f.natDegree) (hv : seedThreshold b x ≤ seedDegree f) :
    jointGain h (tested b x).shape (threshold b x) (seedThreshold b x) ≤ debit h (tested b x) := by
  obtain ⟨hlo, hhi, htop, _, hwidth⟩ := terminal_guards b
  obtain ⟨_, hm, hB, _, _⟩ := tested_spec b x
  have hh : 0 < 2*h := by omega
  have hk : 0 < 131071-h := by omega
  have he : 0 < threshold b x := by cases x <;> exact Nat.succ_pos _
  have hne : f ≠ 0 := by
    intro hz
    have hpos := hf.1
    simp [hz] at hpos
  let t := tested b x
  let top := t.shape.m*agreement
  have htopPos : 0 < top := by
    change 0 < (tested b x).shape.m*agreement
    rwa [hm]
  have hbWidth : t.shape.B*(131071-h) ≤ top := by
    change (tested b x).shape.B*(131071-h) ≤ (tested b x).shape.m*agreement
    rw [hm, hB]
    exact (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hl _)).trans hwidth
  have htopSub : top-1+1 = top := by omega
  have hraw : ∀ q ≤ t.shape.B, ∀ j ≤ min q t.shape.J,
      q*(131071-h) ≤ top-1+1+j := by
    intro q hq j _
    rw [htopSub]
    exact (Nat.mul_le_mul_right _ hq).trans (hbWidth.trans (by omega : top ≤ top+j))
  have hmin := ht.floor_bound (top-1) (show top-1 < top by omega) hraw
  change triangle t.shape.U * shapeSum t.shape (fun q j => top-1+1+j-q*(131071-h)) ≤
    debit h t + ∑ W ∈ range (top-1+1), Module.finrank FX (rows t.shape W) at hmin
  rw [htopSub] at hmin
  have hmax : (∑ W ∈ range top, Module.finrank FX (rows t.shape W)) ≤
      ∑ W ∈ range top, cutoffCapacity h t.shape (threshold b x) (seedThreshold b x) W := by
    apply sum_le_sum
    intro W hW
    exact trace_rank_le ht hne hE hv hk he (mem_range.mp hW)
  have htotal := cutoff_total h t.shape (threshold b x) (seedThreshold b x) hh hk
  change (∑ W ∈ range top, cutoffCapacity h t.shape (threshold b x) (seedThreshold b x) W) +
    jointGain h t.shape (threshold b x) (seedThreshold b x) =
    triangle t.shape.U * shapeSum t.shape (fun q j => top+j-q*(131071-h)) at htotal
  change jointGain h t.shape (threshold b x) (seedThreshold b x) ≤ debit h t
  omega
end
end HighCore82258
end
section
namespace HighCore82258
noncomputable section
open Polynomial
open HighCore82258 (Band AnchorModel AnchoredFamily K)
open K1_14 (Banks Equation SeedBound atMark graphEval)
open K1_14_3 (ProjectedProduct)
open K1_14_4 (seedDegree seedDegree_le_iff)
def c2 : Prop :=
  ∀ (b : Band) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b M.overhead → M.shift ∉ Γ → ∀ rows, Source b M F rows →
    Nonempty (Pairs b M.overhead.toNat rows)
def c3 : Prop :=
  ∀ (b : Band) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b M.overhead → M.shift ∉ Γ → ∀ H, AdjacentChart M F H →
    ((start b) < 7773 → CurveTariff b M F) →
    ∀ rows, Source b M F rows → ∀ pairs : Pairs b M.overhead.toNat rows,
    Nonempty (PrefixInventory b M F pairs)
def c5 : Prop :=
  ∀ (b : Band) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b M.overhead → M.shift ∉ Γ → ∀ H, AdjacentChart M F H →
    ∀ (i : GradeIndex b) f, Reduced f → f.natDegree = i.val+1 → 3 ≤ f.natDegree →
    0 < seedDegree f → SeedBound f ((grades b).get i).seedCap →
    RegularCount M F f (tangentFee (start b) (finish b) f.natDegree ((grades b).get i).seedCap)
private theorem retained_count (h5 : c5) {b u del}
    (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hw : InBand b M.overhead) (hshift : M.shift ∉ Γ) {H} (hH : AdjacentChart M F H)
    (T : Finset K) (hT : T ⊆ Γ) (f : Equation) (hf : Reduced f)
    (i : GradeIndex b) (he : f.natDegree = i.val+1) (hs : SeedBound f ((grades b).get i).seedCap)
    (hr : ∀ γ ∈ T, atMark f (M.label γ) (F.scalar γ) = 0) : T.card ≤ (retainedCap b) := by
  classical
  let v := ((grades b).get i).seedCap
  have cert := grade_checked b i
  rw [← he] at cert
  have hprice : wholePrice (start b) (finish b) f.natDegree v ≤ (retainedCap b) := cert.fee
  by_cases hzero : seedDegree f = 0
  · have hfix := FrontCore82258.fixed_count M F T hT hf.1 ((seedDegree_le_iff f 0).mp hzero.le) hr
    exact hfix.trans ((sheets_le_price _ _ _ _).trans hprice)
  have hpos := Nat.pos_of_ne_zero hzero
  have hv : v ≠ 0 := Nat.ne_of_gt (hpos.trans_le ((seedDegree_le_iff _ _).mpr hs))
  let bad := T.filter fun γ => graphEval (M.label γ) (f.resultant f.derivative) = 0
  have hb : bad ⊆ T := Finset.filter_subset _ _
  have hbad := FrontCore82258.resultant_count M hf hs cert.separant bad
    (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hreg : ∀ γ ∈ T \ bad, regularRoot f (M.label γ) (F.scalar γ) := by
    intro γ hγ
    obtain ⟨ht, hn⟩ := Finset.mem_sdiff.mp hγ
    exact P1_7.regular_of_resultant hf.1 (hr γ ht) (fun hz => hn (Finset.mem_filter.mpr ⟨ht,hz⟩))
  have hpartition := Finset.card_sdiff_add_card_eq_card hb
  have hsub : T \ bad ⊆ Γ := Finset.sdiff_subset.trans hT
  apply le_trans _ hprice
  by_cases hsmall : f.natDegree ≤ 2
  · have hreg' := persistent_count M F hw hH i hf hs _ hsub hreg
    simp only [wholePrice, ite_eq_right hv, ite_eq_left hsmall]
    change bad.card ≤ singularFee f.natDegree v at hbad
    change (T \ bad).card ≤ persistentFee (start b) (finish b) f.natDegree v at hreg'
    omega
  · have hreg' := h5 b u del M Γ F hw hshift H hH i f hf he (by omega) hpos hs _ hsub hreg
    simp only [wholePrice, ite_eq_right hv, ite_eq_right hsmall]
    change bad.card ≤ singularFee f.natDegree v at hbad
    change (T \ bad).card ≤ tangentFee (start b) (finish b) f.natDegree v at hreg'
    omega
def HighStatement : Prop :=
  ∀ (b : Band) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    ((start b) : ℤ) ≤ M.overhead → M.overhead ≤ ((finish b) : ℤ) →
    Γ.card ≤ (prefixFee b) + (retainedCap b) + 1

def RetainedCountAt (b : Band) : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b M.overhead → M.shift ∉ Γ → ∀ H, AdjacentChart M F H →
    ∀ C : ChartSource b M F, ∀ pairs : Pairs b M.overhead.toNat C.rows,
    ∀ Q : PrefixInventory b M F pairs, ∀ f : Equation, Reduced f →
    ProjectedProduct Q.parents f → ∀ T : Finset K, T ⊆ Γ →
    (∀ γ ∈ T, atMark f (M.label γ) (F.scalar γ) = 0) →
    T.card ≤ retainedCap b

theorem legacy_retained (h5 : c5) (b : Band) (hb : b ≠ .h2367) :
    RetainedCountAt b := by
  intro u del M Γ F hw hshift H hH C pairs Q f hf hprod T hT hvanish
  obtain ⟨hl, hu⟩ := window_nat hw
  obtain ⟨i, he, hs⟩ := grade_of_rejections (b := b) hf.1 (by
    intro x hE hv
    have trace := trace_of_full C.source hw Q.geometric Q.terminal_pass hprod x
    exact (HighCore82258Terminal.terminal_bounds b hb hl hu x).not_ge
      (joint_loss hl hu x hf trace hE hv))
  exact retained_count h5 M F hw hshift hH T hT f hf i he hs hvanish

theorem of_children (h1 : CRTSourceExists) (h2 : c2) (h3 : c3)
    (hRetained : ∀ b, RetainedCountAt b) : HighCore82258.HighStatement := by
  classical
  intro b u del M Γ F hlo hhi
  have hw : InBand b M.overhead := ⟨hlo,hhi⟩
  let regular := Γ.erase M.shift
  have hreg : regular ⊆ Γ := Finset.erase_subset _ _
  have hshift : M.shift ∉ regular := Finset.notMem_erase _ _
  let G : AnchoredFamily M regular :=
    ⟨F.scalar, fun γ hγ => F.mark γ (hreg hγ), F.distinct.mono hreg⟩
  suffices hc : regular.card ≤ (prefixFee b) + (retainedCap b) by
    have herase : Γ.card - 1 ≤ regular.card := Finset.pred_card_le_card_erase
    omega
  obtain ⟨H,hH⟩ := FrontCore82258.adjacent_chart M G
  obtain ⟨C⟩ := h1 b u del M regular G hw hshift H hH
  let rows := C.rows
  have src : Source b M G rows := C.source
  obtain ⟨pairs⟩ := h2 b u del M regular G hw hshift rows src
  obtain ⟨Q⟩ := h3 b u del M regular G hw hshift H hH
    (fun _ => persistent_curve M G hw) rows src pairs
  let keep := regular \ Q.books.union
  have hk : keep ⊆ regular := Finset.sdiff_subset
  have hpaid : (regular \ keep).card ≤ (prefixFee b) := by
    apply (Finset.card_le_card ?_).trans Q.books.card_union
    intro γ hγ
    obtain ⟨ha,hn⟩ := Finset.mem_sdiff.mp hγ
    by_contra hm
    exact hn (Finset.mem_sdiff.mpr ⟨ha,hm⟩)
  have cover : ∀ γ ∈ keep, ∃ q ∈ Q.parents, MarkOn M G q γ := fun γ hγ =>
    (Q.covers γ (hk hγ)).resolve_left (Finset.mem_sdiff.mp hγ).2
  suffices hkept : keep.card ≤ (retainedCap b) by
    have hpart := Finset.card_sdiff_add_card_eq_card hk
    omega
  by_cases hm : keep.Nonempty
  · obtain ⟨γ,hγ⟩ := hm
    obtain ⟨q,hq,_⟩ := cover γ hγ
    obtain ⟨f,hf⟩ := K1_14_3_7.proof Q.parents ⟨q,hq⟩ Q.geometric
    have hred : Reduced f := ⟨hf.positive, hf.primitive, hf.separable⟩
    apply hRetained b u del M regular G hw hshift H hH C pairs Q f hred hf keep hk
    intro η hη
    obtain ⟨q',hq',hon⟩ := cover η hη
    have hz := RingHom.mem_ker.mp (hon (hf.vanishes q' hq'))
    simpa only [coe_eval₂RingHom, eval₂_C, atMark] using hz
  · simp [Finset.not_nonempty_iff_eq_empty.mp hm]
end
end HighCore82258
end


namespace HighCore82258

theorem all_high_of_prefix_and_retained
    (hSource : CRTSourceExists) (hPrefix : c3) (hRetained : ∀ b, RetainedCountAt b)
    {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hl : 2414 ≤ M.overhead) (hu : M.overhead ≤ (heightCap : ℤ)) :
    Γ.card ≤ 267872462194200158 := by
  obtain ⟨b, hlo, hhi⟩ := height_cover (h := M.overhead.toNat) (by omega) (by omega)
  have h := of_children hSource
    (fun b _ _ M _ F hb _ _ src => buffered_pairs b M F hb src)
    hPrefix hRetained
    b u del M Γ F (by omega) (by omega)
  have hb : prefixFee b + retainedCap b + 1 ≤ 267872462194200158 := by
    exact (accounting b).1.le.trans (accounting b).2
  exact h.trans hb

#print axioms all_high_of_prefix_and_retained
end HighCore82258