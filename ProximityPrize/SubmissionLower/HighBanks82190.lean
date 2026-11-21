import ProximityPrize.SubmissionLower.GoldBranch7N2

set_option Elab.async false
set_option maxRecDepth 18000

namespace HighBanks82190

open Finset
open P3 (HighBand)
open P3_7 (Stage Bank debit stages)
open P3_7_2 (BankCertificate checked of_certificate worstWidth)
open K1_14 (Shape shapeSum triangle)

def count (s : Shape) : ℕ :=
  let j := min s.B s.J
  triangle j + (s.B-j)*(j+1)

private theorem triangle_succ (n : ℕ) : triangle (n+1) = triangle n + (n+2) := by
  unfold triangle
  rw [show (n+1+1)*(n+1+2) = (n+1)*(n+2) + (n+2)*2 by ring,
    Nat.add_mul_div_right _ _ (by decide : 0 < 2)]

private theorem count_eq (B J : ℕ) :
    (∑ q ∈ range (B+1), (min q J+1)) =
      triangle (min B J) + (B-min B J)*(min B J+1) := by
  induction B with
  | zero => simp [triangle]
  | succ B ih =>
    rw [sum_range_succ, ih]
    by_cases h : B+1 ≤ J
    · have h' : B ≤ J := by omega
      simp [min_eq_left h, min_eq_left h', triangle_succ]
    · have h' : J ≤ B := by omega
      have h'' : J ≤ B+1 := by omega
      simp only [min_eq_right h', min_eq_right h'']
      rw [show B+1-J = (B-J)+1 by omega, Nat.add_mul, Nat.one_mul]
      omega

theorem sum_shift (s : Shape) (f : ℕ → ℕ → ℕ) (d : ℕ) :
    shapeSum s (fun q j => f q j + d) = shapeSum s f + count s*d := by
  unfold shapeSum
  simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
  rw [← sum_mul]
  congr 1
  exact congrArg (· * d) (count_eq s.B s.J)

def width (h r : ℕ) (s : Shape) (q j mode : ℕ) : ℕ :=
  s.m*179954 - 2*h*r + j - q*(131071-h) - mode*(2*h*j)

def gain (h r : ℕ) (s : Shape) (mode : ℕ) : ℕ :=
  triangle s.U * shapeSum s (fun q j => width h r s q j mode)

/-- Pay once per coefficient for the twenty-nine agreements removed from the cutoff. -/
def adjusted (t : Bank) : Bank :=
  {t with nodeRows := t.nodeRows + count t.shape*(29*t.shape.m)}

private theorem at_most_old (h r : ℕ) (s : Shape) (mode : ℕ) :
    P3_7_2.gain h r s mode ≤ gain h r s mode + triangle s.U*(count s*(29*s.m)) := by
  have term_bound (q j : ℕ) :
      P3_7_2.rawWidth h r s q j - mode*(2*h*j) ≤ width h r s q j mode + 29*s.m := by
    change s.m*179983-2*h*r+j-q*(131071-h)-mode*(2*h*j) ≤
      s.m*179954-2*h*r+j-q*(131071-h)-mode*(2*h*j)+29*s.m
    have changed : s.m*179983 = s.m*179954 + 29*s.m := by ring
    omega
  have le : shapeSum s (fun q j => P3_7_2.rawWidth h r s q j - mode*(2*h*j)) ≤
      shapeSum s (fun q j => width h r s q j mode + 29*s.m) :=
    sum_le_sum fun q _ => sum_le_sum fun j _ => term_bound q j
  rw [sum_shift] at le
  simpa only [P3_7_2.gain, gain, Nat.mul_add] using Nat.mul_le_mul_left (triangle s.U) le

theorem transferred {lo h r mode : ℕ} {t : Bank} (hl : lo ≤ h) (hh : h ≤ 131071)
    (c : BankCertificate lo r mode (adjusted t)) : debit h t < gain h r t.shape mode := by
  have pos := (of_certificate hl hh c).2.1
  change debit h (adjusted t) < P3_7_2.gain h r t.shape mode at pos
  have eq : debit h (adjusted t) =
      debit h t + triangle t.shape.U*(count t.shape*(29*t.shape.m)) := by
    unfold P3_7.debit P1_7.debit adjusted
    dsimp only
    ring
  rw [eq] at pos
  have upper := at_most_old h r t.shape mode
  omega

def start : HighBand → ℕ
  | .h2274 => 2349
  | .h2294 => 2369
  | .h7773 => 7773

private def Checks (lo : ℕ) (ss : List Stage) : Prop :=
  ∀ s ∈ ss, BankCertificate lo s.reserve 0 (adjusted s.free) ∧
    BankCertificate lo s.reserve 1 (adjusted s.moving)
private theorem nil {lo : ℕ} : Checks lo [] := fun _ hs => (List.not_mem_nil hs).elim
private theorem cons {lo : ℕ} {s : Stage} {ss : List Stage}
    (hf : BankCertificate lo s.reserve 0 (adjusted s.free))
    (hm : BankCertificate lo s.reserve 1 (adjusted s.moving))
    (ht : Checks lo ss) : Checks lo (s::ss) := List.forall_mem_cons.mpr ⟨⟨hf, hm⟩, ht⟩
set_option quotPrecheck false
local notation "bank!" kk "," ww "," zz "," dd =>
  checked (k := kk) (w := ww) (z := zz) (d := dd)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxHeartbeats 4000000 in
private theorem certificates (b : HighBand) : Checks (start b) (stages b) := by
  cases b with
  | h2274 =>
    rw [stages, start]
    refine cons (bank! 106,162898,0xed7cdf0dc78,0x777b784258) (bank! 499,381619,0xf571d3dca1b458,0x171955a3e3f3b0) ?_
    refine cons (bank! 112,105800,0x171de19f0608,0xbfef2eefc8) (bank! 494,351860,0x164f34f95fbb6a8,0x21437f1a04a3c0) ?_
    refine cons (bank! 126,98824,0x1db73de7e8b0,0x108232b7638) (bank! 543,467911,0x1f2655a8137ac08,0x31ec9d699308f0) ?_
    refine cons (bank! 138,169309,0x25c1b9ae3e90,0x1670ea60a60) (bank! 596,480301,0x28ff3819e304cc8,0x4860eedf7c4a7c) ?_
    refine cons (bank! 148,137272,0x321688512360,0x1f30e6abe10) (bank! 671,540535,0x3657f98407c21ec,0x6a3b5569404c00) ?_
    refine cons (bank! 160,207757,0x3f6836d2bfb0,0x2983e026d00) (bank! 723,552925,0x47ae2bed3b7d158,0x94498602662808) ?_
    refine cons (bank! 159,151798,0x5ff03b364f10,0x3e63be29988) (bank! 812,610881,0x5f186dcaf0a3a60,0xd979d8e1a06f60) ?_
    refine cons (bank! 198,152372,0xd514b7f0e368,0xa1c0e14e070) (bank! 924,625126,0xe1083fdef1eaeb8,0x22f8f78dfd33988) ?_
    refine cons (bank! 271,266577,0x1f3c4ca679740,0x1e82a49a14fc) (bank! 1206,833883,0x279340467acb8f70,0x7bc6af7fc66f1f0) ?_
    refine cons (bank! 328,299330,0x28d24928304c8,0x2db57d01eae0) (bank! 1426,994222,0x388c81753cd99d90,0xcc4279b506c1f90) ?_
    refine cons (bank! 325,297342,0x66ac76e03bf18,0x7407dec5f568) (bank! 1758,0x13043b,0x7c70a502aa202740,0x21edd9cc94eaf694) ?_
    refine cons (bank! 363,227863,0x1793b501ef2970,0x1d35890b7c5e8) (bank! 2033,0x14e4da,0x1194ea480b6e33038,0x54bedbe4e4608378) ?_
    refine cons (bank! 348,160088,0x724977bcae3ff40,0x86b44e4aa89680) (bank! 1685,0x10c407,0x26ed7928b3ff541a4,0x9d5eb6461fbf2e9c) ?_
    refine cons (bank! 616,494730,0x446b99b0956670,0x8b0b967833c00) (bank! 3043,0x1eed9e,0x646f169d2273c3fb8,0x28f1664e858c20290) ?_
    refine cons (bank! 943,751778,0xea9743731d82a8,0x2d3a566eb28a6c) (bank! 4694,0x31354b,0x1f12530be1ad54ea20,0x10ff3712cf586e9970) ?_
    refine cons (bank! 1384,966278,0x6189d660311318c,0x1cc027e4a9aef94) (bank! 7324,0x4da21e,0xd7867dd6607f3c96a0,0xa45b1b33d9358b1058) ?_
    exact nil
  | h2294 =>
    rw [stages, start]
    refine cons (bank! 102,139857,0xde0b97be650,0x6ed6aa9430) (bank! 489,418738,0xb4e46be8e441d0,0x11be6ccec93688) ?_
    refine cons (bank! 109,134120,0x150672753828,0xaf6e1067e8) (bank! 479,312437,0x101d0b25cf747f0,0x18d20caed57110) ?_
    refine cons (bank! 120,153524,0x1bba533a3c9c,0xf5fd0dc284) (bank! 535,428409,0x16c6b5226e0acd8,0x25ca54537ae4a8) ?_
    refine cons (bank! 131,172928,0x248ebe992ad0,0x15561c22410) (bank! 571,341255,0x1ec3f83aa0af004,0x366dad25f9281c) ?_
    refine cons (bank! 142,192332,0x2ee3fda78460,0x1cf1c68ce60) (bank! 608,434084,0x28ac77de2bccbf8,0x4c7a0f8a5588e8) ?_
    refine cons (bank! 151,109174,0x3ec48b0e1f08,0x27c7afeb768) (bank! 725,489784,0x35b39f02665c418,0x76cc055dff2d78) ?_
    refine cons (bank! 150,233138,0x60fc1a03844c,0x3e80456c2d8) (bank! 791,629898,0x460b67408622100,0xa83d438150d640) ?_
    refine cons (bank! 198,155912,0xb952d7bd25c0,0x909d00c6b00) (bank! 966,637252,0xa56601b11534be0,0x1d9264a89b8f2c4) ?_
    refine cons (bank! 227,174769,0x333b5298130c0,0x2c8654eb6340) (bank! 1181,835259,0x1c3e70f2a33d4918,0x602b875c52113c0) ?_
    refine cons (bank! 307,308147,0x23fbc4fd59520,0x27ecfb7d1020) (bank! 1321,857084,0x2647bdcff83b8f14,0x9184d0297cd0d68) ?_
    refine cons (bank! 295,204296,0x8d00d05c6b6a0,0x9870f2f51640) (bank! 1547,0x1077c1,0x4ad1fc8b9af401c4,0x163229a41b6ebcc4) ?_
    refine cons (bank! 363,233823,0x13d2e20025cab0,0x195ff33763350) (bank! 2029,0x151cdd,0xbb089e0e6c75a940,0x44ee5c24ff7d3bc0) ?_
    refine cons (bank! 342,217868,0x64d5d9c931c3840,0x7c3a801381be30) (bank! 1692,0x113e74,0x15d6d04f752777424,0x6752b7fe7bb14d54) ?_
    refine cons (bank! 387,337289,0x6f4079b9692edf0,0x9ac9711d3576b8) (bank! 1720,968974,0x580d1b515c3407af8,0x171c4e6f9d218fd98) ?_
    refine cons (bank! 741,615590,0x33f4766ec50d20,0x8831011597fe0) (bank! 3123,0x200abe,0x40c7c2ef6830f6550,0x231f89755612b8ef8) ?_
    refine cons (bank! 884,621527,0xd44b817d1fd540,0x2ae9a33c929580) (bank! 4818,0x3189a8,0x1325a9cfe0c30b41e4,0xf2c6ae107fd4fd224) ?_
    refine cons (bank! 1073,864498,0x19e74a58e762e40,0x6ba170e70e8480) (bank! 5783,0x3a9c5a,0x2941ec6d2b5846a5f8,0x2642028fce76757d28) ?_
    refine cons (bank! 1444,0x121786,0x456bf4796c687b0,0x19da8c343b0bfe0) (bank! 7610,0x4b3d0f,0x89e86e7434ce319d78,0x96d74bf5e620260e90) ?_
    exact nil
  | h7773 =>
    rw [stages, start]
    refine cons (bank! 16,130343,0x34cb5e68,0x2541db0) (bank! 29,147316,0x30e343108,0x1d4ed9a8) ?_
    refine cons (bank! 30,172909,0x256f3af10,0xd5e5da0) (bank! 54,273468,0x263e5790b0,0x11f852ac0) ?_
    refine cons (bank! 48,246686,0x11633bec18,0x5c1ee518) (bank! 90,467660,0x19e712f0f80,0x9f40923c0) ?_
    refine cons (bank! 76,316272,0x8998ad6fd8,0x2eeb83a88) (bank! 142,637805,0x122fb7620968,0x5d909c030c) ?_
    exact nil

theorem stage_surpluses (b : HighBand) (s : Stage) (hs : s ∈ stages b)
    {h : ℕ} (hl : start b ≤ h) (hu : h ≤ 131071) :
    debit h s.free < gain h s.reserve s.free.shape 0 ∧
      debit h s.moving < gain h s.reserve s.moving.shape 1 := by
  obtain ⟨hf, hm⟩ := certificates b s hs
  exact ⟨transferred hl hu hf, transferred hl hu hm⟩

#print axioms stage_surpluses
end HighBanks82190
