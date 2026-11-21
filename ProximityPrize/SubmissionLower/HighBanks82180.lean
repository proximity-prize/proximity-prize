import ProximityPrize.SubmissionLower.GoldBranch7N2

set_option Elab.async false
set_option maxRecDepth 18000

namespace HighBanks82180

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
  s.m*179964 - 2*h*r + j - q*(131071-h) - mode*(2*h*j)

def gain (h r : ℕ) (s : Shape) (mode : ℕ) : ℕ :=
  triangle s.U * shapeSum s (fun q j => width h r s q j mode)

/-- Pay once per coefficient for the nineteen agreements removed from the cutoff. -/
def adjusted (t : Bank) : Bank :=
  {t with nodeRows := t.nodeRows + count t.shape*(19*t.shape.m)}

private theorem at_most_old (h r : ℕ) (s : Shape) (mode : ℕ) :
    P3_7_2.gain h r s mode ≤ gain h r s mode + triangle s.U*(count s*(19*s.m)) := by
  have term_bound (q j : ℕ) :
      P3_7_2.rawWidth h r s q j - mode*(2*h*j) ≤ width h r s q j mode + 19*s.m := by
    change s.m*179983-2*h*r+j-q*(131071-h)-mode*(2*h*j) ≤
      s.m*179964-2*h*r+j-q*(131071-h)-mode*(2*h*j)+19*s.m
    have changed : s.m*179983 = s.m*179964 + 19*s.m := by ring
    omega
  have le : shapeSum s (fun q j => P3_7_2.rawWidth h r s q j - mode*(2*h*j)) ≤
      shapeSum s (fun q j => width h r s q j mode + 19*s.m) :=
    sum_le_sum fun q _ => sum_le_sum fun j _ => term_bound q j
  rw [sum_shift] at le
  simpa only [P3_7_2.gain, gain, Nat.mul_add] using Nat.mul_le_mul_left (triangle s.U) le

theorem transferred {lo h r mode : ℕ} {t : Bank} (hl : lo ≤ h) (hh : h ≤ 131071)
    (c : BankCertificate lo r mode (adjusted t)) : debit h t < gain h r t.shape mode := by
  have pos := (of_certificate hl hh c).2.1
  change debit h (adjusted t) < P3_7_2.gain h r t.shape mode at pos
  have eq : debit h (adjusted t) =
      debit h t + triangle t.shape.U*(count t.shape*(19*t.shape.m)) := by
    unfold P3_7.debit P1_7.debit adjusted
    dsimp only
    ring
  rw [eq] at pos
  have upper := at_most_old h r t.shape mode
  omega

def start : HighBand → ℕ
  | .h2274 => 2323
  | .h2294 => 2343
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
    refine cons (bank! 106,160168,0x9b8b6235788,0x777b784258) (bank! 499,368645,0x9d9b78322b54c0,0x1718d041e31310) ?_
    refine cons (bank! 112,102966,0xf19dd8ce1b8,0xbfef2eefc8) (bank! 494,339042,0xe52a4a7726f0b0,0x21420d7f02bbb8) ?_
    refine cons (bank! 126,95678,0x1369e9b15520,0x108232b7638) (bank! 543,453897,0x13f9b3194307e10,0x31ebb84db58490) ?_
    refine cons (bank! 138,165903,0x18a1e15bb670,0x1670ea60a60) (bank! 596,464961,0x1a3cc7f5e1eb15c,0x485fcff6287eb4) ?_
    refine cons (bank! 148,133658,0x2094a433c940,0x1f30e6abe10) (bank! 670,523297,0x22ae6e36d6b5904,0x6a383855177a5c) ?_
    refine cons (bank! 160,203883,0x296b4ec45950,0x2983e026d00) (bank! 723,534361,0x2daf408c0e72810,0x9445bcf29b91dc) ?_
    refine cons (bank! 159,148002,0x3e81da297fe0,0x3e63be29988) (bank! 812,590055,0x3c6fe75901ba348,0xd9745de25cdab8) ?_
    refine cons (bank! 198,147770,0x8aa80eefb2e8,0xa1c0e14e070) (bank! 924,601570,0x8e8b2cb0c6f05d0,0x22f7cee0d454700) ?_
    refine cons (bank! 271,260389,0x143d1e0248280,0x1e82a49a14fc) (bank! 1206,803307,0x18da6da0390877d0,0x7bc37e0f879aa10) ?_
    refine cons (bank! 328,291764,0x1aa4eaa2b1cc8,0x2db57d01eae0) (bank! 1426,958004,0x2344bd46863bc210,0xcc3cbfa0f7a8f50) ?_
    refine cons (bank! 325,290166,0x42657a069b558,0x7407dec5f568) (bank! 1757,0x125641,0x4ccd7ec3ee9230d0,0x21ecf28f87f40aa0) ?_
    refine cons (bank! 363,220115,0xf33d1f46472c8,0x1d35890b7c5e8) (bank! 2033,0x141c5e,0xac743e2d470d5cd4,0x54bc64527066a7b0) ?_
    refine cons (bank! 348,152938,0x49b7cc070529b40,0x86b44e4aa89680) (bank! 1685,0x101fcd,0x181ee91dd65690adc,0x9d5a247b5af6c290) ?_
    refine cons (bank! 616,481548,0x2bae2c1316acf0,0x8b0b967833c00) (bank! 3042,0x1dc2d2,0x3c1349d98dd22eb90,0x28f045746a5fe39dc) ?_
    refine cons (bank! 943,731498,0x944e60c67955f0,0x2d3a566eb28a6c) (bank! 4694,0x2f67e5,0x11fb449cbcc6a411c0,0x10fec88a74b90970e0) ?_
    refine cons (bank! 1384,937340,0x3c387b0b4dd99d4,0x1cc027e4a9aef94) (bank! 7323,0x4ad3f8,0x7624f76045513a5958,0xa4571f1bd690ac0e80) ?_
    exact nil
  | h2294 =>
    rw [stages, start]
    refine cons (bank! 102,137231,0x911f3e5ea30,0x6ed6aa9430) (bank! 489,406024,0x7412b11237ed78,0x11be0726818e68) ?_
    refine cons (bank! 109,131364,0xdaf72955318,0xaf6e1067e8) (bank! 479,300009,0xa5656656fb4638,0x18d12dc6ec5ff0) ?_
    refine cons (bank! 120,150534,0x120ce6cedb44,0xf5fd0dc284) (bank! 535,414603,0xe97f8ecb798918,0x25c9982d4248a8) ?_
    refine cons (bank! 131,169704,0x17d5f2764c00,0x15561c22410) (bank! 571,326539,0x13ad81a23a6d550,0x366b2ec67bb8bc) ?_
    refine cons (bank! 142,188874,0x1e9155fa86a0,0x1cf1c68ce60) (bank! 608,418458,0x19f95dbf6c16068,0x4c77c6d80db948) ?_
    refine cons (bank! 151,105534,0x2903c26a1fd8,0x27c7afeb768) (bank! 725,471168,0x222817a37ed9c00,0x76c8b1c00b95f8) ?_
    refine cons (bank! 150,229576,0x3f1770973fbc,0x3e80456c2d8) (bank! 791,609618,0x2c6e0e7109f5e00,0xa839a749031680) ?_
    refine cons (bank! 198,151310,0x784635a992c0,0x909d00c6b00) (bank! 966,612604,0x6849b53bd205154,0x1d91775cc742fa0) ?_
    refine cons (bank! 227,169725,0x213a1a8756700,0x2c8654eb6340) (bank! 1181,805333,0x11a97ba709f8c140,0x6028f1297d3a6f8) ?_
    refine cons (bank! 307,301127,0x176add1cbefe0,0x27ecfb7d1020) (bank! 1321,823596,0x17d026d717d51590,0x9180278a459e1fc) ?_
    refine cons (bank! 295,197900,0x5b117cf1d0240,0x9870f2f51640) (bank! 1547,0xfdf35,0x2debc1bdee53d954,0x16319a945dd24d54) ?_
    refine cons (bank! 363,226075,0xcc8b468e52530,0x195ff33763350) (bank! 2029,0x1454c9,0x70dc54a2085be680,0x44ec52e16b27ad00) ?_
    refine cons (bank! 342,210874,0x40fe8662e9f9ea0,0x7c3a801381be30) (bank! 1692,0x109984,0xd672da7f1a81612c,0x674fd5c88e157abc) ?_
    refine cons (bank! 387,329437,0x478e0ab97ddd248,0x9ac9711d3576b8) (bank! 1720,926308,0x366a5f885377c7ca8,0x171b77ceb98f44df8) ?_
    refine cons (bank! 741,599158,0x21147526bd2ae0,0x8831011597fe0) (bank! 3123,0x1ed7b8,0x2581e47e6db794de0,0x231e86ebe40d51dc8) ?_
    refine cons (bank! 884,602781,0x85e2a58dde9ac0,0x2ae9a33c929580) (bank! 4818,0x2faf90,0xa6a65d95e4a9ab184,0xf2c009a3a98db0bac) ?_
    refine cons (bank! 1073,841826,0x102463c59f312c0,0x6ba170e70e8480) (bank! 5783,0x3863ce,0x15a883d32cb14ecaa8,0x2640f00bf87624caa8) ?_
    refine cons (bank! 1444,0x11a064,0x29eccd51cb29c30,0x19da8c343b0bfe0) (bank! 7609,0x48518f,0x4527f95df4bc0119a0,0x96d2de3607586d4a28) ?_
    exact nil
  | h7773 =>
    rw [stages, start]
    refine cons (bank! 16,130343,0x594e3d78,0x2541db0) (bank! 29,147316,0x58e7392a8,0x1d4ed9a8) ?_
    refine cons (bank! 30,172909,0x3a10da9b0,0xd5e5da0) (bank! 54,273468,0x4b7df895f0,0x11f852ac0) ?_
    refine cons (bank! 48,246686,0x1d6d824f58,0x5c1ee518) (bank! 90,467660,0x3372c66af80,0x9f40923c0) ?_
    refine cons (bank! 76,316272,0x10730830458,0x2eeb83a88) (bank! 142,637805,0x239e56d9a238,0x5d909c030c) ?_
    exact nil

theorem stage_surpluses (b : HighBand) (s : Stage) (hs : s ∈ stages b)
    {h : ℕ} (hl : start b ≤ h) (hu : h ≤ 131071) :
    debit h s.free < gain h s.reserve s.free.shape 0 ∧
      debit h s.moving < gain h s.reserve s.moving.shape 1 := by
  obtain ⟨hf, hm⟩ := certificates b s hs
  exact ⟨transferred hl hu hf, transferred hl hu hm⟩

#print axioms stage_surpluses
end HighBanks82180
