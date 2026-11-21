import ProximityPrize.SubmissionLower.GoldBranch7N2

set_option Elab.async false
set_option maxRecDepth 18000

namespace HighBanks82170

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
  s.m*179974 - 2*h*r + j - q*(131071-h) - mode*(2*h*j)

def gain (h r : ℕ) (s : Shape) (mode : ℕ) : ℕ :=
  triangle s.U * shapeSum s (fun q j => width h r s q j mode)

/-- Pay once per coefficient for the nine agreements removed from the cutoff. -/
def adjusted (t : Bank) : Bank :=
  {t with nodeRows := t.nodeRows + count t.shape*(9*t.shape.m)}

private theorem at_most_old (h r : ℕ) (s : Shape) (mode : ℕ) :
    P3_7_2.gain h r s mode ≤ gain h r s mode + triangle s.U*(count s*(9*s.m)) := by
  have term_bound (q j : ℕ) :
      P3_7_2.rawWidth h r s q j - mode*(2*h*j) ≤ width h r s q j mode + 9*s.m := by
    change s.m*179983-2*h*r+j-q*(131071-h)-mode*(2*h*j) ≤
      s.m*179974-2*h*r+j-q*(131071-h)-mode*(2*h*j)+9*s.m
    have changed : s.m*179983 = s.m*179974 + 9*s.m := by ring
    omega
  have le : shapeSum s (fun q j => P3_7_2.rawWidth h r s q j - mode*(2*h*j)) ≤
      shapeSum s (fun q j => width h r s q j mode + 9*s.m) :=
    sum_le_sum fun q _ => sum_le_sum fun j _ => term_bound q j
  rw [sum_shift] at le
  simpa only [P3_7_2.gain, gain, Nat.mul_add] using Nat.mul_le_mul_left (triangle s.U) le

theorem transferred {lo h r mode : ℕ} {t : Bank} (hl : lo ≤ h) (hh : h ≤ 131071)
    (c : BankCertificate lo r mode (adjusted t)) : debit h t < gain h r t.shape mode := by
  have pos := (of_certificate hl hh c).2.1
  change debit h (adjusted t) < P3_7_2.gain h r t.shape mode at pos
  have eq : debit h (adjusted t) =
      debit h t + triangle t.shape.U*(count t.shape*(9*t.shape.m)) := by
    unfold P3_7.debit P1_7.debit adjusted
    dsimp only
    ring
  rw [eq] at pos
  have upper := at_most_old h r t.shape mode
  omega

def start : HighBand → ℕ
  | .h2274 => 2297
  | .h2294 => 2318
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
    refine cons (bank! 106,157438,0x4999e55d298,0x777b784258) (bank! 499,355671,0x45d20b6c5f3008,0x1718494bc9f330) ?_
    refine cons (bank! 112,100132,0x715d97abd68,0xbfef2eefc8) (bank! 494,326224,0x65830b34104c48,0x214152f27ceeec) ?_
    refine cons (bank! 126,92532,0x91c957ac190,0x108232b7638) (bank! 543,439883,0x8ce78887a27878,0x31ead083db65f0) ?_
    refine cons (bank! 138,162497,0xb8209092e50,0x1670ea60a60) (bank! 595,449621,0xb7c658bce74aa0,0x485d9f1cdb0488) ?_
    refine cons (bank! 148,130044,0xf12c0166f20,0x1f30e6abe10) (bank! 670,506059,0xf097394e2bfd6c,0x6a35bc5e91e654) ?_
    refine cons (bank! 160,200009,0x136e66b5f2f0,0x2983e026d00) (bank! 723,515797,0x13b6d2f7204d700,0x9441d0cc0b1b54) ?_
    refine cons (bank! 159,144206,0x1d13791cb0b0,0x3e63be29988) (bank! 812,569229,0x19d01167a900438,0xd96dd7b6e01fa8) ?_
    refine cons (bank! 198,143168,0x403b65ee8268,0xa1c0e14e070) (bank! 924,578014,0x3c2bf15726a7228,0x22f684ed2b41a70) ?_
    refine cons (bank! 271,254201,0x93def5e16dc0,0x1e82a49a14fc) (bank! 1205,772731,0xa27434524df6000,0x7bbfe587482d660) ?_
    refine cons (bank! 328,284198,0xc778c1d334c8,0x2db57d01eae0) (bank! 1426,921786,0xe0658dfdf4cd6b0,0xcc36ad557b0a740) ?_
    refine cons (bank! 325,282990,0x1e1e7d2cfab98,0x7407dec5f568) (bank! 1757,1157191,0x1d42b53fcec1372c,0x21ec00c7f2d3caf8) ?_
    refine cons (bank! 363,212367,0x6d3eee6d9bc20,0x1d35890b7c5e8) (bank! 2033,1266658,0x3fdb16c4a648c408,0x54b9b86e10b9b1a0) ?_
    refine cons (bank! 348,145788,0x212620515c13740,0x86b44e4aa89680) (bank! 1685,1014675,0x957e80ad01378bd8,0x9d555405e66dcf98) ?_
    refine cons (bank! 616,468366,0x12f0be7597f370,0x8b0b967833c00) (bank! 3042,1873926,0x13d67fd2be32fb3dc,0x28ef12d5a013d8ca0) ?_
    refine cons (bank! 943,711218,0x3e057e19d52938,0x2d3a566eb28a6c) (bank! 4693,2988671,0x4efb5cc1e321499a0,0x10fe51c36ab2980d10) ?_
    refine cons (bank! 1384,908402,0x16e71fb66aa021c,0x1cc027e4a9aef94) (bank! 7323,4720082,0x152e9f835a2745c420,0xa452dc54ede8e06b30) ?_
    exact nil
  | h2294 =>
    rw [stages, start]
    refine cons (bank! 102,134706,0x4b204fa8240,0x6ed6aa9430) (bank! 489,393799,0x450784bfe90b08,0x11bda032b4e908) ?_
    refine cons (bank! 109,128714,0x707e0c5d5f0,0xaf6e1067e8) (bank! 479,288059,0x61e5b94e38b3e8,0x18cff84ab45180) ?_
    refine cons (bank! 120,147659,0x95577713c70,0xf5fd0dc284) (bank! 535,401328,0x8c6f84463a6440,0x25c8d9e3b1c228) ?_
    refine cons (bank! 131,166604,0xc7288159140,0x15561c22410) (bank! 571,312389,0xc01282b064c8cc,0x36693179ca63b4) ?_
    refine cons (bank! 142,185549,0x100dcab65740,0x1cf1c68ce60) (bank! 608,403433,0x1011a8b23d1eb80,0x4c757830593ca8) ?_
    refine cons (bank! 151,102034,0x15bf74c4d810,0x27c7afeb768) (bank! 725,453268,0x160ec30c4607eb0,0x76c4b404bcfb80) ?_
    refine cons (bank! 150,226151,0x211acb81be04,0x3e80456c2d8) (bank! 791,590118,0x1d5a883be763280,0xa835ec179ccf00) ?_
    refine cons (bank! 198,146885,0x404363a26ac0,0x909d00c6b00) (bank! 966,588904,0x48d738275268d88,0x1d9089a75e11390) ?_
    refine cons (bank! 227,164875,0x120147c550080,0x2c8654eb6340) (bank! 1181,776558,0xd1b01b7151ea2d0,0x6026ba402df4980) ?_
    refine cons (bank! 307,294377,0xd58c4f3f5ac0,0x27ecfb7d1020) (bank! 1321,791396,0x1277dc72f19b57d8,0x917baef1b886b80) ?_
    refine cons (bank! 295,191750,0x32a938b686420,0x9870f2f51640) (bank! 1546,1002631,0x2745f3566246be48,0x1630fd55fab6bd6c) ?_
    refine cons (bank! 363,218625,0x75486051ab300,0x195ff33763350) (bank! 2029,1283175,0x6bcf6e55b1c1dbc0,0x44ea51ae4afc8cc0) ?_
    refine cons (bank! 342,204149,0x24eadafdda4c330,0x7c3a801381be30) (bank! 1692,1047276,0xb713d91638ab2158,0x674cccac522632d0) ?_
    refine cons (bank! 387,321887,0x298832cb65e2d58,0x9ac9711d3576b8) (bank! 1719,885283,0x2bf8d18472c7f2f10,0x171a8ec7cd276c638) ?_
    refine cons (bank! 741,583358,0x16b783f00ec880,0x8831011597fe0) (bank! 3123,1945729,0x2d742039e3cb4da40,0x231d89ae9f759297c) ?_
    refine cons (bank! 884,584756,0x62636cdb2ff5c0,0x2ae9a33c929580) (bank! 4817,3008436,0x10e5c640e9dffad8ec,0xf2b93a328182c5950) ?_
    refine cons (bank! 1073,820026,0xd1b9440c7e7bc0,0x6ba170e70e8480) (bank! 5782,3555616,0x286ba16a9168ce02e0,0x263fd5db4cf9db0378) ?_
    refine cons (bank! 1444,1125847,0x2848325e64f7090,0x19da8c343b0bfe0) (bank! 7608,4555471,0x97ac65f5201bdbde70,0x96ce5689484dfdb490) ?_
    exact nil
  | h7773 =>
    rw [stages, start]
    refine cons (bank! 16,130343,0x7dd11c88,0x2541db0) (bank! 29,147316,0x80eb2f448,0x1d4ed9a8) ?_
    refine cons (bank! 30,172909,0x4eb27a450,0xd5e5da0) (bank! 54,273468,0x70bd999b30,0x11f852ac0) ?_
    refine cons (bank! 48,246686,0x2977c8b298,0x5c1ee518) (bank! 90,467660,0x4cfe79e4f80,0x9f40923c0) ?_
    refine cons (bank! 76,316272,0x184c85898d8,0x2eeb83a88) (bank! 142,637805,0x350cf6513b08,0x5d909c030c) ?_
    exact nil

theorem stage_surpluses (b : HighBand) (s : Stage) (hs : s ∈ stages b)
    {h : ℕ} (hl : start b ≤ h) (hu : h ≤ 131071) :
    debit h s.free < gain h s.reserve s.free.shape 0 ∧
      debit h s.moving < gain h s.reserve s.moving.shape 1 := by
  obtain ⟨hf, hm⟩ := certificates b s hs
  exact ⟨transferred hl hu hf, transferred hl hu hm⟩

#print axioms stage_surpluses
end HighBanks82170
