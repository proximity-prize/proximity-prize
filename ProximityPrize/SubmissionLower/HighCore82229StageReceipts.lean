import ProximityPrize.SubmissionLower.HighCore82219Stages

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219Stages

open HighCore82219
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
    refine cons (bank! 106,160015,0xcc276c00,0x817c005c00) (bank! 607,373141,0x9a3b29b4c61c,0x4abc20a2df071c) ?_
    refine cons (bank! 116,127664,0x2f55441600,0xc705d07580) (bank! 605,445866,0xa857dda6e40,0x6758b859d649a4) ?_
    refine cons (bank! 128,197737,0x58871015d0,0x121b6544728) (bank! 705,524970,0xeed426e24a10,0xaaf0d5b804c7a0) ?_
    refine cons (bank! 138,165386,0x42fbf34b40,0x19db5d8ce40) (bank! 684,395499,0x38c2284658e0,0xe0ec94e67e9428) ?_
    refine cons (bank! 149,184247,0x2cb55a1860,0x23ed1b06280) (bank! 730,536423,0x86f6a9cecf58,0x14103bffe0a5254) ?_
    refine cons (bank! 162,125627,0x88e7d52288,0x3133e6881d0) (bank! 889,501169,0x34ad2f74e210,0x20247faf4ff9fa0) ?_
    refine cons (bank! 176,113463,0xd3bb021ca0,0x59a6bd6fb28) (bank! 950,685897,0x1b879d68c4adc,0x3646a2b7db04e20) ?_
    refine cons (bank! 198,146429,0x191b4f44728,0xcd87d9a8f70) (bank! 1199,701374,0xacc40e9c13df0,0x85df8eaf07d41e8) ?_
    refine cons (bank! 238,187418,0x32919ac2960,0x487d45b20618) (bank! 1408,812963,0x10a8e97119d890,0x1a47bfb8f005dc08) ?_
    refine cons (bank! 248,188359,0x2b481c321a0,0xc61a0a4f698) (bank! 1099,746207,0x39e29e7f98834,0x75dd5c4146cfd64) ?_
    refine cons (bank! 348,404564,0xfb8b7e00ec4,0x4d797ee87d54) (bank! 1810,1103110,0x12556cde19e080,0x3e593433f7cce010) ?_
    refine cons (bank! 363,216147,0xf3a04a931bc,0x31a884487cb80) (bank! 2029,1158568,0x4b04ba94d68460,0x114e45c394c335370) ?_
    refine cons (bank! 479,404535,0x4d64fddb5288,0x15b16d53d878c) (bank! 2228,1331044,0x754f3e1f310fe8,0xf93c852154215fe4) ?_
    refine cons (bank! 523,437175,0x190d174b4388,0x56abfb2dddd38) (bank! 3129,1482915,0x1fdfd30c1d5d718,0x429c9767726ea1ae0) ?_
    refine cons (bank! 832,651929,0x1be4fa4200a40,0x2896f4e85d43e0) (bank! 4839,1687203,0x4b4f70088eeaeb0,0x23be30b6aae329e2d8) ?_
    refine cons (bank! 693,355583,0x215794bc0af8,0x115ff25b8666360) (bank! 3832,1427914,0xc4e6ebf3ac883c,0x2c36e18e81cf7f7208) ?_
    refine cons (bank! 1127,684674,0x5004109df4540,0xb886fa66608840) (bank! 6624,1099991,0xfa685466b6e5720,0xa91dedbec540a3f6a0) ?_
    exact nil
  | h2395 =>
    rw [stages]
    refine cons (bank! 102,143960,0x1c131c87f0,0x4ff08e32e0) (bank! 489,438715,0x18cda1c728a0,0x122b0fd274eb08) ?_
    refine cons (bank! 109,138318,0x351efc12d0,0x7f4d1e7fc8) (bank! 479,331893,0x3446a6b47500,0x1956c1a247b700) ?_
    refine cons (bank! 120,157971,0x438ec770e0,0xbb6d859810) (bank! 535,449886,0x45c757c838a0,0x278c2607b42e84) ?_
    refine cons (bank! 131,177624,0x9d3c52b80,0x10dcabfb500) (bank! 571,364099,0x2ce1120a21e4,0x3a0a8b178d1b34) ?_
    refine cons (bank! 142,197277,0x6f4cf713c0,0x17a21d4fd60) (bank! 608,458217,0x89115c333c30,0x5335bbd20e4c28) ?_
    refine cons (bank! 151,114330,0x623420ca90,0x20cf93e1bb0) (bank! 725,518520,0x123adfc8b9084,0x83a9c2878933b0) ?_
    refine cons (bank! 150,238003,0x5c924c5524,0x3174c2451d8) (bank! 791,661098,0x3941b04cf1d8,0xbc902913ab43b4) ?_
    refine cons (bank! 198,162005,0x23a56c06fd0,0x7fe5e0c71c0) (bank! 966,674920,0xbbefe3329428,0x22221759f65b6b0) ?_
    refine cons (bank! 227,180873,0x8eca774c88,0x2690fa52f0b0) (bank! 1181,880528,0x7a871aa02d610,0x737e37dbd44d078) ?_
    refine cons (bank! 307,317099,0x3d7f12c04c0,0x26c1c43f755c) (bank! 1321,907764,0x10fe81297cf9f0,0xaeb23123f443af8) ?_
    refine cons (bank! 295,211622,0x119f5a80980,0x8e1ef53ad490) (bank! 1547,1137957,0x7c897b865e600,0x1b8d4be32e0f7920) ?_
    refine cons (bank! 363,242371,0xf3d0d4311b8,0x18bca3d97bb90) (bank! 2029,1460621,0x5200a2953e4a14,0x5506331bec8780a0) ?_
    refine cons (bank! 342,224773,0x15307d45940,0x5a64714ffd1000) (bank! 1692,1192468,0x216c9b2ec0bd90,0x974fe4df46602990) ?_
    refine cons (bank! 387,344821,0x103738d41128,0x91395efe28d630) (bank! 1720,1031431,0x1474c7b83ab9e4,0x2e7b205192ab77020) ?_
    refine cons (bank! 741,635242,0x1159bb164c170,0x8d69a025cfef8) (bank! 3123,2217477,0xe4c3ff5ee1ccb0,0x2bfe52d1b60bd73e4) ?_
    refine cons (bank! 884,641778,0x27f412dd14d78,0x2dba155877dff8) (bank! 4818,3428328,0x3ec9350637262c0,0x12c65c7e468dc35ac0) ?_
    refine cons (bank! 1073,888710,0x38c2a87f22600,0x73c1b09afc7300) (bank! 5783,4058860,0xfc69bff41941e7c,0x2f95bd7dcad9f6274c) ?_
    refine cons (bank! 1444,1218175,0xd0e7569de28b0,0x1bf54ac48278960) (bank! 7609,5216765,0xfe8f5052ad4bd80,0xbc467c310227267500) ?_
    exact nil
  | h7773 =>
    rw [stages]
    refine cons (bank! 16,130295,0x18313410,0x25e61b0) (bank! 29,147268,0xa590fe10,0x1e94b8a0) ?_
    refine cons (bank! 30,172621,0xfcffec10,0xdcaf4a8) (bank! 54,273150,0x6c49368b4,0x13219a0d0) ?_
    refine cons (bank! 48,246032,0x4de284960,0x603dd280) (bank! 90,466934,0xe3b48fe00,0xaa53368c0) ?_
    refine cons (bank! 76,315030,0x7faa66588,0x319dbdce8) (bank! 142,636461,0x5fd8186a0,0x64fe02fbb0) ?_
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
end HighCore82219Stages
