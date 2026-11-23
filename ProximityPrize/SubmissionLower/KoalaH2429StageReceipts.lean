import ProximityPrize.SubmissionLower.KoalaH2429StageFirst

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace KoalaH2429Stages
open HighCore82258Stages
open KoalaH2429Banks

local notation "rank!" kk "," ww "," zz "," dd =>
  checked (k := kk) (w := ww) (z := zz) (d := dd)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage01_cert :
    BankCertificate 2429 stage01.reserve 0 stage01.free ∧
      BankCertificate 2429 stage01.reserve 1 stage01.moving :=
  ⟨(rank! 108,80900,0x3446f97858,0xe3076c13c8), (rank! 605,464026,0x9bf10e88c99c,0x7eb498325fa3bc)⟩

theorem stage02_cert :
    BankCertificate 2429 stage02.reserve 0 stage02.free ∧
      BankCertificate 2429 stage02.reserve 1 stage02.moving :=
  ⟨(rank! 120,151222,0x28ef98b2d8,0x135ab6b3e38), (rank! 726,542698,0x211b38b8630,0xd8cccf34af5248)⟩

theorem stage03_cert :
    BankCertificate 2429 stage03.reserve 0 stage03.free ∧
      BankCertificate 2429 stage03.reserve 1 stage03.moving :=
  ⟨(rank! 130,119076,0x61fc05ffc0,0x1c25652dc50), (rank! 690,492176,0x290824e899f4,0x1202577bd357c6c)⟩

theorem stage04_cert :
    BankCertificate 2429 stage04.reserve 0 stage04.free ∧
      BankCertificate 2429 stage04.reserve 1 stage04.moving :=
  ⟨(rank! 144,111990,0xeec143c00,0x258b54b1580), (rank! 729,378166,0xf419e0375560,0x198e04ad819f190)⟩

theorem stage05_cert :
    BankCertificate 2429 stage05.reserve 0 stage05.free ∧
      BankCertificate 2429 stage05.reserve 1 stage05.moving :=
  ⟨(rank! 155,131078,0x14e3d9c718,0x3497b73d648), (rank! 905,705210,0x6565aa8c2500,0x284520bda01c6d0)⟩

theorem stage06_cert :
    BankCertificate 2429 stage06.reserve 0 stage06.free ∧
      BankCertificate 2429 stage06.reserve 1 stage06.moving :=
  ⟨(rank! 176,118020,0x9b71248180,0x59c77605030), (rank! 964,711642,0x14a81fc24ee98,0x44de529cb3a79c8)⟩

theorem stage07_cert :
    BankCertificate 2429 stage07.reserve 0 stage07.free ∧
      BankCertificate 2429 stage07.reserve 1 stage07.moving :=
  ⟨(rank! 198,151338,0x1a74c4bad78,0xd03718bdbb0), (rank! 1200,916476,0xa3a9164fbcb40,0xa549c4b55ca8fa0)⟩

theorem stage08_cert :
    BankCertificate 2429 stage08.reserve 0 stage08.free ∧
      BankCertificate 2429 stage08.reserve 1 stage08.moving :=
  ⟨(rank! 238,192914,0x6cc1112f1c,0x4b4675ead190), (rank! 1469,921290,0x17f5cf93949088,0x22f9290b4f5866c8)⟩

theorem stage09_cert :
    BankCertificate 2429 stage09.reserve 0 stage09.free ∧
      BankCertificate 2429 stage09.reserve 1 stage09.moving :=
  ⟨(rank! 248,194774,0x18cf09bb800,0xc99d2e9a480), (rank! 1147,770572,0x52bf9123e7d38,0x9b4cfed39d29738)⟩

theorem stage10_cert :
    BankCertificate 2429 stage10.reserve 0 stage10.free ∧
      BankCertificate 2429 stage10.reserve 1 stage10.moving :=
  ⟨(rank! 334,249868,0x116fd4e2a8dc,0x3432d6ebc9b8), (rank! 1698,879670,0x62622beca61c,0x319f669aba01c804)⟩

theorem stage11_cert :
    BankCertificate 2429 stage11.reserve 0 stage11.free ∧
      BankCertificate 2429 stage11.reserve 1 stage11.moving :=
  ⟨(rank! 300,112222,0x8ca60211d4c,0x54e8c654e57c), (rank! 1872,1145764,0x241358565fef40,0x525b19dc3a0da500)⟩

theorem stage12_cert :
    BankCertificate 2429 stage12.reserve 0 stage12.free ∧
      BankCertificate 2429 stage12.reserve 1 stage12.moving :=
  ⟨(rank! 338,401366,0x467a563178c,0x1bf24a0cd91a8), (rank! 2132,1168150,0x10cc18d32603e0,0xe4d55167decb7800)⟩

theorem stage13_cert :
    BankCertificate 2429 stage13.reserve 0 stage13.free ∧
      BankCertificate 2429 stage13.reserve 1 stage13.moving :=
  ⟨(rank! 356,224890,0x99ec7231090,0x45fbaf70d6c10), (rank! 2034,1164314,0x8e0cfa4afb3b4,0x188d7b32e7479b3f0)⟩

theorem stage14_cert :
    BankCertificate 2429 stage14.reserve 0 stage14.free ∧
      BankCertificate 2429 stage14.reserve 1 stage14.moving :=
  ⟨(rank! 453,367084,0x38649364e780,0xd642bfa2d2cc), (rank! 2234,1495848,0x330d4537d01b30,0xc96a3ffeeb366d58)⟩

theorem stage15_cert :
    BankCertificate 2429 stage15.reserve 0 stage15.free ∧
      BankCertificate 2429 stage15.reserve 1 stage15.moving :=
  ⟨(rank! 472,382854,0x3b8e97b8e068,0x335c3a9dc22e8), (rank! 2855,1749392,0xb5ac4bfb37f598,0x30e888857564ba9f8)⟩

theorem stage16_cert :
    BankCertificate 2429 stage16.reserve 0 stage16.free ∧
      BankCertificate 2429 stage16.reserve 1 stage16.moving :=
  ⟨(rank! 585,178092,0x26097dc10a0,0x9b343a0f3aca0), (rank! 3772,2238492,0x18ca6f6e7f5fd80,0xa3d273049e7510c3c)⟩

theorem stage17_cert :
    BankCertificate 2429 stage17.reserve 0 stage17.free ∧
      BankCertificate 2429 stage17.reserve 1 stage17.moving :=
  ⟨(rank! 716,705950,0x1657e6761fac0,0x1b10d6fe495380), (rank! 4642,2699500,0x5c002502aacd10,0x1d00a8263e5bf6cf20)⟩

theorem stage18_cert :
    BankCertificate 2429 stage18.reserve 0 stage18.free ∧
      BankCertificate 2429 stage18.reserve 1 stage18.moving :=
  ⟨(rank! 627,74248,0x8b1d48513e28,0x1c4618cc3fbe9180), (rank! 3910,1861768,0xc369a8a847718,0x254410c06751ef128c)⟩

theorem stage19_cert :
    BankCertificate 2429 stage19.reserve 0 stage19.free ∧
      BankCertificate 2429 stage19.reserve 1 stage19.moving :=
  ⟨(rank! 905,218960,0x2d3badd163ab0,0x5949961edf8ab0), (rank! 5823,3415922,0xacb869e36630224,0x5d3ea77d1becee6a8c)⟩

theorem stage20_cert :
    BankCertificate 2429 stage20.reserve 0 stage20.free ∧
      BankCertificate 2429 stage20.reserve 1 stage20.moving :=
  ⟨(rank! 1032,556456,0x3b15a6397f200,0x9b28fdbf2199c0), (rank! 6607,3622528,0x45583d0ecb858d8,0xa733e75947e391c138)⟩

theorem stage21_cert :
    BankCertificate 2429 stage21.reserve 0 stage21.free ∧
      BankCertificate 2429 stage21.reserve 1 stage21.moving :=
  ⟨(rank! 555,26642,0x3f3a9d8df268,0x84b6804664d6e1e0), (rank! 3000,1485622,0xcfb4d504564554,0x2c025d1e9a46621984)⟩

private def Checks (ss : List P1_7.Stage) : Prop :=
  ∀ s ∈ ss, BankCertificate 2429 s.reserve 0 s.free ∧ BankCertificate 2429 s.reserve 1 s.moving

private theorem cons {s : P1_7.Stage} {ss : List P1_7.Stage}
    (h : BankCertificate 2429 s.reserve 0 s.free ∧ BankCertificate 2429 s.reserve 1 s.moving)
    (hs : Checks ss) : Checks (s :: ss) :=
  List.forall_mem_cons.mpr ⟨h, hs⟩

theorem certificates : ∀ s ∈ stages,
    BankCertificate 2429 s.reserve 0 s.free ∧ BankCertificate 2429 s.reserve 1 s.moving := by
  change Checks stages
  change Checks [stage00, stage01, stage02, stage03, stage04, stage05, stage06, stage07, stage08, stage09, stage10, stage11, stage12, stage13, stage14, stage15, stage16, stage17, stage18, stage19, stage20, stage21]
  refine cons stage00_cert ?_
  refine cons stage01_cert ?_
  refine cons stage02_cert ?_
  refine cons stage03_cert ?_
  refine cons stage04_cert ?_
  refine cons stage05_cert ?_
  refine cons stage06_cert ?_
  refine cons stage07_cert ?_
  refine cons stage08_cert ?_
  refine cons stage09_cert ?_
  refine cons stage10_cert ?_
  refine cons stage11_cert ?_
  refine cons stage12_cert ?_
  refine cons stage13_cert ?_
  refine cons stage14_cert ?_
  refine cons stage15_cert ?_
  refine cons stage16_cert ?_
  refine cons stage17_cert ?_
  refine cons stage18_cert ?_
  refine cons stage19_cert ?_
  refine cons stage20_cert ?_
  refine cons stage21_cert ?_
  exact fun _ h => (List.not_mem_nil h).elim

theorem stage_bounds {s : P1_7.Stage} (hs : s ∈ stages) {h : ℕ}
    (hlo : 2429 ≤ h) (hraw : h ≤ 131071) :
    (HighCore82258.WidthGuard h s.reserve s.free.shape ∧
      HighCore82258.debit h s.free < HighCore82258.gain h s.reserve s.free.shape 0 ∧
      s.free.shape.U < P3.p) ∧
    (HighCore82258.WidthGuard h s.reserve s.moving.shape ∧
      HighCore82258.debit h s.moving < HighCore82258.gain h s.reserve s.moving.shape 1 ∧
      s.moving.shape.U < P3.p) := by
  obtain ⟨hf, hm⟩ := certificates s hs
  exact ⟨of_certificate hlo hraw hf, of_certificate hlo hraw hm⟩

#print axioms certificates
end KoalaH2429Stages
