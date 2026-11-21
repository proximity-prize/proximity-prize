import ProximityPrize.SubmissionLower.HighCore82209Stages

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82209Stages

open HighCore82209
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
    refine cons (bank! 102,135040,0x7a9bd66d0,0x75f40206d8) (bank! 485,370540,0x6a8435b9370,0x1ef47145537078) ?_
    refine cons (bank! 112,102723,0x2b5aedbc60,0xb54db44980) (bank! 497,311948,0x5185f2acf1e8,0x31064fe7e05318) ?_
    refine cons (bank! 124,172846,0x53526e1330,0x1002165a7b8) (bank! 564,320211,0x5404f655ea70,0x48fe3e651f9d58) ?_
    refine cons (bank! 135,191749,0x6a017ded50,0x16cb7dc6f28) (bank! 590,387674,0x1f446f358200,0x6b9e381ae7b860) ?_
    refine cons (bank! 148,133157,0xb223416d90,0x1f30e6abe10) (bank! 640,553587,0x64ad23dc75b4,0x9983753826a758) ?_
    refine cons (bank! 160,203280,0xe8f84ab380,0x29f98505940) (bank! 715,483025,0x157afccc8e180,0xd6a4bb824e2500) ?_
    refine cons (bank! 161,69853,0xa9e0bdc24,0x40bc705b1cc) (bank! 803,409803,0x2396d2088a20,0x130c0aa8308e8a0) ?_
    refine cons (bank! 198,146795,0x1e7310b7d0,0xa88d9ae7ad0) (bank! 942,621785,0x3be4f9f8181a0,0x355eb479c0c1ad8) ?_
    refine cons (bank! 236,85598,0x2f66b07a4bc,0x351fc15c4e0c) (bank! 1232,1001293,0x31c138d6340c0,0xc11f9ea2921e9c0) ?_
    refine cons (bank! 297,340482,0x4b478722390,0x198365ba3fb8) (bank! 1122,568357,0x69e6bae40a840,0x8230aaef45a4440) ?_
    refine cons (bank! 300,267087,0x2834b24cf80,0xb65d4acb1c2c) (bank! 1644,1244997,0x1f8921a97d8100,0x2db1bb46c718e4a8) ?_
    refine cons (bank! 363,217421,0x3540a0f2120,0x2260baba7df48) (bank! 2011,1394241,0x134eb542ad62d8,0x7ff2253c669c4610) ?_
    refine cons (bank! 360,229560,0x1582ffdc3eb0,0x8538a4f87bd70) (bank! 1767,1118005,0x2306e575cf7944,0xe8237271da4ea5d4) ?_
    refine cons (bank! 594,623808,0x825a3d70d4a0,0x7c8d7dd4d8fd0) (bank! 2808,1666623,0x7e8abe4eb1bde0,0x31feae76914ea43f8) ?_
    refine cons (bank! 847,689283,0x1ebbb78ee6f80,0x2839cf018e31e0) (bank! 4150,2475513,0x464eec78f9224f4,0x1164c1572d2bf73168) ?_
    refine cons (bank! 1077,646884,0x142fa061e4198,0x9f04351ed23c18) (bank! 5720,3617234,0x1003344fa1d9b790,0x479d7403a717fb4198) ?_
    refine cons (bank! 1610,1256387,0x9de7ad9eeb600,0x3b2781dd9755678) (bank! 8389,5181742,0x4cc509b42e38735c,0x1d10d1c2f2df1fd3498) ?_
    exact nil
  | h2395 =>
    rw [stages]
    refine cons (bank! 102,138979,0x20cd23b9b0,0x5c49708750) (bank! 489,414556,0x36f11a1eb700,0x12feab1a8c2820) ?_
    refine cons (bank! 109,133132,0xc97feb700,0x92a63e2c50) (bank! 479,308305,0x4666b232b810,0x1ad9cabed8d288) ?_
    refine cons (bank! 120,152386,0xd65b51268,0xd4047181b8) (bank! 535,423735,0x3eea9c059ec0,0x29613220c42c80) ?_
    refine cons (bank! 131,171640,0x3b11880c10,0x12d68c3d260) (bank! 571,336243,0x74d10f638858,0x3c5d9916f77d74) ?_
    refine cons (bank! 142,190894,0x7ce5c9be00,0x1a11ad1d700) (bank! 608,428686,0xa8221f155b00,0x55f9dc88589800) ?_
    refine cons (bank! 151,107630,0x7348bd4d48,0x240cab29028) (bank! 725,483344,0x44ee2c6ff130,0x85651147a10030) ?_
    refine cons (bank! 150,231516,0x1cb63bdc60,0x376ef9ef160) (bank! 791,622818,0x220f33c284258,0xbdddeec06d3c68) ?_
    refine cons (bank! 198,153698,0x231fc00b010,0x8909c5e3210) (bank! 966,628492,0x3128bf12ad21c,0x220323610449090) ?_
    refine cons (bank! 227,171989,0x172e3d3fb60,0x2a1d2c55b2c0) (bank! 1181,824337,0x5f0aff940e60c,0x71e6bc858a7c874) ?_
    refine cons (bank! 307,304559,0xa4dc28cf374,0x27e0edf8a9ac) (bank! 1321,844876,0xa130a5eaf5e30,0xab9bc6ce147e990) ?_
    refine cons (bank! 295,200516,0x4a603097b28,0x96fac2682758) (bank! 1547,1064765,0xdf02eab37972c,0x1acab7dbff963cb4) ?_
    refine cons (bank! 363,229043,0x6cf54f66fd8,0x19d0e1ca71490) (bank! 2029,1364641,0x4ce82dcff53890,0x526750cc4020d310) ?_
    refine cons (bank! 342,213054,0x6b16412f1d0,0x8b5f9bc34cc300) (bank! 1692,1113764,0xb5de23b462b08,0x8fcccfb5881c72a0) ?_
    refine cons (bank! 387,331749,0x1820b5725784,0xc4e97d393113b0) (bank! 1720,952120,0x27d05d9419c2a0,0x2a953576b79fb4550) ?_
    refine cons (bank! 741,606390,0xb5a307337968,0x8d69a025cfef8) (bank! 3123,2070404,0x18d0e6cff5581f8,0x2a53a4fd190271ef0) ?_
    refine cons (bank! 884,609697,0x85ef1ce54210,0x2d876bf96830b0) (bank! 4817,3201120,0x7f388c3bac38f68,0x120e0e1d2c93eba7c4) ?_
    refine cons (bank! 1073,850018,0x61d515edc1040,0x72d44f239bd340) (bank! 5782,3786502,0x5403f7f5bd177c0,0x2dada1dbaaa1109060) ?_
    refine cons (bank! 1444,1166152,0xa1829ec72f244,0x1ba3ac3b884c5b8) (bank! 7608,4858815,0x1b0c2e2fc6c79098,0xb47c3456671fa882ec) ?_
    exact nil
  | h7773 =>
    rw [stages]
    refine cons (bank! 16,129815,0x78e4cf0,0x25e61b0) (bank! 29,146356,0x8014d9a0,0x1e118c80) ?_
    refine cons (bank! 30,171901,0xf6671b20,0xd947450) (bank! 54,271644,0x3e2f0bac8,0x126e25960) ?_
    refine cons (bank! 48,245054,0x14840d870,0x5d249030) (bank! 90,464588,0x29bb379e00,0xa35cd9aa0) ?_
    refine cons (bank! 76,313680,0x16bbf63c40,0x2fec3bd68) (bank! 142,632957,0x1221655a8e0,0x6002b73ec8) ?_
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
end HighCore82209Stages
