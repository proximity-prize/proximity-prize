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
  | h2405 =>
    rw [stages]
    refine cons (bank! 102,139259,0x3afd4cf030,0x5f42ed71e0) (bank! 490,338519,0x666091d72d84,0x15f3f40f8d2ce4) ?_
    refine cons (bank! 84,111412,0x17e4992980,0x238e5ec82c40) (bank! 562,425857,0x104f0870fae10,0x254aa5effa6900) ?_
    refine cons (bank! 152,173639,0x12965556c48,0xf6a2ecd8a0) (bank! 618,412751,0x1230ec04a4d48,0x39a99bfd7508d8) ?_
    refine cons (bank! 170,191866,0x1cd6c2df208,0x17db7d7c3d0) (bank! 657,299201,0x15473efbc52ec,0x52e18ce37ef0a0) ?_
    refine cons (bank! 182,257579,0x2e3a18cba40,0x283ef6b7a38) (bank! 775,657950,0x2914a9fdfd668,0xac5b326d930574) ?_
    refine cons (bank! 195,189816,0x294cb084d30,0x555577a63d0) (bank! 906,623817,0x642c6ec9a7b78,0x191f01e15a5b9d4) ?_
    refine cons (bank! 249,234877,0xaa820cd7580,0x105750791dc0) (bank! 1192,737175,0xedc16693a6064,0x589f501b9132894) ?_
    refine cons (bank! 268,285123,0x79d79803790,0x2e5f0df484b8) (bank! 1447,880829,0x229501a32c2a74,0xe87083b59ff4180) ?_
    refine cons (bank! 503,422268,0x718f4e9562b8,0xcb7d8f4da930) (bank! 1699,0x11d90d,0x588e205ff96d50,0x277944f7d4bacaf8) ?_
    refine cons (bank! 292,202954,0x153eb623b310,0x4413c7ef848778) (bank! 1828,384886,0x420c99e1aea488,0x412b6769f8795e40) ?_
    refine cons (bank! 410,304371,0x3629e54bb4d8,0x10115b04960e8) (bank! 2103,0x1b169c,0x86a125886867d8,0x5ea7356b033bda04) ?_
    refine cons (bank! 560,179486,0xc9ab527865cc,0x51aea37ff928c) (bank! 2944,0x216ab5,0x2c1f70023d9c710,0x1ecc0fdac6da746c0) ?_
    refine cons (bank! 524,250807,0xb3d2df6da4f0,0x3f7a66e2be99cc8) (bank! 2988,0x21ee9b,0x314e85a0ba4431c,0x45c7d0112065b605c) ?_
    refine cons (bank! 693,622598,0x2415386fa18c0,0x110b2befa04360) (bank! 3739,0x24b630,0x67a6c0c79a0fa40,0x6771866597f3ca8a0) ?_
    refine cons (bank! 732,162424,0x318eb7acd0218,0x2ae9d6f2006200c8) (bank! 3897,0x12ce7b,0x7051ec21450daac,0x19512eae84d9c224a0) ?_
    refine cons (bank! 591,218485,0x135ecbe134958,0x2c435e2549df4988) (bank! 2817,0x1760d6,0x26801fb4cffe9f8,0x104db1269753651c64) ?_
    refine cons (bank! 1117,923244,0xdc7574e3f02c8,0x973d3ec0eba468) (bank! 5950,0x361aab,0x1e27e2fae57347d8,0x3f43058bd7f1316298) ?_
    refine cons (bank! 112,107264,0x65cd4d0a48,0x93b20be9e8) (bank! 528,173710,0x7f95bfb20300,0xbe4b9d79788598) ?_
    refine cons (bank! 120,152676,0x86122e1c2c,0xdc6462e66c) (bank! 760,108531,0x2a4b76ccdbd4c,0x22a46c1e8af8f94) ?_
    refine cons (bank! 127,146829,0x926b14a6e0,0x1540561beb8) (bank! 1502,584833,0x2c9104fd053428,0x76dc80fa24db86f8) ?_
    refine cons (bank! 135,192241,0xc3cc946ee4,0x1e2d0652db8) (bank! 921,434910,0x7426421153790,0xf8616235f251c0) ?_
    refine cons (bank! 154,256917,0x1a3d1093938,0x36b795bf398) (bank! 686,331882,0x1c50ce08f5ba0,0xe840ebc86060dc) ?_
    refine cons (bank! 180,135821,0x2a7245898c8,0x7c2e8b82668) (bank! 973,506119,0x8a6c72a4533b0,0x38cf5a3eb5b3cb0) ?_
    refine cons (bank! 224,212877,0x460cd0da200,0x1160091b6a30) (bank! 1383,554362,0x176371a44545a8,0x6ab85e7514ae5488) ?_
    refine cons (bank! 234,171262,0x46371d34748,0x2a324e5bfd50) (bank! 1556,307934,0x2ad2af8a25f2e0,0x1131c23398151c70) ?_
    refine cons (bank! 264,284062,0x82e651b02b0,0x111ebe36a0e0) (bank! 2512,0x1b79d1,0x159087d241bd5a4,0x4da95ba9201bbe40) ?_
    refine cons (bank! 347,148209,0x2920eeb2fce4,0xd666a3df4758) (bank! 3321,0x16f594,0x317f0486133eda8,0x15cba2f9677816d28) ?_
    refine cons (bank! 352,210149,0x196e766d2e48,0x1aa5181d8c8e8) (bank! 1562,183488,0x2b35867f1239e4,0x1e52b757232b0e90c) ?_
    refine cons (bank! 370,286096,0x2caa04936874,0x432ab7ea9938) (bank! 1417,52102,0x24ffdcdcb51c80,0x158b708c6c3acdc0) ?_
    refine cons (bank! 440,165096,0x4e9cea792be8,0x7624e14a3aa58) (bank! 3479,250665,0x60849a7709647a0,0x2dce541ad80757f64) ?_
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
