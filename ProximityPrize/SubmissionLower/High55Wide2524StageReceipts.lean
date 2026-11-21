import ProximityPrize.SubmissionLower.HighCore82268Stages
import ProximityPrize.SubmissionLower.High55Wide2524Data

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace High55Wide2524Stages

open High55Wide2524
open HighCore82268Stages (BankCertificate checked of_certificate)
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
  | h2524 =>
    rw [stages]
    refine cons (bank! 102,147701,0x5745824f28,0x4ac2776db0) (bank! 490,379651,0x868c3acf39d0,0x138ce6051a5508) ?_
    refine cons (bank! 84,118111,0x192d60a130,0x350d17c23d4) (bank! 563,472771,0xfb63b3622820,0x2216154cea8040) ?_
    refine cons (bank! 152,185791,0x11731014714,0xdce1bfad88) (bank! 618,464131,0x17697dac4cd50,0x3571ad5d013848) ?_
    refine cons (bank! 170,205285,0x1d761cd550c,0x15b9b853fe8) (bank! 657,353731,0x1b4b621253d28,0x4d1026b58b1880) ?_
    refine cons (bank! 182,271509,0x2e03ffc33c8,0x24a2cad01a8) (bank! 775,721643,0x21f3f9064d910,0xa3eb91c1642c38) ?_
    refine cons (bank! 195,204138,0x452b1c28240,0x4cd21c87520) (bank! 906,697968,0x7878150f00d80,0x1831ce2d34d96d0) ?_
    refine cons (bank! 249,252524,0x854d81c6900,0xf1d9b771c80) (bank! 1192,834195,0x124f01eeb9ffc4,0x577ebfb993298f4) ?_
    refine cons (bank! 268,303155,0xc7b14e8a140,0x2a1d0f1be410) (bank! 1447,998107,0x1a5d408345ddec,0xe7221916b9146d4) ?_
    refine cons (bank! 503,458318,0xa4f985aa3430,0xc792b27f1030) (bank! 1700,0x13eef7,0x5ceaad8180dec0,0x278244c69bdc8ca0) ?_
    refine cons (bank! 292,220391,0x11d9ae81be38,0x192a4c847fbfb8) (bank! 1829,532243,0x4b11380f94f400,0x415f7c3472e6ec38) ?_
    refine cons (bank! 410,331209,0x3d9b7d7f0a5c,0xf571f8ce67f0) (bank! 2103,0x1daa1d,0x85e8c4610158a8,0x5fdad12ba1bafe40) ?_
    refine cons (bank! 560,215123,0xd606693f3560,0x4f32cb5f14bd0) (bank! 2945,0x2503f2,0x3538df45f375a54,0x1fb40d0b2b22504f0) ?_
    refine cons (bank! 524,280291,0xcf290b801c50,0x2855e1162b097f4) (bank! 2989,0x258a16,0x33364d1b23c3440,0x488183d2a373a0490) ?_
    refine cons (bank! 693,665452,0x1682b1cbcc980,0x10bb75a9585480) (bank! 3740,0x294649,0x8ab3b03a9bb9174,0x6a4f0eba1f3b25250) ?_
    refine cons (bank! 732,202695,0x20f8470a85d00,0x1db1fe81017dd130) (bank! 3898,0x177fe2,0x6f5a1834b575d30,0x1a6752c291bbed2a04) ?_
    refine cons (bank! 591,251210,0xc950d6706638,0x13c82b31452728d8) (bank! 2818,0x1abcef,0x2c4956abd24888c,0x115df3b47aaec3f32c) ?_
    refine cons (bank! 1117,991564,0x111bbafafbd120,0x97469404515120) (bank! 5951,0x3d5a61,0x3908298dc304c01c,0x41abea4c614272a13c) ?_
    refine cons (bank! 112,116315,0x51e30f7cc0,0x75d3bab1c8) (bank! 528,217922,0xcc7eccfcf6c0,0x76cd0112418020) ?_
    refine cons (bank! 120,162147,0x8556b847d8,0xb1977e752c) (bank! 760,172168,0x2b0145fb95ff0,0x1912a306ab61930) ?_
    refine cons (bank! 127,156650,0xa0d0f889f0,0x11067baa6e0) (bank! 1503,710483,0x1fa36d897b18d0,0x4713a2da3563ec48) ?_
    refine cons (bank! 135,202482,0xf48edcb340,0x186731fbd10) (bank! 922,511497,0x5321d46499e74,0xf3bebae98a08a0) ?_
    refine cons (bank! 154,268257,0xf5e9e9a950,0x2d90eebeee0) (bank! 686,388120,0x151e11a2e0b00,0xcbcebe91e95800) ?_
    refine cons (bank! 180,148659,0x280c6aab5e0,0x698984905e0) (bank! 974,585772,0x5ea1c931e8d60,0x32c3cc3e2fe1960) ?_
    refine cons (bank! 224,228431,0x5bdcaa6be94,0xf85aaa02e10) (bank! 1384,667636,0x1382bf39d0a564,0x45460ff3fab97bc8) ?_
    refine cons (bank! 234,186949,0x6bd3edeb6b0,0x24573e256b58) (bank! 1556,435502,0x4557797a321294,0x11644ce4691d6678) ?_
    refine cons (bank! 264,302955,0x9e5d4b1b4d8,0x100d07ddf028) (bank! 2512,0x1ea592,0x11c9bd761733148,0x4f4858580f5f2fd4) ?_
    refine cons (bank! 347,170518,0x1a9604a902c0,0xc5e3f7cb7a78) (bank! 3322,0x1b1f93,0x45f8382a79b9338,0x162f8f4c566c52240) ?_
    refine cons (bank! 352,232143,0x2822da0db0e0,0x18040564f39c8) (bank! 1563,308004,0x3cb5dd62815aac,0x16c6e08b936d5ca64) ?_
    refine cons (bank! 370,312213,0x38c4378b6a30,0x40bb85672420) (bank! 1418,167196,0x30732698344c20,0x15bb45d4ecc65ec0) ?_
    refine cons (bank! 440,191619,0x6f5a67180b60,0x6bf131da8a930) (bank! 3480,534585,0x4586b95a0478988,0x2f4332d2ee0e5b42c) ?_
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
end High55Wide2524Stages
