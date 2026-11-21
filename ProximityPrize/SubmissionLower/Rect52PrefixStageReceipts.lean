import ProximityPrize.SubmissionLower.Rect52PrefixStages
import ProximityPrize.SubmissionLower.Rect52PrefixData

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace Rect52PrefixStages

open Rect52Prefix
open Rect52PrefixStages (BankCertificate checked of_certificate)
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
  | h2391 =>
    rw [stages]
    refine cons (bank! 98,111390,0x16a6c8c9bc,0x8be66b9f58) (bank! 529,343405,0x52945c858050,0x33d356fbdf4314) ?_
    refine cons (bank! 108,79143,0x2a45d954f8,0xd94cce8a08) (bank! 557,333683,0x19b121faf424,0x51a04a75d60464) ?_
    refine cons (bank! 116,124351,0x2fe88c4750,0x145e0c71400) (bank! 673,385361,0x868df238e0ac,0x86175408ed1bfc) ?_
    refine cons (bank! 127,143329,0x1b44429dc0,0x1d1e1ba9000) (bank! 743,368229,0x606313235dcc,0xcf13b54ffc423c) ?_
    refine cons (bank! 148,130060,0x380ea8aac0,0x33d72654bd8) (bank! 790,556155,0x128aa1f946924,0x171575f4d5d779c) ?_
    refine cons (bank! 167,194246,0xd2a3114b48,0x5ac43a4ad58) (bank! 931,624341,0x1c2d9a585382c,0x2c559609db4f02c) ?_
    refine cons (bank! 198,148730,0x1ffe21c6e58,0xbe0078aca60) (bank! 1138,650400,0x7f98e33677038,0x680ef331263e528) ?_
    refine cons (bank! 236,87633,0x4313f42e038,0x400a707402f8) (bank! 1433,0x10ee31,0x35be0154d9b80,0x1689791299350000) ?_
    refine cons (bank! 286,324464,0x70770fadc58,0x16f63ccae80c) (bank! 1447,735389,0xb14ce0c06efb8,0xffaf01a53021508) ?_
    refine cons (bank! 288,199189,0x7b7d8663020,0xd33fe509d8a0) (bank! 1829,0x140ddd,0xe93956973508,0x49f92b26c170bfb8) ?_
    refine cons (bank! 363,220021,0x14ace9b5c84c,0x2cebdc24c449c) (bank! 2328,0x19e507,0xa14e4264f3aea8,0xf45913aab7fc14d0) ?_
    refine cons (bank! 360,231905,0x1412c5865b20,0xf7c08cb7884a0) (bank! 1970,691235,0x1f14288a44c27c,0x1699aed948af7c1f4) ?_
    refine cons (bank! 408,138561,0x174840510000,0x39c61e08958000) (bank! 2089,687991,0x1f1e000c363de8,0x49547ce167fffc93c) ?_
    refine cons (bank! 613,351627,0x57f9925bded8,0x720ebab52f5b0) (bank! 2941,0x10b483,0x11c0fac7fe6a7f4,0x4c88c89f1387f9a78) ?_
    refine cons (bank! 833,337903,0x294603fbea238,0x3067ad9fd46a6c) (bank! 4677,0x1954e5,0x39067bb8bb18670,0x20ab02aad7f4b55318) ?_
    refine cons (bank! 1284,770537,0xe6e02e89dd570,0x10d178c45b1d860) (bank! 7025,0x541c87,0x2743af6689329a5c,0xd65065642e6610c670) ?_
    refine cons (bank! 1613,681989,0x9c20582f583b4,0x51ea5737b5b69c8) (bank! 9432,0x3394d7,0x6425d9a1d8e2cfc,0x3c517579c78a5c61514) ?_
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
end Rect52PrefixStages
