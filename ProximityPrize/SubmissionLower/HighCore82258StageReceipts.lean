-- Ported from public PR657, e07f14a81dfe2cf1bda985e67040ad4d31fe81ab, HighCore82258StageReceipts.lean.
import ProximityPrize.SubmissionLower.KoalaH2430StageReceipts
import ProximityPrize.SubmissionLower.KoalaH2429StageReceipts

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82258Stages

open HighCore82258
open K1_14 (Shape)
open P3 (p)

private def Checks (lo : ℕ) (ss : List Stage) : Prop :=
  ∀ s ∈ ss,BankCertificate lo s.reserve 0 s.free ∧ BankCertificate lo s.reserve 1 s.moving
private theorem nil {lo:ℕ} : Checks lo []:=fun _ hs => (List.not_mem_nil hs).elim
private theorem cons {lo : ℕ} {s : Stage} {ss : List Stage}
    (hf:BankCertificate lo s.reserve 0 s.free)
    (hm:BankCertificate lo s.reserve 1 s.moving)
    (ht:Checks lo ss):Checks lo (s::ss) :=
  List.forall_mem_cons.mpr ⟨⟨hf,hm⟩,ht⟩
set_option quotPrecheck false

local notation "bank!" kk "," ww "," zz "," dd =>
  checked (k := kk) (w := ww) (z := zz) (d := dd)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem certificates (b : Band) : Checks (start b) (stages b) := by
  cases b with
  | h2367 =>
    rw [stages]
    refine cons (bank! 98,113240,0xffc7e6504,0x8e2ec3f538) (bank! 579,397092,0x758a98bd5608,0x5062ea3c7c5518) ?_
    refine cons (bank! 108,81110,0x1eb5705980,0xdf5b115540) (bank! 605,465234,0x1f60778f1bc4,0x7a9dcce3943ccc) ?_
    refine cons (bank! 120,151452,0xbab15ee18,0x1313beeed88) (bank! 726,544144,0x5f1cb74eb580,0xd300fdc3aad070) ?_
    refine cons (bank! 130,119322,0x13ccd9700,0x1bba9dbab00) (bank! 690,493546,0x64a607389d18,0x11615c273127618) ?_
    refine cons (bank! 144,112260,0x368f8610a0,0x251c94fb220) (bank! 729,379612,0x1574d3b8c7430,0x18a45ab17604ec0) ?_
    refine cons (bank! 155,131366,0xa0e01ad9f0,0x340783d4d20) (bank! 905,707002,0x16119a3a2f200,0x27340e26a187a10) ?_
    refine cons (bank! 176,118342,0x148d34c1e0,0x58c2577e0f0) (bank! 964,713546,0x12c6a04ebee98,0x42d9d5a7ef1de78) ?_
    refine cons (bank! 198,151692,0x23e0d06faa8,0xcdc0f3837e0) (bank! 1200,918840,0x6fa747c4da0ec,0xa0f18878be0767c) ?_
    refine cons (bank! 238,193324,0xa96146657c,0x49f028c9a690) (bank! 1469,924172,0x30b81b6534638,0x21f666e6c41a0f88) ?_
    refine cons (bank! 248,195228,0x3ce62a9ff40,0xc85551e3160) (bank! 1147,772832,0x2ca89ccca843c,0x96e2889dc9484bc) ?_
    refine cons (bank! 300,112740,0x7f3e0185220,0x5401b26f3be0) (bank! 1872,1149440,0x4517f55cf1d814,0x505ca3979c818e08) ?_
    refine cons (bank! 348,233680,0x122af304083c,0x4f63f55217c0) (bank! 1886,1018600,0xb6b8854c84d0,0x51a196d826b00450) ?_
    refine cons (bank! 319,337548,0xf8a7ff4178,0x156b66ca580c8) (bank! 2011,1098268,0x12faece81ee948,0xa90034ae7af9f53c) ?_
    refine cons (bank! 356,225472,0x255f6529530,0x44588b8fc8e50) (bank! 2034,1168268,0x2ea6e807e41970,0x178708d008d0eb6c0) ?_
    refine cons (bank! 472,417678,0x29fb1eba9adc,0x16105a8ea90bc) (bank! 2482,1642358,0xc80da78eb07da4,0x16683a4c85924f348) ?_
    refine cons (bank! 472,383644,0x443ac5154bb8,0x32d5b53b1a518) (bank! 2855,1754968,0x15669febafe96b0,0x2fa600173c1406008) ?_
    refine cons (bank! 585,179060,0x436a1c947580,0x999eec07c5800) (bank! 3772,2245860,0x335080eda9b008c,0x9ff6861932d7d9ba4) ?_
    refine cons (bank! 795,768324,0x73ce96fc14a0,0x24d1619c152be0) (bank! 4835,2854632,0x20e71aa3b606158,0x26ee29b5a450e5c8f8) ?_
    refine cons (bank! 627,75220,0x5c6fe80711c0,0x16e07ceed3376470) (bank! 3910,1869340,0x121512ddd2164c8,0x23c87a6d5af0fc3770) ?_
    refine cons (bank! 905,220432,0x178e06d3a52c0,0x585b5938438840) (bank! 5824,3427272,0xbc80e197ddcab98,0x5b03bcdf7193e066b8) ?_
    refine cons (bank! 1097,611814,0x2497ea1b49da8,0xe3ccb5afb622c8) (bank! 6607,3596514,0x2a906822b37e8d4,0xcf00655b94b3d82208) ?_
    refine cons (bank! 555,27506,0x20746c473de0,0x4aff02736735b758) (bank! 3000,1491402,0x17d1aa0d3ae08,0x2871fce6064036531c) ?_
    exact nil
  | h2430 => exact KoalaH2430Stages.certificates
  | h2429 | h2429B => exact KoalaH2429Stages.certificates

theorem stage_bounds (b : Band) {s : Stage} (hs : s ∈ stages b)
    {h:ℕ} (hl:start b≤h) (hh:h≤131071) :
    (WidthGuard h s.reserve s.free.shape ∧
      debit h s.free < gain h s.reserve s.free.shape 0 ∧ s.free.shape.U < p) ∧
    (WidthGuard h s.reserve s.moving.shape ∧
      debit h s.moving < gain h s.reserve s.moving.shape 1 ∧ s.moving.shape.U < p):=by
  obtain ⟨hf,hm⟩:=certificates b s hs
  exact ⟨of_certificate hl hh hf,of_certificate hl hh hm⟩

#print axioms stage_bounds
end HighCore82258Stages
