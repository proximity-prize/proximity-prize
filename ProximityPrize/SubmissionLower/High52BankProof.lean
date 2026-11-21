import ProximityPrize.SubmissionLower.High52Source
import ProximityPrize.SubmissionLower.HighCore82219Moments11

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace High52BankProof

open P3_7_1 (BankOK checked)
open P1_7_1 (groupedPoleMoment)
open P1_7_1_3 (momentEstimate blockEstimate block_append)
open High52
open HighCore82219BankProof

set_option maxHeartbeats 6000000

local notation "pass!" depth "," grade "," deriv "," nodes "," moment ";" witness =>
  checked _ (m := depth) (B := grade) (J := deriv) (N := nodes) (M := moment)
    rfl rfl rfl rfl rfl (by decide) (by decide) rfl (by decide) witness

private theorem chunk2106 : blockEstimate 9956 2106 2106 155 = 0x1731c0263 := by decide +kernel
private theorem chunk2261 : blockEstimate 9956 2106 2261 155 = 0x9e6a9d04f := by decide +kernel
private theorem chunk2416 : blockEstimate 9956 2106 2416 155 = 0x1a60e73c16 := by decide +kernel
private theorem chunk2571 : blockEstimate 9956 2106 2571 155 = 0x327a9e1fe5 := by decide +kernel
private theorem chunk2726 : blockEstimate 9956 2106 2726 155 = 0x51cc9855e9 := by decide +kernel
private theorem chunk2881 : blockEstimate 9956 2106 2881 155 = 0x77ef9fb84f := by decide +kernel
private theorem chunk3036 : blockEstimate 9956 2106 3036 155 = 0xa47c7e2144 := by decide +kernel
private theorem chunk3191 : blockEstimate 9956 2106 3191 155 = 0xd70bfd6af5 := by decide +kernel
private theorem chunk3346 : blockEstimate 9956 2106 3346 155 = 0x10f36e76f8f := by decide +kernel
private theorem chunk3501 : blockEstimate 9956 2106 3501 155 = 0x14c9606093f := by decide +kernel
private theorem chunk3656 : blockEstimate 9956 2106 3656 155 = 0x18ec2231232 := by decide +kernel
private theorem chunk3811 : blockEstimate 9956 2106 3811 155 = 0x1d554086495 := by decide +kernel
private theorem chunk3966 : blockEstimate 9956 2106 3966 155 = 0x21fe47fda95 := by decide +kernel
private theorem chunk4121 : blockEstimate 9956 2106 4121 155 = 0x26df802e8cf := by decide +kernel
private theorem chunk4276 : blockEstimate 9956 2106 4276 155 = 0x2bc56a0a5e5 := by decide +kernel
private theorem chunk4431 : blockEstimate 9956 2106 4431 155 = 0x307492d1f6a := by decide +kernel
private theorem chunk4586 : blockEstimate 9956 2106 4586 155 = 0x34e94626f4d := by decide +kernel
private theorem chunk4741 : blockEstimate 9956 2106 4741 155 = 0x3923840958e := by decide +kernel
private theorem chunk4896 : blockEstimate 9956 2106 4896 155 = 0x3d234c7922d := by decide +kernel
private theorem chunk5051 : blockEstimate 9956 2106 5051 155 = 0x40e89f7652a := by decide +kernel
private theorem chunk5206 : blockEstimate 9956 2106 5206 155 = 0x44737d00e85 := by decide +kernel
private theorem chunk5361 : blockEstimate 9956 2106 5361 155 = 0x47c3e518e3e := by decide +kernel
private theorem chunk5516 : blockEstimate 9956 2106 5516 155 = 0x4ad9d7be455 := by decide +kernel
private theorem chunk5671 : blockEstimate 9956 2106 5671 155 = 0x4db554f10ca := by decide +kernel
private theorem chunk5826 : blockEstimate 9956 2106 5826 155 = 0x50565cb139d := by decide +kernel
private theorem chunk5981 : blockEstimate 9956 2106 5981 155 = 0x52bceefecce := by decide +kernel
private theorem chunk6136 : blockEstimate 9956 2106 6136 155 = 0x54e90bd9c5d := by decide +kernel
private theorem chunk6291 : blockEstimate 9956 2106 6291 155 = 0x56dab34224a := by decide +kernel
private theorem chunk6446 : blockEstimate 9956 2106 6446 155 = 0x5891e537e95 := by decide +kernel
private theorem chunk6601 : blockEstimate 9956 2106 6601 155 = 0x5a0ea1bb13e := by decide +kernel
private theorem chunk6756 : blockEstimate 9956 2106 6756 155 = 0x5b50e8cba45 := by decide +kernel
private theorem chunk6911 : blockEstimate 9956 2106 6911 155 = 0x5c58ba699aa := by decide +kernel
private theorem chunk7066 : blockEstimate 9956 2106 7066 155 = 0x5d261694f6d := by decide +kernel
private theorem chunk7221 : blockEstimate 9956 2106 7221 155 = 0x5db8fd4db8e := by decide +kernel
private theorem chunk7376 : blockEstimate 9956 2106 7376 155 = 0x5e116e93e0d := by decide +kernel
private theorem chunk7531 : blockEstimate 9956 2106 7531 155 = 0x5e2f6a676ea := by decide +kernel
private theorem chunk7686 : blockEstimate 9956 2106 7686 155 = 0x5e12f0c8625 := by decide +kernel
private theorem chunk7841 : blockEstimate 9956 2106 7841 155 = 0x5dbc01b6bbe := by decide +kernel
private theorem chunk7996 : blockEstimate 9956 2106 7996 155 = 0x5d2a9d327b5 := by decide +kernel
private theorem chunk8151 : blockEstimate 9956 2106 8151 155 = 0x5c5ec33ba0a := by decide +kernel
private theorem chunk8306 : blockEstimate 9956 2106 8306 155 = 0x5b5873d22bd := by decide +kernel
private theorem chunk8461 : blockEstimate 9956 2106 8461 155 = 0x5a17aef61ce := by decide +kernel
private theorem chunk8616 : blockEstimate 9956 2106 8616 155 = 0x589c74a773d := by decide +kernel
private theorem chunk8771 : blockEstimate 9956 2106 8771 155 = 0x56e6c4e630a := by decide +kernel
private theorem chunk8926 : blockEstimate 9956 2106 8926 155 = 0x54f69fb2535 := by decide +kernel
private theorem chunk9081 : blockEstimate 9956 2106 9081 155 = 0x52cc050bdbe := by decide +kernel
private theorem chunk9236 : blockEstimate 9956 2106 9236 155 = 0x5066f4f2ca5 := by decide +kernel
private theorem chunk9391 : blockEstimate 9956 2106 9391 155 = 0x4dc76f671ea := by decide +kernel
private theorem chunk9546 : blockEstimate 9956 2106 9546 155 = 0x4aed7468d8d := by decide +kernel
private theorem chunk9701 : blockEstimate 9956 2106 9701 155 = 0x47d903f7f8e := by decide +kernel
private theorem chunk9856 : blockEstimate 9956 2106 9856 155 = 0x448a6ce8a4f := by decide +kernel
private theorem chunk10011 : blockEstimate 9956 2106 10011 155 = 0x4111c38dbb0 := by decide +kernel
private theorem chunk10166 : blockEstimate 9956 2106 10166 155 = 0x3d88da65a62 := by decide +kernel
private theorem chunk10321 : blockEstimate 9956 2106 10321 155 = 0x39f6177ccf6 := by decide +kernel
private theorem chunk10476 : blockEstimate 9956 2106 10476 155 = 0x365e09bd437 := by decide +kernel
private theorem chunk10631 : blockEstimate 9956 2106 10631 155 = 0x32c521b60c9 := by decide +kernel
private theorem chunk10786 : blockEstimate 9956 2106 10786 155 = 0x2f2fb193bed := by decide +kernel
private theorem chunk10941 : blockEstimate 9956 2106 10941 155 = 0x2ba1ed2734c := by decide +kernel
private theorem chunk11096 : blockEstimate 9956 2106 11096 155 = 0x281fe9df567 := by decide +kernel
private theorem chunk11251 : blockEstimate 9956 2106 11251 155 = 0x24ad9ecf2e5 := by decide +kernel
private theorem chunk11406 : blockEstimate 9956 2106 11406 155 = 0x214ee4a79ab := by decide +kernel
private theorem chunk11561 : blockEstimate 9956 2106 11561 155 = 0x1e0775be2a2 := by decide +kernel
private theorem chunk11716 : blockEstimate 9956 2106 11716 155 = 0x1adaee05c17 := by decide +kernel
private theorem chunk11871 : blockEstimate 9956 2106 11871 155 = 0x17cccb1621f := by decide +kernel
private theorem chunk12026 : blockEstimate 9956 2106 12026 155 = 0x14dd207b879 := by decide +kernel
private theorem chunk12181 : blockEstimate 9956 2106 12181 155 = 0x120d757904a := by decide +kernel
private theorem chunk12336 : blockEstimate 9956 2106 12336 155 = 0xf69aabd5ae := by decide +kernel
private theorem chunk12491 : blockEstimate 9956 2106 12491 155 = 0xcf41ab5839 := by decide +kernel
private theorem chunk12646 : blockEstimate 9956 2106 12646 155 = 0xaaec96e33f := by decide +kernel
private theorem chunk12801 : blockEstimate 9956 2106 12801 155 = 0x89bbaf835d := by decide +kernel
private theorem chunk12956 : blockEstimate 9956 2106 12956 155 = 0x6bcf3601a9 := by decide +kernel
private theorem chunk13111 : blockEstimate 9956 2106 13111 155 = 0x51476b6d73 := by decide +kernel
private theorem chunk13266 : blockEstimate 9956 2106 13266 155 = 0x3a44908fa3 := by decide +kernel
private theorem chunk13421 : blockEstimate 9956 2106 13421 155 = 0x26e6e67742 := by decide +kernel
private theorem chunk13576 : blockEstimate 9956 2106 13576 155 = 0x174eadeb95 := by decide +kernel
private theorem chunk13731 : blockEstimate 9956 2106 13731 155 = 0xb9c27fdbd := by decide +kernel
private theorem chunk13886 : blockEstimate 9956 2106 13886 155 = 0x3ef957436 := by decide +kernel
private theorem chunk14041 : blockEstimate 9956 2106 14041 127 = 0x684c0920 := by decide +kernel
private theorem joined2106_310 : blockEstimate 9956 2106 2106 310 = 0xb59c5d2b2 :=
  block_append chunk2106 chunk2261 rfl rfl rfl

private theorem joined2416_310 : blockEstimate 9956 2106 2416 310 = 0x4cdb855bfb :=
  block_append chunk2416 chunk2571 rfl rfl rfl

private theorem joined2106_620 : blockEstimate 9956 2106 2106 620 = 0x58354b2ead :=
  block_append joined2106_310 joined2416_310 rfl rfl rfl

private theorem joined2726_310 : blockEstimate 9956 2106 2726 310 = 0xc9bc380e38 :=
  block_append chunk2726 chunk2881 rfl rfl rfl

private theorem joined3191_310 : blockEstimate 9956 2106 3191 310 = 0x1e642e4da84 :=
  block_append chunk3191 chunk3346 rfl rfl rfl

private theorem joined3036_465 : blockEstimate 9956 2106 3036 465 = 0x28abf62fbc8 :=
  block_append chunk3036 joined3191_310 rfl rfl rfl

private theorem joined2726_775 : blockEstimate 9956 2106 2726 775 = 0x3547b9b0a00 :=
  block_append joined2726_310 joined3036_465 rfl rfl rfl

private theorem joined2106_1395 : blockEstimate 9956 2106 2106 1395 = 0x3acb0e638ad :=
  block_append joined2106_620 joined2726_775 rfl rfl rfl

private theorem joined3501_310 : blockEstimate 9956 2106 3501 310 = 0x2db58291b71 :=
  block_append chunk3501 chunk3656 rfl rfl rfl

private theorem joined3966_310 : blockEstimate 9956 2106 3966 310 = 0x48ddc82c364 :=
  block_append chunk3966 chunk4121 rfl rfl rfl

private theorem joined3811_465 : blockEstimate 9956 2106 3811 465 = 0x663308b27f9 :=
  block_append chunk3811 joined3966_310 rfl rfl rfl

private theorem joined3501_775 : blockEstimate 9956 2106 3501 775 = 0x93e88b4436a :=
  block_append joined3501_310 joined3811_465 rfl rfl rfl

private theorem joined4276_310 : blockEstimate 9956 2106 4276 310 = 0x5c39fcdc54f :=
  block_append chunk4276 chunk4431 rfl rfl rfl

private theorem joined4741_310 : blockEstimate 9956 2106 4741 310 = 0x7646d0827bb :=
  block_append chunk4741 chunk4896 rfl rfl rfl

private theorem joined4586_465 : blockEstimate 9956 2106 4586 465 = 0xab3016a9708 :=
  block_append chunk4586 joined4741_310 rfl rfl rfl

private theorem joined4276_775 : blockEstimate 9956 2106 4276 775 = 0x1076a1385c57 :=
  block_append joined4276_310 joined4586_465 rfl rfl rfl

private theorem joined3501_1550 : blockEstimate 9956 2106 3501 1550 = 0x19b529ec9fc1 :=
  block_append joined3501_775 joined4276_775 rfl rfl rfl

private theorem joined2106_2945 : blockEstimate 9956 2106 2106 2945 = 0x1d61dad2d86e :=
  block_append joined2106_1395 joined3501_1550 rfl rfl rfl

private theorem joined5051_310 : blockEstimate 9956 2106 5051 310 = 0x855c1c773af :=
  block_append chunk5051 chunk5206 rfl rfl rfl

private theorem joined5516_310 : blockEstimate 9956 2106 5516 310 = 0x988f2caf51f :=
  block_append chunk5516 chunk5671 rfl rfl rfl

private theorem joined5361_465 : blockEstimate 9956 2106 5361 465 = 0xe05311c835d :=
  block_append chunk5361 joined5516_310 rfl rfl rfl

private theorem joined5051_775 : blockEstimate 9956 2106 5051 775 = 0x165af2e3f70c :=
  block_append joined5051_310 joined5361_465 rfl rfl rfl

private theorem joined5826_310 : blockEstimate 9956 2106 5826 310 = 0xa3134bb006b :=
  block_append chunk5826 chunk5981 rfl rfl rfl

private theorem joined6291_310 : blockEstimate 9956 2106 6291 310 = 0xaf6c987a0df :=
  block_append chunk6291 chunk6446 rfl rfl rfl

private theorem joined6136_465 : blockEstimate 9956 2106 6136 465 = 0x10455a453d3c :=
  block_append chunk6136 joined6291_310 rfl rfl rfl

private theorem joined5826_775 : blockEstimate 9956 2106 5826 775 = 0x1a768f003da7 :=
  block_append joined5826_310 joined6136_465 rfl rfl rfl

private theorem joined5051_1550 : blockEstimate 9956 2106 5051 1550 = 0x30d181e434b3 :=
  block_append joined5051_775 joined5826_775 rfl rfl rfl

private theorem joined6601_310 : blockEstimate 9956 2106 6601 310 = 0xb55f8a86b83 :=
  block_append chunk6601 chunk6756 rfl rfl rfl

private theorem joined7066_310 : blockEstimate 9956 2106 7066 310 = 0xbadf13e2afb :=
  block_append chunk7066 chunk7221 rfl rfl rfl

private theorem joined6911_465 : blockEstimate 9956 2106 6911 465 = 0x11737ce4c4a5 :=
  block_append chunk6911 joined7066_310 rfl rfl rfl

private theorem joined6601_775 : blockEstimate 9956 2106 6601 775 = 0x1cc9758d3028 :=
  block_append joined6601_310 joined6911_465 rfl rfl rfl

private theorem joined7376_310 : blockEstimate 9956 2106 7376 310 = 0xbc40d8fb4f7 :=
  block_append chunk7376 chunk7531 rfl rfl rfl

private theorem joined7841_310 : blockEstimate 9956 2106 7841 310 = 0xbae69ee9373 :=
  block_append chunk7841 chunk7996 rfl rfl rfl

private theorem joined7686_465 : blockEstimate 9956 2106 7686 465 = 0x118f98fb1998 :=
  block_append chunk7686 joined7841_310 rfl rfl rfl

private theorem joined7376_775 : blockEstimate 9956 2106 7376 775 = 0x1d53a68ace8f :=
  block_append joined7376_310 joined7686_465 rfl rfl rfl

private theorem joined6601_1550 : blockEstimate 9956 2106 6601 1550 = 0x3a1d1c17feb7 :=
  block_append joined6601_775 joined7376_775 rfl rfl rfl

private theorem joined5051_3100 : blockEstimate 9956 2106 5051 3100 = 0x6aee9dfc336a :=
  block_append joined5051_1550 joined6601_1550 rfl rfl rfl

private theorem joined2106_6045 : blockEstimate 9956 2106 2106 6045 = 0x885078cf0bd8 :=
  block_append joined2106_2945 joined5051_3100 rfl rfl rfl

private theorem joined8151_310 : blockEstimate 9956 2106 8151 310 = 0xb7b7370dcc7 :=
  block_append chunk8151 chunk8306 rfl rfl rfl

private theorem joined8461_310 : blockEstimate 9956 2106 8461 310 = 0xb2b4239d90b :=
  block_append chunk8461 chunk8616 rfl rfl rfl

private theorem joined8151_620 : blockEstimate 9956 2106 8151 620 = 0x16a6b5aab5d2 :=
  block_append joined8151_310 joined8461_310 rfl rfl rfl

private theorem joined8771_310 : blockEstimate 9956 2106 8771 310 = 0xabdd649883f :=
  block_append chunk8771 chunk8926 rfl rfl rfl

private theorem joined9236_310 : blockEstimate 9956 2106 9236 310 = 0x9e2e6459e8f :=
  block_append chunk9236 chunk9391 rfl rfl rfl

private theorem joined9081_465 : blockEstimate 9956 2106 9081 465 = 0xf0fa6965c4d :=
  block_append chunk9081 joined9236_310 rfl rfl rfl

private theorem joined8771_775 : blockEstimate 9956 2106 8771 775 = 0x19cd7cdfe48c :=
  block_append joined8771_310 joined9081_465 rfl rfl rfl

private theorem joined8151_1395 : blockEstimate 9956 2106 8151 1395 = 0x3074328a9a5e :=
  block_append joined8151_620 joined8771_775 rfl rfl rfl

private theorem joined9546_310 : blockEstimate 9956 2106 9546 310 = 0x92c67860d1b :=
  block_append chunk9546 chunk9701 rfl rfl rfl

private theorem joined10011_310 : blockEstimate 9956 2106 10011 310 = 0x7e9a9df3612 :=
  block_append chunk10011 chunk10166 rfl rfl rfl

private theorem joined9856_465 : blockEstimate 9956 2106 9856 465 = 0xc3250adc061 :=
  block_append chunk9856 joined10011_310 rfl rfl rfl

private theorem joined9546_775 : blockEstimate 9956 2106 9546 775 = 0x155eb833cd7c :=
  block_append joined9546_310 joined9856_465 rfl rfl rfl

private theorem joined10321_310 : blockEstimate 9956 2106 10321 310 = 0x7054213a12d :=
  block_append chunk10321 chunk10476 rfl rfl rfl

private theorem joined10786_310 : blockEstimate 9956 2106 10786 310 = 0x5ad19ebaf39 :=
  block_append chunk10786 chunk10941 rfl rfl rfl

private theorem joined10631_465 : blockEstimate 9956 2106 10631 465 = 0x8d96c071002 :=
  block_append chunk10631 joined10786_310 rfl rfl rfl

private theorem joined10321_775 : blockEstimate 9956 2106 10321 775 = 0xfdeae1ab12f :=
  block_append joined10321_310 joined10631_465 rfl rfl rfl

private theorem joined9546_1550 : blockEstimate 9956 2106 9546 1550 = 0x253d664e7eab :=
  block_append joined9546_775 joined10321_775 rfl rfl rfl

private theorem joined8151_2945 : blockEstimate 9956 2106 8151 2945 = 0x55b198d91909 :=
  block_append joined8151_1395 joined9546_1550 rfl rfl rfl

private theorem joined11096_310 : blockEstimate 9956 2106 11096 310 = 0x4ccd88ae84c :=
  block_append chunk11096 chunk11251 rfl rfl rfl

private theorem joined11561_310 : blockEstimate 9956 2106 11561 310 = 0x38e263c3eb9 :=
  block_append chunk11561 chunk11716 rfl rfl rfl

private theorem joined11406_465 : blockEstimate 9956 2106 11406 465 = 0x5a31486b864 :=
  block_append chunk11406 joined11561_310 rfl rfl rfl

private theorem joined11096_775 : blockEstimate 9956 2106 11096 775 = 0xa6fed11a0b0 :=
  block_append joined11096_310 joined11406_465 rfl rfl rfl

private theorem joined11871_310 : blockEstimate 9956 2106 11871 310 = 0x2ca9eb91a98 :=
  block_append chunk11871 chunk12026 rfl rfl rfl

private theorem joined12336_310 : blockEstimate 9956 2106 12336 310 = 0x1c5dc572de7 :=
  block_append chunk12336 chunk12491 rfl rfl rfl

private theorem joined12181_465 : blockEstimate 9956 2106 12181 465 = 0x2e6b3aebe31 :=
  block_append chunk12181 joined12336_310 rfl rfl rfl

private theorem joined11871_775 : blockEstimate 9956 2106 11871 775 = 0x5b15267d8c9 :=
  block_append joined11871_310 joined12181_465 rfl rfl rfl

private theorem joined11096_1550 : blockEstimate 9956 2106 11096 1550 = 0x10213f797979 :=
  block_append joined11096_775 joined11871_775 rfl rfl rfl

private theorem joined12646_310 : blockEstimate 9956 2106 12646 310 = 0x134a846669c :=
  block_append chunk12646 chunk12801 rfl rfl rfl

private theorem joined13111_310 : blockEstimate 9956 2106 13111 310 = 0x8b8bfbfd16 :=
  block_append chunk13111 chunk13266 rfl rfl rfl

private theorem joined12956_465 : blockEstimate 9956 2106 12956 465 = 0xf75b31febf :=
  block_append chunk12956 joined13111_310 rfl rfl rfl

private theorem joined12646_775 : blockEstimate 9956 2106 12646 775 = 0x22c0378655b :=
  block_append joined12646_310 joined12956_465 rfl rfl rfl

private theorem joined13421_310 : blockEstimate 9956 2106 13421 310 = 0x3e359462d7 :=
  block_append chunk13421 chunk13576 rfl rfl rfl

private theorem joined13886_282 : blockEstimate 9956 2106 13886 282 = 0x457e17d56 :=
  block_append chunk13886 chunk14041 rfl rfl rfl

private theorem joined13731_437 : blockEstimate 9956 2106 13731 437 = 0xff4097b13 :=
  block_append chunk13731 joined13886_282 rfl rfl rfl

private theorem joined13421_747 : blockEstimate 9956 2106 13421 747 = 0x4e299dddea :=
  block_append joined13421_310 joined13731_437 rfl rfl rfl

private theorem joined12646_1522 : blockEstimate 9956 2106 12646 1522 = 0x27a2d164345 :=
  block_append joined12646_775 joined13421_747 rfl rfl rfl

private theorem joined11096_3072 : blockEstimate 9956 2106 11096 3072 = 0x129b6c8fbcbe :=
  block_append joined11096_1550 joined12646_1522 rfl rfl rfl

private theorem joined8151_6017 : blockEstimate 9956 2106 8151 6017 = 0x684d0568d5c7 :=
  block_append joined8151_2945 joined11096_3072 rfl rfl rfl

private theorem joined2106_12062 : blockEstimate 9956 2106 2106 12062 = 0xf09d7e37e19f :=
  block_append joined2106_6045 joined8151_6017 rfl rfl rfl

private theorem momentTerminal : momentEstimate 9956 2106 = 0xf09d7e37e19f := joined2106_12062

private theorem terminal_ok (b : Band) : BankOK (terminal b) := by
  cases b with
  | h2452 => exact (pass! 7159,9956,2106,0x2666b9ec700000,0xf09d7e37e19f; momentTerminal)

private def StageOK (ss : List Stage) : Prop :=
  ∀ s ∈ ss, BankOK s.free ∧ BankOK s.moving

private theorem stages_nil : StageOK [] :=
  fun _ hs => (List.not_mem_nil hs).elim

private theorem stages_cons {s : Stage} {ss : List Stage}
    (hf : BankOK s.free) (hm : BankOK s.moving) (ht : StageOK ss) : StageOK (s :: ss) :=
  List.forall_mem_cons.mpr ⟨⟨hf, hm⟩, ht⟩

private theorem stages_ok (b : Band) : StageOK (stages b) := by
  cases b with
  | h2452 =>
    rw [stages]
    refine stages_cons (pass! 73,101,22,0x2e5640000,0x2f6f2a; moment101_22) (pass! 353,491,103,0x12fc4600000,0x5e3742a9; moment491_103) ?_
    refine stages_cons (pass! 60,83,18,0x19fec0000,0x15f0f2; moment83_18) (pass! 405,563,118,0x1c9714c0000,0xa26535f3; moment563_118) ?_
    refine stages_cons (pass! 109,151,33,0x979280000,0xe74c1b; moment151_33) (pass! 445,619,130,0x25f62dc0000,0xed5a05de; moment619_130) ?_
    refine stages_cons (pass! 122,169,38,0xd80c80000,0x170ad54; moment169_38) (pass! 473,659,138,0x2d836e40000,0x12ff82db2; moment659_138) ?_
    refine stages_cons (pass! 131,181,40,0x106e580000,0x1dd3cf8; moment181_40) (pass! 558,775,163,0x4aad7380000,0x246465872; moment775_163) ?_
    refine stages_cons (pass! 140,194,42,0x13bfdc0000,0x26a2eee; moment194_42) (pass! 653,908,191,0x77a65000000,0x447811faa; moment908_191) ?_
    refine stages_cons (pass! 179,248,55,0x29b7600000,0x681fcb3; moment248_55) (pass! 859,1195,253,0x111524d80000,0xcdfbb5b3b; moment1195_253) ?_
    refine stages_cons (pass! 193,267,58,0x3355540000,0x895de88; moment267_58) (pass! 1043,1451,305,0x1e61e4680000,0x1bcaea101e; moment1451_305) ?_
    refine stages_cons (pass! 362,502,114,0x15ae1900000,0x6d68a9c9; moment502_114) (pass! 1225,1703,357,0x310fd3780000,0x349473cb5b; moment1703_357) ?_
    refine stages_cons (pass! 210,291,64,0x42b1ac0000,0xc32b568; moment291_64) (pass! 1318,1839,385,0x3d329b940000,0x4765896c69; moment1839_385) ?_
    refine stages_cons (pass! 295,409,90,0xb7d8100000,0x2f3b1229; moment409_90) (pass! 1516,2105,443,0x5d1c55480000,0x7afe40f467; moment2105_443) ?_
    refine stages_cons (pass! 402,559,122,0x1cd6b900000,0xa2dfd458; moment559_122) (pass! 2123,2950,628,0x101e034e80000,0x1de23726e9e; moment2950_628) ?_
    refine stages_cons (pass! 377,523,114,0x17bd5e40000,0x7cce7b05; moment523_114) (pass! 2155,2994,634,0x10c9546a80000,0x1f9316168cb; moment2994_634) ?_
    refine stages_cons (pass! 500,692,155,0x3841b080000,0x185234383; moment692_155) (pass! 2696,3749,788,0x20b0925680000,0x4d21177bab1; moment3749_788) ?_
    refine stages_cons (pass! 526,731,158,0x3fecfe00000,0x1d7121286; moment731_158) (pass! 2811,3918,819,0x24f5ff3100000,0x5b99db6de2b; moment3918_819) ?_
    refine stages_cons (pass! 425,590,130,0x22423840000,0xcb755a0e; moment590_130) (pass! 2032,2827,594,0xe01986d40000,0x18f3217cfe1; moment2827_594) ?_
    refine stages_cons (pass! 806,1116,251,0xeba01480000,0xa44b9ecd3; moment1116_251) (pass! 4291,5969,1261,0x844328b580000,0x1f12fe9a79ee; moment5969_1261) ?_
    refine stages_cons (pass! 80,111,24,0x3c7300000,0x4451ef; moment111_24) (pass! 380,530,100,0x15dc6d00000,0x7597b06c; moment530_100) ?_
    refine stages_cons (pass! 86,119,26,0x4b3780000,0x5a8245; moment119_26) (pass! 547,764,141,0x3fe66d80000,0x1f060dc24; moment764_141) ?_
    refine stages_cons (pass! 91,126,27,0x57a300000,0x6fafa5; moment126_27) (pass! 1081,1507,264,0x1d679b940000,0x1bfe368baa; moment1507_264) ?_
    refine stages_cons (pass! 97,134,29,0x6a6580000,0x8f605a; moment134_29) (pass! 664,925,200,0x809ed600000,0x4b52e2da2; moment925_200) ?_
    refine stages_cons (pass! 111,153,34,0xa15400000,0xf6b69e; moment153_34) (pass! 494,688,140,0x32b0a2c0000,0x160efc81a; moment688_140) ?_
    refine stages_cons (pass! 129,179,39,0xf95600000,0x1c3d3dd; moment179_39) (pass! 701,976,192,0x8cad28c0000,0x56ac98d52; moment976_192) ?_
    refine stages_cons (pass! 161,223,49,0x1e3a480000,0x43d826b; moment223_49) (pass! 996,1388,254,0x17ce40840000,0x14de8d1a33; moment1388_254) ?_
    refine stages_cons (pass! 168,233,50,0x21bc440000,0x4f48465; moment233_50) (pass! 1122,1566,343,0x271c0f900000,0x26eb47ca19; moment1566_343) ?_
    refine stages_cons (pass! 190,263,59,0x3235480000,0x849a735; moment263_59) (pass! 1811,2518,553,0xa40e21480000,0x1042a2fc6be; moment2518_553) ?_
    refine stages_cons (pass! 249,346,77,0x7002580000,0x187d9080; moment346_77) (pass! 2394,3335,706,0x170d016500000,0x309550b3c97; moment3335_706) ?_
    refine stages_cons (pass! 253,351,80,0x776e8c0000,0x1a683d4b; moment351_80) (pass! 1126,1572,307,0x243638180000,0x241fd7a6b1; moment1572_307) ?_
    refine stages_cons (pass! 266,369,82,0x8812100000,0x1f9950b6; moment369_82) (pass! 1022,1428,311,0x1d7761500000,0x1ace076bd3; moment1428_311) ?_
    refine stages_cons (pass! 316,439,98,0xe4864c0000,0x3f4c6dc0; moment439_98) (pass! 2509,3505,762,0x1b224cb7c0000,0x3c82694be91; moment3505_762) ?_
    exact stages_nil

theorem listed_ok (b : Band) (t : Bank) (ht : Listed b t) : BankOK t := by
  rcases ht with rfl | ⟨s, hs, rfl | rfl⟩ | ⟨i, rfl⟩
  · exact terminal_ok b
  · exact (stages_ok b s hs).1
  · exact (stages_ok b s hs).2
  · exact ⟨(terminal_ok b).nodes, (terminal_ok b).moment⟩

theorem interpolation_sources : SourceExists :=
  source (fun b t ht => (listed_ok b t ht).nodes) (fun b t ht => (listed_ok b t ht).moment)

#print axioms interpolation_sources
end High52BankProof
