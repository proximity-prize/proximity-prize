import ProximityPrize.SubmissionLower.HighCore82200TerminalArithmetic

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82200Terminal

open HighCore82200
open HighCore82200TerminalArithmetic
open K1_14 (Shape)

private def GradeChecks (t : Bank) (h : ℕ) : ℕ → List Grade → Prop
  | _, [] => True
  | e, g :: gs =>
    BlockChecks ({t.shape with U := g.slots}) t.nodeRows t.poleMoment h e (g.seedCap+1) ∧
      GradeChecks t h (e+1) gs

private theorem grade_at (t : Bank) (h : ℕ) (gs : List Grade) (e : ℕ)
    (hc : GradeChecks t h e gs) (i : Fin gs.length) :
    BlockChecks {t.shape with U := (gs.get i).slots} t.nodeRows t.poleMoment h (i.val+e) ((gs.get i).seedCap+1) := by
  induction gs generalizing e with
  | nil => exact Fin.elim0 i
  | cons g gs ih =>
    rcases i with ⟨_ | j, hj⟩
    · simpa [GradeChecks] using hc.1
    · have h' := ih (e+1) hc.2 ⟨j, by simpa using hj⟩
      simpa only [List.get_cons_succ, Nat.succ_add, Nat.add_succ] using h'

set_option quotPrecheck false
local notation "last!" l "," r => Parts.final (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel))
local notation "more!" l "," r "," p => Parts.more (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel)) p
local notation "block!" nn "," k "," l "," r "," p => certify
  (n := nn) (last := k) (cost := l) (costNext := r) p
  (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide) (by decide)

namespace h2367
local notation "S" u => (⟨6825,9490,2013,u⟩ : Shape)
local notation "N" => 0x21575027980000
local notation "P" => 0xc712452a9ff2
private theorem r0 : BlockChecks (S 211201) N P 2367 24 0 :=
  block! 2409,6,0x3cee8b926dfd39e946040fb00,0x3cee8d5584074d943ebbe4000,(more! 0x35cc841e5760cc90effcc5a20,0x35d31c66f226bb95319410700,(more! 0x71d9432109d313e28720fe40,0x7174ed3a717c81434adb74e0,(last! 0x5085b017379972b3497c00,0x4cac376f7be2375dd68340)))
private theorem r1 : BlockChecks (S 211201) N P 2367 1 381 :=
  block! 2568,12,0x3cee8b926dfd39e946040fb00,0x3cee8d5584074d943ebbe4000,(more! 0x33fe8c6666787842d2e6ca800,0x34052d05d21f1c12a1036e8e0,(more! 0x8445f4512da8f2501d3b72c0,0x83f8dd3918f4a31aac146260,(last! 0xaba244ea464ed83c8a1a520,0xa9e85c8f420ffcd42473300)))
private theorem r2 : BlockChecks (S 211201) N P 2367 2 375 :=
  block! 2577,12,0x3cee8b926dfd39e946040fb00,0x3cee8d5584074d943ebbe4000,(more! 0x3416aa99012a2cfc9a08b9480,0x341d4af9d3f4c7029edd43ea0,(more! 0x832dabafa79cf6f1bc3534a0,0x82df6bcde677df052251ddc0,(last! 0xa51183b157cfbdf50fdf0e0,0xa36a6771039baf3c4327600)))
private theorem r3 : BlockChecks (S 211201) N P 2367 3 368 :=
  block! 2587,12,0x3cee8b926dfd39e946040fb00,0x3cee8d5584074d943ebbe4000,(more! 0x342ccd775c6e38c0b3ea00e80,0x34336dbd3749fb1653f6fdec0,(more! 0x822953fe92e6984c4855f600,0x81d9ff6babcbac20ebbba8e0,(last! 0x9f30e97fe54808b9b963aa0,0x9d9b32de1c04c021dd7fce0)))
private theorem r4 : BlockChecks (S 211201) N P 2367 4 361 :=
  block! 2599,13,0x3cee8b926dfd39e946040fb00,0x3cee8d5584074d943ebbe4000,(more! 0x344407310d32069acae604500,0x344aa74c5e49de81e8a8e36a0,(more! 0x812183bd7757139ed2899360,0x80d113898f01234bbd5fb260,(last! 0x98756d423e0c61eb0eb1ae0,0x96f19b489a6412dcb902bc0)))
private theorem r5 : BlockChecks (S 211201) N P 2367 5 354 :=
  block! 2610,13,0x3cee8b926dfd39e946040fb00,0x3cee8d5584074d943ebbe4000,(more! 0x345c54095427d27df54d9e820,0x3462f3e8c7840487bc9673840,(more! 0x80164eed578525b3eaf79f40,0x7fc4bd1b812bcc2625c61740,(last! 0x90e215bb785053641570c40,0x8f709a15b0c7fbf549ac0e0)))
private theorem r6 : BlockChecks (S 211201) N P 2367 6 346 :=
  block! 2624,14,0x3cee8b926dfd39e946040fb00,0x3cee8d5584074d943ebbe4000,(more! 0x34733ea9aef8a8e061e232140,0x3479de69d7d0975d923e46820,(more! 0x7f1be943b7fc50bdfae1d220,0x7ec9450b79e5c709aed58140,(last! 0x8999ccc367890970a4a6000,0x88399646fabfdf0f0940500)))
private theorem r7 : BlockChecks (S 211201) N P 2367 7 338 :=
  block! 2638,14,0x3cee8b926dfd39e946040fb00,0x3cee8d5584074d943ebbe4000,(more! 0x348b739d105bdbc1b9232ae20,0x34921326f4a010a1b66b32640,(more! 0x7e1cd92b0e47f45202419680,0x7dc91ba9dc2f8ddc0c448340,(last! 0x8158711b9c982fa6df48de0,0x800a05a0c1ec1382de3fb80)))
private theorem r8 : BlockChecks (S 211201) N P 2367 8 329 :=
  block! 2655,15,0x3cee8b926dfd39e946040fb00,0x3cee8d5584074d943ebbe4000,(more! 0x34a2c1194fcd920797a3de500,0x34a9608158c52dc032a8937a0,(more! 0x7d2be5473f77cd2eb6af6560,0x7cd71a22d81e20e5a7092560,(last! 0x7914d56fe9fd62ee35e0b00,0x77d765504ae8329cdc8f6e0)))
private theorem r9 : BlockChecks (S 211201) N P 2367 9 320 :=
  block! 2674,16,0x3cee8b926dfd39e946040fb00,0x3cee8d5584074d943ebbe4000,(more! 0x34bb8494fa54d0c538fe1ff60,0x34c223bb21f781fa9405c6ac0,(more! 0x7c34be7bb075665d37855f00,0x7bdede69fce8185694d1cd20,(last! 0x6fc7a91d86968a6495d65c0,0x6e9bc9fec17cef6058a88e0)))
private theorem r10 : BlockChecks (S 211201) N P 2367 10 310 :=
  block! 2695,16,0x3cee8b926dfd39e946040fb00,0x3cee8d5584074d943ebbe4000,(more! 0x34d3c973ad01c16ed05b362e0,0x34da685ef82bb3f78b85df000,(more! 0x7b48951434fb5af4c0ec2cc0,0x7af1a8d2a6ac379feee6cfc0,(last! 0x6645270bea1ee921da065a0,0x652a459a01770a8a6df93a0)))
private theorem r11 : BlockChecks (S 211201) N P 2367 11 299 :=
  block! 2720,1,0x3cee8b926dfd39e946040fb00,0x3cee8d5584074d943ebbe4000,(more! 0x34ebd7c0984e3aa9d39ef56e0,0x34f2766c85912e88cb32285c0,(more! 0x7a64cff468953c65169ffac0,0x7a0cddc3aa706d81a32aea60,(more! 0x5c7226982e44df3aaec99a0,0x5b67e32c7bbc34975a835a0,(last! 0,0))))
private theorem r12 : BlockChecks (S 211201) N P 2367 12 286 :=
  block! 2752,2,0x3cee8b926dfd39e946040fb00,0x3cee8d5584074d943ebbe4000,(more! 0x350250f0584949fabcfe3f6a0,0x3508ef70d9843c0cf278b9000,(more! 0x79965afc01911e6e20f60da0,0x793d73288736c9d111914da0,(more! 0x52d4f4f8dfc132d902793a0,0x51da35b1233dbbc528a25e0,(last! 0,0))))
private theorem r13 : BlockChecks (S 211201) N P 2367 13 273 :=
  block! 2744,2,0x3cee8b926dfd39e946040fb00,0x3cee8d5584074d943ebbe4000,(more! 0x351a5a495be54fc8f909ef660,0x3520f84d29e17bc61c626b780,(more! 0x78b9d7b2f09595cbd39a3080,0x785fefa1e44c973455bd3920,(more! 0x489ff485c2e08640054bc40,0x47b5b6e42b5a9b1f26babe0,(last! 0,0))))
private theorem r14 : BlockChecks (S 211201) N P 2367 14 257 :=
  block! 2691,16,0x3cee8b926dfd39e946040fb00,0x3cee8d5584074d943ebbe4000,(more! 0x352f84ff746bbb78658a65800,0x353622a4b3927a393046baa20,(more! 0x77fbe84e4b91c160af6cb020,0x77a115974a4968f89a46e560,(last! 0x3f523b54263f3721acbcc60,0x3e7706315c8481088376540)))
private theorem r15 : BlockChecks (S 211201) N P 2367 15 239 :=
  block! 2646,15,0x3cee8b926dfd39e946040fb00,0x3cee8d5584074d943ebbe4000,(more! 0x3543680e9564c9569fd53c720,0x354a0549e3609d922311fa340,(more! 0x774a65c3bd3062c99eb97140,0x76eeadba28ffa539d4bce220,(last! 0x36873e81fbd0117235b1f00,0x35bac843e6a23a59a906640)))
private theorem r16 : BlockChecks (S 211201) N P 2367 16 218 :=
  block! 2607,13,0x3cee8b926dfd39e946040fb00,0x3cee8d5584074d943ebbe4000,(more! 0x3555014a480bf53597a7e8380,0x355b9e313ab13b7909b179520,(more! 0x76b0873766b80f0c74e01980,0x7653f3751fc61818b2f90640,(last! 0x2e82ea134c86aae3f17b0a0,0x2dc482915259e9c86b50b20)))
private theorem r17 : BlockChecks (S 211201) N P 2367 17 196 :=
  block! 2572,12,0x3cee8b926dfd39e946040fb00,0x3cee8d5584074d943ebbe4000,(more! 0x35668b1dbd86654a1f0d2e400,0x356d278a4358692b8ac1f6b00,(more! 0x7612216e66e80256b2791040,0x75b4a7bd9b8ce5ab8d582ec0,(last! 0x26e4374f9e5198b7289f840,0x2634a97fe87c24ee53ea020)))
private theorem r18 : BlockChecks (S 211201) N P 2367 18 171 :=
  block! 2541,11,0x3cee8b926dfd39e946040fb00,0x3cee8d5584074d943ebbe4000,(more! 0x35760adbd8f623ed50b19eec0,0x357ca6e5f6cce127c78b7d240,(more! 0x75871e50f7a631f2585de0e0,0x7528c0f6f079a9eaca7c29e0,(last! 0x2010fad673d21ce63f9bca0,0x1f700976fbcf6d53478eca0)))
private theorem r19 : BlockChecks (S 211201) N P 2367 19 144 :=
  block! 2513,10,0x3cee8b926dfd39e946040fb00,0x3cee8d5584074d943ebbe4000,(more! 0x35849546f75b3559be3501de0,0x358b30eb6380cc475beac5c40,(more! 0x75013f5643e511a26caeae20,0x74a1f71fdae776801acb92a0,(last! 0x19e2d2f4c8271484b376b60,0x1950f4be1904eb531cd0c60)))
private theorem r20 : BlockChecks (S 211201) N P 2367 20 115 :=
  block! 2488,9,0x3cee8b926dfd39e946040fb00,0x3cee8d5584074d943ebbe4000,(more! 0x359234efca1ad6f3ff5ffdca0,0x3598d02db311b2afe07288b80,(more! 0x747f5619e9f8ebe28616d6e0,0x741f1b1cc72c05ddcee8cb80,(last! 0x146175c1d773ce6a284f840,0x13df2a55a24dd63af7ff3a0)))
private theorem r21 : BlockChecks (S 211201) N P 2367 21 84 :=
  block! 2465,8,0x3cee8b926dfd39e946040fb00,0x3cee8d5584074d943ebbe4000,(more! 0x359ef5bfedbca9ab0db874000,0x35a590985d0c74a49374fb660,(more! 0x740051445f4e0e428f7f0160,0x739f1be187ffb14f2f565dc0,(last! 0xf91862376cb69a73a6ec80,0xf1f46831bcf15272ac35c0)))
private theorem r22 : BlockChecks (S 211201) N P 2367 22 51 :=
  block! 2445,7,0x3cee8b926dfd39e946040fb00,0x3cee8d5584074d943ebbe4000,(more! 0x35aae4467685ebce8e014e600,0x35b17ebbdce798b71c1c60f40,(more! 0x7383447f681d31295d6cd8e0,0x73210e91a9db520b7071aa20,(last! 0xb74c940cedf39ffb45d400,0xb12f55cea7fb0e75957640)))
private theorem r23 : BlockChecks (S 211201) N P 2367 23 16 :=
  block! 2426,7,0x3cee8b926dfd39e946040fb00,0x3cee8d5584074d943ebbe4000,(more! 0x35b60d3529f5def50ac90f0a0,0x35bca74b020cce69b7a882a60,(more! 0x73077195582acb0208cc4460,0x72a437d1227ef2615df0f600,(last! 0x80a159859219403ea01420,0x7b8deb3678e4d498d2ba40)))

theorem none : BlockChecks (terminal .h2367).shape (terminal .h2367).nodeRows
    (terminal .h2367).poleMoment (start .h2367) (threshold .h2367 Option.none) 0 := r0

theorem all : GradeChecks (terminal .h2367) (start .h2367) 1 (grades .h2367) :=
  ⟨r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,trivial⟩
end h2367

namespace h2368
local notation "S" u => (⟨7062,9814,2080,u⟩ : Shape)
local notation "N" => 0x24e56a1ab40000
local notation "P" => 0xe386fa12aab7
private theorem r0 : BlockChecks (S 216915) N P 2368 24 0 :=
  block! 2489,1,0x47208de05aef32821e5b0c000,0x47208ff1de9290b9098ef8700,(more! 0x42c15ca496c27df0582061a40,0x42cfa765eae078ffa89a2b4c0,(more! 0x45fded4c671cbc0030dcfbc0,0x451acf49d06b82c1859a4880,(last! 0,0)))
private theorem r1 : BlockChecks (S 216915) N P 2368 1 379 :=
  block! 2653,7,0x47208de05aef32821e5b0c000,0x47208ff1de9290b9098ef8700,(more! 0x40ad6b229df88aebbead354e0,0x40bbca1f1d8522f3d857b9680,(more! 0x6492b05b7aee3266734f5420,0x63b90f2e2cc16b30537329e0,(last! 0x2a07b31333b6bb369371900,0x295b9c0c06822ec574b1c60)))
private theorem r2 : BlockChecks (S 216915) N P 2368 2 372 :=
  block! 2664,8,0x47208de05aef32821e5b0c000,0x47208ff1de9290b9098ef8700,(more! 0x40c5d8d507290c73b41c27580,0x40d437b79de80d0497e0ae100,(more! 0x6306efb402c6825399329d80,0x622cf86c6e762ee0f3605280,(last! 0x2a4cb6e01f5556f97c7ce80,0x29a61a52ca9138445772a80)))
private theorem r3 : BlockChecks (S 216915) N P 2368 3 365 :=
  block! 2675,8,0x47208de05aef32821e5b0c000,0x47208ff1de9290b9098ef8700,(more! 0x40df886d2ff79838be8f03640,0x40ede71529a82c87d231b0400,(more! 0x61702a263202e96cdf4cfae0,0x6095cbc16a99ca0f40711fa0,(last! 0x2a04c43de02f7f52969a800,0x2964d38cc914f89a59ad120)))
private theorem r4 : BlockChecks (S 216915) N P 2368 4 358 :=
  block! 2686,9,0x47208de05aef32821e5b0c000,0x47208ff1de9290b9098ef8700,(more! 0x40fa789718a88bc4786ba3580,0x4108d6dffc41482b385701360,(more! 0x5fcf21506daec9127fec1540,0x5ef44c43c234b622b34df880,(last! 0x2925a72022ce60a601f7620,0x288d7ffe6ed669a242ce3c0)))
private theorem r5 : BlockChecks (S 216915) N P 2368 5 351 :=
  block! 2698,9,0x47208de05aef32821e5b0c000,0x47208ff1de9290b9098ef8700,(more! 0x4116a4292c0e60f611d538a20,0x412501ea4934be498ea8bee60,(more! 0x5e24a3406664ef6c033b8fe0,0x5d4949bc9de9be41d4ce00a0,(last! 0x27a84bf49d301f4d9eeb580,0x2718f4a6e6b88fa5a179080)))
private theorem r6 : BlockChecks (S 216915) N P 2368 6 343 :=
  block! 2713,10,0x47208de05aef32821e5b0c000,0x47208ff1de9290b9098ef8700,(more! 0x4131425a71f9d0667e94c6380,0x413f9fd39de377b6f07bcff20,(more! 0x5c92f194e504ae5d2f803f00,0x5bb71484febcbfee589e6920,(last! 0x261f7be745c70100ac3c7e0,0x2598a496aad0044136f4c00)))
private theorem r7 : BlockChecks (S 216915) N P 2368 7 335 :=
  block! 2728,10,0x47208de05aef32821e5b0c000,0x47208ff1de9290b9098ef8700,(more! 0x414d5a0ab05169dcfce8e8140,0x415bb705b5ff3fb10c4170ba0,(more! 0x5af60f1409da9c4cedd22740,0x5a19a115c57493cf75a0e320,(last! 0x23d7fab8442d616667462e0,0x235ab093014d73c6a55e480)))
private theorem r8 : BlockChecks (S 216915) N P 2368 8 327 :=
  block! 2744,11,0x47208de05aef32821e5b0c000,0x47208ff1de9290b9098ef8700,(more! 0x416ad9c1d3649d7ea6019cd40,0x41793600c8ebfdeab157ce120,(more! 0x594ee45366fe83f94cd050c0,0x5871dab30e1f08b7dd9b28a0,(last! 0x20d5e345534b27cffcf9ae0,0x206310664760a1a3b05f180)))
private theorem r9 : BlockChecks (S 216915) N P 2368 9 317 :=
  block! 2765,12,0x47208de05aef32821e5b0c000,0x47208ff1de9290b9098ef8700,(more! 0x41852ed3eff6a2021a7521be0,0x41938adf33d8ee47f743055c0,(more! 0x57d719949b5d1120cf101720,0x56f97b25f224d322683104a0,(last! 0x1deeb363c9179d0e3f9d0a0,0x1d855f5f0c6e16f1bc1e6e0)))
private theorem r10 : BlockChecks (S 216915) N P 2368 10 308 :=
  block! 2785,12,0x47208de05aef32821e5b0c000,0x47208ff1de9290b9098ef8700,(more! 0x41a36d9d26a9ad94e66f19e80,0x41b1c8b19565c741f04924300,(more! 0x563566448d48cd7271703380,0x5557227062993d431c1d0b00,(last! 0x19db865e7c24b4cb0571ac0,0x197d812b11bd377c3ba9dc0)))
private theorem r11 : BlockChecks (S 216915) N P 2368 11 297 :=
  block! 2811,13,0x47208de05aef32821e5b0c000,0x47208ff1de9290b9098ef8700,(more! 0x41bf308dcb4b824e2d300bb40,0x41cd8b0419b6ea6ede980e3a0,(more! 0x54bacb8c47be3603715975a0,0x53dbe6ea090dada744abc6a0,(last! 0x15bf94ef57e143da020fb60,0x156c3a46cc674ef1cdbe660)))
private theorem r12 : BlockChecks (S 216915) N P 2368 12 284 :=
  block! 2844,14,0x47208de05aef32821e5b0c000,0x47208ff1de9290b9098ef8700,(more! 0x41d927056b426384145183580,0x41e781034f9ab1e0d02ed8580,(more! 0x535dfc8d199a8289820c3dc0,0x527e77dcaaf16c231c388340,(last! 0x11872fbe5f7b64201776500,0x113e4c8f43ac495bf310b40)))
private theorem r13 : BlockChecks (S 216915) N P 2368 13 271 :=
  block! 2835,14,0x47208de05aef32821e5b0c000,0x47208ff1de9290b9098ef8700,(more! 0x41f4c590ea648aaf4cc6d72c0,0x42031e5a7206c15b08e7436a0,(more! 0x51eb2efa493f577d49578840,0x510b06dd661b15f1cf8b6120,(last! 0xd2222b4e1191089ab86ba0,0xce4abd49d06ad50497eca0)))
private theorem r14 : BlockChecks (S 216915) N P 2368 14 255 :=
  block! 2782,12,0x47208de05aef32821e5b0c000,0x47208ff1de9290b9098ef8700,(more! 0x420d1c1e819b4fd07e4beca00,0x421b73f6b4ce8fa1a8845e340,(more! 0x50a2f53564cbbde901913920,0x4fc22d2b5c673d7049579020,(last! 0x94b3a3b8a5f0932b2d3e40,0x918b2dff81344ee8a59740)))
private theorem r15 : BlockChecks (S 216915) N P 2368 15 237 :=
  block! 2735,10,0x47208de05aef32821e5b0c000,0x47208ff1de9290b9098ef8700,(more! 0x4223ef6ea4008881837f16740,0x4232463d149ba16319046a620,(more! 0x4f69df6828533ea56ebbcf00,0x4e8878ad8d8cc912d8bc5180,(last! 0x60787e0979c828aee4c2c0,0x5dff4f21fd8f519994b920)))
private theorem r16 : BlockChecks (S 216915) N P 2368 16 217 :=
  block! 2694,9,0x47208de05aef32821e5b0c000,0x47208ff1de9290b9098ef8700,(more! 0x42394d08e26b4da69d84fe440,0x4247a2bbbb77cf30770fbaee0,(more! 0x4e3d1527fa4d6c05a165a5e0,0x4d5b13c48e02b0d5e05f0a00,(last! 0x3777620402657d7ef5a780,0x35aa9470f9dcb30a1d6ea0)))
private theorem r17 : BlockChecks (S 216915) N P 2368 17 195 :=
  block! 2658,8,0x47208de05aef32821e5b0c000,0x47208ff1de9290b9098ef8700,(more! 0x424d43f152111d31b0e5a3220,0x425b987e6c51466782d49dea0,(more! 0x4d1acbb41c81ccc1f66828a0,0x4c3839ce6f4f865ed3f00740,(last! 0x1a857f6b0c906108f9cb40,0x195b936bdc842871079900)))
private theorem r18 : BlockChecks (S 216915) N P 2368 18 170 :=
  block! 2626,6,0x47208de05aef32821e5b0c000,0x47208ff1de9290b9098ef8700,(more! 0x425eeb67144776c99a10756e0,0x426d3f058f1bc7210df6eeb20,(more! 0x4c1137d39bf9f8d12c5f3a80,0x4b2e26f66a63f5ce0a2d48c0,(last! 0x937d54778908bae7fd000,0x89bbd3f3da6117c03c660)))
private theorem r19 : BlockChecks (S 216915) N P 2368 19 143 :=
  block! 2597,5,0x47208de05aef32821e5b0c000,0x47208ff1de9290b9098ef8700,(more! 0x426f76e69c24bd8ab7a994880,0x427dc990a9dce88f02e79c240,(more! 0x4b0fef12200105cf9fad8940,0x4a2c82a52d93c884412a5a60,(last! 0x185dc685c04d017a43bc0,0x15491fd2537f9a3321c00)))
private theorem r20 : BlockChecks (S 216915) N P 2368 20 115 :=
  block! 2571,4,0x47208de05aef32821e5b0c000,0x47208ff1de9290b9098ef8700,(more! 0x427fc9c3bb17fb7a6c48f68e0,0x428e1b4600f6753d6482766c0,(more! 0x4a0cc366092c8982c9316880,0x492938c99c950110703cc620,(last! 0xbd1b80992e17494b60,0x2ae03d3b2e2141f0a0)))
private theorem r21 : BlockChecks (S 216915) N P 2368 21 84 :=
  block! 2548,4,0x47208de05aef32821e5b0c000,0x47208ff1de9290b9098ef8700,(more! 0x428e376806c976764fd751780,0x429c87fc516673bbf56201200,(more! 0x4925cb4fc3caf0290589c9c0,0x48424efc2fa1679a2012e800,(last! 0,0)))
private theorem r22 : BlockChecks (S 216915) N P 2368 22 51 :=
  block! 2527,3,0x47208de05aef32821e5b0c000,0x47208ff1de9290b9098ef8700,(more! 0x429bb5a7ac05abbe1c14a9b00,0x42aa05542fe6744ff8692f8a0,(more! 0x484dd2cf6c28c273c105afe0,0x476a64f4e73be51d9c461180,(last! 0,0)))
private theorem r23 : BlockChecks (S 216915) N P 2368 23 16 :=
  block! 2507,2,0x47208de05aef32821e5b0c000,0x47208ff1de9290b9098ef8700,(more! 0x42a8535fbe4b2e7e039003600,0x42b6a22d0cfde3feee13456c0,(more! 0x4783e5fdd86d6adf525a5b40,0x46a08613c5da11635eece980,(last! 0,0)))

theorem none : BlockChecks (terminal .h2368).shape (terminal .h2368).nodeRows
    (terminal .h2368).poleMoment (start .h2368) (threshold .h2368 Option.none) 0 := r0

theorem all : GradeChecks (terminal .h2368) (start .h2368) 1 (grades .h2368) :=
  ⟨r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,trivial⟩
end h2368

namespace h2395
local notation "S" u => (⟨7550,10506,2218,u⟩ : Shape)
local notation "N" => 0x2cfea55aa80000
local notation "P" => 0x129e297a45c0c
private theorem r0 : BlockChecks (S 234728) N P 2395 22 0 :=
  block! 2696,2,0x65920d07df2e24108e4d94500,0x65920ff60e73bd359cf632400,(more! 0x50e7e3e6dc503ce1ee7dad880,0x50f26ecbeaa45241e7d9d59a0,(more! 0x109e24d5752f69b28072db040,0x109c5e1c1307b51c7718c4d40,(more! 0x40d2ff82ed6c3374bbd0b940,0x4048f09f9fa9f0379a5c6000,(last! 0,0))))
private theorem r1 : BlockChecks (S 179424) N P 2395 1 331 :=
  block! 2761,4,0x3b5dd58c0e4e606bac4a15d00,0x3b5dd7c97dbaa859a2ce70400,(more! 0x2e50c3f577a2cfbae2808d320,0x2e56e5590c47b99c457e22ac0,(more! 0x9aad176d28cc667bb0e70d20,0x9a9e8acd526d06db774f9fc0,(more! 0x35d66ef891cf0968682a5040,0x3586a31895819c8ef58d4280,(last! 0x4efe29850f002c5783c000,0x4c919c3fd46e685f696800))))
private theorem r2 : BlockChecks (S 180915) N P 2395 2 326 :=
  block! 2773,5,0x3c5b4aaa5a4256ac21997e400,0x3c5b4cec8d9148d170000d000,(more! 0x2f1f9b7fcace785d7c0f966e0,0x2f25d77d814fc25651aa67cc0,(more! 0x9d4bed79d2cc9a17e2f15a20,0x9d3ceec35c7b5f4c0cc85340,(more! 0x360e5d17a3187a0ea862c280,0x35bda24385783a242f7ef2c0,(last! 0x621d3dad5b211752cfa4e0,0x5f6d6b9d0b6a3e55b5a700))))
private theorem r3 : BlockChecks (S 182775) N P 2395 3 321 :=
  block! 2788,5,0x3d9a6a15e30ac51ca4ce21800,0x3d9a6c5e08239b914ab0be000,(more! 0x3021a63a0ad3eea07a3971a40,0x302803b0cd170d206a536ce40,(more! 0xa09848d9247982a57a283c00,0xa088c78d9fd570495bd5fc60,(more! 0x367d942e4bf3dbada5869040,0x362b8e03bab94171e1872020,(last! 0x781bb1613099afd4aca540,0x7528f30b9de555341c8e60))))
private theorem r4 : BlockChecks (S 185099) N P 2395 4 316 :=
  block! 2804,6,0x3f2dbaef5d4b077bc1fa6dc00,0x3f2dbd3eefcec800f5a763000,(more! 0x31655a85c112ab4381521e200,0x316be245e14e43587b77bddc0,(more! 0xa4c33b60328944137e207700,0xa4b3220da4c6bd3a2d21f6c0,(more! 0x3733d5883516d01683624c00,0x36e00e2a2573d7d1868fee00,(last! 0x9140d7f7dda658c3d4dcc0,0x8e0b4206a2b3ee48fe7300))))
private theorem r5 : BlockChecks (S 187083) N P 2395 5 310 :=
  block! 2822,6,0x408a120952aa36552098f9c00,0x408a145f3c6bb72ef5db53000,(more! 0x327f6905e3330c5bd0604d100,0x328615672ff5c5700b744f280,(more! 0xa85f6cf5e2e6816f5e133660,0xa84ec7dcd0cfa5101000ee00,(more! 0x37a3d3b951dce68a148bbf20,0x374e8742e0b9f84bfa08b3c0,(last! 0xa962edcc5b1a7e0347e380,0xa5fb699a51b7c625e2b2c0))))
private theorem r6 : BlockChecks (S 189769) N P 2395 6 304 :=
  block! 2843,7,0x426793d9db01912c020c02200,0x426796385a5b0eec07bd82800,(more! 0x33fe0c3e16f0c61e10ece9380,0x3404eac93d67aacdeaa2da060,(more! 0xad516e093673b8f28cb91740,0xad401c778be5d7ba7695bea0,(more! 0x38850dfe2e9e4a3b69f16be0,0x382d881d6767fbbe63ef7980,(last! 0xc43de339f99e5663ebde00,0xc0a3a7d64c199f757b0ae0))))
private theorem r7 : BlockChecks (S 192397) N P 2395 7 297 :=
  block! 2866,8,0x44415b6f84b7bdf04b4015600,0x44415dd66a3517de5a96f3800,(more! 0x357a982192dbab0d99b692e60,0x3581a8902d78cc0705c35adc0,(more! 0xb23ca1e510fb75455155ac60,0xb22aa40fb093357a228e0ac0,(more! 0x39548fa90034067216de5740,0x38fac5521e09bcf2dfa1b9c0,(last! 0xdcbc93358b2a93118bd6e0,0xd8feb43b09218755b7e5c0))))
private theorem r8 : BlockChecks (S 196316) N P 2395 8 290 :=
  block! 2895,9,0x470ff9d1d860628861a7b6900,0x470ffc4544422a4f29760f400,(more! 0x37b5879fe69e974869d0f3ee0,0x37bce3a182899cbbaa047dc80,(more! 0xb9b0933ca7e962a12932a340,0xb99daae398fd759dac8431e0,(more! 0x3b0052ad6e18ed688724e880,0x3aa2f41ad0e7adfb1d652780,(last! 0xf8114215380daec17b5680,0xf427f96f3c70248581d0e0))))
private theorem r9 : BlockChecks (S 201102) N P 2395 9 282 :=
  block! 2932,10,0x4a913712a58c27f41f1735300,0x4a9139955d2bee66067dabc00,(more! 0x3a7b9b32717aa4ca31dc8cfe0,0x3a8355ac4e6239fc24835d540,(more! 0xc301f1750e01175b7b201e20,0xc2edf0f5bad8a850b2cfa400,(more! 0x3d48376e890b7878a013d160,0x3ce645749a89cb68ada91cc0,(last! 0x1111e64af5cf8ead13b9ec0,0x10d0bd74deba1fec703c9a0))))
private theorem r10 : BlockChecks (S 209391) N P 2395 10 274 :=
  block! 2983,12,0x50d642990e9ae6d5130ea3000,0x50d645364401b3878758fc000,(more! 0x3f66e36c55354567fa1919000,0x3f6f46c51b6e54465afe5f4a0,(more! 0xd3aa91f5452eef0052beb200,0xd394c4616b05d5fd8bf64c40,(more! 0x421c2bd2f9b07d725cb5d260,0x41b1ee38d62d485ed2245c60,(last! 0x131ddbb51f8d7581e531ec0,0x12d77853eb8d0ac705b68e0))))
private theorem r11 : BlockChecks (S 221352) N P 2395 11 263 :=
  block! 3060,15,0x5a5484ed517c8d46eef760500,0x5a5487b0c0f8895ab3fb22400,(more! 0x46cf1aca7a8e631125b9d9b00,0x46d87e74671bbbab5563a7940,(more! 0xecf4c6f960d7b92afbc03180,0xecdc5deaef4e26aa392cde40,(more! 0x4a0fda845297de36e992ab20,0x4998eb4467531e2373618ba0,(last! 0x153e927776c5a7ad11de4e0,0x14efd6eed2fc93e33304120))))
private theorem r12 : BlockChecks (S 234728) N P 2395 12 250 :=
  block! 3094,1,0x65920d07df2e24108e4d94500,0x65920ff60e73bd359cf632400,(more! 0x4f9d073df508cdf84bc6ba2e0,0x4fa79a2ae2e76c738032fd8e0,(more! 0x10ade0b7902634046cbddfce0,0x10ac28b9b298ff336a5feec00,(more! 0x532a64b0b35347f63143d6a0,0x52a41f901931d4c3fe9e2220,(more! 0x14b066dbcad8f0b57c12b60,0x145cefa6c8d959203ac03c0,(last! 0,0)))))
private theorem r13 : BlockChecks (S 234728) N P 2395 13 234 :=
  block! 3027,14,0x65920d07df2e24108e4d94500,0x65920ff60e73bd359cf632400,(more! 0x4fc84f7ff2d1ccc0e320f7700,0x4fd2e1e5c43082e3a26e4d980,(more! 0x10aca17401892e6f348c67fa0,0x10aae553dd14b878ece2aa8c0,(more! 0x50f4511637d840c90068cc40,0x506d4fa49effcc9cd5cd4440,(last! 0xe0d4d0108bcd6aebd1d440,0xdca4432f342ef6c6c1fc00))))
private theorem r14 : BlockChecks (S 234728) N P 2395 14 215 :=
  block! 2969,12,0x65920d07df2e24108e4d94500,0x65920ff60e73bd359cf632400,(more! 0x4feecadb45cd9f1475cbb4400,0x4ff95cd4c6d4381321d85a680,(more! 0x10ab973ce8159343449688740,0x10a9d7d7c602d97cc0253e440,(more! 0x4ef332f9f0ecfaeb6cfc86a0,0x4e6b6b84adfbc11fe4095600,(last! 0x8a3151b1e1f997220796e0,0x8701c226272ab1f9c41620))))
private theorem r15 : BlockChecks (S 234728) N P 2395 15 194 :=
  block! 2919,10,0x65920d07df2e24108e4d94500,0x65920ff60e73bd359cf632400,(more! 0x501357c6fb07d3693d169ac80,0x501de92ef4dea4c9b1a2e8280,(more! 0x10aa563ea39bf168017787800,0x10a894300c83d4e3f6a0bc9a0,(more! 0x4cfffca1ef0ae9dc2209fec0,0x4c776c246cdf99adb03e1fa0,(last! 0x48a01c00602f0aabd071a0,0x466d3c42d0f2e5382b69c0))))
private theorem r16 : BlockChecks (S 234728) N P 2395 16 171 :=
  block! 2875,8,0x65920d07df2e24108e4d94500,0x65920ff60e73bd359cf632400,(more! 0x5035e22383abb09b0b06e39a0,0x504072df12ca5bf365ca8b080,(more! 0x10a8f0a88415ad4a4784a1900,0x10a72c8a97a70dacf57f523a0,(more! 0x4b193d78d5ab61ee52c21b20,0x4a8feef80642a8c24d0ddc80,(last! 0x1d92b272b7eebaa7e69aa0,0x1c499974066ddc430c0560))))
private theorem r17 : BlockChecks (S 234728) N P 2395 17 145 :=
  block! 2837,7,0x65920d07df2e24108e4d94500,0x65920ff60e73bd359cf632400,(more! 0x505488fb5259cafa0561a05e0,0x505f1929db9343aee34886360,(more! 0x10a7ca643f3c63e20d048bba0,0x10a6051228b2c588f74569da0,(more! 0x4957372daa172845e83718c0,0x48cd45182dbf394018a958c0,(last! 0x745ef5f63cb1ceafa7a40,0x6bc70503a088d4d818a80))))
private theorem r18 : BlockChecks (S 234728) N P 2395 18 117 :=
  block! 2802,6,0x65920d07df2e24108e4d94500,0x65920ff60e73bd359cf632400,(more! 0x50717daf30afddc70c476fe60,0x507c0d3fdbc0fed41ff425e20,(more! 0x10a690376b1255421e69eb440,0x10a4ca472d89c71d77976ed40,(more! 0x47a2a0fd060996bd215906c0,0x47184b9ba144b6d9f765f220,(last! 0x581cdc05216954244fc0,0x45a8f2b4d25702ae2f60))))
private theorem r19 : BlockChecks (S 234728) N P 2395 19 86 :=
  block! 2771,4,0x65920d07df2e24108e4d94500,0x65920ff60e73bd359cf632400,(more! 0x508b2ea6f52586d2fb1656ea0,0x5095bdba2fe69cf9793235e60,(more! 0x10a5966b427e41172fc9cd680,0x10a3d0b437a991f65b7a943e0,(more! 0x4616ee0b4e272a70494f51a0,0x458c8a64ccdc413e4aca4a20,(last! 0,0))))
private theorem r20 : BlockChecks (S 234728) N P 2395 20 53 :=
  block! 2744,3,0x65920d07df2e24108e4d94500,0x65920ff60e73bd359cf632400,(more! 0x50a3775a5ede6514bb9f3cbe0,0x50ae05e60336f176165fc6820,(more! 0x10a49351739f78b85c765ab80,0x10a2ce6596521b324aec87420,(more! 0x44a2510e6242a0c599f9e3a0,0x4417e9231d85b9e96ccbc580,(last! 0,0))))
private theorem r21 : BlockChecks (S 234728) N P 2395 21 18 :=
  block! 2719,3,0x65920d07df2e24108e4d94500,0x65920ff60e73bd359cf632400,(more! 0x50ba5e21a0240bbb99d63d3c0,0x50c4ec20714383cce490af4a0,(more! 0x10a38ebf737ca32f7f1721560,0x10a1cb2eb179e5fe7577ca140,(more! 0x43442650632df2ac9cec2fa0,0x42b9b17c4418b415458f27e0,(last! 0,0))))

theorem none : BlockChecks (terminal .h2395).shape (terminal .h2395).nodeRows
    (terminal .h2395).poleMoment (start .h2395) (threshold .h2395 Option.none) 0 := r0

theorem all : GradeChecks (terminal .h2395) (start .h2395) 1 (grades .h2395) :=
  ⟨r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,trivial⟩
end h2395

namespace h7773
local notation "S" u => (⟨124,173,32,u⟩ : Shape)
local notation "N" => 0xc4fd80000
local notation "P" => 0x15c66e5
private theorem r0 : BlockChecks (S 946) N P 7773 7 0 :=
  block! 57,1,0x1e110619562db71c0,0x1e1109a388df00e80,(last! 0x1e136d6081ccbea80,0x1e13755d9db1efbc0)
private theorem r1 : BlockChecks (S 886) N P 7773 1 26 :=
  block! 67,2,0x1a6770724bb553ec0,0x1a6773c31431c0c80,(last! 0x1a68e8136230d50a0,0x1a68ef45fe3d17b80)
private theorem r2 : BlockChecks (S 913) N P 7773 2 24 :=
  block! 71,2,0x1c05d1e372dd1a280,0x1c05d54e118aea700,(last! 0x1c062154af35d6520,0x1c0628d3f9e8c12e0)
private theorem r3 : BlockChecks (S 946) N P 7773 3 22 :=
  block! 76,3,0x1e110619562db71c0,0x1e1109a388df00e80,(last! 0x1e124f954049fa480,0x1e125788d2dbe6f00)
private theorem r4 : BlockChecks (S 946) N P 7773 4 19 :=
  block! 76,3,0x1e110619562db71c0,0x1e1109a388df00e80,(last! 0x1e12aec0296508420,0x1e12b6b6c4d1373a0)
private theorem r5 : BlockChecks (S 946) N P 7773 5 14 :=
  block! 67,2,0x1e110619562db71c0,0x1e1109a388df00e80,(last! 0x1e11b7e4e329f2700,0x1e11bfd3968999ec0)
private theorem r6 : BlockChecks (S 946) N P 7773 6 8 :=
  block! 61,1,0x1e110619562db71c0,0x1e1109a388df00e80,(last! 0x1e131e9f28bfd3a00,0x1e132699aca3ee0c0)

theorem none : BlockChecks (terminal .h7773).shape (terminal .h7773).nodeRows
    (terminal .h7773).poleMoment (start .h7773) (threshold .h7773 Option.none) 0 := r0

theorem all : GradeChecks (terminal .h7773) (start .h7773) 1 (grades .h7773) :=
  ⟨r1,r2,r3,r4,r5,r6,trivial⟩
end h7773

set_option maxHeartbeats 800000

private theorem checks (b : Band) (x : Test b) :
    let t := tested b x
    BlockChecks t.shape t.nodeRows t.poleMoment (start b) (threshold b x) (seedThreshold b x) := by
  have hn : BlockChecks (terminal b).shape (terminal b).nodeRows (terminal b).poleMoment
      (start b) (threshold b Option.none) 0 := by
    cases b with
    | h2367 => exact h2367.none
    | h2368 => exact h2368.none
    | h2395 => exact h2395.none
    | h7773 => exact h7773.none
  have hc : GradeChecks (terminal b) (start b) 1 (grades b) := by
    cases b with
    | h2367 => exact h2367.all
    | h2368 => exact h2368.all
    | h2395 => exact h2395.all
    | h7773 => exact h7773.all
  cases x with
  | none => exact hn
  | some i => exact grade_at _ _ _ _ hc i

theorem terminal_bounds (b : Band) {h : ℕ} (hl : start b ≤ h) (hu : h ≤ finish b) (x : Test b) :
    debit h (tested b x) <
      jointGain h (tested b x).shape (threshold b x) (seedThreshold b x) := by
  let t := tested b x
  have hh0 : finish b < 131071 := by cases b <;> decide
  have hh : h < 131071 := hu.trans_lt hh0
  have hshape : t.shape.J = (terminal b).shape.J := by cases x <;> rfl
  have hJ : t.shape.J ≤ 131071 - (start b + 1) := by
    rw [hshape]
    cases b <;> decide
  have he : 0 < threshold b x := by cases x <;> exact Nat.succ_pos _
  have hc := checks b x
  change BlockChecks t.shape t.nodeRows t.poleMoment (start b) (threshold b x) (seedThreshold b x) at hc
  unfold BlockChecks at hc
  rw [blockSurplus_eq t (start b) _ _ (by omega) (by omega) he,
    blockSurplus_eq t (start b+1) _ _ (by omega) hJ he] at hc
  change debit h t < jointGain h t.shape (threshold b x) (seedThreshold b x)
  exact strict_of_first_difference (b := t) hl hh (by omega) (by omega)

#print axioms terminal_bounds
end HighCore82200Terminal
