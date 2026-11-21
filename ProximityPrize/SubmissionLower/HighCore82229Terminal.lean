import ProximityPrize.SubmissionLower.HighCore82229TerminalArithmetic

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82229Terminal

open HighCore82229
open HighCore82229TerminalArithmetic
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

namespace h2395
local notation "S" u => (⟨7550,10506,2218,u⟩ : Shape)
local notation "N" => 0x2cfea55aa80000
local notation "P" => 0x129e297a45c0c
private theorem r0 : BlockChecks (S 225000) N P 2440 24 0 :=
  block! 2656,16,0x5d55108331fe8642a0fc57800,0x5d5513524a25dbb8344455700,(more! 0x4b709f5ffeb9ec135293b33e0,0x4b83bbda61edcc77607c12360,(more! 0xed4d8d0286ae99bc721ac020,0xec9396d3a342f0b103bebb00,(last! 0x30f9ba7ca3e404a4b5383040,0x3083f4f4518296694ef59140)))
private theorem r1 : BlockChecks (S 181533) N P 2440 1 366 :=
  block! 2714,2,0x3cc55bfa9966bf32064b19000,0x3cc55e3ec65616cc880ee6200,(more! 0x3033fd6398ec6b41b7283f9e0,0x30405f4360a87aeff84011b60,(more! 0x99fc976cb3e68b77ba6d1800,0x998782ce7a17833ec1392a60,(more! 0x2f0d79751c096ae453599c80,0x2ebe84eb0c82e3eb66453860,(last! 0xbd8962f6c96daaf016940,0xb20126bc91967a65ffe80))))
private theorem r2 : BlockChecks (S 181341) N P 2440 2 361 :=
  block! 2721,3,0x3ca47db4130848ff71da79000,0x3ca47ff7a2e122a24713f2200,(more! 0x3029c9a96000f5910aa5e34e0,0x303624974ceef0335756239e0,(more! 0x99a0f359e279ddae926a8c60,0x992bbee5a0735bee6e6e4480,(more! 0x2dfb8e62ef4f7332dd00c440,0x2dad3c1a720f7e91907a5b40,(last! 0xebef04a65a100ee1ae340,0xdf26b3c0c92b19bc344a0))))
private theorem r3 : BlockChecks (S 186683) N P 2440 3 355 :=
  block! 2744,3,0x4043f398abd846767202b2000,0x4043f5ed4e559636f524dc400,(more! 0x32fc37c503a877bc044c439c0,0x33095357326547c2689b5dac0,(more! 0xa2fd07fbc701749a9bed2da0,0xa28093a1279b1df1de280380,(more! 0x315a45ce4a87297ca989d300,0x3107d76a4a3690e3909d8f00,(last! 0x246f740cd9c9cbde62cf20,0x230858d47ed288df96a020))))
private theorem r4 : BlockChecks (S 183485) N P 2440 4 350 :=
  block! 2743,3,0x3e157e30f849f12fcb6ec9000,0x3e15807b62489ecafcb0ec200,(more! 0x31621b9c038b7c68cae31eec0,0x316ec2f7f820c4ed6acfe6220,(more! 0x9d4f629963f6fc4bae3ca700,0x9cd6b5e0d6eaa02f5bac0d40,(more! 0x2dc9e1986ccf94b1694b3540,0x2d7aa0aed477e03c3e5eb700,(last! 0x1ce523d8392802dc100840,0x1bc076e5f8fa7076d40540))))
private theorem r5 : BlockChecks (S 185397) N P 2440 5 344 :=
  block! 2757,4,0x3f6238b2bc028fcef3a5ad000,0x3f623b0342568e81e5c954a00,(more! 0x327144ec275fdc2448a3dc800,0x327e314aa3a9b45d2d8405cc0,(more! 0xa0a625e2cb6d11ab2f64b940,0xa02a9f5861f920714b5b7480,(more! 0x2e40b4e011af904637802140,0x2df03d0ba3ae81d3ce50a8c0,(last! 0x2861ac21767c8fb412f500,0x2704a11501f2c265355040))))
private theorem r6 : BlockChecks (S 192822) N P 2440 6 337 :=
  block! 2791,5,0x448f02f97b0a663cb72118800,0x448f0561bc403455adba28900,(more! 0x367c2abb06920bc8e63d06b20,0x368a2a5f3dd39cdb0abb3ea00,(more! 0xae0679b163a03fffc1436fe0,0xad80a32983f4d2c2d45def20,(more! 0x32d515a0553c4fa434600fa0,0x327e917ebcdb3aec7d24aa60,(last! 0x51f49ae624ff1afc3a2de0,0x4fdb8d518bd9ff22209cc0))))
private theorem r7 : BlockChecks (S 189998) N P 2440 7 331 :=
  block! 2793,5,0x4291051bd8e264272d533c800,0x4291077b13980acfef79b9100,(more! 0x3507319a8f6b15a927f165740,0x3514c705d6a5f07823382e200,(more! 0xa8d583d7c235366203d77680,0xa85320b037428433264343a0,(more! 0x2f83237308de8fee03f7fec0,0x2f2f6f2c39b9dd12f53e88c0,(last! 0x4490ca776a59e20911bc20,0x42cd43bd8e52e3f5e63680))))
private theorem r8 : BlockChecks (S 201376) N P 2440 8 323 :=
  block! 2842,7,0x4ac5ad89b7d3b2e721301b800,0x4ac5b00d4fa0e7c7d17bf9f00,(more! 0x3b706988bd2a2207a7c4928e0,0x3b7fb3b03dc7a509ffe23ede0,(more! 0xbe0f9c584ed717e6e0e2be00,0xbd7cf67fc2d71a2785288540,(more! 0x36bacef68835db0c4dd26140,0x365d353a557c5e928c91ee00,(last! 0x89d4c0df7ee3e32b15ae80,0x871a05258d5ac040cb37c0))))
private theorem r9 : BlockChecks (S 197135) N P 2440 9 316 :=
  block! 2842,7,0x47a86a850a78ab55c4b5b8000,0x47a86cfb146e647108821f000,(more! 0x391f1a19a278cf49dab433500,0x392dbe27431b42dce32ebc580,(more! 0xb5f4bcd775d00ef5ee094200,0xb567baf263f2c45811579c80,(more! 0x3237a00483ae504c459d5680,0x31de1e25eec0beb94671f180,(last! 0x68a9ddf29db346a756ff00,0x668416003012c079bf1940))))
private theorem r10 : BlockChecks (S 205550) N P 2440 10 307 :=
  block! 2888,9,0x4de6e723dbec4604f0f5dc800,0x4de6e9b4cabfc80b4ae0ed100,(more! 0x3e0e9e57974b890dfcf9ec240,0x3e1e8eb7ce38b78addb3a6540,(more! 0xc6188fbd8fa7fa04f732d0c0,0xc57f0115f051825c550310c0,(more! 0x36dd9c3ca16b16ee28ed4500,0x367c74e03b62ca0c960592a0,(last! 0x8e60cf9b031b18cd872540,0x8bc9dac53fd478b5ed71e0))))
private theorem r11 : BlockChecks (S 215543) N P 2440 11 297 :=
  block! 2944,11,0x55a7dc6dbf1d30d0c363a4000,0x55a7df1e9ddf570dc57e40800,(more! 0x4431cc0fea45488dd989c4080,0x4443595b9205fd07f6857e0e0,(more! 0xda265c42ca738c2f31147b00,0xd97d3d67dcfd843962e0e1a0,(more! 0x3c8cfe7cbe9aa4c0c242c640,0x3c22273c7a10b12f263c3d60,(last! 0xadab221e5f4fed1efc77a0,0xaaaf58d294f77ab2eddd40))))
private theorem r12 : BlockChecks (S 218969) N P 2440 12 286 :=
  block! 2984,13,0x58660ea557cd733d857d4b000,0x586611612998f135f65c32600,(more! 0x46747bcd197e72568c75402c0,0x46869aebe975720d69bffbe40,(more! 0xe135a564979406f73d35eac0,0xe086bc373590b1b2d6a43920,(more! 0x3d4e65f52ed7540cedf67a80,0x3ce00820dbb80380f90a72e0,(last! 0x95222bafada2e68fa33780,0x9268d5d5d9b6f9257bad80))))
private theorem r13 : BlockChecks (S 222566) N P 2440 13 273 :=
  block! 3027,14,0x5b5335f34f270f5ccdf340800,0x5b5338ba9fe3ed414341a5900,(more! 0x48de1569a6b1eaa87250e8a40,0x48f0d00842014dea9c23ec5c0,(more! 0xe8bc726a6079c709e14ad120,0xe807669ab624898f37bf70e0,(more! 0x3e227b7d1b0c0777ea9f7600,0x3db03e5c4a6a0c530dfa5920,(last! 0x731ab3e97e340c21b54a40,0x70bb07ceab472287e1d720))))
private theorem r14 : BlockChecks (S 224442) N P 2440 14 258 :=
  block! 2969,12,0x5cdec4d4e59b9343a01506800,0x5cdec7a235398aa165eb00500,(more! 0x4a33af1acc537c81b893f7740,0x4a46bb6d1bc095775c456e3e0,(more! 0xecacae6724d7c679db8ea360,0xebf440399dca8cdd7921ca40,(more! 0x3db9dc5e1c91c1415ffde0c0,0x3d456bb2b58784efff682ac0,(last! 0x4ad0f7c569b480fa832f80,0x48f440df18f1b1b458cfa0))))
private theorem r15 : BlockChecks (S 223407) N P 2440 15 242 :=
  block! 2919,10,0x5c042077ed853089f03de8000,0x5c042341ee55e8dc97fa35000,(more! 0x49a5f3146a60714407fcd8ba0,0x49b8d11d3d73922e26fbcc180,(more! 0xea64f80701662f33026f4260,0xe9adec245bad13605d6f8240,(more! 0x3b578623aa983332fc2d7620,0x3ae3f41f963c1b19fc1f3d40,(last! 0x265830799a983a307b67c0,0x251a822853fb9e281cbba0))))
private theorem r16 : BlockChecks (S 224228) N P 2440 16 223 :=
  block! 2875,8,0x5cb17a992904b3c235e229800,0x5cb17d65c98c440e98bdf5b00,(more! 0x4a4a25416d54be4f241fe8ea0,0x4a5d268ce99f1e70a48dd40e0,(more! 0xec14a7d6e0d367bb1a00b1a0,0xeb5c09c9d4e24595a5b0d940,(more! 0x3a511c67360ac2a69d230860,0x39dc671cb9f6dec1e5c5fd20,(last! 0xf913e9b355d4032bc2b20,0xed874c04bb84cf0885240))))
private theorem r17 : BlockChecks (S 224635) N P 2440 17 202 :=
  block! 2837,7,0x5d07a6cb0543baef87a392000,0x5d07a998f2c9a397999498400,(more! 0x4aa818e2f7da73e297199db80,0x4abb2b406e91a86a50146ce60,(more! 0xece2e00c5027f68988ce3000,0xec2969405711df35e6d9f980,(more! 0x3912745422614463ea929940,0x389d189238a2a175cd5c9b40,(last! 0x38a54daa501a484e94d00,0x3416bdaeb43bd72369220))))
private theorem r18 : BlockChecks (S 224832) N P 2440 18 179 :=
  block! 2802,6,0x5d316af015ca18c72599cb800,0x5d316dbea47dc00401e8bff00,(more! 0x4ae1550576623caaf2b03f220,0x4af46f326dde05efdeb306ea0,(more! 0xed3ec937c7b40ddccfd10ca0,0xec84deabbf86a4373bf858a0,(more! 0x37c27bff940dfe84dff00940,0x374cd5c29f63eb7ab1f0bcc0,(last! 0x19a2ed43ce70909da500,0x12d8f60e581df638b600))))
private theorem r19 : BlockChecks (S 224928) N P 2440 19 154 :=
  block! 2771,4,0x5d45c8b7bde78e1381d21b800,0x5d45cb869b26744c346639f00,(more! 0x4b0805990fcbb09b6b5a46f80,0x4b1b23211d8c0498bb3a32aa0,(more! 0xed6429e5d1f7f373458ed140,0xecaa02e5892326390f46b140,(more! 0x3678083570fe107a13c0be00,0x3602625ad216a1ddd7013c60,(last! 0x0,0x0))))
private theorem r20 : BlockChecks (S 224982) N P 2440 20 127 :=
  block! 2744,3,0x5d513e724d3423e960d1c8800,0x5d51414156a15d8fbbecce900,(more! 0x4b26224691deea09e98405a80,0x4b3941517a9514653d2bd3aa0,(more! 0xed737637349eb112292fe4e0,0xecb9310931eb53b43ef75be0,(more! 0x353e4cb76c895ada4cf9a940,0x34c8ad16d73688262aa7ea20,(last! 0x0,0x0))))
private theorem r21 : BlockChecks (S 224490) N P 2440 21 99 :=
  block! 2719,2,0x5ce8eeecd15e48a694312e800,0x5ce8f1ba4841df824529bd500,(more! 0x4ae6fbeec5b1e8c89ba4e62a0,0x4afa047131db64e7b10856ae0,(more! 0xec5880db1cc1fb37bac82400,0xeb9f0bbd13ae82a7181ec8c0,(more! 0x33c6af5a33645308d6f01d60,0x3351a5fddaa900c98887a7e0,(last! 0x0,0x0))))
private theorem r22 : BlockChecks (S 224613) N P 2440 22 68 :=
  block! 2696,2,0x5d02fd53f043e3e4128155000,0x5d030021cbc9e3726e0281a00,(more! 0x4b0de82f661a0d9ba88517c60,0x4b20f54713c03d88cb8891320,(more! 0xec8fa7f8c3a67e0e813dc6c0,0xebd6100f907a74bcf9d28580,(more! 0x32c1aa9aeea141cc5c346fa0,0x324c7b3eb91896a90097cc60,(last! 0x0,0x0))))
private theorem r23 : BlockChecks (S 224744) N P 2440 23 35 :=
  block! 2675,1,0x5d1ec197fde1071a2b10d7800,0x5d1ec466449509f02da065700,(more! 0x4b3510bb8c6c33081762c8100,0x4b4822c878eee0bb73fb685a0,(more! 0xeccc4223591fe84f8f993220,0xec128fc6c5d0925be161fe20,(more! 0x31cecc061caa4b55a35a7840,0x3159685be1cbedd5f90519a0,(last! 0x0,0x0))))
theorem none : BlockChecks (terminal .h2395).shape (terminal .h2395).nodeRows
    (terminal .h2395).poleMoment (start .h2395) (threshold .h2395 Option.none) 0 := r0
theorem all : GradeChecks (terminal .h2395) (start .h2395) 1 (grades .h2395) :=
  ⟨r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,trivial⟩
end h2395

namespace h7773
local notation "S" u => (⟨124,173,32,u⟩ : Shape)
local notation "N" => 0xc4fd80000
local notation "P" => 0x15c66e5
private theorem r0 : BlockChecks (S 900) N P 7773 8 0 :=
  block! 54,1,0x1b3cc3c11c249e440,0x1b3cc71f4a35e9580,(last! 0x1b4672ec48744e340,0x1b467aa55176783e0)
private theorem r1 : BlockChecks (S 745) N P 7773 1 27 :=
  block! 60,1,0x12bbb5230da59e080,0x12bbb7ece95903b00,(last! 0x12bbb5d80592e3280,0x12bbbb665cb0cd260)
private theorem r2 : BlockChecks (S 796) N P 7773 2 25 :=
  block! 64,2,0x155b30a8b220bf240,0x155b33a35b4de0980,(last! 0x155b36e1cb524dfc0,0x155b3d053a3bdf700)
private theorem r3 : BlockChecks (S 822) N P 7773 3 23 :=
  block! 68,2,0x16c2706fc001b6ec0,0x16c273834a67e2c80,(last! 0x16c276d0722c597e0,0x16c27d42552466780)
private theorem r4 : BlockChecks (S 877) N P 7773 4 20 :=
  block! 76,3,0x19e00d2a988811d80,0x19e01072c4495d900,(last! 0x19e0131d718440720,0x19e01a3ad5d8d8c00)
private theorem r5 : BlockChecks (S 885) N P 7773 5 16 :=
  block! 67,2,0x1a58541a0c7e85780,0x1a585769e00299500,(last! 0x1a58614b758646f80,0x1a586882d3f877220)
private theorem r6 : BlockChecks (S 899) N P 7773 6 10 :=
  block! 61,1,0x1b2d6acfe1cdcfd00,0x1b2d6e2d1ae6c1e00,(last! 0x1b2d7ef0fdc4f6700,0x1b2d8655ca972fa40)
private theorem r7 : BlockChecks (S 894) N P 7773 7 3 :=
  block! 57,1,0x1ae0ef06cb2bc78c0,0x1ae0f25f3b6afc880,(last! 0x1ae0f62a5705bb080,0x1ae0fd7e82da64300)
theorem none : BlockChecks (terminal .h7773).shape (terminal .h7773).nodeRows
    (terminal .h7773).poleMoment (start .h7773) (threshold .h7773 Option.none) 0 := r0
theorem all : GradeChecks (terminal .h7773) (start .h7773) 1 (grades .h7773) :=
  ⟨r1,r2,r3,r4,r5,r6,r7,trivial⟩
end h7773

set_option maxHeartbeats 800000

private theorem checks (b : Band) (hb : b ≠ .h2367) (x : Test b) :
    let t := tested b x
    BlockChecks t.shape t.nodeRows t.poleMoment (start b) (threshold b x) (seedThreshold b x) := by
  have hn : BlockChecks (terminal b).shape (terminal b).nodeRows (terminal b).poleMoment
      (start b) (threshold b Option.none) 0 := by
    cases b with
    | h2367 => exact False.elim (hb rfl)
    | h2395 => exact h2395.none
    | h7773 => exact h7773.none
  have hc : GradeChecks (terminal b) (start b) 1 (grades b) := by
    cases b with
    | h2367 => exact False.elim (hb rfl)
    | h2395 => exact h2395.all
    | h7773 => exact h7773.all
  cases x with
  | none => exact hn
  | some i => exact grade_at _ _ _ _ hc i

theorem terminal_bounds (b : Band) (hb : b ≠ .h2367) {h : ℕ} (hl : start b ≤ h) (hu : h ≤ finish b) (x : Test b) :
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
  have hc := checks b hb x
  change BlockChecks t.shape t.nodeRows t.poleMoment (start b) (threshold b x) (seedThreshold b x) at hc
  unfold BlockChecks at hc
  rw [blockSurplus_eq t (start b) _ _ (by omega) (by omega) he,
    blockSurplus_eq t (start b+1) _ _ (by omega) hJ he] at hc
  change debit h t < jointGain h t.shape (threshold b x) (seedThreshold b x)
  exact strict_of_first_difference (b := t) hl hh (by omega) (by omega)

#print axioms terminal_bounds
end HighCore82229Terminal
