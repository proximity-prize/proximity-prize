import ProximityPrize.SubmissionLower.HighCore82219TerminalArithmetic

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219Terminal

open HighCore82219
open HighCore82219TerminalArithmetic
open K1_14 (Shape)

private def GradeChecks (t : Bank) (h : ℕ) : ℕ → List Grade → Prop
  | _, [] => True
  | e, g :: gs =>
    BlockChecks ({t.shape with U := g.slots}) t.nodeRows t.poleMoment h e (g.seedCap+1) ∧
      GradeChecks t h (e+1) gs

theorem grade_at (t : Bank) (h : ℕ) (gs : List Grade) (e : ℕ)
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
private theorem r0 : BlockChecks (S 225000) N P 2491 24 0 :=
  block! 2656,15,0x5d559fc501d48caef853ee500,0x5d55a29419fbe2248b9bec400,(more! 0x4cebd7721610f1c1644a48160,0x4cf55c75f51012e9d98c345e0,(more! 0xe29b5a08372aa84308cea1e0,0xe264f8f59b609073bc051160,(last! 0x2401fa82c7db7278281729c0,0x23a2175bd3528e0462cea4c0)))
private theorem r1 : BlockChecks (S 181533) N P 2491 1 366 :=
  block! 2714,1,0x3cc5cf8f8d1532f9e04cf6600,0x3cc5d1d3ba048a946210c3800,(more! 0x3129d30bc01c8b664097e53a0,0x312ffef431eab07c9d6a925e0,(more! 0x93a9e912dc32d02856a76060,0x938d556d95bcb148fd4bf0e0,(more! 0x26145ecc07de46ce40426260,0x25cfc5faae4cf5da73811100,(last! 0x1eb7f6768cdc725c05340,0x1b5cb57fdb344055d85c0))))
private theorem r2 : BlockChecks (S 181341) N P 2491 2 361 :=
  block! 2721,2,0x3ca4f129bb3ba46fec4d9a600,0x3ca4f36d4b147e12c18713800,(more! 0x311f14777e78fede3fe9f1ca0,0x31253ce5d75c0da77d92b0ce0,(more! 0x9340cda3255ce25b3538fba0,0x932395195497a130d4060980,(more! 0x251a46bbf3f15c300d52efc0,0x24d69b6e9a197498f195c4c0,(last! 0x32192232f629c31fee140,0x2da2cbcf41ce7ac0bff20))))
private theorem r3 : BlockChecks (S 186683) N P 2491 3 355 :=
  block! 2744,3,0x40446a750acf29d091d11cc00,0x40446cc9ad4c799114f347000,(more! 0x340071d6fb544c6ce0b74fec0,0x3406fa377d0f300c13f6555c0,(more! 0x9c35216ff34871fdf4881be0,0x9c15f84153a82e4c90f24340,(more! 0x27fd82f8511bc7c6b3be6640,0x27b64a5c4a986a387693ad20,(last! 0xd565b954a2d9f05644ea0,0xca173f6569a73920088e0))))
private theorem r4 : BlockChecks (S 183485) N P 2491 4 350 :=
  block! 2743,3,0x3e15f3041606871a9b9bc8600,0x3e15f54e800534b5ccddeb800,(more! 0x325d519f9082dfbdc4a6a4820,0x3263a01758aed9bcc41081640,(more! 0x96ab9be55d4d83dea4051c00,0x968c85323847bcaccff0fa80,(more! 0x24d4a722e12a7f6de0cd7ac0,0x2490c99b2826e38a5a504b60,(last! 0xa4055914014e4d51d1380,0x9b090711a266efe3249c0))))
private theorem r5 : BlockChecks (S 185397) N P 2491 5 344 :=
  block! 2757,3,0x3f62aebd7ebe4d7530c011e00,0x3f62b10e05124c2822e3b9800,(more! 0x3371d3bac43643261c467ba80,0x3378448dace1aedb274e07560,(more! 0x99d1dcdd7eda693431d101c0,0x99b19b7860cda49805d83540,(more! 0x252b1a51011254123d651900,0x24e679e3d9a7c272565b50c0,(last! 0x11282a0ddeda7a50ce8160,0x10675847a6a1e10eb34da0))))
private theorem r6 : BlockChecks (S 192822) N P 2491 6 337 :=
  block! 2791,4,0x448f7dbe78c27535d79f4bb00,0x448f8026b9f8434ece385bc00,(more! 0x3792106ec20b8282e723eddc0,0x37990a596b16994c9b2843c60,(more! 0xa69fdab81bfa0d670daaf200,0xa67ce62a14e8babb01735fc0,(more! 0x290b72129d0129556bc963a0,0x28c1a836bbe66f9d4b64e7e0,(last! 0x2bfff9deb0d57cceefd960,0x2aa6535a6f25f17d3f3c20))))
private theorem r7 : BlockChecks (S 189998) N P 2491 7 331 :=
  block! 2793,5,0x42917e148b1297c5dafe0d300,0x42918073c5c83e6e9d2489c00,(more! 0x3614d98e733c7bc22444af920,0x361b9e8a644a8c8b50b4bd740,(more! 0xa18fc449309106e913fc9e60,0xa16cdf625abba208bce6f5a0,(more! 0x261636d246830dc83ed41ac0,0x25cf686090ad6c22f7c89600,(last! 0x24c188732c11b431996c40,0x23a0eea5725c4fd4bd4200))))
private theorem r8 : BlockChecks (S 201376) N P 2491 8 323 :=
  block! 2842,6,0x4ac62dc0f5b53baa404d6bd00,0x4ac630448d82708af0994a400,(more! 0x3c9fec78c7d2e00a963f1e720,0x3ca78af410cca58991989a260,(more! 0xb5e60aa2d6ea04a65852b3a0,0xb5bf09a1b5f81169e7558da0,(more! 0x2c28095e4d51695fb61352c0,0x2bd8b899553588d7bfab63e0,(last! 0x56825516081941776e2080,0x54949d517c802f71387b40))))
private theorem r9 : BlockChecks (S 197135) N P 2491 9 316 :=
  block! 2842,6,0x47a8e809066c8bc4466e3d000,0x47a8ea7f106244df8a3aa4000,(more! 0x3a41babc8beaa7d5ea17dcd00,0x3a4906761c7dd3271327e9ec0,(more! 0xae09824a39c5f02861d17b00,0xade30e49cabb6b799336b040,(more! 0x2829321c8079d96543ee7fc0,0x27ddff309b2ef918c2885800,(last! 0x409ccd1a3595fd855bb2c0,0x3f1f7d55f9047360dec6c0))))
private theorem r10 : BlockChecks (S 205550) N P 2491 10 307 :=
  block! 2888,8,0x4de76a03700f2d48daca29300,0x4de76c945ee2af4f34b539c00,(more! 0x3f4b00b75a90d81fc049bd040,0x3f52f1ea36ca4333eea5f0760,(more! 0xbd77fc589cf5240fc3ff7a80,0xbd4e11507f5e9fc272f46e40,(more! 0x2bf1c095cd3c80e2eb371460,0x2ba02d87cd6f4b47f4f252c0,(last! 0x5d5e59207ab7600291b6c0,0x5b825bf2c38eb8df1c0540))))
private theorem r11 : BlockChecks (S 215543) N P 2491 11 297 :=
  block! 2944,10,0x55a865aa1fcacef82eb0d1800,0x55a8685afe8cf53530cb6e000,(more! 0x458e2ee580c1b4183fc8d8820,0x4596edafd8b4c5b6eb750f660,(more! 0xd0a5c5675f0c841e145b8220,0xd077997356238a24925afa40,(more! 0x30895c570eb87df749eb2a60,0x302faaa33e2550d9761e8fa0,(last! 0x74dd6cd951fd7480724520,0x72b156d7c9d64e168fa000))))
private theorem r12 : BlockChecks (S 218969) N P 2491 12 286 :=
  block! 2984,12,0x58669a1023578bbc01e563200,0x58669ccbf52309b472c44a800,(more! 0x47dc29fbbc1e90d65e9bc42e0,0x47e531571d437b669cf243800,(more! 0xd758c2e934f543a15c483e40,0xd72888ca02e378e1fbc83fe0,(more! 0x30ed208c43f591d048e192a0,0x3090c89f6efd8862e1565240,(last! 0x61b49fe4729c14d25da620,0x5fc29d9fadc67cf5187d60))))
private theorem r13 : BlockChecks (S 222566) N P 2491 13 273 :=
  block! 3027,14,0x5b53c3a864c743e02c9162b00,0x5b53c66fb58421c4a1dfc7c00,(more! 0x4a51ce89a825a4298bed9bc40,0x4a5b2344a8f4638c056f91500,(more! 0xde7ee64b54cffc8285764540,0xde4c8d806d1284f53112e8a0,(more! 0x315a042e9c18194c633aa080,0x30fab47e0fc2f20682f10da0,(last! 0x47024eed20be5dbf145ce0,0x45607a8ffe07a208045b40))))
private theorem r14 : BlockChecks (S 224442) N P 2491 14 258 :=
  block! 2969,11,0x5cdf53bbc213daf209b5caf00,0x5cdf568911b1d24fcf8bc4c00,(more! 0x4badbaa6bde817c509d774ea0,0x4bb7380165b354ed268d60ae0,(more! 0xe23519223252e8f7c00eac80,0xe201549c57ec469c988a40a0,(more! 0x30bbd6feac30317e42486e40,0x305b00a28aa1a375abdb73a0,(last! 0x293dedbcba716baca814c0,0x280ccdffcae9fc2fc2bb80))))
private theorem r15 : BlockChecks (S 223407) N P 2491 15 242 :=
  block! 2919,9,0x5c04aeb61719e9015ac13f000,0x5c04b18017eaa154027d8c000,(more! 0x4b1c659e2f2062d707c687e20,0x4b25cbdf3f0f888c6d657a060,(more! 0xdff6388f4ae25e4389cdf4a0,0xdfc23df55548c7ed4fa6e960,(more! 0x2e7dcade828722cdf0ffb000,0x2e1e17d2be42d59ea2eb3860,(last! 0x1128d7b28884e26abaa680,0x1077782f51e13215cd33a0))))
private theorem r16 : BlockChecks (S 224228) N P 2491 16 223 :=
  block! 2875,8,0x5cb2095d240672f9e7abd7100,0x5cb20c29c48e03464a87a3400,(more! 0x4bc350ea65fd3e2531b6406c0,0x4bccc8aceafd4c4ee241ce740,(more! 0xe187b2844f484c6d9bcd6da0,0xe152e0fc8263c8719a0add00,(more! 0x2d5ff2701f174d8fb42f0460,0x2cff9d89a9e2dfa7e1f1e5c0,(last! 0x47d5327cde403cf9f6060,0x430436f7ba6d1689483e0))))
private theorem r17 : BlockChecks (S 224635) N P 2491 17 202 :=
  block! 2837,6,0x5d0835d156f1146b1aa7d0c00,0x5d08389f4476fd132c98d7000,(more! 0x4c2294e3f165256fc7b650400,0x4c2c151a55bbe40325973edc0,(more! 0xe2432d6372fcbc7397df8660,0xe20dc4cd6e6717bffff01a20,(more! 0x2c17418ee732c7dd32e38960,0x2bb6bc345bd107146b880f00,(last! 0x3b2f483796a3685b3d80,0x302e52c7b91a53e7e100))))
private theorem r18 : BlockChecks (S 224832) N P 2491 18 179 :=
  block! 2802,5,0x5d31fa16839469e709547dd00,0x5d31fce512481123e5a372400,(more! 0x4c5c69cc93c5a1e47f0bbdda0,0x4c65eddb9785de2a0153a0d20,(more! 0xe29342872b51d408821f4a20,0xe25d6e1065b5d8f232b20840,(more! 0x2ac65d215e7322ba3f9dd700,0x2a65fbf8db040b19895d2340,(last! 0x0,0x0))))
private theorem r19 : BlockChecks (S 224928) N P 2491 19 154 :=
  block! 2771,4,0x5d4657edd16f6b5f15542bd00,0x5d465abcaeae5197c7e84a400,(more! 0x4c835ae8b4b5a4a3f012f3160,0x4c8ce09973fcebf54f8c9f840,(more! 0xe2b1360eb5ce2b768167dec0,0xe27b1511d9950424988e3aa0,(more! 0x297f34fa03c5991825152440,0x291f06a581e429f7ebe89c40,(last! 0x0,0x0))))
private theorem r20 : BlockChecks (S 224982) N P 2491 20 127 :=
  block! 2744,3,0x5d51cdb12df6a00d8733fdb00,0x5d51d0803763d9b3e24f03c00,(more! 0x4ca193a8d89f6ea9ca050a020,0x4cab1a110b6d2ef40737849c0,(more! 0xe2bc144bc6e2d5806ef4f520,0xe285bf2ea1f1c1bae84d86a0,(more! 0x2848269d9627f4e6a473cfe0,0x27e8212c4e6ac4bbde683880,(last! 0x0,0x0))))
private theorem r21 : BlockChecks (S 224490) N P 2491 21 99 :=
  block! 2719,2,0x5ce97ddb80b5566ad5b5a1f00,0x5ce980a8f798ed4686ae30c00,(more! 0x4c60ac88ecebdb91f599afd40,0x4c6a27b109c3bc0eca626bb80,(more! 0xe1aaaafaa3f32626a478e820,0xe17469b06966c6aeedd9f640,(more! 0x26e303b75f603e1c04110840,0x26839c410915636627c487e0,(last! 0x0,0x0))))
private theorem r22 : BlockChecks (S 224613) N P 2491 22 68 :=
  block! 2696,1,0x5d038c56abf5cd404d3d38e00,0x5d038f24877bcccea8be65800,(more! 0x4c87f20b788b590af625e1500,0x4c916f73f1d14e430724508c0,(more! 0xe1dfae1856877f6f95afae20,0xe1a956c26b752d8c60a457a0,(more! 0x25da8fed98b3e0d1856dfae0,0x257b1b0667d2823522935a00,(last! 0x0,0x0))))
private theorem r23 : BlockChecks (S 224744) N P 2491 23 35 :=
  block! 2675,16,0x5d1f50b013bd97bcadaa1e500,0x5d1f537e5a719a92b039ac400,(more! 0x4caf7b63fbd43124575ef1c00,0x4cb8fb3d37fcb43359e8cf660,(more! 0xe21bca90869ce6c43d1dfe60,0xe1e56da94e3e3f4cd3833180,(last! 0x24e223792f8c4ec7c20e6680,0x24828da9d2813d1aef468920)))
theorem none : BlockChecks (terminal .h2395).shape (terminal .h2395).nodeRows
    (terminal .h2395).poleMoment (start .h2395) (threshold .h2395 Option.none) 0 := r0
theorem all : GradeChecks (terminal .h2395) (start .h2395) 1 (grades .h2395) :=
  ⟨r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,trivial⟩
end h2395

namespace h7773
local notation "S" u => (⟨124,173,32,u⟩ : Shape)
local notation "N" => 0xc4fd80000
local notation "P" => 0x15c66e5
private theorem r0 : BlockChecks (S 900) N P 7880 8 0 :=
  block! 54,1,0x1b3e2c1e5d5effa00,0x1b3e2f7c8b704ab40,(last! 0x1b47ff2a233d70a20,0x1b4806e32c3f9aac0)
private theorem r1 : BlockChecks (S 745) N P 7880 1 27 :=
  block! 60,1,0x12bcdf81e1a11b400,0x12bce24bbd5480e80,(last! 0x12bce16c8c569a920,0x12bce6fae37484900)
private theorem r2 : BlockChecks (S 796) N P 7880 2 25 :=
  block! 64,1,0x155c6f6d67fdbaa00,0x155c7268112adc140,(last! 0x155c771b0c9f57da0,0x155c7d3e7b993dbc0)
private theorem r3 : BlockChecks (S 822) N P 7880 3 23 :=
  block! 68,2,0x16c3b99a98b60be00,0x16c3bcae231c37bc0,(last! 0x16c3c1873002c45e0,0x16c3c7f91484dcee0)
private theorem r4 : BlockChecks (S 877) N P 7880 4 20 :=
  block! 76,3,0x19e16c54e252b7c00,0x19e16f9d0e1403780,(last! 0x19e1740070e2a9c00,0x19e17b1ddda3c2a00)
private theorem r5 : BlockChecks (S 885) N P 7880 5 16 :=
  block! 67,2,0x1a59b67774b2d0c00,0x1a59b9c74836e4980,(last! 0x1a59c5889957d9460,0x1a59ccbff7ca09700)
private theorem r6 : BlockChecks (S 899) N P 7880 6 10 :=
  block! 61,1,0x1b2ed2c6bf3afc800,0x1b2ed623f853ee900,(last! 0x1b2ee8edd31784ac0,0x1b2ef0529fe9bde00)
private theorem r7 : BlockChecks (S 894) N P 7880 7 3 :=
  block! 57,1,0x1ae254fdb596ece00,0x1ae2585625d621dc0,(last! 0x1ae25df47ebfdec00,0x1ae26548aa9487e80)
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

end HighCore82219Terminal
