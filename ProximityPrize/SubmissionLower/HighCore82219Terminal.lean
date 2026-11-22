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
private theorem r0 : BlockChecks (S 225000) N P 2466 24 0 :=
  block! 2656,16,0x5d55598ba5fd3433964c21e00,0x5d555c5abe2489a929941fd00,(more! 0x4c3833b08aaa94cf217006840,0x4c41c3980f79f1e62c9406de0,(more! 0xe7e05a561583718c0f78fe00,0xe81d34fb42dbba10be119440,(last! 0x29f374e888026b448b554de0,0x291fa7c5404fd6ca2721d3c0)))
private theorem r1 : BlockChecks (S 181533) N P 2466 1 366 :=
  block! 2714,2,0x3cc596e729b5a4e3342dee400,0x3cc5992b56a4fc7db5f1bb600,(more! 0x30b55cad38319b77e9c707bc0,0x30bb8f8480be81ce3d8944b00,(more! 0x96bbfea821cd25f7d3cf9200,0x96edc505c9e5842d6c688ea0,(more! 0x2a436e39fe118a16cc7f89a0,0x29b03e1549ad69d561a32680,(last! 0x5083090c1b6d9fcbbcc00,0x4a0d9d444eb0f25085a40))))
private theorem r2 : BlockChecks (S 181341) N P 2466 2 361 :=
  block! 2721,2,0x3ca4b890af0e638919b0c6400,0x3ca4bad43ee73d2beeea3f600,(more! 0x30aadfec2ed0c3d8fa4a8ace0,0x30b10f45ffc02ce635c753b40,(more! 0x965aaa10e50de89fdcbf8ac0,0x968b30f1f2a183f0bd64bd00,(more! 0x293cb479f5d5f293eb0cb800,0x28ab0ed011df123f61679c00,(last! 0x6fcaef2594efa006c5740,0x6817e0ae50a7ed1e518c0))))
private theorem r3 : BlockChecks (S 186683) N P 2466 3 355 :=
  block! 2744,3,0x404430312c926003c37afc800,0x40443285cf0fafc4469d26c00,(more! 0x33852a13eba6da95162ac1c80,0x338bb9cb814fb443e7f55f6a0,(more! 0x9f81a73721c15301c02f1140,0x9fb4d9dea4fb9a54dea1a060,(more! 0x2c59a8ff838ce5e56b9ddee0,0x2bbfe82247c5ac8d7d945d80,(last! 0x15eee5ab21aff18c765ae0,0x14f0f1d55396daf89ed600))))
private theorem r4 : BlockChecks (S 183485) N P 2466 4 350 :=
  block! 2743,3,0x3e15b9bfbc2792f2cc265a400,0x3e15bc0a2626408dfd687d600,(more! 0x31e64f58e806752f9b76facc0,0x31eca4e7bca25fc34a6ddcb60,(more! 0x99e856a2dcd925677b688a00,0x9a182757ab9e134d3518e8c0,(more! 0x28fe02e76f5eb14b965f9ac0,0x286b092d48dfe833d1b317a0,(last! 0x1122aca9fc2a4e81d3c720,0x10563b6726d56832d8fd20))))
private theorem r5 : BlockChecks (S 185397) N P 2466 5 344 :=
  block! 2757,4,0x3f6274e0608a6dfb8b44b3400,0x3f627730e6de6cae7d685ae00,(more! 0x32f8490be69fecc65d1be3440,0x32fec11ce2ca373cd5c7d6e20,(more! 0x9d2713974c92082497fcec40,0x9d5716f656b242616f4ce000,(more! 0x296278252109ccfedca507c0,0x28cd5fa723b4262c86191ce0,(last! 0x1a0bb54752740772ec2360,0x190a48fdc509215bcacce0))))
private theorem r6 : BlockChecks (S 192822) N P 2466 6 337 :=
  block! 2791,5,0x448f41901a8154c5c2acba200,0x448f43f85bb722deb945ca300,(more! 0x370e69cc5430db97065528ea0,0x37156b8f185ff02ff20c67240,(more! 0xaa3c6e976e498c83c6e6c280,0xaa70642e2a631e41ad005b20,(more! 0x2d96c3a7defd983cd2ab9880,0x2cf5e2ddf8442e6d18dcec80,(last! 0x3b35bae4ee12dc083c0280,0x398b556ffe122fd6c9b300))))
private theorem r7 : BlockChecks (S 189998) N P 2466 7 331 :=
  block! 2793,5,0x429142c7cf55514ae53be3200,0x429145270a0af7f3a7625fb00,(more! 0x35951a770e2246af4cce0ddc0,0x359be710bff31d190d2a66fa0,(more! 0xa51dfb5cea72306700857ae0,0xa54ed6eb2526899d4bd4aca0,(more! 0x2a73f49c7f02eb3442c7f8e0,0x29d9304a8e96e1b9dd94b440,(last! 0x3179edc17dbfb84994ab80,0x3014dcc097a31e58be29c0))))
private theorem r8 : BlockChecks (S 201376) N P 2466 8 323 :=
  block! 2842,7,0x4ac5eee722ab11b908e4b2e00,0x4ac5f16aba784699b93091500,(more! 0x3c10238ff27b70036c1a00b60,0x3c17ca9d9eb46112135cc4d00,(more! 0xb9e317ca4304dda98fdf1320,0xba1a80e781f75c00f03d58c0,(more! 0x310ef7f85d7206e3a82acdc0,0x30610b274b95db1cb2184580,(last! 0x6ba65efba0f965c6c256e0,0x696167935fbec938165fe0))))
private theorem r9 : BlockChecks (S 197135) N P 2466 9 316 :=
  block! 2842,7,0x47a8aa820d6d781aa7782e000,0x47a8acf817633135eb4495000,(more! 0x39b80c71823d37151ccf8dec0,0x39bf6061e75dd8140a50b9a40,(more! 0xb1e9fd562ce8eec5d9351540,0xb21d481fddd30a4800ad7880,(more! 0x2ccfd492b7e8cde7c4e6acc0,0x2c2aa6b0274ac4e201519740,(last! 0x51051e746ac485a909c940,0x4f4087156132fb117b2100))))
private theorem r10 : BlockChecks (S 205550) N P 2466 10 307 :=
  block! 2888,9,0x4de729dc1d677aaa12d58b200,0x4de72c6d0c3afcb06cc09bb00,(more! 0x3eb51ed69a700277087b349e0,0x3ebd18fb87fd1695d7ecff720,(more! 0xc1b14c80a05953d9a5813500,0xc1e90b1a9436e552724d3960,(more! 0x30fec853494fe7a3897a33e0,0x304b4bdcf2f1abc46ceba4a0,(last! 0x71a6935b561650e9e2dbc0,0x6f7b33d6f0c9a48652f000))))
private theorem r11 : BlockChecks (S 215543) N P 2466 11 297 :=
  block! 2944,11,0x55a822645ed51302fa1789000,0x55a825153d97393ffc3225800,(more! 0x44e9241f5c56325a8e3e89260,0x44f1ecc50ecd4575097684040,(more! 0xd54cbe1e704530d40f15d600,0xd58a1bbc2f139a046e3de000,(more! 0x3617d36efe5ea97186947c60,0x355252ba4392bc12b0054b20,(last! 0x8c77df5290e26ca5e7c140,0x89f37a6fdc0f6166fd0c80))))
private theorem r12 : BlockChecks (S 218969) N P 2466 12 286 :=
  block! 2984,12,0x586655b8a6783e78fc20cac00,0x586658747843bc716cffb2200,(more! 0x4731c5a9af1a99ba3dc599300,0x473ad734f44cd3920f7a352a0,(more! 0xdc2dd8ebb236dda302212920,0xdc6c5115fc87a0489c65d2e0,(more! 0x36a561c79ecc150e5362b7e0,0x35da08f9c61507d7e9769420,(last! 0x76f45414c3efc531f14f40,0x74ade26784c88296e52cc0))))
private theorem r13 : BlockChecks (S 222566) N P 2466 13 273 :=
  block! 3027,14,0x5b537e3182559890b7e984200,0x5b5380f8d31276752d37e9300,(more! 0x49a1b5f47277e507f75c37da0,0x49ab153a500dbed61ced57b20,(more! 0xe3842ead1b26e7ff1b9343a0,0xe3c3f2391985e8e76bb4e700,(more! 0x374086280a01c7838bccb200,0x366ec1625ba7c97d2c347b20,(last! 0x590697eed7f6b52c2be6c0,0x5714caf3e2c3b00bfa2ee0))))
private theorem r14 : BlockChecks (S 224442) N P 2466 14 258 :=
  block! 2969,12,0x5cdf0daefba6b2c9b7d065a00,0x5cdf107c4b44aa277da65f700,(more! 0x4afaa39b672d2e79a45528a40,0x4b042bb2daab1d01b18488d80,(more! 0xe757c7c79e1d0fa50d022dc0,0xe797bd5c40bac48884e27fa0,(more! 0x36b96a338fb59e7b39d9d5c0,0x35e47577fa16d3b21d448700,(last! 0x36abca896d428b3111fc40,0x353319bc91b5c1467d6580))))
private theorem r15 : BlockChecks (S 223407) N P 2466 15 242 :=
  block! 2919,10,0x5c0468fc02b7e8eef95dba000,0x5c046bc60388a141a11a07000,(more! 0x4a6b03145fb330142306439c0,0x4a7473fbca20edcad00b224e0,(more! 0xe515c2613cdcc4eb578bb380,0xe553fff21999e6e7cc9fb080,(more! 0x34688afb712b59eb80aa3540,0x33962ebaa94daf4304f49ca0,(last! 0x194a7e1767667b9cc31200,0x185fb9d387ed976caa4b40))))
private theorem r16 : BlockChecks (S 224228) N P 2466 16 223 :=
  block! 2875,8,0x5cb1c36176c95b844034e6600,0x5cb1c62e1750ebd0a310b2900,(more! 0x4b10a458114cacfd22708a280,0x4b1a26d88f0331b91ddce4c60,(more! 0xe6b6df6710b666dc1356aac0,0xe6f4da2df6289169dc50f7a0,(more! 0x3353ec8b95fc5013535f3640,0x328049b314d3552fa94b7060,(last! 0x85fd6ae603d53a68591a0,0x7e8815216c66767145a40))))
private theorem r17 : BlockChecks (S 224635) N P 2466 17 202 :=
  block! 2837,7,0x5d07efb524dd5c015a1e34800,0x5d07f283126344a96c0f3ac00,(more! 0x4b6f492e6af42983ddb3fd500,0x4b78d42fedc1ca3bf7f6f3540,(more! 0xe77c4ac44402c7e31fc84ea0,0xe7b9ded1ae76dcec77498c80,(more! 0x320e4728d451ca6345966ec0,0x313a2d57a97a5034fb315f80,(last! 0x112bcee2ce5e3b612c3a0,0xf2d3b052f8ee7e79bf00))))
private theorem r18 : BlockChecks (S 224832) N P 2466 18 179 :=
  block! 2802,5,0x5d31b3ea940914f5859e9ee00,0x5d31b6b922bcbc3261ed93500,(more! 0x4ba8d5e6770a81fe52bd12760,0x4bb264c84a615eea2f702f980,(more! 0xe7d2d54d8dfb67e0e66c2460,0xe81002b94c09fc14b2487a60,(more! 0x30bc477802b137a652071940,0x2fe837365651a3d8cb046f80,(last! 0x0,0x0))))
private theorem r19 : BlockChecks (S 224928) N P 2466 19 154 :=
  block! 2771,4,0x5d4611ba364aefd5a4dd32e00,0x5d4614891389d60e577151500,(more! 0x4bcfa89bfa9b0b47f76088040,0x4bd939247f80996b370269e40,(more! 0xe7f4fd0a459c202267d5e9c0,0xe831d65863603f5a4143d5e0,(more! 0x2f72d1658dd2ec86e2edb860,0x2e9efb3ffe68ed3a602e44e0,(last! 0x0,0x0))))
private theorem r20 : BlockChecks (S 224982) N P 2466 20 127 :=
  block! 2744,3,0x5d518779424bfecea19066200,0x5d518a484bb93874fcab6c300,(more! 0x4bedd4383688ca510ac170a20,0x4bf7657be4bc4b492d8cff460,(more! 0xe8027f5df75cca3493bd02a0,0xe83f205c49260699ecd81d00,(more! 0x2e39f131ba4cca885bda4e00,0x2d6647e36b80c87f5199b620,(last! 0x0,0x0))))
private theorem r21 : BlockChecks (S 224490) N P 2466 21 99 :=
  block! 2719,2,0x5ce937cae47b9af68d6fafa00,0x5ce93a985b5f31d23e683e700,(more! 0x4badc1d46492c1c7df6273d00,0x4bb747cdc31859973f0146ee0,(more! 0xe6ecdae5c6f732e34be8c920,0xe728ffc8068cb79a736858e0,(more! 0x2ccbbf97074d49574082f9e0,0x2bf944d636013b705589d960,(last! 0x0,0x0))))
private theorem r22 : BlockChecks (S 224613) N P 2466 22 68 :=
  block! 2696,1,0x5d03463c3bdfd8595d9fdd400,0x5d03490a1765d7e7b92109e00,(more! 0x4bd4dd32275f612e80056b320,0x4bde6570fedf83c5c0d4d38c0,(more! 0xe72335a26bd7625e8fb9f480,0xe75f70cbebf1141c1f76b820,(more! 0x2bc49634d495699cb4503360,0x2af1e15e5f31439f7b8c94c0,(last! 0x0,0x0))))
private theorem r23 : BlockChecks (S 224744) N P 2466 23 35 :=
  block! 2675,16,0x5d1f0a8b2c2950d66da541e00,0x5d1f0d5972dd53ac7034cfd00,(more! 0x4bfc38d152fd0b6b89eac0840,0x4c05c3861266c3c5fdb14c840,(more! 0xe75fc824ec366d9b5762bbc0,0xe79c3ab5f9d68cf03e06b480,(last! 0x2ace8efa3cdab90f18a595e0,0x29fb7bf05e8162fe5bf25700)))
theorem none : BlockChecks (terminal .h2395).shape (terminal .h2395).nodeRows
    (terminal .h2395).poleMoment (start .h2395) (threshold .h2395 Option.none) 0 := r0
theorem all : GradeChecks (terminal .h2395) (start .h2395) 1 (grades .h2395) :=
  ⟨r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,trivial⟩
end h2395

namespace h7773
local notation "S" u => (⟨124,173,32,u⟩ : Shape)
local notation "N" => 0xc4fd80000
local notation "P" => 0x15c66e5
private theorem r0 : BlockChecks (S 900) N P 7827 8 0 :=
  block! 54,1,0x1b3d799ed3ca747c0,0x1b3d7cfd01dbbf900,(last! 0x1b473ce7ba59f4700,0x1b4744a0c35c1e7a0)
private theorem r1 : BlockChecks (S 745) N P 7827 1 27 :=
  block! 60,1,0x12bc4bb7657d0f780,0x12bc4e81413075200,(last! 0x12bc4e697483b3dc0,0x12bc53f7cba19dda0)
private theorem r2 : BlockChecks (S 796) N P 7827 2 25 :=
  block! 64,1,0x155bd18861a5cd9c0,0x155bd4830ad2ef100,(last! 0x155bda102325dc700,0x155be033921fc2520)
private theorem r3 : BlockChecks (S 822) N P 7827 3 23 :=
  block! 68,2,0x16c3168ef18ef7540,0x16c319a27bf523300,(last! 0x16c31f64bbcb88ce0,0x16c325d6a04da15e0)
private theorem r4 : BlockChecks (S 877) N P 7827 4 20 :=
  block! 76,3,0x19e0be63d34e0aa80,0x19e0c1abff0f56600,(last! 0x19e0c71d7e15e6100,0x19e0ce3aead6fef00)
private theorem r5 : BlockChecks (S 885) N P 7827 5 16 :=
  block! 67,2,0x1a5906f0aa5ab5080,0x1a590a407ddec8e00,(last! 0x1a591705b6a828340,0x1a591e3d151a585e0)
private theorem r6 : BlockChecks (S 899) N P 7827 6 10 :=
  block! 61,1,0x1b2e2079ed10df300,0x1b2e23d72629d1400,(last! 0x1b2e37a1ced75a280,0x1b2e3f069ba9935c0)
private theorem r7 : BlockChecks (S 894) N P 7827 7 3 :=
  block! 57,1,0x1ae1a3ae7880f4b40,0x1ae1a706e8c029b00,(last! 0x1ae1adb980cd21780,0x1ae1b50daca1caa00)
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
end HighCore82219Terminal
