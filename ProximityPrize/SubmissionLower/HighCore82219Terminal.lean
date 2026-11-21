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

namespace h2405
local notation "S" u => (⟨7052,9807,2078,u⟩ : Shape)
local notation "N" => 0x24c0a185540000
local notation "P" => 0xe2d5b7791e37
private theorem r0 : BlockChecks (S 219723) N P 2405 25 0 :=
  block! 2471,7,0x48b2569bf0e4aafcb1ba15500,0x48b258b2ad716d5d460528600,(more! 0x3f7dc618304158fa8d53b20c0,0x3f857124a4dc4169517b3c700,(more! 0x91c4e705d3c9379d52ccea40,0x9157d17a67e9a7f102564740,(last! 0x195e5f54f1fb1c774fa3600,0x189e3ff100d8c1a072b5b40)))
private theorem r1 : BlockChecks (S 219723) N P 2405 1 394 :=
  block! 2636,14,0x48b2569bf0e4aafcb1ba15500,0x48b258b2ad716d5d460528600,(more! 0x3d56ba6a39775cf4a2b49f6c0,0x3d5e6fc5412d6f36f203db3a0,(more! 0xa315d42e57a2ac61d9a47b60,0xa2c624a289c7cba289879320,(last! 0x12a47adb33f7268dea98fea0,0x127a6c59bd6b5d068b46c8e0)))
private theorem r2 : BlockChecks (S 219723) N P 2405 2 387 :=
  block! 2646,14,0x48b2569bf0e4aafcb1ba15500,0x48b258b2ad716d5d460528600,(more! 0x3d6ecfd0c939630f955855460,0x3d76851c389169fdb40666ee0,(more! 0xa228e0e4b0cf255867181960,0xa1d7ca7d4def623af509ea20,(last! 0x120f9e47fda75b35cd770e60,0x11e6f78d68d1f585749153a0)))
private theorem r3 : BlockChecks (S 219723) N P 2405 3 381 :=
  block! 2655,14,0x48b2569bf0e4aafcb1ba15500,0x48b258b2ad716d5d460528600,(more! 0x3d8b53e6b43bc23b9f9c5eec0,0x3d9308ddd3792b9a702845760,(more! 0xa1252469409edca991e3aa80,0xa0d28666d78e345c1a70cc60,(last! 0x114c0cfc8fac1ec475963b60,0x1124f33ac960a7146def7700)))
private theorem r4 : BlockChecks (S 219723) N P 2405 4 374 :=
  block! 2666,15,0x48b2569bf0e4aafcb1ba15500,0x48b258b2ad716d5d460528600,(more! 0x3da5ae3d2906af65d9f91afe0,0x3dad6305980b63bf690d69060,(more! 0xa0334e7092aa6ce030c74aa0,0x9fdf41144a20cbddb8ad7040,(last! 0x109859ad142028039fd8f780,0x1072b231c935d553c94e1940)))
private theorem r5 : BlockChecks (S 219723) N P 2405 5 366 :=
  block! 2679,15,0x48b2569bf0e4aafcb1ba15500,0x48b258b2ad716d5d460528600,(more! 0x3dbe47a8fb195ee9c5545dc60,0x3dc5fc6582b77bbe537bc6540,(more! 0x9f51e32cf8fc7e0d7f8bbb20,0x9efc7b45e06dcbb7b9d51140,(last! 0xfef7ec977641cd99983ba00,0xfcb32831acb15d6bc6f09e0)))
private theorem r6 : BlockChecks (S 219723) N P 2405 6 358 :=
  block! 2692,16,0x48b2569bf0e4aafcb1ba15500,0x48b258b2ad716d5d460528600,(more! 0x3dd8558924690cf52a10d3220,0x3de00a2483791b4a42c055620,(more! 0x9e6cb2fa188ff6a8e594c6a0,0x9e15eaa6c3acb1ed63ddae60,(last! 0xf33876a8ca768405987ef00,0xf109d995ef662807feffd40)))
private theorem r7 : BlockChecks (S 219723) N P 2405 7 350 :=
  block! 2706,16,0x48b2569bf0e4aafcb1ba15500,0x48b258b2ad716d5d460528600,(more! 0x3df3d1dbc7492f1679818dba0,0x3dfb863de52b3e84c35193a40,(more! 0x9d8398cfb28737d999043120,0x9d2b6af5dabae86820abc540,(last! 0xe65076426fb1102f2043100,0xe4386b048e9bc3ddf4860e0)))
private theorem r8 : BlockChecks (S 219723) N P 2405 8 342 :=
  block! 2721,1,0x48b2569bf0e4aafcb1ba15500,0x48b258b2ad716d5d460528600,(more! 0x3e10af5230101df9ffd037e60,0x3e18635fb869d372d5ceeb2a0,(more! 0x9c96650cf1611672d27f6ea0,0x9c3ccd6092ed11ad15215ba0,(more! 0xd85132fdbac7159cfcec3c0,0xd6501fb86996cca47ec1f40,(last! 0xdc65e4aafcb640e0e0,0x898db6e8fea19dbb40))))
private theorem r9 : BlockChecks (S 219723) N P 2405 9 332 :=
  block! 2740,1,0x48b2569bf0e4aafcb1ba15500,0x48b258b2ad716d5d460528600,(more! 0x3e2a3cc53fac7f7ea3eec8c80,0x3e31f0c37d1adbf83ad1a4a00,(more! 0x9bc7339a8896a16d514bd240,0x9b6c55e8b3b562e20119b7c0,(more! 0xcba6c15d899284f4cff7200,0xc9ba436a26507846d4af8c0,(last! 0x17f6ef425d549ca20380,0x152d985bc15d1ef2f300))))
private theorem r10 : BlockChecks (S 219723) N P 2405 10 323 :=
  block! 2759,2,0x48b2569bf0e4aafcb1ba15500,0x48b258b2ad716d5d460528600,(more! 0x3e47c7b21e49587f637ca23e0,0x3e4f7b4740870143cf3e870e0,(more! 0x9ae07fc56279fe09e242d560,0x9a84421ea5b83f32b349d2e0,(more! 0xbc94c09247b9f2a02d3b5e0,0xbabeb9152672ce18fd7fba0,(last! 0x2e26e6f41716a7cdcc60,0x2a93f58a24e82d9cca20))))
private theorem r11 : BlockChecks (S 219723) N P 2405 11 312 :=
  block! 2783,3,0x48b2569bf0e4aafcb1ba15500,0x48b258b2ad716d5d460528600,(more! 0x3e62bbac8b0571f6ec12e3480,0x3e6a6f0a55b549f6b5ff63880,(more! 0x9a139c38fbf96a2150476400,0x99b61d03559b00b237c15840,(more! 0xae6b470649e21c9b01ee100,0xaca9790470f719e6af7b980,(last! 0x1db1f12e3f75a255c580,0x1b805634a62a5873a9c0))))
private theorem r12 : BlockChecks (S 219723) N P 2405 12 300 :=
  block! 2811,4,0x48b2569bf0e4aafcb1ba15500,0x48b258b2ad716d5d460528600,(more! 0x3e7da2779bbe2616e84045ac0,0x3e85558dce8f178dd6173bf00,(more! 0x994ca1c5c6956cab0aeda000,0x98ede959d5acaea64688a1c0,(more! 0x9ff3d6403fb190ffc6e5180,0x9e45c004adaadace80cb900,(last! 0xadbc3ae0b1807f500,0x526e765d32100c2c0))))
private theorem r13 : BlockChecks (S 219723) N P 2405 13 286 :=
  block! 2833,5,0x48b2569bf0e4aafcb1ba15500,0x48b258b2ad716d5d460528600,(more! 0x3e96e0c8d969f076db5268f40,0x3e9e939dfc0ec5c0d6c04eb60,(more! 0x9897855a2c5ad2d15a259d20,0x9837a94ba34518a6d5cdb8a0,(more! 0x91fdc6ab537cf83c7477b20,0x90622a041457be48e90fdc0,(last! 0,0))))
private theorem r14 : BlockChecks (S 219723) N P 2405 14 271 :=
  block! 2779,3,0x48b2569bf0e4aafcb1ba15500,0x48b258b2ad716d5d460528600,(more! 0x3eb02eaa9191206bc88b89d80,0x3eb7e10c200d8dbfdf28130e0,(more! 0x97e2d582b6fa3606ca8ba0c0,0x9781d8e17183e260e5de0d40,(more! 0x83ff2e36ff5f19499eaeea0,0x82760e8407bba2f3b29adc0,(last! 0,0))))
private theorem r15 : BlockChecks (S 219723) N P 2405 15 254 :=
  block! 2732,1,0x48b2569bf0e4aafcb1ba15500,0x48b258b2ad716d5d460528600,(more! 0x3ec7e0bc3664132e539337080,0x3ecf92a19061ce29a9ef3dc00,(more! 0x973c1b58d0dd44d8bd385c40,0x96da0cdb8c48da6fd8a9cf80,(more! 0x76bd781af31e57f38812aa0,0x7545f2a18b6bccfbd008360,(last! 0,0))))
private theorem r16 : BlockChecks (S 219723) N P 2405 16 234 :=
  block! 2691,16,0x48b2569bf0e4aafcb1ba15500,0x48b258b2ad716d5d460528600,(more! 0x3edcce67bce1547c1e57dbde0,0x3ee47febf1456eedd046ae900,(more! 0x96aed8f3fe36a5f194ad9a80,0x964bcf333fa0ccb75a52dc00,(last! 0x6a9cede99e3e5e6df33c660,0x69357cd40ec2ecc02db3b00)))
private theorem r17 : BlockChecks (S 219723) N P 2405 17 213 :=
  block! 2655,14,0x48b2569bf0e4aafcb1ba15500,0x48b258b2ad716d5d460528600,(more! 0x3ef19e67abf4a9bcdec26de00,0x3ef94f6175533f82ee3fc8680,(more! 0x961f58fa32dda1c4f0ba6740,0x95bb4d5ab4954819cc7d23c0,(last! 0x5ecd22955a5360d2bed2400,0x5d765a8802c2cf5af499da0)))
private theorem r18 : BlockChecks (S 219723) N P 2405 18 189 :=
  block! 2623,13,0x48b2569bf0e4aafcb1ba15500,0x48b258b2ad716d5d460528600,(more! 0x3f03fd9453cc961bb8a9a4700,0x3f0bae1fff67cc071a2979680,(more! 0x95a5d7d60a3b30bb129272a0,0x9540d78e395cedf36741ca60,(last! 0x54039b21f00bd13edc757e0,0x52bc8b4842625f120d9c300)))
private theorem r19 : BlockChecks (S 219723) N P 2405 19 163 :=
  block! 2595,12,0x48b2569bf0e4aafcb1ba15500,0x48b258b2ad716d5d460528600,(more! 0x3f15352bf735fce4c29247720,0x3f1ce5468db2e398596c09ec0,(more! 0x9534535a1d19810f55578ee0,0x94ce5c39992b8677a75fcb80,(last! 0x49e3b3113f723ca05cf4a60,0x48ac81a01a12304eca5adc0)))
private theorem r20 : BlockChecks (S 219723) N P 2405 20 135 :=
  block! 2569,11,0x48b2569bf0e4aafcb1ba15500,0x48b258b2ad716d5d460528600,(more! 0x3f2553420123ce42277948ba0,0x3f2d02eb0fb2d35f3824613e0,(more! 0x94c9bdfd6d1d896501c65360,0x9462caf2d3b064d3397948c0,(last! 0x406f94619baab53a1415460,0x3f48930803dca138f3fec60)))
private theorem r21 : BlockChecks (S 219723) N P 2405 21 105 :=
  block! 2546,10,0x48b2569bf0e4aafcb1ba15500,0x48b258b2ad716d5d460528600,(more! 0x3f3467024605630b9ca7f8e00,0x3f3c163b492178466cd69ea00,(more! 0x94650cd820ae7fa68fa33c80,0x93fd165812851b2b97b307c0,(last! 0x37a838502dcfc5c64cbd400,0x3691de5eb552586d903cba0)))
private theorem r22 : BlockChecks (S 219723) N P 2405 22 72 :=
  block! 2524,9,0x48b2569bf0e4aafcb1ba15500,0x48b258b2ad716d5d460528600,(more! 0x3f41b872a4343031b04ef5ac0,0x3f4967555b22724a939677c00,(more! 0x940f48bee4e3d5e695c8c380,0x93a64c530c67c76e7ef3a780,(last! 0x2fab68ef060eb1508b61600,0x2ea5c317432f4d7389ca240)))
private theorem r23 : BlockChecks (S 219723) N P 2405 23 38 :=
  block! 2505,9,0x48b2569bf0e4aafcb1ba15500,0x48b258b2ad716d5d460528600,(more! 0x3f4ef330c39b08836f965fee0,0x3f56a1a912cce5faab652d6c0,(more! 0x93b2f116be11ae509bca3e20,0x9348dbc5e8a9c212061334a0,(last! 0x28380f1fab20fada3b268c0,0x2744621b16cc2f69539eb80)))
private theorem r24 : BlockChecks (S 219723) N P 2405 24 2 :=
  block! 2487,8,0x48b2569bf0e4aafcb1ba15500,0x48b258b2ad716d5d460528600,(more! 0x3f5b509c9f1b719848f47bfa0,0x3f62feaf61da595d3ba1a8460,(more! 0x93598ebd4bea1ace81ca2fe0,0x92ee548ad17b8cb8066b3b60,(last! 0x21723d0207c7a44931847e0,0x209143b588999ef282cf7c0)))

theorem none : BlockChecks (terminal .h2405).shape (terminal .h2405).nodeRows
    (terminal .h2405).poleMoment (start .h2405) (threshold .h2405 Option.none) 0 := r0

theorem all : GradeChecks (terminal .h2405) (start .h2405) 1 (grades .h2405) :=
  ⟨r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,trivial⟩
end h2405

private theorem checks (b : Band) (x : Test b) :
    let t := tested b x
    BlockChecks t.shape t.nodeRows t.poleMoment (start b) (threshold b x) (seedThreshold b x) := by
  have hn : BlockChecks (terminal b).shape (terminal b).nodeRows (terminal b).poleMoment
      (start b) (threshold b Option.none) 0 := by
    cases b <;> first | exact h2405.none
  have hc : GradeChecks (terminal b) (start b) 1 (grades b) := by
    cases b <;> first | exact h2405.all
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
end HighCore82219Terminal
