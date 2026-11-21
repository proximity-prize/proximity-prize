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

namespace h2395
local notation "S" u => (⟨7550,10506,2218,u⟩ : Shape)
local notation "N" => 0x2cfea55aa80000
local notation "P" => 0x129e297a45c0c
private theorem r0 : BlockChecks (S 229924) N P 2415 24 0 :=
  block! 2656,1,0x617564f0c5b5fae48961bcd00,0x617567cf9a83798f404545000,(more! 0x4dffc69cdc75ff384c5182a40,0x4e13d3cff80219263edbe3c20,(more! 0xfcaaa7e4b84f0f40ff155f00,0xfbf2dad9aa5d323aea2d2fa0,(more! 0x3ab99ad6f9e1b1d56a6aa1c0,0x3a32b7c2c265ee632481d820,(last! 0x0,0x0))))
private theorem r1 : BlockChecks (S 179010) N P 2415 1 366 :=
  block! 2708,2,0x3b1801087cc8b9fa460f0db00,0x3b180344997c824a308923000,(more! 0x2e7488a8ffaa11237f39e0860,0x2e809fde689bfed914cdbedc0,(more! 0x98737fdb4a2ce64eae867ec0,0x98062f27070e5a9a44c0ea20,(more! 0x31b4dc5a2862f65391d58440,0x3162e7061ebb0bbe1219a780,(last! 0xf29c3d97cb97565464560,0xe4f981f3d7acb31557ac0))))
private theorem r2 : BlockChecks (S 185266) N P 2415 2 360 :=
  block! 2733,3,0x3f4b16be3734f6e136924cb00,0x3f4b190e525af24c81a793000,(more! 0x31ac124ed3ef08ad09ad9e200,0x31b909de54df78edd5a185a40,(more! 0xa382f43963abae0ac2095040,0xa30daf6354abcdd8817c0c40,(more! 0x3642b47dc50d818c6f966e00,0x35eb8cf1c5d998655e026200,(last! 0x2a9e415718c4cdfc3fd8c0,0x28fb9df173276a86701f40))))
private theorem r3 : BlockChecks (S 183202) N P 2415 3 355 :=
  block! 2735,3,0x3de4507e04b1abd3400f43b00,0x3de452c78725dd180c5583000,(more! 0x30ada733020a82e7e47e55180,0x30ba53b79c618ee603c914880,(more! 0x9fce557ee6a182897277bac0,0x9f5b7f3f9c7d3fbc31b9cc00,(more! 0x3375c06d599c4813e0b3cfa0,0x3320a694ae9885174a25c300,(last! 0x267ecd27e20f76f62a1ea0,0x2508f1388fea5c4564ffa0))))
private theorem r4 : BlockChecks (S 186942) N P 2415 4 349 :=
  block! 2754,4,0x40715fce798a0163ebe8db700,0x40716223efeefdbbde759f000,(more! 0x32ab7fa5acecff45e633b6f20,0x32b8b4692c54302013b5af440,(more! 0xa6852e7c6088aa1a51521f40,0xa60d6d84909b9775627f8280,(more! 0x359a54dbbb8b335b2a13d3a0,0x354228cbf4ea1ce263311f20,(last! 0x3e7f37e1bd8288ec122140,0x3c903515847bfc2b28caa0))))
private theorem r5 : BlockChecks (S 189067) N P 2415 5 343 :=
  block! 2770,5,0x41ea4e70e44ce280c8124ec00,0x41ea50cd254c23af3eea0c000,(more! 0x33da9bda68d9fa63ee62ff3e0,0x33e81f34325ebd3f5c1254f40,(more! 0xaa63f9f04a1a4477eb2cac40,0xa9e94dab1cab7d103d57aca0,(more! 0x36470ef9a422130da9dda3e0,0x35ed2c979fdab4f809e26fe0,(last! 0x502082241afd346e66d240,0x4df1b566f98da2fc9a13c0))))
private theorem r6 : BlockChecks (S 188960) N P 2415 6 337 :=
  block! 2779,5,0x41d73997df934240c4381a900,0x41d73bf3c9074fe68992c1000,(more! 0x33de65025fa415a55a08e9c60,0x33ebe43841da86b5fcbaf4640,(more! 0xaa2e50f76bdff059aa4bf9e0,0xa9b39bcac51e9e2200c5cf20,(more! 0x350be44ba8c5a8df9c2617a0,0x34b23fac8f654b8867947ac0,(last! 0x531415363652a0c7b3f4e0,0x50f242c833507575513940))))
private theorem r7 : BlockChecks (S 194045) N P 2415 7 330 :=
  block! 2807,6,0x456df8e9b5d270a2a5328ee00,0x456dfb55dfa62e73e82cbe000,(more! 0x36ad203c959d9242cd6f91e80,0x36bb5f36e03e00455e1f04ce0,(more! 0xb3a1938f6f3c1d93aeec5300,0xb31ffacc63aa5d3c690d3800,(more! 0x37f4f3746ae2d84f5867b940,0x3796c1cc67d6cf8692a58b00,(last! 0x7703cf4ec1573952ca8a40,0x7469c5b696745ee2df98e0))))
private theorem r8 : BlockChecks (S 195714) N P 2415 8 323 :=
  block! 2824,7,0x46a0d6824b1000d47115c1b00,0x46a0d8f3ca68984ffe9263000,(more! 0x37ac4eae1dea47dd0f48207a0,0x37bacd966c6014cc83b4c4680,(more! 0xb6c6e2dcad463e55a2b23e20,0xb642dd3cb4fe1f97e6e25fe0,(more! 0x3800e1824c9695694cee2260,0x37a12a0c92944f0f92e56740,(last! 0x80b8e9a718ffef098d12c0,0x7e1925afa80d071898a1c0))))
private theorem r9 : BlockChecks (S 201989) N P 2415 9 315 :=
  block! 2860,8,0x4b3a1259573b85499d7b43600,0x4b3a14dee491df026350c6000,(more! 0x3b47d336bf9a3fc2b7efd3aa0,0x3b5747f61a8821e17aa9ac040,(more! 0xc2e40ff5d579d0e0d7ef9ae0,0xc257396ebd74e3ab6c0966a0,(more! 0x3b9945c5a2449b288040aaa0,0x3b33814d939197b85092e5c0,(last! 0xa69c714d9412760ede2c40,0xa39600f638c6db293f61c0))))
private theorem r10 : BlockChecks (S 201870) N P 2415 10 307 :=
  block! 2876,9,0x4b2366ae380058414ed228700,0x4b23693363fa1691e861ef000,(more! 0x3b4ee8cc137ed009eb8f282a0,0x3b5e588d5e12c7eaf7994e6e0,(more! 0xc2a2e69de09e63f5c3fc09a0,0xc2160c07dd31a33529d63740,(more! 0x3a0ec6be5898a414a0d95ae0,0x39a906dcf30de34f2875e3c0,(last! 0x9630d01bd2a5afbb902f40,0x93793c1129883a77da0940))))
private theorem r11 : BlockChecks (S 210653) N P 2415 11 297 :=
  block! 2928,11,0x51d084146f46a88c6ec20ce00,0x51d086b5ad33f68d7e799e000,(more! 0x408c3399905b01001dd269b60,0x409d086fc709a8378ddabc3e0,(more! 0xd43ae9cb97bcd04a1d63c300,0xd3a14cd3832f2a0bd1a90160,(more! 0x3f5626b0e17bc8f7d6047a20,0x3ee757ca6ac7906e1107ef60,(last! 0xb3f737f76c69c55d8a3620,0xb0e3bff1130629bf2ba820))))
private theorem r12 : BlockChecks (S 223669) N P 2415 12 285 :=
  block! 3003,14,0x5c3b1b113da2813cc67a66600,0x5c3b1ddc14cf401ebc5376000,(more! 0x48b3e8793ca78fc043e3b98c0,0x48c6eae545bd27e35d329c5e0,(more! 0xefb39d86dc6f0e2d54f43a00,0xef062644529f5f8d7f8db4e0,(more! 0x47f084806a8da564a0b502e0,0x477368fb655d6577b796f5c0,(last! 0xcf077a1c17ca13a59178c0,0xcb7999c6fb601775b97b00))))
private theorem r13 : BlockChecks (S 229924) N P 2415 13 271 :=
  block! 3027,14,0x617564f0c5b5fae48961bcd00,0x617567cf9a83798f404545000,(more! 0x4ce15ac49df20728e30c4b4e0,0x4cf574c8e3966ba9153ba7da0,(more! 0xfd7678383cebfdd2f2855820,0xfcbef008e6785f155d200cc0,(more! 0x4b1e7de08549f49ffcf5e100,0x4a99d41aa7ac5bfdc2893a80,(last! 0xabacb4f6fd47df1705b460,0xa8608bcfdc99fda7978d00))))
private theorem r14 : BlockChecks (S 228680) N P 2415 14 256 :=
  block! 2969,12,0x60684ba8e4b621133523a1100,0x60684e83bfb73a3e88c6e9000,(more! 0x4c3316bb65d878ed956c045e0,0x4c46f7b24eba61c60c42aaf20,(more! 0xfaa186471217b2413b9ffca0,0xf9ebd2b8ff88c773cc66d4e0,(more! 0x4845d281b2ecf30ff7da4e00,0x47c2115fbe9e56c014cfd200,(last! 0x6bf614e165d56e8757eb60,0x6977d0e8cd2f0089e086e0))))
private theorem r15 : BlockChecks (S 228103) N P 2415 15 239 :=
  block! 2919,10,0x5febf9cd0b3e428bea8c74800,0x5febfca60e2a6e7d990008000,(more! 0x4bf2293df1e75013cde083dc0,0x4c05ef64acc63948935ee9d40,(more! 0xf94a54681d625351e64c7460,0xf8956b1ec971c78a5b800d80,(more! 0x4616840541ea619e20596aa0,0x4592e82d2ad068a379ae0e20,(last! 0x3c30a08ae3f5e1626171e0,0x3a6d2f0e38bcac226edcc0))))
private theorem r16 : BlockChecks (S 229092) N P 2415 16 219 :=
  block! 2875,9,0x60c141b634c4935308ade8d00,0x60c1449260db4577293a05000,(more! 0x4cb5a39be2d765125f440cbe0,0x4cc995845e52a2dbc5692d440,(more! 0xfb6d8c16c62749a79e63f5e0,0xfab6f60a90ef36919580b980,(more! 0x4530465e475b667553244460,0x44aafc607b2ca0623f767880,(last! 0x1c0f4fc95e2159aabd16a0,0x1aef1deaeb05651d482c60))))
private theorem r17 : BlockChecks (S 229493) N P 2415 17 197 :=
  block! 2837,7,0x6117ff1049426b3ab76532600,0x611801edbd6ec1cac9a236000,(more! 0x4d14d9413db55015570423700,0x4d28dc66d72bb59d08ca0b7c0,(more! 0xfc42955a9f963aea63d8fa20,0xfb8b4958bbb606662b675600,(more! 0x43e70912e44f87f55997dfa0,0x4360cf7426c38437626d3ae0,(last! 0x8bebd8bd29fcc77ad5a40,0x8321cae59e3359b562b20))))
private theorem r18 : BlockChecks (S 229615) N P 2415 18 173 :=
  block! 2802,6,0x61326a81cc4953669da207000,0x61326d5fa4469f56bad6f0000,(more! 0x4d43251c8b4508dedfdf61460,0x4d572cdd12c54052c898fb200,(more! 0xfc78a1fd7955c5831eb07660,0xfbc11944c4b1125c3d5ffae0,(more! 0x427ab5d9b63c3c46dc6a90c0,0x41f405b4e2fa86266cad6b00,(last! 0xfeb2825e380b1062c9c0,0xdc28af9ea4ff219581c0))))
private theorem r19 : BlockChecks (S 229607) N P 2415 19 147 :=
  block! 2771,5,0x6130aee4791a57d7d982c2800,0x6130b1c24a8c0932fa31e8000,(more! 0x4d59a2f3d6c307380852f2140,0x4d6da96c6acb4a3304f346a60,(more! 0xfc64cf528194485f45dbca00,0xfbad45f9d5525c793eaede20,(more! 0x410befb7fb6026f11cb59440,0x4085321aeddc1a6be6994640,(last! 0x0,0x0))))
private theorem r20 : BlockChecks (S 229548) N P 2415 20 119 :=
  block! 2744,4,0x6123e7b654cbf11da62429500,0x6123ea93f5f80e6e0078cd000,(more! 0x4d65cd9c46fa13f4dfa7559e0,0x4d79d0808cba3152e4a7e8980,(more! 0xfc345be179b850ab635e9980,0xfb7ced5e0596ebb7896fb340,(more! 0x3fad4601864196ad4fbf8c60,0x3f26a68bc6261cf30d26d3a0,(last! 0x0,0x0))))
private theorem r21 : BlockChecks (S 229477) N P 2415 21 89 :=
  block! 2719,3,0x6114885234e4bed9cd26a9600,0x61148b2f9bf9e03fe65826000,(more! 0x4d6e64af93fb5c2a47184f980,0x4d8263798e22ca2ecf1592e60,(more! 0xfbfda5581339e31d2f325cc0,0xfb465ce8ca9c644a172d6900,(more! 0x3e6494e6f5add1a915972aa0,0x3dde10abc9a056cc60712a80,(last! 0x0,0x0))))
private theorem r22 : BlockChecks (S 229895) N P 2415 22 56 :=
  block! 2696,2,0x616f1abf93bb8ea7c5e864800,0x616f1d9e50cefcf6696708000,(more! 0x4dc8dd126141a49679bbc7100,0x4ddcede74cf178cb565987280,(more! 0xfcde779151fc7b54bd0bca00,0xfc269424ae5dc0c4eedcc600,(more! 0x3d8563abdd7043a9311b5380,0x3cfe5ba1d5a3ee9a483a6000,(last! 0x0,0x0))))
private theorem r23 : BlockChecks (S 229805) N P 2415 23 22 :=
  block! 2675,1,0x615b96e48cfebea52d28a1e00,0x615b99c3006fa1e7b7c66e000,(more! 0x4dcb9e1a5a5bc2f3967893100,0x4ddfaa026ab42941979b1a7c0,(more! 0xfc9dfff3fd3da25090d5ad20,0xfbe656bc000137953672a7a0,(more! 0x3c618cf0cad350c1fea7eca0,0x3bda991449f1f696f0b3b1e0,(last! 0x0,0x0))))
theorem none : BlockChecks (terminal .h2395).shape (terminal .h2395).nodeRows
    (terminal .h2395).poleMoment (start .h2395) (threshold .h2395 Option.none) 0 := r0
theorem all : GradeChecks (terminal .h2395) (start .h2395) 1 (grades .h2395) :=
  ⟨r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,trivial⟩
end h2395

namespace h7773
local notation "S" u => (⟨124,173,32,u⟩ : Shape)
local notation "N" => 0xc4fd80000
local notation "P" => 0x15c66e5
private theorem r0 : BlockChecks (S 949) N P 7773 7 0 :=
  block! 57,1,0x1e4180371c3222780,0x1e4183c42dcc77500,(last! 0x1e427c872cfb652c0,0x1e42849141783b3a0)
private theorem r1 : BlockChecks (S 729) N P 7773 1 27 :=
  block! 60,1,0x11f21be595b8b6c80,0x11f21ea021e68c300,(last! 0x11f222b29e12fe680,0x11f2280f274d47360)
private theorem r2 : BlockChecks (S 773) N P 7773 2 25 :=
  block! 63,1,0x1426eb99c90432b80,0x1426ee7e6fe154d00,(last! 0x1426f08d3d16885c0,0x1426f6676d817b2a0)
private theorem r3 : BlockChecks (S 800) N P 7773 3 23 :=
  block! 67,2,0x1591b71928dbf8f40,0x1591ba17a5ea7e780,(last! 0x1591bd14ead85f820,0x1591c33eb34edb4c0)
private theorem r4 : BlockChecks (S 949) N P 7773 4 19 :=
  block! 76,3,0x1e4180371c3222780,0x1e4183c42dcc77500,(last! 0x1e4180e8960fca4e0,0x1e4188ea265028ca0)
private theorem r5 : BlockChecks (S 916) N P 7773 5 15 :=
  block! 67,2,0x1c349f7e491185840,0x1c34a2ebc6a860d80,(last! 0x1c34a9dcf28967540,0x1c34b171a61e0c8e0)
private theorem r6 : BlockChecks (S 943) N P 7773 6 8 :=
  block! 61,1,0x1de0b2f031994bc00,0x1de0b67785618a800,(last! 0x1de0c13722a04d800,0x1de0c925474400f00)
theorem none : BlockChecks (terminal .h7773).shape (terminal .h7773).nodeRows
    (terminal .h7773).poleMoment (start .h7773) (threshold .h7773 Option.none) 0 := r0
theorem all : GradeChecks (terminal .h7773) (start .h7773) 1 (grades .h7773) :=
  ⟨r1,r2,r3,r4,r5,r6,trivial⟩
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
