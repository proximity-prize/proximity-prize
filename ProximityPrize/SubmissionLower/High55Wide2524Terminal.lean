import ProximityPrize.SubmissionLower.HighCore82268TerminalArithmetic
import ProximityPrize.SubmissionLower.High55Wide2524Data

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace High55Wide2524Terminal

open High55Wide2524
open HighCore82268TerminalArithmetic
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

namespace h2524
local notation "S" => (⟨7351,10225,2160,229893⟩ : Shape)
local notation "N" => 0x29898d6f900000
local notation "P" => 0x10b67db5c846d
private theorem r0 : BlockChecks S N P 2524 25 0 :=
  block! 2570,9,0x59f27b4849bd82e634d025a00,0x59f27ddbd7c58333a19619780,(more! 0x4ef2afe4edd69670778c75e40,0x4efbcc212ce13fb5f0e6eba60,(more! 0xac20ae056bc351f854dc5c00,0xaba797fe5538c9c375935920,(last! 0x3ed012a06299c03effaab60,0x3d64e993fa3bb3d6f04aa80)))
private theorem r1 : BlockChecks S N P 2524 1 399 :=
  block! 2737,16,0x59f27b4849bd82e634d025a00,0x59f27ddbd7c58333a19619780,(more! 0x4c5745eebaf381298f85f5000,0x4c606d9ac861b440888fddcc0,(more! 0xbd7f4a95e8aec79300ada740,0xbd28859344eb42e78c85dd20,(last! 0x1c3431207e489a933db54180,0x1bfa7518132ad6b287216aa0)))
private theorem r2 : BlockChecks S N P 2524 2 393 :=
  block! 2745,16,0x59f27b4849bd82e634d025a00,0x59f27ddbd7c58333a19619780,(more! 0x4c78c0d7a00443a6d8f159c20,0x4c81e83065d93eee13e62efc0,(more! 0xbc737394a329f17e04868ac0,0xbc1ad091a588edcf319a2940,(last! 0x1b293b9fbd8547ed1f636ee0,0x1af162e1bf934cf6a13ef0c0)))
private theorem r3 : BlockChecks S N P 2524 3 386 :=
  block! 2756,16,0x59f27b4849bd82e634d025a00,0x59f27ddbd7c58333a19619780,(more! 0x4c9772aba452f947318613460,0x4ca099ded9fa312b11783f820,(more! 0xbb7aa71db4a97e8946b65ba0,0xbb2043dcb1283491290aaae0,(last! 0x1a36b0306b3bf6fa87175560,0x1a009a01e7c8a9dae81baac0)))
private theorem r4 : BlockChecks S N P 2524 4 379 :=
  block! 2767,1,0x59f27b4849bd82e634d025a00,0x59f27ddbd7c58333a19619780,(more! 0x4cb79343532aff72b42dadf00,0x4cc0ba3e14acabe4537211e00,(more! 0xba7f431ddb831e14731f1f40,0xba231bdf93c0b32d5ec2fb20,(more! 0x193023fd77446230a0e43820,0x18fbd96fbff312f7314df2a0,(last! 0xf2c22bd6757f9358580,0xb124adcb02b5d8f3a40))))
private theorem r5 : BlockChecks S N P 2524 5 371 :=
  block! 2780,1,0x59f27b4849bd82e634d025a00,0x59f27ddbd7c58333a19619780,(more! 0x4cd58deec44f5fb2e774386a0,0x4cdeb4d995aa1c24d9d4c9020,(more! 0xb9950b2a18bba34a47f0d560,0xb937395e763685c3ca8ab4e0,(more! 0x183958976719a39e4cf4ccc0,0x1806c6fd1da39c0e3d0aa060,(last! 0x8c473827802c0eb273a0,0x7aae0ae2d55878de2260))))
private theorem r6 : BlockChecks S N P 2524 6 364 :=
  block! 2792,2,0x59f27b4849bd82e634d025a00,0x59f27ddbd7c58333a19619780,(more! 0x4cf8aa04446b26ff1531e30c0,0x4d01d089caae5c0bc705b2f60,(more! 0xb893b2518253d4efe3b650c0,0xb8341580c32b537ef5ddebc0,(more! 0x170928fd93ff4989b21480c0,0x16d875f25b9e465151fd0220,(last! 0x168c3335a7328630bb4e0,0x14a0f0fb37a94637a71c0))))
private theorem r7 : BlockChecks S N P 2524 7 356 :=
  block! 2806,2,0x59f27b4849bd82e634d025a00,0x59f27ddbd7c58333a19619780,(more! 0x4d19ea607147d60a4143d1f40,0x4d2310a2b85366002c051f1a0,(more! 0xb7a25431a39ccbaa24d88820,0xb741046b6d429c9cafa144a0,(more! 0x15e55e64b66fa36feb25b1a0,0x15b66fb6399b9cf2507b75e0,(last! 0x2bf2e0300e4249f94a5c0,0x2934993eabd4e88b2cb80))))
private theorem r8 : BlockChecks S N P 2524 8 347 :=
  block! 2823,3,0x59f27b4849bd82e634d025a00,0x59f27ddbd7c58333a19619780,(more! 0x4d39cffb84e4193943046af40,0x4d42f616c17c2f43d8e0461c0,(more! 0xb6bf579dd76c4f4adecaea40,0xb65c69c184bf0e0b060f7a20,(more! 0x14c7d94ba810b68f34298d60,0x149a9518c67b1b64553cd700,(last! 0x4558e17e4f4c0b4fa6920,0x41fa36fda56d19ae52080))))
private theorem r9 : BlockChecks S N P 2524 9 338 :=
  block! 2841,4,0x59f27b4849bd82e634d025a00,0x59f27ddbd7c58333a19619780,(more! 0x4d5ba89deb10cc5923932c2a0,0x4d64ce6c93a9513b2d9f11b60,(more! 0xb5d6ef8339d7f1c579ecbf20,0xb5725deef0cd3516c41d5400,(more! 0x1391fd49c54a2aeaf41dece0,0x136662e44a368c48a2fb14a0,(last! 0x545220cdb28f09b25c200,0x50deddf5a159531d094c0))))
private theorem r10 : BlockChecks S N P 2524 10 328 :=
  block! 2861,5,0x59f27b4849bd82e634d025a00,0x59f27ddbd7c58333a19619780,(more! 0x4d7cb9392d20dfba88a33c980,0x4d85dec891eb3625176c079a0,(more! 0xb4fa2ae8afc5421c8277c900,0xb49407067c0294331326dfe0,(more! 0x125d8667b3a85f375446d9e0,0x12337c2615885948bfa28500,(last! 0x5359b9390bcc70c3552c0,0x5047bc814855c9f4b13a0))))
private theorem r11 : BlockChecks S N P 2524 11 317 :=
  block! 2886,6,0x59f27b4849bd82e634d025a00,0x59f27ddbd7c58333a19619780,(more! 0x4d9d6b43f824ab47eaea3c620,0x4da69094d4edeba627838eb20,(more! 0xb426cae3139167606daa2e00,0xb3bf23575f19cde4aa2dbd60,(more! 0x1126d5fb1178cd14691f44a0,0x10fe45b5f0e99eb3034943c0,(last! 0x3af3ebf4d23bb0c0911c0,0x38ba497e010b916babcc0))))
private theorem r12 : BlockChecks S N P 2524 12 305 :=
  block! 2914,7,0x59f27b4849bd82e634d025a00,0x59f27ddbd7c58333a19619780,(more! 0x4dbe0a87f8fc5b44717b5c380,0x4dc72f8976b0ba533822acc80,(more! 0xb35a0d3a84039b9b5288c140,0xb2f0ee0db4f68c31bfaba360,(more! 0xfebb09fd944a0cc56c7e840,0xfc48aa6b4ef0e0a8e4fdbc0,(last! 0x150649af26ea3fd506920,0x13f090fe3e3bcf8318b40))))
private theorem r13 : BlockChecks S N P 2524 13 292 :=
  block! 2947,8,0x59f27b4849bd82e634d025a00,0x59f27ddbd7c58333a19619780,(more! 0x4ddea65fa23a3f5bbf9fc3060,0x4de7cae9f550cf060ba238c80,(more! 0xb290dc196b74a44d4141c660,0xb2264f34660302cfd4213060,(more! 0xeacb3a95143fcfd2f323c60,0xe86f3a86bf4114315d00700,(last! 0xe8bc6cb5cefed8be000,0xc65cca317f7ce9d5700))))
private theorem r14 : BlockChecks S N P 2524 14 277 :=
  block! 2891,6,0x59f27b4849bd82e634d025a00,0x59f27ddbd7c58333a19619780,(more! 0x4dfd333a06f45edd46615a680,0x4e065748088bdddde75296fa0,(more! 0xb1d8d65570c8c9497f26c960,0xb16cf5e64965524a03db3320,(more! 0xd7c09d3ce5d4a50ba5c8fe0,0xd57a2f8c984790c9045d1c0,(last! 0,0))))
private theorem r15 : BlockChecks S N P 2524 15 260 :=
  block! 2842,4,0x59f27b4849bd82e634d025a00,0x59f27ddbd7c58333a19619780,(more! 0x4e19d96458ea11c2263b19e60,0x4e22fceb7dc3470ec91335760,(more! 0xb130089e1bb7373a48825cc0,0xb0c2ea0f22505971977f7460,(more! 0xc5a8bb11a0c73e38027bfe0,0xc376b616ebe657317a0c9e0,(last! 0,0))))
private theorem r16 : BlockChecks S N P 2524 16 241 :=
  block! 2800,2,0x59f27b4849bd82e634d025a00,0x59f27ddbd7c58333a19619780,(more! 0x4e34b0b305dc50e42687c1380,0x4e3dd3a9d761bf8a96c6ebfc0,(more! 0xb0951ee29fe13ef40b4e28a0,0xb026d30051b48ecab4dde280,(more! 0xb4835bb7da06776d8ab4640,0xb264bc5ad1ce78707d94540,(last! 0,0))))
private theorem r17 : BlockChecks S N P 2524 17 219 :=
  block! 2762,1,0x59f27b4849bd82e634d025a00,0x59f27ddbd7c58333a19619780,(more! 0x4e4c68bf68481302b91f06b60,0x4e558b44dfdfcfd0d1e42c580,(more! 0xb01464818bdff0ebe606d220,0xafa506bb32da5e7d478a6a00,(more! 0xa4cc8763c2590bc534672a0,0xa2bf76537f9d9d0bb53da20,(last! 0,0))))
private theorem r18 : BlockChecks S N P 2524 18 196 :=
  block! 2729,15,0x59f27b4849bd82e634d025a00,0x59f27ddbd7c58333a19619780,(more! 0x4e63fd110b3b520ca88bc3fc0,0x4e6d1efa473945f80a37c7360,(more! 0xaf9180504cba67a5786ac900,0xaf2108fb819ef8992efc8540,(last! 0x956e6039ee61d824e5a2e60,0x937384e7b8aa67a97011f00)))
private theorem r19 : BlockChecks S N P 2524 19 170 :=
  block! 2699,14,0x59f27b4849bd82e634d025a00,0x59f27ddbd7c58333a19619780,(more! 0x4e78cfa9c96c18bb1a43943c0,0x4e81f11770dc3f7f9676c4760,(more! 0xaf25c4b5825fbdb31daac3e0,0xaeb4457f4cddebd3986f70c0,(last! 0x87525f6d01e7ca0db5efd40,0x85687d100006222a670dcc0)))
private theorem r20 : BlockChecks S N P 2524 20 143 :=
  block! 2672,13,0x59f27b4849bd82e634d025a00,0x59f27ddbd7c58333a19619780,(more! 0x4e8d6eef6e9aee11b05cefb00,0x4e968fc18d7d3fca44ae86860,(more! 0xaeb6e9901aa92c4c8cbb3f20,0xae445512394c2d68692a4980,(last! 0x79aad4391020effc4606be0,0x77d2e2bd894922fdf402d00)))
private theorem r21 : BlockChecks S N P 2524 21 113 :=
  block! 2647,12,0x59f27b4849bd82e634d025a00,0x59f27ddbd7c58333a19619780,(more! 0x4e9fa3a1b943c87a7ee9d83c0,0x4ea8c3f956828fa3caea53cc0,(more! 0xae5c4894648a44693d6a04c0,0xade8a7d55dcaaf6deb09b100,(last! 0x6d1d8a651e4a5ae9871e7e0,0x6b56d71292465ddcd5ef300)))
private theorem r22 : BlockChecks S N P 2524 22 81 :=
  block! 2625,11,0x59f27b4849bd82e634d025a00,0x59f27ddbd7c58333a19619780,(more! 0x4eb0af350e21486817a3c2fa0,0x4eb9cf14956fa2ccf9802c9e0,(more! 0xae0884cbb9b8c8647a6cbee0,0xad93d07cc4fc5c346d16f8c0,(last! 0x614c3e4657f314368441ea0,0x5f973bb3f7fc65e50551740)))
private theorem r23 : BlockChecks S N P 2524 23 47 :=
  block! 2605,10,0x59f27b4849bd82e634d025a00,0x59f27ddbd7c58333a19619780,(more! 0x4ec0a327d32610e38ba102180,0x4ec9c29311e5dc0f366970bc0,(more! 0xadbaa5f9a15d6bf338f24880,0xad44d4102a89f690054ae540,(last! 0x5634738b6b5599efb2edb80,0x5491be9d81dae6b3a7edd60)))
private theorem r24 : BlockChecks S N P 2524 24 11 :=
  block! 2587,10,0x59f27b4849bd82e634d025a00,0x59f27ddbd7c58333a19619780,(more! 0x4ecf90b9042b0e0ec06f50f80,0x4ed8afb4cbb87b66774087ec0,(more! 0xad71b62854c348c74cbe0740,0xacfaba34ecc55b87c94403e0,(last! 0x4bd3e1fc0d3e995215da800,0x4a443cd4caa35dc948663a0)))

theorem none : BlockChecks (terminal .h2524).shape (terminal .h2524).nodeRows
    (terminal .h2524).poleMoment (start .h2524) (threshold .h2524 Option.none) 0 := r0

theorem all : GradeChecks (terminal .h2524) (start .h2524) 1 (grades .h2524) :=
  ⟨r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,trivial⟩
end h2524

private theorem checks (b : Band) (x : Test b) :
    let t := tested b x
    BlockChecks t.shape t.nodeRows t.poleMoment (start b) (threshold b x) (seedThreshold b x) := by
  have hn : BlockChecks (terminal b).shape (terminal b).nodeRows (terminal b).poleMoment
      (start b) (threshold b Option.none) 0 := by
    cases b <;> first | exact h2524.none
  have hc : GradeChecks (terminal b) (start b) 1 (grades b) := by
    cases b <;> first | exact h2524.all
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
end High55Wide2524Terminal
