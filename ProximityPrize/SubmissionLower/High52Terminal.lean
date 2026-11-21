import ProximityPrize.SubmissionLower.High52TerminalArithmetic
import ProximityPrize.SubmissionLower.High52Data

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace High52Terminal

open High52
open High52TerminalArithmetic
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

namespace h2452
local notation "S" => (⟨7159,9956,2106,226349⟩ : Shape)
local notation "N" => 0x2666b9ec700000
local notation "P" => 0xf09d7e37e19f
private theorem r0 : BlockChecks S N P 2452 25 0 :=
  block! 2505,7,0x509bcfd254848f943898a1200,0x509bd21aa84eba0c559e7fc80,(more! 0x4719b4b7d1302dbc71c923520,0x47220dbb2245654a5d782b100,(more! 0x96c5f2e6bc2c62e18c0b6a40,0x964d9da3783829a8dbd7bc60,(last! 0x16f909dd8b1d249348137a0,0x1641bcf9b9111163de5cfe0)))
private theorem r1 : BlockChecks S N P 2452 1 400 :=
  block! 2672,14,0x509bcfd254848f943898a1200,0x509bd21aa84eba0c559e7fc80,(more! 0x44b78f781c6c9a69fe3d93cc0,0x44bff3e0e6db339be8df49ec0,(more! 0xaaca70e53323c17be70cf8e0,0xaa7212d599cc782e69f5e620,(last! 0x137a4a1e2da2f845daf74160,0x134e25fc8417c004dacb6f60)))
private theorem r2 : BlockChecks S N P 2452 2 393 :=
  block! 2682,14,0x509bcfd254848f943898a1200,0x509bd21aa84eba0c559e7fc80,(more! 0x44d2a44644f924962871a0ac0,0x44db0896da2cd605c36b5c5a0,(more! 0xa9b6b136765b2581a3e6f960,0xa95ccf4fd5ce8e7e43b3a460,(last! 0x12dc54fc813d98b92583b280,0x12b1b628f795627f1d401440)))
private theorem r3 : BlockChecks S N P 2452 3 386 :=
  block! 2693,15,0x509bcfd254848f943898a1200,0x509bd21aa84eba0c559e7fc80,(more! 0x44ef06a3827d91cd84679f280,0x44f76acba260bb8731d9ed6c0,(more! 0xa89fff7fe7116a38dba1b8c0,0xa84493cb08368e77c373db20,(last! 0x122cc908a368a253cfc69c60,0x1203b686c0299028b12b2e00)))
private theorem r4 : BlockChecks S N P 2452 4 379 :=
  block! 2704,15,0x509bcfd254848f943898a1200,0x509bd21aa84eba0c559e7fc80,(more! 0x450cb4f43a873576bdbc40be0,0x451518e1ec200d3053e778da0,(more! 0xa7865bebb148d16a49174680,0xa72961372c78d87cc374ad20,(last! 0x116bc8fdab1fd12a76167da0,0x11444927a7d44eda6494bae0)))
private theorem r5 : BlockChecks S N P 2452 5 372 :=
  block! 2715,15,0x509bcfd254848f943898a1200,0x509bd21aa84eba0c559e7fc80,(more! 0x452baa04f89c1be39bfe6cea0,0x45340da459a4c022f9f930660,(more! 0xa669c232c99eae5ca0f5e2e0,0xa60b3419a5ad2e8513af0dc0,(last! 0x1099b69324ef6ed7c9fd2d80,0x1073cf1671aeb20741fd6a40)))
private theorem r6 : BlockChecks S N P 2452 6 364 :=
  block! 2728,16,0x509bcfd254848f943898a1200,0x509bd21aa84eba0c559e7fc80,(more! 0x4548d5fa2a949bd4a6b1fa880,0x4551396d6c79649ac1b7d1740,(more! 0xa55f07f79994a1589c581560,0xa4fefc2dfb8419f2a0699560,(last! 0xfd182e7dc2121f00bb96ac0,0xfad1bd6da1b76608f9f7300)))
private theorem r7 : BlockChecks S N P 2452 7 356 :=
  block! 2742,16,0x509bcfd254848f943898a1200,0x509bd21aa84eba0c559e7fc80,(more! 0x45678abe9f3695cf8672dc440,0x456fedebaf93d642fe44d4de0,(more! 0xa4500df9bc5cc883995faaa0,0xa3ee7ed6e6f0dab56aaebf40,(last! 0xef5845ede77b6b42f718ea0,0xed2a510f3e41aeeda660820)))
private theorem r8 : BlockChecks S N P 2452 8 347 :=
  block! 2759,1,0x509bcfd254848f943898a1200,0x509bd21aa84eba0c559e7fc80,(more! 0x45850a523287e9c15949819a0,0x458d6d52537701848434c1660,(more! 0xa3506788c62c6800ee7c0be0,0xa2ed66c0731591d065f86da0,(more! 0xe1cd39e19976dd4fa5fd540,0xdfb6a7da6ccba2cfa731ae0,(last! 0x924fd31a0994b3ec880,0x760c948f8fc264ed000))))
private theorem r9 : BlockChecks S N P 2452 9 337 :=
  block! 2778,2,0x509bcfd254848f943898a1200,0x509bd21aa84eba0c559e7fc80,(more! 0x45a1c6f70b6e4081c210d33c0,0x45aa29dc59e9bb7b254c76f20,(more! 0xa25e14f53361450b41fbe6a0,0xa1f9b10cdb4f2a268ef996c0,(more! 0xd424ea35be8c9ba024e9d80,0xd224ddc805d548fc0b59560,(last! 0x3b0a90c778857e998080,0x35a0481f766aaf66eea0))))
private theorem r10 : BlockChecks S N P 2452 10 327 :=
  block! 2799,3,0x509bcfd254848f943898a1200,0x509bd21aa84eba0c559e7fc80,(more! 0x45c08161ffc311be0c2c49200,0x45c8e400401c4ba9ddb43eea0,(more! 0xa16449708afddd08c8359520,0xa0fe7a393dc2453fa5c16f60,(more! 0xc504f59ac605eef9544f020,0xc31bf46830c37820f26c6e0,(last! 0x61da47a246d21e5c3700,0x5b7977580608b4c5fb40))))
private theorem r11 : BlockChecks S N P 2452 11 317 :=
  block! 2821,3,0x509bcfd254848f943898a1200,0x509bd21aa84eba0c559e7fc80,(more! 0x45e1078254f10c15817144920,0x45e969a52336a433639fab780,(more! 0xa062600e36d5c4608c8271a0,0x9ffb1e8417bec445fea97320,(more! 0xb4b0d4efda3809014049020,0xb2df4ab332c49cff6b404e0,(last! 0x37fed9911dfc06ca0a00,0x34518082db37924f5e60))))
private theorem r12 : BlockChecks S N P 2452 12 304 :=
  block! 2851,5,0x509bcfd254848f943898a1200,0x509bd21aa84eba0c559e7fc80,(more! 0x45fd31168446920eb23de3900,0x4605931110ea99268018319a0,(more! 0x9f8b1d292744fc7dd8757620,0x9f2296ea08a17c616dc887e0,(more! 0xa5ed146aedca46249357d00,0xa42fc4a0c117a28f93e2540,(last! 0x10d3d53eb8d00d4a900,0xcfb07cc7c0c1f09be0))))
private theorem r13 : BlockChecks S N P 2452 13 291 :=
  block! 2872,5,0x509bcfd254848f943898a1200,0x509bd21aa84eba0c559e7fc80,(more! 0x461b6770b4a0df73a5a90f380,0x4623c8e850949cee711008cc0,(more! 0x9ea5a9ee5358bd80f6044b20,0x9e3bd354d6bb5be9e801aaa0,(more! 0x9618746b03b35f361232e00,0x9470aa30cd2c02ba7247280,(last! 0,0))))
private theorem r14 : BlockChecks S N P 2452 14 275 :=
  block! 2818,3,0x509bcfd254848f943898a1200,0x509bd21aa84eba0c559e7fc80,(more! 0x4636136767c9d985a0d029560,0x463e74810732a6d891a3402a0,(more! 0x9de2088ef3767914d12368c0,0x9d77047e44f98220d2568ce0,(more! 0x879dc0c7fd14c2ca68efd20,0x86092ac75aeca494cefe8a0,(last! 0,0))))
private theorem r15 : BlockChecks S N P 2452 15 258 :=
  block! 2770,1,0x509bcfd254848f943898a1200,0x509bd21aa84eba0c559e7fc80,(more! 0x4650b51e0b5ea1d7a82efebe0,0x465915a2e5bf165bfc1e259c0,(more! 0x9d1dc4337d5d563d1edf11c0,0x9cb191dc591ac82f58479d40,(more! 0x7949699dfa254c50e5ea8a0,0x77c84d7e57539d2631cd0e0,(last! 0,0))))
private theorem r16 : BlockChecks S N P 2452 16 238 :=
  block! 2729,16,0x509bcfd254848f943898a1200,0x509bd21aa84eba0c559e7fc80,(more! 0x466845c50d890feffcb36d1a0,0x4670a5d276c9ce38731941520,(more! 0x9c7606a7728e575bd725d360,0x9c08bd36e60eefdc3c287940,(last! 0x6c309fb78c5fd090a7265a0,0x6ac16bf8782767f4fcf6520)))
private theorem r17 : BlockChecks S N P 2452 17 216 :=
  block! 2692,14,0x509bcfd254848f943898a1200,0x509bd21aa84eba0c559e7fc80,(more! 0x467e6b3128cf5ab3537dca480,0x4686cabda856ce957e7beeb80,(more! 0x9bd9b0e32c7831aa3554ffa0,0x9b6b547e3c2b930fa7c07e80,(last! 0x5fcfc94c8837d2a77636e20,0x5e7245739efcd19a9102f80)))
private theorem r18 : BlockChecks S N P 2452 18 192 :=
  block! 2660,13,0x509bcfd254848f943898a1200,0x509bd21aa84eba0c559e7fc80,(more! 0x4693316fba92993fbe6171fa0,0x469b9075ac646f6da56fbcd00,(more! 0x9b4776f6bb865f313f6eea80,0x9ad807ed8efb81a909690d80,(last! 0x542efeb246320c6522dae40,0x52e32bad9347be68ba13e40)))
private theorem r19 : BlockChecks S N P 2452 19 166 :=
  block! 2631,12,0x509bcfd254848f943898a1200,0x509bd21aa84eba0c559e7fc80,(more! 0x46a6a74b6fada1bc85cdb0be0,0x46af05c8815601c19e5c37060,(more! 0x9abe1477a7981f7366119b80,0x9a4d8faf7b7668241bf2fc40,(last! 0x495305214b8a0797c09e960,0x4819172810ee4913030f880)))
private theorem r20 : BlockChecks S N P 2452 20 137 :=
  block! 2604,11,0x509bcfd254848f943898a1200,0x509bd21aa84eba0c559e7fc80,(more! 0x46b7e4024fecdc5ce78ad1ac0,0x46c04212855ed9e4ca4b3e620,(more! 0x9a48601055fa04798ba10480,0x99d6c85502883ad24aea00e0,(last! 0x3f6b1137d344c82630301e0,0x3e42be77b8dafa5d05d0960)))
private theorem r21 : BlockChecks S N P 2452 21 106 :=
  block! 2581,10,0x509bcfd254848f943898a1200,0x509bd21aa84eba0c559e7fc80,(more! 0x46c815bc107fd4172ea32e940,0x46d0735e52db066dce2292880,(more! 0x99d80b46b753451b792aec40,0x996556446a11141dd404a220,(last! 0x363a023ab55e1bb0eb981c0,0x3523f13ef7a1fdc9451b4c0)))
private theorem r22 : BlockChecks S N P 2452 22 74 :=
  block! 2559,9,0x509bcfd254848f943898a1200,0x509bd21aa84eba0c559e7fc80,(more! 0x46d821d0f2423dca431099880,0x46e07eedca7d5775ba6bde8e0,(more! 0x9960da672804b471bb467a40,0x98ecf4e30be3809871bb4a40,(last! 0x2da7d0828966c95e2abc9c0,0x2ca54da96cb371866f12ca0)))
private theorem r23 : BlockChecks S N P 2452 23 39 :=
  block! 2539,9,0x509bcfd254848f943898a1200,0x509bd21aa84eba0c559e7fc80,(more! 0x46e6566de962bfc5351ea7d80,0x46eeb3218b5160d4d90dfbc40,(more! 0x98f86c5571d3709f4c36caa0,0x988350f11d230129f3903820,(last! 0x25f6d425314330567af3440,0x2508181361e531c8238e780)))
private theorem r24 : BlockChecks S N P 2452 24 2 :=
  block! 2521,8,0x509bcfd254848f943898a1200,0x509bd21aa84eba0c559e7fc80,(more! 0x46f3a938e7407e0af51cea360,0x46fc0586baa87f924b520ac80,(more! 0x9892291fe102c315d6833ea0,0x981bca1c667e804a194938c0,(last! 0x1f054686c615535a447a8a0,0x1e2b29ce0f77af04145e4e0)))

theorem none : BlockChecks (terminal .h2452).shape (terminal .h2452).nodeRows
    (terminal .h2452).poleMoment (start .h2452) (threshold .h2452 Option.none) 0 := r0

theorem all : GradeChecks (terminal .h2452) (start .h2452) 1 (grades .h2452) :=
  ⟨r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,trivial⟩
end h2452

private theorem checks (b : Band) (x : Test b) :
    let t := tested b x
    BlockChecks t.shape t.nodeRows t.poleMoment (start b) (threshold b x) (seedThreshold b x) := by
  have hn : BlockChecks (terminal b).shape (terminal b).nodeRows (terminal b).poleMoment
      (start b) (threshold b Option.none) 0 := by
    cases b <;> first | exact h2452.none
  have hc : GradeChecks (terminal b) (start b) 1 (grades b) := by
    cases b <;> first | exact h2452.all
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
end High52Terminal
