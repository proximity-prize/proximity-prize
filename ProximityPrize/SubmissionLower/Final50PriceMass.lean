import ProximityPrize.SubmissionLower.Final50PriceCaps

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
namespace Final50PriceMass
open Final50PriceCaps (Band start thresholds order)
open Final50Price (layerNeed)
open K1_13 (Shape remaining)
open K1_13_8 (zeroShape)
open Final50PriceLayer (fastLayer availableMass)
open K1_13_8_2 (Threshold)
open P0_9_8 (symbol_count)
open private P3_6_8_1.sumBelow P3_6_8_1.sumBelow_eq P3_6_8_1.sumBelow_add
  from ProximityPrize.SubmissionLower.GoldBranch6N8

private theorem mass_eq (r y : Shape) (L : ℕ) (hr : r = zeroShape ∨ 0 < r.j)
    (hj : 0 < r.j+y.j) : availableMass r y L =
    P3_6_8_1.sumBelow (fastLayer r y L) (L + 1650 / (r.j+y.j)) := by
  rw [P3_6_8_1.sumBelow_eq, Final50PriceLayer.availableMass_eq_sum hr hj le_rfl]

private def check (f : ℕ → ℕ) (offset length : ℕ) : List ℕ → Bool
  | [] => decide (length = 0)
  | v :: vs =>
      decide (P3_6_8_1.sumBelow (fun k => f (offset + k)) (min length 12) = v) &&
        check f (offset + min length 12) (length - 12) vs

theorem check_sum (f : ℕ → ℕ) (offset length : ℕ) (values : List ℕ)
    (h : check f offset length values = true) :
    P3_6_8_1.sumBelow f (offset + length) = P3_6_8_1.sumBelow f offset + values.sum := by
  induction values generalizing offset length with
  | nil =>
    have hz : length = 0 := of_decide_eq_true h
    simp [hz]
  | cons v vs ih =>
    have hv : P3_6_8_1.sumBelow (fun k => f (offset + k)) (min length 12) = v :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
    have hr := (Bool.and_eq_true_iff.mp h).2
    have hs : min length 12 + (length - 12) = length := by omega
    calc
      _ = P3_6_8_1.sumBelow f (offset + min length 12 + (length - 12)) := by rw [Nat.add_assoc, hs]
      _ = P3_6_8_1.sumBelow f (offset + min length 12) + vs.sum := ih _ _ hr
      _ = _ := by rw [P3_6_8_1.sumBelow_add, hv, List.sum_cons, Nat.add_assoc]

theorem mass_of_checks (f : ℕ → ℕ) (N : ℕ) (values : List ℕ)
    (h : check f 0 N values = true) (hv : values.sum < layerNeed) :
    P3_6_8_1.sumBelow f N < layerNeed := by
  have hs := check_sum f 0 N values h
  have hsum : P3_6_8_1.sumBelow f N = values.sum := by
    simpa only [Nat.zero_add, P3_6_8_1.sumBelow] using hs
  rwa [hsum]

theorem m0_0 : availableMass (start .empty) ⟨3,9,0⟩ 8 < layerNeed := by
  rw [mass_eq (start .empty) ⟨3,9,0⟩ 8 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 191 [4825948217084, 4132812429204, 3346395229824, 2664912491052, 2081398425432, 1588751196612, 1179732919344, 846969659484, 582951433992, 380032210932, 230429909472, 126226399884, 59367503544, 21662992932, 4786591632, 275974332] (by decide +kernel) (by decide +kernel)

theorem m0_1 : availableMass (start .empty) ⟨4,10,0⟩ 13 < layerNeed := by
  rw [mass_eq (start .empty) ⟨4,10,0⟩ 13 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 178 [4881692334132, 4442155510380, 3525029122525, 2741171948913, 2082291123621, 1537845443449, 1097196937197, 749610865665, 484255721653, 290203229961, 156428347389, 71809262737, 25127396805, 5067402393, 217600323] (by decide +kernel) (by decide +kernel)

theorem m0_2 : availableMass (start .empty) ⟨4,12,0⟩ 20 < layerNeed := by
  rw [mass_eq (start .empty) ⟨4,12,0⟩ 20 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 157 [4881692334132, 4804946414772, 3895730412212, 2911848547124, 2106781953716, 1463763834164, 965597408948, 594655916852, 332882614964, 161790778676, 62463701684, 15554695988, 1287091892, 79630] (by decide +kernel) (by decide +kernel)

theorem m0_3 : availableMass (start .empty) ⟨10,8,0⟩ 7 < layerNeed := by
  rw [mass_eq (start .empty) ⟨10,8,0⟩ 7 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 213 [4793673263835, 4045916974340, 3265316219748, 2600070158276, 2038789804580, 1570624092804, 1185259876580, 872921929028, 624372942756, 430913529860, 284382221924, 177155470020, 102147644708, 52811036036, 23135853540, 7650226244, 1420202660, 50147242] (by decide +kernel) (by decide +kernel)

theorem m0_4 : availableMass (start .empty) ⟨11,7,0⟩ 2 < layerNeed := by
  rw [mass_eq (start .empty) ⟨11,7,0⟩ 2 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 237 [4576725944226, 3797718552125, 3113305534285, 2524422475669, 2021938291349, 1597165238989, 1241858918845, 948218273765, 708885589189, 516946493149, 365929956269, 249808291765, 162997155445, 100355545709, 57185803549, 29233612549, 12687998885, 4181331325, 789321229, 31102506] (by decide +kernel) (by decide +kernel)

theorem m0_5 : availableMass (start .empty) ⟨5,15,0⟩ 27 < layerNeed := by
  rw [mass_eq (start .empty) ⟨5,15,0⟩ 27 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 137 [4881692334132, 4881692334132, 4437255256635, 3154442137598, 2118080059058, 1335147950918, 771962125178, 393789133838, 164845768898, 48299062358, 6266286218, 39699549] (by decide +kernel) (by decide +kernel)

theorem m0_6 : availableMass (start .empty) ⟨6,18,0⟩ 32 < layerNeed := by
  rw [mass_eq (start .empty) ⟨6,18,0⟩ 32 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 123 [4881692334132, 4881692334132, 4763608135197, 3451951091511, 2160613118979, 1236119571567, 620159220603, 252244055079, 69709281651, 7713324639, 17052237] (by decide +kernel) (by decide +kernel)

theorem m0_7 : availableMass (start .empty) ⟨18,6,0⟩ 4 < layerNeed := by
  rw [mass_eq (start .empty) ⟨18,6,0⟩ 4 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 279 [4677119384250, 3894294222043, 3178174636159, 2565180895363, 2044950079975, 1607665705387, 1244057722063, 945402515539, 703522906423, 510788150395, 360113938207, 244962395683, 159342083719, 97807998283, 55461570415, 27950666227, 11469647021, 2842448701, 110010100, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_8 : availableMass (start .empty) ⟨8,24,0⟩ 38 < layerNeed := by
  rw [mass_eq (start .empty) ⟨8,24,0⟩ 38 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 106 [4881692334132, 4881692334132, 4881692334132, 4034607422866, 2218587115688, 1036617456104, 371811488552, 78425324648, 3837150724] (by decide +kernel) (by decide +kernel)

theorem m0_9 : availableMass (start .empty) ⟨33,5,0⟩ 16 < layerNeed := by
  rw [mass_eq (start .empty) ⟨33,5,0⟩ 16 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 346 [4881692334132, 4635795893868, 3709228724609, 2870619424897, 2161142255905, 1567953728033, 1078847119681, 682252477249, 367329153517, 131960742747, 14310064598, 34731191, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_10 : availableMass (start .empty) ⟨33,6,0⟩ 18 < layerNeed := by
  rw [mass_eq (start .empty) ⟨33,6,0⟩ 18 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 293 [4881692334132, 4726497233312, 3781159553572, 2873440552228, 2123781080164, 1513835749348, 1026343083940, 645125520292, 355089944499, 143930988805, 22955636671, 181853441, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_11 : availableMass (start .empty) ⟨34,9,0⟩ 24 < layerNeed := by
  rw [mass_eq (start .empty) ⟨34,9,0⟩ 24 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 207 [4881692334132, 4881692334132, 4155061442049, 2974508646993, 2059427297673, 1367503668009, 860036885937, 501938933409, 261734646393, 111561763727, 28061103148, 876352872, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_12 : availableMass (start .empty) ⟨13,39,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨13,39,0⟩ 44 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 86 [4881692334132, 4881692334132, 4881692334132, 4625783876254, 2193723787754, 570305888534, 52234475402, 15876318] (by decide +kernel) (by decide +kernel)

theorem m0_13 : availableMass (start .empty) ⟨64,4,0⟩ 32 < layerNeed := by
  rw [mass_eq (start .empty) ⟨64,4,0⟩ 32 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 444 [4881692334132, 4881692334132, 4784452944186, 3640887556676, 2374770061700, 1297187869066, 413066750396, 15429985030, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_14 : availableMass (start .empty) ⟨64,5,0⟩ 32 < layerNeed := by
  rw [mass_eq (start .empty) ⟨64,5,0⟩ 32 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 362 [4881692334132, 4881692334132, 4778130961275, 3579103133936, 2288416295700, 1229631223424, 393154559215, 15374694923, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_15 : availableMass (start .empty) ⟨64,6,0⟩ 33 < layerNeed := by
  rw [mass_eq (start .empty) ⟨64,6,0⟩ 33 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 308 [4881692334132, 4881692334132, 4816672740210, 3641030334669, 2302372410249, 1240630875813, 427459431655, 23932786880, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_16 : availableMass (start .empty) ⟨65,7,0⟩ 34 < layerNeed := by
  rw [mass_eq (start .empty) ⟨65,7,0⟩ 34 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 269 [4881692334132, 4881692334132, 4847733561916, 3703132247209, 2297233928969, 1218213918961, 422279450344, 25397754716, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_17 : availableMass (start .empty) ⟨65,9,0⟩ 35 < layerNeed := by
  rw [mass_eq (start .empty) ⟨65,9,0⟩ 35 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 218 [4881692334132, 4881692334132, 4869681942938, 3744275280765, 2244546827493, 1161778346277, 419735400835, 35486857925, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_18 : availableMass (start .empty) ⟨65,10,0⟩ 35 < layerNeed := by
  rw [mass_eq (start .empty) ⟨65,10,0⟩ 35 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 200 [4881692334132, 4881692334132, 4869018683879, 3698711251436, 2168503417956, 1096989792476, 391096458647, 34270888409, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_19 : availableMass (start .empty) ⟨65,12,0⟩ 36 < layerNeed := by
  rw [mass_eq (start .empty) ⟨65,12,0⟩ 36 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 173 [4881692334132, 4881692334132, 4881692334132, 3769988691498, 2130784764234, 1043076571242, 375382717633, 42844993836, 249900, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_20 : availableMass (start .empty) ⟨66,16,0⟩ 39 < layerNeed := by
  rw [mass_eq (start .empty) ⟨66,16,0⟩ 39 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 142 [4881692334132, 4881692334132, 4881692334132, 4124154209185, 2204589682932, 1001428115156, 348354916532, 56012033930, 59555595, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_21 : availableMass (start .empty) ⟨66,18,0⟩ 39 < layerNeed := by
  rw [mass_eq (start .empty) ⟨66,18,0⟩ 39 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 130 [4881692334132, 4881692334132, 4881692334132, 4076492128074, 2080072146321, 888880487229, 286825687497, 44334361883, 59555595, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_22 : availableMass (start .empty) ⟨67,20,0⟩ 40 < layerNeed := by
  rw [mass_eq (start .empty) ⟨67,20,0⟩ 40 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 122 [4881692334132, 4881692334132, 4881692334132, 4188643362892, 2084580273444, 841655623828, 251924265732, 36819536571, 72751124, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_23 : availableMass (start .empty) ⟨66,22,0⟩ 41 < layerNeed := by
  rw [mass_eq (start .empty) ⟨66,22,0⟩ 41 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 116 [4881692334132, 4881692334132, 4881692334132, 4309120735189, 2128138725943, 824831527387, 235504529567, 35620234378, 452655058, 0] (by decide +kernel) (by decide +kernel)

theorem m0_24 : availableMass (start .empty) ⟨66,24,0⟩ 42 < layerNeed := by
  rw [mass_eq (start .empty) ⟨66,24,0⟩ 42 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 110 [4881692334132, 4881692334132, 4881692334132, 4424058554462, 2176196361496, 801683072728, 211939283608, 28845858904, 505158728, 0] (by decide +kernel) (by decide +kernel)

theorem m0_25 : availableMass (start .empty) ⟨67,28,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .empty) ⟨67,28,0⟩ 43 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 101 [4881692334132, 4881692334132, 4881692334132, 4515407663255, 2137300605000, 688815571704, 143701645480, 11773877592, 42210998] (by decide +kernel) (by decide +kernel)

theorem m0_26 : availableMass (start .empty) ⟨68,27,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .empty) ⟨68,27,0⟩ 43 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 104 [4881692334132, 4881692334132, 4881692334132, 4522350741384, 2175920575665, 723498464265, 159928337193, 14994976785, 93996274] (by decide +kernel) (by decide +kernel)

theorem m0_27 : availableMass (start .empty) ⟨68,30,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨68,30,0⟩ 44 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 99 [4881692334132, 4881692334132, 4881692334132, 4621914009735, 2221293901653, 675890992881, 125962234029, 7680751497, 3051063] (by decide +kernel) (by decide +kernel)

theorem m0_28 : availableMass (start .empty) ⟨68,33,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨68,33,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 95 [4881692334132, 4881692334132, 4881692334132, 4713403633292, 2294459305859, 639080627339, 98445368675, 3315302389] (by decide +kernel) (by decide +kernel)

theorem m0_29 : availableMass (start .empty) ⟨69,45,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨69,45,0⟩ 47 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 83 [4881692334132, 4881692334132, 4881692334132, 4845762669415, 2335659223362, 419641515222, 19277143259] (by decide +kernel) (by decide +kernel)

theorem m0_30 : availableMass (start .empty) ⟨71,43,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨71,43,0⟩ 47 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 85 [4881692334132, 4881692334132, 4881692334132, 4846809406261, 2388436467983, 465493169239, 28125584383, 266745] (by decide +kernel) (by decide +kernel)

theorem m0_31 : availableMass (start .empty) ⟨69,49,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨69,49,0⟩ 47 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 80 [4881692334132, 4881692334132, 4881692334132, 4843213012092, 2213651195119, 326897441183, 7463477446] (by decide +kernel) (by decide +kernel)

theorem m0_32 : availableMass (start .empty) ⟨97,28,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨97,28,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 103 [4881692334132, 4881692334132, 4881692334132, 4712125300543, 2273798939836, 606202225612, 71194671746, 13716081, 0] (by decide +kernel) (by decide +kernel)

theorem m0_33 : availableMass (start .empty) ⟨98,31,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨98,31,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 98 [4881692334132, 4881692334132, 4881692334132, 4700836472654, 2154320283129, 513180639801, 50059257997, 3321960, 0] (by decide +kernel) (by decide +kernel)

theorem m0_34 : availableMass (start .empty) ⟨84,46,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨84,46,0⟩ 47 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 82 [4881692334132, 4881692334132, 4881692334132, 4843393484827, 2231091807703, 351894275523, 12169373699] (by decide +kernel) (by decide +kernel)

theorem m0_35 : availableMass (start .empty) ⟨97,36,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨97,36,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 91 [4881692334132, 4881692334132, 4881692334132, 4781577465255, 2214539958918, 462844591302, 37299512838, 61338664] (by decide +kernel) (by decide +kernel)

theorem m0_36 : availableMass (start .empty) ⟨97,37,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨97,37,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 90 [4881692334132, 4881692334132, 4881692334132, 4779750717817, 2181543308011, 438331781139, 32379031707, 43085789] (by decide +kernel) (by decide +kernel)

theorem m0_37 : availableMass (start .empty) ⟨98,44,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨98,44,0⟩ 47 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 84 [4881692334132, 4881692334132, 4881692334132, 4843043065581, 2219190855948, 350088812652, 13582511308] (by decide +kernel) (by decide +kernel)

theorem m0_38 : availableMass (start .empty) ⟨105,43,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨105,43,0⟩ 47 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 85 [4881692334132, 4881692334132, 4881692334132, 4842864306633, 2211625505839, 345751438567, 13312871567, 3177] (by decide +kernel) (by decide +kernel)

theorem m0_39 : availableMass (start .empty) ⟨98,52,0⟩ 48 < layerNeed := by
  rw [mass_eq (start .empty) ⟨98,52,0⟩ 48 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 79 [4881692334132, 4881692334132, 4881692334132, 4881692334132, 2303473978020, 272560553476, 3645523230] (by decide +kernel) (by decide +kernel)

theorem m0_40 : availableMass (start .empty) ⟨112,41,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨112,41,0⟩ 47 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 87 [4881692334132, 4881692334132, 4881692334132, 4843314922666, 2230952093039, 357143460959, 13937804449, 0] (by decide +kernel) (by decide +kernel)

theorem m0_41 : availableMass (start .empty) ⟨105,51,0⟩ 48 < layerNeed := by
  rw [mass_eq (start .empty) ⟨105,51,0⟩ 48 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 80 [4881692334132, 4881692334132, 4881692334132, 4881692334132, 2298793551355, 272729779867, 4047264754] (by decide +kernel) (by decide +kernel)

theorem m0_42 : availableMass (start .empty) ⟨119,40,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨119,40,0⟩ 47 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 88 [4881692334132, 4881692334132, 4881692334132, 4843130547107, 2220665734970, 346097396138, 10847488171, 0] (by decide +kernel) (by decide +kernel)

theorem m0_43 : availableMass (start .empty) ⟨111,50,0⟩ 48 < layerNeed := by
  rw [mass_eq (start .empty) ⟨111,50,0⟩ 48 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 81 [4881692334132, 4881692334132, 4881692334132, 4881692334132, 2297578703854, 273787098046, 4394098198] (by decide +kernel) (by decide +kernel)

theorem m0_44 : availableMass (start .empty) ⟨116,49,0⟩ 48 < layerNeed := by
  rw [mass_eq (start .empty) ⟨116,49,0⟩ 48 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 81 [4881692334132, 4881692334132, 4881692334132, 4881692334132, 2300038288243, 276070542003, 4682415405] (by decide +kernel) (by decide +kernel)

theorem m0_45 : availableMass (start .empty) ⟨122,48,0⟩ 48 < layerNeed := by
  rw [mass_eq (start .empty) ⟨122,48,0⟩ 48 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 82 [4881692334132, 4881692334132, 4881692334132, 4881692334132, 2297525080152, 274344020760, 4527733246] (by decide +kernel) (by decide +kernel)

theorem m1_0 : availableMass (start .one3) ⟨2,5,0⟩ 5 < layerNeed := by
  rw [mass_eq (start .one3) ⟨2,5,0⟩ 5 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 211 [4642206004513, 3908443939100, 3226450469852, 2627896253340, 2107591612508, 1660290247196, 1280689234140, 963429026972, 703093456220, 494209729308, 331248430556, 208623521180, 120692339292, 61755599900, 26057394908, 7785193116, 1069840220, 9396582] (by decide +kernel) (by decide +kernel)

theorem m1_1 : availableMass (start .one3) ⟨2,6,0⟩ 13 < layerNeed := by
  rw [mass_eq (start .one3) ⟨2,6,0⟩ 13 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 196 [4740005313959, 4179716912532, 3387268510392, 2700137567964, 2111365856064, 1613859096612, 1200386962632, 863583078252, 595945018704, 389834310324, 237476430552, 130960807932, 62240822112, 23133803844, 5321034984, 347748492, 0] (by decide +kernel) (by decide +kernel)

theorem m1_2 : availableMass (start .one3) ⟨3,9,0⟩ 29 < layerNeed := by
  rw [mass_eq (start .one3) ⟨3,9,0⟩ 29 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 166 [4740005313959, 4439709210263, 3994562913573, 3043800793124, 2213691030116, 1548101679524, 1029898667492, 641517938468, 364965455204, 181817198756, 73219168484, 19887382052, 2107875428, 3342188] (by decide +kernel) (by decide +kernel)

theorem m1_3 : availableMass (start .one3) ⟨5,15,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .one3) ⟨5,15,0⟩ 43 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 134 [4740005313959, 4439709210263, 4152103344383, 3743774803957, 2530520535747, 1495074929079, 787026332811, 346582096959, 111772789203, 18452194887, 370607902, 0] (by decide +kernel) (by decide +kernel)

theorem m1_4 : availableMass (start .one3) ⟨7,20,0⟩ 48 < layerNeed := by
  rw [mass_eq (start .one3) ⟨7,20,0⟩ 48 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 119 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2786514673371, 1432208984315, 606052134443, 180917044395, 24546638267, 196931359] (by decide +kernel) (by decide +kernel)

theorem m1_5 : availableMass (start .one3) ⟨8,24,0⟩ 51 < layerNeed := by
  rw [mass_eq (start .one3) ⟨8,24,0⟩ 51 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 112 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3039057113695, 1435254996957, 510577153917, 105534727413, 4813289894, 0] (by decide +kernel) (by decide +kernel)

theorem m1_6 : availableMass (start .one3) ⟨64,4,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .one3) ⟨64,4,0⟩ 43 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 278 [4740005313959, 4439709210263, 4152103344383, 3752572946018, 2584412352118, 1537580638914, 756538432182, 206861471946, 3709972440, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m1_7 : availableMass (start .one3) ⟨64,5,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .one3) ⟨64,5,0⟩ 44 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 250 [4740005313959, 4439709210263, 4152103344383, 3788468710533, 2618219619544, 1535932399352, 755413805080, 224757329025, 6718188686, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m1_8 : availableMass (start .one3) ⟨65,15,0⟩ 50 < layerNeed := by
  rw [mass_eq (start .one3) ⟨65,15,0⟩ 50 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 141 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2919910046415, 1388504358813, 546251175849, 155289513621, 18975298538, 1028805, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m1_9 : availableMass (start .one3) ⟨68,28,0⟩ 55 < layerNeed := by
  rw [mass_eq (start .one3) ⟨68,28,0⟩ 55 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 108 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3320523117932, 1340356667044, 320282700704, 35041311940, 342645406] (by decide +kernel) (by decide +kernel)

theorem m1_10 : availableMass (start .one3) ⟨67,33,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one3) ⟨67,33,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 101 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3392497504446, 1313387025948, 250090524828, 14379748380, 26822] (by decide +kernel) (by decide +kernel)

theorem m1_11 : availableMass (start .one3) ⟨69,34,0⟩ 57 < layerNeed := by
  rw [mass_eq (start .one3) ⟨69,34,0⟩ 57 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 101 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3474743873132, 1419128395642, 266257085374, 14737998554, 0] (by decide +kernel) (by decide +kernel)

theorem m1_12 : availableMass (start .one3) ⟨69,37,0⟩ 57 < layerNeed := by
  rw [mass_eq (start .one3) ⟨69,37,0⟩ 57 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 98 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3466173771004, 1333832623220, 209801422420, 6493192690, 0] (by decide +kernel) (by decide +kernel)

theorem m1_13 : availableMass (start .one3) ⟨97,46,0⟩ 59 < layerNeed := by
  rw [mass_eq (start .one3) ⟨97,46,0⟩ 59 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 92 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3581379588887, 1374151293959, 124761144119, 469732184] (by decide +kernel) (by decide +kernel)

theorem m2_0 : availableMass (start .one4) ⟨2,4,0⟩ 7 < layerNeed := by
  rw [mass_eq (start .one4) ⟨2,4,0⟩ 7 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 213 [4636977785678, 3912580500272, 3219286747952, 2613633150768, 2089569294128, 1641073074992, 1262150701872, 946836694832, 689193885488, 483313417008, 323314744112, 203345633072, 117582161712, 60228719408, 25518007088, 7711037232, 1097133872, 11640792] (by decide +kernel) (by decide +kernel)

theorem m2_1 : availableMass (start .one4) ⟨2,5,0⟩ 17 < layerNeed := by
  rw [mass_eq (start .one4) ⟨2,5,0⟩ 17 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 200 [4679106249028, 4183913043040, 3409585951707, 2711153918907, 2115152177931, 1613509753995, 1198140555771, 860943375387, 593801888427, 388584653931, 237145114395, 131321595771, 62937307467, 23800342347, 5703676731, 425170395, 0] (by decide +kernel) (by decide +kernel)

theorem m2_2 : availableMass (start .one4) ⟨2,6,0⟩ 25 < layerNeed := by
  rw [mass_eq (start .one4) ⟨2,6,0⟩ 25 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 190 [4679106249028, 4274622143268, 3657323123495, 2854104521163, 2177212718351, 1616157199859, 1160350682487, 799109115035, 521651678303, 317100785091, 174482080199, 82724440427, 30659974575, 7024023443, 455159831, 0] (by decide +kernel) (by decide +kernel)

theorem m2_3 : availableMass (start .one4) ⟨3,9,0⟩ 38 < layerNeed := by
  rw [mass_eq (start .one4) ⟨3,9,0⟩ 38 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 164 [4679106249028, 4274622143268, 3894297784836, 3263401128705, 2329064903829, 1587884949717, 1022498622133, 609743987061, 326109840213, 147735707029, 50411842677, 9579232053, 333494466, 0] (by decide +kernel) (by decide +kernel)

theorem m2_4 : availableMass (start .one4) ⟨4,12,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .one4) ⟨4,12,0⟩ 46 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 149 [4679106249028, 4274622143268, 3894297784836, 3517174336304, 2589820855372, 1635468552364, 948733647116, 486824113516, 206041955788, 61783208492, 8537936524, 76625962, 0] (by decide +kernel) (by decide +kernel)

theorem m2_5 : availableMass (start .one4) ⟨5,15,0⟩ 51 < layerNeed := by
  rw [mass_eq (start .one4) ⟨5,15,0⟩ 51 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 137 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2862169086096, 1697595233155, 887766733835, 387241499923, 122864943451, 19538690723, 337168944, 0] (by decide +kernel) (by decide +kernel)

theorem m2_6 : availableMass (start .one4) ⟨6,17,0⟩ 53 < layerNeed := by
  rw [mass_eq (start .one4) ⟨6,17,0⟩ 53 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 131 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2961341454934, 1711809284646, 830702543754, 319708835886, 79035689298, 6394162998, 225008] (by decide +kernel) (by decide +kernel)

theorem m2_7 : availableMass (start .one4) ⟨9,27,0⟩ 60 < layerNeed := by
  rw [mass_eq (start .one4) ⟨9,27,0⟩ 60 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 113 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3203080394436, 1982706982542, 684114467842, 131929261614, 4744475064, 0] (by decide +kernel) (by decide +kernel)

theorem m2_8 : availableMass (start .one4) ⟨67,26,0⟩ 61 < layerNeed := by
  rw [mass_eq (start .one4) ⟨67,26,0⟩ 61 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 116 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3203080394436, 1960569472300, 563014499740, 92405737420, 3757559740, 0] (by decide +kernel) (by decide +kernel)

theorem m2_9 : availableMass (start .one4) ⟨67,38,0⟩ 64 < layerNeed := by
  rw [mass_eq (start .one4) ⟨67,38,0⟩ 64 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 103 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3203080394436, 2215799707106, 470185681162, 28649772274, 65774] (by decide +kernel) (by decide +kernel)

theorem m2_10 : availableMass (start .one4) ⟨67,39,0⟩ 64 < layerNeed := by
  rw [mass_eq (start .one4) ⟨67,39,0⟩ 64 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 102 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3203080394436, 2204497947150, 449862398117, 24142520077, 0] (by decide +kernel) (by decide +kernel)

theorem m3_0 : availableMass (start .one5) ⟨1,3,0⟩ 8 < layerNeed := by
  rw [mass_eq (start .one5) ⟨1,3,0⟩ 8 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 214 [4607716673582, 3898952186250, 3218197064346, 2620784491690, 2101527076794, 1655180805066, 1276445038810, 959962517226, 700319356410, 492045049354, 329612465946, 207437852970, 119880834106, 61244409930, 25774957914, 7662232426, 1039364730, 8531027] (by decide +kernel) (by decide +kernel)

theorem m3_1 : availableMass (start .one5) ⟨2,5,0⟩ 31 < layerNeed := by
  rw [mass_eq (start .one5) ⟨2,5,0⟩ 31 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 196 [4628005587678, 4137434455250, 3638699625154, 2893820959159, 2209769463699, 1642357177359, 1180966288939, 814882219239, 533293621059, 325292379199, 179873610459, 85935663639, 32280119539, 7611790959, 538722699, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m3_2 : availableMass (start .one5) ⟨2,6,0⟩ 37 < layerNeed := by
  rw [mass_eq (start .one5) ⟨2,6,0⟩ 37 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 187 [4628005587678, 4137434455250, 3682501885502, 3051842347402, 2281199441886, 1651255490898, 1148449116454, 758988943770, 468853601262, 263791720546, 129321936438, 50732886954, 13083213310, 1201559922, 432433, 0] (by decide +kernel) (by decide +kernel)

theorem m3_3 : availableMass (start .one5) ⟨3,9,0⟩ 49 < layerNeed := by
  rw [mass_eq (start .one5) ⟨3,9,0⟩ 49 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 166 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2589701257010, 1738963263890, 1096866764082, 635184596498, 325044738098, 136930303890, 40679546930, 5485858322, 43264833, 0] (by decide +kernel) (by decide +kernel)

theorem m3_4 : availableMass (start .one5) ⟨5,15,0⟩ 60 < layerNeed := by
  rw [mass_eq (start .one5) ⟨5,15,0⟩ 60 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 142 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 2025884627542, 1065987819926, 469160399830, 151170200854, 24909664598, 496790898, 0] (by decide +kernel) (by decide +kernel)

theorem m3_5 : availableMass (start .one5) ⟨7,19,0⟩ 64 < layerNeed := by
  rw [mass_eq (start .one5) ⟨7,19,0⟩ 64 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 132 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 2228680476695, 1076006409926, 392125707734, 86056245734, 4823182628, 0] (by decide +kernel) (by decide +kernel)

theorem m3_6 : availableMass (start .one5) ⟨8,24,0⟩ 67 < layerNeed := by
  rw [mass_eq (start .one5) ⟨8,24,0⟩ 67 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 123 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 2365540332364, 1087312256608, 309873279852, 37024304592, 138425081, 0] (by decide +kernel) (by decide +kernel)

theorem m3_7 : availableMass (start .one5) ⟨13,39,0⟩ 71 < layerNeed := by
  rw [mass_eq (start .one5) ⟨13,39,0⟩ 71 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 108 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 2501539610304, 1075679297314, 130013272866, 506475111] (by decide +kernel) (by decide +kernel)

theorem m3_8 : availableMass (start .one5) ⟨67,37,0⟩ 72 < layerNeed := by
  rw [mass_eq (start .one5) ⟨67,37,0⟩ 72 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 111 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 2518563168338, 1136182967326, 140813672230, 1593196826, 0] (by decide +kernel) (by decide +kernel)

theorem m3_9 : availableMass (start .one5) ⟨69,38,0⟩ 72 < layerNeed := by
  rw [mass_eq (start .one5) ⟨69,38,0⟩ 72 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 110 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 2518563168338, 1116361829451, 128285624875, 1033940566, 0] (by decide +kernel) (by decide +kernel)

theorem m4_0 : availableMass (start .one6) ⟨1,3,0⟩ 31 < layerNeed := by
  rw [mass_eq (start .one6) ⟨1,3,0⟩ 31 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 214 [4577344072499, 4003054728023, 3452917072720, 2789531199726, 2187519628506, 1677766461774, 1253060268234, 906053567694, 629262831066, 415068480366, 255714888714, 143310380334, 69827230554, 27101665806, 6833863626, 587952654, 79630, 0] (by decide +kernel) (by decide +kernel)

theorem m4_1 : availableMass (start .one6) ⟨2,6,0⟩ 54 < layerNeed := by
  rw [mass_eq (start .one6) ⟨2,6,0⟩ 54 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 191 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2510563557359, 1820141469596, 1239592784924, 796603565468, 473367890972, 251649859484, 112783587356, 37673209244, 6792878108, 194317800, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m4_2 : availableMass (start .one6) ⟨6,18,0⟩ 76 < layerNeed := by
  rw [mass_eq (start .one6) ⟨6,18,0⟩ 76 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 144 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1609639076261, 704972902424, 213031930712, 29753673368, 275870212, 0] (by decide +kernel) (by decide +kernel)

theorem m4_3 : availableMass (start .one6) ⟨11,33,0⟩ 82 < layerNeed := by
  rw [mass_eq (start .one6) ⟨11,33,0⟩ 82 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 124 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1794849109317, 689274807257, 76153300337, 157266145, 0] (by decide +kernel) (by decide +kernel)

theorem m5_0 : availableMass (start .one7) ⟨1,3,0⟩ 73 < layerNeed := by
  rw [mass_eq (start .one7) ⟨1,3,0⟩ 73 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 238 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1408219159335, 994497916451, 670643424767, 425849636283, 249213734999, 129736136915, 56320490031, 17773674347, 2805801863, 47475750, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m5_1 : availableMass (start .one7) ⟨2,6,0⟩ 90 < layerNeed := by
  rw [mass_eq (start .one7) ⟨2,6,0⟩ 90 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 216 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1127927471185, 705005565795, 389918428843, 186201221523, 69815329755, 16372869187, 1136685195, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m5_2 : availableMass (start .one7) ⟨4,12,0⟩ 101 < layerNeed := by
  rw [mass_eq (start .one7) ⟨4,12,0⟩ 101 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 187 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 827098232466, 371051764125, 115686222677, 17613333845, 250903269, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m5_3 : availableMass (start .one7) ⟨8,24,0⟩ 108 < layerNeed := by
  rw [mass_eq (start .one7) ⟨8,24,0⟩ 108 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 161 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 897787493888, 396586615042, 50103348366, 266091540, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m6_0 : availableMass (start .two6thin) ⟨1,3,0⟩ 31 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨1,3,0⟩ 31 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 214 [4577344072499, 4003054728023, 3452917072720, 2789531199726, 2187519628506, 1677766461774, 1253060268234, 906053567694, 629262831066, 415068480366, 255714888714, 143310380334, 69827230554, 27101665806, 6833863626, 587952654, 79630, 0] (by decide +kernel) (by decide +kernel)

theorem m6_1 : availableMass (start .two6thin) ⟨2,6,0⟩ 54 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨2,6,0⟩ 54 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 191 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2510563557359, 1820141469596, 1239592784924, 796603565468, 473367890972, 251649859484, 112783587356, 37673209244, 6792878108, 194317800, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m6_2 : availableMass (start .two6thin) ⟨4,12,0⟩ 70 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨4,12,0⟩ 70 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 161 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2163298428558, 1412812132599, 733439567811, 315742085679, 97538622267, 14471331303, 181944312, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m6_3 : availableMass (start .two6thin) ⟨6,18,0⟩ 76 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨6,18,0⟩ 76 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 144 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1609639076261, 704972902424, 213031930712, 29753673368, 275870212, 0] (by decide +kernel) (by decide +kernel)

theorem m6_4 : availableMass (start .two6thin) ⟨7,19,0⟩ 77 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨7,19,0⟩ 77 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 143 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1647841005765, 715749796229, 205107476965, 25000873501, 107964733, 0] (by decide +kernel) (by decide +kernel)

theorem m6_5 : availableMass (start .two6thin) ⟨7,21,0⟩ 78 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨7,21,0⟩ 78 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 139 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1679373264208, 706376946732, 178118993688, 15092927484, 1404874, 0] (by decide +kernel) (by decide +kernel)

theorem m6_6 : availableMass (start .two6thin) ⟨65,17,0⟩ 78 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨65,17,0⟩ 78 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 149 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1661629786489, 657175695689, 168585025913, 21966066657, 455958501, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m6_7 : availableMass (start .two6thin) ⟨66,30,0⟩ 82 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨66,30,0⟩ 82 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 127 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1791579919530, 655587567492, 76242010884, 666185970, 0] (by decide +kernel) (by decide +kernel)

theorem m6_8 : availableMass (start .two6thin) ⟨68,35,0⟩ 83 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨68,35,0⟩ 83 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 123 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1814597463416, 664694653705, 54911149345, 45707932, 0] (by decide +kernel) (by decide +kernel)

theorem m6_9 : availableMass (start .two6thin) ⟨67,39,0⟩ 84 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨67,39,0⟩ 84 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 120 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1829003555243, 712086006111, 47272342119, 856774] (by decide +kernel) (by decide +kernel)

theorem m6_10 : availableMass (start .two6thin) ⟨96,36,0⟩ 84 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨96,36,0⟩ 84 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 123 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1829003555243, 712728298643, 52640163167, 43783433, 0] (by decide +kernel) (by decide +kernel)

theorem m6_11 : availableMass (start .two6thin) ⟨96,43,0⟩ 84 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨96,43,0⟩ 84 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 117 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1829003555243, 639537380329, 25912393069, 0] (by decide +kernel) (by decide +kernel)

theorem m6_12 : availableMass (start .two6thin) ⟨110,42,0⟩ 84 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨110,42,0⟩ 84 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 118 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1829003555243, 635296154672, 26102579888, 0] (by decide +kernel) (by decide +kernel)

theorem m7_0 : availableMass (start .two6wide) ⟨1,3,0⟩ 87 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨1,3,0⟩ 87 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 270 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1075387724567, 756227964504, 511021542036, 329455388136, 199914958164, 111858982104, 55819464564, 23401684776, 7284196596, 1218828504, 31977764, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m7_1 : availableMass (start .two6wide) ⟨3,9,0⟩ 111 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨3,9,0⟩ 111 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 221 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 863589734713, 601607165778, 306913439410, 130723319950, 41466040090, 7114199830, 196161520, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m7_2 : availableMass (start .two6wide) ⟨5,14,0⟩ 117 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨5,14,0⟩ 117 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 199 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 863589734713, 650239136147, 317811646758, 100333116838, 16934732838, 433998245, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m7_3 : availableMass (start .two6wide) ⟨63,33,0⟩ 125 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨63,33,0⟩ 125 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 167 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 863589734713, 662855171077, 385822161295, 36882344590, 67406562, 0] (by decide +kernel) (by decide +kernel)

theorem m7_4 : availableMass (start .two6wide) ⟨63,36,0⟩ 126 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨63,36,0⟩ 126 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 165 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 863589734713, 662855171077, 407078198593, 39159019732, 33468580, 0] (by decide +kernel) (by decide +kernel)

theorem m7_5 : availableMass (start .two6wide) ⟨62,39,0⟩ 126 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨62,39,0⟩ 126 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 162 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 863589734713, 662855171077, 402608593994, 32978057931, 2291912, 0] (by decide +kernel) (by decide +kernel)

theorem m7_6 : availableMass (start .two6wide) ⟨89,40,0⟩ 126 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨89,40,0⟩ 126 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 161 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 863589734713, 662855171077, 395559396946, 26305504650, 205040, 0] (by decide +kernel) (by decide +kernel)

theorem m7_7 : availableMass (start .two6wide) ⟨89,45,0⟩ 127 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨89,45,0⟩ 127 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 159 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 863589734713, 662855171077, 417080626593, 27746500043, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m7_8 : availableMass (start .two6wide) ⟨101,42,0⟩ 127 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨101,42,0⟩ 127 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 161 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 863589734713, 662855171077, 418451656460, 30005078958, 255245, 0] (by decide +kernel) (by decide +kernel)

theorem m8_0 : availableMass (start .two7) ⟨1,3,0⟩ 73 < layerNeed := by
  rw [mass_eq (start .two7) ⟨1,3,0⟩ 73 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 238 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1408219159335, 994497916451, 670643424767, 425849636283, 249213734999, 129736136915, 56320490031, 17773674347, 2805801863, 47475750, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m8_1 : availableMass (start .two7) ⟨4,11,0⟩ 100 < layerNeed := by
  rw [mass_eq (start .two7) ⟨4,11,0⟩ 100 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 191 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 814034305382, 373494946704, 125419148016, 22921199376, 690879744, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m8_2 : availableMass (start .two7) ⟨4,12,0⟩ 101 < layerNeed := by
  rw [mass_eq (start .two7) ⟨4,12,0⟩ 101 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 187 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 827098232466, 371051764125, 115686222677, 17613333845, 250903269, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m8_3 : availableMass (start .two7) ⟨7,19,0⟩ 106 < layerNeed := by
  rw [mass_eq (start .two7) ⟨7,19,0⟩ 106 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 169 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 885706724675, 379639173521, 70000365133, 2166533734, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m8_4 : availableMass (start .two7) ⟨8,23,0⟩ 108 < layerNeed := by
  rw [mass_eq (start .two7) ⟨8,23,0⟩ 108 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 163 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 897787493888, 405359163390, 56706387510, 531336300, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m8_5 : availableMass (start .two7) ⟨66,32,0⟩ 110 < layerNeed := by
  rw [mass_eq (start .two7) ⟨66,32,0⟩ 110 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 152 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 897787493888, 403741179632, 23445662966, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m8_6 : availableMass (start .two7) ⟨67,34,0⟩ 111 < layerNeed := by
  rw [mass_eq (start .two7) ⟨67,34,0⟩ 111 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 151 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 897787493888, 439251600632, 25351611719, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m8_7 : availableMass (start .two7) ⟨66,36,0⟩ 111 < layerNeed := by
  rw [mass_eq (start .two7) ⟨66,36,0⟩ 111 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 149 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 897787493888, 431266990800, 20851946805, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m8_8 : availableMass (start .two7) ⟨67,35,0⟩ 111 < layerNeed := by
  rw [mass_eq (start .two7) ⟨67,35,0⟩ 111 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 150 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 897787493888, 435074373624, 22955783763, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m8_9 : availableMass (start .two7) ⟨95,40,0⟩ 111 < layerNeed := by
  rw [mass_eq (start .two7) ⟨95,40,0⟩ 111 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 146 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 897787493888, 407803507722, 12107189699, 0, 0] (by decide +kernel) (by decide +kernel)

theorem thresholds_valid (k : Band) (q : Threshold) (hq : q ∈ thresholds k) :
    0 < q.j ∧ availableMass (start k) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  cases k
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m0_0⟩
    · exact ⟨by decide, m0_1⟩
    · exact ⟨by decide, m0_2⟩
    · exact ⟨by decide, m0_3⟩
    · exact ⟨by decide, m0_4⟩
    · exact ⟨by decide, m0_5⟩
    · exact ⟨by decide, m0_6⟩
    · exact ⟨by decide, m0_7⟩
    · exact ⟨by decide, m0_8⟩
    · exact ⟨by decide, m0_9⟩
    · exact ⟨by decide, m0_10⟩
    · exact ⟨by decide, m0_11⟩
    · exact ⟨by decide, m0_12⟩
    · exact ⟨by decide, m0_13⟩
    · exact ⟨by decide, m0_14⟩
    · exact ⟨by decide, m0_15⟩
    · exact ⟨by decide, m0_16⟩
    · exact ⟨by decide, m0_17⟩
    · exact ⟨by decide, m0_18⟩
    · exact ⟨by decide, m0_19⟩
    · exact ⟨by decide, m0_20⟩
    · exact ⟨by decide, m0_21⟩
    · exact ⟨by decide, m0_22⟩
    · exact ⟨by decide, m0_23⟩
    · exact ⟨by decide, m0_24⟩
    · exact ⟨by decide, m0_25⟩
    · exact ⟨by decide, m0_26⟩
    · exact ⟨by decide, m0_27⟩
    · exact ⟨by decide, m0_28⟩
    · exact ⟨by decide, m0_29⟩
    · exact ⟨by decide, m0_30⟩
    · exact ⟨by decide, m0_31⟩
    · exact ⟨by decide, m0_32⟩
    · exact ⟨by decide, m0_33⟩
    · exact ⟨by decide, m0_34⟩
    · exact ⟨by decide, m0_35⟩
    · exact ⟨by decide, m0_36⟩
    · exact ⟨by decide, m0_37⟩
    · exact ⟨by decide, m0_38⟩
    · exact ⟨by decide, m0_39⟩
    · exact ⟨by decide, m0_40⟩
    · exact ⟨by decide, m0_41⟩
    · exact ⟨by decide, m0_42⟩
    · exact ⟨by decide, m0_43⟩
    · exact ⟨by decide, m0_44⟩
    · exact ⟨by decide, m0_45⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m1_0⟩
    · exact ⟨by decide, m1_1⟩
    · exact ⟨by decide, m1_2⟩
    · exact ⟨by decide, m1_3⟩
    · exact ⟨by decide, m1_4⟩
    · exact ⟨by decide, m1_5⟩
    · exact ⟨by decide, m1_6⟩
    · exact ⟨by decide, m1_7⟩
    · exact ⟨by decide, m1_8⟩
    · exact ⟨by decide, m1_9⟩
    · exact ⟨by decide, m1_10⟩
    · exact ⟨by decide, m1_11⟩
    · exact ⟨by decide, m1_12⟩
    · exact ⟨by decide, m1_13⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m2_0⟩
    · exact ⟨by decide, m2_1⟩
    · exact ⟨by decide, m2_2⟩
    · exact ⟨by decide, m2_3⟩
    · exact ⟨by decide, m2_4⟩
    · exact ⟨by decide, m2_5⟩
    · exact ⟨by decide, m2_6⟩
    · exact ⟨by decide, m2_7⟩
    · exact ⟨by decide, m2_8⟩
    · exact ⟨by decide, m2_9⟩
    · exact ⟨by decide, m2_10⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m3_0⟩
    · exact ⟨by decide, m3_1⟩
    · exact ⟨by decide, m3_2⟩
    · exact ⟨by decide, m3_3⟩
    · exact ⟨by decide, m3_4⟩
    · exact ⟨by decide, m3_5⟩
    · exact ⟨by decide, m3_6⟩
    · exact ⟨by decide, m3_7⟩
    · exact ⟨by decide, m3_8⟩
    · exact ⟨by decide, m3_9⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨by decide, m4_0⟩
    · exact ⟨by decide, m4_1⟩
    · exact ⟨by decide, m4_2⟩
    · exact ⟨by decide, m4_3⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨by decide, m5_0⟩
    · exact ⟨by decide, m5_1⟩
    · exact ⟨by decide, m5_2⟩
    · exact ⟨by decide, m5_3⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m6_0⟩
    · exact ⟨by decide, m6_1⟩
    · exact ⟨by decide, m6_2⟩
    · exact ⟨by decide, m6_3⟩
    · exact ⟨by decide, m6_4⟩
    · exact ⟨by decide, m6_5⟩
    · exact ⟨by decide, m6_6⟩
    · exact ⟨by decide, m6_7⟩
    · exact ⟨by decide, m6_8⟩
    · exact ⟨by decide, m6_9⟩
    · exact ⟨by decide, m6_10⟩
    · exact ⟨by decide, m6_11⟩
    · exact ⟨by decide, m6_12⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m7_0⟩
    · exact ⟨by decide, m7_1⟩
    · exact ⟨by decide, m7_2⟩
    · exact ⟨by decide, m7_3⟩
    · exact ⟨by decide, m7_4⟩
    · exact ⟨by decide, m7_5⟩
    · exact ⟨by decide, m7_6⟩
    · exact ⟨by decide, m7_7⟩
    · exact ⟨by decide, m7_8⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m8_0⟩
    · exact ⟨by decide, m8_1⟩
    · exact ⟨by decide, m8_2⟩
    · exact ⟨by decide, m8_3⟩
    · exact ⟨by decide, m8_4⟩
    · exact ⟨by decide, m8_5⟩
    · exact ⟨by decide, m8_6⟩
    · exact ⟨by decide, m8_7⟩
    · exact ⟨by decide, m8_8⟩
    · exact ⟨by decide, m8_9⟩

theorem order_valid (k : Band) (x : Shape) : order k x = 1 ∨
    availableMass (start k) x (order k x - 1) < layerNeed := by
  rcases (P0_9_8.orderFor_select x.b x.j (thresholds k)).2 with h | ⟨q,hq,hb,hj,he⟩
  · exact Or.inl h
  · right
    change order k x = q.l at he
    rw [he]
    obtain ⟨hpos, hsmall⟩ := thresholds_valid k q hq
    have hr : start k = zeroShape ∨ 0 < (start k).j := by cases k <;> decide
    have hi : 0 < (start k).j + q.j := by omega
    exact (Final50PriceLayer.availableMass_anti_prefix (y := ⟨q.b,q.j,0⟩) hr hi hb hj).trans_lt hsmall
#print axioms order_valid
end Final50PriceMass
