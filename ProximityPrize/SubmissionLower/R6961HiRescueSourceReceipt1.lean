import ProximityPrize.SubmissionLower.R6961HiRescueSourceSchedule

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6961.Hi.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open Lower6960.HelperSource (WidthGuard)
open Lower6960.RescueSource (fastLayer fastPhase)

private def pchk (f : ℕ → ℕ) : ℕ → List (ℕ × ℕ) → Option (ℕ × ℕ)
  | _, [] => some (0, 0)
  | s, (n, v) :: rest =>
      if phaseBlock f s n == v then
        match pchk f (s + n) rest with
        | some (tn, tv) => some (n + tn, v + tv)
        | none => none
      else none

private theorem pchk_sound {f : ℕ → ℕ} {s tn tv : ℕ} {cs : List (ℕ × ℕ)}
    (h : pchk f s cs = some (tn, tv)) : phaseBlock f s tn = tv := by
  induction cs generalizing s tn tv with
  | nil =>
    simp only [pchk, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩; rfl
  | cons cv rest ih =>
    rcases cv with ⟨n, v⟩
    unfold pchk at h
    split at h
    · rename_i heq
      cases hrest : pchk f (s + n) rest with
      | none => simp [hrest] at h
      | some p =>
        rw [hrest] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact phaseBlock_append (Nat.eq_of_beq_eq_true heq) (ih hrest) rfl rfl rfl
    · simp at h

private theorem ps {f : ℕ → ℕ} {s n1 v1 : ℕ} (n2 v2 n v : ℕ) (cs : List (ℕ × ℕ))
    (h1 : phaseBlock f s n1 = v1) (h2 : pchk f (s + n1) cs = some (n2, v2))
    (hn : n1 + n2 = n) (hv : v1 + v2 = v) : phaseBlock f s n = v :=
  phaseBlock_append h1 (pchk_sound h2) rfl hn hv

private theorem p1 (r : Fin 4) (s : Fin 17) (h a b c d e n z : ℕ) (cs : List (ℕ × ℕ))
    (h1 : (bank r s).shape.J / b + 1 = n)
    (h2 : pchk (fastLayer (bank r s).shape 179808 h a b c d e) 0 cs = some (n, z)) :
    fastPhase (bank r s).shape 179808 h a b c d e = z :=
  phase_of_block h1 (pchk_sound h2)


private def mchk (B J : ℕ) : ℕ → List (ℕ × ℕ) → Option (ℕ × ℕ)
  | _, [] => some (0, 0)
  | s, (n, v) :: rest =>
      if blockEstimate B J s n == v then
        match mchk B J (s + n) rest with
        | some (tn, tv) => some (n + tn, v + tv)
        | none => none
      else none

private theorem mchk_sound {B J s tn tv : ℕ} {cs : List (ℕ × ℕ)}
    (h : mchk B J s cs = some (tn, tv)) : blockEstimate B J s tn = tv := by
  induction cs generalizing s tn tv with
  | nil =>
    simp only [mchk, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩; rfl
  | cons cv rest ih =>
    rcases cv with ⟨n, v⟩
    unfold mchk at h
    split at h
    · rename_i heq
      cases hrest : mchk B J (s + n) rest with
      | none => simp [hrest] at h
      | some p =>
        rw [hrest] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact block_append (Nat.eq_of_beq_eq_true heq) (ih hrest) rfl rfl rfl
    · simp at h

private theorem bs {B J s n1 v1 : ℕ} (n2 v2 n v : ℕ) (cs : List (ℕ × ℕ))
    (h1 : blockEstimate B J s n1 = v1) (h2 : mchk B J (s + n1) cs = some (n2, v2))
    (hn : n1 + n2 = n) (hv : v1 + v2 = v) : blockEstimate B J s n = v :=
  block_append h1 (mchk_sound h2) rfl hn hv

theorem moment_977_207 : momentEstimate 977 207 = 24758176234 := mchk_sound (by decide +kernel : mchk 977 207 207 [(128,315454880),(128,1893094372),(128,3762297344),(128,4827257344),(128,5019802112),(128,4339931648),(128,2905553180),(128,1377948994),(128,313825184),(32,3011176)] = some (1184,24758176234))

theorem moment_1047_222 : momentEstimate 1047 222 = 32653699308 := mchk_sound (by decide +kernel : mchk 1047 222 222 [(128,340498080),(128,2075230592),(128,4311457024),(128,5736373504),(128,6225960192),(128,5780217088),(128,4419886184),(128,2600283532),(128,1026138287),(117,137654825)] = some (1269,32653699308))

theorem moment_1117_237 : momentEstimate 1117 237 = 42302192650 := mchk_sound (by decide +kernel : mchk 1117 237 237 [(128,365541280),(128,2252469787),(128,4866007104),(128,6688972864),(128,7513694272),(128,7340171328),(128,6168649768),(128,4198892547),(128,2189402175),(128,679563600),(74,38827925)] = some (1354,42302192650))

theorem moment_1326_281 : momentEstimate 1326 281 = 83828003187 := by
  unfold momentEstimate
  have h := mchk_sound (by decide +kernel : mchk 1326 281 281 [(128,440313120),(128,2769958176),(128,6492999306),(128,9717503424),(128,11761980864),(128,12623664576),(128,12302554560),(128,10798650816),(128,8203180395),(128,5254501290),(128,2634292110),(128,787344864)] = some (1536,83786943501))
  have h := bs 71 41059686 1607 83828003187 [(71,41059686)] h (by decide +kernel) (by decide) (by decide)
  exact h

theorem moment_1327_281 : momentEstimate 1327 281 = 84031339757 := by
  unfold momentEstimate
  have h := mchk_sound (by decide +kernel : mchk 1327 281 281 [(128,440670880),(128,2772429472),(128,6499499186),(128,9728620992),(128,11777718720),(128,12644022720),(128,12327532992),(128,10828249536),(128,8234870103),(128,5281874916),(128,2654626290),(128,798423904)] = some (1536,83988539711))
  have h := bs 72 42800046 1608 84031339757 [(72,42800046)] h (by decide +kernel) (by decide) (by decide)
  exact h

theorem moment_1341_282 : momentEstimate 1341 282 = 87154749585 := by
  unfold momentEstimate
  have h := mchk_sound (by decide +kernel : mchk 1341 282 282 [(128,445679520),(128,2807027616),(128,6595706731),(128,9903134464),(128,12026730240),(128,12963337984),(128,12712957696),(128,11275589376),(128,8711118963),(128,5697061300),(128,2967083923),(128,974195776)] = some (1536,87079623589))
  have h := bs 87 75125996 1623 87154749585 [(87,75125996)] h (by decide +kernel) (by decide) (by decide)
  exact h

theorem moment_1387_302 : momentEstimate 1387 302 = 102461756220 := by
  unfold momentEstimate
  have h := mchk_sound (by decide +kernel : mchk 1387 302 302 [(128,462136480),(128,2920707232),(128,6982836384),(128,10787226624),(128,13338903552),(128,14619706368),(128,14629635072),(128,13368689664),(128,10858832125),(128,7630480965),(128,4503008202),(128,1955193296)] = some (1536,102057355964))
  have h := bs 153 404400256 1689 102461756220 [(128,402271696),(25,2128560)] h (by decide +kernel) (by decide) (by decide)
  exact h

theorem moment_1392_291 : momentEstimate 1392 291 = 100699468110 := by
  unfold momentEstimate
  have h := mchk_sound (by decide +kernel : mchk 1392 291 291 [(128,463925280),(128,2933063712),(128,6972032551),(128,10645366912),(128,13102016640),(128,14333929600),(128,14341105792),(128,13123545216),(128,10691106230),(128,7487810802),(128,4379387141),(128,1864956928)] = some (1536,100338246804))
  have h := bs 147 361221306 1683 100699468110 [(128,360231936),(19,989370)] h (by decide +kernel) (by decide) (by decide)
  exact h


private theorem receipt_0_1_2450_0 : fastPhase (bank 0 1).shape 179808 2450 1 1 0 1 0 = 2395428822715458405226443 := p1 0 1 2450 1 1 0 1 0 282 2395428822715458405226443 [(128,1740268094353511183062629),(128,637580200662378974956473),(26,17580527699568247207341)] (by decide +kernel) (by decide +kernel)

private theorem receipt_0_1_2450_1 : fastPhase (bank 0 1).shape 179808 2450 1 1 0 1 1 = 2377017307314442991851875 := p1 0 1 2450 1 1 0 1 1 282 2377017307314442991851875 [(128,1730722641461613454947903),(128,630027001200228566660352),(26,16267664652600970243620)] (by decide +kernel) (by decide +kernel)

private theorem receipt_0_1_2451_0 : fastPhase (bank 0 1).shape 179808 2451 1 1 0 1 0 = 2395447382787672051878768 := p1 0 1 2451 1 1 0 1 0 282 2395447382787672051878768 [(128,1740282775388890489977488),(128,637584010571644312107006),(26,17580596827137249794274)] (by decide +kernel) (by decide +kernel)

private theorem receipt_0_1_2451_1 : fastPhase (bank 0 1).shape 179808 2451 1 1 0 1 1 = 2377035756966157935132369 := p1 0 1 2451 1 1 0 1 1 282 2377035756966157935132369 [(128,1730737255762385794372866),(128,630030772362647764379544),(26,16267728841124376379959)] (by decide +kernel) (by decide +kernel)

theorem receipt_0_1 : Checked (bank 0 1) 1 0 1 := by
  refine checked_from_values (bank 0 1) 1 0 1
    (P3_7_1.checked (bank 0 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1327_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_1_2450_0 receipt_0_1_2450_1 receipt_0_1_2451_0 receipt_0_1_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_1_2450_0 : fastPhase (bank 1 1).shape 179808 2450 1 1 0 2 0 = 2142758792952979278156019 := p1 1 1 2450 1 1 0 2 0 282 2142758792952979278156019 [(128,1559753042643973444040602),(128,567441803578728679037451),(26,15563946730277155077966)] (by decide +kernel) (by decide +kernel)

private theorem receipt_1_1_2450_1 : fastPhase (bank 1 1).shape 179808 2450 1 1 0 2 1 = 2126202216325294958760575 := p1 1 1 2450 1 1 0 2 1 282 2126202216325294958760575 [(128,1551109379608289453099734),(128,560691735993094199505389),(26,14401100723911306155452)] (by decide +kernel) (by decide +kernel)

private theorem receipt_1_1_2451_0 : fastPhase (bank 1 1).shape 179808 2451 1 1 0 2 0 = 2142775406311091071839647 := p1 1 1 2451 1 1 0 2 0 282 2142775406311091071839647 [(128,1559766203176629700519514),(128,567445195205033158736916),(26,15564007929428212583217)] (by decide +kernel) (by decide +kernel)

private theorem receipt_1_1_2451_1 : fastPhase (bank 1 1).shape 179808 2451 1 1 0 2 1 = 2126218730073397207795445 := p1 1 1 2451 1 1 0 2 1 282 2126218730073397207795445 [(128,1551122479569946235852850),(128,560695092955295432522682),(26,14401157548155539419913)] (by decide +kernel) (by decide +kernel)

theorem receipt_1_1 : Checked (bank 1 1) 1 0 2 := by
  refine checked_from_values (bank 1 1) 1 0 2
    (P3_7_1.checked (bank 1 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1327_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_1_2450_0 receipt_1_1_2450_1 receipt_1_1_2451_0 receipt_1_1_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_1_2450_0 : fastPhase (bank 2 1).shape 179808 2450 1 1 0 7 0 = 1106411684946886038484088 := p1 2 1 2450 1 1 0 7 0 282 1106411684946886038484088 [(128,816856823640169292360135),(128,282121848189605979152787),(26,7433013117110766971166)] (by decide +kernel) (by decide +kernel)

private theorem receipt_2_1_2450_1 : fastPhase (bank 2 1).shape 179808 2450 1 1 0 7 1 = 1097530784127924454020694 := p1 2 1 2450 1 1 0 7 1 282 1097530784127924454020694 [(128,811993065316552118948695),(128,278662166692917620265975),(26,6875552118454714806024)] (by decide +kernel) (by decide +kernel)

private theorem receipt_2_1_2451_0 : fastPhase (bank 2 1).shape 179808 2451 1 1 0 7 0 = 1106420304730687985485155 := p1 2 1 2451 1 1 0 7 0 282 1106420304730687985485155 [(128,816863724832247443821194),(128,282123537550659591344740),(26,7433042347780950319221)] (by decide +kernel) (by decide +kernel)

private theorem receipt_2_1_2451_1 : fastPhase (bank 2 1).shape 179808 2451 1 1 0 7 1 = 1097539349290348227931633 := p1 2 1 2451 1 1 0 7 1 282 1097539349290348227931633 [(128,811999931891010820416866),(128,278663838148364040028538),(26,6875579250973367486229)] (by decide +kernel) (by decide +kernel)

theorem receipt_2_1 : Checked (bank 2 1) 1 0 7 := by
  refine checked_from_values (bank 2 1) 1 0 7
    (P3_7_1.checked (bank 2 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1327_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_1_2450_0 receipt_2_1_2450_1 receipt_2_1_2451_0 receipt_2_1_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_1_2450_0 : fastPhase (bank 3 1).shape 179808 2450 1 1 1 1 0 = 157744745236245646959480 := p1 3 1 2450 1 1 1 1 0 208 157744745236245646959480 [(128,137558553747033540162240),(80,20186191489212106797240)] (by decide +kernel) (by decide +kernel)

private theorem receipt_3_1_2450_1 : fastPhase (bank 3 1).shape 179808 2450 1 1 1 1 1 = 156081744621252726900624 := p1 3 1 2450 1 1 1 1 1 208 156081744621252726900624 [(128,136418642736653511494784),(80,19663101884599215405840)] (by decide +kernel) (by decide +kernel)

private theorem receipt_3_1_2451_0 : fastPhase (bank 3 1).shape 179808 2451 1 1 1 1 0 = 157745809022039441987784 := p1 3 1 2451 1 1 1 1 0 208 157745809022039441987784 [(128,137559553302928451134272),(80,20186255719110990853512)] (by decide +kernel) (by decide +kernel)

private theorem receipt_3_1_2451_1 : fastPhase (bank 3 1).shape 179808 2451 1 1 1 1 1 = 156082797894468185292552 := p1 3 1 2451 1 1 1 1 1 208 156082797894468185292552 [(128,136419633319218222260544),(80,19663164575249963032008)] (by decide +kernel) (by decide +kernel)

theorem receipt_3_1 : Checked (bank 3 1) 1 1 1 := by
  refine checked_from_values (bank 3 1) 1 1 1
    (P3_7_1.checked (bank 3 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_977_207)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_1_2450_0 receipt_3_1_2450_1 receipt_3_1_2451_0 receipt_3_1_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_2_2450_0 : fastPhase (bank 0 2).shape 179808 2450 2 1 0 1 0 = 2905419997825181010787998 := p1 0 2 2450 2 1 0 1 0 283 2905419997825181010787998 [(128,2104604761924010176220544),(128,777925024296670286299130),(27,22890211604500548268324)] (by decide +kernel) (by decide +kernel)

private theorem receipt_0_2_2450_1 : fastPhase (bank 0 2).shape 179808 2450 2 1 0 1 1 = 2883198912501435130832144 := p1 0 2 2450 2 1 0 1 1 283 2883198912501435130832144 [(128,2093143772471674289595840),(128,768813484177316837442165),(27,21241655852444003794139)] (by decide +kernel) (by decide +kernel)

private theorem receipt_0_2_2451_0 : fastPhase (bank 0 2).shape 179808 2451 2 1 0 1 0 = 2905442268214258470387124 := p1 0 2 2451 2 1 0 1 0 283 2905442268214258470387124 [(128,2104622296537549821901344),(128,777929669074145346932902),(27,22890302602563301552878)] (by decide +kernel) (by decide +kernel)

private theorem receipt_0_2_2451_1 : fastPhase (bank 0 2).shape 179808 2451 2 1 0 1 1 = 2883221050460281566949148 := p1 0 2 2451 2 1 0 1 1 283 2883221050460281566949148 [(128,2093161227773810157848480),(128,768818082104295417830940),(27,21241740582175991269728)] (by decide +kernel) (by decide +kernel)

theorem receipt_0_2 : Checked (bank 0 2) 2 0 1 := by
  refine checked_from_values (bank 0 2) 2 0 1
    (P3_7_1.checked (bank 0 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1341_282)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_2_2450_0 receipt_0_2_2450_1 receipt_0_2_2451_0 receipt_0_2_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_2_2450_0 : fastPhase (bank 1 2).shape 179808 2450 2 1 0 2 0 = 2602659074636121270895721 := p1 1 2 2450 2 1 0 2 0 283 2602659074636121270895721 [(128,1888747151192135923167232),(128,693602753329592573846214),(27,20309170114392773882275)] (by decide +kernel) (by decide +kernel)

private theorem receipt_1_2_2450_1 : fastPhase (bank 1 2).shape 179808 2450 2 1 0 2 1 = 2582655622946931698212777 := p1 1 2 2450 2 1 0 2 1 283 2582655622946931698212777 [(128,1878362527870867826150400),(128,685447290482128291833724),(27,18845804593935580228653)] (by decide +kernel) (by decide +kernel)

private theorem receipt_1_2_2451_0 : fastPhase (bank 1 2).shape 179808 2451 2 1 0 2 0 = 2602679036294295813134810 := p1 1 2 2451 2 1 0 2 0 283 2602679036294295813134810 [(128,1888762889882590851826592),(128,693606895558832982577268),(27,20309250852871978730950)] (by decide +kernel) (by decide +kernel)

private theorem receipt_1_2_2451_1 : fastPhase (bank 1 2).shape 179808 2451 2 1 0 2 1 = 2582675465048145994720284 := p1 1 2 2451 2 1 0 2 1 283 2582675465048145994720284 [(128,1878378194544288770920800),(128,685451390735905425889184),(27,18845879767951797910300)] (by decide +kernel) (by decide +kernel)

theorem receipt_1_2 : Checked (bank 1 2) 2 0 2 := by
  refine checked_from_values (bank 1 2) 2 0 2
    (P3_7_1.checked (bank 1 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1341_282)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_2_2450_0 receipt_1_2_2450_1 receipt_1_2_2451_0 receipt_1_2_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_2_2450_0 : fastPhase (bank 2 2).shape 179808 2450 2 1 0 7 0 = 1356743172305881149632804 := p1 2 2 2450 2 1 0 7 0 283 1356743172305881149632804 [(128,997655141874017067338464),(128,349233521763416922297627),(27,9854508668447159996713)] (by decide +kernel) (by decide +kernel)

private theorem receipt_2_2_2450_1 : fastPhase (bank 2 2).shape 179808 2450 2 1 0 7 1 = 1345940974683545121748144 := p1 2 2 2450 2 1 0 7 1 283 1345940974683545121748144 [(128,991790341753074877555680),(128,345008757994681168748017),(27,9141874935789075444447)] (by decide +kernel) (by decide +kernel)

private theorem receipt_2_2_2451_0 : fastPhase (bank 2 2).shape 179808 2451 2 1 0 7 0 = 1356753623473017965092658 := p1 2 2 2451 2 1 0 7 0 283 1356753623473017965092658 [(128,997663464788812241975744),(128,349235610835314811181768),(27,9854547848890911935146)] (by decide +kernel) (by decide +kernel)

private theorem receipt_2_2_2451_1 : fastPhase (bank 2 2).shape 179808 2451 2 1 0 7 1 = 1345951359982392046588278 := p1 2 2 2451 2 1 0 7 1 283 1345951359982392046588278 [(128,991798623408778377602880),(128,345010825168226871692807),(27,9141911405386797292591)] (by decide +kernel) (by decide +kernel)

theorem receipt_2_2 : Checked (bank 2 2) 2 0 7 := by
  refine checked_from_values (bank 2 2) 2 0 7
    (P3_7_1.checked (bank 2 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1341_282)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_2_2450_0 receipt_2_2_2450_1 receipt_2_2_2451_0 receipt_2_2_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_2_2450_0 : fastPhase (bank 3 2).shape 179808 2450 2 1 1 1 0 = 246464801688321011213320 := p1 3 2 2450 2 1 1 1 0 223 246464801688321011213320 [(128,207390167058579301888224),(95,39074634629741709325096)] (by decide +kernel) (by decide +kernel)

private theorem receipt_3_2_2450_1 : fastPhase (bank 3 2).shape 179808 2450 2 1 1 1 1 = 244040553624933180101840 := p1 3 2 2450 2 1 1 1 1 223 244040553624933180101840 [(128,205823915285964662207584),(95,38216638338968517894256)] (by decide +kernel) (by decide +kernel)

private theorem receipt_3_2_2451_0 : fastPhase (bank 3 2).shape 179808 2451 2 1 1 1 0 = 246466457065758890735376 := p1 3 2 2451 2 1 1 1 0 223 246466457065758890735376 [(128,207391690344619162554816),(95,39074766721139728180560)] (by decide +kernel) (by decide +kernel)

private theorem receipt_3_2_2451_1 : fastPhase (bank 3 2).shape 179808 2451 2 1 1 1 1 = 244042193747712314693718 := p1 3 2 2451 2 1 1 1 1 223 244042193747712314693718 [(128,205825425994883279326144),(95,38216767752829035367574)] (by decide +kernel) (by decide +kernel)

theorem receipt_3_2 : Checked (bank 3 2) 2 1 1 := by
  refine checked_from_values (bank 3 2) 2 1 1
    (P3_7_1.checked (bank 3 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1047_222)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_2_2450_0 receipt_3_2_2450_1 receipt_3_2_2451_0 receipt_3_2_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_3_2450_0 : fastPhase (bank 0 3).shape 179808 2450 3 1 0 1 0 = 3369422433697493129528026 := p1 0 3 2450 3 1 0 1 0 282 3369422433697493129528026 [(128,2447200006864093614623552),(128,897457878566849741635473),(26,24764548266549773269001)] (by decide +kernel) (by decide +kernel)

private theorem receipt_0_3_2450_1 : fastPhase (bank 0 3).shape 179808 2450 3 1 0 1 1 = 3343543830467050981541577 := p1 0 3 2450 3 1 0 1 1 282 3343543830467050981541577 [(128,2433796388295598876891393),(128,886832111805506204327935),(26,22915330365945900322249)] (by decide +kernel) (by decide +kernel)

private theorem receipt_0_3_2451_0 : fastPhase (bank 0 3).shape 179808 2451 3 1 0 1 0 = 3369448345561305776197840 := p1 0 3 2451 3 1 0 1 0 282 3369448345561305776197840 [(128,2447220511432762617716730),(128,897463189976364592121303),(26,24764644152178566359807)] (by decide +kernel) (by decide +kernel)

private theorem receipt_0_3_2451_1 : fastPhase (bank 0 3).shape 179808 2451 3 1 0 1 1 = 3343569588586841147227146 := p1 0 3 2451 3 1 0 1 1 282 3343569588586841147227146 [(128,2433816799880619879512768),(128,886837369301287668000605),(26,22915419404933599713773)] (by decide +kernel) (by decide +kernel)

theorem receipt_0_3 : Checked (bank 0 3) 3 0 1 := by
  refine checked_from_values (bank 0 3) 3 0 1
    (P3_7_1.checked (bank 0 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1326_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_3_2450_0 receipt_0_3_2450_1 receipt_0_3_2451_0 receipt_0_3_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_3_2450_0 : fastPhase (bank 1 3).shape 179808 2450 3 1 0 2 0 = 3015350536495068477491247 := p1 1 3 2450 3 1 0 2 0 282 3015350536495068477491247 [(128,2193655529787315250523655),(128,799725343457777636369859),(26,21969663249975590597733)] (by decide +kernel) (by decide +kernel)

private theorem receipt_1_3_2450_1 : fastPhase (bank 1 3).shape 179808 2450 3 1 0 2 1 = 2992088076290665782324204 := p1 1 3 2450 3 1 0 2 1 282 2992088076290665782324204 [(128,2181535849831194252829008),(128,790223764442806087609605),(26,20328462016665441885591)] (by decide +kernel) (by decide +kernel)

private theorem receipt_1_3_2451_0 : fastPhase (bank 1 3).shape 179808 2451 3 1 0 2 0 = 3015373738482386003921624 := p1 1 3 2451 3 1 0 2 0 282 3015373738482386003921624 [(128,2193673912717584970529276),(128,799730077449636450084237),(26,21969748315164583308111)] (by decide +kernel) (by decide +kernel)

private theorem receipt_1_3_2451_1 : fastPhase (bank 1 3).shape 179808 2451 3 1 0 2 1 = 2992111139703851431506474 := p1 1 3 2451 3 1 0 2 1 282 2992111139703851431506474 [(128,2181554148517946494400604),(128,790228450180793914848333),(26,20328541005111022257537)] (by decide +kernel) (by decide +kernel)

theorem receipt_1_3 : Checked (bank 1 3) 3 0 2 := by
  refine checked_from_values (bank 1 3) 3 0 2
    (P3_7_1.checked (bank 1 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1326_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_3_2450_0 receipt_1_3_2450_1 receipt_1_3_2451_0 receipt_1_3_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_3_2450_0 : fastPhase (bank 2 3).shape 179808 2450 3 1 0 7 0 = 1558693285355873857789593 := p1 2 3 2450 3 1 0 7 0 282 1558693285355873857789593 [(128,1147585881122167861393509),(128,400469804949730172698968),(26,10637599283975823697116)] (by decide +kernel) (by decide +kernel)

private theorem receipt_2_3_2450_1 : fastPhase (bank 2 3).shape 179808 2450 3 1 0 7 1 = 1546274977332040078384503 := p1 2 3 2450 3 1 0 7 1 282 1546274977332040078384503 [(128,1140846135257789788055841),(128,395588423839399074815316),(26,9840418234851215513346)] (by decide +kernel) (by decide +kernel)

private theorem receipt_2_3_2451_0 : fastPhase (bank 2 3).shape 179808 2451 3 1 0 7 0 = 1558705328163563392510856 := p1 2 3 2451 3 1 0 7 0 282 1558705328163563392510856 [(128,1147595508445831181445884),(128,400472179241753024576970),(26,10637640475979186488002)] (by decide +kernel) (by decide +kernel)

private theorem receipt_2_3_2451_1 : fastPhase (bank 2 3).shape 179808 2451 3 1 0 7 1 = 1546286944751302630681860 := p1 2 3 2451 3 1 0 7 1 282 1546286944751302630681860 [(128,1140855715100997542082936),(128,395590773176119413828342),(26,9840456474185674770582)] (by decide +kernel) (by decide +kernel)

theorem receipt_2_3 : Checked (bank 2 3) 3 0 7 := by
  refine checked_from_values (bank 2 3) 3 0 7
    (P3_7_1.checked (bank 2 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1326_281)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_3_2450_0 receipt_2_3_2450_1 receipt_2_3_2451_0 receipt_2_3_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_3_2450_0 : fastPhase (bank 3 3).shape 179808 2450 3 1 1 1 0 = 373653625959017214083000 := p1 3 3 2450 3 1 1 1 0 238 373653625959017214083000 [(128,303316904612324350152000),(110,70336721346692863931000)] (by decide +kernel) (by decide +kernel)

private theorem receipt_3_3_2450_1 : fastPhase (bank 3 3).shape 179808 2450 3 1 1 1 1 = 370209102617489028128214 := p1 3 3 2450 3 1 1 1 1 238 370209102617489028128214 [(128,301212921261130803204864),(110,68996181356358224923350)] (by decide +kernel) (by decide +kernel)

private theorem receipt_3_3_2451_0 : fastPhase (bank 3 3).shape 179808 2451 3 1 1 1 0 = 373656126688995219447420 := p1 3 3 2451 3 1 1 1 0 238 373656126688995219447420 [(128,303319155250596582506880),(110,70336971438398636940540)] (by decide +kernel) (by decide +kernel)

private theorem receipt_3_3_2451_1 : fastPhase (bank 3 3).shape 179808 2451 3 1 1 1 1 = 370211581759935246325218 := p1 3 3 2451 3 1 1 1 1 238 370211581759935246325218 [(128,301215154707109455564096),(110,68996427052825790761122)] (by decide +kernel) (by decide +kernel)

theorem receipt_3_3 : Checked (bank 3 3) 3 1 1 := by
  refine checked_from_values (bank 3 3) 3 1 1
    (P3_7_1.checked (bank 3 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1117_237)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_3_2450_0 receipt_3_3_2450_1 receipt_3_3_2451_0 receipt_3_3_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_4_2450_0 : fastPhase (bank 0 4).shape 179808 2450 4 1 0 1 0 = 4690689735387176574138460 := p1 0 4 2450 4 1 0 1 0 292 4690689735387176574138460 [(128,3326721018107805747158858),(128,1302364137459359412978927),(36,61604579820011414000675)] (by decide +kernel) (by decide +kernel)

private theorem receipt_0_4_2450_1 : fastPhase (bank 0 4).shape 179808 2450 4 1 0 1 1 = 4655944017617320043296892 := p1 0 4 2450 4 1 0 1 1 292 4655944017617320043296892 [(128,3309314496931776394583173),(128,1288390508138871817246307),(36,58239012546671831467412)] (by decide +kernel) (by decide +kernel)

private theorem receipt_0_4_2451_0 : fastPhase (bank 0 4).shape 179808 2451 4 1 0 1 0 = 4690725683619929947326104 := p1 0 4 2451 4 1 0 1 0 292 4690725683619929947326104 [(128,3326748868986965839566856),(128,1302371984876947351468246),(36,61604829756016756291002)] (by decide +kernel) (by decide +kernel)

private theorem receipt_0_4_2451_1 : fastPhase (bank 0 4).shape 179808 2451 4 1 0 1 1 = 4655979759335875671061006 := p1 0 4 2451 4 1 0 1 1 292 4655979759335875671061006 [(128,3309342226832573091739673),(128,1288398282919994429882758),(36,58239249583308149438575)] (by decide +kernel) (by decide +kernel)

theorem receipt_0_4 : Checked (bank 0 4) 4 0 1 := by
  refine checked_from_values (bank 0 4) 4 0 1
    (P3_7_1.checked (bank 0 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1392_291)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_4_2450_0 receipt_0_4_2450_1 receipt_0_4_2451_0 receipt_0_4_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_4_2450_0 : fastPhase (bank 1 4).shape 179808 2450 4 1 0 2 0 = 4211375290938671526340986 := p1 1 4 2450 4 1 0 2 0 292 4211375290938671526340986 [(128,2991724242232568397328167),(128,1164784140405397655981667),(36,54866908300705473031152)] (by decide +kernel) (by decide +kernel)

private theorem receipt_1_4_2450_1 : fastPhase (bank 1 4).shape 179808 2450 4 1 0 2 1 = 4180047225762985068670194 := p1 1 4 2450 4 1 0 2 1 292 4180047225762985068670194 [(128,2975938573187831153718099),(128,1152240826471967192680011),(36,51867826103186722272084)] (by decide +kernel) (by decide +kernel)

private theorem receipt_1_4_2451_0 : fastPhase (bank 1 4).shape 179808 2451 4 1 0 2 0 = 4211407582871624139683366 := p1 1 4 2451 4 1 0 2 0 292 4211407582871624139683366 [(128,2991749291829694024959614),(128,1164791160136350469196073),(36,54867130905579645527679)] (by decide +kernel) (by decide +kernel)

private theorem receipt_1_4_2451_1 : fastPhase (bank 1 4).shape 179808 2451 4 1 0 2 1 = 4180079331024064877343026 := p1 1 4 2451 4 1 0 2 1 292 4180079331024064877343026 [(128,2975963512866309849568784),(128,1152247780945250525381055),(36,51868037212504502393187)] (by decide +kernel) (by decide +kernel)

theorem receipt_1_4 : Checked (bank 1 4) 4 0 2 := by
  refine checked_from_values (bank 1 4) 4 0 2
    (P3_7_1.checked (bank 1 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1392_291)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_4_2450_0 receipt_1_4_2450_1 receipt_1_4_2451_0 receipt_1_4_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_4_2450_0 : fastPhase (bank 2 4).shape 179808 2450 4 1 0 7 0 = 2226488519484543872431092 := p1 2 4 2450 4 1 0 7 0 292 2226488519484543872431092 [(128,1600514043848633093524482),(128,598639041365051864556291),(36,27335434270858914350319)] (by decide +kernel) (by decide +kernel)

private theorem receipt_2_4_2450_1 : fastPhase (bank 2 4).shape 179808 2450 4 1 0 7 1 = 2209414999736088576892260 := p1 2 4 2450 4 1 0 7 1 292 2209414999736088576892260 [(128,1591560878353214629670121),(128,592018870214053160061279),(36,25835251168820787160860)] (by decide +kernel) (by decide +kernel)

private theorem receipt_2_4_2451_0 : fastPhase (bank 2 4).shape 179808 2451 4 1 0 7 0 = 2226505656731020571161976 := p1 2 4 2451 4 1 0 7 0 292 2226505656731020571161976 [(128,1600527457466623063719704),(128,598642654072799156759082),(36,27335545191598350683190)] (by decide +kernel) (by decide +kernel)

private theorem receipt_2_4_2451_1 : fastPhase (bank 2 4).shape 179808 2451 4 1 0 7 1 = 2209432033445186635579118 := p1 2 4 2451 4 1 0 7 1 292 2209432033445186635579118 [(128,1591574228841688715279981),(128,592022448267283877028258),(36,25835356336214043270879)] (by decide +kernel) (by decide +kernel)

theorem receipt_2_4 : Checked (bank 2 4) 4 0 7 := by
  refine checked_from_values (bank 2 4) 4 0 7
    (P3_7_1.checked (bank 2 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1392_291)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_4_2450_0 receipt_2_4_2450_1 receipt_2_4_2451_0 receipt_2_4_2451_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_4_2450_0 : fastPhase (bank 3 4).shape 179808 2450 4 1 1 1 0 = 1142649012530228083491420 := p1 3 4 2450 4 1 1 1 0 303 1142649012530228083491420 [(128,798906066690045375104160),(128,321506792142243485643936),(47,22236153697939222743324)] (by decide +kernel) (by decide +kernel)

private theorem receipt_3_4_2450_1 : fastPhase (bank 3 4).shape 179808 2450 4 1 1 1 1 = 1134330185625342087192720 := p1 3 4 2450 4 1 1 1 1 303 1134330185625342087192720 [(128,794777247989150490022560),(128,318264625573080133485216),(47,21288312063111463684944)] (by decide +kernel) (by decide +kernel)

private theorem receipt_3_4_2451_0 : fastPhase (bank 3 4).shape 179808 2451 4 1 1 1 0 = 1142656551990451154693976 := p1 3 4 2451 4 1 1 1 0 303 1142656551990451154693976 [(128,798912207969019777562176),(128,321508152137580807124544),(47,22236191883850570007256)] (by decide +kernel) (by decide +kernel)

private theorem receipt_3_4_2451_1 : fastPhase (bank 3 4).shape 179808 2451 4 1 1 1 1 = 1134337673774125277948834 := p1 3 4 2451 4 1 1 1 1 303 1134337673774125277948834 [(128,794783353620757348405824),(128,318265971425282557055552),(47,21288348728085372487458)] (by decide +kernel) (by decide +kernel)

theorem receipt_3_4 : Checked (bank 3 4) 4 1 1 := by
  refine checked_from_values (bank 3 4) 4 1 1
    (P3_7_1.checked (bank 3 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1387_302)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_4_2450_0 receipt_3_4_2450_1 receipt_3_4_2451_0 receipt_3_4_2451_1 (by decide +kernel) (by decide +kernel)

def group1_stage (i : Fin 4) : Fin 17 :=
  ⟨1+i.val, by have := i.isLt; omega⟩

theorem group1_checked (rect : Fin 4) (i : Fin 4) :
    Checked (bank rect (group1_stage i)) (reserve (group1_stage i))
      (excess rect) (seed rect) := by
  fin_cases i
  · fin_cases rect
    · exact receipt_0_1
    · exact receipt_1_1
    · exact receipt_2_1
    · exact receipt_3_1
  · fin_cases rect
    · exact receipt_0_2
    · exact receipt_1_2
    · exact receipt_2_2
    · exact receipt_3_2
  · fin_cases rect
    · exact receipt_0_3
    · exact receipt_1_3
    · exact receipt_2_3
    · exact receipt_3_3
  · fin_cases rect
    · exact receipt_0_4
    · exact receipt_1_4
    · exact receipt_2_4
    · exact receipt_3_4

end Lower6961.Hi.RescueSource
