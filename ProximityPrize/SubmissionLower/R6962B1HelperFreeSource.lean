import ProximityPrize.SubmissionLower.R6960PrefixReceipt
import ProximityPrize.SubmissionLower.R6960FreeSource
import ProximityPrize.SubmissionLower.R6960ExceptionalStage

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6962.B1
open Finset Polynomial
open K1_14 (FX L Jet Shape liftPoly)
open K1_14_1 (PoleData CRTLift evaluated evaluated_mono evaluated_shape MarkResidues nodeL)
open K1_14_2 (UsesSeed jetMarkHom toJet)
open K1_14_2_2_2_1 (seedDegree jetDegree jetDegree_le)
open P1_7 (Bank debit)
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
open Lower6960.HelperSource (WidthGuard cutoffCount compressedPhase surplus gain_eq_compressed
  surplus_positive width_at_height crt_avoiding_row crt_supply nonzero_of_supply)
open Lower6960.FreeSource (buffered_fit nonzero_row rawGain_positive)
open Lower6960.DifferentialContact (Native)
open Lower6960.PrefixRows (Prepared contact_of_crt prepare)

def helperBank : Bank := ⟨⟨350,485,106,6220⟩,1308168290304,1553662951⟩

theorem helper_bank_checked : P3_7_1.BankOK helperBank := by
  have moment : momentEstimate 485 106 = 1553662951 := by
    refine moment_from_blocks
      [(128,138794087),(128,542060288),(128,587644193),(128,265666823),(79,19497560)] ?_ rfl rfl
    exact ⟨rfl,rfl,rfl,rfl,rfl,True.intro⟩
  exact P3_7_1.checked helperBank rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) moment

inductive HelperTest where
  | twoSlopes | seedBoundary | mixedBoundary | jetBoundary

def HelperTest.slope : HelperTest → ℕ
  | .twoSlopes => 2
  | _ => 1

def HelperTest.excess : HelperTest → ℕ
  | .mixedBoundary => 1
  | .jetBoundary => 7
  | _ => 0

def HelperTest.seed : HelperTest → ℕ
  | .seedBoundary => 62
  | .mixedBoundary => 57
  | _ => 1

private def compressedSurplus (h : ℕ) (test : HelperTest) : ℤ :=
  (compressedPhase helperBank.shape 179808 h 10 test.slope test.excess test.seed 0 -
    compressedPhase helperBank.shape 179808 h 10 test.slope test.excess test.seed 1 : ℕ) - (debit h helperBank : ℤ)

private theorem compressedSurplus_eq (h : ℕ) (test : HelperTest) :
    compressedSurplus h test = surplus helperBank 179808 h 10 test.slope test.excess test.seed := by
  unfold compressedSurplus surplus
  rw [gain_eq_compressed _ _ _ _ _ _ _ (by cases test <;> decide)]

private theorem twoSlopes_first :
    compressedSurplus 2360 .twoSlopes = 539094775171 := by rfl
private theorem twoSlopes_next :
    compressedSurplus 2361 .twoSlopes = 158644813177779 := by rfl
private theorem seedBoundary_first :
    compressedSurplus 2360 .seedBoundary = 2131277018133616 := by rfl
private theorem seedBoundary_next :
    compressedSurplus 2361 .seedBoundary = 2290285565893869 := by rfl
private theorem mixedBoundary_first :
    compressedSurplus 2360 .mixedBoundary = 1845344712971731 := by rfl
private theorem mixedBoundary_next :
    compressedSurplus 2361 .mixedBoundary = 2004232128670185 := by rfl
private theorem jetBoundary_first :
    compressedSurplus 2360 .jetBoundary = 8236681693426691 := by rfl
private theorem jetBoundary_next :
    compressedSurplus 2361 .jetBoundary = 8398277302760931 := by rfl

theorem helper_surplus (test : HelperTest) {h : ℕ} (lo : 2360≤h) (hi : h≤2382) :
    debit h helperBank < Lower6960.HelperSource.gain helperBank.shape 179808 h 10 test.slope test.excess test.seed := by
  apply surplus_positive _ _ 2360 _ _ _ _ _ lo (by omega)
  · rw [← compressedSurplus_eq]
    cases test
    · rw [twoSlopes_first]; decide
    · rw [seedBoundary_first]; decide
    · rw [mixedBoundary_first]; decide
    · rw [jetBoundary_first]; decide
  · change surplus helperBank 179808 2360 10 test.slope test.excess test.seed ≤
      surplus helperBank 179808 2361 10 test.slope test.excess test.seed
    rw [← compressedSurplus_eq, ← compressedSurplus_eq]
    cases test
    · rw [twoSlopes_first, twoSlopes_next]; decide
    · rw [seedBoundary_first, seedBoundary_next]; decide
    · rw [mixedBoundary_first, mixedBoundary_next]; decide
    · rw [jetBoundary_first, jetBoundary_next]; decide

theorem helper_width {h : ℕ} (lo : 2360≤h) (hi : h≤2382) :
    WidthGuard helperBank 179808 h 10 :=
  width_at_height _ _ 2360 _ _ lo (by omega) (by decide) (by unfold WidthGuard; decide +kernel)

def helperCutoff (h : ℕ) : ℕ := cutoffCount helperBank.shape 179808 h 10 - 1

theorem helper_avoids {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2360≤h) (hi : h≤2382) (test : HelperTest) {G : Jet} (irr : Irreducible G)
    (seeded : UsesSeed G) (slope : test.slope≤G.natDegree) (seed : test.seed≤seedDegree G)
    (excess : G.natDegree+test.excess≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), ¬ G∣Q :=
  crt_avoiding_row Crt word helperBank 179808 10 test.slope test.excess test.seed
    (by omega) (by omega) (by cases test <;> decide)
    helper_bank_checked.nodes helper_bank_checked.moment.1 helper_bank_checked.moment.2
    (by decide) (helper_width lo hi) (helper_surplus test lo hi) irr seeded slope seed excess

theorem helper_nonzero {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2360≤h) (hi : h≤2382) :
    ∃ P ∈ evaluated Crt word helperBank.shape (helperCutoff h), P≠0 := by
  have sup := crt_supply Crt word helperBank 179808 10 2 0 1 (by omega) (by omega) (by decide)
    helper_bank_checked.nodes helper_bank_checked.moment.1 helper_bank_checked.moment.2
    (helper_width lo hi) (helper_surplus .twoSlopes lo hi)
  exact nonzero_of_supply Crt word helperBank.shape _ (lt_of_le_of_lt (Nat.zero_le _) sup)

private theorem shape_lower_bound {G : Jet} (nz : G≠0) : G.natDegree≤jetDegree G := by
  have coeff : ((G.coeff G.natDegree).coeff G.leadingCoeff.natDegree) ≠ 0 := by
    rw [coeff_natDegree, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr nz)
  have cap := (jetDegree_le G _).1 le_rfl _ _ coeff
  omega

theorem helper_common_caps {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2360≤h) (hi : h≤2382) {G : Jet} (irr : Irreducible G)
    (seeded : UsesSeed G) (slope : 0<G.natDegree)
    (common : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣Q) :
    G.natDegree=1 ∧ 1≤jetDegree G ∧ jetDegree G≤7 ∧
      1≤seedDegree G ∧ seedDegree G≤61 ∧ (2≤jetDegree G → seedDegree G≤56) := by
  have sb : 1≤seedDegree G := by
    obtain ⟨j,i,hs⟩ := seeded
    have ge := (K1_14_2_2_2_1.seedDegree_le G _).1 le_rfl j i
    omega
  have jb := shape_lower_bound irr.ne_zero
  have not_test (test : HelperTest) (a : test.slope≤G.natDegree)
      (b : test.seed≤seedDegree G) (c : G.natDegree+test.excess≤jetDegree G) : False := by
    obtain ⟨Q,hQ,avoid⟩ := helper_avoids Crt word lo hi test irr seeded a b c
    exact avoid (common Q hQ)
  have linear : G.natDegree=1 := by
    by_contra! bad
    exact not_test .twoSlopes (by change 2≤G.natDegree; omega) sb (by simpa [HelperTest.excess] using jb)
  refine ⟨linear, by omega, ?_, sb, ?_, ?_⟩
  · by_contra! bad
    exact not_test .jetBoundary (by change 1≤G.natDegree; omega) sb
      (by change G.natDegree+7≤jetDegree G; omega)
  · by_contra! bad
    exact not_test .seedBoundary (by change 1≤G.natDegree; omega) (by change 62≤seedDegree G; omega)
      (by simpa [HelperTest.excess] using jb)
  · intro j
    by_contra! bad
    exact not_test .mixedBoundary (by change 1≤G.natDegree; omega) (by change 57≤seedDegree G; omega)
      (by change G.natDegree+1≤jetDegree G; omega)

theorem helper_not_two {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2360≤h) (hi : h≤2382) {G H : Jet} (g : Irreducible G) (i : Irreducible H)
    (cop : IsRelPrime G H) (gs : 0<G.natDegree) (hs : 0<H.natDegree)
    (gu : UsesSeed G) (hu : UsesSeed H)
    (allG : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣Q)
    (allH : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), H∣Q) : False := by
  have supply := crt_supply Crt word helperBank 179808 10 2 0 1 (by omega) (by omega) (by decide)
    helper_bank_checked.nodes helper_bank_checked.moment.1 helper_bank_checked.moment.2
    (helper_width lo hi) (helper_surplus .twoSlopes lo hi)
  obtain ⟨P,hP,np⟩ := helper_nonzero Crt word lo hi
  have hpc (j i : ℕ) : ((P.coeff j).coeff i).totalDegree ≤ helperBank.shape.U := by
    by_cases zero : ((P.coeff j).coeff i)=0
    · simp [zero]
    · exact (evaluated_shape Crt word hP j i zero).2.2
  exact Lower6960.HelperPrefix.not_two_common helperBank.shape h (cutoffCount helperBank.shape 179808 h 10)
    (by omega) (evaluated Crt word helperBank.shape) G H P g i cop gs hs gu hu np hP
    (by decide) hpc (fun _ _ _ hR => evaluated_shape Crt word hR)
    (fun W _ R hR hnR => P0_10_1.leading_bound (by omega) (by omega) Crt word helperBank.shape W R hR hnR)
    (fun _ _ _ hR j a hshift => evaluated_mono Crt word rfl rfl rfl le_rfl hshift
      (P0_10_1.evaluated_shift Crt word hR j a))
    supply allG allH

private def freeStages : List (ℕ × Bank) :=
  [
   (0,⟨⟨93,129,29,1046⟩,26012549120,8323789⟩),
   (1,⟨⟨100,139,31,1175⟩,32090619904,11103604⟩),
   (2,⟨⟨114,158,35,1202⟩,46942126080,18313194⟩),
   (3,⟨⟨124,171,38,1305⟩,60131901440,25087376⟩),
   (5,⟨⟨140,195,44,1518⟩,87797268480,42666368⟩),
   (8,⟨⟨164,228,51,1837⟩,139361517568,78737869⟩),
   (13,⟨⟨218,302,68,2205⟩,325793873920,241457300⟩),
   (21,⟨⟨268,373,84,3308⟩,605096509440,559058208⟩),
   (34,⟨⟨560,776,175,3690⟩,5458855198720,10364868560⟩),
   (55,⟨⟨596,825,186,6229⟩,6570814210048,13230254227⟩),
   (90,⟨⟨842,1172,265,10720⟩,18603382669312,53845789320⟩),
   (150,⟨⟨1043,1451,328,66313⟩,35301094850560,126309788863⟩)
  ]

private def stage (i : Fin 12) : ℕ × Bank := freeStages.get ⟨i.val, i.isLt⟩
def reserve (i : Fin 12) : ℕ := (stage i).1
def bank (i : Fin 12) : Bank := (stage i).2
def cutoff (h : ℕ) (i : Fin 12) : ℕ := cutoffCount (bank i).shape 179808 h (reserve i) - 1

structure FreeChecked (i : Fin 12) : Prop where
  debit_ok : P3_7_1.BankOK (bank i)
  reserve_ok : 2*(reserve i)≤(bank i).shape.B
  width_first : WidthGuard (bank i) 179808 2360 (reserve i)
  first : 0<Lower6960.FreeSource.compressedSurplus (bank i) 179808 2360 (reserve i)
  next : Lower6960.FreeSource.compressedSurplus (bank i) 179808 2360 (reserve i) ≤
    Lower6960.FreeSource.compressedSurplus (bank i) 179808 2361 (reserve i)

private theorem free_checked_from_values (i : Fin 12) (db : P3_7_1.BankOK (bank i))
    (res : 2*(reserve i)≤(bank i).shape.B)
    (width : WidthGuard (bank i) 179808 2360 (reserve i))
    {x y : ℤ} (first : Lower6960.FreeSource.compressedSurplus (bank i) 179808 2360 (reserve i) = x)
    (next : Lower6960.FreeSource.compressedSurplus (bank i) 179808 2361 (reserve i) = y)
    (pos : 0<x) (inc : x≤y) : FreeChecked i := by
  refine ⟨db,res,width,?_,?_⟩
  · rwa [first]
  · rwa [first,next]

private theorem moment_0 : momentEstimate 129 29 = 8323789 := by
  refine moment_from_blocks
    [(128,8023257),(30,300532)] ?_ rfl rfl
  exact ⟨rfl,rfl,True.intro⟩
private theorem checked_0 : FreeChecked 0 := by
  refine free_checked_from_values 0
    (P3_7_1.checked (bank 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_0)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 35553083700) (y := 153903013254) rfl rfl (by decide) (by decide)
private theorem moment_1 : momentEstimate 139 31 = 11103604 := by
  refine moment_from_blocks
    [(128,10285015),(42,818589)] ?_ rfl rfl
  exact ⟨rfl,rfl,True.intro⟩
private theorem checked_1 : FreeChecked 1 := by
  refine free_checked_from_values 1
    (P3_7_1.checked (bank 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 25050634560) (y := 205472582784) rfl rfl (by decide) (by decide)
private theorem moment_2 : momentEstimate 158 35 = 18313194 := by
  refine moment_from_blocks
    [(128,15245787),(65,3067407)] ?_ rfl rfl
  exact ⟨rfl,rfl,True.intro⟩
private theorem checked_2 : FreeChecked 2 := by
  refine free_checked_from_values 2
    (P3_7_1.checked (bank 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 48055740552) (y := 311549999868) rfl rfl (by decide) (by decide)
private theorem moment_3 : momentEstimate 171 38 = 25087376 := by
  refine moment_from_blocks
    [(128,19082310),(81,6005066)] ?_ rfl rfl
  exact ⟨rfl,rfl,True.intro⟩
private theorem checked_3 : FreeChecked 3 := by
  refine free_checked_from_values 3
    (P3_7_1.checked (bank 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 42523232012) (y := 428133802203) rfl rfl (by decide) (by decide)
private theorem moment_4 : momentEstimate 195 44 = 42666368 := by
  refine moment_from_blocks
    [(128,26945415),(111,15720953)] ?_ rfl rfl
  exact ⟨rfl,rfl,True.intro⟩
private theorem checked_4 : FreeChecked 4 := by
  refine free_checked_from_values 4
    (P3_7_1.checked (bank 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 48288766960) (y := 804654863376) rfl rfl (by decide) (by decide)
private theorem moment_5 : momentEstimate 228 51 = 78737869 := by
  refine moment_from_blocks
    [(128,38382539),(128,40089100),(23,266230)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,True.intro⟩
private theorem checked_5 : FreeChecked 5 := by
  refine free_checked_from_values 5
    (P3_7_1.checked (bank 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 346674028132) (y := 2027990431788) rfl rfl (by decide) (by decide)
private theorem moment_6 : momentEstimate 302 68 = 241457300 := by
  refine moment_from_blocks
    [(128,67146775),(128,142807856),(114,31502669)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,True.intro⟩
private theorem checked_6 : FreeChecked 6 := by
  refine free_checked_from_values 6
    (P3_7_1.checked (bank 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_6)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 935086124115) (y := 6252510189132) rfl rfl (by decide) (by decide)
private theorem moment_7 : momentEstimate 373 84 = 559058208 := by
  refine moment_from_blocks
    [(128,95728105),(128,282341440),(128,169295835),(73,11692828)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_7 : FreeChecked 7 := by
  refine free_checked_from_values 7
    (P3_7_1.checked (bank 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_7)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 1423609445685) (y := 23160658631016) rfl rfl (by decide) (by decide)
private theorem moment_8 : momentEstimate 776 175 = 10364868560 := by
  refine moment_from_blocks
    [(128,243545120),(128,1362856556),(128,2365423104),(128,2640805376),(128,2180397062),(128,1210301310),(128,350260330),(55,11279702)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_8 : FreeChecked 8 := by
  refine free_checked_from_values 8
    (P3_7_1.checked (bank 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_8)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 2339208986784) (y := 225041925575904) rfl rfl (by decide) (by decide)
private theorem moment_9 : momentEstimate 825 186 = 13230254227 := by
  refine moment_from_blocks
    [(128,261075360),(128,1498288895),(128,2719991296),(128,3179562496),(128,2854798848),(128,1852729730),(128,762130557),(115,101677045)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_9 : FreeChecked 9 := by
  refine free_checked_from_values 9
    (P3_7_1.checked (bank 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 41099089162075) (y := 799472291779455) rfl rfl (by decide) (by decide)
private theorem moment_10 : momentEstimate 1172 265 = 53845789320 := by
  refine moment_from_blocks
    [(128,385218080),(128,2389378592),(128,5410498638),(128,7748533184),(128,8970992576),(128,9077767104),(128,8068856768),(128,6048311854),(128,3710476989),(128,1671082835),(128,361937328),(29,2735372)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_10 : FreeChecked 10 := by
  refine free_checked_from_values 10
    (P3_7_1.checked (bank 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_10)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 58103334848208) (y := 6370836642088056) rfl rfl (by decide) (by decide)
private theorem moment_11 : momentEstimate 1451 328 = 126309788863 := by
  refine moment_from_blocks
    [(128,485033120),(128,3078870176),(128,7472924814),(128,11965303616),(128,15150992192),(128,16956754752),(128,17382591296),(128,16428501824),(128,14096252401),(128,10693275874),(128,7099708260),(128,3870202767),(128,1445227104),(115,184150667)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_11 : FreeChecked 11 := by
  refine free_checked_from_values 11
    (P3_7_1.checked (bank 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_11)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 281394190623790) (y := 453129043689911076) rfl rfl (by decide) (by decide)

theorem free_checked (i : Fin 12) : FreeChecked i := by
  fin_cases i
  · exact checked_0
  · exact checked_1
  · exact checked_2
  · exact checked_3
  · exact checked_4
  · exact checked_5
  · exact checked_6
  · exact checked_7
  · exact checked_8
  · exact checked_9
  · exact checked_10
  · exact checked_11

theorem free_shape_guards (i : Fin 12) :
    0<(bank i).shape.J ∧ (bank i).shape.J≤(bank i).shape.B ∧
      (bank i).shape.B<K1.p ∧ (bank i).shape.U<K1.p ∧ (bank i).shape.m*179808<K1.p := by
  fin_cases i <;> decide +kernel

theorem free_width {h : ℕ} (lo : 2360≤h) (hi : h≤2382) (i : Fin 12) :
    WidthGuard (bank i) 179808 h (reserve i) :=
  width_at_height _ _ 2360 _ _ lo (by omega)
    (free_checked i).reserve_ok (free_checked i).width_first

theorem free_cutoff_fit {h : ℕ} (lo : 2360≤h) (hi : h≤2382) (i : Fin 12) :
    cutoff h i+2*h*(reserve i)<(bank i).shape.m*179808 :=
  buffered_fit _ _ _ _ (free_width lo hi i)

theorem free_rows {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2360≤h) (hi : h≤2382) (i : Fin 12) :
    ∃ P ∈ evaluated Crt word (bank i).shape (cutoff h i), P≠0 := by
  have c := free_checked i
  exact nonzero_row Crt word (bank i) 179808 (reserve i) (by omega) (by omega) c.debit_ok
    (free_width lo hi i) (rawGain_positive _ _ 2360 _ _ lo (by omega) c.first c.next)

def copies (i : Fin 12) : ℕ := (reserve i + 11) / 11

def b1RescueDegrees (G : Jet) : Prop :=
  G.natDegree=1 ∧
    ((jetDegree G=1 ∧ seedDegree G=1) ∨
     (jetDegree G=1 ∧ 2≤seedDegree G ∧ seedDegree G≤6) ∨
     (jetDegree G=1 ∧ 7≤seedDegree G ∧ seedDegree G≤61) ∨
     (2≤jetDegree G ∧ jetDegree G≤7 ∧ 1≤seedDegree G ∧ seedDegree G≤56))

noncomputable section

theorem prepare_b1 {ι : Type*} [Fintype ι] (P : ι→Jet) (s : ι→Shape) (ks : ι→ℕ)
    (proper : ∀ i,P i≠0) (caps : ∀ i,K1_14_2_2.RowCaps (P i) (s i))
    {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I→L)
    (lo : 2360≤h) (hi : h≤2382) :
    let V := evaluated Crt word helperBank.shape (helperCutoff h)
    ∃ out : Prepared P s ks V helperBank.shape, out.exception=1 ∨ b1RescueDegrees out.exception := by
  obtain ⟨out⟩ := prepare P s ks _ helperBank.shape proper caps
    (helper_nonzero Crt word lo hi) (fun _ inside=>evaluated_shape Crt word inside)
    (fun _ _ g i cop=>helper_not_two Crt word lo hi g.1 i.1 cop g.2.1 i.2.1 g.2.2.1
      i.2.2.1 g.2.2.2 i.2.2.2)
  refine ⟨out,out.kind.imp_right ?_⟩
  intro g
  obtain ⟨slope,b0,b1,u0,u1,mixed⟩ :=
    helper_common_caps Crt word lo hi g.1 g.2.2.1 g.2.1 g.2.2.2
  unfold b1RescueDegrees
  omega

theorem native_at_b1 {ι : Type*} {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I→L)
    (lo : 2360≤h) (hi : h≤2382) {P : ι→Jet} {s : ι→Shape} {ks : ι→ℕ}
    (out : Prepared P s ks (evaluated Crt word helperBank.shape (helperCutoff h)) helperBank.shape)
    (i : ι) (W r : ℕ) (inside : P i∈evaluated Crt word (s i) W)
    (width : W+2*h*r<(s i).m*179808) (power : r+1≤ks i*11)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (z : K1.K) (S : (Polynomial K1.K)) (residues : MarkResidues D z S)
    (degree : (liftPoly S).natDegree ≤ 131071+h)
    (hits : Finset K1.I) (many : 179808≤hits.card)
    (agree : ∀ i ∈ hits, (liftPoly S).eval (nodeL i) = word i)
    (regular : toJet out.exception∉RingHom.ker (jetMarkHom z S)) :
    Native (RingHom.ker (jetMarkHom z S)) (r+1) (out.free i) ∧
    Native (RingHom.ker (jetMarkHom z S)) (r+1) (out.helper^(ks i)) := by
  apply out.contacts i _ (RingHom.ker_isPrime _) regular (r+1) 11 power
  · exact contact_of_crt Crt word (s i) _ inside width noPole z S residues degree hits many agree
  · intro H member
    have wh := helper_width lo hi
    unfold WidthGuard cutoffCount at wh
    have fit : helperCutoff h + 2*h*10 < helperBank.shape.m*179808 := by
      unfold helperCutoff cutoffCount
      omega
    exact contact_of_crt Crt word helperBank.shape H member fit noPole z S residues degree hits many agree

theorem main_rows {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I→L)
    (lo : 2360≤h) (hi : h≤2382) :
    ∃ (P : Fin 12→Jet) (out : Prepared P (fun i=>(bank i).shape) copies
          (evaluated Crt word helperBank.shape (helperCutoff h)) helperBank.shape),
      (out.exception=1 ∨ b1RescueDegrees out.exception) ∧
      (∀ i,P i∈evaluated Crt word (bank i).shape (cutoff h i)) ∧
      ∀ (_noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
        (z : K1.K) (S : (Polynomial K1.K)), MarkResidues D z S →
        (liftPoly S).natDegree ≤ 131071+h →
        ∀ hits : Finset K1.I, 179808≤hits.card →
        (∀ i ∈ hits,(liftPoly S).eval (nodeL i)=word i) →
        toJet out.exception∉RingHom.ker (jetMarkHom z S) →
        ∀ i, Native (RingHom.ker (jetMarkHom z S)) (reserve i+1) (out.free i) ∧
          Native (RingHom.ker (jetMarkHom z S)) (reserve i+1) (out.helper^(copies i)) := by
  choose P inside nz using free_rows Crt word lo hi
  obtain ⟨out,kind⟩ := prepare_b1 P (fun i=>(bank i).shape) copies nz
    (fun i=>evaluated_shape Crt word (inside i)) Crt word lo hi
  refine ⟨P,out,kind,inside,?_⟩
  intro noPole z S residues degree hits many agree regular i
  apply native_at_b1 Crt word lo hi out i (cutoff h i) (reserve i) (inside i)
  · exact free_cutoff_fit lo hi i
  · unfold copies
    omega
  all_goals assumption

end

#print axioms helper_common_caps
#print axioms free_rows
#print axioms main_rows
end Lower6962.B1
