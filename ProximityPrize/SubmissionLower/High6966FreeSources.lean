import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Low48BentSupport
set_option Elab.async false

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
namespace Lower6960.Free6966
open FreeSource (compressedSurplus buffered_fit nonzero_row rawGain_positive)
open K1_14 (L)
open K1_14_1 (PoleData CRTLift evaluated)
open P1_7 (Bank debit)
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
open HelperSource (WidthGuard cutoffCount)
private def freeStages : List (ℕ × Bank) := [
  (0,⟨⟨98,136,30,1414⟩,29954146304,10105062⟩),
  (1,⟨⟨104,144,32,1645⟩,35837181952,12729182⟩),
  (2,⟨⟨113,157,35,1780⟩,46031437824,17945628⟩),
  (3,⟨⟨124,172,38,1859⟩,60131901440,25559185⟩),
  (4,⟨⟨133,185,41,1998⟩,74336174080,34174038⟩),
  (6,⟨⟨157,218,48,2125⟩,120884822016,65128192⟩),
  (9,⟨⟨193,267,60,2349⟩,226125676544,147822888⟩),
  (11,⟨⟨219,303,68,2497⟩,329140142080,244031460⟩),
  (16,⟨⟨262,363,82,3156⟩,564966981632,502963348⟩),
  (15,⟨⟨219,303,69,4044⟩,332742000640,246770858⟩),
  (17,⟨⟨227,314,71,4967⟩,368270376960,282799727⟩),
  (22,⟨⟨341,473,107,3615⟩,1242924318720,1443930128⟩),
  (31,⟨⟨345,478,108,7116⟩,1284701945856,1504282153⟩),
  (31,⟨⟨426,590,134,4694⟩,2421227520000,3494198079⟩),
  (73,⟨⟨616,854,193,28862⟩,7274458513408,15213890743⟩),
  (76,⟨⟨812,1126,254,10846⟩,16611521331200,45806632550⟩),
  (129,⟨⟨1055,1462,331,37976⟩,36467458965504,130334735922⟩)]
private def stage (i : Fin 17) : ℕ × Bank := freeStages.get ⟨i.val,i.isLt⟩
def reserve (i : Fin 17) : ℕ := (stage i).1
def bank (i : Fin 17) : Bank := (stage i).2
def cutoff (h : ℕ) (i : Fin 17) : ℕ :=
  cutoffCount (bank i).shape 179759 h (reserve i)-1
structure Checked (i : Fin 17) : Prop where
  debit_ok : P3_7_1.BankOK (bank i)
  reserve_ok : 2*(reserve i)≤(bank i).shape.B
  width_first : WidthGuard (bank i) 179759 2317 (reserve i)
  first : 0<compressedSurplus (bank i) 179759 2317 (reserve i)
  next : compressedSurplus (bank i) 179759 2317 (reserve i) ≤
    compressedSurplus (bank i) 179759 2318 (reserve i)
private theorem checked_from_values (i : Fin 17) (db : P3_7_1.BankOK (bank i))
    (res : 2*(reserve i)≤(bank i).shape.B)
    (width : WidthGuard (bank i) 179759 2317 (reserve i))
    {x y : ℤ} (first : compressedSurplus (bank i) 179759 2317 (reserve i) = x)
    (next : compressedSurplus (bank i) 179759 2318 (reserve i) = y)
    (pos : 0<x) (inc : x≤y) : Checked i := by
  refine ⟨db,res,width,?_,?_⟩
  · rwa [first]
  · rwa [first,next]
private theorem moment_0 : momentEstimate 136 30 = 10105062 := by
  refine moment_from_blocks [(128,9496875),(38,608187)] ?_ rfl rfl
  exact ⟨rfl,rfl,True.intro⟩
private theorem checked_0 : Checked 0 := by
  refine checked_from_values 0
    (P3_7_1.checked (bank 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_0)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 34149072300) (y := 290370174660) rfl rfl (by decide) (by decide)

private theorem moment_1 : momentEstimate 144 32 = 12729182 := by
  refine moment_from_blocks [(128,11505698),(48,1223484)] ?_ rfl rfl
  exact ⟨rfl,rfl,True.intro⟩
private theorem checked_1 : Checked 1 := by
  refine checked_from_values 1
    (P3_7_1.checked (bank 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 30987222358) (y := 437136999764) rfl rfl (by decide) (by decide)

private theorem moment_2 : momentEstimate 157 35 = 17945628 := by
  refine moment_from_blocks [(128,15022913),(64,2922715)] ?_ rfl rfl
  exact ⟨rfl,rfl,True.intro⟩
private theorem checked_2 : Checked 2 := by
  refine checked_from_values 2
    (P3_7_1.checked (bank 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 37922412684) (y := 639114849204) rfl rfl (by decide) (by decide)

private theorem moment_3 : momentEstimate 172 38 = 25559185 := by
  refine moment_from_blocks [(128,19318585),(82,6240600)] ?_ rfl rfl
  exact ⟨rfl,rfl,True.intro⟩
private theorem checked_3 : Checked 3 := by
  refine checked_from_values 3
    (P3_7_1.checked (bank 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 113524110480) (y := 944500451190) rfl rfl (by decide) (by decide)

private theorem moment_4 : momentEstimate 185 41 = 34174038 := by
  refine moment_from_blocks [(128,23412382),(98,10761656)] ?_ rfl rfl
  exact ⟨rfl,rfl,True.intro⟩
private theorem checked_4 : Checked 4 := by
  refine checked_from_values 4
    (P3_7_1.checked (bank 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 127124222092) (y := 1300884896168) rfl rfl (by decide) (by decide)

private theorem moment_5 : momentEstimate 218 48 = 65128192 := by
  refine moment_from_blocks [(128,34487180),(128,30614270),(10,26742)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,True.intro⟩
private theorem checked_5 : Checked 5 := by
  refine checked_from_values 5
    (P3_7_1.checked (bank 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 62645116751) (y := 2129462375962) rfl rfl (by decide) (by decide)

private theorem moment_6 : momentEstimate 267 60 = 147822888 := by
  refine moment_from_blocks [(128,53245619),(128,87146027),(71,7431242)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,True.intro⟩
private theorem checked_6 : Checked 6 := by
  refine checked_from_values 6
    (P3_7_1.checked (bank 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_6)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 595130435900) (y := 5107931776500) rfl rfl (by decide) (by decide)

private theorem moment_7 : momentEstimate 303 68 = 244031460 := by
  refine moment_from_blocks [(128,67468545),(128,144184647),(115,32378268)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,True.intro⟩
private theorem checked_7 : Checked 7 := by
  refine checked_from_values 7
    (P3_7_1.checked (bank 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_7)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 1079195352480) (y := 8336114606430) rfl rfl (by decide) (by decide)

private theorem moment_8 : momentEstimate 363 82 = 502963348 := by
  refine moment_from_blocks [(128,91785135),(128,261531008),(128,142833277),(61,6813928)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_8 : Checked 8 := by
  refine checked_from_values 8
    (P3_7_1.checked (bank 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_8)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 1237358131625) (y := 20661747147580) rfl rfl (by decide) (by decide)

private theorem moment_9 : momentEstimate 303 69 = 246770858 := by
  refine moment_from_blocks [(128,67814285),(128,145794628),(116,33161945)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,True.intro⟩
private theorem checked_9 : Checked 9 := by
  refine checked_from_values 9
    (P3_7_1.checked (bank 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 576235280460) (y := 19882181242290) rfl rfl (by decide) (by decide)

private theorem moment_10 : momentEstimate 314 71 = 282799727 := by
  refine moment_from_blocks [(128,72065658),(128,164702376),(128,46031379),(1,314)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_10 : Checked 10 := by
  refine checked_from_values 10
    (P3_7_1.checked (bank 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_10)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 269684700480) (y := 32228821417392) rfl rfl (by decide) (by decide)

private theorem moment_11 : momentEstimate 473 107 = 1443930128 := by
  refine moment_from_blocks [(128,134603685),(128,522039168),(128,547842897),(128,227089798),(68,12354580)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_11 : Checked 11 := by
  refine checked_from_values 11
    (P3_7_1.checked (bank 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_11)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 3362293868096) (y := 57690860917696) rfl rfl (by decide) (by decide)

private theorem moment_12 : momentEstimate 478 108 = 1504282153 := by
  refine moment_from_blocks [(128,136459825),(128,534570880),(128,570357888),(128,246975702),(74,15917858)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_12 : Checked 12 := by
  refine checked_from_values 12
    (P3_7_1.checked (bank 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_12)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 673505616003) (y := 217265362682236) rfl rfl (by decide) (by decide)

private theorem moment_13 : momentEstimate 590 134 = 3494198079 := by
  refine moment_from_blocks [(128,177001760),(128,840627655),(128,1161328320),(128,921571345),(128,364961726),(84,28707273)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_13 : Checked 13 := by
  refine checked_from_values 13
    (P3_7_1.checked (bank 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_13)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 10364189184630) (y := 184247737064820) rfl rfl (by decide) (by decide)

private theorem moment_14 : momentEstimate 854 193 = 15213890743 := by
  refine moment_from_blocks [(128,271450400),(128,1577914352),(128,2939183808),(128,3519259328),(128,3285639872),(128,2298770218),(128,1090014011),(128,230627552),(23,1031202)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_14 : Checked 14 := by
  refine checked_from_values 14
    (P3_7_1.checked (bank 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_14)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 28456951910166) (y := 19204888978466820) rfl rfl (by decide) (by decide)

private theorem moment_15 : momentEstimate 1126 254 = 45806632550 := by
  refine moment_from_blocks [(128,368761120),(128,2275698105),(128,5049163200),(128,7075454400),(128,8032198080),(128,7919394240),(128,6737830550),(128,4715520891),(128,2605388839),(128,933146400),(100,94076725)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_15 : Checked 15 := by
  refine checked_from_values 15
    (P3_7_1.checked (bank 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_15)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 162190860226780) (y := 6246596854014440) rfl rfl (by decide) (by decide)

private theorem moment_16 : momentEstimate 1462 331 = 130334735922 := by
  refine moment_from_blocks [(128,488968480),(128,3106054432),(128,7550991561),(128,12142732672),(128,15425463680),(128,17315685760),(128,17813398912),(128,16918603136),(128,14631977572),(128,11218824904),(128,7559774220),(128,4230263643),(128,1672330928),(128,259664560),(1,1462)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_16 : Checked 16 := by
  refine checked_from_values 16
    (P3_7_1.checked (bank 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_16)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 279934535648646) (y := 161923404554995086) rfl rfl (by decide) (by decide)

theorem checked (i : Fin 17) : Checked i := by
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
  · exact checked_12
  · exact checked_13
  · exact checked_14
  · exact checked_15
  · exact checked_16
theorem shape_guards (i : Fin 17) :
    0<(bank i).shape.J ∧ (bank i).shape.J≤(bank i).shape.B ∧
      (bank i).shape.B<K1.p ∧ (bank i).shape.U<K1.p ∧ (bank i).shape.m*179759<K1.p := by
  fin_cases i <;> decide +kernel
theorem free_width {h : ℕ} (lo : 2317≤h) (hi : h≤33697) (i : Fin 17) :
    WidthGuard (bank i) 179759 h (reserve i) :=
  HelperSource.width_at_height _ _ 2317 _ _ lo (by omega)
    (checked i).reserve_ok (checked i).width_first
theorem cutoff_fit {h : ℕ} (lo : 2317≤h) (hi : h≤33697) (i : Fin 17) :
    cutoff h i+2*h*(reserve i)<(bank i).shape.m*179759 :=
  buffered_fit _ _ _ _ (free_width lo hi i)
theorem free_rows {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2317≤h) (hi : h≤33697) (i : Fin 17) :
    ∃ P ∈ evaluated Crt word (bank i).shape (cutoff h i), P≠0 := by
  have c := checked i
  exact nonzero_row Crt word (bank i) 179759 (reserve i) (by omega) (by omega) c.debit_ok
    (free_width lo hi i) (rawGain_positive _ _ 2317 _ _ lo (by omega) c.first c.next)
#print axioms checked
#print axioms cutoff_fit
#print axioms free_rows
end Lower6960.Free6966
