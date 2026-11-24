import ProximityPrize.SubmissionLower.R6960FreeSource
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
namespace Lower6960.FreeSource
open K1_14 (L)
open K1_14_1 (PoleData CRTLift evaluated)
open P1_7 (Bank debit)
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
open HelperSource (WidthGuard cutoffCount)
private def freeStages : List (ℕ × Bank) :=
  [
   (0,⟨⟨95,132,29,984⟩,27270840320,8956669⟩),
   (1,⟨⟨104,144,32,1074⟩,35837181952,12729182⟩),
   (2,⟨⟨101,140,31,1384⟩,32807845888,11360420⟩),
   (3,⟨⟨124,172,38,1243⟩,60131901440,25559185⟩),
   (4,⟨⟨118,164,36,1593⟩,51745914880,21071762⟩),
   (5,⟨⟨128,177,39,1665⟩,65782415360,28566713⟩),
   (7,⟨⟨158,219,48,1653⟩,122606059520,66089082⟩),
   (10,⟨⟨178,247,54,2036⟩,174543339520,106278128⟩),
   (16,⟨⟨214,297,67,2918⟩,309161623552,226287616⟩),
   (10,⟨⟨178,247,55,2006⟩,176946151424,107778015⟩),
   (20,⟨⟨250,347,78,3255⟩,490108092416,418829988⟩),
   (32,⟨⟨378,524,119,3993⟩,1694923489280,2177690453⟩),
   (31,⟨⟨345,478,108,4305⟩,1284701945856,1504282153⟩),
   (44,⟨⟨470,651,148,5322⟩,3250957582336,5176394869⟩),
   (73,⟨⟨749,1038,236,7729⟩,13115102855168,33302514887⟩),
   (76,⟨⟨722,1000,227,8859⟩,11730838618112,28660654832⟩),
   (103,⟨⟨1011,1401,318,10575⟩,32159926059008,110150758881⟩)
  ]
private def stage (i : Fin 17) : ℕ × Bank := freeStages.get ⟨i.val,i.isLt⟩
def reserve (i : Fin 17) : ℕ := (stage i).1
def bank (i : Fin 17) : Bank := (stage i).2
def cutoff (h : ℕ) (i : Fin 17) : ℕ :=
  cutoffCount (bank i).shape 179818 h (reserve i)-1
structure Checked (i : Fin 17) : Prop where
  debit_ok : P3_7_1.BankOK (bank i)
  reserve_ok : 2*(reserve i)≤(bank i).shape.B
  width_first : WidthGuard (bank i) 179818 2359 (reserve i)
  first : 0<compressedSurplus (bank i) 179818 2359 (reserve i)
  next : compressedSurplus (bank i) 179818 2359 (reserve i) ≤
    compressedSurplus (bank i) 179818 2360 (reserve i)
private theorem checked_from_values (i : Fin 17) (db : P3_7_1.BankOK (bank i))
    (res : 2*(reserve i)≤(bank i).shape.B)
    (width : WidthGuard (bank i) 179818 2359 (reserve i))
    {x y : ℤ} (first : compressedSurplus (bank i) 179818 2359 (reserve i) = x)
    (next : compressedSurplus (bank i) 179818 2360 (reserve i) = y)
    (pos : 0<x) (inc : x≤y) : Checked i := by
  refine ⟨db,res,width,?_,?_⟩
  · rwa [first]
  · rwa [first,next]
private theorem moment_0 : momentEstimate 132 29 = 8956669 := by
  refine moment_from_blocks
    [(128,8556490),(33,400179)] ?_ rfl rfl
  exact ⟨rfl,rfl,True.intro⟩
private theorem checked_0 : Checked 0 := by
  refine checked_from_values 0
    (P3_7_1.checked (bank 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_0)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 39105453480) (y := 147368479950) rfl rfl (by decide) (by decide)
private theorem moment_1 : momentEstimate 144 32 = 12729182 := by
  refine moment_from_blocks
    [(128,11505698),(48,1223484)] ?_ rfl rfl
  exact ⟨rfl,rfl,True.intro⟩
private theorem checked_1 : Checked 1 := by
  refine checked_from_values 1
    (P3_7_1.checked (bank 1) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 16080159600) (y := 179886010800) rfl rfl (by decide) (by decide)
private theorem moment_2 : momentEstimate 140 31 = 11360420 := by
  refine moment_from_blocks
    [(128,10480802),(43,879618)] ?_ rfl rfl
  exact ⟨rfl,rfl,True.intro⟩
private theorem checked_2 : Checked 2 := by
  refine checked_from_values 2
    (P3_7_1.checked (bank 2) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_2)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 45424332520) (y := 296921840000) rfl rfl (by decide) (by decide)
private theorem moment_3 : momentEstimate 172 38 = 25559185 := by
  refine moment_from_blocks
    [(128,19318585),(82,6240600)] ?_ rfl rfl
  exact ⟨rfl,rfl,True.intro⟩
private theorem checked_3 : Checked 3 := by
  refine checked_from_values 3
    (P3_7_1.checked (bank 3) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 38739721220) (y := 389499003070) rfl rfl (by decide) (by decide)
private theorem moment_4 : momentEstimate 164 36 = 21071762 := by
  refine moment_from_blocks
    [(128,16874923),(72,4196839)] ?_ rfl rfl
  exact ⟨rfl,rfl,True.intro⟩
private theorem checked_4 : Checked 4 := by
  refine checked_from_values 4
    (P3_7_1.checked (bank 4) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 4668194776) (y := 508683911040) rfl rfl (by decide) (by decide)
private theorem moment_5 : momentEstimate 177 39 = 28566713 := by
  refine moment_from_blocks
    [(128,20817690),(88,7749023)] ?_ rfl rfl
  exact ⟨rfl,rfl,True.intro⟩
private theorem checked_5 : Checked 5 := by
  refine checked_from_values 5
    (P3_7_1.checked (bank 5) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_5)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 19243192976) (y := 697293054500) rfl rfl (by decide) (by decide)
private theorem moment_6 : momentEstimate 219 48 = 66089082 := by
  refine moment_from_blocks
    [(128,34759620),(128,31294933),(11,34529)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,True.intro⟩
private theorem checked_6 : Checked 6 := by
  refine checked_from_values 6
    (P3_7_1.checked (bank 6) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_6)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 297300486056) (y := 1485042700850) rfl rfl (by decide) (by decide)
private theorem moment_7 : momentEstimate 247 54 = 106278128 := by
  refine moment_from_blocks
    [(128,44971630),(128,59409708),(45,1896790)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,True.intro⟩
private theorem checked_7 : Checked 7 := by
  refine checked_from_values 7
    (P3_7_1.checked (bank 7) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_7)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 216918156147) (y := 2721486326790) rfl rfl (by decide) (by decide)
private theorem moment_8 : momentEstimate 297 67 = 226287616 := by
  refine moment_from_blocks
    [(128,65190835),(128,134418307),(108,26678474)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,True.intro⟩
private theorem checked_8 : Checked 8 := by
  refine checked_from_values 8
    (P3_7_1.checked (bank 8) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_8)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 180054171528) (y := 9016997781960) rfl rfl (by decide) (by decide)
private theorem moment_9 : momentEstimate 247 55 = 107778015 := by
  refine moment_from_blocks
    [(128,45360574),(128,60399763),(46,2017678)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,True.intro⟩
private theorem checked_9 : Checked 9 := by
  refine checked_from_values 9
    (P3_7_1.checked (bank 9) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 425776215186) (y := 2895778916640) rfl rfl (by decide) (by decide)
private theorem moment_10 : momentEstimate 347 78 = 418829988 := by
  refine moment_from_blocks
    [(128,85234680),(128,227560448),(128,103935818),(41,2099042)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_10 : Checked 10 := by
  refine checked_from_values 10
    (P3_7_1.checked (bank 10) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_10)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 1185266248188) (y := 18152762832160) rfl rfl (by decide) (by decide)
private theorem moment_11 : momentEstimate 524 119 = 2177690453 := by
  refine moment_from_blocks
    [(128,153341750),(128,658287360),(128,798862080),(128,477441955),(128,89753646),(3,3662)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_11 : Checked 11 := by
  refine checked_from_values 11
    (P3_7_1.checked (bank 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_11)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 9823168495924) (y := 93350624269160) rfl rfl (by decide) (by decide)
private theorem moment_12 : momentEstimate 478 108 = 1504282153 := by
  refine moment_from_blocks
    [(128,136459825),(128,534570880),(128,570357888),(128,246975702),(74,15917858)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_12 : Checked 12 := by
  refine checked_from_values 12
    (P3_7_1.checked (bank 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_12)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 5666047301100) (y := 79843204090459) rfl rfl (by decide) (by decide)
private theorem moment_13 : momentEstimate 651 148 = 5176394869 := by
  refine moment_from_blocks
    [(128,198825120),(128,1013136261),(128,1532425664),(128,1427478906),(128,805738851),(128,196970451),(31,1819616)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_13 : Checked 13 := by
  refine checked_from_values 13
    (P3_7_1.checked (bank 13) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_13)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 14911338072722) (y := 292832097713812) rfl rfl (by decide) (by decide)
private theorem moment_14 : momentEstimate 1038 236 = 33302514887 := by
  refine moment_from_blocks
    [(128,337278240),(128,2057177553),(128,4372358016),(128,5878965120),(128,6391522176),(128,5910029184),(128,4481522406),(128,2652304705),(128,1067311419),(122,154046068)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_14 : Checked 14 := by
  refine checked_from_values 14
    (P3_7_1.checked (bank 14) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_14)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 118833819505000) (y := 2404987697168555) rfl rfl (by decide) (by decide)
private theorem moment_15 : momentEstimate 1000 227 = 28660654832 := by
  refine moment_from_blocks
    [(128,323683360),(128,1961263575),(128,4071116928),(128,5361750144),(128,5696082048),(128,5074112640),(128,3602477140),(128,1924849303),(128,609309184),(75,36010510)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_15 : Checked 15 := by
  refine checked_from_values 15
    (P3_7_1.checked (bank 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_15)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 111384553979680) (y := 2799099570337160) rfl rfl (by decide) (by decide)
private theorem moment_16 : momentEstimate 1401 318 = 110150758881 := by
  refine moment_from_blocks
    [(128,467145120),(128,2955305376),(128,7120936534),(128,11215447936),(128,14016849792),(128,15480268672),(128,15605704576),(128,14393157504),(128,11866159893),(128,8558093849),(128,5277857273),(128,2505173440),(128,667990464),(55,20668452)] ?_ rfl rfl
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem checked_16 : Checked 16 := by
  refine checked_from_values 16
    (P3_7_1.checked (bank 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_16)
    (by decide) (by unfold WidthGuard; decide +kernel)
    (x := 254959084826040) (y := 10579378014995976) rfl rfl (by decide) (by decide)
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
      (bank i).shape.B<K1.p ∧ (bank i).shape.U<K1.p ∧ (bank i).shape.m*179818<K1.p := by
  fin_cases i <;> decide +kernel
theorem free_width {h : ℕ} (lo : 2359≤h) (hi : h≤33579) (i : Fin 17) :
    WidthGuard (bank i) 179818 h (reserve i) :=
  HelperSource.width_at_height _ _ 2359 _ _ lo (by omega)
    (checked i).reserve_ok (checked i).width_first
theorem cutoff_fit {h : ℕ} (lo : 2359≤h) (hi : h≤33579) (i : Fin 17) :
    cutoff h i+2*h*(reserve i)<(bank i).shape.m*179818 :=
  buffered_fit _ _ _ _ (free_width lo hi i)
theorem free_rows {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2359≤h) (hi : h≤33579) (i : Fin 17) :
    ∃ P ∈ evaluated Crt word (bank i).shape (cutoff h i), P≠0 := by
  have c := checked i
  exact nonzero_row Crt word (bank i) 179818 (reserve i) (by omega) (by omega) c.debit_ok
    (free_width lo hi i) (rawGain_positive _ _ 2359 _ _ lo (by omega) c.first c.next)
#print axioms checked
#print axioms cutoff_fit
#print axioms free_rows
end Lower6960.FreeSource
