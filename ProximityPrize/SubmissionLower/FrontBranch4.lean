import ProximityPrize.SubmissionLower.UpperBranch2
set_option Elab.async false
set_option autoImplicit true
section
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 900000
namespace P1_4
open P1 Finset
open K1_11 (V J)
open private countRow gradeRow count grade contactRow V_affine rational_fee from ProximityPrize.SubmissionLower.PortFrontA
private theorem dims_5_16_10 : count 5 16 10 = 2982 ∧ grade 5 16 10 = 9324 := by
  constructor
  · have r0 : countRow 5 16 10 0 = 867 := by decide
    have r1:countRow 5 16 10 1=720:=by decide
    have r2:countRow 5 16 10 2=570:=by decide
    have r3:countRow 5 16 10 3=420:=by decide
    have r4:countRow 5 16 10 4=273:=by decide
    have r5:countRow 5 16 10 5=132:=by decide
    simp only [count,sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,r5,zero_add]
  · change (∑ i ∈ range 6, gradeRow 5 16 10 i) = 9324
    have r0:gradeRow 5 16 10 0=1870:=by decide
    have r1:gradeRow 5 16 10 1=2000:=by decide
    have r2:gradeRow 5 16 10 2=1920:=by decide
    have r3:gradeRow 5 16 10 3=1652:=by decide
    have r4:gradeRow 5 16 10 4=1222:=by decide
    have r5:gradeRow 5 16 10 5=660:=by decide
    simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,r5,zero_add]
private theorem dims_4_15_8 : count 4 15 8 = 1675 ∧ grade 4 15 8 = 4189 := by
  constructor
  · have r0 : countRow 4 15 8 0 = 560 := by decide
    have r1:countRow 4 15 8 1=450:=by decide
    have r2:countRow 4 15 8 2=336:=by decide
    have r3:countRow 4 15 8 3=221:=by decide
    have r4:countRow 4 15 8 4=108:=by decide
    simp only [count,sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,zero_add]
  · change (∑ i ∈ range 5, gradeRow 4 15 8 i) = 4189
    have r0:gradeRow 4 15 8 0=960:=by decide
    have r1:gradeRow 4 15 8 1=1050:=by decide
    have r2:gradeRow 4 15 8 2=980:=by decide
    have r3:gradeRow 4 15 8 3=767:=by decide
    have r4:gradeRow 4 15 8 4=432:=by decide
    simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,zero_add]
private theorem jets_4_16_10 : J 4 16 10 = 3326 := by
  change (∑ i ∈ range 4,contactRow 4 16 10 i)=3326
  have r0:contactRow 4 16 10 0=1700:=by decide
  have r1:contactRow 4 16 10 1=992:=by decide
  have r2:contactRow 4 16 10 2=480:=by decide
  have r3:contactRow 4 16 10 3=154:=by decide
  simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,zero_add]
private theorem jets_3_15_8 : J 3 15 8 = 1316 := by
  change (∑ i ∈ range 3,contactRow 3 15 8 i)=1316
  have r0:contactRow 3 15 8 0=800:=by decide
  have r1:contactRow 3 15 8 1=390:=by decide
  have r2:contactRow 3 15 8 2=126:=by decide
  simp only [sum_range_succ,sum_range_zero,r0,r1,r2,zero_add]
private theorem dims_5_8_7 : count 5 8 7 = 952 ∧ grade 5 8 7 = 2814 := by
  constructor
  · have r0 : countRow 5 8 7 0 = 297 := by decide
    have r1:countRow 5 8 7 1=240:=by decide
    have r2:countRow 5 8 7 2=182:=by decide
    have r3:countRow 5 8 7 3=126:=by decide
    have r4:countRow 5 8 7 4=75:=by decide
    have r5:countRow 5 8 7 5=32:=by decide
    simp only [count,sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,r5,zero_add]
  · change (∑ i ∈ range 6, gradeRow 5 8 7 i) = 2814
    have r0:gradeRow 5 8 7 0=585:=by decide
    have r1:gradeRow 5 8 7 1=640:=by decide
    have r2:gradeRow 5 8 7 2=602:=by decide
    have r3:gradeRow 5 8 7 3=492:=by decide
    have r4:gradeRow 5 8 7 4=335:=by decide
    have r5:gradeRow 5 8 7 5=160:=by decide
    simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,r5,zero_add]
private theorem dims_4_7_4 : count 4 7 4 = 355 ∧ grade 4 7 4 = 809 := by
  constructor
  · have r0 : countRow 4 7 4 0 = 120 := by decide
    have r1:countRow 4 7 4 1=98:=by decide
    have r2:countRow 4 7 4 2=72:=by decide
    have r3:countRow 4 7 4 3=45:=by decide
    have r4:countRow 4 7 4 4=20:=by decide
    simp only [count,sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,zero_add]
  · change (∑ i ∈ range 5, gradeRow 4 7 4 i) = 809
    have r0:gradeRow 4 7 4 0=160:=by decide
    have r1:gradeRow 4 7 4 1=210:=by decide
    have r2:gradeRow 4 7 4 2=204:=by decide
    have r3:gradeRow 4 7 4 3=155:=by decide
    have r4:gradeRow 4 7 4 4=80:=by decide
    simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,zero_add]
private theorem jets_4_8_7 : J 4 8 7 = 1191 := by
  change (∑ i ∈ range 4,contactRow 4 8 7 i)=1191
  have r0:contactRow 4 8 7 0=630:=by decide
  have r1:contactRow 4 8 7 1=352:=by decide
  have r2:contactRow 4 8 7 2=161:=by decide
  have r3:contactRow 4 8 7 3=48:=by decide
  simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,zero_add]
private theorem jets_3_7_4 : J 3 7 4 = 336 := by
  change (∑ i ∈ range 3,contactRow 3 7 4 i)=336
  have r0:contactRow 3 7 4 0=208:=by decide
  have r1:contactRow 3 7 4 1=98:=by decide
  have r2:contactRow 3 7 4 2=30:=by decide
  simp only [sum_range_succ,sum_range_zero,r0,r1,r2,zero_add]
private theorem dims_5_10_16 : count 5 10 16 = 2982 ∧ grade 5 10 16 = 9324 := by
  constructor
  · have r0 : countRow 5 10 16 0 = 957 := by decide
    have r1:countRow 5 10 16 1=750:=by decide
    have r2:countRow 5 10 16 2=558:=by decide
    have r3:countRow 5 10 16 3=384:=by decide
    have r4:countRow 5 10 16 4=231:=by decide
    have r5:countRow 5 10 16 5=102:=by decide
    simp only [count,sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,r5,zero_add]
  · change (∑ i ∈ range 6, gradeRow 5 10 16 i) = 9324
    have r0:gradeRow 5 10 16 0=2200:=by decide
    have r1:gradeRow 5 10 16 1=2150:=by decide
    have r2:gradeRow 5 10 16 2=1908:=by decide
    have r3:gradeRow 5 10 16 3=1520:=by decide
    have r4:gradeRow 5 10 16 4=1036:=by decide
    have r5:gradeRow 5 10 16 5=510:=by decide
    simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,r5,zero_add]
private theorem dims_4_8_15 : count 4 8 15 = 1675 ∧ grade 4 8 15 = 4189 := by
  constructor
  · have r0 : countRow 4 8 15 0 = 630 := by decide
    have r1:countRow 4 8 15 1=464:=by decide
    have r2:countRow 4 8 15 2=315:=by decide
    have r3:countRow 4 8 15 3=186:=by decide
    have r4:countRow 4 8 15 4=80:=by decide
    simp only [count,sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,zero_add]
  · change (∑ i ∈ range 5, gradeRow 4 8 15 i) = 4189
    have r0:gradeRow 4 8 15 0=1170:=by decide
    have r1:gradeRow 4 8 15 1=1120:=by decide
    have r2:gradeRow 4 8 15 2=931:=by decide
    have r3:gradeRow 4 8 15 3=648:=by decide
    have r4:gradeRow 4 8 15 4=320:=by decide
    simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,zero_add]
private theorem jets_4_10_16 : J 4 10 16 = 3326 := by
  change (∑ i ∈ range 4,contactRow 4 10 16 i)=3326
  have r0:contactRow 4 10 16 0=1760:=by decide
  have r1:contactRow 4 10 16 1=980:=by decide
  have r2:contactRow 4 10 16 2=450:=by decide
  have r3:contactRow 4 10 16 3=136:=by decide
  simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,zero_add]
private theorem jets_3_8_15 : J 3 8 15 = 1316 := by
  change (∑ i ∈ range 3,contactRow 3 8 15 i)=1316
  have r0:contactRow 3 8 15 0=828:=by decide
  have r1:contactRow 3 8 15 1=376:=by decide
  have r2:contactRow 3 8 15 2=112:=by decide
  simp only [sum_range_succ,sum_range_zero,r0,r1,r2,zero_add]
private theorem dims_5_11_10 : count 5 11 10 = 2002 ∧ grade 5 11 10 = 6174 := by
  constructor
  · have r0 : countRow 5 11 10 0 = 612 := by decide
    have r1:countRow 5 11 10 1=495:=by decide
    have r2:countRow 5 11 10 2=380:=by decide
    have r3:countRow 5 11 10 3=270:=by decide
    have r4:countRow 5 11 10 4=168:=by decide
    have r5:countRow 5 11 10 5=77:=by decide
    simp only [count,sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,r5,zero_add]
  · change (∑ i ∈ range 6, gradeRow 5 11 10 i) = 6174
    have r0:gradeRow 5 11 10 0=1320:=by decide
    have r1:gradeRow 5 11 10 1=1375:=by decide
    have r2:gradeRow 5 11 10 2=1280:=by decide
    have r3:gradeRow 5 11 10 3=1062:=by decide
    have r4:gradeRow 5 11 10 4=752:=by decide
    have r5:gradeRow 5 11 10 5=385:=by decide
    simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,r5,zero_add]
private theorem dims_4_9_8 : count 4 9 8 = 985 ∧ grade 4 9 8 = 2419 := by
  constructor
  · have r0 : countRow 4 9 8 0 = 350 := by decide
    have r1:countRow 4 9 8 1=270:=by decide
    have r2:countRow 4 9 8 2=192:=by decide
    have r3:countRow 4 9 8 3=119:=by decide
    have r4:countRow 4 9 8 4=54:=by decide
    simp only [count,sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,zero_add]
  · change (∑ i ∈ range 5, gradeRow 4 9 8 i) = 2419
    have r0:gradeRow 4 9 8 0=600:=by decide
    have r1:gradeRow 4 9 8 1=630:=by decide
    have r2:gradeRow 4 9 8 2=560:=by decide
    have r3:gradeRow 4 9 8 3=413:=by decide
    have r4:gradeRow 4 9 8 4=216:=by decide
    simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,zero_add]
private theorem jets_4_11_10 : J 4 11 10 = 2301 := by
  change (∑ i ∈ range 4,contactRow 4 11 10 i)=2301
  have r0:contactRow 4 11 10 0=1200:=by decide
  have r1:contactRow 4 11 10 1=682:=by decide
  have r2:contactRow 4 11 10 2=320:=by decide
  have r3:contactRow 4 11 10 3=99:=by decide
  simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,zero_add]
private theorem jets_3_9_8 : J 3 9 8 = 806 := by
  change (∑ i ∈ range 3,contactRow 3 9 8 i)=806
  have r0:contactRow 3 9 8 0=500:=by decide
  have r1:contactRow 3 9 8 1=234:=by decide
  have r2:contactRow 3 9 8 2=72:=by decide
  simp only [sum_range_succ,sum_range_zero,r0,r1,r2,zero_add]
private theorem dims_5_8_6 : count 5 8 6 = 798 ∧ grade 5 8 6 = 2324 := by
  constructor
  · have r0 : countRow 5 8 6 0 = 243 := by decide
    have r1:countRow 5 8 6 1=200:=by decide
    have r2:countRow 5 8 6 2=154:=by decide
    have r3:countRow 5 8 6 3=108:=by decide
    have r4:countRow 5 8 6 4=65:=by decide
    have r5:countRow 5 8 6 5=28:=by decide
    simp only [count,sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,r5,zero_add]
  · change (∑ i ∈ range 6, gradeRow 5 8 6 i) = 2324
    have r0:gradeRow 5 8 6 0=450:=by decide
    have r1:gradeRow 5 8 6 1=520:=by decide
    have r2:gradeRow 5 8 6 2=504:=by decide
    have r3:gradeRow 5 8 6 3=420:=by decide
    have r4:gradeRow 5 8 6 4=290:=by decide
    have r5:gradeRow 5 8 6 5=140:=by decide
    simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,r5,zero_add]
private theorem dims_4_6_3 : count 4 6 3 = 215 ∧ grade 4 6 3 = 459 := by
  constructor
  · have r0 : countRow 4 6 3 0 = 70 := by decide
    have r1:countRow 4 6 3 1=60:=by decide
    have r2:countRow 4 6 3 2=45:=by decide
    have r3:countRow 4 6 3 3=28:=by decide
    have r4:countRow 4 6 3 4=12:=by decide
    simp only [count,sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,zero_add]
  · change (∑ i ∈ range 5, gradeRow 4 6 3 i) = 459
    have r0:gradeRow 4 6 3 0=70:=by decide
    have r1:gradeRow 4 6 3 1=120:=by decide
    have r2:gradeRow 4 6 3 2=125:=by decide
    have r3:gradeRow 4 6 3 3=96:=by decide
    have r4:gradeRow 4 6 3 4=48:=by decide
    simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,zero_add]
private theorem jets_4_8_6 : J 4 8 6 = 1026 := by
  change (∑ i ∈ range 4,contactRow 4 8 6 i)=1026
  have r0:contactRow 4 8 6 0=540:=by decide
  have r1:contactRow 4 8 6 1=304:=by decide
  have r2:contactRow 4 8 6 2=140:=by decide
  have r3:contactRow 4 8 6 3=42:=by decide
  simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,zero_add]
private theorem jets_3_6_3 : J 3 6 3 = 226 := by
  change (∑ i ∈ range 3,contactRow 3 6 3 i)=226
  have r0:contactRow 3 6 3 0=140:=by decide
  have r1:contactRow 3 6 3 1=66:=by decide
  have r2:contactRow 3 6 3 2=20:=by decide
  simp only [sum_range_succ,sum_range_zero,r0,r1,r2,zero_add]
private theorem dims_5_7_8 : count 5 7 8 = 952 ∧ grade 5 7 8 = 2814 := by
  constructor
  · have r0 : countRow 5 7 8 0 = 312 := by decide
    have r1:countRow 5 7 8 1=245:=by decide
    have r2:countRow 5 7 8 2=180:=by decide
    have r3:countRow 5 7 8 3=120:=by decide
    have r4:countRow 5 7 8 4=68:=by decide
    have r5:countRow 5 7 8 5=27:=by decide
    simp only [count,sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,r5,zero_add]
  · change (∑ i ∈ range 6, gradeRow 5 7 8 i) = 2814
    have r0:gradeRow 5 7 8 0=640:=by decide
    have r1:gradeRow 5 7 8 1=665:=by decide
    have r2:gradeRow 5 7 8 2=600:=by decide
    have r3:gradeRow 5 7 8 3=470:=by decide
    have r4:gradeRow 5 7 8 4=304:=by decide
    have r5:gradeRow 5 7 8 5=135:=by decide
    simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,r5,zero_add]
private theorem dims_4_4_7 : count 4 4 7 = 355 ∧ grade 4 4 7 = 809 := by
  constructor
  · have r0 : countRow 4 4 7 0 = 150 := by decide
    have r1:countRow 4 4 7 1=104:=by decide
    have r2:countRow 4 4 7 2=63:=by decide
    have r3:countRow 4 4 7 3=30:=by decide
    have r4:countRow 4 4 7 4=8:=by decide
    simp only [count,sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,zero_add]
  · change (∑ i ∈ range 5, gradeRow 4 4 7 i) = 809
    have r0:gradeRow 4 4 7 0=250:=by decide
    have r1:gradeRow 4 4 7 1=240:=by decide
    have r2:gradeRow 4 4 7 2=183:=by decide
    have r3:gradeRow 4 4 7 3=104:=by decide
    have r4:gradeRow 4 4 7 4=32:=by decide
    simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,zero_add]
private theorem jets_4_7_8 : J 4 7 8 = 1191 := by
  change (∑ i ∈ range 4,contactRow 4 7 8 i)=1191
  have r0:contactRow 4 7 8 0=640:=by decide
  have r1:contactRow 4 7 8 1=350:=by decide
  have r2:contactRow 4 7 8 2=156:=by decide
  have r3:contactRow 4 7 8 3=45:=by decide
  simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,zero_add]
private theorem jets_3_4_7 : J 3 4 7 = 336 := by
  change (∑ i ∈ range 3,contactRow 3 4 7 i)=336
  have r0:contactRow 3 4 7 0=220:=by decide
  have r1:contactRow 3 4 7 1=92:=by decide
  have r2:contactRow 3 4 7 2=24:=by decide
  simp only [sum_range_succ,sum_range_zero,r0,r1,r2,zero_add]
private theorem dims_5_6_8 : count 5 6 8 = 798 ∧ grade 5 6 8 = 2324 := by
  constructor
  · have r0 : countRow 5 6 8 0 = 273 := by decide
    have r1:countRow 5 6 8 1=210:=by decide
    have r2:countRow 5 6 8 2=150:=by decide
    have r3:countRow 5 6 8 3=96:=by decide
    have r4:countRow 5 6 8 4=51:=by decide
    have r5:countRow 5 6 8 5=18:=by decide
    simp only [count,sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,r5,zero_add]
  · change (∑ i ∈ range 6, gradeRow 5 6 8 i) = 2324
    have r0:gradeRow 5 6 8 0=560:=by decide
    have r1:gradeRow 5 6 8 1=570:=by decide
    have r2:gradeRow 5 6 8 2=500:=by decide
    have r3:gradeRow 5 6 8 3=376:=by decide
    have r4:gradeRow 5 6 8 4=228:=by decide
    have r5:gradeRow 5 6 8 5=90:=by decide
    simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,r5,zero_add]
private theorem dims_4_3_6 : count 4 3 6 = 215 ∧ grade 4 3 6 = 459 := by
  constructor
  · have r0 : countRow 4 3 6 0 = 100 := by decide
    have r1:countRow 4 3 6 1=66:=by decide
    have r2:countRow 4 3 6 2=36:=by decide
    have r3:countRow 4 3 6 3=13:=by decide
    have r4:countRow 4 3 6 4=0:=by decide
    simp only [count,sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,zero_add]
  · change (∑ i ∈ range 5, gradeRow 4 3 6 i) = 459
    have r0:gradeRow 4 3 6 0=160:=by decide
    have r1:gradeRow 4 3 6 1=150:=by decide
    have r2:gradeRow 4 3 6 2=104:=by decide
    have r3:gradeRow 4 3 6 3=45:=by decide
    have r4:gradeRow 4 3 6 4=0:=by decide
    simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,zero_add]
private theorem jets_4_6_8 : J 4 6 8 = 1026 := by
  change (∑ i ∈ range 4,contactRow 4 6 8 i)=1026
  have r0:contactRow 4 6 8 0=560:=by decide
  have r1:contactRow 4 6 8 1=300:=by decide
  have r2:contactRow 4 6 8 2=130:=by decide
  have r3:contactRow 4 6 8 3=36:=by decide
  simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,zero_add]
private theorem jets_3_3_6 : J 3 3 6 = 226 := by
  change (∑ i ∈ range 3,contactRow 3 3 6 i)=226
  have r0:contactRow 3 3 6 0=152:=by decide
  have r1:contactRow 3 3 6 1=60:=by decide
  have r2:contactRow 3 3 6 2=14:=by decide
  simp only [sum_range_succ,sum_range_zero,r0,r1,r2,zero_add]
private theorem dims_4_3_5 : count 4 3 5 = 175 ∧ grade 4 3 5 = 364 := by
  constructor
  · have r0 : countRow 4 3 5 0 = 80 := by decide
    have r1:countRow 4 3 5 1=54:=by decide
    have r2:countRow 4 3 5 2=30:=by decide
    have r3:countRow 4 3 5 3=11:=by decide
    have r4:countRow 4 3 5 4=0:=by decide
    simp only [count,sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,zero_add]
  · change (∑ i ∈ range 5, gradeRow 4 3 5 i) = 364
    have r0:gradeRow 4 3 5 0=120:=by decide
    have r1:gradeRow 4 3 5 1=120:=by decide
    have r2:gradeRow 4 3 5 2=86:=by decide
    have r3:gradeRow 4 3 5 3=38:=by decide
    have r4:gradeRow 4 3 5 4=0:=by decide
    simp only [sum_range_succ,sum_range_zero,r0,r1,r2,r3,r4,zero_add]
private theorem jets_3_3_5 : J 3 3 5 = 191 := by
  change (∑ i ∈ range 3,contactRow 3 3 5 i)=191
  have r0:contactRow 3 3 5 0=128:=by decide
  have r1:contactRow 3 3 5 1=51:=by decide
  have r2:contactRow 3 3 5 2=12:=by decide
  simp only [sum_range_succ,sum_range_zero,r0,r1,r2,zero_add]
end P1_4
end
