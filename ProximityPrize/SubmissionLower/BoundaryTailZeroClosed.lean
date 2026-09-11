import ProximityPrize.SubmissionLower.BoundaryTailStrictData

/-!
Closed form for the `zero` table.

For each row `R`, `zero R V` is exactly a quadratic in `V` once `V0 R ≤ V`,
in the falling-factorial basis so every coefficient is a natural number:

    zero R V = qa R * (V * (V-1)) + qb R * V + qc R      (V0 R ≤ V)

Below `V0 R` the remaining 99 values are listed in `zeroHead`; outside the
admissible region (`R = 0`, `30 < R`, `139 < R + V`) the table is `0`.
For `R ≥ 3` the coefficients are themselves polynomial in `R`:
`qa` linear, `qb` quadratic, `qc` cubic.
-/

namespace ProximityPrize.SubmissionLower.BoundaryTailZeroClosed
open ProximityPrize.SubmissionLower.BoundaryTailStrictData
set_option autoImplicit false
set_option maxRecDepth 4000

def qa : ℕ → ℕ
  | 1 => 206160003072
  | 2 => 274880004096
  | 3 => 326426361913
  | 4 => 455278526539
  | 5 => 584130691165
  | 6 => 712982855791
  | 7 => 841835020417
  | 8 => 970687185043
  | 9 => 1099539349669
  | 10 => 1228391514295
  | 11 => 1357243678921
  | 12 => 1486095843547
  | 13 => 1614948008173
  | 14 => 1743800172799
  | 15 => 1872652337425
  | 16 => 2001504502051
  | 17 => 2130356666677
  | 18 => 2259208831303
  | 19 => 2388060995929
  | 20 => 2516913160555
  | 21 => 2645765325181
  | 22 => 2774617489807
  | 23 => 2903469654433
  | 24 => 3032321819059
  | 25 => 3161173983685
  | 26 => 3290026148311
  | 27 => 3418878312937
  | 28 => 3547730477563
  | 29 => 3676582642189
  | 30 => 3805434806815
  | _ => 0

def qb : ℕ → ℕ
  | 1 => 137441050628
  | 2 => 618481582086
  | 3 => 987877212404
  | 4 => 1829715050894
  | 5 => 2929257218636
  | 6 => 4286503715630
  | 7 => 5901454541876
  | 8 => 7774109697374
  | 9 => 9904469182124
  | 10 => 12292532996126
  | 11 => 14938301139380
  | 12 => 17841773611886
  | 13 => 21002950413644
  | 14 => 24421831544654
  | 15 => 28098417004916
  | 16 => 32032706794430
  | 17 => 36224700913196
  | 18 => 40674399361214
  | 19 => 45381802138484
  | 20 => 50346909245006
  | 21 => 55569720680780
  | 22 => 61050236445806
  | 23 => 66788456540084
  | 24 => 72784380963614
  | 25 => 79038009716396
  | 26 => 85549342798430
  | 27 => 92318380209716
  | 28 => 99345121950254
  | 29 => 106629568020044
  | 30 => 114171718419086
  | _ => 0

def qc : ℕ → ℕ
  | 1 => 1
  | 2 => 137441050630
  | 3 => 515420848320
  | 4 => 1511889043900
  | 5 => 3350195077970
  | 6 => 6288043279782
  | 7 => 10583137978588
  | 8 => 16493183503640
  | 9 => 24275884184190
  | 10 => 34188944349490
  | 11 => 46490068328792
  | 12 => 61436960451348
  | 13 => 79287325046410
  | 14 => 100298866443230
  | 15 => 124729288971060
  | 16 => 152836296959152
  | 17 => 184877594736758
  | 18 => 221110886633130
  | 19 => 261793876977520
  | 20 => 307184270099180
  | 21 => 357539770327362
  | 22 => 413118081991318
  | 23 => 474176909420300
  | 24 => 540973956943560
  | 25 => 613766928890350
  | 26 => 692813529589922
  | 27 => 778371463371528
  | 28 => 870698434564420
  | 29 => 970052147497850
  | 30 => 1076690306501070
  | _ => 0

def qV0 : ℕ → ℕ
  | 1 => 2
  | 2 => 1
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | 7 => 2
  | 8 => 2
  | 9 => 2
  | 10 => 2
  | 11 => 2
  | 12 => 3
  | 13 => 3
  | 14 => 3
  | 15 => 3
  | 16 => 3
  | 17 => 3
  | 18 => 4
  | 19 => 4
  | 20 => 4
  | 21 => 4
  | 22 => 4
  | 23 => 4
  | 24 => 5
  | 25 => 5
  | 26 => 5
  | 27 => 5
  | 28 => 5
  | 29 => 5
  | 30 => 6
  | _ => 0

/-- Quadratic body, valid for `V0 R ≤ V`. -/
def zeroQ (R V : ℕ) : ℕ := qa R * (V * (V - 1)) + qb R * V + qc R

/-- The 99 head values, for `V < V0 R`. -/
def zeroHead : ℕ → ℕ → ℕ
  | 1, 0 => 274881052677
  | 1, 1 => 481041580039
  | 2, 0 => 549762105354
  | 3, 0 => 1855444746261
  | 3, 1 => 2405205803033
  | 4, 0 => 4398088454180
  | 4, 1 => 5428890042410
  | 5, 0 => 8590013235255
  | 5, 1 => 10239295356991
  | 6, 0 => 14843539095630
  | 6, 1 => 17248741752920
  | 7, 0 => 23570986041449
  | 7, 1 => 26869549236341
  | 8, 0 => 35184674078856
  | 8, 1 => 39514037813398
  | 9, 0 => 50096923213995
  | 9, 1 => 55594527490235
  | 10, 0 => 68720053453010
  | 10, 1 => 75523338272996
  | 11, 0 => 91466384802045
  | 11, 1 => 99712790167825
  | 12, 0 => 118748237267244
  | 12, 1 => 128575203180866
  | 12, 2 => 100193831747864
  | 13, 0 => 150977930854751
  | 13, 1 => 162522897318263
  | 13, 2 => 129056244760905
  | 14, 0 => 188567785570710
  | 14, 1 => 201968192586160
  | 14, 2 => 163003938898302
  | 15, 0 => 231930121421265
  | 15, 1 => 247323408990701
  | 15, 2 => 202449234166199
  | 16, 0 => 281477258412560
  | 16, 1 => 299000866538030
  | 16, 2 => 247804450570740
  | 17, 0 => 337621516550739
  | 17, 1 => 357412885234291
  | 17, 2 => 299481908118069
  | 18, 0 => 400775215841946
  | 18, 1 => 422971785085628
  | 18, 2 => 357893926814330
  | 18, 3 => 358100087341692
  | 19, 0 => 471350676292325
  | 19, 1 => 496089886098185
  | 19, 2 => 423452826665667
  | 19, 3 => 423658987193029
  | 20, 0 => 549760217908020
  | 20, 1 => 577179508278106
  | 20, 2 => 496570927678224
  | 20, 3 => 496777088205586
  | 21, 0 => 636416160695175
  | 21, 1 => 666652971631535
  | 21, 2 => 577660549858145
  | 21, 3 => 577866710385507
  | 22, 0 => 731730824659934
  | 22, 1 => 764922596164616
  | 22, 2 => 667134013211574
  | 22, 3 => 667340173738936
  | 23, 0 => 836116529808441
  | 23, 1 => 872400701883493
  | 23, 2 => 765403637744655
  | 23, 3 => 765609798272017
  | 24, 0 => 949985596146840
  | 24, 1 => 989499608794310
  | 24, 2 => 872881743463532
  | 24, 3 => 873087903990894
  | 24, 4 => 874049985053810
  | 25, 0 => 1073750343681275
  | 25, 1 => 1116631636903211
  | 25, 2 => 989980650374349
  | 25, 3 => 990186810901711
  | 25, 4 => 991148891964627
  | 26, 0 => 1207823092417890
  | 26, 1 => 1254209106216340
  | 26, 2 => 1117112678483250
  | 26, 3 => 1117318839010612
  | 26, 4 => 1118280920073528
  | 27, 0 => 1352616162362829
  | 27, 1 => 1402644336739841
  | 27, 2 => 1254690147796379
  | 27, 3 => 1254896308323741
  | 27, 4 => 1255858389386657
  | 28, 0 => 1508541873522236
  | 28, 1 => 1562349648479858
  | 28, 2 => 1403125378319880
  | 28, 3 => 1403331538847242
  | 28, 4 => 1404293619910158
  | 29, 0 => 1676012545902255
  | 29, 1 => 1733737361442535
  | 29, 2 => 1562830690059897
  | 29, 3 => 1563036850587259
  | 29, 4 => 1563998931650175
  | 30, 0 => 1855440499509030
  | 30, 1 => 1917219795634016
  | 30, 2 => 1734218403022574
  | 30, 3 => 1734424563549936
  | 30, 4 => 1735386644612852
  | 30, 5 => 1736761045681912
  | _, _ => 0

/-- Closed form, agreeing with `zero` on every input. -/
def zeroClosed (R V : ℕ) : ℕ :=
  if 1 ≤ R ∧ R ≤ 30 ∧ R + V ≤ 139 then
    (if V < qV0 R then zeroHead R V else zeroQ R V)
  else 0

theorem zero_eq_closed_r1 : ∀ V ∈ List.range 140, zero 1 V = zeroClosed 1 V := by
  decide +kernel

theorem zero_eq_closed_r2 : ∀ V ∈ List.range 139, zero 2 V = zeroClosed 2 V := by
  decide +kernel

theorem zero_eq_closed_r3 : ∀ V ∈ List.range 138, zero 3 V = zeroClosed 3 V := by
  decide +kernel

theorem zero_eq_closed_r4 : ∀ V ∈ List.range 137, zero 4 V = zeroClosed 4 V := by
  decide +kernel

theorem zero_eq_closed_r5 : ∀ V ∈ List.range 136, zero 5 V = zeroClosed 5 V := by
  decide +kernel

theorem zero_eq_closed_r6 : ∀ V ∈ List.range 135, zero 6 V = zeroClosed 6 V := by
  decide +kernel

theorem zero_eq_closed_r7 : ∀ V ∈ List.range 134, zero 7 V = zeroClosed 7 V := by
  decide +kernel

theorem zero_eq_closed_r8 : ∀ V ∈ List.range 133, zero 8 V = zeroClosed 8 V := by
  decide +kernel

theorem zero_eq_closed_r9 : ∀ V ∈ List.range 132, zero 9 V = zeroClosed 9 V := by
  decide +kernel

theorem zero_eq_closed_r10 : ∀ V ∈ List.range 131, zero 10 V = zeroClosed 10 V := by
  decide +kernel

theorem zero_eq_closed_r11 : ∀ V ∈ List.range 130, zero 11 V = zeroClosed 11 V := by
  decide +kernel

theorem zero_eq_closed_r12 : ∀ V ∈ List.range 129, zero 12 V = zeroClosed 12 V := by
  decide +kernel

theorem zero_eq_closed_r13 : ∀ V ∈ List.range 128, zero 13 V = zeroClosed 13 V := by
  decide +kernel

theorem zero_eq_closed_r14 : ∀ V ∈ List.range 127, zero 14 V = zeroClosed 14 V := by
  decide +kernel

theorem zero_eq_closed_r15 : ∀ V ∈ List.range 126, zero 15 V = zeroClosed 15 V := by
  decide +kernel

theorem zero_eq_closed_r16 : ∀ V ∈ List.range 125, zero 16 V = zeroClosed 16 V := by
  decide +kernel

theorem zero_eq_closed_r17 : ∀ V ∈ List.range 124, zero 17 V = zeroClosed 17 V := by
  decide +kernel

theorem zero_eq_closed_r18 : ∀ V ∈ List.range 123, zero 18 V = zeroClosed 18 V := by
  decide +kernel

theorem zero_eq_closed_r19 : ∀ V ∈ List.range 122, zero 19 V = zeroClosed 19 V := by
  decide +kernel

theorem zero_eq_closed_r20 : ∀ V ∈ List.range 121, zero 20 V = zeroClosed 20 V := by
  decide +kernel

theorem zero_eq_closed_r21 : ∀ V ∈ List.range 120, zero 21 V = zeroClosed 21 V := by
  decide +kernel

theorem zero_eq_closed_r22 : ∀ V ∈ List.range 119, zero 22 V = zeroClosed 22 V := by
  decide +kernel

theorem zero_eq_closed_r23 : ∀ V ∈ List.range 118, zero 23 V = zeroClosed 23 V := by
  decide +kernel

theorem zero_eq_closed_r24 : ∀ V ∈ List.range 117, zero 24 V = zeroClosed 24 V := by
  decide +kernel

theorem zero_eq_closed_r25 : ∀ V ∈ List.range 116, zero 25 V = zeroClosed 25 V := by
  decide +kernel

theorem zero_eq_closed_r26 : ∀ V ∈ List.range 115, zero 26 V = zeroClosed 26 V := by
  decide +kernel

theorem zero_eq_closed_r27 : ∀ V ∈ List.range 114, zero 27 V = zeroClosed 27 V := by
  decide +kernel

theorem zero_eq_closed_r28 : ∀ V ∈ List.range 113, zero 28 V = zeroClosed 28 V := by
  decide +kernel

theorem zero_eq_closed_r29 : ∀ V ∈ List.range 112, zero 29 V = zeroClosed 29 V := by
  decide +kernel

theorem zero_eq_closed_r30 : ∀ V ∈ List.range 111, zero 30 V = zeroClosed 30 V := by
  decide +kernel

theorem zeroRow1_large (i : ℕ) (h : 139 ≤ i) : zeroRow1 i = 0 := by
  unfold zeroRow1
  rw [if_neg (by omega)]

theorem zeroRow2_large (i : ℕ) (h : 138 ≤ i) : zeroRow2 i = 0 := by
  unfold zeroRow2
  rw [if_neg (by omega)]

theorem zeroRow3_large (i : ℕ) (h : 137 ≤ i) : zeroRow3 i = 0 := by
  unfold zeroRow3
  rw [if_neg (by omega)]

theorem zeroRow4_large (i : ℕ) (h : 136 ≤ i) : zeroRow4 i = 0 := by
  unfold zeroRow4
  rw [if_neg (by omega)]

theorem zeroRow5_large (i : ℕ) (h : 135 ≤ i) : zeroRow5 i = 0 := by
  unfold zeroRow5
  rw [if_neg (by omega)]

theorem zeroRow6_large (i : ℕ) (h : 134 ≤ i) : zeroRow6 i = 0 := by
  unfold zeroRow6
  rw [if_neg (by omega)]

theorem zeroRow7_large (i : ℕ) (h : 133 ≤ i) : zeroRow7 i = 0 := by
  unfold zeroRow7
  rw [if_neg (by omega)]

theorem zeroRow8_large (i : ℕ) (h : 132 ≤ i) : zeroRow8 i = 0 := by
  unfold zeroRow8
  rw [if_neg (by omega)]

theorem zeroRow9_large (i : ℕ) (h : 131 ≤ i) : zeroRow9 i = 0 := by
  unfold zeroRow9
  rw [if_neg (by omega)]

theorem zeroRow10_large (i : ℕ) (h : 130 ≤ i) : zeroRow10 i = 0 := by
  unfold zeroRow10
  rw [if_neg (by omega)]

theorem zeroRow11_large (i : ℕ) (h : 129 ≤ i) : zeroRow11 i = 0 := by
  unfold zeroRow11
  rw [if_neg (by omega)]

theorem zeroRow12_large (i : ℕ) (h : 128 ≤ i) : zeroRow12 i = 0 := by
  unfold zeroRow12
  rw [if_neg (by omega)]

theorem zeroRow13_large (i : ℕ) (h : 127 ≤ i) : zeroRow13 i = 0 := by
  unfold zeroRow13
  rw [if_neg (by omega)]

theorem zeroRow14_large (i : ℕ) (h : 126 ≤ i) : zeroRow14 i = 0 := by
  unfold zeroRow14
  rw [if_neg (by omega)]

theorem zeroRow15_large (i : ℕ) (h : 125 ≤ i) : zeroRow15 i = 0 := by
  unfold zeroRow15
  rw [if_neg (by omega)]

theorem zeroRow16_large (i : ℕ) (h : 124 ≤ i) : zeroRow16 i = 0 := by
  unfold zeroRow16
  rw [if_neg (by omega)]

theorem zeroRow17_large (i : ℕ) (h : 123 ≤ i) : zeroRow17 i = 0 := by
  unfold zeroRow17
  rw [if_neg (by omega)]

theorem zeroRow18_large (i : ℕ) (h : 122 ≤ i) : zeroRow18 i = 0 := by
  unfold zeroRow18
  rw [if_neg (by omega)]

theorem zeroRow19_large (i : ℕ) (h : 121 ≤ i) : zeroRow19 i = 0 := by
  unfold zeroRow19
  rw [if_neg (by omega)]

theorem zeroRow20_large (i : ℕ) (h : 120 ≤ i) : zeroRow20 i = 0 := by
  unfold zeroRow20
  rw [if_neg (by omega)]

theorem zeroRow21_large (i : ℕ) (h : 119 ≤ i) : zeroRow21 i = 0 := by
  unfold zeroRow21
  rw [if_neg (by omega)]

theorem zeroRow22_large (i : ℕ) (h : 118 ≤ i) : zeroRow22 i = 0 := by
  unfold zeroRow22
  rw [if_neg (by omega)]

theorem zeroRow23_large (i : ℕ) (h : 117 ≤ i) : zeroRow23 i = 0 := by
  unfold zeroRow23
  rw [if_neg (by omega)]

theorem zeroRow24_large (i : ℕ) (h : 116 ≤ i) : zeroRow24 i = 0 := by
  unfold zeroRow24
  rw [if_neg (by omega)]

theorem zeroRow25_large (i : ℕ) (h : 115 ≤ i) : zeroRow25 i = 0 := by
  unfold zeroRow25
  rw [if_neg (by omega)]

theorem zeroRow26_large (i : ℕ) (h : 114 ≤ i) : zeroRow26 i = 0 := by
  unfold zeroRow26
  rw [if_neg (by omega)]

theorem zeroRow27_large (i : ℕ) (h : 113 ≤ i) : zeroRow27 i = 0 := by
  unfold zeroRow27
  rw [if_neg (by omega)]

theorem zeroRow28_large (i : ℕ) (h : 112 ≤ i) : zeroRow28 i = 0 := by
  unfold zeroRow28
  rw [if_neg (by omega)]

theorem zeroRow29_large (i : ℕ) (h : 111 ≤ i) : zeroRow29 i = 0 := by
  unfold zeroRow29
  rw [if_neg (by omega)]

theorem zeroRow30_large (i : ℕ) (h : 110 ≤ i) : zeroRow30 i = 0 := by
  unfold zeroRow30
  rw [if_neg (by omega)]

/-- `zeroClosed` agrees with `zero` on every input, with no side conditions. -/
theorem zero_eq_closed (R V : ℕ) : zero R V = zeroClosed R V := by
  by_cases hR : R ≤ 30
  · interval_cases R
    · rw [show zero 0 V = 0 from rfl, zeroClosed, if_neg (by omega)]
    · by_cases hV : 1 + V ≤ 139
      · exact zero_eq_closed_r1 V (List.mem_range.mpr (by omega))
      · rw [show zero 1 V = zeroRow1 V from rfl, zeroRow1_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 2 + V ≤ 139
      · exact zero_eq_closed_r2 V (List.mem_range.mpr (by omega))
      · rw [show zero 2 V = zeroRow2 V from rfl, zeroRow2_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 3 + V ≤ 139
      · exact zero_eq_closed_r3 V (List.mem_range.mpr (by omega))
      · rw [show zero 3 V = zeroRow3 V from rfl, zeroRow3_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 4 + V ≤ 139
      · exact zero_eq_closed_r4 V (List.mem_range.mpr (by omega))
      · rw [show zero 4 V = zeroRow4 V from rfl, zeroRow4_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 5 + V ≤ 139
      · exact zero_eq_closed_r5 V (List.mem_range.mpr (by omega))
      · rw [show zero 5 V = zeroRow5 V from rfl, zeroRow5_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 6 + V ≤ 139
      · exact zero_eq_closed_r6 V (List.mem_range.mpr (by omega))
      · rw [show zero 6 V = zeroRow6 V from rfl, zeroRow6_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 7 + V ≤ 139
      · exact zero_eq_closed_r7 V (List.mem_range.mpr (by omega))
      · rw [show zero 7 V = zeroRow7 V from rfl, zeroRow7_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 8 + V ≤ 139
      · exact zero_eq_closed_r8 V (List.mem_range.mpr (by omega))
      · rw [show zero 8 V = zeroRow8 V from rfl, zeroRow8_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 9 + V ≤ 139
      · exact zero_eq_closed_r9 V (List.mem_range.mpr (by omega))
      · rw [show zero 9 V = zeroRow9 V from rfl, zeroRow9_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 10 + V ≤ 139
      · exact zero_eq_closed_r10 V (List.mem_range.mpr (by omega))
      · rw [show zero 10 V = zeroRow10 V from rfl, zeroRow10_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 11 + V ≤ 139
      · exact zero_eq_closed_r11 V (List.mem_range.mpr (by omega))
      · rw [show zero 11 V = zeroRow11 V from rfl, zeroRow11_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 12 + V ≤ 139
      · exact zero_eq_closed_r12 V (List.mem_range.mpr (by omega))
      · rw [show zero 12 V = zeroRow12 V from rfl, zeroRow12_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 13 + V ≤ 139
      · exact zero_eq_closed_r13 V (List.mem_range.mpr (by omega))
      · rw [show zero 13 V = zeroRow13 V from rfl, zeroRow13_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 14 + V ≤ 139
      · exact zero_eq_closed_r14 V (List.mem_range.mpr (by omega))
      · rw [show zero 14 V = zeroRow14 V from rfl, zeroRow14_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 15 + V ≤ 139
      · exact zero_eq_closed_r15 V (List.mem_range.mpr (by omega))
      · rw [show zero 15 V = zeroRow15 V from rfl, zeroRow15_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 16 + V ≤ 139
      · exact zero_eq_closed_r16 V (List.mem_range.mpr (by omega))
      · rw [show zero 16 V = zeroRow16 V from rfl, zeroRow16_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 17 + V ≤ 139
      · exact zero_eq_closed_r17 V (List.mem_range.mpr (by omega))
      · rw [show zero 17 V = zeroRow17 V from rfl, zeroRow17_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 18 + V ≤ 139
      · exact zero_eq_closed_r18 V (List.mem_range.mpr (by omega))
      · rw [show zero 18 V = zeroRow18 V from rfl, zeroRow18_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 19 + V ≤ 139
      · exact zero_eq_closed_r19 V (List.mem_range.mpr (by omega))
      · rw [show zero 19 V = zeroRow19 V from rfl, zeroRow19_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 20 + V ≤ 139
      · exact zero_eq_closed_r20 V (List.mem_range.mpr (by omega))
      · rw [show zero 20 V = zeroRow20 V from rfl, zeroRow20_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 21 + V ≤ 139
      · exact zero_eq_closed_r21 V (List.mem_range.mpr (by omega))
      · rw [show zero 21 V = zeroRow21 V from rfl, zeroRow21_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 22 + V ≤ 139
      · exact zero_eq_closed_r22 V (List.mem_range.mpr (by omega))
      · rw [show zero 22 V = zeroRow22 V from rfl, zeroRow22_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 23 + V ≤ 139
      · exact zero_eq_closed_r23 V (List.mem_range.mpr (by omega))
      · rw [show zero 23 V = zeroRow23 V from rfl, zeroRow23_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 24 + V ≤ 139
      · exact zero_eq_closed_r24 V (List.mem_range.mpr (by omega))
      · rw [show zero 24 V = zeroRow24 V from rfl, zeroRow24_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 25 + V ≤ 139
      · exact zero_eq_closed_r25 V (List.mem_range.mpr (by omega))
      · rw [show zero 25 V = zeroRow25 V from rfl, zeroRow25_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 26 + V ≤ 139
      · exact zero_eq_closed_r26 V (List.mem_range.mpr (by omega))
      · rw [show zero 26 V = zeroRow26 V from rfl, zeroRow26_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 27 + V ≤ 139
      · exact zero_eq_closed_r27 V (List.mem_range.mpr (by omega))
      · rw [show zero 27 V = zeroRow27 V from rfl, zeroRow27_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 28 + V ≤ 139
      · exact zero_eq_closed_r28 V (List.mem_range.mpr (by omega))
      · rw [show zero 28 V = zeroRow28 V from rfl, zeroRow28_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 29 + V ≤ 139
      · exact zero_eq_closed_r29 V (List.mem_range.mpr (by omega))
      · rw [show zero 29 V = zeroRow29 V from rfl, zeroRow29_large V (by omega),
            zeroClosed, if_neg (by omega)]
    · by_cases hV : 30 + V ≤ 139
      · exact zero_eq_closed_r30 V (List.mem_range.mpr (by omega))
      · rw [show zero 30 V = zeroRow30 V from rfl, zeroRow30_large V (by omega),
            zeroClosed, if_neg (by omega)]
  · have hge : 31 ≤ R := by omega
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hge
    rw [show zero (31+j) V = 0 by rw [Nat.add_comm 31 j]; rfl,
        zeroClosed, if_neg (by omega)]


/-! ### Superadditivity of the quadratic body -/

/-- The coefficient facts the superadditivity argument needs. -/
def qFacts (a b : ℕ) : Prop :=
  qa a ≤ qa (a + b) ∧ qa b ≤ qa (a + b) ∧
  qb a ≤ qb (a + b) ∧ qb b ≤ qb (a + b) ∧
  qc a + qc b ≤ qc (a + b)

instance (a b : ℕ) : Decidable (qFacts a b) := by unfold qFacts; infer_instance

theorem qFacts_all : ∀ a ∈ List.range 31, ∀ b ∈ List.range 31,
    1 ≤ a → 1 ≤ b → a + b ≤ 30 → qFacts a b := by decide +kernel

/-- `V * (V-1)` is additive across a split, exactly, in `ℕ`. -/
theorem falling_add (c d : ℕ) :
    (c + d) * (c + d - 1) = c * (c - 1) + d * (d - 1) + 2 * (c * d) := by
  cases c with
  | zero => simp
  | succ c' =>
    cases d with
    | zero => simp
    | succ d' =>
      have h1 : c' + 1 + (d' + 1) - 1 = c' + d' + 1 := by omega
      have h2 : c' + 1 - 1 = c' := by omega
      have h3 : d' + 1 - 1 = d' := by omega
      rw [h1, h2, h3]
      ring

/-- Superadditivity of the quadratic body on the admissible range. -/
theorem zeroQ_superadd (a b c d : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b ≤ 30) :
    zeroQ a c + zeroQ b d ≤ zeroQ (a + b) (c + d) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    qFacts_all a (List.mem_range.mpr (by omega)) b (List.mem_range.mpr (by omega)) ha hb hab
  unfold zeroQ
  rw [falling_add]
  have e1 : qa a * (c * (c - 1)) ≤ qa (a + b) * (c * (c - 1)) :=
    Nat.mul_le_mul_right _ h1
  have e2 : qa b * (d * (d - 1)) ≤ qa (a + b) * (d * (d - 1)) :=
    Nat.mul_le_mul_right _ h2
  have e3 : qb a * c ≤ qb (a + b) * c := Nat.mul_le_mul_right _ h3
  have e4 : qb b * d ≤ qb (a + b) * d := Nat.mul_le_mul_right _ h4
  have expand :
      qa (a + b) * (c * (c - 1) + d * (d - 1) + 2 * (c * d)) + qb (a + b) * (c + d)
          + qc (a + b)
        = (qa (a + b) * (c * (c - 1)) + qa (a + b) * (d * (d - 1))
            + qa (a + b) * (2 * (c * d)))
          + (qb (a + b) * c + qb (a + b) * d) + qc (a + b) := by ring
  rw [expand]
  omega


/-! ### Superadditivity of `zeroClosed`, including the head region -/

/-- Guarded superadditivity test: trivially `true` off the admissible range. -/
def headOK (a b c d : ℕ) : Bool :=
  if 1 ≤ a ∧ 1 ≤ b ∧ a + b ≤ 30 ∧ a + b + (c + d) ≤ 139 then
    Nat.ble (zeroClosed a c + zeroClosed b d) (zeroClosed (a + b) (c + d))
  else true



/-- Head-region splits, one lemma per row `a`, ranges cut to the admissible box. -/
theorem headOK_left_a1 : ∀ b ∈ List.range 30, ∀ c ∈ List.range 6, ∀ d ∈ List.range 139,
    headOK 1 b c d = true := by decide +kernel

theorem headOK_left_a2 : ∀ b ∈ List.range 29, ∀ c ∈ List.range 6, ∀ d ∈ List.range 138,
    headOK 2 b c d = true := by decide +kernel

theorem headOK_left_a3 : ∀ b ∈ List.range 28, ∀ c ∈ List.range 6, ∀ d ∈ List.range 137,
    headOK 3 b c d = true := by decide +kernel

theorem headOK_left_a4 : ∀ b ∈ List.range 27, ∀ c ∈ List.range 6, ∀ d ∈ List.range 136,
    headOK 4 b c d = true := by decide +kernel

theorem headOK_left_a5 : ∀ b ∈ List.range 26, ∀ c ∈ List.range 6, ∀ d ∈ List.range 135,
    headOK 5 b c d = true := by decide +kernel

theorem headOK_left_a6 : ∀ b ∈ List.range 25, ∀ c ∈ List.range 6, ∀ d ∈ List.range 134,
    headOK 6 b c d = true := by decide +kernel

theorem headOK_left_a7 : ∀ b ∈ List.range 24, ∀ c ∈ List.range 6, ∀ d ∈ List.range 133,
    headOK 7 b c d = true := by decide +kernel

theorem headOK_left_a8 : ∀ b ∈ List.range 23, ∀ c ∈ List.range 6, ∀ d ∈ List.range 132,
    headOK 8 b c d = true := by decide +kernel

theorem headOK_left_a9 : ∀ b ∈ List.range 22, ∀ c ∈ List.range 6, ∀ d ∈ List.range 131,
    headOK 9 b c d = true := by decide +kernel

theorem headOK_left_a10 : ∀ b ∈ List.range 21, ∀ c ∈ List.range 6, ∀ d ∈ List.range 130,
    headOK 10 b c d = true := by decide +kernel

theorem headOK_left_a11 : ∀ b ∈ List.range 20, ∀ c ∈ List.range 6, ∀ d ∈ List.range 129,
    headOK 11 b c d = true := by decide +kernel

theorem headOK_left_a12 : ∀ b ∈ List.range 19, ∀ c ∈ List.range 6, ∀ d ∈ List.range 128,
    headOK 12 b c d = true := by decide +kernel

theorem headOK_left_a13 : ∀ b ∈ List.range 18, ∀ c ∈ List.range 6, ∀ d ∈ List.range 127,
    headOK 13 b c d = true := by decide +kernel

theorem headOK_left_a14 : ∀ b ∈ List.range 17, ∀ c ∈ List.range 6, ∀ d ∈ List.range 126,
    headOK 14 b c d = true := by decide +kernel

theorem headOK_left_a15 : ∀ b ∈ List.range 16, ∀ c ∈ List.range 6, ∀ d ∈ List.range 125,
    headOK 15 b c d = true := by decide +kernel

theorem headOK_left_a16 : ∀ b ∈ List.range 15, ∀ c ∈ List.range 6, ∀ d ∈ List.range 124,
    headOK 16 b c d = true := by decide +kernel

theorem headOK_left_a17 : ∀ b ∈ List.range 14, ∀ c ∈ List.range 6, ∀ d ∈ List.range 123,
    headOK 17 b c d = true := by decide +kernel

theorem headOK_left_a18 : ∀ b ∈ List.range 13, ∀ c ∈ List.range 6, ∀ d ∈ List.range 122,
    headOK 18 b c d = true := by decide +kernel

theorem headOK_left_a19 : ∀ b ∈ List.range 12, ∀ c ∈ List.range 6, ∀ d ∈ List.range 121,
    headOK 19 b c d = true := by decide +kernel

theorem headOK_left_a20 : ∀ b ∈ List.range 11, ∀ c ∈ List.range 6, ∀ d ∈ List.range 120,
    headOK 20 b c d = true := by decide +kernel

theorem headOK_left_a21 : ∀ b ∈ List.range 10, ∀ c ∈ List.range 6, ∀ d ∈ List.range 119,
    headOK 21 b c d = true := by decide +kernel

theorem headOK_left_a22 : ∀ b ∈ List.range 9, ∀ c ∈ List.range 6, ∀ d ∈ List.range 118,
    headOK 22 b c d = true := by decide +kernel

theorem headOK_left_a23 : ∀ b ∈ List.range 8, ∀ c ∈ List.range 6, ∀ d ∈ List.range 117,
    headOK 23 b c d = true := by decide +kernel

theorem headOK_left_a24 : ∀ b ∈ List.range 7, ∀ c ∈ List.range 6, ∀ d ∈ List.range 116,
    headOK 24 b c d = true := by decide +kernel

theorem headOK_left_a25 : ∀ b ∈ List.range 6, ∀ c ∈ List.range 6, ∀ d ∈ List.range 115,
    headOK 25 b c d = true := by decide +kernel

theorem headOK_left_a26 : ∀ b ∈ List.range 5, ∀ c ∈ List.range 6, ∀ d ∈ List.range 114,
    headOK 26 b c d = true := by decide +kernel

theorem headOK_left_a27 : ∀ b ∈ List.range 4, ∀ c ∈ List.range 6, ∀ d ∈ List.range 113,
    headOK 27 b c d = true := by decide +kernel

theorem headOK_left_a28 : ∀ b ∈ List.range 3, ∀ c ∈ List.range 6, ∀ d ∈ List.range 112,
    headOK 28 b c d = true := by decide +kernel

theorem headOK_left_a29 : ∀ b ∈ List.range 2, ∀ c ∈ List.range 6, ∀ d ∈ List.range 111,
    headOK 29 b c d = true := by decide +kernel

theorem headOK_left_a30 : ∀ b ∈ List.range 1, ∀ c ∈ List.range 6, ∀ d ∈ List.range 110,
    headOK 30 b c d = true := by decide +kernel

theorem headOK_right_a1 : ∀ b ∈ List.range 30, ∀ c ∈ List.range 139, ∀ d ∈ List.range 6,
    headOK 1 b c d = true := by decide +kernel

theorem headOK_right_a2 : ∀ b ∈ List.range 29, ∀ c ∈ List.range 138, ∀ d ∈ List.range 6,
    headOK 2 b c d = true := by decide +kernel

theorem headOK_right_a3 : ∀ b ∈ List.range 28, ∀ c ∈ List.range 137, ∀ d ∈ List.range 6,
    headOK 3 b c d = true := by decide +kernel

theorem headOK_right_a4 : ∀ b ∈ List.range 27, ∀ c ∈ List.range 136, ∀ d ∈ List.range 6,
    headOK 4 b c d = true := by decide +kernel

theorem headOK_right_a5 : ∀ b ∈ List.range 26, ∀ c ∈ List.range 135, ∀ d ∈ List.range 6,
    headOK 5 b c d = true := by decide +kernel

theorem headOK_right_a6 : ∀ b ∈ List.range 25, ∀ c ∈ List.range 134, ∀ d ∈ List.range 6,
    headOK 6 b c d = true := by decide +kernel

theorem headOK_right_a7 : ∀ b ∈ List.range 24, ∀ c ∈ List.range 133, ∀ d ∈ List.range 6,
    headOK 7 b c d = true := by decide +kernel

theorem headOK_right_a8 : ∀ b ∈ List.range 23, ∀ c ∈ List.range 132, ∀ d ∈ List.range 6,
    headOK 8 b c d = true := by decide +kernel

theorem headOK_right_a9 : ∀ b ∈ List.range 22, ∀ c ∈ List.range 131, ∀ d ∈ List.range 6,
    headOK 9 b c d = true := by decide +kernel

theorem headOK_right_a10 : ∀ b ∈ List.range 21, ∀ c ∈ List.range 130, ∀ d ∈ List.range 6,
    headOK 10 b c d = true := by decide +kernel

theorem headOK_right_a11 : ∀ b ∈ List.range 20, ∀ c ∈ List.range 129, ∀ d ∈ List.range 6,
    headOK 11 b c d = true := by decide +kernel

theorem headOK_right_a12 : ∀ b ∈ List.range 19, ∀ c ∈ List.range 128, ∀ d ∈ List.range 6,
    headOK 12 b c d = true := by decide +kernel

theorem headOK_right_a13 : ∀ b ∈ List.range 18, ∀ c ∈ List.range 127, ∀ d ∈ List.range 6,
    headOK 13 b c d = true := by decide +kernel

theorem headOK_right_a14 : ∀ b ∈ List.range 17, ∀ c ∈ List.range 126, ∀ d ∈ List.range 6,
    headOK 14 b c d = true := by decide +kernel

theorem headOK_right_a15 : ∀ b ∈ List.range 16, ∀ c ∈ List.range 125, ∀ d ∈ List.range 6,
    headOK 15 b c d = true := by decide +kernel

theorem headOK_right_a16 : ∀ b ∈ List.range 15, ∀ c ∈ List.range 124, ∀ d ∈ List.range 6,
    headOK 16 b c d = true := by decide +kernel

theorem headOK_right_a17 : ∀ b ∈ List.range 14, ∀ c ∈ List.range 123, ∀ d ∈ List.range 6,
    headOK 17 b c d = true := by decide +kernel

theorem headOK_right_a18 : ∀ b ∈ List.range 13, ∀ c ∈ List.range 122, ∀ d ∈ List.range 6,
    headOK 18 b c d = true := by decide +kernel

theorem headOK_right_a19 : ∀ b ∈ List.range 12, ∀ c ∈ List.range 121, ∀ d ∈ List.range 6,
    headOK 19 b c d = true := by decide +kernel

theorem headOK_right_a20 : ∀ b ∈ List.range 11, ∀ c ∈ List.range 120, ∀ d ∈ List.range 6,
    headOK 20 b c d = true := by decide +kernel

theorem headOK_right_a21 : ∀ b ∈ List.range 10, ∀ c ∈ List.range 119, ∀ d ∈ List.range 6,
    headOK 21 b c d = true := by decide +kernel

theorem headOK_right_a22 : ∀ b ∈ List.range 9, ∀ c ∈ List.range 118, ∀ d ∈ List.range 6,
    headOK 22 b c d = true := by decide +kernel

theorem headOK_right_a23 : ∀ b ∈ List.range 8, ∀ c ∈ List.range 117, ∀ d ∈ List.range 6,
    headOK 23 b c d = true := by decide +kernel

theorem headOK_right_a24 : ∀ b ∈ List.range 7, ∀ c ∈ List.range 116, ∀ d ∈ List.range 6,
    headOK 24 b c d = true := by decide +kernel

theorem headOK_right_a25 : ∀ b ∈ List.range 6, ∀ c ∈ List.range 115, ∀ d ∈ List.range 6,
    headOK 25 b c d = true := by decide +kernel

theorem headOK_right_a26 : ∀ b ∈ List.range 5, ∀ c ∈ List.range 114, ∀ d ∈ List.range 6,
    headOK 26 b c d = true := by decide +kernel

theorem headOK_right_a27 : ∀ b ∈ List.range 4, ∀ c ∈ List.range 113, ∀ d ∈ List.range 6,
    headOK 27 b c d = true := by decide +kernel

theorem headOK_right_a28 : ∀ b ∈ List.range 3, ∀ c ∈ List.range 112, ∀ d ∈ List.range 6,
    headOK 28 b c d = true := by decide +kernel

theorem headOK_right_a29 : ∀ b ∈ List.range 2, ∀ c ∈ List.range 111, ∀ d ∈ List.range 6,
    headOK 29 b c d = true := by decide +kernel

theorem headOK_right_a30 : ∀ b ∈ List.range 1, ∀ c ∈ List.range 110, ∀ d ∈ List.range 6,
    headOK 30 b c d = true := by decide +kernel


/-- Turn a `headOK` evaluation into the inequality it encodes. -/
theorem of_headOK {a b c d : ℕ} (h : headOK a b c d = true)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b ≤ 30) (hcd : a + b + (c + d) ≤ 139) :
    zeroClosed a c + zeroClosed b d ≤ zeroClosed (a + b) (c + d) := by
  unfold headOK at h
  rw [if_pos (⟨ha, hb, hab, hcd⟩ : 1 ≤ a ∧ 1 ≤ b ∧ a + b ≤ 30 ∧ a + b + (c + d) ≤ 139)] at h
  exact Nat.le_of_ble_eq_true h

/-- Off the head region every position uses the quadratic body. -/
theorem zeroClosed_eq_zeroQ {R V : ℕ} (h1 : 1 ≤ R) (h2 : R ≤ 30) (h3 : R + V ≤ 139)
    (h4 : 6 ≤ V) : zeroClosed R V = zeroQ R V := by
  unfold zeroClosed
  rw [if_pos ⟨h1, h2, h3⟩, if_neg]
  interval_cases R <;> simp [qV0] <;> omega

/-- Superadditivity of `zeroClosed` on the whole admissible range. -/
theorem zeroClosed_superadd (a b c d : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : a + b ≤ 30) (hcd : a + b + (c + d) ≤ 139) :
    zeroClosed a c + zeroClosed b d ≤ zeroClosed (a + b) (c + d) := by
  have ha30 : a ≤ 30 := by omega
  by_cases hc : c < 6
  · interval_cases a
    · have hbr : b < 30 := by omega
      have hdr : d < 139 := by omega
      exact of_headOK (headOK_left_a1 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 29 := by omega
      have hdr : d < 138 := by omega
      exact of_headOK (headOK_left_a2 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 28 := by omega
      have hdr : d < 137 := by omega
      exact of_headOK (headOK_left_a3 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 27 := by omega
      have hdr : d < 136 := by omega
      exact of_headOK (headOK_left_a4 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 26 := by omega
      have hdr : d < 135 := by omega
      exact of_headOK (headOK_left_a5 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 25 := by omega
      have hdr : d < 134 := by omega
      exact of_headOK (headOK_left_a6 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 24 := by omega
      have hdr : d < 133 := by omega
      exact of_headOK (headOK_left_a7 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 23 := by omega
      have hdr : d < 132 := by omega
      exact of_headOK (headOK_left_a8 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 22 := by omega
      have hdr : d < 131 := by omega
      exact of_headOK (headOK_left_a9 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 21 := by omega
      have hdr : d < 130 := by omega
      exact of_headOK (headOK_left_a10 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 20 := by omega
      have hdr : d < 129 := by omega
      exact of_headOK (headOK_left_a11 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 19 := by omega
      have hdr : d < 128 := by omega
      exact of_headOK (headOK_left_a12 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 18 := by omega
      have hdr : d < 127 := by omega
      exact of_headOK (headOK_left_a13 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 17 := by omega
      have hdr : d < 126 := by omega
      exact of_headOK (headOK_left_a14 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 16 := by omega
      have hdr : d < 125 := by omega
      exact of_headOK (headOK_left_a15 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 15 := by omega
      have hdr : d < 124 := by omega
      exact of_headOK (headOK_left_a16 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 14 := by omega
      have hdr : d < 123 := by omega
      exact of_headOK (headOK_left_a17 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 13 := by omega
      have hdr : d < 122 := by omega
      exact of_headOK (headOK_left_a18 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 12 := by omega
      have hdr : d < 121 := by omega
      exact of_headOK (headOK_left_a19 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 11 := by omega
      have hdr : d < 120 := by omega
      exact of_headOK (headOK_left_a20 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 10 := by omega
      have hdr : d < 119 := by omega
      exact of_headOK (headOK_left_a21 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 9 := by omega
      have hdr : d < 118 := by omega
      exact of_headOK (headOK_left_a22 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 8 := by omega
      have hdr : d < 117 := by omega
      exact of_headOK (headOK_left_a23 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 7 := by omega
      have hdr : d < 116 := by omega
      exact of_headOK (headOK_left_a24 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 6 := by omega
      have hdr : d < 115 := by omega
      exact of_headOK (headOK_left_a25 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 5 := by omega
      have hdr : d < 114 := by omega
      exact of_headOK (headOK_left_a26 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 4 := by omega
      have hdr : d < 113 := by omega
      exact of_headOK (headOK_left_a27 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 3 := by omega
      have hdr : d < 112 := by omega
      exact of_headOK (headOK_left_a28 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 2 := by omega
      have hdr : d < 111 := by omega
      exact of_headOK (headOK_left_a29 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
    · have hbr : b < 1 := by omega
      have hdr : d < 110 := by omega
      exact of_headOK (headOK_left_a30 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hc)
        d (List.mem_range.mpr hdr)) ha hb hab hcd
  · by_cases hd : d < 6
    · interval_cases a
      · have hbr : b < 30 := by omega
        have hcr : c < 139 := by omega
        exact of_headOK (headOK_right_a1 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 29 := by omega
        have hcr : c < 138 := by omega
        exact of_headOK (headOK_right_a2 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 28 := by omega
        have hcr : c < 137 := by omega
        exact of_headOK (headOK_right_a3 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 27 := by omega
        have hcr : c < 136 := by omega
        exact of_headOK (headOK_right_a4 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 26 := by omega
        have hcr : c < 135 := by omega
        exact of_headOK (headOK_right_a5 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 25 := by omega
        have hcr : c < 134 := by omega
        exact of_headOK (headOK_right_a6 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 24 := by omega
        have hcr : c < 133 := by omega
        exact of_headOK (headOK_right_a7 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 23 := by omega
        have hcr : c < 132 := by omega
        exact of_headOK (headOK_right_a8 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 22 := by omega
        have hcr : c < 131 := by omega
        exact of_headOK (headOK_right_a9 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 21 := by omega
        have hcr : c < 130 := by omega
        exact of_headOK (headOK_right_a10 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 20 := by omega
        have hcr : c < 129 := by omega
        exact of_headOK (headOK_right_a11 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 19 := by omega
        have hcr : c < 128 := by omega
        exact of_headOK (headOK_right_a12 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 18 := by omega
        have hcr : c < 127 := by omega
        exact of_headOK (headOK_right_a13 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 17 := by omega
        have hcr : c < 126 := by omega
        exact of_headOK (headOK_right_a14 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 16 := by omega
        have hcr : c < 125 := by omega
        exact of_headOK (headOK_right_a15 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 15 := by omega
        have hcr : c < 124 := by omega
        exact of_headOK (headOK_right_a16 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 14 := by omega
        have hcr : c < 123 := by omega
        exact of_headOK (headOK_right_a17 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 13 := by omega
        have hcr : c < 122 := by omega
        exact of_headOK (headOK_right_a18 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 12 := by omega
        have hcr : c < 121 := by omega
        exact of_headOK (headOK_right_a19 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 11 := by omega
        have hcr : c < 120 := by omega
        exact of_headOK (headOK_right_a20 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 10 := by omega
        have hcr : c < 119 := by omega
        exact of_headOK (headOK_right_a21 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 9 := by omega
        have hcr : c < 118 := by omega
        exact of_headOK (headOK_right_a22 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 8 := by omega
        have hcr : c < 117 := by omega
        exact of_headOK (headOK_right_a23 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 7 := by omega
        have hcr : c < 116 := by omega
        exact of_headOK (headOK_right_a24 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 6 := by omega
        have hcr : c < 115 := by omega
        exact of_headOK (headOK_right_a25 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 5 := by omega
        have hcr : c < 114 := by omega
        exact of_headOK (headOK_right_a26 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 4 := by omega
        have hcr : c < 113 := by omega
        exact of_headOK (headOK_right_a27 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 3 := by omega
        have hcr : c < 112 := by omega
        exact of_headOK (headOK_right_a28 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 2 := by omega
        have hcr : c < 111 := by omega
        exact of_headOK (headOK_right_a29 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
      · have hbr : b < 1 := by omega
        have hcr : c < 110 := by omega
        exact of_headOK (headOK_right_a30 b (List.mem_range.mpr hbr) c (List.mem_range.mpr hcr)
          d (List.mem_range.mpr hd)) ha hb hab hcd
    · rw [zeroClosed_eq_zeroQ ha (by omega) (by omega) (by omega),
          zeroClosed_eq_zeroQ hb (by omega) (by omega) (by omega),
          zeroClosed_eq_zeroQ (show 1 ≤ a + b by omega) (by omega) (by omega) (by omega)]
      exact zeroQ_superadd a b c d ha hb hab

/-- Superadditivity of the shipped `zero` table. -/
theorem zero_superadd (a b c d : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : a + b ≤ 30) (hcd : a + b + (c + d) ≤ 139) :
    zero a c + zero b d ≤ zero (a + b) (c + d) := by
  rw [zero_eq_closed a c, zero_eq_closed b d, zero_eq_closed (a + b) (c + d)]
  exact zeroClosed_superadd a b c d ha hb hab hcd

end ProximityPrize.SubmissionLower.BoundaryTailZeroClosed
