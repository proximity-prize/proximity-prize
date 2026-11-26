import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.R6960ChartImage

section Merged6967_Near6967LargeRank19g5
set_option Elab.async false

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace Research6966.LargeSeed19g5
open K1_14 (Shape)
def shape : Shape := ⟨4000, 5584, 1200, 443000⟩
def box : Fin 2 → ℕ := ![323000, 120000]
def nodes : ℕ := 1914889096396800
def moment : ℕ := 26522789079578

theorem node_eq : P1_7_1.nodeRows shape = nodes := by
  have rank := P1_7_1_2.six_nodeRows shape (by decide) (by decide)
  have closed : 262144*P1_7_1_2.sixPerNode (shape.m-2*shape.J) shape.J = 6*nodes := by decide
  rw [closed] at rank
  omega

private theorem cost_5584_1200_block0 : P1_7_1_3.blockEstimate 5584 1200 1200 128 = 1963655200 := by decide +kernel

private theorem cost_5584_1200_block1 : P1_7_1_3.blockEstimate 5584 1200 1328 128 = 13292736544 := by decide +kernel

private theorem cost_5584_1200_block2 : P1_7_1_3.blockEstimate 5584 1200 1456 128 = 35121209376 := by decide +kernel

private theorem cost_5584_1200_block3 : P1_7_1_3.blockEstimate 5584 1200 1584 128 = 66643767328 := by decide +kernel

private theorem cost_5584_1200_block4 : P1_7_1_3.blockEstimate 5584 1200 1712 128 = 107055104032 := by decide +kernel

private theorem cost_5584_1200_block5 : P1_7_1_3.blockEstimate 5584 1200 1840 128 = 155549913120 := by decide +kernel

private theorem cost_5584_1200_block6 : P1_7_1_3.blockEstimate 5584 1200 1968 128 = 211322888224 := by decide +kernel

private theorem cost_5584_1200_block7 : P1_7_1_3.blockEstimate 5584 1200 2096 128 = 273568722976 := by decide +kernel

private theorem cost_5584_1200_block8 : P1_7_1_3.blockEstimate 5584 1200 2224 128 = 341482111008 := by decide +kernel

private theorem cost_5584_1200_block9 : P1_7_1_3.blockEstimate 5584 1200 2352 128 = 413888779612 := by decide +kernel

private theorem cost_5584_1200_block10 : P1_7_1_3.blockEstimate 5584 1200 2480 128 = 485117451136 := by decide +kernel

private theorem cost_5584_1200_block11 : P1_7_1_3.blockEstimate 5584 1200 2608 128 = 551390206848 := by decide +kernel

private theorem cost_5584_1200_block12 : P1_7_1_3.blockEstimate 5584 1200 2736 128 = 612625603456 := by decide +kernel

private theorem cost_5584_1200_block13 : P1_7_1_3.blockEstimate 5584 1200 2864 128 = 668823640960 := by decide +kernel

private theorem cost_5584_1200_block14 : P1_7_1_3.blockEstimate 5584 1200 2992 128 = 719984319360 := by decide +kernel

private theorem cost_5584_1200_block15 : P1_7_1_3.blockEstimate 5584 1200 3120 128 = 766107638656 := by decide +kernel

private theorem cost_5584_1200_block16 : P1_7_1_3.blockEstimate 5584 1200 3248 128 = 807193598848 := by decide +kernel

private theorem cost_5584_1200_block17 : P1_7_1_3.blockEstimate 5584 1200 3376 128 = 843242199936 := by decide +kernel

private theorem cost_5584_1200_block18 : P1_7_1_3.blockEstimate 5584 1200 3504 128 = 874253441920 := by decide +kernel

private theorem cost_5584_1200_block19 : P1_7_1_3.blockEstimate 5584 1200 3632 128 = 900227324800 := by decide +kernel

private theorem cost_5584_1200_block20 : P1_7_1_3.blockEstimate 5584 1200 3760 128 = 921163848576 := by decide +kernel

private theorem cost_5584_1200_block21 : P1_7_1_3.blockEstimate 5584 1200 3888 128 = 937063013248 := by decide +kernel

private theorem cost_5584_1200_block22 : P1_7_1_3.blockEstimate 5584 1200 4016 128 = 947924818816 := by decide +kernel

private theorem cost_5584_1200_block23 : P1_7_1_3.blockEstimate 5584 1200 4144 128 = 953749265280 := by decide +kernel

private theorem cost_5584_1200_block24 : P1_7_1_3.blockEstimate 5584 1200 4272 128 = 954536352640 := by decide +kernel

private theorem cost_5584_1200_block25 : P1_7_1_3.blockEstimate 5584 1200 4400 128 = 950286080896 := by decide +kernel

private theorem cost_5584_1200_block26 : P1_7_1_3.blockEstimate 5584 1200 4528 128 = 940998450048 := by decide +kernel

private theorem cost_5584_1200_block27 : P1_7_1_3.blockEstimate 5584 1200 4656 128 = 926673460096 := by decide +kernel

private theorem cost_5584_1200_block28 : P1_7_1_3.blockEstimate 5584 1200 4784 128 = 907311111040 := by decide +kernel

private theorem cost_5584_1200_block29 : P1_7_1_3.blockEstimate 5584 1200 4912 128 = 882911402880 := by decide +kernel

private theorem cost_5584_1200_block30 : P1_7_1_3.blockEstimate 5584 1200 5040 128 = 853474335616 := by decide +kernel

private theorem cost_5584_1200_block31 : P1_7_1_3.blockEstimate 5584 1200 5168 128 = 818999909248 := by decide +kernel

private theorem cost_5584_1200_block32 : P1_7_1_3.blockEstimate 5584 1200 5296 128 = 779488123776 := by decide +kernel

private theorem cost_5584_1200_block33 : P1_7_1_3.blockEstimate 5584 1200 5424 128 = 734938979200 := by decide +kernel

private theorem cost_5584_1200_block34 : P1_7_1_3.blockEstimate 5584 1200 5552 128 = 685598907128 := by decide +kernel

private theorem cost_5584_1200_block35 : P1_7_1_3.blockEstimate 5584 1200 5680 128 = 633718960863 := by decide +kernel

private theorem cost_5584_1200_block36 : P1_7_1_3.blockEstimate 5584 1200 5808 128 = 580869400339 := by decide +kernel

private theorem cost_5584_1200_block37 : P1_7_1_3.blockEstimate 5584 1200 5936 128 = 527624752980 := by decide +kernel

private theorem cost_5584_1200_block38 : P1_7_1_3.blockEstimate 5584 1200 6064 128 = 474529907440 := by decide +kernel

private theorem cost_5584_1200_block39 : P1_7_1_3.blockEstimate 5584 1200 6192 128 = 422108296395 := by decide +kernel

private theorem cost_5584_1200_block40 : P1_7_1_3.blockEstimate 5584 1200 6320 128 = 370861895379 := by decide +kernel

private theorem cost_5584_1200_block41 : P1_7_1_3.blockEstimate 5584 1200 6448 128 = 321271222568 := by decide +kernel

private theorem cost_5584_1200_block42 : P1_7_1_3.blockEstimate 5584 1200 6576 128 = 273795339688 := by decide +kernel

private theorem cost_5584_1200_block43 : P1_7_1_3.blockEstimate 5584 1200 6704 128 = 228822828866 := by decide +kernel

private theorem cost_5584_1200_block44 : P1_7_1_3.blockEstimate 5584 1200 6832 128 = 186446438592 := by decide +kernel

private theorem cost_5584_1200_block45 : P1_7_1_3.blockEstimate 5584 1200 6960 128 = 147621929152 := by decide +kernel

private theorem cost_5584_1200_block46 : P1_7_1_3.blockEstimate 5584 1200 7088 128 = 112763723968 := by decide +kernel

private theorem cost_5584_1200_block47 : P1_7_1_3.blockEstimate 5584 1200 7216 128 = 82123481280 := by decide +kernel

private theorem cost_5584_1200_block48 : P1_7_1_3.blockEstimate 5584 1200 7344 128 = 55952859328 := by decide +kernel

private theorem cost_5584_1200_block49 : P1_7_1_3.blockEstimate 5584 1200 7472 128 = 34503516352 := by decide +kernel

private theorem cost_5584_1200_block50 : P1_7_1_3.blockEstimate 5584 1200 7600 128 = 18027110592 := by decide +kernel

private theorem cost_5584_1200_block51 : P1_7_1_3.blockEstimate 5584 1200 7728 128 = 6775300288 := by decide +kernel

private theorem cost_5584_1200_block52 : P1_7_1_3.blockEstimate 5584 1200 7856 128 = 999743680 := by decide +kernel

private theorem cost_5584_1200_join0_0 : P1_7_1_3.blockEstimate 5584 1200 1200 256 = 15256391744 :=
  @P1_7_1_3.block_append 5584 1200 1200 1328 128 128 256 1963655200 13292736544 15256391744 cost_5584_1200_block0 cost_5584_1200_block1 rfl rfl rfl

private theorem cost_5584_1200_join0_2 : P1_7_1_3.blockEstimate 5584 1200 1456 256 = 101764976704 :=
  @P1_7_1_3.block_append 5584 1200 1456 1584 128 128 256 35121209376 66643767328 101764976704 cost_5584_1200_block2 cost_5584_1200_block3 rfl rfl rfl

private theorem cost_5584_1200_join0_4 : P1_7_1_3.blockEstimate 5584 1200 1712 256 = 262605017152 :=
  @P1_7_1_3.block_append 5584 1200 1712 1840 128 128 256 107055104032 155549913120 262605017152 cost_5584_1200_block4 cost_5584_1200_block5 rfl rfl rfl

private theorem cost_5584_1200_join0_6 : P1_7_1_3.blockEstimate 5584 1200 1968 256 = 484891611200 :=
  @P1_7_1_3.block_append 5584 1200 1968 2096 128 128 256 211322888224 273568722976 484891611200 cost_5584_1200_block6 cost_5584_1200_block7 rfl rfl rfl

private theorem cost_5584_1200_join0_8 : P1_7_1_3.blockEstimate 5584 1200 2224 256 = 755370890620 :=
  @P1_7_1_3.block_append 5584 1200 2224 2352 128 128 256 341482111008 413888779612 755370890620 cost_5584_1200_block8 cost_5584_1200_block9 rfl rfl rfl

private theorem cost_5584_1200_join0_10 : P1_7_1_3.blockEstimate 5584 1200 2480 256 = 1036507657984 :=
  @P1_7_1_3.block_append 5584 1200 2480 2608 128 128 256 485117451136 551390206848 1036507657984 cost_5584_1200_block10 cost_5584_1200_block11 rfl rfl rfl

private theorem cost_5584_1200_join0_12 : P1_7_1_3.blockEstimate 5584 1200 2736 256 = 1281449244416 :=
  @P1_7_1_3.block_append 5584 1200 2736 2864 128 128 256 612625603456 668823640960 1281449244416 cost_5584_1200_block12 cost_5584_1200_block13 rfl rfl rfl

private theorem cost_5584_1200_join0_14 : P1_7_1_3.blockEstimate 5584 1200 2992 256 = 1486091958016 :=
  @P1_7_1_3.block_append 5584 1200 2992 3120 128 128 256 719984319360 766107638656 1486091958016 cost_5584_1200_block14 cost_5584_1200_block15 rfl rfl rfl

private theorem cost_5584_1200_join0_16 : P1_7_1_3.blockEstimate 5584 1200 3248 256 = 1650435798784 :=
  @P1_7_1_3.block_append 5584 1200 3248 3376 128 128 256 807193598848 843242199936 1650435798784 cost_5584_1200_block16 cost_5584_1200_block17 rfl rfl rfl

private theorem cost_5584_1200_join0_18 : P1_7_1_3.blockEstimate 5584 1200 3504 256 = 1774480766720 :=
  @P1_7_1_3.block_append 5584 1200 3504 3632 128 128 256 874253441920 900227324800 1774480766720 cost_5584_1200_block18 cost_5584_1200_block19 rfl rfl rfl

private theorem cost_5584_1200_join0_20 : P1_7_1_3.blockEstimate 5584 1200 3760 256 = 1858226861824 :=
  @P1_7_1_3.block_append 5584 1200 3760 3888 128 128 256 921163848576 937063013248 1858226861824 cost_5584_1200_block20 cost_5584_1200_block21 rfl rfl rfl

private theorem cost_5584_1200_join0_22 : P1_7_1_3.blockEstimate 5584 1200 4016 256 = 1901674084096 :=
  @P1_7_1_3.block_append 5584 1200 4016 4144 128 128 256 947924818816 953749265280 1901674084096 cost_5584_1200_block22 cost_5584_1200_block23 rfl rfl rfl

private theorem cost_5584_1200_join0_24 : P1_7_1_3.blockEstimate 5584 1200 4272 256 = 1904822433536 :=
  @P1_7_1_3.block_append 5584 1200 4272 4400 128 128 256 954536352640 950286080896 1904822433536 cost_5584_1200_block24 cost_5584_1200_block25 rfl rfl rfl

private theorem cost_5584_1200_join0_26 : P1_7_1_3.blockEstimate 5584 1200 4528 256 = 1867671910144 :=
  @P1_7_1_3.block_append 5584 1200 4528 4656 128 128 256 940998450048 926673460096 1867671910144 cost_5584_1200_block26 cost_5584_1200_block27 rfl rfl rfl

private theorem cost_5584_1200_join0_28 : P1_7_1_3.blockEstimate 5584 1200 4784 256 = 1790222513920 :=
  @P1_7_1_3.block_append 5584 1200 4784 4912 128 128 256 907311111040 882911402880 1790222513920 cost_5584_1200_block28 cost_5584_1200_block29 rfl rfl rfl

private theorem cost_5584_1200_join0_30 : P1_7_1_3.blockEstimate 5584 1200 5040 256 = 1672474244864 :=
  @P1_7_1_3.block_append 5584 1200 5040 5168 128 128 256 853474335616 818999909248 1672474244864 cost_5584_1200_block30 cost_5584_1200_block31 rfl rfl rfl

private theorem cost_5584_1200_join0_32 : P1_7_1_3.blockEstimate 5584 1200 5296 256 = 1514427102976 :=
  @P1_7_1_3.block_append 5584 1200 5296 5424 128 128 256 779488123776 734938979200 1514427102976 cost_5584_1200_block32 cost_5584_1200_block33 rfl rfl rfl

private theorem cost_5584_1200_join0_34 : P1_7_1_3.blockEstimate 5584 1200 5552 256 = 1319317867991 :=
  @P1_7_1_3.block_append 5584 1200 5552 5680 128 128 256 685598907128 633718960863 1319317867991 cost_5584_1200_block34 cost_5584_1200_block35 rfl rfl rfl

private theorem cost_5584_1200_join0_36 : P1_7_1_3.blockEstimate 5584 1200 5808 256 = 1108494153319 :=
  @P1_7_1_3.block_append 5584 1200 5808 5936 128 128 256 580869400339 527624752980 1108494153319 cost_5584_1200_block36 cost_5584_1200_block37 rfl rfl rfl

private theorem cost_5584_1200_join0_38 : P1_7_1_3.blockEstimate 5584 1200 6064 256 = 896638203835 :=
  @P1_7_1_3.block_append 5584 1200 6064 6192 128 128 256 474529907440 422108296395 896638203835 cost_5584_1200_block38 cost_5584_1200_block39 rfl rfl rfl

private theorem cost_5584_1200_join0_40 : P1_7_1_3.blockEstimate 5584 1200 6320 256 = 692133117947 :=
  @P1_7_1_3.block_append 5584 1200 6320 6448 128 128 256 370861895379 321271222568 692133117947 cost_5584_1200_block40 cost_5584_1200_block41 rfl rfl rfl

private theorem cost_5584_1200_join0_42 : P1_7_1_3.blockEstimate 5584 1200 6576 256 = 502618168554 :=
  @P1_7_1_3.block_append 5584 1200 6576 6704 128 128 256 273795339688 228822828866 502618168554 cost_5584_1200_block42 cost_5584_1200_block43 rfl rfl rfl

private theorem cost_5584_1200_join0_44 : P1_7_1_3.blockEstimate 5584 1200 6832 256 = 334068367744 :=
  @P1_7_1_3.block_append 5584 1200 6832 6960 128 128 256 186446438592 147621929152 334068367744 cost_5584_1200_block44 cost_5584_1200_block45 rfl rfl rfl

private theorem cost_5584_1200_join0_46 : P1_7_1_3.blockEstimate 5584 1200 7088 256 = 194887205248 :=
  @P1_7_1_3.block_append 5584 1200 7088 7216 128 128 256 112763723968 82123481280 194887205248 cost_5584_1200_block46 cost_5584_1200_block47 rfl rfl rfl

private theorem cost_5584_1200_join0_48 : P1_7_1_3.blockEstimate 5584 1200 7344 256 = 90456375680 :=
  @P1_7_1_3.block_append 5584 1200 7344 7472 128 128 256 55952859328 34503516352 90456375680 cost_5584_1200_block48 cost_5584_1200_block49 rfl rfl rfl

private theorem cost_5584_1200_join0_50 : P1_7_1_3.blockEstimate 5584 1200 7600 256 = 24802410880 :=
  @P1_7_1_3.block_append 5584 1200 7600 7728 128 128 256 18027110592 6775300288 24802410880 cost_5584_1200_block50 cost_5584_1200_block51 rfl rfl rfl

private theorem cost_5584_1200_join1_0 : P1_7_1_3.blockEstimate 5584 1200 1200 512 = 117021368448 :=
  @P1_7_1_3.block_append 5584 1200 1200 1456 256 256 512 15256391744 101764976704 117021368448 cost_5584_1200_join0_0 cost_5584_1200_join0_2 rfl rfl rfl

private theorem cost_5584_1200_join1_2 : P1_7_1_3.blockEstimate 5584 1200 1712 512 = 747496628352 :=
  @P1_7_1_3.block_append 5584 1200 1712 1968 256 256 512 262605017152 484891611200 747496628352 cost_5584_1200_join0_4 cost_5584_1200_join0_6 rfl rfl rfl

private theorem cost_5584_1200_join1_4 : P1_7_1_3.blockEstimate 5584 1200 2224 512 = 1791878548604 :=
  @P1_7_1_3.block_append 5584 1200 2224 2480 256 256 512 755370890620 1036507657984 1791878548604 cost_5584_1200_join0_8 cost_5584_1200_join0_10 rfl rfl rfl

private theorem cost_5584_1200_join1_6 : P1_7_1_3.blockEstimate 5584 1200 2736 512 = 2767541202432 :=
  @P1_7_1_3.block_append 5584 1200 2736 2992 256 256 512 1281449244416 1486091958016 2767541202432 cost_5584_1200_join0_12 cost_5584_1200_join0_14 rfl rfl rfl

private theorem cost_5584_1200_join1_8 : P1_7_1_3.blockEstimate 5584 1200 3248 512 = 3424916565504 :=
  @P1_7_1_3.block_append 5584 1200 3248 3504 256 256 512 1650435798784 1774480766720 3424916565504 cost_5584_1200_join0_16 cost_5584_1200_join0_18 rfl rfl rfl

private theorem cost_5584_1200_join1_10 : P1_7_1_3.blockEstimate 5584 1200 3760 512 = 3759900945920 :=
  @P1_7_1_3.block_append 5584 1200 3760 4016 256 256 512 1858226861824 1901674084096 3759900945920 cost_5584_1200_join0_20 cost_5584_1200_join0_22 rfl rfl rfl

private theorem cost_5584_1200_join1_12 : P1_7_1_3.blockEstimate 5584 1200 4272 512 = 3772494343680 :=
  @P1_7_1_3.block_append 5584 1200 4272 4528 256 256 512 1904822433536 1867671910144 3772494343680 cost_5584_1200_join0_24 cost_5584_1200_join0_26 rfl rfl rfl

private theorem cost_5584_1200_join1_14 : P1_7_1_3.blockEstimate 5584 1200 4784 512 = 3462696758784 :=
  @P1_7_1_3.block_append 5584 1200 4784 5040 256 256 512 1790222513920 1672474244864 3462696758784 cost_5584_1200_join0_28 cost_5584_1200_join0_30 rfl rfl rfl

private theorem cost_5584_1200_join1_16 : P1_7_1_3.blockEstimate 5584 1200 5296 512 = 2833744970967 :=
  @P1_7_1_3.block_append 5584 1200 5296 5552 256 256 512 1514427102976 1319317867991 2833744970967 cost_5584_1200_join0_32 cost_5584_1200_join0_34 rfl rfl rfl

private theorem cost_5584_1200_join1_18 : P1_7_1_3.blockEstimate 5584 1200 5808 512 = 2005132357154 :=
  @P1_7_1_3.block_append 5584 1200 5808 6064 256 256 512 1108494153319 896638203835 2005132357154 cost_5584_1200_join0_36 cost_5584_1200_join0_38 rfl rfl rfl

private theorem cost_5584_1200_join1_20 : P1_7_1_3.blockEstimate 5584 1200 6320 512 = 1194751286501 :=
  @P1_7_1_3.block_append 5584 1200 6320 6576 256 256 512 692133117947 502618168554 1194751286501 cost_5584_1200_join0_40 cost_5584_1200_join0_42 rfl rfl rfl

private theorem cost_5584_1200_join1_22 : P1_7_1_3.blockEstimate 5584 1200 6832 512 = 528955572992 :=
  @P1_7_1_3.block_append 5584 1200 6832 7088 256 256 512 334068367744 194887205248 528955572992 cost_5584_1200_join0_44 cost_5584_1200_join0_46 rfl rfl rfl

private theorem cost_5584_1200_join1_24 : P1_7_1_3.blockEstimate 5584 1200 7344 512 = 115258786560 :=
  @P1_7_1_3.block_append 5584 1200 7344 7600 256 256 512 90456375680 24802410880 115258786560 cost_5584_1200_join0_48 cost_5584_1200_join0_50 rfl rfl rfl

private theorem cost_5584_1200_join2_0 : P1_7_1_3.blockEstimate 5584 1200 1200 1024 = 864517996800 :=
  @P1_7_1_3.block_append 5584 1200 1200 1712 512 512 1024 117021368448 747496628352 864517996800 cost_5584_1200_join1_0 cost_5584_1200_join1_2 rfl rfl rfl

private theorem cost_5584_1200_join2_2 : P1_7_1_3.blockEstimate 5584 1200 2224 1024 = 4559419751036 :=
  @P1_7_1_3.block_append 5584 1200 2224 2736 512 512 1024 1791878548604 2767541202432 4559419751036 cost_5584_1200_join1_4 cost_5584_1200_join1_6 rfl rfl rfl

private theorem cost_5584_1200_join2_4 : P1_7_1_3.blockEstimate 5584 1200 3248 1024 = 7184817511424 :=
  @P1_7_1_3.block_append 5584 1200 3248 3760 512 512 1024 3424916565504 3759900945920 7184817511424 cost_5584_1200_join1_8 cost_5584_1200_join1_10 rfl rfl rfl

private theorem cost_5584_1200_join2_6 : P1_7_1_3.blockEstimate 5584 1200 4272 1024 = 7235191102464 :=
  @P1_7_1_3.block_append 5584 1200 4272 4784 512 512 1024 3772494343680 3462696758784 7235191102464 cost_5584_1200_join1_12 cost_5584_1200_join1_14 rfl rfl rfl

private theorem cost_5584_1200_join2_8 : P1_7_1_3.blockEstimate 5584 1200 5296 1024 = 4838877328121 :=
  @P1_7_1_3.block_append 5584 1200 5296 5808 512 512 1024 2833744970967 2005132357154 4838877328121 cost_5584_1200_join1_16 cost_5584_1200_join1_18 rfl rfl rfl

private theorem cost_5584_1200_join2_10 : P1_7_1_3.blockEstimate 5584 1200 6320 1024 = 1723706859493 :=
  @P1_7_1_3.block_append 5584 1200 6320 6832 512 512 1024 1194751286501 528955572992 1723706859493 cost_5584_1200_join1_20 cost_5584_1200_join1_22 rfl rfl rfl

private theorem cost_5584_1200_join2_12 : P1_7_1_3.blockEstimate 5584 1200 7344 640 = 116258530240 :=
  @P1_7_1_3.block_append 5584 1200 7344 7856 512 128 640 115258786560 999743680 116258530240 cost_5584_1200_join1_24 cost_5584_1200_block52 rfl rfl rfl

private theorem cost_5584_1200_join3_0 : P1_7_1_3.blockEstimate 5584 1200 1200 2048 = 5423937747836 :=
  @P1_7_1_3.block_append 5584 1200 1200 2224 1024 1024 2048 864517996800 4559419751036 5423937747836 cost_5584_1200_join2_0 cost_5584_1200_join2_2 rfl rfl rfl

private theorem cost_5584_1200_join3_2 : P1_7_1_3.blockEstimate 5584 1200 3248 2048 = 14420008613888 :=
  @P1_7_1_3.block_append 5584 1200 3248 4272 1024 1024 2048 7184817511424 7235191102464 14420008613888 cost_5584_1200_join2_4 cost_5584_1200_join2_6 rfl rfl rfl

private theorem cost_5584_1200_join3_4 : P1_7_1_3.blockEstimate 5584 1200 5296 2048 = 6562584187614 :=
  @P1_7_1_3.block_append 5584 1200 5296 6320 1024 1024 2048 4838877328121 1723706859493 6562584187614 cost_5584_1200_join2_8 cost_5584_1200_join2_10 rfl rfl rfl

private theorem cost_5584_1200_join4_0 : P1_7_1_3.blockEstimate 5584 1200 1200 4096 = 19843946361724 :=
  @P1_7_1_3.block_append 5584 1200 1200 3248 2048 2048 4096 5423937747836 14420008613888 19843946361724 cost_5584_1200_join3_0 cost_5584_1200_join3_2 rfl rfl rfl

private theorem cost_5584_1200_join4_2 : P1_7_1_3.blockEstimate 5584 1200 5296 2688 = 6678842717854 :=
  @P1_7_1_3.block_append 5584 1200 5296 7344 2048 640 2688 6562584187614 116258530240 6678842717854 cost_5584_1200_join3_4 cost_5584_1200_join2_12 rfl rfl rfl

private theorem cost_5584_1200_join5_0 : P1_7_1_3.blockEstimate 5584 1200 1200 6784 = 26522789079578 :=
  @P1_7_1_3.block_append 5584 1200 1200 5296 4096 2688 6784 19843946361724 6678842717854 26522789079578 cost_5584_1200_join4_0 cost_5584_1200_join4_2 rfl rfl rfl

private theorem cost_5584_1200_total : P1_7_1_3.momentEstimate 5584 1200 = 26522789079578 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 5584 + 1200 = 6784 by decide]
  exact cost_5584_1200_join5_0

theorem pole_cap : P1_7_1.groupedPoleMoment shape.B shape.J ≤ moment :=
  (P1_7_1_3.grouped_bound 5584 1200).trans_eq cost_5584_1200_total
end Research6966.LargeSeed19g5

end Merged6967_Near6967LargeRank19g5

section Merged6967_Near6967LargeRank19g6
set_option Elab.async false

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace Research6966.LargeSeed19g6
open K1_14 (Shape)
def shape : Shape := ⟨3418, 4760, 1033, 443000⟩
def box : Fin 2 → ℕ := ![276875, 166125]
def nodes : ℕ := 1201742268334080
def moment : ℕ := 14115647161906

theorem node_eq : P1_7_1.nodeRows shape = nodes := by
  have rank := P1_7_1_2.six_nodeRows shape (by decide) (by decide)
  have closed : 262144*P1_7_1_2.sixPerNode (shape.m-2*shape.J) shape.J = 6*nodes := by decide
  rw [closed] at rank
  omega

private theorem cost_4760_1033_block0 : P1_7_1_3.blockEstimate 4760 1033 1033 128 = 1668860960 := by decide +kernel

private theorem cost_4760_1033_block1 : P1_7_1_3.blockEstimate 4760 1033 1161 128 = 11256388640 := by decide +kernel

private theorem cost_4760_1033_block2 : P1_7_1_3.blockEstimate 4760 1033 1289 128 = 29615254560 := by decide +kernel

private theorem cost_4760_1033_block3 : P1_7_1_3.blockEstimate 4760 1033 1417 128 = 55940152352 := by decide +kernel

private theorem cost_4760_1033_block4 : P1_7_1_3.blockEstimate 4760 1033 1545 128 = 89425775648 := by decide +kernel

private theorem cost_4760_1033_block5 : P1_7_1_3.blockEstimate 4760 1033 1673 128 = 129266818080 := by decide +kernel

private theorem cost_4760_1033_block6 : P1_7_1_3.blockEstimate 4760 1033 1801 128 = 174657973280 := by decide +kernel

private theorem cost_4760_1033_block7 : P1_7_1_3.blockEstimate 4760 1033 1929 128 = 224793934880 := by decide +kernel

private theorem cost_4760_1033_block8 : P1_7_1_3.blockEstimate 4760 1033 2057 128 = 277847630382 := by decide +kernel

private theorem cost_4760_1033_block9 : P1_7_1_3.blockEstimate 4760 1033 2185 128 = 328204471232 := by decide +kernel

private theorem cost_4760_1033_block10 : P1_7_1_3.blockEstimate 4760 1033 2313 128 = 374224849856 := by decide +kernel

private theorem cost_4760_1033_block11 : P1_7_1_3.blockEstimate 4760 1033 2441 128 = 415908318144 := by decide +kernel

private theorem cost_4760_1033_block12 : P1_7_1_3.blockEstimate 4760 1033 2569 128 = 453254876096 := by decide +kernel

private theorem cost_4760_1033_block13 : P1_7_1_3.blockEstimate 4760 1033 2697 128 = 486264523712 := by decide +kernel

private theorem cost_4760_1033_block14 : P1_7_1_3.blockEstimate 4760 1033 2825 128 = 514937260992 := by decide +kernel

private theorem cost_4760_1033_block15 : P1_7_1_3.blockEstimate 4760 1033 2953 128 = 539273087936 := by decide +kernel

private theorem cost_4760_1033_block16 : P1_7_1_3.blockEstimate 4760 1033 3081 128 = 559272004544 := by decide +kernel

private theorem cost_4760_1033_block17 : P1_7_1_3.blockEstimate 4760 1033 3209 128 = 574934010816 := by decide +kernel

private theorem cost_4760_1033_block18 : P1_7_1_3.blockEstimate 4760 1033 3337 128 = 586259106752 := by decide +kernel

private theorem cost_4760_1033_block19 : P1_7_1_3.blockEstimate 4760 1033 3465 128 = 593247292352 := by decide +kernel

private theorem cost_4760_1033_block20 : P1_7_1_3.blockEstimate 4760 1033 3593 128 = 595898567616 := by decide +kernel

private theorem cost_4760_1033_block21 : P1_7_1_3.blockEstimate 4760 1033 3721 128 = 594212932544 := by decide +kernel

private theorem cost_4760_1033_block22 : P1_7_1_3.blockEstimate 4760 1033 3849 128 = 588190387136 := by decide +kernel

private theorem cost_4760_1033_block23 : P1_7_1_3.blockEstimate 4760 1033 3977 128 = 577830931392 := by decide +kernel

private theorem cost_4760_1033_block24 : P1_7_1_3.blockEstimate 4760 1033 4105 128 = 563134565312 := by decide +kernel

private theorem cost_4760_1033_block25 : P1_7_1_3.blockEstimate 4760 1033 4233 128 = 544101288896 := by decide +kernel

private theorem cost_4760_1033_block26 : P1_7_1_3.blockEstimate 4760 1033 4361 128 = 520731102144 := by decide +kernel

private theorem cost_4760_1033_block27 : P1_7_1_3.blockEstimate 4760 1033 4489 128 = 493024005056 := by decide +kernel

private theorem cost_4760_1033_block28 : P1_7_1_3.blockEstimate 4760 1033 4617 128 = 460979997632 := by decide +kernel

private theorem cost_4760_1033_block29 : P1_7_1_3.blockEstimate 4760 1033 4745 128 = 424942657445 := by decide +kernel

private theorem cost_4760_1033_block30 : P1_7_1_3.blockEstimate 4760 1033 4873 128 = 387012931427 := by decide +kernel

private theorem cost_4760_1033_block31 : P1_7_1_3.blockEstimate 4760 1033 5001 128 = 348380434642 := by decide +kernel

private theorem cost_4760_1033_block32 : P1_7_1_3.blockEstimate 4760 1033 5129 128 = 309602797279 := by decide +kernel

private theorem cost_4760_1033_block33 : P1_7_1_3.blockEstimate 4760 1033 5257 128 = 271212055068 := by decide +kernel

private theorem cost_4760_1033_block34 : P1_7_1_3.blockEstimate 4760 1033 5385 128 = 233715321203 := by decide +kernel

private theorem cost_4760_1033_block35 : P1_7_1_3.blockEstimate 4760 1033 5513 128 = 197594786647 := by decide +kernel

private theorem cost_4760_1033_block36 : P1_7_1_3.blockEstimate 4760 1033 5641 128 = 163307719596 := by decide +kernel

private theorem cost_4760_1033_block37 : P1_7_1_3.blockEstimate 4760 1033 5769 128 = 131137581205 := by decide +kernel

private theorem cost_4760_1033_block38 : P1_7_1_3.blockEstimate 4760 1033 5897 128 = 101523489392 := by decide +kernel

private theorem cost_4760_1033_block39 : P1_7_1_3.blockEstimate 4760 1033 6025 128 = 75188768368 := by decide +kernel

private theorem cost_4760_1033_block40 : P1_7_1_3.blockEstimate 4760 1033 6153 128 = 52394760816 := by decide +kernel

private theorem cost_4760_1033_block41 : P1_7_1_3.blockEstimate 4760 1033 6281 128 = 33393124976 := by decide +kernel

private theorem cost_4760_1033_block42 : P1_7_1_3.blockEstimate 4760 1033 6409 128 = 18435519088 := by decide +kernel

private theorem cost_4760_1033_block43 : P1_7_1_3.blockEstimate 4760 1033 6537 128 = 7773601392 := by decide +kernel

private theorem cost_4760_1033_block44 : P1_7_1_3.blockEstimate 4760 1033 6665 128 = 1659030128 := by decide +kernel

private theorem cost_4760_1033_block45 : P1_7_1_3.blockEstimate 4760 1033 6793 33 = 16214292 := by decide +kernel

private theorem cost_4760_1033_join0_0 : P1_7_1_3.blockEstimate 4760 1033 1033 256 = 12925249600 :=
  @P1_7_1_3.block_append 4760 1033 1033 1161 128 128 256 1668860960 11256388640 12925249600 cost_4760_1033_block0 cost_4760_1033_block1 rfl rfl rfl

private theorem cost_4760_1033_join0_2 : P1_7_1_3.blockEstimate 4760 1033 1289 256 = 85555406912 :=
  @P1_7_1_3.block_append 4760 1033 1289 1417 128 128 256 29615254560 55940152352 85555406912 cost_4760_1033_block2 cost_4760_1033_block3 rfl rfl rfl

private theorem cost_4760_1033_join0_4 : P1_7_1_3.blockEstimate 4760 1033 1545 256 = 218692593728 :=
  @P1_7_1_3.block_append 4760 1033 1545 1673 128 128 256 89425775648 129266818080 218692593728 cost_4760_1033_block4 cost_4760_1033_block5 rfl rfl rfl

private theorem cost_4760_1033_join0_6 : P1_7_1_3.blockEstimate 4760 1033 1801 256 = 399451908160 :=
  @P1_7_1_3.block_append 4760 1033 1801 1929 128 128 256 174657973280 224793934880 399451908160 cost_4760_1033_block6 cost_4760_1033_block7 rfl rfl rfl

private theorem cost_4760_1033_join0_8 : P1_7_1_3.blockEstimate 4760 1033 2057 256 = 606052101614 :=
  @P1_7_1_3.block_append 4760 1033 2057 2185 128 128 256 277847630382 328204471232 606052101614 cost_4760_1033_block8 cost_4760_1033_block9 rfl rfl rfl

private theorem cost_4760_1033_join0_10 : P1_7_1_3.blockEstimate 4760 1033 2313 256 = 790133168000 :=
  @P1_7_1_3.block_append 4760 1033 2313 2441 128 128 256 374224849856 415908318144 790133168000 cost_4760_1033_block10 cost_4760_1033_block11 rfl rfl rfl

private theorem cost_4760_1033_join0_12 : P1_7_1_3.blockEstimate 4760 1033 2569 256 = 939519399808 :=
  @P1_7_1_3.block_append 4760 1033 2569 2697 128 128 256 453254876096 486264523712 939519399808 cost_4760_1033_block12 cost_4760_1033_block13 rfl rfl rfl

private theorem cost_4760_1033_join0_14 : P1_7_1_3.blockEstimate 4760 1033 2825 256 = 1054210348928 :=
  @P1_7_1_3.block_append 4760 1033 2825 2953 128 128 256 514937260992 539273087936 1054210348928 cost_4760_1033_block14 cost_4760_1033_block15 rfl rfl rfl

private theorem cost_4760_1033_join0_16 : P1_7_1_3.blockEstimate 4760 1033 3081 256 = 1134206015360 :=
  @P1_7_1_3.block_append 4760 1033 3081 3209 128 128 256 559272004544 574934010816 1134206015360 cost_4760_1033_block16 cost_4760_1033_block17 rfl rfl rfl

private theorem cost_4760_1033_join0_18 : P1_7_1_3.blockEstimate 4760 1033 3337 256 = 1179506399104 :=
  @P1_7_1_3.block_append 4760 1033 3337 3465 128 128 256 586259106752 593247292352 1179506399104 cost_4760_1033_block18 cost_4760_1033_block19 rfl rfl rfl

private theorem cost_4760_1033_join0_20 : P1_7_1_3.blockEstimate 4760 1033 3593 256 = 1190111500160 :=
  @P1_7_1_3.block_append 4760 1033 3593 3721 128 128 256 595898567616 594212932544 1190111500160 cost_4760_1033_block20 cost_4760_1033_block21 rfl rfl rfl

private theorem cost_4760_1033_join0_22 : P1_7_1_3.blockEstimate 4760 1033 3849 256 = 1166021318528 :=
  @P1_7_1_3.block_append 4760 1033 3849 3977 128 128 256 588190387136 577830931392 1166021318528 cost_4760_1033_block22 cost_4760_1033_block23 rfl rfl rfl

private theorem cost_4760_1033_join0_24 : P1_7_1_3.blockEstimate 4760 1033 4105 256 = 1107235854208 :=
  @P1_7_1_3.block_append 4760 1033 4105 4233 128 128 256 563134565312 544101288896 1107235854208 cost_4760_1033_block24 cost_4760_1033_block25 rfl rfl rfl

private theorem cost_4760_1033_join0_26 : P1_7_1_3.blockEstimate 4760 1033 4361 256 = 1013755107200 :=
  @P1_7_1_3.block_append 4760 1033 4361 4489 128 128 256 520731102144 493024005056 1013755107200 cost_4760_1033_block26 cost_4760_1033_block27 rfl rfl rfl

private theorem cost_4760_1033_join0_28 : P1_7_1_3.blockEstimate 4760 1033 4617 256 = 885922655077 :=
  @P1_7_1_3.block_append 4760 1033 4617 4745 128 128 256 460979997632 424942657445 885922655077 cost_4760_1033_block28 cost_4760_1033_block29 rfl rfl rfl

private theorem cost_4760_1033_join0_30 : P1_7_1_3.blockEstimate 4760 1033 4873 256 = 735393366069 :=
  @P1_7_1_3.block_append 4760 1033 4873 5001 128 128 256 387012931427 348380434642 735393366069 cost_4760_1033_block30 cost_4760_1033_block31 rfl rfl rfl

private theorem cost_4760_1033_join0_32 : P1_7_1_3.blockEstimate 4760 1033 5129 256 = 580814852347 :=
  @P1_7_1_3.block_append 4760 1033 5129 5257 128 128 256 309602797279 271212055068 580814852347 cost_4760_1033_block32 cost_4760_1033_block33 rfl rfl rfl

private theorem cost_4760_1033_join0_34 : P1_7_1_3.blockEstimate 4760 1033 5385 256 = 431310107850 :=
  @P1_7_1_3.block_append 4760 1033 5385 5513 128 128 256 233715321203 197594786647 431310107850 cost_4760_1033_block34 cost_4760_1033_block35 rfl rfl rfl

private theorem cost_4760_1033_join0_36 : P1_7_1_3.blockEstimate 4760 1033 5641 256 = 294445300801 :=
  @P1_7_1_3.block_append 4760 1033 5641 5769 128 128 256 163307719596 131137581205 294445300801 cost_4760_1033_block36 cost_4760_1033_block37 rfl rfl rfl

private theorem cost_4760_1033_join0_38 : P1_7_1_3.blockEstimate 4760 1033 5897 256 = 176712257760 :=
  @P1_7_1_3.block_append 4760 1033 5897 6025 128 128 256 101523489392 75188768368 176712257760 cost_4760_1033_block38 cost_4760_1033_block39 rfl rfl rfl

private theorem cost_4760_1033_join0_40 : P1_7_1_3.blockEstimate 4760 1033 6153 256 = 85787885792 :=
  @P1_7_1_3.block_append 4760 1033 6153 6281 128 128 256 52394760816 33393124976 85787885792 cost_4760_1033_block40 cost_4760_1033_block41 rfl rfl rfl

private theorem cost_4760_1033_join0_42 : P1_7_1_3.blockEstimate 4760 1033 6409 256 = 26209120480 :=
  @P1_7_1_3.block_append 4760 1033 6409 6537 128 128 256 18435519088 7773601392 26209120480 cost_4760_1033_block42 cost_4760_1033_block43 rfl rfl rfl

private theorem cost_4760_1033_join0_44 : P1_7_1_3.blockEstimate 4760 1033 6665 161 = 1675244420 :=
  @P1_7_1_3.block_append 4760 1033 6665 6793 128 33 161 1659030128 16214292 1675244420 cost_4760_1033_block44 cost_4760_1033_block45 rfl rfl rfl

private theorem cost_4760_1033_join1_0 : P1_7_1_3.blockEstimate 4760 1033 1033 512 = 98480656512 :=
  @P1_7_1_3.block_append 4760 1033 1033 1289 256 256 512 12925249600 85555406912 98480656512 cost_4760_1033_join0_0 cost_4760_1033_join0_2 rfl rfl rfl

private theorem cost_4760_1033_join1_2 : P1_7_1_3.blockEstimate 4760 1033 1545 512 = 618144501888 :=
  @P1_7_1_3.block_append 4760 1033 1545 1801 256 256 512 218692593728 399451908160 618144501888 cost_4760_1033_join0_4 cost_4760_1033_join0_6 rfl rfl rfl

private theorem cost_4760_1033_join1_4 : P1_7_1_3.blockEstimate 4760 1033 2057 512 = 1396185269614 :=
  @P1_7_1_3.block_append 4760 1033 2057 2313 256 256 512 606052101614 790133168000 1396185269614 cost_4760_1033_join0_8 cost_4760_1033_join0_10 rfl rfl rfl

private theorem cost_4760_1033_join1_6 : P1_7_1_3.blockEstimate 4760 1033 2569 512 = 1993729748736 :=
  @P1_7_1_3.block_append 4760 1033 2569 2825 256 256 512 939519399808 1054210348928 1993729748736 cost_4760_1033_join0_12 cost_4760_1033_join0_14 rfl rfl rfl

private theorem cost_4760_1033_join1_8 : P1_7_1_3.blockEstimate 4760 1033 3081 512 = 2313712414464 :=
  @P1_7_1_3.block_append 4760 1033 3081 3337 256 256 512 1134206015360 1179506399104 2313712414464 cost_4760_1033_join0_16 cost_4760_1033_join0_18 rfl rfl rfl

private theorem cost_4760_1033_join1_10 : P1_7_1_3.blockEstimate 4760 1033 3593 512 = 2356132818688 :=
  @P1_7_1_3.block_append 4760 1033 3593 3849 256 256 512 1190111500160 1166021318528 2356132818688 cost_4760_1033_join0_20 cost_4760_1033_join0_22 rfl rfl rfl

private theorem cost_4760_1033_join1_12 : P1_7_1_3.blockEstimate 4760 1033 4105 512 = 2120990961408 :=
  @P1_7_1_3.block_append 4760 1033 4105 4361 256 256 512 1107235854208 1013755107200 2120990961408 cost_4760_1033_join0_24 cost_4760_1033_join0_26 rfl rfl rfl

private theorem cost_4760_1033_join1_14 : P1_7_1_3.blockEstimate 4760 1033 4617 512 = 1621316021146 :=
  @P1_7_1_3.block_append 4760 1033 4617 4873 256 256 512 885922655077 735393366069 1621316021146 cost_4760_1033_join0_28 cost_4760_1033_join0_30 rfl rfl rfl

private theorem cost_4760_1033_join1_16 : P1_7_1_3.blockEstimate 4760 1033 5129 512 = 1012124960197 :=
  @P1_7_1_3.block_append 4760 1033 5129 5385 256 256 512 580814852347 431310107850 1012124960197 cost_4760_1033_join0_32 cost_4760_1033_join0_34 rfl rfl rfl

private theorem cost_4760_1033_join1_18 : P1_7_1_3.blockEstimate 4760 1033 5641 512 = 471157558561 :=
  @P1_7_1_3.block_append 4760 1033 5641 5897 256 256 512 294445300801 176712257760 471157558561 cost_4760_1033_join0_36 cost_4760_1033_join0_38 rfl rfl rfl

private theorem cost_4760_1033_join1_20 : P1_7_1_3.blockEstimate 4760 1033 6153 512 = 111997006272 :=
  @P1_7_1_3.block_append 4760 1033 6153 6409 256 256 512 85787885792 26209120480 111997006272 cost_4760_1033_join0_40 cost_4760_1033_join0_42 rfl rfl rfl

private theorem cost_4760_1033_join2_0 : P1_7_1_3.blockEstimate 4760 1033 1033 1024 = 716625158400 :=
  @P1_7_1_3.block_append 4760 1033 1033 1545 512 512 1024 98480656512 618144501888 716625158400 cost_4760_1033_join1_0 cost_4760_1033_join1_2 rfl rfl rfl

private theorem cost_4760_1033_join2_2 : P1_7_1_3.blockEstimate 4760 1033 2057 1024 = 3389915018350 :=
  @P1_7_1_3.block_append 4760 1033 2057 2569 512 512 1024 1396185269614 1993729748736 3389915018350 cost_4760_1033_join1_4 cost_4760_1033_join1_6 rfl rfl rfl

private theorem cost_4760_1033_join2_4 : P1_7_1_3.blockEstimate 4760 1033 3081 1024 = 4669845233152 :=
  @P1_7_1_3.block_append 4760 1033 3081 3593 512 512 1024 2313712414464 2356132818688 4669845233152 cost_4760_1033_join1_8 cost_4760_1033_join1_10 rfl rfl rfl

private theorem cost_4760_1033_join2_6 : P1_7_1_3.blockEstimate 4760 1033 4105 1024 = 3742306982554 :=
  @P1_7_1_3.block_append 4760 1033 4105 4617 512 512 1024 2120990961408 1621316021146 3742306982554 cost_4760_1033_join1_12 cost_4760_1033_join1_14 rfl rfl rfl

private theorem cost_4760_1033_join2_8 : P1_7_1_3.blockEstimate 4760 1033 5129 1024 = 1483282518758 :=
  @P1_7_1_3.block_append 4760 1033 5129 5641 512 512 1024 1012124960197 471157558561 1483282518758 cost_4760_1033_join1_16 cost_4760_1033_join1_18 rfl rfl rfl

private theorem cost_4760_1033_join2_10 : P1_7_1_3.blockEstimate 4760 1033 6153 673 = 113672250692 :=
  @P1_7_1_3.block_append 4760 1033 6153 6665 512 161 673 111997006272 1675244420 113672250692 cost_4760_1033_join1_20 cost_4760_1033_join0_44 rfl rfl rfl

private theorem cost_4760_1033_join3_0 : P1_7_1_3.blockEstimate 4760 1033 1033 2048 = 4106540176750 :=
  @P1_7_1_3.block_append 4760 1033 1033 2057 1024 1024 2048 716625158400 3389915018350 4106540176750 cost_4760_1033_join2_0 cost_4760_1033_join2_2 rfl rfl rfl

private theorem cost_4760_1033_join3_2 : P1_7_1_3.blockEstimate 4760 1033 3081 2048 = 8412152215706 :=
  @P1_7_1_3.block_append 4760 1033 3081 4105 1024 1024 2048 4669845233152 3742306982554 8412152215706 cost_4760_1033_join2_4 cost_4760_1033_join2_6 rfl rfl rfl

private theorem cost_4760_1033_join3_4 : P1_7_1_3.blockEstimate 4760 1033 5129 1697 = 1596954769450 :=
  @P1_7_1_3.block_append 4760 1033 5129 6153 1024 673 1697 1483282518758 113672250692 1596954769450 cost_4760_1033_join2_8 cost_4760_1033_join2_10 rfl rfl rfl

private theorem cost_4760_1033_join4_0 : P1_7_1_3.blockEstimate 4760 1033 1033 4096 = 12518692392456 :=
  @P1_7_1_3.block_append 4760 1033 1033 3081 2048 2048 4096 4106540176750 8412152215706 12518692392456 cost_4760_1033_join3_0 cost_4760_1033_join3_2 rfl rfl rfl

private theorem cost_4760_1033_join5_0 : P1_7_1_3.blockEstimate 4760 1033 1033 5793 = 14115647161906 :=
  @P1_7_1_3.block_append 4760 1033 1033 5129 4096 1697 5793 12518692392456 1596954769450 14115647161906 cost_4760_1033_join4_0 cost_4760_1033_join3_4 rfl rfl rfl

private theorem cost_4760_1033_total : P1_7_1_3.momentEstimate 4760 1033 = 14115647161906 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 4760 + 1033 = 5793 by decide]
  exact cost_4760_1033_join5_0

theorem pole_cap : P1_7_1.groupedPoleMoment shape.B shape.J ≤ moment :=
  (P1_7_1_3.grouped_bound 4760 1033).trans_eq cost_4760_1033_total
end Research6966.LargeSeed19g6

end Merged6967_Near6967LargeRank19g6

section Merged6967_Near6967SpreadRanks
set_option Elab.async false

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace Research6966.SpreadCatalogue
open K1_14 (Shape)
def shape : Shape := ⟨4001, 5585, 1200, 443000⟩
def box : Fin 2 → ℕ := ![221500, 221500]
def nodes : ℕ := 1915959850041344
def moment : ℕ := 26538075533683

theorem node_eq : P1_7_1.nodeRows shape = nodes := by
  have rank := P1_7_1_2.six_nodeRows shape (by decide) (by decide)
  have closed : 262144*P1_7_1_2.sixPerNode (shape.m-2*shape.J) shape.J = 6*nodes := by decide
  rw [closed] at rank
  omega

private theorem cost_5585_1200_block0 : P1_7_1_3.blockEstimate 5585 1200 1200 128 = 1964012960 := by decide +kernel

private theorem cost_5585_1200_block1 : P1_7_1_3.blockEstimate 5585 1200 1328 128 = 13295207840 := by decide +kernel

private theorem cost_5585_1200_block2 : P1_7_1_3.blockEstimate 5585 1200 1456 128 = 35127891360 := by decide +kernel

private theorem cost_5585_1200_block3 : P1_7_1_3.blockEstimate 5585 1200 1584 128 = 66656757152 := by decide +kernel

private theorem cost_5585_1200_block4 : P1_7_1_3.blockEstimate 5585 1200 1712 128 = 107076498848 := by decide +kernel

private theorem cost_5585_1200_block5 : P1_7_1_3.blockEstimate 5585 1200 1840 128 = 155581810080 := by decide +kernel

private theorem cost_5585_1200_block6 : P1_7_1_3.blockEstimate 5585 1200 1968 128 = 211367384480 := by decide +kernel

private theorem cost_5585_1200_block7 : P1_7_1_3.blockEstimate 5585 1200 2096 128 = 273627915680 := by decide +kernel

private theorem cost_5585_1200_block8 : P1_7_1_3.blockEstimate 5585 1200 2224 128 = 341558097312 := by decide +kernel

private theorem cost_5585_1200_block9 : P1_7_1_3.blockEstimate 5585 1200 2352 128 = 413983571348 := by decide +kernel

private theorem cost_5585_1200_block10 : P1_7_1_3.blockEstimate 5585 1200 2480 128 = 485231901632 := by decide +kernel

private theorem cost_5585_1200_block11 : P1_7_1_3.blockEstimate 5585 1200 2608 128 = 551524334528 := by decide +kernel

private theorem cost_5585_1200_block12 : P1_7_1_3.blockEstimate 5585 1200 2736 128 = 612779408320 := by decide +kernel

private theorem cost_5585_1200_block13 : P1_7_1_3.blockEstimate 5585 1200 2864 128 = 668997123008 := by decide +kernel

private theorem cost_5585_1200_block14 : P1_7_1_3.blockEstimate 5585 1200 2992 128 = 720177478592 := by decide +kernel

private theorem cost_5585_1200_block15 : P1_7_1_3.blockEstimate 5585 1200 3120 128 = 766320475072 := by decide +kernel

private theorem cost_5585_1200_block16 : P1_7_1_3.blockEstimate 5585 1200 3248 128 = 807426112448 := by decide +kernel

private theorem cost_5585_1200_block17 : P1_7_1_3.blockEstimate 5585 1200 3376 128 = 843494390720 := by decide +kernel

private theorem cost_5585_1200_block18 : P1_7_1_3.blockEstimate 5585 1200 3504 128 = 874525309888 := by decide +kernel

private theorem cost_5585_1200_block19 : P1_7_1_3.blockEstimate 5585 1200 3632 128 = 900518869952 := by decide +kernel

private theorem cost_5585_1200_block20 : P1_7_1_3.blockEstimate 5585 1200 3760 128 = 921475070912 := by decide +kernel

private theorem cost_5585_1200_block21 : P1_7_1_3.blockEstimate 5585 1200 3888 128 = 937393912768 := by decide +kernel

private theorem cost_5585_1200_block22 : P1_7_1_3.blockEstimate 5585 1200 4016 128 = 948275395520 := by decide +kernel

private theorem cost_5585_1200_block23 : P1_7_1_3.blockEstimate 5585 1200 4144 128 = 954119519168 := by decide +kernel

private theorem cost_5585_1200_block24 : P1_7_1_3.blockEstimate 5585 1200 4272 128 = 954926283712 := by decide +kernel

private theorem cost_5585_1200_block25 : P1_7_1_3.blockEstimate 5585 1200 4400 128 = 950695689152 := by decide +kernel

private theorem cost_5585_1200_block26 : P1_7_1_3.blockEstimate 5585 1200 4528 128 = 941427735488 := by decide +kernel

private theorem cost_5585_1200_block27 : P1_7_1_3.blockEstimate 5585 1200 4656 128 = 927122422720 := by decide +kernel

private theorem cost_5585_1200_block28 : P1_7_1_3.blockEstimate 5585 1200 4784 128 = 907779750848 := by decide +kernel

private theorem cost_5585_1200_block29 : P1_7_1_3.blockEstimate 5585 1200 4912 128 = 883399719872 := by decide +kernel

private theorem cost_5585_1200_block30 : P1_7_1_3.blockEstimate 5585 1200 5040 128 = 853982329792 := by decide +kernel

private theorem cost_5585_1200_block31 : P1_7_1_3.blockEstimate 5585 1200 5168 128 = 819527580608 := by decide +kernel

private theorem cost_5585_1200_block32 : P1_7_1_3.blockEstimate 5585 1200 5296 128 = 780035472320 := by decide +kernel

private theorem cost_5585_1200_block33 : P1_7_1_3.blockEstimate 5585 1200 5424 128 = 735506004928 := by decide +kernel

private theorem cost_5585_1200_block34 : P1_7_1_3.blockEstimate 5585 1200 5552 128 = 686178018303 := by decide +kernel

private theorem cost_5585_1200_block35 : P1_7_1_3.blockEstimate 5585 1200 5680 128 = 634289780073 := by decide +kernel

private theorem cost_5585_1200_block36 : P1_7_1_3.blockEstimate 5585 1200 5808 128 = 581427661381 := by decide +kernel

private theorem cost_5585_1200_block37 : P1_7_1_3.blockEstimate 5585 1200 5936 128 = 528167163137 := by decide +kernel

private theorem cost_5585_1200_block38 : P1_7_1_3.blockEstimate 5585 1200 6064 128 = 475053341610 := by decide +kernel

private theorem cost_5585_1200_block39 : P1_7_1_3.blockEstimate 5585 1200 6192 128 = 422609796993 := by decide +kernel

private theorem cost_5585_1200_block40 : P1_7_1_3.blockEstimate 5585 1200 6320 128 = 371338672337 := by decide +kernel

private theorem cost_5585_1200_block41 : P1_7_1_3.blockEstimate 5585 1200 6448 128 = 321720653524 := by decide +kernel

private theorem cost_5585_1200_block42 : P1_7_1_3.blockEstimate 5585 1200 6576 128 = 274214970103 := by decide +kernel

private theorem cost_5585_1200_block43 : P1_7_1_3.blockEstimate 5585 1200 6704 128 = 229212292777 := by decide +kernel

private theorem cost_5585_1200_block44 : P1_7_1_3.blockEstimate 5585 1200 6832 128 = 186802804176 := by decide +kernel

private theorem cost_5585_1200_block45 : P1_7_1_3.blockEstimate 5585 1200 6960 128 = 147939889616 := by decide +kernel

private theorem cost_5585_1200_block46 : P1_7_1_3.blockEstimate 5585 1200 7088 128 = 113042361808 := by decide +kernel

private theorem cost_5585_1200_block47 : P1_7_1_3.blockEstimate 5585 1200 7216 128 = 82361878992 := by decide +kernel

private theorem cost_5585_1200_block48 : P1_7_1_3.blockEstimate 5585 1200 7344 128 = 56150099408 := by decide +kernel

private theorem cost_5585_1200_block49 : P1_7_1_3.blockEstimate 5585 1200 7472 128 = 34658681296 := by decide +kernel

private theorem cost_5585_1200_block50 : P1_7_1_3.blockEstimate 5585 1200 7600 128 = 18139282896 := by decide +kernel

private theorem cost_5585_1200_block51 : P1_7_1_3.blockEstimate 5585 1200 7728 128 = 6843562448 := by decide +kernel

private theorem cost_5585_1200_block52 : P1_7_1_3.blockEstimate 5585 1200 7856 128 = 1023178192 := by decide +kernel

private theorem cost_5585_1200_block53 : P1_7_1_3.blockEstimate 5585 1200 7984 1 = 5585 := by decide +kernel

private theorem cost_5585_1200_join0_0 : P1_7_1_3.blockEstimate 5585 1200 1200 256 = 15259220800 :=
  @P1_7_1_3.block_append 5585 1200 1200 1328 128 128 256 1964012960 13295207840 15259220800 cost_5585_1200_block0 cost_5585_1200_block1 rfl rfl rfl

private theorem cost_5585_1200_join0_2 : P1_7_1_3.blockEstimate 5585 1200 1456 256 = 101784648512 :=
  @P1_7_1_3.block_append 5585 1200 1456 1584 128 128 256 35127891360 66656757152 101784648512 cost_5585_1200_block2 cost_5585_1200_block3 rfl rfl rfl

private theorem cost_5585_1200_join0_4 : P1_7_1_3.blockEstimate 5585 1200 1712 256 = 262658308928 :=
  @P1_7_1_3.block_append 5585 1200 1712 1840 128 128 256 107076498848 155581810080 262658308928 cost_5585_1200_block4 cost_5585_1200_block5 rfl rfl rfl

private theorem cost_5585_1200_join0_6 : P1_7_1_3.blockEstimate 5585 1200 1968 256 = 484995300160 :=
  @P1_7_1_3.block_append 5585 1200 1968 2096 128 128 256 211367384480 273627915680 484995300160 cost_5585_1200_block6 cost_5585_1200_block7 rfl rfl rfl

private theorem cost_5585_1200_join0_8 : P1_7_1_3.blockEstimate 5585 1200 2224 256 = 755541668660 :=
  @P1_7_1_3.block_append 5585 1200 2224 2352 128 128 256 341558097312 413983571348 755541668660 cost_5585_1200_block8 cost_5585_1200_block9 rfl rfl rfl

private theorem cost_5585_1200_join0_10 : P1_7_1_3.blockEstimate 5585 1200 2480 256 = 1036756236160 :=
  @P1_7_1_3.block_append 5585 1200 2480 2608 128 128 256 485231901632 551524334528 1036756236160 cost_5585_1200_block10 cost_5585_1200_block11 rfl rfl rfl

private theorem cost_5585_1200_join0_12 : P1_7_1_3.blockEstimate 5585 1200 2736 256 = 1281776531328 :=
  @P1_7_1_3.block_append 5585 1200 2736 2864 128 128 256 612779408320 668997123008 1281776531328 cost_5585_1200_block12 cost_5585_1200_block13 rfl rfl rfl

private theorem cost_5585_1200_join0_14 : P1_7_1_3.blockEstimate 5585 1200 2992 256 = 1486497953664 :=
  @P1_7_1_3.block_append 5585 1200 2992 3120 128 128 256 720177478592 766320475072 1486497953664 cost_5585_1200_block14 cost_5585_1200_block15 rfl rfl rfl

private theorem cost_5585_1200_join0_16 : P1_7_1_3.blockEstimate 5585 1200 3248 256 = 1650920503168 :=
  @P1_7_1_3.block_append 5585 1200 3248 3376 128 128 256 807426112448 843494390720 1650920503168 cost_5585_1200_block16 cost_5585_1200_block17 rfl rfl rfl

private theorem cost_5585_1200_join0_18 : P1_7_1_3.blockEstimate 5585 1200 3504 256 = 1775044179840 :=
  @P1_7_1_3.block_append 5585 1200 3504 3632 128 128 256 874525309888 900518869952 1775044179840 cost_5585_1200_block18 cost_5585_1200_block19 rfl rfl rfl

private theorem cost_5585_1200_join0_20 : P1_7_1_3.blockEstimate 5585 1200 3760 256 = 1858868983680 :=
  @P1_7_1_3.block_append 5585 1200 3760 3888 128 128 256 921475070912 937393912768 1858868983680 cost_5585_1200_block20 cost_5585_1200_block21 rfl rfl rfl

private theorem cost_5585_1200_join0_22 : P1_7_1_3.blockEstimate 5585 1200 4016 256 = 1902394914688 :=
  @P1_7_1_3.block_append 5585 1200 4016 4144 128 128 256 948275395520 954119519168 1902394914688 cost_5585_1200_block22 cost_5585_1200_block23 rfl rfl rfl

private theorem cost_5585_1200_join0_24 : P1_7_1_3.blockEstimate 5585 1200 4272 256 = 1905621972864 :=
  @P1_7_1_3.block_append 5585 1200 4272 4400 128 128 256 954926283712 950695689152 1905621972864 cost_5585_1200_block24 cost_5585_1200_block25 rfl rfl rfl

private theorem cost_5585_1200_join0_26 : P1_7_1_3.blockEstimate 5585 1200 4528 256 = 1868550158208 :=
  @P1_7_1_3.block_append 5585 1200 4528 4656 128 128 256 941427735488 927122422720 1868550158208 cost_5585_1200_block26 cost_5585_1200_block27 rfl rfl rfl

private theorem cost_5585_1200_join0_28 : P1_7_1_3.blockEstimate 5585 1200 4784 256 = 1791179470720 :=
  @P1_7_1_3.block_append 5585 1200 4784 4912 128 128 256 907779750848 883399719872 1791179470720 cost_5585_1200_block28 cost_5585_1200_block29 rfl rfl rfl

private theorem cost_5585_1200_join0_30 : P1_7_1_3.blockEstimate 5585 1200 5040 256 = 1673509910400 :=
  @P1_7_1_3.block_append 5585 1200 5040 5168 128 128 256 853982329792 819527580608 1673509910400 cost_5585_1200_block30 cost_5585_1200_block31 rfl rfl rfl

private theorem cost_5585_1200_join0_32 : P1_7_1_3.blockEstimate 5585 1200 5296 256 = 1515541477248 :=
  @P1_7_1_3.block_append 5585 1200 5296 5424 128 128 256 780035472320 735506004928 1515541477248 cost_5585_1200_block32 cost_5585_1200_block33 rfl rfl rfl

private theorem cost_5585_1200_join0_34 : P1_7_1_3.blockEstimate 5585 1200 5552 256 = 1320467798376 :=
  @P1_7_1_3.block_append 5585 1200 5552 5680 128 128 256 686178018303 634289780073 1320467798376 cost_5585_1200_block34 cost_5585_1200_block35 rfl rfl rfl

private theorem cost_5585_1200_join0_36 : P1_7_1_3.blockEstimate 5585 1200 5808 256 = 1109594824518 :=
  @P1_7_1_3.block_append 5585 1200 5808 5936 128 128 256 581427661381 528167163137 1109594824518 cost_5585_1200_block36 cost_5585_1200_block37 rfl rfl rfl

private theorem cost_5585_1200_join0_38 : P1_7_1_3.blockEstimate 5585 1200 6064 256 = 897663138603 :=
  @P1_7_1_3.block_append 5585 1200 6064 6192 128 128 256 475053341610 422609796993 897663138603 cost_5585_1200_block38 cost_5585_1200_block39 rfl rfl rfl

private theorem cost_5585_1200_join0_40 : P1_7_1_3.blockEstimate 5585 1200 6320 256 = 693059325861 :=
  @P1_7_1_3.block_append 5585 1200 6320 6448 128 128 256 371338672337 321720653524 693059325861 cost_5585_1200_block40 cost_5585_1200_block41 rfl rfl rfl

private theorem cost_5585_1200_join0_42 : P1_7_1_3.blockEstimate 5585 1200 6576 256 = 503427262880 :=
  @P1_7_1_3.block_append 5585 1200 6576 6704 128 128 256 274214970103 229212292777 503427262880 cost_5585_1200_block42 cost_5585_1200_block43 rfl rfl rfl

private theorem cost_5585_1200_join0_44 : P1_7_1_3.blockEstimate 5585 1200 6832 256 = 334742693792 :=
  @P1_7_1_3.block_append 5585 1200 6832 6960 128 128 256 186802804176 147939889616 334742693792 cost_5585_1200_block44 cost_5585_1200_block45 rfl rfl rfl

private theorem cost_5585_1200_join0_46 : P1_7_1_3.blockEstimate 5585 1200 7088 256 = 195404240800 :=
  @P1_7_1_3.block_append 5585 1200 7088 7216 128 128 256 113042361808 82361878992 195404240800 cost_5585_1200_block46 cost_5585_1200_block47 rfl rfl rfl

private theorem cost_5585_1200_join0_48 : P1_7_1_3.blockEstimate 5585 1200 7344 256 = 90808780704 :=
  @P1_7_1_3.block_append 5585 1200 7344 7472 128 128 256 56150099408 34658681296 90808780704 cost_5585_1200_block48 cost_5585_1200_block49 rfl rfl rfl

private theorem cost_5585_1200_join0_50 : P1_7_1_3.blockEstimate 5585 1200 7600 256 = 24982845344 :=
  @P1_7_1_3.block_append 5585 1200 7600 7728 128 128 256 18139282896 6843562448 24982845344 cost_5585_1200_block50 cost_5585_1200_block51 rfl rfl rfl

private theorem cost_5585_1200_join0_52 : P1_7_1_3.blockEstimate 5585 1200 7856 129 = 1023183777 :=
  @P1_7_1_3.block_append 5585 1200 7856 7984 128 1 129 1023178192 5585 1023183777 cost_5585_1200_block52 cost_5585_1200_block53 rfl rfl rfl

private theorem cost_5585_1200_join1_0 : P1_7_1_3.blockEstimate 5585 1200 1200 512 = 117043869312 :=
  @P1_7_1_3.block_append 5585 1200 1200 1456 256 256 512 15259220800 101784648512 117043869312 cost_5585_1200_join0_0 cost_5585_1200_join0_2 rfl rfl rfl

private theorem cost_5585_1200_join1_2 : P1_7_1_3.blockEstimate 5585 1200 1712 512 = 747653609088 :=
  @P1_7_1_3.block_append 5585 1200 1712 1968 256 256 512 262658308928 484995300160 747653609088 cost_5585_1200_join0_4 cost_5585_1200_join0_6 rfl rfl rfl

private theorem cost_5585_1200_join1_4 : P1_7_1_3.blockEstimate 5585 1200 2224 512 = 1792297904820 :=
  @P1_7_1_3.block_append 5585 1200 2224 2480 256 256 512 755541668660 1036756236160 1792297904820 cost_5585_1200_join0_8 cost_5585_1200_join0_10 rfl rfl rfl

private theorem cost_5585_1200_join1_6 : P1_7_1_3.blockEstimate 5585 1200 2736 512 = 2768274484992 :=
  @P1_7_1_3.block_append 5585 1200 2736 2992 256 256 512 1281776531328 1486497953664 2768274484992 cost_5585_1200_join0_12 cost_5585_1200_join0_14 rfl rfl rfl

private theorem cost_5585_1200_join1_8 : P1_7_1_3.blockEstimate 5585 1200 3248 512 = 3425964683008 :=
  @P1_7_1_3.block_append 5585 1200 3248 3504 256 256 512 1650920503168 1775044179840 3425964683008 cost_5585_1200_join0_16 cost_5585_1200_join0_18 rfl rfl rfl

private theorem cost_5585_1200_join1_10 : P1_7_1_3.blockEstimate 5585 1200 3760 512 = 3761263898368 :=
  @P1_7_1_3.block_append 5585 1200 3760 4016 256 256 512 1858868983680 1902394914688 3761263898368 cost_5585_1200_join0_20 cost_5585_1200_join0_22 rfl rfl rfl

private theorem cost_5585_1200_join1_12 : P1_7_1_3.blockEstimate 5585 1200 4272 512 = 3774172131072 :=
  @P1_7_1_3.block_append 5585 1200 4272 4528 256 256 512 1905621972864 1868550158208 3774172131072 cost_5585_1200_join0_24 cost_5585_1200_join0_26 rfl rfl rfl

private theorem cost_5585_1200_join1_14 : P1_7_1_3.blockEstimate 5585 1200 4784 512 = 3464689381120 :=
  @P1_7_1_3.block_append 5585 1200 4784 5040 256 256 512 1791179470720 1673509910400 3464689381120 cost_5585_1200_join0_28 cost_5585_1200_join0_30 rfl rfl rfl

private theorem cost_5585_1200_join1_16 : P1_7_1_3.blockEstimate 5585 1200 5296 512 = 2836009275624 :=
  @P1_7_1_3.block_append 5585 1200 5296 5552 256 256 512 1515541477248 1320467798376 2836009275624 cost_5585_1200_join0_32 cost_5585_1200_join0_34 rfl rfl rfl

private theorem cost_5585_1200_join1_18 : P1_7_1_3.blockEstimate 5585 1200 5808 512 = 2007257963121 :=
  @P1_7_1_3.block_append 5585 1200 5808 6064 256 256 512 1109594824518 897663138603 2007257963121 cost_5585_1200_join0_36 cost_5585_1200_join0_38 rfl rfl rfl

private theorem cost_5585_1200_join1_20 : P1_7_1_3.blockEstimate 5585 1200 6320 512 = 1196486588741 :=
  @P1_7_1_3.block_append 5585 1200 6320 6576 256 256 512 693059325861 503427262880 1196486588741 cost_5585_1200_join0_40 cost_5585_1200_join0_42 rfl rfl rfl

private theorem cost_5585_1200_join1_22 : P1_7_1_3.blockEstimate 5585 1200 6832 512 = 530146934592 :=
  @P1_7_1_3.block_append 5585 1200 6832 7088 256 256 512 334742693792 195404240800 530146934592 cost_5585_1200_join0_44 cost_5585_1200_join0_46 rfl rfl rfl

private theorem cost_5585_1200_join1_24 : P1_7_1_3.blockEstimate 5585 1200 7344 512 = 115791626048 :=
  @P1_7_1_3.block_append 5585 1200 7344 7600 256 256 512 90808780704 24982845344 115791626048 cost_5585_1200_join0_48 cost_5585_1200_join0_50 rfl rfl rfl

private theorem cost_5585_1200_join2_0 : P1_7_1_3.blockEstimate 5585 1200 1200 1024 = 864697478400 :=
  @P1_7_1_3.block_append 5585 1200 1200 1712 512 512 1024 117043869312 747653609088 864697478400 cost_5585_1200_join1_0 cost_5585_1200_join1_2 rfl rfl rfl

private theorem cost_5585_1200_join2_2 : P1_7_1_3.blockEstimate 5585 1200 2224 1024 = 4560572389812 :=
  @P1_7_1_3.block_append 5585 1200 2224 2736 512 512 1024 1792297904820 2768274484992 4560572389812 cost_5585_1200_join1_4 cost_5585_1200_join1_6 rfl rfl rfl

private theorem cost_5585_1200_join2_4 : P1_7_1_3.blockEstimate 5585 1200 3248 1024 = 7187228581376 :=
  @P1_7_1_3.block_append 5585 1200 3248 3760 512 512 1024 3425964683008 3761263898368 7187228581376 cost_5585_1200_join1_8 cost_5585_1200_join1_10 rfl rfl rfl

private theorem cost_5585_1200_join2_6 : P1_7_1_3.blockEstimate 5585 1200 4272 1024 = 7238861512192 :=
  @P1_7_1_3.block_append 5585 1200 4272 4784 512 512 1024 3774172131072 3464689381120 7238861512192 cost_5585_1200_join1_12 cost_5585_1200_join1_14 rfl rfl rfl

private theorem cost_5585_1200_join2_8 : P1_7_1_3.blockEstimate 5585 1200 5296 1024 = 4843267238745 :=
  @P1_7_1_3.block_append 5585 1200 5296 5808 512 512 1024 2836009275624 2007257963121 4843267238745 cost_5585_1200_join1_16 cost_5585_1200_join1_18 rfl rfl rfl

private theorem cost_5585_1200_join2_10 : P1_7_1_3.blockEstimate 5585 1200 6320 1024 = 1726633523333 :=
  @P1_7_1_3.block_append 5585 1200 6320 6832 512 512 1024 1196486588741 530146934592 1726633523333 cost_5585_1200_join1_20 cost_5585_1200_join1_22 rfl rfl rfl

private theorem cost_5585_1200_join2_12 : P1_7_1_3.blockEstimate 5585 1200 7344 641 = 116814809825 :=
  @P1_7_1_3.block_append 5585 1200 7344 7856 512 129 641 115791626048 1023183777 116814809825 cost_5585_1200_join1_24 cost_5585_1200_join0_52 rfl rfl rfl

private theorem cost_5585_1200_join3_0 : P1_7_1_3.blockEstimate 5585 1200 1200 2048 = 5425269868212 :=
  @P1_7_1_3.block_append 5585 1200 1200 2224 1024 1024 2048 864697478400 4560572389812 5425269868212 cost_5585_1200_join2_0 cost_5585_1200_join2_2 rfl rfl rfl

private theorem cost_5585_1200_join3_2 : P1_7_1_3.blockEstimate 5585 1200 3248 2048 = 14426090093568 :=
  @P1_7_1_3.block_append 5585 1200 3248 4272 1024 1024 2048 7187228581376 7238861512192 14426090093568 cost_5585_1200_join2_4 cost_5585_1200_join2_6 rfl rfl rfl

private theorem cost_5585_1200_join3_4 : P1_7_1_3.blockEstimate 5585 1200 5296 2048 = 6569900762078 :=
  @P1_7_1_3.block_append 5585 1200 5296 6320 1024 1024 2048 4843267238745 1726633523333 6569900762078 cost_5585_1200_join2_8 cost_5585_1200_join2_10 rfl rfl rfl

private theorem cost_5585_1200_join4_0 : P1_7_1_3.blockEstimate 5585 1200 1200 4096 = 19851359961780 :=
  @P1_7_1_3.block_append 5585 1200 1200 3248 2048 2048 4096 5425269868212 14426090093568 19851359961780 cost_5585_1200_join3_0 cost_5585_1200_join3_2 rfl rfl rfl

private theorem cost_5585_1200_join4_2 : P1_7_1_3.blockEstimate 5585 1200 5296 2689 = 6686715571903 :=
  @P1_7_1_3.block_append 5585 1200 5296 7344 2048 641 2689 6569900762078 116814809825 6686715571903 cost_5585_1200_join3_4 cost_5585_1200_join2_12 rfl rfl rfl

private theorem cost_5585_1200_join5_0 : P1_7_1_3.blockEstimate 5585 1200 1200 6785 = 26538075533683 :=
  @P1_7_1_3.block_append 5585 1200 1200 5296 4096 2689 6785 19851359961780 6686715571903 26538075533683 cost_5585_1200_join4_0 cost_5585_1200_join4_2 rfl rfl rfl

private theorem cost_5585_1200_total : P1_7_1_3.momentEstimate 5585 1200 = 26538075533683 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 5585 + 1200 = 6785 by decide]
  exact cost_5585_1200_join5_0

theorem pole_cap : P1_7_1.groupedPoleMoment shape.B shape.J ≤ moment :=
  (P1_7_1_3.grouped_bound 5585 1200).trans_eq cost_5585_1200_total
end Research6966.SpreadCatalogue

end Merged6967_Near6967SpreadRanks

section Merged6967_Near6967RescueMoment28
set_option Elab.async false


set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private theorem cost_4884_1059_block0 : P1_7_1_3.blockEstimate 4884 1059 1059 128 = 1713223200 := by decide +kernel

private theorem cost_4884_1059_block1 : P1_7_1_3.blockEstimate 4884 1059 1187 128 = 11562829344 := by decide +kernel

private theorem cost_4884_1059_block2 : P1_7_1_3.blockEstimate 4884 1059 1315 128 = 30443820576 := by decide +kernel

private theorem cost_4884_1059_block3 : P1_7_1_3.blockEstimate 4884 1059 1443 128 = 57550890528 := by decide +kernel

private theorem cost_4884_1059_block4 : P1_7_1_3.blockEstimate 4884 1059 1571 128 = 92078732832 := by decide +kernel

private theorem cost_4884_1059_block5 : P1_7_1_3.blockEstimate 4884 1059 1699 128 = 133222041120 := by decide +kernel

private theorem cost_4884_1059_block6 : P1_7_1_3.blockEstimate 4884 1059 1827 128 = 180175509024 := by decide +kernel

private theorem cost_4884_1059_block7 : P1_7_1_3.blockEstimate 4884 1059 1955 128 = 232133830176 := by decide +kernel

private theorem cost_4884_1059_block8 : P1_7_1_3.blockEstimate 4884 1059 2083 128 = 287788262455 := by decide +kernel

private theorem cost_4884_1059_block9 : P1_7_1_3.blockEstimate 4884 1059 2211 128 = 341763571840 := by decide +kernel

private theorem cost_4884_1059_block10 : P1_7_1_3.blockEstimate 4884 1059 2339 128 = 391320420480 := by decide +kernel

private theorem cost_4884_1059_block11 : P1_7_1_3.blockEstimate 4884 1059 2467 128 = 436431306880 := by decide +kernel

private theorem cost_4884_1059_block12 : P1_7_1_3.blockEstimate 4884 1059 2595 128 = 477096231040 := by decide +kernel

private theorem cost_4884_1059_block13 : P1_7_1_3.blockEstimate 4884 1059 2723 128 = 513315192960 := by decide +kernel

private theorem cost_4884_1059_block14 : P1_7_1_3.blockEstimate 4884 1059 2851 128 = 545088192640 := by decide +kernel

private theorem cost_4884_1059_block15 : P1_7_1_3.blockEstimate 4884 1059 2979 128 = 572415230080 := by decide +kernel

private theorem cost_4884_1059_block16 : P1_7_1_3.blockEstimate 4884 1059 3107 128 = 595296305280 := by decide +kernel

private theorem cost_4884_1059_block17 : P1_7_1_3.blockEstimate 4884 1059 3235 128 = 613731418240 := by decide +kernel

private theorem cost_4884_1059_block18 : P1_7_1_3.blockEstimate 4884 1059 3363 128 = 627720568960 := by decide +kernel

private theorem cost_4884_1059_block19 : P1_7_1_3.blockEstimate 4884 1059 3491 128 = 637263757440 := by decide +kernel

private theorem cost_4884_1059_block20 : P1_7_1_3.blockEstimate 4884 1059 3619 128 = 642360983680 := by decide +kernel

private theorem cost_4884_1059_block21 : P1_7_1_3.blockEstimate 4884 1059 3747 128 = 643012247680 := by decide +kernel

private theorem cost_4884_1059_block22 : P1_7_1_3.blockEstimate 4884 1059 3875 128 = 639217549440 := by decide +kernel

private theorem cost_4884_1059_block23 : P1_7_1_3.blockEstimate 4884 1059 4003 128 = 630976888960 := by decide +kernel

private theorem cost_4884_1059_block24 : P1_7_1_3.blockEstimate 4884 1059 4131 128 = 618290266240 := by decide +kernel

private theorem cost_4884_1059_block25 : P1_7_1_3.blockEstimate 4884 1059 4259 128 = 601157681280 := by decide +kernel

private theorem cost_4884_1059_block26 : P1_7_1_3.blockEstimate 4884 1059 4387 128 = 579579134080 := by decide +kernel

private theorem cost_4884_1059_block27 : P1_7_1_3.blockEstimate 4884 1059 4515 128 = 553554624640 := by decide +kernel

private theorem cost_4884_1059_block28 : P1_7_1_3.blockEstimate 4884 1059 4643 128 = 523084152960 := by decide +kernel

private theorem cost_4884_1059_block29 : P1_7_1_3.blockEstimate 4884 1059 4771 128 = 488168576036 := by decide +kernel

private theorem cost_4884_1059_block30 : P1_7_1_3.blockEstimate 4884 1059 4899 128 = 449524789974 := by decide +kernel

private theorem cost_4884_1059_block31 : P1_7_1_3.blockEstimate 4884 1059 5027 128 = 409389324014 := by decide +kernel

private theorem cost_4884_1059_block32 : P1_7_1_3.blockEstimate 4884 1059 5155 128 = 368651857185 := by decide +kernel

private theorem cost_4884_1059_block33 : P1_7_1_3.blockEstimate 4884 1059 5283 128 = 327864803986 := by decide +kernel

private theorem cost_4884_1059_block34 : P1_7_1_3.blockEstimate 4884 1059 5411 128 = 287556266314 := by decide +kernel

private theorem cost_4884_1059_block35 : P1_7_1_3.blockEstimate 4884 1059 5539 128 = 248230035486 := by decide +kernel

private theorem cost_4884_1059_block36 : P1_7_1_3.blockEstimate 4884 1059 5667 128 = 210365592040 := by decide +kernel

private theorem cost_4884_1059_block37 : P1_7_1_3.blockEstimate 4884 1059 5795 128 = 174418104545 := by decide +kernel

private theorem cost_4884_1059_block38 : P1_7_1_3.blockEstimate 4884 1059 5923 128 = 140650232131 := by decide +kernel

private theorem cost_4884_1059_block39 : P1_7_1_3.blockEstimate 4884 1059 6051 128 = 109525882272 := by decide +kernel

private theorem cost_4884_1059_block40 : P1_7_1_3.blockEstimate 4884 1059 6179 128 = 81770411424 := by decide +kernel

private theorem cost_4884_1059_block41 : P1_7_1_3.blockEstimate 4884 1059 6307 128 = 57642423712 := by decide +kernel

private theorem cost_4884_1059_block42 : P1_7_1_3.blockEstimate 4884 1059 6435 128 = 37393577376 := by decide +kernel

private theorem cost_4884_1059_block43 : P1_7_1_3.blockEstimate 4884 1059 6563 128 = 21275530656 := by decide +kernel

private theorem cost_4884_1059_block44 : P1_7_1_3.blockEstimate 4884 1059 6691 128 = 9539941792 := by decide +kernel

private theorem cost_4884_1059_block45 : P1_7_1_3.blockEstimate 4884 1059 6819 128 = 2438469024 := by decide +kernel

private theorem cost_4884_1059_block46 : P1_7_1_3.blockEstimate 4884 1059 6947 55 = 72990078 := by decide +kernel

private theorem cost_4884_1059_join0_0 : P1_7_1_3.blockEstimate 4884 1059 1059 256 = 13276052544 :=
  @P1_7_1_3.block_append 4884 1059 1059 1187 128 128 256 1713223200 11562829344 13276052544 cost_4884_1059_block0 cost_4884_1059_block1 rfl rfl rfl

private theorem cost_4884_1059_join0_2 : P1_7_1_3.blockEstimate 4884 1059 1315 256 = 87994711104 :=
  @P1_7_1_3.block_append 4884 1059 1315 1443 128 128 256 30443820576 57550890528 87994711104 cost_4884_1059_block2 cost_4884_1059_block3 rfl rfl rfl

private theorem cost_4884_1059_join0_4 : P1_7_1_3.blockEstimate 4884 1059 1571 256 = 225300773952 :=
  @P1_7_1_3.block_append 4884 1059 1571 1699 128 128 256 92078732832 133222041120 225300773952 cost_4884_1059_block4 cost_4884_1059_block5 rfl rfl rfl

private theorem cost_4884_1059_join0_6 : P1_7_1_3.blockEstimate 4884 1059 1827 256 = 412309339200 :=
  @P1_7_1_3.block_append 4884 1059 1827 1955 128 128 256 180175509024 232133830176 412309339200 cost_4884_1059_block6 cost_4884_1059_block7 rfl rfl rfl

private theorem cost_4884_1059_join0_8 : P1_7_1_3.blockEstimate 4884 1059 2083 256 = 629551834295 :=
  @P1_7_1_3.block_append 4884 1059 2083 2211 128 128 256 287788262455 341763571840 629551834295 cost_4884_1059_block8 cost_4884_1059_block9 rfl rfl rfl

private theorem cost_4884_1059_join0_10 : P1_7_1_3.blockEstimate 4884 1059 2339 256 = 827751727360 :=
  @P1_7_1_3.block_append 4884 1059 2339 2467 128 128 256 391320420480 436431306880 827751727360 cost_4884_1059_block10 cost_4884_1059_block11 rfl rfl rfl

private theorem cost_4884_1059_join0_12 : P1_7_1_3.blockEstimate 4884 1059 2595 256 = 990411424000 :=
  @P1_7_1_3.block_append 4884 1059 2595 2723 128 128 256 477096231040 513315192960 990411424000 cost_4884_1059_block12 cost_4884_1059_block13 rfl rfl rfl

private theorem cost_4884_1059_join0_14 : P1_7_1_3.blockEstimate 4884 1059 2851 256 = 1117503422720 :=
  @P1_7_1_3.block_append 4884 1059 2851 2979 128 128 256 545088192640 572415230080 1117503422720 cost_4884_1059_block14 cost_4884_1059_block15 rfl rfl rfl

private theorem cost_4884_1059_join0_16 : P1_7_1_3.blockEstimate 4884 1059 3107 256 = 1209027723520 :=
  @P1_7_1_3.block_append 4884 1059 3107 3235 128 128 256 595296305280 613731418240 1209027723520 cost_4884_1059_block16 cost_4884_1059_block17 rfl rfl rfl

private theorem cost_4884_1059_join0_18 : P1_7_1_3.blockEstimate 4884 1059 3363 256 = 1264984326400 :=
  @P1_7_1_3.block_append 4884 1059 3363 3491 128 128 256 627720568960 637263757440 1264984326400 cost_4884_1059_block18 cost_4884_1059_block19 rfl rfl rfl

private theorem cost_4884_1059_join0_20 : P1_7_1_3.blockEstimate 4884 1059 3619 256 = 1285373231360 :=
  @P1_7_1_3.block_append 4884 1059 3619 3747 128 128 256 642360983680 643012247680 1285373231360 cost_4884_1059_block20 cost_4884_1059_block21 rfl rfl rfl

private theorem cost_4884_1059_join0_22 : P1_7_1_3.blockEstimate 4884 1059 3875 256 = 1270194438400 :=
  @P1_7_1_3.block_append 4884 1059 3875 4003 128 128 256 639217549440 630976888960 1270194438400 cost_4884_1059_block22 cost_4884_1059_block23 rfl rfl rfl

private theorem cost_4884_1059_join0_24 : P1_7_1_3.blockEstimate 4884 1059 4131 256 = 1219447947520 :=
  @P1_7_1_3.block_append 4884 1059 4131 4259 128 128 256 618290266240 601157681280 1219447947520 cost_4884_1059_block24 cost_4884_1059_block25 rfl rfl rfl

private theorem cost_4884_1059_join0_26 : P1_7_1_3.blockEstimate 4884 1059 4387 256 = 1133133758720 :=
  @P1_7_1_3.block_append 4884 1059 4387 4515 128 128 256 579579134080 553554624640 1133133758720 cost_4884_1059_block26 cost_4884_1059_block27 rfl rfl rfl

private theorem cost_4884_1059_join0_28 : P1_7_1_3.blockEstimate 4884 1059 4643 256 = 1011252728996 :=
  @P1_7_1_3.block_append 4884 1059 4643 4771 128 128 256 523084152960 488168576036 1011252728996 cost_4884_1059_block28 cost_4884_1059_block29 rfl rfl rfl

private theorem cost_4884_1059_join0_30 : P1_7_1_3.blockEstimate 4884 1059 4899 256 = 858914113988 :=
  @P1_7_1_3.block_append 4884 1059 4899 5027 128 128 256 449524789974 409389324014 858914113988 cost_4884_1059_block30 cost_4884_1059_block31 rfl rfl rfl

private theorem cost_4884_1059_join0_32 : P1_7_1_3.blockEstimate 4884 1059 5155 256 = 696516661171 :=
  @P1_7_1_3.block_append 4884 1059 5155 5283 128 128 256 368651857185 327864803986 696516661171 cost_4884_1059_block32 cost_4884_1059_block33 rfl rfl rfl

private theorem cost_4884_1059_join0_34 : P1_7_1_3.blockEstimate 4884 1059 5411 256 = 535786301800 :=
  @P1_7_1_3.block_append 4884 1059 5411 5539 128 128 256 287556266314 248230035486 535786301800 cost_4884_1059_block34 cost_4884_1059_block35 rfl rfl rfl

private theorem cost_4884_1059_join0_36 : P1_7_1_3.blockEstimate 4884 1059 5667 256 = 384783696585 :=
  @P1_7_1_3.block_append 4884 1059 5667 5795 128 128 256 210365592040 174418104545 384783696585 cost_4884_1059_block36 cost_4884_1059_block37 rfl rfl rfl

private theorem cost_4884_1059_join0_38 : P1_7_1_3.blockEstimate 4884 1059 5923 256 = 250176114403 :=
  @P1_7_1_3.block_append 4884 1059 5923 6051 128 128 256 140650232131 109525882272 250176114403 cost_4884_1059_block38 cost_4884_1059_block39 rfl rfl rfl

private theorem cost_4884_1059_join0_40 : P1_7_1_3.blockEstimate 4884 1059 6179 256 = 139412835136 :=
  @P1_7_1_3.block_append 4884 1059 6179 6307 128 128 256 81770411424 57642423712 139412835136 cost_4884_1059_block40 cost_4884_1059_block41 rfl rfl rfl

private theorem cost_4884_1059_join0_42 : P1_7_1_3.blockEstimate 4884 1059 6435 256 = 58669108032 :=
  @P1_7_1_3.block_append 4884 1059 6435 6563 128 128 256 37393577376 21275530656 58669108032 cost_4884_1059_block42 cost_4884_1059_block43 rfl rfl rfl

private theorem cost_4884_1059_join0_44 : P1_7_1_3.blockEstimate 4884 1059 6691 256 = 11978410816 :=
  @P1_7_1_3.block_append 4884 1059 6691 6819 128 128 256 9539941792 2438469024 11978410816 cost_4884_1059_block44 cost_4884_1059_block45 rfl rfl rfl

private theorem cost_4884_1059_join1_0 : P1_7_1_3.blockEstimate 4884 1059 1059 512 = 101270763648 :=
  @P1_7_1_3.block_append 4884 1059 1059 1315 256 256 512 13276052544 87994711104 101270763648 cost_4884_1059_join0_0 cost_4884_1059_join0_2 rfl rfl rfl

private theorem cost_4884_1059_join1_2 : P1_7_1_3.blockEstimate 4884 1059 1571 512 = 637610113152 :=
  @P1_7_1_3.block_append 4884 1059 1571 1827 256 256 512 225300773952 412309339200 637610113152 cost_4884_1059_join0_4 cost_4884_1059_join0_6 rfl rfl rfl

private theorem cost_4884_1059_join1_4 : P1_7_1_3.blockEstimate 4884 1059 2083 512 = 1457303561655 :=
  @P1_7_1_3.block_append 4884 1059 2083 2339 256 256 512 629551834295 827751727360 1457303561655 cost_4884_1059_join0_8 cost_4884_1059_join0_10 rfl rfl rfl

private theorem cost_4884_1059_join1_6 : P1_7_1_3.blockEstimate 4884 1059 2595 512 = 2107914846720 :=
  @P1_7_1_3.block_append 4884 1059 2595 2851 256 256 512 990411424000 1117503422720 2107914846720 cost_4884_1059_join0_12 cost_4884_1059_join0_14 rfl rfl rfl

private theorem cost_4884_1059_join1_8 : P1_7_1_3.blockEstimate 4884 1059 3107 512 = 2474012049920 :=
  @P1_7_1_3.block_append 4884 1059 3107 3363 256 256 512 1209027723520 1264984326400 2474012049920 cost_4884_1059_join0_16 cost_4884_1059_join0_18 rfl rfl rfl

private theorem cost_4884_1059_join1_10 : P1_7_1_3.blockEstimate 4884 1059 3619 512 = 2555567669760 :=
  @P1_7_1_3.block_append 4884 1059 3619 3875 256 256 512 1285373231360 1270194438400 2555567669760 cost_4884_1059_join0_20 cost_4884_1059_join0_22 rfl rfl rfl

private theorem cost_4884_1059_join1_12 : P1_7_1_3.blockEstimate 4884 1059 4131 512 = 2352581706240 :=
  @P1_7_1_3.block_append 4884 1059 4131 4387 256 256 512 1219447947520 1133133758720 2352581706240 cost_4884_1059_join0_24 cost_4884_1059_join0_26 rfl rfl rfl

private theorem cost_4884_1059_join1_14 : P1_7_1_3.blockEstimate 4884 1059 4643 512 = 1870166842984 :=
  @P1_7_1_3.block_append 4884 1059 4643 4899 256 256 512 1011252728996 858914113988 1870166842984 cost_4884_1059_join0_28 cost_4884_1059_join0_30 rfl rfl rfl

private theorem cost_4884_1059_join1_16 : P1_7_1_3.blockEstimate 4884 1059 5155 512 = 1232302962971 :=
  @P1_7_1_3.block_append 4884 1059 5155 5411 256 256 512 696516661171 535786301800 1232302962971 cost_4884_1059_join0_32 cost_4884_1059_join0_34 rfl rfl rfl

private theorem cost_4884_1059_join1_18 : P1_7_1_3.blockEstimate 4884 1059 5667 512 = 634959810988 :=
  @P1_7_1_3.block_append 4884 1059 5667 5923 256 256 512 384783696585 250176114403 634959810988 cost_4884_1059_join0_36 cost_4884_1059_join0_38 rfl rfl rfl

private theorem cost_4884_1059_join1_20 : P1_7_1_3.blockEstimate 4884 1059 6179 512 = 198081943168 :=
  @P1_7_1_3.block_append 4884 1059 6179 6435 256 256 512 139412835136 58669108032 198081943168 cost_4884_1059_join0_40 cost_4884_1059_join0_42 rfl rfl rfl

private theorem cost_4884_1059_join1_22 : P1_7_1_3.blockEstimate 4884 1059 6691 311 = 12051400894 :=
  @P1_7_1_3.block_append 4884 1059 6691 6947 256 55 311 11978410816 72990078 12051400894 cost_4884_1059_join0_44 cost_4884_1059_block46 rfl rfl rfl

private theorem cost_4884_1059_join2_0 : P1_7_1_3.blockEstimate 4884 1059 1059 1024 = 738880876800 :=
  @P1_7_1_3.block_append 4884 1059 1059 1571 512 512 1024 101270763648 637610113152 738880876800 cost_4884_1059_join1_0 cost_4884_1059_join1_2 rfl rfl rfl

private theorem cost_4884_1059_join2_2 : P1_7_1_3.blockEstimate 4884 1059 2083 1024 = 3565218408375 :=
  @P1_7_1_3.block_append 4884 1059 2083 2595 512 512 1024 1457303561655 2107914846720 3565218408375 cost_4884_1059_join1_4 cost_4884_1059_join1_6 rfl rfl rfl

private theorem cost_4884_1059_join2_4 : P1_7_1_3.blockEstimate 4884 1059 3107 1024 = 5029579719680 :=
  @P1_7_1_3.block_append 4884 1059 3107 3619 512 512 1024 2474012049920 2555567669760 5029579719680 cost_4884_1059_join1_8 cost_4884_1059_join1_10 rfl rfl rfl

private theorem cost_4884_1059_join2_6 : P1_7_1_3.blockEstimate 4884 1059 4131 1024 = 4222748549224 :=
  @P1_7_1_3.block_append 4884 1059 4131 4643 512 512 1024 2352581706240 1870166842984 4222748549224 cost_4884_1059_join1_12 cost_4884_1059_join1_14 rfl rfl rfl

private theorem cost_4884_1059_join2_8 : P1_7_1_3.blockEstimate 4884 1059 5155 1024 = 1867262773959 :=
  @P1_7_1_3.block_append 4884 1059 5155 5667 512 512 1024 1232302962971 634959810988 1867262773959 cost_4884_1059_join1_16 cost_4884_1059_join1_18 rfl rfl rfl

private theorem cost_4884_1059_join2_10 : P1_7_1_3.blockEstimate 4884 1059 6179 823 = 210133344062 :=
  @P1_7_1_3.block_append 4884 1059 6179 6691 512 311 823 198081943168 12051400894 210133344062 cost_4884_1059_join1_20 cost_4884_1059_join1_22 rfl rfl rfl

private theorem cost_4884_1059_join3_0 : P1_7_1_3.blockEstimate 4884 1059 1059 2048 = 4304099285175 :=
  @P1_7_1_3.block_append 4884 1059 1059 2083 1024 1024 2048 738880876800 3565218408375 4304099285175 cost_4884_1059_join2_0 cost_4884_1059_join2_2 rfl rfl rfl

private theorem cost_4884_1059_join3_2 : P1_7_1_3.blockEstimate 4884 1059 3107 2048 = 9252328268904 :=
  @P1_7_1_3.block_append 4884 1059 3107 4131 1024 1024 2048 5029579719680 4222748549224 9252328268904 cost_4884_1059_join2_4 cost_4884_1059_join2_6 rfl rfl rfl

private theorem cost_4884_1059_join3_4 : P1_7_1_3.blockEstimate 4884 1059 5155 1847 = 2077396118021 :=
  @P1_7_1_3.block_append 4884 1059 5155 6179 1024 823 1847 1867262773959 210133344062 2077396118021 cost_4884_1059_join2_8 cost_4884_1059_join2_10 rfl rfl rfl

private theorem cost_4884_1059_join4_0 : P1_7_1_3.blockEstimate 4884 1059 1059 4096 = 13556427554079 :=
  @P1_7_1_3.block_append 4884 1059 1059 3107 2048 2048 4096 4304099285175 9252328268904 13556427554079 cost_4884_1059_join3_0 cost_4884_1059_join3_2 rfl rfl rfl

private theorem cost_4884_1059_join5_0 : P1_7_1_3.blockEstimate 4884 1059 1059 5943 = 15633823672100 :=
  @P1_7_1_3.block_append 4884 1059 1059 5155 4096 1847 5943 13556427554079 2077396118021 15633823672100 cost_4884_1059_join4_0 cost_4884_1059_join3_4 rfl rfl rfl

private theorem cost_4884_1059_total : P1_7_1_3.momentEstimate 4884 1059 = 15633823672100 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 4884 + 1059 = 5943 by decide]
  exact cost_4884_1059_join5_0

theorem moment4884_1059 : P1_7_1.groupedPoleMoment 4884 1059 ≤ 15633823672100 :=
  (P1_7_1_3.grouped_bound 4884 1059).trans_eq cost_4884_1059_total
private theorem cost_4993_1073_block0 : P1_7_1_3.blockEstimate 4993 1073 1073 128 = 1752219040 := by decide +kernel

private theorem cost_4993_1073_block1 : P1_7_1_3.blockEstimate 4993 1073 1201 128 = 11832200608 := by decide +kernel

private theorem cost_4993_1073_block2 : P1_7_1_3.blockEstimate 4993 1073 1329 128 = 31172156832 := by decide +kernel

private theorem cost_4993_1073_block3 : P1_7_1_3.blockEstimate 4993 1073 1457 128 = 58966781344 := by decide +kernel

private theorem cost_4993_1073_block4 : P1_7_1_3.blockEstimate 4993 1073 1585 128 = 94410767776 := by decide +kernel

private theorem cost_4993_1073_block5 : P1_7_1_3.blockEstimate 4993 1073 1713 128 = 136698809760 := by decide +kernel

private theorem cost_4993_1073_block6 : P1_7_1_3.blockEstimate 4993 1073 1841 128 = 185025600928 := by decide +kernel

private theorem cost_4993_1073_block7 : P1_7_1_3.blockEstimate 4993 1073 1969 128 = 238585834912 := by decide +kernel

private theorem cost_4993_1073_block8 : P1_7_1_3.blockEstimate 4993 1073 2097 128 = 296256965044 := by decide +kernel

private theorem cost_4993_1073_block9 : P1_7_1_3.blockEstimate 4993 1073 2225 128 = 352936642752 := by decide +kernel

private theorem cost_4993_1073_block10 : P1_7_1_3.blockEstimate 4993 1073 2353 128 = 405189200064 := by decide +kernel

private theorem cost_4993_1073_block11 : P1_7_1_3.blockEstimate 4993 1073 2481 128 = 452937074880 := by decide +kernel

private theorem cost_4993_1073_block12 : P1_7_1_3.blockEstimate 4993 1073 2609 128 = 496180267200 := by decide +kernel

private theorem cost_4993_1073_block13 : P1_7_1_3.blockEstimate 4993 1073 2737 128 = 534918777024 := by decide +kernel

private theorem cost_4993_1073_block14 : P1_7_1_3.blockEstimate 4993 1073 2865 128 = 569152604352 := by decide +kernel

private theorem cost_4993_1073_block15 : P1_7_1_3.blockEstimate 4993 1073 2993 128 = 598881749184 := by decide +kernel

private theorem cost_4993_1073_block16 : P1_7_1_3.blockEstimate 4993 1073 3121 128 = 624106211520 := by decide +kernel

private theorem cost_4993_1073_block17 : P1_7_1_3.blockEstimate 4993 1073 3249 128 = 644825991360 := by decide +kernel

private theorem cost_4993_1073_block18 : P1_7_1_3.blockEstimate 4993 1073 3377 128 = 661041088704 := by decide +kernel

private theorem cost_4993_1073_block19 : P1_7_1_3.blockEstimate 4993 1073 3505 128 = 672751503552 := by decide +kernel

private theorem cost_4993_1073_block20 : P1_7_1_3.blockEstimate 4993 1073 3633 128 = 679957235904 := by decide +kernel

private theorem cost_4993_1073_block21 : P1_7_1_3.blockEstimate 4993 1073 3761 128 = 682658285760 := by decide +kernel

private theorem cost_4993_1073_block22 : P1_7_1_3.blockEstimate 4993 1073 3889 128 = 680854653120 := by decide +kernel

private theorem cost_4993_1073_block23 : P1_7_1_3.blockEstimate 4993 1073 4017 128 = 674546337984 := by decide +kernel

private theorem cost_4993_1073_block24 : P1_7_1_3.blockEstimate 4993 1073 4145 128 = 663733340352 := by decide +kernel

private theorem cost_4993_1073_block25 : P1_7_1_3.blockEstimate 4993 1073 4273 128 = 648415660224 := by decide +kernel

private theorem cost_4993_1073_block26 : P1_7_1_3.blockEstimate 4993 1073 4401 128 = 628593297600 := by decide +kernel

private theorem cost_4993_1073_block27 : P1_7_1_3.blockEstimate 4993 1073 4529 128 = 604266252480 := by decide +kernel

private theorem cost_4993_1073_block28 : P1_7_1_3.blockEstimate 4993 1073 4657 128 = 575434524864 := by decide +kernel

private theorem cost_4993_1073_block29 : P1_7_1_3.blockEstimate 4993 1073 4785 128 = 542098114752 := by decide +kernel

private theorem cost_4993_1073_block30 : P1_7_1_3.blockEstimate 4993 1073 4913 128 = 504284577544 := by decide +kernel

private theorem cost_4993_1073_block31 : P1_7_1_3.blockEstimate 4993 1073 5041 128 = 463277843542 := by decide +kernel

private theorem cost_4993_1073_block32 : P1_7_1_3.blockEstimate 4993 1073 5169 128 = 421154389486 := by decide +kernel

private theorem cost_4993_1073_block33 : P1_7_1_3.blockEstimate 4993 1073 5297 128 = 378600493940 := by decide +kernel

private theorem cost_4993_1073_block34 : P1_7_1_3.blockEstimate 4993 1073 5425 128 = 336163056044 := by decide +kernel

private theorem cost_4993_1073_block35 : P1_7_1_3.blockEstimate 4993 1073 5553 128 = 294364981511 := by decide +kernel

private theorem cost_4993_1073_block36 : P1_7_1_3.blockEstimate 4993 1073 5681 128 = 253705181892 := by decide +kernel

private theorem cost_4993_1073_block37 : P1_7_1_3.blockEstimate 4993 1073 5809 128 = 214658573545 := by decide +kernel

private theorem cost_4993_1073_block38 : P1_7_1_3.blockEstimate 4993 1073 5937 128 = 177676080090 := by decide +kernel

private theorem cost_4993_1073_block39 : P1_7_1_3.blockEstimate 4993 1073 6065 128 = 142954286096 := by decide +kernel

private theorem cost_4993_1073_block40 : P1_7_1_3.blockEstimate 4993 1073 6193 128 = 111104086032 := by decide +kernel

private theorem cost_4993_1073_block41 : P1_7_1_3.blockEstimate 4993 1073 6321 128 = 82753836048 := by decide +kernel

private theorem cost_4993_1073_block42 : P1_7_1_3.blockEstimate 4993 1073 6449 128 = 58155194384 := by decide +kernel

private theorem cost_4993_1073_block43 : P1_7_1_3.blockEstimate 4993 1073 6577 128 = 37559819280 := by decide +kernel

private theorem cost_4993_1073_block44 : P1_7_1_3.blockEstimate 4993 1073 6705 128 = 21219368976 := by decide +kernel

private theorem cost_4993_1073_block45 : P1_7_1_3.blockEstimate 4993 1073 6833 128 = 9385501712 := by decide +kernel

private theorem cost_4993_1073_block46 : P1_7_1_3.blockEstimate 4993 1073 6961 128 = 2309875728 := by decide +kernel

private theorem cost_4993_1073_block47 : P1_7_1_3.blockEstimate 4993 1073 7089 50 = 56536272 := by decide +kernel

private theorem cost_4993_1073_join0_0 : P1_7_1_3.blockEstimate 4993 1073 1073 256 = 13584419648 :=
  @P1_7_1_3.block_append 4993 1073 1073 1201 128 128 256 1752219040 11832200608 13584419648 cost_4993_1073_block0 cost_4993_1073_block1 rfl rfl rfl

private theorem cost_4993_1073_join0_2 : P1_7_1_3.blockEstimate 4993 1073 1329 256 = 90138938176 :=
  @P1_7_1_3.block_append 4993 1073 1329 1457 128 128 256 31172156832 58966781344 90138938176 cost_4993_1073_block2 cost_4993_1073_block3 rfl rfl rfl

private theorem cost_4993_1073_join0_4 : P1_7_1_3.blockEstimate 4993 1073 1585 256 = 231109577536 :=
  @P1_7_1_3.block_append 4993 1073 1585 1713 128 128 256 94410767776 136698809760 231109577536 cost_4993_1073_block4 cost_4993_1073_block5 rfl rfl rfl

private theorem cost_4993_1073_join0_6 : P1_7_1_3.blockEstimate 4993 1073 1841 256 = 423611435840 :=
  @P1_7_1_3.block_append 4993 1073 1841 1969 128 128 256 185025600928 238585834912 423611435840 cost_4993_1073_block6 cost_4993_1073_block7 rfl rfl rfl

private theorem cost_4993_1073_join0_8 : P1_7_1_3.blockEstimate 4993 1073 2097 256 = 649193607796 :=
  @P1_7_1_3.block_append 4993 1073 2097 2225 128 128 256 296256965044 352936642752 649193607796 cost_4993_1073_block8 cost_4993_1073_block9 rfl rfl rfl

private theorem cost_4993_1073_join0_10 : P1_7_1_3.blockEstimate 4993 1073 2353 256 = 858126274944 :=
  @P1_7_1_3.block_append 4993 1073 2353 2481 128 128 256 405189200064 452937074880 858126274944 cost_4993_1073_block10 cost_4993_1073_block11 rfl rfl rfl

private theorem cost_4993_1073_join0_12 : P1_7_1_3.blockEstimate 4993 1073 2609 256 = 1031099044224 :=
  @P1_7_1_3.block_append 4993 1073 2609 2737 128 128 256 496180267200 534918777024 1031099044224 cost_4993_1073_block12 cost_4993_1073_block13 rfl rfl rfl

private theorem cost_4993_1073_join0_14 : P1_7_1_3.blockEstimate 4993 1073 2865 256 = 1168034353536 :=
  @P1_7_1_3.block_append 4993 1073 2865 2993 128 128 256 569152604352 598881749184 1168034353536 cost_4993_1073_block14 cost_4993_1073_block15 rfl rfl rfl

private theorem cost_4993_1073_join0_16 : P1_7_1_3.blockEstimate 4993 1073 3121 256 = 1268932202880 :=
  @P1_7_1_3.block_append 4993 1073 3121 3249 128 128 256 624106211520 644825991360 1268932202880 cost_4993_1073_block16 cost_4993_1073_block17 rfl rfl rfl

private theorem cost_4993_1073_join0_18 : P1_7_1_3.blockEstimate 4993 1073 3377 256 = 1333792592256 :=
  @P1_7_1_3.block_append 4993 1073 3377 3505 128 128 256 661041088704 672751503552 1333792592256 cost_4993_1073_block18 cost_4993_1073_block19 rfl rfl rfl

private theorem cost_4993_1073_join0_20 : P1_7_1_3.blockEstimate 4993 1073 3633 256 = 1362615521664 :=
  @P1_7_1_3.block_append 4993 1073 3633 3761 128 128 256 679957235904 682658285760 1362615521664 cost_4993_1073_block20 cost_4993_1073_block21 rfl rfl rfl

private theorem cost_4993_1073_join0_22 : P1_7_1_3.blockEstimate 4993 1073 3889 256 = 1355400991104 :=
  @P1_7_1_3.block_append 4993 1073 3889 4017 128 128 256 680854653120 674546337984 1355400991104 cost_4993_1073_block22 cost_4993_1073_block23 rfl rfl rfl

private theorem cost_4993_1073_join0_24 : P1_7_1_3.blockEstimate 4993 1073 4145 256 = 1312149000576 :=
  @P1_7_1_3.block_append 4993 1073 4145 4273 128 128 256 663733340352 648415660224 1312149000576 cost_4993_1073_block24 cost_4993_1073_block25 rfl rfl rfl

private theorem cost_4993_1073_join0_26 : P1_7_1_3.blockEstimate 4993 1073 4401 256 = 1232859550080 :=
  @P1_7_1_3.block_append 4993 1073 4401 4529 128 128 256 628593297600 604266252480 1232859550080 cost_4993_1073_block26 cost_4993_1073_block27 rfl rfl rfl

private theorem cost_4993_1073_join0_28 : P1_7_1_3.blockEstimate 4993 1073 4657 256 = 1117532639616 :=
  @P1_7_1_3.block_append 4993 1073 4657 4785 128 128 256 575434524864 542098114752 1117532639616 cost_4993_1073_block28 cost_4993_1073_block29 rfl rfl rfl

private theorem cost_4993_1073_join0_30 : P1_7_1_3.blockEstimate 4993 1073 4913 256 = 967562421086 :=
  @P1_7_1_3.block_append 4993 1073 4913 5041 128 128 256 504284577544 463277843542 967562421086 cost_4993_1073_block30 cost_4993_1073_block31 rfl rfl rfl

private theorem cost_4993_1073_join0_32 : P1_7_1_3.blockEstimate 4993 1073 5169 256 = 799754883426 :=
  @P1_7_1_3.block_append 4993 1073 5169 5297 128 128 256 421154389486 378600493940 799754883426 cost_4993_1073_block32 cost_4993_1073_block33 rfl rfl rfl

private theorem cost_4993_1073_join0_34 : P1_7_1_3.blockEstimate 4993 1073 5425 256 = 630528037555 :=
  @P1_7_1_3.block_append 4993 1073 5425 5553 128 128 256 336163056044 294364981511 630528037555 cost_4993_1073_block34 cost_4993_1073_block35 rfl rfl rfl

private theorem cost_4993_1073_join0_36 : P1_7_1_3.blockEstimate 4993 1073 5681 256 = 468363755437 :=
  @P1_7_1_3.block_append 4993 1073 5681 5809 128 128 256 253705181892 214658573545 468363755437 cost_4993_1073_block36 cost_4993_1073_block37 rfl rfl rfl

private theorem cost_4993_1073_join0_38 : P1_7_1_3.blockEstimate 4993 1073 5937 256 = 320630366186 :=
  @P1_7_1_3.block_append 4993 1073 5937 6065 128 128 256 177676080090 142954286096 320630366186 cost_4993_1073_block38 cost_4993_1073_block39 rfl rfl rfl

private theorem cost_4993_1073_join0_40 : P1_7_1_3.blockEstimate 4993 1073 6193 256 = 193857922080 :=
  @P1_7_1_3.block_append 4993 1073 6193 6321 128 128 256 111104086032 82753836048 193857922080 cost_4993_1073_block40 cost_4993_1073_block41 rfl rfl rfl

private theorem cost_4993_1073_join0_42 : P1_7_1_3.blockEstimate 4993 1073 6449 256 = 95715013664 :=
  @P1_7_1_3.block_append 4993 1073 6449 6577 128 128 256 58155194384 37559819280 95715013664 cost_4993_1073_block42 cost_4993_1073_block43 rfl rfl rfl

private theorem cost_4993_1073_join0_44 : P1_7_1_3.blockEstimate 4993 1073 6705 256 = 30604870688 :=
  @P1_7_1_3.block_append 4993 1073 6705 6833 128 128 256 21219368976 9385501712 30604870688 cost_4993_1073_block44 cost_4993_1073_block45 rfl rfl rfl

private theorem cost_4993_1073_join0_46 : P1_7_1_3.blockEstimate 4993 1073 6961 178 = 2366412000 :=
  @P1_7_1_3.block_append 4993 1073 6961 7089 128 50 178 2309875728 56536272 2366412000 cost_4993_1073_block46 cost_4993_1073_block47 rfl rfl rfl

private theorem cost_4993_1073_join1_0 : P1_7_1_3.blockEstimate 4993 1073 1073 512 = 103723357824 :=
  @P1_7_1_3.block_append 4993 1073 1073 1329 256 256 512 13584419648 90138938176 103723357824 cost_4993_1073_join0_0 cost_4993_1073_join0_2 rfl rfl rfl

private theorem cost_4993_1073_join1_2 : P1_7_1_3.blockEstimate 4993 1073 1585 512 = 654721013376 :=
  @P1_7_1_3.block_append 4993 1073 1585 1841 256 256 512 231109577536 423611435840 654721013376 cost_4993_1073_join0_4 cost_4993_1073_join0_6 rfl rfl rfl

private theorem cost_4993_1073_join1_4 : P1_7_1_3.blockEstimate 4993 1073 2097 512 = 1507319882740 :=
  @P1_7_1_3.block_append 4993 1073 2097 2353 256 256 512 649193607796 858126274944 1507319882740 cost_4993_1073_join0_8 cost_4993_1073_join0_10 rfl rfl rfl

private theorem cost_4993_1073_join1_6 : P1_7_1_3.blockEstimate 4993 1073 2609 512 = 2199133397760 :=
  @P1_7_1_3.block_append 4993 1073 2609 2865 256 256 512 1031099044224 1168034353536 2199133397760 cost_4993_1073_join0_12 cost_4993_1073_join0_14 rfl rfl rfl

private theorem cost_4993_1073_join1_8 : P1_7_1_3.blockEstimate 4993 1073 3121 512 = 2602724795136 :=
  @P1_7_1_3.block_append 4993 1073 3121 3377 256 256 512 1268932202880 1333792592256 2602724795136 cost_4993_1073_join0_16 cost_4993_1073_join0_18 rfl rfl rfl

private theorem cost_4993_1073_join1_10 : P1_7_1_3.blockEstimate 4993 1073 3633 512 = 2718016512768 :=
  @P1_7_1_3.block_append 4993 1073 3633 3889 256 256 512 1362615521664 1355400991104 2718016512768 cost_4993_1073_join0_20 cost_4993_1073_join0_22 rfl rfl rfl

private theorem cost_4993_1073_join1_12 : P1_7_1_3.blockEstimate 4993 1073 4145 512 = 2545008550656 :=
  @P1_7_1_3.block_append 4993 1073 4145 4401 256 256 512 1312149000576 1232859550080 2545008550656 cost_4993_1073_join0_24 cost_4993_1073_join0_26 rfl rfl rfl

private theorem cost_4993_1073_join1_14 : P1_7_1_3.blockEstimate 4993 1073 4657 512 = 2085095060702 :=
  @P1_7_1_3.block_append 4993 1073 4657 4913 256 256 512 1117532639616 967562421086 2085095060702 cost_4993_1073_join0_28 cost_4993_1073_join0_30 rfl rfl rfl

private theorem cost_4993_1073_join1_16 : P1_7_1_3.blockEstimate 4993 1073 5169 512 = 1430282920981 :=
  @P1_7_1_3.block_append 4993 1073 5169 5425 256 256 512 799754883426 630528037555 1430282920981 cost_4993_1073_join0_32 cost_4993_1073_join0_34 rfl rfl rfl

private theorem cost_4993_1073_join1_18 : P1_7_1_3.blockEstimate 4993 1073 5681 512 = 788994121623 :=
  @P1_7_1_3.block_append 4993 1073 5681 5937 256 256 512 468363755437 320630366186 788994121623 cost_4993_1073_join0_36 cost_4993_1073_join0_38 rfl rfl rfl

private theorem cost_4993_1073_join1_20 : P1_7_1_3.blockEstimate 4993 1073 6193 512 = 289572935744 :=
  @P1_7_1_3.block_append 4993 1073 6193 6449 256 256 512 193857922080 95715013664 289572935744 cost_4993_1073_join0_40 cost_4993_1073_join0_42 rfl rfl rfl

private theorem cost_4993_1073_join1_22 : P1_7_1_3.blockEstimate 4993 1073 6705 434 = 32971282688 :=
  @P1_7_1_3.block_append 4993 1073 6705 6961 256 178 434 30604870688 2366412000 32971282688 cost_4993_1073_join0_44 cost_4993_1073_join0_46 rfl rfl rfl

private theorem cost_4993_1073_join2_0 : P1_7_1_3.blockEstimate 4993 1073 1073 1024 = 758444371200 :=
  @P1_7_1_3.block_append 4993 1073 1073 1585 512 512 1024 103723357824 654721013376 758444371200 cost_4993_1073_join1_0 cost_4993_1073_join1_2 rfl rfl rfl

private theorem cost_4993_1073_join2_2 : P1_7_1_3.blockEstimate 4993 1073 2097 1024 = 3706453280500 :=
  @P1_7_1_3.block_append 4993 1073 2097 2609 512 512 1024 1507319882740 2199133397760 3706453280500 cost_4993_1073_join1_4 cost_4993_1073_join1_6 rfl rfl rfl

private theorem cost_4993_1073_join2_4 : P1_7_1_3.blockEstimate 4993 1073 3121 1024 = 5320741307904 :=
  @P1_7_1_3.block_append 4993 1073 3121 3633 512 512 1024 2602724795136 2718016512768 5320741307904 cost_4993_1073_join1_8 cost_4993_1073_join1_10 rfl rfl rfl

private theorem cost_4993_1073_join2_6 : P1_7_1_3.blockEstimate 4993 1073 4145 1024 = 4630103611358 :=
  @P1_7_1_3.block_append 4993 1073 4145 4657 512 512 1024 2545008550656 2085095060702 4630103611358 cost_4993_1073_join1_12 cost_4993_1073_join1_14 rfl rfl rfl

private theorem cost_4993_1073_join2_8 : P1_7_1_3.blockEstimate 4993 1073 5169 1024 = 2219277042604 :=
  @P1_7_1_3.block_append 4993 1073 5169 5681 512 512 1024 1430282920981 788994121623 2219277042604 cost_4993_1073_join1_16 cost_4993_1073_join1_18 rfl rfl rfl

private theorem cost_4993_1073_join2_10 : P1_7_1_3.blockEstimate 4993 1073 6193 946 = 322544218432 :=
  @P1_7_1_3.block_append 4993 1073 6193 6705 512 434 946 289572935744 32971282688 322544218432 cost_4993_1073_join1_20 cost_4993_1073_join1_22 rfl rfl rfl

private theorem cost_4993_1073_join3_0 : P1_7_1_3.blockEstimate 4993 1073 1073 2048 = 4464897651700 :=
  @P1_7_1_3.block_append 4993 1073 1073 2097 1024 1024 2048 758444371200 3706453280500 4464897651700 cost_4993_1073_join2_0 cost_4993_1073_join2_2 rfl rfl rfl

private theorem cost_4993_1073_join3_2 : P1_7_1_3.blockEstimate 4993 1073 3121 2048 = 9950844919262 :=
  @P1_7_1_3.block_append 4993 1073 3121 4145 1024 1024 2048 5320741307904 4630103611358 9950844919262 cost_4993_1073_join2_4 cost_4993_1073_join2_6 rfl rfl rfl

private theorem cost_4993_1073_join3_4 : P1_7_1_3.blockEstimate 4993 1073 5169 1970 = 2541821261036 :=
  @P1_7_1_3.block_append 4993 1073 5169 6193 1024 946 1970 2219277042604 322544218432 2541821261036 cost_4993_1073_join2_8 cost_4993_1073_join2_10 rfl rfl rfl

private theorem cost_4993_1073_join4_0 : P1_7_1_3.blockEstimate 4993 1073 1073 4096 = 14415742570962 :=
  @P1_7_1_3.block_append 4993 1073 1073 3121 2048 2048 4096 4464897651700 9950844919262 14415742570962 cost_4993_1073_join3_0 cost_4993_1073_join3_2 rfl rfl rfl

private theorem cost_4993_1073_join5_0 : P1_7_1_3.blockEstimate 4993 1073 1073 6066 = 16957563831998 :=
  @P1_7_1_3.block_append 4993 1073 1073 5169 4096 1970 6066 14415742570962 2541821261036 16957563831998 cost_4993_1073_join4_0 cost_4993_1073_join3_4 rfl rfl rfl

private theorem cost_4993_1073_total : P1_7_1_3.momentEstimate 4993 1073 = 16957563831998 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 4993 + 1073 = 6066 by decide]
  exact cost_4993_1073_join5_0

theorem moment4993_1073 : P1_7_1.groupedPoleMoment 4993 1073 ≤ 16957563831998 :=
  (P1_7_1_3.grouped_bound 4993 1073).trans_eq cost_4993_1073_total
private theorem cost_5164_1110_block0 : P1_7_1_3.blockEstimate 5164 1110 1110 128 = 1813396000 := by decide +kernel

private theorem cost_5164_1110_block1 : P1_7_1_3.blockEstimate 5164 1110 1238 128 = 12254792224 := by decide +kernel

private theorem cost_5164_1110_block2 : P1_7_1_3.blockEstimate 5164 1110 1366 128 = 32314776096 := by decide +kernel

private theorem cost_5164_1110_block3 : P1_7_1_3.blockEstimate 5164 1110 1494 128 = 61188041248 := by decide +kernel

private theorem cost_5164_1110_block4 : P1_7_1_3.blockEstimate 5164 1110 1622 128 = 98069281312 := by decide +kernel

private theorem cost_5164_1110_block5 : P1_7_1_3.blockEstimate 5164 1110 1750 128 = 142153189920 := by decide +kernel

private theorem cost_5164_1110_block6 : P1_7_1_3.blockEstimate 5164 1110 1878 128 = 192634460704 := by decide +kernel

private theorem cost_5164_1110_block7 : P1_7_1_3.blockEstimate 5164 1110 2006 128 = 248707787296 := by decide +kernel

private theorem cost_5164_1110_block8 : P1_7_1_3.blockEstimate 5164 1110 2134 128 = 309518215485 := by decide +kernel

private theorem cost_5164_1110_block9 : P1_7_1_3.blockEstimate 5164 1110 2262 128 = 371243583040 := by decide +kernel

private theorem cost_5164_1110_block10 : P1_7_1_3.blockEstimate 5164 1110 2390 128 = 428745672256 := by decide +kernel

private theorem cost_5164_1110_block11 : P1_7_1_3.blockEstimate 5164 1110 2518 128 = 481587889728 := by decide +kernel

private theorem cost_5164_1110_block12 : P1_7_1_3.blockEstimate 5164 1110 2646 128 = 529770235456 := by decide +kernel

private theorem cost_5164_1110_block13 : P1_7_1_3.blockEstimate 5164 1110 2774 128 = 573292709440 := by decide +kernel

private theorem cost_5164_1110_block14 : P1_7_1_3.blockEstimate 5164 1110 2902 128 = 612155311680 := by decide +kernel

private theorem cost_5164_1110_block15 : P1_7_1_3.blockEstimate 5164 1110 3030 128 = 646358042176 := by decide +kernel

private theorem cost_5164_1110_block16 : P1_7_1_3.blockEstimate 5164 1110 3158 128 = 675900900928 := by decide +kernel

private theorem cost_5164_1110_block17 : P1_7_1_3.blockEstimate 5164 1110 3286 128 = 700783887936 := by decide +kernel

private theorem cost_5164_1110_block18 : P1_7_1_3.blockEstimate 5164 1110 3414 128 = 721007003200 := by decide +kernel

private theorem cost_5164_1110_block19 : P1_7_1_3.blockEstimate 5164 1110 3542 128 = 736570246720 := by decide +kernel

private theorem cost_5164_1110_block20 : P1_7_1_3.blockEstimate 5164 1110 3670 128 = 747473618496 := by decide +kernel

private theorem cost_5164_1110_block21 : P1_7_1_3.blockEstimate 5164 1110 3798 128 = 753717118528 := by decide +kernel

private theorem cost_5164_1110_block22 : P1_7_1_3.blockEstimate 5164 1110 3926 128 = 755300746816 := by decide +kernel

private theorem cost_5164_1110_block23 : P1_7_1_3.blockEstimate 5164 1110 4054 128 = 752224503360 := by decide +kernel

private theorem cost_5164_1110_block24 : P1_7_1_3.blockEstimate 5164 1110 4182 128 = 744488388160 := by decide +kernel

private theorem cost_5164_1110_block25 : P1_7_1_3.blockEstimate 5164 1110 4310 128 = 732092401216 := by decide +kernel

private theorem cost_5164_1110_block26 : P1_7_1_3.blockEstimate 5164 1110 4438 128 = 715036542528 := by decide +kernel

private theorem cost_5164_1110_block27 : P1_7_1_3.blockEstimate 5164 1110 4566 128 = 693320812096 := by decide +kernel

private theorem cost_5164_1110_block28 : P1_7_1_3.blockEstimate 5164 1110 4694 128 = 666945209920 := by decide +kernel

private theorem cost_5164_1110_block29 : P1_7_1_3.blockEstimate 5164 1110 4822 128 = 635909736000 := by decide +kernel

private theorem cost_5164_1110_block30 : P1_7_1_3.blockEstimate 5164 1110 4950 128 = 600214390336 := by decide +kernel

private theorem cost_5164_1110_block31 : P1_7_1_3.blockEstimate 5164 1110 5078 128 = 559878287254 := by decide +kernel

private theorem cost_5164_1110_block32 : P1_7_1_3.blockEstimate 5164 1110 5206 128 = 516119076179 := by decide +kernel

private theorem cost_5164_1110_block33 : P1_7_1_3.blockEstimate 5164 1110 5334 128 = 471129846753 := by decide +kernel

private theorem cost_5164_1110_block34 : P1_7_1_3.blockEstimate 5164 1110 5462 128 = 425631913815 := by decide +kernel

private theorem cost_5164_1110_block35 : P1_7_1_3.blockEstimate 5164 1110 5590 128 = 380175166039 := by decide +kernel

private theorem cost_5164_1110_block36 : P1_7_1_3.blockEstimate 5164 1110 5718 128 = 335286295709 := by decide +kernel

private theorem cost_5164_1110_block37 : P1_7_1_3.blockEstimate 5164 1110 5846 128 = 291468801138 := by decide +kernel

private theorem cost_5164_1110_block38 : P1_7_1_3.blockEstimate 5164 1110 5974 128 = 249202984471 := by decide +kernel

private theorem cost_5164_1110_block39 : P1_7_1_3.blockEstimate 5164 1110 6102 128 = 208945953044 := by decide +kernel

private theorem cost_5164_1110_block40 : P1_7_1_3.blockEstimate 5164 1110 6230 128 = 171013245021 := by decide +kernel

private theorem cost_5164_1110_block41 : P1_7_1_3.blockEstimate 5164 1110 6358 128 = 135703587056 := by decide +kernel

private theorem cost_5164_1110_block42 : P1_7_1_3.blockEstimate 5164 1110 6486 128 = 103876328688 := by decide +kernel

private theorem cost_5164_1110_block43 : P1_7_1_3.blockEstimate 5164 1110 6614 128 = 75822698736 := by decide +kernel

private theorem cost_5164_1110_block44 : P1_7_1_3.blockEstimate 5164 1110 6742 128 = 51794355440 := by decide +kernel

private theorem cost_5164_1110_block45 : P1_7_1_3.blockEstimate 5164 1110 6870 128 = 32042957040 := by decide +kernel

private theorem cost_5164_1110_block46 : P1_7_1_3.blockEstimate 5164 1110 6998 128 = 16820161776 := by decide +kernel

private theorem cost_5164_1110_block47 : P1_7_1_3.blockEstimate 5164 1110 7126 128 = 6377627888 := by decide +kernel

private theorem cost_5164_1110_block48 : P1_7_1_3.blockEstimate 5164 1110 7254 128 = 967013616 := by decide +kernel

private theorem cost_5164_1110_block49 : P1_7_1_3.blockEstimate 5164 1110 7382 2 = 15491 := by decide +kernel

private theorem cost_5164_1110_join0_0 : P1_7_1_3.blockEstimate 5164 1110 1110 256 = 14068188224 :=
  @P1_7_1_3.block_append 5164 1110 1110 1238 128 128 256 1813396000 12254792224 14068188224 cost_5164_1110_block0 cost_5164_1110_block1 rfl rfl rfl

private theorem cost_5164_1110_join0_2 : P1_7_1_3.blockEstimate 5164 1110 1366 256 = 93502817344 :=
  @P1_7_1_3.block_append 5164 1110 1366 1494 128 128 256 32314776096 61188041248 93502817344 cost_5164_1110_block2 cost_5164_1110_block3 rfl rfl rfl

private theorem cost_5164_1110_join0_4 : P1_7_1_3.blockEstimate 5164 1110 1622 256 = 240222471232 :=
  @P1_7_1_3.block_append 5164 1110 1622 1750 128 128 256 98069281312 142153189920 240222471232 cost_5164_1110_block4 cost_5164_1110_block5 rfl rfl rfl

private theorem cost_5164_1110_join0_6 : P1_7_1_3.blockEstimate 5164 1110 1878 256 = 441342248000 :=
  @P1_7_1_3.block_append 5164 1110 1878 2006 128 128 256 192634460704 248707787296 441342248000 cost_5164_1110_block6 cost_5164_1110_block7 rfl rfl rfl

private theorem cost_5164_1110_join0_8 : P1_7_1_3.blockEstimate 5164 1110 2134 256 = 680761798525 :=
  @P1_7_1_3.block_append 5164 1110 2134 2262 128 128 256 309518215485 371243583040 680761798525 cost_5164_1110_block8 cost_5164_1110_block9 rfl rfl rfl

private theorem cost_5164_1110_join0_10 : P1_7_1_3.blockEstimate 5164 1110 2390 256 = 910333561984 :=
  @P1_7_1_3.block_append 5164 1110 2390 2518 128 128 256 428745672256 481587889728 910333561984 cost_5164_1110_block10 cost_5164_1110_block11 rfl rfl rfl

private theorem cost_5164_1110_join0_12 : P1_7_1_3.blockEstimate 5164 1110 2646 256 = 1103062944896 :=
  @P1_7_1_3.block_append 5164 1110 2646 2774 128 128 256 529770235456 573292709440 1103062944896 cost_5164_1110_block12 cost_5164_1110_block13 rfl rfl rfl

private theorem cost_5164_1110_join0_14 : P1_7_1_3.blockEstimate 5164 1110 2902 256 = 1258513353856 :=
  @P1_7_1_3.block_append 5164 1110 2902 3030 128 128 256 612155311680 646358042176 1258513353856 cost_5164_1110_block14 cost_5164_1110_block15 rfl rfl rfl

private theorem cost_5164_1110_join0_16 : P1_7_1_3.blockEstimate 5164 1110 3158 256 = 1376684788864 :=
  @P1_7_1_3.block_append 5164 1110 3158 3286 128 128 256 675900900928 700783887936 1376684788864 cost_5164_1110_block16 cost_5164_1110_block17 rfl rfl rfl

private theorem cost_5164_1110_join0_18 : P1_7_1_3.blockEstimate 5164 1110 3414 256 = 1457577249920 :=
  @P1_7_1_3.block_append 5164 1110 3414 3542 128 128 256 721007003200 736570246720 1457577249920 cost_5164_1110_block18 cost_5164_1110_block19 rfl rfl rfl

private theorem cost_5164_1110_join0_20 : P1_7_1_3.blockEstimate 5164 1110 3670 256 = 1501190737024 :=
  @P1_7_1_3.block_append 5164 1110 3670 3798 128 128 256 747473618496 753717118528 1501190737024 cost_5164_1110_block20 cost_5164_1110_block21 rfl rfl rfl

private theorem cost_5164_1110_join0_22 : P1_7_1_3.blockEstimate 5164 1110 3926 256 = 1507525250176 :=
  @P1_7_1_3.block_append 5164 1110 3926 4054 128 128 256 755300746816 752224503360 1507525250176 cost_5164_1110_block22 cost_5164_1110_block23 rfl rfl rfl

private theorem cost_5164_1110_join0_24 : P1_7_1_3.blockEstimate 5164 1110 4182 256 = 1476580789376 :=
  @P1_7_1_3.block_append 5164 1110 4182 4310 128 128 256 744488388160 732092401216 1476580789376 cost_5164_1110_block24 cost_5164_1110_block25 rfl rfl rfl

private theorem cost_5164_1110_join0_26 : P1_7_1_3.blockEstimate 5164 1110 4438 256 = 1408357354624 :=
  @P1_7_1_3.block_append 5164 1110 4438 4566 128 128 256 715036542528 693320812096 1408357354624 cost_5164_1110_block26 cost_5164_1110_block27 rfl rfl rfl

private theorem cost_5164_1110_join0_28 : P1_7_1_3.blockEstimate 5164 1110 4694 256 = 1302854945920 :=
  @P1_7_1_3.block_append 5164 1110 4694 4822 128 128 256 666945209920 635909736000 1302854945920 cost_5164_1110_block28 cost_5164_1110_block29 rfl rfl rfl

private theorem cost_5164_1110_join0_30 : P1_7_1_3.blockEstimate 5164 1110 4950 256 = 1160092677590 :=
  @P1_7_1_3.block_append 5164 1110 4950 5078 128 128 256 600214390336 559878287254 1160092677590 cost_5164_1110_block30 cost_5164_1110_block31 rfl rfl rfl

private theorem cost_5164_1110_join0_32 : P1_7_1_3.blockEstimate 5164 1110 5206 256 = 987248922932 :=
  @P1_7_1_3.block_append 5164 1110 5206 5334 128 128 256 516119076179 471129846753 987248922932 cost_5164_1110_block32 cost_5164_1110_block33 rfl rfl rfl

private theorem cost_5164_1110_join0_34 : P1_7_1_3.blockEstimate 5164 1110 5462 256 = 805807079854 :=
  @P1_7_1_3.block_append 5164 1110 5462 5590 128 128 256 425631913815 380175166039 805807079854 cost_5164_1110_block34 cost_5164_1110_block35 rfl rfl rfl

private theorem cost_5164_1110_join0_36 : P1_7_1_3.blockEstimate 5164 1110 5718 256 = 626755096847 :=
  @P1_7_1_3.block_append 5164 1110 5718 5846 128 128 256 335286295709 291468801138 626755096847 cost_5164_1110_block36 cost_5164_1110_block37 rfl rfl rfl

private theorem cost_5164_1110_join0_38 : P1_7_1_3.blockEstimate 5164 1110 5974 256 = 458148937515 :=
  @P1_7_1_3.block_append 5164 1110 5974 6102 128 128 256 249202984471 208945953044 458148937515 cost_5164_1110_block38 cost_5164_1110_block39 rfl rfl rfl

private theorem cost_5164_1110_join0_40 : P1_7_1_3.blockEstimate 5164 1110 6230 256 = 306716832077 :=
  @P1_7_1_3.block_append 5164 1110 6230 6358 128 128 256 171013245021 135703587056 306716832077 cost_5164_1110_block40 cost_5164_1110_block41 rfl rfl rfl

private theorem cost_5164_1110_join0_42 : P1_7_1_3.blockEstimate 5164 1110 6486 256 = 179699027424 :=
  @P1_7_1_3.block_append 5164 1110 6486 6614 128 128 256 103876328688 75822698736 179699027424 cost_5164_1110_block42 cost_5164_1110_block43 rfl rfl rfl

private theorem cost_5164_1110_join0_44 : P1_7_1_3.blockEstimate 5164 1110 6742 256 = 83837312480 :=
  @P1_7_1_3.block_append 5164 1110 6742 6870 128 128 256 51794355440 32042957040 83837312480 cost_5164_1110_block44 cost_5164_1110_block45 rfl rfl rfl

private theorem cost_5164_1110_join0_46 : P1_7_1_3.blockEstimate 5164 1110 6998 256 = 23197789664 :=
  @P1_7_1_3.block_append 5164 1110 6998 7126 128 128 256 16820161776 6377627888 23197789664 cost_5164_1110_block46 cost_5164_1110_block47 rfl rfl rfl

private theorem cost_5164_1110_join0_48 : P1_7_1_3.blockEstimate 5164 1110 7254 130 = 967029107 :=
  @P1_7_1_3.block_append 5164 1110 7254 7382 128 2 130 967013616 15491 967029107 cost_5164_1110_block48 cost_5164_1110_block49 rfl rfl rfl

private theorem cost_5164_1110_join1_0 : P1_7_1_3.blockEstimate 5164 1110 1110 512 = 107571005568 :=
  @P1_7_1_3.block_append 5164 1110 1110 1366 256 256 512 14068188224 93502817344 107571005568 cost_5164_1110_join0_0 cost_5164_1110_join0_2 rfl rfl rfl

private theorem cost_5164_1110_join1_2 : P1_7_1_3.blockEstimate 5164 1110 1622 512 = 681564719232 :=
  @P1_7_1_3.block_append 5164 1110 1622 1878 256 256 512 240222471232 441342248000 681564719232 cost_5164_1110_join0_4 cost_5164_1110_join0_6 rfl rfl rfl

private theorem cost_5164_1110_join1_4 : P1_7_1_3.blockEstimate 5164 1110 2134 512 = 1591095360509 :=
  @P1_7_1_3.block_append 5164 1110 2134 2390 256 256 512 680761798525 910333561984 1591095360509 cost_5164_1110_join0_8 cost_5164_1110_join0_10 rfl rfl rfl

private theorem cost_5164_1110_join1_6 : P1_7_1_3.blockEstimate 5164 1110 2646 512 = 2361576298752 :=
  @P1_7_1_3.block_append 5164 1110 2646 2902 256 256 512 1103062944896 1258513353856 2361576298752 cost_5164_1110_join0_12 cost_5164_1110_join0_14 rfl rfl rfl

private theorem cost_5164_1110_join1_8 : P1_7_1_3.blockEstimate 5164 1110 3158 512 = 2834262038784 :=
  @P1_7_1_3.block_append 5164 1110 3158 3414 256 256 512 1376684788864 1457577249920 2834262038784 cost_5164_1110_join0_16 cost_5164_1110_join0_18 rfl rfl rfl

private theorem cost_5164_1110_join1_10 : P1_7_1_3.blockEstimate 5164 1110 3670 512 = 3008715987200 :=
  @P1_7_1_3.block_append 5164 1110 3670 3926 256 256 512 1501190737024 1507525250176 3008715987200 cost_5164_1110_join0_20 cost_5164_1110_join0_22 rfl rfl rfl

private theorem cost_5164_1110_join1_12 : P1_7_1_3.blockEstimate 5164 1110 4182 512 = 2884938144000 :=
  @P1_7_1_3.block_append 5164 1110 4182 4438 256 256 512 1476580789376 1408357354624 2884938144000 cost_5164_1110_join0_24 cost_5164_1110_join0_26 rfl rfl rfl

private theorem cost_5164_1110_join1_14 : P1_7_1_3.blockEstimate 5164 1110 4694 512 = 2462947623510 :=
  @P1_7_1_3.block_append 5164 1110 4694 4950 256 256 512 1302854945920 1160092677590 2462947623510 cost_5164_1110_join0_28 cost_5164_1110_join0_30 rfl rfl rfl

private theorem cost_5164_1110_join1_16 : P1_7_1_3.blockEstimate 5164 1110 5206 512 = 1793056002786 :=
  @P1_7_1_3.block_append 5164 1110 5206 5462 256 256 512 987248922932 805807079854 1793056002786 cost_5164_1110_join0_32 cost_5164_1110_join0_34 rfl rfl rfl

private theorem cost_5164_1110_join1_18 : P1_7_1_3.blockEstimate 5164 1110 5718 512 = 1084904034362 :=
  @P1_7_1_3.block_append 5164 1110 5718 5974 256 256 512 626755096847 458148937515 1084904034362 cost_5164_1110_join0_36 cost_5164_1110_join0_38 rfl rfl rfl

private theorem cost_5164_1110_join1_20 : P1_7_1_3.blockEstimate 5164 1110 6230 512 = 486415859501 :=
  @P1_7_1_3.block_append 5164 1110 6230 6486 256 256 512 306716832077 179699027424 486415859501 cost_5164_1110_join0_40 cost_5164_1110_join0_42 rfl rfl rfl

private theorem cost_5164_1110_join1_22 : P1_7_1_3.blockEstimate 5164 1110 6742 512 = 107035102144 :=
  @P1_7_1_3.block_append 5164 1110 6742 6998 256 256 512 83837312480 23197789664 107035102144 cost_5164_1110_join0_44 cost_5164_1110_join0_46 rfl rfl rfl

private theorem cost_5164_1110_join2_0 : P1_7_1_3.blockEstimate 5164 1110 1110 1024 = 789135724800 :=
  @P1_7_1_3.block_append 5164 1110 1110 1622 512 512 1024 107571005568 681564719232 789135724800 cost_5164_1110_join1_0 cost_5164_1110_join1_2 rfl rfl rfl

private theorem cost_5164_1110_join2_2 : P1_7_1_3.blockEstimate 5164 1110 2134 1024 = 3952671659261 :=
  @P1_7_1_3.block_append 5164 1110 2134 2646 512 512 1024 1591095360509 2361576298752 3952671659261 cost_5164_1110_join1_4 cost_5164_1110_join1_6 rfl rfl rfl

private theorem cost_5164_1110_join2_4 : P1_7_1_3.blockEstimate 5164 1110 3158 1024 = 5842978025984 :=
  @P1_7_1_3.block_append 5164 1110 3158 3670 512 512 1024 2834262038784 3008715987200 5842978025984 cost_5164_1110_join1_8 cost_5164_1110_join1_10 rfl rfl rfl

private theorem cost_5164_1110_join2_6 : P1_7_1_3.blockEstimate 5164 1110 4182 1024 = 5347885767510 :=
  @P1_7_1_3.block_append 5164 1110 4182 4694 512 512 1024 2884938144000 2462947623510 5347885767510 cost_5164_1110_join1_12 cost_5164_1110_join1_14 rfl rfl rfl

private theorem cost_5164_1110_join2_8 : P1_7_1_3.blockEstimate 5164 1110 5206 1024 = 2877960037148 :=
  @P1_7_1_3.block_append 5164 1110 5206 5718 512 512 1024 1793056002786 1084904034362 2877960037148 cost_5164_1110_join1_16 cost_5164_1110_join1_18 rfl rfl rfl

private theorem cost_5164_1110_join2_10 : P1_7_1_3.blockEstimate 5164 1110 6230 1024 = 593450961645 :=
  @P1_7_1_3.block_append 5164 1110 6230 6742 512 512 1024 486415859501 107035102144 593450961645 cost_5164_1110_join1_20 cost_5164_1110_join1_22 rfl rfl rfl

private theorem cost_5164_1110_join3_0 : P1_7_1_3.blockEstimate 5164 1110 1110 2048 = 4741807384061 :=
  @P1_7_1_3.block_append 5164 1110 1110 2134 1024 1024 2048 789135724800 3952671659261 4741807384061 cost_5164_1110_join2_0 cost_5164_1110_join2_2 rfl rfl rfl

private theorem cost_5164_1110_join3_2 : P1_7_1_3.blockEstimate 5164 1110 3158 2048 = 11190863793494 :=
  @P1_7_1_3.block_append 5164 1110 3158 4182 1024 1024 2048 5842978025984 5347885767510 11190863793494 cost_5164_1110_join2_4 cost_5164_1110_join2_6 rfl rfl rfl

private theorem cost_5164_1110_join3_4 : P1_7_1_3.blockEstimate 5164 1110 5206 2048 = 3471410998793 :=
  @P1_7_1_3.block_append 5164 1110 5206 6230 1024 1024 2048 2877960037148 593450961645 3471410998793 cost_5164_1110_join2_8 cost_5164_1110_join2_10 rfl rfl rfl

private theorem cost_5164_1110_join4_0 : P1_7_1_3.blockEstimate 5164 1110 1110 4096 = 15932671177555 :=
  @P1_7_1_3.block_append 5164 1110 1110 3158 2048 2048 4096 4741807384061 11190863793494 15932671177555 cost_5164_1110_join3_0 cost_5164_1110_join3_2 rfl rfl rfl

private theorem cost_5164_1110_join4_2 : P1_7_1_3.blockEstimate 5164 1110 5206 2178 = 3472378027900 :=
  @P1_7_1_3.block_append 5164 1110 5206 7254 2048 130 2178 3471410998793 967029107 3472378027900 cost_5164_1110_join3_4 cost_5164_1110_join0_48 rfl rfl rfl

private theorem cost_5164_1110_join5_0 : P1_7_1_3.blockEstimate 5164 1110 1110 6274 = 19405049205455 :=
  @P1_7_1_3.block_append 5164 1110 1110 5206 4096 2178 6274 15932671177555 3472378027900 19405049205455 cost_5164_1110_join4_0 cost_5164_1110_join4_2 rfl rfl rfl

private theorem cost_5164_1110_total : P1_7_1_3.momentEstimate 5164 1110 = 19405049205455 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 5164 + 1110 = 6274 by decide]
  exact cost_5164_1110_join5_0

theorem moment5164_1110 : P1_7_1.groupedPoleMoment 5164 1110 ≤ 19405049205455 :=
  (P1_7_1_3.grouped_bound 5164 1110).trans_eq cost_5164_1110_total
private theorem cost_5167_1111_block0 : P1_7_1_3.blockEstimate 5167 1111 1111 128 = 1814469280 := by decide +kernel

private theorem cost_5167_1111_block1 : P1_7_1_3.blockEstimate 5167 1111 1239 128 = 12262206112 := by decide +kernel

private theorem cost_5167_1111_block2 : P1_7_1_3.blockEstimate 5167 1111 1367 128 = 32334822048 := by decide +kernel

private theorem cost_5167_1111_block3 : P1_7_1_3.blockEstimate 5167 1111 1495 128 = 61227010720 := by decide +kernel

private theorem cost_5167_1111_block4 : P1_7_1_3.blockEstimate 5167 1111 1623 128 = 98133465760 := by decide +kernel

private theorem cost_5167_1111_block5 : P1_7_1_3.blockEstimate 5167 1111 1751 128 = 142248880800 := by decide +kernel

private theorem cost_5167_1111_block6 : P1_7_1_3.blockEstimate 5167 1111 1879 128 = 192767949472 := by decide +kernel

private theorem cost_5167_1111_block7 : P1_7_1_3.blockEstimate 5167 1111 2007 128 = 248885365408 := by decide +kernel

private theorem cost_5167_1111_block8 : P1_7_1_3.blockEstimate 5167 1111 2135 128 = 309749606630 := by decide +kernel

private theorem cost_5167_1111_block9 : P1_7_1_3.blockEstimate 5167 1111 2263 128 = 371578981120 := by decide +kernel

private theorem cost_5167_1111_block10 : P1_7_1_3.blockEstimate 5167 1111 2391 128 = 429196593920 := by decide +kernel

private theorem cost_5167_1111_block11 : P1_7_1_3.blockEstimate 5167 1111 2519 128 = 482150140672 := by decide +kernel

private theorem cost_5167_1111_block12 : P1_7_1_3.blockEstimate 5167 1111 2647 128 = 530439621376 := by decide +kernel

private theorem cost_5167_1111_block13 : P1_7_1_3.blockEstimate 5167 1111 2775 128 = 574065036032 := by decide +kernel

private theorem cost_5167_1111_block14 : P1_7_1_3.blockEstimate 5167 1111 2903 128 = 613026384640 := by decide +kernel

private theorem cost_5167_1111_block15 : P1_7_1_3.blockEstimate 5167 1111 3031 128 = 647323667200 := by decide +kernel

private theorem cost_5167_1111_block16 : P1_7_1_3.blockEstimate 5167 1111 3159 128 = 676956883712 := by decide +kernel

private theorem cost_5167_1111_block17 : P1_7_1_3.blockEstimate 5167 1111 3287 128 = 701926034176 := by decide +kernel

private theorem cost_5167_1111_block18 : P1_7_1_3.blockEstimate 5167 1111 3415 128 = 722231118592 := by decide +kernel

private theorem cost_5167_1111_block19 : P1_7_1_3.blockEstimate 5167 1111 3543 128 = 737872136960 := by decide +kernel

private theorem cost_5167_1111_block20 : P1_7_1_3.blockEstimate 5167 1111 3671 128 = 748849089280 := by decide +kernel

private theorem cost_5167_1111_block21 : P1_7_1_3.blockEstimate 5167 1111 3799 128 = 755161975552 := by decide +kernel

private theorem cost_5167_1111_block22 : P1_7_1_3.blockEstimate 5167 1111 3927 128 = 756810795776 := by decide +kernel

private theorem cost_5167_1111_block23 : P1_7_1_3.blockEstimate 5167 1111 4055 128 = 753795549952 := by decide +kernel

private theorem cost_5167_1111_block24 : P1_7_1_3.blockEstimate 5167 1111 4183 128 = 746116238080 := by decide +kernel

private theorem cost_5167_1111_block25 : P1_7_1_3.blockEstimate 5167 1111 4311 128 = 733772860160 := by decide +kernel

private theorem cost_5167_1111_block26 : P1_7_1_3.blockEstimate 5167 1111 4439 128 = 716765416192 := by decide +kernel

private theorem cost_5167_1111_block27 : P1_7_1_3.blockEstimate 5167 1111 4567 128 = 695093906176 := by decide +kernel

private theorem cost_5167_1111_block28 : P1_7_1_3.blockEstimate 5167 1111 4695 128 = 668758330112 := by decide +kernel

private theorem cost_5167_1111_block29 : P1_7_1_3.blockEstimate 5167 1111 4823 128 = 637758688000 := by decide +kernel

private theorem cost_5167_1111_block30 : P1_7_1_3.blockEstimate 5167 1111 4951 128 = 602094979840 := by decide +kernel

private theorem cost_5167_1111_block31 : P1_7_1_3.blockEstimate 5167 1111 5079 128 = 561783737952 := by decide +kernel

private theorem cost_5167_1111_block32 : P1_7_1_3.blockEstimate 5167 1111 5207 128 = 518007450077 := by decide +kernel

private theorem cost_5167_1111_block33 : P1_7_1_3.blockEstimate 5167 1111 5335 128 = 472978290390 := by decide +kernel

private theorem cost_5167_1111_block34 : P1_7_1_3.blockEstimate 5167 1111 5463 128 = 427428542917 := by decide +kernel

private theorem cost_5167_1111_block35 : P1_7_1_3.blockEstimate 5167 1111 5591 128 = 381908506115 := by decide +kernel

private theorem cost_5167_1111_block36 : P1_7_1_3.blockEstimate 5167 1111 5719 128 = 336945304843 := by decide +kernel

private theorem cost_5167_1111_block37 : P1_7_1_3.blockEstimate 5167 1111 5847 128 = 293042888633 := by decide +kernel

private theorem cost_5167_1111_block38 : P1_7_1_3.blockEstimate 5167 1111 5975 128 = 250682034323 := by decide +kernel

private theorem cost_5167_1111_block39 : P1_7_1_3.blockEstimate 5167 1111 6103 128 = 210320342633 := by decide +kernel

private theorem cost_5167_1111_block40 : P1_7_1_3.blockEstimate 5167 1111 6231 128 = 172281291217 := by decide +kernel

private theorem cost_5167_1111_block41 : P1_7_1_3.blockEstimate 5167 1111 6359 128 = 136846241232 := by decide +kernel

private theorem cost_5167_1111_block42 : P1_7_1_3.blockEstimate 5167 1111 6487 128 = 104882907600 := by decide +kernel

private theorem cost_5167_1111_block43 : P1_7_1_3.blockEstimate 5167 1111 6615 128 = 76688483792 := by decide +kernel

private theorem cost_5167_1111_block44 : P1_7_1_3.blockEstimate 5167 1111 6743 128 = 52514628048 := by decide +kernel

private theorem cost_5167_1111_block45 : P1_7_1_3.blockEstimate 5167 1111 6871 128 = 32612998608 := by decide +kernel

private theorem cost_5167_1111_block46 : P1_7_1_3.blockEstimate 5167 1111 6999 128 = 17235253712 := by decide +kernel

private theorem cost_5167_1111_block47 : P1_7_1_3.blockEstimate 5167 1111 7127 128 = 6633051600 := by decide +kernel

private theorem cost_5167_1111_block48 : P1_7_1_3.blockEstimate 5167 1111 7255 128 = 1058050512 := by decide +kernel

private theorem cost_5167_1111_block49 : P1_7_1_3.blockEstimate 5167 1111 7383 6 = 175603 := by decide +kernel

private theorem cost_5167_1111_join0_0 : P1_7_1_3.blockEstimate 5167 1111 1111 256 = 14076675392 :=
  @P1_7_1_3.block_append 5167 1111 1111 1239 128 128 256 1814469280 12262206112 14076675392 cost_5167_1111_block0 cost_5167_1111_block1 rfl rfl rfl

private theorem cost_5167_1111_join0_2 : P1_7_1_3.blockEstimate 5167 1111 1367 256 = 93561832768 :=
  @P1_7_1_3.block_append 5167 1111 1367 1495 128 128 256 32334822048 61227010720 93561832768 cost_5167_1111_block2 cost_5167_1111_block3 rfl rfl rfl

private theorem cost_5167_1111_join0_4 : P1_7_1_3.blockEstimate 5167 1111 1623 256 = 240382346560 :=
  @P1_7_1_3.block_append 5167 1111 1623 1751 128 128 256 98133465760 142248880800 240382346560 cost_5167_1111_block4 cost_5167_1111_block5 rfl rfl rfl

private theorem cost_5167_1111_join0_6 : P1_7_1_3.blockEstimate 5167 1111 1879 256 = 441653314880 :=
  @P1_7_1_3.block_append 5167 1111 1879 2007 128 128 256 192767949472 248885365408 441653314880 cost_5167_1111_block6 cost_5167_1111_block7 rfl rfl rfl

private theorem cost_5167_1111_join0_8 : P1_7_1_3.blockEstimate 5167 1111 2135 256 = 681328587750 :=
  @P1_7_1_3.block_append 5167 1111 2135 2263 128 128 256 309749606630 371578981120 681328587750 cost_5167_1111_block8 cost_5167_1111_block9 rfl rfl rfl

private theorem cost_5167_1111_join0_10 : P1_7_1_3.blockEstimate 5167 1111 2391 256 = 911346734592 :=
  @P1_7_1_3.block_append 5167 1111 2391 2519 128 128 256 429196593920 482150140672 911346734592 cost_5167_1111_block10 cost_5167_1111_block11 rfl rfl rfl

private theorem cost_5167_1111_join0_12 : P1_7_1_3.blockEstimate 5167 1111 2647 256 = 1104504657408 :=
  @P1_7_1_3.block_append 5167 1111 2647 2775 128 128 256 530439621376 574065036032 1104504657408 cost_5167_1111_block12 cost_5167_1111_block13 rfl rfl rfl

private theorem cost_5167_1111_join0_14 : P1_7_1_3.blockEstimate 5167 1111 2903 256 = 1260350051840 :=
  @P1_7_1_3.block_append 5167 1111 2903 3031 128 128 256 613026384640 647323667200 1260350051840 cost_5167_1111_block14 cost_5167_1111_block15 rfl rfl rfl

private theorem cost_5167_1111_join0_16 : P1_7_1_3.blockEstimate 5167 1111 3159 256 = 1378882917888 :=
  @P1_7_1_3.block_append 5167 1111 3159 3287 128 128 256 676956883712 701926034176 1378882917888 cost_5167_1111_block16 cost_5167_1111_block17 rfl rfl rfl

private theorem cost_5167_1111_join0_18 : P1_7_1_3.blockEstimate 5167 1111 3415 256 = 1460103255552 :=
  @P1_7_1_3.block_append 5167 1111 3415 3543 128 128 256 722231118592 737872136960 1460103255552 cost_5167_1111_block18 cost_5167_1111_block19 rfl rfl rfl

private theorem cost_5167_1111_join0_20 : P1_7_1_3.blockEstimate 5167 1111 3671 256 = 1504011064832 :=
  @P1_7_1_3.block_append 5167 1111 3671 3799 128 128 256 748849089280 755161975552 1504011064832 cost_5167_1111_block20 cost_5167_1111_block21 rfl rfl rfl

private theorem cost_5167_1111_join0_22 : P1_7_1_3.blockEstimate 5167 1111 3927 256 = 1510606345728 :=
  @P1_7_1_3.block_append 5167 1111 3927 4055 128 128 256 756810795776 753795549952 1510606345728 cost_5167_1111_block22 cost_5167_1111_block23 rfl rfl rfl

private theorem cost_5167_1111_join0_24 : P1_7_1_3.blockEstimate 5167 1111 4183 256 = 1479889098240 :=
  @P1_7_1_3.block_append 5167 1111 4183 4311 128 128 256 746116238080 733772860160 1479889098240 cost_5167_1111_block24 cost_5167_1111_block25 rfl rfl rfl

private theorem cost_5167_1111_join0_26 : P1_7_1_3.blockEstimate 5167 1111 4439 256 = 1411859322368 :=
  @P1_7_1_3.block_append 5167 1111 4439 4567 128 128 256 716765416192 695093906176 1411859322368 cost_5167_1111_block26 cost_5167_1111_block27 rfl rfl rfl

private theorem cost_5167_1111_join0_28 : P1_7_1_3.blockEstimate 5167 1111 4695 256 = 1306517018112 :=
  @P1_7_1_3.block_append 5167 1111 4695 4823 128 128 256 668758330112 637758688000 1306517018112 cost_5167_1111_block28 cost_5167_1111_block29 rfl rfl rfl

private theorem cost_5167_1111_join0_30 : P1_7_1_3.blockEstimate 5167 1111 4951 256 = 1163878717792 :=
  @P1_7_1_3.block_append 5167 1111 4951 5079 128 128 256 602094979840 561783737952 1163878717792 cost_5167_1111_block30 cost_5167_1111_block31 rfl rfl rfl

private theorem cost_5167_1111_join0_32 : P1_7_1_3.blockEstimate 5167 1111 5207 256 = 990985740467 :=
  @P1_7_1_3.block_append 5167 1111 5207 5335 128 128 256 518007450077 472978290390 990985740467 cost_5167_1111_block32 cost_5167_1111_block33 rfl rfl rfl

private theorem cost_5167_1111_join0_34 : P1_7_1_3.blockEstimate 5167 1111 5463 256 = 809337049032 :=
  @P1_7_1_3.block_append 5167 1111 5463 5591 128 128 256 427428542917 381908506115 809337049032 cost_5167_1111_block34 cost_5167_1111_block35 rfl rfl rfl

private theorem cost_5167_1111_join0_36 : P1_7_1_3.blockEstimate 5167 1111 5719 256 = 629988193476 :=
  @P1_7_1_3.block_append 5167 1111 5719 5847 128 128 256 336945304843 293042888633 629988193476 cost_5167_1111_block36 cost_5167_1111_block37 rfl rfl rfl

private theorem cost_5167_1111_join0_38 : P1_7_1_3.blockEstimate 5167 1111 5975 256 = 461002376956 :=
  @P1_7_1_3.block_append 5167 1111 5975 6103 128 128 256 250682034323 210320342633 461002376956 cost_5167_1111_block38 cost_5167_1111_block39 rfl rfl rfl

private theorem cost_5167_1111_join0_40 : P1_7_1_3.blockEstimate 5167 1111 6231 256 = 309127532449 :=
  @P1_7_1_3.block_append 5167 1111 6231 6359 128 128 256 172281291217 136846241232 309127532449 cost_5167_1111_block40 cost_5167_1111_block41 rfl rfl rfl

private theorem cost_5167_1111_join0_42 : P1_7_1_3.blockEstimate 5167 1111 6487 256 = 181571391392 :=
  @P1_7_1_3.block_append 5167 1111 6487 6615 128 128 256 104882907600 76688483792 181571391392 cost_5167_1111_block42 cost_5167_1111_block43 rfl rfl rfl

private theorem cost_5167_1111_join0_44 : P1_7_1_3.blockEstimate 5167 1111 6743 256 = 85127626656 :=
  @P1_7_1_3.block_append 5167 1111 6743 6871 128 128 256 52514628048 32612998608 85127626656 cost_5167_1111_block44 cost_5167_1111_block45 rfl rfl rfl

private theorem cost_5167_1111_join0_46 : P1_7_1_3.blockEstimate 5167 1111 6999 256 = 23868305312 :=
  @P1_7_1_3.block_append 5167 1111 6999 7127 128 128 256 17235253712 6633051600 23868305312 cost_5167_1111_block46 cost_5167_1111_block47 rfl rfl rfl

private theorem cost_5167_1111_join0_48 : P1_7_1_3.blockEstimate 5167 1111 7255 134 = 1058226115 :=
  @P1_7_1_3.block_append 5167 1111 7255 7383 128 6 134 1058050512 175603 1058226115 cost_5167_1111_block48 cost_5167_1111_block49 rfl rfl rfl

private theorem cost_5167_1111_join1_0 : P1_7_1_3.blockEstimate 5167 1111 1111 512 = 107638508160 :=
  @P1_7_1_3.block_append 5167 1111 1111 1367 256 256 512 14076675392 93561832768 107638508160 cost_5167_1111_join0_0 cost_5167_1111_join0_2 rfl rfl rfl

private theorem cost_5167_1111_join1_2 : P1_7_1_3.blockEstimate 5167 1111 1623 512 = 682035661440 :=
  @P1_7_1_3.block_append 5167 1111 1623 1879 256 256 512 240382346560 441653314880 682035661440 cost_5167_1111_join0_4 cost_5167_1111_join0_6 rfl rfl rfl

private theorem cost_5167_1111_join1_4 : P1_7_1_3.blockEstimate 5167 1111 2135 512 = 1592675322342 :=
  @P1_7_1_3.block_append 5167 1111 2135 2391 256 256 512 681328587750 911346734592 1592675322342 cost_5167_1111_join0_8 cost_5167_1111_join0_10 rfl rfl rfl

private theorem cost_5167_1111_join1_6 : P1_7_1_3.blockEstimate 5167 1111 2647 512 = 2364854709248 :=
  @P1_7_1_3.block_append 5167 1111 2647 2903 256 256 512 1104504657408 1260350051840 2364854709248 cost_5167_1111_join0_12 cost_5167_1111_join0_14 rfl rfl rfl

private theorem cost_5167_1111_join1_8 : P1_7_1_3.blockEstimate 5167 1111 3159 512 = 2838986173440 :=
  @P1_7_1_3.block_append 5167 1111 3159 3415 256 256 512 1378882917888 1460103255552 2838986173440 cost_5167_1111_join0_16 cost_5167_1111_join0_18 rfl rfl rfl

private theorem cost_5167_1111_join1_10 : P1_7_1_3.blockEstimate 5167 1111 3671 512 = 3014617410560 :=
  @P1_7_1_3.block_append 5167 1111 3671 3927 256 256 512 1504011064832 1510606345728 3014617410560 cost_5167_1111_join0_20 cost_5167_1111_join0_22 rfl rfl rfl

private theorem cost_5167_1111_join1_12 : P1_7_1_3.blockEstimate 5167 1111 4183 512 = 2891748420608 :=
  @P1_7_1_3.block_append 5167 1111 4183 4439 256 256 512 1479889098240 1411859322368 2891748420608 cost_5167_1111_join0_24 cost_5167_1111_join0_26 rfl rfl rfl

private theorem cost_5167_1111_join1_14 : P1_7_1_3.blockEstimate 5167 1111 4695 512 = 2470395735904 :=
  @P1_7_1_3.block_append 5167 1111 4695 4951 256 256 512 1306517018112 1163878717792 2470395735904 cost_5167_1111_join0_28 cost_5167_1111_join0_30 rfl rfl rfl

private theorem cost_5167_1111_join1_16 : P1_7_1_3.blockEstimate 5167 1111 5207 512 = 1800322789499 :=
  @P1_7_1_3.block_append 5167 1111 5207 5463 256 256 512 990985740467 809337049032 1800322789499 cost_5167_1111_join0_32 cost_5167_1111_join0_34 rfl rfl rfl

private theorem cost_5167_1111_join1_18 : P1_7_1_3.blockEstimate 5167 1111 5719 512 = 1090990570432 :=
  @P1_7_1_3.block_append 5167 1111 5719 5975 256 256 512 629988193476 461002376956 1090990570432 cost_5167_1111_join0_36 cost_5167_1111_join0_38 rfl rfl rfl

private theorem cost_5167_1111_join1_20 : P1_7_1_3.blockEstimate 5167 1111 6231 512 = 490698923841 :=
  @P1_7_1_3.block_append 5167 1111 6231 6487 256 256 512 309127532449 181571391392 490698923841 cost_5167_1111_join0_40 cost_5167_1111_join0_42 rfl rfl rfl

private theorem cost_5167_1111_join1_22 : P1_7_1_3.blockEstimate 5167 1111 6743 512 = 108995931968 :=
  @P1_7_1_3.block_append 5167 1111 6743 6999 256 256 512 85127626656 23868305312 108995931968 cost_5167_1111_join0_44 cost_5167_1111_join0_46 rfl rfl rfl

private theorem cost_5167_1111_join2_0 : P1_7_1_3.blockEstimate 5167 1111 1111 1024 = 789674169600 :=
  @P1_7_1_3.block_append 5167 1111 1111 1623 512 512 1024 107638508160 682035661440 789674169600 cost_5167_1111_join1_0 cost_5167_1111_join1_2 rfl rfl rfl

private theorem cost_5167_1111_join2_2 : P1_7_1_3.blockEstimate 5167 1111 2135 1024 = 3957530031590 :=
  @P1_7_1_3.block_append 5167 1111 2135 2647 512 512 1024 1592675322342 2364854709248 3957530031590 cost_5167_1111_join1_4 cost_5167_1111_join1_6 rfl rfl rfl

private theorem cost_5167_1111_join2_4 : P1_7_1_3.blockEstimate 5167 1111 3159 1024 = 5853603584000 :=
  @P1_7_1_3.block_append 5167 1111 3159 3671 512 512 1024 2838986173440 3014617410560 5853603584000 cost_5167_1111_join1_8 cost_5167_1111_join1_10 rfl rfl rfl

private theorem cost_5167_1111_join2_6 : P1_7_1_3.blockEstimate 5167 1111 4183 1024 = 5362144156512 :=
  @P1_7_1_3.block_append 5167 1111 4183 4695 512 512 1024 2891748420608 2470395735904 5362144156512 cost_5167_1111_join1_12 cost_5167_1111_join1_14 rfl rfl rfl

private theorem cost_5167_1111_join2_8 : P1_7_1_3.blockEstimate 5167 1111 5207 1024 = 2891313359931 :=
  @P1_7_1_3.block_append 5167 1111 5207 5719 512 512 1024 1800322789499 1090990570432 2891313359931 cost_5167_1111_join1_16 cost_5167_1111_join1_18 rfl rfl rfl

private theorem cost_5167_1111_join2_10 : P1_7_1_3.blockEstimate 5167 1111 6231 1024 = 599694855809 :=
  @P1_7_1_3.block_append 5167 1111 6231 6743 512 512 1024 490698923841 108995931968 599694855809 cost_5167_1111_join1_20 cost_5167_1111_join1_22 rfl rfl rfl

private theorem cost_5167_1111_join3_0 : P1_7_1_3.blockEstimate 5167 1111 1111 2048 = 4747204201190 :=
  @P1_7_1_3.block_append 5167 1111 1111 2135 1024 1024 2048 789674169600 3957530031590 4747204201190 cost_5167_1111_join2_0 cost_5167_1111_join2_2 rfl rfl rfl

private theorem cost_5167_1111_join3_2 : P1_7_1_3.blockEstimate 5167 1111 3159 2048 = 11215747740512 :=
  @P1_7_1_3.block_append 5167 1111 3159 4183 1024 1024 2048 5853603584000 5362144156512 11215747740512 cost_5167_1111_join2_4 cost_5167_1111_join2_6 rfl rfl rfl

private theorem cost_5167_1111_join3_4 : P1_7_1_3.blockEstimate 5167 1111 5207 2048 = 3491008215740 :=
  @P1_7_1_3.block_append 5167 1111 5207 6231 1024 1024 2048 2891313359931 599694855809 3491008215740 cost_5167_1111_join2_8 cost_5167_1111_join2_10 rfl rfl rfl

private theorem cost_5167_1111_join4_0 : P1_7_1_3.blockEstimate 5167 1111 1111 4096 = 15962951941702 :=
  @P1_7_1_3.block_append 5167 1111 1111 3159 2048 2048 4096 4747204201190 11215747740512 15962951941702 cost_5167_1111_join3_0 cost_5167_1111_join3_2 rfl rfl rfl

private theorem cost_5167_1111_join4_2 : P1_7_1_3.blockEstimate 5167 1111 5207 2182 = 3492066441855 :=
  @P1_7_1_3.block_append 5167 1111 5207 7255 2048 134 2182 3491008215740 1058226115 3492066441855 cost_5167_1111_join3_4 cost_5167_1111_join0_48 rfl rfl rfl

private theorem cost_5167_1111_join5_0 : P1_7_1_3.blockEstimate 5167 1111 1111 6278 = 19455018383557 :=
  @P1_7_1_3.block_append 5167 1111 1111 5207 4096 2182 6278 15962951941702 3492066441855 19455018383557 cost_5167_1111_join4_0 cost_5167_1111_join4_2 rfl rfl rfl

private theorem cost_5167_1111_total : P1_7_1_3.momentEstimate 5167 1111 = 19455018383557 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 5167 + 1111 = 6278 by decide]
  exact cost_5167_1111_join5_0

theorem moment5167_1111 : P1_7_1.groupedPoleMoment 5167 1111 ≤ 19455018383557 :=
  (P1_7_1_3.grouped_bound 5167 1111).trans_eq cost_5167_1111_total
private theorem cost_5225_1133_block0 : P1_7_1_3.blockEstimate 5225 1133 1133 128 = 1835219360 := by decide +kernel

private theorem cost_5225_1133_block1 : P1_7_1_3.blockEstimate 5225 1133 1261 128 = 12405541280 := by decide +kernel

private theorem cost_5225_1133_block2 : P1_7_1_3.blockEstimate 5225 1133 1389 128 = 32722377120 := by decide +kernel

private theorem cost_5225_1133_block3 : P1_7_1_3.blockEstimate 5225 1133 1517 128 = 61980420512 := by decide +kernel

private theorem cost_5225_1133_block4 : P1_7_1_3.blockEstimate 5225 1133 1645 128 = 99374365088 := by decide +kernel

private theorem cost_5225_1133_block5 : P1_7_1_3.blockEstimate 5225 1133 1773 128 = 144098904480 := by decide +kernel

private theorem cost_5225_1133_block6 : P1_7_1_3.blockEstimate 5225 1133 1901 128 = 195348732320 := by decide +kernel

private theorem cost_5225_1133_block7 : P1_7_1_3.blockEstimate 5225 1133 2029 128 = 252318542240 := by decide +kernel

private theorem cost_5225_1133_block8 : P1_7_1_3.blockEstimate 5225 1133 2157 128 = 314198378667 := by decide +kernel

private theorem cost_5225_1133_block9 : P1_7_1_3.blockEstimate 5225 1133 2285 128 = 378093344832 := by decide +kernel

private theorem cost_5225_1133_block10 : P1_7_1_3.blockEstimate 5225 1133 2413 128 = 438132856896 := by decide +kernel

private theorem cost_5225_1133_block11 : P1_7_1_3.blockEstimate 5225 1133 2541 128 = 493416028224 := by decide +kernel

private theorem cost_5225_1133_block12 : P1_7_1_3.blockEstimate 5225 1133 2669 128 = 543942858816 := by decide +kernel

private theorem cost_5225_1133_block13 : P1_7_1_3.blockEstimate 5225 1133 2797 128 = 589713348672 := by decide +kernel

private theorem cost_5225_1133_block14 : P1_7_1_3.blockEstimate 5225 1133 2925 128 = 630727497792 := by decide +kernel

private theorem cost_5225_1133_block15 : P1_7_1_3.blockEstimate 5225 1133 3053 128 = 666985306176 := by decide +kernel

private theorem cost_5225_1133_block16 : P1_7_1_3.blockEstimate 5225 1133 3181 128 = 698486773824 := by decide +kernel

private theorem cost_5225_1133_block17 : P1_7_1_3.blockEstimate 5225 1133 3309 128 = 725231900736 := by decide +kernel

private theorem cost_5225_1133_block18 : P1_7_1_3.blockEstimate 5225 1133 3437 128 = 747220686912 := by decide +kernel

private theorem cost_5225_1133_block19 : P1_7_1_3.blockEstimate 5225 1133 3565 128 = 764453132352 := by decide +kernel

private theorem cost_5225_1133_block20 : P1_7_1_3.blockEstimate 5225 1133 3693 128 = 776929237056 := by decide +kernel

private theorem cost_5225_1133_block21 : P1_7_1_3.blockEstimate 5225 1133 3821 128 = 784649001024 := by decide +kernel

private theorem cost_5225_1133_block22 : P1_7_1_3.blockEstimate 5225 1133 3949 128 = 787612424256 := by decide +kernel

private theorem cost_5225_1133_block23 : P1_7_1_3.blockEstimate 5225 1133 4077 128 = 785819506752 := by decide +kernel

private theorem cost_5225_1133_block24 : P1_7_1_3.blockEstimate 5225 1133 4205 128 = 779270248512 := by decide +kernel

private theorem cost_5225_1133_block25 : P1_7_1_3.blockEstimate 5225 1133 4333 128 = 767964649536 := by decide +kernel

private theorem cost_5225_1133_block26 : P1_7_1_3.blockEstimate 5225 1133 4461 128 = 751902709824 := by decide +kernel

private theorem cost_5225_1133_block27 : P1_7_1_3.blockEstimate 5225 1133 4589 128 = 731084429376 := by decide +kernel

private theorem cost_5225_1133_block28 : P1_7_1_3.blockEstimate 5225 1133 4717 128 = 705509808192 := by decide +kernel

private theorem cost_5225_1133_block29 : P1_7_1_3.blockEstimate 5225 1133 4845 128 = 675178846272 := by decide +kernel

private theorem cost_5225_1133_block30 : P1_7_1_3.blockEstimate 5225 1133 4973 128 = 640091543616 := by decide +kernel

private theorem cost_5225_1133_block31 : P1_7_1_3.blockEstimate 5225 1133 5101 128 = 600247920966 := by decide +kernel

private theorem cost_5225_1133_block32 : P1_7_1_3.blockEstimate 5225 1133 5229 128 = 556250001299 := by decide +kernel

private theorem cost_5225_1133_block33 : P1_7_1_3.blockEstimate 5225 1133 5357 128 = 510472712667 := by decide +kernel

private theorem cost_5225_1133_block34 : P1_7_1_3.blockEstimate 5225 1133 5485 128 = 463938881229 := by decide +kernel

private theorem cost_5225_1133_block35 : P1_7_1_3.blockEstimate 5225 1133 5613 128 = 417206237594 := by decide +kernel

private theorem cost_5225_1133_block36 : P1_7_1_3.blockEstimate 5225 1133 5741 128 = 370809789105 := by decide +kernel

private theorem cost_5225_1133_block37 : P1_7_1_3.blockEstimate 5225 1133 5869 128 = 325261817693 := by decide +kernel

private theorem cost_5225_1133_block38 : P1_7_1_3.blockEstimate 5225 1133 5997 128 = 281051880043 := by decide +kernel

private theorem cost_5225_1133_block39 : P1_7_1_3.blockEstimate 5225 1133 6125 128 = 238646809864 := by decide +kernel

private theorem cost_5225_1133_block40 : P1_7_1_3.blockEstimate 5225 1133 6253 128 = 198480037746 := by decide +kernel

private theorem cost_5225_1133_block41 : P1_7_1_3.blockEstimate 5225 1133 6381 128 = 160664444048 := by decide +kernel

private theorem cost_5225_1133_block42 : P1_7_1_3.blockEstimate 5225 1133 6509 128 = 126006040720 := by decide +kernel

private theorem cost_5225_1133_block43 : P1_7_1_3.blockEstimate 5225 1133 6637 128 = 95020078224 := by decide +kernel

private theorem cost_5225_1133_block44 : P1_7_1_3.blockEstimate 5225 1133 6765 128 = 67958214800 := by decide +kernel

private theorem cost_5225_1133_block45 : P1_7_1_3.blockEstimate 5225 1133 6893 128 = 45072108688 := by decide +kernel

private theorem cost_5225_1133_block46 : P1_7_1_3.blockEstimate 5225 1133 7021 128 = 26613418128 := by decide +kernel

private theorem cost_5225_1133_block47 : P1_7_1_3.blockEstimate 5225 1133 7149 128 = 12833801360 := by decide +kernel

private theorem cost_5225_1133_block48 : P1_7_1_3.blockEstimate 5225 1133 7277 128 = 3984916624 := by decide +kernel

private theorem cost_5225_1133_block49 : P1_7_1_3.blockEstimate 5225 1133 7405 86 = 289415225 := by decide +kernel

private theorem cost_5225_1133_join0_0 : P1_7_1_3.blockEstimate 5225 1133 1133 256 = 14240760640 :=
  @P1_7_1_3.block_append 5225 1133 1133 1261 128 128 256 1835219360 12405541280 14240760640 cost_5225_1133_block0 cost_5225_1133_block1 rfl rfl rfl

private theorem cost_5225_1133_join0_2 : P1_7_1_3.blockEstimate 5225 1133 1389 256 = 94702797632 :=
  @P1_7_1_3.block_append 5225 1133 1389 1517 128 128 256 32722377120 61980420512 94702797632 cost_5225_1133_block2 cost_5225_1133_block3 rfl rfl rfl

private theorem cost_5225_1133_join0_4 : P1_7_1_3.blockEstimate 5225 1133 1645 256 = 243473269568 :=
  @P1_7_1_3.block_append 5225 1133 1645 1773 128 128 256 99374365088 144098904480 243473269568 cost_5225_1133_block4 cost_5225_1133_block5 rfl rfl rfl

private theorem cost_5225_1133_join0_6 : P1_7_1_3.blockEstimate 5225 1133 1901 256 = 447667274560 :=
  @P1_7_1_3.block_append 5225 1133 1901 2029 128 128 256 195348732320 252318542240 447667274560 cost_5225_1133_block6 cost_5225_1133_block7 rfl rfl rfl

private theorem cost_5225_1133_join0_8 : P1_7_1_3.blockEstimate 5225 1133 2157 256 = 692291723499 :=
  @P1_7_1_3.block_append 5225 1133 2157 2285 128 128 256 314198378667 378093344832 692291723499 cost_5225_1133_block8 cost_5225_1133_block9 rfl rfl rfl

private theorem cost_5225_1133_join0_10 : P1_7_1_3.blockEstimate 5225 1133 2413 256 = 931548885120 :=
  @P1_7_1_3.block_append 5225 1133 2413 2541 128 128 256 438132856896 493416028224 931548885120 cost_5225_1133_block10 cost_5225_1133_block11 rfl rfl rfl

private theorem cost_5225_1133_join0_12 : P1_7_1_3.blockEstimate 5225 1133 2669 256 = 1133656207488 :=
  @P1_7_1_3.block_append 5225 1133 2669 2797 128 128 256 543942858816 589713348672 1133656207488 cost_5225_1133_block12 cost_5225_1133_block13 rfl rfl rfl

private theorem cost_5225_1133_join0_14 : P1_7_1_3.blockEstimate 5225 1133 2925 256 = 1297712803968 :=
  @P1_7_1_3.block_append 5225 1133 2925 3053 128 128 256 630727497792 666985306176 1297712803968 cost_5225_1133_block14 cost_5225_1133_block15 rfl rfl rfl

private theorem cost_5225_1133_join0_16 : P1_7_1_3.blockEstimate 5225 1133 3181 256 = 1423718674560 :=
  @P1_7_1_3.block_append 5225 1133 3181 3309 128 128 256 698486773824 725231900736 1423718674560 cost_5225_1133_block16 cost_5225_1133_block17 rfl rfl rfl

private theorem cost_5225_1133_join0_18 : P1_7_1_3.blockEstimate 5225 1133 3437 256 = 1511673819264 :=
  @P1_7_1_3.block_append 5225 1133 3437 3565 128 128 256 747220686912 764453132352 1511673819264 cost_5225_1133_block18 cost_5225_1133_block19 rfl rfl rfl

private theorem cost_5225_1133_join0_20 : P1_7_1_3.blockEstimate 5225 1133 3693 256 = 1561578238080 :=
  @P1_7_1_3.block_append 5225 1133 3693 3821 128 128 256 776929237056 784649001024 1561578238080 cost_5225_1133_block20 cost_5225_1133_block21 rfl rfl rfl

private theorem cost_5225_1133_join0_22 : P1_7_1_3.blockEstimate 5225 1133 3949 256 = 1573431931008 :=
  @P1_7_1_3.block_append 5225 1133 3949 4077 128 128 256 787612424256 785819506752 1573431931008 cost_5225_1133_block22 cost_5225_1133_block23 rfl rfl rfl

private theorem cost_5225_1133_join0_24 : P1_7_1_3.blockEstimate 5225 1133 4205 256 = 1547234898048 :=
  @P1_7_1_3.block_append 5225 1133 4205 4333 128 128 256 779270248512 767964649536 1547234898048 cost_5225_1133_block24 cost_5225_1133_block25 rfl rfl rfl

private theorem cost_5225_1133_join0_26 : P1_7_1_3.blockEstimate 5225 1133 4461 256 = 1482987139200 :=
  @P1_7_1_3.block_append 5225 1133 4461 4589 128 128 256 751902709824 731084429376 1482987139200 cost_5225_1133_block26 cost_5225_1133_block27 rfl rfl rfl

private theorem cost_5225_1133_join0_28 : P1_7_1_3.blockEstimate 5225 1133 4717 256 = 1380688654464 :=
  @P1_7_1_3.block_append 5225 1133 4717 4845 128 128 256 705509808192 675178846272 1380688654464 cost_5225_1133_block28 cost_5225_1133_block29 rfl rfl rfl

private theorem cost_5225_1133_join0_30 : P1_7_1_3.blockEstimate 5225 1133 4973 256 = 1240339464582 :=
  @P1_7_1_3.block_append 5225 1133 4973 5101 128 128 256 640091543616 600247920966 1240339464582 cost_5225_1133_block30 cost_5225_1133_block31 rfl rfl rfl

private theorem cost_5225_1133_join0_32 : P1_7_1_3.blockEstimate 5225 1133 5229 256 = 1066722713966 :=
  @P1_7_1_3.block_append 5225 1133 5229 5357 128 128 256 556250001299 510472712667 1066722713966 cost_5225_1133_block32 cost_5225_1133_block33 rfl rfl rfl

private theorem cost_5225_1133_join0_34 : P1_7_1_3.blockEstimate 5225 1133 5485 256 = 881145118823 :=
  @P1_7_1_3.block_append 5225 1133 5485 5613 128 128 256 463938881229 417206237594 881145118823 cost_5225_1133_block34 cost_5225_1133_block35 rfl rfl rfl

private theorem cost_5225_1133_join0_36 : P1_7_1_3.blockEstimate 5225 1133 5741 256 = 696071606798 :=
  @P1_7_1_3.block_append 5225 1133 5741 5869 128 128 256 370809789105 325261817693 696071606798 cost_5225_1133_block36 cost_5225_1133_block37 rfl rfl rfl

private theorem cost_5225_1133_join0_38 : P1_7_1_3.blockEstimate 5225 1133 5997 256 = 519698689907 :=
  @P1_7_1_3.block_append 5225 1133 5997 6125 128 128 256 281051880043 238646809864 519698689907 cost_5225_1133_block38 cost_5225_1133_block39 rfl rfl rfl

private theorem cost_5225_1133_join0_40 : P1_7_1_3.blockEstimate 5225 1133 6253 256 = 359144481794 :=
  @P1_7_1_3.block_append 5225 1133 6253 6381 128 128 256 198480037746 160664444048 359144481794 cost_5225_1133_block40 cost_5225_1133_block41 rfl rfl rfl

private theorem cost_5225_1133_join0_42 : P1_7_1_3.blockEstimate 5225 1133 6509 256 = 221026118944 :=
  @P1_7_1_3.block_append 5225 1133 6509 6637 128 128 256 126006040720 95020078224 221026118944 cost_5225_1133_block42 cost_5225_1133_block43 rfl rfl rfl

private theorem cost_5225_1133_join0_44 : P1_7_1_3.blockEstimate 5225 1133 6765 256 = 113030323488 :=
  @P1_7_1_3.block_append 5225 1133 6765 6893 128 128 256 67958214800 45072108688 113030323488 cost_5225_1133_block44 cost_5225_1133_block45 rfl rfl rfl

private theorem cost_5225_1133_join0_46 : P1_7_1_3.blockEstimate 5225 1133 7021 256 = 39447219488 :=
  @P1_7_1_3.block_append 5225 1133 7021 7149 128 128 256 26613418128 12833801360 39447219488 cost_5225_1133_block46 cost_5225_1133_block47 rfl rfl rfl

private theorem cost_5225_1133_join0_48 : P1_7_1_3.blockEstimate 5225 1133 7277 214 = 4274331849 :=
  @P1_7_1_3.block_append 5225 1133 7277 7405 128 86 214 3984916624 289415225 4274331849 cost_5225_1133_block48 cost_5225_1133_block49 rfl rfl rfl

private theorem cost_5225_1133_join1_0 : P1_7_1_3.blockEstimate 5225 1133 1133 512 = 108943558272 :=
  @P1_7_1_3.block_append 5225 1133 1133 1389 256 256 512 14240760640 94702797632 108943558272 cost_5225_1133_join0_0 cost_5225_1133_join0_2 rfl rfl rfl

private theorem cost_5225_1133_join1_2 : P1_7_1_3.blockEstimate 5225 1133 1645 512 = 691140544128 :=
  @P1_7_1_3.block_append 5225 1133 1645 1901 256 256 512 243473269568 447667274560 691140544128 cost_5225_1133_join0_4 cost_5225_1133_join0_6 rfl rfl rfl

private theorem cost_5225_1133_join1_4 : P1_7_1_3.blockEstimate 5225 1133 2157 512 = 1623840608619 :=
  @P1_7_1_3.block_append 5225 1133 2157 2413 256 256 512 692291723499 931548885120 1623840608619 cost_5225_1133_join0_8 cost_5225_1133_join0_10 rfl rfl rfl

private theorem cost_5225_1133_join1_6 : P1_7_1_3.blockEstimate 5225 1133 2669 512 = 2431369011456 :=
  @P1_7_1_3.block_append 5225 1133 2669 2925 256 256 512 1133656207488 1297712803968 2431369011456 cost_5225_1133_join0_12 cost_5225_1133_join0_14 rfl rfl rfl

private theorem cost_5225_1133_join1_8 : P1_7_1_3.blockEstimate 5225 1133 3181 512 = 2935392493824 :=
  @P1_7_1_3.block_append 5225 1133 3181 3437 256 256 512 1423718674560 1511673819264 2935392493824 cost_5225_1133_join0_16 cost_5225_1133_join0_18 rfl rfl rfl

private theorem cost_5225_1133_join1_10 : P1_7_1_3.blockEstimate 5225 1133 3693 512 = 3135010169088 :=
  @P1_7_1_3.block_append 5225 1133 3693 3949 256 256 512 1561578238080 1573431931008 3135010169088 cost_5225_1133_join0_20 cost_5225_1133_join0_22 rfl rfl rfl

private theorem cost_5225_1133_join1_12 : P1_7_1_3.blockEstimate 5225 1133 4205 512 = 3030222037248 :=
  @P1_7_1_3.block_append 5225 1133 4205 4461 256 256 512 1547234898048 1482987139200 3030222037248 cost_5225_1133_join0_24 cost_5225_1133_join0_26 rfl rfl rfl

private theorem cost_5225_1133_join1_14 : P1_7_1_3.blockEstimate 5225 1133 4717 512 = 2621028119046 :=
  @P1_7_1_3.block_append 5225 1133 4717 4973 256 256 512 1380688654464 1240339464582 2621028119046 cost_5225_1133_join0_28 cost_5225_1133_join0_30 rfl rfl rfl

private theorem cost_5225_1133_join1_16 : P1_7_1_3.blockEstimate 5225 1133 5229 512 = 1947867832789 :=
  @P1_7_1_3.block_append 5225 1133 5229 5485 256 256 512 1066722713966 881145118823 1947867832789 cost_5225_1133_join0_32 cost_5225_1133_join0_34 rfl rfl rfl

private theorem cost_5225_1133_join1_18 : P1_7_1_3.blockEstimate 5225 1133 5741 512 = 1215770296705 :=
  @P1_7_1_3.block_append 5225 1133 5741 5997 256 256 512 696071606798 519698689907 1215770296705 cost_5225_1133_join0_36 cost_5225_1133_join0_38 rfl rfl rfl

private theorem cost_5225_1133_join1_20 : P1_7_1_3.blockEstimate 5225 1133 6253 512 = 580170600738 :=
  @P1_7_1_3.block_append 5225 1133 6253 6509 256 256 512 359144481794 221026118944 580170600738 cost_5225_1133_join0_40 cost_5225_1133_join0_42 rfl rfl rfl

private theorem cost_5225_1133_join1_22 : P1_7_1_3.blockEstimate 5225 1133 6765 512 = 152477542976 :=
  @P1_7_1_3.block_append 5225 1133 6765 7021 256 256 512 113030323488 39447219488 152477542976 cost_5225_1133_join0_44 cost_5225_1133_join0_46 rfl rfl rfl

private theorem cost_5225_1133_join2_0 : P1_7_1_3.blockEstimate 5225 1133 1133 1024 = 800084102400 :=
  @P1_7_1_3.block_append 5225 1133 1133 1645 512 512 1024 108943558272 691140544128 800084102400 cost_5225_1133_join1_0 cost_5225_1133_join1_2 rfl rfl rfl

private theorem cost_5225_1133_join2_2 : P1_7_1_3.blockEstimate 5225 1133 2157 1024 = 4055209620075 :=
  @P1_7_1_3.block_append 5225 1133 2157 2669 512 512 1024 1623840608619 2431369011456 4055209620075 cost_5225_1133_join1_4 cost_5225_1133_join1_6 rfl rfl rfl

private theorem cost_5225_1133_join2_4 : P1_7_1_3.blockEstimate 5225 1133 3181 1024 = 6070402662912 :=
  @P1_7_1_3.block_append 5225 1133 3181 3693 512 512 1024 2935392493824 3135010169088 6070402662912 cost_5225_1133_join1_8 cost_5225_1133_join1_10 rfl rfl rfl

private theorem cost_5225_1133_join2_6 : P1_7_1_3.blockEstimate 5225 1133 4205 1024 = 5651250156294 :=
  @P1_7_1_3.block_append 5225 1133 4205 4717 512 512 1024 3030222037248 2621028119046 5651250156294 cost_5225_1133_join1_12 cost_5225_1133_join1_14 rfl rfl rfl

private theorem cost_5225_1133_join2_8 : P1_7_1_3.blockEstimate 5225 1133 5229 1024 = 3163638129494 :=
  @P1_7_1_3.block_append 5225 1133 5229 5741 512 512 1024 1947867832789 1215770296705 3163638129494 cost_5225_1133_join1_16 cost_5225_1133_join1_18 rfl rfl rfl

private theorem cost_5225_1133_join2_10 : P1_7_1_3.blockEstimate 5225 1133 6253 1024 = 732648143714 :=
  @P1_7_1_3.block_append 5225 1133 6253 6765 512 512 1024 580170600738 152477542976 732648143714 cost_5225_1133_join1_20 cost_5225_1133_join1_22 rfl rfl rfl

private theorem cost_5225_1133_join3_0 : P1_7_1_3.blockEstimate 5225 1133 1133 2048 = 4855293722475 :=
  @P1_7_1_3.block_append 5225 1133 1133 2157 1024 1024 2048 800084102400 4055209620075 4855293722475 cost_5225_1133_join2_0 cost_5225_1133_join2_2 rfl rfl rfl

private theorem cost_5225_1133_join3_2 : P1_7_1_3.blockEstimate 5225 1133 3181 2048 = 11721652819206 :=
  @P1_7_1_3.block_append 5225 1133 3181 4205 1024 1024 2048 6070402662912 5651250156294 11721652819206 cost_5225_1133_join2_4 cost_5225_1133_join2_6 rfl rfl rfl

private theorem cost_5225_1133_join3_4 : P1_7_1_3.blockEstimate 5225 1133 5229 2048 = 3896286273208 :=
  @P1_7_1_3.block_append 5225 1133 5229 6253 1024 1024 2048 3163638129494 732648143714 3896286273208 cost_5225_1133_join2_8 cost_5225_1133_join2_10 rfl rfl rfl

private theorem cost_5225_1133_join4_0 : P1_7_1_3.blockEstimate 5225 1133 1133 4096 = 16576946541681 :=
  @P1_7_1_3.block_append 5225 1133 1133 3181 2048 2048 4096 4855293722475 11721652819206 16576946541681 cost_5225_1133_join3_0 cost_5225_1133_join3_2 rfl rfl rfl

private theorem cost_5225_1133_join4_2 : P1_7_1_3.blockEstimate 5225 1133 5229 2262 = 3900560605057 :=
  @P1_7_1_3.block_append 5225 1133 5229 7277 2048 214 2262 3896286273208 4274331849 3900560605057 cost_5225_1133_join3_4 cost_5225_1133_join0_48 rfl rfl rfl

private theorem cost_5225_1133_join5_0 : P1_7_1_3.blockEstimate 5225 1133 1133 6358 = 20477507146738 :=
  @P1_7_1_3.block_append 5225 1133 1133 5229 4096 2262 6358 16576946541681 3900560605057 20477507146738 cost_5225_1133_join4_0 cost_5225_1133_join4_2 rfl rfl rfl

private theorem cost_5225_1133_total : P1_7_1_3.momentEstimate 5225 1133 = 20477507146738 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 5225 + 1133 = 6358 by decide]
  exact cost_5225_1133_join5_0

theorem moment5225_1133 : P1_7_1.groupedPoleMoment 5225 1133 ≤ 20477507146738 :=
  (P1_7_1_3.grouped_bound 5225 1133).trans_eq cost_5225_1133_total
private theorem cost_5226_1111_block0 : P1_7_1_3.blockEstimate 5226 1111 1111 128 = 1835577120 := by decide +kernel

private theorem cost_5226_1111_block1 : P1_7_1_3.blockEstimate 5226 1111 1239 128 = 12408012576 := by decide +kernel

private theorem cost_5226_1111_block2 : P1_7_1_3.blockEstimate 5226 1111 1367 128 = 32729059104 := by decide +kernel

private theorem cost_5226_1111_block3 : P1_7_1_3.blockEstimate 5226 1111 1495 128 = 61993410336 := by decide +kernel

private theorem cost_5226_1111_block4 : P1_7_1_3.blockEstimate 5226 1111 1623 128 = 99395759904 := by decide +kernel

private theorem cost_5226_1111_block5 : P1_7_1_3.blockEstimate 5226 1111 1751 128 = 144130801440 := by decide +kernel

private theorem cost_5226_1111_block6 : P1_7_1_3.blockEstimate 5226 1111 1879 128 = 195393228576 := by decide +kernel

private theorem cost_5226_1111_block7 : P1_7_1_3.blockEstimate 5226 1111 2007 128 = 252377734944 := by decide +kernel

private theorem cost_5226_1111_block8 : P1_7_1_3.blockEstimate 5226 1111 2135 128 = 314232121246 := by decide +kernel

private theorem cost_5226_1111_block9 : P1_7_1_3.blockEstimate 5226 1111 2263 128 = 377129942784 := by decide +kernel

private theorem cost_5226_1111_block10 : P1_7_1_3.blockEstimate 5226 1111 2391 128 = 435822477056 := by decide +kernel

private theorem cost_5226_1111_block11 : P1_7_1_3.blockEstimate 5226 1111 2519 128 = 489850945280 := by decide +kernel

private theorem cost_5226_1111_block12 : P1_7_1_3.blockEstimate 5226 1111 2647 128 = 539215347456 := by decide +kernel

private theorem cost_5226_1111_block13 : P1_7_1_3.blockEstimate 5226 1111 2775 128 = 583915683584 := by decide +kernel

private theorem cost_5226_1111_block14 : P1_7_1_3.blockEstimate 5226 1111 2903 128 = 623951953664 := by decide +kernel

private theorem cost_5226_1111_block15 : P1_7_1_3.blockEstimate 5226 1111 3031 128 = 659324157696 := by decide +kernel

private theorem cost_5226_1111_block16 : P1_7_1_3.blockEstimate 5226 1111 3159 128 = 690032295680 := by decide +kernel

private theorem cost_5226_1111_block17 : P1_7_1_3.blockEstimate 5226 1111 3287 128 = 716076367616 := by decide +kernel

private theorem cost_5226_1111_block18 : P1_7_1_3.blockEstimate 5226 1111 3415 128 = 737456373504 := by decide +kernel

private theorem cost_5226_1111_block19 : P1_7_1_3.blockEstimate 5226 1111 3543 128 = 754172313344 := by decide +kernel

private theorem cost_5226_1111_block20 : P1_7_1_3.blockEstimate 5226 1111 3671 128 = 766224187136 := by decide +kernel

private theorem cost_5226_1111_block21 : P1_7_1_3.blockEstimate 5226 1111 3799 128 = 773611994880 := by decide +kernel

private theorem cost_5226_1111_block22 : P1_7_1_3.blockEstimate 5226 1111 3927 128 = 776335736576 := by decide +kernel

private theorem cost_5226_1111_block23 : P1_7_1_3.blockEstimate 5226 1111 4055 128 = 774395412224 := by decide +kernel

private theorem cost_5226_1111_block24 : P1_7_1_3.blockEstimate 5226 1111 4183 128 = 767791021824 := by decide +kernel

private theorem cost_5226_1111_block25 : P1_7_1_3.blockEstimate 5226 1111 4311 128 = 756522565376 := by decide +kernel

private theorem cost_5226_1111_block26 : P1_7_1_3.blockEstimate 5226 1111 4439 128 = 740590042880 := by decide +kernel

private theorem cost_5226_1111_block27 : P1_7_1_3.blockEstimate 5226 1111 4567 128 = 719993454336 := by decide +kernel

private theorem cost_5226_1111_block28 : P1_7_1_3.blockEstimate 5226 1111 4695 128 = 694732799744 := by decide +kernel

private theorem cost_5226_1111_block29 : P1_7_1_3.blockEstimate 5226 1111 4823 128 = 664808079104 := by decide +kernel

private theorem cost_5226_1111_block30 : P1_7_1_3.blockEstimate 5226 1111 4951 128 = 630219292416 := by decide +kernel

private theorem cost_5226_1111_block31 : P1_7_1_3.blockEstimate 5226 1111 5079 128 = 590966439680 := by decide +kernel

private theorem cost_5226_1111_block32 : P1_7_1_3.blockEstimate 5226 1111 5207 128 = 547391467651 := by decide +kernel

private theorem cost_5226_1111_block33 : P1_7_1_3.blockEstimate 5226 1111 5335 128 = 501773518907 := by decide +kernel

private theorem cost_5226_1111_block34 : P1_7_1_3.blockEstimate 5226 1111 5463 128 = 455433829070 := by decide +kernel

private theorem cost_5226_1111_block35 : P1_7_1_3.blockEstimate 5226 1111 5591 128 = 408934941756 := by decide +kernel

private theorem cost_5226_1111_block36 : P1_7_1_3.blockEstimate 5226 1111 5719 128 = 362814663764 := by decide +kernel

private theorem cost_5226_1111_block37 : P1_7_1_3.blockEstimate 5226 1111 5847 128 = 317587626558 := by decide +kernel

private theorem cost_5226_1111_block38 : P1_7_1_3.blockEstimate 5226 1111 5975 128 = 273745288332 := by decide +kernel

private theorem cost_5226_1111_block39 : P1_7_1_3.blockEstimate 5226 1111 6103 128 = 231755932357 := by decide +kernel

private theorem cost_5226_1111_block40 : P1_7_1_3.blockEstimate 5226 1111 6231 128 = 192055247354 := by decide +kernel

private theorem cost_5226_1111_block41 : P1_7_1_3.blockEstimate 5226 1111 6359 128 = 154770792496 := by decide +kernel

private theorem cost_5226_1111_block42 : P1_7_1_3.blockEstimate 5226 1111 6487 128 = 120689757232 := by decide +kernel

private theorem cost_5226_1111_block43 : P1_7_1_3.blockEstimate 5226 1111 6615 128 = 90323499056 := by decide +kernel

private theorem cost_5226_1111_block44 : P1_7_1_3.blockEstimate 5226 1111 6743 128 = 63923676208 := by decide +kernel

private theorem cost_5226_1111_block45 : P1_7_1_3.blockEstimate 5226 1111 6871 128 = 41741946928 := by decide +kernel

private theorem cost_5226_1111_block46 : P1_7_1_3.blockEstimate 5226 1111 6999 128 = 24029969456 := by decide +kernel

private theorem cost_5226_1111_block47 : P1_7_1_3.blockEstimate 5226 1111 7127 128 = 11039402032 := by decide +kernel

private theorem cost_5226_1111_block48 : P1_7_1_3.blockEstimate 5226 1111 7255 128 = 3021902896 := by decide +kernel

private theorem cost_5226_1111_block49 : P1_7_1_3.blockEstimate 5226 1111 7383 65 = 127291138 := by decide +kernel

private theorem cost_5226_1111_join0_0 : P1_7_1_3.blockEstimate 5226 1111 1111 256 = 14243589696 :=
  @P1_7_1_3.block_append 5226 1111 1111 1239 128 128 256 1835577120 12408012576 14243589696 cost_5226_1111_block0 cost_5226_1111_block1 rfl rfl rfl

private theorem cost_5226_1111_join0_2 : P1_7_1_3.blockEstimate 5226 1111 1367 256 = 94722469440 :=
  @P1_7_1_3.block_append 5226 1111 1367 1495 128 128 256 32729059104 61993410336 94722469440 cost_5226_1111_block2 cost_5226_1111_block3 rfl rfl rfl

private theorem cost_5226_1111_join0_4 : P1_7_1_3.blockEstimate 5226 1111 1623 256 = 243526561344 :=
  @P1_7_1_3.block_append 5226 1111 1623 1751 128 128 256 99395759904 144130801440 243526561344 cost_5226_1111_block4 cost_5226_1111_block5 rfl rfl rfl

private theorem cost_5226_1111_join0_6 : P1_7_1_3.blockEstimate 5226 1111 1879 256 = 447770963520 :=
  @P1_7_1_3.block_append 5226 1111 1879 2007 128 128 256 195393228576 252377734944 447770963520 cost_5226_1111_block6 cost_5226_1111_block7 rfl rfl rfl

private theorem cost_5226_1111_join0_8 : P1_7_1_3.blockEstimate 5226 1111 2135 256 = 691362064030 :=
  @P1_7_1_3.block_append 5226 1111 2135 2263 128 128 256 314232121246 377129942784 691362064030 cost_5226_1111_block8 cost_5226_1111_block9 rfl rfl rfl

private theorem cost_5226_1111_join0_10 : P1_7_1_3.blockEstimate 5226 1111 2391 256 = 925673422336 :=
  @P1_7_1_3.block_append 5226 1111 2391 2519 128 128 256 435822477056 489850945280 925673422336 cost_5226_1111_block10 cost_5226_1111_block11 rfl rfl rfl

private theorem cost_5226_1111_join0_12 : P1_7_1_3.blockEstimate 5226 1111 2647 256 = 1123131031040 :=
  @P1_7_1_3.block_append 5226 1111 2647 2775 128 128 256 539215347456 583915683584 1123131031040 cost_5226_1111_block12 cost_5226_1111_block13 rfl rfl rfl

private theorem cost_5226_1111_join0_14 : P1_7_1_3.blockEstimate 5226 1111 2903 256 = 1283276111360 :=
  @P1_7_1_3.block_append 5226 1111 2903 3031 128 128 256 623951953664 659324157696 1283276111360 cost_5226_1111_block14 cost_5226_1111_block15 rfl rfl rfl

private theorem cost_5226_1111_join0_16 : P1_7_1_3.blockEstimate 5226 1111 3159 256 = 1406108663296 :=
  @P1_7_1_3.block_append 5226 1111 3159 3287 128 128 256 690032295680 716076367616 1406108663296 cost_5226_1111_block16 cost_5226_1111_block17 rfl rfl rfl

private theorem cost_5226_1111_join0_18 : P1_7_1_3.blockEstimate 5226 1111 3415 256 = 1491628686848 :=
  @P1_7_1_3.block_append 5226 1111 3415 3543 128 128 256 737456373504 754172313344 1491628686848 cost_5226_1111_block18 cost_5226_1111_block19 rfl rfl rfl

private theorem cost_5226_1111_join0_20 : P1_7_1_3.blockEstimate 5226 1111 3671 256 = 1539836182016 :=
  @P1_7_1_3.block_append 5226 1111 3671 3799 128 128 256 766224187136 773611994880 1539836182016 cost_5226_1111_block20 cost_5226_1111_block21 rfl rfl rfl

private theorem cost_5226_1111_join0_22 : P1_7_1_3.blockEstimate 5226 1111 3927 256 = 1550731148800 :=
  @P1_7_1_3.block_append 5226 1111 3927 4055 128 128 256 776335736576 774395412224 1550731148800 cost_5226_1111_block22 cost_5226_1111_block23 rfl rfl rfl

private theorem cost_5226_1111_join0_24 : P1_7_1_3.blockEstimate 5226 1111 4183 256 = 1524313587200 :=
  @P1_7_1_3.block_append 5226 1111 4183 4311 128 128 256 767791021824 756522565376 1524313587200 cost_5226_1111_block24 cost_5226_1111_block25 rfl rfl rfl

private theorem cost_5226_1111_join0_26 : P1_7_1_3.blockEstimate 5226 1111 4439 256 = 1460583497216 :=
  @P1_7_1_3.block_append 5226 1111 4439 4567 128 128 256 740590042880 719993454336 1460583497216 cost_5226_1111_block26 cost_5226_1111_block27 rfl rfl rfl

private theorem cost_5226_1111_join0_28 : P1_7_1_3.blockEstimate 5226 1111 4695 256 = 1359540878848 :=
  @P1_7_1_3.block_append 5226 1111 4695 4823 128 128 256 694732799744 664808079104 1359540878848 cost_5226_1111_block28 cost_5226_1111_block29 rfl rfl rfl

private theorem cost_5226_1111_join0_30 : P1_7_1_3.blockEstimate 5226 1111 4951 256 = 1221185732096 :=
  @P1_7_1_3.block_append 5226 1111 4951 5079 128 128 256 630219292416 590966439680 1221185732096 cost_5226_1111_block30 cost_5226_1111_block31 rfl rfl rfl

private theorem cost_5226_1111_join0_32 : P1_7_1_3.blockEstimate 5226 1111 5207 256 = 1049164986558 :=
  @P1_7_1_3.block_append 5226 1111 5207 5335 128 128 256 547391467651 501773518907 1049164986558 cost_5226_1111_block32 cost_5226_1111_block33 rfl rfl rfl

private theorem cost_5226_1111_join0_34 : P1_7_1_3.blockEstimate 5226 1111 5463 256 = 864368770826 :=
  @P1_7_1_3.block_append 5226 1111 5463 5591 128 128 256 455433829070 408934941756 864368770826 cost_5226_1111_block34 cost_5226_1111_block35 rfl rfl rfl

private theorem cost_5226_1111_join0_36 : P1_7_1_3.blockEstimate 5226 1111 5719 256 = 680402290322 :=
  @P1_7_1_3.block_append 5226 1111 5719 5847 128 128 256 362814663764 317587626558 680402290322 cost_5226_1111_block36 cost_5226_1111_block37 rfl rfl rfl

private theorem cost_5226_1111_join0_38 : P1_7_1_3.blockEstimate 5226 1111 5975 256 = 505501220689 :=
  @P1_7_1_3.block_append 5226 1111 5975 6103 128 128 256 273745288332 231755932357 505501220689 cost_5226_1111_block38 cost_5226_1111_block39 rfl rfl rfl

private theorem cost_5226_1111_join0_40 : P1_7_1_3.blockEstimate 5226 1111 6231 256 = 346826039850 :=
  @P1_7_1_3.block_append 5226 1111 6231 6359 128 128 256 192055247354 154770792496 346826039850 cost_5226_1111_block40 cost_5226_1111_block41 rfl rfl rfl

private theorem cost_5226_1111_join0_42 : P1_7_1_3.blockEstimate 5226 1111 6487 256 = 211013256288 :=
  @P1_7_1_3.block_append 5226 1111 6487 6615 128 128 256 120689757232 90323499056 211013256288 cost_5226_1111_block42 cost_5226_1111_block43 rfl rfl rfl

private theorem cost_5226_1111_join0_44 : P1_7_1_3.blockEstimate 5226 1111 6743 256 = 105665623136 :=
  @P1_7_1_3.block_append 5226 1111 6743 6871 128 128 256 63923676208 41741946928 105665623136 cost_5226_1111_block44 cost_5226_1111_block45 rfl rfl rfl

private theorem cost_5226_1111_join0_46 : P1_7_1_3.blockEstimate 5226 1111 6999 256 = 35069371488 :=
  @P1_7_1_3.block_append 5226 1111 6999 7127 128 128 256 24029969456 11039402032 35069371488 cost_5226_1111_block46 cost_5226_1111_block47 rfl rfl rfl

private theorem cost_5226_1111_join0_48 : P1_7_1_3.blockEstimate 5226 1111 7255 193 = 3149194034 :=
  @P1_7_1_3.block_append 5226 1111 7255 7383 128 65 193 3021902896 127291138 3149194034 cost_5226_1111_block48 cost_5226_1111_block49 rfl rfl rfl

private theorem cost_5226_1111_join1_0 : P1_7_1_3.blockEstimate 5226 1111 1111 512 = 108966059136 :=
  @P1_7_1_3.block_append 5226 1111 1111 1367 256 256 512 14243589696 94722469440 108966059136 cost_5226_1111_join0_0 cost_5226_1111_join0_2 rfl rfl rfl

private theorem cost_5226_1111_join1_2 : P1_7_1_3.blockEstimate 5226 1111 1623 512 = 691297524864 :=
  @P1_7_1_3.block_append 5226 1111 1623 1879 256 256 512 243526561344 447770963520 691297524864 cost_5226_1111_join0_4 cost_5226_1111_join0_6 rfl rfl rfl

private theorem cost_5226_1111_join1_4 : P1_7_1_3.blockEstimate 5226 1111 2135 512 = 1617035486366 :=
  @P1_7_1_3.block_append 5226 1111 2135 2391 256 256 512 691362064030 925673422336 1617035486366 cost_5226_1111_join0_8 cost_5226_1111_join0_10 rfl rfl rfl

private theorem cost_5226_1111_join1_6 : P1_7_1_3.blockEstimate 5226 1111 2647 512 = 2406407142400 :=
  @P1_7_1_3.block_append 5226 1111 2647 2903 256 256 512 1123131031040 1283276111360 2406407142400 cost_5226_1111_join0_12 cost_5226_1111_join0_14 rfl rfl rfl

private theorem cost_5226_1111_join1_8 : P1_7_1_3.blockEstimate 5226 1111 3159 512 = 2897737350144 :=
  @P1_7_1_3.block_append 5226 1111 3159 3415 256 256 512 1406108663296 1491628686848 2897737350144 cost_5226_1111_join0_16 cost_5226_1111_join0_18 rfl rfl rfl

private theorem cost_5226_1111_join1_10 : P1_7_1_3.blockEstimate 5226 1111 3671 512 = 3090567330816 :=
  @P1_7_1_3.block_append 5226 1111 3671 3927 256 256 512 1539836182016 1550731148800 3090567330816 cost_5226_1111_join0_20 cost_5226_1111_join0_22 rfl rfl rfl

private theorem cost_5226_1111_join1_12 : P1_7_1_3.blockEstimate 5226 1111 4183 512 = 2984897084416 :=
  @P1_7_1_3.block_append 5226 1111 4183 4439 256 256 512 1524313587200 1460583497216 2984897084416 cost_5226_1111_join0_24 cost_5226_1111_join0_26 rfl rfl rfl

private theorem cost_5226_1111_join1_14 : P1_7_1_3.blockEstimate 5226 1111 4695 512 = 2580726610944 :=
  @P1_7_1_3.block_append 5226 1111 4695 4951 256 256 512 1359540878848 1221185732096 2580726610944 cost_5226_1111_join0_28 cost_5226_1111_join0_30 rfl rfl rfl

private theorem cost_5226_1111_join1_16 : P1_7_1_3.blockEstimate 5226 1111 5207 512 = 1913533757384 :=
  @P1_7_1_3.block_append 5226 1111 5207 5463 256 256 512 1049164986558 864368770826 1913533757384 cost_5226_1111_join0_32 cost_5226_1111_join0_34 rfl rfl rfl

private theorem cost_5226_1111_join1_18 : P1_7_1_3.blockEstimate 5226 1111 5719 512 = 1185903511011 :=
  @P1_7_1_3.block_append 5226 1111 5719 5975 256 256 512 680402290322 505501220689 1185903511011 cost_5226_1111_join0_36 cost_5226_1111_join0_38 rfl rfl rfl

private theorem cost_5226_1111_join1_20 : P1_7_1_3.blockEstimate 5226 1111 6231 512 = 557839296138 :=
  @P1_7_1_3.block_append 5226 1111 6231 6487 256 256 512 346826039850 211013256288 557839296138 cost_5226_1111_join0_40 cost_5226_1111_join0_42 rfl rfl rfl

private theorem cost_5226_1111_join1_22 : P1_7_1_3.blockEstimate 5226 1111 6743 512 = 140734994624 :=
  @P1_7_1_3.block_append 5226 1111 6743 6999 256 256 512 105665623136 35069371488 140734994624 cost_5226_1111_join0_44 cost_5226_1111_join0_46 rfl rfl rfl

private theorem cost_5226_1111_join2_0 : P1_7_1_3.blockEstimate 5226 1111 1111 1024 = 800263584000 :=
  @P1_7_1_3.block_append 5226 1111 1111 1623 512 512 1024 108966059136 691297524864 800263584000 cost_5226_1111_join1_0 cost_5226_1111_join1_2 rfl rfl rfl

private theorem cost_5226_1111_join2_2 : P1_7_1_3.blockEstimate 5226 1111 2135 1024 = 4023442628766 :=
  @P1_7_1_3.block_append 5226 1111 2135 2647 512 512 1024 1617035486366 2406407142400 4023442628766 cost_5226_1111_join1_4 cost_5226_1111_join1_6 rfl rfl rfl

private theorem cost_5226_1111_join2_4 : P1_7_1_3.blockEstimate 5226 1111 3159 1024 = 5988304680960 :=
  @P1_7_1_3.block_append 5226 1111 3159 3671 512 512 1024 2897737350144 3090567330816 5988304680960 cost_5226_1111_join1_8 cost_5226_1111_join1_10 rfl rfl rfl

private theorem cost_5226_1111_join2_6 : P1_7_1_3.blockEstimate 5226 1111 4183 1024 = 5565623695360 :=
  @P1_7_1_3.block_append 5226 1111 4183 4695 512 512 1024 2984897084416 2580726610944 5565623695360 cost_5226_1111_join1_12 cost_5226_1111_join1_14 rfl rfl rfl

private theorem cost_5226_1111_join2_8 : P1_7_1_3.blockEstimate 5226 1111 5207 1024 = 3099437268395 :=
  @P1_7_1_3.block_append 5226 1111 5207 5719 512 512 1024 1913533757384 1185903511011 3099437268395 cost_5226_1111_join1_16 cost_5226_1111_join1_18 rfl rfl rfl

private theorem cost_5226_1111_join2_10 : P1_7_1_3.blockEstimate 5226 1111 6231 1024 = 698574290762 :=
  @P1_7_1_3.block_append 5226 1111 6231 6743 512 512 1024 557839296138 140734994624 698574290762 cost_5226_1111_join1_20 cost_5226_1111_join1_22 rfl rfl rfl

private theorem cost_5226_1111_join3_0 : P1_7_1_3.blockEstimate 5226 1111 1111 2048 = 4823706212766 :=
  @P1_7_1_3.block_append 5226 1111 1111 2135 1024 1024 2048 800263584000 4023442628766 4823706212766 cost_5226_1111_join2_0 cost_5226_1111_join2_2 rfl rfl rfl

private theorem cost_5226_1111_join3_2 : P1_7_1_3.blockEstimate 5226 1111 3159 2048 = 11553928376320 :=
  @P1_7_1_3.block_append 5226 1111 3159 4183 1024 1024 2048 5988304680960 5565623695360 11553928376320 cost_5226_1111_join2_4 cost_5226_1111_join2_6 rfl rfl rfl

private theorem cost_5226_1111_join3_4 : P1_7_1_3.blockEstimate 5226 1111 5207 2048 = 3798011559157 :=
  @P1_7_1_3.block_append 5226 1111 5207 6231 1024 1024 2048 3099437268395 698574290762 3798011559157 cost_5226_1111_join2_8 cost_5226_1111_join2_10 rfl rfl rfl

private theorem cost_5226_1111_join4_0 : P1_7_1_3.blockEstimate 5226 1111 1111 4096 = 16377634589086 :=
  @P1_7_1_3.block_append 5226 1111 1111 3159 2048 2048 4096 4823706212766 11553928376320 16377634589086 cost_5226_1111_join3_0 cost_5226_1111_join3_2 rfl rfl rfl

private theorem cost_5226_1111_join4_2 : P1_7_1_3.blockEstimate 5226 1111 5207 2241 = 3801160753191 :=
  @P1_7_1_3.block_append 5226 1111 5207 7255 2048 193 2241 3798011559157 3149194034 3801160753191 cost_5226_1111_join3_4 cost_5226_1111_join0_48 rfl rfl rfl

private theorem cost_5226_1111_join5_0 : P1_7_1_3.blockEstimate 5226 1111 1111 6337 = 20178795342277 :=
  @P1_7_1_3.block_append 5226 1111 1111 5207 4096 2241 6337 16377634589086 3801160753191 20178795342277 cost_5226_1111_join4_0 cost_5226_1111_join4_2 rfl rfl rfl

private theorem cost_5226_1111_total : P1_7_1_3.momentEstimate 5226 1111 = 20178795342277 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 5226 + 1111 = 6337 by decide]
  exact cost_5226_1111_join5_0

theorem moment5226_1111 : P1_7_1.groupedPoleMoment 5226 1111 ≤ 20178795342277 :=
  (P1_7_1_3.grouped_bound 5226 1111).trans_eq cost_5226_1111_total
private theorem cost_5226_1133_block0 : P1_7_1_3.blockEstimate 5226 1133 1133 128 = 1835577120 := by decide +kernel

private theorem cost_5226_1133_block1 : P1_7_1_3.blockEstimate 5226 1133 1261 128 = 12408012576 := by decide +kernel

private theorem cost_5226_1133_block2 : P1_7_1_3.blockEstimate 5226 1133 1389 128 = 32729059104 := by decide +kernel

private theorem cost_5226_1133_block3 : P1_7_1_3.blockEstimate 5226 1133 1517 128 = 61993410336 := by decide +kernel

private theorem cost_5226_1133_block4 : P1_7_1_3.blockEstimate 5226 1133 1645 128 = 99395759904 := by decide +kernel

private theorem cost_5226_1133_block5 : P1_7_1_3.blockEstimate 5226 1133 1773 128 = 144130801440 := by decide +kernel

private theorem cost_5226_1133_block6 : P1_7_1_3.blockEstimate 5226 1133 1901 128 = 195393228576 := by decide +kernel

private theorem cost_5226_1133_block7 : P1_7_1_3.blockEstimate 5226 1133 2029 128 = 252377734944 := by decide +kernel

private theorem cost_5226_1133_block8 : P1_7_1_3.blockEstimate 5226 1133 2157 128 = 314274363831 := by decide +kernel

private theorem cost_5226_1133_block9 : P1_7_1_3.blockEstimate 5226 1133 2285 128 = 378187693632 := by decide +kernel

private theorem cost_5226_1133_block10 : P1_7_1_3.blockEstimate 5226 1133 2413 128 = 438245785152 := by decide +kernel

private theorem cost_5226_1133_block11 : P1_7_1_3.blockEstimate 5226 1133 2541 128 = 493547535936 := by decide +kernel

private theorem cost_5226_1133_block12 : P1_7_1_3.blockEstimate 5226 1133 2669 128 = 544092945984 := by decide +kernel

private theorem cost_5226_1133_block13 : P1_7_1_3.blockEstimate 5226 1133 2797 128 = 589882015296 := by decide +kernel

private theorem cost_5226_1133_block14 : P1_7_1_3.blockEstimate 5226 1133 2925 128 = 630914743872 := by decide +kernel

private theorem cost_5226_1133_block15 : P1_7_1_3.blockEstimate 5226 1133 3053 128 = 667191131712 := by decide +kernel

private theorem cost_5226_1133_block16 : P1_7_1_3.blockEstimate 5226 1133 3181 128 = 698711178816 := by decide +kernel

private theorem cost_5226_1133_block17 : P1_7_1_3.blockEstimate 5226 1133 3309 128 = 725474885184 := by decide +kernel

private theorem cost_5226_1133_block18 : P1_7_1_3.blockEstimate 5226 1133 3437 128 = 747482250816 := by decide +kernel

private theorem cost_5226_1133_block19 : P1_7_1_3.blockEstimate 5226 1133 3565 128 = 764733275712 := by decide +kernel

private theorem cost_5226_1133_block20 : P1_7_1_3.blockEstimate 5226 1133 3693 128 = 777227959872 := by decide +kernel

private theorem cost_5226_1133_block21 : P1_7_1_3.blockEstimate 5226 1133 3821 128 = 784966303296 := by decide +kernel

private theorem cost_5226_1133_block22 : P1_7_1_3.blockEstimate 5226 1133 3949 128 = 787948305984 := by decide +kernel

private theorem cost_5226_1133_block23 : P1_7_1_3.blockEstimate 5226 1133 4077 128 = 786173967936 := by decide +kernel

private theorem cost_5226_1133_block24 : P1_7_1_3.blockEstimate 5226 1133 4205 128 = 779643289152 := by decide +kernel

private theorem cost_5226_1133_block25 : P1_7_1_3.blockEstimate 5226 1133 4333 128 = 768356269632 := by decide +kernel

private theorem cost_5226_1133_block26 : P1_7_1_3.blockEstimate 5226 1133 4461 128 = 752312909376 := by decide +kernel

private theorem cost_5226_1133_block27 : P1_7_1_3.blockEstimate 5226 1133 4589 128 = 731513208384 := by decide +kernel

private theorem cost_5226_1133_block28 : P1_7_1_3.blockEstimate 5226 1133 4717 128 = 705957166656 := by decide +kernel

private theorem cost_5226_1133_block29 : P1_7_1_3.blockEstimate 5226 1133 4845 128 = 675644784192 := by decide +kernel

private theorem cost_5226_1133_block30 : P1_7_1_3.blockEstimate 5226 1133 4973 128 = 640576060992 := by decide +kernel

private theorem cost_5226_1133_block31 : P1_7_1_3.blockEstimate 5226 1133 5101 128 = 600751005945 := by decide +kernel

private theorem cost_5226_1133_block32 : P1_7_1_3.blockEstimate 5226 1133 5229 128 = 556758137643 := by decide +kernel

private theorem cost_5226_1133_block33 : P1_7_1_3.blockEstimate 5226 1133 5357 128 = 510971512733 := by decide +kernel

private theorem cost_5226_1133_block34 : P1_7_1_3.blockEstimate 5226 1133 5485 128 = 464424947017 := by decide +kernel

private theorem cost_5226_1133_block35 : P1_7_1_3.blockEstimate 5226 1133 5613 128 = 417676348410 := by decide +kernel

private theorem cost_5226_1133_block36 : P1_7_1_3.blockEstimate 5226 1133 5741 128 = 371260901851 := by decide +kernel

private theorem cost_5226_1133_block37 : P1_7_1_3.blockEstimate 5226 1133 5869 128 = 325691066805 := by decide +kernel

private theorem cost_5226_1133_block38 : P1_7_1_3.blockEstimate 5226 1133 5997 128 = 281456577537 := by decide +kernel

private theorem cost_5226_1133_block39 : P1_7_1_3.blockEstimate 5226 1133 6125 128 = 239024445122 := by decide +kernel

private theorem cost_5226_1133_block40 : P1_7_1_3.blockEstimate 5226 1133 6253 128 = 198829150481 := by decide +kernel

private theorem cost_5226_1133_block41 : P1_7_1_3.blockEstimate 5226 1133 6381 128 = 160984230240 := by decide +kernel

private theorem cost_5226_1133_block42 : P1_7_1_3.blockEstimate 5226 1133 6509 128 = 126290061664 := by decide +kernel

private theorem cost_5226_1133_block43 : P1_7_1_3.blockEstimate 5226 1133 6637 128 = 95267416416 := by decide +kernel

private theorem cost_5226_1133_block44 : P1_7_1_3.blockEstimate 5226 1133 6765 128 = 68167952736 := by decide +kernel

private theorem cost_5226_1133_block45 : P1_7_1_3.blockEstimate 5226 1133 6893 128 = 45243328864 := by decide +kernel

private theorem cost_5226_1133_block46 : P1_7_1_3.blockEstimate 5226 1133 7021 128 = 26745203040 := by decide +kernel

private theorem cost_5226_1133_block47 : P1_7_1_3.blockEstimate 5226 1133 7149 128 = 12925233504 := by decide +kernel

private theorem cost_5226_1133_block48 : P1_7_1_3.blockEstimate 5226 1133 7277 128 = 4035078496 := by decide +kernel

private theorem cost_5226_1133_block49 : P1_7_1_3.blockEstimate 5226 1133 7405 87 = 299484746 := by decide +kernel

private theorem cost_5226_1133_join0_0 : P1_7_1_3.blockEstimate 5226 1133 1133 256 = 14243589696 :=
  @P1_7_1_3.block_append 5226 1133 1133 1261 128 128 256 1835577120 12408012576 14243589696 cost_5226_1133_block0 cost_5226_1133_block1 rfl rfl rfl

private theorem cost_5226_1133_join0_2 : P1_7_1_3.blockEstimate 5226 1133 1389 256 = 94722469440 :=
  @P1_7_1_3.block_append 5226 1133 1389 1517 128 128 256 32729059104 61993410336 94722469440 cost_5226_1133_block2 cost_5226_1133_block3 rfl rfl rfl

private theorem cost_5226_1133_join0_4 : P1_7_1_3.blockEstimate 5226 1133 1645 256 = 243526561344 :=
  @P1_7_1_3.block_append 5226 1133 1645 1773 128 128 256 99395759904 144130801440 243526561344 cost_5226_1133_block4 cost_5226_1133_block5 rfl rfl rfl

private theorem cost_5226_1133_join0_6 : P1_7_1_3.blockEstimate 5226 1133 1901 256 = 447770963520 :=
  @P1_7_1_3.block_append 5226 1133 1901 2029 128 128 256 195393228576 252377734944 447770963520 cost_5226_1133_block6 cost_5226_1133_block7 rfl rfl rfl

private theorem cost_5226_1133_join0_8 : P1_7_1_3.blockEstimate 5226 1133 2157 256 = 692462057463 :=
  @P1_7_1_3.block_append 5226 1133 2157 2285 128 128 256 314274363831 378187693632 692462057463 cost_5226_1133_block8 cost_5226_1133_block9 rfl rfl rfl

private theorem cost_5226_1133_join0_10 : P1_7_1_3.blockEstimate 5226 1133 2413 256 = 931793321088 :=
  @P1_7_1_3.block_append 5226 1133 2413 2541 128 128 256 438245785152 493547535936 931793321088 cost_5226_1133_block10 cost_5226_1133_block11 rfl rfl rfl

private theorem cost_5226_1133_join0_12 : P1_7_1_3.blockEstimate 5226 1133 2669 256 = 1133974961280 :=
  @P1_7_1_3.block_append 5226 1133 2669 2797 128 128 256 544092945984 589882015296 1133974961280 cost_5226_1133_block12 cost_5226_1133_block13 rfl rfl rfl

private theorem cost_5226_1133_join0_14 : P1_7_1_3.blockEstimate 5226 1133 2925 256 = 1298105875584 :=
  @P1_7_1_3.block_append 5226 1133 2925 3053 128 128 256 630914743872 667191131712 1298105875584 cost_5226_1133_block14 cost_5226_1133_block15 rfl rfl rfl

private theorem cost_5226_1133_join0_16 : P1_7_1_3.blockEstimate 5226 1133 3181 256 = 1424186064000 :=
  @P1_7_1_3.block_append 5226 1133 3181 3309 128 128 256 698711178816 725474885184 1424186064000 cost_5226_1133_block16 cost_5226_1133_block17 rfl rfl rfl

private theorem cost_5226_1133_join0_18 : P1_7_1_3.blockEstimate 5226 1133 3437 256 = 1512215526528 :=
  @P1_7_1_3.block_append 5226 1133 3437 3565 128 128 256 747482250816 764733275712 1512215526528 cost_5226_1133_block18 cost_5226_1133_block19 rfl rfl rfl

private theorem cost_5226_1133_join0_20 : P1_7_1_3.blockEstimate 5226 1133 3693 256 = 1562194263168 :=
  @P1_7_1_3.block_append 5226 1133 3693 3821 128 128 256 777227959872 784966303296 1562194263168 cost_5226_1133_block20 cost_5226_1133_block21 rfl rfl rfl

private theorem cost_5226_1133_join0_22 : P1_7_1_3.blockEstimate 5226 1133 3949 256 = 1574122273920 :=
  @P1_7_1_3.block_append 5226 1133 3949 4077 128 128 256 787948305984 786173967936 1574122273920 cost_5226_1133_block22 cost_5226_1133_block23 rfl rfl rfl

private theorem cost_5226_1133_join0_24 : P1_7_1_3.blockEstimate 5226 1133 4205 256 = 1547999558784 :=
  @P1_7_1_3.block_append 5226 1133 4205 4333 128 128 256 779643289152 768356269632 1547999558784 cost_5226_1133_block24 cost_5226_1133_block25 rfl rfl rfl

private theorem cost_5226_1133_join0_26 : P1_7_1_3.blockEstimate 5226 1133 4461 256 = 1483826117760 :=
  @P1_7_1_3.block_append 5226 1133 4461 4589 128 128 256 752312909376 731513208384 1483826117760 cost_5226_1133_block26 cost_5226_1133_block27 rfl rfl rfl

private theorem cost_5226_1133_join0_28 : P1_7_1_3.blockEstimate 5226 1133 4717 256 = 1381601950848 :=
  @P1_7_1_3.block_append 5226 1133 4717 4845 128 128 256 705957166656 675644784192 1381601950848 cost_5226_1133_block28 cost_5226_1133_block29 rfl rfl rfl

private theorem cost_5226_1133_join0_30 : P1_7_1_3.blockEstimate 5226 1133 4973 256 = 1241327066937 :=
  @P1_7_1_3.block_append 5226 1133 4973 5101 128 128 256 640576060992 600751005945 1241327066937 cost_5226_1133_block30 cost_5226_1133_block31 rfl rfl rfl

private theorem cost_5226_1133_join0_32 : P1_7_1_3.blockEstimate 5226 1133 5229 256 = 1067729650376 :=
  @P1_7_1_3.block_append 5226 1133 5229 5357 128 128 256 556758137643 510971512733 1067729650376 cost_5226_1133_block32 cost_5226_1133_block33 rfl rfl rfl

private theorem cost_5226_1133_join0_34 : P1_7_1_3.blockEstimate 5226 1133 5485 256 = 882101295427 :=
  @P1_7_1_3.block_append 5226 1133 5485 5613 128 128 256 464424947017 417676348410 882101295427 cost_5226_1133_block34 cost_5226_1133_block35 rfl rfl rfl

private theorem cost_5226_1133_join0_36 : P1_7_1_3.blockEstimate 5226 1133 5741 256 = 696951968656 :=
  @P1_7_1_3.block_append 5226 1133 5741 5869 128 128 256 371260901851 325691066805 696951968656 cost_5226_1133_block36 cost_5226_1133_block37 rfl rfl rfl

private theorem cost_5226_1133_join0_38 : P1_7_1_3.blockEstimate 5226 1133 5997 256 = 520481022659 :=
  @P1_7_1_3.block_append 5226 1133 5997 6125 128 128 256 281456577537 239024445122 520481022659 cost_5226_1133_block38 cost_5226_1133_block39 rfl rfl rfl

private theorem cost_5226_1133_join0_40 : P1_7_1_3.blockEstimate 5226 1133 6253 256 = 359813380721 :=
  @P1_7_1_3.block_append 5226 1133 6253 6381 128 128 256 198829150481 160984230240 359813380721 cost_5226_1133_block40 cost_5226_1133_block41 rfl rfl rfl

private theorem cost_5226_1133_join0_42 : P1_7_1_3.blockEstimate 5226 1133 6509 256 = 221557478080 :=
  @P1_7_1_3.block_append 5226 1133 6509 6637 128 128 256 126290061664 95267416416 221557478080 cost_5226_1133_block42 cost_5226_1133_block43 rfl rfl rfl

private theorem cost_5226_1133_join0_44 : P1_7_1_3.blockEstimate 5226 1133 6765 256 = 113411281600 :=
  @P1_7_1_3.block_append 5226 1133 6765 6893 128 128 256 68167952736 45243328864 113411281600 cost_5226_1133_block44 cost_5226_1133_block45 rfl rfl rfl

private theorem cost_5226_1133_join0_46 : P1_7_1_3.blockEstimate 5226 1133 7021 256 = 39670436544 :=
  @P1_7_1_3.block_append 5226 1133 7021 7149 128 128 256 26745203040 12925233504 39670436544 cost_5226_1133_block46 cost_5226_1133_block47 rfl rfl rfl

private theorem cost_5226_1133_join0_48 : P1_7_1_3.blockEstimate 5226 1133 7277 215 = 4334563242 :=
  @P1_7_1_3.block_append 5226 1133 7277 7405 128 87 215 4035078496 299484746 4334563242 cost_5226_1133_block48 cost_5226_1133_block49 rfl rfl rfl

private theorem cost_5226_1133_join1_0 : P1_7_1_3.blockEstimate 5226 1133 1133 512 = 108966059136 :=
  @P1_7_1_3.block_append 5226 1133 1133 1389 256 256 512 14243589696 94722469440 108966059136 cost_5226_1133_join0_0 cost_5226_1133_join0_2 rfl rfl rfl

private theorem cost_5226_1133_join1_2 : P1_7_1_3.blockEstimate 5226 1133 1645 512 = 691297524864 :=
  @P1_7_1_3.block_append 5226 1133 1645 1901 256 256 512 243526561344 447770963520 691297524864 cost_5226_1133_join0_4 cost_5226_1133_join0_6 rfl rfl rfl

private theorem cost_5226_1133_join1_4 : P1_7_1_3.blockEstimate 5226 1133 2157 512 = 1624255378551 :=
  @P1_7_1_3.block_append 5226 1133 2157 2413 256 256 512 692462057463 931793321088 1624255378551 cost_5226_1133_join0_8 cost_5226_1133_join0_10 rfl rfl rfl

private theorem cost_5226_1133_join1_6 : P1_7_1_3.blockEstimate 5226 1133 2669 512 = 2432080836864 :=
  @P1_7_1_3.block_append 5226 1133 2669 2925 256 256 512 1133974961280 1298105875584 2432080836864 cost_5226_1133_join0_12 cost_5226_1133_join0_14 rfl rfl rfl

private theorem cost_5226_1133_join1_8 : P1_7_1_3.blockEstimate 5226 1133 3181 512 = 2936401590528 :=
  @P1_7_1_3.block_append 5226 1133 3181 3437 256 256 512 1424186064000 1512215526528 2936401590528 cost_5226_1133_join0_16 cost_5226_1133_join0_18 rfl rfl rfl

private theorem cost_5226_1133_join1_10 : P1_7_1_3.blockEstimate 5226 1133 3693 512 = 3136316537088 :=
  @P1_7_1_3.block_append 5226 1133 3693 3949 256 256 512 1562194263168 1574122273920 3136316537088 cost_5226_1133_join0_20 cost_5226_1133_join0_22 rfl rfl rfl

private theorem cost_5226_1133_join1_12 : P1_7_1_3.blockEstimate 5226 1133 4205 512 = 3031825676544 :=
  @P1_7_1_3.block_append 5226 1133 4205 4461 256 256 512 1547999558784 1483826117760 3031825676544 cost_5226_1133_join0_24 cost_5226_1133_join0_26 rfl rfl rfl

private theorem cost_5226_1133_join1_14 : P1_7_1_3.blockEstimate 5226 1133 4717 512 = 2622929017785 :=
  @P1_7_1_3.block_append 5226 1133 4717 4973 256 256 512 1381601950848 1241327066937 2622929017785 cost_5226_1133_join0_28 cost_5226_1133_join0_30 rfl rfl rfl

private theorem cost_5226_1133_join1_16 : P1_7_1_3.blockEstimate 5226 1133 5229 512 = 1949830945803 :=
  @P1_7_1_3.block_append 5226 1133 5229 5485 256 256 512 1067729650376 882101295427 1949830945803 cost_5226_1133_join0_32 cost_5226_1133_join0_34 rfl rfl rfl

private theorem cost_5226_1133_join1_18 : P1_7_1_3.blockEstimate 5226 1133 5741 512 = 1217432991315 :=
  @P1_7_1_3.block_append 5226 1133 5741 5997 256 256 512 696951968656 520481022659 1217432991315 cost_5226_1133_join0_36 cost_5226_1133_join0_38 rfl rfl rfl

private theorem cost_5226_1133_join1_20 : P1_7_1_3.blockEstimate 5226 1133 6253 512 = 581370858801 :=
  @P1_7_1_3.block_append 5226 1133 6253 6509 256 256 512 359813380721 221557478080 581370858801 cost_5226_1133_join0_40 cost_5226_1133_join0_42 rfl rfl rfl

private theorem cost_5226_1133_join1_22 : P1_7_1_3.blockEstimate 5226 1133 6765 512 = 153081718144 :=
  @P1_7_1_3.block_append 5226 1133 6765 7021 256 256 512 113411281600 39670436544 153081718144 cost_5226_1133_join0_44 cost_5226_1133_join0_46 rfl rfl rfl

private theorem cost_5226_1133_join2_0 : P1_7_1_3.blockEstimate 5226 1133 1133 1024 = 800263584000 :=
  @P1_7_1_3.block_append 5226 1133 1133 1645 512 512 1024 108966059136 691297524864 800263584000 cost_5226_1133_join1_0 cost_5226_1133_join1_2 rfl rfl rfl

private theorem cost_5226_1133_join2_2 : P1_7_1_3.blockEstimate 5226 1133 2157 1024 = 4056336215415 :=
  @P1_7_1_3.block_append 5226 1133 2157 2669 512 512 1024 1624255378551 2432080836864 4056336215415 cost_5226_1133_join1_4 cost_5226_1133_join1_6 rfl rfl rfl

private theorem cost_5226_1133_join2_4 : P1_7_1_3.blockEstimate 5226 1133 3181 1024 = 6072718127616 :=
  @P1_7_1_3.block_append 5226 1133 3181 3693 512 512 1024 2936401590528 3136316537088 6072718127616 cost_5226_1133_join1_8 cost_5226_1133_join1_10 rfl rfl rfl

private theorem cost_5226_1133_join2_6 : P1_7_1_3.blockEstimate 5226 1133 4205 1024 = 5654754694329 :=
  @P1_7_1_3.block_append 5226 1133 4205 4717 512 512 1024 3031825676544 2622929017785 5654754694329 cost_5226_1133_join1_12 cost_5226_1133_join1_14 rfl rfl rfl

private theorem cost_5226_1133_join2_8 : P1_7_1_3.blockEstimate 5226 1133 5229 1024 = 3167263937118 :=
  @P1_7_1_3.block_append 5226 1133 5229 5741 512 512 1024 1949830945803 1217432991315 3167263937118 cost_5226_1133_join1_16 cost_5226_1133_join1_18 rfl rfl rfl

private theorem cost_5226_1133_join2_10 : P1_7_1_3.blockEstimate 5226 1133 6253 1024 = 734452576945 :=
  @P1_7_1_3.block_append 5226 1133 6253 6765 512 512 1024 581370858801 153081718144 734452576945 cost_5226_1133_join1_20 cost_5226_1133_join1_22 rfl rfl rfl

private theorem cost_5226_1133_join3_0 : P1_7_1_3.blockEstimate 5226 1133 1133 2048 = 4856599799415 :=
  @P1_7_1_3.block_append 5226 1133 1133 2157 1024 1024 2048 800263584000 4056336215415 4856599799415 cost_5226_1133_join2_0 cost_5226_1133_join2_2 rfl rfl rfl

private theorem cost_5226_1133_join3_2 : P1_7_1_3.blockEstimate 5226 1133 3181 2048 = 11727472821945 :=
  @P1_7_1_3.block_append 5226 1133 3181 4205 1024 1024 2048 6072718127616 5654754694329 11727472821945 cost_5226_1133_join2_4 cost_5226_1133_join2_6 rfl rfl rfl

private theorem cost_5226_1133_join3_4 : P1_7_1_3.blockEstimate 5226 1133 5229 2048 = 3901716514063 :=
  @P1_7_1_3.block_append 5226 1133 5229 6253 1024 1024 2048 3167263937118 734452576945 3901716514063 cost_5226_1133_join2_8 cost_5226_1133_join2_10 rfl rfl rfl

private theorem cost_5226_1133_join4_0 : P1_7_1_3.blockEstimate 5226 1133 1133 4096 = 16584072621360 :=
  @P1_7_1_3.block_append 5226 1133 1133 3181 2048 2048 4096 4856599799415 11727472821945 16584072621360 cost_5226_1133_join3_0 cost_5226_1133_join3_2 rfl rfl rfl

private theorem cost_5226_1133_join4_2 : P1_7_1_3.blockEstimate 5226 1133 5229 2263 = 3906051077305 :=
  @P1_7_1_3.block_append 5226 1133 5229 7277 2048 215 2263 3901716514063 4334563242 3906051077305 cost_5226_1133_join3_4 cost_5226_1133_join0_48 rfl rfl rfl

private theorem cost_5226_1133_join5_0 : P1_7_1_3.blockEstimate 5226 1133 1133 6359 = 20490123698665 :=
  @P1_7_1_3.block_append 5226 1133 1133 5229 4096 2263 6359 16584072621360 3906051077305 20490123698665 cost_5226_1133_join4_0 cost_5226_1133_join4_2 rfl rfl rfl

private theorem cost_5226_1133_total : P1_7_1_3.momentEstimate 5226 1133 = 20490123698665 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 5226 + 1133 = 6359 by decide]
  exact cost_5226_1133_join5_0

theorem moment5226_1133 : P1_7_1.groupedPoleMoment 5226 1133 ≤ 20490123698665 :=
  (P1_7_1_3.grouped_bound 5226 1133).trans_eq cost_5226_1133_total
private theorem cost_5226_1159_block0 : P1_7_1_3.blockEstimate 5226 1159 1159 128 = 1835577120 := by decide +kernel

private theorem cost_5226_1159_block1 : P1_7_1_3.blockEstimate 5226 1159 1287 128 = 12408012576 := by decide +kernel

private theorem cost_5226_1159_block2 : P1_7_1_3.blockEstimate 5226 1159 1415 128 = 32729059104 := by decide +kernel

private theorem cost_5226_1159_block3 : P1_7_1_3.blockEstimate 5226 1159 1543 128 = 61993410336 := by decide +kernel

private theorem cost_5226_1159_block4 : P1_7_1_3.blockEstimate 5226 1159 1671 128 = 99395759904 := by decide +kernel

private theorem cost_5226_1159_block5 : P1_7_1_3.blockEstimate 5226 1159 1799 128 = 144130801440 := by decide +kernel

private theorem cost_5226_1159_block6 : P1_7_1_3.blockEstimate 5226 1159 1927 128 = 195393228576 := by decide +kernel

private theorem cost_5226_1159_block7 : P1_7_1_3.blockEstimate 5226 1159 2055 128 = 252377734944 := by decide +kernel

private theorem cost_5226_1159_block8 : P1_7_1_3.blockEstimate 5226 1159 2183 128 = 314279014176 := by decide +kernel

private theorem cost_5226_1159_block9 : P1_7_1_3.blockEstimate 5226 1159 2311 128 = 379117664234 := by decide +kernel

private theorem cost_5226_1159_block10 : P1_7_1_3.blockEstimate 5226 1159 2439 128 = 440799591680 := by decide +kernel

private theorem cost_5226_1159_block11 : P1_7_1_3.blockEstimate 5226 1159 2567 128 = 497616354560 := by decide +kernel

private theorem cost_5226_1159_block12 : P1_7_1_3.blockEstimate 5226 1159 2695 128 = 549567724800 := by decide +kernel

private theorem cost_5226_1159_block13 : P1_7_1_3.blockEstimate 5226 1159 2823 128 = 596653702400 := by decide +kernel

private theorem cost_5226_1159_block14 : P1_7_1_3.blockEstimate 5226 1159 2951 128 = 638874287360 := by decide +kernel

private theorem cost_5226_1159_block15 : P1_7_1_3.blockEstimate 5226 1159 3079 128 = 676229479680 := by decide +kernel

private theorem cost_5226_1159_block16 : P1_7_1_3.blockEstimate 5226 1159 3207 128 = 708719279360 := by decide +kernel

private theorem cost_5226_1159_block17 : P1_7_1_3.blockEstimate 5226 1159 3335 128 = 736343686400 := by decide +kernel

private theorem cost_5226_1159_block18 : P1_7_1_3.blockEstimate 5226 1159 3463 128 = 759102700800 := by decide +kernel

private theorem cost_5226_1159_block19 : P1_7_1_3.blockEstimate 5226 1159 3591 128 = 776996322560 := by decide +kernel

private theorem cost_5226_1159_block20 : P1_7_1_3.blockEstimate 5226 1159 3719 128 = 790024551680 := by decide +kernel

private theorem cost_5226_1159_block21 : P1_7_1_3.blockEstimate 5226 1159 3847 128 = 798187388160 := by decide +kernel

private theorem cost_5226_1159_block22 : P1_7_1_3.blockEstimate 5226 1159 3975 128 = 801484832000 := by decide +kernel

private theorem cost_5226_1159_block23 : P1_7_1_3.blockEstimate 5226 1159 4103 128 = 799916883200 := by decide +kernel

private theorem cost_5226_1159_block24 : P1_7_1_3.blockEstimate 5226 1159 4231 128 = 793483541760 := by decide +kernel

private theorem cost_5226_1159_block25 : P1_7_1_3.blockEstimate 5226 1159 4359 128 = 782184807680 := by decide +kernel

private theorem cost_5226_1159_block26 : P1_7_1_3.blockEstimate 5226 1159 4487 128 = 766020680960 := by decide +kernel

private theorem cost_5226_1159_block27 : P1_7_1_3.blockEstimate 5226 1159 4615 128 = 744991161600 := by decide +kernel

private theorem cost_5226_1159_block28 : P1_7_1_3.blockEstimate 5226 1159 4743 128 = 719096249600 := by decide +kernel

private theorem cost_5226_1159_block29 : P1_7_1_3.blockEstimate 5226 1159 4871 128 = 688335944960 := by decide +kernel

private theorem cost_5226_1159_block30 : P1_7_1_3.blockEstimate 5226 1159 4999 128 = 652710247680 := by decide +kernel

private theorem cost_5226_1159_block31 : P1_7_1_3.blockEstimate 5226 1159 5127 128 = 612225435080 := by decide +kernel

private theorem cost_5226_1159_block32 : P1_7_1_3.blockEstimate 5226 1159 5255 128 = 567860110325 := by decide +kernel

private theorem cost_5226_1159_block33 : P1_7_1_3.blockEstimate 5226 1159 5383 128 = 521887988518 := by decide +kernel

private theorem cost_5226_1159_block34 : P1_7_1_3.blockEstimate 5226 1159 5511 128 = 475108337764 := by decide +kernel

private theorem cost_5226_1159_block35 : P1_7_1_3.blockEstimate 5226 1159 5639 128 = 428075587470 := by decide +kernel

private theorem cost_5226_1159_block36 : P1_7_1_3.blockEstimate 5226 1159 5767 128 = 381321951157 := by decide +kernel

private theorem cost_5226_1159_block37 : P1_7_1_3.blockEstimate 5226 1159 5895 128 = 335357427389 := by decide +kernel

private theorem cost_5226_1159_block38 : P1_7_1_3.blockEstimate 5226 1159 6023 128 = 290669799734 := by decide +kernel

private theorem cost_5226_1159_block39 : P1_7_1_3.blockEstimate 5226 1159 6151 128 = 247724635422 := by decide +kernel

private theorem cost_5226_1159_block40 : P1_7_1_3.blockEstimate 5226 1159 6279 128 = 206955019542 := by decide +kernel

private theorem cost_5226_1159_block41 : P1_7_1_3.blockEstimate 5226 1159 6407 128 = 168457532848 := by decide +kernel

private theorem cost_5226_1159_block42 : P1_7_1_3.blockEstimate 5226 1159 6535 128 = 133048336816 := by decide +kernel

private theorem cost_5226_1159_block43 : P1_7_1_3.blockEstimate 5226 1159 6663 128 = 101259546032 := by decide +kernel

private theorem cost_5226_1159_block44 : P1_7_1_3.blockEstimate 5226 1159 6791 128 = 73342818736 := by decide +kernel

private theorem cost_5226_1159_block45 : P1_7_1_3.blockEstimate 5226 1159 6919 128 = 49549813168 := by decide +kernel

private theorem cost_5226_1159_block46 : P1_7_1_3.blockEstimate 5226 1159 7047 128 = 30132187568 := by decide +kernel

private theorem cost_5226_1159_block47 : P1_7_1_3.blockEstimate 5226 1159 7175 128 = 15341600176 := by decide +kernel

private theorem cost_5226_1159_block48 : P1_7_1_3.blockEstimate 5226 1159 7303 128 = 5429709232 := by decide +kernel

private theorem cost_5226_1159_block49 : P1_7_1_3.blockEstimate 5226 1159 7431 113 = 647110524 := by decide +kernel

private theorem cost_5226_1159_join0_0 : P1_7_1_3.blockEstimate 5226 1159 1159 256 = 14243589696 :=
  @P1_7_1_3.block_append 5226 1159 1159 1287 128 128 256 1835577120 12408012576 14243589696 cost_5226_1159_block0 cost_5226_1159_block1 rfl rfl rfl

private theorem cost_5226_1159_join0_2 : P1_7_1_3.blockEstimate 5226 1159 1415 256 = 94722469440 :=
  @P1_7_1_3.block_append 5226 1159 1415 1543 128 128 256 32729059104 61993410336 94722469440 cost_5226_1159_block2 cost_5226_1159_block3 rfl rfl rfl

private theorem cost_5226_1159_join0_4 : P1_7_1_3.blockEstimate 5226 1159 1671 256 = 243526561344 :=
  @P1_7_1_3.block_append 5226 1159 1671 1799 128 128 256 99395759904 144130801440 243526561344 cost_5226_1159_block4 cost_5226_1159_block5 rfl rfl rfl

private theorem cost_5226_1159_join0_6 : P1_7_1_3.blockEstimate 5226 1159 1927 256 = 447770963520 :=
  @P1_7_1_3.block_append 5226 1159 1927 2055 128 128 256 195393228576 252377734944 447770963520 cost_5226_1159_block6 cost_5226_1159_block7 rfl rfl rfl

private theorem cost_5226_1159_join0_8 : P1_7_1_3.blockEstimate 5226 1159 2183 256 = 693396678410 :=
  @P1_7_1_3.block_append 5226 1159 2183 2311 128 128 256 314279014176 379117664234 693396678410 cost_5226_1159_block8 cost_5226_1159_block9 rfl rfl rfl

private theorem cost_5226_1159_join0_10 : P1_7_1_3.blockEstimate 5226 1159 2439 256 = 938415946240 :=
  @P1_7_1_3.block_append 5226 1159 2439 2567 128 128 256 440799591680 497616354560 938415946240 cost_5226_1159_block10 cost_5226_1159_block11 rfl rfl rfl

private theorem cost_5226_1159_join0_12 : P1_7_1_3.blockEstimate 5226 1159 2695 256 = 1146221427200 :=
  @P1_7_1_3.block_append 5226 1159 2695 2823 128 128 256 549567724800 596653702400 1146221427200 cost_5226_1159_block12 cost_5226_1159_block13 rfl rfl rfl

private theorem cost_5226_1159_join0_14 : P1_7_1_3.blockEstimate 5226 1159 2951 256 = 1315103767040 :=
  @P1_7_1_3.block_append 5226 1159 2951 3079 128 128 256 638874287360 676229479680 1315103767040 cost_5226_1159_block14 cost_5226_1159_block15 rfl rfl rfl

private theorem cost_5226_1159_join0_16 : P1_7_1_3.blockEstimate 5226 1159 3207 256 = 1445062965760 :=
  @P1_7_1_3.block_append 5226 1159 3207 3335 128 128 256 708719279360 736343686400 1445062965760 cost_5226_1159_block16 cost_5226_1159_block17 rfl rfl rfl

private theorem cost_5226_1159_join0_18 : P1_7_1_3.blockEstimate 5226 1159 3463 256 = 1536099023360 :=
  @P1_7_1_3.block_append 5226 1159 3463 3591 128 128 256 759102700800 776996322560 1536099023360 cost_5226_1159_block18 cost_5226_1159_block19 rfl rfl rfl

private theorem cost_5226_1159_join0_20 : P1_7_1_3.blockEstimate 5226 1159 3719 256 = 1588211939840 :=
  @P1_7_1_3.block_append 5226 1159 3719 3847 128 128 256 790024551680 798187388160 1588211939840 cost_5226_1159_block20 cost_5226_1159_block21 rfl rfl rfl

private theorem cost_5226_1159_join0_22 : P1_7_1_3.blockEstimate 5226 1159 3975 256 = 1601401715200 :=
  @P1_7_1_3.block_append 5226 1159 3975 4103 128 128 256 801484832000 799916883200 1601401715200 cost_5226_1159_block22 cost_5226_1159_block23 rfl rfl rfl

private theorem cost_5226_1159_join0_24 : P1_7_1_3.blockEstimate 5226 1159 4231 256 = 1575668349440 :=
  @P1_7_1_3.block_append 5226 1159 4231 4359 128 128 256 793483541760 782184807680 1575668349440 cost_5226_1159_block24 cost_5226_1159_block25 rfl rfl rfl

private theorem cost_5226_1159_join0_26 : P1_7_1_3.blockEstimate 5226 1159 4487 256 = 1511011842560 :=
  @P1_7_1_3.block_append 5226 1159 4487 4615 128 128 256 766020680960 744991161600 1511011842560 cost_5226_1159_block26 cost_5226_1159_block27 rfl rfl rfl

private theorem cost_5226_1159_join0_28 : P1_7_1_3.blockEstimate 5226 1159 4743 256 = 1407432194560 :=
  @P1_7_1_3.block_append 5226 1159 4743 4871 128 128 256 719096249600 688335944960 1407432194560 cost_5226_1159_block28 cost_5226_1159_block29 rfl rfl rfl

private theorem cost_5226_1159_join0_30 : P1_7_1_3.blockEstimate 5226 1159 4999 256 = 1264935682760 :=
  @P1_7_1_3.block_append 5226 1159 4999 5127 128 128 256 652710247680 612225435080 1264935682760 cost_5226_1159_block30 cost_5226_1159_block31 rfl rfl rfl

private theorem cost_5226_1159_join0_32 : P1_7_1_3.blockEstimate 5226 1159 5255 256 = 1089748098843 :=
  @P1_7_1_3.block_append 5226 1159 5255 5383 128 128 256 567860110325 521887988518 1089748098843 cost_5226_1159_block32 cost_5226_1159_block33 rfl rfl rfl

private theorem cost_5226_1159_join0_34 : P1_7_1_3.blockEstimate 5226 1159 5511 256 = 903183925234 :=
  @P1_7_1_3.block_append 5226 1159 5511 5639 128 128 256 475108337764 428075587470 903183925234 cost_5226_1159_block34 cost_5226_1159_block35 rfl rfl rfl

private theorem cost_5226_1159_join0_36 : P1_7_1_3.blockEstimate 5226 1159 5767 256 = 716679378546 :=
  @P1_7_1_3.block_append 5226 1159 5767 5895 128 128 256 381321951157 335357427389 716679378546 cost_5226_1159_block36 cost_5226_1159_block37 rfl rfl rfl

private theorem cost_5226_1159_join0_38 : P1_7_1_3.blockEstimate 5226 1159 6023 256 = 538394435156 :=
  @P1_7_1_3.block_append 5226 1159 6023 6151 128 128 256 290669799734 247724635422 538394435156 cost_5226_1159_block38 cost_5226_1159_block39 rfl rfl rfl

private theorem cost_5226_1159_join0_40 : P1_7_1_3.blockEstimate 5226 1159 6279 256 = 375412552390 :=
  @P1_7_1_3.block_append 5226 1159 6279 6407 128 128 256 206955019542 168457532848 375412552390 cost_5226_1159_block40 cost_5226_1159_block41 rfl rfl rfl

private theorem cost_5226_1159_join0_42 : P1_7_1_3.blockEstimate 5226 1159 6535 256 = 234307882848 :=
  @P1_7_1_3.block_append 5226 1159 6535 6663 128 128 256 133048336816 101259546032 234307882848 cost_5226_1159_block42 cost_5226_1159_block43 rfl rfl rfl

private theorem cost_5226_1159_join0_44 : P1_7_1_3.blockEstimate 5226 1159 6791 256 = 122892631904 :=
  @P1_7_1_3.block_append 5226 1159 6791 6919 128 128 256 73342818736 49549813168 122892631904 cost_5226_1159_block44 cost_5226_1159_block45 rfl rfl rfl

private theorem cost_5226_1159_join0_46 : P1_7_1_3.blockEstimate 5226 1159 7047 256 = 45473787744 :=
  @P1_7_1_3.block_append 5226 1159 7047 7175 128 128 256 30132187568 15341600176 45473787744 cost_5226_1159_block46 cost_5226_1159_block47 rfl rfl rfl

private theorem cost_5226_1159_join0_48 : P1_7_1_3.blockEstimate 5226 1159 7303 241 = 6076819756 :=
  @P1_7_1_3.block_append 5226 1159 7303 7431 128 113 241 5429709232 647110524 6076819756 cost_5226_1159_block48 cost_5226_1159_block49 rfl rfl rfl

private theorem cost_5226_1159_join1_0 : P1_7_1_3.blockEstimate 5226 1159 1159 512 = 108966059136 :=
  @P1_7_1_3.block_append 5226 1159 1159 1415 256 256 512 14243589696 94722469440 108966059136 cost_5226_1159_join0_0 cost_5226_1159_join0_2 rfl rfl rfl

private theorem cost_5226_1159_join1_2 : P1_7_1_3.blockEstimate 5226 1159 1671 512 = 691297524864 :=
  @P1_7_1_3.block_append 5226 1159 1671 1927 256 256 512 243526561344 447770963520 691297524864 cost_5226_1159_join0_4 cost_5226_1159_join0_6 rfl rfl rfl

private theorem cost_5226_1159_join1_4 : P1_7_1_3.blockEstimate 5226 1159 2183 512 = 1631812624650 :=
  @P1_7_1_3.block_append 5226 1159 2183 2439 256 256 512 693396678410 938415946240 1631812624650 cost_5226_1159_join0_8 cost_5226_1159_join0_10 rfl rfl rfl

private theorem cost_5226_1159_join1_6 : P1_7_1_3.blockEstimate 5226 1159 2695 512 = 2461325194240 :=
  @P1_7_1_3.block_append 5226 1159 2695 2951 256 256 512 1146221427200 1315103767040 2461325194240 cost_5226_1159_join0_12 cost_5226_1159_join0_14 rfl rfl rfl

private theorem cost_5226_1159_join1_8 : P1_7_1_3.blockEstimate 5226 1159 3207 512 = 2981161989120 :=
  @P1_7_1_3.block_append 5226 1159 3207 3463 256 256 512 1445062965760 1536099023360 2981161989120 cost_5226_1159_join0_16 cost_5226_1159_join0_18 rfl rfl rfl

private theorem cost_5226_1159_join1_10 : P1_7_1_3.blockEstimate 5226 1159 3719 512 = 3189613655040 :=
  @P1_7_1_3.block_append 5226 1159 3719 3975 256 256 512 1588211939840 1601401715200 3189613655040 cost_5226_1159_join0_20 cost_5226_1159_join0_22 rfl rfl rfl

private theorem cost_5226_1159_join1_12 : P1_7_1_3.blockEstimate 5226 1159 4231 512 = 3086680192000 :=
  @P1_7_1_3.block_append 5226 1159 4231 4487 256 256 512 1575668349440 1511011842560 3086680192000 cost_5226_1159_join0_24 cost_5226_1159_join0_26 rfl rfl rfl

private theorem cost_5226_1159_join1_14 : P1_7_1_3.blockEstimate 5226 1159 4743 512 = 2672367877320 :=
  @P1_7_1_3.block_append 5226 1159 4743 4999 256 256 512 1407432194560 1264935682760 2672367877320 cost_5226_1159_join0_28 cost_5226_1159_join0_30 rfl rfl rfl

private theorem cost_5226_1159_join1_16 : P1_7_1_3.blockEstimate 5226 1159 5255 512 = 1992932024077 :=
  @P1_7_1_3.block_append 5226 1159 5255 5511 256 256 512 1089748098843 903183925234 1992932024077 cost_5226_1159_join0_32 cost_5226_1159_join0_34 rfl rfl rfl

private theorem cost_5226_1159_join1_18 : P1_7_1_3.blockEstimate 5226 1159 5767 512 = 1255073813702 :=
  @P1_7_1_3.block_append 5226 1159 5767 6023 256 256 512 716679378546 538394435156 1255073813702 cost_5226_1159_join0_36 cost_5226_1159_join0_38 rfl rfl rfl

private theorem cost_5226_1159_join1_20 : P1_7_1_3.blockEstimate 5226 1159 6279 512 = 609720435238 :=
  @P1_7_1_3.block_append 5226 1159 6279 6535 256 256 512 375412552390 234307882848 609720435238 cost_5226_1159_join0_40 cost_5226_1159_join0_42 rfl rfl rfl

private theorem cost_5226_1159_join1_22 : P1_7_1_3.blockEstimate 5226 1159 6791 512 = 168366419648 :=
  @P1_7_1_3.block_append 5226 1159 6791 7047 256 256 512 122892631904 45473787744 168366419648 cost_5226_1159_join0_44 cost_5226_1159_join0_46 rfl rfl rfl

private theorem cost_5226_1159_join2_0 : P1_7_1_3.blockEstimate 5226 1159 1159 1024 = 800263584000 :=
  @P1_7_1_3.block_append 5226 1159 1159 1671 512 512 1024 108966059136 691297524864 800263584000 cost_5226_1159_join1_0 cost_5226_1159_join1_2 rfl rfl rfl

private theorem cost_5226_1159_join2_2 : P1_7_1_3.blockEstimate 5226 1159 2183 1024 = 4093137818890 :=
  @P1_7_1_3.block_append 5226 1159 2183 2695 512 512 1024 1631812624650 2461325194240 4093137818890 cost_5226_1159_join1_4 cost_5226_1159_join1_6 rfl rfl rfl

private theorem cost_5226_1159_join2_4 : P1_7_1_3.blockEstimate 5226 1159 3207 1024 = 6170775644160 :=
  @P1_7_1_3.block_append 5226 1159 3207 3719 512 512 1024 2981161989120 3189613655040 6170775644160 cost_5226_1159_join1_8 cost_5226_1159_join1_10 rfl rfl rfl

private theorem cost_5226_1159_join2_6 : P1_7_1_3.blockEstimate 5226 1159 4231 1024 = 5759048069320 :=
  @P1_7_1_3.block_append 5226 1159 4231 4743 512 512 1024 3086680192000 2672367877320 5759048069320 cost_5226_1159_join1_12 cost_5226_1159_join1_14 rfl rfl rfl

private theorem cost_5226_1159_join2_8 : P1_7_1_3.blockEstimate 5226 1159 5255 1024 = 3248005837779 :=
  @P1_7_1_3.block_append 5226 1159 5255 5767 512 512 1024 1992932024077 1255073813702 3248005837779 cost_5226_1159_join1_16 cost_5226_1159_join1_18 rfl rfl rfl

private theorem cost_5226_1159_join2_10 : P1_7_1_3.blockEstimate 5226 1159 6279 1024 = 778086854886 :=
  @P1_7_1_3.block_append 5226 1159 6279 6791 512 512 1024 609720435238 168366419648 778086854886 cost_5226_1159_join1_20 cost_5226_1159_join1_22 rfl rfl rfl

private theorem cost_5226_1159_join3_0 : P1_7_1_3.blockEstimate 5226 1159 1159 2048 = 4893401402890 :=
  @P1_7_1_3.block_append 5226 1159 1159 2183 1024 1024 2048 800263584000 4093137818890 4893401402890 cost_5226_1159_join2_0 cost_5226_1159_join2_2 rfl rfl rfl

private theorem cost_5226_1159_join3_2 : P1_7_1_3.blockEstimate 5226 1159 3207 2048 = 11929823713480 :=
  @P1_7_1_3.block_append 5226 1159 3207 4231 1024 1024 2048 6170775644160 5759048069320 11929823713480 cost_5226_1159_join2_4 cost_5226_1159_join2_6 rfl rfl rfl

private theorem cost_5226_1159_join3_4 : P1_7_1_3.blockEstimate 5226 1159 5255 2048 = 4026092692665 :=
  @P1_7_1_3.block_append 5226 1159 5255 6279 1024 1024 2048 3248005837779 778086854886 4026092692665 cost_5226_1159_join2_8 cost_5226_1159_join2_10 rfl rfl rfl

private theorem cost_5226_1159_join4_0 : P1_7_1_3.blockEstimate 5226 1159 1159 4096 = 16823225116370 :=
  @P1_7_1_3.block_append 5226 1159 1159 3207 2048 2048 4096 4893401402890 11929823713480 16823225116370 cost_5226_1159_join3_0 cost_5226_1159_join3_2 rfl rfl rfl

private theorem cost_5226_1159_join4_2 : P1_7_1_3.blockEstimate 5226 1159 5255 2289 = 4032169512421 :=
  @P1_7_1_3.block_append 5226 1159 5255 7303 2048 241 2289 4026092692665 6076819756 4032169512421 cost_5226_1159_join3_4 cost_5226_1159_join0_48 rfl rfl rfl

private theorem cost_5226_1159_join5_0 : P1_7_1_3.blockEstimate 5226 1159 1159 6385 = 20855394628791 :=
  @P1_7_1_3.block_append 5226 1159 1159 5255 4096 2289 6385 16823225116370 4032169512421 20855394628791 cost_5226_1159_join4_0 cost_5226_1159_join4_2 rfl rfl rfl

private theorem cost_5226_1159_total : P1_7_1_3.momentEstimate 5226 1159 = 20855394628791 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 5226 + 1159 = 6385 by decide]
  exact cost_5226_1159_join5_0

theorem moment5226_1159 : P1_7_1.groupedPoleMoment 5226 1159 ≤ 20855394628791 :=
  (P1_7_1_3.grouped_bound 5226 1159).trans_eq cost_5226_1159_total
private theorem cost_5411_1163_block0 : P1_7_1_3.blockEstimate 5411 1163 1163 128 = 1901762720 := by decide +kernel

private theorem cost_5411_1163_block1 : P1_7_1_3.blockEstimate 5411 1163 1291 128 = 12865202336 := by decide +kernel

private theorem cost_5411_1163_block2 : P1_7_1_3.blockEstimate 5411 1163 1419 128 = 33965226144 := by decide +kernel

private theorem cost_5411_1163_block3 : P1_7_1_3.blockEstimate 5411 1163 1547 128 = 64396527776 := by decide +kernel

private theorem cost_5411_1163_block4 : P1_7_1_3.blockEstimate 5411 1163 1675 128 = 103353800864 := by decide +kernel

private theorem cost_5411_1163_block5 : P1_7_1_3.blockEstimate 5411 1163 1803 128 = 150031739040 := by decide +kernel

private theorem cost_5411_1163_block6 : P1_7_1_3.blockEstimate 5411 1163 1931 128 = 203625035936 := by decide +kernel

private theorem cost_5411_1163_block7 : P1_7_1_3.blockEstimate 5411 1163 2059 128 = 263328385184 := by decide +kernel

private theorem cost_5411_1163_block8 : P1_7_1_3.blockEstimate 5411 1163 2187 128 = 328336480416 := by decide +kernel

private theorem cost_5411_1163_block9 : P1_7_1_3.blockEstimate 5411 1163 2315 128 = 396733444517 := by decide +kernel

private theorem cost_5411_1163_block10 : P1_7_1_3.blockEstimate 5411 1163 2443 128 = 462193633152 := by decide +kernel

private theorem cost_5411_1163_block11 : P1_7_1_3.blockEstimate 5411 1163 2571 128 = 522772588416 := by decide +kernel

private theorem cost_5411_1163_block12 : P1_7_1_3.blockEstimate 5411 1163 2699 128 = 578469373824 := by decide +kernel

private theorem cost_5411_1163_block13 : P1_7_1_3.blockEstimate 5411 1163 2827 128 = 629283989376 := by decide +kernel

private theorem cost_5411_1163_block14 : P1_7_1_3.blockEstimate 5411 1163 2955 128 = 675216435072 := by decide +kernel

private theorem cost_5411_1163_block15 : P1_7_1_3.blockEstimate 5411 1163 3083 128 = 716266710912 := by decide +kernel

private theorem cost_5411_1163_block16 : P1_7_1_3.blockEstimate 5411 1163 3211 128 = 752434816896 := by decide +kernel

private theorem cost_5411_1163_block17 : P1_7_1_3.blockEstimate 5411 1163 3339 128 = 783720753024 := by decide +kernel

private theorem cost_5411_1163_block18 : P1_7_1_3.blockEstimate 5411 1163 3467 128 = 810124519296 := by decide +kernel

private theorem cost_5411_1163_block19 : P1_7_1_3.blockEstimate 5411 1163 3595 128 = 831646115712 := by decide +kernel

private theorem cost_5411_1163_block20 : P1_7_1_3.blockEstimate 5411 1163 3723 128 = 848285542272 := by decide +kernel

private theorem cost_5411_1163_block21 : P1_7_1_3.blockEstimate 5411 1163 3851 128 = 860042798976 := by decide +kernel

private theorem cost_5411_1163_block22 : P1_7_1_3.blockEstimate 5411 1163 3979 128 = 866917885824 := by decide +kernel

private theorem cost_5411_1163_block23 : P1_7_1_3.blockEstimate 5411 1163 4107 128 = 868910802816 := by decide +kernel

private theorem cost_5411_1163_block24 : P1_7_1_3.blockEstimate 5411 1163 4235 128 = 866021549952 := by decide +kernel

private theorem cost_5411_1163_block25 : P1_7_1_3.blockEstimate 5411 1163 4363 128 = 858250127232 := by decide +kernel

private theorem cost_5411_1163_block26 : P1_7_1_3.blockEstimate 5411 1163 4491 128 = 845596534656 := by decide +kernel

private theorem cost_5411_1163_block27 : P1_7_1_3.blockEstimate 5411 1163 4619 128 = 828060772224 := by decide +kernel

private theorem cost_5411_1163_block28 : P1_7_1_3.blockEstimate 5411 1163 4747 128 = 805642839936 := by decide +kernel

private theorem cost_5411_1163_block29 : P1_7_1_3.blockEstimate 5411 1163 4875 128 = 778342737792 := by decide +kernel

private theorem cost_5411_1163_block30 : P1_7_1_3.blockEstimate 5411 1163 5003 128 = 746160465792 := by decide +kernel

private theorem cost_5411_1163_block31 : P1_7_1_3.blockEstimate 5411 1163 5131 128 = 709096023936 := by decide +kernel

private theorem cost_5411_1163_block32 : P1_7_1_3.blockEstimate 5411 1163 5259 128 = 667149412224 := by decide +kernel

private theorem cost_5411_1163_block33 : P1_7_1_3.blockEstimate 5411 1163 5387 128 = 620625013891 := by decide +kernel

private theorem cost_5411_1163_block34 : P1_7_1_3.blockEstimate 5411 1163 5515 128 = 571805979621 := by decide +kernel

private theorem cost_5411_1163_block35 : P1_7_1_3.blockEstimate 5411 1163 5643 128 = 522108948756 := by decide +kernel

private theorem cost_5411_1163_block36 : P1_7_1_3.blockEstimate 5411 1163 5771 128 = 472100979842 := by decide +kernel

private theorem cost_5411_1163_block37 : P1_7_1_3.blockEstimate 5411 1163 5899 128 = 422323700201 := by decide +kernel

private theorem cost_5411_1163_block38 : P1_7_1_3.blockEstimate 5411 1163 6027 128 = 373296598412 := by decide +kernel

private theorem cost_5411_1163_block39 : P1_7_1_3.blockEstimate 5411 1163 6155 128 = 325517023770 := by decide +kernel

private theorem cost_5411_1163_block40 : P1_7_1_3.blockEstimate 5411 1163 6283 128 = 279460186307 := by decide +kernel

private theorem cost_5411_1163_block41 : P1_7_1_3.blockEstimate 5411 1163 6411 128 = 235579157654 := by decide +kernel

private theorem cost_5411_1163_block42 : P1_7_1_3.blockEstimate 5411 1163 6539 128 = 194147209537 := by decide +kernel

private theorem cost_5411_1163_block43 : P1_7_1_3.blockEstimate 5411 1163 6667 128 = 155504136720 := by decide +kernel

private theorem cost_5411_1163_block44 : P1_7_1_3.blockEstimate 5411 1163 6795 128 = 120528715280 := by decide +kernel

private theorem cost_5411_1163_block45 : P1_7_1_3.blockEstimate 5411 1163 6923 128 = 89499413008 := by decide +kernel

private theorem cost_5411_1163_block46 : P1_7_1_3.blockEstimate 5411 1163 7051 128 = 62667888144 := by decide +kernel

private theorem cost_5411_1163_block47 : P1_7_1_3.blockEstimate 5411 1163 7179 128 = 40285798928 := by decide +kernel

private theorem cost_5411_1163_block48 : P1_7_1_3.blockEstimate 5411 1163 7307 128 = 22604803600 := by decide +kernel

private theorem cost_5411_1163_block49 : P1_7_1_3.blockEstimate 5411 1163 7435 128 = 9876560400 := by decide +kernel

private theorem cost_5411_1163_block50 : P1_7_1_3.blockEstimate 5411 1163 7563 128 = 2352727568 := by decide +kernel

private theorem cost_5411_1163_block51 : P1_7_1_3.blockEstimate 5411 1163 7691 46 = 48101214 := by decide +kernel

private theorem cost_5411_1163_join0_0 : P1_7_1_3.blockEstimate 5411 1163 1163 256 = 14766965056 :=
  @P1_7_1_3.block_append 5411 1163 1163 1291 128 128 256 1901762720 12865202336 14766965056 cost_5411_1163_block0 cost_5411_1163_block1 rfl rfl rfl

private theorem cost_5411_1163_join0_2 : P1_7_1_3.blockEstimate 5411 1163 1419 256 = 98361753920 :=
  @P1_7_1_3.block_append 5411 1163 1419 1547 128 128 256 33965226144 64396527776 98361753920 cost_5411_1163_block2 cost_5411_1163_block3 rfl rfl rfl

private theorem cost_5411_1163_join0_4 : P1_7_1_3.blockEstimate 5411 1163 1675 256 = 253385539904 :=
  @P1_7_1_3.block_append 5411 1163 1675 1803 128 128 256 103353800864 150031739040 253385539904 cost_5411_1163_block4 cost_5411_1163_block5 rfl rfl rfl

private theorem cost_5411_1163_join0_6 : P1_7_1_3.blockEstimate 5411 1163 1931 256 = 466953421120 :=
  @P1_7_1_3.block_append 5411 1163 1931 2059 128 128 256 203625035936 263328385184 466953421120 cost_5411_1163_block6 cost_5411_1163_block7 rfl rfl rfl

private theorem cost_5411_1163_join0_8 : P1_7_1_3.blockEstimate 5411 1163 2187 256 = 725069924933 :=
  @P1_7_1_3.block_append 5411 1163 2187 2315 128 128 256 328336480416 396733444517 725069924933 cost_5411_1163_block8 cost_5411_1163_block9 rfl rfl rfl

private theorem cost_5411_1163_join0_10 : P1_7_1_3.blockEstimate 5411 1163 2443 256 = 984966221568 :=
  @P1_7_1_3.block_append 5411 1163 2443 2571 128 128 256 462193633152 522772588416 984966221568 cost_5411_1163_block10 cost_5411_1163_block11 rfl rfl rfl

private theorem cost_5411_1163_join0_12 : P1_7_1_3.blockEstimate 5411 1163 2699 256 = 1207753363200 :=
  @P1_7_1_3.block_append 5411 1163 2699 2827 128 128 256 578469373824 629283989376 1207753363200 cost_5411_1163_block12 cost_5411_1163_block13 rfl rfl rfl

private theorem cost_5411_1163_join0_14 : P1_7_1_3.blockEstimate 5411 1163 2955 256 = 1391483145984 :=
  @P1_7_1_3.block_append 5411 1163 2955 3083 128 128 256 675216435072 716266710912 1391483145984 cost_5411_1163_block14 cost_5411_1163_block15 rfl rfl rfl

private theorem cost_5411_1163_join0_16 : P1_7_1_3.blockEstimate 5411 1163 3211 256 = 1536155569920 :=
  @P1_7_1_3.block_append 5411 1163 3211 3339 128 128 256 752434816896 783720753024 1536155569920 cost_5411_1163_block16 cost_5411_1163_block17 rfl rfl rfl

private theorem cost_5411_1163_join0_18 : P1_7_1_3.blockEstimate 5411 1163 3467 256 = 1641770635008 :=
  @P1_7_1_3.block_append 5411 1163 3467 3595 128 128 256 810124519296 831646115712 1641770635008 cost_5411_1163_block18 cost_5411_1163_block19 rfl rfl rfl

private theorem cost_5411_1163_join0_20 : P1_7_1_3.blockEstimate 5411 1163 3723 256 = 1708328341248 :=
  @P1_7_1_3.block_append 5411 1163 3723 3851 128 128 256 848285542272 860042798976 1708328341248 cost_5411_1163_block20 cost_5411_1163_block21 rfl rfl rfl

private theorem cost_5411_1163_join0_22 : P1_7_1_3.blockEstimate 5411 1163 3979 256 = 1735828688640 :=
  @P1_7_1_3.block_append 5411 1163 3979 4107 128 128 256 866917885824 868910802816 1735828688640 cost_5411_1163_block22 cost_5411_1163_block23 rfl rfl rfl

private theorem cost_5411_1163_join0_24 : P1_7_1_3.blockEstimate 5411 1163 4235 256 = 1724271677184 :=
  @P1_7_1_3.block_append 5411 1163 4235 4363 128 128 256 866021549952 858250127232 1724271677184 cost_5411_1163_block24 cost_5411_1163_block25 rfl rfl rfl

private theorem cost_5411_1163_join0_26 : P1_7_1_3.blockEstimate 5411 1163 4491 256 = 1673657306880 :=
  @P1_7_1_3.block_append 5411 1163 4491 4619 128 128 256 845596534656 828060772224 1673657306880 cost_5411_1163_block26 cost_5411_1163_block27 rfl rfl rfl

private theorem cost_5411_1163_join0_28 : P1_7_1_3.blockEstimate 5411 1163 4747 256 = 1583985577728 :=
  @P1_7_1_3.block_append 5411 1163 4747 4875 128 128 256 805642839936 778342737792 1583985577728 cost_5411_1163_block28 cost_5411_1163_block29 rfl rfl rfl

private theorem cost_5411_1163_join0_30 : P1_7_1_3.blockEstimate 5411 1163 5003 256 = 1455256489728 :=
  @P1_7_1_3.block_append 5411 1163 5003 5131 128 128 256 746160465792 709096023936 1455256489728 cost_5411_1163_block30 cost_5411_1163_block31 rfl rfl rfl

private theorem cost_5411_1163_join0_32 : P1_7_1_3.blockEstimate 5411 1163 5259 256 = 1287774426115 :=
  @P1_7_1_3.block_append 5411 1163 5259 5387 128 128 256 667149412224 620625013891 1287774426115 cost_5411_1163_block32 cost_5411_1163_block33 rfl rfl rfl

private theorem cost_5411_1163_join0_34 : P1_7_1_3.blockEstimate 5411 1163 5515 256 = 1093914928377 :=
  @P1_7_1_3.block_append 5411 1163 5515 5643 128 128 256 571805979621 522108948756 1093914928377 cost_5411_1163_block34 cost_5411_1163_block35 rfl rfl rfl

private theorem cost_5411_1163_join0_36 : P1_7_1_3.blockEstimate 5411 1163 5771 256 = 894424680043 :=
  @P1_7_1_3.block_append 5411 1163 5771 5899 128 128 256 472100979842 422323700201 894424680043 cost_5411_1163_block36 cost_5411_1163_block37 rfl rfl rfl

private theorem cost_5411_1163_join0_38 : P1_7_1_3.blockEstimate 5411 1163 6027 256 = 698813622182 :=
  @P1_7_1_3.block_append 5411 1163 6027 6155 128 128 256 373296598412 325517023770 698813622182 cost_5411_1163_block38 cost_5411_1163_block39 rfl rfl rfl

private theorem cost_5411_1163_join0_40 : P1_7_1_3.blockEstimate 5411 1163 6283 256 = 515039343961 :=
  @P1_7_1_3.block_append 5411 1163 6283 6411 128 128 256 279460186307 235579157654 515039343961 cost_5411_1163_block40 cost_5411_1163_block41 rfl rfl rfl

private theorem cost_5411_1163_join0_42 : P1_7_1_3.blockEstimate 5411 1163 6539 256 = 349651346257 :=
  @P1_7_1_3.block_append 5411 1163 6539 6667 128 128 256 194147209537 155504136720 349651346257 cost_5411_1163_block42 cost_5411_1163_block43 rfl rfl rfl

private theorem cost_5411_1163_join0_44 : P1_7_1_3.blockEstimate 5411 1163 6795 256 = 210028128288 :=
  @P1_7_1_3.block_append 5411 1163 6795 6923 128 128 256 120528715280 89499413008 210028128288 cost_5411_1163_block44 cost_5411_1163_block45 rfl rfl rfl

private theorem cost_5411_1163_join0_46 : P1_7_1_3.blockEstimate 5411 1163 7051 256 = 102953687072 :=
  @P1_7_1_3.block_append 5411 1163 7051 7179 128 128 256 62667888144 40285798928 102953687072 cost_5411_1163_block46 cost_5411_1163_block47 rfl rfl rfl

private theorem cost_5411_1163_join0_48 : P1_7_1_3.blockEstimate 5411 1163 7307 256 = 32481364000 :=
  @P1_7_1_3.block_append 5411 1163 7307 7435 128 128 256 22604803600 9876560400 32481364000 cost_5411_1163_block48 cost_5411_1163_block49 rfl rfl rfl

private theorem cost_5411_1163_join0_50 : P1_7_1_3.blockEstimate 5411 1163 7563 174 = 2400828782 :=
  @P1_7_1_3.block_append 5411 1163 7563 7691 128 46 174 2352727568 48101214 2400828782 cost_5411_1163_block50 cost_5411_1163_block51 rfl rfl rfl

private theorem cost_5411_1163_join1_0 : P1_7_1_3.blockEstimate 5411 1163 1163 512 = 113128718976 :=
  @P1_7_1_3.block_append 5411 1163 1163 1419 256 256 512 14766965056 98361753920 113128718976 cost_5411_1163_join0_0 cost_5411_1163_join0_2 rfl rfl rfl

private theorem cost_5411_1163_join1_2 : P1_7_1_3.blockEstimate 5411 1163 1675 512 = 720338961024 :=
  @P1_7_1_3.block_append 5411 1163 1675 1931 256 256 512 253385539904 466953421120 720338961024 cost_5411_1163_join0_4 cost_5411_1163_join0_6 rfl rfl rfl

private theorem cost_5411_1163_join1_4 : P1_7_1_3.blockEstimate 5411 1163 2187 512 = 1710036146501 :=
  @P1_7_1_3.block_append 5411 1163 2187 2443 256 256 512 725069924933 984966221568 1710036146501 cost_5411_1163_join0_8 cost_5411_1163_join0_10 rfl rfl rfl

private theorem cost_5411_1163_join1_6 : P1_7_1_3.blockEstimate 5411 1163 2699 512 = 2599236509184 :=
  @P1_7_1_3.block_append 5411 1163 2699 2955 256 256 512 1207753363200 1391483145984 2599236509184 cost_5411_1163_join0_12 cost_5411_1163_join0_14 rfl rfl rfl

private theorem cost_5411_1163_join1_8 : P1_7_1_3.blockEstimate 5411 1163 3211 512 = 3177926204928 :=
  @P1_7_1_3.block_append 5411 1163 3211 3467 256 256 512 1536155569920 1641770635008 3177926204928 cost_5411_1163_join0_16 cost_5411_1163_join0_18 rfl rfl rfl

private theorem cost_5411_1163_join1_10 : P1_7_1_3.blockEstimate 5411 1163 3723 512 = 3444157029888 :=
  @P1_7_1_3.block_append 5411 1163 3723 3979 256 256 512 1708328341248 1735828688640 3444157029888 cost_5411_1163_join0_20 cost_5411_1163_join0_22 rfl rfl rfl

private theorem cost_5411_1163_join1_12 : P1_7_1_3.blockEstimate 5411 1163 4235 512 = 3397928984064 :=
  @P1_7_1_3.block_append 5411 1163 4235 4491 256 256 512 1724271677184 1673657306880 3397928984064 cost_5411_1163_join0_24 cost_5411_1163_join0_26 rfl rfl rfl

private theorem cost_5411_1163_join1_14 : P1_7_1_3.blockEstimate 5411 1163 4747 512 = 3039242067456 :=
  @P1_7_1_3.block_append 5411 1163 4747 5003 256 256 512 1583985577728 1455256489728 3039242067456 cost_5411_1163_join0_28 cost_5411_1163_join0_30 rfl rfl rfl

private theorem cost_5411_1163_join1_16 : P1_7_1_3.blockEstimate 5411 1163 5259 512 = 2381689354492 :=
  @P1_7_1_3.block_append 5411 1163 5259 5515 256 256 512 1287774426115 1093914928377 2381689354492 cost_5411_1163_join0_32 cost_5411_1163_join0_34 rfl rfl rfl

private theorem cost_5411_1163_join1_18 : P1_7_1_3.blockEstimate 5411 1163 5771 512 = 1593238302225 :=
  @P1_7_1_3.block_append 5411 1163 5771 6027 256 256 512 894424680043 698813622182 1593238302225 cost_5411_1163_join0_36 cost_5411_1163_join0_38 rfl rfl rfl

private theorem cost_5411_1163_join1_20 : P1_7_1_3.blockEstimate 5411 1163 6283 512 = 864690690218 :=
  @P1_7_1_3.block_append 5411 1163 6283 6539 256 256 512 515039343961 349651346257 864690690218 cost_5411_1163_join0_40 cost_5411_1163_join0_42 rfl rfl rfl

private theorem cost_5411_1163_join1_22 : P1_7_1_3.blockEstimate 5411 1163 6795 512 = 312981815360 :=
  @P1_7_1_3.block_append 5411 1163 6795 7051 256 256 512 210028128288 102953687072 312981815360 cost_5411_1163_join0_44 cost_5411_1163_join0_46 rfl rfl rfl

private theorem cost_5411_1163_join1_24 : P1_7_1_3.blockEstimate 5411 1163 7307 430 = 34882192782 :=
  @P1_7_1_3.block_append 5411 1163 7307 7563 256 174 430 32481364000 2400828782 34882192782 cost_5411_1163_join0_48 cost_5411_1163_join0_50 rfl rfl rfl

private theorem cost_5411_1163_join2_0 : P1_7_1_3.blockEstimate 5411 1163 1163 1024 = 833467680000 :=
  @P1_7_1_3.block_append 5411 1163 1163 1675 512 512 1024 113128718976 720338961024 833467680000 cost_5411_1163_join1_0 cost_5411_1163_join1_2 rfl rfl rfl

private theorem cost_5411_1163_join2_2 : P1_7_1_3.blockEstimate 5411 1163 2187 1024 = 4309272655685 :=
  @P1_7_1_3.block_append 5411 1163 2187 2699 512 512 1024 1710036146501 2599236509184 4309272655685 cost_5411_1163_join1_4 cost_5411_1163_join1_6 rfl rfl rfl

private theorem cost_5411_1163_join2_4 : P1_7_1_3.blockEstimate 5411 1163 3211 1024 = 6622083234816 :=
  @P1_7_1_3.block_append 5411 1163 3211 3723 512 512 1024 3177926204928 3444157029888 6622083234816 cost_5411_1163_join1_8 cost_5411_1163_join1_10 rfl rfl rfl

private theorem cost_5411_1163_join2_6 : P1_7_1_3.blockEstimate 5411 1163 4235 1024 = 6437171051520 :=
  @P1_7_1_3.block_append 5411 1163 4235 4747 512 512 1024 3397928984064 3039242067456 6437171051520 cost_5411_1163_join1_12 cost_5411_1163_join1_14 rfl rfl rfl

private theorem cost_5411_1163_join2_8 : P1_7_1_3.blockEstimate 5411 1163 5259 1024 = 3974927656717 :=
  @P1_7_1_3.block_append 5411 1163 5259 5771 512 512 1024 2381689354492 1593238302225 3974927656717 cost_5411_1163_join1_16 cost_5411_1163_join1_18 rfl rfl rfl

private theorem cost_5411_1163_join2_10 : P1_7_1_3.blockEstimate 5411 1163 6283 1024 = 1177672505578 :=
  @P1_7_1_3.block_append 5411 1163 6283 6795 512 512 1024 864690690218 312981815360 1177672505578 cost_5411_1163_join1_20 cost_5411_1163_join1_22 rfl rfl rfl

private theorem cost_5411_1163_join3_0 : P1_7_1_3.blockEstimate 5411 1163 1163 2048 = 5142740335685 :=
  @P1_7_1_3.block_append 5411 1163 1163 2187 1024 1024 2048 833467680000 4309272655685 5142740335685 cost_5411_1163_join2_0 cost_5411_1163_join2_2 rfl rfl rfl

private theorem cost_5411_1163_join3_2 : P1_7_1_3.blockEstimate 5411 1163 3211 2048 = 13059254286336 :=
  @P1_7_1_3.block_append 5411 1163 3211 4235 1024 1024 2048 6622083234816 6437171051520 13059254286336 cost_5411_1163_join2_4 cost_5411_1163_join2_6 rfl rfl rfl

private theorem cost_5411_1163_join3_4 : P1_7_1_3.blockEstimate 5411 1163 5259 2048 = 5152600162295 :=
  @P1_7_1_3.block_append 5411 1163 5259 6283 1024 1024 2048 3974927656717 1177672505578 5152600162295 cost_5411_1163_join2_8 cost_5411_1163_join2_10 rfl rfl rfl

private theorem cost_5411_1163_join4_0 : P1_7_1_3.blockEstimate 5411 1163 1163 4096 = 18201994622021 :=
  @P1_7_1_3.block_append 5411 1163 1163 3211 2048 2048 4096 5142740335685 13059254286336 18201994622021 cost_5411_1163_join3_0 cost_5411_1163_join3_2 rfl rfl rfl

private theorem cost_5411_1163_join4_2 : P1_7_1_3.blockEstimate 5411 1163 5259 2478 = 5187482355077 :=
  @P1_7_1_3.block_append 5411 1163 5259 7307 2048 430 2478 5152600162295 34882192782 5187482355077 cost_5411_1163_join3_4 cost_5411_1163_join1_24 rfl rfl rfl

private theorem cost_5411_1163_join5_0 : P1_7_1_3.blockEstimate 5411 1163 1163 6574 = 23389476977098 :=
  @P1_7_1_3.block_append 5411 1163 1163 5259 4096 2478 6574 18201994622021 5187482355077 23389476977098 cost_5411_1163_join4_0 cost_5411_1163_join4_2 rfl rfl rfl

private theorem cost_5411_1163_total : P1_7_1_3.momentEstimate 5411 1163 = 23389476977098 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 5411 + 1163 = 6574 by decide]
  exact cost_5411_1163_join5_0

theorem moment5411_1163 : P1_7_1.groupedPoleMoment 5411 1163 ≤ 23389476977098 :=
  (P1_7_1_3.grouped_bound 5411 1163).trans_eq cost_5411_1163_total
private theorem cost_5474_1177_block0 : P1_7_1_3.blockEstimate 5474 1177 1177 128 = 1924301600 := by decide +kernel

private theorem cost_5474_1177_block1 : P1_7_1_3.blockEstimate 5474 1177 1305 128 = 13020893984 := by decide +kernel

private theorem cost_5474_1177_block2 : P1_7_1_3.blockEstimate 5474 1177 1433 128 = 34386191136 := by decide +kernel

private theorem cost_5474_1177_block3 : P1_7_1_3.blockEstimate 5474 1177 1561 128 = 65214886688 := by decide +kernel

private theorem cost_5474_1177_block4 : P1_7_1_3.blockEstimate 5474 1177 1689 128 = 104701674272 := by decide +kernel

private theorem cost_5474_1177_block5 : P1_7_1_3.blockEstimate 5474 1177 1817 128 = 152041247520 := by decide +kernel

private theorem cost_5474_1177_block6 : P1_7_1_3.blockEstimate 5474 1177 1945 128 = 206428300064 := by decide +kernel

private theorem cost_5474_1177_block7 : P1_7_1_3.blockEstimate 5474 1177 2073 128 = 267057525536 := by decide +kernel

private theorem cost_5474_1177_block8 : P1_7_1_3.blockEstimate 5474 1177 2201 128 = 333123617568 := by decide +kernel

private theorem cost_5474_1177_block9 : P1_7_1_3.blockEstimate 5474 1177 2329 128 = 403052745386 := by decide +kernel

private theorem cost_5474_1177_block10 : P1_7_1_3.blockEstimate 5474 1177 2457 128 = 470641006016 := by decide +kernel

private theorem cost_5474_1177_block11 : P1_7_1_3.blockEstimate 5474 1177 2585 128 = 533299598784 := by decide +kernel

private theorem cost_5474_1177_block12 : P1_7_1_3.blockEstimate 5474 1177 2713 128 = 591017301440 := by decide +kernel

private theorem cost_5474_1177_block13 : P1_7_1_3.blockEstimate 5474 1177 2841 128 = 643794113984 := by decide +kernel

private theorem cost_5474_1177_block14 : P1_7_1_3.blockEstimate 5474 1177 2969 128 = 691630036416 := by decide +kernel

private theorem cost_5474_1177_block15 : P1_7_1_3.blockEstimate 5474 1177 3097 128 = 734525068736 := by decide +kernel

private theorem cost_5474_1177_block16 : P1_7_1_3.blockEstimate 5474 1177 3225 128 = 772479210944 := by decide +kernel

private theorem cost_5474_1177_block17 : P1_7_1_3.blockEstimate 5474 1177 3353 128 = 805492463040 := by decide +kernel

private theorem cost_5474_1177_block18 : P1_7_1_3.blockEstimate 5474 1177 3481 128 = 833564825024 := by decide +kernel

private theorem cost_5474_1177_block19 : P1_7_1_3.blockEstimate 5474 1177 3609 128 = 856696296896 := by decide +kernel

private theorem cost_5474_1177_block20 : P1_7_1_3.blockEstimate 5474 1177 3737 128 = 874886878656 := by decide +kernel

private theorem cost_5474_1177_block21 : P1_7_1_3.blockEstimate 5474 1177 3865 128 = 888136570304 := by decide +kernel

private theorem cost_5474_1177_block22 : P1_7_1_3.blockEstimate 5474 1177 3993 128 = 896445371840 := by decide +kernel

private theorem cost_5474_1177_block23 : P1_7_1_3.blockEstimate 5474 1177 4121 128 = 899813283264 := by decide +kernel

private theorem cost_5474_1177_block24 : P1_7_1_3.blockEstimate 5474 1177 4249 128 = 898240304576 := by decide +kernel

private theorem cost_5474_1177_block25 : P1_7_1_3.blockEstimate 5474 1177 4377 128 = 891726435776 := by decide +kernel

private theorem cost_5474_1177_block26 : P1_7_1_3.blockEstimate 5474 1177 4505 128 = 880271676864 := by decide +kernel

private theorem cost_5474_1177_block27 : P1_7_1_3.blockEstimate 5474 1177 4633 128 = 863876027840 := by decide +kernel

private theorem cost_5474_1177_block28 : P1_7_1_3.blockEstimate 5474 1177 4761 128 = 842539488704 := by decide +kernel

private theorem cost_5474_1177_block29 : P1_7_1_3.blockEstimate 5474 1177 4889 128 = 816262059456 := by decide +kernel

private theorem cost_5474_1177_block30 : P1_7_1_3.blockEstimate 5474 1177 5017 128 = 785043740096 := by decide +kernel

private theorem cost_5474_1177_block31 : P1_7_1_3.blockEstimate 5474 1177 5145 128 = 748884530624 := by decide +kernel

private theorem cost_5474_1177_block32 : P1_7_1_3.blockEstimate 5474 1177 5273 128 = 707784431040 := by decide +kernel

private theorem cost_5474_1177_block33 : P1_7_1_3.blockEstimate 5474 1177 5401 128 = 661788738722 := by decide +kernel

private theorem cost_5474_1177_block34 : P1_7_1_3.blockEstimate 5474 1177 5529 128 = 612427596682 := by decide +kernel

private theorem cost_5474_1177_block35 : P1_7_1_3.blockEstimate 5474 1177 5657 128 = 561851777073 := by decide +kernel

private theorem cost_5474_1177_block36 : P1_7_1_3.blockEstimate 5474 1177 5785 128 = 510730323398 := by decide +kernel

private theorem cost_5474_1177_block37 : P1_7_1_3.blockEstimate 5474 1177 5913 128 = 459613977541 := by decide +kernel

private theorem cost_5474_1177_block38 : P1_7_1_3.blockEstimate 5474 1177 6041 128 = 409031606502 := by decide +kernel

private theorem cost_5474_1177_block39 : P1_7_1_3.blockEstimate 5474 1177 6169 128 = 359490201336 := by decide +kernel

private theorem cost_5474_1177_block40 : P1_7_1_3.blockEstimate 5474 1177 6297 128 = 311474877225 := by decide +kernel

private theorem cost_5474_1177_block41 : P1_7_1_3.blockEstimate 5474 1177 6425 128 = 265448872943 := by decide +kernel

private theorem cost_5474_1177_block42 : P1_7_1_3.blockEstimate 5474 1177 6553 128 = 221834345501 := by decide +kernel

private theorem cost_5474_1177_block43 : P1_7_1_3.blockEstimate 5474 1177 6681 128 = 180713685056 := by decide +kernel

private theorem cost_5474_1177_block44 : P1_7_1_3.blockEstimate 5474 1177 6809 128 = 142958979136 := by decide +kernel

private theorem cost_5474_1177_block45 : P1_7_1_3.blockEstimate 5474 1177 6937 128 = 109065064512 := by decide +kernel

private theorem cost_5474_1177_block46 : P1_7_1_3.blockEstimate 5474 1177 7065 128 = 79283599424 := by decide +kernel

private theorem cost_5474_1177_block47 : P1_7_1_3.blockEstimate 5474 1177 7193 128 = 53866242112 := by decide +kernel

private theorem cost_5474_1177_block48 : P1_7_1_3.blockEstimate 5474 1177 7321 128 = 33064650816 := by decide +kernel

private theorem cost_5474_1177_block49 : P1_7_1_3.blockEstimate 5474 1177 7449 128 = 17130483776 := by decide +kernel

private theorem cost_5474_1177_block50 : P1_7_1_3.blockEstimate 5474 1177 7577 128 = 6315399232 := by decide +kernel

private theorem cost_5474_1177_block51 : P1_7_1_3.blockEstimate 5474 1177 7705 123 = 871038992 := by decide +kernel

private theorem cost_5474_1177_join0_0 : P1_7_1_3.blockEstimate 5474 1177 1177 256 = 14945195584 :=
  @P1_7_1_3.block_append 5474 1177 1177 1305 128 128 256 1924301600 13020893984 14945195584 cost_5474_1177_block0 cost_5474_1177_block1 rfl rfl rfl

private theorem cost_5474_1177_join0_2 : P1_7_1_3.blockEstimate 5474 1177 1433 256 = 99601077824 :=
  @P1_7_1_3.block_append 5474 1177 1433 1561 128 128 256 34386191136 65214886688 99601077824 cost_5474_1177_block2 cost_5474_1177_block3 rfl rfl rfl

private theorem cost_5474_1177_join0_4 : P1_7_1_3.blockEstimate 5474 1177 1689 256 = 256742921792 :=
  @P1_7_1_3.block_append 5474 1177 1689 1817 128 128 256 104701674272 152041247520 256742921792 cost_5474_1177_block4 cost_5474_1177_block5 rfl rfl rfl

private theorem cost_5474_1177_join0_6 : P1_7_1_3.blockEstimate 5474 1177 1945 256 = 473485825600 :=
  @P1_7_1_3.block_append 5474 1177 1945 2073 128 128 256 206428300064 267057525536 473485825600 cost_5474_1177_block6 cost_5474_1177_block7 rfl rfl rfl

private theorem cost_5474_1177_join0_8 : P1_7_1_3.blockEstimate 5474 1177 2201 256 = 736176362954 :=
  @P1_7_1_3.block_append 5474 1177 2201 2329 128 128 256 333123617568 403052745386 736176362954 cost_5474_1177_block8 cost_5474_1177_block9 rfl rfl rfl

private theorem cost_5474_1177_join0_10 : P1_7_1_3.blockEstimate 5474 1177 2457 256 = 1003940604800 :=
  @P1_7_1_3.block_append 5474 1177 2457 2585 128 128 256 470641006016 533299598784 1003940604800 cost_5474_1177_block10 cost_5474_1177_block11 rfl rfl rfl

private theorem cost_5474_1177_join0_12 : P1_7_1_3.blockEstimate 5474 1177 2713 256 = 1234811415424 :=
  @P1_7_1_3.block_append 5474 1177 2713 2841 128 128 256 591017301440 643794113984 1234811415424 cost_5474_1177_block12 cost_5474_1177_block13 rfl rfl rfl

private theorem cost_5474_1177_join0_14 : P1_7_1_3.blockEstimate 5474 1177 2969 256 = 1426155105152 :=
  @P1_7_1_3.block_append 5474 1177 2969 3097 128 128 256 691630036416 734525068736 1426155105152 cost_5474_1177_block14 cost_5474_1177_block15 rfl rfl rfl

private theorem cost_5474_1177_join0_16 : P1_7_1_3.blockEstimate 5474 1177 3225 256 = 1577971673984 :=
  @P1_7_1_3.block_append 5474 1177 3225 3353 128 128 256 772479210944 805492463040 1577971673984 cost_5474_1177_block16 cost_5474_1177_block17 rfl rfl rfl

private theorem cost_5474_1177_join0_18 : P1_7_1_3.blockEstimate 5474 1177 3481 256 = 1690261121920 :=
  @P1_7_1_3.block_append 5474 1177 3481 3609 128 128 256 833564825024 856696296896 1690261121920 cost_5474_1177_block18 cost_5474_1177_block19 rfl rfl rfl

private theorem cost_5474_1177_join0_20 : P1_7_1_3.blockEstimate 5474 1177 3737 256 = 1763023448960 :=
  @P1_7_1_3.block_append 5474 1177 3737 3865 128 128 256 874886878656 888136570304 1763023448960 cost_5474_1177_block20 cost_5474_1177_block21 rfl rfl rfl

private theorem cost_5474_1177_join0_22 : P1_7_1_3.blockEstimate 5474 1177 3993 256 = 1796258655104 :=
  @P1_7_1_3.block_append 5474 1177 3993 4121 128 128 256 896445371840 899813283264 1796258655104 cost_5474_1177_block22 cost_5474_1177_block23 rfl rfl rfl

private theorem cost_5474_1177_join0_24 : P1_7_1_3.blockEstimate 5474 1177 4249 256 = 1789966740352 :=
  @P1_7_1_3.block_append 5474 1177 4249 4377 128 128 256 898240304576 891726435776 1789966740352 cost_5474_1177_block24 cost_5474_1177_block25 rfl rfl rfl

private theorem cost_5474_1177_join0_26 : P1_7_1_3.blockEstimate 5474 1177 4505 256 = 1744147704704 :=
  @P1_7_1_3.block_append 5474 1177 4505 4633 128 128 256 880271676864 863876027840 1744147704704 cost_5474_1177_block26 cost_5474_1177_block27 rfl rfl rfl

private theorem cost_5474_1177_join0_28 : P1_7_1_3.blockEstimate 5474 1177 4761 256 = 1658801548160 :=
  @P1_7_1_3.block_append 5474 1177 4761 4889 128 128 256 842539488704 816262059456 1658801548160 cost_5474_1177_block28 cost_5474_1177_block29 rfl rfl rfl

private theorem cost_5474_1177_join0_30 : P1_7_1_3.blockEstimate 5474 1177 5017 256 = 1533928270720 :=
  @P1_7_1_3.block_append 5474 1177 5017 5145 128 128 256 785043740096 748884530624 1533928270720 cost_5474_1177_block30 cost_5474_1177_block31 rfl rfl rfl

private theorem cost_5474_1177_join0_32 : P1_7_1_3.blockEstimate 5474 1177 5273 256 = 1369573169762 :=
  @P1_7_1_3.block_append 5474 1177 5273 5401 128 128 256 707784431040 661788738722 1369573169762 cost_5474_1177_block32 cost_5474_1177_block33 rfl rfl rfl

private theorem cost_5474_1177_join0_34 : P1_7_1_3.blockEstimate 5474 1177 5529 256 = 1174279373755 :=
  @P1_7_1_3.block_append 5474 1177 5529 5657 128 128 256 612427596682 561851777073 1174279373755 cost_5474_1177_block34 cost_5474_1177_block35 rfl rfl rfl

private theorem cost_5474_1177_join0_36 : P1_7_1_3.blockEstimate 5474 1177 5785 256 = 970344300939 :=
  @P1_7_1_3.block_append 5474 1177 5785 5913 128 128 256 510730323398 459613977541 970344300939 cost_5474_1177_block36 cost_5474_1177_block37 rfl rfl rfl

private theorem cost_5474_1177_join0_38 : P1_7_1_3.blockEstimate 5474 1177 6041 256 = 768521807838 :=
  @P1_7_1_3.block_append 5474 1177 6041 6169 128 128 256 409031606502 359490201336 768521807838 cost_5474_1177_block38 cost_5474_1177_block39 rfl rfl rfl

private theorem cost_5474_1177_join0_40 : P1_7_1_3.blockEstimate 5474 1177 6297 256 = 576923750168 :=
  @P1_7_1_3.block_append 5474 1177 6297 6425 128 128 256 311474877225 265448872943 576923750168 cost_5474_1177_block40 cost_5474_1177_block41 rfl rfl rfl

private theorem cost_5474_1177_join0_42 : P1_7_1_3.blockEstimate 5474 1177 6553 256 = 402548030557 :=
  @P1_7_1_3.block_append 5474 1177 6553 6681 128 128 256 221834345501 180713685056 402548030557 cost_5474_1177_block42 cost_5474_1177_block43 rfl rfl rfl

private theorem cost_5474_1177_join0_44 : P1_7_1_3.blockEstimate 5474 1177 6809 256 = 252024043648 :=
  @P1_7_1_3.block_append 5474 1177 6809 6937 128 128 256 142958979136 109065064512 252024043648 cost_5474_1177_block44 cost_5474_1177_block45 rfl rfl rfl

private theorem cost_5474_1177_join0_46 : P1_7_1_3.blockEstimate 5474 1177 7065 256 = 133149841536 :=
  @P1_7_1_3.block_append 5474 1177 7065 7193 128 128 256 79283599424 53866242112 133149841536 cost_5474_1177_block46 cost_5474_1177_block47 rfl rfl rfl

private theorem cost_5474_1177_join0_48 : P1_7_1_3.blockEstimate 5474 1177 7321 256 = 50195134592 :=
  @P1_7_1_3.block_append 5474 1177 7321 7449 128 128 256 33064650816 17130483776 50195134592 cost_5474_1177_block48 cost_5474_1177_block49 rfl rfl rfl

private theorem cost_5474_1177_join0_50 : P1_7_1_3.blockEstimate 5474 1177 7577 251 = 7186438224 :=
  @P1_7_1_3.block_append 5474 1177 7577 7705 128 123 251 6315399232 871038992 7186438224 cost_5474_1177_block50 cost_5474_1177_block51 rfl rfl rfl

private theorem cost_5474_1177_join1_0 : P1_7_1_3.blockEstimate 5474 1177 1177 512 = 114546273408 :=
  @P1_7_1_3.block_append 5474 1177 1177 1433 256 256 512 14945195584 99601077824 114546273408 cost_5474_1177_join0_0 cost_5474_1177_join0_2 rfl rfl rfl

private theorem cost_5474_1177_join1_2 : P1_7_1_3.blockEstimate 5474 1177 1689 512 = 730228747392 :=
  @P1_7_1_3.block_append 5474 1177 1689 1945 256 256 512 256742921792 473485825600 730228747392 cost_5474_1177_join0_4 cost_5474_1177_join0_6 rfl rfl rfl

private theorem cost_5474_1177_join1_4 : P1_7_1_3.blockEstimate 5474 1177 2201 512 = 1740116967754 :=
  @P1_7_1_3.block_append 5474 1177 2201 2457 256 256 512 736176362954 1003940604800 1740116967754 cost_5474_1177_join0_8 cost_5474_1177_join0_10 rfl rfl rfl

private theorem cost_5474_1177_join1_6 : P1_7_1_3.blockEstimate 5474 1177 2713 512 = 2660966520576 :=
  @P1_7_1_3.block_append 5474 1177 2713 2969 256 256 512 1234811415424 1426155105152 2660966520576 cost_5474_1177_join0_12 cost_5474_1177_join0_14 rfl rfl rfl

private theorem cost_5474_1177_join1_8 : P1_7_1_3.blockEstimate 5474 1177 3225 512 = 3268232795904 :=
  @P1_7_1_3.block_append 5474 1177 3225 3481 256 256 512 1577971673984 1690261121920 3268232795904 cost_5474_1177_join0_16 cost_5474_1177_join0_18 rfl rfl rfl

private theorem cost_5474_1177_join1_10 : P1_7_1_3.blockEstimate 5474 1177 3737 512 = 3559282104064 :=
  @P1_7_1_3.block_append 5474 1177 3737 3993 256 256 512 1763023448960 1796258655104 3559282104064 cost_5474_1177_join0_20 cost_5474_1177_join0_22 rfl rfl rfl

private theorem cost_5474_1177_join1_12 : P1_7_1_3.blockEstimate 5474 1177 4249 512 = 3534114445056 :=
  @P1_7_1_3.block_append 5474 1177 4249 4505 256 256 512 1789966740352 1744147704704 3534114445056 cost_5474_1177_join0_24 cost_5474_1177_join0_26 rfl rfl rfl

private theorem cost_5474_1177_join1_14 : P1_7_1_3.blockEstimate 5474 1177 4761 512 = 3192729818880 :=
  @P1_7_1_3.block_append 5474 1177 4761 5017 256 256 512 1658801548160 1533928270720 3192729818880 cost_5474_1177_join0_28 cost_5474_1177_join0_30 rfl rfl rfl

private theorem cost_5474_1177_join1_16 : P1_7_1_3.blockEstimate 5474 1177 5273 512 = 2543852543517 :=
  @P1_7_1_3.block_append 5474 1177 5273 5529 256 256 512 1369573169762 1174279373755 2543852543517 cost_5474_1177_join0_32 cost_5474_1177_join0_34 rfl rfl rfl

private theorem cost_5474_1177_join1_18 : P1_7_1_3.blockEstimate 5474 1177 5785 512 = 1738866108777 :=
  @P1_7_1_3.block_append 5474 1177 5785 6041 256 256 512 970344300939 768521807838 1738866108777 cost_5474_1177_join0_36 cost_5474_1177_join0_38 rfl rfl rfl

private theorem cost_5474_1177_join1_20 : P1_7_1_3.blockEstimate 5474 1177 6297 512 = 979471780725 :=
  @P1_7_1_3.block_append 5474 1177 6297 6553 256 256 512 576923750168 402548030557 979471780725 cost_5474_1177_join0_40 cost_5474_1177_join0_42 rfl rfl rfl

private theorem cost_5474_1177_join1_22 : P1_7_1_3.blockEstimate 5474 1177 6809 512 = 385173885184 :=
  @P1_7_1_3.block_append 5474 1177 6809 7065 256 256 512 252024043648 133149841536 385173885184 cost_5474_1177_join0_44 cost_5474_1177_join0_46 rfl rfl rfl

private theorem cost_5474_1177_join1_24 : P1_7_1_3.blockEstimate 5474 1177 7321 507 = 57381572816 :=
  @P1_7_1_3.block_append 5474 1177 7321 7577 256 251 507 50195134592 7186438224 57381572816 cost_5474_1177_join0_48 cost_5474_1177_join0_50 rfl rfl rfl

private theorem cost_5474_1177_join2_0 : P1_7_1_3.blockEstimate 5474 1177 1177 1024 = 844775020800 :=
  @P1_7_1_3.block_append 5474 1177 1177 1689 512 512 1024 114546273408 730228747392 844775020800 cost_5474_1177_join1_0 cost_5474_1177_join1_2 rfl rfl rfl

private theorem cost_5474_1177_join2_2 : P1_7_1_3.blockEstimate 5474 1177 2201 1024 = 4401083488330 :=
  @P1_7_1_3.block_append 5474 1177 2201 2713 512 512 1024 1740116967754 2660966520576 4401083488330 cost_5474_1177_join1_4 cost_5474_1177_join1_6 rfl rfl rfl

private theorem cost_5474_1177_join2_4 : P1_7_1_3.blockEstimate 5474 1177 3225 1024 = 6827514899968 :=
  @P1_7_1_3.block_append 5474 1177 3225 3737 512 512 1024 3268232795904 3559282104064 6827514899968 cost_5474_1177_join1_8 cost_5474_1177_join1_10 rfl rfl rfl

private theorem cost_5474_1177_join2_6 : P1_7_1_3.blockEstimate 5474 1177 4249 1024 = 6726844263936 :=
  @P1_7_1_3.block_append 5474 1177 4249 4761 512 512 1024 3534114445056 3192729818880 6726844263936 cost_5474_1177_join1_12 cost_5474_1177_join1_14 rfl rfl rfl

private theorem cost_5474_1177_join2_8 : P1_7_1_3.blockEstimate 5474 1177 5273 1024 = 4282718652294 :=
  @P1_7_1_3.block_append 5474 1177 5273 5785 512 512 1024 2543852543517 1738866108777 4282718652294 cost_5474_1177_join1_16 cost_5474_1177_join1_18 rfl rfl rfl

private theorem cost_5474_1177_join2_10 : P1_7_1_3.blockEstimate 5474 1177 6297 1024 = 1364645665909 :=
  @P1_7_1_3.block_append 5474 1177 6297 6809 512 512 1024 979471780725 385173885184 1364645665909 cost_5474_1177_join1_20 cost_5474_1177_join1_22 rfl rfl rfl

private theorem cost_5474_1177_join3_0 : P1_7_1_3.blockEstimate 5474 1177 1177 2048 = 5245858509130 :=
  @P1_7_1_3.block_append 5474 1177 1177 2201 1024 1024 2048 844775020800 4401083488330 5245858509130 cost_5474_1177_join2_0 cost_5474_1177_join2_2 rfl rfl rfl

private theorem cost_5474_1177_join3_2 : P1_7_1_3.blockEstimate 5474 1177 3225 2048 = 13554359163904 :=
  @P1_7_1_3.block_append 5474 1177 3225 4249 1024 1024 2048 6827514899968 6726844263936 13554359163904 cost_5474_1177_join2_4 cost_5474_1177_join2_6 rfl rfl rfl

private theorem cost_5474_1177_join3_4 : P1_7_1_3.blockEstimate 5474 1177 5273 2048 = 5647364318203 :=
  @P1_7_1_3.block_append 5474 1177 5273 6297 1024 1024 2048 4282718652294 1364645665909 5647364318203 cost_5474_1177_join2_8 cost_5474_1177_join2_10 rfl rfl rfl

private theorem cost_5474_1177_join4_0 : P1_7_1_3.blockEstimate 5474 1177 1177 4096 = 18800217673034 :=
  @P1_7_1_3.block_append 5474 1177 1177 3225 2048 2048 4096 5245858509130 13554359163904 18800217673034 cost_5474_1177_join3_0 cost_5474_1177_join3_2 rfl rfl rfl

private theorem cost_5474_1177_join4_2 : P1_7_1_3.blockEstimate 5474 1177 5273 2555 = 5704745891019 :=
  @P1_7_1_3.block_append 5474 1177 5273 7321 2048 507 2555 5647364318203 57381572816 5704745891019 cost_5474_1177_join3_4 cost_5474_1177_join1_24 rfl rfl rfl

private theorem cost_5474_1177_join5_0 : P1_7_1_3.blockEstimate 5474 1177 1177 6651 = 24504963564053 :=
  @P1_7_1_3.block_append 5474 1177 1177 5273 4096 2555 6651 18800217673034 5704745891019 24504963564053 cost_5474_1177_join4_0 cost_5474_1177_join4_2 rfl rfl rfl

private theorem cost_5474_1177_total : P1_7_1_3.momentEstimate 5474 1177 = 24504963564053 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 5474 + 1177 = 6651 by decide]
  exact cost_5474_1177_join5_0

theorem moment5474_1177 : P1_7_1.groupedPoleMoment 5474 1177 ≤ 24504963564053 :=
  (P1_7_1_3.grouped_bound 5474 1177).trans_eq cost_5474_1177_total
private theorem cost_5652_1254_block0 : P1_7_1_3.blockEstimate 5652 1254 1254 128 = 1987982880 := by decide +kernel

private theorem cost_5652_1254_block1 : P1_7_1_3.blockEstimate 5652 1254 1382 128 = 13460784672 := by decide +kernel

private theorem cost_5652_1254_block2 : P1_7_1_3.blockEstimate 5652 1254 1510 128 = 35575584288 := by decide +kernel

private theorem cost_5652_1254_block3 : P1_7_1_3.blockEstimate 5652 1254 1638 128 = 67527075360 := by decide +kernel

private theorem cost_5652_1254_block4 : P1_7_1_3.blockEstimate 5652 1254 1766 128 = 108509951520 := by decide +kernel

private theorem cost_5652_1254_block5 : P1_7_1_3.blockEstimate 5652 1254 1894 128 = 157718906400 := by decide +kernel

private theorem cost_5652_1254_block6 : P1_7_1_3.blockEstimate 5652 1254 2022 128 = 214348633632 := by decide +kernel

private theorem cost_5652_1254_block7 : P1_7_1_3.blockEstimate 5652 1254 2150 128 = 277593826848 := by decide +kernel

private theorem cost_5652_1254_block8 : P1_7_1_3.blockEstimate 5652 1254 2278 128 = 346649179680 := by decide +kernel

private theorem cost_5652_1254_block9 : P1_7_1_3.blockEstimate 5652 1254 2406 128 = 420696577185 := by decide +kernel

private theorem cost_5652_1254_block10 : P1_7_1_3.blockEstimate 5652 1254 2534 128 = 496374949440 := by decide +kernel

private theorem cost_5652_1254_block11 : P1_7_1_3.blockEstimate 5652 1254 2662 128 = 567580878400 := by decide +kernel

private theorem cost_5652_1254_block12 : P1_7_1_3.blockEstimate 5652 1254 2790 128 = 633522955840 := by decide +kernel

private theorem cost_5652_1254_block13 : P1_7_1_3.blockEstimate 5652 1254 2918 128 = 694201181760 := by decide +kernel

private theorem cost_5652_1254_block14 : P1_7_1_3.blockEstimate 5652 1254 3046 128 = 749615556160 := by decide +kernel

private theorem cost_5652_1254_block15 : P1_7_1_3.blockEstimate 5652 1254 3174 128 = 799766079040 := by decide +kernel

private theorem cost_5652_1254_block16 : P1_7_1_3.blockEstimate 5652 1254 3302 128 = 844652750400 := by decide +kernel

private theorem cost_5652_1254_block17 : P1_7_1_3.blockEstimate 5652 1254 3430 128 = 884275570240 := by decide +kernel

private theorem cost_5652_1254_block18 : P1_7_1_3.blockEstimate 5652 1254 3558 128 = 918634538560 := by decide +kernel

private theorem cost_5652_1254_block19 : P1_7_1_3.blockEstimate 5652 1254 3686 128 = 947729655360 := by decide +kernel

private theorem cost_5652_1254_block20 : P1_7_1_3.blockEstimate 5652 1254 3814 128 = 971560920640 := by decide +kernel

private theorem cost_5652_1254_block21 : P1_7_1_3.blockEstimate 5652 1254 3942 128 = 990128334400 := by decide +kernel

private theorem cost_5652_1254_block22 : P1_7_1_3.blockEstimate 5652 1254 4070 128 = 1003431896640 := by decide +kernel

private theorem cost_5652_1254_block23 : P1_7_1_3.blockEstimate 5652 1254 4198 128 = 1011471607360 := by decide +kernel

private theorem cost_5652_1254_block24 : P1_7_1_3.blockEstimate 5652 1254 4326 128 = 1014247466560 := by decide +kernel

private theorem cost_5652_1254_block25 : P1_7_1_3.blockEstimate 5652 1254 4454 128 = 1011759474240 := by decide +kernel

private theorem cost_5652_1254_block26 : P1_7_1_3.blockEstimate 5652 1254 4582 128 = 1004007630400 := by decide +kernel

private theorem cost_5652_1254_block27 : P1_7_1_3.blockEstimate 5652 1254 4710 128 = 990991935040 := by decide +kernel

private theorem cost_5652_1254_block28 : P1_7_1_3.blockEstimate 5652 1254 4838 128 = 972712388160 := by decide +kernel

private theorem cost_5652_1254_block29 : P1_7_1_3.blockEstimate 5652 1254 4966 128 = 949168989760 := by decide +kernel

private theorem cost_5652_1254_block30 : P1_7_1_3.blockEstimate 5652 1254 5094 128 = 920361739840 := by decide +kernel

private theorem cost_5652_1254_block31 : P1_7_1_3.blockEstimate 5652 1254 5222 128 = 886290638400 := by decide +kernel

private theorem cost_5652_1254_block32 : P1_7_1_3.blockEstimate 5652 1254 5350 128 = 846955685440 := by decide +kernel

private theorem cost_5652_1254_block33 : P1_7_1_3.blockEstimate 5652 1254 5478 128 = 802356880960 := by decide +kernel

private theorem cost_5652_1254_block34 : P1_7_1_3.blockEstimate 5652 1254 5606 128 = 752645597135 := by decide +kernel

private theorem cost_5652_1254_block35 : P1_7_1_3.blockEstimate 5652 1254 5734 128 = 699841598533 := by decide +kernel

private theorem cost_5652_1254_block36 : P1_7_1_3.blockEstimate 5652 1254 5862 128 = 645720960400 := by decide +kernel

private theorem cost_5652_1254_block37 : P1_7_1_3.blockEstimate 5652 1254 5990 128 = 590878138670 := by decide +kernel

private theorem cost_5652_1254_block38 : P1_7_1_3.blockEstimate 5652 1254 6118 128 = 535862811113 := by decide +kernel

private theorem cost_5652_1254_block39 : P1_7_1_3.blockEstimate 5652 1254 6246 128 = 481204122023 := by decide +kernel

private theorem cost_5652_1254_block40 : P1_7_1_3.blockEstimate 5652 1254 6374 128 = 427410681911 := by decide +kernel

private theorem cost_5652_1254_block41 : P1_7_1_3.blockEstimate 5652 1254 6502 128 = 374970567092 := by decide +kernel

private theorem cost_5652_1254_block42 : P1_7_1_3.blockEstimate 5652 1254 6630 128 = 324351320628 := by decide +kernel

private theorem cost_5652_1254_block43 : P1_7_1_3.blockEstimate 5652 1254 6758 128 = 275999951742 := by decide +kernel

private theorem cost_5652_1254_block44 : P1_7_1_3.blockEstimate 5652 1254 6886 128 = 230099328707 := by decide +kernel

private theorem cost_5652_1254_block45 : P1_7_1_3.blockEstimate 5652 1254 7014 128 = 187099130288 := by decide +kernel

private theorem cost_5652_1254_block46 : P1_7_1_3.blockEstimate 5652 1254 7142 128 = 147887001008 := by decide +kernel

private theorem cost_5652_1254_block47 : P1_7_1_3.blockEstimate 5652 1254 7270 128 = 112724275632 := by decide +kernel

private theorem cost_5652_1254_block48 : P1_7_1_3.blockEstimate 5652 1254 7398 128 = 81862612400 := by decide +kernel

private theorem cost_5652_1254_block49 : P1_7_1_3.blockEstimate 5652 1254 7526 128 = 55553669552 := by decide +kernel

private theorem cost_5652_1254_block50 : P1_7_1_3.blockEstimate 5652 1254 7654 128 = 34049105328 := by decide +kernel

private theorem cost_5652_1254_block51 : P1_7_1_3.blockEstimate 5652 1254 7782 128 = 17600577968 := by decide +kernel

private theorem cost_5652_1254_block52 : P1_7_1_3.blockEstimate 5652 1254 7910 128 = 6459745712 := by decide +kernel

private theorem cost_5652_1254_block53 : P1_7_1_3.blockEstimate 5652 1254 8038 122 = 878227210 := by decide +kernel

private theorem cost_5652_1254_join0_0 : P1_7_1_3.blockEstimate 5652 1254 1254 256 = 15448767552 :=
  @P1_7_1_3.block_append 5652 1254 1254 1382 128 128 256 1987982880 13460784672 15448767552 cost_5652_1254_block0 cost_5652_1254_block1 rfl rfl rfl

private theorem cost_5652_1254_join0_2 : P1_7_1_3.blockEstimate 5652 1254 1510 256 = 103102659648 :=
  @P1_7_1_3.block_append 5652 1254 1510 1638 128 128 256 35575584288 67527075360 103102659648 cost_5652_1254_block2 cost_5652_1254_block3 rfl rfl rfl

private theorem cost_5652_1254_join0_4 : P1_7_1_3.blockEstimate 5652 1254 1766 256 = 266228857920 :=
  @P1_7_1_3.block_append 5652 1254 1766 1894 128 128 256 108509951520 157718906400 266228857920 cost_5652_1254_block4 cost_5652_1254_block5 rfl rfl rfl

private theorem cost_5652_1254_join0_6 : P1_7_1_3.blockEstimate 5652 1254 2022 256 = 491942460480 :=
  @P1_7_1_3.block_append 5652 1254 2022 2150 128 128 256 214348633632 277593826848 491942460480 cost_5652_1254_block6 cost_5652_1254_block7 rfl rfl rfl

private theorem cost_5652_1254_join0_8 : P1_7_1_3.blockEstimate 5652 1254 2278 256 = 767345756865 :=
  @P1_7_1_3.block_append 5652 1254 2278 2406 128 128 256 346649179680 420696577185 767345756865 cost_5652_1254_block8 cost_5652_1254_block9 rfl rfl rfl

private theorem cost_5652_1254_join0_10 : P1_7_1_3.blockEstimate 5652 1254 2534 256 = 1063955827840 :=
  @P1_7_1_3.block_append 5652 1254 2534 2662 128 128 256 496374949440 567580878400 1063955827840 cost_5652_1254_block10 cost_5652_1254_block11 rfl rfl rfl

private theorem cost_5652_1254_join0_12 : P1_7_1_3.blockEstimate 5652 1254 2790 256 = 1327724137600 :=
  @P1_7_1_3.block_append 5652 1254 2790 2918 128 128 256 633522955840 694201181760 1327724137600 cost_5652_1254_block12 cost_5652_1254_block13 rfl rfl rfl

private theorem cost_5652_1254_join0_14 : P1_7_1_3.blockEstimate 5652 1254 3046 256 = 1549381635200 :=
  @P1_7_1_3.block_append 5652 1254 3046 3174 128 128 256 749615556160 799766079040 1549381635200 cost_5652_1254_block14 cost_5652_1254_block15 rfl rfl rfl

private theorem cost_5652_1254_join0_16 : P1_7_1_3.blockEstimate 5652 1254 3302 256 = 1728928320640 :=
  @P1_7_1_3.block_append 5652 1254 3302 3430 128 128 256 844652750400 884275570240 1728928320640 cost_5652_1254_block16 cost_5652_1254_block17 rfl rfl rfl

private theorem cost_5652_1254_join0_18 : P1_7_1_3.blockEstimate 5652 1254 3558 256 = 1866364193920 :=
  @P1_7_1_3.block_append 5652 1254 3558 3686 128 128 256 918634538560 947729655360 1866364193920 cost_5652_1254_block18 cost_5652_1254_block19 rfl rfl rfl

private theorem cost_5652_1254_join0_20 : P1_7_1_3.blockEstimate 5652 1254 3814 256 = 1961689255040 :=
  @P1_7_1_3.block_append 5652 1254 3814 3942 128 128 256 971560920640 990128334400 1961689255040 cost_5652_1254_block20 cost_5652_1254_block21 rfl rfl rfl

private theorem cost_5652_1254_join0_22 : P1_7_1_3.blockEstimate 5652 1254 4070 256 = 2014903504000 :=
  @P1_7_1_3.block_append 5652 1254 4070 4198 128 128 256 1003431896640 1011471607360 2014903504000 cost_5652_1254_block22 cost_5652_1254_block23 rfl rfl rfl

private theorem cost_5652_1254_join0_24 : P1_7_1_3.blockEstimate 5652 1254 4326 256 = 2026006940800 :=
  @P1_7_1_3.block_append 5652 1254 4326 4454 128 128 256 1014247466560 1011759474240 2026006940800 cost_5652_1254_block24 cost_5652_1254_block25 rfl rfl rfl

private theorem cost_5652_1254_join0_26 : P1_7_1_3.blockEstimate 5652 1254 4582 256 = 1994999565440 :=
  @P1_7_1_3.block_append 5652 1254 4582 4710 128 128 256 1004007630400 990991935040 1994999565440 cost_5652_1254_block26 cost_5652_1254_block27 rfl rfl rfl

private theorem cost_5652_1254_join0_28 : P1_7_1_3.blockEstimate 5652 1254 4838 256 = 1921881377920 :=
  @P1_7_1_3.block_append 5652 1254 4838 4966 128 128 256 972712388160 949168989760 1921881377920 cost_5652_1254_block28 cost_5652_1254_block29 rfl rfl rfl

private theorem cost_5652_1254_join0_30 : P1_7_1_3.blockEstimate 5652 1254 5094 256 = 1806652378240 :=
  @P1_7_1_3.block_append 5652 1254 5094 5222 128 128 256 920361739840 886290638400 1806652378240 cost_5652_1254_block30 cost_5652_1254_block31 rfl rfl rfl

private theorem cost_5652_1254_join0_32 : P1_7_1_3.blockEstimate 5652 1254 5350 256 = 1649312566400 :=
  @P1_7_1_3.block_append 5652 1254 5350 5478 128 128 256 846955685440 802356880960 1649312566400 cost_5652_1254_block32 cost_5652_1254_block33 rfl rfl rfl

private theorem cost_5652_1254_join0_34 : P1_7_1_3.blockEstimate 5652 1254 5606 256 = 1452487195668 :=
  @P1_7_1_3.block_append 5652 1254 5606 5734 128 128 256 752645597135 699841598533 1452487195668 cost_5652_1254_block34 cost_5652_1254_block35 rfl rfl rfl

private theorem cost_5652_1254_join0_36 : P1_7_1_3.blockEstimate 5652 1254 5862 256 = 1236599099070 :=
  @P1_7_1_3.block_append 5652 1254 5862 5990 128 128 256 645720960400 590878138670 1236599099070 cost_5652_1254_block36 cost_5652_1254_block37 rfl rfl rfl

private theorem cost_5652_1254_join0_38 : P1_7_1_3.blockEstimate 5652 1254 6118 256 = 1017066933136 :=
  @P1_7_1_3.block_append 5652 1254 6118 6246 128 128 256 535862811113 481204122023 1017066933136 cost_5652_1254_block38 cost_5652_1254_block39 rfl rfl rfl

private theorem cost_5652_1254_join0_40 : P1_7_1_3.blockEstimate 5652 1254 6374 256 = 802381249003 :=
  @P1_7_1_3.block_append 5652 1254 6374 6502 128 128 256 427410681911 374970567092 802381249003 cost_5652_1254_block40 cost_5652_1254_block41 rfl rfl rfl

private theorem cost_5652_1254_join0_42 : P1_7_1_3.blockEstimate 5652 1254 6630 256 = 600351272370 :=
  @P1_7_1_3.block_append 5652 1254 6630 6758 128 128 256 324351320628 275999951742 600351272370 cost_5652_1254_block42 cost_5652_1254_block43 rfl rfl rfl

private theorem cost_5652_1254_join0_44 : P1_7_1_3.blockEstimate 5652 1254 6886 256 = 417198458995 :=
  @P1_7_1_3.block_append 5652 1254 6886 7014 128 128 256 230099328707 187099130288 417198458995 cost_5652_1254_block44 cost_5652_1254_block45 rfl rfl rfl

private theorem cost_5652_1254_join0_46 : P1_7_1_3.blockEstimate 5652 1254 7142 256 = 260611276640 :=
  @P1_7_1_3.block_append 5652 1254 7142 7270 128 128 256 147887001008 112724275632 260611276640 cost_5652_1254_block46 cost_5652_1254_block47 rfl rfl rfl

private theorem cost_5652_1254_join0_48 : P1_7_1_3.blockEstimate 5652 1254 7398 256 = 137416281952 :=
  @P1_7_1_3.block_append 5652 1254 7398 7526 128 128 256 81862612400 55553669552 137416281952 cost_5652_1254_block48 cost_5652_1254_block49 rfl rfl rfl

private theorem cost_5652_1254_join0_50 : P1_7_1_3.blockEstimate 5652 1254 7654 256 = 51649683296 :=
  @P1_7_1_3.block_append 5652 1254 7654 7782 128 128 256 34049105328 17600577968 51649683296 cost_5652_1254_block50 cost_5652_1254_block51 rfl rfl rfl

private theorem cost_5652_1254_join0_52 : P1_7_1_3.blockEstimate 5652 1254 7910 250 = 7337972922 :=
  @P1_7_1_3.block_append 5652 1254 7910 8038 128 122 250 6459745712 878227210 7337972922 cost_5652_1254_block52 cost_5652_1254_block53 rfl rfl rfl

private theorem cost_5652_1254_join1_0 : P1_7_1_3.blockEstimate 5652 1254 1254 512 = 118551427200 :=
  @P1_7_1_3.block_append 5652 1254 1254 1510 256 256 512 15448767552 103102659648 118551427200 cost_5652_1254_join0_0 cost_5652_1254_join0_2 rfl rfl rfl

private theorem cost_5652_1254_join1_2 : P1_7_1_3.blockEstimate 5652 1254 1766 512 = 758171318400 :=
  @P1_7_1_3.block_append 5652 1254 1766 2022 256 256 512 266228857920 491942460480 758171318400 cost_5652_1254_join0_4 cost_5652_1254_join0_6 rfl rfl rfl

private theorem cost_5652_1254_join1_4 : P1_7_1_3.blockEstimate 5652 1254 2278 512 = 1831301584705 :=
  @P1_7_1_3.block_append 5652 1254 2278 2534 256 256 512 767345756865 1063955827840 1831301584705 cost_5652_1254_join0_8 cost_5652_1254_join0_10 rfl rfl rfl

private theorem cost_5652_1254_join1_6 : P1_7_1_3.blockEstimate 5652 1254 2790 512 = 2877105772800 :=
  @P1_7_1_3.block_append 5652 1254 2790 3046 256 256 512 1327724137600 1549381635200 2877105772800 cost_5652_1254_join0_12 cost_5652_1254_join0_14 rfl rfl rfl

private theorem cost_5652_1254_join1_8 : P1_7_1_3.blockEstimate 5652 1254 3302 512 = 3595292514560 :=
  @P1_7_1_3.block_append 5652 1254 3302 3558 256 256 512 1728928320640 1866364193920 3595292514560 cost_5652_1254_join0_16 cost_5652_1254_join0_18 rfl rfl rfl

private theorem cost_5652_1254_join1_10 : P1_7_1_3.blockEstimate 5652 1254 3814 512 = 3976592759040 :=
  @P1_7_1_3.block_append 5652 1254 3814 4070 256 256 512 1961689255040 2014903504000 3976592759040 cost_5652_1254_join0_20 cost_5652_1254_join0_22 rfl rfl rfl

private theorem cost_5652_1254_join1_12 : P1_7_1_3.blockEstimate 5652 1254 4326 512 = 4021006506240 :=
  @P1_7_1_3.block_append 5652 1254 4326 4582 256 256 512 2026006940800 1994999565440 4021006506240 cost_5652_1254_join0_24 cost_5652_1254_join0_26 rfl rfl rfl

private theorem cost_5652_1254_join1_14 : P1_7_1_3.blockEstimate 5652 1254 4838 512 = 3728533756160 :=
  @P1_7_1_3.block_append 5652 1254 4838 5094 256 256 512 1921881377920 1806652378240 3728533756160 cost_5652_1254_join0_28 cost_5652_1254_join0_30 rfl rfl rfl

private theorem cost_5652_1254_join1_16 : P1_7_1_3.blockEstimate 5652 1254 5350 512 = 3101799762068 :=
  @P1_7_1_3.block_append 5652 1254 5350 5606 256 256 512 1649312566400 1452487195668 3101799762068 cost_5652_1254_join0_32 cost_5652_1254_join0_34 rfl rfl rfl

private theorem cost_5652_1254_join1_18 : P1_7_1_3.blockEstimate 5652 1254 5862 512 = 2253666032206 :=
  @P1_7_1_3.block_append 5652 1254 5862 6118 256 256 512 1236599099070 1017066933136 2253666032206 cost_5652_1254_join0_36 cost_5652_1254_join0_38 rfl rfl rfl

private theorem cost_5652_1254_join1_20 : P1_7_1_3.blockEstimate 5652 1254 6374 512 = 1402732521373 :=
  @P1_7_1_3.block_append 5652 1254 6374 6630 256 256 512 802381249003 600351272370 1402732521373 cost_5652_1254_join0_40 cost_5652_1254_join0_42 rfl rfl rfl

private theorem cost_5652_1254_join1_22 : P1_7_1_3.blockEstimate 5652 1254 6886 512 = 677809735635 :=
  @P1_7_1_3.block_append 5652 1254 6886 7142 256 256 512 417198458995 260611276640 677809735635 cost_5652_1254_join0_44 cost_5652_1254_join0_46 rfl rfl rfl

private theorem cost_5652_1254_join1_24 : P1_7_1_3.blockEstimate 5652 1254 7398 512 = 189065965248 :=
  @P1_7_1_3.block_append 5652 1254 7398 7654 256 256 512 137416281952 51649683296 189065965248 cost_5652_1254_join0_48 cost_5652_1254_join0_50 rfl rfl rfl

private theorem cost_5652_1254_join2_0 : P1_7_1_3.blockEstimate 5652 1254 1254 1024 = 876722745600 :=
  @P1_7_1_3.block_append 5652 1254 1254 1766 512 512 1024 118551427200 758171318400 876722745600 cost_5652_1254_join1_0 cost_5652_1254_join1_2 rfl rfl rfl

private theorem cost_5652_1254_join2_2 : P1_7_1_3.blockEstimate 5652 1254 2278 1024 = 4708407357505 :=
  @P1_7_1_3.block_append 5652 1254 2278 2790 512 512 1024 1831301584705 2877105772800 4708407357505 cost_5652_1254_join1_4 cost_5652_1254_join1_6 rfl rfl rfl

private theorem cost_5652_1254_join2_4 : P1_7_1_3.blockEstimate 5652 1254 3302 1024 = 7571885273600 :=
  @P1_7_1_3.block_append 5652 1254 3302 3814 512 512 1024 3595292514560 3976592759040 7571885273600 cost_5652_1254_join1_8 cost_5652_1254_join1_10 rfl rfl rfl

private theorem cost_5652_1254_join2_6 : P1_7_1_3.blockEstimate 5652 1254 4326 1024 = 7749540262400 :=
  @P1_7_1_3.block_append 5652 1254 4326 4838 512 512 1024 4021006506240 3728533756160 7749540262400 cost_5652_1254_join1_12 cost_5652_1254_join1_14 rfl rfl rfl

private theorem cost_5652_1254_join2_8 : P1_7_1_3.blockEstimate 5652 1254 5350 1024 = 5355465794274 :=
  @P1_7_1_3.block_append 5652 1254 5350 5862 512 512 1024 3101799762068 2253666032206 5355465794274 cost_5652_1254_join1_16 cost_5652_1254_join1_18 rfl rfl rfl

private theorem cost_5652_1254_join2_10 : P1_7_1_3.blockEstimate 5652 1254 6374 1024 = 2080542257008 :=
  @P1_7_1_3.block_append 5652 1254 6374 6886 512 512 1024 1402732521373 677809735635 2080542257008 cost_5652_1254_join1_20 cost_5652_1254_join1_22 rfl rfl rfl

private theorem cost_5652_1254_join2_12 : P1_7_1_3.blockEstimate 5652 1254 7398 762 = 196403938170 :=
  @P1_7_1_3.block_append 5652 1254 7398 7910 512 250 762 189065965248 7337972922 196403938170 cost_5652_1254_join1_24 cost_5652_1254_join0_52 rfl rfl rfl

private theorem cost_5652_1254_join3_0 : P1_7_1_3.blockEstimate 5652 1254 1254 2048 = 5585130103105 :=
  @P1_7_1_3.block_append 5652 1254 1254 2278 1024 1024 2048 876722745600 4708407357505 5585130103105 cost_5652_1254_join2_0 cost_5652_1254_join2_2 rfl rfl rfl

private theorem cost_5652_1254_join3_2 : P1_7_1_3.blockEstimate 5652 1254 3302 2048 = 15321425536000 :=
  @P1_7_1_3.block_append 5652 1254 3302 4326 1024 1024 2048 7571885273600 7749540262400 15321425536000 cost_5652_1254_join2_4 cost_5652_1254_join2_6 rfl rfl rfl

private theorem cost_5652_1254_join3_4 : P1_7_1_3.blockEstimate 5652 1254 5350 2048 = 7436008051282 :=
  @P1_7_1_3.block_append 5652 1254 5350 6374 1024 1024 2048 5355465794274 2080542257008 7436008051282 cost_5652_1254_join2_8 cost_5652_1254_join2_10 rfl rfl rfl

private theorem cost_5652_1254_join4_0 : P1_7_1_3.blockEstimate 5652 1254 1254 4096 = 20906555639105 :=
  @P1_7_1_3.block_append 5652 1254 1254 3302 2048 2048 4096 5585130103105 15321425536000 20906555639105 cost_5652_1254_join3_0 cost_5652_1254_join3_2 rfl rfl rfl

private theorem cost_5652_1254_join4_2 : P1_7_1_3.blockEstimate 5652 1254 5350 2810 = 7632411989452 :=
  @P1_7_1_3.block_append 5652 1254 5350 7398 2048 762 2810 7436008051282 196403938170 7632411989452 cost_5652_1254_join3_4 cost_5652_1254_join2_12 rfl rfl rfl

private theorem cost_5652_1254_join5_0 : P1_7_1_3.blockEstimate 5652 1254 1254 6906 = 28538967628557 :=
  @P1_7_1_3.block_append 5652 1254 1254 5350 4096 2810 6906 20906555639105 7632411989452 28538967628557 cost_5652_1254_join4_0 cost_5652_1254_join4_2 rfl rfl rfl

private theorem cost_5652_1254_total : P1_7_1_3.momentEstimate 5652 1254 = 28538967628557 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 5652 + 1254 = 6906 by decide]
  exact cost_5652_1254_join5_0

theorem moment5652_1254 : P1_7_1.groupedPoleMoment 5652 1254 ≤ 28538967628557 :=
  (P1_7_1_3.grouped_bound 5652 1254).trans_eq cost_5652_1254_total
private theorem cost_5771_1240_block0 : P1_7_1_3.blockEstimate 5771 1240 1240 128 = 2030556320 := by decide +kernel

private theorem cost_5771_1240_block1 : P1_7_1_3.blockEstimate 5771 1240 1368 128 = 13754868896 := by decide +kernel

private theorem cost_5771_1240_block2 : P1_7_1_3.blockEstimate 5771 1240 1496 128 = 36370740384 := by decide +kernel

private theorem cost_5771_1240_block3 : P1_7_1_3.blockEstimate 5771 1240 1624 128 = 69072864416 := by decide +kernel

private theorem cost_5771_1240_block4 : P1_7_1_3.blockEstimate 5771 1240 1752 128 = 111055934624 := by decide +kernel

private theorem cost_5771_1240_block5 : P1_7_1_3.blockEstimate 5771 1240 1880 128 = 161514644640 := by decide +kernel

private theorem cost_5771_1240_block6 : P1_7_1_3.blockEstimate 5771 1240 2008 128 = 219643688096 := by decide +kernel

private theorem cost_5771_1240_block7 : P1_7_1_3.blockEstimate 5771 1240 2136 128 = 284637758624 := by decide +kernel

private theorem cost_5771_1240_block8 : P1_7_1_3.blockEstimate 5771 1240 2264 128 = 355691549856 := by decide +kernel

private theorem cost_5771_1240_block9 : P1_7_1_3.blockEstimate 5771 1240 2392 128 = 431951769434 := by decide +kernel

private theorem cost_5771_1240_block10 : P1_7_1_3.blockEstimate 5771 1240 2520 128 = 509323635008 := by decide +kernel

private theorem cost_5771_1240_block11 : P1_7_1_3.blockEstimate 5771 1240 2648 128 = 582012479808 := by decide +kernel

private theorem cost_5771_1240_block12 : P1_7_1_3.blockEstimate 5771 1240 2776 128 = 649496193344 := by decide +kernel

private theorem cost_5771_1240_block13 : P1_7_1_3.blockEstimate 5771 1240 2904 128 = 711774775616 := by decide +kernel

private theorem cost_5771_1240_block14 : P1_7_1_3.blockEstimate 5771 1240 3032 128 = 768848226624 := by decide +kernel

private theorem cost_5771_1240_block15 : P1_7_1_3.blockEstimate 5771 1240 3160 128 = 820716546368 := by decide +kernel

private theorem cost_5771_1240_block16 : P1_7_1_3.blockEstimate 5771 1240 3288 128 = 867379734848 := by decide +kernel

private theorem cost_5771_1240_block17 : P1_7_1_3.blockEstimate 5771 1240 3416 128 = 908837792064 := by decide +kernel

private theorem cost_5771_1240_block18 : P1_7_1_3.blockEstimate 5771 1240 3544 128 = 945090718016 := by decide +kernel

private theorem cost_5771_1240_block19 : P1_7_1_3.blockEstimate 5771 1240 3672 128 = 976138512704 := by decide +kernel

private theorem cost_5771_1240_block20 : P1_7_1_3.blockEstimate 5771 1240 3800 128 = 1001981176128 := by decide +kernel

private theorem cost_5771_1240_block21 : P1_7_1_3.blockEstimate 5771 1240 3928 128 = 1022618708288 := by decide +kernel

private theorem cost_5771_1240_block22 : P1_7_1_3.blockEstimate 5771 1240 4056 128 = 1038051109184 := by decide +kernel

private theorem cost_5771_1240_block23 : P1_7_1_3.blockEstimate 5771 1240 4184 128 = 1048278378816 := by decide +kernel

private theorem cost_5771_1240_block24 : P1_7_1_3.blockEstimate 5771 1240 4312 128 = 1053300517184 := by decide +kernel

private theorem cost_5771_1240_block25 : P1_7_1_3.blockEstimate 5771 1240 4440 128 = 1053117524288 := by decide +kernel

private theorem cost_5771_1240_block26 : P1_7_1_3.blockEstimate 5771 1240 4568 128 = 1047729400128 := by decide +kernel

private theorem cost_5771_1240_block27 : P1_7_1_3.blockEstimate 5771 1240 4696 128 = 1037136144704 := by decide +kernel

private theorem cost_5771_1240_block28 : P1_7_1_3.blockEstimate 5771 1240 4824 128 = 1021337758016 := by decide +kernel

private theorem cost_5771_1240_block29 : P1_7_1_3.blockEstimate 5771 1240 4952 128 = 1000334240064 := by decide +kernel

private theorem cost_5771_1240_block30 : P1_7_1_3.blockEstimate 5771 1240 5080 128 = 974125590848 := by decide +kernel

private theorem cost_5771_1240_block31 : P1_7_1_3.blockEstimate 5771 1240 5208 128 = 942711810368 := by decide +kernel

private theorem cost_5771_1240_block32 : P1_7_1_3.blockEstimate 5771 1240 5336 128 = 906092898624 := by decide +kernel

private theorem cost_5771_1240_block33 : P1_7_1_3.blockEstimate 5771 1240 5464 128 = 864268855616 := by decide +kernel

private theorem cost_5771_1240_block34 : P1_7_1_3.blockEstimate 5771 1240 5592 128 = 817239681344 := by decide +kernel

private theorem cost_5771_1240_block35 : P1_7_1_3.blockEstimate 5771 1240 5720 128 = 765136338999 := by decide +kernel

private theorem cost_5771_1240_block36 : P1_7_1_3.blockEstimate 5771 1240 5848 128 = 709979865507 := by decide +kernel

private theorem cost_5771_1240_block37 : P1_7_1_3.blockEstimate 5771 1240 5976 128 = 653686325208 := by decide +kernel

private theorem cost_5771_1240_block38 : P1_7_1_3.blockEstimate 5771 1240 6104 128 = 596861031088 := by decide +kernel

private theorem cost_5771_1240_block39 : P1_7_1_3.blockEstimate 5771 1240 6232 128 = 540053860298 := by decide +kernel

private theorem cost_5771_1240_block40 : P1_7_1_3.blockEstimate 5771 1240 6360 128 = 483793923213 := by decide +kernel

private theorem cost_5771_1240_block41 : P1_7_1_3.blockEstimate 5771 1240 6488 128 = 428589565534 := by decide +kernel

private theorem cost_5771_1240_block42 : P1_7_1_3.blockEstimate 5771 1240 6616 128 = 374928367952 := by decide +kernel

private theorem cost_5771_1240_block43 : P1_7_1_3.blockEstimate 5771 1240 6744 128 = 323277144831 := by decide +kernel

private theorem cost_5771_1240_block44 : P1_7_1_3.blockEstimate 5771 1240 6872 128 = 274081945944 := by decide +kernel

private theorem cost_5771_1240_block45 : P1_7_1_3.blockEstimate 5771 1240 7000 128 = 227493447330 := by decide +kernel

private theorem cost_5771_1240_block46 : P1_7_1_3.blockEstimate 5771 1240 7128 128 = 184053917024 := by decide +kernel

private theorem cost_5771_1240_block47 : P1_7_1_3.blockEstimate 5771 1240 7256 128 = 144579431776 := by decide +kernel

private theorem cost_5771_1240_block48 : P1_7_1_3.blockEstimate 5771 1240 7384 128 = 109324350816 := by decide +kernel

private theorem cost_5771_1240_block49 : P1_7_1_3.blockEstimate 5771 1240 7512 128 = 78540332384 := by decide +kernel

private theorem cost_5771_1240_block50 : P1_7_1_3.blockEstimate 5771 1240 7640 128 = 52479034720 := by decide +kernel

private theorem cost_5771_1240_block51 : P1_7_1_3.blockEstimate 5771 1240 7768 128 = 31392116064 := by decide +kernel

private theorem cost_5771_1240_block52 : P1_7_1_3.blockEstimate 5771 1240 7896 128 = 15531234656 := by decide +kernel

private theorem cost_5771_1240_block53 : P1_7_1_3.blockEstimate 5771 1240 8024 128 = 5148048736 := by decide +kernel

private theorem cost_5771_1240_block54 : P1_7_1_3.blockEstimate 5771 1240 8152 99 = 484213775 := by decide +kernel

private theorem cost_5771_1240_join0_0 : P1_7_1_3.blockEstimate 5771 1240 1240 256 = 15785425216 :=
  @P1_7_1_3.block_append 5771 1240 1240 1368 128 128 256 2030556320 13754868896 15785425216 cost_5771_1240_block0 cost_5771_1240_block1 rfl rfl rfl

private theorem cost_5771_1240_join0_2 : P1_7_1_3.blockEstimate 5771 1240 1496 256 = 105443604800 :=
  @P1_7_1_3.block_append 5771 1240 1496 1624 128 128 256 36370740384 69072864416 105443604800 cost_5771_1240_block2 cost_5771_1240_block3 rfl rfl rfl

private theorem cost_5771_1240_join0_4 : P1_7_1_3.blockEstimate 5771 1240 1752 256 = 272570579264 :=
  @P1_7_1_3.block_append 5771 1240 1752 1880 128 128 256 111055934624 161514644640 272570579264 cost_5771_1240_block4 cost_5771_1240_block5 rfl rfl rfl

private theorem cost_5771_1240_join0_6 : P1_7_1_3.blockEstimate 5771 1240 2008 256 = 504281446720 :=
  @P1_7_1_3.block_append 5771 1240 2008 2136 128 128 256 219643688096 284637758624 504281446720 cost_5771_1240_block6 cost_5771_1240_block7 rfl rfl rfl

private theorem cost_5771_1240_join0_8 : P1_7_1_3.blockEstimate 5771 1240 2264 256 = 787643319290 :=
  @P1_7_1_3.block_append 5771 1240 2264 2392 128 128 256 355691549856 431951769434 787643319290 cost_5771_1240_block8 cost_5771_1240_block9 rfl rfl rfl

private theorem cost_5771_1240_join0_10 : P1_7_1_3.blockEstimate 5771 1240 2520 256 = 1091336114816 :=
  @P1_7_1_3.block_append 5771 1240 2520 2648 128 128 256 509323635008 582012479808 1091336114816 cost_5771_1240_block10 cost_5771_1240_block11 rfl rfl rfl

private theorem cost_5771_1240_join0_12 : P1_7_1_3.blockEstimate 5771 1240 2776 256 = 1361270968960 :=
  @P1_7_1_3.block_append 5771 1240 2776 2904 128 128 256 649496193344 711774775616 1361270968960 cost_5771_1240_block12 cost_5771_1240_block13 rfl rfl rfl

private theorem cost_5771_1240_join0_14 : P1_7_1_3.blockEstimate 5771 1240 3032 256 = 1589564772992 :=
  @P1_7_1_3.block_append 5771 1240 3032 3160 128 128 256 768848226624 820716546368 1589564772992 cost_5771_1240_block14 cost_5771_1240_block15 rfl rfl rfl

private theorem cost_5771_1240_join0_16 : P1_7_1_3.blockEstimate 5771 1240 3288 256 = 1776217526912 :=
  @P1_7_1_3.block_append 5771 1240 3288 3416 128 128 256 867379734848 908837792064 1776217526912 cost_5771_1240_block16 cost_5771_1240_block17 rfl rfl rfl

private theorem cost_5771_1240_join0_18 : P1_7_1_3.blockEstimate 5771 1240 3544 256 = 1921229230720 :=
  @P1_7_1_3.block_append 5771 1240 3544 3672 128 128 256 945090718016 976138512704 1921229230720 cost_5771_1240_block18 cost_5771_1240_block19 rfl rfl rfl

private theorem cost_5771_1240_join0_20 : P1_7_1_3.blockEstimate 5771 1240 3800 256 = 2024599884416 :=
  @P1_7_1_3.block_append 5771 1240 3800 3928 128 128 256 1001981176128 1022618708288 2024599884416 cost_5771_1240_block20 cost_5771_1240_block21 rfl rfl rfl

private theorem cost_5771_1240_join0_22 : P1_7_1_3.blockEstimate 5771 1240 4056 256 = 2086329488000 :=
  @P1_7_1_3.block_append 5771 1240 4056 4184 128 128 256 1038051109184 1048278378816 2086329488000 cost_5771_1240_block22 cost_5771_1240_block23 rfl rfl rfl

private theorem cost_5771_1240_join0_24 : P1_7_1_3.blockEstimate 5771 1240 4312 256 = 2106418041472 :=
  @P1_7_1_3.block_append 5771 1240 4312 4440 128 128 256 1053300517184 1053117524288 2106418041472 cost_5771_1240_block24 cost_5771_1240_block25 rfl rfl rfl

private theorem cost_5771_1240_join0_26 : P1_7_1_3.blockEstimate 5771 1240 4568 256 = 2084865544832 :=
  @P1_7_1_3.block_append 5771 1240 4568 4696 128 128 256 1047729400128 1037136144704 2084865544832 cost_5771_1240_block26 cost_5771_1240_block27 rfl rfl rfl

private theorem cost_5771_1240_join0_28 : P1_7_1_3.blockEstimate 5771 1240 4824 256 = 2021671998080 :=
  @P1_7_1_3.block_append 5771 1240 4824 4952 128 128 256 1021337758016 1000334240064 2021671998080 cost_5771_1240_block28 cost_5771_1240_block29 rfl rfl rfl

private theorem cost_5771_1240_join0_30 : P1_7_1_3.blockEstimate 5771 1240 5080 256 = 1916837401216 :=
  @P1_7_1_3.block_append 5771 1240 5080 5208 128 128 256 974125590848 942711810368 1916837401216 cost_5771_1240_block30 cost_5771_1240_block31 rfl rfl rfl

private theorem cost_5771_1240_join0_32 : P1_7_1_3.blockEstimate 5771 1240 5336 256 = 1770361754240 :=
  @P1_7_1_3.block_append 5771 1240 5336 5464 128 128 256 906092898624 864268855616 1770361754240 cost_5771_1240_block32 cost_5771_1240_block33 rfl rfl rfl

private theorem cost_5771_1240_join0_34 : P1_7_1_3.blockEstimate 5771 1240 5592 256 = 1582376020343 :=
  @P1_7_1_3.block_append 5771 1240 5592 5720 128 128 256 817239681344 765136338999 1582376020343 cost_5771_1240_block34 cost_5771_1240_block35 rfl rfl rfl

private theorem cost_5771_1240_join0_36 : P1_7_1_3.blockEstimate 5771 1240 5848 256 = 1363666190715 :=
  @P1_7_1_3.block_append 5771 1240 5848 5976 128 128 256 709979865507 653686325208 1363666190715 cost_5771_1240_block36 cost_5771_1240_block37 rfl rfl rfl

private theorem cost_5771_1240_join0_38 : P1_7_1_3.blockEstimate 5771 1240 6104 256 = 1136914891386 :=
  @P1_7_1_3.block_append 5771 1240 6104 6232 128 128 256 596861031088 540053860298 1136914891386 cost_5771_1240_block38 cost_5771_1240_block39 rfl rfl rfl

private theorem cost_5771_1240_join0_40 : P1_7_1_3.blockEstimate 5771 1240 6360 256 = 912383488747 :=
  @P1_7_1_3.block_append 5771 1240 6360 6488 128 128 256 483793923213 428589565534 912383488747 cost_5771_1240_block40 cost_5771_1240_block41 rfl rfl rfl

private theorem cost_5771_1240_join0_42 : P1_7_1_3.blockEstimate 5771 1240 6616 256 = 698205512783 :=
  @P1_7_1_3.block_append 5771 1240 6616 6744 128 128 256 374928367952 323277144831 698205512783 cost_5771_1240_block42 cost_5771_1240_block43 rfl rfl rfl

private theorem cost_5771_1240_join0_44 : P1_7_1_3.blockEstimate 5771 1240 6872 256 = 501575393274 :=
  @P1_7_1_3.block_append 5771 1240 6872 7000 128 128 256 274081945944 227493447330 501575393274 cost_5771_1240_block44 cost_5771_1240_block45 rfl rfl rfl

private theorem cost_5771_1240_join0_46 : P1_7_1_3.blockEstimate 5771 1240 7128 256 = 328633348800 :=
  @P1_7_1_3.block_append 5771 1240 7128 7256 128 128 256 184053917024 144579431776 328633348800 cost_5771_1240_block46 cost_5771_1240_block47 rfl rfl rfl

private theorem cost_5771_1240_join0_48 : P1_7_1_3.blockEstimate 5771 1240 7384 256 = 187864683200 :=
  @P1_7_1_3.block_append 5771 1240 7384 7512 128 128 256 109324350816 78540332384 187864683200 cost_5771_1240_block48 cost_5771_1240_block49 rfl rfl rfl

private theorem cost_5771_1240_join0_50 : P1_7_1_3.blockEstimate 5771 1240 7640 256 = 83871150784 :=
  @P1_7_1_3.block_append 5771 1240 7640 7768 128 128 256 52479034720 31392116064 83871150784 cost_5771_1240_block50 cost_5771_1240_block51 rfl rfl rfl

private theorem cost_5771_1240_join0_52 : P1_7_1_3.blockEstimate 5771 1240 7896 256 = 20679283392 :=
  @P1_7_1_3.block_append 5771 1240 7896 8024 128 128 256 15531234656 5148048736 20679283392 cost_5771_1240_block52 cost_5771_1240_block53 rfl rfl rfl

private theorem cost_5771_1240_join1_0 : P1_7_1_3.blockEstimate 5771 1240 1240 512 = 121229030016 :=
  @P1_7_1_3.block_append 5771 1240 1240 1496 256 256 512 15785425216 105443604800 121229030016 cost_5771_1240_join0_0 cost_5771_1240_join0_2 rfl rfl rfl

private theorem cost_5771_1240_join1_2 : P1_7_1_3.blockEstimate 5771 1240 1752 512 = 776852025984 :=
  @P1_7_1_3.block_append 5771 1240 1752 2008 256 256 512 272570579264 504281446720 776852025984 cost_5771_1240_join0_4 cost_5771_1240_join0_6 rfl rfl rfl

private theorem cost_5771_1240_join1_4 : P1_7_1_3.blockEstimate 5771 1240 2264 512 = 1878979434106 :=
  @P1_7_1_3.block_append 5771 1240 2264 2520 256 256 512 787643319290 1091336114816 1878979434106 cost_5771_1240_join0_8 cost_5771_1240_join0_10 rfl rfl rfl

private theorem cost_5771_1240_join1_6 : P1_7_1_3.blockEstimate 5771 1240 2776 512 = 2950835741952 :=
  @P1_7_1_3.block_append 5771 1240 2776 3032 256 256 512 1361270968960 1589564772992 2950835741952 cost_5771_1240_join0_12 cost_5771_1240_join0_14 rfl rfl rfl

private theorem cost_5771_1240_join1_8 : P1_7_1_3.blockEstimate 5771 1240 3288 512 = 3697446757632 :=
  @P1_7_1_3.block_append 5771 1240 3288 3544 256 256 512 1776217526912 1921229230720 3697446757632 cost_5771_1240_join0_16 cost_5771_1240_join0_18 rfl rfl rfl

private theorem cost_5771_1240_join1_10 : P1_7_1_3.blockEstimate 5771 1240 3800 512 = 4110929372416 :=
  @P1_7_1_3.block_append 5771 1240 3800 4056 256 256 512 2024599884416 2086329488000 4110929372416 cost_5771_1240_join0_20 cost_5771_1240_join0_22 rfl rfl rfl

private theorem cost_5771_1240_join1_12 : P1_7_1_3.blockEstimate 5771 1240 4312 512 = 4191283586304 :=
  @P1_7_1_3.block_append 5771 1240 4312 4568 256 256 512 2106418041472 2084865544832 4191283586304 cost_5771_1240_join0_24 cost_5771_1240_join0_26 rfl rfl rfl

private theorem cost_5771_1240_join1_14 : P1_7_1_3.blockEstimate 5771 1240 4824 512 = 3938509399296 :=
  @P1_7_1_3.block_append 5771 1240 4824 5080 256 256 512 2021671998080 1916837401216 3938509399296 cost_5771_1240_join0_28 cost_5771_1240_join0_30 rfl rfl rfl

private theorem cost_5771_1240_join1_16 : P1_7_1_3.blockEstimate 5771 1240 5336 512 = 3352737774583 :=
  @P1_7_1_3.block_append 5771 1240 5336 5592 256 256 512 1770361754240 1582376020343 3352737774583 cost_5771_1240_join0_32 cost_5771_1240_join0_34 rfl rfl rfl

private theorem cost_5771_1240_join1_18 : P1_7_1_3.blockEstimate 5771 1240 5848 512 = 2500581082101 :=
  @P1_7_1_3.block_append 5771 1240 5848 6104 256 256 512 1363666190715 1136914891386 2500581082101 cost_5771_1240_join0_36 cost_5771_1240_join0_38 rfl rfl rfl

private theorem cost_5771_1240_join1_20 : P1_7_1_3.blockEstimate 5771 1240 6360 512 = 1610589001530 :=
  @P1_7_1_3.block_append 5771 1240 6360 6616 256 256 512 912383488747 698205512783 1610589001530 cost_5771_1240_join0_40 cost_5771_1240_join0_42 rfl rfl rfl

private theorem cost_5771_1240_join1_22 : P1_7_1_3.blockEstimate 5771 1240 6872 512 = 830208742074 :=
  @P1_7_1_3.block_append 5771 1240 6872 7128 256 256 512 501575393274 328633348800 830208742074 cost_5771_1240_join0_44 cost_5771_1240_join0_46 rfl rfl rfl

private theorem cost_5771_1240_join1_24 : P1_7_1_3.blockEstimate 5771 1240 7384 512 = 271735833984 :=
  @P1_7_1_3.block_append 5771 1240 7384 7640 256 256 512 187864683200 83871150784 271735833984 cost_5771_1240_join0_48 cost_5771_1240_join0_50 rfl rfl rfl

private theorem cost_5771_1240_join1_26 : P1_7_1_3.blockEstimate 5771 1240 7896 355 = 21163497167 :=
  @P1_7_1_3.block_append 5771 1240 7896 8152 256 99 355 20679283392 484213775 21163497167 cost_5771_1240_join0_52 cost_5771_1240_block54 rfl rfl rfl

private theorem cost_5771_1240_join2_0 : P1_7_1_3.blockEstimate 5771 1240 1240 1024 = 898081056000 :=
  @P1_7_1_3.block_append 5771 1240 1240 1752 512 512 1024 121229030016 776852025984 898081056000 cost_5771_1240_join1_0 cost_5771_1240_join1_2 rfl rfl rfl

private theorem cost_5771_1240_join2_2 : P1_7_1_3.blockEstimate 5771 1240 2264 1024 = 4829815176058 :=
  @P1_7_1_3.block_append 5771 1240 2264 2776 512 512 1024 1878979434106 2950835741952 4829815176058 cost_5771_1240_join1_4 cost_5771_1240_join1_6 rfl rfl rfl

private theorem cost_5771_1240_join2_4 : P1_7_1_3.blockEstimate 5771 1240 3288 1024 = 7808376130048 :=
  @P1_7_1_3.block_append 5771 1240 3288 3800 512 512 1024 3697446757632 4110929372416 7808376130048 cost_5771_1240_join1_8 cost_5771_1240_join1_10 rfl rfl rfl

private theorem cost_5771_1240_join2_6 : P1_7_1_3.blockEstimate 5771 1240 4312 1024 = 8129792985600 :=
  @P1_7_1_3.block_append 5771 1240 4312 4824 512 512 1024 4191283586304 3938509399296 8129792985600 cost_5771_1240_join1_12 cost_5771_1240_join1_14 rfl rfl rfl

private theorem cost_5771_1240_join2_8 : P1_7_1_3.blockEstimate 5771 1240 5336 1024 = 5853318856684 :=
  @P1_7_1_3.block_append 5771 1240 5336 5848 512 512 1024 3352737774583 2500581082101 5853318856684 cost_5771_1240_join1_16 cost_5771_1240_join1_18 rfl rfl rfl

private theorem cost_5771_1240_join2_10 : P1_7_1_3.blockEstimate 5771 1240 6360 1024 = 2440797743604 :=
  @P1_7_1_3.block_append 5771 1240 6360 6872 512 512 1024 1610589001530 830208742074 2440797743604 cost_5771_1240_join1_20 cost_5771_1240_join1_22 rfl rfl rfl

private theorem cost_5771_1240_join2_12 : P1_7_1_3.blockEstimate 5771 1240 7384 867 = 292899331151 :=
  @P1_7_1_3.block_append 5771 1240 7384 7896 512 355 867 271735833984 21163497167 292899331151 cost_5771_1240_join1_24 cost_5771_1240_join1_26 rfl rfl rfl

private theorem cost_5771_1240_join3_0 : P1_7_1_3.blockEstimate 5771 1240 1240 2048 = 5727896232058 :=
  @P1_7_1_3.block_append 5771 1240 1240 2264 1024 1024 2048 898081056000 4829815176058 5727896232058 cost_5771_1240_join2_0 cost_5771_1240_join2_2 rfl rfl rfl

private theorem cost_5771_1240_join3_2 : P1_7_1_3.blockEstimate 5771 1240 3288 2048 = 15938169115648 :=
  @P1_7_1_3.block_append 5771 1240 3288 4312 1024 1024 2048 7808376130048 8129792985600 15938169115648 cost_5771_1240_join2_4 cost_5771_1240_join2_6 rfl rfl rfl

private theorem cost_5771_1240_join3_4 : P1_7_1_3.blockEstimate 5771 1240 5336 2048 = 8294116600288 :=
  @P1_7_1_3.block_append 5771 1240 5336 6360 1024 1024 2048 5853318856684 2440797743604 8294116600288 cost_5771_1240_join2_8 cost_5771_1240_join2_10 rfl rfl rfl

private theorem cost_5771_1240_join4_0 : P1_7_1_3.blockEstimate 5771 1240 1240 4096 = 21666065347706 :=
  @P1_7_1_3.block_append 5771 1240 1240 3288 2048 2048 4096 5727896232058 15938169115648 21666065347706 cost_5771_1240_join3_0 cost_5771_1240_join3_2 rfl rfl rfl

private theorem cost_5771_1240_join4_2 : P1_7_1_3.blockEstimate 5771 1240 5336 2915 = 8587015931439 :=
  @P1_7_1_3.block_append 5771 1240 5336 7384 2048 867 2915 8294116600288 292899331151 8587015931439 cost_5771_1240_join3_4 cost_5771_1240_join2_12 rfl rfl rfl

private theorem cost_5771_1240_join5_0 : P1_7_1_3.blockEstimate 5771 1240 1240 7011 = 30253081279145 :=
  @P1_7_1_3.block_append 5771 1240 1240 5336 4096 2915 7011 21666065347706 8587015931439 30253081279145 cost_5771_1240_join4_0 cost_5771_1240_join4_2 rfl rfl rfl

private theorem cost_5771_1240_total : P1_7_1_3.momentEstimate 5771 1240 = 30253081279145 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 5771 + 1240 = 7011 by decide]
  exact cost_5771_1240_join5_0

theorem moment5771_1240 : P1_7_1.groupedPoleMoment 5771 1240 ≤ 30253081279145 :=
  (P1_7_1_3.grouped_bound 5771 1240).trans_eq cost_5771_1240_total

end Research6966.HelperRescueCatalogue

end Merged6967_Near6967RescueMoment28

section Merged6967_Near6967RescueMoment29
set_option Elab.async false


set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private theorem cost_5959_1281_block0 : P1_7_1_3.blockEstimate 5959 1281 1281 128 = 2097815200 := by decide +kernel

private theorem cost_5959_1281_block1 : P1_7_1_3.blockEstimate 5959 1281 1409 128 = 14219472544 := by decide +kernel

private theorem cost_5959_1281_block2 : P1_7_1_3.blockEstimate 5959 1281 1537 128 = 37626953376 := by decide +kernel

private theorem cost_5959_1281_block3 : P1_7_1_3.blockEstimate 5959 1281 1665 128 = 71514951328 := by decide +kernel

private theorem cost_5959_1281_block4 : P1_7_1_3.blockEstimate 5959 1281 1793 128 = 115078160032 := by decide +kernel

private theorem cost_5959_1281_block5 : P1_7_1_3.blockEstimate 5959 1281 1921 128 = 167511273120 := by decide +kernel

private theorem cost_5959_1281_block6 : P1_7_1_3.blockEstimate 5959 1281 2049 128 = 228008984224 := by decide +kernel

private theorem cost_5959_1281_block7 : P1_7_1_3.blockEstimate 5959 1281 2177 128 = 295765986976 := by decide +kernel

private theorem cost_5959_1281_block8 : P1_7_1_3.blockEstimate 5959 1281 2305 128 = 369976975008 := by decide +kernel

private theorem cost_5959_1281_block9 : P1_7_1_3.blockEstimate 5959 1281 2433 128 = 449836641952 := by decide +kernel

private theorem cost_5959_1281_block10 : P1_7_1_3.blockEstimate 5959 1281 2561 128 = 532975069888 := by decide +kernel

private theorem cost_5959_1281_block11 : P1_7_1_3.blockEstimate 5959 1281 2689 128 = 612444793536 := by decide +kernel

private theorem cost_5959_1281_block12 : P1_7_1_3.blockEstimate 5959 1281 2817 128 = 686537419456 := by decide +kernel

private theorem cost_5959_1281_block13 : P1_7_1_3.blockEstimate 5959 1281 2945 128 = 755252947648 := by decide +kernel

private theorem cost_5959_1281_block14 : P1_7_1_3.blockEstimate 5959 1281 3073 128 = 818591378112 := by decide +kernel

private theorem cost_5959_1281_block15 : P1_7_1_3.blockEstimate 5959 1281 3201 128 = 876552710848 := by decide +kernel

private theorem cost_5959_1281_block16 : P1_7_1_3.blockEstimate 5959 1281 3329 128 = 929136945856 := by decide +kernel

private theorem cost_5959_1281_block17 : P1_7_1_3.blockEstimate 5959 1281 3457 128 = 976344083136 := by decide +kernel

private theorem cost_5959_1281_block18 : P1_7_1_3.blockEstimate 5959 1281 3585 128 = 1018174122688 := by decide +kernel

private theorem cost_5959_1281_block19 : P1_7_1_3.blockEstimate 5959 1281 3713 128 = 1054627064512 := by decide +kernel

private theorem cost_5959_1281_block20 : P1_7_1_3.blockEstimate 5959 1281 3841 128 = 1085702908608 := by decide +kernel

private theorem cost_5959_1281_block21 : P1_7_1_3.blockEstimate 5959 1281 3969 128 = 1111401654976 := by decide +kernel

private theorem cost_5959_1281_block22 : P1_7_1_3.blockEstimate 5959 1281 4097 128 = 1131723303616 := by decide +kernel

private theorem cost_5959_1281_block23 : P1_7_1_3.blockEstimate 5959 1281 4225 128 = 1146667854528 := by decide +kernel

private theorem cost_5959_1281_block24 : P1_7_1_3.blockEstimate 5959 1281 4353 128 = 1156235307712 := by decide +kernel

private theorem cost_5959_1281_block25 : P1_7_1_3.blockEstimate 5959 1281 4481 128 = 1160425663168 := by decide +kernel

private theorem cost_5959_1281_block26 : P1_7_1_3.blockEstimate 5959 1281 4609 128 = 1159238920896 := by decide +kernel

private theorem cost_5959_1281_block27 : P1_7_1_3.blockEstimate 5959 1281 4737 128 = 1152675080896 := by decide +kernel

private theorem cost_5959_1281_block28 : P1_7_1_3.blockEstimate 5959 1281 4865 128 = 1140734143168 := by decide +kernel

private theorem cost_5959_1281_block29 : P1_7_1_3.blockEstimate 5959 1281 4993 128 = 1123416107712 := by decide +kernel

private theorem cost_5959_1281_block30 : P1_7_1_3.blockEstimate 5959 1281 5121 128 = 1100720974528 := by decide +kernel

private theorem cost_5959_1281_block31 : P1_7_1_3.blockEstimate 5959 1281 5249 128 = 1072648743616 := by decide +kernel

private theorem cost_5959_1281_block32 : P1_7_1_3.blockEstimate 5959 1281 5377 128 = 1039199414976 := by decide +kernel

private theorem cost_5959_1281_block33 : P1_7_1_3.blockEstimate 5959 1281 5505 128 = 1000372988608 := by decide +kernel

private theorem cost_5959_1281_block34 : P1_7_1_3.blockEstimate 5959 1281 5633 128 = 956169464512 := by decide +kernel

private theorem cost_5959_1281_block35 : P1_7_1_3.blockEstimate 5959 1281 5761 128 = 906588842688 := by decide +kernel

private theorem cost_5959_1281_block36 : P1_7_1_3.blockEstimate 5959 1281 5889 128 = 851688848941 := by decide +kernel

private theorem cost_5959_1281_block37 : P1_7_1_3.blockEstimate 5959 1281 6017 128 = 793186843864 := by decide +kernel

private theorem cost_5959_1281_block38 : P1_7_1_3.blockEstimate 5959 1281 6145 128 = 733342758954 := by decide +kernel

private theorem cost_5959_1281_block39 : P1_7_1_3.blockEstimate 5959 1281 6273 128 = 672824065602 := by decide +kernel

private theorem cost_5959_1281_block40 : P1_7_1_3.blockEstimate 5959 1281 6401 128 = 612185354676 := by decide +kernel

private theorem cost_5959_1281_block41 : P1_7_1_3.blockEstimate 5959 1281 6529 128 = 551961115158 := by decide +kernel

private theorem cost_5959_1281_block42 : P1_7_1_3.blockEstimate 5959 1281 6657 128 = 492665734780 := by decide +kernel

private theorem cost_5959_1281_block43 : P1_7_1_3.blockEstimate 5959 1281 6785 128 = 434793500315 := by decide +kernel

private theorem cost_5959_1281_block44 : P1_7_1_3.blockEstimate 5959 1281 6913 128 = 378818596995 := by decide +kernel

private theorem cost_5959_1281_block45 : P1_7_1_3.blockEstimate 5959 1281 7041 128 = 325195109025 := by decide +kernel

private theorem cost_5959_1281_block46 : P1_7_1_3.blockEstimate 5959 1281 7169 128 = 274279234781 := by decide +kernel

private theorem cost_5959_1281_block47 : P1_7_1_3.blockEstimate 5959 1281 7297 128 = 226139129952 := by decide +kernel

private theorem cost_5959_1281_block48 : P1_7_1_3.blockEstimate 5959 1281 7425 128 = 181822646368 := by decide +kernel

private theorem cost_5959_1281_block49 : P1_7_1_3.blockEstimate 5959 1281 7553 128 = 141724125280 := by decide +kernel

private theorem cost_5959_1281_block50 : P1_7_1_3.blockEstimate 5959 1281 7681 128 = 106095224928 := by decide +kernel

private theorem cost_5959_1281_block51 : P1_7_1_3.blockEstimate 5959 1281 7809 128 = 75187603552 := by decide +kernel

private theorem cost_5959_1281_block52 : P1_7_1_3.blockEstimate 5959 1281 7937 128 = 49252919392 := by decide +kernel

private theorem cost_5959_1281_block53 : P1_7_1_3.blockEstimate 5959 1281 8065 128 = 28542830688 := by decide +kernel

private theorem cost_5959_1281_block54 : P1_7_1_3.blockEstimate 5959 1281 8193 128 = 13308995680 := by decide +kernel

private theorem cost_5959_1281_block55 : P1_7_1_3.blockEstimate 5959 1281 8321 128 = 3803072608 := by decide +kernel

private theorem cost_5959_1281_block56 : P1_7_1_3.blockEstimate 5959 1281 8449 72 = 196017342 := by decide +kernel

private theorem cost_5959_1281_join0_0 : P1_7_1_3.blockEstimate 5959 1281 1281 256 = 16317287744 :=
  @P1_7_1_3.block_append 5959 1281 1281 1409 128 128 256 2097815200 14219472544 16317287744 cost_5959_1281_block0 cost_5959_1281_block1 rfl rfl rfl

private theorem cost_5959_1281_join0_2 : P1_7_1_3.blockEstimate 5959 1281 1537 256 = 109141904704 :=
  @P1_7_1_3.block_append 5959 1281 1537 1665 128 128 256 37626953376 71514951328 109141904704 cost_5959_1281_block2 cost_5959_1281_block3 rfl rfl rfl

private theorem cost_5959_1281_join0_4 : P1_7_1_3.blockEstimate 5959 1281 1793 256 = 282589433152 :=
  @P1_7_1_3.block_append 5959 1281 1793 1921 128 128 256 115078160032 167511273120 282589433152 cost_5959_1281_block4 cost_5959_1281_block5 rfl rfl rfl

private theorem cost_5959_1281_join0_6 : P1_7_1_3.blockEstimate 5959 1281 2049 256 = 523774971200 :=
  @P1_7_1_3.block_append 5959 1281 2049 2177 128 128 256 228008984224 295765986976 523774971200 cost_5959_1281_block6 cost_5959_1281_block7 rfl rfl rfl

private theorem cost_5959_1281_join0_8 : P1_7_1_3.blockEstimate 5959 1281 2305 256 = 819813616960 :=
  @P1_7_1_3.block_append 5959 1281 2305 2433 128 128 256 369976975008 449836641952 819813616960 cost_5959_1281_block8 cost_5959_1281_block9 rfl rfl rfl

private theorem cost_5959_1281_join0_10 : P1_7_1_3.blockEstimate 5959 1281 2561 256 = 1145419863424 :=
  @P1_7_1_3.block_append 5959 1281 2561 2689 128 128 256 532975069888 612444793536 1145419863424 cost_5959_1281_block10 cost_5959_1281_block11 rfl rfl rfl

private theorem cost_5959_1281_join0_12 : P1_7_1_3.blockEstimate 5959 1281 2817 256 = 1441790367104 :=
  @P1_7_1_3.block_append 5959 1281 2817 2945 128 128 256 686537419456 755252947648 1441790367104 cost_5959_1281_block12 cost_5959_1281_block13 rfl rfl rfl

private theorem cost_5959_1281_join0_14 : P1_7_1_3.blockEstimate 5959 1281 3073 256 = 1695144088960 :=
  @P1_7_1_3.block_append 5959 1281 3073 3201 128 128 256 818591378112 876552710848 1695144088960 cost_5959_1281_block14 cost_5959_1281_block15 rfl rfl rfl

private theorem cost_5959_1281_join0_16 : P1_7_1_3.blockEstimate 5959 1281 3329 256 = 1905481028992 :=
  @P1_7_1_3.block_append 5959 1281 3329 3457 128 128 256 929136945856 976344083136 1905481028992 cost_5959_1281_block16 cost_5959_1281_block17 rfl rfl rfl

private theorem cost_5959_1281_join0_18 : P1_7_1_3.blockEstimate 5959 1281 3585 256 = 2072801187200 :=
  @P1_7_1_3.block_append 5959 1281 3585 3713 128 128 256 1018174122688 1054627064512 2072801187200 cost_5959_1281_block18 cost_5959_1281_block19 rfl rfl rfl

private theorem cost_5959_1281_join0_20 : P1_7_1_3.blockEstimate 5959 1281 3841 256 = 2197104563584 :=
  @P1_7_1_3.block_append 5959 1281 3841 3969 128 128 256 1085702908608 1111401654976 2197104563584 cost_5959_1281_block20 cost_5959_1281_block21 rfl rfl rfl

private theorem cost_5959_1281_join0_22 : P1_7_1_3.blockEstimate 5959 1281 4097 256 = 2278391158144 :=
  @P1_7_1_3.block_append 5959 1281 4097 4225 128 128 256 1131723303616 1146667854528 2278391158144 cost_5959_1281_block22 cost_5959_1281_block23 rfl rfl rfl

private theorem cost_5959_1281_join0_24 : P1_7_1_3.blockEstimate 5959 1281 4353 256 = 2316660970880 :=
  @P1_7_1_3.block_append 5959 1281 4353 4481 128 128 256 1156235307712 1160425663168 2316660970880 cost_5959_1281_block24 cost_5959_1281_block25 rfl rfl rfl

private theorem cost_5959_1281_join0_26 : P1_7_1_3.blockEstimate 5959 1281 4609 256 = 2311914001792 :=
  @P1_7_1_3.block_append 5959 1281 4609 4737 128 128 256 1159238920896 1152675080896 2311914001792 cost_5959_1281_block26 cost_5959_1281_block27 rfl rfl rfl

private theorem cost_5959_1281_join0_28 : P1_7_1_3.blockEstimate 5959 1281 4865 256 = 2264150250880 :=
  @P1_7_1_3.block_append 5959 1281 4865 4993 128 128 256 1140734143168 1123416107712 2264150250880 cost_5959_1281_block28 cost_5959_1281_block29 rfl rfl rfl

private theorem cost_5959_1281_join0_30 : P1_7_1_3.blockEstimate 5959 1281 5121 256 = 2173369718144 :=
  @P1_7_1_3.block_append 5959 1281 5121 5249 128 128 256 1100720974528 1072648743616 2173369718144 cost_5959_1281_block30 cost_5959_1281_block31 rfl rfl rfl

private theorem cost_5959_1281_join0_32 : P1_7_1_3.blockEstimate 5959 1281 5377 256 = 2039572403584 :=
  @P1_7_1_3.block_append 5959 1281 5377 5505 128 128 256 1039199414976 1000372988608 2039572403584 cost_5959_1281_block32 cost_5959_1281_block33 rfl rfl rfl

private theorem cost_5959_1281_join0_34 : P1_7_1_3.blockEstimate 5959 1281 5633 256 = 1862758307200 :=
  @P1_7_1_3.block_append 5959 1281 5633 5761 128 128 256 956169464512 906588842688 1862758307200 cost_5959_1281_block34 cost_5959_1281_block35 rfl rfl rfl

private theorem cost_5959_1281_join0_36 : P1_7_1_3.blockEstimate 5959 1281 5889 256 = 1644875692805 :=
  @P1_7_1_3.block_append 5959 1281 5889 6017 128 128 256 851688848941 793186843864 1644875692805 cost_5959_1281_block36 cost_5959_1281_block37 rfl rfl rfl

private theorem cost_5959_1281_join0_38 : P1_7_1_3.blockEstimate 5959 1281 6145 256 = 1406166824556 :=
  @P1_7_1_3.block_append 5959 1281 6145 6273 128 128 256 733342758954 672824065602 1406166824556 cost_5959_1281_block38 cost_5959_1281_block39 rfl rfl rfl

private theorem cost_5959_1281_join0_40 : P1_7_1_3.blockEstimate 5959 1281 6401 256 = 1164146469834 :=
  @P1_7_1_3.block_append 5959 1281 6401 6529 128 128 256 612185354676 551961115158 1164146469834 cost_5959_1281_block40 cost_5959_1281_block41 rfl rfl rfl

private theorem cost_5959_1281_join0_42 : P1_7_1_3.blockEstimate 5959 1281 6657 256 = 927459235095 :=
  @P1_7_1_3.block_append 5959 1281 6657 6785 128 128 256 492665734780 434793500315 927459235095 cost_5959_1281_block42 cost_5959_1281_block43 rfl rfl rfl

private theorem cost_5959_1281_join0_44 : P1_7_1_3.blockEstimate 5959 1281 6913 256 = 704013706020 :=
  @P1_7_1_3.block_append 5959 1281 6913 7041 128 128 256 378818596995 325195109025 704013706020 cost_5959_1281_block44 cost_5959_1281_block45 rfl rfl rfl

private theorem cost_5959_1281_join0_46 : P1_7_1_3.blockEstimate 5959 1281 7169 256 = 500418364733 :=
  @P1_7_1_3.block_append 5959 1281 7169 7297 128 128 256 274279234781 226139129952 500418364733 cost_5959_1281_block46 cost_5959_1281_block47 rfl rfl rfl

private theorem cost_5959_1281_join0_48 : P1_7_1_3.blockEstimate 5959 1281 7425 256 = 323546771648 :=
  @P1_7_1_3.block_append 5959 1281 7425 7553 128 128 256 181822646368 141724125280 323546771648 cost_5959_1281_block48 cost_5959_1281_block49 rfl rfl rfl

private theorem cost_5959_1281_join0_50 : P1_7_1_3.blockEstimate 5959 1281 7681 256 = 181282828480 :=
  @P1_7_1_3.block_append 5959 1281 7681 7809 128 128 256 106095224928 75187603552 181282828480 cost_5959_1281_block50 cost_5959_1281_block51 rfl rfl rfl

private theorem cost_5959_1281_join0_52 : P1_7_1_3.blockEstimate 5959 1281 7937 256 = 77795750080 :=
  @P1_7_1_3.block_append 5959 1281 7937 8065 128 128 256 49252919392 28542830688 77795750080 cost_5959_1281_block52 cost_5959_1281_block53 rfl rfl rfl

private theorem cost_5959_1281_join0_54 : P1_7_1_3.blockEstimate 5959 1281 8193 256 = 17112068288 :=
  @P1_7_1_3.block_append 5959 1281 8193 8321 128 128 256 13308995680 3803072608 17112068288 cost_5959_1281_block54 cost_5959_1281_block55 rfl rfl rfl

private theorem cost_5959_1281_join1_0 : P1_7_1_3.blockEstimate 5959 1281 1281 512 = 125459192448 :=
  @P1_7_1_3.block_append 5959 1281 1281 1537 256 256 512 16317287744 109141904704 125459192448 cost_5959_1281_join0_0 cost_5959_1281_join0_2 rfl rfl rfl

private theorem cost_5959_1281_join1_2 : P1_7_1_3.blockEstimate 5959 1281 1793 512 = 806364404352 :=
  @P1_7_1_3.block_append 5959 1281 1793 2049 256 256 512 282589433152 523774971200 806364404352 cost_5959_1281_join0_4 cost_5959_1281_join0_6 rfl rfl rfl

private theorem cost_5959_1281_join1_4 : P1_7_1_3.blockEstimate 5959 1281 2305 512 = 1965233480384 :=
  @P1_7_1_3.block_append 5959 1281 2305 2561 256 256 512 819813616960 1145419863424 1965233480384 cost_5959_1281_join0_8 cost_5959_1281_join0_10 rfl rfl rfl

private theorem cost_5959_1281_join1_6 : P1_7_1_3.blockEstimate 5959 1281 2817 512 = 3136934456064 :=
  @P1_7_1_3.block_append 5959 1281 2817 3073 256 256 512 1441790367104 1695144088960 3136934456064 cost_5959_1281_join0_12 cost_5959_1281_join0_14 rfl rfl rfl

private theorem cost_5959_1281_join1_8 : P1_7_1_3.blockEstimate 5959 1281 3329 512 = 3978282216192 :=
  @P1_7_1_3.block_append 5959 1281 3329 3585 256 256 512 1905481028992 2072801187200 3978282216192 cost_5959_1281_join0_16 cost_5959_1281_join0_18 rfl rfl rfl

private theorem cost_5959_1281_join1_10 : P1_7_1_3.blockEstimate 5959 1281 3841 512 = 4475495721728 :=
  @P1_7_1_3.block_append 5959 1281 3841 4097 256 256 512 2197104563584 2278391158144 4475495721728 cost_5959_1281_join0_20 cost_5959_1281_join0_22 rfl rfl rfl

private theorem cost_5959_1281_join1_12 : P1_7_1_3.blockEstimate 5959 1281 4353 512 = 4628574972672 :=
  @P1_7_1_3.block_append 5959 1281 4353 4609 256 256 512 2316660970880 2311914001792 4628574972672 cost_5959_1281_join0_24 cost_5959_1281_join0_26 rfl rfl rfl

private theorem cost_5959_1281_join1_14 : P1_7_1_3.blockEstimate 5959 1281 4865 512 = 4437519969024 :=
  @P1_7_1_3.block_append 5959 1281 4865 5121 256 256 512 2264150250880 2173369718144 4437519969024 cost_5959_1281_join0_28 cost_5959_1281_join0_30 rfl rfl rfl

private theorem cost_5959_1281_join1_16 : P1_7_1_3.blockEstimate 5959 1281 5377 512 = 3902330710784 :=
  @P1_7_1_3.block_append 5959 1281 5377 5633 256 256 512 2039572403584 1862758307200 3902330710784 cost_5959_1281_join0_32 cost_5959_1281_join0_34 rfl rfl rfl

private theorem cost_5959_1281_join1_18 : P1_7_1_3.blockEstimate 5959 1281 5889 512 = 3051042517361 :=
  @P1_7_1_3.block_append 5959 1281 5889 6145 256 256 512 1644875692805 1406166824556 3051042517361 cost_5959_1281_join0_36 cost_5959_1281_join0_38 rfl rfl rfl

private theorem cost_5959_1281_join1_20 : P1_7_1_3.blockEstimate 5959 1281 6401 512 = 2091605704929 :=
  @P1_7_1_3.block_append 5959 1281 6401 6657 256 256 512 1164146469834 927459235095 2091605704929 cost_5959_1281_join0_40 cost_5959_1281_join0_42 rfl rfl rfl

private theorem cost_5959_1281_join1_22 : P1_7_1_3.blockEstimate 5959 1281 6913 512 = 1204432070753 :=
  @P1_7_1_3.block_append 5959 1281 6913 7169 256 256 512 704013706020 500418364733 1204432070753 cost_5959_1281_join0_44 cost_5959_1281_join0_46 rfl rfl rfl

private theorem cost_5959_1281_join1_24 : P1_7_1_3.blockEstimate 5959 1281 7425 512 = 504829600128 :=
  @P1_7_1_3.block_append 5959 1281 7425 7681 256 256 512 323546771648 181282828480 504829600128 cost_5959_1281_join0_48 cost_5959_1281_join0_50 rfl rfl rfl

private theorem cost_5959_1281_join1_26 : P1_7_1_3.blockEstimate 5959 1281 7937 512 = 94907818368 :=
  @P1_7_1_3.block_append 5959 1281 7937 8193 256 256 512 77795750080 17112068288 94907818368 cost_5959_1281_join0_52 cost_5959_1281_join0_54 rfl rfl rfl

private theorem cost_5959_1281_join2_0 : P1_7_1_3.blockEstimate 5959 1281 1281 1024 = 931823596800 :=
  @P1_7_1_3.block_append 5959 1281 1281 1793 512 512 1024 125459192448 806364404352 931823596800 cost_5959_1281_join1_0 cost_5959_1281_join1_2 rfl rfl rfl

private theorem cost_5959_1281_join2_2 : P1_7_1_3.blockEstimate 5959 1281 2305 1024 = 5102167936448 :=
  @P1_7_1_3.block_append 5959 1281 2305 2817 512 512 1024 1965233480384 3136934456064 5102167936448 cost_5959_1281_join1_4 cost_5959_1281_join1_6 rfl rfl rfl

private theorem cost_5959_1281_join2_4 : P1_7_1_3.blockEstimate 5959 1281 3329 1024 = 8453777937920 :=
  @P1_7_1_3.block_append 5959 1281 3329 3841 512 512 1024 3978282216192 4475495721728 8453777937920 cost_5959_1281_join1_8 cost_5959_1281_join1_10 rfl rfl rfl

private theorem cost_5959_1281_join2_6 : P1_7_1_3.blockEstimate 5959 1281 4353 1024 = 9066094941696 :=
  @P1_7_1_3.block_append 5959 1281 4353 4865 512 512 1024 4628574972672 4437519969024 9066094941696 cost_5959_1281_join1_12 cost_5959_1281_join1_14 rfl rfl rfl

private theorem cost_5959_1281_join2_8 : P1_7_1_3.blockEstimate 5959 1281 5377 1024 = 6953373228145 :=
  @P1_7_1_3.block_append 5959 1281 5377 5889 512 512 1024 3902330710784 3051042517361 6953373228145 cost_5959_1281_join1_16 cost_5959_1281_join1_18 rfl rfl rfl

private theorem cost_5959_1281_join2_10 : P1_7_1_3.blockEstimate 5959 1281 6401 1024 = 3296037775682 :=
  @P1_7_1_3.block_append 5959 1281 6401 6913 512 512 1024 2091605704929 1204432070753 3296037775682 cost_5959_1281_join1_20 cost_5959_1281_join1_22 rfl rfl rfl

private theorem cost_5959_1281_join2_12 : P1_7_1_3.blockEstimate 5959 1281 7425 1024 = 599737418496 :=
  @P1_7_1_3.block_append 5959 1281 7425 7937 512 512 1024 504829600128 94907818368 599737418496 cost_5959_1281_join1_24 cost_5959_1281_join1_26 rfl rfl rfl

private theorem cost_5959_1281_join3_0 : P1_7_1_3.blockEstimate 5959 1281 1281 2048 = 6033991533248 :=
  @P1_7_1_3.block_append 5959 1281 1281 2305 1024 1024 2048 931823596800 5102167936448 6033991533248 cost_5959_1281_join2_0 cost_5959_1281_join2_2 rfl rfl rfl

private theorem cost_5959_1281_join3_2 : P1_7_1_3.blockEstimate 5959 1281 3329 2048 = 17519872879616 :=
  @P1_7_1_3.block_append 5959 1281 3329 4353 1024 1024 2048 8453777937920 9066094941696 17519872879616 cost_5959_1281_join2_4 cost_5959_1281_join2_6 rfl rfl rfl

private theorem cost_5959_1281_join3_4 : P1_7_1_3.blockEstimate 5959 1281 5377 2048 = 10249411003827 :=
  @P1_7_1_3.block_append 5959 1281 5377 6401 1024 1024 2048 6953373228145 3296037775682 10249411003827 cost_5959_1281_join2_8 cost_5959_1281_join2_10 rfl rfl rfl

private theorem cost_5959_1281_join3_6 : P1_7_1_3.blockEstimate 5959 1281 7425 1096 = 599933435838 :=
  @P1_7_1_3.block_append 5959 1281 7425 8449 1024 72 1096 599737418496 196017342 599933435838 cost_5959_1281_join2_12 cost_5959_1281_block56 rfl rfl rfl

private theorem cost_5959_1281_join4_0 : P1_7_1_3.blockEstimate 5959 1281 1281 4096 = 23553864412864 :=
  @P1_7_1_3.block_append 5959 1281 1281 3329 2048 2048 4096 6033991533248 17519872879616 23553864412864 cost_5959_1281_join3_0 cost_5959_1281_join3_2 rfl rfl rfl

private theorem cost_5959_1281_join4_2 : P1_7_1_3.blockEstimate 5959 1281 5377 3144 = 10849344439665 :=
  @P1_7_1_3.block_append 5959 1281 5377 7425 2048 1096 3144 10249411003827 599933435838 10849344439665 cost_5959_1281_join3_4 cost_5959_1281_join3_6 rfl rfl rfl

private theorem cost_5959_1281_join5_0 : P1_7_1_3.blockEstimate 5959 1281 1281 7240 = 34403208852529 :=
  @P1_7_1_3.block_append 5959 1281 1281 5377 4096 3144 7240 23553864412864 10849344439665 34403208852529 cost_5959_1281_join4_0 cost_5959_1281_join4_2 rfl rfl rfl

private theorem cost_5959_1281_total : P1_7_1_3.momentEstimate 5959 1281 = 34403208852529 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 5959 + 1281 = 7240 by decide]
  exact cost_5959_1281_join5_0

theorem moment5959_1281 : P1_7_1.groupedPoleMoment 5959 1281 ≤ 34403208852529 :=
  (P1_7_1_3.grouped_bound 5959 1281).trans_eq cost_5959_1281_total
private theorem cost_5961_1281_block0 : P1_7_1_3.blockEstimate 5961 1281 1281 128 = 2098530720 := by decide +kernel

private theorem cost_5961_1281_block1 : P1_7_1_3.blockEstimate 5961 1281 1409 128 = 14224415136 := by decide +kernel

private theorem cost_5961_1281_block2 : P1_7_1_3.blockEstimate 5961 1281 1537 128 = 37640317344 := by decide +kernel

private theorem cost_5961_1281_block3 : P1_7_1_3.blockEstimate 5961 1281 1665 128 = 71540930976 := by decide +kernel

private theorem cost_5961_1281_block4 : P1_7_1_3.blockEstimate 5961 1281 1793 128 = 115120949664 := by decide +kernel

private theorem cost_5961_1281_block5 : P1_7_1_3.blockEstimate 5961 1281 1921 128 = 167575067040 := by decide +kernel

private theorem cost_5961_1281_block6 : P1_7_1_3.blockEstimate 5961 1281 2049 128 = 228097976736 := by decide +kernel

private theorem cost_5961_1281_block7 : P1_7_1_3.blockEstimate 5961 1281 2177 128 = 295884372384 := by decide +kernel

private theorem cost_5961_1281_block8 : P1_7_1_3.blockEstimate 5961 1281 2305 128 = 370128947616 := by decide +kernel

private theorem cost_5961_1281_block9 : P1_7_1_3.blockEstimate 5961 1281 2433 128 = 450026396064 := by decide +kernel

private theorem cost_5961_1281_block10 : P1_7_1_3.blockEstimate 5961 1281 2561 128 = 533206117056 := by decide +kernel

private theorem cost_5961_1281_block11 : P1_7_1_3.blockEstimate 5961 1281 2689 128 = 612717849280 := by decide +kernel

private theorem cost_5961_1281_block12 : P1_7_1_3.blockEstimate 5961 1281 2817 128 = 686852483776 := by decide +kernel

private theorem cost_5961_1281_block13 : P1_7_1_3.blockEstimate 5961 1281 2945 128 = 755610020544 := by decide +kernel

private theorem cost_5961_1281_block14 : P1_7_1_3.blockEstimate 5961 1281 3073 128 = 818990459584 := by decide +kernel

private theorem cost_5961_1281_block15 : P1_7_1_3.blockEstimate 5961 1281 3201 128 = 876993800896 := by decide +kernel

private theorem cost_5961_1281_block16 : P1_7_1_3.blockEstimate 5961 1281 3329 128 = 929620044480 := by decide +kernel

private theorem cost_5961_1281_block17 : P1_7_1_3.blockEstimate 5961 1281 3457 128 = 976869190336 := by decide +kernel

private theorem cost_5961_1281_block18 : P1_7_1_3.blockEstimate 5961 1281 3585 128 = 1018741238464 := by decide +kernel

private theorem cost_5961_1281_block19 : P1_7_1_3.blockEstimate 5961 1281 3713 128 = 1055236188864 := by decide +kernel

private theorem cost_5961_1281_block20 : P1_7_1_3.blockEstimate 5961 1281 3841 128 = 1086354041536 := by decide +kernel

private theorem cost_5961_1281_block21 : P1_7_1_3.blockEstimate 5961 1281 3969 128 = 1112094796480 := by decide +kernel

private theorem cost_5961_1281_block22 : P1_7_1_3.blockEstimate 5961 1281 4097 128 = 1132458453696 := by decide +kernel

private theorem cost_5961_1281_block23 : P1_7_1_3.blockEstimate 5961 1281 4225 128 = 1147445013184 := by decide +kernel

private theorem cost_5961_1281_block24 : P1_7_1_3.blockEstimate 5961 1281 4353 128 = 1157054474944 := by decide +kernel

private theorem cost_5961_1281_block25 : P1_7_1_3.blockEstimate 5961 1281 4481 128 = 1161286838976 := by decide +kernel

private theorem cost_5961_1281_block26 : P1_7_1_3.blockEstimate 5961 1281 4609 128 = 1160142105280 := by decide +kernel

private theorem cost_5961_1281_block27 : P1_7_1_3.blockEstimate 5961 1281 4737 128 = 1153620273856 := by decide +kernel

private theorem cost_5961_1281_block28 : P1_7_1_3.blockEstimate 5961 1281 4865 128 = 1141721344704 := by decide +kernel

private theorem cost_5961_1281_block29 : P1_7_1_3.blockEstimate 5961 1281 4993 128 = 1124445317824 := by decide +kernel

private theorem cost_5961_1281_block30 : P1_7_1_3.blockEstimate 5961 1281 5121 128 = 1101792193216 := by decide +kernel

private theorem cost_5961_1281_block31 : P1_7_1_3.blockEstimate 5961 1281 5249 128 = 1073761970880 := by decide +kernel

private theorem cost_5961_1281_block32 : P1_7_1_3.blockEstimate 5961 1281 5377 128 = 1040354650816 := by decide +kernel

private theorem cost_5961_1281_block33 : P1_7_1_3.blockEstimate 5961 1281 5505 128 = 1001570233024 := by decide +kernel

private theorem cost_5961_1281_block34 : P1_7_1_3.blockEstimate 5961 1281 5633 128 = 957408717504 := by decide +kernel

private theorem cost_5961_1281_block35 : P1_7_1_3.blockEstimate 5961 1281 5761 128 = 907870104256 := by decide +kernel

private theorem cost_5961_1281_block36 : P1_7_1_3.blockEstimate 5961 1281 5889 128 = 853006392948 := by decide +kernel

private theorem cost_5961_1281_block37 : P1_7_1_3.blockEstimate 5961 1281 6017 128 = 794495729250 := by decide +kernel

private theorem cost_5961_1281_block38 : P1_7_1_3.blockEstimate 5961 1281 6145 128 = 734627706903 := by decide +kernel

private theorem cost_5961_1281_block39 : P1_7_1_3.blockEstimate 5961 1281 6273 128 = 674078348373 := by decide +kernel

private theorem cost_5961_1281_block40 : P1_7_1_3.blockEstimate 5961 1281 6401 128 = 613402558709 := by decide +kernel

private theorem cost_5961_1281_block41 : P1_7_1_3.blockEstimate 5961 1281 6529 128 = 553135140392 := by decide +kernel

private theorem cost_5961_1281_block42 : P1_7_1_3.blockEstimate 5961 1281 6657 128 = 493790795978 := by decide +kernel

private theorem cost_5961_1281_block43 : P1_7_1_3.blockEstimate 5961 1281 6785 128 = 435864125905 := by decide +kernel

private theorem cost_5961_1281_block44 : P1_7_1_3.blockEstimate 5961 1281 6913 128 = 379829629450 := by decide +kernel

private theorem cost_5961_1281_block45 : P1_7_1_3.blockEstimate 5961 1281 7041 128 = 326141705102 := by decide +kernel

private theorem cost_5961_1281_block46 : P1_7_1_3.blockEstimate 5961 1281 7169 128 = 275161951377 := by decide +kernel

private theorem cost_5961_1281_block47 : P1_7_1_3.blockEstimate 5961 1281 7297 128 = 226950427344 := by decide +kernel

private theorem cost_5961_1281_block48 : P1_7_1_3.blockEstimate 5961 1281 7425 128 = 182552020688 := by decide +kernel

private theorem cost_5961_1281_block49 : P1_7_1_3.blockEstimate 5961 1281 7553 128 = 142369741520 := by decide +kernel

private theorem cost_5961_1281_block50 : P1_7_1_3.blockEstimate 5961 1281 7681 128 = 106655248080 := by decide +kernel

private theorem cost_5961_1281_block51 : P1_7_1_3.blockEstimate 5961 1281 7809 128 = 75660198608 := by decide +kernel

private theorem cost_5961_1281_block52 : P1_7_1_3.blockEstimate 5961 1281 7937 128 = 49636251344 := by decide +kernel

private theorem cost_5961_1281_block53 : P1_7_1_3.blockEstimate 5961 1281 8065 128 = 28835064528 := by decide +kernel

private theorem cost_5961_1281_block54 : P1_7_1_3.blockEstimate 5961 1281 8193 128 = 13508296400 := by decide +kernel

private theorem cost_5961_1281_block55 : P1_7_1_3.blockEstimate 5961 1281 8321 128 = 3907605200 := by decide +kernel

private theorem cost_5961_1281_block56 : P1_7_1_3.blockEstimate 5961 1281 8449 74 = 212499857 := by decide +kernel

private theorem cost_5961_1281_join0_0 : P1_7_1_3.blockEstimate 5961 1281 1281 256 = 16322945856 :=
  @P1_7_1_3.block_append 5961 1281 1281 1409 128 128 256 2098530720 14224415136 16322945856 cost_5961_1281_block0 cost_5961_1281_block1 rfl rfl rfl

private theorem cost_5961_1281_join0_2 : P1_7_1_3.blockEstimate 5961 1281 1537 256 = 109181248320 :=
  @P1_7_1_3.block_append 5961 1281 1537 1665 128 128 256 37640317344 71540930976 109181248320 cost_5961_1281_block2 cost_5961_1281_block3 rfl rfl rfl

private theorem cost_5961_1281_join0_4 : P1_7_1_3.blockEstimate 5961 1281 1793 256 = 282696016704 :=
  @P1_7_1_3.block_append 5961 1281 1793 1921 128 128 256 115120949664 167575067040 282696016704 cost_5961_1281_block4 cost_5961_1281_block5 rfl rfl rfl

private theorem cost_5961_1281_join0_6 : P1_7_1_3.blockEstimate 5961 1281 2049 256 = 523982349120 :=
  @P1_7_1_3.block_append 5961 1281 2049 2177 128 128 256 228097976736 295884372384 523982349120 cost_5961_1281_block6 cost_5961_1281_block7 rfl rfl rfl

private theorem cost_5961_1281_join0_8 : P1_7_1_3.blockEstimate 5961 1281 2305 256 = 820155343680 :=
  @P1_7_1_3.block_append 5961 1281 2305 2433 128 128 256 370128947616 450026396064 820155343680 cost_5961_1281_block8 cost_5961_1281_block9 rfl rfl rfl

private theorem cost_5961_1281_join0_10 : P1_7_1_3.blockEstimate 5961 1281 2561 256 = 1145923966336 :=
  @P1_7_1_3.block_append 5961 1281 2561 2689 128 128 256 533206117056 612717849280 1145923966336 cost_5961_1281_block10 cost_5961_1281_block11 rfl rfl rfl

private theorem cost_5961_1281_join0_12 : P1_7_1_3.blockEstimate 5961 1281 2817 256 = 1442462504320 :=
  @P1_7_1_3.block_append 5961 1281 2817 2945 128 128 256 686852483776 755610020544 1442462504320 cost_5961_1281_block12 cost_5961_1281_block13 rfl rfl rfl

private theorem cost_5961_1281_join0_14 : P1_7_1_3.blockEstimate 5961 1281 3073 256 = 1695984260480 :=
  @P1_7_1_3.block_append 5961 1281 3073 3201 128 128 256 818990459584 876993800896 1695984260480 cost_5961_1281_block14 cost_5961_1281_block15 rfl rfl rfl

private theorem cost_5961_1281_join0_16 : P1_7_1_3.blockEstimate 5961 1281 3329 256 = 1906489234816 :=
  @P1_7_1_3.block_append 5961 1281 3329 3457 128 128 256 929620044480 976869190336 1906489234816 cost_5961_1281_block16 cost_5961_1281_block17 rfl rfl rfl

private theorem cost_5961_1281_join0_18 : P1_7_1_3.blockEstimate 5961 1281 3585 256 = 2073977427328 :=
  @P1_7_1_3.block_append 5961 1281 3585 3713 128 128 256 1018741238464 1055236188864 2073977427328 cost_5961_1281_block18 cost_5961_1281_block19 rfl rfl rfl

private theorem cost_5961_1281_join0_20 : P1_7_1_3.blockEstimate 5961 1281 3841 256 = 2198448838016 :=
  @P1_7_1_3.block_append 5961 1281 3841 3969 128 128 256 1086354041536 1112094796480 2198448838016 cost_5961_1281_block20 cost_5961_1281_block21 rfl rfl rfl

private theorem cost_5961_1281_join0_22 : P1_7_1_3.blockEstimate 5961 1281 4097 256 = 2279903466880 :=
  @P1_7_1_3.block_append 5961 1281 4097 4225 128 128 256 1132458453696 1147445013184 2279903466880 cost_5961_1281_block22 cost_5961_1281_block23 rfl rfl rfl

private theorem cost_5961_1281_join0_24 : P1_7_1_3.blockEstimate 5961 1281 4353 256 = 2318341313920 :=
  @P1_7_1_3.block_append 5961 1281 4353 4481 128 128 256 1157054474944 1161286838976 2318341313920 cost_5961_1281_block24 cost_5961_1281_block25 rfl rfl rfl

private theorem cost_5961_1281_join0_26 : P1_7_1_3.blockEstimate 5961 1281 4609 256 = 2313762379136 :=
  @P1_7_1_3.block_append 5961 1281 4609 4737 128 128 256 1160142105280 1153620273856 2313762379136 cost_5961_1281_block26 cost_5961_1281_block27 rfl rfl rfl

private theorem cost_5961_1281_join0_28 : P1_7_1_3.blockEstimate 5961 1281 4865 256 = 2266166662528 :=
  @P1_7_1_3.block_append 5961 1281 4865 4993 128 128 256 1141721344704 1124445317824 2266166662528 cost_5961_1281_block28 cost_5961_1281_block29 rfl rfl rfl

private theorem cost_5961_1281_join0_30 : P1_7_1_3.blockEstimate 5961 1281 5121 256 = 2175554164096 :=
  @P1_7_1_3.block_append 5961 1281 5121 5249 128 128 256 1101792193216 1073761970880 2175554164096 cost_5961_1281_block30 cost_5961_1281_block31 rfl rfl rfl

private theorem cost_5961_1281_join0_32 : P1_7_1_3.blockEstimate 5961 1281 5377 256 = 2041924883840 :=
  @P1_7_1_3.block_append 5961 1281 5377 5505 128 128 256 1040354650816 1001570233024 2041924883840 cost_5961_1281_block32 cost_5961_1281_block33 rfl rfl rfl

private theorem cost_5961_1281_join0_34 : P1_7_1_3.blockEstimate 5961 1281 5633 256 = 1865278821760 :=
  @P1_7_1_3.block_append 5961 1281 5633 5761 128 128 256 957408717504 907870104256 1865278821760 cost_5961_1281_block34 cost_5961_1281_block35 rfl rfl rfl

private theorem cost_5961_1281_join0_36 : P1_7_1_3.blockEstimate 5961 1281 5889 256 = 1647502122198 :=
  @P1_7_1_3.block_append 5961 1281 5889 6017 128 128 256 853006392948 794495729250 1647502122198 cost_5961_1281_block36 cost_5961_1281_block37 rfl rfl rfl

private theorem cost_5961_1281_join0_38 : P1_7_1_3.blockEstimate 5961 1281 6145 256 = 1408706055276 :=
  @P1_7_1_3.block_append 5961 1281 6145 6273 128 128 256 734627706903 674078348373 1408706055276 cost_5961_1281_block38 cost_5961_1281_block39 rfl rfl rfl

private theorem cost_5961_1281_join0_40 : P1_7_1_3.blockEstimate 5961 1281 6401 256 = 1166537699101 :=
  @P1_7_1_3.block_append 5961 1281 6401 6529 128 128 256 613402558709 553135140392 1166537699101 cost_5961_1281_block40 cost_5961_1281_block41 rfl rfl rfl

private theorem cost_5961_1281_join0_42 : P1_7_1_3.blockEstimate 5961 1281 6657 256 = 929654921883 :=
  @P1_7_1_3.block_append 5961 1281 6657 6785 128 128 256 493790795978 435864125905 929654921883 cost_5961_1281_block42 cost_5961_1281_block43 rfl rfl rfl

private theorem cost_5961_1281_join0_44 : P1_7_1_3.blockEstimate 5961 1281 6913 256 = 705971334552 :=
  @P1_7_1_3.block_append 5961 1281 6913 7041 128 128 256 379829629450 326141705102 705971334552 cost_5961_1281_block44 cost_5961_1281_block45 rfl rfl rfl

private theorem cost_5961_1281_join0_46 : P1_7_1_3.blockEstimate 5961 1281 7169 256 = 502112378721 :=
  @P1_7_1_3.block_append 5961 1281 7169 7297 128 128 256 275161951377 226950427344 502112378721 cost_5961_1281_block46 cost_5961_1281_block47 rfl rfl rfl

private theorem cost_5961_1281_join0_48 : P1_7_1_3.blockEstimate 5961 1281 7425 256 = 324921762208 :=
  @P1_7_1_3.block_append 5961 1281 7425 7553 128 128 256 182552020688 142369741520 324921762208 cost_5961_1281_block48 cost_5961_1281_block49 rfl rfl rfl

private theorem cost_5961_1281_join0_50 : P1_7_1_3.blockEstimate 5961 1281 7681 256 = 182315446688 :=
  @P1_7_1_3.block_append 5961 1281 7681 7809 128 128 256 106655248080 75660198608 182315446688 cost_5961_1281_block50 cost_5961_1281_block51 rfl rfl rfl

private theorem cost_5961_1281_join0_52 : P1_7_1_3.blockEstimate 5961 1281 7937 256 = 78471315872 :=
  @P1_7_1_3.block_append 5961 1281 7937 8065 128 128 256 49636251344 28835064528 78471315872 cost_5961_1281_block52 cost_5961_1281_block53 rfl rfl rfl

private theorem cost_5961_1281_join0_54 : P1_7_1_3.blockEstimate 5961 1281 8193 256 = 17415901600 :=
  @P1_7_1_3.block_append 5961 1281 8193 8321 128 128 256 13508296400 3907605200 17415901600 cost_5961_1281_block54 cost_5961_1281_block55 rfl rfl rfl

private theorem cost_5961_1281_join1_0 : P1_7_1_3.blockEstimate 5961 1281 1281 512 = 125504194176 :=
  @P1_7_1_3.block_append 5961 1281 1281 1537 256 256 512 16322945856 109181248320 125504194176 cost_5961_1281_join0_0 cost_5961_1281_join0_2 rfl rfl rfl

private theorem cost_5961_1281_join1_2 : P1_7_1_3.blockEstimate 5961 1281 1793 512 = 806678365824 :=
  @P1_7_1_3.block_append 5961 1281 1793 2049 256 256 512 282696016704 523982349120 806678365824 cost_5961_1281_join0_4 cost_5961_1281_join0_6 rfl rfl rfl

private theorem cost_5961_1281_join1_4 : P1_7_1_3.blockEstimate 5961 1281 2305 512 = 1966079310016 :=
  @P1_7_1_3.block_append 5961 1281 2305 2561 256 256 512 820155343680 1145923966336 1966079310016 cost_5961_1281_join0_8 cost_5961_1281_join0_10 rfl rfl rfl

private theorem cost_5961_1281_join1_6 : P1_7_1_3.blockEstimate 5961 1281 2817 512 = 3138446764800 :=
  @P1_7_1_3.block_append 5961 1281 2817 3073 256 256 512 1442462504320 1695984260480 3138446764800 cost_5961_1281_join0_12 cost_5961_1281_join0_14 rfl rfl rfl

private theorem cost_5961_1281_join1_8 : P1_7_1_3.blockEstimate 5961 1281 3329 512 = 3980466662144 :=
  @P1_7_1_3.block_append 5961 1281 3329 3585 256 256 512 1906489234816 2073977427328 3980466662144 cost_5961_1281_join0_16 cost_5961_1281_join0_18 rfl rfl rfl

private theorem cost_5961_1281_join1_10 : P1_7_1_3.blockEstimate 5961 1281 3841 512 = 4478352304896 :=
  @P1_7_1_3.block_append 5961 1281 3841 4097 256 256 512 2198448838016 2279903466880 4478352304896 cost_5961_1281_join0_20 cost_5961_1281_join0_22 rfl rfl rfl

private theorem cost_5961_1281_join1_12 : P1_7_1_3.blockEstimate 5961 1281 4353 512 = 4632103693056 :=
  @P1_7_1_3.block_append 5961 1281 4353 4609 256 256 512 2318341313920 2313762379136 4632103693056 cost_5961_1281_join0_24 cost_5961_1281_join0_26 rfl rfl rfl

private theorem cost_5961_1281_join1_14 : P1_7_1_3.blockEstimate 5961 1281 4865 512 = 4441720826624 :=
  @P1_7_1_3.block_append 5961 1281 4865 5121 256 256 512 2266166662528 2175554164096 4441720826624 cost_5961_1281_join0_28 cost_5961_1281_join0_30 rfl rfl rfl

private theorem cost_5961_1281_join1_16 : P1_7_1_3.blockEstimate 5961 1281 5377 512 = 3907203705600 :=
  @P1_7_1_3.block_append 5961 1281 5377 5633 256 256 512 2041924883840 1865278821760 3907203705600 cost_5961_1281_join0_32 cost_5961_1281_join0_34 rfl rfl rfl

private theorem cost_5961_1281_join1_18 : P1_7_1_3.blockEstimate 5961 1281 5889 512 = 3056208177474 :=
  @P1_7_1_3.block_append 5961 1281 5889 6145 256 256 512 1647502122198 1408706055276 3056208177474 cost_5961_1281_join0_36 cost_5961_1281_join0_38 rfl rfl rfl

private theorem cost_5961_1281_join1_20 : P1_7_1_3.blockEstimate 5961 1281 6401 512 = 2096192620984 :=
  @P1_7_1_3.block_append 5961 1281 6401 6657 256 256 512 1166537699101 929654921883 2096192620984 cost_5961_1281_join0_40 cost_5961_1281_join0_42 rfl rfl rfl

private theorem cost_5961_1281_join1_22 : P1_7_1_3.blockEstimate 5961 1281 6913 512 = 1208083713273 :=
  @P1_7_1_3.block_append 5961 1281 6913 7169 256 256 512 705971334552 502112378721 1208083713273 cost_5961_1281_join0_44 cost_5961_1281_join0_46 rfl rfl rfl

private theorem cost_5961_1281_join1_24 : P1_7_1_3.blockEstimate 5961 1281 7425 512 = 507237208896 :=
  @P1_7_1_3.block_append 5961 1281 7425 7681 256 256 512 324921762208 182315446688 507237208896 cost_5961_1281_join0_48 cost_5961_1281_join0_50 rfl rfl rfl

private theorem cost_5961_1281_join1_26 : P1_7_1_3.blockEstimate 5961 1281 7937 512 = 95887217472 :=
  @P1_7_1_3.block_append 5961 1281 7937 8193 256 256 512 78471315872 17415901600 95887217472 cost_5961_1281_join0_52 cost_5961_1281_join0_54 rfl rfl rfl

private theorem cost_5961_1281_join2_0 : P1_7_1_3.blockEstimate 5961 1281 1281 1024 = 932182560000 :=
  @P1_7_1_3.block_append 5961 1281 1281 1793 512 512 1024 125504194176 806678365824 932182560000 cost_5961_1281_join1_0 cost_5961_1281_join1_2 rfl rfl rfl

private theorem cost_5961_1281_join2_2 : P1_7_1_3.blockEstimate 5961 1281 2305 1024 = 5104526074816 :=
  @P1_7_1_3.block_append 5961 1281 2305 2817 512 512 1024 1966079310016 3138446764800 5104526074816 cost_5961_1281_join1_4 cost_5961_1281_join1_6 rfl rfl rfl

private theorem cost_5961_1281_join2_4 : P1_7_1_3.blockEstimate 5961 1281 3329 1024 = 8458818967040 :=
  @P1_7_1_3.block_append 5961 1281 3329 3841 512 512 1024 3980466662144 4478352304896 8458818967040 cost_5961_1281_join1_8 cost_5961_1281_join1_10 rfl rfl rfl

private theorem cost_5961_1281_join2_6 : P1_7_1_3.blockEstimate 5961 1281 4353 1024 = 9073824519680 :=
  @P1_7_1_3.block_append 5961 1281 4353 4865 512 512 1024 4632103693056 4441720826624 9073824519680 cost_5961_1281_join1_12 cost_5961_1281_join1_14 rfl rfl rfl

private theorem cost_5961_1281_join2_8 : P1_7_1_3.blockEstimate 5961 1281 5377 1024 = 6963411883074 :=
  @P1_7_1_3.block_append 5961 1281 5377 5889 512 512 1024 3907203705600 3056208177474 6963411883074 cost_5961_1281_join1_16 cost_5961_1281_join1_18 rfl rfl rfl

private theorem cost_5961_1281_join2_10 : P1_7_1_3.blockEstimate 5961 1281 6401 1024 = 3304276334257 :=
  @P1_7_1_3.block_append 5961 1281 6401 6913 512 512 1024 2096192620984 1208083713273 3304276334257 cost_5961_1281_join1_20 cost_5961_1281_join1_22 rfl rfl rfl

private theorem cost_5961_1281_join2_12 : P1_7_1_3.blockEstimate 5961 1281 7425 1024 = 603124426368 :=
  @P1_7_1_3.block_append 5961 1281 7425 7937 512 512 1024 507237208896 95887217472 603124426368 cost_5961_1281_join1_24 cost_5961_1281_join1_26 rfl rfl rfl

private theorem cost_5961_1281_join3_0 : P1_7_1_3.blockEstimate 5961 1281 1281 2048 = 6036708634816 :=
  @P1_7_1_3.block_append 5961 1281 1281 2305 1024 1024 2048 932182560000 5104526074816 6036708634816 cost_5961_1281_join2_0 cost_5961_1281_join2_2 rfl rfl rfl

private theorem cost_5961_1281_join3_2 : P1_7_1_3.blockEstimate 5961 1281 3329 2048 = 17532643486720 :=
  @P1_7_1_3.block_append 5961 1281 3329 4353 1024 1024 2048 8458818967040 9073824519680 17532643486720 cost_5961_1281_join2_4 cost_5961_1281_join2_6 rfl rfl rfl

private theorem cost_5961_1281_join3_4 : P1_7_1_3.blockEstimate 5961 1281 5377 2048 = 10267688217331 :=
  @P1_7_1_3.block_append 5961 1281 5377 6401 1024 1024 2048 6963411883074 3304276334257 10267688217331 cost_5961_1281_join2_8 cost_5961_1281_join2_10 rfl rfl rfl

private theorem cost_5961_1281_join3_6 : P1_7_1_3.blockEstimate 5961 1281 7425 1098 = 603336926225 :=
  @P1_7_1_3.block_append 5961 1281 7425 8449 1024 74 1098 603124426368 212499857 603336926225 cost_5961_1281_join2_12 cost_5961_1281_block56 rfl rfl rfl

private theorem cost_5961_1281_join4_0 : P1_7_1_3.blockEstimate 5961 1281 1281 4096 = 23569352121536 :=
  @P1_7_1_3.block_append 5961 1281 1281 3329 2048 2048 4096 6036708634816 17532643486720 23569352121536 cost_5961_1281_join3_0 cost_5961_1281_join3_2 rfl rfl rfl

private theorem cost_5961_1281_join4_2 : P1_7_1_3.blockEstimate 5961 1281 5377 3146 = 10871025143556 :=
  @P1_7_1_3.block_append 5961 1281 5377 7425 2048 1098 3146 10267688217331 603336926225 10871025143556 cost_5961_1281_join3_4 cost_5961_1281_join3_6 rfl rfl rfl

private theorem cost_5961_1281_join5_0 : P1_7_1_3.blockEstimate 5961 1281 1281 7242 = 34440377265092 :=
  @P1_7_1_3.block_append 5961 1281 1281 5377 4096 3146 7242 23569352121536 10871025143556 34440377265092 cost_5961_1281_join4_0 cost_5961_1281_join4_2 rfl rfl rfl

private theorem cost_5961_1281_total : P1_7_1_3.momentEstimate 5961 1281 = 34440377265092 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 5961 + 1281 = 7242 by decide]
  exact cost_5961_1281_join5_0

theorem moment5961_1281 : P1_7_1.groupedPoleMoment 5961 1281 ≤ 34440377265092 :=
  (P1_7_1_3.grouped_bound 5961 1281).trans_eq cost_5961_1281_total
private theorem cost_6277_1361_block0 : P1_7_1_3.blockEstimate 6277 1361 1361 128 = 2211582880 := by decide +kernel

private theorem cost_6277_1361_block1 : P1_7_1_3.blockEstimate 6277 1361 1489 128 = 15005344672 := by decide +kernel

private theorem cost_6277_1361_block2 : P1_7_1_3.blockEstimate 6277 1361 1617 128 = 39751824288 := by decide +kernel

private theorem cost_6277_1361_block3 : P1_7_1_3.blockEstimate 6277 1361 1745 128 = 75645715360 := by decide +kernel

private theorem cost_6277_1361_block4 : P1_7_1_3.blockEstimate 6277 1361 1873 128 = 121881711520 := by decide +kernel

private theorem cost_6277_1361_block5 : P1_7_1_3.blockEstimate 6277 1361 2001 128 = 177654506400 := by decide +kernel

private theorem cost_6277_1361_block6 : P1_7_1_3.blockEstimate 6277 1361 2129 128 = 242158793632 := by decide +kernel

private theorem cost_6277_1361_block7 : P1_7_1_3.blockEstimate 6277 1361 2257 128 = 314589266848 := by decide +kernel

private theorem cost_6277_1361_block8 : P1_7_1_3.blockEstimate 6277 1361 2385 128 = 394140619680 := by decide +kernel

private theorem cost_6277_1361_block9 : P1_7_1_3.blockEstimate 6277 1361 2513 128 = 480007545760 := by decide +kernel

private theorem cost_6277_1361_block10 : P1_7_1_3.blockEstimate 6277 1361 2641 128 = 571300312620 := by decide +kernel

private theorem cost_6277_1361_block11 : P1_7_1_3.blockEstimate 6277 1361 2769 128 = 663277132992 := by decide +kernel

private theorem cost_6277_1361_block12 : P1_7_1_3.blockEstimate 6277 1361 2897 128 = 749982096576 := by decide +kernel

private theorem cost_6277_1361_block13 : P1_7_1_3.blockEstimate 6277 1361 3025 128 = 830974418112 := by decide +kernel

private theorem cost_6277_1361_block14 : P1_7_1_3.blockEstimate 6277 1361 3153 128 = 906254097600 := by decide +kernel

private theorem cost_6277_1361_block15 : P1_7_1_3.blockEstimate 6277 1361 3281 128 = 975821135040 := by decide +kernel

private theorem cost_6277_1361_block16 : P1_7_1_3.blockEstimate 6277 1361 3409 128 = 1039675530432 := by decide +kernel

private theorem cost_6277_1361_block17 : P1_7_1_3.blockEstimate 6277 1361 3537 128 = 1097817283776 := by decide +kernel

private theorem cost_6277_1361_block18 : P1_7_1_3.blockEstimate 6277 1361 3665 128 = 1150246395072 := by decide +kernel

private theorem cost_6277_1361_block19 : P1_7_1_3.blockEstimate 6277 1361 3793 128 = 1196962864320 := by decide +kernel

private theorem cost_6277_1361_block20 : P1_7_1_3.blockEstimate 6277 1361 3921 128 = 1237966691520 := by decide +kernel

private theorem cost_6277_1361_block21 : P1_7_1_3.blockEstimate 6277 1361 4049 128 = 1273257876672 := by decide +kernel

private theorem cost_6277_1361_block22 : P1_7_1_3.blockEstimate 6277 1361 4177 128 = 1302836419776 := by decide +kernel

private theorem cost_6277_1361_block23 : P1_7_1_3.blockEstimate 6277 1361 4305 128 = 1326702320832 := by decide +kernel

private theorem cost_6277_1361_block24 : P1_7_1_3.blockEstimate 6277 1361 4433 128 = 1344855579840 := by decide +kernel

private theorem cost_6277_1361_block25 : P1_7_1_3.blockEstimate 6277 1361 4561 128 = 1357296196800 := by decide +kernel

private theorem cost_6277_1361_block26 : P1_7_1_3.blockEstimate 6277 1361 4689 128 = 1364024171712 := by decide +kernel

private theorem cost_6277_1361_block27 : P1_7_1_3.blockEstimate 6277 1361 4817 128 = 1365039504576 := by decide +kernel

private theorem cost_6277_1361_block28 : P1_7_1_3.blockEstimate 6277 1361 4945 128 = 1360342195392 := by decide +kernel

private theorem cost_6277_1361_block29 : P1_7_1_3.blockEstimate 6277 1361 5073 128 = 1349932244160 := by decide +kernel

private theorem cost_6277_1361_block30 : P1_7_1_3.blockEstimate 6277 1361 5201 128 = 1333809650880 := by decide +kernel

private theorem cost_6277_1361_block31 : P1_7_1_3.blockEstimate 6277 1361 5329 128 = 1311974415552 := by decide +kernel

private theorem cost_6277_1361_block32 : P1_7_1_3.blockEstimate 6277 1361 5457 128 = 1284426538176 := by decide +kernel

private theorem cost_6277_1361_block33 : P1_7_1_3.blockEstimate 6277 1361 5585 128 = 1251166018752 := by decide +kernel

private theorem cost_6277_1361_block34 : P1_7_1_3.blockEstimate 6277 1361 5713 128 = 1212192857280 := by decide +kernel

private theorem cost_6277_1361_block35 : P1_7_1_3.blockEstimate 6277 1361 5841 128 = 1167507053760 := by decide +kernel

private theorem cost_6277_1361_block36 : P1_7_1_3.blockEstimate 6277 1361 5969 128 = 1117108608192 := by decide +kernel

private theorem cost_6277_1361_block37 : P1_7_1_3.blockEstimate 6277 1361 6097 128 = 1060997520576 := by decide +kernel

private theorem cost_6277_1361_block38 : P1_7_1_3.blockEstimate 6277 1361 6225 128 = 999309554329 := by decide +kernel

private theorem cost_6277_1361_block39 : P1_7_1_3.blockEstimate 6277 1361 6353 128 = 934197088976 := by decide +kernel

private theorem cost_6277_1361_block40 : P1_7_1_3.blockEstimate 6277 1361 6481 128 = 867708580941 := by decide +kernel

private theorem cost_6277_1361_block41 : P1_7_1_3.blockEstimate 6277 1361 6609 128 = 800457543699 := by decide +kernel

private theorem cost_6277_1361_block42 : P1_7_1_3.blockEstimate 6277 1361 6737 128 = 732998809143 := by decide +kernel

private theorem cost_6277_1361_block43 : P1_7_1_3.blockEstimate 6277 1361 6865 128 = 665868286793 := by decide +kernel

private theorem cost_6277_1361_block44 : P1_7_1_3.blockEstimate 6277 1361 6993 128 = 599582966309 := by decide +kernel

private theorem cost_6277_1361_block45 : P1_7_1_3.blockEstimate 6277 1361 7121 128 = 534640917178 := by decide +kernel

private theorem cost_6277_1361_block46 : P1_7_1_3.blockEstimate 6277 1361 7249 128 = 471521286707 := by decide +kernel

private theorem cost_6277_1361_block47 : P1_7_1_3.blockEstimate 6277 1361 7377 128 = 410684303706 := by decide +kernel

private theorem cost_6277_1361_block48 : P1_7_1_3.blockEstimate 6277 1361 7505 128 = 352571275243 := by decide +kernel

private theorem cost_6277_1361_block49 : P1_7_1_3.blockEstimate 6277 1361 7633 128 = 297236212797 := by decide +kernel

private theorem cost_6277_1361_block50 : P1_7_1_3.blockEstimate 6277 1361 7761 128 = 245306496528 := by decide +kernel

private theorem cost_6277_1361_block51 : P1_7_1_3.blockEstimate 6277 1361 7889 128 = 197648421392 := by decide +kernel

private theorem cost_6277_1361_block52 : P1_7_1_3.blockEstimate 6277 1361 8017 128 = 154514230800 := by decide +kernel

private theorem cost_6277_1361_block53 : P1_7_1_3.blockEstimate 6277 1361 8145 128 = 116155582992 := by decide +kernel

private theorem cost_6277_1361_block54 : P1_7_1_3.blockEstimate 6277 1361 8273 128 = 82824136208 := by decide +kernel

private theorem cost_6277_1361_block55 : P1_7_1_3.blockEstimate 6277 1361 8401 128 = 54771548688 := by decide +kernel

private theorem cost_6277_1361_block56 : P1_7_1_3.blockEstimate 6277 1361 8529 128 = 32249478672 := by decide +kernel

private theorem cost_6277_1361_block57 : P1_7_1_3.blockEstimate 6277 1361 8657 128 = 15509584400 := by decide +kernel

private theorem cost_6277_1361_block58 : P1_7_1_3.blockEstimate 6277 1361 8785 128 = 4803524112 := by decide +kernel

private theorem cost_6277_1361_block59 : P1_7_1_3.blockEstimate 6277 1361 8913 86 = 348131553 := by decide +kernel

private theorem cost_6277_1361_join0_0 : P1_7_1_3.blockEstimate 6277 1361 1361 256 = 17216927552 :=
  @P1_7_1_3.block_append 6277 1361 1361 1489 128 128 256 2211582880 15005344672 17216927552 cost_6277_1361_block0 cost_6277_1361_block1 rfl rfl rfl

private theorem cost_6277_1361_join0_2 : P1_7_1_3.blockEstimate 6277 1361 1617 256 = 115397539648 :=
  @P1_7_1_3.block_append 6277 1361 1617 1745 128 128 256 39751824288 75645715360 115397539648 cost_6277_1361_block2 cost_6277_1361_block3 rfl rfl rfl

private theorem cost_6277_1361_join0_4 : P1_7_1_3.blockEstimate 6277 1361 1873 256 = 299536217920 :=
  @P1_7_1_3.block_append 6277 1361 1873 2001 128 128 256 121881711520 177654506400 299536217920 cost_6277_1361_block4 cost_6277_1361_block5 rfl rfl rfl

private theorem cost_6277_1361_join0_6 : P1_7_1_3.blockEstimate 6277 1361 2129 256 = 556748060480 :=
  @P1_7_1_3.block_append 6277 1361 2129 2257 128 128 256 242158793632 314589266848 556748060480 cost_6277_1361_block6 cost_6277_1361_block7 rfl rfl rfl

private theorem cost_6277_1361_join0_8 : P1_7_1_3.blockEstimate 6277 1361 2385 256 = 874148165440 :=
  @P1_7_1_3.block_append 6277 1361 2385 2513 128 128 256 394140619680 480007545760 874148165440 cost_6277_1361_block8 cost_6277_1361_block9 rfl rfl rfl

private theorem cost_6277_1361_join0_10 : P1_7_1_3.blockEstimate 6277 1361 2641 256 = 1234577445612 :=
  @P1_7_1_3.block_append 6277 1361 2641 2769 128 128 256 571300312620 663277132992 1234577445612 cost_6277_1361_block10 cost_6277_1361_block11 rfl rfl rfl

private theorem cost_6277_1361_join0_12 : P1_7_1_3.blockEstimate 6277 1361 2897 256 = 1580956514688 :=
  @P1_7_1_3.block_append 6277 1361 2897 3025 128 128 256 749982096576 830974418112 1580956514688 cost_6277_1361_block12 cost_6277_1361_block13 rfl rfl rfl

private theorem cost_6277_1361_join0_14 : P1_7_1_3.blockEstimate 6277 1361 3153 256 = 1882075232640 :=
  @P1_7_1_3.block_append 6277 1361 3153 3281 128 128 256 906254097600 975821135040 1882075232640 cost_6277_1361_block14 cost_6277_1361_block15 rfl rfl rfl

private theorem cost_6277_1361_join0_16 : P1_7_1_3.blockEstimate 6277 1361 3409 256 = 2137492814208 :=
  @P1_7_1_3.block_append 6277 1361 3409 3537 128 128 256 1039675530432 1097817283776 2137492814208 cost_6277_1361_block16 cost_6277_1361_block17 rfl rfl rfl

private theorem cost_6277_1361_join0_18 : P1_7_1_3.blockEstimate 6277 1361 3665 256 = 2347209259392 :=
  @P1_7_1_3.block_append 6277 1361 3665 3793 128 128 256 1150246395072 1196962864320 2347209259392 cost_6277_1361_block18 cost_6277_1361_block19 rfl rfl rfl

private theorem cost_6277_1361_join0_20 : P1_7_1_3.blockEstimate 6277 1361 3921 256 = 2511224568192 :=
  @P1_7_1_3.block_append 6277 1361 3921 4049 128 128 256 1237966691520 1273257876672 2511224568192 cost_6277_1361_block20 cost_6277_1361_block21 rfl rfl rfl

private theorem cost_6277_1361_join0_22 : P1_7_1_3.blockEstimate 6277 1361 4177 256 = 2629538740608 :=
  @P1_7_1_3.block_append 6277 1361 4177 4305 128 128 256 1302836419776 1326702320832 2629538740608 cost_6277_1361_block22 cost_6277_1361_block23 rfl rfl rfl

private theorem cost_6277_1361_join0_24 : P1_7_1_3.blockEstimate 6277 1361 4433 256 = 2702151776640 :=
  @P1_7_1_3.block_append 6277 1361 4433 4561 128 128 256 1344855579840 1357296196800 2702151776640 cost_6277_1361_block24 cost_6277_1361_block25 rfl rfl rfl

private theorem cost_6277_1361_join0_26 : P1_7_1_3.blockEstimate 6277 1361 4689 256 = 2729063676288 :=
  @P1_7_1_3.block_append 6277 1361 4689 4817 128 128 256 1364024171712 1365039504576 2729063676288 cost_6277_1361_block26 cost_6277_1361_block27 rfl rfl rfl

private theorem cost_6277_1361_join0_28 : P1_7_1_3.blockEstimate 6277 1361 4945 256 = 2710274439552 :=
  @P1_7_1_3.block_append 6277 1361 4945 5073 128 128 256 1360342195392 1349932244160 2710274439552 cost_6277_1361_block28 cost_6277_1361_block29 rfl rfl rfl

private theorem cost_6277_1361_join0_30 : P1_7_1_3.blockEstimate 6277 1361 5201 256 = 2645784066432 :=
  @P1_7_1_3.block_append 6277 1361 5201 5329 128 128 256 1333809650880 1311974415552 2645784066432 cost_6277_1361_block30 cost_6277_1361_block31 rfl rfl rfl

private theorem cost_6277_1361_join0_32 : P1_7_1_3.blockEstimate 6277 1361 5457 256 = 2535592556928 :=
  @P1_7_1_3.block_append 6277 1361 5457 5585 128 128 256 1284426538176 1251166018752 2535592556928 cost_6277_1361_block32 cost_6277_1361_block33 rfl rfl rfl

private theorem cost_6277_1361_join0_34 : P1_7_1_3.blockEstimate 6277 1361 5713 256 = 2379699911040 :=
  @P1_7_1_3.block_append 6277 1361 5713 5841 128 128 256 1212192857280 1167507053760 2379699911040 cost_6277_1361_block34 cost_6277_1361_block35 rfl rfl rfl

private theorem cost_6277_1361_join0_36 : P1_7_1_3.blockEstimate 6277 1361 5969 256 = 2178106128768 :=
  @P1_7_1_3.block_append 6277 1361 5969 6097 128 128 256 1117108608192 1060997520576 2178106128768 cost_6277_1361_block36 cost_6277_1361_block37 rfl rfl rfl

private theorem cost_6277_1361_join0_38 : P1_7_1_3.blockEstimate 6277 1361 6225 256 = 1933506643305 :=
  @P1_7_1_3.block_append 6277 1361 6225 6353 128 128 256 999309554329 934197088976 1933506643305 cost_6277_1361_block38 cost_6277_1361_block39 rfl rfl rfl

private theorem cost_6277_1361_join0_40 : P1_7_1_3.blockEstimate 6277 1361 6481 256 = 1668166124640 :=
  @P1_7_1_3.block_append 6277 1361 6481 6609 128 128 256 867708580941 800457543699 1668166124640 cost_6277_1361_block40 cost_6277_1361_block41 rfl rfl rfl

private theorem cost_6277_1361_join0_42 : P1_7_1_3.blockEstimate 6277 1361 6737 256 = 1398867095936 :=
  @P1_7_1_3.block_append 6277 1361 6737 6865 128 128 256 732998809143 665868286793 1398867095936 cost_6277_1361_block42 cost_6277_1361_block43 rfl rfl rfl

private theorem cost_6277_1361_join0_44 : P1_7_1_3.blockEstimate 6277 1361 6993 256 = 1134223883487 :=
  @P1_7_1_3.block_append 6277 1361 6993 7121 128 128 256 599582966309 534640917178 1134223883487 cost_6277_1361_block44 cost_6277_1361_block45 rfl rfl rfl

private theorem cost_6277_1361_join0_46 : P1_7_1_3.blockEstimate 6277 1361 7249 256 = 882205590413 :=
  @P1_7_1_3.block_append 6277 1361 7249 7377 128 128 256 471521286707 410684303706 882205590413 cost_6277_1361_block46 cost_6277_1361_block47 rfl rfl rfl

private theorem cost_6277_1361_join0_48 : P1_7_1_3.blockEstimate 6277 1361 7505 256 = 649807488040 :=
  @P1_7_1_3.block_append 6277 1361 7505 7633 128 128 256 352571275243 297236212797 649807488040 cost_6277_1361_block48 cost_6277_1361_block49 rfl rfl rfl

private theorem cost_6277_1361_join0_50 : P1_7_1_3.blockEstimate 6277 1361 7761 256 = 442954917920 :=
  @P1_7_1_3.block_append 6277 1361 7761 7889 128 128 256 245306496528 197648421392 442954917920 cost_6277_1361_block50 cost_6277_1361_block51 rfl rfl rfl

private theorem cost_6277_1361_join0_52 : P1_7_1_3.blockEstimate 6277 1361 8017 256 = 270669813792 :=
  @P1_7_1_3.block_append 6277 1361 8017 8145 128 128 256 154514230800 116155582992 270669813792 cost_6277_1361_block52 cost_6277_1361_block53 rfl rfl rfl

private theorem cost_6277_1361_join0_54 : P1_7_1_3.blockEstimate 6277 1361 8273 256 = 137595684896 :=
  @P1_7_1_3.block_append 6277 1361 8273 8401 128 128 256 82824136208 54771548688 137595684896 cost_6277_1361_block54 cost_6277_1361_block55 rfl rfl rfl

private theorem cost_6277_1361_join0_56 : P1_7_1_3.blockEstimate 6277 1361 8529 256 = 47759063072 :=
  @P1_7_1_3.block_append 6277 1361 8529 8657 128 128 256 32249478672 15509584400 47759063072 cost_6277_1361_block56 cost_6277_1361_block57 rfl rfl rfl

private theorem cost_6277_1361_join0_58 : P1_7_1_3.blockEstimate 6277 1361 8785 214 = 5151655665 :=
  @P1_7_1_3.block_append 6277 1361 8785 8913 128 86 214 4803524112 348131553 5151655665 cost_6277_1361_block58 cost_6277_1361_block59 rfl rfl rfl

private theorem cost_6277_1361_join1_0 : P1_7_1_3.blockEstimate 6277 1361 1361 512 = 132614467200 :=
  @P1_7_1_3.block_append 6277 1361 1361 1617 256 256 512 17216927552 115397539648 132614467200 cost_6277_1361_join0_0 cost_6277_1361_join0_2 rfl rfl rfl

private theorem cost_6277_1361_join1_2 : P1_7_1_3.blockEstimate 6277 1361 1873 512 = 856284278400 :=
  @P1_7_1_3.block_append 6277 1361 1873 2129 256 256 512 299536217920 556748060480 856284278400 cost_6277_1361_join0_4 cost_6277_1361_join0_6 rfl rfl rfl

private theorem cost_6277_1361_join1_4 : P1_7_1_3.blockEstimate 6277 1361 2385 512 = 2108725611052 :=
  @P1_7_1_3.block_append 6277 1361 2385 2641 256 256 512 874148165440 1234577445612 2108725611052 cost_6277_1361_join0_8 cost_6277_1361_join0_10 rfl rfl rfl

private theorem cost_6277_1361_join1_6 : P1_7_1_3.blockEstimate 6277 1361 2897 512 = 3463031747328 :=
  @P1_7_1_3.block_append 6277 1361 2897 3153 256 256 512 1580956514688 1882075232640 3463031747328 cost_6277_1361_join0_12 cost_6277_1361_join0_14 rfl rfl rfl

private theorem cost_6277_1361_join1_8 : P1_7_1_3.blockEstimate 6277 1361 3409 512 = 4484702073600 :=
  @P1_7_1_3.block_append 6277 1361 3409 3665 256 256 512 2137492814208 2347209259392 4484702073600 cost_6277_1361_join0_16 cost_6277_1361_join0_18 rfl rfl rfl

private theorem cost_6277_1361_join1_10 : P1_7_1_3.blockEstimate 6277 1361 3921 512 = 5140763308800 :=
  @P1_7_1_3.block_append 6277 1361 3921 4177 256 256 512 2511224568192 2629538740608 5140763308800 cost_6277_1361_join0_20 cost_6277_1361_join0_22 rfl rfl rfl

private theorem cost_6277_1361_join1_12 : P1_7_1_3.blockEstimate 6277 1361 4433 512 = 5431215452928 :=
  @P1_7_1_3.block_append 6277 1361 4433 4689 256 256 512 2702151776640 2729063676288 5431215452928 cost_6277_1361_join0_24 cost_6277_1361_join0_26 rfl rfl rfl

private theorem cost_6277_1361_join1_14 : P1_7_1_3.blockEstimate 6277 1361 4945 512 = 5356058505984 :=
  @P1_7_1_3.block_append 6277 1361 4945 5201 256 256 512 2710274439552 2645784066432 5356058505984 cost_6277_1361_join0_28 cost_6277_1361_join0_30 rfl rfl rfl

private theorem cost_6277_1361_join1_16 : P1_7_1_3.blockEstimate 6277 1361 5457 512 = 4915292467968 :=
  @P1_7_1_3.block_append 6277 1361 5457 5713 256 256 512 2535592556928 2379699911040 4915292467968 cost_6277_1361_join0_32 cost_6277_1361_join0_34 rfl rfl rfl

private theorem cost_6277_1361_join1_18 : P1_7_1_3.blockEstimate 6277 1361 5969 512 = 4111612772073 :=
  @P1_7_1_3.block_append 6277 1361 5969 6225 256 256 512 2178106128768 1933506643305 4111612772073 cost_6277_1361_join0_36 cost_6277_1361_join0_38 rfl rfl rfl

private theorem cost_6277_1361_join1_20 : P1_7_1_3.blockEstimate 6277 1361 6481 512 = 3067033220576 :=
  @P1_7_1_3.block_append 6277 1361 6481 6737 256 256 512 1668166124640 1398867095936 3067033220576 cost_6277_1361_join0_40 cost_6277_1361_join0_42 rfl rfl rfl

private theorem cost_6277_1361_join1_22 : P1_7_1_3.blockEstimate 6277 1361 6993 512 = 2016429473900 :=
  @P1_7_1_3.block_append 6277 1361 6993 7249 256 256 512 1134223883487 882205590413 2016429473900 cost_6277_1361_join0_44 cost_6277_1361_join0_46 rfl rfl rfl

private theorem cost_6277_1361_join1_24 : P1_7_1_3.blockEstimate 6277 1361 7505 512 = 1092762405960 :=
  @P1_7_1_3.block_append 6277 1361 7505 7761 256 256 512 649807488040 442954917920 1092762405960 cost_6277_1361_join0_48 cost_6277_1361_join0_50 rfl rfl rfl

private theorem cost_6277_1361_join1_26 : P1_7_1_3.blockEstimate 6277 1361 8017 512 = 408265498688 :=
  @P1_7_1_3.block_append 6277 1361 8017 8273 256 256 512 270669813792 137595684896 408265498688 cost_6277_1361_join0_52 cost_6277_1361_join0_54 rfl rfl rfl

private theorem cost_6277_1361_join1_28 : P1_7_1_3.blockEstimate 6277 1361 8529 470 = 52910718737 :=
  @P1_7_1_3.block_append 6277 1361 8529 8785 256 214 470 47759063072 5151655665 52910718737 cost_6277_1361_join0_56 cost_6277_1361_join0_58 rfl rfl rfl

private theorem cost_6277_1361_join2_0 : P1_7_1_3.blockEstimate 6277 1361 1361 1024 = 988898745600 :=
  @P1_7_1_3.block_append 6277 1361 1361 1873 512 512 1024 132614467200 856284278400 988898745600 cost_6277_1361_join1_0 cost_6277_1361_join1_2 rfl rfl rfl

private theorem cost_6277_1361_join2_2 : P1_7_1_3.blockEstimate 6277 1361 2385 1024 = 5571757358380 :=
  @P1_7_1_3.block_append 6277 1361 2385 2897 512 512 1024 2108725611052 3463031747328 5571757358380 cost_6277_1361_join1_4 cost_6277_1361_join1_6 rfl rfl rfl

private theorem cost_6277_1361_join2_4 : P1_7_1_3.blockEstimate 6277 1361 3409 1024 = 9625465382400 :=
  @P1_7_1_3.block_append 6277 1361 3409 3921 512 512 1024 4484702073600 5140763308800 9625465382400 cost_6277_1361_join1_8 cost_6277_1361_join1_10 rfl rfl rfl

private theorem cost_6277_1361_join2_6 : P1_7_1_3.blockEstimate 6277 1361 4433 1024 = 10787273958912 :=
  @P1_7_1_3.block_append 6277 1361 4433 4945 512 512 1024 5431215452928 5356058505984 10787273958912 cost_6277_1361_join1_12 cost_6277_1361_join1_14 rfl rfl rfl

private theorem cost_6277_1361_join2_8 : P1_7_1_3.blockEstimate 6277 1361 5457 1024 = 9026905240041 :=
  @P1_7_1_3.block_append 6277 1361 5457 5969 512 512 1024 4915292467968 4111612772073 9026905240041 cost_6277_1361_join1_16 cost_6277_1361_join1_18 rfl rfl rfl

private theorem cost_6277_1361_join2_10 : P1_7_1_3.blockEstimate 6277 1361 6481 1024 = 5083462694476 :=
  @P1_7_1_3.block_append 6277 1361 6481 6993 512 512 1024 3067033220576 2016429473900 5083462694476 cost_6277_1361_join1_20 cost_6277_1361_join1_22 rfl rfl rfl

private theorem cost_6277_1361_join2_12 : P1_7_1_3.blockEstimate 6277 1361 7505 1024 = 1501027904648 :=
  @P1_7_1_3.block_append 6277 1361 7505 8017 512 512 1024 1092762405960 408265498688 1501027904648 cost_6277_1361_join1_24 cost_6277_1361_join1_26 rfl rfl rfl

private theorem cost_6277_1361_join3_0 : P1_7_1_3.blockEstimate 6277 1361 1361 2048 = 6560656103980 :=
  @P1_7_1_3.block_append 6277 1361 1361 2385 1024 1024 2048 988898745600 5571757358380 6560656103980 cost_6277_1361_join2_0 cost_6277_1361_join2_2 rfl rfl rfl

private theorem cost_6277_1361_join3_2 : P1_7_1_3.blockEstimate 6277 1361 3409 2048 = 20412739341312 :=
  @P1_7_1_3.block_append 6277 1361 3409 4433 1024 1024 2048 9625465382400 10787273958912 20412739341312 cost_6277_1361_join2_4 cost_6277_1361_join2_6 rfl rfl rfl

private theorem cost_6277_1361_join3_4 : P1_7_1_3.blockEstimate 6277 1361 5457 2048 = 14110367934517 :=
  @P1_7_1_3.block_append 6277 1361 5457 6481 1024 1024 2048 9026905240041 5083462694476 14110367934517 cost_6277_1361_join2_8 cost_6277_1361_join2_10 rfl rfl rfl

private theorem cost_6277_1361_join3_6 : P1_7_1_3.blockEstimate 6277 1361 7505 1494 = 1553938623385 :=
  @P1_7_1_3.block_append 6277 1361 7505 8529 1024 470 1494 1501027904648 52910718737 1553938623385 cost_6277_1361_join2_12 cost_6277_1361_join1_28 rfl rfl rfl

private theorem cost_6277_1361_join4_0 : P1_7_1_3.blockEstimate 6277 1361 1361 4096 = 26973395445292 :=
  @P1_7_1_3.block_append 6277 1361 1361 3409 2048 2048 4096 6560656103980 20412739341312 26973395445292 cost_6277_1361_join3_0 cost_6277_1361_join3_2 rfl rfl rfl

private theorem cost_6277_1361_join4_2 : P1_7_1_3.blockEstimate 6277 1361 5457 3542 = 15664306557902 :=
  @P1_7_1_3.block_append 6277 1361 5457 7505 2048 1494 3542 14110367934517 1553938623385 15664306557902 cost_6277_1361_join3_4 cost_6277_1361_join3_6 rfl rfl rfl

private theorem cost_6277_1361_join5_0 : P1_7_1_3.blockEstimate 6277 1361 1361 7638 = 42637702003194 :=
  @P1_7_1_3.block_append 6277 1361 1361 5457 4096 3542 7638 26973395445292 15664306557902 42637702003194 cost_6277_1361_join4_0 cost_6277_1361_join4_2 rfl rfl rfl

private theorem cost_6277_1361_total : P1_7_1_3.momentEstimate 6277 1361 = 42637702003194 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 6277 + 1361 = 7638 by decide]
  exact cost_6277_1361_join5_0

theorem moment6277_1361 : P1_7_1.groupedPoleMoment 6277 1361 ≤ 42637702003194 :=
  (P1_7_1_3.grouped_bound 6277 1361).trans_eq cost_6277_1361_total
private theorem cost_6365_1386_block0 : P1_7_1_3.blockEstimate 6365 1386 1386 128 = 2243065760 := by decide +kernel

private theorem cost_6365_1386_block1 : P1_7_1_3.blockEstimate 6365 1386 1514 128 = 15222818720 := by decide +kernel

private theorem cost_6365_1386_block2 : P1_7_1_3.blockEstimate 6365 1386 1642 128 = 40339838880 := by decide +kernel

private theorem cost_6365_1386_block3 : P1_7_1_3.blockEstimate 6365 1386 1770 128 = 76788819872 := by decide +kernel

private theorem cost_6365_1386_block4 : P1_7_1_3.blockEstimate 6365 1386 1898 128 = 123764455328 := by decide +kernel

private theorem cost_6365_1386_block5 : P1_7_1_3.blockEstimate 6365 1386 2026 128 = 180461438880 := by decide +kernel

private theorem cost_6365_1386_block6 : P1_7_1_3.blockEstimate 6365 1386 2154 128 = 246074464160 := by decide +kernel

private theorem cost_6365_1386_block7 : P1_7_1_3.blockEstimate 6365 1386 2282 128 = 319798224800 := by decide +kernel

private theorem cost_6365_1386_block8 : P1_7_1_3.blockEstimate 6365 1386 2410 128 = 400827414432 := by decide +kernel

private theorem cost_6365_1386_block9 : P1_7_1_3.blockEstimate 6365 1386 2538 128 = 488356726688 := by decide +kernel

private theorem cost_6365_1386_block10 : P1_7_1_3.blockEstimate 6365 1386 2666 128 = 581572065727 := by decide +kernel

private theorem cost_6365_1386_block11 : P1_7_1_3.blockEstimate 6365 1386 2794 128 = 676965717248 := by decide +kernel

private theorem cost_6365_1386_block12 : P1_7_1_3.blockEstimate 6365 1386 2922 128 = 767546004736 := by decide +kernel

private theorem cost_6365_1386_block13 : P1_7_1_3.blockEstimate 6365 1386 3050 128 = 852308792576 := by decide +kernel

private theorem cost_6365_1386_block14 : P1_7_1_3.blockEstimate 6365 1386 3178 128 = 931254080768 := by decide +kernel

private theorem cost_6365_1386_block15 : P1_7_1_3.blockEstimate 6365 1386 3306 128 = 1004381869312 := by decide +kernel

private theorem cost_6365_1386_block16 : P1_7_1_3.blockEstimate 6365 1386 3434 128 = 1071692158208 := by decide +kernel

private theorem cost_6365_1386_block17 : P1_7_1_3.blockEstimate 6365 1386 3562 128 = 1133184947456 := by decide +kernel

private theorem cost_6365_1386_block18 : P1_7_1_3.blockEstimate 6365 1386 3690 128 = 1188860237056 := by decide +kernel

private theorem cost_6365_1386_block19 : P1_7_1_3.blockEstimate 6365 1386 3818 128 = 1238718027008 := by decide +kernel

private theorem cost_6365_1386_block20 : P1_7_1_3.blockEstimate 6365 1386 3946 128 = 1282758317312 := by decide +kernel

private theorem cost_6365_1386_block21 : P1_7_1_3.blockEstimate 6365 1386 4074 128 = 1320981107968 := by decide +kernel

private theorem cost_6365_1386_block22 : P1_7_1_3.blockEstimate 6365 1386 4202 128 = 1353386398976 := by decide +kernel

private theorem cost_6365_1386_block23 : P1_7_1_3.blockEstimate 6365 1386 4330 128 = 1379974190336 := by decide +kernel

private theorem cost_6365_1386_block24 : P1_7_1_3.blockEstimate 6365 1386 4458 128 = 1400744482048 := by decide +kernel

private theorem cost_6365_1386_block25 : P1_7_1_3.blockEstimate 6365 1386 4586 128 = 1415697274112 := by decide +kernel

private theorem cost_6365_1386_block26 : P1_7_1_3.blockEstimate 6365 1386 4714 128 = 1424832566528 := by decide +kernel

private theorem cost_6365_1386_block27 : P1_7_1_3.blockEstimate 6365 1386 4842 128 = 1428150359296 := by decide +kernel

private theorem cost_6365_1386_block28 : P1_7_1_3.blockEstimate 6365 1386 4970 128 = 1425650652416 := by decide +kernel

private theorem cost_6365_1386_block29 : P1_7_1_3.blockEstimate 6365 1386 5098 128 = 1417333445888 := by decide +kernel

private theorem cost_6365_1386_block30 : P1_7_1_3.blockEstimate 6365 1386 5226 128 = 1403198739712 := by decide +kernel

private theorem cost_6365_1386_block31 : P1_7_1_3.blockEstimate 6365 1386 5354 128 = 1383246533888 := by decide +kernel

private theorem cost_6365_1386_block32 : P1_7_1_3.blockEstimate 6365 1386 5482 128 = 1357476828416 := by decide +kernel

private theorem cost_6365_1386_block33 : P1_7_1_3.blockEstimate 6365 1386 5610 128 = 1325889623296 := by decide +kernel

private theorem cost_6365_1386_block34 : P1_7_1_3.blockEstimate 6365 1386 5738 128 = 1288484918528 := by decide +kernel

private theorem cost_6365_1386_block35 : P1_7_1_3.blockEstimate 6365 1386 5866 128 = 1245262714112 := by decide +kernel

private theorem cost_6365_1386_block36 : P1_7_1_3.blockEstimate 6365 1386 5994 128 = 1196223010048 := by decide +kernel

private theorem cost_6365_1386_block37 : P1_7_1_3.blockEstimate 6365 1386 6122 128 = 1141365806336 := by decide +kernel

private theorem cost_6365_1386_block38 : P1_7_1_3.blockEstimate 6365 1386 6250 128 = 1080691835239 := by decide +kernel

private theorem cost_6365_1386_block39 : P1_7_1_3.blockEstimate 6365 1386 6378 128 = 1015083577505 := by decide +kernel

private theorem cost_6365_1386_block40 : P1_7_1_3.blockEstimate 6365 1386 6506 128 = 947351668286 := by decide +kernel

private theorem cost_6365_1386_block41 : P1_7_1_3.blockEstimate 6365 1386 6634 128 = 878512672150 := by decide +kernel

private theorem cost_6365_1386_block42 : P1_7_1_3.blockEstimate 6365 1386 6762 128 = 809131450797 := by decide +kernel

private theorem cost_6365_1386_block43 : P1_7_1_3.blockEstimate 6365 1386 6890 128 = 739754285609 := by decide +kernel

private theorem cost_6365_1386_block44 : P1_7_1_3.blockEstimate 6365 1386 7018 128 = 670908878559 := by decide +kernel

private theorem cost_6365_1386_block45 : P1_7_1_3.blockEstimate 6365 1386 7146 128 = 603104352510 := by decide +kernel

private theorem cost_6365_1386_block46 : P1_7_1_3.blockEstimate 6365 1386 7274 128 = 536831250144 := by decide +kernel

private theorem cost_6365_1386_block47 : P1_7_1_3.blockEstimate 6365 1386 7402 128 = 472561535251 := by decide +kernel

private theorem cost_6365_1386_block48 : P1_7_1_3.blockEstimate 6365 1386 7530 128 = 410748592012 := by decide +kernel

private theorem cost_6365_1386_block49 : P1_7_1_3.blockEstimate 6365 1386 7658 128 = 351791146518 := by decide +kernel

private theorem cost_6365_1386_block50 : P1_7_1_3.blockEstimate 6365 1386 7786 128 = 295617452096 := by decide +kernel

private theorem cost_6365_1386_block51 : P1_7_1_3.blockEstimate 6365 1386 7914 128 = 243292047424 := by decide +kernel

private theorem cost_6365_1386_block52 : P1_7_1_3.blockEstimate 6365 1386 8042 128 = 195360634944 := by decide +kernel

private theorem cost_6365_1386_block53 : P1_7_1_3.blockEstimate 6365 1386 8170 128 = 152074872896 := by decide +kernel

private theorem cost_6365_1386_block54 : P1_7_1_3.blockEstimate 6365 1386 8298 128 = 113686419520 := by decide +kernel

private theorem cost_6365_1386_block55 : P1_7_1_3.blockEstimate 6365 1386 8426 128 = 80446933056 := by decide +kernel

private theorem cost_6365_1386_block56 : P1_7_1_3.blockEstimate 6365 1386 8554 128 = 52608071744 := by decide +kernel

private theorem cost_6365_1386_block57 : P1_7_1_3.blockEstimate 6365 1386 8682 128 = 30421493824 := by decide +kernel

private theorem cost_6365_1386_block58 : P1_7_1_3.blockEstimate 6365 1386 8810 128 = 14138857536 := by decide +kernel

private theorem cost_6365_1386_block59 : P1_7_1_3.blockEstimate 6365 1386 8938 128 = 4011821120 := by decide +kernel

private theorem cost_6365_1386_block60 : P1_7_1_3.blockEstimate 6365 1386 9066 71 = 201027780 := by decide +kernel

private theorem cost_6365_1386_join0_0 : P1_7_1_3.blockEstimate 6365 1386 1386 256 = 17465884480 :=
  @P1_7_1_3.block_append 6365 1386 1386 1514 128 128 256 2243065760 15222818720 17465884480 cost_6365_1386_block0 cost_6365_1386_block1 rfl rfl rfl

private theorem cost_6365_1386_join0_2 : P1_7_1_3.blockEstimate 6365 1386 1642 256 = 117128658752 :=
  @P1_7_1_3.block_append 6365 1386 1642 1770 128 128 256 40339838880 76788819872 117128658752 cost_6365_1386_block2 cost_6365_1386_block3 rfl rfl rfl

private theorem cost_6365_1386_join0_4 : P1_7_1_3.blockEstimate 6365 1386 1898 256 = 304225894208 :=
  @P1_7_1_3.block_append 6365 1386 1898 2026 128 128 256 123764455328 180461438880 304225894208 cost_6365_1386_block4 cost_6365_1386_block5 rfl rfl rfl

private theorem cost_6365_1386_join0_6 : P1_7_1_3.blockEstimate 6365 1386 2154 256 = 565872688960 :=
  @P1_7_1_3.block_append 6365 1386 2154 2282 128 128 256 246074464160 319798224800 565872688960 cost_6365_1386_block6 cost_6365_1386_block7 rfl rfl rfl

private theorem cost_6365_1386_join0_8 : P1_7_1_3.blockEstimate 6365 1386 2410 256 = 889184141120 :=
  @P1_7_1_3.block_append 6365 1386 2410 2538 128 128 256 400827414432 488356726688 889184141120 cost_6365_1386_block8 cost_6365_1386_block9 rfl rfl rfl

private theorem cost_6365_1386_join0_10 : P1_7_1_3.blockEstimate 6365 1386 2666 256 = 1258537782975 :=
  @P1_7_1_3.block_append 6365 1386 2666 2794 128 128 256 581572065727 676965717248 1258537782975 cost_6365_1386_block10 cost_6365_1386_block11 rfl rfl rfl

private theorem cost_6365_1386_join0_12 : P1_7_1_3.blockEstimate 6365 1386 2922 256 = 1619854797312 :=
  @P1_7_1_3.block_append 6365 1386 2922 3050 128 128 256 767546004736 852308792576 1619854797312 cost_6365_1386_block12 cost_6365_1386_block13 rfl rfl rfl

private theorem cost_6365_1386_join0_14 : P1_7_1_3.blockEstimate 6365 1386 3178 256 = 1935635950080 :=
  @P1_7_1_3.block_append 6365 1386 3178 3306 128 128 256 931254080768 1004381869312 1935635950080 cost_6365_1386_block14 cost_6365_1386_block15 rfl rfl rfl

private theorem cost_6365_1386_join0_16 : P1_7_1_3.blockEstimate 6365 1386 3434 256 = 2204877105664 :=
  @P1_7_1_3.block_append 6365 1386 3434 3562 128 128 256 1071692158208 1133184947456 2204877105664 cost_6365_1386_block16 cost_6365_1386_block17 rfl rfl rfl

private theorem cost_6365_1386_join0_18 : P1_7_1_3.blockEstimate 6365 1386 3690 256 = 2427578264064 :=
  @P1_7_1_3.block_append 6365 1386 3690 3818 128 128 256 1188860237056 1238718027008 2427578264064 cost_6365_1386_block18 cost_6365_1386_block19 rfl rfl rfl

private theorem cost_6365_1386_join0_20 : P1_7_1_3.blockEstimate 6365 1386 3946 256 = 2603739425280 :=
  @P1_7_1_3.block_append 6365 1386 3946 4074 128 128 256 1282758317312 1320981107968 2603739425280 cost_6365_1386_block20 cost_6365_1386_block21 rfl rfl rfl

private theorem cost_6365_1386_join0_22 : P1_7_1_3.blockEstimate 6365 1386 4202 256 = 2733360589312 :=
  @P1_7_1_3.block_append 6365 1386 4202 4330 128 128 256 1353386398976 1379974190336 2733360589312 cost_6365_1386_block22 cost_6365_1386_block23 rfl rfl rfl

private theorem cost_6365_1386_join0_24 : P1_7_1_3.blockEstimate 6365 1386 4458 256 = 2816441756160 :=
  @P1_7_1_3.block_append 6365 1386 4458 4586 128 128 256 1400744482048 1415697274112 2816441756160 cost_6365_1386_block24 cost_6365_1386_block25 rfl rfl rfl

private theorem cost_6365_1386_join0_26 : P1_7_1_3.blockEstimate 6365 1386 4714 256 = 2852982925824 :=
  @P1_7_1_3.block_append 6365 1386 4714 4842 128 128 256 1424832566528 1428150359296 2852982925824 cost_6365_1386_block26 cost_6365_1386_block27 rfl rfl rfl

private theorem cost_6365_1386_join0_28 : P1_7_1_3.blockEstimate 6365 1386 4970 256 = 2842984098304 :=
  @P1_7_1_3.block_append 6365 1386 4970 5098 128 128 256 1425650652416 1417333445888 2842984098304 cost_6365_1386_block28 cost_6365_1386_block29 rfl rfl rfl

private theorem cost_6365_1386_join0_30 : P1_7_1_3.blockEstimate 6365 1386 5226 256 = 2786445273600 :=
  @P1_7_1_3.block_append 6365 1386 5226 5354 128 128 256 1403198739712 1383246533888 2786445273600 cost_6365_1386_block30 cost_6365_1386_block31 rfl rfl rfl

private theorem cost_6365_1386_join0_32 : P1_7_1_3.blockEstimate 6365 1386 5482 256 = 2683366451712 :=
  @P1_7_1_3.block_append 6365 1386 5482 5610 128 128 256 1357476828416 1325889623296 2683366451712 cost_6365_1386_block32 cost_6365_1386_block33 rfl rfl rfl

private theorem cost_6365_1386_join0_34 : P1_7_1_3.blockEstimate 6365 1386 5738 256 = 2533747632640 :=
  @P1_7_1_3.block_append 6365 1386 5738 5866 128 128 256 1288484918528 1245262714112 2533747632640 cost_6365_1386_block34 cost_6365_1386_block35 rfl rfl rfl

private theorem cost_6365_1386_join0_36 : P1_7_1_3.blockEstimate 6365 1386 5994 256 = 2337588816384 :=
  @P1_7_1_3.block_append 6365 1386 5994 6122 128 128 256 1196223010048 1141365806336 2337588816384 cost_6365_1386_block36 cost_6365_1386_block37 rfl rfl rfl

private theorem cost_6365_1386_join0_38 : P1_7_1_3.blockEstimate 6365 1386 6250 256 = 2095775412744 :=
  @P1_7_1_3.block_append 6365 1386 6250 6378 128 128 256 1080691835239 1015083577505 2095775412744 cost_6365_1386_block38 cost_6365_1386_block39 rfl rfl rfl

private theorem cost_6365_1386_join0_40 : P1_7_1_3.blockEstimate 6365 1386 6506 256 = 1825864340436 :=
  @P1_7_1_3.block_append 6365 1386 6506 6634 128 128 256 947351668286 878512672150 1825864340436 cost_6365_1386_block40 cost_6365_1386_block41 rfl rfl rfl

private theorem cost_6365_1386_join0_42 : P1_7_1_3.blockEstimate 6365 1386 6762 256 = 1548885736406 :=
  @P1_7_1_3.block_append 6365 1386 6762 6890 128 128 256 809131450797 739754285609 1548885736406 cost_6365_1386_block42 cost_6365_1386_block43 rfl rfl rfl

private theorem cost_6365_1386_join0_44 : P1_7_1_3.blockEstimate 6365 1386 7018 256 = 1274013231069 :=
  @P1_7_1_3.block_append 6365 1386 7018 7146 128 128 256 670908878559 603104352510 1274013231069 cost_6365_1386_block44 cost_6365_1386_block45 rfl rfl rfl

private theorem cost_6365_1386_join0_46 : P1_7_1_3.blockEstimate 6365 1386 7274 256 = 1009392785395 :=
  @P1_7_1_3.block_append 6365 1386 7274 7402 128 128 256 536831250144 472561535251 1009392785395 cost_6365_1386_block46 cost_6365_1386_block47 rfl rfl rfl

private theorem cost_6365_1386_join0_48 : P1_7_1_3.blockEstimate 6365 1386 7530 256 = 762539738530 :=
  @P1_7_1_3.block_append 6365 1386 7530 7658 128 128 256 410748592012 351791146518 762539738530 cost_6365_1386_block48 cost_6365_1386_block49 rfl rfl rfl

private theorem cost_6365_1386_join0_50 : P1_7_1_3.blockEstimate 6365 1386 7786 256 = 538909499520 :=
  @P1_7_1_3.block_append 6365 1386 7786 7914 128 128 256 295617452096 243292047424 538909499520 cost_6365_1386_block50 cost_6365_1386_block51 rfl rfl rfl

private theorem cost_6365_1386_join0_52 : P1_7_1_3.blockEstimate 6365 1386 8042 256 = 347435507840 :=
  @P1_7_1_3.block_append 6365 1386 8042 8170 128 128 256 195360634944 152074872896 347435507840 cost_6365_1386_block52 cost_6365_1386_block53 rfl rfl rfl

private theorem cost_6365_1386_join0_54 : P1_7_1_3.blockEstimate 6365 1386 8298 256 = 194133352576 :=
  @P1_7_1_3.block_append 6365 1386 8298 8426 128 128 256 113686419520 80446933056 194133352576 cost_6365_1386_block54 cost_6365_1386_block55 rfl rfl rfl

private theorem cost_6365_1386_join0_56 : P1_7_1_3.blockEstimate 6365 1386 8554 256 = 83029565568 :=
  @P1_7_1_3.block_append 6365 1386 8554 8682 128 128 256 52608071744 30421493824 83029565568 cost_6365_1386_block56 cost_6365_1386_block57 rfl rfl rfl

private theorem cost_6365_1386_join0_58 : P1_7_1_3.blockEstimate 6365 1386 8810 256 = 18150678656 :=
  @P1_7_1_3.block_append 6365 1386 8810 8938 128 128 256 14138857536 4011821120 18150678656 cost_6365_1386_block58 cost_6365_1386_block59 rfl rfl rfl

private theorem cost_6365_1386_join1_0 : P1_7_1_3.blockEstimate 6365 1386 1386 512 = 134594543232 :=
  @P1_7_1_3.block_append 6365 1386 1386 1642 256 256 512 17465884480 117128658752 134594543232 cost_6365_1386_join0_0 cost_6365_1386_join0_2 rfl rfl rfl

private theorem cost_6365_1386_join1_2 : P1_7_1_3.blockEstimate 6365 1386 1898 512 = 870098583168 :=
  @P1_7_1_3.block_append 6365 1386 1898 2154 256 256 512 304225894208 565872688960 870098583168 cost_6365_1386_join0_4 cost_6365_1386_join0_6 rfl rfl rfl

private theorem cost_6365_1386_join1_4 : P1_7_1_3.blockEstimate 6365 1386 2410 512 = 2147721924095 :=
  @P1_7_1_3.block_append 6365 1386 2410 2666 256 256 512 889184141120 1258537782975 2147721924095 cost_6365_1386_join0_8 cost_6365_1386_join0_10 rfl rfl rfl

private theorem cost_6365_1386_join1_6 : P1_7_1_3.blockEstimate 6365 1386 2922 512 = 3555490747392 :=
  @P1_7_1_3.block_append 6365 1386 2922 3178 256 256 512 1619854797312 1935635950080 3555490747392 cost_6365_1386_join0_12 cost_6365_1386_join0_14 rfl rfl rfl

private theorem cost_6365_1386_join1_8 : P1_7_1_3.blockEstimate 6365 1386 3434 512 = 4632455369728 :=
  @P1_7_1_3.block_append 6365 1386 3434 3690 256 256 512 2204877105664 2427578264064 4632455369728 cost_6365_1386_join0_16 cost_6365_1386_join0_18 rfl rfl rfl

private theorem cost_6365_1386_join1_10 : P1_7_1_3.blockEstimate 6365 1386 3946 512 = 5337100014592 :=
  @P1_7_1_3.block_append 6365 1386 3946 4202 256 256 512 2603739425280 2733360589312 5337100014592 cost_6365_1386_join0_20 cost_6365_1386_join0_22 rfl rfl rfl

private theorem cost_6365_1386_join1_12 : P1_7_1_3.blockEstimate 6365 1386 4458 512 = 5669424681984 :=
  @P1_7_1_3.block_append 6365 1386 4458 4714 256 256 512 2816441756160 2852982925824 5669424681984 cost_6365_1386_join0_24 cost_6365_1386_join0_26 rfl rfl rfl

private theorem cost_6365_1386_join1_14 : P1_7_1_3.blockEstimate 6365 1386 4970 512 = 5629429371904 :=
  @P1_7_1_3.block_append 6365 1386 4970 5226 256 256 512 2842984098304 2786445273600 5629429371904 cost_6365_1386_join0_28 cost_6365_1386_join0_30 rfl rfl rfl

private theorem cost_6365_1386_join1_16 : P1_7_1_3.blockEstimate 6365 1386 5482 512 = 5217114084352 :=
  @P1_7_1_3.block_append 6365 1386 5482 5738 256 256 512 2683366451712 2533747632640 5217114084352 cost_6365_1386_join0_32 cost_6365_1386_join0_34 rfl rfl rfl

private theorem cost_6365_1386_join1_18 : P1_7_1_3.blockEstimate 6365 1386 5994 512 = 4433364229128 :=
  @P1_7_1_3.block_append 6365 1386 5994 6250 256 256 512 2337588816384 2095775412744 4433364229128 cost_6365_1386_join0_36 cost_6365_1386_join0_38 rfl rfl rfl

private theorem cost_6365_1386_join1_20 : P1_7_1_3.blockEstimate 6365 1386 6506 512 = 3374750076842 :=
  @P1_7_1_3.block_append 6365 1386 6506 6762 256 256 512 1825864340436 1548885736406 3374750076842 cost_6365_1386_join0_40 cost_6365_1386_join0_42 rfl rfl rfl

private theorem cost_6365_1386_join1_22 : P1_7_1_3.blockEstimate 6365 1386 7018 512 = 2283406016464 :=
  @P1_7_1_3.block_append 6365 1386 7018 7274 256 256 512 1274013231069 1009392785395 2283406016464 cost_6365_1386_join0_44 cost_6365_1386_join0_46 rfl rfl rfl

private theorem cost_6365_1386_join1_24 : P1_7_1_3.blockEstimate 6365 1386 7530 512 = 1301449238050 :=
  @P1_7_1_3.block_append 6365 1386 7530 7786 256 256 512 762539738530 538909499520 1301449238050 cost_6365_1386_join0_48 cost_6365_1386_join0_50 rfl rfl rfl

private theorem cost_6365_1386_join1_26 : P1_7_1_3.blockEstimate 6365 1386 8042 512 = 541568860416 :=
  @P1_7_1_3.block_append 6365 1386 8042 8298 256 256 512 347435507840 194133352576 541568860416 cost_6365_1386_join0_52 cost_6365_1386_join0_54 rfl rfl rfl

private theorem cost_6365_1386_join1_28 : P1_7_1_3.blockEstimate 6365 1386 8554 512 = 101180244224 :=
  @P1_7_1_3.block_append 6365 1386 8554 8810 256 256 512 83029565568 18150678656 101180244224 cost_6365_1386_join0_56 cost_6365_1386_join0_58 rfl rfl rfl

private theorem cost_6365_1386_join2_0 : P1_7_1_3.blockEstimate 6365 1386 1386 1024 = 1004693126400 :=
  @P1_7_1_3.block_append 6365 1386 1386 1898 512 512 1024 134594543232 870098583168 1004693126400 cost_6365_1386_join1_0 cost_6365_1386_join1_2 rfl rfl rfl

private theorem cost_6365_1386_join2_2 : P1_7_1_3.blockEstimate 6365 1386 2410 1024 = 5703212671487 :=
  @P1_7_1_3.block_append 6365 1386 2410 2922 512 512 1024 2147721924095 3555490747392 5703212671487 cost_6365_1386_join1_4 cost_6365_1386_join1_6 rfl rfl rfl

private theorem cost_6365_1386_join2_4 : P1_7_1_3.blockEstimate 6365 1386 3434 1024 = 9969555384320 :=
  @P1_7_1_3.block_append 6365 1386 3434 3946 512 512 1024 4632455369728 5337100014592 9969555384320 cost_6365_1386_join1_8 cost_6365_1386_join1_10 rfl rfl rfl

private theorem cost_6365_1386_join2_6 : P1_7_1_3.blockEstimate 6365 1386 4458 1024 = 11298854053888 :=
  @P1_7_1_3.block_append 6365 1386 4458 4970 512 512 1024 5669424681984 5629429371904 11298854053888 cost_6365_1386_join1_12 cost_6365_1386_join1_14 rfl rfl rfl

private theorem cost_6365_1386_join2_8 : P1_7_1_3.blockEstimate 6365 1386 5482 1024 = 9650478313480 :=
  @P1_7_1_3.block_append 6365 1386 5482 5994 512 512 1024 5217114084352 4433364229128 9650478313480 cost_6365_1386_join1_16 cost_6365_1386_join1_18 rfl rfl rfl

private theorem cost_6365_1386_join2_10 : P1_7_1_3.blockEstimate 6365 1386 6506 1024 = 5658156093306 :=
  @P1_7_1_3.block_append 6365 1386 6506 7018 512 512 1024 3374750076842 2283406016464 5658156093306 cost_6365_1386_join1_20 cost_6365_1386_join1_22 rfl rfl rfl

private theorem cost_6365_1386_join2_12 : P1_7_1_3.blockEstimate 6365 1386 7530 1024 = 1843018098466 :=
  @P1_7_1_3.block_append 6365 1386 7530 8042 512 512 1024 1301449238050 541568860416 1843018098466 cost_6365_1386_join1_24 cost_6365_1386_join1_26 rfl rfl rfl

private theorem cost_6365_1386_join2_14 : P1_7_1_3.blockEstimate 6365 1386 8554 583 = 101381272004 :=
  @P1_7_1_3.block_append 6365 1386 8554 9066 512 71 583 101180244224 201027780 101381272004 cost_6365_1386_join1_28 cost_6365_1386_block60 rfl rfl rfl

private theorem cost_6365_1386_join3_0 : P1_7_1_3.blockEstimate 6365 1386 1386 2048 = 6707905797887 :=
  @P1_7_1_3.block_append 6365 1386 1386 2410 1024 1024 2048 1004693126400 5703212671487 6707905797887 cost_6365_1386_join2_0 cost_6365_1386_join2_2 rfl rfl rfl

private theorem cost_6365_1386_join3_2 : P1_7_1_3.blockEstimate 6365 1386 3434 2048 = 21268409438208 :=
  @P1_7_1_3.block_append 6365 1386 3434 4458 1024 1024 2048 9969555384320 11298854053888 21268409438208 cost_6365_1386_join2_4 cost_6365_1386_join2_6 rfl rfl rfl

private theorem cost_6365_1386_join3_4 : P1_7_1_3.blockEstimate 6365 1386 5482 2048 = 15308634406786 :=
  @P1_7_1_3.block_append 6365 1386 5482 6506 1024 1024 2048 9650478313480 5658156093306 15308634406786 cost_6365_1386_join2_8 cost_6365_1386_join2_10 rfl rfl rfl

private theorem cost_6365_1386_join3_6 : P1_7_1_3.blockEstimate 6365 1386 7530 1607 = 1944399370470 :=
  @P1_7_1_3.block_append 6365 1386 7530 8554 1024 583 1607 1843018098466 101381272004 1944399370470 cost_6365_1386_join2_12 cost_6365_1386_join2_14 rfl rfl rfl

private theorem cost_6365_1386_join4_0 : P1_7_1_3.blockEstimate 6365 1386 1386 4096 = 27976315236095 :=
  @P1_7_1_3.block_append 6365 1386 1386 3434 2048 2048 4096 6707905797887 21268409438208 27976315236095 cost_6365_1386_join3_0 cost_6365_1386_join3_2 rfl rfl rfl

private theorem cost_6365_1386_join4_2 : P1_7_1_3.blockEstimate 6365 1386 5482 3655 = 17253033777256 :=
  @P1_7_1_3.block_append 6365 1386 5482 7530 2048 1607 3655 15308634406786 1944399370470 17253033777256 cost_6365_1386_join3_4 cost_6365_1386_join3_6 rfl rfl rfl

private theorem cost_6365_1386_join5_0 : P1_7_1_3.blockEstimate 6365 1386 1386 7751 = 45229349013351 :=
  @P1_7_1_3.block_append 6365 1386 1386 5482 4096 3655 7751 27976315236095 17253033777256 45229349013351 cost_6365_1386_join4_0 cost_6365_1386_join4_2 rfl rfl rfl

private theorem cost_6365_1386_total : P1_7_1_3.momentEstimate 6365 1386 = 45229349013351 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 6365 + 1386 = 7751 by decide]
  exact cost_6365_1386_join5_0

theorem moment6365_1386 : P1_7_1.groupedPoleMoment 6365 1386 ≤ 45229349013351 :=
  (P1_7_1_3.grouped_bound 6365 1386).trans_eq cost_6365_1386_total
private theorem cost_6493_1396_block0 : P1_7_1_3.blockEstimate 6493 1396 1396 128 = 2288859040 := by decide +kernel

private theorem cost_6493_1396_block1 : P1_7_1_3.blockEstimate 6493 1396 1524 128 = 15539144608 := by decide +kernel

private theorem cost_6493_1396_block2 : P1_7_1_3.blockEstimate 6493 1396 1652 128 = 41195132832 := by decide +kernel

private theorem cost_6493_1396_block3 : P1_7_1_3.blockEstimate 6493 1396 1780 128 = 78451517344 := by decide +kernel

private theorem cost_6493_1396_block4 : P1_7_1_3.blockEstimate 6493 1396 1908 128 = 126502991776 := by decide +kernel

private theorem cost_6493_1396_block5 : P1_7_1_3.blockEstimate 6493 1396 2036 128 = 184544249760 := by decide +kernel

private theorem cost_6493_1396_block6 : P1_7_1_3.blockEstimate 6493 1396 2164 128 = 251769984928 := by decide +kernel

private theorem cost_6493_1396_block7 : P1_7_1_3.blockEstimate 6493 1396 2292 128 = 327374890912 := by decide +kernel

private theorem cost_6493_1396_block8 : P1_7_1_3.blockEstimate 6493 1396 2420 128 = 410553661344 := by decide +kernel

private theorem cost_6493_1396_block9 : P1_7_1_3.blockEstimate 6493 1396 2548 128 = 500500989856 := by decide +kernel

private theorem cost_6493_1396_block10 : P1_7_1_3.blockEstimate 6493 1396 2676 128 = 596410114769 := by decide +kernel

private theorem cost_6493_1396_block11 : P1_7_1_3.blockEstimate 6493 1396 2804 128 = 695198430784 := by decide +kernel

private theorem cost_6493_1396_block12 : P1_7_1_3.blockEstimate 6493 1396 2932 128 = 789475948096 := by decide +kernel

private theorem cost_6493_1396_block13 : P1_7_1_3.blockEstimate 6493 1396 3060 128 = 877894022720 := by decide +kernel

private theorem cost_6493_1396_block14 : P1_7_1_3.blockEstimate 6493 1396 3188 128 = 960452654656 := by decide +kernel

private theorem cost_6493_1396_block15 : P1_7_1_3.blockEstimate 6493 1396 3316 128 = 1037151843904 := by decide +kernel

private theorem cost_6493_1396_block16 : P1_7_1_3.blockEstimate 6493 1396 3444 128 = 1107991590464 := by decide +kernel

private theorem cost_6493_1396_block17 : P1_7_1_3.blockEstimate 6493 1396 3572 128 = 1172971894336 := by decide +kernel

private theorem cost_6493_1396_block18 : P1_7_1_3.blockEstimate 6493 1396 3700 128 = 1232092755520 := by decide +kernel

private theorem cost_6493_1396_block19 : P1_7_1_3.blockEstimate 6493 1396 3828 128 = 1285354174016 := by decide +kernel

private theorem cost_6493_1396_block20 : P1_7_1_3.blockEstimate 6493 1396 3956 128 = 1332756149824 := by decide +kernel

private theorem cost_6493_1396_block21 : P1_7_1_3.blockEstimate 6493 1396 4084 128 = 1374298682944 := by decide +kernel

private theorem cost_6493_1396_block22 : P1_7_1_3.blockEstimate 6493 1396 4212 128 = 1409981773376 := by decide +kernel

private theorem cost_6493_1396_block23 : P1_7_1_3.blockEstimate 6493 1396 4340 128 = 1439805421120 := by decide +kernel

private theorem cost_6493_1396_block24 : P1_7_1_3.blockEstimate 6493 1396 4468 128 = 1463769626176 := by decide +kernel

private theorem cost_6493_1396_block25 : P1_7_1_3.blockEstimate 6493 1396 4596 128 = 1481874388544 := by decide +kernel

private theorem cost_6493_1396_block26 : P1_7_1_3.blockEstimate 6493 1396 4724 128 = 1494119708224 := by decide +kernel

private theorem cost_6493_1396_block27 : P1_7_1_3.blockEstimate 6493 1396 4852 128 = 1500505585216 := by decide +kernel

private theorem cost_6493_1396_block28 : P1_7_1_3.blockEstimate 6493 1396 4980 128 = 1501032019520 := by decide +kernel

private theorem cost_6493_1396_block29 : P1_7_1_3.blockEstimate 6493 1396 5108 128 = 1495699011136 := by decide +kernel

private theorem cost_6493_1396_block30 : P1_7_1_3.blockEstimate 6493 1396 5236 128 = 1484506560064 := by decide +kernel

private theorem cost_6493_1396_block31 : P1_7_1_3.blockEstimate 6493 1396 5364 128 = 1467454666304 := by decide +kernel

private theorem cost_6493_1396_block32 : P1_7_1_3.blockEstimate 6493 1396 5492 128 = 1444543329856 := by decide +kernel

private theorem cost_6493_1396_block33 : P1_7_1_3.blockEstimate 6493 1396 5620 128 = 1415772550720 := by decide +kernel

private theorem cost_6493_1396_block34 : P1_7_1_3.blockEstimate 6493 1396 5748 128 = 1381142328896 := by decide +kernel

private theorem cost_6493_1396_block35 : P1_7_1_3.blockEstimate 6493 1396 5876 128 = 1340652664384 := by decide +kernel

private theorem cost_6493_1396_block36 : P1_7_1_3.blockEstimate 6493 1396 6004 128 = 1294303557184 := by decide +kernel

private theorem cost_6493_1396_block37 : P1_7_1_3.blockEstimate 6493 1396 6132 128 = 1242095007296 := by decide +kernel

private theorem cost_6493_1396_block38 : P1_7_1_3.blockEstimate 6493 1396 6260 128 = 1184027014720 := by decide +kernel

private theorem cost_6493_1396_block39 : P1_7_1_3.blockEstimate 6493 1396 6388 128 = 1120103596568 := by decide +kernel

private theorem cost_6493_1396_block40 : P1_7_1_3.blockEstimate 6493 1396 6516 128 = 1051429916333 := by decide +kernel

private theorem cost_6493_1396_block41 : P1_7_1_3.blockEstimate 6493 1396 6644 128 = 980842707934 := by decide +kernel

private theorem cost_6493_1396_block42 : P1_7_1_3.blockEstimate 6493 1396 6772 128 = 909264719980 := by decide +kernel

private theorem cost_6493_1396_block43 : P1_7_1_3.blockEstimate 6493 1396 6900 128 = 837259652623 := by decide +kernel

private theorem cost_6493_1396_block44 : P1_7_1_3.blockEstimate 6493 1396 7028 128 = 765372758919 := by decide +kernel

private theorem cost_6493_1396_block45 : P1_7_1_3.blockEstimate 6493 1396 7156 128 = 694130846690 := by decide +kernel

private theorem cost_6493_1396_block46 : P1_7_1_3.blockEstimate 6493 1396 7284 128 = 624042275418 := by decide +kernel

private theorem cost_6493_1396_block47 : P1_7_1_3.blockEstimate 6493 1396 7412 128 = 555596959644 := by decide +kernel

private theorem cost_6493_1396_block48 : P1_7_1_3.blockEstimate 6493 1396 7540 128 = 489266366897 := by decide +kernel

private theorem cost_6493_1396_block49 : P1_7_1_3.blockEstimate 6493 1396 7668 128 = 425503517753 := by decide +kernel

private theorem cost_6493_1396_block50 : P1_7_1_3.blockEstimate 6493 1396 7796 128 = 364706373623 := by decide +kernel

private theorem cost_6493_1396_block51 : P1_7_1_3.blockEstimate 6493 1396 7924 128 = 306794947280 := by decide +kernel

private theorem cost_6493_1396_block52 : P1_7_1_3.blockEstimate 6493 1396 8052 128 = 252842393296 := by decide +kernel

private theorem cost_6493_1396_block53 : P1_7_1_3.blockEstimate 6493 1396 8180 128 = 203398388432 := by decide +kernel

private theorem cost_6493_1396_block54 : P1_7_1_3.blockEstimate 6493 1396 8308 128 = 158714590928 := by decide +kernel

private theorem cost_6493_1396_block55 : P1_7_1_3.blockEstimate 6493 1396 8436 128 = 119042659024 := by decide +kernel

private theorem cost_6493_1396_block56 : P1_7_1_3.blockEstimate 6493 1396 8564 128 = 84634250960 := by decide +kernel

private theorem cost_6493_1396_block57 : P1_7_1_3.blockEstimate 6493 1396 8692 128 = 55741024976 := by decide +kernel

private theorem cost_6493_1396_block58 : P1_7_1_3.blockEstimate 6493 1396 8820 128 = 32614639312 := by decide +kernel

private theorem cost_6493_1396_block59 : P1_7_1_3.blockEstimate 6493 1396 8948 128 = 15506752208 := by decide +kernel

private theorem cost_6493_1396_block60 : P1_7_1_3.blockEstimate 6493 1396 9076 128 = 4669021904 := by decide +kernel

private theorem cost_6493_1396_block61 : P1_7_1_3.blockEstimate 6493 1396 9204 81 = 302003863 := by decide +kernel

private theorem cost_6493_1396_join0_0 : P1_7_1_3.blockEstimate 6493 1396 1396 256 = 17828003648 :=
  @P1_7_1_3.block_append 6493 1396 1396 1524 128 128 256 2288859040 15539144608 17828003648 cost_6493_1396_block0 cost_6493_1396_block1 rfl rfl rfl

private theorem cost_6493_1396_join0_2 : P1_7_1_3.blockEstimate 6493 1396 1652 256 = 119646650176 :=
  @P1_7_1_3.block_append 6493 1396 1652 1780 128 128 256 41195132832 78451517344 119646650176 cost_6493_1396_block2 cost_6493_1396_block3 rfl rfl rfl

private theorem cost_6493_1396_join0_4 : P1_7_1_3.blockEstimate 6493 1396 1908 256 = 311047241536 :=
  @P1_7_1_3.block_append 6493 1396 1908 2036 128 128 256 126502991776 184544249760 311047241536 cost_6493_1396_block4 cost_6493_1396_block5 rfl rfl rfl

private theorem cost_6493_1396_join0_6 : P1_7_1_3.blockEstimate 6493 1396 2164 256 = 579144875840 :=
  @P1_7_1_3.block_append 6493 1396 2164 2292 128 128 256 251769984928 327374890912 579144875840 cost_6493_1396_block6 cost_6493_1396_block7 rfl rfl rfl

private theorem cost_6493_1396_join0_8 : P1_7_1_3.blockEstimate 6493 1396 2420 256 = 911054651200 :=
  @P1_7_1_3.block_append 6493 1396 2420 2548 128 128 256 410553661344 500500989856 911054651200 cost_6493_1396_block8 cost_6493_1396_block9 rfl rfl rfl

private theorem cost_6493_1396_join0_10 : P1_7_1_3.blockEstimate 6493 1396 2676 256 = 1291608545553 :=
  @P1_7_1_3.block_append 6493 1396 2676 2804 128 128 256 596410114769 695198430784 1291608545553 cost_6493_1396_block10 cost_6493_1396_block11 rfl rfl rfl

private theorem cost_6493_1396_join0_12 : P1_7_1_3.blockEstimate 6493 1396 2932 256 = 1667369970816 :=
  @P1_7_1_3.block_append 6493 1396 2932 3060 128 128 256 789475948096 877894022720 1667369970816 cost_6493_1396_block12 cost_6493_1396_block13 rfl rfl rfl

private theorem cost_6493_1396_join0_14 : P1_7_1_3.blockEstimate 6493 1396 3188 256 = 1997604498560 :=
  @P1_7_1_3.block_append 6493 1396 3188 3316 128 128 256 960452654656 1037151843904 1997604498560 cost_6493_1396_block14 cost_6493_1396_block15 rfl rfl rfl

private theorem cost_6493_1396_join0_16 : P1_7_1_3.blockEstimate 6493 1396 3444 256 = 2280963484800 :=
  @P1_7_1_3.block_append 6493 1396 3444 3572 128 128 256 1107991590464 1172971894336 2280963484800 cost_6493_1396_block16 cost_6493_1396_block17 rfl rfl rfl

private theorem cost_6493_1396_join0_18 : P1_7_1_3.blockEstimate 6493 1396 3700 256 = 2517446929536 :=
  @P1_7_1_3.block_append 6493 1396 3700 3828 128 128 256 1232092755520 1285354174016 2517446929536 cost_6493_1396_block18 cost_6493_1396_block19 rfl rfl rfl

private theorem cost_6493_1396_join0_20 : P1_7_1_3.blockEstimate 6493 1396 3956 256 = 2707054832768 :=
  @P1_7_1_3.block_append 6493 1396 3956 4084 128 128 256 1332756149824 1374298682944 2707054832768 cost_6493_1396_block20 cost_6493_1396_block21 rfl rfl rfl

private theorem cost_6493_1396_join0_22 : P1_7_1_3.blockEstimate 6493 1396 4212 256 = 2849787194496 :=
  @P1_7_1_3.block_append 6493 1396 4212 4340 128 128 256 1409981773376 1439805421120 2849787194496 cost_6493_1396_block22 cost_6493_1396_block23 rfl rfl rfl

private theorem cost_6493_1396_join0_24 : P1_7_1_3.blockEstimate 6493 1396 4468 256 = 2945644014720 :=
  @P1_7_1_3.block_append 6493 1396 4468 4596 128 128 256 1463769626176 1481874388544 2945644014720 cost_6493_1396_block24 cost_6493_1396_block25 rfl rfl rfl

private theorem cost_6493_1396_join0_26 : P1_7_1_3.blockEstimate 6493 1396 4724 256 = 2994625293440 :=
  @P1_7_1_3.block_append 6493 1396 4724 4852 128 128 256 1494119708224 1500505585216 2994625293440 cost_6493_1396_block26 cost_6493_1396_block27 rfl rfl rfl

private theorem cost_6493_1396_join0_28 : P1_7_1_3.blockEstimate 6493 1396 4980 256 = 2996731030656 :=
  @P1_7_1_3.block_append 6493 1396 4980 5108 128 128 256 1501032019520 1495699011136 2996731030656 cost_6493_1396_block28 cost_6493_1396_block29 rfl rfl rfl

private theorem cost_6493_1396_join0_30 : P1_7_1_3.blockEstimate 6493 1396 5236 256 = 2951961226368 :=
  @P1_7_1_3.block_append 6493 1396 5236 5364 128 128 256 1484506560064 1467454666304 2951961226368 cost_6493_1396_block30 cost_6493_1396_block31 rfl rfl rfl

private theorem cost_6493_1396_join0_32 : P1_7_1_3.blockEstimate 6493 1396 5492 256 = 2860315880576 :=
  @P1_7_1_3.block_append 6493 1396 5492 5620 128 128 256 1444543329856 1415772550720 2860315880576 cost_6493_1396_block32 cost_6493_1396_block33 rfl rfl rfl

private theorem cost_6493_1396_join0_34 : P1_7_1_3.blockEstimate 6493 1396 5748 256 = 2721794993280 :=
  @P1_7_1_3.block_append 6493 1396 5748 5876 128 128 256 1381142328896 1340652664384 2721794993280 cost_6493_1396_block34 cost_6493_1396_block35 rfl rfl rfl

private theorem cost_6493_1396_join0_36 : P1_7_1_3.blockEstimate 6493 1396 6004 256 = 2536398564480 :=
  @P1_7_1_3.block_append 6493 1396 6004 6132 128 128 256 1294303557184 1242095007296 2536398564480 cost_6493_1396_block36 cost_6493_1396_block37 rfl rfl rfl

private theorem cost_6493_1396_join0_38 : P1_7_1_3.blockEstimate 6493 1396 6260 256 = 2304130611288 :=
  @P1_7_1_3.block_append 6493 1396 6260 6388 128 128 256 1184027014720 1120103596568 2304130611288 cost_6493_1396_block38 cost_6493_1396_block39 rfl rfl rfl

private theorem cost_6493_1396_join0_40 : P1_7_1_3.blockEstimate 6493 1396 6516 256 = 2032272624267 :=
  @P1_7_1_3.block_append 6493 1396 6516 6644 128 128 256 1051429916333 980842707934 2032272624267 cost_6493_1396_block40 cost_6493_1396_block41 rfl rfl rfl

private theorem cost_6493_1396_join0_42 : P1_7_1_3.blockEstimate 6493 1396 6772 256 = 1746524372603 :=
  @P1_7_1_3.block_append 6493 1396 6772 6900 128 128 256 909264719980 837259652623 1746524372603 cost_6493_1396_block42 cost_6493_1396_block43 rfl rfl rfl

private theorem cost_6493_1396_join0_44 : P1_7_1_3.blockEstimate 6493 1396 7028 256 = 1459503605609 :=
  @P1_7_1_3.block_append 6493 1396 7028 7156 128 128 256 765372758919 694130846690 1459503605609 cost_6493_1396_block44 cost_6493_1396_block45 rfl rfl rfl

private theorem cost_6493_1396_join0_46 : P1_7_1_3.blockEstimate 6493 1396 7284 256 = 1179639235062 :=
  @P1_7_1_3.block_append 6493 1396 7284 7412 128 128 256 624042275418 555596959644 1179639235062 cost_6493_1396_block46 cost_6493_1396_block47 rfl rfl rfl

private theorem cost_6493_1396_join0_48 : P1_7_1_3.blockEstimate 6493 1396 7540 256 = 914769884650 :=
  @P1_7_1_3.block_append 6493 1396 7540 7668 128 128 256 489266366897 425503517753 914769884650 cost_6493_1396_block48 cost_6493_1396_block49 rfl rfl rfl

private theorem cost_6493_1396_join0_50 : P1_7_1_3.blockEstimate 6493 1396 7796 256 = 671501320903 :=
  @P1_7_1_3.block_append 6493 1396 7796 7924 128 128 256 364706373623 306794947280 671501320903 cost_6493_1396_block50 cost_6493_1396_block51 rfl rfl rfl

private theorem cost_6493_1396_join0_52 : P1_7_1_3.blockEstimate 6493 1396 8052 256 = 456240781728 :=
  @P1_7_1_3.block_append 6493 1396 8052 8180 128 128 256 252842393296 203398388432 456240781728 cost_6493_1396_block52 cost_6493_1396_block53 rfl rfl rfl

private theorem cost_6493_1396_join0_54 : P1_7_1_3.blockEstimate 6493 1396 8308 256 = 277757249952 :=
  @P1_7_1_3.block_append 6493 1396 8308 8436 128 128 256 158714590928 119042659024 277757249952 cost_6493_1396_block54 cost_6493_1396_block55 rfl rfl rfl

private theorem cost_6493_1396_join0_56 : P1_7_1_3.blockEstimate 6493 1396 8564 256 = 140375275936 :=
  @P1_7_1_3.block_append 6493 1396 8564 8692 128 128 256 84634250960 55741024976 140375275936 cost_6493_1396_block56 cost_6493_1396_block57 rfl rfl rfl

private theorem cost_6493_1396_join0_58 : P1_7_1_3.blockEstimate 6493 1396 8820 256 = 48121391520 :=
  @P1_7_1_3.block_append 6493 1396 8820 8948 128 128 256 32614639312 15506752208 48121391520 cost_6493_1396_block58 cost_6493_1396_block59 rfl rfl rfl

private theorem cost_6493_1396_join0_60 : P1_7_1_3.blockEstimate 6493 1396 9076 209 = 4971025767 :=
  @P1_7_1_3.block_append 6493 1396 9076 9204 128 81 209 4669021904 302003863 4971025767 cost_6493_1396_block60 cost_6493_1396_block61 rfl rfl rfl

private theorem cost_6493_1396_join1_0 : P1_7_1_3.blockEstimate 6493 1396 1396 512 = 137474653824 :=
  @P1_7_1_3.block_append 6493 1396 1396 1652 256 256 512 17828003648 119646650176 137474653824 cost_6493_1396_join0_0 cost_6493_1396_join0_2 rfl rfl rfl

private theorem cost_6493_1396_join1_2 : P1_7_1_3.blockEstimate 6493 1396 1908 512 = 890192117376 :=
  @P1_7_1_3.block_append 6493 1396 1908 2164 256 256 512 311047241536 579144875840 890192117376 cost_6493_1396_join0_4 cost_6493_1396_join0_6 rfl rfl rfl

private theorem cost_6493_1396_join1_4 : P1_7_1_3.blockEstimate 6493 1396 2420 512 = 2202663196753 :=
  @P1_7_1_3.block_append 6493 1396 2420 2676 256 256 512 911054651200 1291608545553 2202663196753 cost_6493_1396_join0_8 cost_6493_1396_join0_10 rfl rfl rfl

private theorem cost_6493_1396_join1_6 : P1_7_1_3.blockEstimate 6493 1396 2932 512 = 3664974469376 :=
  @P1_7_1_3.block_append 6493 1396 2932 3188 256 256 512 1667369970816 1997604498560 3664974469376 cost_6493_1396_join0_12 cost_6493_1396_join0_14 rfl rfl rfl

private theorem cost_6493_1396_join1_8 : P1_7_1_3.blockEstimate 6493 1396 3444 512 = 4798410414336 :=
  @P1_7_1_3.block_append 6493 1396 3444 3700 256 256 512 2280963484800 2517446929536 4798410414336 cost_6493_1396_join0_16 cost_6493_1396_join0_18 rfl rfl rfl

private theorem cost_6493_1396_join1_10 : P1_7_1_3.blockEstimate 6493 1396 3956 512 = 5556842027264 :=
  @P1_7_1_3.block_append 6493 1396 3956 4212 256 256 512 2707054832768 2849787194496 5556842027264 cost_6493_1396_join0_20 cost_6493_1396_join0_22 rfl rfl rfl

private theorem cost_6493_1396_join1_12 : P1_7_1_3.blockEstimate 6493 1396 4468 512 = 5940269308160 :=
  @P1_7_1_3.block_append 6493 1396 4468 4724 256 256 512 2945644014720 2994625293440 5940269308160 cost_6493_1396_join0_24 cost_6493_1396_join0_26 rfl rfl rfl

private theorem cost_6493_1396_join1_14 : P1_7_1_3.blockEstimate 6493 1396 4980 512 = 5948692257024 :=
  @P1_7_1_3.block_append 6493 1396 4980 5236 256 256 512 2996731030656 2951961226368 5948692257024 cost_6493_1396_join0_28 cost_6493_1396_join0_30 rfl rfl rfl

private theorem cost_6493_1396_join1_16 : P1_7_1_3.blockEstimate 6493 1396 5492 512 = 5582110873856 :=
  @P1_7_1_3.block_append 6493 1396 5492 5748 256 256 512 2860315880576 2721794993280 5582110873856 cost_6493_1396_join0_32 cost_6493_1396_join0_34 rfl rfl rfl

private theorem cost_6493_1396_join1_18 : P1_7_1_3.blockEstimate 6493 1396 6004 512 = 4840529175768 :=
  @P1_7_1_3.block_append 6493 1396 6004 6260 256 256 512 2536398564480 2304130611288 4840529175768 cost_6493_1396_join0_36 cost_6493_1396_join0_38 rfl rfl rfl

private theorem cost_6493_1396_join1_20 : P1_7_1_3.blockEstimate 6493 1396 6516 512 = 3778796996870 :=
  @P1_7_1_3.block_append 6493 1396 6516 6772 256 256 512 2032272624267 1746524372603 3778796996870 cost_6493_1396_join0_40 cost_6493_1396_join0_42 rfl rfl rfl

private theorem cost_6493_1396_join1_22 : P1_7_1_3.blockEstimate 6493 1396 7028 512 = 2639142840671 :=
  @P1_7_1_3.block_append 6493 1396 7028 7284 256 256 512 1459503605609 1179639235062 2639142840671 cost_6493_1396_join0_44 cost_6493_1396_join0_46 rfl rfl rfl

private theorem cost_6493_1396_join1_24 : P1_7_1_3.blockEstimate 6493 1396 7540 512 = 1586271205553 :=
  @P1_7_1_3.block_append 6493 1396 7540 7796 256 256 512 914769884650 671501320903 1586271205553 cost_6493_1396_join0_48 cost_6493_1396_join0_50 rfl rfl rfl

private theorem cost_6493_1396_join1_26 : P1_7_1_3.blockEstimate 6493 1396 8052 512 = 733998031680 :=
  @P1_7_1_3.block_append 6493 1396 8052 8308 256 256 512 456240781728 277757249952 733998031680 cost_6493_1396_join0_52 cost_6493_1396_join0_54 rfl rfl rfl

private theorem cost_6493_1396_join1_28 : P1_7_1_3.blockEstimate 6493 1396 8564 512 = 188496667456 :=
  @P1_7_1_3.block_append 6493 1396 8564 8820 256 256 512 140375275936 48121391520 188496667456 cost_6493_1396_join0_56 cost_6493_1396_join0_58 rfl rfl rfl

private theorem cost_6493_1396_join2_0 : P1_7_1_3.blockEstimate 6493 1396 1396 1024 = 1027666771200 :=
  @P1_7_1_3.block_append 6493 1396 1396 1908 512 512 1024 137474653824 890192117376 1027666771200 cost_6493_1396_join1_0 cost_6493_1396_join1_2 rfl rfl rfl

private theorem cost_6493_1396_join2_2 : P1_7_1_3.blockEstimate 6493 1396 2420 1024 = 5867637666129 :=
  @P1_7_1_3.block_append 6493 1396 2420 2932 512 512 1024 2202663196753 3664974469376 5867637666129 cost_6493_1396_join1_4 cost_6493_1396_join1_6 rfl rfl rfl

private theorem cost_6493_1396_join2_4 : P1_7_1_3.blockEstimate 6493 1396 3444 1024 = 10355252441600 :=
  @P1_7_1_3.block_append 6493 1396 3444 3956 512 512 1024 4798410414336 5556842027264 10355252441600 cost_6493_1396_join1_8 cost_6493_1396_join1_10 rfl rfl rfl

private theorem cost_6493_1396_join2_6 : P1_7_1_3.blockEstimate 6493 1396 4468 1024 = 11888961565184 :=
  @P1_7_1_3.block_append 6493 1396 4468 4980 512 512 1024 5940269308160 5948692257024 11888961565184 cost_6493_1396_join1_12 cost_6493_1396_join1_14 rfl rfl rfl

private theorem cost_6493_1396_join2_8 : P1_7_1_3.blockEstimate 6493 1396 5492 1024 = 10422640049624 :=
  @P1_7_1_3.block_append 6493 1396 5492 6004 512 512 1024 5582110873856 4840529175768 10422640049624 cost_6493_1396_join1_16 cost_6493_1396_join1_18 rfl rfl rfl

private theorem cost_6493_1396_join2_10 : P1_7_1_3.blockEstimate 6493 1396 6516 1024 = 6417939837541 :=
  @P1_7_1_3.block_append 6493 1396 6516 7028 512 512 1024 3778796996870 2639142840671 6417939837541 cost_6493_1396_join1_20 cost_6493_1396_join1_22 rfl rfl rfl

private theorem cost_6493_1396_join2_12 : P1_7_1_3.blockEstimate 6493 1396 7540 1024 = 2320269237233 :=
  @P1_7_1_3.block_append 6493 1396 7540 8052 512 512 1024 1586271205553 733998031680 2320269237233 cost_6493_1396_join1_24 cost_6493_1396_join1_26 rfl rfl rfl

private theorem cost_6493_1396_join2_14 : P1_7_1_3.blockEstimate 6493 1396 8564 721 = 193467693223 :=
  @P1_7_1_3.block_append 6493 1396 8564 9076 512 209 721 188496667456 4971025767 193467693223 cost_6493_1396_join1_28 cost_6493_1396_join0_60 rfl rfl rfl

private theorem cost_6493_1396_join3_0 : P1_7_1_3.blockEstimate 6493 1396 1396 2048 = 6895304437329 :=
  @P1_7_1_3.block_append 6493 1396 1396 2420 1024 1024 2048 1027666771200 5867637666129 6895304437329 cost_6493_1396_join2_0 cost_6493_1396_join2_2 rfl rfl rfl

private theorem cost_6493_1396_join3_2 : P1_7_1_3.blockEstimate 6493 1396 3444 2048 = 22244214006784 :=
  @P1_7_1_3.block_append 6493 1396 3444 4468 1024 1024 2048 10355252441600 11888961565184 22244214006784 cost_6493_1396_join2_4 cost_6493_1396_join2_6 rfl rfl rfl

private theorem cost_6493_1396_join3_4 : P1_7_1_3.blockEstimate 6493 1396 5492 2048 = 16840579887165 :=
  @P1_7_1_3.block_append 6493 1396 5492 6516 1024 1024 2048 10422640049624 6417939837541 16840579887165 cost_6493_1396_join2_8 cost_6493_1396_join2_10 rfl rfl rfl

private theorem cost_6493_1396_join3_6 : P1_7_1_3.blockEstimate 6493 1396 7540 1745 = 2513736930456 :=
  @P1_7_1_3.block_append 6493 1396 7540 8564 1024 721 1745 2320269237233 193467693223 2513736930456 cost_6493_1396_join2_12 cost_6493_1396_join2_14 rfl rfl rfl

private theorem cost_6493_1396_join4_0 : P1_7_1_3.blockEstimate 6493 1396 1396 4096 = 29139518444113 :=
  @P1_7_1_3.block_append 6493 1396 1396 3444 2048 2048 4096 6895304437329 22244214006784 29139518444113 cost_6493_1396_join3_0 cost_6493_1396_join3_2 rfl rfl rfl

private theorem cost_6493_1396_join4_2 : P1_7_1_3.blockEstimate 6493 1396 5492 3793 = 19354316817621 :=
  @P1_7_1_3.block_append 6493 1396 5492 7540 2048 1745 3793 16840579887165 2513736930456 19354316817621 cost_6493_1396_join3_4 cost_6493_1396_join3_6 rfl rfl rfl

private theorem cost_6493_1396_join5_0 : P1_7_1_3.blockEstimate 6493 1396 1396 7889 = 48493835261734 :=
  @P1_7_1_3.block_append 6493 1396 1396 5492 4096 3793 7889 29139518444113 19354316817621 48493835261734 cost_6493_1396_join4_0 cost_6493_1396_join4_2 rfl rfl rfl

private theorem cost_6493_1396_total : P1_7_1_3.momentEstimate 6493 1396 = 48493835261734 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 6493 + 1396 = 7889 by decide]
  exact cost_6493_1396_join5_0

theorem moment6493_1396 : P1_7_1.groupedPoleMoment 6493 1396 ≤ 48493835261734 :=
  (P1_7_1_3.grouped_bound 6493 1396).trans_eq cost_6493_1396_total
private theorem cost_6596_1418_block0 : P1_7_1_3.blockEstimate 6596 1418 1418 128 = 2325708320 := by decide +kernel

private theorem cost_6596_1418_block1 : P1_7_1_3.blockEstimate 6596 1418 1546 128 = 15793688096 := by decide +kernel

private theorem cost_6596_1418_block2 : P1_7_1_3.blockEstimate 6596 1418 1674 128 = 41883377184 := by decide +kernel

private theorem cost_6596_1418_block3 : P1_7_1_3.blockEstimate 6596 1418 1802 128 = 79789469216 := by decide +kernel

private theorem cost_6596_1418_block4 : P1_7_1_3.blockEstimate 6596 1418 1930 128 = 128706657824 := by decide +kernel

private theorem cost_6596_1418_block5 : P1_7_1_3.blockEstimate 6596 1418 2058 128 = 187829636640 := by decide +kernel

private theorem cost_6596_1418_block6 : P1_7_1_3.blockEstimate 6596 1418 2186 128 = 256353099296 := by decide +kernel

private theorem cost_6596_1418_block7 : P1_7_1_3.blockEstimate 6596 1418 2314 128 = 333471739424 := by decide +kernel

private theorem cost_6596_1418_block8 : P1_7_1_3.blockEstimate 6596 1418 2442 128 = 418380250656 := by decide +kernel

private theorem cost_6596_1418_block9 : P1_7_1_3.blockEstimate 6596 1418 2570 128 = 510273326624 := by decide +kernel

private theorem cost_6596_1418_block10 : P1_7_1_3.blockEstimate 6596 1418 2698 128 = 608345660960 := by decide +kernel

private theorem cost_6596_1418_block11 : P1_7_1_3.blockEstimate 6596 1418 2826 128 = 710398208586 := by decide +kernel

private theorem cost_6596_1418_block12 : P1_7_1_3.blockEstimate 6596 1418 2954 128 = 808809929664 := by decide +kernel

private theorem cost_6596_1418_block13 : P1_7_1_3.blockEstimate 6596 1418 3082 128 = 901270789056 := by decide +kernel

private theorem cost_6596_1418_block14 : P1_7_1_3.blockEstimate 6596 1418 3210 128 = 987779931072 := by decide +kernel

private theorem cost_6596_1418_block15 : P1_7_1_3.blockEstimate 6596 1418 3338 128 = 1068337355712 := by decide +kernel

private theorem cost_6596_1418_block16 : P1_7_1_3.blockEstimate 6596 1418 3466 128 = 1142943062976 := by decide +kernel

private theorem cost_6596_1418_block17 : P1_7_1_3.blockEstimate 6596 1418 3594 128 = 1211597052864 := by decide +kernel

private theorem cost_6596_1418_block18 : P1_7_1_3.blockEstimate 6596 1418 3722 128 = 1274299325376 := by decide +kernel

private theorem cost_6596_1418_block19 : P1_7_1_3.blockEstimate 6596 1418 3850 128 = 1331049880512 := by decide +kernel

private theorem cost_6596_1418_block20 : P1_7_1_3.blockEstimate 6596 1418 3978 128 = 1381848718272 := by decide +kernel

private theorem cost_6596_1418_block21 : P1_7_1_3.blockEstimate 6596 1418 4106 128 = 1426695838656 := by decide +kernel

private theorem cost_6596_1418_block22 : P1_7_1_3.blockEstimate 6596 1418 4234 128 = 1465591241664 := by decide +kernel

private theorem cost_6596_1418_block23 : P1_7_1_3.blockEstimate 6596 1418 4362 128 = 1498534927296 := by decide +kernel

private theorem cost_6596_1418_block24 : P1_7_1_3.blockEstimate 6596 1418 4490 128 = 1525526895552 := by decide +kernel

private theorem cost_6596_1418_block25 : P1_7_1_3.blockEstimate 6596 1418 4618 128 = 1546567146432 := by decide +kernel

private theorem cost_6596_1418_block26 : P1_7_1_3.blockEstimate 6596 1418 4746 128 = 1561655679936 := by decide +kernel

private theorem cost_6596_1418_block27 : P1_7_1_3.blockEstimate 6596 1418 4874 128 = 1570792496064 := by decide +kernel

private theorem cost_6596_1418_block28 : P1_7_1_3.blockEstimate 6596 1418 5002 128 = 1573977594816 := by decide +kernel

private theorem cost_6596_1418_block29 : P1_7_1_3.blockEstimate 6596 1418 5130 128 = 1571210976192 := by decide +kernel

private theorem cost_6596_1418_block30 : P1_7_1_3.blockEstimate 6596 1418 5258 128 = 1562492640192 := by decide +kernel

private theorem cost_6596_1418_block31 : P1_7_1_3.blockEstimate 6596 1418 5386 128 = 1547822586816 := by decide +kernel

private theorem cost_6596_1418_block32 : P1_7_1_3.blockEstimate 6596 1418 5514 128 = 1527200816064 := by decide +kernel

private theorem cost_6596_1418_block33 : P1_7_1_3.blockEstimate 6596 1418 5642 128 = 1500627327936 := by decide +kernel

private theorem cost_6596_1418_block34 : P1_7_1_3.blockEstimate 6596 1418 5770 128 = 1468102122432 := by decide +kernel

private theorem cost_6596_1418_block35 : P1_7_1_3.blockEstimate 6596 1418 5898 128 = 1429625199552 := by decide +kernel

private theorem cost_6596_1418_block36 : P1_7_1_3.blockEstimate 6596 1418 6026 128 = 1385196559296 := by decide +kernel

private theorem cost_6596_1418_block37 : P1_7_1_3.blockEstimate 6596 1418 6154 128 = 1334816201664 := by decide +kernel

private theorem cost_6596_1418_block38 : P1_7_1_3.blockEstimate 6596 1418 6282 128 = 1278484126656 := by decide +kernel

private theorem cost_6596_1418_block39 : P1_7_1_3.blockEstimate 6596 1418 6410 128 = 1216200334272 := by decide +kernel

private theorem cost_6596_1418_block40 : P1_7_1_3.blockEstimate 6596 1418 6538 128 = 1148076864972 := by decide +kernel

private theorem cost_6596_1418_block41 : P1_7_1_3.blockEstimate 6596 1418 6666 128 = 1076259976846 := by decide +kernel

private theorem cost_6596_1418_block42 : P1_7_1_3.blockEstimate 6596 1418 6794 128 = 1002997354375 := by decide +kernel

private theorem cost_6596_1418_block43 : P1_7_1_3.blockEstimate 6596 1418 6922 128 = 928923307986 := by decide +kernel

private theorem cost_6596_1418_block44 : P1_7_1_3.blockEstimate 6596 1418 7050 128 = 854595493083 := by decide +kernel

private theorem cost_6596_1418_block45 : P1_7_1_3.blockEstimate 6596 1418 7178 128 = 780553406074 := by decide +kernel

private theorem cost_6596_1418_block46 : P1_7_1_3.blockEstimate 6596 1418 7306 128 = 707318381615 := by decide +kernel

private theorem cost_6596_1418_block47 : P1_7_1_3.blockEstimate 6596 1418 7434 128 = 635393594867 := by decide +kernel

private theorem cost_6596_1418_block48 : P1_7_1_3.blockEstimate 6596 1418 7562 128 = 565264058687 := by decide +kernel

private theorem cost_6596_1418_block49 : P1_7_1_3.blockEstimate 6596 1418 7690 128 = 497396627839 := by decide +kernel

private theorem cost_6596_1418_block50 : P1_7_1_3.blockEstimate 6596 1418 7818 128 = 432239994618 := by decide +kernel

private theorem cost_6596_1418_block51 : P1_7_1_3.blockEstimate 6596 1418 7946 128 = 370118743697 := by decide +kernel

private theorem cost_6596_1418_block52 : P1_7_1_3.blockEstimate 6596 1418 8074 128 = 311016977328 := by decide +kernel

private theorem cost_6596_1418_block53 : P1_7_1_3.blockEstimate 6596 1418 8202 128 = 256128102320 := by decide +kernel

private theorem cost_6596_1418_block54 : P1_7_1_3.blockEstimate 6596 1418 8330 128 = 205861678000 := by decide +kernel

private theorem cost_6596_1418_block55 : P1_7_1_3.blockEstimate 6596 1418 8458 128 = 160469362608 := by decide +kernel

private theorem cost_6596_1418_block56 : P1_7_1_3.blockEstimate 6596 1418 8586 128 = 120202814384 := by decide +kernel

private theorem cost_6596_1418_block57 : P1_7_1_3.blockEstimate 6596 1418 8714 128 = 85313691568 := by decide +kernel

private theorem cost_6596_1418_block58 : P1_7_1_3.blockEstimate 6596 1418 8842 128 = 56053652400 := by decide +kernel

private theorem cost_6596_1418_block59 : P1_7_1_3.blockEstimate 6596 1418 8970 128 = 32674355120 := by decide +kernel

private theorem cost_6596_1418_block60 : P1_7_1_3.blockEstimate 6596 1418 9098 128 = 15427457968 := by decide +kernel

private theorem cost_6596_1418_block61 : P1_7_1_3.blockEstimate 6596 1418 9226 128 = 4564619184 := by decide +kernel

private theorem cost_6596_1418_block62 : P1_7_1_3.blockEstimate 6596 1418 9354 78 = 274605830 := by decide +kernel

private theorem cost_6596_1418_join0_0 : P1_7_1_3.blockEstimate 6596 1418 1418 256 = 18119396416 :=
  @P1_7_1_3.block_append 6596 1418 1418 1546 128 128 256 2325708320 15793688096 18119396416 cost_6596_1418_block0 cost_6596_1418_block1 rfl rfl rfl

private theorem cost_6596_1418_join0_2 : P1_7_1_3.blockEstimate 6596 1418 1674 256 = 121672846400 :=
  @P1_7_1_3.block_append 6596 1418 1674 1802 128 128 256 41883377184 79789469216 121672846400 cost_6596_1418_block2 cost_6596_1418_block3 rfl rfl rfl

private theorem cost_6596_1418_join0_4 : P1_7_1_3.blockEstimate 6596 1418 1930 256 = 316536294464 :=
  @P1_7_1_3.block_append 6596 1418 1930 2058 128 128 256 128706657824 187829636640 316536294464 cost_6596_1418_block4 cost_6596_1418_block5 rfl rfl rfl

private theorem cost_6596_1418_join0_6 : P1_7_1_3.blockEstimate 6596 1418 2186 256 = 589824838720 :=
  @P1_7_1_3.block_append 6596 1418 2186 2314 128 128 256 256353099296 333471739424 589824838720 cost_6596_1418_block6 cost_6596_1418_block7 rfl rfl rfl

private theorem cost_6596_1418_join0_8 : P1_7_1_3.blockEstimate 6596 1418 2442 256 = 928653577280 :=
  @P1_7_1_3.block_append 6596 1418 2442 2570 128 128 256 418380250656 510273326624 928653577280 cost_6596_1418_block8 cost_6596_1418_block9 rfl rfl rfl

private theorem cost_6596_1418_join0_10 : P1_7_1_3.blockEstimate 6596 1418 2698 256 = 1318743869546 :=
  @P1_7_1_3.block_append 6596 1418 2698 2826 128 128 256 608345660960 710398208586 1318743869546 cost_6596_1418_block10 cost_6596_1418_block11 rfl rfl rfl

private theorem cost_6596_1418_join0_12 : P1_7_1_3.blockEstimate 6596 1418 2954 256 = 1710080718720 :=
  @P1_7_1_3.block_append 6596 1418 2954 3082 128 128 256 808809929664 901270789056 1710080718720 cost_6596_1418_block12 cost_6596_1418_block13 rfl rfl rfl

private theorem cost_6596_1418_join0_14 : P1_7_1_3.blockEstimate 6596 1418 3210 256 = 2056117286784 :=
  @P1_7_1_3.block_append 6596 1418 3210 3338 128 128 256 987779931072 1068337355712 2056117286784 cost_6596_1418_block14 cost_6596_1418_block15 rfl rfl rfl

private theorem cost_6596_1418_join0_16 : P1_7_1_3.blockEstimate 6596 1418 3466 256 = 2354540115840 :=
  @P1_7_1_3.block_append 6596 1418 3466 3594 128 128 256 1142943062976 1211597052864 2354540115840 cost_6596_1418_block16 cost_6596_1418_block17 rfl rfl rfl

private theorem cost_6596_1418_join0_18 : P1_7_1_3.blockEstimate 6596 1418 3722 256 = 2605349205888 :=
  @P1_7_1_3.block_append 6596 1418 3722 3850 128 128 256 1274299325376 1331049880512 2605349205888 cost_6596_1418_block18 cost_6596_1418_block19 rfl rfl rfl

private theorem cost_6596_1418_join0_20 : P1_7_1_3.blockEstimate 6596 1418 3978 256 = 2808544556928 :=
  @P1_7_1_3.block_append 6596 1418 3978 4106 128 128 256 1381848718272 1426695838656 2808544556928 cost_6596_1418_block20 cost_6596_1418_block21 rfl rfl rfl

private theorem cost_6596_1418_join0_22 : P1_7_1_3.blockEstimate 6596 1418 4234 256 = 2964126168960 :=
  @P1_7_1_3.block_append 6596 1418 4234 4362 128 128 256 1465591241664 1498534927296 2964126168960 cost_6596_1418_block22 cost_6596_1418_block23 rfl rfl rfl

private theorem cost_6596_1418_join0_24 : P1_7_1_3.blockEstimate 6596 1418 4490 256 = 3072094041984 :=
  @P1_7_1_3.block_append 6596 1418 4490 4618 128 128 256 1525526895552 1546567146432 3072094041984 cost_6596_1418_block24 cost_6596_1418_block25 rfl rfl rfl

private theorem cost_6596_1418_join0_26 : P1_7_1_3.blockEstimate 6596 1418 4746 256 = 3132448176000 :=
  @P1_7_1_3.block_append 6596 1418 4746 4874 128 128 256 1561655679936 1570792496064 3132448176000 cost_6596_1418_block26 cost_6596_1418_block27 rfl rfl rfl

private theorem cost_6596_1418_join0_28 : P1_7_1_3.blockEstimate 6596 1418 5002 256 = 3145188571008 :=
  @P1_7_1_3.block_append 6596 1418 5002 5130 128 128 256 1573977594816 1571210976192 3145188571008 cost_6596_1418_block28 cost_6596_1418_block29 rfl rfl rfl

private theorem cost_6596_1418_join0_30 : P1_7_1_3.blockEstimate 6596 1418 5258 256 = 3110315227008 :=
  @P1_7_1_3.block_append 6596 1418 5258 5386 128 128 256 1562492640192 1547822586816 3110315227008 cost_6596_1418_block30 cost_6596_1418_block31 rfl rfl rfl

private theorem cost_6596_1418_join0_32 : P1_7_1_3.blockEstimate 6596 1418 5514 256 = 3027828144000 :=
  @P1_7_1_3.block_append 6596 1418 5514 5642 128 128 256 1527200816064 1500627327936 3027828144000 cost_6596_1418_block32 cost_6596_1418_block33 rfl rfl rfl

private theorem cost_6596_1418_join0_34 : P1_7_1_3.blockEstimate 6596 1418 5770 256 = 2897727321984 :=
  @P1_7_1_3.block_append 6596 1418 5770 5898 128 128 256 1468102122432 1429625199552 2897727321984 cost_6596_1418_block34 cost_6596_1418_block35 rfl rfl rfl

private theorem cost_6596_1418_join0_36 : P1_7_1_3.blockEstimate 6596 1418 6026 256 = 2720012760960 :=
  @P1_7_1_3.block_append 6596 1418 6026 6154 128 128 256 1385196559296 1334816201664 2720012760960 cost_6596_1418_block36 cost_6596_1418_block37 rfl rfl rfl

private theorem cost_6596_1418_join0_38 : P1_7_1_3.blockEstimate 6596 1418 6282 256 = 2494684460928 :=
  @P1_7_1_3.block_append 6596 1418 6282 6410 128 128 256 1278484126656 1216200334272 2494684460928 cost_6596_1418_block38 cost_6596_1418_block39 rfl rfl rfl

private theorem cost_6596_1418_join0_40 : P1_7_1_3.blockEstimate 6596 1418 6538 256 = 2224336841818 :=
  @P1_7_1_3.block_append 6596 1418 6538 6666 128 128 256 1148076864972 1076259976846 2224336841818 cost_6596_1418_block40 cost_6596_1418_block41 rfl rfl rfl

private theorem cost_6596_1418_join0_42 : P1_7_1_3.blockEstimate 6596 1418 6794 256 = 1931920662361 :=
  @P1_7_1_3.block_append 6596 1418 6794 6922 128 128 256 1002997354375 928923307986 1931920662361 cost_6596_1418_block42 cost_6596_1418_block43 rfl rfl rfl

private theorem cost_6596_1418_join0_44 : P1_7_1_3.blockEstimate 6596 1418 7050 256 = 1635148899157 :=
  @P1_7_1_3.block_append 6596 1418 7050 7178 128 128 256 854595493083 780553406074 1635148899157 cost_6596_1418_block44 cost_6596_1418_block45 rfl rfl rfl

private theorem cost_6596_1418_join0_46 : P1_7_1_3.blockEstimate 6596 1418 7306 256 = 1342711976482 :=
  @P1_7_1_3.block_append 6596 1418 7306 7434 128 128 256 707318381615 635393594867 1342711976482 cost_6596_1418_block46 cost_6596_1418_block47 rfl rfl rfl

private theorem cost_6596_1418_join0_48 : P1_7_1_3.blockEstimate 6596 1418 7562 256 = 1062660686526 :=
  @P1_7_1_3.block_append 6596 1418 7562 7690 128 128 256 565264058687 497396627839 1062660686526 cost_6596_1418_block48 cost_6596_1418_block49 rfl rfl rfl

private theorem cost_6596_1418_join0_50 : P1_7_1_3.blockEstimate 6596 1418 7818 256 = 802358738315 :=
  @P1_7_1_3.block_append 6596 1418 7818 7946 128 128 256 432239994618 370118743697 802358738315 cost_6596_1418_block50 cost_6596_1418_block51 rfl rfl rfl

private theorem cost_6596_1418_join0_52 : P1_7_1_3.blockEstimate 6596 1418 8074 256 = 567145079648 :=
  @P1_7_1_3.block_append 6596 1418 8074 8202 128 128 256 311016977328 256128102320 567145079648 cost_6596_1418_block52 cost_6596_1418_block53 rfl rfl rfl

private theorem cost_6596_1418_join0_54 : P1_7_1_3.blockEstimate 6596 1418 8330 256 = 366331040608 :=
  @P1_7_1_3.block_append 6596 1418 8330 8458 128 128 256 205861678000 160469362608 366331040608 cost_6596_1418_block54 cost_6596_1418_block55 rfl rfl rfl

private theorem cost_6596_1418_join0_56 : P1_7_1_3.blockEstimate 6596 1418 8586 256 = 205516505952 :=
  @P1_7_1_3.block_append 6596 1418 8586 8714 128 128 256 120202814384 85313691568 205516505952 cost_6596_1418_block56 cost_6596_1418_block57 rfl rfl rfl

private theorem cost_6596_1418_join0_58 : P1_7_1_3.blockEstimate 6596 1418 8842 256 = 88728007520 :=
  @P1_7_1_3.block_append 6596 1418 8842 8970 128 128 256 56053652400 32674355120 88728007520 cost_6596_1418_block58 cost_6596_1418_block59 rfl rfl rfl

private theorem cost_6596_1418_join0_60 : P1_7_1_3.blockEstimate 6596 1418 9098 256 = 19992077152 :=
  @P1_7_1_3.block_append 6596 1418 9098 9226 128 128 256 15427457968 4564619184 19992077152 cost_6596_1418_block60 cost_6596_1418_block61 rfl rfl rfl

private theorem cost_6596_1418_join1_0 : P1_7_1_3.blockEstimate 6596 1418 1418 512 = 139792242816 :=
  @P1_7_1_3.block_append 6596 1418 1418 1674 256 256 512 18119396416 121672846400 139792242816 cost_6596_1418_join0_0 cost_6596_1418_join0_2 rfl rfl rfl

private theorem cost_6596_1418_join1_2 : P1_7_1_3.blockEstimate 6596 1418 1930 512 = 906361133184 :=
  @P1_7_1_3.block_append 6596 1418 1930 2186 256 256 512 316536294464 589824838720 906361133184 cost_6596_1418_join0_4 cost_6596_1418_join0_6 rfl rfl rfl

private theorem cost_6596_1418_join1_4 : P1_7_1_3.blockEstimate 6596 1418 2442 512 = 2247397446826 :=
  @P1_7_1_3.block_append 6596 1418 2442 2698 256 256 512 928653577280 1318743869546 2247397446826 cost_6596_1418_join0_8 cost_6596_1418_join0_10 rfl rfl rfl

private theorem cost_6596_1418_join1_6 : P1_7_1_3.blockEstimate 6596 1418 2954 512 = 3766198005504 :=
  @P1_7_1_3.block_append 6596 1418 2954 3210 256 256 512 1710080718720 2056117286784 3766198005504 cost_6596_1418_join0_12 cost_6596_1418_join0_14 rfl rfl rfl

private theorem cost_6596_1418_join1_8 : P1_7_1_3.blockEstimate 6596 1418 3466 512 = 4959889321728 :=
  @P1_7_1_3.block_append 6596 1418 3466 3722 256 256 512 2354540115840 2605349205888 4959889321728 cost_6596_1418_join0_16 cost_6596_1418_join0_18 rfl rfl rfl

private theorem cost_6596_1418_join1_10 : P1_7_1_3.blockEstimate 6596 1418 3978 512 = 5772670725888 :=
  @P1_7_1_3.block_append 6596 1418 3978 4234 256 256 512 2808544556928 2964126168960 5772670725888 cost_6596_1418_join0_20 cost_6596_1418_join0_22 rfl rfl rfl

private theorem cost_6596_1418_join1_12 : P1_7_1_3.blockEstimate 6596 1418 4490 512 = 6204542217984 :=
  @P1_7_1_3.block_append 6596 1418 4490 4746 256 256 512 3072094041984 3132448176000 6204542217984 cost_6596_1418_join0_24 cost_6596_1418_join0_26 rfl rfl rfl

private theorem cost_6596_1418_join1_14 : P1_7_1_3.blockEstimate 6596 1418 5002 512 = 6255503798016 :=
  @P1_7_1_3.block_append 6596 1418 5002 5258 256 256 512 3145188571008 3110315227008 6255503798016 cost_6596_1418_join0_28 cost_6596_1418_join0_30 rfl rfl rfl

private theorem cost_6596_1418_join1_16 : P1_7_1_3.blockEstimate 6596 1418 5514 512 = 5925555465984 :=
  @P1_7_1_3.block_append 6596 1418 5514 5770 256 256 512 3027828144000 2897727321984 5925555465984 cost_6596_1418_join0_32 cost_6596_1418_join0_34 rfl rfl rfl

private theorem cost_6596_1418_join1_18 : P1_7_1_3.blockEstimate 6596 1418 6026 512 = 5214697221888 :=
  @P1_7_1_3.block_append 6596 1418 6026 6282 256 256 512 2720012760960 2494684460928 5214697221888 cost_6596_1418_join0_36 cost_6596_1418_join0_38 rfl rfl rfl

private theorem cost_6596_1418_join1_20 : P1_7_1_3.blockEstimate 6596 1418 6538 512 = 4156257504179 :=
  @P1_7_1_3.block_append 6596 1418 6538 6794 256 256 512 2224336841818 1931920662361 4156257504179 cost_6596_1418_join0_40 cost_6596_1418_join0_42 rfl rfl rfl

private theorem cost_6596_1418_join1_22 : P1_7_1_3.blockEstimate 6596 1418 7050 512 = 2977860875639 :=
  @P1_7_1_3.block_append 6596 1418 7050 7306 256 256 512 1635148899157 1342711976482 2977860875639 cost_6596_1418_join0_44 cost_6596_1418_join0_46 rfl rfl rfl

private theorem cost_6596_1418_join1_24 : P1_7_1_3.blockEstimate 6596 1418 7562 512 = 1865019424841 :=
  @P1_7_1_3.block_append 6596 1418 7562 7818 256 256 512 1062660686526 802358738315 1865019424841 cost_6596_1418_join0_48 cost_6596_1418_join0_50 rfl rfl rfl

private theorem cost_6596_1418_join1_26 : P1_7_1_3.blockEstimate 6596 1418 8074 512 = 933476120256 :=
  @P1_7_1_3.block_append 6596 1418 8074 8330 256 256 512 567145079648 366331040608 933476120256 cost_6596_1418_join0_52 cost_6596_1418_join0_54 rfl rfl rfl

private theorem cost_6596_1418_join1_28 : P1_7_1_3.blockEstimate 6596 1418 8586 512 = 294244513472 :=
  @P1_7_1_3.block_append 6596 1418 8586 8842 256 256 512 205516505952 88728007520 294244513472 cost_6596_1418_join0_56 cost_6596_1418_join0_58 rfl rfl rfl

private theorem cost_6596_1418_join1_30 : P1_7_1_3.blockEstimate 6596 1418 9098 334 = 20266682982 :=
  @P1_7_1_3.block_append 6596 1418 9098 9354 256 78 334 19992077152 274605830 20266682982 cost_6596_1418_join0_60 cost_6596_1418_block62 rfl rfl rfl

private theorem cost_6596_1418_join2_0 : P1_7_1_3.blockEstimate 6596 1418 1418 1024 = 1046153376000 :=
  @P1_7_1_3.block_append 6596 1418 1418 1930 512 512 1024 139792242816 906361133184 1046153376000 cost_6596_1418_join1_0 cost_6596_1418_join1_2 rfl rfl rfl

private theorem cost_6596_1418_join2_2 : P1_7_1_3.blockEstimate 6596 1418 2442 1024 = 6013595452330 :=
  @P1_7_1_3.block_append 6596 1418 2442 2954 512 512 1024 2247397446826 3766198005504 6013595452330 cost_6596_1418_join1_4 cost_6596_1418_join1_6 rfl rfl rfl

private theorem cost_6596_1418_join2_4 : P1_7_1_3.blockEstimate 6596 1418 3466 1024 = 10732560047616 :=
  @P1_7_1_3.block_append 6596 1418 3466 3978 512 512 1024 4959889321728 5772670725888 10732560047616 cost_6596_1418_join1_8 cost_6596_1418_join1_10 rfl rfl rfl

private theorem cost_6596_1418_join2_6 : P1_7_1_3.blockEstimate 6596 1418 4490 1024 = 12460046016000 :=
  @P1_7_1_3.block_append 6596 1418 4490 5002 512 512 1024 6204542217984 6255503798016 12460046016000 cost_6596_1418_join1_12 cost_6596_1418_join1_14 rfl rfl rfl

private theorem cost_6596_1418_join2_8 : P1_7_1_3.blockEstimate 6596 1418 5514 1024 = 11140252687872 :=
  @P1_7_1_3.block_append 6596 1418 5514 6026 512 512 1024 5925555465984 5214697221888 11140252687872 cost_6596_1418_join1_16 cost_6596_1418_join1_18 rfl rfl rfl

private theorem cost_6596_1418_join2_10 : P1_7_1_3.blockEstimate 6596 1418 6538 1024 = 7134118379818 :=
  @P1_7_1_3.block_append 6596 1418 6538 7050 512 512 1024 4156257504179 2977860875639 7134118379818 cost_6596_1418_join1_20 cost_6596_1418_join1_22 rfl rfl rfl

private theorem cost_6596_1418_join2_12 : P1_7_1_3.blockEstimate 6596 1418 7562 1024 = 2798495545097 :=
  @P1_7_1_3.block_append 6596 1418 7562 8074 512 512 1024 1865019424841 933476120256 2798495545097 cost_6596_1418_join1_24 cost_6596_1418_join1_26 rfl rfl rfl

private theorem cost_6596_1418_join2_14 : P1_7_1_3.blockEstimate 6596 1418 8586 846 = 314511196454 :=
  @P1_7_1_3.block_append 6596 1418 8586 9098 512 334 846 294244513472 20266682982 314511196454 cost_6596_1418_join1_28 cost_6596_1418_join1_30 rfl rfl rfl

private theorem cost_6596_1418_join3_0 : P1_7_1_3.blockEstimate 6596 1418 1418 2048 = 7059748828330 :=
  @P1_7_1_3.block_append 6596 1418 1418 2442 1024 1024 2048 1046153376000 6013595452330 7059748828330 cost_6596_1418_join2_0 cost_6596_1418_join2_2 rfl rfl rfl

private theorem cost_6596_1418_join3_2 : P1_7_1_3.blockEstimate 6596 1418 3466 2048 = 23192606063616 :=
  @P1_7_1_3.block_append 6596 1418 3466 4490 1024 1024 2048 10732560047616 12460046016000 23192606063616 cost_6596_1418_join2_4 cost_6596_1418_join2_6 rfl rfl rfl

private theorem cost_6596_1418_join3_4 : P1_7_1_3.blockEstimate 6596 1418 5514 2048 = 18274371067690 :=
  @P1_7_1_3.block_append 6596 1418 5514 6538 1024 1024 2048 11140252687872 7134118379818 18274371067690 cost_6596_1418_join2_8 cost_6596_1418_join2_10 rfl rfl rfl

private theorem cost_6596_1418_join3_6 : P1_7_1_3.blockEstimate 6596 1418 7562 1870 = 3113006741551 :=
  @P1_7_1_3.block_append 6596 1418 7562 8586 1024 846 1870 2798495545097 314511196454 3113006741551 cost_6596_1418_join2_12 cost_6596_1418_join2_14 rfl rfl rfl

private theorem cost_6596_1418_join4_0 : P1_7_1_3.blockEstimate 6596 1418 1418 4096 = 30252354891946 :=
  @P1_7_1_3.block_append 6596 1418 1418 3466 2048 2048 4096 7059748828330 23192606063616 30252354891946 cost_6596_1418_join3_0 cost_6596_1418_join3_2 rfl rfl rfl

private theorem cost_6596_1418_join4_2 : P1_7_1_3.blockEstimate 6596 1418 5514 3918 = 21387377809241 :=
  @P1_7_1_3.block_append 6596 1418 5514 7562 2048 1870 3918 18274371067690 3113006741551 21387377809241 cost_6596_1418_join3_4 cost_6596_1418_join3_6 rfl rfl rfl

private theorem cost_6596_1418_join5_0 : P1_7_1_3.blockEstimate 6596 1418 1418 8014 = 51639732701187 :=
  @P1_7_1_3.block_append 6596 1418 1418 5514 4096 3918 8014 30252354891946 21387377809241 51639732701187 cost_6596_1418_join4_0 cost_6596_1418_join4_2 rfl rfl rfl

private theorem cost_6596_1418_total : P1_7_1_3.momentEstimate 6596 1418 = 51639732701187 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 6596 + 1418 = 8014 by decide]
  exact cost_6596_1418_join5_0

theorem moment6596_1418 : P1_7_1.groupedPoleMoment 6596 1418 ≤ 51639732701187 :=
  (P1_7_1_3.grouped_bound 6596 1418).trans_eq cost_6596_1418_total
private theorem cost_6663_1432_block0 : P1_7_1_3.blockEstimate 6663 1432 1432 128 = 2349678240 := by decide +kernel

private theorem cost_6663_1432_block1 : P1_7_1_3.blockEstimate 6663 1432 1560 128 = 15959264928 := by decide +kernel

private theorem cost_6663_1432_block2 : P1_7_1_3.blockEstimate 6663 1432 1688 128 = 42331070112 := by decide +kernel

private theorem cost_6663_1432_block3 : P1_7_1_3.blockEstimate 6663 1432 1816 128 = 80659787424 := by decide +kernel

private theorem cost_6663_1432_block4 : P1_7_1_3.blockEstimate 6663 1432 1944 128 = 130140110496 := by decide +kernel

private theorem cost_6663_1432_block5 : P1_7_1_3.blockEstimate 6663 1432 2072 128 = 189966732960 := by decide +kernel

private theorem cost_6663_1432_block6 : P1_7_1_3.blockEstimate 6663 1432 2200 128 = 259334348448 := by decide +kernel

private theorem cost_6663_1432_block7 : P1_7_1_3.blockEstimate 6663 1432 2328 128 = 337437650592 := by decide +kernel

private theorem cost_6663_1432_block8 : P1_7_1_3.blockEstimate 6663 1432 2456 128 = 423471333024 := by decide +kernel

private theorem cost_6663_1432_block9 : P1_7_1_3.blockEstimate 6663 1432 2584 128 = 516630089376 := by decide +kernel

private theorem cost_6663_1432_block10 : P1_7_1_3.blockEstimate 6663 1432 2712 128 = 616108613280 := by decide +kernel

private theorem cost_6663_1432_block11 : P1_7_1_3.blockEstimate 6663 1432 2840 128 = 720135523258 := by decide +kernel

private theorem cost_6663_1432_block12 : P1_7_1_3.blockEstimate 6663 1432 2968 128 = 821244366912 := by decide +kernel

private theorem cost_6663_1432_block13 : P1_7_1_3.blockEstimate 6663 1432 3096 128 = 916354846784 := by decide +kernel

private theorem cost_6663_1432_block14 : P1_7_1_3.blockEstimate 6663 1432 3224 128 = 1005454889024 := by decide +kernel

private theorem cost_6663_1432_block15 : P1_7_1_3.blockEstimate 6663 1432 3352 128 = 1088544493632 := by decide +kernel

private theorem cost_6663_1432_block16 : P1_7_1_3.blockEstimate 6663 1432 3480 128 = 1165623660608 := by decide +kernel

private theorem cost_6663_1432_block17 : P1_7_1_3.blockEstimate 6663 1432 3608 128 = 1236692389952 := by decide +kernel

private theorem cost_6663_1432_block18 : P1_7_1_3.blockEstimate 6663 1432 3736 128 = 1301750681664 := by decide +kernel

private theorem cost_6663_1432_block19 : P1_7_1_3.blockEstimate 6663 1432 3864 128 = 1360798535744 := by decide +kernel

private theorem cost_6663_1432_block20 : P1_7_1_3.blockEstimate 6663 1432 3992 128 = 1413835952192 := by decide +kernel

private theorem cost_6663_1432_block21 : P1_7_1_3.blockEstimate 6663 1432 4120 128 = 1460862931008 := by decide +kernel

private theorem cost_6663_1432_block22 : P1_7_1_3.blockEstimate 6663 1432 4248 128 = 1501879472192 := by decide +kernel

private theorem cost_6663_1432_block23 : P1_7_1_3.blockEstimate 6663 1432 4376 128 = 1536885575744 := by decide +kernel

private theorem cost_6663_1432_block24 : P1_7_1_3.blockEstimate 6663 1432 4504 128 = 1565881241664 := by decide +kernel

private theorem cost_6663_1432_block25 : P1_7_1_3.blockEstimate 6663 1432 4632 128 = 1588866469952 := by decide +kernel

private theorem cost_6663_1432_block26 : P1_7_1_3.blockEstimate 6663 1432 4760 128 = 1605841260608 := by decide +kernel

private theorem cost_6663_1432_block27 : P1_7_1_3.blockEstimate 6663 1432 4888 128 = 1616805613632 := by decide +kernel

private theorem cost_6663_1432_block28 : P1_7_1_3.blockEstimate 6663 1432 5016 128 = 1621759529024 := by decide +kernel

private theorem cost_6663_1432_block29 : P1_7_1_3.blockEstimate 6663 1432 5144 128 = 1620703006784 := by decide +kernel

private theorem cost_6663_1432_block30 : P1_7_1_3.blockEstimate 6663 1432 5272 128 = 1613636046912 := by decide +kernel

private theorem cost_6663_1432_block31 : P1_7_1_3.blockEstimate 6663 1432 5400 128 = 1600558649408 := by decide +kernel

private theorem cost_6663_1432_block32 : P1_7_1_3.blockEstimate 6663 1432 5528 128 = 1581470814272 := by decide +kernel

private theorem cost_6663_1432_block33 : P1_7_1_3.blockEstimate 6663 1432 5656 128 = 1556372541504 := by decide +kernel

private theorem cost_6663_1432_block34 : P1_7_1_3.blockEstimate 6663 1432 5784 128 = 1525263831104 := by decide +kernel

private theorem cost_6663_1432_block35 : P1_7_1_3.blockEstimate 6663 1432 5912 128 = 1488144683072 := by decide +kernel

private theorem cost_6663_1432_block36 : P1_7_1_3.blockEstimate 6663 1432 6040 128 = 1445015097408 := by decide +kernel

private theorem cost_6663_1432_block37 : P1_7_1_3.blockEstimate 6663 1432 6168 128 = 1395875074112 := by decide +kernel

private theorem cost_6663_1432_block38 : P1_7_1_3.blockEstimate 6663 1432 6296 128 = 1340724613184 := by decide +kernel

private theorem cost_6663_1432_block39 : P1_7_1_3.blockEstimate 6663 1432 6424 128 = 1279563714624 := by decide +kernel

private theorem cost_6663_1432_block40 : P1_7_1_3.blockEstimate 6663 1432 6552 128 = 1212394073492 := by decide +kernel

private theorem cost_6663_1432_block41 : P1_7_1_3.blockEstimate 6663 1432 6680 128 = 1140225576685 := by decide +kernel

private theorem cost_6663_1432_block42 : P1_7_1_3.blockEstimate 6663 1432 6808 128 = 1065995366128 := by decide +kernel

private theorem cost_6663_1432_block43 : P1_7_1_3.blockEstimate 6663 1432 6936 128 = 990699943458 := by decide +kernel

private theorem cost_6663_1432_block44 : P1_7_1_3.blockEstimate 6663 1432 7064 128 = 914904864262 := by decide +kernel

private theorem cost_6663_1432_block45 : P1_7_1_3.blockEstimate 6663 1432 7192 128 = 839157700714 := by decide +kernel

private theorem cost_6663_1432_block46 : P1_7_1_3.blockEstimate 6663 1432 7320 128 = 763988040973 := by decide +kernel

private theorem cost_6663_1432_block47 : P1_7_1_3.blockEstimate 6663 1432 7448 128 = 689907490702 := by decide +kernel

private theorem cost_6663_1432_block48 : P1_7_1_3.blockEstimate 6663 1432 7576 128 = 617409672379 := by decide +kernel

private theorem cost_6663_1432_block49 : P1_7_1_3.blockEstimate 6663 1432 7704 128 = 546970225582 := by decide +kernel

private theorem cost_6663_1432_block50 : P1_7_1_3.blockEstimate 6663 1432 7832 128 = 479046806251 := by decide +kernel

private theorem cost_6663_1432_block51 : P1_7_1_3.blockEstimate 6663 1432 7960 128 = 414079087562 := by decide +kernel

private theorem cost_6663_1432_block52 : P1_7_1_3.blockEstimate 6663 1432 8088 128 = 352089259355 := by decide +kernel

private theorem cost_6663_1432_block53 : P1_7_1_3.blockEstimate 6663 1432 8216 128 = 293686234368 := by decide +kernel

private theorem cost_6663_1432_block54 : P1_7_1_3.blockEstimate 6663 1432 8344 128 = 239815298304 := by decide +kernel

private theorem cost_6663_1432_block55 : P1_7_1_3.blockEstimate 6663 1432 8472 128 = 190729473280 := by decide +kernel

private theorem cost_6663_1432_block56 : P1_7_1_3.blockEstimate 6663 1432 8600 128 = 146680417536 := by decide +kernel

private theorem cost_6663_1432_block57 : P1_7_1_3.blockEstimate 6663 1432 8728 128 = 107919789312 := by decide +kernel

private theorem cost_6663_1432_block58 : P1_7_1_3.blockEstimate 6663 1432 8856 128 = 74699246848 := by decide +kernel

private theorem cost_6663_1432_block59 : P1_7_1_3.blockEstimate 6663 1432 8984 128 = 47270448384 := by decide +kernel

private theorem cost_6663_1432_block60 : P1_7_1_3.blockEstimate 6663 1432 9112 128 = 25885052160 := by decide +kernel

private theorem cost_6663_1432_block61 : P1_7_1_3.blockEstimate 6663 1432 9240 128 = 10794716416 := by decide +kernel

private theorem cost_6663_1432_block62 : P1_7_1_3.blockEstimate 6663 1432 9368 128 = 2251099392 := by decide +kernel

private theorem cost_6663_1432_block63 : P1_7_1_3.blockEstimate 6663 1432 9496 31 = 18989888 := by decide +kernel

private theorem cost_6663_1432_join0_0 : P1_7_1_3.blockEstimate 6663 1432 1432 256 = 18308943168 :=
  @P1_7_1_3.block_append 6663 1432 1432 1560 128 128 256 2349678240 15959264928 18308943168 cost_6663_1432_block0 cost_6663_1432_block1 rfl rfl rfl

private theorem cost_6663_1432_join0_2 : P1_7_1_3.blockEstimate 6663 1432 1688 256 = 122990857536 :=
  @P1_7_1_3.block_append 6663 1432 1688 1816 128 128 256 42331070112 80659787424 122990857536 cost_6663_1432_block2 cost_6663_1432_block3 rfl rfl rfl

private theorem cost_6663_1432_join0_4 : P1_7_1_3.blockEstimate 6663 1432 1944 256 = 320106843456 :=
  @P1_7_1_3.block_append 6663 1432 1944 2072 128 128 256 130140110496 189966732960 320106843456 cost_6663_1432_block4 cost_6663_1432_block5 rfl rfl rfl

private theorem cost_6663_1432_join0_6 : P1_7_1_3.blockEstimate 6663 1432 2200 256 = 596771999040 :=
  @P1_7_1_3.block_append 6663 1432 2200 2328 128 128 256 259334348448 337437650592 596771999040 cost_6663_1432_block6 cost_6663_1432_block7 rfl rfl rfl

private theorem cost_6663_1432_join0_8 : P1_7_1_3.blockEstimate 6663 1432 2456 256 = 940101422400 :=
  @P1_7_1_3.block_append 6663 1432 2456 2584 128 128 256 423471333024 516630089376 940101422400 cost_6663_1432_block8 cost_6663_1432_block9 rfl rfl rfl

private theorem cost_6663_1432_join0_10 : P1_7_1_3.blockEstimate 6663 1432 2712 256 = 1336244136538 :=
  @P1_7_1_3.block_append 6663 1432 2712 2840 128 128 256 616108613280 720135523258 1336244136538 cost_6663_1432_block10 cost_6663_1432_block11 rfl rfl rfl

private theorem cost_6663_1432_join0_12 : P1_7_1_3.blockEstimate 6663 1432 2968 256 = 1737599213696 :=
  @P1_7_1_3.block_append 6663 1432 2968 3096 128 128 256 821244366912 916354846784 1737599213696 cost_6663_1432_block12 cost_6663_1432_block13 rfl rfl rfl

private theorem cost_6663_1432_join0_14 : P1_7_1_3.blockEstimate 6663 1432 3224 256 = 2093999382656 :=
  @P1_7_1_3.block_append 6663 1432 3224 3352 128 128 256 1005454889024 1088544493632 2093999382656 cost_6663_1432_block14 cost_6663_1432_block15 rfl rfl rfl

private theorem cost_6663_1432_join0_16 : P1_7_1_3.blockEstimate 6663 1432 3480 256 = 2402316050560 :=
  @P1_7_1_3.block_append 6663 1432 3480 3608 128 128 256 1165623660608 1236692389952 2402316050560 cost_6663_1432_block16 cost_6663_1432_block17 rfl rfl rfl

private theorem cost_6663_1432_join0_18 : P1_7_1_3.blockEstimate 6663 1432 3736 256 = 2662549217408 :=
  @P1_7_1_3.block_append 6663 1432 3736 3864 128 128 256 1301750681664 1360798535744 2662549217408 cost_6663_1432_block18 cost_6663_1432_block19 rfl rfl rfl

private theorem cost_6663_1432_join0_20 : P1_7_1_3.blockEstimate 6663 1432 3992 256 = 2874698883200 :=
  @P1_7_1_3.block_append 6663 1432 3992 4120 128 128 256 1413835952192 1460862931008 2874698883200 cost_6663_1432_block20 cost_6663_1432_block21 rfl rfl rfl

private theorem cost_6663_1432_join0_22 : P1_7_1_3.blockEstimate 6663 1432 4248 256 = 3038765047936 :=
  @P1_7_1_3.block_append 6663 1432 4248 4376 128 128 256 1501879472192 1536885575744 3038765047936 cost_6663_1432_block22 cost_6663_1432_block23 rfl rfl rfl

private theorem cost_6663_1432_join0_24 : P1_7_1_3.blockEstimate 6663 1432 4504 256 = 3154747711616 :=
  @P1_7_1_3.block_append 6663 1432 4504 4632 128 128 256 1565881241664 1588866469952 3154747711616 cost_6663_1432_block24 cost_6663_1432_block25 rfl rfl rfl

private theorem cost_6663_1432_join0_26 : P1_7_1_3.blockEstimate 6663 1432 4760 256 = 3222646874240 :=
  @P1_7_1_3.block_append 6663 1432 4760 4888 128 128 256 1605841260608 1616805613632 3222646874240 cost_6663_1432_block26 cost_6663_1432_block27 rfl rfl rfl

private theorem cost_6663_1432_join0_28 : P1_7_1_3.blockEstimate 6663 1432 5016 256 = 3242462535808 :=
  @P1_7_1_3.block_append 6663 1432 5016 5144 128 128 256 1621759529024 1620703006784 3242462535808 cost_6663_1432_block28 cost_6663_1432_block29 rfl rfl rfl

private theorem cost_6663_1432_join0_30 : P1_7_1_3.blockEstimate 6663 1432 5272 256 = 3214194696320 :=
  @P1_7_1_3.block_append 6663 1432 5272 5400 128 128 256 1613636046912 1600558649408 3214194696320 cost_6663_1432_block30 cost_6663_1432_block31 rfl rfl rfl

private theorem cost_6663_1432_join0_32 : P1_7_1_3.blockEstimate 6663 1432 5528 256 = 3137843355776 :=
  @P1_7_1_3.block_append 6663 1432 5528 5656 128 128 256 1581470814272 1556372541504 3137843355776 cost_6663_1432_block32 cost_6663_1432_block33 rfl rfl rfl

private theorem cost_6663_1432_join0_34 : P1_7_1_3.blockEstimate 6663 1432 5784 256 = 3013408514176 :=
  @P1_7_1_3.block_append 6663 1432 5784 5912 128 128 256 1525263831104 1488144683072 3013408514176 cost_6663_1432_block34 cost_6663_1432_block35 rfl rfl rfl

private theorem cost_6663_1432_join0_36 : P1_7_1_3.blockEstimate 6663 1432 6040 256 = 2840890171520 :=
  @P1_7_1_3.block_append 6663 1432 6040 6168 128 128 256 1445015097408 1395875074112 2840890171520 cost_6663_1432_block36 cost_6663_1432_block37 rfl rfl rfl

private theorem cost_6663_1432_join0_38 : P1_7_1_3.blockEstimate 6663 1432 6296 256 = 2620288327808 :=
  @P1_7_1_3.block_append 6663 1432 6296 6424 128 128 256 1340724613184 1279563714624 2620288327808 cost_6663_1432_block38 cost_6663_1432_block39 rfl rfl rfl

private theorem cost_6663_1432_join0_40 : P1_7_1_3.blockEstimate 6663 1432 6552 256 = 2352619650177 :=
  @P1_7_1_3.block_append 6663 1432 6552 6680 128 128 256 1212394073492 1140225576685 2352619650177 cost_6663_1432_block40 cost_6663_1432_block41 rfl rfl rfl

private theorem cost_6663_1432_join0_42 : P1_7_1_3.blockEstimate 6663 1432 6808 256 = 2056695309586 :=
  @P1_7_1_3.block_append 6663 1432 6808 6936 128 128 256 1065995366128 990699943458 2056695309586 cost_6663_1432_block42 cost_6663_1432_block43 rfl rfl rfl

private theorem cost_6663_1432_join0_44 : P1_7_1_3.blockEstimate 6663 1432 7064 256 = 1754062564976 :=
  @P1_7_1_3.block_append 6663 1432 7064 7192 128 128 256 914904864262 839157700714 1754062564976 cost_6663_1432_block44 cost_6663_1432_block45 rfl rfl rfl

private theorem cost_6663_1432_join0_46 : P1_7_1_3.blockEstimate 6663 1432 7320 256 = 1453895531675 :=
  @P1_7_1_3.block_append 6663 1432 7320 7448 128 128 256 763988040973 689907490702 1453895531675 cost_6663_1432_block46 cost_6663_1432_block47 rfl rfl rfl

private theorem cost_6663_1432_join0_48 : P1_7_1_3.blockEstimate 6663 1432 7576 256 = 1164379897961 :=
  @P1_7_1_3.block_append 6663 1432 7576 7704 128 128 256 617409672379 546970225582 1164379897961 cost_6663_1432_block48 cost_6663_1432_block49 rfl rfl rfl

private theorem cost_6663_1432_join0_50 : P1_7_1_3.blockEstimate 6663 1432 7832 256 = 893125893813 :=
  @P1_7_1_3.block_append 6663 1432 7832 7960 128 128 256 479046806251 414079087562 893125893813 cost_6663_1432_block50 cost_6663_1432_block51 rfl rfl rfl

private theorem cost_6663_1432_join0_52 : P1_7_1_3.blockEstimate 6663 1432 8088 256 = 645775493723 :=
  @P1_7_1_3.block_append 6663 1432 8088 8216 128 128 256 352089259355 293686234368 645775493723 cost_6663_1432_block52 cost_6663_1432_block53 rfl rfl rfl

private theorem cost_6663_1432_join0_54 : P1_7_1_3.blockEstimate 6663 1432 8344 256 = 430544771584 :=
  @P1_7_1_3.block_append 6663 1432 8344 8472 128 128 256 239815298304 190729473280 430544771584 cost_6663_1432_block54 cost_6663_1432_block55 rfl rfl rfl

private theorem cost_6663_1432_join0_56 : P1_7_1_3.blockEstimate 6663 1432 8600 256 = 254600206848 :=
  @P1_7_1_3.block_append 6663 1432 8600 8728 128 128 256 146680417536 107919789312 254600206848 cost_6663_1432_block56 cost_6663_1432_block57 rfl rfl rfl

private theorem cost_6663_1432_join0_58 : P1_7_1_3.blockEstimate 6663 1432 8856 256 = 121969695232 :=
  @P1_7_1_3.block_append 6663 1432 8856 8984 128 128 256 74699246848 47270448384 121969695232 cost_6663_1432_block58 cost_6663_1432_block59 rfl rfl rfl

private theorem cost_6663_1432_join0_60 : P1_7_1_3.blockEstimate 6663 1432 9112 256 = 36679768576 :=
  @P1_7_1_3.block_append 6663 1432 9112 9240 128 128 256 25885052160 10794716416 36679768576 cost_6663_1432_block60 cost_6663_1432_block61 rfl rfl rfl

private theorem cost_6663_1432_join0_62 : P1_7_1_3.blockEstimate 6663 1432 9368 159 = 2270089280 :=
  @P1_7_1_3.block_append 6663 1432 9368 9496 128 31 159 2251099392 18989888 2270089280 cost_6663_1432_block62 cost_6663_1432_block63 rfl rfl rfl

private theorem cost_6663_1432_join1_0 : P1_7_1_3.blockEstimate 6663 1432 1432 512 = 141299800704 :=
  @P1_7_1_3.block_append 6663 1432 1432 1688 256 256 512 18308943168 122990857536 141299800704 cost_6663_1432_join0_0 cost_6663_1432_join0_2 rfl rfl rfl

private theorem cost_6663_1432_join1_2 : P1_7_1_3.blockEstimate 6663 1432 1944 512 = 916878842496 :=
  @P1_7_1_3.block_append 6663 1432 1944 2200 256 256 512 320106843456 596771999040 916878842496 cost_6663_1432_join0_4 cost_6663_1432_join0_6 rfl rfl rfl

private theorem cost_6663_1432_join1_4 : P1_7_1_3.blockEstimate 6663 1432 2456 512 = 2276345558938 :=
  @P1_7_1_3.block_append 6663 1432 2456 2712 256 256 512 940101422400 1336244136538 2276345558938 cost_6663_1432_join0_8 cost_6663_1432_join0_10 rfl rfl rfl

private theorem cost_6663_1432_join1_6 : P1_7_1_3.blockEstimate 6663 1432 2968 512 = 3831598596352 :=
  @P1_7_1_3.block_append 6663 1432 2968 3224 256 256 512 1737599213696 2093999382656 3831598596352 cost_6663_1432_join0_12 cost_6663_1432_join0_14 rfl rfl rfl

private theorem cost_6663_1432_join1_8 : P1_7_1_3.blockEstimate 6663 1432 3480 512 = 5064865267968 :=
  @P1_7_1_3.block_append 6663 1432 3480 3736 256 256 512 2402316050560 2662549217408 5064865267968 cost_6663_1432_join0_16 cost_6663_1432_join0_18 rfl rfl rfl

private theorem cost_6663_1432_join1_10 : P1_7_1_3.blockEstimate 6663 1432 3992 512 = 5913463931136 :=
  @P1_7_1_3.block_append 6663 1432 3992 4248 256 256 512 2874698883200 3038765047936 5913463931136 cost_6663_1432_join0_20 cost_6663_1432_join0_22 rfl rfl rfl

private theorem cost_6663_1432_join1_12 : P1_7_1_3.blockEstimate 6663 1432 4504 512 = 6377394585856 :=
  @P1_7_1_3.block_append 6663 1432 4504 4760 256 256 512 3154747711616 3222646874240 6377394585856 cost_6663_1432_join0_24 cost_6663_1432_join0_26 rfl rfl rfl

private theorem cost_6663_1432_join1_14 : P1_7_1_3.blockEstimate 6663 1432 5016 512 = 6456657232128 :=
  @P1_7_1_3.block_append 6663 1432 5016 5272 256 256 512 3242462535808 3214194696320 6456657232128 cost_6663_1432_join0_28 cost_6663_1432_join0_30 rfl rfl rfl

private theorem cost_6663_1432_join1_16 : P1_7_1_3.blockEstimate 6663 1432 5528 512 = 6151251869952 :=
  @P1_7_1_3.block_append 6663 1432 5528 5784 256 256 512 3137843355776 3013408514176 6151251869952 cost_6663_1432_join0_32 cost_6663_1432_join0_34 rfl rfl rfl

private theorem cost_6663_1432_join1_18 : P1_7_1_3.blockEstimate 6663 1432 6040 512 = 5461178499328 :=
  @P1_7_1_3.block_append 6663 1432 6040 6296 256 256 512 2840890171520 2620288327808 5461178499328 cost_6663_1432_join0_36 cost_6663_1432_join0_38 rfl rfl rfl

private theorem cost_6663_1432_join1_20 : P1_7_1_3.blockEstimate 6663 1432 6552 512 = 4409314959763 :=
  @P1_7_1_3.block_append 6663 1432 6552 6808 256 256 512 2352619650177 2056695309586 4409314959763 cost_6663_1432_join0_40 cost_6663_1432_join0_42 rfl rfl rfl

private theorem cost_6663_1432_join1_22 : P1_7_1_3.blockEstimate 6663 1432 7064 512 = 3207958096651 :=
  @P1_7_1_3.block_append 6663 1432 7064 7320 256 256 512 1754062564976 1453895531675 3207958096651 cost_6663_1432_join0_44 cost_6663_1432_join0_46 rfl rfl rfl

private theorem cost_6663_1432_join1_24 : P1_7_1_3.blockEstimate 6663 1432 7576 512 = 2057505791774 :=
  @P1_7_1_3.block_append 6663 1432 7576 7832 256 256 512 1164379897961 893125893813 2057505791774 cost_6663_1432_join0_48 cost_6663_1432_join0_50 rfl rfl rfl

private theorem cost_6663_1432_join1_26 : P1_7_1_3.blockEstimate 6663 1432 8088 512 = 1076320265307 :=
  @P1_7_1_3.block_append 6663 1432 8088 8344 256 256 512 645775493723 430544771584 1076320265307 cost_6663_1432_join0_52 cost_6663_1432_join0_54 rfl rfl rfl

private theorem cost_6663_1432_join1_28 : P1_7_1_3.blockEstimate 6663 1432 8600 512 = 376569902080 :=
  @P1_7_1_3.block_append 6663 1432 8600 8856 256 256 512 254600206848 121969695232 376569902080 cost_6663_1432_join0_56 cost_6663_1432_join0_58 rfl rfl rfl

private theorem cost_6663_1432_join1_30 : P1_7_1_3.blockEstimate 6663 1432 9112 415 = 38949857856 :=
  @P1_7_1_3.block_append 6663 1432 9112 9368 256 159 415 36679768576 2270089280 38949857856 cost_6663_1432_join0_60 cost_6663_1432_join0_62 rfl rfl rfl

private theorem cost_6663_1432_join2_0 : P1_7_1_3.blockEstimate 6663 1432 1432 1024 = 1058178643200 :=
  @P1_7_1_3.block_append 6663 1432 1432 1944 512 512 1024 141299800704 916878842496 1058178643200 cost_6663_1432_join1_0 cost_6663_1432_join1_2 rfl rfl rfl

private theorem cost_6663_1432_join2_2 : P1_7_1_3.blockEstimate 6663 1432 2456 1024 = 6107944155290 :=
  @P1_7_1_3.block_append 6663 1432 2456 2968 512 512 1024 2276345558938 3831598596352 6107944155290 cost_6663_1432_join1_4 cost_6663_1432_join1_6 rfl rfl rfl

private theorem cost_6663_1432_join2_4 : P1_7_1_3.blockEstimate 6663 1432 3480 1024 = 10978329199104 :=
  @P1_7_1_3.block_append 6663 1432 3480 3992 512 512 1024 5064865267968 5913463931136 10978329199104 cost_6663_1432_join1_8 cost_6663_1432_join1_10 rfl rfl rfl

private theorem cost_6663_1432_join2_6 : P1_7_1_3.blockEstimate 6663 1432 4504 1024 = 12834051817984 :=
  @P1_7_1_3.block_append 6663 1432 4504 5016 512 512 1024 6377394585856 6456657232128 12834051817984 cost_6663_1432_join1_12 cost_6663_1432_join1_14 rfl rfl rfl

private theorem cost_6663_1432_join2_8 : P1_7_1_3.blockEstimate 6663 1432 5528 1024 = 11612430369280 :=
  @P1_7_1_3.block_append 6663 1432 5528 6040 512 512 1024 6151251869952 5461178499328 11612430369280 cost_6663_1432_join1_16 cost_6663_1432_join1_18 rfl rfl rfl

private theorem cost_6663_1432_join2_10 : P1_7_1_3.blockEstimate 6663 1432 6552 1024 = 7617273056414 :=
  @P1_7_1_3.block_append 6663 1432 6552 7064 512 512 1024 4409314959763 3207958096651 7617273056414 cost_6663_1432_join1_20 cost_6663_1432_join1_22 rfl rfl rfl

private theorem cost_6663_1432_join2_12 : P1_7_1_3.blockEstimate 6663 1432 7576 1024 = 3133826057081 :=
  @P1_7_1_3.block_append 6663 1432 7576 8088 512 512 1024 2057505791774 1076320265307 3133826057081 cost_6663_1432_join1_24 cost_6663_1432_join1_26 rfl rfl rfl

private theorem cost_6663_1432_join2_14 : P1_7_1_3.blockEstimate 6663 1432 8600 927 = 415519759936 :=
  @P1_7_1_3.block_append 6663 1432 8600 9112 512 415 927 376569902080 38949857856 415519759936 cost_6663_1432_join1_28 cost_6663_1432_join1_30 rfl rfl rfl

private theorem cost_6663_1432_join3_0 : P1_7_1_3.blockEstimate 6663 1432 1432 2048 = 7166122798490 :=
  @P1_7_1_3.block_append 6663 1432 1432 2456 1024 1024 2048 1058178643200 6107944155290 7166122798490 cost_6663_1432_join2_0 cost_6663_1432_join2_2 rfl rfl rfl

private theorem cost_6663_1432_join3_2 : P1_7_1_3.blockEstimate 6663 1432 3480 2048 = 23812381017088 :=
  @P1_7_1_3.block_append 6663 1432 3480 4504 1024 1024 2048 10978329199104 12834051817984 23812381017088 cost_6663_1432_join2_4 cost_6663_1432_join2_6 rfl rfl rfl

private theorem cost_6663_1432_join3_4 : P1_7_1_3.blockEstimate 6663 1432 5528 2048 = 19229703425694 :=
  @P1_7_1_3.block_append 6663 1432 5528 6552 1024 1024 2048 11612430369280 7617273056414 19229703425694 cost_6663_1432_join2_8 cost_6663_1432_join2_10 rfl rfl rfl

private theorem cost_6663_1432_join3_6 : P1_7_1_3.blockEstimate 6663 1432 7576 1951 = 3549345817017 :=
  @P1_7_1_3.block_append 6663 1432 7576 8600 1024 927 1951 3133826057081 415519759936 3549345817017 cost_6663_1432_join2_12 cost_6663_1432_join2_14 rfl rfl rfl

private theorem cost_6663_1432_join4_0 : P1_7_1_3.blockEstimate 6663 1432 1432 4096 = 30978503815578 :=
  @P1_7_1_3.block_append 6663 1432 1432 3480 2048 2048 4096 7166122798490 23812381017088 30978503815578 cost_6663_1432_join3_0 cost_6663_1432_join3_2 rfl rfl rfl

private theorem cost_6663_1432_join4_2 : P1_7_1_3.blockEstimate 6663 1432 5528 3999 = 22779049242711 :=
  @P1_7_1_3.block_append 6663 1432 5528 7576 2048 1951 3999 19229703425694 3549345817017 22779049242711 cost_6663_1432_join3_4 cost_6663_1432_join3_6 rfl rfl rfl

private theorem cost_6663_1432_join5_0 : P1_7_1_3.blockEstimate 6663 1432 1432 8095 = 53757553058289 :=
  @P1_7_1_3.block_append 6663 1432 1432 5528 4096 3999 8095 30978503815578 22779049242711 53757553058289 cost_6663_1432_join4_0 cost_6663_1432_join4_2 rfl rfl rfl

private theorem cost_6663_1432_total : P1_7_1_3.momentEstimate 6663 1432 = 53757553058289 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 6663 + 1432 = 8095 by decide]
  exact cost_6663_1432_join5_0

theorem moment6663_1432 : P1_7_1.groupedPoleMoment 6663 1432 ≤ 53757553058289 :=
  (P1_7_1_3.grouped_bound 6663 1432).trans_eq cost_6663_1432_total
private theorem cost_6719_1427_block0 : P1_7_1_3.blockEstimate 6719 1427 1427 128 = 2369712800 := by decide +kernel

private theorem cost_6719_1427_block1 : P1_7_1_3.blockEstimate 6719 1427 1555 128 = 16097657504 := by decide +kernel

private theorem cost_6719_1427_block2 : P1_7_1_3.blockEstimate 6719 1427 1683 128 = 42705261216 := by decide +kernel

private theorem cost_6719_1427_block3 : P1_7_1_3.blockEstimate 6719 1427 1811 128 = 81387217568 := by decide +kernel

private theorem cost_6719_1427_block4 : P1_7_1_3.blockEstimate 6719 1427 1939 128 = 131338220192 := by decide +kernel

private theorem cost_6719_1427_block5 : P1_7_1_3.blockEstimate 6719 1427 2067 128 = 191752962720 := by decide +kernel

private theorem cost_6719_1427_block6 : P1_7_1_3.blockEstimate 6719 1427 2195 128 = 261826138784 := by decide +kernel

private theorem cost_6719_1427_block7 : P1_7_1_3.blockEstimate 6719 1427 2323 128 = 340752442016 := by decide +kernel

private theorem cost_6719_1427_block8 : P1_7_1_3.blockEstimate 6719 1427 2451 128 = 427726566048 := by decide +kernel

private theorem cost_6719_1427_block9 : P1_7_1_3.blockEstimate 6719 1427 2579 128 = 521943204512 := by decide +kernel

private theorem cost_6719_1427_block10 : P1_7_1_3.blockEstimate 6719 1427 2707 128 = 622597051040 := by decide +kernel

private theorem cost_6719_1427_block11 : P1_7_1_3.blockEstimate 6719 1427 2835 128 = 727758215199 := by decide +kernel

private theorem cost_6719_1427_block12 : P1_7_1_3.blockEstimate 6719 1427 2963 128 = 829771958400 := by decide +kernel

private theorem cost_6719_1427_block13 : P1_7_1_3.blockEstimate 6719 1427 3091 128 = 925802285184 := by decide +kernel

private theorem cost_6719_1427_block14 : P1_7_1_3.blockEstimate 6719 1427 3219 128 = 1015843145856 := by decide +kernel

private theorem cost_6719_1427_block15 : P1_7_1_3.blockEstimate 6719 1427 3347 128 = 1099894540416 := by decide +kernel

private theorem cost_6719_1427_block16 : P1_7_1_3.blockEstimate 6719 1427 3475 128 = 1177956468864 := by decide +kernel

private theorem cost_6719_1427_block17 : P1_7_1_3.blockEstimate 6719 1427 3603 128 = 1250028931200 := by decide +kernel

private theorem cost_6719_1427_block18 : P1_7_1_3.blockEstimate 6719 1427 3731 128 = 1316111927424 := by decide +kernel

private theorem cost_6719_1427_block19 : P1_7_1_3.blockEstimate 6719 1427 3859 128 = 1376205457536 := by decide +kernel

private theorem cost_6719_1427_block20 : P1_7_1_3.blockEstimate 6719 1427 3987 128 = 1430309521536 := by decide +kernel

private theorem cost_6719_1427_block21 : P1_7_1_3.blockEstimate 6719 1427 4115 128 = 1478424119424 := by decide +kernel

private theorem cost_6719_1427_block22 : P1_7_1_3.blockEstimate 6719 1427 4243 128 = 1520549251200 := by decide +kernel

private theorem cost_6719_1427_block23 : P1_7_1_3.blockEstimate 6719 1427 4371 128 = 1556684916864 := by decide +kernel

private theorem cost_6719_1427_block24 : P1_7_1_3.blockEstimate 6719 1427 4499 128 = 1586831116416 := by decide +kernel

private theorem cost_6719_1427_block25 : P1_7_1_3.blockEstimate 6719 1427 4627 128 = 1610987849856 := by decide +kernel

private theorem cost_6719_1427_block26 : P1_7_1_3.blockEstimate 6719 1427 4755 128 = 1629155117184 := by decide +kernel

private theorem cost_6719_1427_block27 : P1_7_1_3.blockEstimate 6719 1427 4883 128 = 1641332918400 := by decide +kernel

private theorem cost_6719_1427_block28 : P1_7_1_3.blockEstimate 6719 1427 5011 128 = 1647521253504 := by decide +kernel

private theorem cost_6719_1427_block29 : P1_7_1_3.blockEstimate 6719 1427 5139 128 = 1647720122496 := by decide +kernel

private theorem cost_6719_1427_block30 : P1_7_1_3.blockEstimate 6719 1427 5267 128 = 1641929525376 := by decide +kernel

private theorem cost_6719_1427_block31 : P1_7_1_3.blockEstimate 6719 1427 5395 128 = 1630149462144 := by decide +kernel

private theorem cost_6719_1427_block32 : P1_7_1_3.blockEstimate 6719 1427 5523 128 = 1612379932800 := by decide +kernel

private theorem cost_6719_1427_block33 : P1_7_1_3.blockEstimate 6719 1427 5651 128 = 1588620937344 := by decide +kernel

private theorem cost_6719_1427_block34 : P1_7_1_3.blockEstimate 6719 1427 5779 128 = 1558872475776 := by decide +kernel

private theorem cost_6719_1427_block35 : P1_7_1_3.blockEstimate 6719 1427 5907 128 = 1523134548096 := by decide +kernel

private theorem cost_6719_1427_block36 : P1_7_1_3.blockEstimate 6719 1427 6035 128 = 1481407154304 := by decide +kernel

private theorem cost_6719_1427_block37 : P1_7_1_3.blockEstimate 6719 1427 6163 128 = 1433690294400 := by decide +kernel

private theorem cost_6719_1427_block38 : P1_7_1_3.blockEstimate 6719 1427 6291 128 = 1379983968384 := by decide +kernel

private theorem cost_6719_1427_block39 : P1_7_1_3.blockEstimate 6719 1427 6419 128 = 1320288176256 := by decide +kernel

private theorem cost_6719_1427_block40 : P1_7_1_3.blockEstimate 6719 1427 6547 128 = 1254602918016 := by decide +kernel

private theorem cost_6719_1427_block41 : P1_7_1_3.blockEstimate 6719 1427 6675 128 = 1183127202466 := by decide +kernel

private theorem cost_6719_1427_block42 : P1_7_1_3.blockEstimate 6719 1427 6803 128 = 1108344329262 := by decide +kernel

private theorem cost_6719_1427_block43 : P1_7_1_3.blockEstimate 6719 1427 6931 128 = 1032284383697 := by decide +kernel

private theorem cost_6719_1427_block44 : P1_7_1_3.blockEstimate 6719 1427 7059 128 = 955547524148 := by decide +kernel

private theorem cost_6719_1427_block45 : P1_7_1_3.blockEstimate 6719 1427 7187 128 = 878689726215 := by decide +kernel

private theorem cost_6719_1427_block46 : P1_7_1_3.blockEstimate 6719 1427 7315 128 = 802248917800 := by decide +kernel

private theorem cost_6719_1427_block47 : P1_7_1_3.blockEstimate 6719 1427 7443 128 = 726744981301 := by decide +kernel

private theorem cost_6719_1427_block48 : P1_7_1_3.blockEstimate 6719 1427 7571 128 = 652679752797 := by decide +kernel

private theorem cost_6719_1427_block49 : P1_7_1_3.blockEstimate 6719 1427 7699 128 = 580537021906 := by decide +kernel

private theorem cost_6719_1427_block50 : P1_7_1_3.blockEstimate 6719 1427 7827 128 = 510782533250 := by decide +kernel

private theorem cost_6719_1427_block51 : P1_7_1_3.blockEstimate 6719 1427 7955 128 = 443863984435 := by decide +kernel

private theorem cost_6719_1427_block52 : P1_7_1_3.blockEstimate 6719 1427 8083 128 = 380086092435 := by decide +kernel

private theorem cost_6719_1427_block53 : P1_7_1_3.blockEstimate 6719 1427 8211 128 = 319456087760 := by decide +kernel

private theorem cost_6719_1427_block54 : P1_7_1_3.blockEstimate 6719 1427 8339 128 = 263181906640 := by decide +kernel

private theorem cost_6719_1427_block55 : P1_7_1_3.blockEstimate 6719 1427 8467 128 = 211651286736 := by decide +kernel

private theorem cost_6719_1427_block56 : P1_7_1_3.blockEstimate 6719 1427 8595 128 = 165115886288 := by decide +kernel

private theorem cost_6719_1427_block57 : P1_7_1_3.blockEstimate 6719 1427 8723 128 = 123827363536 := by decide +kernel

private theorem cost_6719_1427_block58 : P1_7_1_3.blockEstimate 6719 1427 8851 128 = 88037376720 := by decide +kernel

private theorem cost_6719_1427_block59 : P1_7_1_3.blockEstimate 6719 1427 8979 128 = 57997584080 := by decide +kernel

private theorem cost_6719_1427_block60 : P1_7_1_3.blockEstimate 6719 1427 9107 128 = 33959643856 := by decide +kernel

private theorem cost_6719_1427_block61 : P1_7_1_3.blockEstimate 6719 1427 9235 128 = 16175214288 := by decide +kernel

private theorem cost_6719_1427_block62 : P1_7_1_3.blockEstimate 6719 1427 9363 128 = 4895953616 := by decide +kernel

private theorem cost_6719_1427_block63 : P1_7_1_3.blockEstimate 6719 1427 9491 82 = 324059526 := by decide +kernel

private theorem cost_6719_1427_join0_0 : P1_7_1_3.blockEstimate 6719 1427 1427 256 = 18467370304 :=
  @P1_7_1_3.block_append 6719 1427 1427 1555 128 128 256 2369712800 16097657504 18467370304 cost_6719_1427_block0 cost_6719_1427_block1 rfl rfl rfl

private theorem cost_6719_1427_join0_2 : P1_7_1_3.blockEstimate 6719 1427 1683 256 = 124092478784 :=
  @P1_7_1_3.block_append 6719 1427 1683 1811 128 128 256 42705261216 81387217568 124092478784 cost_6719_1427_block2 cost_6719_1427_block3 rfl rfl rfl

private theorem cost_6719_1427_join0_4 : P1_7_1_3.blockEstimate 6719 1427 1939 256 = 323091182912 :=
  @P1_7_1_3.block_append 6719 1427 1939 2067 128 128 256 131338220192 191752962720 323091182912 cost_6719_1427_block4 cost_6719_1427_block5 rfl rfl rfl

private theorem cost_6719_1427_join0_6 : P1_7_1_3.blockEstimate 6719 1427 2195 256 = 602578580800 :=
  @P1_7_1_3.block_append 6719 1427 2195 2323 128 128 256 261826138784 340752442016 602578580800 cost_6719_1427_block6 cost_6719_1427_block7 rfl rfl rfl

private theorem cost_6719_1427_join0_8 : P1_7_1_3.blockEstimate 6719 1427 2451 256 = 949669770560 :=
  @P1_7_1_3.block_append 6719 1427 2451 2579 128 128 256 427726566048 521943204512 949669770560 cost_6719_1427_block8 cost_6719_1427_block9 rfl rfl rfl

private theorem cost_6719_1427_join0_10 : P1_7_1_3.blockEstimate 6719 1427 2707 256 = 1350355266239 :=
  @P1_7_1_3.block_append 6719 1427 2707 2835 128 128 256 622597051040 727758215199 1350355266239 cost_6719_1427_block10 cost_6719_1427_block11 rfl rfl rfl

private theorem cost_6719_1427_join0_12 : P1_7_1_3.blockEstimate 6719 1427 2963 256 = 1755574243584 :=
  @P1_7_1_3.block_append 6719 1427 2963 3091 128 128 256 829771958400 925802285184 1755574243584 cost_6719_1427_block12 cost_6719_1427_block13 rfl rfl rfl

private theorem cost_6719_1427_join0_14 : P1_7_1_3.blockEstimate 6719 1427 3219 256 = 2115737686272 :=
  @P1_7_1_3.block_append 6719 1427 3219 3347 128 128 256 1015843145856 1099894540416 2115737686272 cost_6719_1427_block14 cost_6719_1427_block15 rfl rfl rfl

private theorem cost_6719_1427_join0_16 : P1_7_1_3.blockEstimate 6719 1427 3475 256 = 2427985400064 :=
  @P1_7_1_3.block_append 6719 1427 3475 3603 128 128 256 1177956468864 1250028931200 2427985400064 cost_6719_1427_block16 cost_6719_1427_block17 rfl rfl rfl

private theorem cost_6719_1427_join0_18 : P1_7_1_3.blockEstimate 6719 1427 3731 256 = 2692317384960 :=
  @P1_7_1_3.block_append 6719 1427 3731 3859 128 128 256 1316111927424 1376205457536 2692317384960 cost_6719_1427_block18 cost_6719_1427_block19 rfl rfl rfl

private theorem cost_6719_1427_join0_20 : P1_7_1_3.blockEstimate 6719 1427 3987 256 = 2908733640960 :=
  @P1_7_1_3.block_append 6719 1427 3987 4115 128 128 256 1430309521536 1478424119424 2908733640960 cost_6719_1427_block20 cost_6719_1427_block21 rfl rfl rfl

private theorem cost_6719_1427_join0_22 : P1_7_1_3.blockEstimate 6719 1427 4243 256 = 3077234168064 :=
  @P1_7_1_3.block_append 6719 1427 4243 4371 128 128 256 1520549251200 1556684916864 3077234168064 cost_6719_1427_block22 cost_6719_1427_block23 rfl rfl rfl

private theorem cost_6719_1427_join0_24 : P1_7_1_3.blockEstimate 6719 1427 4499 256 = 3197818966272 :=
  @P1_7_1_3.block_append 6719 1427 4499 4627 128 128 256 1586831116416 1610987849856 3197818966272 cost_6719_1427_block24 cost_6719_1427_block25 rfl rfl rfl

private theorem cost_6719_1427_join0_26 : P1_7_1_3.blockEstimate 6719 1427 4755 256 = 3270488035584 :=
  @P1_7_1_3.block_append 6719 1427 4755 4883 128 128 256 1629155117184 1641332918400 3270488035584 cost_6719_1427_block26 cost_6719_1427_block27 rfl rfl rfl

private theorem cost_6719_1427_join0_28 : P1_7_1_3.blockEstimate 6719 1427 5011 256 = 3295241376000 :=
  @P1_7_1_3.block_append 6719 1427 5011 5139 128 128 256 1647521253504 1647720122496 3295241376000 cost_6719_1427_block28 cost_6719_1427_block29 rfl rfl rfl

private theorem cost_6719_1427_join0_30 : P1_7_1_3.blockEstimate 6719 1427 5267 256 = 3272078987520 :=
  @P1_7_1_3.block_append 6719 1427 5267 5395 128 128 256 1641929525376 1630149462144 3272078987520 cost_6719_1427_block30 cost_6719_1427_block31 rfl rfl rfl

private theorem cost_6719_1427_join0_32 : P1_7_1_3.blockEstimate 6719 1427 5523 256 = 3201000870144 :=
  @P1_7_1_3.block_append 6719 1427 5523 5651 128 128 256 1612379932800 1588620937344 3201000870144 cost_6719_1427_block32 cost_6719_1427_block33 rfl rfl rfl

private theorem cost_6719_1427_join0_34 : P1_7_1_3.blockEstimate 6719 1427 5779 256 = 3082007023872 :=
  @P1_7_1_3.block_append 6719 1427 5779 5907 128 128 256 1558872475776 1523134548096 3082007023872 cost_6719_1427_block34 cost_6719_1427_block35 rfl rfl rfl

private theorem cost_6719_1427_join0_36 : P1_7_1_3.blockEstimate 6719 1427 6035 256 = 2915097448704 :=
  @P1_7_1_3.block_append 6719 1427 6035 6163 128 128 256 1481407154304 1433690294400 2915097448704 cost_6719_1427_block36 cost_6719_1427_block37 rfl rfl rfl

private theorem cost_6719_1427_join0_38 : P1_7_1_3.blockEstimate 6719 1427 6291 256 = 2700272144640 :=
  @P1_7_1_3.block_append 6719 1427 6291 6419 128 128 256 1379983968384 1320288176256 2700272144640 cost_6719_1427_block38 cost_6719_1427_block39 rfl rfl rfl

private theorem cost_6719_1427_join0_40 : P1_7_1_3.blockEstimate 6719 1427 6547 256 = 2437730120482 :=
  @P1_7_1_3.block_append 6719 1427 6547 6675 128 128 256 1254602918016 1183127202466 2437730120482 cost_6719_1427_block40 cost_6719_1427_block41 rfl rfl rfl

private theorem cost_6719_1427_join0_42 : P1_7_1_3.blockEstimate 6719 1427 6803 256 = 2140628712959 :=
  @P1_7_1_3.block_append 6719 1427 6803 6931 128 128 256 1108344329262 1032284383697 2140628712959 cost_6719_1427_block42 cost_6719_1427_block43 rfl rfl rfl

private theorem cost_6719_1427_join0_44 : P1_7_1_3.blockEstimate 6719 1427 7059 256 = 1834237250363 :=
  @P1_7_1_3.block_append 6719 1427 7059 7187 128 128 256 955547524148 878689726215 1834237250363 cost_6719_1427_block44 cost_6719_1427_block45 rfl rfl rfl

private theorem cost_6719_1427_join0_46 : P1_7_1_3.blockEstimate 6719 1427 7315 256 = 1528993899101 :=
  @P1_7_1_3.block_append 6719 1427 7315 7443 128 128 256 802248917800 726744981301 1528993899101 cost_6719_1427_block46 cost_6719_1427_block47 rfl rfl rfl

private theorem cost_6719_1427_join0_48 : P1_7_1_3.blockEstimate 6719 1427 7571 256 = 1233216774703 :=
  @P1_7_1_3.block_append 6719 1427 7571 7699 128 128 256 652679752797 580537021906 1233216774703 cost_6719_1427_block48 cost_6719_1427_block49 rfl rfl rfl

private theorem cost_6719_1427_join0_50 : P1_7_1_3.blockEstimate 6719 1427 7827 256 = 954646517685 :=
  @P1_7_1_3.block_append 6719 1427 7827 7955 128 128 256 510782533250 443863984435 954646517685 cost_6719_1427_block50 cost_6719_1427_block51 rfl rfl rfl

private theorem cost_6719_1427_join0_52 : P1_7_1_3.blockEstimate 6719 1427 8083 256 = 699542180195 :=
  @P1_7_1_3.block_append 6719 1427 8083 8211 128 128 256 380086092435 319456087760 699542180195 cost_6719_1427_block52 cost_6719_1427_block53 rfl rfl rfl

private theorem cost_6719_1427_join0_54 : P1_7_1_3.blockEstimate 6719 1427 8339 256 = 474833193376 :=
  @P1_7_1_3.block_append 6719 1427 8339 8467 128 128 256 263181906640 211651286736 474833193376 cost_6719_1427_block54 cost_6719_1427_block55 rfl rfl rfl

private theorem cost_6719_1427_join0_56 : P1_7_1_3.blockEstimate 6719 1427 8595 256 = 288943249824 :=
  @P1_7_1_3.block_append 6719 1427 8595 8723 128 128 256 165115886288 123827363536 288943249824 cost_6719_1427_block56 cost_6719_1427_block57 rfl rfl rfl

private theorem cost_6719_1427_join0_58 : P1_7_1_3.blockEstimate 6719 1427 8851 256 = 146034960800 :=
  @P1_7_1_3.block_append 6719 1427 8851 8979 128 128 256 88037376720 57997584080 146034960800 cost_6719_1427_block58 cost_6719_1427_block59 rfl rfl rfl

private theorem cost_6719_1427_join0_60 : P1_7_1_3.blockEstimate 6719 1427 9107 256 = 50134858144 :=
  @P1_7_1_3.block_append 6719 1427 9107 9235 128 128 256 33959643856 16175214288 50134858144 cost_6719_1427_block60 cost_6719_1427_block61 rfl rfl rfl

private theorem cost_6719_1427_join0_62 : P1_7_1_3.blockEstimate 6719 1427 9363 210 = 5220013142 :=
  @P1_7_1_3.block_append 6719 1427 9363 9491 128 82 210 4895953616 324059526 5220013142 cost_6719_1427_block62 cost_6719_1427_block63 rfl rfl rfl

private theorem cost_6719_1427_join1_0 : P1_7_1_3.blockEstimate 6719 1427 1427 512 = 142559849088 :=
  @P1_7_1_3.block_append 6719 1427 1427 1683 256 256 512 18467370304 124092478784 142559849088 cost_6719_1427_join0_0 cost_6719_1427_join0_2 rfl rfl rfl

private theorem cost_6719_1427_join1_2 : P1_7_1_3.blockEstimate 6719 1427 1939 512 = 925669763712 :=
  @P1_7_1_3.block_append 6719 1427 1939 2195 256 256 512 323091182912 602578580800 925669763712 cost_6719_1427_join0_4 cost_6719_1427_join0_6 rfl rfl rfl

private theorem cost_6719_1427_join1_4 : P1_7_1_3.blockEstimate 6719 1427 2451 512 = 2300025036799 :=
  @P1_7_1_3.block_append 6719 1427 2451 2707 256 256 512 949669770560 1350355266239 2300025036799 cost_6719_1427_join0_8 cost_6719_1427_join0_10 rfl rfl rfl

private theorem cost_6719_1427_join1_6 : P1_7_1_3.blockEstimate 6719 1427 2963 512 = 3871311929856 :=
  @P1_7_1_3.block_append 6719 1427 2963 3219 256 256 512 1755574243584 2115737686272 3871311929856 cost_6719_1427_join0_12 cost_6719_1427_join0_14 rfl rfl rfl

private theorem cost_6719_1427_join1_8 : P1_7_1_3.blockEstimate 6719 1427 3475 512 = 5120302785024 :=
  @P1_7_1_3.block_append 6719 1427 3475 3731 256 256 512 2427985400064 2692317384960 5120302785024 cost_6719_1427_join0_16 cost_6719_1427_join0_18 rfl rfl rfl

private theorem cost_6719_1427_join1_10 : P1_7_1_3.blockEstimate 6719 1427 3987 512 = 5985967809024 :=
  @P1_7_1_3.block_append 6719 1427 3987 4243 256 256 512 2908733640960 3077234168064 5985967809024 cost_6719_1427_join0_20 cost_6719_1427_join0_22 rfl rfl rfl

private theorem cost_6719_1427_join1_12 : P1_7_1_3.blockEstimate 6719 1427 4499 512 = 6468307001856 :=
  @P1_7_1_3.block_append 6719 1427 4499 4755 256 256 512 3197818966272 3270488035584 6468307001856 cost_6719_1427_join0_24 cost_6719_1427_join0_26 rfl rfl rfl

private theorem cost_6719_1427_join1_14 : P1_7_1_3.blockEstimate 6719 1427 5011 512 = 6567320363520 :=
  @P1_7_1_3.block_append 6719 1427 5011 5267 256 256 512 3295241376000 3272078987520 6567320363520 cost_6719_1427_join0_28 cost_6719_1427_join0_30 rfl rfl rfl

private theorem cost_6719_1427_join1_16 : P1_7_1_3.blockEstimate 6719 1427 5523 512 = 6283007894016 :=
  @P1_7_1_3.block_append 6719 1427 5523 5779 256 256 512 3201000870144 3082007023872 6283007894016 cost_6719_1427_join0_32 cost_6719_1427_join0_34 rfl rfl rfl

private theorem cost_6719_1427_join1_18 : P1_7_1_3.blockEstimate 6719 1427 6035 512 = 5615369593344 :=
  @P1_7_1_3.block_append 6719 1427 6035 6291 256 256 512 2915097448704 2700272144640 5615369593344 cost_6719_1427_join0_36 cost_6719_1427_join0_38 rfl rfl rfl

private theorem cost_6719_1427_join1_20 : P1_7_1_3.blockEstimate 6719 1427 6547 512 = 4578358833441 :=
  @P1_7_1_3.block_append 6719 1427 6547 6803 256 256 512 2437730120482 2140628712959 4578358833441 cost_6719_1427_join0_40 cost_6719_1427_join0_42 rfl rfl rfl

private theorem cost_6719_1427_join1_22 : P1_7_1_3.blockEstimate 6719 1427 7059 512 = 3363231149464 :=
  @P1_7_1_3.block_append 6719 1427 7059 7315 256 256 512 1834237250363 1528993899101 3363231149464 cost_6719_1427_join0_44 cost_6719_1427_join0_46 rfl rfl rfl

private theorem cost_6719_1427_join1_24 : P1_7_1_3.blockEstimate 6719 1427 7571 512 = 2187863292388 :=
  @P1_7_1_3.block_append 6719 1427 7571 7827 256 256 512 1233216774703 954646517685 2187863292388 cost_6719_1427_join0_48 cost_6719_1427_join0_50 rfl rfl rfl

private theorem cost_6719_1427_join1_26 : P1_7_1_3.blockEstimate 6719 1427 8083 512 = 1174375373571 :=
  @P1_7_1_3.block_append 6719 1427 8083 8339 256 256 512 699542180195 474833193376 1174375373571 cost_6719_1427_join0_52 cost_6719_1427_join0_54 rfl rfl rfl

private theorem cost_6719_1427_join1_28 : P1_7_1_3.blockEstimate 6719 1427 8595 512 = 434978210624 :=
  @P1_7_1_3.block_append 6719 1427 8595 8851 256 256 512 288943249824 146034960800 434978210624 cost_6719_1427_join0_56 cost_6719_1427_join0_58 rfl rfl rfl

private theorem cost_6719_1427_join1_30 : P1_7_1_3.blockEstimate 6719 1427 9107 466 = 55354871286 :=
  @P1_7_1_3.block_append 6719 1427 9107 9363 256 210 466 50134858144 5220013142 55354871286 cost_6719_1427_join0_60 cost_6719_1427_join0_62 rfl rfl rfl

private theorem cost_6719_1427_join2_0 : P1_7_1_3.blockEstimate 6719 1427 1427 1024 = 1068229612800 :=
  @P1_7_1_3.block_append 6719 1427 1427 1939 512 512 1024 142559849088 925669763712 1068229612800 cost_6719_1427_join1_0 cost_6719_1427_join1_2 rfl rfl rfl

private theorem cost_6719_1427_join2_2 : P1_7_1_3.blockEstimate 6719 1427 2451 1024 = 6171336966655 :=
  @P1_7_1_3.block_append 6719 1427 2451 2963 512 512 1024 2300025036799 3871311929856 6171336966655 cost_6719_1427_join1_4 cost_6719_1427_join1_6 rfl rfl rfl

private theorem cost_6719_1427_join2_4 : P1_7_1_3.blockEstimate 6719 1427 3475 1024 = 11106270594048 :=
  @P1_7_1_3.block_append 6719 1427 3475 3987 512 512 1024 5120302785024 5985967809024 11106270594048 cost_6719_1427_join1_8 cost_6719_1427_join1_10 rfl rfl rfl

private theorem cost_6719_1427_join2_6 : P1_7_1_3.blockEstimate 6719 1427 4499 1024 = 13035627365376 :=
  @P1_7_1_3.block_append 6719 1427 4499 5011 512 512 1024 6468307001856 6567320363520 13035627365376 cost_6719_1427_join1_12 cost_6719_1427_join1_14 rfl rfl rfl

private theorem cost_6719_1427_join2_8 : P1_7_1_3.blockEstimate 6719 1427 5523 1024 = 11898377487360 :=
  @P1_7_1_3.block_append 6719 1427 5523 6035 512 512 1024 6283007894016 5615369593344 11898377487360 cost_6719_1427_join1_16 cost_6719_1427_join1_18 rfl rfl rfl

private theorem cost_6719_1427_join2_10 : P1_7_1_3.blockEstimate 6719 1427 6547 1024 = 7941589982905 :=
  @P1_7_1_3.block_append 6719 1427 6547 7059 512 512 1024 4578358833441 3363231149464 7941589982905 cost_6719_1427_join1_20 cost_6719_1427_join1_22 rfl rfl rfl

private theorem cost_6719_1427_join2_12 : P1_7_1_3.blockEstimate 6719 1427 7571 1024 = 3362238665959 :=
  @P1_7_1_3.block_append 6719 1427 7571 8083 512 512 1024 2187863292388 1174375373571 3362238665959 cost_6719_1427_join1_24 cost_6719_1427_join1_26 rfl rfl rfl

private theorem cost_6719_1427_join2_14 : P1_7_1_3.blockEstimate 6719 1427 8595 978 = 490333081910 :=
  @P1_7_1_3.block_append 6719 1427 8595 9107 512 466 978 434978210624 55354871286 490333081910 cost_6719_1427_join1_28 cost_6719_1427_join1_30 rfl rfl rfl

private theorem cost_6719_1427_join3_0 : P1_7_1_3.blockEstimate 6719 1427 1427 2048 = 7239566579455 :=
  @P1_7_1_3.block_append 6719 1427 1427 2451 1024 1024 2048 1068229612800 6171336966655 7239566579455 cost_6719_1427_join2_0 cost_6719_1427_join2_2 rfl rfl rfl

private theorem cost_6719_1427_join3_2 : P1_7_1_3.blockEstimate 6719 1427 3475 2048 = 24141897959424 :=
  @P1_7_1_3.block_append 6719 1427 3475 4499 1024 1024 2048 11106270594048 13035627365376 24141897959424 cost_6719_1427_join2_4 cost_6719_1427_join2_6 rfl rfl rfl

private theorem cost_6719_1427_join3_4 : P1_7_1_3.blockEstimate 6719 1427 5523 2048 = 19839967470265 :=
  @P1_7_1_3.block_append 6719 1427 5523 6547 1024 1024 2048 11898377487360 7941589982905 19839967470265 cost_6719_1427_join2_8 cost_6719_1427_join2_10 rfl rfl rfl

private theorem cost_6719_1427_join3_6 : P1_7_1_3.blockEstimate 6719 1427 7571 2002 = 3852571747869 :=
  @P1_7_1_3.block_append 6719 1427 7571 8595 1024 978 2002 3362238665959 490333081910 3852571747869 cost_6719_1427_join2_12 cost_6719_1427_join2_14 rfl rfl rfl

private theorem cost_6719_1427_join4_0 : P1_7_1_3.blockEstimate 6719 1427 1427 4096 = 31381464538879 :=
  @P1_7_1_3.block_append 6719 1427 1427 3475 2048 2048 4096 7239566579455 24141897959424 31381464538879 cost_6719_1427_join3_0 cost_6719_1427_join3_2 rfl rfl rfl

private theorem cost_6719_1427_join4_2 : P1_7_1_3.blockEstimate 6719 1427 5523 4050 = 23692539218134 :=
  @P1_7_1_3.block_append 6719 1427 5523 7571 2048 2002 4050 19839967470265 3852571747869 23692539218134 cost_6719_1427_join3_4 cost_6719_1427_join3_6 rfl rfl rfl

private theorem cost_6719_1427_join5_0 : P1_7_1_3.blockEstimate 6719 1427 1427 8146 = 55074003757013 :=
  @P1_7_1_3.block_append 6719 1427 1427 5523 4096 4050 8146 31381464538879 23692539218134 55074003757013 cost_6719_1427_join4_0 cost_6719_1427_join4_2 rfl rfl rfl

private theorem cost_6719_1427_total : P1_7_1_3.momentEstimate 6719 1427 = 55074003757013 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 6719 + 1427 = 8146 by decide]
  exact cost_6719_1427_join5_0

theorem moment6719_1427 : P1_7_1.groupedPoleMoment 6719 1427 ≤ 55074003757013 :=
  (P1_7_1_3.grouped_bound 6719 1427).trans_eq cost_6719_1427_total
private theorem cost_6719_1456_block0 : P1_7_1_3.blockEstimate 6719 1456 1456 128 = 2369712800 := by decide +kernel

private theorem cost_6719_1456_block1 : P1_7_1_3.blockEstimate 6719 1456 1584 128 = 16097657504 := by decide +kernel

private theorem cost_6719_1456_block2 : P1_7_1_3.blockEstimate 6719 1456 1712 128 = 42705261216 := by decide +kernel

private theorem cost_6719_1456_block3 : P1_7_1_3.blockEstimate 6719 1456 1840 128 = 81387217568 := by decide +kernel

private theorem cost_6719_1456_block4 : P1_7_1_3.blockEstimate 6719 1456 1968 128 = 131338220192 := by decide +kernel

private theorem cost_6719_1456_block5 : P1_7_1_3.blockEstimate 6719 1456 2096 128 = 191752962720 := by decide +kernel

private theorem cost_6719_1456_block6 : P1_7_1_3.blockEstimate 6719 1456 2224 128 = 261826138784 := by decide +kernel

private theorem cost_6719_1456_block7 : P1_7_1_3.blockEstimate 6719 1456 2352 128 = 340752442016 := by decide +kernel

private theorem cost_6719_1456_block8 : P1_7_1_3.blockEstimate 6719 1456 2480 128 = 427726566048 := by decide +kernel

private theorem cost_6719_1456_block9 : P1_7_1_3.blockEstimate 6719 1456 2608 128 = 521943204512 := by decide +kernel

private theorem cost_6719_1456_block10 : P1_7_1_3.blockEstimate 6719 1456 2736 128 = 622597051040 := by decide +kernel

private theorem cost_6719_1456_block11 : P1_7_1_3.blockEstimate 6719 1456 2864 128 = 728438836644 := by decide +kernel

private theorem cost_6719_1456_block12 : P1_7_1_3.blockEstimate 6719 1456 2992 128 = 832778958656 := by decide +kernel

private theorem cost_6719_1456_block13 : P1_7_1_3.blockEstimate 6719 1456 3120 128 = 931105617728 := by decide +kernel

private theorem cost_6719_1456_block14 : P1_7_1_3.blockEstimate 6719 1456 3248 128 = 1023321175872 := by decide +kernel

private theorem cost_6719_1456_block15 : P1_7_1_3.blockEstimate 6719 1456 3376 128 = 1109425633088 := by decide +kernel

private theorem cost_6719_1456_block16 : P1_7_1_3.blockEstimate 6719 1456 3504 128 = 1189418989376 := by decide +kernel

private theorem cost_6719_1456_block17 : P1_7_1_3.blockEstimate 6719 1456 3632 128 = 1263301244736 := by decide +kernel

private theorem cost_6719_1456_block18 : P1_7_1_3.blockEstimate 6719 1456 3760 128 = 1331072399168 := by decide +kernel

private theorem cost_6719_1456_block19 : P1_7_1_3.blockEstimate 6719 1456 3888 128 = 1392732452672 := by decide +kernel

private theorem cost_6719_1456_block20 : P1_7_1_3.blockEstimate 6719 1456 4016 128 = 1448281405248 := by decide +kernel

private theorem cost_6719_1456_block21 : P1_7_1_3.blockEstimate 6719 1456 4144 128 = 1497719256896 := by decide +kernel

private theorem cost_6719_1456_block22 : P1_7_1_3.blockEstimate 6719 1456 4272 128 = 1541046007616 := by decide +kernel

private theorem cost_6719_1456_block23 : P1_7_1_3.blockEstimate 6719 1456 4400 128 = 1578261657408 := by decide +kernel

private theorem cost_6719_1456_block24 : P1_7_1_3.blockEstimate 6719 1456 4528 128 = 1609366206272 := by decide +kernel

private theorem cost_6719_1456_block25 : P1_7_1_3.blockEstimate 6719 1456 4656 128 = 1634359654208 := by decide +kernel

private theorem cost_6719_1456_block26 : P1_7_1_3.blockEstimate 6719 1456 4784 128 = 1653242001216 := by decide +kernel

private theorem cost_6719_1456_block27 : P1_7_1_3.blockEstimate 6719 1456 4912 128 = 1666013247296 := by decide +kernel

private theorem cost_6719_1456_block28 : P1_7_1_3.blockEstimate 6719 1456 5040 128 = 1672673392448 := by decide +kernel

private theorem cost_6719_1456_block29 : P1_7_1_3.blockEstimate 6719 1456 5168 128 = 1673222436672 := by decide +kernel

private theorem cost_6719_1456_block30 : P1_7_1_3.blockEstimate 6719 1456 5296 128 = 1667660379968 := by decide +kernel

private theorem cost_6719_1456_block31 : P1_7_1_3.blockEstimate 6719 1456 5424 128 = 1655987222336 := by decide +kernel

private theorem cost_6719_1456_block32 : P1_7_1_3.blockEstimate 6719 1456 5552 128 = 1638202963776 := by decide +kernel

private theorem cost_6719_1456_block33 : P1_7_1_3.blockEstimate 6719 1456 5680 128 = 1614307604288 := by decide +kernel

private theorem cost_6719_1456_block34 : P1_7_1_3.blockEstimate 6719 1456 5808 128 = 1584301143872 := by decide +kernel

private theorem cost_6719_1456_block35 : P1_7_1_3.blockEstimate 6719 1456 5936 128 = 1548183582528 := by decide +kernel

private theorem cost_6719_1456_block36 : P1_7_1_3.blockEstimate 6719 1456 6064 128 = 1505954920256 := by decide +kernel

private theorem cost_6719_1456_block37 : P1_7_1_3.blockEstimate 6719 1456 6192 128 = 1457615157056 := by decide +kernel

private theorem cost_6719_1456_block38 : P1_7_1_3.blockEstimate 6719 1456 6320 128 = 1403164292928 := by decide +kernel

private theorem cost_6719_1456_block39 : P1_7_1_3.blockEstimate 6719 1456 6448 128 = 1342602327872 := by decide +kernel

private theorem cost_6719_1456_block40 : P1_7_1_3.blockEstimate 6719 1456 6576 128 = 1275929261888 := by decide +kernel

private theorem cost_6719_1456_block41 : P1_7_1_3.blockEstimate 6719 1456 6704 128 = 1203624297099 := by decide +kernel

private theorem cost_6719_1456_block42 : P1_7_1_3.blockEstimate 6719 1456 6832 128 = 1128553644040 := by decide +kernel

private theorem cost_6719_1456_block43 : P1_7_1_3.blockEstimate 6719 1456 6960 128 = 1052180677483 := by decide +kernel

private theorem cost_6719_1456_block44 : P1_7_1_3.blockEstimate 6719 1456 7088 128 = 975076957335 := by decide +kernel

private theorem cost_6719_1456_block45 : P1_7_1_3.blockEstimate 6719 1456 7216 128 = 897795406593 := by decide +kernel

private theorem cost_6719_1456_block46 : P1_7_1_3.blockEstimate 6719 1456 7344 128 = 820871261046 := by decide +kernel

private theorem cost_6719_1456_block47 : P1_7_1_3.blockEstimate 6719 1456 7472 128 = 744822069519 := by decide +kernel

private theorem cost_6719_1456_block48 : P1_7_1_3.blockEstimate 6719 1456 7600 128 = 670147693893 := by decide +kernel

private theorem cost_6719_1456_block49 : P1_7_1_3.blockEstimate 6719 1456 7728 128 = 597330310054 := by decide +kernel

private theorem cost_6719_1456_block50 : P1_7_1_3.blockEstimate 6719 1456 7856 128 = 526834405161 := by decide +kernel

private theorem cost_6719_1456_block51 : P1_7_1_3.blockEstimate 6719 1456 7984 128 = 459106781470 := by decide +kernel

private theorem cost_6719_1456_block52 : P1_7_1_3.blockEstimate 6719 1456 8112 128 = 394446255526 := by decide +kernel

private theorem cost_6719_1456_block53 : P1_7_1_3.blockEstimate 6719 1456 8240 128 = 332838856192 := by decide +kernel

private theorem cost_6719_1456_block54 : P1_7_1_3.blockEstimate 6719 1456 8368 128 = 275524929024 := by decide +kernel

private theorem cost_6719_1456_block55 : P1_7_1_3.blockEstimate 6719 1456 8496 128 = 222897546752 := by decide +kernel

private theorem cost_6719_1456_block56 : P1_7_1_3.blockEstimate 6719 1456 8624 128 = 175208367616 := by decide +kernel

private theorem cost_6719_1456_block57 : P1_7_1_3.blockEstimate 6719 1456 8752 128 = 132709049856 := by decide +kernel

private theorem cost_6719_1456_block58 : P1_7_1_3.blockEstimate 6719 1456 8880 128 = 95651251712 := by decide +kernel

private theorem cost_6719_1456_block59 : P1_7_1_3.blockEstimate 6719 1456 9008 128 = 64286631424 := by decide +kernel

private theorem cost_6719_1456_block60 : P1_7_1_3.blockEstimate 6719 1456 9136 128 = 38866847232 := by decide +kernel

private theorem cost_6719_1456_block61 : P1_7_1_3.blockEstimate 6719 1456 9264 128 = 19643557376 := by decide +kernel

private theorem cost_6719_1456_block62 : P1_7_1_3.blockEstimate 6719 1456 9392 128 = 6868420096 := by decide +kernel

private theorem cost_6719_1456_block63 : P1_7_1_3.blockEstimate 6719 1456 9520 111 = 791021504 := by decide +kernel

private theorem cost_6719_1456_join0_0 : P1_7_1_3.blockEstimate 6719 1456 1456 256 = 18467370304 :=
  @P1_7_1_3.block_append 6719 1456 1456 1584 128 128 256 2369712800 16097657504 18467370304 cost_6719_1456_block0 cost_6719_1456_block1 rfl rfl rfl

private theorem cost_6719_1456_join0_2 : P1_7_1_3.blockEstimate 6719 1456 1712 256 = 124092478784 :=
  @P1_7_1_3.block_append 6719 1456 1712 1840 128 128 256 42705261216 81387217568 124092478784 cost_6719_1456_block2 cost_6719_1456_block3 rfl rfl rfl

private theorem cost_6719_1456_join0_4 : P1_7_1_3.blockEstimate 6719 1456 1968 256 = 323091182912 :=
  @P1_7_1_3.block_append 6719 1456 1968 2096 128 128 256 131338220192 191752962720 323091182912 cost_6719_1456_block4 cost_6719_1456_block5 rfl rfl rfl

private theorem cost_6719_1456_join0_6 : P1_7_1_3.blockEstimate 6719 1456 2224 256 = 602578580800 :=
  @P1_7_1_3.block_append 6719 1456 2224 2352 128 128 256 261826138784 340752442016 602578580800 cost_6719_1456_block6 cost_6719_1456_block7 rfl rfl rfl

private theorem cost_6719_1456_join0_8 : P1_7_1_3.blockEstimate 6719 1456 2480 256 = 949669770560 :=
  @P1_7_1_3.block_append 6719 1456 2480 2608 128 128 256 427726566048 521943204512 949669770560 cost_6719_1456_block8 cost_6719_1456_block9 rfl rfl rfl

private theorem cost_6719_1456_join0_10 : P1_7_1_3.blockEstimate 6719 1456 2736 256 = 1351035887684 :=
  @P1_7_1_3.block_append 6719 1456 2736 2864 128 128 256 622597051040 728438836644 1351035887684 cost_6719_1456_block10 cost_6719_1456_block11 rfl rfl rfl

private theorem cost_6719_1456_join0_12 : P1_7_1_3.blockEstimate 6719 1456 2992 256 = 1763884576384 :=
  @P1_7_1_3.block_append 6719 1456 2992 3120 128 128 256 832778958656 931105617728 1763884576384 cost_6719_1456_block12 cost_6719_1456_block13 rfl rfl rfl

private theorem cost_6719_1456_join0_14 : P1_7_1_3.blockEstimate 6719 1456 3248 256 = 2132746808960 :=
  @P1_7_1_3.block_append 6719 1456 3248 3376 128 128 256 1023321175872 1109425633088 2132746808960 cost_6719_1456_block14 cost_6719_1456_block15 rfl rfl rfl

private theorem cost_6719_1456_join0_16 : P1_7_1_3.blockEstimate 6719 1456 3504 256 = 2452720234112 :=
  @P1_7_1_3.block_append 6719 1456 3504 3632 128 128 256 1189418989376 1263301244736 2452720234112 cost_6719_1456_block16 cost_6719_1456_block17 rfl rfl rfl

private theorem cost_6719_1456_join0_18 : P1_7_1_3.blockEstimate 6719 1456 3760 256 = 2723804851840 :=
  @P1_7_1_3.block_append 6719 1456 3760 3888 128 128 256 1331072399168 1392732452672 2723804851840 cost_6719_1456_block18 cost_6719_1456_block19 rfl rfl rfl

private theorem cost_6719_1456_join0_20 : P1_7_1_3.blockEstimate 6719 1456 4016 256 = 2946000662144 :=
  @P1_7_1_3.block_append 6719 1456 4016 4144 128 128 256 1448281405248 1497719256896 2946000662144 cost_6719_1456_block20 cost_6719_1456_block21 rfl rfl rfl

private theorem cost_6719_1456_join0_22 : P1_7_1_3.blockEstimate 6719 1456 4272 256 = 3119307665024 :=
  @P1_7_1_3.block_append 6719 1456 4272 4400 128 128 256 1541046007616 1578261657408 3119307665024 cost_6719_1456_block22 cost_6719_1456_block23 rfl rfl rfl

private theorem cost_6719_1456_join0_24 : P1_7_1_3.blockEstimate 6719 1456 4528 256 = 3243725860480 :=
  @P1_7_1_3.block_append 6719 1456 4528 4656 128 128 256 1609366206272 1634359654208 3243725860480 cost_6719_1456_block24 cost_6719_1456_block25 rfl rfl rfl

private theorem cost_6719_1456_join0_26 : P1_7_1_3.blockEstimate 6719 1456 4784 256 = 3319255248512 :=
  @P1_7_1_3.block_append 6719 1456 4784 4912 128 128 256 1653242001216 1666013247296 3319255248512 cost_6719_1456_block26 cost_6719_1456_block27 rfl rfl rfl

private theorem cost_6719_1456_join0_28 : P1_7_1_3.blockEstimate 6719 1456 5040 256 = 3345895829120 :=
  @P1_7_1_3.block_append 6719 1456 5040 5168 128 128 256 1672673392448 1673222436672 3345895829120 cost_6719_1456_block28 cost_6719_1456_block29 rfl rfl rfl

private theorem cost_6719_1456_join0_30 : P1_7_1_3.blockEstimate 6719 1456 5296 256 = 3323647602304 :=
  @P1_7_1_3.block_append 6719 1456 5296 5424 128 128 256 1667660379968 1655987222336 3323647602304 cost_6719_1456_block30 cost_6719_1456_block31 rfl rfl rfl

private theorem cost_6719_1456_join0_32 : P1_7_1_3.blockEstimate 6719 1456 5552 256 = 3252510568064 :=
  @P1_7_1_3.block_append 6719 1456 5552 5680 128 128 256 1638202963776 1614307604288 3252510568064 cost_6719_1456_block32 cost_6719_1456_block33 rfl rfl rfl

private theorem cost_6719_1456_join0_34 : P1_7_1_3.blockEstimate 6719 1456 5808 256 = 3132484726400 :=
  @P1_7_1_3.block_append 6719 1456 5808 5936 128 128 256 1584301143872 1548183582528 3132484726400 cost_6719_1456_block34 cost_6719_1456_block35 rfl rfl rfl

private theorem cost_6719_1456_join0_36 : P1_7_1_3.blockEstimate 6719 1456 6064 256 = 2963570077312 :=
  @P1_7_1_3.block_append 6719 1456 6064 6192 128 128 256 1505954920256 1457615157056 2963570077312 cost_6719_1456_block36 cost_6719_1456_block37 rfl rfl rfl

private theorem cost_6719_1456_join0_38 : P1_7_1_3.blockEstimate 6719 1456 6320 256 = 2745766620800 :=
  @P1_7_1_3.block_append 6719 1456 6320 6448 128 128 256 1403164292928 1342602327872 2745766620800 cost_6719_1456_block38 cost_6719_1456_block39 rfl rfl rfl

private theorem cost_6719_1456_join0_40 : P1_7_1_3.blockEstimate 6719 1456 6576 256 = 2479553558987 :=
  @P1_7_1_3.block_append 6719 1456 6576 6704 128 128 256 1275929261888 1203624297099 2479553558987 cost_6719_1456_block40 cost_6719_1456_block41 rfl rfl rfl

private theorem cost_6719_1456_join0_42 : P1_7_1_3.blockEstimate 6719 1456 6832 256 = 2180734321523 :=
  @P1_7_1_3.block_append 6719 1456 6832 6960 128 128 256 1128553644040 1052180677483 2180734321523 cost_6719_1456_block42 cost_6719_1456_block43 rfl rfl rfl

private theorem cost_6719_1456_join0_44 : P1_7_1_3.blockEstimate 6719 1456 7088 256 = 1872872363928 :=
  @P1_7_1_3.block_append 6719 1456 7088 7216 128 128 256 975076957335 897795406593 1872872363928 cost_6719_1456_block44 cost_6719_1456_block45 rfl rfl rfl

private theorem cost_6719_1456_join0_46 : P1_7_1_3.blockEstimate 6719 1456 7344 256 = 1565693330565 :=
  @P1_7_1_3.block_append 6719 1456 7344 7472 128 128 256 820871261046 744822069519 1565693330565 cost_6719_1456_block46 cost_6719_1456_block47 rfl rfl rfl

private theorem cost_6719_1456_join0_48 : P1_7_1_3.blockEstimate 6719 1456 7600 256 = 1267478003947 :=
  @P1_7_1_3.block_append 6719 1456 7600 7728 128 128 256 670147693893 597330310054 1267478003947 cost_6719_1456_block48 cost_6719_1456_block49 rfl rfl rfl

private theorem cost_6719_1456_join0_50 : P1_7_1_3.blockEstimate 6719 1456 7856 256 = 985941186631 :=
  @P1_7_1_3.block_append 6719 1456 7856 7984 128 128 256 526834405161 459106781470 985941186631 cost_6719_1456_block50 cost_6719_1456_block51 rfl rfl rfl

private theorem cost_6719_1456_join0_52 : P1_7_1_3.blockEstimate 6719 1456 8112 256 = 727285111718 :=
  @P1_7_1_3.block_append 6719 1456 8112 8240 128 128 256 394446255526 332838856192 727285111718 cost_6719_1456_block52 cost_6719_1456_block53 rfl rfl rfl

private theorem cost_6719_1456_join0_54 : P1_7_1_3.blockEstimate 6719 1456 8368 256 = 498422475776 :=
  @P1_7_1_3.block_append 6719 1456 8368 8496 128 128 256 275524929024 222897546752 498422475776 cost_6719_1456_block54 cost_6719_1456_block55 rfl rfl rfl

private theorem cost_6719_1456_join0_56 : P1_7_1_3.blockEstimate 6719 1456 8624 256 = 307917417472 :=
  @P1_7_1_3.block_append 6719 1456 8624 8752 128 128 256 175208367616 132709049856 307917417472 cost_6719_1456_block56 cost_6719_1456_block57 rfl rfl rfl

private theorem cost_6719_1456_join0_58 : P1_7_1_3.blockEstimate 6719 1456 8880 256 = 159937883136 :=
  @P1_7_1_3.block_append 6719 1456 8880 9008 128 128 256 95651251712 64286631424 159937883136 cost_6719_1456_block58 cost_6719_1456_block59 rfl rfl rfl

private theorem cost_6719_1456_join0_60 : P1_7_1_3.blockEstimate 6719 1456 9136 256 = 58510404608 :=
  @P1_7_1_3.block_append 6719 1456 9136 9264 128 128 256 38866847232 19643557376 58510404608 cost_6719_1456_block60 cost_6719_1456_block61 rfl rfl rfl

private theorem cost_6719_1456_join0_62 : P1_7_1_3.blockEstimate 6719 1456 9392 239 = 7659441600 :=
  @P1_7_1_3.block_append 6719 1456 9392 9520 128 111 239 6868420096 791021504 7659441600 cost_6719_1456_block62 cost_6719_1456_block63 rfl rfl rfl

private theorem cost_6719_1456_join1_0 : P1_7_1_3.blockEstimate 6719 1456 1456 512 = 142559849088 :=
  @P1_7_1_3.block_append 6719 1456 1456 1712 256 256 512 18467370304 124092478784 142559849088 cost_6719_1456_join0_0 cost_6719_1456_join0_2 rfl rfl rfl

private theorem cost_6719_1456_join1_2 : P1_7_1_3.blockEstimate 6719 1456 1968 512 = 925669763712 :=
  @P1_7_1_3.block_append 6719 1456 1968 2224 256 256 512 323091182912 602578580800 925669763712 cost_6719_1456_join0_4 cost_6719_1456_join0_6 rfl rfl rfl

private theorem cost_6719_1456_join1_4 : P1_7_1_3.blockEstimate 6719 1456 2480 512 = 2300705658244 :=
  @P1_7_1_3.block_append 6719 1456 2480 2736 256 256 512 949669770560 1351035887684 2300705658244 cost_6719_1456_join0_8 cost_6719_1456_join0_10 rfl rfl rfl

private theorem cost_6719_1456_join1_6 : P1_7_1_3.blockEstimate 6719 1456 2992 512 = 3896631385344 :=
  @P1_7_1_3.block_append 6719 1456 2992 3248 256 256 512 1763884576384 2132746808960 3896631385344 cost_6719_1456_join0_12 cost_6719_1456_join0_14 rfl rfl rfl

private theorem cost_6719_1456_join1_8 : P1_7_1_3.blockEstimate 6719 1456 3504 512 = 5176525085952 :=
  @P1_7_1_3.block_append 6719 1456 3504 3760 256 256 512 2452720234112 2723804851840 5176525085952 cost_6719_1456_join0_16 cost_6719_1456_join0_18 rfl rfl rfl

private theorem cost_6719_1456_join1_10 : P1_7_1_3.blockEstimate 6719 1456 4016 512 = 6065308327168 :=
  @P1_7_1_3.block_append 6719 1456 4016 4272 256 256 512 2946000662144 3119307665024 6065308327168 cost_6719_1456_join0_20 cost_6719_1456_join0_22 rfl rfl rfl

private theorem cost_6719_1456_join1_12 : P1_7_1_3.blockEstimate 6719 1456 4528 512 = 6562981108992 :=
  @P1_7_1_3.block_append 6719 1456 4528 4784 256 256 512 3243725860480 3319255248512 6562981108992 cost_6719_1456_join0_24 cost_6719_1456_join0_26 rfl rfl rfl

private theorem cost_6719_1456_join1_14 : P1_7_1_3.blockEstimate 6719 1456 5040 512 = 6669543431424 :=
  @P1_7_1_3.block_append 6719 1456 5040 5296 256 256 512 3345895829120 3323647602304 6669543431424 cost_6719_1456_join0_28 cost_6719_1456_join0_30 rfl rfl rfl

private theorem cost_6719_1456_join1_16 : P1_7_1_3.blockEstimate 6719 1456 5552 512 = 6384995294464 :=
  @P1_7_1_3.block_append 6719 1456 5552 5808 256 256 512 3252510568064 3132484726400 6384995294464 cost_6719_1456_join0_32 cost_6719_1456_join0_34 rfl rfl rfl

private theorem cost_6719_1456_join1_18 : P1_7_1_3.blockEstimate 6719 1456 6064 512 = 5709336698112 :=
  @P1_7_1_3.block_append 6719 1456 6064 6320 256 256 512 2963570077312 2745766620800 5709336698112 cost_6719_1456_join0_36 cost_6719_1456_join0_38 rfl rfl rfl

private theorem cost_6719_1456_join1_20 : P1_7_1_3.blockEstimate 6719 1456 6576 512 = 4660287880510 :=
  @P1_7_1_3.block_append 6719 1456 6576 6832 256 256 512 2479553558987 2180734321523 4660287880510 cost_6719_1456_join0_40 cost_6719_1456_join0_42 rfl rfl rfl

private theorem cost_6719_1456_join1_22 : P1_7_1_3.blockEstimate 6719 1456 7088 512 = 3438565694493 :=
  @P1_7_1_3.block_append 6719 1456 7088 7344 256 256 512 1872872363928 1565693330565 3438565694493 cost_6719_1456_join0_44 cost_6719_1456_join0_46 rfl rfl rfl

private theorem cost_6719_1456_join1_24 : P1_7_1_3.blockEstimate 6719 1456 7600 512 = 2253419190578 :=
  @P1_7_1_3.block_append 6719 1456 7600 7856 256 256 512 1267478003947 985941186631 2253419190578 cost_6719_1456_join0_48 cost_6719_1456_join0_50 rfl rfl rfl

private theorem cost_6719_1456_join1_26 : P1_7_1_3.blockEstimate 6719 1456 8112 512 = 1225707587494 :=
  @P1_7_1_3.block_append 6719 1456 8112 8368 256 256 512 727285111718 498422475776 1225707587494 cost_6719_1456_join0_52 cost_6719_1456_join0_54 rfl rfl rfl

private theorem cost_6719_1456_join1_28 : P1_7_1_3.blockEstimate 6719 1456 8624 512 = 467855300608 :=
  @P1_7_1_3.block_append 6719 1456 8624 8880 256 256 512 307917417472 159937883136 467855300608 cost_6719_1456_join0_56 cost_6719_1456_join0_58 rfl rfl rfl

private theorem cost_6719_1456_join1_30 : P1_7_1_3.blockEstimate 6719 1456 9136 495 = 66169846208 :=
  @P1_7_1_3.block_append 6719 1456 9136 9392 256 239 495 58510404608 7659441600 66169846208 cost_6719_1456_join0_60 cost_6719_1456_join0_62 rfl rfl rfl

private theorem cost_6719_1456_join2_0 : P1_7_1_3.blockEstimate 6719 1456 1456 1024 = 1068229612800 :=
  @P1_7_1_3.block_append 6719 1456 1456 1968 512 512 1024 142559849088 925669763712 1068229612800 cost_6719_1456_join1_0 cost_6719_1456_join1_2 rfl rfl rfl

private theorem cost_6719_1456_join2_2 : P1_7_1_3.blockEstimate 6719 1456 2480 1024 = 6197337043588 :=
  @P1_7_1_3.block_append 6719 1456 2480 2992 512 512 1024 2300705658244 3896631385344 6197337043588 cost_6719_1456_join1_4 cost_6719_1456_join1_6 rfl rfl rfl

private theorem cost_6719_1456_join2_4 : P1_7_1_3.blockEstimate 6719 1456 3504 1024 = 11241833413120 :=
  @P1_7_1_3.block_append 6719 1456 3504 4016 512 512 1024 5176525085952 6065308327168 11241833413120 cost_6719_1456_join1_8 cost_6719_1456_join1_10 rfl rfl rfl

private theorem cost_6719_1456_join2_6 : P1_7_1_3.blockEstimate 6719 1456 4528 1024 = 13232524540416 :=
  @P1_7_1_3.block_append 6719 1456 4528 5040 512 512 1024 6562981108992 6669543431424 13232524540416 cost_6719_1456_join1_12 cost_6719_1456_join1_14 rfl rfl rfl

private theorem cost_6719_1456_join2_8 : P1_7_1_3.blockEstimate 6719 1456 5552 1024 = 12094331992576 :=
  @P1_7_1_3.block_append 6719 1456 5552 6064 512 512 1024 6384995294464 5709336698112 12094331992576 cost_6719_1456_join1_16 cost_6719_1456_join1_18 rfl rfl rfl

private theorem cost_6719_1456_join2_10 : P1_7_1_3.blockEstimate 6719 1456 6576 1024 = 8098853575003 :=
  @P1_7_1_3.block_append 6719 1456 6576 7088 512 512 1024 4660287880510 3438565694493 8098853575003 cost_6719_1456_join1_20 cost_6719_1456_join1_22 rfl rfl rfl

private theorem cost_6719_1456_join2_12 : P1_7_1_3.blockEstimate 6719 1456 7600 1024 = 3479126778072 :=
  @P1_7_1_3.block_append 6719 1456 7600 8112 512 512 1024 2253419190578 1225707587494 3479126778072 cost_6719_1456_join1_24 cost_6719_1456_join1_26 rfl rfl rfl

private theorem cost_6719_1456_join2_14 : P1_7_1_3.blockEstimate 6719 1456 8624 1007 = 534025146816 :=
  @P1_7_1_3.block_append 6719 1456 8624 9136 512 495 1007 467855300608 66169846208 534025146816 cost_6719_1456_join1_28 cost_6719_1456_join1_30 rfl rfl rfl

private theorem cost_6719_1456_join3_0 : P1_7_1_3.blockEstimate 6719 1456 1456 2048 = 7265566656388 :=
  @P1_7_1_3.block_append 6719 1456 1456 2480 1024 1024 2048 1068229612800 6197337043588 7265566656388 cost_6719_1456_join2_0 cost_6719_1456_join2_2 rfl rfl rfl

private theorem cost_6719_1456_join3_2 : P1_7_1_3.blockEstimate 6719 1456 3504 2048 = 24474357953536 :=
  @P1_7_1_3.block_append 6719 1456 3504 4528 1024 1024 2048 11241833413120 13232524540416 24474357953536 cost_6719_1456_join2_4 cost_6719_1456_join2_6 rfl rfl rfl

private theorem cost_6719_1456_join3_4 : P1_7_1_3.blockEstimate 6719 1456 5552 2048 = 20193185567579 :=
  @P1_7_1_3.block_append 6719 1456 5552 6576 1024 1024 2048 12094331992576 8098853575003 20193185567579 cost_6719_1456_join2_8 cost_6719_1456_join2_10 rfl rfl rfl

private theorem cost_6719_1456_join3_6 : P1_7_1_3.blockEstimate 6719 1456 7600 2031 = 4013151924888 :=
  @P1_7_1_3.block_append 6719 1456 7600 8624 1024 1007 2031 3479126778072 534025146816 4013151924888 cost_6719_1456_join2_12 cost_6719_1456_join2_14 rfl rfl rfl

private theorem cost_6719_1456_join4_0 : P1_7_1_3.blockEstimate 6719 1456 1456 4096 = 31739924609924 :=
  @P1_7_1_3.block_append 6719 1456 1456 3504 2048 2048 4096 7265566656388 24474357953536 31739924609924 cost_6719_1456_join3_0 cost_6719_1456_join3_2 rfl rfl rfl

private theorem cost_6719_1456_join4_2 : P1_7_1_3.blockEstimate 6719 1456 5552 4079 = 24206337492467 :=
  @P1_7_1_3.block_append 6719 1456 5552 7600 2048 2031 4079 20193185567579 4013151924888 24206337492467 cost_6719_1456_join3_4 cost_6719_1456_join3_6 rfl rfl rfl

private theorem cost_6719_1456_join5_0 : P1_7_1_3.blockEstimate 6719 1456 1456 8175 = 55946262102391 :=
  @P1_7_1_3.block_append 6719 1456 1456 5552 4096 4079 8175 31739924609924 24206337492467 55946262102391 cost_6719_1456_join4_0 cost_6719_1456_join4_2 rfl rfl rfl

private theorem cost_6719_1456_total : P1_7_1_3.momentEstimate 6719 1456 = 55946262102391 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 6719 + 1456 = 8175 by decide]
  exact cost_6719_1456_join5_0

theorem moment6719_1456 : P1_7_1.groupedPoleMoment 6719 1456 ≤ 55946262102391 :=
  (P1_7_1_3.grouped_bound 6719 1456).trans_eq cost_6719_1456_total
private theorem cost_6719_1491_block0 : P1_7_1_3.blockEstimate 6719 1491 1491 128 = 2369712800 := by decide +kernel

private theorem cost_6719_1491_block1 : P1_7_1_3.blockEstimate 6719 1491 1619 128 = 16097657504 := by decide +kernel

private theorem cost_6719_1491_block2 : P1_7_1_3.blockEstimate 6719 1491 1747 128 = 42705261216 := by decide +kernel

private theorem cost_6719_1491_block3 : P1_7_1_3.blockEstimate 6719 1491 1875 128 = 81387217568 := by decide +kernel

private theorem cost_6719_1491_block4 : P1_7_1_3.blockEstimate 6719 1491 2003 128 = 131338220192 := by decide +kernel

private theorem cost_6719_1491_block5 : P1_7_1_3.blockEstimate 6719 1491 2131 128 = 191752962720 := by decide +kernel

private theorem cost_6719_1491_block6 : P1_7_1_3.blockEstimate 6719 1491 2259 128 = 261826138784 := by decide +kernel

private theorem cost_6719_1491_block7 : P1_7_1_3.blockEstimate 6719 1491 2387 128 = 340752442016 := by decide +kernel

private theorem cost_6719_1491_block8 : P1_7_1_3.blockEstimate 6719 1491 2515 128 = 427726566048 := by decide +kernel

private theorem cost_6719_1491_block9 : P1_7_1_3.blockEstimate 6719 1491 2643 128 = 521943204512 := by decide +kernel

private theorem cost_6719_1491_block10 : P1_7_1_3.blockEstimate 6719 1491 2771 128 = 622597051040 := by decide +kernel

private theorem cost_6719_1491_block11 : P1_7_1_3.blockEstimate 6719 1491 2899 128 = 728803942959 := by decide +kernel

private theorem cost_6719_1491_block12 : P1_7_1_3.blockEstimate 6719 1491 3027 128 = 835674165376 := by decide +kernel

private theorem cost_6719_1491_block13 : P1_7_1_3.blockEstimate 6719 1491 3155 128 = 936790610048 := by decide +kernel

private theorem cost_6719_1491_block14 : P1_7_1_3.blockEstimate 6719 1491 3283 128 = 1031649153152 := by decide +kernel

private theorem cost_6719_1491_block15 : P1_7_1_3.blockEstimate 6719 1491 3411 128 = 1120249794688 := by decide +kernel

private theorem cost_6719_1491_block16 : P1_7_1_3.blockEstimate 6719 1491 3539 128 = 1202592534656 := by decide +kernel

private theorem cost_6719_1491_block17 : P1_7_1_3.blockEstimate 6719 1491 3667 128 = 1278677373056 := by decide +kernel

private theorem cost_6719_1491_block18 : P1_7_1_3.blockEstimate 6719 1491 3795 128 = 1348504309888 := by decide +kernel

private theorem cost_6719_1491_block19 : P1_7_1_3.blockEstimate 6719 1491 3923 128 = 1412073345152 := by decide +kernel

private theorem cost_6719_1491_block20 : P1_7_1_3.blockEstimate 6719 1491 4051 128 = 1469384478848 := by decide +kernel

private theorem cost_6719_1491_block21 : P1_7_1_3.blockEstimate 6719 1491 4179 128 = 1520437710976 := by decide +kernel

private theorem cost_6719_1491_block22 : P1_7_1_3.blockEstimate 6719 1491 4307 128 = 1565233041536 := by decide +kernel

private theorem cost_6719_1491_block23 : P1_7_1_3.blockEstimate 6719 1491 4435 128 = 1603770470528 := by decide +kernel

private theorem cost_6719_1491_block24 : P1_7_1_3.blockEstimate 6719 1491 4563 128 = 1636049997952 := by decide +kernel

private theorem cost_6719_1491_block25 : P1_7_1_3.blockEstimate 6719 1491 4691 128 = 1662071623808 := by decide +kernel

private theorem cost_6719_1491_block26 : P1_7_1_3.blockEstimate 6719 1491 4819 128 = 1681835348096 := by decide +kernel

private theorem cost_6719_1491_block27 : P1_7_1_3.blockEstimate 6719 1491 4947 128 = 1695341170816 := by decide +kernel

private theorem cost_6719_1491_block28 : P1_7_1_3.blockEstimate 6719 1491 5075 128 = 1702589091968 := by decide +kernel

private theorem cost_6719_1491_block29 : P1_7_1_3.blockEstimate 6719 1491 5203 128 = 1703579111552 := by decide +kernel

private theorem cost_6719_1491_block30 : P1_7_1_3.blockEstimate 6719 1491 5331 128 = 1698311229568 := by decide +kernel

private theorem cost_6719_1491_block31 : P1_7_1_3.blockEstimate 6719 1491 5459 128 = 1686785446016 := by decide +kernel

private theorem cost_6719_1491_block32 : P1_7_1_3.blockEstimate 6719 1491 5587 128 = 1669001760896 := by decide +kernel

private theorem cost_6719_1491_block33 : P1_7_1_3.blockEstimate 6719 1491 5715 128 = 1644960174208 := by decide +kernel

private theorem cost_6719_1491_block34 : P1_7_1_3.blockEstimate 6719 1491 5843 128 = 1614660685952 := by decide +kernel

private theorem cost_6719_1491_block35 : P1_7_1_3.blockEstimate 6719 1491 5971 128 = 1578103296128 := by decide +kernel

private theorem cost_6719_1491_block36 : P1_7_1_3.blockEstimate 6719 1491 6099 128 = 1535288004736 := by decide +kernel

private theorem cost_6719_1491_block37 : P1_7_1_3.blockEstimate 6719 1491 6227 128 = 1486214811776 := by decide +kernel

private theorem cost_6719_1491_block38 : P1_7_1_3.blockEstimate 6719 1491 6355 128 = 1430883717248 := by decide +kernel

private theorem cost_6719_1491_block39 : P1_7_1_3.blockEstimate 6719 1491 6483 128 = 1369294721152 := by decide +kernel

private theorem cost_6719_1491_block40 : P1_7_1_3.blockEstimate 6719 1491 6611 128 = 1301450511228 := by decide +kernel

private theorem cost_6719_1491_block41 : P1_7_1_3.blockEstimate 6719 1491 6739 128 = 1228405202466 := by decide +kernel

private theorem cost_6719_1491_block42 : P1_7_1_3.blockEstimate 6719 1491 6867 128 = 1153038628562 := by decide +kernel

private theorem cost_6719_1491_block43 : P1_7_1_3.blockEstimate 6719 1491 6995 128 = 1076308897022 := by decide +kernel

private theorem cost_6719_1491_block44 : P1_7_1_3.blockEstimate 6719 1491 7123 128 = 998782677535 := by decide +kernel

private theorem cost_6719_1491_block45 : P1_7_1_3.blockEstimate 6719 1491 7251 128 = 921009368286 := by decide +kernel

private theorem cost_6719_1491_block46 : P1_7_1_3.blockEstimate 6719 1491 7379 128 = 843521094617 := by decide +kernel

private theorem cost_6719_1491_block47 : P1_7_1_3.blockEstimate 6719 1491 7507 128 = 766832709762 := by decide +kernel

private theorem cost_6719_1491_block48 : P1_7_1_3.blockEstimate 6719 1491 7635 128 = 691441796146 := by decide +kernel

private theorem cost_6719_1491_block49 : P1_7_1_3.blockEstimate 6719 1491 7763 128 = 617828662989 := by decide +kernel

private theorem cost_6719_1491_block50 : P1_7_1_3.blockEstimate 6719 1491 7891 128 = 546456347722 := by decide +kernel

private theorem cost_6719_1491_block51 : P1_7_1_3.blockEstimate 6719 1491 8019 128 = 477770616460 := by decide +kernel

private theorem cost_6719_1491_block52 : P1_7_1_3.blockEstimate 6719 1491 8147 128 = 412063045723 := by decide +kernel

private theorem cost_6719_1491_block53 : P1_7_1_3.blockEstimate 6719 1491 8275 128 = 349293370576 := by decide +kernel

private theorem cost_6719_1491_block54 : P1_7_1_3.blockEstimate 6719 1491 8403 128 = 290741780688 := by decide +kernel

private theorem cost_6719_1491_block55 : P1_7_1_3.blockEstimate 6719 1491 8531 128 = 236807922896 := by decide +kernel

private theorem cost_6719_1491_block56 : P1_7_1_3.blockEstimate 6719 1491 8659 128 = 187743455440 := by decide +kernel

private theorem cost_6719_1491_block57 : P1_7_1_3.blockEstimate 6719 1491 8787 128 = 143800036560 := by decide +kernel

private theorem cost_6719_1491_block58 : P1_7_1_3.blockEstimate 6719 1491 8915 128 = 105229324496 := by decide +kernel

private theorem cost_6719_1491_block59 : P1_7_1_3.blockEstimate 6719 1491 9043 128 = 72282977488 := by decide +kernel

private theorem cost_6719_1491_block60 : P1_7_1_3.blockEstimate 6719 1491 9171 128 = 45212653776 := by decide +kernel

private theorem cost_6719_1491_block61 : P1_7_1_3.blockEstimate 6719 1491 9299 128 = 24270011600 := by decide +kernel

private theorem cost_6719_1491_block62 : P1_7_1_3.blockEstimate 6719 1491 9427 128 = 9706709200 := by decide +kernel

private theorem cost_6719_1491_block63 : P1_7_1_3.blockEstimate 6719 1491 9555 128 = 1774404816 := by decide +kernel

private theorem cost_6719_1491_block64 : P1_7_1_3.blockEstimate 6719 1491 9683 18 = 4127390 := by decide +kernel

private theorem cost_6719_1491_join0_0 : P1_7_1_3.blockEstimate 6719 1491 1491 256 = 18467370304 :=
  @P1_7_1_3.block_append 6719 1491 1491 1619 128 128 256 2369712800 16097657504 18467370304 cost_6719_1491_block0 cost_6719_1491_block1 rfl rfl rfl

private theorem cost_6719_1491_join0_2 : P1_7_1_3.blockEstimate 6719 1491 1747 256 = 124092478784 :=
  @P1_7_1_3.block_append 6719 1491 1747 1875 128 128 256 42705261216 81387217568 124092478784 cost_6719_1491_block2 cost_6719_1491_block3 rfl rfl rfl

private theorem cost_6719_1491_join0_4 : P1_7_1_3.blockEstimate 6719 1491 2003 256 = 323091182912 :=
  @P1_7_1_3.block_append 6719 1491 2003 2131 128 128 256 131338220192 191752962720 323091182912 cost_6719_1491_block4 cost_6719_1491_block5 rfl rfl rfl

private theorem cost_6719_1491_join0_6 : P1_7_1_3.blockEstimate 6719 1491 2259 256 = 602578580800 :=
  @P1_7_1_3.block_append 6719 1491 2259 2387 128 128 256 261826138784 340752442016 602578580800 cost_6719_1491_block6 cost_6719_1491_block7 rfl rfl rfl

private theorem cost_6719_1491_join0_8 : P1_7_1_3.blockEstimate 6719 1491 2515 256 = 949669770560 :=
  @P1_7_1_3.block_append 6719 1491 2515 2643 128 128 256 427726566048 521943204512 949669770560 cost_6719_1491_block8 cost_6719_1491_block9 rfl rfl rfl

private theorem cost_6719_1491_join0_10 : P1_7_1_3.blockEstimate 6719 1491 2771 256 = 1351400993999 :=
  @P1_7_1_3.block_append 6719 1491 2771 2899 128 128 256 622597051040 728803942959 1351400993999 cost_6719_1491_block10 cost_6719_1491_block11 rfl rfl rfl

private theorem cost_6719_1491_join0_12 : P1_7_1_3.blockEstimate 6719 1491 3027 256 = 1772464775424 :=
  @P1_7_1_3.block_append 6719 1491 3027 3155 128 128 256 835674165376 936790610048 1772464775424 cost_6719_1491_block12 cost_6719_1491_block13 rfl rfl rfl

private theorem cost_6719_1491_join0_14 : P1_7_1_3.blockEstimate 6719 1491 3283 256 = 2151898947840 :=
  @P1_7_1_3.block_append 6719 1491 3283 3411 128 128 256 1031649153152 1120249794688 2151898947840 cost_6719_1491_block14 cost_6719_1491_block15 rfl rfl rfl

private theorem cost_6719_1491_join0_16 : P1_7_1_3.blockEstimate 6719 1491 3539 256 = 2481269907712 :=
  @P1_7_1_3.block_append 6719 1491 3539 3667 128 128 256 1202592534656 1278677373056 2481269907712 cost_6719_1491_block16 cost_6719_1491_block17 rfl rfl rfl

private theorem cost_6719_1491_join0_18 : P1_7_1_3.blockEstimate 6719 1491 3795 256 = 2760577655040 :=
  @P1_7_1_3.block_append 6719 1491 3795 3923 128 128 256 1348504309888 1412073345152 2760577655040 cost_6719_1491_block18 cost_6719_1491_block19 rfl rfl rfl

private theorem cost_6719_1491_join0_20 : P1_7_1_3.blockEstimate 6719 1491 4051 256 = 2989822189824 :=
  @P1_7_1_3.block_append 6719 1491 4051 4179 128 128 256 1469384478848 1520437710976 2989822189824 cost_6719_1491_block20 cost_6719_1491_block21 rfl rfl rfl

private theorem cost_6719_1491_join0_22 : P1_7_1_3.blockEstimate 6719 1491 4307 256 = 3169003512064 :=
  @P1_7_1_3.block_append 6719 1491 4307 4435 128 128 256 1565233041536 1603770470528 3169003512064 cost_6719_1491_block22 cost_6719_1491_block23 rfl rfl rfl

private theorem cost_6719_1491_join0_24 : P1_7_1_3.blockEstimate 6719 1491 4563 256 = 3298121621760 :=
  @P1_7_1_3.block_append 6719 1491 4563 4691 128 128 256 1636049997952 1662071623808 3298121621760 cost_6719_1491_block24 cost_6719_1491_block25 rfl rfl rfl

private theorem cost_6719_1491_join0_26 : P1_7_1_3.blockEstimate 6719 1491 4819 256 = 3377176518912 :=
  @P1_7_1_3.block_append 6719 1491 4819 4947 128 128 256 1681835348096 1695341170816 3377176518912 cost_6719_1491_block26 cost_6719_1491_block27 rfl rfl rfl

private theorem cost_6719_1491_join0_28 : P1_7_1_3.blockEstimate 6719 1491 5075 256 = 3406168203520 :=
  @P1_7_1_3.block_append 6719 1491 5075 5203 128 128 256 1702589091968 1703579111552 3406168203520 cost_6719_1491_block28 cost_6719_1491_block29 rfl rfl rfl

private theorem cost_6719_1491_join0_30 : P1_7_1_3.blockEstimate 6719 1491 5331 256 = 3385096675584 :=
  @P1_7_1_3.block_append 6719 1491 5331 5459 128 128 256 1698311229568 1686785446016 3385096675584 cost_6719_1491_block30 cost_6719_1491_block31 rfl rfl rfl

private theorem cost_6719_1491_join0_32 : P1_7_1_3.blockEstimate 6719 1491 5587 256 = 3313961935104 :=
  @P1_7_1_3.block_append 6719 1491 5587 5715 128 128 256 1669001760896 1644960174208 3313961935104 cost_6719_1491_block32 cost_6719_1491_block33 rfl rfl rfl

private theorem cost_6719_1491_join0_34 : P1_7_1_3.blockEstimate 6719 1491 5843 256 = 3192763982080 :=
  @P1_7_1_3.block_append 6719 1491 5843 5971 128 128 256 1614660685952 1578103296128 3192763982080 cost_6719_1491_block34 cost_6719_1491_block35 rfl rfl rfl

private theorem cost_6719_1491_join0_36 : P1_7_1_3.blockEstimate 6719 1491 6099 256 = 3021502816512 :=
  @P1_7_1_3.block_append 6719 1491 6099 6227 128 128 256 1535288004736 1486214811776 3021502816512 cost_6719_1491_block36 cost_6719_1491_block37 rfl rfl rfl

private theorem cost_6719_1491_join0_38 : P1_7_1_3.blockEstimate 6719 1491 6355 256 = 2800178438400 :=
  @P1_7_1_3.block_append 6719 1491 6355 6483 128 128 256 1430883717248 1369294721152 2800178438400 cost_6719_1491_block38 cost_6719_1491_block39 rfl rfl rfl

private theorem cost_6719_1491_join0_40 : P1_7_1_3.blockEstimate 6719 1491 6611 256 = 2529855713694 :=
  @P1_7_1_3.block_append 6719 1491 6611 6739 128 128 256 1301450511228 1228405202466 2529855713694 cost_6719_1491_block40 cost_6719_1491_block41 rfl rfl rfl

private theorem cost_6719_1491_join0_42 : P1_7_1_3.blockEstimate 6719 1491 6867 256 = 2229347525584 :=
  @P1_7_1_3.block_append 6719 1491 6867 6995 128 128 256 1153038628562 1076308897022 2229347525584 cost_6719_1491_block42 cost_6719_1491_block43 rfl rfl rfl

private theorem cost_6719_1491_join0_44 : P1_7_1_3.blockEstimate 6719 1491 7123 256 = 1919792045821 :=
  @P1_7_1_3.block_append 6719 1491 7123 7251 128 128 256 998782677535 921009368286 1919792045821 cost_6719_1491_block44 cost_6719_1491_block45 rfl rfl rfl

private theorem cost_6719_1491_join0_46 : P1_7_1_3.blockEstimate 6719 1491 7379 256 = 1610353804379 :=
  @P1_7_1_3.block_append 6719 1491 7379 7507 128 128 256 843521094617 766832709762 1610353804379 cost_6719_1491_block46 cost_6719_1491_block47 rfl rfl rfl

private theorem cost_6719_1491_join0_48 : P1_7_1_3.blockEstimate 6719 1491 7635 256 = 1309270459135 :=
  @P1_7_1_3.block_append 6719 1491 7635 7763 128 128 256 691441796146 617828662989 1309270459135 cost_6719_1491_block48 cost_6719_1491_block49 rfl rfl rfl

private theorem cost_6719_1491_join0_50 : P1_7_1_3.blockEstimate 6719 1491 7891 256 = 1024226964182 :=
  @P1_7_1_3.block_append 6719 1491 7891 8019 128 128 256 546456347722 477770616460 1024226964182 cost_6719_1491_block50 cost_6719_1491_block51 rfl rfl rfl

private theorem cost_6719_1491_join0_52 : P1_7_1_3.blockEstimate 6719 1491 8147 256 = 761356416299 :=
  @P1_7_1_3.block_append 6719 1491 8147 8275 128 128 256 412063045723 349293370576 761356416299 cost_6719_1491_block52 cost_6719_1491_block53 rfl rfl rfl

private theorem cost_6719_1491_join0_54 : P1_7_1_3.blockEstimate 6719 1491 8403 256 = 527549703584 :=
  @P1_7_1_3.block_append 6719 1491 8403 8531 128 128 256 290741780688 236807922896 527549703584 cost_6719_1491_block54 cost_6719_1491_block55 rfl rfl rfl

private theorem cost_6719_1491_join0_56 : P1_7_1_3.blockEstimate 6719 1491 8659 256 = 331543492000 :=
  @P1_7_1_3.block_append 6719 1491 8659 8787 128 128 256 187743455440 143800036560 331543492000 cost_6719_1491_block56 cost_6719_1491_block57 rfl rfl rfl

private theorem cost_6719_1491_join0_58 : P1_7_1_3.blockEstimate 6719 1491 8915 256 = 177512301984 :=
  @P1_7_1_3.block_append 6719 1491 8915 9043 128 128 256 105229324496 72282977488 177512301984 cost_6719_1491_block58 cost_6719_1491_block59 rfl rfl rfl

private theorem cost_6719_1491_join0_60 : P1_7_1_3.blockEstimate 6719 1491 9171 256 = 69482665376 :=
  @P1_7_1_3.block_append 6719 1491 9171 9299 128 128 256 45212653776 24270011600 69482665376 cost_6719_1491_block60 cost_6719_1491_block61 rfl rfl rfl

private theorem cost_6719_1491_join0_62 : P1_7_1_3.blockEstimate 6719 1491 9427 256 = 11481114016 :=
  @P1_7_1_3.block_append 6719 1491 9427 9555 128 128 256 9706709200 1774404816 11481114016 cost_6719_1491_block62 cost_6719_1491_block63 rfl rfl rfl

private theorem cost_6719_1491_join1_0 : P1_7_1_3.blockEstimate 6719 1491 1491 512 = 142559849088 :=
  @P1_7_1_3.block_append 6719 1491 1491 1747 256 256 512 18467370304 124092478784 142559849088 cost_6719_1491_join0_0 cost_6719_1491_join0_2 rfl rfl rfl

private theorem cost_6719_1491_join1_2 : P1_7_1_3.blockEstimate 6719 1491 2003 512 = 925669763712 :=
  @P1_7_1_3.block_append 6719 1491 2003 2259 256 256 512 323091182912 602578580800 925669763712 cost_6719_1491_join0_4 cost_6719_1491_join0_6 rfl rfl rfl

private theorem cost_6719_1491_join1_4 : P1_7_1_3.blockEstimate 6719 1491 2515 512 = 2301070764559 :=
  @P1_7_1_3.block_append 6719 1491 2515 2771 256 256 512 949669770560 1351400993999 2301070764559 cost_6719_1491_join0_8 cost_6719_1491_join0_10 rfl rfl rfl

private theorem cost_6719_1491_join1_6 : P1_7_1_3.blockEstimate 6719 1491 3027 512 = 3924363723264 :=
  @P1_7_1_3.block_append 6719 1491 3027 3283 256 256 512 1772464775424 2151898947840 3924363723264 cost_6719_1491_join0_12 cost_6719_1491_join0_14 rfl rfl rfl

private theorem cost_6719_1491_join1_8 : P1_7_1_3.blockEstimate 6719 1491 3539 512 = 5241847562752 :=
  @P1_7_1_3.block_append 6719 1491 3539 3795 256 256 512 2481269907712 2760577655040 5241847562752 cost_6719_1491_join0_16 cost_6719_1491_join0_18 rfl rfl rfl

private theorem cost_6719_1491_join1_10 : P1_7_1_3.blockEstimate 6719 1491 4051 512 = 6158825701888 :=
  @P1_7_1_3.block_append 6719 1491 4051 4307 256 256 512 2989822189824 3169003512064 6158825701888 cost_6719_1491_join0_20 cost_6719_1491_join0_22 rfl rfl rfl

private theorem cost_6719_1491_join1_12 : P1_7_1_3.blockEstimate 6719 1491 4563 512 = 6675298140672 :=
  @P1_7_1_3.block_append 6719 1491 4563 4819 256 256 512 3298121621760 3377176518912 6675298140672 cost_6719_1491_join0_24 cost_6719_1491_join0_26 rfl rfl rfl

private theorem cost_6719_1491_join1_14 : P1_7_1_3.blockEstimate 6719 1491 5075 512 = 6791264879104 :=
  @P1_7_1_3.block_append 6719 1491 5075 5331 256 256 512 3406168203520 3385096675584 6791264879104 cost_6719_1491_join0_28 cost_6719_1491_join0_30 rfl rfl rfl

private theorem cost_6719_1491_join1_16 : P1_7_1_3.blockEstimate 6719 1491 5587 512 = 6506725917184 :=
  @P1_7_1_3.block_append 6719 1491 5587 5843 256 256 512 3313961935104 3192763982080 6506725917184 cost_6719_1491_join0_32 cost_6719_1491_join0_34 rfl rfl rfl

private theorem cost_6719_1491_join1_18 : P1_7_1_3.blockEstimate 6719 1491 6099 512 = 5821681254912 :=
  @P1_7_1_3.block_append 6719 1491 6099 6355 256 256 512 3021502816512 2800178438400 5821681254912 cost_6719_1491_join0_36 cost_6719_1491_join0_38 rfl rfl rfl

private theorem cost_6719_1491_join1_20 : P1_7_1_3.blockEstimate 6719 1491 6611 512 = 4759203239278 :=
  @P1_7_1_3.block_append 6719 1491 6611 6867 256 256 512 2529855713694 2229347525584 4759203239278 cost_6719_1491_join0_40 cost_6719_1491_join0_42 rfl rfl rfl

private theorem cost_6719_1491_join1_22 : P1_7_1_3.blockEstimate 6719 1491 7123 512 = 3530145850200 :=
  @P1_7_1_3.block_append 6719 1491 7123 7379 256 256 512 1919792045821 1610353804379 3530145850200 cost_6719_1491_join0_44 cost_6719_1491_join0_46 rfl rfl rfl

private theorem cost_6719_1491_join1_24 : P1_7_1_3.blockEstimate 6719 1491 7635 512 = 2333497423317 :=
  @P1_7_1_3.block_append 6719 1491 7635 7891 256 256 512 1309270459135 1024226964182 2333497423317 cost_6719_1491_join0_48 cost_6719_1491_join0_50 rfl rfl rfl

private theorem cost_6719_1491_join1_26 : P1_7_1_3.blockEstimate 6719 1491 8147 512 = 1288906119883 :=
  @P1_7_1_3.block_append 6719 1491 8147 8403 256 256 512 761356416299 527549703584 1288906119883 cost_6719_1491_join0_52 cost_6719_1491_join0_54 rfl rfl rfl

private theorem cost_6719_1491_join1_28 : P1_7_1_3.blockEstimate 6719 1491 8659 512 = 509055793984 :=
  @P1_7_1_3.block_append 6719 1491 8659 8915 256 256 512 331543492000 177512301984 509055793984 cost_6719_1491_join0_56 cost_6719_1491_join0_58 rfl rfl rfl

private theorem cost_6719_1491_join1_30 : P1_7_1_3.blockEstimate 6719 1491 9171 512 = 80963779392 :=
  @P1_7_1_3.block_append 6719 1491 9171 9427 256 256 512 69482665376 11481114016 80963779392 cost_6719_1491_join0_60 cost_6719_1491_join0_62 rfl rfl rfl

private theorem cost_6719_1491_join2_0 : P1_7_1_3.blockEstimate 6719 1491 1491 1024 = 1068229612800 :=
  @P1_7_1_3.block_append 6719 1491 1491 2003 512 512 1024 142559849088 925669763712 1068229612800 cost_6719_1491_join1_0 cost_6719_1491_join1_2 rfl rfl rfl

private theorem cost_6719_1491_join2_2 : P1_7_1_3.blockEstimate 6719 1491 2515 1024 = 6225434487823 :=
  @P1_7_1_3.block_append 6719 1491 2515 3027 512 512 1024 2301070764559 3924363723264 6225434487823 cost_6719_1491_join1_4 cost_6719_1491_join1_6 rfl rfl rfl

private theorem cost_6719_1491_join2_4 : P1_7_1_3.blockEstimate 6719 1491 3539 1024 = 11400673264640 :=
  @P1_7_1_3.block_append 6719 1491 3539 4051 512 512 1024 5241847562752 6158825701888 11400673264640 cost_6719_1491_join1_8 cost_6719_1491_join1_10 rfl rfl rfl

private theorem cost_6719_1491_join2_6 : P1_7_1_3.blockEstimate 6719 1491 4563 1024 = 13466563019776 :=
  @P1_7_1_3.block_append 6719 1491 4563 5075 512 512 1024 6675298140672 6791264879104 13466563019776 cost_6719_1491_join1_12 cost_6719_1491_join1_14 rfl rfl rfl

private theorem cost_6719_1491_join2_8 : P1_7_1_3.blockEstimate 6719 1491 5587 1024 = 12328407172096 :=
  @P1_7_1_3.block_append 6719 1491 5587 6099 512 512 1024 6506725917184 5821681254912 12328407172096 cost_6719_1491_join1_16 cost_6719_1491_join1_18 rfl rfl rfl

private theorem cost_6719_1491_join2_10 : P1_7_1_3.blockEstimate 6719 1491 6611 1024 = 8289349089478 :=
  @P1_7_1_3.block_append 6719 1491 6611 7123 512 512 1024 4759203239278 3530145850200 8289349089478 cost_6719_1491_join1_20 cost_6719_1491_join1_22 rfl rfl rfl

private theorem cost_6719_1491_join2_12 : P1_7_1_3.blockEstimate 6719 1491 7635 1024 = 3622403543200 :=
  @P1_7_1_3.block_append 6719 1491 7635 8147 512 512 1024 2333497423317 1288906119883 3622403543200 cost_6719_1491_join1_24 cost_6719_1491_join1_26 rfl rfl rfl

private theorem cost_6719_1491_join2_14 : P1_7_1_3.blockEstimate 6719 1491 8659 1024 = 590019573376 :=
  @P1_7_1_3.block_append 6719 1491 8659 9171 512 512 1024 509055793984 80963779392 590019573376 cost_6719_1491_join1_28 cost_6719_1491_join1_30 rfl rfl rfl

private theorem cost_6719_1491_join3_0 : P1_7_1_3.blockEstimate 6719 1491 1491 2048 = 7293664100623 :=
  @P1_7_1_3.block_append 6719 1491 1491 2515 1024 1024 2048 1068229612800 6225434487823 7293664100623 cost_6719_1491_join2_0 cost_6719_1491_join2_2 rfl rfl rfl

private theorem cost_6719_1491_join3_2 : P1_7_1_3.blockEstimate 6719 1491 3539 2048 = 24867236284416 :=
  @P1_7_1_3.block_append 6719 1491 3539 4563 1024 1024 2048 11400673264640 13466563019776 24867236284416 cost_6719_1491_join2_4 cost_6719_1491_join2_6 rfl rfl rfl

private theorem cost_6719_1491_join3_4 : P1_7_1_3.blockEstimate 6719 1491 5587 2048 = 20617756261574 :=
  @P1_7_1_3.block_append 6719 1491 5587 6611 1024 1024 2048 12328407172096 8289349089478 20617756261574 cost_6719_1491_join2_8 cost_6719_1491_join2_10 rfl rfl rfl

private theorem cost_6719_1491_join3_6 : P1_7_1_3.blockEstimate 6719 1491 7635 2048 = 4212423116576 :=
  @P1_7_1_3.block_append 6719 1491 7635 8659 1024 1024 2048 3622403543200 590019573376 4212423116576 cost_6719_1491_join2_12 cost_6719_1491_join2_14 rfl rfl rfl

private theorem cost_6719_1491_join4_0 : P1_7_1_3.blockEstimate 6719 1491 1491 4096 = 32160900385039 :=
  @P1_7_1_3.block_append 6719 1491 1491 3539 2048 2048 4096 7293664100623 24867236284416 32160900385039 cost_6719_1491_join3_0 cost_6719_1491_join3_2 rfl rfl rfl

private theorem cost_6719_1491_join4_2 : P1_7_1_3.blockEstimate 6719 1491 5587 4096 = 24830179378150 :=
  @P1_7_1_3.block_append 6719 1491 5587 7635 2048 2048 4096 20617756261574 4212423116576 24830179378150 cost_6719_1491_join3_4 cost_6719_1491_join3_6 rfl rfl rfl

private theorem cost_6719_1491_join5_0 : P1_7_1_3.blockEstimate 6719 1491 1491 8192 = 56991079763189 :=
  @P1_7_1_3.block_append 6719 1491 1491 5587 4096 4096 8192 32160900385039 24830179378150 56991079763189 cost_6719_1491_join4_0 cost_6719_1491_join4_2 rfl rfl rfl

private theorem cost_6719_1491_join6_0 : P1_7_1_3.blockEstimate 6719 1491 1491 8210 = 56991083890579 :=
  @P1_7_1_3.block_append 6719 1491 1491 9683 8192 18 8210 56991079763189 4127390 56991083890579 cost_6719_1491_join5_0 cost_6719_1491_block64 rfl rfl rfl

private theorem cost_6719_1491_total : P1_7_1_3.momentEstimate 6719 1491 = 56991083890579 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 6719 + 1491 = 8210 by decide]
  exact cost_6719_1491_join6_0

theorem moment6719_1491 : P1_7_1.groupedPoleMoment 6719 1491 ≤ 56991083890579 :=
  (P1_7_1_3.grouped_bound 6719 1491).trans_eq cost_6719_1491_total
private theorem cost_7573_1628_block0 : P1_7_1_3.blockEstimate 7573 1628 1628 128 = 2675239840 := by decide +kernel

private theorem cost_7573_1628_block1 : P1_7_1_3.blockEstimate 7573 1628 1756 128 = 18208144288 := by decide +kernel

private theorem cost_7573_1628_block2 : P1_7_1_3.blockEstimate 7573 1628 1884 128 = 48411675552 := by decide +kernel

private theorem cost_7573_1628_block3 : P1_7_1_3.blockEstimate 7573 1628 2012 128 = 92480527264 := by decide +kernel

private theorem cost_7573_1628_block4 : P1_7_1_3.blockEstimate 7573 1628 2140 128 = 149609393056 := by decide +kernel

private theorem cost_7573_1628_block5 : P1_7_1_3.blockEstimate 7573 1628 2268 128 = 218992966560 := by decide +kernel

private theorem cost_7573_1628_block6 : P1_7_1_3.blockEstimate 7573 1628 2396 128 = 299825941408 := by decide +kernel

private theorem cost_7573_1628_block7 : P1_7_1_3.blockEstimate 7573 1628 2524 128 = 391303011232 := by decide +kernel

private theorem cost_7573_1628_block8 : P1_7_1_3.blockEstimate 7573 1628 2652 128 = 492618869664 := by decide +kernel

private theorem cost_7573_1628_block9 : P1_7_1_3.blockEstimate 7573 1628 2780 128 = 602968210336 := by decide +kernel

private theorem cost_7573_1628_block10 : P1_7_1_3.blockEstimate 7573 1628 2908 128 = 721545726880 := by decide +kernel

private theorem cost_7573_1628_block11 : P1_7_1_3.blockEstimate 7573 1628 3036 128 = 847546112928 := by decide +kernel

private theorem cost_7573_1628_block12 : P1_7_1_3.blockEstimate 7573 1628 3164 128 = 980118075367 := by decide +kernel

private theorem cost_7573_1628_block13 : P1_7_1_3.blockEstimate 7573 1628 3292 128 = 1114359960384 := by decide +kernel

private theorem cost_7573_1628_block14 : P1_7_1_3.blockEstimate 7573 1628 3420 128 = 1242549801792 := by decide +kernel

private theorem cost_7573_1628_block15 : P1_7_1_3.blockEstimate 7573 1628 3548 128 = 1363907121984 := by decide +kernel

private theorem cost_7573_1628_block16 : P1_7_1_3.blockEstimate 7573 1628 3676 128 = 1478431920960 := by decide +kernel

private theorem cost_7573_1628_block17 : P1_7_1_3.blockEstimate 7573 1628 3804 128 = 1586124198720 := by decide +kernel

private theorem cost_7573_1628_block18 : P1_7_1_3.blockEstimate 7573 1628 3932 128 = 1686983955264 := by decide +kernel

private theorem cost_7573_1628_block19 : P1_7_1_3.blockEstimate 7573 1628 4060 128 = 1781011190592 := by decide +kernel

private theorem cost_7573_1628_block20 : P1_7_1_3.blockEstimate 7573 1628 4188 128 = 1868205904704 := by decide +kernel

private theorem cost_7573_1628_block21 : P1_7_1_3.blockEstimate 7573 1628 4316 128 = 1948568097600 := by decide +kernel

private theorem cost_7573_1628_block22 : P1_7_1_3.blockEstimate 7573 1628 4444 128 = 2022097769280 := by decide +kernel

private theorem cost_7573_1628_block23 : P1_7_1_3.blockEstimate 7573 1628 4572 128 = 2088794919744 := by decide +kernel

private theorem cost_7573_1628_block24 : P1_7_1_3.blockEstimate 7573 1628 4700 128 = 2148659548992 := by decide +kernel

private theorem cost_7573_1628_block25 : P1_7_1_3.blockEstimate 7573 1628 4828 128 = 2201691657024 := by decide +kernel

private theorem cost_7573_1628_block26 : P1_7_1_3.blockEstimate 7573 1628 4956 128 = 2247891243840 := by decide +kernel

private theorem cost_7573_1628_block27 : P1_7_1_3.blockEstimate 7573 1628 5084 128 = 2287258309440 := by decide +kernel

private theorem cost_7573_1628_block28 : P1_7_1_3.blockEstimate 7573 1628 5212 128 = 2319792853824 := by decide +kernel

private theorem cost_7573_1628_block29 : P1_7_1_3.blockEstimate 7573 1628 5340 128 = 2345494876992 := by decide +kernel

private theorem cost_7573_1628_block30 : P1_7_1_3.blockEstimate 7573 1628 5468 128 = 2364364378944 := by decide +kernel

private theorem cost_7573_1628_block31 : P1_7_1_3.blockEstimate 7573 1628 5596 128 = 2376401359680 := by decide +kernel

private theorem cost_7573_1628_block32 : P1_7_1_3.blockEstimate 7573 1628 5724 128 = 2381605819200 := by decide +kernel

private theorem cost_7573_1628_block33 : P1_7_1_3.blockEstimate 7573 1628 5852 128 = 2379977757504 := by decide +kernel

private theorem cost_7573_1628_block34 : P1_7_1_3.blockEstimate 7573 1628 5980 128 = 2371517174592 := by decide +kernel

private theorem cost_7573_1628_block35 : P1_7_1_3.blockEstimate 7573 1628 6108 128 = 2356224070464 := by decide +kernel

private theorem cost_7573_1628_block36 : P1_7_1_3.blockEstimate 7573 1628 6236 128 = 2334098445120 := by decide +kernel

private theorem cost_7573_1628_block37 : P1_7_1_3.blockEstimate 7573 1628 6364 128 = 2305140298560 := by decide +kernel

private theorem cost_7573_1628_block38 : P1_7_1_3.blockEstimate 7573 1628 6492 128 = 2269349630784 := by decide +kernel

private theorem cost_7573_1628_block39 : P1_7_1_3.blockEstimate 7573 1628 6620 128 = 2226726441792 := by decide +kernel

private theorem cost_7573_1628_block40 : P1_7_1_3.blockEstimate 7573 1628 6748 128 = 2177270731584 := by decide +kernel

private theorem cost_7573_1628_block41 : P1_7_1_3.blockEstimate 7573 1628 6876 128 = 2120982500160 := by decide +kernel

private theorem cost_7573_1628_block42 : P1_7_1_3.blockEstimate 7573 1628 7004 128 = 2057861747520 := by decide +kernel

private theorem cost_7573_1628_block43 : P1_7_1_3.blockEstimate 7573 1628 7132 128 = 1987908473664 := by decide +kernel

private theorem cost_7573_1628_block44 : P1_7_1_3.blockEstimate 7573 1628 7260 128 = 1911122678592 := by decide +kernel

private theorem cost_7573_1628_block45 : P1_7_1_3.blockEstimate 7573 1628 7388 128 = 1827504362304 := by decide +kernel

private theorem cost_7573_1628_block46 : P1_7_1_3.blockEstimate 7573 1628 7516 128 = 1737187396440 := by decide +kernel

private theorem cost_7573_1628_block47 : P1_7_1_3.blockEstimate 7573 1628 7644 128 = 1642639569578 := by decide +kernel

private theorem cost_7573_1628_block48 : P1_7_1_3.blockEstimate 7573 1628 7772 128 = 1546350050284 := by decide +kernel

private theorem cost_7573_1628_block49 : P1_7_1_3.blockEstimate 7573 1628 7900 128 = 1448962040856 := by decide +kernel

private theorem cost_7573_1628_block50 : P1_7_1_3.blockEstimate 7573 1628 8028 128 = 1351039045014 := by decide +kernel

private theorem cost_7573_1628_block51 : P1_7_1_3.blockEstimate 7573 1628 8156 128 = 1253128746910 := by decide +kernel

private theorem cost_7573_1628_block52 : P1_7_1_3.blockEstimate 7573 1628 8284 128 = 1155763013396 := by decide +kernel

private theorem cost_7573_1628_block53 : P1_7_1_3.blockEstimate 7573 1628 8412 128 = 1059457889067 := by decide +kernel

private theorem cost_7573_1628_block54 : P1_7_1_3.blockEstimate 7573 1628 8540 128 = 964713602405 := by decide +kernel

private theorem cost_7573_1628_block55 : P1_7_1_3.blockEstimate 7573 1628 8668 128 = 872014558832 := by decide +kernel

private theorem cost_7573_1628_block56 : P1_7_1_3.blockEstimate 7573 1628 8796 128 = 781829348031 := by decide +kernel

private theorem cost_7573_1628_block57 : P1_7_1_3.blockEstimate 7573 1628 8924 128 = 694610737453 := by decide +kernel

private theorem cost_7573_1628_block58 : P1_7_1_3.blockEstimate 7573 1628 9052 128 = 610795676988 := by decide +kernel

private theorem cost_7573_1628_block59 : P1_7_1_3.blockEstimate 7573 1628 9180 128 = 530385236799 := by decide +kernel

private theorem cost_7573_1628_block60 : P1_7_1_3.blockEstimate 7573 1628 9308 128 = 453756368080 := by decide +kernel

private theorem cost_7573_1628_block61 : P1_7_1_3.blockEstimate 7573 1628 9436 128 = 382184378576 := by decide +kernel

private theorem cost_7573_1628_block62 : P1_7_1_3.blockEstimate 7573 1628 9564 128 = 315938827472 := by decide +kernel

private theorem cost_7573_1628_block63 : P1_7_1_3.blockEstimate 7573 1628 9692 128 = 255271373008 := by decide +kernel

private theorem cost_7573_1628_block64 : P1_7_1_3.blockEstimate 7573 1628 9820 128 = 200433673424 := by decide +kernel

private theorem cost_7573_1628_block65 : P1_7_1_3.blockEstimate 7573 1628 9948 128 = 151677386960 := by decide +kernel

private theorem cost_7573_1628_block66 : P1_7_1_3.blockEstimate 7573 1628 10076 128 = 109254171856 := by decide +kernel

private theorem cost_7573_1628_block67 : P1_7_1_3.blockEstimate 7573 1628 10204 128 = 73415686352 := by decide +kernel

private theorem cost_7573_1628_block68 : P1_7_1_3.blockEstimate 7573 1628 10332 128 = 44413588688 := by decide +kernel

private theorem cost_7573_1628_block69 : P1_7_1_3.blockEstimate 7573 1628 10460 128 = 22499537104 := by decide +kernel

private theorem cost_7573_1628_block70 : P1_7_1_3.blockEstimate 7573 1628 10588 128 = 7925189840 := by decide +kernel

private theorem cost_7573_1628_block71 : P1_7_1_3.blockEstimate 7573 1628 10716 113 = 940666243 := by decide +kernel

private theorem cost_7573_1628_join0_0 : P1_7_1_3.blockEstimate 7573 1628 1628 256 = 20883384128 :=
  @P1_7_1_3.block_append 7573 1628 1628 1756 128 128 256 2675239840 18208144288 20883384128 cost_7573_1628_block0 cost_7573_1628_block1 rfl rfl rfl

private theorem cost_7573_1628_join0_2 : P1_7_1_3.blockEstimate 7573 1628 1884 256 = 140892202816 :=
  @P1_7_1_3.block_append 7573 1628 1884 2012 128 128 256 48411675552 92480527264 140892202816 cost_7573_1628_block2 cost_7573_1628_block3 rfl rfl rfl

private theorem cost_7573_1628_join0_4 : P1_7_1_3.blockEstimate 7573 1628 2140 256 = 368602359616 :=
  @P1_7_1_3.block_append 7573 1628 2140 2268 128 128 256 149609393056 218992966560 368602359616 cost_7573_1628_block4 cost_7573_1628_block5 rfl rfl rfl

private theorem cost_7573_1628_join0_6 : P1_7_1_3.blockEstimate 7573 1628 2396 256 = 691128952640 :=
  @P1_7_1_3.block_append 7573 1628 2396 2524 128 128 256 299825941408 391303011232 691128952640 cost_7573_1628_block6 cost_7573_1628_block7 rfl rfl rfl

private theorem cost_7573_1628_join0_8 : P1_7_1_3.blockEstimate 7573 1628 2652 256 = 1095587080000 :=
  @P1_7_1_3.block_append 7573 1628 2652 2780 128 128 256 492618869664 602968210336 1095587080000 cost_7573_1628_block8 cost_7573_1628_block9 rfl rfl rfl

private theorem cost_7573_1628_join0_10 : P1_7_1_3.blockEstimate 7573 1628 2908 256 = 1569091839808 :=
  @P1_7_1_3.block_append 7573 1628 2908 3036 128 128 256 721545726880 847546112928 1569091839808 cost_7573_1628_block10 cost_7573_1628_block11 rfl rfl rfl

private theorem cost_7573_1628_join0_12 : P1_7_1_3.blockEstimate 7573 1628 3164 256 = 2094478035751 :=
  @P1_7_1_3.block_append 7573 1628 3164 3292 128 128 256 980118075367 1114359960384 2094478035751 cost_7573_1628_block12 cost_7573_1628_block13 rfl rfl rfl

private theorem cost_7573_1628_join0_14 : P1_7_1_3.blockEstimate 7573 1628 3420 256 = 2606456923776 :=
  @P1_7_1_3.block_append 7573 1628 3420 3548 128 128 256 1242549801792 1363907121984 2606456923776 cost_7573_1628_block14 cost_7573_1628_block15 rfl rfl rfl

private theorem cost_7573_1628_join0_16 : P1_7_1_3.blockEstimate 7573 1628 3676 256 = 3064556119680 :=
  @P1_7_1_3.block_append 7573 1628 3676 3804 128 128 256 1478431920960 1586124198720 3064556119680 cost_7573_1628_block16 cost_7573_1628_block17 rfl rfl rfl

private theorem cost_7573_1628_join0_18 : P1_7_1_3.blockEstimate 7573 1628 3932 256 = 3467995145856 :=
  @P1_7_1_3.block_append 7573 1628 3932 4060 128 128 256 1686983955264 1781011190592 3467995145856 cost_7573_1628_block18 cost_7573_1628_block19 rfl rfl rfl

private theorem cost_7573_1628_join0_20 : P1_7_1_3.blockEstimate 7573 1628 4188 256 = 3816774002304 :=
  @P1_7_1_3.block_append 7573 1628 4188 4316 128 128 256 1868205904704 1948568097600 3816774002304 cost_7573_1628_block20 cost_7573_1628_block21 rfl rfl rfl

private theorem cost_7573_1628_join0_22 : P1_7_1_3.blockEstimate 7573 1628 4444 256 = 4110892689024 :=
  @P1_7_1_3.block_append 7573 1628 4444 4572 128 128 256 2022097769280 2088794919744 4110892689024 cost_7573_1628_block22 cost_7573_1628_block23 rfl rfl rfl

private theorem cost_7573_1628_join0_24 : P1_7_1_3.blockEstimate 7573 1628 4700 256 = 4350351206016 :=
  @P1_7_1_3.block_append 7573 1628 4700 4828 128 128 256 2148659548992 2201691657024 4350351206016 cost_7573_1628_block24 cost_7573_1628_block25 rfl rfl rfl

private theorem cost_7573_1628_join0_26 : P1_7_1_3.blockEstimate 7573 1628 4956 256 = 4535149553280 :=
  @P1_7_1_3.block_append 7573 1628 4956 5084 128 128 256 2247891243840 2287258309440 4535149553280 cost_7573_1628_block26 cost_7573_1628_block27 rfl rfl rfl

private theorem cost_7573_1628_join0_28 : P1_7_1_3.blockEstimate 7573 1628 5212 256 = 4665287730816 :=
  @P1_7_1_3.block_append 7573 1628 5212 5340 128 128 256 2319792853824 2345494876992 4665287730816 cost_7573_1628_block28 cost_7573_1628_block29 rfl rfl rfl

private theorem cost_7573_1628_join0_30 : P1_7_1_3.blockEstimate 7573 1628 5468 256 = 4740765738624 :=
  @P1_7_1_3.block_append 7573 1628 5468 5596 128 128 256 2364364378944 2376401359680 4740765738624 cost_7573_1628_block30 cost_7573_1628_block31 rfl rfl rfl

private theorem cost_7573_1628_join0_32 : P1_7_1_3.blockEstimate 7573 1628 5724 256 = 4761583576704 :=
  @P1_7_1_3.block_append 7573 1628 5724 5852 128 128 256 2381605819200 2379977757504 4761583576704 cost_7573_1628_block32 cost_7573_1628_block33 rfl rfl rfl

private theorem cost_7573_1628_join0_34 : P1_7_1_3.blockEstimate 7573 1628 5980 256 = 4727741245056 :=
  @P1_7_1_3.block_append 7573 1628 5980 6108 128 128 256 2371517174592 2356224070464 4727741245056 cost_7573_1628_block34 cost_7573_1628_block35 rfl rfl rfl

private theorem cost_7573_1628_join0_36 : P1_7_1_3.blockEstimate 7573 1628 6236 256 = 4639238743680 :=
  @P1_7_1_3.block_append 7573 1628 6236 6364 128 128 256 2334098445120 2305140298560 4639238743680 cost_7573_1628_block36 cost_7573_1628_block37 rfl rfl rfl

private theorem cost_7573_1628_join0_38 : P1_7_1_3.blockEstimate 7573 1628 6492 256 = 4496076072576 :=
  @P1_7_1_3.block_append 7573 1628 6492 6620 128 128 256 2269349630784 2226726441792 4496076072576 cost_7573_1628_block38 cost_7573_1628_block39 rfl rfl rfl

private theorem cost_7573_1628_join0_40 : P1_7_1_3.blockEstimate 7573 1628 6748 256 = 4298253231744 :=
  @P1_7_1_3.block_append 7573 1628 6748 6876 128 128 256 2177270731584 2120982500160 4298253231744 cost_7573_1628_block40 cost_7573_1628_block41 rfl rfl rfl

private theorem cost_7573_1628_join0_42 : P1_7_1_3.blockEstimate 7573 1628 7004 256 = 4045770221184 :=
  @P1_7_1_3.block_append 7573 1628 7004 7132 128 128 256 2057861747520 1987908473664 4045770221184 cost_7573_1628_block42 cost_7573_1628_block43 rfl rfl rfl

private theorem cost_7573_1628_join0_44 : P1_7_1_3.blockEstimate 7573 1628 7260 256 = 3738627040896 :=
  @P1_7_1_3.block_append 7573 1628 7260 7388 128 128 256 1911122678592 1827504362304 3738627040896 cost_7573_1628_block44 cost_7573_1628_block45 rfl rfl rfl

private theorem cost_7573_1628_join0_46 : P1_7_1_3.blockEstimate 7573 1628 7516 256 = 3379826966018 :=
  @P1_7_1_3.block_append 7573 1628 7516 7644 128 128 256 1737187396440 1642639569578 3379826966018 cost_7573_1628_block46 cost_7573_1628_block47 rfl rfl rfl

private theorem cost_7573_1628_join0_48 : P1_7_1_3.blockEstimate 7573 1628 7772 256 = 2995312091140 :=
  @P1_7_1_3.block_append 7573 1628 7772 7900 128 128 256 1546350050284 1448962040856 2995312091140 cost_7573_1628_block48 cost_7573_1628_block49 rfl rfl rfl

private theorem cost_7573_1628_join0_50 : P1_7_1_3.blockEstimate 7573 1628 8028 256 = 2604167791924 :=
  @P1_7_1_3.block_append 7573 1628 8028 8156 128 128 256 1351039045014 1253128746910 2604167791924 cost_7573_1628_block50 cost_7573_1628_block51 rfl rfl rfl

private theorem cost_7573_1628_join0_52 : P1_7_1_3.blockEstimate 7573 1628 8284 256 = 2215220902463 :=
  @P1_7_1_3.block_append 7573 1628 8284 8412 128 128 256 1155763013396 1059457889067 2215220902463 cost_7573_1628_block52 cost_7573_1628_block53 rfl rfl rfl

private theorem cost_7573_1628_join0_54 : P1_7_1_3.blockEstimate 7573 1628 8540 256 = 1836728161237 :=
  @P1_7_1_3.block_append 7573 1628 8540 8668 128 128 256 964713602405 872014558832 1836728161237 cost_7573_1628_block54 cost_7573_1628_block55 rfl rfl rfl

private theorem cost_7573_1628_join0_56 : P1_7_1_3.blockEstimate 7573 1628 8796 256 = 1476440085484 :=
  @P1_7_1_3.block_append 7573 1628 8796 8924 128 128 256 781829348031 694610737453 1476440085484 cost_7573_1628_block56 cost_7573_1628_block57 rfl rfl rfl

private theorem cost_7573_1628_join0_58 : P1_7_1_3.blockEstimate 7573 1628 9052 256 = 1141180913787 :=
  @P1_7_1_3.block_append 7573 1628 9052 9180 128 128 256 610795676988 530385236799 1141180913787 cost_7573_1628_block58 cost_7573_1628_block59 rfl rfl rfl

private theorem cost_7573_1628_join0_60 : P1_7_1_3.blockEstimate 7573 1628 9308 256 = 835940746656 :=
  @P1_7_1_3.block_append 7573 1628 9308 9436 128 128 256 453756368080 382184378576 835940746656 cost_7573_1628_block60 cost_7573_1628_block61 rfl rfl rfl

private theorem cost_7573_1628_join0_62 : P1_7_1_3.blockEstimate 7573 1628 9564 256 = 571210200480 :=
  @P1_7_1_3.block_append 7573 1628 9564 9692 128 128 256 315938827472 255271373008 571210200480 cost_7573_1628_block62 cost_7573_1628_block63 rfl rfl rfl

private theorem cost_7573_1628_join0_64 : P1_7_1_3.blockEstimate 7573 1628 9820 256 = 352111060384 :=
  @P1_7_1_3.block_append 7573 1628 9820 9948 128 128 256 200433673424 151677386960 352111060384 cost_7573_1628_block64 cost_7573_1628_block65 rfl rfl rfl

private theorem cost_7573_1628_join0_66 : P1_7_1_3.blockEstimate 7573 1628 10076 256 = 182669858208 :=
  @P1_7_1_3.block_append 7573 1628 10076 10204 128 128 256 109254171856 73415686352 182669858208 cost_7573_1628_block66 cost_7573_1628_block67 rfl rfl rfl

private theorem cost_7573_1628_join0_68 : P1_7_1_3.blockEstimate 7573 1628 10332 256 = 66913125792 :=
  @P1_7_1_3.block_append 7573 1628 10332 10460 128 128 256 44413588688 22499537104 66913125792 cost_7573_1628_block68 cost_7573_1628_block69 rfl rfl rfl

private theorem cost_7573_1628_join0_70 : P1_7_1_3.blockEstimate 7573 1628 10588 241 = 8865856083 :=
  @P1_7_1_3.block_append 7573 1628 10588 10716 128 113 241 7925189840 940666243 8865856083 cost_7573_1628_block70 cost_7573_1628_block71 rfl rfl rfl

private theorem cost_7573_1628_join1_0 : P1_7_1_3.blockEstimate 7573 1628 1628 512 = 161775586944 :=
  @P1_7_1_3.block_append 7573 1628 1628 1884 256 256 512 20883384128 140892202816 161775586944 cost_7573_1628_join0_0 cost_7573_1628_join0_2 rfl rfl rfl

private theorem cost_7573_1628_join1_2 : P1_7_1_3.blockEstimate 7573 1628 2140 512 = 1059731312256 :=
  @P1_7_1_3.block_append 7573 1628 2140 2396 256 256 512 368602359616 691128952640 1059731312256 cost_7573_1628_join0_4 cost_7573_1628_join0_6 rfl rfl rfl

private theorem cost_7573_1628_join1_4 : P1_7_1_3.blockEstimate 7573 1628 2652 512 = 2664678919808 :=
  @P1_7_1_3.block_append 7573 1628 2652 2908 256 256 512 1095587080000 1569091839808 2664678919808 cost_7573_1628_join0_8 cost_7573_1628_join0_10 rfl rfl rfl

private theorem cost_7573_1628_join1_6 : P1_7_1_3.blockEstimate 7573 1628 3164 512 = 4700934959527 :=
  @P1_7_1_3.block_append 7573 1628 3164 3420 256 256 512 2094478035751 2606456923776 4700934959527 cost_7573_1628_join0_12 cost_7573_1628_join0_14 rfl rfl rfl

private theorem cost_7573_1628_join1_8 : P1_7_1_3.blockEstimate 7573 1628 3676 512 = 6532551265536 :=
  @P1_7_1_3.block_append 7573 1628 3676 3932 256 256 512 3064556119680 3467995145856 6532551265536 cost_7573_1628_join0_16 cost_7573_1628_join0_18 rfl rfl rfl

private theorem cost_7573_1628_join1_10 : P1_7_1_3.blockEstimate 7573 1628 4188 512 = 7927666691328 :=
  @P1_7_1_3.block_append 7573 1628 4188 4444 256 256 512 3816774002304 4110892689024 7927666691328 cost_7573_1628_join0_20 cost_7573_1628_join0_22 rfl rfl rfl

private theorem cost_7573_1628_join1_12 : P1_7_1_3.blockEstimate 7573 1628 4700 512 = 8885500759296 :=
  @P1_7_1_3.block_append 7573 1628 4700 4956 256 256 512 4350351206016 4535149553280 8885500759296 cost_7573_1628_join0_24 cost_7573_1628_join0_26 rfl rfl rfl

private theorem cost_7573_1628_join1_14 : P1_7_1_3.blockEstimate 7573 1628 5212 512 = 9406053469440 :=
  @P1_7_1_3.block_append 7573 1628 5212 5468 256 256 512 4665287730816 4740765738624 9406053469440 cost_7573_1628_join0_28 cost_7573_1628_join0_30 rfl rfl rfl

private theorem cost_7573_1628_join1_16 : P1_7_1_3.blockEstimate 7573 1628 5724 512 = 9489324821760 :=
  @P1_7_1_3.block_append 7573 1628 5724 5980 256 256 512 4761583576704 4727741245056 9489324821760 cost_7573_1628_join0_32 cost_7573_1628_join0_34 rfl rfl rfl

private theorem cost_7573_1628_join1_18 : P1_7_1_3.blockEstimate 7573 1628 6236 512 = 9135314816256 :=
  @P1_7_1_3.block_append 7573 1628 6236 6492 256 256 512 4639238743680 4496076072576 9135314816256 cost_7573_1628_join0_36 cost_7573_1628_join0_38 rfl rfl rfl

private theorem cost_7573_1628_join1_20 : P1_7_1_3.blockEstimate 7573 1628 6748 512 = 8344023452928 :=
  @P1_7_1_3.block_append 7573 1628 6748 7004 256 256 512 4298253231744 4045770221184 8344023452928 cost_7573_1628_join0_40 cost_7573_1628_join0_42 rfl rfl rfl

private theorem cost_7573_1628_join1_22 : P1_7_1_3.blockEstimate 7573 1628 7260 512 = 7118454006914 :=
  @P1_7_1_3.block_append 7573 1628 7260 7516 256 256 512 3738627040896 3379826966018 7118454006914 cost_7573_1628_join0_44 cost_7573_1628_join0_46 rfl rfl rfl

private theorem cost_7573_1628_join1_24 : P1_7_1_3.blockEstimate 7573 1628 7772 512 = 5599479883064 :=
  @P1_7_1_3.block_append 7573 1628 7772 8028 256 256 512 2995312091140 2604167791924 5599479883064 cost_7573_1628_join0_48 cost_7573_1628_join0_50 rfl rfl rfl

private theorem cost_7573_1628_join1_26 : P1_7_1_3.blockEstimate 7573 1628 8284 512 = 4051949063700 :=
  @P1_7_1_3.block_append 7573 1628 8284 8540 256 256 512 2215220902463 1836728161237 4051949063700 cost_7573_1628_join0_52 cost_7573_1628_join0_54 rfl rfl rfl

private theorem cost_7573_1628_join1_28 : P1_7_1_3.blockEstimate 7573 1628 8796 512 = 2617620999271 :=
  @P1_7_1_3.block_append 7573 1628 8796 9052 256 256 512 1476440085484 1141180913787 2617620999271 cost_7573_1628_join0_56 cost_7573_1628_join0_58 rfl rfl rfl

private theorem cost_7573_1628_join1_30 : P1_7_1_3.blockEstimate 7573 1628 9308 512 = 1407150947136 :=
  @P1_7_1_3.block_append 7573 1628 9308 9564 256 256 512 835940746656 571210200480 1407150947136 cost_7573_1628_join0_60 cost_7573_1628_join0_62 rfl rfl rfl

private theorem cost_7573_1628_join1_32 : P1_7_1_3.blockEstimate 7573 1628 9820 512 = 534780918592 :=
  @P1_7_1_3.block_append 7573 1628 9820 10076 256 256 512 352111060384 182669858208 534780918592 cost_7573_1628_join0_64 cost_7573_1628_join0_66 rfl rfl rfl

private theorem cost_7573_1628_join1_34 : P1_7_1_3.blockEstimate 7573 1628 10332 497 = 75778981875 :=
  @P1_7_1_3.block_append 7573 1628 10332 10588 256 241 497 66913125792 8865856083 75778981875 cost_7573_1628_join0_68 cost_7573_1628_join0_70 rfl rfl rfl

private theorem cost_7573_1628_join2_0 : P1_7_1_3.blockEstimate 7573 1628 1628 1024 = 1221506899200 :=
  @P1_7_1_3.block_append 7573 1628 1628 2140 512 512 1024 161775586944 1059731312256 1221506899200 cost_7573_1628_join1_0 cost_7573_1628_join1_2 rfl rfl rfl

private theorem cost_7573_1628_join2_2 : P1_7_1_3.blockEstimate 7573 1628 2652 1024 = 7365613879335 :=
  @P1_7_1_3.block_append 7573 1628 2652 3164 512 512 1024 2664678919808 4700934959527 7365613879335 cost_7573_1628_join1_4 cost_7573_1628_join1_6 rfl rfl rfl

private theorem cost_7573_1628_join2_4 : P1_7_1_3.blockEstimate 7573 1628 3676 1024 = 14460217956864 :=
  @P1_7_1_3.block_append 7573 1628 3676 4188 512 512 1024 6532551265536 7927666691328 14460217956864 cost_7573_1628_join1_8 cost_7573_1628_join1_10 rfl rfl rfl

private theorem cost_7573_1628_join2_6 : P1_7_1_3.blockEstimate 7573 1628 4700 1024 = 18291554228736 :=
  @P1_7_1_3.block_append 7573 1628 4700 5212 512 512 1024 8885500759296 9406053469440 18291554228736 cost_7573_1628_join1_12 cost_7573_1628_join1_14 rfl rfl rfl

private theorem cost_7573_1628_join2_8 : P1_7_1_3.blockEstimate 7573 1628 5724 1024 = 18624639638016 :=
  @P1_7_1_3.block_append 7573 1628 5724 6236 512 512 1024 9489324821760 9135314816256 18624639638016 cost_7573_1628_join1_16 cost_7573_1628_join1_18 rfl rfl rfl

private theorem cost_7573_1628_join2_10 : P1_7_1_3.blockEstimate 7573 1628 6748 1024 = 15462477459842 :=
  @P1_7_1_3.block_append 7573 1628 6748 7260 512 512 1024 8344023452928 7118454006914 15462477459842 cost_7573_1628_join1_20 cost_7573_1628_join1_22 rfl rfl rfl

private theorem cost_7573_1628_join2_12 : P1_7_1_3.blockEstimate 7573 1628 7772 1024 = 9651428946764 :=
  @P1_7_1_3.block_append 7573 1628 7772 8284 512 512 1024 5599479883064 4051949063700 9651428946764 cost_7573_1628_join1_24 cost_7573_1628_join1_26 rfl rfl rfl

private theorem cost_7573_1628_join2_14 : P1_7_1_3.blockEstimate 7573 1628 8796 1024 = 4024771946407 :=
  @P1_7_1_3.block_append 7573 1628 8796 9308 512 512 1024 2617620999271 1407150947136 4024771946407 cost_7573_1628_join1_28 cost_7573_1628_join1_30 rfl rfl rfl

private theorem cost_7573_1628_join2_16 : P1_7_1_3.blockEstimate 7573 1628 9820 1009 = 610559900467 :=
  @P1_7_1_3.block_append 7573 1628 9820 10332 512 497 1009 534780918592 75778981875 610559900467 cost_7573_1628_join1_32 cost_7573_1628_join1_34 rfl rfl rfl

private theorem cost_7573_1628_join3_0 : P1_7_1_3.blockEstimate 7573 1628 1628 2048 = 8587120778535 :=
  @P1_7_1_3.block_append 7573 1628 1628 2652 1024 1024 2048 1221506899200 7365613879335 8587120778535 cost_7573_1628_join2_0 cost_7573_1628_join2_2 rfl rfl rfl

private theorem cost_7573_1628_join3_2 : P1_7_1_3.blockEstimate 7573 1628 3676 2048 = 32751772185600 :=
  @P1_7_1_3.block_append 7573 1628 3676 4700 1024 1024 2048 14460217956864 18291554228736 32751772185600 cost_7573_1628_join2_4 cost_7573_1628_join2_6 rfl rfl rfl

private theorem cost_7573_1628_join3_4 : P1_7_1_3.blockEstimate 7573 1628 5724 2048 = 34087117097858 :=
  @P1_7_1_3.block_append 7573 1628 5724 6748 1024 1024 2048 18624639638016 15462477459842 34087117097858 cost_7573_1628_join2_8 cost_7573_1628_join2_10 rfl rfl rfl

private theorem cost_7573_1628_join3_6 : P1_7_1_3.blockEstimate 7573 1628 7772 2048 = 13676200893171 :=
  @P1_7_1_3.block_append 7573 1628 7772 8796 1024 1024 2048 9651428946764 4024771946407 13676200893171 cost_7573_1628_join2_12 cost_7573_1628_join2_14 rfl rfl rfl

private theorem cost_7573_1628_join4_0 : P1_7_1_3.blockEstimate 7573 1628 1628 4096 = 41338892964135 :=
  @P1_7_1_3.block_append 7573 1628 1628 3676 2048 2048 4096 8587120778535 32751772185600 41338892964135 cost_7573_1628_join3_0 cost_7573_1628_join3_2 rfl rfl rfl

private theorem cost_7573_1628_join4_2 : P1_7_1_3.blockEstimate 7573 1628 5724 4096 = 47763317991029 :=
  @P1_7_1_3.block_append 7573 1628 5724 7772 2048 2048 4096 34087117097858 13676200893171 47763317991029 cost_7573_1628_join3_4 cost_7573_1628_join3_6 rfl rfl rfl

private theorem cost_7573_1628_join5_0 : P1_7_1_3.blockEstimate 7573 1628 1628 8192 = 89102210955164 :=
  @P1_7_1_3.block_append 7573 1628 1628 5724 4096 4096 8192 41338892964135 47763317991029 89102210955164 cost_7573_1628_join4_0 cost_7573_1628_join4_2 rfl rfl rfl

private theorem cost_7573_1628_join6_0 : P1_7_1_3.blockEstimate 7573 1628 1628 9201 = 89712770855631 :=
  @P1_7_1_3.block_append 7573 1628 1628 9820 8192 1009 9201 89102210955164 610559900467 89712770855631 cost_7573_1628_join5_0 cost_7573_1628_join2_16 rfl rfl rfl

private theorem cost_7573_1628_total : P1_7_1_3.momentEstimate 7573 1628 = 89712770855631 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 7573 + 1628 = 9201 by decide]
  exact cost_7573_1628_join6_0

theorem moment7573_1628 : P1_7_1.groupedPoleMoment 7573 1628 ≤ 89712770855631 :=
  (P1_7_1_3.grouped_bound 7573 1628).trans_eq cost_7573_1628_total
private theorem cost_9847_2145_block0 : P1_7_1_3.blockEstimate 9847 2145 2145 128 = 3488786080 := by decide +kernel

private theorem cost_9847_2145_block1 : P1_7_1_3.blockEstimate 9847 2145 2273 128 = 23827871392 := by decide +kernel

private theorem cost_9847_2145_block2 : P1_7_1_3.blockEstimate 9847 2145 2401 128 = 63606507168 := by decide +kernel

private theorem cost_9847_2145_block3 : P1_7_1_3.blockEstimate 9847 2145 2529 128 = 122019387040 := by decide +kernel

private theorem cost_9847_2145_block4 : P1_7_1_3.blockEstimate 9847 2145 2657 128 = 198261204640 := by decide +kernel

private theorem cost_9847_2145_block5 : P1_7_1_3.blockEstimate 9847 2145 2785 128 = 291526653600 := by decide +kernel

private theorem cost_9847_2145_block6 : P1_7_1_3.blockEstimate 9847 2145 2913 128 = 401010427552 := by decide +kernel

private theorem cost_9847_2145_block7 : P1_7_1_3.blockEstimate 9847 2145 3041 128 = 525907220128 := by decide +kernel

private theorem cost_9847_2145_block8 : P1_7_1_3.blockEstimate 9847 2145 3169 128 = 665411724960 := by decide +kernel

private theorem cost_9847_2145_block9 : P1_7_1_3.blockEstimate 9847 2145 3297 128 = 818718635680 := by decide +kernel

private theorem cost_9847_2145_block10 : P1_7_1_3.blockEstimate 9847 2145 3425 128 = 985022645920 := by decide +kernel

private theorem cost_9847_2145_block11 : P1_7_1_3.blockEstimate 9847 2145 3553 128 = 1163518449312 := by decide +kernel

private theorem cost_9847_2145_block12 : P1_7_1_3.blockEstimate 9847 2145 3681 128 = 1353400739488 := by decide +kernel

private theorem cost_9847_2145_block13 : P1_7_1_3.blockEstimate 9847 2145 3809 128 = 1553864210080 := by decide +kernel

private theorem cost_9847_2145_block14 : P1_7_1_3.blockEstimate 9847 2145 3937 128 = 1764103554720 := by decide +kernel

private theorem cost_9847_2145_block15 : P1_7_1_3.blockEstimate 9847 2145 4065 128 = 1983313467040 := by decide +kernel

private theorem cost_9847_2145_block16 : P1_7_1_3.blockEstimate 9847 2145 4193 128 = 2210650551592 := by decide +kernel

private theorem cost_9847_2145_block17 : P1_7_1_3.blockEstimate 9847 2145 4321 128 = 2440381687488 := by decide +kernel

private theorem cost_9847_2145_block18 : P1_7_1_3.blockEstimate 9847 2145 4449 128 = 2662294431424 := by decide +kernel

private theorem cost_9847_2145_block19 : P1_7_1_3.blockEstimate 9847 2145 4577 128 = 2875206198976 := by decide +kernel

private theorem cost_9847_2145_block20 : P1_7_1_3.blockEstimate 9847 2145 4705 128 = 3079116990144 := by decide +kernel

private theorem cost_9847_2145_block21 : P1_7_1_3.blockEstimate 9847 2145 4833 128 = 3274026804928 := by decide +kernel

private theorem cost_9847_2145_block22 : P1_7_1_3.blockEstimate 9847 2145 4961 128 = 3459935643328 := by decide +kernel

private theorem cost_9847_2145_block23 : P1_7_1_3.blockEstimate 9847 2145 5089 128 = 3636843505344 := by decide +kernel

private theorem cost_9847_2145_block24 : P1_7_1_3.blockEstimate 9847 2145 5217 128 = 3804750390976 := by decide +kernel

private theorem cost_9847_2145_block25 : P1_7_1_3.blockEstimate 9847 2145 5345 128 = 3963656300224 := by decide +kernel

private theorem cost_9847_2145_block26 : P1_7_1_3.blockEstimate 9847 2145 5473 128 = 4113561233088 := by decide +kernel

private theorem cost_9847_2145_block27 : P1_7_1_3.blockEstimate 9847 2145 5601 128 = 4254465189568 := by decide +kernel

private theorem cost_9847_2145_block28 : P1_7_1_3.blockEstimate 9847 2145 5729 128 = 4386368169664 := by decide +kernel

private theorem cost_9847_2145_block29 : P1_7_1_3.blockEstimate 9847 2145 5857 128 = 4509270173376 := by decide +kernel

private theorem cost_9847_2145_block30 : P1_7_1_3.blockEstimate 9847 2145 5985 128 = 4623171200704 := by decide +kernel

private theorem cost_9847_2145_block31 : P1_7_1_3.blockEstimate 9847 2145 6113 128 = 4728071251648 := by decide +kernel

private theorem cost_9847_2145_block32 : P1_7_1_3.blockEstimate 9847 2145 6241 128 = 4823970326208 := by decide +kernel

private theorem cost_9847_2145_block33 : P1_7_1_3.blockEstimate 9847 2145 6369 128 = 4910868424384 := by decide +kernel

private theorem cost_9847_2145_block34 : P1_7_1_3.blockEstimate 9847 2145 6497 128 = 4988765546176 := by decide +kernel

private theorem cost_9847_2145_block35 : P1_7_1_3.blockEstimate 9847 2145 6625 128 = 5057661691584 := by decide +kernel

private theorem cost_9847_2145_block36 : P1_7_1_3.blockEstimate 9847 2145 6753 128 = 5117556860608 := by decide +kernel

private theorem cost_9847_2145_block37 : P1_7_1_3.blockEstimate 9847 2145 6881 128 = 5168451053248 := by decide +kernel

private theorem cost_9847_2145_block38 : P1_7_1_3.blockEstimate 9847 2145 7009 128 = 5210344269504 := by decide +kernel

private theorem cost_9847_2145_block39 : P1_7_1_3.blockEstimate 9847 2145 7137 128 = 5243236509376 := by decide +kernel

private theorem cost_9847_2145_block40 : P1_7_1_3.blockEstimate 9847 2145 7265 128 = 5267127772864 := by decide +kernel

private theorem cost_9847_2145_block41 : P1_7_1_3.blockEstimate 9847 2145 7393 128 = 5282018059968 := by decide +kernel

private theorem cost_9847_2145_block42 : P1_7_1_3.blockEstimate 9847 2145 7521 128 = 5287907370688 := by decide +kernel

private theorem cost_9847_2145_block43 : P1_7_1_3.blockEstimate 9847 2145 7649 128 = 5284795705024 := by decide +kernel

private theorem cost_9847_2145_block44 : P1_7_1_3.blockEstimate 9847 2145 7777 128 = 5272683062976 := by decide +kernel

private theorem cost_9847_2145_block45 : P1_7_1_3.blockEstimate 9847 2145 7905 128 = 5251569444544 := by decide +kernel

private theorem cost_9847_2145_block46 : P1_7_1_3.blockEstimate 9847 2145 8033 128 = 5221454849728 := by decide +kernel

private theorem cost_9847_2145_block47 : P1_7_1_3.blockEstimate 9847 2145 8161 128 = 5182339278528 := by decide +kernel

private theorem cost_9847_2145_block48 : P1_7_1_3.blockEstimate 9847 2145 8289 128 = 5134222730944 := by decide +kernel

private theorem cost_9847_2145_block49 : P1_7_1_3.blockEstimate 9847 2145 8417 128 = 5077105206976 := by decide +kernel

private theorem cost_9847_2145_block50 : P1_7_1_3.blockEstimate 9847 2145 8545 128 = 5010986706624 := by decide +kernel

private theorem cost_9847_2145_block51 : P1_7_1_3.blockEstimate 9847 2145 8673 128 = 4935867229888 := by decide +kernel

private theorem cost_9847_2145_block52 : P1_7_1_3.blockEstimate 9847 2145 8801 128 = 4851746776768 := by decide +kernel

private theorem cost_9847_2145_block53 : P1_7_1_3.blockEstimate 9847 2145 8929 128 = 4758625347264 := by decide +kernel

private theorem cost_9847_2145_block54 : P1_7_1_3.blockEstimate 9847 2145 9057 128 = 4656502941376 := by decide +kernel

private theorem cost_9847_2145_block55 : P1_7_1_3.blockEstimate 9847 2145 9185 128 = 4545379559104 := by decide +kernel

private theorem cost_9847_2145_block56 : P1_7_1_3.blockEstimate 9847 2145 9313 128 = 4425255200448 := by decide +kernel

private theorem cost_9847_2145_block57 : P1_7_1_3.blockEstimate 9847 2145 9441 128 = 4296129865408 := by decide +kernel

private theorem cost_9847_2145_block58 : P1_7_1_3.blockEstimate 9847 2145 9569 128 = 4158003553984 := by decide +kernel

private theorem cost_9847_2145_block59 : P1_7_1_3.blockEstimate 9847 2145 9697 128 = 4010876266176 := by decide +kernel

private theorem cost_9847_2145_block60 : P1_7_1_3.blockEstimate 9847 2145 9825 128 = 3855319251091 := by decide +kernel

private theorem cost_9847_2145_block61 : P1_7_1_3.blockEstimate 9847 2145 9953 128 = 3695299725821 := by decide +kernel

private theorem cost_9847_2145_block62 : P1_7_1_3.blockEstimate 9847 2145 10081 128 = 3532893447062 := by decide +kernel

private theorem cost_9847_2145_block63 : P1_7_1_3.blockEstimate 9847 2145 10209 128 = 3368686949747 := by decide +kernel

private theorem cost_9847_2145_block64 : P1_7_1_3.blockEstimate 9847 2145 10337 128 = 3203250206777 := by decide +kernel

private theorem cost_9847_2145_block65 : P1_7_1_3.blockEstimate 9847 2145 10465 128 = 3037141181351 := by decide +kernel

private theorem cost_9847_2145_block66 : P1_7_1_3.blockEstimate 9847 2145 10593 128 = 2870905829358 := by decide +kernel

private theorem cost_9847_2145_block67 : P1_7_1_3.blockEstimate 9847 2145 10721 128 = 2705078096660 := by decide +kernel

private theorem cost_9847_2145_block68 : P1_7_1_3.blockEstimate 9847 2145 10849 128 = 2540179922720 := by decide +kernel

private theorem cost_9847_2145_block69 : P1_7_1_3.blockEstimate 9847 2145 10977 128 = 2376721238535 := by decide +kernel

private theorem cost_9847_2145_block70 : P1_7_1_3.blockEstimate 9847 2145 11105 128 = 2215199965128 := by decide +kernel

private theorem cost_9847_2145_block71 : P1_7_1_3.blockEstimate 9847 2145 11233 128 = 2056102017207 := by decide +kernel

private theorem cost_9847_2145_block72 : P1_7_1_3.blockEstimate 9847 2145 11361 128 = 1899901299433 := by decide +kernel

private theorem cost_9847_2145_block73 : P1_7_1_3.blockEstimate 9847 2145 11489 128 = 1747059709719 := by decide +kernel

private theorem cost_9847_2145_block74 : P1_7_1_3.blockEstimate 9847 2145 11617 128 = 1598027136840 := by decide +kernel

private theorem cost_9847_2145_block75 : P1_7_1_3.blockEstimate 9847 2145 11745 128 = 1453241461600 := by decide +kernel

private theorem cost_9847_2145_block76 : P1_7_1_3.blockEstimate 9847 2145 11873 128 = 1313122125626 := by decide +kernel

private theorem cost_9847_2145_block77 : P1_7_1_3.blockEstimate 9847 2145 12001 128 = 1176912052320 := by decide +kernel

private theorem cost_9847_2145_block78 : P1_7_1_3.blockEstimate 9847 2145 12129 128 = 1045823340640 := by decide +kernel

private theorem cost_9847_2145_block79 : P1_7_1_3.blockEstimate 9847 2145 12257 128 = 921236389984 := by decide +kernel

private theorem cost_9847_2145_block80 : P1_7_1_3.blockEstimate 9847 2145 12385 128 = 803402858592 := by decide +kernel

private theorem cost_9847_2145_block81 : P1_7_1_3.blockEstimate 9847 2145 12513 128 = 692574404704 := by decide +kernel

private theorem cost_9847_2145_block82 : P1_7_1_3.blockEstimate 9847 2145 12641 128 = 589002686560 := by decide +kernel

private theorem cost_9847_2145_block83 : P1_7_1_3.blockEstimate 9847 2145 12769 128 = 492939362400 := by decide +kernel

private theorem cost_9847_2145_block84 : P1_7_1_3.blockEstimate 9847 2145 12897 128 = 404636090464 := by decide +kernel

private theorem cost_9847_2145_block85 : P1_7_1_3.blockEstimate 9847 2145 13025 128 = 324344528992 := by decide +kernel

private theorem cost_9847_2145_block86 : P1_7_1_3.blockEstimate 9847 2145 13153 128 = 252316336224 := by decide +kernel

private theorem cost_9847_2145_block87 : P1_7_1_3.blockEstimate 9847 2145 13281 128 = 188803170400 := by decide +kernel

private theorem cost_9847_2145_block88 : P1_7_1_3.blockEstimate 9847 2145 13409 128 = 134056689760 := by decide +kernel

private theorem cost_9847_2145_block89 : P1_7_1_3.blockEstimate 9847 2145 13537 128 = 88328552544 := by decide +kernel

private theorem cost_9847_2145_block90 : P1_7_1_3.blockEstimate 9847 2145 13665 128 = 51870416992 := by decide +kernel

private theorem cost_9847_2145_block91 : P1_7_1_3.blockEstimate 9847 2145 13793 128 = 24933941344 := by decide +kernel

private theorem cost_9847_2145_block92 : P1_7_1_3.blockEstimate 9847 2145 13921 128 = 7770783840 := by decide +kernel

private theorem cost_9847_2145_block93 : P1_7_1_3.blockEstimate 9847 2145 14049 88 = 585737130 := by decide +kernel

private theorem cost_9847_2145_join0_0 : P1_7_1_3.blockEstimate 9847 2145 2145 256 = 27316657472 :=
  @P1_7_1_3.block_append 9847 2145 2145 2273 128 128 256 3488786080 23827871392 27316657472 cost_9847_2145_block0 cost_9847_2145_block1 rfl rfl rfl

private theorem cost_9847_2145_join0_2 : P1_7_1_3.blockEstimate 9847 2145 2401 256 = 185625894208 :=
  @P1_7_1_3.block_append 9847 2145 2401 2529 128 128 256 63606507168 122019387040 185625894208 cost_9847_2145_block2 cost_9847_2145_block3 rfl rfl rfl

private theorem cost_9847_2145_join0_4 : P1_7_1_3.blockEstimate 9847 2145 2657 256 = 489787858240 :=
  @P1_7_1_3.block_append 9847 2145 2657 2785 128 128 256 198261204640 291526653600 489787858240 cost_9847_2145_block4 cost_9847_2145_block5 rfl rfl rfl

private theorem cost_9847_2145_join0_6 : P1_7_1_3.blockEstimate 9847 2145 2913 256 = 926917647680 :=
  @P1_7_1_3.block_append 9847 2145 2913 3041 128 128 256 401010427552 525907220128 926917647680 cost_9847_2145_block6 cost_9847_2145_block7 rfl rfl rfl

private theorem cost_9847_2145_join0_8 : P1_7_1_3.blockEstimate 9847 2145 3169 256 = 1484130360640 :=
  @P1_7_1_3.block_append 9847 2145 3169 3297 128 128 256 665411724960 818718635680 1484130360640 cost_9847_2145_block8 cost_9847_2145_block9 rfl rfl rfl

private theorem cost_9847_2145_join0_10 : P1_7_1_3.blockEstimate 9847 2145 3425 256 = 2148541095232 :=
  @P1_7_1_3.block_append 9847 2145 3425 3553 128 128 256 985022645920 1163518449312 2148541095232 cost_9847_2145_block10 cost_9847_2145_block11 rfl rfl rfl

private theorem cost_9847_2145_join0_12 : P1_7_1_3.blockEstimate 9847 2145 3681 256 = 2907264949568 :=
  @P1_7_1_3.block_append 9847 2145 3681 3809 128 128 256 1353400739488 1553864210080 2907264949568 cost_9847_2145_block12 cost_9847_2145_block13 rfl rfl rfl

private theorem cost_9847_2145_join0_14 : P1_7_1_3.blockEstimate 9847 2145 3937 256 = 3747417021760 :=
  @P1_7_1_3.block_append 9847 2145 3937 4065 128 128 256 1764103554720 1983313467040 3747417021760 cost_9847_2145_block14 cost_9847_2145_block15 rfl rfl rfl

private theorem cost_9847_2145_join0_16 : P1_7_1_3.blockEstimate 9847 2145 4193 256 = 4651032239080 :=
  @P1_7_1_3.block_append 9847 2145 4193 4321 128 128 256 2210650551592 2440381687488 4651032239080 cost_9847_2145_block16 cost_9847_2145_block17 rfl rfl rfl

private theorem cost_9847_2145_join0_18 : P1_7_1_3.blockEstimate 9847 2145 4449 256 = 5537500630400 :=
  @P1_7_1_3.block_append 9847 2145 4449 4577 128 128 256 2662294431424 2875206198976 5537500630400 cost_9847_2145_block18 cost_9847_2145_block19 rfl rfl rfl

private theorem cost_9847_2145_join0_20 : P1_7_1_3.blockEstimate 9847 2145 4705 256 = 6353143795072 :=
  @P1_7_1_3.block_append 9847 2145 4705 4833 128 128 256 3079116990144 3274026804928 6353143795072 cost_9847_2145_block20 cost_9847_2145_block21 rfl rfl rfl

private theorem cost_9847_2145_join0_22 : P1_7_1_3.blockEstimate 9847 2145 4961 256 = 7096779148672 :=
  @P1_7_1_3.block_append 9847 2145 4961 5089 128 128 256 3459935643328 3636843505344 7096779148672 cost_9847_2145_block22 cost_9847_2145_block23 rfl rfl rfl

private theorem cost_9847_2145_join0_24 : P1_7_1_3.blockEstimate 9847 2145 5217 256 = 7768406691200 :=
  @P1_7_1_3.block_append 9847 2145 5217 5345 128 128 256 3804750390976 3963656300224 7768406691200 cost_9847_2145_block24 cost_9847_2145_block25 rfl rfl rfl

private theorem cost_9847_2145_join0_26 : P1_7_1_3.blockEstimate 9847 2145 5473 256 = 8368026422656 :=
  @P1_7_1_3.block_append 9847 2145 5473 5601 128 128 256 4113561233088 4254465189568 8368026422656 cost_9847_2145_block26 cost_9847_2145_block27 rfl rfl rfl

private theorem cost_9847_2145_join0_28 : P1_7_1_3.blockEstimate 9847 2145 5729 256 = 8895638343040 :=
  @P1_7_1_3.block_append 9847 2145 5729 5857 128 128 256 4386368169664 4509270173376 8895638343040 cost_9847_2145_block28 cost_9847_2145_block29 rfl rfl rfl

private theorem cost_9847_2145_join0_30 : P1_7_1_3.blockEstimate 9847 2145 5985 256 = 9351242452352 :=
  @P1_7_1_3.block_append 9847 2145 5985 6113 128 128 256 4623171200704 4728071251648 9351242452352 cost_9847_2145_block30 cost_9847_2145_block31 rfl rfl rfl

private theorem cost_9847_2145_join0_32 : P1_7_1_3.blockEstimate 9847 2145 6241 256 = 9734838750592 :=
  @P1_7_1_3.block_append 9847 2145 6241 6369 128 128 256 4823970326208 4910868424384 9734838750592 cost_9847_2145_block32 cost_9847_2145_block33 rfl rfl rfl

private theorem cost_9847_2145_join0_34 : P1_7_1_3.blockEstimate 9847 2145 6497 256 = 10046427237760 :=
  @P1_7_1_3.block_append 9847 2145 6497 6625 128 128 256 4988765546176 5057661691584 10046427237760 cost_9847_2145_block34 cost_9847_2145_block35 rfl rfl rfl

private theorem cost_9847_2145_join0_36 : P1_7_1_3.blockEstimate 9847 2145 6753 256 = 10286007913856 :=
  @P1_7_1_3.block_append 9847 2145 6753 6881 128 128 256 5117556860608 5168451053248 10286007913856 cost_9847_2145_block36 cost_9847_2145_block37 rfl rfl rfl

private theorem cost_9847_2145_join0_38 : P1_7_1_3.blockEstimate 9847 2145 7009 256 = 10453580778880 :=
  @P1_7_1_3.block_append 9847 2145 7009 7137 128 128 256 5210344269504 5243236509376 10453580778880 cost_9847_2145_block38 cost_9847_2145_block39 rfl rfl rfl

private theorem cost_9847_2145_join0_40 : P1_7_1_3.blockEstimate 9847 2145 7265 256 = 10549145832832 :=
  @P1_7_1_3.block_append 9847 2145 7265 7393 128 128 256 5267127772864 5282018059968 10549145832832 cost_9847_2145_block40 cost_9847_2145_block41 rfl rfl rfl

private theorem cost_9847_2145_join0_42 : P1_7_1_3.blockEstimate 9847 2145 7521 256 = 10572703075712 :=
  @P1_7_1_3.block_append 9847 2145 7521 7649 128 128 256 5287907370688 5284795705024 10572703075712 cost_9847_2145_block42 cost_9847_2145_block43 rfl rfl rfl

private theorem cost_9847_2145_join0_44 : P1_7_1_3.blockEstimate 9847 2145 7777 256 = 10524252507520 :=
  @P1_7_1_3.block_append 9847 2145 7777 7905 128 128 256 5272683062976 5251569444544 10524252507520 cost_9847_2145_block44 cost_9847_2145_block45 rfl rfl rfl

private theorem cost_9847_2145_join0_46 : P1_7_1_3.blockEstimate 9847 2145 8033 256 = 10403794128256 :=
  @P1_7_1_3.block_append 9847 2145 8033 8161 128 128 256 5221454849728 5182339278528 10403794128256 cost_9847_2145_block46 cost_9847_2145_block47 rfl rfl rfl

private theorem cost_9847_2145_join0_48 : P1_7_1_3.blockEstimate 9847 2145 8289 256 = 10211327937920 :=
  @P1_7_1_3.block_append 9847 2145 8289 8417 128 128 256 5134222730944 5077105206976 10211327937920 cost_9847_2145_block48 cost_9847_2145_block49 rfl rfl rfl

private theorem cost_9847_2145_join0_50 : P1_7_1_3.blockEstimate 9847 2145 8545 256 = 9946853936512 :=
  @P1_7_1_3.block_append 9847 2145 8545 8673 128 128 256 5010986706624 4935867229888 9946853936512 cost_9847_2145_block50 cost_9847_2145_block51 rfl rfl rfl

private theorem cost_9847_2145_join0_52 : P1_7_1_3.blockEstimate 9847 2145 8801 256 = 9610372124032 :=
  @P1_7_1_3.block_append 9847 2145 8801 8929 128 128 256 4851746776768 4758625347264 9610372124032 cost_9847_2145_block52 cost_9847_2145_block53 rfl rfl rfl

private theorem cost_9847_2145_join0_54 : P1_7_1_3.blockEstimate 9847 2145 9057 256 = 9201882500480 :=
  @P1_7_1_3.block_append 9847 2145 9057 9185 128 128 256 4656502941376 4545379559104 9201882500480 cost_9847_2145_block54 cost_9847_2145_block55 rfl rfl rfl

private theorem cost_9847_2145_join0_56 : P1_7_1_3.blockEstimate 9847 2145 9313 256 = 8721385065856 :=
  @P1_7_1_3.block_append 9847 2145 9313 9441 128 128 256 4425255200448 4296129865408 8721385065856 cost_9847_2145_block56 cost_9847_2145_block57 rfl rfl rfl

private theorem cost_9847_2145_join0_58 : P1_7_1_3.blockEstimate 9847 2145 9569 256 = 8168879820160 :=
  @P1_7_1_3.block_append 9847 2145 9569 9697 128 128 256 4158003553984 4010876266176 8168879820160 cost_9847_2145_block58 cost_9847_2145_block59 rfl rfl rfl

private theorem cost_9847_2145_join0_60 : P1_7_1_3.blockEstimate 9847 2145 9825 256 = 7550618976912 :=
  @P1_7_1_3.block_append 9847 2145 9825 9953 128 128 256 3855319251091 3695299725821 7550618976912 cost_9847_2145_block60 cost_9847_2145_block61 rfl rfl rfl

private theorem cost_9847_2145_join0_62 : P1_7_1_3.blockEstimate 9847 2145 10081 256 = 6901580396809 :=
  @P1_7_1_3.block_append 9847 2145 10081 10209 128 128 256 3532893447062 3368686949747 6901580396809 cost_9847_2145_block62 cost_9847_2145_block63 rfl rfl rfl

private theorem cost_9847_2145_join0_64 : P1_7_1_3.blockEstimate 9847 2145 10337 256 = 6240391388128 :=
  @P1_7_1_3.block_append 9847 2145 10337 10465 128 128 256 3203250206777 3037141181351 6240391388128 cost_9847_2145_block64 cost_9847_2145_block65 rfl rfl rfl

private theorem cost_9847_2145_join0_66 : P1_7_1_3.blockEstimate 9847 2145 10593 256 = 5575983926018 :=
  @P1_7_1_3.block_append 9847 2145 10593 10721 128 128 256 2870905829358 2705078096660 5575983926018 cost_9847_2145_block66 cost_9847_2145_block67 rfl rfl rfl

private theorem cost_9847_2145_join0_68 : P1_7_1_3.blockEstimate 9847 2145 10849 256 = 4916901161255 :=
  @P1_7_1_3.block_append 9847 2145 10849 10977 128 128 256 2540179922720 2376721238535 4916901161255 cost_9847_2145_block68 cost_9847_2145_block69 rfl rfl rfl

private theorem cost_9847_2145_join0_70 : P1_7_1_3.blockEstimate 9847 2145 11105 256 = 4271301982335 :=
  @P1_7_1_3.block_append 9847 2145 11105 11233 128 128 256 2215199965128 2056102017207 4271301982335 cost_9847_2145_block70 cost_9847_2145_block71 rfl rfl rfl

private theorem cost_9847_2145_join0_72 : P1_7_1_3.blockEstimate 9847 2145 11361 256 = 3646961009152 :=
  @P1_7_1_3.block_append 9847 2145 11361 11489 128 128 256 1899901299433 1747059709719 3646961009152 cost_9847_2145_block72 cost_9847_2145_block73 rfl rfl rfl

private theorem cost_9847_2145_join0_74 : P1_7_1_3.blockEstimate 9847 2145 11617 256 = 3051268598440 :=
  @P1_7_1_3.block_append 9847 2145 11617 11745 128 128 256 1598027136840 1453241461600 3051268598440 cost_9847_2145_block74 cost_9847_2145_block75 rfl rfl rfl

private theorem cost_9847_2145_join0_76 : P1_7_1_3.blockEstimate 9847 2145 11873 256 = 2490034177946 :=
  @P1_7_1_3.block_append 9847 2145 11873 12001 128 128 256 1313122125626 1176912052320 2490034177946 cost_9847_2145_block76 cost_9847_2145_block77 rfl rfl rfl

private theorem cost_9847_2145_join0_78 : P1_7_1_3.blockEstimate 9847 2145 12129 256 = 1967059730624 :=
  @P1_7_1_3.block_append 9847 2145 12129 12257 128 128 256 1045823340640 921236389984 1967059730624 cost_9847_2145_block78 cost_9847_2145_block79 rfl rfl rfl

private theorem cost_9847_2145_join0_80 : P1_7_1_3.blockEstimate 9847 2145 12385 256 = 1495977263296 :=
  @P1_7_1_3.block_append 9847 2145 12385 12513 128 128 256 803402858592 692574404704 1495977263296 cost_9847_2145_block80 cost_9847_2145_block81 rfl rfl rfl

private theorem cost_9847_2145_join0_82 : P1_7_1_3.blockEstimate 9847 2145 12641 256 = 1081942048960 :=
  @P1_7_1_3.block_append 9847 2145 12641 12769 128 128 256 589002686560 492939362400 1081942048960 cost_9847_2145_block82 cost_9847_2145_block83 rfl rfl rfl

private theorem cost_9847_2145_join0_84 : P1_7_1_3.blockEstimate 9847 2145 12897 256 = 728980619456 :=
  @P1_7_1_3.block_append 9847 2145 12897 13025 128 128 256 404636090464 324344528992 728980619456 cost_9847_2145_block84 cost_9847_2145_block85 rfl rfl rfl

private theorem cost_9847_2145_join0_86 : P1_7_1_3.blockEstimate 9847 2145 13153 256 = 441119506624 :=
  @P1_7_1_3.block_append 9847 2145 13153 13281 128 128 256 252316336224 188803170400 441119506624 cost_9847_2145_block86 cost_9847_2145_block87 rfl rfl rfl

private theorem cost_9847_2145_join0_88 : P1_7_1_3.blockEstimate 9847 2145 13409 256 = 222385242304 :=
  @P1_7_1_3.block_append 9847 2145 13409 13537 128 128 256 134056689760 88328552544 222385242304 cost_9847_2145_block88 cost_9847_2145_block89 rfl rfl rfl

private theorem cost_9847_2145_join0_90 : P1_7_1_3.blockEstimate 9847 2145 13665 256 = 76804358336 :=
  @P1_7_1_3.block_append 9847 2145 13665 13793 128 128 256 51870416992 24933941344 76804358336 cost_9847_2145_block90 cost_9847_2145_block91 rfl rfl rfl

private theorem cost_9847_2145_join0_92 : P1_7_1_3.blockEstimate 9847 2145 13921 216 = 8356520970 :=
  @P1_7_1_3.block_append 9847 2145 13921 14049 128 88 216 7770783840 585737130 8356520970 cost_9847_2145_block92 cost_9847_2145_block93 rfl rfl rfl

private theorem cost_9847_2145_join1_0 : P1_7_1_3.blockEstimate 9847 2145 2145 512 = 212942551680 :=
  @P1_7_1_3.block_append 9847 2145 2145 2401 256 256 512 27316657472 185625894208 212942551680 cost_9847_2145_join0_0 cost_9847_2145_join0_2 rfl rfl rfl

private theorem cost_9847_2145_join1_2 : P1_7_1_3.blockEstimate 9847 2145 2657 512 = 1416705505920 :=
  @P1_7_1_3.block_append 9847 2145 2657 2913 256 256 512 489787858240 926917647680 1416705505920 cost_9847_2145_join0_4 cost_9847_2145_join0_6 rfl rfl rfl

private theorem cost_9847_2145_join1_4 : P1_7_1_3.blockEstimate 9847 2145 3169 512 = 3632671455872 :=
  @P1_7_1_3.block_append 9847 2145 3169 3425 256 256 512 1484130360640 2148541095232 3632671455872 cost_9847_2145_join0_8 cost_9847_2145_join0_10 rfl rfl rfl

private theorem cost_9847_2145_join1_6 : P1_7_1_3.blockEstimate 9847 2145 3681 512 = 6654681971328 :=
  @P1_7_1_3.block_append 9847 2145 3681 3937 256 256 512 2907264949568 3747417021760 6654681971328 cost_9847_2145_join0_12 cost_9847_2145_join0_14 rfl rfl rfl

private theorem cost_9847_2145_join1_8 : P1_7_1_3.blockEstimate 9847 2145 4193 512 = 10188532869480 :=
  @P1_7_1_3.block_append 9847 2145 4193 4449 256 256 512 4651032239080 5537500630400 10188532869480 cost_9847_2145_join0_16 cost_9847_2145_join0_18 rfl rfl rfl

private theorem cost_9847_2145_join1_10 : P1_7_1_3.blockEstimate 9847 2145 4705 512 = 13449922943744 :=
  @P1_7_1_3.block_append 9847 2145 4705 4961 256 256 512 6353143795072 7096779148672 13449922943744 cost_9847_2145_join0_20 cost_9847_2145_join0_22 rfl rfl rfl

private theorem cost_9847_2145_join1_12 : P1_7_1_3.blockEstimate 9847 2145 5217 512 = 16136433113856 :=
  @P1_7_1_3.block_append 9847 2145 5217 5473 256 256 512 7768406691200 8368026422656 16136433113856 cost_9847_2145_join0_24 cost_9847_2145_join0_26 rfl rfl rfl

private theorem cost_9847_2145_join1_14 : P1_7_1_3.blockEstimate 9847 2145 5729 512 = 18246880795392 :=
  @P1_7_1_3.block_append 9847 2145 5729 5985 256 256 512 8895638343040 9351242452352 18246880795392 cost_9847_2145_join0_28 cost_9847_2145_join0_30 rfl rfl rfl

private theorem cost_9847_2145_join1_16 : P1_7_1_3.blockEstimate 9847 2145 6241 512 = 19781265988352 :=
  @P1_7_1_3.block_append 9847 2145 6241 6497 256 256 512 9734838750592 10046427237760 19781265988352 cost_9847_2145_join0_32 cost_9847_2145_join0_34 rfl rfl rfl

private theorem cost_9847_2145_join1_18 : P1_7_1_3.blockEstimate 9847 2145 6753 512 = 20739588692736 :=
  @P1_7_1_3.block_append 9847 2145 6753 7009 256 256 512 10286007913856 10453580778880 20739588692736 cost_9847_2145_join0_36 cost_9847_2145_join0_38 rfl rfl rfl

private theorem cost_9847_2145_join1_20 : P1_7_1_3.blockEstimate 9847 2145 7265 512 = 21121848908544 :=
  @P1_7_1_3.block_append 9847 2145 7265 7521 256 256 512 10549145832832 10572703075712 21121848908544 cost_9847_2145_join0_40 cost_9847_2145_join0_42 rfl rfl rfl

private theorem cost_9847_2145_join1_22 : P1_7_1_3.blockEstimate 9847 2145 7777 512 = 20928046635776 :=
  @P1_7_1_3.block_append 9847 2145 7777 8033 256 256 512 10524252507520 10403794128256 20928046635776 cost_9847_2145_join0_44 cost_9847_2145_join0_46 rfl rfl rfl

private theorem cost_9847_2145_join1_24 : P1_7_1_3.blockEstimate 9847 2145 8289 512 = 20158181874432 :=
  @P1_7_1_3.block_append 9847 2145 8289 8545 256 256 512 10211327937920 9946853936512 20158181874432 cost_9847_2145_join0_48 cost_9847_2145_join0_50 rfl rfl rfl

private theorem cost_9847_2145_join1_26 : P1_7_1_3.blockEstimate 9847 2145 8801 512 = 18812254624512 :=
  @P1_7_1_3.block_append 9847 2145 8801 9057 256 256 512 9610372124032 9201882500480 18812254624512 cost_9847_2145_join0_52 cost_9847_2145_join0_54 rfl rfl rfl

private theorem cost_9847_2145_join1_28 : P1_7_1_3.blockEstimate 9847 2145 9313 512 = 16890264886016 :=
  @P1_7_1_3.block_append 9847 2145 9313 9569 256 256 512 8721385065856 8168879820160 16890264886016 cost_9847_2145_join0_56 cost_9847_2145_join0_58 rfl rfl rfl

private theorem cost_9847_2145_join1_30 : P1_7_1_3.blockEstimate 9847 2145 9825 512 = 14452199373721 :=
  @P1_7_1_3.block_append 9847 2145 9825 10081 256 256 512 7550618976912 6901580396809 14452199373721 cost_9847_2145_join0_60 cost_9847_2145_join0_62 rfl rfl rfl

private theorem cost_9847_2145_join1_32 : P1_7_1_3.blockEstimate 9847 2145 10337 512 = 11816375314146 :=
  @P1_7_1_3.block_append 9847 2145 10337 10593 256 256 512 6240391388128 5575983926018 11816375314146 cost_9847_2145_join0_64 cost_9847_2145_join0_66 rfl rfl rfl

private theorem cost_9847_2145_join1_34 : P1_7_1_3.blockEstimate 9847 2145 10849 512 = 9188203143590 :=
  @P1_7_1_3.block_append 9847 2145 10849 11105 256 256 512 4916901161255 4271301982335 9188203143590 cost_9847_2145_join0_68 cost_9847_2145_join0_70 rfl rfl rfl

private theorem cost_9847_2145_join1_36 : P1_7_1_3.blockEstimate 9847 2145 11361 512 = 6698229607592 :=
  @P1_7_1_3.block_append 9847 2145 11361 11617 256 256 512 3646961009152 3051268598440 6698229607592 cost_9847_2145_join0_72 cost_9847_2145_join0_74 rfl rfl rfl

private theorem cost_9847_2145_join1_38 : P1_7_1_3.blockEstimate 9847 2145 11873 512 = 4457093908570 :=
  @P1_7_1_3.block_append 9847 2145 11873 12129 256 256 512 2490034177946 1967059730624 4457093908570 cost_9847_2145_join0_76 cost_9847_2145_join0_78 rfl rfl rfl

private theorem cost_9847_2145_join1_40 : P1_7_1_3.blockEstimate 9847 2145 12385 512 = 2577919312256 :=
  @P1_7_1_3.block_append 9847 2145 12385 12641 256 256 512 1495977263296 1081942048960 2577919312256 cost_9847_2145_join0_80 cost_9847_2145_join0_82 rfl rfl rfl

private theorem cost_9847_2145_join1_42 : P1_7_1_3.blockEstimate 9847 2145 12897 512 = 1170100126080 :=
  @P1_7_1_3.block_append 9847 2145 12897 13153 256 256 512 728980619456 441119506624 1170100126080 cost_9847_2145_join0_84 cost_9847_2145_join0_86 rfl rfl rfl

private theorem cost_9847_2145_join1_44 : P1_7_1_3.blockEstimate 9847 2145 13409 512 = 299189600640 :=
  @P1_7_1_3.block_append 9847 2145 13409 13665 256 256 512 222385242304 76804358336 299189600640 cost_9847_2145_join0_88 cost_9847_2145_join0_90 rfl rfl rfl

private theorem cost_9847_2145_join2_0 : P1_7_1_3.blockEstimate 9847 2145 2145 1024 = 1629648057600 :=
  @P1_7_1_3.block_append 9847 2145 2145 2657 512 512 1024 212942551680 1416705505920 1629648057600 cost_9847_2145_join1_0 cost_9847_2145_join1_2 rfl rfl rfl

private theorem cost_9847_2145_join2_2 : P1_7_1_3.blockEstimate 9847 2145 3169 1024 = 10287353427200 :=
  @P1_7_1_3.block_append 9847 2145 3169 3681 512 512 1024 3632671455872 6654681971328 10287353427200 cost_9847_2145_join1_4 cost_9847_2145_join1_6 rfl rfl rfl

private theorem cost_9847_2145_join2_4 : P1_7_1_3.blockEstimate 9847 2145 4193 1024 = 23638455813224 :=
  @P1_7_1_3.block_append 9847 2145 4193 4705 512 512 1024 10188532869480 13449922943744 23638455813224 cost_9847_2145_join1_8 cost_9847_2145_join1_10 rfl rfl rfl

private theorem cost_9847_2145_join2_6 : P1_7_1_3.blockEstimate 9847 2145 5217 1024 = 34383313909248 :=
  @P1_7_1_3.block_append 9847 2145 5217 5729 512 512 1024 16136433113856 18246880795392 34383313909248 cost_9847_2145_join1_12 cost_9847_2145_join1_14 rfl rfl rfl

private theorem cost_9847_2145_join2_8 : P1_7_1_3.blockEstimate 9847 2145 6241 1024 = 40520854681088 :=
  @P1_7_1_3.block_append 9847 2145 6241 6753 512 512 1024 19781265988352 20739588692736 40520854681088 cost_9847_2145_join1_16 cost_9847_2145_join1_18 rfl rfl rfl

private theorem cost_9847_2145_join2_10 : P1_7_1_3.blockEstimate 9847 2145 7265 1024 = 42049895544320 :=
  @P1_7_1_3.block_append 9847 2145 7265 7777 512 512 1024 21121848908544 20928046635776 42049895544320 cost_9847_2145_join1_20 cost_9847_2145_join1_22 rfl rfl rfl

private theorem cost_9847_2145_join2_12 : P1_7_1_3.blockEstimate 9847 2145 8289 1024 = 38970436498944 :=
  @P1_7_1_3.block_append 9847 2145 8289 8801 512 512 1024 20158181874432 18812254624512 38970436498944 cost_9847_2145_join1_24 cost_9847_2145_join1_26 rfl rfl rfl

private theorem cost_9847_2145_join2_14 : P1_7_1_3.blockEstimate 9847 2145 9313 1024 = 31342464259737 :=
  @P1_7_1_3.block_append 9847 2145 9313 9825 512 512 1024 16890264886016 14452199373721 31342464259737 cost_9847_2145_join1_28 cost_9847_2145_join1_30 rfl rfl rfl

private theorem cost_9847_2145_join2_16 : P1_7_1_3.blockEstimate 9847 2145 10337 1024 = 21004578457736 :=
  @P1_7_1_3.block_append 9847 2145 10337 10849 512 512 1024 11816375314146 9188203143590 21004578457736 cost_9847_2145_join1_32 cost_9847_2145_join1_34 rfl rfl rfl

private theorem cost_9847_2145_join2_18 : P1_7_1_3.blockEstimate 9847 2145 11361 1024 = 11155323516162 :=
  @P1_7_1_3.block_append 9847 2145 11361 11873 512 512 1024 6698229607592 4457093908570 11155323516162 cost_9847_2145_join1_36 cost_9847_2145_join1_38 rfl rfl rfl

private theorem cost_9847_2145_join2_20 : P1_7_1_3.blockEstimate 9847 2145 12385 1024 = 3748019438336 :=
  @P1_7_1_3.block_append 9847 2145 12385 12897 512 512 1024 2577919312256 1170100126080 3748019438336 cost_9847_2145_join1_40 cost_9847_2145_join1_42 rfl rfl rfl

private theorem cost_9847_2145_join2_22 : P1_7_1_3.blockEstimate 9847 2145 13409 728 = 307546121610 :=
  @P1_7_1_3.block_append 9847 2145 13409 13921 512 216 728 299189600640 8356520970 307546121610 cost_9847_2145_join1_44 cost_9847_2145_join0_92 rfl rfl rfl

private theorem cost_9847_2145_join3_0 : P1_7_1_3.blockEstimate 9847 2145 2145 2048 = 11917001484800 :=
  @P1_7_1_3.block_append 9847 2145 2145 3169 1024 1024 2048 1629648057600 10287353427200 11917001484800 cost_9847_2145_join2_0 cost_9847_2145_join2_2 rfl rfl rfl

private theorem cost_9847_2145_join3_2 : P1_7_1_3.blockEstimate 9847 2145 4193 2048 = 58021769722472 :=
  @P1_7_1_3.block_append 9847 2145 4193 5217 1024 1024 2048 23638455813224 34383313909248 58021769722472 cost_9847_2145_join2_4 cost_9847_2145_join2_6 rfl rfl rfl

private theorem cost_9847_2145_join3_4 : P1_7_1_3.blockEstimate 9847 2145 6241 2048 = 82570750225408 :=
  @P1_7_1_3.block_append 9847 2145 6241 7265 1024 1024 2048 40520854681088 42049895544320 82570750225408 cost_9847_2145_join2_8 cost_9847_2145_join2_10 rfl rfl rfl

private theorem cost_9847_2145_join3_6 : P1_7_1_3.blockEstimate 9847 2145 8289 2048 = 70312900758681 :=
  @P1_7_1_3.block_append 9847 2145 8289 9313 1024 1024 2048 38970436498944 31342464259737 70312900758681 cost_9847_2145_join2_12 cost_9847_2145_join2_14 rfl rfl rfl

private theorem cost_9847_2145_join3_8 : P1_7_1_3.blockEstimate 9847 2145 10337 2048 = 32159901973898 :=
  @P1_7_1_3.block_append 9847 2145 10337 11361 1024 1024 2048 21004578457736 11155323516162 32159901973898 cost_9847_2145_join2_16 cost_9847_2145_join2_18 rfl rfl rfl

private theorem cost_9847_2145_join3_10 : P1_7_1_3.blockEstimate 9847 2145 12385 1752 = 4055565559946 :=
  @P1_7_1_3.block_append 9847 2145 12385 13409 1024 728 1752 3748019438336 307546121610 4055565559946 cost_9847_2145_join2_20 cost_9847_2145_join2_22 rfl rfl rfl

private theorem cost_9847_2145_join4_0 : P1_7_1_3.blockEstimate 9847 2145 2145 4096 = 69938771207272 :=
  @P1_7_1_3.block_append 9847 2145 2145 4193 2048 2048 4096 11917001484800 58021769722472 69938771207272 cost_9847_2145_join3_0 cost_9847_2145_join3_2 rfl rfl rfl

private theorem cost_9847_2145_join4_2 : P1_7_1_3.blockEstimate 9847 2145 6241 4096 = 152883650984089 :=
  @P1_7_1_3.block_append 9847 2145 6241 8289 2048 2048 4096 82570750225408 70312900758681 152883650984089 cost_9847_2145_join3_4 cost_9847_2145_join3_6 rfl rfl rfl

private theorem cost_9847_2145_join4_4 : P1_7_1_3.blockEstimate 9847 2145 10337 3800 = 36215467533844 :=
  @P1_7_1_3.block_append 9847 2145 10337 12385 2048 1752 3800 32159901973898 4055565559946 36215467533844 cost_9847_2145_join3_8 cost_9847_2145_join3_10 rfl rfl rfl

private theorem cost_9847_2145_join5_0 : P1_7_1_3.blockEstimate 9847 2145 2145 8192 = 222822422191361 :=
  @P1_7_1_3.block_append 9847 2145 2145 6241 4096 4096 8192 69938771207272 152883650984089 222822422191361 cost_9847_2145_join4_0 cost_9847_2145_join4_2 rfl rfl rfl

private theorem cost_9847_2145_join6_0 : P1_7_1_3.blockEstimate 9847 2145 2145 11992 = 259037889725205 :=
  @P1_7_1_3.block_append 9847 2145 2145 10337 8192 3800 11992 222822422191361 36215467533844 259037889725205 cost_9847_2145_join5_0 cost_9847_2145_join4_4 rfl rfl rfl

private theorem cost_9847_2145_total : P1_7_1_3.momentEstimate 9847 2145 = 259037889725205 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 9847 + 2145 = 11992 by decide]
  exact cost_9847_2145_join6_0

theorem moment9847_2145 : P1_7_1.groupedPoleMoment 9847 2145 ≤ 259037889725205 :=
  (P1_7_1_3.grouped_bound 9847 2145).trans_eq cost_9847_2145_total

end Research6966.HelperRescueCatalogue

end Merged6967_Near6967RescueMoment29

section Merged6967_Near6967RescueMoment7
set_option Elab.async false


set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private theorem cost_776_170_block0 : P1_7_1_3.blockEstimate 776 170 170 128 = 243545120 := by decide +kernel

private theorem cost_776_170_block1 : P1_7_1_3.blockEstimate 776 170 298 128 = 1353296086 := by decide +kernel

private theorem cost_776_170_block2 : P1_7_1_3.blockEstimate 776 170 426 128 = 2323203264 := by decide +kernel

private theorem cost_776_170_block3 : P1_7_1_3.blockEstimate 776 170 554 128 = 2583758016 := by decide +kernel

private theorem cost_776_170_block4 : P1_7_1_3.blockEstimate 776 170 682 128 = 2128705328 := by decide +kernel

private theorem cost_776_170_block5 : P1_7_1_3.blockEstimate 776 170 810 128 = 1168512808 := by decide +kernel

private theorem cost_776_170_block6 : P1_7_1_3.blockEstimate 776 170 938 128 = 325495649 := by decide +kernel

private theorem cost_776_170_block7 : P1_7_1_3.blockEstimate 776 170 1066 50 = 8567897 := by decide +kernel

private theorem cost_776_170_join0_0 : P1_7_1_3.blockEstimate 776 170 170 256 = 1596841206 :=
  @P1_7_1_3.block_append 776 170 170 298 128 128 256 243545120 1353296086 1596841206 cost_776_170_block0 cost_776_170_block1 rfl rfl rfl

private theorem cost_776_170_join0_2 : P1_7_1_3.blockEstimate 776 170 426 256 = 4906961280 :=
  @P1_7_1_3.block_append 776 170 426 554 128 128 256 2323203264 2583758016 4906961280 cost_776_170_block2 cost_776_170_block3 rfl rfl rfl

private theorem cost_776_170_join0_4 : P1_7_1_3.blockEstimate 776 170 682 256 = 3297218136 :=
  @P1_7_1_3.block_append 776 170 682 810 128 128 256 2128705328 1168512808 3297218136 cost_776_170_block4 cost_776_170_block5 rfl rfl rfl

private theorem cost_776_170_join0_6 : P1_7_1_3.blockEstimate 776 170 938 178 = 334063546 :=
  @P1_7_1_3.block_append 776 170 938 1066 128 50 178 325495649 8567897 334063546 cost_776_170_block6 cost_776_170_block7 rfl rfl rfl

private theorem cost_776_170_join1_0 : P1_7_1_3.blockEstimate 776 170 170 512 = 6503802486 :=
  @P1_7_1_3.block_append 776 170 170 426 256 256 512 1596841206 4906961280 6503802486 cost_776_170_join0_0 cost_776_170_join0_2 rfl rfl rfl

private theorem cost_776_170_join1_2 : P1_7_1_3.blockEstimate 776 170 682 434 = 3631281682 :=
  @P1_7_1_3.block_append 776 170 682 938 256 178 434 3297218136 334063546 3631281682 cost_776_170_join0_4 cost_776_170_join0_6 rfl rfl rfl

private theorem cost_776_170_join2_0 : P1_7_1_3.blockEstimate 776 170 170 946 = 10135084168 :=
  @P1_7_1_3.block_append 776 170 170 682 512 434 946 6503802486 3631281682 10135084168 cost_776_170_join1_0 cost_776_170_join1_2 rfl rfl rfl

private theorem cost_776_170_total : P1_7_1_3.momentEstimate 776 170 = 10135084168 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 776 + 170 = 946 by decide]
  exact cost_776_170_join2_0

theorem moment776_170 : P1_7_1.groupedPoleMoment 776 170 ≤ 10135084168 :=
  (P1_7_1_3.grouped_bound 776 170).trans_eq cost_776_170_total
private theorem cost_776_172_block0 : P1_7_1_3.blockEstimate 776 172 172 128 = 243545120 := by decide +kernel

private theorem cost_776_172_block1 : P1_7_1_3.blockEstimate 776 172 300 128 = 1357261421 := by decide +kernel

private theorem cost_776_172_block2 : P1_7_1_3.blockEstimate 776 172 428 128 = 2340266496 := by decide +kernel

private theorem cost_776_172_block3 : P1_7_1_3.blockEstimate 776 172 556 128 = 2606703104 := by decide +kernel

private theorem cost_776_172_block4 : P1_7_1_3.blockEstimate 776 172 684 128 = 2149434819 := by decide +kernel

private theorem cost_776_172_block5 : P1_7_1_3.blockEstimate 776 172 812 128 = 1185169515 := by decide +kernel

private theorem cost_776_172_block6 : P1_7_1_3.blockEstimate 776 172 940 128 = 335294674 := by decide +kernel

private theorem cost_776_172_block7 : P1_7_1_3.blockEstimate 776 172 1068 52 = 9593883 := by decide +kernel

private theorem cost_776_172_join0_0 : P1_7_1_3.blockEstimate 776 172 172 256 = 1600806541 :=
  @P1_7_1_3.block_append 776 172 172 300 128 128 256 243545120 1357261421 1600806541 cost_776_172_block0 cost_776_172_block1 rfl rfl rfl

private theorem cost_776_172_join0_2 : P1_7_1_3.blockEstimate 776 172 428 256 = 4946969600 :=
  @P1_7_1_3.block_append 776 172 428 556 128 128 256 2340266496 2606703104 4946969600 cost_776_172_block2 cost_776_172_block3 rfl rfl rfl

private theorem cost_776_172_join0_4 : P1_7_1_3.blockEstimate 776 172 684 256 = 3334604334 :=
  @P1_7_1_3.block_append 776 172 684 812 128 128 256 2149434819 1185169515 3334604334 cost_776_172_block4 cost_776_172_block5 rfl rfl rfl

private theorem cost_776_172_join0_6 : P1_7_1_3.blockEstimate 776 172 940 180 = 344888557 :=
  @P1_7_1_3.block_append 776 172 940 1068 128 52 180 335294674 9593883 344888557 cost_776_172_block6 cost_776_172_block7 rfl rfl rfl

private theorem cost_776_172_join1_0 : P1_7_1_3.blockEstimate 776 172 172 512 = 6547776141 :=
  @P1_7_1_3.block_append 776 172 172 428 256 256 512 1600806541 4946969600 6547776141 cost_776_172_join0_0 cost_776_172_join0_2 rfl rfl rfl

private theorem cost_776_172_join1_2 : P1_7_1_3.blockEstimate 776 172 684 436 = 3679492891 :=
  @P1_7_1_3.block_append 776 172 684 940 256 180 436 3334604334 344888557 3679492891 cost_776_172_join0_4 cost_776_172_join0_6 rfl rfl rfl

private theorem cost_776_172_join2_0 : P1_7_1_3.blockEstimate 776 172 172 948 = 10227269032 :=
  @P1_7_1_3.block_append 776 172 172 684 512 436 948 6547776141 3679492891 10227269032 cost_776_172_join1_0 cost_776_172_join1_2 rfl rfl rfl

private theorem cost_776_172_total : P1_7_1_3.momentEstimate 776 172 = 10227269032 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 776 + 172 = 948 by decide]
  exact cost_776_172_join2_0

theorem moment776_172 : P1_7_1.groupedPoleMoment 776 172 ≤ 10227269032 :=
  (P1_7_1_3.grouped_bound 776 172).trans_eq cost_776_172_total
private theorem cost_776_174_block0 : P1_7_1_3.blockEstimate 776 174 174 128 = 243545120 := by decide +kernel

private theorem cost_776_174_block1 : P1_7_1_3.blockEstimate 776 174 302 128 = 1361037755 := by decide +kernel

private theorem cost_776_174_block2 : P1_7_1_3.blockEstimate 776 174 430 128 = 2357096000 := by decide +kernel

private theorem cost_776_174_block3 : P1_7_1_3.blockEstimate 776 174 558 128 = 2629480000 := by decide +kernel

private theorem cost_776_174_block4 : P1_7_1_3.blockEstimate 776 174 686 128 = 2170093706 := by decide +kernel

private theorem cost_776_174_block5 : P1_7_1_3.blockEstimate 776 174 814 128 = 1201904662 := by decide +kernel

private theorem cost_776_174_block6 : P1_7_1_3.blockEstimate 776 174 942 128 = 345236323 := by decide +kernel

private theorem cost_776_174_block7 : P1_7_1_3.blockEstimate 776 174 1070 54 = 10697687 := by decide +kernel

private theorem cost_776_174_join0_0 : P1_7_1_3.blockEstimate 776 174 174 256 = 1604582875 :=
  @P1_7_1_3.block_append 776 174 174 302 128 128 256 243545120 1361037755 1604582875 cost_776_174_block0 cost_776_174_block1 rfl rfl rfl

private theorem cost_776_174_join0_2 : P1_7_1_3.blockEstimate 776 174 430 256 = 4986576000 :=
  @P1_7_1_3.block_append 776 174 430 558 128 128 256 2357096000 2629480000 4986576000 cost_776_174_block2 cost_776_174_block3 rfl rfl rfl

private theorem cost_776_174_join0_4 : P1_7_1_3.blockEstimate 776 174 686 256 = 3371998368 :=
  @P1_7_1_3.block_append 776 174 686 814 128 128 256 2170093706 1201904662 3371998368 cost_776_174_block4 cost_776_174_block5 rfl rfl rfl

private theorem cost_776_174_join0_6 : P1_7_1_3.blockEstimate 776 174 942 182 = 355934010 :=
  @P1_7_1_3.block_append 776 174 942 1070 128 54 182 345236323 10697687 355934010 cost_776_174_block6 cost_776_174_block7 rfl rfl rfl

private theorem cost_776_174_join1_0 : P1_7_1_3.blockEstimate 776 174 174 512 = 6591158875 :=
  @P1_7_1_3.block_append 776 174 174 430 256 256 512 1604582875 4986576000 6591158875 cost_776_174_join0_0 cost_776_174_join0_2 rfl rfl rfl

private theorem cost_776_174_join1_2 : P1_7_1_3.blockEstimate 776 174 686 438 = 3727932378 :=
  @P1_7_1_3.block_append 776 174 686 942 256 182 438 3371998368 355934010 3727932378 cost_776_174_join0_4 cost_776_174_join0_6 rfl rfl rfl

private theorem cost_776_174_join2_0 : P1_7_1_3.blockEstimate 776 174 174 950 = 10319091253 :=
  @P1_7_1_3.block_append 776 174 174 686 512 438 950 6591158875 3727932378 10319091253 cost_776_174_join1_0 cost_776_174_join1_2 rfl rfl rfl

private theorem cost_776_174_total : P1_7_1_3.momentEstimate 776 174 = 10319091253 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 776 + 174 = 950 by decide]
  exact cost_776_174_join2_0

theorem moment776_174 : P1_7_1.groupedPoleMoment 776 174 ≤ 10319091253 :=
  (P1_7_1_3.grouped_bound 776 174).trans_eq cost_776_174_total
private theorem cost_777_167_block0 : P1_7_1_3.blockEstimate 777 167 167 128 = 243902880 := by decide +kernel

private theorem cost_777_167_block1 : P1_7_1_3.blockEstimate 777 167 295 128 = 1349336922 := by decide +kernel

private theorem cost_777_167_block2 : P1_7_1_3.blockEstimate 777 167 423 128 = 2302266624 := by decide +kernel

private theorem cost_777_167_block3 : P1_7_1_3.blockEstimate 777 167 551 128 = 2556873984 := by decide +kernel

private theorem cost_777_167_block4 : P1_7_1_3.blockEstimate 777 167 679 128 = 2107962250 := by decide +kernel

private theorem cost_777_167_block5 : P1_7_1_3.blockEstimate 777 167 807 128 = 1153298437 := by decide +kernel

private theorem cost_777_167_block6 : P1_7_1_3.blockEstimate 777 167 935 128 = 316288110 := by decide +kernel

private theorem cost_777_167_block7 : P1_7_1_3.blockEstimate 777 167 1063 48 = 7627100 := by decide +kernel

private theorem cost_777_167_join0_0 : P1_7_1_3.blockEstimate 777 167 167 256 = 1593239802 :=
  @P1_7_1_3.block_append 777 167 167 295 128 128 256 243902880 1349336922 1593239802 cost_777_167_block0 cost_777_167_block1 rfl rfl rfl

private theorem cost_777_167_join0_2 : P1_7_1_3.blockEstimate 777 167 423 256 = 4859140608 :=
  @P1_7_1_3.block_append 777 167 423 551 128 128 256 2302266624 2556873984 4859140608 cost_777_167_block2 cost_777_167_block3 rfl rfl rfl

private theorem cost_777_167_join0_4 : P1_7_1_3.blockEstimate 777 167 679 256 = 3261260687 :=
  @P1_7_1_3.block_append 777 167 679 807 128 128 256 2107962250 1153298437 3261260687 cost_777_167_block4 cost_777_167_block5 rfl rfl rfl

private theorem cost_777_167_join0_6 : P1_7_1_3.blockEstimate 777 167 935 176 = 323915210 :=
  @P1_7_1_3.block_append 777 167 935 1063 128 48 176 316288110 7627100 323915210 cost_777_167_block6 cost_777_167_block7 rfl rfl rfl

private theorem cost_777_167_join1_0 : P1_7_1_3.blockEstimate 777 167 167 512 = 6452380410 :=
  @P1_7_1_3.block_append 777 167 167 423 256 256 512 1593239802 4859140608 6452380410 cost_777_167_join0_0 cost_777_167_join0_2 rfl rfl rfl

private theorem cost_777_167_join1_2 : P1_7_1_3.blockEstimate 777 167 679 432 = 3585175897 :=
  @P1_7_1_3.block_append 777 167 679 935 256 176 432 3261260687 323915210 3585175897 cost_777_167_join0_4 cost_777_167_join0_6 rfl rfl rfl

private theorem cost_777_167_join2_0 : P1_7_1_3.blockEstimate 777 167 167 944 = 10037556307 :=
  @P1_7_1_3.block_append 777 167 167 679 512 432 944 6452380410 3585175897 10037556307 cost_777_167_join1_0 cost_777_167_join1_2 rfl rfl rfl

private theorem cost_777_167_total : P1_7_1_3.momentEstimate 777 167 = 10037556307 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 777 + 167 = 944 by decide]
  exact cost_777_167_join2_0

theorem moment777_167 : P1_7_1.groupedPoleMoment 777 167 ≤ 10037556307 :=
  (P1_7_1_3.grouped_bound 777 167).trans_eq cost_777_167_total
private theorem cost_777_170_block0 : P1_7_1_3.blockEstimate 777 170 170 128 = 243902880 := by decide +kernel

private theorem cost_777_170_block1 : P1_7_1_3.blockEstimate 777 170 298 128 = 1355661387 := by decide +kernel

private theorem cost_777_170_block2 : P1_7_1_3.blockEstimate 777 170 426 128 = 2328357888 := by decide +kernel

private theorem cost_777_170_block3 : P1_7_1_3.blockEstimate 777 170 554 128 = 2591714304 := by decide +kernel

private theorem cost_777_170_block4 : P1_7_1_3.blockEstimate 777 170 682 128 = 2139326072 := by decide +kernel

private theorem cost_777_170_block5 : P1_7_1_3.blockEstimate 777 170 810 128 = 1178234881 := by decide +kernel

private theorem cost_777_170_block6 : P1_7_1_3.blockEstimate 777 170 938 128 = 330846992 := by decide +kernel

private theorem cost_777_170_block7 : P1_7_1_3.blockEstimate 777 170 1066 51 = 9083477 := by decide +kernel

private theorem cost_777_170_join0_0 : P1_7_1_3.blockEstimate 777 170 170 256 = 1599564267 :=
  @P1_7_1_3.block_append 777 170 170 298 128 128 256 243902880 1355661387 1599564267 cost_777_170_block0 cost_777_170_block1 rfl rfl rfl

private theorem cost_777_170_join0_2 : P1_7_1_3.blockEstimate 777 170 426 256 = 4920072192 :=
  @P1_7_1_3.block_append 777 170 426 554 128 128 256 2328357888 2591714304 4920072192 cost_777_170_block2 cost_777_170_block3 rfl rfl rfl

private theorem cost_777_170_join0_4 : P1_7_1_3.blockEstimate 777 170 682 256 = 3317560953 :=
  @P1_7_1_3.block_append 777 170 682 810 128 128 256 2139326072 1178234881 3317560953 cost_777_170_block4 cost_777_170_block5 rfl rfl rfl

private theorem cost_777_170_join0_6 : P1_7_1_3.blockEstimate 777 170 938 179 = 339930469 :=
  @P1_7_1_3.block_append 777 170 938 1066 128 51 179 330846992 9083477 339930469 cost_777_170_block6 cost_777_170_block7 rfl rfl rfl

private theorem cost_777_170_join1_0 : P1_7_1_3.blockEstimate 777 170 170 512 = 6519636459 :=
  @P1_7_1_3.block_append 777 170 170 426 256 256 512 1599564267 4920072192 6519636459 cost_777_170_join0_0 cost_777_170_join0_2 rfl rfl rfl

private theorem cost_777_170_join1_2 : P1_7_1_3.blockEstimate 777 170 682 435 = 3657491422 :=
  @P1_7_1_3.block_append 777 170 682 938 256 179 435 3317560953 339930469 3657491422 cost_777_170_join0_4 cost_777_170_join0_6 rfl rfl rfl

private theorem cost_777_170_join2_0 : P1_7_1_3.blockEstimate 777 170 170 947 = 10177127881 :=
  @P1_7_1_3.block_append 777 170 170 682 512 435 947 6519636459 3657491422 10177127881 cost_777_170_join1_0 cost_777_170_join1_2 rfl rfl rfl

private theorem cost_777_170_total : P1_7_1_3.momentEstimate 777 170 = 10177127881 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 777 + 170 = 947 by decide]
  exact cost_777_170_join2_0

theorem moment777_170 : P1_7_1.groupedPoleMoment 777 170 ≤ 10177127881 :=
  (P1_7_1_3.grouped_bound 777 170).trans_eq cost_777_170_total
private theorem cost_777_172_block0 : P1_7_1_3.blockEstimate 777 172 172 128 = 243902880 := by decide +kernel

private theorem cost_777_172_block1 : P1_7_1_3.blockEstimate 777 172 300 128 = 1359633947 := by decide +kernel

private theorem cost_777_172_block2 : P1_7_1_3.blockEstimate 777 172 428 128 = 2345459264 := by decide +kernel

private theorem cost_777_172_block3 : P1_7_1_3.blockEstimate 777 172 556 128 = 2614730304 := by decide +kernel

private theorem cost_777_172_block4 : P1_7_1_3.blockEstimate 777 172 684 128 = 2160143185 := by decide +kernel

private theorem cost_777_172_block5 : P1_7_1_3.blockEstimate 777 172 812 128 = 1194958219 := by decide +kernel

private theorem cost_777_172_block6 : P1_7_1_3.blockEstimate 777 172 940 128 = 340732305 := by decide +kernel

private theorem cost_777_172_block7 : P1_7_1_3.blockEstimate 777 172 1068 53 = 10149461 := by decide +kernel

private theorem cost_777_172_join0_0 : P1_7_1_3.blockEstimate 777 172 172 256 = 1603536827 :=
  @P1_7_1_3.block_append 777 172 172 300 128 128 256 243902880 1359633947 1603536827 cost_777_172_block0 cost_777_172_block1 rfl rfl rfl

private theorem cost_777_172_join0_2 : P1_7_1_3.blockEstimate 777 172 428 256 = 4960189568 :=
  @P1_7_1_3.block_append 777 172 428 556 128 128 256 2345459264 2614730304 4960189568 cost_777_172_block2 cost_777_172_block3 rfl rfl rfl

private theorem cost_777_172_join0_4 : P1_7_1_3.blockEstimate 777 172 684 256 = 3355101404 :=
  @P1_7_1_3.block_append 777 172 684 812 128 128 256 2160143185 1194958219 3355101404 cost_777_172_block4 cost_777_172_block5 rfl rfl rfl

private theorem cost_777_172_join0_6 : P1_7_1_3.blockEstimate 777 172 940 181 = 350881766 :=
  @P1_7_1_3.block_append 777 172 940 1068 128 53 181 340732305 10149461 350881766 cost_777_172_block6 cost_777_172_block7 rfl rfl rfl

private theorem cost_777_172_join1_0 : P1_7_1_3.blockEstimate 777 172 172 512 = 6563726395 :=
  @P1_7_1_3.block_append 777 172 172 428 256 256 512 1603536827 4960189568 6563726395 cost_777_172_join0_0 cost_777_172_join0_2 rfl rfl rfl

private theorem cost_777_172_join1_2 : P1_7_1_3.blockEstimate 777 172 684 437 = 3705983170 :=
  @P1_7_1_3.block_append 777 172 684 940 256 181 437 3355101404 350881766 3705983170 cost_777_172_join0_4 cost_777_172_join0_6 rfl rfl rfl

private theorem cost_777_172_join2_0 : P1_7_1_3.blockEstimate 777 172 172 949 = 10269709565 :=
  @P1_7_1_3.block_append 777 172 172 684 512 437 949 6563726395 3705983170 10269709565 cost_777_172_join1_0 cost_777_172_join1_2 rfl rfl rfl

private theorem cost_777_172_total : P1_7_1_3.momentEstimate 777 172 = 10269709565 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 777 + 172 = 949 by decide]
  exact cost_777_172_join2_0

theorem moment777_172 : P1_7_1.groupedPoleMoment 777 172 ≤ 10269709565 :=
  (P1_7_1_3.grouped_bound 777 172).trans_eq cost_777_172_total
private theorem cost_790_173_block0 : P1_7_1_3.blockEstimate 790 173 173 128 = 248553760 := by decide +kernel

private theorem cost_790_173_block1 : P1_7_1_3.blockEstimate 790 173 301 128 = 1392437079 := by decide +kernel

private theorem cost_790_173_block2 : P1_7_1_3.blockEstimate 790 173 429 128 = 2421673536 := by decide +kernel

private theorem cost_790_173_block3 : P1_7_1_3.blockEstimate 790 173 557 128 = 2730987072 := by decide +kernel

private theorem cost_790_173_block4 : P1_7_1_3.blockEstimate 790 173 685 128 = 2310997778 := by decide +kernel

private theorem cost_790_173_block5 : P1_7_1_3.blockEstimate 790 173 813 128 = 1334701738 := by decide +kernel

private theorem cost_790_173_block6 : P1_7_1_3.blockEstimate 790 173 941 128 = 421493687 := by decide +kernel

private theorem cost_790_173_block7 : P1_7_1_3.blockEstimate 790 173 1069 67 = 20329076 := by decide +kernel

private theorem cost_790_173_join0_0 : P1_7_1_3.blockEstimate 790 173 173 256 = 1640990839 :=
  @P1_7_1_3.block_append 790 173 173 301 128 128 256 248553760 1392437079 1640990839 cost_790_173_block0 cost_790_173_block1 rfl rfl rfl

private theorem cost_790_173_join0_2 : P1_7_1_3.blockEstimate 790 173 429 256 = 5152660608 :=
  @P1_7_1_3.block_append 790 173 429 557 128 128 256 2421673536 2730987072 5152660608 cost_790_173_block2 cost_790_173_block3 rfl rfl rfl

private theorem cost_790_173_join0_4 : P1_7_1_3.blockEstimate 790 173 685 256 = 3645699516 :=
  @P1_7_1_3.block_append 790 173 685 813 128 128 256 2310997778 1334701738 3645699516 cost_790_173_block4 cost_790_173_block5 rfl rfl rfl

private theorem cost_790_173_join0_6 : P1_7_1_3.blockEstimate 790 173 941 195 = 441822763 :=
  @P1_7_1_3.block_append 790 173 941 1069 128 67 195 421493687 20329076 441822763 cost_790_173_block6 cost_790_173_block7 rfl rfl rfl

private theorem cost_790_173_join1_0 : P1_7_1_3.blockEstimate 790 173 173 512 = 6793651447 :=
  @P1_7_1_3.block_append 790 173 173 429 256 256 512 1640990839 5152660608 6793651447 cost_790_173_join0_0 cost_790_173_join0_2 rfl rfl rfl

private theorem cost_790_173_join1_2 : P1_7_1_3.blockEstimate 790 173 685 451 = 4087522279 :=
  @P1_7_1_3.block_append 790 173 685 941 256 195 451 3645699516 441822763 4087522279 cost_790_173_join0_4 cost_790_173_join0_6 rfl rfl rfl

private theorem cost_790_173_join2_0 : P1_7_1_3.blockEstimate 790 173 173 963 = 10881173726 :=
  @P1_7_1_3.block_append 790 173 173 685 512 451 963 6793651447 4087522279 10881173726 cost_790_173_join1_0 cost_790_173_join1_2 rfl rfl rfl

private theorem cost_790_173_total : P1_7_1_3.momentEstimate 790 173 = 10881173726 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 790 + 173 = 963 by decide]
  exact cost_790_173_join2_0

theorem moment790_173 : P1_7_1.groupedPoleMoment 790 173 ≤ 10881173726 :=
  (P1_7_1_3.grouped_bound 790 173).trans_eq cost_790_173_total
private theorem cost_791_173_block0 : P1_7_1_3.blockEstimate 791 173 173 128 = 248911520 := by decide +kernel

private theorem cost_791_173_block1 : P1_7_1_3.blockEstimate 791 173 301 128 = 1394813091 := by decide +kernel

private theorem cost_791_173_block2 : P1_7_1_3.blockEstimate 791 173 429 128 = 2426885184 := by decide +kernel

private theorem cost_791_173_block3 : P1_7_1_3.blockEstimate 791 173 557 128 = 2739049536 := by decide +kernel

private theorem cost_791_173_block4 : P1_7_1_3.blockEstimate 791 173 685 128 = 2321848974 := by decide +kernel

private theorem cost_791_173_block5 : P1_7_1_3.blockEstimate 791 173 813 128 = 1345086346 := by decide +kernel

private theorem cost_791_173_block6 : P1_7_1_3.blockEstimate 791 173 941 128 = 427670247 := by decide +kernel

private theorem cost_791_173_block7 : P1_7_1_3.blockEstimate 791 173 1069 68 = 21247450 := by decide +kernel

private theorem cost_791_173_join0_0 : P1_7_1_3.blockEstimate 791 173 173 256 = 1643724611 :=
  @P1_7_1_3.block_append 791 173 173 301 128 128 256 248911520 1394813091 1643724611 cost_791_173_block0 cost_791_173_block1 rfl rfl rfl

private theorem cost_791_173_join0_2 : P1_7_1_3.blockEstimate 791 173 429 256 = 5165934720 :=
  @P1_7_1_3.block_append 791 173 429 557 128 128 256 2426885184 2739049536 5165934720 cost_791_173_block2 cost_791_173_block3 rfl rfl rfl

private theorem cost_791_173_join0_4 : P1_7_1_3.blockEstimate 791 173 685 256 = 3666935320 :=
  @P1_7_1_3.block_append 791 173 685 813 128 128 256 2321848974 1345086346 3666935320 cost_791_173_block4 cost_791_173_block5 rfl rfl rfl

private theorem cost_791_173_join0_6 : P1_7_1_3.blockEstimate 791 173 941 196 = 448917697 :=
  @P1_7_1_3.block_append 791 173 941 1069 128 68 196 427670247 21247450 448917697 cost_791_173_block6 cost_791_173_block7 rfl rfl rfl

private theorem cost_791_173_join1_0 : P1_7_1_3.blockEstimate 791 173 173 512 = 6809659331 :=
  @P1_7_1_3.block_append 791 173 173 429 256 256 512 1643724611 5165934720 6809659331 cost_791_173_join0_0 cost_791_173_join0_2 rfl rfl rfl

private theorem cost_791_173_join1_2 : P1_7_1_3.blockEstimate 791 173 685 452 = 4115853017 :=
  @P1_7_1_3.block_append 791 173 685 941 256 196 452 3666935320 448917697 4115853017 cost_791_173_join0_4 cost_791_173_join0_6 rfl rfl rfl

private theorem cost_791_173_join2_0 : P1_7_1_3.blockEstimate 791 173 173 964 = 10925512348 :=
  @P1_7_1_3.block_append 791 173 173 685 512 452 964 6809659331 4115853017 10925512348 cost_791_173_join1_0 cost_791_173_join1_2 rfl rfl rfl

private theorem cost_791_173_total : P1_7_1_3.momentEstimate 791 173 = 10925512348 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 791 + 173 = 964 by decide]
  exact cost_791_173_join2_0

theorem moment791_173 : P1_7_1.groupedPoleMoment 791 173 ≤ 10925512348 :=
  (P1_7_1_3.grouped_bound 791 173).trans_eq cost_791_173_total
private theorem cost_834_185_block0 : P1_7_1_3.blockEstimate 834 185 185 128 = 264295200 := by decide +kernel

private theorem cost_834_185_block1 : P1_7_1_3.blockEstimate 834 185 313 128 = 1518520194 := by decide +kernel

private theorem cost_834_185_block2 : P1_7_1_3.blockEstimate 834 185 441 128 = 2760317376 := by decide +kernel

private theorem cost_834_185_block3 : P1_7_1_3.blockEstimate 834 185 569 128 = 3243334080 := by decide +kernel

private theorem cost_834_185_block4 : P1_7_1_3.blockEstimate 834 185 697 128 = 2946210240 := by decide +kernel

private theorem cost_834_185_block5 : P1_7_1_3.blockEstimate 834 185 825 128 = 1953146450 := by decide +kernel

private theorem cost_834_185_block6 : P1_7_1_3.blockEstimate 834 185 953 128 = 832431845 := by decide +kernel

private theorem cost_834_185_block7 : P1_7_1_3.blockEstimate 834 185 1081 123 = 124940912 := by decide +kernel

private theorem cost_834_185_join0_0 : P1_7_1_3.blockEstimate 834 185 185 256 = 1782815394 :=
  @P1_7_1_3.block_append 834 185 185 313 128 128 256 264295200 1518520194 1782815394 cost_834_185_block0 cost_834_185_block1 rfl rfl rfl

private theorem cost_834_185_join0_2 : P1_7_1_3.blockEstimate 834 185 441 256 = 6003651456 :=
  @P1_7_1_3.block_append 834 185 441 569 128 128 256 2760317376 3243334080 6003651456 cost_834_185_block2 cost_834_185_block3 rfl rfl rfl

private theorem cost_834_185_join0_4 : P1_7_1_3.blockEstimate 834 185 697 256 = 4899356690 :=
  @P1_7_1_3.block_append 834 185 697 825 128 128 256 2946210240 1953146450 4899356690 cost_834_185_block4 cost_834_185_block5 rfl rfl rfl

private theorem cost_834_185_join0_6 : P1_7_1_3.blockEstimate 834 185 953 251 = 957372757 :=
  @P1_7_1_3.block_append 834 185 953 1081 128 123 251 832431845 124940912 957372757 cost_834_185_block6 cost_834_185_block7 rfl rfl rfl

private theorem cost_834_185_join1_0 : P1_7_1_3.blockEstimate 834 185 185 512 = 7786466850 :=
  @P1_7_1_3.block_append 834 185 185 441 256 256 512 1782815394 6003651456 7786466850 cost_834_185_join0_0 cost_834_185_join0_2 rfl rfl rfl

private theorem cost_834_185_join1_2 : P1_7_1_3.blockEstimate 834 185 697 507 = 5856729447 :=
  @P1_7_1_3.block_append 834 185 697 953 256 251 507 4899356690 957372757 5856729447 cost_834_185_join0_4 cost_834_185_join0_6 rfl rfl rfl

private theorem cost_834_185_join2_0 : P1_7_1_3.blockEstimate 834 185 185 1019 = 13643196297 :=
  @P1_7_1_3.block_append 834 185 185 697 512 507 1019 7786466850 5856729447 13643196297 cost_834_185_join1_0 cost_834_185_join1_2 rfl rfl rfl

private theorem cost_834_185_total : P1_7_1_3.momentEstimate 834 185 = 13643196297 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 834 + 185 = 1019 by decide]
  exact cost_834_185_join2_0

theorem moment834_185 : P1_7_1.groupedPoleMoment 834 185 ≤ 13643196297 :=
  (P1_7_1_3.grouped_bound 834 185).trans_eq cost_834_185_total
private theorem cost_835_182_block0 : P1_7_1_3.blockEstimate 835 182 182 128 = 264652960 := by decide +kernel

private theorem cost_835_182_block1 : P1_7_1_3.blockEstimate 835 182 310 128 = 1516171890 := by decide +kernel

private theorem cost_835_182_block2 : P1_7_1_3.blockEstimate 835 182 438 128 = 2739249408 := by decide +kernel

private theorem cost_835_182_block3 : P1_7_1_3.blockEstimate 835 182 566 128 = 3212976384 := by decide +kernel

private theorem cost_835_182_block4 : P1_7_1_3.blockEstimate 835 182 694 128 = 2919145728 := by decide +kernel

private theorem cost_835_182_block5 : P1_7_1_3.blockEstimate 835 182 822 128 = 1934140166 := by decide +kernel

private theorem cost_835_182_block6 : P1_7_1_3.blockEstimate 835 182 950 128 = 817846004 := by decide +kernel

private theorem cost_835_182_block7 : P1_7_1_3.blockEstimate 835 182 1078 121 = 119312180 := by decide +kernel

private theorem cost_835_182_join0_0 : P1_7_1_3.blockEstimate 835 182 182 256 = 1780824850 :=
  @P1_7_1_3.block_append 835 182 182 310 128 128 256 264652960 1516171890 1780824850 cost_835_182_block0 cost_835_182_block1 rfl rfl rfl

private theorem cost_835_182_join0_2 : P1_7_1_3.blockEstimate 835 182 438 256 = 5952225792 :=
  @P1_7_1_3.block_append 835 182 438 566 128 128 256 2739249408 3212976384 5952225792 cost_835_182_block2 cost_835_182_block3 rfl rfl rfl

private theorem cost_835_182_join0_4 : P1_7_1_3.blockEstimate 835 182 694 256 = 4853285894 :=
  @P1_7_1_3.block_append 835 182 694 822 128 128 256 2919145728 1934140166 4853285894 cost_835_182_block4 cost_835_182_block5 rfl rfl rfl

private theorem cost_835_182_join0_6 : P1_7_1_3.blockEstimate 835 182 950 249 = 937158184 :=
  @P1_7_1_3.block_append 835 182 950 1078 128 121 249 817846004 119312180 937158184 cost_835_182_block6 cost_835_182_block7 rfl rfl rfl

private theorem cost_835_182_join1_0 : P1_7_1_3.blockEstimate 835 182 182 512 = 7733050642 :=
  @P1_7_1_3.block_append 835 182 182 438 256 256 512 1780824850 5952225792 7733050642 cost_835_182_join0_0 cost_835_182_join0_2 rfl rfl rfl

private theorem cost_835_182_join1_2 : P1_7_1_3.blockEstimate 835 182 694 505 = 5790444078 :=
  @P1_7_1_3.block_append 835 182 694 950 256 249 505 4853285894 937158184 5790444078 cost_835_182_join0_4 cost_835_182_join0_6 rfl rfl rfl

private theorem cost_835_182_join2_0 : P1_7_1_3.blockEstimate 835 182 182 1017 = 13523494720 :=
  @P1_7_1_3.block_append 835 182 182 694 512 505 1017 7733050642 5790444078 13523494720 cost_835_182_join1_0 cost_835_182_join1_2 rfl rfl rfl

private theorem cost_835_182_total : P1_7_1_3.momentEstimate 835 182 = 13523494720 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 835 + 182 = 1017 by decide]
  exact cost_835_182_join2_0

theorem moment835_182 : P1_7_1.groupedPoleMoment 835 182 ≤ 13523494720 :=
  (P1_7_1_3.grouped_bound 835 182).trans_eq cost_835_182_total
private theorem cost_835_185_block0 : P1_7_1_3.blockEstimate 835 185 185 128 = 264652960 := by decide +kernel

private theorem cost_835_185_block1 : P1_7_1_3.blockEstimate 835 185 313 128 = 1520931850 := by decide +kernel

private theorem cost_835_185_block2 : P1_7_1_3.blockEstimate 835 185 441 128 = 2765745600 := by decide +kernel

private theorem cost_835_185_block3 : P1_7_1_3.blockEstimate 835 185 569 128 = 3251809728 := by decide +kernel

private theorem cost_835_185_block4 : P1_7_1_3.blockEstimate 835 185 697 128 = 2957733312 := by decide +kernel

private theorem cost_835_185_block5 : P1_7_1_3.blockEstimate 835 185 825 128 = 1965616606 := by decide +kernel

private theorem cost_835_185_block6 : P1_7_1_3.blockEstimate 835 185 953 128 = 841323913 := by decide +kernel

private theorem cost_835_185_block7 : P1_7_1_3.blockEstimate 835 185 1081 124 = 128063418 := by decide +kernel

private theorem cost_835_185_join0_0 : P1_7_1_3.blockEstimate 835 185 185 256 = 1785584810 :=
  @P1_7_1_3.block_append 835 185 185 313 128 128 256 264652960 1520931850 1785584810 cost_835_185_block0 cost_835_185_block1 rfl rfl rfl

private theorem cost_835_185_join0_2 : P1_7_1_3.blockEstimate 835 185 441 256 = 6017555328 :=
  @P1_7_1_3.block_append 835 185 441 569 128 128 256 2765745600 3251809728 6017555328 cost_835_185_block2 cost_835_185_block3 rfl rfl rfl

private theorem cost_835_185_join0_4 : P1_7_1_3.blockEstimate 835 185 697 256 = 4923349918 :=
  @P1_7_1_3.block_append 835 185 697 825 128 128 256 2957733312 1965616606 4923349918 cost_835_185_block4 cost_835_185_block5 rfl rfl rfl

private theorem cost_835_185_join0_6 : P1_7_1_3.blockEstimate 835 185 953 252 = 969387331 :=
  @P1_7_1_3.block_append 835 185 953 1081 128 124 252 841323913 128063418 969387331 cost_835_185_block6 cost_835_185_block7 rfl rfl rfl

private theorem cost_835_185_join1_0 : P1_7_1_3.blockEstimate 835 185 185 512 = 7803140138 :=
  @P1_7_1_3.block_append 835 185 185 441 256 256 512 1785584810 6017555328 7803140138 cost_835_185_join0_0 cost_835_185_join0_2 rfl rfl rfl

private theorem cost_835_185_join1_2 : P1_7_1_3.blockEstimate 835 185 697 508 = 5892737249 :=
  @P1_7_1_3.block_append 835 185 697 953 256 252 508 4923349918 969387331 5892737249 cost_835_185_join0_4 cost_835_185_join0_6 rfl rfl rfl

private theorem cost_835_185_join2_0 : P1_7_1_3.blockEstimate 835 185 185 1020 = 13695877387 :=
  @P1_7_1_3.block_append 835 185 185 697 512 508 1020 7803140138 5892737249 13695877387 cost_835_185_join1_0 cost_835_185_join1_2 rfl rfl rfl

private theorem cost_835_185_total : P1_7_1_3.momentEstimate 835 185 = 13695877387 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 835 + 185 = 1020 by decide]
  exact cost_835_185_join2_0

theorem moment835_185 : P1_7_1.groupedPoleMoment 835 185 ≤ 13695877387 :=
  (P1_7_1_3.grouped_bound 835 185).trans_eq cost_835_185_total
private theorem cost_876_195_block0 : P1_7_1_3.blockEstimate 876 195 195 128 = 279321120 := by decide +kernel

private theorem cost_876_195_block1 : P1_7_1_3.blockEstimate 876 195 323 128 = 1633830911 := by decide +kernel

private theorem cost_876_195_block2 : P1_7_1_3.blockEstimate 876 195 451 128 = 3079156864 := by decide +kernel

private theorem cost_876_195_block3 : P1_7_1_3.blockEstimate 876 195 579 128 = 3739071616 := by decide +kernel

private theorem cost_876_195_block4 : P1_7_1_3.blockEstimate 876 195 707 128 = 3576902784 := by decide +kernel

private theorem cost_876_195_block5 : P1_7_1_3.blockEstimate 876 195 835 128 = 2625077594 := by decide +kernel

private theorem cost_876_195_block6 : P1_7_1_3.blockEstimate 876 195 963 128 = 1345926675 := by decide +kernel

private theorem cost_876_195_block7 : P1_7_1_3.blockEstimate 876 195 1091 128 = 355961376 := by decide +kernel

private theorem cost_876_195_block8 : P1_7_1_3.blockEstimate 876 195 1219 47 = 8118956 := by decide +kernel

private theorem cost_876_195_join0_0 : P1_7_1_3.blockEstimate 876 195 195 256 = 1913152031 :=
  @P1_7_1_3.block_append 876 195 195 323 128 128 256 279321120 1633830911 1913152031 cost_876_195_block0 cost_876_195_block1 rfl rfl rfl

private theorem cost_876_195_join0_2 : P1_7_1_3.blockEstimate 876 195 451 256 = 6818228480 :=
  @P1_7_1_3.block_append 876 195 451 579 128 128 256 3079156864 3739071616 6818228480 cost_876_195_block2 cost_876_195_block3 rfl rfl rfl

private theorem cost_876_195_join0_4 : P1_7_1_3.blockEstimate 876 195 707 256 = 6201980378 :=
  @P1_7_1_3.block_append 876 195 707 835 128 128 256 3576902784 2625077594 6201980378 cost_876_195_block4 cost_876_195_block5 rfl rfl rfl

private theorem cost_876_195_join0_6 : P1_7_1_3.blockEstimate 876 195 963 256 = 1701888051 :=
  @P1_7_1_3.block_append 876 195 963 1091 128 128 256 1345926675 355961376 1701888051 cost_876_195_block6 cost_876_195_block7 rfl rfl rfl

private theorem cost_876_195_join1_0 : P1_7_1_3.blockEstimate 876 195 195 512 = 8731380511 :=
  @P1_7_1_3.block_append 876 195 195 451 256 256 512 1913152031 6818228480 8731380511 cost_876_195_join0_0 cost_876_195_join0_2 rfl rfl rfl

private theorem cost_876_195_join1_2 : P1_7_1_3.blockEstimate 876 195 707 512 = 7903868429 :=
  @P1_7_1_3.block_append 876 195 707 963 256 256 512 6201980378 1701888051 7903868429 cost_876_195_join0_4 cost_876_195_join0_6 rfl rfl rfl

private theorem cost_876_195_join2_0 : P1_7_1_3.blockEstimate 876 195 195 1024 = 16635248940 :=
  @P1_7_1_3.block_append 876 195 195 707 512 512 1024 8731380511 7903868429 16635248940 cost_876_195_join1_0 cost_876_195_join1_2 rfl rfl rfl

private theorem cost_876_195_join3_0 : P1_7_1_3.blockEstimate 876 195 195 1071 = 16643367896 :=
  @P1_7_1_3.block_append 876 195 195 1219 1024 47 1071 16635248940 8118956 16643367896 cost_876_195_join2_0 cost_876_195_block8 rfl rfl rfl

private theorem cost_876_195_total : P1_7_1_3.momentEstimate 876 195 = 16643367896 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 876 + 195 = 1071 by decide]
  exact cost_876_195_join3_0

theorem moment876_195 : P1_7_1.groupedPoleMoment 876 195 ≤ 16643367896 :=
  (P1_7_1_3.grouped_bound 876 195).trans_eq cost_876_195_total

end Research6966.HelperRescueCatalogue

end Merged6967_Near6967RescueMoment7

section Merged6967_Near6967RescueMoment8
set_option Elab.async false


set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private theorem cost_877_188_block0 : P1_7_1_3.blockEstimate 877 188 188 128 = 279678880 := by decide +kernel

private theorem cost_877_188_block1 : P1_7_1_3.blockEstimate 877 188 316 128 = 1626892703 := by decide +kernel

private theorem cost_877_188_block2 : P1_7_1_3.blockEstimate 877 188 444 128 = 3021786432 := by decide +kernel

private theorem cost_877_188_block3 : P1_7_1_3.blockEstimate 877 188 572 128 = 3650391360 := by decide +kernel

private theorem cost_877_188_block4 : P1_7_1_3.blockEstimate 877 188 700 128 = 3486272832 := by decide +kernel

private theorem cost_877_188_block5 : P1_7_1_3.blockEstimate 877 188 828 128 = 2554019645 := by decide +kernel

private theorem cost_877_188_block6 : P1_7_1_3.blockEstimate 877 188 956 128 = 1288783772 := by decide +kernel

private theorem cost_877_188_block7 : P1_7_1_3.blockEstimate 877 188 1084 128 = 324285200 := by decide +kernel

private theorem cost_877_188_block8 : P1_7_1_3.blockEstimate 877 188 1212 41 = 5486272 := by decide +kernel

private theorem cost_877_188_join0_0 : P1_7_1_3.blockEstimate 877 188 188 256 = 1906571583 :=
  @P1_7_1_3.block_append 877 188 188 316 128 128 256 279678880 1626892703 1906571583 cost_877_188_block0 cost_877_188_block1 rfl rfl rfl

private theorem cost_877_188_join0_2 : P1_7_1_3.blockEstimate 877 188 444 256 = 6672177792 :=
  @P1_7_1_3.block_append 877 188 444 572 128 128 256 3021786432 3650391360 6672177792 cost_877_188_block2 cost_877_188_block3 rfl rfl rfl

private theorem cost_877_188_join0_4 : P1_7_1_3.blockEstimate 877 188 700 256 = 6040292477 :=
  @P1_7_1_3.block_append 877 188 700 828 128 128 256 3486272832 2554019645 6040292477 cost_877_188_block4 cost_877_188_block5 rfl rfl rfl

private theorem cost_877_188_join0_6 : P1_7_1_3.blockEstimate 877 188 956 256 = 1613068972 :=
  @P1_7_1_3.block_append 877 188 956 1084 128 128 256 1288783772 324285200 1613068972 cost_877_188_block6 cost_877_188_block7 rfl rfl rfl

private theorem cost_877_188_join1_0 : P1_7_1_3.blockEstimate 877 188 188 512 = 8578749375 :=
  @P1_7_1_3.block_append 877 188 188 444 256 256 512 1906571583 6672177792 8578749375 cost_877_188_join0_0 cost_877_188_join0_2 rfl rfl rfl

private theorem cost_877_188_join1_2 : P1_7_1_3.blockEstimate 877 188 700 512 = 7653361449 :=
  @P1_7_1_3.block_append 877 188 700 956 256 256 512 6040292477 1613068972 7653361449 cost_877_188_join0_4 cost_877_188_join0_6 rfl rfl rfl

private theorem cost_877_188_join2_0 : P1_7_1_3.blockEstimate 877 188 188 1024 = 16232110824 :=
  @P1_7_1_3.block_append 877 188 188 700 512 512 1024 8578749375 7653361449 16232110824 cost_877_188_join1_0 cost_877_188_join1_2 rfl rfl rfl

private theorem cost_877_188_join3_0 : P1_7_1_3.blockEstimate 877 188 188 1065 = 16237597096 :=
  @P1_7_1_3.block_append 877 188 188 1212 1024 41 1065 16232110824 5486272 16237597096 cost_877_188_join2_0 cost_877_188_block8 rfl rfl rfl

private theorem cost_877_188_total : P1_7_1_3.momentEstimate 877 188 = 16237597096 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 877 + 188 = 1065 by decide]
  exact cost_877_188_join3_0

theorem moment877_188 : P1_7_1.groupedPoleMoment 877 188 ≤ 16237597096 :=
  (P1_7_1_3.grouped_bound 877 188).trans_eq cost_877_188_total
private theorem cost_877_192_block0 : P1_7_1_3.blockEstimate 877 192 192 128 = 279678880 := by decide +kernel

private theorem cost_877_192_block1 : P1_7_1_3.blockEstimate 877 192 320 128 = 1632500272 := by decide +kernel

private theorem cost_877_192_block2 : P1_7_1_3.blockEstimate 877 192 448 128 = 3058194624 := by decide +kernel

private theorem cost_877_192_block3 : P1_7_1_3.blockEstimate 877 192 576 128 = 3706427584 := by decide +kernel

private theorem cost_877_192_block4 : P1_7_1_3.blockEstimate 877 192 704 128 = 3545159872 := by decide +kernel

private theorem cost_877_192_block5 : P1_7_1_3.blockEstimate 877 192 832 128 = 2602702976 := by decide +kernel

private theorem cost_877_192_block6 : P1_7_1_3.blockEstimate 877 192 960 128 = 1327779499 := by decide +kernel

private theorem cost_877_192_block7 : P1_7_1_3.blockEstimate 877 192 1088 128 = 345529616 := by decide +kernel

private theorem cost_877_192_block8 : P1_7_1_3.blockEstimate 877 192 1216 45 = 7171150 := by decide +kernel

private theorem cost_877_192_join0_0 : P1_7_1_3.blockEstimate 877 192 192 256 = 1912179152 :=
  @P1_7_1_3.block_append 877 192 192 320 128 128 256 279678880 1632500272 1912179152 cost_877_192_block0 cost_877_192_block1 rfl rfl rfl

private theorem cost_877_192_join0_2 : P1_7_1_3.blockEstimate 877 192 448 256 = 6764622208 :=
  @P1_7_1_3.block_append 877 192 448 576 128 128 256 3058194624 3706427584 6764622208 cost_877_192_block2 cost_877_192_block3 rfl rfl rfl

private theorem cost_877_192_join0_4 : P1_7_1_3.blockEstimate 877 192 704 256 = 6147862848 :=
  @P1_7_1_3.block_append 877 192 704 832 128 128 256 3545159872 2602702976 6147862848 cost_877_192_block4 cost_877_192_block5 rfl rfl rfl

private theorem cost_877_192_join0_6 : P1_7_1_3.blockEstimate 877 192 960 256 = 1673309115 :=
  @P1_7_1_3.block_append 877 192 960 1088 128 128 256 1327779499 345529616 1673309115 cost_877_192_block6 cost_877_192_block7 rfl rfl rfl

private theorem cost_877_192_join1_0 : P1_7_1_3.blockEstimate 877 192 192 512 = 8676801360 :=
  @P1_7_1_3.block_append 877 192 192 448 256 256 512 1912179152 6764622208 8676801360 cost_877_192_join0_0 cost_877_192_join0_2 rfl rfl rfl

private theorem cost_877_192_join1_2 : P1_7_1_3.blockEstimate 877 192 704 512 = 7821171963 :=
  @P1_7_1_3.block_append 877 192 704 960 256 256 512 6147862848 1673309115 7821171963 cost_877_192_join0_4 cost_877_192_join0_6 rfl rfl rfl

private theorem cost_877_192_join2_0 : P1_7_1_3.blockEstimate 877 192 192 1024 = 16497973323 :=
  @P1_7_1_3.block_append 877 192 192 704 512 512 1024 8676801360 7821171963 16497973323 cost_877_192_join1_0 cost_877_192_join1_2 rfl rfl rfl

private theorem cost_877_192_join3_0 : P1_7_1_3.blockEstimate 877 192 192 1069 = 16505144473 :=
  @P1_7_1_3.block_append 877 192 192 1216 1024 45 1069 16497973323 7171150 16505144473 cost_877_192_join2_0 cost_877_192_block8 rfl rfl rfl

private theorem cost_877_192_total : P1_7_1_3.momentEstimate 877 192 = 16505144473 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 877 + 192 = 1069 by decide]
  exact cost_877_192_join3_0

theorem moment877_192 : P1_7_1.groupedPoleMoment 877 192 ≤ 16505144473 :=
  (P1_7_1_3.grouped_bound 877 192).trans_eq cost_877_192_total
private theorem cost_877_193_block0 : P1_7_1_3.blockEstimate 877 193 193 128 = 279678880 := by decide +kernel

private theorem cost_877_193_block1 : P1_7_1_3.blockEstimate 877 193 321 128 = 1633795888 := by decide +kernel

private theorem cost_877_193_block2 : P1_7_1_3.blockEstimate 877 193 449 128 = 3067118272 := by decide +kernel

private theorem cost_877_193_block3 : P1_7_1_3.blockEstimate 877 193 577 128 = 3720299200 := by decide +kernel

private theorem cost_877_193_block4 : P1_7_1_3.blockEstimate 877 193 705 128 = 3559785152 := by decide +kernel

private theorem cost_877_193_block5 : P1_7_1_3.blockEstimate 877 193 833 128 = 2614870754 := by decide +kernel

private theorem cost_877_193_block6 : P1_7_1_3.blockEstimate 877 193 961 128 = 1337596742 := by decide +kernel

private theorem cost_877_193_block7 : P1_7_1_3.blockEstimate 877 193 1089 128 = 350948432 := by decide +kernel

private theorem cost_877_193_block8 : P1_7_1_3.blockEstimate 877 193 1217 46 = 7639798 := by decide +kernel

private theorem cost_877_193_join0_0 : P1_7_1_3.blockEstimate 877 193 193 256 = 1913474768 :=
  @P1_7_1_3.block_append 877 193 193 321 128 128 256 279678880 1633795888 1913474768 cost_877_193_block0 cost_877_193_block1 rfl rfl rfl

private theorem cost_877_193_join0_2 : P1_7_1_3.blockEstimate 877 193 449 256 = 6787417472 :=
  @P1_7_1_3.block_append 877 193 449 577 128 128 256 3067118272 3720299200 6787417472 cost_877_193_block2 cost_877_193_block3 rfl rfl rfl

private theorem cost_877_193_join0_4 : P1_7_1_3.blockEstimate 877 193 705 256 = 6174655906 :=
  @P1_7_1_3.block_append 877 193 705 833 128 128 256 3559785152 2614870754 6174655906 cost_877_193_block4 cost_877_193_block5 rfl rfl rfl

private theorem cost_877_193_join0_6 : P1_7_1_3.blockEstimate 877 193 961 256 = 1688545174 :=
  @P1_7_1_3.block_append 877 193 961 1089 128 128 256 1337596742 350948432 1688545174 cost_877_193_block6 cost_877_193_block7 rfl rfl rfl

private theorem cost_877_193_join1_0 : P1_7_1_3.blockEstimate 877 193 193 512 = 8700892240 :=
  @P1_7_1_3.block_append 877 193 193 449 256 256 512 1913474768 6787417472 8700892240 cost_877_193_join0_0 cost_877_193_join0_2 rfl rfl rfl

private theorem cost_877_193_join1_2 : P1_7_1_3.blockEstimate 877 193 705 512 = 7863201080 :=
  @P1_7_1_3.block_append 877 193 705 961 256 256 512 6174655906 1688545174 7863201080 cost_877_193_join0_4 cost_877_193_join0_6 rfl rfl rfl

private theorem cost_877_193_join2_0 : P1_7_1_3.blockEstimate 877 193 193 1024 = 16564093320 :=
  @P1_7_1_3.block_append 877 193 193 705 512 512 1024 8700892240 7863201080 16564093320 cost_877_193_join1_0 cost_877_193_join1_2 rfl rfl rfl

private theorem cost_877_193_join3_0 : P1_7_1_3.blockEstimate 877 193 193 1070 = 16571733118 :=
  @P1_7_1_3.block_append 877 193 193 1217 1024 46 1070 16564093320 7639798 16571733118 cost_877_193_join2_0 cost_877_193_block8 rfl rfl rfl

private theorem cost_877_193_total : P1_7_1_3.momentEstimate 877 193 = 16571733118 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 877 + 193 = 1070 by decide]
  exact cost_877_193_join3_0

theorem moment877_193 : P1_7_1.groupedPoleMoment 877 193 ≤ 16571733118 :=
  (P1_7_1_3.grouped_bound 877 193).trans_eq cost_877_193_total
private theorem cost_878_190_block0 : P1_7_1_3.blockEstimate 878 190 190 128 = 280036640 := by decide +kernel

private theorem cost_878_190_block1 : P1_7_1_3.blockEstimate 878 190 318 128 = 1632206273 := by decide +kernel

private theorem cost_878_190_block2 : P1_7_1_3.blockEstimate 878 190 446 128 = 3045646272 := by decide +kernel

private theorem cost_878_190_block3 : P1_7_1_3.blockEstimate 878 190 574 128 = 3687161792 := by decide +kernel

private theorem cost_878_190_block4 : P1_7_1_3.blockEstimate 878 190 702 128 = 3527565248 := by decide +kernel

private theorem cost_878_190_block5 : P1_7_1_3.blockEstimate 878 190 830 128 = 2592302225 := by decide +kernel

private theorem cost_878_190_block6 : P1_7_1_3.blockEstimate 878 190 958 128 = 1319458608 := by decide +kernel

private theorem cost_878_190_block7 : P1_7_1_3.blockEstimate 878 190 1086 128 = 340581152 := by decide +kernel

private theorem cost_878_190_block8 : P1_7_1_3.blockEstimate 878 190 1214 44 = 6729547 := by decide +kernel

private theorem cost_878_190_join0_0 : P1_7_1_3.blockEstimate 878 190 190 256 = 1912242913 :=
  @P1_7_1_3.block_append 878 190 190 318 128 128 256 280036640 1632206273 1912242913 cost_878_190_block0 cost_878_190_block1 rfl rfl rfl

private theorem cost_878_190_join0_2 : P1_7_1_3.blockEstimate 878 190 446 256 = 6732808064 :=
  @P1_7_1_3.block_append 878 190 446 574 128 128 256 3045646272 3687161792 6732808064 cost_878_190_block2 cost_878_190_block3 rfl rfl rfl

private theorem cost_878_190_join0_4 : P1_7_1_3.blockEstimate 878 190 702 256 = 6119867473 :=
  @P1_7_1_3.block_append 878 190 702 830 128 128 256 3527565248 2592302225 6119867473 cost_878_190_block4 cost_878_190_block5 rfl rfl rfl

private theorem cost_878_190_join0_6 : P1_7_1_3.blockEstimate 878 190 958 256 = 1660039760 :=
  @P1_7_1_3.block_append 878 190 958 1086 128 128 256 1319458608 340581152 1660039760 cost_878_190_block6 cost_878_190_block7 rfl rfl rfl

private theorem cost_878_190_join1_0 : P1_7_1_3.blockEstimate 878 190 190 512 = 8645050977 :=
  @P1_7_1_3.block_append 878 190 190 446 256 256 512 1912242913 6732808064 8645050977 cost_878_190_join0_0 cost_878_190_join0_2 rfl rfl rfl

private theorem cost_878_190_join1_2 : P1_7_1_3.blockEstimate 878 190 702 512 = 7779907233 :=
  @P1_7_1_3.block_append 878 190 702 958 256 256 512 6119867473 1660039760 7779907233 cost_878_190_join0_4 cost_878_190_join0_6 rfl rfl rfl

private theorem cost_878_190_join2_0 : P1_7_1_3.blockEstimate 878 190 190 1024 = 16424958210 :=
  @P1_7_1_3.block_append 878 190 190 702 512 512 1024 8645050977 7779907233 16424958210 cost_878_190_join1_0 cost_878_190_join1_2 rfl rfl rfl

private theorem cost_878_190_join3_0 : P1_7_1_3.blockEstimate 878 190 190 1068 = 16431687757 :=
  @P1_7_1_3.block_append 878 190 190 1214 1024 44 1068 16424958210 6729547 16431687757 cost_878_190_join2_0 cost_878_190_block8 rfl rfl rfl

private theorem cost_878_190_total : P1_7_1_3.momentEstimate 878 190 = 16431687757 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 878 + 190 = 1068 by decide]
  exact cost_878_190_join3_0

theorem moment878_190 : P1_7_1.groupedPoleMoment 878 190 ≤ 16431687757 :=
  (P1_7_1_3.grouped_bound 878 190).trans_eq cost_878_190_total
private theorem cost_878_192_block0 : P1_7_1_3.blockEstimate 878 192 192 128 = 280036640 := by decide +kernel

private theorem cost_878_192_block1 : P1_7_1_3.blockEstimate 878 192 320 128 = 1634927888 := by decide +kernel

private theorem cost_878_192_block2 : P1_7_1_3.blockEstimate 878 192 448 128 = 3063740672 := by decide +kernel

private theorem cost_878_192_block3 : P1_7_1_3.blockEstimate 878 192 576 128 = 3715135744 := by decide +kernel

private theorem cost_878_192_block4 : P1_7_1_3.blockEstimate 878 192 704 128 = 3557030144 := by decide +kernel

private theorem cost_878_192_block5 : P1_7_1_3.blockEstimate 878 192 832 128 = 2616727356 := by decide +kernel

private theorem cost_878_192_block6 : P1_7_1_3.blockEstimate 878 192 960 128 = 1339092580 := by decide +kernel

private theorem cost_878_192_block7 : P1_7_1_3.blockEstimate 878 192 1088 128 = 351389936 := by decide +kernel

private theorem cost_878_192_block8 : P1_7_1_3.blockEstimate 878 192 1216 46 = 7648722 := by decide +kernel

private theorem cost_878_192_join0_0 : P1_7_1_3.blockEstimate 878 192 192 256 = 1914964528 :=
  @P1_7_1_3.block_append 878 192 192 320 128 128 256 280036640 1634927888 1914964528 cost_878_192_block0 cost_878_192_block1 rfl rfl rfl

private theorem cost_878_192_join0_2 : P1_7_1_3.blockEstimate 878 192 448 256 = 6778876416 :=
  @P1_7_1_3.block_append 878 192 448 576 128 128 256 3063740672 3715135744 6778876416 cost_878_192_block2 cost_878_192_block3 rfl rfl rfl

private theorem cost_878_192_join0_4 : P1_7_1_3.blockEstimate 878 192 704 256 = 6173757500 :=
  @P1_7_1_3.block_append 878 192 704 832 128 128 256 3557030144 2616727356 6173757500 cost_878_192_block4 cost_878_192_block5 rfl rfl rfl

private theorem cost_878_192_join0_6 : P1_7_1_3.blockEstimate 878 192 960 256 = 1690482516 :=
  @P1_7_1_3.block_append 878 192 960 1088 128 128 256 1339092580 351389936 1690482516 cost_878_192_block6 cost_878_192_block7 rfl rfl rfl

private theorem cost_878_192_join1_0 : P1_7_1_3.blockEstimate 878 192 192 512 = 8693840944 :=
  @P1_7_1_3.block_append 878 192 192 448 256 256 512 1914964528 6778876416 8693840944 cost_878_192_join0_0 cost_878_192_join0_2 rfl rfl rfl

private theorem cost_878_192_join1_2 : P1_7_1_3.blockEstimate 878 192 704 512 = 7864240016 :=
  @P1_7_1_3.block_append 878 192 704 960 256 256 512 6173757500 1690482516 7864240016 cost_878_192_join0_4 cost_878_192_join0_6 rfl rfl rfl

private theorem cost_878_192_join2_0 : P1_7_1_3.blockEstimate 878 192 192 1024 = 16558080960 :=
  @P1_7_1_3.block_append 878 192 192 704 512 512 1024 8693840944 7864240016 16558080960 cost_878_192_join1_0 cost_878_192_join1_2 rfl rfl rfl

private theorem cost_878_192_join3_0 : P1_7_1_3.blockEstimate 878 192 192 1070 = 16565729682 :=
  @P1_7_1_3.block_append 878 192 192 1216 1024 46 1070 16558080960 7648722 16565729682 cost_878_192_join2_0 cost_878_192_block8 rfl rfl rfl

private theorem cost_878_192_total : P1_7_1_3.momentEstimate 878 192 = 16565729682 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 878 + 192 = 1070 by decide]
  exact cost_878_192_join3_0

theorem moment878_192 : P1_7_1.groupedPoleMoment 878 192 ≤ 16565729682 :=
  (P1_7_1_3.grouped_bound 878 192).trans_eq cost_878_192_total
private theorem cost_878_195_block0 : P1_7_1_3.blockEstimate 878 195 195 128 = 280036640 := by decide +kernel

private theorem cost_878_195_block1 : P1_7_1_3.blockEstimate 878 195 323 128 = 1638697863 := by decide +kernel

private theorem cost_878_195_block2 : P1_7_1_3.blockEstimate 878 195 451 128 = 3090346112 := by decide +kernel

private theorem cost_878_195_block3 : P1_7_1_3.blockEstimate 878 195 579 128 = 3756683392 := by decide +kernel

private theorem cost_878_195_block4 : P1_7_1_3.blockEstimate 878 195 707 128 = 3600937088 := by decide +kernel

private theorem cost_878_195_block5 : P1_7_1_3.blockEstimate 878 195 835 128 = 2653354789 := by decide +kernel

private theorem cost_878_195_block6 : P1_7_1_3.blockEstimate 878 195 963 128 = 1368746766 := by decide +kernel

private theorem cost_878_195_block7 : P1_7_1_3.blockEstimate 878 195 1091 128 = 367924528 := by decide +kernel

private theorem cost_878_195_block8 : P1_7_1_3.blockEstimate 878 195 1219 49 = 9177272 := by decide +kernel

private theorem cost_878_195_join0_0 : P1_7_1_3.blockEstimate 878 195 195 256 = 1918734503 :=
  @P1_7_1_3.block_append 878 195 195 323 128 128 256 280036640 1638697863 1918734503 cost_878_195_block0 cost_878_195_block1 rfl rfl rfl

private theorem cost_878_195_join0_2 : P1_7_1_3.blockEstimate 878 195 451 256 = 6847029504 :=
  @P1_7_1_3.block_append 878 195 451 579 128 128 256 3090346112 3756683392 6847029504 cost_878_195_block2 cost_878_195_block3 rfl rfl rfl

private theorem cost_878_195_join0_4 : P1_7_1_3.blockEstimate 878 195 707 256 = 6254291877 :=
  @P1_7_1_3.block_append 878 195 707 835 128 128 256 3600937088 2653354789 6254291877 cost_878_195_block4 cost_878_195_block5 rfl rfl rfl

private theorem cost_878_195_join0_6 : P1_7_1_3.blockEstimate 878 195 963 256 = 1736671294 :=
  @P1_7_1_3.block_append 878 195 963 1091 128 128 256 1368746766 367924528 1736671294 cost_878_195_block6 cost_878_195_block7 rfl rfl rfl

private theorem cost_878_195_join1_0 : P1_7_1_3.blockEstimate 878 195 195 512 = 8765764007 :=
  @P1_7_1_3.block_append 878 195 195 451 256 256 512 1918734503 6847029504 8765764007 cost_878_195_join0_0 cost_878_195_join0_2 rfl rfl rfl

private theorem cost_878_195_join1_2 : P1_7_1_3.blockEstimate 878 195 707 512 = 7990963171 :=
  @P1_7_1_3.block_append 878 195 707 963 256 256 512 6254291877 1736671294 7990963171 cost_878_195_join0_4 cost_878_195_join0_6 rfl rfl rfl

private theorem cost_878_195_join2_0 : P1_7_1_3.blockEstimate 878 195 195 1024 = 16756727178 :=
  @P1_7_1_3.block_append 878 195 195 707 512 512 1024 8765764007 7990963171 16756727178 cost_878_195_join1_0 cost_878_195_join1_2 rfl rfl rfl

private theorem cost_878_195_join3_0 : P1_7_1_3.blockEstimate 878 195 195 1073 = 16765904450 :=
  @P1_7_1_3.block_append 878 195 195 1219 1024 49 1073 16756727178 9177272 16765904450 cost_878_195_join2_0 cost_878_195_block8 rfl rfl rfl

private theorem cost_878_195_total : P1_7_1_3.momentEstimate 878 195 = 16765904450 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 878 + 195 = 1073 by decide]
  exact cost_878_195_join3_0

theorem moment878_195 : P1_7_1.groupedPoleMoment 878 195 ≤ 16765904450 :=
  (P1_7_1_3.grouped_bound 878 195).trans_eq cost_878_195_total
private theorem cost_879_190_block0 : P1_7_1_3.blockEstimate 879 190 190 128 = 280394400 := by decide +kernel

private theorem cost_879_190_block1 : P1_7_1_3.blockEstimate 879 190 318 128 = 1634629664 := by decide +kernel

private theorem cost_879_190_block2 : P1_7_1_3.blockEstimate 879 190 446 128 = 3051159296 := by decide +kernel

private theorem cost_879_190_block3 : P1_7_1_3.blockEstimate 879 190 574 128 = 3695804160 := by decide +kernel

private theorem cost_879_190_block4 : P1_7_1_3.blockEstimate 879 190 702 128 = 3539336960 := by decide +kernel

private theorem cost_879_190_block5 : P1_7_1_3.blockEstimate 879 190 830 128 = 2606263865 := by decide +kernel

private theorem cost_879_190_block6 : P1_7_1_3.blockEstimate 879 190 958 128 = 1330739222 := by decide +kernel

private theorem cost_879_190_block7 : P1_7_1_3.blockEstimate 879 190 1086 128 = 346398416 := by decide +kernel

private theorem cost_879_190_block8 : P1_7_1_3.blockEstimate 879 190 1214 45 = 7187894 := by decide +kernel

private theorem cost_879_190_join0_0 : P1_7_1_3.blockEstimate 879 190 190 256 = 1915024064 :=
  @P1_7_1_3.block_append 879 190 190 318 128 128 256 280394400 1634629664 1915024064 cost_879_190_block0 cost_879_190_block1 rfl rfl rfl

private theorem cost_879_190_join0_2 : P1_7_1_3.blockEstimate 879 190 446 256 = 6746963456 :=
  @P1_7_1_3.block_append 879 190 446 574 128 128 256 3051159296 3695804160 6746963456 cost_879_190_block2 cost_879_190_block3 rfl rfl rfl

private theorem cost_879_190_join0_4 : P1_7_1_3.blockEstimate 879 190 702 256 = 6145600825 :=
  @P1_7_1_3.block_append 879 190 702 830 128 128 256 3539336960 2606263865 6145600825 cost_879_190_block4 cost_879_190_block5 rfl rfl rfl

private theorem cost_879_190_join0_6 : P1_7_1_3.blockEstimate 879 190 958 256 = 1677137638 :=
  @P1_7_1_3.block_append 879 190 958 1086 128 128 256 1330739222 346398416 1677137638 cost_879_190_block6 cost_879_190_block7 rfl rfl rfl

private theorem cost_879_190_join1_0 : P1_7_1_3.blockEstimate 879 190 190 512 = 8661987520 :=
  @P1_7_1_3.block_append 879 190 190 446 256 256 512 1915024064 6746963456 8661987520 cost_879_190_join0_0 cost_879_190_join0_2 rfl rfl rfl

private theorem cost_879_190_join1_2 : P1_7_1_3.blockEstimate 879 190 702 512 = 7822738463 :=
  @P1_7_1_3.block_append 879 190 702 958 256 256 512 6145600825 1677137638 7822738463 cost_879_190_join0_4 cost_879_190_join0_6 rfl rfl rfl

private theorem cost_879_190_join2_0 : P1_7_1_3.blockEstimate 879 190 190 1024 = 16484725983 :=
  @P1_7_1_3.block_append 879 190 190 702 512 512 1024 8661987520 7822738463 16484725983 cost_879_190_join1_0 cost_879_190_join1_2 rfl rfl rfl

private theorem cost_879_190_join3_0 : P1_7_1_3.blockEstimate 879 190 190 1069 = 16491913877 :=
  @P1_7_1_3.block_append 879 190 190 1214 1024 45 1069 16484725983 7187894 16491913877 cost_879_190_join2_0 cost_879_190_block8 rfl rfl rfl

private theorem cost_879_190_total : P1_7_1_3.momentEstimate 879 190 = 16491913877 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 879 + 190 = 1069 by decide]
  exact cost_879_190_join3_0

theorem moment879_190 : P1_7_1.groupedPoleMoment 879 190 ≤ 16491913877 :=
  (P1_7_1_3.grouped_bound 879 190).trans_eq cost_879_190_total
private theorem cost_879_195_block0 : P1_7_1_3.blockEstimate 879 195 195 128 = 280394400 := by decide +kernel

private theorem cost_879_195_block1 : P1_7_1_3.blockEstimate 879 195 323 128 = 1641131339 := by decide +kernel

private theorem cost_879_195_block2 : P1_7_1_3.blockEstimate 879 195 451 128 = 3095940736 := by decide +kernel

private theorem cost_879_195_block3 : P1_7_1_3.blockEstimate 879 195 579 128 = 3765489280 := by decide +kernel

private theorem cost_879_195_block4 : P1_7_1_3.blockEstimate 879 195 707 128 = 3612954240 := by decide +kernel

private theorem cost_879_195_block5 : P1_7_1_3.blockEstimate 879 195 835 128 = 2667531119 := by decide +kernel

private theorem cost_879_195_block6 : P1_7_1_3.blockEstimate 879 195 963 128 = 1380229866 := by decide +kernel

private theorem cost_879_195_block7 : P1_7_1_3.blockEstimate 879 195 1091 128 = 373991888 := by decide +kernel

private theorem cost_879_195_block8 : P1_7_1_3.blockEstimate 879 195 1219 50 = 9739522 := by decide +kernel

private theorem cost_879_195_join0_0 : P1_7_1_3.blockEstimate 879 195 195 256 = 1921525739 :=
  @P1_7_1_3.block_append 879 195 195 323 128 128 256 280394400 1641131339 1921525739 cost_879_195_block0 cost_879_195_block1 rfl rfl rfl

private theorem cost_879_195_join0_2 : P1_7_1_3.blockEstimate 879 195 451 256 = 6861430016 :=
  @P1_7_1_3.block_append 879 195 451 579 128 128 256 3095940736 3765489280 6861430016 cost_879_195_block2 cost_879_195_block3 rfl rfl rfl

private theorem cost_879_195_join0_4 : P1_7_1_3.blockEstimate 879 195 707 256 = 6280485359 :=
  @P1_7_1_3.block_append 879 195 707 835 128 128 256 3612954240 2667531119 6280485359 cost_879_195_block4 cost_879_195_block5 rfl rfl rfl

private theorem cost_879_195_join0_6 : P1_7_1_3.blockEstimate 879 195 963 256 = 1754221754 :=
  @P1_7_1_3.block_append 879 195 963 1091 128 128 256 1380229866 373991888 1754221754 cost_879_195_block6 cost_879_195_block7 rfl rfl rfl

private theorem cost_879_195_join1_0 : P1_7_1_3.blockEstimate 879 195 195 512 = 8782955755 :=
  @P1_7_1_3.block_append 879 195 195 451 256 256 512 1921525739 6861430016 8782955755 cost_879_195_join0_0 cost_879_195_join0_2 rfl rfl rfl

private theorem cost_879_195_join1_2 : P1_7_1_3.blockEstimate 879 195 707 512 = 8034707113 :=
  @P1_7_1_3.block_append 879 195 707 963 256 256 512 6280485359 1754221754 8034707113 cost_879_195_join0_4 cost_879_195_join0_6 rfl rfl rfl

private theorem cost_879_195_join2_0 : P1_7_1_3.blockEstimate 879 195 195 1024 = 16817662868 :=
  @P1_7_1_3.block_append 879 195 195 707 512 512 1024 8782955755 8034707113 16817662868 cost_879_195_join1_0 cost_879_195_join1_2 rfl rfl rfl

private theorem cost_879_195_join3_0 : P1_7_1_3.blockEstimate 879 195 195 1074 = 16827402390 :=
  @P1_7_1_3.block_append 879 195 195 1219 1024 50 1074 16817662868 9739522 16827402390 cost_879_195_join2_0 cost_879_195_block8 rfl rfl rfl

private theorem cost_879_195_total : P1_7_1_3.momentEstimate 879 195 = 16827402390 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 879 + 195 = 1074 by decide]
  exact cost_879_195_join3_0

theorem moment879_195 : P1_7_1.groupedPoleMoment 879 195 ≤ 16827402390 :=
  (P1_7_1_3.grouped_bound 879 195).trans_eq cost_879_195_total
private theorem cost_879_197_block0 : P1_7_1_3.blockEstimate 879 197 197 128 = 280394400 := by decide +kernel

private theorem cost_879_197_block1 : P1_7_1_3.blockEstimate 879 197 325 128 = 1643447949 := by decide +kernel

private theorem cost_879_197_block2 : P1_7_1_3.blockEstimate 879 197 453 128 = 3113352000 := by decide +kernel

private theorem cost_879_197_block3 : P1_7_1_3.blockEstimate 879 197 581 128 = 3792976704 := by decide +kernel

private theorem cost_879_197_block4 : P1_7_1_3.blockEstimate 879 197 709 128 = 3642129216 := by decide +kernel

private theorem cost_879_197_block5 : P1_7_1_3.blockEstimate 879 197 837 128 = 2692028066 := by decide +kernel

private theorem cost_879_197_block6 : P1_7_1_3.blockEstimate 879 197 965 128 = 1400213959 := by decide +kernel

private theorem cost_879_197_block7 : P1_7_1_3.blockEstimate 879 197 1093 128 = 385327488 := by decide +kernel

private theorem cost_879_197_block8 : P1_7_1_3.blockEstimate 879 197 1221 52 = 10907442 := by decide +kernel

private theorem cost_879_197_join0_0 : P1_7_1_3.blockEstimate 879 197 197 256 = 1923842349 :=
  @P1_7_1_3.block_append 879 197 197 325 128 128 256 280394400 1643447949 1923842349 cost_879_197_block0 cost_879_197_block1 rfl rfl rfl

private theorem cost_879_197_join0_2 : P1_7_1_3.blockEstimate 879 197 453 256 = 6906328704 :=
  @P1_7_1_3.block_append 879 197 453 581 128 128 256 3113352000 3792976704 6906328704 cost_879_197_block2 cost_879_197_block3 rfl rfl rfl

private theorem cost_879_197_join0_4 : P1_7_1_3.blockEstimate 879 197 709 256 = 6334157282 :=
  @P1_7_1_3.block_append 879 197 709 837 128 128 256 3642129216 2692028066 6334157282 cost_879_197_block4 cost_879_197_block5 rfl rfl rfl

private theorem cost_879_197_join0_6 : P1_7_1_3.blockEstimate 879 197 965 256 = 1785541447 :=
  @P1_7_1_3.block_append 879 197 965 1093 128 128 256 1400213959 385327488 1785541447 cost_879_197_block6 cost_879_197_block7 rfl rfl rfl

private theorem cost_879_197_join1_0 : P1_7_1_3.blockEstimate 879 197 197 512 = 8830171053 :=
  @P1_7_1_3.block_append 879 197 197 453 256 256 512 1923842349 6906328704 8830171053 cost_879_197_join0_0 cost_879_197_join0_2 rfl rfl rfl

private theorem cost_879_197_join1_2 : P1_7_1_3.blockEstimate 879 197 709 512 = 8119698729 :=
  @P1_7_1_3.block_append 879 197 709 965 256 256 512 6334157282 1785541447 8119698729 cost_879_197_join0_4 cost_879_197_join0_6 rfl rfl rfl

private theorem cost_879_197_join2_0 : P1_7_1_3.blockEstimate 879 197 197 1024 = 16949869782 :=
  @P1_7_1_3.block_append 879 197 197 709 512 512 1024 8830171053 8119698729 16949869782 cost_879_197_join1_0 cost_879_197_join1_2 rfl rfl rfl

private theorem cost_879_197_join3_0 : P1_7_1_3.blockEstimate 879 197 197 1076 = 16960777224 :=
  @P1_7_1_3.block_append 879 197 197 1221 1024 52 1076 16949869782 10907442 16960777224 cost_879_197_join2_0 cost_879_197_block8 rfl rfl rfl

private theorem cost_879_197_total : P1_7_1_3.momentEstimate 879 197 = 16960777224 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 879 + 197 = 1076 by decide]
  exact cost_879_197_join3_0

theorem moment879_197 : P1_7_1.groupedPoleMoment 879 197 ≤ 16960777224 :=
  (P1_7_1_3.grouped_bound 879 197).trans_eq cost_879_197_total
private theorem cost_939_207_block0 : P1_7_1_3.blockEstimate 939 207 207 128 = 301860000 := by decide +kernel

private theorem cost_939_207_block1 : P1_7_1_3.blockEstimate 939 207 335 128 = 1799929924 := by decide +kernel

private theorem cost_939_207_block2 : P1_7_1_3.blockEstimate 939 207 463 128 = 3542755840 := by decide +kernel

private theorem cost_939_207_block3 : P1_7_1_3.blockEstimate 939 207 591 128 = 4478216704 := by decide +kernel

private theorem cost_939_207_block4 : P1_7_1_3.blockEstimate 939 207 719 128 = 4541262336 := by decide +kernel

private theorem cost_939_207_block5 : P1_7_1_3.blockEstimate 939 207 847 128 = 3734179118 := by decide +kernel

private theorem cost_939_207_block6 : P1_7_1_3.blockEstimate 939 207 975 128 = 2307396158 := by decide +kernel

private theorem cost_939_207_block7 : P1_7_1_3.blockEstimate 939 207 1103 128 = 949963705 := by decide +kernel

private theorem cost_939_207_block8 : P1_7_1_3.blockEstimate 939 207 1231 122 = 138507721 := by decide +kernel

private theorem cost_939_207_join0_0 : P1_7_1_3.blockEstimate 939 207 207 256 = 2101789924 :=
  @P1_7_1_3.block_append 939 207 207 335 128 128 256 301860000 1799929924 2101789924 cost_939_207_block0 cost_939_207_block1 rfl rfl rfl

private theorem cost_939_207_join0_2 : P1_7_1_3.blockEstimate 939 207 463 256 = 8020972544 :=
  @P1_7_1_3.block_append 939 207 463 591 128 128 256 3542755840 4478216704 8020972544 cost_939_207_block2 cost_939_207_block3 rfl rfl rfl

private theorem cost_939_207_join0_4 : P1_7_1_3.blockEstimate 939 207 719 256 = 8275441454 :=
  @P1_7_1_3.block_append 939 207 719 847 128 128 256 4541262336 3734179118 8275441454 cost_939_207_block4 cost_939_207_block5 rfl rfl rfl

private theorem cost_939_207_join0_6 : P1_7_1_3.blockEstimate 939 207 975 256 = 3257359863 :=
  @P1_7_1_3.block_append 939 207 975 1103 128 128 256 2307396158 949963705 3257359863 cost_939_207_block6 cost_939_207_block7 rfl rfl rfl

private theorem cost_939_207_join1_0 : P1_7_1_3.blockEstimate 939 207 207 512 = 10122762468 :=
  @P1_7_1_3.block_append 939 207 207 463 256 256 512 2101789924 8020972544 10122762468 cost_939_207_join0_0 cost_939_207_join0_2 rfl rfl rfl

private theorem cost_939_207_join1_2 : P1_7_1_3.blockEstimate 939 207 719 512 = 11532801317 :=
  @P1_7_1_3.block_append 939 207 719 975 256 256 512 8275441454 3257359863 11532801317 cost_939_207_join0_4 cost_939_207_join0_6 rfl rfl rfl

private theorem cost_939_207_join2_0 : P1_7_1_3.blockEstimate 939 207 207 1024 = 21655563785 :=
  @P1_7_1_3.block_append 939 207 207 719 512 512 1024 10122762468 11532801317 21655563785 cost_939_207_join1_0 cost_939_207_join1_2 rfl rfl rfl

private theorem cost_939_207_join3_0 : P1_7_1_3.blockEstimate 939 207 207 1146 = 21794071506 :=
  @P1_7_1_3.block_append 939 207 207 1231 1024 122 1146 21655563785 138507721 21794071506 cost_939_207_join2_0 cost_939_207_block8 rfl rfl rfl

private theorem cost_939_207_total : P1_7_1_3.momentEstimate 939 207 = 21794071506 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 939 + 207 = 1146 by decide]
  exact cost_939_207_join3_0

theorem moment939_207 : P1_7_1.groupedPoleMoment 939 207 ≤ 21794071506 :=
  (P1_7_1_3.grouped_bound 939 207).trans_eq cost_939_207_total
private theorem cost_939_209_block0 : P1_7_1_3.blockEstimate 939 209 209 128 = 301860000 := by decide +kernel

private theorem cost_939_209_block1 : P1_7_1_3.blockEstimate 939 209 337 128 = 1801541580 := by decide +kernel

private theorem cost_939_209_block2 : P1_7_1_3.blockEstimate 939 209 465 128 = 3560168640 := by decide +kernel

private theorem cost_939_209_block3 : P1_7_1_3.blockEstimate 939 209 593 128 = 4508064960 := by decide +kernel

private theorem cost_939_209_block4 : P1_7_1_3.blockEstimate 939 209 721 128 = 4575157440 := by decide +kernel

private theorem cost_939_209_block5 : P1_7_1_3.blockEstimate 939 209 849 128 = 3764121125 := by decide +kernel

private theorem cost_939_209_block6 : P1_7_1_3.blockEstimate 939 209 977 128 = 2332685997 := by decide +kernel

private theorem cost_939_209_block7 : P1_7_1_3.blockEstimate 939 209 1105 128 = 968196776 := by decide +kernel

private theorem cost_939_209_block8 : P1_7_1_3.blockEstimate 939 209 1233 124 = 145192530 := by decide +kernel

private theorem cost_939_209_join0_0 : P1_7_1_3.blockEstimate 939 209 209 256 = 2103401580 :=
  @P1_7_1_3.block_append 939 209 209 337 128 128 256 301860000 1801541580 2103401580 cost_939_209_block0 cost_939_209_block1 rfl rfl rfl

private theorem cost_939_209_join0_2 : P1_7_1_3.blockEstimate 939 209 465 256 = 8068233600 :=
  @P1_7_1_3.block_append 939 209 465 593 128 128 256 3560168640 4508064960 8068233600 cost_939_209_block2 cost_939_209_block3 rfl rfl rfl

private theorem cost_939_209_join0_4 : P1_7_1_3.blockEstimate 939 209 721 256 = 8339278565 :=
  @P1_7_1_3.block_append 939 209 721 849 128 128 256 4575157440 3764121125 8339278565 cost_939_209_block4 cost_939_209_block5 rfl rfl rfl

private theorem cost_939_209_join0_6 : P1_7_1_3.blockEstimate 939 209 977 256 = 3300882773 :=
  @P1_7_1_3.block_append 939 209 977 1105 128 128 256 2332685997 968196776 3300882773 cost_939_209_block6 cost_939_209_block7 rfl rfl rfl

private theorem cost_939_209_join1_0 : P1_7_1_3.blockEstimate 939 209 209 512 = 10171635180 :=
  @P1_7_1_3.block_append 939 209 209 465 256 256 512 2103401580 8068233600 10171635180 cost_939_209_join0_0 cost_939_209_join0_2 rfl rfl rfl

private theorem cost_939_209_join1_2 : P1_7_1_3.blockEstimate 939 209 721 512 = 11640161338 :=
  @P1_7_1_3.block_append 939 209 721 977 256 256 512 8339278565 3300882773 11640161338 cost_939_209_join0_4 cost_939_209_join0_6 rfl rfl rfl

private theorem cost_939_209_join2_0 : P1_7_1_3.blockEstimate 939 209 209 1024 = 21811796518 :=
  @P1_7_1_3.block_append 939 209 209 721 512 512 1024 10171635180 11640161338 21811796518 cost_939_209_join1_0 cost_939_209_join1_2 rfl rfl rfl

private theorem cost_939_209_join3_0 : P1_7_1_3.blockEstimate 939 209 209 1148 = 21956989048 :=
  @P1_7_1_3.block_append 939 209 209 1233 1024 124 1148 21811796518 145192530 21956989048 cost_939_209_join2_0 cost_939_209_block8 rfl rfl rfl

private theorem cost_939_209_total : P1_7_1_3.momentEstimate 939 209 = 21956989048 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 939 + 209 = 1148 by decide]
  exact cost_939_209_join3_0

theorem moment939_209 : P1_7_1.groupedPoleMoment 939 209 ≤ 21956989048 :=
  (P1_7_1_3.grouped_bound 939 209).trans_eq cost_939_209_total
private theorem cost_939_211_block0 : P1_7_1_3.blockEstimate 939 211 211 128 = 301860000 := by decide +kernel

private theorem cost_939_211_block1 : P1_7_1_3.blockEstimate 939 211 339 128 = 1803020319 := by decide +kernel

private theorem cost_939_211_block2 : P1_7_1_3.blockEstimate 939 211 467 128 = 3577264256 := by decide +kernel

private theorem cost_939_211_block3 : P1_7_1_3.blockEstimate 939 211 595 128 = 4537661568 := by decide +kernel

private theorem cost_939_211_block4 : P1_7_1_3.blockEstimate 939 211 723 128 = 4608866432 := by decide +kernel

private theorem cost_939_211_block5 : P1_7_1_3.blockEstimate 939 211 851 128 = 3793983265 := by decide +kernel

private theorem cost_939_211_block6 : P1_7_1_3.blockEstimate 939 211 979 128 = 2358059899 := by decide +kernel

private theorem cost_939_211_block7 : P1_7_1_3.blockEstimate 939 211 1107 128 = 986579362 := by decide +kernel

private theorem cost_939_211_block8 : P1_7_1_3.blockEstimate 939 211 1235 126 = 152083856 := by decide +kernel

private theorem cost_939_211_join0_0 : P1_7_1_3.blockEstimate 939 211 211 256 = 2104880319 :=
  @P1_7_1_3.block_append 939 211 211 339 128 128 256 301860000 1803020319 2104880319 cost_939_211_block0 cost_939_211_block1 rfl rfl rfl

private theorem cost_939_211_join0_2 : P1_7_1_3.blockEstimate 939 211 467 256 = 8114925824 :=
  @P1_7_1_3.block_append 939 211 467 595 128 128 256 3577264256 4537661568 8114925824 cost_939_211_block2 cost_939_211_block3 rfl rfl rfl

private theorem cost_939_211_join0_4 : P1_7_1_3.blockEstimate 939 211 723 256 = 8402849697 :=
  @P1_7_1_3.block_append 939 211 723 851 128 128 256 4608866432 3793983265 8402849697 cost_939_211_block4 cost_939_211_block5 rfl rfl rfl

private theorem cost_939_211_join0_6 : P1_7_1_3.blockEstimate 939 211 979 256 = 3344639261 :=
  @P1_7_1_3.block_append 939 211 979 1107 128 128 256 2358059899 986579362 3344639261 cost_939_211_block6 cost_939_211_block7 rfl rfl rfl

private theorem cost_939_211_join1_0 : P1_7_1_3.blockEstimate 939 211 211 512 = 10219806143 :=
  @P1_7_1_3.block_append 939 211 211 467 256 256 512 2104880319 8114925824 10219806143 cost_939_211_join0_0 cost_939_211_join0_2 rfl rfl rfl

private theorem cost_939_211_join1_2 : P1_7_1_3.blockEstimate 939 211 723 512 = 11747488958 :=
  @P1_7_1_3.block_append 939 211 723 979 256 256 512 8402849697 3344639261 11747488958 cost_939_211_join0_4 cost_939_211_join0_6 rfl rfl rfl

private theorem cost_939_211_join2_0 : P1_7_1_3.blockEstimate 939 211 211 1024 = 21967295101 :=
  @P1_7_1_3.block_append 939 211 211 723 512 512 1024 10219806143 11747488958 21967295101 cost_939_211_join1_0 cost_939_211_join1_2 rfl rfl rfl

private theorem cost_939_211_join3_0 : P1_7_1_3.blockEstimate 939 211 211 1150 = 22119378957 :=
  @P1_7_1_3.block_append 939 211 211 1235 1024 126 1150 21967295101 152083856 22119378957 cost_939_211_join2_0 cost_939_211_block8 rfl rfl rfl

private theorem cost_939_211_total : P1_7_1_3.momentEstimate 939 211 = 22119378957 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 939 + 211 = 1150 by decide]
  exact cost_939_211_join3_0

theorem moment939_211 : P1_7_1.groupedPoleMoment 939 211 ≤ 22119378957 :=
  (P1_7_1_3.grouped_bound 939 211).trans_eq cost_939_211_total

end Research6966.HelperRescueCatalogue

end Merged6967_Near6967RescueMoment8

section Merged6967_Near6967RescueMoment9
set_option Elab.async false


set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private theorem cost_941_201_block0 : P1_7_1_3.blockEstimate 941 201 201 128 = 302575520 := by decide +kernel

private theorem cost_941_201_block1 : P1_7_1_3.blockEstimate 941 201 329 128 = 1799126006 := by decide +kernel

private theorem cost_941_201_block2 : P1_7_1_3.blockEstimate 941 201 457 128 = 3499990976 := by decide +kernel

private theorem cost_941_201_block3 : P1_7_1_3.blockEstimate 941 201 585 128 = 4405157824 := by decide +kernel

private theorem cost_941_201_block4 : P1_7_1_3.blockEstimate 941 201 713 128 = 4463075264 := by decide +kernel

private theorem cost_941_201_block5 : P1_7_1_3.blockEstimate 941 201 841 128 = 3674840686 := by decide +kernel

private theorem cost_941_201_block6 : P1_7_1_3.blockEstimate 941 201 969 128 = 2261387287 := by decide +kernel

private theorem cost_941_201_block7 : P1_7_1_3.blockEstimate 941 201 1097 128 = 916017919 := by decide +kernel

private theorem cost_941_201_block8 : P1_7_1_3.blockEstimate 941 201 1225 118 = 126030645 := by decide +kernel

private theorem cost_941_201_join0_0 : P1_7_1_3.blockEstimate 941 201 201 256 = 2101701526 :=
  @P1_7_1_3.block_append 941 201 201 329 128 128 256 302575520 1799126006 2101701526 cost_941_201_block0 cost_941_201_block1 rfl rfl rfl

private theorem cost_941_201_join0_2 : P1_7_1_3.blockEstimate 941 201 457 256 = 7905148800 :=
  @P1_7_1_3.block_append 941 201 457 585 128 128 256 3499990976 4405157824 7905148800 cost_941_201_block2 cost_941_201_block3 rfl rfl rfl

private theorem cost_941_201_join0_4 : P1_7_1_3.blockEstimate 941 201 713 256 = 8137915950 :=
  @P1_7_1_3.block_append 941 201 713 841 128 128 256 4463075264 3674840686 8137915950 cost_941_201_block4 cost_941_201_block5 rfl rfl rfl

private theorem cost_941_201_join0_6 : P1_7_1_3.blockEstimate 941 201 969 256 = 3177405206 :=
  @P1_7_1_3.block_append 941 201 969 1097 128 128 256 2261387287 916017919 3177405206 cost_941_201_block6 cost_941_201_block7 rfl rfl rfl

private theorem cost_941_201_join1_0 : P1_7_1_3.blockEstimate 941 201 201 512 = 10006850326 :=
  @P1_7_1_3.block_append 941 201 201 457 256 256 512 2101701526 7905148800 10006850326 cost_941_201_join0_0 cost_941_201_join0_2 rfl rfl rfl

private theorem cost_941_201_join1_2 : P1_7_1_3.blockEstimate 941 201 713 512 = 11315321156 :=
  @P1_7_1_3.block_append 941 201 713 969 256 256 512 8137915950 3177405206 11315321156 cost_941_201_join0_4 cost_941_201_join0_6 rfl rfl rfl

private theorem cost_941_201_join2_0 : P1_7_1_3.blockEstimate 941 201 201 1024 = 21322171482 :=
  @P1_7_1_3.block_append 941 201 201 713 512 512 1024 10006850326 11315321156 21322171482 cost_941_201_join1_0 cost_941_201_join1_2 rfl rfl rfl

private theorem cost_941_201_join3_0 : P1_7_1_3.blockEstimate 941 201 201 1142 = 21448202127 :=
  @P1_7_1_3.block_append 941 201 201 1225 1024 118 1142 21322171482 126030645 21448202127 cost_941_201_join2_0 cost_941_201_block8 rfl rfl rfl

private theorem cost_941_201_total : P1_7_1_3.momentEstimate 941 201 = 21448202127 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 941 + 201 = 1142 by decide]
  exact cost_941_201_join3_0

theorem moment941_201 : P1_7_1.groupedPoleMoment 941 201 ≤ 21448202127 :=
  (P1_7_1_3.grouped_bound 941 201).trans_eq cost_941_201_total
private theorem cost_941_205_block0 : P1_7_1_3.blockEstimate 941 205 205 128 = 302575520 := by decide +kernel

private theorem cost_941_205_block1 : P1_7_1_3.blockEstimate 941 205 333 128 = 1803077891 := by decide +kernel

private theorem cost_941_205_block2 : P1_7_1_3.blockEstimate 941 205 461 128 = 3536522304 := by decide +kernel

private theorem cost_941_205_block3 : P1_7_1_3.blockEstimate 941 205 589 128 = 4466363456 := by decide +kernel

private theorem cost_941_205_block4 : P1_7_1_3.blockEstimate 941 205 717 128 = 4532177984 := by decide +kernel

private theorem cost_941_205_block5 : P1_7_1_3.blockEstimate 941 205 845 128 = 3735583909 := by decide +kernel

private theorem cost_941_205_block6 : P1_7_1_3.blockEstimate 941 205 973 128 = 2311851270 := by decide +kernel

private theorem cost_941_205_block7 : P1_7_1_3.blockEstimate 941 205 1101 128 = 952121093 := by decide +kernel

private theorem cost_941_205_block8 : P1_7_1_3.blockEstimate 941 205 1229 122 = 138821627 := by decide +kernel

private theorem cost_941_205_join0_0 : P1_7_1_3.blockEstimate 941 205 205 256 = 2105653411 :=
  @P1_7_1_3.block_append 941 205 205 333 128 128 256 302575520 1803077891 2105653411 cost_941_205_block0 cost_941_205_block1 rfl rfl rfl

private theorem cost_941_205_join0_2 : P1_7_1_3.blockEstimate 941 205 461 256 = 8002885760 :=
  @P1_7_1_3.block_append 941 205 461 589 128 128 256 3536522304 4466363456 8002885760 cost_941_205_block2 cost_941_205_block3 rfl rfl rfl

private theorem cost_941_205_join0_4 : P1_7_1_3.blockEstimate 941 205 717 256 = 8267761893 :=
  @P1_7_1_3.block_append 941 205 717 845 128 128 256 4532177984 3735583909 8267761893 cost_941_205_block4 cost_941_205_block5 rfl rfl rfl

private theorem cost_941_205_join0_6 : P1_7_1_3.blockEstimate 941 205 973 256 = 3263972363 :=
  @P1_7_1_3.block_append 941 205 973 1101 128 128 256 2311851270 952121093 3263972363 cost_941_205_block6 cost_941_205_block7 rfl rfl rfl

private theorem cost_941_205_join1_0 : P1_7_1_3.blockEstimate 941 205 205 512 = 10108539171 :=
  @P1_7_1_3.block_append 941 205 205 461 256 256 512 2105653411 8002885760 10108539171 cost_941_205_join0_0 cost_941_205_join0_2 rfl rfl rfl

private theorem cost_941_205_join1_2 : P1_7_1_3.blockEstimate 941 205 717 512 = 11531734256 :=
  @P1_7_1_3.block_append 941 205 717 973 256 256 512 8267761893 3263972363 11531734256 cost_941_205_join0_4 cost_941_205_join0_6 rfl rfl rfl

private theorem cost_941_205_join2_0 : P1_7_1_3.blockEstimate 941 205 205 1024 = 21640273427 :=
  @P1_7_1_3.block_append 941 205 205 717 512 512 1024 10108539171 11531734256 21640273427 cost_941_205_join1_0 cost_941_205_join1_2 rfl rfl rfl

private theorem cost_941_205_join3_0 : P1_7_1_3.blockEstimate 941 205 205 1146 = 21779095054 :=
  @P1_7_1_3.block_append 941 205 205 1229 1024 122 1146 21640273427 138821627 21779095054 cost_941_205_join2_0 cost_941_205_block8 rfl rfl rfl

private theorem cost_941_205_total : P1_7_1_3.momentEstimate 941 205 = 21779095054 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 941 + 205 = 1146 by decide]
  exact cost_941_205_join3_0

theorem moment941_205 : P1_7_1.groupedPoleMoment 941 205 ≤ 21779095054 :=
  (P1_7_1_3.grouped_bound 941 205).trans_eq cost_941_205_total
private theorem cost_941_207_block0 : P1_7_1_3.blockEstimate 941 207 207 128 = 302575520 := by decide +kernel

private theorem cost_941_207_block1 : P1_7_1_3.blockEstimate 941 207 335 128 = 1804833316 := by decide +kernel

private theorem cost_941_207_block2 : P1_7_1_3.blockEstimate 941 207 463 128 = 3554310656 := by decide +kernel

private theorem cost_941_207_block3 : P1_7_1_3.blockEstimate 941 207 591 128 = 4496587264 := by decide +kernel

private theorem cost_941_207_block4 : P1_7_1_3.blockEstimate 941 207 719 128 = 4566448640 := by decide +kernel

private theorem cost_941_207_block5 : P1_7_1_3.blockEstimate 941 207 847 128 = 3765824533 := by decide +kernel

private theorem cost_941_207_block6 : P1_7_1_3.blockEstimate 941 207 975 128 = 2337211926 := by decide +kernel

private theorem cost_941_207_block7 : P1_7_1_3.blockEstimate 941 207 1103 128 = 970399675 := by decide +kernel

private theorem cost_941_207_block8 : P1_7_1_3.blockEstimate 941 207 1231 124 = 145521936 := by decide +kernel

private theorem cost_941_207_join0_0 : P1_7_1_3.blockEstimate 941 207 207 256 = 2107408836 :=
  @P1_7_1_3.block_append 941 207 207 335 128 128 256 302575520 1804833316 2107408836 cost_941_207_block0 cost_941_207_block1 rfl rfl rfl

private theorem cost_941_207_join0_2 : P1_7_1_3.blockEstimate 941 207 463 256 = 8050897920 :=
  @P1_7_1_3.block_append 941 207 463 591 128 128 256 3554310656 4496587264 8050897920 cost_941_207_block2 cost_941_207_block3 rfl rfl rfl

private theorem cost_941_207_join0_4 : P1_7_1_3.blockEstimate 941 207 719 256 = 8332273173 :=
  @P1_7_1_3.block_append 941 207 719 847 128 128 256 4566448640 3765824533 8332273173 cost_941_207_block4 cost_941_207_block5 rfl rfl rfl

private theorem cost_941_207_join0_6 : P1_7_1_3.blockEstimate 941 207 975 256 = 3307611601 :=
  @P1_7_1_3.block_append 941 207 975 1103 128 128 256 2337211926 970399675 3307611601 cost_941_207_block6 cost_941_207_block7 rfl rfl rfl

private theorem cost_941_207_join1_0 : P1_7_1_3.blockEstimate 941 207 207 512 = 10158306756 :=
  @P1_7_1_3.block_append 941 207 207 463 256 256 512 2107408836 8050897920 10158306756 cost_941_207_join0_0 cost_941_207_join0_2 rfl rfl rfl

private theorem cost_941_207_join1_2 : P1_7_1_3.blockEstimate 941 207 719 512 = 11639884774 :=
  @P1_7_1_3.block_append 941 207 719 975 256 256 512 8332273173 3307611601 11639884774 cost_941_207_join0_4 cost_941_207_join0_6 rfl rfl rfl

private theorem cost_941_207_join2_0 : P1_7_1_3.blockEstimate 941 207 207 1024 = 21798191530 :=
  @P1_7_1_3.block_append 941 207 207 719 512 512 1024 10158306756 11639884774 21798191530 cost_941_207_join1_0 cost_941_207_join1_2 rfl rfl rfl

private theorem cost_941_207_join3_0 : P1_7_1_3.blockEstimate 941 207 207 1148 = 21943713466 :=
  @P1_7_1_3.block_append 941 207 207 1231 1024 124 1148 21798191530 145521936 21943713466 cost_941_207_join2_0 cost_941_207_block8 rfl rfl rfl

private theorem cost_941_207_total : P1_7_1_3.momentEstimate 941 207 = 21943713466 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 941 + 207 = 1148 by decide]
  exact cost_941_207_join3_0

theorem moment941_207 : P1_7_1.groupedPoleMoment 941 207 ≤ 21943713466 :=
  (P1_7_1_3.grouped_bound 941 207).trans_eq cost_941_207_total
private theorem cost_941_209_block0 : P1_7_1_3.blockEstimate 941 209 209 128 = 302575520 := by decide +kernel

private theorem cost_941_209_block1 : P1_7_1_3.blockEstimate 941 209 337 128 = 1806449580 := by decide +kernel

private theorem cost_941_209_block2 : P1_7_1_3.blockEstimate 941 209 465 128 = 3571780800 := by decide +kernel

private theorem cost_941_209_block3 : P1_7_1_3.blockEstimate 941 209 593 128 = 4526558400 := by decide +kernel

private theorem cost_941_209_block4 : P1_7_1_3.blockEstimate 941 209 721 128 = 4600532160 := by decide +kernel

private theorem cost_941_209_block5 : P1_7_1_3.blockEstimate 941 209 849 128 = 3795980384 := by decide +kernel

private theorem cost_941_209_block6 : P1_7_1_3.blockEstimate 941 209 977 128 = 2362657106 := by decide +kernel

private theorem cost_941_209_block7 : P1_7_1_3.blockEstimate 941 209 1105 128 = 988828269 := by decide +kernel

private theorem cost_941_209_block8 : P1_7_1_3.blockEstimate 941 209 1233 126 = 152429264 := by decide +kernel

private theorem cost_941_209_join0_0 : P1_7_1_3.blockEstimate 941 209 209 256 = 2109025100 :=
  @P1_7_1_3.block_append 941 209 209 337 128 128 256 302575520 1806449580 2109025100 cost_941_209_block0 cost_941_209_block1 rfl rfl rfl

private theorem cost_941_209_join0_2 : P1_7_1_3.blockEstimate 941 209 465 256 = 8098339200 :=
  @P1_7_1_3.block_append 941 209 465 593 128 128 256 3571780800 4526558400 8098339200 cost_941_209_block2 cost_941_209_block3 rfl rfl rfl

private theorem cost_941_209_join0_4 : P1_7_1_3.blockEstimate 941 209 721 256 = 8396512544 :=
  @P1_7_1_3.block_append 941 209 721 849 128 128 256 4600532160 3795980384 8396512544 cost_941_209_block4 cost_941_209_block5 rfl rfl rfl

private theorem cost_941_209_join0_6 : P1_7_1_3.blockEstimate 941 209 977 256 = 3351485375 :=
  @P1_7_1_3.block_append 941 209 977 1105 128 128 256 2362657106 988828269 3351485375 cost_941_209_block6 cost_941_209_block7 rfl rfl rfl

private theorem cost_941_209_join1_0 : P1_7_1_3.blockEstimate 941 209 209 512 = 10207364300 :=
  @P1_7_1_3.block_append 941 209 209 465 256 256 512 2109025100 8098339200 10207364300 cost_941_209_join0_0 cost_941_209_join0_2 rfl rfl rfl

private theorem cost_941_209_join1_2 : P1_7_1_3.blockEstimate 941 209 721 512 = 11747997919 :=
  @P1_7_1_3.block_append 941 209 721 977 256 256 512 8396512544 3351485375 11747997919 cost_941_209_join0_4 cost_941_209_join0_6 rfl rfl rfl

private theorem cost_941_209_join2_0 : P1_7_1_3.blockEstimate 941 209 209 1024 = 21955362219 :=
  @P1_7_1_3.block_append 941 209 209 721 512 512 1024 10207364300 11747997919 21955362219 cost_941_209_join1_0 cost_941_209_join1_2 rfl rfl rfl

private theorem cost_941_209_join3_0 : P1_7_1_3.blockEstimate 941 209 209 1150 = 22107791483 :=
  @P1_7_1_3.block_append 941 209 209 1233 1024 126 1150 21955362219 152429264 22107791483 cost_941_209_join2_0 cost_941_209_block8 rfl rfl rfl

private theorem cost_941_209_total : P1_7_1_3.momentEstimate 941 209 = 22107791483 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 941 + 209 = 1150 by decide]
  exact cost_941_209_join3_0

theorem moment941_209 : P1_7_1.groupedPoleMoment 941 209 ≤ 22107791483 :=
  (P1_7_1_3.grouped_bound 941 209).trans_eq cost_941_209_total
private theorem cost_942_202_block0 : P1_7_1_3.blockEstimate 942 202 202 128 = 302933280 := by decide +kernel

private theorem cost_942_202_block1 : P1_7_1_3.blockEstimate 942 202 330 128 = 1802616012 := by decide +kernel

private theorem cost_942_202_block2 : P1_7_1_3.blockEstimate 942 202 458 128 = 3514946624 := by decide +kernel

private theorem cost_942_202_block3 : P1_7_1_3.blockEstimate 942 202 586 128 = 4429583424 := by decide +kernel

private theorem cost_942_202_block4 : P1_7_1_3.blockEstimate 942 202 714 128 = 4492776512 := by decide +kernel

private theorem cost_942_202_block5 : P1_7_1_3.blockEstimate 942 202 842 128 = 3705621353 := by decide +kernel

private theorem cost_942_202_block6 : P1_7_1_3.blockEstimate 942 202 970 128 = 2288753734 := by decide +kernel

private theorem cost_942_202_block7 : P1_7_1_3.blockEstimate 942 202 1098 128 = 935046384 := by decide +kernel

private theorem cost_942_202_block8 : P1_7_1_3.blockEstimate 942 202 1226 120 = 132474920 := by decide +kernel

private theorem cost_942_202_join0_0 : P1_7_1_3.blockEstimate 942 202 202 256 = 2105549292 :=
  @P1_7_1_3.block_append 942 202 202 330 128 128 256 302933280 1802616012 2105549292 cost_942_202_block0 cost_942_202_block1 rfl rfl rfl

private theorem cost_942_202_join0_2 : P1_7_1_3.blockEstimate 942 202 458 256 = 7944530048 :=
  @P1_7_1_3.block_append 942 202 458 586 128 128 256 3514946624 4429583424 7944530048 cost_942_202_block2 cost_942_202_block3 rfl rfl rfl

private theorem cost_942_202_join0_4 : P1_7_1_3.blockEstimate 942 202 714 256 = 8198397865 :=
  @P1_7_1_3.block_append 942 202 714 842 128 128 256 4492776512 3705621353 8198397865 cost_942_202_block4 cost_942_202_block5 rfl rfl rfl

private theorem cost_942_202_join0_6 : P1_7_1_3.blockEstimate 942 202 970 256 = 3223800118 :=
  @P1_7_1_3.block_append 942 202 970 1098 128 128 256 2288753734 935046384 3223800118 cost_942_202_block6 cost_942_202_block7 rfl rfl rfl

private theorem cost_942_202_join1_0 : P1_7_1_3.blockEstimate 942 202 202 512 = 10050079340 :=
  @P1_7_1_3.block_append 942 202 202 458 256 256 512 2105549292 7944530048 10050079340 cost_942_202_join0_0 cost_942_202_join0_2 rfl rfl rfl

private theorem cost_942_202_join1_2 : P1_7_1_3.blockEstimate 942 202 714 512 = 11422197983 :=
  @P1_7_1_3.block_append 942 202 714 970 256 256 512 8198397865 3223800118 11422197983 cost_942_202_join0_4 cost_942_202_join0_6 rfl rfl rfl

private theorem cost_942_202_join2_0 : P1_7_1_3.blockEstimate 942 202 202 1024 = 21472277323 :=
  @P1_7_1_3.block_append 942 202 202 714 512 512 1024 10050079340 11422197983 21472277323 cost_942_202_join1_0 cost_942_202_join1_2 rfl rfl rfl

private theorem cost_942_202_join3_0 : P1_7_1_3.blockEstimate 942 202 202 1144 = 21604752243 :=
  @P1_7_1_3.block_append 942 202 202 1226 1024 120 1144 21472277323 132474920 21604752243 cost_942_202_join2_0 cost_942_202_block8 rfl rfl rfl

private theorem cost_942_202_total : P1_7_1_3.momentEstimate 942 202 = 21604752243 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 942 + 202 = 1144 by decide]
  exact cost_942_202_join3_0

theorem moment942_202 : P1_7_1.groupedPoleMoment 942 202 ≤ 21604752243 :=
  (P1_7_1_3.grouped_bound 942 202).trans_eq cost_942_202_total
private theorem cost_994_217_block0 : P1_7_1_3.blockEstimate 994 217 217 128 = 321536800 := by decide +kernel

private theorem cost_994_217_block1 : P1_7_1_3.blockEstimate 994 217 345 128 = 1942095194 := by decide +kernel

private theorem cost_994_217_block2 : P1_7_1_3.blockEstimate 994 217 473 128 = 3952008640 := by decide +kernel

private theorem cost_994_217_block3 : P1_7_1_3.blockEstimate 994 217 601 128 = 5146746304 := by decide +kernel

private theorem cost_994_217_block4 : P1_7_1_3.blockEstimate 994 217 729 128 = 5427125696 := by decide +kernel

private theorem cost_994_217_block5 : P1_7_1_3.blockEstimate 994 217 857 128 = 4793146816 := by decide +kernel

private theorem cost_994_217_block6 : P1_7_1_3.blockEstimate 994 217 985 128 = 3342780376 := by decide +kernel

private theorem cost_994_217_block7 : P1_7_1_3.blockEstimate 994 217 1113 128 = 1715617210 := by decide +kernel

private theorem cost_994_217_block8 : P1_7_1_3.blockEstimate 994 217 1241 128 = 488389696 := by decide +kernel

private theorem cost_994_217_block9 : P1_7_1_3.blockEstimate 994 217 1369 59 = 17836400 := by decide +kernel

private theorem cost_994_217_join0_0 : P1_7_1_3.blockEstimate 994 217 217 256 = 2263631994 :=
  @P1_7_1_3.block_append 994 217 217 345 128 128 256 321536800 1942095194 2263631994 cost_994_217_block0 cost_994_217_block1 rfl rfl rfl

private theorem cost_994_217_join0_2 : P1_7_1_3.blockEstimate 994 217 473 256 = 9098754944 :=
  @P1_7_1_3.block_append 994 217 473 601 128 128 256 3952008640 5146746304 9098754944 cost_994_217_block2 cost_994_217_block3 rfl rfl rfl

private theorem cost_994_217_join0_4 : P1_7_1_3.blockEstimate 994 217 729 256 = 10220272512 :=
  @P1_7_1_3.block_append 994 217 729 857 128 128 256 5427125696 4793146816 10220272512 cost_994_217_block4 cost_994_217_block5 rfl rfl rfl

private theorem cost_994_217_join0_6 : P1_7_1_3.blockEstimate 994 217 985 256 = 5058397586 :=
  @P1_7_1_3.block_append 994 217 985 1113 128 128 256 3342780376 1715617210 5058397586 cost_994_217_block6 cost_994_217_block7 rfl rfl rfl

private theorem cost_994_217_join0_8 : P1_7_1_3.blockEstimate 994 217 1241 187 = 506226096 :=
  @P1_7_1_3.block_append 994 217 1241 1369 128 59 187 488389696 17836400 506226096 cost_994_217_block8 cost_994_217_block9 rfl rfl rfl

private theorem cost_994_217_join1_0 : P1_7_1_3.blockEstimate 994 217 217 512 = 11362386938 :=
  @P1_7_1_3.block_append 994 217 217 473 256 256 512 2263631994 9098754944 11362386938 cost_994_217_join0_0 cost_994_217_join0_2 rfl rfl rfl

private theorem cost_994_217_join1_2 : P1_7_1_3.blockEstimate 994 217 729 512 = 15278670098 :=
  @P1_7_1_3.block_append 994 217 729 985 256 256 512 10220272512 5058397586 15278670098 cost_994_217_join0_4 cost_994_217_join0_6 rfl rfl rfl

private theorem cost_994_217_join2_0 : P1_7_1_3.blockEstimate 994 217 217 1024 = 26641057036 :=
  @P1_7_1_3.block_append 994 217 217 729 512 512 1024 11362386938 15278670098 26641057036 cost_994_217_join1_0 cost_994_217_join1_2 rfl rfl rfl

private theorem cost_994_217_join3_0 : P1_7_1_3.blockEstimate 994 217 217 1211 = 27147283132 :=
  @P1_7_1_3.block_append 994 217 217 1241 1024 187 1211 26641057036 506226096 27147283132 cost_994_217_join2_0 cost_994_217_join0_8 rfl rfl rfl

private theorem cost_994_217_total : P1_7_1_3.momentEstimate 994 217 = 27147283132 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 994 + 217 = 1211 by decide]
  exact cost_994_217_join3_0

theorem moment994_217 : P1_7_1.groupedPoleMoment 994 217 ≤ 27147283132 :=
  (P1_7_1_3.grouped_bound 994 217).trans_eq cost_994_217_total
private theorem cost_994_220_block0 : P1_7_1_3.blockEstimate 994 220 220 128 = 321536800 := by decide +kernel

private theorem cost_994_220_block1 : P1_7_1_3.blockEstimate 994 220 348 128 = 1943679829 := by decide +kernel

private theorem cost_994_220_block2 : P1_7_1_3.blockEstimate 994 220 476 128 = 3977773696 := by decide +kernel

private theorem cost_994_220_block3 : P1_7_1_3.blockEstimate 994 220 604 128 = 5194384000 := by decide +kernel

private theorem cost_994_220_block4 : P1_7_1_3.blockEstimate 994 220 732 128 = 5484053120 := by decide +kernel

private theorem cost_994_220_block5 : P1_7_1_3.blockEstimate 994 220 860 128 = 4846781056 := by decide +kernel

private theorem cost_994_220_block6 : P1_7_1_3.blockEstimate 994 220 988 128 = 3387675048 := by decide +kernel

private theorem cost_994_220_block7 : P1_7_1_3.blockEstimate 994 220 1116 128 = 1752020196 := by decide +kernel

private theorem cost_994_220_block8 : P1_7_1_3.blockEstimate 994 220 1244 128 = 509366256 := by decide +kernel

private theorem cost_994_220_block9 : P1_7_1_3.blockEstimate 994 220 1372 62 = 20594296 := by decide +kernel

private theorem cost_994_220_join0_0 : P1_7_1_3.blockEstimate 994 220 220 256 = 2265216629 :=
  @P1_7_1_3.block_append 994 220 220 348 128 128 256 321536800 1943679829 2265216629 cost_994_220_block0 cost_994_220_block1 rfl rfl rfl

private theorem cost_994_220_join0_2 : P1_7_1_3.blockEstimate 994 220 476 256 = 9172157696 :=
  @P1_7_1_3.block_append 994 220 476 604 128 128 256 3977773696 5194384000 9172157696 cost_994_220_block2 cost_994_220_block3 rfl rfl rfl

private theorem cost_994_220_join0_4 : P1_7_1_3.blockEstimate 994 220 732 256 = 10330834176 :=
  @P1_7_1_3.block_append 994 220 732 860 128 128 256 5484053120 4846781056 10330834176 cost_994_220_block4 cost_994_220_block5 rfl rfl rfl

private theorem cost_994_220_join0_6 : P1_7_1_3.blockEstimate 994 220 988 256 = 5139695244 :=
  @P1_7_1_3.block_append 994 220 988 1116 128 128 256 3387675048 1752020196 5139695244 cost_994_220_block6 cost_994_220_block7 rfl rfl rfl

private theorem cost_994_220_join0_8 : P1_7_1_3.blockEstimate 994 220 1244 190 = 529960552 :=
  @P1_7_1_3.block_append 994 220 1244 1372 128 62 190 509366256 20594296 529960552 cost_994_220_block8 cost_994_220_block9 rfl rfl rfl

private theorem cost_994_220_join1_0 : P1_7_1_3.blockEstimate 994 220 220 512 = 11437374325 :=
  @P1_7_1_3.block_append 994 220 220 476 256 256 512 2265216629 9172157696 11437374325 cost_994_220_join0_0 cost_994_220_join0_2 rfl rfl rfl

private theorem cost_994_220_join1_2 : P1_7_1_3.blockEstimate 994 220 732 512 = 15470529420 :=
  @P1_7_1_3.block_append 994 220 732 988 256 256 512 10330834176 5139695244 15470529420 cost_994_220_join0_4 cost_994_220_join0_6 rfl rfl rfl

private theorem cost_994_220_join2_0 : P1_7_1_3.blockEstimate 994 220 220 1024 = 26907903745 :=
  @P1_7_1_3.block_append 994 220 220 732 512 512 1024 11437374325 15470529420 26907903745 cost_994_220_join1_0 cost_994_220_join1_2 rfl rfl rfl

private theorem cost_994_220_join3_0 : P1_7_1_3.blockEstimate 994 220 220 1214 = 27437864297 :=
  @P1_7_1_3.block_append 994 220 220 1244 1024 190 1214 26907903745 529960552 27437864297 cost_994_220_join2_0 cost_994_220_join0_8 rfl rfl rfl

private theorem cost_994_220_total : P1_7_1_3.momentEstimate 994 220 = 27437864297 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 994 + 220 = 1214 by decide]
  exact cost_994_220_join3_0

theorem moment994_220 : P1_7_1.groupedPoleMoment 994 220 ≤ 27437864297 :=
  (P1_7_1_3.grouped_bound 994 220).trans_eq cost_994_220_total
private theorem cost_995_217_block0 : P1_7_1_3.blockEstimate 995 217 217 128 = 321894560 := by decide +kernel

private theorem cost_995_217_block1 : P1_7_1_3.blockEstimate 995 217 345 128 = 1944556610 := by decide +kernel

private theorem cost_995_217_block2 : P1_7_1_3.blockEstimate 995 217 473 128 = 3957924288 := by decide +kernel

private theorem cost_995_217_block3 : P1_7_1_3.blockEstimate 995 217 601 128 = 5156233664 := by decide +kernel

private theorem cost_995_217_block4 : P1_7_1_3.blockEstimate 995 217 729 128 = 5440184768 := by decide +kernel

private theorem cost_995_217_block5 : P1_7_1_3.blockEstimate 995 217 857 128 = 4809777600 := by decide +kernel

private theorem cost_995_217_block6 : P1_7_1_3.blockEstimate 995 217 985 128 = 3360537764 := by decide +kernel

private theorem cost_995_217_block7 : P1_7_1_3.blockEstimate 995 217 1113 128 = 1729463038 := by decide +kernel

private theorem cost_995_217_block8 : P1_7_1_3.blockEstimate 995 217 1241 128 = 495880960 := by decide +kernel

private theorem cost_995_217_block9 : P1_7_1_3.blockEstimate 995 217 1369 60 = 18746010 := by decide +kernel

private theorem cost_995_217_join0_0 : P1_7_1_3.blockEstimate 995 217 217 256 = 2266451170 :=
  @P1_7_1_3.block_append 995 217 217 345 128 128 256 321894560 1944556610 2266451170 cost_995_217_block0 cost_995_217_block1 rfl rfl rfl

private theorem cost_995_217_join0_2 : P1_7_1_3.blockEstimate 995 217 473 256 = 9114157952 :=
  @P1_7_1_3.block_append 995 217 473 601 128 128 256 3957924288 5156233664 9114157952 cost_995_217_block2 cost_995_217_block3 rfl rfl rfl

private theorem cost_995_217_join0_4 : P1_7_1_3.blockEstimate 995 217 729 256 = 10249962368 :=
  @P1_7_1_3.block_append 995 217 729 857 128 128 256 5440184768 4809777600 10249962368 cost_995_217_block4 cost_995_217_block5 rfl rfl rfl

private theorem cost_995_217_join0_6 : P1_7_1_3.blockEstimate 995 217 985 256 = 5090000802 :=
  @P1_7_1_3.block_append 995 217 985 1113 128 128 256 3360537764 1729463038 5090000802 cost_995_217_block6 cost_995_217_block7 rfl rfl rfl

private theorem cost_995_217_join0_8 : P1_7_1_3.blockEstimate 995 217 1241 188 = 514626970 :=
  @P1_7_1_3.block_append 995 217 1241 1369 128 60 188 495880960 18746010 514626970 cost_995_217_block8 cost_995_217_block9 rfl rfl rfl

private theorem cost_995_217_join1_0 : P1_7_1_3.blockEstimate 995 217 217 512 = 11380609122 :=
  @P1_7_1_3.block_append 995 217 217 473 256 256 512 2266451170 9114157952 11380609122 cost_995_217_join0_0 cost_995_217_join0_2 rfl rfl rfl

private theorem cost_995_217_join1_2 : P1_7_1_3.blockEstimate 995 217 729 512 = 15339963170 :=
  @P1_7_1_3.block_append 995 217 729 985 256 256 512 10249962368 5090000802 15339963170 cost_995_217_join0_4 cost_995_217_join0_6 rfl rfl rfl

private theorem cost_995_217_join2_0 : P1_7_1_3.blockEstimate 995 217 217 1024 = 26720572292 :=
  @P1_7_1_3.block_append 995 217 217 729 512 512 1024 11380609122 15339963170 26720572292 cost_995_217_join1_0 cost_995_217_join1_2 rfl rfl rfl

private theorem cost_995_217_join3_0 : P1_7_1_3.blockEstimate 995 217 217 1212 = 27235199262 :=
  @P1_7_1_3.block_append 995 217 217 1241 1024 188 1212 26720572292 514626970 27235199262 cost_995_217_join2_0 cost_995_217_join0_8 rfl rfl rfl

private theorem cost_995_217_total : P1_7_1_3.momentEstimate 995 217 = 27235199262 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 995 + 217 = 1212 by decide]
  exact cost_995_217_join3_0

theorem moment995_217 : P1_7_1.groupedPoleMoment 995 217 ≤ 27235199262 :=
  (P1_7_1_3.grouped_bound 995 217).trans_eq cost_995_217_total
private theorem cost_1044_228_block0 : P1_7_1_3.blockEstimate 1044 228 228 128 = 339424800 := by decide +kernel

private theorem cost_1044_228_block1 : P1_7_1_3.blockEstimate 1044 228 356 128 = 2070145947 := by decide +kernel

private theorem cost_1044_228_block2 : P1_7_1_3.blockEstimate 1044 228 484 128 = 4345328128 := by decide +kernel

private theorem cost_1044_228_block3 : P1_7_1_3.blockEstimate 1044 228 612 128 = 5808583168 := by decide +kernel

private theorem cost_1044_228_block4 : P1_7_1_3.blockEstimate 1044 228 740 128 = 6311342592 := by decide +kernel

private theorem cost_1044_228_block5 : P1_7_1_3.blockEstimate 1044 228 868 128 = 5853606400 := by decide +kernel

private theorem cost_1044_228_block6 : P1_7_1_3.blockEstimate 1044 228 996 128 = 4464749704 := by decide +kernel

private theorem cost_1044_228_block7 : P1_7_1_3.blockEstimate 1044 228 1124 128 = 2637419527 := by decide +kernel

private theorem cost_1044_228_block8 : P1_7_1_3.blockEstimate 1044 228 1252 128 = 1053513697 := by decide +kernel

private theorem cost_1044_228_block9 : P1_7_1_3.blockEstimate 1044 228 1380 120 = 147718820 := by decide +kernel

private theorem cost_1044_228_join0_0 : P1_7_1_3.blockEstimate 1044 228 228 256 = 2409570747 :=
  @P1_7_1_3.block_append 1044 228 228 356 128 128 256 339424800 2070145947 2409570747 cost_1044_228_block0 cost_1044_228_block1 rfl rfl rfl

private theorem cost_1044_228_join0_2 : P1_7_1_3.blockEstimate 1044 228 484 256 = 10153911296 :=
  @P1_7_1_3.block_append 1044 228 484 612 128 128 256 4345328128 5808583168 10153911296 cost_1044_228_block2 cost_1044_228_block3 rfl rfl rfl

private theorem cost_1044_228_join0_4 : P1_7_1_3.blockEstimate 1044 228 740 256 = 12164948992 :=
  @P1_7_1_3.block_append 1044 228 740 868 128 128 256 6311342592 5853606400 12164948992 cost_1044_228_block4 cost_1044_228_block5 rfl rfl rfl

private theorem cost_1044_228_join0_6 : P1_7_1_3.blockEstimate 1044 228 996 256 = 7102169231 :=
  @P1_7_1_3.block_append 1044 228 996 1124 128 128 256 4464749704 2637419527 7102169231 cost_1044_228_block6 cost_1044_228_block7 rfl rfl rfl

private theorem cost_1044_228_join0_8 : P1_7_1_3.blockEstimate 1044 228 1252 248 = 1201232517 :=
  @P1_7_1_3.block_append 1044 228 1252 1380 128 120 248 1053513697 147718820 1201232517 cost_1044_228_block8 cost_1044_228_block9 rfl rfl rfl

private theorem cost_1044_228_join1_0 : P1_7_1_3.blockEstimate 1044 228 228 512 = 12563482043 :=
  @P1_7_1_3.block_append 1044 228 228 484 256 256 512 2409570747 10153911296 12563482043 cost_1044_228_join0_0 cost_1044_228_join0_2 rfl rfl rfl

private theorem cost_1044_228_join1_2 : P1_7_1_3.blockEstimate 1044 228 740 512 = 19267118223 :=
  @P1_7_1_3.block_append 1044 228 740 996 256 256 512 12164948992 7102169231 19267118223 cost_1044_228_join0_4 cost_1044_228_join0_6 rfl rfl rfl

private theorem cost_1044_228_join2_0 : P1_7_1_3.blockEstimate 1044 228 228 1024 = 31830600266 :=
  @P1_7_1_3.block_append 1044 228 228 740 512 512 1024 12563482043 19267118223 31830600266 cost_1044_228_join1_0 cost_1044_228_join1_2 rfl rfl rfl

private theorem cost_1044_228_join3_0 : P1_7_1_3.blockEstimate 1044 228 228 1272 = 33031832783 :=
  @P1_7_1_3.block_append 1044 228 228 1252 1024 248 1272 31830600266 1201232517 33031832783 cost_1044_228_join2_0 cost_1044_228_join0_8 rfl rfl rfl

private theorem cost_1044_228_total : P1_7_1_3.momentEstimate 1044 228 = 33031832783 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1044 + 228 = 1272 by decide]
  exact cost_1044_228_join3_0

theorem moment1044_228 : P1_7_1.groupedPoleMoment 1044 228 ≤ 33031832783 :=
  (P1_7_1_3.grouped_bound 1044 228).trans_eq cost_1044_228_total
private theorem cost_1044_232_block0 : P1_7_1_3.blockEstimate 1044 232 232 128 = 339424800 := by decide +kernel

private theorem cost_1044_232_block1 : P1_7_1_3.blockEstimate 1044 232 360 128 = 2071225354 := by decide +kernel

private theorem cost_1044_232_block2 : P1_7_1_3.blockEstimate 1044 232 488 128 = 4378014080 := by decide +kernel

private theorem cost_1044_232_block3 : P1_7_1_3.blockEstimate 1044 232 616 128 = 5874463104 := by decide +kernel

private theorem cost_1044_232_block4 : P1_7_1_3.blockEstimate 1044 232 744 128 = 6393639296 := by decide +kernel

private theorem cost_1044_232_block5 : P1_7_1_3.blockEstimate 1044 232 872 128 = 5935542656 := by decide +kernel

private theorem cost_1044_232_block6 : P1_7_1_3.blockEstimate 1044 232 1000 128 = 4533964541 := by decide +kernel

private theorem cost_1044_232_block7 : P1_7_1_3.blockEstimate 1044 232 1128 128 = 2696645771 := by decide +kernel

private theorem cost_1044_232_block8 : P1_7_1_3.blockEstimate 1044 232 1256 128 = 1094914216 := by decide +kernel

private theorem cost_1044_232_block9 : P1_7_1_3.blockEstimate 1044 232 1384 124 = 162486345 := by decide +kernel

private theorem cost_1044_232_join0_0 : P1_7_1_3.blockEstimate 1044 232 232 256 = 2410650154 :=
  @P1_7_1_3.block_append 1044 232 232 360 128 128 256 339424800 2071225354 2410650154 cost_1044_232_block0 cost_1044_232_block1 rfl rfl rfl

private theorem cost_1044_232_join0_2 : P1_7_1_3.blockEstimate 1044 232 488 256 = 10252477184 :=
  @P1_7_1_3.block_append 1044 232 488 616 128 128 256 4378014080 5874463104 10252477184 cost_1044_232_block2 cost_1044_232_block3 rfl rfl rfl

private theorem cost_1044_232_join0_4 : P1_7_1_3.blockEstimate 1044 232 744 256 = 12329181952 :=
  @P1_7_1_3.block_append 1044 232 744 872 128 128 256 6393639296 5935542656 12329181952 cost_1044_232_block4 cost_1044_232_block5 rfl rfl rfl

private theorem cost_1044_232_join0_6 : P1_7_1_3.blockEstimate 1044 232 1000 256 = 7230610312 :=
  @P1_7_1_3.block_append 1044 232 1000 1128 128 128 256 4533964541 2696645771 7230610312 cost_1044_232_block6 cost_1044_232_block7 rfl rfl rfl

private theorem cost_1044_232_join0_8 : P1_7_1_3.blockEstimate 1044 232 1256 252 = 1257400561 :=
  @P1_7_1_3.block_append 1044 232 1256 1384 128 124 252 1094914216 162486345 1257400561 cost_1044_232_block8 cost_1044_232_block9 rfl rfl rfl

private theorem cost_1044_232_join1_0 : P1_7_1_3.blockEstimate 1044 232 232 512 = 12663127338 :=
  @P1_7_1_3.block_append 1044 232 232 488 256 256 512 2410650154 10252477184 12663127338 cost_1044_232_join0_0 cost_1044_232_join0_2 rfl rfl rfl

private theorem cost_1044_232_join1_2 : P1_7_1_3.blockEstimate 1044 232 744 512 = 19559792264 :=
  @P1_7_1_3.block_append 1044 232 744 1000 256 256 512 12329181952 7230610312 19559792264 cost_1044_232_join0_4 cost_1044_232_join0_6 rfl rfl rfl

private theorem cost_1044_232_join2_0 : P1_7_1_3.blockEstimate 1044 232 232 1024 = 32222919602 :=
  @P1_7_1_3.block_append 1044 232 232 744 512 512 1024 12663127338 19559792264 32222919602 cost_1044_232_join1_0 cost_1044_232_join1_2 rfl rfl rfl

private theorem cost_1044_232_join3_0 : P1_7_1_3.blockEstimate 1044 232 232 1276 = 33480320163 :=
  @P1_7_1_3.block_append 1044 232 232 1256 1024 252 1276 32222919602 1257400561 33480320163 cost_1044_232_join2_0 cost_1044_232_join0_8 rfl rfl rfl

private theorem cost_1044_232_total : P1_7_1_3.momentEstimate 1044 232 = 33480320163 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1044 + 232 = 1276 by decide]
  exact cost_1044_232_join3_0

theorem moment1044_232 : P1_7_1.groupedPoleMoment 1044 232 ≤ 33480320163 :=
  (P1_7_1_3.grouped_bound 1044 232).trans_eq cost_1044_232_total
private theorem cost_1045_234_block0 : P1_7_1_3.blockEstimate 1045 234 234 128 = 339782560 := by decide +kernel

private theorem cost_1045_234_block1 : P1_7_1_3.blockEstimate 1045 234 362 128 = 2074116055 := by decide +kernel

private theorem cost_1045_234_block2 : P1_7_1_3.blockEstimate 1045 234 490 128 = 4399921920 := by decide +kernel

private theorem cost_1045_234_block3 : P1_7_1_3.blockEstimate 1045 234 618 128 = 5916916480 := by decide +kernel

private theorem cost_1045_234_block4 : P1_7_1_3.blockEstimate 1045 234 746 128 = 6448249600 := by decide +kernel

private theorem cost_1045_234_block5 : P1_7_1_3.blockEstimate 1045 234 874 128 = 5993921280 := by decide +kernel

private theorem cost_1045_234_block6 : P1_7_1_3.blockEstimate 1045 234 1002 128 = 4588837507 := by decide +kernel

private theorem cost_1045_234_block7 : P1_7_1_3.blockEstimate 1045 234 1130 128 = 2743869357 := by decide +kernel

private theorem cost_1045_234_block8 : P1_7_1_3.blockEstimate 1045 234 1258 128 = 1127616346 := by decide +kernel

private theorem cost_1045_234_block9 : P1_7_1_3.blockEstimate 1045 234 1386 127 = 174348736 := by decide +kernel

private theorem cost_1045_234_join0_0 : P1_7_1_3.blockEstimate 1045 234 234 256 = 2413898615 :=
  @P1_7_1_3.block_append 1045 234 234 362 128 128 256 339782560 2074116055 2413898615 cost_1045_234_block0 cost_1045_234_block1 rfl rfl rfl

private theorem cost_1045_234_join0_2 : P1_7_1_3.blockEstimate 1045 234 490 256 = 10316838400 :=
  @P1_7_1_3.block_append 1045 234 490 618 128 128 256 4399921920 5916916480 10316838400 cost_1045_234_block2 cost_1045_234_block3 rfl rfl rfl

private theorem cost_1045_234_join0_4 : P1_7_1_3.blockEstimate 1045 234 746 256 = 12442170880 :=
  @P1_7_1_3.block_append 1045 234 746 874 128 128 256 6448249600 5993921280 12442170880 cost_1045_234_block4 cost_1045_234_block5 rfl rfl rfl

private theorem cost_1045_234_join0_6 : P1_7_1_3.blockEstimate 1045 234 1002 256 = 7332706864 :=
  @P1_7_1_3.block_append 1045 234 1002 1130 128 128 256 4588837507 2743869357 7332706864 cost_1045_234_block6 cost_1045_234_block7 rfl rfl rfl

private theorem cost_1045_234_join0_8 : P1_7_1_3.blockEstimate 1045 234 1258 255 = 1301965082 :=
  @P1_7_1_3.block_append 1045 234 1258 1386 128 127 255 1127616346 174348736 1301965082 cost_1045_234_block8 cost_1045_234_block9 rfl rfl rfl

private theorem cost_1045_234_join1_0 : P1_7_1_3.blockEstimate 1045 234 234 512 = 12730737015 :=
  @P1_7_1_3.block_append 1045 234 234 490 256 256 512 2413898615 10316838400 12730737015 cost_1045_234_join0_0 cost_1045_234_join0_2 rfl rfl rfl

private theorem cost_1045_234_join1_2 : P1_7_1_3.blockEstimate 1045 234 746 512 = 19774877744 :=
  @P1_7_1_3.block_append 1045 234 746 1002 256 256 512 12442170880 7332706864 19774877744 cost_1045_234_join0_4 cost_1045_234_join0_6 rfl rfl rfl

private theorem cost_1045_234_join2_0 : P1_7_1_3.blockEstimate 1045 234 234 1024 = 32505614759 :=
  @P1_7_1_3.block_append 1045 234 234 746 512 512 1024 12730737015 19774877744 32505614759 cost_1045_234_join1_0 cost_1045_234_join1_2 rfl rfl rfl

private theorem cost_1045_234_join3_0 : P1_7_1_3.blockEstimate 1045 234 234 1279 = 33807579841 :=
  @P1_7_1_3.block_append 1045 234 234 1258 1024 255 1279 32505614759 1301965082 33807579841 cost_1045_234_join2_0 cost_1045_234_join0_8 rfl rfl rfl

private theorem cost_1045_234_total : P1_7_1_3.momentEstimate 1045 234 = 33807579841 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1045 + 234 = 1279 by decide]
  exact cost_1045_234_join3_0

theorem moment1045_234 : P1_7_1.groupedPoleMoment 1045 234 ≤ 33807579841 :=
  (P1_7_1_3.grouped_bound 1045 234).trans_eq cost_1045_234_total
private theorem cost_1046_226_block0 : P1_7_1_3.blockEstimate 1046 226 226 128 = 340140320 := by decide +kernel

private theorem cost_1046_226_block1 : P1_7_1_3.blockEstimate 1046 226 354 128 = 2074408286 := by decide +kernel

private theorem cost_1046_226_block2 : P1_7_1_3.blockEstimate 1046 226 482 128 = 4340486976 := by decide +kernel

private theorem cost_1046_226_block3 : P1_7_1_3.blockEstimate 1046 226 610 128 = 5794681664 := by decide +kernel

private theorem cost_1046_226_block4 : P1_7_1_3.blockEstimate 1046 226 738 128 = 6296769344 := by decide +kernel

private theorem cost_1046_226_block5 : P1_7_1_3.blockEstimate 1046 226 866 128 = 5846750016 := by decide +kernel

private theorem cost_1046_226_block6 : P1_7_1_3.blockEstimate 1046 226 994 128 = 4469896026 := by decide +kernel

private theorem cost_1046_226_block7 : P1_7_1_3.blockEstimate 1046 226 1122 128 = 2642185983 := by decide +kernel

private theorem cost_1046_226_block8 : P1_7_1_3.blockEstimate 1046 226 1250 128 = 1055722254 := by decide +kernel

private theorem cost_1046_226_block9 : P1_7_1_3.blockEstimate 1046 226 1378 120 = 148017720 := by decide +kernel

private theorem cost_1046_226_join0_0 : P1_7_1_3.blockEstimate 1046 226 226 256 = 2414548606 :=
  @P1_7_1_3.block_append 1046 226 226 354 128 128 256 340140320 2074408286 2414548606 cost_1046_226_block0 cost_1046_226_block1 rfl rfl rfl

private theorem cost_1046_226_join0_2 : P1_7_1_3.blockEstimate 1046 226 482 256 = 10135168640 :=
  @P1_7_1_3.block_append 1046 226 482 610 128 128 256 4340486976 5794681664 10135168640 cost_1046_226_block2 cost_1046_226_block3 rfl rfl rfl

private theorem cost_1046_226_join0_4 : P1_7_1_3.blockEstimate 1046 226 738 256 = 12143519360 :=
  @P1_7_1_3.block_append 1046 226 738 866 128 128 256 6296769344 5846750016 12143519360 cost_1046_226_block4 cost_1046_226_block5 rfl rfl rfl

private theorem cost_1046_226_join0_6 : P1_7_1_3.blockEstimate 1046 226 994 256 = 7112082009 :=
  @P1_7_1_3.block_append 1046 226 994 1122 128 128 256 4469896026 2642185983 7112082009 cost_1046_226_block6 cost_1046_226_block7 rfl rfl rfl

private theorem cost_1046_226_join0_8 : P1_7_1_3.blockEstimate 1046 226 1250 248 = 1203739974 :=
  @P1_7_1_3.block_append 1046 226 1250 1378 128 120 248 1055722254 148017720 1203739974 cost_1046_226_block8 cost_1046_226_block9 rfl rfl rfl

private theorem cost_1046_226_join1_0 : P1_7_1_3.blockEstimate 1046 226 226 512 = 12549717246 :=
  @P1_7_1_3.block_append 1046 226 226 482 256 256 512 2414548606 10135168640 12549717246 cost_1046_226_join0_0 cost_1046_226_join0_2 rfl rfl rfl

private theorem cost_1046_226_join1_2 : P1_7_1_3.blockEstimate 1046 226 738 512 = 19255601369 :=
  @P1_7_1_3.block_append 1046 226 738 994 256 256 512 12143519360 7112082009 19255601369 cost_1046_226_join0_4 cost_1046_226_join0_6 rfl rfl rfl

private theorem cost_1046_226_join2_0 : P1_7_1_3.blockEstimate 1046 226 226 1024 = 31805318615 :=
  @P1_7_1_3.block_append 1046 226 226 738 512 512 1024 12549717246 19255601369 31805318615 cost_1046_226_join1_0 cost_1046_226_join1_2 rfl rfl rfl

private theorem cost_1046_226_join3_0 : P1_7_1_3.blockEstimate 1046 226 226 1272 = 33009058589 :=
  @P1_7_1_3.block_append 1046 226 226 1250 1024 248 1272 31805318615 1203739974 33009058589 cost_1046_226_join2_0 cost_1046_226_join0_8 rfl rfl rfl

private theorem cost_1046_226_total : P1_7_1_3.momentEstimate 1046 226 = 33009058589 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1046 + 226 = 1272 by decide]
  exact cost_1046_226_join3_0

theorem moment1046_226 : P1_7_1.groupedPoleMoment 1046 226 ≤ 33009058589 :=
  (P1_7_1_3.grouped_bound 1046 226).trans_eq cost_1046_226_total

end Research6966.HelperRescueCatalogue

end Merged6967_Near6967RescueMoment9
