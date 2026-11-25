import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt0
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open HelperSource (WidthGuard)

private theorem moment_9204_1934_part0 :
    blockEstimate 9204 1934 1934 128 = 3258746400 := by decide +kernel
private theorem moment_9204_1934_part1 :
    blockEstimate 9204 1934 2062 128 = 22238828064 := by decide +kernel
private theorem moment_9204_1934_part2 :
    blockEstimate 9204 1934 2190 128 = 59309991456 := by decide +kernel
private theorem moment_9204_1934_part3 :
    blockEstimate 9204 1934 2318 128 = 113666930208 := by decide +kernel
private theorem moment_9204_1934_part4 :
    blockEstimate 9204 1934 2446 128 = 184504337952 := by decide +kernel
private theorem moment_9204_1934_part5 :
    blockEstimate 9204 1934 2574 128 = 271016908320 := by decide +kernel
private theorem moment_9204_1934_part6 :
    blockEstimate 9204 1934 2702 128 = 372399334944 := by decide +kernel
private theorem moment_9204_1934_part7 :
    blockEstimate 9204 1934 2830 128 = 487846311456 := by decide +kernel
private theorem moment_9204_1934_part8 :
    blockEstimate 9204 1934 2958 128 = 616552531488 := by decide +kernel
private theorem moment_9204_1934_part9 :
    blockEstimate 9204 1934 3086 128 = 757712688672 := by decide +kernel
private theorem moment_9204_1934_part10 :
    blockEstimate 9204 1934 3214 128 = 910521476640 := by decide +kernel
private theorem moment_9204_1934_part11 :
    blockEstimate 9204 1934 3342 128 = 1074173589024 := by decide +kernel
private theorem moment_9204_1934_part12 :
    blockEstimate 9204 1934 3470 128 = 1247863719456 := by decide +kernel
private theorem moment_9204_1934_part13 :
    blockEstimate 9204 1934 3598 128 = 1430786561568 := by decide +kernel
private theorem moment_9204_1934_part14 :
    blockEstimate 9204 1934 3726 128 = 1622136808992 := by decide +kernel
private theorem moment_9204_1934_part15 :
    blockEstimate 9204 1934 3854 128 = 1819335142935 := by decide +kernel
private theorem moment_9204_1934_part16 :
    blockEstimate 9204 1934 3982 128 = 2011927798080 := by decide +kernel
private theorem moment_9204_1934_part17 :
    blockEstimate 9204 1934 4110 128 = 2196407787840 := by decide +kernel
private theorem moment_9204_1934_part18 :
    blockEstimate 9204 1934 4238 128 = 2372771799360 := by decide +kernel
private theorem moment_9204_1934_part19 :
    blockEstimate 9204 1934 4366 128 = 2541019832640 := by decide +kernel
private theorem moment_9204_1934_part20 :
    blockEstimate 9204 1934 4494 128 = 2701151887680 := by decide +kernel
private theorem moment_9204_1934_part21 :
    blockEstimate 9204 1934 4622 128 = 2853167964480 := by decide +kernel
private theorem moment_9204_1934_part22 :
    blockEstimate 9204 1934 4750 128 = 2997068063040 := by decide +kernel
private theorem moment_9204_1934_part23 :
    blockEstimate 9204 1934 4878 128 = 3132852183360 := by decide +kernel
private theorem moment_9204_1934_part24 :
    blockEstimate 9204 1934 5006 128 = 3260520325440 := by decide +kernel
private theorem moment_9204_1934_part25 :
    blockEstimate 9204 1934 5134 128 = 3380072489280 := by decide +kernel
private theorem moment_9204_1934_part26 :
    blockEstimate 9204 1934 5262 128 = 3491508674880 := by decide +kernel
private theorem moment_9204_1934_part27 :
    blockEstimate 9204 1934 5390 128 = 3594828882240 := by decide +kernel
private theorem moment_9204_1934_part28 :
    blockEstimate 9204 1934 5518 128 = 3690033111360 := by decide +kernel
private theorem moment_9204_1934_part29 :
    blockEstimate 9204 1934 5646 128 = 3777121362240 := by decide +kernel
private theorem moment_9204_1934_part30 :
    blockEstimate 9204 1934 5774 128 = 3856093634880 := by decide +kernel
private theorem moment_9204_1934_part31 :
    blockEstimate 9204 1934 5902 128 = 3926949929280 := by decide +kernel
private theorem moment_9204_1934_part32 :
    blockEstimate 9204 1934 6030 128 = 3989690245440 := by decide +kernel
private theorem moment_9204_1934_part33 :
    blockEstimate 9204 1934 6158 128 = 4044314583360 := by decide +kernel
private theorem moment_9204_1934_part34 :
    blockEstimate 9204 1934 6286 128 = 4090822943040 := by decide +kernel
private theorem moment_9204_1934_part35 :
    blockEstimate 9204 1934 6414 128 = 4129215324480 := by decide +kernel
private theorem moment_9204_1934_part36 :
    blockEstimate 9204 1934 6542 128 = 4159491727680 := by decide +kernel
private theorem moment_9204_1934_part37 :
    blockEstimate 9204 1934 6670 128 = 4181652152640 := by decide +kernel
private theorem moment_9204_1934_part38 :
    blockEstimate 9204 1934 6798 128 = 4195696599360 := by decide +kernel
private theorem moment_9204_1934_part39 :
    blockEstimate 9204 1934 6926 128 = 4201625067840 := by decide +kernel
private theorem moment_9204_1934_part40 :
    blockEstimate 9204 1934 7054 128 = 4199437558080 := by decide +kernel
private theorem moment_9204_1934_part41 :
    blockEstimate 9204 1934 7182 128 = 4189134070080 := by decide +kernel
private theorem moment_9204_1934_part42 :
    blockEstimate 9204 1934 7310 128 = 4170714603840 := by decide +kernel
private theorem moment_9204_1934_part43 :
    blockEstimate 9204 1934 7438 128 = 4144179159360 := by decide +kernel
private theorem moment_9204_1934_part44 :
    blockEstimate 9204 1934 7566 128 = 4109527736640 := by decide +kernel
private theorem moment_9204_1934_part45 :
    blockEstimate 9204 1934 7694 128 = 4066760335680 := by decide +kernel
private theorem moment_9204_1934_part46 :
    blockEstimate 9204 1934 7822 128 = 4015876956480 := by decide +kernel
private theorem moment_9204_1934_part47 :
    blockEstimate 9204 1934 7950 128 = 3956877599040 := by decide +kernel
private theorem moment_9204_1934_part48 :
    blockEstimate 9204 1934 8078 128 = 3889762263360 := by decide +kernel
private theorem moment_9204_1934_part49 :
    blockEstimate 9204 1934 8206 128 = 3814530949440 := by decide +kernel
private theorem moment_9204_1934_part50 :
    blockEstimate 9204 1934 8334 128 = 3731183657280 := by decide +kernel
private theorem moment_9204_1934_part51 :
    blockEstimate 9204 1934 8462 128 = 3639720386880 := by decide +kernel
private theorem moment_9204_1934_part52 :
    blockEstimate 9204 1934 8590 128 = 3540141138240 := by decide +kernel
private theorem moment_9204_1934_part53 :
    blockEstimate 9204 1934 8718 128 = 3432445911360 := by decide +kernel
private theorem moment_9204_1934_part54 :
    blockEstimate 9204 1934 8846 128 = 3316634706240 := by decide +kernel
private theorem moment_9204_1934_part55 :
    blockEstimate 9204 1934 8974 128 = 3192707522880 := by decide +kernel
private theorem moment_9204_1934_part56 :
    blockEstimate 9204 1934 9102 128 = 3060672660662 := by decide +kernel
private theorem moment_9204_1934_part57 :
    blockEstimate 9204 1934 9230 128 = 2922189666835 := by decide +kernel
private theorem moment_9204_1934_part58 :
    blockEstimate 9204 1934 9358 128 = 2781152560075 := by decide +kernel
private theorem moment_9204_1934_part59 :
    blockEstimate 9204 1934 9486 128 = 2638604095811 := by decide +kernel
private theorem moment_9204_1934_part60 :
    blockEstimate 9204 1934 9614 128 = 2495118862611 := by decide +kernel
private theorem moment_9204_1934_part61 :
    blockEstimate 9204 1934 9742 128 = 2351258128260 := by decide +kernel
private theorem moment_9204_1934_part62 :
    blockEstimate 9204 1934 9870 128 = 2207569845614 := by decide +kernel
private theorem moment_9204_1934_part63 :
    blockEstimate 9204 1934 9998 128 = 2064588648047 := by decide +kernel
private theorem moment_9204_1934_part64 :
    blockEstimate 9204 1934 10126 128 = 1922835851962 := by decide +kernel
private theorem moment_9204_1934_part65 :
    blockEstimate 9204 1934 10254 128 = 1782819456131 := by decide +kernel
private theorem moment_9204_1934_part66 :
    blockEstimate 9204 1934 10382 128 = 1645034141248 := by decide +kernel
private theorem moment_9204_1934_part67 :
    blockEstimate 9204 1934 10510 128 = 1509961269335 := by decide +kernel
private theorem moment_9204_1934_part68 :
    blockEstimate 9204 1934 10638 128 = 1378068887308 := by decide +kernel
private theorem moment_9204_1934_part69 :
    blockEstimate 9204 1934 10766 128 = 1249811721549 := by decide +kernel
private theorem moment_9204_1934_part70 :
    blockEstimate 9204 1934 10894 128 = 1125631182398 := by decide +kernel
private theorem moment_9204_1934_part71 :
    blockEstimate 9204 1934 11022 128 = 1005946333810 := by decide +kernel
private theorem moment_9204_1934_part72 :
    blockEstimate 9204 1934 11150 128 = 890209793520 := by decide +kernel
private theorem moment_9204_1934_part73 :
    blockEstimate 9204 1934 11278 128 = 779590273520 := by decide +kernel
private theorem moment_9204_1934_part74 :
    blockEstimate 9204 1934 11406 128 = 675219021296 := by decide +kernel
private theorem moment_9204_1934_part75 :
    blockEstimate 9204 1934 11534 128 = 577347695088 := by decide +kernel
private theorem moment_9204_1934_part76 :
    blockEstimate 9204 1934 11662 128 = 486227953136 := by decide +kernel
private theorem moment_9204_1934_part77 :
    blockEstimate 9204 1934 11790 128 = 402111453680 := by decide +kernel
private theorem moment_9204_1934_part78 :
    blockEstimate 9204 1934 11918 128 = 325249854960 := by decide +kernel
private theorem moment_9204_1934_part79 :
    blockEstimate 9204 1934 12046 128 = 255894815216 := by decide +kernel
private theorem moment_9204_1934_part80 :
    blockEstimate 9204 1934 12174 128 = 194297992688 := by decide +kernel
private theorem moment_9204_1934_part81 :
    blockEstimate 9204 1934 12302 128 = 140711045616 := by decide +kernel
private theorem moment_9204_1934_part82 :
    blockEstimate 9204 1934 12430 128 = 95385632240 := by decide +kernel
private theorem moment_9204_1934_part83 :
    blockEstimate 9204 1934 12558 128 = 58573410800 := by decide +kernel
private theorem moment_9204_1934_part84 :
    blockEstimate 9204 1934 12686 128 = 30526039536 := by decide +kernel
private theorem moment_9204_1934_part85 :
    blockEstimate 9204 1934 12814 128 = 11495176688 := by decide +kernel
private theorem moment_9204_1934_part86 :
    blockEstimate 9204 1934 12942 128 = 1732480496 := by decide +kernel
private theorem moment_9204_1934_part87 :
    blockEstimate 9204 1934 13070 2 = 27611 := by decide +kernel
private theorem moment_9204_1934_join0 :
    blockEstimate 9204 1934 1934 256 = 25497574464 :=
  block_append moment_9204_1934_part0 moment_9204_1934_part1 rfl rfl rfl
private theorem moment_9204_1934_join1 :
    blockEstimate 9204 1934 2318 256 = 298171268160 :=
  block_append moment_9204_1934_part3 moment_9204_1934_part4 rfl rfl rfl
private theorem moment_9204_1934_join2 :
    blockEstimate 9204 1934 2190 384 = 357481259616 :=
  block_append moment_9204_1934_part2 moment_9204_1934_join1 rfl rfl rfl
private theorem moment_9204_1934_join3 :
    blockEstimate 9204 1934 1934 640 = 382978834080 :=
  block_append moment_9204_1934_join0 moment_9204_1934_join2 rfl rfl rfl
private theorem moment_9204_1934_join4 :
    blockEstimate 9204 1934 2702 256 = 860245646400 :=
  block_append moment_9204_1934_part6 moment_9204_1934_part7 rfl rfl rfl
private theorem moment_9204_1934_join5 :
    blockEstimate 9204 1934 2574 384 = 1131262554720 :=
  block_append moment_9204_1934_part5 moment_9204_1934_join4 rfl rfl rfl
private theorem moment_9204_1934_join6 :
    blockEstimate 9204 1934 3086 256 = 1668234165312 :=
  block_append moment_9204_1934_part9 moment_9204_1934_part10 rfl rfl rfl
private theorem moment_9204_1934_join7 :
    blockEstimate 9204 1934 2958 384 = 2284786696800 :=
  block_append moment_9204_1934_part8 moment_9204_1934_join6 rfl rfl rfl
private theorem moment_9204_1934_join8 :
    blockEstimate 9204 1934 2574 768 = 3416049251520 :=
  block_append moment_9204_1934_join5 moment_9204_1934_join7 rfl rfl rfl
private theorem moment_9204_1934_join9 :
    blockEstimate 9204 1934 1934 1408 = 3799028085600 :=
  block_append moment_9204_1934_join3 moment_9204_1934_join8 rfl rfl rfl
private theorem moment_9204_1934_join10 :
    blockEstimate 9204 1934 3342 256 = 2322037308480 :=
  block_append moment_9204_1934_part11 moment_9204_1934_part12 rfl rfl rfl
private theorem moment_9204_1934_join11 :
    blockEstimate 9204 1934 3726 256 = 3441471951927 :=
  block_append moment_9204_1934_part14 moment_9204_1934_part15 rfl rfl rfl
private theorem moment_9204_1934_join12 :
    blockEstimate 9204 1934 3598 384 = 4872258513495 :=
  block_append moment_9204_1934_part13 moment_9204_1934_join11 rfl rfl rfl
private theorem moment_9204_1934_join13 :
    blockEstimate 9204 1934 3342 640 = 7194295821975 :=
  block_append moment_9204_1934_join10 moment_9204_1934_join12 rfl rfl rfl
private theorem moment_9204_1934_join14 :
    blockEstimate 9204 1934 4110 256 = 4569179587200 :=
  block_append moment_9204_1934_part17 moment_9204_1934_part18 rfl rfl rfl
private theorem moment_9204_1934_join15 :
    blockEstimate 9204 1934 3982 384 = 6581107385280 :=
  block_append moment_9204_1934_part16 moment_9204_1934_join14 rfl rfl rfl
private theorem moment_9204_1934_join16 :
    blockEstimate 9204 1934 4494 256 = 5554319852160 :=
  block_append moment_9204_1934_part20 moment_9204_1934_part21 rfl rfl rfl
private theorem moment_9204_1934_join17 :
    blockEstimate 9204 1934 4366 384 = 8095339684800 :=
  block_append moment_9204_1934_part19 moment_9204_1934_join16 rfl rfl rfl
private theorem moment_9204_1934_join18 :
    blockEstimate 9204 1934 3982 768 = 14676447070080 :=
  block_append moment_9204_1934_join15 moment_9204_1934_join17 rfl rfl rfl
private theorem moment_9204_1934_join19 :
    blockEstimate 9204 1934 3342 1408 = 21870742892055 :=
  block_append moment_9204_1934_join13 moment_9204_1934_join18 rfl rfl rfl
private theorem moment_9204_1934_join20 :
    blockEstimate 9204 1934 1934 2816 = 25669770977655 :=
  block_append moment_9204_1934_join9 moment_9204_1934_join19 rfl rfl rfl
private theorem moment_9204_1934_join21 :
    blockEstimate 9204 1934 4750 256 = 6129920246400 :=
  block_append moment_9204_1934_part22 moment_9204_1934_part23 rfl rfl rfl
private theorem moment_9204_1934_join22 :
    blockEstimate 9204 1934 5134 256 = 6871581164160 :=
  block_append moment_9204_1934_part25 moment_9204_1934_part26 rfl rfl rfl
private theorem moment_9204_1934_join23 :
    blockEstimate 9204 1934 5006 384 = 10132101489600 :=
  block_append moment_9204_1934_part24 moment_9204_1934_join22 rfl rfl rfl
private theorem moment_9204_1934_join24 :
    blockEstimate 9204 1934 4750 640 = 16262021736000 :=
  block_append moment_9204_1934_join21 moment_9204_1934_join23 rfl rfl rfl
private theorem moment_9204_1934_join25 :
    blockEstimate 9204 1934 5518 256 = 7467154473600 :=
  block_append moment_9204_1934_part28 moment_9204_1934_part29 rfl rfl rfl
private theorem moment_9204_1934_join26 :
    blockEstimate 9204 1934 5390 384 = 11061983355840 :=
  block_append moment_9204_1934_part27 moment_9204_1934_join25 rfl rfl rfl
private theorem moment_9204_1934_join27 :
    blockEstimate 9204 1934 5902 256 = 7916640174720 :=
  block_append moment_9204_1934_part31 moment_9204_1934_part32 rfl rfl rfl
private theorem moment_9204_1934_join28 :
    blockEstimate 9204 1934 5774 384 = 11772733809600 :=
  block_append moment_9204_1934_part30 moment_9204_1934_join27 rfl rfl rfl
private theorem moment_9204_1934_join29 :
    blockEstimate 9204 1934 5390 768 = 22834717165440 :=
  block_append moment_9204_1934_join26 moment_9204_1934_join28 rfl rfl rfl
private theorem moment_9204_1934_join30 :
    blockEstimate 9204 1934 4750 1408 = 39096738901440 :=
  block_append moment_9204_1934_join24 moment_9204_1934_join29 rfl rfl rfl
private theorem moment_9204_1934_join31 :
    blockEstimate 9204 1934 6158 256 = 8135137526400 :=
  block_append moment_9204_1934_part33 moment_9204_1934_part34 rfl rfl rfl
private theorem moment_9204_1934_join32 :
    blockEstimate 9204 1934 6542 256 = 8341143880320 :=
  block_append moment_9204_1934_part36 moment_9204_1934_part37 rfl rfl rfl
private theorem moment_9204_1934_join33 :
    blockEstimate 9204 1934 6414 384 = 12470359204800 :=
  block_append moment_9204_1934_part35 moment_9204_1934_join32 rfl rfl rfl
private theorem moment_9204_1934_join34 :
    blockEstimate 9204 1934 6158 640 = 20605496731200 :=
  block_append moment_9204_1934_join31 moment_9204_1934_join33 rfl rfl rfl
private theorem moment_9204_1934_join35 :
    blockEstimate 9204 1934 6926 256 = 8401062625920 :=
  block_append moment_9204_1934_part39 moment_9204_1934_part40 rfl rfl rfl
private theorem moment_9204_1934_join36 :
    blockEstimate 9204 1934 6798 384 = 12596759225280 :=
  block_append moment_9204_1934_part38 moment_9204_1934_join35 rfl rfl rfl
private theorem moment_9204_1934_join37 :
    blockEstimate 9204 1934 7310 256 = 8314893763200 :=
  block_append moment_9204_1934_part42 moment_9204_1934_part43 rfl rfl rfl
private theorem moment_9204_1934_join38 :
    blockEstimate 9204 1934 7182 384 = 12504027833280 :=
  block_append moment_9204_1934_part41 moment_9204_1934_join37 rfl rfl rfl
private theorem moment_9204_1934_join39 :
    blockEstimate 9204 1934 6798 768 = 25100787058560 :=
  block_append moment_9204_1934_join36 moment_9204_1934_join38 rfl rfl rfl
private theorem moment_9204_1934_join40 :
    blockEstimate 9204 1934 6158 1408 = 45706283789760 :=
  block_append moment_9204_1934_join34 moment_9204_1934_join39 rfl rfl rfl
private theorem moment_9204_1934_join41 :
    blockEstimate 9204 1934 4750 2816 = 84803022691200 :=
  block_append moment_9204_1934_join30 moment_9204_1934_join40 rfl rfl rfl
private theorem moment_9204_1934_join42 :
    blockEstimate 9204 1934 1934 5632 = 110472793668855 :=
  block_append moment_9204_1934_join20 moment_9204_1934_join41 rfl rfl rfl
private theorem moment_9204_1934_join43 :
    blockEstimate 9204 1934 7566 256 = 8176288072320 :=
  block_append moment_9204_1934_part44 moment_9204_1934_part45 rfl rfl rfl
private theorem moment_9204_1934_join44 :
    blockEstimate 9204 1934 7950 256 = 7846639862400 :=
  block_append moment_9204_1934_part47 moment_9204_1934_part48 rfl rfl rfl
private theorem moment_9204_1934_join45 :
    blockEstimate 9204 1934 7822 384 = 11862516818880 :=
  block_append moment_9204_1934_part46 moment_9204_1934_join44 rfl rfl rfl
private theorem moment_9204_1934_join46 :
    blockEstimate 9204 1934 7566 640 = 20038804891200 :=
  block_append moment_9204_1934_join43 moment_9204_1934_join45 rfl rfl rfl
private theorem moment_9204_1934_join47 :
    blockEstimate 9204 1934 8334 256 = 7370904044160 :=
  block_append moment_9204_1934_part50 moment_9204_1934_part51 rfl rfl rfl
private theorem moment_9204_1934_join48 :
    blockEstimate 9204 1934 8206 384 = 11185434993600 :=
  block_append moment_9204_1934_part49 moment_9204_1934_join47 rfl rfl rfl
private theorem moment_9204_1934_join49 :
    blockEstimate 9204 1934 8718 256 = 6749080617600 :=
  block_append moment_9204_1934_part53 moment_9204_1934_part54 rfl rfl rfl
private theorem moment_9204_1934_join50 :
    blockEstimate 9204 1934 8590 384 = 10289221755840 :=
  block_append moment_9204_1934_part52 moment_9204_1934_join49 rfl rfl rfl
private theorem moment_9204_1934_join51 :
    blockEstimate 9204 1934 8206 768 = 21474656749440 :=
  block_append moment_9204_1934_join48 moment_9204_1934_join50 rfl rfl rfl
private theorem moment_9204_1934_join52 :
    blockEstimate 9204 1934 7566 1408 = 41513461640640 :=
  block_append moment_9204_1934_join46 moment_9204_1934_join51 rfl rfl rfl
private theorem moment_9204_1934_join53 :
    blockEstimate 9204 1934 8974 256 = 6253380183542 :=
  block_append moment_9204_1934_part55 moment_9204_1934_part56 rfl rfl rfl
private theorem moment_9204_1934_join54 :
    blockEstimate 9204 1934 9358 256 = 5419756655886 :=
  block_append moment_9204_1934_part58 moment_9204_1934_part59 rfl rfl rfl
private theorem moment_9204_1934_join55 :
    blockEstimate 9204 1934 9230 384 = 8341946322721 :=
  block_append moment_9204_1934_part57 moment_9204_1934_join54 rfl rfl rfl
private theorem moment_9204_1934_join56 :
    blockEstimate 9204 1934 8974 640 = 14595326506263 :=
  block_append moment_9204_1934_join53 moment_9204_1934_join55 rfl rfl rfl
private theorem moment_9204_1934_join57 :
    blockEstimate 9204 1934 9742 256 = 4558827973874 :=
  block_append moment_9204_1934_part61 moment_9204_1934_part62 rfl rfl rfl
private theorem moment_9204_1934_join58 :
    blockEstimate 9204 1934 9614 384 = 7053946836485 :=
  block_append moment_9204_1934_part60 moment_9204_1934_join57 rfl rfl rfl
private theorem moment_9204_1934_join59 :
    blockEstimate 9204 1934 10126 256 = 3705655308093 :=
  block_append moment_9204_1934_part64 moment_9204_1934_part65 rfl rfl rfl
private theorem moment_9204_1934_join60 :
    blockEstimate 9204 1934 9998 384 = 5770243956140 :=
  block_append moment_9204_1934_part63 moment_9204_1934_join59 rfl rfl rfl
private theorem moment_9204_1934_join61 :
    blockEstimate 9204 1934 9614 768 = 12824190792625 :=
  block_append moment_9204_1934_join58 moment_9204_1934_join60 rfl rfl rfl
private theorem moment_9204_1934_join62 :
    blockEstimate 9204 1934 8974 1408 = 27419517298888 :=
  block_append moment_9204_1934_join56 moment_9204_1934_join61 rfl rfl rfl
private theorem moment_9204_1934_join63 :
    blockEstimate 9204 1934 7566 2816 = 68932978939528 :=
  block_append moment_9204_1934_join52 moment_9204_1934_join62 rfl rfl rfl
private theorem moment_9204_1934_join64 :
    blockEstimate 9204 1934 10382 256 = 3154995410583 :=
  block_append moment_9204_1934_part66 moment_9204_1934_part67 rfl rfl rfl
private theorem moment_9204_1934_join65 :
    blockEstimate 9204 1934 10766 256 = 2375442903947 :=
  block_append moment_9204_1934_part69 moment_9204_1934_part70 rfl rfl rfl
private theorem moment_9204_1934_join66 :
    blockEstimate 9204 1934 10638 384 = 3753511791255 :=
  block_append moment_9204_1934_part68 moment_9204_1934_join65 rfl rfl rfl
private theorem moment_9204_1934_join67 :
    blockEstimate 9204 1934 10382 640 = 6908507201838 :=
  block_append moment_9204_1934_join64 moment_9204_1934_join66 rfl rfl rfl
private theorem moment_9204_1934_join68 :
    blockEstimate 9204 1934 11150 256 = 1669800067040 :=
  block_append moment_9204_1934_part72 moment_9204_1934_part73 rfl rfl rfl
private theorem moment_9204_1934_join69 :
    blockEstimate 9204 1934 11022 384 = 2675746400850 :=
  block_append moment_9204_1934_part71 moment_9204_1934_join68 rfl rfl rfl
private theorem moment_9204_1934_join70 :
    blockEstimate 9204 1934 11534 256 = 1063575648224 :=
  block_append moment_9204_1934_part75 moment_9204_1934_part76 rfl rfl rfl
private theorem moment_9204_1934_join71 :
    blockEstimate 9204 1934 11406 384 = 1738794669520 :=
  block_append moment_9204_1934_part74 moment_9204_1934_join70 rfl rfl rfl
private theorem moment_9204_1934_join72 :
    blockEstimate 9204 1934 11022 768 = 4414541070370 :=
  block_append moment_9204_1934_join69 moment_9204_1934_join71 rfl rfl rfl
private theorem moment_9204_1934_join73 :
    blockEstimate 9204 1934 10382 1408 = 11323048272208 :=
  block_append moment_9204_1934_join67 moment_9204_1934_join72 rfl rfl rfl
private theorem moment_9204_1934_join74 :
    blockEstimate 9204 1934 11790 256 = 727361308640 :=
  block_append moment_9204_1934_part77 moment_9204_1934_part78 rfl rfl rfl
private theorem moment_9204_1934_join75 :
    blockEstimate 9204 1934 12174 256 = 335009038304 :=
  block_append moment_9204_1934_part80 moment_9204_1934_part81 rfl rfl rfl
private theorem moment_9204_1934_join76 :
    blockEstimate 9204 1934 12046 384 = 590903853520 :=
  block_append moment_9204_1934_part79 moment_9204_1934_join75 rfl rfl rfl
private theorem moment_9204_1934_join77 :
    blockEstimate 9204 1934 11790 640 = 1318265162160 :=
  block_append moment_9204_1934_join74 moment_9204_1934_join76 rfl rfl rfl
private theorem moment_9204_1934_join78 :
    blockEstimate 9204 1934 12558 256 = 89099450336 :=
  block_append moment_9204_1934_part83 moment_9204_1934_part84 rfl rfl rfl
private theorem moment_9204_1934_join79 :
    blockEstimate 9204 1934 12430 384 = 184485082576 :=
  block_append moment_9204_1934_part82 moment_9204_1934_join78 rfl rfl rfl
private theorem moment_9204_1934_join80 :
    blockEstimate 9204 1934 12942 130 = 1732508107 :=
  block_append moment_9204_1934_part86 moment_9204_1934_part87 rfl rfl rfl
private theorem moment_9204_1934_join81 :
    blockEstimate 9204 1934 12814 258 = 13227684795 :=
  block_append moment_9204_1934_part85 moment_9204_1934_join80 rfl rfl rfl
private theorem moment_9204_1934_join82 :
    blockEstimate 9204 1934 12430 642 = 197712767371 :=
  block_append moment_9204_1934_join79 moment_9204_1934_join81 rfl rfl rfl
private theorem moment_9204_1934_join83 :
    blockEstimate 9204 1934 11790 1282 = 1515977929531 :=
  block_append moment_9204_1934_join77 moment_9204_1934_join82 rfl rfl rfl
private theorem moment_9204_1934_join84 :
    blockEstimate 9204 1934 10382 2690 = 12839026201739 :=
  block_append moment_9204_1934_join73 moment_9204_1934_join83 rfl rfl rfl
private theorem moment_9204_1934_join85 :
    blockEstimate 9204 1934 7566 5506 = 81772005141267 :=
  block_append moment_9204_1934_join63 moment_9204_1934_join84 rfl rfl rfl
private theorem moment_9204_1934_join86 :
    blockEstimate 9204 1934 1934 11138 = 192244798810122 :=
  block_append moment_9204_1934_join42 moment_9204_1934_join85 rfl rfl rfl

theorem moment_9204_1934 : momentEstimate 9204 1934 = 192244798810122 := moment_9204_1934_join86

private theorem moment_9204_2007_part0 :
    blockEstimate 9204 2007 2007 128 = 3258746400 := by decide +kernel
private theorem moment_9204_2007_part1 :
    blockEstimate 9204 2007 2135 128 = 22238828064 := by decide +kernel
private theorem moment_9204_2007_part2 :
    blockEstimate 9204 2007 2263 128 = 59309991456 := by decide +kernel
private theorem moment_9204_2007_part3 :
    blockEstimate 9204 2007 2391 128 = 113666930208 := by decide +kernel
private theorem moment_9204_2007_part4 :
    blockEstimate 9204 2007 2519 128 = 184504337952 := by decide +kernel
private theorem moment_9204_2007_part5 :
    blockEstimate 9204 2007 2647 128 = 271016908320 := by decide +kernel
private theorem moment_9204_2007_part6 :
    blockEstimate 9204 2007 2775 128 = 372399334944 := by decide +kernel
private theorem moment_9204_2007_part7 :
    blockEstimate 9204 2007 2903 128 = 487846311456 := by decide +kernel
private theorem moment_9204_2007_part8 :
    blockEstimate 9204 2007 3031 128 = 616552531488 := by decide +kernel
private theorem moment_9204_2007_part9 :
    blockEstimate 9204 2007 3159 128 = 757712688672 := by decide +kernel
private theorem moment_9204_2007_part10 :
    blockEstimate 9204 2007 3287 128 = 910521476640 := by decide +kernel
private theorem moment_9204_2007_part11 :
    blockEstimate 9204 2007 3415 128 = 1074173589024 := by decide +kernel
private theorem moment_9204_2007_part12 :
    blockEstimate 9204 2007 3543 128 = 1247863719456 := by decide +kernel
private theorem moment_9204_2007_part13 :
    blockEstimate 9204 2007 3671 128 = 1430786561568 := by decide +kernel
private theorem moment_9204_2007_part14 :
    blockEstimate 9204 2007 3799 128 = 1622136808992 := by decide +kernel
private theorem moment_9204_2007_part15 :
    blockEstimate 9204 2007 3927 128 = 1821026881070 := by decide +kernel
private theorem moment_9204_2007_part16 :
    blockEstimate 9204 2007 4055 128 = 2021292574464 := by decide +kernel
private theorem moment_9204_2007_part17 :
    blockEstimate 9204 2007 4183 128 = 2213933090560 := by decide +kernel
private theorem moment_9204_2007_part18 :
    blockEstimate 9204 2007 4311 128 = 2398151444224 := by decide +kernel
private theorem moment_9204_2007_part19 :
    blockEstimate 9204 2007 4439 128 = 2573947635456 := by decide +kernel
private theorem moment_9204_2007_part20 :
    blockEstimate 9204 2007 4567 128 = 2741321664256 := by decide +kernel
private theorem moment_9204_2007_part21 :
    blockEstimate 9204 2007 4695 128 = 2900273530624 := by decide +kernel
private theorem moment_9204_2007_part22 :
    blockEstimate 9204 2007 4823 128 = 3050803234560 := by decide +kernel
private theorem moment_9204_2007_part23 :
    blockEstimate 9204 2007 4951 128 = 3192910776064 := by decide +kernel
private theorem moment_9204_2007_part24 :
    blockEstimate 9204 2007 5079 128 = 3326596155136 := by decide +kernel
private theorem moment_9204_2007_part25 :
    blockEstimate 9204 2007 5207 128 = 3451859371776 := by decide +kernel
private theorem moment_9204_2007_part26 :
    blockEstimate 9204 2007 5335 128 = 3568700425984 := by decide +kernel
private theorem moment_9204_2007_part27 :
    blockEstimate 9204 2007 5463 128 = 3677119317760 := by decide +kernel
private theorem moment_9204_2007_part28 :
    blockEstimate 9204 2007 5591 128 = 3777116047104 := by decide +kernel
private theorem moment_9204_2007_part29 :
    blockEstimate 9204 2007 5719 128 = 3868690614016 := by decide +kernel
private theorem moment_9204_2007_part30 :
    blockEstimate 9204 2007 5847 128 = 3951843018496 := by decide +kernel
private theorem moment_9204_2007_part31 :
    blockEstimate 9204 2007 5975 128 = 4026573260544 := by decide +kernel
private theorem moment_9204_2007_part32 :
    blockEstimate 9204 2007 6103 128 = 4092881340160 := by decide +kernel
private theorem moment_9204_2007_part33 :
    blockEstimate 9204 2007 6231 128 = 4150767257344 := by decide +kernel
private theorem moment_9204_2007_part34 :
    blockEstimate 9204 2007 6359 128 = 4200231012096 := by decide +kernel
private theorem moment_9204_2007_part35 :
    blockEstimate 9204 2007 6487 128 = 4241272604416 := by decide +kernel
private theorem moment_9204_2007_part36 :
    blockEstimate 9204 2007 6615 128 = 4273892034304 := by decide +kernel
private theorem moment_9204_2007_part37 :
    blockEstimate 9204 2007 6743 128 = 4298089301760 := by decide +kernel
private theorem moment_9204_2007_part38 :
    blockEstimate 9204 2007 6871 128 = 4313864406784 := by decide +kernel
private theorem moment_9204_2007_part39 :
    blockEstimate 9204 2007 6999 128 = 4321217349376 := by decide +kernel
private theorem moment_9204_2007_part40 :
    blockEstimate 9204 2007 7127 128 = 4320148129536 := by decide +kernel
private theorem moment_9204_2007_part41 :
    blockEstimate 9204 2007 7255 128 = 4310656747264 := by decide +kernel
private theorem moment_9204_2007_part42 :
    blockEstimate 9204 2007 7383 128 = 4292743202560 := by decide +kernel
private theorem moment_9204_2007_part43 :
    blockEstimate 9204 2007 7511 128 = 4266407495424 := by decide +kernel
private theorem moment_9204_2007_part44 :
    blockEstimate 9204 2007 7639 128 = 4231649625856 := by decide +kernel
private theorem moment_9204_2007_part45 :
    blockEstimate 9204 2007 7767 128 = 4188469593856 := by decide +kernel
private theorem moment_9204_2007_part46 :
    blockEstimate 9204 2007 7895 128 = 4136867399424 := by decide +kernel
private theorem moment_9204_2007_part47 :
    blockEstimate 9204 2007 8023 128 = 4076843042560 := by decide +kernel
private theorem moment_9204_2007_part48 :
    blockEstimate 9204 2007 8151 128 = 4008396523264 := by decide +kernel
private theorem moment_9204_2007_part49 :
    blockEstimate 9204 2007 8279 128 = 3931527841536 := by decide +kernel
private theorem moment_9204_2007_part50 :
    blockEstimate 9204 2007 8407 128 = 3846236997376 := by decide +kernel
private theorem moment_9204_2007_part51 :
    blockEstimate 9204 2007 8535 128 = 3752523990784 := by decide +kernel
private theorem moment_9204_2007_part52 :
    blockEstimate 9204 2007 8663 128 = 3650388821760 := by decide +kernel
private theorem moment_9204_2007_part53 :
    blockEstimate 9204 2007 8791 128 = 3539831490304 := by decide +kernel
private theorem moment_9204_2007_part54 :
    blockEstimate 9204 2007 8919 128 = 3420851996416 := by decide +kernel
private theorem moment_9204_2007_part55 :
    blockEstimate 9204 2007 9047 128 = 3293450340096 := by decide +kernel
private theorem moment_9204_2007_part56 :
    blockEstimate 9204 2007 9175 128 = 3158061593754 := by decide +kernel
private theorem moment_9204_2007_part57 :
    blockEstimate 9204 2007 9303 128 = 3018286486228 := by decide +kernel
private theorem moment_9204_2007_part58 :
    blockEstimate 9204 2007 9431 128 = 2876280298777 := by decide +kernel
private theorem moment_9204_2007_part59 :
    blockEstimate 9204 2007 9559 128 = 2732634120428 := by decide +kernel
private theorem moment_9204_2007_part60 :
    blockEstimate 9204 2007 9687 128 = 2587916286557 := by decide +kernel
private theorem moment_9204_2007_part61 :
    blockEstimate 9204 2007 9815 128 = 2442682301637 := by decide +kernel
private theorem moment_9204_2007_part62 :
    blockEstimate 9204 2007 9943 128 = 2297474834023 := by decide +kernel
private theorem moment_9204_2007_part63 :
    blockEstimate 9204 2007 10071 128 = 2152823720748 := by decide +kernel
private theorem moment_9204_2007_part64 :
    blockEstimate 9204 2007 10199 128 = 2009245963108 := by decide +kernel
private theorem moment_9204_2007_part65 :
    blockEstimate 9204 2007 10327 128 = 1867245729694 := by decide +kernel
private theorem moment_9204_2007_part66 :
    blockEstimate 9204 2007 10455 128 = 1727314356507 := by decide +kernel
private theorem moment_9204_2007_part67 :
    blockEstimate 9204 2007 10583 128 = 1589930344406 := by decide +kernel
private theorem moment_9204_2007_part68 :
    blockEstimate 9204 2007 10711 128 = 1455559361812 := by decide +kernel
private theorem moment_9204_2007_part69 :
    blockEstimate 9204 2007 10839 128 = 1324654242939 := by decide +kernel
private theorem moment_9204_2007_part70 :
    blockEstimate 9204 2007 10967 128 = 1197654988582 := by decide +kernel
private theorem moment_9204_2007_part71 :
    blockEstimate 9204 2007 11095 128 = 1074979041323 := by decide +kernel
private theorem moment_9204_2007_part72 :
    blockEstimate 9204 2007 11223 128 = 955998817152 := by decide +kernel
private theorem moment_9204_2007_part73 :
    blockEstimate 9204 2007 11351 128 = 841928520576 := by decide +kernel
private theorem moment_9204_2007_part74 :
    blockEstimate 9204 2007 11479 128 = 733962967936 := by decide +kernel
private theorem moment_9204_2007_part75 :
    blockEstimate 9204 2007 11607 128 = 632353817472 := by decide +kernel
private theorem moment_9204_2007_part76 :
    blockEstimate 9204 2007 11735 128 = 537352727424 := by decide +kernel
private theorem moment_9204_2007_part77 :
    blockEstimate 9204 2007 11863 128 = 449211356032 := by decide +kernel
private theorem moment_9204_2007_part78 :
    blockEstimate 9204 2007 11991 128 = 368181361536 := by decide +kernel
private theorem moment_9204_2007_part79 :
    blockEstimate 9204 2007 12119 128 = 294514402176 := by decide +kernel
private theorem moment_9204_2007_part80 :
    blockEstimate 9204 2007 12247 128 = 228462136192 := by decide +kernel
private theorem moment_9204_2007_part81 :
    blockEstimate 9204 2007 12375 128 = 170276221824 := by decide +kernel
private theorem moment_9204_2007_part82 :
    blockEstimate 9204 2007 12503 128 = 120208317312 := by decide +kernel
private theorem moment_9204_2007_part83 :
    blockEstimate 9204 2007 12631 128 = 78510080896 := by decide +kernel
private theorem moment_9204_2007_part84 :
    blockEstimate 9204 2007 12759 128 = 45433170816 := by decide +kernel
private theorem moment_9204_2007_part85 :
    blockEstimate 9204 2007 12887 128 = 21229245312 := by decide +kernel
private theorem moment_9204_2007_part86 :
    blockEstimate 9204 2007 13015 128 = 6149962624 := by decide +kernel
private theorem moment_9204_2007_part87 :
    blockEstimate 9204 2007 13143 75 = 341995098 := by decide +kernel
private theorem moment_9204_2007_join0 :
    blockEstimate 9204 2007 2007 256 = 25497574464 :=
  block_append moment_9204_2007_part0 moment_9204_2007_part1 rfl rfl rfl
private theorem moment_9204_2007_join1 :
    blockEstimate 9204 2007 2391 256 = 298171268160 :=
  block_append moment_9204_2007_part3 moment_9204_2007_part4 rfl rfl rfl
private theorem moment_9204_2007_join2 :
    blockEstimate 9204 2007 2263 384 = 357481259616 :=
  block_append moment_9204_2007_part2 moment_9204_2007_join1 rfl rfl rfl
private theorem moment_9204_2007_join3 :
    blockEstimate 9204 2007 2007 640 = 382978834080 :=
  block_append moment_9204_2007_join0 moment_9204_2007_join2 rfl rfl rfl
private theorem moment_9204_2007_join4 :
    blockEstimate 9204 2007 2775 256 = 860245646400 :=
  block_append moment_9204_2007_part6 moment_9204_2007_part7 rfl rfl rfl
private theorem moment_9204_2007_join5 :
    blockEstimate 9204 2007 2647 384 = 1131262554720 :=
  block_append moment_9204_2007_part5 moment_9204_2007_join4 rfl rfl rfl
private theorem moment_9204_2007_join6 :
    blockEstimate 9204 2007 3159 256 = 1668234165312 :=
  block_append moment_9204_2007_part9 moment_9204_2007_part10 rfl rfl rfl
private theorem moment_9204_2007_join7 :
    blockEstimate 9204 2007 3031 384 = 2284786696800 :=
  block_append moment_9204_2007_part8 moment_9204_2007_join6 rfl rfl rfl
private theorem moment_9204_2007_join8 :
    blockEstimate 9204 2007 2647 768 = 3416049251520 :=
  block_append moment_9204_2007_join5 moment_9204_2007_join7 rfl rfl rfl
private theorem moment_9204_2007_join9 :
    blockEstimate 9204 2007 2007 1408 = 3799028085600 :=
  block_append moment_9204_2007_join3 moment_9204_2007_join8 rfl rfl rfl
private theorem moment_9204_2007_join10 :
    blockEstimate 9204 2007 3415 256 = 2322037308480 :=
  block_append moment_9204_2007_part11 moment_9204_2007_part12 rfl rfl rfl
private theorem moment_9204_2007_join11 :
    blockEstimate 9204 2007 3799 256 = 3443163690062 :=
  block_append moment_9204_2007_part14 moment_9204_2007_part15 rfl rfl rfl
private theorem moment_9204_2007_join12 :
    blockEstimate 9204 2007 3671 384 = 4873950251630 :=
  block_append moment_9204_2007_part13 moment_9204_2007_join11 rfl rfl rfl
private theorem moment_9204_2007_join13 :
    blockEstimate 9204 2007 3415 640 = 7195987560110 :=
  block_append moment_9204_2007_join10 moment_9204_2007_join12 rfl rfl rfl
private theorem moment_9204_2007_join14 :
    blockEstimate 9204 2007 4183 256 = 4612084534784 :=
  block_append moment_9204_2007_part17 moment_9204_2007_part18 rfl rfl rfl
private theorem moment_9204_2007_join15 :
    blockEstimate 9204 2007 4055 384 = 6633377109248 :=
  block_append moment_9204_2007_part16 moment_9204_2007_join14 rfl rfl rfl
private theorem moment_9204_2007_join16 :
    blockEstimate 9204 2007 4567 256 = 5641595194880 :=
  block_append moment_9204_2007_part20 moment_9204_2007_part21 rfl rfl rfl
private theorem moment_9204_2007_join17 :
    blockEstimate 9204 2007 4439 384 = 8215542830336 :=
  block_append moment_9204_2007_part19 moment_9204_2007_join16 rfl rfl rfl
private theorem moment_9204_2007_join18 :
    blockEstimate 9204 2007 4055 768 = 14848919939584 :=
  block_append moment_9204_2007_join15 moment_9204_2007_join17 rfl rfl rfl
private theorem moment_9204_2007_join19 :
    blockEstimate 9204 2007 3415 1408 = 22044907499694 :=
  block_append moment_9204_2007_join13 moment_9204_2007_join18 rfl rfl rfl
private theorem moment_9204_2007_join20 :
    blockEstimate 9204 2007 2007 2816 = 25843935585294 :=
  block_append moment_9204_2007_join9 moment_9204_2007_join19 rfl rfl rfl
private theorem moment_9204_2007_join21 :
    blockEstimate 9204 2007 4823 256 = 6243714010624 :=
  block_append moment_9204_2007_part22 moment_9204_2007_part23 rfl rfl rfl
private theorem moment_9204_2007_join22 :
    blockEstimate 9204 2007 5207 256 = 7020559797760 :=
  block_append moment_9204_2007_part25 moment_9204_2007_part26 rfl rfl rfl
private theorem moment_9204_2007_join23 :
    blockEstimate 9204 2007 5079 384 = 10347155952896 :=
  block_append moment_9204_2007_part24 moment_9204_2007_join22 rfl rfl rfl
private theorem moment_9204_2007_join24 :
    blockEstimate 9204 2007 4823 640 = 16590869963520 :=
  block_append moment_9204_2007_join21 moment_9204_2007_join23 rfl rfl rfl
private theorem moment_9204_2007_join25 :
    blockEstimate 9204 2007 5591 256 = 7645806661120 :=
  block_append moment_9204_2007_part28 moment_9204_2007_part29 rfl rfl rfl
private theorem moment_9204_2007_join26 :
    blockEstimate 9204 2007 5463 384 = 11322925978880 :=
  block_append moment_9204_2007_part27 moment_9204_2007_join25 rfl rfl rfl
private theorem moment_9204_2007_join27 :
    blockEstimate 9204 2007 5975 256 = 8119454600704 :=
  block_append moment_9204_2007_part31 moment_9204_2007_part32 rfl rfl rfl
private theorem moment_9204_2007_join28 :
    blockEstimate 9204 2007 5847 384 = 12071297619200 :=
  block_append moment_9204_2007_part30 moment_9204_2007_join27 rfl rfl rfl
private theorem moment_9204_2007_join29 :
    blockEstimate 9204 2007 5463 768 = 23394223598080 :=
  block_append moment_9204_2007_join26 moment_9204_2007_join28 rfl rfl rfl
private theorem moment_9204_2007_join30 :
    blockEstimate 9204 2007 4823 1408 = 39985093561600 :=
  block_append moment_9204_2007_join24 moment_9204_2007_join29 rfl rfl rfl
private theorem moment_9204_2007_join31 :
    blockEstimate 9204 2007 6231 256 = 8350998269440 :=
  block_append moment_9204_2007_part33 moment_9204_2007_part34 rfl rfl rfl
private theorem moment_9204_2007_join32 :
    blockEstimate 9204 2007 6615 256 = 8571981336064 :=
  block_append moment_9204_2007_part36 moment_9204_2007_part37 rfl rfl rfl
private theorem moment_9204_2007_join33 :
    blockEstimate 9204 2007 6487 384 = 12813253940480 :=
  block_append moment_9204_2007_part35 moment_9204_2007_join32 rfl rfl rfl
private theorem moment_9204_2007_join34 :
    blockEstimate 9204 2007 6231 640 = 21164252209920 :=
  block_append moment_9204_2007_join31 moment_9204_2007_join33 rfl rfl rfl
private theorem moment_9204_2007_join35 :
    blockEstimate 9204 2007 6999 256 = 8641365478912 :=
  block_append moment_9204_2007_part39 moment_9204_2007_part40 rfl rfl rfl
private theorem moment_9204_2007_join36 :
    blockEstimate 9204 2007 6871 384 = 12955229885696 :=
  block_append moment_9204_2007_part38 moment_9204_2007_join35 rfl rfl rfl
private theorem moment_9204_2007_join37 :
    blockEstimate 9204 2007 7383 256 = 8559150697984 :=
  block_append moment_9204_2007_part42 moment_9204_2007_part43 rfl rfl rfl
private theorem moment_9204_2007_join38 :
    blockEstimate 9204 2007 7255 384 = 12869807445248 :=
  block_append moment_9204_2007_part41 moment_9204_2007_join37 rfl rfl rfl
private theorem moment_9204_2007_join39 :
    blockEstimate 9204 2007 6871 768 = 25825037330944 :=
  block_append moment_9204_2007_join36 moment_9204_2007_join38 rfl rfl rfl
private theorem moment_9204_2007_join40 :
    blockEstimate 9204 2007 6231 1408 = 46989289540864 :=
  block_append moment_9204_2007_join34 moment_9204_2007_join39 rfl rfl rfl
private theorem moment_9204_2007_join41 :
    blockEstimate 9204 2007 4823 2816 = 86974383102464 :=
  block_append moment_9204_2007_join30 moment_9204_2007_join40 rfl rfl rfl
private theorem moment_9204_2007_join42 :
    blockEstimate 9204 2007 2007 5632 = 112818318687758 :=
  block_append moment_9204_2007_join20 moment_9204_2007_join41 rfl rfl rfl
private theorem moment_9204_2007_join43 :
    blockEstimate 9204 2007 7639 256 = 8420119219712 :=
  block_append moment_9204_2007_part44 moment_9204_2007_part45 rfl rfl rfl
private theorem moment_9204_2007_join44 :
    blockEstimate 9204 2007 8023 256 = 8085239565824 :=
  block_append moment_9204_2007_part47 moment_9204_2007_part48 rfl rfl rfl
private theorem moment_9204_2007_join45 :
    blockEstimate 9204 2007 7895 384 = 12222106965248 :=
  block_append moment_9204_2007_part46 moment_9204_2007_join44 rfl rfl rfl
private theorem moment_9204_2007_join46 :
    blockEstimate 9204 2007 7639 640 = 20642226184960 :=
  block_append moment_9204_2007_join43 moment_9204_2007_join45 rfl rfl rfl
private theorem moment_9204_2007_join47 :
    blockEstimate 9204 2007 8407 256 = 7598760988160 :=
  block_append moment_9204_2007_part50 moment_9204_2007_part51 rfl rfl rfl
private theorem moment_9204_2007_join48 :
    blockEstimate 9204 2007 8279 384 = 11530288829696 :=
  block_append moment_9204_2007_part49 moment_9204_2007_join47 rfl rfl rfl
private theorem moment_9204_2007_join49 :
    blockEstimate 9204 2007 8791 256 = 6960683486720 :=
  block_append moment_9204_2007_part53 moment_9204_2007_part54 rfl rfl rfl
private theorem moment_9204_2007_join50 :
    blockEstimate 9204 2007 8663 384 = 10611072308480 :=
  block_append moment_9204_2007_part52 moment_9204_2007_join49 rfl rfl rfl
private theorem moment_9204_2007_join51 :
    blockEstimate 9204 2007 8279 768 = 22141361138176 :=
  block_append moment_9204_2007_join48 moment_9204_2007_join50 rfl rfl rfl
private theorem moment_9204_2007_join52 :
    blockEstimate 9204 2007 7639 1408 = 42783587323136 :=
  block_append moment_9204_2007_join46 moment_9204_2007_join51 rfl rfl rfl
private theorem moment_9204_2007_join53 :
    blockEstimate 9204 2007 9047 256 = 6451511933850 :=
  block_append moment_9204_2007_part55 moment_9204_2007_part56 rfl rfl rfl
private theorem moment_9204_2007_join54 :
    blockEstimate 9204 2007 9431 256 = 5608914419205 :=
  block_append moment_9204_2007_part58 moment_9204_2007_part59 rfl rfl rfl
private theorem moment_9204_2007_join55 :
    blockEstimate 9204 2007 9303 384 = 8627200905433 :=
  block_append moment_9204_2007_part57 moment_9204_2007_join54 rfl rfl rfl
private theorem moment_9204_2007_join56 :
    blockEstimate 9204 2007 9047 640 = 15078712839283 :=
  block_append moment_9204_2007_join53 moment_9204_2007_join55 rfl rfl rfl
private theorem moment_9204_2007_join57 :
    blockEstimate 9204 2007 9815 256 = 4740157135660 :=
  block_append moment_9204_2007_part61 moment_9204_2007_part62 rfl rfl rfl
private theorem moment_9204_2007_join58 :
    blockEstimate 9204 2007 9687 384 = 7328073422217 :=
  block_append moment_9204_2007_part60 moment_9204_2007_join57 rfl rfl rfl
private theorem moment_9204_2007_join59 :
    blockEstimate 9204 2007 10199 256 = 3876491692802 :=
  block_append moment_9204_2007_part64 moment_9204_2007_part65 rfl rfl rfl
private theorem moment_9204_2007_join60 :
    blockEstimate 9204 2007 10071 384 = 6029315413550 :=
  block_append moment_9204_2007_part63 moment_9204_2007_join59 rfl rfl rfl
private theorem moment_9204_2007_join61 :
    blockEstimate 9204 2007 9687 768 = 13357388835767 :=
  block_append moment_9204_2007_join58 moment_9204_2007_join60 rfl rfl rfl
private theorem moment_9204_2007_join62 :
    blockEstimate 9204 2007 9047 1408 = 28436101675050 :=
  block_append moment_9204_2007_join56 moment_9204_2007_join61 rfl rfl rfl
private theorem moment_9204_2007_join63 :
    blockEstimate 9204 2007 7639 2816 = 71219688998186 :=
  block_append moment_9204_2007_join52 moment_9204_2007_join62 rfl rfl rfl
private theorem moment_9204_2007_join64 :
    blockEstimate 9204 2007 10455 256 = 3317244700913 :=
  block_append moment_9204_2007_part66 moment_9204_2007_part67 rfl rfl rfl
private theorem moment_9204_2007_join65 :
    blockEstimate 9204 2007 10839 256 = 2522309231521 :=
  block_append moment_9204_2007_part69 moment_9204_2007_part70 rfl rfl rfl
private theorem moment_9204_2007_join66 :
    blockEstimate 9204 2007 10711 384 = 3977868593333 :=
  block_append moment_9204_2007_part68 moment_9204_2007_join65 rfl rfl rfl
private theorem moment_9204_2007_join67 :
    blockEstimate 9204 2007 10455 640 = 7295113294246 :=
  block_append moment_9204_2007_join64 moment_9204_2007_join66 rfl rfl rfl
private theorem moment_9204_2007_join68 :
    blockEstimate 9204 2007 11223 256 = 1797927337728 :=
  block_append moment_9204_2007_part72 moment_9204_2007_part73 rfl rfl rfl
private theorem moment_9204_2007_join69 :
    blockEstimate 9204 2007 11095 384 = 2872906379051 :=
  block_append moment_9204_2007_part71 moment_9204_2007_join68 rfl rfl rfl
private theorem moment_9204_2007_join70 :
    blockEstimate 9204 2007 11607 256 = 1169706544896 :=
  block_append moment_9204_2007_part75 moment_9204_2007_part76 rfl rfl rfl
private theorem moment_9204_2007_join71 :
    blockEstimate 9204 2007 11479 384 = 1903669512832 :=
  block_append moment_9204_2007_part74 moment_9204_2007_join70 rfl rfl rfl
private theorem moment_9204_2007_join72 :
    blockEstimate 9204 2007 11095 768 = 4776575891883 :=
  block_append moment_9204_2007_join69 moment_9204_2007_join71 rfl rfl rfl
private theorem moment_9204_2007_join73 :
    blockEstimate 9204 2007 10455 1408 = 12071689186129 :=
  block_append moment_9204_2007_join67 moment_9204_2007_join72 rfl rfl rfl
private theorem moment_9204_2007_join74 :
    blockEstimate 9204 2007 11863 256 = 817392717568 :=
  block_append moment_9204_2007_part77 moment_9204_2007_part78 rfl rfl rfl
private theorem moment_9204_2007_join75 :
    blockEstimate 9204 2007 12247 256 = 398738358016 :=
  block_append moment_9204_2007_part80 moment_9204_2007_part81 rfl rfl rfl
private theorem moment_9204_2007_join76 :
    blockEstimate 9204 2007 12119 384 = 693252760192 :=
  block_append moment_9204_2007_part79 moment_9204_2007_join75 rfl rfl rfl
private theorem moment_9204_2007_join77 :
    blockEstimate 9204 2007 11863 640 = 1510645477760 :=
  block_append moment_9204_2007_join74 moment_9204_2007_join76 rfl rfl rfl
private theorem moment_9204_2007_join78 :
    blockEstimate 9204 2007 12631 256 = 123943251712 :=
  block_append moment_9204_2007_part83 moment_9204_2007_part84 rfl rfl rfl
private theorem moment_9204_2007_join79 :
    blockEstimate 9204 2007 12503 384 = 244151569024 :=
  block_append moment_9204_2007_part82 moment_9204_2007_join78 rfl rfl rfl
private theorem moment_9204_2007_join80 :
    blockEstimate 9204 2007 13015 203 = 6491957722 :=
  block_append moment_9204_2007_part86 moment_9204_2007_part87 rfl rfl rfl
private theorem moment_9204_2007_join81 :
    blockEstimate 9204 2007 12887 331 = 27721203034 :=
  block_append moment_9204_2007_part85 moment_9204_2007_join80 rfl rfl rfl
private theorem moment_9204_2007_join82 :
    blockEstimate 9204 2007 12503 715 = 271872772058 :=
  block_append moment_9204_2007_join79 moment_9204_2007_join81 rfl rfl rfl
private theorem moment_9204_2007_join83 :
    blockEstimate 9204 2007 11863 1355 = 1782518249818 :=
  block_append moment_9204_2007_join77 moment_9204_2007_join82 rfl rfl rfl
private theorem moment_9204_2007_join84 :
    blockEstimate 9204 2007 10455 2763 = 13854207435947 :=
  block_append moment_9204_2007_join73 moment_9204_2007_join83 rfl rfl rfl
private theorem moment_9204_2007_join85 :
    blockEstimate 9204 2007 7639 5579 = 85073896434133 :=
  block_append moment_9204_2007_join63 moment_9204_2007_join84 rfl rfl rfl
private theorem moment_9204_2007_join86 :
    blockEstimate 9204 2007 2007 11211 = 197892215121891 :=
  block_append moment_9204_2007_join42 moment_9204_2007_join85 rfl rfl rfl

theorem moment_9204_2007 : momentEstimate 9204 2007 = 197892215121891 := moment_9204_2007_join86

private theorem receipt_0_15_2402_0_part0 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 0 128 = 232909589637017294430016404960 := by decide +kernel
private theorem receipt_0_15_2402_0_part1 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 128 128 = 213192211294166292678044052960 := by decide +kernel
private theorem receipt_0_15_2402_0_part2 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 256 128 = 194069510308149081873833549280 := by decide +kernel
private theorem receipt_0_15_2402_0_part3 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 384 128 = 175532336888287635758767427040 := by decide +kernel
private theorem receipt_0_15_2402_0_part4 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 512 128 = 157571554564808340685695237600 := by decide +kernel
private theorem receipt_0_15_2402_0_part5 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 640 128 = 140178040182549314651311058400 := by decide +kernel
private theorem receipt_0_15_2402_0_part6 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 768 128 = 123342683894667726328531000800 := by decide +kernel
private theorem receipt_0_15_2402_0_part7 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 896 128 = 107056389156347114098870717920 := by decide +kernel
private theorem receipt_0_15_2402_0_part8 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 1024 128 = 91310072718504705084822912480 := by decide +kernel
private theorem receipt_0_15_2402_0_part9 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 1152 128 = 76094664621498734182234844640 := by decide +kernel
private theorem receipt_0_15_2402_0_part10 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 1280 128 = 61401111673341451110417816954 := by decide +kernel
private theorem receipt_0_15_2402_0_part11 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 1408 128 = 47220391627686646591226106177 := by decide +kernel
private theorem receipt_0_15_2402_0_part12 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 1536 128 = 33543460932937447917966681045 := by decide +kernel
private theorem receipt_0_15_2402_0_part13 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 1664 128 = 20361271053583495145579197500 := by decide +kernel
private theorem receipt_0_15_2402_0_part14 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 1792 128 = 7664786677242299495346309807 := by decide +kernel
private theorem receipt_0_15_2402_0_part15 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 1920 15 = 89216051213421131460644232 := by decide +kernel
private theorem receipt_0_15_2402_0_join0 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 0 256 = 446101800931183587108060457920 :=
  phaseBlock_append receipt_0_15_2402_0_part0 receipt_0_15_2402_0_part1 rfl rfl rfl
private theorem receipt_0_15_2402_0_join1 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 256 256 = 369601847196436717632600976320 :=
  phaseBlock_append receipt_0_15_2402_0_part2 receipt_0_15_2402_0_part3 rfl rfl rfl
private theorem receipt_0_15_2402_0_join2 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 0 512 = 815703648127620304740661434240 :=
  phaseBlock_append receipt_0_15_2402_0_join0 receipt_0_15_2402_0_join1 rfl rfl rfl
private theorem receipt_0_15_2402_0_join3 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 512 256 = 297749594747357655337006296000 :=
  phaseBlock_append receipt_0_15_2402_0_part4 receipt_0_15_2402_0_part5 rfl rfl rfl
private theorem receipt_0_15_2402_0_join4 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 768 256 = 230399073051014840427401718720 :=
  phaseBlock_append receipt_0_15_2402_0_part6 receipt_0_15_2402_0_part7 rfl rfl rfl
private theorem receipt_0_15_2402_0_join5 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 512 512 = 528148667798372495764408014720 :=
  phaseBlock_append receipt_0_15_2402_0_join3 receipt_0_15_2402_0_join4 rfl rfl rfl
private theorem receipt_0_15_2402_0_join6 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 0 1024 = 1343852315925992800505069448960 :=
  phaseBlock_append receipt_0_15_2402_0_join2 receipt_0_15_2402_0_join5 rfl rfl rfl
private theorem receipt_0_15_2402_0_join7 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 1024 256 = 167404737340003439267057757120 :=
  phaseBlock_append receipt_0_15_2402_0_part8 receipt_0_15_2402_0_part9 rfl rfl rfl
private theorem receipt_0_15_2402_0_join8 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 1280 256 = 108621503301028097701643923131 :=
  phaseBlock_append receipt_0_15_2402_0_part10 receipt_0_15_2402_0_part11 rfl rfl rfl
private theorem receipt_0_15_2402_0_join9 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 1024 512 = 276026240641031536968701680251 :=
  phaseBlock_append receipt_0_15_2402_0_join7 receipt_0_15_2402_0_join8 rfl rfl rfl
private theorem receipt_0_15_2402_0_join10 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 1536 256 = 53904731986520943063545878545 :=
  phaseBlock_append receipt_0_15_2402_0_part12 receipt_0_15_2402_0_part13 rfl rfl rfl
private theorem receipt_0_15_2402_0_join11 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 1792 143 = 7754002728455720626806954039 :=
  phaseBlock_append receipt_0_15_2402_0_part14 receipt_0_15_2402_0_part15 rfl rfl rfl
private theorem receipt_0_15_2402_0_join12 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 1536 399 = 61658734714976663690352832584 :=
  phaseBlock_append receipt_0_15_2402_0_join10 receipt_0_15_2402_0_join11 rfl rfl rfl
private theorem receipt_0_15_2402_0_join13 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 1024 911 = 337684975356008200659054512835 :=
  phaseBlock_append receipt_0_15_2402_0_join9 receipt_0_15_2402_0_join12 rfl rfl rfl
private theorem receipt_0_15_2402_0_join14 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 0) 0 1935 = 1681537291282001001164123961795 :=
  phaseBlock_append receipt_0_15_2402_0_join6 receipt_0_15_2402_0_join13 rfl rfl rfl

private theorem receipt_0_15_2402_0 : fastPhase (bank 0 15).shape 179798 2402 76 1 0 1 0 = 1681537291282001001164123961795 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_15_2402_0_join14

private theorem receipt_0_15_2402_1_part0 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 0 128 = 232755304527651368154126567840 := by decide +kernel
private theorem receipt_0_15_2402_1_part1 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 128 128 = 213042449013552450768862149024 := by decide +kernel
private theorem receipt_0_15_2402_1_part2 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 256 128 = 193924201667709236073041471904 := by decide +kernel
private theorem receipt_0_15_2402_1_part3 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 384 128 = 175391412800932146387771972000 := by decide +kernel
private theorem receipt_0_15_2402_1_part4 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 512 128 = 157434946044887845460667271584 := by decide +kernel
private theorem receipt_0_15_2402_1_part5 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 640 128 = 140045678345806557498224687520 := by decide +kernel
private theorem receipt_0_15_2402_1_part6 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 768 128 = 123214499958189386198202739104 := by decide +kernel
private theorem receipt_0_15_2402_1_part7 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 896 128 = 106932314438515633781998655904 := by decide +kernel
private theorem receipt_0_15_2402_1_part8 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 1024 128 = 91190038638950120027025885600 := by decide +kernel
private theorem receipt_0_15_2402_1_part9 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 1152 128 = 75978602701050501299091601824 := by decide +kernel
private theorem receipt_0_15_2402_1_part10 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 1280 128 = 61288953527644808086613854941 := by decide +kernel
private theorem receipt_0_15_2402_1_part11 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 1408 128 = 47112068921743423445515393308 := by decide +kernel
private theorem receipt_0_15_2402_1_part12 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 1536 128 = 33438905408352107923336164285 := by decide +kernel
private theorem receipt_0_15_2402_1_part13 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 1664 128 = 20260414553030919597563244345 := by decide +kernel
private theorem receipt_0_15_2402_1_part14 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 1792 128 = 7567561144530936651852492999 := by decide +kernel
private theorem receipt_0_15_2402_1_part15 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 1920 15 = 78056977624110905810660844 := by decide +kernel
private theorem receipt_0_15_2402_1_join0 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 0 256 = 445797753541203818922988716864 :=
  phaseBlock_append receipt_0_15_2402_1_part0 receipt_0_15_2402_1_part1 rfl rfl rfl
private theorem receipt_0_15_2402_1_join1 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 256 256 = 369315614468641382460813443904 :=
  phaseBlock_append receipt_0_15_2402_1_part2 receipt_0_15_2402_1_part3 rfl rfl rfl
private theorem receipt_0_15_2402_1_join2 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 0 512 = 815113368009845201383802160768 :=
  phaseBlock_append receipt_0_15_2402_1_join0 receipt_0_15_2402_1_join1 rfl rfl rfl
private theorem receipt_0_15_2402_1_join3 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 512 256 = 297480624390694402958891959104 :=
  phaseBlock_append receipt_0_15_2402_1_part4 receipt_0_15_2402_1_part5 rfl rfl rfl
private theorem receipt_0_15_2402_1_join4 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 768 256 = 230146814396705019980201395008 :=
  phaseBlock_append receipt_0_15_2402_1_part6 receipt_0_15_2402_1_part7 rfl rfl rfl
private theorem receipt_0_15_2402_1_join5 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 512 512 = 527627438787399422939093354112 :=
  phaseBlock_append receipt_0_15_2402_1_join3 receipt_0_15_2402_1_join4 rfl rfl rfl
private theorem receipt_0_15_2402_1_join6 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 0 1024 = 1342740806797244624322895514880 :=
  phaseBlock_append receipt_0_15_2402_1_join2 receipt_0_15_2402_1_join5 rfl rfl rfl
private theorem receipt_0_15_2402_1_join7 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 1024 256 = 167168641340000621326117487424 :=
  phaseBlock_append receipt_0_15_2402_1_part8 receipt_0_15_2402_1_part9 rfl rfl rfl
private theorem receipt_0_15_2402_1_join8 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 1280 256 = 108401022449388231532129248249 :=
  phaseBlock_append receipt_0_15_2402_1_part10 receipt_0_15_2402_1_part11 rfl rfl rfl
private theorem receipt_0_15_2402_1_join9 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 1024 512 = 275569663789388852858246735673 :=
  phaseBlock_append receipt_0_15_2402_1_join7 receipt_0_15_2402_1_join8 rfl rfl rfl
private theorem receipt_0_15_2402_1_join10 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 1536 256 = 53699319961383027520899408630 :=
  phaseBlock_append receipt_0_15_2402_1_part12 receipt_0_15_2402_1_part13 rfl rfl rfl
private theorem receipt_0_15_2402_1_join11 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 1792 143 = 7645618122155047557663153843 :=
  phaseBlock_append receipt_0_15_2402_1_part14 receipt_0_15_2402_1_part15 rfl rfl rfl
private theorem receipt_0_15_2402_1_join12 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 1536 399 = 61344938083538075078562562473 :=
  phaseBlock_append receipt_0_15_2402_1_join10 receipt_0_15_2402_1_join11 rfl rfl rfl
private theorem receipt_0_15_2402_1_join13 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 1024 911 = 336914601872926927936809298146 :=
  phaseBlock_append receipt_0_15_2402_1_join9 receipt_0_15_2402_1_join12 rfl rfl rfl
private theorem receipt_0_15_2402_1_join14 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2402 76 1 0 1 1) 0 1935 = 1679655408670171552259704813026 :=
  phaseBlock_append receipt_0_15_2402_1_join6 receipt_0_15_2402_1_join13 rfl rfl rfl

private theorem receipt_0_15_2402_1 : fastPhase (bank 0 15).shape 179798 2402 76 1 0 1 1 = 1679655408670171552259704813026 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_15_2402_1_join14

private theorem receipt_0_15_2403_0_part0 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 0 128 = 232911677048058430083654083520 := by decide +kernel
private theorem receipt_0_15_2403_0_part1 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 128 128 = 213194051072875469278021649344 := by decide +kernel
private theorem receipt_0_15_2403_0_part2 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 256 128 = 194071119178245042972466422720 := by decide +kernel
private theorem receipt_0_15_2403_0_part3 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 384 128 = 175533731258138803308189631424 := by decide +kernel
private theorem receipt_0_15_2403_0_part4 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 512 128 = 157572750527896667691896562624 := by decide +kernel
private theorem receipt_0_15_2403_0_part5 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 640 128 = 140179053517933917925848515520 := by decide +kernel
private theorem receipt_0_15_2403_0_part6 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 768 128 = 123343530067448299337914753984 := by decide +kernel
private theorem receipt_0_15_2403_0_part7 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 896 128 = 107057083318127119911624459200 := by decide +kernel
private theorem receipt_0_15_2403_0_part8 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 1024 128 = 91310629707854349416218682304 := by decide +kernel
private theorem receipt_0_15_2403_0_part9 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 1152 128 = 76095098964417718536702297024 := by decide +kernel
private theorem receipt_0_15_2403_0_part10 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 1280 128 = 61401437443744685389041195526 := by decide +kernel
private theorem receipt_0_15_2403_0_part11 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 1408 128 = 47220622534164207282742447533 := by decide +kernel
private theorem receipt_0_15_2403_0_part12 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 1536 128 = 33543610781964051890524994714 := by decide +kernel
private theorem receipt_0_15_2403_0_part13 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 1664 128 = 20361353332729871510910410640 := by decide +kernel
private theorem receipt_0_15_2403_0_part14 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 1792 128 = 7664814533540663351507315838 := by decide +kernel
private theorem receipt_0_15_2403_0_part15 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 1920 15 = 89216348316783539713660848 := by decide +kernel
private theorem receipt_0_15_2403_0_join0 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 0 256 = 446105728120933899361675732864 :=
  phaseBlock_append receipt_0_15_2403_0_part0 receipt_0_15_2403_0_part1 rfl rfl rfl
private theorem receipt_0_15_2403_0_join1 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 256 256 = 369604850436383846280656054144 :=
  phaseBlock_append receipt_0_15_2403_0_part2 receipt_0_15_2403_0_part3 rfl rfl rfl
private theorem receipt_0_15_2403_0_join2 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 0 512 = 815710578557317745642331787008 :=
  phaseBlock_append receipt_0_15_2403_0_join0 receipt_0_15_2403_0_join1 rfl rfl rfl
private theorem receipt_0_15_2403_0_join3 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 512 256 = 297751804045830585617745078144 :=
  phaseBlock_append receipt_0_15_2403_0_part4 receipt_0_15_2403_0_part5 rfl rfl rfl
private theorem receipt_0_15_2403_0_join4 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 768 256 = 230400613385575419249539213184 :=
  phaseBlock_append receipt_0_15_2403_0_part6 receipt_0_15_2403_0_part7 rfl rfl rfl
private theorem receipt_0_15_2403_0_join5 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 512 512 = 528152417431406004867284291328 :=
  phaseBlock_append receipt_0_15_2403_0_join3 receipt_0_15_2403_0_join4 rfl rfl rfl
private theorem receipt_0_15_2403_0_join6 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 0 1024 = 1343862995988723750509616078336 :=
  phaseBlock_append receipt_0_15_2403_0_join2 receipt_0_15_2403_0_join5 rfl rfl rfl
private theorem receipt_0_15_2403_0_join7 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 1024 256 = 167405728672272067952920979328 :=
  phaseBlock_append receipt_0_15_2403_0_part8 receipt_0_15_2403_0_part9 rfl rfl rfl
private theorem receipt_0_15_2403_0_join8 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 1280 256 = 108622059977908892671783643059 :=
  phaseBlock_append receipt_0_15_2403_0_part10 receipt_0_15_2403_0_part11 rfl rfl rfl
private theorem receipt_0_15_2403_0_join9 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 1024 512 = 276027788650180960624704622387 :=
  phaseBlock_append receipt_0_15_2403_0_join7 receipt_0_15_2403_0_join8 rfl rfl rfl
private theorem receipt_0_15_2403_0_join10 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 1536 256 = 53904964114693923401435405354 :=
  phaseBlock_append receipt_0_15_2403_0_part12 receipt_0_15_2403_0_part13 rfl rfl rfl
private theorem receipt_0_15_2403_0_join11 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 1792 143 = 7754030881857446891220976686 :=
  phaseBlock_append receipt_0_15_2403_0_part14 receipt_0_15_2403_0_part15 rfl rfl rfl
private theorem receipt_0_15_2403_0_join12 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 1536 399 = 61658994996551370292656382040 :=
  phaseBlock_append receipt_0_15_2403_0_join10 receipt_0_15_2403_0_join11 rfl rfl rfl
private theorem receipt_0_15_2403_0_join13 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 1024 911 = 337686783646732330917361004427 :=
  phaseBlock_append receipt_0_15_2403_0_join9 receipt_0_15_2403_0_join12 rfl rfl rfl
private theorem receipt_0_15_2403_0_join14 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 0) 0 1935 = 1681549779635456081426977082763 :=
  phaseBlock_append receipt_0_15_2403_0_join6 receipt_0_15_2403_0_join13 rfl rfl rfl

private theorem receipt_0_15_2403_0 : fastPhase (bank 0 15).shape 179798 2403 76 1 0 1 0 = 1681549779635456081426977082763 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_15_2403_0_join14

private theorem receipt_0_15_2403_1_part0 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 0 128 = 232757390806584767572437765120 := by decide +kernel
private theorem receipt_0_15_2403_1_part1 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 128 128 = 213044287726009480150591605760 := by decide +kernel
private theorem receipt_0_15_2403_1_part2 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 256 128 = 193925809535919771594057190400 := by decide +kernel
private theorem receipt_0_15_2403_1_part3 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 384 128 = 175392806231778282601384381440 := by decide +kernel
private theorem receipt_0_15_2403_1_part4 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 512 128 = 157436141130367746645996211200 := by decide +kernel
private theorem receipt_0_15_2403_1_part5 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 640 128 = 140046690863498089106240834560 := by decide +kernel
private theorem receipt_0_15_2403_1_part6 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 768 128 = 123215345371713526395443481600 := by decide +kernel
private theorem receipt_0_15_2403_1_part7 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 896 128 = 106933007897999665091958410240 := by decide +kernel
private theorem receipt_0_15_2403_1_part8 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 1024 128 = 91190594981490601069220858880 := by decide +kernel
private theorem receipt_0_15_2403_1_part9 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 1152 128 = 75979036451176018625798999040 := by decide +kernel
private theorem receipt_0_15_2403_1_part10 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 1280 128 = 61289278758052295549812178626 := by decide +kernel
private theorem receipt_0_15_2403_1_part11 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 1408 128 = 47112299340096660643291922657 := by decide +kernel
private theorem receipt_0_15_2403_1_part12 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 1536 128 = 33439054819619079379902140322 := by decide +kernel
private theorem receipt_0_15_2403_1_part13 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 1664 128 = 20260496443244239926031719954 := by decide +kernel
private theorem receipt_0_15_2403_1_part14 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 1792 128 = 7567588659194008595959294336 := by decide +kernel
private theorem receipt_0_15_2403_1_part15 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 1920 15 = 78057237716476092385573556 := by decide +kernel
private theorem receipt_0_15_2403_1_join0 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 0 256 = 445801678532594247723029370880 :=
  phaseBlock_append receipt_0_15_2403_1_part0 receipt_0_15_2403_1_part1 rfl rfl rfl
private theorem receipt_0_15_2403_1_join1 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 256 256 = 369318615767698054195441571840 :=
  phaseBlock_append receipt_0_15_2403_1_part2 receipt_0_15_2403_1_part3 rfl rfl rfl
private theorem receipt_0_15_2403_1_join2 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 0 512 = 815120294300292301918470942720 :=
  phaseBlock_append receipt_0_15_2403_1_join0 receipt_0_15_2403_1_join1 rfl rfl rfl
private theorem receipt_0_15_2403_1_join3 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 512 256 = 297482831993865835752237045760 :=
  phaseBlock_append receipt_0_15_2403_1_part4 receipt_0_15_2403_1_part5 rfl rfl rfl
private theorem receipt_0_15_2403_1_join4 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 768 256 = 230148353269713191487401891840 :=
  phaseBlock_append receipt_0_15_2403_1_part6 receipt_0_15_2403_1_part7 rfl rfl rfl
private theorem receipt_0_15_2403_1_join5 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 512 512 = 527631185263579027239638937600 :=
  phaseBlock_append receipt_0_15_2403_1_join3 receipt_0_15_2403_1_join4 rfl rfl rfl
private theorem receipt_0_15_2403_1_join6 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 0 1024 = 1342751479563871329158109880320 :=
  phaseBlock_append receipt_0_15_2403_1_join2 receipt_0_15_2403_1_join5 rfl rfl rfl
private theorem receipt_0_15_2403_1_join7 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 1024 256 = 167169631432666619695019857920 :=
  phaseBlock_append receipt_0_15_2403_1_part8 receipt_0_15_2403_1_part9 rfl rfl rfl
private theorem receipt_0_15_2403_1_join8 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 1280 256 = 108401578098148956193104101283 :=
  phaseBlock_append receipt_0_15_2403_1_part10 receipt_0_15_2403_1_part11 rfl rfl rfl
private theorem receipt_0_15_2403_1_join9 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 1024 512 = 275571209530815575888123959203 :=
  phaseBlock_append receipt_0_15_2403_1_join7 receipt_0_15_2403_1_join8 rfl rfl rfl
private theorem receipt_0_15_2403_1_join10 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 1536 256 = 53699551262863319305933860276 :=
  phaseBlock_append receipt_0_15_2403_1_part12 receipt_0_15_2403_1_part13 rfl rfl rfl
private theorem receipt_0_15_2403_1_join11 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 1792 143 = 7645645896910484688344867892 :=
  phaseBlock_append receipt_0_15_2403_1_part14 receipt_0_15_2403_1_part15 rfl rfl rfl
private theorem receipt_0_15_2403_1_join12 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 1536 399 = 61345197159773803994278728168 :=
  phaseBlock_append receipt_0_15_2403_1_join10 receipt_0_15_2403_1_join11 rfl rfl rfl
private theorem receipt_0_15_2403_1_join13 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 1024 911 = 336916406690589379882402687371 :=
  phaseBlock_append receipt_0_15_2403_1_join9 receipt_0_15_2403_1_join12 rfl rfl rfl
private theorem receipt_0_15_2403_1_join14 :
    phaseBlock (fastLayer (bank 0 15).shape 179798 2403 76 1 0 1 1) 0 1935 = 1679667886254460709040512567691 :=
  phaseBlock_append receipt_0_15_2403_1_join6 receipt_0_15_2403_1_join13 rfl rfl rfl

private theorem receipt_0_15_2403_1 : fastPhase (bank 0 15).shape 179798 2403 76 1 0 1 1 = 1679667886254460709040512567691 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_15_2403_1_join14

theorem receipt_0_15 : Checked (bank 0 15) 76 0 1 := by
  refine checked_from_values (bank 0 15) 76 0 1
    (P3_7_1.checked (bank 0 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9204_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_15_2402_0 receipt_0_15_2402_1 receipt_0_15_2403_0 receipt_0_15_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_15_2402_0_part0 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 0 128 = 209686554343744794797118939456 := by decide +kernel
private theorem receipt_1_15_2402_0_part1 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 128 128 = 191853302255741431610708992320 := by decide +kernel
private theorem receipt_1_15_2402_0_part2 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 256 128 = 174570110809971447715080626496 := by decide +kernel
private theorem receipt_1_15_2402_0_part3 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 384 128 = 157828071441126277991691428160 := by decide +kernel
private theorem receipt_1_15_2402_0_part4 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 512 128 = 141618301386610301667514802496 := by decide +kernel
private theorem receipt_1_15_2402_0_part5 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 640 128 = 125931943661370118444550005056 := by decide +kernel
private theorem receipt_1_15_2402_0_part6 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 768 128 = 110760167032723824629332173120 := by decide +kernel
private theorem receipt_1_15_2402_0_part7 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 896 128 = 96094165995190289262442357056 := by decide +kernel
private theorem receipt_1_15_2402_0_part8 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 1024 128 = 81925160745318430248017551680 := by decide +kernel
private theorem receipt_1_15_2402_0_part9 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 1152 128 = 68244397156516490483260727616 := by decide +kernel
private theorem receipt_1_15_2402_0_part10 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 1280 128 = 55043149877138951612128700831 := by decide +kernel
private theorem receipt_1_15_2402_0_part11 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 1408 128 = 42312735009347459513066248882 := by decide +kernel
private theorem receipt_1_15_2402_0_part12 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 1536 128 = 30044463256895850694320682344 := by decide +kernel
private theorem receipt_1_15_2402_0_part13 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 1664 128 = 18229654581518450245967759759 := by decide +kernel
private theorem receipt_1_15_2402_0_part14 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 1792 128 = 6859654513519975885573350399 := by decide +kernel
private theorem receipt_1_15_2402_0_part15 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 1920 15 = 79821315658484332576810236 := by decide +kernel
private theorem receipt_1_15_2402_0_join0 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 0 256 = 401539856599486226407827931776 :=
  phaseBlock_append receipt_1_15_2402_0_part0 receipt_1_15_2402_0_part1 rfl rfl rfl
private theorem receipt_1_15_2402_0_join1 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 256 256 = 332398182251097725706772054656 :=
  phaseBlock_append receipt_1_15_2402_0_part2 receipt_1_15_2402_0_part3 rfl rfl rfl
private theorem receipt_1_15_2402_0_join2 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 0 512 = 733938038850583952114599986432 :=
  phaseBlock_append receipt_1_15_2402_0_join0 receipt_1_15_2402_0_join1 rfl rfl rfl
private theorem receipt_1_15_2402_0_join3 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 512 256 = 267550245047980420112064807552 :=
  phaseBlock_append receipt_1_15_2402_0_part4 receipt_1_15_2402_0_part5 rfl rfl rfl
private theorem receipt_1_15_2402_0_join4 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 768 256 = 206854333027914113891774530176 :=
  phaseBlock_append receipt_1_15_2402_0_part6 receipt_1_15_2402_0_part7 rfl rfl rfl
private theorem receipt_1_15_2402_0_join5 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 512 512 = 474404578075894534003839337728 :=
  phaseBlock_append receipt_1_15_2402_0_join3 receipt_1_15_2402_0_join4 rfl rfl rfl
private theorem receipt_1_15_2402_0_join6 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 0 1024 = 1208342616926478486118439324160 :=
  phaseBlock_append receipt_1_15_2402_0_join2 receipt_1_15_2402_0_join5 rfl rfl rfl
private theorem receipt_1_15_2402_0_join7 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 1024 256 = 150169557901834920731278279296 :=
  phaseBlock_append receipt_1_15_2402_0_part8 receipt_1_15_2402_0_part9 rfl rfl rfl
private theorem receipt_1_15_2402_0_join8 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 1280 256 = 97355884886486411125194949713 :=
  phaseBlock_append receipt_1_15_2402_0_part10 receipt_1_15_2402_0_part11 rfl rfl rfl
private theorem receipt_1_15_2402_0_join9 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 1024 512 = 247525442788321331856473229009 :=
  phaseBlock_append receipt_1_15_2402_0_join7 receipt_1_15_2402_0_join8 rfl rfl rfl
private theorem receipt_1_15_2402_0_join10 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 1536 256 = 48274117838414300940288442103 :=
  phaseBlock_append receipt_1_15_2402_0_part12 receipt_1_15_2402_0_part13 rfl rfl rfl
private theorem receipt_1_15_2402_0_join11 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 1792 143 = 6939475829178460218150160635 :=
  phaseBlock_append receipt_1_15_2402_0_part14 receipt_1_15_2402_0_part15 rfl rfl rfl
private theorem receipt_1_15_2402_0_join12 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 1536 399 = 55213593667592761158438602738 :=
  phaseBlock_append receipt_1_15_2402_0_join10 receipt_1_15_2402_0_join11 rfl rfl rfl
private theorem receipt_1_15_2402_0_join13 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 1024 911 = 302739036455914093014911831747 :=
  phaseBlock_append receipt_1_15_2402_0_join9 receipt_1_15_2402_0_join12 rfl rfl rfl
private theorem receipt_1_15_2402_0_join14 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 0) 0 1935 = 1511081653382392579133351155907 :=
  phaseBlock_append receipt_1_15_2402_0_join6 receipt_1_15_2402_0_join13 rfl rfl rfl

private theorem receipt_1_15_2402_0 : fastPhase (bank 1 15).shape 179798 2402 76 1 0 2 0 = 1511081653382392579133351155907 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_15_2402_0_join14

private theorem receipt_1_15_2402_1_part0 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 0 128 = 209546954561838402272964340160 := by decide +kernel
private theorem receipt_1_15_2402_1_part1 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 128 128 = 191717890904648462967507790272 := by decide +kernel
private theorem receipt_1_15_2402_1_part2 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 256 128 = 174438820423272091438803380672 := by decide +kernel
private theorem receipt_1_15_2402_1_part3 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 384 128 = 157700834749066364407412795840 := by decide +kernel
private theorem receipt_1_15_2402_1_part4 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 512 128 = 141495051315908618199570213312 := by decide +kernel
private theorem receipt_1_15_2402_1_part5 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 640 128 = 125812613335025724876692335040 := by decide +kernel
private theorem receipt_1_15_2402_1_part6 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 768 128 = 110644689769823368364888418752 := by decide +kernel
private theorem receipt_1_15_2402_1_part7 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 896 128 = 95982475310715320584470309312 := by decide +kernel
private theorem receipt_1_15_2402_1_part8 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 1024 128 = 81817190349952717579462470080 := by decide +kernel
private theorem receipt_1_15_2402_1_part9 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 1152 128 = 68140080956453335647112014272 := by decide +kernel
private theorem receipt_1_15_2402_1_part10 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 1280 128 = 54942421968199406437411309974 := by decide +kernel
private theorem receipt_1_15_2402_1_part11 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 1408 128 = 42215529636053790875193378263 := by decide +kernel
private theorem receipt_1_15_2402_1_part12 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 1536 128 = 29950714836906120805299734345 := by decide +kernel
private theorem receipt_1_15_2402_1_part13 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 1664 128 = 18139297727477061005479867676 := by decide +kernel
private theorem receipt_1_15_2402_1_part14 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 1792 128 = 6772624032964735463157006569 := by decide +kernel
private theorem receipt_1_15_2402_1_part15 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 1920 15 = 69837171603205441796451909 := by decide +kernel
private theorem receipt_1_15_2402_1_join0 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 0 256 = 401264845466486865240472130432 :=
  phaseBlock_append receipt_1_15_2402_1_part0 receipt_1_15_2402_1_part1 rfl rfl rfl
private theorem receipt_1_15_2402_1_join1 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 256 256 = 332139655172338455846216176512 :=
  phaseBlock_append receipt_1_15_2402_1_part2 receipt_1_15_2402_1_part3 rfl rfl rfl
private theorem receipt_1_15_2402_1_join2 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 0 512 = 733404500638825321086688306944 :=
  phaseBlock_append receipt_1_15_2402_1_join0 receipt_1_15_2402_1_join1 rfl rfl rfl
private theorem receipt_1_15_2402_1_join3 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 512 256 = 267307664650934343076262548352 :=
  phaseBlock_append receipt_1_15_2402_1_part4 receipt_1_15_2402_1_part5 rfl rfl rfl
private theorem receipt_1_15_2402_1_join4 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 768 256 = 206627165080538688949358728064 :=
  phaseBlock_append receipt_1_15_2402_1_part6 receipt_1_15_2402_1_part7 rfl rfl rfl
private theorem receipt_1_15_2402_1_join5 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 512 512 = 473934829731473032025621276416 :=
  phaseBlock_append receipt_1_15_2402_1_join3 receipt_1_15_2402_1_join4 rfl rfl rfl
private theorem receipt_1_15_2402_1_join6 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 0 1024 = 1207339330370298353112309583360 :=
  phaseBlock_append receipt_1_15_2402_1_join2 receipt_1_15_2402_1_join5 rfl rfl rfl
private theorem receipt_1_15_2402_1_join7 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 1024 256 = 149957271306406053226574484352 :=
  phaseBlock_append receipt_1_15_2402_1_part8 receipt_1_15_2402_1_part9 rfl rfl rfl
private theorem receipt_1_15_2402_1_join8 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 1280 256 = 97157951604253197312604688237 :=
  phaseBlock_append receipt_1_15_2402_1_part10 receipt_1_15_2402_1_part11 rfl rfl rfl
private theorem receipt_1_15_2402_1_join9 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 1024 512 = 247115222910659250539179172589 :=
  phaseBlock_append receipt_1_15_2402_1_join7 receipt_1_15_2402_1_join8 rfl rfl rfl
private theorem receipt_1_15_2402_1_join10 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 1536 256 = 48090012564383181810779602021 :=
  phaseBlock_append receipt_1_15_2402_1_part12 receipt_1_15_2402_1_part13 rfl rfl rfl
private theorem receipt_1_15_2402_1_join11 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 1792 143 = 6842461204567940904953458478 :=
  phaseBlock_append receipt_1_15_2402_1_part14 receipt_1_15_2402_1_part15 rfl rfl rfl
private theorem receipt_1_15_2402_1_join12 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 1536 399 = 54932473768951122715733060499 :=
  phaseBlock_append receipt_1_15_2402_1_join10 receipt_1_15_2402_1_join11 rfl rfl rfl
private theorem receipt_1_15_2402_1_join13 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 1024 911 = 302047696679610373254912233088 :=
  phaseBlock_append receipt_1_15_2402_1_join9 receipt_1_15_2402_1_join12 rfl rfl rfl
private theorem receipt_1_15_2402_1_join14 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2402 76 1 0 2 1) 0 1935 = 1509387027049908726367221816448 :=
  phaseBlock_append receipt_1_15_2402_1_join6 receipt_1_15_2402_1_join13 rfl rfl rfl

private theorem receipt_1_15_2402_1 : fastPhase (bank 1 15).shape 179798 2402 76 1 0 2 1 = 1509387027049908726367221816448 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_15_2402_1_join14

private theorem receipt_1_15_2403_0_part0 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 0 128 = 209688433624890343910351673600 := by decide +kernel
private theorem receipt_1_15_2403_0_part1 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 128 128 = 191854957888972857029586508032 := by decide +kernel
private theorem receipt_1_15_2403_0_part2 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 256 128 = 174571558028774934863999146240 := by decide +kernel
private theorem receipt_1_15_2403_0_part3 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 384 128 = 157829325176214547334828742912 := by decide +kernel
private theorem receipt_1_15_2403_0_part4 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 512 128 = 141619376266817679068682950912 := by decide +kernel
private theorem receipt_1_15_2403_0_part5 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 640 128 = 125932854014546725917745731840 := by decide +kernel
private theorem receipt_1_15_2403_0_part6 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 768 128 = 110760926886628891479985166592 := by decide +kernel
private theorem receipt_1_15_2403_0_part7 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 896 128 = 96094789078384583619361265920 := by decide +kernel
private theorem receipt_1_15_2403_0_part8 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 1024 128 = 81925660488055810986033780992 := by decide +kernel
private theorem receipt_1_15_2403_0_part9 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 1152 128 = 68244786691634579536570013952 := by decide +kernel
private theorem receipt_1_15_2403_0_part10 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 1280 128 = 55043441915480267595459275689 := by decide +kernel
private theorem receipt_1_15_2403_0_part11 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 1408 128 = 42312941918147526648225428903 := by decide +kernel
private theorem receipt_1_15_2403_0_part12 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 1536 128 = 30044597475273741484146665271 := by decide +kernel
private theorem receipt_1_15_2403_0_part13 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 1664 128 = 18229728247158860210631404954 := by decide +kernel
private theorem receipt_1_15_2403_0_part14 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 1792 128 = 6859679443795458131002353723 := by decide +kernel
private theorem receipt_1_15_2403_0_part15 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 1920 15 = 79821581475924749255413580 := by decide +kernel
private theorem receipt_1_15_2403_0_join0 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 0 256 = 401543391513863200939938181632 :=
  phaseBlock_append receipt_1_15_2403_0_part0 receipt_1_15_2403_0_part1 rfl rfl rfl
private theorem receipt_1_15_2403_0_join1 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 256 256 = 332400883204989482198827889152 :=
  phaseBlock_append receipt_1_15_2403_0_part2 receipt_1_15_2403_0_part3 rfl rfl rfl
private theorem receipt_1_15_2403_0_join2 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 0 512 = 733944274718852683138766070784 :=
  phaseBlock_append receipt_1_15_2403_0_join0 receipt_1_15_2403_0_join1 rfl rfl rfl
private theorem receipt_1_15_2403_0_join3 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 512 256 = 267552230281364404986428682752 :=
  phaseBlock_append receipt_1_15_2403_0_part4 receipt_1_15_2403_0_part5 rfl rfl rfl
private theorem receipt_1_15_2403_0_join4 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 768 256 = 206855715965013475099346432512 :=
  phaseBlock_append receipt_1_15_2403_0_part6 receipt_1_15_2403_0_part7 rfl rfl rfl
private theorem receipt_1_15_2403_0_join5 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 512 512 = 474407946246377880085775115264 :=
  phaseBlock_append receipt_1_15_2403_0_join3 receipt_1_15_2403_0_join4 rfl rfl rfl
private theorem receipt_1_15_2403_0_join6 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 0 1024 = 1208352220965230563224541186048 :=
  phaseBlock_append receipt_1_15_2403_0_join2 receipt_1_15_2403_0_join5 rfl rfl rfl
private theorem receipt_1_15_2403_0_join7 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 1024 256 = 150170447179690390522603794944 :=
  phaseBlock_append receipt_1_15_2403_0_part8 receipt_1_15_2403_0_part9 rfl rfl rfl
private theorem receipt_1_15_2403_0_join8 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 1280 256 = 97356383833627794243684704592 :=
  phaseBlock_append receipt_1_15_2403_0_part10 receipt_1_15_2403_0_part11 rfl rfl rfl
private theorem receipt_1_15_2403_0_join9 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 1024 512 = 247526831013318184766288499536 :=
  phaseBlock_append receipt_1_15_2403_0_join7 receipt_1_15_2403_0_join8 rfl rfl rfl
private theorem receipt_1_15_2403_0_join10 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 1536 256 = 48274325722432601694778070225 :=
  phaseBlock_append receipt_1_15_2403_0_part12 receipt_1_15_2403_0_part13 rfl rfl rfl
private theorem receipt_1_15_2403_0_join11 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 1792 143 = 6939501025271382880257767303 :=
  phaseBlock_append receipt_1_15_2403_0_part14 receipt_1_15_2403_0_part15 rfl rfl rfl
private theorem receipt_1_15_2403_0_join12 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 1536 399 = 55213826747703984575035837528 :=
  phaseBlock_append receipt_1_15_2403_0_join10 receipt_1_15_2403_0_join11 rfl rfl rfl
private theorem receipt_1_15_2403_0_join13 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 1024 911 = 302740657761022169341324337064 :=
  phaseBlock_append receipt_1_15_2403_0_join9 receipt_1_15_2403_0_join12 rfl rfl rfl
private theorem receipt_1_15_2403_0_join14 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 0) 0 1935 = 1511092878726252732565865523112 :=
  phaseBlock_append receipt_1_15_2403_0_join6 receipt_1_15_2403_0_join13 rfl rfl rfl

private theorem receipt_1_15_2403_0 : fastPhase (bank 1 15).shape 179798 2403 76 1 0 2 0 = 1511092878726252732565865523112 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_15_2403_0_join14

private theorem receipt_1_15_2403_1_part0 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 0 128 = 209548832817497171414896741056 := by decide +kernel
private theorem receipt_1_15_2403_1_part1 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 128 128 = 191719545572833771194058418880 := by decide +kernel
private theorem receipt_1_15_2403_1_part2 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 256 128 = 174440266736030384144539339456 := by decide +kernel
private theorem receipt_1_15_2403_1_part3 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 384 128 = 157702087635675530076401068736 := by decide +kernel
private theorem receipt_1_15_2403_1_part4 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 512 128 = 141496125403773053542550112960 := by decide +kernel
private theorem receipt_1_15_2403_1_part5 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 640 128 = 125813522950570520358945729216 := by decide +kernel
private theorem receipt_1_15_2403_1_part6 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 768 128 = 110645448939387614124807736000 := by decide +kernel
private theorem receipt_1_15_2403_1_part7 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 896 128 = 95983097761444532742824323776 := by decide +kernel
private theorem receipt_1_15_2403_1_part8 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 1024 128 = 81817689510690384939359865536 := by decide +kernel
private theorem receipt_1_15_2403_1_part9 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 1152 128 = 68140469958631586784662727360 := by decide +kernel
private theorem receipt_1_15_2403_1_part10 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 1280 128 = 54942713521485190763127737968 := by decide +kernel
private theorem receipt_1_15_2403_1_part11 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 1408 128 = 42215736106770942762189421673 := by decide +kernel
private theorem receipt_1_15_2403_1_part12 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 1536 128 = 29950848662742866915004066481 := by decide +kernel
private theorem receipt_1_15_2403_1_part13 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 1664 128 = 18139371044661819024426988178 := by decide +kernel
private theorem receipt_1_15_2403_1_part14 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 1792 128 = 6772648657424876512842004562 := by decide +kernel
private theorem receipt_1_15_2403_1_part15 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 1920 15 = 69837404306500284153285677 := by decide +kernel
private theorem receipt_1_15_2403_1_join0 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 0 256 = 401268378390330942608955159936 :=
  phaseBlock_append receipt_1_15_2403_1_part0 receipt_1_15_2403_1_part1 rfl rfl rfl
private theorem receipt_1_15_2403_1_join1 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 256 256 = 332142354371705914220940408192 :=
  phaseBlock_append receipt_1_15_2403_1_part2 receipt_1_15_2403_1_part3 rfl rfl rfl
private theorem receipt_1_15_2403_1_join2 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 0 512 = 733410732762036856829895568128 :=
  phaseBlock_append receipt_1_15_2403_1_join0 receipt_1_15_2403_1_join1 rfl rfl rfl
private theorem receipt_1_15_2403_1_join3 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 512 256 = 267309648354343573901495842176 :=
  phaseBlock_append receipt_1_15_2403_1_part4 receipt_1_15_2403_1_part5 rfl rfl rfl
private theorem receipt_1_15_2403_1_join4 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 768 256 = 206628546700832146867632059776 :=
  phaseBlock_append receipt_1_15_2403_1_part6 receipt_1_15_2403_1_part7 rfl rfl rfl
private theorem receipt_1_15_2403_1_join5 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 512 512 = 473938195055175720769127901952 :=
  phaseBlock_append receipt_1_15_2403_1_join3 receipt_1_15_2403_1_join4 rfl rfl rfl
private theorem receipt_1_15_2403_1_join6 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 0 1024 = 1207348927817212577599023470080 :=
  phaseBlock_append receipt_1_15_2403_1_join2 receipt_1_15_2403_1_join5 rfl rfl rfl
private theorem receipt_1_15_2403_1_join7 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 1024 256 = 149958159469321971724022592896 :=
  phaseBlock_append receipt_1_15_2403_1_part8 receipt_1_15_2403_1_part9 rfl rfl rfl
private theorem receipt_1_15_2403_1_join8 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 1280 256 = 97158449628256133525317159641 :=
  phaseBlock_append receipt_1_15_2403_1_part10 receipt_1_15_2403_1_part11 rfl rfl rfl
private theorem receipt_1_15_2403_1_join9 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 1024 512 = 247116609097578105249339752537 :=
  phaseBlock_append receipt_1_15_2403_1_join7 receipt_1_15_2403_1_join8 rfl rfl rfl
private theorem receipt_1_15_2403_1_join10 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 1536 256 = 48090219707404685939431054659 :=
  phaseBlock_append receipt_1_15_2403_1_part12 receipt_1_15_2403_1_part13 rfl rfl rfl
private theorem receipt_1_15_2403_1_join11 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 1792 143 = 6842486061731376796995290239 :=
  phaseBlock_append receipt_1_15_2403_1_part14 receipt_1_15_2403_1_part15 rfl rfl rfl
private theorem receipt_1_15_2403_1_join12 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 1536 399 = 54932705769136062736426344898 :=
  phaseBlock_append receipt_1_15_2403_1_join10 receipt_1_15_2403_1_join11 rfl rfl rfl
private theorem receipt_1_15_2403_1_join13 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 1024 911 = 302049314866714167985766097435 :=
  phaseBlock_append receipt_1_15_2403_1_join9 receipt_1_15_2403_1_join12 rfl rfl rfl
private theorem receipt_1_15_2403_1_join14 :
    phaseBlock (fastLayer (bank 1 15).shape 179798 2403 76 1 0 2 1) 0 1935 = 1509398242683926745584789567515 :=
  phaseBlock_append receipt_1_15_2403_1_join6 receipt_1_15_2403_1_join13 rfl rfl rfl

private theorem receipt_1_15_2403_1 : fastPhase (bank 1 15).shape 179798 2403 76 1 0 2 1 = 1509398242683926745584789567515 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_15_2403_1_join14

theorem receipt_1_15 : Checked (bank 1 15) 76 0 2 := by
  refine checked_from_values (bank 1 15) 76 0 2
    (P3_7_1.checked (bank 1 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9204_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_15_2402_0 receipt_1_15_2402_1 receipt_1_15_2403_0 receipt_1_15_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_15_2402_0_part0 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 0 128 = 112456922101268248408139939040 := by decide +kernel
private theorem receipt_2_15_2402_0_part1 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 128 128 = 102577362766281562385478814944 := by decide +kernel
private theorem receipt_2_15_2402_0_part2 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 256 128 = 93049861791705179838838758624 := by decide +kernel
private theorem receipt_2_15_2402_0_part3 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 384 128 = 83866912182331000225354034400 := by decide +kernel
private theorem receipt_2_15_2402_0_part4 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 512 128 = 75021082736754845764737694944 := by decide +kernel
private theorem receipt_2_15_2402_0_part5 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 640 128 = 66505017739035094025779465440 := by decide +kernel
private theorem receipt_2_15_2402_0_part6 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 768 128 = 58311436650351310512843627744 := by decide +kernel
private theorem receipt_2_15_2402_0_part7 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 896 128 = 50433133800662881252366904544 := by decide +kernel
private theorem receipt_2_15_2402_0_part8 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 1024 128 = 42862978080367645379356343520 := by decide +kernel
private theorem receipt_2_15_2402_0_part9 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 1152 128 = 35593912631960527723887201504 := by decide +kernel
private theorem receipt_2_15_2402_0_part10 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 1280 128 = 28618956163935480477466519725 := by decide +kernel
private theorem receipt_2_15_2402_0_part11 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 1408 128 = 21931209204047664631885286463 := by decide +kernel
private theorem receipt_2_15_2402_0_part12 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 1536 128 = 15523829473429479380246812173 := by decide +kernel
private theorem receipt_2_15_2402_0_part13 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 1664 128 = 9390039381145853198697992235 := by decide +kernel
private theorem receipt_2_15_2402_0_part14 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 1792 128 = 3523134240508507575397885122 := by decide +kernel
private theorem receipt_2_15_2402_0_part15 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 1920 15 = 40908588114542704477711020 := by decide +kernel
private theorem receipt_2_15_2402_0_join0 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 0 256 = 215034284867549810793618753984 :=
  phaseBlock_append receipt_2_15_2402_0_part0 receipt_2_15_2402_0_part1 rfl rfl rfl
private theorem receipt_2_15_2402_0_join1 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 256 256 = 176916773974036180064192793024 :=
  phaseBlock_append receipt_2_15_2402_0_part2 receipt_2_15_2402_0_part3 rfl rfl rfl
private theorem receipt_2_15_2402_0_join2 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 0 512 = 391951058841585990857811547008 :=
  phaseBlock_append receipt_2_15_2402_0_join0 receipt_2_15_2402_0_join1 rfl rfl rfl
private theorem receipt_2_15_2402_0_join3 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 512 256 = 141526100475789939790517160384 :=
  phaseBlock_append receipt_2_15_2402_0_part4 receipt_2_15_2402_0_part5 rfl rfl rfl
private theorem receipt_2_15_2402_0_join4 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 768 256 = 108744570451014191765210532288 :=
  phaseBlock_append receipt_2_15_2402_0_part6 receipt_2_15_2402_0_part7 rfl rfl rfl
private theorem receipt_2_15_2402_0_join5 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 512 512 = 250270670926804131555727692672 :=
  phaseBlock_append receipt_2_15_2402_0_join3 receipt_2_15_2402_0_join4 rfl rfl rfl
private theorem receipt_2_15_2402_0_join6 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 0 1024 = 642221729768390122413539239680 :=
  phaseBlock_append receipt_2_15_2402_0_join2 receipt_2_15_2402_0_join5 rfl rfl rfl
private theorem receipt_2_15_2402_0_join7 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 1024 256 = 78456890712328173103243545024 :=
  phaseBlock_append receipt_2_15_2402_0_part8 receipt_2_15_2402_0_part9 rfl rfl rfl
private theorem receipt_2_15_2402_0_join8 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 1280 256 = 50550165367983145109351806188 :=
  phaseBlock_append receipt_2_15_2402_0_part10 receipt_2_15_2402_0_part11 rfl rfl rfl
private theorem receipt_2_15_2402_0_join9 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 1024 512 = 129007056080311318212595351212 :=
  phaseBlock_append receipt_2_15_2402_0_join7 receipt_2_15_2402_0_join8 rfl rfl rfl
private theorem receipt_2_15_2402_0_join10 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 1536 256 = 24913868854575332578944804408 :=
  phaseBlock_append receipt_2_15_2402_0_part12 receipt_2_15_2402_0_part13 rfl rfl rfl
private theorem receipt_2_15_2402_0_join11 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 1792 143 = 3564042828623050279875596142 :=
  phaseBlock_append receipt_2_15_2402_0_part14 receipt_2_15_2402_0_part15 rfl rfl rfl
private theorem receipt_2_15_2402_0_join12 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 1536 399 = 28477911683198382858820400550 :=
  phaseBlock_append receipt_2_15_2402_0_join10 receipt_2_15_2402_0_join11 rfl rfl rfl
private theorem receipt_2_15_2402_0_join13 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 1024 911 = 157484967763509701071415751762 :=
  phaseBlock_append receipt_2_15_2402_0_join9 receipt_2_15_2402_0_join12 rfl rfl rfl
private theorem receipt_2_15_2402_0_join14 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 0) 0 1935 = 799706697531899823484954991442 :=
  phaseBlock_append receipt_2_15_2402_0_join6 receipt_2_15_2402_0_join13 rfl rfl rfl

private theorem receipt_2_15_2402_0 : fastPhase (bank 2 15).shape 179798 2402 76 1 0 7 0 = 799706697531899823484954991442 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_15_2402_0_join14

private theorem receipt_2_15_2402_1_part0 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 0 128 = 112379360915474884447310374176 := by decide +kernel
private theorem receipt_2_15_2402_1_part1 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 128 128 = 102502501512041076799116113184 := by decide +kernel
private theorem receipt_2_15_2402_1_part2 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 256 128 = 92977643189590117943980066080 := by decide +kernel
private theorem receipt_2_15_2402_1_part3 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 384 128 = 83797279532079839756922688800 := by decide +kernel
private theorem receipt_2_15_2402_1_part4 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 512 128 = 74953979914911608812462482720 := by decide +kernel
private theorem receipt_2_15_2402_1_part5 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 640 128 = 66440389196588958971113878816 := by decide +kernel
private theorem receipt_2_15_2402_1_part6 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 768 128 = 58249227410376223965885121824 := by decide +kernel
private theorem receipt_2_15_2402_1_part7 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 896 128 = 50373289455957169988776154400 := by decide +kernel
private theorem receipt_2_15_2402_1_part8 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 1024 128 = 42805444791093628277276501280 := by decide +kernel
private theorem receipt_2_15_2402_1_part9 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 1152 128 = 35538637123284127700863153440 := by decide +kernel
private theorem receipt_2_15_2402_1_part10 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 1280 128 = 28565885720671151448600469581 := by decide +kernel
private theorem receipt_2_15_2402_1_part11 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 1408 128 = 21880291647024162857095122783 := by decide +kernel
private theorem receipt_2_15_2402_1_part12 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 1536 128 = 15475013170539767173515886422 := by decide +kernel
private theorem receipt_2_15_2402_1_part13 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 1664 128 = 9343273256694970715159686251 := by decide +kernel
private theorem receipt_2_15_2402_1_part14 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 1792 128 = 3478367772900997158365417298 := by decide +kernel
private theorem receipt_2_15_2402_1_part15 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 1920 15 = 35791101557464661926289583 := by decide +kernel
private theorem receipt_2_15_2402_1_join0 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 0 256 = 214881862427515961246426487360 :=
  phaseBlock_append receipt_2_15_2402_1_part0 receipt_2_15_2402_1_part1 rfl rfl rfl
private theorem receipt_2_15_2402_1_join1 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 256 256 = 176774922721669957700902754880 :=
  phaseBlock_append receipt_2_15_2402_1_part2 receipt_2_15_2402_1_part3 rfl rfl rfl
private theorem receipt_2_15_2402_1_join2 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 0 512 = 391656785149185918947329242240 :=
  phaseBlock_append receipt_2_15_2402_1_join0 receipt_2_15_2402_1_join1 rfl rfl rfl
private theorem receipt_2_15_2402_1_join3 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 512 256 = 141394369111500567783576361536 :=
  phaseBlock_append receipt_2_15_2402_1_part4 receipt_2_15_2402_1_part5 rfl rfl rfl
private theorem receipt_2_15_2402_1_join4 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 768 256 = 108622516866333393954661276224 :=
  phaseBlock_append receipt_2_15_2402_1_part6 receipt_2_15_2402_1_part7 rfl rfl rfl
private theorem receipt_2_15_2402_1_join5 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 512 512 = 250016885977833961738237637760 :=
  phaseBlock_append receipt_2_15_2402_1_join3 receipt_2_15_2402_1_join4 rfl rfl rfl
private theorem receipt_2_15_2402_1_join6 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 0 1024 = 641673671127019880685566880000 :=
  phaseBlock_append receipt_2_15_2402_1_join2 receipt_2_15_2402_1_join5 rfl rfl rfl
private theorem receipt_2_15_2402_1_join7 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 1024 256 = 78344081914377755978139654720 :=
  phaseBlock_append receipt_2_15_2402_1_part8 receipt_2_15_2402_1_part9 rfl rfl rfl
private theorem receipt_2_15_2402_1_join8 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 1280 256 = 50446177367695314305695592364 :=
  phaseBlock_append receipt_2_15_2402_1_part10 receipt_2_15_2402_1_part11 rfl rfl rfl
private theorem receipt_2_15_2402_1_join9 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 1024 512 = 128790259282073070283835247084 :=
  phaseBlock_append receipt_2_15_2402_1_join7 receipt_2_15_2402_1_join8 rfl rfl rfl
private theorem receipt_2_15_2402_1_join10 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 1536 256 = 24818286427234737888675572673 :=
  phaseBlock_append receipt_2_15_2402_1_part12 receipt_2_15_2402_1_part13 rfl rfl rfl
private theorem receipt_2_15_2402_1_join11 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 1792 143 = 3514158874458461820291706881 :=
  phaseBlock_append receipt_2_15_2402_1_part14 receipt_2_15_2402_1_part15 rfl rfl rfl
private theorem receipt_2_15_2402_1_join12 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 1536 399 = 28332445301693199708967279554 :=
  phaseBlock_append receipt_2_15_2402_1_join10 receipt_2_15_2402_1_join11 rfl rfl rfl
private theorem receipt_2_15_2402_1_join13 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 1024 911 = 157122704583766269992802526638 :=
  phaseBlock_append receipt_2_15_2402_1_join9 receipt_2_15_2402_1_join12 rfl rfl rfl
private theorem receipt_2_15_2402_1_join14 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2402 76 1 0 7 1) 0 1935 = 798796375710786150678369406638 :=
  phaseBlock_append receipt_2_15_2402_1_join6 receipt_2_15_2402_1_join13 rfl rfl rfl

private theorem receipt_2_15_2402_1 : fastPhase (bank 2 15).shape 179798 2402 76 1 0 7 1 = 798796375710786150678369406638 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_15_2402_1_join14

private theorem receipt_2_15_2403_0_part0 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 0 128 = 112457929987343433089711163840 := by decide +kernel
private theorem receipt_2_15_2403_0_part1 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 128 128 = 102578247985264497607802038720 := by decide +kernel
private theorem receipt_2_15_2403_0_part2 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 256 128 = 93050633200624268523530160576 := by decide +kernel
private theorem receipt_2_15_2403_0_part3 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 384 128 = 83867578401479903352410270144 := by decide +kernel
private theorem receipt_2_15_2403_0_part4 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 512 128 = 75021652152260004922912459200 := by decide +kernel
private theorem receipt_2_15_2403_0_part5 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 640 128 = 66505498505412478749007849920 := by decide +kernel
private theorem receipt_2_15_2403_0_part6 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 768 128 = 58311836693052390402714274240 := by decide +kernel
private theorem receipt_2_15_2403_0_part7 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 896 128 = 50433460818609822886641953216 := by decide +kernel
private theorem receipt_2_15_2403_0_part8 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 1024 128 = 42863239548477734006539176384 := by decide +kernel
private theorem receipt_2_15_2403_0_part9 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 1152 128 = 35594115803659813743837981120 := by decide +kernel
private theorem receipt_2_15_2403_0_part10 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 1280 128 = 28619108008478556689564096365 := by decide +kernel
private theorem receipt_2_15_2403_0_part11 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 1408 128 = 21931316449826971450766692560 := by decide +kernel
private theorem receipt_2_15_2403_0_part12 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 1536 128 = 15523898825154534049632822455 := by decide +kernel
private theorem receipt_2_15_2403_0_part13 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 1664 128 = 9390077327144498991363693228 := by decide +kernel
private theorem receipt_2_15_2403_0_part14 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 1792 128 = 3523147045081162959084902175 := by decide +kernel
private theorem receipt_2_15_2403_0_part15 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 1920 15 = 40908724346573309016344844 := by decide +kernel
private theorem receipt_2_15_2403_0_join0 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 0 256 = 215036177972607930697513202560 :=
  phaseBlock_append receipt_2_15_2403_0_part0 receipt_2_15_2403_0_part1 rfl rfl rfl
private theorem receipt_2_15_2403_0_join1 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 256 256 = 176918211602104171875940430720 :=
  phaseBlock_append receipt_2_15_2403_0_part2 receipt_2_15_2403_0_part3 rfl rfl rfl
private theorem receipt_2_15_2403_0_join2 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 0 512 = 391954389574712102573453633280 :=
  phaseBlock_append receipt_2_15_2403_0_join0 receipt_2_15_2403_0_join1 rfl rfl rfl
private theorem receipt_2_15_2403_0_join3 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 512 256 = 141527150657672483671920309120 :=
  phaseBlock_append receipt_2_15_2403_0_part4 receipt_2_15_2403_0_part5 rfl rfl rfl
private theorem receipt_2_15_2403_0_join4 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 768 256 = 108745297511662213289356227456 :=
  phaseBlock_append receipt_2_15_2403_0_part6 receipt_2_15_2403_0_part7 rfl rfl rfl
private theorem receipt_2_15_2403_0_join5 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 512 512 = 250272448169334696961276536576 :=
  phaseBlock_append receipt_2_15_2403_0_join3 receipt_2_15_2403_0_join4 rfl rfl rfl
private theorem receipt_2_15_2403_0_join6 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 0 1024 = 642226837744046799534730169856 :=
  phaseBlock_append receipt_2_15_2403_0_join2 receipt_2_15_2403_0_join5 rfl rfl rfl
private theorem receipt_2_15_2403_0_join7 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 1024 256 = 78457355352137547750377157504 :=
  phaseBlock_append receipt_2_15_2403_0_part8 receipt_2_15_2403_0_part9 rfl rfl rfl
private theorem receipt_2_15_2403_0_join8 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 1280 256 = 50550424458305528140330788925 :=
  phaseBlock_append receipt_2_15_2403_0_part10 receipt_2_15_2403_0_part11 rfl rfl rfl
private theorem receipt_2_15_2403_0_join9 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 1024 512 = 129007779810443075890707946429 :=
  phaseBlock_append receipt_2_15_2403_0_join7 receipt_2_15_2403_0_join8 rfl rfl rfl
private theorem receipt_2_15_2403_0_join10 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 1536 256 = 24913976152299033040996515683 :=
  phaseBlock_append receipt_2_15_2403_0_part12 receipt_2_15_2403_0_part13 rfl rfl rfl
private theorem receipt_2_15_2403_0_join11 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 1792 143 = 3564055769427736268101247019 :=
  phaseBlock_append receipt_2_15_2403_0_part14 receipt_2_15_2403_0_part15 rfl rfl rfl
private theorem receipt_2_15_2403_0_join12 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 1536 399 = 28478031921726769309097762702 :=
  phaseBlock_append receipt_2_15_2403_0_join10 receipt_2_15_2403_0_join11 rfl rfl rfl
private theorem receipt_2_15_2403_0_join13 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 1024 911 = 157485811732169845199805709131 :=
  phaseBlock_append receipt_2_15_2403_0_join9 receipt_2_15_2403_0_join12 rfl rfl rfl
private theorem receipt_2_15_2403_0_join14 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 0) 0 1935 = 799712649476216644734535878987 :=
  phaseBlock_append receipt_2_15_2403_0_join6 receipt_2_15_2403_0_join13 rfl rfl rfl

private theorem receipt_2_15_2403_0 : fastPhase (bank 2 15).shape 179798 2403 76 1 0 7 0 = 799712649476216644734535878987 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_15_2403_0_join14

private theorem receipt_2_15_2403_1_part0 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 0 128 = 112380368227431920607797045184 := by decide +kernel
private theorem receipt_2_15_2403_1_part1 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 128 128 = 102503386193796921592190142400 := by decide +kernel
private theorem receipt_2_15_2403_1_part2 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 256 128 = 92978414097006262683709482944 := by decide +kernel
private theorem receipt_2_15_2403_1_part3 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 384 128 = 83797945284297235842379761600 := by decide +kernel
private theorem receipt_2_15_2403_1_part4 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 512 128 = 74954548896918126300267440064 := by decide +kernel
private theorem receipt_2_15_2403_1_part5 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 640 128 = 66440869561776069934026426304 := by decide +kernel
private theorem receipt_2_15_2403_1_part6 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 768 128 = 58249627083084910637443753920 := by decide +kernel
private theorem receipt_2_15_2403_1_part7 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 896 128 = 50373616134013057693985261504 := by decide +kernel
private theorem receipt_2_15_2403_1_part8 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 1024 128 = 42805705948331343149341272000 := by decide +kernel
private theorem receipt_2_15_2403_1_part9 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 1152 128 = 35538840012060879183972272064 := by decide +kernel
private theorem receipt_2_15_2403_1_part10 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 1280 128 = 28566037309304959356212207284 := by decide +kernel
private theorem receipt_2_15_2403_1_part11 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 1408 128 = 21880398663118504200619000130 := by decide +kernel
private theorem receipt_2_15_2403_1_part12 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 1536 128 = 15475082317750979476973680923 := by decide +kernel
private theorem receipt_2_15_2403_1_part13 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 1664 128 = 9343311022295968314765647736 := by decide +kernel
private theorem receipt_2_15_2403_1_part14 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 1792 128 = 3478380420154677590123329852 := by decide +kernel
private theorem receipt_2_15_2403_1_part15 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 1920 15 = 35791220816443302117814151 := by decide +kernel
private theorem receipt_2_15_2403_1_join0 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 0 256 = 214883754421228842199987187584 :=
  phaseBlock_append receipt_2_15_2403_1_part0 receipt_2_15_2403_1_part1 rfl rfl rfl
private theorem receipt_2_15_2403_1_join1 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 256 256 = 176776359381303498526089244544 :=
  phaseBlock_append receipt_2_15_2403_1_part2 receipt_2_15_2403_1_part3 rfl rfl rfl
private theorem receipt_2_15_2403_1_join2 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 0 512 = 391660113802532340726076432128 :=
  phaseBlock_append receipt_2_15_2403_1_join0 receipt_2_15_2403_1_join1 rfl rfl rfl
private theorem receipt_2_15_2403_1_join3 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 512 256 = 141395418458694196234293866368 :=
  phaseBlock_append receipt_2_15_2403_1_part4 receipt_2_15_2403_1_part5 rfl rfl rfl
private theorem receipt_2_15_2403_1_join4 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 768 256 = 108623243217097968331429015424 :=
  phaseBlock_append receipt_2_15_2403_1_part6 receipt_2_15_2403_1_part7 rfl rfl rfl
private theorem receipt_2_15_2403_1_join5 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 512 512 = 250018661675792164565722881792 :=
  phaseBlock_append receipt_2_15_2403_1_join3 receipt_2_15_2403_1_join4 rfl rfl rfl
private theorem receipt_2_15_2403_1_join6 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 0 1024 = 641678775478324505291799313920 :=
  phaseBlock_append receipt_2_15_2403_1_join2 receipt_2_15_2403_1_join5 rfl rfl rfl
private theorem receipt_2_15_2403_1_join7 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 1024 256 = 78344545960392222333313544064 :=
  phaseBlock_append receipt_2_15_2403_1_part8 receipt_2_15_2403_1_part9 rfl rfl rfl
private theorem receipt_2_15_2403_1_join8 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 1280 256 = 50446435972423463556831207414 :=
  phaseBlock_append receipt_2_15_2403_1_part10 receipt_2_15_2403_1_part11 rfl rfl rfl
private theorem receipt_2_15_2403_1_join9 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 1024 512 = 128790981932815685890144751478 :=
  phaseBlock_append receipt_2_15_2403_1_join7 receipt_2_15_2403_1_join8 rfl rfl rfl
private theorem receipt_2_15_2403_1_join10 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 1536 256 = 24818393340046947791739328659 :=
  phaseBlock_append receipt_2_15_2403_1_part12 receipt_2_15_2403_1_part13 rfl rfl rfl
private theorem receipt_2_15_2403_1_join11 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 1792 143 = 3514171640971120892241144003 :=
  phaseBlock_append receipt_2_15_2403_1_part14 receipt_2_15_2403_1_part15 rfl rfl rfl
private theorem receipt_2_15_2403_1_join12 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 1536 399 = 28332564981018068683980472662 :=
  phaseBlock_append receipt_2_15_2403_1_join10 receipt_2_15_2403_1_join11 rfl rfl rfl
private theorem receipt_2_15_2403_1_join13 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 1024 911 = 157123546913833754574125224140 :=
  phaseBlock_append receipt_2_15_2403_1_join9 receipt_2_15_2403_1_join12 rfl rfl rfl
private theorem receipt_2_15_2403_1_join14 :
    phaseBlock (fastLayer (bank 2 15).shape 179798 2403 76 1 0 7 1) 0 1935 = 798802322392158259865924538060 :=
  phaseBlock_append receipt_2_15_2403_1_join6 receipt_2_15_2403_1_join13 rfl rfl rfl

private theorem receipt_2_15_2403_1 : fastPhase (bank 2 15).shape 179798 2403 76 1 0 7 1 = 798802322392158259865924538060 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_15_2403_1_join14

theorem receipt_2_15 : Checked (bank 2 15) 76 0 7 := by
  refine checked_from_values (bank 2 15) 76 0 7
    (P3_7_1.checked (bank 2 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9204_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_15_2402_0 receipt_2_15_2402_1 receipt_2_15_2403_0 receipt_2_15_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_15_2402_0_part0 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 0 128 = 23040055009940168479685659104 := by decide +kernel
private theorem receipt_3_15_2402_0_part1 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 128 128 = 21113975081783672419736844768 := by decide +kernel
private theorem receipt_3_15_2402_0_part2 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 256 128 = 19241173758986843226529081824 := by decide +kernel
private theorem receipt_3_15_2402_0_part3 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 384 128 = 17422680395726251993376545248 := by decide +kernel
private theorem receipt_3_15_2402_0_part4 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 512 128 = 15659518523032123666959010272 := by decide +kernel
private theorem receipt_3_15_2402_0_part5 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 640 128 = 13952705858204862490851293664 := by decide +kernel
private theorem receipt_3_15_2402_0_part6 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 768 128 = 12303254314231577449052695008 := by decide +kernel
private theorem receipt_3_15_2402_0_part7 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 896 128 = 10712170009202607709516437984 := by decide +kernel
private theorem receipt_3_15_2402_0_part8 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 1024 128 = 9180453275728048067679111648 := by decide +kernel
private theorem receipt_3_15_2402_0_part9 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 1152 128 = 7709098670354274389990111712 := by decide +kernel
private theorem receipt_3_15_2402_0_part10 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 1280 128 = 6299094982980469057441081824 := by decide +kernel
private theorem receipt_3_15_2402_0_part11 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 1408 128 = 4951425246275146409095354848 := by decide +kernel
private theorem receipt_3_15_2402_0_part12 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 1536 128 = 3667066745092678185617394144 := by decide +kernel
private theorem receipt_3_15_2402_0_part13 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 1664 128 = 2446991025889818972802234848 := by decide +kernel
private theorem receipt_3_15_2402_0_part14 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 1792 128 = 1292163906142231645104925152 := by decide +kernel
private theorem receipt_3_15_2402_0_part15 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 1920 88 = 252839497625446671518987298 := by decide +kernel
private theorem receipt_3_15_2402_0_join0 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 0 256 = 44154030091723840899422503872 :=
  phaseBlock_append receipt_3_15_2402_0_part0 receipt_3_15_2402_0_part1 rfl rfl rfl
private theorem receipt_3_15_2402_0_join1 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 256 256 = 36663854154713095219905627072 :=
  phaseBlock_append receipt_3_15_2402_0_part2 receipt_3_15_2402_0_part3 rfl rfl rfl
private theorem receipt_3_15_2402_0_join2 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 0 512 = 80817884246436936119328130944 :=
  phaseBlock_append receipt_3_15_2402_0_join0 receipt_3_15_2402_0_join1 rfl rfl rfl
private theorem receipt_3_15_2402_0_join3 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 512 256 = 29612224381236986157810303936 :=
  phaseBlock_append receipt_3_15_2402_0_part4 receipt_3_15_2402_0_part5 rfl rfl rfl
private theorem receipt_3_15_2402_0_join4 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 768 256 = 23015424323434185158569132992 :=
  phaseBlock_append receipt_3_15_2402_0_part6 receipt_3_15_2402_0_part7 rfl rfl rfl
private theorem receipt_3_15_2402_0_join5 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 512 512 = 52627648704671171316379436928 :=
  phaseBlock_append receipt_3_15_2402_0_join3 receipt_3_15_2402_0_join4 rfl rfl rfl
private theorem receipt_3_15_2402_0_join6 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 0 1024 = 133445532951108107435707567872 :=
  phaseBlock_append receipt_3_15_2402_0_join2 receipt_3_15_2402_0_join5 rfl rfl rfl
private theorem receipt_3_15_2402_0_join7 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 1024 256 = 16889551946082322457669223360 :=
  phaseBlock_append receipt_3_15_2402_0_part8 receipt_3_15_2402_0_part9 rfl rfl rfl
private theorem receipt_3_15_2402_0_join8 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 1280 256 = 11250520229255615466536436672 :=
  phaseBlock_append receipt_3_15_2402_0_part10 receipt_3_15_2402_0_part11 rfl rfl rfl
private theorem receipt_3_15_2402_0_join9 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 1024 512 = 28140072175337937924205660032 :=
  phaseBlock_append receipt_3_15_2402_0_join7 receipt_3_15_2402_0_join8 rfl rfl rfl
private theorem receipt_3_15_2402_0_join10 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 1536 256 = 6114057770982497158419628992 :=
  phaseBlock_append receipt_3_15_2402_0_part12 receipt_3_15_2402_0_part13 rfl rfl rfl
private theorem receipt_3_15_2402_0_join11 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 1792 216 = 1545003403767678316623912450 :=
  phaseBlock_append receipt_3_15_2402_0_part14 receipt_3_15_2402_0_part15 rfl rfl rfl
private theorem receipt_3_15_2402_0_join12 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 1536 472 = 7659061174750175475043541442 :=
  phaseBlock_append receipt_3_15_2402_0_join10 receipt_3_15_2402_0_join11 rfl rfl rfl
private theorem receipt_3_15_2402_0_join13 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 1024 984 = 35799133350088113399249201474 :=
  phaseBlock_append receipt_3_15_2402_0_join9 receipt_3_15_2402_0_join12 rfl rfl rfl
private theorem receipt_3_15_2402_0_join14 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 0) 0 2008 = 169244666301196220834956769346 :=
  phaseBlock_append receipt_3_15_2402_0_join6 receipt_3_15_2402_0_join13 rfl rfl rfl

private theorem receipt_3_15_2402_0 : fastPhase (bank 3 15).shape 179798 2402 76 1 1 1 0 = 169244666301196220834956769346 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_15_2402_0_join14

private theorem receipt_3_15_2402_1_part0 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 0 128 = 23025009212116552547398261728 := by decide +kernel
private theorem receipt_3_15_2402_1_part1 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 128 128 = 21099323203097419967143513056 := by decide +kernel
private theorem receipt_3_15_2402_1_part2 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 256 128 = 19226924548599721767117126624 := by decide +kernel
private theorem receipt_3_15_2402_1_part3 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 384 128 = 17408842554841220924722211808 := by decide +kernel
private theorem receipt_3_15_2402_1_part4 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 512 128 = 15646100704969872031051209696 := by decide +kernel
private theorem receipt_3_15_2402_1_part5 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 640 128 = 13939716668480346734415334368 := by decide +kernel
private theorem receipt_3_15_2402_1_part6 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 768 128 = 12290702310630559183874014176 := by decide +kernel
private theorem receipt_3_15_2402_1_part7 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 896 128 = 10700063701858191472764333024 := by decide +kernel
private theorem receipt_3_15_2402_1_part8 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 1024 128 = 9168801127197219082230471648 := by decide +kernel
private theorem receipt_3_15_2402_1_part9 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 1152 128 = 7697909095694436324753148896 := by decide +kernel
private theorem receipt_3_15_2402_1_part10 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 1280 128 = 6288376349825981787679063008 := by decide +kernel
private theorem receipt_3_15_2402_1_part11 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 1408 128 = 4941185874913863776750332896 := by decide +kernel
private theorem receipt_3_15_2402_1_part12 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 1536 128 = 3657314908542485759633939424 := by decide +kernel
private theorem receipt_3_15_2402_1_part13 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 1664 128 = 2437734949975171809451166688 := by decide +kernel
private theorem receipt_3_15_2402_1_part14 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 1792 128 = 1283411769570692048307043296 := by decide +kernel
private theorem receipt_3_15_2402_1_part15 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 1920 88 = 247118955477089473350973026 := by decide +kernel
private theorem receipt_3_15_2402_1_join0 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 0 256 = 44124332415213972514541774784 :=
  phaseBlock_append receipt_3_15_2402_1_part0 receipt_3_15_2402_1_part1 rfl rfl rfl
private theorem receipt_3_15_2402_1_join1 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 256 256 = 36635767103440942691839338432 :=
  phaseBlock_append receipt_3_15_2402_1_part2 receipt_3_15_2402_1_part3 rfl rfl rfl
private theorem receipt_3_15_2402_1_join2 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 0 512 = 80760099518654915206381113216 :=
  phaseBlock_append receipt_3_15_2402_1_join0 receipt_3_15_2402_1_join1 rfl rfl rfl
private theorem receipt_3_15_2402_1_join3 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 512 256 = 29585817373450218765466544064 :=
  phaseBlock_append receipt_3_15_2402_1_part4 receipt_3_15_2402_1_part5 rfl rfl rfl
private theorem receipt_3_15_2402_1_join4 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 768 256 = 22990766012488750656638347200 :=
  phaseBlock_append receipt_3_15_2402_1_part6 receipt_3_15_2402_1_part7 rfl rfl rfl
private theorem receipt_3_15_2402_1_join5 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 512 512 = 52576583385938969422104891264 :=
  phaseBlock_append receipt_3_15_2402_1_join3 receipt_3_15_2402_1_join4 rfl rfl rfl
private theorem receipt_3_15_2402_1_join6 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 0 1024 = 133336682904593884628486004480 :=
  phaseBlock_append receipt_3_15_2402_1_join2 receipt_3_15_2402_1_join5 rfl rfl rfl
private theorem receipt_3_15_2402_1_join7 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 1024 256 = 16866710222891655406983620544 :=
  phaseBlock_append receipt_3_15_2402_1_part8 receipt_3_15_2402_1_part9 rfl rfl rfl
private theorem receipt_3_15_2402_1_join8 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 1280 256 = 11229562224739845564429395904 :=
  phaseBlock_append receipt_3_15_2402_1_part10 receipt_3_15_2402_1_part11 rfl rfl rfl
private theorem receipt_3_15_2402_1_join9 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 1024 512 = 28096272447631500971413016448 :=
  phaseBlock_append receipt_3_15_2402_1_join7 receipt_3_15_2402_1_join8 rfl rfl rfl
private theorem receipt_3_15_2402_1_join10 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 1536 256 = 6095049858517657569085106112 :=
  phaseBlock_append receipt_3_15_2402_1_part12 receipt_3_15_2402_1_part13 rfl rfl rfl
private theorem receipt_3_15_2402_1_join11 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 1792 216 = 1530530725047781521658016322 :=
  phaseBlock_append receipt_3_15_2402_1_part14 receipt_3_15_2402_1_part15 rfl rfl rfl
private theorem receipt_3_15_2402_1_join12 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 1536 472 = 7625580583565439090743122434 :=
  phaseBlock_append receipt_3_15_2402_1_join10 receipt_3_15_2402_1_join11 rfl rfl rfl
private theorem receipt_3_15_2402_1_join13 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 1024 984 = 35721853031196940062156138882 :=
  phaseBlock_append receipt_3_15_2402_1_join9 receipt_3_15_2402_1_join12 rfl rfl rfl
private theorem receipt_3_15_2402_1_join14 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2402 76 1 1 1 1) 0 2008 = 169058535935790824690642143362 :=
  phaseBlock_append receipt_3_15_2402_1_join6 receipt_3_15_2402_1_join13 rfl rfl rfl

private theorem receipt_3_15_2402_1 : fastPhase (bank 3 15).shape 179798 2402 76 1 1 1 1 = 169058535935790824690642143362 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_15_2402_1_join14

private theorem receipt_3_15_2403_0_part0 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 0 128 = 23040260159517124979081767200 := by decide +kernel
private theorem receipt_3_15_2403_0_part1 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 128 128 = 21114150810928093700724554016 := by decide +kernel
private theorem receipt_3_15_2403_0_part2 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 256 128 = 19241322847189788632996350240 := by decide +kernel
private theorem receipt_3_15_2403_0_part3 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 384 128 = 17422805498824476491324070176 := by decide +kernel
private theorem receipt_3_15_2403_0_part4 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 512 128 = 15659622173785658999152355616 := by decide +kernel
private theorem receipt_3_15_2403_0_part5 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 640 128 = 13952790466873718722170796320 := by decide +kernel
private theorem receipt_3_15_2403_0_part6 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 768 128 = 12303322169151564902541150496 := by decide +kernel
private theorem receipt_3_15_2403_0_part7 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 896 128 = 10712223277360279293124565280 := by decide +kernel
private theorem receipt_3_15_2403_0_part8 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 1024 128 = 9180494003334761991708797216 := by decide +kernel
private theorem receipt_3_15_2403_0_part9 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 1152 128 = 7709128783419377275235432736 := by decide +kernel
private theorem receipt_3_15_2403_0_part10 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 1280 128 = 6299116287883599434027108640 := by decide +kernel
private theorem receipt_3_15_2403_0_part11 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 1408 128 = 4951439430337658606014732576 := by decide +kernel
private theorem receipt_3_15_2403_0_part12 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 1536 128 = 3667075377148186610964703520 := by decide +kernel
private theorem receipt_3_15_2403_0_part13 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 1664 128 = 2446995556853862784706132256 := by decide +kernel
private theorem receipt_3_15_2403_0_part14 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 1792 128 = 1292165669581059813358061856 := by decide +kernel
private theorem receipt_3_15_2403_0_part15 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 1920 88 = 252839741639195607673973262 := by decide +kernel
private theorem receipt_3_15_2403_0_join0 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 0 256 = 44154410970445218679806321216 :=
  phaseBlock_append receipt_3_15_2403_0_part0 receipt_3_15_2403_0_part1 rfl rfl rfl
private theorem receipt_3_15_2403_0_join1 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 256 256 = 36664128346014265124320420416 :=
  phaseBlock_append receipt_3_15_2403_0_part2 receipt_3_15_2403_0_part3 rfl rfl rfl
private theorem receipt_3_15_2403_0_join2 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 0 512 = 80818539316459483804126741632 :=
  phaseBlock_append receipt_3_15_2403_0_join0 receipt_3_15_2403_0_join1 rfl rfl rfl
private theorem receipt_3_15_2403_0_join3 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 512 256 = 29612412640659377721323151936 :=
  phaseBlock_append receipt_3_15_2403_0_part4 receipt_3_15_2403_0_part5 rfl rfl rfl
private theorem receipt_3_15_2403_0_join4 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 768 256 = 23015545446511844195665715776 :=
  phaseBlock_append receipt_3_15_2403_0_part6 receipt_3_15_2403_0_part7 rfl rfl rfl
private theorem receipt_3_15_2403_0_join5 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 512 512 = 52627958087171221916988867712 :=
  phaseBlock_append receipt_3_15_2403_0_join3 receipt_3_15_2403_0_join4 rfl rfl rfl
private theorem receipt_3_15_2403_0_join6 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 0 1024 = 133446497403630705721115609344 :=
  phaseBlock_append receipt_3_15_2403_0_join2 receipt_3_15_2403_0_join5 rfl rfl rfl
private theorem receipt_3_15_2403_0_join7 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 1024 256 = 16889622786754139266944229952 :=
  phaseBlock_append receipt_3_15_2403_0_part8 receipt_3_15_2403_0_part9 rfl rfl rfl
private theorem receipt_3_15_2403_0_join8 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 1280 256 = 11250555718221258040041841216 :=
  phaseBlock_append receipt_3_15_2403_0_part10 receipt_3_15_2403_0_part11 rfl rfl rfl
private theorem receipt_3_15_2403_0_join9 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 1024 512 = 28140178504975397306986071168 :=
  phaseBlock_append receipt_3_15_2403_0_join7 receipt_3_15_2403_0_join8 rfl rfl rfl
private theorem receipt_3_15_2403_0_join10 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 1536 256 = 6114070934002049395670835776 :=
  phaseBlock_append receipt_3_15_2403_0_part12 receipt_3_15_2403_0_part13 rfl rfl rfl
private theorem receipt_3_15_2403_0_join11 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 1792 216 = 1545005411220255421032035118 :=
  phaseBlock_append receipt_3_15_2403_0_part14 receipt_3_15_2403_0_part15 rfl rfl rfl
private theorem receipt_3_15_2403_0_join12 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 1536 472 = 7659076345222304816702870894 :=
  phaseBlock_append receipt_3_15_2403_0_join10 receipt_3_15_2403_0_join11 rfl rfl rfl
private theorem receipt_3_15_2403_0_join13 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 1024 984 = 35799254850197702123688942062 :=
  phaseBlock_append receipt_3_15_2403_0_join9 receipt_3_15_2403_0_join12 rfl rfl rfl
private theorem receipt_3_15_2403_0_join14 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 0) 0 2008 = 169245752253828407844804551406 :=
  phaseBlock_append receipt_3_15_2403_0_join6 receipt_3_15_2403_0_join13 rfl rfl rfl

private theorem receipt_3_15_2403_0 : fastPhase (bank 3 15).shape 179798 2403 76 1 1 1 0 = 169245752253828407844804551406 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_15_2403_0_join14

private theorem receipt_3_15_2403_1_part0 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 0 128 = 23025214206322614083040225696 := by decide +kernel
private theorem receipt_3_15_2403_1_part1 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 128 128 = 21099498791441371849913711008 := by decide +kernel
private theorem receipt_3_15_2403_1_part2 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 256 128 = 19227073509889403661403998624 := by decide +kernel
private theorem receipt_3_15_2403_1_part3 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 384 128 = 17408967544233672646057974176 := by decide +kernel
private theorem receipt_3_15_2403_1_part4 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 512 128 = 15646204254548909065766889888 := by decide +kernel
private theorem receipt_3_15_2403_1_part5 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 640 128 = 13939801187833256149993585056 := by decide +kernel
private theorem receipt_3_15_2403_1_part6 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 768 128 = 12290770087423915929999706528 := by decide +kernel
private theorem receipt_3_15_2403_1_part7 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 896 128 = 10700116902412795073072929184 := by decide +kernel
private theorem receipt_3_15_2403_1_part8 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 1024 128 = 9168841797062150716754176416 := by decide +kernel
private theorem receipt_3_15_2403_1_part9 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 1152 128 = 7697939160220236303064840608 := by decide +kernel
private theorem receipt_3_15_2403_1_part10 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 1280 128 = 6288397614736947412734003616 := by decide +kernel
private theorem receipt_3_15_2403_1_part11 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 1408 128 = 4941200026879467599425657248 := by decide +kernel
private theorem receipt_3_15_2403_1_part12 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 1536 128 = 3657323515747914223965923744 := by decide +kernel
private theorem receipt_3_15_2403_1_part13 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 1664 128 = 2437739462690984288570276256 := by decide +kernel
private theorem receipt_3_15_2403_1_part14 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 1792 128 = 1283413520721600271070759328 := by decide +kernel
private theorem receipt_3_15_2403_1_part15 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 1920 88 = 247119194168609382164953254 := by decide +kernel
private theorem receipt_3_15_2403_1_join0 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 0 256 = 44124712997763985932953936704 :=
  phaseBlock_append receipt_3_15_2403_1_part0 receipt_3_15_2403_1_part1 rfl rfl rfl
private theorem receipt_3_15_2403_1_join1 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 256 256 = 36636041054123076307461972800 :=
  phaseBlock_append receipt_3_15_2403_1_part2 receipt_3_15_2403_1_part3 rfl rfl rfl
private theorem receipt_3_15_2403_1_join2 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 0 512 = 80760754051887062240415909504 :=
  phaseBlock_append receipt_3_15_2403_1_join0 receipt_3_15_2403_1_join1 rfl rfl rfl
private theorem receipt_3_15_2403_1_join3 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 512 256 = 29586005442382165215760474944 :=
  phaseBlock_append receipt_3_15_2403_1_part4 receipt_3_15_2403_1_part5 rfl rfl rfl
private theorem receipt_3_15_2403_1_join4 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 768 256 = 22990886989836711003072635712 :=
  phaseBlock_append receipt_3_15_2403_1_part6 receipt_3_15_2403_1_part7 rfl rfl rfl
private theorem receipt_3_15_2403_1_join5 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 512 512 = 52576892432218876218833110656 :=
  phaseBlock_append receipt_3_15_2403_1_join3 receipt_3_15_2403_1_join4 rfl rfl rfl
private theorem receipt_3_15_2403_1_join6 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 0 1024 = 133337646484105938459249020160 :=
  phaseBlock_append receipt_3_15_2403_1_join2 receipt_3_15_2403_1_join5 rfl rfl rfl
private theorem receipt_3_15_2403_1_join7 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 1024 256 = 16866780957282387019819017024 :=
  phaseBlock_append receipt_3_15_2403_1_part8 receipt_3_15_2403_1_part9 rfl rfl rfl
private theorem receipt_3_15_2403_1_join8 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 1280 256 = 11229597641616415012159660864 :=
  phaseBlock_append receipt_3_15_2403_1_part10 receipt_3_15_2403_1_part11 rfl rfl rfl
private theorem receipt_3_15_2403_1_join9 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 1024 512 = 28096378598898802031978677888 :=
  phaseBlock_append receipt_3_15_2403_1_join7 receipt_3_15_2403_1_join8 rfl rfl rfl
private theorem receipt_3_15_2403_1_join10 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 1536 256 = 6095062978438898512536200000 :=
  phaseBlock_append receipt_3_15_2403_1_part12 receipt_3_15_2403_1_part13 rfl rfl rfl
private theorem receipt_3_15_2403_1_join11 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 1792 216 = 1530532714890209653235712582 :=
  phaseBlock_append receipt_3_15_2403_1_part14 receipt_3_15_2403_1_part15 rfl rfl rfl
private theorem receipt_3_15_2403_1_join12 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 1536 472 = 7625595693329108165771912582 :=
  phaseBlock_append receipt_3_15_2403_1_join10 receipt_3_15_2403_1_join11 rfl rfl rfl
private theorem receipt_3_15_2403_1_join13 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 1024 984 = 35721974292227910197750590470 :=
  phaseBlock_append receipt_3_15_2403_1_join9 receipt_3_15_2403_1_join12 rfl rfl rfl
private theorem receipt_3_15_2403_1_join14 :
    phaseBlock (fastLayer (bank 3 15).shape 179798 2403 76 1 1 1 1) 0 2008 = 169059620776333848656999610630 :=
  phaseBlock_append receipt_3_15_2403_1_join6 receipt_3_15_2403_1_join13 rfl rfl rfl

private theorem receipt_3_15_2403_1 : fastPhase (bank 3 15).shape 179798 2403 76 1 1 1 1 = 169059620776333848656999610630 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_15_2403_1_join14

theorem receipt_3_15 : Checked (bank 3 15) 76 1 1 := by
  refine checked_from_values (bank 3 15) 76 1 1
    (P3_7_1.checked (bank 3 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9204_2007)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_15_2402_0 receipt_3_15_2402_1 receipt_3_15_2403_0 receipt_3_15_2403_1 (by decide +kernel) (by decide +kernel)

def group6_stage (i : Fin 1) : Fin 17 :=
  ⟨15+i.val, by have := i.isLt; omega⟩

theorem group6_checked (rect : Fin 4) (i : Fin 1) :
    Checked (bank rect (group6_stage i)) (reserve (group6_stage i))
      (excess rect) (seed rect) := by
  fin_cases i
  · fin_cases rect
    · exact receipt_0_15
    · exact receipt_1_15
    · exact receipt_2_15
    · exact receipt_3_15

theorem group6_avoids {h : ℕ} {D : K1_14_1.PoleData h} (Crt : K1_14_1.CRTLift D)
    (word : K1.I → K1_14.L) (lo : 2402 ≤ h) (hi : h ≤ 33619) (rect : Fin 4)
    (i : Fin 1) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group6_stage i)).shape
      (cutoff h rect (group6_stage i)), ¬ G∣Q :=
  (group6_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group6_avoids

end Lower6960.RescueSource
