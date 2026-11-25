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

private theorem receipt_0_15_2383_0_part0 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 0 128 = 221656458106188758879713663680 := by decide +kernel
private theorem receipt_0_15_2383_0_part1 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 128 128 = 202891296300750831810935913152 := by decide +kernel
private theorem receipt_0_15_2383_0_part2 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 256 128 = 184692184995511165379900299968 := by decide +kernel
private theorem receipt_0_15_2383_0_part3 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 384 128 = 167050405810637740962067036864 := by decide +kernel
private theorem receipt_0_15_2383_0_part4 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 512 128 = 149957253359222586620005194432 := by decide +kernel
private theorem receipt_0_15_2383_0_part5 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 640 128 = 133404035240993274279955757760 := by decide +kernel
private theorem receipt_0_15_2383_0_part6 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 768 128 = 117382072036024416908394683072 := by decide +kernel
private theorem receipt_0_15_2383_0_part7 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 896 128 = 101882697298449165688595954368 := by decide +kernel
private theorem receipt_0_15_2383_0_part8 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 1024 128 = 86897257550170707197194640064 := by decide +kernel
private theorem receipt_0_15_2383_0_part9 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 1152 128 = 72417112274573760580749949632 := by decide +kernel
private theorem receipt_0_15_2383_0_part10 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 1280 128 = 58433638522340269387501844132 := by decide +kernel
private theorem receipt_0_15_2383_0_part11 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 1408 128 = 44938241721019761166864338228 := by decide +kernel
private theorem receipt_0_15_2383_0_part12 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 1536 128 = 31922304311443966397774798719 := by decide +kernel
private theorem receipt_0_15_2383_0_part13 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 1664 128 = 19377207816326792115077879289 := by decide +kernel
private theorem receipt_0_15_2383_0_part14 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 1792 128 = 7294346738066067559441659762 := by decide +kernel
private theorem receipt_0_15_2383_0_part15 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 1920 15 = 84904240994931126878659356 := by decide +kernel
private theorem receipt_0_15_2383_0_join0 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 0 256 = 424547754406939590690649576832 :=
  phaseBlock_append receipt_0_15_2383_0_part0 receipt_0_15_2383_0_part1 rfl rfl rfl
private theorem receipt_0_15_2383_0_join1 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 256 256 = 351742590806148906341967336832 :=
  phaseBlock_append receipt_0_15_2383_0_part2 receipt_0_15_2383_0_part3 rfl rfl rfl
private theorem receipt_0_15_2383_0_join2 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 0 512 = 776290345213088497032616913664 :=
  phaseBlock_append receipt_0_15_2383_0_join0 receipt_0_15_2383_0_join1 rfl rfl rfl
private theorem receipt_0_15_2383_0_join3 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 512 256 = 283361288600215860899960952192 :=
  phaseBlock_append receipt_0_15_2383_0_part4 receipt_0_15_2383_0_part5 rfl rfl rfl
private theorem receipt_0_15_2383_0_join4 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 768 256 = 219264769334473582596990637440 :=
  phaseBlock_append receipt_0_15_2383_0_part6 receipt_0_15_2383_0_part7 rfl rfl rfl
private theorem receipt_0_15_2383_0_join5 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 512 512 = 502626057934689443496951589632 :=
  phaseBlock_append receipt_0_15_2383_0_join3 receipt_0_15_2383_0_join4 rfl rfl rfl
private theorem receipt_0_15_2383_0_join6 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 0 1024 = 1278916403147777940529568503296 :=
  phaseBlock_append receipt_0_15_2383_0_join2 receipt_0_15_2383_0_join5 rfl rfl rfl
private theorem receipt_0_15_2383_0_join7 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 1024 256 = 159314369824744467777944589696 :=
  phaseBlock_append receipt_0_15_2383_0_part8 receipt_0_15_2383_0_part9 rfl rfl rfl
private theorem receipt_0_15_2383_0_join8 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 1280 256 = 103371880243360030554366182360 :=
  phaseBlock_append receipt_0_15_2383_0_part10 receipt_0_15_2383_0_part11 rfl rfl rfl
private theorem receipt_0_15_2383_0_join9 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 1024 512 = 262686250068104498332310772056 :=
  phaseBlock_append receipt_0_15_2383_0_join7 receipt_0_15_2383_0_join8 rfl rfl rfl
private theorem receipt_0_15_2383_0_join10 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 1536 256 = 51299512127770758512852678008 :=
  phaseBlock_append receipt_0_15_2383_0_part12 receipt_0_15_2383_0_part13 rfl rfl rfl
private theorem receipt_0_15_2383_0_join11 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 1792 143 = 7379250979060998686320319118 :=
  phaseBlock_append receipt_0_15_2383_0_part14 receipt_0_15_2383_0_part15 rfl rfl rfl
private theorem receipt_0_15_2383_0_join12 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 1536 399 = 58678763106831757199172997126 :=
  phaseBlock_append receipt_0_15_2383_0_join10 receipt_0_15_2383_0_join11 rfl rfl rfl
private theorem receipt_0_15_2383_0_join13 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 1024 911 = 321365013174936255531483769182 :=
  phaseBlock_append receipt_0_15_2383_0_join9 receipt_0_15_2383_0_join12 rfl rfl rfl
private theorem receipt_0_15_2383_0_join14 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 0) 0 1935 = 1600281416322714196061052272478 :=
  phaseBlock_append receipt_0_15_2383_0_join6 receipt_0_15_2383_0_join13 rfl rfl rfl

private theorem receipt_0_15_2383_0 : fastPhase (bank 0 15).shape 179808 2383 76 1 0 1 0 = 1600281416322714196061052272478 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_15_2383_0_join14

private theorem receipt_0_15_2383_1_part0 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 0 128 = 221509607891632258178320464768 := by decide +kernel
private theorem receipt_0_15_2383_1_part1 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 128 128 = 202748752426110449374032329600 := by decide +kernel
private theorem receipt_0_15_2383_1_part2 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 256 128 = 184553881515823105585390058368 := by decide +kernel
private theorem receipt_0_15_2383_1_part3 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 384 128 = 166916276879947241972491910016 := by decide +kernel
private theorem receipt_0_15_2383_1_part4 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 512 128 = 149827233230535774005315271552 := by decide +kernel
private theorem receipt_0_15_2383_1_part5 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 640 128 = 133278058266229014640279714688 := by decide +kernel
private theorem receipt_0_15_2383_1_part6 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 768 128 = 117260072665966171496810052480 := by decide +kernel
private theorem receipt_0_15_2383_1_part7 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 896 128 = 101764610082696844033899395968 := by decide +kernel
private theorem receipt_0_15_2383_1_part8 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 1024 128 = 86783017137092520726672210816 := by decide +kernel
private theorem receipt_0_15_2383_1_part9 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 1152 128 = 72306653411258076242947373952 := by decide +kernel
private theorem receipt_0_15_2383_1_part10 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 1280 128 = 58326896046207146932009397906 := by decide +kernel
private theorem receipt_0_15_2383_1_part11 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 1408 128 = 44835150517464351507411663463 := by decide +kernel
private theorem receipt_0_15_2383_1_part12 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 1536 128 = 31822799346011548307362509555 := by decide +kernel
private theorem receipt_0_15_2383_1_part13 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 1664 128 = 19281224153278461905024702100 := by decide +kernel
private theorem receipt_0_15_2383_1_part14 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 1792 128 = 7201819540352174383652335868 := by decide +kernel
private theorem receipt_0_15_2383_1_part15 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 1920 15 = 74284479209301419018787904 := by decide +kernel
private theorem receipt_0_15_2383_1_join0 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 0 256 = 424258360317742707552352794368 :=
  phaseBlock_append receipt_0_15_2383_1_part0 receipt_0_15_2383_1_part1 rfl rfl rfl
private theorem receipt_0_15_2383_1_join1 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 256 256 = 351470158395770347557881968384 :=
  phaseBlock_append receipt_0_15_2383_1_part2 receipt_0_15_2383_1_part3 rfl rfl rfl
private theorem receipt_0_15_2383_1_join2 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 0 512 = 775728518713513055110234762752 :=
  phaseBlock_append receipt_0_15_2383_1_join0 receipt_0_15_2383_1_join1 rfl rfl rfl
private theorem receipt_0_15_2383_1_join3 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 512 256 = 283105291496764788645594986240 :=
  phaseBlock_append receipt_0_15_2383_1_part4 receipt_0_15_2383_1_part5 rfl rfl rfl
private theorem receipt_0_15_2383_1_join4 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 768 256 = 219024682748663015530709448448 :=
  phaseBlock_append receipt_0_15_2383_1_part6 receipt_0_15_2383_1_part7 rfl rfl rfl
private theorem receipt_0_15_2383_1_join5 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 512 512 = 502129974245427804176304434688 :=
  phaseBlock_append receipt_0_15_2383_1_join3 receipt_0_15_2383_1_join4 rfl rfl rfl
private theorem receipt_0_15_2383_1_join6 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 0 1024 = 1277858492958940859286539197440 :=
  phaseBlock_append receipt_0_15_2383_1_join2 receipt_0_15_2383_1_join5 rfl rfl rfl
private theorem receipt_0_15_2383_1_join7 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 1024 256 = 159089670548350596969619584768 :=
  phaseBlock_append receipt_0_15_2383_1_part8 receipt_0_15_2383_1_part9 rfl rfl rfl
private theorem receipt_0_15_2383_1_join8 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 1280 256 = 103162046563671498439421061369 :=
  phaseBlock_append receipt_0_15_2383_1_part10 receipt_0_15_2383_1_part11 rfl rfl rfl
private theorem receipt_0_15_2383_1_join9 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 1024 512 = 262251717112022095409040646137 :=
  phaseBlock_append receipt_0_15_2383_1_join7 receipt_0_15_2383_1_join8 rfl rfl rfl
private theorem receipt_0_15_2383_1_join10 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 1536 256 = 51104023499290010212387211655 :=
  phaseBlock_append receipt_0_15_2383_1_part12 receipt_0_15_2383_1_part13 rfl rfl rfl
private theorem receipt_0_15_2383_1_join11 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 1792 143 = 7276104019561475802671123772 :=
  phaseBlock_append receipt_0_15_2383_1_part14 receipt_0_15_2383_1_part15 rfl rfl rfl
private theorem receipt_0_15_2383_1_join12 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 1536 399 = 58380127518851486015058335427 :=
  phaseBlock_append receipt_0_15_2383_1_join10 receipt_0_15_2383_1_join11 rfl rfl rfl
private theorem receipt_0_15_2383_1_join13 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 1024 911 = 320631844630873581424098981564 :=
  phaseBlock_append receipt_0_15_2383_1_join9 receipt_0_15_2383_1_join12 rfl rfl rfl
private theorem receipt_0_15_2383_1_join14 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2383 76 1 0 1 1) 0 1935 = 1598490337589814440710638179004 :=
  phaseBlock_append receipt_0_15_2383_1_join6 receipt_0_15_2383_1_join13 rfl rfl rfl

private theorem receipt_0_15_2383_1 : fastPhase (bank 0 15).shape 179808 2383 76 1 0 1 1 = 1598490337589814440710638179004 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_15_2383_1_join14

private theorem receipt_0_15_2384_0_part0 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 0 128 = 221658444755978458083996881664 := by decide +kernel
private theorem receipt_0_15_2384_0_part1 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 128 128 = 202893047254766917204751069952 := by decide +kernel
private theorem receipt_0_15_2384_0_part2 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 256 128 = 184693716174436462051287307008 := by decide +kernel
private theorem receipt_0_15_2384_0_part3 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 384 128 = 167051732834577300356213207808 := by decide +kernel
private theorem receipt_0_15_2384_0_part4 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 512 128 = 149958391548156377775870825216 := by decide +kernel
private theorem receipt_0_15_2384_0_part5 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 640 128 = 133404999615228655164574151424 := by decide +kernel
private theorem receipt_0_15_2384_0_part6 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 768 128 = 117382877316648385848846619392 := by decide +kernel
private theorem receipt_0_15_2384_0_part7 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 896 128 = 101883357907780392901658604288 := by decide +kernel
private theorem receipt_0_15_2384_0_part8 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 1024 128 = 86897787612211346416664924928 := by decide +kernel
private theorem receipt_0_15_2384_0_part9 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 1152 128 = 72417525615461040782442345216 := by decide +kernel
private theorem receipt_0_15_2384_0_part10 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 1280 128 = 58433948502975588799364610219 := by decide +kernel
private theorem receipt_0_15_2384_0_part11 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 1408 128 = 44938461428579222381763907251 := by decide +kernel
private theorem receipt_0_15_2384_0_part12 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 1536 128 = 31922446894166437858521046299 := by decide +kernel
private theorem receipt_0_15_2384_0_part13 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 1664 128 = 19377286104000871584523263594 := by decide +kernel
private theorem receipt_0_15_2384_0_part14 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 1792 128 = 7294373242818109383246202248 := by decide +kernel
private theorem receipt_0_15_2384_0_part15 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 1920 15 = 84904523710966148469202695 := by decide +kernel
private theorem receipt_0_15_2384_0_join0 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 0 256 = 424551492010745375288747951616 :=
  phaseBlock_append receipt_0_15_2384_0_part0 receipt_0_15_2384_0_part1 rfl rfl rfl
private theorem receipt_0_15_2384_0_join1 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 256 256 = 351745449009013762407500514816 :=
  phaseBlock_append receipt_0_15_2384_0_part2 receipt_0_15_2384_0_part3 rfl rfl rfl
private theorem receipt_0_15_2384_0_join2 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 0 512 = 776296941019759137696248466432 :=
  phaseBlock_append receipt_0_15_2384_0_join0 receipt_0_15_2384_0_join1 rfl rfl rfl
private theorem receipt_0_15_2384_0_join3 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 512 256 = 283363391163385032940444976640 :=
  phaseBlock_append receipt_0_15_2384_0_part4 receipt_0_15_2384_0_part5 rfl rfl rfl
private theorem receipt_0_15_2384_0_join4 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 768 256 = 219266235224428778750505223680 :=
  phaseBlock_append receipt_0_15_2384_0_part6 receipt_0_15_2384_0_part7 rfl rfl rfl
private theorem receipt_0_15_2384_0_join5 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 512 512 = 502629626387813811690950200320 :=
  phaseBlock_append receipt_0_15_2384_0_join3 receipt_0_15_2384_0_join4 rfl rfl rfl
private theorem receipt_0_15_2384_0_join6 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 0 1024 = 1278926567407572949387198666752 :=
  phaseBlock_append receipt_0_15_2384_0_join2 receipt_0_15_2384_0_join5 rfl rfl rfl
private theorem receipt_0_15_2384_0_join7 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 1024 256 = 159315313227672387199107270144 :=
  phaseBlock_append receipt_0_15_2384_0_part8 receipt_0_15_2384_0_part9 rfl rfl rfl
private theorem receipt_0_15_2384_0_join8 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 1280 256 = 103372409931554811181128517470 :=
  phaseBlock_append receipt_0_15_2384_0_part10 receipt_0_15_2384_0_part11 rfl rfl rfl
private theorem receipt_0_15_2384_0_join9 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 1024 512 = 262687723159227198380235787614 :=
  phaseBlock_append receipt_0_15_2384_0_join7 receipt_0_15_2384_0_join8 rfl rfl rfl
private theorem receipt_0_15_2384_0_join10 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 1536 256 = 51299732998167309443044309893 :=
  phaseBlock_append receipt_0_15_2384_0_part12 receipt_0_15_2384_0_part13 rfl rfl rfl
private theorem receipt_0_15_2384_0_join11 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 1792 143 = 7379277766529075531715404943 :=
  phaseBlock_append receipt_0_15_2384_0_part14 receipt_0_15_2384_0_part15 rfl rfl rfl
private theorem receipt_0_15_2384_0_join12 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 1536 399 = 58679010764696384974759714836 :=
  phaseBlock_append receipt_0_15_2384_0_join10 receipt_0_15_2384_0_join11 rfl rfl rfl
private theorem receipt_0_15_2384_0_join13 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 1024 911 = 321366733923923583354995502450 :=
  phaseBlock_append receipt_0_15_2384_0_join9 receipt_0_15_2384_0_join12 rfl rfl rfl
private theorem receipt_0_15_2384_0_join14 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 0) 0 1935 = 1600293301331496532742194169202 :=
  phaseBlock_append receipt_0_15_2384_0_join6 receipt_0_15_2384_0_join13 rfl rfl rfl

private theorem receipt_0_15_2384_0 : fastPhase (bank 0 15).shape 179808 2384 76 1 0 1 0 = 1600293301331496532742194169202 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_15_2384_0_join14

private theorem receipt_0_15_2384_1_part0 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 0 128 = 221511593463812532047546710848 := by decide +kernel
private theorem receipt_0_15_2384_1_part1 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 128 128 = 202750502365221278823286053696 := by decide +kernel
private theorem receipt_0_15_2384_1_part2 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 256 128 = 184555411741127952214412737344 := by decide +kernel
private theorem receipt_0_15_2384_1_part3 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 384 128 = 166917603010134272676794686272 := by decide +kernel
private theorem receipt_0_15_2384_1_part4 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 512 128 = 149828370584170550907134475072 := by decide +kernel
private theorem receipt_0_15_2384_1_part5 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 640 128 = 133279021862206965117206829888 := by decide +kernel
private theorem receipt_0_15_2384_1_part6 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 768 128 = 117260877223964838308096129856 := by decide +kernel
private theorem receipt_0_15_2384_1_part7 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 896 128 = 101765270023627915544433908544 := by decide +kernel
private theorem receipt_0_15_2384_1_part8 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 1024 128 = 86783546583553641228636355392 := by decide +kernel
private theorem receipt_0_15_2384_1_part9 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 1152 128 = 72307066187984436375141817152 := by decide +kernel
private theorem receipt_0_15_2384_1_part10 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 1280 128 = 58327205512999152863310159735 := by decide +kernel
private theorem receipt_0_15_2384_1_part11 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 1408 128 = 44835369760559032769457127311 := by decide +kernel
private theorem receipt_0_15_2384_1_part12 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 1536 128 = 31822941512192127204375631545 := by decide +kernel
private theorem receipt_0_15_2384_1_part13 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 1664 128 = 19281302070880810623716822658 := by decide +kernel
private theorem receipt_0_15_2384_1_part14 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 1792 128 = 7201845720042361143559077045 := by decide +kernel
private theorem receipt_0_15_2384_1_part15 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 1920 15 = 74284726708944743204050575 := by decide +kernel
private theorem receipt_0_15_2384_1_join0 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 0 256 = 424262095829033810870832764544 :=
  phaseBlock_append receipt_0_15_2384_1_part0 receipt_0_15_2384_1_part1 rfl rfl rfl
private theorem receipt_0_15_2384_1_join1 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 256 256 = 351473014751262224891207423616 :=
  phaseBlock_append receipt_0_15_2384_1_part2 receipt_0_15_2384_1_part3 rfl rfl rfl
private theorem receipt_0_15_2384_1_join2 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 0 512 = 775735110580296035762040188160 :=
  phaseBlock_append receipt_0_15_2384_1_join0 receipt_0_15_2384_1_join1 rfl rfl rfl
private theorem receipt_0_15_2384_1_join3 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 512 256 = 283107392446377516024341304960 :=
  phaseBlock_append receipt_0_15_2384_1_part4 receipt_0_15_2384_1_part5 rfl rfl rfl
private theorem receipt_0_15_2384_1_join4 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 768 256 = 219026147247592753852530038400 :=
  phaseBlock_append receipt_0_15_2384_1_part6 receipt_0_15_2384_1_part7 rfl rfl rfl
private theorem receipt_0_15_2384_1_join5 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 512 512 = 502133539693970269876871343360 :=
  phaseBlock_append receipt_0_15_2384_1_join3 receipt_0_15_2384_1_join4 rfl rfl rfl
private theorem receipt_0_15_2384_1_join6 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 0 1024 = 1277868650274266305638911531520 :=
  phaseBlock_append receipt_0_15_2384_1_join2 receipt_0_15_2384_1_join5 rfl rfl rfl
private theorem receipt_0_15_2384_1_join7 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 1024 256 = 159090612771538077603778172544 :=
  phaseBlock_append receipt_0_15_2384_1_part8 receipt_0_15_2384_1_part9 rfl rfl rfl
private theorem receipt_0_15_2384_1_join8 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 1280 256 = 103162575273558185632767287046 :=
  phaseBlock_append receipt_0_15_2384_1_part10 receipt_0_15_2384_1_part11 rfl rfl rfl
private theorem receipt_0_15_2384_1_join9 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 1024 512 = 262253188045096263236545459590 :=
  phaseBlock_append receipt_0_15_2384_1_join7 receipt_0_15_2384_1_join8 rfl rfl rfl
private theorem receipt_0_15_2384_1_join10 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 1536 256 = 51104243583072937828092454203 :=
  phaseBlock_append receipt_0_15_2384_1_part12 receipt_0_15_2384_1_part13 rfl rfl rfl
private theorem receipt_0_15_2384_1_join11 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 1792 143 = 7276130446751305886763127620 :=
  phaseBlock_append receipt_0_15_2384_1_part14 receipt_0_15_2384_1_part15 rfl rfl rfl
private theorem receipt_0_15_2384_1_join12 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 1536 399 = 58380374029824243714855581823 :=
  phaseBlock_append receipt_0_15_2384_1_join10 receipt_0_15_2384_1_join11 rfl rfl rfl
private theorem receipt_0_15_2384_1_join13 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 1024 911 = 320633562074920506951401041413 :=
  phaseBlock_append receipt_0_15_2384_1_join9 receipt_0_15_2384_1_join12 rfl rfl rfl
private theorem receipt_0_15_2384_1_join14 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2384 76 1 0 1 1) 0 1935 = 1598502212349186812590312572933 :=
  phaseBlock_append receipt_0_15_2384_1_join6 receipt_0_15_2384_1_join13 rfl rfl rfl

private theorem receipt_0_15_2384_1 : fastPhase (bank 0 15).shape 179808 2384 76 1 0 1 1 = 1598502212349186812590312572933 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_15_2384_1_join14

theorem receipt_0_15 : Checked (bank 0 15) 76 0 1 := by
  refine checked_from_values (bank 0 15) 76 0 1
    (P3_7_1.checked (bank 0 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9204_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_15_2383_0 receipt_0_15_2383_1 receipt_0_15_2384_0 receipt_0_15_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_15_2383_0_part0 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 0 128 = 199556109565283647027548549760 := by decide +kernel
private theorem receipt_1_15_2383_0_part1 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 128 128 = 182582078495304604165744996992 := by decide +kernel
private theorem receipt_1_15_2383_0_part2 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 256 128 = 166131977902327412257715057280 := by decide +kernel
private theorem receipt_1_15_2383_0_part3 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 384 128 = 150197303995274176157012734592 := by decide +kernel
private theorem receipt_1_15_2383_0_part4 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 512 128 = 134769578163166803780904252032 := by decide +kernel
private theorem receipt_1_15_2383_0_part5 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 640 128 = 119840346949972994816620278400 := by decide +kernel
private theorem receipt_1_15_2383_0_part6 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 768 128 = 105401182029452229427608154752 := by decide +kernel
private theorem receipt_1_15_2383_0_part7 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 896 128 = 91443680180001756959784120960 := by decide +kernel
private theorem receipt_1_15_2383_0_part8 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 1024 128 = 77959463259502584647785542272 := by decide +kernel
private theorem receipt_1_15_2383_0_part9 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 1152 128 = 64940178180165466321223135872 := by decide +kernel
private theorem receipt_1_15_2383_0_part10 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 1280 128 = 52377501016931324919621055705 := by decide +kernel
private theorem receipt_1_15_2383_0_part11 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 1408 128 = 40263146665023402326851453115 := by decide +kernel
private theorem receipt_1_15_2383_0_part12 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 1536 128 = 28588822790958328496682515931 := by decide +kernel
private theorem receipt_1_15_2383_0_part13 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 1664 128 = 17346249636743982286088303822 := by decide +kernel
private theorem receipt_1_15_2383_0_part14 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 1792 128 = 6527172464321956937962925340 := by decide +kernel
private theorem receipt_1_15_2383_0_part15 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 1920 15 = 75951891151498768013033859 := by decide +kernel
private theorem receipt_1_15_2383_0_join0 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 0 256 = 382138188060588251193293546752 :=
  phaseBlock_append receipt_1_15_2383_0_part0 receipt_1_15_2383_0_part1 rfl rfl rfl
private theorem receipt_1_15_2383_0_join1 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 256 256 = 316329281897601588414727791872 :=
  phaseBlock_append receipt_1_15_2383_0_part2 receipt_1_15_2383_0_part3 rfl rfl rfl
private theorem receipt_1_15_2383_0_join2 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 0 512 = 698467469958189839608021338624 :=
  phaseBlock_append receipt_1_15_2383_0_join0 receipt_1_15_2383_0_join1 rfl rfl rfl
private theorem receipt_1_15_2383_0_join3 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 512 256 = 254609925113139798597524530432 :=
  phaseBlock_append receipt_1_15_2383_0_part4 receipt_1_15_2383_0_part5 rfl rfl rfl
private theorem receipt_1_15_2383_0_join4 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 768 256 = 196844862209453986387392275712 :=
  phaseBlock_append receipt_1_15_2383_0_part6 receipt_1_15_2383_0_part7 rfl rfl rfl
private theorem receipt_1_15_2383_0_join5 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 512 512 = 451454787322593784984916806144 :=
  phaseBlock_append receipt_1_15_2383_0_join3 receipt_1_15_2383_0_join4 rfl rfl rfl
private theorem receipt_1_15_2383_0_join6 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 0 1024 = 1149922257280783624592938144768 :=
  phaseBlock_append receipt_1_15_2383_0_join2 receipt_1_15_2383_0_join5 rfl rfl rfl
private theorem receipt_1_15_2383_0_join7 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 1024 256 = 142899641439668050969008678144 :=
  phaseBlock_append receipt_1_15_2383_0_part8 receipt_1_15_2383_0_part9 rfl rfl rfl
private theorem receipt_1_15_2383_0_join8 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 1280 256 = 92640647681954727246472508820 :=
  phaseBlock_append receipt_1_15_2383_0_part10 receipt_1_15_2383_0_part11 rfl rfl rfl
private theorem receipt_1_15_2383_0_join9 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 1024 512 = 235540289121622778215481186964 :=
  phaseBlock_append receipt_1_15_2383_0_join7 receipt_1_15_2383_0_join8 rfl rfl rfl
private theorem receipt_1_15_2383_0_join10 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 1536 256 = 45935072427702310782770819753 :=
  phaseBlock_append receipt_1_15_2383_0_part12 receipt_1_15_2383_0_part13 rfl rfl rfl
private theorem receipt_1_15_2383_0_join11 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 1792 143 = 6603124355473455705975959199 :=
  phaseBlock_append receipt_1_15_2383_0_part14 receipt_1_15_2383_0_part15 rfl rfl rfl
private theorem receipt_1_15_2383_0_join12 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 1536 399 = 52538196783175766488746778952 :=
  phaseBlock_append receipt_1_15_2383_0_join10 receipt_1_15_2383_0_join11 rfl rfl rfl
private theorem receipt_1_15_2383_0_join13 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 1024 911 = 288078485904798544704227965916 :=
  phaseBlock_append receipt_1_15_2383_0_join9 receipt_1_15_2383_0_join12 rfl rfl rfl
private theorem receipt_1_15_2383_0_join14 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 0) 0 1935 = 1438000743185582169297166110684 :=
  phaseBlock_append receipt_1_15_2383_0_join6 receipt_1_15_2383_0_join13 rfl rfl rfl

private theorem receipt_1_15_2383_0 : fastPhase (bank 1 15).shape 179808 2383 76 1 0 2 0 = 1438000743185582169297166110684 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_15_2383_0_join14

private theorem receipt_1_15_2383_1_part0 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 0 128 = 199423220014094211089126344256 := by decide +kernel
private theorem receipt_1_15_2383_1_part1 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 128 128 = 182453179636743445782763071040 := by decide +kernel
private theorem receipt_1_15_2383_1_part2 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 256 128 = 166007005315560948338217354816 := by decide +kernel
private theorem receipt_1_15_2383_1_part3 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 384 128 = 150076193451428199282195441216 := by decide +kernel
private theorem receipt_1_15_2383_1_part4 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 512 128 = 134652265625133896696196875840 := by decide +kernel
private theorem receipt_1_15_2383_1_part5 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 640 128 = 119726768572219944922766730816 := by decide +kernel
private theorem receipt_1_15_2383_1_part6 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 768 128 = 105291274157827443271747831360 := by decide +kernel
private theorem receipt_1_15_2383_1_part7 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 896 128 = 91337379351542674726532982336 := by decide +kernel
private theorem receipt_1_15_2383_1_part8 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 1024 128 = 77856706202243094650317194816 := by decide +kernel
private theorem receipt_1_15_2383_1_part9 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 1152 128 = 64840901812943319492349912640 := by decide +kernel
private theorem receipt_1_15_2383_1_part10 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 1280 128 = 52281642441706453360229510482 := by decide +kernel
private theorem receipt_1_15_2383_1_part11 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 1408 128 = 40170643128744248989603395555 := by decide +kernel
private theorem receipt_1_15_2383_1_part12 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 1536 128 = 28499611714415396836572362801 := by decide +kernel
private theorem receipt_1_15_2383_1_part13 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 1664 128 = 17260268631113155700191974279 := by decide +kernel
private theorem receipt_1_15_2383_1_part14 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 1792 128 = 6444359330990863467584335966 := by decide +kernel
private theorem receipt_1_15_2383_1_part15 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 1920 15 = 66451730105066645027697015 := by decide +kernel
private theorem receipt_1_15_2383_1_join0 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 0 256 = 381876399650837656871889415296 :=
  phaseBlock_append receipt_1_15_2383_1_part0 receipt_1_15_2383_1_part1 rfl rfl rfl
private theorem receipt_1_15_2383_1_join1 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 256 256 = 316083198766989147620412796032 :=
  phaseBlock_append receipt_1_15_2383_1_part2 receipt_1_15_2383_1_part3 rfl rfl rfl
private theorem receipt_1_15_2383_1_join2 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 0 512 = 697959598417826804492302211328 :=
  phaseBlock_append receipt_1_15_2383_1_join0 receipt_1_15_2383_1_join1 rfl rfl rfl
private theorem receipt_1_15_2383_1_join3 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 512 256 = 254379034197353841618963606656 :=
  phaseBlock_append receipt_1_15_2383_1_part4 receipt_1_15_2383_1_part5 rfl rfl rfl
private theorem receipt_1_15_2383_1_join4 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 768 256 = 196628653509370117998280813696 :=
  phaseBlock_append receipt_1_15_2383_1_part6 receipt_1_15_2383_1_part7 rfl rfl rfl
private theorem receipt_1_15_2383_1_join5 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 512 512 = 451007687706723959617244420352 :=
  phaseBlock_append receipt_1_15_2383_1_join3 receipt_1_15_2383_1_join4 rfl rfl rfl
private theorem receipt_1_15_2383_1_join6 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 0 1024 = 1148967286124550764109546631680 :=
  phaseBlock_append receipt_1_15_2383_1_join2 receipt_1_15_2383_1_join5 rfl rfl rfl
private theorem receipt_1_15_2383_1_join7 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 1024 256 = 142697608015186414142667107456 :=
  phaseBlock_append receipt_1_15_2383_1_part8 receipt_1_15_2383_1_part9 rfl rfl rfl
private theorem receipt_1_15_2383_1_join8 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 1280 256 = 92452285570450702349832906037 :=
  phaseBlock_append receipt_1_15_2383_1_part10 receipt_1_15_2383_1_part11 rfl rfl rfl
private theorem receipt_1_15_2383_1_join9 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 1024 512 = 235149893585637116492500013493 :=
  phaseBlock_append receipt_1_15_2383_1_join7 receipt_1_15_2383_1_join8 rfl rfl rfl
private theorem receipt_1_15_2383_1_join10 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 1536 256 = 45759880345528552536764337080 :=
  phaseBlock_append receipt_1_15_2383_1_part12 receipt_1_15_2383_1_part13 rfl rfl rfl
private theorem receipt_1_15_2383_1_join11 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 1792 143 = 6510811061095930112612032981 :=
  phaseBlock_append receipt_1_15_2383_1_part14 receipt_1_15_2383_1_part15 rfl rfl rfl
private theorem receipt_1_15_2383_1_join12 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 1536 399 = 52270691406624482649376370061 :=
  phaseBlock_append receipt_1_15_2383_1_join10 receipt_1_15_2383_1_join11 rfl rfl rfl
private theorem receipt_1_15_2383_1_join13 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 1024 911 = 287420584992261599141876383554 :=
  phaseBlock_append receipt_1_15_2383_1_join9 receipt_1_15_2383_1_join12 rfl rfl rfl
private theorem receipt_1_15_2383_1_join14 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2383 76 1 0 2 1) 0 1935 = 1436387871116812363251423015234 :=
  phaseBlock_append receipt_1_15_2383_1_join6 receipt_1_15_2383_1_join13 rfl rfl rfl

private theorem receipt_1_15_2383_1 : fastPhase (bank 1 15).shape 179808 2383 76 1 0 2 1 = 1436387871116812363251423015234 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_15_2383_1_join14

private theorem receipt_1_15_2384_0_part0 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 0 128 = 199557898137732140363880880544 := by decide +kernel
private theorem receipt_1_15_2384_0_part1 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 128 128 = 182583654182795653717038082464 := by decide +kernel
private theorem receipt_1_15_2384_0_part2 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 256 128 = 166133355211104315211756075424 := by decide +kernel
private theorem receipt_1_15_2384_0_part3 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 384 128 = 150198497142562981561884592544 := by decide +kernel
private theorem receipt_1_15_2384_0_part4 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 512 128 = 134770601078050203562108230048 := by decide +kernel
private theorem receipt_1_15_2384_0_part5 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 640 128 = 119841213274263335184896453024 := by decide +kernel
private theorem receipt_1_15_2384_0_part6 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 768 128 = 105401905118563642677453601184 := by decide +kernel
private theorem receipt_1_15_2384_0_part7 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 896 128 = 91444273103821413658668894624 := by decide +kernel
private theorem receipt_1_15_2384_0_part8 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 1024 128 = 77959938803261066216066439584 := by decide +kernel
private theorem receipt_1_15_2384_0_part9 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 1152 128 = 64940548845306258002755234208 := by decide +kernel
private theorem receipt_1_15_2384_0_part10 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 1280 128 = 52377778871565404654851401431 := by decide +kernel
private theorem receipt_1_15_2384_0_part11 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 1408 128 = 40263343516195043607080445957 := by decide +kernel
private theorem receipt_1_15_2384_0_part12 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 1536 128 = 28588950484949042231753634366 := by decide +kernel
private theorem receipt_1_15_2384_0_part13 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 1664 128 = 17346319719224207755532684759 := by decide +kernel
private theorem receipt_1_15_2384_0_part14 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 1792 128 = 6527196181552155440937233638 := by decide +kernel
private theorem receipt_1_15_2384_0_part15 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 1920 15 = 75952144057811863415769947 := by decide +kernel
private theorem receipt_1_15_2384_0_join0 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 0 256 = 382141552320527794080918963008 :=
  phaseBlock_append receipt_1_15_2384_0_part0 receipt_1_15_2384_0_part1 rfl rfl rfl
private theorem receipt_1_15_2384_0_join1 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 256 256 = 316331852353667296773640667968 :=
  phaseBlock_append receipt_1_15_2384_0_part2 receipt_1_15_2384_0_part3 rfl rfl rfl
private theorem receipt_1_15_2384_0_join2 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 0 512 = 698473404674195090854559630976 :=
  phaseBlock_append receipt_1_15_2384_0_join0 receipt_1_15_2384_0_join1 rfl rfl rfl
private theorem receipt_1_15_2384_0_join3 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 512 256 = 254611814352313538747004683072 :=
  phaseBlock_append receipt_1_15_2384_0_part4 receipt_1_15_2384_0_part5 rfl rfl rfl
private theorem receipt_1_15_2384_0_join4 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 768 256 = 196846178222385056336122495808 :=
  phaseBlock_append receipt_1_15_2384_0_part6 receipt_1_15_2384_0_part7 rfl rfl rfl
private theorem receipt_1_15_2384_0_join5 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 512 512 = 451457992574698595083127178880 :=
  phaseBlock_append receipt_1_15_2384_0_join3 receipt_1_15_2384_0_join4 rfl rfl rfl
private theorem receipt_1_15_2384_0_join6 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 0 1024 = 1149931397248893685937686809856 :=
  phaseBlock_append receipt_1_15_2384_0_join2 receipt_1_15_2384_0_join5 rfl rfl rfl
private theorem receipt_1_15_2384_0_join7 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 1024 256 = 142900487648567324218821673792 :=
  phaseBlock_append receipt_1_15_2384_0_part8 receipt_1_15_2384_0_part9 rfl rfl rfl
private theorem receipt_1_15_2384_0_join8 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 1280 256 = 92641122387760448261931847388 :=
  phaseBlock_append receipt_1_15_2384_0_part10 receipt_1_15_2384_0_part11 rfl rfl rfl
private theorem receipt_1_15_2384_0_join9 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 1024 512 = 235541610036327772480753521180 :=
  phaseBlock_append receipt_1_15_2384_0_join7 receipt_1_15_2384_0_join8 rfl rfl rfl
private theorem receipt_1_15_2384_0_join10 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 1536 256 = 45935270204173249987286319125 :=
  phaseBlock_append receipt_1_15_2384_0_part12 receipt_1_15_2384_0_part13 rfl rfl rfl
private theorem receipt_1_15_2384_0_join11 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 1792 143 = 6603148325609967304353003585 :=
  phaseBlock_append receipt_1_15_2384_0_part14 receipt_1_15_2384_0_part15 rfl rfl rfl
private theorem receipt_1_15_2384_0_join12 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 1536 399 = 52538418529783217291639322710 :=
  phaseBlock_append receipt_1_15_2384_0_join10 receipt_1_15_2384_0_join11 rfl rfl rfl
private theorem receipt_1_15_2384_0_join13 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 1024 911 = 288080028566110989772392843890 :=
  phaseBlock_append receipt_1_15_2384_0_join9 receipt_1_15_2384_0_join12 rfl rfl rfl
private theorem receipt_1_15_2384_0_join14 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 0) 0 1935 = 1438011425815004675710079653746 :=
  phaseBlock_append receipt_1_15_2384_0_join6 receipt_1_15_2384_0_join13 rfl rfl rfl

private theorem receipt_1_15_2384_0 : fastPhase (bank 1 15).shape 179808 2384 76 1 0 2 0 = 1438011425815004675710079653746 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_15_2384_0_join14

private theorem receipt_1_15_2384_1_part0 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 0 128 = 199425007610270058807260606752 := by decide +kernel
private theorem receipt_1_15_2384_1_part1 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 128 128 = 182454754405537445075049103648 := by decide +kernel
private theorem receipt_1_15_2384_1_part2 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 256 128 = 166008381761841627380039258400 := by decide +kernel
private theorem receipt_1_15_2384_1_part3 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 384 128 = 150077385791051630334420803872 := by decide +kernel
private theorem receipt_1_15_2384_1_part4 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 512 128 = 134653287785817581899619184928 := by decide +kernel
private theorem receipt_1_15_2384_1_part5 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 640 128 = 119727634194415822483245564192 := by decide +kernel
private theorem receipt_1_15_2384_1_part6 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 768 128 = 105291996595594014036046827808 := by decide +kernel
private theorem receipt_1_15_2384_1_part7 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 896 128 = 91337971673416249148855591200 := by decide +kernel
private theorem receipt_1_15_2384_1_part8 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 1024 128 = 77857181192108160149540204832 := by decide +kernel
private theorem receipt_1_15_2384_1_part9 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 1152 128 = 64841271970902028199954759968 := by decide +kernel
private theorem receipt_1_15_2384_1_part10 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 1280 128 = 52281919834801326020716248506 := by decide +kernel
private theorem receipt_1_15_2384_1_part11 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 1408 128 = 40170839563098339260299542452 := by decide +kernel
private theorem receipt_1_15_2384_1_part12 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 1536 128 = 28499739034927241642346402925 := by decide +kernel
private theorem receipt_1_15_2384_1_part13 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 1664 128 = 17260338382075505703055427776 := by decide +kernel
private theorem receipt_1_15_2384_1_part14 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 1792 128 = 6444382757282394719330107917 := by decide +kernel
private theorem receipt_1_15_2384_1_part15 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 1920 15 = 66451951507711791160320254 := by decide +kernel
private theorem receipt_1_15_2384_1_join0 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 0 256 = 381879762015807503882309710400 :=
  phaseBlock_append receipt_1_15_2384_1_part0 receipt_1_15_2384_1_part1 rfl rfl rfl
private theorem receipt_1_15_2384_1_join1 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 256 256 = 316085767552893257714460062272 :=
  phaseBlock_append receipt_1_15_2384_1_part2 receipt_1_15_2384_1_part3 rfl rfl rfl
private theorem receipt_1_15_2384_1_join2 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 0 512 = 697965529568700761596769772672 :=
  phaseBlock_append receipt_1_15_2384_1_join0 receipt_1_15_2384_1_join1 rfl rfl rfl
private theorem receipt_1_15_2384_1_join3 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 512 256 = 254380921980233404382864749120 :=
  phaseBlock_append receipt_1_15_2384_1_part4 receipt_1_15_2384_1_part5 rfl rfl rfl
private theorem receipt_1_15_2384_1_join4 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 768 256 = 196629968269010263184902419008 :=
  phaseBlock_append receipt_1_15_2384_1_part6 receipt_1_15_2384_1_part7 rfl rfl rfl
private theorem receipt_1_15_2384_1_join5 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 512 512 = 451010890249243667567767168128 :=
  phaseBlock_append receipt_1_15_2384_1_join3 receipt_1_15_2384_1_join4 rfl rfl rfl
private theorem receipt_1_15_2384_1_join6 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 0 1024 = 1148976419817944429164536940800 :=
  phaseBlock_append receipt_1_15_2384_1_join2 receipt_1_15_2384_1_join5 rfl rfl rfl
private theorem receipt_1_15_2384_1_join7 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 1024 256 = 142698453163010188349494964800 :=
  phaseBlock_append receipt_1_15_2384_1_part8 receipt_1_15_2384_1_part9 rfl rfl rfl
private theorem receipt_1_15_2384_1_join8 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 1280 256 = 92452759397899665281015790958 :=
  phaseBlock_append receipt_1_15_2384_1_part10 receipt_1_15_2384_1_part11 rfl rfl rfl
private theorem receipt_1_15_2384_1_join9 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 1024 512 = 235151212560909853630510755758 :=
  phaseBlock_append receipt_1_15_2384_1_join7 receipt_1_15_2384_1_join8 rfl rfl rfl
private theorem receipt_1_15_2384_1_join10 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 1536 256 = 45760077417002747345401830701 :=
  phaseBlock_append receipt_1_15_2384_1_part12 receipt_1_15_2384_1_part13 rfl rfl rfl
private theorem receipt_1_15_2384_1_join11 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 1792 143 = 6510834708790106510490428171 :=
  phaseBlock_append receipt_1_15_2384_1_part14 receipt_1_15_2384_1_part15 rfl rfl rfl
private theorem receipt_1_15_2384_1_join12 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 1536 399 = 52270912125792853855892258872 :=
  phaseBlock_append receipt_1_15_2384_1_join10 receipt_1_15_2384_1_join11 rfl rfl rfl
private theorem receipt_1_15_2384_1_join13 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 1024 911 = 287422124686702707486403014630 :=
  phaseBlock_append receipt_1_15_2384_1_join9 receipt_1_15_2384_1_join12 rfl rfl rfl
private theorem receipt_1_15_2384_1_join14 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2384 76 1 0 2 1) 0 1935 = 1436398544504647136650939955430 :=
  phaseBlock_append receipt_1_15_2384_1_join6 receipt_1_15_2384_1_join13 rfl rfl rfl

private theorem receipt_1_15_2384_1 : fastPhase (bank 1 15).shape 179808 2384 76 1 0 2 1 = 1436398544504647136650939955430 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_15_2384_1_join14

theorem receipt_1_15 : Checked (bank 1 15) 76 0 2 := by
  refine checked_from_values (bank 1 15) 76 0 2
    (P3_7_1.checked (bank 1 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9204_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_15_2383_0 receipt_1_15_2383_1 receipt_1_15_2384_0 receipt_1_15_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_15_2383_0_part0 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 0 128 = 107041553390899959260428614720 := by decide +kernel
private theorem receipt_2_15_2383_0_part1 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 128 128 = 97629006904855853090874874944 := by decide +kernel
private theorem receipt_2_15_2383_0_part2 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 256 128 = 88553169089249826327012637760 := by decide +kernel
private theorem receipt_2_15_2383_0_part3 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 384 128 = 79806812402864064412615285824 := by decide +kernel
private theorem receipt_2_15_2383_0_part4 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 512 128 = 71382783502884768176652303424 := by decide +kernel
private theorem receipt_2_15_2383_0_part5 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 640 128 = 63274002936765515484879051840 := by decide +kernel
private theorem receipt_2_15_2383_0_part6 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 768 128 = 55473464834090622891426544704 := by decide +kernel
private theorem receipt_2_15_2383_0_part7 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 896 128 = 47974236598438507290391223360 := by decide +kernel
private theorem receipt_2_15_2383_0_part8 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 1024 128 = 40769458599245047567424732224 := by decide +kernel
private theorem receipt_2_15_2383_0_part9 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 1152 128 = 33852343863666946251323694144 := by decide +kernel
private theorem receipt_2_15_2383_0_part10 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 1280 128 = 27216179914231149992535455553 := by decide +kernel
private theorem receipt_2_15_2383_0_part11 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 1408 128 = 20854333445695712223977953433 := by decide +kernel
private theorem receipt_2_15_2383_0_part12 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 1536 128 = 14760226143133398182331172796 := by decide +kernel
private theorem receipt_2_15_2383_0_part13 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 1664 128 = 8927344838077606977481482261 := by decide +kernel
private theorem receipt_2_15_2383_0_part14 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 1792 128 = 3349247703889640015984648638 := by decide +kernel
private theorem receipt_2_15_2383_0_part15 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 1920 15 = 38887085202729153884959157 := by decide +kernel
private theorem receipt_2_15_2383_0_join0 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 0 256 = 204670560295755812351303489664 :=
  phaseBlock_append receipt_2_15_2383_0_part0 receipt_2_15_2383_0_part1 rfl rfl rfl
private theorem receipt_2_15_2383_0_join1 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 256 256 = 168359981492113890739627923584 :=
  phaseBlock_append receipt_2_15_2383_0_part2 receipt_2_15_2383_0_part3 rfl rfl rfl
private theorem receipt_2_15_2383_0_join2 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 0 512 = 373030541787869703090931413248 :=
  phaseBlock_append receipt_2_15_2383_0_join0 receipt_2_15_2383_0_join1 rfl rfl rfl
private theorem receipt_2_15_2383_0_join3 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 512 256 = 134656786439650283661531355264 :=
  phaseBlock_append receipt_2_15_2383_0_part4 receipt_2_15_2383_0_part5 rfl rfl rfl
private theorem receipt_2_15_2383_0_join4 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 768 256 = 103447701432529130181817768064 :=
  phaseBlock_append receipt_2_15_2383_0_part6 receipt_2_15_2383_0_part7 rfl rfl rfl
private theorem receipt_2_15_2383_0_join5 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 512 512 = 238104487872179413843349123328 :=
  phaseBlock_append receipt_2_15_2383_0_join3 receipt_2_15_2383_0_join4 rfl rfl rfl
private theorem receipt_2_15_2383_0_join6 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 0 1024 = 611135029660049116934280536576 :=
  phaseBlock_append receipt_2_15_2383_0_join2 receipt_2_15_2383_0_join5 rfl rfl rfl
private theorem receipt_2_15_2383_0_join7 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 1024 256 = 74621802462911993818748426368 :=
  phaseBlock_append receipt_2_15_2383_0_part8 receipt_2_15_2383_0_part9 rfl rfl rfl
private theorem receipt_2_15_2383_0_join8 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 1280 256 = 48070513359926862216513408986 :=
  phaseBlock_append receipt_2_15_2383_0_part10 receipt_2_15_2383_0_part11 rfl rfl rfl
private theorem receipt_2_15_2383_0_join9 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 1024 512 = 122692315822838856035261835354 :=
  phaseBlock_append receipt_2_15_2383_0_join7 receipt_2_15_2383_0_join8 rfl rfl rfl
private theorem receipt_2_15_2383_0_join10 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 1536 256 = 23687570981211005159812655057 :=
  phaseBlock_append receipt_2_15_2383_0_part12 receipt_2_15_2383_0_part13 rfl rfl rfl
private theorem receipt_2_15_2383_0_join11 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 1792 143 = 3388134789092369169869607795 :=
  phaseBlock_append receipt_2_15_2383_0_part14 receipt_2_15_2383_0_part15 rfl rfl rfl
private theorem receipt_2_15_2383_0_join12 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 1536 399 = 27075705770303374329682262852 :=
  phaseBlock_append receipt_2_15_2383_0_join10 receipt_2_15_2383_0_join11 rfl rfl rfl
private theorem receipt_2_15_2383_0_join13 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 1024 911 = 149768021593142230364944098206 :=
  phaseBlock_append receipt_2_15_2383_0_join9 receipt_2_15_2383_0_join12 rfl rfl rfl
private theorem receipt_2_15_2383_0_join14 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 0) 0 1935 = 760903051253191347299224634782 :=
  phaseBlock_append receipt_2_15_2383_0_join6 receipt_2_15_2383_0_join13 rfl rfl rfl

private theorem receipt_2_15_2383_0 : fastPhase (bank 2 15).shape 179808 2383 76 1 0 7 0 = 760903051253191347299224634782 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_15_2383_0_join14

private theorem receipt_2_15_2383_1_part0 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 0 128 = 106967644936118421849036344128 := by decide +kernel
private theorem receipt_2_15_2383_1_part1 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 128 128 = 97557681731060255495041231680 := by decide +kernel
private theorem receipt_2_15_2383_1_part2 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 256 128 = 88484372027892645422246169408 := by decide +kernel
private theorem receipt_2_15_2383_1_part3 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 384 128 = 79740488852513121704686545728 := by decide +kernel
private theorem receipt_2_15_2383_1_part4 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 512 128 = 71318879426864057317337090880 := by decide +kernel
private theorem receipt_2_15_2383_1_part5 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 640 128 = 63212464860796029787701652288 := by decide +kernel
private theorem receipt_2_15_2383_1_part6 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 768 128 = 55414239843931182847402969920 := by decide +kernel
private theorem receipt_2_15_2383_1_part7 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 896 128 = 47917272337526588083772451648 := by decide +kernel
private theorem receipt_2_15_2383_1_part8 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 1024 128 = 40714703266337606591439948608 := by decide +kernel
private theorem receipt_2_15_2383_1_part9 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 1152 128 = 33799746210481250623923530560 := by decide +kernel
private theorem receipt_2_15_2383_1_part10 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 1280 128 = 27165689239144039227447730318 := by decide +kernel
private theorem receipt_2_15_2383_1_part11 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 1408 128 = 20805899571603502259696057930 := by decide +kernel
private theorem receipt_2_15_2383_1_part12 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 1536 128 = 14713799430803425960200615870 := by decide +kernel
private theorem receipt_2_15_2383_1_part13 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 1664 128 = 8882876192676750540017219681 := by decide +kernel
private theorem receipt_2_15_2383_1_part14 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 1792 128 = 3306688572629659422509795862 := by decide +kernel
private theorem receipt_2_15_2383_1_part15 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 1920 15 = 34022460639767644882425189 := by decide +kernel
private theorem receipt_2_15_2383_1_join0 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 0 256 = 204525326667178677344077575808 :=
  phaseBlock_append receipt_2_15_2383_1_part0 receipt_2_15_2383_1_part1 rfl rfl rfl
private theorem receipt_2_15_2383_1_join1 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 256 256 = 168224860880405767126932715136 :=
  phaseBlock_append receipt_2_15_2383_1_part2 receipt_2_15_2383_1_part3 rfl rfl rfl
private theorem receipt_2_15_2383_1_join2 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 0 512 = 372750187547584444471010290944 :=
  phaseBlock_append receipt_2_15_2383_1_join0 receipt_2_15_2383_1_join1 rfl rfl rfl
private theorem receipt_2_15_2383_1_join3 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 512 256 = 134531344287660087105038743168 :=
  phaseBlock_append receipt_2_15_2383_1_part4 receipt_2_15_2383_1_part5 rfl rfl rfl
private theorem receipt_2_15_2383_1_join4 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 768 256 = 103331512181457770931175421568 :=
  phaseBlock_append receipt_2_15_2383_1_part6 receipt_2_15_2383_1_part7 rfl rfl rfl
private theorem receipt_2_15_2383_1_join5 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 512 512 = 237862856469117858036214164736 :=
  phaseBlock_append receipt_2_15_2383_1_join3 receipt_2_15_2383_1_join4 rfl rfl rfl
private theorem receipt_2_15_2383_1_join6 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 0 1024 = 610613044016702302507224455680 :=
  phaseBlock_append receipt_2_15_2383_1_join2 receipt_2_15_2383_1_join5 rfl rfl rfl
private theorem receipt_2_15_2383_1_join7 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 1024 256 = 74514449476818857215363479168 :=
  phaseBlock_append receipt_2_15_2383_1_part8 receipt_2_15_2383_1_part9 rfl rfl rfl
private theorem receipt_2_15_2383_1_join8 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 1280 256 = 47971588810747541487143788248 :=
  phaseBlock_append receipt_2_15_2383_1_part10 receipt_2_15_2383_1_part11 rfl rfl rfl
private theorem receipt_2_15_2383_1_join9 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 1024 512 = 122486038287566398702507267416 :=
  phaseBlock_append receipt_2_15_2383_1_join7 receipt_2_15_2383_1_join8 rfl rfl rfl
private theorem receipt_2_15_2383_1_join10 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 1536 256 = 23596675623480176500217835551 :=
  phaseBlock_append receipt_2_15_2383_1_part12 receipt_2_15_2383_1_part13 rfl rfl rfl
private theorem receipt_2_15_2383_1_join11 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 1792 143 = 3340711033269427067392221051 :=
  phaseBlock_append receipt_2_15_2383_1_part14 receipt_2_15_2383_1_part15 rfl rfl rfl
private theorem receipt_2_15_2383_1_join12 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 1536 399 = 26937386656749603567610056602 :=
  phaseBlock_append receipt_2_15_2383_1_join10 receipt_2_15_2383_1_join11 rfl rfl rfl
private theorem receipt_2_15_2383_1_join13 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 1024 911 = 149423424944316002270117324018 :=
  phaseBlock_append receipt_2_15_2383_1_join9 receipt_2_15_2383_1_join12 rfl rfl rfl
private theorem receipt_2_15_2383_1_join14 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2383 76 1 0 7 1) 0 1935 = 760036468961018304777341779698 :=
  phaseBlock_append receipt_2_15_2383_1_join6 receipt_2_15_2383_1_join13 rfl rfl rfl

private theorem receipt_2_15_2383_1 : fastPhase (bank 2 15).shape 179808 2383 76 1 0 7 1 = 760036468961018304777341779698 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_15_2383_1_join14

private theorem receipt_2_15_2384_0_part0 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 0 128 = 107042512787317224995114536992 := by decide +kernel
private theorem receipt_2_15_2384_0_part1 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 128 128 = 97629849454024823528027815968 := by decide +kernel
private theorem receipt_2_15_2384_0_part2 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 256 128 = 88553903242825690379808256032 := by decide +kernel
private theorem receipt_2_15_2384_0_part3 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 384 128 = 79807446384879194833538768928 := by decide +kernel
private theorem receipt_2_15_2384_0_part4 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 512 128 = 71383325312262137140672073760 := by decide +kernel
private theorem receipt_2_15_2384_0_part5 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 640 128 = 63274460349821334958668267552 := by decide +kernel
private theorem receipt_2_15_2384_0_part6 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 768 128 = 55473845407026209788632395808 := by decide +kernel
private theorem receipt_2_15_2384_0_part7 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 896 128 = 47974547669821373412952023072 := by decide +kernel
private theorem receipt_2_15_2384_0_part8 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 1024 128 = 40769707292479214332934803488 := by decide +kernel
private theorem receipt_2_15_2384_0_part9 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 1152 128 = 33852537089452484206446051360 := by decide +kernel
private theorem receipt_2_15_2384_0_part10 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 1280 128 = 27216324294912249786698938172 := by decide +kernel
private theorem receipt_2_15_2384_0_part11 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 1408 128 = 20854435407292923686259872590 := by decide +kernel
private theorem receipt_2_15_2384_0_part12 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 1536 128 = 14760292072415883521144097537 := by decide +kernel
private theorem receipt_2_15_2384_0_part13 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 1664 128 = 8927380907445318179856547959 := by decide +kernel
private theorem receipt_2_15_2384_0_part14 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 1792 128 = 3349259874083465845430238906 := by decide +kernel
private theorem receipt_2_15_2384_0_part15 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 1920 15 = 38887214689865083092107676 := by decide +kernel
private theorem receipt_2_15_2384_0_join0 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 0 256 = 204672362241342048523142352960 :=
  phaseBlock_append receipt_2_15_2384_0_part0 receipt_2_15_2384_0_part1 rfl rfl rfl
private theorem receipt_2_15_2384_0_join1 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 256 256 = 168361349627704885213347024960 :=
  phaseBlock_append receipt_2_15_2384_0_part2 receipt_2_15_2384_0_part3 rfl rfl rfl
private theorem receipt_2_15_2384_0_join2 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 0 512 = 373033711869046933736489377920 :=
  phaseBlock_append receipt_2_15_2384_0_join0 receipt_2_15_2384_0_join1 rfl rfl rfl
private theorem receipt_2_15_2384_0_join3 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 512 256 = 134657785662083472099340341312 :=
  phaseBlock_append receipt_2_15_2384_0_part4 receipt_2_15_2384_0_part5 rfl rfl rfl
private theorem receipt_2_15_2384_0_join4 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 768 256 = 103448393076847583201584418880 :=
  phaseBlock_append receipt_2_15_2384_0_part6 receipt_2_15_2384_0_part7 rfl rfl rfl
private theorem receipt_2_15_2384_0_join5 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 512 512 = 238106178738931055300924760192 :=
  phaseBlock_append receipt_2_15_2384_0_join3 receipt_2_15_2384_0_join4 rfl rfl rfl
private theorem receipt_2_15_2384_0_join6 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 0 1024 = 611139890607977989037414138112 :=
  phaseBlock_append receipt_2_15_2384_0_join2 receipt_2_15_2384_0_join5 rfl rfl rfl
private theorem receipt_2_15_2384_0_join7 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 1024 256 = 74622244381931698539380854848 :=
  phaseBlock_append receipt_2_15_2384_0_part8 receipt_2_15_2384_0_part9 rfl rfl rfl
private theorem receipt_2_15_2384_0_join8 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 1280 256 = 48070759702205173472958810762 :=
  phaseBlock_append receipt_2_15_2384_0_part10 receipt_2_15_2384_0_part11 rfl rfl rfl
private theorem receipt_2_15_2384_0_join9 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 1024 512 = 122693004084136872012339665610 :=
  phaseBlock_append receipt_2_15_2384_0_join7 receipt_2_15_2384_0_join8 rfl rfl rfl
private theorem receipt_2_15_2384_0_join10 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 1536 256 = 23687672979861201701000645496 :=
  phaseBlock_append receipt_2_15_2384_0_part12 receipt_2_15_2384_0_part13 rfl rfl rfl
private theorem receipt_2_15_2384_0_join11 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 1792 143 = 3388147088773330928522346582 :=
  phaseBlock_append receipt_2_15_2384_0_part14 receipt_2_15_2384_0_part15 rfl rfl rfl
private theorem receipt_2_15_2384_0_join12 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 1536 399 = 27075820068634532629522992078 :=
  phaseBlock_append receipt_2_15_2384_0_join10 receipt_2_15_2384_0_join11 rfl rfl rfl
private theorem receipt_2_15_2384_0_join13 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 1024 911 = 149768824152771404641862657688 :=
  phaseBlock_append receipt_2_15_2384_0_join9 receipt_2_15_2384_0_join12 rfl rfl rfl
private theorem receipt_2_15_2384_0_join14 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 0) 0 1935 = 760908714760749393679276795800 :=
  phaseBlock_append receipt_2_15_2384_0_join6 receipt_2_15_2384_0_join13 rfl rfl rfl

private theorem receipt_2_15_2384_0 : fastPhase (bank 2 15).shape 179808 2384 76 1 0 7 0 = 760908714760749393679276795800 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_15_2384_0_join14

private theorem receipt_2_15_2384_1_part0 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 0 128 = 106968603785313387240894446816 := by decide +kernel
private theorem receipt_2_15_2384_1_part1 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 128 128 = 97558523768258596331725008096 := by decide +kernel
private theorem receipt_2_15_2384_1_part2 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 256 128 = 88485105703626599776180313312 := by decide +kernel
private theorem receipt_2_15_2384_1_part3 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 384 128 = 79741122389706017616752151776 := by decide +kernel
private theorem receipt_2_15_2384_1_part4 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 512 128 = 71319420823343664402212519136 := by decide +kernel
private theorem receipt_2_15_2384_1_part5 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 640 128 = 63212921891797135625251187936 := by decide +kernel
private theorem receipt_2_15_2384_1_part6 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 768 128 = 55414620064587394160113278176 := by decide +kernel
private theorem receipt_2_15_2384_1_part7 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 896 128 = 47917583085351356700236827872 := by decide +kernel
private theorem receipt_2_15_2384_1_part8 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 1024 128 = 40714951663694480195890363616 := by decide +kernel
private theorem receipt_2_15_2384_1_part9 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 1152 128 = 33799939167043348291810471136 := by decide +kernel
private theorem receipt_2_15_2384_1_part10 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 1280 128 = 27165833376383235923404746969 := by decide +kernel
private theorem receipt_2_15_2384_1_part11 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 1408 128 = 20806001314753792176377324567 := by decide +kernel
private theorem receipt_2_15_2384_1_part12 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 1536 128 = 14713865165613588734263733124 := by decide +kernel
private theorem receipt_2_15_2384_1_part13 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 1664 128 = 8882912090540446775363012354 := by decide +kernel
private theorem receipt_2_15_2384_1_part14 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 1792 128 = 3306700593290702643792606934 := by decide +kernel
private theorem receipt_2_15_2384_1_part15 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 1920 15 = 34022573995207818918092909 := by decide +kernel
private theorem receipt_2_15_2384_1_join0 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 0 256 = 204527127553571983572619454912 :=
  phaseBlock_append receipt_2_15_2384_1_part0 receipt_2_15_2384_1_part1 rfl rfl rfl
private theorem receipt_2_15_2384_1_join1 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 256 256 = 168226228093332617392932465088 :=
  phaseBlock_append receipt_2_15_2384_1_part2 receipt_2_15_2384_1_part3 rfl rfl rfl
private theorem receipt_2_15_2384_1_join2 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 0 512 = 372753355646904600965551920000 :=
  phaseBlock_append receipt_2_15_2384_1_join0 receipt_2_15_2384_1_join1 rfl rfl rfl
private theorem receipt_2_15_2384_1_join3 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 512 256 = 134532342715140800027463707072 :=
  phaseBlock_append receipt_2_15_2384_1_part4 receipt_2_15_2384_1_part5 rfl rfl rfl
private theorem receipt_2_15_2384_1_join4 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 768 256 = 103332203149938750860350106048 :=
  phaseBlock_append receipt_2_15_2384_1_part6 receipt_2_15_2384_1_part7 rfl rfl rfl
private theorem receipt_2_15_2384_1_join5 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 512 512 = 237864545865079550887813813120 :=
  phaseBlock_append receipt_2_15_2384_1_join3 receipt_2_15_2384_1_join4 rfl rfl rfl
private theorem receipt_2_15_2384_1_join6 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 0 1024 = 610617901511984151853365733120 :=
  phaseBlock_append receipt_2_15_2384_1_join2 receipt_2_15_2384_1_join5 rfl rfl rfl
private theorem receipt_2_15_2384_1_join7 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 1024 256 = 74514890830737828487700834752 :=
  phaseBlock_append receipt_2_15_2384_1_part8 receipt_2_15_2384_1_part9 rfl rfl rfl
private theorem receipt_2_15_2384_1_join8 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 1280 256 = 47971834691137028099782071536 :=
  phaseBlock_append receipt_2_15_2384_1_part10 receipt_2_15_2384_1_part11 rfl rfl rfl
private theorem receipt_2_15_2384_1_join9 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 1024 512 = 122486725521874856587482906288 :=
  phaseBlock_append receipt_2_15_2384_1_join7 receipt_2_15_2384_1_join8 rfl rfl rfl
private theorem receipt_2_15_2384_1_join10 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 1536 256 = 23596777256154035509626745478 :=
  phaseBlock_append receipt_2_15_2384_1_part12 receipt_2_15_2384_1_part13 rfl rfl rfl
private theorem receipt_2_15_2384_1_join11 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 1792 143 = 3340723167285910462710699843 :=
  phaseBlock_append receipt_2_15_2384_1_part14 receipt_2_15_2384_1_part15 rfl rfl rfl
private theorem receipt_2_15_2384_1_join12 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 1536 399 = 26937500423439945972337445321 :=
  phaseBlock_append receipt_2_15_2384_1_join10 receipt_2_15_2384_1_join11 rfl rfl rfl
private theorem receipt_2_15_2384_1_join13 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 1024 911 = 149424225945314802559820351609 :=
  phaseBlock_append receipt_2_15_2384_1_join9 receipt_2_15_2384_1_join12 rfl rfl rfl
private theorem receipt_2_15_2384_1_join14 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2384 76 1 0 7 1) 0 1935 = 760042127457298954413186084729 :=
  phaseBlock_append receipt_2_15_2384_1_join6 receipt_2_15_2384_1_join13 rfl rfl rfl

private theorem receipt_2_15_2384_1 : fastPhase (bank 2 15).shape 179808 2384 76 1 0 7 1 = 760042127457298954413186084729 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_15_2384_1_join14

theorem receipt_2_15 : Checked (bank 2 15) 76 0 7 := by
  refine checked_from_values (bank 2 15) 76 0 7
    (P3_7_1.checked (bank 2 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9204_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_15_2383_0 receipt_2_15_2383_1 receipt_2_15_2384_0 receipt_2_15_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_15_2383_0_part0 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 0 128 = 22543325140001741523216050784 := by decide +kernel
private theorem receipt_3_15_2383_0_part1 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 128 128 = 20658702510474038133017746016 := by decide +kernel
private theorem receipt_3_15_2383_0_part2 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 256 128 = 18826219299437006801871374944 := by decide +kernel
private theorem receipt_3_15_2383_0_part3 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 384 128 = 17046882904626253892129585760 := by decide +kernel
private theorem receipt_3_15_2383_0_part4 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 512 128 = 15321694955376885200512412256 := by decide +kernel
private theorem receipt_3_15_2383_0_part5 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 640 128 = 13651651322056743978378910304 := by decide +kernel
private theorem receipt_3_15_2383_0_part6 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 768 128 = 12037742125499648951998794336 := by decide +kernel
private theorem receipt_3_15_2383_0_part7 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 896 128 = 10480951746438632342824073824 := by decide +kernel
private theorem receipt_3_15_2383_0_part8 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 1024 128 = 8982258834939177887760689760 := by decide +kernel
private theorem receipt_3_15_2383_0_part9 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 1152 128 = 7542636319832458859440151136 := by decide +kernel
private theorem receipt_3_15_2383_0_part10 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 1280 128 = 6163051418148576086491171424 := by decide +kernel
private theorem receipt_3_15_2383_0_part11 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 1408 128 = 4844465644549795973811305056 := by decide +kernel
private theorem receipt_3_15_2383_0_part12 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 1536 128 = 3587834820763788522838583904 := by decide +kernel
private theorem receipt_3_15_2383_0_part13 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 1664 128 = 2394109085016865351823153760 := by decide +kernel
private theorem receipt_3_15_2383_0_part14 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 1792 128 = 1264232901467217716098910816 := by decide +kernel
private theorem receipt_3_15_2383_0_part15 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 1920 88 = 247373199892359320916005914 := by decide +kernel
private theorem receipt_3_15_2383_0_join0 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 0 256 = 43202027650475779656233796800 :=
  phaseBlock_append receipt_3_15_2383_0_part0 receipt_3_15_2383_0_part1 rfl rfl rfl
private theorem receipt_3_15_2383_0_join1 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 256 256 = 35873102204063260694000960704 :=
  phaseBlock_append receipt_3_15_2383_0_part2 receipt_3_15_2383_0_part3 rfl rfl rfl
private theorem receipt_3_15_2383_0_join2 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 0 512 = 79075129854539040350234757504 :=
  phaseBlock_append receipt_3_15_2383_0_join0 receipt_3_15_2383_0_join1 rfl rfl rfl
private theorem receipt_3_15_2383_0_join3 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 512 256 = 28973346277433629178891322560 :=
  phaseBlock_append receipt_3_15_2383_0_part4 receipt_3_15_2383_0_part5 rfl rfl rfl
private theorem receipt_3_15_2383_0_join4 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 768 256 = 22518693871938281294822868160 :=
  phaseBlock_append receipt_3_15_2383_0_part6 receipt_3_15_2383_0_part7 rfl rfl rfl
private theorem receipt_3_15_2383_0_join5 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 512 512 = 51492040149371910473714190720 :=
  phaseBlock_append receipt_3_15_2383_0_join3 receipt_3_15_2383_0_join4 rfl rfl rfl
private theorem receipt_3_15_2383_0_join6 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 0 1024 = 130567170003910950823948948224 :=
  phaseBlock_append receipt_3_15_2383_0_join2 receipt_3_15_2383_0_join5 rfl rfl rfl
private theorem receipt_3_15_2383_0_join7 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 1024 256 = 16524895154771636747200840896 :=
  phaseBlock_append receipt_3_15_2383_0_part8 receipt_3_15_2383_0_part9 rfl rfl rfl
private theorem receipt_3_15_2383_0_join8 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 1280 256 = 11007517062698372060302476480 :=
  phaseBlock_append receipt_3_15_2383_0_part10 receipt_3_15_2383_0_part11 rfl rfl rfl
private theorem receipt_3_15_2383_0_join9 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 1024 512 = 27532412217470008807503317376 :=
  phaseBlock_append receipt_3_15_2383_0_join7 receipt_3_15_2383_0_join8 rfl rfl rfl
private theorem receipt_3_15_2383_0_join10 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 1536 256 = 5981943905780653874661737664 :=
  phaseBlock_append receipt_3_15_2383_0_part12 receipt_3_15_2383_0_part13 rfl rfl rfl
private theorem receipt_3_15_2383_0_join11 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 1792 216 = 1511606101359577037014916730 :=
  phaseBlock_append receipt_3_15_2383_0_part14 receipt_3_15_2383_0_part15 rfl rfl rfl
private theorem receipt_3_15_2383_0_join12 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 1536 472 = 7493550007140230911676654394 :=
  phaseBlock_append receipt_3_15_2383_0_join10 receipt_3_15_2383_0_join11 rfl rfl rfl
private theorem receipt_3_15_2383_0_join13 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 1024 984 = 35025962224610239719179971770 :=
  phaseBlock_append receipt_3_15_2383_0_join9 receipt_3_15_2383_0_join12 rfl rfl rfl
private theorem receipt_3_15_2383_0_join14 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 0) 0 2008 = 165593132228521190543128919994 :=
  phaseBlock_append receipt_3_15_2383_0_join6 receipt_3_15_2383_0_join13 rfl rfl rfl

private theorem receipt_3_15_2383_0 : fastPhase (bank 3 15).shape 179808 2383 76 1 1 1 0 = 165593132228521190543128919994 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_15_2383_0_join14

private theorem receipt_3_15_2383_1_part0 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 0 128 = 22528601573116776466938880224 := by decide +kernel
private theorem receipt_3_15_2383_1_part1 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 128 128 = 20644364581403220671541858528 := by decide +kernel
private theorem receipt_3_15_2383_1_part2 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 256 128 = 18812275566026279719148273888 := by decide +kernel
private theorem receipt_3_15_2383_1_part3 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 384 128 = 17033341877235256220417110240 := by decide +kernel
private theorem receipt_3_15_2383_1_part4 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 512 128 = 15308565096955597045643223264 := by decide +kernel
private theorem receipt_3_15_2383_1_part5 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 640 128 = 13638941048222131345028976864 := by decide +kernel
private theorem receipt_3_15_2383_1_part6 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 768 128 = 12025459804612308568955879648 := by decide +kernel
private theorem receipt_3_15_2383_1_part7 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 896 128 = 10469105699679436488256221408 := by decide +kernel
private theorem receipt_3_15_2383_1_part8 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 1024 128 = 8970857336385919214484709600 := by decide +kernel
private theorem receipt_3_15_2383_1_part9 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 1152 128 = 7531687596536495220190105824 := by decide +kernel
private theorem receipt_3_15_2383_1_part10 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 1280 128 = 6152563650211475359186862304 := by decide +kernel
private theorem receipt_3_15_2383_1_part11 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 1408 128 = 4834446965199980886826758368 := by decide +kernel
private theorem receipt_3_15_2383_1_part12 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 1536 128 = 3578293316433181480270536928 := by decide +kernel
private theorem receipt_3_15_2383_1_part13 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 1664 128 = 2385052795417533258759540960 := by decide +kernel
private theorem receipt_3_15_2383_1_part14 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 1792 128 = 1255669819668016803887349984 := by decide +kernel
private theorem receipt_3_15_2383_1_part15 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 1920 88 = 241776311525854924798316370 := by decide +kernel
private theorem receipt_3_15_2383_1_join0 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 0 256 = 43172966154519997138480738752 :=
  phaseBlock_append receipt_3_15_2383_1_part0 receipt_3_15_2383_1_part1 rfl rfl rfl
private theorem receipt_3_15_2383_1_join1 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 256 256 = 35845617443261535939565384128 :=
  phaseBlock_append receipt_3_15_2383_1_part2 receipt_3_15_2383_1_part3 rfl rfl rfl
private theorem receipt_3_15_2383_1_join2 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 0 512 = 79018583597781533078046122880 :=
  phaseBlock_append receipt_3_15_2383_1_join0 receipt_3_15_2383_1_join1 rfl rfl rfl
private theorem receipt_3_15_2383_1_join3 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 512 256 = 28947506145177728390672200128 :=
  phaseBlock_append receipt_3_15_2383_1_part4 receipt_3_15_2383_1_part5 rfl rfl rfl
private theorem receipt_3_15_2383_1_join4 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 768 256 = 22494565504291745057212101056 :=
  phaseBlock_append receipt_3_15_2383_1_part6 receipt_3_15_2383_1_part7 rfl rfl rfl
private theorem receipt_3_15_2383_1_join5 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 512 512 = 51442071649469473447884301184 :=
  phaseBlock_append receipt_3_15_2383_1_join3 receipt_3_15_2383_1_join4 rfl rfl rfl
private theorem receipt_3_15_2383_1_join6 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 0 1024 = 130460655247251006525930424064 :=
  phaseBlock_append receipt_3_15_2383_1_join2 receipt_3_15_2383_1_join5 rfl rfl rfl
private theorem receipt_3_15_2383_1_join7 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 1024 256 = 16502544932922414434674815424 :=
  phaseBlock_append receipt_3_15_2383_1_part8 receipt_3_15_2383_1_part9 rfl rfl rfl
private theorem receipt_3_15_2383_1_join8 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 1280 256 = 10987010615411456246013620672 :=
  phaseBlock_append receipt_3_15_2383_1_part10 receipt_3_15_2383_1_part11 rfl rfl rfl
private theorem receipt_3_15_2383_1_join9 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 1024 512 = 27489555548333870680688436096 :=
  phaseBlock_append receipt_3_15_2383_1_join7 receipt_3_15_2383_1_join8 rfl rfl rfl
private theorem receipt_3_15_2383_1_join10 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 1536 256 = 5963346111850714739030077888 :=
  phaseBlock_append receipt_3_15_2383_1_part12 receipt_3_15_2383_1_part13 rfl rfl rfl
private theorem receipt_3_15_2383_1_join11 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 1792 216 = 1497446131193871728685666354 :=
  phaseBlock_append receipt_3_15_2383_1_part14 receipt_3_15_2383_1_part15 rfl rfl rfl
private theorem receipt_3_15_2383_1_join12 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 1536 472 = 7460792243044586467715744242 :=
  phaseBlock_append receipt_3_15_2383_1_join10 receipt_3_15_2383_1_join11 rfl rfl rfl
private theorem receipt_3_15_2383_1_join13 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 1024 984 = 34950347791378457148404180338 :=
  phaseBlock_append receipt_3_15_2383_1_join9 receipt_3_15_2383_1_join12 rfl rfl rfl
private theorem receipt_3_15_2383_1_join14 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2383 76 1 1 1 1) 0 2008 = 165411003038629463674334604402 :=
  phaseBlock_append receipt_3_15_2383_1_join6 receipt_3_15_2383_1_join13 rfl rfl rfl

private theorem receipt_3_15_2383_1 : fastPhase (bank 3 15).shape 179808 2383 76 1 1 1 1 = 165411003038629463674334604402 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_15_2383_1_join14

private theorem receipt_3_15_2384_0_part0 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 0 128 = 22543525875941897963970590880 := by decide +kernel
private theorem receipt_3_15_2384_0_part1 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 128 128 = 20658874456603751702671018144 := by decide +kernel
private theorem receipt_3_15_2384_0_part2 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 256 128 = 18826365176154774424717301920 := by decide +kernel
private theorem receipt_3_15_2384_0_part3 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 384 128 = 17047005311231798484900767904 := by decide +kernel
private theorem receipt_3_15_2384_0_part4 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 512 128 = 15321796370642612547265542304 := by decide +kernel
private theorem receipt_3_15_2384_0_part5 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 640 128 = 13651734104798319996077967520 := by decide +kernel
private theorem receipt_3_15_2384_0_part6 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 768 128 = 12037808515145697346796017824 := by decide +kernel
private theorem receipt_3_15_2384_0_part7 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 896 128 = 10481003863599552657038715040 := by decide +kernel
private theorem receipt_3_15_2384_0_part8 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 1024 128 = 8982298681975083937555544224 := by decide +kernel
private theorem receipt_3_15_2384_0_part9 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 1152 128 = 7542665781420237563195869344 := by decide +kernel
private theorem receipt_3_15_2384_0_part10 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 1280 128 = 6163072261848066683878348960 := by decide +kernel
private theorem receipt_3_15_2384_0_part11 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 1408 128 = 4844479521369089635560351904 := by decide +kernel
private theorem receipt_3_15_2384_0_part12 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 1536 128 = 3587843265723648351207372960 := by decide +kernel
private theorem receipt_3_15_2384_0_part13 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 1664 128 = 2394113517714266771762448544 := by decide +kernel
private theorem receipt_3_15_2384_0_part14 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 1792 128 = 1264234626638009257115572384 := by decide +kernel
private theorem receipt_3_15_2384_0_part15 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 1920 88 = 247373438608116066385095638 := by decide +kernel
private theorem receipt_3_15_2384_0_join0 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 0 256 = 43202400332545649666641609024 :=
  phaseBlock_append receipt_3_15_2384_0_part0 receipt_3_15_2384_0_part1 rfl rfl rfl
private theorem receipt_3_15_2384_0_join1 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 256 256 = 35873370487386572909618069824 :=
  phaseBlock_append receipt_3_15_2384_0_part2 receipt_3_15_2384_0_part3 rfl rfl rfl
private theorem receipt_3_15_2384_0_join2 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 0 512 = 79075770819932222576259678848 :=
  phaseBlock_append receipt_3_15_2384_0_join0 receipt_3_15_2384_0_join1 rfl rfl rfl
private theorem receipt_3_15_2384_0_join3 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 512 256 = 28973530475440932543343509824 :=
  phaseBlock_append receipt_3_15_2384_0_part4 receipt_3_15_2384_0_part5 rfl rfl rfl
private theorem receipt_3_15_2384_0_join4 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 768 256 = 22518812378745250003834732864 :=
  phaseBlock_append receipt_3_15_2384_0_part6 receipt_3_15_2384_0_part7 rfl rfl rfl
private theorem receipt_3_15_2384_0_join5 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 512 512 = 51492342854186182547178242688 :=
  phaseBlock_append receipt_3_15_2384_0_join3 receipt_3_15_2384_0_join4 rfl rfl rfl
private theorem receipt_3_15_2384_0_join6 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 0 1024 = 130568113674118405123437921536 :=
  phaseBlock_append receipt_3_15_2384_0_join2 receipt_3_15_2384_0_join5 rfl rfl rfl
private theorem receipt_3_15_2384_0_join7 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 1024 256 = 16524964463395321500751413568 :=
  phaseBlock_append receipt_3_15_2384_0_part8 receipt_3_15_2384_0_part9 rfl rfl rfl
private theorem receipt_3_15_2384_0_join8 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 1280 256 = 11007551783217156319438700864 :=
  phaseBlock_append receipt_3_15_2384_0_part10 receipt_3_15_2384_0_part11 rfl rfl rfl
private theorem receipt_3_15_2384_0_join9 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 1024 512 = 27532516246612477820190114432 :=
  phaseBlock_append receipt_3_15_2384_0_join7 receipt_3_15_2384_0_join8 rfl rfl rfl
private theorem receipt_3_15_2384_0_join10 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 1536 256 = 5981956783437915122969821504 :=
  phaseBlock_append receipt_3_15_2384_0_part12 receipt_3_15_2384_0_part13 rfl rfl rfl
private theorem receipt_3_15_2384_0_join11 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 1792 216 = 1511608065246125323500668022 :=
  phaseBlock_append receipt_3_15_2384_0_part14 receipt_3_15_2384_0_part15 rfl rfl rfl
private theorem receipt_3_15_2384_0_join12 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 1536 472 = 7493564848684040446470489526 :=
  phaseBlock_append receipt_3_15_2384_0_join10 receipt_3_15_2384_0_join11 rfl rfl rfl
private theorem receipt_3_15_2384_0_join13 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 1024 984 = 35026081095296518266660603958 :=
  phaseBlock_append receipt_3_15_2384_0_join9 receipt_3_15_2384_0_join12 rfl rfl rfl
private theorem receipt_3_15_2384_0_join14 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 0) 0 2008 = 165594194769414923390098525494 :=
  phaseBlock_append receipt_3_15_2384_0_join6 receipt_3_15_2384_0_join13 rfl rfl rfl

private theorem receipt_3_15_2384_0 : fastPhase (bank 3 15).shape 179808 2384 76 1 1 1 0 = 165594194769414923390098525494 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_15_2384_0_join14

private theorem receipt_3_15_2384_1_part0 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 0 128 = 22528802157007440663960612000 := by decide +kernel
private theorem receipt_3_15_2384_1_part1 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 128 128 = 20644536389745299351723015328 := by decide +kernel
private theorem receipt_3_15_2384_1_part2 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 256 128 = 18812421318549099936776391840 := by decide +kernel
private theorem receipt_3_15_2384_1_part3 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 384 128 = 17033464172572838470649289888 := by decide +kernel
private theorem receipt_3_15_2384_1_part4 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 512 128 = 15308666413218106504394452128 := by decide +kernel
private theorem receipt_3_15_2384_1_part5 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 640 128 = 13639023743566449499558231200 := by decide +kernel
private theorem receipt_3_15_2384_1_part6 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 768 128 = 12025526117811725239150005408 := by decide +kernel
private theorem receipt_3_15_2384_1_part7 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 896 128 = 10469157750692462238611594400 := by decide +kernel
private theorem receipt_3_15_2384_1_part8 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 1024 128 = 8970897126924218156786674848 := by decide +kernel
private theorem receipt_3_15_2384_1_part9 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 1152 128 = 7531717010631938206890196128 := by decide +kernel
private theorem receipt_3_15_2384_1_part10 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 1280 128 = 6152584454782313567477796000 := by decide +kernel
private theorem receipt_3_15_2384_1_part11 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 1408 128 = 4834460810616139793415216288 := by decide +kernel
private theorem receipt_3_15_2384_1_part12 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 1536 128 = 3578301737080675226847718560 := by decide +kernel
private theorem receipt_3_15_2384_1_part13 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 1664 128 = 2385057210261999408169499808 := by decide +kernel
private theorem receipt_3_15_2384_1_part14 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 1792 128 = 1255671532817371486993108128 := by decide +kernel
private theorem receipt_3_15_2384_1_part15 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 1920 88 = 241776545034920214617470326 := by decide +kernel
private theorem receipt_3_15_2384_1_join0 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 0 256 = 43173338546752740015683627328 :=
  phaseBlock_append receipt_3_15_2384_1_part0 receipt_3_15_2384_1_part1 rfl rfl rfl
private theorem receipt_3_15_2384_1_join1 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 256 256 = 35845885491121938407425681728 :=
  phaseBlock_append receipt_3_15_2384_1_part2 receipt_3_15_2384_1_part3 rfl rfl rfl
private theorem receipt_3_15_2384_1_join2 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 0 512 = 79019224037874678423109309056 :=
  phaseBlock_append receipt_3_15_2384_1_join0 receipt_3_15_2384_1_join1 rfl rfl rfl
private theorem receipt_3_15_2384_1_join3 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 512 256 = 28947690156784556003952683328 :=
  phaseBlock_append receipt_3_15_2384_1_part4 receipt_3_15_2384_1_part5 rfl rfl rfl
private theorem receipt_3_15_2384_1_join4 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 768 256 = 22494683868504187477761599808 :=
  phaseBlock_append receipt_3_15_2384_1_part6 receipt_3_15_2384_1_part7 rfl rfl rfl
private theorem receipt_3_15_2384_1_join5 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 512 512 = 51442374025288743481714283136 :=
  phaseBlock_append receipt_3_15_2384_1_join3 receipt_3_15_2384_1_join4 rfl rfl rfl
private theorem receipt_3_15_2384_1_join6 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 0 1024 = 130461598063163421904823592192 :=
  phaseBlock_append receipt_3_15_2384_1_join2 receipt_3_15_2384_1_join5 rfl rfl rfl
private theorem receipt_3_15_2384_1_join7 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 1024 256 = 16502614137556156363676870976 :=
  phaseBlock_append receipt_3_15_2384_1_part8 receipt_3_15_2384_1_part9 rfl rfl rfl
private theorem receipt_3_15_2384_1_join8 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 1280 256 = 10987045265398453360893012288 :=
  phaseBlock_append receipt_3_15_2384_1_part10 receipt_3_15_2384_1_part11 rfl rfl rfl
private theorem receipt_3_15_2384_1_join9 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 1024 512 = 27489659402954609724569883264 :=
  phaseBlock_append receipt_3_15_2384_1_join7 receipt_3_15_2384_1_join8 rfl rfl rfl
private theorem receipt_3_15_2384_1_join10 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 1536 256 = 5963358947342674635017218368 :=
  phaseBlock_append receipt_3_15_2384_1_part12 receipt_3_15_2384_1_part13 rfl rfl rfl
private theorem receipt_3_15_2384_1_join11 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 1792 216 = 1497448077852291701610578454 :=
  phaseBlock_append receipt_3_15_2384_1_part14 receipt_3_15_2384_1_part15 rfl rfl rfl
private theorem receipt_3_15_2384_1_join12 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 1536 472 = 7460807025194966336627796822 :=
  phaseBlock_append receipt_3_15_2384_1_join10 receipt_3_15_2384_1_join11 rfl rfl rfl
private theorem receipt_3_15_2384_1_join13 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 1024 984 = 34950466428149576061197680086 :=
  phaseBlock_append receipt_3_15_2384_1_join9 receipt_3_15_2384_1_join12 rfl rfl rfl
private theorem receipt_3_15_2384_1_join14 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2384 76 1 1 1 1) 0 2008 = 165412064491312997966021272278 :=
  phaseBlock_append receipt_3_15_2384_1_join6 receipt_3_15_2384_1_join13 rfl rfl rfl

private theorem receipt_3_15_2384_1 : fastPhase (bank 3 15).shape 179808 2384 76 1 1 1 1 = 165412064491312997966021272278 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_15_2384_1_join14

theorem receipt_3_15 : Checked (bank 3 15) 76 1 1 := by
  refine checked_from_values (bank 3 15) 76 1 1
    (P3_7_1.checked (bank 3 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9204_2007)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_15_2383_0 receipt_3_15_2383_1 receipt_3_15_2384_0 receipt_3_15_2384_1 (by decide +kernel) (by decide +kernel)

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
    (word : K1.I → K1_14.L) (lo : 2383 ≤ h) (hi : h ≤ 33599) (rect : Fin 4)
    (i : Fin 1) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group6_stage i)).shape
      (cutoff h rect (group6_stage i)), ¬ G∣Q :=
  (group6_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group6_avoids

end Lower6960.RescueSource
