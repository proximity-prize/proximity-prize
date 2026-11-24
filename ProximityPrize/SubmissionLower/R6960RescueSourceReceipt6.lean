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

private theorem receipt_0_15_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 0 128 = 239962925155163692620682190784 := by decide +kernel
private theorem receipt_0_15_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 128 128 = 219651626628181679980770574272 := by decide +kernel
private theorem receipt_0_15_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 256 128 = 199952477167687024155999936448 := by decide +kernel
private theorem receipt_0_15_2359_0_part3 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 384 128 = 180856066769663970795937923008 := by decide +kernel
private theorem receipt_0_15_2359_0_part4 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 512 128 = 162352998937188127300689387456 := by decide +kernel
private theorem receipt_0_15_2359_0_part5 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 640 128 = 144433890674138839606761668544 := by decide +kernel
private theorem receipt_0_15_2359_0_part6 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 768 128 = 127089372478911568972929867712 := by decide +kernel
private theorem receipt_0_15_2359_0_part7 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 896 128 = 110310088338130268766102126528 := by decide +kernel
private theorem receipt_0_15_2359_0_part8 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 1024 128 = 94086695720359761247184904128 := by decide +kernel
private theorem receipt_0_15_2359_0_part9 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 1152 128 = 78409865569818114356948254656 := by decide +kernel
private theorem receipt_0_15_2359_0_part10 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 1280 128 = 63270288067090577383595016495 := by decide +kernel
private theorem receipt_0_15_2359_0_part11 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 1408 128 = 48658682591829933695833509370 := by decide +kernel
private theorem receipt_0_15_2359_0_part12 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 1536 128 = 34565741763711446746574181650 := by decide +kernel
private theorem receipt_0_15_2359_0_part13 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 1664 128 = 20982158267465095378059751383 := by decide +kernel
private theorem receipt_0_15_2359_0_part14 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 1792 128 = 7898638278841618666740576595 := by decide +kernel
private theorem receipt_0_15_2359_0_part15 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 1920 15 = 91939104059827562086211528 := by decide +kernel
private theorem receipt_0_15_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 0 256 = 459614551783345372601452765056 :=
  phaseBlock_append receipt_0_15_2359_0_part0 receipt_0_15_2359_0_part1 rfl rfl rfl
private theorem receipt_0_15_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 256 256 = 380808543937350994951937859456 :=
  phaseBlock_append receipt_0_15_2359_0_part2 receipt_0_15_2359_0_part3 rfl rfl rfl
private theorem receipt_0_15_2359_0_join2 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 0 512 = 840423095720696367553390624512 :=
  phaseBlock_append receipt_0_15_2359_0_join0 receipt_0_15_2359_0_join1 rfl rfl rfl
private theorem receipt_0_15_2359_0_join3 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 512 256 = 306786889611326966907451056000 :=
  phaseBlock_append receipt_0_15_2359_0_part4 receipt_0_15_2359_0_part5 rfl rfl rfl
private theorem receipt_0_15_2359_0_join4 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 768 256 = 237399460817041837739031994240 :=
  phaseBlock_append receipt_0_15_2359_0_part6 receipt_0_15_2359_0_part7 rfl rfl rfl
private theorem receipt_0_15_2359_0_join5 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 512 512 = 544186350428368804646483050240 :=
  phaseBlock_append receipt_0_15_2359_0_join3 receipt_0_15_2359_0_join4 rfl rfl rfl
private theorem receipt_0_15_2359_0_join6 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 0 1024 = 1384609446149065172199873674752 :=
  phaseBlock_append receipt_0_15_2359_0_join2 receipt_0_15_2359_0_join5 rfl rfl rfl
private theorem receipt_0_15_2359_0_join7 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 1024 256 = 172496561290177875604133158784 :=
  phaseBlock_append receipt_0_15_2359_0_part8 receipt_0_15_2359_0_part9 rfl rfl rfl
private theorem receipt_0_15_2359_0_join8 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 1280 256 = 111928970658920511079428525865 :=
  phaseBlock_append receipt_0_15_2359_0_part10 receipt_0_15_2359_0_part11 rfl rfl rfl
private theorem receipt_0_15_2359_0_join9 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 1024 512 = 284425531949098386683561684649 :=
  phaseBlock_append receipt_0_15_2359_0_join7 receipt_0_15_2359_0_join8 rfl rfl rfl
private theorem receipt_0_15_2359_0_join10 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 1536 256 = 55547900031176542124633933033 :=
  phaseBlock_append receipt_0_15_2359_0_part12 receipt_0_15_2359_0_part13 rfl rfl rfl
private theorem receipt_0_15_2359_0_join11 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 1792 143 = 7990577382901446228826788123 :=
  phaseBlock_append receipt_0_15_2359_0_part14 receipt_0_15_2359_0_part15 rfl rfl rfl
private theorem receipt_0_15_2359_0_join12 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 1536 399 = 63538477414077988353460721156 :=
  phaseBlock_append receipt_0_15_2359_0_join10 receipt_0_15_2359_0_join11 rfl rfl rfl
private theorem receipt_0_15_2359_0_join13 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 1024 911 = 347964009363176375037022405805 :=
  phaseBlock_append receipt_0_15_2359_0_join9 receipt_0_15_2359_0_join12 rfl rfl rfl
private theorem receipt_0_15_2359_0_join14 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 0) 0 1935 = 1732573455512241547236896080557 :=
  phaseBlock_append receipt_0_15_2359_0_join6 receipt_0_15_2359_0_join13 rfl rfl rfl

private theorem receipt_0_15_2359_0 : fastPhase (bank 0 15).shape 179808 2379 76 1 0 1 0 = 1732573455512241547236896080557 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_15_2359_0_join14

private theorem receipt_0_15_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 0 128 = 239803974412556770475715447168 := by decide +kernel
private theorem receipt_0_15_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 128 128 = 219497332980899850810008553856 := by decide +kernel
private theorem receipt_0_15_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 256 128 = 199802769439789417046775613824 := by decide +kernel
private theorem receipt_0_15_2359_1_part3 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 384 128 = 180710873888139292547236579712 := by decide +kernel
private theorem receipt_0_15_2359_1_part4 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 512 128 = 162212249931906521268599114112 := by decide +kernel
private theorem receipt_0_15_2359_1_part5 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 640 128 = 144297514677803744549923867008 := by decide +kernel
private theorem receipt_0_15_2359_1_part6 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 768 128 = 126957298727011577897989753216 := by decide +kernel
private theorem receipt_0_15_2359_1_part7 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 896 128 = 110182246168890987773159229824 := by decide +kernel
private theorem receipt_0_15_2359_1_part8 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 1024 128 = 93963014574695668375243573632 := by decide +kernel
private theorem receipt_0_15_2359_1_part9 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 1152 128 = 78290274991284418429368158592 := by decide +kernel
private theorem receipt_0_15_2359_1_part10 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 1280 128 = 63154717691433592584543471823 := by decide +kernel
private theorem receipt_0_15_2359_1_part11 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 1408 128 = 48547062101952906417421488240 := by decide +kernel
private theorem receipt_0_15_2359_1_part12 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 1536 128 = 34458000927259000430790652228 := by decide +kernel
private theorem receipt_0_15_2359_1_part13 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 1664 128 = 20878226954717807220677524417 := by decide +kernel
private theorem receipt_0_15_2359_1_part14 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 1792 128 = 7798446462699551851055670087 := by decide +kernel
private theorem receipt_0_15_2359_1_part15 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 1920 15 = 80439432469924273107558273 := by decide +kernel
private theorem receipt_0_15_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 0 256 = 459301307393456621285724001024 :=
  phaseBlock_append receipt_0_15_2359_1_part0 receipt_0_15_2359_1_part1 rfl rfl rfl
private theorem receipt_0_15_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 256 256 = 380513643327928709594012193536 :=
  phaseBlock_append receipt_0_15_2359_1_part2 receipt_0_15_2359_1_part3 rfl rfl rfl
private theorem receipt_0_15_2359_1_join2 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 0 512 = 839814950721385330879736194560 :=
  phaseBlock_append receipt_0_15_2359_1_join0 receipt_0_15_2359_1_join1 rfl rfl rfl
private theorem receipt_0_15_2359_1_join3 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 512 256 = 306509764609710265818522981120 :=
  phaseBlock_append receipt_0_15_2359_1_part4 receipt_0_15_2359_1_part5 rfl rfl rfl
private theorem receipt_0_15_2359_1_join4 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 768 256 = 237139544895902565671148983040 :=
  phaseBlock_append receipt_0_15_2359_1_part6 receipt_0_15_2359_1_part7 rfl rfl rfl
private theorem receipt_0_15_2359_1_join5 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 512 512 = 543649309505612831489671964160 :=
  phaseBlock_append receipt_0_15_2359_1_join3 receipt_0_15_2359_1_join4 rfl rfl rfl
private theorem receipt_0_15_2359_1_join6 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 0 1024 = 1383464260226998162369408158720 :=
  phaseBlock_append receipt_0_15_2359_1_join2 receipt_0_15_2359_1_join5 rfl rfl rfl
private theorem receipt_0_15_2359_1_join7 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 1024 256 = 172253289565980086804611732224 :=
  phaseBlock_append receipt_0_15_2359_1_part8 receipt_0_15_2359_1_part9 rfl rfl rfl
private theorem receipt_0_15_2359_1_join8 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 1280 256 = 111701779793386499001964960063 :=
  phaseBlock_append receipt_0_15_2359_1_part10 receipt_0_15_2359_1_part11 rfl rfl rfl
private theorem receipt_0_15_2359_1_join9 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 1024 512 = 283955069359366585806576692287 :=
  phaseBlock_append receipt_0_15_2359_1_join7 receipt_0_15_2359_1_join8 rfl rfl rfl
private theorem receipt_0_15_2359_1_join10 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 1536 256 = 55336227881976807651468176645 :=
  phaseBlock_append receipt_0_15_2359_1_part12 receipt_0_15_2359_1_part13 rfl rfl rfl
private theorem receipt_0_15_2359_1_join11 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 1792 143 = 7878885895169476124163228360 :=
  phaseBlock_append receipt_0_15_2359_1_part14 receipt_0_15_2359_1_part15 rfl rfl rfl
private theorem receipt_0_15_2359_1_join12 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 1536 399 = 63215113777146283775631405005 :=
  phaseBlock_append receipt_0_15_2359_1_join10 receipt_0_15_2359_1_join11 rfl rfl rfl
private theorem receipt_0_15_2359_1_join13 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 1024 911 = 347170183136512869582208097292 :=
  phaseBlock_append receipt_0_15_2359_1_join9 receipt_0_15_2359_1_join12 rfl rfl rfl
private theorem receipt_0_15_2359_1_join14 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2379 76 1 0 1 1) 0 1935 = 1730634443363511031951616256012 :=
  phaseBlock_append receipt_0_15_2359_1_join6 receipt_0_15_2359_1_join13 rfl rfl rfl

private theorem receipt_0_15_2359_1 : fastPhase (bank 0 15).shape 179808 2379 76 1 0 1 1 = 1730634443363511031951616256012 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_15_2359_1_join14

private theorem receipt_0_15_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 0 128 = 239965075958113490033286486208 := by decide +kernel
private theorem receipt_0_15_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 128 128 = 219653522289368113175541258432 := by decide +kernel
private theorem receipt_0_15_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 256 128 = 199954134915989225734154459328 := by decide +kernel
private theorem receipt_0_15_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 384 128 = 180857503509322558756403026112 := by decide +kernel
private theorem receipt_0_15_2360_0_part4 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 512 128 = 162354231248275942011317557440 := by decide +kernel
private theorem receipt_0_15_2360_0_part5 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 640 128 = 144434934813031460873222035648 := by decide +kernel
private theorem receipt_0_15_2360_0_part6 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 768 128 = 127090244378757613205273548992 := by decide +kernel
private theorem receipt_0_15_2360_0_part7 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 896 128 = 110310803609321466243002013888 := by decide +kernel
private theorem receipt_0_15_2360_0_part8 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 1024 128 = 94087269651000813477849897152 := by decide +kernel
private theorem receipt_0_15_2360_0_part9 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 1152 128 = 78410313126196331540711938240 := by decide +kernel
private theorem receipt_0_15_2360_0_part10 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 1280 128 = 63270623693932308126192588515 := by decide +kernel
private theorem receipt_0_15_2360_0_part11 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 1408 128 = 48658920476856520272891189402 := by decide +kernel
private theorem receipt_0_15_2360_0_part12 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 1536 128 = 34565896145505575908077113317 := by decide +kernel
private theorem receipt_0_15_2360_0_part13 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 1664 128 = 20982243035807467434301254007 := by decide +kernel
private theorem receipt_0_15_2360_0_part14 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 1792 128 = 7898666977357527259194983866 := by decide +kernel
private theorem receipt_0_15_2360_0_part15 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 1920 15 = 91939410176059704136393418 := by decide +kernel
private theorem receipt_0_15_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 0 256 = 459618598247481603208827744640 :=
  phaseBlock_append receipt_0_15_2360_0_part0 receipt_0_15_2360_0_part1 rfl rfl rfl
private theorem receipt_0_15_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 256 256 = 380811638425311784490557485440 :=
  phaseBlock_append receipt_0_15_2360_0_part2 receipt_0_15_2360_0_part3 rfl rfl rfl
private theorem receipt_0_15_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 0 512 = 840430236672793387699385230080 :=
  phaseBlock_append receipt_0_15_2360_0_join0 receipt_0_15_2360_0_join1 rfl rfl rfl
private theorem receipt_0_15_2360_0_join3 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 512 256 = 306789166061307402884539593088 :=
  phaseBlock_append receipt_0_15_2360_0_part4 receipt_0_15_2360_0_part5 rfl rfl rfl
private theorem receipt_0_15_2360_0_join4 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 768 256 = 237401047988079079448275562880 :=
  phaseBlock_append receipt_0_15_2360_0_part6 receipt_0_15_2360_0_part7 rfl rfl rfl
private theorem receipt_0_15_2360_0_join5 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 512 512 = 544190214049386482332815155968 :=
  phaseBlock_append receipt_0_15_2360_0_join3 receipt_0_15_2360_0_join4 rfl rfl rfl
private theorem receipt_0_15_2360_0_join6 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 0 1024 = 1384620450722179870032200386048 :=
  phaseBlock_append receipt_0_15_2360_0_join2 receipt_0_15_2360_0_join5 rfl rfl rfl
private theorem receipt_0_15_2360_0_join7 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 1024 256 = 172497582777197145018561835392 :=
  phaseBlock_append receipt_0_15_2360_0_part8 receipt_0_15_2360_0_part9 rfl rfl rfl
private theorem receipt_0_15_2360_0_join8 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 1280 256 = 111929544170788828399083777917 :=
  phaseBlock_append receipt_0_15_2360_0_part10 receipt_0_15_2360_0_part11 rfl rfl rfl
private theorem receipt_0_15_2360_0_join9 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 1024 512 = 284427126947985973417645613309 :=
  phaseBlock_append receipt_0_15_2360_0_join7 receipt_0_15_2360_0_join8 rfl rfl rfl
private theorem receipt_0_15_2360_0_join10 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 1536 256 = 55548139181313043342378367324 :=
  phaseBlock_append receipt_0_15_2360_0_part12 receipt_0_15_2360_0_part13 rfl rfl rfl
private theorem receipt_0_15_2360_0_join11 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 1792 143 = 7990606387533586963331377284 :=
  phaseBlock_append receipt_0_15_2360_0_part14 receipt_0_15_2360_0_part15 rfl rfl rfl
private theorem receipt_0_15_2360_0_join12 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 1536 399 = 63538745568846630305709744608 :=
  phaseBlock_append receipt_0_15_2360_0_join10 receipt_0_15_2360_0_join11 rfl rfl rfl
private theorem receipt_0_15_2360_0_join13 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 1024 911 = 347965872516832603723355357917 :=
  phaseBlock_append receipt_0_15_2360_0_join9 receipt_0_15_2360_0_join12 rfl rfl rfl
private theorem receipt_0_15_2360_0_join14 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 0) 0 1935 = 1732586323239012473755555743965 :=
  phaseBlock_append receipt_0_15_2360_0_join6 receipt_0_15_2360_0_join13 rfl rfl rfl

private theorem receipt_0_15_2360_0 : fastPhase (bank 0 15).shape 179808 2380 76 1 0 1 0 = 1732586323239012473755555743965 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_15_2360_0_join14

private theorem receipt_0_15_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 0 128 = 239806124049114209754080235008 := by decide +kernel
private theorem receipt_0_15_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 128 128 = 219499227543531820043667246592 := by decide +kernel
private theorem receipt_0_15_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 256 128 = 199804426155842484187912588800 := by decide +kernel
private theorem receipt_0_15_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 384 128 = 180712309660324088571978812928 := by decide +kernel
private theorem receipt_0_15_2360_1_part4 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 512 128 = 162213481338768475842562575872 := by decide +kernel
private theorem receipt_0_15_2360_1_part5 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 640 128 = 144298557974193601791434362368 := by decide +kernel
private theorem receipt_0_15_2360_1_part6 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 768 128 = 126958169844555692238978207232 := by decide +kernel
private theorem receipt_0_15_2360_1_part7 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 896 128 = 110182960716461399917731417600 := by decide +kernel
private theorem receipt_0_15_2360_1_part8 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 1024 128 = 93963587838879961355924295168 := by decide +kernel
private theorem receipt_0_15_2360_1_part9 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 1152 128 = 78290721936855353761019858432 := by decide +kernel
private theorem receipt_0_15_2360_1_part10 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 1280 128 = 63155052761960152664725667528 := by decide +kernel
private theorem receipt_0_15_2360_1_part11 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 1408 128 = 48547299484116338692360549382 := by decide +kernel
private theorem receipt_0_15_2360_1_part12 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 1536 128 = 34458154858060738055988185218 := by decide +kernel
private theorem receipt_0_15_2360_1_part13 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 1664 128 = 20878311322364004680841707920 := by decide +kernel
private theorem receipt_0_15_2360_1_part14 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 1792 128 = 7798474809249282437648052879 := by decide +kernel
private theorem receipt_0_15_2360_1_part15 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 1920 15 = 80439700456517229958333315 := by decide +kernel
private theorem receipt_0_15_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 0 256 = 459305351592646029797747481600 :=
  phaseBlock_append receipt_0_15_2360_1_part0 receipt_0_15_2360_1_part1 rfl rfl rfl
private theorem receipt_0_15_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 256 256 = 380516735816166572759891401728 :=
  phaseBlock_append receipt_0_15_2360_1_part2 receipt_0_15_2360_1_part3 rfl rfl rfl
private theorem receipt_0_15_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 0 512 = 839822087408812602557638883328 :=
  phaseBlock_append receipt_0_15_2360_1_join0 receipt_0_15_2360_1_join1 rfl rfl rfl
private theorem receipt_0_15_2360_1_join3 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 512 256 = 306512039312962077633996938240 :=
  phaseBlock_append receipt_0_15_2360_1_part4 receipt_0_15_2360_1_part5 rfl rfl rfl
private theorem receipt_0_15_2360_1_join4 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 768 256 = 237141130561017092156709624832 :=
  phaseBlock_append receipt_0_15_2360_1_part6 receipt_0_15_2360_1_part7 rfl rfl rfl
private theorem receipt_0_15_2360_1_join5 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 512 512 = 543653169873979169790706563072 :=
  phaseBlock_append receipt_0_15_2360_1_join3 receipt_0_15_2360_1_join4 rfl rfl rfl
private theorem receipt_0_15_2360_1_join6 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 0 1024 = 1383475257282791772348345446400 :=
  phaseBlock_append receipt_0_15_2360_1_join2 receipt_0_15_2360_1_join5 rfl rfl rfl
private theorem receipt_0_15_2360_1_join7 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 1024 256 = 172254309775735315116944153600 :=
  phaseBlock_append receipt_0_15_2360_1_part8 receipt_0_15_2360_1_part9 rfl rfl rfl
private theorem receipt_0_15_2360_1_join8 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 1280 256 = 111702352246076491357086216910 :=
  phaseBlock_append receipt_0_15_2360_1_part10 receipt_0_15_2360_1_part11 rfl rfl rfl
private theorem receipt_0_15_2360_1_join9 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 1024 512 = 283956662021811806474030370510 :=
  phaseBlock_append receipt_0_15_2360_1_join7 receipt_0_15_2360_1_join8 rfl rfl rfl
private theorem receipt_0_15_2360_1_join10 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 1536 256 = 55336466180424742736829893138 :=
  phaseBlock_append receipt_0_15_2360_1_part12 receipt_0_15_2360_1_part13 rfl rfl rfl
private theorem receipt_0_15_2360_1_join11 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 1792 143 = 7878914509705799667606386194 :=
  phaseBlock_append receipt_0_15_2360_1_part14 receipt_0_15_2360_1_part15 rfl rfl rfl
private theorem receipt_0_15_2360_1_join12 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 1536 399 = 63215380690130542404436279332 :=
  phaseBlock_append receipt_0_15_2360_1_join10 receipt_0_15_2360_1_join11 rfl rfl rfl
private theorem receipt_0_15_2360_1_join13 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 1024 911 = 347172042711942348878466649842 :=
  phaseBlock_append receipt_0_15_2360_1_join9 receipt_0_15_2360_1_join12 rfl rfl rfl
private theorem receipt_0_15_2360_1_join14 :
    phaseBlock (fastLayer (bank 0 15).shape 179808 2380 76 1 0 1 1) 0 1935 = 1730647299994734121226812096242 :=
  phaseBlock_append receipt_0_15_2360_1_join6 receipt_0_15_2360_1_join13 rfl rfl rfl

private theorem receipt_0_15_2360_1 : fastPhase (bank 0 15).shape 179808 2380 76 1 0 1 1 = 1730647299994734121226812096242 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_15_2360_1_join14

theorem receipt_0_15 : Checked (bank 0 15) 76 0 1 := by
  refine checked_from_values (bank 0 15) 76 0 1
    (P3_7_1.checked (bank 0 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9204_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_15_2359_0 receipt_0_15_2359_1 receipt_0_15_2360_0 receipt_0_15_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_15_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 0 128 = 216036310194848454051737835264 := by decide +kernel
private theorem receipt_1_15_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 128 128 = 197667154441811874198424114944 := by decide +kernel
private theorem receipt_1_15_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 256 128 = 179864006327710246203185469184 := by decide +kernel
private theorem receipt_1_15_2359_0_part3 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 384 128 = 162617713509648347272270141184 := by decide +kernel
private theorem receipt_1_15_2359_0_part4 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 512 128 = 145919149800436020983189346048 := by decide +kernel
private theorem receipt_1_15_2359_0_part5 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 640 128 = 129759215143437684428178380544 := by decide +kernel
private theorem receipt_1_15_2359_0_part6 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 768 128 = 114128835587421835357657732864 := by decide +kernel
private theorem receipt_1_15_2359_0_part7 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 896 128 = 99018963261410559323694192384 := by decide +kernel
private theorem receipt_1_15_2359_0_part8 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 1024 128 = 84420576349529036823461959424 := by decide +kernel
private theorem receipt_1_15_2359_0_part9 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 1152 128 = 70324679065855050442703755008 := by decide +kernel
private theorem receipt_1_15_2359_0_part10 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 1280 128 = 56722306798799903885343239775 := by decide +kernel
private theorem receipt_1_15_2359_0_part11 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 1408 128 = 43604535010022106970687809688 := by decide +kernel
private theorem receipt_1_15_2359_0_part12 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 1536 128 = 30962429060023208904581260754 := by decide +kernel
private theorem receipt_1_15_2359_0_part13 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 1664 128 = 18787068280986450551367429054 := by decide +kernel
private theorem receipt_1_15_2359_0_part14 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 1792 128 = 7069557999882515717482862131 := by decide +kernel
private theorem receipt_1_15_2359_0_part15 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 1920 15 = 82265152723223795698196810 := by decide +kernel
private theorem receipt_1_15_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 0 256 = 413703464636660328250161950208 :=
  phaseBlock_append receipt_1_15_2359_0_part0 receipt_1_15_2359_0_part1 rfl rfl rfl
private theorem receipt_1_15_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 256 256 = 342481719837358593475455610368 :=
  phaseBlock_append receipt_1_15_2359_0_part2 receipt_1_15_2359_0_part3 rfl rfl rfl
private theorem receipt_1_15_2359_0_join2 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 0 512 = 756185184474018921725617560576 :=
  phaseBlock_append receipt_1_15_2359_0_join0 receipt_1_15_2359_0_join1 rfl rfl rfl
private theorem receipt_1_15_2359_0_join3 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 512 256 = 275678364943873705411367726592 :=
  phaseBlock_append receipt_1_15_2359_0_part4 receipt_1_15_2359_0_part5 rfl rfl rfl
private theorem receipt_1_15_2359_0_join4 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 768 256 = 213147798848832394681351925248 :=
  phaseBlock_append receipt_1_15_2359_0_part6 receipt_1_15_2359_0_part7 rfl rfl rfl
private theorem receipt_1_15_2359_0_join5 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 512 512 = 488826163792706100092719651840 :=
  phaseBlock_append receipt_1_15_2359_0_join3 receipt_1_15_2359_0_join4 rfl rfl rfl
private theorem receipt_1_15_2359_0_join6 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 0 1024 = 1245011348266725021818337212416 :=
  phaseBlock_append receipt_1_15_2359_0_join2 receipt_1_15_2359_0_join5 rfl rfl rfl
private theorem receipt_1_15_2359_0_join7 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 1024 256 = 154745255415384087266165714432 :=
  phaseBlock_append receipt_1_15_2359_0_part8 receipt_1_15_2359_0_part9 rfl rfl rfl
private theorem receipt_1_15_2359_0_join8 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 1280 256 = 100326841808822010856031049463 :=
  phaseBlock_append receipt_1_15_2359_0_part10 receipt_1_15_2359_0_part11 rfl rfl rfl
private theorem receipt_1_15_2359_0_join9 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 1024 512 = 255072097224206098122196763895 :=
  phaseBlock_append receipt_1_15_2359_0_join7 receipt_1_15_2359_0_join8 rfl rfl rfl
private theorem receipt_1_15_2359_0_join10 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 1536 256 = 49749497341009659455948689808 :=
  phaseBlock_append receipt_1_15_2359_0_part12 receipt_1_15_2359_0_part13 rfl rfl rfl
private theorem receipt_1_15_2359_0_join11 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 1792 143 = 7151823152605739513181058941 :=
  phaseBlock_append receipt_1_15_2359_0_part14 receipt_1_15_2359_0_part15 rfl rfl rfl
private theorem receipt_1_15_2359_0_join12 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 1536 399 = 56901320493615398969129748749 :=
  phaseBlock_append receipt_1_15_2359_0_join10 receipt_1_15_2359_0_join11 rfl rfl rfl
private theorem receipt_1_15_2359_0_join13 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 1024 911 = 311973417717821497091326512644 :=
  phaseBlock_append receipt_1_15_2359_0_join9 receipt_1_15_2359_0_join12 rfl rfl rfl
private theorem receipt_1_15_2359_0_join14 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 0) 0 1935 = 1556984765984546518909663725060 :=
  phaseBlock_append receipt_1_15_2359_0_join6 receipt_1_15_2359_0_join13 rfl rfl rfl

private theorem receipt_1_15_2359_0 : fastPhase (bank 1 15).shape 179808 2379 76 1 0 2 0 = 1556984765984546518909663725060 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_15_2359_0_join14

private theorem receipt_1_15_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 0 128 = 215892499719465673386805234752 := by decide +kernel
private theorem receipt_1_15_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 128 128 = 197527655008039849014276025408 := by decide +kernel
private theorem receipt_1_15_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 256 128 = 179728748605543251804915485760 := by decide +kernel
private theorem receipt_1_15_2359_1_part3 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 384 128 = 162486628368479159946410011712 := by decide +kernel
private theorem receipt_1_15_2359_1_part4 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 512 128 = 145792168308863353379510979648 := by decide +kernel
private theorem receipt_1_15_2359_1_part5 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 640 128 = 129636268569073620941495856192 := by decide +kernel
private theorem receipt_1_15_2359_1_part6 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 768 128 = 114009855396699267509629307968 := by decide +kernel
private theorem receipt_1_15_2359_1_part7 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 896 128 = 98903881119390621144624311360 := by decide +kernel
private theorem receipt_1_15_2359_1_part8 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 1024 128 = 84309324119708540234103262272 := by decide +kernel
private theorem receipt_1_15_2359_1_part9 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 1152 128 = 70217188809973920636059085888 := by decide +kernel
private theorem receipt_1_15_2359_1_part10 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 1280 128 = 56618510767307718683110447444 := by decide +kernel
private theorem receipt_1_15_2359_1_part11 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 1408 128 = 43504365601541262662707259598 := by decide +kernel
private theorem receipt_1_15_2359_1_part12 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 1536 128 = 30865818855066398577960529396 := by decide +kernel
private theorem receipt_1_15_2359_1_part13 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 1664 128 = 18693950057897512793552561119 := by decide +kernel
private theorem receipt_1_15_2359_1_part14 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 1792 128 = 6979864734671884647744782910 := by decide +kernel
private theorem receipt_1_15_2359_1_part15 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 1920 15 = 71975332452634089215906589 := by decide +kernel
private theorem receipt_1_15_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 0 256 = 413420154727505522401081260160 :=
  phaseBlock_append receipt_1_15_2359_1_part0 receipt_1_15_2359_1_part1 rfl rfl rfl
private theorem receipt_1_15_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 256 256 = 342215376974022411751325497472 :=
  phaseBlock_append receipt_1_15_2359_1_part2 receipt_1_15_2359_1_part3 rfl rfl rfl
private theorem receipt_1_15_2359_1_join2 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 0 512 = 755635531701527934152406757632 :=
  phaseBlock_append receipt_1_15_2359_1_join0 receipt_1_15_2359_1_join1 rfl rfl rfl
private theorem receipt_1_15_2359_1_join3 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 512 256 = 275428436877936974321006835840 :=
  phaseBlock_append receipt_1_15_2359_1_part4 receipt_1_15_2359_1_part5 rfl rfl rfl
private theorem receipt_1_15_2359_1_join4 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 768 256 = 212913736516089888654253619328 :=
  phaseBlock_append receipt_1_15_2359_1_part6 receipt_1_15_2359_1_part7 rfl rfl rfl
private theorem receipt_1_15_2359_1_join5 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 512 512 = 488342173394026862975260455168 :=
  phaseBlock_append receipt_1_15_2359_1_join3 receipt_1_15_2359_1_join4 rfl rfl rfl
private theorem receipt_1_15_2359_1_join6 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 0 1024 = 1243977705095554797127667212800 :=
  phaseBlock_append receipt_1_15_2359_1_join2 receipt_1_15_2359_1_join5 rfl rfl rfl
private theorem receipt_1_15_2359_1_join7 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 1024 256 = 154526512929682460870162348160 :=
  phaseBlock_append receipt_1_15_2359_1_part8 receipt_1_15_2359_1_part9 rfl rfl rfl
private theorem receipt_1_15_2359_1_join8 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 1280 256 = 100122876368848981345817707042 :=
  phaseBlock_append receipt_1_15_2359_1_part10 receipt_1_15_2359_1_part11 rfl rfl rfl
private theorem receipt_1_15_2359_1_join9 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 1024 512 = 254649389298531442215980055202 :=
  phaseBlock_append receipt_1_15_2359_1_join7 receipt_1_15_2359_1_join8 rfl rfl rfl
private theorem receipt_1_15_2359_1_join10 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 1536 256 = 49559768912963911371513090515 :=
  phaseBlock_append receipt_1_15_2359_1_part12 receipt_1_15_2359_1_part13 rfl rfl rfl
private theorem receipt_1_15_2359_1_join11 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 1792 143 = 7051840067124518736960689499 :=
  phaseBlock_append receipt_1_15_2359_1_part14 receipt_1_15_2359_1_part15 rfl rfl rfl
private theorem receipt_1_15_2359_1_join12 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 1536 399 = 56611608980088430108473780014 :=
  phaseBlock_append receipt_1_15_2359_1_join10 receipt_1_15_2359_1_join11 rfl rfl rfl
private theorem receipt_1_15_2359_1_join13 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 1024 911 = 311260998278619872324453835216 :=
  phaseBlock_append receipt_1_15_2359_1_join9 receipt_1_15_2359_1_join12 rfl rfl rfl
private theorem receipt_1_15_2359_1_join14 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2379 76 1 0 2 1) 0 1935 = 1555238703374174669452121048016 :=
  phaseBlock_append receipt_1_15_2359_1_join6 receipt_1_15_2359_1_join13 rfl rfl rfl

private theorem receipt_1_15_2359_1 : fastPhase (bank 1 15).shape 179808 2379 76 1 0 2 1 = 1555238703374174669452121048016 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_15_2359_1_join14

private theorem receipt_1_15_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 0 128 = 216038246544519846080689396288 := by decide +kernel
private theorem receipt_1_15_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 128 128 = 197668860372560981095726848576 := by decide +kernel
private theorem receipt_1_15_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 256 128 = 179865497530459857186711755328 := by decide +kernel
private theorem receipt_1_15_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 384 128 = 162619005363903926835699292736 := by decide +kernel
private theorem receipt_1_15_2360_0_part4 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 512 128 = 145920257375193842828387801664 := by decide +kernel
private theorem receipt_1_15_2360_0_part5 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 640 128 = 129760153198092085788277676608 := by decide +kernel
private theorem receipt_1_15_2360_0_part6 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 768 128 = 114129618572671591710830254656 := by decide +kernel
private theorem receipt_1_15_2360_0_part7 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 896 128 = 99019605320164379497626704448 := by decide +kernel
private theorem receipt_1_15_2360_0_part8 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 1024 128 = 84421091317810178490526915136 := by decide +kernel
private theorem receipt_1_15_2360_0_part9 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 1152 128 = 70325080473705056005828385344 := by decide +kernel
private theorem receipt_1_15_2360_0_part10 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 1280 128 = 56722607691704786961299240219 := by decide +kernel
private theorem receipt_1_15_2360_0_part11 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 1408 128 = 43604748186721212371448145821 := by decide +kernel
private theorem receipt_1_15_2360_0_part12 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 1536 128 = 30962567348720649793148322733 := by decide +kernel
private theorem receipt_1_15_2360_0_part13 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 1664 128 = 18787144181402748104712583312 := by decide +kernel
private theorem receipt_1_15_2360_0_part14 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 1792 128 = 7069583686147151690093367634 := by decide +kernel
private theorem receipt_1_15_2360_0_part15 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 1920 15 = 82265426629523510172928982 := by decide +kernel
private theorem receipt_1_15_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 0 256 = 413707106917080827176416244864 :=
  phaseBlock_append receipt_1_15_2360_0_part0 receipt_1_15_2360_0_part1 rfl rfl rfl
private theorem receipt_1_15_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 256 256 = 342484502894363784022411048064 :=
  phaseBlock_append receipt_1_15_2360_0_part2 receipt_1_15_2360_0_part3 rfl rfl rfl
private theorem receipt_1_15_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 0 512 = 756191609811444611198827292928 :=
  phaseBlock_append receipt_1_15_2360_0_join0 receipt_1_15_2360_0_join1 rfl rfl rfl
private theorem receipt_1_15_2360_0_join3 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 512 256 = 275680410573285928616665478272 :=
  phaseBlock_append receipt_1_15_2360_0_part4 receipt_1_15_2360_0_part5 rfl rfl rfl
private theorem receipt_1_15_2360_0_join4 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 768 256 = 213149223892835971208456959104 :=
  phaseBlock_append receipt_1_15_2360_0_part6 receipt_1_15_2360_0_part7 rfl rfl rfl
private theorem receipt_1_15_2360_0_join5 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 512 512 = 488829634466121899825122437376 :=
  phaseBlock_append receipt_1_15_2360_0_join3 receipt_1_15_2360_0_join4 rfl rfl rfl
private theorem receipt_1_15_2360_0_join6 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 0 1024 = 1245021244277566511023949730304 :=
  phaseBlock_append receipt_1_15_2360_0_join2 receipt_1_15_2360_0_join5 rfl rfl rfl
private theorem receipt_1_15_2360_0_join7 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 1024 256 = 154746171791515234496355300480 :=
  phaseBlock_append receipt_1_15_2360_0_part8 receipt_1_15_2360_0_part9 rfl rfl rfl
private theorem receipt_1_15_2360_0_join8 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 1280 256 = 100327355878425999332747386040 :=
  phaseBlock_append receipt_1_15_2360_0_part10 receipt_1_15_2360_0_part11 rfl rfl rfl
private theorem receipt_1_15_2360_0_join9 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 1024 512 = 255073527669941233829102686520 :=
  phaseBlock_append receipt_1_15_2360_0_join7 receipt_1_15_2360_0_join8 rfl rfl rfl
private theorem receipt_1_15_2360_0_join10 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 1536 256 = 49749711530123397897860906045 :=
  phaseBlock_append receipt_1_15_2360_0_part12 receipt_1_15_2360_0_part13 rfl rfl rfl
private theorem receipt_1_15_2360_0_join11 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 1792 143 = 7151849112776675200266296616 :=
  phaseBlock_append receipt_1_15_2360_0_part14 receipt_1_15_2360_0_part15 rfl rfl rfl
private theorem receipt_1_15_2360_0_join12 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 1536 399 = 56901560642900073098127202661 :=
  phaseBlock_append receipt_1_15_2360_0_join10 receipt_1_15_2360_0_join11 rfl rfl rfl
private theorem receipt_1_15_2360_0_join13 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 1024 911 = 311975088312841306927229889181 :=
  phaseBlock_append receipt_1_15_2360_0_join9 receipt_1_15_2360_0_join12 rfl rfl rfl
private theorem receipt_1_15_2360_0_join14 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 0) 0 1935 = 1556996332590407817951179619485 :=
  phaseBlock_append receipt_1_15_2360_0_join6 receipt_1_15_2360_0_join13 rfl rfl rfl

private theorem receipt_1_15_2360_0 : fastPhase (bank 1 15).shape 179808 2380 76 1 0 2 0 = 1556996332590407817951179619485 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_15_2360_0_join14

private theorem receipt_1_15_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 0 128 = 215894435012691262589871933248 := by decide +kernel
private theorem receipt_1_15_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 128 128 = 197529359944585687870447863616 := by decide +kernel
private theorem receipt_1_15_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 256 128 = 179730238874851569944373774144 := by decide +kernel
private theorem receipt_1_15_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 384 128 = 162487919348579841766273566528 := by decide +kernel
private theorem receipt_1_15_2360_1_part4 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 512 128 = 145793275067282066753536083776 := by decide +kernel
private theorem receipt_1_15_2360_1_part5 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 640 128 = 129637205863739066320473999168 := by decide +kernel
private theorem receipt_1_15_2360_1_part6 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 768 128 = 114010637676849547412482705216 := by decide +kernel
private theorem receipt_1_15_2360_1_part7 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 896 128 = 98904522526478730040199202624 := by decide +kernel
private theorem receipt_1_15_2360_1_part8 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 1024 128 = 84309838488306974813660989248 := by decide +kernel
private theorem receipt_1_15_2360_1_part9 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 1152 128 = 70217589668678410476464949056 := by decide +kernel
private theorem receipt_1_15_2360_1_part10 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 1280 128 = 56618811160481884208844545711 := by decide +kernel
private theorem receipt_1_15_2360_1_part11 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 1408 128 = 43504578326909244524762137481 := by decide +kernel
private theorem receipt_1_15_2360_1_part12 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 1536 128 = 30865956739333341718763028661 := by decide +kernel
private theorem receipt_1_15_2360_1_part13 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 1664 128 = 18694025599293776967420013255 := by decide +kernel
private theorem receipt_1_15_2360_1_part14 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 1792 128 = 6979890105847026104267766576 := by decide +kernel
private theorem receipt_1_15_2360_1_part15 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 1920 15 = 71975572240811774975872957 := by decide +kernel
private theorem receipt_1_15_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 0 256 = 413423794957276950460319796864 :=
  phaseBlock_append receipt_1_15_2360_1_part0 receipt_1_15_2360_1_part1 rfl rfl rfl
private theorem receipt_1_15_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 256 256 = 342218158223431411710647340672 :=
  phaseBlock_append receipt_1_15_2360_1_part2 receipt_1_15_2360_1_part3 rfl rfl rfl
private theorem receipt_1_15_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 0 512 = 755641953180708362170967137536 :=
  phaseBlock_append receipt_1_15_2360_1_join0 receipt_1_15_2360_1_join1 rfl rfl rfl
private theorem receipt_1_15_2360_1_join3 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 512 256 = 275430480931021133074010082944 :=
  phaseBlock_append receipt_1_15_2360_1_part4 receipt_1_15_2360_1_part5 rfl rfl rfl
private theorem receipt_1_15_2360_1_join4 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 768 256 = 212915160203328277452681907840 :=
  phaseBlock_append receipt_1_15_2360_1_part6 receipt_1_15_2360_1_part7 rfl rfl rfl
private theorem receipt_1_15_2360_1_join5 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 512 512 = 488345641134349410526691990784 :=
  phaseBlock_append receipt_1_15_2360_1_join3 receipt_1_15_2360_1_join4 rfl rfl rfl
private theorem receipt_1_15_2360_1_join6 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 0 1024 = 1243987594315057772697659128320 :=
  phaseBlock_append receipt_1_15_2360_1_join2 receipt_1_15_2360_1_join5 rfl rfl rfl
private theorem receipt_1_15_2360_1_join7 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 1024 256 = 154527428156985385290125938304 :=
  phaseBlock_append receipt_1_15_2360_1_part8 receipt_1_15_2360_1_part9 rfl rfl rfl
private theorem receipt_1_15_2360_1_join8 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 1280 256 = 100123389487391128733606683192 :=
  phaseBlock_append receipt_1_15_2360_1_part10 receipt_1_15_2360_1_part11 rfl rfl rfl
private theorem receipt_1_15_2360_1_join9 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 1024 512 = 254650817644376514023732621496 :=
  phaseBlock_append receipt_1_15_2360_1_join7 receipt_1_15_2360_1_join8 rfl rfl rfl
private theorem receipt_1_15_2360_1_join10 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 1536 256 = 49559982338627118686183041916 :=
  phaseBlock_append receipt_1_15_2360_1_part12 receipt_1_15_2360_1_part13 rfl rfl rfl
private theorem receipt_1_15_2360_1_join11 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 1792 143 = 7051865678087837879243639533 :=
  phaseBlock_append receipt_1_15_2360_1_part14 receipt_1_15_2360_1_part15 rfl rfl rfl
private theorem receipt_1_15_2360_1_join12 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 1536 399 = 56611848016714956565426681449 :=
  phaseBlock_append receipt_1_15_2360_1_join10 receipt_1_15_2360_1_join11 rfl rfl rfl
private theorem receipt_1_15_2360_1_join13 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 1024 911 = 311262665661091470589159302945 :=
  phaseBlock_append receipt_1_15_2360_1_join9 receipt_1_15_2360_1_join12 rfl rfl rfl
private theorem receipt_1_15_2360_1_join14 :
    phaseBlock (fastLayer (bank 1 15).shape 179808 2380 76 1 0 2 1) 0 1935 = 1555250259976149243286818431265 :=
  phaseBlock_append receipt_1_15_2360_1_join6 receipt_1_15_2360_1_join13 rfl rfl rfl

private theorem receipt_1_15_2360_1 : fastPhase (bank 1 15).shape 179808 2380 76 1 0 2 1 = 1555250259976149243286818431265 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_15_2360_1_join14

theorem receipt_1_15 : Checked (bank 1 15) 76 0 2 := by
  refine checked_from_values (bank 1 15) 76 0 2
    (P3_7_1.checked (bank 1 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9204_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_15_2359_0 receipt_1_15_2359_1 receipt_1_15_2360_0 receipt_1_15_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_15_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 0 128 = 115854541812422116595161932480 := by decide +kernel
private theorem receipt_2_15_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 128 128 = 105683509395618941772470731456 := by decide +kernel
private theorem receipt_2_15_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 256 128 = 95873907129804793113903162048 := by decide +kernel
private theorem receipt_2_15_2359_0_part3 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 384 128 = 86418060977031896931096920768 := by decide +kernel
private theorem receipt_2_15_2359_0_part4 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 512 128 = 77308373590000032410913022656 := by decide +kernel
private theorem receipt_2_15_2359_0_part5 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 640 128 = 68537324003962994122834395840 := by decide +kernel
private theorem receipt_2_15_2359_0_part6 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 768 128 = 60097467328635054526364476096 := by decide +kernel
private theorem receipt_2_15_2359_0_part7 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 896 128 = 51981434440097426478425801408 := by decide +kernel
private theorem receipt_2_15_2359_0_part8 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 1024 128 = 44181931672704725740758606528 := by decide +kernel
private theorem receipt_2_15_2359_0_part9 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 1152 128 = 36691740510991433487319417536 := by decide +kernel
private theorem receipt_2_15_2359_0_part10 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 1280 128 = 29503719968075506466201652190 := by decide +kernel
private theorem receipt_2_15_2359_0_part11 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 1408 128 = 22610810869134775344617524734 := by decide +kernel
private theorem receipt_2_15_2359_0_part12 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 1536 128 = 16006009507481571530926449602 := by decide +kernel
private theorem receipt_2_15_2359_0_part13 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 1664 128 = 9682380036017848207224082578 := by decide +kernel
private theorem receipt_2_15_2359_0_part14 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 1792 128 = 3633060448522302109626207768 := by decide +kernel
private theorem receipt_2_15_2359_0_part15 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 1920 15 = 42187052728238743758307896 := by decide +kernel
private theorem receipt_2_15_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 0 256 = 221538051208041058367632663936 :=
  phaseBlock_append receipt_2_15_2359_0_part0 receipt_2_15_2359_0_part1 rfl rfl rfl
private theorem receipt_2_15_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 256 256 = 182291968106836690045000082816 :=
  phaseBlock_append receipt_2_15_2359_0_part2 receipt_2_15_2359_0_part3 rfl rfl rfl
private theorem receipt_2_15_2359_0_join2 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 0 512 = 403830019314877748412632746752 :=
  phaseBlock_append receipt_2_15_2359_0_join0 receipt_2_15_2359_0_join1 rfl rfl rfl
private theorem receipt_2_15_2359_0_join3 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 512 256 = 145845697593963026533747418496 :=
  phaseBlock_append receipt_2_15_2359_0_part4 receipt_2_15_2359_0_part5 rfl rfl rfl
private theorem receipt_2_15_2359_0_join4 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 768 256 = 112078901768732481004790277504 :=
  phaseBlock_append receipt_2_15_2359_0_part6 receipt_2_15_2359_0_part7 rfl rfl rfl
private theorem receipt_2_15_2359_0_join5 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 512 512 = 257924599362695507538537696000 :=
  phaseBlock_append receipt_2_15_2359_0_join3 receipt_2_15_2359_0_join4 rfl rfl rfl
private theorem receipt_2_15_2359_0_join6 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 0 1024 = 661754618677573255951170442752 :=
  phaseBlock_append receipt_2_15_2359_0_join2 receipt_2_15_2359_0_join5 rfl rfl rfl
private theorem receipt_2_15_2359_0_join7 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 1024 256 = 80873672183696159228078024064 :=
  phaseBlock_append receipt_2_15_2359_0_part8 receipt_2_15_2359_0_part9 rfl rfl rfl
private theorem receipt_2_15_2359_0_join8 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 1280 256 = 52114530837210281810819176924 :=
  phaseBlock_append receipt_2_15_2359_0_part10 receipt_2_15_2359_0_part11 rfl rfl rfl
private theorem receipt_2_15_2359_0_join9 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 1024 512 = 132988203020906441038897200988 :=
  phaseBlock_append receipt_2_15_2359_0_join7 receipt_2_15_2359_0_join8 rfl rfl rfl
private theorem receipt_2_15_2359_0_join10 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 1536 256 = 25688389543499419738150532180 :=
  phaseBlock_append receipt_2_15_2359_0_part12 receipt_2_15_2359_0_part13 rfl rfl rfl
private theorem receipt_2_15_2359_0_join11 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 1792 143 = 3675247501250540853384515664 :=
  phaseBlock_append receipt_2_15_2359_0_part14 receipt_2_15_2359_0_part15 rfl rfl rfl
private theorem receipt_2_15_2359_0_join12 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 1536 399 = 29363637044749960591535047844 :=
  phaseBlock_append receipt_2_15_2359_0_join10 receipt_2_15_2359_0_join11 rfl rfl rfl
private theorem receipt_2_15_2359_0_join13 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 1024 911 = 162351840065656401630432248832 :=
  phaseBlock_append receipt_2_15_2359_0_join9 receipt_2_15_2359_0_join12 rfl rfl rfl
private theorem receipt_2_15_2359_0_join14 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 0) 0 1935 = 824106458743229657581602691584 :=
  phaseBlock_append receipt_2_15_2359_0_join6 receipt_2_15_2359_0_join13 rfl rfl rfl

private theorem receipt_2_15_2359_0 : fastPhase (bank 2 15).shape 179808 2379 76 1 0 7 0 = 824106458743229657581602691584 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_15_2359_0_join14

private theorem receipt_2_15_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 0 128 = 115774687311170338115585743872 := by decide +kernel
private theorem receipt_2_15_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 128 128 = 105606427116357292351986113536 := by decide +kernel
private theorem receipt_2_15_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 256 128 = 95799538509611138116013431808 := by decide +kernel
private theorem receipt_2_15_2359_1_part3 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 384 128 = 86346348039105054540486712320 := by decide +kernel
private theorem receipt_2_15_2359_1_part4 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 512 128 = 77239258941300857060522892288 := by decide +kernel
private theorem receipt_2_15_2359_1_part5 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 640 128 = 68470750832855459920935427072 := by decide +kernel
private theorem receipt_2_15_2359_1_part6 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 768 128 = 60033379402527338683632884736 := by decide +kernel
private theorem receipt_2_15_2359_1_part7 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 896 128 = 51919776103082992735017540608 := by decide +kernel
private theorem receipt_2_15_2359_1_part8 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 1024 128 = 44122647843203407793383971840 := by decide +kernel
private theorem receipt_2_15_2359_1_part9 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 1152 128 = 36634776679390518416317651968 := by decide +kernel
private theorem receipt_2_15_2359_1_part10 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 1280 128 = 29449022189451794623254838228 := by decide +kernel
private theorem receipt_2_15_2359_1_part11 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 1408 128 = 22558325739858395966417414504 := by decide +kernel
private theorem receipt_2_15_2359_1_part12 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 1536 128 = 15955684181149513494905655864 := by decide +kernel
private theorem receipt_2_15_2359_1_part13 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 1664 128 = 9634162229664524715125421396 := by decide +kernel
private theorem receipt_2_15_2359_1_part14 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 1792 128 = 3586898440269937424788135294 := by decide +kernel
private theorem receipt_2_15_2359_1_part15 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 1920 15 = 36909646081528929968174888 := by decide +kernel
private theorem receipt_2_15_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 0 256 = 221381114427527630467571857408 :=
  phaseBlock_append receipt_2_15_2359_1_part0 receipt_2_15_2359_1_part1 rfl rfl rfl
private theorem receipt_2_15_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 256 256 = 182145886548716192656500144128 :=
  phaseBlock_append receipt_2_15_2359_1_part2 receipt_2_15_2359_1_part3 rfl rfl rfl
private theorem receipt_2_15_2359_1_join2 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 0 512 = 403527000976243823124072001536 :=
  phaseBlock_append receipt_2_15_2359_1_join0 receipt_2_15_2359_1_join1 rfl rfl rfl
private theorem receipt_2_15_2359_1_join3 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 512 256 = 145710009774156316981458319360 :=
  phaseBlock_append receipt_2_15_2359_1_part4 receipt_2_15_2359_1_part5 rfl rfl rfl
private theorem receipt_2_15_2359_1_join4 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 768 256 = 111953155505610331418650425344 :=
  phaseBlock_append receipt_2_15_2359_1_part6 receipt_2_15_2359_1_part7 rfl rfl rfl
private theorem receipt_2_15_2359_1_join5 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 512 512 = 257663165279766648400108744704 :=
  phaseBlock_append receipt_2_15_2359_1_join3 receipt_2_15_2359_1_join4 rfl rfl rfl
private theorem receipt_2_15_2359_1_join6 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 0 1024 = 661190166256010471524180746240 :=
  phaseBlock_append receipt_2_15_2359_1_join2 receipt_2_15_2359_1_join5 rfl rfl rfl
private theorem receipt_2_15_2359_1_join7 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 1024 256 = 80757424522593926209701623808 :=
  phaseBlock_append receipt_2_15_2359_1_part8 receipt_2_15_2359_1_part9 rfl rfl rfl
private theorem receipt_2_15_2359_1_join8 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 1280 256 = 52007347929310190589672252732 :=
  phaseBlock_append receipt_2_15_2359_1_part10 receipt_2_15_2359_1_part11 rfl rfl rfl
private theorem receipt_2_15_2359_1_join9 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 1024 512 = 132764772451904116799373876540 :=
  phaseBlock_append receipt_2_15_2359_1_join7 receipt_2_15_2359_1_join8 rfl rfl rfl
private theorem receipt_2_15_2359_1_join10 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 1536 256 = 25589846410814038210031077260 :=
  phaseBlock_append receipt_2_15_2359_1_part12 receipt_2_15_2359_1_part13 rfl rfl rfl
private theorem receipt_2_15_2359_1_join11 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 1792 143 = 3623808086351466354756310182 :=
  phaseBlock_append receipt_2_15_2359_1_part14 receipt_2_15_2359_1_part15 rfl rfl rfl
private theorem receipt_2_15_2359_1_join12 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 1536 399 = 29213654497165504564787387442 :=
  phaseBlock_append receipt_2_15_2359_1_join10 receipt_2_15_2359_1_join11 rfl rfl rfl
private theorem receipt_2_15_2359_1_join13 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 1024 911 = 161978426949069621364161263982 :=
  phaseBlock_append receipt_2_15_2359_1_join9 receipt_2_15_2359_1_join12 rfl rfl rfl
private theorem receipt_2_15_2359_1_join14 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2379 76 1 0 7 1) 0 1935 = 823168593205080092888342010222 :=
  phaseBlock_append receipt_2_15_2359_1_join6 receipt_2_15_2359_1_join13 rfl rfl rfl

private theorem receipt_2_15_2359_1 : fastPhase (bank 2 15).shape 179808 2379 76 1 0 7 1 = 823168593205080092888342010222 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_15_2359_1_join14

private theorem receipt_2_15_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 0 128 = 115855580234991070149546517920 := by decide +kernel
private theorem receipt_2_15_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 128 128 = 105684421487065951637184869792 := by decide +kernel
private theorem receipt_2_15_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 256 128 = 95874702002184501072799090080 := by decide +kernel
private theorem receipt_2_15_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 384 128 = 86418747499953314808154428832 := by decide +kernel
private theorem receipt_2_15_2360_0_part4 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 512 128 = 77308960393227472594231223712 := by decide +kernel
private theorem receipt_2_15_2360_0_part5 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 640 128 = 68537819480006224874671289760 := by decide +kernel
private theorem receipt_2_15_2360_0_part6 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 768 128 = 60097879635328680079224309152 := by decide +kernel
private theorem receipt_2_15_2360_0_part7 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 896 128 = 51981771503169491917194220960 := by decide +kernel
private theorem receipt_2_15_2360_0_part8 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 1024 128 = 44182201188334546670885610912 := by decide +kernel
private theorem receipt_2_15_2360_0_part9 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 1152 128 = 36691949948356650489050101152 := by decide +kernel
private theorem receipt_2_15_2360_0_part10 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 1280 128 = 29503876478595068584792623152 := by decide +kernel
private theorem receipt_2_15_2360_0_part11 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 1408 128 = 22610921412794047394851648992 := by decide +kernel
private theorem receipt_2_15_2360_0_part12 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 1536 128 = 16006080997505504193304754878 := by decide +kernel
private theorem receipt_2_15_2360_0_part13 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 1664 128 = 9682419154241445087860308785 := by decide +kernel
private theorem receipt_2_15_2360_0_part14 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 1792 128 = 3633073649077594409978218719 := by decide +kernel
private theorem receipt_2_15_2360_0_part15 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 1920 15 = 42187193192374537549645662 := by decide +kernel
private theorem receipt_2_15_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 0 256 = 221540001722057021786731387712 :=
  phaseBlock_append receipt_2_15_2360_0_part0 receipt_2_15_2360_0_part1 rfl rfl rfl
private theorem receipt_2_15_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 256 256 = 182293449502137815880953518912 :=
  phaseBlock_append receipt_2_15_2360_0_part2 receipt_2_15_2360_0_part3 rfl rfl rfl
private theorem receipt_2_15_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 0 512 = 403833451224194837667684906624 :=
  phaseBlock_append receipt_2_15_2360_0_join0 receipt_2_15_2360_0_join1 rfl rfl rfl
private theorem receipt_2_15_2360_0_join3 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 512 256 = 145846779873233697468902513472 :=
  phaseBlock_append receipt_2_15_2360_0_part4 receipt_2_15_2360_0_part5 rfl rfl rfl
private theorem receipt_2_15_2360_0_join4 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 768 256 = 112079651138498171996418530112 :=
  phaseBlock_append receipt_2_15_2360_0_part6 receipt_2_15_2360_0_part7 rfl rfl rfl
private theorem receipt_2_15_2360_0_join5 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 512 512 = 257926431011731869465321043584 :=
  phaseBlock_append receipt_2_15_2360_0_join3 receipt_2_15_2360_0_join4 rfl rfl rfl
private theorem receipt_2_15_2360_0_join6 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 0 1024 = 661759882235926707133005950208 :=
  phaseBlock_append receipt_2_15_2360_0_join2 receipt_2_15_2360_0_join5 rfl rfl rfl
private theorem receipt_2_15_2360_0_join7 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 1024 256 = 80874151136691197159935712064 :=
  phaseBlock_append receipt_2_15_2360_0_part8 receipt_2_15_2360_0_part9 rfl rfl rfl
private theorem receipt_2_15_2360_0_join8 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 1280 256 = 52114797891389115979644272144 :=
  phaseBlock_append receipt_2_15_2360_0_part10 receipt_2_15_2360_0_part11 rfl rfl rfl
private theorem receipt_2_15_2360_0_join9 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 1024 512 = 132988949028080313139579984208 :=
  phaseBlock_append receipt_2_15_2360_0_join7 receipt_2_15_2360_0_join8 rfl rfl rfl
private theorem receipt_2_15_2360_0_join10 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 1536 256 = 25688500151746949281165063663 :=
  phaseBlock_append receipt_2_15_2360_0_part12 receipt_2_15_2360_0_part13 rfl rfl rfl
private theorem receipt_2_15_2360_0_join11 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 1792 143 = 3675260842269968947527864381 :=
  phaseBlock_append receipt_2_15_2360_0_part14 receipt_2_15_2360_0_part15 rfl rfl rfl
private theorem receipt_2_15_2360_0_join12 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 1536 399 = 29363760994016918228692928044 :=
  phaseBlock_append receipt_2_15_2360_0_join10 receipt_2_15_2360_0_join11 rfl rfl rfl
private theorem receipt_2_15_2360_0_join13 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 1024 911 = 162352710022097231368272912252 :=
  phaseBlock_append receipt_2_15_2360_0_join9 receipt_2_15_2360_0_join12 rfl rfl rfl
private theorem receipt_2_15_2360_0_join14 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 0) 0 1935 = 824112592258023938501278862460 :=
  phaseBlock_append receipt_2_15_2360_0_join6 receipt_2_15_2360_0_join13 rfl rfl rfl

private theorem receipt_2_15_2360_0 : fastPhase (bank 2 15).shape 179808 2380 76 1 0 7 0 = 824112592258023938501278862460 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_15_2360_0_join14

private theorem receipt_2_15_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 0 128 = 115775725142692558634881596000 := by decide +kernel
private theorem receipt_2_15_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 128 128 = 105607338654679357421817268832 := by decide +kernel
private theorem receipt_2_15_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 256 128 = 95800332865593237176566667872 := by decide +kernel
private theorem receipt_2_15_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 384 128 = 86347034081176131798555830880 := by decide +kernel
private theorem receipt_2_15_2360_1_part4 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 512 128 = 77239845298059478035667647072 := by decide +kernel
private theorem receipt_2_15_2360_1_part5 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 640 128 = 68471245895659902777688246880 := by decide +kernel
private theorem receipt_2_15_2360_1_part6 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 768 128 = 60033791328074910349753391712 := by decide +kernel
private theorem receipt_2_15_2360_1_part7 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 896 128 = 51920112815978569805794863712 := by decide +kernel
private theorem receipt_2_15_2360_1_part8 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 1024 128 = 44122917038517202221986855520 := by decide +kernel
private theorem receipt_2_15_2360_1_part9 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 1152 128 = 36634985825205067990192360032 := by decide +kernel
private theorem receipt_2_15_2360_1_part10 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 1280 128 = 29449178436272675889993945509 := by decide +kernel
private theorem receipt_2_15_2360_1_part11 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 1408 128 = 22558436046822437902286082307 := by decide +kernel
private theorem receipt_2_15_2360_1_part12 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 1536 128 = 15955755460388027126367390264 := by decide +kernel
private theorem receipt_2_15_2360_1_part13 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 1664 128 = 9634201161935282414335536480 := by decide +kernel
private theorem receipt_2_15_2360_1_part14 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 1792 128 = 3586911478644761530865463176 := by decide +kernel
private theorem receipt_2_15_2360_1_part15 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 1920 15 = 36909769047261720424610446 := by decide +kernel
private theorem receipt_2_15_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 0 256 = 221383063797371916056698864832 :=
  phaseBlock_append receipt_2_15_2360_1_part0 receipt_2_15_2360_1_part1 rfl rfl rfl
private theorem receipt_2_15_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 256 256 = 182147366946769368975122498752 :=
  phaseBlock_append receipt_2_15_2360_1_part2 receipt_2_15_2360_1_part3 rfl rfl rfl
private theorem receipt_2_15_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 0 512 = 403530430744141285031821363584 :=
  phaseBlock_append receipt_2_15_2360_1_join0 receipt_2_15_2360_1_join1 rfl rfl rfl
private theorem receipt_2_15_2360_1_join3 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 512 256 = 145711091193719380813355893952 :=
  phaseBlock_append receipt_2_15_2360_1_part4 receipt_2_15_2360_1_part5 rfl rfl rfl
private theorem receipt_2_15_2360_1_join4 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 768 256 = 111953904144053480155548255424 :=
  phaseBlock_append receipt_2_15_2360_1_part6 receipt_2_15_2360_1_part7 rfl rfl rfl
private theorem receipt_2_15_2360_1_join5 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 512 512 = 257664995337772860968904149376 :=
  phaseBlock_append receipt_2_15_2360_1_join3 receipt_2_15_2360_1_join4 rfl rfl rfl
private theorem receipt_2_15_2360_1_join6 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 0 1024 = 661195426081914146000725512960 :=
  phaseBlock_append receipt_2_15_2360_1_join2 receipt_2_15_2360_1_join5 rfl rfl rfl
private theorem receipt_2_15_2360_1_join7 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 1024 256 = 80757902863722270212179215552 :=
  phaseBlock_append receipt_2_15_2360_1_part8 receipt_2_15_2360_1_part9 rfl rfl rfl
private theorem receipt_2_15_2360_1_join8 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 1280 256 = 52007614483095113792280027816 :=
  phaseBlock_append receipt_2_15_2360_1_part10 receipt_2_15_2360_1_part11 rfl rfl rfl
private theorem receipt_2_15_2360_1_join9 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 1024 512 = 132765517346817384004459243368 :=
  phaseBlock_append receipt_2_15_2360_1_join7 receipt_2_15_2360_1_join8 rfl rfl rfl
private theorem receipt_2_15_2360_1_join10 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 1536 256 = 25589956622323309540702926744 :=
  phaseBlock_append receipt_2_15_2360_1_part12 receipt_2_15_2360_1_part13 rfl rfl rfl
private theorem receipt_2_15_2360_1_join11 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 1792 143 = 3623821247692023251290073622 :=
  phaseBlock_append receipt_2_15_2360_1_part14 receipt_2_15_2360_1_part15 rfl rfl rfl
private theorem receipt_2_15_2360_1_join12 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 1536 399 = 29213777870015332791993000366 :=
  phaseBlock_append receipt_2_15_2360_1_join10 receipt_2_15_2360_1_join11 rfl rfl rfl
private theorem receipt_2_15_2360_1_join13 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 1024 911 = 161979295216832716796452243734 :=
  phaseBlock_append receipt_2_15_2360_1_join9 receipt_2_15_2360_1_join12 rfl rfl rfl
private theorem receipt_2_15_2360_1_join14 :
    phaseBlock (fastLayer (bank 2 15).shape 179808 2380 76 1 0 7 1) 0 1935 = 823174721298746862797177756694 :=
  phaseBlock_append receipt_2_15_2360_1_join6 receipt_2_15_2360_1_join13 rfl rfl rfl

private theorem receipt_2_15_2360_1 : fastPhase (bank 2 15).shape 179808 2380 76 1 0 7 1 = 823174721298746862797177756694 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_15_2360_1_join14

theorem receipt_2_15 : Checked (bank 2 15) 76 0 7 := by
  refine checked_from_values (bank 2 15) 76 0 7
    (P3_7_1.checked (bank 2 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9204_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_15_2359_0 receipt_2_15_2359_1 receipt_2_15_2360_0 receipt_2_15_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_15_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 0 128 = 23173694000170944846955432416 := by decide +kernel
private theorem receipt_3_15_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 128 128 = 21236787805906234280538733024 := by decide +kernel
private theorem receipt_3_15_2359_0_part2 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 256 128 = 19353405192607518705738295776 := by decide +kernel
private theorem receipt_3_15_2359_0_part3 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 384 128 = 17524584968162641912286173664 := by decide +kernel
private theorem receipt_3_15_2359_0_part4 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 512 128 = 15751360086228335112107919840 := by decide +kernel
private theorem receipt_3_15_2359_0_part5 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 640 128 = 14034757655666973396803107296 := by decide +kernel
private theorem receipt_3_15_2359_0_part6 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 768 128 = 12375798949983332195125848544 := by decide +kernel
private theorem receipt_3_15_2359_0_part7 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 896 128 = 10775499416761343730465315296 := by decide +kernel
private theorem receipt_3_15_2359_0_part8 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 1024 128 = 9234868687100853478326258144 := by decide +kernel
private theorem receipt_3_15_2359_0_part9 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 1152 128 = 7754910585054376623809526240 := by decide +kernel
private theorem receipt_3_15_2359_0_part10 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 1280 128 = 6336623137063854519092586976 := by decide +kernel
private theorem receipt_3_15_2359_0_part11 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 1408 128 = 4980998581397411140910045664 := by decide +kernel
private theorem receipt_3_15_2359_0_part12 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 1536 128 = 3689023377586109548034165216 := by decide +kernel
private theorem receipt_3_15_2359_0_part13 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 1664 128 = 2461678215860708338755385824 := by decide +kernel
private theorem receipt_3_15_2359_0_part14 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 1792 128 = 1299938026588418108362844640 := by decide +kernel
private theorem receipt_3_15_2359_0_part15 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 1920 88 = 254363627154716100921519906 := by decide +kernel
private theorem receipt_3_15_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 0 256 = 44410481806077179127494165440 :=
  phaseBlock_append receipt_3_15_2359_0_part0 receipt_3_15_2359_0_part1 rfl rfl rfl
private theorem receipt_3_15_2359_0_join1 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 256 256 = 36877990160770160618024469440 :=
  phaseBlock_append receipt_3_15_2359_0_part2 receipt_3_15_2359_0_part3 rfl rfl rfl
private theorem receipt_3_15_2359_0_join2 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 0 512 = 81288471966847339745518634880 :=
  phaseBlock_append receipt_3_15_2359_0_join0 receipt_3_15_2359_0_join1 rfl rfl rfl
private theorem receipt_3_15_2359_0_join3 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 512 256 = 29786117741895308508911027136 :=
  phaseBlock_append receipt_3_15_2359_0_part4 receipt_3_15_2359_0_part5 rfl rfl rfl
private theorem receipt_3_15_2359_0_join4 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 768 256 = 23151298366744675925591163840 :=
  phaseBlock_append receipt_3_15_2359_0_part6 receipt_3_15_2359_0_part7 rfl rfl rfl
private theorem receipt_3_15_2359_0_join5 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 512 512 = 52937416108639984434502190976 :=
  phaseBlock_append receipt_3_15_2359_0_join3 receipt_3_15_2359_0_join4 rfl rfl rfl
private theorem receipt_3_15_2359_0_join6 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 0 1024 = 134225888075487324180020825856 :=
  phaseBlock_append receipt_3_15_2359_0_join2 receipt_3_15_2359_0_join5 rfl rfl rfl
private theorem receipt_3_15_2359_0_join7 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 1024 256 = 16989779272155230102135784384 :=
  phaseBlock_append receipt_3_15_2359_0_part8 receipt_3_15_2359_0_part9 rfl rfl rfl
private theorem receipt_3_15_2359_0_join8 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 1280 256 = 11317621718461265660002632640 :=
  phaseBlock_append receipt_3_15_2359_0_part10 receipt_3_15_2359_0_part11 rfl rfl rfl
private theorem receipt_3_15_2359_0_join9 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 1024 512 = 28307400990616495762138417024 :=
  phaseBlock_append receipt_3_15_2359_0_join7 receipt_3_15_2359_0_join8 rfl rfl rfl
private theorem receipt_3_15_2359_0_join10 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 1536 256 = 6150701593446817886789551040 :=
  phaseBlock_append receipt_3_15_2359_0_part12 receipt_3_15_2359_0_part13 rfl rfl rfl
private theorem receipt_3_15_2359_0_join11 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 1792 216 = 1554301653743134209284364546 :=
  phaseBlock_append receipt_3_15_2359_0_part14 receipt_3_15_2359_0_part15 rfl rfl rfl
private theorem receipt_3_15_2359_0_join12 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 1536 472 = 7705003247189952096073915586 :=
  phaseBlock_append receipt_3_15_2359_0_join10 receipt_3_15_2359_0_join11 rfl rfl rfl
private theorem receipt_3_15_2359_0_join13 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 1024 984 = 36012404237806447858212332610 :=
  phaseBlock_append receipt_3_15_2359_0_join9 receipt_3_15_2359_0_join12 rfl rfl rfl
private theorem receipt_3_15_2359_0_join14 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 0) 0 2008 = 170238292313293772038233158466 :=
  phaseBlock_append receipt_3_15_2359_0_join6 receipt_3_15_2359_0_join13 rfl rfl rfl

private theorem receipt_3_15_2359_0 : fastPhase (bank 3 15).shape 179808 2379 76 1 1 1 0 = 170238292313293772038233158466 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_15_2359_0_join14

private theorem receipt_3_15_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 0 128 = 23158561926487465872311454624 := by decide +kernel
private theorem receipt_3_15_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 128 128 = 21222051597858835803744050080 := by decide +kernel
private theorem receipt_3_15_2359_1_part2 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 256 128 = 19339073670641268076130216864 := by decide +kernel
private theorem receipt_3_15_2359_1_part3 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 384 128 = 17510666904537174130986531744 := by decide +kernel
private theorem receipt_3_15_2359_1_part4 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 512 128 = 15737864205094520197279927200 := by decide +kernel
private theorem receipt_3_15_2359_1_part5 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 640 128 = 14021692633143583748908211104 := by decide +kernel
private theorem receipt_3_15_2359_1_part6 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 768 128 = 12363173414233709962180586400 := by decide +kernel
private theorem receipt_3_15_2359_1_part7 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 896 128 = 10763321948070068173298170784 := by decide +kernel
private theorem receipt_3_15_2359_1_part8 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 1024 128 = 9223147817950408335834516384 := by decide +kernel
private theorem receipt_3_15_2359_1_part9 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 1152 128 = 7743654800201817478216129440 := by decide +kernel
private theorem receipt_3_15_2359_1_part10 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 1280 128 = 6325840873617476161202989984 := by decide +kernel
private theorem receipt_3_15_2359_1_part11 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 1408 128 = 4970698228893414935369071520 := by decide +kernel
private theorem receipt_3_15_2359_1_part12 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 1536 128 = 3679213278065270798582860704 := by decide +kernel
private theorem receipt_3_15_2359_1_part13 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 1664 128 = 2452366663945043653487877024 := by decide +kernel
private theorem receipt_3_15_2359_1_part14 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 1792 128 = 1291133269557852764983192480 := by decide +kernel
private theorem receipt_3_15_2359_1_part15 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 1920 88 = 248608600404254862295181702 := by decide +kernel
private theorem receipt_3_15_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 0 256 = 44380613524346301676055504704 :=
  phaseBlock_append receipt_3_15_2359_1_part0 receipt_3_15_2359_1_part1 rfl rfl rfl
private theorem receipt_3_15_2359_1_join1 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 256 256 = 36849740575178442207116748608 :=
  phaseBlock_append receipt_3_15_2359_1_part2 receipt_3_15_2359_1_part3 rfl rfl rfl
private theorem receipt_3_15_2359_1_join2 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 0 512 = 81230354099524743883172253312 :=
  phaseBlock_append receipt_3_15_2359_1_join0 receipt_3_15_2359_1_join1 rfl rfl rfl
private theorem receipt_3_15_2359_1_join3 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 512 256 = 29759556838238103946188138304 :=
  phaseBlock_append receipt_3_15_2359_1_part4 receipt_3_15_2359_1_part5 rfl rfl rfl
private theorem receipt_3_15_2359_1_join4 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 768 256 = 23126495362303778135478757184 :=
  phaseBlock_append receipt_3_15_2359_1_part6 receipt_3_15_2359_1_part7 rfl rfl rfl
private theorem receipt_3_15_2359_1_join5 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 512 512 = 52886052200541882081666895488 :=
  phaseBlock_append receipt_3_15_2359_1_join3 receipt_3_15_2359_1_join4 rfl rfl rfl
private theorem receipt_3_15_2359_1_join6 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 0 1024 = 134116406300066625964839148800 :=
  phaseBlock_append receipt_3_15_2359_1_join2 receipt_3_15_2359_1_join5 rfl rfl rfl
private theorem receipt_3_15_2359_1_join7 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 1024 256 = 16966802618152225814050645824 :=
  phaseBlock_append receipt_3_15_2359_1_part8 receipt_3_15_2359_1_part9 rfl rfl rfl
private theorem receipt_3_15_2359_1_join8 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 1280 256 = 11296539102510891096572061504 :=
  phaseBlock_append receipt_3_15_2359_1_part10 receipt_3_15_2359_1_part11 rfl rfl rfl
private theorem receipt_3_15_2359_1_join9 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 1024 512 = 28263341720663116910622707328 :=
  phaseBlock_append receipt_3_15_2359_1_join7 receipt_3_15_2359_1_join8 rfl rfl rfl
private theorem receipt_3_15_2359_1_join10 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 1536 256 = 6131579942010314452070737728 :=
  phaseBlock_append receipt_3_15_2359_1_part12 receipt_3_15_2359_1_part13 rfl rfl rfl
private theorem receipt_3_15_2359_1_join11 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 1792 216 = 1539741869962107627278374182 :=
  phaseBlock_append receipt_3_15_2359_1_part14 receipt_3_15_2359_1_part15 rfl rfl rfl
private theorem receipt_3_15_2359_1_join12 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 1536 472 = 7671321811972422079349111910 :=
  phaseBlock_append receipt_3_15_2359_1_join10 receipt_3_15_2359_1_join11 rfl rfl rfl
private theorem receipt_3_15_2359_1_join13 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 1024 984 = 35934663532635538989971819238 :=
  phaseBlock_append receipt_3_15_2359_1_join9 receipt_3_15_2359_1_join12 rfl rfl rfl
private theorem receipt_3_15_2359_1_join14 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2379 76 1 1 1 1) 0 2008 = 170051069832702164954810968038 :=
  phaseBlock_append receipt_3_15_2359_1_join6 receipt_3_15_2359_1_join13 rfl rfl rfl

private theorem receipt_3_15_2359_1 : fastPhase (bank 3 15).shape 179808 2379 76 1 1 1 1 = 170051069832702164954810968038 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_15_2359_1_join14

private theorem receipt_3_15_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 0 128 = 23173900356530412660580944352 := by decide +kernel
private theorem receipt_3_15_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 128 128 = 21236964569412062448923032032 := by decide +kernel
private theorem receipt_3_15_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 256 128 = 19353555158906598314542590432 := by decide +kernel
private theorem receipt_3_15_2360_0_part3 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 384 128 = 17524710808549019877345401312 := by decide +kernel
private theorem receipt_3_15_2360_0_part4 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 512 128 = 15751464348222458345419885024 := by decide +kernel
private theorem receipt_3_15_2360_0_part5 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 640 128 = 14034842763594053363215399392 := by decide +kernel
private theorem receipt_3_15_2360_0_part6 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 768 128 = 12375867205550829859720538592 := by decide +kernel
private theorem receipt_3_15_2360_0_part7 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 896 128 = 10775552999635574896641432032 := by decide +kernel
private theorem receipt_3_15_2360_0_part8 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 1024 128 = 9234909655482714516580043232 := by decide +kernel
private theorem receipt_3_15_2360_0_part9 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 1152 128 = 7754940876254190591212468704 := by decide +kernel
private theorem receipt_3_15_2360_0_part10 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 1280 128 = 6336644568075337669467236832 := by decide +kernel
private theorem receipt_3_15_2360_0_part11 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 1408 128 = 4981012849470759825703606752 := by decide +kernel
private theorem receipt_3_15_2360_0_part12 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 1536 128 = 3689032060800207507889867232 := by decide +kernel
private theorem receipt_3_15_2360_0_part13 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 1664 128 = 2461682773694454385781635552 := by decide +kernel
private theorem receipt_3_15_2360_0_part14 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 1792 128 = 1299939800491174199100156384 := by decide +kernel
private theorem receipt_3_15_2360_0_part15 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 1920 88 = 254363872617141559265135010 := by decide +kernel
private theorem receipt_3_15_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 0 256 = 44410864925942475109503976384 :=
  phaseBlock_append receipt_3_15_2360_0_part0 receipt_3_15_2360_0_part1 rfl rfl rfl
private theorem receipt_3_15_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 256 256 = 36878265967455618191887991744 :=
  phaseBlock_append receipt_3_15_2360_0_part2 receipt_3_15_2360_0_part3 rfl rfl rfl
private theorem receipt_3_15_2360_0_join2 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 0 512 = 81289130893398093301391968128 :=
  phaseBlock_append receipt_3_15_2360_0_join0 receipt_3_15_2360_0_join1 rfl rfl rfl
private theorem receipt_3_15_2360_0_join3 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 512 256 = 29786307111816511708635284416 :=
  phaseBlock_append receipt_3_15_2360_0_part4 receipt_3_15_2360_0_part5 rfl rfl rfl
private theorem receipt_3_15_2360_0_join4 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 768 256 = 23151420205186404756361970624 :=
  phaseBlock_append receipt_3_15_2360_0_part6 receipt_3_15_2360_0_part7 rfl rfl rfl
private theorem receipt_3_15_2360_0_join5 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 512 512 = 52937727317002916464997255040 :=
  phaseBlock_append receipt_3_15_2360_0_join3 receipt_3_15_2360_0_join4 rfl rfl rfl
private theorem receipt_3_15_2360_0_join6 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 0 1024 = 134226858210401009766389223168 :=
  phaseBlock_append receipt_3_15_2360_0_join2 receipt_3_15_2360_0_join5 rfl rfl rfl
private theorem receipt_3_15_2360_0_join7 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 1024 256 = 16989850531736905107792511936 :=
  phaseBlock_append receipt_3_15_2360_0_part8 receipt_3_15_2360_0_part9 rfl rfl rfl
private theorem receipt_3_15_2360_0_join8 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 1280 256 = 11317657417546097495170843584 :=
  phaseBlock_append receipt_3_15_2360_0_part10 receipt_3_15_2360_0_part11 rfl rfl rfl
private theorem receipt_3_15_2360_0_join9 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 1024 512 = 28307507949283002602963355520 :=
  phaseBlock_append receipt_3_15_2360_0_join7 receipt_3_15_2360_0_join8 rfl rfl rfl
private theorem receipt_3_15_2360_0_join10 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 1536 256 = 6150714834494661893671502784 :=
  phaseBlock_append receipt_3_15_2360_0_part12 receipt_3_15_2360_0_part13 rfl rfl rfl
private theorem receipt_3_15_2360_0_join11 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 1792 216 = 1554303673108315758365291394 :=
  phaseBlock_append receipt_3_15_2360_0_part14 receipt_3_15_2360_0_part15 rfl rfl rfl
private theorem receipt_3_15_2360_0_join12 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 1536 472 = 7705018507602977652036794178 :=
  phaseBlock_append receipt_3_15_2360_0_join10 receipt_3_15_2360_0_join11 rfl rfl rfl
private theorem receipt_3_15_2360_0_join13 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 1024 984 = 36012526456885980255000149698 :=
  phaseBlock_append receipt_3_15_2360_0_join9 receipt_3_15_2360_0_join12 rfl rfl rfl
private theorem receipt_3_15_2360_0_join14 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 0) 0 2008 = 170239384667286990021389372866 :=
  phaseBlock_append receipt_3_15_2360_0_join6 receipt_3_15_2360_0_join13 rfl rfl rfl

private theorem receipt_3_15_2360_0 : fastPhase (bank 3 15).shape 179808 2380 76 1 1 1 0 = 170239384667286990021389372866 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_15_2360_0_join14

private theorem receipt_3_15_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 0 128 = 23158768126567936716555031392 := by decide +kernel
private theorem receipt_3_15_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 128 128 = 21222228219740452438664266592 := by decide +kernel
private theorem receipt_3_15_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 256 128 = 19339223509283861605505659744 := by decide +kernel
private theorem receipt_3_15_2360_1_part3 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 384 128 = 17510792630551246086814507872 := by decide +kernel
private theorem receipt_3_15_2360_1_part4 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 512 128 = 15737968365320481070768509792 := by decide +kernel
private theorem receipt_3_15_2360_1_part5 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 640 128 = 14021777651230111912166064992 := by decide +kernel
private theorem receipt_3_15_2360_1_part6 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 768 128 = 12363241591215230980604572512 := by decide +kernel
private theorem receipt_3_15_2360_1_part7 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 896 128 = 10763375462943354508658729824 := by decide +kernel
private theorem receipt_3_15_2360_1_part8 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 1024 128 = 9223188728250299440058831712 := by decide +kernel
private theorem receipt_3_15_2360_1_part9 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 1152 128 = 7743685042576060277869069152 := by decide +kernel
private theorem receipt_3_15_2360_1_part10 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 1280 128 = 6325862264400685932665828192 := by decide +kernel
private theorem receipt_3_15_2360_1_part11 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 1408 128 = 4970712464680156570715988832 := by decide +kernel
private theorem receipt_3_15_2360_1_part12 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 1536 128 = 3679221936282260462155223904 := by decide +kernel
private theorem receipt_3_15_2360_1_part13 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 1664 128 = 2452371203422470829166297952 := by decide +kernel
private theorem receipt_3_15_2360_1_part14 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 1792 128 = 1291135031099822694157366112 := by decide +kernel
private theorem receipt_3_15_2360_1_part15 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 1920 88 = 248608840512858874946313130 := by decide +kernel
private theorem receipt_3_15_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 0 256 = 44380996346308389155219297984 :=
  phaseBlock_append receipt_3_15_2360_1_part0 receipt_3_15_2360_1_part1 rfl rfl rfl
private theorem receipt_3_15_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 256 256 = 36850016139835107692320167616 :=
  phaseBlock_append receipt_3_15_2360_1_part2 receipt_3_15_2360_1_part3 rfl rfl rfl
private theorem receipt_3_15_2360_1_join2 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 0 512 = 81231012486143496847539465600 :=
  phaseBlock_append receipt_3_15_2360_1_join0 receipt_3_15_2360_1_join1 rfl rfl rfl
private theorem receipt_3_15_2360_1_join3 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 512 256 = 29759746016550592982934574784 :=
  phaseBlock_append receipt_3_15_2360_1_part4 receipt_3_15_2360_1_part5 rfl rfl rfl
private theorem receipt_3_15_2360_1_join4 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 768 256 = 23126617054158585489263302336 :=
  phaseBlock_append receipt_3_15_2360_1_part6 receipt_3_15_2360_1_part7 rfl rfl rfl
private theorem receipt_3_15_2360_1_join5 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 512 512 = 52886363070709178472197877120 :=
  phaseBlock_append receipt_3_15_2360_1_join3 receipt_3_15_2360_1_join4 rfl rfl rfl
private theorem receipt_3_15_2360_1_join6 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 0 1024 = 134117375556852675319737342720 :=
  phaseBlock_append receipt_3_15_2360_1_join2 receipt_3_15_2360_1_join5 rfl rfl rfl
private theorem receipt_3_15_2360_1_join7 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 1024 256 = 16966873770826359717927900864 :=
  phaseBlock_append receipt_3_15_2360_1_part8 receipt_3_15_2360_1_part9 rfl rfl rfl
private theorem receipt_3_15_2360_1_join8 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 1280 256 = 11296574729080842503381817024 :=
  phaseBlock_append receipt_3_15_2360_1_part10 receipt_3_15_2360_1_part11 rfl rfl rfl
private theorem receipt_3_15_2360_1_join9 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 1024 512 = 28263448499907202221309717888 :=
  phaseBlock_append receipt_3_15_2360_1_join7 receipt_3_15_2360_1_join8 rfl rfl rfl
private theorem receipt_3_15_2360_1_join10 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 1536 256 = 6131593139704731291321521856 :=
  phaseBlock_append receipt_3_15_2360_1_part12 receipt_3_15_2360_1_part13 rfl rfl rfl
private theorem receipt_3_15_2360_1_join11 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 1792 216 = 1539743871612681569103679242 :=
  phaseBlock_append receipt_3_15_2360_1_part14 receipt_3_15_2360_1_part15 rfl rfl rfl
private theorem receipt_3_15_2360_1_join12 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 1536 472 = 7671337011317412860425201098 :=
  phaseBlock_append receipt_3_15_2360_1_join10 receipt_3_15_2360_1_join11 rfl rfl rfl
private theorem receipt_3_15_2360_1_join13 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 1024 984 = 35934785511224615081734918986 :=
  phaseBlock_append receipt_3_15_2360_1_join9 receipt_3_15_2360_1_join12 rfl rfl rfl
private theorem receipt_3_15_2360_1_join14 :
    phaseBlock (fastLayer (bank 3 15).shape 179808 2380 76 1 1 1 1) 0 2008 = 170052161068077290401472261706 :=
  phaseBlock_append receipt_3_15_2360_1_join6 receipt_3_15_2360_1_join13 rfl rfl rfl

private theorem receipt_3_15_2360_1 : fastPhase (bank 3 15).shape 179808 2380 76 1 1 1 1 = 170052161068077290401472261706 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_15_2360_1_join14

theorem receipt_3_15 : Checked (bank 3 15) 76 1 1 := by
  refine checked_from_values (bank 3 15) 76 1 1
    (P3_7_1.checked (bank 3 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9204_2007)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_15_2359_0 receipt_3_15_2359_1 receipt_3_15_2360_0 receipt_3_15_2360_1 (by decide +kernel) (by decide +kernel)

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
    (word : K1.I → K1_14.L) (lo : 2379 ≤ h) (hi : h ≤ 33599) (rect : Fin 4)
    (i : Fin 1) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group6_stage i)).shape
      (cutoff h rect (group6_stage i)), ¬ G∣Q :=
  (group6_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group6_avoids

end Lower6960.RescueSource
