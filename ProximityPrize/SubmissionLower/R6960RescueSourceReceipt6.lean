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
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 0 128 = 221636160047699758441837735104 := by decide +kernel
private theorem receipt_0_15_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 128 128 = 202874573363247523422521461952 := by decide +kernel
private theorem receipt_0_15_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 256 128 = 184678685906188021250830396608 := by decide +kernel
private theorem receipt_0_15_2359_0_part3 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 384 128 = 167039786475496056137379859648 := by decide +kernel
private theorem receipt_0_15_2359_0_part4 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 512 128 = 149949176852219545235297086656 := by decide +kernel
private theorem receipt_0_15_2359_0_part5 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 640 128 = 133398171793196293472597609664 := by decide +kernel
private theorem receipt_0_15_2359_0_part6 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 768 128 = 117378099024770768384561638592 := by decide +kernel
private theorem receipt_0_15_2359_0_part7 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 896 128 = 101880299236510874946110442688 := by decide +kernel
private theorem receipt_0_15_2359_0_part8 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 1024 128 = 86896126074924730404182731968 := by decide +kernel
private theorem receipt_0_15_2359_0_part9 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 1152 128 = 72416946137177439110111038656 := by decide +kernel
private theorem receipt_0_15_2359_0_part10 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 1280 128 = 58434146277240922778013006785 := by decide +kernel
private theorem receipt_0_15_2359_0_part11 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 1408 128 = 44939137571483742318786132732 := by decide +kernel
private theorem receipt_0_15_2359_0_part12 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 1536 128 = 31923305233629042905594482210 := by decide +kernel
private theorem receipt_0_15_2359_0_part13 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 1664 128 = 19378038480796935263474030265 := by decide +kernel
private theorem receipt_0_15_2359_0_part14 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 1792 128 = 7294739482547491401308315382 := by decide +kernel
private theorem receipt_0_15_2359_0_part15 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 1920 15 = 84909508799909467538574168 := by decide +kernel
private theorem receipt_0_15_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 0 256 = 424510733410947281864359197056 :=
  phaseBlock_append receipt_0_15_2359_0_part0 receipt_0_15_2359_0_part1 rfl rfl rfl
private theorem receipt_0_15_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 256 256 = 351718472381684077388210256256 :=
  phaseBlock_append receipt_0_15_2359_0_part2 receipt_0_15_2359_0_part3 rfl rfl rfl
private theorem receipt_0_15_2359_0_join2 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 0 512 = 776229205792631359252569453312 :=
  phaseBlock_append receipt_0_15_2359_0_join0 receipt_0_15_2359_0_join1 rfl rfl rfl
private theorem receipt_0_15_2359_0_join3 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 512 256 = 283347348645415838707894696320 :=
  phaseBlock_append receipt_0_15_2359_0_part4 receipt_0_15_2359_0_part5 rfl rfl rfl
private theorem receipt_0_15_2359_0_join4 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 768 256 = 219258398261281643330672081280 :=
  phaseBlock_append receipt_0_15_2359_0_part6 receipt_0_15_2359_0_part7 rfl rfl rfl
private theorem receipt_0_15_2359_0_join5 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 512 512 = 502605746906697482038566777600 :=
  phaseBlock_append receipt_0_15_2359_0_join3 receipt_0_15_2359_0_join4 rfl rfl rfl
private theorem receipt_0_15_2359_0_join6 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 0 1024 = 1278834952699328841291136230912 :=
  phaseBlock_append receipt_0_15_2359_0_join2 receipt_0_15_2359_0_join5 rfl rfl rfl
private theorem receipt_0_15_2359_0_join7 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 1024 256 = 159313072212102169514293770624 :=
  phaseBlock_append receipt_0_15_2359_0_part8 receipt_0_15_2359_0_part9 rfl rfl rfl
private theorem receipt_0_15_2359_0_join8 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 1280 256 = 103373283848724665096799139517 :=
  phaseBlock_append receipt_0_15_2359_0_part10 receipt_0_15_2359_0_part11 rfl rfl rfl
private theorem receipt_0_15_2359_0_join9 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 1024 512 = 262686356060826834611092910141 :=
  phaseBlock_append receipt_0_15_2359_0_join7 receipt_0_15_2359_0_join8 rfl rfl rfl
private theorem receipt_0_15_2359_0_join10 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 1536 256 = 51301343714425978169068512475 :=
  phaseBlock_append receipt_0_15_2359_0_part12 receipt_0_15_2359_0_part13 rfl rfl rfl
private theorem receipt_0_15_2359_0_join11 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 1792 143 = 7379648991347400868846889550 :=
  phaseBlock_append receipt_0_15_2359_0_part14 receipt_0_15_2359_0_part15 rfl rfl rfl
private theorem receipt_0_15_2359_0_join12 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 1536 399 = 58680992705773379037915402025 :=
  phaseBlock_append receipt_0_15_2359_0_join10 receipt_0_15_2359_0_join11 rfl rfl rfl
private theorem receipt_0_15_2359_0_join13 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 1024 911 = 321367348766600213649008312166 :=
  phaseBlock_append receipt_0_15_2359_0_join9 receipt_0_15_2359_0_join12 rfl rfl rfl
private theorem receipt_0_15_2359_0_join14 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 0) 0 1935 = 1600202301465929054940144543078 :=
  phaseBlock_append receipt_0_15_2359_0_join6 receipt_0_15_2359_0_join13 rfl rfl rfl

private theorem receipt_0_15_2359_0 : fastPhase (bank 0 15).shape 179818 2359 76 1 0 1 0 = 1600202301465929054940144543078 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_15_2359_0_join14

private theorem receipt_0_15_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 0 128 = 221489319313890396175190206848 := by decide +kernel
private theorem receipt_0_15_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 128 128 = 202732037705399367902109182336 := by decide +kernel
private theorem receipt_0_15_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 256 128 = 184540389413128043392336537984 := by decide +kernel
private theorem receipt_0_15_2359_1_part3 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 384 128 = 166905663335000872801178954112 := by decide +kernel
private theorem receipt_0_15_2359_1_part4 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 512 128 = 149819161350967304185306687872 := by decide +kernel
private theorem receipt_0_15_2359_1_part5 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 640 128 = 133272198316718558335129954688 := by decide +kernel
private theorem receipt_0_15_2359_1_part6 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 768 128 = 117256102057404403607175309696 := by decide +kernel
private theorem receipt_0_15_2359_1_part7 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 896 128 = 101762213361349930756462029184 := by decide +kernel
private theorem receipt_0_15_2359_1_part8 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 1024 128 = 86781885973772327768878492032 := by decide +kernel
private theorem receipt_0_15_2359_1_part9 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 1152 128 = 72306486590497654693558561152 := by decide +kernel
private theorem receipt_0_15_2359_1_part10 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 1280 128 = 58327402151003061018877059686 := by decide +kernel
private theorem receipt_0_15_2359_1_part11 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 1408 128 = 44836043779279747507382075785 := by decide +kernel
private theorem receipt_0_15_2359_1_part12 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 1536 128 = 31823796775815875290655913540 := by decide +kernel
private theorem receipt_0_15_2359_1_part13 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 1664 128 = 19282050456360793296890921259 := by decide +kernel
private theorem receipt_0_15_2359_1_part14 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 1792 128 = 7202207089050010894173280358 := by decide +kernel
private theorem receipt_0_15_2359_1_part15 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 1920 15 = 74289085103906323624897462 := by decide +kernel
private theorem receipt_0_15_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 0 256 = 424221357019289764077299389184 :=
  phaseBlock_append receipt_0_15_2359_1_part0 receipt_0_15_2359_1_part1 rfl rfl rfl
private theorem receipt_0_15_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 256 256 = 351446052748128916193515492096 :=
  phaseBlock_append receipt_0_15_2359_1_part2 receipt_0_15_2359_1_part3 rfl rfl rfl
private theorem receipt_0_15_2359_1_join2 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 0 512 = 775667409767418680270814881280 :=
  phaseBlock_append receipt_0_15_2359_1_join0 receipt_0_15_2359_1_join1 rfl rfl rfl
private theorem receipt_0_15_2359_1_join3 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 512 256 = 283091359667685862520436642560 :=
  phaseBlock_append receipt_0_15_2359_1_part4 receipt_0_15_2359_1_part5 rfl rfl rfl
private theorem receipt_0_15_2359_1_join4 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 768 256 = 219018315418754334363637338880 :=
  phaseBlock_append receipt_0_15_2359_1_part6 receipt_0_15_2359_1_part7 rfl rfl rfl
private theorem receipt_0_15_2359_1_join5 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 512 512 = 502109675086440196884073981440 :=
  phaseBlock_append receipt_0_15_2359_1_join3 receipt_0_15_2359_1_join4 rfl rfl rfl
private theorem receipt_0_15_2359_1_join6 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 0 1024 = 1277777084853858877154888862720 :=
  phaseBlock_append receipt_0_15_2359_1_join2 receipt_0_15_2359_1_join5 rfl rfl rfl
private theorem receipt_0_15_2359_1_join7 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 1024 256 = 159088372564269982462437053184 :=
  phaseBlock_append receipt_0_15_2359_1_part8 receipt_0_15_2359_1_part9 rfl rfl rfl
private theorem receipt_0_15_2359_1_join8 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 1280 256 = 103163445930282808526259135471 :=
  phaseBlock_append receipt_0_15_2359_1_part10 receipt_0_15_2359_1_part11 rfl rfl rfl
private theorem receipt_0_15_2359_1_join9 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 1024 512 = 262251818494552790988696188655 :=
  phaseBlock_append receipt_0_15_2359_1_join7 receipt_0_15_2359_1_join8 rfl rfl rfl
private theorem receipt_0_15_2359_1_join10 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 1536 256 = 51105847232176668587546834799 :=
  phaseBlock_append receipt_0_15_2359_1_part12 receipt_0_15_2359_1_part13 rfl rfl rfl
private theorem receipt_0_15_2359_1_join11 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 1792 143 = 7276496174153917217798177820 :=
  phaseBlock_append receipt_0_15_2359_1_part14 receipt_0_15_2359_1_part15 rfl rfl rfl
private theorem receipt_0_15_2359_1_join12 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 1536 399 = 58382343406330585805345012619 :=
  phaseBlock_append receipt_0_15_2359_1_join10 receipt_0_15_2359_1_join11 rfl rfl rfl
private theorem receipt_0_15_2359_1_join13 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 1024 911 = 320634161900883376794041201274 :=
  phaseBlock_append receipt_0_15_2359_1_join9 receipt_0_15_2359_1_join12 rfl rfl rfl
private theorem receipt_0_15_2359_1_join14 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2359 76 1 0 1 1) 0 1935 = 1598411246754742253948930063994 :=
  phaseBlock_append receipt_0_15_2359_1_join6 receipt_0_15_2359_1_join13 rfl rfl rfl

private theorem receipt_0_15_2359_1 : fastPhase (bank 0 15).shape 179818 2359 76 1 0 1 1 = 1598411246754742253948930063994 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_15_2359_1_join14

private theorem receipt_0_15_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 0 128 = 221638146697489457646120953088 := by decide +kernel
private theorem receipt_0_15_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 128 128 = 202876324317263608816336618752 := by decide +kernel
private theorem receipt_0_15_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 256 128 = 184680217085113317922217403648 := by decide +kernel
private theorem receipt_0_15_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 384 128 = 167041113499435615531526030592 := by decide +kernel
private theorem receipt_0_15_2360_0_part4 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 512 128 = 149950315041153336391162717440 := by decide +kernel
private theorem receipt_0_15_2360_0_part5 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 640 128 = 133399136167431674357216003328 := by decide +kernel
private theorem receipt_0_15_2360_0_part6 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 768 128 = 117378904305394737325013574912 := by decide +kernel
private theorem receipt_0_15_2360_0_part7 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 896 128 = 101880959845842102159173092608 := by decide +kernel
private theorem receipt_0_15_2360_0_part8 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 1024 128 = 86896656136965369623653016832 := by decide +kernel
private theorem receipt_0_15_2360_0_part9 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 1152 128 = 72417359478064719311803434240 := by decide +kernel
private theorem receipt_0_15_2360_0_part10 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 1280 128 = 58434456195400300409944262769 := by decide +kernel
private theorem receipt_0_15_2360_0_part11 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 1408 128 = 44939357231888445917515925616 := by decide +kernel
private theorem receipt_0_15_2360_0_part12 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 1536 128 = 31923447784130313328279389951 := by decide +kernel
private theorem receipt_0_15_2360_0_part13 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 1664 128 = 19378116752609110699768216077 := by decide +kernel
private theorem receipt_0_15_2360_0_part14 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 1792 128 = 7294765981940125167950600121 := by decide +kernel
private theorem receipt_0_15_2360_0_part15 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 1920 15 = 84909791392078995208158192 := by decide +kernel
private theorem receipt_0_15_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 0 256 = 424514471014753066462457571840 :=
  phaseBlock_append receipt_0_15_2360_0_part0 receipt_0_15_2360_0_part1 rfl rfl rfl
private theorem receipt_0_15_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 256 256 = 351721330584548933453743434240 :=
  phaseBlock_append receipt_0_15_2360_0_part2 receipt_0_15_2360_0_part3 rfl rfl rfl
private theorem receipt_0_15_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 0 512 = 776235801599301999916201006080 :=
  phaseBlock_append receipt_0_15_2360_0_join0 receipt_0_15_2360_0_join1 rfl rfl rfl
private theorem receipt_0_15_2360_0_join3 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 512 256 = 283349451208585010748378720768 :=
  phaseBlock_append receipt_0_15_2360_0_part4 receipt_0_15_2360_0_part5 rfl rfl rfl
private theorem receipt_0_15_2360_0_join4 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 768 256 = 219259864151236839484186667520 :=
  phaseBlock_append receipt_0_15_2360_0_part6 receipt_0_15_2360_0_part7 rfl rfl rfl
private theorem receipt_0_15_2360_0_join5 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 512 512 = 502609315359821850232565388288 :=
  phaseBlock_append receipt_0_15_2360_0_join3 receipt_0_15_2360_0_join4 rfl rfl rfl
private theorem receipt_0_15_2360_0_join6 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 0 1024 = 1278845116959123850148766394368 :=
  phaseBlock_append receipt_0_15_2360_0_join2 receipt_0_15_2360_0_join5 rfl rfl rfl
private theorem receipt_0_15_2360_0_join7 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 1024 256 = 159314015615030088935456451072 :=
  phaseBlock_append receipt_0_15_2360_0_part8 receipt_0_15_2360_0_part9 rfl rfl rfl
private theorem receipt_0_15_2360_0_join8 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 1280 256 = 103373813427288746327460188385 :=
  phaseBlock_append receipt_0_15_2360_0_part10 receipt_0_15_2360_0_part11 rfl rfl rfl
private theorem receipt_0_15_2360_0_join9 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 1024 512 = 262687829042318835262916639457 :=
  phaseBlock_append receipt_0_15_2360_0_join7 receipt_0_15_2360_0_join8 rfl rfl rfl
private theorem receipt_0_15_2360_0_join10 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 1536 256 = 51301564536739424028047606028 :=
  phaseBlock_append receipt_0_15_2360_0_part12 receipt_0_15_2360_0_part13 rfl rfl rfl
private theorem receipt_0_15_2360_0_join11 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 1792 143 = 7379675773332204163158758313 :=
  phaseBlock_append receipt_0_15_2360_0_part14 receipt_0_15_2360_0_part15 rfl rfl rfl
private theorem receipt_0_15_2360_0_join12 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 1536 399 = 58681240310071628191206364341 :=
  phaseBlock_append receipt_0_15_2360_0_join10 receipt_0_15_2360_0_join11 rfl rfl rfl
private theorem receipt_0_15_2360_0_join13 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 1024 911 = 321369069352390463454123003798 :=
  phaseBlock_append receipt_0_15_2360_0_join9 receipt_0_15_2360_0_join12 rfl rfl rfl
private theorem receipt_0_15_2360_0_join14 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 0) 0 1935 = 1600214186311514313602889398166 :=
  phaseBlock_append receipt_0_15_2360_0_join6 receipt_0_15_2360_0_join13 rfl rfl rfl

private theorem receipt_0_15_2360_0 : fastPhase (bank 0 15).shape 179818 2360 76 1 0 1 0 = 1600214186311514313602889398166 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_15_2360_0_join14

private theorem receipt_0_15_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 0 128 = 221491304886070670044416452928 := by decide +kernel
private theorem receipt_0_15_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 128 128 = 202733787644510197351362906432 := by decide +kernel
private theorem receipt_0_15_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 256 128 = 184541919638432890021359216960 := by decide +kernel
private theorem receipt_0_15_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 384 128 = 166906989465187903505481730368 := by decide +kernel
private theorem receipt_0_15_2360_1_part4 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 512 128 = 149820298704602081087125891392 := by decide +kernel
private theorem receipt_0_15_2360_1_part5 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 640 128 = 133273161912696508812057069888 := by decide +kernel
private theorem receipt_0_15_2360_1_part6 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 768 128 = 117256906615403070418461387072 := by decide +kernel
private theorem receipt_0_15_2360_1_part7 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 896 128 = 101762873302281002266996541760 := by decide +kernel
private theorem receipt_0_15_2360_1_part8 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 1024 128 = 86782415420233448270842636608 := by decide +kernel
private theorem receipt_0_15_2360_1_part9 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 1152 128 = 72306899367224014825753004352 := by decide +kernel
private theorem receipt_0_15_2360_1_part10 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 1280 128 = 58327711555425310901215644174 := by decide +kernel
private theorem receipt_0_15_2360_1_part11 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 1408 128 = 44836262975320504031461171365 := by decide +kernel
private theorem receipt_0_15_2360_1_part12 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 1536 128 = 31823938909871013923806814607 := by decide +kernel
private theorem receipt_0_15_2360_1_part13 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 1664 128 = 19282128358178414706418814436 := by decide +kernel
private theorem receipt_0_15_2360_1_part14 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 1792 128 = 7202233263444588956561198556 := by decide +kernel
private theorem receipt_0_15_2360_1_part15 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 1920 15 = 74289332492807103184138227 := by decide +kernel
private theorem receipt_0_15_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 0 256 = 424225092530580867395779359360 :=
  phaseBlock_append receipt_0_15_2360_1_part0 receipt_0_15_2360_1_part1 rfl rfl rfl
private theorem receipt_0_15_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 256 256 = 351448909103620793526840947328 :=
  phaseBlock_append receipt_0_15_2360_1_part2 receipt_0_15_2360_1_part3 rfl rfl rfl
private theorem receipt_0_15_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 0 512 = 775674001634201660922620306688 :=
  phaseBlock_append receipt_0_15_2360_1_join0 receipt_0_15_2360_1_join1 rfl rfl rfl
private theorem receipt_0_15_2360_1_join3 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 512 256 = 283093460617298589899182961280 :=
  phaseBlock_append receipt_0_15_2360_1_part4 receipt_0_15_2360_1_part5 rfl rfl rfl
private theorem receipt_0_15_2360_1_join4 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 768 256 = 219019779917684072685457928832 :=
  phaseBlock_append receipt_0_15_2360_1_part6 receipt_0_15_2360_1_part7 rfl rfl rfl
private theorem receipt_0_15_2360_1_join5 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 512 512 = 502113240534982662584640890112 :=
  phaseBlock_append receipt_0_15_2360_1_join3 receipt_0_15_2360_1_join4 rfl rfl rfl
private theorem receipt_0_15_2360_1_join6 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 0 1024 = 1277787242169184323507261196800 :=
  phaseBlock_append receipt_0_15_2360_1_join2 receipt_0_15_2360_1_join5 rfl rfl rfl
private theorem receipt_0_15_2360_1_join7 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 1024 256 = 159089314787457463096595640960 :=
  phaseBlock_append receipt_0_15_2360_1_part8 receipt_0_15_2360_1_part9 rfl rfl rfl
private theorem receipt_0_15_2360_1_join8 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 1280 256 = 103163974530745814932676815539 :=
  phaseBlock_append receipt_0_15_2360_1_part10 receipt_0_15_2360_1_part11 rfl rfl rfl
private theorem receipt_0_15_2360_1_join9 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 1024 512 = 262253289318203278029272456499 :=
  phaseBlock_append receipt_0_15_2360_1_join7 receipt_0_15_2360_1_join8 rfl rfl rfl
private theorem receipt_0_15_2360_1_join10 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 1536 256 = 51106067268049428630225629043 :=
  phaseBlock_append receipt_0_15_2360_1_part12 receipt_0_15_2360_1_part13 rfl rfl rfl
private theorem receipt_0_15_2360_1_join11 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 1792 143 = 7276522595937396059745336783 :=
  phaseBlock_append receipt_0_15_2360_1_part14 receipt_0_15_2360_1_part15 rfl rfl rfl
private theorem receipt_0_15_2360_1_join12 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 1536 399 = 58382589863986824689970965826 :=
  phaseBlock_append receipt_0_15_2360_1_join10 receipt_0_15_2360_1_join11 rfl rfl rfl
private theorem receipt_0_15_2360_1_join13 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 1024 911 = 320635879182190102719243422325 :=
  phaseBlock_append receipt_0_15_2360_1_join9 receipt_0_15_2360_1_join12 rfl rfl rfl
private theorem receipt_0_15_2360_1_join14 :
    phaseBlock (fastLayer (bank 0 15).shape 179818 2360 76 1 0 1 1) 0 1935 = 1598423121351374426226504619125 :=
  phaseBlock_append receipt_0_15_2360_1_join6 receipt_0_15_2360_1_join13 rfl rfl rfl

private theorem receipt_0_15_2360_1 : fastPhase (bank 0 15).shape 179818 2360 76 1 0 1 1 = 1598423121351374426226504619125 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_15_2360_1_join14

theorem receipt_0_15 : Checked (bank 0 15) 76 0 1 := by
  refine checked_from_values (bank 0 15) 76 0 1
    (P3_7_1.checked (bank 0 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9204_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_15_2359_0 receipt_0_15_2359_1 receipt_0_15_2360_0 receipt_0_15_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_15_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 0 128 = 199537835267189590749140262784 := by decide +kernel
private theorem receipt_1_15_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 128 128 = 182567029445756322532640448384 := by decide +kernel
private theorem receipt_1_15_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 256 128 = 166119835315128055425545019264 := by decide +kernel
private theorem receipt_1_15_2359_0_part3 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 384 128 = 150187755953126710029178888064 := by decide +kernel
private theorem receipt_1_15_2359_0_part4 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 512 128 = 134762319596755249335303643008 := by decide +kernel
private theorem receipt_1_15_2359_0_part5 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 640 128 = 119835079617064778055623073664 := by decide +kernel
private theorem receipt_1_15_2359_0_part6 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 768 128 = 105397614494021641951288696704 := by decide +kernel
private theorem receipt_1_15_2359_0_part7 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 896 128 = 91441527791374527162405281664 := by decide +kernel
private theorem receipt_1_15_2359_0_part8 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 1024 128 = 77958448131521559537536376704 := by decide +kernel
private theorem receipt_1_15_2359_0_part9 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 1152 128 = 64940029170377403963209834368 := by decide +kernel
private theorem receipt_1_15_2359_0_part10 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 1280 128 = 52377956126053328286386725124 := by decide +kernel
private theorem receipt_1_15_2359_0_part11 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 1408 128 = 40263949300034483419249911874 := by decide +kernel
private theorem receipt_1_15_2359_0_part12 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 1536 128 = 28589719179947242190135437864 := by decide +kernel
private theorem receipt_1_15_2359_0_part13 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 1664 128 = 17346993230544426194629562721 := by decide +kernel
private theorem receipt_1_15_2359_0_part14 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 1792 128 = 6527523900101041527021529537 := by decide +kernel
private theorem receipt_1_15_2359_0_part15 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 1920 15 = 75956603515891285060032464 := by decide +kernel
private theorem receipt_1_15_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 0 256 = 382104864712945913281780711168 :=
  phaseBlock_append receipt_1_15_2359_0_part0 receipt_1_15_2359_0_part1 rfl rfl rfl
private theorem receipt_1_15_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 256 256 = 316307591268254765454723907328 :=
  phaseBlock_append receipt_1_15_2359_0_part2 receipt_1_15_2359_0_part3 rfl rfl rfl
private theorem receipt_1_15_2359_0_join2 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 0 512 = 698412455981200678736504618496 :=
  phaseBlock_append receipt_1_15_2359_0_join0 receipt_1_15_2359_0_join1 rfl rfl rfl
private theorem receipt_1_15_2359_0_join3 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 512 256 = 254597399213820027390926716672 :=
  phaseBlock_append receipt_1_15_2359_0_part4 receipt_1_15_2359_0_part5 rfl rfl rfl
private theorem receipt_1_15_2359_0_join4 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 768 256 = 196839142285396169113693978368 :=
  phaseBlock_append receipt_1_15_2359_0_part6 receipt_1_15_2359_0_part7 rfl rfl rfl
private theorem receipt_1_15_2359_0_join5 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 512 512 = 451436541499216196504620695040 :=
  phaseBlock_append receipt_1_15_2359_0_join3 receipt_1_15_2359_0_join4 rfl rfl rfl
private theorem receipt_1_15_2359_0_join6 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 0 1024 = 1149848997480416875241125313536 :=
  phaseBlock_append receipt_1_15_2359_0_join2 receipt_1_15_2359_0_join5 rfl rfl rfl
private theorem receipt_1_15_2359_0_join7 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 1024 256 = 142898477301898963500746211072 :=
  phaseBlock_append receipt_1_15_2359_0_part8 receipt_1_15_2359_0_part9 rfl rfl rfl
private theorem receipt_1_15_2359_0_join8 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 1280 256 = 92641905426087811705636636998 :=
  phaseBlock_append receipt_1_15_2359_0_part10 receipt_1_15_2359_0_part11 rfl rfl rfl
private theorem receipt_1_15_2359_0_join9 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 1024 512 = 235540382727986775206382848070 :=
  phaseBlock_append receipt_1_15_2359_0_join7 receipt_1_15_2359_0_join8 rfl rfl rfl
private theorem receipt_1_15_2359_0_join10 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 1536 256 = 45936712410491668384765000585 :=
  phaseBlock_append receipt_1_15_2359_0_part12 receipt_1_15_2359_0_part13 rfl rfl rfl
private theorem receipt_1_15_2359_0_join11 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 1792 143 = 6603480503616932812081562001 :=
  phaseBlock_append receipt_1_15_2359_0_part14 receipt_1_15_2359_0_part15 rfl rfl rfl
private theorem receipt_1_15_2359_0_join12 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 1536 399 = 52540192914108601196846562586 :=
  phaseBlock_append receipt_1_15_2359_0_join10 receipt_1_15_2359_0_join11 rfl rfl rfl
private theorem receipt_1_15_2359_0_join13 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 1024 911 = 288080575642095376403229410656 :=
  phaseBlock_append receipt_1_15_2359_0_join9 receipt_1_15_2359_0_join12 rfl rfl rfl
private theorem receipt_1_15_2359_0_join14 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 0) 0 1935 = 1437929573122512251644354724192 :=
  phaseBlock_append receipt_1_15_2359_0_join6 receipt_1_15_2359_0_join13 rfl rfl rfl

private theorem receipt_1_15_2359_0 : fastPhase (bank 1 15).shape 179818 2359 76 1 0 2 0 = 1437929573122512251644354724192 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_15_2359_0_join14

private theorem receipt_1_15_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 0 128 = 199404954313888904148116355392 := by decide +kernel
private theorem receipt_1_15_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 128 128 = 182438138032934887526249781568 := by decide +kernel
private theorem receipt_1_15_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 256 128 = 165994869054419079296849213760 := by decide +kernel
private theorem receipt_1_15_2359_1_part3 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 384 128 = 150066650648008189077836142912 := by decide +kernel
private theorem receipt_1_15_2359_1_part4 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 512 128 = 134645011242357508712975382848 := by decide +kernel
private theorem receipt_1_15_2359_1_part5 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 640 128 = 119721504399978011601380596032 := by decide +kernel
private theorem receipt_1_15_2359_1_part6 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 768 128 = 105287708792103452027019819328 := by decide +kernel
private theorem receipt_1_15_2359_1_part7 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 896 128 = 91335228173557464488220989760 := by decide +kernel
private theorem receipt_1_15_2359_1_part8 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 1024 128 = 77855691357620663027177470272 := by decide +kernel
private theorem receipt_1_15_2359_1_part9 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 1152 128 = 64840752190897740559453575488 := by decide +kernel
private theorem receipt_1_15_2359_1_part10 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 1280 128 = 52282096070227304372657286205 := by decide +kernel
private theorem receipt_1_15_2359_1_part11 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 1408 128 = 40171443441715983712060460644 := by decide +kernel
private theorem receipt_1_15_2359_1_part12 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 1536 128 = 28500504972715371909531910026 := by decide +kernel
private theorem receipt_1_15_2359_1_part13 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 1664 128 = 17261008318221881592104900374 := by decide +kernel
private theorem receipt_1_15_2359_1_part14 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 1792 128 = 6444706116556310266360047717 := by decide +kernel
private theorem receipt_1_15_2359_1_part15 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 1920 15 = 66455850341884700032820260 := by decide +kernel
private theorem receipt_1_15_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 0 256 = 381843092346823791674366136960 :=
  phaseBlock_append receipt_1_15_2359_1_part0 receipt_1_15_2359_1_part1 rfl rfl rfl
private theorem receipt_1_15_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 256 256 = 316061519702427268374685356672 :=
  phaseBlock_append receipt_1_15_2359_1_part2 receipt_1_15_2359_1_part3 rfl rfl rfl
private theorem receipt_1_15_2359_1_join2 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 0 512 = 697904612049251060049051493632 :=
  phaseBlock_append receipt_1_15_2359_1_join0 receipt_1_15_2359_1_join1 rfl rfl rfl
private theorem receipt_1_15_2359_1_join3 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 512 256 = 254366515642335520314355978880 :=
  phaseBlock_append receipt_1_15_2359_1_part4 receipt_1_15_2359_1_part5 rfl rfl rfl
private theorem receipt_1_15_2359_1_join4 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 768 256 = 196622936965660916515240809088 :=
  phaseBlock_append receipt_1_15_2359_1_part6 receipt_1_15_2359_1_part7 rfl rfl rfl
private theorem receipt_1_15_2359_1_join5 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 512 512 = 450989452607996436829596787968 :=
  phaseBlock_append receipt_1_15_2359_1_join3 receipt_1_15_2359_1_join4 rfl rfl rfl
private theorem receipt_1_15_2359_1_join6 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 0 1024 = 1148894064657247496878648281600 :=
  phaseBlock_append receipt_1_15_2359_1_join2 receipt_1_15_2359_1_join5 rfl rfl rfl
private theorem receipt_1_15_2359_1_join7 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 1024 256 = 142696443548518403586631045760 :=
  phaseBlock_append receipt_1_15_2359_1_part8 receipt_1_15_2359_1_part9 rfl rfl rfl
private theorem receipt_1_15_2359_1_join8 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 1280 256 = 92453539511943288084717746849 :=
  phaseBlock_append receipt_1_15_2359_1_part10 receipt_1_15_2359_1_part11 rfl rfl rfl
private theorem receipt_1_15_2359_1_join9 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 1024 512 = 235149983060461691671348792609 :=
  phaseBlock_append receipt_1_15_2359_1_join7 receipt_1_15_2359_1_join8 rfl rfl rfl
private theorem receipt_1_15_2359_1_join10 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 1536 256 = 45761513290937253501636810400 :=
  phaseBlock_append receipt_1_15_2359_1_part12 receipt_1_15_2359_1_part13 rfl rfl rfl
private theorem receipt_1_15_2359_1_join11 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 1792 143 = 6511161966898194966392867977 :=
  phaseBlock_append receipt_1_15_2359_1_part14 receipt_1_15_2359_1_part15 rfl rfl rfl
private theorem receipt_1_15_2359_1_join12 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 1536 399 = 52272675257835448468029678377 :=
  phaseBlock_append receipt_1_15_2359_1_join10 receipt_1_15_2359_1_join11 rfl rfl rfl
private theorem receipt_1_15_2359_1_join13 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 1024 911 = 287422658318297140139378470986 :=
  phaseBlock_append receipt_1_15_2359_1_join9 receipt_1_15_2359_1_join12 rfl rfl rfl
private theorem receipt_1_15_2359_1_join14 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2359 76 1 0 2 1) 0 1935 = 1436316722975544637018026752586 :=
  phaseBlock_append receipt_1_15_2359_1_join6 receipt_1_15_2359_1_join13 rfl rfl rfl

private theorem receipt_1_15_2359_1 : fastPhase (bank 1 15).shape 179818 2359 76 1 0 2 1 = 1436316722975544637018026752586 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_15_2359_1_join14

private theorem receipt_1_15_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 0 128 = 199539623839638084085472593568 := by decide +kernel
private theorem receipt_1_15_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 128 128 = 182568605133247372083933533856 := by decide +kernel
private theorem receipt_1_15_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 256 128 = 166121212623904958379586037408 := by decide +kernel
private theorem receipt_1_15_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 384 128 = 150188949100415515434050746016 := by decide +kernel
private theorem receipt_1_15_2360_0_part4 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 512 128 = 134763342511638649116507621024 := by decide +kernel
private theorem receipt_1_15_2360_0_part5 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 640 128 = 119835945941355118423899248288 := by decide +kernel
private theorem receipt_1_15_2360_0_part6 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 768 128 = 105398337583133055201134143136 := by decide +kernel
private theorem receipt_1_15_2360_0_part7 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 896 128 = 91442120715194183861290055328 := by decide +kernel
private theorem receipt_1_15_2360_0_part8 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 1024 128 = 77958923675280041105817274016 := by decide +kernel
private theorem receipt_1_15_2360_0_part9 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 1152 128 = 64940399835518195644741932704 := by decide +kernel
private theorem receipt_1_15_2360_0_part10 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 1280 128 = 52378233924687171795245064701 := by decide +kernel
private theorem receipt_1_15_2360_0_part11 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 1408 128 = 40264146108956540410987031671 := by decide +kernel
private theorem receipt_1_15_2360_0_part12 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 1536 128 = 28589846845081317482631448058 := by decide +kernel
private theorem receipt_1_15_2360_0_part13 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 1664 128 = 17347063298825371484487807597 := by decide +kernel
private theorem receipt_1_15_2360_0_part14 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 1792 128 = 6527547612535479776121587595 := by decide +kernel
private theorem receipt_1_15_2360_0_part15 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 1920 15 = 75956856311399180213242900 := by decide +kernel
private theorem receipt_1_15_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 0 256 = 382108228972885456169406127424 :=
  phaseBlock_append receipt_1_15_2360_0_part0 receipt_1_15_2360_0_part1 rfl rfl rfl
private theorem receipt_1_15_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 256 256 = 316310161724320473813636783424 :=
  phaseBlock_append receipt_1_15_2360_0_part2 receipt_1_15_2360_0_part3 rfl rfl rfl
private theorem receipt_1_15_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 0 512 = 698418390697205929983042910848 :=
  phaseBlock_append receipt_1_15_2360_0_join0 receipt_1_15_2360_0_join1 rfl rfl rfl
private theorem receipt_1_15_2360_0_join3 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 512 256 = 254599288452993767540406869312 :=
  phaseBlock_append receipt_1_15_2360_0_part4 receipt_1_15_2360_0_part5 rfl rfl rfl
private theorem receipt_1_15_2360_0_join4 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 768 256 = 196840458298327239062424198464 :=
  phaseBlock_append receipt_1_15_2360_0_part6 receipt_1_15_2360_0_part7 rfl rfl rfl
private theorem receipt_1_15_2360_0_join5 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 512 512 = 451439746751321006602831067776 :=
  phaseBlock_append receipt_1_15_2360_0_join3 receipt_1_15_2360_0_join4 rfl rfl rfl
private theorem receipt_1_15_2360_0_join6 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 0 1024 = 1149858137448526936585873978624 :=
  phaseBlock_append receipt_1_15_2360_0_join2 receipt_1_15_2360_0_join5 rfl rfl rfl
private theorem receipt_1_15_2360_0_join7 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 1024 256 = 142899323510798236750559206720 :=
  phaseBlock_append receipt_1_15_2360_0_part8 receipt_1_15_2360_0_part9 rfl rfl rfl
private theorem receipt_1_15_2360_0_join8 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 1280 256 = 92642380033643712206232096372 :=
  phaseBlock_append receipt_1_15_2360_0_part10 receipt_1_15_2360_0_part11 rfl rfl rfl
private theorem receipt_1_15_2360_0_join9 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 1024 512 = 235541703544441948956791303092 :=
  phaseBlock_append receipt_1_15_2360_0_join7 receipt_1_15_2360_0_join8 rfl rfl rfl
private theorem receipt_1_15_2360_0_join10 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 1536 256 = 45936910143906688967119255655 :=
  phaseBlock_append receipt_1_15_2360_0_part12 receipt_1_15_2360_0_part13 rfl rfl rfl
private theorem receipt_1_15_2360_0_join11 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 1792 143 = 6603504468846878956334830495 :=
  phaseBlock_append receipt_1_15_2360_0_part14 receipt_1_15_2360_0_part15 rfl rfl rfl
private theorem receipt_1_15_2360_0_join12 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 1536 399 = 52540414612753567923454086150 :=
  phaseBlock_append receipt_1_15_2360_0_join10 receipt_1_15_2360_0_join11 rfl rfl rfl
private theorem receipt_1_15_2360_0_join13 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 1024 911 = 288082118157195516880245389242 :=
  phaseBlock_append receipt_1_15_2360_0_join9 receipt_1_15_2360_0_join12 rfl rfl rfl
private theorem receipt_1_15_2360_0_join14 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 0) 0 1935 = 1437940255605722453466119367866 :=
  phaseBlock_append receipt_1_15_2360_0_join6 receipt_1_15_2360_0_join13 rfl rfl rfl

private theorem receipt_1_15_2360_0 : fastPhase (bank 1 15).shape 179818 2360 76 1 0 2 0 = 1437940255605722453466119367866 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_15_2360_0_join14

private theorem receipt_1_15_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 0 128 = 199406741910064751866250617888 := by decide +kernel
private theorem receipt_1_15_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 128 128 = 182439712801728886818535814176 := by decide +kernel
private theorem receipt_1_15_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 256 128 = 165996245500699758338671117344 := by decide +kernel
private theorem receipt_1_15_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 384 128 = 150067842987631620130061505568 := by decide +kernel
private theorem receipt_1_15_2360_1_part4 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 512 128 = 134646033403041193916397691936 := by decide +kernel
private theorem receipt_1_15_2360_1_part5 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 640 128 = 119722370022173889161859429408 := by decide +kernel
private theorem receipt_1_15_2360_1_part6 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 768 128 = 105288431229870022791318815776 := by decide +kernel
private theorem receipt_1_15_2360_1_part7 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 896 128 = 91335820495431038910543598624 := by decide +kernel
private theorem receipt_1_15_2360_1_part8 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 1024 128 = 77856166347485728526400480288 := by decide +kernel
private theorem receipt_1_15_2360_1_part9 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 1152 128 = 64841122348856449267058422816 := by decide +kernel
private theorem receipt_1_15_2360_1_part10 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 1280 128 = 52282373407417311811062622996 := by decide +kernel
private theorem receipt_1_15_2360_1_part11 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 1408 128 = 40171639833910977798862502898 := by decide +kernel
private theorem receipt_1_15_2360_1_part12 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 1536 128 = 28500632264456437365586709109 := by decide +kernel
private theorem receipt_1_15_2360_1_part13 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 1664 128 = 17261078055054085736025343114 := by decide +kernel
private theorem receipt_1_15_2360_1_part14 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 1792 128 = 6444729538109184411620398572 := by decide +kernel
private theorem receipt_1_15_2360_1_part15 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 1920 15 = 66456071645464209470789090 := by decide +kernel
private theorem receipt_1_15_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 0 256 = 381846454711793638684786432064 :=
  phaseBlock_append receipt_1_15_2360_1_part0 receipt_1_15_2360_1_part1 rfl rfl rfl
private theorem receipt_1_15_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 256 256 = 316064088488331378468732622912 :=
  phaseBlock_append receipt_1_15_2360_1_part2 receipt_1_15_2360_1_part3 rfl rfl rfl
private theorem receipt_1_15_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 0 512 = 697910543200125017153519054976 :=
  phaseBlock_append receipt_1_15_2360_1_join0 receipt_1_15_2360_1_join1 rfl rfl rfl
private theorem receipt_1_15_2360_1_join3 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 512 256 = 254368403425215083078257121344 :=
  phaseBlock_append receipt_1_15_2360_1_part4 receipt_1_15_2360_1_part5 rfl rfl rfl
private theorem receipt_1_15_2360_1_join4 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 768 256 = 196624251725301061701862414400 :=
  phaseBlock_append receipt_1_15_2360_1_part6 receipt_1_15_2360_1_part7 rfl rfl rfl
private theorem receipt_1_15_2360_1_join5 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 512 512 = 450992655150516144780119535744 :=
  phaseBlock_append receipt_1_15_2360_1_join3 receipt_1_15_2360_1_join4 rfl rfl rfl
private theorem receipt_1_15_2360_1_join6 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 0 1024 = 1148903198350641161933638590720 :=
  phaseBlock_append receipt_1_15_2360_1_join2 receipt_1_15_2360_1_join5 rfl rfl rfl
private theorem receipt_1_15_2360_1_join7 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 1024 256 = 142697288696342177793458903104 :=
  phaseBlock_append receipt_1_15_2360_1_part8 receipt_1_15_2360_1_part9 rfl rfl rfl
private theorem receipt_1_15_2360_1_join8 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 1280 256 = 92454013241328289609925125894 :=
  phaseBlock_append receipt_1_15_2360_1_part10 receipt_1_15_2360_1_part11 rfl rfl rfl
private theorem receipt_1_15_2360_1_join9 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 1024 512 = 235151301937670467403384028998 :=
  phaseBlock_append receipt_1_15_2360_1_join7 receipt_1_15_2360_1_join8 rfl rfl rfl
private theorem receipt_1_15_2360_1_join10 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 1536 256 = 45761710319510523101612052223 :=
  phaseBlock_append receipt_1_15_2360_1_part12 receipt_1_15_2360_1_part13 rfl rfl rfl
private theorem receipt_1_15_2360_1_join11 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 1792 143 = 6511185609754648621091187662 :=
  phaseBlock_append receipt_1_15_2360_1_part14 receipt_1_15_2360_1_part15 rfl rfl rfl
private theorem receipt_1_15_2360_1_join12 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 1536 399 = 52272895929265171722703239885 :=
  phaseBlock_append receipt_1_15_2360_1_join10 receipt_1_15_2360_1_join11 rfl rfl rfl
private theorem receipt_1_15_2360_1_join13 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 1024 911 = 287424197866935639126087268883 :=
  phaseBlock_append receipt_1_15_2360_1_join9 receipt_1_15_2360_1_join12 rfl rfl rfl
private theorem receipt_1_15_2360_1_join14 :
    phaseBlock (fastLayer (bank 1 15).shape 179818 2360 76 1 0 2 1) 0 1935 = 1436327396217576801059725859603 :=
  phaseBlock_append receipt_1_15_2360_1_join6 receipt_1_15_2360_1_join13 rfl rfl rfl

private theorem receipt_1_15_2360_1 : fastPhase (bank 1 15).shape 179818 2360 76 1 0 2 1 = 1436327396217576801059725859603 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_15_2360_1_join14

theorem receipt_1_15 : Checked (bank 1 15) 76 0 2 := by
  refine checked_from_values (bank 1 15) 76 0 2
    (P3_7_1.checked (bank 1 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9204_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_15_2359_0 receipt_1_15_2359_1 receipt_1_15_2360_0 receipt_1_15_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_15_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 0 128 = 107031750834751853529788104512 := by decide +kernel
private theorem receipt_2_15_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 128 128 = 97620959745797967638984908608 := by decide +kernel
private theorem receipt_2_15_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 256 128 = 88546696517876748196706975552 := by decide +kernel
private theorem receipt_2_15_2359_0_part3 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 384 128 = 79801738881554303697357250368 := by decide +kernel
private theorem receipt_2_15_2359_0_part4 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 512 128 = 71378938706147924810797760320 := by decide +kernel
private theorem receipt_2_15_2359_0_part5 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 640 128 = 63271221691848051168792305472 := by decide +kernel
private theorem receipt_2_15_2359_0_part6 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 768 128 = 55471587061840238151449149248 := by decide +kernel
private theorem receipt_2_15_2359_0_part7 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 896 128 = 47973107254427123673663708992 := by decide +kernel
private theorem receipt_2_15_2359_0_part8 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 1024 128 = 40768927615150394971561246528 := by decide +kernel
private theorem receipt_2_15_2359_0_part9 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 1152 128 = 33852266088912755388939558720 := by decide +kernel
private theorem receipt_2_15_2359_0_part10 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 1280 128 = 27216416314711686620664052723 := by decide +kernel
private theorem receipt_2_15_2359_0_part11 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 1408 128 = 20854749107620350059376211966 := by decide +kernel
private theorem receipt_2_15_2359_0_part12 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 1536 128 = 14760688897289953093961965074 := by decide +kernel
private theorem receipt_2_15_2359_0_part13 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 1664 128 = 8927727505110497285024013954 := by decide +kernel
private theorem receipt_2_15_2359_0_part14 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 1792 128 = 3349428025384959538056252741 := by decide +kernel
private theorem receipt_2_15_2359_0_part15 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 1920 15 = 38889497914476311882869320 := by decide +kernel
private theorem receipt_2_15_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 0 256 = 204652710580549821168773013120 :=
  phaseBlock_append receipt_2_15_2359_0_part0 receipt_2_15_2359_0_part1 rfl rfl rfl
private theorem receipt_2_15_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 256 256 = 168348435399431051894064225920 :=
  phaseBlock_append receipt_2_15_2359_0_part2 receipt_2_15_2359_0_part3 rfl rfl rfl
private theorem receipt_2_15_2359_0_join2 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 0 512 = 373001145979980873062837239040 :=
  phaseBlock_append receipt_2_15_2359_0_join0 receipt_2_15_2359_0_join1 rfl rfl rfl
private theorem receipt_2_15_2359_0_join3 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 512 256 = 134650160397995975979590065792 :=
  phaseBlock_append receipt_2_15_2359_0_part4 receipt_2_15_2359_0_part5 rfl rfl rfl
private theorem receipt_2_15_2359_0_join4 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 768 256 = 103444694316267361825112858240 :=
  phaseBlock_append receipt_2_15_2359_0_part6 receipt_2_15_2359_0_part7 rfl rfl rfl
private theorem receipt_2_15_2359_0_join5 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 512 512 = 238094854714263337804702924032 :=
  phaseBlock_append receipt_2_15_2359_0_join3 receipt_2_15_2359_0_join4 rfl rfl rfl
private theorem receipt_2_15_2359_0_join6 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 0 1024 = 611096000694244210867540163072 :=
  phaseBlock_append receipt_2_15_2359_0_join2 receipt_2_15_2359_0_join5 rfl rfl rfl
private theorem receipt_2_15_2359_0_join7 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 1024 256 = 74621193704063150360500805248 :=
  phaseBlock_append receipt_2_15_2359_0_part8 receipt_2_15_2359_0_part9 rfl rfl rfl
private theorem receipt_2_15_2359_0_join8 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 1280 256 = 48071165422332036680040264689 :=
  phaseBlock_append receipt_2_15_2359_0_part10 receipt_2_15_2359_0_part11 rfl rfl rfl
private theorem receipt_2_15_2359_0_join9 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 1024 512 = 122692359126395187040541069937 :=
  phaseBlock_append receipt_2_15_2359_0_join7 receipt_2_15_2359_0_join8 rfl rfl rfl
private theorem receipt_2_15_2359_0_join10 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 1536 256 = 23688416402400450378985979028 :=
  phaseBlock_append receipt_2_15_2359_0_part12 receipt_2_15_2359_0_part13 rfl rfl rfl
private theorem receipt_2_15_2359_0_join11 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 1792 143 = 3388317523299435849939122061 :=
  phaseBlock_append receipt_2_15_2359_0_part14 receipt_2_15_2359_0_part15 rfl rfl rfl
private theorem receipt_2_15_2359_0_join12 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 1536 399 = 27076733925699886228925101089 :=
  phaseBlock_append receipt_2_15_2359_0_join10 receipt_2_15_2359_0_join11 rfl rfl rfl
private theorem receipt_2_15_2359_0_join13 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 1024 911 = 149769093052095073269466171026 :=
  phaseBlock_append receipt_2_15_2359_0_join9 receipt_2_15_2359_0_join12 rfl rfl rfl
private theorem receipt_2_15_2359_0_join14 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 0) 0 1935 = 760865093746339284137006334098 :=
  phaseBlock_append receipt_2_15_2359_0_join6 receipt_2_15_2359_0_join13 rfl rfl rfl

private theorem receipt_2_15_2359_0 : fastPhase (bank 2 15).shape 179818 2359 76 1 0 7 0 = 760865093746339284137006334098 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_15_2359_0_join14

private theorem receipt_2_15_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 0 128 = 106957847232609322582117635136 := by decide +kernel
private theorem receipt_2_15_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 128 128 = 97549638751455768223084393536 := by decide +kernel
private theorem receipt_2_15_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 256 128 = 88477902988242117824170923072 := by decide +kernel
private theorem receipt_2_15_2359_1_part3 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 384 128 = 79735418240321305072911250496 := by decide +kernel
private theorem receipt_2_15_2359_1_part4 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 512 128 = 71315036941439808816029914176 := by decide +kernel
private theorem receipt_2_15_2359_1_part5 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 640 128 = 63209685353859619845884654656 := by decide +kernel
private theorem receipt_2_15_2359_1_part6 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 768 128 = 55412363260480207686909105216 := by decide +kernel
private theorem receipt_2_15_2359_1_part7 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 896 128 = 47916143656960487382055482432 := by decide +kernel
private theorem receipt_2_15_2359_1_part8 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 1024 128 = 40714172443840786279237276736 := by decide +kernel
private theorem receipt_2_15_2359_1_part9 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 1152 128 = 33799668118664810817771942976 := by decide +kernel
private theorem receipt_2_15_2359_1_part10 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 1280 128 = 27165924864517164205528593125 := by decide +kernel
private theorem receipt_2_15_2359_1_part11 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 1408 128 = 20806314020578656325728346255 := by decide +kernel
private theorem receipt_2_15_2359_1_part12 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 1536 128 = 14714260557227099715944841730 := by decide +kernel
private theorem receipt_2_15_2359_1_part13 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 1664 128 = 8883256839909420803141956887 := by decide +kernel
private theorem receipt_2_15_2359_1_part14 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 1792 128 = 3306866504620430647332054709 := by decide +kernel
private theorem receipt_2_15_2359_1_part15 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 1920 15 = 34024570148891655679076486 := by decide +kernel
private theorem receipt_2_15_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 0 256 = 204507485984065090805202028672 :=
  phaseBlock_append receipt_2_15_2359_1_part0 receipt_2_15_2359_1_part1 rfl rfl rfl
private theorem receipt_2_15_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 256 256 = 168213321228563422897082173568 :=
  phaseBlock_append receipt_2_15_2359_1_part2 receipt_2_15_2359_1_part3 rfl rfl rfl
private theorem receipt_2_15_2359_1_join2 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 0 512 = 372720807212628513702284202240 :=
  phaseBlock_append receipt_2_15_2359_1_join0 receipt_2_15_2359_1_join1 rfl rfl rfl
private theorem receipt_2_15_2359_1_join3 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 512 256 = 134524722295299428661914568832 :=
  phaseBlock_append receipt_2_15_2359_1_part4 receipt_2_15_2359_1_part5 rfl rfl rfl
private theorem receipt_2_15_2359_1_join4 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 768 256 = 103328506917440695068964587648 :=
  phaseBlock_append receipt_2_15_2359_1_part6 receipt_2_15_2359_1_part7 rfl rfl rfl
private theorem receipt_2_15_2359_1_join5 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 512 512 = 237853229212740123730879156480 :=
  phaseBlock_append receipt_2_15_2359_1_join3 receipt_2_15_2359_1_join4 rfl rfl rfl
private theorem receipt_2_15_2359_1_join6 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 0 1024 = 610574036425368637433163358720 :=
  phaseBlock_append receipt_2_15_2359_1_join2 receipt_2_15_2359_1_join5 rfl rfl rfl
private theorem receipt_2_15_2359_1_join7 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 1024 256 = 74513840562505597097009219712 :=
  phaseBlock_append receipt_2_15_2359_1_part8 receipt_2_15_2359_1_part9 rfl rfl rfl
private theorem receipt_2_15_2359_1_join8 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 1280 256 = 47972238885095820531256939380 :=
  phaseBlock_append receipt_2_15_2359_1_part10 receipt_2_15_2359_1_part11 rfl rfl rfl
private theorem receipt_2_15_2359_1_join9 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 1024 512 = 122486079447601417628266159092 :=
  phaseBlock_append receipt_2_15_2359_1_join7 receipt_2_15_2359_1_join8 rfl rfl rfl
private theorem receipt_2_15_2359_1_join10 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 1536 256 = 23597517397136520519086798617 :=
  phaseBlock_append receipt_2_15_2359_1_part12 receipt_2_15_2359_1_part13 rfl rfl rfl
private theorem receipt_2_15_2359_1_join11 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 1792 143 = 3340891074769322303011131195 :=
  phaseBlock_append receipt_2_15_2359_1_part14 receipt_2_15_2359_1_part15 rfl rfl rfl
private theorem receipt_2_15_2359_1_join12 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 1536 399 = 26938408471905842822097929812 :=
  phaseBlock_append receipt_2_15_2359_1_join10 receipt_2_15_2359_1_join11 rfl rfl rfl
private theorem receipt_2_15_2359_1_join13 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 1024 911 = 149424487919507260450364088904 :=
  phaseBlock_append receipt_2_15_2359_1_join9 receipt_2_15_2359_1_join12 rfl rfl rfl
private theorem receipt_2_15_2359_1_join14 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2359 76 1 0 7 1) 0 1935 = 759998524344875897883527447624 :=
  phaseBlock_append receipt_2_15_2359_1_join6 receipt_2_15_2359_1_join13 rfl rfl rfl

private theorem receipt_2_15_2359_1 : fastPhase (bank 2 15).shape 179818 2359 76 1 0 7 1 = 759998524344875897883527447624 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_15_2359_1_join14

private theorem receipt_2_15_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 0 128 = 107032710231169119264474026784 := by decide +kernel
private theorem receipt_2_15_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 128 128 = 97621802294966938076137849632 := by decide +kernel
private theorem receipt_2_15_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 256 128 = 88547430671452612249502593824 := by decide +kernel
private theorem receipt_2_15_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 384 128 = 79802372863569434118280733472 := by decide +kernel
private theorem receipt_2_15_2360_0_part4 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 512 128 = 71379480515525293774817530656 := by decide +kernel
private theorem receipt_2_15_2360_0_part5 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 640 128 = 63271679104903870642581521184 := by decide +kernel
private theorem receipt_2_15_2360_0_part6 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 768 128 = 55471967634775825048655000352 := by decide +kernel
private theorem receipt_2_15_2360_0_part7 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 896 128 = 47973418325809989796224508704 := by decide +kernel
private theorem receipt_2_15_2360_0_part8 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 1024 128 = 40769176308384561737071317792 := by decide +kernel
private theorem receipt_2_15_2360_0_part9 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 1152 128 = 33852459314698293344061915936 := by decide +kernel
private theorem receipt_2_15_2360_0_part10 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 1280 128 = 27216560666296529876052894126 := by decide +kernel
private theorem receipt_2_15_2360_0_part11 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 1408 128 = 20854851047332397476806983817 := by decide +kernel
private theorem receipt_2_15_2360_0_part12 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 1536 128 = 14760754811673442862851871289 := by decide +kernel
private theorem receipt_2_15_2360_0_part13 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 1664 128 = 8927763567170888472199374690 := by decide +kernel
private theorem receipt_2_15_2360_0_part14 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 1792 128 = 3349440193117884874760949162 := by decide +kernel
private theorem receipt_2_15_2360_0_part15 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 1920 15 = 38889627344879816628299316 := by decide +kernel
private theorem receipt_2_15_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 0 256 = 204654512526136057340611876416 :=
  phaseBlock_append receipt_2_15_2360_0_part0 receipt_2_15_2360_0_part1 rfl rfl rfl
private theorem receipt_2_15_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 256 256 = 168349803535022046367783327296 :=
  phaseBlock_append receipt_2_15_2360_0_part2 receipt_2_15_2360_0_part3 rfl rfl rfl
private theorem receipt_2_15_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 0 512 = 373004316061158103708395203712 :=
  phaseBlock_append receipt_2_15_2360_0_join0 receipt_2_15_2360_0_join1 rfl rfl rfl
private theorem receipt_2_15_2360_0_join3 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 512 256 = 134651159620429164417399051840 :=
  phaseBlock_append receipt_2_15_2360_0_part4 receipt_2_15_2360_0_part5 rfl rfl rfl
private theorem receipt_2_15_2360_0_join4 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 768 256 = 103445385960585814844879509056 :=
  phaseBlock_append receipt_2_15_2360_0_part6 receipt_2_15_2360_0_part7 rfl rfl rfl
private theorem receipt_2_15_2360_0_join5 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 512 512 = 238096545581014979262278560896 :=
  phaseBlock_append receipt_2_15_2360_0_join3 receipt_2_15_2360_0_join4 rfl rfl rfl
private theorem receipt_2_15_2360_0_join6 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 0 1024 = 611100861642173082970673764608 :=
  phaseBlock_append receipt_2_15_2360_0_join2 receipt_2_15_2360_0_join5 rfl rfl rfl
private theorem receipt_2_15_2360_0_join7 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 1024 256 = 74621635623082855081133233728 :=
  phaseBlock_append receipt_2_15_2360_0_part8 receipt_2_15_2360_0_part9 rfl rfl rfl
private theorem receipt_2_15_2360_0_join8 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 1280 256 = 48071411713628927352859877943 :=
  phaseBlock_append receipt_2_15_2360_0_part10 receipt_2_15_2360_0_part11 rfl rfl rfl
private theorem receipt_2_15_2360_0_join9 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 1024 512 = 122693047336711782433993111671 :=
  phaseBlock_append receipt_2_15_2360_0_join7 receipt_2_15_2360_0_join8 rfl rfl rfl
private theorem receipt_2_15_2360_0_join10 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 1536 256 = 23688518378844331335051245979 :=
  phaseBlock_append receipt_2_15_2360_0_part12 receipt_2_15_2360_0_part13 rfl rfl rfl
private theorem receipt_2_15_2360_0_join11 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 1792 143 = 3388329820462764691389248478 :=
  phaseBlock_append receipt_2_15_2360_0_part14 receipt_2_15_2360_0_part15 rfl rfl rfl
private theorem receipt_2_15_2360_0_join12 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 1536 399 = 27076848199307096026440494457 :=
  phaseBlock_append receipt_2_15_2360_0_join10 receipt_2_15_2360_0_join11 rfl rfl rfl
private theorem receipt_2_15_2360_0_join13 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 1024 911 = 149769895536018878460433606128 :=
  phaseBlock_append receipt_2_15_2360_0_join9 receipt_2_15_2360_0_join12 rfl rfl rfl
private theorem receipt_2_15_2360_0_join14 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 0) 0 1935 = 760870757178191961431107370736 :=
  phaseBlock_append receipt_2_15_2360_0_join6 receipt_2_15_2360_0_join13 rfl rfl rfl

private theorem receipt_2_15_2360_0 : fastPhase (bank 2 15).shape 179818 2360 76 1 0 7 0 = 760870757178191961431107370736 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_15_2360_0_join14

private theorem receipt_2_15_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 0 128 = 106958806081804287973975737824 := by decide +kernel
private theorem receipt_2_15_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 128 128 = 97550480788654109059768169952 := by decide +kernel
private theorem receipt_2_15_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 256 128 = 88478636663976072178105066976 := by decide +kernel
private theorem receipt_2_15_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 384 128 = 79736051777514200984976856544 := by decide +kernel
private theorem receipt_2_15_2360_1_part4 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 512 128 = 71315578337919415900905342432 := by decide +kernel
private theorem receipt_2_15_2360_1_part5 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 640 128 = 63210142384860725683434190304 := by decide +kernel
private theorem receipt_2_15_2360_1_part6 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 768 128 = 55412743481136418999619413472 := by decide +kernel
private theorem receipt_2_15_2360_1_part7 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 896 128 = 47916454404785255998519858656 := by decide +kernel
private theorem receipt_2_15_2360_1_part8 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 1024 128 = 40714420841197659883687691744 := by decide +kernel
private theorem receipt_2_15_2360_1_part9 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 1152 128 = 33799861075226908485658883552 := by decide +kernel
private theorem receipt_2_15_2360_1_part10 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 1280 128 = 27166068972710385295589699786 := by decide +kernel
private theorem receipt_2_15_2360_1_part11 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 1408 128 = 20806415741891202411228559711 := by decide +kernel
private theorem receipt_2_15_2360_1_part12 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 1536 128 = 14714326277182967664704480558 := by decide +kernel
private theorem receipt_2_15_2360_1_part13 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 1664 128 = 8883292730501554001708365630 := by decide +kernel
private theorem receipt_2_15_2360_1_part14 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 1792 128 = 3306878522849926613668065560 := by decide +kernel
private theorem receipt_2_15_2360_1_part15 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 1920 15 = 34024683453611171862000691 := by decide +kernel
private theorem receipt_2_15_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 0 256 = 204509286870458397033743907776 :=
  phaseBlock_append receipt_2_15_2360_1_part0 receipt_2_15_2360_1_part1 rfl rfl rfl
private theorem receipt_2_15_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 256 256 = 168214688441490273163081923520 :=
  phaseBlock_append receipt_2_15_2360_1_part2 receipt_2_15_2360_1_part3 rfl rfl rfl
private theorem receipt_2_15_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 0 512 = 372723975311948670196825831296 :=
  phaseBlock_append receipt_2_15_2360_1_join0 receipt_2_15_2360_1_join1 rfl rfl rfl
private theorem receipt_2_15_2360_1_join3 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 512 256 = 134525720722780141584339532736 :=
  phaseBlock_append receipt_2_15_2360_1_part4 receipt_2_15_2360_1_part5 rfl rfl rfl
private theorem receipt_2_15_2360_1_join4 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 768 256 = 103329197885921674998139272128 :=
  phaseBlock_append receipt_2_15_2360_1_part6 receipt_2_15_2360_1_part7 rfl rfl rfl
private theorem receipt_2_15_2360_1_join5 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 512 512 = 237854918608701816582478804864 :=
  phaseBlock_append receipt_2_15_2360_1_join3 receipt_2_15_2360_1_join4 rfl rfl rfl
private theorem receipt_2_15_2360_1_join6 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 0 1024 = 610578893920650486779304636160 :=
  phaseBlock_append receipt_2_15_2360_1_join2 receipt_2_15_2360_1_join5 rfl rfl rfl
private theorem receipt_2_15_2360_1_join7 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 1024 256 = 74514281916424568369346575296 :=
  phaseBlock_append receipt_2_15_2360_1_part8 receipt_2_15_2360_1_part9 rfl rfl rfl
private theorem receipt_2_15_2360_1_join8 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 1280 256 = 47972484714601587706818259497 :=
  phaseBlock_append receipt_2_15_2360_1_part10 receipt_2_15_2360_1_part11 rfl rfl rfl
private theorem receipt_2_15_2360_1_join9 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 1024 512 = 122486766631026156076164834793 :=
  phaseBlock_append receipt_2_15_2360_1_join7 receipt_2_15_2360_1_join8 rfl rfl rfl
private theorem receipt_2_15_2360_1_join10 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 1536 256 = 23597619007684521666412846188 :=
  phaseBlock_append receipt_2_15_2360_1_part12 receipt_2_15_2360_1_part13 rfl rfl rfl
private theorem receipt_2_15_2360_1_join11 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 1792 143 = 3340903206303537785530066251 :=
  phaseBlock_append receipt_2_15_2360_1_part14 receipt_2_15_2360_1_part15 rfl rfl rfl
private theorem receipt_2_15_2360_1_join12 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 1536 399 = 26938522213988059451942912439 :=
  phaseBlock_append receipt_2_15_2360_1_join10 receipt_2_15_2360_1_join11 rfl rfl rfl
private theorem receipt_2_15_2360_1_join13 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 1024 911 = 149425288845014215528107747232 :=
  phaseBlock_append receipt_2_15_2360_1_join9 receipt_2_15_2360_1_join12 rfl rfl rfl
private theorem receipt_2_15_2360_1_join14 :
    phaseBlock (fastLayer (bank 2 15).shape 179818 2360 76 1 0 7 1) 0 1935 = 760004182765664702307412383392 :=
  phaseBlock_append receipt_2_15_2360_1_join6 receipt_2_15_2360_1_join13 rfl rfl rfl

private theorem receipt_2_15_2360_1 : fastPhase (bank 2 15).shape 179818 2360 76 1 0 7 1 = 760004182765664702307412383392 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_15_2360_1_join14

theorem receipt_2_15 : Checked (bank 2 15) 76 0 7 := by
  refine checked_from_values (bank 2 15) 76 0 7
    (P3_7_1.checked (bank 2 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9204_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_15_2359_0 receipt_2_15_2359_1 receipt_2_15_2360_0 receipt_2_15_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_15_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 0 128 = 22541282490107033126843802720 := by decide +kernel
private theorem receipt_3_15_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 128 128 = 20657103599756253694156756064 := by decide +kernel
private theorem receipt_3_15_2359_0_part2 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 256 128 = 18825008083422549413549261920 := by decide +kernel
private theorem receipt_3_15_2359_0_part3 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 384 128 = 17046006212076298027011683424 := by decide +kernel
private theorem receipt_3_15_2359_0_part4 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 512 128 = 15321102474613379516902745184 := by decide +kernel
private theorem receipt_3_15_2359_0_part5 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 640 128 = 13651295587309524749474468960 := by decide +kernel
private theorem receipt_3_15_2359_0_part6 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 768 128 = 12037578503274664118397109344 := by decide +kernel
private theorem receipt_3_15_2359_0_part7 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 896 128 = 10480938421907276188284089440 := by decide +kernel
private theorem receipt_3_15_2359_0_part8 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 1024 128 = 8982356798348736338216936544 := by decide +kernel
private theorem receipt_3_15_2359_0_part9 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 1152 128 = 7542809352937665405270217824 := by decide +kernel
private theorem receipt_3_15_2359_0_part10 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 1280 128 = 6163266080664278328036476000 := by decide +kernel
private theorem receipt_3_15_2359_0_part11 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 1408 128 = 4844691260624732790151165024 := by decide +kernel
private theorem receipt_3_15_2359_0_part12 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 1536 128 = 3588043465475477863817585760 := by decide +kernel
private theorem receipt_3_15_2359_0_part13 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 1664 128 = 2394275570887602653331821664 := by decide +kernel
private theorem receipt_3_15_2359_0_part14 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 1792 128 = 1264334765001184938607674464 := by decide +kernel
private theorem receipt_3_15_2359_0_part15 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 1920 88 = 247395370738680873248727418 := by decide +kernel
private theorem receipt_3_15_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 0 256 = 43198386089863286821000558784 :=
  phaseBlock_append receipt_3_15_2359_0_part0 receipt_3_15_2359_0_part1 rfl rfl rfl
private theorem receipt_3_15_2359_0_join1 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 256 256 = 35871014295498847440560945344 :=
  phaseBlock_append receipt_3_15_2359_0_part2 receipt_3_15_2359_0_part3 rfl rfl rfl
private theorem receipt_3_15_2359_0_join2 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 0 512 = 79069400385362134261561504128 :=
  phaseBlock_append receipt_3_15_2359_0_join0 receipt_3_15_2359_0_join1 rfl rfl rfl
private theorem receipt_3_15_2359_0_join3 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 512 256 = 28972398061922904266377214144 :=
  phaseBlock_append receipt_3_15_2359_0_part4 receipt_3_15_2359_0_part5 rfl rfl rfl
private theorem receipt_3_15_2359_0_join4 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 768 256 = 22518516925181940306681198784 :=
  phaseBlock_append receipt_3_15_2359_0_part6 receipt_3_15_2359_0_part7 rfl rfl rfl
private theorem receipt_3_15_2359_0_join5 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 512 512 = 51490914987104844573058412928 :=
  phaseBlock_append receipt_3_15_2359_0_join3 receipt_3_15_2359_0_join4 rfl rfl rfl
private theorem receipt_3_15_2359_0_join6 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 0 1024 = 130560315372466978834619917056 :=
  phaseBlock_append receipt_3_15_2359_0_join2 receipt_3_15_2359_0_join5 rfl rfl rfl
private theorem receipt_3_15_2359_0_join7 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 1024 256 = 16525166151286401743487154368 :=
  phaseBlock_append receipt_3_15_2359_0_part8 receipt_3_15_2359_0_part9 rfl rfl rfl
private theorem receipt_3_15_2359_0_join8 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 1280 256 = 11007957341289011118187641024 :=
  phaseBlock_append receipt_3_15_2359_0_part10 receipt_3_15_2359_0_part11 rfl rfl rfl
private theorem receipt_3_15_2359_0_join9 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 1024 512 = 27533123492575412861674795392 :=
  phaseBlock_append receipt_3_15_2359_0_join7 receipt_3_15_2359_0_join8 rfl rfl rfl
private theorem receipt_3_15_2359_0_join10 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 1536 256 = 5982319036363080517149407424 :=
  phaseBlock_append receipt_3_15_2359_0_part12 receipt_3_15_2359_0_part13 rfl rfl rfl
private theorem receipt_3_15_2359_0_join11 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 1792 216 = 1511730135739865811856401882 :=
  phaseBlock_append receipt_3_15_2359_0_part14 receipt_3_15_2359_0_part15 rfl rfl rfl
private theorem receipt_3_15_2359_0_join12 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 1536 472 = 7494049172102946329005809306 :=
  phaseBlock_append receipt_3_15_2359_0_join10 receipt_3_15_2359_0_join11 rfl rfl rfl
private theorem receipt_3_15_2359_0_join13 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 1024 984 = 35027172664678359190680604698 :=
  phaseBlock_append receipt_3_15_2359_0_join9 receipt_3_15_2359_0_join12 rfl rfl rfl
private theorem receipt_3_15_2359_0_join14 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 0) 0 2008 = 165587488037145338025300521754 :=
  phaseBlock_append receipt_3_15_2359_0_join6 receipt_3_15_2359_0_join13 rfl rfl rfl

private theorem receipt_3_15_2359_0 : fastPhase (bank 3 15).shape 179818 2359 76 1 1 1 0 = 165587488037145338025300521754 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_15_2359_0_join14

private theorem receipt_3_15_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 0 128 = 22526560605115885826612287200 := by decide +kernel
private theorem receipt_3_15_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 128 128 = 20642767082650476636939994848 := by decide +kernel
private theorem receipt_3_15_2359_1_part2 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 256 128 = 18811065507849130008194397920 := by decide +kernel
private theorem receipt_3_15_2359_1_part3 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 384 128 = 17032466104113021229293807328 := by decide +kernel
private theorem receipt_3_15_2359_1_part4 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 512 128 = 15307973312845607894723598048 := by decide +kernel
private theorem receipt_3_15_2359_1_part5 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 640 128 = 13638585802906978548061144800 := by decide +kernel
private theorem receipt_3_15_2359_1_part6 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 768 128 = 12025296480068201325500757728 := by decide +kernel
private theorem receipt_3_15_2359_1_part7 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 896 128 = 10469092496465672599378618080 := by decide +kernel
private theorem receipt_3_15_2359_1_part8 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 1024 128 = 8970955260055465621697713888 := by decide +kernel
private theorem receipt_3_15_2359_1_part9 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 1152 128 = 7531860444067679167652775648 := by decide +kernel
private theorem receipt_3_15_2359_1_part10 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 1280 128 = 6152777996460786179155212000 := by decide +kernel
private theorem receipt_3_15_2359_1_part11 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 1408 128 = 4834672149375982408358045408 := by decide +kernel
private theorem receipt_3_15_2359_1_part12 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 1536 128 = 3578501428591535061180847840 := by decide +kernel
private theorem receipt_3_15_2359_1_part13 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 1664 128 = 2385218662977131440834676448 := by decide +kernel
private theorem receipt_3_15_2359_1_part14 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 1792 128 = 1255770993948227591347009248 := by decide +kernel
private theorem receipt_3_15_2359_1_part15 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 1920 88 = 241797975017779440567054066 := by decide +kernel
private theorem receipt_3_15_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 0 256 = 43169327687766362463552282048 :=
  phaseBlock_append receipt_3_15_2359_1_part0 receipt_3_15_2359_1_part1 rfl rfl rfl
private theorem receipt_3_15_2359_1_join1 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 256 256 = 35843531611962151237488205248 :=
  phaseBlock_append receipt_3_15_2359_1_part2 receipt_3_15_2359_1_part3 rfl rfl rfl
private theorem receipt_3_15_2359_1_join2 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 0 512 = 79012859299728513701040487296 :=
  phaseBlock_append receipt_3_15_2359_1_join0 receipt_3_15_2359_1_join1 rfl rfl rfl
private theorem receipt_3_15_2359_1_join3 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 512 256 = 28946559115752586442784742848 :=
  phaseBlock_append receipt_3_15_2359_1_part4 receipt_3_15_2359_1_part5 rfl rfl rfl
private theorem receipt_3_15_2359_1_join4 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 768 256 = 22494388976533873924879375808 :=
  phaseBlock_append receipt_3_15_2359_1_part6 receipt_3_15_2359_1_part7 rfl rfl rfl
private theorem receipt_3_15_2359_1_join5 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 512 512 = 51440948092286460367664118656 :=
  phaseBlock_append receipt_3_15_2359_1_join3 receipt_3_15_2359_1_join4 rfl rfl rfl
private theorem receipt_3_15_2359_1_join6 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 0 1024 = 130453807392014974068704605952 :=
  phaseBlock_append receipt_3_15_2359_1_join2 receipt_3_15_2359_1_join5 rfl rfl rfl
private theorem receipt_3_15_2359_1_join7 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 1024 256 = 16502815704123144789350489536 :=
  phaseBlock_append receipt_3_15_2359_1_part8 receipt_3_15_2359_1_part9 rfl rfl rfl
private theorem receipt_3_15_2359_1_join8 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 1280 256 = 10987450145836768587513257408 :=
  phaseBlock_append receipt_3_15_2359_1_part10 receipt_3_15_2359_1_part11 rfl rfl rfl
private theorem receipt_3_15_2359_1_join9 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 1024 512 = 27490265849959913376863746944 :=
  phaseBlock_append receipt_3_15_2359_1_join7 receipt_3_15_2359_1_join8 rfl rfl rfl
private theorem receipt_3_15_2359_1_join10 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 1536 256 = 5963720091568666502015524288 :=
  phaseBlock_append receipt_3_15_2359_1_part12 receipt_3_15_2359_1_part13 rfl rfl rfl
private theorem receipt_3_15_2359_1_join11 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 1792 216 = 1497568968966007031914063314 :=
  phaseBlock_append receipt_3_15_2359_1_part14 receipt_3_15_2359_1_part15 rfl rfl rfl
private theorem receipt_3_15_2359_1_join12 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 1536 472 = 7461289060534673533929587602 :=
  phaseBlock_append receipt_3_15_2359_1_join10 receipt_3_15_2359_1_join11 rfl rfl rfl
private theorem receipt_3_15_2359_1_join13 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 1024 984 = 34951554910494586910793334546 :=
  phaseBlock_append receipt_3_15_2359_1_join9 receipt_3_15_2359_1_join12 rfl rfl rfl
private theorem receipt_3_15_2359_1_join14 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2359 76 1 1 1 1) 0 2008 = 165405362302509560979497940498 :=
  phaseBlock_append receipt_3_15_2359_1_join6 receipt_3_15_2359_1_join13 rfl rfl rfl

private theorem receipt_3_15_2359_1 : fastPhase (bank 3 15).shape 179818 2359 76 1 1 1 1 = 165405362302509560979497940498 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_15_2359_1_join14

private theorem receipt_3_15_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 0 128 = 22541483226047189567598342816 := by decide +kernel
private theorem receipt_3_15_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 128 128 = 20657275545885967263810028192 := by decide +kernel
private theorem receipt_3_15_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 256 128 = 18825153960140317036395188896 := by decide +kernel
private theorem receipt_3_15_2360_0_part3 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 384 128 = 17046128618681842619782865568 := by decide +kernel
private theorem receipt_3_15_2360_0_part4 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 512 128 = 15321203889879106863655875232 := by decide +kernel
private theorem receipt_3_15_2360_0_part5 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 640 128 = 13651378370051100767173526176 := by decide +kernel
private theorem receipt_3_15_2360_0_part6 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 768 128 = 12037644892920712513194332832 := by decide +kernel
private theorem receipt_3_15_2360_0_part7 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 896 128 = 10480990539068196502498730656 := by decide +kernel
private theorem receipt_3_15_2360_0_part8 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 1024 128 = 8982396645384642388011791008 := by decide +kernel
private theorem receipt_3_15_2360_0_part9 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 1152 128 = 7542838814525444109025936032 := by decide +kernel
private theorem receipt_3_15_2360_0_part10 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 1280 128 = 6163286924363768925423653536 := by decide +kernel
private theorem receipt_3_15_2360_0_part11 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 1408 128 = 4844705137444026451900211872 := by decide +kernel
private theorem receipt_3_15_2360_0_part12 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 1536 128 = 3588051910435337692186374816 := by decide +kernel
private theorem receipt_3_15_2360_0_part13 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 1664 128 = 2394280003585004073271116448 := by decide +kernel
private theorem receipt_3_15_2360_0_part14 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 1792 128 = 1264336490171976479624336032 := by decide +kernel
private theorem receipt_3_15_2360_0_part15 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 1920 88 = 247395609454437618717817142 := by decide +kernel
private theorem receipt_3_15_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 0 256 = 43198758771933156831408371008 :=
  phaseBlock_append receipt_3_15_2360_0_part0 receipt_3_15_2360_0_part1 rfl rfl rfl
private theorem receipt_3_15_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 256 256 = 35871282578822159656178054464 :=
  phaseBlock_append receipt_3_15_2360_0_part2 receipt_3_15_2360_0_part3 rfl rfl rfl
private theorem receipt_3_15_2360_0_join2 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 0 512 = 79070041350755316487586425472 :=
  phaseBlock_append receipt_3_15_2360_0_join0 receipt_3_15_2360_0_join1 rfl rfl rfl
private theorem receipt_3_15_2360_0_join3 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 512 256 = 28972582259930207630829401408 :=
  phaseBlock_append receipt_3_15_2360_0_part4 receipt_3_15_2360_0_part5 rfl rfl rfl
private theorem receipt_3_15_2360_0_join4 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 768 256 = 22518635431988909015693063488 :=
  phaseBlock_append receipt_3_15_2360_0_part6 receipt_3_15_2360_0_part7 rfl rfl rfl
private theorem receipt_3_15_2360_0_join5 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 512 512 = 51491217691919116646522464896 :=
  phaseBlock_append receipt_3_15_2360_0_join3 receipt_3_15_2360_0_join4 rfl rfl rfl
private theorem receipt_3_15_2360_0_join6 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 0 1024 = 130561259042674433134108890368 :=
  phaseBlock_append receipt_3_15_2360_0_join2 receipt_3_15_2360_0_join5 rfl rfl rfl
private theorem receipt_3_15_2360_0_join7 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 1024 256 = 16525235459910086497037727040 :=
  phaseBlock_append receipt_3_15_2360_0_part8 receipt_3_15_2360_0_part9 rfl rfl rfl
private theorem receipt_3_15_2360_0_join8 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 1280 256 = 11007992061807795377323865408 :=
  phaseBlock_append receipt_3_15_2360_0_part10 receipt_3_15_2360_0_part11 rfl rfl rfl
private theorem receipt_3_15_2360_0_join9 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 1024 512 = 27533227521717881874361592448 :=
  phaseBlock_append receipt_3_15_2360_0_join7 receipt_3_15_2360_0_join8 rfl rfl rfl
private theorem receipt_3_15_2360_0_join10 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 1536 256 = 5982331914020341765457491264 :=
  phaseBlock_append receipt_3_15_2360_0_part12 receipt_3_15_2360_0_part13 rfl rfl rfl
private theorem receipt_3_15_2360_0_join11 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 1792 216 = 1511732099626414098342153174 :=
  phaseBlock_append receipt_3_15_2360_0_part14 receipt_3_15_2360_0_part15 rfl rfl rfl
private theorem receipt_3_15_2360_0_join12 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 1536 472 = 7494064013646755863799644438 :=
  phaseBlock_append receipt_3_15_2360_0_join10 receipt_3_15_2360_0_join11 rfl rfl rfl
private theorem receipt_3_15_2360_0_join13 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 1024 984 = 35027291535364637738161236886 :=
  phaseBlock_append receipt_3_15_2360_0_join9 receipt_3_15_2360_0_join12 rfl rfl rfl
private theorem receipt_3_15_2360_0_join14 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 0) 0 2008 = 165588550578039070872270127254 :=
  phaseBlock_append receipt_3_15_2360_0_join6 receipt_3_15_2360_0_join13 rfl rfl rfl

private theorem receipt_3_15_2360_0 : fastPhase (bank 3 15).shape 179818 2360 76 1 1 1 0 = 165588550578039070872270127254 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_15_2360_0_join14

private theorem receipt_3_15_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 0 128 = 22526761189006550023634018976 := by decide +kernel
private theorem receipt_3_15_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 128 128 = 20642938890992555317121151648 := by decide +kernel
private theorem receipt_3_15_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 256 128 = 18811211260371950225822515872 := by decide +kernel
private theorem receipt_3_15_2360_1_part3 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 384 128 = 17032588399450603479525986976 := by decide +kernel
private theorem receipt_3_15_2360_1_part4 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 512 128 = 15308074629108117353474826912 := by decide +kernel
private theorem receipt_3_15_2360_1_part5 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 640 128 = 13638668498251296702590399136 := by decide +kernel
private theorem receipt_3_15_2360_1_part6 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 768 128 = 12025362793267617995694883488 := by decide +kernel
private theorem receipt_3_15_2360_1_part7 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 896 128 = 10469144547478698349733991072 := by decide +kernel
private theorem receipt_3_15_2360_1_part8 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 1024 128 = 8970995050593764563999679136 := by decide +kernel
private theorem receipt_3_15_2360_1_part9 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 1152 128 = 7531889858163122154352865952 := by decide +kernel
private theorem receipt_3_15_2360_1_part10 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 1280 128 = 6152798801031624387446145696 := by decide +kernel
private theorem receipt_3_15_2360_1_part11 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 1408 128 = 4834685994792141314946503328 := by decide +kernel
private theorem receipt_3_15_2360_1_part12 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 1536 128 = 3578509849239028807758029472 := by decide +kernel
private theorem receipt_3_15_2360_1_part13 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 1664 128 = 2385223077821597590244635296 := by decide +kernel
private theorem receipt_3_15_2360_1_part14 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 1792 128 = 1255772707097582274452767392 := by decide +kernel
private theorem receipt_3_15_2360_1_part15 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 1920 88 = 241798208526844730386208022 := by decide +kernel
private theorem receipt_3_15_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 0 256 = 43169700079999105340755170624 :=
  phaseBlock_append receipt_3_15_2360_1_part0 receipt_3_15_2360_1_part1 rfl rfl rfl
private theorem receipt_3_15_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 256 256 = 35843799659822553705348502848 :=
  phaseBlock_append receipt_3_15_2360_1_part2 receipt_3_15_2360_1_part3 rfl rfl rfl
private theorem receipt_3_15_2360_1_join2 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 0 512 = 79013499739821659046103673472 :=
  phaseBlock_append receipt_3_15_2360_1_join0 receipt_3_15_2360_1_join1 rfl rfl rfl
private theorem receipt_3_15_2360_1_join3 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 512 256 = 28946743127359414056065226048 :=
  phaseBlock_append receipt_3_15_2360_1_part4 receipt_3_15_2360_1_part5 rfl rfl rfl
private theorem receipt_3_15_2360_1_join4 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 768 256 = 22494507340746316345428874560 :=
  phaseBlock_append receipt_3_15_2360_1_part6 receipt_3_15_2360_1_part7 rfl rfl rfl
private theorem receipt_3_15_2360_1_join5 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 512 512 = 51441250468105730401494100608 :=
  phaseBlock_append receipt_3_15_2360_1_join3 receipt_3_15_2360_1_join4 rfl rfl rfl
private theorem receipt_3_15_2360_1_join6 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 0 1024 = 130454750207927389447597774080 :=
  phaseBlock_append receipt_3_15_2360_1_join2 receipt_3_15_2360_1_join5 rfl rfl rfl
private theorem receipt_3_15_2360_1_join7 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 1024 256 = 16502884908756886718352545088 :=
  phaseBlock_append receipt_3_15_2360_1_part8 receipt_3_15_2360_1_part9 rfl rfl rfl
private theorem receipt_3_15_2360_1_join8 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 1280 256 = 10987484795823765702392649024 :=
  phaseBlock_append receipt_3_15_2360_1_part10 receipt_3_15_2360_1_part11 rfl rfl rfl
private theorem receipt_3_15_2360_1_join9 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 1024 512 = 27490369704580652420745194112 :=
  phaseBlock_append receipt_3_15_2360_1_join7 receipt_3_15_2360_1_join8 rfl rfl rfl
private theorem receipt_3_15_2360_1_join10 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 1536 256 = 5963732927060626398002664768 :=
  phaseBlock_append receipt_3_15_2360_1_part12 receipt_3_15_2360_1_part13 rfl rfl rfl
private theorem receipt_3_15_2360_1_join11 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 1792 216 = 1497570915624427004838975414 :=
  phaseBlock_append receipt_3_15_2360_1_part14 receipt_3_15_2360_1_part15 rfl rfl rfl
private theorem receipt_3_15_2360_1_join12 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 1536 472 = 7461303842685053402841640182 :=
  phaseBlock_append receipt_3_15_2360_1_join10 receipt_3_15_2360_1_join11 rfl rfl rfl
private theorem receipt_3_15_2360_1_join13 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 1024 984 = 34951673547265705823586834294 :=
  phaseBlock_append receipt_3_15_2360_1_join9 receipt_3_15_2360_1_join12 rfl rfl rfl
private theorem receipt_3_15_2360_1_join14 :
    phaseBlock (fastLayer (bank 3 15).shape 179818 2360 76 1 1 1 1) 0 2008 = 165406423755193095271184608374 :=
  phaseBlock_append receipt_3_15_2360_1_join6 receipt_3_15_2360_1_join13 rfl rfl rfl

private theorem receipt_3_15_2360_1 : fastPhase (bank 3 15).shape 179818 2360 76 1 1 1 1 = 165406423755193095271184608374 :=
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
    (word : K1.I → K1_14.L) (lo : 2359 ≤ h) (hi : h ≤ 33579) (rect : Fin 4)
    (i : Fin 1) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group6_stage i)).shape
      (cutoff h rect (group6_stage i)), ¬ G∣Q :=
  (group6_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group6_avoids

end Lower6960.RescueSource
