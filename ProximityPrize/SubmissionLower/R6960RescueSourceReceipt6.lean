import ProximityPrize.SubmissionLower.R6960RescueSourceSchedule

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open HelperSource (WidthGuard)

private theorem moment_9204_1934_part0 :
    blockEstimate 9204 1934 1934 128 = 3258746400 := rfl
private theorem moment_9204_1934_part1 :
    blockEstimate 9204 1934 2062 128 = 22238828064 := rfl
private theorem moment_9204_1934_part2 :
    blockEstimate 9204 1934 2190 128 = 59309991456 := rfl
private theorem moment_9204_1934_part3 :
    blockEstimate 9204 1934 2318 128 = 113666930208 := rfl
private theorem moment_9204_1934_part4 :
    blockEstimate 9204 1934 2446 128 = 184504337952 := rfl
private theorem moment_9204_1934_part5 :
    blockEstimate 9204 1934 2574 128 = 271016908320 := rfl
private theorem moment_9204_1934_part6 :
    blockEstimate 9204 1934 2702 128 = 372399334944 := rfl
private theorem moment_9204_1934_part7 :
    blockEstimate 9204 1934 2830 128 = 487846311456 := rfl
private theorem moment_9204_1934_part8 :
    blockEstimate 9204 1934 2958 128 = 616552531488 := rfl
private theorem moment_9204_1934_part9 :
    blockEstimate 9204 1934 3086 128 = 757712688672 := rfl
private theorem moment_9204_1934_part10 :
    blockEstimate 9204 1934 3214 128 = 910521476640 := rfl
private theorem moment_9204_1934_part11 :
    blockEstimate 9204 1934 3342 128 = 1074173589024 := rfl
private theorem moment_9204_1934_part12 :
    blockEstimate 9204 1934 3470 128 = 1247863719456 := rfl
private theorem moment_9204_1934_part13 :
    blockEstimate 9204 1934 3598 128 = 1430786561568 := rfl
private theorem moment_9204_1934_part14 :
    blockEstimate 9204 1934 3726 128 = 1622136808992 := rfl
private theorem moment_9204_1934_part15 :
    blockEstimate 9204 1934 3854 128 = 1819335142935 := rfl
private theorem moment_9204_1934_part16 :
    blockEstimate 9204 1934 3982 128 = 2011927798080 := rfl
private theorem moment_9204_1934_part17 :
    blockEstimate 9204 1934 4110 128 = 2196407787840 := rfl
private theorem moment_9204_1934_part18 :
    blockEstimate 9204 1934 4238 128 = 2372771799360 := rfl
private theorem moment_9204_1934_part19 :
    blockEstimate 9204 1934 4366 128 = 2541019832640 := rfl
private theorem moment_9204_1934_part20 :
    blockEstimate 9204 1934 4494 128 = 2701151887680 := rfl
private theorem moment_9204_1934_part21 :
    blockEstimate 9204 1934 4622 128 = 2853167964480 := rfl
private theorem moment_9204_1934_part22 :
    blockEstimate 9204 1934 4750 128 = 2997068063040 := rfl
private theorem moment_9204_1934_part23 :
    blockEstimate 9204 1934 4878 128 = 3132852183360 := rfl
private theorem moment_9204_1934_part24 :
    blockEstimate 9204 1934 5006 128 = 3260520325440 := rfl
private theorem moment_9204_1934_part25 :
    blockEstimate 9204 1934 5134 128 = 3380072489280 := rfl
private theorem moment_9204_1934_part26 :
    blockEstimate 9204 1934 5262 128 = 3491508674880 := rfl
private theorem moment_9204_1934_part27 :
    blockEstimate 9204 1934 5390 128 = 3594828882240 := rfl
private theorem moment_9204_1934_part28 :
    blockEstimate 9204 1934 5518 128 = 3690033111360 := rfl
private theorem moment_9204_1934_part29 :
    blockEstimate 9204 1934 5646 128 = 3777121362240 := rfl
private theorem moment_9204_1934_part30 :
    blockEstimate 9204 1934 5774 128 = 3856093634880 := rfl
private theorem moment_9204_1934_part31 :
    blockEstimate 9204 1934 5902 128 = 3926949929280 := rfl
private theorem moment_9204_1934_part32 :
    blockEstimate 9204 1934 6030 128 = 3989690245440 := rfl
private theorem moment_9204_1934_part33 :
    blockEstimate 9204 1934 6158 128 = 4044314583360 := rfl
private theorem moment_9204_1934_part34 :
    blockEstimate 9204 1934 6286 128 = 4090822943040 := rfl
private theorem moment_9204_1934_part35 :
    blockEstimate 9204 1934 6414 128 = 4129215324480 := rfl
private theorem moment_9204_1934_part36 :
    blockEstimate 9204 1934 6542 128 = 4159491727680 := rfl
private theorem moment_9204_1934_part37 :
    blockEstimate 9204 1934 6670 128 = 4181652152640 := rfl
private theorem moment_9204_1934_part38 :
    blockEstimate 9204 1934 6798 128 = 4195696599360 := rfl
private theorem moment_9204_1934_part39 :
    blockEstimate 9204 1934 6926 128 = 4201625067840 := rfl
private theorem moment_9204_1934_part40 :
    blockEstimate 9204 1934 7054 128 = 4199437558080 := rfl
private theorem moment_9204_1934_part41 :
    blockEstimate 9204 1934 7182 128 = 4189134070080 := rfl
private theorem moment_9204_1934_part42 :
    blockEstimate 9204 1934 7310 128 = 4170714603840 := rfl
private theorem moment_9204_1934_part43 :
    blockEstimate 9204 1934 7438 128 = 4144179159360 := rfl
private theorem moment_9204_1934_part44 :
    blockEstimate 9204 1934 7566 128 = 4109527736640 := rfl
private theorem moment_9204_1934_part45 :
    blockEstimate 9204 1934 7694 128 = 4066760335680 := rfl
private theorem moment_9204_1934_part46 :
    blockEstimate 9204 1934 7822 128 = 4015876956480 := rfl
private theorem moment_9204_1934_part47 :
    blockEstimate 9204 1934 7950 128 = 3956877599040 := rfl
private theorem moment_9204_1934_part48 :
    blockEstimate 9204 1934 8078 128 = 3889762263360 := rfl
private theorem moment_9204_1934_part49 :
    blockEstimate 9204 1934 8206 128 = 3814530949440 := rfl
private theorem moment_9204_1934_part50 :
    blockEstimate 9204 1934 8334 128 = 3731183657280 := rfl
private theorem moment_9204_1934_part51 :
    blockEstimate 9204 1934 8462 128 = 3639720386880 := rfl
private theorem moment_9204_1934_part52 :
    blockEstimate 9204 1934 8590 128 = 3540141138240 := rfl
private theorem moment_9204_1934_part53 :
    blockEstimate 9204 1934 8718 128 = 3432445911360 := rfl
private theorem moment_9204_1934_part54 :
    blockEstimate 9204 1934 8846 128 = 3316634706240 := rfl
private theorem moment_9204_1934_part55 :
    blockEstimate 9204 1934 8974 128 = 3192707522880 := rfl
private theorem moment_9204_1934_part56 :
    blockEstimate 9204 1934 9102 128 = 3060672660662 := rfl
private theorem moment_9204_1934_part57 :
    blockEstimate 9204 1934 9230 128 = 2922189666835 := rfl
private theorem moment_9204_1934_part58 :
    blockEstimate 9204 1934 9358 128 = 2781152560075 := rfl
private theorem moment_9204_1934_part59 :
    blockEstimate 9204 1934 9486 128 = 2638604095811 := rfl
private theorem moment_9204_1934_part60 :
    blockEstimate 9204 1934 9614 128 = 2495118862611 := rfl
private theorem moment_9204_1934_part61 :
    blockEstimate 9204 1934 9742 128 = 2351258128260 := rfl
private theorem moment_9204_1934_part62 :
    blockEstimate 9204 1934 9870 128 = 2207569845614 := rfl
private theorem moment_9204_1934_part63 :
    blockEstimate 9204 1934 9998 128 = 2064588648047 := rfl
private theorem moment_9204_1934_part64 :
    blockEstimate 9204 1934 10126 128 = 1922835851962 := rfl
private theorem moment_9204_1934_part65 :
    blockEstimate 9204 1934 10254 128 = 1782819456131 := rfl
private theorem moment_9204_1934_part66 :
    blockEstimate 9204 1934 10382 128 = 1645034141248 := rfl
private theorem moment_9204_1934_part67 :
    blockEstimate 9204 1934 10510 128 = 1509961269335 := rfl
private theorem moment_9204_1934_part68 :
    blockEstimate 9204 1934 10638 128 = 1378068887308 := rfl
private theorem moment_9204_1934_part69 :
    blockEstimate 9204 1934 10766 128 = 1249811721549 := rfl
private theorem moment_9204_1934_part70 :
    blockEstimate 9204 1934 10894 128 = 1125631182398 := rfl
private theorem moment_9204_1934_part71 :
    blockEstimate 9204 1934 11022 128 = 1005946333810 := rfl
private theorem moment_9204_1934_part72 :
    blockEstimate 9204 1934 11150 128 = 890209793520 := rfl
private theorem moment_9204_1934_part73 :
    blockEstimate 9204 1934 11278 128 = 779590273520 := rfl
private theorem moment_9204_1934_part74 :
    blockEstimate 9204 1934 11406 128 = 675219021296 := rfl
private theorem moment_9204_1934_part75 :
    blockEstimate 9204 1934 11534 128 = 577347695088 := rfl
private theorem moment_9204_1934_part76 :
    blockEstimate 9204 1934 11662 128 = 486227953136 := rfl
private theorem moment_9204_1934_part77 :
    blockEstimate 9204 1934 11790 128 = 402111453680 := rfl
private theorem moment_9204_1934_part78 :
    blockEstimate 9204 1934 11918 128 = 325249854960 := rfl
private theorem moment_9204_1934_part79 :
    blockEstimate 9204 1934 12046 128 = 255894815216 := rfl
private theorem moment_9204_1934_part80 :
    blockEstimate 9204 1934 12174 128 = 194297992688 := rfl
private theorem moment_9204_1934_part81 :
    blockEstimate 9204 1934 12302 128 = 140711045616 := rfl
private theorem moment_9204_1934_part82 :
    blockEstimate 9204 1934 12430 128 = 95385632240 := rfl
private theorem moment_9204_1934_part83 :
    blockEstimate 9204 1934 12558 128 = 58573410800 := rfl
private theorem moment_9204_1934_part84 :
    blockEstimate 9204 1934 12686 128 = 30526039536 := rfl
private theorem moment_9204_1934_part85 :
    blockEstimate 9204 1934 12814 128 = 11495176688 := rfl
private theorem moment_9204_1934_part86 :
    blockEstimate 9204 1934 12942 128 = 1732480496 := rfl
private theorem moment_9204_1934_part87 :
    blockEstimate 9204 1934 13070 2 = 27611 := rfl
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
    blockEstimate 9204 2007 2007 128 = 3258746400 := rfl
private theorem moment_9204_2007_part1 :
    blockEstimate 9204 2007 2135 128 = 22238828064 := rfl
private theorem moment_9204_2007_part2 :
    blockEstimate 9204 2007 2263 128 = 59309991456 := rfl
private theorem moment_9204_2007_part3 :
    blockEstimate 9204 2007 2391 128 = 113666930208 := rfl
private theorem moment_9204_2007_part4 :
    blockEstimate 9204 2007 2519 128 = 184504337952 := rfl
private theorem moment_9204_2007_part5 :
    blockEstimate 9204 2007 2647 128 = 271016908320 := rfl
private theorem moment_9204_2007_part6 :
    blockEstimate 9204 2007 2775 128 = 372399334944 := rfl
private theorem moment_9204_2007_part7 :
    blockEstimate 9204 2007 2903 128 = 487846311456 := rfl
private theorem moment_9204_2007_part8 :
    blockEstimate 9204 2007 3031 128 = 616552531488 := rfl
private theorem moment_9204_2007_part9 :
    blockEstimate 9204 2007 3159 128 = 757712688672 := rfl
private theorem moment_9204_2007_part10 :
    blockEstimate 9204 2007 3287 128 = 910521476640 := rfl
private theorem moment_9204_2007_part11 :
    blockEstimate 9204 2007 3415 128 = 1074173589024 := rfl
private theorem moment_9204_2007_part12 :
    blockEstimate 9204 2007 3543 128 = 1247863719456 := rfl
private theorem moment_9204_2007_part13 :
    blockEstimate 9204 2007 3671 128 = 1430786561568 := rfl
private theorem moment_9204_2007_part14 :
    blockEstimate 9204 2007 3799 128 = 1622136808992 := rfl
private theorem moment_9204_2007_part15 :
    blockEstimate 9204 2007 3927 128 = 1821026881070 := rfl
private theorem moment_9204_2007_part16 :
    blockEstimate 9204 2007 4055 128 = 2021292574464 := rfl
private theorem moment_9204_2007_part17 :
    blockEstimate 9204 2007 4183 128 = 2213933090560 := rfl
private theorem moment_9204_2007_part18 :
    blockEstimate 9204 2007 4311 128 = 2398151444224 := rfl
private theorem moment_9204_2007_part19 :
    blockEstimate 9204 2007 4439 128 = 2573947635456 := rfl
private theorem moment_9204_2007_part20 :
    blockEstimate 9204 2007 4567 128 = 2741321664256 := rfl
private theorem moment_9204_2007_part21 :
    blockEstimate 9204 2007 4695 128 = 2900273530624 := rfl
private theorem moment_9204_2007_part22 :
    blockEstimate 9204 2007 4823 128 = 3050803234560 := rfl
private theorem moment_9204_2007_part23 :
    blockEstimate 9204 2007 4951 128 = 3192910776064 := rfl
private theorem moment_9204_2007_part24 :
    blockEstimate 9204 2007 5079 128 = 3326596155136 := rfl
private theorem moment_9204_2007_part25 :
    blockEstimate 9204 2007 5207 128 = 3451859371776 := rfl
private theorem moment_9204_2007_part26 :
    blockEstimate 9204 2007 5335 128 = 3568700425984 := rfl
private theorem moment_9204_2007_part27 :
    blockEstimate 9204 2007 5463 128 = 3677119317760 := rfl
private theorem moment_9204_2007_part28 :
    blockEstimate 9204 2007 5591 128 = 3777116047104 := rfl
private theorem moment_9204_2007_part29 :
    blockEstimate 9204 2007 5719 128 = 3868690614016 := rfl
private theorem moment_9204_2007_part30 :
    blockEstimate 9204 2007 5847 128 = 3951843018496 := rfl
private theorem moment_9204_2007_part31 :
    blockEstimate 9204 2007 5975 128 = 4026573260544 := rfl
private theorem moment_9204_2007_part32 :
    blockEstimate 9204 2007 6103 128 = 4092881340160 := rfl
private theorem moment_9204_2007_part33 :
    blockEstimate 9204 2007 6231 128 = 4150767257344 := rfl
private theorem moment_9204_2007_part34 :
    blockEstimate 9204 2007 6359 128 = 4200231012096 := rfl
private theorem moment_9204_2007_part35 :
    blockEstimate 9204 2007 6487 128 = 4241272604416 := rfl
private theorem moment_9204_2007_part36 :
    blockEstimate 9204 2007 6615 128 = 4273892034304 := rfl
private theorem moment_9204_2007_part37 :
    blockEstimate 9204 2007 6743 128 = 4298089301760 := rfl
private theorem moment_9204_2007_part38 :
    blockEstimate 9204 2007 6871 128 = 4313864406784 := rfl
private theorem moment_9204_2007_part39 :
    blockEstimate 9204 2007 6999 128 = 4321217349376 := rfl
private theorem moment_9204_2007_part40 :
    blockEstimate 9204 2007 7127 128 = 4320148129536 := rfl
private theorem moment_9204_2007_part41 :
    blockEstimate 9204 2007 7255 128 = 4310656747264 := rfl
private theorem moment_9204_2007_part42 :
    blockEstimate 9204 2007 7383 128 = 4292743202560 := rfl
private theorem moment_9204_2007_part43 :
    blockEstimate 9204 2007 7511 128 = 4266407495424 := rfl
private theorem moment_9204_2007_part44 :
    blockEstimate 9204 2007 7639 128 = 4231649625856 := rfl
private theorem moment_9204_2007_part45 :
    blockEstimate 9204 2007 7767 128 = 4188469593856 := rfl
private theorem moment_9204_2007_part46 :
    blockEstimate 9204 2007 7895 128 = 4136867399424 := rfl
private theorem moment_9204_2007_part47 :
    blockEstimate 9204 2007 8023 128 = 4076843042560 := rfl
private theorem moment_9204_2007_part48 :
    blockEstimate 9204 2007 8151 128 = 4008396523264 := rfl
private theorem moment_9204_2007_part49 :
    blockEstimate 9204 2007 8279 128 = 3931527841536 := rfl
private theorem moment_9204_2007_part50 :
    blockEstimate 9204 2007 8407 128 = 3846236997376 := rfl
private theorem moment_9204_2007_part51 :
    blockEstimate 9204 2007 8535 128 = 3752523990784 := rfl
private theorem moment_9204_2007_part52 :
    blockEstimate 9204 2007 8663 128 = 3650388821760 := rfl
private theorem moment_9204_2007_part53 :
    blockEstimate 9204 2007 8791 128 = 3539831490304 := rfl
private theorem moment_9204_2007_part54 :
    blockEstimate 9204 2007 8919 128 = 3420851996416 := rfl
private theorem moment_9204_2007_part55 :
    blockEstimate 9204 2007 9047 128 = 3293450340096 := rfl
private theorem moment_9204_2007_part56 :
    blockEstimate 9204 2007 9175 128 = 3158061593754 := rfl
private theorem moment_9204_2007_part57 :
    blockEstimate 9204 2007 9303 128 = 3018286486228 := rfl
private theorem moment_9204_2007_part58 :
    blockEstimate 9204 2007 9431 128 = 2876280298777 := rfl
private theorem moment_9204_2007_part59 :
    blockEstimate 9204 2007 9559 128 = 2732634120428 := rfl
private theorem moment_9204_2007_part60 :
    blockEstimate 9204 2007 9687 128 = 2587916286557 := rfl
private theorem moment_9204_2007_part61 :
    blockEstimate 9204 2007 9815 128 = 2442682301637 := rfl
private theorem moment_9204_2007_part62 :
    blockEstimate 9204 2007 9943 128 = 2297474834023 := rfl
private theorem moment_9204_2007_part63 :
    blockEstimate 9204 2007 10071 128 = 2152823720748 := rfl
private theorem moment_9204_2007_part64 :
    blockEstimate 9204 2007 10199 128 = 2009245963108 := rfl
private theorem moment_9204_2007_part65 :
    blockEstimate 9204 2007 10327 128 = 1867245729694 := rfl
private theorem moment_9204_2007_part66 :
    blockEstimate 9204 2007 10455 128 = 1727314356507 := rfl
private theorem moment_9204_2007_part67 :
    blockEstimate 9204 2007 10583 128 = 1589930344406 := rfl
private theorem moment_9204_2007_part68 :
    blockEstimate 9204 2007 10711 128 = 1455559361812 := rfl
private theorem moment_9204_2007_part69 :
    blockEstimate 9204 2007 10839 128 = 1324654242939 := rfl
private theorem moment_9204_2007_part70 :
    blockEstimate 9204 2007 10967 128 = 1197654988582 := rfl
private theorem moment_9204_2007_part71 :
    blockEstimate 9204 2007 11095 128 = 1074979041323 := rfl
private theorem moment_9204_2007_part72 :
    blockEstimate 9204 2007 11223 128 = 955998817152 := rfl
private theorem moment_9204_2007_part73 :
    blockEstimate 9204 2007 11351 128 = 841928520576 := rfl
private theorem moment_9204_2007_part74 :
    blockEstimate 9204 2007 11479 128 = 733962967936 := rfl
private theorem moment_9204_2007_part75 :
    blockEstimate 9204 2007 11607 128 = 632353817472 := rfl
private theorem moment_9204_2007_part76 :
    blockEstimate 9204 2007 11735 128 = 537352727424 := rfl
private theorem moment_9204_2007_part77 :
    blockEstimate 9204 2007 11863 128 = 449211356032 := rfl
private theorem moment_9204_2007_part78 :
    blockEstimate 9204 2007 11991 128 = 368181361536 := rfl
private theorem moment_9204_2007_part79 :
    blockEstimate 9204 2007 12119 128 = 294514402176 := rfl
private theorem moment_9204_2007_part80 :
    blockEstimate 9204 2007 12247 128 = 228462136192 := rfl
private theorem moment_9204_2007_part81 :
    blockEstimate 9204 2007 12375 128 = 170276221824 := rfl
private theorem moment_9204_2007_part82 :
    blockEstimate 9204 2007 12503 128 = 120208317312 := rfl
private theorem moment_9204_2007_part83 :
    blockEstimate 9204 2007 12631 128 = 78510080896 := rfl
private theorem moment_9204_2007_part84 :
    blockEstimate 9204 2007 12759 128 = 45433170816 := rfl
private theorem moment_9204_2007_part85 :
    blockEstimate 9204 2007 12887 128 = 21229245312 := rfl
private theorem moment_9204_2007_part86 :
    blockEstimate 9204 2007 13015 128 = 6149962624 := rfl
private theorem moment_9204_2007_part87 :
    blockEstimate 9204 2007 13143 75 = 341995098 := rfl
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

private theorem receipt_0_15_2339_0_part0 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 0 128 = 221804970338863754459718367680 := rfl
private theorem receipt_0_15_2339_0_part1 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 128 128 = 203030691474495956506674649536 := rfl
private theorem receipt_0_15_2339_0_part2 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 256 128 = 184822284388313184687559375296 := rfl
private theorem receipt_0_15_2339_0_part3 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 384 128 = 167171036905974077008962394560 := rfl
private theorem receipt_0_15_2339_0_part4 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 512 128 = 150068249831446989077134358976 := rfl
private theorem receipt_0_15_2339_0_part5 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 640 128 = 133505236940731166976874207680 := rfl
private theorem receipt_0_15_2339_0_part6 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 768 128 = 117473324975577920150416652736 := rfl
private theorem receipt_0_15_2339_0_part7 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 896 128 = 101963853637211794276319664576 := rfl
private theorem receipt_0_15_2339_0_part8 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 1024 128 = 86968175580051744148351957440 := rfl
private theorem receipt_0_15_2339_0_part9 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 1152 128 = 72477656408606427036563555887 := rfl
private theorem receipt_0_15_2339_0_part10 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 1280 128 = 58483684740578685955707762290 := rfl
private theorem receipt_0_15_2339_0_part11 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 1408 128 = 44977667976871678976375142590 := rfl
private theorem receipt_0_15_2339_0_part12 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 1536 128 = 31950987916670546641403901492 := rfl
private theorem receipt_0_15_2339_0_part13 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 1664 128 = 19395033209219499955390341937 := rfl
private theorem receipt_0_15_2339_0_part14 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 1792 128 = 7301205481107094212599481726 := rfl
private theorem receipt_0_15_2339_0_part15 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 1920 15 = 84985367354632791752365848 := rfl
private theorem receipt_0_15_2339_0_join0 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 0 256 = 424835661813359710966393017216 :=
  phaseBlock_append receipt_0_15_2339_0_part0 receipt_0_15_2339_0_part1 rfl rfl rfl
private theorem receipt_0_15_2339_0_join1 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 256 256 = 351993321294287261696521769856 :=
  phaseBlock_append receipt_0_15_2339_0_part2 receipt_0_15_2339_0_part3 rfl rfl rfl
private theorem receipt_0_15_2339_0_join2 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 0 512 = 776828983107646972662914787072 :=
  phaseBlock_append receipt_0_15_2339_0_join0 receipt_0_15_2339_0_join1 rfl rfl rfl
private theorem receipt_0_15_2339_0_join3 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 512 256 = 283573486772178156054008566656 :=
  phaseBlock_append receipt_0_15_2339_0_part4 receipt_0_15_2339_0_part5 rfl rfl rfl
private theorem receipt_0_15_2339_0_join4 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 768 256 = 219437178612789714426736317312 :=
  phaseBlock_append receipt_0_15_2339_0_part6 receipt_0_15_2339_0_part7 rfl rfl rfl
private theorem receipt_0_15_2339_0_join5 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 512 512 = 503010665384967870480744883968 :=
  phaseBlock_append receipt_0_15_2339_0_join3 receipt_0_15_2339_0_join4 rfl rfl rfl
private theorem receipt_0_15_2339_0_join6 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 0 1024 = 1279839648492614843143659671040 :=
  phaseBlock_append receipt_0_15_2339_0_join2 receipt_0_15_2339_0_join5 rfl rfl rfl
private theorem receipt_0_15_2339_0_join7 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 1024 256 = 159445831988658171184915513327 :=
  phaseBlock_append receipt_0_15_2339_0_part8 receipt_0_15_2339_0_part9 rfl rfl rfl
private theorem receipt_0_15_2339_0_join8 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 1280 256 = 103461352717450364932082904880 :=
  phaseBlock_append receipt_0_15_2339_0_part10 receipt_0_15_2339_0_part11 rfl rfl rfl
private theorem receipt_0_15_2339_0_join9 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 1024 512 = 262907184706108536116998418207 :=
  phaseBlock_append receipt_0_15_2339_0_join7 receipt_0_15_2339_0_join8 rfl rfl rfl
private theorem receipt_0_15_2339_0_join10 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 1536 256 = 51346021125890046596794243429 :=
  phaseBlock_append receipt_0_15_2339_0_part12 receipt_0_15_2339_0_part13 rfl rfl rfl
private theorem receipt_0_15_2339_0_join11 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 1792 143 = 7386190848461727004351847574 :=
  phaseBlock_append receipt_0_15_2339_0_part14 receipt_0_15_2339_0_part15 rfl rfl rfl
private theorem receipt_0_15_2339_0_join12 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 1536 399 = 58732211974351773601146091003 :=
  phaseBlock_append receipt_0_15_2339_0_join10 receipt_0_15_2339_0_join11 rfl rfl rfl
private theorem receipt_0_15_2339_0_join13 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 1024 911 = 321639396680460309718144509210 :=
  phaseBlock_append receipt_0_15_2339_0_join9 receipt_0_15_2339_0_join12 rfl rfl rfl
private theorem receipt_0_15_2339_0_join14 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 0) 0 1935 = 1601479045173075152861804180250 :=
  phaseBlock_append receipt_0_15_2339_0_join6 receipt_0_15_2339_0_join13 rfl rfl rfl

private theorem receipt_0_15_2339_0 : fastPhase (bank 0 15).shape 179827 2339 76 1 0 1 0 = 1601479045173075152861804180250 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_15_2339_0_join14

private theorem receipt_0_15_2339_1_part0 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 0 128 = 221658014854936291613646254144 := rfl
private theorem receipt_0_15_2339_1_part1 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 128 128 = 202888043553513520679512150080 := rfl
private theorem receipt_0_15_2339_1_part2 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 256 128 = 184683878094659157129576263744 := rfl
private theorem receipt_0_15_2339_1_part3 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 384 128 = 167036806402972224239243284544 := rfl
private theorem receipt_0_15_2339_1_part4 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 512 128 = 149938129381313373955831525440 := rfl
private theorem receipt_0_15_2339_1_part5 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 640 128 = 133379160904526059777460408384 := rfl
private theorem receipt_0_15_2339_1_part6 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 768 128 = 117351227813157709631937949760 := rfl
private theorem receipt_0_15_2339_1_part7 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 896 128 = 101845669907180898755648245824 := rfl
private theorem receipt_0_15_2339_1_part8 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 1024 128 = 86853839939714522572438958144 := rfl
private theorem receipt_0_15_2339_1_part9 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 1152 128 = 72367103613914039747273232566 := rfl
private theorem receipt_0_15_2339_1_part10 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 1280 128 = 58376849628145546608997126972 := rfl
private theorem receipt_0_15_2339_1_part11 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 1408 128 = 44874485433113123589479967776 := rfl
private theorem receipt_0_15_2339_1_part12 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 1536 128 = 31851392918602781875727666898 := rfl
private theorem receipt_0_15_2339_1_part13 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 1664 128 = 19298960832520168337091370825 := rfl
private theorem receipt_0_15_2339_1_part14 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 1792 128 = 7208590900072320324866483064 := rfl
private theorem receipt_0_15_2339_1_part15 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 1920 15 = 74355452924996901669357892 := rfl
private theorem receipt_0_15_2339_1_join0 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 0 256 = 424546058408449812293158404224 :=
  phaseBlock_append receipt_0_15_2339_1_part0 receipt_0_15_2339_1_part1 rfl rfl rfl
private theorem receipt_0_15_2339_1_join1 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 256 256 = 351720684497631381368819548288 :=
  phaseBlock_append receipt_0_15_2339_1_part2 receipt_0_15_2339_1_part3 rfl rfl rfl
private theorem receipt_0_15_2339_1_join2 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 0 512 = 776266742906081193661977952512 :=
  phaseBlock_append receipt_0_15_2339_1_join0 receipt_0_15_2339_1_join1 rfl rfl rfl
private theorem receipt_0_15_2339_1_join3 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 512 256 = 283317290285839433733291933824 :=
  phaseBlock_append receipt_0_15_2339_1_part4 receipt_0_15_2339_1_part5 rfl rfl rfl
private theorem receipt_0_15_2339_1_join4 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 768 256 = 219196897720338608387586195584 :=
  phaseBlock_append receipt_0_15_2339_1_part6 receipt_0_15_2339_1_part7 rfl rfl rfl
private theorem receipt_0_15_2339_1_join5 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 512 512 = 502514188006178042120878129408 :=
  phaseBlock_append receipt_0_15_2339_1_join3 receipt_0_15_2339_1_join4 rfl rfl rfl
private theorem receipt_0_15_2339_1_join6 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 0 1024 = 1278780930912259235782856081920 :=
  phaseBlock_append receipt_0_15_2339_1_join2 receipt_0_15_2339_1_join5 rfl rfl rfl
private theorem receipt_0_15_2339_1_join7 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 1024 256 = 159220943553628562319712190710 :=
  phaseBlock_append receipt_0_15_2339_1_part8 receipt_0_15_2339_1_part9 rfl rfl rfl
private theorem receipt_0_15_2339_1_join8 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 1280 256 = 103251335061258670198477094748 :=
  phaseBlock_append receipt_0_15_2339_1_part10 receipt_0_15_2339_1_part11 rfl rfl rfl
private theorem receipt_0_15_2339_1_join9 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 1024 512 = 262472278614887232518189285458 :=
  phaseBlock_append receipt_0_15_2339_1_join7 receipt_0_15_2339_1_join8 rfl rfl rfl
private theorem receipt_0_15_2339_1_join10 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 1536 256 = 51150353751122950212819037723 :=
  phaseBlock_append receipt_0_15_2339_1_part12 receipt_0_15_2339_1_part13 rfl rfl rfl
private theorem receipt_0_15_2339_1_join11 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 1792 143 = 7282946352997317226535840956 :=
  phaseBlock_append receipt_0_15_2339_1_part14 receipt_0_15_2339_1_part15 rfl rfl rfl
private theorem receipt_0_15_2339_1_join12 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 1536 399 = 58433300104120267439354878679 :=
  phaseBlock_append receipt_0_15_2339_1_join10 receipt_0_15_2339_1_join11 rfl rfl rfl
private theorem receipt_0_15_2339_1_join13 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 1024 911 = 320905578719007499957544164137 :=
  phaseBlock_append receipt_0_15_2339_1_join9 receipt_0_15_2339_1_join12 rfl rfl rfl
private theorem receipt_0_15_2339_1_join14 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2339 76 1 0 1 1) 0 1935 = 1599686509631266735740400246057 :=
  phaseBlock_append receipt_0_15_2339_1_join6 receipt_0_15_2339_1_join13 rfl rfl rfl

private theorem receipt_0_15_2339_1 : fastPhase (bank 0 15).shape 179827 2339 76 1 0 1 1 = 1599686509631266735740400246057 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_15_2339_1_join14

private theorem receipt_0_15_2340_0_part0 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 0 128 = 221806958637163156340772711552 := rfl
private theorem receipt_0_15_2340_0_part1 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 128 128 = 203032443881729573280179645568 := rfl
private theorem receipt_0_15_2340_0_part2 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 256 128 = 184823816838302825558571134080 := rfl
private theorem receipt_0_15_2340_0_part3 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 384 128 = 167172365031721998095443029120 := rfl
private theorem receipt_0_15_2340_0_part4 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 512 128 = 150069388965588769501969984640 := rfl
private theorem receipt_0_15_2340_0_part5 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 640 128 = 133506202115988365057567386752 := rfl
private theorem receipt_0_15_2340_0_part6 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 768 128 = 117474130925210509686453283968 := rfl
private theorem receipt_0_15_2340_0_part7 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 896 128 = 101964514795470380934210317440 := rfl
private theorem receipt_0_15_2340_0_part8 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 1024 128 = 86968706082629561944347651200 := rfl
private theorem receipt_0_15_2340_0_part9 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 1152 128 = 72478070090888160431603726970 := rfl
private theorem receipt_0_15_2340_0_part10 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 1280 128 = 58483994861074085806550111251 := rfl
private theorem receipt_0_15_2340_0_part11 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 1408 128 = 44977887782096072702091735899 := rfl
private theorem receipt_0_15_2340_0_part12 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 1536 128 = 31951130564287986292195946754 := rfl
private theorem receipt_0_15_2340_0_part13 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 1664 128 = 19395111532637071284927886740 := rfl
private theorem receipt_0_15_2340_0_part14 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 1792 128 = 7301231998296987705602999302 := rfl
private theorem receipt_0_15_2340_0_part15 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 1920 15 = 84985650181971097513161312 := rfl
private theorem receipt_0_15_2340_0_join0 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 0 256 = 424839402518892729620952357120 :=
  phaseBlock_append receipt_0_15_2340_0_part0 receipt_0_15_2340_0_part1 rfl rfl rfl
private theorem receipt_0_15_2340_0_join1 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 256 256 = 351996181870024823654014163200 :=
  phaseBlock_append receipt_0_15_2340_0_part2 receipt_0_15_2340_0_part3 rfl rfl rfl
private theorem receipt_0_15_2340_0_join2 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 0 512 = 776835584388917553274966520320 :=
  phaseBlock_append receipt_0_15_2340_0_join0 receipt_0_15_2340_0_join1 rfl rfl rfl
private theorem receipt_0_15_2340_0_join3 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 512 256 = 283575591081577134559537371392 :=
  phaseBlock_append receipt_0_15_2340_0_part4 receipt_0_15_2340_0_part5 rfl rfl rfl
private theorem receipt_0_15_2340_0_join4 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 768 256 = 219438645720680890620663601408 :=
  phaseBlock_append receipt_0_15_2340_0_part6 receipt_0_15_2340_0_part7 rfl rfl rfl
private theorem receipt_0_15_2340_0_join5 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 512 512 = 503014236802258025180200972800 :=
  phaseBlock_append receipt_0_15_2340_0_join3 receipt_0_15_2340_0_join4 rfl rfl rfl
private theorem receipt_0_15_2340_0_join6 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 0 1024 = 1279849821191175578455167493120 :=
  phaseBlock_append receipt_0_15_2340_0_join2 receipt_0_15_2340_0_join5 rfl rfl rfl
private theorem receipt_0_15_2340_0_join7 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 1024 256 = 159446776173517722375951378170 :=
  phaseBlock_append receipt_0_15_2340_0_part8 receipt_0_15_2340_0_part9 rfl rfl rfl
private theorem receipt_0_15_2340_0_join8 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 1280 256 = 103461882643170158508641847150 :=
  phaseBlock_append receipt_0_15_2340_0_part10 receipt_0_15_2340_0_part11 rfl rfl rfl
private theorem receipt_0_15_2340_0_join9 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 1024 512 = 262908658816687880884593225320 :=
  phaseBlock_append receipt_0_15_2340_0_join7 receipt_0_15_2340_0_join8 rfl rfl rfl
private theorem receipt_0_15_2340_0_join10 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 1536 256 = 51346242096925057577123833494 :=
  phaseBlock_append receipt_0_15_2340_0_part12 receipt_0_15_2340_0_part13 rfl rfl rfl
private theorem receipt_0_15_2340_0_join11 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 1792 143 = 7386217648478958803116160614 :=
  phaseBlock_append receipt_0_15_2340_0_part14 receipt_0_15_2340_0_part15 rfl rfl rfl
private theorem receipt_0_15_2340_0_join12 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 1536 399 = 58732459745404016380239994108 :=
  phaseBlock_append receipt_0_15_2340_0_join10 receipt_0_15_2340_0_join11 rfl rfl rfl
private theorem receipt_0_15_2340_0_join13 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 1024 911 = 321641118562091897264833219428 :=
  phaseBlock_append receipt_0_15_2340_0_join9 receipt_0_15_2340_0_join12 rfl rfl rfl
private theorem receipt_0_15_2340_0_join14 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 0) 0 1935 = 1601490939753267475720000712548 :=
  phaseBlock_append receipt_0_15_2340_0_join6 receipt_0_15_2340_0_join13 rfl rfl rfl

private theorem receipt_0_15_2340_0 : fastPhase (bank 0 15).shape 179827 2340 76 1 0 1 0 = 1601490939753267475720000712548 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_15_2340_0_join14

private theorem receipt_0_15_2340_1_part0 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 0 128 = 221660002074734614819949231040 := rfl
private theorem receipt_0_15_2340_1_part1 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 128 128 = 202889794945001792800048282560 := rfl
private theorem receipt_0_15_2340_1_part2 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 256 128 = 184685409590238686274090712000 := rfl
private theorem receipt_0_15_2340_1_part3 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 384 128 = 167038133634227245379937401792 := rfl
private theorem receipt_0_15_2340_1_part4 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 512 128 = 149939267679463923713710799808 := rfl
private theorem receipt_0_15_2340_1_part5 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 640 128 = 133380125300880631306356849600 := rfl
private theorem receipt_0_15_2340_1_part6 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 768 128 = 117352033039565687600206920640 := rfl
private theorem receipt_0_15_2340_1_part7 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 896 128 = 101846330396484774425539738560 := rfl
private theorem receipt_0_15_2340_1_part8 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 1024 128 = 86854369826201888977143315392 := rfl
private theorem receipt_0_15_2340_1_part9 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 1152 128 = 72367516731569842308773761498 := rfl
private theorem receipt_0_15_2340_1_part10 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 1280 128 = 58377159234570272954625839654 := rfl
private theorem receipt_0_15_2340_1_part11 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 1408 128 = 44874704773669793070690013666 := rfl
private theorem receipt_0_15_2340_1_part12 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 1536 128 = 31851535149491469663830927414 := rfl
private theorem receipt_0_15_2340_1_part13 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 1664 128 = 19299038785699082126573948304 := rfl
private theorem receipt_0_15_2340_1_part14 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 1792 128 = 7208617092048947145225426675 := rfl
private theorem receipt_0_15_2340_1_part15 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 1920 15 = 74355700519771063285892202 := rfl
private theorem receipt_0_15_2340_1_join0 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 0 256 = 424549797019736407619997513600 :=
  phaseBlock_append receipt_0_15_2340_1_part0 receipt_0_15_2340_1_part1 rfl rfl rfl
private theorem receipt_0_15_2340_1_join1 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 256 256 = 351723543224465931654028113792 :=
  phaseBlock_append receipt_0_15_2340_1_part2 receipt_0_15_2340_1_part3 rfl rfl rfl
private theorem receipt_0_15_2340_1_join2 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 0 512 = 776273340244202339274025627392 :=
  phaseBlock_append receipt_0_15_2340_1_join0 receipt_0_15_2340_1_join1 rfl rfl rfl
private theorem receipt_0_15_2340_1_join3 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 512 256 = 283319392980344555020067649408 :=
  phaseBlock_append receipt_0_15_2340_1_part4 receipt_0_15_2340_1_part5 rfl rfl rfl
private theorem receipt_0_15_2340_1_join4 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 768 256 = 219198363436050462025746659200 :=
  phaseBlock_append receipt_0_15_2340_1_part6 receipt_0_15_2340_1_part7 rfl rfl rfl
private theorem receipt_0_15_2340_1_join5 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 512 512 = 502517756416395017045814308608 :=
  phaseBlock_append receipt_0_15_2340_1_join3 receipt_0_15_2340_1_join4 rfl rfl rfl
private theorem receipt_0_15_2340_1_join6 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 0 1024 = 1278791096660597356319839936000 :=
  phaseBlock_append receipt_0_15_2340_1_join2 receipt_0_15_2340_1_join5 rfl rfl rfl
private theorem receipt_0_15_2340_1_join7 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 1024 256 = 159221886557771731285917076890 :=
  phaseBlock_append receipt_0_15_2340_1_part8 receipt_0_15_2340_1_part9 rfl rfl rfl
private theorem receipt_0_15_2340_1_join8 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 1280 256 = 103251864008240066025315853320 :=
  phaseBlock_append receipt_0_15_2340_1_part10 receipt_0_15_2340_1_part11 rfl rfl rfl
private theorem receipt_0_15_2340_1_join9 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 1024 512 = 262473750566011797311232930210 :=
  phaseBlock_append receipt_0_15_2340_1_join7 receipt_0_15_2340_1_join8 rfl rfl rfl
private theorem receipt_0_15_2340_1_join10 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 1536 256 = 51150573935190551790404875718 :=
  phaseBlock_append receipt_0_15_2340_1_part12 receipt_0_15_2340_1_part13 rfl rfl rfl
private theorem receipt_0_15_2340_1_join11 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 1792 143 = 7282972792568718208511318877 :=
  phaseBlock_append receipt_0_15_2340_1_part14 receipt_0_15_2340_1_part15 rfl rfl rfl
private theorem receipt_0_15_2340_1_join12 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 1536 399 = 58433546727759269998916194595 :=
  phaseBlock_append receipt_0_15_2340_1_join10 receipt_0_15_2340_1_join11 rfl rfl rfl
private theorem receipt_0_15_2340_1_join13 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 1024 911 = 320907297293771067310149124805 :=
  phaseBlock_append receipt_0_15_2340_1_join9 receipt_0_15_2340_1_join12 rfl rfl rfl
private theorem receipt_0_15_2340_1_join14 :
    phaseBlock (fastLayer (bank 0 15).shape 179827 2340 76 1 0 1 1) 0 1935 = 1599698393954368423629989060805 :=
  phaseBlock_append receipt_0_15_2340_1_join6 receipt_0_15_2340_1_join13 rfl rfl rfl

private theorem receipt_0_15_2340_1 : fastPhase (bank 0 15).shape 179827 2340 76 1 0 1 1 = 1599698393954368423629989060805 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_0_15_2340_1_join14

theorem receipt_0_15 : Checked (bank 0 15) 76 0 1 := by
  refine checked_from_values (bank 0 15) 76 0 1
    (P3_7_1.checked (bank 0 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9204_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_15_2339_0 receipt_0_15_2339_1 receipt_0_15_2340_0 receipt_0_15_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_15_2339_0_part0 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 0 128 = 199689660067183115693942524160 := rfl
private theorem receipt_1_15_2339_0_part1 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 128 128 = 182707412288144795781870749952 := rfl
private theorem receipt_1_15_2339_0_part2 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 256 128 = 166248935066736333374484957440 := rfl
private theorem receipt_1_15_2339_0_part3 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 384 128 = 150305730680344434501204576512 := rfl
private theorem receipt_1_15_2339_0_part4 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 512 128 = 134869326558115069327607023872 := rfl
private theorem receipt_1_15_2339_0_part5 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 640 128 = 119931275255838163670977644800 := rfl
private theorem receipt_1_15_2339_0_part6 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 768 128 = 105483154430832290515859654912 := rfl
private theorem receipt_1_15_2339_0_part7 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 896 128 = 91516566816829361529604081920 := rfl
private theorem receipt_1_15_2339_0_part8 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 1024 128 = 78023140198859318577919707392 := rfl
private theorem receipt_1_15_2339_0_part9 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 1152 128 = 64994527390980590655814819758 := rfl
private theorem receipt_1_15_2339_0_part10 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 1280 128 = 52422415236040910932507829322 := rfl
private theorem receipt_1_15_2339_0_part11 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 1408 128 = 40298520779172601457864879403 := rfl
private theorem receipt_1_15_2339_0_part12 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 1536 128 = 28614551484965981518362393776 := rfl
private theorem receipt_1_15_2339_0_part13 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 1664 128 = 17362234343454525472150332829 := rfl
private theorem receipt_1_15_2339_0_part14 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 1792 128 = 6533321345850747691115819802 := rfl
private theorem receipt_1_15_2339_0_part15 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 1920 15 = 76024606818415082793002176 := rfl
private theorem receipt_1_15_2339_0_join0 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 0 256 = 382397072355327911475813274112 :=
  phaseBlock_append receipt_1_15_2339_0_part0 receipt_1_15_2339_0_part1 rfl rfl rfl
private theorem receipt_1_15_2339_0_join1 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 256 256 = 316554665747080767875689533952 :=
  phaseBlock_append receipt_1_15_2339_0_part2 receipt_1_15_2339_0_part3 rfl rfl rfl
private theorem receipt_1_15_2339_0_join2 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 0 512 = 698951738102408679351502808064 :=
  phaseBlock_append receipt_1_15_2339_0_join0 receipt_1_15_2339_0_join1 rfl rfl rfl
private theorem receipt_1_15_2339_0_join3 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 512 256 = 254800601813953232998584668672 :=
  phaseBlock_append receipt_1_15_2339_0_part4 receipt_1_15_2339_0_part5 rfl rfl rfl
private theorem receipt_1_15_2339_0_join4 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 768 256 = 196999721247661652045463736832 :=
  phaseBlock_append receipt_1_15_2339_0_part6 receipt_1_15_2339_0_part7 rfl rfl rfl
private theorem receipt_1_15_2339_0_join5 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 512 512 = 451800323061614885044048405504 :=
  phaseBlock_append receipt_1_15_2339_0_join3 receipt_1_15_2339_0_join4 rfl rfl rfl
private theorem receipt_1_15_2339_0_join6 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 0 1024 = 1150752061164023564395551213568 :=
  phaseBlock_append receipt_1_15_2339_0_join2 receipt_1_15_2339_0_join5 rfl rfl rfl
private theorem receipt_1_15_2339_0_join7 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 1024 256 = 143017667589839909233734527150 :=
  phaseBlock_append receipt_1_15_2339_0_part8 receipt_1_15_2339_0_part9 rfl rfl rfl
private theorem receipt_1_15_2339_0_join8 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 1280 256 = 92720936015213512390372708725 :=
  phaseBlock_append receipt_1_15_2339_0_part10 receipt_1_15_2339_0_part11 rfl rfl rfl
private theorem receipt_1_15_2339_0_join9 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 1024 512 = 235738603605053421624107235875 :=
  phaseBlock_append receipt_1_15_2339_0_join7 receipt_1_15_2339_0_join8 rfl rfl rfl
private theorem receipt_1_15_2339_0_join10 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 1536 256 = 45976785828420506990512726605 :=
  phaseBlock_append receipt_1_15_2339_0_part12 receipt_1_15_2339_0_part13 rfl rfl rfl
private theorem receipt_1_15_2339_0_join11 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 1792 143 = 6609345952669162773908821978 :=
  phaseBlock_append receipt_1_15_2339_0_part14 receipt_1_15_2339_0_part15 rfl rfl rfl
private theorem receipt_1_15_2339_0_join12 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 1536 399 = 52586131781089669764421548583 :=
  phaseBlock_append receipt_1_15_2339_0_join10 receipt_1_15_2339_0_join11 rfl rfl rfl
private theorem receipt_1_15_2339_0_join13 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 1024 911 = 288324735386143091388528784458 :=
  phaseBlock_append receipt_1_15_2339_0_join9 receipt_1_15_2339_0_join12 rfl rfl rfl
private theorem receipt_1_15_2339_0_join14 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 0) 0 1935 = 1439076796550166655784079998026 :=
  phaseBlock_append receipt_1_15_2339_0_join6 receipt_1_15_2339_0_join13 rfl rfl rfl

private theorem receipt_1_15_2339_0 : fastPhase (bank 1 15).shape 179827 2339 76 1 0 2 0 = 1439076796550166655784079998026 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_15_2339_0_join14

private theorem receipt_1_15_2339_1_part0 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 0 128 = 199556675671047414641143509568 := rfl
private theorem receipt_1_15_2339_1_part1 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 128 128 = 182578419704520349348193751616 := rfl
private theorem receipt_1_15_2339_1_part2 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 256 128 = 166123869884929573055185072704 := rfl
private theorem receipt_1_15_2339_1_part3 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 384 128 = 150184528681487377849365533248 := rfl
private theorem receipt_1_15_2339_1_part4 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 512 128 = 134751923714972964243152466496 := rfl
private theorem receipt_1_15_2339_1_part5 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 640 128 = 119817607732617132689682420288 := rfl
private theorem receipt_1_15_2339_1_part6 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 768 128 = 105373158582986975098361098816 := rfl
private theorem receipt_1_15_2339_1_part7 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 896 128 = 91410179190870566350413304384 := rfl
private theorem receipt_1_15_2339_1_part8 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 1024 128 = 77920297532161655814432879168 := rfl
private theorem receipt_1_15_2339_1_part9 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 1152 128 = 64895166611585586651331007235 := rfl
private theorem receipt_1_15_2339_1_part10 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 1280 128 = 52326473446358755135767142510 := rfl
private theorem receipt_1_15_2339_1_part11 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 1408 128 = 40205935228189683186969496065 := rfl
private theorem receipt_1_15_2339_1_part12 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 1536 128 = 28525259604829756036208475745 := rfl
private theorem receipt_1_15_2339_1_part13 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 1664 128 = 17276173756571924004852621732 := rfl
private theorem receipt_1_15_2339_1_part14 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 1792 128 = 6450429864699987954981223312 := rfl
private theorem receipt_1_15_2339_1_part15 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 1920 15 = 66515345620245538400999342 := rfl
private theorem receipt_1_15_2339_1_join0 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 0 256 = 382135095375567763989337261184 :=
  phaseBlock_append receipt_1_15_2339_1_part0 receipt_1_15_2339_1_part1 rfl rfl rfl
private theorem receipt_1_15_2339_1_join1 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 256 256 = 316308398566416950904550605952 :=
  phaseBlock_append receipt_1_15_2339_1_part2 receipt_1_15_2339_1_part3 rfl rfl rfl
private theorem receipt_1_15_2339_1_join2 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 0 512 = 698443493941984714893887867136 :=
  phaseBlock_append receipt_1_15_2339_1_join0 receipt_1_15_2339_1_join1 rfl rfl rfl
private theorem receipt_1_15_2339_1_join3 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 512 256 = 254569531447590096932834886784 :=
  phaseBlock_append receipt_1_15_2339_1_part4 receipt_1_15_2339_1_part5 rfl rfl rfl
private theorem receipt_1_15_2339_1_join4 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 768 256 = 196783337773857541448774403200 :=
  phaseBlock_append receipt_1_15_2339_1_part6 receipt_1_15_2339_1_part7 rfl rfl rfl
private theorem receipt_1_15_2339_1_join5 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 512 512 = 451352869221447638381609289984 :=
  phaseBlock_append receipt_1_15_2339_1_join3 receipt_1_15_2339_1_join4 rfl rfl rfl
private theorem receipt_1_15_2339_1_join6 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 0 1024 = 1149796363163432353275497157120 :=
  phaseBlock_append receipt_1_15_2339_1_join2 receipt_1_15_2339_1_join5 rfl rfl rfl
private theorem receipt_1_15_2339_1_join7 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 1024 256 = 142815464143747242465763886403 :=
  phaseBlock_append receipt_1_15_2339_1_part8 receipt_1_15_2339_1_part9 rfl rfl rfl
private theorem receipt_1_15_2339_1_join8 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 1280 256 = 92532408674548438322736638575 :=
  phaseBlock_append receipt_1_15_2339_1_part10 receipt_1_15_2339_1_part11 rfl rfl rfl
private theorem receipt_1_15_2339_1_join9 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 1024 512 = 235347872818295680788500524978 :=
  phaseBlock_append receipt_1_15_2339_1_join7 receipt_1_15_2339_1_join8 rfl rfl rfl
private theorem receipt_1_15_2339_1_join10 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 1536 256 = 45801433361401680041061097477 :=
  phaseBlock_append receipt_1_15_2339_1_part12 receipt_1_15_2339_1_part13 rfl rfl rfl
private theorem receipt_1_15_2339_1_join11 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 1792 143 = 6516945210320233493382222654 :=
  phaseBlock_append receipt_1_15_2339_1_part14 receipt_1_15_2339_1_part15 rfl rfl rfl
private theorem receipt_1_15_2339_1_join12 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 1536 399 = 52318378571721913534443320131 :=
  phaseBlock_append receipt_1_15_2339_1_join10 receipt_1_15_2339_1_join11 rfl rfl rfl
private theorem receipt_1_15_2339_1_join13 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 1024 911 = 287666251390017594322943845109 :=
  phaseBlock_append receipt_1_15_2339_1_join9 receipt_1_15_2339_1_join12 rfl rfl rfl
private theorem receipt_1_15_2339_1_join14 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2339 76 1 0 2 1) 0 1935 = 1437462614553449947598441002229 :=
  phaseBlock_append receipt_1_15_2339_1_join6 receipt_1_15_2339_1_join13 rfl rfl rfl

private theorem receipt_1_15_2339_1 : fastPhase (bank 1 15).shape 179827 2339 76 1 0 2 1 = 1437462614553449947598441002229 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_15_2339_1_join14

private theorem receipt_1_15_2340_0_part0 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 0 128 = 199691450122395263985242394624 := rfl
private theorem receipt_1_15_2340_0_part1 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 128 128 = 182708989282456937962218860544 := rfl
private theorem receipt_1_15_2340_0_part2 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 256 128 = 166250313518281249222950621184 := rfl
private theorem receipt_1_15_2340_0_part3 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 384 128 = 150306924818012615397781336064 := rfl
private theorem receipt_1_15_2340_0_part4 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 512 128 = 134870350322428959739666649088 := rfl
private theorem receipt_1_15_2340_0_part5 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 640 128 = 119932142299825523030421909504 := rfl
private theorem receipt_1_15_2340_0_part6 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 768 128 = 105483878120898675486969892864 := rfl
private theorem receipt_1_15_2340_0_part7 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 896 128 = 91517160233629728667588521984 := rfl
private theorem receipt_1_15_2340_0_part8 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 1024 128 = 78023616138168747378158587904 := rfl
private theorem receipt_1_15_2340_0_part9 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 1152 128 = 64994898362589061532815839174 := rfl
private theorem receipt_1_15_2340_0_part10 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 1280 128 = 52422693216331262439784419147 := rfl
private theorem receipt_1_15_2340_0_part11 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 1408 128 = 40298717718090798719135449375 := rfl
private theorem receipt_1_15_2340_0_part12 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 1536 128 = 28614679237255343100652361093 := rfl
private theorem receipt_1_15_2340_0_part13 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 1664 128 = 17362304458043525745632916945 := rfl
private theorem receipt_1_15_2340_0_part14 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 1792 128 = 6533345074252455682101665004 := rfl
private theorem receipt_1_15_2340_0_part15 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 1920 15 = 76024859824772384077034112 := rfl
private theorem receipt_1_15_2340_0_join0 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 0 256 = 382400439404852201947461255168 :=
  phaseBlock_append receipt_1_15_2340_0_part0 receipt_1_15_2340_0_part1 rfl rfl rfl
private theorem receipt_1_15_2340_0_join1 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 256 256 = 316557238336293864620731957248 :=
  phaseBlock_append receipt_1_15_2340_0_part2 receipt_1_15_2340_0_part3 rfl rfl rfl
private theorem receipt_1_15_2340_0_join2 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 0 512 = 698957677741146066568193212416 :=
  phaseBlock_append receipt_1_15_2340_0_join0 receipt_1_15_2340_0_join1 rfl rfl rfl
private theorem receipt_1_15_2340_0_join3 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 512 256 = 254802492622254482770088558592 :=
  phaseBlock_append receipt_1_15_2340_0_part4 receipt_1_15_2340_0_part5 rfl rfl rfl
private theorem receipt_1_15_2340_0_join4 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 768 256 = 197001038354528404154558414848 :=
  phaseBlock_append receipt_1_15_2340_0_part6 receipt_1_15_2340_0_part7 rfl rfl rfl
private theorem receipt_1_15_2340_0_join5 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 512 512 = 451803530976782886924646973440 :=
  phaseBlock_append receipt_1_15_2340_0_join3 receipt_1_15_2340_0_join4 rfl rfl rfl
private theorem receipt_1_15_2340_0_join6 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 0 1024 = 1150761208717928953492840185856 :=
  phaseBlock_append receipt_1_15_2340_0_join2 receipt_1_15_2340_0_join5 rfl rfl rfl
private theorem receipt_1_15_2340_0_join7 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 1024 256 = 143018514500757808910974427078 :=
  phaseBlock_append receipt_1_15_2340_0_part8 receipt_1_15_2340_0_part9 rfl rfl rfl
private theorem receipt_1_15_2340_0_join8 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 1280 256 = 92721410934422061158919868522 :=
  phaseBlock_append receipt_1_15_2340_0_part10 receipt_1_15_2340_0_part11 rfl rfl rfl
private theorem receipt_1_15_2340_0_join9 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 1024 512 = 235739925435179870069894295600 :=
  phaseBlock_append receipt_1_15_2340_0_join7 receipt_1_15_2340_0_join8 rfl rfl rfl
private theorem receipt_1_15_2340_0_join10 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 1536 256 = 45976983695298868846285278038 :=
  phaseBlock_append receipt_1_15_2340_0_part12 receipt_1_15_2340_0_part13 rfl rfl rfl
private theorem receipt_1_15_2340_0_join11 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 1792 143 = 6609369934077228066178699116 :=
  phaseBlock_append receipt_1_15_2340_0_part14 receipt_1_15_2340_0_part15 rfl rfl rfl
private theorem receipt_1_15_2340_0_join12 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 1536 399 = 52586353629376096912463977154 :=
  phaseBlock_append receipt_1_15_2340_0_join10 receipt_1_15_2340_0_join11 rfl rfl rfl
private theorem receipt_1_15_2340_0_join13 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 1024 911 = 288326279064555966982358272754 :=
  phaseBlock_append receipt_1_15_2340_0_join9 receipt_1_15_2340_0_join12 rfl rfl rfl
private theorem receipt_1_15_2340_0_join14 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 0) 0 1935 = 1439087487782484920475198458610 :=
  phaseBlock_append receipt_1_15_2340_0_join6 receipt_1_15_2340_0_join13 rfl rfl rfl

private theorem receipt_1_15_2340_0 : fastPhase (bank 1 15).shape 179827 2340 76 1 0 2 0 = 1439087487782484920475198458610 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_15_2340_0_join14

private theorem receipt_1_15_2340_1_part0 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 0 128 = 199558464749182383202717438464 := rfl
private theorem receipt_1_15_2340_1_part1 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 128 128 = 182579995779377751533426881024 := rfl
private theorem receipt_1_15_2340_1_part2 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 256 128 = 166125247473266356666823397888 := rfl
private theorem receipt_1_15_2340_1_part3 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 384 128 = 150185722010822996432896193024 := rfl
private theorem receipt_1_15_2340_1_part4 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 512 128 = 134752946724463613350577508864 := rfl
private theorem receipt_1_15_2340_1_part5 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 640 128 = 119818474073929106533990347264 := rfl
private theorem receipt_1_15_2340_1_part6 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 768 128 = 105373881621169143598696190464 := rfl
private theorem receipt_1_15_2340_1_part7 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 896 128 = 91410772005225972567942722048 := rfl
private theorem receipt_1_15_2340_1_part8 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 1024 128 = 77920772917118233778911547904 := rfl
private theorem receipt_1_15_2340_1_part9 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 1152 128 = 64895537075594015915027053845 := rfl
private theorem receipt_1_15_2340_1_part10 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 1280 128 = 52326750964905586489166136005 := rfl
private theorem receipt_1_15_2340_1_part11 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 1408 128 = 40206131750107967059155891722 := rfl
private theorem receipt_1_15_2340_1_part12 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 1536 128 = 28525386983472358284574948925 := rfl
private theorem receipt_1_15_2340_1_part13 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 1664 128 = 17276243539493080721743306128 := rfl
private theorem receipt_1_15_2340_1_part14 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 1792 128 = 6450453302027025687022521117 := rfl
private theorem receipt_1_15_2340_1_part15 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 1920 15 = 66515567108408352971170197 := rfl
private theorem receipt_1_15_2340_1_join0 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 0 256 = 382138460528560134736144319488 :=
  phaseBlock_append receipt_1_15_2340_1_part0 receipt_1_15_2340_1_part1 rfl rfl rfl
private theorem receipt_1_15_2340_1_join1 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 256 256 = 316310969484089353099719590912 :=
  phaseBlock_append receipt_1_15_2340_1_part2 receipt_1_15_2340_1_part3 rfl rfl rfl
private theorem receipt_1_15_2340_1_join2 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 0 512 = 698449430012649487835863910400 :=
  phaseBlock_append receipt_1_15_2340_1_join0 receipt_1_15_2340_1_join1 rfl rfl rfl
private theorem receipt_1_15_2340_1_join3 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 512 256 = 254571420798392719884567856128 :=
  phaseBlock_append receipt_1_15_2340_1_part4 receipt_1_15_2340_1_part5 rfl rfl rfl
private theorem receipt_1_15_2340_1_join4 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 768 256 = 196784653626395116166638912512 :=
  phaseBlock_append receipt_1_15_2340_1_part6 receipt_1_15_2340_1_part7 rfl rfl rfl
private theorem receipt_1_15_2340_1_join5 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 512 512 = 451356074424787836051206768640 :=
  phaseBlock_append receipt_1_15_2340_1_join3 receipt_1_15_2340_1_join4 rfl rfl rfl
private theorem receipt_1_15_2340_1_join6 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 0 1024 = 1149805504437437323887070679040 :=
  phaseBlock_append receipt_1_15_2340_1_join2 receipt_1_15_2340_1_join5 rfl rfl rfl
private theorem receipt_1_15_2340_1_join7 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 1024 256 = 142816309992712249693938601749 :=
  phaseBlock_append receipt_1_15_2340_1_part8 receipt_1_15_2340_1_part9 rfl rfl rfl
private theorem receipt_1_15_2340_1_join8 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 1280 256 = 92532882715013553548322027727 :=
  phaseBlock_append receipt_1_15_2340_1_part10 receipt_1_15_2340_1_part11 rfl rfl rfl
private theorem receipt_1_15_2340_1_join9 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 1024 512 = 235349192707725803242260629476 :=
  phaseBlock_append receipt_1_15_2340_1_join7 receipt_1_15_2340_1_join8 rfl rfl rfl
private theorem receipt_1_15_2340_1_join10 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 1536 256 = 45801630522965439006318255053 :=
  phaseBlock_append receipt_1_15_2340_1_part12 receipt_1_15_2340_1_part13 rfl rfl rfl
private theorem receipt_1_15_2340_1_join11 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 1792 143 = 6516968869135434039993691314 :=
  phaseBlock_append receipt_1_15_2340_1_part14 receipt_1_15_2340_1_part15 rfl rfl rfl
private theorem receipt_1_15_2340_1_join12 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 1536 399 = 52318599392100873046311946367 :=
  phaseBlock_append receipt_1_15_2340_1_join10 receipt_1_15_2340_1_join11 rfl rfl rfl
private theorem receipt_1_15_2340_1_join13 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 1024 911 = 287667792099826676288572575843 :=
  phaseBlock_append receipt_1_15_2340_1_join9 receipt_1_15_2340_1_join12 rfl rfl rfl
private theorem receipt_1_15_2340_1_join14 :
    phaseBlock (fastLayer (bank 1 15).shape 179827 2340 76 1 0 2 1) 0 1935 = 1437473296537264000175643254883 :=
  phaseBlock_append receipt_1_15_2340_1_join6 receipt_1_15_2340_1_join13 rfl rfl rfl

private theorem receipt_1_15_2340_1 : fastPhase (bank 1 15).shape 179827 2340 76 1 0 2 1 = 1437473296537264000175643254883 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_1_15_2340_1_join14

theorem receipt_1_15 : Checked (bank 1 15) 76 0 2 := by
  refine checked_from_values (bank 1 15) 76 0 2
    (P3_7_1.checked (bank 1 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9204_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_15_2339_0 receipt_1_15_2339_1 receipt_1_15_2340_0 receipt_1_15_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_15_2339_0_part0 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 0 128 = 107114728745022683675023373760 := rfl
private theorem receipt_2_15_2339_0_part1 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 128 128 = 97697558587060596191747020224 := rfl
private theorem receipt_2_15_2339_0_part2 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 256 128 = 88617020889104166146826909120 := rfl
private theorem receipt_2_15_2339_0_part3 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 384 128 = 79865893161197115500874945984 := rfl
private theorem receipt_2_15_2339_0_part4 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 512 128 = 71437027028564638656400618944 := rfl
private theorem receipt_2_15_2339_0_part5 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 640 128 = 63323347923950873523297785280 := rfl
private theorem receipt_2_15_2339_0_part6 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 768 128 = 55517854779956372584331457984 := rfl
private theorem receipt_2_15_2339_0_part7 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 896 128 = 48013619721375573960624592320 := rfl
private theorem receipt_2_15_2339_0_part8 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 1024 128 = 40803787757534272477144872384 := rfl
private theorem receipt_2_15_2339_0_part9 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 1152 128 = 33881576476108165359370162179 := rfl
private theorem receipt_2_15_2339_0_part10 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 1280 128 = 27240280421588126270072827314 := rfl
private theorem receipt_2_15_2339_0_part11 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 1408 128 = 20873268753707976898309823778 := rfl
private theorem receipt_2_15_2339_0_part12 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 1536 128 = 14773964362414030735239328260 := rfl
private theorem receipt_2_15_2339_0_part13 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 1664 128 = 8935858837926344028954975789 := rfl
private theorem receipt_2_15_2339_0_part14 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 1792 128 = 3352515032016455021036178894 := rfl
private theorem receipt_2_15_2339_0_part15 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 1920 15 = 38925655678335121886984472 := rfl
private theorem receipt_2_15_2339_0_join0 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 0 256 = 204812287332083279866770393984 :=
  phaseBlock_append receipt_2_15_2339_0_part0 receipt_2_15_2339_0_part1 rfl rfl rfl
private theorem receipt_2_15_2339_0_join1 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 256 256 = 168482914050301281647701855104 :=
  phaseBlock_append receipt_2_15_2339_0_part2 receipt_2_15_2339_0_part3 rfl rfl rfl
private theorem receipt_2_15_2339_0_join2 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 0 512 = 373295201382384561514472249088 :=
  phaseBlock_append receipt_2_15_2339_0_join0 receipt_2_15_2339_0_join1 rfl rfl rfl
private theorem receipt_2_15_2339_0_join3 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 512 256 = 134760374952515512179698404224 :=
  phaseBlock_append receipt_2_15_2339_0_part4 receipt_2_15_2339_0_part5 rfl rfl rfl
private theorem receipt_2_15_2339_0_join4 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 768 256 = 103531474501331946544956050304 :=
  phaseBlock_append receipt_2_15_2339_0_part6 receipt_2_15_2339_0_part7 rfl rfl rfl
private theorem receipt_2_15_2339_0_join5 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 512 512 = 238291849453847458724654454528 :=
  phaseBlock_append receipt_2_15_2339_0_join3 receipt_2_15_2339_0_join4 rfl rfl rfl
private theorem receipt_2_15_2339_0_join6 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 0 1024 = 611587050836232020239126703616 :=
  phaseBlock_append receipt_2_15_2339_0_join2 receipt_2_15_2339_0_join5 rfl rfl rfl
private theorem receipt_2_15_2339_0_join7 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 1024 256 = 74685364233642437836515034563 :=
  phaseBlock_append receipt_2_15_2339_0_part8 receipt_2_15_2339_0_part9 rfl rfl rfl
private theorem receipt_2_15_2339_0_join8 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 1280 256 = 48113549175296103168382651092 :=
  phaseBlock_append receipt_2_15_2339_0_part10 receipt_2_15_2339_0_part11 rfl rfl rfl
private theorem receipt_2_15_2339_0_join9 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 1024 512 = 122798913408938541004897685655 :=
  phaseBlock_append receipt_2_15_2339_0_join7 receipt_2_15_2339_0_join8 rfl rfl rfl
private theorem receipt_2_15_2339_0_join10 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 1536 256 = 23709823200340374764194304049 :=
  phaseBlock_append receipt_2_15_2339_0_part12 receipt_2_15_2339_0_part13 rfl rfl rfl
private theorem receipt_2_15_2339_0_join11 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 1792 143 = 3391440687694790142923163366 :=
  phaseBlock_append receipt_2_15_2339_0_part14 receipt_2_15_2339_0_part15 rfl rfl rfl
private theorem receipt_2_15_2339_0_join12 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 1536 399 = 27101263888035164907117467415 :=
  phaseBlock_append receipt_2_15_2339_0_join10 receipt_2_15_2339_0_join11 rfl rfl rfl
private theorem receipt_2_15_2339_0_join13 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 1024 911 = 149900177296973705912015153070 :=
  phaseBlock_append receipt_2_15_2339_0_join9 receipt_2_15_2339_0_join12 rfl rfl rfl
private theorem receipt_2_15_2339_0_join14 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 0) 0 1935 = 761487228133205726151141856686 :=
  phaseBlock_append receipt_2_15_2339_0_join6 receipt_2_15_2339_0_join13 rfl rfl rfl

private theorem receipt_2_15_2339_0 : fastPhase (bank 2 15).shape 179827 2339 76 1 0 7 0 = 761487228133205726151141856686 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_15_2339_0_join14

private theorem receipt_2_15_2339_1_part0 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 0 128 = 107040767707726698636274714944 := rfl
private theorem receipt_2_15_2339_1_part1 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 128 128 = 97626181547824331490477893952 := rfl
private theorem receipt_2_15_2339_1_part2 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 256 128 = 88548172690975191735488383296 := rfl
private theorem receipt_2_15_2339_1_part3 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 384 128 = 79799519213935276362847136064 := rfl
private theorem receipt_2_15_2339_1_part4 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 512 128 = 71373073306285697346380941632 := rfl
private theorem receipt_2_15_2339_1_part5 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 640 128 = 63261760962770152707689212224 := rfl
private theorem receipt_2_15_2339_1_part6 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 768 128 = 55458581675632397581630769472 := rfl
private theorem receipt_2_15_2339_1_part7 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 896 128 = 47956608126953715281810630976 := rfl
private theorem receipt_2_15_2339_1_part8 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 1024 128 = 40748985880990388366066796864 := rfl
private theorem receipt_2_15_2339_1_part9 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 1152 128 = 33828933077989845575758218870 := rfl
private theorem receipt_2_15_2339_1_part10 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 1280 128 = 27189744804177909910850120388 := rfl
private theorem receipt_2_15_2339_1_part11 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 1408 128 = 20824790744403975999719055916 := rfl
private theorem receipt_2_15_2339_1_part12 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 1536 128 = 14727494331101890816418526138 := rfl
private theorem receipt_2_15_2339_1_part13 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 1664 128 = 8891347698493456995377792997 := rfl
private theorem receipt_2_15_2339_1_part14 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 1792 128 = 3309914239992415085758544544 := rfl
private theorem receipt_2_15_2339_1_part15 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 1920 15 = 34056203902833353175664548 := rfl
private theorem receipt_2_15_2339_1_join0 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 0 256 = 204666949255551030126752608896 :=
  phaseBlock_append receipt_2_15_2339_1_part0 receipt_2_15_2339_1_part1 rfl rfl rfl
private theorem receipt_2_15_2339_1_join1 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 256 256 = 168347691904910468098335519360 :=
  phaseBlock_append receipt_2_15_2339_1_part2 receipt_2_15_2339_1_part3 rfl rfl rfl
private theorem receipt_2_15_2339_1_join2 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 0 512 = 373014641160461498225088128256 :=
  phaseBlock_append receipt_2_15_2339_1_join0 receipt_2_15_2339_1_join1 rfl rfl rfl
private theorem receipt_2_15_2339_1_join3 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 512 256 = 134634834269055850054070153856 :=
  phaseBlock_append receipt_2_15_2339_1_part4 receipt_2_15_2339_1_part5 rfl rfl rfl
private theorem receipt_2_15_2339_1_join4 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 768 256 = 103415189802586112863441400448 :=
  phaseBlock_append receipt_2_15_2339_1_part6 receipt_2_15_2339_1_part7 rfl rfl rfl
private theorem receipt_2_15_2339_1_join5 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 512 512 = 238050024071641962917511554304 :=
  phaseBlock_append receipt_2_15_2339_1_join3 receipt_2_15_2339_1_join4 rfl rfl rfl
private theorem receipt_2_15_2339_1_join6 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 0 1024 = 611064665232103461142599682560 :=
  phaseBlock_append receipt_2_15_2339_1_join2 receipt_2_15_2339_1_join5 rfl rfl rfl
private theorem receipt_2_15_2339_1_join7 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 1024 256 = 74577918958980233941825015734 :=
  phaseBlock_append receipt_2_15_2339_1_part8 receipt_2_15_2339_1_part9 rfl rfl rfl
private theorem receipt_2_15_2339_1_join8 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 1280 256 = 48014535548581885910569176304 :=
  phaseBlock_append receipt_2_15_2339_1_part10 receipt_2_15_2339_1_part11 rfl rfl rfl
private theorem receipt_2_15_2339_1_join9 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 1024 512 = 122592454507562119852394192038 :=
  phaseBlock_append receipt_2_15_2339_1_join7 receipt_2_15_2339_1_join8 rfl rfl rfl
private theorem receipt_2_15_2339_1_join10 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 1536 256 = 23618842029595347811796319135 :=
  phaseBlock_append receipt_2_15_2339_1_part12 receipt_2_15_2339_1_part13 rfl rfl rfl
private theorem receipt_2_15_2339_1_join11 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 1792 143 = 3343970443895248438934209092 :=
  phaseBlock_append receipt_2_15_2339_1_part14 receipt_2_15_2339_1_part15 rfl rfl rfl
private theorem receipt_2_15_2339_1_join12 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 1536 399 = 26962812473490596250730528227 :=
  phaseBlock_append receipt_2_15_2339_1_join10 receipt_2_15_2339_1_join11 rfl rfl rfl
private theorem receipt_2_15_2339_1_join13 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 1024 911 = 149555266981052716103124720265 :=
  phaseBlock_append receipt_2_15_2339_1_join9 receipt_2_15_2339_1_join12 rfl rfl rfl
private theorem receipt_2_15_2339_1_join14 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2339 76 1 0 7 1) 0 1935 = 760619932213156177245724402825 :=
  phaseBlock_append receipt_2_15_2339_1_join6 receipt_2_15_2339_1_join13 rfl rfl rfl

private theorem receipt_2_15_2339_1 : fastPhase (bank 2 15).shape 179827 2339 76 1 0 7 1 = 760619932213156177245724402825 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_15_2339_1_join14

private theorem receipt_2_15_2340_0_part0 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 0 128 = 107115688950596627437883749632 := rfl
private theorem receipt_2_15_2340_0_part1 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 128 128 = 97698401848252162977879586048 := rfl
private theorem receipt_2_15_2340_0_part2 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 256 128 = 88617755664337390115329996032 := rfl
private theorem receipt_2_15_2340_0_part3 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 384 128 = 79866527681120706955592430848 := rfl
private theorem receipt_2_15_2340_0_part4 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 512 128 = 71437569298566313598136218880 := rfl
private theorem receipt_2_15_2340_0_part5 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 640 128 = 63323805726660907988077147392 := rfl
private theorem receipt_2_15_2340_0_part6 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 768 128 = 55518235677740381767712044288 := rfl
private theorem receipt_2_15_2340_0_part7 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 896 128 = 48013931058816516128053359872 := rfl
private theorem receipt_2_15_2340_0_part8 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 1024 128 = 40804036663903677660363748608 := rfl
private theorem receipt_2_15_2340_0_part9 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 1152 128 = 33881769866798663927779042122 := rfl
private theorem receipt_2_15_2340_0_part10 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 1280 128 = 27240424871607095916447967399 := rfl
private theorem receipt_2_15_2340_0_part11 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 1408 128 = 20873370763750854819125534739 := rfl
private theorem receipt_2_15_2340_0_part12 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 1536 128 = 14774030323825975654912409306 := rfl
private theorem receipt_2_15_2340_0_part13 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 1664 128 = 8935894924979820747079949112 := rfl
private theorem receipt_2_15_2340_0_part14 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 1792 128 = 3352527208350240025903154574 := rfl
private theorem receipt_2_15_2340_0_part15 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 1920 15 = 38925785221153303816480368 := rfl
private theorem receipt_2_15_2340_0_join0 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 0 256 = 204814090798848790415763335680 :=
  phaseBlock_append receipt_2_15_2340_0_part0 receipt_2_15_2340_0_part1 rfl rfl rfl
private theorem receipt_2_15_2340_0_join1 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 256 256 = 168484283345458097070922426880 :=
  phaseBlock_append receipt_2_15_2340_0_part2 receipt_2_15_2340_0_part3 rfl rfl rfl
private theorem receipt_2_15_2340_0_join2 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 0 512 = 373298374144306887486685762560 :=
  phaseBlock_append receipt_2_15_2340_0_join0 receipt_2_15_2340_0_join1 rfl rfl rfl
private theorem receipt_2_15_2340_0_join3 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 512 256 = 134761375025227221586213366272 :=
  phaseBlock_append receipt_2_15_2340_0_part4 receipt_2_15_2340_0_part5 rfl rfl rfl
private theorem receipt_2_15_2340_0_join4 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 768 256 = 103532166736556897895765404160 :=
  phaseBlock_append receipt_2_15_2340_0_part6 receipt_2_15_2340_0_part7 rfl rfl rfl
private theorem receipt_2_15_2340_0_join5 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 512 512 = 238293541761784119481978770432 :=
  phaseBlock_append receipt_2_15_2340_0_join3 receipt_2_15_2340_0_join4 rfl rfl rfl
private theorem receipt_2_15_2340_0_join6 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 0 1024 = 611591915906091006968664532992 :=
  phaseBlock_append receipt_2_15_2340_0_join2 receipt_2_15_2340_0_join5 rfl rfl rfl
private theorem receipt_2_15_2340_0_join7 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 1024 256 = 74685806530702341588142790730 :=
  phaseBlock_append receipt_2_15_2340_0_part8 receipt_2_15_2340_0_part9 rfl rfl rfl
private theorem receipt_2_15_2340_0_join8 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 1280 256 = 48113795635357950735573502138 :=
  phaseBlock_append receipt_2_15_2340_0_part10 receipt_2_15_2340_0_part11 rfl rfl rfl
private theorem receipt_2_15_2340_0_join9 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 1024 512 = 122799602166060292323716292868 :=
  phaseBlock_append receipt_2_15_2340_0_join7 receipt_2_15_2340_0_join8 rfl rfl rfl
private theorem receipt_2_15_2340_0_join10 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 1536 256 = 23709925248805796401992358418 :=
  phaseBlock_append receipt_2_15_2340_0_part12 receipt_2_15_2340_0_part13 rfl rfl rfl
private theorem receipt_2_15_2340_0_join11 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 1792 143 = 3391452993571393329719634942 :=
  phaseBlock_append receipt_2_15_2340_0_part14 receipt_2_15_2340_0_part15 rfl rfl rfl
private theorem receipt_2_15_2340_0_join12 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 1536 399 = 27101378242377189731711993360 :=
  phaseBlock_append receipt_2_15_2340_0_join10 receipt_2_15_2340_0_join11 rfl rfl rfl
private theorem receipt_2_15_2340_0_join13 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 1024 911 = 149900980408437482055428286228 :=
  phaseBlock_append receipt_2_15_2340_0_join9 receipt_2_15_2340_0_join12 rfl rfl rfl
private theorem receipt_2_15_2340_0_join14 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 0) 0 1935 = 761492896314528489024092819220 :=
  phaseBlock_append receipt_2_15_2340_0_join6 receipt_2_15_2340_0_join13 rfl rfl rfl

private theorem receipt_2_15_2340_0 : fastPhase (bank 2 15).shape 179827 2340 76 1 0 7 0 = 761492896314528489024092819220 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_15_2340_0_join14

private theorem receipt_2_15_2340_1_part0 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 0 128 = 107041727365629373493129174592 := rfl
private theorem receipt_2_15_2340_1_part1 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 128 128 = 97627024296623684810278854208 := rfl
private theorem receipt_2_15_2340_1_part2 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 256 128 = 88548906987971570865300430400 := rfl
private theorem receipt_2_15_2340_1_part3 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 384 128 = 79800153288667615921895464512 := rfl
private theorem receipt_2_15_2340_1_part4 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 512 128 = 71373615163045784800432807488 := rfl
private theorem receipt_2_15_2340_1_part5 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 640 128 = 63262218383106118729483181632 := rfl
private theorem receipt_2_15_2340_1_part6 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 768 128 = 55458962220841431197353762368 := rfl
private theorem receipt_2_15_2340_1_part7 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 896 128 = 47956919140564003803622760000 := rfl
private theorem receipt_2_15_2340_1_part8 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 1024 128 = 40749234491232282110674001472 := rfl
private theorem receipt_2_15_2340_1_part9 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 1152 128 = 33829126199229952171819547610 := rfl
private theorem receipt_2_15_2340_1_part10 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 1280 128 = 27189889010641925639312997994 := rfl
private theorem receipt_2_15_2340_1_part11 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 1408 128 = 20824892535899028312472574474 := rfl
private theorem receipt_2_15_2340_1_part12 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 1536 128 = 14727560097948809944610968134 := rfl
private theorem receipt_2_15_2340_1_part13 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 1664 128 = 8891383613960198456815054800 := rfl
private theorem receipt_2_15_2340_1_part14 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 1792 128 = 3309926266718615297961513103 := rfl
private theorem receipt_2_15_2340_1_part15 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 1920 15 = 34056317305962898175785178 := rfl
private theorem receipt_2_15_2340_1_join0 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 0 256 = 204668751662253058303408028800 :=
  phaseBlock_append receipt_2_15_2340_1_part0 receipt_2_15_2340_1_part1 rfl rfl rfl
private theorem receipt_2_15_2340_1_join1 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 256 256 = 168349060276639186787195894912 :=
  phaseBlock_append receipt_2_15_2340_1_part2 receipt_2_15_2340_1_part3 rfl rfl rfl
private theorem receipt_2_15_2340_1_join2 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 0 512 = 373017811938892245090603923712 :=
  phaseBlock_append receipt_2_15_2340_1_join0 receipt_2_15_2340_1_join1 rfl rfl rfl
private theorem receipt_2_15_2340_1_join3 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 512 256 = 134635833546151903529915989120 :=
  phaseBlock_append receipt_2_15_2340_1_part4 receipt_2_15_2340_1_part5 rfl rfl rfl
private theorem receipt_2_15_2340_1_join4 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 768 256 = 103415881361405435000976522368 :=
  phaseBlock_append receipt_2_15_2340_1_part6 receipt_2_15_2340_1_part7 rfl rfl rfl
private theorem receipt_2_15_2340_1_join5 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 512 512 = 238051714907557338530892511488 :=
  phaseBlock_append receipt_2_15_2340_1_join3 receipt_2_15_2340_1_join4 rfl rfl rfl
private theorem receipt_2_15_2340_1_join6 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 0 1024 = 611069526846449583621496435200 :=
  phaseBlock_append receipt_2_15_2340_1_join2 receipt_2_15_2340_1_join5 rfl rfl rfl
private theorem receipt_2_15_2340_1_join7 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 1024 256 = 74578360690462234282493549082 :=
  phaseBlock_append receipt_2_15_2340_1_part8 receipt_2_15_2340_1_part9 rfl rfl rfl
private theorem receipt_2_15_2340_1_join8 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 1280 256 = 48014781546540953951785572468 :=
  phaseBlock_append receipt_2_15_2340_1_part10 receipt_2_15_2340_1_part11 rfl rfl rfl
private theorem receipt_2_15_2340_1_join9 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 1024 512 = 122593142237003188234279121550 :=
  phaseBlock_append receipt_2_15_2340_1_join7 receipt_2_15_2340_1_join8 rfl rfl rfl
private theorem receipt_2_15_2340_1_join10 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 1536 256 = 23618943711909008401426022934 :=
  phaseBlock_append receipt_2_15_2340_1_part12 receipt_2_15_2340_1_part13 rfl rfl rfl
private theorem receipt_2_15_2340_1_join11 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 1792 143 = 3343982584024578196137298281 :=
  phaseBlock_append receipt_2_15_2340_1_part14 receipt_2_15_2340_1_part15 rfl rfl rfl
private theorem receipt_2_15_2340_1_join12 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 1536 399 = 26962926295933586597563321215 :=
  phaseBlock_append receipt_2_15_2340_1_join10 receipt_2_15_2340_1_join11 rfl rfl rfl
private theorem receipt_2_15_2340_1_join13 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 1024 911 = 149556068532936774831842442765 :=
  phaseBlock_append receipt_2_15_2340_1_join9 receipt_2_15_2340_1_join12 rfl rfl rfl
private theorem receipt_2_15_2340_1_join14 :
    phaseBlock (fastLayer (bank 2 15).shape 179827 2340 76 1 0 7 1) 0 1935 = 760625595379386358453338877965 :=
  phaseBlock_append receipt_2_15_2340_1_join6 receipt_2_15_2340_1_join13 rfl rfl rfl

private theorem receipt_2_15_2340_1 : fastPhase (bank 2 15).shape 179827 2340 76 1 0 7 1 = 760625595379386358453338877965 :=
  phase_of_block (n := 1935) (by decide +kernel) receipt_2_15_2340_1_join14

theorem receipt_2_15 : Checked (bank 2 15) 76 0 7 := by
  refine checked_from_values (bank 2 15) 76 0 7
    (P3_7_1.checked (bank 2 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9204_1934)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_15_2339_0 receipt_2_15_2339_1 receipt_2_15_2340_0 receipt_2_15_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_15_2339_0_part0 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 0 128 = 22478526881604565348881550272 := rfl
private theorem receipt_3_15_2339_0_part1 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 128 128 = 20599784232757432236182932416 := rfl
private theorem receipt_3_15_2339_0_part2 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 256 128 = 18772943701172527383610510272 := rfl
private theorem receipt_3_15_2339_0_part3 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 384 128 = 16999014938429301585078553536 := rfl
private theorem receipt_3_15_2339_0_part4 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 512 128 = 15279001810839590180683205568 := rfl
private theorem receipt_3_15_2339_0_part5 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 640 128 = 13613902408919553886271835072 := rfl
private theorem receipt_3_15_2339_0_part6 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 768 128 = 12004709056861619623012387776 := rfl
private theorem receipt_3_15_2339_0_part7 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 896 128 = 10452408322006421346962738112 := rfl
private theorem receipt_3_15_2339_0_part8 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 1024 128 = 8957981024314740878640040896 := rfl
private theorem receipt_3_15_2339_0_part9 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 1152 128 = 7522402245839448732590083008 := rfl
private theorem receipt_3_15_2339_0_part10 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 1280 128 = 6146641340197444946956635072 := rfl
private theorem receipt_3_15_2339_0_part11 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 1408 128 = 4831661942041599913050803136 := rfl
private theorem receipt_3_15_2339_0_part12 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 1536 128 = 3578421976532695204920380352 := rfl
private theorem receipt_3_15_2339_0_part13 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 1664 128 = 2387873668811364408919198656 := rfl
private theorem receipt_3_15_2339_0_part14 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 1792 128 = 1260963553470033953276480448 := rfl
private theorem receipt_3_15_2339_0_part15 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 1920 88 = 246737225066112579477564468 := rfl
private theorem receipt_3_15_2339_0_join0 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 0 256 = 43078311114361997585064482688 :=
  phaseBlock_append receipt_3_15_2339_0_part0 receipt_3_15_2339_0_part1 rfl rfl rfl
private theorem receipt_3_15_2339_0_join1 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 256 256 = 35771958639601828968689063808 :=
  phaseBlock_append receipt_3_15_2339_0_part2 receipt_3_15_2339_0_part3 rfl rfl rfl
private theorem receipt_3_15_2339_0_join2 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 0 512 = 78850269753963826553753546496 :=
  phaseBlock_append receipt_3_15_2339_0_join0 receipt_3_15_2339_0_join1 rfl rfl rfl
private theorem receipt_3_15_2339_0_join3 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 512 256 = 28892904219759144066955040640 :=
  phaseBlock_append receipt_3_15_2339_0_part4 receipt_3_15_2339_0_part5 rfl rfl rfl
private theorem receipt_3_15_2339_0_join4 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 768 256 = 22457117378868040969975125888 :=
  phaseBlock_append receipt_3_15_2339_0_part6 receipt_3_15_2339_0_part7 rfl rfl rfl
private theorem receipt_3_15_2339_0_join5 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 512 512 = 51350021598627185036930166528 :=
  phaseBlock_append receipt_3_15_2339_0_join3 receipt_3_15_2339_0_join4 rfl rfl rfl
private theorem receipt_3_15_2339_0_join6 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 0 1024 = 130200291352591011590683713024 :=
  phaseBlock_append receipt_3_15_2339_0_join2 receipt_3_15_2339_0_join5 rfl rfl rfl
private theorem receipt_3_15_2339_0_join7 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 1024 256 = 16480383270154189611230123904 :=
  phaseBlock_append receipt_3_15_2339_0_part8 receipt_3_15_2339_0_part9 rfl rfl rfl
private theorem receipt_3_15_2339_0_join8 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 1280 256 = 10978303282239044860007438208 :=
  phaseBlock_append receipt_3_15_2339_0_part10 receipt_3_15_2339_0_part11 rfl rfl rfl
private theorem receipt_3_15_2339_0_join9 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 1024 512 = 27458686552393234471237562112 :=
  phaseBlock_append receipt_3_15_2339_0_join7 receipt_3_15_2339_0_join8 rfl rfl rfl
private theorem receipt_3_15_2339_0_join10 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 1536 256 = 5966295645344059613839579008 :=
  phaseBlock_append receipt_3_15_2339_0_part12 receipt_3_15_2339_0_part13 rfl rfl rfl
private theorem receipt_3_15_2339_0_join11 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 1792 216 = 1507700778536146532754044916 :=
  phaseBlock_append receipt_3_15_2339_0_part14 receipt_3_15_2339_0_part15 rfl rfl rfl
private theorem receipt_3_15_2339_0_join12 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 1536 472 = 7473996423880206146593623924 :=
  phaseBlock_append receipt_3_15_2339_0_join10 receipt_3_15_2339_0_join11 rfl rfl rfl
private theorem receipt_3_15_2339_0_join13 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 1024 984 = 34932682976273440617831186036 :=
  phaseBlock_append receipt_3_15_2339_0_join9 receipt_3_15_2339_0_join12 rfl rfl rfl
private theorem receipt_3_15_2339_0_join14 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 0) 0 2008 = 165132974328864452208514899060 :=
  phaseBlock_append receipt_3_15_2339_0_join6 receipt_3_15_2339_0_join13 rfl rfl rfl

private theorem receipt_3_15_2339_0 : fastPhase (bank 3 15).shape 179827 2339 76 1 1 1 0 = 165132974328864452208514899060 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_15_2339_0_join14

private theorem receipt_3_15_2339_1_part0 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 0 128 = 22463845961545003205772097920 := rfl
private theorem receipt_3_15_2339_1_part1 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 128 128 = 20585487463264902154283440512 := rfl
private theorem receipt_3_15_2339_1_part2 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 256 128 = 18759039643767964513850554752 := rfl
private theorem receipt_3_15_2339_1_part3 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 384 128 = 16985512107062564123883411840 := rfl
private theorem receipt_3_15_2339_1_part4 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 512 128 = 15265908671966352135114406272 := rfl
private theorem receipt_3_15_2339_1_part5 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 640 128 = 13601227381578197839167707520 := rfl
private theorem receipt_3_15_2339_1_part6 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 768 128 = 11992460512750129498128611712 := rfl
private theorem receipt_3_15_2339_1_part7 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 896 128 = 10440594585559275174112893312 := rfl
private theorem receipt_3_15_2339_1_part8 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 1024 128 = 8946610372779803558836156800 := rfl
private theorem receipt_3_15_2339_1_part9 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 1152 128 = 7511482909354864803183188352 := rfl
private theorem receipt_3_15_2339_1_part10 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 1280 128 = 6136181501868531346777307520 := rfl
private theorem receipt_3_15_2339_1_part11 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 1408 128 = 4821669738017738747549718912 := rfl
private theorem receipt_3_15_2339_1_part12 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 1536 128 = 3568905496084226511308863872 := rfl
private theorem receipt_3_15_2339_1_part13 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 1664 128 = 2378840954406478921309772160 := rfl
private theorem receipt_3_15_2339_1_part14 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 1792 128 = 1252422600851665867823413632 := rfl
private theorem receipt_3_15_2339_1_part15 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 1920 88 = 241154713060965278416050264 := rfl
private theorem receipt_3_15_2339_1_join0 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 0 256 = 43049333424809905360055538432 :=
  phaseBlock_append receipt_3_15_2339_1_part0 receipt_3_15_2339_1_part1 rfl rfl rfl
private theorem receipt_3_15_2339_1_join1 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 256 256 = 35744551750830528637733966592 :=
  phaseBlock_append receipt_3_15_2339_1_part2 receipt_3_15_2339_1_part3 rfl rfl rfl
private theorem receipt_3_15_2339_1_join2 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 0 512 = 78793885175640433997789505024 :=
  phaseBlock_append receipt_3_15_2339_1_join0 receipt_3_15_2339_1_join1 rfl rfl rfl
private theorem receipt_3_15_2339_1_join3 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 512 256 = 28867136053544549974282113792 :=
  phaseBlock_append receipt_3_15_2339_1_part4 receipt_3_15_2339_1_part5 rfl rfl rfl
private theorem receipt_3_15_2339_1_join4 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 768 256 = 22433055098309404672241505024 :=
  phaseBlock_append receipt_3_15_2339_1_part6 receipt_3_15_2339_1_part7 rfl rfl rfl
private theorem receipt_3_15_2339_1_join5 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 512 512 = 51300191151853954646523618816 :=
  phaseBlock_append receipt_3_15_2339_1_join3 receipt_3_15_2339_1_join4 rfl rfl rfl
private theorem receipt_3_15_2339_1_join6 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 0 1024 = 130094076327494388644313123840 :=
  phaseBlock_append receipt_3_15_2339_1_join2 receipt_3_15_2339_1_join5 rfl rfl rfl
private theorem receipt_3_15_2339_1_join7 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 1024 256 = 16458093282134668362019345152 :=
  phaseBlock_append receipt_3_15_2339_1_part8 receipt_3_15_2339_1_part9 rfl rfl rfl
private theorem receipt_3_15_2339_1_join8 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 1280 256 = 10957851239886270094327026432 :=
  phaseBlock_append receipt_3_15_2339_1_part10 receipt_3_15_2339_1_part11 rfl rfl rfl
private theorem receipt_3_15_2339_1_join9 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 1024 512 = 27415944522020938456346371584 :=
  phaseBlock_append receipt_3_15_2339_1_join7 receipt_3_15_2339_1_join8 rfl rfl rfl
private theorem receipt_3_15_2339_1_join10 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 1536 256 = 5947746450490705432618636032 :=
  phaseBlock_append receipt_3_15_2339_1_part12 receipt_3_15_2339_1_part13 rfl rfl rfl
private theorem receipt_3_15_2339_1_join11 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 1792 216 = 1493577313912631146239463896 :=
  phaseBlock_append receipt_3_15_2339_1_part14 receipt_3_15_2339_1_part15 rfl rfl rfl
private theorem receipt_3_15_2339_1_join12 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 1536 472 = 7441323764403336578858099928 :=
  phaseBlock_append receipt_3_15_2339_1_join10 receipt_3_15_2339_1_join11 rfl rfl rfl
private theorem receipt_3_15_2339_1_join13 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 1024 984 = 34857268286424275035204471512 :=
  phaseBlock_append receipt_3_15_2339_1_join9 receipt_3_15_2339_1_join12 rfl rfl rfl
private theorem receipt_3_15_2339_1_join14 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2339 76 1 1 1 1) 0 2008 = 164951344613918663679517595352 :=
  phaseBlock_append receipt_3_15_2339_1_join6 receipt_3_15_2339_1_join13 rfl rfl rfl

private theorem receipt_3_15_2339_1 : fastPhase (bank 3 15).shape 179827 2339 76 1 1 1 1 = 164951344613918663679517595352 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_15_2339_1_join14

private theorem receipt_3_15_2340_0_part0 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 0 128 = 22478727072166114807605976128 := rfl
private theorem receipt_3_15_2340_0_part1 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 128 128 = 20599955711434236139139210304 := rfl
private theorem receipt_3_15_2340_0_part2 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 256 128 = 18773089181060667812934442048 := rfl
private theorem receipt_3_15_2340_0_part3 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 384 128 = 16999137011841944768596679744 := rfl
private theorem receipt_3_15_2340_0_part4 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 512 128 = 15279102949877681954995985472 := rfl
private theorem receipt_3_15_2340_0_part5 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 640 128 = 13613984966041635550534605888 := rfl
private theorem receipt_3_15_2340_0_part6 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 768 128 = 12004775265452764183414103104 := rfl
private theorem receipt_3_15_2340_0_part7 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 896 128 = 10452460296946290151902485568 := rfl
private theorem receipt_3_15_2340_0_part8 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 1024 128 = 8958020762544760644601338944 := rfl
private theorem receipt_3_15_2340_0_part9 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 1152 128 = 7522431626929108960712956992 := rfl
private theorem receipt_3_15_2340_0_part10 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 1280 128 = 6146662126909715730307472448 := rfl
private theorem receipt_3_15_2340_0_part11 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 1408 128 = 4831675780897470134589987904 := rfl
private theorem receipt_3_15_2340_0_part12 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 1536 128 = 3578430398374831126167706688 := rfl
private theorem receipt_3_15_2340_0_part13 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 1664 128 = 2387878089366888649317063744 := rfl
private theorem receipt_3_15_2340_0_part14 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 1792 128 = 1260965273912424860250856512 := rfl
private theorem receipt_3_15_2340_0_part15 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 1920 88 = 246737463127251221542946892 := rfl
private theorem receipt_3_15_2340_0_join0 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 0 256 = 43078682783600350946745186432 :=
  phaseBlock_append receipt_3_15_2340_0_part0 receipt_3_15_2340_0_part1 rfl rfl rfl
private theorem receipt_3_15_2340_0_join1 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 256 256 = 35772226192902612581531121792 :=
  phaseBlock_append receipt_3_15_2340_0_part2 receipt_3_15_2340_0_part3 rfl rfl rfl
private theorem receipt_3_15_2340_0_join2 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 0 512 = 78850908976502963528276308224 :=
  phaseBlock_append receipt_3_15_2340_0_join0 receipt_3_15_2340_0_join1 rfl rfl rfl
private theorem receipt_3_15_2340_0_join3 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 512 256 = 28893087915919317505530591360 :=
  phaseBlock_append receipt_3_15_2340_0_part4 receipt_3_15_2340_0_part5 rfl rfl rfl
private theorem receipt_3_15_2340_0_join4 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 768 256 = 22457235562399054335316588672 :=
  phaseBlock_append receipt_3_15_2340_0_part6 receipt_3_15_2340_0_part7 rfl rfl rfl
private theorem receipt_3_15_2340_0_join5 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 512 512 = 51350323478318371840847180032 :=
  phaseBlock_append receipt_3_15_2340_0_join3 receipt_3_15_2340_0_join4 rfl rfl rfl
private theorem receipt_3_15_2340_0_join6 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 0 1024 = 130201232454821335369123488256 :=
  phaseBlock_append receipt_3_15_2340_0_join2 receipt_3_15_2340_0_join5 rfl rfl rfl
private theorem receipt_3_15_2340_0_join7 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 1024 256 = 16480452389473869605314295936 :=
  phaseBlock_append receipt_3_15_2340_0_part8 receipt_3_15_2340_0_part9 rfl rfl rfl
private theorem receipt_3_15_2340_0_join8 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 1280 256 = 10978337907807185864897460352 :=
  phaseBlock_append receipt_3_15_2340_0_part10 receipt_3_15_2340_0_part11 rfl rfl rfl
private theorem receipt_3_15_2340_0_join9 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 1024 512 = 27458790297281055470211756288 :=
  phaseBlock_append receipt_3_15_2340_0_join7 receipt_3_15_2340_0_join8 rfl rfl rfl
private theorem receipt_3_15_2340_0_join10 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 1536 256 = 5966308487741719775484770432 :=
  phaseBlock_append receipt_3_15_2340_0_part12 receipt_3_15_2340_0_part13 rfl rfl rfl
private theorem receipt_3_15_2340_0_join11 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 1792 216 = 1507702737039676081793803404 :=
  phaseBlock_append receipt_3_15_2340_0_part14 receipt_3_15_2340_0_part15 rfl rfl rfl
private theorem receipt_3_15_2340_0_join12 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 1536 472 = 7474011224781395857278573836 :=
  phaseBlock_append receipt_3_15_2340_0_join10 receipt_3_15_2340_0_join11 rfl rfl rfl
private theorem receipt_3_15_2340_0_join13 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 1024 984 = 34932801522062451327490330124 :=
  phaseBlock_append receipt_3_15_2340_0_join9 receipt_3_15_2340_0_join12 rfl rfl rfl
private theorem receipt_3_15_2340_0_join14 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 0) 0 2008 = 165134033976883786696613818380 :=
  phaseBlock_append receipt_3_15_2340_0_join6 receipt_3_15_2340_0_join13 rfl rfl rfl

private theorem receipt_3_15_2340_0 : fastPhase (bank 3 15).shape 179827 2340 76 1 1 1 0 = 165134033976883786696613818380 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_15_2340_0_join14

private theorem receipt_3_15_2340_1_part0 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 0 128 = 22464046000467491602148186688 := rfl
private theorem receipt_3_15_2340_1_part1 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 128 128 = 20585658804526369837604067904 := rfl
private theorem receipt_3_15_2340_1_part2 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 256 128 = 18759184999797060277127633472 := rfl
private theorem receipt_3_15_2340_1_part3 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 384 128 = 16985634069508483744139958848 := rfl
private theorem receipt_3_15_2340_1_part4 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 512 128 = 15266009712269528201470630464 := rfl
private theorem receipt_3_15_2340_1_part5 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 640 128 = 13601309851540109971624876608 := rfl
private theorem receipt_3_15_2340_1_part6 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 768 128 = 11992526645102234957050698304 := rfl
private theorem receipt_3_15_2340_1_part7 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 896 128 = 10440646494531059860406000192 := rfl
private theorem receipt_3_15_2340_1_part8 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 1024 128 = 8946650054665953404825721408 := rfl
private theorem receipt_3_15_2340_1_part9 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 1152 128 = 7511512243081557554188966464 := rfl
private theorem receipt_3_15_2340_1_part10 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 1280 128 = 6136202249558848733386136128 := rfl
private theorem receipt_3_15_2340_1_part11 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 1408 128 = 4821683545556199048586058304 := rfl
private theorem receipt_3_15_2340_1_part12 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 1536 128 = 3568913893680437507503118912 := rfl
private theorem receipt_3_15_2340_1_part13 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 1664 128 = 2378845357157911239664392768 := rfl
private theorem receipt_3_15_2340_1_part14 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 1792 128 = 1252424309305546716676774464 := rfl
private theorem receipt_3_15_2340_1_part15 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 1920 88 = 241154945929688261575226892 := rfl
private theorem receipt_3_15_2340_1_join0 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 0 256 = 43049704804993861439752254592 :=
  phaseBlock_append receipt_3_15_2340_1_part0 receipt_3_15_2340_1_part1 rfl rfl rfl
private theorem receipt_3_15_2340_1_join1 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 256 256 = 35744819069305544021267592320 :=
  phaseBlock_append receipt_3_15_2340_1_part2 receipt_3_15_2340_1_part3 rfl rfl rfl
private theorem receipt_3_15_2340_1_join2 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 0 512 = 78794523874299405461019846912 :=
  phaseBlock_append receipt_3_15_2340_1_join0 receipt_3_15_2340_1_join1 rfl rfl rfl
private theorem receipt_3_15_2340_1_join3 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 512 256 = 28867319563809638173095507072 :=
  phaseBlock_append receipt_3_15_2340_1_part4 receipt_3_15_2340_1_part5 rfl rfl rfl
private theorem receipt_3_15_2340_1_join4 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 768 256 = 22433173139633294817456698496 :=
  phaseBlock_append receipt_3_15_2340_1_part6 receipt_3_15_2340_1_part7 rfl rfl rfl
private theorem receipt_3_15_2340_1_join5 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 512 512 = 51300492703442932990552205568 :=
  phaseBlock_append receipt_3_15_2340_1_join3 receipt_3_15_2340_1_join4 rfl rfl rfl
private theorem receipt_3_15_2340_1_join6 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 0 1024 = 130095016577742338451572052480 :=
  phaseBlock_append receipt_3_15_2340_1_join2 receipt_3_15_2340_1_join5 rfl rfl rfl
private theorem receipt_3_15_2340_1_join7 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 1024 256 = 16458162297747510959014687872 :=
  phaseBlock_append receipt_3_15_2340_1_part8 receipt_3_15_2340_1_part9 rfl rfl rfl
private theorem receipt_3_15_2340_1_join8 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 1280 256 = 10957885795115047781972194432 :=
  phaseBlock_append receipt_3_15_2340_1_part10 receipt_3_15_2340_1_part11 rfl rfl rfl
private theorem receipt_3_15_2340_1_join9 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 1024 512 = 27416048092862558740986882304 :=
  phaseBlock_append receipt_3_15_2340_1_join7 receipt_3_15_2340_1_join8 rfl rfl rfl
private theorem receipt_3_15_2340_1_join10 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 1536 256 = 5947759250838348747167511680 :=
  phaseBlock_append receipt_3_15_2340_1_part12 receipt_3_15_2340_1_part13 rfl rfl rfl
private theorem receipt_3_15_2340_1_join11 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 1792 216 = 1493579255235234978252001356 :=
  phaseBlock_append receipt_3_15_2340_1_part14 receipt_3_15_2340_1_part15 rfl rfl rfl
private theorem receipt_3_15_2340_1_join12 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 1536 472 = 7441338506073583725419513036 :=
  phaseBlock_append receipt_3_15_2340_1_join10 receipt_3_15_2340_1_join11 rfl rfl rfl
private theorem receipt_3_15_2340_1_join13 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 1024 984 = 34857386598936142466406395340 :=
  phaseBlock_append receipt_3_15_2340_1_join9 receipt_3_15_2340_1_join12 rfl rfl rfl
private theorem receipt_3_15_2340_1_join14 :
    phaseBlock (fastLayer (bank 3 15).shape 179827 2340 76 1 1 1 1) 0 2008 = 164952403176678480917978447820 :=
  phaseBlock_append receipt_3_15_2340_1_join6 receipt_3_15_2340_1_join13 rfl rfl rfl

private theorem receipt_3_15_2340_1 : fastPhase (bank 3 15).shape 179827 2340 76 1 1 1 1 = 164952403176678480917978447820 :=
  phase_of_block (n := 2008) (by decide +kernel) receipt_3_15_2340_1_join14

theorem receipt_3_15 : Checked (bank 3 15) 76 1 1 := by
  refine checked_from_values (bank 3 15) 76 1 1
    (P3_7_1.checked (bank 3 15) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_9204_2007)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_15_2339_0 receipt_3_15_2339_1 receipt_3_15_2340_0 receipt_3_15_2340_1 (by decide +kernel) (by decide +kernel)

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
    (word : K1.I → K1_14.L) (lo : 2339 ≤ h) (hi : h ≤ 33561) (rect : Fin 4)
    (i : Fin 1) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group6_stage i)).shape
      (cutoff h rect (group6_stage i)), ¬ G∣Q :=
  (group6_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group6_avoids

end Lower6960.RescueSource
