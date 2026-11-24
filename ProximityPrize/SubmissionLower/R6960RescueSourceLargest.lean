import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt0

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open HelperSource (WidthGuard)

def largestBank : Bank := ⟨⟨9071,12604,2749,270589⟩,22490098892800000,695862530200649⟩

private theorem moment_12604_2749_part0 :
    blockEstimate 12604 2749 2749 128 = 4475130400 := by decide +kernel
private theorem moment_12604_2749_part1 :
    blockEstimate 12604 2749 2877 128 = 30641234464 := by decide +kernel
private theorem moment_12604_2749_part2 :
    blockEstimate 12604 2749 3005 128 = 82028737056 := by decide +kernel
private theorem moment_12604_2749_part3 :
    blockEstimate 12604 2749 3133 128 = 157832331808 := by decide +kernel
private theorem moment_12604_2749_part4 :
    blockEstimate 12604 2749 3261 128 = 257246712352 := by decide +kernel
private theorem moment_12604_2749_part5 :
    blockEstimate 12604 2749 3389 128 = 379466572320 := by decide +kernel
private theorem moment_12604_2749_part6 :
    blockEstimate 12604 2749 3517 128 = 523686605344 := by decide +kernel
private theorem moment_12604_2749_part7 :
    blockEstimate 12604 2749 3645 128 = 689101505056 := by decide +kernel
private theorem moment_12604_2749_part8 :
    blockEstimate 12604 2749 3773 128 = 874905965088 := by decide +kernel
private theorem moment_12604_2749_part9 :
    blockEstimate 12604 2749 3901 128 = 1080294679072 := by decide +kernel
private theorem moment_12604_2749_part10 :
    blockEstimate 12604 2749 4029 128 = 1304462340640 := by decide +kernel
private theorem moment_12604_2749_part11 :
    blockEstimate 12604 2749 4157 128 = 1546603643424 := by decide +kernel
private theorem moment_12604_2749_part12 :
    blockEstimate 12604 2749 4285 128 = 1805913281056 := by decide +kernel
private theorem moment_12604_2749_part13 :
    blockEstimate 12604 2749 4413 128 = 2081585947168 := by decide +kernel
private theorem moment_12604_2749_part14 :
    blockEstimate 12604 2749 4541 128 = 2372816335392 := by decide +kernel
private theorem moment_12604_2749_part15 :
    blockEstimate 12604 2749 4669 128 = 2678799139360 := by decide +kernel
private theorem moment_12604_2749_part16 :
    blockEstimate 12604 2749 4797 128 = 2998729052704 := by decide +kernel
private theorem moment_12604_2749_part17 :
    blockEstimate 12604 2749 4925 128 = 3331800769056 := by decide +kernel
private theorem moment_12604_2749_part18 :
    blockEstimate 12604 2749 5053 128 = 3677208982048 := by decide +kernel
private theorem moment_12604_2749_part19 :
    blockEstimate 12604 2749 5181 128 = 4034148385312 := by decide +kernel
private theorem moment_12604_2749_part20 :
    blockEstimate 12604 2749 5309 128 = 4401813672480 := by decide +kernel
private theorem moment_12604_2749_part21 :
    blockEstimate 12604 2749 5437 128 = 4778908137275 := by decide +kernel
private theorem moment_12604_2749_part22 :
    blockEstimate 12604 2749 5565 128 = 5154593576000 := by decide +kernel
private theorem moment_12604_2749_part23 :
    blockEstimate 12604 2749 5693 128 = 5519119144000 := by decide +kernel
private theorem moment_12604_2749_part24 :
    blockEstimate 12604 2749 5821 128 = 5872110376000 := by decide +kernel
private theorem moment_12604_2749_part25 :
    blockEstimate 12604 2749 5949 128 = 6213567272000 := by decide +kernel
private theorem moment_12604_2749_part26 :
    blockEstimate 12604 2749 6077 128 = 6543489832000 := by decide +kernel
private theorem moment_12604_2749_part27 :
    blockEstimate 12604 2749 6205 128 = 6861878056000 := by decide +kernel
private theorem moment_12604_2749_part28 :
    blockEstimate 12604 2749 6333 128 = 7168731944000 := by decide +kernel
private theorem moment_12604_2749_part29 :
    blockEstimate 12604 2749 6461 128 = 7464051496000 := by decide +kernel
private theorem moment_12604_2749_part30 :
    blockEstimate 12604 2749 6589 128 = 7747836712000 := by decide +kernel
private theorem moment_12604_2749_part31 :
    blockEstimate 12604 2749 6717 128 = 8020087592000 := by decide +kernel
private theorem moment_12604_2749_part32 :
    blockEstimate 12604 2749 6845 128 = 8280804136000 := by decide +kernel
private theorem moment_12604_2749_part33 :
    blockEstimate 12604 2749 6973 128 = 8529986344000 := by decide +kernel
private theorem moment_12604_2749_part34 :
    blockEstimate 12604 2749 7101 128 = 8767634216000 := by decide +kernel
private theorem moment_12604_2749_part35 :
    blockEstimate 12604 2749 7229 128 = 8993747752000 := by decide +kernel
private theorem moment_12604_2749_part36 :
    blockEstimate 12604 2749 7357 128 = 9208326952000 := by decide +kernel
private theorem moment_12604_2749_part37 :
    blockEstimate 12604 2749 7485 128 = 9411371816000 := by decide +kernel
private theorem moment_12604_2749_part38 :
    blockEstimate 12604 2749 7613 128 = 9602882344000 := by decide +kernel
private theorem moment_12604_2749_part39 :
    blockEstimate 12604 2749 7741 128 = 9782858536000 := by decide +kernel
private theorem moment_12604_2749_part40 :
    blockEstimate 12604 2749 7869 128 = 9951300392000 := by decide +kernel
private theorem moment_12604_2749_part41 :
    blockEstimate 12604 2749 7997 128 = 10108207912000 := by decide +kernel
private theorem moment_12604_2749_part42 :
    blockEstimate 12604 2749 8125 128 = 10253581096000 := by decide +kernel
private theorem moment_12604_2749_part43 :
    blockEstimate 12604 2749 8253 128 = 10387419944000 := by decide +kernel
private theorem moment_12604_2749_part44 :
    blockEstimate 12604 2749 8381 128 = 10509724456000 := by decide +kernel
private theorem moment_12604_2749_part45 :
    blockEstimate 12604 2749 8509 128 = 10620494632000 := by decide +kernel
private theorem moment_12604_2749_part46 :
    blockEstimate 12604 2749 8637 128 = 10719730472000 := by decide +kernel
private theorem moment_12604_2749_part47 :
    blockEstimate 12604 2749 8765 128 = 10807431976000 := by decide +kernel
private theorem moment_12604_2749_part48 :
    blockEstimate 12604 2749 8893 128 = 10883599144000 := by decide +kernel
private theorem moment_12604_2749_part49 :
    blockEstimate 12604 2749 9021 128 = 10948231976000 := by decide +kernel
private theorem moment_12604_2749_part50 :
    blockEstimate 12604 2749 9149 128 = 11001330472000 := by decide +kernel
private theorem moment_12604_2749_part51 :
    blockEstimate 12604 2749 9277 128 = 11042894632000 := by decide +kernel
private theorem moment_12604_2749_part52 :
    blockEstimate 12604 2749 9405 128 = 11072924456000 := by decide +kernel
private theorem moment_12604_2749_part53 :
    blockEstimate 12604 2749 9533 128 = 11091419944000 := by decide +kernel
private theorem moment_12604_2749_part54 :
    blockEstimate 12604 2749 9661 128 = 11098381096000 := by decide +kernel
private theorem moment_12604_2749_part55 :
    blockEstimate 12604 2749 9789 128 = 11093807912000 := by decide +kernel
private theorem moment_12604_2749_part56 :
    blockEstimate 12604 2749 9917 128 = 11077700392000 := by decide +kernel
private theorem moment_12604_2749_part57 :
    blockEstimate 12604 2749 10045 128 = 11050058536000 := by decide +kernel
private theorem moment_12604_2749_part58 :
    blockEstimate 12604 2749 10173 128 = 11010882344000 := by decide +kernel
private theorem moment_12604_2749_part59 :
    blockEstimate 12604 2749 10301 128 = 10960171816000 := by decide +kernel
private theorem moment_12604_2749_part60 :
    blockEstimate 12604 2749 10429 128 = 10897926952000 := by decide +kernel
private theorem moment_12604_2749_part61 :
    blockEstimate 12604 2749 10557 128 = 10824147752000 := by decide +kernel
private theorem moment_12604_2749_part62 :
    blockEstimate 12604 2749 10685 128 = 10738834216000 := by decide +kernel
private theorem moment_12604_2749_part63 :
    blockEstimate 12604 2749 10813 128 = 10641986344000 := by decide +kernel
private theorem moment_12604_2749_part64 :
    blockEstimate 12604 2749 10941 128 = 10533604136000 := by decide +kernel
private theorem moment_12604_2749_part65 :
    blockEstimate 12604 2749 11069 128 = 10413687592000 := by decide +kernel
private theorem moment_12604_2749_part66 :
    blockEstimate 12604 2749 11197 128 = 10282236712000 := by decide +kernel
private theorem moment_12604_2749_part67 :
    blockEstimate 12604 2749 11325 128 = 10139251496000 := by decide +kernel
private theorem moment_12604_2749_part68 :
    blockEstimate 12604 2749 11453 128 = 9984731944000 := by decide +kernel
private theorem moment_12604_2749_part69 :
    blockEstimate 12604 2749 11581 128 = 9818678056000 := by decide +kernel
private theorem moment_12604_2749_part70 :
    blockEstimate 12604 2749 11709 128 = 9641089832000 := by decide +kernel
private theorem moment_12604_2749_part71 :
    blockEstimate 12604 2749 11837 128 = 9451967272000 := by decide +kernel
private theorem moment_12604_2749_part72 :
    blockEstimate 12604 2749 11965 128 = 9251310376000 := by decide +kernel
private theorem moment_12604_2749_part73 :
    blockEstimate 12604 2749 12093 128 = 9039119144000 := by decide +kernel
private theorem moment_12604_2749_part74 :
    blockEstimate 12604 2749 12221 128 = 8815393576000 := by decide +kernel
private theorem moment_12604_2749_part75 :
    blockEstimate 12604 2749 12349 128 = 8580133672000 := by decide +kernel
private theorem moment_12604_2749_part76 :
    blockEstimate 12604 2749 12477 128 = 8333339432000 := by decide +kernel
private theorem moment_12604_2749_part77 :
    blockEstimate 12604 2749 12605 128 = 8076322923672 := by decide +kernel
private theorem moment_12604_2749_part78 :
    blockEstimate 12604 2749 12733 128 = 7814355005473 := by decide +kernel
private theorem moment_12604_2749_part79 :
    blockEstimate 12604 2749 12861 128 = 7549204580708 := by decide +kernel
private theorem moment_12604_2749_part80 :
    blockEstimate 12604 2749 12989 128 = 7281456774182 := by decide +kernel
private theorem moment_12604_2749_part81 :
    blockEstimate 12604 2749 13117 128 = 7011687342928 := by decide +kernel
private theorem moment_12604_2749_part82 :
    blockEstimate 12604 2749 13245 128 = 6740462672856 := by decide +kernel
private theorem moment_12604_2749_part83 :
    blockEstimate 12604 2749 13373 128 = 6468339781435 := by decide +kernel
private theorem moment_12604_2749_part84 :
    blockEstimate 12604 2749 13501 128 = 6195866311436 := by decide +kernel
private theorem moment_12604_2749_part85 :
    blockEstimate 12604 2749 13629 128 = 5923580538974 := by decide +kernel
private theorem moment_12604_2749_part86 :
    blockEstimate 12604 2749 13757 128 = 5652011365945 := by decide +kernel
private theorem moment_12604_2749_part87 :
    blockEstimate 12604 2749 13885 128 = 5381678324736 := by decide +kernel
private theorem moment_12604_2749_part88 :
    blockEstimate 12604 2749 14013 128 = 5113091578386 := by decide +kernel
private theorem moment_12604_2749_part89 :
    blockEstimate 12604 2749 14141 128 = 4846751916437 := by decide +kernel
private theorem moment_12604_2749_part90 :
    blockEstimate 12604 2749 14269 128 = 4583150758670 := by decide +kernel
private theorem moment_12604_2749_part91 :
    blockEstimate 12604 2749 14397 128 = 4322770153949 := by decide +kernel
private theorem moment_12604_2749_part92 :
    blockEstimate 12604 2749 14525 128 = 4066082782556 := by decide +kernel
private theorem moment_12604_2749_part93 :
    blockEstimate 12604 2749 14653 128 = 3813551949784 := by decide +kernel
private theorem moment_12604_2749_part94 :
    blockEstimate 12604 2749 14781 128 = 3565631593032 := by decide +kernel
private theorem moment_12604_2749_part95 :
    blockEstimate 12604 2749 14909 128 = 3322766277002 := by decide +kernel
private theorem moment_12604_2749_part96 :
    blockEstimate 12604 2749 15037 128 = 3085391198094 := by decide +kernel
private theorem moment_12604_2749_part97 :
    blockEstimate 12604 2749 15165 128 = 2853932179582 := by decide +kernel
private theorem moment_12604_2749_part98 :
    blockEstimate 12604 2749 15293 128 = 2628277578258 := by decide +kernel
private theorem moment_12604_2749_part99 :
    blockEstimate 12604 2749 15421 128 = 2406996045104 := by decide +kernel
private theorem moment_12604_2749_part100 :
    blockEstimate 12604 2749 15549 128 = 2193346701616 := by decide +kernel
private theorem moment_12604_2749_part101 :
    blockEstimate 12604 2749 15677 128 = 1988018529584 := by decide +kernel
private theorem moment_12604_2749_part102 :
    blockEstimate 12604 2749 15805 128 = 1791263187248 := by decide +kernel
private theorem moment_12604_2749_part103 :
    blockEstimate 12604 2749 15933 128 = 1603332332848 := by decide +kernel
private theorem moment_12604_2749_part104 :
    blockEstimate 12604 2749 16061 128 = 1424477624624 := by decide +kernel
private theorem moment_12604_2749_part105 :
    blockEstimate 12604 2749 16189 128 = 1254950720816 := by decide +kernel
private theorem moment_12604_2749_part106 :
    blockEstimate 12604 2749 16317 128 = 1095003279664 := by decide +kernel
private theorem moment_12604_2749_part107 :
    blockEstimate 12604 2749 16445 128 = 944886959408 := by decide +kernel
private theorem moment_12604_2749_part108 :
    blockEstimate 12604 2749 16573 128 = 804853418288 := by decide +kernel
private theorem moment_12604_2749_part109 :
    blockEstimate 12604 2749 16701 128 = 675154314544 := by decide +kernel
private theorem moment_12604_2749_part110 :
    blockEstimate 12604 2749 16829 128 = 556041306416 := by decide +kernel
private theorem moment_12604_2749_part111 :
    blockEstimate 12604 2749 16957 128 = 447766052144 := by decide +kernel
private theorem moment_12604_2749_part112 :
    blockEstimate 12604 2749 17085 128 = 350580209968 := by decide +kernel
private theorem moment_12604_2749_part113 :
    blockEstimate 12604 2749 17213 128 = 264735438128 := by decide +kernel
private theorem moment_12604_2749_part114 :
    blockEstimate 12604 2749 17341 128 = 190483394864 := by decide +kernel
private theorem moment_12604_2749_part115 :
    blockEstimate 12604 2749 17469 128 = 128075738416 := by decide +kernel
private theorem moment_12604_2749_part116 :
    blockEstimate 12604 2749 17597 128 = 77764127024 := by decide +kernel
private theorem moment_12604_2749_part117 :
    blockEstimate 12604 2749 17725 128 = 39800218928 := by decide +kernel
private theorem moment_12604_2749_part118 :
    blockEstimate 12604 2749 17853 128 = 14435672368 := by decide +kernel
private theorem moment_12604_2749_part119 :
    blockEstimate 12604 2749 17981 121 = 1921981679 := by decide +kernel
private theorem moment_12604_2749_join0 :
    blockEstimate 12604 2749 2877 256 = 112669971520 :=
  block_append moment_12604_2749_part1 moment_12604_2749_part2 rfl rfl rfl
private theorem moment_12604_2749_join1 :
    blockEstimate 12604 2749 2749 384 = 117145101920 :=
  block_append moment_12604_2749_part0 moment_12604_2749_join0 rfl rfl rfl
private theorem moment_12604_2749_join2 :
    blockEstimate 12604 2749 3133 256 = 415079044160 :=
  block_append moment_12604_2749_part3 moment_12604_2749_part4 rfl rfl rfl
private theorem moment_12604_2749_join3 :
    blockEstimate 12604 2749 3389 256 = 903153177664 :=
  block_append moment_12604_2749_part5 moment_12604_2749_part6 rfl rfl rfl
private theorem moment_12604_2749_join4 :
    blockEstimate 12604 2749 3133 512 = 1318232221824 :=
  block_append moment_12604_2749_join2 moment_12604_2749_join3 rfl rfl rfl
private theorem moment_12604_2749_join5 :
    blockEstimate 12604 2749 2749 896 = 1435377323744 :=
  block_append moment_12604_2749_join1 moment_12604_2749_join4 rfl rfl rfl
private theorem moment_12604_2749_join6 :
    blockEstimate 12604 2749 3645 256 = 1564007470144 :=
  block_append moment_12604_2749_part7 moment_12604_2749_part8 rfl rfl rfl
private theorem moment_12604_2749_join7 :
    blockEstimate 12604 2749 3901 256 = 2384757019712 :=
  block_append moment_12604_2749_part9 moment_12604_2749_part10 rfl rfl rfl
private theorem moment_12604_2749_join8 :
    blockEstimate 12604 2749 3645 512 = 3948764489856 :=
  block_append moment_12604_2749_join6 moment_12604_2749_join7 rfl rfl rfl
private theorem moment_12604_2749_join9 :
    blockEstimate 12604 2749 4157 256 = 3352516924480 :=
  block_append moment_12604_2749_part11 moment_12604_2749_part12 rfl rfl rfl
private theorem moment_12604_2749_join10 :
    blockEstimate 12604 2749 4413 256 = 4454402282560 :=
  block_append moment_12604_2749_part13 moment_12604_2749_part14 rfl rfl rfl
private theorem moment_12604_2749_join11 :
    blockEstimate 12604 2749 4157 512 = 7806919207040 :=
  block_append moment_12604_2749_join9 moment_12604_2749_join10 rfl rfl rfl
private theorem moment_12604_2749_join12 :
    blockEstimate 12604 2749 3645 1024 = 11755683696896 :=
  block_append moment_12604_2749_join8 moment_12604_2749_join11 rfl rfl rfl
private theorem moment_12604_2749_join13 :
    blockEstimate 12604 2749 2749 1920 = 13191061020640 :=
  block_append moment_12604_2749_join5 moment_12604_2749_join12 rfl rfl rfl
private theorem moment_12604_2749_join14 :
    blockEstimate 12604 2749 4797 256 = 6330529821760 :=
  block_append moment_12604_2749_part16 moment_12604_2749_part17 rfl rfl rfl
private theorem moment_12604_2749_join15 :
    blockEstimate 12604 2749 4669 384 = 9009328961120 :=
  block_append moment_12604_2749_part15 moment_12604_2749_join14 rfl rfl rfl
private theorem moment_12604_2749_join16 :
    blockEstimate 12604 2749 5053 256 = 7711357367360 :=
  block_append moment_12604_2749_part18 moment_12604_2749_part19 rfl rfl rfl
private theorem moment_12604_2749_join17 :
    blockEstimate 12604 2749 5309 256 = 9180721809755 :=
  block_append moment_12604_2749_part20 moment_12604_2749_part21 rfl rfl rfl
private theorem moment_12604_2749_join18 :
    blockEstimate 12604 2749 5053 512 = 16892079177115 :=
  block_append moment_12604_2749_join16 moment_12604_2749_join17 rfl rfl rfl
private theorem moment_12604_2749_join19 :
    blockEstimate 12604 2749 4669 896 = 25901408138235 :=
  block_append moment_12604_2749_join15 moment_12604_2749_join18 rfl rfl rfl
private theorem moment_12604_2749_join20 :
    blockEstimate 12604 2749 5565 256 = 10673712720000 :=
  block_append moment_12604_2749_part22 moment_12604_2749_part23 rfl rfl rfl
private theorem moment_12604_2749_join21 :
    blockEstimate 12604 2749 5821 256 = 12085677648000 :=
  block_append moment_12604_2749_part24 moment_12604_2749_part25 rfl rfl rfl
private theorem moment_12604_2749_join22 :
    blockEstimate 12604 2749 5565 512 = 22759390368000 :=
  block_append moment_12604_2749_join20 moment_12604_2749_join21 rfl rfl rfl
private theorem moment_12604_2749_join23 :
    blockEstimate 12604 2749 6077 256 = 13405367888000 :=
  block_append moment_12604_2749_part26 moment_12604_2749_part27 rfl rfl rfl
private theorem moment_12604_2749_join24 :
    blockEstimate 12604 2749 6333 256 = 14632783440000 :=
  block_append moment_12604_2749_part28 moment_12604_2749_part29 rfl rfl rfl
private theorem moment_12604_2749_join25 :
    blockEstimate 12604 2749 6077 512 = 28038151328000 :=
  block_append moment_12604_2749_join23 moment_12604_2749_join24 rfl rfl rfl
private theorem moment_12604_2749_join26 :
    blockEstimate 12604 2749 5565 1024 = 50797541696000 :=
  block_append moment_12604_2749_join22 moment_12604_2749_join25 rfl rfl rfl
private theorem moment_12604_2749_join27 :
    blockEstimate 12604 2749 4669 1920 = 76698949834235 :=
  block_append moment_12604_2749_join19 moment_12604_2749_join26 rfl rfl rfl
private theorem moment_12604_2749_join28 :
    blockEstimate 12604 2749 2749 3840 = 89890010854875 :=
  block_append moment_12604_2749_join13 moment_12604_2749_join27 rfl rfl rfl
private theorem moment_12604_2749_join29 :
    blockEstimate 12604 2749 6717 256 = 16300891728000 :=
  block_append moment_12604_2749_part31 moment_12604_2749_part32 rfl rfl rfl
private theorem moment_12604_2749_join30 :
    blockEstimate 12604 2749 6589 384 = 24048728440000 :=
  block_append moment_12604_2749_part30 moment_12604_2749_join29 rfl rfl rfl
private theorem moment_12604_2749_join31 :
    blockEstimate 12604 2749 6973 256 = 17297620560000 :=
  block_append moment_12604_2749_part33 moment_12604_2749_part34 rfl rfl rfl
private theorem moment_12604_2749_join32 :
    blockEstimate 12604 2749 7229 256 = 18202074704000 :=
  block_append moment_12604_2749_part35 moment_12604_2749_part36 rfl rfl rfl
private theorem moment_12604_2749_join33 :
    blockEstimate 12604 2749 6973 512 = 35499695264000 :=
  block_append moment_12604_2749_join31 moment_12604_2749_join32 rfl rfl rfl
private theorem moment_12604_2749_join34 :
    blockEstimate 12604 2749 6589 896 = 59548423704000 :=
  block_append moment_12604_2749_join30 moment_12604_2749_join33 rfl rfl rfl
private theorem moment_12604_2749_join35 :
    blockEstimate 12604 2749 7485 256 = 19014254160000 :=
  block_append moment_12604_2749_part37 moment_12604_2749_part38 rfl rfl rfl
private theorem moment_12604_2749_join36 :
    blockEstimate 12604 2749 7741 256 = 19734158928000 :=
  block_append moment_12604_2749_part39 moment_12604_2749_part40 rfl rfl rfl
private theorem moment_12604_2749_join37 :
    blockEstimate 12604 2749 7485 512 = 38748413088000 :=
  block_append moment_12604_2749_join35 moment_12604_2749_join36 rfl rfl rfl
private theorem moment_12604_2749_join38 :
    blockEstimate 12604 2749 7997 256 = 20361789008000 :=
  block_append moment_12604_2749_part41 moment_12604_2749_part42 rfl rfl rfl
private theorem moment_12604_2749_join39 :
    blockEstimate 12604 2749 8253 256 = 20897144400000 :=
  block_append moment_12604_2749_part43 moment_12604_2749_part44 rfl rfl rfl
private theorem moment_12604_2749_join40 :
    blockEstimate 12604 2749 7997 512 = 41258933408000 :=
  block_append moment_12604_2749_join38 moment_12604_2749_join39 rfl rfl rfl
private theorem moment_12604_2749_join41 :
    blockEstimate 12604 2749 7485 1024 = 80007346496000 :=
  block_append moment_12604_2749_join37 moment_12604_2749_join40 rfl rfl rfl
private theorem moment_12604_2749_join42 :
    blockEstimate 12604 2749 6589 1920 = 139555770200000 :=
  block_append moment_12604_2749_join34 moment_12604_2749_join41 rfl rfl rfl
private theorem moment_12604_2749_join43 :
    blockEstimate 12604 2749 8637 256 = 21527162448000 :=
  block_append moment_12604_2749_part46 moment_12604_2749_part47 rfl rfl rfl
private theorem moment_12604_2749_join44 :
    blockEstimate 12604 2749 8509 384 = 32147657080000 :=
  block_append moment_12604_2749_part45 moment_12604_2749_join43 rfl rfl rfl
private theorem moment_12604_2749_join45 :
    blockEstimate 12604 2749 8893 256 = 21831831120000 :=
  block_append moment_12604_2749_part48 moment_12604_2749_part49 rfl rfl rfl
private theorem moment_12604_2749_join46 :
    blockEstimate 12604 2749 9149 256 = 22044225104000 :=
  block_append moment_12604_2749_part50 moment_12604_2749_part51 rfl rfl rfl
private theorem moment_12604_2749_join47 :
    blockEstimate 12604 2749 8893 512 = 43876056224000 :=
  block_append moment_12604_2749_join45 moment_12604_2749_join46 rfl rfl rfl
private theorem moment_12604_2749_join48 :
    blockEstimate 12604 2749 8509 896 = 76023713304000 :=
  block_append moment_12604_2749_join44 moment_12604_2749_join47 rfl rfl rfl
private theorem moment_12604_2749_join49 :
    blockEstimate 12604 2749 9405 256 = 22164344400000 :=
  block_append moment_12604_2749_part52 moment_12604_2749_part53 rfl rfl rfl
private theorem moment_12604_2749_join50 :
    blockEstimate 12604 2749 9661 256 = 22192189008000 :=
  block_append moment_12604_2749_part54 moment_12604_2749_part55 rfl rfl rfl
private theorem moment_12604_2749_join51 :
    blockEstimate 12604 2749 9405 512 = 44356533408000 :=
  block_append moment_12604_2749_join49 moment_12604_2749_join50 rfl rfl rfl
private theorem moment_12604_2749_join52 :
    blockEstimate 12604 2749 9917 256 = 22127758928000 :=
  block_append moment_12604_2749_part56 moment_12604_2749_part57 rfl rfl rfl
private theorem moment_12604_2749_join53 :
    blockEstimate 12604 2749 10173 256 = 21971054160000 :=
  block_append moment_12604_2749_part58 moment_12604_2749_part59 rfl rfl rfl
private theorem moment_12604_2749_join54 :
    blockEstimate 12604 2749 9917 512 = 44098813088000 :=
  block_append moment_12604_2749_join52 moment_12604_2749_join53 rfl rfl rfl
private theorem moment_12604_2749_join55 :
    blockEstimate 12604 2749 9405 1024 = 88455346496000 :=
  block_append moment_12604_2749_join51 moment_12604_2749_join54 rfl rfl rfl
private theorem moment_12604_2749_join56 :
    blockEstimate 12604 2749 8509 1920 = 164479059800000 :=
  block_append moment_12604_2749_join48 moment_12604_2749_join55 rfl rfl rfl
private theorem moment_12604_2749_join57 :
    blockEstimate 12604 2749 6589 3840 = 304034830000000 :=
  block_append moment_12604_2749_join42 moment_12604_2749_join56 rfl rfl rfl
private theorem moment_12604_2749_join58 :
    blockEstimate 12604 2749 2749 7680 = 393924840854875 :=
  block_append moment_12604_2749_join28 moment_12604_2749_join57 rfl rfl rfl
private theorem moment_12604_2749_join59 :
    blockEstimate 12604 2749 10557 256 = 21562981968000 :=
  block_append moment_12604_2749_part61 moment_12604_2749_part62 rfl rfl rfl
private theorem moment_12604_2749_join60 :
    blockEstimate 12604 2749 10429 384 = 32460908920000 :=
  block_append moment_12604_2749_part60 moment_12604_2749_join59 rfl rfl rfl
private theorem moment_12604_2749_join61 :
    blockEstimate 12604 2749 10813 256 = 21175590480000 :=
  block_append moment_12604_2749_part63 moment_12604_2749_part64 rfl rfl rfl
private theorem moment_12604_2749_join62 :
    blockEstimate 12604 2749 11069 256 = 20695924304000 :=
  block_append moment_12604_2749_part65 moment_12604_2749_part66 rfl rfl rfl
private theorem moment_12604_2749_join63 :
    blockEstimate 12604 2749 10813 512 = 41871514784000 :=
  block_append moment_12604_2749_join61 moment_12604_2749_join62 rfl rfl rfl
private theorem moment_12604_2749_join64 :
    blockEstimate 12604 2749 10429 896 = 74332423704000 :=
  block_append moment_12604_2749_join60 moment_12604_2749_join63 rfl rfl rfl
private theorem moment_12604_2749_join65 :
    blockEstimate 12604 2749 11325 256 = 20123983440000 :=
  block_append moment_12604_2749_part67 moment_12604_2749_part68 rfl rfl rfl
private theorem moment_12604_2749_join66 :
    blockEstimate 12604 2749 11581 256 = 19459767888000 :=
  block_append moment_12604_2749_part69 moment_12604_2749_part70 rfl rfl rfl
private theorem moment_12604_2749_join67 :
    blockEstimate 12604 2749 11325 512 = 39583751328000 :=
  block_append moment_12604_2749_join65 moment_12604_2749_join66 rfl rfl rfl
private theorem moment_12604_2749_join68 :
    blockEstimate 12604 2749 11837 256 = 18703277648000 :=
  block_append moment_12604_2749_part71 moment_12604_2749_part72 rfl rfl rfl
private theorem moment_12604_2749_join69 :
    blockEstimate 12604 2749 12093 256 = 17854512720000 :=
  block_append moment_12604_2749_part73 moment_12604_2749_part74 rfl rfl rfl
private theorem moment_12604_2749_join70 :
    blockEstimate 12604 2749 11837 512 = 36557790368000 :=
  block_append moment_12604_2749_join68 moment_12604_2749_join69 rfl rfl rfl
private theorem moment_12604_2749_join71 :
    blockEstimate 12604 2749 11325 1024 = 76141541696000 :=
  block_append moment_12604_2749_join67 moment_12604_2749_join70 rfl rfl rfl
private theorem moment_12604_2749_join72 :
    blockEstimate 12604 2749 10429 1920 = 150473965400000 :=
  block_append moment_12604_2749_join64 moment_12604_2749_join71 rfl rfl rfl
private theorem moment_12604_2749_join73 :
    blockEstimate 12604 2749 12477 256 = 16409662355672 :=
  block_append moment_12604_2749_part76 moment_12604_2749_part77 rfl rfl rfl
private theorem moment_12604_2749_join74 :
    blockEstimate 12604 2749 12349 384 = 24989796027672 :=
  block_append moment_12604_2749_part75 moment_12604_2749_join73 rfl rfl rfl
private theorem moment_12604_2749_join75 :
    blockEstimate 12604 2749 12733 256 = 15363559586181 :=
  block_append moment_12604_2749_part78 moment_12604_2749_part79 rfl rfl rfl
private theorem moment_12604_2749_join76 :
    blockEstimate 12604 2749 12989 256 = 14293144117110 :=
  block_append moment_12604_2749_part80 moment_12604_2749_part81 rfl rfl rfl
private theorem moment_12604_2749_join77 :
    blockEstimate 12604 2749 12733 512 = 29656703703291 :=
  block_append moment_12604_2749_join75 moment_12604_2749_join76 rfl rfl rfl
private theorem moment_12604_2749_join78 :
    blockEstimate 12604 2749 12349 896 = 54646499730963 :=
  block_append moment_12604_2749_join74 moment_12604_2749_join77 rfl rfl rfl
private theorem moment_12604_2749_join79 :
    blockEstimate 12604 2749 13245 256 = 13208802454291 :=
  block_append moment_12604_2749_part82 moment_12604_2749_part83 rfl rfl rfl
private theorem moment_12604_2749_join80 :
    blockEstimate 12604 2749 13501 256 = 12119446850410 :=
  block_append moment_12604_2749_part84 moment_12604_2749_part85 rfl rfl rfl
private theorem moment_12604_2749_join81 :
    blockEstimate 12604 2749 13245 512 = 25328249304701 :=
  block_append moment_12604_2749_join79 moment_12604_2749_join80 rfl rfl rfl
private theorem moment_12604_2749_join82 :
    blockEstimate 12604 2749 13757 256 = 11033689690681 :=
  block_append moment_12604_2749_part86 moment_12604_2749_part87 rfl rfl rfl
private theorem moment_12604_2749_join83 :
    blockEstimate 12604 2749 14013 256 = 9959843494823 :=
  block_append moment_12604_2749_part88 moment_12604_2749_part89 rfl rfl rfl
private theorem moment_12604_2749_join84 :
    blockEstimate 12604 2749 13757 512 = 20993533185504 :=
  block_append moment_12604_2749_join82 moment_12604_2749_join83 rfl rfl rfl
private theorem moment_12604_2749_join85 :
    blockEstimate 12604 2749 13245 1024 = 46321782490205 :=
  block_append moment_12604_2749_join81 moment_12604_2749_join84 rfl rfl rfl
private theorem moment_12604_2749_join86 :
    blockEstimate 12604 2749 12349 1920 = 100968282221168 :=
  block_append moment_12604_2749_join78 moment_12604_2749_join85 rfl rfl rfl
private theorem moment_12604_2749_join87 :
    blockEstimate 12604 2749 10429 3840 = 251442247621168 :=
  block_append moment_12604_2749_join72 moment_12604_2749_join86 rfl rfl rfl
private theorem moment_12604_2749_join88 :
    blockEstimate 12604 2749 14397 256 = 8388852936505 :=
  block_append moment_12604_2749_part91 moment_12604_2749_part92 rfl rfl rfl
private theorem moment_12604_2749_join89 :
    blockEstimate 12604 2749 14269 384 = 12972003695175 :=
  block_append moment_12604_2749_part90 moment_12604_2749_join88 rfl rfl rfl
private theorem moment_12604_2749_join90 :
    blockEstimate 12604 2749 14653 256 = 7379183542816 :=
  block_append moment_12604_2749_part93 moment_12604_2749_part94 rfl rfl rfl
private theorem moment_12604_2749_join91 :
    blockEstimate 12604 2749 14909 256 = 6408157475096 :=
  block_append moment_12604_2749_part95 moment_12604_2749_part96 rfl rfl rfl
private theorem moment_12604_2749_join92 :
    blockEstimate 12604 2749 14653 512 = 13787341017912 :=
  block_append moment_12604_2749_join90 moment_12604_2749_join91 rfl rfl rfl
private theorem moment_12604_2749_join93 :
    blockEstimate 12604 2749 14269 896 = 26759344713087 :=
  block_append moment_12604_2749_join89 moment_12604_2749_join92 rfl rfl rfl
private theorem moment_12604_2749_join94 :
    blockEstimate 12604 2749 15165 256 = 5482209757840 :=
  block_append moment_12604_2749_part97 moment_12604_2749_part98 rfl rfl rfl
private theorem moment_12604_2749_join95 :
    blockEstimate 12604 2749 15421 256 = 4600342746720 :=
  block_append moment_12604_2749_part99 moment_12604_2749_part100 rfl rfl rfl
private theorem moment_12604_2749_join96 :
    blockEstimate 12604 2749 15165 512 = 10082552504560 :=
  block_append moment_12604_2749_join94 moment_12604_2749_join95 rfl rfl rfl
private theorem moment_12604_2749_join97 :
    blockEstimate 12604 2749 15677 256 = 3779281716832 :=
  block_append moment_12604_2749_part101 moment_12604_2749_part102 rfl rfl rfl
private theorem moment_12604_2749_join98 :
    blockEstimate 12604 2749 15933 256 = 3027809957472 :=
  block_append moment_12604_2749_part103 moment_12604_2749_part104 rfl rfl rfl
private theorem moment_12604_2749_join99 :
    blockEstimate 12604 2749 15677 512 = 6807091674304 :=
  block_append moment_12604_2749_join97 moment_12604_2749_join98 rfl rfl rfl
private theorem moment_12604_2749_join100 :
    blockEstimate 12604 2749 15165 1024 = 16889644178864 :=
  block_append moment_12604_2749_join96 moment_12604_2749_join99 rfl rfl rfl
private theorem moment_12604_2749_join101 :
    blockEstimate 12604 2749 14269 1920 = 43648988891951 :=
  block_append moment_12604_2749_join93 moment_12604_2749_join100 rfl rfl rfl
private theorem moment_12604_2749_join102 :
    blockEstimate 12604 2749 16317 256 = 2039890239072 :=
  block_append moment_12604_2749_part106 moment_12604_2749_part107 rfl rfl rfl
private theorem moment_12604_2749_join103 :
    blockEstimate 12604 2749 16189 384 = 3294840959888 :=
  block_append moment_12604_2749_part105 moment_12604_2749_join102 rfl rfl rfl
private theorem moment_12604_2749_join104 :
    blockEstimate 12604 2749 16573 256 = 1480007732832 :=
  block_append moment_12604_2749_part108 moment_12604_2749_part109 rfl rfl rfl
private theorem moment_12604_2749_join105 :
    blockEstimate 12604 2749 16829 256 = 1003807358560 :=
  block_append moment_12604_2749_part110 moment_12604_2749_part111 rfl rfl rfl
private theorem moment_12604_2749_join106 :
    blockEstimate 12604 2749 16573 512 = 2483815091392 :=
  block_append moment_12604_2749_join104 moment_12604_2749_join105 rfl rfl rfl
private theorem moment_12604_2749_join107 :
    blockEstimate 12604 2749 16189 896 = 5778656051280 :=
  block_append moment_12604_2749_join103 moment_12604_2749_join106 rfl rfl rfl
private theorem moment_12604_2749_join108 :
    blockEstimate 12604 2749 17085 256 = 615315648096 :=
  block_append moment_12604_2749_part112 moment_12604_2749_part113 rfl rfl rfl
private theorem moment_12604_2749_join109 :
    blockEstimate 12604 2749 17341 256 = 318559133280 :=
  block_append moment_12604_2749_part114 moment_12604_2749_part115 rfl rfl rfl
private theorem moment_12604_2749_join110 :
    blockEstimate 12604 2749 17085 512 = 933874781376 :=
  block_append moment_12604_2749_join108 moment_12604_2749_join109 rfl rfl rfl
private theorem moment_12604_2749_join111 :
    blockEstimate 12604 2749 17597 256 = 117564345952 :=
  block_append moment_12604_2749_part116 moment_12604_2749_part117 rfl rfl rfl
private theorem moment_12604_2749_join112 :
    blockEstimate 12604 2749 17853 249 = 16357654047 :=
  block_append moment_12604_2749_part118 moment_12604_2749_part119 rfl rfl rfl
private theorem moment_12604_2749_join113 :
    blockEstimate 12604 2749 17597 505 = 133921999999 :=
  block_append moment_12604_2749_join111 moment_12604_2749_join112 rfl rfl rfl
private theorem moment_12604_2749_join114 :
    blockEstimate 12604 2749 17085 1017 = 1067796781375 :=
  block_append moment_12604_2749_join110 moment_12604_2749_join113 rfl rfl rfl
private theorem moment_12604_2749_join115 :
    blockEstimate 12604 2749 16189 1913 = 6846452832655 :=
  block_append moment_12604_2749_join107 moment_12604_2749_join114 rfl rfl rfl
private theorem moment_12604_2749_join116 :
    blockEstimate 12604 2749 14269 3833 = 50495441724606 :=
  block_append moment_12604_2749_join101 moment_12604_2749_join115 rfl rfl rfl
private theorem moment_12604_2749_join117 :
    blockEstimate 12604 2749 10429 7673 = 301937689345774 :=
  block_append moment_12604_2749_join87 moment_12604_2749_join116 rfl rfl rfl
private theorem moment_12604_2749_join118 :
    blockEstimate 12604 2749 2749 15353 = 695862530200649 :=
  block_append moment_12604_2749_join58 moment_12604_2749_join117 rfl rfl rfl

theorem moment_12604_2749 : momentEstimate 12604 2749 = 695862530200649 := moment_12604_2749_join118

private theorem largest_checked_2359_0_part0 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 0 128 = 103167551928182495703010935520 := by decide +kernel
private theorem largest_checked_2359_0_part1 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 128 128 = 96892405627359115651330200288 := by decide +kernel
private theorem largest_checked_2359_0_part2 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 256 128 = 90742317591220127522680414944 := by decide +kernel
private theorem largest_checked_2359_0_part3 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 384 128 = 84719063154705543077676741344 := by decide +kernel
private theorem largest_checked_2359_0_part4 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 512 128 = 78824409978315206517389116128 := by decide +kernel
private theorem largest_checked_2359_0_part5 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 640 128 = 73060118057563143126867186400 := by decide +kernel
private theorem largest_checked_2359_0_part6 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 768 128 = 67427939732431907918665245408 := by decide +kernel
private theorem largest_checked_2359_0_part7 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 896 128 = 61929619696826934276367168224 := by decide +kernel
private theorem largest_checked_2359_0_part8 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 1024 128 = 56566895008030882598111347424 := by decide +kernel
private theorem largest_checked_2359_0_part9 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 1152 128 = 51341495096157988940115628768 := by decide +kernel
private theorem largest_checked_2359_0_part10 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 1280 128 = 46255141773608413660202246880 := by decide +kernel
private theorem largest_checked_2359_0_part11 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 1408 128 = 41309549244522590061322760928 := by decide +kernel
private theorem largest_checked_2359_0_part12 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 1536 128 = 36506424114235573035082990304 := by decide +kernel
private theorem largest_checked_2359_0_part13 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 1664 128 = 31847465398731387705267950304 := by decide +kernel
private theorem largest_checked_2359_0_part14 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 1792 128 = 27334364534097378071366787808 := by decide +kernel
private theorem largest_checked_2359_0_part15 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 1920 128 = 22968805385978555652097716960 := by decide +kernel
private theorem largest_checked_2359_0_part16 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 2048 128 = 18752464259031948128932954848 := by decide +kernel
private theorem largest_checked_2359_0_part17 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 2176 128 = 14687009906380947989623657184 := by decide +kernel
private theorem largest_checked_2359_0_part18 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 2304 128 = 10774103539069661171724853984 := by decide +kernel
private theorem largest_checked_2359_0_part19 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 2432 128 = 7015398835517255706120385248 := by decide +kernel
private theorem largest_checked_2359_0_part20 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 2560 128 = 3412541950972310360547836640 := by decide +kernel
private theorem largest_checked_2359_0_part21 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 2688 62 = 404555887926766847014698864 := by decide +kernel
private theorem largest_checked_2359_0_join0 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 0 256 = 200059957555541611354341135808 :=
  phaseBlock_append largest_checked_2359_0_part0 largest_checked_2359_0_part1 rfl rfl rfl
private theorem largest_checked_2359_0_join1 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 384 256 = 163543473133020749595065857472 :=
  phaseBlock_append largest_checked_2359_0_part3 largest_checked_2359_0_part4 rfl rfl rfl
private theorem largest_checked_2359_0_join2 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 256 384 = 254285790724240877117746272416 :=
  phaseBlock_append largest_checked_2359_0_part2 largest_checked_2359_0_join1 rfl rfl rfl
private theorem largest_checked_2359_0_join3 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 0 640 = 454345748279782488472087408224 :=
  phaseBlock_append largest_checked_2359_0_join0 largest_checked_2359_0_join2 rfl rfl rfl
private theorem largest_checked_2359_0_join4 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 768 256 = 129357559429258842195032413632 :=
  phaseBlock_append largest_checked_2359_0_part6 largest_checked_2359_0_part7 rfl rfl rfl
private theorem largest_checked_2359_0_join5 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 640 384 = 202417677486821985321899600032 :=
  phaseBlock_append largest_checked_2359_0_part5 largest_checked_2359_0_join4 rfl rfl rfl
private theorem largest_checked_2359_0_join6 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 1152 256 = 97596636869766402600317875648 :=
  phaseBlock_append largest_checked_2359_0_part9 largest_checked_2359_0_part10 rfl rfl rfl
private theorem largest_checked_2359_0_join7 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 1024 384 = 154163531877797285198429223072 :=
  phaseBlock_append largest_checked_2359_0_part8 largest_checked_2359_0_join6 rfl rfl rfl
private theorem largest_checked_2359_0_join8 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 640 768 = 356581209364619270520328823104 :=
  phaseBlock_append largest_checked_2359_0_join5 largest_checked_2359_0_join7 rfl rfl rfl
private theorem largest_checked_2359_0_join9 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 0 1408 = 810926957644401758992416231328 :=
  phaseBlock_append largest_checked_2359_0_join3 largest_checked_2359_0_join8 rfl rfl rfl
private theorem largest_checked_2359_0_join10 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 1408 256 = 77815973358758163096405751232 :=
  phaseBlock_append largest_checked_2359_0_part11 largest_checked_2359_0_part12 rfl rfl rfl
private theorem largest_checked_2359_0_join11 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 1792 256 = 50303169920075933723464504768 :=
  phaseBlock_append largest_checked_2359_0_part14 largest_checked_2359_0_part15 rfl rfl rfl
private theorem largest_checked_2359_0_join12 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 1664 384 = 82150635318807321428732455072 :=
  phaseBlock_append largest_checked_2359_0_part13 largest_checked_2359_0_join11 rfl rfl rfl
private theorem largest_checked_2359_0_join13 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 1408 640 = 159966608677565484525138206304 :=
  phaseBlock_append largest_checked_2359_0_join10 largest_checked_2359_0_join12 rfl rfl rfl
private theorem largest_checked_2359_0_join14 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 2176 256 = 25461113445450609161348511168 :=
  phaseBlock_append largest_checked_2359_0_part17 largest_checked_2359_0_part18 rfl rfl rfl
private theorem largest_checked_2359_0_join15 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 2048 384 = 44213577704482557290281466016 :=
  phaseBlock_append largest_checked_2359_0_part16 largest_checked_2359_0_join14 rfl rfl rfl
private theorem largest_checked_2359_0_join16 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 2560 190 = 3817097838899077207562535504 :=
  phaseBlock_append largest_checked_2359_0_part20 largest_checked_2359_0_part21 rfl rfl rfl
private theorem largest_checked_2359_0_join17 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 2432 318 = 10832496674416332913682920752 :=
  phaseBlock_append largest_checked_2359_0_part19 largest_checked_2359_0_join16 rfl rfl rfl
private theorem largest_checked_2359_0_join18 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 2048 702 = 55046074378898890203964386768 :=
  phaseBlock_append largest_checked_2359_0_join15 largest_checked_2359_0_join17 rfl rfl rfl
private theorem largest_checked_2359_0_join19 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 1408 1342 = 215012683056464374729102593072 :=
  phaseBlock_append largest_checked_2359_0_join13 largest_checked_2359_0_join18 rfl rfl rfl
private theorem largest_checked_2359_0_join20 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 0) 0 2750 = 1025939640700866133721518824400 :=
  phaseBlock_append largest_checked_2359_0_join9 largest_checked_2359_0_join19 rfl rfl rfl

private theorem largest_checked_2359_0 : fastPhase largestBank.shape 179818 2359 103 1 1 1 0 = 1025939640700866133721518824400 :=
  phase_of_block (n := 2750) (by decide +kernel) largest_checked_2359_0_join20

private theorem largest_checked_2359_1_part0 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 0 128 = 103118708015766234236559727072 := by decide +kernel
private theorem largest_checked_2359_1_part1 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 128 128 = 96844488903377610339670026720 := by decide +kernel
private theorem largest_checked_2359_1_part2 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 256 128 = 90695343119738550672438147552 := by decide +kernel
private theorem largest_checked_2359_1_part3 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 384 128 = 84673045936659092351328881120 := by decide +kernel
private theorem largest_checked_2359_1_part4 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 512 128 = 78779364951585884998460496352 := by decide +kernel
private theorem largest_checked_2359_1_part5 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 640 128 = 73016060097056539385129675232 := by decide +kernel
private theorem largest_checked_2359_1_part6 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 768 128 = 67384883650153976075336448480 := by decide +kernel
private theorem largest_checked_2359_1_part7 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 896 128 = 61887580241960774069309131232 := by decide +kernel
private theorem largest_checked_2359_1_part8 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 1024 128 = 56525886867013519447029258720 := by decide +kernel
private theorem largest_checked_2359_1_part9 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 1152 128 = 51301532892757154011756521952 := by decide +kernel
private theorem largest_checked_2359_1_part10 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 1280 128 = 46216240068999323933553703392 := by decide +kernel
private theorem largest_checked_2359_1_part11 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 1408 128 = 41271722537364728392811612640 := by decide +kernel
private theorem largest_checked_2359_1_part12 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 1536 128 = 36469686840749468223774022112 := by decide +kernel
private theorem largest_checked_2359_1_part13 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 1664 128 = 31811831932775394558062602720 := by decide +kernel
private theorem largest_checked_2359_1_part14 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 1792 128 = 27299849187244457468201859552 := by decide +kernel
private theorem largest_checked_2359_1_part15 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 1920 128 = 22935422407593054611144067552 := by decide +kernel
private theorem largest_checked_2359_1_part16 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 2048 128 = 18720227836346379871794207200 := by decide +kernel
private theorem largest_checked_2359_1_part17 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 2176 128 = 14655934164572772006534900192 := by decide +kernel
private theorem largest_checked_2359_1_part18 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 2304 128 = 10744202541338063286751345120 := by decide +kernel
private theorem largest_checked_2359_1_part19 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 2432 128 = 6986686583159928142356253152 := by decide +kernel
private theorem largest_checked_2359_1_part20 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 2560 128 = 3385032383462231805314783712 := by decide +kernel
private theorem largest_checked_2359_1_part21 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 2688 62 = 391667436727647411779906574 := by decide +kernel
private theorem largest_checked_2359_1_join0 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 0 256 = 199963196919143844576229753792 :=
  phaseBlock_append largest_checked_2359_1_part0 largest_checked_2359_1_part1 rfl rfl rfl
private theorem largest_checked_2359_1_join1 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 384 256 = 163452410888244977349789377472 :=
  phaseBlock_append largest_checked_2359_1_part3 largest_checked_2359_1_part4 rfl rfl rfl
private theorem largest_checked_2359_1_join2 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 256 384 = 254147754007983528022227525024 :=
  phaseBlock_append largest_checked_2359_1_part2 largest_checked_2359_1_join1 rfl rfl rfl
private theorem largest_checked_2359_1_join3 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 0 640 = 454110950927127372598457278816 :=
  phaseBlock_append largest_checked_2359_1_join0 largest_checked_2359_1_join2 rfl rfl rfl
private theorem largest_checked_2359_1_join4 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 768 256 = 129272463892114750144645579712 :=
  phaseBlock_append largest_checked_2359_1_part6 largest_checked_2359_1_part7 rfl rfl rfl
private theorem largest_checked_2359_1_join5 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 640 384 = 202288523989171289529775254944 :=
  phaseBlock_append largest_checked_2359_1_part5 largest_checked_2359_1_join4 rfl rfl rfl
private theorem largest_checked_2359_1_join6 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 1152 256 = 97517772961756477945310225344 :=
  phaseBlock_append largest_checked_2359_1_part9 largest_checked_2359_1_part10 rfl rfl rfl
private theorem largest_checked_2359_1_join7 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 1024 384 = 154043659828769997392339484064 :=
  phaseBlock_append largest_checked_2359_1_part8 largest_checked_2359_1_join6 rfl rfl rfl
private theorem largest_checked_2359_1_join8 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 640 768 = 356332183817941286922114739008 :=
  phaseBlock_append largest_checked_2359_1_join5 largest_checked_2359_1_join7 rfl rfl rfl
private theorem largest_checked_2359_1_join9 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 0 1408 = 810443134745068659520572017824 :=
  phaseBlock_append largest_checked_2359_1_join3 largest_checked_2359_1_join8 rfl rfl rfl
private theorem largest_checked_2359_1_join10 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 1408 256 = 77741409378114196616585634752 :=
  phaseBlock_append largest_checked_2359_1_part11 largest_checked_2359_1_part12 rfl rfl rfl
private theorem largest_checked_2359_1_join11 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 1792 256 = 50235271594837512079345927104 :=
  phaseBlock_append largest_checked_2359_1_part14 largest_checked_2359_1_part15 rfl rfl rfl
private theorem largest_checked_2359_1_join12 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 1664 384 = 82047103527612906637408529824 :=
  phaseBlock_append largest_checked_2359_1_part13 largest_checked_2359_1_join11 rfl rfl rfl
private theorem largest_checked_2359_1_join13 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 1408 640 = 159788512905727103253994164576 :=
  phaseBlock_append largest_checked_2359_1_join10 largest_checked_2359_1_join12 rfl rfl rfl
private theorem largest_checked_2359_1_join14 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 2176 256 = 25400136705910835293286245312 :=
  phaseBlock_append largest_checked_2359_1_part17 largest_checked_2359_1_part18 rfl rfl rfl
private theorem largest_checked_2359_1_join15 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 2048 384 = 44120364542257215165080452512 :=
  phaseBlock_append largest_checked_2359_1_part16 largest_checked_2359_1_join14 rfl rfl rfl
private theorem largest_checked_2359_1_join16 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 2560 190 = 3776699820189879217094690286 :=
  phaseBlock_append largest_checked_2359_1_part20 largest_checked_2359_1_part21 rfl rfl rfl
private theorem largest_checked_2359_1_join17 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 2432 318 = 10763386403349807359450943438 :=
  phaseBlock_append largest_checked_2359_1_part19 largest_checked_2359_1_join16 rfl rfl rfl
private theorem largest_checked_2359_1_join18 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 2048 702 = 54883750945607022524531395950 :=
  phaseBlock_append largest_checked_2359_1_join15 largest_checked_2359_1_join17 rfl rfl rfl
private theorem largest_checked_2359_1_join19 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 1408 1342 = 214672263851334125778525560526 :=
  phaseBlock_append largest_checked_2359_1_join13 largest_checked_2359_1_join18 rfl rfl rfl
private theorem largest_checked_2359_1_join20 :
    phaseBlock (fastLayer largestBank.shape 179818 2359 103 1 1 1 1) 0 2750 = 1025115398596402785299097578350 :=
  phaseBlock_append largest_checked_2359_1_join9 largest_checked_2359_1_join19 rfl rfl rfl

private theorem largest_checked_2359_1 : fastPhase largestBank.shape 179818 2359 103 1 1 1 1 = 1025115398596402785299097578350 :=
  phase_of_block (n := 2750) (by decide +kernel) largest_checked_2359_1_join20

private theorem largest_checked_2360_0_part0 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 0 128 = 103168478855255663956096737504 := by decide +kernel
private theorem largest_checked_2360_0_part1 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 128 128 = 96893234898709183738854879456 := by decide +kernel
private theorem largest_checked_2360_0_part2 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 256 128 = 90743055895826708966149390560 := by decide +kernel
private theorem largest_checked_2360_0_part3 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 384 128 = 84719716967040165383947964640 := by decide +kernel
private theorem largest_checked_2360_0_part4 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 512 128 = 78824985559101208128762781920 := by decide +kernel
private theorem largest_checked_2360_0_part5 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 640 128 = 73060621454534690761873223904 := by decide +kernel
private theorem largest_checked_2360_0_part6 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 768 128 = 67428376781092134303548588256 := by decide +kernel
private theorem largest_checked_2360_0_part7 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 896 128 = 61929996021205196267270803680 := by decide +kernel
private theorem largest_checked_2360_0_part8 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 1024 128 = 56567216021439139693957144800 := by decide +kernel
private theorem largest_checked_2360_0_part9 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 1152 128 = 51341766001946302186182947040 := by decide +kernel
private theorem largest_checked_2360_0_part10 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 1280 128 = 46255367565919564942404321504 := by decide +kernel
private theorem largest_checked_2360_0_part11 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 1408 128 = 41309734709045821791180869856 := by decide +kernel
private theorem largest_checked_2360_0_part12 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 1536 128 = 36506573828959448225398399200 := by decide +kernel
private theorem largest_checked_2360_0_part13 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 1664 128 = 31847583734695770436491636960 := by decide +kernel
private theorem largest_checked_2360_0_part14 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 1792 128 = 27334455656144534348666945760 := by decide +kernel
private theorem largest_checked_2360_0_part15 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 1920 128 = 22968873253503374653125038304 := by decide +kernel
private theorem largest_checked_2360_0_part16 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 2048 128 = 18752512626731283842283692256 := by decide +kernel
private theorem largest_checked_2360_0_part17 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 2176 128 = 14687042325002081244000465120 := by decide +kernel
private theorem largest_checked_2360_0_part18 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 2304 128 = 10774123356157882055795409120 := by decide +kernel
private theorem largest_checked_2360_0_part19 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 2432 128 = 7015409196162566379073786080 := by decide +kernel
private theorem largest_checked_2360_0_part20 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 2560 128 = 3412545798555248253348782304 := by decide +kernel
private theorem largest_checked_2360_0_part21 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 2688 62 = 404556234305907921289009776 := by decide +kernel
private theorem largest_checked_2360_0_join0 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 0 256 = 200061713753964847694951616960 :=
  phaseBlock_append largest_checked_2360_0_part0 largest_checked_2360_0_part1 rfl rfl rfl
private theorem largest_checked_2360_0_join1 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 384 256 = 163544702526141373512710746560 :=
  phaseBlock_append largest_checked_2360_0_part3 largest_checked_2360_0_part4 rfl rfl rfl
private theorem largest_checked_2360_0_join2 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 256 384 = 254287758421968082478860137120 :=
  phaseBlock_append largest_checked_2360_0_part2 largest_checked_2360_0_join1 rfl rfl rfl
private theorem largest_checked_2360_0_join3 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 0 640 = 454349472175932930173811754080 :=
  phaseBlock_append largest_checked_2360_0_join0 largest_checked_2360_0_join2 rfl rfl rfl
private theorem largest_checked_2360_0_join4 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 768 256 = 129358372802297330570819391936 :=
  phaseBlock_append largest_checked_2360_0_part6 largest_checked_2360_0_part7 rfl rfl rfl
private theorem largest_checked_2360_0_join5 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 640 384 = 202418994256832021332692615840 :=
  phaseBlock_append largest_checked_2360_0_part5 largest_checked_2360_0_join4 rfl rfl rfl
private theorem largest_checked_2360_0_join6 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 1152 256 = 97597133567865867128587268544 :=
  phaseBlock_append largest_checked_2360_0_part9 largest_checked_2360_0_part10 rfl rfl rfl
private theorem largest_checked_2360_0_join7 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 1024 384 = 154164349589305006822544413344 :=
  phaseBlock_append largest_checked_2360_0_part8 largest_checked_2360_0_join6 rfl rfl rfl
private theorem largest_checked_2360_0_join8 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 640 768 = 356583343846137028155237029184 :=
  phaseBlock_append largest_checked_2360_0_join5 largest_checked_2360_0_join7 rfl rfl rfl
private theorem largest_checked_2360_0_join9 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 0 1408 = 810932816022069958329048783264 :=
  phaseBlock_append largest_checked_2360_0_join3 largest_checked_2360_0_join8 rfl rfl rfl
private theorem largest_checked_2360_0_join10 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 1408 256 = 77816308538005270016579269056 :=
  phaseBlock_append largest_checked_2360_0_part11 largest_checked_2360_0_part12 rfl rfl rfl
private theorem largest_checked_2360_0_join11 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 1792 256 = 50303328909647909001791984064 :=
  phaseBlock_append largest_checked_2360_0_part14 largest_checked_2360_0_part15 rfl rfl rfl
private theorem largest_checked_2360_0_join12 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 1664 384 = 82150912644343679438283621024 :=
  phaseBlock_append largest_checked_2360_0_part13 largest_checked_2360_0_join11 rfl rfl rfl
private theorem largest_checked_2360_0_join13 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 1408 640 = 159967221182348949454862890080 :=
  phaseBlock_append largest_checked_2360_0_join10 largest_checked_2360_0_join12 rfl rfl rfl
private theorem largest_checked_2360_0_join14 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 2176 256 = 25461165681159963299795874240 :=
  phaseBlock_append largest_checked_2360_0_part17 largest_checked_2360_0_part18 rfl rfl rfl
private theorem largest_checked_2360_0_join15 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 2048 384 = 44213678307891247142079566496 :=
  phaseBlock_append largest_checked_2360_0_part16 largest_checked_2360_0_join14 rfl rfl rfl
private theorem largest_checked_2360_0_join16 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 2560 190 = 3817102032861156174637792080 :=
  phaseBlock_append largest_checked_2360_0_part20 largest_checked_2360_0_part21 rfl rfl rfl
private theorem largest_checked_2360_0_join17 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 2432 318 = 10832511229023722553711578160 :=
  phaseBlock_append largest_checked_2360_0_part19 largest_checked_2360_0_join16 rfl rfl rfl
private theorem largest_checked_2360_0_join18 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 2048 702 = 55046189536914969695791144656 :=
  phaseBlock_append largest_checked_2360_0_join15 largest_checked_2360_0_join17 rfl rfl rfl
private theorem largest_checked_2360_0_join19 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 1408 1342 = 215013410719263919150654034736 :=
  phaseBlock_append largest_checked_2360_0_join13 largest_checked_2360_0_join18 rfl rfl rfl
private theorem largest_checked_2360_0_join20 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 0) 0 2750 = 1025946226741333877479702818000 :=
  phaseBlock_append largest_checked_2360_0_join9 largest_checked_2360_0_join19 rfl rfl rfl

private theorem largest_checked_2360_0 : fastPhase largestBank.shape 179818 2360 103 1 1 1 0 = 1025946226741333877479702818000 :=
  phase_of_block (n := 2750) (by decide +kernel) largest_checked_2360_0_join20

private theorem largest_checked_2360_1_part0 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 0 128 = 103119634433534514960580038240 := by decide +kernel
private theorem largest_checked_2360_1_part1 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 128 128 = 96845317700315912008409931360 := by decide +kernel
private theorem largest_checked_2360_1_part2 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 256 128 = 90696080983641333177076575840 := by decide +kernel
private theorem largest_checked_2360_1_part3 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 384 128 = 84673699340817339969902673504 := by decide +kernel
private theorem largest_checked_2360_1_part4 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 512 128 = 78779940155546997710957022816 := by decide +kernel
private theorem largest_checked_2360_1_part5 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 640 128 = 73016563147383344579277233760 := by decide +kernel
private theorem largest_checked_2360_1_part6 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 768 128 = 67385320381182860643092442720 := by decide +kernel
private theorem largest_checked_2360_1_part7 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 896 128 = 61887956276558936894046027360 := by decide +kernel
private theorem largest_checked_2360_1_part8 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 1024 128 = 56526207617335344281418321504 := by decide +kernel
private theorem largest_checked_2360_1_part9 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 1152 128 = 51301803560999702746349330016 := by decide +kernel
private theorem largest_checked_2360_1_part10 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 1280 128 = 46216465648156950256061443680 := by decide +kernel
private theorem largest_checked_2360_1_part11 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 1408 128 = 41271907811982811838082154080 := by decide +kernel
private theorem largest_checked_2360_1_part12 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 1536 128 = 36469836387677268614466768480 := by decide +kernel
private theorem largest_checked_2360_1_part13 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 1664 128 = 31811950121918026836021124704 := by decide +kernel
private theorem largest_checked_2360_1_part14 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 1792 128 = 27299940182313986916524306016 := by decide +kernel
private theorem largest_checked_2360_1_part15 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 1920 128 = 22935490166858712466951356000 := by decide +kernel
private theorem largest_checked_2360_1_part16 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 2048 128 = 18720276113383899329695993440 := by decide +kernel
private theorem largest_checked_2360_1_part17 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 2176 128 = 14655966509012844612793327200 := by decide +kernel
private theorem largest_checked_2360_1_part18 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 2304 128 = 10744222299613915724142571104 := by decide +kernel
private theorem largest_checked_2360_1_part19 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 2432 128 = 6986696899254019405729758816 := by decide +kernel
private theorem largest_checked_2360_1_part20 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 2560 128 = 3385036199652070767850458720 := by decide +kernel
private theorem largest_checked_2360_1_part21 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 2688 62 = 391667772303850436340472890 := by decide +kernel
private theorem largest_checked_2360_1_join0 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 0 256 = 199964952133850426968989969600 :=
  phaseBlock_append largest_checked_2360_1_part0 largest_checked_2360_1_part1 rfl rfl rfl
private theorem largest_checked_2360_1_join1 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 384 256 = 163453639496364337680859696320 :=
  phaseBlock_append largest_checked_2360_1_part3 largest_checked_2360_1_part4 rfl rfl rfl
private theorem largest_checked_2360_1_join2 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 256 384 = 254149720480005670857936272160 :=
  phaseBlock_append largest_checked_2360_1_part2 largest_checked_2360_1_join1 rfl rfl rfl
private theorem largest_checked_2360_1_join3 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 0 640 = 454114672613856097826926241760 :=
  phaseBlock_append largest_checked_2360_1_join0 largest_checked_2360_1_join2 rfl rfl rfl
private theorem largest_checked_2360_1_join4 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 768 256 = 129273276657741797537138470080 :=
  phaseBlock_append largest_checked_2360_1_part6 largest_checked_2360_1_part7 rfl rfl rfl
private theorem largest_checked_2360_1_join5 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 640 384 = 202289839805125142116415703840 :=
  phaseBlock_append largest_checked_2360_1_part5 largest_checked_2360_1_join4 rfl rfl rfl
private theorem largest_checked_2360_1_join6 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 1152 256 = 97518269209156653002410773696 :=
  phaseBlock_append largest_checked_2360_1_part9 largest_checked_2360_1_part10 rfl rfl rfl
private theorem largest_checked_2360_1_join7 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 1024 384 = 154044476826491997283829095200 :=
  phaseBlock_append largest_checked_2360_1_part8 largest_checked_2360_1_join6 rfl rfl rfl
private theorem largest_checked_2360_1_join8 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 640 768 = 356334316631617139400244799040 :=
  phaseBlock_append largest_checked_2360_1_join5 largest_checked_2360_1_join7 rfl rfl rfl
private theorem largest_checked_2360_1_join9 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 0 1408 = 810448989245473237227171040800 :=
  phaseBlock_append largest_checked_2360_1_join3 largest_checked_2360_1_join8 rfl rfl rfl
private theorem largest_checked_2360_1_join10 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 1408 256 = 77741744199660080452548922560 :=
  phaseBlock_append largest_checked_2360_1_part11 largest_checked_2360_1_part12 rfl rfl rfl
private theorem largest_checked_2360_1_join11 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 1792 256 = 50235430349172699383475662016 :=
  phaseBlock_append largest_checked_2360_1_part14 largest_checked_2360_1_part15 rfl rfl rfl
private theorem largest_checked_2360_1_join12 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 1664 384 = 82047380471090726219496786720 :=
  phaseBlock_append largest_checked_2360_1_part13 largest_checked_2360_1_join11 rfl rfl rfl
private theorem largest_checked_2360_1_join13 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 1408 640 = 159789124670750806672045709280 :=
  phaseBlock_append largest_checked_2360_1_join10 largest_checked_2360_1_join12 rfl rfl rfl
private theorem largest_checked_2360_1_join14 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 2176 256 = 25400188808626760336935898304 :=
  phaseBlock_append largest_checked_2360_1_part17 largest_checked_2360_1_part18 rfl rfl rfl
private theorem largest_checked_2360_1_join15 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 2048 384 = 44120464922010659666631891744 :=
  phaseBlock_append largest_checked_2360_1_part16 largest_checked_2360_1_join14 rfl rfl rfl
private theorem largest_checked_2360_1_join16 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 2560 190 = 3776703971955921204190931610 :=
  phaseBlock_append largest_checked_2360_1_part20 largest_checked_2360_1_part21 rfl rfl rfl
private theorem largest_checked_2360_1_join17 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 2432 318 = 10763400871209940609920690426 :=
  phaseBlock_append largest_checked_2360_1_part19 largest_checked_2360_1_join16 rfl rfl rfl
private theorem largest_checked_2360_1_join18 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 2048 702 = 54883865793220600276552582170 :=
  phaseBlock_append largest_checked_2360_1_join15 largest_checked_2360_1_join17 rfl rfl rfl
private theorem largest_checked_2360_1_join19 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 1408 1342 = 214672990463971406948598291450 :=
  phaseBlock_append largest_checked_2360_1_join13 largest_checked_2360_1_join18 rfl rfl rfl
private theorem largest_checked_2360_1_join20 :
    phaseBlock (fastLayer largestBank.shape 179818 2360 103 1 1 1 1) 0 2750 = 1025121979709444644175769332250 :=
  phaseBlock_append largest_checked_2360_1_join9 largest_checked_2360_1_join19 rfl rfl rfl

private theorem largest_checked_2360_1 : fastPhase largestBank.shape 179818 2360 103 1 1 1 1 = 1025121979709444644175769332250 :=
  phase_of_block (n := 2750) (by decide +kernel) largest_checked_2360_1_join20

theorem largest_checked : Checked largestBank 103 1 1 := by
  refine checked_from_values largestBank 103 1 1
    (P3_7_1.checked largestBank rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_12604_2749)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) largest_checked_2359_0 largest_checked_2359_1 largest_checked_2360_0 largest_checked_2360_1 (by decide +kernel) (by decide +kernel)


/-- The last stage of the high-jet rectangle, with no numerical premises. -/
theorem largest_avoids {h : ℕ} {D : K1_14_1.PoleData h} (Crt : K1_14_1.CRTLift D)
    (word : K1.I → K1_14.L) (lo : 2359≤h) (hi : h≤33579) {G : K1_14.Jet}
    (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (seed : 1≤K1_14_2_2_2_1.seedDegree G)
    (excess : G.natDegree+1≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word largestBank.shape (buffered largestBank h 103), ¬ G∣Q :=
  largest_checked.avoids Crt word lo hi irr seeded slope seed excess

#print axioms largest_checked
#print axioms largest_avoids

end Lower6960.RescueSource
