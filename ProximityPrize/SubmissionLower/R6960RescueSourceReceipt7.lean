import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt1

set_option Elab.async false

-- merged module R6960RescueSourceLargest
section Merged_R6960RescueSourceLargest

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


end Lower6960.RescueSource

end Merged_R6960RescueSourceLargest

-- merged module R6960RescueSourceReceipt7
section Merged_R6960RescueSourceReceipt7

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open HelperSource (WidthGuard)

private theorem moment_12604_2649_part0 :
    blockEstimate 12604 2649 2649 128 = 4475130400 := by decide +kernel
private theorem moment_12604_2649_part1 :
    blockEstimate 12604 2649 2777 128 = 30641234464 := by decide +kernel
private theorem moment_12604_2649_part2 :
    blockEstimate 12604 2649 2905 128 = 82028737056 := by decide +kernel
private theorem moment_12604_2649_part3 :
    blockEstimate 12604 2649 3033 128 = 157832331808 := by decide +kernel
private theorem moment_12604_2649_part4 :
    blockEstimate 12604 2649 3161 128 = 257246712352 := by decide +kernel
private theorem moment_12604_2649_part5 :
    blockEstimate 12604 2649 3289 128 = 379466572320 := by decide +kernel
private theorem moment_12604_2649_part6 :
    blockEstimate 12604 2649 3417 128 = 523686605344 := by decide +kernel
private theorem moment_12604_2649_part7 :
    blockEstimate 12604 2649 3545 128 = 689101505056 := by decide +kernel
private theorem moment_12604_2649_part8 :
    blockEstimate 12604 2649 3673 128 = 874905965088 := by decide +kernel
private theorem moment_12604_2649_part9 :
    blockEstimate 12604 2649 3801 128 = 1080294679072 := by decide +kernel
private theorem moment_12604_2649_part10 :
    blockEstimate 12604 2649 3929 128 = 1304462340640 := by decide +kernel
private theorem moment_12604_2649_part11 :
    blockEstimate 12604 2649 4057 128 = 1546603643424 := by decide +kernel
private theorem moment_12604_2649_part12 :
    blockEstimate 12604 2649 4185 128 = 1805913281056 := by decide +kernel
private theorem moment_12604_2649_part13 :
    blockEstimate 12604 2649 4313 128 = 2081585947168 := by decide +kernel
private theorem moment_12604_2649_part14 :
    blockEstimate 12604 2649 4441 128 = 2372816335392 := by decide +kernel
private theorem moment_12604_2649_part15 :
    blockEstimate 12604 2649 4569 128 = 2678799139360 := by decide +kernel
private theorem moment_12604_2649_part16 :
    blockEstimate 12604 2649 4697 128 = 2998729052704 := by decide +kernel
private theorem moment_12604_2649_part17 :
    blockEstimate 12604 2649 4825 128 = 3331800769056 := by decide +kernel
private theorem moment_12604_2649_part18 :
    blockEstimate 12604 2649 4953 128 = 3677208982048 := by decide +kernel
private theorem moment_12604_2649_part19 :
    blockEstimate 12604 2649 5081 128 = 4034148385312 := by decide +kernel
private theorem moment_12604_2649_part20 :
    blockEstimate 12604 2649 5209 128 = 4401715601130 := by decide +kernel
private theorem moment_12604_2649_part21 :
    blockEstimate 12604 2649 5337 128 = 4771867211200 := by decide +kernel
private theorem moment_12604_2649_part22 :
    blockEstimate 12604 2649 5465 128 = 5132081329600 := by decide +kernel
private theorem moment_12604_2649_part23 :
    blockEstimate 12604 2649 5593 128 = 5481180542400 := by decide +kernel
private theorem moment_12604_2649_part24 :
    blockEstimate 12604 2649 5721 128 = 5819164849600 := by decide +kernel
private theorem moment_12604_2649_part25 :
    blockEstimate 12604 2649 5849 128 = 6146034251200 := by decide +kernel
private theorem moment_12604_2649_part26 :
    blockEstimate 12604 2649 5977 128 = 6461788747200 := by decide +kernel
private theorem moment_12604_2649_part27 :
    blockEstimate 12604 2649 6105 128 = 6766428337600 := by decide +kernel
private theorem moment_12604_2649_part28 :
    blockEstimate 12604 2649 6233 128 = 7059953022400 := by decide +kernel
private theorem moment_12604_2649_part29 :
    blockEstimate 12604 2649 6361 128 = 7342362801600 := by decide +kernel
private theorem moment_12604_2649_part30 :
    blockEstimate 12604 2649 6489 128 = 7613657675200 := by decide +kernel
private theorem moment_12604_2649_part31 :
    blockEstimate 12604 2649 6617 128 = 7873837643200 := by decide +kernel
private theorem moment_12604_2649_part32 :
    blockEstimate 12604 2649 6745 128 = 8122902705600 := by decide +kernel
private theorem moment_12604_2649_part33 :
    blockEstimate 12604 2649 6873 128 = 8360852862400 := by decide +kernel
private theorem moment_12604_2649_part34 :
    blockEstimate 12604 2649 7001 128 = 8587688113600 := by decide +kernel
private theorem moment_12604_2649_part35 :
    blockEstimate 12604 2649 7129 128 = 8803408459200 := by decide +kernel
private theorem moment_12604_2649_part36 :
    blockEstimate 12604 2649 7257 128 = 9008013899200 := by decide +kernel
private theorem moment_12604_2649_part37 :
    blockEstimate 12604 2649 7385 128 = 9201504433600 := by decide +kernel
private theorem moment_12604_2649_part38 :
    blockEstimate 12604 2649 7513 128 = 9383880062400 := by decide +kernel
private theorem moment_12604_2649_part39 :
    blockEstimate 12604 2649 7641 128 = 9555140785600 := by decide +kernel
private theorem moment_12604_2649_part40 :
    blockEstimate 12604 2649 7769 128 = 9715286603200 := by decide +kernel
private theorem moment_12604_2649_part41 :
    blockEstimate 12604 2649 7897 128 = 9864317515200 := by decide +kernel
private theorem moment_12604_2649_part42 :
    blockEstimate 12604 2649 8025 128 = 10002233521600 := by decide +kernel
private theorem moment_12604_2649_part43 :
    blockEstimate 12604 2649 8153 128 = 10129034622400 := by decide +kernel
private theorem moment_12604_2649_part44 :
    blockEstimate 12604 2649 8281 128 = 10244720817600 := by decide +kernel
private theorem moment_12604_2649_part45 :
    blockEstimate 12604 2649 8409 128 = 10349292107200 := by decide +kernel
private theorem moment_12604_2649_part46 :
    blockEstimate 12604 2649 8537 128 = 10442748491200 := by decide +kernel
private theorem moment_12604_2649_part47 :
    blockEstimate 12604 2649 8665 128 = 10525089969600 := by decide +kernel
private theorem moment_12604_2649_part48 :
    blockEstimate 12604 2649 8793 128 = 10596316542400 := by decide +kernel
private theorem moment_12604_2649_part49 :
    blockEstimate 12604 2649 8921 128 = 10656428209600 := by decide +kernel
private theorem moment_12604_2649_part50 :
    blockEstimate 12604 2649 9049 128 = 10705424971200 := by decide +kernel
private theorem moment_12604_2649_part51 :
    blockEstimate 12604 2649 9177 128 = 10743306827200 := by decide +kernel
private theorem moment_12604_2649_part52 :
    blockEstimate 12604 2649 9305 128 = 10770073777600 := by decide +kernel
private theorem moment_12604_2649_part53 :
    blockEstimate 12604 2649 9433 128 = 10785725822400 := by decide +kernel
private theorem moment_12604_2649_part54 :
    blockEstimate 12604 2649 9561 128 = 10790262961600 := by decide +kernel
private theorem moment_12604_2649_part55 :
    blockEstimate 12604 2649 9689 128 = 10783685195200 := by decide +kernel
private theorem moment_12604_2649_part56 :
    blockEstimate 12604 2649 9817 128 = 10765992523200 := by decide +kernel
private theorem moment_12604_2649_part57 :
    blockEstimate 12604 2649 9945 128 = 10737184945600 := by decide +kernel
private theorem moment_12604_2649_part58 :
    blockEstimate 12604 2649 10073 128 = 10697262462400 := by decide +kernel
private theorem moment_12604_2649_part59 :
    blockEstimate 12604 2649 10201 128 = 10646225073600 := by decide +kernel
private theorem moment_12604_2649_part60 :
    blockEstimate 12604 2649 10329 128 = 10584072779200 := by decide +kernel
private theorem moment_12604_2649_part61 :
    blockEstimate 12604 2649 10457 128 = 10510805579200 := by decide +kernel
private theorem moment_12604_2649_part62 :
    blockEstimate 12604 2649 10585 128 = 10426423473600 := by decide +kernel
private theorem moment_12604_2649_part63 :
    blockEstimate 12604 2649 10713 128 = 10330926462400 := by decide +kernel
private theorem moment_12604_2649_part64 :
    blockEstimate 12604 2649 10841 128 = 10224314545600 := by decide +kernel
private theorem moment_12604_2649_part65 :
    blockEstimate 12604 2649 10969 128 = 10106587723200 := by decide +kernel
private theorem moment_12604_2649_part66 :
    blockEstimate 12604 2649 11097 128 = 9977745995200 := by decide +kernel
private theorem moment_12604_2649_part67 :
    blockEstimate 12604 2649 11225 128 = 9837789361600 := by decide +kernel
private theorem moment_12604_2649_part68 :
    blockEstimate 12604 2649 11353 128 = 9686717822400 := by decide +kernel
private theorem moment_12604_2649_part69 :
    blockEstimate 12604 2649 11481 128 = 9524531377600 := by decide +kernel
private theorem moment_12604_2649_part70 :
    blockEstimate 12604 2649 11609 128 = 9351230027200 := by decide +kernel
private theorem moment_12604_2649_part71 :
    blockEstimate 12604 2649 11737 128 = 9166813771200 := by decide +kernel
private theorem moment_12604_2649_part72 :
    blockEstimate 12604 2649 11865 128 = 8971282609600 := by decide +kernel
private theorem moment_12604_2649_part73 :
    blockEstimate 12604 2649 11993 128 = 8764636542400 := by decide +kernel
private theorem moment_12604_2649_part74 :
    blockEstimate 12604 2649 12121 128 = 8546875569600 := by decide +kernel
private theorem moment_12604_2649_part75 :
    blockEstimate 12604 2649 12249 128 = 8317999691200 := by decide +kernel
private theorem moment_12604_2649_part76 :
    blockEstimate 12604 2649 12377 128 = 8078008907200 := by decide +kernel
private theorem moment_12604_2649_part77 :
    blockEstimate 12604 2649 12505 128 = 7826918884650 := by decide +kernel
private theorem moment_12604_2649_part78 :
    blockEstimate 12604 2649 12633 128 = 7567102754034 := by decide +kernel
private theorem moment_12604_2649_part79 :
    blockEstimate 12604 2649 12761 128 = 7303696640350 := by decide +kernel
private theorem moment_12604_2649_part80 :
    blockEstimate 12604 2649 12889 128 = 7037865387632 := by decide +kernel
private theorem moment_12604_2649_part81 :
    blockEstimate 12604 2649 13017 128 = 6770191281197 := by decide +kernel
private theorem moment_12604_2649_part82 :
    blockEstimate 12604 2649 13145 128 = 6501246890254 := by decide +kernel
private theorem moment_12604_2649_part83 :
    blockEstimate 12604 2649 13273 128 = 6231595052787 := by decide +kernel
private theorem moment_12604_2649_part84 :
    blockEstimate 12604 2649 13401 128 = 5961788886798 := by decide +kernel
private theorem moment_12604_2649_part85 :
    blockEstimate 12604 2649 13529 128 = 5692371783893 := by decide +kernel
private theorem moment_12604_2649_part86 :
    blockEstimate 12604 2649 13657 128 = 5423877411117 := by decide +kernel
private theorem moment_12604_2649_part87 :
    blockEstimate 12604 2649 13785 128 = 5156829711342 := by decide +kernel
private theorem moment_12604_2649_part88 :
    blockEstimate 12604 2649 13913 128 = 4891742903279 := by decide +kernel
private theorem moment_12604_2649_part89 :
    blockEstimate 12604 2649 14041 128 = 4629121481428 := by decide +kernel
private theorem moment_12604_2649_part90 :
    blockEstimate 12604 2649 14169 128 = 4369460214349 := by decide +kernel
private theorem moment_12604_2649_part91 :
    blockEstimate 12604 2649 14297 128 = 4113244148396 := by decide +kernel
private theorem moment_12604_2649_part92 :
    blockEstimate 12604 2649 14425 128 = 3860948603163 := by decide +kernel
private theorem moment_12604_2649_part93 :
    blockEstimate 12604 2649 14553 128 = 3613039175669 := by decide +kernel
private theorem moment_12604_2649_part94 :
    blockEstimate 12604 2649 14681 128 = 3369971737114 := by decide +kernel
private theorem moment_12604_2649_part95 :
    blockEstimate 12604 2649 14809 128 = 3132192435330 := by decide +kernel
private theorem moment_12604_2649_part96 :
    blockEstimate 12604 2649 14937 128 = 2900137692866 := by decide +kernel
private theorem moment_12604_2649_part97 :
    blockEstimate 12604 2649 15065 128 = 2674234208264 := by decide +kernel
private theorem moment_12604_2649_part98 :
    blockEstimate 12604 2649 15193 128 = 2454409472858 := by decide +kernel
private theorem moment_12604_2649_part99 :
    blockEstimate 12604 2649 15321 128 = 2239380193904 := by decide +kernel
private theorem moment_12604_2649_part100 :
    blockEstimate 12604 2649 15449 128 = 2032210261616 := by decide +kernel
private theorem moment_12604_2649_part101 :
    blockEstimate 12604 2649 15577 128 = 1833558108784 := by decide +kernel
private theorem moment_12604_2649_part102 :
    blockEstimate 12604 2649 15705 128 = 1643675393648 := by decide +kernel
private theorem moment_12604_2649_part103 :
    blockEstimate 12604 2649 15833 128 = 1462813774448 := by decide +kernel
private theorem moment_12604_2649_part104 :
    blockEstimate 12604 2649 15961 128 = 1291224909424 := by decide +kernel
private theorem moment_12604_2649_part105 :
    blockEstimate 12604 2649 16089 128 = 1129160456816 := by decide +kernel
private theorem moment_12604_2649_part106 :
    blockEstimate 12604 2649 16217 128 = 976872074864 := by decide +kernel
private theorem moment_12604_2649_part107 :
    blockEstimate 12604 2649 16345 128 = 834611421808 := by decide +kernel
private theorem moment_12604_2649_part108 :
    blockEstimate 12604 2649 16473 128 = 702630155888 := by decide +kernel
private theorem moment_12604_2649_part109 :
    blockEstimate 12604 2649 16601 128 = 581179935344 := by decide +kernel
private theorem moment_12604_2649_part110 :
    blockEstimate 12604 2649 16729 128 = 470512418416 := by decide +kernel
private theorem moment_12604_2649_part111 :
    blockEstimate 12604 2649 16857 128 = 370879263344 := by decide +kernel
private theorem moment_12604_2649_part112 :
    blockEstimate 12604 2649 16985 128 = 282532128368 := by decide +kernel
private theorem moment_12604_2649_part113 :
    blockEstimate 12604 2649 17113 128 = 205722671728 := by decide +kernel
private theorem moment_12604_2649_part114 :
    blockEstimate 12604 2649 17241 128 = 140702551664 := by decide +kernel
private theorem moment_12604_2649_part115 :
    blockEstimate 12604 2649 17369 128 = 87723426416 := by decide +kernel
private theorem moment_12604_2649_part116 :
    blockEstimate 12604 2649 17497 128 = 47036954224 := by decide +kernel
private theorem moment_12604_2649_part117 :
    blockEstimate 12604 2649 17625 128 = 18894793328 := by decide +kernel
private theorem moment_12604_2649_part118 :
    blockEstimate 12604 2649 17753 128 = 3548601968 := by decide +kernel
private theorem moment_12604_2649_part119 :
    blockEstimate 12604 2649 17881 21 = 11914679 := by decide +kernel
private theorem moment_12604_2649_join0 :
    blockEstimate 12604 2649 2777 256 = 112669971520 :=
  block_append moment_12604_2649_part1 moment_12604_2649_part2 rfl rfl rfl
private theorem moment_12604_2649_join1 :
    blockEstimate 12604 2649 2649 384 = 117145101920 :=
  block_append moment_12604_2649_part0 moment_12604_2649_join0 rfl rfl rfl
private theorem moment_12604_2649_join2 :
    blockEstimate 12604 2649 3033 256 = 415079044160 :=
  block_append moment_12604_2649_part3 moment_12604_2649_part4 rfl rfl rfl
private theorem moment_12604_2649_join3 :
    blockEstimate 12604 2649 3289 256 = 903153177664 :=
  block_append moment_12604_2649_part5 moment_12604_2649_part6 rfl rfl rfl
private theorem moment_12604_2649_join4 :
    blockEstimate 12604 2649 3033 512 = 1318232221824 :=
  block_append moment_12604_2649_join2 moment_12604_2649_join3 rfl rfl rfl
private theorem moment_12604_2649_join5 :
    blockEstimate 12604 2649 2649 896 = 1435377323744 :=
  block_append moment_12604_2649_join1 moment_12604_2649_join4 rfl rfl rfl
private theorem moment_12604_2649_join6 :
    blockEstimate 12604 2649 3545 256 = 1564007470144 :=
  block_append moment_12604_2649_part7 moment_12604_2649_part8 rfl rfl rfl
private theorem moment_12604_2649_join7 :
    blockEstimate 12604 2649 3801 256 = 2384757019712 :=
  block_append moment_12604_2649_part9 moment_12604_2649_part10 rfl rfl rfl
private theorem moment_12604_2649_join8 :
    blockEstimate 12604 2649 3545 512 = 3948764489856 :=
  block_append moment_12604_2649_join6 moment_12604_2649_join7 rfl rfl rfl
private theorem moment_12604_2649_join9 :
    blockEstimate 12604 2649 4057 256 = 3352516924480 :=
  block_append moment_12604_2649_part11 moment_12604_2649_part12 rfl rfl rfl
private theorem moment_12604_2649_join10 :
    blockEstimate 12604 2649 4313 256 = 4454402282560 :=
  block_append moment_12604_2649_part13 moment_12604_2649_part14 rfl rfl rfl
private theorem moment_12604_2649_join11 :
    blockEstimate 12604 2649 4057 512 = 7806919207040 :=
  block_append moment_12604_2649_join9 moment_12604_2649_join10 rfl rfl rfl
private theorem moment_12604_2649_join12 :
    blockEstimate 12604 2649 3545 1024 = 11755683696896 :=
  block_append moment_12604_2649_join8 moment_12604_2649_join11 rfl rfl rfl
private theorem moment_12604_2649_join13 :
    blockEstimate 12604 2649 2649 1920 = 13191061020640 :=
  block_append moment_12604_2649_join5 moment_12604_2649_join12 rfl rfl rfl
private theorem moment_12604_2649_join14 :
    blockEstimate 12604 2649 4697 256 = 6330529821760 :=
  block_append moment_12604_2649_part16 moment_12604_2649_part17 rfl rfl rfl
private theorem moment_12604_2649_join15 :
    blockEstimate 12604 2649 4569 384 = 9009328961120 :=
  block_append moment_12604_2649_part15 moment_12604_2649_join14 rfl rfl rfl
private theorem moment_12604_2649_join16 :
    blockEstimate 12604 2649 4953 256 = 7711357367360 :=
  block_append moment_12604_2649_part18 moment_12604_2649_part19 rfl rfl rfl
private theorem moment_12604_2649_join17 :
    blockEstimate 12604 2649 5209 256 = 9173582812330 :=
  block_append moment_12604_2649_part20 moment_12604_2649_part21 rfl rfl rfl
private theorem moment_12604_2649_join18 :
    blockEstimate 12604 2649 4953 512 = 16884940179690 :=
  block_append moment_12604_2649_join16 moment_12604_2649_join17 rfl rfl rfl
private theorem moment_12604_2649_join19 :
    blockEstimate 12604 2649 4569 896 = 25894269140810 :=
  block_append moment_12604_2649_join15 moment_12604_2649_join18 rfl rfl rfl
private theorem moment_12604_2649_join20 :
    blockEstimate 12604 2649 5465 256 = 10613261872000 :=
  block_append moment_12604_2649_part22 moment_12604_2649_part23 rfl rfl rfl
private theorem moment_12604_2649_join21 :
    blockEstimate 12604 2649 5721 256 = 11965199100800 :=
  block_append moment_12604_2649_part24 moment_12604_2649_part25 rfl rfl rfl
private theorem moment_12604_2649_join22 :
    blockEstimate 12604 2649 5465 512 = 22578460972800 :=
  block_append moment_12604_2649_join20 moment_12604_2649_join21 rfl rfl rfl
private theorem moment_12604_2649_join23 :
    blockEstimate 12604 2649 5977 256 = 13228217084800 :=
  block_append moment_12604_2649_part26 moment_12604_2649_part27 rfl rfl rfl
private theorem moment_12604_2649_join24 :
    blockEstimate 12604 2649 6233 256 = 14402315824000 :=
  block_append moment_12604_2649_part28 moment_12604_2649_part29 rfl rfl rfl
private theorem moment_12604_2649_join25 :
    blockEstimate 12604 2649 5977 512 = 27630532908800 :=
  block_append moment_12604_2649_join23 moment_12604_2649_join24 rfl rfl rfl
private theorem moment_12604_2649_join26 :
    blockEstimate 12604 2649 5465 1024 = 50208993881600 :=
  block_append moment_12604_2649_join22 moment_12604_2649_join25 rfl rfl rfl
private theorem moment_12604_2649_join27 :
    blockEstimate 12604 2649 4569 1920 = 76103263022410 :=
  block_append moment_12604_2649_join19 moment_12604_2649_join26 rfl rfl rfl
private theorem moment_12604_2649_join28 :
    blockEstimate 12604 2649 2649 3840 = 89294324043050 :=
  block_append moment_12604_2649_join13 moment_12604_2649_join27 rfl rfl rfl
private theorem moment_12604_2649_join29 :
    blockEstimate 12604 2649 6617 256 = 15996740348800 :=
  block_append moment_12604_2649_part31 moment_12604_2649_part32 rfl rfl rfl
private theorem moment_12604_2649_join30 :
    blockEstimate 12604 2649 6489 384 = 23610398024000 :=
  block_append moment_12604_2649_part30 moment_12604_2649_join29 rfl rfl rfl
private theorem moment_12604_2649_join31 :
    blockEstimate 12604 2649 6873 256 = 16948540976000 :=
  block_append moment_12604_2649_part33 moment_12604_2649_part34 rfl rfl rfl
private theorem moment_12604_2649_join32 :
    blockEstimate 12604 2649 7129 256 = 17811422358400 :=
  block_append moment_12604_2649_part35 moment_12604_2649_part36 rfl rfl rfl
private theorem moment_12604_2649_join33 :
    blockEstimate 12604 2649 6873 512 = 34759963334400 :=
  block_append moment_12604_2649_join31 moment_12604_2649_join32 rfl rfl rfl
private theorem moment_12604_2649_join34 :
    blockEstimate 12604 2649 6489 896 = 58370361358400 :=
  block_append moment_12604_2649_join30 moment_12604_2649_join33 rfl rfl rfl
private theorem moment_12604_2649_join35 :
    blockEstimate 12604 2649 7385 256 = 18585384496000 :=
  block_append moment_12604_2649_part37 moment_12604_2649_part38 rfl rfl rfl
private theorem moment_12604_2649_join36 :
    blockEstimate 12604 2649 7641 256 = 19270427388800 :=
  block_append moment_12604_2649_part39 moment_12604_2649_part40 rfl rfl rfl
private theorem moment_12604_2649_join37 :
    blockEstimate 12604 2649 7385 512 = 37855811884800 :=
  block_append moment_12604_2649_join35 moment_12604_2649_join36 rfl rfl rfl
private theorem moment_12604_2649_join38 :
    blockEstimate 12604 2649 7897 256 = 19866551036800 :=
  block_append moment_12604_2649_part41 moment_12604_2649_part42 rfl rfl rfl
private theorem moment_12604_2649_join39 :
    blockEstimate 12604 2649 8153 256 = 20373755440000 :=
  block_append moment_12604_2649_part43 moment_12604_2649_part44 rfl rfl rfl
private theorem moment_12604_2649_join40 :
    blockEstimate 12604 2649 7897 512 = 40240306476800 :=
  block_append moment_12604_2649_join38 moment_12604_2649_join39 rfl rfl rfl
private theorem moment_12604_2649_join41 :
    blockEstimate 12604 2649 7385 1024 = 78096118361600 :=
  block_append moment_12604_2649_join37 moment_12604_2649_join40 rfl rfl rfl
private theorem moment_12604_2649_join42 :
    blockEstimate 12604 2649 6489 1920 = 136466479720000 :=
  block_append moment_12604_2649_join34 moment_12604_2649_join41 rfl rfl rfl
private theorem moment_12604_2649_join43 :
    blockEstimate 12604 2649 8537 256 = 20967838460800 :=
  block_append moment_12604_2649_part46 moment_12604_2649_part47 rfl rfl rfl
private theorem moment_12604_2649_join44 :
    blockEstimate 12604 2649 8409 384 = 31317130568000 :=
  block_append moment_12604_2649_part45 moment_12604_2649_join43 rfl rfl rfl
private theorem moment_12604_2649_join45 :
    blockEstimate 12604 2649 8793 256 = 21252744752000 :=
  block_append moment_12604_2649_part48 moment_12604_2649_part49 rfl rfl rfl
private theorem moment_12604_2649_join46 :
    blockEstimate 12604 2649 9049 256 = 21448731798400 :=
  block_append moment_12604_2649_part50 moment_12604_2649_part51 rfl rfl rfl
private theorem moment_12604_2649_join47 :
    blockEstimate 12604 2649 8793 512 = 42701476550400 :=
  block_append moment_12604_2649_join45 moment_12604_2649_join46 rfl rfl rfl
private theorem moment_12604_2649_join48 :
    blockEstimate 12604 2649 8409 896 = 74018607118400 :=
  block_append moment_12604_2649_join44 moment_12604_2649_join47 rfl rfl rfl
private theorem moment_12604_2649_join49 :
    blockEstimate 12604 2649 9305 256 = 21555799600000 :=
  block_append moment_12604_2649_part52 moment_12604_2649_part53 rfl rfl rfl
private theorem moment_12604_2649_join50 :
    blockEstimate 12604 2649 9561 256 = 21573948156800 :=
  block_append moment_12604_2649_part54 moment_12604_2649_part55 rfl rfl rfl
private theorem moment_12604_2649_join51 :
    blockEstimate 12604 2649 9305 512 = 43129747756800 :=
  block_append moment_12604_2649_join49 moment_12604_2649_join50 rfl rfl rfl
private theorem moment_12604_2649_join52 :
    blockEstimate 12604 2649 9817 256 = 21503177468800 :=
  block_append moment_12604_2649_part56 moment_12604_2649_part57 rfl rfl rfl
private theorem moment_12604_2649_join53 :
    blockEstimate 12604 2649 10073 256 = 21343487536000 :=
  block_append moment_12604_2649_part58 moment_12604_2649_part59 rfl rfl rfl
private theorem moment_12604_2649_join54 :
    blockEstimate 12604 2649 9817 512 = 42846665004800 :=
  block_append moment_12604_2649_join52 moment_12604_2649_join53 rfl rfl rfl
private theorem moment_12604_2649_join55 :
    blockEstimate 12604 2649 9305 1024 = 85976412761600 :=
  block_append moment_12604_2649_join51 moment_12604_2649_join54 rfl rfl rfl
private theorem moment_12604_2649_join56 :
    blockEstimate 12604 2649 8409 1920 = 159995019880000 :=
  block_append moment_12604_2649_join48 moment_12604_2649_join55 rfl rfl rfl
private theorem moment_12604_2649_join57 :
    blockEstimate 12604 2649 6489 3840 = 296461499600000 :=
  block_append moment_12604_2649_join42 moment_12604_2649_join56 rfl rfl rfl
private theorem moment_12604_2649_join58 :
    blockEstimate 12604 2649 2649 7680 = 385755823643050 :=
  block_append moment_12604_2649_join28 moment_12604_2649_join57 rfl rfl rfl
private theorem moment_12604_2649_join59 :
    blockEstimate 12604 2649 10457 256 = 20937229052800 :=
  block_append moment_12604_2649_part61 moment_12604_2649_part62 rfl rfl rfl
private theorem moment_12604_2649_join60 :
    blockEstimate 12604 2649 10329 384 = 31521301832000 :=
  block_append moment_12604_2649_part60 moment_12604_2649_join59 rfl rfl rfl
private theorem moment_12604_2649_join61 :
    blockEstimate 12604 2649 10713 256 = 20555241008000 :=
  block_append moment_12604_2649_part63 moment_12604_2649_part64 rfl rfl rfl
private theorem moment_12604_2649_join62 :
    blockEstimate 12604 2649 10969 256 = 20084333718400 :=
  block_append moment_12604_2649_part65 moment_12604_2649_part66 rfl rfl rfl
private theorem moment_12604_2649_join63 :
    blockEstimate 12604 2649 10713 512 = 40639574726400 :=
  block_append moment_12604_2649_join61 moment_12604_2649_join62 rfl rfl rfl
private theorem moment_12604_2649_join64 :
    blockEstimate 12604 2649 10329 896 = 72160876558400 :=
  block_append moment_12604_2649_join60 moment_12604_2649_join63 rfl rfl rfl
private theorem moment_12604_2649_join65 :
    blockEstimate 12604 2649 11225 256 = 19524507184000 :=
  block_append moment_12604_2649_part67 moment_12604_2649_part68 rfl rfl rfl
private theorem moment_12604_2649_join66 :
    blockEstimate 12604 2649 11481 256 = 18875761404800 :=
  block_append moment_12604_2649_part69 moment_12604_2649_part70 rfl rfl rfl
private theorem moment_12604_2649_join67 :
    blockEstimate 12604 2649 11225 512 = 38400268588800 :=
  block_append moment_12604_2649_join65 moment_12604_2649_join66 rfl rfl rfl
private theorem moment_12604_2649_join68 :
    blockEstimate 12604 2649 11737 256 = 18138096380800 :=
  block_append moment_12604_2649_part71 moment_12604_2649_part72 rfl rfl rfl
private theorem moment_12604_2649_join69 :
    blockEstimate 12604 2649 11993 256 = 17311512112000 :=
  block_append moment_12604_2649_part73 moment_12604_2649_part74 rfl rfl rfl
private theorem moment_12604_2649_join70 :
    blockEstimate 12604 2649 11737 512 = 35449608492800 :=
  block_append moment_12604_2649_join68 moment_12604_2649_join69 rfl rfl rfl
private theorem moment_12604_2649_join71 :
    blockEstimate 12604 2649 11225 1024 = 73849877081600 :=
  block_append moment_12604_2649_join67 moment_12604_2649_join70 rfl rfl rfl
private theorem moment_12604_2649_join72 :
    blockEstimate 12604 2649 10329 1920 = 146010753640000 :=
  block_append moment_12604_2649_join64 moment_12604_2649_join71 rfl rfl rfl
private theorem moment_12604_2649_join73 :
    blockEstimate 12604 2649 12377 256 = 15904927791850 :=
  block_append moment_12604_2649_part76 moment_12604_2649_part77 rfl rfl rfl
private theorem moment_12604_2649_join74 :
    blockEstimate 12604 2649 12249 384 = 24222927483050 :=
  block_append moment_12604_2649_part75 moment_12604_2649_join73 rfl rfl rfl
private theorem moment_12604_2649_join75 :
    blockEstimate 12604 2649 12633 256 = 14870799394384 :=
  block_append moment_12604_2649_part78 moment_12604_2649_part79 rfl rfl rfl
private theorem moment_12604_2649_join76 :
    blockEstimate 12604 2649 12889 256 = 13808056668829 :=
  block_append moment_12604_2649_part80 moment_12604_2649_part81 rfl rfl rfl
private theorem moment_12604_2649_join77 :
    blockEstimate 12604 2649 12633 512 = 28678856063213 :=
  block_append moment_12604_2649_join75 moment_12604_2649_join76 rfl rfl rfl
private theorem moment_12604_2649_join78 :
    blockEstimate 12604 2649 12249 896 = 52901783546263 :=
  block_append moment_12604_2649_join74 moment_12604_2649_join77 rfl rfl rfl
private theorem moment_12604_2649_join79 :
    blockEstimate 12604 2649 13145 256 = 12732841943041 :=
  block_append moment_12604_2649_part82 moment_12604_2649_part83 rfl rfl rfl
private theorem moment_12604_2649_join80 :
    blockEstimate 12604 2649 13401 256 = 11654160670691 :=
  block_append moment_12604_2649_part84 moment_12604_2649_part85 rfl rfl rfl
private theorem moment_12604_2649_join81 :
    blockEstimate 12604 2649 13145 512 = 24387002613732 :=
  block_append moment_12604_2649_join79 moment_12604_2649_join80 rfl rfl rfl
private theorem moment_12604_2649_join82 :
    blockEstimate 12604 2649 13657 256 = 10580707122459 :=
  block_append moment_12604_2649_part86 moment_12604_2649_part87 rfl rfl rfl
private theorem moment_12604_2649_join83 :
    blockEstimate 12604 2649 13913 256 = 9520864384707 :=
  block_append moment_12604_2649_part88 moment_12604_2649_part89 rfl rfl rfl
private theorem moment_12604_2649_join84 :
    blockEstimate 12604 2649 13657 512 = 20101571507166 :=
  block_append moment_12604_2649_join82 moment_12604_2649_join83 rfl rfl rfl
private theorem moment_12604_2649_join85 :
    blockEstimate 12604 2649 13145 1024 = 44488574120898 :=
  block_append moment_12604_2649_join81 moment_12604_2649_join84 rfl rfl rfl
private theorem moment_12604_2649_join86 :
    blockEstimate 12604 2649 12249 1920 = 97390357667161 :=
  block_append moment_12604_2649_join78 moment_12604_2649_join85 rfl rfl rfl
private theorem moment_12604_2649_join87 :
    blockEstimate 12604 2649 10329 3840 = 243401111307161 :=
  block_append moment_12604_2649_join72 moment_12604_2649_join86 rfl rfl rfl
private theorem moment_12604_2649_join88 :
    blockEstimate 12604 2649 14297 256 = 7974192751559 :=
  block_append moment_12604_2649_part91 moment_12604_2649_part92 rfl rfl rfl
private theorem moment_12604_2649_join89 :
    blockEstimate 12604 2649 14169 384 = 12343652965908 :=
  block_append moment_12604_2649_part90 moment_12604_2649_join88 rfl rfl rfl
private theorem moment_12604_2649_join90 :
    blockEstimate 12604 2649 14553 256 = 6983010912783 :=
  block_append moment_12604_2649_part93 moment_12604_2649_part94 rfl rfl rfl
private theorem moment_12604_2649_join91 :
    blockEstimate 12604 2649 14809 256 = 6032330128196 :=
  block_append moment_12604_2649_part95 moment_12604_2649_part96 rfl rfl rfl
private theorem moment_12604_2649_join92 :
    blockEstimate 12604 2649 14553 512 = 13015341040979 :=
  block_append moment_12604_2649_join90 moment_12604_2649_join91 rfl rfl rfl
private theorem moment_12604_2649_join93 :
    blockEstimate 12604 2649 14169 896 = 25358994006887 :=
  block_append moment_12604_2649_join89 moment_12604_2649_join92 rfl rfl rfl
private theorem moment_12604_2649_join94 :
    blockEstimate 12604 2649 15065 256 = 5128643681122 :=
  block_append moment_12604_2649_part97 moment_12604_2649_part98 rfl rfl rfl
private theorem moment_12604_2649_join95 :
    blockEstimate 12604 2649 15321 256 = 4271590455520 :=
  block_append moment_12604_2649_part99 moment_12604_2649_part100 rfl rfl rfl
private theorem moment_12604_2649_join96 :
    blockEstimate 12604 2649 15065 512 = 9400234136642 :=
  block_append moment_12604_2649_join94 moment_12604_2649_join95 rfl rfl rfl
private theorem moment_12604_2649_join97 :
    blockEstimate 12604 2649 15577 256 = 3477233502432 :=
  block_append moment_12604_2649_part101 moment_12604_2649_part102 rfl rfl rfl
private theorem moment_12604_2649_join98 :
    blockEstimate 12604 2649 15833 256 = 2754038683872 :=
  block_append moment_12604_2649_part103 moment_12604_2649_part104 rfl rfl rfl
private theorem moment_12604_2649_join99 :
    blockEstimate 12604 2649 15577 512 = 6231272186304 :=
  block_append moment_12604_2649_join97 moment_12604_2649_join98 rfl rfl rfl
private theorem moment_12604_2649_join100 :
    blockEstimate 12604 2649 15065 1024 = 15631506322946 :=
  block_append moment_12604_2649_join96 moment_12604_2649_join99 rfl rfl rfl
private theorem moment_12604_2649_join101 :
    blockEstimate 12604 2649 14169 1920 = 40990500329833 :=
  block_append moment_12604_2649_join93 moment_12604_2649_join100 rfl rfl rfl
private theorem moment_12604_2649_join102 :
    blockEstimate 12604 2649 16217 256 = 1811483496672 :=
  block_append moment_12604_2649_part106 moment_12604_2649_part107 rfl rfl rfl
private theorem moment_12604_2649_join103 :
    blockEstimate 12604 2649 16089 384 = 2940643953488 :=
  block_append moment_12604_2649_part105 moment_12604_2649_join102 rfl rfl rfl
private theorem moment_12604_2649_join104 :
    blockEstimate 12604 2649 16473 256 = 1283810091232 :=
  block_append moment_12604_2649_part108 moment_12604_2649_part109 rfl rfl rfl
private theorem moment_12604_2649_join105 :
    blockEstimate 12604 2649 16729 256 = 841391681760 :=
  block_append moment_12604_2649_part110 moment_12604_2649_part111 rfl rfl rfl
private theorem moment_12604_2649_join106 :
    blockEstimate 12604 2649 16473 512 = 2125201772992 :=
  block_append moment_12604_2649_join104 moment_12604_2649_join105 rfl rfl rfl
private theorem moment_12604_2649_join107 :
    blockEstimate 12604 2649 16089 896 = 5065845726480 :=
  block_append moment_12604_2649_join103 moment_12604_2649_join106 rfl rfl rfl
private theorem moment_12604_2649_join108 :
    blockEstimate 12604 2649 16985 256 = 488254800096 :=
  block_append moment_12604_2649_part112 moment_12604_2649_part113 rfl rfl rfl
private theorem moment_12604_2649_join109 :
    blockEstimate 12604 2649 17241 256 = 228425978080 :=
  block_append moment_12604_2649_part114 moment_12604_2649_part115 rfl rfl rfl
private theorem moment_12604_2649_join110 :
    blockEstimate 12604 2649 16985 512 = 716680778176 :=
  block_append moment_12604_2649_join108 moment_12604_2649_join109 rfl rfl rfl
private theorem moment_12604_2649_join111 :
    blockEstimate 12604 2649 17497 256 = 65931747552 :=
  block_append moment_12604_2649_part116 moment_12604_2649_part117 rfl rfl rfl
private theorem moment_12604_2649_join112 :
    blockEstimate 12604 2649 17753 149 = 3560516647 :=
  block_append moment_12604_2649_part118 moment_12604_2649_part119 rfl rfl rfl
private theorem moment_12604_2649_join113 :
    blockEstimate 12604 2649 17497 405 = 69492264199 :=
  block_append moment_12604_2649_join111 moment_12604_2649_join112 rfl rfl rfl
private theorem moment_12604_2649_join114 :
    blockEstimate 12604 2649 16985 917 = 786173042375 :=
  block_append moment_12604_2649_join110 moment_12604_2649_join113 rfl rfl rfl
private theorem moment_12604_2649_join115 :
    blockEstimate 12604 2649 16089 1813 = 5852018768855 :=
  block_append moment_12604_2649_join107 moment_12604_2649_join114 rfl rfl rfl
private theorem moment_12604_2649_join116 :
    blockEstimate 12604 2649 14169 3733 = 46842519098688 :=
  block_append moment_12604_2649_join101 moment_12604_2649_join115 rfl rfl rfl
private theorem moment_12604_2649_join117 :
    blockEstimate 12604 2649 10329 7573 = 290243630405849 :=
  block_append moment_12604_2649_join87 moment_12604_2649_join116 rfl rfl rfl
private theorem moment_12604_2649_join118 :
    blockEstimate 12604 2649 2649 15253 = 675999454048899 :=
  block_append moment_12604_2649_join58 moment_12604_2649_join117 rfl rfl rfl

theorem moment_12604_2649 : momentEstimate 12604 2649 = 675999454048899 := moment_12604_2649_join118

private theorem receipt_0_16_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 0 128 = 890430599907289168407962619264 := by decide +kernel
private theorem receipt_0_16_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 128 128 = 835547081385767067836854095232 := by decide +kernel
private theorem receipt_0_16_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 256 128 = 781872282714501710660417424768 := by decide +kernel
private theorem receipt_0_16_2359_0_part3 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 384 128 = 729392616625836201600098848128 := by decide +kernel
private theorem receipt_0_16_2359_0_part4 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 512 128 = 678094512034418060466223680896 := by decide +kernel
private theorem receipt_0_16_2359_0_part5 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 640 128 = 627964414030915996990372695424 := by decide +kernel
private theorem receipt_0_16_2359_0_part6 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 768 128 = 578988783875736685657758502272 := by decide +kernel
private theorem receipt_0_16_2359_0_part7 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 896 128 = 531154098992741540539601931648 := by decide +kernel
private theorem receipt_0_16_2359_0_part8 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 1024 128 = 484446852962963490125508414848 := by decide +kernel
private theorem receipt_0_16_2359_0_part9 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 1152 128 = 438853555518323752155844365696 := by decide +kernel
private theorem receipt_0_16_2359_0_part10 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 1280 128 = 394360732535348608454113561984 := by decide +kernel
private theorem receipt_0_16_2359_0_part11 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 1408 128 = 350954926028886179759333526912 := by decide +kernel
private theorem receipt_0_16_2359_0_part12 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 1536 128 = 308622694145823200558411910528 := by decide +kernel
private theorem receipt_0_16_2359_0_part13 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 1664 128 = 267350611415566653688706457128 := by decide +kernel
private theorem receipt_0_16_2359_0_part14 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 1792 128 = 227125297187035098305984360974 := by decide +kernel
private theorem receipt_0_16_2359_0_part15 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 1920 128 = 187933391698509201911520680409 := by decide +kernel
private theorem receipt_0_16_2359_0_part16 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 2048 128 = 149761479878115718522323081150 := by decide +kernel
private theorem receipt_0_16_2359_0_part17 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 2176 128 = 112596155348869341721547323760 := by decide +kernel
private theorem receipt_0_16_2359_0_part18 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 2304 128 = 76424027948308901100361868538 := by decide +kernel
private theorem receipt_0_16_2359_0_part19 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 2432 128 = 41231723605708184319769151296 := by decide +kernel
private theorem receipt_0_16_2359_0_part20 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 2560 90 = 8441436918027540619877858322 := by decide +kernel
private theorem receipt_0_16_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 0 256 = 1725977681293056236244816714496 :=
  phaseBlock_append receipt_0_16_2359_0_part0 receipt_0_16_2359_0_part1 rfl rfl rfl
private theorem receipt_0_16_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 384 256 = 1407487128660254262066322529024 :=
  phaseBlock_append receipt_0_16_2359_0_part3 receipt_0_16_2359_0_part4 rfl rfl rfl
private theorem receipt_0_16_2359_0_join2 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 256 384 = 2189359411374755972726739953792 :=
  phaseBlock_append receipt_0_16_2359_0_part2 receipt_0_16_2359_0_join1 rfl rfl rfl
private theorem receipt_0_16_2359_0_join3 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 0 640 = 3915337092667812208971556668288 :=
  phaseBlock_append receipt_0_16_2359_0_join0 receipt_0_16_2359_0_join2 rfl rfl rfl
private theorem receipt_0_16_2359_0_join4 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 640 256 = 1206953197906652682648131197696 :=
  phaseBlock_append receipt_0_16_2359_0_part5 receipt_0_16_2359_0_part6 rfl rfl rfl
private theorem receipt_0_16_2359_0_join5 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 1024 256 = 923300408481287242281352780544 :=
  phaseBlock_append receipt_0_16_2359_0_part8 receipt_0_16_2359_0_part9 rfl rfl rfl
private theorem receipt_0_16_2359_0_join6 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 896 384 = 1454454507474028782820954712192 :=
  phaseBlock_append receipt_0_16_2359_0_part7 receipt_0_16_2359_0_join5 rfl rfl rfl
private theorem receipt_0_16_2359_0_join7 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 640 640 = 2661407705380681465469085909888 :=
  phaseBlock_append receipt_0_16_2359_0_join4 receipt_0_16_2359_0_join6 rfl rfl rfl
private theorem receipt_0_16_2359_0_join8 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 0 1280 = 6576744798048493674440642578176 :=
  phaseBlock_append receipt_0_16_2359_0_join3 receipt_0_16_2359_0_join7 rfl rfl rfl
private theorem receipt_0_16_2359_0_join9 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 1280 256 = 745315658564234788213447088896 :=
  phaseBlock_append receipt_0_16_2359_0_part10 receipt_0_16_2359_0_part11 rfl rfl rfl
private theorem receipt_0_16_2359_0_join10 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 1664 256 = 494475908602601751994690818102 :=
  phaseBlock_append receipt_0_16_2359_0_part13 receipt_0_16_2359_0_part14 rfl rfl rfl
private theorem receipt_0_16_2359_0_join11 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 1536 384 = 803098602748424952553102728630 :=
  phaseBlock_append receipt_0_16_2359_0_part12 receipt_0_16_2359_0_join10 rfl rfl rfl
private theorem receipt_0_16_2359_0_join12 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 1280 640 = 1548414261312659740766549817526 :=
  phaseBlock_append receipt_0_16_2359_0_join9 receipt_0_16_2359_0_join11 rfl rfl rfl
private theorem receipt_0_16_2359_0_join13 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 2048 256 = 262357635226985060243870404910 :=
  phaseBlock_append receipt_0_16_2359_0_part16 receipt_0_16_2359_0_part17 rfl rfl rfl
private theorem receipt_0_16_2359_0_join14 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 1920 384 = 450291026925494262155391085319 :=
  phaseBlock_append receipt_0_16_2359_0_part15 receipt_0_16_2359_0_join13 rfl rfl rfl
private theorem receipt_0_16_2359_0_join15 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 2432 218 = 49673160523735724939647009618 :=
  phaseBlock_append receipt_0_16_2359_0_part19 receipt_0_16_2359_0_part20 rfl rfl rfl
private theorem receipt_0_16_2359_0_join16 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 2304 346 = 126097188472044626040008878156 :=
  phaseBlock_append receipt_0_16_2359_0_part18 receipt_0_16_2359_0_join15 rfl rfl rfl
private theorem receipt_0_16_2359_0_join17 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 1920 730 = 576388215397538888195399963475 :=
  phaseBlock_append receipt_0_16_2359_0_join14 receipt_0_16_2359_0_join16 rfl rfl rfl
private theorem receipt_0_16_2359_0_join18 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 1280 1370 = 2124802476710198628961949781001 :=
  phaseBlock_append receipt_0_16_2359_0_join12 receipt_0_16_2359_0_join17 rfl rfl rfl
private theorem receipt_0_16_2359_0_join19 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 0) 0 2650 = 8701547274758692303402592359177 :=
  phaseBlock_append receipt_0_16_2359_0_join8 receipt_0_16_2359_0_join18 rfl rfl rfl

private theorem receipt_0_16_2359_0 : fastPhase (bank 0 16).shape 179818 2359 103 1 0 1 0 = 8701547274758692303402592359177 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_0_16_2359_0_join19

private theorem receipt_0_16_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 0 128 = 890002814953699666055256490688 := by decide +kernel
private theorem receipt_0_16_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 128 128 = 835128476866782196741455635136 := by decide +kernel
private theorem receipt_0_16_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 256 128 = 781462755832171852924825273024 := by decide +kernel
private theorem receipt_0_16_2359_1_part3 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 384 128 = 728992064705549849455760417472 := by decide +kernel
private theorem receipt_0_16_2359_1_part4 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 512 128 = 677702832524853701232386818752 := by decide +kernel
private theorem receipt_0_16_2359_1_part5 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 640 128 = 627581504503993998032937345728 := by decide +kernel
private theorem receipt_0_16_2359_1_part6 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 768 128 = 578614542026571179348128367296 := by decide +kernel
private theorem receipt_0_16_2359_1_part7 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 896 128 = 530788422639592309213536133824 := by decide +kernel
private theorem receipt_0_16_2359_1_part8 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 1024 128 = 484089640047187851041973158592 := by decide +kernel
private theorem receipt_0_16_2359_1_part9 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 1152 128 = 438504704104328442455864599232 := by decide +kernel
private theorem receipt_0_16_2359_1_part10 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 1280 128 = 394020140810541670119624639168 := by decide +kernel
private theorem receipt_0_16_2359_1_part11 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 1408 128 = 350622492303628844572032869056 := by decide +kernel
private theorem receipt_0_16_2359_1_part12 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 1536 128 = 308298316853381775058610668224 := by decide +kernel
private theorem receipt_0_16_2359_1_part13 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 1664 128 = 267034189111764145873317412452 := by decide +kernel
private theorem receipt_0_16_2359_1_part14 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 1792 128 = 226816728512657510061541015610 := by decide +kernel
private theorem receipt_0_16_2359_1_part15 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 1920 128 = 187632575345460028342463162115 := by decide +kernel
private theorem receipt_0_16_2359_1_part16 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 2048 128 = 149468314653512652673237409300 := by decide +kernel
private theorem receipt_0_16_2359_1_part17 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 2176 128 = 112310540182774587146680485300 := by decide +kernel
private theorem receipt_0_16_2359_1_part18 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 2304 128 = 76145861893551918981732530408 := by decide +kernel
private theorem receipt_0_16_2359_1_part19 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 2432 128 = 40960905837913834177712095276 := by decide +kernel
private theorem receipt_0_16_2359_1_part20 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 2560 90 = 8255363664047686212692549114 := by decide +kernel
private theorem receipt_0_16_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 0 256 = 1725131291820481862796712125824 :=
  phaseBlock_append receipt_0_16_2359_1_part0 receipt_0_16_2359_1_part1 rfl rfl rfl
private theorem receipt_0_16_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 384 256 = 1406694897230403550688147236224 :=
  phaseBlock_append receipt_0_16_2359_1_part3 receipt_0_16_2359_1_part4 rfl rfl rfl
private theorem receipt_0_16_2359_1_join2 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 256 384 = 2188157653062575403612972509248 :=
  phaseBlock_append receipt_0_16_2359_1_part2 receipt_0_16_2359_1_join1 rfl rfl rfl
private theorem receipt_0_16_2359_1_join3 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 0 640 = 3913288944883057266409684635072 :=
  phaseBlock_append receipt_0_16_2359_1_join0 receipt_0_16_2359_1_join2 rfl rfl rfl
private theorem receipt_0_16_2359_1_join4 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 640 256 = 1206196046530565177381065713024 :=
  phaseBlock_append receipt_0_16_2359_1_part5 receipt_0_16_2359_1_part6 rfl rfl rfl
private theorem receipt_0_16_2359_1_join5 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 1024 256 = 922594344151516293497837757824 :=
  phaseBlock_append receipt_0_16_2359_1_part8 receipt_0_16_2359_1_part9 rfl rfl rfl
private theorem receipt_0_16_2359_1_join6 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 896 384 = 1453382766791108602711373891648 :=
  phaseBlock_append receipt_0_16_2359_1_part7 receipt_0_16_2359_1_join5 rfl rfl rfl
private theorem receipt_0_16_2359_1_join7 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 640 640 = 2659578813321673780092439604672 :=
  phaseBlock_append receipt_0_16_2359_1_join4 receipt_0_16_2359_1_join6 rfl rfl rfl
private theorem receipt_0_16_2359_1_join8 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 0 1280 = 6572867758204731046502124239744 :=
  phaseBlock_append receipt_0_16_2359_1_join3 receipt_0_16_2359_1_join7 rfl rfl rfl
private theorem receipt_0_16_2359_1_join9 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 1280 256 = 744642633114170514691657508224 :=
  phaseBlock_append receipt_0_16_2359_1_part10 receipt_0_16_2359_1_part11 rfl rfl rfl
private theorem receipt_0_16_2359_1_join10 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 1664 256 = 493850917624421655934858428062 :=
  phaseBlock_append receipt_0_16_2359_1_part13 receipt_0_16_2359_1_part14 rfl rfl rfl
private theorem receipt_0_16_2359_1_join11 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 1536 384 = 802149234477803430993469096286 :=
  phaseBlock_append receipt_0_16_2359_1_part12 receipt_0_16_2359_1_join10 rfl rfl rfl
private theorem receipt_0_16_2359_1_join12 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 1280 640 = 1546791867591973945685126604510 :=
  phaseBlock_append receipt_0_16_2359_1_join9 receipt_0_16_2359_1_join11 rfl rfl rfl
private theorem receipt_0_16_2359_1_join13 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 2048 256 = 261778854836287239819917894600 :=
  phaseBlock_append receipt_0_16_2359_1_part16 receipt_0_16_2359_1_part17 rfl rfl rfl
private theorem receipt_0_16_2359_1_join14 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 1920 384 = 449411430181747268162381056715 :=
  phaseBlock_append receipt_0_16_2359_1_part15 receipt_0_16_2359_1_join13 rfl rfl rfl
private theorem receipt_0_16_2359_1_join15 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 2432 218 = 49216269501961520390404644390 :=
  phaseBlock_append receipt_0_16_2359_1_part19 receipt_0_16_2359_1_part20 rfl rfl rfl
private theorem receipt_0_16_2359_1_join16 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 2304 346 = 125362131395513439372137174798 :=
  phaseBlock_append receipt_0_16_2359_1_part18 receipt_0_16_2359_1_join15 rfl rfl rfl
private theorem receipt_0_16_2359_1_join17 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 1920 730 = 574773561577260707534518231513 :=
  phaseBlock_append receipt_0_16_2359_1_join14 receipt_0_16_2359_1_join16 rfl rfl rfl
private theorem receipt_0_16_2359_1_join18 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 1280 1370 = 2121565429169234653219644836023 :=
  phaseBlock_append receipt_0_16_2359_1_join12 receipt_0_16_2359_1_join17 rfl rfl rfl
private theorem receipt_0_16_2359_1_join19 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2359 103 1 0 1 1) 0 2650 = 8694433187373965699721769075767 :=
  phaseBlock_append receipt_0_16_2359_1_join8 receipt_0_16_2359_1_join18 rfl rfl rfl

private theorem receipt_0_16_2359_1 : fastPhase (bank 0 16).shape 179818 2359 103 1 0 1 1 = 8694433187373965699721769075767 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_0_16_2359_1_join19

private theorem receipt_0_16_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 0 128 = 890438622473909581785025879584 := by decide +kernel
private theorem receipt_0_16_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 128 128 = 835554407453667559494793735712 := by decide +kernel
private theorem receipt_0_16_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 256 128 = 781878946300258268636252683808 := by decide +kernel
private theorem receipt_0_16_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 384 128 = 729398651277832947095633645088 := by decide +kernel
private theorem receipt_0_16_2360_0_part4 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 512 128 = 678099950833411329095853694496 := by decide +kernel
private theorem receipt_0_16_2360_0_part5 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 640 128 = 627969289590598200126566886944 := by decide +kernel
private theorem receipt_0_16_2360_0_part6 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 768 128 = 578993128343299951874215083552 := by decide +kernel
private theorem receipt_0_16_2360_0_part7 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 896 128 = 531157944049441137152078777888 := by decide +kernel
private theorem receipt_0_16_2360_0_part8 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 1024 128 = 484450229824681024830327922208 := by decide +kernel
private theorem receipt_0_16_2360_0_part9 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 1152 128 = 438856494936130154766072753696 := by decide +kernel
private theorem receipt_0_16_2360_0_part10 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 1280 128 = 394363264796066892733414620704 := by decide +kernel
private theorem receipt_0_16_2360_0_part11 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 1408 128 = 350957080955653985353496808992 := by decide +kernel
private theorem receipt_0_16_2360_0_part12 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 1536 128 = 308624501098655115024555367968 := by decide +kernel
private theorem receipt_0_16_2360_0_part13 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 1664 128 = 267352099245334605457988269208 := by decide +kernel
private theorem receipt_0_16_2360_0_part14 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 1792 128 = 227126493432122198584658238660 := by decide +kernel
private theorem receipt_0_16_2360_0_part15 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 1920 128 = 187934324375689286234476427166 := by decide +kernel
private theorem receipt_0_16_2360_0_part16 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 2048 128 = 149762176953923985939143110112 := by decide +kernel
private theorem receipt_0_16_2360_0_part17 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 2176 128 = 112596644309600213326083380545 := by decide +kernel
private theorem receipt_0_16_2360_0_part18 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 2304 128 = 76424335773624414968004036972 := by decide +kernel
private theorem receipt_0_16_2360_0_part19 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 2432 128 = 41231876773549734857316928137 := by decide +kernel
private theorem receipt_0_16_2360_0_part20 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 2560 90 = 8441466051458847636935327846 := by decide +kernel
private theorem receipt_0_16_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 0 256 = 1725993029927577141279819615296 :=
  phaseBlock_append receipt_0_16_2360_0_part0 receipt_0_16_2360_0_part1 rfl rfl rfl
private theorem receipt_0_16_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 384 256 = 1407498602111244276191487339584 :=
  phaseBlock_append receipt_0_16_2360_0_part3 receipt_0_16_2360_0_part4 rfl rfl rfl
private theorem receipt_0_16_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 256 384 = 2189377548411502544827740023392 :=
  phaseBlock_append receipt_0_16_2360_0_part2 receipt_0_16_2360_0_join1 rfl rfl rfl
private theorem receipt_0_16_2360_0_join3 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 0 640 = 3915370578339079686107559638688 :=
  phaseBlock_append receipt_0_16_2360_0_join0 receipt_0_16_2360_0_join2 rfl rfl rfl
private theorem receipt_0_16_2360_0_join4 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 640 256 = 1206962417933898152000781970496 :=
  phaseBlock_append receipt_0_16_2360_0_part5 receipt_0_16_2360_0_part6 rfl rfl rfl
private theorem receipt_0_16_2360_0_join5 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 1024 256 = 923306724760811179596400675904 :=
  phaseBlock_append receipt_0_16_2360_0_part8 receipt_0_16_2360_0_part9 rfl rfl rfl
private theorem receipt_0_16_2360_0_join6 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 896 384 = 1454464668810252316748479453792 :=
  phaseBlock_append receipt_0_16_2360_0_part7 receipt_0_16_2360_0_join5 rfl rfl rfl
private theorem receipt_0_16_2360_0_join7 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 640 640 = 2661427086744150468749261424288 :=
  phaseBlock_append receipt_0_16_2360_0_join4 receipt_0_16_2360_0_join6 rfl rfl rfl
private theorem receipt_0_16_2360_0_join8 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 0 1280 = 6576797665083230154856821062976 :=
  phaseBlock_append receipt_0_16_2360_0_join3 receipt_0_16_2360_0_join7 rfl rfl rfl
private theorem receipt_0_16_2360_0_join9 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 1280 256 = 745320345751720878086911429696 :=
  phaseBlock_append receipt_0_16_2360_0_part10 receipt_0_16_2360_0_part11 rfl rfl rfl
private theorem receipt_0_16_2360_0_join10 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 1664 256 = 494478592677456804042646507868 :=
  phaseBlock_append receipt_0_16_2360_0_part13 receipt_0_16_2360_0_part14 rfl rfl rfl
private theorem receipt_0_16_2360_0_join11 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 1536 384 = 803103093776111919067201875836 :=
  phaseBlock_append receipt_0_16_2360_0_part12 receipt_0_16_2360_0_join10 rfl rfl rfl
private theorem receipt_0_16_2360_0_join12 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 1280 640 = 1548423439527832797154113305532 :=
  phaseBlock_append receipt_0_16_2360_0_join9 receipt_0_16_2360_0_join11 rfl rfl rfl
private theorem receipt_0_16_2360_0_join13 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 2048 256 = 262358821263524199265226490657 :=
  phaseBlock_append receipt_0_16_2360_0_part16 receipt_0_16_2360_0_part17 rfl rfl rfl
private theorem receipt_0_16_2360_0_join14 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 1920 384 = 450293145639213485499702917823 :=
  phaseBlock_append receipt_0_16_2360_0_part15 receipt_0_16_2360_0_join13 rfl rfl rfl
private theorem receipt_0_16_2360_0_join15 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 2432 218 = 49673342825008582494252255983 :=
  phaseBlock_append receipt_0_16_2360_0_part19 receipt_0_16_2360_0_part20 rfl rfl rfl
private theorem receipt_0_16_2360_0_join16 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 2304 346 = 126097678598632997462256292955 :=
  phaseBlock_append receipt_0_16_2360_0_part18 receipt_0_16_2360_0_join15 rfl rfl rfl
private theorem receipt_0_16_2360_0_join17 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 1920 730 = 576390824237846482961959210778 :=
  phaseBlock_append receipt_0_16_2360_0_join14 receipt_0_16_2360_0_join16 rfl rfl rfl
private theorem receipt_0_16_2360_0_join18 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 1280 1370 = 2124814263765679280116072516310 :=
  phaseBlock_append receipt_0_16_2360_0_join12 receipt_0_16_2360_0_join17 rfl rfl rfl
private theorem receipt_0_16_2360_0_join19 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 0) 0 2650 = 8701611928848909434972893579286 :=
  phaseBlock_append receipt_0_16_2360_0_join8 receipt_0_16_2360_0_join18 rfl rfl rfl

private theorem receipt_0_16_2360_0 : fastPhase (bank 0 16).shape 179818 2360 103 1 0 1 0 = 8701611928848909434972893579286 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_0_16_2360_0_join19

private theorem receipt_0_16_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 0 128 = 890010834367332891099420607648 := by decide +kernel
private theorem receipt_0_16_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 128 128 = 835135799915568921062833476768 := by decide +kernel
private theorem receipt_0_16_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 256 128 = 781469416530475908969954272416 := by decide +kernel
private theorem receipt_0_16_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 384 128 = 728998096599546292007833334944 := by decide +kernel
private theorem receipt_0_16_2360_1_part4 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 512 128 = 677708268693092887353388762272 := by decide +kernel
private theorem receipt_0_16_2360_1_part5 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 640 128 = 627586377557965447103457236128 := by decide +kernel
private theorem receipt_0_16_2360_1_part6 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 768 128 = 578618884111267213204844848288 := by decide +kernel
private theorem receipt_0_16_2360_1_part7 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 896 128 = 530792265434071472384377926816 := by decide +kernel
private theorem receipt_0_16_2360_1_part8 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 1024 128 = 484093014765138111078953862304 := by decide +kernel
private theorem receipt_0_16_2360_1_part9 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 1152 128 = 438507641494630170365591934112 := by decide +kernel
private theorem receipt_0_16_2360_1_part10 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 1280 128 = 394022671157830400891484136608 := by decide +kernel
private theorem receipt_0_16_2360_1_part11 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 1408 128 = 350624645428857817804046005408 := by decide +kernel
private theorem receipt_0_16_2360_1_part12 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 1536 128 = 308300122114384255680967443616 := by decide +kernel
private theorem receipt_0_16_2360_1_part13 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 1664 128 = 267035675357287887153377208336 := by decide +kernel
private theorem receipt_0_16_2360_1_part14 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 1792 128 = 226817923280074793684166704971 := by decide +kernel
private theorem receipt_0_16_2360_1_part15 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 1920 128 = 187633506649749469474167645202 := by decide +kernel
private theorem receipt_0_16_2360_1_part16 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 2048 128 = 149469010458954893262825537848 := by decide +kernel
private theorem receipt_0_16_2360_1_part17 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 2176 128 = 112311027973383902655678216958 := by decide +kernel
private theorem receipt_0_16_2360_1_part18 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 2304 128 = 76146168646720712314095744339 := by decide +kernel
private theorem receipt_0_16_2360_1_part19 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 2432 128 = 40961058029332093889909132467 := by decide +kernel
private theorem receipt_0_16_2360_1_part20 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 2560 90 = 8255392167024551924932340364 := by decide +kernel
private theorem receipt_0_16_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 0 256 = 1725146634282901812162254084416 :=
  phaseBlock_append receipt_0_16_2360_1_part0 receipt_0_16_2360_1_part1 rfl rfl rfl
private theorem receipt_0_16_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 384 256 = 1406706365292639179361222097216 :=
  phaseBlock_append receipt_0_16_2360_1_part3 receipt_0_16_2360_1_part4 rfl rfl rfl
private theorem receipt_0_16_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 256 384 = 2188175781823115088331176369632 :=
  phaseBlock_append receipt_0_16_2360_1_part2 receipt_0_16_2360_1_join1 rfl rfl rfl
private theorem receipt_0_16_2360_1_join3 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 0 640 = 3913322416106016900493430454048 :=
  phaseBlock_append receipt_0_16_2360_1_join0 receipt_0_16_2360_1_join2 rfl rfl rfl
private theorem receipt_0_16_2360_1_join4 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 640 256 = 1206205261669232660308302084416 :=
  phaseBlock_append receipt_0_16_2360_1_part5 receipt_0_16_2360_1_part6 rfl rfl rfl
private theorem receipt_0_16_2360_1_join5 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 1024 256 = 922600656259768281444545796416 :=
  phaseBlock_append receipt_0_16_2360_1_part8 receipt_0_16_2360_1_part9 rfl rfl rfl
private theorem receipt_0_16_2360_1_join6 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 896 384 = 1453392921693839753828923723232 :=
  phaseBlock_append receipt_0_16_2360_1_part7 receipt_0_16_2360_1_join5 rfl rfl rfl
private theorem receipt_0_16_2360_1_join7 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 640 640 = 2659598183363072414137225807648 :=
  phaseBlock_append receipt_0_16_2360_1_join4 receipt_0_16_2360_1_join6 rfl rfl rfl
private theorem receipt_0_16_2360_1_join8 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 0 1280 = 6572920599469089314630656261696 :=
  phaseBlock_append receipt_0_16_2360_1_join3 receipt_0_16_2360_1_join7 rfl rfl rfl
private theorem receipt_0_16_2360_1_join9 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 1280 256 = 744647316586688218695530142016 :=
  phaseBlock_append receipt_0_16_2360_1_part10 receipt_0_16_2360_1_part11 rfl rfl rfl
private theorem receipt_0_16_2360_1_join10 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 1664 256 = 493853598637362680837543913307 :=
  phaseBlock_append receipt_0_16_2360_1_part13 receipt_0_16_2360_1_part14 rfl rfl rfl
private theorem receipt_0_16_2360_1_join11 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 1536 384 = 802153720751746936518511356923 :=
  phaseBlock_append receipt_0_16_2360_1_part12 receipt_0_16_2360_1_join10 rfl rfl rfl
private theorem receipt_0_16_2360_1_join12 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 1280 640 = 1546801037338435155214041498939 :=
  phaseBlock_append receipt_0_16_2360_1_join9 receipt_0_16_2360_1_join11 rfl rfl rfl
private theorem receipt_0_16_2360_1_join13 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 2048 256 = 261780038432338795918503754806 :=
  phaseBlock_append receipt_0_16_2360_1_part16 receipt_0_16_2360_1_part17 rfl rfl rfl
private theorem receipt_0_16_2360_1_join14 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 1920 384 = 449413545082088265392671400008 :=
  phaseBlock_append receipt_0_16_2360_1_part15 receipt_0_16_2360_1_join13 rfl rfl rfl
private theorem receipt_0_16_2360_1_join15 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 2432 218 = 49216450196356645814841472831 :=
  phaseBlock_append receipt_0_16_2360_1_part19 receipt_0_16_2360_1_part20 rfl rfl rfl
private theorem receipt_0_16_2360_1_join16 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 2304 346 = 125362618843077358128937217170 :=
  phaseBlock_append receipt_0_16_2360_1_part18 receipt_0_16_2360_1_join15 rfl rfl rfl
private theorem receipt_0_16_2360_1_join17 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 1920 730 = 574776163925165623521608617178 :=
  phaseBlock_append receipt_0_16_2360_1_join14 receipt_0_16_2360_1_join16 rfl rfl rfl
private theorem receipt_0_16_2360_1_join18 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 1280 1370 = 2121577201263600778735650116117 :=
  phaseBlock_append receipt_0_16_2360_1_join12 receipt_0_16_2360_1_join17 rfl rfl rfl
private theorem receipt_0_16_2360_1_join19 :
    phaseBlock (fastLayer (bank 0 16).shape 179818 2360 103 1 0 1 1) 0 2650 = 8694497800732690093366306377813 :=
  phaseBlock_append receipt_0_16_2360_1_join8 receipt_0_16_2360_1_join18 rfl rfl rfl

private theorem receipt_0_16_2360_1 : fastPhase (bank 0 16).shape 179818 2360 103 1 0 1 1 = 8694497800732690093366306377813 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_0_16_2360_1_join19

theorem receipt_0_16 : Checked (bank 0 16) 103 0 1 := by
  refine checked_from_values (bank 0 16) 103 0 1
    (P3_7_1.checked (bank 0 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_12604_2649)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_16_2359_0 receipt_0_16_2359_1 receipt_0_16_2360_0 receipt_0_16_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_16_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 0 128 = 801680815459664894687637863424 := by decide +kernel
private theorem receipt_1_16_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 128 128 = 752003090952645843156265237504 := by decide +kernel
private theorem receipt_1_16_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 256 128 = 703447563307302820759795006464 := by decide +kernel
private theorem receipt_1_16_2359_0_part3 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 384 128 = 656000871430339427658002955264 := by decide +kernel
private theorem receipt_1_16_2359_0_part4 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 512 128 = 609649685665792387847301168128 := by decide +kernel
private theorem receipt_1_16_2359_0_part5 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 640 128 = 564380707769898648490243554304 := by decide +kernel
private theorem receipt_1_16_2359_0_part6 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 768 128 = 520180670885962479245031373824 := by decide +kernel
private theorem receipt_1_16_2359_0_part7 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 896 128 = 477036339519222571595018763264 := by decide +kernel
private theorem receipt_1_16_2359_0_part8 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 1024 128 = 434934509511719138178218261504 := by decide +kernel
private theorem receipt_1_16_2359_0_part9 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 1152 128 = 393862008017161012116806335488 := by decide +kernel
private theorem receipt_1_16_2359_0_part10 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 1280 128 = 353805693475792746346628905984 := by decide +kernel
private theorem receipt_1_16_2359_0_part11 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 1408 128 = 314752455589261712946706873344 := by decide +kernel
private theorem receipt_1_16_2359_0_part12 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 1536 128 = 276689215295485202468741643264 := by decide +kernel
private theorem receipt_1_16_2359_0_part13 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 1664 128 = 239602924973595813573742878239 := by decide +kernel
private theorem receipt_1_16_2359_0_part14 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 1792 128 = 203480593898930069744590524292 := by decide +kernel
private theorem receipt_1_16_2359_0_part15 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 1920 128 = 168309266752081805698955542929 := by decide +kernel
private theorem receipt_1_16_2359_0_part16 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 2048 128 = 134075955368631046305401720568 := by decide +kernel
private theorem receipt_1_16_2359_0_part17 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 2176 128 = 100767696114142756018244672045 := by decide +kernel
private theorem receipt_1_16_2359_0_part18 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 2304 128 = 68371556604404976680880657168 := by decide +kernel
private theorem receipt_1_16_2359_0_part19 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 2432 128 = 36874635575932383735943308568 := by decide +kernel
private theorem receipt_1_16_2359_0_part20 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 2560 90 = 7547244980172902832603864426 := by decide +kernel
private theorem receipt_1_16_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 0 256 = 1553683906412310737843903100928 :=
  phaseBlock_append receipt_1_16_2359_0_part0 receipt_1_16_2359_0_part1 rfl rfl rfl
private theorem receipt_1_16_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 384 256 = 1265650557096131815505304123392 :=
  phaseBlock_append receipt_1_16_2359_0_part3 receipt_1_16_2359_0_part4 rfl rfl rfl
private theorem receipt_1_16_2359_0_join2 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 256 384 = 1969098120403434636265099129856 :=
  phaseBlock_append receipt_1_16_2359_0_part2 receipt_1_16_2359_0_join1 rfl rfl rfl
private theorem receipt_1_16_2359_0_join3 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 0 640 = 3522782026815745374109002230784 :=
  phaseBlock_append receipt_1_16_2359_0_join0 receipt_1_16_2359_0_join2 rfl rfl rfl
private theorem receipt_1_16_2359_0_join4 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 640 256 = 1084561378655861127735274928128 :=
  phaseBlock_append receipt_1_16_2359_0_part5 receipt_1_16_2359_0_part6 rfl rfl rfl
private theorem receipt_1_16_2359_0_join5 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 1024 256 = 828796517528880150295024596992 :=
  phaseBlock_append receipt_1_16_2359_0_part8 receipt_1_16_2359_0_part9 rfl rfl rfl
private theorem receipt_1_16_2359_0_join6 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 896 384 = 1305832857048102721890043360256 :=
  phaseBlock_append receipt_1_16_2359_0_part7 receipt_1_16_2359_0_join5 rfl rfl rfl
private theorem receipt_1_16_2359_0_join7 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 640 640 = 2390394235703963849625318288384 :=
  phaseBlock_append receipt_1_16_2359_0_join4 receipt_1_16_2359_0_join6 rfl rfl rfl
private theorem receipt_1_16_2359_0_join8 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 0 1280 = 5913176262519709223734320519168 :=
  phaseBlock_append receipt_1_16_2359_0_join3 receipt_1_16_2359_0_join7 rfl rfl rfl
private theorem receipt_1_16_2359_0_join9 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 1280 256 = 668558149065054459293335779328 :=
  phaseBlock_append receipt_1_16_2359_0_part10 receipt_1_16_2359_0_part11 rfl rfl rfl
private theorem receipt_1_16_2359_0_join10 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 1664 256 = 443083518872525883318333402531 :=
  phaseBlock_append receipt_1_16_2359_0_part13 receipt_1_16_2359_0_part14 rfl rfl rfl
private theorem receipt_1_16_2359_0_join11 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 1536 384 = 719772734168011085787075045795 :=
  phaseBlock_append receipt_1_16_2359_0_part12 receipt_1_16_2359_0_join10 rfl rfl rfl
private theorem receipt_1_16_2359_0_join12 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 1280 640 = 1388330883233065545080410825123 :=
  phaseBlock_append receipt_1_16_2359_0_join9 receipt_1_16_2359_0_join11 rfl rfl rfl
private theorem receipt_1_16_2359_0_join13 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 2048 256 = 234843651482773802323646392613 :=
  phaseBlock_append receipt_1_16_2359_0_part16 receipt_1_16_2359_0_part17 rfl rfl rfl
private theorem receipt_1_16_2359_0_join14 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 1920 384 = 403152918234855608022601935542 :=
  phaseBlock_append receipt_1_16_2359_0_part15 receipt_1_16_2359_0_join13 rfl rfl rfl
private theorem receipt_1_16_2359_0_join15 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 2432 218 = 44421880556105286568547172994 :=
  phaseBlock_append receipt_1_16_2359_0_part19 receipt_1_16_2359_0_part20 rfl rfl rfl
private theorem receipt_1_16_2359_0_join16 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 2304 346 = 112793437160510263249427830162 :=
  phaseBlock_append receipt_1_16_2359_0_part18 receipt_1_16_2359_0_join15 rfl rfl rfl
private theorem receipt_1_16_2359_0_join17 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 1920 730 = 515946355395365871272029765704 :=
  phaseBlock_append receipt_1_16_2359_0_join14 receipt_1_16_2359_0_join16 rfl rfl rfl
private theorem receipt_1_16_2359_0_join18 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 1280 1370 = 1904277238628431416352440590827 :=
  phaseBlock_append receipt_1_16_2359_0_join12 receipt_1_16_2359_0_join17 rfl rfl rfl
private theorem receipt_1_16_2359_0_join19 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 0) 0 2650 = 7817453501148140640086761109995 :=
  phaseBlock_append receipt_1_16_2359_0_join8 receipt_1_16_2359_0_join18 rfl rfl rfl

private theorem receipt_1_16_2359_0 : fastPhase (bank 1 16).shape 179818 2359 103 1 0 2 0 = 7817453501148140640086761109995 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_1_16_2359_0_join19

private theorem receipt_1_16_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 0 128 = 801293467309651581425129102912 := by decide +kernel
private theorem receipt_1_16_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 128 128 = 751624276166907826302134419008 := by decide +kernel
private theorem receipt_1_16_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 256 128 = 703077180652603911065749741120 := by decide +kernel
private theorem receipt_1_16_2359_1_part3 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 384 128 = 655638819913145089028172758592 := by decide +kernel
private theorem receipt_1_16_2359_1_part4 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 512 128 = 609295864532077277173644107328 := by decide +kernel
private theorem receipt_1_16_2359_1_part5 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 640 128 = 564035016504954155487952895552 := by decide +kernel
private theorem receipt_1_16_2359_1_part6 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 768 128 = 519843009214204266287942229568 := by decide +kernel
private theorem receipt_1_16_2359_1_part7 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 896 128 = 476706607403998113551014739520 := by decide +kernel
private theorem receipt_1_16_2359_1_part8 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 1024 128 = 434612607155115262244638105152 := by decide +kernel
private theorem receipt_1_16_2359_1_part9 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 1152 128 = 393547835859811437655850581568 := by decide +kernel
private theorem receipt_1_16_2359_1_part10 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 1280 128 = 353499152196685624720766524992 := by decide +kernel
private theorem receipt_1_16_2359_1_part11 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 1408 128 = 314453446105547167354081918528 := by decide +kernel
private theorem receipt_1_16_2359_1_part12 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 1536 128 = 276397638762282867778579897920 := by decide +kernel
private theorem receipt_1_16_2359_1_part13 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 1664 128 = 239318682783532689378480954987 := by decide +kernel
private theorem receipt_1_16_2359_1_part14 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 1792 128 = 203203587648242839300685620916 := by decide +kernel
private theorem receipt_1_16_2359_1_part15 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 1920 128 = 168039398210188808164772453091 := by decide +kernel
private theorem receipt_1_16_2359_1_part16 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 2048 128 = 133813126535634383336597061260 := by decide +kernel
private theorem receipt_1_16_2359_1_part17 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 2176 128 = 100511809227625763369899110207 := by decide +kernel
private theorem receipt_1_16_2359_1_part18 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 2304 128 = 68122514139123678918131796062 := by decide +kernel
private theorem receipt_1_16_2359_1_part19 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 2432 128 = 36632340243691135223842516057 := by decide +kernel
private theorem receipt_1_16_2359_1_part20 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 2560 90 = 7380868584615810487093725875 := by decide +kernel
private theorem receipt_1_16_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 0 256 = 1552917743476559407727263521920 :=
  phaseBlock_append receipt_1_16_2359_1_part0 receipt_1_16_2359_1_part1 rfl rfl rfl
private theorem receipt_1_16_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 384 256 = 1264934684445222366201816865920 :=
  phaseBlock_append receipt_1_16_2359_1_part3 receipt_1_16_2359_1_part4 rfl rfl rfl
private theorem receipt_1_16_2359_1_join2 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 256 384 = 1968011865097826277267566607040 :=
  phaseBlock_append receipt_1_16_2359_1_part2 receipt_1_16_2359_1_join1 rfl rfl rfl
private theorem receipt_1_16_2359_1_join3 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 0 640 = 3520929608574385684994830128960 :=
  phaseBlock_append receipt_1_16_2359_1_join0 receipt_1_16_2359_1_join2 rfl rfl rfl
private theorem receipt_1_16_2359_1_join4 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 640 256 = 1083878025719158421775895125120 :=
  phaseBlock_append receipt_1_16_2359_1_part5 receipt_1_16_2359_1_part6 rfl rfl rfl
private theorem receipt_1_16_2359_1_join5 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 1024 256 = 828160443014926699900488686720 :=
  phaseBlock_append receipt_1_16_2359_1_part8 receipt_1_16_2359_1_part9 rfl rfl rfl
private theorem receipt_1_16_2359_1_join6 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 896 384 = 1304867050418924813451503426240 :=
  phaseBlock_append receipt_1_16_2359_1_part7 receipt_1_16_2359_1_join5 rfl rfl rfl
private theorem receipt_1_16_2359_1_join7 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 640 640 = 2388745076138083235227398551360 :=
  phaseBlock_append receipt_1_16_2359_1_join4 receipt_1_16_2359_1_join6 rfl rfl rfl
private theorem receipt_1_16_2359_1_join8 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 0 1280 = 5909674684712468920222228680320 :=
  phaseBlock_append receipt_1_16_2359_1_join3 receipt_1_16_2359_1_join7 rfl rfl rfl
private theorem receipt_1_16_2359_1_join9 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 1280 256 = 667952598302232792074848443520 :=
  phaseBlock_append receipt_1_16_2359_1_part10 receipt_1_16_2359_1_part11 rfl rfl rfl
private theorem receipt_1_16_2359_1_join10 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 1664 256 = 442522270431775528679166575903 :=
  phaseBlock_append receipt_1_16_2359_1_part13 receipt_1_16_2359_1_part14 rfl rfl rfl
private theorem receipt_1_16_2359_1_join11 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 1536 384 = 718919909194058396457746473823 :=
  phaseBlock_append receipt_1_16_2359_1_part12 receipt_1_16_2359_1_join10 rfl rfl rfl
private theorem receipt_1_16_2359_1_join12 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 1280 640 = 1386872507496291188532594917343 :=
  phaseBlock_append receipt_1_16_2359_1_join9 receipt_1_16_2359_1_join11 rfl rfl rfl
private theorem receipt_1_16_2359_1_join13 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 2048 256 = 234324935763260146706496171467 :=
  phaseBlock_append receipt_1_16_2359_1_part16 receipt_1_16_2359_1_part17 rfl rfl rfl
private theorem receipt_1_16_2359_1_join14 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 1920 384 = 402364333973448954871268624558 :=
  phaseBlock_append receipt_1_16_2359_1_part15 receipt_1_16_2359_1_join13 rfl rfl rfl
private theorem receipt_1_16_2359_1_join15 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 2432 218 = 44013208828306945710936241932 :=
  phaseBlock_append receipt_1_16_2359_1_part19 receipt_1_16_2359_1_part20 rfl rfl rfl
private theorem receipt_1_16_2359_1_join16 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 2304 346 = 112135722967430624629068037994 :=
  phaseBlock_append receipt_1_16_2359_1_part18 receipt_1_16_2359_1_join15 rfl rfl rfl
private theorem receipt_1_16_2359_1_join17 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 1920 730 = 514500056940879579500336662552 :=
  phaseBlock_append receipt_1_16_2359_1_join14 receipt_1_16_2359_1_join16 rfl rfl rfl
private theorem receipt_1_16_2359_1_join18 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 1280 1370 = 1901372564437170768032931579895 :=
  phaseBlock_append receipt_1_16_2359_1_join12 receipt_1_16_2359_1_join17 rfl rfl rfl
private theorem receipt_1_16_2359_1_join19 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2359 103 1 0 2 1) 0 2650 = 7811047249149639688255160260215 :=
  phaseBlock_append receipt_1_16_2359_1_join8 receipt_1_16_2359_1_join18 rfl rfl rfl

private theorem receipt_1_16_2359_1 : fastPhase (bank 1 16).shape 179818 2359 103 1 0 2 1 = 7811047249149639688255160260215 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_1_16_2359_1_join19

private theorem receipt_1_16_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 0 128 = 801688038417602795861078958624 := by decide +kernel
private theorem receipt_1_16_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 128 128 = 752009684513098373790910321184 := by decide +kernel
private theorem receipt_1_16_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 256 128 = 703453558515541890104139858464 := by decide +kernel
private theorem receipt_1_16_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 384 128 = 656006298878330521371964437024 := by decide +kernel
private theorem receipt_1_16_2360_0_part4 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 512 128 = 609654575493285732962348868128 := by decide +kernel
private theorem receipt_1_16_2360_0_part5 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 640 128 = 564385089665519498760229212704 := by decide +kernel
private theorem receipt_1_16_2360_0_part6 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 768 128 = 520184574088300520887716086304 := by decide +kernel
private theorem receipt_1_16_2360_0_part7 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 896 128 = 477039792817920449424297964064 := by decide +kernel
private theorem receipt_1_16_2360_0_part8 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 1024 128 = 434937541248560102127044485664 := by decide +kernel
private theorem receipt_1_16_2360_0_part9 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 1152 128 = 393864646087155684150809760288 := by decide +kernel
private theorem receipt_1_16_2360_0_part10 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 1280 128 = 353807965328265007768435671584 := by decide +kernel
private theorem receipt_1_16_2360_0_part11 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 1408 128 = 314754388228933712090955182624 := by decide +kernel
private theorem receipt_1_16_2360_0_part12 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 1536 128 = 276690835283561482787795640864 := by decide +kernel
private theorem receipt_1_16_2360_0_part13 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 1664 128 = 239604258387105944290715968286 := by decide +kernel
private theorem receipt_1_16_2360_0_part14 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 1792 128 = 203481665611661816400816719598 := by decide +kernel
private theorem receipt_1_16_2360_0_part15 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 1920 128 = 168310102040035211136659783331 := by decide +kernel
private theorem receipt_1_16_2360_0_part16 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 2048 128 = 134076579436241015951830809812 := by decide +kernel
private theorem receipt_1_16_2360_0_part17 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 2176 128 = 100768133709470423110770143650 := by decide +kernel
private theorem receipt_1_16_2360_0_part18 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 2304 128 = 68371831996127361406170173007 := by decide +kernel
private theorem receipt_1_16_2360_0_part19 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 2432 128 = 36874772558372916548686829013 := by decide +kernel
private theorem receipt_1_16_2360_0_part20 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 2560 90 = 7547271027557015868939078671 := by decide +kernel
private theorem receipt_1_16_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 0 256 = 1553697722930701169651989279808 :=
  phaseBlock_append receipt_1_16_2360_0_part0 receipt_1_16_2360_0_part1 rfl rfl rfl
private theorem receipt_1_16_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 384 256 = 1265660874371616254334313305152 :=
  phaseBlock_append receipt_1_16_2360_0_part3 receipt_1_16_2360_0_part4 rfl rfl rfl
private theorem receipt_1_16_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 256 384 = 1969114432887158144438453163616 :=
  phaseBlock_append receipt_1_16_2360_0_part2 receipt_1_16_2360_0_join1 rfl rfl rfl
private theorem receipt_1_16_2360_0_join3 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 0 640 = 3522812155817859314090442443424 :=
  phaseBlock_append receipt_1_16_2360_0_join0 receipt_1_16_2360_0_join2 rfl rfl rfl
private theorem receipt_1_16_2360_0_join4 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 640 256 = 1084569663753820019647945299008 :=
  phaseBlock_append receipt_1_16_2360_0_part5 receipt_1_16_2360_0_part6 rfl rfl rfl
private theorem receipt_1_16_2360_0_join5 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 1024 256 = 828802187335715786277854245952 :=
  phaseBlock_append receipt_1_16_2360_0_part8 receipt_1_16_2360_0_part9 rfl rfl rfl
private theorem receipt_1_16_2360_0_join6 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 896 384 = 1305841980153636235702152210016 :=
  phaseBlock_append receipt_1_16_2360_0_part7 receipt_1_16_2360_0_join5 rfl rfl rfl
private theorem receipt_1_16_2360_0_join7 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 640 640 = 2390411643907456255350097509024 :=
  phaseBlock_append receipt_1_16_2360_0_join4 receipt_1_16_2360_0_join6 rfl rfl rfl
private theorem receipt_1_16_2360_0_join8 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 0 1280 = 5913223799725315569440539952448 :=
  phaseBlock_append receipt_1_16_2360_0_join3 receipt_1_16_2360_0_join7 rfl rfl rfl
private theorem receipt_1_16_2360_0_join9 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 1280 256 = 668562353557198719859390854208 :=
  phaseBlock_append receipt_1_16_2360_0_part10 receipt_1_16_2360_0_part11 rfl rfl rfl
private theorem receipt_1_16_2360_0_join10 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 1664 256 = 443085923998767760691532687884 :=
  phaseBlock_append receipt_1_16_2360_0_part13 receipt_1_16_2360_0_part14 rfl rfl rfl
private theorem receipt_1_16_2360_0_join11 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 1536 384 = 719776759282329243479328328748 :=
  phaseBlock_append receipt_1_16_2360_0_part12 receipt_1_16_2360_0_join10 rfl rfl rfl
private theorem receipt_1_16_2360_0_join12 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 1280 640 = 1388339112839527963338719182956 :=
  phaseBlock_append receipt_1_16_2360_0_join9 receipt_1_16_2360_0_join11 rfl rfl rfl
private theorem receipt_1_16_2360_0_join13 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 2048 256 = 234844713145711439062600953462 :=
  phaseBlock_append receipt_1_16_2360_0_part16 receipt_1_16_2360_0_part17 rfl rfl rfl
private theorem receipt_1_16_2360_0_join14 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 1920 384 = 403154815185746650199260736793 :=
  phaseBlock_append receipt_1_16_2360_0_part15 receipt_1_16_2360_0_join13 rfl rfl rfl
private theorem receipt_1_16_2360_0_join15 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 2432 218 = 44422043585929932417625907684 :=
  phaseBlock_append receipt_1_16_2360_0_part19 receipt_1_16_2360_0_part20 rfl rfl rfl
private theorem receipt_1_16_2360_0_join16 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 2304 346 = 112793875582057293823796080691 :=
  phaseBlock_append receipt_1_16_2360_0_part18 receipt_1_16_2360_0_join15 rfl rfl rfl
private theorem receipt_1_16_2360_0_join17 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 1920 730 = 515948690767803944023056817484 :=
  phaseBlock_append receipt_1_16_2360_0_join14 receipt_1_16_2360_0_join16 rfl rfl rfl
private theorem receipt_1_16_2360_0_join18 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 1280 1370 = 1904287803607331907361776000440 :=
  phaseBlock_append receipt_1_16_2360_0_join12 receipt_1_16_2360_0_join17 rfl rfl rfl
private theorem receipt_1_16_2360_0_join19 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 0) 0 2650 = 7817511603332647476802315952888 :=
  phaseBlock_append receipt_1_16_2360_0_join8 receipt_1_16_2360_0_join18 rfl rfl rfl

private theorem receipt_1_16_2360_0 : fastPhase (bank 1 16).shape 179818 2360 103 1 0 2 0 = 7817511603332647476802315952888 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_1_16_2360_0_join19

private theorem receipt_1_16_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 0 128 = 801300687409029650106648234784 := by decide +kernel
private theorem receipt_1_16_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 128 128 = 751630866992006168311126473504 := by decide +kernel
private theorem receipt_1_16_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 256 128 = 703083173246535866399260633888 := by decide +kernel
private theorem receipt_1_16_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 384 128 = 655644244865723558813232012064 := by decide +kernel
private theorem receipt_1_16_2360_1_part4 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 512 128 = 609300751980905883404716264224 := by decide +kernel
private theorem receipt_1_16_2360_1_part5 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 640 128 = 564039396136517521155086711584 := by decide +kernel
private theorem receipt_1_16_2360_1_part6 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 768 128 = 519846910264957415895617645344 := by decide +kernel
private theorem receipt_1_16_2360_1_part7 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 896 128 = 476710058661454994027687631648 := by decide +kernel
private theorem receipt_1_16_2360_1_part8 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 1024 128 = 434615636958936384242982816544 := by decide +kernel
private theorem receipt_1_16_2360_1_part9 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 1152 128 = 393550472102890637243700230944 := by decide +kernel
private theorem receipt_1_16_2360_1_part10 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 1280 128 = 353501422326235945462751095584 := by decide +kernel
private theorem receipt_1_16_2360_1_part11 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 1408 128 = 314455377124185862783964125984 := by decide +kernel
private theorem receipt_1_16_2360_1_part12 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 1536 128 = 276399257229115524262288837408 := by decide +kernel
private theorem receipt_1_16_2360_1_part13 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 1664 128 = 239320014773544418724614107144 := by decide +kernel
private theorem receipt_1_16_2360_1_part14 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 1792 128 = 203204658034179589720808786359 := by decide +kernel
private theorem receipt_1_16_2360_1_part15 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 1920 128 = 168040232266306130633386753327 := by decide +kernel
private theorem receipt_1_16_2360_1_part16 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 2048 128 = 133813749464213216591717733713 := by decide +kernel
private theorem receipt_1_16_2360_1_part17 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 2176 128 = 100512245774553666303097521472 := by decide +kernel
private theorem receipt_1_16_2360_1_part18 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 2304 128 = 68122788570916887727393299495 := by decide +kernel
private theorem receipt_1_16_2360_1_part19 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 2432 128 = 36632476352531961602869323865 := by decide +kernel
private theorem receipt_1_16_2360_1_part20 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 2560 90 = 7380894068280541327720035759 := by decide +kernel
private theorem receipt_1_16_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 0 256 = 1552931554401035818417774708288 :=
  phaseBlock_append receipt_1_16_2360_1_part0 receipt_1_16_2360_1_part1 rfl rfl rfl
private theorem receipt_1_16_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 384 256 = 1264944996846629442217948276288 :=
  phaseBlock_append receipt_1_16_2360_1_part3 receipt_1_16_2360_1_part4 rfl rfl rfl
private theorem receipt_1_16_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 256 384 = 1968028170093165308617208910176 :=
  phaseBlock_append receipt_1_16_2360_1_part2 receipt_1_16_2360_1_join1 rfl rfl rfl
private theorem receipt_1_16_2360_1_join3 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 0 640 = 3520959724494201127034983618464 :=
  phaseBlock_append receipt_1_16_2360_1_join0 receipt_1_16_2360_1_join2 rfl rfl rfl
private theorem receipt_1_16_2360_1_join4 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 640 256 = 1083886306401474937050704356928 :=
  phaseBlock_append receipt_1_16_2360_1_part5 receipt_1_16_2360_1_part6 rfl rfl rfl
private theorem receipt_1_16_2360_1_join5 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 1024 256 = 828166109061827021486683047488 :=
  phaseBlock_append receipt_1_16_2360_1_part8 receipt_1_16_2360_1_part9 rfl rfl rfl
private theorem receipt_1_16_2360_1_join6 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 896 384 = 1304876167723282015514370679136 :=
  phaseBlock_append receipt_1_16_2360_1_part7 receipt_1_16_2360_1_join5 rfl rfl rfl
private theorem receipt_1_16_2360_1_join7 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 640 640 = 2388762474124756952565075036064 :=
  phaseBlock_append receipt_1_16_2360_1_join4 receipt_1_16_2360_1_join6 rfl rfl rfl
private theorem receipt_1_16_2360_1_join8 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 0 1280 = 5909722198618958079600058654528 :=
  phaseBlock_append receipt_1_16_2360_1_join3 receipt_1_16_2360_1_join7 rfl rfl rfl
private theorem receipt_1_16_2360_1_join9 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 1280 256 = 667956799450421808246715221568 :=
  phaseBlock_append receipt_1_16_2360_1_part10 receipt_1_16_2360_1_part11 rfl rfl rfl
private theorem receipt_1_16_2360_1_join10 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 1664 256 = 442524672807724008445422893503 :=
  phaseBlock_append receipt_1_16_2360_1_part13 receipt_1_16_2360_1_part14 rfl rfl rfl
private theorem receipt_1_16_2360_1_join11 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 1536 384 = 718923930036839532707711730911 :=
  phaseBlock_append receipt_1_16_2360_1_part12 receipt_1_16_2360_1_join10 rfl rfl rfl
private theorem receipt_1_16_2360_1_join12 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 1280 640 = 1386880729487261340954426952479 :=
  phaseBlock_append receipt_1_16_2360_1_join9 receipt_1_16_2360_1_join11 rfl rfl rfl
private theorem receipt_1_16_2360_1_join13 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 2048 256 = 234325995238766882894815255185 :=
  phaseBlock_append receipt_1_16_2360_1_part16 receipt_1_16_2360_1_part17 rfl rfl rfl
private theorem receipt_1_16_2360_1_join14 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 1920 384 = 402366227505073013528202008512 :=
  phaseBlock_append receipt_1_16_2360_1_part15 receipt_1_16_2360_1_join13 rfl rfl rfl
private theorem receipt_1_16_2360_1_join15 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 2432 218 = 44013370420812502930589359624 :=
  phaseBlock_append receipt_1_16_2360_1_part19 receipt_1_16_2360_1_part20 rfl rfl rfl
private theorem receipt_1_16_2360_1_join16 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 2304 346 = 112136158991729390657982659119 :=
  phaseBlock_append receipt_1_16_2360_1_part18 receipt_1_16_2360_1_join15 rfl rfl rfl
private theorem receipt_1_16_2360_1_join17 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 1920 730 = 514502386496802404186184667631 :=
  phaseBlock_append receipt_1_16_2360_1_join14 receipt_1_16_2360_1_join16 rfl rfl rfl
private theorem receipt_1_16_2360_1_join18 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 1280 1370 = 1901383115984063745140611620110 :=
  phaseBlock_append receipt_1_16_2360_1_join12 receipt_1_16_2360_1_join17 rfl rfl rfl
private theorem receipt_1_16_2360_1_join19 :
    phaseBlock (fastLayer (bank 1 16).shape 179818 2360 103 1 0 2 1) 0 2650 = 7811105314603021824740670274638 :=
  phaseBlock_append receipt_1_16_2360_1_join8 receipt_1_16_2360_1_join18 rfl rfl rfl

private theorem receipt_1_16_2360_1 : fastPhase (bank 1 16).shape 179818 2360 103 1 0 2 1 = 7811105314603021824740670274638 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_1_16_2360_1_join19

theorem receipt_1_16 : Checked (bank 1 16) 103 0 2 := by
  refine checked_from_values (bank 1 16) 103 0 2
    (P3_7_1.checked (bank 1 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_12604_2649)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_16_2359_0 receipt_1_16_2359_1 receipt_1_16_2360_0 receipt_1_16_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_16_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 0 128 = 430377919230925719094268233344 := by decide +kernel
private theorem receipt_2_16_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 128 128 = 402689103813198495359109449344 := by decide +kernel
private theorem receipt_2_16_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 256 128 = 375734992852349291999591466624 := by decide +kernel
private theorem receipt_2_16_2359_0_part3 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 384 128 = 349503788913863190624488244864 := by decide +kernel
private theorem receipt_2_16_2359_0_part4 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 512 128 = 323983788597474870211336373888 := by decide +kernel
private theorem receipt_2_16_2359_0_part5 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 640 128 = 299163382229290573892877764224 := by decide +kernel
private theorem receipt_2_16_2359_0_part6 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 768 128 = 275031053553910075743502337664 := by decide +kernel
private theorem receipt_2_16_2359_0_part7 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 896 128 = 251575379426548647565690717824 := by decide +kernel
private theorem receipt_2_16_2359_0_part8 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 1024 128 = 228785029505159025676456920704 := by decide +kernel
private theorem receipt_2_16_2359_0_part9 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 1152 128 = 206648765942553377693791045248 := by decide +kernel
private theorem receipt_2_16_2359_0_part10 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 1280 128 = 185155443078525269323101963904 := by decide +kernel
private theorem receipt_2_16_2359_0_part11 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 1408 128 = 164294007131971631143660013184 := by decide +kernel
private theorem receipt_2_16_2359_0_part12 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 1536 128 = 144053495893014725395039684224 := by decide +kernel
private theorem receipt_2_16_2359_0_part13 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 1664 128 = 124423038534458334254992262639 := by decide +kernel
private theorem receipt_2_16_2359_0_part14 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 1792 128 = 105391868493293845212276852502 := by decide +kernel
private theorem receipt_2_16_2359_0_part15 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 1920 128 = 86949311921280847070071522314 := by decide +kernel
private theorem receipt_2_16_2359_0_part16 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 2048 128 = 69084752177391969781656318528 := by decide +kernel
private theorem receipt_2_16_2359_0_part17 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 2176 128 = 51787659449651285593748107115 := by decide +kernel
private theorem receipt_2_16_2359_0_part18 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 2304 128 = 35047593951337527312054947418 := by decide +kernel
private theorem receipt_2_16_2359_0_part19 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 2432 128 = 18854205558301282513406899603 := by decide +kernel
private theorem receipt_2_16_2359_0_part20 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 2560 90 = 3850799411352674942411689581 := by decide +kernel
private theorem receipt_2_16_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 0 256 = 833067023044124214453377682688 :=
  phaseBlock_append receipt_2_16_2359_0_part0 receipt_2_16_2359_0_part1 rfl rfl rfl
private theorem receipt_2_16_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 384 256 = 673487577511338060835824618752 :=
  phaseBlock_append receipt_2_16_2359_0_part3 receipt_2_16_2359_0_part4 rfl rfl rfl
private theorem receipt_2_16_2359_0_join2 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 256 384 = 1049222570363687352835416085376 :=
  phaseBlock_append receipt_2_16_2359_0_part2 receipt_2_16_2359_0_join1 rfl rfl rfl
private theorem receipt_2_16_2359_0_join3 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 0 640 = 1882289593407811567288793768064 :=
  phaseBlock_append receipt_2_16_2359_0_join0 receipt_2_16_2359_0_join2 rfl rfl rfl
private theorem receipt_2_16_2359_0_join4 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 640 256 = 574194435783200649636380101888 :=
  phaseBlock_append receipt_2_16_2359_0_part5 receipt_2_16_2359_0_part6 rfl rfl rfl
private theorem receipt_2_16_2359_0_join5 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 1024 256 = 435433795447712403370247965952 :=
  phaseBlock_append receipt_2_16_2359_0_part8 receipt_2_16_2359_0_part9 rfl rfl rfl
private theorem receipt_2_16_2359_0_join6 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 896 384 = 687009174874261050935938683776 :=
  phaseBlock_append receipt_2_16_2359_0_part7 receipt_2_16_2359_0_join5 rfl rfl rfl
private theorem receipt_2_16_2359_0_join7 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 640 640 = 1261203610657461700572318785664 :=
  phaseBlock_append receipt_2_16_2359_0_join4 receipt_2_16_2359_0_join6 rfl rfl rfl
private theorem receipt_2_16_2359_0_join8 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 0 1280 = 3143493204065273267861112553728 :=
  phaseBlock_append receipt_2_16_2359_0_join3 receipt_2_16_2359_0_join7 rfl rfl rfl
private theorem receipt_2_16_2359_0_join9 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 1280 256 = 349449450210496900466761977088 :=
  phaseBlock_append receipt_2_16_2359_0_part10 receipt_2_16_2359_0_part11 rfl rfl rfl
private theorem receipt_2_16_2359_0_join10 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 1664 256 = 229814907027752179467269115141 :=
  phaseBlock_append receipt_2_16_2359_0_part13 receipt_2_16_2359_0_part14 rfl rfl rfl
private theorem receipt_2_16_2359_0_join11 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 1536 384 = 373868402920766904862308799365 :=
  phaseBlock_append receipt_2_16_2359_0_part12 receipt_2_16_2359_0_join10 rfl rfl rfl
private theorem receipt_2_16_2359_0_join12 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 1280 640 = 723317853131263805329070776453 :=
  phaseBlock_append receipt_2_16_2359_0_join9 receipt_2_16_2359_0_join11 rfl rfl rfl
private theorem receipt_2_16_2359_0_join13 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 2048 256 = 120872411627043255375404425643 :=
  phaseBlock_append receipt_2_16_2359_0_part16 receipt_2_16_2359_0_part17 rfl rfl rfl
private theorem receipt_2_16_2359_0_join14 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 1920 384 = 207821723548324102445475947957 :=
  phaseBlock_append receipt_2_16_2359_0_part15 receipt_2_16_2359_0_join13 rfl rfl rfl
private theorem receipt_2_16_2359_0_join15 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 2432 218 = 22705004969653957455818589184 :=
  phaseBlock_append receipt_2_16_2359_0_part19 receipt_2_16_2359_0_part20 rfl rfl rfl
private theorem receipt_2_16_2359_0_join16 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 2304 346 = 57752598920991484767873536602 :=
  phaseBlock_append receipt_2_16_2359_0_part18 receipt_2_16_2359_0_join15 rfl rfl rfl
private theorem receipt_2_16_2359_0_join17 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 1920 730 = 265574322469315587213349484559 :=
  phaseBlock_append receipt_2_16_2359_0_join14 receipt_2_16_2359_0_join16 rfl rfl rfl
private theorem receipt_2_16_2359_0_join18 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 1280 1370 = 988892175600579392542420261012 :=
  phaseBlock_append receipt_2_16_2359_0_join12 receipt_2_16_2359_0_join17 rfl rfl rfl
private theorem receipt_2_16_2359_0_join19 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 0) 0 2650 = 4132385379665852660403532814740 :=
  phaseBlock_append receipt_2_16_2359_0_join8 receipt_2_16_2359_0_join18 rfl rfl rfl

private theorem receipt_2_16_2359_0 : fastPhase (bank 2 16).shape 179818 2359 103 1 0 7 0 = 4132385379665852660403532814740 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_2_16_2359_0_join19

private theorem receipt_2_16_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 0 128 = 430161483152986307583344997632 := by decide +kernel
private theorem receipt_2_16_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 128 128 = 402478293640806801796616779008 := by decide +kernel
private theorem receipt_2_16_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 256 128 = 375529718579040557890819421440 := by decide +kernel
private theorem receipt_2_16_2359_1_part3 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 384 128 = 349303961251832810652416439552 := by decide +kernel
private theorem receipt_2_16_2359_1_part4 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 512 128 = 323789318975220755220365407488 := by decide +kernel
private theorem receipt_2_16_2359_1_part5 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 640 128 = 298974182789255513872560649472 := by decide +kernel
private theorem receipt_2_16_2359_1_part6 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 768 128 = 274847037150124102812275930368 := by decide +kernel
private theorem receipt_2_16_2359_1_part7 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 896 128 = 251396459622271398954607146240 := by decide +kernel
private theorem receipt_2_16_2359_1_part8 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 1024 128 = 228611120570522106712915014912 := by decide +kernel
private theorem receipt_2_16_2359_1_part9 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 1152 128 = 206479782852202724785267766528 := by decide +kernel
private theorem receipt_2_16_2359_1_part10 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 1280 128 = 184991301509263512940883834112 := by decide +kernel
private theorem receipt_2_16_2359_1_part11 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 1408 128 = 164134623460400458806574544128 := by decide +kernel
private theorem receipt_2_16_2359_1_part12 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 1536 128 = 143898787193177244653186807040 := by decide +kernel
private theorem receipt_2_16_2359_1_part13 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 1664 128 = 124272922575339142149397276497 := by decide +kernel
private theorem receipt_2_16_2359_1_part14 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 1792 128 = 105246263718744622915032314591 := by decide +kernel
private theorem receipt_2_16_2359_1_part15 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 1920 128 = 86808137432168397534614580111 := by decide +kernel
private theorem receipt_2_16_2359_1_part16 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 2048 128 = 68947927759986421274823768110 := by decide +kernel
private theorem receipt_2_16_2359_1_part17 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 2176 128 = 51655105576966050622321071717 := by decide +kernel
private theorem receipt_2_16_2359_1_part18 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 2304 128 = 34919231780706298905520125482 := by decide +kernel
private theorem receipt_2_16_2359_1_part19 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 2432 128 = 18729956929051090252718081962 := by decide +kernel
private theorem receipt_2_16_2359_1_part20 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 2560 90 = 3765858268518139666819434335 := by decide +kernel
private theorem receipt_2_16_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 0 256 = 832639776793793109379961776640 :=
  phaseBlock_append receipt_2_16_2359_1_part0 receipt_2_16_2359_1_part1 rfl rfl rfl
private theorem receipt_2_16_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 384 256 = 673093280227053565872781847040 :=
  phaseBlock_append receipt_2_16_2359_1_part3 receipt_2_16_2359_1_part4 rfl rfl rfl
private theorem receipt_2_16_2359_1_join2 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 256 384 = 1048622998806094123763601268480 :=
  phaseBlock_append receipt_2_16_2359_1_part2 receipt_2_16_2359_1_join1 rfl rfl rfl
private theorem receipt_2_16_2359_1_join3 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 0 640 = 1881262775599887233143563045120 :=
  phaseBlock_append receipt_2_16_2359_1_join0 receipt_2_16_2359_1_join2 rfl rfl rfl
private theorem receipt_2_16_2359_1_join4 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 640 256 = 573821219939379616684836579840 :=
  phaseBlock_append receipt_2_16_2359_1_part5 receipt_2_16_2359_1_part6 rfl rfl rfl
private theorem receipt_2_16_2359_1_join5 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 1024 256 = 435090903422724831498182781440 :=
  phaseBlock_append receipt_2_16_2359_1_part8 receipt_2_16_2359_1_part9 rfl rfl rfl
private theorem receipt_2_16_2359_1_join6 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 896 384 = 686487363044996230452789927680 :=
  phaseBlock_append receipt_2_16_2359_1_part7 receipt_2_16_2359_1_join5 rfl rfl rfl
private theorem receipt_2_16_2359_1_join7 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 640 640 = 1260308582984375847137626507520 :=
  phaseBlock_append receipt_2_16_2359_1_join4 receipt_2_16_2359_1_join6 rfl rfl rfl
private theorem receipt_2_16_2359_1_join8 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 0 1280 = 3141571358584263080281189552640 :=
  phaseBlock_append receipt_2_16_2359_1_join3 receipt_2_16_2359_1_join7 rfl rfl rfl
private theorem receipt_2_16_2359_1_join9 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 1280 256 = 349125924969663971747458378240 :=
  phaseBlock_append receipt_2_16_2359_1_part10 receipt_2_16_2359_1_part11 rfl rfl rfl
private theorem receipt_2_16_2359_1_join10 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 1664 256 = 229519186294083765064429591088 :=
  phaseBlock_append receipt_2_16_2359_1_part13 receipt_2_16_2359_1_part14 rfl rfl rfl
private theorem receipt_2_16_2359_1_join11 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 1536 384 = 373417973487261009717616398128 :=
  phaseBlock_append receipt_2_16_2359_1_part12 receipt_2_16_2359_1_join10 rfl rfl rfl
private theorem receipt_2_16_2359_1_join12 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 1280 640 = 722543898456924981465074776368 :=
  phaseBlock_append receipt_2_16_2359_1_join9 receipt_2_16_2359_1_join11 rfl rfl rfl
private theorem receipt_2_16_2359_1_join13 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 2048 256 = 120603033336952471897144839827 :=
  phaseBlock_append receipt_2_16_2359_1_part16 receipt_2_16_2359_1_part17 rfl rfl rfl
private theorem receipt_2_16_2359_1_join14 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 1920 384 = 207411170769120869431759419938 :=
  phaseBlock_append receipt_2_16_2359_1_part15 receipt_2_16_2359_1_join13 rfl rfl rfl
private theorem receipt_2_16_2359_1_join15 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 2432 218 = 22495815197569229919537516297 :=
  phaseBlock_append receipt_2_16_2359_1_part19 receipt_2_16_2359_1_part20 rfl rfl rfl
private theorem receipt_2_16_2359_1_join16 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 2304 346 = 57415046978275528825057641779 :=
  phaseBlock_append receipt_2_16_2359_1_part18 receipt_2_16_2359_1_join15 rfl rfl rfl
private theorem receipt_2_16_2359_1_join17 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 1920 730 = 264826217747396398256817061717 :=
  phaseBlock_append receipt_2_16_2359_1_join14 receipt_2_16_2359_1_join16 rfl rfl rfl
private theorem receipt_2_16_2359_1_join18 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 1280 1370 = 987370116204321379721891838085 :=
  phaseBlock_append receipt_2_16_2359_1_join12 receipt_2_16_2359_1_join17 rfl rfl rfl
private theorem receipt_2_16_2359_1_join19 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2359 103 1 0 7 1) 0 2650 = 4128941474788584460003081390725 :=
  phaseBlock_append receipt_2_16_2359_1_join8 receipt_2_16_2359_1_join18 rfl rfl rfl

private theorem receipt_2_16_2359_1 : fastPhase (bank 2 16).shape 179818 2359 103 1 0 7 1 = 4128941474788584460003081390725 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_2_16_2359_1_join19

private theorem receipt_2_16_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 0 128 = 430381796857759553152730034144 := by decide +kernel
private theorem receipt_2_16_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 128 128 = 402692634610533978672251232224 := by decide +kernel
private theorem receipt_2_16_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 256 128 = 375738195114257367731972755424 := by decide +kernel
private theorem receipt_2_16_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 384 128 = 349506680565237466118591430624 := by decide +kernel
private theorem receipt_2_16_2360_0_part4 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 512 128 = 323986387197211318887547678688 := by decide +kernel
private theorem receipt_2_16_2360_0_part5 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 640 128 = 299165704973456461935516000224 := by decide +kernel
private theorem receipt_2_16_2360_0_part6 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 768 128 = 275033117278902113572895461344 := by decide +kernel
private theorem receipt_2_16_2360_0_part7 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 896 128 = 251577200612240366096300179424 := by decide +kernel
private theorem receipt_2_16_2360_0_part8 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 1024 128 = 228786624278037377361049808864 := by decide +kernel
private theorem receipt_2_16_2360_0_part9 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 1152 128 = 206650150078844562353660026848 := by decide +kernel
private theorem receipt_2_16_2360_0_part10 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 1280 128 = 185156632007309784764333019104 := by decide +kernel
private theorem receipt_2_16_2360_0_part11 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 1408 128 = 164295015938288548559447965664 := by decide +kernel
private theorem receipt_2_16_2360_0_part12 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 1536 128 = 144054339320955189554051526624 := by decide +kernel
private theorem receipt_2_16_2360_0_part13 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 1664 128 = 124423730968597528549860119546 := by decide +kernel
private theorem receipt_2_16_2360_0_part14 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 1792 128 = 105392423589025564222732075683 := by decide +kernel
private theorem receipt_2_16_2360_0_part15 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 1920 128 = 86949743440504493137227828096 := by decide +kernel
private theorem receipt_2_16_2360_0_part16 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 2048 128 = 69085073742730916312785540037 := by decide +kernel
private theorem receipt_2_16_2360_0_part17 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 2176 128 = 51787884347063447631540015430 := by decide +kernel
private theorem receipt_2_16_2360_0_part18 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 2304 128 = 35047735120889873841906269352 := by decide +kernel
private theorem receipt_2_16_2360_0_part19 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 2432 128 = 18854275599445537592338345233 := by decide +kernel
private theorem receipt_2_16_2360_0_part20 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 2560 90 = 3850812701493520805552364086 := by decide +kernel
private theorem receipt_2_16_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 0 256 = 833074431468293531824981266368 :=
  phaseBlock_append receipt_2_16_2360_0_part0 receipt_2_16_2360_0_part1 rfl rfl rfl
private theorem receipt_2_16_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 384 256 = 673493067762448785006139109312 :=
  phaseBlock_append receipt_2_16_2360_0_part3 receipt_2_16_2360_0_part4 rfl rfl rfl
private theorem receipt_2_16_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 256 384 = 1049231262876706152738111864736 :=
  phaseBlock_append receipt_2_16_2360_0_part2 receipt_2_16_2360_0_join1 rfl rfl rfl
private theorem receipt_2_16_2360_0_join3 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 0 640 = 1882305694344999684563093131104 :=
  phaseBlock_append receipt_2_16_2360_0_join0 receipt_2_16_2360_0_join2 rfl rfl rfl
private theorem receipt_2_16_2360_0_join4 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 640 256 = 574198822252358575508411461568 :=
  phaseBlock_append receipt_2_16_2360_0_part5 receipt_2_16_2360_0_part6 rfl rfl rfl
private theorem receipt_2_16_2360_0_join5 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 1024 256 = 435436774356881939714709835712 :=
  phaseBlock_append receipt_2_16_2360_0_part8 receipt_2_16_2360_0_part9 rfl rfl rfl
private theorem receipt_2_16_2360_0_join6 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 896 384 = 687013974969122305811010015136 :=
  phaseBlock_append receipt_2_16_2360_0_part7 receipt_2_16_2360_0_join5 rfl rfl rfl
private theorem receipt_2_16_2360_0_join7 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 640 640 = 1261212797221480881319421476704 :=
  phaseBlock_append receipt_2_16_2360_0_join4 receipt_2_16_2360_0_join6 rfl rfl rfl
private theorem receipt_2_16_2360_0_join8 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 0 1280 = 3143518491566480565882514607808 :=
  phaseBlock_append receipt_2_16_2360_0_join3 receipt_2_16_2360_0_join7 rfl rfl rfl
private theorem receipt_2_16_2360_0_join9 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 1280 256 = 349451647945598333323780984768 :=
  phaseBlock_append receipt_2_16_2360_0_part10 receipt_2_16_2360_0_part11 rfl rfl rfl
private theorem receipt_2_16_2360_0_join10 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 1664 256 = 229816154557623092772592195229 :=
  phaseBlock_append receipt_2_16_2360_0_part13 receipt_2_16_2360_0_part14 rfl rfl rfl
private theorem receipt_2_16_2360_0_join11 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 1536 384 = 373870493878578282326643721853 :=
  phaseBlock_append receipt_2_16_2360_0_part12 receipt_2_16_2360_0_join10 rfl rfl rfl
private theorem receipt_2_16_2360_0_join12 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 1280 640 = 723322141824176615650424706621 :=
  phaseBlock_append receipt_2_16_2360_0_join9 receipt_2_16_2360_0_join11 rfl rfl rfl
private theorem receipt_2_16_2360_0_join13 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 2048 256 = 120872958089794363944325555467 :=
  phaseBlock_append receipt_2_16_2360_0_part16 receipt_2_16_2360_0_part17 rfl rfl rfl
private theorem receipt_2_16_2360_0_join14 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 1920 384 = 207822701530298857081553383563 :=
  phaseBlock_append receipt_2_16_2360_0_part15 receipt_2_16_2360_0_join13 rfl rfl rfl
private theorem receipt_2_16_2360_0_join15 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 2432 218 = 22705088300939058397890709319 :=
  phaseBlock_append receipt_2_16_2360_0_part19 receipt_2_16_2360_0_part20 rfl rfl rfl
private theorem receipt_2_16_2360_0_join16 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 2304 346 = 57752823421828932239796978671 :=
  phaseBlock_append receipt_2_16_2360_0_part18 receipt_2_16_2360_0_join15 rfl rfl rfl
private theorem receipt_2_16_2360_0_join17 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 1920 730 = 265575524952127789321350362234 :=
  phaseBlock_append receipt_2_16_2360_0_join14 receipt_2_16_2360_0_join16 rfl rfl rfl
private theorem receipt_2_16_2360_0_join18 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 1280 1370 = 988897666776304404971775068855 :=
  phaseBlock_append receipt_2_16_2360_0_join12 receipt_2_16_2360_0_join17 rfl rfl rfl
private theorem receipt_2_16_2360_0_join19 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 0) 0 2650 = 4132416158342784970854289676663 :=
  phaseBlock_append receipt_2_16_2360_0_join8 receipt_2_16_2360_0_join18 rfl rfl rfl

private theorem receipt_2_16_2360_0 : fastPhase (bank 2 16).shape 179818 2360 103 1 0 7 0 = 4132416158342784970854289676663 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_2_16_2360_0_join19

private theorem receipt_2_16_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 0 128 = 430165359168705314756059349344 := by decide +kernel
private theorem receipt_2_16_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 128 128 = 402481822903589292226204823904 := by decide +kernel
private theorem receipt_2_16_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 256 128 = 375532919381131818309099626848 := by decide +kernel
private theorem receipt_2_16_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 384 128 = 349306851516318394238684025184 := by decide +kernel
private theorem receipt_2_16_2360_1_part4 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 512 128 = 323791916259206119523540468064 := by decide +kernel
private theorem receipt_2_16_2360_1_part5 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 640 128 = 298976504287034883519384072544 := by decide +kernel
private theorem receipt_2_16_2360_1_part6 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 768 128 = 274849099696338557001553109344 := by decide +kernel
private theorem receipt_2_16_2360_1_part7 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 896 128 = 251398279695056183737499488608 := by decide +kernel
private theorem receipt_2_16_2360_1_part8 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 1024 128 = 228612714294643172059279245664 := by decide +kernel
private theorem receipt_2_16_2360_1_part9 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 1152 128 = 206481166002182486436043026784 := by decide +kernel
private theorem receipt_2_16_2360_1_part10 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 1280 128 = 184992489512495839046526574944 := by decide +kernel
private theorem receipt_2_16_2360_1_part11 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 1408 128 = 164135631400254881351541215584 := by decide +kernel
private theorem receipt_2_16_2360_1_part12 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 1536 128 = 143899629812092395666464342368 := by decide +kernel
private theorem receipt_2_16_2360_1_part13 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 1664 128 = 124273614256280284716351636669 := by decide +kernel
private theorem receipt_2_16_2360_1_part14 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 1792 128 = 105246818116036465811415053854 := by decide +kernel
private theorem receipt_2_16_2360_1_part15 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 1920 128 = 86808568306279242330514360747 := by decide +kernel
private theorem receipt_2_16_2360_1_part16 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 2048 128 = 68948248731905920069514416748 := by decide +kernel
private theorem receipt_2_16_2360_1_part17 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 2176 128 = 51655329931022506232625590887 := by decide +kernel
private theorem receipt_2_16_2360_1_part18 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 2304 128 = 34919372455358124870921412755 := by decide +kernel
private theorem receipt_2_16_2360_1_part19 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 2432 128 = 18730026522165870215510770930 := by decide +kernel
private theorem receipt_2_16_2360_1_part20 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 2560 90 = 3765871270852587667275557739 := by decide +kernel
private theorem receipt_2_16_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 0 256 = 832647182072294606982264173248 :=
  phaseBlock_append receipt_2_16_2360_1_part0 receipt_2_16_2360_1_part1 rfl rfl rfl
private theorem receipt_2_16_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 384 256 = 673098767775524513762224493248 :=
  phaseBlock_append receipt_2_16_2360_1_part3 receipt_2_16_2360_1_part4 rfl rfl rfl
private theorem receipt_2_16_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 256 384 = 1048631687156656332071324120096 :=
  phaseBlock_append receipt_2_16_2360_1_part2 receipt_2_16_2360_1_join1 rfl rfl rfl
private theorem receipt_2_16_2360_1_join3 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 0 640 = 1881278869228950939053588293344 :=
  phaseBlock_append receipt_2_16_2360_1_join0 receipt_2_16_2360_1_join2 rfl rfl rfl
private theorem receipt_2_16_2360_1_join4 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 640 256 = 573825603983373440520937181888 :=
  phaseBlock_append receipt_2_16_2360_1_part5 receipt_2_16_2360_1_part6 rfl rfl rfl
private theorem receipt_2_16_2360_1_join5 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 1024 256 = 435093880296825658495322272448 :=
  phaseBlock_append receipt_2_16_2360_1_part8 receipt_2_16_2360_1_part9 rfl rfl rfl
private theorem receipt_2_16_2360_1_join6 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 896 384 = 686492159991881842232821761056 :=
  phaseBlock_append receipt_2_16_2360_1_part7 receipt_2_16_2360_1_join5 rfl rfl rfl
private theorem receipt_2_16_2360_1_join7 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 640 640 = 1260317763975255282753758942944 :=
  phaseBlock_append receipt_2_16_2360_1_join4 receipt_2_16_2360_1_join6 rfl rfl rfl
private theorem receipt_2_16_2360_1_join8 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 0 1280 = 3141596633204206221807347236288 :=
  phaseBlock_append receipt_2_16_2360_1_join3 receipt_2_16_2360_1_join7 rfl rfl rfl
private theorem receipt_2_16_2360_1_join9 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 1280 256 = 349128120912750720398067790528 :=
  phaseBlock_append receipt_2_16_2360_1_part10 receipt_2_16_2360_1_part11 rfl rfl rfl
private theorem receipt_2_16_2360_1_join10 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 1664 256 = 229520432372316750527766690523 :=
  phaseBlock_append receipt_2_16_2360_1_part13 receipt_2_16_2360_1_part14 rfl rfl rfl
private theorem receipt_2_16_2360_1_join11 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 1536 384 = 373420062184409146194231032891 :=
  phaseBlock_append receipt_2_16_2360_1_part12 receipt_2_16_2360_1_join10 rfl rfl rfl
private theorem receipt_2_16_2360_1_join12 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 1280 640 = 722548183097159866592298823419 :=
  phaseBlock_append receipt_2_16_2360_1_join9 receipt_2_16_2360_1_join11 rfl rfl rfl
private theorem receipt_2_16_2360_1_join13 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 2048 256 = 120603578662928426302140007635 :=
  phaseBlock_append receipt_2_16_2360_1_part16 receipt_2_16_2360_1_part17 rfl rfl rfl
private theorem receipt_2_16_2360_1_join14 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 1920 384 = 207412146969207668632654368382 :=
  phaseBlock_append receipt_2_16_2360_1_part15 receipt_2_16_2360_1_join13 rfl rfl rfl
private theorem receipt_2_16_2360_1_join15 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 2432 218 = 22495897793018457882786328669 :=
  phaseBlock_append receipt_2_16_2360_1_part19 receipt_2_16_2360_1_part20 rfl rfl rfl
private theorem receipt_2_16_2360_1_join16 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 2304 346 = 57415270248376582753707741424 :=
  phaseBlock_append receipt_2_16_2360_1_part18 receipt_2_16_2360_1_join15 rfl rfl rfl
private theorem receipt_2_16_2360_1_join17 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 1920 730 = 264827417217584251386362109806 :=
  phaseBlock_append receipt_2_16_2360_1_join14 receipt_2_16_2360_1_join16 rfl rfl rfl
private theorem receipt_2_16_2360_1_join18 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 1280 1370 = 987375600314744117978660933225 :=
  phaseBlock_append receipt_2_16_2360_1_join12 receipt_2_16_2360_1_join17 rfl rfl rfl
private theorem receipt_2_16_2360_1_join19 :
    phaseBlock (fastLayer (bank 2 16).shape 179818 2360 103 1 0 7 1) 0 2650 = 4128972233518950339786008169513 :=
  phaseBlock_append receipt_2_16_2360_1_join8 receipt_2_16_2360_1_join18 rfl rfl rfl

private theorem receipt_2_16_2360_1 : fastPhase (bank 2 16).shape 179818 2360 103 1 0 7 1 = 4128972233518950339786008169513 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_2_16_2360_1_join19

theorem receipt_2_16 : Checked (bank 2 16) 103 0 7 := by
  refine checked_from_values (bank 2 16) 103 0 7
    (P3_7_1.checked (bank 2 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_12604_2649)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_16_2359_0 receipt_2_16_2359_1 receipt_2_16_2360_0 receipt_2_16_2360_1 (by decide +kernel) (by decide +kernel)

def group7_stage (i : Fin 1) : Fin 17 :=
  ⟨16+i.val, by have := i.isLt; omega⟩

theorem group7_checked (rect : Fin 4) (i : Fin 1) :
    Checked (bank rect (group7_stage i)) (reserve (group7_stage i))
      (excess rect) (seed rect) := by
  fin_cases i
  · fin_cases rect
    · exact receipt_0_16
    · exact receipt_1_16
    · exact receipt_2_16
    · exact largest_checked

theorem group7_avoids {h : ℕ} {D : K1_14_1.PoleData h} (Crt : K1_14_1.CRTLift D)
    (word : K1.I → K1_14.L) (lo : 2359 ≤ h) (hi : h ≤ 33579) (rect : Fin 4)
    (i : Fin 1) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group7_stage i)).shape
      (cutoff h rect (group7_stage i)), ¬ G∣Q :=
  (group7_checked rect i).avoids Crt word lo hi irr seeded slope hs hj


end Lower6960.RescueSource

end Merged_R6960RescueSourceReceipt7
