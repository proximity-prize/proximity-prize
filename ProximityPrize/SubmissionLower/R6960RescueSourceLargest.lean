import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt0
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open HelperSource (WidthGuard)

def largestBank : Bank := ⟨⟨9071,12604,2749,273579⟩,22490098892800000,695862530200649⟩

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

private theorem largest_checked_2402_0_part0 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 0 128 = 105475425099290076283712318592 := by decide +kernel
private theorem largest_checked_2402_0_part1 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 128 128 = 99059220674237121231585823872 := by decide +kernel
private theorem largest_checked_2402_0_part2 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 256 128 = 92770973185197526489565523072 := by decide +kernel
private theorem largest_checked_2402_0_part3 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 384 128 = 86612491974260627266943356032 := by decide +kernel
private theorem largest_checked_2402_0_part4 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 512 128 = 80585578653653296667120413824 := by decide +kernel
private theorem largest_checked_2402_0_part5 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 640 128 = 74692027115156471131136380032 := by decide +kernel
private theorem largest_checked_2402_0_part6 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 768 128 = 68933623539521675881198972032 := by decide +kernel
private theorem largest_checked_2402_0_part7 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 896 128 = 63312146405887550364213382272 := by decide +kernel
private theorem largest_checked_2402_0_part8 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 1024 128 = 57829366501196373695311719552 := by decide +kernel
private theorem largest_checked_2402_0_part9 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 1152 128 = 52487046929610590101382450304 := by decide +kernel
private theorem largest_checked_2402_0_part10 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 1280 128 = 47286943121929334364599839872 := by decide +kernel
private theorem largest_checked_2402_0_part11 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 1408 128 = 42230802845004957265953393792 := by decide +kernel
private theorem largest_checked_2402_0_part12 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 1536 128 = 37320366211159551028777299072 := by decide +kernel
private theorem largest_checked_2402_0_part13 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 1664 128 = 32557365687601474762279865472 := by decide +kernel
private theorem largest_checked_2402_0_part14 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 1792 128 = 27943526105841879905072966784 := by decide +kernel
private theorem largest_checked_2402_0_part15 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 1920 128 = 23480564671111235668701482112 := by decide +kernel
private theorem largest_checked_2402_0_part16 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 2048 128 = 19170190971775854481172737152 := by decide +kernel
private theorem largest_checked_2402_0_part17 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 2176 128 = 15014106988754417430485945472 := by decide +kernel
private theorem largest_checked_2402_0_part18 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 2304 128 = 11014007104934499708161649792 := by decide +kernel
private theorem largest_checked_2402_0_part19 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 2432 128 = 7171578114589096052771163264 := by decide +kernel
private theorem largest_checked_2402_0_part20 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 2560 128 = 3488499232793146193466010752 := by decide +kernel
private theorem largest_checked_2402_0_part21 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 2688 62 = 413559345160541595948922080 := by decide +kernel
private theorem largest_checked_2402_0_join0 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 0 256 = 204534645773527197515298142464 :=
  phaseBlock_append largest_checked_2402_0_part0 largest_checked_2402_0_part1 rfl rfl rfl
private theorem largest_checked_2402_0_join1 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 384 256 = 167198070627913923934063769856 :=
  phaseBlock_append largest_checked_2402_0_part3 largest_checked_2402_0_part4 rfl rfl rfl
private theorem largest_checked_2402_0_join2 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 256 384 = 259969043813111450423629292928 :=
  phaseBlock_append largest_checked_2402_0_part2 largest_checked_2402_0_join1 rfl rfl rfl
private theorem largest_checked_2402_0_join3 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 0 640 = 464503689586638647938927435392 :=
  phaseBlock_append largest_checked_2402_0_join0 largest_checked_2402_0_join2 rfl rfl rfl
private theorem largest_checked_2402_0_join4 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 768 256 = 132245769945409226245412354304 :=
  phaseBlock_append largest_checked_2402_0_part6 largest_checked_2402_0_part7 rfl rfl rfl
private theorem largest_checked_2402_0_join5 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 640 384 = 206937797060565697376548734336 :=
  phaseBlock_append largest_checked_2402_0_part5 largest_checked_2402_0_join4 rfl rfl rfl
private theorem largest_checked_2402_0_join6 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 1152 256 = 99773990051539924465982290176 :=
  phaseBlock_append largest_checked_2402_0_part9 largest_checked_2402_0_part10 rfl rfl rfl
private theorem largest_checked_2402_0_join7 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 1024 384 = 157603356552736298161294009728 :=
  phaseBlock_append largest_checked_2402_0_part8 largest_checked_2402_0_join6 rfl rfl rfl
private theorem largest_checked_2402_0_join8 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 640 768 = 364541153613301995537842744064 :=
  phaseBlock_append largest_checked_2402_0_join5 largest_checked_2402_0_join7 rfl rfl rfl
private theorem largest_checked_2402_0_join9 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 0 1408 = 829044843199940643476770179456 :=
  phaseBlock_append largest_checked_2402_0_join3 largest_checked_2402_0_join8 rfl rfl rfl
private theorem largest_checked_2402_0_join10 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 1408 256 = 79551169056164508294730692864 :=
  phaseBlock_append largest_checked_2402_0_part11 largest_checked_2402_0_part12 rfl rfl rfl
private theorem largest_checked_2402_0_join11 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 1792 256 = 51424090776953115573774448896 :=
  phaseBlock_append largest_checked_2402_0_part14 largest_checked_2402_0_part15 rfl rfl rfl
private theorem largest_checked_2402_0_join12 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 1664 384 = 83981456464554590336054314368 :=
  phaseBlock_append largest_checked_2402_0_part13 largest_checked_2402_0_join11 rfl rfl rfl
private theorem largest_checked_2402_0_join13 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 1408 640 = 163532625520719098630785007232 :=
  phaseBlock_append largest_checked_2402_0_join10 largest_checked_2402_0_join12 rfl rfl rfl
private theorem largest_checked_2402_0_join14 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 2176 256 = 26028114093688917138647595264 :=
  phaseBlock_append largest_checked_2402_0_part17 largest_checked_2402_0_part18 rfl rfl rfl
private theorem largest_checked_2402_0_join15 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 2048 384 = 45198305065464771619820332416 :=
  phaseBlock_append largest_checked_2402_0_part16 largest_checked_2402_0_join14 rfl rfl rfl
private theorem largest_checked_2402_0_join16 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 2560 190 = 3902058577953687789414932832 :=
  phaseBlock_append largest_checked_2402_0_part20 largest_checked_2402_0_part21 rfl rfl rfl
private theorem largest_checked_2402_0_join17 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 2432 318 = 11073636692542783842186096096 :=
  phaseBlock_append largest_checked_2402_0_part19 largest_checked_2402_0_join16 rfl rfl rfl
private theorem largest_checked_2402_0_join18 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 2048 702 = 56271941758007555462006428512 :=
  phaseBlock_append largest_checked_2402_0_join15 largest_checked_2402_0_join17 rfl rfl rfl
private theorem largest_checked_2402_0_join19 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 1408 1342 = 219804567278726654092791435744 :=
  phaseBlock_append largest_checked_2402_0_join13 largest_checked_2402_0_join18 rfl rfl rfl
private theorem largest_checked_2402_0_join20 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 0) 0 2750 = 1048849410478667297569561615200 :=
  phaseBlock_append largest_checked_2402_0_join9 largest_checked_2402_0_join19 rfl rfl rfl

private theorem largest_checked_2402_0 : fastPhase largestBank.shape 179798 2402 103 1 1 1 0 = 1048849410478667297569561615200 :=
  phase_of_block (n := 2750) (by decide +kernel) largest_checked_2402_0_join20

private theorem largest_checked_2402_1_part0 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 0 128 = 105425495023028359788584787456 := by decide +kernel
private theorem largest_checked_2402_1_part1 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 128 128 = 99010238552902227811347955200 := by decide +kernel
private theorem largest_checked_2402_1_part2 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 256 128 = 92722954395437988616442912256 := by decide +kernel
private theorem largest_checked_2402_1_part3 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 384 128 = 86565451829070283310555315712 := by decide +kernel
private theorem largest_checked_2402_1_part4 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 512 128 = 80539532402447828654803705344 := by decide +kernel
private theorem largest_checked_2402_1_part5 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 640 128 = 74646989943849942508268944896 := by decide +kernel
private theorem largest_checked_2402_1_part6 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 768 128 = 68889610570603069271523663360 := by decide +kernel
private theorem largest_checked_2402_1_part7 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 896 128 = 63269172698497305330161696256 := by decide +kernel
private theorem largest_checked_2402_1_part8 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 1024 128 = 57787447051202924498327526912 := by decide +kernel
private theorem largest_checked_2402_1_part9 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 1152 128 = 52446196669686903462245727744 := by decide +kernel
private theorem largest_checked_2402_1_part10 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 1280 128 = 47247176921629447223750401536 := by decide +kernel
private theorem largest_checked_2402_1_part11 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 1408 128 = 42192135510840514543814622720 := by decide +kernel
private theorem largest_checked_2402_1_part12 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 1536 128 = 37282812486676343386079878656 := by decide +kernel
private theorem largest_checked_2402_1_part13 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 1664 128 = 32520940253455976360385510912 := by decide +kernel
private theorem largest_checked_2402_1_part14 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 1792 128 = 27908243579877786166298156544 := by decide +kernel
private theorem largest_checked_2402_1_part15 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 1920 128 = 23446439608436001036641189376 := by decide +kernel
private theorem largest_checked_2402_1_part16 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 2048 128 = 19137237864837230181024161280 := by decide +kernel
private theorem largest_checked_2402_1_part17 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 2176 128 = 14982340267416989229372243456 := by decide +kernel
private theorem largest_checked_2402_1_part18 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 2304 128 = 10983441136556225675455667712 := by decide +kernel
private theorem largest_checked_2402_1_part19 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 2432 128 = 7142227204097844320419167744 := by decide +kernel
private theorem largest_checked_2402_1_part20 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 2560 128 = 3460377622763232716311420416 := by decide +kernel
private theorem largest_checked_2402_1_part21 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 2688 62 = 400384094199813527261857812 := by decide +kernel
private theorem largest_checked_2402_1_join0 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 0 256 = 204435733575930587599932742656 :=
  phaseBlock_append largest_checked_2402_1_part0 largest_checked_2402_1_part1 rfl rfl rfl
private theorem largest_checked_2402_1_join1 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 384 256 = 167104984231518111965359021056 :=
  phaseBlock_append largest_checked_2402_1_part3 largest_checked_2402_1_part4 rfl rfl rfl
private theorem largest_checked_2402_1_join2 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 256 384 = 259827938626956100581801933312 :=
  phaseBlock_append largest_checked_2402_1_part2 largest_checked_2402_1_join1 rfl rfl rfl
private theorem largest_checked_2402_1_join3 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 0 640 = 464263672202886688181734675968 :=
  phaseBlock_append largest_checked_2402_1_join0 largest_checked_2402_1_join2 rfl rfl rfl
private theorem largest_checked_2402_1_join4 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 768 256 = 132158783269100374601685359616 :=
  phaseBlock_append largest_checked_2402_1_part6 largest_checked_2402_1_part7 rfl rfl rfl
private theorem largest_checked_2402_1_join5 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 640 384 = 206805773212950317109954304512 :=
  phaseBlock_append largest_checked_2402_1_part5 largest_checked_2402_1_join4 rfl rfl rfl
private theorem largest_checked_2402_1_join6 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 1152 256 = 99693373591316350685996129280 :=
  phaseBlock_append largest_checked_2402_1_part9 largest_checked_2402_1_part10 rfl rfl rfl
private theorem largest_checked_2402_1_join7 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 1024 384 = 157480820642519275184323656192 :=
  phaseBlock_append largest_checked_2402_1_part8 largest_checked_2402_1_join6 rfl rfl rfl
private theorem largest_checked_2402_1_join8 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 640 768 = 364286593855469592294277960704 :=
  phaseBlock_append largest_checked_2402_1_join5 largest_checked_2402_1_join7 rfl rfl rfl
private theorem largest_checked_2402_1_join9 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 0 1408 = 828550266058356280476012636672 :=
  phaseBlock_append largest_checked_2402_1_join3 largest_checked_2402_1_join8 rfl rfl rfl
private theorem largest_checked_2402_1_join10 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 1408 256 = 79474947997516857929894501376 :=
  phaseBlock_append largest_checked_2402_1_part11 largest_checked_2402_1_part12 rfl rfl rfl
private theorem largest_checked_2402_1_join11 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 1792 256 = 51354683188313787202939345920 :=
  phaseBlock_append largest_checked_2402_1_part14 largest_checked_2402_1_part15 rfl rfl rfl
private theorem largest_checked_2402_1_join12 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 1664 384 = 83875623441769763563324856832 :=
  phaseBlock_append largest_checked_2402_1_part13 largest_checked_2402_1_join11 rfl rfl rfl
private theorem largest_checked_2402_1_join13 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 1408 640 = 163350571439286621493219358208 :=
  phaseBlock_append largest_checked_2402_1_join10 largest_checked_2402_1_join12 rfl rfl rfl
private theorem largest_checked_2402_1_join14 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 2176 256 = 25965781403973214904827911168 :=
  phaseBlock_append largest_checked_2402_1_part17 largest_checked_2402_1_part18 rfl rfl rfl
private theorem largest_checked_2402_1_join15 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 2048 384 = 45103019268810445085852072448 :=
  phaseBlock_append largest_checked_2402_1_part16 largest_checked_2402_1_join14 rfl rfl rfl
private theorem largest_checked_2402_1_join16 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 2560 190 = 3860761716963046243573278228 :=
  phaseBlock_append largest_checked_2402_1_part20 largest_checked_2402_1_part21 rfl rfl rfl
private theorem largest_checked_2402_1_join17 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 2432 318 = 11002988921060890563992445972 :=
  phaseBlock_append largest_checked_2402_1_part19 largest_checked_2402_1_join16 rfl rfl rfl
private theorem largest_checked_2402_1_join18 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 2048 702 = 56106008189871335649844518420 :=
  phaseBlock_append largest_checked_2402_1_join15 largest_checked_2402_1_join17 rfl rfl rfl
private theorem largest_checked_2402_1_join19 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 1408 1342 = 219456579629157957143063876628 :=
  phaseBlock_append largest_checked_2402_1_join13 largest_checked_2402_1_join18 rfl rfl rfl
private theorem largest_checked_2402_1_join20 :
    phaseBlock (fastLayer largestBank.shape 179798 2402 103 1 1 1 1) 0 2750 = 1048006845687514237619076513300 :=
  phaseBlock_append largest_checked_2402_1_join9 largest_checked_2402_1_join19 rfl rfl rfl

private theorem largest_checked_2402_1 : fastPhase largestBank.shape 179798 2402 103 1 1 1 1 = 1048006845687514237619076513300 :=
  phase_of_block (n := 2750) (by decide +kernel) largest_checked_2402_1_join20

private theorem largest_checked_2403_0_part0 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 0 128 = 105476372629231163263791423616 := by decide +kernel
private theorem largest_checked_2403_0_part1 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 128 128 = 99060068386624951621331484800 := by decide +kernel
private theorem largest_checked_2403_0_part2 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 256 128 = 92771727915771210713447833728 := by decide +kernel
private theorem largest_checked_2403_0_part3 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 384 128 = 86613160339686232086512189568 := by decide +kernel
private theorem largest_checked_2403_0_part4 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 512 128 = 80586167052291960980512759936 := by decide +kernel
private theorem largest_checked_2403_0_part5 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 640 128 = 74692541727831642163281461376 := by decide +kernel
private theorem largest_checked_2403_0_part6 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 768 128 = 68934070330285465764721139840 := by decide +kernel
private theorem largest_checked_2403_0_part7 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 896 128 = 63312531122786213111032791168 := by decide +kernel
private theorem largest_checked_2403_0_part8 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 1024 128 = 57829694677034902558942781568 := by decide +kernel
private theorem largest_checked_2403_0_part9 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 1152 128 = 52487323882716435329930068096 := by decide +kernel
private theorem largest_checked_2403_0_part10 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 1280 128 = 47287173956915241344453419136 := by decide +kernel
private theorem largest_checked_2403_0_part11 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 1408 128 = 42230992453530925056178634880 := by decide +kernel
private theorem largest_checked_2403_0_part12 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 1536 128 = 37320519272693911286205767808 := by decide +kernel
private theorem largest_checked_2403_0_part13 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 1664 128 = 32557486670181091057296343168 := by decide +kernel
private theorem largest_checked_2403_0_part14 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 1792 128 = 27943619266831467428100579456 := by decide +kernel
private theorem largest_checked_2403_0_part15 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 1920 128 = 23480634057961801327384608896 := by decide +kernel
private theorem largest_checked_2403_0_part16 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 2048 128 = 19170240422782257388257697920 := by decide +kernel
private theorem largest_checked_2403_0_part17 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 2176 128 = 15014140133812049782399467648 := by decide +kernel
private theorem largest_checked_2403_0_part18 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 2304 128 = 11014027366295088054287114368 := by decide +kernel
private theorem largest_checked_2403_0_part19 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 2432 128 = 7171588707615622955422630016 := by decide +kernel
private theorem largest_checked_2403_0_part20 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 2560 128 = 3488503166713892278560022656 := by decide +kernel
private theorem largest_checked_2403_0_part21 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 2688 62 = 413559699315120677132329152 := by decide +kernel
private theorem largest_checked_2403_0_join0 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 0 256 = 204536441015856114885122908416 :=
  phaseBlock_append largest_checked_2403_0_part0 largest_checked_2403_0_part1 rfl rfl rfl
private theorem largest_checked_2403_0_join1 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 384 256 = 167199327391978193067024949504 :=
  phaseBlock_append largest_checked_2403_0_part3 largest_checked_2403_0_part4 rfl rfl rfl
private theorem largest_checked_2403_0_join2 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 256 384 = 259971055307749403780472783232 :=
  phaseBlock_append largest_checked_2403_0_part2 largest_checked_2403_0_join1 rfl rfl rfl
private theorem largest_checked_2403_0_join3 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 0 640 = 464507496323605518665595691648 :=
  phaseBlock_append largest_checked_2403_0_join0 largest_checked_2403_0_join2 rfl rfl rfl
private theorem largest_checked_2403_0_join4 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 768 256 = 132246601453071678875753931008 :=
  phaseBlock_append largest_checked_2403_0_part6 largest_checked_2403_0_part7 rfl rfl rfl
private theorem largest_checked_2403_0_join5 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 640 384 = 206939143180903321039035392384 :=
  phaseBlock_append largest_checked_2403_0_part5 largest_checked_2403_0_join4 rfl rfl rfl
private theorem largest_checked_2403_0_join6 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 1152 256 = 99774497839631676674383487232 :=
  phaseBlock_append largest_checked_2403_0_part9 largest_checked_2403_0_part10 rfl rfl rfl
private theorem largest_checked_2403_0_join7 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 1024 384 = 157604192516666579233326268800 :=
  phaseBlock_append largest_checked_2403_0_part8 largest_checked_2403_0_join6 rfl rfl rfl
private theorem largest_checked_2403_0_join8 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 640 768 = 364543335697569900272361661184 :=
  phaseBlock_append largest_checked_2403_0_join5 largest_checked_2403_0_join7 rfl rfl rfl
private theorem largest_checked_2403_0_join9 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 0 1408 = 829050832021175418937957352832 :=
  phaseBlock_append largest_checked_2403_0_join3 largest_checked_2403_0_join8 rfl rfl rfl
private theorem largest_checked_2403_0_join10 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 1408 256 = 79551511726224836342384402688 :=
  phaseBlock_append largest_checked_2403_0_part11 largest_checked_2403_0_part12 rfl rfl rfl
private theorem largest_checked_2403_0_join11 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 1792 256 = 51424253324793268755485188352 :=
  phaseBlock_append largest_checked_2403_0_part14 largest_checked_2403_0_part15 rfl rfl rfl
private theorem largest_checked_2403_0_join12 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 1664 384 = 83981739994974359812781531520 :=
  phaseBlock_append largest_checked_2403_0_part13 largest_checked_2403_0_join11 rfl rfl rfl
private theorem largest_checked_2403_0_join13 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 1408 640 = 163533251721199196155165934208 :=
  phaseBlock_append largest_checked_2403_0_join10 largest_checked_2403_0_join12 rfl rfl rfl
private theorem largest_checked_2403_0_join14 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 2176 256 = 26028167500107137836686582016 :=
  phaseBlock_append largest_checked_2403_0_part17 largest_checked_2403_0_part18 rfl rfl rfl
private theorem largest_checked_2403_0_join15 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 2048 384 = 45198407922889395224944279936 :=
  phaseBlock_append largest_checked_2403_0_part16 largest_checked_2403_0_join14 rfl rfl rfl
private theorem largest_checked_2403_0_join16 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 2560 190 = 3902062866029012955692351808 :=
  phaseBlock_append largest_checked_2403_0_part20 largest_checked_2403_0_part21 rfl rfl rfl
private theorem largest_checked_2403_0_join17 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 2432 318 = 11073651573644635911114981824 :=
  phaseBlock_append largest_checked_2403_0_part19 largest_checked_2403_0_join16 rfl rfl rfl
private theorem largest_checked_2403_0_join18 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 2048 702 = 56272059496534031136059261760 :=
  phaseBlock_append largest_checked_2403_0_join15 largest_checked_2403_0_join17 rfl rfl rfl
private theorem largest_checked_2403_0_join19 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 1408 1342 = 219805311217733227291225195968 :=
  phaseBlock_append largest_checked_2403_0_join13 largest_checked_2403_0_join18 rfl rfl rfl
private theorem largest_checked_2403_0_join20 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 0) 0 2750 = 1048856143238908646229182548800 :=
  phaseBlock_append largest_checked_2403_0_join9 largest_checked_2403_0_join19 rfl rfl rfl

private theorem largest_checked_2403_0 : fastPhase largestBank.shape 179798 2403 103 1 1 1 0 = 1048856143238908646229182548800 :=
  phase_of_block (n := 2750) (by decide +kernel) largest_checked_2403_0_join20

private theorem largest_checked_2403_1_part0 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 0 128 = 105426442032420723655116167424 := by decide +kernel
private theorem largest_checked_2403_1_part1 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 128 128 = 99011085780397011450394753280 := by decide +kernel
private theorem largest_checked_2403_1_part2 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 256 128 = 92723708675564053302359349504 := by decide +kernel
private theorem largest_checked_2403_1_part3 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 384 128 = 86566119777288106818845604096 := by decide +kernel
private theorem largest_checked_2403_1_part4 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 512 128 = 80540120415917615426632292608 := by decide +kernel
private theorem largest_checked_2403_1_part5 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 640 128 = 74647504202198854205668538624 := by decide +kernel
private theorem largest_checked_2403_1_part6 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 768 128 = 68890057036691575723301034240 := by decide +kernel
private theorem largest_checked_2403_1_part7 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 896 128 = 63269557119184655868501260544 := by decide +kernel
private theorem largest_checked_2403_1_part8 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 1024 128 = 57787774958111739686092708096 := by decide +kernel
private theorem largest_checked_2403_1_part9 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 1152 128 = 52446473379966887210978097408 := by decide +kernel
private theorem largest_checked_2403_1_part10 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 1280 128 = 47247407538720219302366599424 := by decide +kernel
private theorem largest_checked_2403_1_part11 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 1408 128 = 42192324925233563478001056000 := by decide +kernel
private theorem largest_checked_2403_1_part12 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 1536 128 = 37282965376676099748385200384 := by decide +kernel
private theorem largest_checked_2403_1_part13 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 1664 128 = 32521061085940006451010877696 := by decide +kernel
private theorem largest_checked_2403_1_part14 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 1792 128 = 27908336611056106084585265408 := by decide +kernel
private theorem largest_checked_2403_1_part15 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 1920 128 = 23446508884609511143258093824 := by decide +kernel
private theorem largest_checked_2403_1_part16 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 2048 128 = 19137287223155269950848866560 := by decide +kernel
private theorem largest_checked_2403_1_part17 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 2176 128 = 14982373336634012495074081024 := by decide +kernel
private theorem largest_checked_2403_1_part18 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 2304 128 = 10983461337787596261774448896 := by decide +kernel
private theorem largest_checked_2403_1_part19 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 2432 128 = 7142237751574752069142116608 := by decide +kernel
private theorem largest_checked_2403_1_part20 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 2560 128 = 3460381524586729901947885824 := by decide +kernel
private theorem largest_checked_2403_1_part21 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 2688 62 = 400384437308972270005107228 := by decide +kernel
private theorem largest_checked_2403_1_join0 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 0 256 = 204437527812817735105510920704 :=
  phaseBlock_append largest_checked_2403_1_part0 largest_checked_2403_1_part1 rfl rfl rfl
private theorem largest_checked_2403_1_join1 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 384 256 = 167106240193205722245477896704 :=
  phaseBlock_append largest_checked_2403_1_part3 largest_checked_2403_1_part4 rfl rfl rfl
private theorem largest_checked_2403_1_join2 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 256 384 = 259829948868769775547837246208 :=
  phaseBlock_append largest_checked_2403_1_part2 largest_checked_2403_1_join1 rfl rfl rfl
private theorem largest_checked_2403_1_join3 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 0 640 = 464267476681587510653348166912 :=
  phaseBlock_append largest_checked_2403_1_join0 largest_checked_2403_1_join2 rfl rfl rfl
private theorem largest_checked_2403_1_join4 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 768 256 = 132159614155876231591802294784 :=
  phaseBlock_append largest_checked_2403_1_part6 largest_checked_2403_1_part7 rfl rfl rfl
private theorem largest_checked_2403_1_join5 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 640 384 = 206807118358075085797470833408 :=
  phaseBlock_append largest_checked_2403_1_part5 largest_checked_2403_1_join4 rfl rfl rfl
private theorem largest_checked_2403_1_join6 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 1152 256 = 99693880918687106513344696832 :=
  phaseBlock_append largest_checked_2403_1_part9 largest_checked_2403_1_part10 rfl rfl rfl
private theorem largest_checked_2403_1_join7 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 1024 384 = 157481655876798846199437404928 :=
  phaseBlock_append largest_checked_2403_1_part8 largest_checked_2403_1_join6 rfl rfl rfl
private theorem largest_checked_2403_1_join8 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 640 768 = 364288774234873931996908238336 :=
  phaseBlock_append largest_checked_2403_1_join5 largest_checked_2403_1_join7 rfl rfl rfl
private theorem largest_checked_2403_1_join9 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 0 1408 = 828556250916461442650256405248 :=
  phaseBlock_append largest_checked_2403_1_join3 largest_checked_2403_1_join8 rfl rfl rfl
private theorem largest_checked_2403_1_join10 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 1408 256 = 79475290301909663226386256384 :=
  phaseBlock_append largest_checked_2403_1_part11 largest_checked_2403_1_part12 rfl rfl rfl
private theorem largest_checked_2403_1_join11 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 1792 256 = 51354845495665617227843359232 :=
  phaseBlock_append largest_checked_2403_1_part14 largest_checked_2403_1_part15 rfl rfl rfl
private theorem largest_checked_2403_1_join12 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 1664 384 = 83875906581605623678854236928 :=
  phaseBlock_append largest_checked_2403_1_part13 largest_checked_2403_1_join11 rfl rfl rfl
private theorem largest_checked_2403_1_join13 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 1408 640 = 163351196883515286905240493312 :=
  phaseBlock_append largest_checked_2403_1_join10 largest_checked_2403_1_join12 rfl rfl rfl
private theorem largest_checked_2403_1_join14 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 2176 256 = 25965834674421608756848529920 :=
  phaseBlock_append largest_checked_2403_1_part17 largest_checked_2403_1_part18 rfl rfl rfl
private theorem largest_checked_2403_1_join15 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 2048 384 = 45103121897576878707697396480 :=
  phaseBlock_append largest_checked_2403_1_part16 largest_checked_2403_1_join14 rfl rfl rfl
private theorem largest_checked_2403_1_join16 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 2560 190 = 3860765961895702171952993052 :=
  phaseBlock_append largest_checked_2403_1_part20 largest_checked_2403_1_part21 rfl rfl rfl
private theorem largest_checked_2403_1_join17 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 2432 318 = 11003003713470454241095109660 :=
  phaseBlock_append largest_checked_2403_1_part19 largest_checked_2403_1_join16 rfl rfl rfl
private theorem largest_checked_2403_1_join18 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 2048 702 = 56106125611047332948792506140 :=
  phaseBlock_append largest_checked_2403_1_join15 largest_checked_2403_1_join17 rfl rfl rfl
private theorem largest_checked_2403_1_join19 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 1408 1342 = 219457322494562619854032999452 :=
  phaseBlock_append largest_checked_2403_1_join13 largest_checked_2403_1_join18 rfl rfl rfl
private theorem largest_checked_2403_1_join20 :
    phaseBlock (fastLayer largestBank.shape 179798 2403 103 1 1 1 1) 0 2750 = 1048013573411024062504289404700 :=
  phaseBlock_append largest_checked_2403_1_join9 largest_checked_2403_1_join19 rfl rfl rfl

private theorem largest_checked_2403_1 : fastPhase largestBank.shape 179798 2403 103 1 1 1 1 = 1048013573411024062504289404700 :=
  phase_of_block (n := 2750) (by decide +kernel) largest_checked_2403_1_join20

theorem largest_checked : Checked largestBank 103 1 1 := by
  refine checked_from_values largestBank 103 1 1
    (P3_7_1.checked largestBank rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_12604_2749)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) largest_checked_2402_0 largest_checked_2402_1 largest_checked_2403_0 largest_checked_2403_1 (by decide +kernel) (by decide +kernel)


/-- The last stage of the high-jet rectangle, with no numerical premises. -/
theorem largest_avoids {h : ℕ} {D : K1_14_1.PoleData h} (Crt : K1_14_1.CRTLift D)
    (word : K1.I → K1_14.L) (lo : 2402≤h) (hi : h≤33619) {G : K1_14.Jet}
    (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (seed : 1≤K1_14_2_2_2_1.seedDegree G)
    (excess : G.natDegree+1≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word largestBank.shape (buffered largestBank h 103), ¬ G∣Q :=
  largest_checked.avoids Crt word lo hi irr seeded slope seed excess

#print axioms largest_checked
#print axioms largest_avoids

end Lower6960.RescueSource
