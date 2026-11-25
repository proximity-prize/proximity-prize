import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt0
import ProximityPrize.SubmissionLower.R6960RescueSourceLargest

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

private theorem receipt_0_16_2383_0_part0 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 0 128 = 890513268814382048661986894784 := by decide +kernel
private theorem receipt_0_16_2383_0_part1 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 128 128 = 835619098669583130358109602752 := by decide +kernel
private theorem receipt_0_16_2383_0_part2 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 256 128 = 781934399108328081482339361728 := by decide +kernel
private theorem receipt_0_16_2383_0_part3 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 384 128 = 729445571686158871660454659008 := by decide +kernel
private theorem receipt_0_16_2383_0_part4 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 512 128 = 678139034154441134923278771136 := by decide +kernel
private theorem receipt_0_16_2383_0_part5 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 640 128 = 628001220454075666883242820544 := by decide +kernel
private theorem receipt_0_16_2383_0_part6 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 768 128 = 579018580709209921910948832192 := by decide +kernel
private theorem receipt_0_16_2383_0_part7 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 896 128 = 531177581220949510311732790208 := by decide +kernel
private theorem receipt_0_16_2383_0_part8 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 1024 128 = 484464704461069695502227694528 := by decide +kernel
private theorem receipt_0_16_2383_0_part9 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 1152 128 = 438866449065726891186926617536 := by decide +kernel
private theorem receipt_0_16_2383_0_part10 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 1280 128 = 394369329829170158534745760704 := by decide +kernel
private theorem receipt_0_16_2383_0_part11 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 1408 128 = 350959877697452703355587511232 := by decide +kernel
private theorem receipt_0_16_2383_0_part12 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 1536 128 = 308624639762143373276903498688 := by decide +kernel
private theorem receipt_0_16_2383_0_part13 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 1664 128 = 267350179254038154920257651648 := by decide +kernel
private theorem receipt_0_16_2383_0_part14 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 1792 128 = 227123093522658390620205609082 := by decide +kernel
private theorem receipt_0_16_2383_0_part15 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 1920 128 = 187930022409361344257572117330 := by decide +kernel
private theorem receipt_0_16_2383_0_part16 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 2048 128 = 149757547145111018338303659168 := by decide +kernel
private theorem receipt_0_16_2383_0_part17 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 2176 128 = 112592249429539340798740379078 := by decide +kernel
private theorem receipt_0_16_2383_0_part18 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 2304 128 = 76420727160116056352757080522 := by decide +kernel
private theorem receipt_0_16_2383_0_part19 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 2432 128 = 41229594399128705247672584806 := by decide +kernel
private theorem receipt_0_16_2383_0_part20 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 2560 90 = 8440940978277938612418068502 := by decide +kernel
private theorem receipt_0_16_2383_0_join0 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 0 256 = 1726132367483965179020096497536 :=
  phaseBlock_append receipt_0_16_2383_0_part0 receipt_0_16_2383_0_part1 rfl rfl rfl
private theorem receipt_0_16_2383_0_join1 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 384 256 = 1407584605840600006583733430144 :=
  phaseBlock_append receipt_0_16_2383_0_part3 receipt_0_16_2383_0_part4 rfl rfl rfl
private theorem receipt_0_16_2383_0_join2 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 256 384 = 2189519004948928088066072791872 :=
  phaseBlock_append receipt_0_16_2383_0_part2 receipt_0_16_2383_0_join1 rfl rfl rfl
private theorem receipt_0_16_2383_0_join3 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 0 640 = 3915651372432893267086169289408 :=
  phaseBlock_append receipt_0_16_2383_0_join0 receipt_0_16_2383_0_join2 rfl rfl rfl
private theorem receipt_0_16_2383_0_join4 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 640 256 = 1207019801163285588794191652736 :=
  phaseBlock_append receipt_0_16_2383_0_part5 receipt_0_16_2383_0_part6 rfl rfl rfl
private theorem receipt_0_16_2383_0_join5 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 1024 256 = 923331153526796586689154312064 :=
  phaseBlock_append receipt_0_16_2383_0_part8 receipt_0_16_2383_0_part9 rfl rfl rfl
private theorem receipt_0_16_2383_0_join6 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 896 384 = 1454508734747746097000887102272 :=
  phaseBlock_append receipt_0_16_2383_0_part7 receipt_0_16_2383_0_join5 rfl rfl rfl
private theorem receipt_0_16_2383_0_join7 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 640 640 = 2661528535911031685795078755008 :=
  phaseBlock_append receipt_0_16_2383_0_join4 receipt_0_16_2383_0_join6 rfl rfl rfl
private theorem receipt_0_16_2383_0_join8 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 0 1280 = 6577179908343924952881248044416 :=
  phaseBlock_append receipt_0_16_2383_0_join3 receipt_0_16_2383_0_join7 rfl rfl rfl
private theorem receipt_0_16_2383_0_join9 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 1280 256 = 745329207526622861890333271936 :=
  phaseBlock_append receipt_0_16_2383_0_part10 receipt_0_16_2383_0_part11 rfl rfl rfl
private theorem receipt_0_16_2383_0_join10 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 1664 256 = 494473272776696545540463260730 :=
  phaseBlock_append receipt_0_16_2383_0_part13 receipt_0_16_2383_0_part14 rfl rfl rfl
private theorem receipt_0_16_2383_0_join11 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 1536 384 = 803097912538839918817366759418 :=
  phaseBlock_append receipt_0_16_2383_0_part12 receipt_0_16_2383_0_join10 rfl rfl rfl
private theorem receipt_0_16_2383_0_join12 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 1280 640 = 1548427120065462780707700031354 :=
  phaseBlock_append receipt_0_16_2383_0_join9 receipt_0_16_2383_0_join11 rfl rfl rfl
private theorem receipt_0_16_2383_0_join13 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 2048 256 = 262349796574650359137044038246 :=
  phaseBlock_append receipt_0_16_2383_0_part16 receipt_0_16_2383_0_part17 rfl rfl rfl
private theorem receipt_0_16_2383_0_join14 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 1920 384 = 450279818984011703394616155576 :=
  phaseBlock_append receipt_0_16_2383_0_part15 receipt_0_16_2383_0_join13 rfl rfl rfl
private theorem receipt_0_16_2383_0_join15 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 2432 218 = 49670535377406643860090653308 :=
  phaseBlock_append receipt_0_16_2383_0_part19 receipt_0_16_2383_0_part20 rfl rfl rfl
private theorem receipt_0_16_2383_0_join16 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 2304 346 = 126091262537522700212847733830 :=
  phaseBlock_append receipt_0_16_2383_0_part18 receipt_0_16_2383_0_join15 rfl rfl rfl
private theorem receipt_0_16_2383_0_join17 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 1920 730 = 576371081521534403607463889406 :=
  phaseBlock_append receipt_0_16_2383_0_join14 receipt_0_16_2383_0_join16 rfl rfl rfl
private theorem receipt_0_16_2383_0_join18 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 1280 1370 = 2124798201586997184315163920760 :=
  phaseBlock_append receipt_0_16_2383_0_join12 receipt_0_16_2383_0_join17 rfl rfl rfl
private theorem receipt_0_16_2383_0_join19 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 0) 0 2650 = 8701978109930922137196411965176 :=
  phaseBlock_append receipt_0_16_2383_0_join8 receipt_0_16_2383_0_join18 rfl rfl rfl

private theorem receipt_0_16_2383_0 : fastPhase (bank 0 16).shape 179808 2383 103 1 0 1 0 = 8701978109930922137196411965176 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_0_16_2383_0_join19

private theorem receipt_0_16_2383_1_part0 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 0 128 = 890085455821455289335179744128 := by decide +kernel
private theorem receipt_0_16_2383_1_part1 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 128 128 = 835200468810987082966858191744 := by decide +kernel
private theorem receipt_0_16_2383_1_part2 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 256 128 = 781524849533488682599889638272 := by decide +kernel
private theorem receipt_0_16_2383_1_part3 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 384 128 = 729044999667914162015215571840 := by decide +kernel
private theorem receipt_0_16_2383_1_part4 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 512 128 = 677747337088993113021592540032 := by decide +kernel
private theorem receipt_0_16_2383_1_part5 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 640 128 = 627618295860942142632155206528 := by decide +kernel
private theorem receipt_0_16_2383_1_part6 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 768 128 = 578644326231176370240979407744 := by decide +kernel
private theorem receipt_0_16_2383_1_part7 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 896 128 = 530811894624020924799645209472 := by decide +kernel
private theorem receipt_0_16_2383_1_part8 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 1024 128 = 484107483634422441993799963520 := by decide +kernel
private theorem receipt_0_16_2383_1_part9 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 1152 128 = 438517592021660561419721364352 := by decide +kernel
private theorem receipt_0_16_2383_1_part10 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 1280 128 = 394028734703059423760880505728 := by decide +kernel
private theorem receipt_0_16_2383_1_part11 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 1408 128 = 350627442747699167964504937344 := by decide +kernel
private theorem receipt_0_16_2383_1_part12 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 1536 128 = 308300263370127428418141721472 := by decide +kernel
private theorem receipt_0_16_2383_1_part13 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 1664 128 = 267033759924070832126220489600 := by decide +kernel
private theorem receipt_0_16_2383_1_part14 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 1792 128 = 226814529858306725021548831348 := by decide +kernel
private theorem receipt_0_16_2383_1_part15 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 1920 128 = 187629213057073355293167140514 := by decide +kernel
private theorem receipt_0_16_2383_1_part16 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 2048 128 = 149464390857951608459803750380 := by decide +kernel
private theorem receipt_0_16_2383_1_part17 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 2176 128 = 112306645083576701124627236582 := by decide +kernel
private theorem receipt_0_16_2383_1_part18 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 2304 128 = 76142573754339958370910390940 := by decide +kernel
private theorem receipt_0_16_2383_1_part19 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 2432 128 = 40958791055359319254929856536 := by decide +kernel
private theorem receipt_0_16_2383_1_part20 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 2560 90 = 8254878899955420562341619380 := by decide +kernel
private theorem receipt_0_16_2383_1_join0 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 0 256 = 1725285924632442372302037935872 :=
  phaseBlock_append receipt_0_16_2383_1_part0 receipt_0_16_2383_1_part1 rfl rfl rfl
private theorem receipt_0_16_2383_1_join1 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 384 256 = 1406792336756907275036808111872 :=
  phaseBlock_append receipt_0_16_2383_1_part3 receipt_0_16_2383_1_part4 rfl rfl rfl
private theorem receipt_0_16_2383_1_join2 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 256 384 = 2188317186290395957636697750144 :=
  phaseBlock_append receipt_0_16_2383_1_part2 receipt_0_16_2383_1_join1 rfl rfl rfl
private theorem receipt_0_16_2383_1_join3 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 0 640 = 3913603110922838329938735686016 :=
  phaseBlock_append receipt_0_16_2383_1_join0 receipt_0_16_2383_1_join2 rfl rfl rfl
private theorem receipt_0_16_2383_1_join4 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 640 256 = 1206262622092118512873134614272 :=
  phaseBlock_append receipt_0_16_2383_1_part5 receipt_0_16_2383_1_part6 rfl rfl rfl
private theorem receipt_0_16_2383_1_join5 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 1024 256 = 922625075656083003413521327872 :=
  phaseBlock_append receipt_0_16_2383_1_part8 receipt_0_16_2383_1_part9 rfl rfl rfl
private theorem receipt_0_16_2383_1_join6 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 896 384 = 1453436970280103928213166537344 :=
  phaseBlock_append receipt_0_16_2383_1_part7 receipt_0_16_2383_1_join5 rfl rfl rfl
private theorem receipt_0_16_2383_1_join7 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 640 640 = 2659699592372222441086301151616 :=
  phaseBlock_append receipt_0_16_2383_1_join4 receipt_0_16_2383_1_join6 rfl rfl rfl
private theorem receipt_0_16_2383_1_join8 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 0 1280 = 6573302703295060771025036837632 :=
  phaseBlock_append receipt_0_16_2383_1_join3 receipt_0_16_2383_1_join7 rfl rfl rfl
private theorem receipt_0_16_2383_1_join9 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 1280 256 = 744656177450758591725385443072 :=
  phaseBlock_append receipt_0_16_2383_1_part10 receipt_0_16_2383_1_part11 rfl rfl rfl
private theorem receipt_0_16_2383_1_join10 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 1664 256 = 493848289782377557147769320948 :=
  phaseBlock_append receipt_0_16_2383_1_part13 receipt_0_16_2383_1_part14 rfl rfl rfl
private theorem receipt_0_16_2383_1_join11 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 1536 384 = 802148553152504985565911042420 :=
  phaseBlock_append receipt_0_16_2383_1_part12 receipt_0_16_2383_1_join10 rfl rfl rfl
private theorem receipt_0_16_2383_1_join12 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 1280 640 = 1546804730603263577291296485492 :=
  phaseBlock_append receipt_0_16_2383_1_join9 receipt_0_16_2383_1_join11 rfl rfl rfl
private theorem receipt_0_16_2383_1_join13 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 2048 256 = 261771035941528309584430986962 :=
  phaseBlock_append receipt_0_16_2383_1_part16 receipt_0_16_2383_1_part17 rfl rfl rfl
private theorem receipt_0_16_2383_1_join14 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 1920 384 = 449400248998601664877598127476 :=
  phaseBlock_append receipt_0_16_2383_1_part15 receipt_0_16_2383_1_join13 rfl rfl rfl
private theorem receipt_0_16_2383_1_join15 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 2432 218 = 49213669955314739817271475916 :=
  phaseBlock_append receipt_0_16_2383_1_part19 receipt_0_16_2383_1_part20 rfl rfl rfl
private theorem receipt_0_16_2383_1_join16 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 2304 346 = 125356243709654698188181866856 :=
  phaseBlock_append receipt_0_16_2383_1_part18 receipt_0_16_2383_1_join15 rfl rfl rfl
private theorem receipt_0_16_2383_1_join17 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 1920 730 = 574756492708256363065779994332 :=
  phaseBlock_append receipt_0_16_2383_1_join14 receipt_0_16_2383_1_join16 rfl rfl rfl
private theorem receipt_0_16_2383_1_join18 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 1280 1370 = 2121561223311519940357076479824 :=
  phaseBlock_append receipt_0_16_2383_1_join12 receipt_0_16_2383_1_join17 rfl rfl rfl
private theorem receipt_0_16_2383_1_join19 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2383 103 1 0 1 1) 0 2650 = 8694863926606580711382113317456 :=
  phaseBlock_append receipt_0_16_2383_1_join8 receipt_0_16_2383_1_join18 rfl rfl rfl

private theorem receipt_0_16_2383_1 : fastPhase (bank 0 16).shape 179808 2383 103 1 0 1 1 = 8694863926606580711382113317456 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_0_16_2383_1_join19

private theorem receipt_0_16_2384_0_part0 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 0 128 = 890521291381002462039050155104 := by decide +kernel
private theorem receipt_0_16_2384_0_part1 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 128 128 = 835626424737483622016049243232 := by decide +kernel
private theorem receipt_0_16_2384_0_part2 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 256 128 = 781941062694084639458174620768 := by decide +kernel
private theorem receipt_0_16_2384_0_part3 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 384 128 = 729451606338155617155989455968 := by decide +kernel
private theorem receipt_0_16_2384_0_part4 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 512 128 = 678144472953434403552908784736 := by decide +kernel
private theorem receipt_0_16_2384_0_part5 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 640 128 = 628006096013757870019437012064 := by decide +kernel
private theorem receipt_0_16_2384_0_part6 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 768 128 = 579022925176773188127405413472 := by decide +kernel
private theorem receipt_0_16_2384_0_part7 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 896 128 = 531181426277649106924209636448 := by decide +kernel
private theorem receipt_0_16_2384_0_part8 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 1024 128 = 484468081322787230207047201888 := by decide +kernel
private theorem receipt_0_16_2384_0_part9 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 1152 128 = 438869388483533293797155005536 := by decide +kernel
private theorem receipt_0_16_2384_0_part10 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 1280 128 = 394371862089888442814046819424 := by decide +kernel
private theorem receipt_0_16_2384_0_part11 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 1408 128 = 350962032624220508949750793312 := by decide +kernel
private theorem receipt_0_16_2384_0_part12 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 1536 128 = 308626446714975287743046956128 := by decide +kernel
private theorem receipt_0_16_2384_0_part13 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 1664 128 = 267351667130387815853704717408 := by decide +kernel
private theorem receipt_0_16_2384_0_part14 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 1792 128 = 227124290028134577847439874412 := by decide +kernel
private theorem receipt_0_16_2384_0_part15 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 1920 128 = 187930955285980814276930464400 := by decide +kernel
private theorem receipt_0_16_2384_0_part16 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 2048 128 = 149758244374758978137244424955 := by decide +kernel
private theorem receipt_0_16_2384_0_part17 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 2176 128 = 112592738491457127242968070083 := by decide +kernel
private theorem receipt_0_16_2384_0_part18 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 2304 128 = 76421035048460717556246087568 := by decide +kernel
private theorem receipt_0_16_2384_0_part19 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 2432 128 = 41229747599591992832561108673 := by decide +kernel
private theorem receipt_0_16_2384_0_part20 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 2560 90 = 8440970117758107471338524350 := by decide +kernel
private theorem receipt_0_16_2384_0_join0 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 0 256 = 1726147716118486084055099398336 :=
  phaseBlock_append receipt_0_16_2384_0_part0 receipt_0_16_2384_0_part1 rfl rfl rfl
private theorem receipt_0_16_2384_0_join1 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 384 256 = 1407596079291590020708898240704 :=
  phaseBlock_append receipt_0_16_2384_0_part3 receipt_0_16_2384_0_part4 rfl rfl rfl
private theorem receipt_0_16_2384_0_join2 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 256 384 = 2189537141985674660167072861472 :=
  phaseBlock_append receipt_0_16_2384_0_part2 receipt_0_16_2384_0_join1 rfl rfl rfl
private theorem receipt_0_16_2384_0_join3 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 0 640 = 3915684858104160744222172259808 :=
  phaseBlock_append receipt_0_16_2384_0_join0 receipt_0_16_2384_0_join2 rfl rfl rfl
private theorem receipt_0_16_2384_0_join4 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 640 256 = 1207029021190531058146842425536 :=
  phaseBlock_append receipt_0_16_2384_0_part5 receipt_0_16_2384_0_part6 rfl rfl rfl
private theorem receipt_0_16_2384_0_join5 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 1024 256 = 923337469806320524004202207424 :=
  phaseBlock_append receipt_0_16_2384_0_part8 receipt_0_16_2384_0_part9 rfl rfl rfl
private theorem receipt_0_16_2384_0_join6 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 896 384 = 1454518896083969630928411843872 :=
  phaseBlock_append receipt_0_16_2384_0_part7 receipt_0_16_2384_0_join5 rfl rfl rfl
private theorem receipt_0_16_2384_0_join7 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 640 640 = 2661547917274500689075254269408 :=
  phaseBlock_append receipt_0_16_2384_0_join4 receipt_0_16_2384_0_join6 rfl rfl rfl
private theorem receipt_0_16_2384_0_join8 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 0 1280 = 6577232775378661433297426529216 :=
  phaseBlock_append receipt_0_16_2384_0_join3 receipt_0_16_2384_0_join7 rfl rfl rfl
private theorem receipt_0_16_2384_0_join9 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 1280 256 = 745333894714108951763797612736 :=
  phaseBlock_append receipt_0_16_2384_0_part10 receipt_0_16_2384_0_part11 rfl rfl rfl
private theorem receipt_0_16_2384_0_join10 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 1664 256 = 494475957158522393701144591820 :=
  phaseBlock_append receipt_0_16_2384_0_part13 receipt_0_16_2384_0_part14 rfl rfl rfl
private theorem receipt_0_16_2384_0_join11 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 1536 384 = 803102403873497681444191547948 :=
  phaseBlock_append receipt_0_16_2384_0_part12 receipt_0_16_2384_0_join10 rfl rfl rfl
private theorem receipt_0_16_2384_0_join12 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 1280 640 = 1548436298587606633207989160684 :=
  phaseBlock_append receipt_0_16_2384_0_join9 receipt_0_16_2384_0_join11 rfl rfl rfl
private theorem receipt_0_16_2384_0_join13 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 2048 256 = 262350982866216105380212495038 :=
  phaseBlock_append receipt_0_16_2384_0_part16 receipt_0_16_2384_0_part17 rfl rfl rfl
private theorem receipt_0_16_2384_0_join14 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 1920 384 = 450281938152196919657142959438 :=
  phaseBlock_append receipt_0_16_2384_0_part15 receipt_0_16_2384_0_join13 rfl rfl rfl
private theorem receipt_0_16_2384_0_join15 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 2432 218 = 49670717717350100303899633023 :=
  phaseBlock_append receipt_0_16_2384_0_part19 receipt_0_16_2384_0_part20 rfl rfl rfl
private theorem receipt_0_16_2384_0_join16 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 2304 346 = 126091752765810817860145720591 :=
  phaseBlock_append receipt_0_16_2384_0_part18 receipt_0_16_2384_0_join15 rfl rfl rfl
private theorem receipt_0_16_2384_0_join17 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 1920 730 = 576373690918007737517288680029 :=
  phaseBlock_append receipt_0_16_2384_0_join14 receipt_0_16_2384_0_join16 rfl rfl rfl
private theorem receipt_0_16_2384_0_join18 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 1280 1370 = 2124809989505614370725277840713 :=
  phaseBlock_append receipt_0_16_2384_0_join12 receipt_0_16_2384_0_join17 rfl rfl rfl
private theorem receipt_0_16_2384_0_join19 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 0) 0 2650 = 8702042764884275804022704369929 :=
  phaseBlock_append receipt_0_16_2384_0_join8 receipt_0_16_2384_0_join18 rfl rfl rfl

private theorem receipt_0_16_2384_0 : fastPhase (bank 0 16).shape 179808 2384 103 1 0 1 0 = 8702042764884275804022704369929 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_0_16_2384_0_join19

private theorem receipt_0_16_2384_1_part0 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 0 128 = 890093475235088514379343861088 := by decide +kernel
private theorem receipt_0_16_2384_1_part1 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 128 128 = 835207791859773807288236033376 := by decide +kernel
private theorem receipt_0_16_2384_1_part2 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 256 128 = 781531510231792738645018637664 := by decide +kernel
private theorem receipt_0_16_2384_1_part3 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 384 128 = 729051031561910604567288489312 := by decide +kernel
private theorem receipt_0_16_2384_1_part4 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 512 128 = 677752773257232299142594483552 := by decide +kernel
private theorem receipt_0_16_2384_1_part5 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 640 128 = 627623168914913591702675096928 := by decide +kernel
private theorem receipt_0_16_2384_1_part6 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 768 128 = 578648668315872404097695888736 := by decide +kernel
private theorem receipt_0_16_2384_1_part7 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 896 128 = 530815737418500087970487002464 := by decide +kernel
private theorem receipt_0_16_2384_1_part8 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 1024 128 = 484110858352372702030780667232 := by decide +kernel
private theorem receipt_0_16_2384_1_part9 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 1152 128 = 438520529411962289329448699232 := by decide +kernel
private theorem receipt_0_16_2384_1_part10 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 1280 128 = 394031265050348154532740003168 := by decide +kernel
private theorem receipt_0_16_2384_1_part11 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 1408 128 = 350629595872928141196518073696 := by decide +kernel
private theorem receipt_0_16_2384_1_part12 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 1536 128 = 308302068631129909040498496864 := by decide +kernel
private theorem receipt_0_16_2384_1_part13 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 1664 128 = 267035246216122211222486451552 := by decide +kernel
private theorem receipt_0_16_2384_1_part14 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 1792 128 = 226815724885785203606629446317 := by decide +kernel
private theorem receipt_0_16_2384_1_part15 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 1920 128 = 187630144560503428383678205138 := by decide +kernel
private theorem receipt_0_16_2384_1_part16 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 2048 128 = 149465086816947920179752444400 := by decide +kernel
private theorem receipt_0_16_2384_1_part17 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 2176 128 = 112307132975125839188996018324 := by decide +kernel
private theorem receipt_0_16_2384_1_part18 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 2304 128 = 76142880570316168175320122939 := by decide +kernel
private theorem receipt_0_16_2384_1_part19 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 2432 128 = 40958943279191794327252648766 := by decide +kernel
private theorem receipt_0_16_2384_1_part20 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 2560 90 = 8254907408853635470804888584 := by decide +kernel
private theorem receipt_0_16_2384_1_join0 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 0 256 = 1725301267094862321667579894464 :=
  phaseBlock_append receipt_0_16_2384_1_part0 receipt_0_16_2384_1_part1 rfl rfl rfl
private theorem receipt_0_16_2384_1_join1 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 384 256 = 1406803804819142903709882972864 :=
  phaseBlock_append receipt_0_16_2384_1_part3 receipt_0_16_2384_1_part4 rfl rfl rfl
private theorem receipt_0_16_2384_1_join2 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 256 384 = 2188335315050935642354901610528 :=
  phaseBlock_append receipt_0_16_2384_1_part2 receipt_0_16_2384_1_join1 rfl rfl rfl
private theorem receipt_0_16_2384_1_join3 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 0 640 = 3913636582145797964022481504992 :=
  phaseBlock_append receipt_0_16_2384_1_join0 receipt_0_16_2384_1_join2 rfl rfl rfl
private theorem receipt_0_16_2384_1_join4 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 640 256 = 1206271837230785995800370985664 :=
  phaseBlock_append receipt_0_16_2384_1_part5 receipt_0_16_2384_1_part6 rfl rfl rfl
private theorem receipt_0_16_2384_1_join5 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 1024 256 = 922631387764334991360229366464 :=
  phaseBlock_append receipt_0_16_2384_1_part8 receipt_0_16_2384_1_part9 rfl rfl rfl
private theorem receipt_0_16_2384_1_join6 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 896 384 = 1453447125182835079330716368928 :=
  phaseBlock_append receipt_0_16_2384_1_part7 receipt_0_16_2384_1_join5 rfl rfl rfl
private theorem receipt_0_16_2384_1_join7 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 640 640 = 2659718962413621075131087354592 :=
  phaseBlock_append receipt_0_16_2384_1_join4 receipt_0_16_2384_1_join6 rfl rfl rfl
private theorem receipt_0_16_2384_1_join8 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 0 1280 = 6573355544559419039153568859584 :=
  phaseBlock_append receipt_0_16_2384_1_join3 receipt_0_16_2384_1_join7 rfl rfl rfl
private theorem receipt_0_16_2384_1_join9 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 1280 256 = 744660860923276295729258076864 :=
  phaseBlock_append receipt_0_16_2384_1_part10 receipt_0_16_2384_1_part11 rfl rfl rfl
private theorem receipt_0_16_2384_1_join10 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 1664 256 = 493850971101907414829115897869 :=
  phaseBlock_append receipt_0_16_2384_1_part13 receipt_0_16_2384_1_part14 rfl rfl rfl
private theorem receipt_0_16_2384_1_join11 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 1536 384 = 802153039733037323869614394733 :=
  phaseBlock_append receipt_0_16_2384_1_part12 receipt_0_16_2384_1_join10 rfl rfl rfl
private theorem receipt_0_16_2384_1_join12 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 1280 640 = 1546813900656313619598872471597 :=
  phaseBlock_append receipt_0_16_2384_1_join9 receipt_0_16_2384_1_join11 rfl rfl rfl
private theorem receipt_0_16_2384_1_join13 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 2048 256 = 261772219792073759368748462724 :=
  phaseBlock_append receipt_0_16_2384_1_part16 receipt_0_16_2384_1_part17 rfl rfl rfl
private theorem receipt_0_16_2384_1_join14 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 1920 384 = 449402364352577187752426667862 :=
  phaseBlock_append receipt_0_16_2384_1_part15 receipt_0_16_2384_1_join13 rfl rfl rfl
private theorem receipt_0_16_2384_1_join15 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 2432 218 = 49213850688045429798057537350 :=
  phaseBlock_append receipt_0_16_2384_1_part19 receipt_0_16_2384_1_part20 rfl rfl rfl
private theorem receipt_0_16_2384_1_join16 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 2304 346 = 125356731258361597973377660289 :=
  phaseBlock_append receipt_0_16_2384_1_part18 receipt_0_16_2384_1_join15 rfl rfl rfl
private theorem receipt_0_16_2384_1_join17 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 1920 730 = 574759095610938785725804328151 :=
  phaseBlock_append receipt_0_16_2384_1_join14 receipt_0_16_2384_1_join16 rfl rfl rfl
private theorem receipt_0_16_2384_1_join18 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 1280 1370 = 2121572996267252405324676799748 :=
  phaseBlock_append receipt_0_16_2384_1_join12 receipt_0_16_2384_1_join17 rfl rfl rfl
private theorem receipt_0_16_2384_1_join19 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2384 103 1 0 1 1) 0 2650 = 8694928540826671444478245659332 :=
  phaseBlock_append receipt_0_16_2384_1_join8 receipt_0_16_2384_1_join18 rfl rfl rfl

private theorem receipt_0_16_2384_1 : fastPhase (bank 0 16).shape 179808 2384 103 1 0 1 1 = 8694928540826671444478245659332 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_0_16_2384_1_join19

theorem receipt_0_16 : Checked (bank 0 16) 103 0 1 := by
  refine checked_from_values (bank 0 16) 103 0 1
    (P3_7_1.checked (bank 0 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_12604_2649)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_16_2383_0 receipt_0_16_2383_1 receipt_0_16_2384_0 receipt_0_16_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_16_2383_0_part0 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 0 128 = 801755244859266558361016816064 := by decide +kernel
private theorem receipt_1_16_2383_0_part1 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 128 128 = 752067907579503963795713847744 := by decide +kernel
private theorem receipt_1_16_2383_0_part2 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 256 128 = 703503449334281675142715642304 := by decide +kernel
private theorem receipt_1_16_2383_0_part3 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 384 128 = 656048498266306380647053439424 := by decide +kernel
private theorem receipt_1_16_2383_0_part4 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 512 128 = 609689713981731048908737597888 := by decide +kernel
private theorem receipt_1_16_2383_0_part5 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 640 128 = 564413787525000917589009822144 := by decide +kernel
private theorem receipt_1_16_2383_0_part6 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 768 128 = 520207441353699482116595388864 := by decide +kernel
private theorem receipt_1_16_2383_0_part7 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 896 128 = 477057429313394484393955373504 := by decide +kernel
private theorem receipt_1_16_2383_0_part8 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 1024 128 = 434950536612483901503538876864 := by decide +kernel
private theorem receipt_1_16_2383_0_part9 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 1152 128 = 393873579797041934414035251648 := by decide +kernel
private theorem receipt_1_16_2383_0_part10 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 1280 128 = 353813406725664996686626329024 := by decide +kernel
private theorem receipt_1_16_2383_0_part11 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 1408 128 = 314756896544317703181238645184 := by decide +kernel
private theorem receipt_1_16_2383_0_part12 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 1536 128 = 276690959661178858762795667904 := by decide +kernel
private theorem receipt_1_16_2383_0_part13 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 1664 128 = 239602537721487447007470023104 := by decide +kernel
private theorem receipt_1_16_2383_0_part14 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 1792 128 = 203478619694378897493206243428 := by decide +kernel
private theorem receipt_1_16_2383_0_part15 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 1920 128 = 168306249327390453176430258034 := by decide +kernel
private theorem receipt_1_16_2383_0_part16 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 2048 128 = 134072434570327733407058646669 := by decide +kernel
private theorem receipt_1_16_2383_0_part17 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 2176 128 = 100764200544946957107841001900 := by decide +kernel
private theorem receipt_1_16_2383_0_part18 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 2304 128 = 68368603623279591388012175747 := by decide +kernel
private theorem receipt_1_16_2383_0_part19 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 2432 128 = 36872731378443497746656841078 := by decide +kernel
private theorem receipt_1_16_2383_0_part20 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 2560 90 = 7546801575424972936623624852 := by decide +kernel
private theorem receipt_1_16_2383_0_join0 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 0 256 = 1553823152438770522156730663808 :=
  phaseBlock_append receipt_1_16_2383_0_part0 receipt_1_16_2383_0_part1 rfl rfl rfl
private theorem receipt_1_16_2383_0_join1 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 384 256 = 1265738212248037429555791037312 :=
  phaseBlock_append receipt_1_16_2383_0_part3 receipt_1_16_2383_0_part4 rfl rfl rfl
private theorem receipt_1_16_2383_0_join2 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 256 384 = 1969241661582319104698506679616 :=
  phaseBlock_append receipt_1_16_2383_0_part2 receipt_1_16_2383_0_join1 rfl rfl rfl
private theorem receipt_1_16_2383_0_join3 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 0 640 = 3523064814021089626855237343424 :=
  phaseBlock_append receipt_1_16_2383_0_join0 receipt_1_16_2383_0_join2 rfl rfl rfl
private theorem receipt_1_16_2383_0_join4 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 640 256 = 1084621228878700399705605211008 :=
  phaseBlock_append receipt_1_16_2383_0_part5 receipt_1_16_2383_0_part6 rfl rfl rfl
private theorem receipt_1_16_2383_0_join5 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 1024 256 = 828824116409525835917574128512 :=
  phaseBlock_append receipt_1_16_2383_0_part8 receipt_1_16_2383_0_part9 rfl rfl rfl
private theorem receipt_1_16_2383_0_join6 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 896 384 = 1305881545722920320311529502016 :=
  phaseBlock_append receipt_1_16_2383_0_part7 receipt_1_16_2383_0_join5 rfl rfl rfl
private theorem receipt_1_16_2383_0_join7 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 640 640 = 2390502774601620720017134713024 :=
  phaseBlock_append receipt_1_16_2383_0_join4 receipt_1_16_2383_0_join6 rfl rfl rfl
private theorem receipt_1_16_2383_0_join8 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 0 1280 = 5913567588622710346872372056448 :=
  phaseBlock_append receipt_1_16_2383_0_join3 receipt_1_16_2383_0_join7 rfl rfl rfl
private theorem receipt_1_16_2383_0_join9 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 1280 256 = 668570303269982699867864974208 :=
  phaseBlock_append receipt_1_16_2383_0_part10 receipt_1_16_2383_0_part11 rfl rfl rfl
private theorem receipt_1_16_2383_0_join10 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 1664 256 = 443081157415866344500676266532 :=
  phaseBlock_append receipt_1_16_2383_0_part13 receipt_1_16_2383_0_part14 rfl rfl rfl
private theorem receipt_1_16_2383_0_join11 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 1536 384 = 719772117077045203263471934436 :=
  phaseBlock_append receipt_1_16_2383_0_part12 receipt_1_16_2383_0_join10 rfl rfl rfl
private theorem receipt_1_16_2383_0_join12 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 1280 640 = 1388342420347027903131336908644 :=
  phaseBlock_append receipt_1_16_2383_0_join9 receipt_1_16_2383_0_join11 rfl rfl rfl
private theorem receipt_1_16_2383_0_join13 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 2048 256 = 234836635115274690514899648569 :=
  phaseBlock_append receipt_1_16_2383_0_part16 receipt_1_16_2383_0_part17 rfl rfl rfl
private theorem receipt_1_16_2383_0_join14 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 1920 384 = 403142884442665143691329906603 :=
  phaseBlock_append receipt_1_16_2383_0_part15 receipt_1_16_2383_0_join13 rfl rfl rfl
private theorem receipt_1_16_2383_0_join15 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 2432 218 = 44419532953868470683280465930 :=
  phaseBlock_append receipt_1_16_2383_0_part19 receipt_1_16_2383_0_part20 rfl rfl rfl
private theorem receipt_1_16_2383_0_join16 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 2304 346 = 112788136577148062071292641677 :=
  phaseBlock_append receipt_1_16_2383_0_part18 receipt_1_16_2383_0_join15 rfl rfl rfl
private theorem receipt_1_16_2383_0_join17 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 1920 730 = 515931021019813205762622548280 :=
  phaseBlock_append receipt_1_16_2383_0_join14 receipt_1_16_2383_0_join16 rfl rfl rfl
private theorem receipt_1_16_2383_0_join18 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 1280 1370 = 1904273441366841108893959456924 :=
  phaseBlock_append receipt_1_16_2383_0_join12 receipt_1_16_2383_0_join17 rfl rfl rfl
private theorem receipt_1_16_2383_0_join19 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 0) 0 2650 = 7817841029989551455766331513372 :=
  phaseBlock_append receipt_1_16_2383_0_join8 receipt_1_16_2383_0_join18 rfl rfl rfl

private theorem receipt_1_16_2383_0 : fastPhase (bank 1 16).shape 179808 2383 103 1 0 2 0 = 7817841029989551455766331513372 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_1_16_2383_0_join19

private theorem receipt_1_16_2383_1_part0 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 0 128 = 801367871260192273442957985280 := by decide +kernel
private theorem receipt_1_16_2383_1_part1 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 128 128 = 751689069809680160883078661632 := by decide +kernel
private theorem receipt_1_16_2383_1_part2 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 256 128 = 703133046109568021415510246912 := by decide +kernel
private theorem receipt_1_16_2383_1_part3 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 384 128 = 655686428542407245288481359360 := by decide +kernel
private theorem receipt_1_16_2383_1_part4 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 512 128 = 609335876954002917596280817152 := by decide +kernel
private theorem receipt_1_16_2383_1_part5 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 640 128 = 564068082628259806985509864960 := by decide +kernel
private theorem receipt_1_16_2383_1_part6 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 768 128 = 519869768262028354361334400512 := by decide +kernel
private theorem receipt_1_16_2383_1_part7 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 896 128 = 476727687939950661593737201152 := by decide +kernel
private theorem receipt_1_16_2383_1_part8 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 1024 128 = 434628627109306480223770150400 := by decide +kernel
private theorem receipt_1_16_2383_1_part9 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 1152 128 = 393559402554859200169806464512 := by decide +kernel
private theorem receipt_1_16_2383_1_part10 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 1280 128 = 353506862373701838433792919040 := by decide +kernel
private theorem receipt_1_16_2383_1_part11 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 1408 128 = 314457885950103027807502075392 := by decide +kernel
private theorem receipt_1_16_2383_1_part12 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 1536 128 = 276399383930353005578784507392 := by decide +kernel
private theorem receipt_1_16_2383_1_part13 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 1664 128 = 239318298197609602237821027840 := by decide +kernel
private theorem receipt_1_16_2383_1_part14 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 1792 128 = 203201617937525009435473444327 := by decide +kernel
private theorem receipt_1_16_2383_1_part15 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 1920 128 = 168036387063478344064296571590 := by decide +kernel
private theorem receipt_1_16_2383_1_part16 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 2048 128 = 133809613748313117406989915702 := by decide +kernel
private theorem receipt_1_16_2383_1_part17 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 2176 128 = 100508323351399511056733607413 := by decide +kernel
private theorem receipt_1_16_2383_1_part18 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 2304 128 = 68119572482159873641667780968 := by decide +kernel
private theorem receipt_1_16_2383_1_part19 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 2432 128 = 36630448950871527755010387177 := by decide +kernel
private theorem receipt_1_16_2383_1_part20 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 2560 90 = 7380435172474495736628701811 := by decide +kernel
private theorem receipt_1_16_2383_1_join0 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 0 256 = 1553056941069872434326036646912 :=
  phaseBlock_append receipt_1_16_2383_1_part0 receipt_1_16_2383_1_part1 rfl rfl rfl
private theorem receipt_1_16_2383_1_join1 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 384 256 = 1265022305496410162884762176512 :=
  phaseBlock_append receipt_1_16_2383_1_part3 receipt_1_16_2383_1_part4 rfl rfl rfl
private theorem receipt_1_16_2383_1_join2 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 256 384 = 1968155351605978184300272423424 :=
  phaseBlock_append receipt_1_16_2383_1_part2 receipt_1_16_2383_1_join1 rfl rfl rfl
private theorem receipt_1_16_2383_1_join3 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 0 640 = 3521212292675850618626309070336 :=
  phaseBlock_append receipt_1_16_2383_1_join0 receipt_1_16_2383_1_join2 rfl rfl rfl
private theorem receipt_1_16_2383_1_join4 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 640 256 = 1083937850890288161346844265472 :=
  phaseBlock_append receipt_1_16_2383_1_part5 receipt_1_16_2383_1_part6 rfl rfl rfl
private theorem receipt_1_16_2383_1_join5 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 1024 256 = 828188029664165680393576614912 :=
  phaseBlock_append receipt_1_16_2383_1_part8 receipt_1_16_2383_1_part9 rfl rfl rfl
private theorem receipt_1_16_2383_1_join6 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 896 384 = 1304915717604116341987313816064 :=
  phaseBlock_append receipt_1_16_2383_1_part7 receipt_1_16_2383_1_join5 rfl rfl rfl
private theorem receipt_1_16_2383_1_join7 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 640 640 = 2388853568494404503334158081536 :=
  phaseBlock_append receipt_1_16_2383_1_join4 receipt_1_16_2383_1_join6 rfl rfl rfl
private theorem receipt_1_16_2383_1_join8 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 0 1280 = 5910065861170255121960467151872 :=
  phaseBlock_append receipt_1_16_2383_1_join3 receipt_1_16_2383_1_join7 rfl rfl rfl
private theorem receipt_1_16_2383_1_join9 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 1280 256 = 667964748323804866241294994432 :=
  phaseBlock_append receipt_1_16_2383_1_part10 receipt_1_16_2383_1_part11 rfl rfl rfl
private theorem receipt_1_16_2383_1_join10 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 1664 256 = 442519916135134611673294472167 :=
  phaseBlock_append receipt_1_16_2383_1_part13 receipt_1_16_2383_1_part14 rfl rfl rfl
private theorem receipt_1_16_2383_1_join11 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 1536 384 = 718919300065487617252078979559 :=
  phaseBlock_append receipt_1_16_2383_1_part12 receipt_1_16_2383_1_join10 rfl rfl rfl
private theorem receipt_1_16_2383_1_join12 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 1280 640 = 1386884048389292483493373973991 :=
  phaseBlock_append receipt_1_16_2383_1_join9 receipt_1_16_2383_1_join11 rfl rfl rfl
private theorem receipt_1_16_2383_1_join13 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 2048 256 = 234317937099712628463723523115 :=
  phaseBlock_append receipt_1_16_2383_1_part16 receipt_1_16_2383_1_part17 rfl rfl rfl
private theorem receipt_1_16_2383_1_join14 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 1920 384 = 402354324163190972528020094705 :=
  phaseBlock_append receipt_1_16_2383_1_part15 receipt_1_16_2383_1_join13 rfl rfl rfl
private theorem receipt_1_16_2383_1_join15 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 2432 218 = 44010884123346023491639088988 :=
  phaseBlock_append receipt_1_16_2383_1_part19 receipt_1_16_2383_1_part20 rfl rfl rfl
private theorem receipt_1_16_2383_1_join16 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 2304 346 = 112130456605505897133306869956 :=
  phaseBlock_append receipt_1_16_2383_1_part18 receipt_1_16_2383_1_join15 rfl rfl rfl
private theorem receipt_1_16_2383_1_join17 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 1920 730 = 514484780768696869661326964661 :=
  phaseBlock_append receipt_1_16_2383_1_join14 receipt_1_16_2383_1_join16 rfl rfl rfl
private theorem receipt_1_16_2383_1_join18 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 1280 1370 = 1901368829157989353154700938652 :=
  phaseBlock_append receipt_1_16_2383_1_join12 receipt_1_16_2383_1_join17 rfl rfl rfl
private theorem receipt_1_16_2383_1_join19 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2383 103 1 0 2 1) 0 2650 = 7811434690328244475115168090524 :=
  phaseBlock_append receipt_1_16_2383_1_join8 receipt_1_16_2383_1_join18 rfl rfl rfl

private theorem receipt_1_16_2383_1 : fastPhase (bank 1 16).shape 179808 2383 103 1 0 2 1 = 7811434690328244475115168090524 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_1_16_2383_1_join19

private theorem receipt_1_16_2384_0_part0 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 0 128 = 801762467817204459534457911264 := by decide +kernel
private theorem receipt_1_16_2384_0_part1 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 128 128 = 752074501139956494430358931424 := by decide +kernel
private theorem receipt_1_16_2384_0_part2 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 256 128 = 703509444542520744487060494304 := by decide +kernel
private theorem receipt_1_16_2384_0_part3 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 384 128 = 656053925714297474361014921184 := by decide +kernel
private theorem receipt_1_16_2384_0_part4 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 512 128 = 609694603809224394023785297888 := by decide +kernel
private theorem receipt_1_16_2384_0_part5 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 640 128 = 564418169420621767858995480544 := by decide +kernel
private theorem receipt_1_16_2384_0_part6 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 768 128 = 520211344556037523759280101344 := by decide +kernel
private theorem receipt_1_16_2384_0_part7 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 896 128 = 477060882612092362223234574304 := by decide +kernel
private theorem receipt_1_16_2384_0_part8 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 1024 128 = 434953568349324865452365101024 := by decide +kernel
private theorem receipt_1_16_2384_0_part9 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 1152 128 = 393876217867036606448038676448 := by decide +kernel
private theorem receipt_1_16_2384_0_part10 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 1280 128 = 353815678578137258108433094624 := by decide +kernel
private theorem receipt_1_16_2384_0_part11 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 1408 128 = 314758829183989702325486954464 := by decide +kernel
private theorem receipt_1_16_2384_0_part12 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 1536 128 = 276692579649255139081849665504 := by decide +kernel
private theorem receipt_1_16_2384_0_part13 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 1664 128 = 239603871176738195547831453664 := by decide +kernel
private theorem receipt_1_16_2384_0_part14 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 1792 128 = 203479691640392517629740862599 := by decide +kernel
private theorem receipt_1_16_2384_0_part15 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 1920 128 = 168307084793958528082030248305 := by decide +kernel
private theorem receipt_1_16_2384_0_part16 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 2048 128 = 134073058775664982306171324868 := by decide +kernel
private theorem receipt_1_16_2384_0_part17 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 2176 128 = 100764638230831367003337655522 := by decide +kernel
private theorem receipt_1_16_2384_0_part18 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 2304 128 = 68368879071390244911180063607 := by decide +kernel
private theorem receipt_1_16_2384_0_part19 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 2432 128 = 36872868390058735344571970889 := by decide +kernel
private theorem receipt_1_16_2384_0_part20 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 2560 90 = 7546827628217203210798255554 := by decide +kernel
private theorem receipt_1_16_2384_0_join0 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 0 256 = 1553836968957160953964816842688 :=
  phaseBlock_append receipt_1_16_2384_0_part0 receipt_1_16_2384_0_part1 rfl rfl rfl
private theorem receipt_1_16_2384_0_join1 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 384 256 = 1265748529523521868384800219072 :=
  phaseBlock_append receipt_1_16_2384_0_part3 receipt_1_16_2384_0_part4 rfl rfl rfl
private theorem receipt_1_16_2384_0_join2 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 256 384 = 1969257974066042612871860713376 :=
  phaseBlock_append receipt_1_16_2384_0_part2 receipt_1_16_2384_0_join1 rfl rfl rfl
private theorem receipt_1_16_2384_0_join3 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 0 640 = 3523094943023203566836677556064 :=
  phaseBlock_append receipt_1_16_2384_0_join0 receipt_1_16_2384_0_join2 rfl rfl rfl
private theorem receipt_1_16_2384_0_join4 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 640 256 = 1084629513976659291618275581888 :=
  phaseBlock_append receipt_1_16_2384_0_part5 receipt_1_16_2384_0_part6 rfl rfl rfl
private theorem receipt_1_16_2384_0_join5 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 1024 256 = 828829786216361471900403777472 :=
  phaseBlock_append receipt_1_16_2384_0_part8 receipt_1_16_2384_0_part9 rfl rfl rfl
private theorem receipt_1_16_2384_0_join6 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 896 384 = 1305890668828453834123638351776 :=
  phaseBlock_append receipt_1_16_2384_0_part7 receipt_1_16_2384_0_join5 rfl rfl rfl
private theorem receipt_1_16_2384_0_join7 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 640 640 = 2390520182805113125741913933664 :=
  phaseBlock_append receipt_1_16_2384_0_join4 receipt_1_16_2384_0_join6 rfl rfl rfl
private theorem receipt_1_16_2384_0_join8 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 0 1280 = 5913615125828316692578591489728 :=
  phaseBlock_append receipt_1_16_2384_0_join3 receipt_1_16_2384_0_join7 rfl rfl rfl
private theorem receipt_1_16_2384_0_join9 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 1280 256 = 668574507762126960433920049088 :=
  phaseBlock_append receipt_1_16_2384_0_part10 receipt_1_16_2384_0_part11 rfl rfl rfl
private theorem receipt_1_16_2384_0_join10 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 1664 256 = 443083562817130713177572316263 :=
  phaseBlock_append receipt_1_16_2384_0_part13 receipt_1_16_2384_0_part14 rfl rfl rfl
private theorem receipt_1_16_2384_0_join11 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 1536 384 = 719776142466385852259421981767 :=
  phaseBlock_append receipt_1_16_2384_0_part12 receipt_1_16_2384_0_join10 rfl rfl rfl
private theorem receipt_1_16_2384_0_join12 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 1280 640 = 1388350650228512812693342030855 :=
  phaseBlock_append receipt_1_16_2384_0_join9 receipt_1_16_2384_0_join11 rfl rfl rfl
private theorem receipt_1_16_2384_0_join13 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 2048 256 = 234837697006496349309508980390 :=
  phaseBlock_append receipt_1_16_2384_0_part16 receipt_1_16_2384_0_part17 rfl rfl rfl
private theorem receipt_1_16_2384_0_join14 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 1920 384 = 403144781800454877391539228695 :=
  phaseBlock_append receipt_1_16_2384_0_part15 receipt_1_16_2384_0_join13 rfl rfl rfl
private theorem receipt_1_16_2384_0_join15 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 2432 218 = 44419696018275938555370226443 :=
  phaseBlock_append receipt_1_16_2384_0_part19 receipt_1_16_2384_0_part20 rfl rfl rfl
private theorem receipt_1_16_2384_0_join16 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 2304 346 = 112788575089666183466550290050 :=
  phaseBlock_append receipt_1_16_2384_0_part18 receipt_1_16_2384_0_join15 rfl rfl rfl
private theorem receipt_1_16_2384_0_join17 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 1920 730 = 515933356890121060858089518745 :=
  phaseBlock_append receipt_1_16_2384_0_join14 receipt_1_16_2384_0_join16 rfl rfl rfl
private theorem receipt_1_16_2384_0_join18 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 1280 1370 = 1904284007118633873551431549600 :=
  phaseBlock_append receipt_1_16_2384_0_join12 receipt_1_16_2384_0_join17 rfl rfl rfl
private theorem receipt_1_16_2384_0_join19 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 0) 0 2650 = 7817899132946950566130023039328 :=
  phaseBlock_append receipt_1_16_2384_0_join8 receipt_1_16_2384_0_join18 rfl rfl rfl

private theorem receipt_1_16_2384_0 : fastPhase (bank 1 16).shape 179808 2384 103 1 0 2 0 = 7817899132946950566130023039328 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_1_16_2384_0_join19

private theorem receipt_1_16_2384_1_part0 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 0 128 = 801375091359570342124477117152 := by decide +kernel
private theorem receipt_1_16_2384_1_part1 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 128 128 = 751695660634778502892070716128 := by decide +kernel
private theorem receipt_1_16_2384_1_part2 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 256 128 = 703139038703499976749021139680 := by decide +kernel
private theorem receipt_1_16_2384_1_part3 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 384 128 = 655691853494985715073540612832 := by decide +kernel
private theorem receipt_1_16_2384_1_part4 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 512 128 = 609340764402831523827352974048 := by decide +kernel
private theorem receipt_1_16_2384_1_part5 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 640 128 = 564072462259823172652643680992 := by decide +kernel
private theorem receipt_1_16_2384_1_part6 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 768 128 = 519873669312781503969009816288 := by decide +kernel
private theorem receipt_1_16_2384_1_part7 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 896 128 = 476731139197407542070410093280 := by decide +kernel
private theorem receipt_1_16_2384_1_part8 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 1024 128 = 434631656913127602222114861792 := by decide +kernel
private theorem receipt_1_16_2384_1_part9 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 1152 128 = 393562038797938399757656113888 := by decide +kernel
private theorem receipt_1_16_2384_1_part10 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 1280 128 = 353509132503252159175777489632 := by decide +kernel
private theorem receipt_1_16_2384_1_part11 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 1408 128 = 314459816968741723237384282848 := by decide +kernel
private theorem receipt_1_16_2384_1_part12 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 1536 128 = 276401002397185662062493446880 := by decide +kernel
private theorem receipt_1_16_2384_1_part13 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 1664 128 = 239319630229313382227183600352 := by decide +kernel
private theorem receipt_1_16_2384_1_part14 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 1792 128 = 203202688556449232708738808260 := by decide +kernel
private theorem receipt_1_16_2384_1_part15 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 1920 128 = 168037221297942284911951695529 := by decide +kernel
private theorem receipt_1_16_2384_1_part16 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 2048 128 = 133810236814363144489974204163 := by decide +kernel
private theorem receipt_1_16_2384_1_part17 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 2176 128 = 100508759988662774478900218951 := by decide +kernel
private theorem receipt_1_16_2384_1_part18 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 2304 128 = 68119846970142829202538359760 := by decide +kernel
private theorem receipt_1_16_2384_1_part19 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 2432 128 = 36630585088701389524655719250 := by decide +kernel
private theorem receipt_1_16_2384_1_part20 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 2560 90 = 7380460661433327844408079565 := by decide +kernel
private theorem receipt_1_16_2384_1_join0 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 0 256 = 1553070751994348845016547833280 :=
  phaseBlock_append receipt_1_16_2384_1_part0 receipt_1_16_2384_1_part1 rfl rfl rfl
private theorem receipt_1_16_2384_1_join1 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 384 256 = 1265032617897817238900893586880 :=
  phaseBlock_append receipt_1_16_2384_1_part3 receipt_1_16_2384_1_part4 rfl rfl rfl
private theorem receipt_1_16_2384_1_join2 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 256 384 = 1968171656601317215649914726560 :=
  phaseBlock_append receipt_1_16_2384_1_part2 receipt_1_16_2384_1_join1 rfl rfl rfl
private theorem receipt_1_16_2384_1_join3 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 0 640 = 3521242408595666060666462559840 :=
  phaseBlock_append receipt_1_16_2384_1_join0 receipt_1_16_2384_1_join2 rfl rfl rfl
private theorem receipt_1_16_2384_1_join4 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 640 256 = 1083946131572604676621653497280 :=
  phaseBlock_append receipt_1_16_2384_1_part5 receipt_1_16_2384_1_part6 rfl rfl rfl
private theorem receipt_1_16_2384_1_join5 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 1024 256 = 828193695711066001979770975680 :=
  phaseBlock_append receipt_1_16_2384_1_part8 receipt_1_16_2384_1_part9 rfl rfl rfl
private theorem receipt_1_16_2384_1_join6 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 896 384 = 1304924834908473544050181068960 :=
  phaseBlock_append receipt_1_16_2384_1_part7 receipt_1_16_2384_1_join5 rfl rfl rfl
private theorem receipt_1_16_2384_1_join7 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 640 640 = 2388870966481078220671834566240 :=
  phaseBlock_append receipt_1_16_2384_1_join4 receipt_1_16_2384_1_join6 rfl rfl rfl
private theorem receipt_1_16_2384_1_join8 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 0 1280 = 5910113375076744281338297126080 :=
  phaseBlock_append receipt_1_16_2384_1_join3 receipt_1_16_2384_1_join7 rfl rfl rfl
private theorem receipt_1_16_2384_1_join9 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 1280 256 = 667968949471993882413161772480 :=
  phaseBlock_append receipt_1_16_2384_1_part10 receipt_1_16_2384_1_part11 rfl rfl rfl
private theorem receipt_1_16_2384_1_join10 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 1664 256 = 442522318785762614935922408612 :=
  phaseBlock_append receipt_1_16_2384_1_part13 receipt_1_16_2384_1_part14 rfl rfl rfl
private theorem receipt_1_16_2384_1_join11 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 1536 384 = 718923321182948276998415855492 :=
  phaseBlock_append receipt_1_16_2384_1_part12 receipt_1_16_2384_1_join10 rfl rfl rfl
private theorem receipt_1_16_2384_1_join12 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 1280 640 = 1386892270654942159411577627972 :=
  phaseBlock_append receipt_1_16_2384_1_join9 receipt_1_16_2384_1_join11 rfl rfl rfl
private theorem receipt_1_16_2384_1_join13 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 2048 256 = 234318996803025918968874423114 :=
  phaseBlock_append receipt_1_16_2384_1_part16 receipt_1_16_2384_1_part17 rfl rfl rfl
private theorem receipt_1_16_2384_1_join14 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 1920 384 = 402356218100968203880826118643 :=
  phaseBlock_append receipt_1_16_2384_1_part15 receipt_1_16_2384_1_join13 rfl rfl rfl
private theorem receipt_1_16_2384_1_join15 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 2432 218 = 44011045750134717369063798815 :=
  phaseBlock_append receipt_1_16_2384_1_part19 receipt_1_16_2384_1_part20 rfl rfl rfl
private theorem receipt_1_16_2384_1_join16 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 2304 346 = 112130892720277546571602158575 :=
  phaseBlock_append receipt_1_16_2384_1_part18 receipt_1_16_2384_1_join15 rfl rfl rfl
private theorem receipt_1_16_2384_1_join17 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 1920 730 = 514487110821245750452428277218 :=
  phaseBlock_append receipt_1_16_2384_1_join14 receipt_1_16_2384_1_join16 rfl rfl rfl
private theorem receipt_1_16_2384_1_join18 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 1280 1370 = 1901379381476187909864005905190 :=
  phaseBlock_append receipt_1_16_2384_1_join12 receipt_1_16_2384_1_join17 rfl rfl rfl
private theorem receipt_1_16_2384_1_join19 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2384 103 1 0 2 1) 0 2650 = 7811492756552932191202303031270 :=
  phaseBlock_append receipt_1_16_2384_1_join8 receipt_1_16_2384_1_join18 rfl rfl rfl

private theorem receipt_1_16_2384_1 : fastPhase (bank 1 16).shape 179808 2384 103 1 0 2 1 = 7811492756552932191202303031270 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_1_16_2384_1_join19

theorem receipt_1_16 : Checked (bank 1 16) 103 0 2 := by
  refine checked_from_values (bank 1 16) 103 0 2
    (P3_7_1.checked (bank 1 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_12604_2649)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_16_2383_0 receipt_1_16_2383_1 receipt_1_16_2384_0 receipt_1_16_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_16_2383_0_part0 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 0 128 = 430417876841405635119702595584 := by decide +kernel
private theorem receipt_2_16_2383_0_part1 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 128 128 = 402723812948796787609616553984 := by decide +kernel
private theorem receipt_2_16_2383_0_part2 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 256 128 = 375764843997837185296131774464 := by decide +kernel
private theorem receipt_2_16_2383_0_part3 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 384 128 = 349529164023988835505755265024 := by decide +kernel
private theorem receipt_2_16_2383_0_part4 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 512 128 = 324005061172359857604295579648 := by decide +kernel
private theorem receipt_2_16_2383_0_part5 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 640 128 = 299180917389567844648452593664 := by decide +kernel
private theorem receipt_2_16_2383_0_part6 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 768 128 = 275045208115603225037407279104 := by decide +kernel
private theorem receipt_2_16_2383_0_part7 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 896 128 = 251586501975692624164411480064 := by decide +kernel
private theorem receipt_2_16_2383_0_part8 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 1024 128 = 228793460472162226068377688064 := by decide +kernel
private theorem receipt_2_16_2383_0_part9 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 1152 128 = 206654837676301135085468817408 := by decide +kernel
private theorem receipt_2_16_2383_0_part10 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 1280 128 = 185159479920224737500687980544 := by decide +kernel
private theorem receipt_2_16_2383_0_part11 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 1408 128 = 164296325488738063199468263424 := by decide +kernel
private theorem receipt_2_16_2383_0_part12 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 1536 128 = 144054404311199147319262500864 := by decide +kernel
private theorem receipt_2_16_2383_0_part13 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 1664 128 = 124422837653382391901133051904 := by decide +kernel
private theorem receipt_2_16_2383_0_part14 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 1792 128 = 105390846149157572726586734743 := by decide +kernel
private theorem receipt_2_16_2383_0_part15 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 1920 128 = 86947753262394937135606969384 := by decide +kernel
private theorem receipt_2_16_2383_0_part16 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 2048 128 = 69082938156290832699383346714 := by decide +kernel
private theorem receipt_2_16_2383_0_part17 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 2176 128 = 51785863063189918144567448495 := by decide +kernel
private theorem receipt_2_16_2383_0_part18 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 2304 128 = 35046080303840297154784671212 := by decide +kernel
private theorem receipt_2_16_2383_0_part19 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 2432 128 = 18853231965662976618255102373 := by decide +kernel
private theorem receipt_2_16_2383_0_part20 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 2560 90 = 3850573177285835947179412857 := by decide +kernel
private theorem receipt_2_16_2383_0_join0 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 0 256 = 833141689790202422729319149568 :=
  phaseBlock_append receipt_2_16_2383_0_part0 receipt_2_16_2383_0_part1 rfl rfl rfl
private theorem receipt_2_16_2383_0_join1 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 384 256 = 673534225196348693110050844672 :=
  phaseBlock_append receipt_2_16_2383_0_part3 receipt_2_16_2383_0_part4 rfl rfl rfl
private theorem receipt_2_16_2383_0_join2 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 256 384 = 1049299069194185878406182619136 :=
  phaseBlock_append receipt_2_16_2383_0_part2 receipt_2_16_2383_0_join1 rfl rfl rfl
private theorem receipt_2_16_2383_0_join3 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 0 640 = 1882440758984388301135501768704 :=
  phaseBlock_append receipt_2_16_2383_0_join0 receipt_2_16_2383_0_join2 rfl rfl rfl
private theorem receipt_2_16_2383_0_join4 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 640 256 = 574226125505171069685859872768 :=
  phaseBlock_append receipt_2_16_2383_0_part5 receipt_2_16_2383_0_part6 rfl rfl rfl
private theorem receipt_2_16_2383_0_join5 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 1024 256 = 435448298148463361153846505472 :=
  phaseBlock_append receipt_2_16_2383_0_part8 receipt_2_16_2383_0_part9 rfl rfl rfl
private theorem receipt_2_16_2383_0_join6 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 896 384 = 687034800124155985318257985536 :=
  phaseBlock_append receipt_2_16_2383_0_part7 receipt_2_16_2383_0_join5 rfl rfl rfl
private theorem receipt_2_16_2383_0_join7 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 640 640 = 1261260925629327055004117858304 :=
  phaseBlock_append receipt_2_16_2383_0_join4 receipt_2_16_2383_0_join6 rfl rfl rfl
private theorem receipt_2_16_2383_0_join8 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 0 1280 = 3143701684613715356139619627008 :=
  phaseBlock_append receipt_2_16_2383_0_join3 receipt_2_16_2383_0_join7 rfl rfl rfl
private theorem receipt_2_16_2383_0_join9 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 1280 256 = 349455805408962800700156243968 :=
  phaseBlock_append receipt_2_16_2383_0_part10 receipt_2_16_2383_0_part11 rfl rfl rfl
private theorem receipt_2_16_2383_0_join10 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 1664 256 = 229813683802539964627719786647 :=
  phaseBlock_append receipt_2_16_2383_0_part13 receipt_2_16_2383_0_part14 rfl rfl rfl
private theorem receipt_2_16_2383_0_join11 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 1536 384 = 373868088113739111946982287511 :=
  phaseBlock_append receipt_2_16_2383_0_part12 receipt_2_16_2383_0_join10 rfl rfl rfl
private theorem receipt_2_16_2383_0_join12 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 1280 640 = 723323893522701912647138531479 :=
  phaseBlock_append receipt_2_16_2383_0_join9 receipt_2_16_2383_0_join11 rfl rfl rfl
private theorem receipt_2_16_2383_0_join13 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 2048 256 = 120868801219480750843950795209 :=
  phaseBlock_append receipt_2_16_2383_0_part16 receipt_2_16_2383_0_part17 rfl rfl rfl
private theorem receipt_2_16_2383_0_join14 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 1920 384 = 207816554481875687979557764593 :=
  phaseBlock_append receipt_2_16_2383_0_part15 receipt_2_16_2383_0_join13 rfl rfl rfl
private theorem receipt_2_16_2383_0_join15 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 2432 218 = 22703805142948812565434515230 :=
  phaseBlock_append receipt_2_16_2383_0_part19 receipt_2_16_2383_0_part20 rfl rfl rfl
private theorem receipt_2_16_2383_0_join16 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 2304 346 = 57749885446789109720219186442 :=
  phaseBlock_append receipt_2_16_2383_0_part18 receipt_2_16_2383_0_join15 rfl rfl rfl
private theorem receipt_2_16_2383_0_join17 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 1920 730 = 265566439928664797699776951035 :=
  phaseBlock_append receipt_2_16_2383_0_join14 receipt_2_16_2383_0_join16 rfl rfl rfl
private theorem receipt_2_16_2383_0_join18 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 1280 1370 = 988890333451366710346915482514 :=
  phaseBlock_append receipt_2_16_2383_0_join12 receipt_2_16_2383_0_join17 rfl rfl rfl
private theorem receipt_2_16_2383_0_join19 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 0) 0 2650 = 4132592018065082066486535109522 :=
  phaseBlock_append receipt_2_16_2383_0_join8 receipt_2_16_2383_0_join18 rfl rfl rfl

private theorem receipt_2_16_2383_0 : fastPhase (bank 2 16).shape 179808 2383 103 1 0 7 0 = 4132592018065082066486535109522 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_2_16_2383_0_join19

private theorem receipt_2_16_2383_1_part0 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 0 128 = 430201426312638685776118936960 := by decide +kernel
private theorem receipt_2_16_2383_1_part1 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 128 128 = 402512989782303292542115919232 := by decide +kernel
private theorem receipt_2_16_2383_1_part2 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 256 128 = 375559558145920128276518827392 := by decide +kernel
private theorem receipt_2_16_2383_1_part3 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 384 128 = 349329326158026649117434623360 := by decide +kernel
private theorem receipt_2_16_2383_1_part4 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 512 128 = 323810582680447250758015055232 := by decide +kernel
private theorem receipt_2_16_2383_1_part5 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 640 128 = 298991710374156630098046432640 := by decide +kernel
private theorem receipt_2_16_2383_1_part6 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 768 128 = 274861185391143146895539402112 := by decide +kernel
private theorem receipt_2_16_2383_1_part7 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 896 128 = 251407577066272185418318722432 := by decide +kernel
private theorem receipt_2_16_2383_1_part8 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 1024 128 = 228619547609149516095613040000 := by decide +kernel
private theorem receipt_2_16_2383_1_part9 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 1152 128 = 206485851795984657169644664192 := by decide +kernel
private theorem receipt_2_16_2383_1_part10 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 1280 128 = 184995336661454236347219342720 := by decide +kernel
private theorem receipt_2_16_2383_1_part11 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 1408 128 = 164136941190565352451316036992 := by decide +kernel
private theorem receipt_2_16_2383_1_part12 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 1536 128 = 143899696010518937072676697472 := by decide +kernel
private theorem receipt_2_16_2383_1_part13 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 1664 128 = 124272723082573116221396039040 := by decide +kernel
private theorem receipt_2_16_2383_1_part14 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 1792 128 = 105245243722574986641866568787 := by decide +kernel
private theorem receipt_2_16_2383_1_part15 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 1920 128 = 86806582047793659473492664150 := by decide +kernel
private theorem receipt_2_16_2383_1_part16 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 2048 128 = 68946117903118571672875036557 := by decide +kernel
private theorem receipt_2_16_2383_1_part17 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 2176 128 = 51653314208045100699137512328 := by decide +kernel
private theorem receipt_2_16_2383_1_part18 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 2304 128 = 34917723968091642883251888688 := by decide +kernel
private theorem receipt_2_16_2383_1_part19 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 2432 128 = 18728989953065313293300042037 := by decide +kernel
private theorem receipt_2_16_2383_1_part20 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 2560 90 = 3765637135859292935252802861 := by decide +kernel
private theorem receipt_2_16_2383_1_join0 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 0 256 = 832714416094941978318234856192 :=
  phaseBlock_append receipt_2_16_2383_1_part0 receipt_2_16_2383_1_part1 rfl rfl rfl
private theorem receipt_2_16_2383_1_join1 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 384 256 = 673139908838473899875449678592 :=
  phaseBlock_append receipt_2_16_2383_1_part3 receipt_2_16_2383_1_part4 rfl rfl rfl
private theorem receipt_2_16_2383_1_join2 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 256 384 = 1048699466984394028151968505984 :=
  phaseBlock_append receipt_2_16_2383_1_part2 receipt_2_16_2383_1_join1 rfl rfl rfl
private theorem receipt_2_16_2383_1_join3 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 0 640 = 1881413883079336006470203362176 :=
  phaseBlock_append receipt_2_16_2383_1_join0 receipt_2_16_2383_1_join2 rfl rfl rfl
private theorem receipt_2_16_2383_1_join4 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 640 256 = 573852895765299776993585834752 :=
  phaseBlock_append receipt_2_16_2383_1_part5 receipt_2_16_2383_1_part6 rfl rfl rfl
private theorem receipt_2_16_2383_1_join5 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 1024 256 = 435105399405134173265257704192 :=
  phaseBlock_append receipt_2_16_2383_1_part8 receipt_2_16_2383_1_part9 rfl rfl rfl
private theorem receipt_2_16_2383_1_join6 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 896 384 = 686512976471406358683576426624 :=
  phaseBlock_append receipt_2_16_2383_1_part7 receipt_2_16_2383_1_join5 rfl rfl rfl
private theorem receipt_2_16_2383_1_join7 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 640 640 = 1260365872236706135677162261376 :=
  phaseBlock_append receipt_2_16_2383_1_join4 receipt_2_16_2383_1_join6 rfl rfl rfl
private theorem receipt_2_16_2383_1_join8 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 0 1280 = 3141779755316042142147365623552 :=
  phaseBlock_append receipt_2_16_2383_1_join3 receipt_2_16_2383_1_join7 rfl rfl rfl
private theorem receipt_2_16_2383_1_join9 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 1280 256 = 349132277852019588798535379712 :=
  phaseBlock_append receipt_2_16_2383_1_part10 receipt_2_16_2383_1_part11 rfl rfl rfl
private theorem receipt_2_16_2383_1_join10 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 1664 256 = 229517966805148102863262607827 :=
  phaseBlock_append receipt_2_16_2383_1_part13 receipt_2_16_2383_1_part14 rfl rfl rfl
private theorem receipt_2_16_2383_1_join11 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 1536 384 = 373417662815667039935939305299 :=
  phaseBlock_append receipt_2_16_2383_1_part12 receipt_2_16_2383_1_join10 rfl rfl rfl
private theorem receipt_2_16_2383_1_join12 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 1280 640 = 722549940667686628734474685011 :=
  phaseBlock_append receipt_2_16_2383_1_join9 receipt_2_16_2383_1_join11 rfl rfl rfl
private theorem receipt_2_16_2383_1_join13 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 2048 256 = 120599432111163672372012548885 :=
  phaseBlock_append receipt_2_16_2383_1_part16 receipt_2_16_2383_1_part17 rfl rfl rfl
private theorem receipt_2_16_2383_1_join14 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 1920 384 = 207406014158957331845505213035 :=
  phaseBlock_append receipt_2_16_2383_1_part15 receipt_2_16_2383_1_join13 rfl rfl rfl
private theorem receipt_2_16_2383_1_join15 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 2432 218 = 22494627088924606228552844898 :=
  phaseBlock_append receipt_2_16_2383_1_part19 receipt_2_16_2383_1_part20 rfl rfl rfl
private theorem receipt_2_16_2383_1_join16 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 2304 346 = 57412351057016249111804733586 :=
  phaseBlock_append receipt_2_16_2383_1_part18 receipt_2_16_2383_1_join15 rfl rfl rfl
private theorem receipt_2_16_2383_1_join17 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 1920 730 = 264818365215973580957309946621 :=
  phaseBlock_append receipt_2_16_2383_1_join14 receipt_2_16_2383_1_join16 rfl rfl rfl
private theorem receipt_2_16_2383_1_join18 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 1280 1370 = 987368305883660209691784631632 :=
  phaseBlock_append receipt_2_16_2383_1_join12 receipt_2_16_2383_1_join17 rfl rfl rfl
private theorem receipt_2_16_2383_1_join19 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2383 103 1 0 7 1) 0 2650 = 4129148061199702351839150255184 :=
  phaseBlock_append receipt_2_16_2383_1_join8 receipt_2_16_2383_1_join18 rfl rfl rfl

private theorem receipt_2_16_2383_1 : fastPhase (bank 2 16).shape 179808 2383 103 1 0 7 1 = 4129148061199702351839150255184 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_2_16_2383_1_join19

private theorem receipt_2_16_2384_0_part0 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 0 128 = 430421754468239469178164396384 := by decide +kernel
private theorem receipt_2_16_2384_0_part1 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 128 128 = 402727343746132270922758336864 := by decide +kernel
private theorem receipt_2_16_2384_0_part2 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 256 128 = 375768046259745261028513063264 := by decide +kernel
private theorem receipt_2_16_2384_0_part3 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 384 128 = 349532055675363110999858450784 := by decide +kernel
private theorem receipt_2_16_2384_0_part4 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 512 128 = 324007659772096306280506884448 := by decide +kernel
private theorem receipt_2_16_2384_0_part5 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 640 128 = 299183240133733732691090829664 := by decide +kernel
private theorem receipt_2_16_2384_0_part6 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 768 128 = 275047271840595262866800402784 := by decide +kernel
private theorem receipt_2_16_2384_0_part7 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 896 128 = 251588323161384342695020941664 := by decide +kernel
private theorem receipt_2_16_2384_0_part8 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 1024 128 = 228795055245040577752970576224 := by decide +kernel
private theorem receipt_2_16_2384_0_part9 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 1152 128 = 206656221812592319745337799008 := by decide +kernel
private theorem receipt_2_16_2384_0_part10 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 1280 128 = 185160668849009252941919035744 := by decide +kernel
private theorem receipt_2_16_2384_0_part11 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 1408 128 = 164297334295054980615256215904 := by decide +kernel
private theorem receipt_2_16_2384_0_part12 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 1536 128 = 144055247739139611478274343264 := by decide +kernel
private theorem receipt_2_16_2384_0_part13 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 1664 128 = 124423530109172346121919066464 := by decide +kernel
private theorem receipt_2_16_2384_0_part14 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 1792 128 = 105391401365718085251938663449 := by decide +kernel
private theorem receipt_2_16_2384_0_part15 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 1920 128 = 86948184873895020091777504790 := by decide +kernel
private theorem receipt_2_16_2384_0_part16 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 2048 128 = 69083259792596881636285165733 := by decide +kernel
private theorem receipt_2_16_2384_0_part17 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 2176 128 = 51786088007140963006590473047 := by decide +kernel
private theorem receipt_2_16_2384_0_part18 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 2304 128 = 35046221502298422227942950417 := by decide +kernel
private theorem receipt_2_16_2384_0_part19 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 2432 128 = 18853302021725216958487674444 := by decide +kernel
private theorem receipt_2_16_2384_0_part20 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 2560 90 = 3850586470186060100111431584 := by decide +kernel
private theorem receipt_2_16_2384_0_join0 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 0 256 = 833149098214371740100922733248 :=
  phaseBlock_append receipt_2_16_2384_0_part0 receipt_2_16_2384_0_part1 rfl rfl rfl
private theorem receipt_2_16_2384_0_join1 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 384 256 = 673539715447459417280365335232 :=
  phaseBlock_append receipt_2_16_2384_0_part3 receipt_2_16_2384_0_part4 rfl rfl rfl
private theorem receipt_2_16_2384_0_join2 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 256 384 = 1049307761707204678308878398496 :=
  phaseBlock_append receipt_2_16_2384_0_part2 receipt_2_16_2384_0_join1 rfl rfl rfl
private theorem receipt_2_16_2384_0_join3 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 0 640 = 1882456859921576418409801131744 :=
  phaseBlock_append receipt_2_16_2384_0_join0 receipt_2_16_2384_0_join2 rfl rfl rfl
private theorem receipt_2_16_2384_0_join4 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 640 256 = 574230511974328995557891232448 :=
  phaseBlock_append receipt_2_16_2384_0_part5 receipt_2_16_2384_0_part6 rfl rfl rfl
private theorem receipt_2_16_2384_0_join5 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 1024 256 = 435451277057632897498308375232 :=
  phaseBlock_append receipt_2_16_2384_0_part8 receipt_2_16_2384_0_part9 rfl rfl rfl
private theorem receipt_2_16_2384_0_join6 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 896 384 = 687039600219017240193329316896 :=
  phaseBlock_append receipt_2_16_2384_0_part7 receipt_2_16_2384_0_join5 rfl rfl rfl
private theorem receipt_2_16_2384_0_join7 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 640 640 = 1261270112193346235751220549344 :=
  phaseBlock_append receipt_2_16_2384_0_join4 receipt_2_16_2384_0_join6 rfl rfl rfl
private theorem receipt_2_16_2384_0_join8 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 0 1280 = 3143726972114922654161021681088 :=
  phaseBlock_append receipt_2_16_2384_0_join3 receipt_2_16_2384_0_join7 rfl rfl rfl
private theorem receipt_2_16_2384_0_join9 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 1280 256 = 349458003144064233557175251648 :=
  phaseBlock_append receipt_2_16_2384_0_part10 receipt_2_16_2384_0_part11 rfl rfl rfl
private theorem receipt_2_16_2384_0_join10 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 1664 256 = 229814931474890431373857729913 :=
  phaseBlock_append receipt_2_16_2384_0_part13 receipt_2_16_2384_0_part14 rfl rfl rfl
private theorem receipt_2_16_2384_0_join11 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 1536 384 = 373870179214030042852132073177 :=
  phaseBlock_append receipt_2_16_2384_0_part12 receipt_2_16_2384_0_join10 rfl rfl rfl
private theorem receipt_2_16_2384_0_join12 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 1280 640 = 723328182358094276409307324825 :=
  phaseBlock_append receipt_2_16_2384_0_join9 receipt_2_16_2384_0_join11 rfl rfl rfl
private theorem receipt_2_16_2384_0_join13 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 2048 256 = 120869347799737844642875638780 :=
  phaseBlock_append receipt_2_16_2384_0_part16 receipt_2_16_2384_0_part17 rfl rfl rfl
private theorem receipt_2_16_2384_0_join14 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 1920 384 = 207817532673632864734653143570 :=
  phaseBlock_append receipt_2_16_2384_0_part15 receipt_2_16_2384_0_join13 rfl rfl rfl
private theorem receipt_2_16_2384_0_join15 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 2432 218 = 22703888491911277058599106028 :=
  phaseBlock_append receipt_2_16_2384_0_part19 receipt_2_16_2384_0_part20 rfl rfl rfl
private theorem receipt_2_16_2384_0_join16 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 2304 346 = 57750109994209699286542056445 :=
  phaseBlock_append receipt_2_16_2384_0_part18 receipt_2_16_2384_0_join15 rfl rfl rfl
private theorem receipt_2_16_2384_0_join17 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 1920 730 = 265567642667842564021195200015 :=
  phaseBlock_append receipt_2_16_2384_0_join14 receipt_2_16_2384_0_join16 rfl rfl rfl
private theorem receipt_2_16_2384_0_join18 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 1280 1370 = 988895825025936840430502524840 :=
  phaseBlock_append receipt_2_16_2384_0_join12 receipt_2_16_2384_0_join17 rfl rfl rfl
private theorem receipt_2_16_2384_0_join19 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 0) 0 2650 = 4132622797140859494591524205928 :=
  phaseBlock_append receipt_2_16_2384_0_join8 receipt_2_16_2384_0_join18 rfl rfl rfl

private theorem receipt_2_16_2384_0 : fastPhase (bank 2 16).shape 179808 2384 103 1 0 7 0 = 4132622797140859494591524205928 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_2_16_2384_0_join19

private theorem receipt_2_16_2384_1_part0 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 0 128 = 430205302328357692948833288672 := by decide +kernel
private theorem receipt_2_16_2384_1_part1 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 128 128 = 402516519045085782971703964128 := by decide +kernel
private theorem receipt_2_16_2384_1_part2 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 256 128 = 375562758948011388694799032800 := by decide +kernel
private theorem receipt_2_16_2384_1_part3 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 384 128 = 349332216422512232703702208992 := by decide +kernel
private theorem receipt_2_16_2384_1_part4 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 512 128 = 323813179964432615061190115808 := by decide +kernel
private theorem receipt_2_16_2384_1_part5 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 640 128 = 298994031871935999744869855712 := by decide +kernel
private theorem receipt_2_16_2384_1_part6 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 768 128 = 274863247937357601084816581088 := by decide +kernel
private theorem receipt_2_16_2384_1_part7 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 896 128 = 251409397139056970201211064800 := by decide +kernel
private theorem receipt_2_16_2384_1_part8 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 1024 128 = 228621141333270581441977270752 := by decide +kernel
private theorem receipt_2_16_2384_1_part9 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 1152 128 = 206487234945964418820419924448 := by decide +kernel
private theorem receipt_2_16_2384_1_part10 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 1280 128 = 184996524664686562452862083552 := by decide +kernel
private theorem receipt_2_16_2384_1_part11 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 1408 128 = 164137949130419774996282708448 := by decide +kernel
private theorem receipt_2_16_2384_1_part12 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 1536 128 = 143900538629434088085954232800 := by decide +kernel
private theorem receipt_2_16_2384_1_part13 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 1664 128 = 124273414785139388773080134112 := by decide +kernel
private theorem receipt_2_16_2384_1_part14 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 1792 128 = 105245798240540694756250284365 := by decide +kernel
private theorem receipt_2_16_2384_1_part15 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 1920 128 = 86807013014040592526367576394 := by decide +kernel
private theorem receipt_2_16_2384_1_part16 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 2048 128 = 68946438945871783545032870533 := by decide +kernel
private theorem receipt_2_16_2384_1_part17 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 2176 128 = 51653538608525726524463709866 := by decide +kernel
private theorem receipt_2_16_2384_1_part18 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 2304 128 = 34917864671546901583310276100 := by decide +kernel
private theorem receipt_2_16_2384_1_part19 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 2432 128 = 18729059561002853133473207615 := by decide +kernel
private theorem receipt_2_16_2384_1_part20 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 2560 90 = 3765650140894905335790005460 := by decide +kernel
private theorem receipt_2_16_2384_1_join0 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 0 256 = 832721821373443475920537252800 :=
  phaseBlock_append receipt_2_16_2384_1_part0 receipt_2_16_2384_1_part1 rfl rfl rfl
private theorem receipt_2_16_2384_1_join1 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 384 256 = 673145396386944847764892324800 :=
  phaseBlock_append receipt_2_16_2384_1_part3 receipt_2_16_2384_1_part4 rfl rfl rfl
private theorem receipt_2_16_2384_1_join2 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 256 384 = 1048708155334956236459691357600 :=
  phaseBlock_append receipt_2_16_2384_1_part2 receipt_2_16_2384_1_join1 rfl rfl rfl
private theorem receipt_2_16_2384_1_join3 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 0 640 = 1881429976708399712380228610400 :=
  phaseBlock_append receipt_2_16_2384_1_join0 receipt_2_16_2384_1_join2 rfl rfl rfl
private theorem receipt_2_16_2384_1_join4 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 640 256 = 573857279809293600829686436800 :=
  phaseBlock_append receipt_2_16_2384_1_part5 receipt_2_16_2384_1_part6 rfl rfl rfl
private theorem receipt_2_16_2384_1_join5 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 1024 256 = 435108376279235000262397195200 :=
  phaseBlock_append receipt_2_16_2384_1_part8 receipt_2_16_2384_1_part9 rfl rfl rfl
private theorem receipt_2_16_2384_1_join6 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 896 384 = 686517773418291970463608260000 :=
  phaseBlock_append receipt_2_16_2384_1_part7 receipt_2_16_2384_1_join5 rfl rfl rfl
private theorem receipt_2_16_2384_1_join7 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 640 640 = 1260375053227585571293294696800 :=
  phaseBlock_append receipt_2_16_2384_1_join4 receipt_2_16_2384_1_join6 rfl rfl rfl
private theorem receipt_2_16_2384_1_join8 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 0 1280 = 3141805029935985283673523307200 :=
  phaseBlock_append receipt_2_16_2384_1_join3 receipt_2_16_2384_1_join7 rfl rfl rfl
private theorem receipt_2_16_2384_1_join9 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 1280 256 = 349134473795106337449144792000 :=
  phaseBlock_append receipt_2_16_2384_1_part10 receipt_2_16_2384_1_part11 rfl rfl rfl
private theorem receipt_2_16_2384_1_join10 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 1664 256 = 229519213025680083529330418477 :=
  phaseBlock_append receipt_2_16_2384_1_part13 receipt_2_16_2384_1_part14 rfl rfl rfl
private theorem receipt_2_16_2384_1_join11 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 1536 384 = 373419751655114171615284651277 :=
  phaseBlock_append receipt_2_16_2384_1_part12 receipt_2_16_2384_1_join10 rfl rfl rfl
private theorem receipt_2_16_2384_1_join12 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 1280 640 = 722554225450220509064429443277 :=
  phaseBlock_append receipt_2_16_2384_1_join9 receipt_2_16_2384_1_join11 rfl rfl rfl
private theorem receipt_2_16_2384_1_join13 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 2048 256 = 120599977554397510069496580399 :=
  phaseBlock_append receipt_2_16_2384_1_part16 receipt_2_16_2384_1_part17 rfl rfl rfl
private theorem receipt_2_16_2384_1_join14 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 1920 384 = 207406990568438102595864156793 :=
  phaseBlock_append receipt_2_16_2384_1_part15 receipt_2_16_2384_1_join13 rfl rfl rfl
private theorem receipt_2_16_2384_1_join15 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 2432 218 = 22494709701897758469263213075 :=
  phaseBlock_append receipt_2_16_2384_1_part19 receipt_2_16_2384_1_part20 rfl rfl rfl
private theorem receipt_2_16_2384_1_join16 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 2304 346 = 57412574373444660052573489175 :=
  phaseBlock_append receipt_2_16_2384_1_part18 receipt_2_16_2384_1_join15 rfl rfl rfl
private theorem receipt_2_16_2384_1_join17 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 1920 730 = 264819564941882762648437645968 :=
  phaseBlock_append receipt_2_16_2384_1_join14 receipt_2_16_2384_1_join16 rfl rfl rfl
private theorem receipt_2_16_2384_1_join18 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 1280 1370 = 987373790392103271712867089245 :=
  phaseBlock_append receipt_2_16_2384_1_join12 receipt_2_16_2384_1_join17 rfl rfl rfl
private theorem receipt_2_16_2384_1_join19 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2384 103 1 0 7 1) 0 2650 = 4129178820328088555386390396445 :=
  phaseBlock_append receipt_2_16_2384_1_join8 receipt_2_16_2384_1_join18 rfl rfl rfl

private theorem receipt_2_16_2384_1 : fastPhase (bank 2 16).shape 179808 2384 103 1 0 7 1 = 4129178820328088555386390396445 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_2_16_2384_1_join19

theorem receipt_2_16 : Checked (bank 2 16) 103 0 7 := by
  refine checked_from_values (bank 2 16) 103 0 7
    (P3_7_1.checked (bank 2 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_12604_2649)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_16_2383_0 receipt_2_16_2383_1 receipt_2_16_2384_0 receipt_2_16_2384_1 (by decide +kernel) (by decide +kernel)

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
    (word : K1.I → K1_14.L) (lo : 2383 ≤ h) (hi : h ≤ 33599) (rect : Fin 4)
    (i : Fin 1) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group7_stage i)).shape
      (cutoff h rect (group7_stage i)), ¬ G∣Q :=
  (group7_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group7_avoids

end Lower6960.RescueSource
