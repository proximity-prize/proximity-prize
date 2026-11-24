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

private theorem receipt_0_16_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 0 128 = 958197845490836036898110787392 := by decide +kernel
private theorem receipt_0_16_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 128 128 = 899142513240825251266676797248 := by decide +kernel
private theorem receipt_0_16_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 256 128 = 841387162837580588348814200640 := by decide +kernel
private theorem receipt_0_16_2359_0_part3 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 384 128 = 784917207226689720057967931200 := by decide +kernel
private theorem receipt_0_16_2359_0_part4 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 512 128 = 729718076138815811591123423040 := by decide +kernel
private theorem receipt_0_16_2359_0_part5 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 640 128 = 675775216083409898214671888192 := by decide +kernel
private theorem receipt_0_16_2359_0_part6 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 768 128 = 623074090342423262050275594048 := by decide +kernel
private theorem receipt_0_16_2359_0_part7 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 896 128 = 571600178964019808860733140800 := by decide +kernel
private theorem receipt_0_16_2359_0_part8 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 1024 128 = 521338978756288444835844738880 := by decide +kernel
private theorem receipt_0_16_2359_0_part9 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 1152 128 = 472276003280955453378277486400 := by decide +kernel
private theorem receipt_0_16_2359_0_part10 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 1280 128 = 424396782847096871889430646592 := by decide +kernel
private theorem receipt_0_16_2359_0_part11 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 1408 128 = 377686864504850868555300925248 := by decide +kernel
private theorem receipt_0_16_2359_0_part12 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 1536 128 = 332131812039130119132347748160 := by decide +kernel
private theorem receipt_0_16_2359_0_part13 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 1664 128 = 287717205964927162536065958408 := by decide +kernel
private theorem receipt_0_16_2359_0_part14 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 1792 128 = 244428666230083043398884364286 := by decide +kernel
private theorem receipt_0_16_2359_0_part15 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 1920 128 = 202251851896322643198050038758 := by decide +kernel
private theorem receipt_0_16_2359_0_part16 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 2048 128 = 161172358177769193575161523934 := by decide +kernel
private theorem receipt_0_16_2359_0_part17 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 2176 128 = 121175783088880688679556756696 := by decide +kernel
private theorem receipt_0_16_2359_0_part18 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 2304 128 = 82247741389911136600087572932 := by decide +kernel
private theorem receipt_0_16_2359_0_part19 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 2432 128 = 44373864628704434690411903670 := by decide +kernel
private theorem receipt_0_16_2359_0_part20 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 2560 90 = 9084761544463547963318718402 := by decide +kernel
private theorem receipt_0_16_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 0 256 = 1857340358731661288164787584640 :=
  phaseBlock_append receipt_0_16_2359_0_part0 receipt_0_16_2359_0_part1 rfl rfl rfl
private theorem receipt_0_16_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 384 256 = 1514635283365505531649091354240 :=
  phaseBlock_append receipt_0_16_2359_0_part3 receipt_0_16_2359_0_part4 rfl rfl rfl
private theorem receipt_0_16_2359_0_join2 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 256 384 = 2356022446203086119997905554880 :=
  phaseBlock_append receipt_0_16_2359_0_part2 receipt_0_16_2359_0_join1 rfl rfl rfl
private theorem receipt_0_16_2359_0_join3 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 0 640 = 4213362804934747408162693139520 :=
  phaseBlock_append receipt_0_16_2359_0_join0 receipt_0_16_2359_0_join2 rfl rfl rfl
private theorem receipt_0_16_2359_0_join4 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 640 256 = 1298849306425833160264947482240 :=
  phaseBlock_append receipt_0_16_2359_0_part5 receipt_0_16_2359_0_part6 rfl rfl rfl
private theorem receipt_0_16_2359_0_join5 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 1024 256 = 993614982037243898214122225280 :=
  phaseBlock_append receipt_0_16_2359_0_part8 receipt_0_16_2359_0_part9 rfl rfl rfl
private theorem receipt_0_16_2359_0_join6 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 896 384 = 1565215161001263707074855366080 :=
  phaseBlock_append receipt_0_16_2359_0_part7 receipt_0_16_2359_0_join5 rfl rfl rfl
private theorem receipt_0_16_2359_0_join7 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 640 640 = 2864064467427096867339802848320 :=
  phaseBlock_append receipt_0_16_2359_0_join4 receipt_0_16_2359_0_join6 rfl rfl rfl
private theorem receipt_0_16_2359_0_join8 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 0 1280 = 7077427272361844275502495987840 :=
  phaseBlock_append receipt_0_16_2359_0_join3 receipt_0_16_2359_0_join7 rfl rfl rfl
private theorem receipt_0_16_2359_0_join9 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 1280 256 = 802083647351947740444731571840 :=
  phaseBlock_append receipt_0_16_2359_0_part10 receipt_0_16_2359_0_part11 rfl rfl rfl
private theorem receipt_0_16_2359_0_join10 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 1664 256 = 532145872195010205934950322694 :=
  phaseBlock_append receipt_0_16_2359_0_part13 receipt_0_16_2359_0_part14 rfl rfl rfl
private theorem receipt_0_16_2359_0_join11 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 1536 384 = 864277684234140325067298070854 :=
  phaseBlock_append receipt_0_16_2359_0_part12 receipt_0_16_2359_0_join10 rfl rfl rfl
private theorem receipt_0_16_2359_0_join12 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 1280 640 = 1666361331586088065512029642694 :=
  phaseBlock_append receipt_0_16_2359_0_join9 receipt_0_16_2359_0_join11 rfl rfl rfl
private theorem receipt_0_16_2359_0_join13 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 2048 256 = 282348141266649882254718280630 :=
  phaseBlock_append receipt_0_16_2359_0_part16 receipt_0_16_2359_0_part17 rfl rfl rfl
private theorem receipt_0_16_2359_0_join14 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 1920 384 = 484599993162972525452768319388 :=
  phaseBlock_append receipt_0_16_2359_0_part15 receipt_0_16_2359_0_join13 rfl rfl rfl
private theorem receipt_0_16_2359_0_join15 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 2432 218 = 53458626173167982653730622072 :=
  phaseBlock_append receipt_0_16_2359_0_part19 receipt_0_16_2359_0_part20 rfl rfl rfl
private theorem receipt_0_16_2359_0_join16 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 2304 346 = 135706367563079119253818195004 :=
  phaseBlock_append receipt_0_16_2359_0_part18 receipt_0_16_2359_0_join15 rfl rfl rfl
private theorem receipt_0_16_2359_0_join17 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 1920 730 = 620306360726051644706586514392 :=
  phaseBlock_append receipt_0_16_2359_0_join14 receipt_0_16_2359_0_join16 rfl rfl rfl
private theorem receipt_0_16_2359_0_join18 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 1280 1370 = 2286667692312139710218616157086 :=
  phaseBlock_append receipt_0_16_2359_0_join12 receipt_0_16_2359_0_join17 rfl rfl rfl
private theorem receipt_0_16_2359_0_join19 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 0) 0 2650 = 9364094964673983985721112144926 :=
  phaseBlock_append receipt_0_16_2359_0_join8 receipt_0_16_2359_0_join18 rfl rfl rfl

private theorem receipt_0_16_2359_0 : fastPhase (bank 0 16).shape 179808 2379 103 1 0 1 0 = 9364094964673983985721112144926 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_0_16_2359_0_join19

private theorem receipt_0_16_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 0 128 = 957737598458769989759540546048 := by decide +kernel
private theorem receipt_0_16_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 128 128 = 898692136709783638590388554240 := by decide +kernel
private theorem receipt_0_16_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 256 128 = 840946546479604971798877260288 := by decide +kernel
private theorem receipt_0_16_2359_1_part3 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 384 128 = 784486240841727218295910222336 := by decide +kernel
private theorem receipt_0_16_2359_1_part4 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 512 128 = 729296649654670959121382001152 := by decide +kernel
private theorem receipt_0_16_2359_1_part5 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 640 128 = 675363219555696504230043437568 := by decide +kernel
private theorem receipt_0_16_2359_1_part6 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 768 128 = 622671413954516269277366929920 := by decide +kernel
private theorem receipt_0_16_2359_1_part7 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 896 128 = 571206713027007152405411711488 := by decide +kernel
private theorem receipt_0_16_2359_1_part8 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 1024 128 = 520954613708922911028689127936 := by decide +kernel
private theorem receipt_0_16_2359_1_part9 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 1152 128 = 471900629689606538620027914752 := by decide +kernel
private theorem receipt_0_16_2359_1_part10 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 1280 128 = 424030291405702641496439474688 := by decide +kernel
private theorem receipt_0_16_2359_1_part11 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 1408 128 = 377329146034869815604983155200 := by decide +kernel
private theorem receipt_0_16_2359_1_part12 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 1536 128 = 331782757489493023308631525888 := by decide +kernel
private theorem receipt_0_16_2359_1_part13 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 1664 128 = 287376706411986796515540733418 := by decide +kernel
private theorem receipt_0_16_2359_1_part14 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 1792 128 = 244096612847810304865590208311 := by decide +kernel
private theorem receipt_0_16_2359_1_part15 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 1920 128 = 201928135901665328520818064108 := by decide +kernel
private theorem receipt_0_16_2359_1_part16 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 2048 128 = 160856870900632201497040829230 := by decide +kernel
private theorem receipt_0_16_2359_1_part17 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 2176 128 = 120868415986635246257591383188 := by decide +kernel
private theorem receipt_0_16_2359_1_part18 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 2304 128 = 81948386047395932177976213302 := by decide +kernel
private theorem receipt_0_16_2359_1_part19 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 2432 128 = 44082412758119684911496499618 := by decide +kernel
private theorem receipt_0_16_2359_1_part20 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 2560 90 = 8884508332319628385416326502 := by decide +kernel
private theorem receipt_0_16_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 0 256 = 1856429735168553628349929100288 :=
  phaseBlock_append receipt_0_16_2359_1_part0 receipt_0_16_2359_1_part1 rfl rfl rfl
private theorem receipt_0_16_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 384 256 = 1513782890496398177417292223488 :=
  phaseBlock_append receipt_0_16_2359_1_part3 receipt_0_16_2359_1_part4 rfl rfl rfl
private theorem receipt_0_16_2359_1_join2 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 256 384 = 2354729436976003149216169483776 :=
  phaseBlock_append receipt_0_16_2359_1_part2 receipt_0_16_2359_1_join1 rfl rfl rfl
private theorem receipt_0_16_2359_1_join3 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 0 640 = 4211159172144556777566098584064 :=
  phaseBlock_append receipt_0_16_2359_1_join0 receipt_0_16_2359_1_join2 rfl rfl rfl
private theorem receipt_0_16_2359_1_join4 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 640 256 = 1298034633510212773507410367488 :=
  phaseBlock_append receipt_0_16_2359_1_part5 receipt_0_16_2359_1_part6 rfl rfl rfl
private theorem receipt_0_16_2359_1_join5 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 1024 256 = 992855243398529449648717042688 :=
  phaseBlock_append receipt_0_16_2359_1_part8 receipt_0_16_2359_1_part9 rfl rfl rfl
private theorem receipt_0_16_2359_1_join6 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 896 384 = 1564061956425536602054128754176 :=
  phaseBlock_append receipt_0_16_2359_1_part7 receipt_0_16_2359_1_join5 rfl rfl rfl
private theorem receipt_0_16_2359_1_join7 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 640 640 = 2862096589935749375561539121664 :=
  phaseBlock_append receipt_0_16_2359_1_join4 receipt_0_16_2359_1_join6 rfl rfl rfl
private theorem receipt_0_16_2359_1_join8 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 0 1280 = 7073255762080306153127637705728 :=
  phaseBlock_append receipt_0_16_2359_1_join3 receipt_0_16_2359_1_join7 rfl rfl rfl
private theorem receipt_0_16_2359_1_join9 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 1280 256 = 801359437440572457101422629888 :=
  phaseBlock_append receipt_0_16_2359_1_part10 receipt_0_16_2359_1_part11 rfl rfl rfl
private theorem receipt_0_16_2359_1_join10 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 1664 256 = 531473319259797101381130941729 :=
  phaseBlock_append receipt_0_16_2359_1_part13 receipt_0_16_2359_1_part14 rfl rfl rfl
private theorem receipt_0_16_2359_1_join11 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 1536 384 = 863256076749290124689762467617 :=
  phaseBlock_append receipt_0_16_2359_1_part12 receipt_0_16_2359_1_join10 rfl rfl rfl
private theorem receipt_0_16_2359_1_join12 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 1280 640 = 1664615514189862581791185097505 :=
  phaseBlock_append receipt_0_16_2359_1_join9 receipt_0_16_2359_1_join11 rfl rfl rfl
private theorem receipt_0_16_2359_1_join13 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 2048 256 = 281725286887267447754632212418 :=
  phaseBlock_append receipt_0_16_2359_1_part16 receipt_0_16_2359_1_part17 rfl rfl rfl
private theorem receipt_0_16_2359_1_join14 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 1920 384 = 483653422788932776275450276526 :=
  phaseBlock_append receipt_0_16_2359_1_part15 receipt_0_16_2359_1_join13 rfl rfl rfl
private theorem receipt_0_16_2359_1_join15 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 2432 218 = 52966921090439313296912826120 :=
  phaseBlock_append receipt_0_16_2359_1_part19 receipt_0_16_2359_1_part20 rfl rfl rfl
private theorem receipt_0_16_2359_1_join16 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 2304 346 = 134915307137835245474889039422 :=
  phaseBlock_append receipt_0_16_2359_1_part18 receipt_0_16_2359_1_join15 rfl rfl rfl
private theorem receipt_0_16_2359_1_join17 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 1920 730 = 618568729926768021750339315948 :=
  phaseBlock_append receipt_0_16_2359_1_join14 receipt_0_16_2359_1_join16 rfl rfl rfl
private theorem receipt_0_16_2359_1_join18 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 1280 1370 = 2283184244116630603541524413453 :=
  phaseBlock_append receipt_0_16_2359_1_join12 receipt_0_16_2359_1_join17 rfl rfl rfl
private theorem receipt_0_16_2359_1_join19 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2379 103 1 0 1 1) 0 2650 = 9356440006196936756669162119181 :=
  phaseBlock_append receipt_0_16_2359_1_join8 receipt_0_16_2359_1_join18 rfl rfl rfl

private theorem receipt_0_16_2359_1 : fastPhase (bank 0 16).shape 179808 2379 103 1 0 1 1 = 9356440006196936756669162119181 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_0_16_2359_1_join19

private theorem receipt_0_16_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 0 128 = 958206478133548031318433550432 := by decide +kernel
private theorem receipt_0_16_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 128 128 = 899150396509594467015208353888 := by decide +kernel
private theorem receipt_0_16_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 256 128 = 841394333319516245889754804320 := by decide +kernel
private theorem receipt_0_16_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 384 128 = 784923701006335124481623466080 := by decide +kernel
private theorem receipt_0_16_2360_0_part4 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 512 128 = 729723928798733121172989087840 := by decide +kernel
private theorem receipt_0_16_2360_0_part5 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 640 128 = 675780462704764673072190324832 := by decide +kernel
private theorem receipt_0_16_2360_0_part6 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 768 128 = 623078765505568792897269461088 := by decide +kernel
private theorem receipt_0_16_2360_0_part7 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 896 128 = 571604316749081225859512131680 := by decide +kernel
private theorem receipt_0_16_2360_0_part8 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 1024 128 = 521342612743746606546987044960 := by decide +kernel
private theorem receipt_0_16_2360_0_part9 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 1152 128 = 472279166552230615808085704800 := by decide +kernel
private theorem receipt_0_16_2360_0_part10 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 1280 128 = 424399507985132137635062132832 := by decide +kernel
private theorem receipt_0_16_2360_0_part11 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 1408 128 = 377689183594695416047572590688 := by decide +kernel
private theorem receipt_0_16_2360_0_part12 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 1536 128 = 332133756668522211976215302240 := by decide +kernel
private theorem receipt_0_16_2360_0_part13 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 1664 128 = 287718807223283960146070175840 := by decide +kernel
private theorem receipt_0_16_2360_0_part14 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 1792 128 = 244429953843156801227899986664 := by decide +kernel
private theorem receipt_0_16_2360_0_part15 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 1920 128 = 202252855816475241566113058085 := by decide +kernel
private theorem receipt_0_16_2360_0_part16 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 2048 128 = 161173108515007627322366848380 := by decide +kernel
private theorem receipt_0_16_2360_0_part17 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 2176 128 = 121176309413291120278996097702 := by decide +kernel
private theorem receipt_0_16_2360_0_part18 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 2304 128 = 82248072735532338349144762891 := by decide +kernel
private theorem receipt_0_16_2360_0_part19 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 2432 128 = 44374029502964284658759045751 := by decide +kernel
private theorem receipt_0_16_2360_0_part20 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 2560 90 = 9084792904923932819882652345 := by decide +kernel
private theorem receipt_0_16_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 0 256 = 1857356874643142498333641904320 :=
  phaseBlock_append receipt_0_16_2360_0_part0 receipt_0_16_2360_0_part1 rfl rfl rfl
private theorem receipt_0_16_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 384 256 = 1514647629805068245654612553920 :=
  phaseBlock_append receipt_0_16_2360_0_part3 receipt_0_16_2360_0_part4 rfl rfl rfl
private theorem receipt_0_16_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 256 384 = 2356041963124584491544367358240 :=
  phaseBlock_append receipt_0_16_2360_0_part2 receipt_0_16_2360_0_join1 rfl rfl rfl
private theorem receipt_0_16_2360_0_join3 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 0 640 = 4213398837767726989878009262560 :=
  phaseBlock_append receipt_0_16_2360_0_join0 receipt_0_16_2360_0_join2 rfl rfl rfl
private theorem receipt_0_16_2360_0_join4 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 640 256 = 1298859228210333465969459785920 :=
  phaseBlock_append receipt_0_16_2360_0_part5 receipt_0_16_2360_0_part6 rfl rfl rfl
private theorem receipt_0_16_2360_0_join5 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 1024 256 = 993621779295977222355072749760 :=
  phaseBlock_append receipt_0_16_2360_0_part8 receipt_0_16_2360_0_part9 rfl rfl rfl
private theorem receipt_0_16_2360_0_join6 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 896 384 = 1565226096045058448214584881440 :=
  phaseBlock_append receipt_0_16_2360_0_part7 receipt_0_16_2360_0_join5 rfl rfl rfl
private theorem receipt_0_16_2360_0_join7 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 640 640 = 2864085324255391914184044667360 :=
  phaseBlock_append receipt_0_16_2360_0_join4 receipt_0_16_2360_0_join6 rfl rfl rfl
private theorem receipt_0_16_2360_0_join8 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 0 1280 = 7077484162023118904062053929920 :=
  phaseBlock_append receipt_0_16_2360_0_join3 receipt_0_16_2360_0_join7 rfl rfl rfl
private theorem receipt_0_16_2360_0_join9 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 1280 256 = 802088691579827553682634723520 :=
  phaseBlock_append receipt_0_16_2360_0_part10 receipt_0_16_2360_0_part11 rfl rfl rfl
private theorem receipt_0_16_2360_0_join10 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 1664 256 = 532148761066440761373970162504 :=
  phaseBlock_append receipt_0_16_2360_0_part13 receipt_0_16_2360_0_part14 rfl rfl rfl
private theorem receipt_0_16_2360_0_join11 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 1536 384 = 864282517734962973350185464744 :=
  phaseBlock_append receipt_0_16_2360_0_part12 receipt_0_16_2360_0_join10 rfl rfl rfl
private theorem receipt_0_16_2360_0_join12 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 1280 640 = 1666371209314790527032820188264 :=
  phaseBlock_append receipt_0_16_2360_0_join9 receipt_0_16_2360_0_join11 rfl rfl rfl
private theorem receipt_0_16_2360_0_join13 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 2048 256 = 282349417928298747601362946082 :=
  phaseBlock_append receipt_0_16_2360_0_part16 receipt_0_16_2360_0_part17 rfl rfl rfl
private theorem receipt_0_16_2360_0_join14 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 1920 384 = 484602273744773989167476004167 :=
  phaseBlock_append receipt_0_16_2360_0_part15 receipt_0_16_2360_0_join13 rfl rfl rfl
private theorem receipt_0_16_2360_0_join15 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 2432 218 = 53458822407888217478641698096 :=
  phaseBlock_append receipt_0_16_2360_0_part19 receipt_0_16_2360_0_part20 rfl rfl rfl
private theorem receipt_0_16_2360_0_join16 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 2304 346 = 135706895143420555827786460987 :=
  phaseBlock_append receipt_0_16_2360_0_part18 receipt_0_16_2360_0_join15 rfl rfl rfl
private theorem receipt_0_16_2360_0_join17 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 1920 730 = 620309168888194544995262465154 :=
  phaseBlock_append receipt_0_16_2360_0_join14 receipt_0_16_2360_0_join16 rfl rfl rfl
private theorem receipt_0_16_2360_0_join18 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 1280 1370 = 2286680378202985072028082653418 :=
  phaseBlock_append receipt_0_16_2360_0_join12 receipt_0_16_2360_0_join17 rfl rfl rfl
private theorem receipt_0_16_2360_0_join19 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 0) 0 2650 = 9364164540226103976090136583338 :=
  phaseBlock_append receipt_0_16_2360_0_join8 receipt_0_16_2360_0_join18 rfl rfl rfl

private theorem receipt_0_16_2360_0 : fastPhase (bank 0 16).shape 179808 2380 103 1 0 1 0 = 9364164540226103976090136583338 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_0_16_2360_0_join19

private theorem receipt_0_16_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 0 128 = 957746227709495720004043876960 := by decide +kernel
private theorem receipt_0_16_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 128 128 = 898700016730516679981253057120 := by decide +kernel
private theorem receipt_0_16_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 256 128 = 840953713855080615830870198880 := by decide +kernel
private theorem receipt_0_16_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 384 128 = 784492731654118043395508681312 := by decide +kernel
private theorem receipt_0_16_2360_1_part4 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 512 128 = 729302499484171597900186511968 := by decide +kernel
private theorem receipt_0_16_2360_1_part5 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 640 128 = 675368463481108190835866049120 := by decide +kernel
private theorem receipt_0_16_2360_1_part6 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 768 128 = 622676086553831166842993724000 := by decide +kernel
private theorem receipt_0_16_2360_1_part7 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 896 128 = 571210848377992460595039763040 := by decide +kernel
private theorem receipt_0_16_2360_1_part8 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 1024 128 = 520958245389704753682037910112 := by decide +kernel
private theorem receipt_0_16_2360_1_part9 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 1152 128 = 471903790779253631494125148768 := by decide +kernel
private theorem receipt_0_16_2360_1_part10 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 1280 128 = 424033014484809740105081424480 := by decide +kernel
private theorem receipt_0_16_2360_1_part11 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 1408 128 = 377331463186140943155869366880 := by decide +kernel
private theorem receipt_0_16_2360_1_part12 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 1536 128 = 331784700298324478738174012000 := by decide +kernel
private theorem receipt_0_16_2360_1_part13 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 1664 128 = 287378305965459116277942524512 := by decide +kernel
private theorem receipt_0_16_2360_1_part14 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 1792 128 = 244097898870460312542662606913 := by decide +kernel
private theorem receipt_0_16_2360_1_part15 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 1920 128 = 201929138344144318915992197445 := by decide +kernel
private theorem receipt_0_16_2360_1_part16 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 2048 128 = 160857619870503998933237902610 := by decide +kernel
private theorem receipt_0_16_2360_1_part17 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 2176 128 = 120868941051552289746220055028 := by decide +kernel
private theorem receipt_0_16_2360_1_part18 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 2304 128 = 81948716238976113285291381085 := by decide +kernel
private theorem receipt_0_16_2360_1_part19 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 2432 128 = 44082576581345465338155462693 := by decide +kernel
private theorem receipt_0_16_2360_1_part20 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 2560 90 = 8884539014138727410265563307 := by decide +kernel
private theorem receipt_0_16_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 0 256 = 1856446244440012399985296934080 :=
  phaseBlock_append receipt_0_16_2360_1_part0 receipt_0_16_2360_1_part1 rfl rfl rfl
private theorem receipt_0_16_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 384 256 = 1513795231138289641295695193280 :=
  phaseBlock_append receipt_0_16_2360_1_part3 receipt_0_16_2360_1_part4 rfl rfl rfl
private theorem receipt_0_16_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 256 384 = 2354748944993370257126565392160 :=
  phaseBlock_append receipt_0_16_2360_1_part2 receipt_0_16_2360_1_join1 rfl rfl rfl
private theorem receipt_0_16_2360_1_join3 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 0 640 = 4211195189433382657111862326240 :=
  phaseBlock_append receipt_0_16_2360_1_join0 receipt_0_16_2360_1_join2 rfl rfl rfl
private theorem receipt_0_16_2360_1_join4 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 640 256 = 1298044550034939357678859773120 :=
  phaseBlock_append receipt_0_16_2360_1_part5 receipt_0_16_2360_1_part6 rfl rfl rfl
private theorem receipt_0_16_2360_1_join5 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 1024 256 = 992862036168958385176163058880 :=
  phaseBlock_append receipt_0_16_2360_1_part8 receipt_0_16_2360_1_part9 rfl rfl rfl
private theorem receipt_0_16_2360_1_join6 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 896 384 = 1564072884546950845771202821920 :=
  phaseBlock_append receipt_0_16_2360_1_part7 receipt_0_16_2360_1_join5 rfl rfl rfl
private theorem receipt_0_16_2360_1_join7 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 640 640 = 2862117434581890203450062595040 :=
  phaseBlock_append receipt_0_16_2360_1_join4 receipt_0_16_2360_1_join6 rfl rfl rfl
private theorem receipt_0_16_2360_1_join8 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 0 1280 = 7073312624015272860561924921280 :=
  phaseBlock_append receipt_0_16_2360_1_join3 receipt_0_16_2360_1_join7 rfl rfl rfl
private theorem receipt_0_16_2360_1_join9 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 1280 256 = 801364477670950683260950791360 :=
  phaseBlock_append receipt_0_16_2360_1_part10 receipt_0_16_2360_1_part11 rfl rfl rfl
private theorem receipt_0_16_2360_1_join10 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 1664 256 = 531476204835919428820605131425 :=
  phaseBlock_append receipt_0_16_2360_1_part13 receipt_0_16_2360_1_part14 rfl rfl rfl
private theorem receipt_0_16_2360_1_join11 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 1536 384 = 863260905134243907558779143425 :=
  phaseBlock_append receipt_0_16_2360_1_part12 receipt_0_16_2360_1_join10 rfl rfl rfl
private theorem receipt_0_16_2360_1_join12 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 1280 640 = 1664625382805194590819729934785 :=
  phaseBlock_append receipt_0_16_2360_1_join9 receipt_0_16_2360_1_join11 rfl rfl rfl
private theorem receipt_0_16_2360_1_join13 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 2048 256 = 281726560922056288679457957638 :=
  phaseBlock_append receipt_0_16_2360_1_part16 receipt_0_16_2360_1_part17 rfl rfl rfl
private theorem receipt_0_16_2360_1_join14 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 1920 384 = 483655699266200607595450155083 :=
  phaseBlock_append receipt_0_16_2360_1_part15 receipt_0_16_2360_1_join13 rfl rfl rfl
private theorem receipt_0_16_2360_1_join15 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 2432 218 = 52967115595484192748421026000 :=
  phaseBlock_append receipt_0_16_2360_1_part19 receipt_0_16_2360_1_part20 rfl rfl rfl
private theorem receipt_0_16_2360_1_join16 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 2304 346 = 134915831834460306033712407085 :=
  phaseBlock_append receipt_0_16_2360_1_part18 receipt_0_16_2360_1_join15 rfl rfl rfl
private theorem receipt_0_16_2360_1_join17 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 1920 730 = 618571531100660913629162562168 :=
  phaseBlock_append receipt_0_16_2360_1_join14 receipt_0_16_2360_1_join16 rfl rfl rfl
private theorem receipt_0_16_2360_1_join18 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 1280 1370 = 2283196913905855504448892496953 :=
  phaseBlock_append receipt_0_16_2360_1_join12 receipt_0_16_2360_1_join17 rfl rfl rfl
private theorem receipt_0_16_2360_1_join19 :
    phaseBlock (fastLayer (bank 0 16).shape 179808 2380 103 1 0 1 1) 0 2650 = 9356509537921128365010817418233 :=
  phaseBlock_append receipt_0_16_2360_1_join8 receipt_0_16_2360_1_join18 rfl rfl rfl

private theorem receipt_0_16_2360_1 : fastPhase (bank 0 16).shape 179808 2380 103 1 0 1 1 = 9356509537921128365010817418233 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_0_16_2360_1_join19

theorem receipt_0_16 : Checked (bank 0 16) 103 0 1 := by
  refine checked_from_values (bank 0 16) 103 0 1
    (P3_7_1.checked (bank 0 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_12604_2649)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_16_2359_0 receipt_0_16_2359_1 receipt_0_16_2360_0 receipt_0_16_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_16_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 0 128 = 862688467772838713487355031104 := by decide +kernel
private theorem receipt_1_16_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 128 128 = 809245168282519287503715618368 := by decide +kernel
private theorem receipt_1_16_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 256 128 = 757007492220633217147060448832 := by decide +kernel
private theorem receipt_1_16_2359_0_part3 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 384 128 = 705961136637797908236391026240 := by decide +kernel
private theorem receipt_1_16_2359_0_part4 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 512 128 = 656091831166131726118386052672 := by decide +kernel
private theorem receipt_1_16_2359_0_part5 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 640 128 = 607385337994103502810862538304 := by decide +kernel
private theorem receipt_1_16_2359_0_part6 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 768 128 = 559827451841382044146236911168 := by decide +kernel
private theorem receipt_1_16_2359_0_part7 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 896 128 = 513403999933685636914986126912 := by decide +kernel
private theorem receipt_1_16_2359_0_part8 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 1024 128 = 468100841977631556009108778560 := by decide +kernel
private theorem receipt_1_16_2359_0_part9 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 1152 128 = 423903870135585571565586206272 := by decide +kernel
private theorem receipt_1_16_2359_0_part10 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 1280 128 = 380799009000511456109843607104 := by decide +kernel
private theorem receipt_1_16_2359_0_part11 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 1408 128 = 338772215570820491699211144768 := by decide +kernel
private theorem receipt_1_16_2359_0_part12 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 1536 128 = 297809479225220977066385059392 := by decide +kernel
private theorem receipt_1_16_2359_0_part13 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 1664 128 = 257896821698995362045675085760 := by decide +kernel
private theorem receipt_1_16_2359_0_part14 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 1792 128 = 219020317405701047757768573783 := by decide +kernel
private theorem receipt_1_16_2359_0_part15 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 1920 128 = 181166093101750297748194615389 := by decide +kernel
private theorem receipt_1_16_2359_0_part16 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 2048 128 = 144320235634062945557294555998 := by decide +kernel
private theorem receipt_1_16_2359_0_part17 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 2176 128 = 108468851701265547260396279442 := by decide +kernel
private theorem receipt_1_16_2359_0_part18 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 2304 128 = 73598080335384887932945221668 := by decide +kernel
private theorem receipt_1_16_2359_0_part19 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 2432 128 = 39694092919649207631952189479 := by decide +kernel
private theorem receipt_1_16_2359_0_part20 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 2560 90 = 8124422310612230551849265751 := by decide +kernel
private theorem receipt_1_16_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 0 256 = 1671933636055358000991070649472 :=
  phaseBlock_append receipt_1_16_2359_0_part0 receipt_1_16_2359_0_part1 rfl rfl rfl
private theorem receipt_1_16_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 384 256 = 1362052967803929634354777078912 :=
  phaseBlock_append receipt_1_16_2359_0_part3 receipt_1_16_2359_0_part4 rfl rfl rfl
private theorem receipt_1_16_2359_0_join2 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 256 384 = 2119060460024562851501837527744 :=
  phaseBlock_append receipt_1_16_2359_0_part2 receipt_1_16_2359_0_join1 rfl rfl rfl
private theorem receipt_1_16_2359_0_join3 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 0 640 = 3790994096079920852492908177216 :=
  phaseBlock_append receipt_1_16_2359_0_join0 receipt_1_16_2359_0_join2 rfl rfl rfl
private theorem receipt_1_16_2359_0_join4 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 640 256 = 1167212789835485546957099449472 :=
  phaseBlock_append receipt_1_16_2359_0_part5 receipt_1_16_2359_0_part6 rfl rfl rfl
private theorem receipt_1_16_2359_0_join5 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 1024 256 = 892004712113217127574694984832 :=
  phaseBlock_append receipt_1_16_2359_0_part8 receipt_1_16_2359_0_part9 rfl rfl rfl
private theorem receipt_1_16_2359_0_join6 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 896 384 = 1405408712046902764489681111744 :=
  phaseBlock_append receipt_1_16_2359_0_part7 receipt_1_16_2359_0_join5 rfl rfl rfl
private theorem receipt_1_16_2359_0_join7 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 640 640 = 2572621501882388311446780561216 :=
  phaseBlock_append receipt_1_16_2359_0_join4 receipt_1_16_2359_0_join6 rfl rfl rfl
private theorem receipt_1_16_2359_0_join8 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 0 1280 = 6363615597962309163939688738432 :=
  phaseBlock_append receipt_1_16_2359_0_join3 receipt_1_16_2359_0_join7 rfl rfl rfl
private theorem receipt_1_16_2359_0_join9 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 1280 256 = 719571224571331947809054751872 :=
  phaseBlock_append receipt_1_16_2359_0_part10 receipt_1_16_2359_0_part11 rfl rfl rfl
private theorem receipt_1_16_2359_0_join10 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 1664 256 = 476917139104696409803443659543 :=
  phaseBlock_append receipt_1_16_2359_0_part13 receipt_1_16_2359_0_part14 rfl rfl rfl
private theorem receipt_1_16_2359_0_join11 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 1536 384 = 774726618329917386869828718935 :=
  phaseBlock_append receipt_1_16_2359_0_part12 receipt_1_16_2359_0_join10 rfl rfl rfl
private theorem receipt_1_16_2359_0_join12 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 1280 640 = 1494297842901249334678883470807 :=
  phaseBlock_append receipt_1_16_2359_0_join9 receipt_1_16_2359_0_join11 rfl rfl rfl
private theorem receipt_1_16_2359_0_join13 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 2048 256 = 252789087335328492817690835440 :=
  phaseBlock_append receipt_1_16_2359_0_part16 receipt_1_16_2359_0_part17 rfl rfl rfl
private theorem receipt_1_16_2359_0_join14 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 1920 384 = 433955180437078790565885450829 :=
  phaseBlock_append receipt_1_16_2359_0_part15 receipt_1_16_2359_0_join13 rfl rfl rfl
private theorem receipt_1_16_2359_0_join15 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 2432 218 = 47818515230261438183801455230 :=
  phaseBlock_append receipt_1_16_2359_0_part19 receipt_1_16_2359_0_part20 rfl rfl rfl
private theorem receipt_1_16_2359_0_join16 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 2304 346 = 121416595565646326116746676898 :=
  phaseBlock_append receipt_1_16_2359_0_part18 receipt_1_16_2359_0_join15 rfl rfl rfl
private theorem receipt_1_16_2359_0_join17 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 1920 730 = 555371776002725116682632127727 :=
  phaseBlock_append receipt_1_16_2359_0_join14 receipt_1_16_2359_0_join16 rfl rfl rfl
private theorem receipt_1_16_2359_0_join18 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 1280 1370 = 2049669618903974451361515598534 :=
  phaseBlock_append receipt_1_16_2359_0_join12 receipt_1_16_2359_0_join17 rfl rfl rfl
private theorem receipt_1_16_2359_0_join19 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 0) 0 2650 = 8413285216866283615301204336966 :=
  phaseBlock_append receipt_1_16_2359_0_join8 receipt_1_16_2359_0_join18 rfl rfl rfl

private theorem receipt_1_16_2359_0 : fastPhase (bank 1 16).shape 179808 2379 103 1 0 2 0 = 8413285216866283615301204336966 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_1_16_2359_0_join19

private theorem receipt_1_16_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 0 128 = 862271813276828572250885305344 := by decide +kernel
private theorem receipt_1_16_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 128 128 = 808837678373480881913008010240 := by decide +kernel
private theorem receipt_1_16_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 256 128 = 756609058566635385834091951104 := by decide +kernel
private theorem receipt_1_16_2359_1_part3 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 384 128 = 705571651155280275004972250112 := by decide +kernel
private theorem receipt_1_16_2359_1_part4 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 512 128 = 655711186019712135325963236352 := by decide +kernel
private theorem receipt_1_16_2359_1_part5 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 640 128 = 607013425596385454750319555584 := by decide +kernel
private theorem receipt_1_16_2359_1_part6 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 768 128 = 559464164852762130427697280000 := by decide +kernel
private theorem receipt_1_16_2359_1_part7 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 896 128 = 513049231262160975847615017984 := by decide +kernel
private theorem receipt_1_16_2359_1_part8 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 1024 128 = 467754484778607227982915023872 := by decide +kernel
private theorem receipt_1_16_2359_1_part9 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 1152 128 = 423565817811682054433224307712 := by decide +kernel
private theorem receipt_1_16_2359_1_part10 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 1280 128 = 380469155201372060568415745024 := by decide +kernel
private theorem receipt_1_16_2359_1_part11 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 1408 128 = 338450454192918796672069186560 := by decide +kernel
private theorem receipt_1_16_2359_1_part12 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 1536 128 = 297495704411668265084932568064 := by decide +kernel
private theorem receipt_1_16_2359_1_part13 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 1664 128 = 257590927839346121797252493309 := by decide +kernel
private theorem receipt_1_16_2359_1_part14 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 1792 128 = 218722199109045769050935992650 := by decide +kernel
private theorem receipt_1_16_2359_1_part15 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 1920 128 = 180875645147601888937304255535 := by decide +kernel
private theorem receipt_1_16_2359_1_part16 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 2048 128 = 144037353035164916034291454916 := by decide +kernel
private theorem receipt_1_16_2359_1_part17 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 2176 128 = 108193429716482203540580410465 := by decide +kernel
private theorem receipt_1_16_2359_1_part18 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 2304 128 = 73330014469552545563395263384 := by decide +kernel
private theorem receipt_1_16_2359_1_part19 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 2432 128 = 39433278923331441165202006548 := by decide +kernel
private theorem receipt_1_16_2359_1_part20 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 2560 90 = 7945323441448515302569665690 := by decide +kernel
private theorem receipt_1_16_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 0 256 = 1671109491650309454163893315584 :=
  phaseBlock_append receipt_1_16_2359_1_part0 receipt_1_16_2359_1_part1 rfl rfl rfl
private theorem receipt_1_16_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 384 256 = 1361282837174992410330935486464 :=
  phaseBlock_append receipt_1_16_2359_1_part3 receipt_1_16_2359_1_part4 rfl rfl rfl
private theorem receipt_1_16_2359_1_join2 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 256 384 = 2117891895741627796165027437568 :=
  phaseBlock_append receipt_1_16_2359_1_part2 receipt_1_16_2359_1_join1 rfl rfl rfl
private theorem receipt_1_16_2359_1_join3 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 0 640 = 3789001387391937250328920753152 :=
  phaseBlock_append receipt_1_16_2359_1_join0 receipt_1_16_2359_1_join2 rfl rfl rfl
private theorem receipt_1_16_2359_1_join4 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 640 256 = 1166477590449147585178016835584 :=
  phaseBlock_append receipt_1_16_2359_1_part5 receipt_1_16_2359_1_part6 rfl rfl rfl
private theorem receipt_1_16_2359_1_join5 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 1024 256 = 891320302590289282416139331584 :=
  phaseBlock_append receipt_1_16_2359_1_part8 receipt_1_16_2359_1_part9 rfl rfl rfl
private theorem receipt_1_16_2359_1_join6 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 896 384 = 1404369533852450258263754349568 :=
  phaseBlock_append receipt_1_16_2359_1_part7 receipt_1_16_2359_1_join5 rfl rfl rfl
private theorem receipt_1_16_2359_1_join7 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 640 640 = 2570847124301597843441771185152 :=
  phaseBlock_append receipt_1_16_2359_1_join4 receipt_1_16_2359_1_join6 rfl rfl rfl
private theorem receipt_1_16_2359_1_join8 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 0 1280 = 6359848511693535093770691938304 :=
  phaseBlock_append receipt_1_16_2359_1_join3 receipt_1_16_2359_1_join7 rfl rfl rfl
private theorem receipt_1_16_2359_1_join9 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 1280 256 = 718919609394290857240484931584 :=
  phaseBlock_append receipt_1_16_2359_1_part10 receipt_1_16_2359_1_part11 rfl rfl rfl
private theorem receipt_1_16_2359_1_join10 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 1664 256 = 476313126948391890848188485959 :=
  phaseBlock_append receipt_1_16_2359_1_part13 receipt_1_16_2359_1_part14 rfl rfl rfl
private theorem receipt_1_16_2359_1_join11 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 1536 384 = 773808831360060155933121054023 :=
  phaseBlock_append receipt_1_16_2359_1_part12 receipt_1_16_2359_1_join10 rfl rfl rfl
private theorem receipt_1_16_2359_1_join12 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 1280 640 = 1492728440754351013173605985607 :=
  phaseBlock_append receipt_1_16_2359_1_join9 receipt_1_16_2359_1_join11 rfl rfl rfl
private theorem receipt_1_16_2359_1_join13 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 2048 256 = 252230782751647119574871865381 :=
  phaseBlock_append receipt_1_16_2359_1_part16 receipt_1_16_2359_1_part17 rfl rfl rfl
private theorem receipt_1_16_2359_1_join14 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 1920 384 = 433106427899249008512176120916 :=
  phaseBlock_append receipt_1_16_2359_1_part15 receipt_1_16_2359_1_join13 rfl rfl rfl
private theorem receipt_1_16_2359_1_join15 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 2432 218 = 47378602364779956467771672238 :=
  phaseBlock_append receipt_1_16_2359_1_part19 receipt_1_16_2359_1_part20 rfl rfl rfl
private theorem receipt_1_16_2359_1_join16 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 2304 346 = 120708616834332502031166935622 :=
  phaseBlock_append receipt_1_16_2359_1_part18 receipt_1_16_2359_1_join15 rfl rfl rfl
private theorem receipt_1_16_2359_1_join17 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 1920 730 = 553815044733581510543343056538 :=
  phaseBlock_append receipt_1_16_2359_1_join14 receipt_1_16_2359_1_join16 rfl rfl rfl
private theorem receipt_1_16_2359_1_join18 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 1280 1370 = 2046543485487932523716949042145 :=
  phaseBlock_append receipt_1_16_2359_1_join12 receipt_1_16_2359_1_join17 rfl rfl rfl
private theorem receipt_1_16_2359_1_join19 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2379 103 1 0 2 1) 0 2650 = 8406391997181467617487640980449 :=
  phaseBlock_append receipt_1_16_2359_1_join8 receipt_1_16_2359_1_join18 rfl rfl rfl

private theorem receipt_1_16_2359_1 : fastPhase (bank 1 16).shape 179808 2379 103 1 0 2 1 = 8406391997181467617487640980449 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_1_16_2359_1_join19

private theorem receipt_1_16_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 0 128 = 862696239953658090667439005824 := by decide +kernel
private theorem receipt_1_16_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 128 128 = 809252263378207498982188769408 := by decide +kernel
private theorem receipt_1_16_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 256 128 = 757013943606200602436989886592 := by decide +kernel
private theorem receipt_1_16_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 384 128 = 705966977202827626833053376640 := by decide +kernel
private theorem receipt_1_16_2360_0_part4 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 512 128 = 656097093315910177773289775232 := by decide +kernel
private theorem receipt_1_16_2360_0_part5 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 640 128 = 607390053650749868196468023424 := by decide +kernel
private theorem receipt_1_16_2360_0_part6 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 768 128 = 559831652444976945911374356608 := by decide +kernel
private theorem receipt_1_16_2360_0_part7 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 896 128 = 513407716443398921130971193472 := by decide +kernel
private theorem receipt_1_16_2360_0_part8 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 1024 128 = 468104104872849194006556024960 := by decide +kernel
private theorem receipt_1_16_2360_0_part9 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 1152 128 = 423906709417035682161920303232 := by decide +kernel
private theorem receipt_1_16_2360_0_part10 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 1280 128 = 380801454191389448227508330624 := by decide +kernel
private theorem receipt_1_16_2360_0_part11 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 1408 128 = 338774295717913327374576148608 := by decide +kernel
private theorem receipt_1_16_2360_0_part12 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 1536 128 = 297811222900030554849350426752 := by decide +kernel
private theorem receipt_1_16_2360_0_part13 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 1664 128 = 257898256997433393507187351680 := by decide +kernel
private theorem receipt_1_16_2360_0_part14 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 1792 128 = 219021471173334244474667977206 := by decide +kernel
private theorem receipt_1_16_2360_0_part15 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 1920 128 = 181166992359825697151526090661 := by decide +kernel
private theorem receipt_1_16_2360_0_part16 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 2048 128 = 144320907517589831231504115500 := by decide +kernel
private theorem receipt_1_16_2360_0_part17 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 2176 128 = 108469322834360961922228743064 := by decide +kernel
private theorem receipt_1_16_2360_0_part18 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 2304 128 = 73598376835393260903202091450 := by decide +kernel
private theorem receipt_1_16_2360_0_part19 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 2432 128 = 39694240406230517725101395463 := by decide +kernel
private theorem receipt_1_16_2360_0_part20 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 2560 90 = 8124450356021431437588743811 := by decide +kernel
private theorem receipt_1_16_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 0 256 = 1671948503331865589649627775232 :=
  phaseBlock_append receipt_1_16_2360_0_part0 receipt_1_16_2360_0_part1 rfl rfl rfl
private theorem receipt_1_16_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 384 256 = 1362064070518737804606343151872 :=
  phaseBlock_append receipt_1_16_2360_0_part3 receipt_1_16_2360_0_part4 rfl rfl rfl
private theorem receipt_1_16_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 256 384 = 2119078014124938407043333038464 :=
  phaseBlock_append receipt_1_16_2360_0_part2 receipt_1_16_2360_0_join1 rfl rfl rfl
private theorem receipt_1_16_2360_0_join3 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 0 640 = 3791026517456803996692960813696 :=
  phaseBlock_append receipt_1_16_2360_0_join0 receipt_1_16_2360_0_join2 rfl rfl rfl
private theorem receipt_1_16_2360_0_join4 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 640 256 = 1167221706095726814107842380032 :=
  phaseBlock_append receipt_1_16_2360_0_part5 receipt_1_16_2360_0_part6 rfl rfl rfl
private theorem receipt_1_16_2360_0_join5 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 1024 256 = 892010814289884876168476328192 :=
  phaseBlock_append receipt_1_16_2360_0_part8 receipt_1_16_2360_0_part9 rfl rfl rfl
private theorem receipt_1_16_2360_0_join6 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 896 384 = 1405418530733283797299447521664 :=
  phaseBlock_append receipt_1_16_2360_0_part7 receipt_1_16_2360_0_join5 rfl rfl rfl
private theorem receipt_1_16_2360_0_join7 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 640 640 = 2572640236829010611407289901696 :=
  phaseBlock_append receipt_1_16_2360_0_join4 receipt_1_16_2360_0_join6 rfl rfl rfl
private theorem receipt_1_16_2360_0_join8 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 0 1280 = 6363666754285814608100250715392 :=
  phaseBlock_append receipt_1_16_2360_0_join3 receipt_1_16_2360_0_join7 rfl rfl rfl
private theorem receipt_1_16_2360_0_join9 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 1280 256 = 719575749909302775602084479232 :=
  phaseBlock_append receipt_1_16_2360_0_part10 receipt_1_16_2360_0_part11 rfl rfl rfl
private theorem receipt_1_16_2360_0_join10 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 1664 256 = 476919728170767637981855328886 :=
  phaseBlock_append receipt_1_16_2360_0_part13 receipt_1_16_2360_0_part14 rfl rfl rfl
private theorem receipt_1_16_2360_0_join11 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 1536 384 = 774730951070798192831205755638 :=
  phaseBlock_append receipt_1_16_2360_0_part12 receipt_1_16_2360_0_join10 rfl rfl rfl
private theorem receipt_1_16_2360_0_join12 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 1280 640 = 1494306700980100968433290234870 :=
  phaseBlock_append receipt_1_16_2360_0_join9 receipt_1_16_2360_0_join11 rfl rfl rfl
private theorem receipt_1_16_2360_0_join13 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 2048 256 = 252790230351950793153732858564 :=
  phaseBlock_append receipt_1_16_2360_0_part16 receipt_1_16_2360_0_part17 rfl rfl rfl
private theorem receipt_1_16_2360_0_join14 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 1920 384 = 433957222711776490305258949225 :=
  phaseBlock_append receipt_1_16_2360_0_part15 receipt_1_16_2360_0_join13 rfl rfl rfl
private theorem receipt_1_16_2360_0_join15 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 2432 218 = 47818690762251949162690139274 :=
  phaseBlock_append receipt_1_16_2360_0_part19 receipt_1_16_2360_0_part20 rfl rfl rfl
private theorem receipt_1_16_2360_0_join16 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 2304 346 = 121417067597645210065892230724 :=
  phaseBlock_append receipt_1_16_2360_0_part18 receipt_1_16_2360_0_join15 rfl rfl rfl
private theorem receipt_1_16_2360_0_join17 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 1920 730 = 555374290309421700371151179949 :=
  phaseBlock_append receipt_1_16_2360_0_join14 receipt_1_16_2360_0_join16 rfl rfl rfl
private theorem receipt_1_16_2360_0_join18 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 1280 1370 = 2049680991289522668804441414819 :=
  phaseBlock_append receipt_1_16_2360_0_join12 receipt_1_16_2360_0_join17 rfl rfl rfl
private theorem receipt_1_16_2360_0_join19 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 0) 0 2650 = 8413347745575337276904692130211 :=
  phaseBlock_append receipt_1_16_2360_0_join8 receipt_1_16_2360_0_join18 rfl rfl rfl

private theorem receipt_1_16_2360_0 : fastPhase (bank 1 16).shape 179808 2380 103 1 0 2 0 = 8413347745575337276904692130211 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_1_16_2360_0_join19

private theorem receipt_1_16_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 0 128 = 862279582383188324768001852672 := by decide +kernel
private theorem receipt_1_16_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 128 128 = 808844770527086192881903699200 := by decide +kernel
private theorem receipt_1_16_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 256 128 = 756615507140186235497410364672 := by decide +kernel
private theorem receipt_1_16_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 384 128 = 705577489036055662983626851584 := by decide +kernel
private theorem receipt_1_16_2360_1_part4 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 512 128 = 655716445610700495670479455488 := by decide +kernel
private theorem receipt_1_16_2360_1_part5 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 640 128 = 607018138817414191382874653952 := by decide +kernel
private theorem receipt_1_16_2360_1_part6 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 768 128 = 559468363141626272974857995520 := by decide +kernel
private theorem receipt_1_16_2360_1_part7 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 896 128 = 513052945575750955863772988672 := by decide +kernel
private theorem receipt_1_16_2360_1_part8 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 1024 128 = 467757745594035775564419990784 := by decide +kernel
private theorem receipt_1_16_2360_1_part9 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 1152 128 = 423568655127410215223215097088 := by decide +kernel
private theorem receipt_1_16_2360_1_part10 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 1280 128 = 380471598538334333152349029632 := by decide +kernel
private theorem receipt_1_16_2360_1_part11 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 1408 128 = 338452532595647390363946026240 := by decide +kernel
private theorem receipt_1_16_2360_1_part12 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 1536 128 = 297497446449416478104222729472 := by decide +kernel
private theorem receipt_1_16_2360_1_part13 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 1664 128 = 257592361605785145387647075584 := by decide +kernel
private theorem receipt_1_16_2360_1_part14 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 1792 128 = 218723351448511741864967543460 := by decide +kernel
private theorem receipt_1_16_2360_1_part15 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 1920 128 = 180876543079668368447724525180 := by decide +kernel
private theorem receipt_1_16_2360_1_part16 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 2048 128 = 144038023692512830935658162064 := by decide +kernel
private theorem receipt_1_16_2360_1_part17 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 2176 128 = 108193899720912186394458876631 := by decide +kernel
private theorem receipt_1_16_2360_1_part18 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 2304 128 = 73330309936107576921380865954 := by decide +kernel
private theorem receipt_1_16_2360_1_part19 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 2432 128 = 39433425469351543443886987083 := by decide +kernel
private theorem receipt_1_16_2360_1_part20 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 2560 90 = 7945350879904697633633714181 := by decide +kernel
private theorem receipt_1_16_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 0 256 = 1671124352910274517649905551872 :=
  phaseBlock_append receipt_1_16_2360_1_part0 receipt_1_16_2360_1_part1 rfl rfl rfl
private theorem receipt_1_16_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 384 256 = 1361293934646756158654106307072 :=
  phaseBlock_append receipt_1_16_2360_1_part3 receipt_1_16_2360_1_part4 rfl rfl rfl
private theorem receipt_1_16_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 256 384 = 2117909441786942394151516671744 :=
  phaseBlock_append receipt_1_16_2360_1_part2 receipt_1_16_2360_1_join1 rfl rfl rfl
private theorem receipt_1_16_2360_1_join3 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 0 640 = 3789033794697216911801422223616 :=
  phaseBlock_append receipt_1_16_2360_1_join0 receipt_1_16_2360_1_join2 rfl rfl rfl
private theorem receipt_1_16_2360_1_join4 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 640 256 = 1166486501959040464357732649472 :=
  phaseBlock_append receipt_1_16_2360_1_part5 receipt_1_16_2360_1_part6 rfl rfl rfl
private theorem receipt_1_16_2360_1_join5 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 1024 256 = 891326400721445990787635087872 :=
  phaseBlock_append receipt_1_16_2360_1_part8 receipt_1_16_2360_1_part9 rfl rfl rfl
private theorem receipt_1_16_2360_1_join6 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 896 384 = 1404379346297196946651408076544 :=
  phaseBlock_append receipt_1_16_2360_1_part7 receipt_1_16_2360_1_join5 rfl rfl rfl
private theorem receipt_1_16_2360_1_join7 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 640 640 = 2570865848256237411009140726016 :=
  phaseBlock_append receipt_1_16_2360_1_join4 receipt_1_16_2360_1_join6 rfl rfl rfl
private theorem receipt_1_16_2360_1_join8 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 0 1280 = 6359899642953454322810562949632 :=
  phaseBlock_append receipt_1_16_2360_1_join3 receipt_1_16_2360_1_join7 rfl rfl rfl
private theorem receipt_1_16_2360_1_join9 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 1280 256 = 718924131133981723516295055872 :=
  phaseBlock_append receipt_1_16_2360_1_part10 receipt_1_16_2360_1_part11 rfl rfl rfl
private theorem receipt_1_16_2360_1_join10 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 1664 256 = 476315713054296887252614619044 :=
  phaseBlock_append receipt_1_16_2360_1_part13 receipt_1_16_2360_1_part14 rfl rfl rfl
private theorem receipt_1_16_2360_1_join11 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 1536 384 = 773813159503713365356837348516 :=
  phaseBlock_append receipt_1_16_2360_1_part12 receipt_1_16_2360_1_join10 rfl rfl rfl
private theorem receipt_1_16_2360_1_join12 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 1280 640 = 1492737290637695088873132404388 :=
  phaseBlock_append receipt_1_16_2360_1_join9 receipt_1_16_2360_1_join11 rfl rfl rfl
private theorem receipt_1_16_2360_1_join13 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 2048 256 = 252231923413425017330117038695 :=
  phaseBlock_append receipt_1_16_2360_1_part16 receipt_1_16_2360_1_part17 rfl rfl rfl
private theorem receipt_1_16_2360_1_join14 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 1920 384 = 433108466493093385777841563875 :=
  phaseBlock_append receipt_1_16_2360_1_part15 receipt_1_16_2360_1_join13 rfl rfl rfl
private theorem receipt_1_16_2360_1_join15 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 2432 218 = 47378776349256241077520701264 :=
  phaseBlock_append receipt_1_16_2360_1_part19 receipt_1_16_2360_1_part20 rfl rfl rfl
private theorem receipt_1_16_2360_1_join16 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 2304 346 = 120709086285363817998901567218 :=
  phaseBlock_append receipt_1_16_2360_1_part18 receipt_1_16_2360_1_join15 rfl rfl rfl
private theorem receipt_1_16_2360_1_join17 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 1920 730 = 553817552778457203776743131093 :=
  phaseBlock_append receipt_1_16_2360_1_join14 receipt_1_16_2360_1_join16 rfl rfl rfl
private theorem receipt_1_16_2360_1_join18 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 1280 1370 = 2046554843416152292649875535481 :=
  phaseBlock_append receipt_1_16_2360_1_join12 receipt_1_16_2360_1_join17 rfl rfl rfl
private theorem receipt_1_16_2360_1_join19 :
    phaseBlock (fastLayer (bank 1 16).shape 179808 2380 103 1 0 2 1) 0 2650 = 8406454486369606615460438485113 :=
  phaseBlock_append receipt_1_16_2360_1_join8 receipt_1_16_2360_1_join18 rfl rfl rfl

private theorem receipt_1_16_2360_1 : fastPhase (bank 1 16).shape 179808 2380 103 1 0 2 1 = 8406454486369606615460438485113 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_1_16_2360_1_join19

theorem receipt_1_16 : Checked (bank 1 16) 103 0 2 := by
  refine checked_from_values (bank 1 16) 103 0 2
    (P3_7_1.checked (bank 1 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_12604_2649)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_16_2359_0 receipt_1_16_2359_1 receipt_1_16_2360_0 receipt_1_16_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_16_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 0 128 = 463011248606653598266333239360 := by decide +kernel
private theorem receipt_2_16_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 128 128 = 433270187330760708606386698304 := by decide +kernel
private theorem receipt_2_16_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 256 128 = 404313330108928721441001789504 := by decide +kernel
private theorem receipt_2_16_2359_0_part3 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 384 128 = 376128214976423964142649194560 := by decide +kernel
private theorem receipt_2_16_2359_0_part4 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 512 128 = 348702476933598344118363494464 := by decide +kernel
private theorem receipt_2_16_2359_0_part5 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 640 128 = 322023847637795811317141764160 := by decide +kernel
private theorem receipt_2_16_2359_0_part6 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 768 128 = 296080155095258820737342167104 := by decide +kernel
private theorem receipt_2_16_2359_0_part7 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 896 128 = 270859323353034794934082549824 := by decide +kernel
private theorem receipt_2_16_2359_0_part8 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 1024 128 = 246349372190882586526639036480 := by decide +kernel
private theorem receipt_2_16_2359_0_part9 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 1152 128 = 222538416813178940705844623424 := by decide +kernel
private theorem receipt_2_16_2359_0_part10 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 1280 128 = 199414667540824957741487773760 := by decide +kernel
private theorem receipt_2_16_2359_0_part11 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 1408 128 = 176966429503152555489711011904 := by decide +kernel
private theorem receipt_2_16_2359_0_part12 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 1536 128 = 155182102329830931900409518144 := by decide +kernel
private theorem receipt_2_16_2359_0_part13 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 1664 128 = 134050179843514141020717377128 := by decide +kernel
private theorem receipt_2_16_2359_0_part14 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 1792 128 = 113559260295253260985920397042 := by decide +kernel
private theorem receipt_2_16_2359_0_part15 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 1920 128 = 93698045781265778584707500126 := by decide +kernel
private theorem receipt_2_16_2359_0_part16 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 2048 128 = 74455294214577168926875901430 := by decide +kernel
private theorem receipt_2_16_2359_0_part17 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 2176 128 = 55819850246168578808230279060 := by decide +kernel
private theorem receipt_2_16_2359_0_part18 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 2304 128 = 37780651461167952062695691208 := by decide +kernel
private theorem receipt_2_16_2359_0_part19 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 2432 128 = 20326728091711013039346272598 := by decide +kernel
private theorem receipt_2_16_2359_0_part20 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 2560 90 = 4151931145431840752090404074 := by decide +kernel
private theorem receipt_2_16_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 0 256 = 896281435937414306872719937664 :=
  phaseBlock_append receipt_2_16_2359_0_part0 receipt_2_16_2359_0_part1 rfl rfl rfl
private theorem receipt_2_16_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 384 256 = 724830691910022308261012689024 :=
  phaseBlock_append receipt_2_16_2359_0_part3 receipt_2_16_2359_0_part4 rfl rfl rfl
private theorem receipt_2_16_2359_0_join2 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 256 384 = 1129144022018951029702014478528 :=
  phaseBlock_append receipt_2_16_2359_0_part2 receipt_2_16_2359_0_join1 rfl rfl rfl
private theorem receipt_2_16_2359_0_join3 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 0 640 = 2025425457956365336574734416192 :=
  phaseBlock_append receipt_2_16_2359_0_join0 receipt_2_16_2359_0_join2 rfl rfl rfl
private theorem receipt_2_16_2359_0_join4 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 640 256 = 618104002733054632054483931264 :=
  phaseBlock_append receipt_2_16_2359_0_part5 receipt_2_16_2359_0_part6 rfl rfl rfl
private theorem receipt_2_16_2359_0_join5 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 1024 256 = 468887789004061527232483659904 :=
  phaseBlock_append receipt_2_16_2359_0_part8 receipt_2_16_2359_0_part9 rfl rfl rfl
private theorem receipt_2_16_2359_0_join6 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 896 384 = 739747112357096322166566209728 :=
  phaseBlock_append receipt_2_16_2359_0_part7 receipt_2_16_2359_0_join5 rfl rfl rfl
private theorem receipt_2_16_2359_0_join7 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 640 640 = 1357851115090150954221050140992 :=
  phaseBlock_append receipt_2_16_2359_0_join4 receipt_2_16_2359_0_join6 rfl rfl rfl
private theorem receipt_2_16_2359_0_join8 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 0 1280 = 3383276573046516290795784557184 :=
  phaseBlock_append receipt_2_16_2359_0_join3 receipt_2_16_2359_0_join7 rfl rfl rfl
private theorem receipt_2_16_2359_0_join9 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 1280 256 = 376381097043977513231198785664 :=
  phaseBlock_append receipt_2_16_2359_0_part10 receipt_2_16_2359_0_part11 rfl rfl rfl
private theorem receipt_2_16_2359_0_join10 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 1664 256 = 247609440138767402006637774170 :=
  phaseBlock_append receipt_2_16_2359_0_part13 receipt_2_16_2359_0_part14 rfl rfl rfl
private theorem receipt_2_16_2359_0_join11 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 1536 384 = 402791542468598333907047292314 :=
  phaseBlock_append receipt_2_16_2359_0_part12 receipt_2_16_2359_0_join10 rfl rfl rfl
private theorem receipt_2_16_2359_0_join12 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 1280 640 = 779172639512575847138246077978 :=
  phaseBlock_append receipt_2_16_2359_0_join9 receipt_2_16_2359_0_join11 rfl rfl rfl
private theorem receipt_2_16_2359_0_join13 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 2048 256 = 130275144460745747735106180490 :=
  phaseBlock_append receipt_2_16_2359_0_part16 receipt_2_16_2359_0_part17 rfl rfl rfl
private theorem receipt_2_16_2359_0_join14 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 1920 384 = 223973190242011526319813680616 :=
  phaseBlock_append receipt_2_16_2359_0_part15 receipt_2_16_2359_0_join13 rfl rfl rfl
private theorem receipt_2_16_2359_0_join15 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 2432 218 = 24478659237142853791436676672 :=
  phaseBlock_append receipt_2_16_2359_0_part19 receipt_2_16_2359_0_part20 rfl rfl rfl
private theorem receipt_2_16_2359_0_join16 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 2304 346 = 62259310698310805854132367880 :=
  phaseBlock_append receipt_2_16_2359_0_part18 receipt_2_16_2359_0_join15 rfl rfl rfl
private theorem receipt_2_16_2359_0_join17 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 1920 730 = 286232500940322332173946048496 :=
  phaseBlock_append receipt_2_16_2359_0_join14 receipt_2_16_2359_0_join16 rfl rfl rfl
private theorem receipt_2_16_2359_0_join18 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 1280 1370 = 1065405140452898179312192126474 :=
  phaseBlock_append receipt_2_16_2359_0_join12 receipt_2_16_2359_0_join17 rfl rfl rfl
private theorem receipt_2_16_2359_0_join19 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 0) 0 2650 = 4448681713499414470107976683658 :=
  phaseBlock_append receipt_2_16_2359_0_join8 receipt_2_16_2359_0_join18 rfl rfl rfl

private theorem receipt_2_16_2359_0 : fastPhase (bank 2 16).shape 179808 2379 103 1 0 7 0 = 4448681713499414470107976683658 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_2_16_2359_0_join19

private theorem receipt_2_16_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 0 128 = 462778820150719594991864293376 := by decide +kernel
private theorem receipt_2_16_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 128 128 = 433043760826390350174500628480 := by decide +kernel
private theorem receipt_2_16_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 256 128 = 404092810522884340310077188096 := by decide +kernel
private theorem receipt_2_16_2359_1_part3 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 384 128 = 375913508016321109586273904640 := by decide +kernel
private theorem receipt_2_16_2359_1_part4 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 512 128 = 348493489045546865652409214976 := by decide +kernel
private theorem receipt_2_16_2359_1_part5 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 640 128 = 321820486004040942126838654976 := by decide +kernel
private theorem receipt_2_16_2359_1_part6 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 768 128 = 295882327631822261104353454080 := by decide +kernel
private theorem receipt_2_16_2359_1_part7 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 896 128 = 270666938707355795663579129856 := by decide +kernel
private theorem receipt_2_16_2359_1_part8 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 1024 128 = 246162339739459032374374082560 := by decide +kernel
private theorem receipt_2_16_2359_1_part9 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 1152 128 = 222356646659208433805228189696 := by decide +kernel
private theorem receipt_2_16_2359_1_part10 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 1280 128 = 199238070511845901030661400576 := by decide +kernel
private theorem receipt_2_16_2359_1_part11 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 1408 128 = 176794917148685236138622330880 := by decide +kernel
private theorem receipt_2_16_2359_1_part12 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 1536 128 = 155015586919018604737886857216 := by decide +kernel
private theorem receipt_2_16_2359_1_part13 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 1664 128 = 133888574362763094133214941386 := by decide +kernel
private theorem receipt_2_16_2359_1_part14 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 1792 128 = 113402478431825062388164883931 := by decide +kernel
private theorem receipt_2_16_2359_1_part15 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 1920 128 = 93546001895543642259674696408 := by decide +kernel
private theorem receipt_2_16_2359_1_part16 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 2048 128 = 74307903371328626648781397062 := by decide +kernel
private theorem receipt_2_16_2359_1_part17 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 2176 128 = 55677028219113052360873445908 := by decide +kernel
private theorem receipt_2_16_2359_1_part18 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 2304 128 = 37642314730635285038249718590 := by decide +kernel
private theorem receipt_2_16_2359_1_part19 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 2432 128 = 20192793842250153046699695574 := by decide +kernel
private theorem receipt_2_16_2359_1_part20 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 2560 90 = 4060350304729612302759468162 := by decide +kernel
private theorem receipt_2_16_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 0 256 = 895822580977109945166364921856 :=
  phaseBlock_append receipt_2_16_2359_1_part0 receipt_2_16_2359_1_part1 rfl rfl rfl
private theorem receipt_2_16_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 384 256 = 724406997061867975238683119616 :=
  phaseBlock_append receipt_2_16_2359_1_part3 receipt_2_16_2359_1_part4 rfl rfl rfl
private theorem receipt_2_16_2359_1_join2 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 256 384 = 1128499807584752315548760307712 :=
  phaseBlock_append receipt_2_16_2359_1_part2 receipt_2_16_2359_1_join1 rfl rfl rfl
private theorem receipt_2_16_2359_1_join3 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 0 640 = 2024322388561862260715125229568 :=
  phaseBlock_append receipt_2_16_2359_1_join0 receipt_2_16_2359_1_join2 rfl rfl rfl
private theorem receipt_2_16_2359_1_join4 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 640 256 = 617702813635863203231192109056 :=
  phaseBlock_append receipt_2_16_2359_1_part5 receipt_2_16_2359_1_part6 rfl rfl rfl
private theorem receipt_2_16_2359_1_join5 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 1024 256 = 468518986398667466179602272256 :=
  phaseBlock_append receipt_2_16_2359_1_part8 receipt_2_16_2359_1_part9 rfl rfl rfl
private theorem receipt_2_16_2359_1_join6 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 896 384 = 739185925106023261843181402112 :=
  phaseBlock_append receipt_2_16_2359_1_part7 receipt_2_16_2359_1_join5 rfl rfl rfl
private theorem receipt_2_16_2359_1_join7 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 640 640 = 1356888738741886465074373511168 :=
  phaseBlock_append receipt_2_16_2359_1_join4 receipt_2_16_2359_1_join6 rfl rfl rfl
private theorem receipt_2_16_2359_1_join8 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 0 1280 = 3381211127303748725789498740736 :=
  phaseBlock_append receipt_2_16_2359_1_join3 receipt_2_16_2359_1_join7 rfl rfl rfl
private theorem receipt_2_16_2359_1_join9 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 1280 256 = 376032987660531137169283731456 :=
  phaseBlock_append receipt_2_16_2359_1_part10 receipt_2_16_2359_1_part11 rfl rfl rfl
private theorem receipt_2_16_2359_1_join10 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 1664 256 = 247291052794588156521379825317 :=
  phaseBlock_append receipt_2_16_2359_1_part13 receipt_2_16_2359_1_part14 rfl rfl rfl
private theorem receipt_2_16_2359_1_join11 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 1536 384 = 402306639713606761259266682533 :=
  phaseBlock_append receipt_2_16_2359_1_part12 receipt_2_16_2359_1_join10 rfl rfl rfl
private theorem receipt_2_16_2359_1_join12 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 1280 640 = 778339627374137898428550413989 :=
  phaseBlock_append receipt_2_16_2359_1_join9 receipt_2_16_2359_1_join11 rfl rfl rfl
private theorem receipt_2_16_2359_1_join13 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 2048 256 = 129984931590441679009654842970 :=
  phaseBlock_append receipt_2_16_2359_1_part16 receipt_2_16_2359_1_part17 rfl rfl rfl
private theorem receipt_2_16_2359_1_join14 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 1920 384 = 223530933485985321269329539378 :=
  phaseBlock_append receipt_2_16_2359_1_part15 receipt_2_16_2359_1_join13 rfl rfl rfl
private theorem receipt_2_16_2359_1_join15 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 2432 218 = 24253144146979765349459163736 :=
  phaseBlock_append receipt_2_16_2359_1_part19 receipt_2_16_2359_1_part20 rfl rfl rfl
private theorem receipt_2_16_2359_1_join16 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 2304 346 = 61895458877615050387708882326 :=
  phaseBlock_append receipt_2_16_2359_1_part18 receipt_2_16_2359_1_join15 rfl rfl rfl
private theorem receipt_2_16_2359_1_join17 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 1920 730 = 285426392363600371657038421704 :=
  phaseBlock_append receipt_2_16_2359_1_join14 receipt_2_16_2359_1_join16 rfl rfl rfl
private theorem receipt_2_16_2359_1_join18 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 1280 1370 = 1063766019737738270085588835693 :=
  phaseBlock_append receipt_2_16_2359_1_join12 receipt_2_16_2359_1_join17 rfl rfl rfl
private theorem receipt_2_16_2359_1_join19 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2379 103 1 0 7 1) 0 2650 = 4444977147041486995875087576429 :=
  phaseBlock_append receipt_2_16_2359_1_join8 receipt_2_16_2359_1_join18 rfl rfl rfl

private theorem receipt_2_16_2359_1 : fastPhase (bank 2 16).shape 179808 2379 103 1 0 7 1 = 4444977147041486995875087576429 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_2_16_2359_1_join19

private theorem receipt_2_16_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 0 128 = 463015420015841504257191663840 := by decide +kernel
private theorem receipt_2_16_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 128 128 = 433273986069293440769986201824 := by decide +kernel
private theorem receipt_2_16_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 256 128 = 404316775777068096614712391904 := by decide +kernel
private theorem receipt_2_16_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 384 128 = 376131326783554311430548515040 := by decide +kernel
private theorem receipt_2_16_2360_0_part4 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 512 128 = 348705273701506517298604021984 := by decide +kernel
private theorem receipt_2_16_2360_0_part5 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 640 128 = 322026347803940426035365923040 := by decide +kernel
private theorem receipt_2_16_2360_0_part6 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 768 128 = 296082376716028716486145177824 := by decide +kernel
private theorem receipt_2_16_2360_0_part7 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 896 128 = 270861284106996721818523085024 := by decide +kernel
private theorem receipt_2_16_2360_0_part8 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 1024 128 = 246351089382018116815797672160 := by decide +kernel
private theorem receipt_2_16_2360_0_part9 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 1152 128 = 222539907374110605170430085344 := by decide +kernel
private theorem receipt_2_16_2360_0_part10 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 1280 128 = 199415948036031606777490979040 := by decide +kernel
private theorem receipt_2_16_2360_0_part11 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 1408 128 = 176967516132173945028106905824 := by decide +kernel
private theorem receipt_2_16_2360_0_part12 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 1536 128 = 155183010930461534102906706144 := by decide +kernel
private theorem receipt_2_16_2360_0_part13 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 1664 128 = 134050925894245066265467898080 := by decide +kernel
private theorem receipt_2_16_2360_0_part14 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 1792 128 = 113559858516302745663936096716 := by decide +kernel
private theorem receipt_2_16_2360_0_part15 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 1920 128 = 93698510878285332891766479857 := by decide +kernel
private theorem receipt_2_16_2360_0_part16 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 2048 128 = 74455640846377699087454725540 := by decide +kernel
private theorem receipt_2_16_2360_0_part17 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 2176 128 = 55820092702655899308032078950 := by decide +kernel
private theorem receipt_2_16_2360_0_part18 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 2304 128 = 37780803668229599916343962591 := by decide +kernel
private theorem receipt_2_16_2360_0_part19 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 2432 128 = 20326803618609279047183750807 := by decide +kernel
private theorem receipt_2_16_2360_0_part20 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 2560 90 = 4151945477944801582776488577 := by decide +kernel
private theorem receipt_2_16_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 0 256 = 896289406085134945027177865664 :=
  phaseBlock_append receipt_2_16_2360_0_part0 receipt_2_16_2360_0_part1 rfl rfl rfl
private theorem receipt_2_16_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 384 256 = 724836600485060828729152537024 :=
  phaseBlock_append receipt_2_16_2360_0_part3 receipt_2_16_2360_0_part4 rfl rfl rfl
private theorem receipt_2_16_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 256 384 = 1129153376262128925343864928928 :=
  phaseBlock_append receipt_2_16_2360_0_part2 receipt_2_16_2360_0_join1 rfl rfl rfl
private theorem receipt_2_16_2360_0_join3 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 0 640 = 2025442782347263870371042794592 :=
  phaseBlock_append receipt_2_16_2360_0_join0 receipt_2_16_2360_0_join2 rfl rfl rfl
private theorem receipt_2_16_2360_0_join4 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 640 256 = 618108724519969142521511100864 :=
  phaseBlock_append receipt_2_16_2360_0_part5 receipt_2_16_2360_0_part6 rfl rfl rfl
private theorem receipt_2_16_2360_0_join5 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 1024 256 = 468890996756128721986227757504 :=
  phaseBlock_append receipt_2_16_2360_0_part8 receipt_2_16_2360_0_part9 rfl rfl rfl
private theorem receipt_2_16_2360_0_join6 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 896 384 = 739752280863125443804750842528 :=
  phaseBlock_append receipt_2_16_2360_0_part7 receipt_2_16_2360_0_join5 rfl rfl rfl
private theorem receipt_2_16_2360_0_join7 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 640 640 = 1357861005383094586326261943392 :=
  phaseBlock_append receipt_2_16_2360_0_join4 receipt_2_16_2360_0_join6 rfl rfl rfl
private theorem receipt_2_16_2360_0_join8 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 0 1280 = 3383303787730358456697304737984 :=
  phaseBlock_append receipt_2_16_2360_0_join3 receipt_2_16_2360_0_join7 rfl rfl rfl
private theorem receipt_2_16_2360_0_join9 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 1280 256 = 376383464168205551805597884864 :=
  phaseBlock_append receipt_2_16_2360_0_part10 receipt_2_16_2360_0_part11 rfl rfl rfl
private theorem receipt_2_16_2360_0_join10 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 1664 256 = 247610784410547811929403994796 :=
  phaseBlock_append receipt_2_16_2360_0_part13 receipt_2_16_2360_0_part14 rfl rfl rfl
private theorem receipt_2_16_2360_0_join11 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 1536 384 = 402793795341009346032310700940 :=
  phaseBlock_append receipt_2_16_2360_0_part12 receipt_2_16_2360_0_join10 rfl rfl rfl
private theorem receipt_2_16_2360_0_join12 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 1280 640 = 779177259509214897837908585804 :=
  phaseBlock_append receipt_2_16_2360_0_join9 receipt_2_16_2360_0_join11 rfl rfl rfl
private theorem receipt_2_16_2360_0_join13 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 2048 256 = 130275733549033598395486804490 :=
  phaseBlock_append receipt_2_16_2360_0_part16 receipt_2_16_2360_0_part17 rfl rfl rfl
private theorem receipt_2_16_2360_0_join14 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 1920 384 = 223974244427318931287253284347 :=
  phaseBlock_append receipt_2_16_2360_0_part15 receipt_2_16_2360_0_join13 rfl rfl rfl
private theorem receipt_2_16_2360_0_join15 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 2432 218 = 24478749096554080629960239384 :=
  phaseBlock_append receipt_2_16_2360_0_part19 receipt_2_16_2360_0_part20 rfl rfl rfl
private theorem receipt_2_16_2360_0_join16 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 2304 346 = 62259552764783680546304201975 :=
  phaseBlock_append receipt_2_16_2360_0_part18 receipt_2_16_2360_0_join15 rfl rfl rfl
private theorem receipt_2_16_2360_0_join17 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 1920 730 = 286233797192102611833557486322 :=
  phaseBlock_append receipt_2_16_2360_0_join14 receipt_2_16_2360_0_join16 rfl rfl rfl
private theorem receipt_2_16_2360_0_join18 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 1280 1370 = 1065411056701317509671466072126 :=
  phaseBlock_append receipt_2_16_2360_0_join12 receipt_2_16_2360_0_join17 rfl rfl rfl
private theorem receipt_2_16_2360_0_join19 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 0) 0 2650 = 4448714844431675966368770810110 :=
  phaseBlock_append receipt_2_16_2360_0_join8 receipt_2_16_2360_0_join18 rfl rfl rfl

private theorem receipt_2_16_2360_0 : fastPhase (bank 2 16).shape 179808 2380 103 1 0 7 0 = 4448714844431675966368770810110 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_2_16_2360_0_join19

private theorem receipt_2_16_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 0 128 = 462782989830461408679732385504 := by decide +kernel
private theorem receipt_2_16_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 128 128 = 433047557917327096496971941600 := by decide +kernel
private theorem receipt_2_16_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 256 128 = 404096254623347332547178657504 := by decide +kernel
private theorem receipt_2_16_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 384 128 = 375916618333782324127381219040 := by decide +kernel
private theorem receipt_2_16_2360_1_part4 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 512 128 = 348496284399898890425781245664 := by decide +kernel
private theorem receipt_2_16_2360_1_part5 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 640 128 = 321822984830866149815199680224 := by decide +kernel
private theorem receipt_2_16_2360_1_part6 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 768 128 = 295884547985651207146523178720 := by decide +kernel
private theorem receipt_2_16_2360_1_part7 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 896 128 = 270668898264914841042150500064 := by decide +kernel
private theorem receipt_2_16_2360_1_part8 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 1024 128 = 246164055802907191189438895840 := by decide +kernel
private theorem receipt_2_16_2360_1_part9 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 1152 128 = 222358136159363445634150500064 := by decide +kernel
private theorem receipt_2_16_2360_1_part10 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 1280 128 = 199239350011399528073898718944 := by decide +kernel
private theorem receipt_2_16_2360_1_part11 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 1408 128 = 176796002845407785151594620640 := by decide +kernel
private theorem receipt_2_16_2360_1_part12 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 1536 128 = 155016494648952673748893325024 := by decide +kernel
private theorem receipt_2_16_2360_1_part13 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 1664 128 = 133889319602666448279640393440 := by decide +kernel
private theorem receipt_2_16_2360_1_part14 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 1792 128 = 113403075900728170753711589413 := by decide +kernel
private theorem receipt_2_16_2360_1_part15 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 1920 128 = 93546466297685265305418159165 := by decide +kernel
private theorem receipt_2_16_2360_1_part16 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 2048 128 = 74308249363774998924883085478 := by decide +kernel
private theorem receipt_2_16_2360_1_part17 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 2176 128 = 55677270090046398351628351400 := by decide +kernel
private theorem receipt_2_16_2360_1_part18 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 2304 128 = 37642466404242049642447448293 := by decide +kernel
private theorem receipt_2_16_2360_1_part19 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 2432 128 = 20192868886096721336609350029 := by decide +kernel
private theorem receipt_2_16_2360_1_part20 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 2560 90 = 4060364326874143282548317859 := by decide +kernel
private theorem receipt_2_16_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 0 256 = 895830547747788505176704327104 :=
  phaseBlock_append receipt_2_16_2360_1_part0 receipt_2_16_2360_1_part1 rfl rfl rfl
private theorem receipt_2_16_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 384 256 = 724412902733681214553162464704 :=
  phaseBlock_append receipt_2_16_2360_1_part3 receipt_2_16_2360_1_part4 rfl rfl rfl
private theorem receipt_2_16_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 256 384 = 1128509157357028547100341122208 :=
  phaseBlock_append receipt_2_16_2360_1_part2 receipt_2_16_2360_1_join1 rfl rfl rfl
private theorem receipt_2_16_2360_1_join3 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 0 640 = 2024339705104817052277045449312 :=
  phaseBlock_append receipt_2_16_2360_1_join0 receipt_2_16_2360_1_join2 rfl rfl rfl
private theorem receipt_2_16_2360_1_join4 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 640 256 = 617707532816517356961722858944 :=
  phaseBlock_append receipt_2_16_2360_1_part5 receipt_2_16_2360_1_part6 rfl rfl rfl
private theorem receipt_2_16_2360_1_join5 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 1024 256 = 468522191962270636823589395904 :=
  phaseBlock_append receipt_2_16_2360_1_part8 receipt_2_16_2360_1_part9 rfl rfl rfl
private theorem receipt_2_16_2360_1_join6 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 896 384 = 739191090227185477865739895968 :=
  phaseBlock_append receipt_2_16_2360_1_part7 receipt_2_16_2360_1_join5 rfl rfl rfl
private theorem receipt_2_16_2360_1_join7 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 640 640 = 1356898623043702834827462754912 :=
  phaseBlock_append receipt_2_16_2360_1_join4 receipt_2_16_2360_1_join6 rfl rfl rfl
private theorem receipt_2_16_2360_1_join8 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 0 1280 = 3381238328148519887104508204224 :=
  phaseBlock_append receipt_2_16_2360_1_join3 receipt_2_16_2360_1_join7 rfl rfl rfl
private theorem receipt_2_16_2360_1_join9 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 1280 256 = 376035352856807313225493339584 :=
  phaseBlock_append receipt_2_16_2360_1_part10 receipt_2_16_2360_1_part11 rfl rfl rfl
private theorem receipt_2_16_2360_1_join10 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 1664 256 = 247292395503394619033351982853 :=
  phaseBlock_append receipt_2_16_2360_1_part13 receipt_2_16_2360_1_part14 rfl rfl rfl
private theorem receipt_2_16_2360_1_join11 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 1536 384 = 402308890152347292782245307877 :=
  phaseBlock_append receipt_2_16_2360_1_part12 receipt_2_16_2360_1_join10 rfl rfl rfl
private theorem receipt_2_16_2360_1_join12 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 1280 640 = 778344243009154606007738647461 :=
  phaseBlock_append receipt_2_16_2360_1_join9 receipt_2_16_2360_1_join11 rfl rfl rfl
private theorem receipt_2_16_2360_1_join13 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 2048 256 = 129985519453821397276511436878 :=
  phaseBlock_append receipt_2_16_2360_1_part16 receipt_2_16_2360_1_part17 rfl rfl rfl
private theorem receipt_2_16_2360_1_join14 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 1920 384 = 223531985751506662581929596043 :=
  phaseBlock_append receipt_2_16_2360_1_part15 receipt_2_16_2360_1_join13 rfl rfl rfl
private theorem receipt_2_16_2360_1_join15 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 2432 218 = 24253233212970864619157667888 :=
  phaseBlock_append receipt_2_16_2360_1_part19 receipt_2_16_2360_1_part20 rfl rfl rfl
private theorem receipt_2_16_2360_1_join16 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 2304 346 = 61895699617212914261605116181 :=
  phaseBlock_append receipt_2_16_2360_1_part18 receipt_2_16_2360_1_join15 rfl rfl rfl
private theorem receipt_2_16_2360_1_join17 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 1920 730 = 285427685368719576843534712224 :=
  phaseBlock_append receipt_2_16_2360_1_join14 receipt_2_16_2360_1_join16 rfl rfl rfl
private theorem receipt_2_16_2360_1_join18 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 1280 1370 = 1063771928377874182851273359685 :=
  phaseBlock_append receipt_2_16_2360_1_join12 receipt_2_16_2360_1_join17 rfl rfl rfl
private theorem receipt_2_16_2360_1_join19 :
    phaseBlock (fastLayer (bank 2 16).shape 179808 2380 103 1 0 7 1) 0 2650 = 4445010256526394069955781563909 :=
  phaseBlock_append receipt_2_16_2360_1_join8 receipt_2_16_2360_1_join18 rfl rfl rfl

private theorem receipt_2_16_2360_1 : fastPhase (bank 2 16).shape 179808 2380 103 1 0 7 1 = 4445010256526394069955781563909 :=
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
    (word : K1.I → K1_14.L) (lo : 2379 ≤ h) (hi : h ≤ 33599) (rect : Fin 4)
    (i : Fin 1) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group7_stage i)).shape
      (cutoff h rect (group7_stage i)), ¬ G∣Q :=
  (group7_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group7_avoids

end Lower6960.RescueSource
