import ProximityPrize.SubmissionLower.R6960RescueSourceSchedule
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

private theorem receipt_0_16_2339_0_part0 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 0 128 = 889892184036665413764002445024 := by decide +kernel
private theorem receipt_0_16_2339_0_part1 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 128 128 = 835046455698370272752799254240 := by decide +kernel
private theorem receipt_0_16_2339_0_part2 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 256 128 = 781408188064127796687808796384 := by decide +kernel
private theorem receipt_0_16_2339_0_part3 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 384 128 = 728963810147807436195757958880 := by decide +kernel
private theorem receipt_0_16_2339_0_part4 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 512 128 = 677699767130080054297443940064 := by decide +kernel
private theorem receipt_0_16_2339_0_part5 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 640 128 = 627602520352139099286621734624 := by decide +kernel
private theorem receipt_0_16_2339_0_part6 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 768 128 = 578658547309421777608891619040 := by decide +kernel
private theorem receipt_0_16_2339_0_part7 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 896 128 = 530854341645330226740586637024 := by decide +kernel
private theorem receipt_0_16_2339_0_part8 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 1024 128 = 484176413144952688067660084960 := by decide +kernel
private theorem receipt_0_16_2339_0_part9 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 1152 128 = 438611287728784679764572997344 := by decide +kernel
private theorem receipt_0_16_2339_0_part10 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 1280 128 = 394145507446450169673181632224 := by decide +kernel
private theorem receipt_0_16_2339_0_part11 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 1408 128 = 350765630470422748181624956640 := by decide +kernel
private theorem receipt_0_16_2339_0_part12 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 1536 128 = 308458231089746801103212132064 := by decide +kernel
private theorem receipt_0_16_2339_0_part13 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 1664 128 = 267209900869676278728617642124 := by decide +kernel
private theorem receipt_0_16_2339_0_part14 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 1792 128 = 227007284181644966151510939513 := by decide +kernel
private theorem receipt_0_16_2339_0_part15 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 1920 128 = 187837025522065696786287629433 := by decide +kernel
private theorem receipt_0_16_2339_0_part16 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 2048 128 = 149685722701126107120185299095 := by decide +kernel
private theorem receipt_0_16_2339_0_part17 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 2176 128 = 112539986285094507313086855005 := by decide +kernel
private theorem receipt_0_16_2339_0_part18 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 2304 128 = 76386442886311098725751021334 := by decide +kernel
private theorem receipt_0_16_2339_0_part19 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 2432 128 = 41211735272735454721688958102 := by decide +kernel
private theorem receipt_0_16_2339_0_part20 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 2560 90 = 8437394525989442473352394591 := by decide +kernel
private theorem receipt_0_16_2339_0_join0 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 0 256 = 1724938639735035686516801699264 :=
  phaseBlock_append receipt_0_16_2339_0_part0 receipt_0_16_2339_0_part1 rfl rfl rfl
private theorem receipt_0_16_2339_0_join1 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 384 256 = 1406663577277887490493201898944 :=
  phaseBlock_append receipt_0_16_2339_0_part3 receipt_0_16_2339_0_part4 rfl rfl rfl
private theorem receipt_0_16_2339_0_join2 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 256 384 = 2188071765342015287181010695328 :=
  phaseBlock_append receipt_0_16_2339_0_part2 receipt_0_16_2339_0_join1 rfl rfl rfl
private theorem receipt_0_16_2339_0_join3 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 0 640 = 3913010405077050973697812394592 :=
  phaseBlock_append receipt_0_16_2339_0_join0 receipt_0_16_2339_0_join2 rfl rfl rfl
private theorem receipt_0_16_2339_0_join4 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 640 256 = 1206261067661560876895513353664 :=
  phaseBlock_append receipt_0_16_2339_0_part5 receipt_0_16_2339_0_part6 rfl rfl rfl
private theorem receipt_0_16_2339_0_join5 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 1024 256 = 922787700873737367832233082304 :=
  phaseBlock_append receipt_0_16_2339_0_part8 receipt_0_16_2339_0_part9 rfl rfl rfl
private theorem receipt_0_16_2339_0_join6 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 896 384 = 1453642042519067594572819719328 :=
  phaseBlock_append receipt_0_16_2339_0_part7 receipt_0_16_2339_0_join5 rfl rfl rfl
private theorem receipt_0_16_2339_0_join7 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 640 640 = 2659903110180628471468333072992 :=
  phaseBlock_append receipt_0_16_2339_0_join4 receipt_0_16_2339_0_join6 rfl rfl rfl
private theorem receipt_0_16_2339_0_join8 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 0 1280 = 6572913515257679445166145467584 :=
  phaseBlock_append receipt_0_16_2339_0_join3 receipt_0_16_2339_0_join7 rfl rfl rfl
private theorem receipt_0_16_2339_0_join9 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 1280 256 = 744911137916872917854806588864 :=
  phaseBlock_append receipt_0_16_2339_0_part10 receipt_0_16_2339_0_part11 rfl rfl rfl
private theorem receipt_0_16_2339_0_join10 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 1664 256 = 494217185051321244880128581637 :=
  phaseBlock_append receipt_0_16_2339_0_part13 receipt_0_16_2339_0_part14 rfl rfl rfl
private theorem receipt_0_16_2339_0_join11 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 1536 384 = 802675416141068045983340713701 :=
  phaseBlock_append receipt_0_16_2339_0_part12 receipt_0_16_2339_0_join10 rfl rfl rfl
private theorem receipt_0_16_2339_0_join12 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 1280 640 = 1547586554057940963838147302565 :=
  phaseBlock_append receipt_0_16_2339_0_join9 receipt_0_16_2339_0_join11 rfl rfl rfl
private theorem receipt_0_16_2339_0_join13 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 2048 256 = 262225708986220614433272154100 :=
  phaseBlock_append receipt_0_16_2339_0_part16 receipt_0_16_2339_0_part17 rfl rfl rfl
private theorem receipt_0_16_2339_0_join14 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 1920 384 = 450062734508286311219559783533 :=
  phaseBlock_append receipt_0_16_2339_0_part15 receipt_0_16_2339_0_join13 rfl rfl rfl
private theorem receipt_0_16_2339_0_join15 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 2432 218 = 49649129798724897195041352693 :=
  phaseBlock_append receipt_0_16_2339_0_part19 receipt_0_16_2339_0_part20 rfl rfl rfl
private theorem receipt_0_16_2339_0_join16 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 2304 346 = 126035572685035995920792374027 :=
  phaseBlock_append receipt_0_16_2339_0_part18 receipt_0_16_2339_0_join15 rfl rfl rfl
private theorem receipt_0_16_2339_0_join17 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 1920 730 = 576098307193322307140352157560 :=
  phaseBlock_append receipt_0_16_2339_0_join14 receipt_0_16_2339_0_join16 rfl rfl rfl
private theorem receipt_0_16_2339_0_join18 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 1280 1370 = 2123684861251263270978499460125 :=
  phaseBlock_append receipt_0_16_2339_0_join12 receipt_0_16_2339_0_join17 rfl rfl rfl
private theorem receipt_0_16_2339_0_join19 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 0) 0 2650 = 8696598376508942716144644927709 :=
  phaseBlock_append receipt_0_16_2339_0_join8 receipt_0_16_2339_0_join18 rfl rfl rfl

private theorem receipt_0_16_2339_0 : fastPhase (bank 0 16).shape 179827 2339 103 1 0 1 0 = 8696598376508942716144644927709 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_0_16_2339_0_join19

private theorem receipt_0_16_2339_1_part0 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 0 128 = 889464647778520526314534596832 := by decide +kernel
private theorem receipt_0_16_2339_1_part1 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 128 128 = 834628092815575772002805334240 := by decide +kernel
private theorem receipt_0_16_2339_1_part2 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 256 128 = 780998895855276816854046445792 := by decide +kernel
private theorem receipt_0_16_2339_1_part3 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 384 128 = 728563486034737272393146261728 := by decide +kernel
private theorem receipt_0_16_2339_1_part4 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 512 128 = 677308308657824073611316244704 := by decide +kernel
private theorem receipt_0_16_2339_1_part5 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 640 128 = 627219825188878651844978475232 := by decide +kernel
private theorem receipt_0_16_2339_1_part6 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 768 128 = 578284513246438107654653137120 := by decide +kernel
private theorem receipt_0_16_2339_1_part7 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 896 128 = 530488866596956383703846002912 := by decide +kernel
private theorem receipt_0_16_2339_1_part8 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 1024 128 = 483819395148525437637935919328 := by decide +kernel
private theorem receipt_0_16_2339_1_part9 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 1152 128 = 438262624944596414963062292704 := by decide +kernel
private theorem receipt_0_16_2339_1_part10 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 1280 128 = 393805098157700821925012574432 := by decide +kernel
private theorem receipt_0_16_2339_1_part11 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 1408 128 = 350433373083171698388109746400 := by decide +kernel
private theorem receipt_0_16_2339_1_part12 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 1536 128 = 308134024132864790714099806432 := by decide +kernel
private theorem receipt_0_16_2339_1_part13 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 1664 128 = 266893642993448415371716942977 := by decide +kernel
private theorem receipt_0_16_2339_1_part14 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 1792 128 = 226698874109456131139970791937 := by decide +kernel
private theorem receipt_0_16_2339_1_part15 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 1920 128 = 187536362039091680824492636910 := by decide +kernel
private theorem receipt_0_16_2339_1_part16 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 2048 128 = 149392704711860290498901310516 := by decide +kernel
private theorem receipt_0_16_2339_1_part17 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 2176 128 = 112254512816727667237801700191 := by decide +kernel
private theorem receipt_0_16_2339_1_part18 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 2304 128 = 76108413088817288473174935654 := by decide +kernel
private theorem receipt_0_16_2339_1_part19 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 2432 128 = 40941048418826751432182541178 := by decide +kernel
private theorem receipt_0_16_2339_1_part20 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 2560 90 = 8251410173674475976503437011 := by decide +kernel
private theorem receipt_0_16_2339_1_join0 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 0 256 = 1724092740594096298317339931072 :=
  phaseBlock_append receipt_0_16_2339_1_part0 receipt_0_16_2339_1_part1 rfl rfl rfl
private theorem receipt_0_16_2339_1_join1 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 384 256 = 1405871794692561346004462506432 :=
  phaseBlock_append receipt_0_16_2339_1_part3 receipt_0_16_2339_1_part4 rfl rfl rfl
private theorem receipt_0_16_2339_1_join2 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 256 384 = 2186870690547838162858508952224 :=
  phaseBlock_append receipt_0_16_2339_1_part2 receipt_0_16_2339_1_join1 rfl rfl rfl
private theorem receipt_0_16_2339_1_join3 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 0 640 = 3910963431141934461175848883296 :=
  phaseBlock_append receipt_0_16_2339_1_join0 receipt_0_16_2339_1_join2 rfl rfl rfl
private theorem receipt_0_16_2339_1_join4 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 640 256 = 1205504338435316759499631612352 :=
  phaseBlock_append receipt_0_16_2339_1_part5 receipt_0_16_2339_1_part6 rfl rfl rfl
private theorem receipt_0_16_2339_1_join5 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 1024 256 = 922082020093121852600998212032 :=
  phaseBlock_append receipt_0_16_2339_1_part8 receipt_0_16_2339_1_part9 rfl rfl rfl
private theorem receipt_0_16_2339_1_join6 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 896 384 = 1452570886690078236304844214944 :=
  phaseBlock_append receipt_0_16_2339_1_part7 receipt_0_16_2339_1_join5 rfl rfl rfl
private theorem receipt_0_16_2339_1_join7 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 640 640 = 2658075225125394995804475827296 :=
  phaseBlock_append receipt_0_16_2339_1_join4 receipt_0_16_2339_1_join6 rfl rfl rfl
private theorem receipt_0_16_2339_1_join8 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 0 1280 = 6569038656267329456980324710592 :=
  phaseBlock_append receipt_0_16_2339_1_join3 receipt_0_16_2339_1_join7 rfl rfl rfl
private theorem receipt_0_16_2339_1_join9 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 1280 256 = 744238471240872520313122320832 :=
  phaseBlock_append receipt_0_16_2339_1_part10 receipt_0_16_2339_1_part11 rfl rfl rfl
private theorem receipt_0_16_2339_1_join10 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 1664 256 = 493592517102904546511687734914 :=
  phaseBlock_append receipt_0_16_2339_1_part13 receipt_0_16_2339_1_part14 rfl rfl rfl
private theorem receipt_0_16_2339_1_join11 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 1536 384 = 801726541235769337225787541346 :=
  phaseBlock_append receipt_0_16_2339_1_part12 receipt_0_16_2339_1_join10 rfl rfl rfl
private theorem receipt_0_16_2339_1_join12 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 1280 640 = 1545965012476641857538909862178 :=
  phaseBlock_append receipt_0_16_2339_1_join9 receipt_0_16_2339_1_join11 rfl rfl rfl
private theorem receipt_0_16_2339_1_join13 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 2048 256 = 261647217528587957736703010707 :=
  phaseBlock_append receipt_0_16_2339_1_part16 receipt_0_16_2339_1_part17 rfl rfl rfl
private theorem receipt_0_16_2339_1_join14 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 1920 384 = 449183579567679638561195647617 :=
  phaseBlock_append receipt_0_16_2339_1_part15 receipt_0_16_2339_1_join13 rfl rfl rfl
private theorem receipt_0_16_2339_1_join15 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 2432 218 = 49192458592501227408685978189 :=
  phaseBlock_append receipt_0_16_2339_1_part19 receipt_0_16_2339_1_part20 rfl rfl rfl
private theorem receipt_0_16_2339_1_join16 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 2304 346 = 125300871681318515881860913843 :=
  phaseBlock_append receipt_0_16_2339_1_part18 receipt_0_16_2339_1_join15 rfl rfl rfl
private theorem receipt_0_16_2339_1_join17 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 1920 730 = 574484451248998154443056561460 :=
  phaseBlock_append receipt_0_16_2339_1_join14 receipt_0_16_2339_1_join16 rfl rfl rfl
private theorem receipt_0_16_2339_1_join18 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 1280 1370 = 2120449463725640011981966423638 :=
  phaseBlock_append receipt_0_16_2339_1_join12 receipt_0_16_2339_1_join17 rfl rfl rfl
private theorem receipt_0_16_2339_1_join19 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2339 103 1 0 1 1) 0 2650 = 8689488119992969468962291134230 :=
  phaseBlock_append receipt_0_16_2339_1_join8 receipt_0_16_2339_1_join18 rfl rfl rfl

private theorem receipt_0_16_2339_1 : fastPhase (bank 0 16).shape 179827 2339 103 1 0 1 1 = 8689488119992969468962291134230 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_0_16_2339_1_join19

private theorem receipt_0_16_2340_0_part0 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 0 128 = 889900202306686231911232414464 := by decide +kernel
private theorem receipt_0_16_2340_0_part1 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 128 128 = 835053777842068440929382286080 := by decide +kernel
private theorem receipt_0_16_2340_0_part2 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 256 128 = 781414848079973666081564779264 := by decide +kernel
private theorem receipt_0_16_2340_0_part3 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 384 128 = 728969841566321734256526754560 := by decide +kernel
private theorem receipt_0_16_2340_0_part4 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 512 128 = 677705203014397817550822712064 := by decide +kernel
private theorem receipt_0_16_2340_0_part5 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 640 128 = 627607393298573386245376721664 := by decide +kernel
private theorem receipt_0_16_2340_0_part6 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 768 128 = 578662889448027161782044353280 := by decide +kernel
private theorem receipt_0_16_2340_0_part7 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 896 128 = 530858184640466069740174607104 := by decide +kernel
private theorem receipt_0_16_2340_0_part8 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 1024 128 = 484179788195846192813171843840 := by decide +kernel
private theorem receipt_0_16_2340_0_part9 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 1152 128 = 438614225570093723785057714944 := by decide +kernel
private theorem receipt_0_16_2340_0_part10 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 1280 128 = 394148038348825918507033092864 := by decide +kernel
private theorem receipt_0_16_2340_0_part11 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 1408 128 = 350767784241072048874040001280 := by decide +kernel
private theorem receipt_0_16_2340_0_part12 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 1536 128 = 308460037072994355801323545344 := by decide +kernel
private theorem receipt_0_16_2340_0_part13 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 1664 128 = 267211387820203088652946925206 := by decide +kernel
private theorem receipt_0_16_2340_0_part14 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 1792 128 = 227008479585726239043349674365 := by decide +kernel
private theorem receipt_0_16_2340_0_part15 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 1920 128 = 187837957534047358577919398844 := by decide +kernel
private theorem receipt_0_16_2340_0_part16 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 2048 128 = 149686419288994247017656225891 := by decide +kernel
private theorem receipt_0_16_2340_0_part17 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 2176 128 = 112540474906837505903493212932 := by decide +kernel
private theorem receipt_0_16_2340_0_part18 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 2304 128 = 76386750493420377372893874237 := by decide +kernel
private theorem receipt_0_16_2340_0_part19 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 2432 128 = 41211888334338465164468776724 := by decide +kernel
private theorem receipt_0_16_2340_0_part20 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 2560 90 = 8437423639395326382652717394 := by decide +kernel
private theorem receipt_0_16_2340_0_join0 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 0 256 = 1724953980148754672840614700544 :=
  phaseBlock_append receipt_0_16_2340_0_part0 receipt_0_16_2340_0_part1 rfl rfl rfl
private theorem receipt_0_16_2340_0_join1 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 384 256 = 1406675044580719551807349466624 :=
  phaseBlock_append receipt_0_16_2340_0_part3 receipt_0_16_2340_0_part4 rfl rfl rfl
private theorem receipt_0_16_2340_0_join2 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 256 384 = 2188089892660693217888914245888 :=
  phaseBlock_append receipt_0_16_2340_0_part2 receipt_0_16_2340_0_join1 rfl rfl rfl
private theorem receipt_0_16_2340_0_join3 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 0 640 = 3913043872809447890729528946432 :=
  phaseBlock_append receipt_0_16_2340_0_join0 receipt_0_16_2340_0_join2 rfl rfl rfl
private theorem receipt_0_16_2340_0_join4 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 640 256 = 1206270282746600548027421074944 :=
  phaseBlock_append receipt_0_16_2340_0_part5 receipt_0_16_2340_0_part6 rfl rfl rfl
private theorem receipt_0_16_2340_0_join5 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 1024 256 = 922794013765939916598229558784 :=
  phaseBlock_append receipt_0_16_2340_0_part8 receipt_0_16_2340_0_part9 rfl rfl rfl
private theorem receipt_0_16_2340_0_join6 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 896 384 = 1453652198406405986338404165888 :=
  phaseBlock_append receipt_0_16_2340_0_part7 receipt_0_16_2340_0_join5 rfl rfl rfl
private theorem receipt_0_16_2340_0_join7 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 640 640 = 2659922481153006534365825240832 :=
  phaseBlock_append receipt_0_16_2340_0_join4 receipt_0_16_2340_0_join6 rfl rfl rfl
private theorem receipt_0_16_2340_0_join8 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 0 1280 = 6572966353962454425095354187264 :=
  phaseBlock_append receipt_0_16_2340_0_join3 receipt_0_16_2340_0_join7 rfl rfl rfl
private theorem receipt_0_16_2340_0_join9 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 1280 256 = 744915822589897967381073094144 :=
  phaseBlock_append receipt_0_16_2340_0_part10 receipt_0_16_2340_0_part11 rfl rfl rfl
private theorem receipt_0_16_2340_0_join10 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 1664 256 = 494219867405929327696296599571 :=
  phaseBlock_append receipt_0_16_2340_0_part13 receipt_0_16_2340_0_part14 rfl rfl rfl
private theorem receipt_0_16_2340_0_join11 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 1536 384 = 802679904478923683497620144915 :=
  phaseBlock_append receipt_0_16_2340_0_part12 receipt_0_16_2340_0_join10 rfl rfl rfl
private theorem receipt_0_16_2340_0_join12 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 1280 640 = 1547595727068821650878693239059 :=
  phaseBlock_append receipt_0_16_2340_0_join9 receipt_0_16_2340_0_join11 rfl rfl rfl
private theorem receipt_0_16_2340_0_join13 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 2048 256 = 262226894195831752921149438823 :=
  phaseBlock_append receipt_0_16_2340_0_part16 receipt_0_16_2340_0_part17 rfl rfl rfl
private theorem receipt_0_16_2340_0_join14 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 1920 384 = 450064851729879111499068837667 :=
  phaseBlock_append receipt_0_16_2340_0_part15 receipt_0_16_2340_0_join13 rfl rfl rfl
private theorem receipt_0_16_2340_0_join15 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 2432 218 = 49649311973733791547121494118 :=
  phaseBlock_append receipt_0_16_2340_0_part19 receipt_0_16_2340_0_part20 rfl rfl rfl
private theorem receipt_0_16_2340_0_join16 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 2304 346 = 126036062467154168920015368355 :=
  phaseBlock_append receipt_0_16_2340_0_part18 receipt_0_16_2340_0_join15 rfl rfl rfl
private theorem receipt_0_16_2340_0_join17 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 1920 730 = 576100914197033280419084206022 :=
  phaseBlock_append receipt_0_16_2340_0_join14 receipt_0_16_2340_0_join16 rfl rfl rfl
private theorem receipt_0_16_2340_0_join18 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 1280 1370 = 2123696641265854931297777445081 :=
  phaseBlock_append receipt_0_16_2340_0_join12 receipt_0_16_2340_0_join17 rfl rfl rfl
private theorem receipt_0_16_2340_0_join19 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 0) 0 2650 = 8696662995228309356393131632345 :=
  phaseBlock_append receipt_0_16_2340_0_join8 receipt_0_16_2340_0_join18 rfl rfl rfl

private theorem receipt_0_16_2340_0 : fastPhase (bank 0 16).shape 179827 2340 103 1 0 1 0 = 8696662995228309356393131632345 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_0_16_2340_0_join19

private theorem receipt_0_16_2340_1_part0 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 0 128 = 889472662897237459723022028864 := by decide +kernel
private theorem receipt_0_16_2340_1_part1 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 128 128 = 834635411941772495992495886400 := by decide +kernel
private theorem receipt_0_16_2340_1_part2 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 256 128 = 781005552985212667164942520384 := by decide +kernel
private theorem receipt_0_16_2340_1_part3 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 384 128 = 728569514696725049387392061504 := by decide +kernel
private theorem receipt_0_16_2340_1_part4 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 512 128 = 677313741912793973781265043520 := by decide +kernel
private theorem receipt_0_16_2340_1_part5 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 640 128 = 627224695630941979418934333504 := by decide +kernel
private theorem receipt_0_16_2340_1_part6 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 768 128 = 578288853003450766300287062080 := by decide +kernel
private theorem receipt_0_16_2340_1_part7 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 896 128 = 530492707331082148329286553664 := by decide +kernel
private theorem receipt_0_16_2340_1_part8 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 1024 128 = 483822768056799006290534256704 := by decide +kernel
private theorem receipt_0_16_2340_1_part9 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 1152 128 = 438265560759486240825831673920 := by decide +kernel
private theorem receipt_0_16_2340_1_part10 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 1280 128 = 393807627147671725410742292544 := by decide +kernel
private theorem receipt_0_16_2340_1_part11 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 1408 128 = 350435525053247259331153514560 := by decide +kernel
private theorem receipt_0_16_2340_1_part12 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 1536 128 = 308135828425189520659838586944 := by decide +kernel
private theorem receipt_0_16_2340_1_part13 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 1664 128 = 266895128360672604803448579594 := by decide +kernel
private theorem receipt_0_16_2340_1_part14 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 1792 128 = 226700068036910192733751025634 := by decide +kernel
private theorem receipt_0_16_2340_1_part15 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 1920 128 = 187537292679165516869140244664 := by decide +kernel
private theorem receipt_0_16_2340_1_part16 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 2048 128 = 149393400030255885784249428064 := by decide +kernel
private theorem receipt_0_16_2340_1_part17 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 2176 128 = 112255000269162072057574467644 := by decide +kernel
private theorem receipt_0_16_2340_1_part18 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 2304 128 = 76108719624540839831530778223 := by decide +kernel
private theorem receipt_0_16_2340_1_part19 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 2432 128 = 40941200504687553396449292935 := by decide +kernel
private theorem receipt_0_16_2340_1_part20 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 2560 90 = 8251438657064799482859182697 := by decide +kernel
private theorem receipt_0_16_2340_1_join0 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 0 256 = 1724108074839009955715517915264 :=
  phaseBlock_append receipt_0_16_2340_1_part0 receipt_0_16_2340_1_part1 rfl rfl rfl
private theorem receipt_0_16_2340_1_join1 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 384 256 = 1405883256609519023168657105024 :=
  phaseBlock_append receipt_0_16_2340_1_part3 receipt_0_16_2340_1_part4 rfl rfl rfl
private theorem receipt_0_16_2340_1_join2 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 256 384 = 2186888809594731690333599625408 :=
  phaseBlock_append receipt_0_16_2340_1_part2 receipt_0_16_2340_1_join1 rfl rfl rfl
private theorem receipt_0_16_2340_1_join3 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 0 640 = 3910996884433741646049117540672 :=
  phaseBlock_append receipt_0_16_2340_1_join0 receipt_0_16_2340_1_join2 rfl rfl rfl
private theorem receipt_0_16_2340_1_join4 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 640 256 = 1205513548634392745719221395584 :=
  phaseBlock_append receipt_0_16_2340_1_part5 receipt_0_16_2340_1_part6 rfl rfl rfl
private theorem receipt_0_16_2340_1_join5 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 1024 256 = 922088328816285247116365930624 :=
  phaseBlock_append receipt_0_16_2340_1_part8 receipt_0_16_2340_1_part9 rfl rfl rfl
private theorem receipt_0_16_2340_1_join6 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 896 384 = 1452581036147367395445652484288 :=
  phaseBlock_append receipt_0_16_2340_1_part7 receipt_0_16_2340_1_join5 rfl rfl rfl
private theorem receipt_0_16_2340_1_join7 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 640 640 = 2658094584781760141164873879872 :=
  phaseBlock_append receipt_0_16_2340_1_join4 receipt_0_16_2340_1_join6 rfl rfl rfl
private theorem receipt_0_16_2340_1_join8 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 0 1280 = 6569091469215501787213991420544 :=
  phaseBlock_append receipt_0_16_2340_1_join3 receipt_0_16_2340_1_join7 rfl rfl rfl
private theorem receipt_0_16_2340_1_join9 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 1280 256 = 744243152200918984741895807104 :=
  phaseBlock_append receipt_0_16_2340_1_part10 receipt_0_16_2340_1_part11 rfl rfl rfl
private theorem receipt_0_16_2340_1_join10 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 1664 256 = 493595196397582797537199605228 :=
  phaseBlock_append receipt_0_16_2340_1_part13 receipt_0_16_2340_1_part14 rfl rfl rfl
private theorem receipt_0_16_2340_1_join11 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 1536 384 = 801731024822772318197038192172 :=
  phaseBlock_append receipt_0_16_2340_1_part12 receipt_0_16_2340_1_join10 rfl rfl rfl
private theorem receipt_0_16_2340_1_join12 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 1280 640 = 1545974177023691302938933999276 :=
  phaseBlock_append receipt_0_16_2340_1_join9 receipt_0_16_2340_1_join11 rfl rfl rfl
private theorem receipt_0_16_2340_1_join13 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 2048 256 = 261648400299417957841823895708 :=
  phaseBlock_append receipt_0_16_2340_1_part16 receipt_0_16_2340_1_part17 rfl rfl rfl
private theorem receipt_0_16_2340_1_join14 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 1920 384 = 449185692978583474710964140372 :=
  phaseBlock_append receipt_0_16_2340_1_part15 receipt_0_16_2340_1_join13 rfl rfl rfl
private theorem receipt_0_16_2340_1_join15 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 2432 218 = 49192639161752352879308475632 :=
  phaseBlock_append receipt_0_16_2340_1_part19 receipt_0_16_2340_1_part20 rfl rfl rfl
private theorem receipt_0_16_2340_1_join16 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 2304 346 = 125301358786293192710839253855 :=
  phaseBlock_append receipt_0_16_2340_1_part18 receipt_0_16_2340_1_join15 rfl rfl rfl
private theorem receipt_0_16_2340_1_join17 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 1920 730 = 574487051764876667421803394227 :=
  phaseBlock_append receipt_0_16_2340_1_join14 receipt_0_16_2340_1_join16 rfl rfl rfl
private theorem receipt_0_16_2340_1_join18 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 1280 1370 = 2120461228788567970360737393503 :=
  phaseBlock_append receipt_0_16_2340_1_join12 receipt_0_16_2340_1_join17 rfl rfl rfl
private theorem receipt_0_16_2340_1_join19 :
    phaseBlock (fastLayer (bank 0 16).shape 179827 2340 103 1 0 1 1) 0 2650 = 8689552698004069757574728814047 :=
  phaseBlock_append receipt_0_16_2340_1_join8 receipt_0_16_2340_1_join18 rfl rfl rfl

private theorem receipt_0_16_2340_1 : fastPhase (bank 0 16).shape 179827 2340 103 1 0 1 1 = 8689552698004069757574728814047 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_0_16_2340_1_join19

theorem receipt_0_16 : Checked (bank 0 16) 103 0 1 := by
  refine checked_from_values (bank 0 16) 103 0 1
    (P3_7_1.checked (bank 0 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_12604_2649)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_16_2339_0 receipt_0_16_2339_1 receipt_0_16_2340_0 receipt_0_16_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_16_2339_0_part0 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 0 128 = 801198059903775462461763887904 := by decide +kernel
private theorem receipt_1_16_2339_0_part1 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 128 128 = 751554323605366175989638501152 := by decide +kernel
private theorem receipt_1_16_2339_0_part2 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 256 128 = 703031639205605935282118591264 := by decide +kernel
private theorem receipt_1_16_2339_0_part3 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 384 128 = 655616661115083476766966280992 := by decide +kernel
private theorem receipt_1_16_2339_0_part4 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 512 128 = 609296075151959179198863631136 := by decide +kernel
private theorem receipt_1_16_2339_0_part5 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 640 128 = 564056598516849755174962582304 := by decide +kernel
private theorem receipt_1_16_2339_0_part6 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 768 128 = 519884979767712942650434896672 := by decide +kernel
private theorem receipt_1_16_2339_0_part7 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 896 128 = 476767998794732196454022099744 := by decide +kernel
private theorem receipt_1_16_2339_0_part8 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 1024 128 = 434692466795201379803585422112 := by decide +kernel
private theorem receipt_1_16_2339_0_part9 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 1152 128 = 393645226248409455821655741216 := by decide +kernel
private theorem receipt_1_16_2339_0_part10 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 1280 128 = 353613150890525179050983523104 := by decide +kernel
private theorem receipt_1_16_2339_0_part11 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 1408 128 = 314583145689481786970088764192 := by decide +kernel
private theorem receipt_1_16_2339_0_part12 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 1536 128 = 276542146819861691508810933024 := by decide +kernel
private theorem receipt_1_16_2339_0_part13 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 1664 128 = 239477122682539201633080482928 := by decide +kernel
private theorem receipt_1_16_2339_0_part14 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 1792 128 = 203375105713070297484753114690 := by decide +kernel
private theorem receipt_1_16_2339_0_part15 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 1920 128 = 168223145129549104187278357041 := by decide +kernel
private theorem receipt_1_16_2339_0_part16 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 2048 128 = 134008265024156220038462547495 := by decide +kernel
private theorem receipt_1_16_2339_0_part17 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 2176 128 = 100717517642289334721897430251 := by decide +kernel
private theorem receipt_1_16_2339_0_part18 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 2304 128 = 68337986312066884425089614540 := by decide +kernel
private theorem receipt_1_16_2339_0_part19 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 2432 128 = 36856785522879534088541676576 := by decide +kernel
private theorem receipt_1_16_2339_0_part20 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 2560 90 = 7543635548468045546129524215 := by decide +kernel
private theorem receipt_1_16_2339_0_join0 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 0 256 = 1552752383509141638451402389056 :=
  phaseBlock_append receipt_1_16_2339_0_part0 receipt_1_16_2339_0_part1 rfl rfl rfl
private theorem receipt_1_16_2339_0_join1 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 384 256 = 1264912736267042655965829912128 :=
  phaseBlock_append receipt_1_16_2339_0_part3 receipt_1_16_2339_0_part4 rfl rfl rfl
private theorem receipt_1_16_2339_0_join2 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 256 384 = 1967944375472648591247948503392 :=
  phaseBlock_append receipt_1_16_2339_0_part2 receipt_1_16_2339_0_join1 rfl rfl rfl
private theorem receipt_1_16_2339_0_join3 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 0 640 = 3520696758981790229699350892448 :=
  phaseBlock_append receipt_1_16_2339_0_join0 receipt_1_16_2339_0_join2 rfl rfl rfl
private theorem receipt_1_16_2339_0_join4 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 640 256 = 1083941578284562697825397478976 :=
  phaseBlock_append receipt_1_16_2339_0_part5 receipt_1_16_2339_0_part6 rfl rfl rfl
private theorem receipt_1_16_2339_0_join5 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 1024 256 = 828337693043610835625241163328 :=
  phaseBlock_append receipt_1_16_2339_0_part8 receipt_1_16_2339_0_part9 rfl rfl rfl
private theorem receipt_1_16_2339_0_join6 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 896 384 = 1305105691838343032079263263072 :=
  phaseBlock_append receipt_1_16_2339_0_part7 receipt_1_16_2339_0_join5 rfl rfl rfl
private theorem receipt_1_16_2339_0_join7 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 640 640 = 2389047270122905729904660742048 :=
  phaseBlock_append receipt_1_16_2339_0_join4 receipt_1_16_2339_0_join6 rfl rfl rfl
private theorem receipt_1_16_2339_0_join8 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 0 1280 = 5909744029104695959604011634496 :=
  phaseBlock_append receipt_1_16_2339_0_join3 receipt_1_16_2339_0_join7 rfl rfl rfl
private theorem receipt_1_16_2339_0_join9 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 1280 256 = 668196296580006966021072287296 :=
  phaseBlock_append receipt_1_16_2339_0_part10 receipt_1_16_2339_0_part11 rfl rfl rfl
private theorem receipt_1_16_2339_0_join10 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 1664 256 = 442852228395609499117833597618 :=
  phaseBlock_append receipt_1_16_2339_0_part13 receipt_1_16_2339_0_part14 rfl rfl rfl
private theorem receipt_1_16_2339_0_join11 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 1536 384 = 719394375215471190626644530642 :=
  phaseBlock_append receipt_1_16_2339_0_part12 receipt_1_16_2339_0_join10 rfl rfl rfl
private theorem receipt_1_16_2339_0_join12 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 1280 640 = 1387590671795478156647716817938 :=
  phaseBlock_append receipt_1_16_2339_0_join9 receipt_1_16_2339_0_join11 rfl rfl rfl
private theorem receipt_1_16_2339_0_join13 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 2048 256 = 234725782666445554760359977746 :=
  phaseBlock_append receipt_1_16_2339_0_part16 receipt_1_16_2339_0_part17 rfl rfl rfl
private theorem receipt_1_16_2339_0_join14 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 1920 384 = 402948927795994658947638334787 :=
  phaseBlock_append receipt_1_16_2339_0_part15 receipt_1_16_2339_0_join13 rfl rfl rfl
private theorem receipt_1_16_2339_0_join15 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 2432 218 = 44400421071347579634671200791 :=
  phaseBlock_append receipt_1_16_2339_0_part19 receipt_1_16_2339_0_part20 rfl rfl rfl
private theorem receipt_1_16_2339_0_join16 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 2304 346 = 112738407383414464059760815331 :=
  phaseBlock_append receipt_1_16_2339_0_part18 receipt_1_16_2339_0_join15 rfl rfl rfl
private theorem receipt_1_16_2339_0_join17 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 1920 730 = 515687335179409123007399150118 :=
  phaseBlock_append receipt_1_16_2339_0_join14 receipt_1_16_2339_0_join16 rfl rfl rfl
private theorem receipt_1_16_2339_0_join18 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 1280 1370 = 1903278006974887279655115968056 :=
  phaseBlock_append receipt_1_16_2339_0_join12 receipt_1_16_2339_0_join17 rfl rfl rfl
private theorem receipt_1_16_2339_0_join19 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 0) 0 2650 = 7813022036079583239259127602552 :=
  phaseBlock_append receipt_1_16_2339_0_join8 receipt_1_16_2339_0_join18 rfl rfl rfl

private theorem receipt_1_16_2339_0 : fastPhase (bank 1 16).shape 179827 2339 103 1 0 2 0 = 7813022036079583239259127602552 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_1_16_2339_0_join19

private theorem receipt_1_16_2339_1_part0 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 0 128 = 800810935443884384645602540768 := by decide +kernel
private theorem receipt_1_16_2339_1_part1 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 128 128 = 751175726076596660816631172320 := by decide +kernel
private theorem receipt_1_16_2339_1_part2 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 256 128 = 702661467466588708417308007648 := by decide +kernel
private theorem receipt_1_16_2339_1_part3 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 384 128 = 655254814263970742634353798368 := by decide +kernel
private theorem receipt_1_16_2339_1_part4 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 512 128 = 608942452526232265270420520160 := by decide +kernel
private theorem receipt_1_16_2339_1_part5 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 640 128 = 563711099693126756259641314528 := by decide +kernel
private theorem receipt_1_16_2339_1_part6 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 768 128 = 519547504561556365183180430560 := by decide +kernel
private theorem receipt_1_16_2339_1_part7 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 896 128 = 476438447260456602784783166688 := by decide +kernel
private theorem receipt_1_16_2339_1_part8 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 1024 128 = 434370739225681032486325812448 := by decide +kernel
private theorem receipt_1_16_2339_1_part9 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 1152 128 = 393331223174885961903365590240 := by decide +kernel
private theorem receipt_1_16_2339_1_part10 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 1280 128 = 353306773082415134360690597088 := by decide +kernel
private theorem receipt_1_16_2339_1_part11 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 1408 128 = 314284294154184420407869746400 := by decide +kernel
private theorem receipt_1_16_2339_1_part12 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 1536 128 = 276250722802566509334802709728 := by decide +kernel
private theorem receipt_1_16_2339_1_part13 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 1664 128 = 239193027664822015250279636325 := by decide +kernel
private theorem receipt_1_16_2339_1_part14 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 1792 128 = 203098241369372257126835651898 := by decide +kernel
private theorem receipt_1_16_2339_1_part15 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 1920 128 = 167953413316997674202120775278 := by decide +kernel
private theorem receipt_1_16_2339_1_part16 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 2048 128 = 133745567834151491061287830068 := by decide +kernel
private theorem receipt_1_16_2339_1_part17 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 2176 128 = 100461757403392370521136170465 := by decide +kernel
private theorem receipt_1_16_2339_1_part18 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 2304 128 = 68089065589927239703659456576 := by decide +kernel
private theorem receipt_1_16_2339_1_part19 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 2432 128 = 36614607120044976644738249392 := by decide +kernel
private theorem receipt_1_16_2339_1_part20 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 2560 90 = 7377338535410921749895295165 := by decide +kernel
private theorem receipt_1_16_2339_1_join0 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 0 256 = 1551986661520481045462233713088 :=
  phaseBlock_append receipt_1_16_2339_1_part0 receipt_1_16_2339_1_part1 rfl rfl rfl
private theorem receipt_1_16_2339_1_join1 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 384 256 = 1264197266790203007904774318528 :=
  phaseBlock_append receipt_1_16_2339_1_part3 receipt_1_16_2339_1_part4 rfl rfl rfl
private theorem receipt_1_16_2339_1_join2 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 256 384 = 1966858734256791716322082326176 :=
  phaseBlock_append receipt_1_16_2339_1_part2 receipt_1_16_2339_1_join1 rfl rfl rfl
private theorem receipt_1_16_2339_1_join3 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 0 640 = 3518845395777272761784316039264 :=
  phaseBlock_append receipt_1_16_2339_1_join0 receipt_1_16_2339_1_join2 rfl rfl rfl
private theorem receipt_1_16_2339_1_join4 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 640 256 = 1083258604254683121442821745088 :=
  phaseBlock_append receipt_1_16_2339_1_part5 receipt_1_16_2339_1_part6 rfl rfl rfl
private theorem receipt_1_16_2339_1_join5 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 1024 256 = 827701962400566994389691402688 :=
  phaseBlock_append receipt_1_16_2339_1_part8 receipt_1_16_2339_1_part9 rfl rfl rfl
private theorem receipt_1_16_2339_1_join6 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 896 384 = 1304140409661023597174474569376 :=
  phaseBlock_append receipt_1_16_2339_1_part7 receipt_1_16_2339_1_join5 rfl rfl rfl
private theorem receipt_1_16_2339_1_join7 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 640 640 = 2387399013915706718617296314464 :=
  phaseBlock_append receipt_1_16_2339_1_join4 receipt_1_16_2339_1_join6 rfl rfl rfl
private theorem receipt_1_16_2339_1_join8 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 0 1280 = 5906244409692979480401612353728 :=
  phaseBlock_append receipt_1_16_2339_1_join3 receipt_1_16_2339_1_join7 rfl rfl rfl
private theorem receipt_1_16_2339_1_join9 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 1280 256 = 667591067236599554768560343488 :=
  phaseBlock_append receipt_1_16_2339_1_part10 receipt_1_16_2339_1_part11 rfl rfl rfl
private theorem receipt_1_16_2339_1_join10 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 1664 256 = 442291269034194272377115288223 :=
  phaseBlock_append receipt_1_16_2339_1_part13 receipt_1_16_2339_1_part14 rfl rfl rfl
private theorem receipt_1_16_2339_1_join11 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 1536 384 = 718541991836760781711917997951 :=
  phaseBlock_append receipt_1_16_2339_1_part12 receipt_1_16_2339_1_join10 rfl rfl rfl
private theorem receipt_1_16_2339_1_join12 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 1280 640 = 1386133059073360336480478341439 :=
  phaseBlock_append receipt_1_16_2339_1_join9 receipt_1_16_2339_1_join11 rfl rfl rfl
private theorem receipt_1_16_2339_1_join13 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 2048 256 = 234207325237543861582424000533 :=
  phaseBlock_append receipt_1_16_2339_1_part16 receipt_1_16_2339_1_part17 rfl rfl rfl
private theorem receipt_1_16_2339_1_join14 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 1920 384 = 402160738554541535784544775811 :=
  phaseBlock_append receipt_1_16_2339_1_part15 receipt_1_16_2339_1_join13 rfl rfl rfl
private theorem receipt_1_16_2339_1_join15 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 2432 218 = 43991945655455898394633544557 :=
  phaseBlock_append receipt_1_16_2339_1_part19 receipt_1_16_2339_1_part20 rfl rfl rfl
private theorem receipt_1_16_2339_1_join16 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 2304 346 = 112081011245383138098293001133 :=
  phaseBlock_append receipt_1_16_2339_1_part18 receipt_1_16_2339_1_join15 rfl rfl rfl
private theorem receipt_1_16_2339_1_join17 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 1920 730 = 514241749799924673882837776944 :=
  phaseBlock_append receipt_1_16_2339_1_join14 receipt_1_16_2339_1_join16 rfl rfl rfl
private theorem receipt_1_16_2339_1_join18 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 1280 1370 = 1900374808873285010363316118383 :=
  phaseBlock_append receipt_1_16_2339_1_join12 receipt_1_16_2339_1_join17 rfl rfl rfl
private theorem receipt_1_16_2339_1_join19 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2339 103 1 0 2 1) 0 2650 = 7806619218566264490764928472111 :=
  phaseBlock_append receipt_1_16_2339_1_join8 receipt_1_16_2339_1_join18 rfl rfl rfl

private theorem receipt_1_16_2339_1 : fastPhase (bank 1 16).shape 179827 2339 103 1 0 2 1 = 7806619218566264490764928472111 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_1_16_2339_1_join19

private theorem receipt_1_16_2340_0_part0 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 0 128 = 801205279011343538308740152064 := by decide +kernel
private theorem receipt_1_16_2340_0_part1 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 128 128 = 751560913649788544084970093312 := by decide +kernel
private theorem receipt_1_16_2340_0_part2 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 256 128 = 703037631215817778539361172224 := by decide +kernel
private theorem receipt_1_16_2340_0_part3 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 384 128 = 655622085666939034294604151552 := by decide +kernel
private theorem receipt_1_16_2340_0_part4 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 512 128 = 609300962369322630884976294656 := by decide +kernel
private theorem receipt_1_16_2340_0_part5 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 640 128 = 564060978072685226662589086464 := by decide +kernel
private theorem receipt_1_16_2340_0_part6 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 768 128 = 519888880885173630703635954432 := by decide +kernel
private theorem receipt_1_16_2340_0_part7 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 896 128 = 476771450248248614714639989504 := by decide +kernel
private theorem receipt_1_16_2340_0_part8 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 1024 128 = 434695496911568724938701667072 := by decide +kernel
private theorem receipt_1_16_2340_0_part9 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 1152 128 = 393647862907874094061746567936 := by decide +kernel
private theorem receipt_1_16_2340_0_part10 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 1280 128 = 353615421527870253118773099264 := by decide +kernel
private theorem receipt_1_16_2340_0_part11 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 1408 128 = 314585077295111943400100215552 := by decide +kernel
private theorem receipt_1_16_2340_0_part12 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 1536 128 = 276543765940886928357615139584 := by decide +kernel
private theorem receipt_1_16_2340_0_part13 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 1664 128 = 239478455309764249542053416261 := by decide +kernel
private theorem receipt_1_16_2340_0_part14 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 1792 128 = 203376176673606600736152466595 := by decide +kernel
private theorem receipt_1_16_2340_0_part15 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 1920 128 = 168223979822666443796450309367 := by decide +kernel
private theorem receipt_1_16_2340_0_part16 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 2048 128 = 134008888655547081700268989851 := by decide +kernel
private theorem receipt_1_16_2340_0_part17 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 2176 128 = 100717954934630230122157117324 := by decide +kernel
private theorem receipt_1_16_2340_0_part18 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 2304 128 = 68338261508793815674853401029 := by decide +kernel
private theorem receipt_1_16_2340_0_part19 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 2432 128 = 36856922410404865704915181169 := by decide +kernel
private theorem receipt_1_16_2340_0_part20 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 2560 90 = 7543661577964416643508602316 := by decide +kernel
private theorem receipt_1_16_2340_0_join0 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 0 256 = 1552766192661132082393710245376 :=
  phaseBlock_append receipt_1_16_2340_0_part0 receipt_1_16_2340_0_part1 rfl rfl rfl
private theorem receipt_1_16_2340_0_join1 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 384 256 = 1264923048036261665179580446208 :=
  phaseBlock_append receipt_1_16_2340_0_part3 receipt_1_16_2340_0_part4 rfl rfl rfl
private theorem receipt_1_16_2340_0_join2 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 256 384 = 1967960679252079443718941618432 :=
  phaseBlock_append receipt_1_16_2340_0_part2 receipt_1_16_2340_0_join1 rfl rfl rfl
private theorem receipt_1_16_2340_0_join3 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 0 640 = 3520726871913211526112651863808 :=
  phaseBlock_append receipt_1_16_2340_0_join0 receipt_1_16_2340_0_join2 rfl rfl rfl
private theorem receipt_1_16_2340_0_join4 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 640 256 = 1083949858957858857366225040896 :=
  phaseBlock_append receipt_1_16_2340_0_part5 receipt_1_16_2340_0_part6 rfl rfl rfl
private theorem receipt_1_16_2340_0_join5 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 1024 256 = 828343359819442819000448235008 :=
  phaseBlock_append receipt_1_16_2340_0_part8 receipt_1_16_2340_0_part9 rfl rfl rfl
private theorem receipt_1_16_2340_0_join6 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 896 384 = 1305114810067691433715088224512 :=
  phaseBlock_append receipt_1_16_2340_0_part7 receipt_1_16_2340_0_join5 rfl rfl rfl
private theorem receipt_1_16_2340_0_join7 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 640 640 = 2389064669025550291081313265408 :=
  phaseBlock_append receipt_1_16_2340_0_join4 receipt_1_16_2340_0_join6 rfl rfl rfl
private theorem receipt_1_16_2340_0_join8 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 0 1280 = 5909791540938761817193965129216 :=
  phaseBlock_append receipt_1_16_2340_0_join3 receipt_1_16_2340_0_join7 rfl rfl rfl
private theorem receipt_1_16_2340_0_join9 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 1280 256 = 668200498822982196518873314816 :=
  phaseBlock_append receipt_1_16_2340_0_part10 receipt_1_16_2340_0_part11 rfl rfl rfl
private theorem receipt_1_16_2340_0_join10 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 1664 256 = 442854631983370850278205882856 :=
  phaseBlock_append receipt_1_16_2340_0_part13 receipt_1_16_2340_0_part14 rfl rfl rfl
private theorem receipt_1_16_2340_0_join11 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 1536 384 = 719398397924257778635821022440 :=
  phaseBlock_append receipt_1_16_2340_0_part12 receipt_1_16_2340_0_join10 rfl rfl rfl
private theorem receipt_1_16_2340_0_join12 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 1280 640 = 1387598896747239975154694337256 :=
  phaseBlock_append receipt_1_16_2340_0_join9 receipt_1_16_2340_0_join11 rfl rfl rfl
private theorem receipt_1_16_2340_0_join13 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 2048 256 = 234726843590177311822426107175 :=
  phaseBlock_append receipt_1_16_2340_0_part16 receipt_1_16_2340_0_part17 rfl rfl rfl
private theorem receipt_1_16_2340_0_join14 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 1920 384 = 402950823412843755618876416542 :=
  phaseBlock_append receipt_1_16_2340_0_part15 receipt_1_16_2340_0_join13 rfl rfl rfl
private theorem receipt_1_16_2340_0_join15 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 2432 218 = 44400583988369282348423783485 :=
  phaseBlock_append receipt_1_16_2340_0_part19 receipt_1_16_2340_0_part20 rfl rfl rfl
private theorem receipt_1_16_2340_0_join16 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 2304 346 = 112738845497163098023277184514 :=
  phaseBlock_append receipt_1_16_2340_0_part18 receipt_1_16_2340_0_join15 rfl rfl rfl
private theorem receipt_1_16_2340_0_join17 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 1920 730 = 515689668910006853642153601056 :=
  phaseBlock_append receipt_1_16_2340_0_join14 receipt_1_16_2340_0_join16 rfl rfl rfl
private theorem receipt_1_16_2340_0_join18 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 1280 1370 = 1903288565657246828796847938312 :=
  phaseBlock_append receipt_1_16_2340_0_join12 receipt_1_16_2340_0_join17 rfl rfl rfl
private theorem receipt_1_16_2340_0_join19 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 0) 0 2650 = 7813080106596008645990813067528 :=
  phaseBlock_append receipt_1_16_2340_0_join8 receipt_1_16_2340_0_join18 rfl rfl rfl

private theorem receipt_1_16_2340_0 : fastPhase (bank 1 16).shape 179827 2340 103 1 0 2 0 = 7813080106596008645990813067528 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_1_16_2340_0_join19

private theorem receipt_1_16_2340_1_part0 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 0 128 = 800818151694406395902154616704 := by decide +kernel
private theorem receipt_1_16_2340_1_part1 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 128 128 = 751182313387114288659393720192 := by decide +kernel
private theorem receipt_1_16_2340_1_part2 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 256 128 = 702667456863879632186925625216 := by decide +kernel
private theorem receipt_1_16_2340_1_part3 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 384 128 = 655260236321737681051658923904 := by decide +kernel
private theorem receipt_1_16_2340_1_part4 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 512 128 = 608947337366193855798419763072 := by decide +kernel
private theorem receipt_1_16_2340_1_part5 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 640 128 = 563715476986107554856199565184 := by decide +kernel
private theorem receipt_1_16_2340_1_part6 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 768 128 = 519551403528575966444402749312 := by decide +kernel
private theorem receipt_1_16_2340_1_part7 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 896 128 = 476441896673817880479094452096 := by decide +kernel
private theorem receipt_1_16_2340_1_part8 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 1024 128 = 434373767410057500479248248704 := by decide +kernel
private theorem receipt_1_16_2340_1_part9 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 1152 128 = 393333858008408255472993873792 := by decide +kernel
private theorem receipt_1_16_2340_1_part10 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 1280 128 = 353309041997756611903864942464 := by decide +kernel
private theorem receipt_1_16_2340_1_part11 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 1408 128 = 314286224139645885537046671232 := by decide +kernel
private theorem receipt_1_16_2340_1_part12 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 1536 128 = 276252340403160053365623598976 := by decide +kernel
private theorem receipt_1_16_2340_1_part13 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 1664 128 = 239194358869391900193269850858 := by decide +kernel
private theorem receipt_1_16_2340_1_part14 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 1792 128 = 203099311004047360123259226786 := by decide +kernel
private theorem receipt_1_16_2340_1_part15 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 1920 128 = 167954246779158817836217052664 := by decide +kernel
private theorem receipt_1_16_2340_1_part16 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 2048 128 = 133746190327310736842273871886 := by decide +kernel
private theorem receipt_1_16_2340_1_part17 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 2176 128 = 100462193648060637848397187787 := by decide +kernel
private theorem receipt_1_16_2340_1_part18 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 2304 128 = 68089339827405370865855330931 := by decide +kernel
private theorem receipt_1_16_2340_1_part19 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 2432 128 = 36614743134579246317592743984 := by decide +kernel
private theorem receipt_1_16_2340_1_part20 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 2560 90 = 7377364001579965762194463245 := by decide +kernel
private theorem receipt_1_16_2340_1_join0 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 0 256 = 1552000465081520684561548336896 :=
  phaseBlock_append receipt_1_16_2340_1_part0 receipt_1_16_2340_1_part1 rfl rfl rfl
private theorem receipt_1_16_2340_1_join1 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 384 256 = 1264207573687931536850078686976 :=
  phaseBlock_append receipt_1_16_2340_1_part3 receipt_1_16_2340_1_part4 rfl rfl rfl
private theorem receipt_1_16_2340_1_join2 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 256 384 = 1966875030551811169037004312192 :=
  phaseBlock_append receipt_1_16_2340_1_part2 receipt_1_16_2340_1_join1 rfl rfl rfl
private theorem receipt_1_16_2340_1_join3 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 0 640 = 3518875495633331853598552649088 :=
  phaseBlock_append receipt_1_16_2340_1_join0 receipt_1_16_2340_1_join2 rfl rfl rfl
private theorem receipt_1_16_2340_1_join4 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 640 256 = 1083266880514683521300602314496 :=
  phaseBlock_append receipt_1_16_2340_1_part5 receipt_1_16_2340_1_part6 rfl rfl rfl
private theorem receipt_1_16_2340_1_join5 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 1024 256 = 827707625418465755952242122496 :=
  phaseBlock_append receipt_1_16_2340_1_part8 receipt_1_16_2340_1_part9 rfl rfl rfl
private theorem receipt_1_16_2340_1_join6 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 896 384 = 1304149522092283636431336574592 :=
  phaseBlock_append receipt_1_16_2340_1_part7 receipt_1_16_2340_1_join5 rfl rfl rfl
private theorem receipt_1_16_2340_1_join7 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 640 640 = 2387416402606967157731938889088 :=
  phaseBlock_append receipt_1_16_2340_1_join4 receipt_1_16_2340_1_join6 rfl rfl rfl
private theorem receipt_1_16_2340_1_join8 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 0 1280 = 5906291898240299011330491538176 :=
  phaseBlock_append receipt_1_16_2340_1_join3 receipt_1_16_2340_1_join7 rfl rfl rfl
private theorem receipt_1_16_2340_1_join9 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 1280 256 = 667595266137402497440911613696 :=
  phaseBlock_append receipt_1_16_2340_1_part10 receipt_1_16_2340_1_part11 rfl rfl rfl
private theorem receipt_1_16_2340_1_join10 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 1664 256 = 442293669873439260316529077644 :=
  phaseBlock_append receipt_1_16_2340_1_part13 receipt_1_16_2340_1_part14 rfl rfl rfl
private theorem receipt_1_16_2340_1_join11 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 1536 384 = 718546010276599313682152676620 :=
  phaseBlock_append receipt_1_16_2340_1_part12 receipt_1_16_2340_1_join10 rfl rfl rfl
private theorem receipt_1_16_2340_1_join12 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 1280 640 = 1386141276414001811123064290316 :=
  phaseBlock_append receipt_1_16_2340_1_join9 receipt_1_16_2340_1_join11 rfl rfl rfl
private theorem receipt_1_16_2340_1_join13 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 2048 256 = 234208383975371374690671059673 :=
  phaseBlock_append receipt_1_16_2340_1_part16 receipt_1_16_2340_1_part17 rfl rfl rfl
private theorem receipt_1_16_2340_1_join14 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 1920 384 = 402162630754530192526888112337 :=
  phaseBlock_append receipt_1_16_2340_1_part15 receipt_1_16_2340_1_join13 rfl rfl rfl
private theorem receipt_1_16_2340_1_join15 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 2432 218 = 43992107136159212079787207229 :=
  phaseBlock_append receipt_1_16_2340_1_part19 receipt_1_16_2340_1_part20 rfl rfl rfl
private theorem receipt_1_16_2340_1_join16 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 2304 346 = 112081446963564582945642538160 :=
  phaseBlock_append receipt_1_16_2340_1_part18 receipt_1_16_2340_1_join15 rfl rfl rfl
private theorem receipt_1_16_2340_1_join17 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 1920 730 = 514244077718094775472530650497 :=
  phaseBlock_append receipt_1_16_2340_1_join14 receipt_1_16_2340_1_join16 rfl rfl rfl
private theorem receipt_1_16_2340_1_join18 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 1280 1370 = 1900385354132096586595594940813 :=
  phaseBlock_append receipt_1_16_2340_1_join12 receipt_1_16_2340_1_join17 rfl rfl rfl
private theorem receipt_1_16_2340_1_join19 :
    phaseBlock (fastLayer (bank 1 16).shape 179827 2340 103 1 0 2 1) 0 2650 = 7806677252372395597926086478989 :=
  phaseBlock_append receipt_1_16_2340_1_join8 receipt_1_16_2340_1_join18 rfl rfl rfl

private theorem receipt_1_16_2340_1 : fastPhase (bank 1 16).shape 179827 2340 103 1 0 2 1 = 7806677252372395597926086478989 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_1_16_2340_1_join19

theorem receipt_1_16 : Checked (bank 1 16) 103 0 2 := by
  refine checked_from_values (bank 1 16) 103 0 2
    (P3_7_1.checked (bank 1 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_12604_2649)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_16_2339_0 receipt_1_16_2339_1 receipt_1_16_2340_0 receipt_1_16_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_16_2339_0_part0 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 0 128 = 430124079375443818019323513920 := by decide +kernel
private theorem receipt_2_16_2339_0_part1 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 128 128 = 402453512588201375370480708672 := by decide +kernel
private theorem receipt_2_16_2339_0_part2 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 256 128 = 375516989608242770998458960960 := by decide +kernel
private theorem receipt_2_16_2339_0_part3 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 384 128 = 349302724625961155544426196032 := by decide +kernel
private theorem receipt_2_16_2339_0_part4 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 512 128 = 323799025783176932736744393792 := by decide +kernel
private theorem receipt_2_16_2339_0_part5 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 640 128 = 298994294865475230456456375360 := by decide +kernel
private theorem receipt_2_16_2339_0_part6 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 768 128 = 274877026994543371802772589632 := by decide +kernel
private theorem receipt_2_16_2339_0_part7 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 896 128 = 251435810320508346158557899840 := by decide +kernel
private theorem receipt_2_16_2339_0_part8 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 1024 128 = 228659325714274280255818370112 := by decide +kernel
private theorem receipt_2_16_2339_0_part9 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 1152 128 = 206536346459859909241188052032 := by decide +kernel
private theorem receipt_2_16_2339_0_part10 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 1280 128 = 185055737946736047741415771200 := by decide +kernel
private theorem receipt_2_16_2339_0_part11 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 1408 128 = 164206457362163060928851913792 := by decide +kernel
private theorem receipt_2_16_2339_0_part12 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 1536 128 = 143977553383528335586935213120 := by decide +kernel
private theorem receipt_2_16_2339_0_part13 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 1664 128 = 124358166412634528262949991640 := by decide +kernel
private theorem receipt_2_16_2339_0_part14 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 1792 128 = 105337544743542157961391042283 := by decide +kernel
private theorem receipt_2_16_2339_0_part15 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 1920 128 = 86905019658215260222783581936 := by decide +kernel
private theorem receipt_2_16_2339_0_part16 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 2048 128 = 69049983612071969770303776848 := by decide +kernel
private theorem receipt_2_16_2339_0_part17 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 2176 128 = 51761917703441526400950994890 := by decide +kernel
private theorem receipt_2_16_2339_0_part18 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 2304 128 = 35030392901157544028591693422 := by decide +kernel
private theorem receipt_2_16_2339_0_part19 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 2432 128 = 18845069789415294702100638966 := by decide +kernel
private theorem receipt_2_16_2339_0_part20 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 2560 90 = 3848953776685275655673921232 := by decide +kernel
private theorem receipt_2_16_2339_0_join0 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 0 256 = 832577591963645193389804222592 :=
  phaseBlock_append receipt_2_16_2339_0_part0 receipt_2_16_2339_0_part1 rfl rfl rfl
private theorem receipt_2_16_2339_0_join1 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 384 256 = 673101750409138088281170589824 :=
  phaseBlock_append receipt_2_16_2339_0_part3 receipt_2_16_2339_0_part4 rfl rfl rfl
private theorem receipt_2_16_2339_0_join2 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 256 384 = 1048618740017380859279629550784 :=
  phaseBlock_append receipt_2_16_2339_0_part2 receipt_2_16_2339_0_join1 rfl rfl rfl
private theorem receipt_2_16_2339_0_join3 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 0 640 = 1881196331981026052669433773376 :=
  phaseBlock_append receipt_2_16_2339_0_join0 receipt_2_16_2339_0_join2 rfl rfl rfl
private theorem receipt_2_16_2339_0_join4 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 640 256 = 573871321860018602259228964992 :=
  phaseBlock_append receipt_2_16_2339_0_part5 receipt_2_16_2339_0_part6 rfl rfl rfl
private theorem receipt_2_16_2339_0_join5 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 1024 256 = 435195672174134189497006422144 :=
  phaseBlock_append receipt_2_16_2339_0_part8 receipt_2_16_2339_0_part9 rfl rfl rfl
private theorem receipt_2_16_2339_0_join6 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 896 384 = 686631482494642535655564321984 :=
  phaseBlock_append receipt_2_16_2339_0_part7 receipt_2_16_2339_0_join5 rfl rfl rfl
private theorem receipt_2_16_2339_0_join7 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 640 640 = 1260502804354661137914793286976 :=
  phaseBlock_append receipt_2_16_2339_0_join4 receipt_2_16_2339_0_join6 rfl rfl rfl
private theorem receipt_2_16_2339_0_join8 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 0 1280 = 3141699136335687190584227060352 :=
  phaseBlock_append receipt_2_16_2339_0_join3 receipt_2_16_2339_0_join7 rfl rfl rfl
private theorem receipt_2_16_2339_0_join9 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 1280 256 = 349262195308899108670267684992 :=
  phaseBlock_append receipt_2_16_2339_0_part10 receipt_2_16_2339_0_part11 rfl rfl rfl
private theorem receipt_2_16_2339_0_join10 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 1664 256 = 229695711156176686224341033923 :=
  phaseBlock_append receipt_2_16_2339_0_part13 receipt_2_16_2339_0_part14 rfl rfl rfl
private theorem receipt_2_16_2339_0_join11 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 1536 384 = 373673264539705021811276247043 :=
  phaseBlock_append receipt_2_16_2339_0_part12 receipt_2_16_2339_0_join10 rfl rfl rfl
private theorem receipt_2_16_2339_0_join12 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 1280 640 = 722935459848604130481543932035 :=
  phaseBlock_append receipt_2_16_2339_0_join9 receipt_2_16_2339_0_join11 rfl rfl rfl
private theorem receipt_2_16_2339_0_join13 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 2048 256 = 120811901315513496171254771738 :=
  phaseBlock_append receipt_2_16_2339_0_part16 receipt_2_16_2339_0_part17 rfl rfl rfl
private theorem receipt_2_16_2339_0_join14 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 1920 384 = 207716920973728756394038353674 :=
  phaseBlock_append receipt_2_16_2339_0_part15 receipt_2_16_2339_0_join13 rfl rfl rfl
private theorem receipt_2_16_2339_0_join15 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 2432 218 = 22694023566100570357774560198 :=
  phaseBlock_append receipt_2_16_2339_0_part19 receipt_2_16_2339_0_part20 rfl rfl rfl
private theorem receipt_2_16_2339_0_join16 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 2304 346 = 57724416467258114386366253620 :=
  phaseBlock_append receipt_2_16_2339_0_part18 receipt_2_16_2339_0_join15 rfl rfl rfl
private theorem receipt_2_16_2339_0_join17 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 1920 730 = 265441337440986870780404607294 :=
  phaseBlock_append receipt_2_16_2339_0_join14 receipt_2_16_2339_0_join16 rfl rfl rfl
private theorem receipt_2_16_2339_0_join18 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 1280 1370 = 988376797289591001261948539329 :=
  phaseBlock_append receipt_2_16_2339_0_join12 receipt_2_16_2339_0_join17 rfl rfl rfl
private theorem receipt_2_16_2339_0_join19 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 0) 0 2650 = 4130075933625278191846175599681 :=
  phaseBlock_append receipt_2_16_2339_0_join8 receipt_2_16_2339_0_join18 rfl rfl rfl

private theorem receipt_2_16_2339_0 : fastPhase (bank 2 16).shape 179827 2339 103 1 0 7 0 = 4130075933625278191846175599681 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_2_16_2339_0_join19

private theorem receipt_2_16_2339_1_part0 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 0 128 = 429907763623105279562702377344 := by decide +kernel
private theorem receipt_2_16_2339_1_part1 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 128 128 = 402242818971236533814952513920 := by decide +kernel
private theorem receipt_2_16_2339_1_part2 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 256 128 = 375311828188859524854965719424 := by decide +kernel
private theorem receipt_2_16_2339_1_part3 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 384 128 = 349103006184529140069793714560 := by decide +kernel
private theorem receipt_2_16_2339_1_part4 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 512 128 = 323604661815871162474070528384 := by decide +kernel
private theorem receipt_2_16_2339_1_part5 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 640 128 = 298805197581919741775499284864 := by decide +kernel
private theorem receipt_2_16_2339_1_part6 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 768 128 = 274693109315454865440338989440 := by decide +kernel
private theorem receipt_2_16_2339_1_part7 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 896 128 = 251256985875339829758891315584 := by decide +kernel
private theorem receipt_2_16_2339_1_part8 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 1024 128 = 228485508838858710910987391360 := by decide +kernel
private theorem receipt_2_16_2339_1_part9 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 1152 128 = 206367452194053836031474585984 := by decide +kernel
private theorem receipt_2_16_2339_1_part10 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 1280 128 = 184891682032063254275703296384 := by decide +kernel
private theorem receipt_2_16_2339_1_part11 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 1408 128 = 164047156239458207885013733760 := by decide +kernel
private theorem receipt_2_16_2339_1_part12 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 1536 128 = 143822924190580603252222710144 := by decide +kernel
private theorem receipt_2_16_2339_1_part13 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 1664 128 = 124208126981191781753702862276 := by decide +kernel
private theorem receipt_2_16_2339_1_part14 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 1792 128 = 105192013574183057091992106731 := by decide +kernel
private theorem receipt_2_16_2339_1_part15 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 1920 128 = 86763915913208603376965996716 := by decide +kernel
private theorem receipt_2_16_2339_1_part16 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 2048 128 = 68913227140588218063506810324 := by decide +kernel
private theorem receipt_2_16_2339_1_part17 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 2176 128 = 51629429040825166650462874890 := by decide +kernel
private theorem receipt_2_16_2339_1_part18 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 2304 128 = 34902093266628562290716491654 := by decide +kernel
private theorem receipt_2_16_2339_1_part19 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 2432 128 = 18720881083708442127142595250 := by decide +kernel
private theorem receipt_2_16_2339_1_part20 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 2560 90 = 3764053236138012218560191018 := by decide +kernel
private theorem receipt_2_16_2339_1_join0 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 0 256 = 832150582594341813377654891264 :=
  phaseBlock_append receipt_2_16_2339_1_part0 receipt_2_16_2339_1_part1 rfl rfl rfl
private theorem receipt_2_16_2339_1_join1 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 384 256 = 672707668000400302543864242944 :=
  phaseBlock_append receipt_2_16_2339_1_part3 receipt_2_16_2339_1_part4 rfl rfl rfl
private theorem receipt_2_16_2339_1_join2 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 256 384 = 1048019496189259827398829962368 :=
  phaseBlock_append receipt_2_16_2339_1_part2 receipt_2_16_2339_1_join1 rfl rfl rfl
private theorem receipt_2_16_2339_1_join3 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 0 640 = 1880170078783601640776484853632 :=
  phaseBlock_append receipt_2_16_2339_1_join0 receipt_2_16_2339_1_join2 rfl rfl rfl
private theorem receipt_2_16_2339_1_join4 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 640 256 = 573498306897374607215838274304 :=
  phaseBlock_append receipt_2_16_2339_1_part5 receipt_2_16_2339_1_part6 rfl rfl rfl
private theorem receipt_2_16_2339_1_join5 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 1024 256 = 434852961032912546942461977344 :=
  phaseBlock_append receipt_2_16_2339_1_part8 receipt_2_16_2339_1_part9 rfl rfl rfl
private theorem receipt_2_16_2339_1_join6 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 896 384 = 686109946908252376701353292928 :=
  phaseBlock_append receipt_2_16_2339_1_part7 receipt_2_16_2339_1_join5 rfl rfl rfl
private theorem receipt_2_16_2339_1_join7 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 640 640 = 1259608253805626983917191567232 :=
  phaseBlock_append receipt_2_16_2339_1_join4 receipt_2_16_2339_1_join6 rfl rfl rfl
private theorem receipt_2_16_2339_1_join8 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 0 1280 = 3139778332589228624693676420864 :=
  phaseBlock_append receipt_2_16_2339_1_join3 receipt_2_16_2339_1_join7 rfl rfl rfl
private theorem receipt_2_16_2339_1_join9 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 1280 256 = 348938838271521462160717030144 :=
  phaseBlock_append receipt_2_16_2339_1_part10 receipt_2_16_2339_1_part11 rfl rfl rfl
private theorem receipt_2_16_2339_1_join10 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 1664 256 = 229400140555374838845694969007 :=
  phaseBlock_append receipt_2_16_2339_1_part13 receipt_2_16_2339_1_part14 rfl rfl rfl
private theorem receipt_2_16_2339_1_join11 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 1536 384 = 373223064745955442097917679151 :=
  phaseBlock_append receipt_2_16_2339_1_part12 receipt_2_16_2339_1_join10 rfl rfl rfl
private theorem receipt_2_16_2339_1_join12 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 1280 640 = 722161903017476904258634709295 :=
  phaseBlock_append receipt_2_16_2339_1_join9 receipt_2_16_2339_1_join11 rfl rfl rfl
private theorem receipt_2_16_2339_1_join13 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 2048 256 = 120542656181413384713969685214 :=
  phaseBlock_append receipt_2_16_2339_1_part16 receipt_2_16_2339_1_part17 rfl rfl rfl
private theorem receipt_2_16_2339_1_join14 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 1920 384 = 207306572094621988090935681930 :=
  phaseBlock_append receipt_2_16_2339_1_part15 receipt_2_16_2339_1_join13 rfl rfl rfl
private theorem receipt_2_16_2339_1_join15 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 2432 218 = 22484934319846454345702786268 :=
  phaseBlock_append receipt_2_16_2339_1_part19 receipt_2_16_2339_1_part20 rfl rfl rfl
private theorem receipt_2_16_2339_1_join16 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 2304 346 = 57387027586475016636419277922 :=
  phaseBlock_append receipt_2_16_2339_1_part18 receipt_2_16_2339_1_join15 rfl rfl rfl
private theorem receipt_2_16_2339_1_join17 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 1920 730 = 264693599681097004727354959852 :=
  phaseBlock_append receipt_2_16_2339_1_join14 receipt_2_16_2339_1_join16 rfl rfl rfl
private theorem receipt_2_16_2339_1_join18 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 1280 1370 = 986855502698573908985989669147 :=
  phaseBlock_append receipt_2_16_2339_1_join12 receipt_2_16_2339_1_join17 rfl rfl rfl
private theorem receipt_2_16_2339_1_join19 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2339 103 1 0 7 1) 0 2650 = 4126633835287802533679666090011 :=
  phaseBlock_append receipt_2_16_2339_1_join8 receipt_2_16_2339_1_join18 rfl rfl rfl

private theorem receipt_2_16_2339_1 : fastPhase (bank 2 16).shape 179827 2339 103 1 0 7 1 = 4126633835287802533679666090011 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_2_16_2339_1_join19

private theorem receipt_2_16_2340_0_part0 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 0 128 = 430127954983205230751760133760 := by decide +kernel
private theorem receipt_2_16_2340_0_part1 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 128 128 = 402457041544116636805227564672 := by decide +kernel
private theorem receipt_2_16_2340_0_part2 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 256 128 = 375520190197396023752807706240 := by decide +kernel
private theorem receipt_2_16_2340_0_part3 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 384 128 = 349305614764409080195301871232 := by decide +kernel
private theorem receipt_2_16_2340_0_part4 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 512 128 = 323801623021127747407634148992 := by decide +kernel
private theorem receipt_2_16_2340_0_part5 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 640 128 = 298996616390456915190385987200 := by decide +kernel
private theorem receipt_2_16_2340_0_part6 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 768 128 = 274879089634561117721330773632 := by decide +kernel
private theorem receipt_2_16_2340_0_part7 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 896 128 = 251437630547191229406968417920 := by decide +kernel
private theorem receipt_2_16_2340_0_part8 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 1024 128 = 228660919646011160734059933312 := by decide +kernel
private theorem receipt_2_16_2340_0_part9 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 1152 128 = 206537729864924554121162018432 := by decide +kernel
private theorem receipt_2_16_2340_0_part10 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 1280 128 = 185056926246401479770161639040 := by decide +kernel
private theorem receipt_2_16_2340_0_part11 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 1408 128 = 164207465633805131517810609792 := by decide +kernel
private theorem receipt_2_16_2340_0_part12 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 1536 128 = 143978396363718522687260176000 := by decide +kernel
private theorem receipt_2_16_2340_0_part13 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 1664 128 = 124358858441033051502089784137 := by decide +kernel
private theorem receipt_2_16_2340_0_part14 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 1792 128 = 105338099451322893816019548590 := by decide +kernel
private theorem receipt_2_16_2340_0_part15 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 1920 128 = 86905450871126015246443620041 := by decide +kernel
private theorem receipt_2_16_2340_0_part16 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 2048 128 = 69050304953154629751966428928 := by decide +kernel
private theorem receipt_2_16_2340_0_part17 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 2176 128 = 51762142445338858706336887188 := by decide +kernel
private theorem receipt_2_16_2340_0_part18 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 2304 128 = 35030533970781490375577407832 := by decide +kernel
private theorem receipt_2_16_2340_0_part19 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 2432 128 = 18845139781995786057333440283 := by decide +kernel
private theorem receipt_2_16_2340_0_part20 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 2560 90 = 3848967057685520999681617542 := by decide +kernel
private theorem receipt_2_16_2340_0_join0 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 0 256 = 832584996527321867556987698432 :=
  phaseBlock_append receipt_2_16_2340_0_part0 receipt_2_16_2340_0_part1 rfl rfl rfl
private theorem receipt_2_16_2340_0_join1 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 384 256 = 673107237785536827602936020224 :=
  phaseBlock_append receipt_2_16_2340_0_part3 receipt_2_16_2340_0_part4 rfl rfl rfl
private theorem receipt_2_16_2340_0_join2 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 256 384 = 1048627427982932851355743726464 :=
  phaseBlock_append receipt_2_16_2340_0_part2 receipt_2_16_2340_0_join1 rfl rfl rfl
private theorem receipt_2_16_2340_0_join3 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 0 640 = 1881212424510254718912731424896 :=
  phaseBlock_append receipt_2_16_2340_0_join0 receipt_2_16_2340_0_join2 rfl rfl rfl
private theorem receipt_2_16_2340_0_join4 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 640 256 = 573875706025018032911716760832 :=
  phaseBlock_append receipt_2_16_2340_0_part5 receipt_2_16_2340_0_part6 rfl rfl rfl
private theorem receipt_2_16_2340_0_join5 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 1024 256 = 435198649510935714855221951744 :=
  phaseBlock_append receipt_2_16_2340_0_part8 receipt_2_16_2340_0_part9 rfl rfl rfl
private theorem receipt_2_16_2340_0_join6 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 896 384 = 686636280058126944262190369664 :=
  phaseBlock_append receipt_2_16_2340_0_part7 receipt_2_16_2340_0_join5 rfl rfl rfl
private theorem receipt_2_16_2340_0_join7 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 640 640 = 1260511986083144977173907130496 :=
  phaseBlock_append receipt_2_16_2340_0_join4 receipt_2_16_2340_0_join6 rfl rfl rfl
private theorem receipt_2_16_2340_0_join8 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 0 1280 = 3141724410593399696086638555392 :=
  phaseBlock_append receipt_2_16_2340_0_join3 receipt_2_16_2340_0_join7 rfl rfl rfl
private theorem receipt_2_16_2340_0_join9 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 1280 256 = 349264391880206611287972248832 :=
  phaseBlock_append receipt_2_16_2340_0_part10 receipt_2_16_2340_0_part11 rfl rfl rfl
private theorem receipt_2_16_2340_0_join10 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 1664 256 = 229696957892355945318109332727 :=
  phaseBlock_append receipt_2_16_2340_0_part13 receipt_2_16_2340_0_part14 rfl rfl rfl
private theorem receipt_2_16_2340_0_join11 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 1536 384 = 373675354256074468005369508727 :=
  phaseBlock_append receipt_2_16_2340_0_part12 receipt_2_16_2340_0_join10 rfl rfl rfl
private theorem receipt_2_16_2340_0_join12 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 1280 640 = 722939746136281079293341757559 :=
  phaseBlock_append receipt_2_16_2340_0_join9 receipt_2_16_2340_0_join11 rfl rfl rfl
private theorem receipt_2_16_2340_0_join13 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 2048 256 = 120812447398493488458303316116 :=
  phaseBlock_append receipt_2_16_2340_0_part16 receipt_2_16_2340_0_part17 rfl rfl rfl
private theorem receipt_2_16_2340_0_join14 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 1920 384 = 207717898269619503704746936157 :=
  phaseBlock_append receipt_2_16_2340_0_part15 receipt_2_16_2340_0_join13 rfl rfl rfl
private theorem receipt_2_16_2340_0_join15 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 2432 218 = 22694106839681307057015057825 :=
  phaseBlock_append receipt_2_16_2340_0_part19 receipt_2_16_2340_0_part20 rfl rfl rfl
private theorem receipt_2_16_2340_0_join16 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 2304 346 = 57724640810462797432592465657 :=
  phaseBlock_append receipt_2_16_2340_0_part18 receipt_2_16_2340_0_join15 rfl rfl rfl
private theorem receipt_2_16_2340_0_join17 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 1920 730 = 265442539080082301137339401814 :=
  phaseBlock_append receipt_2_16_2340_0_join14 receipt_2_16_2340_0_join16 rfl rfl rfl
private theorem receipt_2_16_2340_0_join18 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 1280 1370 = 988382285216363380430681159373 :=
  phaseBlock_append receipt_2_16_2340_0_join12 receipt_2_16_2340_0_join17 rfl rfl rfl
private theorem receipt_2_16_2340_0_join19 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 0) 0 2650 = 4130106695809763076517319714765 :=
  phaseBlock_append receipt_2_16_2340_0_join8 receipt_2_16_2340_0_join18 rfl rfl rfl

private theorem receipt_2_16_2340_0 : fastPhase (bank 2 16).shape 179827 2340 103 1 0 7 0 = 4130106695809763076517319714765 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_2_16_2340_0_join19

private theorem receipt_2_16_2340_1_part0 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 0 128 = 429911637620565581624995379520 := by decide +kernel
private theorem receipt_2_16_2340_1_part1 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 128 128 = 402246346393376111688332818752 := by decide +kernel
private theorem receipt_2_16_2340_1_part2 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 256 128 = 375315027318937589155322919232 := by decide +kernel
private theorem receipt_2_16_2340_1_part3 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 384 128 = 349105894936795037801430169920 := by decide +kernel
private theorem receipt_2_16_2340_1_part4 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 512 128 = 323607257738743312638797248832 := by decide +kernel
private theorem receipt_2_16_2340_1_part5 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 640 128 = 298807517861153795767779604800 := by decide +kernel
private theorem receipt_2_16_2340_1_part6 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 768 128 = 274695170777301092228480039232 := by decide +kernel
private theorem receipt_2_16_2340_1_part7 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 896 128 = 251258804989689725852283287872 := by decide +kernel
private theorem receipt_2_16_2340_1_part8 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 1024 128 = 228487101722380835113390602560 := by decide +kernel
private theorem receipt_2_16_2340_1_part9 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 1152 128 = 206368834613318868980354332992 := by decide +kernel
private theorem receipt_2_16_2340_1_part10 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 1280 128 = 184892869406658282767612508480 := by decide +kernel
private theorem receipt_2_16_2340_1_part11 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 1408 128 = 164048163645090233987023419712 := by decide +kernel
private theorem receipt_2_16_2340_1_part12 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 1536 128 = 143823766362169278199400200512 := by decide +kernel
private theorem receipt_2_16_2340_1_part13 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 1664 128 = 124208818256831877866632828460 := by decide +kernel
private theorem receipt_2_16_2340_1_part14 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 1792 128 = 105192567584010396020287384496 := by decide +kernel
private theorem receipt_2_16_2340_1_part15 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 1920 128 = 86764346481463534683410432944 := by decide +kernel
private theorem receipt_2_16_2340_1_part16 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 2048 128 = 68913547888665261849285632566 := by decide +kernel
private theorem receipt_2_16_2340_1_part17 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 2176 128 = 51629653239741939095736029285 := by decide +kernel
private theorem receipt_2_16_2340_1_part18 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 2304 128 = 34902233841701900454848438544 := by decide +kernel
private theorem receipt_2_16_2340_1_part19 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 2432 128 = 18720950628571443721504089183 := by decide +kernel
private theorem receipt_2_16_2340_1_part20 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 2560 90 = 3764066229532268874814515848 := by decide +kernel
private theorem receipt_2_16_2340_1_join0 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 0 256 = 832157984013941693313328198272 :=
  phaseBlock_append receipt_2_16_2340_1_part0 receipt_2_16_2340_1_part1 rfl rfl rfl
private theorem receipt_2_16_2340_1_join1 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 384 256 = 672713152675538350440227418752 :=
  phaseBlock_append receipt_2_16_2340_1_part3 receipt_2_16_2340_1_part4 rfl rfl rfl
private theorem receipt_2_16_2340_1_join2 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 256 384 = 1048028179994475939595550337984 :=
  phaseBlock_append receipt_2_16_2340_1_part2 receipt_2_16_2340_1_join1 rfl rfl rfl
private theorem receipt_2_16_2340_1_join3 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 0 640 = 1880186164008417632908878536256 :=
  phaseBlock_append receipt_2_16_2340_1_join0 receipt_2_16_2340_1_join2 rfl rfl rfl
private theorem receipt_2_16_2340_1_join4 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 640 256 = 573502688638454887996259644032 :=
  phaseBlock_append receipt_2_16_2340_1_part5 receipt_2_16_2340_1_part6 rfl rfl rfl
private theorem receipt_2_16_2340_1_join5 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 1024 256 = 434855936335699704093744935552 :=
  phaseBlock_append receipt_2_16_2340_1_part8 receipt_2_16_2340_1_part9 rfl rfl rfl
private theorem receipt_2_16_2340_1_join6 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 896 384 = 686114741325389429946028223424 :=
  phaseBlock_append receipt_2_16_2340_1_part7 receipt_2_16_2340_1_join5 rfl rfl rfl
private theorem receipt_2_16_2340_1_join7 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 640 640 = 1259617429963844317942287867456 :=
  phaseBlock_append receipt_2_16_2340_1_join4 receipt_2_16_2340_1_join6 rfl rfl rfl
private theorem receipt_2_16_2340_1_join8 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 0 1280 = 3139803593972261950851166403712 :=
  phaseBlock_append receipt_2_16_2340_1_join3 receipt_2_16_2340_1_join7 rfl rfl rfl
private theorem receipt_2_16_2340_1_join9 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 1280 256 = 348941033051748516754635928192 :=
  phaseBlock_append receipt_2_16_2340_1_part10 receipt_2_16_2340_1_part11 rfl rfl rfl
private theorem receipt_2_16_2340_1_join10 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 1664 256 = 229401385840842273886920212956 :=
  phaseBlock_append receipt_2_16_2340_1_part13 receipt_2_16_2340_1_part14 rfl rfl rfl
private theorem receipt_2_16_2340_1_join11 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 1536 384 = 373225152203011552086320413468 :=
  phaseBlock_append receipt_2_16_2340_1_part12 receipt_2_16_2340_1_join10 rfl rfl rfl
private theorem receipt_2_16_2340_1_join12 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 1280 640 = 722166185254760068840956341660 :=
  phaseBlock_append receipt_2_16_2340_1_join9 receipt_2_16_2340_1_join11 rfl rfl rfl
private theorem receipt_2_16_2340_1_join13 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 2048 256 = 120543201128407200945021661851 :=
  phaseBlock_append receipt_2_16_2340_1_part16 receipt_2_16_2340_1_part17 rfl rfl rfl
private theorem receipt_2_16_2340_1_join14 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 1920 384 = 207307547609870735628432094795 :=
  phaseBlock_append receipt_2_16_2340_1_part15 receipt_2_16_2340_1_join13 rfl rfl rfl
private theorem receipt_2_16_2340_1_join15 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 2432 218 = 22485016858103712596318605031 :=
  phaseBlock_append receipt_2_16_2340_1_part19 receipt_2_16_2340_1_part20 rfl rfl rfl
private theorem receipt_2_16_2340_1_join16 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 2304 346 = 57387250699805613051167043575 :=
  phaseBlock_append receipt_2_16_2340_1_part18 receipt_2_16_2340_1_join15 rfl rfl rfl
private theorem receipt_2_16_2340_1_join17 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 1920 730 = 264694798309676348679599138370 :=
  phaseBlock_append receipt_2_16_2340_1_join14 receipt_2_16_2340_1_join16 rfl rfl rfl
private theorem receipt_2_16_2340_1_join18 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 1280 1370 = 986860983564436417520555480030 :=
  phaseBlock_append receipt_2_16_2340_1_join12 receipt_2_16_2340_1_join17 rfl rfl rfl
private theorem receipt_2_16_2340_1_join19 :
    phaseBlock (fastLayer (bank 2 16).shape 179827 2340 103 1 0 7 1) 0 2650 = 4126664577536698368371721883742 :=
  phaseBlock_append receipt_2_16_2340_1_join8 receipt_2_16_2340_1_join18 rfl rfl rfl

private theorem receipt_2_16_2340_1 : fastPhase (bank 2 16).shape 179827 2340 103 1 0 7 1 = 4126664577536698368371721883742 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_2_16_2340_1_join19

theorem receipt_2_16 : Checked (bank 2 16) 103 0 7 := by
  refine checked_from_values (bank 2 16) 103 0 7
    (P3_7_1.checked (bank 2 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_12604_2649)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_16_2339_0 receipt_2_16_2339_1 receipt_2_16_2340_0 receipt_2_16_2340_1 (by decide +kernel) (by decide +kernel)

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
    (word : K1.I → K1_14.L) (lo : 2339 ≤ h) (hi : h ≤ 33561) (rect : Fin 4)
    (i : Fin 1) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group7_stage i)).shape
      (cutoff h rect (group7_stage i)), ¬ G∣Q :=
  (group7_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group7_avoids

end Lower6960.RescueSource
