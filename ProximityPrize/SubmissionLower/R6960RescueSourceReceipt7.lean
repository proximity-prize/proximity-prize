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

private theorem receipt_0_16_2402_0_part0 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 0 128 = 934015781259714302192072474784 := by decide +kernel
private theorem receipt_0_16_2402_0_part1 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 128 128 = 876441754219184241273783652512 := by decide +kernel
private theorem receipt_0_16_2402_0_part2 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 256 128 = 820135990327019095283320414368 := by decide +kernel
private theorem receipt_0_16_2402_0_part3 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 384 128 = 765084245993935508204541882528 := by decide +kernel
private theorem receipt_0_16_2402_0_part4 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 512 128 = 711272294219551323426667790496 := by decide +kernel
private theorem receipt_0_16_2402_0_part5 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 640 128 = 658685924586092902776655990944 := by decide +kernel
private theorem receipt_0_16_2402_0_part6 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 768 128 = 607310943252102445551579963552 := by decide +kernel
private theorem receipt_0_16_2402_0_part7 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 896 128 = 557133172946145307551006322848 := by decide +kernel
private theorem receipt_0_16_2402_0_part8 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 1024 128 = 508138452960517320109372326048 := by decide +kernel
private theorem receipt_0_16_2402_0_part9 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 1152 128 = 460312639144952109128363380896 := by decide +kernel
private theorem receipt_0_16_2402_0_part10 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 1280 128 = 413641603900328414109290553504 := by decide +kernel
private theorem receipt_0_16_2402_0_part11 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 1408 128 = 368111236172377407185468076192 := by decide +kernel
private theorem receipt_0_16_2402_0_part12 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 1536 128 = 323707441445390012154590855328 := by decide +kernel
private theorem receipt_0_16_2402_0_part13 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 1664 128 = 280416141735924223511111979168 := by decide +kernel
private theorem receipt_0_16_2402_0_part14 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 1792 128 = 238223288624306645966217685062 := by decide +kernel
private theorem receipt_0_16_2402_0_part15 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 1920 128 = 197114887054445857903324978545 := by decide +kernel
private theorem receipt_0_16_2402_0_part16 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 2048 128 = 157076883836495063602544954697 := by decide +kernel
private theorem receipt_0_16_2402_0_part17 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 2176 128 = 118095218027900931746574311490 := by decide +kernel
private theorem receipt_0_16_2402_0_part18 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 2304 128 = 80155845230270335108851279807 := by decide +kernel
private theorem receipt_0_16_2402_0_part19 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 2432 128 = 43244737599604473380640572709 := by decide +kernel
private theorem receipt_0_16_2402_0_part20 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 2560 90 = 8853503849179641309100129269 := by decide +kernel
private theorem receipt_0_16_2402_0_join0 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 0 256 = 1810457535478898543465856127296 :=
  phaseBlock_append receipt_0_16_2402_0_part0 receipt_0_16_2402_0_part1 rfl rfl rfl
private theorem receipt_0_16_2402_0_join1 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 384 256 = 1476356540213486831631209673024 :=
  phaseBlock_append receipt_0_16_2402_0_part3 receipt_0_16_2402_0_part4 rfl rfl rfl
private theorem receipt_0_16_2402_0_join2 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 256 384 = 2296492530540505926914530087392 :=
  phaseBlock_append receipt_0_16_2402_0_part2 receipt_0_16_2402_0_join1 rfl rfl rfl
private theorem receipt_0_16_2402_0_join3 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 0 640 = 4106950066019404470380386214688 :=
  phaseBlock_append receipt_0_16_2402_0_join0 receipt_0_16_2402_0_join2 rfl rfl rfl
private theorem receipt_0_16_2402_0_join4 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 640 256 = 1265996867838195348328235954496 :=
  phaseBlock_append receipt_0_16_2402_0_part5 receipt_0_16_2402_0_part6 rfl rfl rfl
private theorem receipt_0_16_2402_0_join5 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 1024 256 = 968451092105469429237735706944 :=
  phaseBlock_append receipt_0_16_2402_0_part8 receipt_0_16_2402_0_part9 rfl rfl rfl
private theorem receipt_0_16_2402_0_join6 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 896 384 = 1525584265051614736788742029792 :=
  phaseBlock_append receipt_0_16_2402_0_part7 receipt_0_16_2402_0_join5 rfl rfl rfl
private theorem receipt_0_16_2402_0_join7 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 640 640 = 2791581132889810085116977984288 :=
  phaseBlock_append receipt_0_16_2402_0_join4 receipt_0_16_2402_0_join6 rfl rfl rfl
private theorem receipt_0_16_2402_0_join8 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 0 1280 = 6898531198909214555497364198976 :=
  phaseBlock_append receipt_0_16_2402_0_join3 receipt_0_16_2402_0_join7 rfl rfl rfl
private theorem receipt_0_16_2402_0_join9 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 1280 256 = 781752840072705821294758629696 :=
  phaseBlock_append receipt_0_16_2402_0_part10 receipt_0_16_2402_0_part11 rfl rfl rfl
private theorem receipt_0_16_2402_0_join10 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 1664 256 = 518639430360230869477329664230 :=
  phaseBlock_append receipt_0_16_2402_0_part13 receipt_0_16_2402_0_part14 rfl rfl rfl
private theorem receipt_0_16_2402_0_join11 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 1536 384 = 842346871805620881631920519558 :=
  phaseBlock_append receipt_0_16_2402_0_part12 receipt_0_16_2402_0_join10 rfl rfl rfl
private theorem receipt_0_16_2402_0_join12 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 1280 640 = 1624099711878326702926679149254 :=
  phaseBlock_append receipt_0_16_2402_0_join9 receipt_0_16_2402_0_join11 rfl rfl rfl
private theorem receipt_0_16_2402_0_join13 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 2048 256 = 275172101864395995349119266187 :=
  phaseBlock_append receipt_0_16_2402_0_part16 receipt_0_16_2402_0_part17 rfl rfl rfl
private theorem receipt_0_16_2402_0_join14 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 1920 384 = 472286988918841853252444244732 :=
  phaseBlock_append receipt_0_16_2402_0_part15 receipt_0_16_2402_0_join13 rfl rfl rfl
private theorem receipt_0_16_2402_0_join15 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 2432 218 = 52098241448784114689740701978 :=
  phaseBlock_append receipt_0_16_2402_0_part19 receipt_0_16_2402_0_part20 rfl rfl rfl
private theorem receipt_0_16_2402_0_join16 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 2304 346 = 132254086679054449798591981785 :=
  phaseBlock_append receipt_0_16_2402_0_part18 receipt_0_16_2402_0_join15 rfl rfl rfl
private theorem receipt_0_16_2402_0_join17 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 1920 730 = 604541075597896303051036226517 :=
  phaseBlock_append receipt_0_16_2402_0_join14 receipt_0_16_2402_0_join16 rfl rfl rfl
private theorem receipt_0_16_2402_0_join18 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 1280 1370 = 2228640787476223005977715375771 :=
  phaseBlock_append receipt_0_16_2402_0_join12 receipt_0_16_2402_0_join17 rfl rfl rfl
private theorem receipt_0_16_2402_0_join19 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 0) 0 2650 = 9127171986385437561475079574747 :=
  phaseBlock_append receipt_0_16_2402_0_join8 receipt_0_16_2402_0_join18 rfl rfl rfl

private theorem receipt_0_16_2402_0 : fastPhase (bank 0 16).shape 179798 2402 103 1 0 1 0 = 9127171986385437561475079574747 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_0_16_2402_0_join19

private theorem receipt_0_16_2402_1_part0 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 0 128 = 933567132209864495921147754528 := by decide +kernel
private theorem receipt_0_16_2402_1_part1 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 128 128 = 876002731952841728177387653152 := by decide +kernel
private theorem receipt_0_16_2402_1_part2 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 256 128 = 819706487144142108404758632480 := by decide +kernel
private theorem receipt_0_16_2402_1_part3 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 384 128 = 764664154320865039727900747808 := by decide +kernel
private theorem receipt_0_16_2402_1_part4 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 512 128 = 710861506608962953491853834272 := by decide +kernel
private theorem receipt_0_16_2402_1_part5 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 640 128 = 658284333716948628294435014688 := by decide +kernel
private theorem receipt_0_16_2402_1_part6 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 768 128 = 606918441929602509018616207392 := by decide +kernel
private theorem receipt_0_16_2402_1_part7 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 896 128 = 556749654101680025864901634080 := by decide +kernel
private theorem receipt_0_16_2402_1_part8 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 1024 128 = 507763809651618913383705327648 := by decide +kernel
private theorem receipt_0_16_2402_1_part9 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 1152 128 = 459946764555246529507728640032 := by decide +kernel
private theorem receipt_0_16_2402_1_part10 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 1280 128 = 413284391339487174584337750048 := by decide +kernel
private theorem receipt_0_16_2402_1_part11 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 1408 128 = 367762579076069410407941171232 := by decide +kernel
private theorem receipt_0_16_2402_1_part12 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 1536 128 = 323367233375233379252367259680 := by decide +kernel
private theorem receipt_0_16_2402_1_part13 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 1664 128 = 280084276379438122903241721888 := by decide +kernel
private theorem receipt_0_16_2402_1_part14 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 1792 128 = 237899659777642598599750541907 := by decide +kernel
private theorem receipt_0_16_2402_1_part15 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 1920 128 = 196799388554450039658516540721 := by decide +kernel
private theorem receipt_0_16_2402_1_part16 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 2048 128 = 156769409620472059603394431590 := by decide +kernel
private theorem receipt_0_16_2402_1_part17 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 2176 128 = 117795662159080445864521375035 := by decide +kernel
private theorem receipt_0_16_2402_1_part18 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 2304 128 = 79864101897780089931659282484 := by decide +kernel
private theorem receipt_0_16_2402_1_part19 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 2432 128 = 42960701118433629080151546876 := by decide +kernel
private theorem receipt_0_16_2402_1_part20 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 2560 90 = 8658348258694991947687233870 := by decide +kernel
private theorem receipt_0_16_2402_1_join0 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 0 256 = 1809569864162706224098535407680 :=
  phaseBlock_append receipt_0_16_2402_1_part0 receipt_0_16_2402_1_part1 rfl rfl rfl
private theorem receipt_0_16_2402_1_join1 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 384 256 = 1475525660929827993219754582080 :=
  phaseBlock_append receipt_0_16_2402_1_part3 receipt_0_16_2402_1_part4 rfl rfl rfl
private theorem receipt_0_16_2402_1_join2 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 256 384 = 2295232148073970101624513214560 :=
  phaseBlock_append receipt_0_16_2402_1_part2 receipt_0_16_2402_1_join1 rfl rfl rfl
private theorem receipt_0_16_2402_1_join3 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 0 640 = 4104802012236676325723048622240 :=
  phaseBlock_append receipt_0_16_2402_1_join0 receipt_0_16_2402_1_join2 rfl rfl rfl
private theorem receipt_0_16_2402_1_join4 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 640 256 = 1265202775646551137313051222080 :=
  phaseBlock_append receipt_0_16_2402_1_part5 receipt_0_16_2402_1_part6 rfl rfl rfl
private theorem receipt_0_16_2402_1_join5 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 1024 256 = 967710574206865442891433967680 :=
  phaseBlock_append receipt_0_16_2402_1_part8 receipt_0_16_2402_1_part9 rfl rfl rfl
private theorem receipt_0_16_2402_1_join6 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 896 384 = 1524460228308545468756335601760 :=
  phaseBlock_append receipt_0_16_2402_1_part7 receipt_0_16_2402_1_join5 rfl rfl rfl
private theorem receipt_0_16_2402_1_join7 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 640 640 = 2789663003955096606069386823840 :=
  phaseBlock_append receipt_0_16_2402_1_join4 receipt_0_16_2402_1_join6 rfl rfl rfl
private theorem receipt_0_16_2402_1_join8 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 0 1280 = 6894465016191772931792435446080 :=
  phaseBlock_append receipt_0_16_2402_1_join3 receipt_0_16_2402_1_join7 rfl rfl rfl
private theorem receipt_0_16_2402_1_join9 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 1280 256 = 781046970415556584992278921280 :=
  phaseBlock_append receipt_0_16_2402_1_part10 receipt_0_16_2402_1_part11 rfl rfl rfl
private theorem receipt_0_16_2402_1_join10 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 1664 256 = 517983936157080721502992263795 :=
  phaseBlock_append receipt_0_16_2402_1_part13 receipt_0_16_2402_1_part14 rfl rfl rfl
private theorem receipt_0_16_2402_1_join11 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 1536 384 = 841351169532314100755359523475 :=
  phaseBlock_append receipt_0_16_2402_1_part12 receipt_0_16_2402_1_join10 rfl rfl rfl
private theorem receipt_0_16_2402_1_join12 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 1280 640 = 1622398139947870685747638444755 :=
  phaseBlock_append receipt_0_16_2402_1_join9 receipt_0_16_2402_1_join11 rfl rfl rfl
private theorem receipt_0_16_2402_1_join13 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 2048 256 = 274565071779552505467915806625 :=
  phaseBlock_append receipt_0_16_2402_1_part16 receipt_0_16_2402_1_part17 rfl rfl rfl
private theorem receipt_0_16_2402_1_join14 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 1920 384 = 471364460334002545126432347346 :=
  phaseBlock_append receipt_0_16_2402_1_part15 receipt_0_16_2402_1_join13 rfl rfl rfl
private theorem receipt_0_16_2402_1_join15 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 2432 218 = 51619049377128621027838780746 :=
  phaseBlock_append receipt_0_16_2402_1_part19 receipt_0_16_2402_1_part20 rfl rfl rfl
private theorem receipt_0_16_2402_1_join16 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 2304 346 = 131483151274908710959498063230 :=
  phaseBlock_append receipt_0_16_2402_1_part18 receipt_0_16_2402_1_join15 rfl rfl rfl
private theorem receipt_0_16_2402_1_join17 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 1920 730 = 602847611608911256085930410576 :=
  phaseBlock_append receipt_0_16_2402_1_join14 receipt_0_16_2402_1_join16 rfl rfl rfl
private theorem receipt_0_16_2402_1_join18 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 1280 1370 = 2225245751556781941833568855331 :=
  phaseBlock_append receipt_0_16_2402_1_join12 receipt_0_16_2402_1_join17 rfl rfl rfl
private theorem receipt_0_16_2402_1_join19 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2402 103 1 0 1 1) 0 2650 = 9119710767748554873626004301411 :=
  phaseBlock_append receipt_0_16_2402_1_join8 receipt_0_16_2402_1_join18 rfl rfl rfl

private theorem receipt_0_16_2402_1 : fastPhase (bank 0 16).shape 179798 2402 103 1 0 1 1 = 9119710767748554873626004301411 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_0_16_2402_1_join19

private theorem receipt_0_16_2403_0_part0 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 0 128 = 934024195334942422992515976704 := by decide +kernel
private theorem receipt_0_16_2403_0_part1 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 128 128 = 876449437863323923775545953792 := by decide +kernel
private theorem receipt_0_16_2403_0_part2 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 256 128 = 820142979206319060422542315008 := by decide +kernel
private theorem receipt_0_16_2403_0_part3 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 384 128 = 765090575284388561198780927488 := by decide +kernel
private theorem receipt_0_16_2403_0_part4 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 512 128 = 711277998607471797524956663296 := by decide +kernel
private theorem receipt_0_16_2403_0_part5 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 640 128 = 658691038268693883107235352064 := by decide +kernel
private theorem receipt_0_16_2403_0_part6 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 768 128 = 607315499938072773067305733632 := by decide +kernel
private theorem receipt_0_16_2403_0_part7 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 896 128 = 557137205856226363072431410688 := by decide +kernel
private theorem receipt_0_16_2403_0_part8 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 1024 128 = 508141994828079588465502801408 := by decide +kernel
private theorem receipt_0_16_2403_0_part9 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 1152 128 = 460315722216571523395089092096 := by decide +kernel
private theorem receipt_0_16_2403_0_part10 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 1280 128 = 413644259936362479945490189824 := by decide +kernel
private theorem receipt_0_16_2403_0_part11 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 1408 128 = 368113496447541107266788675072 := by decide +kernel
private theorem receipt_0_16_2403_0_part12 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 1536 128 = 323709336749331490704901754368 := by decide +kernel
private theorem receipt_0_16_2403_0_part13 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 1664 128 = 280417702373800250931633212928 := by decide +kernel
private theorem receipt_0_16_2403_0_part14 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 1792 128 = 238224543828844375164768069905 := by decide +kernel
private theorem receipt_0_16_2403_0_part15 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 1920 128 = 197115865692209202272838451638 := by decide +kernel
private theorem receipt_0_16_2403_0_part16 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 2048 128 = 157077615271953678827800212894 := by decide +kernel
private theorem receipt_0_16_2403_0_part17 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 2176 128 = 118095731091289047567504350785 := by decide +kernel
private theorem receipt_0_16_2403_0_part18 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 2304 128 = 80156168228839551554178179966 := by decide +kernel
private theorem receipt_0_16_2403_0_part19 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 2432 128 = 43244898317108739253546366416 := by decide +kernel
private theorem receipt_0_16_2403_0_part20 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 2560 90 = 8853534418802162363029951125 := by decide +kernel
private theorem receipt_0_16_2403_0_join0 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 0 256 = 1810473633198266346768061930496 :=
  phaseBlock_append receipt_0_16_2403_0_part0 receipt_0_16_2403_0_part1 rfl rfl rfl
private theorem receipt_0_16_2403_0_join1 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 384 256 = 1476368573891860358723737590784 :=
  phaseBlock_append receipt_0_16_2403_0_part3 receipt_0_16_2403_0_part4 rfl rfl rfl
private theorem receipt_0_16_2403_0_join2 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 256 384 = 2296511553098179419146279905792 :=
  phaseBlock_append receipt_0_16_2403_0_part2 receipt_0_16_2403_0_join1 rfl rfl rfl
private theorem receipt_0_16_2403_0_join3 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 0 640 = 4106985186296445765914341836288 :=
  phaseBlock_append receipt_0_16_2403_0_join0 receipt_0_16_2403_0_join2 rfl rfl rfl
private theorem receipt_0_16_2403_0_join4 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 640 256 = 1266006538206766656174541085696 :=
  phaseBlock_append receipt_0_16_2403_0_part5 receipt_0_16_2403_0_part6 rfl rfl rfl
private theorem receipt_0_16_2403_0_join5 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 1024 256 = 968457717044651111860591893504 :=
  phaseBlock_append receipt_0_16_2403_0_part8 receipt_0_16_2403_0_part9 rfl rfl rfl
private theorem receipt_0_16_2403_0_join6 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 896 384 = 1525594922900877474933023304192 :=
  phaseBlock_append receipt_0_16_2403_0_part7 receipt_0_16_2403_0_join5 rfl rfl rfl
private theorem receipt_0_16_2403_0_join7 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 640 640 = 2791601461107644131107564389888 :=
  phaseBlock_append receipt_0_16_2403_0_join4 receipt_0_16_2403_0_join6 rfl rfl rfl
private theorem receipt_0_16_2403_0_join8 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 0 1280 = 6898586647404089897021906226176 :=
  phaseBlock_append receipt_0_16_2403_0_join3 receipt_0_16_2403_0_join7 rfl rfl rfl
private theorem receipt_0_16_2403_0_join9 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 1280 256 = 781757756383903587212278864896 :=
  phaseBlock_append receipt_0_16_2403_0_part10 receipt_0_16_2403_0_part11 rfl rfl rfl
private theorem receipt_0_16_2403_0_join10 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 1664 256 = 518642246202644626096401282833 :=
  phaseBlock_append receipt_0_16_2403_0_part13 receipt_0_16_2403_0_part14 rfl rfl rfl
private theorem receipt_0_16_2403_0_join11 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 1536 384 = 842351582951976116801303037201 :=
  phaseBlock_append receipt_0_16_2403_0_part12 receipt_0_16_2403_0_join10 rfl rfl rfl
private theorem receipt_0_16_2403_0_join12 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 1280 640 = 1624109339335879704013581902097 :=
  phaseBlock_append receipt_0_16_2403_0_join9 receipt_0_16_2403_0_join11 rfl rfl rfl
private theorem receipt_0_16_2403_0_join13 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 2048 256 = 275173346363242726395304563679 :=
  phaseBlock_append receipt_0_16_2403_0_part16 receipt_0_16_2403_0_part17 rfl rfl rfl
private theorem receipt_0_16_2403_0_join14 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 1920 384 = 472289212055451928668143015317 :=
  phaseBlock_append receipt_0_16_2403_0_part15 receipt_0_16_2403_0_join13 rfl rfl rfl
private theorem receipt_0_16_2403_0_join15 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 2432 218 = 52098432735910901616576317541 :=
  phaseBlock_append receipt_0_16_2403_0_part19 receipt_0_16_2403_0_part20 rfl rfl rfl
private theorem receipt_0_16_2403_0_join16 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 2304 346 = 132254600964750453170754497507 :=
  phaseBlock_append receipt_0_16_2403_0_part18 receipt_0_16_2403_0_join15 rfl rfl rfl
private theorem receipt_0_16_2403_0_join17 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 1920 730 = 604543813020202381838897512824 :=
  phaseBlock_append receipt_0_16_2403_0_join14 receipt_0_16_2403_0_join16 rfl rfl rfl
private theorem receipt_0_16_2403_0_join18 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 1280 1370 = 2228653152356082085852479414921 :=
  phaseBlock_append receipt_0_16_2403_0_join12 receipt_0_16_2403_0_join17 rfl rfl rfl
private theorem receipt_0_16_2403_0_join19 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 0) 0 2650 = 9127239799760171982874385641097 :=
  phaseBlock_append receipt_0_16_2403_0_join8 receipt_0_16_2403_0_join18 rfl rfl rfl

private theorem receipt_0_16_2403_0 : fastPhase (bank 0 16).shape 179798 2403 103 1 0 1 0 = 9127239799760171982874385641097 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_0_16_2403_0_join19

private theorem receipt_0_16_2403_1_part0 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 0 128 = 933575542978727687741743468928 := by decide +kernel
private theorem receipt_0_16_2403_1_part1 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 128 128 = 876010412430956895495341199744 := by decide +kernel
private theorem receipt_0_16_2403_1_part2 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 256 128 = 819713472995441974696312639872 := by decide +kernel
private theorem receipt_0_16_2403_1_part3 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 384 128 = 764670480719029574998769422720 := by decide +kernel
private theorem receipt_0_16_2403_1_part4 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 512 128 = 710867208237996816721611297152 := by decide +kernel
private theorem receipt_0_16_2403_1_part5 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 640 128 = 658289444771758389978578080128 := by decide +kernel
private theorem receipt_0_16_2403_1_part6 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 768 128 = 606922996116573653808301609344 := by decide +kernel
private theorem receipt_0_16_2403_1_part7 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 896 128 = 556753684639253735304357695872 := by decide +kernel
private theorem receipt_0_16_2403_1_part8 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 1024 128 = 507767349270868628745318076800 := by decide +kernel
private theorem receipt_0_16_2403_1_part9 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 1152 128 = 459949845500454294724802367872 := by decide +kernel
private theorem receipt_0_16_2403_1_part10 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 1280 128 = 413287045368719759281530016128 := by decide +kernel
private theorem receipt_0_16_2403_1_part11 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 1408 128 = 367764837461754213029372252544 := by decide +kernel
private theorem receipt_0_16_2403_1_part12 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 1536 128 = 323369126904734110287404044672 := by decide +kernel
private theorem receipt_0_16_2403_1_part13 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 1664 128 = 280085835355630268209956049280 := by decide +kernel
private theorem receipt_0_16_2403_1_part14 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 1792 128 = 237900913431741738338795113419 := by decide +kernel
private theorem receipt_0_16_2403_1_part15 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 1920 128 = 196800365751716650743963690924 := by decide +kernel
private theorem receipt_0_16_2403_1_part16 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 2048 128 = 156770139722982186477541444480 := by decide +kernel
private theorem receipt_0_16_2403_1_part17 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 2176 128 = 117796173994690523606026149054 := by decide +kernel
private theorem receipt_0_16_2403_1_part18 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 2304 128 = 79864423771367267738395208432 := by decide +kernel
private theorem receipt_0_16_2403_1_part19 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 2432 128 = 42960860811392045398040231751 := by decide +kernel
private theorem receipt_0_16_2403_1_part20 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 2560 90 = 8658378166785791261748279342 := by decide +kernel
private theorem receipt_0_16_2403_1_join0 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 0 256 = 1809585955409684583237084668672 :=
  phaseBlock_append receipt_0_16_2403_1_part0 receipt_0_16_2403_1_part1 rfl rfl rfl
private theorem receipt_0_16_2403_1_join1 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 384 256 = 1475537688957026391720380719872 :=
  phaseBlock_append receipt_0_16_2403_1_part3 receipt_0_16_2403_1_part4 rfl rfl rfl
private theorem receipt_0_16_2403_1_join2 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 256 384 = 2295251161952468366416693359744 :=
  phaseBlock_append receipt_0_16_2403_1_part2 receipt_0_16_2403_1_join1 rfl rfl rfl
private theorem receipt_0_16_2403_1_join3 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 0 640 = 4104837117362152949653778028416 :=
  phaseBlock_append receipt_0_16_2403_1_join0 receipt_0_16_2403_1_join2 rfl rfl rfl
private theorem receipt_0_16_2403_1_join4 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 640 256 = 1265212440888332043786879689472 :=
  phaseBlock_append receipt_0_16_2403_1_part5 receipt_0_16_2403_1_part6 rfl rfl rfl
private theorem receipt_0_16_2403_1_join5 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 1024 256 = 967717194771322923470120444672 :=
  phaseBlock_append receipt_0_16_2403_1_part8 receipt_0_16_2403_1_part9 rfl rfl rfl
private theorem receipt_0_16_2403_1_join6 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 896 384 = 1524470879410576658774478140544 :=
  phaseBlock_append receipt_0_16_2403_1_part7 receipt_0_16_2403_1_join5 rfl rfl rfl
private theorem receipt_0_16_2403_1_join7 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 640 640 = 2789683320298908702561357830016 :=
  phaseBlock_append receipt_0_16_2403_1_join4 receipt_0_16_2403_1_join6 rfl rfl rfl
private theorem receipt_0_16_2403_1_join8 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 0 1280 = 6894520437661061652215135858432 :=
  phaseBlock_append receipt_0_16_2403_1_join3 receipt_0_16_2403_1_join7 rfl rfl rfl
private theorem receipt_0_16_2403_1_join9 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 1280 256 = 781051882830473972310902268672 :=
  phaseBlock_append receipt_0_16_2403_1_part10 receipt_0_16_2403_1_part11 rfl rfl rfl
private theorem receipt_0_16_2403_1_join10 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 1664 256 = 517986748787372006548751162699 :=
  phaseBlock_append receipt_0_16_2403_1_part13 receipt_0_16_2403_1_part14 rfl rfl rfl
private theorem receipt_0_16_2403_1_join11 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 1536 384 = 841355875692106116836155207371 :=
  phaseBlock_append receipt_0_16_2403_1_part12 receipt_0_16_2403_1_join10 rfl rfl rfl
private theorem receipt_0_16_2403_1_join12 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 1280 640 = 1622407758522580089147057476043 :=
  phaseBlock_append receipt_0_16_2403_1_join9 receipt_0_16_2403_1_join11 rfl rfl rfl
private theorem receipt_0_16_2403_1_join13 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 2048 256 = 274566313717672710083567593534 :=
  phaseBlock_append receipt_0_16_2403_1_part16 receipt_0_16_2403_1_part17 rfl rfl rfl
private theorem receipt_0_16_2403_1_join14 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 1920 384 = 471366679469389360827531284458 :=
  phaseBlock_append receipt_0_16_2403_1_part15 receipt_0_16_2403_1_join13 rfl rfl rfl
private theorem receipt_0_16_2403_1_join15 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 2432 218 = 51619238978177836659788511093 :=
  phaseBlock_append receipt_0_16_2403_1_part19 receipt_0_16_2403_1_part20 rfl rfl rfl
private theorem receipt_0_16_2403_1_join16 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 2304 346 = 131483662749545104398183719525 :=
  phaseBlock_append receipt_0_16_2403_1_part18 receipt_0_16_2403_1_join15 rfl rfl rfl
private theorem receipt_0_16_2403_1_join17 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 1920 730 = 602850342218934465225715003983 :=
  phaseBlock_append receipt_0_16_2403_1_join14 receipt_0_16_2403_1_join16 rfl rfl rfl
private theorem receipt_0_16_2403_1_join18 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 1280 1370 = 2225258100741514554372772480026 :=
  phaseBlock_append receipt_0_16_2403_1_join12 receipt_0_16_2403_1_join17 rfl rfl rfl
private theorem receipt_0_16_2403_1_join19 :
    phaseBlock (fastLayer (bank 0 16).shape 179798 2403 103 1 0 1 1) 0 2650 = 9119778538402576206587908338458 :=
  phaseBlock_append receipt_0_16_2403_1_join8 receipt_0_16_2403_1_join18 rfl rfl rfl

private theorem receipt_0_16_2403_1 : fastPhase (bank 0 16).shape 179798 2403 103 1 0 1 1 = 9119778538402576206587908338458 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_0_16_2403_1_join19

theorem receipt_0_16 : Checked (bank 0 16) 103 0 1 := by
  refine checked_from_values (bank 0 16) 103 0 1
    (P3_7_1.checked (bank 0 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_12604_2649)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_16_2402_0 receipt_0_16_2402_1 receipt_0_16_2403_0 receipt_0_16_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_16_2402_0_part0 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 0 128 = 840918568296144004759270594720 := by decide +kernel
private theorem receipt_1_16_2402_0_part1 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 128 128 = 788812288341794895320126785696 := by decide +kernel
private theorem receipt_1_16_2402_0_part2 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 256 128 = 737882635881560315383198251168 := by decide +kernel
private theorem receipt_1_16_2402_0_part3 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 384 128 = 688115631079302737292621047968 := by decide +kernel
private theorem receipt_1_16_2402_0_part4 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 512 128 = 639497326308573690288115931296 := by decide +kernel
private theorem receipt_1_16_2402_0_part5 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 640 128 = 592013806127443036634498386080 := by decide +kernel
private theorem receipt_1_16_2402_0_part6 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 768 128 = 545651187253328247751188658336 := by decide +kernel
private theorem receipt_1_16_2402_0_part7 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 896 128 = 500395618537823680341721786528 := by decide +kernel
private theorem receipt_1_16_2402_0_part8 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 1024 128 = 456233280941529852523257632928 := by decide +kernel
private theorem receipt_1_16_2402_0_part9 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 1152 128 = 413150387508882719956090914976 := by decide +kernel
private theorem receipt_1_16_2402_0_part10 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 1280 128 = 371133183342982951973161236640 := by decide +kernel
private theorem receipt_1_16_2402_0_part11 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 1408 128 = 330167945580425207709563119776 := by decide +kernel
private theorem receipt_1_16_2402_0_part12 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 1536 128 = 290240983366127412232056035488 := by decide +kernel
private theorem receipt_1_16_2402_0_part13 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 1664 128 = 251338637828160032668574435488 := by decide +kernel
private theorem receipt_1_16_2402_0_part14 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 1792 128 = 213447293733271690274082299842 := by decide +kernel
private theorem receipt_1_16_2402_0_part15 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 1920 128 = 176553400766882587633230965962 := by decide +kernel
private theorem receipt_1_16_2402_0_part16 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 2048 128 = 140643373624534275274087769579 := by decide +kernel
private theorem receipt_1_16_2402_0_part17 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 2176 128 = 105703637199040235355370056363 := by decide +kernel
private theorem receipt_1_16_2402_0_part18 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 2304 128 = 71720648340063269826312357601 := by decide +kernel
private theorem receipt_1_16_2402_0_part19 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 2432 128 = 38680895843683746795447782918 := by decide +kernel
private theorem receipt_1_16_2402_0_part20 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 2560 90 = 7916937365354574875665332615 := by decide +kernel
private theorem receipt_1_16_2402_0_join0 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 0 256 = 1629730856637938900079397380416 :=
  phaseBlock_append receipt_1_16_2402_0_part0 receipt_1_16_2402_0_part1 rfl rfl rfl
private theorem receipt_1_16_2402_0_join1 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 384 256 = 1327612957387876427580736979264 :=
  phaseBlock_append receipt_1_16_2402_0_part3 receipt_1_16_2402_0_part4 rfl rfl rfl
private theorem receipt_1_16_2402_0_join2 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 256 384 = 2065495593269436742963935230432 :=
  phaseBlock_append receipt_1_16_2402_0_part2 receipt_1_16_2402_0_join1 rfl rfl rfl
private theorem receipt_1_16_2402_0_join3 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 0 640 = 3695226449907375643043332610848 :=
  phaseBlock_append receipt_1_16_2402_0_join0 receipt_1_16_2402_0_join2 rfl rfl rfl
private theorem receipt_1_16_2402_0_join4 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 640 256 = 1137664993380771284385687044416 :=
  phaseBlock_append receipt_1_16_2402_0_part5 receipt_1_16_2402_0_part6 rfl rfl rfl
private theorem receipt_1_16_2402_0_join5 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 1024 256 = 869383668450412572479348547904 :=
  phaseBlock_append receipt_1_16_2402_0_part8 receipt_1_16_2402_0_part9 rfl rfl rfl
private theorem receipt_1_16_2402_0_join6 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 896 384 = 1369779286988236252821070334432 :=
  phaseBlock_append receipt_1_16_2402_0_part7 receipt_1_16_2402_0_join5 rfl rfl rfl
private theorem receipt_1_16_2402_0_join7 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 640 640 = 2507444280369007537206757378848 :=
  phaseBlock_append receipt_1_16_2402_0_join4 receipt_1_16_2402_0_join6 rfl rfl rfl
private theorem receipt_1_16_2402_0_join8 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 0 1280 = 6202670730276383180250089989696 :=
  phaseBlock_append receipt_1_16_2402_0_join3 receipt_1_16_2402_0_join7 rfl rfl rfl
private theorem receipt_1_16_2402_0_join9 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 1280 256 = 701301128923408159682724356416 :=
  phaseBlock_append receipt_1_16_2402_0_part10 receipt_1_16_2402_0_part11 rfl rfl rfl
private theorem receipt_1_16_2402_0_join10 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 1664 256 = 464785931561431722942656735330 :=
  phaseBlock_append receipt_1_16_2402_0_part13 receipt_1_16_2402_0_part14 rfl rfl rfl
private theorem receipt_1_16_2402_0_join11 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 1536 384 = 755026914927559135174712770818 :=
  phaseBlock_append receipt_1_16_2402_0_part12 receipt_1_16_2402_0_join10 rfl rfl rfl
private theorem receipt_1_16_2402_0_join12 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 1280 640 = 1456328043850967294857437127234 :=
  phaseBlock_append receipt_1_16_2402_0_join9 receipt_1_16_2402_0_join11 rfl rfl rfl
private theorem receipt_1_16_2402_0_join13 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 2048 256 = 246347010823574510629457825942 :=
  phaseBlock_append receipt_1_16_2402_0_part16 receipt_1_16_2402_0_part17 rfl rfl rfl
private theorem receipt_1_16_2402_0_join14 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 1920 384 = 422900411590457098262688791904 :=
  phaseBlock_append receipt_1_16_2402_0_part15 receipt_1_16_2402_0_join13 rfl rfl rfl
private theorem receipt_1_16_2402_0_join15 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 2432 218 = 46597833209038321671113115533 :=
  phaseBlock_append receipt_1_16_2402_0_part19 receipt_1_16_2402_0_part20 rfl rfl rfl
private theorem receipt_1_16_2402_0_join16 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 2304 346 = 118318481549101591497425473134 :=
  phaseBlock_append receipt_1_16_2402_0_part18 receipt_1_16_2402_0_join15 rfl rfl rfl
private theorem receipt_1_16_2402_0_join17 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 1920 730 = 541218893139558689760114265038 :=
  phaseBlock_append receipt_1_16_2402_0_join14 receipt_1_16_2402_0_join16 rfl rfl rfl
private theorem receipt_1_16_2402_0_join18 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 1280 1370 = 1997546936990525984617551392272 :=
  phaseBlock_append receipt_1_16_2402_0_join12 receipt_1_16_2402_0_join17 rfl rfl rfl
private theorem receipt_1_16_2402_0_join19 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 0) 0 2650 = 8200217667266909164867641381968 :=
  phaseBlock_append receipt_1_16_2402_0_join8 receipt_1_16_2402_0_join18 rfl rfl rfl

private theorem receipt_1_16_2402_0 : fastPhase (bank 1 16).shape 179798 2402 103 1 0 2 0 = 8200217667266909164867641381968 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_1_16_2402_0_join19

private theorem receipt_1_16_2402_1_part0 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 0 128 = 840512383778841655935182484000 := by decide +kernel
private theorem receipt_1_16_2402_1_part1 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 128 128 = 788415045509140491140406960672 := by decide +kernel
private theorem receipt_1_16_2402_1_part2 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 256 128 = 737494228876176395213205475872 := by decide +kernel
private theorem receipt_1_16_2402_1_part3 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 384 128 = 687735954289295557056816890400 := by decide +kernel
private theorem receipt_1_16_2402_1_part4 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 512 128 = 639126274367340537730221437472 := by decide +kernel
private theorem receipt_1_16_2402_1_part5 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 640 128 = 591651273913479546577650754080 := by decide +kernel
private theorem receipt_1_16_2402_1_part6 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 768 128 = 545297069890035717358097912352 := by decide +kernel
private theorem receipt_1_16_2402_1_part7 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 896 128 = 500049811393316384374827450912 := by decide +kernel
private theorem receipt_1_16_2402_1_part8 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 1024 128 = 455895679628442358604885406240 := by decide +kernel
private theorem receipt_1_16_2402_1_part9 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 1152 128 = 412820887884177203828609344032 := by decide +kernel
private theorem receipt_1_16_2402_1_part10 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 1280 128 = 370811681507756512759138390560 := by decide +kernel
private theorem receipt_1_16_2402_1_part11 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 1408 128 = 329854337879717183171923264032 := by decide +kernel
private theorem receipt_1_16_2402_1_part12 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 1536 128 = 289935166388726694034236305952 := by decide +kernel
private theorem receipt_1_16_2402_1_part13 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 1664 128 = 251040508406412381634681512480 := by decide +kernel
private theorem receipt_1_16_2402_1_part14 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 1792 128 = 213156748927427523876784971642 := by decide +kernel
private theorem receipt_1_16_2402_1_part15 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 1920 128 = 176270337804028148556712416852 := by decide +kernel
private theorem receipt_1_16_2402_1_part16 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 2048 128 = 140367689952236546409727986414 := by decide +kernel
private theorem receipt_1_16_2402_1_part17 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 2176 128 = 105435230508083627667424963236 := by decide +kernel
private theorem receipt_1_16_2402_1_part18 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 2304 128 = 71459416564275518781769234413 := by decide +kernel
private theorem receipt_1_16_2402_1_part19 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 2432 128 = 38426737159753250434761167656 := by decide +kernel
private theorem receipt_1_16_2402_1_part20 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 2560 90 = 7742412276246118432712322955 := by decide +kernel
private theorem receipt_1_16_2402_1_join0 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 0 256 = 1628927429287982147075589444672 :=
  phaseBlock_append receipt_1_16_2402_1_part0 receipt_1_16_2402_1_part1 rfl rfl rfl
private theorem receipt_1_16_2402_1_join1 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 384 256 = 1326862228656636094787038327872 :=
  phaseBlock_append receipt_1_16_2402_1_part3 receipt_1_16_2402_1_part4 rfl rfl rfl
private theorem receipt_1_16_2402_1_join2 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 256 384 = 2064356457532812490000243803744 :=
  phaseBlock_append receipt_1_16_2402_1_part2 receipt_1_16_2402_1_join1 rfl rfl rfl
private theorem receipt_1_16_2402_1_join3 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 0 640 = 3693283886820794637075833248416 :=
  phaseBlock_append receipt_1_16_2402_1_join0 receipt_1_16_2402_1_join2 rfl rfl rfl
private theorem receipt_1_16_2402_1_join4 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 640 256 = 1136948343803515263935748666432 :=
  phaseBlock_append receipt_1_16_2402_1_part5 receipt_1_16_2402_1_part6 rfl rfl rfl
private theorem receipt_1_16_2402_1_join5 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 1024 256 = 868716567512619562433494750272 :=
  phaseBlock_append receipt_1_16_2402_1_part8 receipt_1_16_2402_1_part9 rfl rfl rfl
private theorem receipt_1_16_2402_1_join6 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 896 384 = 1368766378905935946808322201184 :=
  phaseBlock_append receipt_1_16_2402_1_part7 receipt_1_16_2402_1_join5 rfl rfl rfl
private theorem receipt_1_16_2402_1_join7 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 640 640 = 2505714722709451210744070867616 :=
  phaseBlock_append receipt_1_16_2402_1_join4 receipt_1_16_2402_1_join6 rfl rfl rfl
private theorem receipt_1_16_2402_1_join8 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 0 1280 = 6198998609530245847819904116032 :=
  phaseBlock_append receipt_1_16_2402_1_join3 receipt_1_16_2402_1_join7 rfl rfl rfl
private theorem receipt_1_16_2402_1_join9 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 1280 256 = 700666019387473695931061654592 :=
  phaseBlock_append receipt_1_16_2402_1_part10 receipt_1_16_2402_1_part11 rfl rfl rfl
private theorem receipt_1_16_2402_1_join10 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 1664 256 = 464197257333839905511466484122 :=
  phaseBlock_append receipt_1_16_2402_1_part13 receipt_1_16_2402_1_part14 rfl rfl rfl
private theorem receipt_1_16_2402_1_join11 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 1536 384 = 754132423722566599545702790074 :=
  phaseBlock_append receipt_1_16_2402_1_part12 receipt_1_16_2402_1_join10 rfl rfl rfl
private theorem receipt_1_16_2402_1_join12 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 1280 640 = 1454798443110040295476764444666 :=
  phaseBlock_append receipt_1_16_2402_1_join9 receipt_1_16_2402_1_join11 rfl rfl rfl
private theorem receipt_1_16_2402_1_join13 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 2048 256 = 245802920460320174077152949650 :=
  phaseBlock_append receipt_1_16_2402_1_part16 receipt_1_16_2402_1_part17 rfl rfl rfl
private theorem receipt_1_16_2402_1_join14 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 1920 384 = 422073258264348322633865366502 :=
  phaseBlock_append receipt_1_16_2402_1_part15 receipt_1_16_2402_1_join13 rfl rfl rfl
private theorem receipt_1_16_2402_1_join15 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 2432 218 = 46169149435999368867473490611 :=
  phaseBlock_append receipt_1_16_2402_1_part19 receipt_1_16_2402_1_part20 rfl rfl rfl
private theorem receipt_1_16_2402_1_join16 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 2304 346 = 117628566000274887649242725024 :=
  phaseBlock_append receipt_1_16_2402_1_part18 receipt_1_16_2402_1_join15 rfl rfl rfl
private theorem receipt_1_16_2402_1_join17 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 1920 730 = 539701824264623210283108091526 :=
  phaseBlock_append receipt_1_16_2402_1_join14 receipt_1_16_2402_1_join16 rfl rfl rfl
private theorem receipt_1_16_2402_1_join18 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 1280 1370 = 1994500267374663505759872536192 :=
  phaseBlock_append receipt_1_16_2402_1_join12 receipt_1_16_2402_1_join17 rfl rfl rfl
private theorem receipt_1_16_2402_1_join19 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2402 103 1 0 2 1) 0 2650 = 8193498876904909353579776652224 :=
  phaseBlock_append receipt_1_16_2402_1_join8 receipt_1_16_2402_1_join18 rfl rfl rfl

private theorem receipt_1_16_2402_1 : fastPhase (bank 1 16).shape 179798 2402 103 1 0 2 1 = 8193498876904909353579776652224 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_1_16_2402_1_join19

private theorem receipt_1_16_2403_0_part0 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 0 128 = 840926143711491318811238242560 := by decide +kernel
private theorem receipt_1_16_2403_0_part1 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 128 128 = 788819203755973587516388055296 := by decide +kernel
private theorem receipt_1_16_2403_0_part2 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 256 128 = 737888923835049315363581499648 := by decide +kernel
private theorem receipt_1_16_2403_0_part3 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 384 128 = 688121323638652058315875981568 := by decide +kernel
private theorem receipt_1_16_2403_0_part4 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 512 128 = 639502455067520950304571300096 := by decide +kernel
private theorem receipt_1_16_2403_0_part5 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 640 128 = 592018402208029099749417457920 := by decide +kernel
private theorem receipt_1_16_2403_0_part6 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 768 128 = 545655281307011986078822471936 := by decide +kernel
private theorem receipt_1_16_2403_0_part7 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 896 128 = 500399240746595856250060183808 := by decide +kernel
private theorem receipt_1_16_2403_0_part8 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 1024 128 = 456236461019026121269478070528 := by decide +kernel
private theorem receipt_1_16_2403_0_part9 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 1152 128 = 413153154701495752712705054976 := by decide +kernel
private theorem receipt_1_16_2403_0_part10 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 1280 128 = 371135566430973679244859316480 := by decide +kernel
private theorem receipt_1_16_2403_0_part11 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 1408 128 = 330169972879033183140756101376 := by decide +kernel
private theorem receipt_1_16_2403_0_part12 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 1536 128 = 290242682726680296805115533568 := by decide +kernel
private theorem receipt_1_16_2403_0_part13 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 1664 128 = 251340036639182199292770425088 := by decide +kernel
private theorem receipt_1_16_2403_0_part14 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 1792 128 = 213448418394321724291723317654 := by decide +kernel
private theorem receipt_1_16_2403_0_part15 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 1920 128 = 176554277322351730333117705225 := by decide +kernel
private theorem receipt_1_16_2403_0_part16 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 2048 128 = 140644028537883882627033532384 := by decide +kernel
private theorem receipt_1_16_2403_0_part17 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 2176 128 = 105704096428297185663587118824 := by decide +kernel
private theorem receipt_1_16_2403_0_part18 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 2304 128 = 71720937348544731495744309849 := by decide +kernel
private theorem receipt_1_16_2403_0_part19 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 2432 128 = 38681039600177568883466646751 := by decide +kernel
private theorem receipt_1_16_2403_0_part20 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 2560 90 = 7916964701199565741641168658 := by decide +kernel
private theorem receipt_1_16_2403_0_join0 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 0 256 = 1629745347467464906327626297856 :=
  phaseBlock_append receipt_1_16_2403_0_part0 receipt_1_16_2403_0_part1 rfl rfl rfl
private theorem receipt_1_16_2403_0_join1 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 384 256 = 1327623778706173008620447281664 :=
  phaseBlock_append receipt_1_16_2403_0_part3 receipt_1_16_2403_0_part4 rfl rfl rfl
private theorem receipt_1_16_2403_0_join2 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 256 384 = 2065512702541222323984028781312 :=
  phaseBlock_append receipt_1_16_2403_0_part2 receipt_1_16_2403_0_join1 rfl rfl rfl
private theorem receipt_1_16_2403_0_join3 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 0 640 = 3695258050008687230311655079168 :=
  phaseBlock_append receipt_1_16_2403_0_join0 receipt_1_16_2403_0_join2 rfl rfl rfl
private theorem receipt_1_16_2403_0_join4 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 640 256 = 1137673683515041085828239929856 :=
  phaseBlock_append receipt_1_16_2403_0_part5 receipt_1_16_2403_0_part6 rfl rfl rfl
private theorem receipt_1_16_2403_0_join5 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 1024 256 = 869389615720521873982183125504 :=
  phaseBlock_append receipt_1_16_2403_0_part8 receipt_1_16_2403_0_part9 rfl rfl rfl
private theorem receipt_1_16_2403_0_join6 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 896 384 = 1369788856467117730232243309312 :=
  phaseBlock_append receipt_1_16_2403_0_part7 receipt_1_16_2403_0_join5 rfl rfl rfl
private theorem receipt_1_16_2403_0_join7 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 640 640 = 2507462539982158816060483239168 :=
  phaseBlock_append receipt_1_16_2403_0_join4 receipt_1_16_2403_0_join6 rfl rfl rfl
private theorem receipt_1_16_2403_0_join8 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 0 1280 = 6202720589990846046372138318336 :=
  phaseBlock_append receipt_1_16_2403_0_join3 receipt_1_16_2403_0_join7 rfl rfl rfl
private theorem receipt_1_16_2403_0_join9 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 1280 256 = 701305539310006862385615417856 :=
  phaseBlock_append receipt_1_16_2403_0_part10 receipt_1_16_2403_0_part11 rfl rfl rfl
private theorem receipt_1_16_2403_0_join10 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 1664 256 = 464788455033503923584493742742 :=
  phaseBlock_append receipt_1_16_2403_0_part13 receipt_1_16_2403_0_part14 rfl rfl rfl
private theorem receipt_1_16_2403_0_join11 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 1536 384 = 755031137760184220389609276310 :=
  phaseBlock_append receipt_1_16_2403_0_part12 receipt_1_16_2403_0_join10 rfl rfl rfl
private theorem receipt_1_16_2403_0_join12 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 1280 640 = 1456336677070191082775224694166 :=
  phaseBlock_append receipt_1_16_2403_0_join9 receipt_1_16_2403_0_join11 rfl rfl rfl
private theorem receipt_1_16_2403_0_join13 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 2048 256 = 246348124966181068290620651208 :=
  phaseBlock_append receipt_1_16_2403_0_part16 receipt_1_16_2403_0_part17 rfl rfl rfl
private theorem receipt_1_16_2403_0_join14 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 1920 384 = 422902402288532798623738356433 :=
  phaseBlock_append receipt_1_16_2403_0_part15 receipt_1_16_2403_0_join13 rfl rfl rfl
private theorem receipt_1_16_2403_0_join15 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 2432 218 = 46598004301377134625107815409 :=
  phaseBlock_append receipt_1_16_2403_0_part19 receipt_1_16_2403_0_part20 rfl rfl rfl
private theorem receipt_1_16_2403_0_join16 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 2304 346 = 118318941649921866120852125258 :=
  phaseBlock_append receipt_1_16_2403_0_part18 receipt_1_16_2403_0_join15 rfl rfl rfl
private theorem receipt_1_16_2403_0_join17 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 1920 730 = 541221343938454664744590481691 :=
  phaseBlock_append receipt_1_16_2403_0_join14 receipt_1_16_2403_0_join16 rfl rfl rfl
private theorem receipt_1_16_2403_0_join18 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 1280 1370 = 1997558021008645747519815175857 :=
  phaseBlock_append receipt_1_16_2403_0_join12 receipt_1_16_2403_0_join17 rfl rfl rfl
private theorem receipt_1_16_2403_0_join19 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 0) 0 2650 = 8200278610999491793891953494193 :=
  phaseBlock_append receipt_1_16_2403_0_join8 receipt_1_16_2403_0_join18 rfl rfl rfl

private theorem receipt_1_16_2403_0 : fastPhase (bank 1 16).shape 179798 2403 103 1 0 2 0 = 8200278610999491793891953494193 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_1_16_2403_0_join19

private theorem receipt_1_16_2403_1_part0 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 0 128 = 840519956197072051556789528256 := by decide +kernel
private theorem receipt_1_16_2403_1_part1 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 128 128 = 788421958055294136518774113984 := by decide +kernel
private theorem receipt_1_16_2403_1_part2 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 256 128 = 737500514088476192202986383040 := by decide +kernel
private theorem receipt_1_16_2403_1_part3 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 384 128 = 687741644232041614516389447360 := by decide +kernel
private theorem receipt_1_16_2403_1_part4 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 512 128 = 639131400632026687371665254080 := by decide +kernel
private theorem receipt_1_16_2403_1_part5 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 640 128 = 591655867619908979207422396096 := by decide +kernel
private theorem receipt_1_16_2403_1_part6 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 768 128 = 545301161687435739508403922624 := by decide +kernel
private theorem receipt_1_16_2403_1_part7 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 896 128 = 500053431461452295325695149760 := by decide +kernel
private theorem receipt_1_16_2403_1_part8 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 1024 128 = 455898857678730447796931471040 := by decide +kernel
private theorem receipt_1_16_2403_1_part9 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 1152 128 = 412823653160796868666506168000 := by decide +kernel
private theorem receipt_1_16_2403_1_part10 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 1280 128 = 370814062788761496805778220736 := by decide +kernel
private theorem receipt_1_16_2403_1_part11 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 1408 128 = 329856363478145934733280118464 := by decide +kernel
private theorem receipt_1_16_2403_1_part12 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 1536 128 = 289936864153711845134925670080 := by decide +kernel
private theorem receipt_1_16_2403_1_part13 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 1664 128 = 251041905724289347384217814720 := by decide +kernel
private theorem receipt_1_16_2403_1_part14 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 1792 128 = 213157872196260210179552505649 := by decide +kernel
private theorem receipt_1_16_2403_1_part15 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 1920 128 = 176271213066901880352138213808 := by decide +kernel
private theorem receipt_1_16_2403_1_part16 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 2048 128 = 140368343670330568217691782404 := by decide +kernel
private theorem receipt_1_16_2403_1_part17 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 2176 128 = 105435688637160339674437221976 := by decide +kernel
private theorem receipt_1_16_2403_1_part18 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 2304 128 = 71459704565394037140873320640 := by decide +kernel
private theorem receipt_1_16_2403_1_part19 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 2432 128 = 38426879999459898569224962064 := by decide +kernel
private theorem receipt_1_16_2403_1_part20 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 2560 90 = 7742439020489958262331512307 := by decide +kernel
private theorem receipt_1_16_2403_1_join0 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 0 256 = 1628941914252366188075563642240 :=
  phaseBlock_append receipt_1_16_2403_1_part0 receipt_1_16_2403_1_part1 rfl rfl rfl
private theorem receipt_1_16_2403_1_join1 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 384 256 = 1326873044864068301888054701440 :=
  phaseBlock_append receipt_1_16_2403_1_part3 receipt_1_16_2403_1_part4 rfl rfl rfl
private theorem receipt_1_16_2403_1_join2 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 256 384 = 2064373558952544494091041084480 :=
  phaseBlock_append receipt_1_16_2403_1_part2 receipt_1_16_2403_1_join1 rfl rfl rfl
private theorem receipt_1_16_2403_1_join3 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 0 640 = 3693315473204910682166604726720 :=
  phaseBlock_append receipt_1_16_2403_1_join0 receipt_1_16_2403_1_join2 rfl rfl rfl
private theorem receipt_1_16_2403_1_join4 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 640 256 = 1136957029307344718715826318720 :=
  phaseBlock_append receipt_1_16_2403_1_part5 receipt_1_16_2403_1_part6 rfl rfl rfl
private theorem receipt_1_16_2403_1_join5 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 1024 256 = 868722510839527316463437639040 :=
  phaseBlock_append receipt_1_16_2403_1_part8 receipt_1_16_2403_1_part9 rfl rfl rfl
private theorem receipt_1_16_2403_1_join6 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 896 384 = 1368775942300979611789132788800 :=
  phaseBlock_append receipt_1_16_2403_1_part7 receipt_1_16_2403_1_join5 rfl rfl rfl
private theorem receipt_1_16_2403_1_join7 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 640 640 = 2505732971608324330504959107520 :=
  phaseBlock_append receipt_1_16_2403_1_join4 receipt_1_16_2403_1_join6 rfl rfl rfl
private theorem receipt_1_16_2403_1_join8 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 0 1280 = 6199048444813235012671563834240 :=
  phaseBlock_append receipt_1_16_2403_1_join3 receipt_1_16_2403_1_join7 rfl rfl rfl
private theorem receipt_1_16_2403_1_join9 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 1280 256 = 700670426266907431539058339200 :=
  phaseBlock_append receipt_1_16_2403_1_part10 receipt_1_16_2403_1_part11 rfl rfl rfl
private theorem receipt_1_16_2403_1_join10 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 1664 256 = 464199777920549557563770320369 :=
  phaseBlock_append receipt_1_16_2403_1_part13 receipt_1_16_2403_1_part14 rfl rfl rfl
private theorem receipt_1_16_2403_1_join11 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 1536 384 = 754136642074261402698695990449 :=
  phaseBlock_append receipt_1_16_2403_1_part12 receipt_1_16_2403_1_join10 rfl rfl rfl
private theorem receipt_1_16_2403_1_join12 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 1280 640 = 1454807068341168834237754329649 :=
  phaseBlock_append receipt_1_16_2403_1_join9 receipt_1_16_2403_1_join11 rfl rfl rfl
private theorem receipt_1_16_2403_1_join13 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 2048 256 = 245804032307490907892129004380 :=
  phaseBlock_append receipt_1_16_2403_1_part16 receipt_1_16_2403_1_part17 rfl rfl rfl
private theorem receipt_1_16_2403_1_join14 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 1920 384 = 422075245374392788244267218188 :=
  phaseBlock_append receipt_1_16_2403_1_part15 receipt_1_16_2403_1_join13 rfl rfl rfl
private theorem receipt_1_16_2403_1_join15 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 2432 218 = 46169319019949856831556474371 :=
  phaseBlock_append receipt_1_16_2403_1_part19 receipt_1_16_2403_1_part20 rfl rfl rfl
private theorem receipt_1_16_2403_1_join16 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 2304 346 = 117629023585343893972429795011 :=
  phaseBlock_append receipt_1_16_2403_1_part18 receipt_1_16_2403_1_join15 rfl rfl rfl
private theorem receipt_1_16_2403_1_join17 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 1920 730 = 539704268959736682216697013199 :=
  phaseBlock_append receipt_1_16_2403_1_join14 receipt_1_16_2403_1_join16 rfl rfl rfl
private theorem receipt_1_16_2403_1_join18 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 1280 1370 = 1994511337300905516454451342848 :=
  phaseBlock_append receipt_1_16_2403_1_join12 receipt_1_16_2403_1_join17 rfl rfl rfl
private theorem receipt_1_16_2403_1_join19 :
    phaseBlock (fastLayer (bank 1 16).shape 179798 2403 103 1 0 2 1) 0 2650 = 8193559782114140529126015177088 :=
  phaseBlock_append receipt_1_16_2403_1_join8 receipt_1_16_2403_1_join18 rfl rfl rfl

private theorem receipt_1_16_2403_1 : fastPhase (bank 1 16).shape 179798 2403 103 1 0 2 1 = 8193559782114140529126015177088 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_1_16_2403_1_join19

theorem receipt_1_16 : Checked (bank 1 16) 103 0 2 := by
  refine checked_from_values (bank 1 16) 103 0 2
    (P3_7_1.checked (bank 1 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_12604_2649)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_16_2402_0 receipt_1_16_2402_1 receipt_1_16_2403_0 receipt_1_16_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_16_2402_0_part0 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 0 128 = 451358338494916189073247121440 := by decide +kernel
private theorem receipt_2_16_2402_0_part1 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 128 128 = 422346314060241577662281826336 := by decide +kernel
private theorem receipt_2_16_2402_0_part2 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 256 128 = 394101276358477363826539319328 := by decide +kernel
private theorem receipt_2_16_2402_0_part3 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 384 128 = 366610989827896294738654683168 := by decide +kernel
private theorem receipt_2_16_2402_0_part4 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 512 128 = 339863314929267096770213146656 := by decide +kernel
private theorem receipt_2_16_2402_0_part5 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 640 128 = 313846207837513108078247968800 := by decide +kernel
private theorem receipt_2_16_2402_0_part6 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 768 128 = 288547720133370911191738322976 := by decide +kernel
private theorem receipt_2_16_2402_0_part7 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 896 128 = 263955998495048965598107181088 := by decide +kernel
private theorem receipt_2_16_2402_0_part8 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 1024 128 = 240059284389886240329719197728 := by decide +kernel
private theorem receipt_2_16_2402_0_part9 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 1152 128 = 216845913766010846550378594336 := by decide +kernel
private theorem receipt_2_16_2402_0_part10 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 1280 128 = 194304316743998670141827043360 := by decide +kernel
private theorem receipt_2_16_2402_0_part11 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 1408 128 = 172423017308532004290241552416 := by decide +kernel
private theorem receipt_2_16_2402_0_part12 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 1536 128 = 151190633000058182072732348448 := by decide +kernel
private theorem receipt_2_16_2402_0_part13 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 1664 128 = 130595874606448209043840761888 := by decide +kernel
private theorem receipt_2_16_2402_0_part14 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 1792 128 = 110627551904366486397701248422 := by decide +kernel
private theorem receipt_2_16_2402_0_part15 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 1920 128 = 91274584298160453870350786097 := by decide +kernel
private theorem receipt_2_16_2402_0_part16 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 2048 128 = 72525948789746553640915037909 := by decide +kernel
private theorem receipt_2_16_2402_0_part17 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 2176 128 = 54370703351623588692380677118 := by decide +kernel
private theorem receipt_2_16_2402_0_part18 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 2304 128 = 36797997943486633586643534411 := by decide +kernel
private theorem receipt_2_16_2402_0_part19 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 2432 128 = 19797074210431128185850633813 := by decide +kernel
private theorem receipt_2_16_2402_0_part20 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 2560 90 = 4043579241705614828548945105 := by decide +kernel
private theorem receipt_2_16_2402_0_join0 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 0 256 = 873704652555157766735528947776 :=
  phaseBlock_append receipt_2_16_2402_0_part0 receipt_2_16_2402_0_part1 rfl rfl rfl
private theorem receipt_2_16_2402_0_join1 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 384 256 = 706474304757163391508867829824 :=
  phaseBlock_append receipt_2_16_2402_0_part3 receipt_2_16_2402_0_part4 rfl rfl rfl
private theorem receipt_2_16_2402_0_join2 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 256 384 = 1100575581115640755335407149152 :=
  phaseBlock_append receipt_2_16_2402_0_part2 receipt_2_16_2402_0_join1 rfl rfl rfl
private theorem receipt_2_16_2402_0_join3 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 0 640 = 1974280233670798522070936096928 :=
  phaseBlock_append receipt_2_16_2402_0_join0 receipt_2_16_2402_0_join2 rfl rfl rfl
private theorem receipt_2_16_2402_0_join4 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 640 256 = 602393927970884019269986291776 :=
  phaseBlock_append receipt_2_16_2402_0_part5 receipt_2_16_2402_0_part6 rfl rfl rfl
private theorem receipt_2_16_2402_0_join5 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 1024 256 = 456905198155897086880097792064 :=
  phaseBlock_append receipt_2_16_2402_0_part8 receipt_2_16_2402_0_part9 rfl rfl rfl
private theorem receipt_2_16_2402_0_join6 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 896 384 = 720861196650946052478204973152 :=
  phaseBlock_append receipt_2_16_2402_0_part7 receipt_2_16_2402_0_join5 rfl rfl rfl
private theorem receipt_2_16_2402_0_join7 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 640 640 = 1323255124621830071748191264928 :=
  phaseBlock_append receipt_2_16_2402_0_join4 receipt_2_16_2402_0_join6 rfl rfl rfl
private theorem receipt_2_16_2402_0_join8 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 0 1280 = 3297535358292628593819127361856 :=
  phaseBlock_append receipt_2_16_2402_0_join3 receipt_2_16_2402_0_join7 rfl rfl rfl
private theorem receipt_2_16_2402_0_join9 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 1280 256 = 366727334052530674432068595776 :=
  phaseBlock_append receipt_2_16_2402_0_part10 receipt_2_16_2402_0_part11 rfl rfl rfl
private theorem receipt_2_16_2402_0_join10 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 1664 256 = 241223426510814695441542010310 :=
  phaseBlock_append receipt_2_16_2402_0_part13 receipt_2_16_2402_0_part14 rfl rfl rfl
private theorem receipt_2_16_2402_0_join11 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 1536 384 = 392414059510872877514274358758 :=
  phaseBlock_append receipt_2_16_2402_0_part12 receipt_2_16_2402_0_join10 rfl rfl rfl
private theorem receipt_2_16_2402_0_join12 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 1280 640 = 759141393563403551946342954534 :=
  phaseBlock_append receipt_2_16_2402_0_join9 receipt_2_16_2402_0_join11 rfl rfl rfl
private theorem receipt_2_16_2402_0_join13 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 2048 256 = 126896652141370142333295715027 :=
  phaseBlock_append receipt_2_16_2402_0_part16 receipt_2_16_2402_0_part17 rfl rfl rfl
private theorem receipt_2_16_2402_0_join14 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 1920 384 = 218171236439530596203646501124 :=
  phaseBlock_append receipt_2_16_2402_0_part15 receipt_2_16_2402_0_join13 rfl rfl rfl
private theorem receipt_2_16_2402_0_join15 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 2432 218 = 23840653452136743014399578918 :=
  phaseBlock_append receipt_2_16_2402_0_part19 receipt_2_16_2402_0_part20 rfl rfl rfl
private theorem receipt_2_16_2402_0_join16 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 2304 346 = 60638651395623376601043113329 :=
  phaseBlock_append receipt_2_16_2402_0_part18 receipt_2_16_2402_0_join15 rfl rfl rfl
private theorem receipt_2_16_2402_0_join17 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 1920 730 = 278809887835153972804689614453 :=
  phaseBlock_append receipt_2_16_2402_0_join14 receipt_2_16_2402_0_join16 rfl rfl rfl
private theorem receipt_2_16_2402_0_join18 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 1280 1370 = 1037951281398557524751032568987 :=
  phaseBlock_append receipt_2_16_2402_0_join12 receipt_2_16_2402_0_join17 rfl rfl rfl
private theorem receipt_2_16_2402_0_join19 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 0) 0 2650 = 4335486639691186118570159930843 :=
  phaseBlock_append receipt_2_16_2402_0_join8 receipt_2_16_2402_0_join18 rfl rfl rfl

private theorem receipt_2_16_2402_0 : fastPhase (bank 2 16).shape 179798 2402 103 1 0 7 0 = 4335486639691186118570159930843 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_2_16_2402_0_join19

private theorem receipt_2_16_2402_1_part0 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 0 128 = 451131625551690991757075764640 := by decide +kernel
private theorem receipt_2_16_2402_1_part1 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 128 128 = 422125470308991845926559098272 := by decide +kernel
private theorem receipt_2_16_2402_1_part2 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 256 128 = 393886208508631828653710570912 := by decide +kernel
private theorem receipt_2_16_2402_1_part3 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 384 128 = 366401605322401115166695015840 := by decide +kernel
private theorem receipt_2_16_2402_1_part4 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 512 128 = 339659521942225471829546669472 := by decide +kernel
private theorem receipt_2_16_2402_1_part5 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 640 128 = 313647915271824888728667055520 := by decide +kernel
private theorem receipt_2_16_2402_1_part6 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 768 128 = 288354837618372212259322869152 := by decide +kernel
private theorem receipt_2_16_2402_1_part7 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 896 128 = 263768436384151777712143861152 := by decide +kernel
private theorem receipt_2_16_2402_1_part8 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 1024 128 = 239876953758218041859620722080 := by decide +kernel
private theorem receipt_2_16_2402_1_part9 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 1152 128 = 216668726408054215542602966432 := by decide +kernel
private theorem receipt_2_16_2402_1_part10 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 1280 128 = 194132185171230896256796816800 := by decide +kernel
private theorem receipt_2_16_2402_1_part11 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 1408 128 = 172255854747064700739263088032 := by decide +kernel
private theorem receipt_2_16_2402_1_part12 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 1536 128 = 151028353388276897554915071392 := by decide +kernel
private theorem receipt_2_16_2402_1_part13 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 1664 128 = 130438392592652039683016418720 := by decide +kernel
private theorem receipt_2_16_2402_1_part14 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 1792 128 = 110474782836281245635421812427 := by decide +kernel
private theorem receipt_2_16_2402_1_part15 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 1920 128 = 91126444188847845598179498377 := by decide +kernel
private theorem receipt_2_16_2402_1_part16 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 2048 128 = 72382354344082962209135202934 := by decide +kernel
private theorem receipt_2_16_2402_1_part17 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 2176 128 = 54231571976079134935912635291 := by decide +kernel
private theorem receipt_2_16_2402_1_part18 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 2304 128 = 36663247743769386162036530048 := by decide +kernel
private theorem receipt_2_16_2402_1_part19 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 2432 128 = 19666623989126638688033836036 := by decide +kernel
private theorem receipt_2_16_2402_1_part20 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 2560 90 = 3954387603630949120983736570 := by decide +kernel
private theorem receipt_2_16_2402_1_join0 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 0 256 = 873257095860682837683634862912 :=
  phaseBlock_append receipt_2_16_2402_1_part0 receipt_2_16_2402_1_part1 rfl rfl rfl
private theorem receipt_2_16_2402_1_join1 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 384 256 = 706061127264626586996241685312 :=
  phaseBlock_append receipt_2_16_2402_1_part3 receipt_2_16_2402_1_part4 rfl rfl rfl
private theorem receipt_2_16_2402_1_join2 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 256 384 = 1099947335773258415649952256224 :=
  phaseBlock_append receipt_2_16_2402_1_part2 receipt_2_16_2402_1_join1 rfl rfl rfl
private theorem receipt_2_16_2402_1_join3 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 0 640 = 1973204431633941253333587119136 :=
  phaseBlock_append receipt_2_16_2402_1_join0 receipt_2_16_2402_1_join2 rfl rfl rfl
private theorem receipt_2_16_2402_1_join4 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 640 256 = 602002752890197100987989924672 :=
  phaseBlock_append receipt_2_16_2402_1_part5 receipt_2_16_2402_1_part6 rfl rfl rfl
private theorem receipt_2_16_2402_1_join5 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 1024 256 = 456545680166272257402223688512 :=
  phaseBlock_append receipt_2_16_2402_1_part8 receipt_2_16_2402_1_part9 rfl rfl rfl
private theorem receipt_2_16_2402_1_join6 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 896 384 = 720314116550424035114367549664 :=
  phaseBlock_append receipt_2_16_2402_1_part7 receipt_2_16_2402_1_join5 rfl rfl rfl
private theorem receipt_2_16_2402_1_join7 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 640 640 = 1322316869440621136102357474336 :=
  phaseBlock_append receipt_2_16_2402_1_join4 receipt_2_16_2402_1_join6 rfl rfl rfl
private theorem receipt_2_16_2402_1_join8 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 0 1280 = 3295521301074562389435944593472 :=
  phaseBlock_append receipt_2_16_2402_1_join3 receipt_2_16_2402_1_join7 rfl rfl rfl
private theorem receipt_2_16_2402_1_join9 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 1280 256 = 366388039918295596996059904832 :=
  phaseBlock_append receipt_2_16_2402_1_part10 receipt_2_16_2402_1_part11 rfl rfl rfl
private theorem receipt_2_16_2402_1_join10 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 1664 256 = 240913175428933285318438231147 :=
  phaseBlock_append receipt_2_16_2402_1_part13 receipt_2_16_2402_1_part14 rfl rfl rfl
private theorem receipt_2_16_2402_1_join11 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 1536 384 = 391941528817210182873353302539 :=
  phaseBlock_append receipt_2_16_2402_1_part12 receipt_2_16_2402_1_join10 rfl rfl rfl
private theorem receipt_2_16_2402_1_join12 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 1280 640 = 758329568735505779869413207371 :=
  phaseBlock_append receipt_2_16_2402_1_join9 receipt_2_16_2402_1_join11 rfl rfl rfl
private theorem receipt_2_16_2402_1_join13 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 2048 256 = 126613926320162097145047838225 :=
  phaseBlock_append receipt_2_16_2402_1_part16 receipt_2_16_2402_1_part17 rfl rfl rfl
private theorem receipt_2_16_2402_1_join14 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 1920 384 = 217740370509009942743227336602 :=
  phaseBlock_append receipt_2_16_2402_1_part15 receipt_2_16_2402_1_join13 rfl rfl rfl
private theorem receipt_2_16_2402_1_join15 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 2432 218 = 23621011592757587809017572606 :=
  phaseBlock_append receipt_2_16_2402_1_part19 receipt_2_16_2402_1_part20 rfl rfl rfl
private theorem receipt_2_16_2402_1_join16 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 2304 346 = 60284259336526973971054102654 :=
  phaseBlock_append receipt_2_16_2402_1_part18 receipt_2_16_2402_1_join15 rfl rfl rfl
private theorem receipt_2_16_2402_1_join17 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 1920 730 = 278024629845536916714281439256 :=
  phaseBlock_append receipt_2_16_2402_1_join14 receipt_2_16_2402_1_join16 rfl rfl rfl
private theorem receipt_2_16_2402_1_join18 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 1280 1370 = 1036354198581042696583694646627 :=
  phaseBlock_append receipt_2_16_2402_1_join12 receipt_2_16_2402_1_join17 rfl rfl rfl
private theorem receipt_2_16_2402_1_join19 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2402 103 1 0 7 1) 0 2650 = 4331875499655605086019639240099 :=
  phaseBlock_append receipt_2_16_2402_1_join8 receipt_2_16_2402_1_join18 rfl rfl rfl

private theorem receipt_2_16_2402_1 : fastPhase (bank 2 16).shape 179798 2402 103 1 0 7 1 = 4331875499655605086019639240099 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_2_16_2402_1_join19

private theorem receipt_2_16_2403_0_part0 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 0 128 = 451362404578996302199189562880 := by decide +kernel
private theorem receipt_2_16_2403_0_part1 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 128 128 = 422350016736327052183877019136 := by decide +kernel
private theorem receipt_2_16_2403_0_part2 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 256 128 = 394104634758859151853468804608 := by decide +kernel
private theorem receipt_2_16_2403_0_part3 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 384 128 = 366614022701743801928428512768 := by decide +kernel
private theorem receipt_2_16_2403_0_part4 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 512 128 = 339866040645872650960584992256 := by decide +kernel
private theorem receipt_2_16_2403_0_part5 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 640 128 = 313848644389525652705678026240 := by decide +kernel
private theorem receipt_2_16_2403_0_part6 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 768 128 = 288549885140018923495904011776 := by decide +kernel
private theorem receipt_2_16_2403_0_part7 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 896 128 = 263957909205352599612461639168 := by decide +kernel
private theorem receipt_2_16_2403_0_part8 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 1024 128 = 240060957685858694658097571328 := by decide +kernel
private theorem receipt_2_16_2403_0_part9 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 1152 128 = 216847366165848956929652123136 := by decide +kernel
private theorem receipt_2_16_2403_0_part10 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 1280 128 = 194305564405262726790604940800 := by decide +kernel
private theorem receipt_2_16_2403_0_part11 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 1408 128 = 172424076031314794043620681216 := by decide +kernel
private theorem receipt_2_16_2403_0_part12 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 1536 128 = 151191518230143255303094691328 := by decide +kernel
private theorem receipt_2_16_2403_0_part13 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 1664 128 = 130596601438457371367698687488 := by decide +kernel
private theorem receipt_2_16_2403_0_part14 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 1792 128 = 110628134811754354533088577649 := by decide +kernel
private theorem receipt_2_16_2403_0_part15 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 1920 128 = 91275037465755243738123916450 := by decide +kernel
private theorem receipt_2_16_2403_0_part16 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 2048 128 = 72526286515455355289815130894 := by decide +kernel
private theorem receipt_2_16_2403_0_part17 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 2176 128 = 54370939568667571894646364209 := by decide +kernel
private theorem receipt_2_16_2403_0_part18 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 2304 128 = 36798146228685318336183889194 := by decide +kernel
private theorem receipt_2_16_2403_0_part19 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 2432 128 = 19797147787011450560778677396 := by decide +kernel
private theorem receipt_2_16_2403_0_part20 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 2560 90 = 4043593203595168762783387013 := by decide +kernel
private theorem receipt_2_16_2403_0_join0 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 0 256 = 873712421315323354383066582016 :=
  phaseBlock_append receipt_2_16_2403_0_part0 receipt_2_16_2403_0_part1 rfl rfl rfl
private theorem receipt_2_16_2403_0_join1 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 384 256 = 706480063347616452889013505024 :=
  phaseBlock_append receipt_2_16_2403_0_part3 receipt_2_16_2403_0_part4 rfl rfl rfl
private theorem receipt_2_16_2403_0_join2 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 256 384 = 1100584698106475604742482309632 :=
  phaseBlock_append receipt_2_16_2403_0_part2 receipt_2_16_2403_0_join1 rfl rfl rfl
private theorem receipt_2_16_2403_0_join3 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 0 640 = 1974297119421798959125548891648 :=
  phaseBlock_append receipt_2_16_2403_0_join0 receipt_2_16_2403_0_join2 rfl rfl rfl
private theorem receipt_2_16_2403_0_join4 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 640 256 = 602398529529544576201582038016 :=
  phaseBlock_append receipt_2_16_2403_0_part5 receipt_2_16_2403_0_part6 rfl rfl rfl
private theorem receipt_2_16_2403_0_join5 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 1024 256 = 456908323851707651587749694464 :=
  phaseBlock_append receipt_2_16_2403_0_part8 receipt_2_16_2403_0_part9 rfl rfl rfl
private theorem receipt_2_16_2403_0_join6 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 896 384 = 720866233057060251200211333632 :=
  phaseBlock_append receipt_2_16_2403_0_part7 receipt_2_16_2403_0_join5 rfl rfl rfl
private theorem receipt_2_16_2403_0_join7 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 640 640 = 1323264762586604827401793371648 :=
  phaseBlock_append receipt_2_16_2403_0_join4 receipt_2_16_2403_0_join6 rfl rfl rfl
private theorem receipt_2_16_2403_0_join8 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 0 1280 = 3297561882008403786527342263296 :=
  phaseBlock_append receipt_2_16_2403_0_join3 receipt_2_16_2403_0_join7 rfl rfl rfl
private theorem receipt_2_16_2403_0_join9 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 1280 256 = 366729640436577520834225622016 :=
  phaseBlock_append receipt_2_16_2403_0_part10 receipt_2_16_2403_0_part11 rfl rfl rfl
private theorem receipt_2_16_2403_0_join10 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 1664 256 = 241224736250211725900787265137 :=
  phaseBlock_append receipt_2_16_2403_0_part13 receipt_2_16_2403_0_part14 rfl rfl rfl
private theorem receipt_2_16_2403_0_join11 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 1536 384 = 392416254480354981203881956465 :=
  phaseBlock_append receipt_2_16_2403_0_part12 receipt_2_16_2403_0_join10 rfl rfl rfl
private theorem receipt_2_16_2403_0_join12 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 1280 640 = 759145894916932502038107578481 :=
  phaseBlock_append receipt_2_16_2403_0_join9 receipt_2_16_2403_0_join11 rfl rfl rfl
private theorem receipt_2_16_2403_0_join13 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 2048 256 = 126897226084122927184461495103 :=
  phaseBlock_append receipt_2_16_2403_0_part16 receipt_2_16_2403_0_part17 rfl rfl rfl
private theorem receipt_2_16_2403_0_join14 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 1920 384 = 218172263549878170922585411553 :=
  phaseBlock_append receipt_2_16_2403_0_part15 receipt_2_16_2403_0_join13 rfl rfl rfl
private theorem receipt_2_16_2403_0_join15 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 2432 218 = 23840740990606619323562064409 :=
  phaseBlock_append receipt_2_16_2403_0_part19 receipt_2_16_2403_0_part20 rfl rfl rfl
private theorem receipt_2_16_2403_0_join16 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 2304 346 = 60638887219291937659745953603 :=
  phaseBlock_append receipt_2_16_2403_0_part18 receipt_2_16_2403_0_join15 rfl rfl rfl
private theorem receipt_2_16_2403_0_join17 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 1920 730 = 278811150769170108582331365156 :=
  phaseBlock_append receipt_2_16_2403_0_join14 receipt_2_16_2403_0_join16 rfl rfl rfl
private theorem receipt_2_16_2403_0_join18 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 1280 1370 = 1037957045686102610620438943637 :=
  phaseBlock_append receipt_2_16_2403_0_join12 receipt_2_16_2403_0_join17 rfl rfl rfl
private theorem receipt_2_16_2403_0_join19 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 0) 0 2650 = 4335518927694506397147781206933 :=
  phaseBlock_append receipt_2_16_2403_0_join8 receipt_2_16_2403_0_join18 rfl rfl rfl

private theorem receipt_2_16_2403_0 : fastPhase (bank 2 16).shape 179798 2403 103 1 0 7 0 = 4335518927694506397147781206933 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_2_16_2403_0_join19

private theorem receipt_2_16_2403_1_part0 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 0 128 = 451135689948733406688300382336 := by decide +kernel
private theorem receipt_2_16_2403_1_part1 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 128 128 = 422129171377995829693894752384 := by decide +kernel
private theorem receipt_2_16_2403_1_part2 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 256 128 = 393889565379995294032385390720 := by decide +kernel
private theorem receipt_2_16_2403_1_part3 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 384 128 = 366404636743418384942387525760 := by decide +kernel
private theorem receipt_2_16_2403_1_part4 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 512 128 = 339662246280331683452968056960 := by decide +kernel
private theorem receipt_2_16_2403_1_part5 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 640 128 = 313650350517829623756191234176 := by decide +kernel
private theorem receipt_2_16_2403_1_part6 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 768 128 = 288357001389682350579664337024 := by decide +kernel
private theorem receipt_2_16_2403_1_part7 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 896 128 = 263770345927983576559083354240 := by decide +kernel
private theorem receipt_2_16_2403_1_part8 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 1024 128 = 239878625954798439610778663040 := by decide +kernel
private theorem receipt_2_16_2403_1_part9 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 1152 128 = 216670177773811360304260708480 := by decide +kernel
private theorem receipt_2_16_2403_1_part10 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 1280 128 = 194133431861973899234765682816 := by decide +kernel
private theorem receipt_2_16_2403_1_part11 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 1408 128 = 172256912561152614395801204864 := by decide +kernel
private theorem receipt_2_16_2403_1_part12 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 1536 128 = 151029237769776918551691999360 := by decide +kernel
private theorem receipt_2_16_2403_1_part13 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 1664 128 = 130439118634486936610125576320 := by decide +kernel
private theorem receipt_2_16_2403_1_part14 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 1792 128 = 110475365010585762478595397759 := by decide +kernel
private theorem receipt_2_16_2403_1_part15 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 1920 128 = 91126896679238513889679038588 := by decide +kernel
private theorem receipt_2_16_2403_1_part16 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 2048 128 = 72382691446753205424942007424 := by decide +kernel
private theorem receipt_2_16_2403_1_part17 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 2176 128 = 54231807622560414082649188406 := by decide +kernel
private theorem receipt_2_16_2403_1_part18 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 2304 128 = 36663395509209491036369852480 := by decide +kernel
private theorem receipt_2_16_2403_1_part19 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 2432 128 = 19666697095103860147243680799 := by decide +kernel
private theorem receipt_2_16_2403_1_part20 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 2560 90 = 3954401263173198733266936002 := by decide +kernel
private theorem receipt_2_16_2403_1_join0 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 0 256 = 873264861326729236382195134720 :=
  phaseBlock_append receipt_2_16_2403_1_part0 receipt_2_16_2403_1_part1 rfl rfl rfl
private theorem receipt_2_16_2403_1_join1 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 384 256 = 706066883023750068395355582720 :=
  phaseBlock_append receipt_2_16_2403_1_part3 receipt_2_16_2403_1_part4 rfl rfl rfl
private theorem receipt_2_16_2403_1_join2 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 256 384 = 1099956448403745362427740973440 :=
  phaseBlock_append receipt_2_16_2403_1_part2 receipt_2_16_2403_1_join1 rfl rfl rfl
private theorem receipt_2_16_2403_1_join3 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 0 640 = 1973221309730474598809936108160 :=
  phaseBlock_append receipt_2_16_2403_1_join0 receipt_2_16_2403_1_join2 rfl rfl rfl
private theorem receipt_2_16_2403_1_join4 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 640 256 = 602007351907511974335855571200 :=
  phaseBlock_append receipt_2_16_2403_1_part5 receipt_2_16_2403_1_part6 rfl rfl rfl
private theorem receipt_2_16_2403_1_join5 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 1024 256 = 456548803728609799915039371520 :=
  phaseBlock_append receipt_2_16_2403_1_part8 receipt_2_16_2403_1_part9 rfl rfl rfl
private theorem receipt_2_16_2403_1_join6 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 896 384 = 720319149656593376474122725760 :=
  phaseBlock_append receipt_2_16_2403_1_part7 receipt_2_16_2403_1_join5 rfl rfl rfl
private theorem receipt_2_16_2403_1_join7 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 640 640 = 1322326501564105350809978296960 :=
  phaseBlock_append receipt_2_16_2403_1_join4 receipt_2_16_2403_1_join6 rfl rfl rfl
private theorem receipt_2_16_2403_1_join8 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 0 1280 = 3295547811294579949619914405120 :=
  phaseBlock_append receipt_2_16_2403_1_join3 receipt_2_16_2403_1_join7 rfl rfl rfl
private theorem receipt_2_16_2403_1_join9 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 1280 256 = 366390344423126513630566887680 :=
  phaseBlock_append receipt_2_16_2403_1_part10 receipt_2_16_2403_1_part11 rfl rfl rfl
private theorem receipt_2_16_2403_1_join10 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 1664 256 = 240914483645072699088720974079 :=
  phaseBlock_append receipt_2_16_2403_1_part13 receipt_2_16_2403_1_part14 rfl rfl rfl
private theorem receipt_2_16_2403_1_join11 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 1536 384 = 391943721414849617640412973439 :=
  phaseBlock_append receipt_2_16_2403_1_part12 receipt_2_16_2403_1_join10 rfl rfl rfl
private theorem receipt_2_16_2403_1_join12 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 1280 640 = 758334065837976131270979861119 :=
  phaseBlock_append receipt_2_16_2403_1_join9 receipt_2_16_2403_1_join11 rfl rfl rfl
private theorem receipt_2_16_2403_1_join13 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 2048 256 = 126614499069313619507591195830 :=
  phaseBlock_append receipt_2_16_2403_1_part16 receipt_2_16_2403_1_part17 rfl rfl rfl
private theorem receipt_2_16_2403_1_join14 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 1920 384 = 217741395748552133397270234418 :=
  phaseBlock_append receipt_2_16_2403_1_part15 receipt_2_16_2403_1_join13 rfl rfl rfl
private theorem receipt_2_16_2403_1_join15 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 2432 218 = 23621098358277058880510616801 :=
  phaseBlock_append receipt_2_16_2403_1_part19 receipt_2_16_2403_1_part20 rfl rfl rfl
private theorem receipt_2_16_2403_1_join16 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 2304 346 = 60284493867486549916880469281 :=
  phaseBlock_append receipt_2_16_2403_1_part18 receipt_2_16_2403_1_join15 rfl rfl rfl
private theorem receipt_2_16_2403_1_join17 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 1920 730 = 278025889616038683314150703699 :=
  phaseBlock_append receipt_2_16_2403_1_join14 receipt_2_16_2403_1_join16 rfl rfl rfl
private theorem receipt_2_16_2403_1_join18 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 1280 1370 = 1036359955454014814585130564818 :=
  phaseBlock_append receipt_2_16_2403_1_join12 receipt_2_16_2403_1_join17 rfl rfl rfl
private theorem receipt_2_16_2403_1_join19 :
    phaseBlock (fastLayer (bank 2 16).shape 179798 2403 103 1 0 7 1) 0 2650 = 4331907766748594764205044969938 :=
  phaseBlock_append receipt_2_16_2403_1_join8 receipt_2_16_2403_1_join18 rfl rfl rfl

private theorem receipt_2_16_2403_1 : fastPhase (bank 2 16).shape 179798 2403 103 1 0 7 1 = 4331907766748594764205044969938 :=
  phase_of_block (n := 2650) (by decide +kernel) receipt_2_16_2403_1_join19

theorem receipt_2_16 : Checked (bank 2 16) 103 0 7 := by
  refine checked_from_values (bank 2 16) 103 0 7
    (P3_7_1.checked (bank 2 16) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_12604_2649)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_16_2402_0 receipt_2_16_2402_1 receipt_2_16_2403_0 receipt_2_16_2403_1 (by decide +kernel) (by decide +kernel)

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
    (word : K1.I → K1_14.L) (lo : 2402 ≤ h) (hi : h ≤ 33619) (rect : Fin 4)
    (i : Fin 1) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group7_stage i)).shape
      (cutoff h rect (group7_stage i)), ¬ G∣Q :=
  (group7_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group7_avoids

end Lower6960.RescueSource
