import ProximityPrize.SubmissionLower.HighCore82258Source

set_option Elab.async false
set_option maxHeartbeats 9000000
set_option maxRecDepth 18000

namespace Lower6961.Lo.TerminalBank
open P1_7_1_3 (blockEstimate block_append momentEstimate)

private theorem p0 : blockEstimate 6285 1329 1329 128 = 2214444960 := by decide +kernel
private theorem p1 : blockEstimate 6285 1329 1457 128 = 15025115040 := by decide +kernel
private theorem p2 : blockEstimate 6285 1329 1585 128 = 39805280160 := by decide +kernel
private theorem p3 : blockEstimate 6285 1329 1713 128 = 75749633952 := by decide +kernel
private theorem p4 : blockEstimate 6285 1329 1841 128 = 122052870048 := by decide +kernel
private theorem p5 : blockEstimate 6285 1329 1969 128 = 177909682080 := by decide +kernel
private theorem p6 : blockEstimate 6285 1329 2097 128 = 242514763680 := by decide +kernel
private theorem p7 : blockEstimate 6285 1329 2225 128 = 315062808480 := by decide +kernel
private theorem p8 : blockEstimate 6285 1329 2353 128 = 394748510112 := by decide +kernel
private theorem p9 : blockEstimate 6285 1329 2481 128 = 480766562208 := by decide +kernel
private theorem p10 : blockEstimate 6285 1329 2609 128 = 571909300340 := by decide +kernel
private theorem p11 : blockEstimate 6285 1329 2737 128 = 661883373760 := by decide +kernel
private theorem p12 : blockEstimate 6285 1329 2865 128 = 746376890560 := by decide +kernel
private theorem p13 : blockEstimate 6285 1329 2993 128 = 825291983040 := by decide +kernel
private theorem p14 : blockEstimate 6285 1329 3121 128 = 898628651200 := by decide +kernel
private theorem p15 : blockEstimate 6285 1329 3249 128 = 966386895040 := by decide +kernel
private theorem p16 : blockEstimate 6285 1329 3377 128 = 1028566714560 := by decide +kernel
private theorem p17 : blockEstimate 6285 1329 3505 128 = 1085168109760 := by decide +kernel
private theorem p18 : blockEstimate 6285 1329 3633 128 = 1136191080640 := by decide +kernel
private theorem p19 : blockEstimate 6285 1329 3761 128 = 1181635627200 := by decide +kernel
private theorem p20 : blockEstimate 6285 1329 3889 128 = 1221501749440 := by decide +kernel
private theorem p21 : blockEstimate 6285 1329 4017 128 = 1255789447360 := by decide +kernel
private theorem p22 : blockEstimate 6285 1329 4145 128 = 1284498720960 := by decide +kernel
private theorem p23 : blockEstimate 6285 1329 4273 128 = 1307629570240 := by decide +kernel
private theorem p24 : blockEstimate 6285 1329 4401 128 = 1325181995200 := by decide +kernel
private theorem p25 : blockEstimate 6285 1329 4529 128 = 1337155995840 := by decide +kernel
private theorem p26 : blockEstimate 6285 1329 4657 128 = 1343551572160 := by decide +kernel
private theorem p27 : blockEstimate 6285 1329 4785 128 = 1344368724160 := by decide +kernel
private theorem p28 : blockEstimate 6285 1329 4913 128 = 1339607451840 := by decide +kernel
private theorem p29 : blockEstimate 6285 1329 5041 128 = 1329267755200 := by decide +kernel
private theorem p30 : blockEstimate 6285 1329 5169 128 = 1313349634240 := by decide +kernel
private theorem p31 : blockEstimate 6285 1329 5297 128 = 1291853088960 := by decide +kernel
private theorem p32 : blockEstimate 6285 1329 5425 128 = 1264778119360 := by decide +kernel
private theorem p33 : blockEstimate 6285 1329 5553 128 = 1232124725440 := by decide +kernel
private theorem p34 : blockEstimate 6285 1329 5681 128 = 1193892907200 := by decide +kernel
private theorem p35 : blockEstimate 6285 1329 5809 128 = 1150082664640 := by decide +kernel
private theorem p36 : blockEstimate 6285 1329 5937 128 = 1100693997760 := by decide +kernel
private theorem p37 : blockEstimate 6285 1329 6065 128 = 1045726906560 := by decide +kernel
private theorem p38 : blockEstimate 6285 1329 6193 128 = 985196231674 := by decide +kernel
private theorem p39 : blockEstimate 6285 1329 6321 128 = 920455840186 := by decide +kernel
private theorem p40 : blockEstimate 6285 1329 6449 128 = 854180662092 := by decide +kernel
private theorem p41 : blockEstimate 6285 1329 6577 128 = 787174623339 := by decide +kernel
private theorem p42 : blockEstimate 6285 1329 6705 128 = 719997427233 := by decide +kernel
private theorem p43 : blockEstimate 6285 1329 6833 128 = 653189401337 := by decide +kernel
private theorem p44 : blockEstimate 6285 1329 6961 128 = 587271497069 := by decide +kernel
private theorem p45 : blockEstimate 6285 1329 7089 128 = 522745290055 := by decide +kernel
private theorem p46 : blockEstimate 6285 1329 7217 128 = 460092980144 := by decide +kernel
private theorem p47 : blockEstimate 6285 1329 7345 128 = 399777391540 := by decide +kernel
private theorem p48 : blockEstimate 6285 1329 7473 128 = 342241972346 := by decide +kernel
private theorem p49 : blockEstimate 6285 1329 7601 128 = 287601070306 := by decide +kernel
private theorem p50 : blockEstimate 6285 1329 7729 128 = 236377389264 := by decide +kernel
private theorem p51 : blockEstimate 6285 1329 7857 128 = 189477102800 := by decide +kernel
private theorem p52 : blockEstimate 6285 1329 7985 128 = 147156275408 := by decide +kernel
private theorem p53 : blockEstimate 6285 1329 8113 128 = 109666565328 := by decide +kernel
private theorem p54 : blockEstimate 6285 1329 8241 128 = 77259630800 := by decide +kernel
private theorem p55 : blockEstimate 6285 1329 8369 128 = 50187130064 := by decide +kernel
private theorem p56 : blockEstimate 6285 1329 8497 128 = 28700721360 := by decide +kernel
private theorem p57 : blockEstimate 6285 1329 8625 128 = 13052062928 := by decide +kernel
private theorem p58 : blockEstimate 6285 1329 8753 128 = 3492813008 := by decide +kernel
private theorem p59 : blockEstimate 6285 1329 8881 62 = 133440744 := by decide +kernel
private theorem j0 : blockEstimate 6285 1329 1457 256 = 54830395200 := block_append p1 p2 rfl rfl rfl
private theorem j1 : blockEstimate 6285 1329 1329 384 = 57044840160 := block_append p0 j0 rfl rfl rfl
private theorem j2 : blockEstimate 6285 1329 1713 256 = 197802504000 := block_append p3 p4 rfl rfl rfl
private theorem j3 : blockEstimate 6285 1329 1969 256 = 420424445760 := block_append p5 p6 rfl rfl rfl
private theorem j4 : blockEstimate 6285 1329 1713 512 = 618226949760 := block_append j2 j3 rfl rfl rfl
private theorem j5 : blockEstimate 6285 1329 1329 896 = 675271789920 := block_append j1 j4 rfl rfl rfl
private theorem j6 : blockEstimate 6285 1329 2225 256 = 709811318592 := block_append p7 p8 rfl rfl rfl
private theorem j7 : blockEstimate 6285 1329 2481 256 = 1052675862548 := block_append p9 p10 rfl rfl rfl
private theorem j8 : blockEstimate 6285 1329 2225 512 = 1762487181140 := block_append j6 j7 rfl rfl rfl
private theorem j9 : blockEstimate 6285 1329 2737 256 = 1408260264320 := block_append p11 p12 rfl rfl rfl
private theorem j10 : blockEstimate 6285 1329 2993 256 = 1723920634240 := block_append p13 p14 rfl rfl rfl
private theorem j11 : blockEstimate 6285 1329 2737 512 = 3132180898560 := block_append j9 j10 rfl rfl rfl
private theorem j12 : blockEstimate 6285 1329 2225 1024 = 4894668079700 := block_append j8 j11 rfl rfl rfl
private theorem j13 : blockEstimate 6285 1329 1329 1920 = 5569939869620 := block_append j5 j12 rfl rfl rfl
private theorem j14 : blockEstimate 6285 1329 3377 256 = 2113734824320 := block_append p16 p17 rfl rfl rfl
private theorem j15 : blockEstimate 6285 1329 3249 384 = 3080121719360 := block_append p15 j14 rfl rfl rfl
private theorem j16 : blockEstimate 6285 1329 3633 256 = 2317826707840 := block_append p18 p19 rfl rfl rfl
private theorem j17 : blockEstimate 6285 1329 3889 256 = 2477291196800 := block_append p20 p21 rfl rfl rfl
private theorem j18 : blockEstimate 6285 1329 3633 512 = 4795117904640 := block_append j16 j17 rfl rfl rfl
private theorem j19 : blockEstimate 6285 1329 3249 896 = 7875239624000 := block_append j15 j18 rfl rfl rfl
private theorem j20 : blockEstimate 6285 1329 4145 256 = 2592128291200 := block_append p22 p23 rfl rfl rfl
private theorem j21 : blockEstimate 6285 1329 4401 256 = 2662337991040 := block_append p24 p25 rfl rfl rfl
private theorem j22 : blockEstimate 6285 1329 4145 512 = 5254466282240 := block_append j20 j21 rfl rfl rfl
private theorem j23 : blockEstimate 6285 1329 4657 256 = 2687920296320 := block_append p26 p27 rfl rfl rfl
private theorem j24 : blockEstimate 6285 1329 4913 256 = 2668875207040 := block_append p28 p29 rfl rfl rfl
private theorem j25 : blockEstimate 6285 1329 4657 512 = 5356795503360 := block_append j23 j24 rfl rfl rfl
private theorem j26 : blockEstimate 6285 1329 4145 1024 = 10611261785600 := block_append j22 j25 rfl rfl rfl
private theorem j27 : blockEstimate 6285 1329 3249 1920 = 18486501409600 := block_append j19 j26 rfl rfl rfl
private theorem j28 : blockEstimate 6285 1329 1329 3840 = 24056441279220 := block_append j13 j27 rfl rfl rfl
private theorem j29 : blockEstimate 6285 1329 5297 256 = 2556631208320 := block_append p31 p32 rfl rfl rfl
private theorem j30 : blockEstimate 6285 1329 5169 384 = 3869980842560 := block_append p30 j29 rfl rfl rfl
private theorem j31 : blockEstimate 6285 1329 5553 256 = 2426017632640 := block_append p33 p34 rfl rfl rfl
private theorem j32 : blockEstimate 6285 1329 5809 256 = 2250776662400 := block_append p35 p36 rfl rfl rfl
private theorem j33 : blockEstimate 6285 1329 5553 512 = 4676794295040 := block_append j31 j32 rfl rfl rfl
private theorem j34 : blockEstimate 6285 1329 5169 896 = 8546775137600 := block_append j30 j33 rfl rfl rfl
private theorem j35 : blockEstimate 6285 1329 6065 256 = 2030923138234 := block_append p37 p38 rfl rfl rfl
private theorem j36 : blockEstimate 6285 1329 6321 256 = 1774636502278 := block_append p39 p40 rfl rfl rfl
private theorem j37 : blockEstimate 6285 1329 6065 512 = 3805559640512 := block_append j35 j36 rfl rfl rfl
private theorem j38 : blockEstimate 6285 1329 6577 256 = 1507172050572 := block_append p41 p42 rfl rfl rfl
private theorem j39 : blockEstimate 6285 1329 6833 256 = 1240460898406 := block_append p43 p44 rfl rfl rfl
private theorem j40 : blockEstimate 6285 1329 6577 512 = 2747632948978 := block_append j38 j39 rfl rfl rfl
private theorem j41 : blockEstimate 6285 1329 6065 1024 = 6553192589490 := block_append j37 j40 rfl rfl rfl
private theorem j42 : blockEstimate 6285 1329 5169 1920 = 15099967727090 := block_append j34 j41 rfl rfl rfl
private theorem j43 : blockEstimate 6285 1329 7217 256 = 859870371684 := block_append p46 p47 rfl rfl rfl
private theorem j44 : blockEstimate 6285 1329 7089 384 = 1382615661739 := block_append p45 j43 rfl rfl rfl
private theorem j45 : blockEstimate 6285 1329 7473 256 = 629843042652 := block_append p48 p49 rfl rfl rfl
private theorem j46 : blockEstimate 6285 1329 7729 256 = 425854492064 := block_append p50 p51 rfl rfl rfl
private theorem j47 : blockEstimate 6285 1329 7473 512 = 1055697534716 := block_append j45 j46 rfl rfl rfl
private theorem j48 : blockEstimate 6285 1329 7089 896 = 2438313196455 := block_append j44 j47 rfl rfl rfl
private theorem j49 : blockEstimate 6285 1329 7985 256 = 256822840736 := block_append p52 p53 rfl rfl rfl
private theorem j50 : blockEstimate 6285 1329 8241 256 = 127446760864 := block_append p54 p55 rfl rfl rfl
private theorem j51 : blockEstimate 6285 1329 7985 512 = 384269601600 := block_append j49 j50 rfl rfl rfl
private theorem j52 : blockEstimate 6285 1329 8497 256 = 41752784288 := block_append p56 p57 rfl rfl rfl
private theorem j53 : blockEstimate 6285 1329 8753 190 = 3626253752 := block_append p58 p59 rfl rfl rfl
private theorem j54 : blockEstimate 6285 1329 8497 446 = 45379038040 := block_append j52 j53 rfl rfl rfl
private theorem j55 : blockEstimate 6285 1329 7985 958 = 429648639640 := block_append j51 j54 rfl rfl rfl
private theorem j56 : blockEstimate 6285 1329 7089 1854 = 2867961836095 := block_append j48 j55 rfl rfl rfl
private theorem j57 : blockEstimate 6285 1329 5169 3774 = 17967929563185 := block_append j42 j56 rfl rfl rfl
private theorem j58 : blockEstimate 6285 1329 1329 7614 = 42024370842405 := block_append j28 j57 rfl rfl rfl

theorem moment_6285_1329 : momentEstimate 6285 1329 = 42024370842405 := j58

end Lower6961.Lo.TerminalBank
