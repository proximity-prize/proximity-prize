import ProximityPrize.SubmissionLower.KoalaH2430ContactData
import ProximityPrize.SubmissionLower.KoalaH2429Banks

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000

namespace KoalaH2429Contact
open KoalaH2430Contact

def contact01 : StageContact :=
  ⟨KoalaH2429Banks.stage01.free.shape, KoalaH2429Banks.stage01.moving.shape, KoalaH2429Banks.stage01.reserve,
    ![12345/2, 156263, 730035, 6037392],
    ![(.splitZ 84 (.leaf 1) (.leaf 1)),
      (.leaf 1),
      (.leaf 1),
      (.leaf 1)]⟩

private theorem checked01 : stageChecked contact01 := by decide +kernel

def contact02 : StageContact :=
  ⟨KoalaH2429Banks.stage02.free.shape, KoalaH2429Banks.stage02.moving.shape, KoalaH2429Banks.stage02.reserve,
    ![33224/9, 721814/9, 3329873/9, 8179834/3],
    ![(.splitZ 93 (.leaf 1) (.leaf 1)),
      (.leaf 1),
      (.leaf 1),
      (.leaf 1)]⟩

private theorem checked02 : stageChecked contact02 := by decide +kernel

def contact03 : StageContact :=
  ⟨KoalaH2429Banks.stage03.free.shape, KoalaH2429Banks.stage03.moving.shape, KoalaH2429Banks.stage03.reserve,
    ![8473/4, 56831, 4224741/16, 2079792],
    ![(.splitZ 101 (.leaf 1) (.leaf 1)),
      (.leaf 1),
      (.splitX 643 (.leaf 1) (.splitZ 64 (.splitX 965 (.leaf 1) (.splitZ 32 (.leaf 1) (.splitX 1126 (.leaf 1) (.splitZ 48 (.leaf 1) (.leaf 2))))) (.leaf 2))),
      (.leaf 1)]⟩

private theorem checked03 : stageChecked contact03 := by decide +kernel

def contact04 : StageContact :=
  ⟨KoalaH2429Banks.stage04.free.shape, KoalaH2429Banks.stage04.moving.shape, KoalaH2429Banks.stage04.reserve,
    ![39909/25, 1078772/25, 431887/2, 36821454/25],
    ![(.splitZ 112 (.leaf 1) (.leaf 1)),
      (.leaf 1),
      (.splitX 649 (.leaf 1) (.splitZ 71 (.splitX 974 (.splitZ 35 (.leaf 1) (.splitX 812 (.leaf 1) (.splitZ 53 (.leaf 1) (.leaf 2)))) (.splitZ 35 (.leaf 1) (.leaf 2))) (.leaf 2))),
      (.splitX 649 (.leaf 1) (.leaf 2))]⟩

private theorem checked04 : stageChecked contact04 := by decide +kernel

def contact05 : StageContact :=
  ⟨KoalaH2429Banks.stage05.free.shape, KoalaH2429Banks.stage05.moving.shape, KoalaH2429Banks.stage05.reserve,
    ![53009/36, 562535/18, 325121/2, 9096500/9],
    ![(.splitZ 121 (.leaf 1) (.leaf 1)),
      (.leaf 1),
      (.splitX 700 (.splitZ 77 (.splitX 350 (.leaf 1) (.splitZ 38 (.leaf 1) (.leaf 2))) (.leaf 2)) (.splitZ 77 (.splitZ 38 (.splitX 1050 (.splitX 875 (.leaf 1) (.splitZ 19 (.leaf 1) (.leaf 2))) (.splitX 1225 (.splitZ 19 (.leaf 1) (.leaf 2)) (.leaf 2))) (.leaf 2)) (.leaf 2))),
      (.splitX 700 (.leaf 1) (.leaf 2))]⟩

private theorem checked05 : stageChecked contact05 := by decide +kernel

def contact06 : StageContact :=
  ⟨KoalaH2429Banks.stage06.free.shape, KoalaH2429Banks.stage06.moving.shape, KoalaH2429Banks.stage06.reserve,
    ![32709/32, 1516011/64, 1707525/14, 146138425/196],
    ![(.splitZ 136 (.leaf 1) (.leaf 1)),
      (.leaf 1),
      (.splitX 758 (.splitZ 87 (.splitX 379 (.splitZ 43 (.leaf 1) (.leaf 2)) (.splitZ 43 (.splitX 569 (.splitZ 21 (.leaf 1) (.leaf 2)) (.splitZ 21 (.leaf 1) (.leaf 2))) (.leaf 2))) (.leaf 2)) (.splitZ 87 (.splitX 1138 (.splitZ 43 (.splitX 948 (.splitZ 21 (.leaf 1) (.leaf 2)) (.leaf 2)) (.leaf 2)) (.leaf 2)) (.leaf 3))),
      (.splitX 758 (.splitX 379 (.leaf 1) (.leaf 2)) (.leaf 2))]⟩

private theorem checked06 : stageChecked contact06 := by decide +kernel

def contact07 : StageContact :=
  ⟨KoalaH2429Banks.stage07.free.shape, KoalaH2429Banks.stage07.moving.shape, KoalaH2429Banks.stage07.reserve,
    ![90802/121, 1999933/121, 7215157/81, 3080033/5],
    ![(.splitZ 154 (.leaf 1) (.leaf 2)),
      (.leaf 1),
      (.splitX 994 (.splitZ 98 (.splitX 497 (.splitZ 49 (.splitX 248 (.leaf 1) (.leaf 2)) (.leaf 2)) (.splitZ 49 (.leaf 2) (.leaf 3))) (.leaf 3)) (.splitZ 98 (.splitX 1491 (.splitZ 49 (.splitX 1243 (.leaf 2) (.splitZ 24 (.leaf 2) (.leaf 3))) (.leaf 3)) (.leaf 3)) (.leaf 4))),
      (.splitX 994 (.splitX 497 (.splitX 248 (.leaf 1) (.leaf 2)) (.leaf 2)) (.leaf 3))]⟩

private theorem checked07 : stageChecked contact07 := by decide +kernel

def contact08 : StageContact :=
  ⟨KoalaH2429Banks.stage08.free.shape, KoalaH2429Banks.stage08.moving.shape, KoalaH2429Banks.stage08.reserve,
    ![131620/289, 3538170/289, 3493309/49, 89172395/98],
    ![(.splitZ 187 (.leaf 1) (.leaf 2)),
      (.leaf 1),
      (.splitX 1878 (.splitZ 118 (.splitX 939 (.splitZ 59 (.splitX 469 (.leaf 2) (.leaf 3)) (.leaf 3)) (.splitZ 59 (.splitX 1409 (.leaf 3) (.splitZ 29 (.leaf 3) (.leaf 4))) (.leaf 4))) (.leaf 5)) (.splitZ 118 (.splitX 2818 (.splitZ 59 (.leaf 4) (.splitX 2348 (.splitZ 89 (.leaf 4) (.leaf 5)) (.leaf 5))) (.leaf 5)) (.leaf 6))),
      (.leaf 4)]⟩

private theorem checked08 : stageChecked contact08 := by decide +kernel

def contact09 : StageContact :=
  ⟨KoalaH2429Banks.stage09.free.shape, KoalaH2429Banks.stage09.moving.shape, KoalaH2429Banks.stage09.reserve,
    ![9974/11, 211336/11, 10529932/81, 4847663/11],
    ![(.splitZ 192 (.leaf 1) (.leaf 2)),
      (.leaf 1),
      (.leaf 3),
      (.splitX 711 (.splitX 355 (.leaf 1) (.leaf 2)) (.leaf 3))]⟩

private theorem checked09 : stageChecked contact09 := by decide +kernel

def contact10 : StageContact :=
  ⟨KoalaH2429Banks.stage10.free.shape, KoalaH2429Banks.stage10.moving.shape, KoalaH2429Banks.stage10.reserve,
    ![219077/324, 4061537/324, 10487591/150, 291512],
    ![(.splitZ 259 (.leaf 1) (.leaf 2)),
      (.leaf 1),
      (.splitX 956 (.splitZ 166 (.splitX 478 (.splitZ 83 (.leaf 2) (.leaf 3)) (.splitZ 83 (.leaf 3) (.leaf 4))) (.leaf 5)) (.splitZ 166 (.splitX 1435 (.splitZ 83 (.splitX 1196 (.splitZ 41 (.leaf 3) (.leaf 4)) (.splitZ 41 (.leaf 3) (.leaf 4))) (.leaf 4)) (.splitZ 83 (.leaf 4) (.leaf 5))) (.leaf 6))),
      (.splitX 956 (.splitX 478 (.splitX 239 (.leaf 1) (.leaf 2)) (.leaf 3)) (.leaf 4))]⟩

private theorem checked10 : stageChecked contact10 := by decide +kernel

def contact11 : StageContact :=
  ⟨KoalaH2429Banks.stage11.free.shape, KoalaH2429Banks.stage11.moving.shape, KoalaH2429Banks.stage11.reserve,
    ![3432/7, 498058/49, 408534933/7225, 8509395/17],
    ![(.splitZ 233 (.leaf 1) (.leaf 3)),
      (.leaf 1),
      (.splitX 1422 (.splitZ 149 (.splitX 711 (.splitZ 74 (.splitX 355 (.leaf 2) (.leaf 3)) (.leaf 4)) (.splitZ 74 (.splitX 1067 (.splitZ 37 (.leaf 3) (.leaf 4)) (.leaf 4)) (.leaf 5))) (.leaf 6)) (.splitZ 149 (.splitX 2134 (.splitZ 74 (.splitX 1778 (.leaf 4) (.splitZ 37 (.leaf 4) (.leaf 5))) (.leaf 5)) (.splitZ 74 (.leaf 5) (.leaf 6))) (.leaf 6))),
      (.leaf 5)]⟩

private theorem checked11 : stageChecked contact11 := by decide +kernel

def contact12 : StageContact :=
  ⟨KoalaH2429Banks.stage12.free.shape, KoalaH2429Banks.stage12.moving.shape, KoalaH2429Banks.stage12.reserve,
    ![270871/784, 8101669/841, 196327722/3703, 387127411/529],
    ![(.splitZ 263 (.splitZ 131 (.splitZ 65 (.splitZ 32 (.leaf 1) (.splitZ 49 (.splitZ 41 (.leaf 1) (.leaf 2)) (.leaf 2))) (.leaf 2)) (.leaf 3)) (.leaf 4)),
      (.splitX 2766 (.splitX 1383 (.leaf 1) (.leaf 2)) (.leaf 2)),
      (.splitX 2766 (.splitZ 168 (.splitX 1383 (.splitZ 84 (.leaf 4) (.leaf 5)) (.splitZ 84 (.splitX 2075 (.leaf 5) (.leaf 6)) (.splitX 2075 (.leaf 6) (.leaf 7)))) (.leaf 8)) (.splitZ 168 (.splitX 4150 (.splitZ 84 (.splitX 3458 (.leaf 6) (.leaf 7)) (.splitX 3458 (.leaf 7) (.leaf 8))) (.leaf 8)) (.leaf 9))),
      (.leaf 7)]⟩

private theorem checked12 : stageChecked contact12 := by decide +kernel

def contact13 : StageContact :=
  ⟨KoalaH2429Banks.stage13.free.shape, KoalaH2429Banks.stage13.moving.shape, KoalaH2429Banks.stage13.reserve,
    ![140159/512, 5632117/512, 51389018/625, 198805900/169],
    ![(.splitZ 276 (.splitZ 138 (.splitZ 69 (.leaf 2) (.splitZ 104 (.leaf 2) (.leaf 3))) (.leaf 3)) (.leaf 5)),
      (.leaf 2),
      (.leaf 9),
      (.leaf 8)]⟩

private theorem checked13 : stageChecked contact13 := by decide +kernel

def contact14 : StageContact :=
  ⟨KoalaH2429Banks.stage14.free.shape, KoalaH2429Banks.stage14.moving.shape, KoalaH2429Banks.stage14.reserve,
    ![15155/26, 2602673/243, 8313920/121, 38204100/169],
    ![(.splitZ 350 (.leaf 2) (.leaf 4)),
      (.leaf 1),
      (.leaf 6),
      (.splitX 1248 (.splitX 624 (.splitX 312 (.leaf 2) (.leaf 3)) (.splitX 936 (.leaf 4) (.leaf 5))) (.leaf 6))]⟩

private theorem checked14 : stageChecked contact14 := by decide +kernel

def contact15 : StageContact :=
  ⟨KoalaH2429Banks.stage15.free.shape, KoalaH2429Banks.stage15.moving.shape, KoalaH2429Banks.stage15.reserve,
    ![262331/722, 11557535/1444, 44686193/1024, 97517559/256],
    ![(.splitZ 367 (.leaf 2) (.leaf 5)),
      (.splitX 2329 (.leaf 2) (.leaf 3)),
      (.splitX 2329 (.splitZ 235 (.splitX 1164 (.splitZ 117 (.leaf 5) (.leaf 6)) (.splitZ 117 (.splitX 1747 (.leaf 6) (.leaf 7)) (.leaf 8))) (.leaf 10)) (.splitZ 235 (.splitX 3494 (.splitZ 117 (.splitX 2912 (.splitZ 58 (.leaf 7) (.leaf 8)) (.splitZ 58 (.leaf 7) (.splitX 3203 (.leaf 8) (.leaf 9)))) (.leaf 9)) (.splitZ 117 (.leaf 9) (.leaf 10))) (.leaf 12))),
      (.leaf 8)]⟩

private theorem checked15 : stageChecked contact15 := by decide +kernel

def contact16 : StageContact :=
  ⟨KoalaH2429Banks.stage16.free.shape, KoalaH2429Banks.stage16.moving.shape, KoalaH2429Banks.stage16.reserve,
    ![851681/2401, 52860058/7203, 48697004/1225, 8832784/25],
    ![(.splitZ 455 (.leaf 3) (.leaf 7)),
      (.splitX 2972 (.splitX 1486 (.leaf 2) (.leaf 3)) (.leaf 3)),
      (.splitX 2972 (.splitZ 292 (.splitX 1486 (.splitZ 146 (.splitX 743 (.leaf 5) (.leaf 7)) (.leaf 8)) (.splitZ 146 (.splitZ 73 (.leaf 8) (.splitX 2229 (.leaf 9) (.leaf 10))) (.leaf 11))) (.leaf 14)) (.splitZ 292 (.splitZ 146 (.splitX 4458 (.splitZ 73 (.leaf 9) (.splitX 3715 (.leaf 10) (.leaf 11))) (.leaf 12)) (.splitX 4458 (.leaf 12) (.leaf 13))) (.leaf 15))),
      (.leaf 10)]⟩

private theorem checked16 : stageChecked contact16 := by decide +kernel

def contact17 : StageContact :=
  ⟨KoalaH2429Banks.stage17.free.shape, KoalaH2429Banks.stage17.moving.shape, KoalaH2429Banks.stage17.reserve,
    ![643307/1922, 564083/81, 17643838981/474721, 923854059/2809],
    ![(.splitZ 556 (.leaf 4) (.leaf 9)),
      (.splitX 3694 (.splitX 1847 (.leaf 3) (.splitX 2771 (.splitX 2309 (.leaf 3) (.leaf 4)) (.leaf 4))) (.leaf 4)),
      (.splitX 3694 (.splitZ 357 (.splitX 1847 (.splitZ 178 (.splitX 923 (.leaf 7) (.leaf 9)) (.leaf 11)) (.splitZ 178 (.splitX 2771 (.splitZ 89 (.leaf 9) (.leaf 11)) (.splitZ 89 (.leaf 10) (.leaf 12))) (.leaf 13))) (.leaf 17)) (.splitZ 357 (.splitX 5542 (.splitZ 178 (.splitX 4618 (.leaf 13) (.leaf 14)) (.splitX 4618 (.splitZ 268 (.leaf 14) (.leaf 16)) (.leaf 15))) (.splitZ 178 (.leaf 15) (.leaf 17))) (.leaf 19))),
      (.leaf 13)]⟩

private theorem checked17 : stageChecked contact17 := by decide +kernel

def contact18 : StageContact :=
  ⟨KoalaH2429Banks.stage18.free.shape, KoalaH2429Banks.stage18.moving.shape, KoalaH2429Banks.stage18.reserve,
    ![4650542/22445, 148056648/4489, 697488408/2209, 19079424],
    ![(.splitZ 492 (.splitZ 246 (.splitZ 123 (.splitZ 61 (.leaf 3) (.splitZ 92 (.leaf 4) (.leaf 5))) (.leaf 5)) (.leaf 7)) (.leaf 11)),
      (.leaf 5),
      (.leaf 25),
      (.leaf 34)]⟩

private theorem checked18 : stageChecked contact18 := by decide +kernel

def contact19 : StageContact :=
  ⟨KoalaH2429Banks.stage19.free.shape, KoalaH2429Banks.stage19.moving.shape, KoalaH2429Banks.stage19.reserve,
    ![679112/2187, 217279789/32805, 48806582438/1375929, 169655864/529],
    ![(.splitZ 704 (.leaf 5) (.leaf 12)),
      (.splitX 4778 (.splitX 2389 (.leaf 4) (.leaf 5)) (.leaf 6)),
      (.splitX 4778 (.splitZ 452 (.splitZ 226 (.splitX 2389 (.splitZ 113 (.leaf 9) (.leaf 13)) (.splitZ 113 (.leaf 13) (.splitX 3584 (.leaf 14) (.leaf 16)))) (.leaf 17)) (.leaf 23)) (.splitZ 452 (.splitZ 226 (.splitX 7168 (.splitZ 113 (.leaf 14) (.splitX 5973 (.leaf 17) (.leaf 18))) (.leaf 20)) (.splitX 7168 (.splitX 5973 (.leaf 19) (.leaf 20)) (.leaf 22))) (.leaf 25))),
      (.leaf 17)]⟩

private theorem checked19 : stageChecked contact19 := by decide +kernel

def contact20 : StageContact :=
  ⟨KoalaH2429Banks.stage20.free.shape, KoalaH2429Banks.stage20.moving.shape, KoalaH2429Banks.stage20.reserve,
    ![372383/1183, 54443131/8464, 19304458028/549081, 1857516187/6084],
    ![(.splitZ 808 (.leaf 6) (.leaf 14)),
      (.splitX 5240 (.splitX 2620 (.leaf 5) (.splitX 3930 (.leaf 5) (.leaf 6))) (.leaf 7)),
      (.splitX 5240 (.splitZ 515 (.splitX 2620 (.splitZ 257 (.leaf 12) (.leaf 16)) (.splitZ 257 (.splitX 3930 (.leaf 15) (.splitZ 128 (.leaf 15) (.leaf 18))) (.leaf 20))) (.leaf 25)) (.splitZ 515 (.splitX 7861 (.splitZ 257 (.splitX 6551 (.splitZ 128 (.leaf 16) (.splitX 5896 (.leaf 19) (.leaf 20))) (.leaf 21)) (.splitX 6551 (.leaf 21) (.leaf 23))) (.splitZ 257 (.leaf 22) (.leaf 24))) (.leaf 28))),
      (.leaf 19)]⟩

private theorem checked20 : stageChecked contact20 := by decide +kernel

def contact21 : StageContact :=
  ⟨KoalaH2429Banks.stage21.free.shape, KoalaH2429Banks.stage21.moving.shape, KoalaH2429Banks.stage21.reserve,
    ![1564103/8410, 138857919/1682, 163972254887/203401, 87216855625/841],
    ![(.splitZ 436 (.splitZ 218 (.splitZ 109 (.leaf 4) (.leaf 5)) (.leaf 7)) (.leaf 10)),
      (.leaf 5),
      (.leaf 22),
      (.leaf 29)]⟩

private theorem checked21 : stageChecked contact21 := by decide +kernel

def contact : Fin 21 → StageContact :=
  ![contact01, contact02, contact03, contact04, contact05, contact06, contact07, contact08, contact09, contact10, contact11, contact12, contact13, contact14, contact15, contact16, contact17, contact18, contact19, contact20, contact21]

theorem stage_checked (i : Fin 21) : stageChecked (contact i) := by
  fin_cases i <;> first | exact checked01 | exact checked02 | exact checked03 | exact checked04 | exact checked05 | exact checked06 | exact checked07 | exact checked08 | exact checked09 | exact checked10 | exact checked11 | exact checked12 | exact checked13 | exact checked14 | exact checked15 | exact checked16 | exact checked17 | exact checked18 | exact checked19 | exact checked20 | exact checked21

end KoalaH2429Contact
