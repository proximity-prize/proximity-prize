import ProximityPrize.SubmissionLower.R6960RescueSourceSchedule

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open HelperSource (WidthGuard)

private theorem moment_3870_809_part0 :
    blockEstimate 3870 809 809 128 = 1350454560 := rfl
private theorem moment_3870_809_part1 :
    blockEstimate 3870 809 937 128 = 9056935200 := rfl
private theorem moment_3870_809_part2 :
    blockEstimate 3870 809 1065 128 = 23668288800 := rfl
private theorem moment_3870_809_part3 :
    blockEstimate 3870 809 1193 128 = 44379208992 := rfl
private theorem moment_3870_809_part4 :
    blockEstimate 3870 809 1321 128 = 70384389408 := rfl
private theorem moment_3870_809_part5 :
    blockEstimate 3870 809 1449 128 = 100878523680 := rfl
private theorem moment_3870_809_part6 :
    blockEstimate 3870 809 1577 128 = 134727508950 := rfl
private theorem moment_3870_809_part7 :
    blockEstimate 3870 809 1705 128 = 167637366720 := rfl
private theorem moment_3870_809_part8 :
    blockEstimate 3870 809 1833 128 = 197185337280 := rfl
private theorem moment_3870_809_part9 :
    blockEstimate 3870 809 1961 128 = 223335921600 := rfl
private theorem moment_3870_809_part10 :
    blockEstimate 3870 809 2089 128 = 246089119680 := rfl
private theorem moment_3870_809_part11 :
    blockEstimate 3870 809 2217 128 = 265444931520 := rfl
private theorem moment_3870_809_part12 :
    blockEstimate 3870 809 2345 128 = 281403357120 := rfl
private theorem moment_3870_809_part13 :
    blockEstimate 3870 809 2473 128 = 293964396480 := rfl
private theorem moment_3870_809_part14 :
    blockEstimate 3870 809 2601 128 = 303128049600 := rfl
private theorem moment_3870_809_part15 :
    blockEstimate 3870 809 2729 128 = 308894316480 := rfl
private theorem moment_3870_809_part16 :
    blockEstimate 3870 809 2857 128 = 311263197120 := rfl
private theorem moment_3870_809_part17 :
    blockEstimate 3870 809 2985 128 = 310234691520 := rfl
private theorem moment_3870_809_part18 :
    blockEstimate 3870 809 3113 128 = 305808799680 := rfl
private theorem moment_3870_809_part19 :
    blockEstimate 3870 809 3241 128 = 297985521600 := rfl
private theorem moment_3870_809_part20 :
    blockEstimate 3870 809 3369 128 = 286764857280 := rfl
private theorem moment_3870_809_part21 :
    blockEstimate 3870 809 3497 128 = 272146806720 := rfl
private theorem moment_3870_809_part22 :
    blockEstimate 3870 809 3625 128 = 254131369920 := rfl
private theorem moment_3870_809_part23 :
    blockEstimate 3870 809 3753 128 = 232718829875 := rfl
private theorem moment_3870_809_part24 :
    blockEstimate 3870 809 3881 128 = 208452439454 := rfl
private theorem moment_3870_809_part25 :
    blockEstimate 3870 809 4009 128 = 183217087457 := rfl
private theorem moment_3870_809_part26 :
    blockEstimate 3870 809 4137 128 = 157861267698 := rfl
private theorem moment_3870_809_part27 :
    blockEstimate 3870 809 4265 128 = 132922472315 := rfl
private theorem moment_3870_809_part28 :
    blockEstimate 3870 809 4393 128 = 108906379528 := rfl
private theorem moment_3870_809_part29 :
    blockEstimate 3870 809 4521 128 = 86286851710 := rfl
private theorem moment_3870_809_part30 :
    blockEstimate 3870 809 4649 128 = 65428117547 := rfl
private theorem moment_3870_809_part31 :
    blockEstimate 3870 809 4777 128 = 46761079776 := rfl
private theorem moment_3870_809_part32 :
    blockEstimate 3870 809 4905 128 = 30868837344 := rfl
private theorem moment_3870_809_part33 :
    blockEstimate 3870 809 5033 128 = 18012681184 := rfl
private theorem moment_3870_809_part34 :
    blockEstimate 3870 809 5161 128 = 8444269536 := rfl
private theorem moment_3870_809_part35 :
    blockEstimate 3870 809 5289 128 = 2415260640 := rfl
private theorem moment_3870_809_part36 :
    blockEstimate 3870 809 5417 71 = 121821510 := rfl
private theorem moment_3870_809_join0 :
    blockEstimate 3870 809 809 256 = 10407389760 :=
  block_append moment_3870_809_part0 moment_3870_809_part1 rfl rfl rfl
private theorem moment_3870_809_join1 :
    blockEstimate 3870 809 1065 256 = 68047497792 :=
  block_append moment_3870_809_part2 moment_3870_809_part3 rfl rfl rfl
private theorem moment_3870_809_join2 :
    blockEstimate 3870 809 809 512 = 78454887552 :=
  block_append moment_3870_809_join0 moment_3870_809_join1 rfl rfl rfl
private theorem moment_3870_809_join3 :
    blockEstimate 3870 809 1321 256 = 171262913088 :=
  block_append moment_3870_809_part4 moment_3870_809_part5 rfl rfl rfl
private theorem moment_3870_809_join4 :
    blockEstimate 3870 809 1705 256 = 364822704000 :=
  block_append moment_3870_809_part7 moment_3870_809_part8 rfl rfl rfl
private theorem moment_3870_809_join5 :
    blockEstimate 3870 809 1577 384 = 499550212950 :=
  block_append moment_3870_809_part6 moment_3870_809_join4 rfl rfl rfl
private theorem moment_3870_809_join6 :
    blockEstimate 3870 809 1321 640 = 670813126038 :=
  block_append moment_3870_809_join3 moment_3870_809_join5 rfl rfl rfl
private theorem moment_3870_809_join7 :
    blockEstimate 3870 809 809 1152 = 749268013590 :=
  block_append moment_3870_809_join2 moment_3870_809_join6 rfl rfl rfl
private theorem moment_3870_809_join8 :
    blockEstimate 3870 809 1961 256 = 469425041280 :=
  block_append moment_3870_809_part9 moment_3870_809_part10 rfl rfl rfl
private theorem moment_3870_809_join9 :
    blockEstimate 3870 809 2217 256 = 546848288640 :=
  block_append moment_3870_809_part11 moment_3870_809_part12 rfl rfl rfl
private theorem moment_3870_809_join10 :
    blockEstimate 3870 809 1961 512 = 1016273329920 :=
  block_append moment_3870_809_join8 moment_3870_809_join9 rfl rfl rfl
private theorem moment_3870_809_join11 :
    blockEstimate 3870 809 2473 256 = 597092446080 :=
  block_append moment_3870_809_part13 moment_3870_809_part14 rfl rfl rfl
private theorem moment_3870_809_join12 :
    blockEstimate 3870 809 2857 256 = 621497888640 :=
  block_append moment_3870_809_part16 moment_3870_809_part17 rfl rfl rfl
private theorem moment_3870_809_join13 :
    blockEstimate 3870 809 2729 384 = 930392205120 :=
  block_append moment_3870_809_part15 moment_3870_809_join12 rfl rfl rfl
private theorem moment_3870_809_join14 :
    blockEstimate 3870 809 2473 640 = 1527484651200 :=
  block_append moment_3870_809_join11 moment_3870_809_join13 rfl rfl rfl
private theorem moment_3870_809_join15 :
    blockEstimate 3870 809 1961 1152 = 2543757981120 :=
  block_append moment_3870_809_join10 moment_3870_809_join14 rfl rfl rfl
private theorem moment_3870_809_join16 :
    blockEstimate 3870 809 809 2304 = 3293025994710 :=
  block_append moment_3870_809_join7 moment_3870_809_join15 rfl rfl rfl
private theorem moment_3870_809_join17 :
    blockEstimate 3870 809 3113 256 = 603794321280 :=
  block_append moment_3870_809_part18 moment_3870_809_part19 rfl rfl rfl
private theorem moment_3870_809_join18 :
    blockEstimate 3870 809 3369 256 = 558911664000 :=
  block_append moment_3870_809_part20 moment_3870_809_part21 rfl rfl rfl
private theorem moment_3870_809_join19 :
    blockEstimate 3870 809 3113 512 = 1162705985280 :=
  block_append moment_3870_809_join17 moment_3870_809_join18 rfl rfl rfl
private theorem moment_3870_809_join20 :
    blockEstimate 3870 809 3625 256 = 486850199795 :=
  block_append moment_3870_809_part22 moment_3870_809_part23 rfl rfl rfl
private theorem moment_3870_809_join21 :
    blockEstimate 3870 809 4009 256 = 341078355155 :=
  block_append moment_3870_809_part25 moment_3870_809_part26 rfl rfl rfl
private theorem moment_3870_809_join22 :
    blockEstimate 3870 809 3881 384 = 549530794609 :=
  block_append moment_3870_809_part24 moment_3870_809_join21 rfl rfl rfl
private theorem moment_3870_809_join23 :
    blockEstimate 3870 809 3625 640 = 1036380994404 :=
  block_append moment_3870_809_join20 moment_3870_809_join22 rfl rfl rfl
private theorem moment_3870_809_join24 :
    blockEstimate 3870 809 3113 1152 = 2199086979684 :=
  block_append moment_3870_809_join19 moment_3870_809_join23 rfl rfl rfl
private theorem moment_3870_809_join25 :
    blockEstimate 3870 809 4265 256 = 241828851843 :=
  block_append moment_3870_809_part27 moment_3870_809_part28 rfl rfl rfl
private theorem moment_3870_809_join26 :
    blockEstimate 3870 809 4649 256 = 112189197323 :=
  block_append moment_3870_809_part30 moment_3870_809_part31 rfl rfl rfl
private theorem moment_3870_809_join27 :
    blockEstimate 3870 809 4521 384 = 198476049033 :=
  block_append moment_3870_809_part29 moment_3870_809_join26 rfl rfl rfl
private theorem moment_3870_809_join28 :
    blockEstimate 3870 809 4265 640 = 440304900876 :=
  block_append moment_3870_809_join25 moment_3870_809_join27 rfl rfl rfl
private theorem moment_3870_809_join29 :
    blockEstimate 3870 809 4905 256 = 48881518528 :=
  block_append moment_3870_809_part32 moment_3870_809_part33 rfl rfl rfl
private theorem moment_3870_809_join30 :
    blockEstimate 3870 809 5289 199 = 2537082150 :=
  block_append moment_3870_809_part35 moment_3870_809_part36 rfl rfl rfl
private theorem moment_3870_809_join31 :
    blockEstimate 3870 809 5161 327 = 10981351686 :=
  block_append moment_3870_809_part34 moment_3870_809_join30 rfl rfl rfl
private theorem moment_3870_809_join32 :
    blockEstimate 3870 809 4905 583 = 59862870214 :=
  block_append moment_3870_809_join29 moment_3870_809_join31 rfl rfl rfl
private theorem moment_3870_809_join33 :
    blockEstimate 3870 809 4265 1223 = 500167771090 :=
  block_append moment_3870_809_join28 moment_3870_809_join32 rfl rfl rfl
private theorem moment_3870_809_join34 :
    blockEstimate 3870 809 3113 2375 = 2699254750774 :=
  block_append moment_3870_809_join24 moment_3870_809_join33 rfl rfl rfl
private theorem moment_3870_809_join35 :
    blockEstimate 3870 809 809 4679 = 5992280745484 :=
  block_append moment_3870_809_join16 moment_3870_809_join34 rfl rfl rfl

theorem moment_3870_809 : momentEstimate 3870 809 = 5992280745484 := moment_3870_809_join35

private theorem moment_4235_890_part0 :
    blockEstimate 4235 890 890 128 = 1481036960 := rfl
private theorem moment_4235_890_part1 :
    blockEstimate 4235 890 1018 128 = 9958958240 := rfl
private theorem moment_4235_890_part2 :
    blockEstimate 4235 890 1146 128 = 26107212960 := rfl
private theorem moment_4235_890_part3 :
    blockEstimate 4235 890 1274 128 = 49120494752 := rfl
private theorem moment_4235_890_part4 :
    blockEstimate 4235 890 1402 128 = 78193497248 := rfl
private theorem moment_4235_890_part5 :
    blockEstimate 4235 890 1530 128 = 112520914080 := rfl
private theorem moment_4235_890_part6 :
    blockEstimate 4235 890 1658 128 = 151297321945 := rfl
private theorem moment_4235_890_part7 :
    blockEstimate 4235 890 1786 128 = 192416653440 := rfl
private theorem moment_4235_890_part8 :
    blockEstimate 4235 890 1914 128 = 230838968448 := rfl
private theorem moment_4235_890_part9 :
    blockEstimate 4235 890 2042 128 = 265524158592 := rfl
private theorem moment_4235_890_part10 :
    blockEstimate 4235 890 2170 128 = 296472223872 := rfl
private theorem moment_4235_890_part11 :
    blockEstimate 4235 890 2298 128 = 323683164288 := rfl
private theorem moment_4235_890_part12 :
    blockEstimate 4235 890 2426 128 = 347156979840 := rfl
private theorem moment_4235_890_part13 :
    blockEstimate 4235 890 2554 128 = 366893670528 := rfl
private theorem moment_4235_890_part14 :
    blockEstimate 4235 890 2682 128 = 382893236352 := rfl
private theorem moment_4235_890_part15 :
    blockEstimate 4235 890 2810 128 = 395155677312 := rfl
private theorem moment_4235_890_part16 :
    blockEstimate 4235 890 2938 128 = 403680993408 := rfl
private theorem moment_4235_890_part17 :
    blockEstimate 4235 890 3066 128 = 408469184640 := rfl
private theorem moment_4235_890_part18 :
    blockEstimate 4235 890 3194 128 = 409520251008 := rfl
private theorem moment_4235_890_part19 :
    blockEstimate 4235 890 3322 128 = 406834192512 := rfl
private theorem moment_4235_890_part20 :
    blockEstimate 4235 890 3450 128 = 400411009152 := rfl
private theorem moment_4235_890_part21 :
    blockEstimate 4235 890 3578 128 = 390250700928 := rfl
private theorem moment_4235_890_part22 :
    blockEstimate 4235 890 3706 128 = 376353267840 := rfl
private theorem moment_4235_890_part23 :
    blockEstimate 4235 890 3834 128 = 358718709888 := rfl
private theorem moment_4235_890_part24 :
    blockEstimate 4235 890 3962 128 = 337347027072 := rfl
private theorem moment_4235_890_part25 :
    blockEstimate 4235 890 4090 128 = 312238219392 := rfl
private theorem moment_4235_890_part26 :
    blockEstimate 4235 890 4218 128 = 283690141688 := rfl
private theorem moment_4235_890_part27 :
    blockEstimate 4235 890 4346 128 = 253624141004 := rfl
private theorem moment_4235_890_part28 :
    blockEstimate 4235 890 4474 128 = 223191153402 := rfl
private theorem moment_4235_890_part29 :
    blockEstimate 4235 890 4602 128 = 192941946510 := rfl
private theorem moment_4235_890_part30 :
    blockEstimate 4235 890 4730 128 = 163397461409 := rfl
private theorem moment_4235_890_part31 :
    blockEstimate 4235 890 4858 128 = 135049716262 := rfl
private theorem moment_4235_890_part32 :
    blockEstimate 4235 890 4986 128 = 108361807977 := rfl
private theorem moment_4235_890_part33 :
    blockEstimate 4235 890 5114 128 = 83636873128 := rfl
private theorem moment_4235_890_part34 :
    blockEstimate 4235 890 5242 128 = 61387552016 := rfl
private theorem moment_4235_890_part35 :
    blockEstimate 4235 890 5370 128 = 42182088976 := rfl
private theorem moment_4235_890_part36 :
    blockEstimate 4235 890 5498 128 = 26273545488 := rfl
private theorem moment_4235_890_part37 :
    blockEstimate 4235 890 5626 128 = 13913579792 := rfl
private theorem moment_4235_890_part38 :
    blockEstimate 4235 890 5754 128 = 5353850128 := rfl
private theorem moment_4235_890_part39 :
    blockEstimate 4235 890 5882 128 = 846014736 := rfl
private theorem moment_4235_890_part40 :
    blockEstimate 4235 890 6010 5 = 93131 := rfl
private theorem moment_4235_890_join0 :
    blockEstimate 4235 890 890 256 = 11439995200 :=
  block_append moment_4235_890_part0 moment_4235_890_part1 rfl rfl rfl
private theorem moment_4235_890_join1 :
    blockEstimate 4235 890 1274 256 = 127313992000 :=
  block_append moment_4235_890_part3 moment_4235_890_part4 rfl rfl rfl
private theorem moment_4235_890_join2 :
    blockEstimate 4235 890 1146 384 = 153421204960 :=
  block_append moment_4235_890_part2 moment_4235_890_join1 rfl rfl rfl
private theorem moment_4235_890_join3 :
    blockEstimate 4235 890 890 640 = 164861200160 :=
  block_append moment_4235_890_join0 moment_4235_890_join2 rfl rfl rfl
private theorem moment_4235_890_join4 :
    blockEstimate 4235 890 1530 256 = 263818236025 :=
  block_append moment_4235_890_part5 moment_4235_890_part6 rfl rfl rfl
private theorem moment_4235_890_join5 :
    blockEstimate 4235 890 1914 256 = 496363127040 :=
  block_append moment_4235_890_part8 moment_4235_890_part9 rfl rfl rfl
private theorem moment_4235_890_join6 :
    blockEstimate 4235 890 1786 384 = 688779780480 :=
  block_append moment_4235_890_part7 moment_4235_890_join5 rfl rfl rfl
private theorem moment_4235_890_join7 :
    blockEstimate 4235 890 1530 640 = 952598016505 :=
  block_append moment_4235_890_join4 moment_4235_890_join6 rfl rfl rfl
private theorem moment_4235_890_join8 :
    blockEstimate 4235 890 890 1280 = 1117459216665 :=
  block_append moment_4235_890_join3 moment_4235_890_join7 rfl rfl rfl
private theorem moment_4235_890_join9 :
    blockEstimate 4235 890 2170 256 = 620155388160 :=
  block_append moment_4235_890_part10 moment_4235_890_part11 rfl rfl rfl
private theorem moment_4235_890_join10 :
    blockEstimate 4235 890 2554 256 = 749786906880 :=
  block_append moment_4235_890_part13 moment_4235_890_part14 rfl rfl rfl
private theorem moment_4235_890_join11 :
    blockEstimate 4235 890 2426 384 = 1096943886720 :=
  block_append moment_4235_890_part12 moment_4235_890_join10 rfl rfl rfl
private theorem moment_4235_890_join12 :
    blockEstimate 4235 890 2170 640 = 1717099274880 :=
  block_append moment_4235_890_join9 moment_4235_890_join11 rfl rfl rfl
private theorem moment_4235_890_join13 :
    blockEstimate 4235 890 2810 256 = 798836670720 :=
  block_append moment_4235_890_part15 moment_4235_890_part16 rfl rfl rfl
private theorem moment_4235_890_join14 :
    blockEstimate 4235 890 3194 256 = 816354443520 :=
  block_append moment_4235_890_part18 moment_4235_890_part19 rfl rfl rfl
private theorem moment_4235_890_join15 :
    blockEstimate 4235 890 3066 384 = 1224823628160 :=
  block_append moment_4235_890_part17 moment_4235_890_join14 rfl rfl rfl
private theorem moment_4235_890_join16 :
    blockEstimate 4235 890 2810 640 = 2023660298880 :=
  block_append moment_4235_890_join13 moment_4235_890_join15 rfl rfl rfl
private theorem moment_4235_890_join17 :
    blockEstimate 4235 890 2170 1280 = 3740759573760 :=
  block_append moment_4235_890_join12 moment_4235_890_join16 rfl rfl rfl
private theorem moment_4235_890_join18 :
    blockEstimate 4235 890 890 2560 = 4858218790425 :=
  block_append moment_4235_890_join8 moment_4235_890_join17 rfl rfl rfl
private theorem moment_4235_890_join19 :
    blockEstimate 4235 890 3450 256 = 790661710080 :=
  block_append moment_4235_890_part20 moment_4235_890_part21 rfl rfl rfl
private theorem moment_4235_890_join20 :
    blockEstimate 4235 890 3834 256 = 696065736960 :=
  block_append moment_4235_890_part23 moment_4235_890_part24 rfl rfl rfl
private theorem moment_4235_890_join21 :
    blockEstimate 4235 890 3706 384 = 1072419004800 :=
  block_append moment_4235_890_part22 moment_4235_890_join20 rfl rfl rfl
private theorem moment_4235_890_join22 :
    blockEstimate 4235 890 3450 640 = 1863080714880 :=
  block_append moment_4235_890_join19 moment_4235_890_join21 rfl rfl rfl
private theorem moment_4235_890_join23 :
    blockEstimate 4235 890 4090 256 = 595928361080 :=
  block_append moment_4235_890_part25 moment_4235_890_part26 rfl rfl rfl
private theorem moment_4235_890_join24 :
    blockEstimate 4235 890 4474 256 = 416133099912 :=
  block_append moment_4235_890_part28 moment_4235_890_part29 rfl rfl rfl
private theorem moment_4235_890_join25 :
    blockEstimate 4235 890 4346 384 = 669757240916 :=
  block_append moment_4235_890_part27 moment_4235_890_join24 rfl rfl rfl
private theorem moment_4235_890_join26 :
    blockEstimate 4235 890 4090 640 = 1265685601996 :=
  block_append moment_4235_890_join23 moment_4235_890_join25 rfl rfl rfl
private theorem moment_4235_890_join27 :
    blockEstimate 4235 890 3450 1280 = 3128766316876 :=
  block_append moment_4235_890_join22 moment_4235_890_join26 rfl rfl rfl
private theorem moment_4235_890_join28 :
    blockEstimate 4235 890 4730 256 = 298447177671 :=
  block_append moment_4235_890_part30 moment_4235_890_part31 rfl rfl rfl
private theorem moment_4235_890_join29 :
    blockEstimate 4235 890 5114 256 = 145024425144 :=
  block_append moment_4235_890_part33 moment_4235_890_part34 rfl rfl rfl
private theorem moment_4235_890_join30 :
    blockEstimate 4235 890 4986 384 = 253386233121 :=
  block_append moment_4235_890_part32 moment_4235_890_join29 rfl rfl rfl
private theorem moment_4235_890_join31 :
    blockEstimate 4235 890 4730 640 = 551833410792 :=
  block_append moment_4235_890_join28 moment_4235_890_join30 rfl rfl rfl
private theorem moment_4235_890_join32 :
    blockEstimate 4235 890 5498 256 = 40187125280 :=
  block_append moment_4235_890_part36 moment_4235_890_part37 rfl rfl rfl
private theorem moment_4235_890_join33 :
    blockEstimate 4235 890 5370 384 = 82369214256 :=
  block_append moment_4235_890_part35 moment_4235_890_join32 rfl rfl rfl
private theorem moment_4235_890_join34 :
    blockEstimate 4235 890 5882 133 = 846107867 :=
  block_append moment_4235_890_part39 moment_4235_890_part40 rfl rfl rfl
private theorem moment_4235_890_join35 :
    blockEstimate 4235 890 5754 261 = 6199957995 :=
  block_append moment_4235_890_part38 moment_4235_890_join34 rfl rfl rfl
private theorem moment_4235_890_join36 :
    blockEstimate 4235 890 5370 645 = 88569172251 :=
  block_append moment_4235_890_join33 moment_4235_890_join35 rfl rfl rfl
private theorem moment_4235_890_join37 :
    blockEstimate 4235 890 4730 1285 = 640402583043 :=
  block_append moment_4235_890_join31 moment_4235_890_join36 rfl rfl rfl
private theorem moment_4235_890_join38 :
    blockEstimate 4235 890 3450 2565 = 3769168899919 :=
  block_append moment_4235_890_join27 moment_4235_890_join37 rfl rfl rfl
private theorem moment_4235_890_join39 :
    blockEstimate 4235 890 890 5125 = 8627387690344 :=
  block_append moment_4235_890_join18 moment_4235_890_join38 rfl rfl rfl

theorem moment_4235_890 : momentEstimate 4235 890 = 8627387690344 := moment_4235_890_join39

private theorem moment_4235_924_part0 :
    blockEstimate 4235 924 924 128 = 1481036960 := rfl
private theorem moment_4235_924_part1 :
    blockEstimate 4235 924 1052 128 = 9958958240 := rfl
private theorem moment_4235_924_part2 :
    blockEstimate 4235 924 1180 128 = 26107212960 := rfl
private theorem moment_4235_924_part3 :
    blockEstimate 4235 924 1308 128 = 49120494752 := rfl
private theorem moment_4235_924_part4 :
    blockEstimate 4235 924 1436 128 = 78193497248 := rfl
private theorem moment_4235_924_part5 :
    blockEstimate 4235 924 1564 128 = 112520914080 := rfl
private theorem moment_4235_924_part6 :
    blockEstimate 4235 924 1692 128 = 151297438880 := rfl
private theorem moment_4235_924_part7 :
    blockEstimate 4235 924 1820 128 = 193178402555 := rfl
private theorem moment_4235_924_part8 :
    blockEstimate 4235 924 1948 128 = 233312350400 := rfl
private theorem moment_4235_924_part9 :
    blockEstimate 4235 924 2076 128 = 269578744000 := rfl
private theorem moment_4235_924_part10 :
    blockEstimate 4235 924 2204 128 = 301965406400 := rfl
private theorem moment_4235_924_part11 :
    blockEstimate 4235 924 2332 128 = 330472337600 := rfl
private theorem moment_4235_924_part12 :
    blockEstimate 4235 924 2460 128 = 355099537600 := rfl
private theorem moment_4235_924_part13 :
    blockEstimate 4235 924 2588 128 = 375847006400 := rfl
private theorem moment_4235_924_part14 :
    blockEstimate 4235 924 2716 128 = 392714744000 := rfl
private theorem moment_4235_924_part15 :
    blockEstimate 4235 924 2844 128 = 405702750400 := rfl
private theorem moment_4235_924_part16 :
    blockEstimate 4235 924 2972 128 = 414811025600 := rfl
private theorem moment_4235_924_part17 :
    blockEstimate 4235 924 3100 128 = 420039569600 := rfl
private theorem moment_4235_924_part18 :
    blockEstimate 4235 924 3228 128 = 421388382400 := rfl
private theorem moment_4235_924_part19 :
    blockEstimate 4235 924 3356 128 = 418857464000 := rfl
private theorem moment_4235_924_part20 :
    blockEstimate 4235 924 3484 128 = 412446814400 := rfl
private theorem moment_4235_924_part21 :
    blockEstimate 4235 924 3612 128 = 402156433600 := rfl
private theorem moment_4235_924_part22 :
    blockEstimate 4235 924 3740 128 = 387986321600 := rfl
private theorem moment_4235_924_part23 :
    blockEstimate 4235 924 3868 128 = 369936478400 := rfl
private theorem moment_4235_924_part24 :
    blockEstimate 4235 924 3996 128 = 348006904000 := rfl
private theorem moment_4235_924_part25 :
    blockEstimate 4235 924 4124 128 = 322198666532 := rfl
private theorem moment_4235_924_part26 :
    blockEstimate 4235 924 4252 128 = 293161594589 := rfl
private theorem moment_4235_924_part27 :
    blockEstimate 4235 924 4380 128 = 262868460698 := rfl
private theorem moment_4235_924_part28 :
    blockEstimate 4235 924 4508 128 = 232145769140 := rfl
private theorem moment_4235_924_part29 :
    blockEstimate 4235 924 4636 128 = 201537973074 := rfl
private theorem moment_4235_924_part30 :
    blockEstimate 4235 924 4764 128 = 171561665426 := rfl
private theorem moment_4235_924_part31 :
    blockEstimate 4235 924 4892 128 = 142705580189 := rfl
private theorem moment_4235_924_part32 :
    blockEstimate 4235 924 5020 128 = 115430591933 := rfl
private theorem moment_4235_924_part33 :
    blockEstimate 4235 924 5148 128 = 90027048170 := rfl
private theorem moment_4235_924_part34 :
    blockEstimate 4235 924 5276 128 = 67011238656 := rfl
private theorem moment_4235_924_part35 :
    blockEstimate 4235 924 5404 128 = 46972332800 := rfl
private theorem moment_4235_924_part36 :
    blockEstimate 4235 924 5532 128 = 30163499776 := rfl
private theorem moment_4235_924_part37 :
    blockEstimate 4235 924 5660 128 = 16836397824 := rfl
private theorem moment_4235_924_part38 :
    blockEstimate 4235 924 5788 128 = 7242685184 := rfl
private theorem moment_4235_924_part39 :
    blockEstimate 4235 924 5916 128 = 1634020096 := rfl
private theorem moment_4235_924_part40 :
    blockEstimate 4235 924 6044 39 = 23322080 := rfl
private theorem moment_4235_924_join0 :
    blockEstimate 4235 924 924 256 = 11439995200 :=
  block_append moment_4235_924_part0 moment_4235_924_part1 rfl rfl rfl
private theorem moment_4235_924_join1 :
    blockEstimate 4235 924 1308 256 = 127313992000 :=
  block_append moment_4235_924_part3 moment_4235_924_part4 rfl rfl rfl
private theorem moment_4235_924_join2 :
    blockEstimate 4235 924 1180 384 = 153421204960 :=
  block_append moment_4235_924_part2 moment_4235_924_join1 rfl rfl rfl
private theorem moment_4235_924_join3 :
    blockEstimate 4235 924 924 640 = 164861200160 :=
  block_append moment_4235_924_join0 moment_4235_924_join2 rfl rfl rfl
private theorem moment_4235_924_join4 :
    blockEstimate 4235 924 1564 256 = 263818352960 :=
  block_append moment_4235_924_part5 moment_4235_924_part6 rfl rfl rfl
private theorem moment_4235_924_join5 :
    blockEstimate 4235 924 1948 256 = 502891094400 :=
  block_append moment_4235_924_part8 moment_4235_924_part9 rfl rfl rfl
private theorem moment_4235_924_join6 :
    blockEstimate 4235 924 1820 384 = 696069496955 :=
  block_append moment_4235_924_part7 moment_4235_924_join5 rfl rfl rfl
private theorem moment_4235_924_join7 :
    blockEstimate 4235 924 1564 640 = 959887849915 :=
  block_append moment_4235_924_join4 moment_4235_924_join6 rfl rfl rfl
private theorem moment_4235_924_join8 :
    blockEstimate 4235 924 924 1280 = 1124749050075 :=
  block_append moment_4235_924_join3 moment_4235_924_join7 rfl rfl rfl
private theorem moment_4235_924_join9 :
    blockEstimate 4235 924 2204 256 = 632437744000 :=
  block_append moment_4235_924_part10 moment_4235_924_part11 rfl rfl rfl
private theorem moment_4235_924_join10 :
    blockEstimate 4235 924 2588 256 = 768561750400 :=
  block_append moment_4235_924_part13 moment_4235_924_part14 rfl rfl rfl
private theorem moment_4235_924_join11 :
    blockEstimate 4235 924 2460 384 = 1123661288000 :=
  block_append moment_4235_924_part12 moment_4235_924_join10 rfl rfl rfl
private theorem moment_4235_924_join12 :
    blockEstimate 4235 924 2204 640 = 1756099032000 :=
  block_append moment_4235_924_join9 moment_4235_924_join11 rfl rfl rfl
private theorem moment_4235_924_join13 :
    blockEstimate 4235 924 2844 256 = 820513776000 :=
  block_append moment_4235_924_part15 moment_4235_924_part16 rfl rfl rfl
private theorem moment_4235_924_join14 :
    blockEstimate 4235 924 3228 256 = 840245846400 :=
  block_append moment_4235_924_part18 moment_4235_924_part19 rfl rfl rfl
private theorem moment_4235_924_join15 :
    blockEstimate 4235 924 3100 384 = 1260285416000 :=
  block_append moment_4235_924_part17 moment_4235_924_join14 rfl rfl rfl
private theorem moment_4235_924_join16 :
    blockEstimate 4235 924 2844 640 = 2080799192000 :=
  block_append moment_4235_924_join13 moment_4235_924_join15 rfl rfl rfl
private theorem moment_4235_924_join17 :
    blockEstimate 4235 924 2204 1280 = 3836898224000 :=
  block_append moment_4235_924_join12 moment_4235_924_join16 rfl rfl rfl
private theorem moment_4235_924_join18 :
    blockEstimate 4235 924 924 2560 = 4961647274075 :=
  block_append moment_4235_924_join8 moment_4235_924_join17 rfl rfl rfl
private theorem moment_4235_924_join19 :
    blockEstimate 4235 924 3484 256 = 814603248000 :=
  block_append moment_4235_924_part20 moment_4235_924_part21 rfl rfl rfl
private theorem moment_4235_924_join20 :
    blockEstimate 4235 924 3868 256 = 717943382400 :=
  block_append moment_4235_924_part23 moment_4235_924_part24 rfl rfl rfl
private theorem moment_4235_924_join21 :
    blockEstimate 4235 924 3740 384 = 1105929704000 :=
  block_append moment_4235_924_part22 moment_4235_924_join20 rfl rfl rfl
private theorem moment_4235_924_join22 :
    blockEstimate 4235 924 3484 640 = 1920532952000 :=
  block_append moment_4235_924_join19 moment_4235_924_join21 rfl rfl rfl
private theorem moment_4235_924_join23 :
    blockEstimate 4235 924 4124 256 = 615360261121 :=
  block_append moment_4235_924_part25 moment_4235_924_part26 rfl rfl rfl
private theorem moment_4235_924_join24 :
    blockEstimate 4235 924 4508 256 = 433683742214 :=
  block_append moment_4235_924_part28 moment_4235_924_part29 rfl rfl rfl
private theorem moment_4235_924_join25 :
    blockEstimate 4235 924 4380 384 = 696552202912 :=
  block_append moment_4235_924_part27 moment_4235_924_join24 rfl rfl rfl
private theorem moment_4235_924_join26 :
    blockEstimate 4235 924 4124 640 = 1311912464033 :=
  block_append moment_4235_924_join23 moment_4235_924_join25 rfl rfl rfl
private theorem moment_4235_924_join27 :
    blockEstimate 4235 924 3484 1280 = 3232445416033 :=
  block_append moment_4235_924_join22 moment_4235_924_join26 rfl rfl rfl
private theorem moment_4235_924_join28 :
    blockEstimate 4235 924 4764 256 = 314267245615 :=
  block_append moment_4235_924_part30 moment_4235_924_part31 rfl rfl rfl
private theorem moment_4235_924_join29 :
    blockEstimate 4235 924 5148 256 = 157038286826 :=
  block_append moment_4235_924_part33 moment_4235_924_part34 rfl rfl rfl
private theorem moment_4235_924_join30 :
    blockEstimate 4235 924 5020 384 = 272468878759 :=
  block_append moment_4235_924_part32 moment_4235_924_join29 rfl rfl rfl
private theorem moment_4235_924_join31 :
    blockEstimate 4235 924 4764 640 = 586736124374 :=
  block_append moment_4235_924_join28 moment_4235_924_join30 rfl rfl rfl
private theorem moment_4235_924_join32 :
    blockEstimate 4235 924 5532 256 = 46999897600 :=
  block_append moment_4235_924_part36 moment_4235_924_part37 rfl rfl rfl
private theorem moment_4235_924_join33 :
    blockEstimate 4235 924 5404 384 = 93972230400 :=
  block_append moment_4235_924_part35 moment_4235_924_join32 rfl rfl rfl
private theorem moment_4235_924_join34 :
    blockEstimate 4235 924 5916 167 = 1657342176 :=
  block_append moment_4235_924_part39 moment_4235_924_part40 rfl rfl rfl
private theorem moment_4235_924_join35 :
    blockEstimate 4235 924 5788 295 = 8900027360 :=
  block_append moment_4235_924_part38 moment_4235_924_join34 rfl rfl rfl
private theorem moment_4235_924_join36 :
    blockEstimate 4235 924 5404 679 = 102872257760 :=
  block_append moment_4235_924_join33 moment_4235_924_join35 rfl rfl rfl
private theorem moment_4235_924_join37 :
    blockEstimate 4235 924 4764 1319 = 689608382134 :=
  block_append moment_4235_924_join31 moment_4235_924_join36 rfl rfl rfl
private theorem moment_4235_924_join38 :
    blockEstimate 4235 924 3484 2599 = 3922053798167 :=
  block_append moment_4235_924_join27 moment_4235_924_join37 rfl rfl rfl
private theorem moment_4235_924_join39 :
    blockEstimate 4235 924 924 5159 = 8883701072242 :=
  block_append moment_4235_924_join18 moment_4235_924_join38 rfl rfl rfl

theorem moment_4235_924 : momentEstimate 4235 924 = 8883701072242 := moment_4235_924_join39

private theorem moment_4255_890_part0 :
    blockEstimate 4255 890 890 128 = 1488192160 := rfl
private theorem moment_4255_890_part1 :
    blockEstimate 4255 890 1018 128 = 10008384160 := rfl
private theorem moment_4255_890_part2 :
    blockEstimate 4255 890 1146 128 = 26240852640 := rfl
private theorem moment_4255_890_part3 :
    blockEstimate 4255 890 1274 128 = 49380291232 := rfl
private theorem moment_4255_890_part4 :
    blockEstimate 4255 890 1402 128 = 78621393568 := rfl
private theorem moment_4255_890_part5 :
    blockEstimate 4255 890 1530 128 = 113158853280 := rfl
private theorem moment_4255_890_part6 :
    blockEstimate 4255 890 1658 128 = 152187246365 := rfl
private theorem moment_4255_890_part7 :
    blockEstimate 4255 890 1786 128 = 193592488320 := rfl
private theorem moment_4255_890_part8 :
    blockEstimate 4255 890 1914 128 = 232306766208 := rfl
private theorem moment_4255_890_part9 :
    blockEstimate 4255 890 2042 128 = 267283919232 := rfl
private theorem moment_4255_890_part10 :
    blockEstimate 4255 890 2170 128 = 298523947392 := rfl
private theorem moment_4255_890_part11 :
    blockEstimate 4255 890 2298 128 = 326026850688 := rfl
private theorem moment_4255_890_part12 :
    blockEstimate 4255 890 2426 128 = 349792629120 := rfl
private theorem moment_4255_890_part13 :
    blockEstimate 4255 890 2554 128 = 369821282688 := rfl
private theorem moment_4255_890_part14 :
    blockEstimate 4255 890 2682 128 = 386112811392 := rfl
private theorem moment_4255_890_part15 :
    blockEstimate 4255 890 2810 128 = 398667215232 := rfl
private theorem moment_4255_890_part16 :
    blockEstimate 4255 890 2938 128 = 407484494208 := rfl
private theorem moment_4255_890_part17 :
    blockEstimate 4255 890 3066 128 = 412564648320 := rfl
private theorem moment_4255_890_part18 :
    blockEstimate 4255 890 3194 128 = 413907677568 := rfl
private theorem moment_4255_890_part19 :
    blockEstimate 4255 890 3322 128 = 411513581952 := rfl
private theorem moment_4255_890_part20 :
    blockEstimate 4255 890 3450 128 = 405382361472 := rfl
private theorem moment_4255_890_part21 :
    blockEstimate 4255 890 3578 128 = 395514016128 := rfl
private theorem moment_4255_890_part22 :
    blockEstimate 4255 890 3706 128 = 381908545920 := rfl
private theorem moment_4255_890_part23 :
    blockEstimate 4255 890 3834 128 = 364565950848 := rfl
private theorem moment_4255_890_part24 :
    blockEstimate 4255 890 3962 128 = 343486230912 := rfl
private theorem moment_4255_890_part25 :
    blockEstimate 4255 890 4090 128 = 318669386112 := rfl
private theorem moment_4255_890_part26 :
    blockEstimate 4255 890 4218 128 = 290279870826 := rfl
private theorem moment_4255_890_part27 :
    blockEstimate 4255 890 4346 128 = 260054586913 := rfl
private theorem moment_4255_890_part28 :
    blockEstimate 4255 890 4474 128 = 229385819232 := rfl
private theorem moment_4255_890_part29 :
    blockEstimate 4255 890 4602 128 = 198837794000 := rfl
private theorem moment_4255_890_part30 :
    blockEstimate 4255 890 4730 128 = 168935971457 := rfl
private theorem moment_4255_890_part31 :
    blockEstimate 4255 890 4858 128 = 140176889005 := rfl
private theorem moment_4255_890_part32 :
    blockEstimate 4255 890 4986 128 = 113028162661 := rfl
private theorem moment_4255_890_part33 :
    blockEstimate 4255 890 5114 128 = 87833864441 := rfl
private theorem moment_4255_890_part34 :
    blockEstimate 4255 890 5242 128 = 65012280656 := rfl
private theorem moment_4255_890_part35 :
    blockEstimate 4255 890 5370 128 = 45205207376 := rfl
private theorem moment_4255_890_part36 :
    blockEstimate 4255 890 5498 128 = 28676703568 := rfl
private theorem moment_4255_890_part37 :
    blockEstimate 4255 890 5626 128 = 15678427472 := rfl
private theorem moment_4255_890_part38 :
    blockEstimate 4255 890 5754 128 = 6462037328 := rfl
private theorem moment_4255_890_part39 :
    blockEstimate 4255 890 5882 128 = 1279191376 := rfl
private theorem moment_4255_890_part40 :
    blockEstimate 4255 890 6010 25 = 6565356 := rfl
private theorem moment_4255_890_join0 :
    blockEstimate 4255 890 890 256 = 11496576320 :=
  block_append moment_4255_890_part0 moment_4255_890_part1 rfl rfl rfl
private theorem moment_4255_890_join1 :
    blockEstimate 4255 890 1274 256 = 128001684800 :=
  block_append moment_4255_890_part3 moment_4255_890_part4 rfl rfl rfl
private theorem moment_4255_890_join2 :
    blockEstimate 4255 890 1146 384 = 154242537440 :=
  block_append moment_4255_890_part2 moment_4255_890_join1 rfl rfl rfl
private theorem moment_4255_890_join3 :
    blockEstimate 4255 890 890 640 = 165739113760 :=
  block_append moment_4255_890_join0 moment_4255_890_join2 rfl rfl rfl
private theorem moment_4255_890_join4 :
    blockEstimate 4255 890 1530 256 = 265346099645 :=
  block_append moment_4255_890_part5 moment_4255_890_part6 rfl rfl rfl
private theorem moment_4255_890_join5 :
    blockEstimate 4255 890 1914 256 = 499590685440 :=
  block_append moment_4255_890_part8 moment_4255_890_part9 rfl rfl rfl
private theorem moment_4255_890_join6 :
    blockEstimate 4255 890 1786 384 = 693183173760 :=
  block_append moment_4255_890_part7 moment_4255_890_join5 rfl rfl rfl
private theorem moment_4255_890_join7 :
    blockEstimate 4255 890 1530 640 = 958529273405 :=
  block_append moment_4255_890_join4 moment_4255_890_join6 rfl rfl rfl
private theorem moment_4255_890_join8 :
    blockEstimate 4255 890 890 1280 = 1124268387165 :=
  block_append moment_4255_890_join3 moment_4255_890_join7 rfl rfl rfl
private theorem moment_4255_890_join9 :
    blockEstimate 4255 890 2170 256 = 624550798080 :=
  block_append moment_4255_890_part10 moment_4255_890_part11 rfl rfl rfl
private theorem moment_4255_890_join10 :
    blockEstimate 4255 890 2554 256 = 755934094080 :=
  block_append moment_4255_890_part13 moment_4255_890_part14 rfl rfl rfl
private theorem moment_4255_890_join11 :
    blockEstimate 4255 890 2426 384 = 1105726723200 :=
  block_append moment_4255_890_part12 moment_4255_890_join10 rfl rfl rfl
private theorem moment_4255_890_join12 :
    blockEstimate 4255 890 2170 640 = 1730277521280 :=
  block_append moment_4255_890_join9 moment_4255_890_join11 rfl rfl rfl
private theorem moment_4255_890_join13 :
    blockEstimate 4255 890 2810 256 = 806151709440 :=
  block_append moment_4255_890_part15 moment_4255_890_part16 rfl rfl rfl
private theorem moment_4255_890_join14 :
    blockEstimate 4255 890 3194 256 = 825421259520 :=
  block_append moment_4255_890_part18 moment_4255_890_part19 rfl rfl rfl
private theorem moment_4255_890_join15 :
    blockEstimate 4255 890 3066 384 = 1237985907840 :=
  block_append moment_4255_890_part17 moment_4255_890_join14 rfl rfl rfl
private theorem moment_4255_890_join16 :
    blockEstimate 4255 890 2810 640 = 2044137617280 :=
  block_append moment_4255_890_join13 moment_4255_890_join15 rfl rfl rfl
private theorem moment_4255_890_join17 :
    blockEstimate 4255 890 2170 1280 = 3774415138560 :=
  block_append moment_4255_890_join12 moment_4255_890_join16 rfl rfl rfl
private theorem moment_4255_890_join18 :
    blockEstimate 4255 890 890 2560 = 4898683525725 :=
  block_append moment_4255_890_join8 moment_4255_890_join17 rfl rfl rfl
private theorem moment_4255_890_join19 :
    blockEstimate 4255 890 3450 256 = 800896377600 :=
  block_append moment_4255_890_part20 moment_4255_890_part21 rfl rfl rfl
private theorem moment_4255_890_join20 :
    blockEstimate 4255 890 3834 256 = 708052181760 :=
  block_append moment_4255_890_part23 moment_4255_890_part24 rfl rfl rfl
private theorem moment_4255_890_join21 :
    blockEstimate 4255 890 3706 384 = 1089960727680 :=
  block_append moment_4255_890_part22 moment_4255_890_join20 rfl rfl rfl
private theorem moment_4255_890_join22 :
    blockEstimate 4255 890 3450 640 = 1890857105280 :=
  block_append moment_4255_890_join19 moment_4255_890_join21 rfl rfl rfl
private theorem moment_4255_890_join23 :
    blockEstimate 4255 890 4090 256 = 608949256938 :=
  block_append moment_4255_890_part25 moment_4255_890_part26 rfl rfl rfl
private theorem moment_4255_890_join24 :
    blockEstimate 4255 890 4474 256 = 428223613232 :=
  block_append moment_4255_890_part28 moment_4255_890_part29 rfl rfl rfl
private theorem moment_4255_890_join25 :
    blockEstimate 4255 890 4346 384 = 688278200145 :=
  block_append moment_4255_890_part27 moment_4255_890_join24 rfl rfl rfl
private theorem moment_4255_890_join26 :
    blockEstimate 4255 890 4090 640 = 1297227457083 :=
  block_append moment_4255_890_join23 moment_4255_890_join25 rfl rfl rfl
private theorem moment_4255_890_join27 :
    blockEstimate 4255 890 3450 1280 = 3188084562363 :=
  block_append moment_4255_890_join22 moment_4255_890_join26 rfl rfl rfl
private theorem moment_4255_890_join28 :
    blockEstimate 4255 890 4730 256 = 309112860462 :=
  block_append moment_4255_890_part30 moment_4255_890_part31 rfl rfl rfl
private theorem moment_4255_890_join29 :
    blockEstimate 4255 890 5114 256 = 152846145097 :=
  block_append moment_4255_890_part33 moment_4255_890_part34 rfl rfl rfl
private theorem moment_4255_890_join30 :
    blockEstimate 4255 890 4986 384 = 265874307758 :=
  block_append moment_4255_890_part32 moment_4255_890_join29 rfl rfl rfl
private theorem moment_4255_890_join31 :
    blockEstimate 4255 890 4730 640 = 574987168220 :=
  block_append moment_4255_890_join28 moment_4255_890_join30 rfl rfl rfl
private theorem moment_4255_890_join32 :
    blockEstimate 4255 890 5498 256 = 44355131040 :=
  block_append moment_4255_890_part36 moment_4255_890_part37 rfl rfl rfl
private theorem moment_4255_890_join33 :
    blockEstimate 4255 890 5370 384 = 89560338416 :=
  block_append moment_4255_890_part35 moment_4255_890_join32 rfl rfl rfl
private theorem moment_4255_890_join34 :
    blockEstimate 4255 890 5882 153 = 1285756732 :=
  block_append moment_4255_890_part39 moment_4255_890_part40 rfl rfl rfl
private theorem moment_4255_890_join35 :
    blockEstimate 4255 890 5754 281 = 7747794060 :=
  block_append moment_4255_890_part38 moment_4255_890_join34 rfl rfl rfl
private theorem moment_4255_890_join36 :
    blockEstimate 4255 890 5370 665 = 97308132476 :=
  block_append moment_4255_890_join33 moment_4255_890_join35 rfl rfl rfl
private theorem moment_4255_890_join37 :
    blockEstimate 4255 890 4730 1305 = 672295300696 :=
  block_append moment_4255_890_join31 moment_4255_890_join36 rfl rfl rfl
private theorem moment_4255_890_join38 :
    blockEstimate 4255 890 3450 2585 = 3860379863059 :=
  block_append moment_4255_890_join27 moment_4255_890_join37 rfl rfl rfl
private theorem moment_4255_890_join39 :
    blockEstimate 4255 890 890 5145 = 8759063388784 :=
  block_append moment_4255_890_join18 moment_4255_890_join38 rfl rfl rfl

theorem moment_4255_890 : momentEstimate 4255 890 = 8759063388784 := moment_4255_890_join39

private theorem moment_4866_1061_part0 :
    blockEstimate 4866 1061 1061 128 = 1706783520 := rfl
private theorem moment_4866_1061_part1 :
    blockEstimate 4866 1061 1189 128 = 11518346016 := rfl
private theorem moment_4866_1061_part2 :
    blockEstimate 4866 1061 1317 128 = 30323544864 := rfl
private theorem moment_4866_1061_part3 :
    blockEstimate 4866 1061 1445 128 = 57317073696 := rfl
private theorem moment_4866_1061_part4 :
    blockEstimate 4866 1061 1573 128 = 91693626144 := rfl
private theorem moment_4866_1061_part5 :
    blockEstimate 4866 1061 1701 128 = 132647895840 := rfl
private theorem moment_4866_1061_part6 :
    blockEstimate 4866 1061 1829 128 = 179374576416 := rfl
private theorem moment_4866_1061_part7 :
    blockEstimate 4866 1061 1957 128 = 231068361504 := rfl
private theorem moment_4866_1061_part8 :
    blockEstimate 4866 1061 2085 128 = 286454620881 := rfl
private theorem moment_4866_1061_part9 :
    blockEstimate 4866 1061 2213 128 = 340231189824 := rfl
private theorem moment_4866_1061_part10 :
    blockEstimate 4866 1061 2341 128 = 389585745216 := rfl
private theorem moment_4866_1061_part11 :
    blockEstimate 4866 1061 2469 128 = 434485949760 := rfl
private theorem moment_4866_1061_part12 :
    blockEstimate 4866 1061 2597 128 = 474931803456 := rfl
private theorem moment_4866_1061_part13 :
    blockEstimate 4866 1061 2725 128 = 510923306304 := rfl
private theorem moment_4866_1061_part14 :
    blockEstimate 4866 1061 2853 128 = 542460458304 := rfl
private theorem moment_4866_1061_part15 :
    blockEstimate 4866 1061 2981 128 = 569543259456 := rfl
private theorem moment_4866_1061_part16 :
    blockEstimate 4866 1061 3109 128 = 592171709760 := rfl
private theorem moment_4866_1061_part17 :
    blockEstimate 4866 1061 3237 128 = 610345809216 := rfl
private theorem moment_4866_1061_part18 :
    blockEstimate 4866 1061 3365 128 = 624065557824 := rfl
private theorem moment_4866_1061_part19 :
    blockEstimate 4866 1061 3493 128 = 633330955584 := rfl
private theorem moment_4866_1061_part20 :
    blockEstimate 4866 1061 3621 128 = 638142002496 := rfl
private theorem moment_4866_1061_part21 :
    blockEstimate 4866 1061 3749 128 = 638498698560 := rfl
private theorem moment_4866_1061_part22 :
    blockEstimate 4866 1061 3877 128 = 634401043776 := rfl
private theorem moment_4866_1061_part23 :
    blockEstimate 4866 1061 4005 128 = 625849038144 := rfl
private theorem moment_4866_1061_part24 :
    blockEstimate 4866 1061 4133 128 = 612842681664 := rfl
private theorem moment_4866_1061_part25 :
    blockEstimate 4866 1061 4261 128 = 595381974336 := rfl
private theorem moment_4866_1061_part26 :
    blockEstimate 4866 1061 4389 128 = 573466916160 := rfl
private theorem moment_4866_1061_part27 :
    blockEstimate 4866 1061 4517 128 = 547097507136 := rfl
private theorem moment_4866_1061_part28 :
    blockEstimate 4866 1061 4645 128 = 516273747264 := rfl
private theorem moment_4866_1061_part29 :
    blockEstimate 4866 1061 4773 128 = 481005997449 := rfl
private theorem moment_4866_1061_part30 :
    blockEstimate 4866 1061 4901 128 = 442318295470 := rfl
private theorem moment_4866_1061_part31 :
    blockEstimate 4866 1061 5029 128 = 402338149752 := rfl
private theorem moment_4866_1061_part32 :
    blockEstimate 4866 1061 5157 128 = 361812541516 := rfl
private theorem moment_4866_1061_part33 :
    blockEstimate 4866 1061 5285 128 = 321290189818 := rfl
private theorem moment_4866_1061_part34 :
    blockEstimate 4866 1061 5413 128 = 281295549078 := rfl
private theorem moment_4866_1061_part35 :
    blockEstimate 4866 1061 5541 128 = 242328807457 := rfl
private theorem moment_4866_1061_part36 :
    blockEstimate 4866 1061 5669 128 = 204865888039 := rfl
private theorem moment_4866_1061_part37 :
    blockEstimate 4866 1061 5797 128 = 169358449123 := rfl
private theorem moment_4866_1061_part38 :
    blockEstimate 4866 1061 5925 128 = 136012354473 := rfl
private theorem moment_4866_1061_part39 :
    blockEstimate 4866 1061 6053 128 = 105427402336 := rfl
private theorem moment_4866_1061_part40 :
    blockEstimate 4866 1061 6181 128 = 78230822496 := rfl
private theorem moment_4866_1061_part41 :
    blockEstimate 4866 1061 6309 128 = 54674308704 := rfl
private theorem moment_4866_1061_part42 :
    blockEstimate 4866 1061 6437 128 = 35009519200 := rfl
private theorem moment_4866_1061_part43 :
    blockEstimate 4866 1061 6565 128 = 19488112224 := rfl
private theorem moment_4866_1061_part44 :
    blockEstimate 4866 1061 6693 128 = 8361746016 := rfl
private theorem moment_4866_1061_part45 :
    blockEstimate 4866 1061 6821 128 = 1882078816 := rfl
private theorem moment_4866_1061_part46 :
    blockEstimate 4866 1061 6949 39 = 26811510 := rfl
private theorem moment_4866_1061_join0 :
    blockEstimate 4866 1061 1061 256 = 13225129536 :=
  block_append moment_4866_1061_part0 moment_4866_1061_part1 rfl rfl rfl
private theorem moment_4866_1061_join1 :
    blockEstimate 4866 1061 1445 256 = 149010699840 :=
  block_append moment_4866_1061_part3 moment_4866_1061_part4 rfl rfl rfl
private theorem moment_4866_1061_join2 :
    blockEstimate 4866 1061 1317 384 = 179334244704 :=
  block_append moment_4866_1061_part2 moment_4866_1061_join1 rfl rfl rfl
private theorem moment_4866_1061_join3 :
    blockEstimate 4866 1061 1061 640 = 192559374240 :=
  block_append moment_4866_1061_join0 moment_4866_1061_join2 rfl rfl rfl
private theorem moment_4866_1061_join4 :
    blockEstimate 4866 1061 1829 256 = 410442937920 :=
  block_append moment_4866_1061_part6 moment_4866_1061_part7 rfl rfl rfl
private theorem moment_4866_1061_join5 :
    blockEstimate 4866 1061 1701 384 = 543090833760 :=
  block_append moment_4866_1061_part5 moment_4866_1061_join4 rfl rfl rfl
private theorem moment_4866_1061_join6 :
    blockEstimate 4866 1061 2213 256 = 729816935040 :=
  block_append moment_4866_1061_part9 moment_4866_1061_part10 rfl rfl rfl
private theorem moment_4866_1061_join7 :
    blockEstimate 4866 1061 2085 384 = 1016271555921 :=
  block_append moment_4866_1061_part8 moment_4866_1061_join6 rfl rfl rfl
private theorem moment_4866_1061_join8 :
    blockEstimate 4866 1061 1701 768 = 1559362389681 :=
  block_append moment_4866_1061_join5 moment_4866_1061_join7 rfl rfl rfl
private theorem moment_4866_1061_join9 :
    blockEstimate 4866 1061 1061 1408 = 1751921763921 :=
  block_append moment_4866_1061_join3 moment_4866_1061_join8 rfl rfl rfl
private theorem moment_4866_1061_join10 :
    blockEstimate 4866 1061 2597 256 = 985855109760 :=
  block_append moment_4866_1061_part12 moment_4866_1061_part13 rfl rfl rfl
private theorem moment_4866_1061_join11 :
    blockEstimate 4866 1061 2469 384 = 1420341059520 :=
  block_append moment_4866_1061_part11 moment_4866_1061_join10 rfl rfl rfl
private theorem moment_4866_1061_join12 :
    blockEstimate 4866 1061 2981 256 = 1161714969216 :=
  block_append moment_4866_1061_part15 moment_4866_1061_part16 rfl rfl rfl
private theorem moment_4866_1061_join13 :
    blockEstimate 4866 1061 2853 384 = 1704175427520 :=
  block_append moment_4866_1061_part14 moment_4866_1061_join12 rfl rfl rfl
private theorem moment_4866_1061_join14 :
    blockEstimate 4866 1061 2469 768 = 3124516487040 :=
  block_append moment_4866_1061_join11 moment_4866_1061_join13 rfl rfl rfl
private theorem moment_4866_1061_join15 :
    blockEstimate 4866 1061 3365 256 = 1257396513408 :=
  block_append moment_4866_1061_part18 moment_4866_1061_part19 rfl rfl rfl
private theorem moment_4866_1061_join16 :
    blockEstimate 4866 1061 3237 384 = 1867742322624 :=
  block_append moment_4866_1061_part17 moment_4866_1061_join15 rfl rfl rfl
private theorem moment_4866_1061_join17 :
    blockEstimate 4866 1061 3749 256 = 1272899742336 :=
  block_append moment_4866_1061_part21 moment_4866_1061_part22 rfl rfl rfl
private theorem moment_4866_1061_join18 :
    blockEstimate 4866 1061 3621 384 = 1911041744832 :=
  block_append moment_4866_1061_part20 moment_4866_1061_join17 rfl rfl rfl
private theorem moment_4866_1061_join19 :
    blockEstimate 4866 1061 3237 768 = 3778784067456 :=
  block_append moment_4866_1061_join16 moment_4866_1061_join18 rfl rfl rfl
private theorem moment_4866_1061_join20 :
    blockEstimate 4866 1061 2469 1536 = 6903300554496 :=
  block_append moment_4866_1061_join14 moment_4866_1061_join19 rfl rfl rfl
private theorem moment_4866_1061_join21 :
    blockEstimate 4866 1061 1061 2944 = 8655222318417 :=
  block_append moment_4866_1061_join9 moment_4866_1061_join20 rfl rfl rfl
private theorem moment_4866_1061_join22 :
    blockEstimate 4866 1061 4133 256 = 1208224656000 :=
  block_append moment_4866_1061_part24 moment_4866_1061_part25 rfl rfl rfl
private theorem moment_4866_1061_join23 :
    blockEstimate 4866 1061 4005 384 = 1834073694144 :=
  block_append moment_4866_1061_part23 moment_4866_1061_join22 rfl rfl rfl
private theorem moment_4866_1061_join24 :
    blockEstimate 4866 1061 4517 256 = 1063371254400 :=
  block_append moment_4866_1061_part27 moment_4866_1061_part28 rfl rfl rfl
private theorem moment_4866_1061_join25 :
    blockEstimate 4866 1061 4389 384 = 1636838170560 :=
  block_append moment_4866_1061_part26 moment_4866_1061_join24 rfl rfl rfl
private theorem moment_4866_1061_join26 :
    blockEstimate 4866 1061 4005 768 = 3470911864704 :=
  block_append moment_4866_1061_join23 moment_4866_1061_join25 rfl rfl rfl
private theorem moment_4866_1061_join27 :
    blockEstimate 4866 1061 4901 256 = 844656445222 :=
  block_append moment_4866_1061_part30 moment_4866_1061_part31 rfl rfl rfl
private theorem moment_4866_1061_join28 :
    blockEstimate 4866 1061 4773 384 = 1325662442671 :=
  block_append moment_4866_1061_part29 moment_4866_1061_join27 rfl rfl rfl
private theorem moment_4866_1061_join29 :
    blockEstimate 4866 1061 5285 256 = 602585738896 :=
  block_append moment_4866_1061_part33 moment_4866_1061_part34 rfl rfl rfl
private theorem moment_4866_1061_join30 :
    blockEstimate 4866 1061 5157 384 = 964398280412 :=
  block_append moment_4866_1061_part32 moment_4866_1061_join29 rfl rfl rfl
private theorem moment_4866_1061_join31 :
    blockEstimate 4866 1061 4773 768 = 2290060723083 :=
  block_append moment_4866_1061_join28 moment_4866_1061_join30 rfl rfl rfl
private theorem moment_4866_1061_join32 :
    blockEstimate 4866 1061 4005 1536 = 5760972587787 :=
  block_append moment_4866_1061_join26 moment_4866_1061_join31 rfl rfl rfl
private theorem moment_4866_1061_join33 :
    blockEstimate 4866 1061 5669 256 = 374224337162 :=
  block_append moment_4866_1061_part36 moment_4866_1061_part37 rfl rfl rfl
private theorem moment_4866_1061_join34 :
    blockEstimate 4866 1061 5541 384 = 616553144619 :=
  block_append moment_4866_1061_part35 moment_4866_1061_join33 rfl rfl rfl
private theorem moment_4866_1061_join35 :
    blockEstimate 4866 1061 6053 256 = 183658224832 :=
  block_append moment_4866_1061_part39 moment_4866_1061_part40 rfl rfl rfl
private theorem moment_4866_1061_join36 :
    blockEstimate 4866 1061 5925 384 = 319670579305 :=
  block_append moment_4866_1061_part38 moment_4866_1061_join35 rfl rfl rfl
private theorem moment_4866_1061_join37 :
    blockEstimate 4866 1061 5541 768 = 936223723924 :=
  block_append moment_4866_1061_join34 moment_4866_1061_join36 rfl rfl rfl
private theorem moment_4866_1061_join38 :
    blockEstimate 4866 1061 6437 256 = 54497631424 :=
  block_append moment_4866_1061_part42 moment_4866_1061_part43 rfl rfl rfl
private theorem moment_4866_1061_join39 :
    blockEstimate 4866 1061 6309 384 = 109171940128 :=
  block_append moment_4866_1061_part41 moment_4866_1061_join38 rfl rfl rfl
private theorem moment_4866_1061_join40 :
    blockEstimate 4866 1061 6821 167 = 1908890326 :=
  block_append moment_4866_1061_part45 moment_4866_1061_part46 rfl rfl rfl
private theorem moment_4866_1061_join41 :
    blockEstimate 4866 1061 6693 295 = 10270636342 :=
  block_append moment_4866_1061_part44 moment_4866_1061_join40 rfl rfl rfl
private theorem moment_4866_1061_join42 :
    blockEstimate 4866 1061 6309 679 = 119442576470 :=
  block_append moment_4866_1061_join39 moment_4866_1061_join41 rfl rfl rfl
private theorem moment_4866_1061_join43 :
    blockEstimate 4866 1061 5541 1447 = 1055666300394 :=
  block_append moment_4866_1061_join37 moment_4866_1061_join42 rfl rfl rfl
private theorem moment_4866_1061_join44 :
    blockEstimate 4866 1061 4005 2983 = 6816638888181 :=
  block_append moment_4866_1061_join32 moment_4866_1061_join43 rfl rfl rfl
private theorem moment_4866_1061_join45 :
    blockEstimate 4866 1061 1061 5927 = 15471861206598 :=
  block_append moment_4866_1061_join21 moment_4866_1061_join44 rfl rfl rfl

theorem moment_4866_1061 : momentEstimate 4866 1061 = 15471861206598 := moment_4866_1061_join45

private theorem receipt_0_11_2339_0_part0 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 0) 0 128 = 8187487708804675804821234240 := rfl
private theorem receipt_0_11_2339_0_part1 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 0) 128 128 = 6901663671054002406274105920 := rfl
private theorem receipt_0_11_2339_0_part2 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 0) 256 128 = 5689636439572169909439259200 := rfl
private theorem receipt_0_11_2339_0_part3 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 0) 384 128 = 4549212411935773164108694080 := rfl
private theorem receipt_0_11_2339_0_part4 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 0) 512 128 = 3478204493268477209253126720 := rfl
private theorem receipt_0_11_2339_0_part5 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 0) 640 128 = 2474432530917260915950409484 := rfl
private theorem receipt_0_11_2339_0_part6 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 0) 768 128 = 1535724494885756594995968666 := rfl
private theorem receipt_0_11_2339_0_part7 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 0) 896 128 = 659908486524539189798949018 := rfl
private theorem receipt_0_11_2339_0_part8 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 0) 1024 38 = 36317399516756707447702506 := rfl
private theorem receipt_0_11_2339_0_join0 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 0) 0 256 = 15089151379858678211095340160 :=
  phaseBlock_append receipt_0_11_2339_0_part0 receipt_0_11_2339_0_part1 rfl rfl rfl
private theorem receipt_0_11_2339_0_join1 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 0) 256 256 = 10238848851507943073547953280 :=
  phaseBlock_append receipt_0_11_2339_0_part2 receipt_0_11_2339_0_part3 rfl rfl rfl
private theorem receipt_0_11_2339_0_join2 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 0) 0 512 = 25328000231366621284643293440 :=
  phaseBlock_append receipt_0_11_2339_0_join0 receipt_0_11_2339_0_join1 rfl rfl rfl
private theorem receipt_0_11_2339_0_join3 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 0) 512 256 = 5952637024185738125203536204 :=
  phaseBlock_append receipt_0_11_2339_0_part4 receipt_0_11_2339_0_part5 rfl rfl rfl
private theorem receipt_0_11_2339_0_join4 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 0) 896 166 = 696225886041295897246651524 :=
  phaseBlock_append receipt_0_11_2339_0_part7 receipt_0_11_2339_0_part8 rfl rfl rfl
private theorem receipt_0_11_2339_0_join5 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 0) 768 294 = 2231950380927052492242620190 :=
  phaseBlock_append receipt_0_11_2339_0_part6 receipt_0_11_2339_0_join4 rfl rfl rfl
private theorem receipt_0_11_2339_0_join6 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 0) 512 550 = 8184587405112790617446156394 :=
  phaseBlock_append receipt_0_11_2339_0_join3 receipt_0_11_2339_0_join5 rfl rfl rfl
private theorem receipt_0_11_2339_0_join7 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 0) 0 1062 = 33512587636479411902089449834 :=
  phaseBlock_append receipt_0_11_2339_0_join2 receipt_0_11_2339_0_join6 rfl rfl rfl

private theorem receipt_0_11_2339_0 : fastPhase (bank 0 11).shape 179827 2339 32 1 0 1 0 = 33512587636479411902089449834 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_0_11_2339_0_join7

private theorem receipt_0_11_2339_1_part0 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 1) 0 128 = 8177286578111862224148967680 := rfl
private theorem receipt_0_11_2339_1_part1 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 1) 128 128 = 6892028287145035593452368128 := rfl
private theorem receipt_0_11_2339_1_part2 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 1) 256 128 = 5680550188205344081786253568 := rfl
private theorem receipt_0_11_2339_1_part3 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 1) 384 128 = 4540658728491819084712915200 := rfl
private theorem receipt_0_11_2339_1_part4 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 1) 512 128 = 3470166862702473259226181888 := rfl
private theorem receipt_0_11_2339_1_part5 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 1) 640 128 = 2466894486322242976034971350 := rfl
private theorem receipt_0_11_2339_1_part6 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 1) 768 128 = 1528669607158945242399801528 := rfl
private theorem receipt_0_11_2339_1_part7 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 1) 896 128 = 653320370377461938139609558 := rfl
private theorem receipt_0_11_2339_1_part8 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 1) 1024 38 = 34448999373491517825357336 := rfl
private theorem receipt_0_11_2339_1_join0 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 1) 0 256 = 15069314865256897817601335808 :=
  phaseBlock_append receipt_0_11_2339_1_part0 receipt_0_11_2339_1_part1 rfl rfl rfl
private theorem receipt_0_11_2339_1_join1 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 1) 256 256 = 10221208916697163166499168768 :=
  phaseBlock_append receipt_0_11_2339_1_part2 receipt_0_11_2339_1_part3 rfl rfl rfl
private theorem receipt_0_11_2339_1_join2 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 1) 0 512 = 25290523781954060984100504576 :=
  phaseBlock_append receipt_0_11_2339_1_join0 receipt_0_11_2339_1_join1 rfl rfl rfl
private theorem receipt_0_11_2339_1_join3 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 1) 512 256 = 5937061349024716235261153238 :=
  phaseBlock_append receipt_0_11_2339_1_part4 receipt_0_11_2339_1_part5 rfl rfl rfl
private theorem receipt_0_11_2339_1_join4 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 1) 896 166 = 687769369750953455964966894 :=
  phaseBlock_append receipt_0_11_2339_1_part7 receipt_0_11_2339_1_part8 rfl rfl rfl
private theorem receipt_0_11_2339_1_join5 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 1) 768 294 = 2216438976909898698364768422 :=
  phaseBlock_append receipt_0_11_2339_1_part6 receipt_0_11_2339_1_join4 rfl rfl rfl
private theorem receipt_0_11_2339_1_join6 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 1) 512 550 = 8153500325934614933625921660 :=
  phaseBlock_append receipt_0_11_2339_1_join3 receipt_0_11_2339_1_join5 rfl rfl rfl
private theorem receipt_0_11_2339_1_join7 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2339 32 1 0 1 1) 0 1062 = 33444024107888675917726426236 :=
  phaseBlock_append receipt_0_11_2339_1_join2 receipt_0_11_2339_1_join6 rfl rfl rfl

private theorem receipt_0_11_2339_1 : fastPhase (bank 0 11).shape 179827 2339 32 1 0 1 1 = 33444024107888675917726426236 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_0_11_2339_1_join7

private theorem receipt_0_11_2340_0_part0 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 0) 0 128 = 8187560964378168613460821440 := rfl
private theorem receipt_0_11_2340_0_part1 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 0) 128 128 = 6901721005676141603080308160 := rfl
private theorem receipt_0_11_2340_0_part2 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 0) 256 128 = 5689679921927024134564693440 := rfl
private theorem receipt_0_11_2340_0_part3 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 0) 384 128 = 4549244035019041377787282880 := rfl
private theorem receipt_0_11_2340_0_part4 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 0) 512 128 = 3478226174614526332423488960 := rfl
private theorem receipt_0_11_2340_0_part5 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 0) 640 128 = 2474446102999345473177455733 := rfl
private theorem receipt_0_11_2340_0_part6 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 0) 768 128 = 1535731716989682002209453474 := rfl
private theorem receipt_0_11_2340_0_part7 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 0) 896 128 = 659911076567685121708383503 := rfl
private theorem receipt_0_11_2340_0_part8 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 0) 1024 38 = 36317520228477148874402229 := rfl
private theorem receipt_0_11_2340_0_join0 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 0) 0 256 = 15089281970054310216541129600 :=
  phaseBlock_append receipt_0_11_2340_0_part0 receipt_0_11_2340_0_part1 rfl rfl rfl
private theorem receipt_0_11_2340_0_join1 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 0) 256 256 = 10238923956946065512351976320 :=
  phaseBlock_append receipt_0_11_2340_0_part2 receipt_0_11_2340_0_part3 rfl rfl rfl
private theorem receipt_0_11_2340_0_join2 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 0) 0 512 = 25328205927000375728893105920 :=
  phaseBlock_append receipt_0_11_2340_0_join0 receipt_0_11_2340_0_join1 rfl rfl rfl
private theorem receipt_0_11_2340_0_join3 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 0) 512 256 = 5952672277613871805600944693 :=
  phaseBlock_append receipt_0_11_2340_0_part4 receipt_0_11_2340_0_part5 rfl rfl rfl
private theorem receipt_0_11_2340_0_join4 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 0) 896 166 = 696228596796162270582785732 :=
  phaseBlock_append receipt_0_11_2340_0_part7 receipt_0_11_2340_0_part8 rfl rfl rfl
private theorem receipt_0_11_2340_0_join5 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 0) 768 294 = 2231960313785844272792239206 :=
  phaseBlock_append receipt_0_11_2340_0_part6 receipt_0_11_2340_0_join4 rfl rfl rfl
private theorem receipt_0_11_2340_0_join6 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 0) 512 550 = 8184632591399716078393183899 :=
  phaseBlock_append receipt_0_11_2340_0_join3 receipt_0_11_2340_0_join5 rfl rfl rfl
private theorem receipt_0_11_2340_0_join7 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 0) 0 1062 = 33512838518400091807286289819 :=
  phaseBlock_append receipt_0_11_2340_0_join2 receipt_0_11_2340_0_join6 rfl rfl rfl

private theorem receipt_0_11_2340_0 : fastPhase (bank 0 11).shape 179827 2340 32 1 0 1 0 = 33512838518400091807286289819 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_0_11_2340_0_join7

private theorem receipt_0_11_2340_1_part0 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 1) 0 128 = 8177359759253571747165188160 := rfl
private theorem receipt_0_11_2340_1_part1 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 1) 128 128 = 6892085555535534957170159680 := rfl
private theorem receipt_0_11_2340_1_part2 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 1) 256 128 = 5680593612171014328507805760 := rfl
private theorem receipt_0_11_2340_1_part3 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 1) 384 128 = 4540690300671915117493416000 := rfl
private theorem receipt_0_11_2340_1_part4 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 1) 512 128 = 3470188500276160176827150400 := rfl
private theorem receipt_0_11_2340_1_part5 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 1) 640 128 = 2466908021438919980697729490 := rfl
private theorem receipt_0_11_2340_1_part6 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 1) 768 128 = 1528676798815678961116712904 := rfl
private theorem receipt_0_11_2340_1_part7 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 1) 896 128 = 653322936125558866422153674 := rfl
private theorem receipt_0_11_2340_1_part8 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 1) 1024 38 = 34449114002810246051456055 := rfl
private theorem receipt_0_11_2340_1_join0 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 1) 0 256 = 15069445314789106704335347840 :=
  phaseBlock_append receipt_0_11_2340_1_part0 receipt_0_11_2340_1_part1 rfl rfl rfl
private theorem receipt_0_11_2340_1_join1 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 1) 256 256 = 10221283912842929446001221760 :=
  phaseBlock_append receipt_0_11_2340_1_part2 receipt_0_11_2340_1_part3 rfl rfl rfl
private theorem receipt_0_11_2340_1_join2 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 1) 0 512 = 25290729227632036150336569600 :=
  phaseBlock_append receipt_0_11_2340_1_join0 receipt_0_11_2340_1_join1 rfl rfl rfl
private theorem receipt_0_11_2340_1_join3 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 1) 512 256 = 5937096521715080157524879890 :=
  phaseBlock_append receipt_0_11_2340_1_part4 receipt_0_11_2340_1_part5 rfl rfl rfl
private theorem receipt_0_11_2340_1_join4 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 1) 896 166 = 687772050128369112473609729 :=
  phaseBlock_append receipt_0_11_2340_1_part7 receipt_0_11_2340_1_part8 rfl rfl rfl
private theorem receipt_0_11_2340_1_join5 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 1) 768 294 = 2216448848944048073590322633 :=
  phaseBlock_append receipt_0_11_2340_1_part6 receipt_0_11_2340_1_join4 rfl rfl rfl
private theorem receipt_0_11_2340_1_join6 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 1) 512 550 = 8153545370659128231115202523 :=
  phaseBlock_append receipt_0_11_2340_1_join3 receipt_0_11_2340_1_join5 rfl rfl rfl
private theorem receipt_0_11_2340_1_join7 :
    phaseBlock (fastLayer (bank 0 11).shape 179827 2340 32 1 0 1 1) 0 1062 = 33444274598291164381451772123 :=
  phaseBlock_append receipt_0_11_2340_1_join2 receipt_0_11_2340_1_join6 rfl rfl rfl

private theorem receipt_0_11_2340_1 : fastPhase (bank 0 11).shape 179827 2340 32 1 0 1 1 = 33444274598291164381451772123 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_0_11_2340_1_join7

theorem receipt_0_11 : Checked (bank 0 11) 32 0 1 := by
  refine checked_from_values (bank 0 11) 32 0 1
    (P3_7_1.checked (bank 0 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4866_1061)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_11_2339_0 receipt_0_11_2339_1 receipt_0_11_2340_0 receipt_0_11_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_11_2339_0_part0 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 0) 0 128 = 7304385859489288632165223680 := rfl
private theorem receipt_1_11_2339_0_part1 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 0) 128 128 = 6151843782210128618074557696 := rfl
private theorem receipt_1_11_2339_0_part2 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 0) 256 128 = 5067038729048702866992155904 := rfl
private theorem receipt_1_11_2339_0_part3 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 0) 384 128 = 4047846096082531660380130560 := rfl
private theorem receipt_1_11_2339_0_part4 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 0) 512 128 = 3092153835901160845330894080 := rfl
private theorem receipt_1_11_2339_0_part5 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 0) 640 128 = 2197862824043439681153940038 := rfl
private theorem receipt_1_11_2339_0_part6 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 0) 768 128 = 1362887885562846979450643703 := rfl
private theorem receipt_1_11_2339_0_part7 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 0) 896 128 = 585150683920010728421088306 := rfl
private theorem receipt_1_11_2339_0_part8 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 0) 1024 38 = 32182990524847444606753341 := rfl
private theorem receipt_1_11_2339_0_join0 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 0) 0 256 = 13456229641699417250239781376 :=
  phaseBlock_append receipt_1_11_2339_0_part0 receipt_1_11_2339_0_part1 rfl rfl rfl
private theorem receipt_1_11_2339_0_join1 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 0) 256 256 = 9114884825131234527372286464 :=
  phaseBlock_append receipt_1_11_2339_0_part2 receipt_1_11_2339_0_part3 rfl rfl rfl
private theorem receipt_1_11_2339_0_join2 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 0) 0 512 = 22571114466830651777612067840 :=
  phaseBlock_append receipt_1_11_2339_0_join0 receipt_1_11_2339_0_join1 rfl rfl rfl
private theorem receipt_1_11_2339_0_join3 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 0) 512 256 = 5290016659944600526484834118 :=
  phaseBlock_append receipt_1_11_2339_0_part4 receipt_1_11_2339_0_part5 rfl rfl rfl
private theorem receipt_1_11_2339_0_join4 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 0) 896 166 = 617333674444858173027841647 :=
  phaseBlock_append receipt_1_11_2339_0_part7 receipt_1_11_2339_0_part8 rfl rfl rfl
private theorem receipt_1_11_2339_0_join5 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 0) 768 294 = 1980221560007705152478485350 :=
  phaseBlock_append receipt_1_11_2339_0_part6 receipt_1_11_2339_0_join4 rfl rfl rfl
private theorem receipt_1_11_2339_0_join6 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 0) 512 550 = 7270238219952305678963319468 :=
  phaseBlock_append receipt_1_11_2339_0_join3 receipt_1_11_2339_0_join5 rfl rfl rfl
private theorem receipt_1_11_2339_0_join7 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 0) 0 1062 = 29841352686782957456575387308 :=
  phaseBlock_append receipt_1_11_2339_0_join2 receipt_1_11_2339_0_join6 rfl rfl rfl

private theorem receipt_1_11_2339_0 : fastPhase (bank 1 11).shape 179827 2339 32 1 0 2 0 = 29841352686782957456575387308 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_1_11_2339_0_join7

private theorem receipt_1_11_2339_1_part0 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 1) 0 128 = 7295234971368348878210503872 := rfl
private theorem receipt_1_11_2339_1_part1 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 1) 128 128 = 6143213038400191213468431552 := rfl
private theorem receipt_1_11_2339_1_part2 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 1) 256 128 = 5058912001110490464020518080 := rfl
private theorem receipt_1_11_2339_1_part3 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 1) 384 128 = 4040207351390313006614246592 := rfl
private theorem receipt_1_11_2339_1_part4 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 1) 512 128 = 3084987137450395072638686400 := rfl
private theorem receipt_1_11_2339_1_part5 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 1) 640 128 = 2191152329022967795449491793 := rfl
private theorem receipt_1_11_2339_1_part6 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 1) 768 128 = 1356617836029468419237120760 := rfl
private theorem receipt_1_11_2339_1_part7 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 1) 896 128 = 579305412051841366755066408 := rfl
private theorem receipt_1_11_2339_1_part8 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 1) 1024 38 = 30527149524876803170525920 := rfl
private theorem receipt_1_11_2339_1_join0 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 1) 0 256 = 13438448009768540091678935424 :=
  phaseBlock_append receipt_1_11_2339_1_part0 receipt_1_11_2339_1_part1 rfl rfl rfl
private theorem receipt_1_11_2339_1_join1 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 1) 256 256 = 9099119352500803470634764672 :=
  phaseBlock_append receipt_1_11_2339_1_part2 receipt_1_11_2339_1_part3 rfl rfl rfl
private theorem receipt_1_11_2339_1_join2 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 1) 0 512 = 22537567362269343562313700096 :=
  phaseBlock_append receipt_1_11_2339_1_join0 receipt_1_11_2339_1_join1 rfl rfl rfl
private theorem receipt_1_11_2339_1_join3 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 1) 512 256 = 5276139466473362868088178193 :=
  phaseBlock_append receipt_1_11_2339_1_part4 receipt_1_11_2339_1_part5 rfl rfl rfl
private theorem receipt_1_11_2339_1_join4 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 1) 896 166 = 609832561576718169925592328 :=
  phaseBlock_append receipt_1_11_2339_1_part7 receipt_1_11_2339_1_part8 rfl rfl rfl
private theorem receipt_1_11_2339_1_join5 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 1) 768 294 = 1966450397606186589162713088 :=
  phaseBlock_append receipt_1_11_2339_1_part6 receipt_1_11_2339_1_join4 rfl rfl rfl
private theorem receipt_1_11_2339_1_join6 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 1) 512 550 = 7242589864079549457250891281 :=
  phaseBlock_append receipt_1_11_2339_1_join3 receipt_1_11_2339_1_join5 rfl rfl rfl
private theorem receipt_1_11_2339_1_join7 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2339 32 1 0 2 1) 0 1062 = 29780157226348893019564591377 :=
  phaseBlock_append receipt_1_11_2339_1_join2 receipt_1_11_2339_1_join6 rfl rfl rfl

private theorem receipt_1_11_2339_1 : fastPhase (bank 1 11).shape 179827 2339 32 1 0 2 1 = 29780157226348893019564591377 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_1_11_2339_1_join7

private theorem receipt_1_11_2340_0_part0 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 0) 0 128 = 7304451214057688943405950400 := rfl
private theorem receipt_1_11_2340_0_part1 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 0) 128 128 = 6151894888100964341709063616 := rfl
private theorem receipt_1_11_2340_0_part2 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 0) 256 128 = 5067077453528487634947777984 := rfl
private theorem receipt_1_11_2340_0_part3 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 0) 384 128 = 4047874234211997895785874880 := rfl
private theorem receipt_1_11_2340_0_part4 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 0) 512 128 = 3092173110971523986186397120 := rfl
private theorem receipt_1_11_2340_0_part5 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 0) 640 128 = 2197874879285557953689357940 := rfl
private theorem receipt_1_11_2340_0_part6 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 0) 768 128 = 1362894294941530148620425682 := rfl
private theorem receipt_1_11_2340_0_part7 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 0) 896 128 = 585152980581418154824024694 := rfl
private theorem receipt_1_11_2340_0_part8 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 0) 1024 38 = 32183097494749235824370733 := rfl
private theorem receipt_1_11_2340_0_join0 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 0) 0 256 = 13456346102158653285115014016 :=
  phaseBlock_append receipt_1_11_2340_0_part0 receipt_1_11_2340_0_part1 rfl rfl rfl
private theorem receipt_1_11_2340_0_join1 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 0) 256 256 = 9114951687740485530733652864 :=
  phaseBlock_append receipt_1_11_2340_0_part2 receipt_1_11_2340_0_part3 rfl rfl rfl
private theorem receipt_1_11_2340_0_join2 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 0) 0 512 = 22571297789899138815848666880 :=
  phaseBlock_append receipt_1_11_2340_0_join0 receipt_1_11_2340_0_join1 rfl rfl rfl
private theorem receipt_1_11_2340_0_join3 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 0) 512 256 = 5290047990257081939875755060 :=
  phaseBlock_append receipt_1_11_2340_0_part4 receipt_1_11_2340_0_part5 rfl rfl rfl
private theorem receipt_1_11_2340_0_join4 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 0) 896 166 = 617336078076167390648395427 :=
  phaseBlock_append receipt_1_11_2340_0_part7 receipt_1_11_2340_0_part8 rfl rfl rfl
private theorem receipt_1_11_2340_0_join5 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 0) 768 294 = 1980230373017697539268821109 :=
  phaseBlock_append receipt_1_11_2340_0_part6 receipt_1_11_2340_0_join4 rfl rfl rfl
private theorem receipt_1_11_2340_0_join6 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 0) 512 550 = 7270278363274779479144576169 :=
  phaseBlock_append receipt_1_11_2340_0_join3 receipt_1_11_2340_0_join5 rfl rfl rfl
private theorem receipt_1_11_2340_0_join7 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 0) 0 1062 = 29841576153173918294993243049 :=
  phaseBlock_append receipt_1_11_2340_0_join2 receipt_1_11_2340_0_join6 rfl rfl rfl

private theorem receipt_1_11_2340_0 : fastPhase (bank 1 11).shape 179827 2340 32 1 0 2 0 = 29841576153173918294993243049 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_1_11_2340_0_join7

private theorem receipt_1_11_2340_1_part0 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 1) 0 128 = 7295300259084864248449973184 := rfl
private theorem receipt_1_11_2340_1_part1 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 1) 128 128 = 6143264084904138308276378560 := rfl
private theorem receipt_1_11_2340_1_part2 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 1) 256 128 = 5058950673324368883605044160 := rfl
private theorem receipt_1_11_2340_1_part3 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 1) 384 128 = 4040235444033234676656446400 := rfl
private theorem receipt_1_11_2340_1_part4 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 1) 512 128 = 3085006373474343245281377216 := rfl
private theorem receipt_1_11_2340_1_part5 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 1) 640 128 = 2191164351348745846246213012 := rfl
private theorem receipt_1_11_2340_1_part6 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 1) 768 128 = 1356624218344201393076572908 := rfl
private theorem receipt_1_11_2340_1_part7 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 1) 896 128 = 579307687156350786394028885 := rfl
private theorem receipt_1_11_2340_1_part8 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 1) 1024 38 = 30527251104320668865936838 := rfl
private theorem receipt_1_11_2340_1_join0 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 1) 0 256 = 13438564343989002556726351744 :=
  phaseBlock_append receipt_1_11_2340_1_part0 receipt_1_11_2340_1_part1 rfl rfl rfl
private theorem receipt_1_11_2340_1_join1 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 1) 256 256 = 9099186117357603560261490560 :=
  phaseBlock_append receipt_1_11_2340_1_part2 receipt_1_11_2340_1_part3 rfl rfl rfl
private theorem receipt_1_11_2340_1_join2 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 1) 0 512 = 22537750461346606116987842304 :=
  phaseBlock_append receipt_1_11_2340_1_join0 receipt_1_11_2340_1_join1 rfl rfl rfl
private theorem receipt_1_11_2340_1_join3 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 1) 512 256 = 5276170724823089091527590228 :=
  phaseBlock_append receipt_1_11_2340_1_part4 receipt_1_11_2340_1_part5 rfl rfl rfl
private theorem receipt_1_11_2340_1_join4 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 1) 896 166 = 609834938260671455259965723 :=
  phaseBlock_append receipt_1_11_2340_1_part7 receipt_1_11_2340_1_part8 rfl rfl rfl
private theorem receipt_1_11_2340_1_join5 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 1) 768 294 = 1966459156604872848336538631 :=
  phaseBlock_append receipt_1_11_2340_1_part6 receipt_1_11_2340_1_join4 rfl rfl rfl
private theorem receipt_1_11_2340_1_join6 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 1) 512 550 = 7242629881427961939864128859 :=
  phaseBlock_append receipt_1_11_2340_1_join3 receipt_1_11_2340_1_join5 rfl rfl rfl
private theorem receipt_1_11_2340_1_join7 :
    phaseBlock (fastLayer (bank 1 11).shape 179827 2340 32 1 0 2 1) 0 1062 = 29780380342774568056851971163 :=
  phaseBlock_append receipt_1_11_2340_1_join2 receipt_1_11_2340_1_join6 rfl rfl rfl

private theorem receipt_1_11_2340_1 : fastPhase (bank 1 11).shape 179827 2340 32 1 0 2 1 = 29780380342774568056851971163 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_1_11_2340_1_join7

theorem receipt_1_11 : Checked (bank 1 11) 32 0 2 := by
  refine checked_from_values (bank 1 11) 32 0 2
    (P3_7_1.checked (bank 1 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4866_1061)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_11_2339_0 receipt_1_11_2339_1 receipt_1_11_2340_0 receipt_1_11_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_11_2339_0_part0 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 0) 0 128 = 3670239314031770263304337984 := rfl
private theorem receipt_2_11_2339_0_part1 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 0) 128 128 = 3070887528675366657054726720 := rfl
private theorem receipt_2_11_2339_0_part2 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 0) 256 128 = 2512743497278027029248391744 := rfl
private theorem receipt_2_11_2339_0_part3 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 0) 384 128 = 1994075105376790003989977664 := rfl
private theorem receipt_2_11_2339_0_part4 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 0) 512 128 = 1513186265773974037409593920 := rfl
private theorem receipt_2_11_2339_0_part5 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 0) 640 128 = 1068416800784258697126628518 := rfl
private theorem receipt_2_11_2339_0_part6 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 0) 768 128 = 658142636995339994108660211 := rfl
private theorem receipt_2_11_2339_0_part7 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 0) 896 128 = 280772077160113381076109168 := rfl
private theorem receipt_2_11_2339_0_part8 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 0) 1024 38 = 15368219731520320881554517 := rfl
private theorem receipt_2_11_2339_0_join0 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 0) 0 256 = 6741126842707136920359064704 :=
  phaseBlock_append receipt_2_11_2339_0_part0 receipt_2_11_2339_0_part1 rfl rfl rfl
private theorem receipt_2_11_2339_0_join1 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 0) 256 256 = 4506818602654817033238369408 :=
  phaseBlock_append receipt_2_11_2339_0_part2 receipt_2_11_2339_0_part3 rfl rfl rfl
private theorem receipt_2_11_2339_0_join2 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 0) 0 512 = 11247945445361953953597434112 :=
  phaseBlock_append receipt_2_11_2339_0_join0 receipt_2_11_2339_0_join1 rfl rfl rfl
private theorem receipt_2_11_2339_0_join3 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 0) 512 256 = 2581603066558232734536222438 :=
  phaseBlock_append receipt_2_11_2339_0_part4 receipt_2_11_2339_0_part5 rfl rfl rfl
private theorem receipt_2_11_2339_0_join4 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 0) 896 166 = 296140296891633701957663685 :=
  phaseBlock_append receipt_2_11_2339_0_part7 receipt_2_11_2339_0_part8 rfl rfl rfl
private theorem receipt_2_11_2339_0_join5 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 0) 768 294 = 954282933886973696066323896 :=
  phaseBlock_append receipt_2_11_2339_0_part6 receipt_2_11_2339_0_join4 rfl rfl rfl
private theorem receipt_2_11_2339_0_join6 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 0) 512 550 = 3535886000445206430602546334 :=
  phaseBlock_append receipt_2_11_2339_0_join3 receipt_2_11_2339_0_join5 rfl rfl rfl
private theorem receipt_2_11_2339_0_join7 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 0) 0 1062 = 14783831445807160384199980446 :=
  phaseBlock_append receipt_2_11_2339_0_join2 receipt_2_11_2339_0_join6 rfl rfl rfl

private theorem receipt_2_11_2339_0 : fastPhase (bank 2 11).shape 179827 2339 32 1 0 7 0 = 14783831445807160384199980446 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_2_11_2339_0_join7

private theorem receipt_2_11_2339_1_part0 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 1) 0 128 = 3665453621198934064571575872 := rfl
private theorem receipt_2_11_2339_1_part1 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 1) 128 128 = 3066421534494470393315282496 := rfl
private theorem receipt_2_11_2339_1_part2 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 1) 256 128 = 2508583900952609378537254464 := rfl
private theorem receipt_2_11_2339_1_part3 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 1) 384 128 = 1990208882207141984061951552 := rfl
private theorem receipt_2_11_2339_1_part4 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 1) 512 128 = 1509600664800781546127552064 := rfl
private theorem receipt_2_11_2339_1_part5 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 1) 640 128 = 1065099341823097489865337309 := rfl
private theorem receipt_2_11_2339_1_part6 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 1) 768 128 = 655081103851741962913085352 := rfl
private theorem receipt_2_11_2339_1_part7 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 1) 896 128 = 277954518158140967390427510 := rfl
private theorem receipt_2_11_2339_1_part8 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 1) 1024 38 = 14576993793760853949929232 := rfl
private theorem receipt_2_11_2339_1_join0 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 1) 0 256 = 6731875155693404457886858368 :=
  phaseBlock_append receipt_2_11_2339_1_part0 receipt_2_11_2339_1_part1 rfl rfl rfl
private theorem receipt_2_11_2339_1_join1 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 1) 256 256 = 4498792783159751362599206016 :=
  phaseBlock_append receipt_2_11_2339_1_part2 receipt_2_11_2339_1_part3 rfl rfl rfl
private theorem receipt_2_11_2339_1_join2 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 1) 0 512 = 11230667938853155820486064384 :=
  phaseBlock_append receipt_2_11_2339_1_join0 receipt_2_11_2339_1_join1 rfl rfl rfl
private theorem receipt_2_11_2339_1_join3 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 1) 512 256 = 2574700006623879035992889373 :=
  phaseBlock_append receipt_2_11_2339_1_part4 receipt_2_11_2339_1_part5 rfl rfl rfl
private theorem receipt_2_11_2339_1_join4 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 1) 896 166 = 292531511951901821340356742 :=
  phaseBlock_append receipt_2_11_2339_1_part7 receipt_2_11_2339_1_part8 rfl rfl rfl
private theorem receipt_2_11_2339_1_join5 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 1) 768 294 = 947612615803643784253442094 :=
  phaseBlock_append receipt_2_11_2339_1_part6 receipt_2_11_2339_1_join4 rfl rfl rfl
private theorem receipt_2_11_2339_1_join6 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 1) 512 550 = 3522312622427522820246331467 :=
  phaseBlock_append receipt_2_11_2339_1_join3 receipt_2_11_2339_1_join5 rfl rfl rfl
private theorem receipt_2_11_2339_1_join7 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2339 32 1 0 7 1) 0 1062 = 14752980561280678640732395851 :=
  phaseBlock_append receipt_2_11_2339_1_join2 receipt_2_11_2339_1_join6 rfl rfl rfl

private theorem receipt_2_11_2339_1 : fastPhase (bank 2 11).shape 179827 2339 32 1 0 7 1 = 14752980561280678640732395851 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_2_11_2339_1_join7

private theorem receipt_2_11_2340_0_part0 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 0) 0 128 = 3670272154041820480802317824 := rfl
private theorem receipt_2_11_2340_0_part1 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 0) 128 128 = 3070913040898600299771512320 := rfl
private theorem receipt_2_11_2340_0_part2 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 0) 256 128 = 2512762701680129525328029184 := rfl
private theorem receipt_2_11_2340_0_part3 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 0) 384 128 = 1994088967736212989798024704 := rfl
private theorem receipt_2_11_2340_0_part4 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 0) 512 128 = 1513195698900832129651729920 := rfl
private theorem receipt_2_11_2340_0_part5 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 0) 640 128 = 1068422661494047752671009565 := rfl
private theorem receipt_2_11_2340_0_part6 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 0) 768 128 = 658145732395931856703236016 := rfl
private theorem receipt_2_11_2340_0_part7 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 0) 896 128 = 280773179280111131475723965 := rfl
private theorem receipt_2_11_2340_0_part8 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 0) 1024 38 = 15368270812901052599440404 := rfl
private theorem receipt_2_11_2340_0_join0 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 0) 0 256 = 6741185194940420780573830144 :=
  phaseBlock_append receipt_2_11_2340_0_part0 receipt_2_11_2340_0_part1 rfl rfl rfl
private theorem receipt_2_11_2340_0_join1 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 0) 256 256 = 4506851669416342515126053888 :=
  phaseBlock_append receipt_2_11_2340_0_part2 receipt_2_11_2340_0_part3 rfl rfl rfl
private theorem receipt_2_11_2340_0_join2 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 0) 0 512 = 11248036864356763295699884032 :=
  phaseBlock_append receipt_2_11_2340_0_join0 receipt_2_11_2340_0_join1 rfl rfl rfl
private theorem receipt_2_11_2340_0_join3 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 0) 512 256 = 2581618360394879882322739485 :=
  phaseBlock_append receipt_2_11_2340_0_part4 receipt_2_11_2340_0_part5 rfl rfl rfl
private theorem receipt_2_11_2340_0_join4 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 0) 896 166 = 296141450093012184075164369 :=
  phaseBlock_append receipt_2_11_2340_0_part7 receipt_2_11_2340_0_part8 rfl rfl rfl
private theorem receipt_2_11_2340_0_join5 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 0) 768 294 = 954287182488944040778400385 :=
  phaseBlock_append receipt_2_11_2340_0_part6 receipt_2_11_2340_0_join4 rfl rfl rfl
private theorem receipt_2_11_2340_0_join6 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 0) 512 550 = 3535905542883823923101139870 :=
  phaseBlock_append receipt_2_11_2340_0_join3 receipt_2_11_2340_0_join5 rfl rfl rfl
private theorem receipt_2_11_2340_0_join7 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 0) 0 1062 = 14783942407240587218801023902 :=
  phaseBlock_append receipt_2_11_2340_0_join2 receipt_2_11_2340_0_join6 rfl rfl rfl

private theorem receipt_2_11_2340_0 : fastPhase (bank 2 11).shape 179827 2340 32 1 0 7 0 = 14783942407240587218801023902 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_2_11_2340_0_join7

private theorem receipt_2_11_2340_1_part0 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 1) 0 128 = 3665486425937126866022542464 := rfl
private theorem receipt_2_11_2340_1_part1 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 1) 128 128 = 3066447015761125047087942784 := rfl
private theorem receipt_2_11_2340_1_part2 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 1) 256 128 = 2508603078444266401648929920 := rfl
private theorem receipt_2_11_2340_1_part3 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 1) 384 128 = 1990222721439868443626146944 := rfl
private theorem receipt_2_11_2340_1_part4 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 1) 512 128 = 1509610078329003853639724160 := rfl
private theorem receipt_2_11_2340_1_part5 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 1) 640 128 = 1065105186226478681416236022 := rfl
private theorem receipt_2_11_2340_1_part6 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 1) 768 128 = 655084186023105306628171644 := rfl
private theorem receipt_2_11_2340_1_part7 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 1) 896 128 = 277955609882641319553687869 := rfl
private theorem receipt_2_11_2340_1_part8 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 1) 1024 38 = 14577042299285958876765237 := rfl
private theorem receipt_2_11_2340_1_join0 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 1) 0 256 = 6731933441698251913110485248 :=
  phaseBlock_append receipt_2_11_2340_1_part0 receipt_2_11_2340_1_part1 rfl rfl rfl
private theorem receipt_2_11_2340_1_join1 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 1) 256 256 = 4498825799884134845275076864 :=
  phaseBlock_append receipt_2_11_2340_1_part2 receipt_2_11_2340_1_part3 rfl rfl rfl
private theorem receipt_2_11_2340_1_join2 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 1) 0 512 = 11230759241582386758385562112 :=
  phaseBlock_append receipt_2_11_2340_1_join0 receipt_2_11_2340_1_join1 rfl rfl rfl
private theorem receipt_2_11_2340_1_join3 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 1) 512 256 = 2574715264555482535055960182 :=
  phaseBlock_append receipt_2_11_2340_1_part4 receipt_2_11_2340_1_part5 rfl rfl rfl
private theorem receipt_2_11_2340_1_join4 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 1) 896 166 = 292532652181927278430453106 :=
  phaseBlock_append receipt_2_11_2340_1_part7 receipt_2_11_2340_1_part8 rfl rfl rfl
private theorem receipt_2_11_2340_1_join5 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 1) 768 294 = 947616838205032585058624750 :=
  phaseBlock_append receipt_2_11_2340_1_part6 receipt_2_11_2340_1_join4 rfl rfl rfl
private theorem receipt_2_11_2340_1_join6 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 1) 512 550 = 3522332102760515120114584932 :=
  phaseBlock_append receipt_2_11_2340_1_join3 receipt_2_11_2340_1_join5 rfl rfl rfl
private theorem receipt_2_11_2340_1_join7 :
    phaseBlock (fastLayer (bank 2 11).shape 179827 2340 32 1 0 7 1) 0 1062 = 14753091344342901878500147044 :=
  phaseBlock_append receipt_2_11_2340_1_join2 receipt_2_11_2340_1_join6 rfl rfl rfl

private theorem receipt_2_11_2340_1 : fastPhase (bank 2 11).shape 179827 2340 32 1 0 7 1 = 14753091344342901878500147044 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_2_11_2340_1_join7

theorem receipt_2_11 : Checked (bank 2 11) 32 0 7 := by
  refine checked_from_values (bank 2 11) 32 0 7
    (P3_7_1.checked (bank 2 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4866_1061)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_11_2339_0 receipt_2_11_2339_1 receipt_2_11_2340_0 receipt_2_11_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_11_2339_0_part0 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 0) 0 128 = 393458211017991363902771232 := rfl
private theorem receipt_3_11_2339_0_part1 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 0) 128 128 = 311183717225977364927316000 := rfl
private theorem receipt_3_11_2339_0_part2 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 0) 256 128 = 234718386661604003067719712 := rfl
private theorem receipt_3_11_2339_0_part3 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 0) 384 128 = 164331657074328183847149600 := rfl
private theorem receipt_3_11_2339_0_part4 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 0) 512 128 = 100290000660265945561354272 := rfl
private theorem receipt_3_11_2339_0_part5 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 0) 640 128 = 42856933534133288848015392 := rfl
private theorem receipt_3_11_2339_0_part6 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 0) 768 42 = 2702225880435784621570281 := rfl
private theorem receipt_3_11_2339_0_join0 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 0) 128 256 = 545902103887581367995035712 :=
  phaseBlock_append receipt_3_11_2339_0_part1 receipt_3_11_2339_0_part2 rfl rfl rfl
private theorem receipt_3_11_2339_0_join1 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 0) 0 384 = 939360314905572731897806944 :=
  phaseBlock_append receipt_3_11_2339_0_part0 receipt_3_11_2339_0_join0 rfl rfl rfl
private theorem receipt_3_11_2339_0_join2 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 0) 384 256 = 264621657734594129408503872 :=
  phaseBlock_append receipt_3_11_2339_0_part3 receipt_3_11_2339_0_part4 rfl rfl rfl
private theorem receipt_3_11_2339_0_join3 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 0) 640 170 = 45559159414569073469585673 :=
  phaseBlock_append receipt_3_11_2339_0_part5 receipt_3_11_2339_0_part6 rfl rfl rfl
private theorem receipt_3_11_2339_0_join4 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 0) 384 426 = 310180817149163202878089545 :=
  phaseBlock_append receipt_3_11_2339_0_join2 receipt_3_11_2339_0_join3 rfl rfl rfl
private theorem receipt_3_11_2339_0_join5 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 0) 0 810 = 1249541132054735934775896489 :=
  phaseBlock_append receipt_3_11_2339_0_join1 receipt_3_11_2339_0_join4 rfl rfl rfl

private theorem receipt_3_11_2339_0 : fastPhase (bank 3 11).shape 179827 2339 32 1 1 1 0 = 1249541132054735934775896489 :=
  phase_of_block (n := 810) (by decide +kernel) receipt_3_11_2339_0_join5

private theorem receipt_3_11_2339_1_part0 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 1) 0 128 = 392801763800023537492050336 := rfl
private theorem receipt_3_11_2339_1_part1 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 1) 128 128 = 310569806728837958042988960 := rfl
private theorem receipt_3_11_2339_1_part2 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 1) 256 128 = 234149296461683785858294176 := rfl
private theorem receipt_3_11_2339_1_part3 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 1) 384 128 = 163809646355274494488023456 := rfl
private theorem receipt_3_11_2339_1_part4 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 1) 512 128 = 99817304289875455395365280 := rfl
private theorem receipt_3_11_2339_1_part5 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 1) 640 128 = 42435762141244767525990816 := rfl
private theorem receipt_3_11_2339_1_part6 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 1) 768 42 = 2575626485870023926046833 := rfl
private theorem receipt_3_11_2339_1_join0 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 1) 128 256 = 544719103190521743901283136 :=
  phaseBlock_append receipt_3_11_2339_1_part1 receipt_3_11_2339_1_part2 rfl rfl rfl
private theorem receipt_3_11_2339_1_join1 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 1) 0 384 = 937520866990545281393333472 :=
  phaseBlock_append receipt_3_11_2339_1_part0 receipt_3_11_2339_1_join0 rfl rfl rfl
private theorem receipt_3_11_2339_1_join2 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 1) 384 256 = 263626950645149949883388736 :=
  phaseBlock_append receipt_3_11_2339_1_part3 receipt_3_11_2339_1_part4 rfl rfl rfl
private theorem receipt_3_11_2339_1_join3 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 1) 640 170 = 45011388627114791452037649 :=
  phaseBlock_append receipt_3_11_2339_1_part5 receipt_3_11_2339_1_part6 rfl rfl rfl
private theorem receipt_3_11_2339_1_join4 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 1) 384 426 = 308638339272264741335426385 :=
  phaseBlock_append receipt_3_11_2339_1_join2 receipt_3_11_2339_1_join3 rfl rfl rfl
private theorem receipt_3_11_2339_1_join5 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2339 32 1 1 1 1) 0 810 = 1246159206262810022728759857 :=
  phaseBlock_append receipt_3_11_2339_1_join1 receipt_3_11_2339_1_join4 rfl rfl rfl

private theorem receipt_3_11_2339_1 : fastPhase (bank 3 11).shape 179827 2339 32 1 1 1 1 = 1246159206262810022728759857 :=
  phase_of_block (n := 810) (by decide +kernel) receipt_3_11_2339_1_join5

private theorem receipt_3_11_2340_0_part0 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 0) 0 128 = 393461572722983539531496256 := rfl
private theorem receipt_3_11_2340_0_part1 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 0) 128 128 = 311185950551870597357550400 := rfl
private theorem receipt_3_11_2340_0_part2 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 0) 256 128 = 234719759453138091552979776 := rfl
private theorem receipt_3_11_2340_0_part3 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 0) 384 128 = 164332406418837707890015040 := rfl
private theorem receipt_3_11_2340_0_part4 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 0) 512 128 = 100290333177047123771439936 := rfl
private theorem receipt_3_11_2340_0_part5 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 0) 640 128 = 42857025662931228497722176 := rfl
private theorem receipt_3_11_2340_0_part6 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 0) 768 42 = 2702229354972728135929248 := rfl
private theorem receipt_3_11_2340_0_join0 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 0) 128 256 = 545905710005008688910530176 :=
  phaseBlock_append receipt_3_11_2340_0_part1 receipt_3_11_2340_0_part2 rfl rfl rfl
private theorem receipt_3_11_2340_0_join1 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 0) 0 384 = 939367282727992228442026432 :=
  phaseBlock_append receipt_3_11_2340_0_part0 receipt_3_11_2340_0_join0 rfl rfl rfl
private theorem receipt_3_11_2340_0_join2 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 0) 384 256 = 264622739595884831661454976 :=
  phaseBlock_append receipt_3_11_2340_0_part3 receipt_3_11_2340_0_part4 rfl rfl rfl
private theorem receipt_3_11_2340_0_join3 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 0) 640 170 = 45559255017903956633651424 :=
  phaseBlock_append receipt_3_11_2340_0_part5 receipt_3_11_2340_0_part6 rfl rfl rfl
private theorem receipt_3_11_2340_0_join4 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 0) 384 426 = 310181994613788788295106400 :=
  phaseBlock_append receipt_3_11_2340_0_join2 receipt_3_11_2340_0_join3 rfl rfl rfl
private theorem receipt_3_11_2340_0_join5 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 0) 0 810 = 1249549277341781016737132832 :=
  phaseBlock_append receipt_3_11_2340_0_join1 receipt_3_11_2340_0_join4 rfl rfl rfl

private theorem receipt_3_11_2340_0 : fastPhase (bank 3 11).shape 179827 2340 32 1 1 1 0 = 1249549277341781016737132832 :=
  phase_of_block (n := 810) (by decide +kernel) receipt_3_11_2340_0_join5

private theorem receipt_3_11_2340_1_part0 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 1) 0 128 = 392805119050937463806110656 := rfl
private theorem receipt_3_11_2340_1_part1 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 1) 128 128 = 310572035045530592031386560 := rfl
private theorem receipt_3_11_2340_1_part2 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 1) 256 128 = 234150665518909410797890496 := rfl
private theorem receipt_3_11_2340_1_part3 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 1) 384 128 = 163810393072138503069936576 := rfl
private theorem receipt_3_11_2340_1_part4 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 1) 512 128 = 99817635119195573585849280 := rfl
private theorem receipt_3_11_2340_1_part5 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 1) 640 128 = 42435853358032669125094336 := rfl
private theorem receipt_3_11_2340_1_part6 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 1) 768 42 = 2575629802510036000738268 := rfl
private theorem receipt_3_11_2340_1_join0 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 1) 128 256 = 544722700564440002829277056 :=
  phaseBlock_append receipt_3_11_2340_1_part1 receipt_3_11_2340_1_part2 rfl rfl rfl
private theorem receipt_3_11_2340_1_join1 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 1) 0 384 = 937527819615377466635387712 :=
  phaseBlock_append receipt_3_11_2340_1_part0 receipt_3_11_2340_1_join0 rfl rfl rfl
private theorem receipt_3_11_2340_1_join2 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 1) 384 256 = 263628028191334076655785856 :=
  phaseBlock_append receipt_3_11_2340_1_part3 receipt_3_11_2340_1_part4 rfl rfl rfl
private theorem receipt_3_11_2340_1_join3 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 1) 640 170 = 45011483160542705125832604 :=
  phaseBlock_append receipt_3_11_2340_1_part5 receipt_3_11_2340_1_part6 rfl rfl rfl
private theorem receipt_3_11_2340_1_join4 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 1) 384 426 = 308639511351876781781618460 :=
  phaseBlock_append receipt_3_11_2340_1_join2 receipt_3_11_2340_1_join3 rfl rfl rfl
private theorem receipt_3_11_2340_1_join5 :
    phaseBlock (fastLayer (bank 3 11).shape 179827 2340 32 1 1 1 1) 0 810 = 1246167330967254248417006172 :=
  phaseBlock_append receipt_3_11_2340_1_join1 receipt_3_11_2340_1_join4 rfl rfl rfl

private theorem receipt_3_11_2340_1 : fastPhase (bank 3 11).shape 179827 2340 32 1 1 1 1 = 1246167330967254248417006172 :=
  phase_of_block (n := 810) (by decide +kernel) receipt_3_11_2340_1_join5

theorem receipt_3_11 : Checked (bank 3 11) 32 1 1 := by
  refine checked_from_values (bank 3 11) 32 1 1
    (P3_7_1.checked (bank 3 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3870_809)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_11_2339_0 receipt_3_11_2339_1 receipt_3_11_2340_0 receipt_3_11_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_12_2339_0_part0 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 0) 0 128 = 5286436476717344419183071393 := rfl
private theorem receipt_0_12_2339_0_part1 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 0) 128 128 = 4300434079381937548544071179 := rfl
private theorem receipt_0_12_2339_0_part2 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 0) 256 128 = 3379445275144556240235044514 := rfl
private theorem receipt_0_12_2339_0_part3 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 0) 384 128 = 2521245913393108753446006910 := rfl
private theorem receipt_0_12_2339_0_part4 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 0) 512 128 = 1723618375162950303547707108 := rfl
private theorem receipt_0_12_2339_0_part5 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 0) 640 128 = 984351630405974511567849921 := rfl
private theorem receipt_0_12_2339_0_part6 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 0) 768 123 = 301625862827205676702419834 := rfl
private theorem receipt_0_12_2339_0_join0 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 0) 128 256 = 7679879354526493788779115693 :=
  phaseBlock_append receipt_0_12_2339_0_part1 receipt_0_12_2339_0_part2 rfl rfl rfl
private theorem receipt_0_12_2339_0_join1 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 0) 0 384 = 12966315831243838207962187086 :=
  phaseBlock_append receipt_0_12_2339_0_part0 receipt_0_12_2339_0_join0 rfl rfl rfl
private theorem receipt_0_12_2339_0_join2 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 0) 384 256 = 4244864288556059056993714018 :=
  phaseBlock_append receipt_0_12_2339_0_part3 receipt_0_12_2339_0_part4 rfl rfl rfl
private theorem receipt_0_12_2339_0_join3 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 0) 640 251 = 1285977493233180188270269755 :=
  phaseBlock_append receipt_0_12_2339_0_part5 receipt_0_12_2339_0_part6 rfl rfl rfl
private theorem receipt_0_12_2339_0_join4 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 0) 384 507 = 5530841781789239245263983773 :=
  phaseBlock_append receipt_0_12_2339_0_join2 receipt_0_12_2339_0_join3 rfl rfl rfl
private theorem receipt_0_12_2339_0_join5 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 0) 0 891 = 18497157613033077453226170859 :=
  phaseBlock_append receipt_0_12_2339_0_join1 receipt_0_12_2339_0_join4 rfl rfl rfl

private theorem receipt_0_12_2339_0 : fastPhase (bank 0 12).shape 179827 2339 31 1 0 1 0 = 18497157613033077453226170859 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_0_12_2339_0_join5

private theorem receipt_0_12_2339_1_part0 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 1) 0 128 = 5278576743065150458999693236 := rfl
private theorem receipt_0_12_2339_1_part1 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 1) 128 128 = 4293073626887909333083755834 := rfl
private theorem receipt_0_12_2339_1_part2 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 1) 256 128 = 3372567296811429420623469372 := rfl
private theorem receipt_0_12_2339_1_part3 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 1) 384 128 = 2514833652278509568621890761 := rfl
private theorem receipt_0_12_2339_1_part4 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 1) 512 128 = 1717655124399607168868513190 := rfl
private theorem receipt_0_12_2339_1_part5 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 1) 640 128 = 978820733130352944075356469 := rfl
private theorem receipt_0_12_2339_1_part6 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 1) 768 123 = 296702923123397493801648144 := rfl
private theorem receipt_0_12_2339_1_join0 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 1) 128 256 = 7665640923699338753707225206 :=
  phaseBlock_append receipt_0_12_2339_1_part1 receipt_0_12_2339_1_part2 rfl rfl rfl
private theorem receipt_0_12_2339_1_join1 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 1) 0 384 = 12944217666764489212706918442 :=
  phaseBlock_append receipt_0_12_2339_1_part0 receipt_0_12_2339_1_join0 rfl rfl rfl
private theorem receipt_0_12_2339_1_join2 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 1) 384 256 = 4232488776678116737490403951 :=
  phaseBlock_append receipt_0_12_2339_1_part3 receipt_0_12_2339_1_part4 rfl rfl rfl
private theorem receipt_0_12_2339_1_join3 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 1) 640 251 = 1275523656253750437877004613 :=
  phaseBlock_append receipt_0_12_2339_1_part5 receipt_0_12_2339_1_part6 rfl rfl rfl
private theorem receipt_0_12_2339_1_join4 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 1) 384 507 = 5508012432931867175367408564 :=
  phaseBlock_append receipt_0_12_2339_1_join2 receipt_0_12_2339_1_join3 rfl rfl rfl
private theorem receipt_0_12_2339_1_join5 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2339 31 1 0 1 1) 0 891 = 18452230099696356388074327006 :=
  phaseBlock_append receipt_0_12_2339_1_join1 receipt_0_12_2339_1_join4 rfl rfl rfl

private theorem receipt_0_12_2339_1 : fastPhase (bank 0 12).shape 179827 2339 31 1 0 1 1 = 18452230099696356388074327006 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_0_12_2339_1_join5

private theorem receipt_0_12_2340_0_part0 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 0) 0 128 = 5286483488240062677078697659 := rfl
private theorem receipt_0_12_2340_0_part1 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 0) 128 128 = 4300469054411402163535517063 := rfl
private theorem receipt_0_12_2340_0_part2 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 0) 256 128 = 3379470082618508034425063466 := rfl
private theorem receipt_0_12_2340_0_part3 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 0) 384 128 = 2521262341050305309015555027 := rfl
private theorem receipt_0_12_2340_0_part4 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 0) 512 128 = 1723628128112149334233208061 := rfl
private theorem receipt_0_12_2340_0_part5 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 0) 640 128 = 984356331785581447296842502 := rfl
private theorem receipt_0_12_2340_0_part6 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 0) 768 123 = 301627054054606894759139115 := rfl
private theorem receipt_0_12_2340_0_join0 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 0) 128 256 = 7679939137029910197960580529 :=
  phaseBlock_append receipt_0_12_2340_0_part1 receipt_0_12_2340_0_part2 rfl rfl rfl
private theorem receipt_0_12_2340_0_join1 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 0) 0 384 = 12966422625269972875039278188 :=
  phaseBlock_append receipt_0_12_2340_0_part0 receipt_0_12_2340_0_join0 rfl rfl rfl
private theorem receipt_0_12_2340_0_join2 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 0) 384 256 = 4244890469162454643248763088 :=
  phaseBlock_append receipt_0_12_2340_0_part3 receipt_0_12_2340_0_part4 rfl rfl rfl
private theorem receipt_0_12_2340_0_join3 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 0) 640 251 = 1285983385840188342055981617 :=
  phaseBlock_append receipt_0_12_2340_0_part5 receipt_0_12_2340_0_part6 rfl rfl rfl
private theorem receipt_0_12_2340_0_join4 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 0) 384 507 = 5530873855002642985304744705 :=
  phaseBlock_append receipt_0_12_2340_0_join2 receipt_0_12_2340_0_join3 rfl rfl rfl
private theorem receipt_0_12_2340_0_join5 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 0) 0 891 = 18497296480272615860344022893 :=
  phaseBlock_append receipt_0_12_2340_0_join1 receipt_0_12_2340_0_join4 rfl rfl rfl

private theorem receipt_0_12_2340_0 : fastPhase (bank 0 12).shape 179827 2340 31 1 0 1 0 = 18497296480272615860344022893 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_0_12_2340_0_join5

private theorem receipt_0_12_2340_1_part0 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 1) 0 128 = 5278623697145509551330056160 := rfl
private theorem receipt_0_12_2340_1_part1 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 1) 128 128 = 4293108551851795530184188208 := rfl
private theorem receipt_0_12_2340_1_part2 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 1) 256 128 = 3372592061220055598781671702 := rfl
private theorem receipt_0_12_2340_1_part3 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 1) 384 128 = 2514850043493559117898696838 := rfl
private theorem receipt_0_12_2340_1_part4 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 1) 512 128 = 1717664847154365079496359302 := rfl
private theorem receipt_0_12_2340_1_part5 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 1) 640 128 = 978825410187044633808226471 := rfl
private theorem receipt_0_12_2340_1_part6 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 1) 768 123 = 296704096163277450751112366 := rfl
private theorem receipt_0_12_2340_1_join0 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 1) 128 256 = 7665700613071851128965859910 :=
  phaseBlock_append receipt_0_12_2340_1_part1 receipt_0_12_2340_1_part2 rfl rfl rfl
private theorem receipt_0_12_2340_1_join1 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 1) 0 384 = 12944324310217360680295916070 :=
  phaseBlock_append receipt_0_12_2340_1_part0 receipt_0_12_2340_1_join0 rfl rfl rfl
private theorem receipt_0_12_2340_1_join2 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 1) 384 256 = 4232514890647924197395056140 :=
  phaseBlock_append receipt_0_12_2340_1_part3 receipt_0_12_2340_1_part4 rfl rfl rfl
private theorem receipt_0_12_2340_1_join3 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 1) 640 251 = 1275529506350322084559338837 :=
  phaseBlock_append receipt_0_12_2340_1_part5 receipt_0_12_2340_1_part6 rfl rfl rfl
private theorem receipt_0_12_2340_1_join4 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 1) 384 507 = 5508044396998246281954394977 :=
  phaseBlock_append receipt_0_12_2340_1_join2 receipt_0_12_2340_1_join3 rfl rfl rfl
private theorem receipt_0_12_2340_1_join5 :
    phaseBlock (fastLayer (bank 0 12).shape 179827 2340 31 1 0 1 1) 0 891 = 18452368707215606962250311047 :=
  phaseBlock_append receipt_0_12_2340_1_join1 receipt_0_12_2340_1_join4 rfl rfl rfl

private theorem receipt_0_12_2340_1 : fastPhase (bank 0 12).shape 179827 2340 31 1 0 1 1 = 18452368707215606962250311047 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_0_12_2340_1_join5

theorem receipt_0_12 : Checked (bank 0 12) 31 0 1 := by
  refine checked_from_values (bank 0 12) 31 0 1
    (P3_7_1.checked (bank 0 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4255_890)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_12_2339_0 receipt_0_12_2339_1 receipt_0_12_2340_0 receipt_0_12_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_12_2339_0_part0 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 0) 0 128 = 4764876863560856713003551645 := rfl
private theorem receipt_1_12_2339_0_part1 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 0) 128 128 = 3872821905068470740271232955 := rfl
private theorem receipt_1_12_2339_0_part2 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 0) 256 128 = 3040795132177306014485611344 := rfl
private theorem receipt_1_12_2339_0_part3 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 0) 384 128 = 2266646271435959425724515640 := rfl
private theorem receipt_1_12_2339_0_part4 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 0) 512 128 = 1548237726692925885464965022 := rfl
private theorem receipt_1_12_2339_0_part5 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 0) 640 128 = 883444611153912728734163641 := rfl
private theorem receipt_1_12_2339_0_part6 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 0) 768 123 = 270499460934554980540517304 := rfl
private theorem receipt_1_12_2339_0_join0 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 0) 128 256 = 6913617037245776754756844299 :=
  phaseBlock_append receipt_1_12_2339_0_part1 receipt_1_12_2339_0_part2 rfl rfl rfl
private theorem receipt_1_12_2339_0_join1 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 0) 0 384 = 11678493900806633467760395944 :=
  phaseBlock_append receipt_1_12_2339_0_part0 receipt_1_12_2339_0_join0 rfl rfl rfl
private theorem receipt_1_12_2339_0_join2 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 0) 384 256 = 3814883998128885311189480662 :=
  phaseBlock_append receipt_1_12_2339_0_part3 receipt_1_12_2339_0_part4 rfl rfl rfl
private theorem receipt_1_12_2339_0_join3 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 0) 640 251 = 1153944072088467709274680945 :=
  phaseBlock_append receipt_1_12_2339_0_part5 receipt_1_12_2339_0_part6 rfl rfl rfl
private theorem receipt_1_12_2339_0_join4 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 0) 384 507 = 4968828070217353020464161607 :=
  phaseBlock_append receipt_1_12_2339_0_join2 receipt_1_12_2339_0_join3 rfl rfl rfl
private theorem receipt_1_12_2339_0_join5 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 0) 0 891 = 16647321971023986488224557551 :=
  phaseBlock_append receipt_1_12_2339_0_join1 receipt_1_12_2339_0_join4 rfl rfl rfl

private theorem receipt_1_12_2339_0 : fastPhase (bank 1 12).shape 179827 2339 31 1 0 2 0 = 16647321971023986488224557551 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_1_12_2339_0_join5

private theorem receipt_1_12_2339_1_part0 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 1) 0 128 = 4757760617197724725961422514 := rfl
private theorem receipt_1_12_2339_1_part1 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 1) 128 128 = 3866167360370290176840037392 := rfl
private theorem receipt_1_12_2339_1_part2 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 1) 256 128 = 3034586002667811560898567566 := rfl
private theorem receipt_1_12_2339_1_part3 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 1) 384 128 = 2260866367508074325607030887 := rfl
private theorem receipt_1_12_2339_1_part4 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 1) 512 128 = 1542870955477917105120236107 := rfl
private theorem receipt_1_12_2339_1_part5 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 1) 640 128 = 878474976307694182657168997 := rfl
private theorem receipt_1_12_2339_1_part6 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 1) 768 123 = 266083335785239265736295848 := rfl
private theorem receipt_1_12_2339_1_join0 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 1) 128 256 = 6900753363038101737738604958 :=
  phaseBlock_append receipt_1_12_2339_1_part1 receipt_1_12_2339_1_part2 rfl rfl rfl
private theorem receipt_1_12_2339_1_join1 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 1) 0 384 = 11658513980235826463700027472 :=
  phaseBlock_append receipt_1_12_2339_1_part0 receipt_1_12_2339_1_join0 rfl rfl rfl
private theorem receipt_1_12_2339_1_join2 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 1) 384 256 = 3803737322985991430727266994 :=
  phaseBlock_append receipt_1_12_2339_1_part3 receipt_1_12_2339_1_part4 rfl rfl rfl
private theorem receipt_1_12_2339_1_join3 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 1) 640 251 = 1144558312092933448393464845 :=
  phaseBlock_append receipt_1_12_2339_1_part5 receipt_1_12_2339_1_part6 rfl rfl rfl
private theorem receipt_1_12_2339_1_join4 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 1) 384 507 = 4948295635078924879120731839 :=
  phaseBlock_append receipt_1_12_2339_1_join2 receipt_1_12_2339_1_join3 rfl rfl rfl
private theorem receipt_1_12_2339_1_join5 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2339 31 1 0 2 1) 0 891 = 16606809615314751342820759311 :=
  phaseBlock_append receipt_1_12_2339_1_join1 receipt_1_12_2339_1_join4 rfl rfl rfl

private theorem receipt_1_12_2339_1 : fastPhase (bank 1 12).shape 179827 2339 31 1 0 2 1 = 16606809615314751342820759311 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_1_12_2339_1_join5

private theorem receipt_1_12_2340_0_part0 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 0) 0 128 = 4764919237182050438299829868 := rfl
private theorem receipt_1_12_2340_0_part1 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 0) 128 128 = 3872853402583903670316669867 := rfl
private theorem receipt_1_12_2340_0_part2 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 0) 256 128 = 3040817453901067316201745215 := rfl
private theorem receipt_1_12_2340_0_part3 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 0) 384 128 = 2266661040338064464618650157 := rfl
private theorem receipt_1_12_2340_0_part4 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 0) 512 128 = 1548246487362821625178618143 := rfl
private theorem receipt_1_12_2340_0_part5 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 0) 640 128 = 883448830646194287236983796 := rfl
private theorem receipt_1_12_2340_0_part6 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 0) 768 123 = 270500529244370155137872362 := rfl
private theorem receipt_1_12_2340_0_join0 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 0) 128 256 = 6913670856484970986518415082 :=
  phaseBlock_append receipt_1_12_2340_0_part1 receipt_1_12_2340_0_part2 rfl rfl rfl
private theorem receipt_1_12_2340_0_join1 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 0) 0 384 = 11678590093667021424818244950 :=
  phaseBlock_append receipt_1_12_2340_0_part0 receipt_1_12_2340_0_join0 rfl rfl rfl
private theorem receipt_1_12_2340_0_join2 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 0) 384 256 = 3814907527700886089797268300 :=
  phaseBlock_append receipt_1_12_2340_0_part3 receipt_1_12_2340_0_part4 rfl rfl rfl
private theorem receipt_1_12_2340_0_join3 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 0) 640 251 = 1153949359890564442374856158 :=
  phaseBlock_append receipt_1_12_2340_0_part5 receipt_1_12_2340_0_part6 rfl rfl rfl
private theorem receipt_1_12_2340_0_join4 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 0) 384 507 = 4968856887591450532172124458 :=
  phaseBlock_append receipt_1_12_2340_0_join2 receipt_1_12_2340_0_join3 rfl rfl rfl
private theorem receipt_1_12_2340_0_join5 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 0) 0 891 = 16647446981258471956990369408 :=
  phaseBlock_append receipt_1_12_2340_0_join1 receipt_1_12_2340_0_join4 rfl rfl rfl

private theorem receipt_1_12_2340_0 : fastPhase (bank 1 12).shape 179827 2340 31 1 0 2 0 = 16647446981258471956990369408 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_1_12_2340_0_join5

private theorem receipt_1_12_2340_1_part0 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 1) 0 128 = 4757802938759233981621495312 := rfl
private theorem receipt_1_12_2340_1_part1 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 1) 128 128 = 3866198812586729447207736549 := rfl
private theorem receipt_1_12_2340_1_part2 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 1) 256 128 = 3034608285491743989941191908 := rfl
private theorem receipt_1_12_2340_1_part3 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 1) 384 128 = 2260881103548850333175046044 := rfl
private theorem receipt_1_12_2340_1_part4 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 1) 512 128 = 1542879688967120877504288061 := rfl
private theorem receipt_1_12_2340_1_part5 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 1) 640 128 = 878479173942781405056514308 := rfl
private theorem receipt_1_12_2340_1_part6 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 1) 768 123 = 266084387779244109683270105 := rfl
private theorem receipt_1_12_2340_1_join0 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 1) 128 256 = 6900807098078473437148928457 :=
  phaseBlock_append receipt_1_12_2340_1_part1 receipt_1_12_2340_1_part2 rfl rfl rfl
private theorem receipt_1_12_2340_1_join1 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 1) 0 384 = 11658610036837707418770423769 :=
  phaseBlock_append receipt_1_12_2340_1_part0 receipt_1_12_2340_1_join0 rfl rfl rfl
private theorem receipt_1_12_2340_1_join2 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 1) 384 256 = 3803760792515971210679334105 :=
  phaseBlock_append receipt_1_12_2340_1_part3 receipt_1_12_2340_1_part4 rfl rfl rfl
private theorem receipt_1_12_2340_1_join3 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 1) 640 251 = 1144563561722025514739784413 :=
  phaseBlock_append receipt_1_12_2340_1_part5 receipt_1_12_2340_1_part6 rfl rfl rfl
private theorem receipt_1_12_2340_1_join4 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 1) 384 507 = 4948324354237996725419118518 :=
  phaseBlock_append receipt_1_12_2340_1_join2 receipt_1_12_2340_1_join3 rfl rfl rfl
private theorem receipt_1_12_2340_1_join5 :
    phaseBlock (fastLayer (bank 1 12).shape 179827 2340 31 1 0 2 1) 0 891 = 16606934391075704144189542287 :=
  phaseBlock_append receipt_1_12_2340_1_join1 receipt_1_12_2340_1_join4 rfl rfl rfl

private theorem receipt_1_12_2340_1 : fastPhase (bank 1 12).shape 179827 2340 31 1 0 2 1 = 16606934391075704144189542287 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_1_12_2340_1_join5

theorem receipt_1_12 : Checked (bank 1 12) 31 0 2 := by
  refine checked_from_values (bank 1 12) 31 0 2
    (P3_7_1.checked (bank 1 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4255_890)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_12_2339_0 receipt_1_12_2339_1 receipt_1_12_2340_0 receipt_1_12_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_12_2339_0_part0 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 0) 0 128 = 2585656325259536988497124960 := rfl
private theorem receipt_2_12_2339_0_part1 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 0) 128 128 = 2088717543784441298582294112 := rfl
private theorem receipt_2_12_2339_0_part2 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 0) 256 128 = 1629902308825290062578810464 := rfl
private theorem receipt_2_12_2339_0_part3 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 0) 384 128 = 1207457389098326260696100448 := rfl
private theorem receipt_2_12_2339_0_part4 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 0) 512 128 = 819666406355001620545842012 := rfl
private theorem receipt_2_12_2339_0_part5 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 0) 640 128 = 464850095276838019228208301 := rfl
private theorem receipt_2_12_2339_0_part6 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 0) 768 123 = 141543134984046066920060154 := rfl
private theorem receipt_2_12_2339_0_join0 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 0) 128 256 = 3718619852609731361161104576 :=
  phaseBlock_append receipt_2_12_2339_0_part1 receipt_2_12_2339_0_part2 rfl rfl rfl
private theorem receipt_2_12_2339_0_join1 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 0) 0 384 = 6304276177869268349658229536 :=
  phaseBlock_append receipt_2_12_2339_0_part0 receipt_2_12_2339_0_join0 rfl rfl rfl
private theorem receipt_2_12_2339_0_join2 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 0) 384 256 = 2027123795453327881241942460 :=
  phaseBlock_append receipt_2_12_2339_0_part3 receipt_2_12_2339_0_part4 rfl rfl rfl
private theorem receipt_2_12_2339_0_join3 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 0) 640 251 = 606393230260884086148268455 :=
  phaseBlock_append receipt_2_12_2339_0_part5 receipt_2_12_2339_0_part6 rfl rfl rfl
private theorem receipt_2_12_2339_0_join4 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 0) 384 507 = 2633517025714211967390210915 :=
  phaseBlock_append receipt_2_12_2339_0_join2 receipt_2_12_2339_0_join3 rfl rfl rfl
private theorem receipt_2_12_2339_0_join5 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 0) 0 891 = 8937793203583480317048440451 :=
  phaseBlock_append receipt_2_12_2339_0_join1 receipt_2_12_2339_0_join4 rfl rfl rfl

private theorem receipt_2_12_2339_0 : fastPhase (bank 2 12).shape 179827 2339 31 1 0 7 0 = 8937793203583480317048440451 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_2_12_2339_0_join5

private theorem receipt_2_12_2339_1_part0 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 1) 0 128 = 2581670861684979286489586592 := rfl
private theorem receipt_2_12_2339_1_part1 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 1) 128 128 = 2085028166041739873372801952 := rfl
private theorem receipt_2_12_2339_1_part2 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 1) 256 128 = 1626495562221361833046686624 := rfl
private theorem receipt_2_12_2339_1_part3 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 1) 384 128 = 1204320101018252425658919840 := rfl
private theorem receipt_2_12_2339_1_part4 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 1) 512 128 = 816785683775539177181898099 := rfl
private theorem receipt_2_12_2339_1_part5 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 1) 640 128 = 462213318467968168755504225 := rfl
private theorem receipt_2_12_2339_1_part6 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 1) 768 123 = 139227709474408329854596800 := rfl
private theorem receipt_2_12_2339_1_join0 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 1) 128 256 = 3711523728263101706419488576 :=
  phaseBlock_append receipt_2_12_2339_1_part1 receipt_2_12_2339_1_part2 rfl rfl rfl
private theorem receipt_2_12_2339_1_join1 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 1) 0 384 = 6293194589948080992909075168 :=
  phaseBlock_append receipt_2_12_2339_1_part0 receipt_2_12_2339_1_join0 rfl rfl rfl
private theorem receipt_2_12_2339_1_join2 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 1) 384 256 = 2021105784793791602840817939 :=
  phaseBlock_append receipt_2_12_2339_1_part3 receipt_2_12_2339_1_part4 rfl rfl rfl
private theorem receipt_2_12_2339_1_join3 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 1) 640 251 = 601441027942376498610101025 :=
  phaseBlock_append receipt_2_12_2339_1_part5 receipt_2_12_2339_1_part6 rfl rfl rfl
private theorem receipt_2_12_2339_1_join4 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 1) 384 507 = 2622546812736168101450918964 :=
  phaseBlock_append receipt_2_12_2339_1_join2 receipt_2_12_2339_1_join3 rfl rfl rfl
private theorem receipt_2_12_2339_1_join5 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2339 31 1 0 7 1) 0 891 = 8915741402684249094359994132 :=
  phaseBlock_append receipt_2_12_2339_1_join1 receipt_2_12_2339_1_join4 rfl rfl rfl

private theorem receipt_2_12_2339_1 : fastPhase (bank 2 12).shape 179827 2339 31 1 0 7 1 = 8915741402684249094359994132 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_2_12_2339_1_join5

private theorem receipt_2_12_2340_0_part0 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 0) 0 128 = 2585679106923314314544856000 := rfl
private theorem receipt_2_12_2340_0_part1 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 0) 128 128 = 2088734404658116626136644544 := rfl
private theorem receipt_2_12_2340_0_part2 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 0) 256 128 = 1629914208893061681879694272 := rfl
private theorem receipt_2_12_2340_0_part3 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 0) 384 128 = 1207465232698283923921714112 := rfl
private theorem receipt_2_12_2340_0_part4 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 0) 512 128 = 819671042247852740199336537 := rfl
private theorem receipt_2_12_2340_0_part5 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 0) 640 128 = 464852315701589046227315406 := rfl
private theorem receipt_2_12_2340_0_part6 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 0) 768 123 = 141543694038362850525105267 := rfl
private theorem receipt_2_12_2340_0_join0 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 0) 128 256 = 3718648613551178308016338816 :=
  phaseBlock_append receipt_2_12_2340_0_part1 receipt_2_12_2340_0_part2 rfl rfl rfl
private theorem receipt_2_12_2340_0_join1 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 0) 0 384 = 6304327720474492622561194816 :=
  phaseBlock_append receipt_2_12_2340_0_part0 receipt_2_12_2340_0_join0 rfl rfl rfl
private theorem receipt_2_12_2340_0_join2 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 0) 384 256 = 2027136274946136664121050649 :=
  phaseBlock_append receipt_2_12_2340_0_part3 receipt_2_12_2340_0_part4 rfl rfl rfl
private theorem receipt_2_12_2340_0_join3 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 0) 640 251 = 606396009739951896752420673 :=
  phaseBlock_append receipt_2_12_2340_0_part5 receipt_2_12_2340_0_part6 rfl rfl rfl
private theorem receipt_2_12_2340_0_join4 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 0) 384 507 = 2633532284686088560873471322 :=
  phaseBlock_append receipt_2_12_2340_0_join2 receipt_2_12_2340_0_join3 rfl rfl rfl
private theorem receipt_2_12_2340_0_join5 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 0) 0 891 = 8937860005160581183434666138 :=
  phaseBlock_append receipt_2_12_2340_0_join1 receipt_2_12_2340_0_join4 rfl rfl rfl

private theorem receipt_2_12_2340_0 : fastPhase (bank 2 12).shape 179827 2340 31 1 0 7 0 = 8937860005160581183434666138 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_2_12_2340_0_join5

private theorem receipt_2_12_2340_1_part0 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 1) 0 128 = 2581693614265639370071247232 := rfl
private theorem receipt_2_12_2340_1_part1 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 1) 128 128 = 2085045001855155070154549632 := rfl
private theorem receipt_2_12_2340_1_part2 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 1) 256 128 = 1626507440977107909726095744 := rfl
private theorem receipt_2_12_2340_1_part3 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 1) 384 128 = 1204327926786728761638906240 := rfl
private theorem receipt_2_12_2340_1_part4 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 1) 512 128 = 816790305061098989952222972 := rfl
private theorem receipt_2_12_2340_1_part5 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 1) 640 128 = 462215527286184324291019375 := rfl
private theorem receipt_2_12_2340_1_part6 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 1) 768 123 = 139228259971537436840660978 := rfl
private theorem receipt_2_12_2340_1_join0 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 1) 128 256 = 3711552442832262979880645376 :=
  phaseBlock_append receipt_2_12_2340_1_part1 receipt_2_12_2340_1_part2 rfl rfl rfl
private theorem receipt_2_12_2340_1_join1 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 1) 0 384 = 6293246057097902349951892608 :=
  phaseBlock_append receipt_2_12_2340_1_part0 receipt_2_12_2340_1_join0 rfl rfl rfl
private theorem receipt_2_12_2340_1_join2 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 1) 384 256 = 2021118231847827751591129212 :=
  phaseBlock_append receipt_2_12_2340_1_part3 receipt_2_12_2340_1_part4 rfl rfl rfl
private theorem receipt_2_12_2340_1_join3 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 1) 640 251 = 601443787257721761131680353 :=
  phaseBlock_append receipt_2_12_2340_1_part5 receipt_2_12_2340_1_part6 rfl rfl rfl
private theorem receipt_2_12_2340_1_join4 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 1) 384 507 = 2622562019105549512722809565 :=
  phaseBlock_append receipt_2_12_2340_1_join2 receipt_2_12_2340_1_join3 rfl rfl rfl
private theorem receipt_2_12_2340_1_join5 :
    phaseBlock (fastLayer (bank 2 12).shape 179827 2340 31 1 0 7 1) 0 891 = 8915808076203451862674702173 :=
  phaseBlock_append receipt_2_12_2340_1_join1 receipt_2_12_2340_1_join4 rfl rfl rfl

private theorem receipt_2_12_2340_1 : fastPhase (bank 2 12).shape 179827 2340 31 1 0 7 1 = 8915808076203451862674702173 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_2_12_2340_1_join5

theorem receipt_2_12 : Checked (bank 2 12) 31 0 7 := by
  refine checked_from_values (bank 2 12) 31 0 7
    (P3_7_1.checked (bank 2 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4235_890)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_12_2339_0 receipt_2_12_2339_1 receipt_2_12_2340_0 receipt_2_12_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_12_2339_0_part0 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 0) 0 128 = 472820821309455629799533472 := rfl
private theorem receipt_3_12_2339_0_part1 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 0) 128 128 = 385604427266594919935523744 := rfl
private theorem receipt_3_12_2339_0_part2 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 0) 256 128 = 303969653145375125421837216 := rfl
private theorem receipt_3_12_2339_0_part3 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 0) 384 128 = 228143786107002378082999200 := rfl
private theorem receipt_3_12_2339_0_part4 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 0) 512 128 = 158351368242181256037952416 := rfl
private theorem receipt_3_12_2339_0_part5 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 0) 640 128 = 94814206043055613269408672 := rfl
private theorem receipt_3_12_2339_0_part6 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 0) 768 128 = 37751379875149409193200544 := rfl
private theorem receipt_3_12_2339_0_part7 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 0) 896 29 = 1310059959865952916070821 := rfl
private theorem receipt_3_12_2339_0_join0 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 0) 0 256 = 858425248576050549735057216 :=
  phaseBlock_append receipt_3_12_2339_0_part0 receipt_3_12_2339_0_part1 rfl rfl rfl
private theorem receipt_3_12_2339_0_join1 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 0) 256 256 = 532113439252377503504836416 :=
  phaseBlock_append receipt_3_12_2339_0_part2 receipt_3_12_2339_0_part3 rfl rfl rfl
private theorem receipt_3_12_2339_0_join2 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 0) 0 512 = 1390538687828428053239893632 :=
  phaseBlock_append receipt_3_12_2339_0_join0 receipt_3_12_2339_0_join1 rfl rfl rfl
private theorem receipt_3_12_2339_0_join3 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 0) 512 256 = 253165574285236869307361088 :=
  phaseBlock_append receipt_3_12_2339_0_part4 receipt_3_12_2339_0_part5 rfl rfl rfl
private theorem receipt_3_12_2339_0_join4 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 0) 768 157 = 39061439835015362109271365 :=
  phaseBlock_append receipt_3_12_2339_0_part6 receipt_3_12_2339_0_part7 rfl rfl rfl
private theorem receipt_3_12_2339_0_join5 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 0) 512 413 = 292227014120252231416632453 :=
  phaseBlock_append receipt_3_12_2339_0_join3 receipt_3_12_2339_0_join4 rfl rfl rfl
private theorem receipt_3_12_2339_0_join6 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 0) 0 925 = 1682765701948680284656526085 :=
  phaseBlock_append receipt_3_12_2339_0_join2 receipt_3_12_2339_0_join5 rfl rfl rfl

private theorem receipt_3_12_2339_0 : fastPhase (bank 3 12).shape 179827 2339 31 1 1 1 0 = 1682765701948680284656526085 :=
  phase_of_block (n := 925) (by decide +kernel) receipt_3_12_2339_0_join6

private theorem receipt_3_12_2339_1_part0 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 1) 0 128 = 472127290362344378932977696 := rfl
private theorem receipt_3_12_2339_1_part1 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 1) 128 128 = 384951879475931665131261984 := rfl
private theorem receipt_3_12_2339_1_part2 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 1) 256 128 = 303360021207012596056834080 := rfl
private theorem receipt_3_12_2339_1_part3 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 1) 384 128 = 227578980125435103947075616 := rfl
private theorem receipt_3_12_2339_1_part4 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 1) 512 128 = 157833275807438332474335264 := rfl
private theorem receipt_3_12_2339_1_part5 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 1) 640 128 = 94344692307593466315280416 := rfl
private theorem receipt_3_12_2339_1_part6 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 1) 768 128 = 37332287630744560720248864 := rfl
private theorem receipt_3_12_2339_1_part7 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 1) 896 29 = 1222303446732972880435005 := rfl
private theorem receipt_3_12_2339_1_join0 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 1) 0 256 = 857079169838276044064239680 :=
  phaseBlock_append receipt_3_12_2339_1_part0 receipt_3_12_2339_1_part1 rfl rfl rfl
private theorem receipt_3_12_2339_1_join1 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 1) 256 256 = 530939001332447700003909696 :=
  phaseBlock_append receipt_3_12_2339_1_part2 receipt_3_12_2339_1_part3 rfl rfl rfl
private theorem receipt_3_12_2339_1_join2 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 1) 0 512 = 1388018171170723744068149376 :=
  phaseBlock_append receipt_3_12_2339_1_join0 receipt_3_12_2339_1_join1 rfl rfl rfl
private theorem receipt_3_12_2339_1_join3 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 1) 512 256 = 252177968115031798789615680 :=
  phaseBlock_append receipt_3_12_2339_1_part4 receipt_3_12_2339_1_part5 rfl rfl rfl
private theorem receipt_3_12_2339_1_join4 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 1) 768 157 = 38554591077477533600683869 :=
  phaseBlock_append receipt_3_12_2339_1_part6 receipt_3_12_2339_1_part7 rfl rfl rfl
private theorem receipt_3_12_2339_1_join5 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 1) 512 413 = 290732559192509332390299549 :=
  phaseBlock_append receipt_3_12_2339_1_join3 receipt_3_12_2339_1_join4 rfl rfl rfl
private theorem receipt_3_12_2339_1_join6 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2339 31 1 1 1 1) 0 925 = 1678750730363233076458448925 :=
  phaseBlock_append receipt_3_12_2339_1_join2 receipt_3_12_2339_1_join5 rfl rfl rfl

private theorem receipt_3_12_2339_1 : fastPhase (bank 3 12).shape 179827 2339 31 1 1 1 1 = 1678750730363233076458448925 :=
  phase_of_block (n := 925) (by decide +kernel) receipt_3_12_2339_1_join6

private theorem receipt_3_12_2340_0_part0 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 0) 0 128 = 472824894578260304583283872 := rfl
private theorem receipt_3_12_2340_0_part1 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 0) 128 128 = 385607268995374200365589664 := rfl
private theorem receipt_3_12_2340_0_part2 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 0) 256 128 = 303971524363139899479356576 := rfl
private theorem receipt_3_12_2340_0_part3 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 0) 384 128 = 228144920834057419881497760 := rfl
private theorem receipt_3_12_2340_0_part4 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 0) 512 128 = 158351973760442564693759136 := rfl
private theorem receipt_3_12_2340_0_part5 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 0) 640 128 = 94814463165488142469850272 := rfl
private theorem receipt_3_12_2340_0_part6 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 0) 768 128 = 37751443214325187462575264 := rfl
private theorem receipt_3_12_2340_0_part7 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 0) 896 29 = 1310061168330425055047741 := rfl
private theorem receipt_3_12_2340_0_join0 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 0) 0 256 = 858432163573634504948873536 :=
  phaseBlock_append receipt_3_12_2340_0_part0 receipt_3_12_2340_0_part1 rfl rfl rfl
private theorem receipt_3_12_2340_0_join1 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 0) 256 256 = 532116445197197319360854336 :=
  phaseBlock_append receipt_3_12_2340_0_part2 receipt_3_12_2340_0_part3 rfl rfl rfl
private theorem receipt_3_12_2340_0_join2 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 0) 0 512 = 1390548608770831824309727872 :=
  phaseBlock_append receipt_3_12_2340_0_join0 receipt_3_12_2340_0_join1 rfl rfl rfl
private theorem receipt_3_12_2340_0_join3 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 0) 512 256 = 253166436925930707163609408 :=
  phaseBlock_append receipt_3_12_2340_0_part4 receipt_3_12_2340_0_part5 rfl rfl rfl
private theorem receipt_3_12_2340_0_join4 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 0) 768 157 = 39061504382655612517623005 :=
  phaseBlock_append receipt_3_12_2340_0_part6 receipt_3_12_2340_0_part7 rfl rfl rfl
private theorem receipt_3_12_2340_0_join5 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 0) 512 413 = 292227941308586319681232413 :=
  phaseBlock_append receipt_3_12_2340_0_join3 receipt_3_12_2340_0_join4 rfl rfl rfl
private theorem receipt_3_12_2340_0_join6 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 0) 0 925 = 1682776550079418143990960285 :=
  phaseBlock_append receipt_3_12_2340_0_join2 receipt_3_12_2340_0_join5 rfl rfl rfl

private theorem receipt_3_12_2340_0 : fastPhase (bank 3 12).shape 179827 2340 31 1 1 1 0 = 1682776550079418143990960285 :=
  phase_of_block (n := 925) (by decide +kernel) receipt_3_12_2340_0_join6

private theorem receipt_3_12_2340_1_part0 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 1) 0 128 = 472131356728679686035640096 := rfl
private theorem receipt_3_12_2340_1_part1 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 1) 128 128 = 384954715705024801569480480 := rfl
private theorem receipt_3_12_2340_1_part2 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 1) 256 128 = 303361888178389051113778976 := rfl
private theorem receipt_3_12_2340_1_part3 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 1) 384 128 = 227580111711555474395610912 := rfl
private theorem receipt_3_12_2340_1_part4 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 1) 512 128 = 157833879144010026450341664 := rfl
private theorem receipt_3_12_2340_1_part5 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 1) 640 128 = 94344948063002797888757536 := rfl
private theorem receipt_3_12_2340_1_part6 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 1) 768 128 = 37332350274609235164196640 := rfl
private theorem receipt_3_12_2340_1_part7 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 1) 896 29 = 1222304576390735242411881 := rfl
private theorem receipt_3_12_2340_1_join0 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 1) 0 256 = 857086072433704487605120576 :=
  phaseBlock_append receipt_3_12_2340_1_part0 receipt_3_12_2340_1_part1 rfl rfl rfl
private theorem receipt_3_12_2340_1_join1 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 1) 256 256 = 530941999889944525509389888 :=
  phaseBlock_append receipt_3_12_2340_1_part2 receipt_3_12_2340_1_part3 rfl rfl rfl
private theorem receipt_3_12_2340_1_join2 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 1) 0 512 = 1388028072323649013114510464 :=
  phaseBlock_append receipt_3_12_2340_1_join0 receipt_3_12_2340_1_join1 rfl rfl rfl
private theorem receipt_3_12_2340_1_join3 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 1) 512 256 = 252178827207012824339099200 :=
  phaseBlock_append receipt_3_12_2340_1_part4 receipt_3_12_2340_1_part5 rfl rfl rfl
private theorem receipt_3_12_2340_1_join4 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 1) 768 157 = 38554654850999970406608521 :=
  phaseBlock_append receipt_3_12_2340_1_part6 receipt_3_12_2340_1_part7 rfl rfl rfl
private theorem receipt_3_12_2340_1_join5 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 1) 512 413 = 290733482058012794745707721 :=
  phaseBlock_append receipt_3_12_2340_1_join3 receipt_3_12_2340_1_join4 rfl rfl rfl
private theorem receipt_3_12_2340_1_join6 :
    phaseBlock (fastLayer (bank 3 12).shape 179827 2340 31 1 1 1 1) 0 925 = 1678761554381661807860218185 :=
  phaseBlock_append receipt_3_12_2340_1_join2 receipt_3_12_2340_1_join5 rfl rfl rfl

private theorem receipt_3_12_2340_1 : fastPhase (bank 3 12).shape 179827 2340 31 1 1 1 1 = 1678761554381661807860218185 :=
  phase_of_block (n := 925) (by decide +kernel) receipt_3_12_2340_1_join6

theorem receipt_3_12 : Checked (bank 3 12) 31 1 1 := by
  refine checked_from_values (bank 3 12) 31 1 1
    (P3_7_1.checked (bank 3 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4235_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_12_2339_0 receipt_3_12_2339_1 receipt_3_12_2340_0 receipt_3_12_2340_1 (by decide +kernel) (by decide +kernel)

def group4_stage (i : Fin 2) : Fin 17 :=
  ⟨11+i.val, by have := i.isLt; omega⟩

theorem group4_checked (rect : Fin 4) (i : Fin 2) :
    Checked (bank rect (group4_stage i)) (reserve (group4_stage i))
      (excess rect) (seed rect) := by
  fin_cases i
  · fin_cases rect
    · exact receipt_0_11
    · exact receipt_1_11
    · exact receipt_2_11
    · exact receipt_3_11
  · fin_cases rect
    · exact receipt_0_12
    · exact receipt_1_12
    · exact receipt_2_12
    · exact receipt_3_12

theorem group4_avoids {h : ℕ} {D : K1_14_1.PoleData h} (Crt : K1_14_1.CRTLift D)
    (word : K1.I → K1_14.L) (lo : 2339 ≤ h) (hi : h ≤ 33561) (rect : Fin 4)
    (i : Fin 2) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group4_stage i)).shape
      (cutoff h rect (group4_stage i)), ¬ G∣Q :=
  (group4_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group4_avoids

end Lower6960.RescueSource
