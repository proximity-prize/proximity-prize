import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt0

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open HelperSource (WidthGuard)

private theorem moment_3870_809_part0 :
    blockEstimate 3870 809 809 128 = 1350454560 := by decide +kernel
private theorem moment_3870_809_part1 :
    blockEstimate 3870 809 937 128 = 9056935200 := by decide +kernel
private theorem moment_3870_809_part2 :
    blockEstimate 3870 809 1065 128 = 23668288800 := by decide +kernel
private theorem moment_3870_809_part3 :
    blockEstimate 3870 809 1193 128 = 44379208992 := by decide +kernel
private theorem moment_3870_809_part4 :
    blockEstimate 3870 809 1321 128 = 70384389408 := by decide +kernel
private theorem moment_3870_809_part5 :
    blockEstimate 3870 809 1449 128 = 100878523680 := by decide +kernel
private theorem moment_3870_809_part6 :
    blockEstimate 3870 809 1577 128 = 134727508950 := by decide +kernel
private theorem moment_3870_809_part7 :
    blockEstimate 3870 809 1705 128 = 167637366720 := by decide +kernel
private theorem moment_3870_809_part8 :
    blockEstimate 3870 809 1833 128 = 197185337280 := by decide +kernel
private theorem moment_3870_809_part9 :
    blockEstimate 3870 809 1961 128 = 223335921600 := by decide +kernel
private theorem moment_3870_809_part10 :
    blockEstimate 3870 809 2089 128 = 246089119680 := by decide +kernel
private theorem moment_3870_809_part11 :
    blockEstimate 3870 809 2217 128 = 265444931520 := by decide +kernel
private theorem moment_3870_809_part12 :
    blockEstimate 3870 809 2345 128 = 281403357120 := by decide +kernel
private theorem moment_3870_809_part13 :
    blockEstimate 3870 809 2473 128 = 293964396480 := by decide +kernel
private theorem moment_3870_809_part14 :
    blockEstimate 3870 809 2601 128 = 303128049600 := by decide +kernel
private theorem moment_3870_809_part15 :
    blockEstimate 3870 809 2729 128 = 308894316480 := by decide +kernel
private theorem moment_3870_809_part16 :
    blockEstimate 3870 809 2857 128 = 311263197120 := by decide +kernel
private theorem moment_3870_809_part17 :
    blockEstimate 3870 809 2985 128 = 310234691520 := by decide +kernel
private theorem moment_3870_809_part18 :
    blockEstimate 3870 809 3113 128 = 305808799680 := by decide +kernel
private theorem moment_3870_809_part19 :
    blockEstimate 3870 809 3241 128 = 297985521600 := by decide +kernel
private theorem moment_3870_809_part20 :
    blockEstimate 3870 809 3369 128 = 286764857280 := by decide +kernel
private theorem moment_3870_809_part21 :
    blockEstimate 3870 809 3497 128 = 272146806720 := by decide +kernel
private theorem moment_3870_809_part22 :
    blockEstimate 3870 809 3625 128 = 254131369920 := by decide +kernel
private theorem moment_3870_809_part23 :
    blockEstimate 3870 809 3753 128 = 232718829875 := by decide +kernel
private theorem moment_3870_809_part24 :
    blockEstimate 3870 809 3881 128 = 208452439454 := by decide +kernel
private theorem moment_3870_809_part25 :
    blockEstimate 3870 809 4009 128 = 183217087457 := by decide +kernel
private theorem moment_3870_809_part26 :
    blockEstimate 3870 809 4137 128 = 157861267698 := by decide +kernel
private theorem moment_3870_809_part27 :
    blockEstimate 3870 809 4265 128 = 132922472315 := by decide +kernel
private theorem moment_3870_809_part28 :
    blockEstimate 3870 809 4393 128 = 108906379528 := by decide +kernel
private theorem moment_3870_809_part29 :
    blockEstimate 3870 809 4521 128 = 86286851710 := by decide +kernel
private theorem moment_3870_809_part30 :
    blockEstimate 3870 809 4649 128 = 65428117547 := by decide +kernel
private theorem moment_3870_809_part31 :
    blockEstimate 3870 809 4777 128 = 46761079776 := by decide +kernel
private theorem moment_3870_809_part32 :
    blockEstimate 3870 809 4905 128 = 30868837344 := by decide +kernel
private theorem moment_3870_809_part33 :
    blockEstimate 3870 809 5033 128 = 18012681184 := by decide +kernel
private theorem moment_3870_809_part34 :
    blockEstimate 3870 809 5161 128 = 8444269536 := by decide +kernel
private theorem moment_3870_809_part35 :
    blockEstimate 3870 809 5289 128 = 2415260640 := by decide +kernel
private theorem moment_3870_809_part36 :
    blockEstimate 3870 809 5417 71 = 121821510 := by decide +kernel
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
    blockEstimate 4235 890 890 128 = 1481036960 := by decide +kernel
private theorem moment_4235_890_part1 :
    blockEstimate 4235 890 1018 128 = 9958958240 := by decide +kernel
private theorem moment_4235_890_part2 :
    blockEstimate 4235 890 1146 128 = 26107212960 := by decide +kernel
private theorem moment_4235_890_part3 :
    blockEstimate 4235 890 1274 128 = 49120494752 := by decide +kernel
private theorem moment_4235_890_part4 :
    blockEstimate 4235 890 1402 128 = 78193497248 := by decide +kernel
private theorem moment_4235_890_part5 :
    blockEstimate 4235 890 1530 128 = 112520914080 := by decide +kernel
private theorem moment_4235_890_part6 :
    blockEstimate 4235 890 1658 128 = 151297321945 := by decide +kernel
private theorem moment_4235_890_part7 :
    blockEstimate 4235 890 1786 128 = 192416653440 := by decide +kernel
private theorem moment_4235_890_part8 :
    blockEstimate 4235 890 1914 128 = 230838968448 := by decide +kernel
private theorem moment_4235_890_part9 :
    blockEstimate 4235 890 2042 128 = 265524158592 := by decide +kernel
private theorem moment_4235_890_part10 :
    blockEstimate 4235 890 2170 128 = 296472223872 := by decide +kernel
private theorem moment_4235_890_part11 :
    blockEstimate 4235 890 2298 128 = 323683164288 := by decide +kernel
private theorem moment_4235_890_part12 :
    blockEstimate 4235 890 2426 128 = 347156979840 := by decide +kernel
private theorem moment_4235_890_part13 :
    blockEstimate 4235 890 2554 128 = 366893670528 := by decide +kernel
private theorem moment_4235_890_part14 :
    blockEstimate 4235 890 2682 128 = 382893236352 := by decide +kernel
private theorem moment_4235_890_part15 :
    blockEstimate 4235 890 2810 128 = 395155677312 := by decide +kernel
private theorem moment_4235_890_part16 :
    blockEstimate 4235 890 2938 128 = 403680993408 := by decide +kernel
private theorem moment_4235_890_part17 :
    blockEstimate 4235 890 3066 128 = 408469184640 := by decide +kernel
private theorem moment_4235_890_part18 :
    blockEstimate 4235 890 3194 128 = 409520251008 := by decide +kernel
private theorem moment_4235_890_part19 :
    blockEstimate 4235 890 3322 128 = 406834192512 := by decide +kernel
private theorem moment_4235_890_part20 :
    blockEstimate 4235 890 3450 128 = 400411009152 := by decide +kernel
private theorem moment_4235_890_part21 :
    blockEstimate 4235 890 3578 128 = 390250700928 := by decide +kernel
private theorem moment_4235_890_part22 :
    blockEstimate 4235 890 3706 128 = 376353267840 := by decide +kernel
private theorem moment_4235_890_part23 :
    blockEstimate 4235 890 3834 128 = 358718709888 := by decide +kernel
private theorem moment_4235_890_part24 :
    blockEstimate 4235 890 3962 128 = 337347027072 := by decide +kernel
private theorem moment_4235_890_part25 :
    blockEstimate 4235 890 4090 128 = 312238219392 := by decide +kernel
private theorem moment_4235_890_part26 :
    blockEstimate 4235 890 4218 128 = 283690141688 := by decide +kernel
private theorem moment_4235_890_part27 :
    blockEstimate 4235 890 4346 128 = 253624141004 := by decide +kernel
private theorem moment_4235_890_part28 :
    blockEstimate 4235 890 4474 128 = 223191153402 := by decide +kernel
private theorem moment_4235_890_part29 :
    blockEstimate 4235 890 4602 128 = 192941946510 := by decide +kernel
private theorem moment_4235_890_part30 :
    blockEstimate 4235 890 4730 128 = 163397461409 := by decide +kernel
private theorem moment_4235_890_part31 :
    blockEstimate 4235 890 4858 128 = 135049716262 := by decide +kernel
private theorem moment_4235_890_part32 :
    blockEstimate 4235 890 4986 128 = 108361807977 := by decide +kernel
private theorem moment_4235_890_part33 :
    blockEstimate 4235 890 5114 128 = 83636873128 := by decide +kernel
private theorem moment_4235_890_part34 :
    blockEstimate 4235 890 5242 128 = 61387552016 := by decide +kernel
private theorem moment_4235_890_part35 :
    blockEstimate 4235 890 5370 128 = 42182088976 := by decide +kernel
private theorem moment_4235_890_part36 :
    blockEstimate 4235 890 5498 128 = 26273545488 := by decide +kernel
private theorem moment_4235_890_part37 :
    blockEstimate 4235 890 5626 128 = 13913579792 := by decide +kernel
private theorem moment_4235_890_part38 :
    blockEstimate 4235 890 5754 128 = 5353850128 := by decide +kernel
private theorem moment_4235_890_part39 :
    blockEstimate 4235 890 5882 128 = 846014736 := by decide +kernel
private theorem moment_4235_890_part40 :
    blockEstimate 4235 890 6010 5 = 93131 := by decide +kernel
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
    blockEstimate 4235 924 924 128 = 1481036960 := by decide +kernel
private theorem moment_4235_924_part1 :
    blockEstimate 4235 924 1052 128 = 9958958240 := by decide +kernel
private theorem moment_4235_924_part2 :
    blockEstimate 4235 924 1180 128 = 26107212960 := by decide +kernel
private theorem moment_4235_924_part3 :
    blockEstimate 4235 924 1308 128 = 49120494752 := by decide +kernel
private theorem moment_4235_924_part4 :
    blockEstimate 4235 924 1436 128 = 78193497248 := by decide +kernel
private theorem moment_4235_924_part5 :
    blockEstimate 4235 924 1564 128 = 112520914080 := by decide +kernel
private theorem moment_4235_924_part6 :
    blockEstimate 4235 924 1692 128 = 151297438880 := by decide +kernel
private theorem moment_4235_924_part7 :
    blockEstimate 4235 924 1820 128 = 193178402555 := by decide +kernel
private theorem moment_4235_924_part8 :
    blockEstimate 4235 924 1948 128 = 233312350400 := by decide +kernel
private theorem moment_4235_924_part9 :
    blockEstimate 4235 924 2076 128 = 269578744000 := by decide +kernel
private theorem moment_4235_924_part10 :
    blockEstimate 4235 924 2204 128 = 301965406400 := by decide +kernel
private theorem moment_4235_924_part11 :
    blockEstimate 4235 924 2332 128 = 330472337600 := by decide +kernel
private theorem moment_4235_924_part12 :
    blockEstimate 4235 924 2460 128 = 355099537600 := by decide +kernel
private theorem moment_4235_924_part13 :
    blockEstimate 4235 924 2588 128 = 375847006400 := by decide +kernel
private theorem moment_4235_924_part14 :
    blockEstimate 4235 924 2716 128 = 392714744000 := by decide +kernel
private theorem moment_4235_924_part15 :
    blockEstimate 4235 924 2844 128 = 405702750400 := by decide +kernel
private theorem moment_4235_924_part16 :
    blockEstimate 4235 924 2972 128 = 414811025600 := by decide +kernel
private theorem moment_4235_924_part17 :
    blockEstimate 4235 924 3100 128 = 420039569600 := by decide +kernel
private theorem moment_4235_924_part18 :
    blockEstimate 4235 924 3228 128 = 421388382400 := by decide +kernel
private theorem moment_4235_924_part19 :
    blockEstimate 4235 924 3356 128 = 418857464000 := by decide +kernel
private theorem moment_4235_924_part20 :
    blockEstimate 4235 924 3484 128 = 412446814400 := by decide +kernel
private theorem moment_4235_924_part21 :
    blockEstimate 4235 924 3612 128 = 402156433600 := by decide +kernel
private theorem moment_4235_924_part22 :
    blockEstimate 4235 924 3740 128 = 387986321600 := by decide +kernel
private theorem moment_4235_924_part23 :
    blockEstimate 4235 924 3868 128 = 369936478400 := by decide +kernel
private theorem moment_4235_924_part24 :
    blockEstimate 4235 924 3996 128 = 348006904000 := by decide +kernel
private theorem moment_4235_924_part25 :
    blockEstimate 4235 924 4124 128 = 322198666532 := by decide +kernel
private theorem moment_4235_924_part26 :
    blockEstimate 4235 924 4252 128 = 293161594589 := by decide +kernel
private theorem moment_4235_924_part27 :
    blockEstimate 4235 924 4380 128 = 262868460698 := by decide +kernel
private theorem moment_4235_924_part28 :
    blockEstimate 4235 924 4508 128 = 232145769140 := by decide +kernel
private theorem moment_4235_924_part29 :
    blockEstimate 4235 924 4636 128 = 201537973074 := by decide +kernel
private theorem moment_4235_924_part30 :
    blockEstimate 4235 924 4764 128 = 171561665426 := by decide +kernel
private theorem moment_4235_924_part31 :
    blockEstimate 4235 924 4892 128 = 142705580189 := by decide +kernel
private theorem moment_4235_924_part32 :
    blockEstimate 4235 924 5020 128 = 115430591933 := by decide +kernel
private theorem moment_4235_924_part33 :
    blockEstimate 4235 924 5148 128 = 90027048170 := by decide +kernel
private theorem moment_4235_924_part34 :
    blockEstimate 4235 924 5276 128 = 67011238656 := by decide +kernel
private theorem moment_4235_924_part35 :
    blockEstimate 4235 924 5404 128 = 46972332800 := by decide +kernel
private theorem moment_4235_924_part36 :
    blockEstimate 4235 924 5532 128 = 30163499776 := by decide +kernel
private theorem moment_4235_924_part37 :
    blockEstimate 4235 924 5660 128 = 16836397824 := by decide +kernel
private theorem moment_4235_924_part38 :
    blockEstimate 4235 924 5788 128 = 7242685184 := by decide +kernel
private theorem moment_4235_924_part39 :
    blockEstimate 4235 924 5916 128 = 1634020096 := by decide +kernel
private theorem moment_4235_924_part40 :
    blockEstimate 4235 924 6044 39 = 23322080 := by decide +kernel
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
    blockEstimate 4255 890 890 128 = 1488192160 := by decide +kernel
private theorem moment_4255_890_part1 :
    blockEstimate 4255 890 1018 128 = 10008384160 := by decide +kernel
private theorem moment_4255_890_part2 :
    blockEstimate 4255 890 1146 128 = 26240852640 := by decide +kernel
private theorem moment_4255_890_part3 :
    blockEstimate 4255 890 1274 128 = 49380291232 := by decide +kernel
private theorem moment_4255_890_part4 :
    blockEstimate 4255 890 1402 128 = 78621393568 := by decide +kernel
private theorem moment_4255_890_part5 :
    blockEstimate 4255 890 1530 128 = 113158853280 := by decide +kernel
private theorem moment_4255_890_part6 :
    blockEstimate 4255 890 1658 128 = 152187246365 := by decide +kernel
private theorem moment_4255_890_part7 :
    blockEstimate 4255 890 1786 128 = 193592488320 := by decide +kernel
private theorem moment_4255_890_part8 :
    blockEstimate 4255 890 1914 128 = 232306766208 := by decide +kernel
private theorem moment_4255_890_part9 :
    blockEstimate 4255 890 2042 128 = 267283919232 := by decide +kernel
private theorem moment_4255_890_part10 :
    blockEstimate 4255 890 2170 128 = 298523947392 := by decide +kernel
private theorem moment_4255_890_part11 :
    blockEstimate 4255 890 2298 128 = 326026850688 := by decide +kernel
private theorem moment_4255_890_part12 :
    blockEstimate 4255 890 2426 128 = 349792629120 := by decide +kernel
private theorem moment_4255_890_part13 :
    blockEstimate 4255 890 2554 128 = 369821282688 := by decide +kernel
private theorem moment_4255_890_part14 :
    blockEstimate 4255 890 2682 128 = 386112811392 := by decide +kernel
private theorem moment_4255_890_part15 :
    blockEstimate 4255 890 2810 128 = 398667215232 := by decide +kernel
private theorem moment_4255_890_part16 :
    blockEstimate 4255 890 2938 128 = 407484494208 := by decide +kernel
private theorem moment_4255_890_part17 :
    blockEstimate 4255 890 3066 128 = 412564648320 := by decide +kernel
private theorem moment_4255_890_part18 :
    blockEstimate 4255 890 3194 128 = 413907677568 := by decide +kernel
private theorem moment_4255_890_part19 :
    blockEstimate 4255 890 3322 128 = 411513581952 := by decide +kernel
private theorem moment_4255_890_part20 :
    blockEstimate 4255 890 3450 128 = 405382361472 := by decide +kernel
private theorem moment_4255_890_part21 :
    blockEstimate 4255 890 3578 128 = 395514016128 := by decide +kernel
private theorem moment_4255_890_part22 :
    blockEstimate 4255 890 3706 128 = 381908545920 := by decide +kernel
private theorem moment_4255_890_part23 :
    blockEstimate 4255 890 3834 128 = 364565950848 := by decide +kernel
private theorem moment_4255_890_part24 :
    blockEstimate 4255 890 3962 128 = 343486230912 := by decide +kernel
private theorem moment_4255_890_part25 :
    blockEstimate 4255 890 4090 128 = 318669386112 := by decide +kernel
private theorem moment_4255_890_part26 :
    blockEstimate 4255 890 4218 128 = 290279870826 := by decide +kernel
private theorem moment_4255_890_part27 :
    blockEstimate 4255 890 4346 128 = 260054586913 := by decide +kernel
private theorem moment_4255_890_part28 :
    blockEstimate 4255 890 4474 128 = 229385819232 := by decide +kernel
private theorem moment_4255_890_part29 :
    blockEstimate 4255 890 4602 128 = 198837794000 := by decide +kernel
private theorem moment_4255_890_part30 :
    blockEstimate 4255 890 4730 128 = 168935971457 := by decide +kernel
private theorem moment_4255_890_part31 :
    blockEstimate 4255 890 4858 128 = 140176889005 := by decide +kernel
private theorem moment_4255_890_part32 :
    blockEstimate 4255 890 4986 128 = 113028162661 := by decide +kernel
private theorem moment_4255_890_part33 :
    blockEstimate 4255 890 5114 128 = 87833864441 := by decide +kernel
private theorem moment_4255_890_part34 :
    blockEstimate 4255 890 5242 128 = 65012280656 := by decide +kernel
private theorem moment_4255_890_part35 :
    blockEstimate 4255 890 5370 128 = 45205207376 := by decide +kernel
private theorem moment_4255_890_part36 :
    blockEstimate 4255 890 5498 128 = 28676703568 := by decide +kernel
private theorem moment_4255_890_part37 :
    blockEstimate 4255 890 5626 128 = 15678427472 := by decide +kernel
private theorem moment_4255_890_part38 :
    blockEstimate 4255 890 5754 128 = 6462037328 := by decide +kernel
private theorem moment_4255_890_part39 :
    blockEstimate 4255 890 5882 128 = 1279191376 := by decide +kernel
private theorem moment_4255_890_part40 :
    blockEstimate 4255 890 6010 25 = 6565356 := by decide +kernel
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
    blockEstimate 4866 1061 1061 128 = 1706783520 := by decide +kernel
private theorem moment_4866_1061_part1 :
    blockEstimate 4866 1061 1189 128 = 11518346016 := by decide +kernel
private theorem moment_4866_1061_part2 :
    blockEstimate 4866 1061 1317 128 = 30323544864 := by decide +kernel
private theorem moment_4866_1061_part3 :
    blockEstimate 4866 1061 1445 128 = 57317073696 := by decide +kernel
private theorem moment_4866_1061_part4 :
    blockEstimate 4866 1061 1573 128 = 91693626144 := by decide +kernel
private theorem moment_4866_1061_part5 :
    blockEstimate 4866 1061 1701 128 = 132647895840 := by decide +kernel
private theorem moment_4866_1061_part6 :
    blockEstimate 4866 1061 1829 128 = 179374576416 := by decide +kernel
private theorem moment_4866_1061_part7 :
    blockEstimate 4866 1061 1957 128 = 231068361504 := by decide +kernel
private theorem moment_4866_1061_part8 :
    blockEstimate 4866 1061 2085 128 = 286454620881 := by decide +kernel
private theorem moment_4866_1061_part9 :
    blockEstimate 4866 1061 2213 128 = 340231189824 := by decide +kernel
private theorem moment_4866_1061_part10 :
    blockEstimate 4866 1061 2341 128 = 389585745216 := by decide +kernel
private theorem moment_4866_1061_part11 :
    blockEstimate 4866 1061 2469 128 = 434485949760 := by decide +kernel
private theorem moment_4866_1061_part12 :
    blockEstimate 4866 1061 2597 128 = 474931803456 := by decide +kernel
private theorem moment_4866_1061_part13 :
    blockEstimate 4866 1061 2725 128 = 510923306304 := by decide +kernel
private theorem moment_4866_1061_part14 :
    blockEstimate 4866 1061 2853 128 = 542460458304 := by decide +kernel
private theorem moment_4866_1061_part15 :
    blockEstimate 4866 1061 2981 128 = 569543259456 := by decide +kernel
private theorem moment_4866_1061_part16 :
    blockEstimate 4866 1061 3109 128 = 592171709760 := by decide +kernel
private theorem moment_4866_1061_part17 :
    blockEstimate 4866 1061 3237 128 = 610345809216 := by decide +kernel
private theorem moment_4866_1061_part18 :
    blockEstimate 4866 1061 3365 128 = 624065557824 := by decide +kernel
private theorem moment_4866_1061_part19 :
    blockEstimate 4866 1061 3493 128 = 633330955584 := by decide +kernel
private theorem moment_4866_1061_part20 :
    blockEstimate 4866 1061 3621 128 = 638142002496 := by decide +kernel
private theorem moment_4866_1061_part21 :
    blockEstimate 4866 1061 3749 128 = 638498698560 := by decide +kernel
private theorem moment_4866_1061_part22 :
    blockEstimate 4866 1061 3877 128 = 634401043776 := by decide +kernel
private theorem moment_4866_1061_part23 :
    blockEstimate 4866 1061 4005 128 = 625849038144 := by decide +kernel
private theorem moment_4866_1061_part24 :
    blockEstimate 4866 1061 4133 128 = 612842681664 := by decide +kernel
private theorem moment_4866_1061_part25 :
    blockEstimate 4866 1061 4261 128 = 595381974336 := by decide +kernel
private theorem moment_4866_1061_part26 :
    blockEstimate 4866 1061 4389 128 = 573466916160 := by decide +kernel
private theorem moment_4866_1061_part27 :
    blockEstimate 4866 1061 4517 128 = 547097507136 := by decide +kernel
private theorem moment_4866_1061_part28 :
    blockEstimate 4866 1061 4645 128 = 516273747264 := by decide +kernel
private theorem moment_4866_1061_part29 :
    blockEstimate 4866 1061 4773 128 = 481005997449 := by decide +kernel
private theorem moment_4866_1061_part30 :
    blockEstimate 4866 1061 4901 128 = 442318295470 := by decide +kernel
private theorem moment_4866_1061_part31 :
    blockEstimate 4866 1061 5029 128 = 402338149752 := by decide +kernel
private theorem moment_4866_1061_part32 :
    blockEstimate 4866 1061 5157 128 = 361812541516 := by decide +kernel
private theorem moment_4866_1061_part33 :
    blockEstimate 4866 1061 5285 128 = 321290189818 := by decide +kernel
private theorem moment_4866_1061_part34 :
    blockEstimate 4866 1061 5413 128 = 281295549078 := by decide +kernel
private theorem moment_4866_1061_part35 :
    blockEstimate 4866 1061 5541 128 = 242328807457 := by decide +kernel
private theorem moment_4866_1061_part36 :
    blockEstimate 4866 1061 5669 128 = 204865888039 := by decide +kernel
private theorem moment_4866_1061_part37 :
    blockEstimate 4866 1061 5797 128 = 169358449123 := by decide +kernel
private theorem moment_4866_1061_part38 :
    blockEstimate 4866 1061 5925 128 = 136012354473 := by decide +kernel
private theorem moment_4866_1061_part39 :
    blockEstimate 4866 1061 6053 128 = 105427402336 := by decide +kernel
private theorem moment_4866_1061_part40 :
    blockEstimate 4866 1061 6181 128 = 78230822496 := by decide +kernel
private theorem moment_4866_1061_part41 :
    blockEstimate 4866 1061 6309 128 = 54674308704 := by decide +kernel
private theorem moment_4866_1061_part42 :
    blockEstimate 4866 1061 6437 128 = 35009519200 := by decide +kernel
private theorem moment_4866_1061_part43 :
    blockEstimate 4866 1061 6565 128 = 19488112224 := by decide +kernel
private theorem moment_4866_1061_part44 :
    blockEstimate 4866 1061 6693 128 = 8361746016 := by decide +kernel
private theorem moment_4866_1061_part45 :
    blockEstimate 4866 1061 6821 128 = 1882078816 := by decide +kernel
private theorem moment_4866_1061_part46 :
    blockEstimate 4866 1061 6949 39 = 26811510 := by decide +kernel
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

private theorem receipt_0_11_2383_0_part0 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 0) 0 128 = 8224659443109858160678219392 := by decide +kernel
private theorem receipt_0_11_2383_0_part1 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 0) 128 128 = 6932784754047927182295723648 := by decide +kernel
private theorem receipt_0_11_2383_0_part2 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 0) 256 128 = 5715109677965493990292827776 := by decide +kernel
private theorem receipt_0_11_2383_0_part3 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 0) 384 128 = 4569428038942203282383761024 := by decide +kernel
private theorem receipt_0_11_2383_0_part4 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 0) 512 128 = 3493540192572627545408679552 := by decide +kernel
private theorem receipt_0_11_2383_0_part5 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 0) 640 128 = 2485253264221425962968337556 := by decide +kernel
private theorem receipt_0_11_2383_0_part6 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 0) 768 128 = 1542382725933226411898257748 := by decide +kernel
private theorem receipt_0_11_2383_0_part7 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 0) 896 128 = 662744974646791841575217376 := by decide +kernel
private theorem receipt_0_11_2383_0_part8 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 0) 1024 38 = 36472456959180206217251560 := by decide +kernel
private theorem receipt_0_11_2383_0_join0 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 0) 0 256 = 15157444197157785342973943040 :=
  phaseBlock_append receipt_0_11_2383_0_part0 receipt_0_11_2383_0_part1 rfl rfl rfl
private theorem receipt_0_11_2383_0_join1 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 0) 256 256 = 10284537716907697272676588800 :=
  phaseBlock_append receipt_0_11_2383_0_part2 receipt_0_11_2383_0_part3 rfl rfl rfl
private theorem receipt_0_11_2383_0_join2 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 0) 0 512 = 25441981914065482615650531840 :=
  phaseBlock_append receipt_0_11_2383_0_join0 receipt_0_11_2383_0_join1 rfl rfl rfl
private theorem receipt_0_11_2383_0_join3 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 0) 512 256 = 5978793456794053508377017108 :=
  phaseBlock_append receipt_0_11_2383_0_part4 receipt_0_11_2383_0_part5 rfl rfl rfl
private theorem receipt_0_11_2383_0_join4 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 0) 896 166 = 699217431605972047792468936 :=
  phaseBlock_append receipt_0_11_2383_0_part7 receipt_0_11_2383_0_part8 rfl rfl rfl
private theorem receipt_0_11_2383_0_join5 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 0) 768 294 = 2241600157539198459690726684 :=
  phaseBlock_append receipt_0_11_2383_0_part6 receipt_0_11_2383_0_join4 rfl rfl rfl
private theorem receipt_0_11_2383_0_join6 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 0) 512 550 = 8220393614333251968067743792 :=
  phaseBlock_append receipt_0_11_2383_0_join3 receipt_0_11_2383_0_join5 rfl rfl rfl
private theorem receipt_0_11_2383_0_join7 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 0) 0 1062 = 33662375528398734583718275632 :=
  phaseBlock_append receipt_0_11_2383_0_join2 receipt_0_11_2383_0_join6 rfl rfl rfl

private theorem receipt_0_11_2383_0 : fastPhase (bank 0 11).shape 179808 2383 32 1 0 1 0 = 33662375528398734583718275632 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_0_11_2383_0_join7

private theorem receipt_0_11_2383_1_part0 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 1) 0 128 = 8214412614728292447255527872 := by decide +kernel
private theorem receipt_0_11_2383_1_part1 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 1) 128 128 = 6923106418927471805249626560 := by decide +kernel
private theorem receipt_0_11_2383_1_part2 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 1) 256 128 = 5705983136242562278267044288 := by decide +kernel
private theorem receipt_0_11_2383_1_part3 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 1) 384 128 = 4560836640536832877695361472 := by decide +kernel
private theorem receipt_0_11_2383_1_part4 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 1) 512 128 = 3485467337140334026818355648 := by decide +kernel
private theorem receipt_0_11_2383_1_part5 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 1) 640 128 = 2477682400323658276172869056 := by decide +kernel
private theorem receipt_0_11_2383_1_part6 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 1) 768 128 = 1535297340901316057698965908 := by decide +kernel
private theorem receipt_0_11_2383_1_part7 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 1) 896 128 = 656128597677635846506926594 := by decide +kernel
private theorem receipt_0_11_2383_1_part8 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 1) 1024 38 = 34596084824737023936223386 := by decide +kernel
private theorem receipt_0_11_2383_1_join0 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 1) 0 256 = 15137519033655764252505154432 :=
  phaseBlock_append receipt_0_11_2383_1_part0 receipt_0_11_2383_1_part1 rfl rfl rfl
private theorem receipt_0_11_2383_1_join1 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 1) 256 256 = 10266819776779395155962405760 :=
  phaseBlock_append receipt_0_11_2383_1_part2 receipt_0_11_2383_1_part3 rfl rfl rfl
private theorem receipt_0_11_2383_1_join2 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 1) 0 512 = 25404338810435159408467560192 :=
  phaseBlock_append receipt_0_11_2383_1_join0 receipt_0_11_2383_1_join1 rfl rfl rfl
private theorem receipt_0_11_2383_1_join3 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 1) 512 256 = 5963149737463992302991224704 :=
  phaseBlock_append receipt_0_11_2383_1_part4 receipt_0_11_2383_1_part5 rfl rfl rfl
private theorem receipt_0_11_2383_1_join4 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 1) 896 166 = 690724682502372870443149980 :=
  phaseBlock_append receipt_0_11_2383_1_part7 receipt_0_11_2383_1_part8 rfl rfl rfl
private theorem receipt_0_11_2383_1_join5 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 1) 768 294 = 2226022023403688928142115888 :=
  phaseBlock_append receipt_0_11_2383_1_part6 receipt_0_11_2383_1_join4 rfl rfl rfl
private theorem receipt_0_11_2383_1_join6 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 1) 512 550 = 8189171760867681231133340592 :=
  phaseBlock_append receipt_0_11_2383_1_join3 receipt_0_11_2383_1_join5 rfl rfl rfl
private theorem receipt_0_11_2383_1_join7 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2383 32 1 0 1 1) 0 1062 = 33593510571302840639600900784 :=
  phaseBlock_append receipt_0_11_2383_1_join2 receipt_0_11_2383_1_join6 rfl rfl rfl

private theorem receipt_0_11_2383_1 : fastPhase (bank 0 11).shape 179808 2383 32 1 0 1 1 = 33593510571302840639600900784 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_0_11_2383_1_join7

private theorem receipt_0_11_2384_0_part0 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 0) 0 128 = 8224733019710920350718534272 := by decide +kernel
private theorem receipt_0_11_2384_0_part1 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 0) 128 128 = 6932842340026107150173340288 := by decide +kernel
private theorem receipt_0_11_2384_0_part2 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 0) 256 128 = 5715153351022718548317004416 := by decide +kernel
private theorem receipt_0_11_2384_0_part3 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 0) 384 128 = 4569459800770615282695717504 := by decide +kernel
private theorem receipt_0_11_2384_0_part4 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 0) 512 128 = 3493561969082112803279348352 := by decide +kernel
private theorem receipt_0_11_2384_0_part5 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 0) 640 128 = 2485266899143242865981234512 := by decide +kernel
private theorem receipt_0_11_2384_0_part6 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 0) 768 128 = 1542389982680020789384608034 := by decide +kernel
private theorem receipt_0_11_2384_0_part7 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 0) 896 128 = 662747577028436620950961649 := by decide +kernel
private theorem receipt_0_11_2384_0_part8 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 0) 1024 38 = 36472578235239468344629362 := by decide +kernel
private theorem receipt_0_11_2384_0_join0 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 0) 0 256 = 15157575359737027500891874560 :=
  phaseBlock_append receipt_0_11_2384_0_part0 receipt_0_11_2384_0_part1 rfl rfl rfl
private theorem receipt_0_11_2384_0_join1 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 0) 256 256 = 10284613151793333831012721920 :=
  phaseBlock_append receipt_0_11_2384_0_part2 receipt_0_11_2384_0_part3 rfl rfl rfl
private theorem receipt_0_11_2384_0_join2 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 0) 0 512 = 25442188511530361331904596480 :=
  phaseBlock_append receipt_0_11_2384_0_join0 receipt_0_11_2384_0_join1 rfl rfl rfl
private theorem receipt_0_11_2384_0_join3 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 0) 512 256 = 5978828868225355669260582864 :=
  phaseBlock_append receipt_0_11_2384_0_part4 receipt_0_11_2384_0_part5 rfl rfl rfl
private theorem receipt_0_11_2384_0_join4 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 0) 896 166 = 699220155263676089295591011 :=
  phaseBlock_append receipt_0_11_2384_0_part7 receipt_0_11_2384_0_part8 rfl rfl rfl
private theorem receipt_0_11_2384_0_join5 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 0) 768 294 = 2241610137943696878680199045 :=
  phaseBlock_append receipt_0_11_2384_0_part6 receipt_0_11_2384_0_join4 rfl rfl rfl
private theorem receipt_0_11_2384_0_join6 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 0) 512 550 = 8220439006169052547940781909 :=
  phaseBlock_append receipt_0_11_2384_0_join3 receipt_0_11_2384_0_join5 rfl rfl rfl
private theorem receipt_0_11_2384_0_join7 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 0) 0 1062 = 33662627517699413879845378389 :=
  phaseBlock_append receipt_0_11_2384_0_join2 receipt_0_11_2384_0_join6 rfl rfl rfl

private theorem receipt_0_11_2384_0 : fastPhase (bank 0 11).shape 179808 2384 32 1 0 1 0 = 33662627517699413879845378389 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_0_11_2384_0_join7

private theorem receipt_0_11_2384_1_part0 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 1) 0 128 = 8214486116572374952984456064 := by decide +kernel
private theorem receipt_0_11_2384_1_part1 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 1) 128 128 = 6923163938384422839504194432 := by decide +kernel
private theorem receipt_0_11_2384_1_part2 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 1) 256 128 = 5706026750655108159223589760 := by decide +kernel
private theorem receipt_0_11_2384_1_part3 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 1) 384 128 = 4560868351239162179798502272 := by decide +kernel
private theorem receipt_0_11_2384_1_part4 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 1) 512 128 = 3485489069685623198408682368 := by decide +kernel
private theorem receipt_0_11_2384_1_part5 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 1) 640 128 = 2477695998108432574959308202 := by decide +kernel
private theorem receipt_0_11_2384_1_part6 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 1) 768 128 = 1535304567054846841141493278 := by decide +kernel
private theorem receipt_0_11_2384_1_part7 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 1) 896 128 = 656131175648122418529867306 := by decide +kernel
private theorem receipt_0_11_2384_1_part8 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 1) 1024 38 = 34596199989826923930698556 := by decide +kernel
private theorem receipt_0_11_2384_1_join0 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 1) 0 256 = 15137650054956797792488650496 :=
  phaseBlock_append receipt_0_11_2384_1_part0 receipt_0_11_2384_1_part1 rfl rfl rfl
private theorem receipt_0_11_2384_1_join1 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 1) 256 256 = 10266895101894270339022092032 :=
  phaseBlock_append receipt_0_11_2384_1_part2 receipt_0_11_2384_1_part3 rfl rfl rfl
private theorem receipt_0_11_2384_1_join2 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 1) 0 512 = 25404545156851068131510742528 :=
  phaseBlock_append receipt_0_11_2384_1_join0 receipt_0_11_2384_1_join1 rfl rfl rfl
private theorem receipt_0_11_2384_1_join3 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 1) 512 256 = 5963185067794055773367990570 :=
  phaseBlock_append receipt_0_11_2384_1_part4 receipt_0_11_2384_1_part5 rfl rfl rfl
private theorem receipt_0_11_2384_1_join4 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 1) 896 166 = 690727375637949342460565862 :=
  phaseBlock_append receipt_0_11_2384_1_part7 receipt_0_11_2384_1_part8 rfl rfl rfl
private theorem receipt_0_11_2384_1_join5 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 1) 768 294 = 2226031942692796183602059140 :=
  phaseBlock_append receipt_0_11_2384_1_part6 receipt_0_11_2384_1_join4 rfl rfl rfl
private theorem receipt_0_11_2384_1_join6 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 1) 512 550 = 8189217010486851956970049710 :=
  phaseBlock_append receipt_0_11_2384_1_join3 receipt_0_11_2384_1_join5 rfl rfl rfl
private theorem receipt_0_11_2384_1_join7 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2384 32 1 0 1 1) 0 1062 = 33593762167337920088480792238 :=
  phaseBlock_append receipt_0_11_2384_1_join2 receipt_0_11_2384_1_join6 rfl rfl rfl

private theorem receipt_0_11_2384_1 : fastPhase (bank 0 11).shape 179808 2384 32 1 0 1 1 = 33593762167337920088480792238 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_0_11_2384_1_join7

theorem receipt_0_11 : Checked (bank 0 11) 32 0 1 := by
  refine checked_from_values (bank 0 11) 32 0 1
    (P3_7_1.checked (bank 0 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4866_1061)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_11_2383_0 receipt_0_11_2383_1 receipt_0_11_2384_0 receipt_0_11_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_11_2383_0_part0 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 0) 0 128 = 7337524128683607236007210816 := by decide +kernel
private theorem receipt_1_11_2383_0_part1 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 0) 128 128 = 6179575296620592672184291136 := by decide +kernel
private theorem receipt_1_11_2383_0_part2 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 0) 256 128 = 5089727317671267567617568576 := by decide +kernel
private theorem receipt_1_11_2383_0_part3 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 0) 384 128 = 4065843828952890901101973312 := by decide +kernel
private theorem receipt_1_11_2383_0_part4 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 0) 512 128 = 3105801069647215438415474496 := by decide +kernel
private theorem receipt_1_11_2383_0_part5 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 0) 640 128 = 2207488072986695980795383261 := by decide +kernel
private theorem receipt_1_11_2383_0_part6 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 0) 768 128 = 1368808045223074001207934809 := by decide +kernel
private theorem receipt_1_11_2383_0_part7 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 0) 896 128 = 587671758952450983618629365 := by decide +kernel
private theorem receipt_1_11_2383_0_part8 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 0) 1024 38 = 32320766113664874269482674 := by decide +kernel
private theorem receipt_1_11_2383_0_join0 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 0) 0 256 = 13517099425304199908191501952 :=
  phaseBlock_append receipt_1_11_2383_0_part0 receipt_1_11_2383_0_part1 rfl rfl rfl
private theorem receipt_1_11_2383_0_join1 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 0) 256 256 = 9155571146624158468719541888 :=
  phaseBlock_append receipt_1_11_2383_0_part2 receipt_1_11_2383_0_part3 rfl rfl rfl
private theorem receipt_1_11_2383_0_join2 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 0) 0 512 = 22672670571928358376911043840 :=
  phaseBlock_append receipt_1_11_2383_0_join0 receipt_1_11_2383_0_join1 rfl rfl rfl
private theorem receipt_1_11_2383_0_join3 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 0) 512 256 = 5313289142633911419210857757 :=
  phaseBlock_append receipt_1_11_2383_0_part4 receipt_1_11_2383_0_part5 rfl rfl rfl
private theorem receipt_1_11_2383_0_join4 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 0) 896 166 = 619992525066115857888112039 :=
  phaseBlock_append receipt_1_11_2383_0_part7 receipt_1_11_2383_0_part8 rfl rfl rfl
private theorem receipt_1_11_2383_0_join5 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 0) 768 294 = 1988800570289189859096046848 :=
  phaseBlock_append receipt_1_11_2383_0_part6 receipt_1_11_2383_0_join4 rfl rfl rfl
private theorem receipt_1_11_2383_0_join6 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 0) 512 550 = 7302089712923101278306904605 :=
  phaseBlock_append receipt_1_11_2383_0_join3 receipt_1_11_2383_0_join5 rfl rfl rfl
private theorem receipt_1_11_2383_0_join7 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 0) 0 1062 = 29974760284851459655217948445 :=
  phaseBlock_append receipt_1_11_2383_0_join2 receipt_1_11_2383_0_join6 rfl rfl rfl

private theorem receipt_1_11_2383_0 : fastPhase (bank 1 11).shape 179808 2383 32 1 0 2 0 = 29974760284851459655217948445 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_1_11_2383_0_join7

private theorem receipt_1_11_2383_1_part0 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 1) 0 128 = 7328332384458516216740687232 := by decide +kernel
private theorem receipt_1_11_2383_1_part1 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 1) 128 128 = 6170906182160925762194435456 := by decide +kernel
private theorem receipt_1_11_2383_1_part2 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 1) 256 128 = 5081564624442666776006241664 := by decide +kernel
private theorem receipt_1_11_2383_1_part3 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 1) 384 128 = 4058171444540614278126333312 := by decide +kernel
private theorem receipt_1_11_2383_1_part4 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 1) 512 128 = 3098602977563551566569057664 := by decide +kernel
private theorem receipt_1_11_2383_1_part5 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 1) 640 128 = 2200748351783053103095823867 := by decide +kernel
private theorem receipt_1_11_2383_1_part6 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 1) 768 128 = 1362510859337037493779973137 := by decide +kernel
private theorem receipt_1_11_2383_1_part7 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 1) 896 128 = 581801361369208602235528810 := by decide +kernel
private theorem receipt_1_11_2383_1_part8 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 1) 1024 38 = 30657841331714941921739817 := by decide +kernel
private theorem receipt_1_11_2383_1_join0 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 1) 0 256 = 13499238566619441978935122688 :=
  phaseBlock_append receipt_1_11_2383_1_part0 receipt_1_11_2383_1_part1 rfl rfl rfl
private theorem receipt_1_11_2383_1_join1 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 1) 256 256 = 9139736068983281054132574976 :=
  phaseBlock_append receipt_1_11_2383_1_part2 receipt_1_11_2383_1_part3 rfl rfl rfl
private theorem receipt_1_11_2383_1_join2 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 1) 0 512 = 22638974635602723033067697664 :=
  phaseBlock_append receipt_1_11_2383_1_join0 receipt_1_11_2383_1_join1 rfl rfl rfl
private theorem receipt_1_11_2383_1_join3 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 1) 512 256 = 5299351329346604669664881531 :=
  phaseBlock_append receipt_1_11_2383_1_part4 receipt_1_11_2383_1_part5 rfl rfl rfl
private theorem receipt_1_11_2383_1_join4 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 1) 896 166 = 612459202700923544157268627 :=
  phaseBlock_append receipt_1_11_2383_1_part7 receipt_1_11_2383_1_part8 rfl rfl rfl
private theorem receipt_1_11_2383_1_join5 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 1) 768 294 = 1974970062037961037937241764 :=
  phaseBlock_append receipt_1_11_2383_1_part6 receipt_1_11_2383_1_join4 rfl rfl rfl
private theorem receipt_1_11_2383_1_join6 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 1) 512 550 = 7274321391384565707602123295 :=
  phaseBlock_append receipt_1_11_2383_1_join3 receipt_1_11_2383_1_join5 rfl rfl rfl
private theorem receipt_1_11_2383_1_join7 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2383 32 1 0 2 1) 0 1062 = 29913296026987288740669820959 :=
  phaseBlock_append receipt_1_11_2383_1_join2 receipt_1_11_2383_1_join6 rfl rfl rfl

private theorem receipt_1_11_2383_1 : fastPhase (bank 1 11).shape 179808 2383 32 1 0 2 1 = 29913296026987288740669820959 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_1_11_2383_1_join7

private theorem receipt_1_11_2384_0_part0 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 0) 0 128 = 7337589769438334409323091456 := by decide +kernel
private theorem receipt_1_11_2384_0_part1 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 0) 128 128 = 6179626626489473728045979136 := by decide +kernel
private theorem receipt_1_11_2384_0_part2 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 0) 256 128 = 5089766212007363060785583616 := by decide +kernel
private theorem receipt_1_11_2384_0_part3 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 0) 384 128 = 4065872090606780121584113152 := by decide +kernel
private theorem receipt_1_11_2384_0_part4 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 0) 512 128 = 3105820429404184224903108096 := by decide +kernel
private theorem receipt_1_11_2384_0_part5 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 0) 640 128 = 2207500184121333943237863396 := by decide +kernel
private theorem receipt_1_11_2384_0_part6 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 0) 768 128 = 1368814485399048145036328376 := by decide +kernel
private theorem receipt_1_11_2384_0_part7 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 0) 896 128 = 587674066577892308184464298 := by decide +kernel
private theorem receipt_1_11_2384_0_part8 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 0) 1024 38 = 32320873584890553622121721 := by decide +kernel
private theorem receipt_1_11_2384_0_join0 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 0) 0 256 = 13517216395927808137369070592 :=
  phaseBlock_append receipt_1_11_2384_0_part0 receipt_1_11_2384_0_part1 rfl rfl rfl
private theorem receipt_1_11_2384_0_join1 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 0) 256 256 = 9155638302614143182369696768 :=
  phaseBlock_append receipt_1_11_2384_0_part2 receipt_1_11_2384_0_part3 rfl rfl rfl
private theorem receipt_1_11_2384_0_join2 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 0) 0 512 = 22672854698541951319738767360 :=
  phaseBlock_append receipt_1_11_2384_0_join0 receipt_1_11_2384_0_join1 rfl rfl rfl
private theorem receipt_1_11_2384_0_join3 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 0) 512 256 = 5313320613525518168140971492 :=
  phaseBlock_append receipt_1_11_2384_0_part4 receipt_1_11_2384_0_part5 rfl rfl rfl
private theorem receipt_1_11_2384_0_join4 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 0) 896 166 = 619994940162782861806586019 :=
  phaseBlock_append receipt_1_11_2384_0_part7 receipt_1_11_2384_0_part8 rfl rfl rfl
private theorem receipt_1_11_2384_0_join5 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 0) 768 294 = 1988809425561831006842914395 :=
  phaseBlock_append receipt_1_11_2384_0_part6 receipt_1_11_2384_0_join4 rfl rfl rfl
private theorem receipt_1_11_2384_0_join6 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 0) 512 550 = 7302130039087349174983885887 :=
  phaseBlock_append receipt_1_11_2384_0_join3 receipt_1_11_2384_0_join5 rfl rfl rfl
private theorem receipt_1_11_2384_0_join7 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 0) 0 1062 = 29974984737629300494722653247 :=
  phaseBlock_append receipt_1_11_2384_0_join2 receipt_1_11_2384_0_join6 rfl rfl rfl

private theorem receipt_1_11_2384_0 : fastPhase (bank 1 11).shape 179808 2384 32 1 0 2 0 = 29974984737629300494722653247 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_1_11_2384_0_join7

private theorem receipt_1_11_2384_1_part0 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 1) 0 128 = 7328397958070475983650218624 := by decide +kernel
private theorem receipt_1_11_2384_1_part1 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 1) 128 128 = 6170957452384104174950949504 := by decide +kernel
private theorem receipt_1_11_2384_1_part2 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 1) 256 128 = 5081603466284707746590843520 := by decide +kernel
private theorem receipt_1_11_2384_1_part3 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 1) 384 128 = 4058199660509079038920270464 := by decide +kernel
private theorem receipt_1_11_2384_1_part4 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 1) 512 128 = 3098622298103101261109781120 := by decide +kernel
private theorem receipt_1_11_2384_1_part5 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 1) 640 128 = 2200760429848491331685605938 := by decide +kernel
private theorem receipt_1_11_2384_1_part6 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 1) 768 128 = 1362517272319092618254762496 := by decide +kernel
private theorem receipt_1_11_2384_1_part7 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 1) 896 128 = 581803647334542222586187307 := by decide +kernel
private theorem receipt_1_11_2384_1_part8 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 1) 1024 38 = 30657943387104043061742867 := by decide +kernel
private theorem receipt_1_11_2384_1_join0 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 1) 0 256 = 13499355410454580158601168128 :=
  phaseBlock_append receipt_1_11_2384_1_part0 receipt_1_11_2384_1_part1 rfl rfl rfl
private theorem receipt_1_11_2384_1_join1 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 1) 256 256 = 9139803126793786785511113984 :=
  phaseBlock_append receipt_1_11_2384_1_part2 receipt_1_11_2384_1_part3 rfl rfl rfl
private theorem receipt_1_11_2384_1_join2 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 1) 0 512 = 22639158537248366944112282112 :=
  phaseBlock_append receipt_1_11_2384_1_join0 receipt_1_11_2384_1_join1 rfl rfl rfl
private theorem receipt_1_11_2384_1_join3 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 1) 512 256 = 5299382727951592592795387058 :=
  phaseBlock_append receipt_1_11_2384_1_part4 receipt_1_11_2384_1_part5 rfl rfl rfl
private theorem receipt_1_11_2384_1_join4 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 1) 896 166 = 612461590721646265647930174 :=
  phaseBlock_append receipt_1_11_2384_1_part7 receipt_1_11_2384_1_part8 rfl rfl rfl
private theorem receipt_1_11_2384_1_join5 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 1) 768 294 = 1974978863040738883902692670 :=
  phaseBlock_append receipt_1_11_2384_1_part6 receipt_1_11_2384_1_join4 rfl rfl rfl
private theorem receipt_1_11_2384_1_join6 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 1) 512 550 = 7274361590992331476698079728 :=
  phaseBlock_append receipt_1_11_2384_1_join3 receipt_1_11_2384_1_join5 rfl rfl rfl
private theorem receipt_1_11_2384_1_join7 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2384 32 1 0 2 1) 0 1062 = 29913520128240698420810361840 :=
  phaseBlock_append receipt_1_11_2384_1_join2 receipt_1_11_2384_1_join6 rfl rfl rfl

private theorem receipt_1_11_2384_1 : fastPhase (bank 1 11).shape 179808 2384 32 1 0 2 1 = 29913520128240698420810361840 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_1_11_2384_1_join7

theorem receipt_1_11 : Checked (bank 1 11) 32 0 2 := by
  refine checked_from_values (bank 1 11) 32 0 2
    (P3_7_1.checked (bank 1 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4866_1061)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_11_2383_0 receipt_1_11_2383_1 receipt_1_11_2384_0 receipt_1_11_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_11_2383_0_part0 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 0) 0 128 = 3686777262493737823413241728 := by decide +kernel
private theorem receipt_2_11_2383_0_part1 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 0) 128 128 = 3084679928974876564993361792 := by decide +kernel
private theorem receipt_2_11_2383_0_part2 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 0) 256 128 = 2523989593976589447275218816 := by decide +kernel
private theorem receipt_2_11_2383_0_part3 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 0) 384 128 = 2002966213157319682125449088 := by decide +kernel
private theorem receipt_2_11_2383_0_part4 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 0) 512 128 = 1519905887466449826074298240 := by decide +kernel
private theorem receipt_2_11_2383_0_part5 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 0) 640 128 = 1073140660301707751739685208 := by decide +kernel
private theorem receipt_2_11_2383_0_part6 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 0) 768 128 = 661038884118515051211526344 := by decide +kernel
private theorem receipt_2_11_2383_0_part7 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 0) 896 128 = 282001731916951051335421828 := by decide +kernel
private theorem receipt_2_11_2383_0_part8 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 0) 1024 38 = 15435270531669056943521328 := by decide +kernel
private theorem receipt_2_11_2383_0_join0 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 0) 0 256 = 6771457191468614388406603520 :=
  phaseBlock_append receipt_2_11_2383_0_part0 receipt_2_11_2383_0_part1 rfl rfl rfl
private theorem receipt_2_11_2383_0_join1 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 0) 256 256 = 4526955807133909129400667904 :=
  phaseBlock_append receipt_2_11_2383_0_part2 receipt_2_11_2383_0_part3 rfl rfl rfl
private theorem receipt_2_11_2383_0_join2 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 0) 0 512 = 11298412998602523517807271424 :=
  phaseBlock_append receipt_2_11_2383_0_join0 receipt_2_11_2383_0_join1 rfl rfl rfl
private theorem receipt_2_11_2383_0_join3 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 0) 512 256 = 2593046547768157577813983448 :=
  phaseBlock_append receipt_2_11_2383_0_part4 receipt_2_11_2383_0_part5 rfl rfl rfl
private theorem receipt_2_11_2383_0_join4 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 0) 896 166 = 297437002448620108278943156 :=
  phaseBlock_append receipt_2_11_2383_0_part7 receipt_2_11_2383_0_part8 rfl rfl rfl
private theorem receipt_2_11_2383_0_join5 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 0) 768 294 = 958475886567135159490469500 :=
  phaseBlock_append receipt_2_11_2383_0_part6 receipt_2_11_2383_0_join4 rfl rfl rfl
private theorem receipt_2_11_2383_0_join6 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 0) 512 550 = 3551522434335292737304452948 :=
  phaseBlock_append receipt_2_11_2383_0_join3 receipt_2_11_2383_0_join5 rfl rfl rfl
private theorem receipt_2_11_2383_0_join7 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 0) 0 1062 = 14849935432937816255111724372 :=
  phaseBlock_append receipt_2_11_2383_0_join2 receipt_2_11_2383_0_join6 rfl rfl rfl

private theorem receipt_2_11_2383_0 : fastPhase (bank 2 11).shape 179808 2383 32 1 0 7 0 = 14849935432937816255111724372 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_2_11_2383_0_join7

private theorem receipt_2_11_2383_1_part0 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 1) 0 128 = 3681970744507485903929890752 := by decide +kernel
private theorem receipt_2_11_2383_1_part1 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 1) 128 128 = 3080194488043074050219800512 := by decide +kernel
private theorem receipt_2_11_2383_1_part2 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 1) 256 128 = 2519811875221398311160551360 := by decide +kernel
private theorem receipt_2_11_2383_1_part3 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 1) 384 128 = 1999083138585481063864580032 := by decide +kernel
private theorem receipt_2_11_2383_1_part4 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 1) 512 128 = 1516304653610111545851172800 := by decide +kernel
private theorem receipt_2_11_2383_1_part5 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 1) 640 128 = 1069808735516578237100247036 := by decide +kernel
private theorem receipt_2_11_2383_1_part6 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 1) 768 128 = 657964001869133196070133256 := by decide +kernel
private theorem receipt_2_11_2383_1_part7 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 1) 896 128 = 279171890031392836529303786 := by decide +kernel
private theorem receipt_2_11_2383_1_part8 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 1) 1024 38 = 14640596014983468813752398 := by decide +kernel
private theorem receipt_2_11_2383_1_join0 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 1) 0 256 = 6762165232550559954149691264 :=
  phaseBlock_append receipt_2_11_2383_1_part0 receipt_2_11_2383_1_part1 rfl rfl rfl
private theorem receipt_2_11_2383_1_join1 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 1) 256 256 = 4518895013806879375025131392 :=
  phaseBlock_append receipt_2_11_2383_1_part2 receipt_2_11_2383_1_part3 rfl rfl rfl
private theorem receipt_2_11_2383_1_join2 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 1) 0 512 = 11281060246357439329174822656 :=
  phaseBlock_append receipt_2_11_2383_1_join0 receipt_2_11_2383_1_join1 rfl rfl rfl
private theorem receipt_2_11_2383_1_join3 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 1) 512 256 = 2586113389126689782951419836 :=
  phaseBlock_append receipt_2_11_2383_1_part4 receipt_2_11_2383_1_part5 rfl rfl rfl
private theorem receipt_2_11_2383_1_join4 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 1) 896 166 = 293812486046376305343056184 :=
  phaseBlock_append receipt_2_11_2383_1_part7 receipt_2_11_2383_1_part8 rfl rfl rfl
private theorem receipt_2_11_2383_1_join5 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 1) 768 294 = 951776487915509501413189440 :=
  phaseBlock_append receipt_2_11_2383_1_part6 receipt_2_11_2383_1_join4 rfl rfl rfl
private theorem receipt_2_11_2383_1_join6 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 1) 512 550 = 3537889877042199284364609276 :=
  phaseBlock_append receipt_2_11_2383_1_join3 receipt_2_11_2383_1_join5 rfl rfl rfl
private theorem receipt_2_11_2383_1_join7 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2383 32 1 0 7 1) 0 1062 = 14818950123399638613539431932 :=
  phaseBlock_append receipt_2_11_2383_1_join2 receipt_2_11_2383_1_join6 rfl rfl rfl

private theorem receipt_2_11_2383_1 : fastPhase (bank 2 11).shape 179808 2383 32 1 0 7 1 = 14818950123399638613539431932 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_2_11_2383_1_join7

private theorem receipt_2_11_2384_0_part0 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 0) 0 128 = 3686810245294769117910699648 := by decide +kernel
private theorem receipt_2_11_2384_0_part1 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 0) 128 128 = 3084705552584953980988419712 := by decide +kernel
private theorem receipt_2_11_2384_0_part2 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 0) 256 128 = 2524008882572590778261524096 := by decide +kernel
private theorem receipt_2_11_2384_0_part3 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 0) 384 128 = 2002980136542996004832980608 := by decide +kernel
private theorem receipt_2_11_2384_0_part4 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 0) 512 128 = 1519915362293597574462705280 := by decide +kernel
private theorem receipt_2_11_2384_0_part5 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 0) 640 128 = 1073146548427416845861113984 := by decide +kernel
private theorem receipt_2_11_2384_0_part6 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 0) 768 128 = 661041994567967846679733730 := by decide +kernel
private theorem receipt_2_11_2384_0_part7 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 0) 896 128 = 282002839376457958327835033 := by decide +kernel
private theorem receipt_2_11_2384_0_part8 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 0) 1024 38 = 15435321856630865019045382 := by decide +kernel
private theorem receipt_2_11_2384_0_join0 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 0) 0 256 = 6771515797879723098899119360 :=
  phaseBlock_append receipt_2_11_2384_0_part0 receipt_2_11_2384_0_part1 rfl rfl rfl
private theorem receipt_2_11_2384_0_join1 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 0) 256 256 = 4526989019115586783094504704 :=
  phaseBlock_append receipt_2_11_2384_0_part2 receipt_2_11_2384_0_part3 rfl rfl rfl
private theorem receipt_2_11_2384_0_join2 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 0) 0 512 = 11298504816995309881993624064 :=
  phaseBlock_append receipt_2_11_2384_0_join0 receipt_2_11_2384_0_join1 rfl rfl rfl
private theorem receipt_2_11_2384_0_join3 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 0) 512 256 = 2593061910721014420323819264 :=
  phaseBlock_append receipt_2_11_2384_0_part4 receipt_2_11_2384_0_part5 rfl rfl rfl
private theorem receipt_2_11_2384_0_join4 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 0) 896 166 = 297438161233088823346880415 :=
  phaseBlock_append receipt_2_11_2384_0_part7 receipt_2_11_2384_0_part8 rfl rfl rfl
private theorem receipt_2_11_2384_0_join5 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 0) 768 294 = 958480155801056670026614145 :=
  phaseBlock_append receipt_2_11_2384_0_part6 receipt_2_11_2384_0_join4 rfl rfl rfl
private theorem receipt_2_11_2384_0_join6 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 0) 512 550 = 3551542066522071090350433409 :=
  phaseBlock_append receipt_2_11_2384_0_join3 receipt_2_11_2384_0_join5 rfl rfl rfl
private theorem receipt_2_11_2384_0_join7 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 0) 0 1062 = 14850046883517380972344057473 :=
  phaseBlock_append receipt_2_11_2384_0_join2 receipt_2_11_2384_0_join6 rfl rfl rfl

private theorem receipt_2_11_2384_0 : fastPhase (bank 2 11).shape 179808 2384 32 1 0 7 0 = 14850046883517380972344057473 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_2_11_2384_0_join7

private theorem receipt_2_11_2384_1_part0 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 1) 0 128 = 3682003691887878352467210624 := by decide +kernel
private theorem receipt_2_11_2384_1_part1 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 1) 128 128 = 3080220080565003624275890560 := by decide +kernel
private theorem receipt_2_11_2384_1_part2 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 1) 256 128 = 2519831136791697377432334720 := by decide +kernel
private theorem receipt_2_11_2384_1_part3 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 1) 384 128 = 1999097038744628057217110400 := by decide +kernel
private theorem receipt_2_11_2384_1_part4 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 1) 512 128 = 1516314108753339065478132096 := by decide +kernel
private theorem receipt_2_11_2384_1_part5 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 1) 640 128 = 1069814607260156236068905010 := by decide +kernel
private theorem receipt_2_11_2384_1_part6 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 1) 768 128 = 657967099025432593635781566 := by decide +kernel
private theorem receipt_2_11_2384_1_part7 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 1) 896 128 = 279172987045009652080112550 := by decide +kernel
private theorem receipt_2_11_2384_1_part8 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 1) 1024 38 = 14640644751755290532609880 := by decide +kernel
private theorem receipt_2_11_2384_1_join0 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 1) 0 256 = 6762223772452881976743101184 :=
  phaseBlock_append receipt_2_11_2384_1_part0 receipt_2_11_2384_1_part1 rfl rfl rfl
private theorem receipt_2_11_2384_1_join1 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 1) 256 256 = 4518928175536325434649445120 :=
  phaseBlock_append receipt_2_11_2384_1_part2 receipt_2_11_2384_1_part3 rfl rfl rfl
private theorem receipt_2_11_2384_1_join2 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 1) 0 512 = 11281151947989207411392546304 :=
  phaseBlock_append receipt_2_11_2384_1_join0 receipt_2_11_2384_1_join1 rfl rfl rfl
private theorem receipt_2_11_2384_1_join3 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 1) 512 256 = 2586128716013495301547037106 :=
  phaseBlock_append receipt_2_11_2384_1_part4 receipt_2_11_2384_1_part5 rfl rfl rfl
private theorem receipt_2_11_2384_1_join4 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 1) 896 166 = 293813631796764942612722430 :=
  phaseBlock_append receipt_2_11_2384_1_part7 receipt_2_11_2384_1_part8 rfl rfl rfl
private theorem receipt_2_11_2384_1_join5 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 1) 768 294 = 951780730822197536248503996 :=
  phaseBlock_append receipt_2_11_2384_1_part6 receipt_2_11_2384_1_join4 rfl rfl rfl
private theorem receipt_2_11_2384_1_join6 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 1) 512 550 = 3537909446835692837795541102 :=
  phaseBlock_append receipt_2_11_2384_1_join3 receipt_2_11_2384_1_join5 rfl rfl rfl
private theorem receipt_2_11_2384_1_join7 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2384 32 1 0 7 1) 0 1062 = 14819061394824900249188087406 :=
  phaseBlock_append receipt_2_11_2384_1_join2 receipt_2_11_2384_1_join6 rfl rfl rfl

private theorem receipt_2_11_2384_1 : fastPhase (bank 2 11).shape 179808 2384 32 1 0 7 1 = 14819061394824900249188087406 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_2_11_2384_1_join7

theorem receipt_2_11 : Checked (bank 2 11) 32 0 7 := by
  refine checked_from_values (bank 2 11) 32 0 7
    (P3_7_1.checked (bank 2 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4866_1061)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_11_2383_0 receipt_2_11_2383_1 receipt_2_11_2384_0 receipt_2_11_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_11_2383_0_part0 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 0) 0 128 = 391397807043993863371866144 := by decide +kernel
private theorem receipt_3_11_2383_0_part1 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 0) 128 128 = 309534514859343560412377120 := by decide +kernel
private theorem receipt_3_11_2383_0_part2 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 0) 256 128 = 233459999909502227970301984 := by decide +kernel
private theorem receipt_3_11_2383_0_part3 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 0) 384 128 = 163440800516376068320596000 := by decide +kernel
private theorem receipt_3_11_2383_0_part4 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 0) 512 128 = 99740510402181617392648224 := by decide +kernel
private theorem receipt_3_11_2383_0_part5 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 0) 640 128 = 42619788122683765041917984 := by decide +kernel
private theorem receipt_3_11_2383_0_part6 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 0) 768 42 = 2687164173842355183405457 := by decide +kernel
private theorem receipt_3_11_2383_0_join0 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 0) 128 256 = 542994514768845788382679104 :=
  phaseBlock_append receipt_3_11_2383_0_part1 receipt_3_11_2383_0_part2 rfl rfl rfl
private theorem receipt_3_11_2383_0_join1 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 0) 0 384 = 934392321812839651754545248 :=
  phaseBlock_append receipt_3_11_2383_0_part0 receipt_3_11_2383_0_join0 rfl rfl rfl
private theorem receipt_3_11_2383_0_join2 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 0) 384 256 = 263181310918557685713244224 :=
  phaseBlock_append receipt_3_11_2383_0_part3 receipt_3_11_2383_0_part4 rfl rfl rfl
private theorem receipt_3_11_2383_0_join3 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 0) 640 170 = 45306952296526120225323441 :=
  phaseBlock_append receipt_3_11_2383_0_part5 receipt_3_11_2383_0_part6 rfl rfl rfl
private theorem receipt_3_11_2383_0_join4 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 0) 384 426 = 308488263215083805938567665 :=
  phaseBlock_append receipt_3_11_2383_0_join2 receipt_3_11_2383_0_join3 rfl rfl rfl
private theorem receipt_3_11_2383_0_join5 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 0) 0 810 = 1242880585027923457693112913 :=
  phaseBlock_append receipt_3_11_2383_0_join1 receipt_3_11_2383_0_join4 rfl rfl rfl

private theorem receipt_3_11_2383_0 : fastPhase (bank 3 11).shape 179808 2383 32 1 1 1 0 = 1242880585027923457693112913 :=
  phase_of_block (n := 810) (by decide +kernel) receipt_3_11_2383_0_join5

private theorem receipt_3_11_2383_1_part0 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 1) 0 128 = 390744752337748290497627552 := by decide +kernel
private theorem receipt_3_11_2383_1_part1 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 1) 128 128 = 308923824920765712501290400 := by decide +kernel
private theorem receipt_3_11_2383_1_part2 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 1) 256 128 = 232893937831167999117895072 := by decide +kernel
private theorem receipt_3_11_2383_1_part3 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 1) 384 128 = 162921605142850941918156192 := by decide +kernel
private theorem receipt_3_11_2383_1_part4 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 1) 512 128 = 99270396406665491395708320 := by decide +kernel
private theorem receipt_3_11_2383_1_part5 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 1) 640 128 = 42200946083655777238742432 := by decide +kernel
private theorem receipt_3_11_2383_1_part6 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 1) 768 42 = 2561270596197295262091301 := by decide +kernel
private theorem receipt_3_11_2383_1_join0 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 1) 128 256 = 541817762751933711619185472 :=
  phaseBlock_append receipt_3_11_2383_1_part1 receipt_3_11_2383_1_part2 rfl rfl rfl
private theorem receipt_3_11_2383_1_join1 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 1) 0 384 = 932562515089682002116813024 :=
  phaseBlock_append receipt_3_11_2383_1_part0 receipt_3_11_2383_1_join0 rfl rfl rfl
private theorem receipt_3_11_2383_1_join2 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 1) 384 256 = 262192001549516433313864512 :=
  phaseBlock_append receipt_3_11_2383_1_part3 receipt_3_11_2383_1_part4 rfl rfl rfl
private theorem receipt_3_11_2383_1_join3 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 1) 640 170 = 44762216679853072500833733 :=
  phaseBlock_append receipt_3_11_2383_1_part5 receipt_3_11_2383_1_part6 rfl rfl rfl
private theorem receipt_3_11_2383_1_join4 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 1) 384 426 = 306954218229369505814698245 :=
  phaseBlock_append receipt_3_11_2383_1_join2 receipt_3_11_2383_1_join3 rfl rfl rfl
private theorem receipt_3_11_2383_1_join5 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2383 32 1 1 1 1) 0 810 = 1239516733319051507931511269 :=
  phaseBlock_append receipt_3_11_2383_1_join1 receipt_3_11_2383_1_join4 rfl rfl rfl

private theorem receipt_3_11_2383_1 : fastPhase (bank 3 11).shape 179808 2383 32 1 1 1 1 = 1239516733319051507931511269 :=
  phase_of_block (n := 810) (by decide +kernel) receipt_3_11_2383_1_join5

private theorem receipt_3_11_2384_0_part0 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 0) 0 128 = 391401150668223023628007488 := by decide +kernel
private theorem receipt_3_11_2384_0_part1 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 0) 128 128 = 309536736158698953722280000 := by decide +kernel
private theorem receipt_3_11_2384_0_part2 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 0) 256 128 = 233461365299466812178151488 := by decide +kernel
private theorem receipt_3_11_2384_0_part3 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 0) 384 128 = 163441545815782559526926400 := by decide +kernel
private theorem receipt_3_11_2384_0_part4 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 0) 512 128 = 99740841121809690672871488 := by decide +kernel
private theorem receipt_3_11_2384_0_part5 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 0) 640 128 = 42619879752977645862631488 := by decide +kernel
private theorem receipt_3_11_2384_0_part6 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 0) 768 42 = 2687167629561290764436604 := by decide +kernel
private theorem receipt_3_11_2384_0_join0 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 0) 128 256 = 542998101458165765900431488 :=
  phaseBlock_append receipt_3_11_2384_0_part1 receipt_3_11_2384_0_part2 rfl rfl rfl
private theorem receipt_3_11_2384_0_join1 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 0) 0 384 = 934399252126388789528438976 :=
  phaseBlock_append receipt_3_11_2384_0_part0 receipt_3_11_2384_0_join0 rfl rfl rfl
private theorem receipt_3_11_2384_0_join2 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 0) 384 256 = 263182386937592250199797888 :=
  phaseBlock_append receipt_3_11_2384_0_part3 receipt_3_11_2384_0_part4 rfl rfl rfl
private theorem receipt_3_11_2384_0_join3 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 0) 640 170 = 45307047382538936627068092 :=
  phaseBlock_append receipt_3_11_2384_0_part5 receipt_3_11_2384_0_part6 rfl rfl rfl
private theorem receipt_3_11_2384_0_join4 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 0) 384 426 = 308489434320131186826865980 :=
  phaseBlock_append receipt_3_11_2384_0_join2 receipt_3_11_2384_0_join3 rfl rfl rfl
private theorem receipt_3_11_2384_0_join5 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 0) 0 810 = 1242888686446519976355304956 :=
  phaseBlock_append receipt_3_11_2384_0_join1 receipt_3_11_2384_0_join4 rfl rfl rfl

private theorem receipt_3_11_2384_0 : fastPhase (bank 3 11).shape 179808 2384 32 1 1 1 0 = 1242888686446519976355304956 :=
  phase_of_block (n := 810) (by decide +kernel) receipt_3_11_2384_0_join5

private theorem receipt_3_11_2384_1_part0 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 1) 0 128 = 390748089542439320174983872 := by decide +kernel
private theorem receipt_3_11_2384_1_part1 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 1) 128 128 = 308926041237780311068113600 := by decide +kernel
private theorem receipt_3_11_2384_1_part2 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 1) 256 128 = 232895299506887471607052992 := by decide +kernel
private theorem receipt_3_11_2384_1_part3 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 1) 384 128 = 162922347828758020744542912 := by decide +kernel
private theorem receipt_3_11_2384_1_part4 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 1) 512 128 = 99270725447935902077680320 := by decide +kernel
private theorem receipt_3_11_2384_1_part5 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 1) 640 128 = 42201036806870194817333952 := by decide +kernel
private theorem receipt_3_11_2384_1_part6 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 1) 768 42 = 2561273894874343062231636 := by decide +kernel
private theorem receipt_3_11_2384_1_join0 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 1) 128 256 = 541821340744667782675166592 :=
  phaseBlock_append receipt_3_11_2384_1_part1 receipt_3_11_2384_1_part2 rfl rfl rfl
private theorem receipt_3_11_2384_1_join1 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 1) 0 384 = 932569430287107102850150464 :=
  phaseBlock_append receipt_3_11_2384_1_part0 receipt_3_11_2384_1_join0 rfl rfl rfl
private theorem receipt_3_11_2384_1_join2 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 1) 384 256 = 262193073276693922822223232 :=
  phaseBlock_append receipt_3_11_2384_1_part3 receipt_3_11_2384_1_part4 rfl rfl rfl
private theorem receipt_3_11_2384_1_join3 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 1) 640 170 = 44762310701744537879565588 :=
  phaseBlock_append receipt_3_11_2384_1_part5 receipt_3_11_2384_1_part6 rfl rfl rfl
private theorem receipt_3_11_2384_1_join4 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 1) 384 426 = 306955383978438460701788820 :=
  phaseBlock_append receipt_3_11_2384_1_join2 receipt_3_11_2384_1_join3 rfl rfl rfl
private theorem receipt_3_11_2384_1_join5 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2384 32 1 1 1 1) 0 810 = 1239524814265545563551939284 :=
  phaseBlock_append receipt_3_11_2384_1_join1 receipt_3_11_2384_1_join4 rfl rfl rfl

private theorem receipt_3_11_2384_1 : fastPhase (bank 3 11).shape 179808 2384 32 1 1 1 1 = 1239524814265545563551939284 :=
  phase_of_block (n := 810) (by decide +kernel) receipt_3_11_2384_1_join5

theorem receipt_3_11 : Checked (bank 3 11) 32 1 1 := by
  refine checked_from_values (bank 3 11) 32 1 1
    (P3_7_1.checked (bank 3 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3870_809)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_11_2383_0 receipt_3_11_2383_1 receipt_3_11_2384_0 receipt_3_11_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_12_2383_0_part0 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 0) 0 128 = 5238490746188642882954035541 := by decide +kernel
private theorem receipt_0_12_2383_0_part1 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 0) 128 128 = 4261253465255374462930181483 := by decide +kernel
private theorem receipt_0_12_2383_0_part2 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 0) 256 128 = 3348510865413549485726363834 := by decide +kernel
private theorem receipt_0_12_2383_0_part3 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 0) 384 128 = 2498055253998762039625772736 := by decide +kernel
private theorem receipt_0_12_2383_0_part4 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 0) 512 128 = 1707685233440257569941205279 := by decide +kernel
private theorem receipt_0_12_2383_0_part5 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 0) 640 128 = 975205962510840991399515102 := by decide +kernel
private theorem receipt_0_12_2383_0_part6 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 0) 768 123 = 298810199084552952804662193 := by decide +kernel
private theorem receipt_0_12_2383_0_join0 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 0) 128 256 = 7609764330668923948656545317 :=
  phaseBlock_append receipt_0_12_2383_0_part1 receipt_0_12_2383_0_part2 rfl rfl rfl
private theorem receipt_0_12_2383_0_join1 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 0) 0 384 = 12848255076857566831610580858 :=
  phaseBlock_append receipt_0_12_2383_0_part0 receipt_0_12_2383_0_join0 rfl rfl rfl
private theorem receipt_0_12_2383_0_join2 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 0) 384 256 = 4205740487439019609566978015 :=
  phaseBlock_append receipt_0_12_2383_0_part3 receipt_0_12_2383_0_part4 rfl rfl rfl
private theorem receipt_0_12_2383_0_join3 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 0) 640 251 = 1274016161595393944204177295 :=
  phaseBlock_append receipt_0_12_2383_0_part5 receipt_0_12_2383_0_part6 rfl rfl rfl
private theorem receipt_0_12_2383_0_join4 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 0) 384 507 = 5479756649034413553771155310 :=
  phaseBlock_append receipt_0_12_2383_0_join2 receipt_0_12_2383_0_join3 rfl rfl rfl
private theorem receipt_0_12_2383_0_join5 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 0) 0 891 = 18328011725891980385381736168 :=
  phaseBlock_append receipt_0_12_2383_0_join1 receipt_0_12_2383_0_join4 rfl rfl rfl

private theorem receipt_0_12_2383_0 : fastPhase (bank 0 12).shape 179808 2383 31 1 0 1 0 = 18328011725891980385381736168 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_0_12_2383_0_join5

private theorem receipt_0_12_2383_1_part0 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 1) 0 128 = 5230702518161570126110635157 := by decide +kernel
private theorem receipt_0_12_2383_1_part1 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 1) 128 128 = 4253960233982304220862078726 := by decide +kernel
private theorem receipt_0_12_2383_1_part2 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 1) 256 128 = 3341695957534470811731543376 := by decide +kernel
private theorem receipt_0_12_2383_1_part3 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 1) 384 128 = 2491702045786351881187145039 := by decide +kernel
private theorem receipt_0_12_2383_1_part4 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 1) 512 128 = 1701777151057171470652589045 := by decide +kernel
private theorem receipt_0_12_2383_1_part5 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 1) 640 128 = 969726481966583069966409895 := by decide +kernel
private theorem receipt_0_12_2383_1_part6 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 1) 768 123 = 293933256371264295087329577 := by decide +kernel
private theorem receipt_0_12_2383_1_join0 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 1) 128 256 = 7595656191516775032593622102 :=
  phaseBlock_append receipt_0_12_2383_1_part1 receipt_0_12_2383_1_part2 rfl rfl rfl
private theorem receipt_0_12_2383_1_join1 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 1) 0 384 = 12826358709678345158704257259 :=
  phaseBlock_append receipt_0_12_2383_1_part0 receipt_0_12_2383_1_join0 rfl rfl rfl
private theorem receipt_0_12_2383_1_join2 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 1) 384 256 = 4193479196843523351839734084 :=
  phaseBlock_append receipt_0_12_2383_1_part3 receipt_0_12_2383_1_part4 rfl rfl rfl
private theorem receipt_0_12_2383_1_join3 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 1) 640 251 = 1263659738337847365053739472 :=
  phaseBlock_append receipt_0_12_2383_1_part5 receipt_0_12_2383_1_part6 rfl rfl rfl
private theorem receipt_0_12_2383_1_join4 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 1) 384 507 = 5457138935181370716893473556 :=
  phaseBlock_append receipt_0_12_2383_1_join2 receipt_0_12_2383_1_join3 rfl rfl rfl
private theorem receipt_0_12_2383_1_join5 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2383 31 1 0 1 1) 0 891 = 18283497644859715875597730815 :=
  phaseBlock_append receipt_0_12_2383_1_join1 receipt_0_12_2383_1_join4 rfl rfl rfl

private theorem receipt_0_12_2383_1 : fastPhase (bank 0 12).shape 179808 2383 31 1 0 1 1 = 18283497644859715875597730815 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_0_12_2383_1_join5

private theorem receipt_0_12_2384_0_part0 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 0) 0 128 = 5238537337246823096904146151 := by decide +kernel
private theorem receipt_0_12_2384_0_part1 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 0) 128 128 = 4261288133355047117149293101 := by decide +kernel
private theorem receipt_0_12_2384_0_part2 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 0) 256 128 = 3348535454283783283027638508 := by decide +kernel
private theorem receipt_0_12_2384_0_part3 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 0) 384 128 = 2498071536632688110698450896 := by decide +kernel
private theorem receipt_0_12_2384_0_part4 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 0) 512 128 = 1707694900331707607981326638 := by decide +kernel
private theorem receipt_0_12_2384_0_part5 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 0) 640 128 = 975210622085907702836163945 := by decide +kernel
private theorem receipt_0_12_2384_0_part6 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 0) 768 123 = 298811379733215684088347009 := by decide +kernel
private theorem receipt_0_12_2384_0_join0 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 0) 128 256 = 7609823587638830400176931609 :=
  phaseBlock_append receipt_0_12_2384_0_part1 receipt_0_12_2384_0_part2 rfl rfl rfl
private theorem receipt_0_12_2384_0_join1 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 0) 0 384 = 12848360924885653497081077760 :=
  phaseBlock_append receipt_0_12_2384_0_part0 receipt_0_12_2384_0_join0 rfl rfl rfl
private theorem receipt_0_12_2384_0_join2 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 0) 384 256 = 4205766436964395718679777534 :=
  phaseBlock_append receipt_0_12_2384_0_part3 receipt_0_12_2384_0_part4 rfl rfl rfl
private theorem receipt_0_12_2384_0_join3 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 0) 640 251 = 1274022001819123386924510954 :=
  phaseBlock_append receipt_0_12_2384_0_part5 receipt_0_12_2384_0_part6 rfl rfl rfl
private theorem receipt_0_12_2384_0_join4 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 0) 384 507 = 5479788438783519105604288488 :=
  phaseBlock_append receipt_0_12_2384_0_join2 receipt_0_12_2384_0_join3 rfl rfl rfl
private theorem receipt_0_12_2384_0_join5 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 0) 0 891 = 18328149363669172602685366248 :=
  phaseBlock_append receipt_0_12_2384_0_join1 receipt_0_12_2384_0_join4 rfl rfl rfl

private theorem receipt_0_12_2384_0 : fastPhase (bank 0 12).shape 179808 2384 31 1 0 1 0 = 18328149363669172602685366248 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_0_12_2384_0_join5

private theorem receipt_0_12_2384_1_part0 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 1) 0 128 = 5230749052289511401991483421 := by decide +kernel
private theorem receipt_0_12_2384_1_part1 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 1) 128 128 = 4253994852454751779162656022 := by decide +kernel
private theorem receipt_0_12_2384_1_part2 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 1) 256 128 = 3341720503718030193282907248 := by decide +kernel
private theorem receipt_0_12_2384_1_part3 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 1) 384 128 = 2491718292299262868946400467 := by decide +kernel
private theorem receipt_0_12_2384_1_part4 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 1) 512 128 = 1701786788020095535628719857 := by decide +kernel
private theorem receipt_0_12_2384_1_part5 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 1) 640 128 = 969731117434607766777826092 := by decide +kernel
private theorem receipt_0_12_2384_1_part6 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 1) 768 123 = 293934418993927855673961175 := by decide +kernel
private theorem receipt_0_12_2384_1_join0 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 1) 128 256 = 7595715356172781972445563270 :=
  phaseBlock_append receipt_0_12_2384_1_part1 receipt_0_12_2384_1_part2 rfl rfl rfl
private theorem receipt_0_12_2384_1_join1 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 1) 0 384 = 12826464408462293374437046691 :=
  phaseBlock_append receipt_0_12_2384_1_part0 receipt_0_12_2384_1_join0 rfl rfl rfl
private theorem receipt_0_12_2384_1_join2 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 1) 384 256 = 4193505080319358404575120324 :=
  phaseBlock_append receipt_0_12_2384_1_part3 receipt_0_12_2384_1_part4 rfl rfl rfl
private theorem receipt_0_12_2384_1_join3 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 1) 640 251 = 1263665536428535622451787267 :=
  phaseBlock_append receipt_0_12_2384_1_part5 receipt_0_12_2384_1_part6 rfl rfl rfl
private theorem receipt_0_12_2384_1_join4 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 1) 384 507 = 5457170616747894027026907591 :=
  phaseBlock_append receipt_0_12_2384_1_join2 receipt_0_12_2384_1_join3 rfl rfl rfl
private theorem receipt_0_12_2384_1_join5 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2384 31 1 0 1 1) 0 891 = 18283635025210187401463954282 :=
  phaseBlock_append receipt_0_12_2384_1_join1 receipt_0_12_2384_1_join4 rfl rfl rfl

private theorem receipt_0_12_2384_1 : fastPhase (bank 0 12).shape 179808 2384 31 1 0 1 1 = 18283635025210187401463954282 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_0_12_2384_1_join5

theorem receipt_0_12 : Checked (bank 0 12) 31 0 1 := by
  refine checked_from_values (bank 0 12) 31 0 1
    (P3_7_1.checked (bank 0 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4255_890)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_12_2383_0 receipt_0_12_2383_1 receipt_0_12_2384_0 receipt_0_12_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_12_2383_0_part0 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 0) 0 128 = 4721633264762637279723080475 := by decide +kernel
private theorem receipt_1_12_2383_0_part1 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 0) 128 128 = 3837498939231088612612866857 := by decide +kernel
private theorem receipt_1_12_2383_0_part2 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 0) 256 128 = 3012918513856487340143826000 := by decide +kernel
private theorem receipt_1_12_2383_0_part3 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 0) 384 128 = 2245757058101110701230892466 := by decide +kernel
private theorem receipt_1_12_2383_0_part4 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 0) 512 128 = 1533892086659160660689044173 := by decide +kernel
private theorem receipt_1_12_2383_0_part5 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 0) 640 128 = 875213775456389526143689830 := by decide +kernel
private theorem receipt_1_12_2383_0_part6 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 0) 768 123 = 267966453665905385084007375 := by decide +kernel
private theorem receipt_1_12_2383_0_join0 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 0) 128 256 = 6850417453087575952756692857 :=
  phaseBlock_append receipt_1_12_2383_0_part1 receipt_1_12_2383_0_part2 rfl rfl rfl
private theorem receipt_1_12_2383_0_join1 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 0) 0 384 = 11572050717850213232479773332 :=
  phaseBlock_append receipt_1_12_2383_0_part0 receipt_1_12_2383_0_join0 rfl rfl rfl
private theorem receipt_1_12_2383_0_join2 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 0) 384 256 = 3779649144760271361919936639 :=
  phaseBlock_append receipt_1_12_2383_0_part3 receipt_1_12_2383_0_part4 rfl rfl rfl
private theorem receipt_1_12_2383_0_join3 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 0) 640 251 = 1143180229122294911227697205 :=
  phaseBlock_append receipt_1_12_2383_0_part5 receipt_1_12_2383_0_part6 rfl rfl rfl
private theorem receipt_1_12_2383_0_join4 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 0) 384 507 = 4922829373882566273147633844 :=
  phaseBlock_append receipt_1_12_2383_0_join2 receipt_1_12_2383_0_join3 rfl rfl rfl
private theorem receipt_1_12_2383_0_join5 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 0) 0 891 = 16494880091732779505627407176 :=
  phaseBlock_append receipt_1_12_2383_0_join1 receipt_1_12_2383_0_join4 rfl rfl rfl

private theorem receipt_1_12_2383_0 : fastPhase (bank 1 12).shape 179808 2383 31 1 0 2 0 = 16494880091732779505627407176 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_1_12_2383_0_join5

private theorem receipt_1_12_2383_1_part0 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 1) 0 128 = 4714581653986720328228163279 := by decide +kernel
private theorem receipt_1_12_2383_1_part1 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 1) 128 128 = 3830905114236837391826110742 := by decide +kernel
private theorem receipt_1_12_2383_1_part2 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 1) 256 128 = 3006766313038128256867130518 := by decide +kernel
private theorem receipt_1_12_2383_1_part3 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 1) 384 128 = 2240030416172292819033143019 := by decide +kernel
private theorem receipt_1_12_2383_1_part4 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 1) 512 128 = 1528575034737060530417983479 := by decide +kernel
private theorem receipt_1_12_2383_1_part5 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 1) 640 128 = 870290440873295149862054597 := by decide +kernel
private theorem receipt_1_12_2383_1_part6 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 1) 768 123 = 263591713591685983228604077 := by decide +kernel
private theorem receipt_1_12_2383_1_join0 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 1) 128 256 = 6837671427274965648693241260 :=
  phaseBlock_append receipt_1_12_2383_1_part1 receipt_1_12_2383_1_part2 rfl rfl rfl
private theorem receipt_1_12_2383_1_join1 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 1) 0 384 = 11552253081261685976921404539 :=
  phaseBlock_append receipt_1_12_2383_1_part0 receipt_1_12_2383_1_join0 rfl rfl rfl
private theorem receipt_1_12_2383_1_join2 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 1) 384 256 = 3768605450909353349451126498 :=
  phaseBlock_append receipt_1_12_2383_1_part3 receipt_1_12_2383_1_part4 rfl rfl rfl
private theorem receipt_1_12_2383_1_join3 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 1) 640 251 = 1133882154464981133090658674 :=
  phaseBlock_append receipt_1_12_2383_1_part5 receipt_1_12_2383_1_part6 rfl rfl rfl
private theorem receipt_1_12_2383_1_join4 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 1) 384 507 = 4902487605374334482541785172 :=
  phaseBlock_append receipt_1_12_2383_1_join2 receipt_1_12_2383_1_join3 rfl rfl rfl
private theorem receipt_1_12_2383_1_join5 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2383 31 1 0 2 1) 0 891 = 16454740686636020459463189711 :=
  phaseBlock_append receipt_1_12_2383_1_join1 receipt_1_12_2383_1_join4 rfl rfl rfl

private theorem receipt_1_12_2383_1 : fastPhase (bank 1 12).shape 179808 2383 31 1 0 2 1 = 16454740686636020459463189711 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_1_12_2383_1_join5

private theorem receipt_1_12_2384_0_part0 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 0) 0 128 = 4721675259148418283454038897 := by decide +kernel
private theorem receipt_1_12_2384_0_part1 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 0) 128 128 = 3837530160023903767972188609 := by decide +kernel
private theorem receipt_1_12_2384_0_part2 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 0) 256 128 = 3012940638572529671651253930 := by decide +kernel
private theorem receipt_1_12_2384_0_part3 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 0) 384 128 = 2245771696360877039539144854 := by decide +kernel
private theorem receipt_1_12_2384_0_part4 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 0) 512 128 = 1533900769836494906041135269 := by decide +kernel
private theorem receipt_1_12_2384_0_part5 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 0) 640 128 = 875217957320807705729222346 := by decide +kernel
private theorem receipt_1_12_2384_0_part6 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 0) 768 123 = 267967512457367063295845254 := by decide +kernel
private theorem receipt_1_12_2384_0_join0 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 0) 128 256 = 6850470798596433439623442539 :=
  phaseBlock_append receipt_1_12_2384_0_part1 receipt_1_12_2384_0_part2 rfl rfl rfl
private theorem receipt_1_12_2384_0_join1 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 0) 0 384 = 11572146057744851723077481436 :=
  phaseBlock_append receipt_1_12_2384_0_part0 receipt_1_12_2384_0_join0 rfl rfl rfl
private theorem receipt_1_12_2384_0_join2 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 0) 384 256 = 3779672466197371945580280123 :=
  phaseBlock_append receipt_1_12_2384_0_part3 receipt_1_12_2384_0_part4 rfl rfl rfl
private theorem receipt_1_12_2384_0_join3 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 0) 640 251 = 1143185469778174769025067600 :=
  phaseBlock_append receipt_1_12_2384_0_part5 receipt_1_12_2384_0_part6 rfl rfl rfl
private theorem receipt_1_12_2384_0_join4 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 0) 384 507 = 4922857935975546714605347723 :=
  phaseBlock_append receipt_1_12_2384_0_join2 receipt_1_12_2384_0_join3 rfl rfl rfl
private theorem receipt_1_12_2384_0_join5 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 0) 0 891 = 16495003993720398437682829159 :=
  phaseBlock_append receipt_1_12_2384_0_join1 receipt_1_12_2384_0_join4 rfl rfl rfl

private theorem receipt_1_12_2384_0 : fastPhase (bank 1 12).shape 179808 2384 31 1 0 2 0 = 16495003993720398437682829159 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_1_12_2384_0_join5

private theorem receipt_1_12_2384_1_part0 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 1) 0 128 = 4714623596775955942581924933 := by decide +kernel
private theorem receipt_1_12_2384_1_part1 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 1) 128 128 = 3830936290126753498551342204 := by decide +kernel
private theorem receipt_1_12_2384_1_part2 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 1) 256 128 = 3006788399196216763131220470 := by decide +kernel
private theorem receipt_1_12_2384_1_part3 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 1) 384 128 = 2240045021860436055727046463 := by decide +kernel
private theorem receipt_1_12_2384_1_part4 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 1) 512 128 = 1528583690973398702940655794 := by decide +kernel
private theorem receipt_1_12_2384_1_part5 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 1) 640 128 = 870294601074942606334218081 := by decide +kernel
private theorem receipt_1_12_2384_1_part6 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 1) 768 123 = 263592756212690093023784001 := by decide +kernel
private theorem receipt_1_12_2384_1_join0 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 1) 128 256 = 6837724689322970261682562674 :=
  phaseBlock_append receipt_1_12_2384_1_part1 receipt_1_12_2384_1_part2 rfl rfl rfl
private theorem receipt_1_12_2384_1_join1 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 1) 0 384 = 11552348286098926204264487607 :=
  phaseBlock_append receipt_1_12_2384_1_part0 receipt_1_12_2384_1_join0 rfl rfl rfl
private theorem receipt_1_12_2384_1_join2 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 1) 384 256 = 3768628712833834758667702257 :=
  phaseBlock_append receipt_1_12_2384_1_part3 receipt_1_12_2384_1_part4 rfl rfl rfl
private theorem receipt_1_12_2384_1_join3 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 1) 640 251 = 1133887357287632699358002082 :=
  phaseBlock_append receipt_1_12_2384_1_part5 receipt_1_12_2384_1_part6 rfl rfl rfl
private theorem receipt_1_12_2384_1_join4 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 1) 384 507 = 4902516070121467458025704339 :=
  phaseBlock_append receipt_1_12_2384_1_join2 receipt_1_12_2384_1_join3 rfl rfl rfl
private theorem receipt_1_12_2384_1_join5 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2384 31 1 0 2 1) 0 891 = 16454864356220393662290191946 :=
  phaseBlock_append receipt_1_12_2384_1_join1 receipt_1_12_2384_1_join4 rfl rfl rfl

private theorem receipt_1_12_2384_1 : fastPhase (bank 1 12).shape 179808 2384 31 1 0 2 1 = 16454864356220393662290191946 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_1_12_2384_1_join5

theorem receipt_1_12 : Checked (bank 1 12) 31 0 2 := by
  refine checked_from_values (bank 1 12) 31 0 2
    (P3_7_1.checked (bank 1 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4255_890)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_12_2383_0 receipt_1_12_2383_1 receipt_1_12_2384_0 receipt_1_12_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_12_2383_0_part0 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 0) 0 128 = 2567216526653114932823028480 := by decide +kernel
private theorem receipt_2_12_2383_0_part1 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 0) 128 128 = 2073684972628922141547934464 := by decide +kernel
private theorem receipt_2_12_2383_0_part2 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 0) 256 128 = 1618062247358170093607187200 := by decide +kernel
private theorem receipt_2_12_2383_0_part3 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 0) 384 128 = 1198602714486340339061764864 := by decide +kernel
private theorem receipt_2_12_2383_0_part4 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 0) 512 128 = 813597508352184471324640266 := by decide +kernel
private theorem receipt_2_12_2383_0_part5 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 0) 640 128 = 461374746402071379238769304 := by decide +kernel
private theorem receipt_2_12_2383_0_part6 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 0) 768 123 = 140475463303951231757534196 := by decide +kernel
private theorem receipt_2_12_2383_0_join0 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 0) 128 256 = 3691747219987092235155121664 :=
  phaseBlock_append receipt_2_12_2383_0_part1 receipt_2_12_2383_0_part2 rfl rfl rfl
private theorem receipt_2_12_2383_0_join1 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 0) 0 384 = 6258963746640207167978150144 :=
  phaseBlock_append receipt_2_12_2383_0_part0 receipt_2_12_2383_0_join0 rfl rfl rfl
private theorem receipt_2_12_2383_0_join2 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 0) 384 256 = 2012200222838524810386405130 :=
  phaseBlock_append receipt_2_12_2383_0_part3 receipt_2_12_2383_0_part4 rfl rfl rfl
private theorem receipt_2_12_2383_0_join3 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 0) 640 251 = 601850209706022610996303500 :=
  phaseBlock_append receipt_2_12_2383_0_part5 receipt_2_12_2383_0_part6 rfl rfl rfl
private theorem receipt_2_12_2383_0_join4 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 0) 384 507 = 2614050432544547421382708630 :=
  phaseBlock_append receipt_2_12_2383_0_join2 receipt_2_12_2383_0_join3 rfl rfl rfl
private theorem receipt_2_12_2383_0_join5 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 0) 0 891 = 8873014179184754589360858774 :=
  phaseBlock_append receipt_2_12_2383_0_join1 receipt_2_12_2383_0_join4 rfl rfl rfl

private theorem receipt_2_12_2383_0 : fastPhase (bank 2 12).shape 179808 2383 31 1 0 7 0 = 8873014179184754589360858774 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_2_12_2383_0_join5

private theorem receipt_2_12_2383_1_part0 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 1) 0 128 = 2563259094507192673022786880 := by decide +kernel
private theorem receipt_2_12_2383_1_part1 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 1) 128 128 = 2070021819587080928657415488 := by decide +kernel
private theorem receipt_2_12_2383_1_part2 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 1) 256 128 = 1614679983164912059894463808 := by decide +kernel
private theorem receipt_2_12_2383_1_part3 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 1) 384 128 = 1195488230385647855145835840 := by decide +kernel
private theorem receipt_2_12_2383_1_part4 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 1) 512 128 = 810737974679836981717192046 := by decide +kernel
private theorem receipt_2_12_2383_1_part5 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 1) 640 128 = 458757606838995864880027096 := by decide +kernel
private theorem receipt_2_12_2383_1_part6 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 1) 768 123 = 138177503726144229806633790 := by decide +kernel
private theorem receipt_2_12_2383_1_join0 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 1) 128 256 = 3684701802751992988551879296 :=
  phaseBlock_append receipt_2_12_2383_1_part1 receipt_2_12_2383_1_part2 rfl rfl rfl
private theorem receipt_2_12_2383_1_join1 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 1) 0 384 = 6247960897259185661574666176 :=
  phaseBlock_append receipt_2_12_2383_1_part0 receipt_2_12_2383_1_join0 rfl rfl rfl
private theorem receipt_2_12_2383_1_join2 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 1) 384 256 = 2006226205065484836863027886 :=
  phaseBlock_append receipt_2_12_2383_1_part3 receipt_2_12_2383_1_part4 rfl rfl rfl
private theorem receipt_2_12_2383_1_join3 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 1) 640 251 = 596935110565140094686660886 :=
  phaseBlock_append receipt_2_12_2383_1_part5 receipt_2_12_2383_1_part6 rfl rfl rfl
private theorem receipt_2_12_2383_1_join4 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 1) 384 507 = 2603161315630624931549688772 :=
  phaseBlock_append receipt_2_12_2383_1_join2 receipt_2_12_2383_1_join3 rfl rfl rfl
private theorem receipt_2_12_2383_1_join5 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2383 31 1 0 7 1) 0 891 = 8851122212889810593124354948 :=
  phaseBlock_append receipt_2_12_2383_1_join1 receipt_2_12_2383_1_join4 rfl rfl rfl

private theorem receipt_2_12_2383_1 : fastPhase (bank 2 12).shape 179808 2383 31 1 0 7 1 = 8851122212889810593124354948 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_2_12_2383_1_join5

private theorem receipt_2_12_2384_0_part0 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 0) 0 128 = 2567239142420682230243903520 := by decide +kernel
private theorem receipt_2_12_2384_0_part1 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 0) 128 128 = 2073701710243953065986299936 := by decide +kernel
private theorem receipt_2_12_2384_0_part2 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 0) 256 128 = 1618074060093140576606906400 := by decide +kernel
private theorem receipt_2_12_2384_0_part3 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 0) 384 128 = 1198610500298427824669046816 := by decide +kernel
private theorem receipt_2_12_2384_0_part4 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 0) 512 128 = 813602110565227645378087665 := by decide +kernel
private theorem receipt_2_12_2384_0_part5 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 0) 640 128 = 461376951114748768471924263 := by decide +kernel
private theorem receipt_2_12_2384_0_part6 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 0) 768 123 = 140476018395958782254058315 := by decide +kernel
private theorem receipt_2_12_2384_0_join0 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 0) 128 256 = 3691775770337093642593206336 :=
  phaseBlock_append receipt_2_12_2384_0_part1 receipt_2_12_2384_0_part2 rfl rfl rfl
private theorem receipt_2_12_2384_0_join1 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 0) 0 384 = 6259014912757775872837109856 :=
  phaseBlock_append receipt_2_12_2384_0_part0 receipt_2_12_2384_0_join0 rfl rfl rfl
private theorem receipt_2_12_2384_0_join2 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 0) 384 256 = 2012212610863655470047134481 :=
  phaseBlock_append receipt_2_12_2384_0_part3 receipt_2_12_2384_0_part4 rfl rfl rfl
private theorem receipt_2_12_2384_0_join3 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 0) 640 251 = 601852969510707550725982578 :=
  phaseBlock_append receipt_2_12_2384_0_part5 receipt_2_12_2384_0_part6 rfl rfl rfl
private theorem receipt_2_12_2384_0_join4 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 0) 384 507 = 2614065580374363020773117059 :=
  phaseBlock_append receipt_2_12_2384_0_join2 receipt_2_12_2384_0_join3 rfl rfl rfl
private theorem receipt_2_12_2384_0_join5 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 0) 0 891 = 8873080493132138893610226915 :=
  phaseBlock_append receipt_2_12_2384_0_join1 receipt_2_12_2384_0_join4 rfl rfl rfl

private theorem receipt_2_12_2384_0 : fastPhase (bank 2 12).shape 179808 2384 31 1 0 7 0 = 8873080493132138893610226915 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_2_12_2384_0_join5

private theorem receipt_2_12_2384_1_part0 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 1) 0 128 = 2563281681398402393989879200 := by decide +kernel
private theorem receipt_2_12_2384_1_part1 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 1) 128 128 = 2070038532321307171689383328 := by decide +kernel
private theorem receipt_2_12_2384_1_part2 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 1) 256 128 = 1614691774741604409918027168 := by decide +kernel
private theorem receipt_2_12_2384_1_part3 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 1) 384 128 = 1195495998495867489057056160 := by decide +kernel
private theorem receipt_2_12_2384_1_part4 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 1) 512 128 = 810742562390329898077380789 := by decide +kernel
private theorem receipt_2_12_2384_1_part5 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 1) 640 128 = 458759800026646811879421537 := by decide +kernel
private theorem receipt_2_12_2384_1_part6 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 1) 768 123 = 138178050321538327597681168 := by decide +kernel
private theorem receipt_2_12_2384_1_join0 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 1) 128 256 = 3684730307062911581607410496 :=
  phaseBlock_append receipt_2_12_2384_1_part1 receipt_2_12_2384_1_part2 rfl rfl rfl
private theorem receipt_2_12_2384_1_join1 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 1) 0 384 = 6248011988461313975597289696 :=
  phaseBlock_append receipt_2_12_2384_1_part0 receipt_2_12_2384_1_join0 rfl rfl rfl
private theorem receipt_2_12_2384_1_join2 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 1) 384 256 = 2006238560886197387134436949 :=
  phaseBlock_append receipt_2_12_2384_1_part3 receipt_2_12_2384_1_part4 rfl rfl rfl
private theorem receipt_2_12_2384_1_join3 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 1) 640 251 = 596937850348185139477102705 :=
  phaseBlock_append receipt_2_12_2384_1_part5 receipt_2_12_2384_1_part6 rfl rfl rfl
private theorem receipt_2_12_2384_1_join4 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 1) 384 507 = 2603176411234382526611539654 :=
  phaseBlock_append receipt_2_12_2384_1_join2 receipt_2_12_2384_1_join3 rfl rfl rfl
private theorem receipt_2_12_2384_1_join5 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2384 31 1 0 7 1) 0 891 = 8851188399695696502208829350 :=
  phaseBlock_append receipt_2_12_2384_1_join1 receipt_2_12_2384_1_join4 rfl rfl rfl

private theorem receipt_2_12_2384_1 : fastPhase (bank 2 12).shape 179808 2384 31 1 0 7 1 = 8851188399695696502208829350 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_2_12_2384_1_join5

theorem receipt_2_12 : Checked (bank 2 12) 31 0 7 := by
  refine checked_from_values (bank 2 12) 31 0 7
    (P3_7_1.checked (bank 2 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4235_890)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_12_2383_0 receipt_2_12_2383_1 receipt_2_12_2384_0 receipt_2_12_2384_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_12_2383_0_part0 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 0) 0 128 = 473319642762680491459081568 := by decide +kernel
private theorem receipt_3_12_2383_0_part1 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 0) 128 128 = 385991716605640648189519200 := by decide +kernel
private theorem receipt_3_12_2383_0_part2 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 0) 256 128 = 304259970441771135388702048 := by decide +kernel
private theorem receipt_3_12_2383_0_part3 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 0) 384 128 = 228350742578452386137965920 := by decide +kernel
private theorem receipt_3_12_2383_0_part4 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 0) 512 128 = 158487636813638821293372768 := by decide +kernel
private theorem receipt_3_12_2383_0_part5 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 0) 640 128 = 94891531869096869757347168 := by decide +kernel
private theorem receipt_3_12_2383_0_part6 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 0) 768 128 = 37780590823642988750312800 := by decide +kernel
private theorem receipt_3_12_2383_0_part7 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 0) 896 29 = 1311033718056132933933483 := by decide +kernel
private theorem receipt_3_12_2383_0_join0 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 0) 0 256 = 859311359368321139648600768 :=
  phaseBlock_append receipt_3_12_2383_0_part0 receipt_3_12_2383_0_part1 rfl rfl rfl
private theorem receipt_3_12_2383_0_join1 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 0) 256 256 = 532610713020223521526667968 :=
  phaseBlock_append receipt_3_12_2383_0_part2 receipt_3_12_2383_0_part3 rfl rfl rfl
private theorem receipt_3_12_2383_0_join2 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 0) 0 512 = 1391922072388544661175268736 :=
  phaseBlock_append receipt_3_12_2383_0_join0 receipt_3_12_2383_0_join1 rfl rfl rfl
private theorem receipt_3_12_2383_0_join3 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 0) 512 256 = 253379168682735691050719936 :=
  phaseBlock_append receipt_3_12_2383_0_part4 receipt_3_12_2383_0_part5 rfl rfl rfl
private theorem receipt_3_12_2383_0_join4 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 0) 768 157 = 39091624541699121684246283 :=
  phaseBlock_append receipt_3_12_2383_0_part6 receipt_3_12_2383_0_part7 rfl rfl rfl
private theorem receipt_3_12_2383_0_join5 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 0) 512 413 = 292470793224434812734966219 :=
  phaseBlock_append receipt_3_12_2383_0_join3 receipt_3_12_2383_0_join4 rfl rfl rfl
private theorem receipt_3_12_2383_0_join6 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 0) 0 925 = 1684392865612979473910234955 :=
  phaseBlock_append receipt_3_12_2383_0_join2 receipt_3_12_2383_0_join5 rfl rfl rfl

private theorem receipt_3_12_2383_0 : fastPhase (bank 3 12).shape 179808 2383 31 1 1 1 0 = 1684392865612979473910234955 :=
  phase_of_block (n := 925) (by decide +kernel) receipt_3_12_2383_0_join6

private theorem receipt_3_12_2383_1_part0 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 1) 0 128 = 472625357038342057555646816 := by decide +kernel
private theorem receipt_3_12_2383_1_part1 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 1) 128 128 = 385338497252098809773549920 := by decide +kernel
private theorem receipt_3_12_2383_1_part2 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 1) 256 128 = 303649745585661216682932576 := by decide +kernel
private theorem receipt_3_12_2383_1_part3 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 1) 384 128 = 227785417816345441030768992 := by decide +kernel
private theorem receipt_3_12_2383_1_part4 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 1) 512 128 = 157969095288686458607245664 := by decide +kernel
private theorem receipt_3_12_2383_1_part5 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 1) 640 128 = 94421634347676078517397856 := by decide +kernel
private theorem receipt_3_12_2383_1_part6 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 1) 768 128 = 37361175772000963452746080 := by decide +kernel
private theorem receipt_3_12_2383_1_part7 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 1) 896 29 = 1223212100642281580955831 := by decide +kernel
private theorem receipt_3_12_2383_1_join0 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 1) 0 256 = 857963854290440867329196736 :=
  phaseBlock_append receipt_3_12_2383_1_part0 receipt_3_12_2383_1_part1 rfl rfl rfl
private theorem receipt_3_12_2383_1_join1 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 1) 256 256 = 531435163402006657713701568 :=
  phaseBlock_append receipt_3_12_2383_1_part2 receipt_3_12_2383_1_part3 rfl rfl rfl
private theorem receipt_3_12_2383_1_join2 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 1) 0 512 = 1389399017692447525042898304 :=
  phaseBlock_append receipt_3_12_2383_1_join0 receipt_3_12_2383_1_join1 rfl rfl rfl
private theorem receipt_3_12_2383_1_join3 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 1) 512 256 = 252390729636362537124643520 :=
  phaseBlock_append receipt_3_12_2383_1_part4 receipt_3_12_2383_1_part5 rfl rfl rfl
private theorem receipt_3_12_2383_1_join4 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 1) 768 157 = 38584387872643245033701911 :=
  phaseBlock_append receipt_3_12_2383_1_part6 receipt_3_12_2383_1_part7 rfl rfl rfl
private theorem receipt_3_12_2383_1_join5 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 1) 512 413 = 290975117509005782158345431 :=
  phaseBlock_append receipt_3_12_2383_1_join3 receipt_3_12_2383_1_join4 rfl rfl rfl
private theorem receipt_3_12_2383_1_join6 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2383 31 1 1 1 1) 0 925 = 1680374135201453307201243735 :=
  phaseBlock_append receipt_3_12_2383_1_join2 receipt_3_12_2383_1_join5 rfl rfl rfl

private theorem receipt_3_12_2383_1 : fastPhase (bank 3 12).shape 179808 2383 31 1 1 1 1 = 1680374135201453307201243735 :=
  phase_of_block (n := 925) (by decide +kernel) receipt_3_12_2383_1_join6

private theorem receipt_3_12_2384_0_part0 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 0) 0 128 = 473323719733746181518321888 := by decide +kernel
private theorem receipt_3_12_2384_0_part1 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 0) 128 128 = 385994560920719184433617120 := by decide +kernel
private theorem receipt_3_12_2384_0_part2 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 0) 256 128 = 304261843364803469601163488 := by decide +kernel
private theorem receipt_3_12_2384_0_part3 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 0) 384 128 = 228351878340961566569199840 := by decide +kernel
private theorem receipt_3_12_2384_0_part4 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 0) 512 128 = 158488242885168277810161888 := by decide +kernel
private theorem receipt_3_12_2384_0_part5 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 0) 640 128 = 94891789226769089690097888 := by decide +kernel
private theorem receipt_3_12_2384_0_part6 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 0) 768 128 = 37780654220838583438084320 := by decide +kernel
private theorem receipt_3_12_2384_0_part7 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 0) 896 29 = 1311034927628668477702923 := by decide +kernel
private theorem receipt_3_12_2384_0_join0 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 0) 0 256 = 859318280654465365951939008 :=
  phaseBlock_append receipt_3_12_2384_0_part0 receipt_3_12_2384_0_part1 rfl rfl rfl
private theorem receipt_3_12_2384_0_join1 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 0) 256 256 = 532613721705765036170363328 :=
  phaseBlock_append receipt_3_12_2384_0_part2 receipt_3_12_2384_0_part3 rfl rfl rfl
private theorem receipt_3_12_2384_0_join2 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 0) 0 512 = 1391932002360230402122302336 :=
  phaseBlock_append receipt_3_12_2384_0_join0 receipt_3_12_2384_0_join1 rfl rfl rfl
private theorem receipt_3_12_2384_0_join3 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 0) 512 256 = 253380032111937367500259776 :=
  phaseBlock_append receipt_3_12_2384_0_part4 receipt_3_12_2384_0_part5 rfl rfl rfl
private theorem receipt_3_12_2384_0_join4 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 0) 768 157 = 39091689148467251915787243 :=
  phaseBlock_append receipt_3_12_2384_0_part6 receipt_3_12_2384_0_part7 rfl rfl rfl
private theorem receipt_3_12_2384_0_join5 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 0) 512 413 = 292471721260404619416047019 :=
  phaseBlock_append receipt_3_12_2384_0_join3 receipt_3_12_2384_0_join4 rfl rfl rfl
private theorem receipt_3_12_2384_0_join6 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 0) 0 925 = 1684403723620635021538349355 :=
  phaseBlock_append receipt_3_12_2384_0_join2 receipt_3_12_2384_0_join5 rfl rfl rfl

private theorem receipt_3_12_2384_0 : fastPhase (bank 3 12).shape 179808 2384 31 1 1 1 0 = 1684403723620635021538349355 :=
  phase_of_block (n := 925) (by decide +kernel) receipt_3_12_2384_0_join6

private theorem receipt_3_12_2384_1_part0 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 1) 0 128 = 472629427100702702165362272 := by decide +kernel
private theorem receipt_3_12_2384_1_part1 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 1) 128 128 = 385341336062512473489667680 := by decide +kernel
private theorem receipt_3_12_2384_1_part2 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 1) 256 128 = 303651614258452981810914912 := by decide +kernel
private theorem receipt_3_12_2384_1_part3 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 1) 384 128 = 227786550435064439992211040 := by decide +kernel
private theorem receipt_3_12_2384_1_part4 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 1) 512 128 = 157969699176538524092253792 := by decide +kernel
private theorem receipt_3_12_2384_1_part5 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 1) 640 128 = 94421890337076784334747232 := by decide +kernel
private theorem receipt_3_12_2384_1_part6 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 1) 768 128 = 37361238473249056077817440 := by decide +kernel
private theorem receipt_3_12_2384_1_part7 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 1) 896 29 = 1223213231335855557182427 := by decide +kernel
private theorem receipt_3_12_2384_1_join0 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 1) 0 256 = 857970763163215175655029952 :=
  phaseBlock_append receipt_3_12_2384_1_part0 receipt_3_12_2384_1_part1 rfl rfl rfl
private theorem receipt_3_12_2384_1_join1 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 1) 256 256 = 531438164693517421803125952 :=
  phaseBlock_append receipt_3_12_2384_1_part2 receipt_3_12_2384_1_part3 rfl rfl rfl
private theorem receipt_3_12_2384_1_join2 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 1) 0 512 = 1389408927856732597458155904 :=
  phaseBlock_append receipt_3_12_2384_1_join0 receipt_3_12_2384_1_join1 rfl rfl rfl
private theorem receipt_3_12_2384_1_join3 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 1) 512 256 = 252391589513615308427001024 :=
  phaseBlock_append receipt_3_12_2384_1_part4 receipt_3_12_2384_1_part5 rfl rfl rfl
private theorem receipt_3_12_2384_1_join4 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 1) 768 157 = 38584451704584911634999867 :=
  phaseBlock_append receipt_3_12_2384_1_part6 receipt_3_12_2384_1_part7 rfl rfl rfl
private theorem receipt_3_12_2384_1_join5 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 1) 512 413 = 290976041218200220062000891 :=
  phaseBlock_append receipt_3_12_2384_1_join3 receipt_3_12_2384_1_join4 rfl rfl rfl
private theorem receipt_3_12_2384_1_join6 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2384 31 1 1 1 1) 0 925 = 1680384969074932817520156795 :=
  phaseBlock_append receipt_3_12_2384_1_join2 receipt_3_12_2384_1_join5 rfl rfl rfl

private theorem receipt_3_12_2384_1 : fastPhase (bank 3 12).shape 179808 2384 31 1 1 1 1 = 1680384969074932817520156795 :=
  phase_of_block (n := 925) (by decide +kernel) receipt_3_12_2384_1_join6

theorem receipt_3_12 : Checked (bank 3 12) 31 1 1 := by
  refine checked_from_values (bank 3 12) 31 1 1
    (P3_7_1.checked (bank 3 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4235_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_12_2383_0 receipt_3_12_2383_1 receipt_3_12_2384_0 receipt_3_12_2384_1 (by decide +kernel) (by decide +kernel)

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
    (word : K1.I → K1_14.L) (lo : 2383 ≤ h) (hi : h ≤ 33599) (rect : Fin 4)
    (i : Fin 2) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group4_stage i)).shape
      (cutoff h rect (group4_stage i)), ¬ G∣Q :=
  (group4_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group4_avoids

end Lower6960.RescueSource
