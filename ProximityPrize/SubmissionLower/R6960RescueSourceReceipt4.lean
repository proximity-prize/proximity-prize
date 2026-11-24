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

private theorem receipt_0_11_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 0) 0 128 = 8920813190610197612036001600 := by decide +kernel
private theorem receipt_0_11_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 0) 128 128 = 7519845439979094352221712192 := by decide +kernel
private theorem receipt_0_11_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 0) 256 128 = 6199269128203426430702702400 := by decide +kernel
private theorem receipt_0_11_2359_0_part3 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 0) 384 128 = 4956698822462846364042358592 := by decide +kernel
private theorem receipt_0_11_2359_0_part4 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 0) 512 128 = 3789755886252854029563531072 := by decide +kernel
private theorem receipt_0_11_2359_0_part5 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 0) 640 128 = 2696068768544075133436642935 := by decide +kernel
private theorem receipt_0_11_2359_0_part6 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 0) 768 128 = 1673274673687441570200516379 := by decide +kernel
private theorem receipt_0_11_2359_0_part7 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 0) 896 128 = 719011348964575172688102434 := by decide +kernel
private theorem receipt_0_11_2359_0_part8 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 0) 1024 38 = 39569906235847260087817899 := by decide +kernel
private theorem receipt_0_11_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 0) 0 256 = 16440658630589291964257713792 :=
  phaseBlock_append receipt_0_11_2359_0_part0 receipt_0_11_2359_0_part1 rfl rfl rfl
private theorem receipt_0_11_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 0) 256 256 = 11155967950666272794745060992 :=
  phaseBlock_append receipt_0_11_2359_0_part2 receipt_0_11_2359_0_part3 rfl rfl rfl
private theorem receipt_0_11_2359_0_join2 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 0) 0 512 = 27596626581255564759002774784 :=
  phaseBlock_append receipt_0_11_2359_0_join0 receipt_0_11_2359_0_join1 rfl rfl rfl
private theorem receipt_0_11_2359_0_join3 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 0) 512 256 = 6485824654796929163000174007 :=
  phaseBlock_append receipt_0_11_2359_0_part4 receipt_0_11_2359_0_part5 rfl rfl rfl
private theorem receipt_0_11_2359_0_join4 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 0) 896 166 = 758581255200422432775920333 :=
  phaseBlock_append receipt_0_11_2359_0_part7 receipt_0_11_2359_0_part8 rfl rfl rfl
private theorem receipt_0_11_2359_0_join5 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 0) 768 294 = 2431855928887864002976436712 :=
  phaseBlock_append receipt_0_11_2359_0_part6 receipt_0_11_2359_0_join4 rfl rfl rfl
private theorem receipt_0_11_2359_0_join6 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 0) 512 550 = 8917680583684793165976610719 :=
  phaseBlock_append receipt_0_11_2359_0_join3 receipt_0_11_2359_0_join5 rfl rfl rfl
private theorem receipt_0_11_2359_0_join7 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 0) 0 1062 = 36514307164940357924979385503 :=
  phaseBlock_append receipt_0_11_2359_0_join2 receipt_0_11_2359_0_join6 rfl rfl rfl

private theorem receipt_0_11_2359_0 : fastPhase (bank 0 11).shape 179808 2379 32 1 0 1 0 = 36514307164940357924979385503 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_0_11_2359_0_join7

private theorem receipt_0_11_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 1) 0 128 = 8909701148088475971875054400 := by decide +kernel
private theorem receipt_0_11_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 1) 128 128 = 7509349326622121573923996480 := by decide +kernel
private theorem receipt_0_11_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 1) 256 128 = 6189370887881674622312932160 := by decide +kernel
private theorem receipt_0_11_2359_1_part3 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 1) 384 128 = 4947380450849479110206948160 := by decide +kernel
private theorem receipt_0_11_2359_1_part4 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 1) 512 128 = 3780999430775585236981097280 := by decide +kernel
private theorem receipt_0_11_2359_1_part5 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 1) 640 128 = 2687856327395259979096056208 := by decide +kernel
private theorem receipt_0_11_2359_1_part6 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 1) 768 128 = 1665588384714977169130463292 := by decide +kernel
private theorem receipt_0_11_2359_1_part7 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 1) 896 128 = 711833393589677591180184401 := by decide +kernel
private theorem receipt_0_11_2359_1_part8 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 1) 1024 38 = 37534187471965737896032365 := by decide +kernel
private theorem receipt_0_11_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 1) 0 256 = 16419050474710597545799050880 :=
  phaseBlock_append receipt_0_11_2359_1_part0 receipt_0_11_2359_1_part1 rfl rfl rfl
private theorem receipt_0_11_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 1) 256 256 = 11136751338731153732519880320 :=
  phaseBlock_append receipt_0_11_2359_1_part2 receipt_0_11_2359_1_part3 rfl rfl rfl
private theorem receipt_0_11_2359_1_join2 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 1) 0 512 = 27555801813441751278318931200 :=
  phaseBlock_append receipt_0_11_2359_1_join0 receipt_0_11_2359_1_join1 rfl rfl rfl
private theorem receipt_0_11_2359_1_join3 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 1) 512 256 = 6468855758170845216077153488 :=
  phaseBlock_append receipt_0_11_2359_1_part4 receipt_0_11_2359_1_part5 rfl rfl rfl
private theorem receipt_0_11_2359_1_join4 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 1) 896 166 = 749367581061643329076216766 :=
  phaseBlock_append receipt_0_11_2359_1_part7 receipt_0_11_2359_1_part8 rfl rfl rfl
private theorem receipt_0_11_2359_1_join5 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 1) 768 294 = 2414955965776620498206680058 :=
  phaseBlock_append receipt_0_11_2359_1_part6 receipt_0_11_2359_1_join4 rfl rfl rfl
private theorem receipt_0_11_2359_1_join6 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 1) 512 550 = 8883811723947465714283833546 :=
  phaseBlock_append receipt_0_11_2359_1_join3 receipt_0_11_2359_1_join5 rfl rfl rfl
private theorem receipt_0_11_2359_1_join7 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2379 32 1 0 1 1) 0 1062 = 36439613537389216992602764746 :=
  phaseBlock_append receipt_0_11_2359_1_join2 receipt_0_11_2359_1_join6 rfl rfl rfl

private theorem receipt_0_11_2359_1 : fastPhase (bank 0 11).shape 179808 2379 32 1 0 1 1 = 36439613537389216992602764746 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_0_11_2359_1_join7

private theorem receipt_0_11_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 0) 0 128 = 8920892997742107830720724000 := by decide +kernel
private theorem receipt_0_11_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 0) 128 128 = 7519907904337998679332940832 := by decide +kernel
private theorem receipt_0_11_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 0) 256 128 = 6199316502490871564979985440 := by decide +kernel
private theorem receipt_0_11_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 0) 384 128 = 4956733277136796342627650592 := by decide +kernel
private theorem receipt_0_11_2360_0_part4 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 0) 512 128 = 3789779509764510086137953312 := by decide +kernel
private theorem receipt_0_11_2360_0_part5 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 0) 640 128 = 2696083559850502896848572689 := by decide +kernel
private theorem receipt_0_11_2360_0_part6 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 0) 768 128 = 1673282545843247023455348917 := by decide +kernel
private theorem receipt_0_11_2360_0_part7 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 0) 896 128 = 719014172134190416034528912 := by decide +kernel
private theorem receipt_0_11_2360_0_part8 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 0) 1024 38 = 39570037798364504062678410 := by decide +kernel
private theorem receipt_0_11_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 0) 0 256 = 16440800902080106510053664832 :=
  phaseBlock_append receipt_0_11_2360_0_part0 receipt_0_11_2360_0_part1 rfl rfl rfl
private theorem receipt_0_11_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 0) 256 256 = 11156049779627667907607636032 :=
  phaseBlock_append receipt_0_11_2360_0_part2 receipt_0_11_2360_0_part3 rfl rfl rfl
private theorem receipt_0_11_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 0) 0 512 = 27596850681707774417661300864 :=
  phaseBlock_append receipt_0_11_2360_0_join0 receipt_0_11_2360_0_join1 rfl rfl rfl
private theorem receipt_0_11_2360_0_join3 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 0) 512 256 = 6485863069615012982986526001 :=
  phaseBlock_append receipt_0_11_2360_0_part4 receipt_0_11_2360_0_part5 rfl rfl rfl
private theorem receipt_0_11_2360_0_join4 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 0) 896 166 = 758584209932554920097207322 :=
  phaseBlock_append receipt_0_11_2360_0_part7 receipt_0_11_2360_0_part8 rfl rfl rfl
private theorem receipt_0_11_2360_0_join5 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 0) 768 294 = 2431866755775801943552556239 :=
  phaseBlock_append receipt_0_11_2360_0_part6 receipt_0_11_2360_0_join4 rfl rfl rfl
private theorem receipt_0_11_2360_0_join6 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 0) 512 550 = 8917729825390814926539082240 :=
  phaseBlock_append receipt_0_11_2360_0_join3 receipt_0_11_2360_0_join5 rfl rfl rfl
private theorem receipt_0_11_2360_0_join7 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 0) 0 1062 = 36514580507098589344200383104 :=
  phaseBlock_append receipt_0_11_2360_0_join2 receipt_0_11_2360_0_join6 rfl rfl rfl

private theorem receipt_0_11_2360_0 : fastPhase (bank 0 11).shape 179808 2380 32 1 0 1 0 = 36514580507098589344200383104 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_0_11_2360_0_join7

private theorem receipt_0_11_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 1) 0 128 = 8909780874152374926249023520 := by decide +kernel
private theorem receipt_0_11_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 1) 128 128 = 7509411718839699221368473632 := by decide +kernel
private theorem receipt_0_11_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 1) 256 128 = 6189418198565937209997670432 := by decide +kernel
private theorem receipt_0_11_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 1) 384 128 = 4947414850071147260877826080 := by decide +kernel
private theorem receipt_0_11_2360_1_part4 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 1) 512 128 = 3781023006599912501426821152 := by decide +kernel
private theorem receipt_0_11_2360_1_part5 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 1) 640 128 = 2687871078418740190957750364 := by decide +kernel
private theorem receipt_0_11_2360_1_part6 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 1) 768 128 = 1665596223684999102561065568 := by decide +kernel
private theorem receipt_0_11_2360_1_part7 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 1) 896 128 = 711836190277742564985273208 := by decide +kernel
private theorem receipt_0_11_2360_1_part8 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 1) 1024 38 = 37534312405127635174767912 := by decide +kernel
private theorem receipt_0_11_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 1) 0 256 = 16419192592992074147617497152 :=
  phaseBlock_append receipt_0_11_2360_1_part0 receipt_0_11_2360_1_part1 rfl rfl rfl
private theorem receipt_0_11_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 1) 256 256 = 11136833048637084470875496512 :=
  phaseBlock_append receipt_0_11_2360_1_part2 receipt_0_11_2360_1_part3 rfl rfl rfl
private theorem receipt_0_11_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 1) 0 512 = 27556025641629158618492993664 :=
  phaseBlock_append receipt_0_11_2360_1_join0 receipt_0_11_2360_1_join1 rfl rfl rfl
private theorem receipt_0_11_2360_1_join3 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 1) 512 256 = 6468894085018652692384571516 :=
  phaseBlock_append receipt_0_11_2360_1_part4 receipt_0_11_2360_1_part5 rfl rfl rfl
private theorem receipt_0_11_2360_1_join4 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 1) 896 166 = 749370502682870200160041120 :=
  phaseBlock_append receipt_0_11_2360_1_part7 receipt_0_11_2360_1_part8 rfl rfl rfl
private theorem receipt_0_11_2360_1_join5 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 1) 768 294 = 2414966726367869302721106688 :=
  phaseBlock_append receipt_0_11_2360_1_part6 receipt_0_11_2360_1_join4 rfl rfl rfl
private theorem receipt_0_11_2360_1_join6 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 1) 512 550 = 8883860811386521995105678204 :=
  phaseBlock_append receipt_0_11_2360_1_join3 receipt_0_11_2360_1_join5 rfl rfl rfl
private theorem receipt_0_11_2360_1_join7 :
    phaseBlock (fastLayer (bank 0 11).shape 179808 2380 32 1 0 1 1) 0 1062 = 36439886453015680613598671868 :=
  phaseBlock_append receipt_0_11_2360_1_join2 receipt_0_11_2360_1_join6 rfl rfl rfl

private theorem receipt_0_11_2360_1 : fastPhase (bank 0 11).shape 179808 2380 32 1 0 1 1 = 36439886453015680613598671868 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_0_11_2360_1_join7

theorem receipt_0_11 : Checked (bank 0 11) 32 0 1 := by
  refine checked_from_values (bank 0 11) 32 0 1
    (P3_7_1.checked (bank 0 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4866_1061)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_11_2359_0 receipt_0_11_2359_1 receipt_0_11_2360_0 receipt_0_11_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_11_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 0) 0 128 = 7958594644246832340672103488 := by decide +kernel
private theorem receipt_1_11_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 0) 128 128 = 6703094163279712975242748992 := by decide +kernel
private theorem receipt_1_11_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 0) 256 128 = 5521297281669163884703122496 := by decide +kernel
private theorem receipt_1_11_2359_0_part3 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 0) 384 128 = 4410900889901744389717402688 := by decide +kernel
private theorem receipt_1_11_2359_0_part4 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 0) 512 128 = 3369614980728577057580205120 := by decide +kernel
private theorem receipt_1_11_2359_0_part5 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 0) 640 128 = 2395162886405092040382069330 := by decide +kernel
private theorem receipt_1_11_2359_0_part6 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 0) 768 128 = 1485282740386214812468828189 := by decide +kernel
private theorem receipt_1_11_2359_0_part7 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 0) 896 128 = 637720167531811918150916562 := by decide +kernel
private theorem receipt_1_11_2359_0_part8 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 0) 1024 38 = 35075073748878141181902621 := by decide +kernel
private theorem receipt_1_11_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 0) 0 256 = 14661688807526545315914852480 :=
  phaseBlock_append receipt_1_11_2359_0_part0 receipt_1_11_2359_0_part1 rfl rfl rfl
private theorem receipt_1_11_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 0) 256 256 = 9932198171570908274420525184 :=
  phaseBlock_append receipt_1_11_2359_0_part2 receipt_1_11_2359_0_part3 rfl rfl rfl
private theorem receipt_1_11_2359_0_join2 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 0) 0 512 = 24593886979097453590335377664 :=
  phaseBlock_append receipt_1_11_2359_0_join0 receipt_1_11_2359_0_join1 rfl rfl rfl
private theorem receipt_1_11_2359_0_join3 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 0) 512 256 = 5764777867133669097962274450 :=
  phaseBlock_append receipt_1_11_2359_0_part4 receipt_1_11_2359_0_part5 rfl rfl rfl
private theorem receipt_1_11_2359_0_join4 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 0) 896 166 = 672795241280690059332819183 :=
  phaseBlock_append receipt_1_11_2359_0_part7 receipt_1_11_2359_0_part8 rfl rfl rfl
private theorem receipt_1_11_2359_0_join5 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 0) 768 294 = 2158077981666904871801647372 :=
  phaseBlock_append receipt_1_11_2359_0_part6 receipt_1_11_2359_0_join4 rfl rfl rfl
private theorem receipt_1_11_2359_0_join6 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 0) 512 550 = 7922855848800573969763921822 :=
  phaseBlock_append receipt_1_11_2359_0_join3 receipt_1_11_2359_0_join5 rfl rfl rfl
private theorem receipt_1_11_2359_0_join7 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 0) 0 1062 = 32516742827898027560099299486 :=
  phaseBlock_append receipt_1_11_2359_0_join2 receipt_1_11_2359_0_join6 rfl rfl rfl

private theorem receipt_1_11_2359_0 : fastPhase (bank 1 11).shape 179808 2379 32 1 0 2 0 = 32516742827898027560099299486 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_1_11_2359_0_join7

private theorem receipt_1_11_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 1) 0 128 = 7948628923875104889152360064 := by decide +kernel
private theorem receipt_1_11_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 1) 128 128 = 6693694030949117281389235840 := by decide +kernel
private theorem receipt_1_11_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 1) 256 128 = 5512445265717801209194696320 := by decide +kernel
private theorem receipt_1_11_2359_1_part3 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 1) 384 128 = 4402579618601329583482916480 := by decide +kernel
private theorem receipt_1_11_2359_1_part4 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 1) 512 128 = 3361807182091873943600516736 := by decide +kernel
private theorem receipt_1_11_2359_1_part5 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 1) 640 128 = 2387851387155224116473496137 := by decide +kernel
private theorem receipt_1_11_2359_1_part6 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 1) 768 128 = 1478450455938102070123351570 := by decide +kernel
private theorem receipt_1_11_2359_1_part7 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 1) 896 128 = 631350105387843935066377583 := by decide +kernel
private theorem receipt_1_11_2359_1_part8 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 1) 1024 38 = 33270449166010743617642821 := by decide +kernel
private theorem receipt_1_11_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 1) 0 256 = 14642322954824222170541595904 :=
  phaseBlock_append receipt_1_11_2359_1_part0 receipt_1_11_2359_1_part1 rfl rfl rfl
private theorem receipt_1_11_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 1) 256 256 = 9915024884319130792677612800 :=
  phaseBlock_append receipt_1_11_2359_1_part2 receipt_1_11_2359_1_part3 rfl rfl rfl
private theorem receipt_1_11_2359_1_join2 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 1) 0 512 = 24557347839143352963219208704 :=
  phaseBlock_append receipt_1_11_2359_1_join0 receipt_1_11_2359_1_join1 rfl rfl rfl
private theorem receipt_1_11_2359_1_join3 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 1) 512 256 = 5749658569247098060074012873 :=
  phaseBlock_append receipt_1_11_2359_1_part4 receipt_1_11_2359_1_part5 rfl rfl rfl
private theorem receipt_1_11_2359_1_join4 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 1) 896 166 = 664620554553854678684020404 :=
  phaseBlock_append receipt_1_11_2359_1_part7 receipt_1_11_2359_1_part8 rfl rfl rfl
private theorem receipt_1_11_2359_1_join5 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 1) 768 294 = 2143071010491956748807371974 :=
  phaseBlock_append receipt_1_11_2359_1_part6 receipt_1_11_2359_1_join4 rfl rfl rfl
private theorem receipt_1_11_2359_1_join6 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 1) 512 550 = 7892729579739054808881384847 :=
  phaseBlock_append receipt_1_11_2359_1_join3 receipt_1_11_2359_1_join5 rfl rfl rfl
private theorem receipt_1_11_2359_1_join7 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2379 32 1 0 2 1) 0 1062 = 32450077418882407772100593551 :=
  phaseBlock_append receipt_1_11_2359_1_join2 receipt_1_11_2359_1_join6 rfl rfl rfl

private theorem receipt_1_11_2359_1 : fastPhase (bank 1 11).shape 179808 2379 32 1 0 2 1 = 32450077418882407772100593551 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_1_11_2359_1_join7

private theorem receipt_1_11_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 0) 0 128 = 7958665843556304565155103008 := by decide +kernel
private theorem receipt_1_11_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 0) 128 128 = 6703149843518400662375092512 := by decide +kernel
private theorem receipt_1_11_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 0) 256 128 = 5521339475216622040746303776 := by decide +kernel
private theorem receipt_1_11_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 0) 384 128 = 4410931550880290047997931808 := by decide +kernel
private theorem receipt_1_11_2360_0_part4 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 0) 512 128 = 3369635985458032169452880160 := by decide +kernel
private theorem receipt_1_11_2360_0_part5 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 0) 640 128 = 2395176026996559541365425010 := by decide +kernel
private theorem receipt_1_11_2360_0_part6 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 0) 768 128 = 1485289728190480975081085768 := by decide +kernel
private theorem receipt_1_11_2360_0_part7 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 0) 896 128 = 637722671547774073984377720 := by decide +kernel
private theorem receipt_1_11_2360_0_part8 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 0) 1024 38 = 35075190367048647967551637 := by decide +kernel
private theorem receipt_1_11_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 0) 0 256 = 14661815687074705227530195520 :=
  phaseBlock_append receipt_1_11_2360_0_part0 receipt_1_11_2360_0_part1 rfl rfl rfl
private theorem receipt_1_11_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 0) 256 256 = 9932271026096912088744235584 :=
  phaseBlock_append receipt_1_11_2360_0_part2 receipt_1_11_2360_0_part3 rfl rfl rfl
private theorem receipt_1_11_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 0) 0 512 = 24594086713171617316274431104 :=
  phaseBlock_append receipt_1_11_2360_0_join0 receipt_1_11_2360_0_join1 rfl rfl rfl
private theorem receipt_1_11_2360_0_join3 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 0) 512 256 = 5764812012454591710818305170 :=
  phaseBlock_append receipt_1_11_2360_0_part4 receipt_1_11_2360_0_part5 rfl rfl rfl
private theorem receipt_1_11_2360_0_join4 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 0) 896 166 = 672797861914822721951929357 :=
  phaseBlock_append receipt_1_11_2360_0_part7 receipt_1_11_2360_0_part8 rfl rfl rfl
private theorem receipt_1_11_2360_0_join5 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 0) 768 294 = 2158087590105303697033015125 :=
  phaseBlock_append receipt_1_11_2360_0_part6 receipt_1_11_2360_0_join4 rfl rfl rfl
private theorem receipt_1_11_2360_0_join6 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 0) 512 550 = 7922899602559895407851320295 :=
  phaseBlock_append receipt_1_11_2360_0_join3 receipt_1_11_2360_0_join5 rfl rfl rfl
private theorem receipt_1_11_2360_0_join7 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 0) 0 1062 = 32516986315731512724125751399 :=
  phaseBlock_append receipt_1_11_2360_0_join2 receipt_1_11_2360_0_join6 rfl rfl rfl

private theorem receipt_1_11_2360_0 : fastPhase (bank 1 11).shape 179808 2380 32 1 0 2 0 = 32516986315731512724125751399 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_1_11_2360_0_join7

private theorem receipt_1_11_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 1) 0 128 = 7948700050392813782327765536 := by decide +kernel
private theorem receipt_1_11_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 1) 128 128 = 6693749646515710868091337248 := by decide +kernel
private theorem receipt_1_11_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 1) 256 128 = 5512487402340217581408537120 := by decide +kernel
private theorem receipt_1_11_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 1) 384 128 = 4402610230031763449741646368 := by decide +kernel
private theorem receipt_1_11_2360_1_part4 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 1) 512 128 = 3361828144282514297268431392 := by decide +kernel
private theorem receipt_1_11_2360_1_part5 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 1) 640 128 = 2387864491873458297451236405 := by decide +kernel
private theorem receipt_1_11_2360_1_part6 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 1) 768 128 = 1478457414239670534277199343 := by decide +kernel
private theorem receipt_1_11_2360_1_part7 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 1) 896 128 = 631352585901511040132977995 := by decide +kernel
private theorem receipt_1_11_2360_1_part8 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 1) 1024 38 = 33270559907364784956824796 := by decide +kernel
private theorem receipt_1_11_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 1) 0 256 = 14642449696908524650419102784 :=
  phaseBlock_append receipt_1_11_2360_1_part0 receipt_1_11_2360_1_part1 rfl rfl rfl
private theorem receipt_1_11_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 1) 256 256 = 9915097632371981031150183488 :=
  phaseBlock_append receipt_1_11_2360_1_part2 receipt_1_11_2360_1_part3 rfl rfl rfl
private theorem receipt_1_11_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 1) 0 512 = 24557547329280505681569286272 :=
  phaseBlock_append receipt_1_11_2360_1_join0 receipt_1_11_2360_1_join1 rfl rfl rfl
private theorem receipt_1_11_2360_1_join3 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 1) 512 256 = 5749692636155972594719667797 :=
  phaseBlock_append receipt_1_11_2360_1_part4 receipt_1_11_2360_1_part5 rfl rfl rfl
private theorem receipt_1_11_2360_1_join4 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 1) 896 166 = 664623145808875825089802791 :=
  phaseBlock_append receipt_1_11_2360_1_part7 receipt_1_11_2360_1_part8 rfl rfl rfl
private theorem receipt_1_11_2360_1_join5 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 1) 768 294 = 2143080560048546359367002134 :=
  phaseBlock_append receipt_1_11_2360_1_part6 receipt_1_11_2360_1_join4 rfl rfl rfl
private theorem receipt_1_11_2360_1_join6 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 1) 512 550 = 7892773196204518954086669931 :=
  phaseBlock_append receipt_1_11_2360_1_join3 receipt_1_11_2360_1_join5 rfl rfl rfl
private theorem receipt_1_11_2360_1_join7 :
    phaseBlock (fastLayer (bank 1 11).shape 179808 2380 32 1 0 2 1) 0 1062 = 32450320525485024635655956203 :=
  phaseBlock_append receipt_1_11_2360_1_join2 receipt_1_11_2360_1_join6 rfl rfl rfl

private theorem receipt_1_11_2360_1 : fastPhase (bank 1 11).shape 179808 2380 32 1 0 2 1 = 32450320525485024635655956203 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_1_11_2360_1_join7

theorem receipt_1_11 : Checked (bank 1 11) 32 0 2 := by
  refine checked_from_values (bank 1 11) 32 0 2
    (P3_7_1.checked (bank 1 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4866_1061)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_11_2359_0 receipt_1_11_2359_1 receipt_1_11_2360_0 receipt_1_11_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_11_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 0) 0 128 = 3997780984497934819510037376 := by decide +kernel
private theorem receipt_2_11_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 0) 128 128 = 3345994453703284793389804416 := by decide +kernel
private theorem receipt_2_11_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 0) 256 128 = 2738714717962826800111561600 := by decide +kernel
private theorem receipt_2_11_2359_0_part3 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 0) 384 128 = 2174092739320513674363628416 := by decide +kernel
private theorem receipt_2_11_2359_0_part4 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 0) 512 128 = 1650316861403371769718811520 := by decide +kernel
private theorem receipt_2_11_2359_0_part5 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 0) 640 128 = 1165612628717459631968537851 := by decide +kernel
private theorem receipt_2_11_2359_0_part6 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 0) 768 128 = 718243193763075712198118438 := by decide +kernel
private theorem receipt_2_11_2359_0_part7 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 0) 896 128 = 306505484679118265130208046 := by decide +kernel
private theorem receipt_2_11_2359_0_part8 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 0) 1024 38 = 16780618473218839852843932 := by decide +kernel
private theorem receipt_2_11_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 0) 0 256 = 7343775438201219612899841792 :=
  phaseBlock_append receipt_2_11_2359_0_part0 receipt_2_11_2359_0_part1 rfl rfl rfl
private theorem receipt_2_11_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 0) 256 256 = 4912807457283340474475190016 :=
  phaseBlock_append receipt_2_11_2359_0_part2 receipt_2_11_2359_0_part3 rfl rfl rfl
private theorem receipt_2_11_2359_0_join2 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 0) 0 512 = 12256582895484560087375031808 :=
  phaseBlock_append receipt_2_11_2359_0_join0 receipt_2_11_2359_0_join1 rfl rfl rfl
private theorem receipt_2_11_2359_0_join3 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 0) 512 256 = 2815929490120831401687349371 :=
  phaseBlock_append receipt_2_11_2359_0_part4 receipt_2_11_2359_0_part5 rfl rfl rfl
private theorem receipt_2_11_2359_0_join4 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 0) 896 166 = 323286103152337104983051978 :=
  phaseBlock_append receipt_2_11_2359_0_part7 receipt_2_11_2359_0_part8 rfl rfl rfl
private theorem receipt_2_11_2359_0_join5 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 0) 768 294 = 1041529296915412817181170416 :=
  phaseBlock_append receipt_2_11_2359_0_part6 receipt_2_11_2359_0_join4 rfl rfl rfl
private theorem receipt_2_11_2359_0_join6 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 0) 512 550 = 3857458787036244218868519787 :=
  phaseBlock_append receipt_2_11_2359_0_join3 receipt_2_11_2359_0_join5 rfl rfl rfl
private theorem receipt_2_11_2359_0_join7 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 0) 0 1062 = 16114041682520804306243551595 :=
  phaseBlock_append receipt_2_11_2359_0_join2 receipt_2_11_2359_0_join6 rfl rfl rfl

private theorem receipt_2_11_2359_0 : fastPhase (bank 2 11).shape 179808 2379 32 1 0 7 0 = 16114041682520804306243551595 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_2_11_2359_0_join7

private theorem receipt_2_11_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 1) 0 128 = 3992579125530673883087720640 := by decide +kernel
private theorem receipt_2_11_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 1) 128 128 = 3341137569293987732327264448 := by decide +kernel
private theorem receipt_2_11_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 1) 256 128 = 2734188622162776436228722880 := by decide +kernel
private theorem receipt_2_11_2359_1_part3 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 1) 384 128 = 2169883532493137258700517568 := by decide +kernel
private theorem receipt_2_11_2359_1_part4 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 1) 512 128 = 1646410927865324409610162368 := by decide +kernel
private theorem receipt_2_11_2359_1_part5 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 1) 640 128 = 1161996633966417375657253701 := by decide +kernel
private theorem receipt_2_11_2359_1_part6 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 1) 768 128 = 714904077338801262347093188 := by decide +kernel
private theorem receipt_2_11_2359_1_part7 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 1) 896 128 = 303430459789863599012778936 := by decide +kernel
private theorem receipt_2_11_2359_1_part8 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 1) 1024 38 = 15916708201084151178244416 := by decide +kernel
private theorem receipt_2_11_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 1) 0 256 = 7333716694824661615414985088 :=
  phaseBlock_append receipt_2_11_2359_1_part0 receipt_2_11_2359_1_part1 rfl rfl rfl
private theorem receipt_2_11_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 1) 256 256 = 4904072154655913694929240448 :=
  phaseBlock_append receipt_2_11_2359_1_part2 receipt_2_11_2359_1_part3 rfl rfl rfl
private theorem receipt_2_11_2359_1_join2 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 1) 0 512 = 12237788849480575310344225536 :=
  phaseBlock_append receipt_2_11_2359_1_join0 receipt_2_11_2359_1_join1 rfl rfl rfl
private theorem receipt_2_11_2359_1_join3 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 1) 512 256 = 2808407561831741785267416069 :=
  phaseBlock_append receipt_2_11_2359_1_part4 receipt_2_11_2359_1_part5 rfl rfl rfl
private theorem receipt_2_11_2359_1_join4 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 1) 896 166 = 319347167990947750191023352 :=
  phaseBlock_append receipt_2_11_2359_1_part7 receipt_2_11_2359_1_part8 rfl rfl rfl
private theorem receipt_2_11_2359_1_join5 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 1) 768 294 = 1034251245329749012538116540 :=
  phaseBlock_append receipt_2_11_2359_1_part6 receipt_2_11_2359_1_join4 rfl rfl rfl
private theorem receipt_2_11_2359_1_join6 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 1) 512 550 = 3842658807161490797805532609 :=
  phaseBlock_append receipt_2_11_2359_1_join3 receipt_2_11_2359_1_join5 rfl rfl rfl
private theorem receipt_2_11_2359_1_join7 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2379 32 1 0 7 1) 0 1062 = 16080447656642066108149758145 :=
  phaseBlock_append receipt_2_11_2359_1_join2 receipt_2_11_2359_1_join6 rfl rfl rfl

private theorem receipt_2_11_2359_1 : fastPhase (bank 2 11).shape 179808 2379 32 1 0 7 1 = 16080447656642066108149758145 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_2_11_2359_1_join7

private theorem receipt_2_11_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 0) 0 128 = 3997816750825273901376306816 := by decide +kernel
private theorem receipt_2_11_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 0) 128 128 = 3346022248846975030696631936 := by decide +kernel
private theorem receipt_2_11_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 0) 256 128 = 2738735648099582631431716480 := by decide +kernel
private theorem receipt_2_11_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 0) 384 128 = 2174107852649903020541091456 := by decide +kernel
private theorem receipt_2_11_2360_0_part4 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 0) 512 128 = 1650327149412396826926710400 := by decide +kernel
private theorem receipt_2_11_2360_0_part5 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 0) 640 128 = 1165619024102608843134412919 := by decide +kernel
private theorem receipt_2_11_2360_0_part6 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 0) 768 128 = 718246573184933278670797017 := by decide +kernel
private theorem receipt_2_11_2360_0_part7 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 0) 896 128 = 306506688297782145788925424 := by decide +kernel
private theorem receipt_2_11_2360_0_part8 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 0) 1024 38 = 16780674266160498718664043 := by decide +kernel
private theorem receipt_2_11_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 0) 0 256 = 7343838999672248932072938752 :=
  phaseBlock_append receipt_2_11_2360_0_part0 receipt_2_11_2360_0_part1 rfl rfl rfl
private theorem receipt_2_11_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 0) 256 256 = 4912843500749485651972807936 :=
  phaseBlock_append receipt_2_11_2360_0_part2 receipt_2_11_2360_0_part3 rfl rfl rfl
private theorem receipt_2_11_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 0) 0 512 = 12256682500421734584045746688 :=
  phaseBlock_append receipt_2_11_2360_0_join0 receipt_2_11_2360_0_join1 rfl rfl rfl
private theorem receipt_2_11_2360_0_join3 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 0) 512 256 = 2815946173515005670061123319 :=
  phaseBlock_append receipt_2_11_2360_0_part4 receipt_2_11_2360_0_part5 rfl rfl rfl
private theorem receipt_2_11_2360_0_join4 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 0) 896 166 = 323287362563942644507589467 :=
  phaseBlock_append receipt_2_11_2360_0_part7 receipt_2_11_2360_0_part8 rfl rfl rfl
private theorem receipt_2_11_2360_0_join5 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 0) 768 294 = 1041533935748875923178386484 :=
  phaseBlock_append receipt_2_11_2360_0_part6 receipt_2_11_2360_0_join4 rfl rfl rfl
private theorem receipt_2_11_2360_0_join6 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 0) 512 550 = 3857480109263881593239509803 :=
  phaseBlock_append receipt_2_11_2360_0_join3 receipt_2_11_2360_0_join5 rfl rfl rfl
private theorem receipt_2_11_2360_0_join7 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 0) 0 1062 = 16114162609685616177285256491 :=
  phaseBlock_append receipt_2_11_2360_0_join2 receipt_2_11_2360_0_join6 rfl rfl rfl

private theorem receipt_2_11_2360_0 : fastPhase (bank 2 11).shape 179808 2380 32 1 0 7 0 = 16114162609685616177285256491 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_2_11_2360_0_join7

private theorem receipt_2_11_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 1) 0 128 = 3992614853538972020065265280 := by decide +kernel
private theorem receipt_2_11_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 1) 128 128 = 3341165330786033478391694976 := by decide +kernel
private theorem receipt_2_11_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 1) 256 128 = 2734209523027788971588101760 := by decide +kernel
private theorem receipt_2_11_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 1) 384 128 = 2169898620650199422198302336 := by decide +kernel
private theorem receipt_2_11_2360_1_part4 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 1) 512 128 = 1646421194527899513950299776 := by decide +kernel
private theorem receipt_2_11_2360_1_part5 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 1) 640 128 = 1162003011574913477717784333 := by decide +kernel
private theorem receipt_2_11_2360_1_part6 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 1) 768 128 = 714907442326796228560714235 := by decide +kernel
private theorem receipt_2_11_2360_1_part7 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 1) 896 128 = 303431652058479784802844597 := by decide +kernel
private theorem receipt_2_11_2360_1_part8 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 1) 1024 38 = 15916761180588555221495988 := by decide +kernel
private theorem receipt_2_11_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 1) 0 256 = 7333780184325005498456960256 :=
  phaseBlock_append receipt_2_11_2360_1_part0 receipt_2_11_2360_1_part1 rfl rfl rfl
private theorem receipt_2_11_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 1) 256 256 = 4904108143677988393786404096 :=
  phaseBlock_append receipt_2_11_2360_1_part2 receipt_2_11_2360_1_part3 rfl rfl rfl
private theorem receipt_2_11_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 1) 0 512 = 12237888328002993892243364352 :=
  phaseBlock_append receipt_2_11_2360_1_join0 receipt_2_11_2360_1_join1 rfl rfl rfl
private theorem receipt_2_11_2360_1_join3 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 1) 512 256 = 2808424206102812991668084109 :=
  phaseBlock_append receipt_2_11_2360_1_part4 receipt_2_11_2360_1_part5 rfl rfl rfl
private theorem receipt_2_11_2360_1_join4 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 1) 896 166 = 319348413239068340024340585 :=
  phaseBlock_append receipt_2_11_2360_1_part7 receipt_2_11_2360_1_part8 rfl rfl rfl
private theorem receipt_2_11_2360_1_join5 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 1) 768 294 = 1034255855565864568585054820 :=
  phaseBlock_append receipt_2_11_2360_1_part6 receipt_2_11_2360_1_join4 rfl rfl rfl
private theorem receipt_2_11_2360_1_join6 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 1) 512 550 = 3842680061668677560253138929 :=
  phaseBlock_append receipt_2_11_2360_1_join3 receipt_2_11_2360_1_join5 rfl rfl rfl
private theorem receipt_2_11_2360_1_join7 :
    phaseBlock (fastLayer (bank 2 11).shape 179808 2380 32 1 0 7 1) 0 1062 = 16080568389671671452496503281 :=
  phaseBlock_append receipt_2_11_2360_1_join2 receipt_2_11_2360_1_join6 rfl rfl rfl

private theorem receipt_2_11_2360_1 : fastPhase (bank 2 11).shape 179808 2380 32 1 0 7 1 = 16080568389671671452496503281 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_2_11_2360_1_join7

theorem receipt_2_11 : Checked (bank 2 11) 32 0 7 := by
  refine checked_from_values (bank 2 11) 32 0 7
    (P3_7_1.checked (bank 2 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4866_1061)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_11_2359_0 receipt_2_11_2359_1 receipt_2_11_2360_0 receipt_2_11_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_11_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 0) 0 128 = 401068059332411516038805568 := by decide +kernel
private theorem receipt_3_11_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 0) 128 128 = 317193399107613507461953600 := by decide +kernel
private theorem receipt_3_11_2359_0_part2 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 0) 256 128 = 239244990843065687655675968 := by decide +kernel
private theorem receipt_3_11_2359_0_part3 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 0) 384 128 = 167496635883070269254875200 := by decide +kernel
private theorem receipt_3_11_2359_0_part4 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 0) 512 128 = 102219152218274485400827968 := by decide +kernel
private theorem receipt_3_11_2359_0_part5 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 0) 640 128 = 43680383922427047221704768 := by decide +kernel
private theorem receipt_3_11_2359_0_part6 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 0) 768 42 = 2754103758366598871263394 := by decide +kernel
private theorem receipt_3_11_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 0) 128 256 = 556438389950679195117629568 :=
  phaseBlock_append receipt_3_11_2359_0_part1 receipt_3_11_2359_0_part2 rfl rfl rfl
private theorem receipt_3_11_2359_0_join1 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 0) 0 384 = 957506449283090711156435136 :=
  phaseBlock_append receipt_3_11_2359_0_part0 receipt_3_11_2359_0_join0 rfl rfl rfl
private theorem receipt_3_11_2359_0_join2 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 0) 384 256 = 269715788101344754655703168 :=
  phaseBlock_append receipt_3_11_2359_0_part3 receipt_3_11_2359_0_part4 rfl rfl rfl
private theorem receipt_3_11_2359_0_join3 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 0) 640 170 = 46434487680793646092968162 :=
  phaseBlock_append receipt_3_11_2359_0_part5 receipt_3_11_2359_0_part6 rfl rfl rfl
private theorem receipt_3_11_2359_0_join4 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 0) 384 426 = 316150275782138400748671330 :=
  phaseBlock_append receipt_3_11_2359_0_join2 receipt_3_11_2359_0_join3 rfl rfl rfl
private theorem receipt_3_11_2359_0_join5 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 0) 0 810 = 1273656725065229111905106466 :=
  phaseBlock_append receipt_3_11_2359_0_join1 receipt_3_11_2359_0_join4 rfl rfl rfl

private theorem receipt_3_11_2359_0 : fastPhase (bank 3 11).shape 179808 2379 32 1 1 1 0 = 1273656725065229111905106466 :=
  phase_of_block (n := 810) (by decide +kernel) receipt_3_11_2359_0_join5

private theorem receipt_3_11_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 1) 0 128 = 400398966613687059276115072 := by decide +kernel
private theorem receipt_3_11_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 1) 128 128 = 316567675238310834298473600 := by decide +kernel
private theorem receipt_3_11_2359_1_part2 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 1) 256 128 = 238664959605649206219992192 := by decide +kernel
private theorem receipt_3_11_2359_1_part3 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 1) 384 128 = 166964596496584556533648512 := by decide +kernel
private theorem receipt_3_11_2359_1_part4 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 1) 512 128 = 101737379415011652495649920 := by decide +kernel
private theorem receipt_3_11_2359_1_part5 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 1) 640 128 = 43251128024594104605953152 := by decide +kernel
private theorem receipt_3_11_2359_1_part6 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 1) 768 42 = 2625074460141162008281736 := by decide +kernel
private theorem receipt_3_11_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 1) 128 256 = 555232634843960040518465792 :=
  phaseBlock_append receipt_3_11_2359_1_part1 receipt_3_11_2359_1_part2 rfl rfl rfl
private theorem receipt_3_11_2359_1_join1 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 1) 0 384 = 955631601457647099794580864 :=
  phaseBlock_append receipt_3_11_2359_1_part0 receipt_3_11_2359_1_join0 rfl rfl rfl
private theorem receipt_3_11_2359_1_join2 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 1) 384 256 = 268701975911596209029298432 :=
  phaseBlock_append receipt_3_11_2359_1_part3 receipt_3_11_2359_1_part4 rfl rfl rfl
private theorem receipt_3_11_2359_1_join3 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 1) 640 170 = 45876202484735266614234888 :=
  phaseBlock_append receipt_3_11_2359_1_part5 receipt_3_11_2359_1_part6 rfl rfl rfl
private theorem receipt_3_11_2359_1_join4 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 1) 384 426 = 314578178396331475643533320 :=
  phaseBlock_append receipt_3_11_2359_1_join2 receipt_3_11_2359_1_join3 rfl rfl rfl
private theorem receipt_3_11_2359_1_join5 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2379 32 1 1 1 1) 0 810 = 1270209779853978575438114184 :=
  phaseBlock_append receipt_3_11_2359_1_join1 receipt_3_11_2359_1_join4 rfl rfl rfl

private theorem receipt_3_11_2359_1 : fastPhase (bank 3 11).shape 179808 2379 32 1 1 1 1 = 1270209779853978575438114184 :=
  phase_of_block (n := 810) (by decide +kernel) receipt_3_11_2359_1_join5

private theorem receipt_3_11_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 0) 0 128 = 401071485683145171705489312 := by decide +kernel
private theorem receipt_3_11_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 0) 128 128 = 317195675433366810079410080 := by decide +kernel
private theorem receipt_3_11_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 0) 256 128 = 239246390098478339374778272 := by decide +kernel
private theorem receipt_3_11_2360_0_part3 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 0) 384 128 = 167497399690717016324560800 := by decide +kernel
private theorem receipt_3_11_2360_0_part4 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 0) 512 128 = 102219491160767012200163232 := by decide +kernel
private theorem receipt_3_11_2360_0_part5 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 0) 640 128 = 43680477833636260989728672 := by decide +kernel
private theorem receipt_3_11_2360_0_part6 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 0) 768 42 = 2754107300188092535505266 := by decide +kernel
private theorem receipt_3_11_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 0) 128 256 = 556442065531845149454188352 :=
  phaseBlock_append receipt_3_11_2360_0_part1 receipt_3_11_2360_0_part2 rfl rfl rfl
private theorem receipt_3_11_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 0) 0 384 = 957513551214990321159677664 :=
  phaseBlock_append receipt_3_11_2360_0_part0 receipt_3_11_2360_0_join0 rfl rfl rfl
private theorem receipt_3_11_2360_0_join2 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 0) 384 256 = 269716890851484028524724032 :=
  phaseBlock_append receipt_3_11_2360_0_part3 receipt_3_11_2360_0_part4 rfl rfl rfl
private theorem receipt_3_11_2360_0_join3 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 0) 640 170 = 46434585133824353525233938 :=
  phaseBlock_append receipt_3_11_2360_0_part5 receipt_3_11_2360_0_part6 rfl rfl rfl
private theorem receipt_3_11_2360_0_join4 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 0) 384 426 = 316151475985308382049957970 :=
  phaseBlock_append receipt_3_11_2360_0_join2 receipt_3_11_2360_0_join3 rfl rfl rfl
private theorem receipt_3_11_2360_0_join5 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 0) 0 810 = 1273665027200298703209635634 :=
  phaseBlock_append receipt_3_11_2360_0_join1 receipt_3_11_2360_0_join4 rfl rfl rfl

private theorem receipt_3_11_2360_0 : fastPhase (bank 3 11).shape 179808 2380 32 1 1 1 0 = 1273665027200298703209635634 :=
  phase_of_block (n := 810) (by decide +kernel) receipt_3_11_2360_0_join5

private theorem receipt_3_11_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 1) 0 128 = 400402386386851923246831392 := by decide +kernel
private theorem receipt_3_11_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 1) 128 128 = 316569946458831118691968800 := by decide +kernel
private theorem receipt_3_11_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 1) 256 128 = 238666355055019602823182112 := by decide +kernel
private theorem receipt_3_11_2360_1_part3 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 1) 384 128 = 166965357626007690179987232 := by decide +kernel
private theorem receipt_3_11_2360_1_part4 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 1) 512 128 = 101737716637494340100101920 := by decide +kernel
private theorem receipt_3_11_2360_1_part5 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 1) 640 128 = 43251221006164004897744672 := by decide +kernel
private theorem receipt_3_11_2360_1_part6 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 1) 768 42 = 2625077841008483665806946 := by decide +kernel
private theorem receipt_3_11_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 1) 128 256 = 555236301513850721515150912 :=
  phaseBlock_append receipt_3_11_2360_1_part1 receipt_3_11_2360_1_part2 rfl rfl rfl
private theorem receipt_3_11_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 1) 0 384 = 955638687900702644761982304 :=
  phaseBlock_append receipt_3_11_2360_1_part0 receipt_3_11_2360_1_join0 rfl rfl rfl
private theorem receipt_3_11_2360_1_join2 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 1) 384 256 = 268703074263502030280089152 :=
  phaseBlock_append receipt_3_11_2360_1_part3 receipt_3_11_2360_1_part4 rfl rfl rfl
private theorem receipt_3_11_2360_1_join3 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 1) 640 170 = 45876298847172488563551618 :=
  phaseBlock_append receipt_3_11_2360_1_part5 receipt_3_11_2360_1_part6 rfl rfl rfl
private theorem receipt_3_11_2360_1_join4 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 1) 384 426 = 314579373110674518843640770 :=
  phaseBlock_append receipt_3_11_2360_1_join2 receipt_3_11_2360_1_join3 rfl rfl rfl
private theorem receipt_3_11_2360_1_join5 :
    phaseBlock (fastLayer (bank 3 11).shape 179808 2380 32 1 1 1 1) 0 810 = 1270218061011377163605623074 :=
  phaseBlock_append receipt_3_11_2360_1_join1 receipt_3_11_2360_1_join4 rfl rfl rfl

private theorem receipt_3_11_2360_1 : fastPhase (bank 3 11).shape 179808 2380 32 1 1 1 1 = 1270218061011377163605623074 :=
  phase_of_block (n := 810) (by decide +kernel) receipt_3_11_2360_1_join5

theorem receipt_3_11 : Checked (bank 3 11) 32 1 1 := by
  refine checked_from_values (bank 3 11) 32 1 1
    (P3_7_1.checked (bank 3 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3870_809)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_11_2359_0 receipt_3_11_2359_1 receipt_3_11_2360_0 receipt_3_11_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_12_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 0) 0 128 = 5659957310220879788860172037 := by decide +kernel
private theorem receipt_0_12_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 0) 128 128 = 4604246101737199669764570934 := by decide +kernel
private theorem receipt_0_12_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 0) 256 128 = 3618154573975979749608927876 := by decide +kernel
private theorem receipt_0_12_2359_0_part3 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 0) 384 128 = 2699303563920429442081983839 := by decide +kernel
private theorem receipt_0_12_2359_0_part4 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 0) 512 128 = 1845320489443596955709988781 := by decide +kernel
private theorem receipt_0_12_2359_0_part5 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 0) 640 128 = 1053839576250973658827225098 := by decide +kernel
private theorem receipt_0_12_2359_0_part6 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 0) 768 123 = 322913647423382751086464284 := by decide +kernel
private theorem receipt_0_12_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 0) 128 256 = 8222400675713179419373498810 :=
  phaseBlock_append receipt_0_12_2359_0_part1 receipt_0_12_2359_0_part2 rfl rfl rfl
private theorem receipt_0_12_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 0) 0 384 = 13882357985934059208233670847 :=
  phaseBlock_append receipt_0_12_2359_0_part0 receipt_0_12_2359_0_join0 rfl rfl rfl
private theorem receipt_0_12_2359_0_join2 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 0) 384 256 = 4544624053364026397791972620 :=
  phaseBlock_append receipt_0_12_2359_0_part3 receipt_0_12_2359_0_part4 rfl rfl rfl
private theorem receipt_0_12_2359_0_join3 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 0) 640 251 = 1376753223674356409913689382 :=
  phaseBlock_append receipt_0_12_2359_0_part5 receipt_0_12_2359_0_part6 rfl rfl rfl
private theorem receipt_0_12_2359_0_join4 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 0) 384 507 = 5921377277038382807705662002 :=
  phaseBlock_append receipt_0_12_2359_0_join2 receipt_0_12_2359_0_join3 rfl rfl rfl
private theorem receipt_0_12_2359_0_join5 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 0) 0 891 = 19803735262972442015939332849 :=
  phaseBlock_append receipt_0_12_2359_0_join1 receipt_0_12_2359_0_join4 rfl rfl rfl

private theorem receipt_0_12_2359_0 : fastPhase (bank 0 12).shape 179808 2379 31 1 0 1 0 = 19803735262972442015939332849 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_0_12_2359_0_join5

private theorem receipt_0_12_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 1) 0 128 = 5651543729728749456177014569 := by decide +kernel
private theorem receipt_0_12_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 1) 128 128 = 4596366852947506673736209155 := by decide +kernel
private theorem receipt_0_12_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 1) 256 128 = 3610791689304383285024624756 := by decide +kernel
private theorem receipt_0_12_2359_1_part3 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 1) 384 128 = 2692439127383567242321758885 := by decide +kernel
private theorem receipt_0_12_2359_1_part4 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 1) 512 128 = 1838936636876676079620678450 := by decide +kernel
private theorem receipt_0_12_2359_1_part5 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 1) 640 128 = 1047918495265434825055590229 := by decide +kernel
private theorem receipt_0_12_2359_1_part6 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 1) 768 123 = 317643351666146170290185525 := by decide +kernel
private theorem receipt_0_12_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 1) 128 256 = 8207158542251889958760833911 :=
  phaseBlock_append receipt_0_12_2359_1_part1 receipt_0_12_2359_1_part2 rfl rfl rfl
private theorem receipt_0_12_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 1) 0 384 = 13858702271980639414937848480 :=
  phaseBlock_append receipt_0_12_2359_1_part0 receipt_0_12_2359_1_join0 rfl rfl rfl
private theorem receipt_0_12_2359_1_join2 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 1) 384 256 = 4531375764260243321942437335 :=
  phaseBlock_append receipt_0_12_2359_1_part3 receipt_0_12_2359_1_part4 rfl rfl rfl
private theorem receipt_0_12_2359_1_join3 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 1) 640 251 = 1365561846931580995345775754 :=
  phaseBlock_append receipt_0_12_2359_1_part5 receipt_0_12_2359_1_part6 rfl rfl rfl
private theorem receipt_0_12_2359_1_join4 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 1) 384 507 = 5896937611191824317288213089 :=
  phaseBlock_append receipt_0_12_2359_1_join2 receipt_0_12_2359_1_join3 rfl rfl rfl
private theorem receipt_0_12_2359_1_join5 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2379 31 1 0 1 1) 0 891 = 19755639883172463732226061569 :=
  phaseBlock_append receipt_0_12_2359_1_join1 receipt_0_12_2359_1_join4 rfl rfl rfl

private theorem receipt_0_12_2359_1 : fastPhase (bank 0 12).shape 179808 2379 31 1 0 1 1 = 19755639883172463732226061569 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_0_12_2359_1_join5

private theorem receipt_0_12_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 0) 0 128 = 5660007649775940980602001604 := by decide +kernel
private theorem receipt_0_12_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 0) 128 128 = 4604283559547352772652859521 := by decide +kernel
private theorem receipt_0_12_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 0) 256 128 = 3618181141895659079749995090 := by decide +kernel
private theorem receipt_0_12_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 0) 384 128 = 2699321157652239450933169189 := by decide +kernel
private theorem receipt_0_12_2360_0_part4 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 0) 512 128 = 1845330935088580512682533405 := by decide +kernel
private theorem receipt_0_12_2360_0_part5 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 0) 640 128 = 1053844611390676649399416770 := by decide +kernel
private theorem receipt_0_12_2360_0_part6 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 0) 768 123 = 322914923232876342472241871 := by decide +kernel
private theorem receipt_0_12_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 0) 128 256 = 8222464701443011852402854611 :=
  phaseBlock_append receipt_0_12_2360_0_part1 receipt_0_12_2360_0_part2 rfl rfl rfl
private theorem receipt_0_12_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 0) 0 384 = 13882472351218952833004856215 :=
  phaseBlock_append receipt_0_12_2360_0_part0 receipt_0_12_2360_0_join0 rfl rfl rfl
private theorem receipt_0_12_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 0) 384 256 = 4544652092740819963615702594 :=
  phaseBlock_append receipt_0_12_2360_0_part3 receipt_0_12_2360_0_part4 rfl rfl rfl
private theorem receipt_0_12_2360_0_join3 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 0) 640 251 = 1376759534623552991871658641 :=
  phaseBlock_append receipt_0_12_2360_0_part5 receipt_0_12_2360_0_part6 rfl rfl rfl
private theorem receipt_0_12_2360_0_join4 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 0) 384 507 = 5921411627364372955487361235 :=
  phaseBlock_append receipt_0_12_2360_0_join2 receipt_0_12_2360_0_join3 rfl rfl rfl
private theorem receipt_0_12_2360_0_join5 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 0) 0 891 = 19803883978583325788492217450 :=
  phaseBlock_append receipt_0_12_2360_0_join1 receipt_0_12_2360_0_join4 rfl rfl rfl

private theorem receipt_0_12_2360_0 : fastPhase (bank 0 12).shape 179808 2380 31 1 0 1 0 = 19803883978583325788492217450 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_0_12_2360_0_join5

private theorem receipt_0_12_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 1) 0 128 = 5651594007784931074802650050 := by decide +kernel
private theorem receipt_0_12_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 1) 128 128 = 4596404257145579048139946148 := by decide +kernel
private theorem receipt_0_12_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 1) 256 128 = 3610818211107855215934863923 := by decide +kernel
private theorem receipt_0_12_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 1) 384 128 = 2692456682089946571439592403 := by decide +kernel
private theorem receipt_0_12_2360_1_part4 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 1) 512 128 = 1838947050184594093784102442 := by decide +kernel
private theorem receipt_0_12_2360_1_part5 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 1) 640 128 = 1047923504356200024560821184 := by decide +kernel
private theorem receipt_0_12_2360_1_part6 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 1) 768 123 = 317644607996930181767689174 := by decide +kernel
private theorem receipt_0_12_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 1) 128 256 = 8207222468253434264074810071 :=
  phaseBlock_append receipt_0_12_2360_1_part1 receipt_0_12_2360_1_part2 rfl rfl rfl
private theorem receipt_0_12_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 1) 0 384 = 13858816476038365338877460121 :=
  phaseBlock_append receipt_0_12_2360_1_part0 receipt_0_12_2360_1_join0 rfl rfl rfl
private theorem receipt_0_12_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 1) 384 256 = 4531403732274540665223694845 :=
  phaseBlock_append receipt_0_12_2360_1_part3 receipt_0_12_2360_1_part4 rfl rfl rfl
private theorem receipt_0_12_2360_1_join3 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 1) 640 251 = 1365568112353130206328510358 :=
  phaseBlock_append receipt_0_12_2360_1_part5 receipt_0_12_2360_1_part6 rfl rfl rfl
private theorem receipt_0_12_2360_1_join4 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 1) 384 507 = 5896971844627670871552205203 :=
  phaseBlock_append receipt_0_12_2360_1_join2 receipt_0_12_2360_1_join3 rfl rfl rfl
private theorem receipt_0_12_2360_1_join5 :
    phaseBlock (fastLayer (bank 0 12).shape 179808 2380 31 1 0 1 1) 0 891 = 19755788320666036210429665324 :=
  phaseBlock_append receipt_0_12_2360_1_join1 receipt_0_12_2360_1_join4 rfl rfl rfl

private theorem receipt_0_12_2360_1 : fastPhase (bank 0 12).shape 179808 2380 31 1 0 1 1 = 19755788320666036210429665324 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_0_12_2360_1_join5

theorem receipt_0_12 : Checked (bank 0 12) 31 0 1 := by
  refine checked_from_values (bank 0 12) 31 0 1
    (P3_7_1.checked (bank 0 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4255_890)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_12_2359_0 receipt_0_12_2359_1 receipt_0_12_2360_0 receipt_0_12_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_12_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 0) 0 128 = 5101513367699927026007756503 := by decide +kernel
private theorem receipt_1_12_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 0) 128 128 = 4146517340670698129709116527 := by decide +kernel
private theorem receipt_1_12_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 0) 256 128 = 3255750516954682095570892825 := by decide +kernel
private theorem receipt_1_12_2359_0_part3 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 0) 384 128 = 2426917798576916220146112467 := by decide +kernel
private theorem receipt_1_12_2359_0_part4 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 0) 512 128 = 1657737043522852143493700580 := by decide +kernel
private theorem receipt_1_12_2359_0_part5 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 0) 640 128 = 945939250816924353257890515 := by decide +kernel
private theorem receipt_1_12_2359_0_part6 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 0) 768 123 = 289637688859381003378040937 := by decide +kernel
private theorem receipt_1_12_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 0) 128 256 = 7402267857625380225280009352 :=
  phaseBlock_append receipt_1_12_2359_0_part1 receipt_1_12_2359_0_part2 rfl rfl rfl
private theorem receipt_1_12_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 0) 0 384 = 12503781225325307251287765855 :=
  phaseBlock_append receipt_1_12_2359_0_part0 receipt_1_12_2359_0_join0 rfl rfl rfl
private theorem receipt_1_12_2359_0_join2 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 0) 384 256 = 4084654842099768363639813047 :=
  phaseBlock_append receipt_1_12_2359_0_part3 receipt_1_12_2359_0_part4 rfl rfl rfl
private theorem receipt_1_12_2359_0_join3 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 0) 640 251 = 1235576939676305356635931452 :=
  phaseBlock_append receipt_1_12_2359_0_part5 receipt_1_12_2359_0_part6 rfl rfl rfl
private theorem receipt_1_12_2359_0_join4 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 0) 384 507 = 5320231781776073720275744499 :=
  phaseBlock_append receipt_1_12_2359_0_join2 receipt_1_12_2359_0_join3 rfl rfl rfl
private theorem receipt_1_12_2359_0_join5 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 0) 0 891 = 17824013007101380971563510354 :=
  phaseBlock_append receipt_1_12_2359_0_join1 receipt_1_12_2359_0_join4 rfl rfl rfl

private theorem receipt_1_12_2359_0 : fastPhase (bank 1 12).shape 179808 2379 31 1 0 2 0 = 17824013007101380971563510354 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_1_12_2359_0_join5

private theorem receipt_1_12_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 1) 0 128 = 5093896854170828427598363324 := by decide +kernel
private theorem receipt_1_12_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 1) 128 128 = 4139394524031829711406659844 := by decide +kernel
private theorem receipt_1_12_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 1) 256 128 = 3249104025207588889281407292 := by decide +kernel
private theorem receipt_1_12_2359_1_part3 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 1) 384 128 = 2420730359743914426605729789 := by decide +kernel
private theorem receipt_1_12_2359_1_part4 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 1) 512 128 = 1651991485695118582279204399 := by decide +kernel
private theorem receipt_1_12_2359_1_part5 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 1) 640 128 = 940618501966838010336105822 := by decide +kernel
private theorem receipt_1_12_2359_1_part6 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 1) 768 123 = 284909240193509485184134182 := by decide +kernel
private theorem receipt_1_12_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 1) 128 256 = 7388498549239418600688067136 :=
  phaseBlock_append receipt_1_12_2359_1_part1 receipt_1_12_2359_1_part2 rfl rfl rfl
private theorem receipt_1_12_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 1) 0 384 = 12482395403410247028286430460 :=
  phaseBlock_append receipt_1_12_2359_1_part0 receipt_1_12_2359_1_join0 rfl rfl rfl
private theorem receipt_1_12_2359_1_join2 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 1) 384 256 = 4072721845439033008884934188 :=
  phaseBlock_append receipt_1_12_2359_1_part3 receipt_1_12_2359_1_part4 rfl rfl rfl
private theorem receipt_1_12_2359_1_join3 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 1) 640 251 = 1225527742160347495520240004 :=
  phaseBlock_append receipt_1_12_2359_1_part5 receipt_1_12_2359_1_part6 rfl rfl rfl
private theorem receipt_1_12_2359_1_join4 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 1) 384 507 = 5298249587599380504405174192 :=
  phaseBlock_append receipt_1_12_2359_1_join2 receipt_1_12_2359_1_join3 rfl rfl rfl
private theorem receipt_1_12_2359_1_join5 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2379 31 1 0 2 1) 0 891 = 17780644991009627532691604652 :=
  phaseBlock_append receipt_1_12_2359_1_join1 receipt_1_12_2359_1_join4 rfl rfl rfl

private theorem receipt_1_12_2359_1 : fastPhase (bank 1 12).shape 179808 2379 31 1 0 2 1 = 17780644991009627532691604652 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_1_12_2359_1_join5

private theorem receipt_1_12_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 0) 0 128 = 5101558740725495925199334408 := by decide +kernel
private theorem receipt_1_12_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 0) 128 128 = 4146551074855321272974500432 := by decide +kernel
private theorem receipt_1_12_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 0) 256 128 = 3255774423943324203355849458 := by decide +kernel
private theorem receipt_1_12_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 0) 384 128 = 2426933617073656908943420063 := by decide +kernel
private theorem receipt_1_12_2360_0_part4 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 0) 512 128 = 1657746427431275421219467713 := by decide +kernel
private theorem receipt_1_12_2360_0_part5 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 0) 640 128 = 945943770478157141002105487 := by decide +kernel
private theorem receipt_1_12_2360_0_part6 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 0) 768 123 = 289638833209870893664819486 := by decide +kernel
private theorem receipt_1_12_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 0) 128 256 = 7402325498798645476330349890 :=
  phaseBlock_append receipt_1_12_2360_0_part1 receipt_1_12_2360_0_part2 rfl rfl rfl
private theorem receipt_1_12_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 0) 0 384 = 12503884239524141401529684298 :=
  phaseBlock_append receipt_1_12_2360_0_part0 receipt_1_12_2360_0_join0 rfl rfl rfl
private theorem receipt_1_12_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 0) 384 256 = 4084680044504932330162887776 :=
  phaseBlock_append receipt_1_12_2360_0_part3 receipt_1_12_2360_0_part4 rfl rfl rfl
private theorem receipt_1_12_2360_0_join3 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 0) 640 251 = 1235582603688028034666924973 :=
  phaseBlock_append receipt_1_12_2360_0_part5 receipt_1_12_2360_0_part6 rfl rfl rfl
private theorem receipt_1_12_2360_0_join4 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 0) 384 507 = 5320262648192960364829812749 :=
  phaseBlock_append receipt_1_12_2360_0_join2 receipt_1_12_2360_0_join3 rfl rfl rfl
private theorem receipt_1_12_2360_0_join5 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 0) 0 891 = 17824146887717101766359497047 :=
  phaseBlock_append receipt_1_12_2360_0_join1 receipt_1_12_2360_0_join4 rfl rfl rfl

private theorem receipt_1_12_2360_0 : fastPhase (bank 1 12).shape 179808 2380 31 1 0 2 0 = 17824146887717101766359497047 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_1_12_2360_0_join5

private theorem receipt_1_12_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 1) 0 128 = 5093942171470829866075565005 := by decide +kernel
private theorem receipt_1_12_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 1) 128 128 = 4139428209715092697128134070 := by decide +kernel
private theorem receipt_1_12_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 1) 256 128 = 3249127890543859068737585515 := by decide +kernel
private theorem receipt_1_12_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 1) 384 128 = 2420746143050618013685001786 := by decide +kernel
private theorem receipt_1_12_2360_1_part4 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 1) 512 128 = 1652000840493020639965087409 := by decide +kernel
private theorem receipt_1_12_2360_1_part5 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 1) 640 128 = 940622998217608620189815476 := by decide +kernel
private theorem receipt_1_12_2360_1_part6 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 1) 768 123 = 284910367067214757994622477 := by decide +kernel
private theorem receipt_1_12_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 1) 128 256 = 7388556100258951765865719585 :=
  phaseBlock_append receipt_1_12_2360_1_part1 receipt_1_12_2360_1_part2 rfl rfl rfl
private theorem receipt_1_12_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 1) 0 384 = 12482498271729781631941284590 :=
  phaseBlock_append receipt_1_12_2360_1_part0 receipt_1_12_2360_1_join0 rfl rfl rfl
private theorem receipt_1_12_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 1) 384 256 = 4072746983543638653650089195 :=
  phaseBlock_append receipt_1_12_2360_1_part3 receipt_1_12_2360_1_part4 rfl rfl rfl
private theorem receipt_1_12_2360_1_join3 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 1) 640 251 = 1225533365284823378184437953 :=
  phaseBlock_append receipt_1_12_2360_1_part5 receipt_1_12_2360_1_part6 rfl rfl rfl
private theorem receipt_1_12_2360_1_join4 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 1) 384 507 = 5298280348828462031834527148 :=
  phaseBlock_append receipt_1_12_2360_1_join2 receipt_1_12_2360_1_join3 rfl rfl rfl
private theorem receipt_1_12_2360_1_join5 :
    phaseBlock (fastLayer (bank 1 12).shape 179808 2380 31 1 0 2 1) 0 891 = 17780778620558243663775811738 :=
  phaseBlock_append receipt_1_12_2360_1_join1 receipt_1_12_2360_1_join4 rfl rfl rfl

private theorem receipt_1_12_2360_1 : fastPhase (bank 1 12).shape 179808 2380 31 1 0 2 1 = 17780778620558243663775811738 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_1_12_2360_1_join5

theorem receipt_1_12 : Checked (bank 1 12) 31 0 2 := by
  refine checked_from_values (bank 1 12) 31 0 2
    (P3_7_1.checked (bank 1 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4255_890)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_12_2359_0 receipt_1_12_2359_1 receipt_1_12_2360_0 receipt_1_12_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_12_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 0) 0 128 = 2784773386497738488009652768 := by decide +kernel
private theorem receipt_2_12_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 0) 128 128 = 2250126973765095553057622560 := by decide +kernel
private theorem receipt_2_12_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 0) 256 128 = 1756294384123619734971947552 := by decide +kernel
private theorem receipt_2_12_2359_0_part3 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 0) 384 128 = 1301415658170939678048856608 := by decide +kernel
private theorem receipt_2_12_2359_0_part4 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 0) 512 128 = 883668914952042604318384661 := by decide +kernel
private theorem receipt_2_12_2359_0_part5 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 0) 640 128 = 501270622810313331342863825 := by decide +kernel
private theorem receipt_2_12_2359_0_part6 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 0) 768 123 = 152666782086824977960398487 := by decide +kernel
private theorem receipt_2_12_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 0) 128 256 = 4006421357888715288029570112 :=
  phaseBlock_append receipt_2_12_2359_0_part1 receipt_2_12_2359_0_part2 rfl rfl rfl
private theorem receipt_2_12_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 0) 0 384 = 6791194744386453776039222880 :=
  phaseBlock_append receipt_2_12_2359_0_part0 receipt_2_12_2359_0_join0 rfl rfl rfl
private theorem receipt_2_12_2359_0_join2 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 0) 384 256 = 2185084573122982282367241269 :=
  phaseBlock_append receipt_2_12_2359_0_part3 receipt_2_12_2359_0_part4 rfl rfl rfl
private theorem receipt_2_12_2359_0_join3 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 0) 640 251 = 653937404897138309303262312 :=
  phaseBlock_append receipt_2_12_2359_0_part5 receipt_2_12_2359_0_part6 rfl rfl rfl
private theorem receipt_2_12_2359_0_join4 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 0) 384 507 = 2839021978020120591670503581 :=
  phaseBlock_append receipt_2_12_2359_0_join2 receipt_2_12_2359_0_join3 rfl rfl rfl
private theorem receipt_2_12_2359_0_join5 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 0) 0 891 = 9630216722406574367709726461 :=
  phaseBlock_append receipt_2_12_2359_0_join1 receipt_2_12_2359_0_join4 rfl rfl rfl

private theorem receipt_2_12_2359_0 : fastPhase (bank 2 12).shape 179808 2379 31 1 0 7 0 = 9630216722406574367709726461 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_2_12_2359_0_join5

private theorem receipt_2_12_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 1) 0 128 = 2780487318085142943008452000 := by decide +kernel
private theorem receipt_2_12_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 1) 128 128 = 2246157614562049992787066272 := by decide +kernel
private theorem receipt_2_12_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 1) 256 128 = 1752627472519462824829554080 := by decide +kernel
private theorem receipt_2_12_2359_1_part3 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 1) 384 128 = 1298037223998034067969514912 := by decide +kernel
private theorem receipt_2_12_2359_1_part4 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 1) 512 128 = 880565277063877060838962220 := by decide +kernel
private theorem receipt_2_12_2359_1_part5 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 1) 640 128 = 498428382930759094090677932 := by decide +kernel
private theorem receipt_2_12_2359_1_part6 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 1) 768 123 = 150169645971731187066310822 := by decide +kernel
private theorem receipt_2_12_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 1) 128 256 = 3998785087081512817616620352 :=
  phaseBlock_append receipt_2_12_2359_1_part1 receipt_2_12_2359_1_part2 rfl rfl rfl
private theorem receipt_2_12_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 1) 0 384 = 6779272405166655760625072352 :=
  phaseBlock_append receipt_2_12_2359_1_part0 receipt_2_12_2359_1_join0 rfl rfl rfl
private theorem receipt_2_12_2359_1_join2 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 1) 384 256 = 2178602501061911128808477132 :=
  phaseBlock_append receipt_2_12_2359_1_part3 receipt_2_12_2359_1_part4 rfl rfl rfl
private theorem receipt_2_12_2359_1_join3 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 1) 640 251 = 648598028902490281156988754 :=
  phaseBlock_append receipt_2_12_2359_1_part5 receipt_2_12_2359_1_part6 rfl rfl rfl
private theorem receipt_2_12_2359_1_join4 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 1) 384 507 = 2827200529964401409965465886 :=
  phaseBlock_append receipt_2_12_2359_1_join2 receipt_2_12_2359_1_join3 rfl rfl rfl
private theorem receipt_2_12_2359_1_join5 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2379 31 1 0 7 1) 0 891 = 9606472935131057170590538238 :=
  phaseBlock_append receipt_2_12_2359_1_join1 receipt_2_12_2359_1_join4 rfl rfl rfl

private theorem receipt_2_12_2359_1 : fastPhase (bank 2 12).shape 179808 2379 31 1 0 7 1 = 9606472935131057170590538238 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_2_12_2359_1_join5

private theorem receipt_2_12_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 0) 0 128 = 2784797919634015383931238112 := by decide +kernel
private theorem receipt_2_12_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 0) 128 128 = 2250145136062367745794959072 := by decide +kernel
private theorem receipt_2_12_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 0) 256 128 = 1756307206366367610992006880 := by decide +kernel
private theorem receipt_2_12_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 0) 384 128 = 1301424112020454584313005792 := by decide +kernel
private theorem receipt_2_12_2360_0_part4 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 0) 512 128 = 883673913533833966290758368 := by decide +kernel
private theorem receipt_2_12_2360_0_part5 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 0) 640 128 = 501273018086098595530927832 := by decide +kernel
private theorem receipt_2_12_2360_0_part6 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 0) 768 123 = 152667385314978854199969376 := by decide +kernel
private theorem receipt_2_12_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 0) 128 256 = 4006452342428735356786965952 :=
  phaseBlock_append receipt_2_12_2360_0_part1 receipt_2_12_2360_0_part2 rfl rfl rfl
private theorem receipt_2_12_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 0) 0 384 = 6791250262062750740718204064 :=
  phaseBlock_append receipt_2_12_2360_0_part0 receipt_2_12_2360_0_join0 rfl rfl rfl
private theorem receipt_2_12_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 0) 384 256 = 2185098025554288550603764160 :=
  phaseBlock_append receipt_2_12_2360_0_part3 receipt_2_12_2360_0_part4 rfl rfl rfl
private theorem receipt_2_12_2360_0_join3 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 0) 640 251 = 653940403401077449730897208 :=
  phaseBlock_append receipt_2_12_2360_0_part5 receipt_2_12_2360_0_part6 rfl rfl rfl
private theorem receipt_2_12_2360_0_join4 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 0) 384 507 = 2839038428955366000334661368 :=
  phaseBlock_append receipt_2_12_2360_0_join2 receipt_2_12_2360_0_join3 rfl rfl rfl
private theorem receipt_2_12_2360_0_join5 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 0) 0 891 = 9630288691018116741052865432 :=
  phaseBlock_append receipt_2_12_2360_0_join1 receipt_2_12_2360_0_join4 rfl rfl rfl

private theorem receipt_2_12_2360_0 : fastPhase (bank 2 12).shape 179808 2380 31 1 0 7 0 = 9630288691018116741052865432 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_2_12_2360_0_join5

private theorem receipt_2_12_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 1) 0 128 = 2780511819956489375348225760 := by decide +kernel
private theorem receipt_2_12_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 1) 128 128 = 2246175749905094392565974752 := by decide +kernel
private theorem receipt_2_12_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 1) 256 128 = 1752640271827293571744175840 := by decide +kernel
private theorem receipt_2_12_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 1) 384 128 = 1298045658647710942300825312 := by decide +kernel
private theorem receipt_2_12_2360_1_part4 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 1) 512 128 = 880570259906484531966291934 := by decide +kernel
private theorem receipt_2_12_2360_1_part5 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 1) 640 128 = 498430765691175327990254786 := by decide +kernel
private theorem receipt_2_12_2360_1_part6 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 1) 768 123 = 150170239967519829358879102 := by decide +kernel
private theorem receipt_2_12_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 1) 128 256 = 3998816021732387964310150592 :=
  phaseBlock_append receipt_2_12_2360_1_part1 receipt_2_12_2360_1_part2 rfl rfl rfl
private theorem receipt_2_12_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 1) 0 384 = 6779327841688877339658376352 :=
  phaseBlock_append receipt_2_12_2360_1_part0 receipt_2_12_2360_1_join0 rfl rfl rfl
private theorem receipt_2_12_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 1) 384 256 = 2178615918554195474267117246 :=
  phaseBlock_append receipt_2_12_2360_1_part3 receipt_2_12_2360_1_part4 rfl rfl rfl
private theorem receipt_2_12_2360_1_join3 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 1) 640 251 = 648601005658695157349133888 :=
  phaseBlock_append receipt_2_12_2360_1_part5 receipt_2_12_2360_1_part6 rfl rfl rfl
private theorem receipt_2_12_2360_1_join4 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 1) 384 507 = 2827216924212890631616251134 :=
  phaseBlock_append receipt_2_12_2360_1_join2 receipt_2_12_2360_1_join3 rfl rfl rfl
private theorem receipt_2_12_2360_1_join5 :
    phaseBlock (fastLayer (bank 2 12).shape 179808 2380 31 1 0 7 1) 0 891 = 9606544765901767971274627486 :=
  phaseBlock_append receipt_2_12_2360_1_join1 receipt_2_12_2360_1_join4 rfl rfl rfl

private theorem receipt_2_12_2360_1 : fastPhase (bank 2 12).shape 179808 2380 31 1 0 7 1 = 9606544765901767971274627486 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_2_12_2360_1_join5

theorem receipt_2_12 : Checked (bank 2 12) 31 0 7 := by
  refine checked_from_values (bank 2 12) 31 0 7
    (P3_7_1.checked (bank 2 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4235_890)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_12_2359_0 receipt_2_12_2359_1 receipt_2_12_2360_0 receipt_2_12_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_12_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 0) 0 128 = 486100254468057456194744896 := by decide +kernel
private theorem receipt_3_12_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 0) 128 128 = 396430131753278139298378304 := by decide +kernel
private theorem receipt_3_12_2359_0_part2 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 0) 256 128 = 312500569506316626322453056 := by decide +kernel
private theorem receipt_3_12_2359_0_part3 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 0) 384 128 = 234544743934381024523809344 := by decide +kernel
private theorem receipt_3_12_2359_0_part4 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 0) 512 128 = 162793057287187315891892800 := by decide +kernel
private theorem receipt_3_12_2359_0_part5 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 0) 640 128 = 97473147293715814629274176 := by decide +kernel
private theorem receipt_3_12_2359_0_part6 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 0) 768 128 = 38809896598967624632169024 := by decide +kernel
private theorem receipt_3_12_2359_0_part7 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 0) 896 29 = 1346789309687503001022150 := by decide +kernel
private theorem receipt_3_12_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 0) 0 256 = 882530386221335595493123200 :=
  phaseBlock_append receipt_3_12_2359_0_part0 receipt_3_12_2359_0_part1 rfl rfl rfl
private theorem receipt_3_12_2359_0_join1 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 0) 256 256 = 547045313440697650846262400 :=
  phaseBlock_append receipt_3_12_2359_0_part2 receipt_3_12_2359_0_part3 rfl rfl rfl
private theorem receipt_3_12_2359_0_join2 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 0) 0 512 = 1429575699662033246339385600 :=
  phaseBlock_append receipt_3_12_2359_0_join0 receipt_3_12_2359_0_join1 rfl rfl rfl
private theorem receipt_3_12_2359_0_join3 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 0) 512 256 = 260266204580903130521166976 :=
  phaseBlock_append receipt_3_12_2359_0_part4 receipt_3_12_2359_0_part5 rfl rfl rfl
private theorem receipt_3_12_2359_0_join4 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 0) 768 157 = 40156685908655127633191174 :=
  phaseBlock_append receipt_3_12_2359_0_part6 receipt_3_12_2359_0_part7 rfl rfl rfl
private theorem receipt_3_12_2359_0_join5 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 0) 512 413 = 300422890489558258154358150 :=
  phaseBlock_append receipt_3_12_2359_0_join3 receipt_3_12_2359_0_join4 rfl rfl rfl
private theorem receipt_3_12_2359_0_join6 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 0) 0 925 = 1729998590151591504493743750 :=
  phaseBlock_append receipt_3_12_2359_0_join2 receipt_3_12_2359_0_join5 rfl rfl rfl

private theorem receipt_3_12_2359_0 : fastPhase (bank 3 12).shape 179808 2379 31 1 1 1 0 = 1729998590151591504493743750 :=
  phase_of_block (n := 925) (by decide +kernel) receipt_3_12_2359_0_join6

private theorem receipt_3_12_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 1) 0 128 = 485387357901727796581409856 := by decide +kernel
private theorem receipt_3_12_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 1) 128 128 = 395759358395665566348534848 := by decide +kernel
private theorem receipt_3_12_2359_1_part2 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 1) 256 128 = 311873904719913849907389504 := by decide +kernel
private theorem receipt_3_12_2359_1_part3 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 1) 384 128 = 233964150230356928517334080 := by decide +kernel
private theorem receipt_3_12_2359_1_part4 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 1) 512 128 = 162260474402054323427189824 := by decide +kernel
private theorem receipt_3_12_2359_1_part5 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 1) 640 128 = 96990492265997253355758656 := by decide +kernel
private theorem receipt_3_12_2359_1_part6 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 1) 768 128 = 38379063845865091972342848 := by decide +kernel
private theorem receipt_3_12_2359_1_part7 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 1) 896 29 = 1256572773714755301787374 := by decide +kernel
private theorem receipt_3_12_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 1) 0 256 = 881146716297393362929944704 :=
  phaseBlock_append receipt_3_12_2359_1_part0 receipt_3_12_2359_1_part1 rfl rfl rfl
private theorem receipt_3_12_2359_1_join1 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 1) 256 256 = 545838054950270778424723584 :=
  phaseBlock_append receipt_3_12_2359_1_part2 receipt_3_12_2359_1_part3 rfl rfl rfl
private theorem receipt_3_12_2359_1_join2 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 1) 0 512 = 1426984771247664141354668288 :=
  phaseBlock_append receipt_3_12_2359_1_join0 receipt_3_12_2359_1_join1 rfl rfl rfl
private theorem receipt_3_12_2359_1_join3 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 1) 512 256 = 259250966668051576782948480 :=
  phaseBlock_append receipt_3_12_2359_1_part4 receipt_3_12_2359_1_part5 rfl rfl rfl
private theorem receipt_3_12_2359_1_join4 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 1) 768 157 = 39635636619579847274130222 :=
  phaseBlock_append receipt_3_12_2359_1_part6 receipt_3_12_2359_1_part7 rfl rfl rfl
private theorem receipt_3_12_2359_1_join5 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 1) 512 413 = 298886603287631424057078702 :=
  phaseBlock_append receipt_3_12_2359_1_join3 receipt_3_12_2359_1_join4 rfl rfl rfl
private theorem receipt_3_12_2359_1_join6 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2379 31 1 1 1 1) 0 925 = 1725871374535295565411746990 :=
  phaseBlock_append receipt_3_12_2359_1_join2 receipt_3_12_2359_1_join5 rfl rfl rfl

private theorem receipt_3_12_2359_1 : fastPhase (bank 3 12).shape 179808 2379 31 1 1 1 1 = 1725871374535295565411746990 :=
  phase_of_block (n := 925) (by decide +kernel) receipt_3_12_2359_1_join6

private theorem receipt_3_12_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 0) 0 128 = 486104441668275188285168096 := by decide +kernel
private theorem receipt_3_12_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 0) 128 128 = 396433053072155978364013024 := by decide +kernel
private theorem receipt_3_12_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 0) 256 128 = 312502493202002218587765216 := by decide +kernel
private theorem receipt_3_12_2360_0_part3 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 0) 384 128 = 234545910526792400211585504 := by decide +kernel
private theorem receipt_3_12_2360_0_part4 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 0) 512 128 = 162793679832027335942052320 := by decide +kernel
private theorem receipt_3_12_2360_0_part5 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 0) 640 128 = 97473411655607008115460576 := by decide +kernel
private theorem receipt_3_12_2360_0_part6 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 0) 768 128 = 38809961723707416876120544 := by decide +kernel
private theorem receipt_3_12_2360_0_part7 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 0) 896 29 = 1346790552252931206018045 := by decide +kernel
private theorem receipt_3_12_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 0) 0 256 = 882537494740431166649181120 :=
  phaseBlock_append receipt_3_12_2360_0_part0 receipt_3_12_2360_0_part1 rfl rfl rfl
private theorem receipt_3_12_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 0) 256 256 = 547048403728794618799350720 :=
  phaseBlock_append receipt_3_12_2360_0_part2 receipt_3_12_2360_0_part3 rfl rfl rfl
private theorem receipt_3_12_2360_0_join2 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 0) 0 512 = 1429585898469225785448531840 :=
  phaseBlock_append receipt_3_12_2360_0_join0 receipt_3_12_2360_0_join1 rfl rfl rfl
private theorem receipt_3_12_2360_0_join3 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 0) 512 256 = 260267091487634344057512896 :=
  phaseBlock_append receipt_3_12_2360_0_part4 receipt_3_12_2360_0_part5 rfl rfl rfl
private theorem receipt_3_12_2360_0_join4 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 0) 768 157 = 40156752275960348082138589 :=
  phaseBlock_append receipt_3_12_2360_0_part6 receipt_3_12_2360_0_part7 rfl rfl rfl
private theorem receipt_3_12_2360_0_join5 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 0) 512 413 = 300423843763594692139651485 :=
  phaseBlock_append receipt_3_12_2360_0_join3 receipt_3_12_2360_0_join4 rfl rfl rfl
private theorem receipt_3_12_2360_0_join6 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 0) 0 925 = 1730009742232820477588183325 :=
  phaseBlock_append receipt_3_12_2360_0_join2 receipt_3_12_2360_0_join5 rfl rfl rfl

private theorem receipt_3_12_2360_0 : fastPhase (bank 3 12).shape 179808 2380 31 1 1 1 0 = 1730009742232820477588183325 :=
  phase_of_block (n := 925) (by decide +kernel) receipt_3_12_2360_0_join6

private theorem receipt_3_12_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 1) 0 128 = 485391538007590542999761376 := by decide +kernel
private theorem receipt_3_12_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 1) 128 128 = 395762274061648637219283424 := by decide +kernel
private theorem receipt_3_12_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 1) 256 128 = 311875824050665550393119200 := by decide +kernel
private theorem receipt_3_12_2360_1_part3 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 1) 384 128 = 233965313593959553968931296 := by decide +kernel
private theorem receipt_3_12_2360_1_part4 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 1) 512 128 = 162261094704032971105563104 := by decide +kernel
private theorem receipt_3_12_2360_1_part5 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 1) 640 128 = 96990755222449024851337696 := by decide +kernel
private theorem receipt_3_12_2360_1_part6 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 1) 768 128 = 38379128255708686322356704 := by decide +kernel
private theorem receipt_3_12_2360_1_part7 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 1) 896 29 = 1256573935249906562542575 := by decide +kernel
private theorem receipt_3_12_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 1) 0 256 = 881153812069239180219044800 :=
  phaseBlock_append receipt_3_12_2360_1_part0 receipt_3_12_2360_1_part1 rfl rfl rfl
private theorem receipt_3_12_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 1) 256 256 = 545841137644625104362050496 :=
  phaseBlock_append receipt_3_12_2360_1_part2 receipt_3_12_2360_1_part3 rfl rfl rfl
private theorem receipt_3_12_2360_1_join2 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 1) 0 512 = 1426994949713864284581095296 :=
  phaseBlock_append receipt_3_12_2360_1_join0 receipt_3_12_2360_1_join1 rfl rfl rfl
private theorem receipt_3_12_2360_1_join3 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 1) 512 256 = 259251849926481995956900800 :=
  phaseBlock_append receipt_3_12_2360_1_part4 receipt_3_12_2360_1_part5 rfl rfl rfl
private theorem receipt_3_12_2360_1_join4 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 1) 768 157 = 39635702190958592884899279 :=
  phaseBlock_append receipt_3_12_2360_1_part6 receipt_3_12_2360_1_part7 rfl rfl rfl
private theorem receipt_3_12_2360_1_join5 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 1) 512 413 = 298887552117440588841800079 :=
  phaseBlock_append receipt_3_12_2360_1_join3 receipt_3_12_2360_1_join4 rfl rfl rfl
private theorem receipt_3_12_2360_1_join6 :
    phaseBlock (fastLayer (bank 3 12).shape 179808 2380 31 1 1 1 1) 0 925 = 1725882501831304873422895375 :=
  phaseBlock_append receipt_3_12_2360_1_join2 receipt_3_12_2360_1_join5 rfl rfl rfl

private theorem receipt_3_12_2360_1 : fastPhase (bank 3 12).shape 179808 2380 31 1 1 1 1 = 1725882501831304873422895375 :=
  phase_of_block (n := 925) (by decide +kernel) receipt_3_12_2360_1_join6

theorem receipt_3_12 : Checked (bank 3 12) 31 1 1 := by
  refine checked_from_values (bank 3 12) 31 1 1
    (P3_7_1.checked (bank 3 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4235_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_12_2359_0 receipt_3_12_2359_1 receipt_3_12_2360_0 receipt_3_12_2360_1 (by decide +kernel) (by decide +kernel)

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
    (word : K1.I → K1_14.L) (lo : 2379 ≤ h) (hi : h ≤ 33599) (rect : Fin 4)
    (i : Fin 2) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group4_stage i)).shape
      (cutoff h rect (group4_stage i)), ¬ G∣Q :=
  (group4_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group4_avoids

end Lower6960.RescueSource
