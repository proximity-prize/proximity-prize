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
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 0) 0 128 = 8223917662167301636378211072 := by decide +kernel
private theorem receipt_0_11_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 0) 128 128 = 6932281532071113723765535488 := by decide +kernel
private theorem receipt_0_11_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 0) 256 128 = 5714799273932087588800443136 := by decide +kernel
private theorem receipt_0_11_2359_0_part3 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 0) 384 128 = 4569266526745980816157127424 := by decide +kernel
private theorem receipt_0_11_2359_0_part4 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 0) 512 128 = 3493485455570052288715567872 := by decide +kernel
private theorem receipt_0_11_2359_0_part5 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 0) 640 128 = 2485265091603514067153637306 := by decide +kernel
private theorem receipt_0_11_2359_0_part6 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 0) 768 128 = 1542422729904855029197305902 := by decide +kernel
private theorem receipt_0_11_2359_0_part7 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 0) 896 128 = 662776108436828443392634598 := by decide +kernel
private theorem receipt_0_11_2359_0_part8 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 0) 1024 38 = 36474762813402105138997560 := by decide +kernel
private theorem receipt_0_11_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 0) 0 256 = 15156199194238415360143746560 :=
  phaseBlock_append receipt_0_11_2359_0_part0 receipt_0_11_2359_0_part1 rfl rfl rfl
private theorem receipt_0_11_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 0) 256 256 = 10284065800678068404957570560 :=
  phaseBlock_append receipt_0_11_2359_0_part2 receipt_0_11_2359_0_part3 rfl rfl rfl
private theorem receipt_0_11_2359_0_join2 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 0) 0 512 = 25440264994916483765101317120 :=
  phaseBlock_append receipt_0_11_2359_0_join0 receipt_0_11_2359_0_join1 rfl rfl rfl
private theorem receipt_0_11_2359_0_join3 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 0) 512 256 = 5978750547173566355869205178 :=
  phaseBlock_append receipt_0_11_2359_0_part4 receipt_0_11_2359_0_part5 rfl rfl rfl
private theorem receipt_0_11_2359_0_join4 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 0) 896 166 = 699250871250230548531632158 :=
  phaseBlock_append receipt_0_11_2359_0_part7 receipt_0_11_2359_0_part8 rfl rfl rfl
private theorem receipt_0_11_2359_0_join5 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 0) 768 294 = 2241673601155085577728938060 :=
  phaseBlock_append receipt_0_11_2359_0_part6 receipt_0_11_2359_0_join4 rfl rfl rfl
private theorem receipt_0_11_2359_0_join6 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 0) 512 550 = 8220424148328651933598143238 :=
  phaseBlock_append receipt_0_11_2359_0_join3 receipt_0_11_2359_0_join5 rfl rfl rfl
private theorem receipt_0_11_2359_0_join7 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 0) 0 1062 = 33660689143245135698699460358 :=
  phaseBlock_append receipt_0_11_2359_0_join2 receipt_0_11_2359_0_join6 rfl rfl rfl

private theorem receipt_0_11_2359_0 : fastPhase (bank 0 11).shape 179818 2359 32 1 0 1 0 = 33660689143245135698699460358 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_0_11_2359_0_join7

private theorem receipt_0_11_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 1) 0 128 = 8213671477446542067420542784 := by decide +kernel
private theorem receipt_0_11_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 1) 128 128 = 6922603675206956129450399552 := by decide +kernel
private theorem receipt_0_11_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 1) 256 128 = 5705673053608926814857295680 := by decide +kernel
private theorem receipt_0_11_2359_1_part3 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 1) 384 128 = 4560675301401983231175153472 := by decide +kernel
private theorem receipt_0_11_2359_1_part4 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 1) 512 128 = 3485412633349040742995343168 := by decide +kernel
private theorem receipt_0_11_2359_1_part5 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 1) 640 128 = 2477694129209102445978699852 := by decide +kernel
private theorem receipt_0_11_2359_1_part6 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 1) 768 128 = 1535337122246621744246726996 := by decide +kernel
private theorem receipt_0_11_2359_1_part7 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 1) 896 128 = 656159393426694410529876832 := by decide +kernel
private theorem receipt_0_11_2359_1_part8 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 1) 1024 38 = 34598269392652020380629740 := by decide +kernel
private theorem receipt_0_11_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 1) 0 256 = 15136275152653498196870942336 :=
  phaseBlock_append receipt_0_11_2359_1_part0 receipt_0_11_2359_1_part1 rfl rfl rfl
private theorem receipt_0_11_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 1) 256 256 = 10266348355010910046032449152 :=
  phaseBlock_append receipt_0_11_2359_1_part2 receipt_0_11_2359_1_part3 rfl rfl rfl
private theorem receipt_0_11_2359_1_join2 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 1) 0 512 = 25402623507664408242903391488 :=
  phaseBlock_append receipt_0_11_2359_1_join0 receipt_0_11_2359_1_join1 rfl rfl rfl
private theorem receipt_0_11_2359_1_join3 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 1) 512 256 = 5963106762558143188974043020 :=
  phaseBlock_append receipt_0_11_2359_1_part4 receipt_0_11_2359_1_part5 rfl rfl rfl
private theorem receipt_0_11_2359_1_join4 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 1) 896 166 = 690757662819346430910506572 :=
  phaseBlock_append receipt_0_11_2359_1_part7 receipt_0_11_2359_1_part8 rfl rfl rfl
private theorem receipt_0_11_2359_1_join5 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 1) 768 294 = 2226094785065968175157233568 :=
  phaseBlock_append receipt_0_11_2359_1_part6 receipt_0_11_2359_1_join4 rfl rfl rfl
private theorem receipt_0_11_2359_1_join6 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 1) 512 550 = 8189201547624111364131276588 :=
  phaseBlock_append receipt_0_11_2359_1_join3 receipt_0_11_2359_1_join5 rfl rfl rfl
private theorem receipt_0_11_2359_1_join7 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2359 32 1 0 1 1) 0 1062 = 33591825055288519607034668076 :=
  phaseBlock_append receipt_0_11_2359_1_join2 receipt_0_11_2359_1_join6 rfl rfl rfl

private theorem receipt_0_11_2359_1 : fastPhase (bank 0 11).shape 179818 2359 32 1 0 1 1 = 33591825055288519607034668076 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_0_11_2359_1_join7

private theorem receipt_0_11_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 0) 0 128 = 8223991238768363826418525952 := by decide +kernel
private theorem receipt_0_11_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 0) 128 128 = 6932339118049293691643152128 := by decide +kernel
private theorem receipt_0_11_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 0) 256 128 = 5714842946989312146824619776 := by decide +kernel
private theorem receipt_0_11_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 0) 384 128 = 4569298288574392816469083904 := by decide +kernel
private theorem receipt_0_11_2360_0_part4 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 0) 512 128 = 3493507232079537546586236672 := by decide +kernel
private theorem receipt_0_11_2360_0_part5 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 0) 640 128 = 2485278724776099012213327461 := by decide +kernel
private theorem receipt_0_11_2360_0_part6 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 0) 768 128 = 1542429985002753694647724624 := by decide +kernel
private theorem receipt_0_11_2360_0_part7 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 0) 896 128 = 662778710296731596642556488 := by decide +kernel
private theorem receipt_0_11_2360_0_part8 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 0) 1024 38 = 36474884067915651322481544 := by decide +kernel
private theorem receipt_0_11_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 0) 0 256 = 15156330356817657518061678080 :=
  phaseBlock_append receipt_0_11_2360_0_part0 receipt_0_11_2360_0_part1 rfl rfl rfl
private theorem receipt_0_11_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 0) 256 256 = 10284141235563704963293703680 :=
  phaseBlock_append receipt_0_11_2360_0_part2 receipt_0_11_2360_0_part3 rfl rfl rfl
private theorem receipt_0_11_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 0) 0 512 = 25440471592381362481355381760 :=
  phaseBlock_append receipt_0_11_2360_0_join0 receipt_0_11_2360_0_join1 rfl rfl rfl
private theorem receipt_0_11_2360_0_join3 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 0) 512 256 = 5978785956855636558799564133 :=
  phaseBlock_append receipt_0_11_2360_0_part4 receipt_0_11_2360_0_part5 rfl rfl rfl
private theorem receipt_0_11_2360_0_join4 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 0) 896 166 = 699253594364647247965038032 :=
  phaseBlock_append receipt_0_11_2360_0_part7 receipt_0_11_2360_0_part8 rfl rfl rfl
private theorem receipt_0_11_2360_0_join5 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 0) 768 294 = 2241683579367400942612762656 :=
  phaseBlock_append receipt_0_11_2360_0_part6 receipt_0_11_2360_0_join4 rfl rfl rfl
private theorem receipt_0_11_2360_0_join6 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 0) 512 550 = 8220469536223037501412326789 :=
  phaseBlock_append receipt_0_11_2360_0_join3 receipt_0_11_2360_0_join5 rfl rfl rfl
private theorem receipt_0_11_2360_0_join7 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 0) 0 1062 = 33660941128604399982767708549 :=
  phaseBlock_append receipt_0_11_2360_0_join2 receipt_0_11_2360_0_join6 rfl rfl rfl

private theorem receipt_0_11_2360_0 : fastPhase (bank 0 11).shape 179818 2360 32 1 0 1 0 = 33660941128604399982767708549 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_0_11_2360_0_join7

private theorem receipt_0_11_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 1) 0 128 = 8213744979290624573149470976 := by decide +kernel
private theorem receipt_0_11_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 1) 128 128 = 6922661194663907163704967424 := by decide +kernel
private theorem receipt_0_11_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 1) 256 128 = 5705716668021472695813841152 := by decide +kernel
private theorem receipt_0_11_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 1) 384 128 = 4560707012104312533278294272 := by decide +kernel
private theorem receipt_0_11_2360_1_part4 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 1) 512 128 = 3485434365894329914585669888 := by decide +kernel
private theorem receipt_0_11_2360_1_part5 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 1) 640 128 = 2477707725249803801566492668 := by decide +kernel
private theorem receipt_0_11_2360_1_part6 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 1) 768 128 = 1535344346758345339724671915 := by decide +kernel
private theorem receipt_0_11_2360_1_part7 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 1) 896 128 = 656161970880631364096838506 := by decide +kernel
private theorem receipt_0_11_2360_1_part8 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 1) 1024 38 = 34598384537367232512366821 := by decide +kernel
private theorem receipt_0_11_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 1) 0 256 = 15136406173954531736854438400 :=
  phaseBlock_append receipt_0_11_2360_1_part0 receipt_0_11_2360_1_part1 rfl rfl rfl
private theorem receipt_0_11_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 1) 256 256 = 10266423680125785229092135424 :=
  phaseBlock_append receipt_0_11_2360_1_part2 receipt_0_11_2360_1_part3 rfl rfl rfl
private theorem receipt_0_11_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 1) 0 512 = 25402829854080316965946573824 :=
  phaseBlock_append receipt_0_11_2360_1_join0 receipt_0_11_2360_1_join1 rfl rfl rfl
private theorem receipt_0_11_2360_1_join3 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 1) 512 256 = 5963142091144133716152162556 :=
  phaseBlock_append receipt_0_11_2360_1_part4 receipt_0_11_2360_1_part5 rfl rfl rfl
private theorem receipt_0_11_2360_1_join4 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 1) 896 166 = 690760355417998596609205327 :=
  phaseBlock_append receipt_0_11_2360_1_part7 receipt_0_11_2360_1_part8 rfl rfl rfl
private theorem receipt_0_11_2360_1_join5 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 1) 768 294 = 2226104702176343936333877242 :=
  phaseBlock_append receipt_0_11_2360_1_part6 receipt_0_11_2360_1_join4 rfl rfl rfl
private theorem receipt_0_11_2360_1_join6 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 1) 512 550 = 8189246793320477652486039798 :=
  phaseBlock_append receipt_0_11_2360_1_join3 receipt_0_11_2360_1_join5 rfl rfl rfl
private theorem receipt_0_11_2360_1_join7 :
    phaseBlock (fastLayer (bank 0 11).shape 179818 2360 32 1 0 1 1) 0 1062 = 33592076647400794618432613622 :=
  phaseBlock_append receipt_0_11_2360_1_join2 receipt_0_11_2360_1_join6 rfl rfl rfl

private theorem receipt_0_11_2360_1 : fastPhase (bank 0 11).shape 179818 2360 32 1 0 1 1 = 33592076647400794618432613622 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_0_11_2360_1_join7

theorem receipt_0_11 : Checked (bank 0 11) 32 0 1 := by
  refine checked_from_values (bank 0 11) 32 0 1
    (P3_7_1.checked (bank 0 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4866_1061)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_11_2359_0 receipt_0_11_2359_1 receipt_0_11_2360_0 receipt_0_11_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_11_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 0) 0 128 = 7336862349088841112850262976 := by decide +kernel
private theorem receipt_1_11_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 0) 128 128 = 6179126738870322052215720896 := by decide +kernel
private theorem receipt_1_11_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 0) 256 128 = 5089450873008172622516300736 := by decide +kernel
private theorem receipt_1_11_2359_0_part3 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 0) 384 128 = 4065700110812582031066500032 := by decide +kernel
private theorem receipt_1_11_2359_0_part4 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 0) 512 128 = 3105752403194604422596357056 := by decide +kernel
private theorem receipt_1_11_2359_0_part5 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 0) 640 128 = 2207498575089378896461548630 := by decide +kernel
private theorem receipt_1_11_2359_0_part6 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 0) 768 128 = 1368843545125803449362102223 := by decide +kernel
private theorem receipt_1_11_2359_0_part7 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 0) 896 128 = 587699365170910324986911035 := by decide +kernel
private theorem receipt_1_11_2359_0_part8 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 0) 1024 38 = 32322809487195159535221294 := by decide +kernel
private theorem receipt_1_11_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 0) 0 256 = 13515989087959163165065983872 :=
  phaseBlock_append receipt_1_11_2359_0_part0 receipt_1_11_2359_0_part1 rfl rfl rfl
private theorem receipt_1_11_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 0) 256 256 = 9155150983820754653582800768 :=
  phaseBlock_append receipt_1_11_2359_0_part2 receipt_1_11_2359_0_part3 rfl rfl rfl
private theorem receipt_1_11_2359_0_join2 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 0) 0 512 = 22671140071779917818648784640 :=
  phaseBlock_append receipt_1_11_2359_0_join0 receipt_1_11_2359_0_join1 rfl rfl rfl
private theorem receipt_1_11_2359_0_join3 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 0) 512 256 = 5313250978283983319057905686 :=
  phaseBlock_append receipt_1_11_2359_0_part4 receipt_1_11_2359_0_part5 rfl rfl rfl
private theorem receipt_1_11_2359_0_join4 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 0) 896 166 = 620022174658105484522132329 :=
  phaseBlock_append receipt_1_11_2359_0_part7 receipt_1_11_2359_0_part8 rfl rfl rfl
private theorem receipt_1_11_2359_0_join5 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 0) 768 294 = 1988865719783908933884234552 :=
  phaseBlock_append receipt_1_11_2359_0_part6 receipt_1_11_2359_0_join4 rfl rfl rfl
private theorem receipt_1_11_2359_0_join6 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 0) 512 550 = 7302116698067892252942140238 :=
  phaseBlock_append receipt_1_11_2359_0_join3 receipt_1_11_2359_0_join5 rfl rfl rfl
private theorem receipt_1_11_2359_0_join7 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 0) 0 1062 = 29973256769847810071590924878 :=
  phaseBlock_append receipt_1_11_2359_0_join2 receipt_1_11_2359_0_join6 rfl rfl rfl

private theorem receipt_1_11_2359_0 : fastPhase (bank 1 11).shape 179818 2359 32 1 0 2 0 = 29973256769847810071590924878 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_1_11_2359_0_join7

private theorem receipt_1_11_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 1) 0 128 = 7327671183634436137027609344 := by decide +kernel
private theorem receipt_1_11_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 1) 128 128 = 6170458053787639724055536384 := by decide +kernel
private theorem receipt_1_11_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 1) 256 128 = 5081288467913159482086695680 := by decide +kernel
private theorem receipt_1_11_2359_1_part3 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 1) 384 128 = 4058027881383460230554198784 := by decide +kernel
private theorem receipt_1_11_2359_1_part4 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 1) 512 128 = 3098554340979411561713345280 := by decide +kernel
private theorem receipt_1_11_2359_1_part5 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 1) 640 128 = 2200758766336642942447635653 := by decide +kernel
private theorem receipt_1_11_2359_1_part6 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 1) 768 128 = 1362546161439698824078625103 := by decide +kernel
private theorem receipt_1_11_2359_1_part7 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 1) 896 128 = 581828667685449917769567826 := by decide +kernel
private theorem receipt_1_11_2359_1_part8 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 1) 1024 38 = 30659777216450303237805219 := by decide +kernel
private theorem receipt_1_11_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 1) 0 256 = 13498129237422075861083145728 :=
  phaseBlock_append receipt_1_11_2359_1_part0 receipt_1_11_2359_1_part1 rfl rfl rfl
private theorem receipt_1_11_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 1) 256 256 = 9139316349296619712640894464 :=
  phaseBlock_append receipt_1_11_2359_1_part2 receipt_1_11_2359_1_part3 rfl rfl rfl
private theorem receipt_1_11_2359_1_join2 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 1) 0 512 = 22637445586718695573724040192 :=
  phaseBlock_append receipt_1_11_2359_1_join0 receipt_1_11_2359_1_join1 rfl rfl rfl
private theorem receipt_1_11_2359_1_join3 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 1) 512 256 = 5299313107316054504160980933 :=
  phaseBlock_append receipt_1_11_2359_1_part4 receipt_1_11_2359_1_part5 rfl rfl rfl
private theorem receipt_1_11_2359_1_join4 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 1) 896 166 = 612488444901900221007373045 :=
  phaseBlock_append receipt_1_11_2359_1_part7 receipt_1_11_2359_1_part8 rfl rfl rfl
private theorem receipt_1_11_2359_1_join5 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 1) 768 294 = 1975034606341599045085998148 :=
  phaseBlock_append receipt_1_11_2359_1_part6 receipt_1_11_2359_1_join4 rfl rfl rfl
private theorem receipt_1_11_2359_1_join6 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 1) 512 550 = 7274347713657653549246979081 :=
  phaseBlock_append receipt_1_11_2359_1_join3 receipt_1_11_2359_1_join5 rfl rfl rfl
private theorem receipt_1_11_2359_1_join7 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2359 32 1 0 2 1) 0 1062 = 29911793300376349122971019273 :=
  phaseBlock_append receipt_1_11_2359_1_join2 receipt_1_11_2359_1_join6 rfl rfl rfl

private theorem receipt_1_11_2359_1 : fastPhase (bank 1 11).shape 179818 2359 32 1 0 2 1 = 29911793300376349122971019273 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_1_11_2359_1_join7

private theorem receipt_1_11_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 0) 0 128 = 7336927989843568286166143616 := by decide +kernel
private theorem receipt_1_11_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 0) 128 128 = 6179178068739203108077408896 := by decide +kernel
private theorem receipt_1_11_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 0) 256 128 = 5089489767344268115684315776 := by decide +kernel
private theorem receipt_1_11_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 0) 384 128 = 4065728372466471251548639872 := by decide +kernel
private theorem receipt_1_11_2360_0_part4 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 0) 512 128 = 3105771762951573209083990656 := by decide +kernel
private theorem receipt_1_11_2360_0_part5 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 0) 640 128 = 2207510684670524234119284342 := by decide +kernel
private theorem receipt_1_11_2360_0_part6 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 0) 768 128 = 1368849983838420569919425238 := by decide +kernel
private theorem receipt_1_11_2360_0_part7 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 0) 896 128 = 587701672333717660771771788 := by decide +kernel
private theorem receipt_1_11_2360_0_part8 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 0) 1024 38 = 32322916939327880839402794 := by decide +kernel
private theorem receipt_1_11_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 0) 0 256 = 13516106058582771394243552512 :=
  phaseBlock_append receipt_1_11_2360_0_part0 receipt_1_11_2360_0_part1 rfl rfl rfl
private theorem receipt_1_11_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 0) 256 256 = 9155218139810739367232955648 :=
  phaseBlock_append receipt_1_11_2360_0_part2 receipt_1_11_2360_0_part3 rfl rfl rfl
private theorem receipt_1_11_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 0) 0 512 = 22671324198393510761476508160 :=
  phaseBlock_append receipt_1_11_2360_0_join0 receipt_1_11_2360_0_join1 rfl rfl rfl
private theorem receipt_1_11_2360_0_join3 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 0) 512 256 = 5313282447622097443203274998 :=
  phaseBlock_append receipt_1_11_2360_0_part4 receipt_1_11_2360_0_part5 rfl rfl rfl
private theorem receipt_1_11_2360_0_join4 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 0) 896 166 = 620024589273045541611174582 :=
  phaseBlock_append receipt_1_11_2360_0_part7 receipt_1_11_2360_0_part8 rfl rfl rfl
private theorem receipt_1_11_2360_0_join5 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 0) 768 294 = 1988874573111466111530599820 :=
  phaseBlock_append receipt_1_11_2360_0_part6 receipt_1_11_2360_0_join4 rfl rfl rfl
private theorem receipt_1_11_2360_0_join6 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 0) 512 550 = 7302157020733563554733874818 :=
  phaseBlock_append receipt_1_11_2360_0_join3 receipt_1_11_2360_0_join5 rfl rfl rfl
private theorem receipt_1_11_2360_0_join7 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 0) 0 1062 = 29973481219127074316210382978 :=
  phaseBlock_append receipt_1_11_2360_0_join2 receipt_1_11_2360_0_join6 rfl rfl rfl

private theorem receipt_1_11_2360_0 : fastPhase (bank 1 11).shape 179818 2360 32 1 0 2 0 = 29973481219127074316210382978 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_1_11_2360_0_join7

private theorem receipt_1_11_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 1) 0 128 = 7327736757246395903937140736 := by decide +kernel
private theorem receipt_1_11_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 1) 128 128 = 6170509324010818136812050432 := by decide +kernel
private theorem receipt_1_11_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 1) 256 128 = 5081327309755200452671297536 := by decide +kernel
private theorem receipt_1_11_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 1) 384 128 = 4058056097351924991348135936 := by decide +kernel
private theorem receipt_1_11_2360_1_part4 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 1) 512 128 = 3098573661518961256254068736 := by decide +kernel
private theorem receipt_1_11_2360_1_part5 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 1) 640 128 = 2200770842853180907388874126 := by decide +kernel
private theorem receipt_1_11_2360_1_part6 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 1) 768 128 = 1362552572964697617051251442 := by decide +kernel
private theorem receipt_1_11_2360_1_part7 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 1) 896 128 = 581830953192756092875717680 := by decide +kernel
private theorem receipt_1_11_2360_1_part8 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 1) 1024 38 = 30659879253784247693545965 := by decide +kernel
private theorem receipt_1_11_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 1) 0 256 = 13498246081257214040749191168 :=
  phaseBlock_append receipt_1_11_2360_1_part0 receipt_1_11_2360_1_part1 rfl rfl rfl
private theorem receipt_1_11_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 1) 256 256 = 9139383407107125444019433472 :=
  phaseBlock_append receipt_1_11_2360_1_part2 receipt_1_11_2360_1_part3 rfl rfl rfl
private theorem receipt_1_11_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 1) 0 512 = 22637629488364339484768624640 :=
  phaseBlock_append receipt_1_11_2360_1_join0 receipt_1_11_2360_1_join1 rfl rfl rfl
private theorem receipt_1_11_2360_1_join3 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 1) 512 256 = 5299344504372142163642942862 :=
  phaseBlock_append receipt_1_11_2360_1_part4 receipt_1_11_2360_1_part5 rfl rfl rfl
private theorem receipt_1_11_2360_1_join4 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 1) 896 166 = 612490832446540340569263645 :=
  phaseBlock_append receipt_1_11_2360_1_part7 receipt_1_11_2360_1_part8 rfl rfl rfl
private theorem receipt_1_11_2360_1_join5 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 1) 768 294 = 1975043405411237957620515087 :=
  phaseBlock_append receipt_1_11_2360_1_part6 receipt_1_11_2360_1_join4 rfl rfl rfl
private theorem receipt_1_11_2360_1_join6 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 1) 512 550 = 7274387909783380121263457949 :=
  phaseBlock_append receipt_1_11_2360_1_join3 receipt_1_11_2360_1_join5 rfl rfl rfl
private theorem receipt_1_11_2360_1_join7 :
    phaseBlock (fastLayer (bank 1 11).shape 179818 2360 32 1 0 2 1) 0 1062 = 29912017398147719606032082589 :=
  phaseBlock_append receipt_1_11_2360_1_join2 receipt_1_11_2360_1_join6 rfl rfl rfl

private theorem receipt_1_11_2360_1 : fastPhase (bank 1 11).shape 179818 2360 32 1 0 2 1 = 29912017398147719606032082589 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_1_11_2360_1_join7

theorem receipt_1_11 : Checked (bank 1 11) 32 0 2 := by
  refine checked_from_values (bank 1 11) 32 0 2
    (P3_7_1.checked (bank 1 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4866_1061)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_11_2359_0 receipt_1_11_2359_1 receipt_1_11_2360_0 receipt_1_11_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_11_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 0) 0 128 = 3686444713139156897548297728 := by decide +kernel
private theorem receipt_2_11_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 0) 128 128 = 3084455990531416323198019072 := by decide +kernel
private theorem receipt_2_11_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 0) 256 128 = 2523852479522594582306121216 := by decide +kernel
private theorem receipt_2_11_2359_0_part3 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 0) 384 128 = 2002895391531102981431551488 := by decide +kernel
private theorem receipt_2_11_2359_0_part4 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 0) 512 128 = 1519882054311926139025057280 := by decide +kernel
private theorem receipt_2_11_2359_0_part5 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 0) 640 128 = 1073145753237820217052697138 := by decide +kernel
private theorem receipt_2_11_2359_0_part6 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 0) 768 128 = 661056020162432528139441978 := by decide +kernel
private theorem receipt_2_11_2359_0_part7 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 0) 896 128 = 282014975969196893168830530 := by decide +kernel
private theorem receipt_2_11_2359_0_part8 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 0) 1024 38 = 15436246363340971365375760 := by decide +kernel
private theorem receipt_2_11_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 0) 0 256 = 6770900703670573220746316800 :=
  phaseBlock_append receipt_2_11_2359_0_part0 receipt_2_11_2359_0_part1 rfl rfl rfl
private theorem receipt_2_11_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 0) 256 256 = 4526747871053697563737672704 :=
  phaseBlock_append receipt_2_11_2359_0_part2 receipt_2_11_2359_0_part3 rfl rfl rfl
private theorem receipt_2_11_2359_0_join2 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 0) 0 512 = 11297648574724270784483989504 :=
  phaseBlock_append receipt_2_11_2359_0_join0 receipt_2_11_2359_0_join1 rfl rfl rfl
private theorem receipt_2_11_2359_0_join3 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 0) 512 256 = 2593027807549746356077754418 :=
  phaseBlock_append receipt_2_11_2359_0_part4 receipt_2_11_2359_0_part5 rfl rfl rfl
private theorem receipt_2_11_2359_0_join4 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 0) 896 166 = 297451222332537864534206290 :=
  phaseBlock_append receipt_2_11_2359_0_part7 receipt_2_11_2359_0_part8 rfl rfl rfl
private theorem receipt_2_11_2359_0_join5 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 0) 768 294 = 958507242494970392673648268 :=
  phaseBlock_append receipt_2_11_2359_0_part6 receipt_2_11_2359_0_join4 rfl rfl rfl
private theorem receipt_2_11_2359_0_join6 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 0) 512 550 = 3551535050044716748751402686 :=
  phaseBlock_append receipt_2_11_2359_0_join3 receipt_2_11_2359_0_join5 rfl rfl rfl
private theorem receipt_2_11_2359_0_join7 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 0) 0 1062 = 14849183624768987533235392190 :=
  phaseBlock_append receipt_2_11_2359_0_join2 receipt_2_11_2359_0_join6 rfl rfl rfl

private theorem receipt_2_11_2359_0 : fastPhase (bank 2 11).shape 179818 2359 32 1 0 7 0 = 14849183624768987533235392190 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_2_11_2359_0_join7

private theorem receipt_2_11_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 1) 0 128 = 3681638502969206592263207744 := by decide +kernel
private theorem receipt_2_11_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 1) 128 128 = 3079970775450547911996152640 := by decide +kernel
private theorem receipt_2_11_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 1) 256 128 = 2519674910748352679995865920 := by decide +kernel
private theorem receipt_2_11_2359_1_part3 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 1) 384 128 = 1999012397005828308946639680 := by decide +kernel
private theorem receipt_2_11_2359_1_part4 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 1) 512 128 = 1516280836345118507155995456 := by decide +kernel
private theorem receipt_2_11_2359_1_part5 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 1) 640 128 = 1069813785666951338372087600 := by decide +kernel
private theorem receipt_2_11_2359_1_part6 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 1) 768 128 = 657981041551720538832994528 := by decide +kernel
private theorem receipt_2_11_2359_1_part7 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 1) 896 128 = 279184989608706089815245288 := by decide +kernel
private theorem receipt_2_11_2359_1_part8 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 1) 1024 38 = 14641520482172265655299816 := by decide +kernel
private theorem receipt_2_11_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 1) 0 256 = 6761609278419754504259360384 :=
  phaseBlock_append receipt_2_11_2359_1_part0 receipt_2_11_2359_1_part1 rfl rfl rfl
private theorem receipt_2_11_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 1) 256 256 = 4518687307754180988942505600 :=
  phaseBlock_append receipt_2_11_2359_1_part2 receipt_2_11_2359_1_part3 rfl rfl rfl
private theorem receipt_2_11_2359_1_join2 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 1) 0 512 = 11280296586173935493201865984 :=
  phaseBlock_append receipt_2_11_2359_1_join0 receipt_2_11_2359_1_join1 rfl rfl rfl
private theorem receipt_2_11_2359_1_join3 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 1) 512 256 = 2586094622012069845528083056 :=
  phaseBlock_append receipt_2_11_2359_1_part4 receipt_2_11_2359_1_part5 rfl rfl rfl
private theorem receipt_2_11_2359_1_join4 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 1) 896 166 = 293826510090878355470545104 :=
  phaseBlock_append receipt_2_11_2359_1_part7 receipt_2_11_2359_1_part8 rfl rfl rfl
private theorem receipt_2_11_2359_1_join5 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 1) 768 294 = 951807551642598894303539632 :=
  phaseBlock_append receipt_2_11_2359_1_part6 receipt_2_11_2359_1_join4 rfl rfl rfl
private theorem receipt_2_11_2359_1_join6 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 1) 512 550 = 3537902173654668739831622688 :=
  phaseBlock_append receipt_2_11_2359_1_join3 receipt_2_11_2359_1_join5 rfl rfl rfl
private theorem receipt_2_11_2359_1_join7 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2359 32 1 0 7 1) 0 1062 = 14818198759828604233033488672 :=
  phaseBlock_append receipt_2_11_2359_1_join2 receipt_2_11_2359_1_join6 rfl rfl rfl

private theorem receipt_2_11_2359_1 : fastPhase (bank 2 11).shape 179818 2359 32 1 0 7 1 = 14818198759828604233033488672 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_2_11_2359_1_join7

private theorem receipt_2_11_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 0) 0 128 = 3686477695940188192045755648 := by decide +kernel
private theorem receipt_2_11_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 0) 128 128 = 3084481614141493739193076992 := by decide +kernel
private theorem receipt_2_11_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 0) 256 128 = 2523871768118595913292426496 := by decide +kernel
private theorem receipt_2_11_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 0) 384 128 = 2002909314916779304139083008 := by decide +kernel
private theorem receipt_2_11_2360_0_part4 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 0) 512 128 = 1519891529139073887413464320 := by decide +kernel
private theorem receipt_2_11_2360_0_part5 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 0) 640 128 = 1073151640609191486773859165 := by decide +kernel
private theorem receipt_2_11_2360_0_part6 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 0) 768 128 = 661059129905102497339905288 := by decide +kernel
private theorem receipt_2_11_2360_0_part7 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 0) 896 128 = 282016083206727813704181560 := by decide +kernel
private theorem receipt_2_11_2360_0_part8 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 0) 1024 38 = 15436297679185347475854800 := by decide +kernel
private theorem receipt_2_11_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 0) 0 256 = 6770959310081681931238832640 :=
  phaseBlock_append receipt_2_11_2360_0_part0 receipt_2_11_2360_0_part1 rfl rfl rfl
private theorem receipt_2_11_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 0) 256 256 = 4526781083035375217431509504 :=
  phaseBlock_append receipt_2_11_2360_0_part2 receipt_2_11_2360_0_part3 rfl rfl rfl
private theorem receipt_2_11_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 0) 0 512 = 11297740393117057148670342144 :=
  phaseBlock_append receipt_2_11_2360_0_join0 receipt_2_11_2360_0_join1 rfl rfl rfl
private theorem receipt_2_11_2360_0_join3 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 0) 512 256 = 2593043169748265374187323485 :=
  phaseBlock_append receipt_2_11_2360_0_part4 receipt_2_11_2360_0_part5 rfl rfl rfl
private theorem receipt_2_11_2360_0_join4 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 0) 896 166 = 297452380885913161180036360 :=
  phaseBlock_append receipt_2_11_2360_0_part7 receipt_2_11_2360_0_part8 rfl rfl rfl
private theorem receipt_2_11_2360_0_join5 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 0) 768 294 = 958511510791015658519941648 :=
  phaseBlock_append receipt_2_11_2360_0_part6 receipt_2_11_2360_0_join4 rfl rfl rfl
private theorem receipt_2_11_2360_0_join6 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 0) 512 550 = 3551554680539281032707265133 :=
  phaseBlock_append receipt_2_11_2360_0_join3 receipt_2_11_2360_0_join5 rfl rfl rfl
private theorem receipt_2_11_2360_0_join7 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 0) 0 1062 = 14849295073656338181377607277 :=
  phaseBlock_append receipt_2_11_2360_0_join2 receipt_2_11_2360_0_join6 rfl rfl rfl

private theorem receipt_2_11_2360_0 : fastPhase (bank 2 11).shape 179818 2360 32 1 0 7 0 = 14849295073656338181377607277 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_2_11_2360_0_join7

private theorem receipt_2_11_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 1) 0 128 = 3681671450349599040800527616 := by decide +kernel
private theorem receipt_2_11_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 1) 128 128 = 3079996367972477486052242688 := by decide +kernel
private theorem receipt_2_11_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 1) 256 128 = 2519694172318651746267649280 := by decide +kernel
private theorem receipt_2_11_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 1) 384 128 = 1999026297164975302299170048 := by decide +kernel
private theorem receipt_2_11_2360_1_part4 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 1) 512 128 = 1516290291488346026782954752 := by decide +kernel
private theorem receipt_2_11_2360_1_part5 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 1) 640 128 = 1069819656658460756344694420 := by decide +kernel
private theorem receipt_2_11_2360_1_part6 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 1) 768 128 = 657984138004316341769784691 := by decide +kernel
private theorem receipt_2_11_2360_1_part7 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 1) 896 128 = 279186086402567226711072010 := by decide +kernel
private theorem receipt_2_11_2360_1_part8 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 1) 1024 38 = 14641569210322538686877545 := by decide +kernel
private theorem receipt_2_11_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 1) 0 256 = 6761667818322076526852770304 :=
  phaseBlock_append receipt_2_11_2360_1_part0 receipt_2_11_2360_1_part1 rfl rfl rfl
private theorem receipt_2_11_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 1) 256 256 = 4518720469483627048566819328 :=
  phaseBlock_append receipt_2_11_2360_1_part2 receipt_2_11_2360_1_part3 rfl rfl rfl
private theorem receipt_2_11_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 1) 0 512 = 11280388287805703575419589632 :=
  phaseBlock_append receipt_2_11_2360_1_join0 receipt_2_11_2360_1_join1 rfl rfl rfl
private theorem receipt_2_11_2360_1_join3 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 1) 512 256 = 2586109948146806783127649172 :=
  phaseBlock_append receipt_2_11_2360_1_part4 receipt_2_11_2360_1_part5 rfl rfl rfl
private theorem receipt_2_11_2360_1_join4 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 1) 896 166 = 293827655612889765397949555 :=
  phaseBlock_append receipt_2_11_2360_1_part7 receipt_2_11_2360_1_part8 rfl rfl rfl
private theorem receipt_2_11_2360_1_join5 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 1) 768 294 = 951811793617206107167734246 :=
  phaseBlock_append receipt_2_11_2360_1_part6 receipt_2_11_2360_1_join4 rfl rfl rfl
private theorem receipt_2_11_2360_1_join6 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 1) 512 550 = 3537921741764012890295383418 :=
  phaseBlock_append receipt_2_11_2360_1_join3 receipt_2_11_2360_1_join5 rfl rfl rfl
private theorem receipt_2_11_2360_1_join7 :
    phaseBlock (fastLayer (bank 2 11).shape 179818 2360 32 1 0 7 1) 0 1062 = 14818310029569716465714973050 :=
  phaseBlock_append receipt_2_11_2360_1_join2 receipt_2_11_2360_1_join6 rfl rfl rfl

private theorem receipt_2_11_2360_1 : fastPhase (bank 2 11).shape 179818 2360 32 1 0 7 1 = 14818310029569716465714973050 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_2_11_2360_1_join7

theorem receipt_2_11 : Checked (bank 2 11) 32 0 7 := by
  refine checked_from_values (bank 2 11) 32 0 7
    (P3_7_1.checked (bank 2 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4866_1061)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_11_2359_0 receipt_2_11_2359_1 receipt_2_11_2360_0 receipt_2_11_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_11_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 0) 0 128 = 391365608946557058575785248 := by decide +kernel
private theorem receipt_3_11_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 0) 128 128 = 309518662692320100481191200 := by decide +kernel
private theorem receipt_3_11_2359_0_part2 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 0) 256 128 = 233455084584970005594127648 := by decide +kernel
private theorem receipt_3_11_2359_0_part3 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 0) 384 128 = 163442140247102735226842400 := by decide +kernel
private theorem receipt_3_11_2359_0_part4 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 0) 512 128 = 99744143792435902157430048 := by decide +kernel
private theorem receipt_3_11_2359_0_part5 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 0) 640 128 = 42622467280157414154767648 := by decide +kernel
private theorem receipt_3_11_2359_0_part6 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 0) 768 42 = 2687385692222626068541609 := by decide +kernel
private theorem receipt_3_11_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 0) 128 256 = 542973747277290106075318848 :=
  phaseBlock_append receipt_3_11_2359_0_part1 receipt_3_11_2359_0_part2 rfl rfl rfl
private theorem receipt_3_11_2359_0_join1 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 0) 0 384 = 934339356223847164651104096 :=
  phaseBlock_append receipt_3_11_2359_0_part0 receipt_3_11_2359_0_join0 rfl rfl rfl
private theorem receipt_3_11_2359_0_join2 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 0) 384 256 = 263186284039538637384272448 :=
  phaseBlock_append receipt_3_11_2359_0_part3 receipt_3_11_2359_0_part4 rfl rfl rfl
private theorem receipt_3_11_2359_0_join3 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 0) 640 170 = 45309852972380040223309257 :=
  phaseBlock_append receipt_3_11_2359_0_part5 receipt_3_11_2359_0_part6 rfl rfl rfl
private theorem receipt_3_11_2359_0_join4 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 0) 384 426 = 308496137011918677607581705 :=
  phaseBlock_append receipt_3_11_2359_0_join2 receipt_3_11_2359_0_join3 rfl rfl rfl
private theorem receipt_3_11_2359_0_join5 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 0) 0 810 = 1242835493235765842258685801 :=
  phaseBlock_append receipt_3_11_2359_0_join1 receipt_3_11_2359_0_join4 rfl rfl rfl

private theorem receipt_3_11_2359_0 : fastPhase (bank 3 11).shape 179818 2359 32 1 1 1 0 = 1242835493235765842258685801 :=
  phase_of_block (n := 810) (by decide +kernel) receipt_3_11_2359_0_join5

private theorem receipt_3_11_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 1) 0 128 = 390712621740650783517993632 := by decide +kernel
private theorem receipt_3_11_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 1) 128 128 = 308908013482996718285642400 := by decide +kernel
private theorem receipt_3_11_2359_1_part2 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 1) 256 128 = 232889040468343350163425952 := by decide +kernel
private theorem receipt_3_11_2359_1_part3 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 1) 384 128 = 162922944029370109298227872 := by decide +kernel
private theorem receipt_3_11_2359_1_part4 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 1) 512 128 = 99274014066658142501481120 := by decide +kernel
private theorem receipt_3_11_2359_1_part5 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 1) 640 128 = 42203598503038956774103712 := by decide +kernel
private theorem receipt_3_11_2359_1_part6 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 1) 768 42 = 2561481592536155830280341 := by decide +kernel
private theorem receipt_3_11_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 1) 128 256 = 541797053951340068449068352 :=
  phaseBlock_append receipt_3_11_2359_1_part1 receipt_3_11_2359_1_part2 rfl rfl rfl
private theorem receipt_3_11_2359_1_join1 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 1) 0 384 = 932509675691990851967061984 :=
  phaseBlock_append receipt_3_11_2359_1_part0 receipt_3_11_2359_1_join0 rfl rfl rfl
private theorem receipt_3_11_2359_1_join2 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 1) 384 256 = 262196958096028251799708992 :=
  phaseBlock_append receipt_3_11_2359_1_part3 receipt_3_11_2359_1_part4 rfl rfl rfl
private theorem receipt_3_11_2359_1_join3 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 1) 640 170 = 44765080095575112604384053 :=
  phaseBlock_append receipt_3_11_2359_1_part5 receipt_3_11_2359_1_part6 rfl rfl rfl
private theorem receipt_3_11_2359_1_join4 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 1) 384 426 = 306962038191603364404093045 :=
  phaseBlock_append receipt_3_11_2359_1_join2 receipt_3_11_2359_1_join3 rfl rfl rfl
private theorem receipt_3_11_2359_1_join5 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2359 32 1 1 1 1) 0 810 = 1239471713883594216371155029 :=
  phaseBlock_append receipt_3_11_2359_1_join1 receipt_3_11_2359_1_join4 rfl rfl rfl

private theorem receipt_3_11_2359_1 : fastPhase (bank 3 11).shape 179818 2359 32 1 1 1 1 = 1239471713883594216371155029 :=
  phase_of_block (n := 810) (by decide +kernel) receipt_3_11_2359_1_join5

private theorem receipt_3_11_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 0) 0 128 = 391368952570786218831926592 := by decide +kernel
private theorem receipt_3_11_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 0) 128 128 = 309520883991675493791094080 := by decide +kernel
private theorem receipt_3_11_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 0) 256 128 = 233456449974934589801977152 := by decide +kernel
private theorem receipt_3_11_2360_0_part3 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 0) 384 128 = 163442885546509226433172800 := by decide +kernel
private theorem receipt_3_11_2360_0_part4 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 0) 512 128 = 99744474512063975437653312 := by decide +kernel
private theorem receipt_3_11_2360_0_part5 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 0) 640 128 = 42622558910451294975481152 := by decide +kernel
private theorem receipt_3_11_2360_0_part6 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 0) 768 42 = 2687389147941561649572756 := by decide +kernel
private theorem receipt_3_11_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 0) 128 256 = 542977333966610083593071232 :=
  phaseBlock_append receipt_3_11_2360_0_part1 receipt_3_11_2360_0_part2 rfl rfl rfl
private theorem receipt_3_11_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 0) 0 384 = 934346286537396302424997824 :=
  phaseBlock_append receipt_3_11_2360_0_part0 receipt_3_11_2360_0_join0 rfl rfl rfl
private theorem receipt_3_11_2360_0_join2 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 0) 384 256 = 263187360058573201870826112 :=
  phaseBlock_append receipt_3_11_2360_0_part3 receipt_3_11_2360_0_part4 rfl rfl rfl
private theorem receipt_3_11_2360_0_join3 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 0) 640 170 = 45309948058392856625053908 :=
  phaseBlock_append receipt_3_11_2360_0_part5 receipt_3_11_2360_0_part6 rfl rfl rfl
private theorem receipt_3_11_2360_0_join4 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 0) 384 426 = 308497308116966058495880020 :=
  phaseBlock_append receipt_3_11_2360_0_join2 receipt_3_11_2360_0_join3 rfl rfl rfl
private theorem receipt_3_11_2360_0_join5 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 0) 0 810 = 1242843594654362360920877844 :=
  phaseBlock_append receipt_3_11_2360_0_join1 receipt_3_11_2360_0_join4 rfl rfl rfl

private theorem receipt_3_11_2360_0 : fastPhase (bank 3 11).shape 179818 2360 32 1 1 1 0 = 1242843594654362360920877844 :=
  phase_of_block (n := 810) (by decide +kernel) receipt_3_11_2360_0_join5

private theorem receipt_3_11_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 1) 0 128 = 390715958945341813195349952 := by decide +kernel
private theorem receipt_3_11_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 1) 128 128 = 308910229800011316852465600 := by decide +kernel
private theorem receipt_3_11_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 1) 256 128 = 232890402144062822652583872 := by decide +kernel
private theorem receipt_3_11_2360_1_part3 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 1) 384 128 = 162923686715277188124614592 := by decide +kernel
private theorem receipt_3_11_2360_1_part4 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 1) 512 128 = 99274343107928553183453120 := by decide +kernel
private theorem receipt_3_11_2360_1_part5 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 1) 640 128 = 42203689226253374352695232 := by decide +kernel
private theorem receipt_3_11_2360_1_part6 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 1) 768 42 = 2561484891213203630420676 := by decide +kernel
private theorem receipt_3_11_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 1) 128 256 = 541800631944074139505049472 :=
  phaseBlock_append receipt_3_11_2360_1_part1 receipt_3_11_2360_1_part2 rfl rfl rfl
private theorem receipt_3_11_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 1) 0 384 = 932516590889415952700399424 :=
  phaseBlock_append receipt_3_11_2360_1_part0 receipt_3_11_2360_1_join0 rfl rfl rfl
private theorem receipt_3_11_2360_1_join2 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 1) 384 256 = 262198029823205741308067712 :=
  phaseBlock_append receipt_3_11_2360_1_part3 receipt_3_11_2360_1_part4 rfl rfl rfl
private theorem receipt_3_11_2360_1_join3 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 1) 640 170 = 44765174117466577983115908 :=
  phaseBlock_append receipt_3_11_2360_1_part5 receipt_3_11_2360_1_part6 rfl rfl rfl
private theorem receipt_3_11_2360_1_join4 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 1) 384 426 = 306963203940672319291183620 :=
  phaseBlock_append receipt_3_11_2360_1_join2 receipt_3_11_2360_1_join3 rfl rfl rfl
private theorem receipt_3_11_2360_1_join5 :
    phaseBlock (fastLayer (bank 3 11).shape 179818 2360 32 1 1 1 1) 0 810 = 1239479794830088271991583044 :=
  phaseBlock_append receipt_3_11_2360_1_join1 receipt_3_11_2360_1_join4 rfl rfl rfl

private theorem receipt_3_11_2360_1 : fastPhase (bank 3 11).shape 179818 2360 32 1 1 1 1 = 1239479794830088271991583044 :=
  phase_of_block (n := 810) (by decide +kernel) receipt_3_11_2360_1_join5

theorem receipt_3_11 : Checked (bank 3 11) 32 1 1 := by
  refine checked_from_values (bank 3 11) 32 1 1
    (P3_7_1.checked (bank 3 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3870_809)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_11_2359_0 receipt_3_11_2359_1 receipt_3_11_2360_0 receipt_3_11_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_12_2359_0_part0 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 0) 0 128 = 5238026383535905637951615591 := by decide +kernel
private theorem receipt_0_12_2359_0_part1 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 0) 128 128 = 4260963754497660576817200014 := by decide +kernel
private theorem receipt_0_12_2359_0_part2 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 0) 256 128 = 3348355294707772099558881242 := by decide +kernel
private theorem receipt_0_12_2359_0_part3 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 0) 384 128 = 2497995112038295845878073355 := by decide +kernel
private theorem receipt_0_12_2359_0_part4 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 0) 512 128 = 1707683778691791497274232590 := by decide +kernel
private theorem receipt_0_12_2359_0_part5 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 0) 640 128 = 975228415734354362510410619 := by decide +kernel
private theorem receipt_0_12_2359_0_part6 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 0) 768 123 = 298823754149286666507308687 := by decide +kernel
private theorem receipt_0_12_2359_0_join0 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 0) 128 256 = 7609319049205432676376081256 :=
  phaseBlock_append receipt_0_12_2359_0_part1 receipt_0_12_2359_0_part2 rfl rfl rfl
private theorem receipt_0_12_2359_0_join1 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 0) 0 384 = 12847345432741338314327696847 :=
  phaseBlock_append receipt_0_12_2359_0_part0 receipt_0_12_2359_0_join0 rfl rfl rfl
private theorem receipt_0_12_2359_0_join2 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 0) 384 256 = 4205678890730087343152305945 :=
  phaseBlock_append receipt_0_12_2359_0_part3 receipt_0_12_2359_0_part4 rfl rfl rfl
private theorem receipt_0_12_2359_0_join3 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 0) 640 251 = 1274052169883641029017719306 :=
  phaseBlock_append receipt_0_12_2359_0_part5 receipt_0_12_2359_0_part6 rfl rfl rfl
private theorem receipt_0_12_2359_0_join4 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 0) 384 507 = 5479731060613728372170025251 :=
  phaseBlock_append receipt_0_12_2359_0_join2 receipt_0_12_2359_0_join3 rfl rfl rfl
private theorem receipt_0_12_2359_0_join5 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 0) 0 891 = 18327076493355066686497722098 :=
  phaseBlock_append receipt_0_12_2359_0_join1 receipt_0_12_2359_0_join4 rfl rfl rfl

private theorem receipt_0_12_2359_0 : fastPhase (bank 0 12).shape 179818 2359 31 1 0 1 0 = 18327076493355066686497722098 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_0_12_2359_0_join5

private theorem receipt_0_12_2359_1_part0 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 1) 0 128 = 5230238641527756557211197671 := by decide +kernel
private theorem receipt_0_12_2359_1_part1 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 1) 128 128 = 4253670862945832398742975457 := by decide +kernel
private theorem receipt_0_12_2359_1_part2 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 1) 256 128 = 3341540589014195479468697015 := by decide +kernel
private theorem receipt_0_12_2359_1_part3 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 1) 384 128 = 2491641977404755783391043624 := by decide +kernel
private theorem receipt_0_12_2359_1_part4 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 1) 512 128 = 1701775650174768583590157018 := by decide +kernel
private theorem receipt_0_12_2359_1_part5 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 1) 640 128 = 969748778193986902319317809 := by decide +kernel
private theorem receipt_0_12_2359_1_part6 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 1) 768 123 = 293946564325721699213602570 := by decide +kernel
private theorem receipt_0_12_2359_1_join0 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 1) 128 256 = 7595211451960027878211672472 :=
  phaseBlock_append receipt_0_12_2359_1_part1 receipt_0_12_2359_1_part2 rfl rfl rfl
private theorem receipt_0_12_2359_1_join1 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 1) 0 384 = 12825450093487784435422870143 :=
  phaseBlock_append receipt_0_12_2359_1_part0 receipt_0_12_2359_1_join0 rfl rfl rfl
private theorem receipt_0_12_2359_1_join2 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 1) 384 256 = 4193417627579524366981200642 :=
  phaseBlock_append receipt_0_12_2359_1_part3 receipt_0_12_2359_1_part4 rfl rfl rfl
private theorem receipt_0_12_2359_1_join3 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 1) 640 251 = 1263695342519708601532920379 :=
  phaseBlock_append receipt_0_12_2359_1_part5 receipt_0_12_2359_1_part6 rfl rfl rfl
private theorem receipt_0_12_2359_1_join4 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 1) 384 507 = 5457112970099232968514121021 :=
  phaseBlock_append receipt_0_12_2359_1_join2 receipt_0_12_2359_1_join3 rfl rfl rfl
private theorem receipt_0_12_2359_1_join5 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2359 31 1 0 1 1) 0 891 = 18282563063587017403936991164 :=
  phaseBlock_append receipt_0_12_2359_1_join1 receipt_0_12_2359_1_join4 rfl rfl rfl

private theorem receipt_0_12_2359_1 : fastPhase (bank 0 12).shape 179818 2359 31 1 0 1 1 = 18282563063587017403936991164 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_0_12_2359_1_join5

private theorem receipt_0_12_2360_0_part0 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 0) 0 128 = 5238072967468954182509421930 := by decide +kernel
private theorem receipt_0_12_2360_0_part1 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 0) 128 128 = 4260998414332550676093255249 := by decide +kernel
private theorem receipt_0_12_2360_0_part2 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 0) 256 128 = 3348379878009440074717584588 := by decide +kernel
private theorem receipt_0_12_2360_0_part3 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 0) 384 128 = 2498011390680185019765721605 := by decide +kernel
private theorem receipt_0_12_2360_0_part4 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 0) 512 128 = 1707693443395740310380838014 := by decide +kernel
private theorem receipt_0_12_2360_0_part5 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 0) 640 128 = 975233074464085002510767849 := by decide +kernel
private theorem receipt_0_12_2360_0_part6 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 0) 768 123 = 298824934522927499606209489 := by decide +kernel
private theorem receipt_0_12_2360_0_join0 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 0) 128 256 = 7609378292341990750810839837 :=
  phaseBlock_append receipt_0_12_2360_0_part1 receipt_0_12_2360_0_part2 rfl rfl rfl
private theorem receipt_0_12_2360_0_join1 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 0) 0 384 = 12847451259810944933320261767 :=
  phaseBlock_append receipt_0_12_2360_0_part0 receipt_0_12_2360_0_join0 rfl rfl rfl
private theorem receipt_0_12_2360_0_join2 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 0) 384 256 = 4205704834075925330146559619 :=
  phaseBlock_append receipt_0_12_2360_0_part3 receipt_0_12_2360_0_part4 rfl rfl rfl
private theorem receipt_0_12_2360_0_join3 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 0) 640 251 = 1274058008987012502116977338 :=
  phaseBlock_append receipt_0_12_2360_0_part5 receipt_0_12_2360_0_part6 rfl rfl rfl
private theorem receipt_0_12_2360_0_join4 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 0) 384 507 = 5479762843062937832263536957 :=
  phaseBlock_append receipt_0_12_2360_0_join2 receipt_0_12_2360_0_join3 rfl rfl rfl
private theorem receipt_0_12_2360_0_join5 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 0) 0 891 = 18327214102873882765583798724 :=
  phaseBlock_append receipt_0_12_2360_0_join1 receipt_0_12_2360_0_join4 rfl rfl rfl

private theorem receipt_0_12_2360_0 : fastPhase (bank 0 12).shape 179818 2360 31 1 0 1 0 = 18327214102873882765583798724 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_0_12_2360_0_join5

private theorem receipt_0_12_2360_1_part0 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 1) 0 128 = 5230285168539515388866116246 := by decide +kernel
private theorem receipt_0_12_2360_1_part1 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 1) 128 128 = 4253705473165379904432298385 := by decide +kernel
private theorem receipt_0_12_2360_1_part2 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 1) 256 128 = 3341565129638853643830047315 := by decide +kernel
private theorem receipt_0_12_2360_1_part3 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 1) 384 128 = 2491658219934538054696811854 := by decide +kernel
private theorem receipt_0_12_2360_1_part4 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 1) 512 128 = 1701785284957156943351190655 := by decide +kernel
private theorem receipt_0_12_2360_1_part5 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 1) 640 128 = 969753412821141685694905548 := by decide +kernel
private theorem receipt_0_12_2360_1_part6 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 1) 768 123 = 293947726677363933046654622 := by decide +kernel
private theorem receipt_0_12_2360_1_join0 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 1) 128 256 = 7595270602804233548262345700 :=
  phaseBlock_append receipt_0_12_2360_1_part1 receipt_0_12_2360_1_part2 rfl rfl rfl
private theorem receipt_0_12_2360_1_join1 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 1) 0 384 = 12825555771343748937128461946 :=
  phaseBlock_append receipt_0_12_2360_1_part0 receipt_0_12_2360_1_join0 rfl rfl rfl
private theorem receipt_0_12_2360_1_join2 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 1) 384 256 = 4193443504891694998048002509 :=
  phaseBlock_append receipt_0_12_2360_1_part3 receipt_0_12_2360_1_part4 rfl rfl rfl
private theorem receipt_0_12_2360_1_join3 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 1) 640 251 = 1263701139498505618741560170 :=
  phaseBlock_append receipt_0_12_2360_1_part5 receipt_0_12_2360_1_part6 rfl rfl rfl
private theorem receipt_0_12_2360_1_join4 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 1) 384 507 = 5457144644390200616789562679 :=
  phaseBlock_append receipt_0_12_2360_1_join2 receipt_0_12_2360_1_join3 rfl rfl rfl
private theorem receipt_0_12_2360_1_join5 :
    phaseBlock (fastLayer (bank 0 12).shape 179818 2360 31 1 0 1 1) 0 891 = 18282700415733949553918024625 :=
  phaseBlock_append receipt_0_12_2360_1_join1 receipt_0_12_2360_1_join4 rfl rfl rfl

private theorem receipt_0_12_2360_1 : fastPhase (bank 0 12).shape 179818 2360 31 1 0 1 1 = 18282700415733949553918024625 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_0_12_2360_1_join5

theorem receipt_0_12 : Checked (bank 0 12) 31 0 1 := by
  refine checked_from_values (bank 0 12) 31 0 1
    (P3_7_1.checked (bank 0 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4255_890)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_12_2359_0 receipt_0_12_2359_1 receipt_0_12_2360_0 receipt_0_12_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_12_2359_0_part0 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 0) 0 128 = 4721214711749797971412941417 := by decide +kernel
private theorem receipt_1_12_2359_0_part1 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 0) 128 128 = 3837238032519095572824061607 := by decide +kernel
private theorem receipt_1_12_2359_0_part2 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 0) 256 128 = 3012778529881408927325394126 := by decide +kernel
private theorem receipt_1_12_2359_0_part3 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 0) 384 128 = 2245702986642540076728367063 := by decide +kernel
private theorem receipt_1_12_2359_0_part4 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 0) 512 128 = 1533890777339338846605345192 := by decide +kernel
private theorem receipt_1_12_2359_0_part5 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 0) 640 128 = 875233924931317054148399109 := by decide +kernel
private theorem receipt_1_12_2359_0_part6 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 0) 768 123 = 267978609239845337610259671 := by decide +kernel
private theorem receipt_1_12_2359_0_join0 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 0) 128 256 = 6850016562400504500149455733 :=
  phaseBlock_append receipt_1_12_2359_0_part1 receipt_1_12_2359_0_part2 rfl rfl rfl
private theorem receipt_1_12_2359_0_join1 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 0) 0 384 = 11571231274150302471562397150 :=
  phaseBlock_append receipt_1_12_2359_0_part0 receipt_1_12_2359_0_join0 rfl rfl rfl
private theorem receipt_1_12_2359_0_join2 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 0) 384 256 = 3779593763981878923333712255 :=
  phaseBlock_append receipt_1_12_2359_0_part3 receipt_1_12_2359_0_part4 rfl rfl rfl
private theorem receipt_1_12_2359_0_join3 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 0) 640 251 = 1143212534171162391758658780 :=
  phaseBlock_append receipt_1_12_2359_0_part5 receipt_1_12_2359_0_part6 rfl rfl rfl
private theorem receipt_1_12_2359_0_join4 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 0) 384 507 = 4922806298153041315092371035 :=
  phaseBlock_append receipt_1_12_2359_0_join2 receipt_1_12_2359_0_join3 rfl rfl rfl
private theorem receipt_1_12_2359_0_join5 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 0) 0 891 = 16494037572303343786654768185 :=
  phaseBlock_append receipt_1_12_2359_0_join1 receipt_1_12_2359_0_join4 rfl rfl rfl

private theorem receipt_1_12_2359_0 : fastPhase (bank 1 12).shape 179818 2359 31 1 0 2 0 = 16494037572303343786654768185 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_1_12_2359_0_join5

private theorem receipt_1_12_2359_1_part0 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 1) 0 128 = 4714163541870090969739135953 := by decide +kernel
private theorem receipt_1_12_2359_1_part1 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 1) 128 128 = 3830644515231329739299029703 := by decide +kernel
private theorem receipt_1_12_2359_1_part2 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 1) 256 128 = 3006626511937896598756465357 := by decide +kernel
private theorem receipt_1_12_2359_1_part3 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 1) 384 128 = 2239976411234220892678574826 := by decide +kernel
private theorem receipt_1_12_2359_1_part4 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 1) 512 128 = 1528573683996401914124528967 := by decide +kernel
private theorem receipt_1_12_2359_1_part5 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 1) 640 128 = 870310449327819078213574307 := by decide +kernel
private theorem receipt_1_12_2359_1_part6 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 1) 768 123 = 263603647518019488981861490 := by decide +kernel
private theorem receipt_1_12_2359_1_join0 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 1) 128 256 = 6837271027169226338055495060 :=
  phaseBlock_append receipt_1_12_2359_1_part1 receipt_1_12_2359_1_part2 rfl rfl rfl
private theorem receipt_1_12_2359_1_join1 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 1) 0 384 = 11551434569039317307794631013 :=
  phaseBlock_append receipt_1_12_2359_1_part0 receipt_1_12_2359_1_join0 rfl rfl rfl
private theorem receipt_1_12_2359_1_join2 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 1) 384 256 = 3768550095230622806803103793 :=
  phaseBlock_append receipt_1_12_2359_1_part3 receipt_1_12_2359_1_part4 rfl rfl rfl
private theorem receipt_1_12_2359_1_join3 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 1) 640 251 = 1133914096845838567195435797 :=
  phaseBlock_append receipt_1_12_2359_1_part5 receipt_1_12_2359_1_part6 rfl rfl rfl
private theorem receipt_1_12_2359_1_join4 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 1) 384 507 = 4902464192076461373998539590 :=
  phaseBlock_append receipt_1_12_2359_1_join2 receipt_1_12_2359_1_join3 rfl rfl rfl
private theorem receipt_1_12_2359_1_join5 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2359 31 1 0 2 1) 0 891 = 16453898761115778681793170603 :=
  phaseBlock_append receipt_1_12_2359_1_join1 receipt_1_12_2359_1_join4 rfl rfl rfl

private theorem receipt_1_12_2359_1 : fastPhase (bank 1 12).shape 179818 2359 31 1 0 2 1 = 16453898761115778681793170603 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_1_12_2359_1_join5

private theorem receipt_1_12_2360_0_part0 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 0) 0 128 = 4721256699714712325018626677 := by decide +kernel
private theorem receipt_1_12_2360_0_part1 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 0) 128 128 = 3837269245869121997209793668 := by decide +kernel
private theorem receipt_1_12_2360_0_part2 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 0) 256 128 = 3012800649586828204436661696 := by decide +kernel
private theorem receipt_1_12_2360_0_part3 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 0) 384 128 = 2245717621313332283198217507 := by decide +kernel
private theorem receipt_1_12_2360_0_part4 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 0) 512 128 = 1533899458551823420153594356 := by decide +kernel
private theorem receipt_1_12_2360_0_part5 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 0) 640 128 = 875238106037078085888248274 := by decide +kernel
private theorem receipt_1_12_2360_0_part6 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 0) 768 123 = 267979667784661623789317454 := by decide +kernel
private theorem receipt_1_12_2360_0_join0 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 0) 128 256 = 6850069895455950201646455364 :=
  phaseBlock_append receipt_1_12_2360_0_part1 receipt_1_12_2360_0_part2 rfl rfl rfl
private theorem receipt_1_12_2360_0_join1 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 0) 0 384 = 11571326595170662526665082041 :=
  phaseBlock_append receipt_1_12_2360_0_part0 receipt_1_12_2360_0_join0 rfl rfl rfl
private theorem receipt_1_12_2360_0_join2 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 0) 384 256 = 3779617079865155703351811863 :=
  phaseBlock_append receipt_1_12_2360_0_part3 receipt_1_12_2360_0_part4 rfl rfl rfl
private theorem receipt_1_12_2360_0_join3 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 0) 640 251 = 1143217773821739709677565728 :=
  phaseBlock_append receipt_1_12_2360_0_part5 receipt_1_12_2360_0_part6 rfl rfl rfl
private theorem receipt_1_12_2360_0_join4 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 0) 384 507 = 4922834853686895413029377591 :=
  phaseBlock_append receipt_1_12_2360_0_join2 receipt_1_12_2360_0_join3 rfl rfl rfl
private theorem receipt_1_12_2360_0_join5 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 0) 0 891 = 16494161448857557939694459632 :=
  phaseBlock_append receipt_1_12_2360_0_join1 receipt_1_12_2360_0_join4 rfl rfl rfl

private theorem receipt_1_12_2360_0 : fastPhase (bank 1 12).shape 179818 2360 31 1 0 2 0 = 16494161448857557939694459632 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_1_12_2360_0_join5

private theorem receipt_1_12_2360_1_part0 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 1) 0 128 = 4714205478246567936112077108 := by decide +kernel
private theorem receipt_1_12_2360_1_part1 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 1) 128 128 = 3830675683689207993461288892 := by decide +kernel
private theorem receipt_1_12_2360_1_part2 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 1) 256 128 = 3006648593094092085667388361 := by decide +kernel
private theorem receipt_1_12_2360_1_part3 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 1) 384 128 = 2239991013341422872458401083 := by decide +kernel
private theorem receipt_1_12_2360_1_part4 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 1) 512 128 = 1528582338274160067719393385 := by decide +kernel
private theorem receipt_1_12_2360_1_part5 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 1) 640 128 = 870314608774822583068702209 := by decide +kernel
private theorem receipt_1_12_2360_1_part6 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 1) 768 123 = 263604689895967147763821236 := by decide +kernel
private theorem receipt_1_12_2360_1_join0 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 1) 128 256 = 6837324276783300079128677253 :=
  phaseBlock_append receipt_1_12_2360_1_part1 receipt_1_12_2360_1_part2 rfl rfl rfl
private theorem receipt_1_12_2360_1_join1 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 1) 0 384 = 11551529755029868015240754361 :=
  phaseBlock_append receipt_1_12_2360_1_part0 receipt_1_12_2360_1_join0 rfl rfl rfl
private theorem receipt_1_12_2360_1_join2 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 1) 384 256 = 3768573351615582940177794468 :=
  phaseBlock_append receipt_1_12_2360_1_part3 receipt_1_12_2360_1_part4 rfl rfl rfl
private theorem receipt_1_12_2360_1_join3 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 1) 640 251 = 1133919298670789730832523445 :=
  phaseBlock_append receipt_1_12_2360_1_part5 receipt_1_12_2360_1_part6 rfl rfl rfl
private theorem receipt_1_12_2360_1_join4 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 1) 384 507 = 4902492650286372671010317913 :=
  phaseBlock_append receipt_1_12_2360_1_join2 receipt_1_12_2360_1_join3 rfl rfl rfl
private theorem receipt_1_12_2360_1_join5 :
    phaseBlock (fastLayer (bank 1 12).shape 179818 2360 31 1 0 2 1) 0 891 = 16454022405316240686251072274 :=
  phaseBlock_append receipt_1_12_2360_1_join1 receipt_1_12_2360_1_join4 rfl rfl rfl

private theorem receipt_1_12_2360_1 : fastPhase (bank 1 12).shape 179818 2360 31 1 0 2 1 = 16454022405316240686251072274 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_1_12_2360_1_join5

theorem receipt_1_12 : Checked (bank 1 12) 31 0 2 := by
  refine checked_from_values (bank 1 12) 31 0 2
    (P3_7_1.checked (bank 1 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4255_890)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_12_2359_0 receipt_1_12_2359_1 receipt_1_12_2360_0 receipt_1_12_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_12_2359_0_part0 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 0) 0 128 = 2566992499620178669054878720 := by decide +kernel
private theorem receipt_2_12_2359_0_part1 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 0) 128 128 = 2073546078246927338452755456 := by decide +kernel
private theorem receipt_2_12_2359_0_part2 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 0) 256 128 = 1617988106630817799293363200 := by decide +kernel
private theorem receipt_2_12_2359_0_part3 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 0) 384 128 = 1198574232054546006739035136 := by decide +kernel
private theorem receipt_2_12_2359_0_part4 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 0) 512 128 = 813596852881844152128392670 := by decide +kernel
private theorem receipt_2_12_2359_0_part5 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 0) 640 128 = 461385362515284347962322600 := by decide +kernel
private theorem receipt_2_12_2359_0_part6 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 0) 768 123 = 140481834403852046802631802 := by decide +kernel
private theorem receipt_2_12_2359_0_join0 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 0) 128 256 = 3691534184877745137746118656 :=
  phaseBlock_append receipt_2_12_2359_0_part1 receipt_2_12_2359_0_part2 rfl rfl rfl
private theorem receipt_2_12_2359_0_join1 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 0) 0 384 = 6258526684497923806800997376 :=
  phaseBlock_append receipt_2_12_2359_0_part0 receipt_2_12_2359_0_join0 rfl rfl rfl
private theorem receipt_2_12_2359_0_join2 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 0) 384 256 = 2012171084936390158867427806 :=
  phaseBlock_append receipt_2_12_2359_0_part3 receipt_2_12_2359_0_part4 rfl rfl rfl
private theorem receipt_2_12_2359_0_join3 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 0) 640 251 = 601867196919136394764954402 :=
  phaseBlock_append receipt_2_12_2359_0_part5 receipt_2_12_2359_0_part6 rfl rfl rfl
private theorem receipt_2_12_2359_0_join4 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 0) 384 507 = 2614038281855526553632382208 :=
  phaseBlock_append receipt_2_12_2359_0_join2 receipt_2_12_2359_0_join3 rfl rfl rfl
private theorem receipt_2_12_2359_0_join5 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 0) 0 891 = 8872564966353450360433379584 :=
  phaseBlock_append receipt_2_12_2359_0_join1 receipt_2_12_2359_0_join4 rfl rfl rfl

private theorem receipt_2_12_2359_0 : fastPhase (bank 2 12).shape 179818 2359 31 1 0 7 0 = 8872564966353450360433379584 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_2_12_2359_0_join5

private theorem receipt_2_12_2359_1_part0 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 1) 0 128 = 2563035313650856272056001600 := by decide +kernel
private theorem receipt_2_12_2359_1_part1 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 1) 128 128 = 2069883095187150343101482048 := by decide +kernel
private theorem receipt_2_12_2359_1_part2 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 1) 256 128 = 1614605942433324583051879488 := by decide +kernel
private theorem receipt_2_12_2359_1_part3 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 1) 384 128 = 1195459784008118760546026560 := by decide +kernel
private theorem receipt_2_12_2359_1_part4 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 1) 512 128 = 810737297166769717995400894 := by decide +kernel
private theorem receipt_2_12_2359_1_part5 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 1) 640 128 = 458768148146444522978578284 := by decide +kernel
private theorem receipt_2_12_2359_1_part6 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 1) 768 123 = 138183758462236914422894560 := by decide +kernel
private theorem receipt_2_12_2359_1_join0 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 1) 128 256 = 3684489037620474926153361536 :=
  phaseBlock_append receipt_2_12_2359_1_part1 receipt_2_12_2359_1_part2 rfl rfl rfl
private theorem receipt_2_12_2359_1_join1 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 1) 0 384 = 6247524351271331198209363136 :=
  phaseBlock_append receipt_2_12_2359_1_part0 receipt_2_12_2359_1_join0 rfl rfl rfl
private theorem receipt_2_12_2359_1_join2 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 1) 384 256 = 2006197081174888478541427454 :=
  phaseBlock_append receipt_2_12_2359_1_part3 receipt_2_12_2359_1_part4 rfl rfl rfl
private theorem receipt_2_12_2359_1_join3 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 1) 640 251 = 596951906608681437401472844 :=
  phaseBlock_append receipt_2_12_2359_1_part5 receipt_2_12_2359_1_part6 rfl rfl rfl
private theorem receipt_2_12_2359_1_join4 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 1) 384 507 = 2603148987783569915942900298 :=
  phaseBlock_append receipt_2_12_2359_1_join2 receipt_2_12_2359_1_join3 rfl rfl rfl
private theorem receipt_2_12_2359_1_join5 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2359 31 1 0 7 1) 0 891 = 8850673339054901114152263434 :=
  phaseBlock_append receipt_2_12_2359_1_join1 receipt_2_12_2359_1_join4 rfl rfl rfl

private theorem receipt_2_12_2359_1 : fastPhase (bank 2 12).shape 179818 2359 31 1 0 7 1 = 8850673339054901114152263434 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_2_12_2359_1_join5

private theorem receipt_2_12_2360_0_part0 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 0) 0 128 = 2567015115387745966475753760 := by decide +kernel
private theorem receipt_2_12_2360_0_part1 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 0) 128 128 = 2073562815861958262891120928 := by decide +kernel
private theorem receipt_2_12_2360_0_part2 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 0) 256 128 = 1617999919365788282293082400 := by decide +kernel
private theorem receipt_2_12_2360_0_part3 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 0) 384 128 = 1198582017866633492346317088 := by decide +kernel
private theorem receipt_2_12_2360_0_part4 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 0) 512 128 = 813601454766387399286946013 := by decide +kernel
private theorem receipt_2_12_2360_0_part5 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 0) 640 128 = 461387566828041676083382895 := by decide +kernel
private theorem receipt_2_12_2360_0_part6 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 0) 768 123 = 140482389366516296623263415 := by decide +kernel
private theorem receipt_2_12_2360_0_join0 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 0) 128 256 = 3691562735227746545184203328 :=
  phaseBlock_append receipt_2_12_2360_0_part1 receipt_2_12_2360_0_part2 rfl rfl rfl
private theorem receipt_2_12_2360_0_join1 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 0) 0 384 = 6258577850615492511659957088 :=
  phaseBlock_append receipt_2_12_2360_0_part0 receipt_2_12_2360_0_join0 rfl rfl rfl
private theorem receipt_2_12_2360_0_join2 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 0) 384 256 = 2012183472633020891633263101 :=
  phaseBlock_append receipt_2_12_2360_0_part3 receipt_2_12_2360_0_part4 rfl rfl rfl
private theorem receipt_2_12_2360_0_join3 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 0) 640 251 = 601869956194557972706646310 :=
  phaseBlock_append receipt_2_12_2360_0_part5 receipt_2_12_2360_0_part6 rfl rfl rfl
private theorem receipt_2_12_2360_0_join4 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 0) 384 507 = 2614053428827578864339909411 :=
  phaseBlock_append receipt_2_12_2360_0_join2 receipt_2_12_2360_0_join3 rfl rfl rfl
private theorem receipt_2_12_2360_0_join5 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 0) 0 891 = 8872631279443071375999866499 :=
  phaseBlock_append receipt_2_12_2360_0_join1 receipt_2_12_2360_0_join4 rfl rfl rfl

private theorem receipt_2_12_2360_0 : fastPhase (bank 2 12).shape 179818 2360 31 1 0 7 0 = 8872631279443071375999866499 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_2_12_2360_0_join5

private theorem receipt_2_12_2360_1_part0 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 1) 0 128 = 2563057900542065993023093920 := by decide +kernel
private theorem receipt_2_12_2360_1_part1 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 1) 128 128 = 2069899807921376586133449888 := by decide +kernel
private theorem receipt_2_12_2360_1_part2 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 1) 256 128 = 1614617734010016933075442848 := by decide +kernel
private theorem receipt_2_12_2360_1_part3 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 1) 384 128 = 1195467552118338394457246880 := by decide +kernel
private theorem receipt_2_12_2360_1_part4 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 1) 512 128 = 810741884549995307230466169 := by decide +kernel
private theorem receipt_2_12_2360_1_part5 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 1) 640 128 = 458770340936310021290175873 := by decide +kernel
private theorem receipt_2_12_2360_1_part6 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 1) 768 123 = 138184304930174160223185542 := by decide +kernel
private theorem receipt_2_12_2360_1_join0 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 1) 128 256 = 3684517541931393519208892736 :=
  phaseBlock_append receipt_2_12_2360_1_part1 receipt_2_12_2360_1_part2 rfl rfl rfl
private theorem receipt_2_12_2360_1_join1 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 1) 0 384 = 6247575442473459512231986656 :=
  phaseBlock_append receipt_2_12_2360_1_part0 receipt_2_12_2360_1_join0 rfl rfl rfl
private theorem receipt_2_12_2360_1_join2 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 1) 384 256 = 2006209436668333701687713049 :=
  phaseBlock_append receipt_2_12_2360_1_part3 receipt_2_12_2360_1_part4 rfl rfl rfl
private theorem receipt_2_12_2360_1_join3 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 1) 640 251 = 596954645866484181513361415 :=
  phaseBlock_append receipt_2_12_2360_1_part5 receipt_2_12_2360_1_part6 rfl rfl rfl
private theorem receipt_2_12_2360_1_join4 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 1) 384 507 = 2603164082534817883201074464 :=
  phaseBlock_append receipt_2_12_2360_1_join2 receipt_2_12_2360_1_join3 rfl rfl rfl
private theorem receipt_2_12_2360_1_join5 :
    phaseBlock (fastLayer (bank 2 12).shape 179818 2360 31 1 0 7 1) 0 891 = 8850739525008277395433061120 :=
  phaseBlock_append receipt_2_12_2360_1_join1 receipt_2_12_2360_1_join4 rfl rfl rfl

private theorem receipt_2_12_2360_1 : fastPhase (bank 2 12).shape 179818 2360 31 1 0 7 1 = 8850739525008277395433061120 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_2_12_2360_1_join5

theorem receipt_2_12 : Checked (bank 2 12) 31 0 7 := by
  refine checked_from_values (bank 2 12) 31 0 7
    (P3_7_1.checked (bank 2 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4235_890)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_12_2359_0 receipt_2_12_2359_1 receipt_2_12_2360_0 receipt_2_12_2360_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_12_2359_0_part0 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 0) 0 128 = 473279862205441242332640608 := by decide +kernel
private theorem receipt_3_12_2359_0_part1 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 0) 128 128 = 385970195806973950209779040 := by decide +kernel
private theorem receipt_3_12_2359_0_part2 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 0) 256 128 = 304251393533293143783576928 := by decide +kernel
private theorem receipt_3_12_2359_0_part3 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 0) 384 128 = 228350435242021809516889440 := by decide +kernel
private theorem receipt_3_12_2359_0_part4 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 0) 512 128 = 158491559809689204918220128 := by decide +kernel
private theorem receipt_3_12_2359_0_part5 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 0) 640 128 = 94896274586079502066656608 := by decide +kernel
private theorem receipt_3_12_2359_0_part6 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 0) 768 128 = 37783364848580431136806240 := by decide +kernel
private theorem receipt_3_12_2359_0_part7 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 0) 896 29 = 1311152418143549984738763 := by decide +kernel
private theorem receipt_3_12_2359_0_join0 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 0) 0 256 = 859250058012415192542419648 :=
  phaseBlock_append receipt_3_12_2359_0_part0 receipt_3_12_2359_0_part1 rfl rfl rfl
private theorem receipt_3_12_2359_0_join1 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 0) 256 256 = 532601828775314953300466368 :=
  phaseBlock_append receipt_3_12_2359_0_part2 receipt_3_12_2359_0_part3 rfl rfl rfl
private theorem receipt_3_12_2359_0_join2 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 0) 0 512 = 1391851886787730145842886016 :=
  phaseBlock_append receipt_3_12_2359_0_join0 receipt_3_12_2359_0_join1 rfl rfl rfl
private theorem receipt_3_12_2359_0_join3 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 0) 512 256 = 253387834395768706984876736 :=
  phaseBlock_append receipt_3_12_2359_0_part4 receipt_3_12_2359_0_part5 rfl rfl rfl
private theorem receipt_3_12_2359_0_join4 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 0) 768 157 = 39094517266723981121545003 :=
  phaseBlock_append receipt_3_12_2359_0_part6 receipt_3_12_2359_0_part7 rfl rfl rfl
private theorem receipt_3_12_2359_0_join5 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 0) 512 413 = 292482351662492688106421739 :=
  phaseBlock_append receipt_3_12_2359_0_join3 receipt_3_12_2359_0_join4 rfl rfl rfl
private theorem receipt_3_12_2359_0_join6 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 0) 0 925 = 1684334238450222833949307755 :=
  phaseBlock_append receipt_3_12_2359_0_join2 receipt_3_12_2359_0_join5 rfl rfl rfl

private theorem receipt_3_12_2359_0 : fastPhase (bank 3 12).shape 179818 2359 31 1 1 1 0 = 1684334238450222833949307755 :=
  phase_of_block (n := 925) (by decide +kernel) receipt_3_12_2359_0_join6

private theorem receipt_3_12_2359_1_part0 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 1) 0 128 = 472585650103495907215375712 := by decide +kernel
private theorem receipt_3_12_2359_1_part1 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 1) 128 128 = 385317023863689726742269280 := by decide +kernel
private theorem receipt_3_12_2359_1_part2 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 1) 256 128 = 303641193409546074773888352 := by decide +kernel
private theorem receipt_3_12_2359_1_part3 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 1) 384 128 = 227785116029364054285790560 := by decide +kernel
private theorem receipt_3_12_2359_1_part4 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 1) 512 128 = 157973008107129104497884512 := by decide +kernel
private theorem receipt_3_12_2359_1_part5 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 1) 640 128 = 94426354576861644399365472 := by decide +kernel
private theorem receipt_3_12_2359_1_part6 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 1) 768 128 = 37363918376965716273651040 := by decide +kernel
private theorem receipt_3_12_2359_1_part7 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 1) 896 29 = 1223322786180343898683767 := by decide +kernel
private theorem receipt_3_12_2359_1_join0 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 1) 0 256 = 857902673967185633957644992 :=
  phaseBlock_append receipt_3_12_2359_1_part0 receipt_3_12_2359_1_part1 rfl rfl rfl
private theorem receipt_3_12_2359_1_join1 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 1) 256 256 = 531426309438910129059678912 :=
  phaseBlock_append receipt_3_12_2359_1_part2 receipt_3_12_2359_1_part3 rfl rfl rfl
private theorem receipt_3_12_2359_1_join2 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 1) 0 512 = 1389328983406095763017323904 :=
  phaseBlock_append receipt_3_12_2359_1_join0 receipt_3_12_2359_1_join1 rfl rfl rfl
private theorem receipt_3_12_2359_1_join3 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 1) 512 256 = 252399362683990748897249984 :=
  phaseBlock_append receipt_3_12_2359_1_part4 receipt_3_12_2359_1_part5 rfl rfl rfl
private theorem receipt_3_12_2359_1_join4 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 1) 768 157 = 38587241163146060172334807 :=
  phaseBlock_append receipt_3_12_2359_1_part6 receipt_3_12_2359_1_part7 rfl rfl rfl
private theorem receipt_3_12_2359_1_join5 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 1) 512 413 = 290986603847136809069584791 :=
  phaseBlock_append receipt_3_12_2359_1_join3 receipt_3_12_2359_1_join4 rfl rfl rfl
private theorem receipt_3_12_2359_1_join6 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2359 31 1 1 1 1) 0 925 = 1680315587253232572086908695 :=
  phaseBlock_append receipt_3_12_2359_1_join2 receipt_3_12_2359_1_join5 rfl rfl rfl

private theorem receipt_3_12_2359_1 : fastPhase (bank 3 12).shape 179818 2359 31 1 1 1 1 = 1680315587253232572086908695 :=
  phase_of_block (n := 925) (by decide +kernel) receipt_3_12_2359_1_join6

private theorem receipt_3_12_2360_0_part0 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 0) 0 128 = 473283939176506932391880928 := by decide +kernel
private theorem receipt_3_12_2360_0_part1 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 0) 128 128 = 385973040122052486453876960 := by decide +kernel
private theorem receipt_3_12_2360_0_part2 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 0) 256 128 = 304253266456325477996038368 := by decide +kernel
private theorem receipt_3_12_2360_0_part3 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 0) 384 128 = 228351571004530989948123360 := by decide +kernel
private theorem receipt_3_12_2360_0_part4 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 0) 512 128 = 158492165881218661435009248 := by decide +kernel
private theorem receipt_3_12_2360_0_part5 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 0) 640 128 = 94896531943751721999407328 := by decide +kernel
private theorem receipt_3_12_2360_0_part6 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 0) 768 128 = 37783428245776025824577760 := by decide +kernel
private theorem receipt_3_12_2360_0_part7 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 0) 896 29 = 1311153627716085528508203 := by decide +kernel
private theorem receipt_3_12_2360_0_join0 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 0) 0 256 = 859256979298559418845757888 :=
  phaseBlock_append receipt_3_12_2360_0_part0 receipt_3_12_2360_0_part1 rfl rfl rfl
private theorem receipt_3_12_2360_0_join1 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 0) 256 256 = 532604837460856467944161728 :=
  phaseBlock_append receipt_3_12_2360_0_part2 receipt_3_12_2360_0_part3 rfl rfl rfl
private theorem receipt_3_12_2360_0_join2 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 0) 0 512 = 1391861816759415886789919616 :=
  phaseBlock_append receipt_3_12_2360_0_join0 receipt_3_12_2360_0_join1 rfl rfl rfl
private theorem receipt_3_12_2360_0_join3 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 0) 512 256 = 253388697824970383434416576 :=
  phaseBlock_append receipt_3_12_2360_0_part4 receipt_3_12_2360_0_part5 rfl rfl rfl
private theorem receipt_3_12_2360_0_join4 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 0) 768 157 = 39094581873492111353085963 :=
  phaseBlock_append receipt_3_12_2360_0_part6 receipt_3_12_2360_0_part7 rfl rfl rfl
private theorem receipt_3_12_2360_0_join5 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 0) 512 413 = 292483279698462494787502539 :=
  phaseBlock_append receipt_3_12_2360_0_join3 receipt_3_12_2360_0_join4 rfl rfl rfl
private theorem receipt_3_12_2360_0_join6 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 0) 0 925 = 1684345096457878381577422155 :=
  phaseBlock_append receipt_3_12_2360_0_join2 receipt_3_12_2360_0_join5 rfl rfl rfl

private theorem receipt_3_12_2360_0 : fastPhase (bank 3 12).shape 179818 2360 31 1 1 1 0 = 1684345096457878381577422155 :=
  phase_of_block (n := 925) (by decide +kernel) receipt_3_12_2360_0_join6

private theorem receipt_3_12_2360_1_part0 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 1) 0 128 = 472589720165856551825091168 := by decide +kernel
private theorem receipt_3_12_2360_1_part1 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 1) 128 128 = 385319862674103390458387040 := by decide +kernel
private theorem receipt_3_12_2360_1_part2 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 1) 256 128 = 303643062082337839901870688 := by decide +kernel
private theorem receipt_3_12_2360_1_part3 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 1) 384 128 = 227786248648083053247232608 := by decide +kernel
private theorem receipt_3_12_2360_1_part4 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 1) 512 128 = 157973611994981169982892640 := by decide +kernel
private theorem receipt_3_12_2360_1_part5 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 1) 640 128 = 94426610566262350216714848 := by decide +kernel
private theorem receipt_3_12_2360_1_part6 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 1) 768 128 = 37363981078213808898722400 := by decide +kernel
private theorem receipt_3_12_2360_1_part7 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 1) 896 29 = 1223323916873917874910363 := by decide +kernel
private theorem receipt_3_12_2360_1_join0 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 1) 0 256 = 857909582839959942283478208 :=
  phaseBlock_append receipt_3_12_2360_1_part0 receipt_3_12_2360_1_part1 rfl rfl rfl
private theorem receipt_3_12_2360_1_join1 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 1) 256 256 = 531429310730420893149103296 :=
  phaseBlock_append receipt_3_12_2360_1_part2 receipt_3_12_2360_1_part3 rfl rfl rfl
private theorem receipt_3_12_2360_1_join2 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 1) 0 512 = 1389338893570380835432581504 :=
  phaseBlock_append receipt_3_12_2360_1_join0 receipt_3_12_2360_1_join1 rfl rfl rfl
private theorem receipt_3_12_2360_1_join3 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 1) 512 256 = 252400222561243520199607488 :=
  phaseBlock_append receipt_3_12_2360_1_part4 receipt_3_12_2360_1_part5 rfl rfl rfl
private theorem receipt_3_12_2360_1_join4 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 1) 768 157 = 38587304995087726773632763 :=
  phaseBlock_append receipt_3_12_2360_1_part6 receipt_3_12_2360_1_part7 rfl rfl rfl
private theorem receipt_3_12_2360_1_join5 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 1) 512 413 = 290987527556331246973240251 :=
  phaseBlock_append receipt_3_12_2360_1_join3 receipt_3_12_2360_1_join4 rfl rfl rfl
private theorem receipt_3_12_2360_1_join6 :
    phaseBlock (fastLayer (bank 3 12).shape 179818 2360 31 1 1 1 1) 0 925 = 1680326421126712082405821755 :=
  phaseBlock_append receipt_3_12_2360_1_join2 receipt_3_12_2360_1_join5 rfl rfl rfl

private theorem receipt_3_12_2360_1 : fastPhase (bank 3 12).shape 179818 2360 31 1 1 1 1 = 1680326421126712082405821755 :=
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
    (word : K1.I → K1_14.L) (lo : 2359 ≤ h) (hi : h ≤ 33579) (rect : Fin 4)
    (i : Fin 2) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group4_stage i)).shape
      (cutoff h rect (group4_stage i)), ¬ G∣Q :=
  (group4_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group4_avoids

end Lower6960.RescueSource
