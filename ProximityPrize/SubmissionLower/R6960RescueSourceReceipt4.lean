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

private theorem receipt_0_11_2402_0_part0 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 0) 0 128 = 8720464910251865629394828512 := by decide +kernel
private theorem receipt_0_11_2402_0_part1 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 0) 128 128 = 7350772669609222327742762208 := by decide +kernel
private theorem receipt_0_11_2402_0_part2 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 0) 256 128 = 6059728569822439332259208416 := by decide +kernel
private theorem receipt_0_11_2402_0_part3 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 0) 384 128 = 4844997146270551976837197024 := by decide +kernel
private theorem receipt_0_11_2402_0_part4 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 0) 512 128 = 3704249660418591389388356832 := by decide +kernel
private theorem receipt_0_11_2402_0_part5 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 0) 640 128 = 2635164297536781308856488053 := by decide +kernel
private theorem receipt_0_11_2402_0_part6 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 0) 768 128 = 1635427913174820948248803537 := by decide +kernel
private theorem receipt_0_11_2402_0_part7 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 0) 896 128 = 702728483308687498360507587 := by decide +kernel
private theorem receipt_0_11_2402_0_part8 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 0) 1024 38 = 38672956156075053069536881 := by decide +kernel
private theorem receipt_0_11_2402_0_join0 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 0) 0 256 = 16071237579861087957137590720 :=
  phaseBlock_append receipt_0_11_2402_0_part0 receipt_0_11_2402_0_part1 rfl rfl rfl
private theorem receipt_0_11_2402_0_join1 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 0) 256 256 = 10904725716092991309096405440 :=
  phaseBlock_append receipt_0_11_2402_0_part2 receipt_0_11_2402_0_part3 rfl rfl rfl
private theorem receipt_0_11_2402_0_join2 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 0) 0 512 = 26975963295954079266233996160 :=
  phaseBlock_append receipt_0_11_2402_0_join0 receipt_0_11_2402_0_join1 rfl rfl rfl
private theorem receipt_0_11_2402_0_join3 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 0) 512 256 = 6339413957955372698244844885 :=
  phaseBlock_append receipt_0_11_2402_0_part4 receipt_0_11_2402_0_part5 rfl rfl rfl
private theorem receipt_0_11_2402_0_join4 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 0) 896 166 = 741401439464762551430044468 :=
  phaseBlock_append receipt_0_11_2402_0_part7 receipt_0_11_2402_0_part8 rfl rfl rfl
private theorem receipt_0_11_2402_0_join5 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 0) 768 294 = 2376829352639583499678848005 :=
  phaseBlock_append receipt_0_11_2402_0_part6 receipt_0_11_2402_0_join4 rfl rfl rfl
private theorem receipt_0_11_2402_0_join6 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 0) 512 550 = 8716243310594956197923692890 :=
  phaseBlock_append receipt_0_11_2402_0_join3 receipt_0_11_2402_0_join5 rfl rfl rfl
private theorem receipt_0_11_2402_0_join7 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 0) 0 1062 = 35692206606549035464157689050 :=
  phaseBlock_append receipt_0_11_2402_0_join2 receipt_0_11_2402_0_join6 rfl rfl rfl

private theorem receipt_0_11_2402_0 : fastPhase (bank 0 11).shape 179798 2402 32 1 0 1 0 = 35692206606549035464157689050 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_0_11_2402_0_join7

private theorem receipt_0_11_2402_1_part0 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 1) 0 128 = 8709602119983215266701996000 := by decide +kernel
private theorem receipt_0_11_2402_1_part1 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 1) 128 128 = 7340512274018511064968151008 := by decide +kernel
private theorem receipt_0_11_2402_1_part2 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 1) 256 128 = 6050052895846014310699962336 := by decide +kernel
private theorem receipt_0_11_2402_1_part3 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 1) 384 128 = 4835888572100946111778709472 := by decide +kernel
private theorem receipt_0_11_2402_1_part4 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 1) 512 128 = 3695690615456352185143439328 := by decide +kernel
private theorem receipt_0_11_2402_1_part5 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 1) 640 128 = 2627137261687129170543831468 := by decide +kernel
private theorem receipt_0_11_2402_1_part6 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 1) 768 128 = 1627915406319628795299431403 := by decide +kernel
private theorem receipt_0_11_2402_1_part7 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 1) 896 128 = 695713067387416428915257055 := by decide +kernel
private theorem receipt_0_11_2402_1_part8 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 1) 1024 38 = 36683383027610483260146934 := by decide +kernel
private theorem receipt_0_11_2402_1_join0 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 1) 0 256 = 16050114394001726331670147008 :=
  phaseBlock_append receipt_0_11_2402_1_part0 receipt_0_11_2402_1_part1 rfl rfl rfl
private theorem receipt_0_11_2402_1_join1 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 1) 256 256 = 10885941467946960422478671808 :=
  phaseBlock_append receipt_0_11_2402_1_part2 receipt_0_11_2402_1_part3 rfl rfl rfl
private theorem receipt_0_11_2402_1_join2 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 1) 0 512 = 26936055861948686754148818816 :=
  phaseBlock_append receipt_0_11_2402_1_join0 receipt_0_11_2402_1_join1 rfl rfl rfl
private theorem receipt_0_11_2402_1_join3 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 1) 512 256 = 6322827877143481355687270796 :=
  phaseBlock_append receipt_0_11_2402_1_part4 receipt_0_11_2402_1_part5 rfl rfl rfl
private theorem receipt_0_11_2402_1_join4 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 1) 896 166 = 732396450415026912175403989 :=
  phaseBlock_append receipt_0_11_2402_1_part7 receipt_0_11_2402_1_part8 rfl rfl rfl
private theorem receipt_0_11_2402_1_join5 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 1) 768 294 = 2360311856734655707474835392 :=
  phaseBlock_append receipt_0_11_2402_1_part6 receipt_0_11_2402_1_join4 rfl rfl rfl
private theorem receipt_0_11_2402_1_join6 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 1) 512 550 = 8683139733878137063162106188 :=
  phaseBlock_append receipt_0_11_2402_1_join3 receipt_0_11_2402_1_join5 rfl rfl rfl
private theorem receipt_0_11_2402_1_join7 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2402 32 1 0 1 1) 0 1062 = 35619195595826823817310925004 :=
  phaseBlock_append receipt_0_11_2402_1_join2 receipt_0_11_2402_1_join6 rfl rfl rfl

private theorem receipt_0_11_2402_1 : fastPhase (bank 0 11).shape 179798 2402 32 1 0 1 1 = 35619195595826823817310925004 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_0_11_2402_1_join7

private theorem receipt_0_11_2403_0_part0 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 0) 0 128 = 8720542918699534325587811392 := by decide +kernel
private theorem receipt_0_11_2403_0_part1 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 0) 128 128 = 7350833725626684238539766848 := by decide +kernel
private theorem receipt_0_11_2403_0_part2 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 0) 256 128 = 6059774875594555725503061056 := by decide +kernel
private theorem receipt_0_11_2403_0_part3 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 0) 384 128 = 4845030823537427097345981504 := by decide +kernel
private theorem receipt_0_11_2403_0_part4 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 0) 512 128 = 3704272750709747991627373632 := by decide +kernel
private theorem receipt_0_11_2403_0_part5 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 0) 640 128 = 2635178756484561071809915402 := by decide +kernel
private theorem receipt_0_11_2403_0_part6 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 0) 768 128 = 1635435609050810192297689181 := by decide +kernel
private theorem receipt_0_11_2403_0_part7 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 0) 896 128 = 702731243144911725228431755 := by decide +kernel
private theorem receipt_0_11_2403_0_part8 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 0) 1024 38 = 38673084780526728180750973 := by decide +kernel
private theorem receipt_0_11_2403_0_join0 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 0) 0 256 = 16071376644326218564127578240 :=
  phaseBlock_append receipt_0_11_2403_0_part0 receipt_0_11_2403_0_part1 rfl rfl rfl
private theorem receipt_0_11_2403_0_join1 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 0) 256 256 = 10904805699131982822849042560 :=
  phaseBlock_append receipt_0_11_2403_0_part2 receipt_0_11_2403_0_part3 rfl rfl rfl
private theorem receipt_0_11_2403_0_join2 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 0) 0 512 = 26976182343458201386976620800 :=
  phaseBlock_append receipt_0_11_2403_0_join0 receipt_0_11_2403_0_join1 rfl rfl rfl
private theorem receipt_0_11_2403_0_join3 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 0) 512 256 = 6339451507194309063437289034 :=
  phaseBlock_append receipt_0_11_2403_0_part4 receipt_0_11_2403_0_part5 rfl rfl rfl
private theorem receipt_0_11_2403_0_join4 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 0) 896 166 = 741404327925438453409182728 :=
  phaseBlock_append receipt_0_11_2403_0_part7 receipt_0_11_2403_0_part8 rfl rfl rfl
private theorem receipt_0_11_2403_0_join5 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 0) 768 294 = 2376839936976248645706871909 :=
  phaseBlock_append receipt_0_11_2403_0_part6 receipt_0_11_2403_0_join4 rfl rfl rfl
private theorem receipt_0_11_2403_0_join6 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 0) 512 550 = 8716291444170557709144160943 :=
  phaseBlock_append receipt_0_11_2403_0_join3 receipt_0_11_2403_0_join5 rfl rfl rfl
private theorem receipt_0_11_2403_0_join7 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 0) 0 1062 = 35692473787628759096120781743 :=
  phaseBlock_append receipt_0_11_2403_0_join2 receipt_0_11_2403_0_join6 rfl rfl rfl

private theorem receipt_0_11_2403_0 : fastPhase (bank 0 11).shape 179798 2403 32 1 0 1 0 = 35692473787628759096120781743 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_0_11_2403_0_join7

private theorem receipt_0_11_2403_1_part0 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 1) 0 128 = 8709680049184719326770230592 := by decide +kernel
private theorem receipt_0_11_2403_1_part1 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 1) 128 128 = 7340573259517053771758146880 := by decide +kernel
private theorem receipt_0_11_2403_1_part2 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 1) 256 128 = 6050099139446382344787801408 := by decide +kernel
private theorem receipt_0_11_2403_1_part3 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 1) 384 128 = 4835922195164451706734564672 := by decide +kernel
private theorem receipt_0_11_2403_1_part4 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 1) 512 128 = 3695713659135007354533475648 := by decide +kernel
private theorem receipt_0_11_2403_1_part5 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 1) 640 128 = 2627151681255696937811627478 := by decide +kernel
private theorem receipt_0_11_2403_1_part6 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 1) 768 128 = 1627923069752174308695827477 := by decide +kernel
private theorem receipt_0_11_2403_1_part7 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 1) 896 128 = 695715801335877766588572018 := by decide +kernel
private theorem receipt_0_11_2403_1_part8 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 1) 1024 38 = 36683505170923346185087202 := by decide +kernel
private theorem receipt_0_11_2403_1_join0 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 1) 0 256 = 16050253308701773098528377472 :=
  phaseBlock_append receipt_0_11_2403_1_part0 receipt_0_11_2403_1_part1 rfl rfl rfl
private theorem receipt_0_11_2403_1_join1 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 1) 256 256 = 10886021334610834051522366080 :=
  phaseBlock_append receipt_0_11_2403_1_part2 receipt_0_11_2403_1_part3 rfl rfl rfl
private theorem receipt_0_11_2403_1_join2 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 1) 0 512 = 26936274643312607150050743552 :=
  phaseBlock_append receipt_0_11_2403_1_join0 receipt_0_11_2403_1_join1 rfl rfl rfl
private theorem receipt_0_11_2403_1_join3 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 1) 512 256 = 6322865340390704292345103126 :=
  phaseBlock_append receipt_0_11_2403_1_part4 receipt_0_11_2403_1_part5 rfl rfl rfl
private theorem receipt_0_11_2403_1_join4 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 1) 896 166 = 732399306506801112773659220 :=
  phaseBlock_append receipt_0_11_2403_1_part7 receipt_0_11_2403_1_part8 rfl rfl rfl
private theorem receipt_0_11_2403_1_join5 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 1) 768 294 = 2360322376258975421469486697 :=
  phaseBlock_append receipt_0_11_2403_1_part6 receipt_0_11_2403_1_join4 rfl rfl rfl
private theorem receipt_0_11_2403_1_join6 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 1) 512 550 = 8683187716649679713814589823 :=
  phaseBlock_append receipt_0_11_2403_1_join3 receipt_0_11_2403_1_join5 rfl rfl rfl
private theorem receipt_0_11_2403_1_join7 :
    phaseBlock (fastLayer (bank 0 11).shape 179798 2403 32 1 0 1 1) 0 1062 = 35619462359962286863865333375 :=
  phaseBlock_append receipt_0_11_2403_1_join2 receipt_0_11_2403_1_join6 rfl rfl rfl

private theorem receipt_0_11_2403_1 : fastPhase (bank 0 11).shape 179798 2403 32 1 0 1 1 = 35619462359962286863865333375 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_0_11_2403_1_join7

theorem receipt_0_11 : Checked (bank 0 11) 32 0 1 := by
  refine checked_from_values (bank 0 11) 32 0 1
    (P3_7_1.checked (bank 0 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4866_1061)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_11_2402_0 receipt_0_11_2402_1 receipt_0_11_2403_0 receipt_0_11_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_11_2402_0_part0 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 0) 0 128 = 7779834458391938317550637408 := by decide +kernel
private theorem receipt_1_11_2402_0_part1 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 0) 128 128 = 6552303130419998588646441312 := by decide +kernel
private theorem receipt_1_11_2402_0_part2 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 0) 256 128 = 5396897800783074652084711776 := by decide +kernel
private theorem receipt_1_11_2402_0_part3 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 0) 384 128 = 4311361790051598620526289248 := by decide +kernel
private theorem receipt_1_11_2402_0_part4 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 0) 512 128 = 3293451388528927939340669280 := by decide +kernel
private theorem receipt_1_11_2402_0_part5 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 0) 640 128 = 2340936012253309920301583400 := by decide +kernel
private theorem receipt_1_11_2402_0_part6 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 0) 768 128 = 1451599732789975080590326695 := by decide +kernel
private theorem receipt_1_11_2402_0_part7 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 0) 896 128 = 623234555645182256826275328 := by decide +kernel
private theorem receipt_1_11_2402_0_part8 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 0) 1024 38 = 34277369584158454514898462 := by decide +kernel
private theorem receipt_1_11_2402_0_join0 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 0) 0 256 = 14332137588811936906197078720 :=
  phaseBlock_append receipt_1_11_2402_0_part0 receipt_1_11_2402_0_part1 rfl rfl rfl
private theorem receipt_1_11_2402_0_join1 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 0) 256 256 = 9708259590834673272611001024 :=
  phaseBlock_append receipt_1_11_2402_0_part2 receipt_1_11_2402_0_part3 rfl rfl rfl
private theorem receipt_1_11_2402_0_join2 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 0) 0 512 = 24040397179646610178808079744 :=
  phaseBlock_append receipt_1_11_2402_0_join0 receipt_1_11_2402_0_join1 rfl rfl rfl
private theorem receipt_1_11_2402_0_join3 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 0) 512 256 = 5634387400782237859642252680 :=
  phaseBlock_append receipt_1_11_2402_0_part4 receipt_1_11_2402_0_part5 rfl rfl rfl
private theorem receipt_1_11_2402_0_join4 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 0) 896 166 = 657511925229340711341173790 :=
  phaseBlock_append receipt_1_11_2402_0_part7 receipt_1_11_2402_0_part8 rfl rfl rfl
private theorem receipt_1_11_2402_0_join5 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 0) 768 294 = 2109111658019315791931500485 :=
  phaseBlock_append receipt_1_11_2402_0_part6 receipt_1_11_2402_0_join4 rfl rfl rfl
private theorem receipt_1_11_2402_0_join6 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 0) 512 550 = 7743499058801553651573753165 :=
  phaseBlock_append receipt_1_11_2402_0_join3 receipt_1_11_2402_0_join5 rfl rfl rfl
private theorem receipt_1_11_2402_0_join7 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 0) 0 1062 = 31783896238448163830381832909 :=
  phaseBlock_append receipt_1_11_2402_0_join2 receipt_1_11_2402_0_join6 rfl rfl rfl

private theorem receipt_1_11_2402_0 : fastPhase (bank 1 11).shape 179798 2402 32 1 0 2 0 = 31783896238448163830381832909 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_1_11_2402_0_join7

private theorem receipt_1_11_2402_1_part0 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 1) 0 128 = 7770091720612140664663000800 := by decide +kernel
private theorem receipt_1_11_2402_1_part1 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 1) 128 128 = 6543113724400594188572915424 := by decide +kernel
private theorem receipt_1_11_2402_1_part2 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 1) 256 128 = 5388244611289812263173859040 := by decide +kernel
private theorem receipt_1_11_2402_1_part3 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 1) 384 128 = 4303227800752226504392169184 := by decide +kernel
private theorem receipt_1_11_2402_1_part4 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 1) 512 128 = 3285819681800509121019512544 := by decide +kernel
private theorem receipt_1_11_2402_1_part5 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 1) 640 128 = 2333789768406505697978367471 := by decide +kernel
private theorem receipt_1_11_2402_1_part6 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 1) 768 128 = 1444922220566012547126936672 := by decide +kernel
private theorem receipt_1_11_2402_1_part7 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 1) 896 128 = 617009133976511998015196274 := by decide +kernel
private theorem receipt_1_11_2402_1_part8 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 1) 1024 38 = 32513786389462476211693497 := by decide +kernel
private theorem receipt_1_11_2402_1_join0 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 1) 0 256 = 14313205445012734853235916224 :=
  phaseBlock_append receipt_1_11_2402_1_part0 receipt_1_11_2402_1_part1 rfl rfl rfl
private theorem receipt_1_11_2402_1_join1 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 1) 256 256 = 9691472412042038767566028224 :=
  phaseBlock_append receipt_1_11_2402_1_part2 receipt_1_11_2402_1_part3 rfl rfl rfl
private theorem receipt_1_11_2402_1_join2 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 1) 0 512 = 24004677857054773620801944448 :=
  phaseBlock_append receipt_1_11_2402_1_join0 receipt_1_11_2402_1_join1 rfl rfl rfl
private theorem receipt_1_11_2402_1_join3 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 1) 512 256 = 5619609450207014818997880015 :=
  phaseBlock_append receipt_1_11_2402_1_part4 receipt_1_11_2402_1_part5 rfl rfl rfl
private theorem receipt_1_11_2402_1_join4 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 1) 896 166 = 649522920365974474226889771 :=
  phaseBlock_append receipt_1_11_2402_1_part7 receipt_1_11_2402_1_part8 rfl rfl rfl
private theorem receipt_1_11_2402_1_join5 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 1) 768 294 = 2094445140931987021353826443 :=
  phaseBlock_append receipt_1_11_2402_1_part6 receipt_1_11_2402_1_join4 rfl rfl rfl
private theorem receipt_1_11_2402_1_join6 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 1) 512 550 = 7714054591139001840351706458 :=
  phaseBlock_append receipt_1_11_2402_1_join3 receipt_1_11_2402_1_join5 rfl rfl rfl
private theorem receipt_1_11_2402_1_join7 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2402 32 1 0 2 1) 0 1062 = 31718732448193775461153650906 :=
  phaseBlock_append receipt_1_11_2402_1_join2 receipt_1_11_2402_1_join6 rfl rfl rfl

private theorem receipt_1_11_2402_1 : fastPhase (bank 1 11).shape 179798 2402 32 1 0 2 1 = 31718732448193775461153650906 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_1_11_2402_1_join7

private theorem receipt_1_11_2403_0_part0 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 0) 0 128 = 7779904052827143411941790528 := by decide +kernel
private theorem receipt_1_11_2403_0_part1 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 0) 128 128 = 6552357554598751605369140032 := by decide +kernel
private theorem receipt_1_11_2403_0_part2 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 0) 256 128 = 5396939041755067973224731456 := by decide +kernel
private theorem receipt_1_11_2403_0_part3 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 0) 384 128 = 4311391758269293501560795968 := by decide +kernel
private theorem receipt_1_11_2403_0_part4 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 0) 512 128 = 3293471918297301494142784320 := by decide +kernel
private theorem receipt_1_11_2403_0_part5 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 0) 640 128 = 2340948856920751422295687734 := by decide +kernel
private theorem receipt_1_11_2403_0_part6 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 0) 768 128 = 1451606563702819294714324849 := by decide +kernel
private theorem receipt_1_11_2403_0_part7 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 0) 896 128 = 623237003316268445356242779 := by decide +kernel
private theorem receipt_1_11_2403_0_part8 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 0) 1024 38 = 34277483589221627683681531 := by decide +kernel
private theorem receipt_1_11_2403_0_join0 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 0) 0 256 = 14332261607425895017310930560 :=
  phaseBlock_append receipt_1_11_2403_0_part0 receipt_1_11_2403_0_part1 rfl rfl rfl
private theorem receipt_1_11_2403_0_join1 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 0) 256 256 = 9708330800024361474785527424 :=
  phaseBlock_append receipt_1_11_2403_0_part2 receipt_1_11_2403_0_part3 rfl rfl rfl
private theorem receipt_1_11_2403_0_join2 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 0) 0 512 = 24040592407450256492096457984 :=
  phaseBlock_append receipt_1_11_2403_0_join0 receipt_1_11_2403_0_join1 rfl rfl rfl
private theorem receipt_1_11_2403_0_join3 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 0) 512 256 = 5634420775218052916438472054 :=
  phaseBlock_append receipt_1_11_2403_0_part4 receipt_1_11_2403_0_part5 rfl rfl rfl
private theorem receipt_1_11_2403_0_join4 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 0) 896 166 = 657514486905490073039924310 :=
  phaseBlock_append receipt_1_11_2403_0_part7 receipt_1_11_2403_0_part8 rfl rfl rfl
private theorem receipt_1_11_2403_0_join5 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 0) 768 294 = 2109121050608309367754249159 :=
  phaseBlock_append receipt_1_11_2403_0_part6 receipt_1_11_2403_0_join4 rfl rfl rfl
private theorem receipt_1_11_2403_0_join6 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 0) 512 550 = 7743541825826362284192721213 :=
  phaseBlock_append receipt_1_11_2403_0_join3 receipt_1_11_2403_0_join5 rfl rfl rfl
private theorem receipt_1_11_2403_0_join7 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 0) 0 1062 = 31784134233276618776289179197 :=
  phaseBlock_append receipt_1_11_2403_0_join2 receipt_1_11_2403_0_join6 rfl rfl rfl

private theorem receipt_1_11_2403_0 : fastPhase (bank 1 11).shape 179798 2403 32 1 0 2 0 = 31784134233276618776289179197 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_1_11_2403_0_join7

private theorem receipt_1_11_2403_1_part0 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 1) 0 128 = 7770161243886423027915201792 := by decide +kernel
private theorem receipt_1_11_2403_1_part1 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 1) 128 128 = 6543168085358382926148197632 := by decide +kernel
private theorem receipt_1_11_2403_1_part2 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 1) 256 128 = 5388285796616028113673985280 := by decide +kernel
private theorem receipt_1_11_2403_1_part3 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 1) 384 128 = 4303257720537026347932671232 := by decide +kernel
private theorem receipt_1_11_2403_1_part4 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 1) 512 128 = 3285840169989027741554023680 := by decide +kernel
private theorem receipt_1_11_2403_1_part5 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 1) 640 128 = 2333802578006346598670334664 := by decide +kernel
private theorem receipt_1_11_2403_1_part6 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 1) 768 128 = 1444929022637355587614320463 := by decide +kernel
private theorem receipt_1_11_2403_1_part7 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 1) 896 128 = 617011558673731477594243352 := by decide +kernel
private theorem receipt_1_11_2403_1_part8 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 1) 1024 38 = 32513894649537579091207344 := by decide +kernel
private theorem receipt_1_11_2403_1_join0 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 1) 0 256 = 14313329329244805954063399424 :=
  phaseBlock_append receipt_1_11_2403_1_part0 receipt_1_11_2403_1_part1 rfl rfl rfl
private theorem receipt_1_11_2403_1_join1 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 1) 256 256 = 9691543517153054461606656512 :=
  phaseBlock_append receipt_1_11_2403_1_part2 receipt_1_11_2403_1_part3 rfl rfl rfl
private theorem receipt_1_11_2403_1_join2 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 1) 0 512 = 24004872846397860415670055936 :=
  phaseBlock_append receipt_1_11_2403_1_join0 receipt_1_11_2403_1_join1 rfl rfl rfl
private theorem receipt_1_11_2403_1_join3 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 1) 512 256 = 5619642747995374340224358344 :=
  phaseBlock_append receipt_1_11_2403_1_part4 receipt_1_11_2403_1_part5 rfl rfl rfl
private theorem receipt_1_11_2403_1_join4 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 1) 896 166 = 649525453323269056685450696 :=
  phaseBlock_append receipt_1_11_2403_1_part7 receipt_1_11_2403_1_part8 rfl rfl rfl
private theorem receipt_1_11_2403_1_join5 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 1) 768 294 = 2094454475960624644299771159 :=
  phaseBlock_append receipt_1_11_2403_1_part6 receipt_1_11_2403_1_join4 rfl rfl rfl
private theorem receipt_1_11_2403_1_join6 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 1) 512 550 = 7714097223955998984524129503 :=
  phaseBlock_append receipt_1_11_2403_1_join3 receipt_1_11_2403_1_join5 rfl rfl rfl
private theorem receipt_1_11_2403_1_join7 :
    phaseBlock (fastLayer (bank 1 11).shape 179798 2403 32 1 0 2 1) 0 1062 = 31718970070353859400194185439 :=
  phaseBlock_append receipt_1_11_2403_1_join2 receipt_1_11_2403_1_join6 rfl rfl rfl

private theorem receipt_1_11_2403_1 : fastPhase (bank 1 11).shape 179798 2403 32 1 0 2 1 = 31718970070353859400194185439 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_1_11_2403_1_join7

theorem receipt_1_11 : Checked (bank 1 11) 32 0 2 := by
  refine checked_from_values (bank 1 11) 32 0 2
    (P3_7_1.checked (bank 1 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4866_1061)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_11_2402_0 receipt_1_11_2402_1 receipt_1_11_2403_0 receipt_1_11_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_11_2402_0_part0 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 0) 0 128 = 3908204792594182773124330656 := by decide +kernel
private theorem receipt_2_11_2402_0_part1 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 0) 128 128 = 3270671411075762301648659616 := by decide +kernel
private theorem receipt_2_11_2402_0_part2 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 0) 256 128 = 2676771535784987830536197280 := by decide +kernel
private theorem receipt_2_11_2402_0_part3 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 0) 384 128 = 2124686290793520067816211616 := by decide +kernel
private theorem receipt_2_11_2402_0_part4 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 0) 512 128 = 1612633856721029589139666080 := by decide +kernel
private theorem receipt_2_11_2402_0_part5 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 0) 640 128 = 1138869250311728356834487961 := by decide +kernel
private theorem receipt_2_11_2402_0_part6 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 0) 768 128 = 701684764840839956657891394 := by decide +kernel
private theorem receipt_2_11_2402_0_part7 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 0) 896 128 = 299406421964889968143659231 := by decide +kernel
private theorem receipt_2_11_2402_0_part8 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 0) 1024 38 = 16390593341111804865612297 := by decide +kernel
private theorem receipt_2_11_2402_0_join0 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 0) 0 256 = 7178876203669945074772990272 :=
  phaseBlock_append receipt_2_11_2402_0_part0 receipt_2_11_2402_0_part1 rfl rfl rfl
private theorem receipt_2_11_2402_0_join1 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 0) 256 256 = 4801457826578507898352408896 :=
  phaseBlock_append receipt_2_11_2402_0_part2 receipt_2_11_2402_0_part3 rfl rfl rfl
private theorem receipt_2_11_2402_0_join2 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 0) 0 512 = 11980334030248452973125399168 :=
  phaseBlock_append receipt_2_11_2402_0_join0 receipt_2_11_2402_0_join1 rfl rfl rfl
private theorem receipt_2_11_2402_0_join3 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 0) 512 256 = 2751503107032757945974154041 :=
  phaseBlock_append receipt_2_11_2402_0_part4 receipt_2_11_2402_0_part5 rfl rfl rfl
private theorem receipt_2_11_2402_0_join4 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 0) 896 166 = 315797015306001773009271528 :=
  phaseBlock_append receipt_2_11_2402_0_part7 receipt_2_11_2402_0_part8 rfl rfl rfl
private theorem receipt_2_11_2402_0_join5 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 0) 768 294 = 1017481780146841729667162922 :=
  phaseBlock_append receipt_2_11_2402_0_part6 receipt_2_11_2402_0_join4 rfl rfl rfl
private theorem receipt_2_11_2402_0_join6 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 0) 512 550 = 3768984887179599675641316963 :=
  phaseBlock_append receipt_2_11_2402_0_join3 receipt_2_11_2402_0_join5 rfl rfl rfl
private theorem receipt_2_11_2402_0_join7 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 0) 0 1062 = 15749318917428052648766716131 :=
  phaseBlock_append receipt_2_11_2402_0_join2 receipt_2_11_2402_0_join6 rfl rfl rfl

private theorem receipt_2_11_2402_0 : fastPhase (bank 2 11).shape 179798 2402 32 1 0 7 0 = 15749318917428052648766716131 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_2_11_2402_0_join7

private theorem receipt_2_11_2402_1_part0 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 1) 0 128 = 3903116868634183945422118560 := by decide +kernel
private theorem receipt_2_11_2402_1_part1 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 1) 128 128 = 3265921646570287036813594272 := by decide +kernel
private theorem receipt_2_11_2402_1_part2 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 1) 256 128 = 2672345978081215356557688480 := by decide +kernel
private theorem receipt_2_11_2402_1_part3 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 1) 384 128 = 2120571271015040067587681952 := by decide +kernel
private theorem receipt_2_11_2402_1_part4 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 1) 512 128 = 1608815987407454137377808032 := by decide +kernel
private theorem receipt_2_11_2402_1_part5 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 1) 640 128 = 1135335422770915158130547577 := by decide +kernel
private theorem receipt_2_11_2402_1_part6 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 1) 768 128 = 698422142256842038205101515 := by decide +kernel
private theorem receipt_2_11_2402_1_part7 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 1) 896 128 = 296402438215942392910532067 := by decide +kernel
private theorem receipt_2_11_2402_1_part8 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 1) 1024 38 = 15546755945096023809667533 := by decide +kernel
private theorem receipt_2_11_2402_1_join0 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 1) 0 256 = 7169038515204470982235712832 :=
  phaseBlock_append receipt_2_11_2402_1_part0 receipt_2_11_2402_1_part1 rfl rfl rfl
private theorem receipt_2_11_2402_1_join1 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 1) 256 256 = 4792917249096255424145370432 :=
  phaseBlock_append receipt_2_11_2402_1_part2 receipt_2_11_2402_1_part3 rfl rfl rfl
private theorem receipt_2_11_2402_1_join2 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 1) 0 512 = 11961955764300726406381083264 :=
  phaseBlock_append receipt_2_11_2402_1_join0 receipt_2_11_2402_1_join1 rfl rfl rfl
private theorem receipt_2_11_2402_1_join3 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 1) 512 256 = 2744151410178369295508355609 :=
  phaseBlock_append receipt_2_11_2402_1_part4 receipt_2_11_2402_1_part5 rfl rfl rfl
private theorem receipt_2_11_2402_1_join4 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 1) 896 166 = 311949194161038416720199600 :=
  phaseBlock_append receipt_2_11_2402_1_part7 receipt_2_11_2402_1_part8 rfl rfl rfl
private theorem receipt_2_11_2402_1_join5 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 1) 768 294 = 1010371336417880454925301115 :=
  phaseBlock_append receipt_2_11_2402_1_part6 receipt_2_11_2402_1_join4 rfl rfl rfl
private theorem receipt_2_11_2402_1_join6 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 1) 512 550 = 3754522746596249750433656724 :=
  phaseBlock_append receipt_2_11_2402_1_join3 receipt_2_11_2402_1_join5 rfl rfl rfl
private theorem receipt_2_11_2402_1_join7 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2402 32 1 0 7 1) 0 1062 = 15716478510896976156814739988 :=
  phaseBlock_append receipt_2_11_2402_1_join2 receipt_2_11_2402_1_join6 rfl rfl rfl

private theorem receipt_2_11_2402_1 : fastPhase (bank 2 11).shape 179798 2402 32 1 0 7 1 = 15716478510896976156814739988 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_2_11_2402_1_join7

private theorem receipt_2_11_2403_0_part0 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 0) 0 128 = 3908239754701597634584701696 := by decide +kernel
private theorem receipt_2_11_2403_0_part1 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 0) 128 128 = 3270698578781139542676564736 := by decide +kernel
private theorem receipt_2_11_2403_0_part2 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 0) 256 128 = 2676791991590960137556847360 := by decide +kernel
private theorem receipt_2_11_2403_0_part3 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 0) 384 128 = 2124701060263115590239808256 := by decide +kernel
private theorem receipt_2_11_2403_0_part4 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 0) 512 128 = 1612643909729890098554530560 := by decide +kernel
private theorem receipt_2_11_2403_0_part5 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 0) 640 128 = 1138875499737183407632223928 := by decide +kernel
private theorem receipt_2_11_2403_0_part6 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 0) 768 128 = 701688067118891485079346826 := by decide +kernel
private theorem receipt_2_11_2403_0_part7 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 0) 896 128 = 299407597963638801817495319 := by decide +kernel
private theorem receipt_2_11_2403_0_part8 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 0) 1024 38 = 16390647855992138548686973 := by decide +kernel
private theorem receipt_2_11_2403_0_join0 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 0) 0 256 = 7178938333482737177261266432 :=
  phaseBlock_append receipt_2_11_2403_0_part0 receipt_2_11_2403_0_part1 rfl rfl rfl
private theorem receipt_2_11_2403_0_join1 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 0) 256 256 = 4801493051854075727796655616 :=
  phaseBlock_append receipt_2_11_2403_0_part2 receipt_2_11_2403_0_part3 rfl rfl rfl
private theorem receipt_2_11_2403_0_join2 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 0) 0 512 = 11980431385336812905057922048 :=
  phaseBlock_append receipt_2_11_2403_0_join0 receipt_2_11_2403_0_join1 rfl rfl rfl
private theorem receipt_2_11_2403_0_join3 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 0) 512 256 = 2751519409467073506186754488 :=
  phaseBlock_append receipt_2_11_2403_0_part4 receipt_2_11_2403_0_part5 rfl rfl rfl
private theorem receipt_2_11_2403_0_join4 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 0) 896 166 = 315798245819630940366182292 :=
  phaseBlock_append receipt_2_11_2403_0_part7 receipt_2_11_2403_0_part8 rfl rfl rfl
private theorem receipt_2_11_2403_0_join5 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 0) 768 294 = 1017486312938522425445529118 :=
  phaseBlock_append receipt_2_11_2403_0_part6 receipt_2_11_2403_0_join4 rfl rfl rfl
private theorem receipt_2_11_2403_0_join6 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 0) 512 550 = 3769005722405595931632283606 :=
  phaseBlock_append receipt_2_11_2403_0_join3 receipt_2_11_2403_0_join5 rfl rfl rfl
private theorem receipt_2_11_2403_0_join7 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 0) 0 1062 = 15749437107742408836690205654 :=
  phaseBlock_append receipt_2_11_2403_0_join2 receipt_2_11_2403_0_join6 rfl rfl rfl

private theorem receipt_2_11_2403_0 : fastPhase (bank 2 11).shape 179798 2403 32 1 0 7 0 = 15749437107742408836690205654 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_2_11_2403_0_join7

private theorem receipt_2_11_2403_1_part0 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 1) 0 128 = 3903151793259607895336239680 := by decide +kernel
private theorem receipt_2_11_2403_1_part1 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 1) 128 128 = 3265948781364428146896462400 := by decide +kernel
private theorem receipt_2_11_2403_1_part2 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 1) 256 128 = 2672366405264232876331926080 := by decide +kernel
private theorem receipt_2_11_2403_1_part3 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 1) 384 128 = 2120586015874431277771137600 := by decide +kernel
private theorem receipt_2_11_2403_1_part4 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 1) 512 128 = 1608826019550208531243844160 := by decide +kernel
private theorem receipt_2_11_2403_1_part5 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 1) 640 128 = 1135341654820711957244831050 := by decide +kernel
private theorem receipt_2_11_2403_1_part6 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 1) 768 128 = 698425430428032373268818162 := by decide +kernel
private theorem receipt_2_11_2403_1_part7 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 1) 896 128 = 296403603124284771948658241 := by decide +kernel
private theorem receipt_2_11_2403_1_part8 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 1) 1024 38 = 15546807711035057464002837 := by decide +kernel
private theorem receipt_2_11_2403_1_join0 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 1) 0 256 = 7169100574624036042232702080 :=
  phaseBlock_append receipt_2_11_2403_1_part0 receipt_2_11_2403_1_part1 rfl rfl rfl
private theorem receipt_2_11_2403_1_join1 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 1) 256 256 = 4792952421138664154103063680 :=
  phaseBlock_append receipt_2_11_2403_1_part2 receipt_2_11_2403_1_part3 rfl rfl rfl
private theorem receipt_2_11_2403_1_join2 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 1) 0 512 = 11962052995762700196335765760 :=
  phaseBlock_append receipt_2_11_2403_1_join0 receipt_2_11_2403_1_join1 rfl rfl rfl
private theorem receipt_2_11_2403_1_join3 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 1) 512 256 = 2744167674370920488488675210 :=
  phaseBlock_append receipt_2_11_2403_1_part4 receipt_2_11_2403_1_part5 rfl rfl rfl
private theorem receipt_2_11_2403_1_join4 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 1) 896 166 = 311950410835319829412661078 :=
  phaseBlock_append receipt_2_11_2403_1_part7 receipt_2_11_2403_1_part8 rfl rfl rfl
private theorem receipt_2_11_2403_1_join5 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 1) 768 294 = 1010375841263352202681479240 :=
  phaseBlock_append receipt_2_11_2403_1_part6 receipt_2_11_2403_1_join4 rfl rfl rfl
private theorem receipt_2_11_2403_1_join6 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 1) 512 550 = 3754543515634272691170154450 :=
  phaseBlock_append receipt_2_11_2403_1_join3 receipt_2_11_2403_1_join5 rfl rfl rfl
private theorem receipt_2_11_2403_1_join7 :
    phaseBlock (fastLayer (bank 2 11).shape 179798 2403 32 1 0 7 1) 0 1062 = 15716596511396972887505920210 :=
  phaseBlock_append receipt_2_11_2403_1_join2 receipt_2_11_2403_1_join6 rfl rfl rfl

private theorem receipt_2_11_2403_1 : fastPhase (bank 2 11).shape 179798 2403 32 1 0 7 1 = 15716596511396972887505920210 :=
  phase_of_block (n := 1062) (by decide +kernel) receipt_2_11_2403_1_join7

theorem receipt_2_11 : Checked (bank 2 11) 32 0 7 := by
  refine checked_from_values (bank 2 11) 32 0 7
    (P3_7_1.checked (bank 2 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4866_1061)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_11_2402_0 receipt_2_11_2402_1 receipt_2_11_2403_0 receipt_2_11_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_11_2402_0_part0 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 0) 0 128 = 394476663829606763628525120 := by decide +kernel
private theorem receipt_3_11_2402_0_part1 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 0) 128 128 = 311964844452320229503284800 := by decide +kernel
private theorem receipt_3_11_2402_0_part2 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 0) 256 128 = 235289748923761531804284480 := by decide +kernel
private theorem receipt_3_11_2402_0_part3 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 0) 384 128 = 164719593979159797611542080 := by decide +kernel
private theorem receipt_3_11_2402_0_part4 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 0) 512 128 = 100519645302467151788504640 := by decide +kernel
private theorem receipt_3_11_2402_0_part5 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 0) 640 128 = 42952226942884160511489600 := by decide +kernel
private theorem receipt_3_11_2402_0_part6 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 0) 768 42 = 2708101870023154818204810 := by decide +kernel
private theorem receipt_3_11_2402_0_join0 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 0) 128 256 = 547254593376081761307569280 :=
  phaseBlock_append receipt_3_11_2402_0_part1 receipt_3_11_2402_0_part2 rfl rfl rfl
private theorem receipt_3_11_2402_0_join1 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 0) 0 384 = 941731257205688524936094400 :=
  phaseBlock_append receipt_3_11_2402_0_part0 receipt_3_11_2402_0_join0 rfl rfl rfl
private theorem receipt_3_11_2402_0_join2 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 0) 384 256 = 265239239281626949400046720 :=
  phaseBlock_append receipt_3_11_2402_0_part3 receipt_3_11_2402_0_part4 rfl rfl rfl
private theorem receipt_3_11_2402_0_join3 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 0) 640 170 = 45660328812907315329694410 :=
  phaseBlock_append receipt_3_11_2402_0_part5 receipt_3_11_2402_0_part6 rfl rfl rfl
private theorem receipt_3_11_2402_0_join4 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 0) 384 426 = 310899568094534264729741130 :=
  phaseBlock_append receipt_3_11_2402_0_join2 receipt_3_11_2402_0_join3 rfl rfl rfl
private theorem receipt_3_11_2402_0_join5 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 0) 0 810 = 1252630825300222789665835530 :=
  phaseBlock_append receipt_3_11_2402_0_join1 receipt_3_11_2402_0_join4 rfl rfl rfl

private theorem receipt_3_11_2402_0 : fastPhase (bank 3 11).shape 179798 2402 32 1 1 1 0 = 1252630825300222789665835530 :=
  phase_of_block (n := 810) (by decide +kernel) receipt_3_11_2402_0_join5

private theorem receipt_3_11_2402_1_part0 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 1) 0 128 = 393818491812449575550384832 := by decide +kernel
private theorem receipt_3_11_2402_1_part1 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 1) 128 128 = 311349376466826965409643200 := by decide +kernel
private theorem receipt_3_11_2402_1_part2 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 1) 256 128 = 234719263853826082062236352 := by decide +kernel
private theorem receipt_3_11_2402_1_part3 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 1) 384 128 = 164196346396005221701532352 := by decide +kernel
private theorem receipt_3_11_2402_1_part4 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 1) 512 128 = 100045865541183438628059840 := by decide +kernel
private theorem receipt_3_11_2402_1_part5 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 1) 640 128 = 42530121178965988778949312 := by decide +kernel
private theorem receipt_3_11_2402_1_part6 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 1) 768 42 = 2581227613802033826824166 := by decide +kernel
private theorem receipt_3_11_2402_1_join0 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 1) 128 256 = 546068640320653047471879552 :=
  phaseBlock_append receipt_3_11_2402_1_part1 receipt_3_11_2402_1_part2 rfl rfl rfl
private theorem receipt_3_11_2402_1_join1 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 1) 0 384 = 939887132133102623022264384 :=
  phaseBlock_append receipt_3_11_2402_1_part0 receipt_3_11_2402_1_join0 rfl rfl rfl
private theorem receipt_3_11_2402_1_join2 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 1) 384 256 = 264242211937188660329592192 :=
  phaseBlock_append receipt_3_11_2402_1_part3 receipt_3_11_2402_1_part4 rfl rfl rfl
private theorem receipt_3_11_2402_1_join3 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 1) 640 170 = 45111348792768022605773478 :=
  phaseBlock_append receipt_3_11_2402_1_part5 receipt_3_11_2402_1_part6 rfl rfl rfl
private theorem receipt_3_11_2402_1_join4 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 1) 384 426 = 309353560729956682935365670 :=
  phaseBlock_append receipt_3_11_2402_1_join2 receipt_3_11_2402_1_join3 rfl rfl rfl
private theorem receipt_3_11_2402_1_join5 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2402 32 1 1 1 1) 0 810 = 1249240692863059305957630054 :=
  phaseBlock_append receipt_3_11_2402_1_join1 receipt_3_11_2402_1_join4 rfl rfl rfl

private theorem receipt_3_11_2402_1 : fastPhase (bank 3 11).shape 179798 2402 32 1 1 1 1 = 1249240692863059305957630054 :=
  phase_of_block (n := 810) (by decide +kernel) receipt_3_11_2402_1_join5

private theorem receipt_3_11_2403_0_part0 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 0) 0 128 = 394480033622109175344402144 := by decide +kernel
private theorem receipt_3_11_2403_0_part1 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 0) 128 128 = 311967083157686672662847200 := by decide +kernel
private theorem receipt_3_11_2403_0_part2 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 0) 256 128 = 235291125026027314632568544 := by decide +kernel
private theorem receipt_3_11_2403_0_part3 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 0) 384 128 = 164720345133053497951223520 := by decide +kernel
private theorem receipt_3_11_2403_0_part4 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 0) 512 128 = 100519978623121073341550304 := by decide +kernel
private theorem receipt_3_11_2403_0_part5 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 0) 640 128 = 42952319294665179778588384 := by decide +kernel
private theorem receipt_3_11_2403_0_part6 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 0) 768 42 = 2708105352977492218830527 := by decide +kernel
private theorem receipt_3_11_2403_0_join0 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 0) 128 256 = 547258208183713987295415744 :=
  phaseBlock_append receipt_3_11_2403_0_part1 receipt_3_11_2403_0_part2 rfl rfl rfl
private theorem receipt_3_11_2403_0_join1 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 0) 0 384 = 941738241805823162639817888 :=
  phaseBlock_append receipt_3_11_2403_0_part0 receipt_3_11_2403_0_join0 rfl rfl rfl
private theorem receipt_3_11_2403_0_join2 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 0) 384 256 = 265240323756174571292773824 :=
  phaseBlock_append receipt_3_11_2403_0_part3 receipt_3_11_2403_0_part4 rfl rfl rfl
private theorem receipt_3_11_2403_0_join3 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 0) 640 170 = 45660424647642671997418911 :=
  phaseBlock_append receipt_3_11_2403_0_part5 receipt_3_11_2403_0_part6 rfl rfl rfl
private theorem receipt_3_11_2403_0_join4 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 0) 384 426 = 310900748403817243290192735 :=
  phaseBlock_append receipt_3_11_2403_0_join2 receipt_3_11_2403_0_join3 rfl rfl rfl
private theorem receipt_3_11_2403_0_join5 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 0) 0 810 = 1252638990209640405930010623 :=
  phaseBlock_append receipt_3_11_2403_0_join1 receipt_3_11_2403_0_join4 rfl rfl rfl

private theorem receipt_3_11_2403_0 : fastPhase (bank 3 11).shape 179798 2403 32 1 1 1 0 = 1252638990209640405930010623 :=
  phase_of_block (n := 810) (by decide +kernel) receipt_3_11_2403_0_join5

private theorem receipt_3_11_2403_1_part0 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 1) 0 128 = 393821855135424122475845152 := by decide +kernel
private theorem receipt_3_11_2403_1_part1 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 1) 128 128 = 311351610150978514040800800 := by decide +kernel
private theorem receipt_3_11_2403_1_part2 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 1) 256 128 = 234720636212809099698992672 := by decide +kernel
private theorem receipt_3_11_2403_1_part3 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 1) 384 128 = 164197094915925854801405472 := by decide +kernel
private theorem receipt_3_11_2403_1_part4 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 1) 512 128 = 100046197170304334050743840 := by decide +kernel
private theorem receipt_3_11_2403_1_part5 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 1) 640 128 = 42530212616531505728652832 := by decide +kernel
private theorem receipt_3_11_2403_1_part6 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 1) 768 42 = 2581230938476974371230601 := by decide +kernel
private theorem receipt_3_11_2403_1_join0 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 1) 128 256 = 546072246363787613739793472 :=
  phaseBlock_append receipt_3_11_2403_1_part1 receipt_3_11_2403_1_part2 rfl rfl rfl
private theorem receipt_3_11_2403_1_join1 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 1) 0 384 = 939894101499211736215638624 :=
  phaseBlock_append receipt_3_11_2403_1_part0 receipt_3_11_2403_1_join0 rfl rfl rfl
private theorem receipt_3_11_2403_1_join2 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 1) 384 256 = 264243292086230188852149312 :=
  phaseBlock_append receipt_3_11_2403_1_part3 receipt_3_11_2403_1_part4 rfl rfl rfl
private theorem receipt_3_11_2403_1_join3 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 1) 640 170 = 45111443555008480099883433 :=
  phaseBlock_append receipt_3_11_2403_1_part5 receipt_3_11_2403_1_part6 rfl rfl rfl
private theorem receipt_3_11_2403_1_join4 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 1) 384 426 = 309354735641238668952032745 :=
  phaseBlock_append receipt_3_11_2403_1_join2 receipt_3_11_2403_1_join3 rfl rfl rfl
private theorem receipt_3_11_2403_1_join5 :
    phaseBlock (fastLayer (bank 3 11).shape 179798 2403 32 1 1 1 1) 0 810 = 1249248837140450405167671369 :=
  phaseBlock_append receipt_3_11_2403_1_join1 receipt_3_11_2403_1_join4 rfl rfl rfl

private theorem receipt_3_11_2403_1 : fastPhase (bank 3 11).shape 179798 2403 32 1 1 1 1 = 1249248837140450405167671369 :=
  phase_of_block (n := 810) (by decide +kernel) receipt_3_11_2403_1_join5

theorem receipt_3_11 : Checked (bank 3 11) 32 1 1 := by
  refine checked_from_values (bank 3 11) 32 1 1
    (P3_7_1.checked (bank 3 11) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_3870_809)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_11_2402_0 receipt_3_11_2402_1 receipt_3_11_2403_0 receipt_3_11_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_0_12_2402_0_part0 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 0) 0 128 = 5427992584640601000638702904 := by decide +kernel
private theorem receipt_0_12_2402_0_part1 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 0) 128 128 = 4415390029538274365012746008 := by decide +kernel
private theorem receipt_0_12_2402_0_part2 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 0) 256 128 = 3469618689475162845915682314 := by decide +kernel
private theorem receipt_0_12_2402_0_part3 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 0) 384 128 = 2588392293674624272542318006 := by decide +kernel
private theorem receipt_0_12_2402_0_part4 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 0) 512 128 = 1769430813714228247326594930 := by decide +kernel
private theorem receipt_0_12_2402_0_part5 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 0) 640 128 = 1010460900027148046698708653 := by decide +kernel
private theorem receipt_0_12_2402_0_part6 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 0) 768 123 = 309610693313838562182314433 := by decide +kernel
private theorem receipt_0_12_2402_0_join0 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 0) 128 256 = 7885008719013437210928428322 :=
  phaseBlock_append receipt_0_12_2402_0_part1 receipt_0_12_2402_0_part2 rfl rfl rfl
private theorem receipt_0_12_2402_0_join1 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 0) 0 384 = 13313001303654038211567131226 :=
  phaseBlock_append receipt_0_12_2402_0_part0 receipt_0_12_2402_0_join0 rfl rfl rfl
private theorem receipt_0_12_2402_0_join2 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 0) 384 256 = 4357823107388852519868912936 :=
  phaseBlock_append receipt_0_12_2402_0_part3 receipt_0_12_2402_0_part4 rfl rfl rfl
private theorem receipt_0_12_2402_0_join3 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 0) 640 251 = 1320071593340986608881023086 :=
  phaseBlock_append receipt_0_12_2402_0_part5 receipt_0_12_2402_0_part6 rfl rfl rfl
private theorem receipt_0_12_2402_0_join4 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 0) 384 507 = 5677894700729839128749936022 :=
  phaseBlock_append receipt_0_12_2402_0_join2 receipt_0_12_2402_0_join3 rfl rfl rfl
private theorem receipt_0_12_2402_0_join5 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 0) 0 891 = 18990896004383877340317067248 :=
  phaseBlock_append receipt_0_12_2402_0_join1 receipt_0_12_2402_0_join4 rfl rfl rfl

private theorem receipt_0_12_2402_0 : fastPhase (bank 0 12).shape 179798 2402 31 1 0 1 0 = 18990896004383877340317067248 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_0_12_2402_0_join5

private theorem receipt_0_12_2402_1_part0 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 1) 0 128 = 5419923347414701308385121055 := by decide +kernel
private theorem receipt_0_12_2402_1_part1 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 1) 128 128 = 4407833574275747335112736931 := by decide +kernel
private theorem receipt_0_12_2402_1_part2 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 1) 256 128 = 3462557753863677750142081782 := by decide +kernel
private theorem receipt_0_12_2402_1_part3 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 1) 384 128 = 2581809665740583298183271842 := by decide +kernel
private theorem receipt_0_12_2402_1_part4 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 1) 512 128 = 1763309332281360013358208870 := by decide +kernel
private theorem receipt_0_12_2402_1_part5 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 1) 640 128 = 1004783454670691732700410919 := by decide +kernel
private theorem receipt_0_12_2402_1_part6 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 1) 768 123 = 304557515949228959200743864 := by decide +kernel
private theorem receipt_0_12_2402_1_join0 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 1) 128 256 = 7870391328139425085254818713 :=
  phaseBlock_append receipt_0_12_2402_1_part1 receipt_0_12_2402_1_part2 rfl rfl rfl
private theorem receipt_0_12_2402_1_join1 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 1) 0 384 = 13290314675554126393639939768 :=
  phaseBlock_append receipt_0_12_2402_1_part0 receipt_0_12_2402_1_join0 rfl rfl rfl
private theorem receipt_0_12_2402_1_join2 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 1) 384 256 = 4345118998021943311541480712 :=
  phaseBlock_append receipt_0_12_2402_1_part3 receipt_0_12_2402_1_part4 rfl rfl rfl
private theorem receipt_0_12_2402_1_join3 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 1) 640 251 = 1309340970619920691901154783 :=
  phaseBlock_append receipt_0_12_2402_1_part5 receipt_0_12_2402_1_part6 rfl rfl rfl
private theorem receipt_0_12_2402_1_join4 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 1) 384 507 = 5654459968641864003442635495 :=
  phaseBlock_append receipt_0_12_2402_1_join2 receipt_0_12_2402_1_join3 rfl rfl rfl
private theorem receipt_0_12_2402_1_join5 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2402 31 1 0 1 1) 0 891 = 18944774644195990397082575263 :=
  phaseBlock_append receipt_0_12_2402_1_join1 receipt_0_12_2402_1_join4 rfl rfl rfl

private theorem receipt_0_12_2402_1 : fastPhase (bank 0 12).shape 179798 2402 31 1 0 1 1 = 18944774644195990397082575263 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_0_12_2402_1_join5

private theorem receipt_0_12_2403_0_part0 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 0) 0 128 = 5428040862725802104888722179 := by decide +kernel
private theorem receipt_0_12_2403_0_part1 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 0) 128 128 = 4415425957018147955473902496 := by decide +kernel
private theorem receipt_0_12_2403_0_part2 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 0) 256 128 = 3469644171820688388644269332 := by decide +kernel
private theorem receipt_0_12_2403_0_part3 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 0) 384 128 = 2588409167967747131933236907 := by decide +kernel
private theorem receipt_0_12_2403_0_part4 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 0) 512 128 = 1769440831685155662549088866 := by decide +kernel
private theorem receipt_0_12_2403_0_part5 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 0) 640 128 = 1010465728982490519944405820 := by decide +kernel
private theorem receipt_0_12_2403_0_part6 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 0) 768 123 = 309611916888373730239878381 := by decide +kernel
private theorem receipt_0_12_2403_0_join0 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 0) 128 256 = 7885070128838836344118171828 :=
  phaseBlock_append receipt_0_12_2403_0_part1 receipt_0_12_2403_0_part2 rfl rfl rfl
private theorem receipt_0_12_2403_0_join1 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 0) 0 384 = 13313110991564638449006894007 :=
  phaseBlock_append receipt_0_12_2403_0_part0 receipt_0_12_2403_0_join0 rfl rfl rfl
private theorem receipt_0_12_2403_0_join2 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 0) 384 256 = 4357849999652902794482325773 :=
  phaseBlock_append receipt_0_12_2403_0_part3 receipt_0_12_2403_0_part4 rfl rfl rfl
private theorem receipt_0_12_2403_0_join3 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 0) 640 251 = 1320077645870864250184284201 :=
  phaseBlock_append receipt_0_12_2403_0_part5 receipt_0_12_2403_0_part6 rfl rfl rfl
private theorem receipt_0_12_2403_0_join4 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 0) 384 507 = 5677927645523767044666609974 :=
  phaseBlock_append receipt_0_12_2403_0_join2 receipt_0_12_2403_0_join3 rfl rfl rfl
private theorem receipt_0_12_2403_0_join5 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 0) 0 891 = 18991038637088405493673503981 :=
  phaseBlock_append receipt_0_12_2403_0_join1 receipt_0_12_2403_0_join4 rfl rfl rfl

private theorem receipt_0_12_2403_0 : fastPhase (bank 0 12).shape 179798 2403 31 1 0 1 0 = 18991038637088405493673503981 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_0_12_2403_0_join5

private theorem receipt_0_12_2403_1_part0 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 1) 0 128 = 5419971566513263793182722222 := by decide +kernel
private theorem receipt_0_12_2403_1_part1 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 1) 128 128 = 4407869450329510444119148015 := by decide +kernel
private theorem receipt_0_12_2403_1_part2 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 1) 256 128 = 3462583191974104693647112007 := by decide +kernel
private theorem receipt_0_12_2403_1_part3 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 1) 384 128 = 2581826502601787174768461449 := by decide +kernel
private theorem receipt_0_12_2403_1_part4 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 1) 512 128 = 1763319319237775402082649557 := by decide +kernel
private theorem receipt_0_12_2403_1_part5 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 1) 640 128 = 1004788258643229850951702288 := by decide +kernel
private theorem receipt_0_12_2403_1_part6 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 1) 768 123 = 304558720842462329217903392 := by decide +kernel
private theorem receipt_0_12_2403_1_join0 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 1) 128 256 = 7870452642303615137766260022 :=
  phaseBlock_append receipt_0_12_2403_1_part1 receipt_0_12_2403_1_part2 rfl rfl rfl
private theorem receipt_0_12_2403_1_join1 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 1) 0 384 = 13290424208816878930948982244 :=
  phaseBlock_append receipt_0_12_2403_1_part0 receipt_0_12_2403_1_join0 rfl rfl rfl
private theorem receipt_0_12_2403_1_join2 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 1) 384 256 = 4345145821839562576851111006 :=
  phaseBlock_append receipt_0_12_2403_1_part3 receipt_0_12_2403_1_part4 rfl rfl rfl
private theorem receipt_0_12_2403_1_join3 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 1) 640 251 = 1309346979485692180169605680 :=
  phaseBlock_append receipt_0_12_2403_1_part5 receipt_0_12_2403_1_part6 rfl rfl rfl
private theorem receipt_0_12_2403_1_join4 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 1) 384 507 = 5654492801325254757020716686 :=
  phaseBlock_append receipt_0_12_2403_1_join2 receipt_0_12_2403_1_join3 rfl rfl rfl
private theorem receipt_0_12_2403_1_join5 :
    phaseBlock (fastLayer (bank 0 12).shape 179798 2403 31 1 0 1 1) 0 891 = 18944917010142133687969698930 :=
  phaseBlock_append receipt_0_12_2403_1_join1 receipt_0_12_2403_1_join4 rfl rfl rfl

private theorem receipt_0_12_2403_1 : fastPhase (bank 0 12).shape 179798 2403 31 1 0 1 1 = 18944917010142133687969698930 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_0_12_2403_1_join5

theorem receipt_0_12 : Checked (bank 0 12) 31 0 1 := by
  refine checked_from_values (bank 0 12) 31 0 1
    (P3_7_1.checked (bank 0 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4255_890)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_12_2402_0 receipt_0_12_2402_1 receipt_0_12_2403_0 receipt_0_12_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_12_2402_0_part0 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 0) 0 128 = 4892365028800790387856655437 := by decide +kernel
private theorem receipt_1_12_2402_0_part1 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 0) 128 128 = 3976308833904351416723289207 := by decide +kernel
private theorem receipt_1_12_2402_0_part2 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 0) 256 128 = 3121937202981425421571035519 := by decide +kernel
private theorem receipt_1_12_2402_0_part3 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 0) 384 128 = 2327041784532453727080083898 := by decide +kernel
private theorem receipt_1_12_2402_0_part4 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 0) 512 128 = 1589426744823616855664235207 := by decide +kernel
private theorem receipt_1_12_2402_0_part5 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 0) 640 128 = 906909141858666718815960351 := by decide +kernel
private theorem receipt_1_12_2402_0_part6 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 0) 768 123 = 277672787618554061455394007 := by decide +kernel
private theorem receipt_1_12_2402_0_join0 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 0) 128 256 = 7098246036885776838294324726 :=
  phaseBlock_append receipt_1_12_2402_0_part1 receipt_1_12_2402_0_part2 rfl rfl rfl
private theorem receipt_1_12_2402_0_join1 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 0) 0 384 = 11990611065686567226150980163 :=
  phaseBlock_append receipt_1_12_2402_0_part0 receipt_1_12_2402_0_join0 rfl rfl rfl
private theorem receipt_1_12_2402_0_join2 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 0) 384 256 = 3916468529356070582744319105 :=
  phaseBlock_append receipt_1_12_2402_0_part3 receipt_1_12_2402_0_part4 rfl rfl rfl
private theorem receipt_1_12_2402_0_join3 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 0) 640 251 = 1184581929477220780271354358 :=
  phaseBlock_append receipt_1_12_2402_0_part5 receipt_1_12_2402_0_part6 rfl rfl rfl
private theorem receipt_1_12_2402_0_join4 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 0) 384 507 = 5101050458833291363015673463 :=
  phaseBlock_append receipt_1_12_2402_0_join2 receipt_1_12_2402_0_join3 rfl rfl rfl
private theorem receipt_1_12_2402_0_join5 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 0) 0 891 = 17091661524519858589166653626 :=
  phaseBlock_append receipt_1_12_2402_0_join1 receipt_1_12_2402_0_join4 rfl rfl rfl

private theorem receipt_1_12_2402_0 : fastPhase (bank 1 12).shape 179798 2402 31 1 0 2 0 = 17091661524519858589166653626 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_1_12_2402_0_join5

private theorem receipt_1_12_2402_1_part0 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 1) 0 128 = 4885059671972778267834409032 := by decide +kernel
private theorem receipt_1_12_2402_1_part1 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 1) 128 128 = 3969477494873115443274567556 := by decide +kernel
private theorem receipt_1_12_2402_1_part2 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 1) 256 128 = 3115563169230762712589540919 := by decide +kernel
private theorem receipt_1_12_2402_1_part3 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 1) 384 128 = 2321108441403141628417661127 := by decide +kernel
private theorem receipt_1_12_2402_1_part4 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 1) 512 128 = 1583917575779913502417116210 := by decide +kernel
private theorem receipt_1_12_2402_1_part5 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 1) 640 128 = 901807728297379881920072571 := by decide +kernel
private theorem receipt_1_12_2402_1_part6 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 1) 768 123 = 273139644988942627614319977 := by decide +kernel
private theorem receipt_1_12_2402_1_join0 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 1) 128 256 = 7085040664103878155864108475 :=
  phaseBlock_append receipt_1_12_2402_1_part1 receipt_1_12_2402_1_part2 rfl rfl rfl
private theorem receipt_1_12_2402_1_join1 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 1) 0 384 = 11970100336076656423698517507 :=
  phaseBlock_append receipt_1_12_2402_1_part0 receipt_1_12_2402_1_join0 rfl rfl rfl
private theorem receipt_1_12_2402_1_join2 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 1) 384 256 = 3905026017183055130834777337 :=
  phaseBlock_append receipt_1_12_2402_1_part3 receipt_1_12_2402_1_part4 rfl rfl rfl
private theorem receipt_1_12_2402_1_join3 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 1) 640 251 = 1174947373286322509534392548 :=
  phaseBlock_append receipt_1_12_2402_1_part5 receipt_1_12_2402_1_part6 rfl rfl rfl
private theorem receipt_1_12_2402_1_join4 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 1) 384 507 = 5079973390469377640369169885 :=
  phaseBlock_append receipt_1_12_2402_1_join2 receipt_1_12_2402_1_join3 rfl rfl rfl
private theorem receipt_1_12_2402_1_join5 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2402 31 1 0 2 1) 0 891 = 17050073726546034064067687392 :=
  phaseBlock_append receipt_1_12_2402_1_join1 receipt_1_12_2402_1_join4 rfl rfl rfl

private theorem receipt_1_12_2402_1 : fastPhase (bank 1 12).shape 179798 2402 31 1 0 2 1 = 17050073726546034064067687392 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_1_12_2402_1_join5

private theorem receipt_1_12_2403_0_part0 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 0) 0 128 = 4892408543118630795439623114 := by decide +kernel
private theorem receipt_1_12_2403_0_part1 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 0) 128 128 = 3976341188854093603477355164 := by decide +kernel
private theorem receipt_1_12_2403_0_part2 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 0) 256 128 = 3121960131986530053361573539 := by decide +kernel
private theorem receipt_1_12_2403_0_part3 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 0) 384 128 = 2327056955163830069954340518 := by decide +kernel
private theorem receipt_1_12_2403_0_part4 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 0) 512 128 = 1589435743765667308227013491 := by decide +kernel
private theorem receipt_1_12_2403_0_part5 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 0) 640 128 = 906913476001240715225188437 := by decide +kernel
private theorem receipt_1_12_2403_0_part6 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 0) 768 123 = 277673884986964247349921813 := by decide +kernel
private theorem receipt_1_12_2403_0_join0 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 0) 128 256 = 7098301320840623656838928703 :=
  phaseBlock_append receipt_1_12_2403_0_part1 receipt_1_12_2403_0_part2 rfl rfl rfl
private theorem receipt_1_12_2403_0_join1 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 0) 0 384 = 11990709863959254452278551817 :=
  phaseBlock_append receipt_1_12_2403_0_part0 receipt_1_12_2403_0_join0 rfl rfl rfl
private theorem receipt_1_12_2403_0_join2 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 0) 384 256 = 3916492698929497378181354009 :=
  phaseBlock_append receipt_1_12_2403_0_part3 receipt_1_12_2403_0_part4 rfl rfl rfl
private theorem receipt_1_12_2403_0_join3 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 0) 640 251 = 1184587360988204962575110250 :=
  phaseBlock_append receipt_1_12_2403_0_part5 receipt_1_12_2403_0_part6 rfl rfl rfl
private theorem receipt_1_12_2403_0_join4 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 0) 384 507 = 5101080059917702340756464259 :=
  phaseBlock_append receipt_1_12_2403_0_join2 receipt_1_12_2403_0_join3 rfl rfl rfl
private theorem receipt_1_12_2403_0_join5 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 0) 0 891 = 17091789923876956793035016076 :=
  phaseBlock_append receipt_1_12_2403_0_join1 receipt_1_12_2403_0_join4 rfl rfl rfl

private theorem receipt_1_12_2403_0 : fastPhase (bank 1 12).shape 179798 2403 31 1 0 2 0 = 17091789923876956793035016076 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_1_12_2403_0_join5

private theorem receipt_1_12_2403_1_part0 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 1) 0 128 = 4885103132836265911198178733 := by decide +kernel
private theorem receipt_1_12_2403_1_part1 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 1) 128 128 = 3969509803296132903068535358 := by decide +kernel
private theorem receipt_1_12_2403_1_part2 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 1) 256 128 = 3115586058281353407822928859 := by decide +kernel
private theorem receipt_1_12_2403_1_part3 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 1) 384 128 = 2321123578281568865290491147 := by decide +kernel
private theorem receipt_1_12_2403_1_part4 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 1) 512 128 = 1583926546803170779224280623 := by decide +kernel
private theorem receipt_1_12_2403_1_part5 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 1) 640 128 = 901812039989351851924789249 := by decide +kernel
private theorem receipt_1_12_2403_1_part6 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 1) 768 123 = 273140725597893072489054350 := by decide +kernel
private theorem receipt_1_12_2403_1_join0 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 1) 128 256 = 7085095861577486310891464217 :=
  phaseBlock_append receipt_1_12_2403_1_part1 receipt_1_12_2403_1_part2 rfl rfl rfl
private theorem receipt_1_12_2403_1_join1 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 1) 0 384 = 11970198994413752222089642950 :=
  phaseBlock_append receipt_1_12_2403_1_part0 receipt_1_12_2403_1_join0 rfl rfl rfl
private theorem receipt_1_12_2403_1_join2 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 1) 384 256 = 3905050125084739644514771770 :=
  phaseBlock_append receipt_1_12_2403_1_part3 receipt_1_12_2403_1_part4 rfl rfl rfl
private theorem receipt_1_12_2403_1_join3 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 1) 640 251 = 1174952765587244924413843599 :=
  phaseBlock_append receipt_1_12_2403_1_part5 receipt_1_12_2403_1_part6 rfl rfl rfl
private theorem receipt_1_12_2403_1_join4 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 1) 384 507 = 5080002890671984568928615369 :=
  phaseBlock_append receipt_1_12_2403_1_join2 receipt_1_12_2403_1_join3 rfl rfl rfl
private theorem receipt_1_12_2403_1_join5 :
    phaseBlock (fastLayer (bank 1 12).shape 179798 2403 31 1 0 2 1) 0 891 = 17050201885085736791018258319 :=
  phaseBlock_append receipt_1_12_2403_1_join1 receipt_1_12_2403_1_join4 rfl rfl rfl

private theorem receipt_1_12_2403_1 : fastPhase (bank 1 12).shape 179798 2403 31 1 0 2 1 = 17050201885085736791018258319 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_1_12_2403_1_join5

theorem receipt_1_12 : Checked (bank 1 12) 31 0 2 := by
  refine checked_from_values (bank 1 12) 31 0 2
    (P3_7_1.checked (bank 1 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4255_890)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_12_2402_0 receipt_1_12_2402_1 receipt_1_12_2403_0 receipt_1_12_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_12_2402_0_part0 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 0) 0 128 = 2674926946798057120474655520 := by decide +kernel
private theorem receipt_2_12_2402_0_part1 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 0) 128 128 = 2160996705063131023045327648 := by decide +kernel
private theorem receipt_2_12_2402_0_part2 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 0) 256 128 = 1686431102578697476480699168 := by decide +kernel
private theorem receipt_2_12_2402_0_part3 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 0) 384 128 = 1249426681884050048705076000 := by decide +kernel
private theorem receipt_2_12_2402_0_part4 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 0) 512 128 = 848217429955273824577792928 := by decide +kernel
private theorem receipt_2_12_2402_0_part5 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 0) 640 128 = 481074985778104179715242306 := by decide +kernel
private theorem receipt_2_12_2402_0_part6 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 0) 768 123 = 146492315271241796257383507 := by decide +kernel
private theorem receipt_2_12_2402_0_join0 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 0) 128 256 = 3847427807641828499526026816 :=
  phaseBlock_append receipt_2_12_2402_0_part1 receipt_2_12_2402_0_part2 rfl rfl rfl
private theorem receipt_2_12_2402_0_join1 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 0) 0 384 = 6522354754439885620000682336 :=
  phaseBlock_append receipt_2_12_2402_0_part0 receipt_2_12_2402_0_join0 rfl rfl rfl
private theorem receipt_2_12_2402_0_join2 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 0) 384 256 = 2097644111839323873282868928 :=
  phaseBlock_append receipt_2_12_2402_0_part3 receipt_2_12_2402_0_part4 rfl rfl rfl
private theorem receipt_2_12_2402_0_join3 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 0) 640 251 = 627567301049345975972625813 :=
  phaseBlock_append receipt_2_12_2402_0_part5 receipt_2_12_2402_0_part6 rfl rfl rfl
private theorem receipt_2_12_2402_0_join4 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 0) 384 507 = 2725211412888669849255494741 :=
  phaseBlock_append receipt_2_12_2402_0_join2 receipt_2_12_2402_0_join3 rfl rfl rfl
private theorem receipt_2_12_2402_0_join5 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 0) 0 891 = 9247566167328555469256177077 :=
  phaseBlock_append receipt_2_12_2402_0_join1 receipt_2_12_2402_0_join4 rfl rfl rfl

private theorem receipt_2_12_2402_0 : fastPhase (bank 2 12).shape 179798 2402 31 1 0 7 0 = 9247566167328555469256177077 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_2_12_2402_0_join5

private theorem receipt_2_12_2402_1_part0 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 1) 0 128 = 2670806856981705853548452000 := by decide +kernel
private theorem receipt_2_12_2402_1_part1 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 1) 128 128 = 2157182061425815210606413984 := by decide +kernel
private theorem receipt_2_12_2402_1_part2 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 1) 256 128 = 1682908077380891018273044640 := by decide +kernel
private theorem receipt_2_12_2402_1_part3 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 1) 384 128 = 1246181733997298482791000224 := by decide +kernel
private theorem receipt_2_12_2402_1_part4 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 1) 512 128 = 845237302468388612029844779 := by decide +kernel
private theorem receipt_2_12_2402_1_part5 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 1) 640 128 = 478346700317979775277524506 := by decide +kernel
private theorem receipt_2_12_2402_1_part6 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 1) 768 123 = 144096064709385517095302002 := by decide +kernel
private theorem receipt_2_12_2402_1_join0 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 1) 128 256 = 3840090138806706228879458624 :=
  phaseBlock_append receipt_2_12_2402_1_part1 receipt_2_12_2402_1_part2 rfl rfl rfl
private theorem receipt_2_12_2402_1_join1 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 1) 0 384 = 6510896995788412082427910624 :=
  phaseBlock_append receipt_2_12_2402_1_part0 receipt_2_12_2402_1_join0 rfl rfl rfl
private theorem receipt_2_12_2402_1_join2 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 1) 384 256 = 2091419036465687094820845003 :=
  phaseBlock_append receipt_2_12_2402_1_part3 receipt_2_12_2402_1_part4 rfl rfl rfl
private theorem receipt_2_12_2402_1_join3 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 1) 640 251 = 622442765027365292372826508 :=
  phaseBlock_append receipt_2_12_2402_1_part5 receipt_2_12_2402_1_part6 rfl rfl rfl
private theorem receipt_2_12_2402_1_join4 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 1) 384 507 = 2713861801493052387193671511 :=
  phaseBlock_append receipt_2_12_2402_1_join2 receipt_2_12_2402_1_join3 rfl rfl rfl
private theorem receipt_2_12_2402_1_join5 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2402 31 1 0 7 1) 0 891 = 9224758797281464469621582135 :=
  phaseBlock_append receipt_2_12_2402_1_join1 receipt_2_12_2402_1_join4 rfl rfl rfl

private theorem receipt_2_12_2402_1 : fastPhase (bank 2 12).shape 179798 2402 31 1 0 7 1 = 9224758797281464469621582135 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_2_12_2402_1_join5

private theorem receipt_2_12_2403_0_part0 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 0) 0 128 = 2674950510391352408173664928 := by decide +kernel
private theorem receipt_2_12_2403_0_part1 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 0) 128 128 = 2161014146923122323392473760 := by decide +kernel
private theorem receipt_2_12_2403_0_part2 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 0) 256 128 = 1686443414310945205832776352 := by decide +kernel
private theorem receipt_2_12_2403_0_part3 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 0) 384 128 = 1249434797892267146195061408 := by decide +kernel
private theorem receipt_2_12_2403_0_part4 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 0) 512 128 = 848222228258676817806294405 := by decide +kernel
private theorem receipt_2_12_2403_0_part5 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 0) 640 128 = 481077285067677289082596487 := by decide +kernel
private theorem receipt_2_12_2403_0_part6 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 0) 768 123 = 146492894256806224219185903 := by decide +kernel
private theorem receipt_2_12_2403_0_join0 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 0) 128 256 = 3847457561234067529225250112 :=
  phaseBlock_append receipt_2_12_2403_0_part1 receipt_2_12_2403_0_part2 rfl rfl rfl
private theorem receipt_2_12_2403_0_join1 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 0) 0 384 = 6522408071625419937398915040 :=
  phaseBlock_append receipt_2_12_2403_0_part0 receipt_2_12_2403_0_join0 rfl rfl rfl
private theorem receipt_2_12_2403_0_join2 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 0) 384 256 = 2097657026150943964001355813 :=
  phaseBlock_append receipt_2_12_2403_0_part3 receipt_2_12_2403_0_part4 rfl rfl rfl
private theorem receipt_2_12_2403_0_join3 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 0) 640 251 = 627570179324483513301782390 :=
  phaseBlock_append receipt_2_12_2403_0_part5 receipt_2_12_2403_0_part6 rfl rfl rfl
private theorem receipt_2_12_2403_0_join4 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 0) 384 507 = 2725227205475427477303138203 :=
  phaseBlock_append receipt_2_12_2403_0_join2 receipt_2_12_2403_0_join3 rfl rfl rfl
private theorem receipt_2_12_2403_0_join5 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 0) 0 891 = 9247635277100847414702053243 :=
  phaseBlock_append receipt_2_12_2403_0_join1 receipt_2_12_2403_0_join4 rfl rfl rfl

private theorem receipt_2_12_2403_0 : fastPhase (bank 2 12).shape 179798 2403 31 1 0 7 0 = 9247635277100847414702053243 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_2_12_2403_0_join5

private theorem receipt_2_12_2403_1_part0 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 1) 0 128 = 2670830390517593451239401120 := by decide +kernel
private theorem receipt_2_12_2403_1_part1 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 1) 128 128 = 2157199477379855515444688544 := by decide +kernel
private theorem receipt_2_12_2403_1_part2 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 1) 256 128 = 1682920367076517113316902560 := by decide +kernel
private theorem receipt_2_12_2403_1_part3 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 1) 384 128 = 1246189831563131088966669984 := by decide +kernel
private theorem receipt_2_12_2403_1_part4 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 1) 512 128 = 845242085657280780941845029 := by decide +kernel
private theorem receipt_2_12_2403_1_part5 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 1) 640 128 = 478348987590997018802290159 := by decide +kernel
private theorem receipt_2_12_2403_1_part6 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 1) 768 123 = 144096634833120282082760400 := by decide +kernel
private theorem receipt_2_12_2403_1_join0 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 1) 128 256 = 3840119844456372628761591104 :=
  phaseBlock_append receipt_2_12_2403_1_part1 receipt_2_12_2403_1_part2 rfl rfl rfl
private theorem receipt_2_12_2403_1_join1 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 1) 0 384 = 6510950234973966080000992224 :=
  phaseBlock_append receipt_2_12_2403_1_part0 receipt_2_12_2403_1_join0 rfl rfl rfl
private theorem receipt_2_12_2403_1_join2 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 1) 384 256 = 2091431917220411869908515013 :=
  phaseBlock_append receipt_2_12_2403_1_part3 receipt_2_12_2403_1_part4 rfl rfl rfl
private theorem receipt_2_12_2403_1_join3 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 1) 640 251 = 622445622424117300885050559 :=
  phaseBlock_append receipt_2_12_2403_1_part5 receipt_2_12_2403_1_part6 rfl rfl rfl
private theorem receipt_2_12_2403_1_join4 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 1) 384 507 = 2713877539644529170793565572 :=
  phaseBlock_append receipt_2_12_2403_1_join2 receipt_2_12_2403_1_join3 rfl rfl rfl
private theorem receipt_2_12_2403_1_join5 :
    phaseBlock (fastLayer (bank 2 12).shape 179798 2403 31 1 0 7 1) 0 891 = 9224827774618495250794557796 :=
  phaseBlock_append receipt_2_12_2403_1_join1 receipt_2_12_2403_1_join4 rfl rfl rfl

private theorem receipt_2_12_2403_1 : fastPhase (bank 2 12).shape 179798 2403 31 1 0 7 1 = 9224827774618495250794557796 :=
  phase_of_block (n := 891) (by decide +kernel) receipt_2_12_2403_1_join5

theorem receipt_2_12 : Checked (bank 2 12) 31 0 7 := by
  refine checked_from_values (bank 2 12) 31 0 7
    (P3_7_1.checked (bank 2 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4235_890)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_12_2402_0 receipt_2_12_2402_1 receipt_2_12_2403_0 receipt_2_12_2403_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_12_2402_0_part0 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 0) 0 128 = 482174102723463332605760928 := by decide +kernel
private theorem receipt_3_12_2402_0_part1 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 0) 128 128 = 393213395858544983377798560 := by decide +kernel
private theorem receipt_3_12_2402_0_part2 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 0) 256 128 = 309953375491862811088663968 := by decide +kernel
private theorem receipt_3_12_2402_0_part3 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 0) 384 128 = 232624507498194892582749600 := by decide +kernel
private theorem receipt_3_12_2402_0_part4 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 0) 512 128 = 161454501878391773534344608 := by decide +kernel
private theorem receipt_3_12_2402_0_part5 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 0) 640 128 = 96668322175901911977076128 := by decide +kernel
private theorem receipt_3_12_2402_0_part6 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 0) 768 128 = 38488194893297121833350560 := by decide +kernel
private theorem receipt_3_12_2402_0_part7 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 0) 896 29 = 1335593605319506685440053 := by decide +kernel
private theorem receipt_3_12_2402_0_join0 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 0) 0 256 = 875387498582008315983559488 :=
  phaseBlock_append receipt_3_12_2402_0_part0 receipt_3_12_2402_0_part1 rfl rfl rfl
private theorem receipt_3_12_2402_0_join1 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 0) 256 256 = 542577882990057703671413568 :=
  phaseBlock_append receipt_3_12_2402_0_part2 receipt_3_12_2402_0_part3 rfl rfl rfl
private theorem receipt_3_12_2402_0_join2 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 0) 0 512 = 1417965381572066019654973056 :=
  phaseBlock_append receipt_3_12_2402_0_join0 receipt_3_12_2402_0_join1 rfl rfl rfl
private theorem receipt_3_12_2402_0_join3 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 0) 512 256 = 258122824054293685511420736 :=
  phaseBlock_append receipt_3_12_2402_0_part4 receipt_3_12_2402_0_part5 rfl rfl rfl
private theorem receipt_3_12_2402_0_join4 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 0) 768 157 = 39823788498616628518790613 :=
  phaseBlock_append receipt_3_12_2402_0_part6 receipt_3_12_2402_0_part7 rfl rfl rfl
private theorem receipt_3_12_2402_0_join5 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 0) 512 413 = 297946612552910314030211349 :=
  phaseBlock_append receipt_3_12_2402_0_join3 receipt_3_12_2402_0_join4 rfl rfl rfl
private theorem receipt_3_12_2402_0_join6 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 0) 0 925 = 1715911994124976333685184405 :=
  phaseBlock_append receipt_3_12_2402_0_join2 receipt_3_12_2402_0_join5 rfl rfl rfl

private theorem receipt_3_12_2402_0 : fastPhase (bank 3 12).shape 179798 2402 31 1 1 1 0 = 1715911994124976333685184405 :=
  phase_of_block (n := 925) (by decide +kernel) receipt_3_12_2402_0_join6

private theorem receipt_3_12_2402_1_part0 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 1) 0 128 = 481466909358844994330334240 := by decide +kernel
private theorem receipt_3_12_2402_1_part1 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 1) 128 128 = 392548022050870551877116960 := by decide +kernel
private theorem receipt_3_12_2402_1_part2 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 1) 256 128 = 309331785614220755395621920 := by decide +kernel
private theorem receipt_3_12_2402_1_part3 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 1) 384 128 = 232048643207307711824561184 := by decide +kernel
private theorem receipt_3_12_2402_1_part4 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 1) 512 128 = 160926282191153757256274976 := by decide +kernel
private theorem receipt_3_12_2402_1_part5 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 1) 640 128 = 96189643545916900466172960 := by decide +kernel
private theorem receipt_3_12_2402_1_part6 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 1) 768 128 = 38060931287416266442175520 := by decide +kernel
private theorem receipt_3_12_2402_1_part7 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 1) 896 29 = 1246127020472607589767465 := by decide +kernel
private theorem receipt_3_12_2402_1_join0 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 1) 0 256 = 874014931409715546207451200 :=
  phaseBlock_append receipt_3_12_2402_1_part0 receipt_3_12_2402_1_part1 rfl rfl rfl
private theorem receipt_3_12_2402_1_join1 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 1) 256 256 = 541380428821528467220183104 :=
  phaseBlock_append receipt_3_12_2402_1_part2 receipt_3_12_2402_1_part3 rfl rfl rfl
private theorem receipt_3_12_2402_1_join2 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 1) 0 512 = 1415395360231244013427634304 :=
  phaseBlock_append receipt_3_12_2402_1_join0 receipt_3_12_2402_1_join1 rfl rfl rfl
private theorem receipt_3_12_2402_1_join3 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 1) 512 256 = 257115925737070657722447936 :=
  phaseBlock_append receipt_3_12_2402_1_part4 receipt_3_12_2402_1_part5 rfl rfl rfl
private theorem receipt_3_12_2402_1_join4 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 1) 768 157 = 39307058307888874031942985 :=
  phaseBlock_append receipt_3_12_2402_1_part6 receipt_3_12_2402_1_part7 rfl rfl rfl
private theorem receipt_3_12_2402_1_join5 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 1) 512 413 = 296422984044959531754390921 :=
  phaseBlock_append receipt_3_12_2402_1_join3 receipt_3_12_2402_1_join4 rfl rfl rfl
private theorem receipt_3_12_2402_1_join6 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2402 31 1 1 1 1) 0 925 = 1711818344276203545182025225 :=
  phaseBlock_append receipt_3_12_2402_1_join2 receipt_3_12_2402_1_join5 rfl rfl rfl

private theorem receipt_3_12_2402_1 : fastPhase (bank 3 12).shape 179798 2402 31 1 1 1 1 = 1711818344276203545182025225 :=
  phase_of_block (n := 925) (by decide +kernel) receipt_3_12_2402_1_join6

private theorem receipt_3_12_2403_0_part0 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 0) 0 128 = 482178255791609307350489248 := by decide +kernel
private theorem receipt_3_12_2403_0_part1 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 0) 128 128 = 393216293333322135908280480 := by decide +kernel
private theorem receipt_3_12_2403_0_part2 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 0) 256 128 = 309955283465784658037045408 := by decide +kernel
private theorem receipt_3_12_2403_0_part3 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 0) 384 128 = 232625664544062539892623520 := by decide +kernel
private theorem receipt_3_12_2403_0_part4 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 0) 512 128 = 161455119322206102772717728 := by decide +kernel
private theorem receipt_3_12_2403_0_part5 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 0) 640 128 = 96668584368896157344114848 := by decide +kernel
private theorem receipt_3_12_2403_0_part6 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 0) 768 128 = 38488259483089837869906080 := by decide +kernel
private theorem receipt_3_12_2403_0_part7 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 0) 896 29 = 1335594837668390969816493 := by decide +kernel
private theorem receipt_3_12_2403_0_join0 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 0) 0 256 = 875394549124931443258769728 :=
  phaseBlock_append receipt_3_12_2403_0_part0 receipt_3_12_2403_0_part1 rfl rfl rfl
private theorem receipt_3_12_2403_0_join1 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 0) 256 256 = 542580948009847197929668928 :=
  phaseBlock_append receipt_3_12_2403_0_part2 receipt_3_12_2403_0_part3 rfl rfl rfl
private theorem receipt_3_12_2403_0_join2 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 0) 0 512 = 1417975497134778641188438656 :=
  phaseBlock_append receipt_3_12_2403_0_join0 receipt_3_12_2403_0_join1 rfl rfl rfl
private theorem receipt_3_12_2403_0_join3 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 0) 512 256 = 258123703691102260116832576 :=
  phaseBlock_append receipt_3_12_2403_0_part4 receipt_3_12_2403_0_part5 rfl rfl rfl
private theorem receipt_3_12_2403_0_join4 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 0) 768 157 = 39823854320758228839722573 :=
  phaseBlock_append receipt_3_12_2403_0_part6 receipt_3_12_2403_0_part7 rfl rfl rfl
private theorem receipt_3_12_2403_0_join5 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 0) 512 413 = 297947558011860488956555149 :=
  phaseBlock_append receipt_3_12_2403_0_join3 receipt_3_12_2403_0_join4 rfl rfl rfl
private theorem receipt_3_12_2403_0_join6 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 0) 0 925 = 1715923055146639130144993805 :=
  phaseBlock_append receipt_3_12_2403_0_join2 receipt_3_12_2403_0_join5 rfl rfl rfl

private theorem receipt_3_12_2403_0 : fastPhase (bank 3 12).shape 179798 2403 31 1 1 1 0 = 1715923055146639130144993805 :=
  phase_of_block (n := 925) (by decide +kernel) receipt_3_12_2403_0_join6

private theorem receipt_3_12_2403_1_part0 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 1) 0 128 = 481471055390120237780382496 := by decide +kernel
private theorem receipt_3_12_2403_1_part1 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 1) 128 128 = 392550913918650961158021920 := by decide +kernel
private theorem receipt_3_12_2403_1_part2 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 1) 256 128 = 309333689258722784977556256 := by decide +kernel
private theorem receipt_3_12_2403_1_part3 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 1) 384 128 = 232049797050692337836819232 := by decide +kernel
private theorem receipt_3_12_2403_1_part4 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 1) 512 128 = 160926897410433028802147104 := by decide +kernel
private theorem receipt_3_12_2403_1_part5 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 1) 640 128 = 96189904344980881635599136 := by decide +kernel
private theorem receipt_3_12_2403_1_part6 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 1) 768 128 = 38060995168180369022178080 := by decide +kernel
private theorem receipt_3_12_2403_1_part7 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 1) 896 29 = 1246128172457388633299061 := by decide +kernel
private theorem receipt_3_12_2403_1_join0 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 1) 0 256 = 874021969308771198938404416 :=
  phaseBlock_append receipt_3_12_2403_1_part0 receipt_3_12_2403_1_part1 rfl rfl rfl
private theorem receipt_3_12_2403_1_join1 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 1) 256 256 = 541383486309415122814375488 :=
  phaseBlock_append receipt_3_12_2403_1_part2 receipt_3_12_2403_1_part3 rfl rfl rfl
private theorem receipt_3_12_2403_1_join2 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 1) 0 512 = 1415405455618186321752779904 :=
  phaseBlock_append receipt_3_12_2403_1_join0 receipt_3_12_2403_1_join1 rfl rfl rfl
private theorem receipt_3_12_2403_1_join3 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 1) 512 256 = 257116801755413910437746240 :=
  phaseBlock_append receipt_3_12_2403_1_part4 receipt_3_12_2403_1_part5 rfl rfl rfl
private theorem receipt_3_12_2403_1_join4 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 1) 768 157 = 39307123340637757655477141 :=
  phaseBlock_append receipt_3_12_2403_1_part6 receipt_3_12_2403_1_part7 rfl rfl rfl
private theorem receipt_3_12_2403_1_join5 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 1) 512 413 = 296423925096051668093223381 :=
  phaseBlock_append receipt_3_12_2403_1_join3 receipt_3_12_2403_1_join4 rfl rfl rfl
private theorem receipt_3_12_2403_1_join6 :
    phaseBlock (fastLayer (bank 3 12).shape 179798 2403 31 1 1 1 1) 0 925 = 1711829380714237989846003285 :=
  phaseBlock_append receipt_3_12_2403_1_join2 receipt_3_12_2403_1_join5 rfl rfl rfl

private theorem receipt_3_12_2403_1 : fastPhase (bank 3 12).shape 179798 2403 31 1 1 1 1 = 1711829380714237989846003285 :=
  phase_of_block (n := 925) (by decide +kernel) receipt_3_12_2403_1_join6

theorem receipt_3_12 : Checked (bank 3 12) 31 1 1 := by
  refine checked_from_values (bank 3 12) 31 1 1
    (P3_7_1.checked (bank 3 12) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_4235_924)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_12_2402_0 receipt_3_12_2402_1 receipt_3_12_2403_0 receipt_3_12_2403_1 (by decide +kernel) (by decide +kernel)

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
    (word : K1.I → K1_14.L) (lo : 2402 ≤ h) (hi : h ≤ 33619) (rect : Fin 4)
    (i : Fin 2) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group4_stage i)).shape
      (cutoff h rect (group4_stage i)), ¬ G∣Q :=
  (group4_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group4_avoids

end Lower6960.RescueSource
