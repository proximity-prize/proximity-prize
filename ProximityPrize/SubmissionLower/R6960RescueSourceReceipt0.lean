import ProximityPrize.SubmissionLower.R6960RescueSourceSchedule

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open HelperSource (WidthGuard)

private theorem moment_907_192_part0 :
    blockEstimate 907 192 192 128 = 290411680 := by decide +kernel
private theorem moment_907_192_part1 :
    blockEstimate 907 192 320 128 = 1705328752 := by decide +kernel
private theorem moment_907_192_part2 :
    blockEstimate 907 192 448 128 = 3224576064 := by decide +kernel
private theorem moment_907_192_part3 :
    blockEstimate 907 192 576 128 = 3967672384 := by decide +kernel
private theorem moment_907_192_part4 :
    blockEstimate 907 192 704 128 = 3901268032 := by decide +kernel
private theorem moment_907_192_part5 :
    blockEstimate 907 192 832 128 = 3032779128 := by decide +kernel
private theorem moment_907_192_part6 :
    blockEstimate 907 192 960 128 = 1688215192 := by decide +kernel
private theorem moment_907_192_part7 :
    blockEstimate 907 192 1088 128 = 546427967 := by decide +kernel
private theorem moment_907_192_part8 :
    blockEstimate 907 192 1216 75 = 32541889 := by decide +kernel
private theorem moment_907_192_join0 :
    blockEstimate 907 192 192 256 = 1995740432 :=
  block_append moment_907_192_part0 moment_907_192_part1 rfl rfl rfl
private theorem moment_907_192_join1 :
    blockEstimate 907 192 448 256 = 7192248448 :=
  block_append moment_907_192_part2 moment_907_192_part3 rfl rfl rfl
private theorem moment_907_192_join2 :
    blockEstimate 907 192 192 512 = 9187988880 :=
  block_append moment_907_192_join0 moment_907_192_join1 rfl rfl rfl
private theorem moment_907_192_join3 :
    blockEstimate 907 192 704 256 = 6934047160 :=
  block_append moment_907_192_part4 moment_907_192_part5 rfl rfl rfl
private theorem moment_907_192_join4 :
    blockEstimate 907 192 1088 203 = 578969856 :=
  block_append moment_907_192_part7 moment_907_192_part8 rfl rfl rfl
private theorem moment_907_192_join5 :
    blockEstimate 907 192 960 331 = 2267185048 :=
  block_append moment_907_192_part6 moment_907_192_join4 rfl rfl rfl
private theorem moment_907_192_join6 :
    blockEstimate 907 192 704 587 = 9201232208 :=
  block_append moment_907_192_join3 moment_907_192_join5 rfl rfl rfl
private theorem moment_907_192_join7 :
    blockEstimate 907 192 192 1099 = 18389221088 :=
  block_append moment_907_192_join2 moment_907_192_join6 rfl rfl rfl

theorem moment_907_192 : momentEstimate 907 192 = 18389221088 := moment_907_192_join7

private theorem moment_1257_266_part0 :
    blockEstimate 1257 266 266 128 = 415627680 := by decide +kernel
private theorem moment_1257_266_part1 :
    blockEstimate 1257 266 394 128 = 2599438752 := by decide +kernel
private theorem moment_1257_266_part2 :
    blockEstimate 1257 266 522 128 = 5961006051 := by decide +kernel
private theorem moment_1257_266_part3 :
    blockEstimate 1257 266 650 128 = 8681797632 := by decide +kernel
private theorem moment_1257_266_part4 :
    blockEstimate 1257 266 778 128 = 10282874880 := by decide +kernel
private theorem moment_1257_266_part5 :
    blockEstimate 1257 266 906 128 = 10764072960 := by decide +kernel
private theorem moment_1257_266_part6 :
    blockEstimate 1257 266 1034 128 = 10125391872 := by decide +kernel
private theorem moment_1257_266_part7 :
    blockEstimate 1257 266 1162 128 = 8369214195 := by decide +kernel
private theorem moment_1257_266_part8 :
    blockEstimate 1257 266 1290 128 = 5801507064 := by decide +kernel
private theorem moment_1257_266_part9 :
    blockEstimate 1257 266 1418 128 = 3249804063 := by decide +kernel
private theorem moment_1257_266_part10 :
    blockEstimate 1257 266 1546 128 = 1234496544 := by decide +kernel
private theorem moment_1257_266_part11 :
    blockEstimate 1257 266 1674 115 = 158591749 := by decide +kernel
private theorem moment_1257_266_join0 :
    blockEstimate 1257 266 394 256 = 8560444803 :=
  block_append moment_1257_266_part1 moment_1257_266_part2 rfl rfl rfl
private theorem moment_1257_266_join1 :
    blockEstimate 1257 266 266 384 = 8976072483 :=
  block_append moment_1257_266_part0 moment_1257_266_join0 rfl rfl rfl
private theorem moment_1257_266_join2 :
    blockEstimate 1257 266 778 256 = 21046947840 :=
  block_append moment_1257_266_part4 moment_1257_266_part5 rfl rfl rfl
private theorem moment_1257_266_join3 :
    blockEstimate 1257 266 650 384 = 29728745472 :=
  block_append moment_1257_266_part3 moment_1257_266_join2 rfl rfl rfl
private theorem moment_1257_266_join4 :
    blockEstimate 1257 266 266 768 = 38704817955 :=
  block_append moment_1257_266_join1 moment_1257_266_join3 rfl rfl rfl
private theorem moment_1257_266_join5 :
    blockEstimate 1257 266 1162 256 = 14170721259 :=
  block_append moment_1257_266_part7 moment_1257_266_part8 rfl rfl rfl
private theorem moment_1257_266_join6 :
    blockEstimate 1257 266 1034 384 = 24296113131 :=
  block_append moment_1257_266_part6 moment_1257_266_join5 rfl rfl rfl
private theorem moment_1257_266_join7 :
    blockEstimate 1257 266 1546 243 = 1393088293 :=
  block_append moment_1257_266_part10 moment_1257_266_part11 rfl rfl rfl
private theorem moment_1257_266_join8 :
    blockEstimate 1257 266 1418 371 = 4642892356 :=
  block_append moment_1257_266_part9 moment_1257_266_join7 rfl rfl rfl
private theorem moment_1257_266_join9 :
    blockEstimate 1257 266 1034 755 = 28939005487 :=
  block_append moment_1257_266_join6 moment_1257_266_join8 rfl rfl rfl
private theorem moment_1257_266_join10 :
    blockEstimate 1257 266 266 1523 = 67643823442 :=
  block_append moment_1257_266_join4 moment_1257_266_join9 rfl rfl rfl

theorem moment_1257_266 : momentEstimate 1257 266 = 67643823442 := moment_1257_266_join10

private theorem receipt_0_0_2339_0_part0 :
    phaseBlock (fastLayer (bank 0 0).shape 179827 2339 0 1 0 1 0) 0 128 = 4680742522694463842366790 := by decide +kernel
private theorem receipt_0_0_2339_0_part1 :
    phaseBlock (fastLayer (bank 0 0).shape 179827 2339 0 1 0 1 0) 128 128 = 1534704482944064005703510 := by decide +kernel
private theorem receipt_0_0_2339_0_part2 :
    phaseBlock (fastLayer (bank 0 0).shape 179827 2339 0 1 0 1 0) 256 11 = 9531515712446511454715 := by decide +kernel
private theorem receipt_0_0_2339_0_join0 :
    phaseBlock (fastLayer (bank 0 0).shape 179827 2339 0 1 0 1 0) 128 139 = 1544235998656510517158225 :=
  phaseBlock_append receipt_0_0_2339_0_part1 receipt_0_0_2339_0_part2 rfl rfl rfl
private theorem receipt_0_0_2339_0_join1 :
    phaseBlock (fastLayer (bank 0 0).shape 179827 2339 0 1 0 1 0) 0 267 = 6224978521350974359525015 :=
  phaseBlock_append receipt_0_0_2339_0_part0 receipt_0_0_2339_0_join0 rfl rfl rfl

private theorem receipt_0_0_2339_0 : fastPhase (bank 0 0).shape 179827 2339 0 1 0 1 0 = 6224978521350974359525015 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_0_0_2339_0_join1

private theorem receipt_0_0_2339_1_part0 :
    phaseBlock (fastLayer (bank 0 0).shape 179827 2339 0 1 0 1 1) 0 128 = 4653387614304656931544538 := by decide +kernel
private theorem receipt_0_0_2339_1_part1 :
    phaseBlock (fastLayer (bank 0 0).shape 179827 2339 0 1 0 1 1) 128 128 = 1513237486251473542627128 := by decide +kernel
private theorem receipt_0_0_2339_1_part2 :
    phaseBlock (fastLayer (bank 0 0).shape 179827 2339 0 1 0 1 1) 256 11 = 7937586976855527156561 := by decide +kernel
private theorem receipt_0_0_2339_1_join0 :
    phaseBlock (fastLayer (bank 0 0).shape 179827 2339 0 1 0 1 1) 128 139 = 1521175073228329069783689 :=
  phaseBlock_append receipt_0_0_2339_1_part1 receipt_0_0_2339_1_part2 rfl rfl rfl
private theorem receipt_0_0_2339_1_join1 :
    phaseBlock (fastLayer (bank 0 0).shape 179827 2339 0 1 0 1 1) 0 267 = 6174562687532986001328227 :=
  phaseBlock_append receipt_0_0_2339_1_part0 receipt_0_0_2339_1_join0 rfl rfl rfl

private theorem receipt_0_0_2339_1 : fastPhase (bank 0 0).shape 179827 2339 0 1 0 1 1 = 6174562687532986001328227 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_0_0_2339_1_join1

private theorem receipt_0_0_2340_0_part0 :
    phaseBlock (fastLayer (bank 0 0).shape 179827 2340 0 1 0 1 0) 0 128 = 4680781855334406563796184 := by decide +kernel
private theorem receipt_0_0_2340_0_part1 :
    phaseBlock (fastLayer (bank 0 0).shape 179827 2340 0 1 0 1 0) 128 128 = 1534713460110394380222500 := by decide +kernel
private theorem receipt_0_0_2340_0_part2 :
    phaseBlock (fastLayer (bank 0 0).shape 179827 2340 0 1 0 1 0) 256 11 = 9531551184242438751873 := by decide +kernel
private theorem receipt_0_0_2340_0_join0 :
    phaseBlock (fastLayer (bank 0 0).shape 179827 2340 0 1 0 1 0) 128 139 = 1544245011294636818974373 :=
  phaseBlock_append receipt_0_0_2340_0_part1 receipt_0_0_2340_0_part2 rfl rfl rfl
private theorem receipt_0_0_2340_0_join1 :
    phaseBlock (fastLayer (bank 0 0).shape 179827 2340 0 1 0 1 0) 0 267 = 6225026866629043382770557 :=
  phaseBlock_append receipt_0_0_2340_0_part0 receipt_0_0_2340_0_join0 rfl rfl rfl

private theorem receipt_0_0_2340_0 : fastPhase (bank 0 0).shape 179827 2340 0 1 0 1 0 = 6225026866629043382770557 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_0_0_2340_0_join1

private theorem receipt_0_0_2340_1_part0 :
    phaseBlock (fastLayer (bank 0 0).shape 179827 2340 0 1 0 1 1) 0 128 = 4653426756607515621728133 := by decide +kernel
private theorem receipt_0_0_2340_1_part1 :
    phaseBlock (fastLayer (bank 0 0).shape 179827 2340 0 1 0 1 1) 128 128 = 1513246356554588443092552 := by decide +kernel
private theorem receipt_0_0_2340_1_part2 :
    phaseBlock (fastLayer (bank 0 0).shape 179827 2340 0 1 0 1 1) 256 11 = 7937616630285088622601 := by decide +kernel
private theorem receipt_0_0_2340_1_join0 :
    phaseBlock (fastLayer (bank 0 0).shape 179827 2340 0 1 0 1 1) 128 139 = 1521183973184873531715153 :=
  phaseBlock_append receipt_0_0_2340_1_part1 receipt_0_0_2340_1_part2 rfl rfl rfl
private theorem receipt_0_0_2340_1_join1 :
    phaseBlock (fastLayer (bank 0 0).shape 179827 2340 0 1 0 1 1) 0 267 = 6174610729792389153443286 :=
  phaseBlock_append receipt_0_0_2340_1_part0 receipt_0_0_2340_1_join0 rfl rfl rfl

private theorem receipt_0_0_2340_1 : fastPhase (bank 0 0).shape 179827 2340 0 1 0 1 1 = 6174610729792389153443286 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_0_0_2340_1_join1

theorem receipt_0_0 : Checked (bank 0 0) 0 0 1 := by
  refine checked_from_values (bank 0 0) 0 0 1
    (P3_7_1.checked (bank 0 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1257_266)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_0_0_2339_0 receipt_0_0_2339_1 receipt_0_0_2340_0 receipt_0_0_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_1_0_2339_0_part0 :
    phaseBlock (fastLayer (bank 1 0).shape 179827 2339 0 1 0 2 0) 0 128 = 4200915111296462578635360 := by decide +kernel
private theorem receipt_1_0_2339_0_part1 :
    phaseBlock (fastLayer (bank 1 0).shape 179827 2339 0 1 0 2 0) 128 128 = 1372128712299033750988362 := by decide +kernel
private theorem receipt_1_0_2339_0_part2 :
    phaseBlock (fastLayer (bank 1 0).shape 179827 2339 0 1 0 2 0) 256 11 = 8497496301008360238879 := by decide +kernel
private theorem receipt_1_0_2339_0_join0 :
    phaseBlock (fastLayer (bank 1 0).shape 179827 2339 0 1 0 2 0) 128 139 = 1380626208600042111227241 :=
  phaseBlock_append receipt_1_0_2339_0_part1 receipt_1_0_2339_0_part2 rfl rfl rfl
private theorem receipt_1_0_2339_0_join1 :
    phaseBlock (fastLayer (bank 1 0).shape 179827 2339 0 1 0 2 0) 0 267 = 5581541319896504689862601 :=
  phaseBlock_append receipt_1_0_2339_0_part0 receipt_1_0_2339_0_join0 rfl rfl rfl

private theorem receipt_1_0_2339_0 : fastPhase (bank 1 0).shape 179827 2339 0 1 0 2 0 = 5581541319896504689862601 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_1_0_2339_0_join1

private theorem receipt_1_0_2339_1_part0 :
    phaseBlock (fastLayer (bank 1 0).shape 179827 2339 0 1 0 2 1) 0 128 = 4176232739717178186038979 := by decide +kernel
private theorem receipt_1_0_2339_1_part1 :
    phaseBlock (fastLayer (bank 1 0).shape 179827 2339 0 1 0 2 1) 128 128 = 1352901790982174149798671 := by decide +kernel
private theorem receipt_1_0_2339_1_part2 :
    phaseBlock (fastLayer (bank 1 0).shape 179827 2339 0 1 0 2 1) 256 11 = 7076328189025328673858 := by decide +kernel
private theorem receipt_1_0_2339_1_join0 :
    phaseBlock (fastLayer (bank 1 0).shape 179827 2339 0 1 0 2 1) 128 139 = 1359978119171199478472529 :=
  phaseBlock_append receipt_1_0_2339_1_part1 receipt_1_0_2339_1_part2 rfl rfl rfl
private theorem receipt_1_0_2339_1_join1 :
    phaseBlock (fastLayer (bank 1 0).shape 179827 2339 0 1 0 2 1) 0 267 = 5536210858888377664511508 :=
  phaseBlock_append receipt_1_0_2339_1_part0 receipt_1_0_2339_1_join0 rfl rfl rfl

private theorem receipt_1_0_2339_1 : fastPhase (bank 1 0).shape 179827 2339 0 1 0 2 1 = 5536210858888377664511508 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_1_0_2339_1_join1

private theorem receipt_1_0_2340_0_part0 :
    phaseBlock (fastLayer (bank 1 0).shape 179827 2340 0 1 0 2 0) 0 128 = 4200950415596566586436058 := by decide +kernel
private theorem receipt_1_0_2340_0_part1 :
    phaseBlock (fastLayer (bank 1 0).shape 179827 2340 0 1 0 2 0) 128 128 = 1372136739569275338794186 := by decide +kernel
private theorem receipt_1_0_2340_0_part2 :
    phaseBlock (fastLayer (bank 1 0).shape 179827 2340 0 1 0 2 0) 256 11 = 8497527924724073450787 := by decide +kernel
private theorem receipt_1_0_2340_0_join0 :
    phaseBlock (fastLayer (bank 1 0).shape 179827 2340 0 1 0 2 0) 128 139 = 1380634267493999412244973 :=
  phaseBlock_append receipt_1_0_2340_0_part1 receipt_1_0_2340_0_part2 rfl rfl rfl
private theorem receipt_1_0_2340_0_join1 :
    phaseBlock (fastLayer (bank 1 0).shape 179827 2340 0 1 0 2 0) 0 267 = 5581584683090565998681031 :=
  phaseBlock_append receipt_1_0_2340_0_part0 receipt_1_0_2340_0_join0 rfl rfl rfl

private theorem receipt_1_0_2340_0 : fastPhase (bank 1 0).shape 179827 2340 0 1 0 2 0 = 5581584683090565998681031 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_1_0_2340_0_join1

private theorem receipt_1_0_2340_1_part0 :
    phaseBlock (fastLayer (bank 1 0).shape 179827 2340 0 1 0 2 1) 0 128 = 4176267872062960184080923 := by decide +kernel
private theorem receipt_1_0_2340_1_part1 :
    phaseBlock (fastLayer (bank 1 0).shape 179827 2340 0 1 0 2 1) 128 128 = 1352909722486249340530730 := by decide +kernel
private theorem receipt_1_0_2340_1_part2 :
    phaseBlock (fastLayer (bank 1 0).shape 179827 2340 0 1 0 2 1) 256 11 = 7076354624978926731213 := by decide +kernel
private theorem receipt_1_0_2340_1_join0 :
    phaseBlock (fastLayer (bank 1 0).shape 179827 2340 0 1 0 2 1) 128 139 = 1359986077111228267261943 :=
  phaseBlock_append receipt_1_0_2340_1_part1 receipt_1_0_2340_1_part2 rfl rfl rfl
private theorem receipt_1_0_2340_1_join1 :
    phaseBlock (fastLayer (bank 1 0).shape 179827 2340 0 1 0 2 1) 0 267 = 5536253949174188451342866 :=
  phaseBlock_append receipt_1_0_2340_1_part0 receipt_1_0_2340_1_join0 rfl rfl rfl

private theorem receipt_1_0_2340_1 : fastPhase (bank 1 0).shape 179827 2340 0 1 0 2 1 = 5536253949174188451342866 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_1_0_2340_1_join1

theorem receipt_1_0 : Checked (bank 1 0) 0 0 2 := by
  refine checked_from_values (bank 1 0) 0 0 2
    (P3_7_1.checked (bank 1 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1257_266)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_1_0_2339_0 receipt_1_0_2339_1 receipt_1_0_2340_0 receipt_1_0_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_2_0_2339_0_part0 :
    phaseBlock (fastLayer (bank 2 0).shape 179827 2339 0 1 0 7 0) 0 128 = 2206946532517778928002980 := by decide +kernel
private theorem receipt_2_0_2339_0_part1 :
    phaseBlock (fastLayer (bank 2 0).shape 179827 2339 0 1 0 7 0) 128 128 = 700930989375578088260172 := by decide +kernel
private theorem receipt_2_0_2339_0_part2 :
    phaseBlock (fastLayer (bank 2 0).shape 179827 2339 0 1 0 7 0) 256 11 = 4249473995064112531464 := by decide +kernel
private theorem receipt_2_0_2339_0_join0 :
    phaseBlock (fastLayer (bank 2 0).shape 179827 2339 0 1 0 7 0) 128 139 = 705180463370642200791636 :=
  phaseBlock_append receipt_2_0_2339_0_part1 receipt_2_0_2339_0_part2 rfl rfl rfl
private theorem receipt_2_0_2339_0_join1 :
    phaseBlock (fastLayer (bank 2 0).shape 179827 2339 0 1 0 7 0) 0 267 = 2912126995888421128794616 :=
  phaseBlock_append receipt_2_0_2339_0_part0 receipt_2_0_2339_0_join0 rfl rfl rfl

private theorem receipt_2_0_2339_0 : fastPhase (bank 2 0).shape 179827 2339 0 1 0 7 0 = 2912126995888421128794616 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_2_0_2339_0_join1

private theorem receipt_2_0_2339_1_part0 :
    phaseBlock (fastLayer (bank 2 0).shape 179827 2339 0 1 0 7 1) 0 128 = 2193476593259805372749384 := by decide +kernel
private theorem receipt_2_0_2339_1_part1 :
    phaseBlock (fastLayer (bank 2 0).shape 179827 2339 0 1 0 7 1) 128 128 = 690980789650088524645306 := by decide +kernel
private theorem receipt_2_0_2339_1_part2 :
    phaseBlock (fastLayer (bank 2 0).shape 179827 2339 0 1 0 7 1) 256 11 = 3538186536921067811538 := by decide +kernel
private theorem receipt_2_0_2339_1_join0 :
    phaseBlock (fastLayer (bank 2 0).shape 179827 2339 0 1 0 7 1) 128 139 = 694518976187009592456844 :=
  phaseBlock_append receipt_2_0_2339_1_part1 receipt_2_0_2339_1_part2 rfl rfl rfl
private theorem receipt_2_0_2339_1_join1 :
    phaseBlock (fastLayer (bank 2 0).shape 179827 2339 0 1 0 7 1) 0 267 = 2887995569446814965206228 :=
  phaseBlock_append receipt_2_0_2339_1_part0 receipt_2_0_2339_1_join0 rfl rfl rfl

private theorem receipt_2_0_2339_1 : fastPhase (bank 2 0).shape 179827 2339 0 1 0 7 1 = 2887995569446814965206228 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_2_0_2339_1_join1

private theorem receipt_2_0_2340_0_part0 :
    phaseBlock (fastLayer (bank 2 0).shape 179827 2340 0 1 0 7 0) 0 128 = 2206965093676974715622448 := by decide +kernel
private theorem receipt_2_0_2340_0_part1 :
    phaseBlock (fastLayer (bank 2 0).shape 179827 2340 0 1 0 7 0) 128 128 = 700935094062574413712626 := by decide +kernel
private theorem receipt_2_0_2340_0_part2 :
    phaseBlock (fastLayer (bank 2 0).shape 179827 2340 0 1 0 7 0) 256 11 = 4249489809814955139467 := by decide +kernel
private theorem receipt_2_0_2340_0_join0 :
    phaseBlock (fastLayer (bank 2 0).shape 179827 2340 0 1 0 7 0) 128 139 = 705184583872389368852093 :=
  phaseBlock_append receipt_2_0_2340_0_part1 receipt_2_0_2340_0_part2 rfl rfl rfl
private theorem receipt_2_0_2340_0_join1 :
    phaseBlock (fastLayer (bank 2 0).shape 179827 2340 0 1 0 7 0) 0 267 = 2912149677549364084474541 :=
  phaseBlock_append receipt_2_0_2340_0_part0 receipt_2_0_2340_0_join0 rfl rfl rfl

private theorem receipt_2_0_2340_0 : fastPhase (bank 2 0).shape 179827 2340 0 1 0 7 0 = 2912149677549364084474541 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_2_0_2340_0_join1

private theorem receipt_2_0_2340_1_part0 :
    phaseBlock (fastLayer (bank 2 0).shape 179827 2340 0 1 0 7 1) 0 128 = 2193495059767048403485673 := by decide +kernel
private theorem receipt_2_0_2340_1_part1 :
    phaseBlock (fastLayer (bank 2 0).shape 179827 2340 0 1 0 7 1) 128 128 = 690984844572455127298120 := by decide +kernel
private theorem receipt_2_0_2340_1_part2 :
    phaseBlock (fastLayer (bank 2 0).shape 179827 2340 0 1 0 7 1) 256 11 = 3538199755114362401943 := by decide +kernel
private theorem receipt_2_0_2340_1_join0 :
    phaseBlock (fastLayer (bank 2 0).shape 179827 2340 0 1 0 7 1) 128 139 = 694523044327569489700063 :=
  phaseBlock_append receipt_2_0_2340_1_part1 receipt_2_0_2340_1_part2 rfl rfl rfl
private theorem receipt_2_0_2340_1_join1 :
    phaseBlock (fastLayer (bank 2 0).shape 179827 2340 0 1 0 7 1) 0 267 = 2888018104094617893185736 :=
  phaseBlock_append receipt_2_0_2340_1_part0 receipt_2_0_2340_1_join0 rfl rfl rfl

private theorem receipt_2_0_2340_1 : fastPhase (bank 2 0).shape 179827 2340 0 1 0 7 1 = 2888018104094617893185736 :=
  phase_of_block (n := 267) (by decide +kernel) receipt_2_0_2340_1_join1

theorem receipt_2_0 : Checked (bank 2 0) 0 0 7 := by
  refine checked_from_values (bank 2 0) 0 0 7
    (P3_7_1.checked (bank 2 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_1257_266)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_2_0_2339_0 receipt_2_0_2339_1 receipt_2_0_2340_0 receipt_2_0_2340_1 (by decide +kernel) (by decide +kernel)

private theorem receipt_3_0_2339_0_part0 :
    phaseBlock (fastLayer (bank 3 0).shape 179827 2339 0 1 1 1 0) 0 128 = 198686348756332477527552 := by decide +kernel
private theorem receipt_3_0_2339_0_part1 :
    phaseBlock (fastLayer (bank 3 0).shape 179827 2339 0 1 1 1 0) 128 65 = 21450838274245230426576 := by decide +kernel
private theorem receipt_3_0_2339_0_join0 :
    phaseBlock (fastLayer (bank 3 0).shape 179827 2339 0 1 1 1 0) 0 193 = 220137187030577707954128 :=
  phaseBlock_append receipt_3_0_2339_0_part0 receipt_3_0_2339_0_part1 rfl rfl rfl

private theorem receipt_3_0_2339_0 : fastPhase (bank 3 0).shape 179827 2339 0 1 1 1 0 = 220137187030577707954128 :=
  phase_of_block (n := 193) (by decide +kernel) receipt_3_0_2339_0_join0

private theorem receipt_3_0_2339_1_part0 :
    phaseBlock (fastLayer (bank 3 0).shape 179827 2339 0 1 1 1 1) 0 128 = 196870227972899148306240 := by decide +kernel
private theorem receipt_3_0_2339_1_part1 :
    phaseBlock (fastLayer (bank 3 0).shape 179827 2339 0 1 1 1 1) 128 65 = 20772722872842937764768 := by decide +kernel
private theorem receipt_3_0_2339_1_join0 :
    phaseBlock (fastLayer (bank 3 0).shape 179827 2339 0 1 1 1 1) 0 193 = 217642950845742086071008 :=
  phaseBlock_append receipt_3_0_2339_1_part0 receipt_3_0_2339_1_part1 rfl rfl rfl

private theorem receipt_3_0_2339_1 : fastPhase (bank 3 0).shape 179827 2339 0 1 1 1 1 = 217642950845742086071008 :=
  phase_of_block (n := 193) (by decide +kernel) receipt_3_0_2339_1_join0

private theorem receipt_3_0_2340_0_part0 :
    phaseBlock (fastLayer (bank 3 0).shape 179827 2340 0 1 1 1 0) 0 128 = 198687776830780171887680 := by decide +kernel
private theorem receipt_3_0_2340_0_part1 :
    phaseBlock (fastLayer (bank 3 0).shape 179827 2340 0 1 1 1 0) 128 65 = 21450901654841056187790 := by decide +kernel
private theorem receipt_3_0_2340_0_join0 :
    phaseBlock (fastLayer (bank 3 0).shape 179827 2340 0 1 1 1 0) 0 193 = 220138678485621228075470 :=
  phaseBlock_append receipt_3_0_2340_0_part0 receipt_3_0_2340_0_part1 rfl rfl rfl

private theorem receipt_3_0_2340_0 : fastPhase (bank 3 0).shape 179827 2340 0 1 1 1 0 = 220138678485621228075470 :=
  phase_of_block (n := 193) (by decide +kernel) receipt_3_0_2340_0_join0

private theorem receipt_3_0_2340_1_part0 :
    phaseBlock (fastLayer (bank 3 0).shape 179827 2340 0 1 1 1 1) 0 128 = 196871642066874530458304 := by decide +kernel
private theorem receipt_3_0_2340_1_part1 :
    phaseBlock (fastLayer (bank 3 0).shape 179827 2340 0 1 1 1 1) 128 65 = 20772784395540133188960 := by decide +kernel
private theorem receipt_3_0_2340_1_join0 :
    phaseBlock (fastLayer (bank 3 0).shape 179827 2340 0 1 1 1 1) 0 193 = 217644426462414663647264 :=
  phaseBlock_append receipt_3_0_2340_1_part0 receipt_3_0_2340_1_part1 rfl rfl rfl

private theorem receipt_3_0_2340_1 : fastPhase (bank 3 0).shape 179827 2340 0 1 1 1 1 = 217644426462414663647264 :=
  phase_of_block (n := 193) (by decide +kernel) receipt_3_0_2340_1_join0

theorem receipt_3_0 : Checked (bank 3 0) 0 1 1 := by
  refine checked_from_values (bank 3 0) 0 1 1
    (P3_7_1.checked (bank 3 0) rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide +kernel) (by decide) moment_907_192)
    (by decide) (by decide) (by unfold WidthGuard; decide +kernel)
    (by decide) (by decide) receipt_3_0_2339_0 receipt_3_0_2339_1 receipt_3_0_2340_0 receipt_3_0_2340_1 (by decide +kernel) (by decide +kernel)

def group0_stage (i : Fin 1) : Fin 17 :=
  ⟨0+i.val, by have := i.isLt; omega⟩

theorem group0_checked (rect : Fin 4) (i : Fin 1) :
    Checked (bank rect (group0_stage i)) (reserve (group0_stage i))
      (excess rect) (seed rect) := by
  fin_cases i
  · fin_cases rect
    · exact receipt_0_0
    · exact receipt_1_0
    · exact receipt_2_0
    · exact receipt_3_0

theorem group0_avoids {h : ℕ} {D : K1_14_1.PoleData h} (Crt : K1_14_1.CRTLift D)
    (word : K1.I → K1_14.L) (lo : 2339 ≤ h) (hi : h ≤ 33561) (rect : Fin 4)
    (i : Fin 1) {G : K1_14.Jet} (irr : Irreducible G) (seeded : K1_14_2.UsesSeed G)
    (slope : 1≤G.natDegree) (hs : seed rect≤K1_14_2_2_2_1.seedDegree G)
    (hj : G.natDegree+excess rect≤K1_14_2_2_2_1.jetDegree G) :
    ∃ Q ∈ K1_14_1.evaluated Crt word (bank rect (group0_stage i)).shape
      (cutoff h rect (group0_stage i)), ¬ G∣Q :=
  (group0_checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms group0_avoids

end Lower6960.RescueSource
