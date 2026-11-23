import ProximityPrize.SubmissionLower.ZlUbT2c
import ProximityPrize.SubmissionLower.ZTbuynb
import ProximityPrize.SubmissionLower.ZYV8Uma
import ProximityPrize.SubmissionLower.ZK7Ye0a
import ProximityPrize.SubmissionLower.Z7V3Ypa
import ProximityPrize.SubmissionLower.ZCvigsb
import ProximityPrize.SubmissionLower.Zf9KUOa
import ProximityPrize.SubmissionLower.ZyrUiId
import ProximityPrize.SubmissionLower.ZkTBRqe
import ProximityPrize.SubmissionLower.ZrmuHpc
import ProximityPrize.SubmissionLower.ZxOkaeb
import ProximityPrize.SubmissionLower.Zmvf5Qb
import ProximityPrize.SubmissionLower.ZiYDlxa
import ProximityPrize.SubmissionLower.ZIQZXYc
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.DG
import ProximityPrize.SubmissionLower.E2
import ProximityPrize.SubmissionLower.ZYswgKc
import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.P6Defs
set_option Elab.async false
open _root_ renaming qMHqmcc.appendGrades→aU
section
set_option autoImplicit true
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace qd4jtSc
open qMHqmcc (GG receipt)
private theorem vQj0 :GG b2 0 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQj1 :GG b2 1 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQj2 :GG b2 2 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQj3 :GG b2 3 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQj4 :GG b2 4 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQj5 :GG b2 5 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQj6 :GG b2 6 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQj7 :GG b2 7 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem r1 :GG b2 0 8:=aU (aU (aU (aU (aU (aU (aU vQj0 vQj1) vQj2) vQj3) vQj4) vQj5) vQj6) vQj7
private theorem vQj8 :GG b2 8 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQj9 :GG b2 9 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQj10 :GG b2 10 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQj11 :GG b2 11 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQj12 :GG b2 12 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQj13 :GG b2 13 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQj14 :GG b2 14 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQj15 :GG b2 15 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem r2 :GG b2 8 8:=aU (aU (aU (aU (aU (aU (aU vQj8 vQj9) vQj10) vQj11) vQj12) vQj13) vQj14) vQj15
theorem p2_0:GG b2 0 16:=aU r1 r2
end qd4jtSc
end
section
set_option autoImplicit true
namespace qd4jtSc
open qMHqmcc (GG receipts)
private theorem g2 :GG b2 0 104 :=
 aU (aU (aU (aU (aU (aU p2_0 p2_1) p2_2) p2_3) p2_4) p2_5) p2_6
private theorem g3:GG b3 0 108 :=
 aU (aU (aU (aU (aU (aU p3_0 p3_1) p3_2) p3_3) p3_4) p3_5) p3_6
theorem proof :qMHqmcc.c2 := by
 intro b hl hu x
 rcases (show b.val = 2∨b.val=3 by omega) with h | h
 · have hb:b=b2 :=Fin.ext h
   subst b
   exact receipts b2 g2 x
 · have hb:b=b3:=Fin.ext h
   subst b
   exact receipts b3 g3 x
end qd4jtSc
end
