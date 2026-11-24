import ProximityPrize.SubmissionLower.ZZZuA2c
import ProximityPrize.SubmissionLower.ZW31ykd
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
section
set_option autoImplicit true
namespace qyV6B3d
open P5_7_2 (fO)
open qMHqmcc (GG receipt appendGrades)
private abbrev kA:fO:=⟨6,by decide⟩
set_option quotPrecheck false in
local notation "kU" => receipt 2539 rfl (by decide +kernel) (by decide +kernel)
private theorem zB:GG kA 48 3:=⟨kU,kU,kU,True.intro⟩
private theorem LB:GG kA 51 3:=⟨kU,kU,kU,True.intro⟩
private theorem OD:GG kA 54 3:=⟨kU,kU,kU,True.intro⟩
private theorem Vb:GG kA 57 3:=⟨kU,kU,kU,True.intro⟩
theorem e :GG kA 48 12 :=
  appendGrades (appendGrades (appendGrades zB LB) OD) Vb
end qyV6B3d
end
section
set_option autoImplicit true
namespace qwtjEYd
open P5_7_2 (fO)
open qMHqmcc (GG appendGrades receipt test)
private abbrev b:fO:=⟨12,by decide⟩
set_option quotPrecheck false in
local notation "az" n:arg=>receipt (b:=b) (x :=test b n) 2581 rfl
  (by decide +kernel) (by decide +kernel)
private theorem a0:GG b 0 4 :=⟨az 3,az 2,az 1,az 0,True.intro⟩
private theorem a4 :GG b 4 4 :=⟨az 7,az 6,az 5,az 4,True.intro⟩
private theorem a8:GG b 8 5:=⟨az 12,az 11,az 10,az 9,az 8,True.intro⟩
theorem earlyA:GG (⟨12,by decide⟩:fO) 0 13:=appendGrades (appendGrades a0 a4) a8
end qwtjEYd
end
