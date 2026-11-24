import ProximityPrize.SubmissionLower.ZZZuA2c
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
section
set_option autoImplicit true
namespace qyV6B3d
open P5_7_2 (fO)
open qMHqmcc (GG receipt appendGrades)
private abbrev kA:fO:=⟨7,by decide⟩
set_option quotPrecheck false in
local notation "kU" => receipt 2542 rfl (by decide +kernel) (by decide +kernel)
private theorem dK:GG kA 12 3:=⟨kU,kU,kU,True.intro⟩
private theorem gx :GG kA 15 3:=⟨kU,kU,kU,True.intro⟩
private theorem lH :GG kA 18 3:=⟨kU,kU,kU,True.intro⟩
private theorem lp:GG kA 21 3:=⟨kU,kU,kU,True.intro⟩
theorem k :GG kA 12 12 :=
  appendGrades (appendGrades (appendGrades dK gx) lH) lp
end qyV6B3d
end
section
set_option autoImplicit true
namespace qwtjEYd
open P5_7_2 (fO)
open qMHqmcc (GG appendGrades receipt test)
private abbrev b:fO:=⟨13,by decide⟩
set_option quotPrecheck false in
local notation "az" n:arg=>receipt (b:=b) (x :=test b n) 2582 rfl
  (by decide +kernel) (by decide +kernel)
private theorem r0:GG b 0 4 :=⟨az 3,az 2,az 1,az 0,True.intro⟩
private theorem r4 :GG b 4 4 :=⟨az 7,az 6,az 5,az 4,True.intro⟩
private theorem r8:GG b 8 5:=⟨az 12,az 11,az 10,az 9,az 8,True.intro⟩
theorem lateA:GG (⟨13,by decide⟩:fO) 0 13 :=
  appendGrades (appendGrades r0 r4) r8
end qwtjEYd
end
