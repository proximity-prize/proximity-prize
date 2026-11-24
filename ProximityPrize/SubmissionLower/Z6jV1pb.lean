import ProximityPrize.SubmissionLower.ZlUbT2c
set_option Elab.async false
section
set_option autoImplicit true
namespace q3UL7Tb
open P5_7_2 (fO)
abbrev b4 :fO:=⟨4,by decide⟩
abbrev b5:fO:=⟨5,by decide⟩
end q3UL7Tb
end
section
set_option autoImplicit true
namespace qgVOTOa
open P5_7_2 (fO)
abbrev b8:fO:=⟨8,by decide⟩
abbrev b9:fO:=⟨9,by decide⟩
end qgVOTOa
end
section
set_option autoImplicit true
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace qJrKOKe
open P5_7_2 (fO)
open qMHqmcc (GG receipt appendGrades)
abbrev b10 :fO:=⟨10,by decide⟩
set_option quotPrecheck false in
local notation "az" => (receipt 2565 rfl (by decide +kernel) (by decide +kernel))
private theorem r1 :GG b10 0 4 :=⟨az,az,az,az,True.intro⟩
private theorem r2 :GG b10 4 4 :=⟨az,az,az,az,True.intro⟩
private theorem r3:GG b10 8 4 :=⟨az,az,az,az,True.intro⟩
theorem a :GG b10 0 12 :=appendGrades (appendGrades r1 r2) r3
end qJrKOKe
end
