import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked26FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr26p112:∀ i ∈ List.range 1,StrictCheckAt 26 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 112 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 26 112) 26 112:=by decide +kernel
  exact strictAtFast_sound (row 26 112) 26 112 hvalid hfast

theorem sr26p113:∀ i ∈ List.range 1,StrictCheckAt 26 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 113 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 26 113) 26 113:=by decide +kernel
  exact strictAtFast_sound (row 26 113) 26 113 hvalid hfast

theorem sr26p114:∀ i ∈ List.range 1,StrictCheckAt 26 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 114 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 26 114) 26 114:=by decide +kernel
  exact strictAtFast_sound (row 26 114) 26 114 hvalid hfast

theorem sr26p115:∀ i ∈ List.range 1,StrictCheckAt 26 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 115 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 26 115) 26 115:=by decide +kernel
  exact strictAtFast_sound (row 26 115) 26 115 hvalid hfast

theorem sr26p116:∀ i ∈ List.range 1,StrictCheckAt 26 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 116 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 26 116) 26 116:=by decide +kernel
  exact strictAtFast_sound (row 26 116) 26 116 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
