import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked11FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr11p128:∀ i ∈ List.range 1,StrictCheckAt 11 (128+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 128 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 128) 11 128:=by decide +kernel
  exact strictAtFast_sound (row 11 128) 11 128 hvalid hfast

theorem sr11p129:∀ i ∈ List.range 1,StrictCheckAt 11 (129+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 129 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 129) 11 129:=by decide +kernel
  exact strictAtFast_sound (row 11 129) 11 129 hvalid hfast

theorem sr11p130:∀ i ∈ List.range 1,StrictCheckAt 11 (130+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 130 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 130) 11 130:=by decide +kernel
  exact strictAtFast_sound (row 11 130) 11 130 hvalid hfast

theorem sr11p131:∀ i ∈ List.range 1,StrictCheckAt 11 (131+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 131 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 131) 11 131:=by decide +kernel
  exact strictAtFast_sound (row 11 131) 11 131 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
