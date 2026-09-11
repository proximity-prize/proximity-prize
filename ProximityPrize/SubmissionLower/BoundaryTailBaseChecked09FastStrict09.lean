import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked09FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr9p128:∀ i ∈ List.range 1,StrictCheckAt 9 (128+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 128 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 128) 9 128:=by decide +kernel
  exact strictAtFast_sound (row 9 128) 9 128 hvalid hfast

theorem sr9p129:∀ i ∈ List.range 1,StrictCheckAt 9 (129+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 129 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 129) 9 129:=by decide +kernel
  exact strictAtFast_sound (row 9 129) 9 129 hvalid hfast

theorem sr9p130:∀ i ∈ List.range 1,StrictCheckAt 9 (130+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 130 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 130) 9 130:=by decide +kernel
  exact strictAtFast_sound (row 9 130) 9 130 hvalid hfast

theorem sr9p131:∀ i ∈ List.range 1,StrictCheckAt 9 (131+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 131 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 131) 9 131:=by decide +kernel
  exact strictAtFast_sound (row 9 131) 9 131 hvalid hfast

theorem sr9p132:∀ i ∈ List.range 1,StrictCheckAt 9 (132+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 132 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 132) 9 132:=by decide +kernel
  exact strictAtFast_sound (row 9 132) 9 132 hvalid hfast

theorem sr9p133:∀ i ∈ List.range 1,StrictCheckAt 9 (133+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 133 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 133) 9 133:=by decide +kernel
  exact strictAtFast_sound (row 9 133) 9 133 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
