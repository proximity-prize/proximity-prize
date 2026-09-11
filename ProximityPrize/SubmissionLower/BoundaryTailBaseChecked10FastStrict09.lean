import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr10p128:∀ i ∈ List.range 1,StrictCheckAt 10 (128+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 128 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 128) 10 128:=by decide +kernel
  exact strictAtFast_sound (row 10 128) 10 128 hvalid hfast

theorem sr10p129:∀ i ∈ List.range 1,StrictCheckAt 10 (129+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 129 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 129) 10 129:=by decide +kernel
  exact strictAtFast_sound (row 10 129) 10 129 hvalid hfast

theorem sr10p130:∀ i ∈ List.range 1,StrictCheckAt 10 (130+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 130 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 130) 10 130:=by decide +kernel
  exact strictAtFast_sound (row 10 130) 10 130 hvalid hfast

theorem sr10p131:∀ i ∈ List.range 1,StrictCheckAt 10 (131+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 131 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 131) 10 131:=by decide +kernel
  exact strictAtFast_sound (row 10 131) 10 131 hvalid hfast

theorem sr10p132:∀ i ∈ List.range 1,StrictCheckAt 10 (132+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 132 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 132) 10 132:=by decide +kernel
  exact strictAtFast_sound (row 10 132) 10 132 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
