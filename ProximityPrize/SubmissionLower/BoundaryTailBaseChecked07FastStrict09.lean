import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked07FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr7p128:∀ i ∈ List.range 1,StrictCheckAt 7 (128+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 128 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 7 128) 7 128:=by decide +kernel
  exact strictAtFast_sound (row 7 128) 7 128 hvalid hfast

theorem sr7p129:∀ i ∈ List.range 1,StrictCheckAt 7 (129+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 129 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 7 129) 7 129:=by decide +kernel
  exact strictAtFast_sound (row 7 129) 7 129 hvalid hfast

theorem sr7p130:∀ i ∈ List.range 1,StrictCheckAt 7 (130+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 130 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 7 130) 7 130:=by decide +kernel
  exact strictAtFast_sound (row 7 130) 7 130 hvalid hfast

theorem sr7p131:∀ i ∈ List.range 1,StrictCheckAt 7 (131+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 131 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 7 131) 7 131:=by decide +kernel
  exact strictAtFast_sound (row 7 131) 7 131 hvalid hfast

theorem sr7p132:∀ i ∈ List.range 1,StrictCheckAt 7 (132+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 132 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 7 132) 7 132:=by decide +kernel
  exact strictAtFast_sound (row 7 132) 7 132 hvalid hfast

theorem sr7p133:∀ i ∈ List.range 1,StrictCheckAt 7 (133+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 133 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 7 133) 7 133:=by decide +kernel
  exact strictAtFast_sound (row 7 133) 7 133 hvalid hfast

theorem sr7p134:∀ i ∈ List.range 1,StrictCheckAt 7 (134+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 134 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 7 134) 7 134:=by decide +kernel
  exact strictAtFast_sound (row 7 134) 7 134 hvalid hfast

theorem sr7p135:∀ i ∈ List.range 1,StrictCheckAt 7 (135+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 135 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 7 135) 7 135:=by decide +kernel
  exact strictAtFast_sound (row 7 135) 7 135 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
