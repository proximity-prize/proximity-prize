import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked27FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr27p32:∀ i ∈ List.range 1,StrictCheckAt 27 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 32 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 27 32) 27 32:=by decide +kernel
  exact strictAtFast_sound (row 27 32) 27 32 hvalid hfast

theorem sr27p33:∀ i ∈ List.range 1,StrictCheckAt 27 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 33 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 27 33) 27 33:=by decide +kernel
  exact strictAtFast_sound (row 27 33) 27 33 hvalid hfast

theorem sr27p34:∀ i ∈ List.range 1,StrictCheckAt 27 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 34 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 27 34) 27 34:=by decide +kernel
  exact strictAtFast_sound (row 27 34) 27 34 hvalid hfast

theorem sr27p35:∀ i ∈ List.range 1,StrictCheckAt 27 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 35 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 27 35) 27 35:=by decide +kernel
  exact strictAtFast_sound (row 27 35) 27 35 hvalid hfast

theorem sr27p36:∀ i ∈ List.range 1,StrictCheckAt 27 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 36 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 27 36) 27 36:=by decide +kernel
  exact strictAtFast_sound (row 27 36) 27 36 hvalid hfast

theorem sr27p37:∀ i ∈ List.range 1,StrictCheckAt 27 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 37 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 27 37) 27 37:=by decide +kernel
  exact strictAtFast_sound (row 27 37) 27 37 hvalid hfast

theorem sr27p38:∀ i ∈ List.range 1,StrictCheckAt 27 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 38 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 27 38) 27 38:=by decide +kernel
  exact strictAtFast_sound (row 27 38) 27 38 hvalid hfast

theorem sr27p39:∀ i ∈ List.range 1,StrictCheckAt 27 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 39 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 27 39) 27 39:=by decide +kernel
  exact strictAtFast_sound (row 27 39) 27 39 hvalid hfast

theorem sr27p40:∀ i ∈ List.range 1,StrictCheckAt 27 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 40 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 27 40) 27 40:=by decide +kernel
  exact strictAtFast_sound (row 27 40) 27 40 hvalid hfast

theorem sr27p41:∀ i ∈ List.range 1,StrictCheckAt 27 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 41 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 27 41) 27 41:=by decide +kernel
  exact strictAtFast_sound (row 27 41) 27 41 hvalid hfast

theorem sr27p42:∀ i ∈ List.range 1,StrictCheckAt 27 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 42 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 27 42) 27 42:=by decide +kernel
  exact strictAtFast_sound (row 27 42) 27 42 hvalid hfast

theorem sr27p43:∀ i ∈ List.range 1,StrictCheckAt 27 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 43 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 27 43) 27 43:=by decide +kernel
  exact strictAtFast_sound (row 27 43) 27 43 hvalid hfast

theorem sr27p44:∀ i ∈ List.range 1,StrictCheckAt 27 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 44 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 27 44) 27 44:=by decide +kernel
  exact strictAtFast_sound (row 27 44) 27 44 hvalid hfast

theorem sr27p45:∀ i ∈ List.range 1,StrictCheckAt 27 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 45 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 27 45) 27 45:=by decide +kernel
  exact strictAtFast_sound (row 27 45) 27 45 hvalid hfast

theorem sr27p46:∀ i ∈ List.range 1,StrictCheckAt 27 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 46 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 27 46) 27 46:=by decide +kernel
  exact strictAtFast_sound (row 27 46) 27 46 hvalid hfast

theorem sr27p47:∀ i ∈ List.range 1,StrictCheckAt 27 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 47 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 27 47) 27 47:=by decide +kernel
  exact strictAtFast_sound (row 27 47) 27 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
