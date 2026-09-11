import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked13FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr13p32:∀ i ∈ List.range 1,StrictCheckAt 13 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 32 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 32) 13 32:=by decide +kernel
  exact strictAtFast_sound (row 13 32) 13 32 hvalid hfast

theorem sr13p33:∀ i ∈ List.range 1,StrictCheckAt 13 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 33 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 33) 13 33:=by decide +kernel
  exact strictAtFast_sound (row 13 33) 13 33 hvalid hfast

theorem sr13p34:∀ i ∈ List.range 1,StrictCheckAt 13 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 34 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 34) 13 34:=by decide +kernel
  exact strictAtFast_sound (row 13 34) 13 34 hvalid hfast

theorem sr13p35:∀ i ∈ List.range 1,StrictCheckAt 13 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 35 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 35) 13 35:=by decide +kernel
  exact strictAtFast_sound (row 13 35) 13 35 hvalid hfast

theorem sr13p36:∀ i ∈ List.range 1,StrictCheckAt 13 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 36 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 36) 13 36:=by decide +kernel
  exact strictAtFast_sound (row 13 36) 13 36 hvalid hfast

theorem sr13p37:∀ i ∈ List.range 1,StrictCheckAt 13 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 37 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 37) 13 37:=by decide +kernel
  exact strictAtFast_sound (row 13 37) 13 37 hvalid hfast

theorem sr13p38:∀ i ∈ List.range 1,StrictCheckAt 13 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 38 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 38) 13 38:=by decide +kernel
  exact strictAtFast_sound (row 13 38) 13 38 hvalid hfast

theorem sr13p39:∀ i ∈ List.range 1,StrictCheckAt 13 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 39 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 39) 13 39:=by decide +kernel
  exact strictAtFast_sound (row 13 39) 13 39 hvalid hfast

theorem sr13p40:∀ i ∈ List.range 1,StrictCheckAt 13 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 40 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 40) 13 40:=by decide +kernel
  exact strictAtFast_sound (row 13 40) 13 40 hvalid hfast

theorem sr13p41:∀ i ∈ List.range 1,StrictCheckAt 13 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 41 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 41) 13 41:=by decide +kernel
  exact strictAtFast_sound (row 13 41) 13 41 hvalid hfast

theorem sr13p42:∀ i ∈ List.range 1,StrictCheckAt 13 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 42 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 42) 13 42:=by decide +kernel
  exact strictAtFast_sound (row 13 42) 13 42 hvalid hfast

theorem sr13p43:∀ i ∈ List.range 1,StrictCheckAt 13 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 43 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 43) 13 43:=by decide +kernel
  exact strictAtFast_sound (row 13 43) 13 43 hvalid hfast

theorem sr13p44:∀ i ∈ List.range 1,StrictCheckAt 13 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 44 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 44) 13 44:=by decide +kernel
  exact strictAtFast_sound (row 13 44) 13 44 hvalid hfast

theorem sr13p45:∀ i ∈ List.range 1,StrictCheckAt 13 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 45 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 45) 13 45:=by decide +kernel
  exact strictAtFast_sound (row 13 45) 13 45 hvalid hfast

theorem sr13p46:∀ i ∈ List.range 1,StrictCheckAt 13 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 46 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 46) 13 46:=by decide +kernel
  exact strictAtFast_sound (row 13 46) 13 46 hvalid hfast

theorem sr13p47:∀ i ∈ List.range 1,StrictCheckAt 13 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 47 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 47) 13 47:=by decide +kernel
  exact strictAtFast_sound (row 13 47) 13 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
