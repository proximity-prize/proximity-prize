import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked29FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr29p32:∀ i ∈ List.range 1,StrictCheckAt 29 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 32 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 32) 29 32:=by decide +kernel
  exact strictAtFast_sound (row 29 32) 29 32 hvalid hfast

theorem sr29p33:∀ i ∈ List.range 1,StrictCheckAt 29 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 33 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 33) 29 33:=by decide +kernel
  exact strictAtFast_sound (row 29 33) 29 33 hvalid hfast

theorem sr29p34:∀ i ∈ List.range 1,StrictCheckAt 29 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 34 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 34) 29 34:=by decide +kernel
  exact strictAtFast_sound (row 29 34) 29 34 hvalid hfast

theorem sr29p35:∀ i ∈ List.range 1,StrictCheckAt 29 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 35 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 35) 29 35:=by decide +kernel
  exact strictAtFast_sound (row 29 35) 29 35 hvalid hfast

theorem sr29p36:∀ i ∈ List.range 1,StrictCheckAt 29 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 36 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 36) 29 36:=by decide +kernel
  exact strictAtFast_sound (row 29 36) 29 36 hvalid hfast

theorem sr29p37:∀ i ∈ List.range 1,StrictCheckAt 29 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 37 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 37) 29 37:=by decide +kernel
  exact strictAtFast_sound (row 29 37) 29 37 hvalid hfast

theorem sr29p38:∀ i ∈ List.range 1,StrictCheckAt 29 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 38 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 38) 29 38:=by decide +kernel
  exact strictAtFast_sound (row 29 38) 29 38 hvalid hfast

theorem sr29p39:∀ i ∈ List.range 1,StrictCheckAt 29 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 39 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 39) 29 39:=by decide +kernel
  exact strictAtFast_sound (row 29 39) 29 39 hvalid hfast

theorem sr29p40:∀ i ∈ List.range 1,StrictCheckAt 29 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 40 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 40) 29 40:=by decide +kernel
  exact strictAtFast_sound (row 29 40) 29 40 hvalid hfast

theorem sr29p41:∀ i ∈ List.range 1,StrictCheckAt 29 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 41 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 41) 29 41:=by decide +kernel
  exact strictAtFast_sound (row 29 41) 29 41 hvalid hfast

theorem sr29p42:∀ i ∈ List.range 1,StrictCheckAt 29 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 42 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 42) 29 42:=by decide +kernel
  exact strictAtFast_sound (row 29 42) 29 42 hvalid hfast

theorem sr29p43:∀ i ∈ List.range 1,StrictCheckAt 29 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 43 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 43) 29 43:=by decide +kernel
  exact strictAtFast_sound (row 29 43) 29 43 hvalid hfast

theorem sr29p44:∀ i ∈ List.range 1,StrictCheckAt 29 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 44 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 44) 29 44:=by decide +kernel
  exact strictAtFast_sound (row 29 44) 29 44 hvalid hfast

theorem sr29p45:∀ i ∈ List.range 1,StrictCheckAt 29 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 45 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 45) 29 45:=by decide +kernel
  exact strictAtFast_sound (row 29 45) 29 45 hvalid hfast

theorem sr29p46:∀ i ∈ List.range 1,StrictCheckAt 29 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 46 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 46) 29 46:=by decide +kernel
  exact strictAtFast_sound (row 29 46) 29 46 hvalid hfast

theorem sr29p47:∀ i ∈ List.range 1,StrictCheckAt 29 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 47 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 47) 29 47:=by decide +kernel
  exact strictAtFast_sound (row 29 47) 29 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
