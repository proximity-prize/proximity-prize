import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked15FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr15p32:∀ i ∈ List.range 1,StrictCheckAt 15 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 32 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 32) 15 32:=by decide +kernel
  exact strictAtFast_sound (row 15 32) 15 32 hvalid hfast

theorem sr15p33:∀ i ∈ List.range 1,StrictCheckAt 15 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 33 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 33) 15 33:=by decide +kernel
  exact strictAtFast_sound (row 15 33) 15 33 hvalid hfast

theorem sr15p34:∀ i ∈ List.range 1,StrictCheckAt 15 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 34 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 34) 15 34:=by decide +kernel
  exact strictAtFast_sound (row 15 34) 15 34 hvalid hfast

theorem sr15p35:∀ i ∈ List.range 1,StrictCheckAt 15 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 35 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 35) 15 35:=by decide +kernel
  exact strictAtFast_sound (row 15 35) 15 35 hvalid hfast

theorem sr15p36:∀ i ∈ List.range 1,StrictCheckAt 15 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 36 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 36) 15 36:=by decide +kernel
  exact strictAtFast_sound (row 15 36) 15 36 hvalid hfast

theorem sr15p37:∀ i ∈ List.range 1,StrictCheckAt 15 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 37 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 37) 15 37:=by decide +kernel
  exact strictAtFast_sound (row 15 37) 15 37 hvalid hfast

theorem sr15p38:∀ i ∈ List.range 1,StrictCheckAt 15 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 38 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 38) 15 38:=by decide +kernel
  exact strictAtFast_sound (row 15 38) 15 38 hvalid hfast

theorem sr15p39:∀ i ∈ List.range 1,StrictCheckAt 15 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 39 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 39) 15 39:=by decide +kernel
  exact strictAtFast_sound (row 15 39) 15 39 hvalid hfast

theorem sr15p40:∀ i ∈ List.range 1,StrictCheckAt 15 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 40 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 40) 15 40:=by decide +kernel
  exact strictAtFast_sound (row 15 40) 15 40 hvalid hfast

theorem sr15p41:∀ i ∈ List.range 1,StrictCheckAt 15 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 41 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 41) 15 41:=by decide +kernel
  exact strictAtFast_sound (row 15 41) 15 41 hvalid hfast

theorem sr15p42:∀ i ∈ List.range 1,StrictCheckAt 15 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 42 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 42) 15 42:=by decide +kernel
  exact strictAtFast_sound (row 15 42) 15 42 hvalid hfast

theorem sr15p43:∀ i ∈ List.range 1,StrictCheckAt 15 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 43 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 43) 15 43:=by decide +kernel
  exact strictAtFast_sound (row 15 43) 15 43 hvalid hfast

theorem sr15p44:∀ i ∈ List.range 1,StrictCheckAt 15 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 44 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 44) 15 44:=by decide +kernel
  exact strictAtFast_sound (row 15 44) 15 44 hvalid hfast

theorem sr15p45:∀ i ∈ List.range 1,StrictCheckAt 15 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 45 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 45) 15 45:=by decide +kernel
  exact strictAtFast_sound (row 15 45) 15 45 hvalid hfast

theorem sr15p46:∀ i ∈ List.range 1,StrictCheckAt 15 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 46 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 46) 15 46:=by decide +kernel
  exact strictAtFast_sound (row 15 46) 15 46 hvalid hfast

theorem sr15p47:∀ i ∈ List.range 1,StrictCheckAt 15 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 47 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 47) 15 47:=by decide +kernel
  exact strictAtFast_sound (row 15 47) 15 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
