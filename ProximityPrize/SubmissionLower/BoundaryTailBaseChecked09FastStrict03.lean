import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked09FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr9p32:∀ i ∈ List.range 1,StrictCheckAt 9 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 32 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 32) 9 32:=by decide +kernel
  exact strictAtFast_sound (row 9 32) 9 32 hvalid hfast

theorem sr9p33:∀ i ∈ List.range 1,StrictCheckAt 9 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 33 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 33) 9 33:=by decide +kernel
  exact strictAtFast_sound (row 9 33) 9 33 hvalid hfast

theorem sr9p34:∀ i ∈ List.range 1,StrictCheckAt 9 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 34 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 34) 9 34:=by decide +kernel
  exact strictAtFast_sound (row 9 34) 9 34 hvalid hfast

theorem sr9p35:∀ i ∈ List.range 1,StrictCheckAt 9 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 35 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 35) 9 35:=by decide +kernel
  exact strictAtFast_sound (row 9 35) 9 35 hvalid hfast

theorem sr9p36:∀ i ∈ List.range 1,StrictCheckAt 9 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 36 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 36) 9 36:=by decide +kernel
  exact strictAtFast_sound (row 9 36) 9 36 hvalid hfast

theorem sr9p37:∀ i ∈ List.range 1,StrictCheckAt 9 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 37 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 37) 9 37:=by decide +kernel
  exact strictAtFast_sound (row 9 37) 9 37 hvalid hfast

theorem sr9p38:∀ i ∈ List.range 1,StrictCheckAt 9 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 38 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 38) 9 38:=by decide +kernel
  exact strictAtFast_sound (row 9 38) 9 38 hvalid hfast

theorem sr9p39:∀ i ∈ List.range 1,StrictCheckAt 9 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 39 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 39) 9 39:=by decide +kernel
  exact strictAtFast_sound (row 9 39) 9 39 hvalid hfast

theorem sr9p40:∀ i ∈ List.range 1,StrictCheckAt 9 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 40 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 40) 9 40:=by decide +kernel
  exact strictAtFast_sound (row 9 40) 9 40 hvalid hfast

theorem sr9p41:∀ i ∈ List.range 1,StrictCheckAt 9 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 41 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 41) 9 41:=by decide +kernel
  exact strictAtFast_sound (row 9 41) 9 41 hvalid hfast

theorem sr9p42:∀ i ∈ List.range 1,StrictCheckAt 9 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 42 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 42) 9 42:=by decide +kernel
  exact strictAtFast_sound (row 9 42) 9 42 hvalid hfast

theorem sr9p43:∀ i ∈ List.range 1,StrictCheckAt 9 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 43 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 43) 9 43:=by decide +kernel
  exact strictAtFast_sound (row 9 43) 9 43 hvalid hfast

theorem sr9p44:∀ i ∈ List.range 1,StrictCheckAt 9 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 44 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 44) 9 44:=by decide +kernel
  exact strictAtFast_sound (row 9 44) 9 44 hvalid hfast

theorem sr9p45:∀ i ∈ List.range 1,StrictCheckAt 9 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 45 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 45) 9 45:=by decide +kernel
  exact strictAtFast_sound (row 9 45) 9 45 hvalid hfast

theorem sr9p46:∀ i ∈ List.range 1,StrictCheckAt 9 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 46 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 46) 9 46:=by decide +kernel
  exact strictAtFast_sound (row 9 46) 9 46 hvalid hfast

theorem sr9p47:∀ i ∈ List.range 1,StrictCheckAt 9 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 47 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 47) 9 47:=by decide +kernel
  exact strictAtFast_sound (row 9 47) 9 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
