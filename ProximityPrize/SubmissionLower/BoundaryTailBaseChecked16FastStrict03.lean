import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked16FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr16p32:∀ i ∈ List.range 1,StrictCheckAt 16 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 32 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 32) 16 32:=by decide +kernel
  exact strictAtFast_sound (row 16 32) 16 32 hvalid hfast

theorem sr16p33:∀ i ∈ List.range 1,StrictCheckAt 16 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 33 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 33) 16 33:=by decide +kernel
  exact strictAtFast_sound (row 16 33) 16 33 hvalid hfast

theorem sr16p34:∀ i ∈ List.range 1,StrictCheckAt 16 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 34 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 34) 16 34:=by decide +kernel
  exact strictAtFast_sound (row 16 34) 16 34 hvalid hfast

theorem sr16p35:∀ i ∈ List.range 1,StrictCheckAt 16 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 35 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 35) 16 35:=by decide +kernel
  exact strictAtFast_sound (row 16 35) 16 35 hvalid hfast

theorem sr16p36:∀ i ∈ List.range 1,StrictCheckAt 16 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 36 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 36) 16 36:=by decide +kernel
  exact strictAtFast_sound (row 16 36) 16 36 hvalid hfast

theorem sr16p37:∀ i ∈ List.range 1,StrictCheckAt 16 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 37 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 37) 16 37:=by decide +kernel
  exact strictAtFast_sound (row 16 37) 16 37 hvalid hfast

theorem sr16p38:∀ i ∈ List.range 1,StrictCheckAt 16 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 38 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 38) 16 38:=by decide +kernel
  exact strictAtFast_sound (row 16 38) 16 38 hvalid hfast

theorem sr16p39:∀ i ∈ List.range 1,StrictCheckAt 16 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 39 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 39) 16 39:=by decide +kernel
  exact strictAtFast_sound (row 16 39) 16 39 hvalid hfast

theorem sr16p40:∀ i ∈ List.range 1,StrictCheckAt 16 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 40 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 40) 16 40:=by decide +kernel
  exact strictAtFast_sound (row 16 40) 16 40 hvalid hfast

theorem sr16p41:∀ i ∈ List.range 1,StrictCheckAt 16 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 41 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 41) 16 41:=by decide +kernel
  exact strictAtFast_sound (row 16 41) 16 41 hvalid hfast

theorem sr16p42:∀ i ∈ List.range 1,StrictCheckAt 16 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 42 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 42) 16 42:=by decide +kernel
  exact strictAtFast_sound (row 16 42) 16 42 hvalid hfast

theorem sr16p43:∀ i ∈ List.range 1,StrictCheckAt 16 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 43 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 43) 16 43:=by decide +kernel
  exact strictAtFast_sound (row 16 43) 16 43 hvalid hfast

theorem sr16p44:∀ i ∈ List.range 1,StrictCheckAt 16 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 44 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 44) 16 44:=by decide +kernel
  exact strictAtFast_sound (row 16 44) 16 44 hvalid hfast

theorem sr16p45:∀ i ∈ List.range 1,StrictCheckAt 16 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 45 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 45) 16 45:=by decide +kernel
  exact strictAtFast_sound (row 16 45) 16 45 hvalid hfast

theorem sr16p46:∀ i ∈ List.range 1,StrictCheckAt 16 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 46 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 46) 16 46:=by decide +kernel
  exact strictAtFast_sound (row 16 46) 16 46 hvalid hfast

theorem sr16p47:∀ i ∈ List.range 1,StrictCheckAt 16 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 47 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 47) 16 47:=by decide +kernel
  exact strictAtFast_sound (row 16 47) 16 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
