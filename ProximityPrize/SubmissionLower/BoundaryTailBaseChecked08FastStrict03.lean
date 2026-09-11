import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked08FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr8p32:∀ i ∈ List.range 1,StrictCheckAt 8 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 32 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 32) 8 32:=by decide +kernel
  exact strictAtFast_sound (row 8 32) 8 32 hvalid hfast

theorem sr8p33:∀ i ∈ List.range 1,StrictCheckAt 8 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 33 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 33) 8 33:=by decide +kernel
  exact strictAtFast_sound (row 8 33) 8 33 hvalid hfast

theorem sr8p34:∀ i ∈ List.range 1,StrictCheckAt 8 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 34 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 34) 8 34:=by decide +kernel
  exact strictAtFast_sound (row 8 34) 8 34 hvalid hfast

theorem sr8p35:∀ i ∈ List.range 1,StrictCheckAt 8 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 35 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 35) 8 35:=by decide +kernel
  exact strictAtFast_sound (row 8 35) 8 35 hvalid hfast

theorem sr8p36:∀ i ∈ List.range 1,StrictCheckAt 8 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 36 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 36) 8 36:=by decide +kernel
  exact strictAtFast_sound (row 8 36) 8 36 hvalid hfast

theorem sr8p37:∀ i ∈ List.range 1,StrictCheckAt 8 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 37 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 37) 8 37:=by decide +kernel
  exact strictAtFast_sound (row 8 37) 8 37 hvalid hfast

theorem sr8p38:∀ i ∈ List.range 1,StrictCheckAt 8 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 38 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 38) 8 38:=by decide +kernel
  exact strictAtFast_sound (row 8 38) 8 38 hvalid hfast

theorem sr8p39:∀ i ∈ List.range 1,StrictCheckAt 8 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 39 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 39) 8 39:=by decide +kernel
  exact strictAtFast_sound (row 8 39) 8 39 hvalid hfast

theorem sr8p40:∀ i ∈ List.range 1,StrictCheckAt 8 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 40 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 40) 8 40:=by decide +kernel
  exact strictAtFast_sound (row 8 40) 8 40 hvalid hfast

theorem sr8p41:∀ i ∈ List.range 1,StrictCheckAt 8 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 41 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 41) 8 41:=by decide +kernel
  exact strictAtFast_sound (row 8 41) 8 41 hvalid hfast

theorem sr8p42:∀ i ∈ List.range 1,StrictCheckAt 8 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 42 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 42) 8 42:=by decide +kernel
  exact strictAtFast_sound (row 8 42) 8 42 hvalid hfast

theorem sr8p43:∀ i ∈ List.range 1,StrictCheckAt 8 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 43 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 43) 8 43:=by decide +kernel
  exact strictAtFast_sound (row 8 43) 8 43 hvalid hfast

theorem sr8p44:∀ i ∈ List.range 1,StrictCheckAt 8 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 44 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 44) 8 44:=by decide +kernel
  exact strictAtFast_sound (row 8 44) 8 44 hvalid hfast

theorem sr8p45:∀ i ∈ List.range 1,StrictCheckAt 8 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 45 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 45) 8 45:=by decide +kernel
  exact strictAtFast_sound (row 8 45) 8 45 hvalid hfast

theorem sr8p46:∀ i ∈ List.range 1,StrictCheckAt 8 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 46 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 46) 8 46:=by decide +kernel
  exact strictAtFast_sound (row 8 46) 8 46 hvalid hfast

theorem sr8p47:∀ i ∈ List.range 1,StrictCheckAt 8 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 47 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 47) 8 47:=by decide +kernel
  exact strictAtFast_sound (row 8 47) 8 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
