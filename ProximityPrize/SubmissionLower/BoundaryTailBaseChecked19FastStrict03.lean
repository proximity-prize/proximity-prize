import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked19FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr19p32:∀ i ∈ List.range 1,StrictCheckAt 19 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 32 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 19 32) 19 32:=by decide +kernel
  exact strictAtFast_sound (row 19 32) 19 32 hvalid hfast

theorem sr19p33:∀ i ∈ List.range 1,StrictCheckAt 19 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 33 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 19 33) 19 33:=by decide +kernel
  exact strictAtFast_sound (row 19 33) 19 33 hvalid hfast

theorem sr19p34:∀ i ∈ List.range 1,StrictCheckAt 19 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 34 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 19 34) 19 34:=by decide +kernel
  exact strictAtFast_sound (row 19 34) 19 34 hvalid hfast

theorem sr19p35:∀ i ∈ List.range 1,StrictCheckAt 19 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 35 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 19 35) 19 35:=by decide +kernel
  exact strictAtFast_sound (row 19 35) 19 35 hvalid hfast

theorem sr19p36:∀ i ∈ List.range 1,StrictCheckAt 19 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 36 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 19 36) 19 36:=by decide +kernel
  exact strictAtFast_sound (row 19 36) 19 36 hvalid hfast

theorem sr19p37:∀ i ∈ List.range 1,StrictCheckAt 19 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 37 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 19 37) 19 37:=by decide +kernel
  exact strictAtFast_sound (row 19 37) 19 37 hvalid hfast

theorem sr19p38:∀ i ∈ List.range 1,StrictCheckAt 19 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 38 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 19 38) 19 38:=by decide +kernel
  exact strictAtFast_sound (row 19 38) 19 38 hvalid hfast

theorem sr19p39:∀ i ∈ List.range 1,StrictCheckAt 19 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 39 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 19 39) 19 39:=by decide +kernel
  exact strictAtFast_sound (row 19 39) 19 39 hvalid hfast

theorem sr19p40:∀ i ∈ List.range 1,StrictCheckAt 19 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 40 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 19 40) 19 40:=by decide +kernel
  exact strictAtFast_sound (row 19 40) 19 40 hvalid hfast

theorem sr19p41:∀ i ∈ List.range 1,StrictCheckAt 19 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 41 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 19 41) 19 41:=by decide +kernel
  exact strictAtFast_sound (row 19 41) 19 41 hvalid hfast

theorem sr19p42:∀ i ∈ List.range 1,StrictCheckAt 19 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 42 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 19 42) 19 42:=by decide +kernel
  exact strictAtFast_sound (row 19 42) 19 42 hvalid hfast

theorem sr19p43:∀ i ∈ List.range 1,StrictCheckAt 19 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 43 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 19 43) 19 43:=by decide +kernel
  exact strictAtFast_sound (row 19 43) 19 43 hvalid hfast

theorem sr19p44:∀ i ∈ List.range 1,StrictCheckAt 19 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 44 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 19 44) 19 44:=by decide +kernel
  exact strictAtFast_sound (row 19 44) 19 44 hvalid hfast

theorem sr19p45:∀ i ∈ List.range 1,StrictCheckAt 19 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 45 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 19 45) 19 45:=by decide +kernel
  exact strictAtFast_sound (row 19 45) 19 45 hvalid hfast

theorem sr19p46:∀ i ∈ List.range 1,StrictCheckAt 19 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 46 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 19 46) 19 46:=by decide +kernel
  exact strictAtFast_sound (row 19 46) 19 46 hvalid hfast

theorem sr19p47:∀ i ∈ List.range 1,StrictCheckAt 19 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 47 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 19 47) 19 47:=by decide +kernel
  exact strictAtFast_sound (row 19 47) 19 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
