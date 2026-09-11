import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked31FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr31p32:∀ i ∈ List.range 1,StrictCheckAt 31 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 32 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 32) 31 32:=by decide +kernel
  exact strictAtFast_sound (row 31 32) 31 32 hvalid hfast

theorem sr31p33:∀ i ∈ List.range 1,StrictCheckAt 31 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 33 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 33) 31 33:=by decide +kernel
  exact strictAtFast_sound (row 31 33) 31 33 hvalid hfast

theorem sr31p34:∀ i ∈ List.range 1,StrictCheckAt 31 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 34 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 34) 31 34:=by decide +kernel
  exact strictAtFast_sound (row 31 34) 31 34 hvalid hfast

theorem sr31p35:∀ i ∈ List.range 1,StrictCheckAt 31 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 35 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 35) 31 35:=by decide +kernel
  exact strictAtFast_sound (row 31 35) 31 35 hvalid hfast

theorem sr31p36:∀ i ∈ List.range 1,StrictCheckAt 31 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 36 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 36) 31 36:=by decide +kernel
  exact strictAtFast_sound (row 31 36) 31 36 hvalid hfast

theorem sr31p37:∀ i ∈ List.range 1,StrictCheckAt 31 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 37 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 37) 31 37:=by decide +kernel
  exact strictAtFast_sound (row 31 37) 31 37 hvalid hfast

theorem sr31p38:∀ i ∈ List.range 1,StrictCheckAt 31 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 38 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 38) 31 38:=by decide +kernel
  exact strictAtFast_sound (row 31 38) 31 38 hvalid hfast

theorem sr31p39:∀ i ∈ List.range 1,StrictCheckAt 31 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 39 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 39) 31 39:=by decide +kernel
  exact strictAtFast_sound (row 31 39) 31 39 hvalid hfast

theorem sr31p40:∀ i ∈ List.range 1,StrictCheckAt 31 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 40 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 40) 31 40:=by decide +kernel
  exact strictAtFast_sound (row 31 40) 31 40 hvalid hfast

theorem sr31p41:∀ i ∈ List.range 1,StrictCheckAt 31 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 41 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 41) 31 41:=by decide +kernel
  exact strictAtFast_sound (row 31 41) 31 41 hvalid hfast

theorem sr31p42:∀ i ∈ List.range 1,StrictCheckAt 31 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 42 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 42) 31 42:=by decide +kernel
  exact strictAtFast_sound (row 31 42) 31 42 hvalid hfast

theorem sr31p43:∀ i ∈ List.range 1,StrictCheckAt 31 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 43 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 43) 31 43:=by decide +kernel
  exact strictAtFast_sound (row 31 43) 31 43 hvalid hfast

theorem sr31p44:∀ i ∈ List.range 1,StrictCheckAt 31 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 44 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 44) 31 44:=by decide +kernel
  exact strictAtFast_sound (row 31 44) 31 44 hvalid hfast

theorem sr31p45:∀ i ∈ List.range 1,StrictCheckAt 31 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 45 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 45) 31 45:=by decide +kernel
  exact strictAtFast_sound (row 31 45) 31 45 hvalid hfast

theorem sr31p46:∀ i ∈ List.range 1,StrictCheckAt 31 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 46 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 46) 31 46:=by decide +kernel
  exact strictAtFast_sound (row 31 46) 31 46 hvalid hfast

theorem sr31p47:∀ i ∈ List.range 1,StrictCheckAt 31 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 47 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 47) 31 47:=by decide +kernel
  exact strictAtFast_sound (row 31 47) 31 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
