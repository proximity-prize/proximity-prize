import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr18p32:∀ i ∈ List.range 1,StrictCheckAt 18 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 32 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 32) 18 32:=by decide +kernel
  exact strictAtFast_sound (row 18 32) 18 32 hvalid hfast

theorem sr18p33:∀ i ∈ List.range 1,StrictCheckAt 18 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 33 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 33) 18 33:=by decide +kernel
  exact strictAtFast_sound (row 18 33) 18 33 hvalid hfast

theorem sr18p34:∀ i ∈ List.range 1,StrictCheckAt 18 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 34 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 34) 18 34:=by decide +kernel
  exact strictAtFast_sound (row 18 34) 18 34 hvalid hfast

theorem sr18p35:∀ i ∈ List.range 1,StrictCheckAt 18 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 35 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 35) 18 35:=by decide +kernel
  exact strictAtFast_sound (row 18 35) 18 35 hvalid hfast

theorem sr18p36:∀ i ∈ List.range 1,StrictCheckAt 18 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 36 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 36) 18 36:=by decide +kernel
  exact strictAtFast_sound (row 18 36) 18 36 hvalid hfast

theorem sr18p37:∀ i ∈ List.range 1,StrictCheckAt 18 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 37 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 37) 18 37:=by decide +kernel
  exact strictAtFast_sound (row 18 37) 18 37 hvalid hfast

theorem sr18p38:∀ i ∈ List.range 1,StrictCheckAt 18 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 38 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 38) 18 38:=by decide +kernel
  exact strictAtFast_sound (row 18 38) 18 38 hvalid hfast

theorem sr18p39:∀ i ∈ List.range 1,StrictCheckAt 18 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 39 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 39) 18 39:=by decide +kernel
  exact strictAtFast_sound (row 18 39) 18 39 hvalid hfast

theorem sr18p40:∀ i ∈ List.range 1,StrictCheckAt 18 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 40 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 40) 18 40:=by decide +kernel
  exact strictAtFast_sound (row 18 40) 18 40 hvalid hfast

theorem sr18p41:∀ i ∈ List.range 1,StrictCheckAt 18 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 41 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 41) 18 41:=by decide +kernel
  exact strictAtFast_sound (row 18 41) 18 41 hvalid hfast

theorem sr18p42:∀ i ∈ List.range 1,StrictCheckAt 18 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 42 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 42) 18 42:=by decide +kernel
  exact strictAtFast_sound (row 18 42) 18 42 hvalid hfast

theorem sr18p43:∀ i ∈ List.range 1,StrictCheckAt 18 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 43 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 43) 18 43:=by decide +kernel
  exact strictAtFast_sound (row 18 43) 18 43 hvalid hfast

theorem sr18p44:∀ i ∈ List.range 1,StrictCheckAt 18 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 44 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 44) 18 44:=by decide +kernel
  exact strictAtFast_sound (row 18 44) 18 44 hvalid hfast

theorem sr18p45:∀ i ∈ List.range 1,StrictCheckAt 18 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 45 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 45) 18 45:=by decide +kernel
  exact strictAtFast_sound (row 18 45) 18 45 hvalid hfast

theorem sr18p46:∀ i ∈ List.range 1,StrictCheckAt 18 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 46 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 46) 18 46:=by decide +kernel
  exact strictAtFast_sound (row 18 46) 18 46 hvalid hfast

theorem sr18p47:∀ i ∈ List.range 1,StrictCheckAt 18 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 47 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 47) 18 47:=by decide +kernel
  exact strictAtFast_sound (row 18 47) 18 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
