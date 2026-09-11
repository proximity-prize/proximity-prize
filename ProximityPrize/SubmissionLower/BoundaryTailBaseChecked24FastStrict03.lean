import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked24FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr24p32:∀ i ∈ List.range 1,StrictCheckAt 24 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 32 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 32) 24 32:=by decide +kernel
  exact strictAtFast_sound (row 24 32) 24 32 hvalid hfast

theorem sr24p33:∀ i ∈ List.range 1,StrictCheckAt 24 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 33 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 33) 24 33:=by decide +kernel
  exact strictAtFast_sound (row 24 33) 24 33 hvalid hfast

theorem sr24p34:∀ i ∈ List.range 1,StrictCheckAt 24 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 34 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 34) 24 34:=by decide +kernel
  exact strictAtFast_sound (row 24 34) 24 34 hvalid hfast

theorem sr24p35:∀ i ∈ List.range 1,StrictCheckAt 24 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 35 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 35) 24 35:=by decide +kernel
  exact strictAtFast_sound (row 24 35) 24 35 hvalid hfast

theorem sr24p36:∀ i ∈ List.range 1,StrictCheckAt 24 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 36 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 36) 24 36:=by decide +kernel
  exact strictAtFast_sound (row 24 36) 24 36 hvalid hfast

theorem sr24p37:∀ i ∈ List.range 1,StrictCheckAt 24 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 37 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 37) 24 37:=by decide +kernel
  exact strictAtFast_sound (row 24 37) 24 37 hvalid hfast

theorem sr24p38:∀ i ∈ List.range 1,StrictCheckAt 24 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 38 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 38) 24 38:=by decide +kernel
  exact strictAtFast_sound (row 24 38) 24 38 hvalid hfast

theorem sr24p39:∀ i ∈ List.range 1,StrictCheckAt 24 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 39 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 39) 24 39:=by decide +kernel
  exact strictAtFast_sound (row 24 39) 24 39 hvalid hfast

theorem sr24p40:∀ i ∈ List.range 1,StrictCheckAt 24 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 40 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 40) 24 40:=by decide +kernel
  exact strictAtFast_sound (row 24 40) 24 40 hvalid hfast

theorem sr24p41:∀ i ∈ List.range 1,StrictCheckAt 24 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 41 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 41) 24 41:=by decide +kernel
  exact strictAtFast_sound (row 24 41) 24 41 hvalid hfast

theorem sr24p42:∀ i ∈ List.range 1,StrictCheckAt 24 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 42 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 42) 24 42:=by decide +kernel
  exact strictAtFast_sound (row 24 42) 24 42 hvalid hfast

theorem sr24p43:∀ i ∈ List.range 1,StrictCheckAt 24 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 43 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 43) 24 43:=by decide +kernel
  exact strictAtFast_sound (row 24 43) 24 43 hvalid hfast

theorem sr24p44:∀ i ∈ List.range 1,StrictCheckAt 24 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 44 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 44) 24 44:=by decide +kernel
  exact strictAtFast_sound (row 24 44) 24 44 hvalid hfast

theorem sr24p45:∀ i ∈ List.range 1,StrictCheckAt 24 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 45 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 45) 24 45:=by decide +kernel
  exact strictAtFast_sound (row 24 45) 24 45 hvalid hfast

theorem sr24p46:∀ i ∈ List.range 1,StrictCheckAt 24 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 46 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 46) 24 46:=by decide +kernel
  exact strictAtFast_sound (row 24 46) 24 46 hvalid hfast

theorem sr24p47:∀ i ∈ List.range 1,StrictCheckAt 24 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 47 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 47) 24 47:=by decide +kernel
  exact strictAtFast_sound (row 24 47) 24 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
