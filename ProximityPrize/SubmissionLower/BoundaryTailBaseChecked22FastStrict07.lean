import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked22FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr22p96:∀ i ∈ List.range 1,StrictCheckAt 22 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 96 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 96) 22 96:=by decide +kernel
  exact strictAtFast_sound (row 22 96) 22 96 hvalid hfast

theorem sr22p97:∀ i ∈ List.range 1,StrictCheckAt 22 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 97 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 97) 22 97:=by decide +kernel
  exact strictAtFast_sound (row 22 97) 22 97 hvalid hfast

theorem sr22p98:∀ i ∈ List.range 1,StrictCheckAt 22 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 98 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 98) 22 98:=by decide +kernel
  exact strictAtFast_sound (row 22 98) 22 98 hvalid hfast

theorem sr22p99:∀ i ∈ List.range 1,StrictCheckAt 22 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 99 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 99) 22 99:=by decide +kernel
  exact strictAtFast_sound (row 22 99) 22 99 hvalid hfast

theorem sr22p100:∀ i ∈ List.range 1,StrictCheckAt 22 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 100 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 100) 22 100:=by decide +kernel
  exact strictAtFast_sound (row 22 100) 22 100 hvalid hfast

theorem sr22p101:∀ i ∈ List.range 1,StrictCheckAt 22 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 101 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 101) 22 101:=by decide +kernel
  exact strictAtFast_sound (row 22 101) 22 101 hvalid hfast

theorem sr22p102:∀ i ∈ List.range 1,StrictCheckAt 22 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 102 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 102) 22 102:=by decide +kernel
  exact strictAtFast_sound (row 22 102) 22 102 hvalid hfast

theorem sr22p103:∀ i ∈ List.range 1,StrictCheckAt 22 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 103 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 103) 22 103:=by decide +kernel
  exact strictAtFast_sound (row 22 103) 22 103 hvalid hfast

theorem sr22p104:∀ i ∈ List.range 1,StrictCheckAt 22 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 104 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 104) 22 104:=by decide +kernel
  exact strictAtFast_sound (row 22 104) 22 104 hvalid hfast

theorem sr22p105:∀ i ∈ List.range 1,StrictCheckAt 22 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 105 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 105) 22 105:=by decide +kernel
  exact strictAtFast_sound (row 22 105) 22 105 hvalid hfast

theorem sr22p106:∀ i ∈ List.range 1,StrictCheckAt 22 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 106 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 106) 22 106:=by decide +kernel
  exact strictAtFast_sound (row 22 106) 22 106 hvalid hfast

theorem sr22p107:∀ i ∈ List.range 1,StrictCheckAt 22 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 107 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 107) 22 107:=by decide +kernel
  exact strictAtFast_sound (row 22 107) 22 107 hvalid hfast

theorem sr22p108:∀ i ∈ List.range 1,StrictCheckAt 22 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 108 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 108) 22 108:=by decide +kernel
  exact strictAtFast_sound (row 22 108) 22 108 hvalid hfast

theorem sr22p109:∀ i ∈ List.range 1,StrictCheckAt 22 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 109 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 109) 22 109:=by decide +kernel
  exact strictAtFast_sound (row 22 109) 22 109 hvalid hfast

theorem sr22p110:∀ i ∈ List.range 1,StrictCheckAt 22 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 110 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 110) 22 110:=by decide +kernel
  exact strictAtFast_sound (row 22 110) 22 110 hvalid hfast

theorem sr22p111:∀ i ∈ List.range 1,StrictCheckAt 22 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 111 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 111) 22 111:=by decide +kernel
  exact strictAtFast_sound (row 22 111) 22 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
