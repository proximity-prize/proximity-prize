import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked09FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr9p96:∀ i ∈ List.range 1,StrictCheckAt 9 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 96 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 96) 9 96:=by decide +kernel
  exact strictAtFast_sound (row 9 96) 9 96 hvalid hfast

theorem sr9p97:∀ i ∈ List.range 1,StrictCheckAt 9 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 97 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 97) 9 97:=by decide +kernel
  exact strictAtFast_sound (row 9 97) 9 97 hvalid hfast

theorem sr9p98:∀ i ∈ List.range 1,StrictCheckAt 9 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 98 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 98) 9 98:=by decide +kernel
  exact strictAtFast_sound (row 9 98) 9 98 hvalid hfast

theorem sr9p99:∀ i ∈ List.range 1,StrictCheckAt 9 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 99 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 99) 9 99:=by decide +kernel
  exact strictAtFast_sound (row 9 99) 9 99 hvalid hfast

theorem sr9p100:∀ i ∈ List.range 1,StrictCheckAt 9 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 100 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 100) 9 100:=by decide +kernel
  exact strictAtFast_sound (row 9 100) 9 100 hvalid hfast

theorem sr9p101:∀ i ∈ List.range 1,StrictCheckAt 9 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 101 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 101) 9 101:=by decide +kernel
  exact strictAtFast_sound (row 9 101) 9 101 hvalid hfast

theorem sr9p102:∀ i ∈ List.range 1,StrictCheckAt 9 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 102 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 102) 9 102:=by decide +kernel
  exact strictAtFast_sound (row 9 102) 9 102 hvalid hfast

theorem sr9p103:∀ i ∈ List.range 1,StrictCheckAt 9 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 103 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 103) 9 103:=by decide +kernel
  exact strictAtFast_sound (row 9 103) 9 103 hvalid hfast

theorem sr9p104:∀ i ∈ List.range 1,StrictCheckAt 9 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 104 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 104) 9 104:=by decide +kernel
  exact strictAtFast_sound (row 9 104) 9 104 hvalid hfast

theorem sr9p105:∀ i ∈ List.range 1,StrictCheckAt 9 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 105 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 105) 9 105:=by decide +kernel
  exact strictAtFast_sound (row 9 105) 9 105 hvalid hfast

theorem sr9p106:∀ i ∈ List.range 1,StrictCheckAt 9 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 106 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 106) 9 106:=by decide +kernel
  exact strictAtFast_sound (row 9 106) 9 106 hvalid hfast

theorem sr9p107:∀ i ∈ List.range 1,StrictCheckAt 9 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 107 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 107) 9 107:=by decide +kernel
  exact strictAtFast_sound (row 9 107) 9 107 hvalid hfast

theorem sr9p108:∀ i ∈ List.range 1,StrictCheckAt 9 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 108 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 108) 9 108:=by decide +kernel
  exact strictAtFast_sound (row 9 108) 9 108 hvalid hfast

theorem sr9p109:∀ i ∈ List.range 1,StrictCheckAt 9 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 109 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 109) 9 109:=by decide +kernel
  exact strictAtFast_sound (row 9 109) 9 109 hvalid hfast

theorem sr9p110:∀ i ∈ List.range 1,StrictCheckAt 9 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 110 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 110) 9 110:=by decide +kernel
  exact strictAtFast_sound (row 9 110) 9 110 hvalid hfast

theorem sr9p111:∀ i ∈ List.range 1,StrictCheckAt 9 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 111 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 111) 9 111:=by decide +kernel
  exact strictAtFast_sound (row 9 111) 9 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
