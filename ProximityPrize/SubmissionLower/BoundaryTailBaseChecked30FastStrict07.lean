import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked30FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr30p96:∀ i ∈ List.range 1,StrictCheckAt 30 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 96 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 96) 30 96:=by decide +kernel
  exact strictAtFast_sound (row 30 96) 30 96 hvalid hfast

theorem sr30p97:∀ i ∈ List.range 1,StrictCheckAt 30 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 97 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 97) 30 97:=by decide +kernel
  exact strictAtFast_sound (row 30 97) 30 97 hvalid hfast

theorem sr30p98:∀ i ∈ List.range 1,StrictCheckAt 30 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 98 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 98) 30 98:=by decide +kernel
  exact strictAtFast_sound (row 30 98) 30 98 hvalid hfast

theorem sr30p99:∀ i ∈ List.range 1,StrictCheckAt 30 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 99 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 99) 30 99:=by decide +kernel
  exact strictAtFast_sound (row 30 99) 30 99 hvalid hfast

theorem sr30p100:∀ i ∈ List.range 1,StrictCheckAt 30 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 100 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 100) 30 100:=by decide +kernel
  exact strictAtFast_sound (row 30 100) 30 100 hvalid hfast

theorem sr30p101:∀ i ∈ List.range 1,StrictCheckAt 30 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 101 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 101) 30 101:=by decide +kernel
  exact strictAtFast_sound (row 30 101) 30 101 hvalid hfast

theorem sr30p102:∀ i ∈ List.range 1,StrictCheckAt 30 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 102 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 102) 30 102:=by decide +kernel
  exact strictAtFast_sound (row 30 102) 30 102 hvalid hfast

theorem sr30p103:∀ i ∈ List.range 1,StrictCheckAt 30 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 103 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 103) 30 103:=by decide +kernel
  exact strictAtFast_sound (row 30 103) 30 103 hvalid hfast

theorem sr30p104:∀ i ∈ List.range 1,StrictCheckAt 30 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 104 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 104) 30 104:=by decide +kernel
  exact strictAtFast_sound (row 30 104) 30 104 hvalid hfast

theorem sr30p105:∀ i ∈ List.range 1,StrictCheckAt 30 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 105 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 105) 30 105:=by decide +kernel
  exact strictAtFast_sound (row 30 105) 30 105 hvalid hfast

theorem sr30p106:∀ i ∈ List.range 1,StrictCheckAt 30 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 106 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 106) 30 106:=by decide +kernel
  exact strictAtFast_sound (row 30 106) 30 106 hvalid hfast

theorem sr30p107:∀ i ∈ List.range 1,StrictCheckAt 30 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 107 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 107) 30 107:=by decide +kernel
  exact strictAtFast_sound (row 30 107) 30 107 hvalid hfast

theorem sr30p108:∀ i ∈ List.range 1,StrictCheckAt 30 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 108 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 108) 30 108:=by decide +kernel
  exact strictAtFast_sound (row 30 108) 30 108 hvalid hfast

theorem sr30p109:∀ i ∈ List.range 1,StrictCheckAt 30 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 109 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 109) 30 109:=by decide +kernel
  exact strictAtFast_sound (row 30 109) 30 109 hvalid hfast

theorem sr30p110:∀ i ∈ List.range 1,StrictCheckAt 30 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 110 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 110) 30 110:=by decide +kernel
  exact strictAtFast_sound (row 30 110) 30 110 hvalid hfast

theorem sr30p111:∀ i ∈ List.range 1,StrictCheckAt 30 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 111 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 111) 30 111:=by decide +kernel
  exact strictAtFast_sound (row 30 111) 30 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
