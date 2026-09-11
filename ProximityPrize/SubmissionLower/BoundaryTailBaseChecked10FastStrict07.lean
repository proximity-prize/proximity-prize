import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr10p96:∀ i ∈ List.range 1,StrictCheckAt 10 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 96 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 96) 10 96:=by decide +kernel
  exact strictAtFast_sound (row 10 96) 10 96 hvalid hfast

theorem sr10p97:∀ i ∈ List.range 1,StrictCheckAt 10 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 97 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 97) 10 97:=by decide +kernel
  exact strictAtFast_sound (row 10 97) 10 97 hvalid hfast

theorem sr10p98:∀ i ∈ List.range 1,StrictCheckAt 10 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 98 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 98) 10 98:=by decide +kernel
  exact strictAtFast_sound (row 10 98) 10 98 hvalid hfast

theorem sr10p99:∀ i ∈ List.range 1,StrictCheckAt 10 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 99 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 99) 10 99:=by decide +kernel
  exact strictAtFast_sound (row 10 99) 10 99 hvalid hfast

theorem sr10p100:∀ i ∈ List.range 1,StrictCheckAt 10 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 100 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 100) 10 100:=by decide +kernel
  exact strictAtFast_sound (row 10 100) 10 100 hvalid hfast

theorem sr10p101:∀ i ∈ List.range 1,StrictCheckAt 10 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 101 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 101) 10 101:=by decide +kernel
  exact strictAtFast_sound (row 10 101) 10 101 hvalid hfast

theorem sr10p102:∀ i ∈ List.range 1,StrictCheckAt 10 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 102 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 102) 10 102:=by decide +kernel
  exact strictAtFast_sound (row 10 102) 10 102 hvalid hfast

theorem sr10p103:∀ i ∈ List.range 1,StrictCheckAt 10 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 103 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 103) 10 103:=by decide +kernel
  exact strictAtFast_sound (row 10 103) 10 103 hvalid hfast

theorem sr10p104:∀ i ∈ List.range 1,StrictCheckAt 10 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 104 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 104) 10 104:=by decide +kernel
  exact strictAtFast_sound (row 10 104) 10 104 hvalid hfast

theorem sr10p105:∀ i ∈ List.range 1,StrictCheckAt 10 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 105 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 105) 10 105:=by decide +kernel
  exact strictAtFast_sound (row 10 105) 10 105 hvalid hfast

theorem sr10p106:∀ i ∈ List.range 1,StrictCheckAt 10 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 106 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 106) 10 106:=by decide +kernel
  exact strictAtFast_sound (row 10 106) 10 106 hvalid hfast

theorem sr10p107:∀ i ∈ List.range 1,StrictCheckAt 10 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 107 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 107) 10 107:=by decide +kernel
  exact strictAtFast_sound (row 10 107) 10 107 hvalid hfast

theorem sr10p108:∀ i ∈ List.range 1,StrictCheckAt 10 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 108 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 108) 10 108:=by decide +kernel
  exact strictAtFast_sound (row 10 108) 10 108 hvalid hfast

theorem sr10p109:∀ i ∈ List.range 1,StrictCheckAt 10 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 109 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 109) 10 109:=by decide +kernel
  exact strictAtFast_sound (row 10 109) 10 109 hvalid hfast

theorem sr10p110:∀ i ∈ List.range 1,StrictCheckAt 10 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 110 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 110) 10 110:=by decide +kernel
  exact strictAtFast_sound (row 10 110) 10 110 hvalid hfast

theorem sr10p111:∀ i ∈ List.range 1,StrictCheckAt 10 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 111 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 111) 10 111:=by decide +kernel
  exact strictAtFast_sound (row 10 111) 10 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
