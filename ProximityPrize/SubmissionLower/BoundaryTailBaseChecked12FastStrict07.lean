import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked12FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr12p96:∀ i ∈ List.range 1,StrictCheckAt 12 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 96 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 12 96) 12 96:=by decide +kernel
  exact strictAtFast_sound (row 12 96) 12 96 hvalid hfast

theorem sr12p97:∀ i ∈ List.range 1,StrictCheckAt 12 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 97 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 12 97) 12 97:=by decide +kernel
  exact strictAtFast_sound (row 12 97) 12 97 hvalid hfast

theorem sr12p98:∀ i ∈ List.range 1,StrictCheckAt 12 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 98 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 12 98) 12 98:=by decide +kernel
  exact strictAtFast_sound (row 12 98) 12 98 hvalid hfast

theorem sr12p99:∀ i ∈ List.range 1,StrictCheckAt 12 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 99 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 12 99) 12 99:=by decide +kernel
  exact strictAtFast_sound (row 12 99) 12 99 hvalid hfast

theorem sr12p100:∀ i ∈ List.range 1,StrictCheckAt 12 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 100 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 12 100) 12 100:=by decide +kernel
  exact strictAtFast_sound (row 12 100) 12 100 hvalid hfast

theorem sr12p101:∀ i ∈ List.range 1,StrictCheckAt 12 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 101 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 12 101) 12 101:=by decide +kernel
  exact strictAtFast_sound (row 12 101) 12 101 hvalid hfast

theorem sr12p102:∀ i ∈ List.range 1,StrictCheckAt 12 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 102 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 12 102) 12 102:=by decide +kernel
  exact strictAtFast_sound (row 12 102) 12 102 hvalid hfast

theorem sr12p103:∀ i ∈ List.range 1,StrictCheckAt 12 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 103 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 12 103) 12 103:=by decide +kernel
  exact strictAtFast_sound (row 12 103) 12 103 hvalid hfast

theorem sr12p104:∀ i ∈ List.range 1,StrictCheckAt 12 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 104 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 12 104) 12 104:=by decide +kernel
  exact strictAtFast_sound (row 12 104) 12 104 hvalid hfast

theorem sr12p105:∀ i ∈ List.range 1,StrictCheckAt 12 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 105 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 12 105) 12 105:=by decide +kernel
  exact strictAtFast_sound (row 12 105) 12 105 hvalid hfast

theorem sr12p106:∀ i ∈ List.range 1,StrictCheckAt 12 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 106 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 12 106) 12 106:=by decide +kernel
  exact strictAtFast_sound (row 12 106) 12 106 hvalid hfast

theorem sr12p107:∀ i ∈ List.range 1,StrictCheckAt 12 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 107 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 12 107) 12 107:=by decide +kernel
  exact strictAtFast_sound (row 12 107) 12 107 hvalid hfast

theorem sr12p108:∀ i ∈ List.range 1,StrictCheckAt 12 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 108 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 12 108) 12 108:=by decide +kernel
  exact strictAtFast_sound (row 12 108) 12 108 hvalid hfast

theorem sr12p109:∀ i ∈ List.range 1,StrictCheckAt 12 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 109 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 12 109) 12 109:=by decide +kernel
  exact strictAtFast_sound (row 12 109) 12 109 hvalid hfast

theorem sr12p110:∀ i ∈ List.range 1,StrictCheckAt 12 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 110 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 12 110) 12 110:=by decide +kernel
  exact strictAtFast_sound (row 12 110) 12 110 hvalid hfast

theorem sr12p111:∀ i ∈ List.range 1,StrictCheckAt 12 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 111 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 12 111) 12 111:=by decide +kernel
  exact strictAtFast_sound (row 12 111) 12 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
