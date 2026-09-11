import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked28FastStrict05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr28p80:∀ i ∈ List.range 1,StrictCheckAt 28 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 80 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 80) 28 80:=by decide +kernel
  exact strictAtFast_sound (row 28 80) 28 80 hvalid hfast

theorem sr28p81:∀ i ∈ List.range 1,StrictCheckAt 28 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 81 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 81) 28 81:=by decide +kernel
  exact strictAtFast_sound (row 28 81) 28 81 hvalid hfast

theorem sr28p82:∀ i ∈ List.range 1,StrictCheckAt 28 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 82 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 82) 28 82:=by decide +kernel
  exact strictAtFast_sound (row 28 82) 28 82 hvalid hfast

theorem sr28p83:∀ i ∈ List.range 1,StrictCheckAt 28 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 83 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 83) 28 83:=by decide +kernel
  exact strictAtFast_sound (row 28 83) 28 83 hvalid hfast

theorem sr28p84:∀ i ∈ List.range 1,StrictCheckAt 28 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 84 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 84) 28 84:=by decide +kernel
  exact strictAtFast_sound (row 28 84) 28 84 hvalid hfast

theorem sr28p85:∀ i ∈ List.range 1,StrictCheckAt 28 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 85 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 85) 28 85:=by decide +kernel
  exact strictAtFast_sound (row 28 85) 28 85 hvalid hfast

theorem sr28p86:∀ i ∈ List.range 1,StrictCheckAt 28 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 86 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 86) 28 86:=by decide +kernel
  exact strictAtFast_sound (row 28 86) 28 86 hvalid hfast

theorem sr28p87:∀ i ∈ List.range 1,StrictCheckAt 28 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 87 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 87) 28 87:=by decide +kernel
  exact strictAtFast_sound (row 28 87) 28 87 hvalid hfast

theorem sr28p88:∀ i ∈ List.range 1,StrictCheckAt 28 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 88 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 88) 28 88:=by decide +kernel
  exact strictAtFast_sound (row 28 88) 28 88 hvalid hfast

theorem sr28p89:∀ i ∈ List.range 1,StrictCheckAt 28 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 89 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 89) 28 89:=by decide +kernel
  exact strictAtFast_sound (row 28 89) 28 89 hvalid hfast

theorem sr28p90:∀ i ∈ List.range 1,StrictCheckAt 28 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 90 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 90) 28 90:=by decide +kernel
  exact strictAtFast_sound (row 28 90) 28 90 hvalid hfast

theorem sr28p91:∀ i ∈ List.range 1,StrictCheckAt 28 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 91 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 91) 28 91:=by decide +kernel
  exact strictAtFast_sound (row 28 91) 28 91 hvalid hfast

theorem sr28p92:∀ i ∈ List.range 1,StrictCheckAt 28 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 92 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 92) 28 92:=by decide +kernel
  exact strictAtFast_sound (row 28 92) 28 92 hvalid hfast

theorem sr28p93:∀ i ∈ List.range 1,StrictCheckAt 28 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 93 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 93) 28 93:=by decide +kernel
  exact strictAtFast_sound (row 28 93) 28 93 hvalid hfast

theorem sr28p94:∀ i ∈ List.range 1,StrictCheckAt 28 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 94 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 94) 28 94:=by decide +kernel
  exact strictAtFast_sound (row 28 94) 28 94 hvalid hfast

theorem sr28p95:∀ i ∈ List.range 1,StrictCheckAt 28 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 95 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 95) 28 95:=by decide +kernel
  exact strictAtFast_sound (row 28 95) 28 95 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
