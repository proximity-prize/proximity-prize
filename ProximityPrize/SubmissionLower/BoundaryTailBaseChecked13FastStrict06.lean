import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked13FastStrict05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr13p80:∀ i ∈ List.range 1,StrictCheckAt 13 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 80 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 80) 13 80:=by decide +kernel
  exact strictAtFast_sound (row 13 80) 13 80 hvalid hfast

theorem sr13p81:∀ i ∈ List.range 1,StrictCheckAt 13 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 81 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 81) 13 81:=by decide +kernel
  exact strictAtFast_sound (row 13 81) 13 81 hvalid hfast

theorem sr13p82:∀ i ∈ List.range 1,StrictCheckAt 13 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 82 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 82) 13 82:=by decide +kernel
  exact strictAtFast_sound (row 13 82) 13 82 hvalid hfast

theorem sr13p83:∀ i ∈ List.range 1,StrictCheckAt 13 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 83 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 83) 13 83:=by decide +kernel
  exact strictAtFast_sound (row 13 83) 13 83 hvalid hfast

theorem sr13p84:∀ i ∈ List.range 1,StrictCheckAt 13 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 84 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 84) 13 84:=by decide +kernel
  exact strictAtFast_sound (row 13 84) 13 84 hvalid hfast

theorem sr13p85:∀ i ∈ List.range 1,StrictCheckAt 13 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 85 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 85) 13 85:=by decide +kernel
  exact strictAtFast_sound (row 13 85) 13 85 hvalid hfast

theorem sr13p86:∀ i ∈ List.range 1,StrictCheckAt 13 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 86 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 86) 13 86:=by decide +kernel
  exact strictAtFast_sound (row 13 86) 13 86 hvalid hfast

theorem sr13p87:∀ i ∈ List.range 1,StrictCheckAt 13 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 87 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 87) 13 87:=by decide +kernel
  exact strictAtFast_sound (row 13 87) 13 87 hvalid hfast

theorem sr13p88:∀ i ∈ List.range 1,StrictCheckAt 13 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 88 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 88) 13 88:=by decide +kernel
  exact strictAtFast_sound (row 13 88) 13 88 hvalid hfast

theorem sr13p89:∀ i ∈ List.range 1,StrictCheckAt 13 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 89 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 89) 13 89:=by decide +kernel
  exact strictAtFast_sound (row 13 89) 13 89 hvalid hfast

theorem sr13p90:∀ i ∈ List.range 1,StrictCheckAt 13 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 90 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 90) 13 90:=by decide +kernel
  exact strictAtFast_sound (row 13 90) 13 90 hvalid hfast

theorem sr13p91:∀ i ∈ List.range 1,StrictCheckAt 13 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 91 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 91) 13 91:=by decide +kernel
  exact strictAtFast_sound (row 13 91) 13 91 hvalid hfast

theorem sr13p92:∀ i ∈ List.range 1,StrictCheckAt 13 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 92 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 92) 13 92:=by decide +kernel
  exact strictAtFast_sound (row 13 92) 13 92 hvalid hfast

theorem sr13p93:∀ i ∈ List.range 1,StrictCheckAt 13 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 93 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 93) 13 93:=by decide +kernel
  exact strictAtFast_sound (row 13 93) 13 93 hvalid hfast

theorem sr13p94:∀ i ∈ List.range 1,StrictCheckAt 13 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 94 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 94) 13 94:=by decide +kernel
  exact strictAtFast_sound (row 13 94) 13 94 hvalid hfast

theorem sr13p95:∀ i ∈ List.range 1,StrictCheckAt 13 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 95 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 13 95) 13 95:=by decide +kernel
  exact strictAtFast_sound (row 13 95) 13 95 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
