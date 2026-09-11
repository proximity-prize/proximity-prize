import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked21FastStrict05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr21p80:∀ i ∈ List.range 1,StrictCheckAt 21 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 80 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 80) 21 80:=by decide +kernel
  exact strictAtFast_sound (row 21 80) 21 80 hvalid hfast

theorem sr21p81:∀ i ∈ List.range 1,StrictCheckAt 21 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 81 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 81) 21 81:=by decide +kernel
  exact strictAtFast_sound (row 21 81) 21 81 hvalid hfast

theorem sr21p82:∀ i ∈ List.range 1,StrictCheckAt 21 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 82 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 82) 21 82:=by decide +kernel
  exact strictAtFast_sound (row 21 82) 21 82 hvalid hfast

theorem sr21p83:∀ i ∈ List.range 1,StrictCheckAt 21 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 83 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 83) 21 83:=by decide +kernel
  exact strictAtFast_sound (row 21 83) 21 83 hvalid hfast

theorem sr21p84:∀ i ∈ List.range 1,StrictCheckAt 21 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 84 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 84) 21 84:=by decide +kernel
  exact strictAtFast_sound (row 21 84) 21 84 hvalid hfast

theorem sr21p85:∀ i ∈ List.range 1,StrictCheckAt 21 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 85 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 85) 21 85:=by decide +kernel
  exact strictAtFast_sound (row 21 85) 21 85 hvalid hfast

theorem sr21p86:∀ i ∈ List.range 1,StrictCheckAt 21 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 86 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 86) 21 86:=by decide +kernel
  exact strictAtFast_sound (row 21 86) 21 86 hvalid hfast

theorem sr21p87:∀ i ∈ List.range 1,StrictCheckAt 21 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 87 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 87) 21 87:=by decide +kernel
  exact strictAtFast_sound (row 21 87) 21 87 hvalid hfast

theorem sr21p88:∀ i ∈ List.range 1,StrictCheckAt 21 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 88 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 88) 21 88:=by decide +kernel
  exact strictAtFast_sound (row 21 88) 21 88 hvalid hfast

theorem sr21p89:∀ i ∈ List.range 1,StrictCheckAt 21 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 89 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 89) 21 89:=by decide +kernel
  exact strictAtFast_sound (row 21 89) 21 89 hvalid hfast

theorem sr21p90:∀ i ∈ List.range 1,StrictCheckAt 21 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 90 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 90) 21 90:=by decide +kernel
  exact strictAtFast_sound (row 21 90) 21 90 hvalid hfast

theorem sr21p91:∀ i ∈ List.range 1,StrictCheckAt 21 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 91 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 91) 21 91:=by decide +kernel
  exact strictAtFast_sound (row 21 91) 21 91 hvalid hfast

theorem sr21p92:∀ i ∈ List.range 1,StrictCheckAt 21 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 92 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 92) 21 92:=by decide +kernel
  exact strictAtFast_sound (row 21 92) 21 92 hvalid hfast

theorem sr21p93:∀ i ∈ List.range 1,StrictCheckAt 21 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 93 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 93) 21 93:=by decide +kernel
  exact strictAtFast_sound (row 21 93) 21 93 hvalid hfast

theorem sr21p94:∀ i ∈ List.range 1,StrictCheckAt 21 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 94 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 94) 21 94:=by decide +kernel
  exact strictAtFast_sound (row 21 94) 21 94 hvalid hfast

theorem sr21p95:∀ i ∈ List.range 1,StrictCheckAt 21 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 95 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 95) 21 95:=by decide +kernel
  exact strictAtFast_sound (row 21 95) 21 95 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
