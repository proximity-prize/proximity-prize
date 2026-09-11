import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked17FastStrict05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr17p80:∀ i ∈ List.range 1,StrictCheckAt 17 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 80 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 80) 17 80:=by decide +kernel
  exact strictAtFast_sound (row 17 80) 17 80 hvalid hfast

theorem sr17p81:∀ i ∈ List.range 1,StrictCheckAt 17 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 81 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 81) 17 81:=by decide +kernel
  exact strictAtFast_sound (row 17 81) 17 81 hvalid hfast

theorem sr17p82:∀ i ∈ List.range 1,StrictCheckAt 17 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 82 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 82) 17 82:=by decide +kernel
  exact strictAtFast_sound (row 17 82) 17 82 hvalid hfast

theorem sr17p83:∀ i ∈ List.range 1,StrictCheckAt 17 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 83 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 83) 17 83:=by decide +kernel
  exact strictAtFast_sound (row 17 83) 17 83 hvalid hfast

theorem sr17p84:∀ i ∈ List.range 1,StrictCheckAt 17 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 84 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 84) 17 84:=by decide +kernel
  exact strictAtFast_sound (row 17 84) 17 84 hvalid hfast

theorem sr17p85:∀ i ∈ List.range 1,StrictCheckAt 17 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 85 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 85) 17 85:=by decide +kernel
  exact strictAtFast_sound (row 17 85) 17 85 hvalid hfast

theorem sr17p86:∀ i ∈ List.range 1,StrictCheckAt 17 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 86 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 86) 17 86:=by decide +kernel
  exact strictAtFast_sound (row 17 86) 17 86 hvalid hfast

theorem sr17p87:∀ i ∈ List.range 1,StrictCheckAt 17 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 87 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 87) 17 87:=by decide +kernel
  exact strictAtFast_sound (row 17 87) 17 87 hvalid hfast

theorem sr17p88:∀ i ∈ List.range 1,StrictCheckAt 17 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 88 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 88) 17 88:=by decide +kernel
  exact strictAtFast_sound (row 17 88) 17 88 hvalid hfast

theorem sr17p89:∀ i ∈ List.range 1,StrictCheckAt 17 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 89 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 89) 17 89:=by decide +kernel
  exact strictAtFast_sound (row 17 89) 17 89 hvalid hfast

theorem sr17p90:∀ i ∈ List.range 1,StrictCheckAt 17 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 90 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 90) 17 90:=by decide +kernel
  exact strictAtFast_sound (row 17 90) 17 90 hvalid hfast

theorem sr17p91:∀ i ∈ List.range 1,StrictCheckAt 17 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 91 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 91) 17 91:=by decide +kernel
  exact strictAtFast_sound (row 17 91) 17 91 hvalid hfast

theorem sr17p92:∀ i ∈ List.range 1,StrictCheckAt 17 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 92 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 92) 17 92:=by decide +kernel
  exact strictAtFast_sound (row 17 92) 17 92 hvalid hfast

theorem sr17p93:∀ i ∈ List.range 1,StrictCheckAt 17 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 93 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 93) 17 93:=by decide +kernel
  exact strictAtFast_sound (row 17 93) 17 93 hvalid hfast

theorem sr17p94:∀ i ∈ List.range 1,StrictCheckAt 17 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 94 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 94) 17 94:=by decide +kernel
  exact strictAtFast_sound (row 17 94) 17 94 hvalid hfast

theorem sr17p95:∀ i ∈ List.range 1,StrictCheckAt 17 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 95 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 95) 17 95:=by decide +kernel
  exact strictAtFast_sound (row 17 95) 17 95 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
