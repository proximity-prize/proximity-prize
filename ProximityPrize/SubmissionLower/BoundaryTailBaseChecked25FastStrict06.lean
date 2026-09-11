import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked25FastStrict05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr25p80:∀ i ∈ List.range 1,StrictCheckAt 25 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 80 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 80) 25 80:=by decide +kernel
  exact strictAtFast_sound (row 25 80) 25 80 hvalid hfast

theorem sr25p81:∀ i ∈ List.range 1,StrictCheckAt 25 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 81 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 81) 25 81:=by decide +kernel
  exact strictAtFast_sound (row 25 81) 25 81 hvalid hfast

theorem sr25p82:∀ i ∈ List.range 1,StrictCheckAt 25 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 82 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 82) 25 82:=by decide +kernel
  exact strictAtFast_sound (row 25 82) 25 82 hvalid hfast

theorem sr25p83:∀ i ∈ List.range 1,StrictCheckAt 25 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 83 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 83) 25 83:=by decide +kernel
  exact strictAtFast_sound (row 25 83) 25 83 hvalid hfast

theorem sr25p84:∀ i ∈ List.range 1,StrictCheckAt 25 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 84 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 84) 25 84:=by decide +kernel
  exact strictAtFast_sound (row 25 84) 25 84 hvalid hfast

theorem sr25p85:∀ i ∈ List.range 1,StrictCheckAt 25 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 85 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 85) 25 85:=by decide +kernel
  exact strictAtFast_sound (row 25 85) 25 85 hvalid hfast

theorem sr25p86:∀ i ∈ List.range 1,StrictCheckAt 25 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 86 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 86) 25 86:=by decide +kernel
  exact strictAtFast_sound (row 25 86) 25 86 hvalid hfast

theorem sr25p87:∀ i ∈ List.range 1,StrictCheckAt 25 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 87 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 87) 25 87:=by decide +kernel
  exact strictAtFast_sound (row 25 87) 25 87 hvalid hfast

theorem sr25p88:∀ i ∈ List.range 1,StrictCheckAt 25 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 88 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 88) 25 88:=by decide +kernel
  exact strictAtFast_sound (row 25 88) 25 88 hvalid hfast

theorem sr25p89:∀ i ∈ List.range 1,StrictCheckAt 25 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 89 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 89) 25 89:=by decide +kernel
  exact strictAtFast_sound (row 25 89) 25 89 hvalid hfast

theorem sr25p90:∀ i ∈ List.range 1,StrictCheckAt 25 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 90 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 90) 25 90:=by decide +kernel
  exact strictAtFast_sound (row 25 90) 25 90 hvalid hfast

theorem sr25p91:∀ i ∈ List.range 1,StrictCheckAt 25 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 91 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 91) 25 91:=by decide +kernel
  exact strictAtFast_sound (row 25 91) 25 91 hvalid hfast

theorem sr25p92:∀ i ∈ List.range 1,StrictCheckAt 25 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 92 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 92) 25 92:=by decide +kernel
  exact strictAtFast_sound (row 25 92) 25 92 hvalid hfast

theorem sr25p93:∀ i ∈ List.range 1,StrictCheckAt 25 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 93 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 93) 25 93:=by decide +kernel
  exact strictAtFast_sound (row 25 93) 25 93 hvalid hfast

theorem sr25p94:∀ i ∈ List.range 1,StrictCheckAt 25 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 94 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 94) 25 94:=by decide +kernel
  exact strictAtFast_sound (row 25 94) 25 94 hvalid hfast

theorem sr25p95:∀ i ∈ List.range 1,StrictCheckAt 25 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 95 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 95) 25 95:=by decide +kernel
  exact strictAtFast_sound (row 25 95) 25 95 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
