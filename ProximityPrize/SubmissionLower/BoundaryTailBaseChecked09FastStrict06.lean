import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked09FastStrict05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr9p80:∀ i ∈ List.range 1,StrictCheckAt 9 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 80 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 80) 9 80:=by decide +kernel
  exact strictAtFast_sound (row 9 80) 9 80 hvalid hfast

theorem sr9p81:∀ i ∈ List.range 1,StrictCheckAt 9 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 81 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 81) 9 81:=by decide +kernel
  exact strictAtFast_sound (row 9 81) 9 81 hvalid hfast

theorem sr9p82:∀ i ∈ List.range 1,StrictCheckAt 9 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 82 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 82) 9 82:=by decide +kernel
  exact strictAtFast_sound (row 9 82) 9 82 hvalid hfast

theorem sr9p83:∀ i ∈ List.range 1,StrictCheckAt 9 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 83 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 83) 9 83:=by decide +kernel
  exact strictAtFast_sound (row 9 83) 9 83 hvalid hfast

theorem sr9p84:∀ i ∈ List.range 1,StrictCheckAt 9 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 84 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 84) 9 84:=by decide +kernel
  exact strictAtFast_sound (row 9 84) 9 84 hvalid hfast

theorem sr9p85:∀ i ∈ List.range 1,StrictCheckAt 9 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 85 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 85) 9 85:=by decide +kernel
  exact strictAtFast_sound (row 9 85) 9 85 hvalid hfast

theorem sr9p86:∀ i ∈ List.range 1,StrictCheckAt 9 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 86 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 86) 9 86:=by decide +kernel
  exact strictAtFast_sound (row 9 86) 9 86 hvalid hfast

theorem sr9p87:∀ i ∈ List.range 1,StrictCheckAt 9 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 87 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 87) 9 87:=by decide +kernel
  exact strictAtFast_sound (row 9 87) 9 87 hvalid hfast

theorem sr9p88:∀ i ∈ List.range 1,StrictCheckAt 9 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 88 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 88) 9 88:=by decide +kernel
  exact strictAtFast_sound (row 9 88) 9 88 hvalid hfast

theorem sr9p89:∀ i ∈ List.range 1,StrictCheckAt 9 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 89 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 89) 9 89:=by decide +kernel
  exact strictAtFast_sound (row 9 89) 9 89 hvalid hfast

theorem sr9p90:∀ i ∈ List.range 1,StrictCheckAt 9 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 90 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 90) 9 90:=by decide +kernel
  exact strictAtFast_sound (row 9 90) 9 90 hvalid hfast

theorem sr9p91:∀ i ∈ List.range 1,StrictCheckAt 9 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 91 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 91) 9 91:=by decide +kernel
  exact strictAtFast_sound (row 9 91) 9 91 hvalid hfast

theorem sr9p92:∀ i ∈ List.range 1,StrictCheckAt 9 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 92 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 92) 9 92:=by decide +kernel
  exact strictAtFast_sound (row 9 92) 9 92 hvalid hfast

theorem sr9p93:∀ i ∈ List.range 1,StrictCheckAt 9 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 93 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 93) 9 93:=by decide +kernel
  exact strictAtFast_sound (row 9 93) 9 93 hvalid hfast

theorem sr9p94:∀ i ∈ List.range 1,StrictCheckAt 9 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 94 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 94) 9 94:=by decide +kernel
  exact strictAtFast_sound (row 9 94) 9 94 hvalid hfast

theorem sr9p95:∀ i ∈ List.range 1,StrictCheckAt 9 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 95 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 95) 9 95:=by decide +kernel
  exact strictAtFast_sound (row 9 95) 9 95 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
