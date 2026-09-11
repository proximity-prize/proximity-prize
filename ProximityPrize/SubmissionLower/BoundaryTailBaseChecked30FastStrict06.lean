import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked30FastStrict05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr30p80:∀ i ∈ List.range 1,StrictCheckAt 30 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 80 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 80) 30 80:=by decide +kernel
  exact strictAtFast_sound (row 30 80) 30 80 hvalid hfast

theorem sr30p81:∀ i ∈ List.range 1,StrictCheckAt 30 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 81 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 81) 30 81:=by decide +kernel
  exact strictAtFast_sound (row 30 81) 30 81 hvalid hfast

theorem sr30p82:∀ i ∈ List.range 1,StrictCheckAt 30 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 82 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 82) 30 82:=by decide +kernel
  exact strictAtFast_sound (row 30 82) 30 82 hvalid hfast

theorem sr30p83:∀ i ∈ List.range 1,StrictCheckAt 30 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 83 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 83) 30 83:=by decide +kernel
  exact strictAtFast_sound (row 30 83) 30 83 hvalid hfast

theorem sr30p84:∀ i ∈ List.range 1,StrictCheckAt 30 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 84 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 84) 30 84:=by decide +kernel
  exact strictAtFast_sound (row 30 84) 30 84 hvalid hfast

theorem sr30p85:∀ i ∈ List.range 1,StrictCheckAt 30 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 85 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 85) 30 85:=by decide +kernel
  exact strictAtFast_sound (row 30 85) 30 85 hvalid hfast

theorem sr30p86:∀ i ∈ List.range 1,StrictCheckAt 30 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 86 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 86) 30 86:=by decide +kernel
  exact strictAtFast_sound (row 30 86) 30 86 hvalid hfast

theorem sr30p87:∀ i ∈ List.range 1,StrictCheckAt 30 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 87 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 87) 30 87:=by decide +kernel
  exact strictAtFast_sound (row 30 87) 30 87 hvalid hfast

theorem sr30p88:∀ i ∈ List.range 1,StrictCheckAt 30 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 88 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 88) 30 88:=by decide +kernel
  exact strictAtFast_sound (row 30 88) 30 88 hvalid hfast

theorem sr30p89:∀ i ∈ List.range 1,StrictCheckAt 30 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 89 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 89) 30 89:=by decide +kernel
  exact strictAtFast_sound (row 30 89) 30 89 hvalid hfast

theorem sr30p90:∀ i ∈ List.range 1,StrictCheckAt 30 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 90 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 90) 30 90:=by decide +kernel
  exact strictAtFast_sound (row 30 90) 30 90 hvalid hfast

theorem sr30p91:∀ i ∈ List.range 1,StrictCheckAt 30 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 91 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 91) 30 91:=by decide +kernel
  exact strictAtFast_sound (row 30 91) 30 91 hvalid hfast

theorem sr30p92:∀ i ∈ List.range 1,StrictCheckAt 30 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 92 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 92) 30 92:=by decide +kernel
  exact strictAtFast_sound (row 30 92) 30 92 hvalid hfast

theorem sr30p93:∀ i ∈ List.range 1,StrictCheckAt 30 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 93 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 93) 30 93:=by decide +kernel
  exact strictAtFast_sound (row 30 93) 30 93 hvalid hfast

theorem sr30p94:∀ i ∈ List.range 1,StrictCheckAt 30 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 94 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 94) 30 94:=by decide +kernel
  exact strictAtFast_sound (row 30 94) 30 94 hvalid hfast

theorem sr30p95:∀ i ∈ List.range 1,StrictCheckAt 30 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 95 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 95) 30 95:=by decide +kernel
  exact strictAtFast_sound (row 30 95) 30 95 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
