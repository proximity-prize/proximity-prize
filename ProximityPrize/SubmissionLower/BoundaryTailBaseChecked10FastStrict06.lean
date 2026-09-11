import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10FastStrict05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr10p80:∀ i ∈ List.range 1,StrictCheckAt 10 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 80 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 80) 10 80:=by decide +kernel
  exact strictAtFast_sound (row 10 80) 10 80 hvalid hfast

theorem sr10p81:∀ i ∈ List.range 1,StrictCheckAt 10 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 81 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 81) 10 81:=by decide +kernel
  exact strictAtFast_sound (row 10 81) 10 81 hvalid hfast

theorem sr10p82:∀ i ∈ List.range 1,StrictCheckAt 10 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 82 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 82) 10 82:=by decide +kernel
  exact strictAtFast_sound (row 10 82) 10 82 hvalid hfast

theorem sr10p83:∀ i ∈ List.range 1,StrictCheckAt 10 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 83 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 83) 10 83:=by decide +kernel
  exact strictAtFast_sound (row 10 83) 10 83 hvalid hfast

theorem sr10p84:∀ i ∈ List.range 1,StrictCheckAt 10 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 84 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 84) 10 84:=by decide +kernel
  exact strictAtFast_sound (row 10 84) 10 84 hvalid hfast

theorem sr10p85:∀ i ∈ List.range 1,StrictCheckAt 10 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 85 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 85) 10 85:=by decide +kernel
  exact strictAtFast_sound (row 10 85) 10 85 hvalid hfast

theorem sr10p86:∀ i ∈ List.range 1,StrictCheckAt 10 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 86 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 86) 10 86:=by decide +kernel
  exact strictAtFast_sound (row 10 86) 10 86 hvalid hfast

theorem sr10p87:∀ i ∈ List.range 1,StrictCheckAt 10 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 87 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 87) 10 87:=by decide +kernel
  exact strictAtFast_sound (row 10 87) 10 87 hvalid hfast

theorem sr10p88:∀ i ∈ List.range 1,StrictCheckAt 10 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 88 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 88) 10 88:=by decide +kernel
  exact strictAtFast_sound (row 10 88) 10 88 hvalid hfast

theorem sr10p89:∀ i ∈ List.range 1,StrictCheckAt 10 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 89 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 89) 10 89:=by decide +kernel
  exact strictAtFast_sound (row 10 89) 10 89 hvalid hfast

theorem sr10p90:∀ i ∈ List.range 1,StrictCheckAt 10 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 90 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 90) 10 90:=by decide +kernel
  exact strictAtFast_sound (row 10 90) 10 90 hvalid hfast

theorem sr10p91:∀ i ∈ List.range 1,StrictCheckAt 10 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 91 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 91) 10 91:=by decide +kernel
  exact strictAtFast_sound (row 10 91) 10 91 hvalid hfast

theorem sr10p92:∀ i ∈ List.range 1,StrictCheckAt 10 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 92 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 92) 10 92:=by decide +kernel
  exact strictAtFast_sound (row 10 92) 10 92 hvalid hfast

theorem sr10p93:∀ i ∈ List.range 1,StrictCheckAt 10 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 93 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 93) 10 93:=by decide +kernel
  exact strictAtFast_sound (row 10 93) 10 93 hvalid hfast

theorem sr10p94:∀ i ∈ List.range 1,StrictCheckAt 10 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 94 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 94) 10 94:=by decide +kernel
  exact strictAtFast_sound (row 10 94) 10 94 hvalid hfast

theorem sr10p95:∀ i ∈ List.range 1,StrictCheckAt 10 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 95 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 95) 10 95:=by decide +kernel
  exact strictAtFast_sound (row 10 95) 10 95 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
