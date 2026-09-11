import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked08FastStrict05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr8p80:∀ i ∈ List.range 1,StrictCheckAt 8 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 80 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 80) 8 80:=by decide +kernel
  exact strictAtFast_sound (row 8 80) 8 80 hvalid hfast

theorem sr8p81:∀ i ∈ List.range 1,StrictCheckAt 8 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 81 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 81) 8 81:=by decide +kernel
  exact strictAtFast_sound (row 8 81) 8 81 hvalid hfast

theorem sr8p82:∀ i ∈ List.range 1,StrictCheckAt 8 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 82 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 82) 8 82:=by decide +kernel
  exact strictAtFast_sound (row 8 82) 8 82 hvalid hfast

theorem sr8p83:∀ i ∈ List.range 1,StrictCheckAt 8 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 83 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 83) 8 83:=by decide +kernel
  exact strictAtFast_sound (row 8 83) 8 83 hvalid hfast

theorem sr8p84:∀ i ∈ List.range 1,StrictCheckAt 8 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 84 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 84) 8 84:=by decide +kernel
  exact strictAtFast_sound (row 8 84) 8 84 hvalid hfast

theorem sr8p85:∀ i ∈ List.range 1,StrictCheckAt 8 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 85 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 85) 8 85:=by decide +kernel
  exact strictAtFast_sound (row 8 85) 8 85 hvalid hfast

theorem sr8p86:∀ i ∈ List.range 1,StrictCheckAt 8 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 86 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 86) 8 86:=by decide +kernel
  exact strictAtFast_sound (row 8 86) 8 86 hvalid hfast

theorem sr8p87:∀ i ∈ List.range 1,StrictCheckAt 8 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 87 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 87) 8 87:=by decide +kernel
  exact strictAtFast_sound (row 8 87) 8 87 hvalid hfast

theorem sr8p88:∀ i ∈ List.range 1,StrictCheckAt 8 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 88 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 88) 8 88:=by decide +kernel
  exact strictAtFast_sound (row 8 88) 8 88 hvalid hfast

theorem sr8p89:∀ i ∈ List.range 1,StrictCheckAt 8 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 89 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 89) 8 89:=by decide +kernel
  exact strictAtFast_sound (row 8 89) 8 89 hvalid hfast

theorem sr8p90:∀ i ∈ List.range 1,StrictCheckAt 8 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 90 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 90) 8 90:=by decide +kernel
  exact strictAtFast_sound (row 8 90) 8 90 hvalid hfast

theorem sr8p91:∀ i ∈ List.range 1,StrictCheckAt 8 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 91 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 91) 8 91:=by decide +kernel
  exact strictAtFast_sound (row 8 91) 8 91 hvalid hfast

theorem sr8p92:∀ i ∈ List.range 1,StrictCheckAt 8 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 92 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 92) 8 92:=by decide +kernel
  exact strictAtFast_sound (row 8 92) 8 92 hvalid hfast

theorem sr8p93:∀ i ∈ List.range 1,StrictCheckAt 8 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 93 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 93) 8 93:=by decide +kernel
  exact strictAtFast_sound (row 8 93) 8 93 hvalid hfast

theorem sr8p94:∀ i ∈ List.range 1,StrictCheckAt 8 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 94 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 94) 8 94:=by decide +kernel
  exact strictAtFast_sound (row 8 94) 8 94 hvalid hfast

theorem sr8p95:∀ i ∈ List.range 1,StrictCheckAt 8 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 95 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 95) 8 95:=by decide +kernel
  exact strictAtFast_sound (row 8 95) 8 95 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
