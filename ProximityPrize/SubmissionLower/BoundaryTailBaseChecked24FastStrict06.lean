import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked24FastStrict05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr24p80:∀ i ∈ List.range 1,StrictCheckAt 24 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 80 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 80) 24 80:=by decide +kernel
  exact strictAtFast_sound (row 24 80) 24 80 hvalid hfast

theorem sr24p81:∀ i ∈ List.range 1,StrictCheckAt 24 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 81 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 81) 24 81:=by decide +kernel
  exact strictAtFast_sound (row 24 81) 24 81 hvalid hfast

theorem sr24p82:∀ i ∈ List.range 1,StrictCheckAt 24 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 82 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 82) 24 82:=by decide +kernel
  exact strictAtFast_sound (row 24 82) 24 82 hvalid hfast

theorem sr24p83:∀ i ∈ List.range 1,StrictCheckAt 24 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 83 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 83) 24 83:=by decide +kernel
  exact strictAtFast_sound (row 24 83) 24 83 hvalid hfast

theorem sr24p84:∀ i ∈ List.range 1,StrictCheckAt 24 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 84 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 84) 24 84:=by decide +kernel
  exact strictAtFast_sound (row 24 84) 24 84 hvalid hfast

theorem sr24p85:∀ i ∈ List.range 1,StrictCheckAt 24 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 85 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 85) 24 85:=by decide +kernel
  exact strictAtFast_sound (row 24 85) 24 85 hvalid hfast

theorem sr24p86:∀ i ∈ List.range 1,StrictCheckAt 24 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 86 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 86) 24 86:=by decide +kernel
  exact strictAtFast_sound (row 24 86) 24 86 hvalid hfast

theorem sr24p87:∀ i ∈ List.range 1,StrictCheckAt 24 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 87 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 87) 24 87:=by decide +kernel
  exact strictAtFast_sound (row 24 87) 24 87 hvalid hfast

theorem sr24p88:∀ i ∈ List.range 1,StrictCheckAt 24 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 88 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 88) 24 88:=by decide +kernel
  exact strictAtFast_sound (row 24 88) 24 88 hvalid hfast

theorem sr24p89:∀ i ∈ List.range 1,StrictCheckAt 24 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 89 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 89) 24 89:=by decide +kernel
  exact strictAtFast_sound (row 24 89) 24 89 hvalid hfast

theorem sr24p90:∀ i ∈ List.range 1,StrictCheckAt 24 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 90 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 90) 24 90:=by decide +kernel
  exact strictAtFast_sound (row 24 90) 24 90 hvalid hfast

theorem sr24p91:∀ i ∈ List.range 1,StrictCheckAt 24 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 91 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 91) 24 91:=by decide +kernel
  exact strictAtFast_sound (row 24 91) 24 91 hvalid hfast

theorem sr24p92:∀ i ∈ List.range 1,StrictCheckAt 24 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 92 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 92) 24 92:=by decide +kernel
  exact strictAtFast_sound (row 24 92) 24 92 hvalid hfast

theorem sr24p93:∀ i ∈ List.range 1,StrictCheckAt 24 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 93 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 93) 24 93:=by decide +kernel
  exact strictAtFast_sound (row 24 93) 24 93 hvalid hfast

theorem sr24p94:∀ i ∈ List.range 1,StrictCheckAt 24 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 94 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 94) 24 94:=by decide +kernel
  exact strictAtFast_sound (row 24 94) 24 94 hvalid hfast

theorem sr24p95:∀ i ∈ List.range 1,StrictCheckAt 24 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 95 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 95) 24 95:=by decide +kernel
  exact strictAtFast_sound (row 24 95) 24 95 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
