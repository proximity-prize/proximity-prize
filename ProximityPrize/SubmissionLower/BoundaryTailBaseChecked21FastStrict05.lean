import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked21FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr21p64:∀ i ∈ List.range 1,StrictCheckAt 21 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 64 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 64) 21 64:=by decide +kernel
  exact strictAtFast_sound (row 21 64) 21 64 hvalid hfast

theorem sr21p65:∀ i ∈ List.range 1,StrictCheckAt 21 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 65 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 65) 21 65:=by decide +kernel
  exact strictAtFast_sound (row 21 65) 21 65 hvalid hfast

theorem sr21p66:∀ i ∈ List.range 1,StrictCheckAt 21 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 66 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 66) 21 66:=by decide +kernel
  exact strictAtFast_sound (row 21 66) 21 66 hvalid hfast

theorem sr21p67:∀ i ∈ List.range 1,StrictCheckAt 21 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 67 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 67) 21 67:=by decide +kernel
  exact strictAtFast_sound (row 21 67) 21 67 hvalid hfast

theorem sr21p68:∀ i ∈ List.range 1,StrictCheckAt 21 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 68 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 68) 21 68:=by decide +kernel
  exact strictAtFast_sound (row 21 68) 21 68 hvalid hfast

theorem sr21p69:∀ i ∈ List.range 1,StrictCheckAt 21 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 69 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 69) 21 69:=by decide +kernel
  exact strictAtFast_sound (row 21 69) 21 69 hvalid hfast

theorem sr21p70:∀ i ∈ List.range 1,StrictCheckAt 21 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 70 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 70) 21 70:=by decide +kernel
  exact strictAtFast_sound (row 21 70) 21 70 hvalid hfast

theorem sr21p71:∀ i ∈ List.range 1,StrictCheckAt 21 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 71 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 71) 21 71:=by decide +kernel
  exact strictAtFast_sound (row 21 71) 21 71 hvalid hfast

theorem sr21p72:∀ i ∈ List.range 1,StrictCheckAt 21 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 72 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 72) 21 72:=by decide +kernel
  exact strictAtFast_sound (row 21 72) 21 72 hvalid hfast

theorem sr21p73:∀ i ∈ List.range 1,StrictCheckAt 21 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 73 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 73) 21 73:=by decide +kernel
  exact strictAtFast_sound (row 21 73) 21 73 hvalid hfast

theorem sr21p74:∀ i ∈ List.range 1,StrictCheckAt 21 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 74 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 74) 21 74:=by decide +kernel
  exact strictAtFast_sound (row 21 74) 21 74 hvalid hfast

theorem sr21p75:∀ i ∈ List.range 1,StrictCheckAt 21 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 75 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 75) 21 75:=by decide +kernel
  exact strictAtFast_sound (row 21 75) 21 75 hvalid hfast

theorem sr21p76:∀ i ∈ List.range 1,StrictCheckAt 21 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 76 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 76) 21 76:=by decide +kernel
  exact strictAtFast_sound (row 21 76) 21 76 hvalid hfast

theorem sr21p77:∀ i ∈ List.range 1,StrictCheckAt 21 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 77 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 77) 21 77:=by decide +kernel
  exact strictAtFast_sound (row 21 77) 21 77 hvalid hfast

theorem sr21p78:∀ i ∈ List.range 1,StrictCheckAt 21 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 78 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 78) 21 78:=by decide +kernel
  exact strictAtFast_sound (row 21 78) 21 78 hvalid hfast

theorem sr21p79:∀ i ∈ List.range 1,StrictCheckAt 21 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 79 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 21 79) 21 79:=by decide +kernel
  exact strictAtFast_sound (row 21 79) 21 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
