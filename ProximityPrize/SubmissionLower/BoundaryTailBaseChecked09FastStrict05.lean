import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked09FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr9p64:∀ i ∈ List.range 1,StrictCheckAt 9 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 64 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 64) 9 64:=by decide +kernel
  exact strictAtFast_sound (row 9 64) 9 64 hvalid hfast

theorem sr9p65:∀ i ∈ List.range 1,StrictCheckAt 9 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 65 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 65) 9 65:=by decide +kernel
  exact strictAtFast_sound (row 9 65) 9 65 hvalid hfast

theorem sr9p66:∀ i ∈ List.range 1,StrictCheckAt 9 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 66 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 66) 9 66:=by decide +kernel
  exact strictAtFast_sound (row 9 66) 9 66 hvalid hfast

theorem sr9p67:∀ i ∈ List.range 1,StrictCheckAt 9 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 67 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 67) 9 67:=by decide +kernel
  exact strictAtFast_sound (row 9 67) 9 67 hvalid hfast

theorem sr9p68:∀ i ∈ List.range 1,StrictCheckAt 9 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 68 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 68) 9 68:=by decide +kernel
  exact strictAtFast_sound (row 9 68) 9 68 hvalid hfast

theorem sr9p69:∀ i ∈ List.range 1,StrictCheckAt 9 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 69 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 69) 9 69:=by decide +kernel
  exact strictAtFast_sound (row 9 69) 9 69 hvalid hfast

theorem sr9p70:∀ i ∈ List.range 1,StrictCheckAt 9 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 70 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 70) 9 70:=by decide +kernel
  exact strictAtFast_sound (row 9 70) 9 70 hvalid hfast

theorem sr9p71:∀ i ∈ List.range 1,StrictCheckAt 9 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 71 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 71) 9 71:=by decide +kernel
  exact strictAtFast_sound (row 9 71) 9 71 hvalid hfast

theorem sr9p72:∀ i ∈ List.range 1,StrictCheckAt 9 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 72 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 72) 9 72:=by decide +kernel
  exact strictAtFast_sound (row 9 72) 9 72 hvalid hfast

theorem sr9p73:∀ i ∈ List.range 1,StrictCheckAt 9 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 73 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 73) 9 73:=by decide +kernel
  exact strictAtFast_sound (row 9 73) 9 73 hvalid hfast

theorem sr9p74:∀ i ∈ List.range 1,StrictCheckAt 9 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 74 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 74) 9 74:=by decide +kernel
  exact strictAtFast_sound (row 9 74) 9 74 hvalid hfast

theorem sr9p75:∀ i ∈ List.range 1,StrictCheckAt 9 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 75 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 75) 9 75:=by decide +kernel
  exact strictAtFast_sound (row 9 75) 9 75 hvalid hfast

theorem sr9p76:∀ i ∈ List.range 1,StrictCheckAt 9 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 76 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 76) 9 76:=by decide +kernel
  exact strictAtFast_sound (row 9 76) 9 76 hvalid hfast

theorem sr9p77:∀ i ∈ List.range 1,StrictCheckAt 9 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 77 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 77) 9 77:=by decide +kernel
  exact strictAtFast_sound (row 9 77) 9 77 hvalid hfast

theorem sr9p78:∀ i ∈ List.range 1,StrictCheckAt 9 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 78 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 78) 9 78:=by decide +kernel
  exact strictAtFast_sound (row 9 78) 9 78 hvalid hfast

theorem sr9p79:∀ i ∈ List.range 1,StrictCheckAt 9 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 79 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 79) 9 79:=by decide +kernel
  exact strictAtFast_sound (row 9 79) 9 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
