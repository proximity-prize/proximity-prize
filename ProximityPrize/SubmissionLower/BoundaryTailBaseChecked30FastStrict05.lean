import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked30FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr30p64:∀ i ∈ List.range 1,StrictCheckAt 30 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 64 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 64) 30 64:=by decide +kernel
  exact strictAtFast_sound (row 30 64) 30 64 hvalid hfast

theorem sr30p65:∀ i ∈ List.range 1,StrictCheckAt 30 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 65 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 65) 30 65:=by decide +kernel
  exact strictAtFast_sound (row 30 65) 30 65 hvalid hfast

theorem sr30p66:∀ i ∈ List.range 1,StrictCheckAt 30 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 66 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 66) 30 66:=by decide +kernel
  exact strictAtFast_sound (row 30 66) 30 66 hvalid hfast

theorem sr30p67:∀ i ∈ List.range 1,StrictCheckAt 30 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 67 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 67) 30 67:=by decide +kernel
  exact strictAtFast_sound (row 30 67) 30 67 hvalid hfast

theorem sr30p68:∀ i ∈ List.range 1,StrictCheckAt 30 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 68 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 68) 30 68:=by decide +kernel
  exact strictAtFast_sound (row 30 68) 30 68 hvalid hfast

theorem sr30p69:∀ i ∈ List.range 1,StrictCheckAt 30 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 69 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 69) 30 69:=by decide +kernel
  exact strictAtFast_sound (row 30 69) 30 69 hvalid hfast

theorem sr30p70:∀ i ∈ List.range 1,StrictCheckAt 30 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 70 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 70) 30 70:=by decide +kernel
  exact strictAtFast_sound (row 30 70) 30 70 hvalid hfast

theorem sr30p71:∀ i ∈ List.range 1,StrictCheckAt 30 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 71 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 71) 30 71:=by decide +kernel
  exact strictAtFast_sound (row 30 71) 30 71 hvalid hfast

theorem sr30p72:∀ i ∈ List.range 1,StrictCheckAt 30 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 72 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 72) 30 72:=by decide +kernel
  exact strictAtFast_sound (row 30 72) 30 72 hvalid hfast

theorem sr30p73:∀ i ∈ List.range 1,StrictCheckAt 30 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 73 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 73) 30 73:=by decide +kernel
  exact strictAtFast_sound (row 30 73) 30 73 hvalid hfast

theorem sr30p74:∀ i ∈ List.range 1,StrictCheckAt 30 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 74 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 74) 30 74:=by decide +kernel
  exact strictAtFast_sound (row 30 74) 30 74 hvalid hfast

theorem sr30p75:∀ i ∈ List.range 1,StrictCheckAt 30 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 75 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 75) 30 75:=by decide +kernel
  exact strictAtFast_sound (row 30 75) 30 75 hvalid hfast

theorem sr30p76:∀ i ∈ List.range 1,StrictCheckAt 30 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 76 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 76) 30 76:=by decide +kernel
  exact strictAtFast_sound (row 30 76) 30 76 hvalid hfast

theorem sr30p77:∀ i ∈ List.range 1,StrictCheckAt 30 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 77 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 77) 30 77:=by decide +kernel
  exact strictAtFast_sound (row 30 77) 30 77 hvalid hfast

theorem sr30p78:∀ i ∈ List.range 1,StrictCheckAt 30 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 78 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 78) 30 78:=by decide +kernel
  exact strictAtFast_sound (row 30 78) 30 78 hvalid hfast

theorem sr30p79:∀ i ∈ List.range 1,StrictCheckAt 30 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 79 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 79) 30 79:=by decide +kernel
  exact strictAtFast_sound (row 30 79) 30 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
