import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked31FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr31p64:∀ i ∈ List.range 1,StrictCheckAt 31 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 64 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 64) 31 64:=by decide +kernel
  exact strictAtFast_sound (row 31 64) 31 64 hvalid hfast

theorem sr31p65:∀ i ∈ List.range 1,StrictCheckAt 31 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 65 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 65) 31 65:=by decide +kernel
  exact strictAtFast_sound (row 31 65) 31 65 hvalid hfast

theorem sr31p66:∀ i ∈ List.range 1,StrictCheckAt 31 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 66 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 66) 31 66:=by decide +kernel
  exact strictAtFast_sound (row 31 66) 31 66 hvalid hfast

theorem sr31p67:∀ i ∈ List.range 1,StrictCheckAt 31 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 67 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 67) 31 67:=by decide +kernel
  exact strictAtFast_sound (row 31 67) 31 67 hvalid hfast

theorem sr31p68:∀ i ∈ List.range 1,StrictCheckAt 31 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 68 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 68) 31 68:=by decide +kernel
  exact strictAtFast_sound (row 31 68) 31 68 hvalid hfast

theorem sr31p69:∀ i ∈ List.range 1,StrictCheckAt 31 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 69 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 69) 31 69:=by decide +kernel
  exact strictAtFast_sound (row 31 69) 31 69 hvalid hfast

theorem sr31p70:∀ i ∈ List.range 1,StrictCheckAt 31 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 70 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 70) 31 70:=by decide +kernel
  exact strictAtFast_sound (row 31 70) 31 70 hvalid hfast

theorem sr31p71:∀ i ∈ List.range 1,StrictCheckAt 31 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 71 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 71) 31 71:=by decide +kernel
  exact strictAtFast_sound (row 31 71) 31 71 hvalid hfast

theorem sr31p72:∀ i ∈ List.range 1,StrictCheckAt 31 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 72 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 72) 31 72:=by decide +kernel
  exact strictAtFast_sound (row 31 72) 31 72 hvalid hfast

theorem sr31p73:∀ i ∈ List.range 1,StrictCheckAt 31 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 73 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 73) 31 73:=by decide +kernel
  exact strictAtFast_sound (row 31 73) 31 73 hvalid hfast

theorem sr31p74:∀ i ∈ List.range 1,StrictCheckAt 31 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 74 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 74) 31 74:=by decide +kernel
  exact strictAtFast_sound (row 31 74) 31 74 hvalid hfast

theorem sr31p75:∀ i ∈ List.range 1,StrictCheckAt 31 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 75 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 75) 31 75:=by decide +kernel
  exact strictAtFast_sound (row 31 75) 31 75 hvalid hfast

theorem sr31p76:∀ i ∈ List.range 1,StrictCheckAt 31 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 76 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 76) 31 76:=by decide +kernel
  exact strictAtFast_sound (row 31 76) 31 76 hvalid hfast

theorem sr31p77:∀ i ∈ List.range 1,StrictCheckAt 31 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 77 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 77) 31 77:=by decide +kernel
  exact strictAtFast_sound (row 31 77) 31 77 hvalid hfast

theorem sr31p78:∀ i ∈ List.range 1,StrictCheckAt 31 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 78 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 78) 31 78:=by decide +kernel
  exact strictAtFast_sound (row 31 78) 31 78 hvalid hfast

theorem sr31p79:∀ i ∈ List.range 1,StrictCheckAt 31 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 79 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 79) 31 79:=by decide +kernel
  exact strictAtFast_sound (row 31 79) 31 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
