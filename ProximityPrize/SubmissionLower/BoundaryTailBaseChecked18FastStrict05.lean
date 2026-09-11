import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr18p64:∀ i ∈ List.range 1,StrictCheckAt 18 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 64 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 64) 18 64:=by decide +kernel
  exact strictAtFast_sound (row 18 64) 18 64 hvalid hfast

theorem sr18p65:∀ i ∈ List.range 1,StrictCheckAt 18 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 65 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 65) 18 65:=by decide +kernel
  exact strictAtFast_sound (row 18 65) 18 65 hvalid hfast

theorem sr18p66:∀ i ∈ List.range 1,StrictCheckAt 18 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 66 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 66) 18 66:=by decide +kernel
  exact strictAtFast_sound (row 18 66) 18 66 hvalid hfast

theorem sr18p67:∀ i ∈ List.range 1,StrictCheckAt 18 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 67 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 67) 18 67:=by decide +kernel
  exact strictAtFast_sound (row 18 67) 18 67 hvalid hfast

theorem sr18p68:∀ i ∈ List.range 1,StrictCheckAt 18 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 68 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 68) 18 68:=by decide +kernel
  exact strictAtFast_sound (row 18 68) 18 68 hvalid hfast

theorem sr18p69:∀ i ∈ List.range 1,StrictCheckAt 18 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 69 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 69) 18 69:=by decide +kernel
  exact strictAtFast_sound (row 18 69) 18 69 hvalid hfast

theorem sr18p70:∀ i ∈ List.range 1,StrictCheckAt 18 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 70 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 70) 18 70:=by decide +kernel
  exact strictAtFast_sound (row 18 70) 18 70 hvalid hfast

theorem sr18p71:∀ i ∈ List.range 1,StrictCheckAt 18 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 71 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 71) 18 71:=by decide +kernel
  exact strictAtFast_sound (row 18 71) 18 71 hvalid hfast

theorem sr18p72:∀ i ∈ List.range 1,StrictCheckAt 18 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 72 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 72) 18 72:=by decide +kernel
  exact strictAtFast_sound (row 18 72) 18 72 hvalid hfast

theorem sr18p73:∀ i ∈ List.range 1,StrictCheckAt 18 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 73 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 73) 18 73:=by decide +kernel
  exact strictAtFast_sound (row 18 73) 18 73 hvalid hfast

theorem sr18p74:∀ i ∈ List.range 1,StrictCheckAt 18 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 74 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 74) 18 74:=by decide +kernel
  exact strictAtFast_sound (row 18 74) 18 74 hvalid hfast

theorem sr18p75:∀ i ∈ List.range 1,StrictCheckAt 18 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 75 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 75) 18 75:=by decide +kernel
  exact strictAtFast_sound (row 18 75) 18 75 hvalid hfast

theorem sr18p76:∀ i ∈ List.range 1,StrictCheckAt 18 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 76 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 76) 18 76:=by decide +kernel
  exact strictAtFast_sound (row 18 76) 18 76 hvalid hfast

theorem sr18p77:∀ i ∈ List.range 1,StrictCheckAt 18 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 77 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 77) 18 77:=by decide +kernel
  exact strictAtFast_sound (row 18 77) 18 77 hvalid hfast

theorem sr18p78:∀ i ∈ List.range 1,StrictCheckAt 18 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 78 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 78) 18 78:=by decide +kernel
  exact strictAtFast_sound (row 18 78) 18 78 hvalid hfast

theorem sr18p79:∀ i ∈ List.range 1,StrictCheckAt 18 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 79 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 79) 18 79:=by decide +kernel
  exact strictAtFast_sound (row 18 79) 18 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
