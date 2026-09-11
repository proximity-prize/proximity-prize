import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked11FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr11p64:∀ i ∈ List.range 1,StrictCheckAt 11 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 64 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 64) 11 64:=by decide +kernel
  exact strictAtFast_sound (row 11 64) 11 64 hvalid hfast

theorem sr11p65:∀ i ∈ List.range 1,StrictCheckAt 11 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 65 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 65) 11 65:=by decide +kernel
  exact strictAtFast_sound (row 11 65) 11 65 hvalid hfast

theorem sr11p66:∀ i ∈ List.range 1,StrictCheckAt 11 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 66 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 66) 11 66:=by decide +kernel
  exact strictAtFast_sound (row 11 66) 11 66 hvalid hfast

theorem sr11p67:∀ i ∈ List.range 1,StrictCheckAt 11 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 67 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 67) 11 67:=by decide +kernel
  exact strictAtFast_sound (row 11 67) 11 67 hvalid hfast

theorem sr11p68:∀ i ∈ List.range 1,StrictCheckAt 11 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 68 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 68) 11 68:=by decide +kernel
  exact strictAtFast_sound (row 11 68) 11 68 hvalid hfast

theorem sr11p69:∀ i ∈ List.range 1,StrictCheckAt 11 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 69 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 69) 11 69:=by decide +kernel
  exact strictAtFast_sound (row 11 69) 11 69 hvalid hfast

theorem sr11p70:∀ i ∈ List.range 1,StrictCheckAt 11 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 70 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 70) 11 70:=by decide +kernel
  exact strictAtFast_sound (row 11 70) 11 70 hvalid hfast

theorem sr11p71:∀ i ∈ List.range 1,StrictCheckAt 11 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 71 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 71) 11 71:=by decide +kernel
  exact strictAtFast_sound (row 11 71) 11 71 hvalid hfast

theorem sr11p72:∀ i ∈ List.range 1,StrictCheckAt 11 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 72 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 72) 11 72:=by decide +kernel
  exact strictAtFast_sound (row 11 72) 11 72 hvalid hfast

theorem sr11p73:∀ i ∈ List.range 1,StrictCheckAt 11 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 73 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 73) 11 73:=by decide +kernel
  exact strictAtFast_sound (row 11 73) 11 73 hvalid hfast

theorem sr11p74:∀ i ∈ List.range 1,StrictCheckAt 11 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 74 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 74) 11 74:=by decide +kernel
  exact strictAtFast_sound (row 11 74) 11 74 hvalid hfast

theorem sr11p75:∀ i ∈ List.range 1,StrictCheckAt 11 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 75 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 75) 11 75:=by decide +kernel
  exact strictAtFast_sound (row 11 75) 11 75 hvalid hfast

theorem sr11p76:∀ i ∈ List.range 1,StrictCheckAt 11 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 76 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 76) 11 76:=by decide +kernel
  exact strictAtFast_sound (row 11 76) 11 76 hvalid hfast

theorem sr11p77:∀ i ∈ List.range 1,StrictCheckAt 11 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 77 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 77) 11 77:=by decide +kernel
  exact strictAtFast_sound (row 11 77) 11 77 hvalid hfast

theorem sr11p78:∀ i ∈ List.range 1,StrictCheckAt 11 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 78 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 78) 11 78:=by decide +kernel
  exact strictAtFast_sound (row 11 78) 11 78 hvalid hfast

theorem sr11p79:∀ i ∈ List.range 1,StrictCheckAt 11 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 79 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 79) 11 79:=by decide +kernel
  exact strictAtFast_sound (row 11 79) 11 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
