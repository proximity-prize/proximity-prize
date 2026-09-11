import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked22FastStrict03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr22p48:∀ i ∈ List.range 1,StrictCheckAt 22 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 48 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 48) 22 48:=by decide +kernel
  exact strictAtFast_sound (row 22 48) 22 48 hvalid hfast

theorem sr22p49:∀ i ∈ List.range 1,StrictCheckAt 22 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 49 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 49) 22 49:=by decide +kernel
  exact strictAtFast_sound (row 22 49) 22 49 hvalid hfast

theorem sr22p50:∀ i ∈ List.range 1,StrictCheckAt 22 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 50 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 50) 22 50:=by decide +kernel
  exact strictAtFast_sound (row 22 50) 22 50 hvalid hfast

theorem sr22p51:∀ i ∈ List.range 1,StrictCheckAt 22 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 51 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 51) 22 51:=by decide +kernel
  exact strictAtFast_sound (row 22 51) 22 51 hvalid hfast

theorem sr22p52:∀ i ∈ List.range 1,StrictCheckAt 22 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 52 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 52) 22 52:=by decide +kernel
  exact strictAtFast_sound (row 22 52) 22 52 hvalid hfast

theorem sr22p53:∀ i ∈ List.range 1,StrictCheckAt 22 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 53 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 53) 22 53:=by decide +kernel
  exact strictAtFast_sound (row 22 53) 22 53 hvalid hfast

theorem sr22p54:∀ i ∈ List.range 1,StrictCheckAt 22 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 54 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 54) 22 54:=by decide +kernel
  exact strictAtFast_sound (row 22 54) 22 54 hvalid hfast

theorem sr22p55:∀ i ∈ List.range 1,StrictCheckAt 22 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 55 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 55) 22 55:=by decide +kernel
  exact strictAtFast_sound (row 22 55) 22 55 hvalid hfast

theorem sr22p56:∀ i ∈ List.range 1,StrictCheckAt 22 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 56 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 56) 22 56:=by decide +kernel
  exact strictAtFast_sound (row 22 56) 22 56 hvalid hfast

theorem sr22p57:∀ i ∈ List.range 1,StrictCheckAt 22 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 57 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 57) 22 57:=by decide +kernel
  exact strictAtFast_sound (row 22 57) 22 57 hvalid hfast

theorem sr22p58:∀ i ∈ List.range 1,StrictCheckAt 22 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 58 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 58) 22 58:=by decide +kernel
  exact strictAtFast_sound (row 22 58) 22 58 hvalid hfast

theorem sr22p59:∀ i ∈ List.range 1,StrictCheckAt 22 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 59 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 59) 22 59:=by decide +kernel
  exact strictAtFast_sound (row 22 59) 22 59 hvalid hfast

theorem sr22p60:∀ i ∈ List.range 1,StrictCheckAt 22 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 60 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 60) 22 60:=by decide +kernel
  exact strictAtFast_sound (row 22 60) 22 60 hvalid hfast

theorem sr22p61:∀ i ∈ List.range 1,StrictCheckAt 22 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 61 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 61) 22 61:=by decide +kernel
  exact strictAtFast_sound (row 22 61) 22 61 hvalid hfast

theorem sr22p62:∀ i ∈ List.range 1,StrictCheckAt 22 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 62 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 62) 22 62:=by decide +kernel
  exact strictAtFast_sound (row 22 62) 22 62 hvalid hfast

theorem sr22p63:∀ i ∈ List.range 1,StrictCheckAt 22 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 63 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 22 63) 22 63:=by decide +kernel
  exact strictAtFast_sound (row 22 63) 22 63 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
