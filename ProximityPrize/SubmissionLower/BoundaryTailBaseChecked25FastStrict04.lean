import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked25FastStrict03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr25p48:∀ i ∈ List.range 1,StrictCheckAt 25 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 48 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 48) 25 48:=by decide +kernel
  exact strictAtFast_sound (row 25 48) 25 48 hvalid hfast

theorem sr25p49:∀ i ∈ List.range 1,StrictCheckAt 25 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 49 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 49) 25 49:=by decide +kernel
  exact strictAtFast_sound (row 25 49) 25 49 hvalid hfast

theorem sr25p50:∀ i ∈ List.range 1,StrictCheckAt 25 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 50 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 50) 25 50:=by decide +kernel
  exact strictAtFast_sound (row 25 50) 25 50 hvalid hfast

theorem sr25p51:∀ i ∈ List.range 1,StrictCheckAt 25 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 51 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 51) 25 51:=by decide +kernel
  exact strictAtFast_sound (row 25 51) 25 51 hvalid hfast

theorem sr25p52:∀ i ∈ List.range 1,StrictCheckAt 25 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 52 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 52) 25 52:=by decide +kernel
  exact strictAtFast_sound (row 25 52) 25 52 hvalid hfast

theorem sr25p53:∀ i ∈ List.range 1,StrictCheckAt 25 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 53 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 53) 25 53:=by decide +kernel
  exact strictAtFast_sound (row 25 53) 25 53 hvalid hfast

theorem sr25p54:∀ i ∈ List.range 1,StrictCheckAt 25 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 54 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 54) 25 54:=by decide +kernel
  exact strictAtFast_sound (row 25 54) 25 54 hvalid hfast

theorem sr25p55:∀ i ∈ List.range 1,StrictCheckAt 25 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 55 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 55) 25 55:=by decide +kernel
  exact strictAtFast_sound (row 25 55) 25 55 hvalid hfast

theorem sr25p56:∀ i ∈ List.range 1,StrictCheckAt 25 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 56 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 56) 25 56:=by decide +kernel
  exact strictAtFast_sound (row 25 56) 25 56 hvalid hfast

theorem sr25p57:∀ i ∈ List.range 1,StrictCheckAt 25 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 57 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 57) 25 57:=by decide +kernel
  exact strictAtFast_sound (row 25 57) 25 57 hvalid hfast

theorem sr25p58:∀ i ∈ List.range 1,StrictCheckAt 25 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 58 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 58) 25 58:=by decide +kernel
  exact strictAtFast_sound (row 25 58) 25 58 hvalid hfast

theorem sr25p59:∀ i ∈ List.range 1,StrictCheckAt 25 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 59 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 59) 25 59:=by decide +kernel
  exact strictAtFast_sound (row 25 59) 25 59 hvalid hfast

theorem sr25p60:∀ i ∈ List.range 1,StrictCheckAt 25 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 60 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 60) 25 60:=by decide +kernel
  exact strictAtFast_sound (row 25 60) 25 60 hvalid hfast

theorem sr25p61:∀ i ∈ List.range 1,StrictCheckAt 25 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 61 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 61) 25 61:=by decide +kernel
  exact strictAtFast_sound (row 25 61) 25 61 hvalid hfast

theorem sr25p62:∀ i ∈ List.range 1,StrictCheckAt 25 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 62 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 62) 25 62:=by decide +kernel
  exact strictAtFast_sound (row 25 62) 25 62 hvalid hfast

theorem sr25p63:∀ i ∈ List.range 1,StrictCheckAt 25 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 63 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 25 63) 25 63:=by decide +kernel
  exact strictAtFast_sound (row 25 63) 25 63 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
