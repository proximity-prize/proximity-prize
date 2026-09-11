import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked17FastStrict03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr17p48:∀ i ∈ List.range 1,StrictCheckAt 17 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 48 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 48) 17 48:=by decide +kernel
  exact strictAtFast_sound (row 17 48) 17 48 hvalid hfast

theorem sr17p49:∀ i ∈ List.range 1,StrictCheckAt 17 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 49 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 49) 17 49:=by decide +kernel
  exact strictAtFast_sound (row 17 49) 17 49 hvalid hfast

theorem sr17p50:∀ i ∈ List.range 1,StrictCheckAt 17 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 50 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 50) 17 50:=by decide +kernel
  exact strictAtFast_sound (row 17 50) 17 50 hvalid hfast

theorem sr17p51:∀ i ∈ List.range 1,StrictCheckAt 17 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 51 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 51) 17 51:=by decide +kernel
  exact strictAtFast_sound (row 17 51) 17 51 hvalid hfast

theorem sr17p52:∀ i ∈ List.range 1,StrictCheckAt 17 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 52 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 52) 17 52:=by decide +kernel
  exact strictAtFast_sound (row 17 52) 17 52 hvalid hfast

theorem sr17p53:∀ i ∈ List.range 1,StrictCheckAt 17 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 53 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 53) 17 53:=by decide +kernel
  exact strictAtFast_sound (row 17 53) 17 53 hvalid hfast

theorem sr17p54:∀ i ∈ List.range 1,StrictCheckAt 17 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 54 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 54) 17 54:=by decide +kernel
  exact strictAtFast_sound (row 17 54) 17 54 hvalid hfast

theorem sr17p55:∀ i ∈ List.range 1,StrictCheckAt 17 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 55 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 55) 17 55:=by decide +kernel
  exact strictAtFast_sound (row 17 55) 17 55 hvalid hfast

theorem sr17p56:∀ i ∈ List.range 1,StrictCheckAt 17 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 56 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 56) 17 56:=by decide +kernel
  exact strictAtFast_sound (row 17 56) 17 56 hvalid hfast

theorem sr17p57:∀ i ∈ List.range 1,StrictCheckAt 17 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 57 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 57) 17 57:=by decide +kernel
  exact strictAtFast_sound (row 17 57) 17 57 hvalid hfast

theorem sr17p58:∀ i ∈ List.range 1,StrictCheckAt 17 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 58 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 58) 17 58:=by decide +kernel
  exact strictAtFast_sound (row 17 58) 17 58 hvalid hfast

theorem sr17p59:∀ i ∈ List.range 1,StrictCheckAt 17 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 59 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 59) 17 59:=by decide +kernel
  exact strictAtFast_sound (row 17 59) 17 59 hvalid hfast

theorem sr17p60:∀ i ∈ List.range 1,StrictCheckAt 17 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 60 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 60) 17 60:=by decide +kernel
  exact strictAtFast_sound (row 17 60) 17 60 hvalid hfast

theorem sr17p61:∀ i ∈ List.range 1,StrictCheckAt 17 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 61 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 61) 17 61:=by decide +kernel
  exact strictAtFast_sound (row 17 61) 17 61 hvalid hfast

theorem sr17p62:∀ i ∈ List.range 1,StrictCheckAt 17 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 62 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 62) 17 62:=by decide +kernel
  exact strictAtFast_sound (row 17 62) 17 62 hvalid hfast

theorem sr17p63:∀ i ∈ List.range 1,StrictCheckAt 17 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 63 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 17 63) 17 63:=by decide +kernel
  exact strictAtFast_sound (row 17 63) 17 63 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
