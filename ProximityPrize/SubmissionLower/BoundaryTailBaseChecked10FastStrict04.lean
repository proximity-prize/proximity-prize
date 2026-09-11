import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10FastStrict03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr10p48:∀ i ∈ List.range 1,StrictCheckAt 10 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 48 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 48) 10 48:=by decide +kernel
  exact strictAtFast_sound (row 10 48) 10 48 hvalid hfast

theorem sr10p49:∀ i ∈ List.range 1,StrictCheckAt 10 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 49 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 49) 10 49:=by decide +kernel
  exact strictAtFast_sound (row 10 49) 10 49 hvalid hfast

theorem sr10p50:∀ i ∈ List.range 1,StrictCheckAt 10 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 50 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 50) 10 50:=by decide +kernel
  exact strictAtFast_sound (row 10 50) 10 50 hvalid hfast

theorem sr10p51:∀ i ∈ List.range 1,StrictCheckAt 10 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 51 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 51) 10 51:=by decide +kernel
  exact strictAtFast_sound (row 10 51) 10 51 hvalid hfast

theorem sr10p52:∀ i ∈ List.range 1,StrictCheckAt 10 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 52 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 52) 10 52:=by decide +kernel
  exact strictAtFast_sound (row 10 52) 10 52 hvalid hfast

theorem sr10p53:∀ i ∈ List.range 1,StrictCheckAt 10 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 53 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 53) 10 53:=by decide +kernel
  exact strictAtFast_sound (row 10 53) 10 53 hvalid hfast

theorem sr10p54:∀ i ∈ List.range 1,StrictCheckAt 10 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 54 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 54) 10 54:=by decide +kernel
  exact strictAtFast_sound (row 10 54) 10 54 hvalid hfast

theorem sr10p55:∀ i ∈ List.range 1,StrictCheckAt 10 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 55 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 55) 10 55:=by decide +kernel
  exact strictAtFast_sound (row 10 55) 10 55 hvalid hfast

theorem sr10p56:∀ i ∈ List.range 1,StrictCheckAt 10 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 56 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 56) 10 56:=by decide +kernel
  exact strictAtFast_sound (row 10 56) 10 56 hvalid hfast

theorem sr10p57:∀ i ∈ List.range 1,StrictCheckAt 10 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 57 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 57) 10 57:=by decide +kernel
  exact strictAtFast_sound (row 10 57) 10 57 hvalid hfast

theorem sr10p58:∀ i ∈ List.range 1,StrictCheckAt 10 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 58 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 58) 10 58:=by decide +kernel
  exact strictAtFast_sound (row 10 58) 10 58 hvalid hfast

theorem sr10p59:∀ i ∈ List.range 1,StrictCheckAt 10 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 59 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 59) 10 59:=by decide +kernel
  exact strictAtFast_sound (row 10 59) 10 59 hvalid hfast

theorem sr10p60:∀ i ∈ List.range 1,StrictCheckAt 10 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 60 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 60) 10 60:=by decide +kernel
  exact strictAtFast_sound (row 10 60) 10 60 hvalid hfast

theorem sr10p61:∀ i ∈ List.range 1,StrictCheckAt 10 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 61 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 61) 10 61:=by decide +kernel
  exact strictAtFast_sound (row 10 61) 10 61 hvalid hfast

theorem sr10p62:∀ i ∈ List.range 1,StrictCheckAt 10 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 62 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 62) 10 62:=by decide +kernel
  exact strictAtFast_sound (row 10 62) 10 62 hvalid hfast

theorem sr10p63:∀ i ∈ List.range 1,StrictCheckAt 10 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 63 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 10 63) 10 63:=by decide +kernel
  exact strictAtFast_sound (row 10 63) 10 63 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
