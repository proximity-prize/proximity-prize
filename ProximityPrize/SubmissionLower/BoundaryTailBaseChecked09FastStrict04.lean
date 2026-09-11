import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked09FastStrict03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr9p48:∀ i ∈ List.range 1,StrictCheckAt 9 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 48 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 48) 9 48:=by decide +kernel
  exact strictAtFast_sound (row 9 48) 9 48 hvalid hfast

theorem sr9p49:∀ i ∈ List.range 1,StrictCheckAt 9 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 49 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 49) 9 49:=by decide +kernel
  exact strictAtFast_sound (row 9 49) 9 49 hvalid hfast

theorem sr9p50:∀ i ∈ List.range 1,StrictCheckAt 9 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 50 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 50) 9 50:=by decide +kernel
  exact strictAtFast_sound (row 9 50) 9 50 hvalid hfast

theorem sr9p51:∀ i ∈ List.range 1,StrictCheckAt 9 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 51 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 51) 9 51:=by decide +kernel
  exact strictAtFast_sound (row 9 51) 9 51 hvalid hfast

theorem sr9p52:∀ i ∈ List.range 1,StrictCheckAt 9 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 52 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 52) 9 52:=by decide +kernel
  exact strictAtFast_sound (row 9 52) 9 52 hvalid hfast

theorem sr9p53:∀ i ∈ List.range 1,StrictCheckAt 9 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 53 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 53) 9 53:=by decide +kernel
  exact strictAtFast_sound (row 9 53) 9 53 hvalid hfast

theorem sr9p54:∀ i ∈ List.range 1,StrictCheckAt 9 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 54 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 54) 9 54:=by decide +kernel
  exact strictAtFast_sound (row 9 54) 9 54 hvalid hfast

theorem sr9p55:∀ i ∈ List.range 1,StrictCheckAt 9 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 55 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 55) 9 55:=by decide +kernel
  exact strictAtFast_sound (row 9 55) 9 55 hvalid hfast

theorem sr9p56:∀ i ∈ List.range 1,StrictCheckAt 9 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 56 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 56) 9 56:=by decide +kernel
  exact strictAtFast_sound (row 9 56) 9 56 hvalid hfast

theorem sr9p57:∀ i ∈ List.range 1,StrictCheckAt 9 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 57 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 57) 9 57:=by decide +kernel
  exact strictAtFast_sound (row 9 57) 9 57 hvalid hfast

theorem sr9p58:∀ i ∈ List.range 1,StrictCheckAt 9 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 58 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 58) 9 58:=by decide +kernel
  exact strictAtFast_sound (row 9 58) 9 58 hvalid hfast

theorem sr9p59:∀ i ∈ List.range 1,StrictCheckAt 9 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 59 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 59) 9 59:=by decide +kernel
  exact strictAtFast_sound (row 9 59) 9 59 hvalid hfast

theorem sr9p60:∀ i ∈ List.range 1,StrictCheckAt 9 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 60 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 60) 9 60:=by decide +kernel
  exact strictAtFast_sound (row 9 60) 9 60 hvalid hfast

theorem sr9p61:∀ i ∈ List.range 1,StrictCheckAt 9 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 61 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 61) 9 61:=by decide +kernel
  exact strictAtFast_sound (row 9 61) 9 61 hvalid hfast

theorem sr9p62:∀ i ∈ List.range 1,StrictCheckAt 9 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 62 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 62) 9 62:=by decide +kernel
  exact strictAtFast_sound (row 9 62) 9 62 hvalid hfast

theorem sr9p63:∀ i ∈ List.range 1,StrictCheckAt 9 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 63 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 63) 9 63:=by decide +kernel
  exact strictAtFast_sound (row 9 63) 9 63 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
