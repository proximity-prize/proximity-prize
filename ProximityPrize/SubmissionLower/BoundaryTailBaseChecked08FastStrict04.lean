import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked08FastStrict03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr8p48:∀ i ∈ List.range 1,StrictCheckAt 8 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 48 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 48) 8 48:=by decide +kernel
  exact strictAtFast_sound (row 8 48) 8 48 hvalid hfast

theorem sr8p49:∀ i ∈ List.range 1,StrictCheckAt 8 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 49 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 49) 8 49:=by decide +kernel
  exact strictAtFast_sound (row 8 49) 8 49 hvalid hfast

theorem sr8p50:∀ i ∈ List.range 1,StrictCheckAt 8 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 50 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 50) 8 50:=by decide +kernel
  exact strictAtFast_sound (row 8 50) 8 50 hvalid hfast

theorem sr8p51:∀ i ∈ List.range 1,StrictCheckAt 8 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 51 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 51) 8 51:=by decide +kernel
  exact strictAtFast_sound (row 8 51) 8 51 hvalid hfast

theorem sr8p52:∀ i ∈ List.range 1,StrictCheckAt 8 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 52 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 52) 8 52:=by decide +kernel
  exact strictAtFast_sound (row 8 52) 8 52 hvalid hfast

theorem sr8p53:∀ i ∈ List.range 1,StrictCheckAt 8 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 53 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 53) 8 53:=by decide +kernel
  exact strictAtFast_sound (row 8 53) 8 53 hvalid hfast

theorem sr8p54:∀ i ∈ List.range 1,StrictCheckAt 8 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 54 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 54) 8 54:=by decide +kernel
  exact strictAtFast_sound (row 8 54) 8 54 hvalid hfast

theorem sr8p55:∀ i ∈ List.range 1,StrictCheckAt 8 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 55 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 55) 8 55:=by decide +kernel
  exact strictAtFast_sound (row 8 55) 8 55 hvalid hfast

theorem sr8p56:∀ i ∈ List.range 1,StrictCheckAt 8 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 56 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 56) 8 56:=by decide +kernel
  exact strictAtFast_sound (row 8 56) 8 56 hvalid hfast

theorem sr8p57:∀ i ∈ List.range 1,StrictCheckAt 8 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 57 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 57) 8 57:=by decide +kernel
  exact strictAtFast_sound (row 8 57) 8 57 hvalid hfast

theorem sr8p58:∀ i ∈ List.range 1,StrictCheckAt 8 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 58 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 58) 8 58:=by decide +kernel
  exact strictAtFast_sound (row 8 58) 8 58 hvalid hfast

theorem sr8p59:∀ i ∈ List.range 1,StrictCheckAt 8 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 59 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 59) 8 59:=by decide +kernel
  exact strictAtFast_sound (row 8 59) 8 59 hvalid hfast

theorem sr8p60:∀ i ∈ List.range 1,StrictCheckAt 8 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 60 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 60) 8 60:=by decide +kernel
  exact strictAtFast_sound (row 8 60) 8 60 hvalid hfast

theorem sr8p61:∀ i ∈ List.range 1,StrictCheckAt 8 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 61 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 61) 8 61:=by decide +kernel
  exact strictAtFast_sound (row 8 61) 8 61 hvalid hfast

theorem sr8p62:∀ i ∈ List.range 1,StrictCheckAt 8 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 62 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 62) 8 62:=by decide +kernel
  exact strictAtFast_sound (row 8 62) 8 62 hvalid hfast

theorem sr8p63:∀ i ∈ List.range 1,StrictCheckAt 8 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 63 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 8 63) 8 63:=by decide +kernel
  exact strictAtFast_sound (row 8 63) 8 63 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
