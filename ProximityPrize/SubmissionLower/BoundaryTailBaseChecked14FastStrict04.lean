import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked14FastStrict03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr14p48:∀ i ∈ List.range 1,StrictCheckAt 14 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 48 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 48) 14 48:=by decide +kernel
  exact strictAtFast_sound (row 14 48) 14 48 hvalid hfast

theorem sr14p49:∀ i ∈ List.range 1,StrictCheckAt 14 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 49 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 49) 14 49:=by decide +kernel
  exact strictAtFast_sound (row 14 49) 14 49 hvalid hfast

theorem sr14p50:∀ i ∈ List.range 1,StrictCheckAt 14 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 50 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 50) 14 50:=by decide +kernel
  exact strictAtFast_sound (row 14 50) 14 50 hvalid hfast

theorem sr14p51:∀ i ∈ List.range 1,StrictCheckAt 14 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 51 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 51) 14 51:=by decide +kernel
  exact strictAtFast_sound (row 14 51) 14 51 hvalid hfast

theorem sr14p52:∀ i ∈ List.range 1,StrictCheckAt 14 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 52 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 52) 14 52:=by decide +kernel
  exact strictAtFast_sound (row 14 52) 14 52 hvalid hfast

theorem sr14p53:∀ i ∈ List.range 1,StrictCheckAt 14 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 53 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 53) 14 53:=by decide +kernel
  exact strictAtFast_sound (row 14 53) 14 53 hvalid hfast

theorem sr14p54:∀ i ∈ List.range 1,StrictCheckAt 14 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 54 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 54) 14 54:=by decide +kernel
  exact strictAtFast_sound (row 14 54) 14 54 hvalid hfast

theorem sr14p55:∀ i ∈ List.range 1,StrictCheckAt 14 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 55 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 55) 14 55:=by decide +kernel
  exact strictAtFast_sound (row 14 55) 14 55 hvalid hfast

theorem sr14p56:∀ i ∈ List.range 1,StrictCheckAt 14 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 56 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 56) 14 56:=by decide +kernel
  exact strictAtFast_sound (row 14 56) 14 56 hvalid hfast

theorem sr14p57:∀ i ∈ List.range 1,StrictCheckAt 14 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 57 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 57) 14 57:=by decide +kernel
  exact strictAtFast_sound (row 14 57) 14 57 hvalid hfast

theorem sr14p58:∀ i ∈ List.range 1,StrictCheckAt 14 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 58 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 58) 14 58:=by decide +kernel
  exact strictAtFast_sound (row 14 58) 14 58 hvalid hfast

theorem sr14p59:∀ i ∈ List.range 1,StrictCheckAt 14 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 59 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 59) 14 59:=by decide +kernel
  exact strictAtFast_sound (row 14 59) 14 59 hvalid hfast

theorem sr14p60:∀ i ∈ List.range 1,StrictCheckAt 14 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 60 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 60) 14 60:=by decide +kernel
  exact strictAtFast_sound (row 14 60) 14 60 hvalid hfast

theorem sr14p61:∀ i ∈ List.range 1,StrictCheckAt 14 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 61 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 61) 14 61:=by decide +kernel
  exact strictAtFast_sound (row 14 61) 14 61 hvalid hfast

theorem sr14p62:∀ i ∈ List.range 1,StrictCheckAt 14 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 62 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 62) 14 62:=by decide +kernel
  exact strictAtFast_sound (row 14 62) 14 62 hvalid hfast

theorem sr14p63:∀ i ∈ List.range 1,StrictCheckAt 14 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 63 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 63) 14 63:=by decide +kernel
  exact strictAtFast_sound (row 14 63) 14 63 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
