import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked30FastStrict03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr30p48:∀ i ∈ List.range 1,StrictCheckAt 30 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 48 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 48) 30 48:=by decide +kernel
  exact strictAtFast_sound (row 30 48) 30 48 hvalid hfast

theorem sr30p49:∀ i ∈ List.range 1,StrictCheckAt 30 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 49 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 49) 30 49:=by decide +kernel
  exact strictAtFast_sound (row 30 49) 30 49 hvalid hfast

theorem sr30p50:∀ i ∈ List.range 1,StrictCheckAt 30 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 50 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 50) 30 50:=by decide +kernel
  exact strictAtFast_sound (row 30 50) 30 50 hvalid hfast

theorem sr30p51:∀ i ∈ List.range 1,StrictCheckAt 30 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 51 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 51) 30 51:=by decide +kernel
  exact strictAtFast_sound (row 30 51) 30 51 hvalid hfast

theorem sr30p52:∀ i ∈ List.range 1,StrictCheckAt 30 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 52 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 52) 30 52:=by decide +kernel
  exact strictAtFast_sound (row 30 52) 30 52 hvalid hfast

theorem sr30p53:∀ i ∈ List.range 1,StrictCheckAt 30 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 53 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 53) 30 53:=by decide +kernel
  exact strictAtFast_sound (row 30 53) 30 53 hvalid hfast

theorem sr30p54:∀ i ∈ List.range 1,StrictCheckAt 30 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 54 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 54) 30 54:=by decide +kernel
  exact strictAtFast_sound (row 30 54) 30 54 hvalid hfast

theorem sr30p55:∀ i ∈ List.range 1,StrictCheckAt 30 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 55 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 55) 30 55:=by decide +kernel
  exact strictAtFast_sound (row 30 55) 30 55 hvalid hfast

theorem sr30p56:∀ i ∈ List.range 1,StrictCheckAt 30 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 56 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 56) 30 56:=by decide +kernel
  exact strictAtFast_sound (row 30 56) 30 56 hvalid hfast

theorem sr30p57:∀ i ∈ List.range 1,StrictCheckAt 30 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 57 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 57) 30 57:=by decide +kernel
  exact strictAtFast_sound (row 30 57) 30 57 hvalid hfast

theorem sr30p58:∀ i ∈ List.range 1,StrictCheckAt 30 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 58 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 58) 30 58:=by decide +kernel
  exact strictAtFast_sound (row 30 58) 30 58 hvalid hfast

theorem sr30p59:∀ i ∈ List.range 1,StrictCheckAt 30 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 59 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 59) 30 59:=by decide +kernel
  exact strictAtFast_sound (row 30 59) 30 59 hvalid hfast

theorem sr30p60:∀ i ∈ List.range 1,StrictCheckAt 30 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 60 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 60) 30 60:=by decide +kernel
  exact strictAtFast_sound (row 30 60) 30 60 hvalid hfast

theorem sr30p61:∀ i ∈ List.range 1,StrictCheckAt 30 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 61 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 61) 30 61:=by decide +kernel
  exact strictAtFast_sound (row 30 61) 30 61 hvalid hfast

theorem sr30p62:∀ i ∈ List.range 1,StrictCheckAt 30 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 62 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 62) 30 62:=by decide +kernel
  exact strictAtFast_sound (row 30 62) 30 62 hvalid hfast

theorem sr30p63:∀ i ∈ List.range 1,StrictCheckAt 30 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 63 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 63) 30 63:=by decide +kernel
  exact strictAtFast_sound (row 30 63) 30 63 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
