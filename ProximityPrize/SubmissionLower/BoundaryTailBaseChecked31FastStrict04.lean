import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked31FastStrict03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr31p48:∀ i ∈ List.range 1,StrictCheckAt 31 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 48 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 48) 31 48:=by decide +kernel
  exact strictAtFast_sound (row 31 48) 31 48 hvalid hfast

theorem sr31p49:∀ i ∈ List.range 1,StrictCheckAt 31 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 49 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 49) 31 49:=by decide +kernel
  exact strictAtFast_sound (row 31 49) 31 49 hvalid hfast

theorem sr31p50:∀ i ∈ List.range 1,StrictCheckAt 31 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 50 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 50) 31 50:=by decide +kernel
  exact strictAtFast_sound (row 31 50) 31 50 hvalid hfast

theorem sr31p51:∀ i ∈ List.range 1,StrictCheckAt 31 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 51 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 51) 31 51:=by decide +kernel
  exact strictAtFast_sound (row 31 51) 31 51 hvalid hfast

theorem sr31p52:∀ i ∈ List.range 1,StrictCheckAt 31 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 52 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 52) 31 52:=by decide +kernel
  exact strictAtFast_sound (row 31 52) 31 52 hvalid hfast

theorem sr31p53:∀ i ∈ List.range 1,StrictCheckAt 31 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 53 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 53) 31 53:=by decide +kernel
  exact strictAtFast_sound (row 31 53) 31 53 hvalid hfast

theorem sr31p54:∀ i ∈ List.range 1,StrictCheckAt 31 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 54 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 54) 31 54:=by decide +kernel
  exact strictAtFast_sound (row 31 54) 31 54 hvalid hfast

theorem sr31p55:∀ i ∈ List.range 1,StrictCheckAt 31 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 55 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 55) 31 55:=by decide +kernel
  exact strictAtFast_sound (row 31 55) 31 55 hvalid hfast

theorem sr31p56:∀ i ∈ List.range 1,StrictCheckAt 31 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 56 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 56) 31 56:=by decide +kernel
  exact strictAtFast_sound (row 31 56) 31 56 hvalid hfast

theorem sr31p57:∀ i ∈ List.range 1,StrictCheckAt 31 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 57 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 57) 31 57:=by decide +kernel
  exact strictAtFast_sound (row 31 57) 31 57 hvalid hfast

theorem sr31p58:∀ i ∈ List.range 1,StrictCheckAt 31 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 58 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 58) 31 58:=by decide +kernel
  exact strictAtFast_sound (row 31 58) 31 58 hvalid hfast

theorem sr31p59:∀ i ∈ List.range 1,StrictCheckAt 31 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 59 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 59) 31 59:=by decide +kernel
  exact strictAtFast_sound (row 31 59) 31 59 hvalid hfast

theorem sr31p60:∀ i ∈ List.range 1,StrictCheckAt 31 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 60 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 60) 31 60:=by decide +kernel
  exact strictAtFast_sound (row 31 60) 31 60 hvalid hfast

theorem sr31p61:∀ i ∈ List.range 1,StrictCheckAt 31 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 61 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 61) 31 61:=by decide +kernel
  exact strictAtFast_sound (row 31 61) 31 61 hvalid hfast

theorem sr31p62:∀ i ∈ List.range 1,StrictCheckAt 31 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 62 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 62) 31 62:=by decide +kernel
  exact strictAtFast_sound (row 31 62) 31 62 hvalid hfast

theorem sr31p63:∀ i ∈ List.range 1,StrictCheckAt 31 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 63 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 63) 31 63:=by decide +kernel
  exact strictAtFast_sound (row 31 63) 31 63 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
