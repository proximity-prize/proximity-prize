import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked29FastStrict01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr29p16:∀ i ∈ List.range 1,StrictCheckAt 29 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 16 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 16) 29 16:=by decide +kernel
  exact strictAtFast_sound (row 29 16) 29 16 hvalid hfast

theorem sr29p17:∀ i ∈ List.range 1,StrictCheckAt 29 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 17 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 17) 29 17:=by decide +kernel
  exact strictAtFast_sound (row 29 17) 29 17 hvalid hfast

theorem sr29p18:∀ i ∈ List.range 1,StrictCheckAt 29 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 18 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 18) 29 18:=by decide +kernel
  exact strictAtFast_sound (row 29 18) 29 18 hvalid hfast

theorem sr29p19:∀ i ∈ List.range 1,StrictCheckAt 29 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 19 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 19) 29 19:=by decide +kernel
  exact strictAtFast_sound (row 29 19) 29 19 hvalid hfast

theorem sr29p20:∀ i ∈ List.range 1,StrictCheckAt 29 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 20 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 20) 29 20:=by decide +kernel
  exact strictAtFast_sound (row 29 20) 29 20 hvalid hfast

theorem sr29p21:∀ i ∈ List.range 1,StrictCheckAt 29 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 21 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 21) 29 21:=by decide +kernel
  exact strictAtFast_sound (row 29 21) 29 21 hvalid hfast

theorem sr29p22:∀ i ∈ List.range 1,StrictCheckAt 29 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 22 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 22) 29 22:=by decide +kernel
  exact strictAtFast_sound (row 29 22) 29 22 hvalid hfast

theorem sr29p23:∀ i ∈ List.range 1,StrictCheckAt 29 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 23 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 23) 29 23:=by decide +kernel
  exact strictAtFast_sound (row 29 23) 29 23 hvalid hfast

theorem sr29p24:∀ i ∈ List.range 1,StrictCheckAt 29 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 24 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 24) 29 24:=by decide +kernel
  exact strictAtFast_sound (row 29 24) 29 24 hvalid hfast

theorem sr29p25:∀ i ∈ List.range 1,StrictCheckAt 29 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 25 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 25) 29 25:=by decide +kernel
  exact strictAtFast_sound (row 29 25) 29 25 hvalid hfast

theorem sr29p26:∀ i ∈ List.range 1,StrictCheckAt 29 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 26 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 26) 29 26:=by decide +kernel
  exact strictAtFast_sound (row 29 26) 29 26 hvalid hfast

theorem sr29p27:∀ i ∈ List.range 1,StrictCheckAt 29 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 27 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 27) 29 27:=by decide +kernel
  exact strictAtFast_sound (row 29 27) 29 27 hvalid hfast

theorem sr29p28:∀ i ∈ List.range 1,StrictCheckAt 29 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 28 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 28) 29 28:=by decide +kernel
  exact strictAtFast_sound (row 29 28) 29 28 hvalid hfast

theorem sr29p29:∀ i ∈ List.range 1,StrictCheckAt 29 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 29 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 29) 29 29:=by decide +kernel
  exact strictAtFast_sound (row 29 29) 29 29 hvalid hfast

theorem sr29p30:∀ i ∈ List.range 1,StrictCheckAt 29 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 30 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 30) 29 30:=by decide +kernel
  exact strictAtFast_sound (row 29 30) 29 30 hvalid hfast

theorem sr29p31:∀ i ∈ List.range 1,StrictCheckAt 29 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 31 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 31) 29 31:=by decide +kernel
  exact strictAtFast_sound (row 29 31) 29 31 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
