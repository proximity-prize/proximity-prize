import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked15FastStrict01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr15p16:∀ i ∈ List.range 1,StrictCheckAt 15 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 16 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 16) 15 16:=by decide +kernel
  exact strictAtFast_sound (row 15 16) 15 16 hvalid hfast

theorem sr15p17:∀ i ∈ List.range 1,StrictCheckAt 15 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 17 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 17) 15 17:=by decide +kernel
  exact strictAtFast_sound (row 15 17) 15 17 hvalid hfast

theorem sr15p18:∀ i ∈ List.range 1,StrictCheckAt 15 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 18 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 18) 15 18:=by decide +kernel
  exact strictAtFast_sound (row 15 18) 15 18 hvalid hfast

theorem sr15p19:∀ i ∈ List.range 1,StrictCheckAt 15 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 19 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 19) 15 19:=by decide +kernel
  exact strictAtFast_sound (row 15 19) 15 19 hvalid hfast

theorem sr15p20:∀ i ∈ List.range 1,StrictCheckAt 15 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 20 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 20) 15 20:=by decide +kernel
  exact strictAtFast_sound (row 15 20) 15 20 hvalid hfast

theorem sr15p21:∀ i ∈ List.range 1,StrictCheckAt 15 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 21 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 21) 15 21:=by decide +kernel
  exact strictAtFast_sound (row 15 21) 15 21 hvalid hfast

theorem sr15p22:∀ i ∈ List.range 1,StrictCheckAt 15 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 22 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 22) 15 22:=by decide +kernel
  exact strictAtFast_sound (row 15 22) 15 22 hvalid hfast

theorem sr15p23:∀ i ∈ List.range 1,StrictCheckAt 15 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 23 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 23) 15 23:=by decide +kernel
  exact strictAtFast_sound (row 15 23) 15 23 hvalid hfast

theorem sr15p24:∀ i ∈ List.range 1,StrictCheckAt 15 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 24 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 24) 15 24:=by decide +kernel
  exact strictAtFast_sound (row 15 24) 15 24 hvalid hfast

theorem sr15p25:∀ i ∈ List.range 1,StrictCheckAt 15 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 25 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 25) 15 25:=by decide +kernel
  exact strictAtFast_sound (row 15 25) 15 25 hvalid hfast

theorem sr15p26:∀ i ∈ List.range 1,StrictCheckAt 15 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 26 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 26) 15 26:=by decide +kernel
  exact strictAtFast_sound (row 15 26) 15 26 hvalid hfast

theorem sr15p27:∀ i ∈ List.range 1,StrictCheckAt 15 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 27 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 27) 15 27:=by decide +kernel
  exact strictAtFast_sound (row 15 27) 15 27 hvalid hfast

theorem sr15p28:∀ i ∈ List.range 1,StrictCheckAt 15 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 28 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 28) 15 28:=by decide +kernel
  exact strictAtFast_sound (row 15 28) 15 28 hvalid hfast

theorem sr15p29:∀ i ∈ List.range 1,StrictCheckAt 15 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 29 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 29) 15 29:=by decide +kernel
  exact strictAtFast_sound (row 15 29) 15 29 hvalid hfast

theorem sr15p30:∀ i ∈ List.range 1,StrictCheckAt 15 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 30 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 30) 15 30:=by decide +kernel
  exact strictAtFast_sound (row 15 30) 15 30 hvalid hfast

theorem sr15p31:∀ i ∈ List.range 1,StrictCheckAt 15 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 31 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 15 31) 15 31:=by decide +kernel
  exact strictAtFast_sound (row 15 31) 15 31 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
