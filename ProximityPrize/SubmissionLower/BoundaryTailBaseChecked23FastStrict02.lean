import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked23FastStrict01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr23p16:∀ i ∈ List.range 1,StrictCheckAt 23 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 16 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 23 16) 23 16:=by decide +kernel
  exact strictAtFast_sound (row 23 16) 23 16 hvalid hfast

theorem sr23p17:∀ i ∈ List.range 1,StrictCheckAt 23 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 17 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 23 17) 23 17:=by decide +kernel
  exact strictAtFast_sound (row 23 17) 23 17 hvalid hfast

theorem sr23p18:∀ i ∈ List.range 1,StrictCheckAt 23 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 18 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 23 18) 23 18:=by decide +kernel
  exact strictAtFast_sound (row 23 18) 23 18 hvalid hfast

theorem sr23p19:∀ i ∈ List.range 1,StrictCheckAt 23 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 19 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 23 19) 23 19:=by decide +kernel
  exact strictAtFast_sound (row 23 19) 23 19 hvalid hfast

theorem sr23p20:∀ i ∈ List.range 1,StrictCheckAt 23 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 20 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 23 20) 23 20:=by decide +kernel
  exact strictAtFast_sound (row 23 20) 23 20 hvalid hfast

theorem sr23p21:∀ i ∈ List.range 1,StrictCheckAt 23 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 21 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 23 21) 23 21:=by decide +kernel
  exact strictAtFast_sound (row 23 21) 23 21 hvalid hfast

theorem sr23p22:∀ i ∈ List.range 1,StrictCheckAt 23 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 22 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 23 22) 23 22:=by decide +kernel
  exact strictAtFast_sound (row 23 22) 23 22 hvalid hfast

theorem sr23p23:∀ i ∈ List.range 1,StrictCheckAt 23 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 23 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 23 23) 23 23:=by decide +kernel
  exact strictAtFast_sound (row 23 23) 23 23 hvalid hfast

theorem sr23p24:∀ i ∈ List.range 1,StrictCheckAt 23 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 24 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 23 24) 23 24:=by decide +kernel
  exact strictAtFast_sound (row 23 24) 23 24 hvalid hfast

theorem sr23p25:∀ i ∈ List.range 1,StrictCheckAt 23 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 25 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 23 25) 23 25:=by decide +kernel
  exact strictAtFast_sound (row 23 25) 23 25 hvalid hfast

theorem sr23p26:∀ i ∈ List.range 1,StrictCheckAt 23 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 26 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 23 26) 23 26:=by decide +kernel
  exact strictAtFast_sound (row 23 26) 23 26 hvalid hfast

theorem sr23p27:∀ i ∈ List.range 1,StrictCheckAt 23 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 27 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 23 27) 23 27:=by decide +kernel
  exact strictAtFast_sound (row 23 27) 23 27 hvalid hfast

theorem sr23p28:∀ i ∈ List.range 1,StrictCheckAt 23 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 28 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 23 28) 23 28:=by decide +kernel
  exact strictAtFast_sound (row 23 28) 23 28 hvalid hfast

theorem sr23p29:∀ i ∈ List.range 1,StrictCheckAt 23 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 29 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 23 29) 23 29:=by decide +kernel
  exact strictAtFast_sound (row 23 29) 23 29 hvalid hfast

theorem sr23p30:∀ i ∈ List.range 1,StrictCheckAt 23 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 30 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 23 30) 23 30:=by decide +kernel
  exact strictAtFast_sound (row 23 30) 23 30 hvalid hfast

theorem sr23p31:∀ i ∈ List.range 1,StrictCheckAt 23 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 31 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 23 31) 23 31:=by decide +kernel
  exact strictAtFast_sound (row 23 31) 23 31 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
