import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18FastStrict01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr18p16:∀ i ∈ List.range 1,StrictCheckAt 18 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 16 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 16) 18 16:=by decide +kernel
  exact strictAtFast_sound (row 18 16) 18 16 hvalid hfast

theorem sr18p17:∀ i ∈ List.range 1,StrictCheckAt 18 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 17 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 17) 18 17:=by decide +kernel
  exact strictAtFast_sound (row 18 17) 18 17 hvalid hfast

theorem sr18p18:∀ i ∈ List.range 1,StrictCheckAt 18 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 18 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 18) 18 18:=by decide +kernel
  exact strictAtFast_sound (row 18 18) 18 18 hvalid hfast

theorem sr18p19:∀ i ∈ List.range 1,StrictCheckAt 18 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 19 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 19) 18 19:=by decide +kernel
  exact strictAtFast_sound (row 18 19) 18 19 hvalid hfast

theorem sr18p20:∀ i ∈ List.range 1,StrictCheckAt 18 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 20 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 20) 18 20:=by decide +kernel
  exact strictAtFast_sound (row 18 20) 18 20 hvalid hfast

theorem sr18p21:∀ i ∈ List.range 1,StrictCheckAt 18 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 21 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 21) 18 21:=by decide +kernel
  exact strictAtFast_sound (row 18 21) 18 21 hvalid hfast

theorem sr18p22:∀ i ∈ List.range 1,StrictCheckAt 18 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 22 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 22) 18 22:=by decide +kernel
  exact strictAtFast_sound (row 18 22) 18 22 hvalid hfast

theorem sr18p23:∀ i ∈ List.range 1,StrictCheckAt 18 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 23 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 23) 18 23:=by decide +kernel
  exact strictAtFast_sound (row 18 23) 18 23 hvalid hfast

theorem sr18p24:∀ i ∈ List.range 1,StrictCheckAt 18 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 24 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 24) 18 24:=by decide +kernel
  exact strictAtFast_sound (row 18 24) 18 24 hvalid hfast

theorem sr18p25:∀ i ∈ List.range 1,StrictCheckAt 18 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 25 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 25) 18 25:=by decide +kernel
  exact strictAtFast_sound (row 18 25) 18 25 hvalid hfast

theorem sr18p26:∀ i ∈ List.range 1,StrictCheckAt 18 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 26 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 26) 18 26:=by decide +kernel
  exact strictAtFast_sound (row 18 26) 18 26 hvalid hfast

theorem sr18p27:∀ i ∈ List.range 1,StrictCheckAt 18 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 27 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 27) 18 27:=by decide +kernel
  exact strictAtFast_sound (row 18 27) 18 27 hvalid hfast

theorem sr18p28:∀ i ∈ List.range 1,StrictCheckAt 18 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 28 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 28) 18 28:=by decide +kernel
  exact strictAtFast_sound (row 18 28) 18 28 hvalid hfast

theorem sr18p29:∀ i ∈ List.range 1,StrictCheckAt 18 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 29 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 29) 18 29:=by decide +kernel
  exact strictAtFast_sound (row 18 29) 18 29 hvalid hfast

theorem sr18p30:∀ i ∈ List.range 1,StrictCheckAt 18 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 30 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 30) 18 30:=by decide +kernel
  exact strictAtFast_sound (row 18 30) 18 30 hvalid hfast

theorem sr18p31:∀ i ∈ List.range 1,StrictCheckAt 18 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 31 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 31) 18 31:=by decide +kernel
  exact strictAtFast_sound (row 18 31) 18 31 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
