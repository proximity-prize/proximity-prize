import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked16FastStrict01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr16p16:∀ i ∈ List.range 1,StrictCheckAt 16 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 16 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 16) 16 16:=by decide +kernel
  exact strictAtFast_sound (row 16 16) 16 16 hvalid hfast

theorem sr16p17:∀ i ∈ List.range 1,StrictCheckAt 16 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 17 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 17) 16 17:=by decide +kernel
  exact strictAtFast_sound (row 16 17) 16 17 hvalid hfast

theorem sr16p18:∀ i ∈ List.range 1,StrictCheckAt 16 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 18 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 18) 16 18:=by decide +kernel
  exact strictAtFast_sound (row 16 18) 16 18 hvalid hfast

theorem sr16p19:∀ i ∈ List.range 1,StrictCheckAt 16 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 19 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 19) 16 19:=by decide +kernel
  exact strictAtFast_sound (row 16 19) 16 19 hvalid hfast

theorem sr16p20:∀ i ∈ List.range 1,StrictCheckAt 16 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 20 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 20) 16 20:=by decide +kernel
  exact strictAtFast_sound (row 16 20) 16 20 hvalid hfast

theorem sr16p21:∀ i ∈ List.range 1,StrictCheckAt 16 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 21 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 21) 16 21:=by decide +kernel
  exact strictAtFast_sound (row 16 21) 16 21 hvalid hfast

theorem sr16p22:∀ i ∈ List.range 1,StrictCheckAt 16 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 22 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 22) 16 22:=by decide +kernel
  exact strictAtFast_sound (row 16 22) 16 22 hvalid hfast

theorem sr16p23:∀ i ∈ List.range 1,StrictCheckAt 16 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 23 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 23) 16 23:=by decide +kernel
  exact strictAtFast_sound (row 16 23) 16 23 hvalid hfast

theorem sr16p24:∀ i ∈ List.range 1,StrictCheckAt 16 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 24 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 24) 16 24:=by decide +kernel
  exact strictAtFast_sound (row 16 24) 16 24 hvalid hfast

theorem sr16p25:∀ i ∈ List.range 1,StrictCheckAt 16 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 25 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 25) 16 25:=by decide +kernel
  exact strictAtFast_sound (row 16 25) 16 25 hvalid hfast

theorem sr16p26:∀ i ∈ List.range 1,StrictCheckAt 16 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 26 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 26) 16 26:=by decide +kernel
  exact strictAtFast_sound (row 16 26) 16 26 hvalid hfast

theorem sr16p27:∀ i ∈ List.range 1,StrictCheckAt 16 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 27 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 27) 16 27:=by decide +kernel
  exact strictAtFast_sound (row 16 27) 16 27 hvalid hfast

theorem sr16p28:∀ i ∈ List.range 1,StrictCheckAt 16 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 28 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 28) 16 28:=by decide +kernel
  exact strictAtFast_sound (row 16 28) 16 28 hvalid hfast

theorem sr16p29:∀ i ∈ List.range 1,StrictCheckAt 16 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 29 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 29) 16 29:=by decide +kernel
  exact strictAtFast_sound (row 16 29) 16 29 hvalid hfast

theorem sr16p30:∀ i ∈ List.range 1,StrictCheckAt 16 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 30 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 30) 16 30:=by decide +kernel
  exact strictAtFast_sound (row 16 30) 16 30 hvalid hfast

theorem sr16p31:∀ i ∈ List.range 1,StrictCheckAt 16 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 31 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 16 31) 16 31:=by decide +kernel
  exact strictAtFast_sound (row 16 31) 16 31 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
