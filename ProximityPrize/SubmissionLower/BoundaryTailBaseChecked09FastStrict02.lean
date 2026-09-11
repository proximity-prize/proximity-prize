import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked09FastStrict01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr9p16:∀ i ∈ List.range 1,StrictCheckAt 9 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 16 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 16) 9 16:=by decide +kernel
  exact strictAtFast_sound (row 9 16) 9 16 hvalid hfast

theorem sr9p17:∀ i ∈ List.range 1,StrictCheckAt 9 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 17 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 17) 9 17:=by decide +kernel
  exact strictAtFast_sound (row 9 17) 9 17 hvalid hfast

theorem sr9p18:∀ i ∈ List.range 1,StrictCheckAt 9 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 18 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 18) 9 18:=by decide +kernel
  exact strictAtFast_sound (row 9 18) 9 18 hvalid hfast

theorem sr9p19:∀ i ∈ List.range 1,StrictCheckAt 9 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 19 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 19) 9 19:=by decide +kernel
  exact strictAtFast_sound (row 9 19) 9 19 hvalid hfast

theorem sr9p20:∀ i ∈ List.range 1,StrictCheckAt 9 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 20 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 20) 9 20:=by decide +kernel
  exact strictAtFast_sound (row 9 20) 9 20 hvalid hfast

theorem sr9p21:∀ i ∈ List.range 1,StrictCheckAt 9 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 21 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 21) 9 21:=by decide +kernel
  exact strictAtFast_sound (row 9 21) 9 21 hvalid hfast

theorem sr9p22:∀ i ∈ List.range 1,StrictCheckAt 9 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 22 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 22) 9 22:=by decide +kernel
  exact strictAtFast_sound (row 9 22) 9 22 hvalid hfast

theorem sr9p23:∀ i ∈ List.range 1,StrictCheckAt 9 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 23 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 23) 9 23:=by decide +kernel
  exact strictAtFast_sound (row 9 23) 9 23 hvalid hfast

theorem sr9p24:∀ i ∈ List.range 1,StrictCheckAt 9 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 24 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 24) 9 24:=by decide +kernel
  exact strictAtFast_sound (row 9 24) 9 24 hvalid hfast

theorem sr9p25:∀ i ∈ List.range 1,StrictCheckAt 9 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 25 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 25) 9 25:=by decide +kernel
  exact strictAtFast_sound (row 9 25) 9 25 hvalid hfast

theorem sr9p26:∀ i ∈ List.range 1,StrictCheckAt 9 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 26 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 26) 9 26:=by decide +kernel
  exact strictAtFast_sound (row 9 26) 9 26 hvalid hfast

theorem sr9p27:∀ i ∈ List.range 1,StrictCheckAt 9 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 27 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 27) 9 27:=by decide +kernel
  exact strictAtFast_sound (row 9 27) 9 27 hvalid hfast

theorem sr9p28:∀ i ∈ List.range 1,StrictCheckAt 9 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 28 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 28) 9 28:=by decide +kernel
  exact strictAtFast_sound (row 9 28) 9 28 hvalid hfast

theorem sr9p29:∀ i ∈ List.range 1,StrictCheckAt 9 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 29 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 29) 9 29:=by decide +kernel
  exact strictAtFast_sound (row 9 29) 9 29 hvalid hfast

theorem sr9p30:∀ i ∈ List.range 1,StrictCheckAt 9 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 30 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 30) 9 30:=by decide +kernel
  exact strictAtFast_sound (row 9 30) 9 30 hvalid hfast

theorem sr9p31:∀ i ∈ List.range 1,StrictCheckAt 9 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 31 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 31) 9 31:=by decide +kernel
  exact strictAtFast_sound (row 9 31) 9 31 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
