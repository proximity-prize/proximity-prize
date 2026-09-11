import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked31FastStrict01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr31p16:∀ i ∈ List.range 1,StrictCheckAt 31 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 16 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 16) 31 16:=by decide +kernel
  exact strictAtFast_sound (row 31 16) 31 16 hvalid hfast

theorem sr31p17:∀ i ∈ List.range 1,StrictCheckAt 31 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 17 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 17) 31 17:=by decide +kernel
  exact strictAtFast_sound (row 31 17) 31 17 hvalid hfast

theorem sr31p18:∀ i ∈ List.range 1,StrictCheckAt 31 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 18 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 18) 31 18:=by decide +kernel
  exact strictAtFast_sound (row 31 18) 31 18 hvalid hfast

theorem sr31p19:∀ i ∈ List.range 1,StrictCheckAt 31 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 19 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 19) 31 19:=by decide +kernel
  exact strictAtFast_sound (row 31 19) 31 19 hvalid hfast

theorem sr31p20:∀ i ∈ List.range 1,StrictCheckAt 31 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 20 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 20) 31 20:=by decide +kernel
  exact strictAtFast_sound (row 31 20) 31 20 hvalid hfast

theorem sr31p21:∀ i ∈ List.range 1,StrictCheckAt 31 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 21 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 21) 31 21:=by decide +kernel
  exact strictAtFast_sound (row 31 21) 31 21 hvalid hfast

theorem sr31p22:∀ i ∈ List.range 1,StrictCheckAt 31 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 22 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 22) 31 22:=by decide +kernel
  exact strictAtFast_sound (row 31 22) 31 22 hvalid hfast

theorem sr31p23:∀ i ∈ List.range 1,StrictCheckAt 31 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 23 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 23) 31 23:=by decide +kernel
  exact strictAtFast_sound (row 31 23) 31 23 hvalid hfast

theorem sr31p24:∀ i ∈ List.range 1,StrictCheckAt 31 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 24 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 24) 31 24:=by decide +kernel
  exact strictAtFast_sound (row 31 24) 31 24 hvalid hfast

theorem sr31p25:∀ i ∈ List.range 1,StrictCheckAt 31 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 25 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 25) 31 25:=by decide +kernel
  exact strictAtFast_sound (row 31 25) 31 25 hvalid hfast

theorem sr31p26:∀ i ∈ List.range 1,StrictCheckAt 31 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 26 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 26) 31 26:=by decide +kernel
  exact strictAtFast_sound (row 31 26) 31 26 hvalid hfast

theorem sr31p27:∀ i ∈ List.range 1,StrictCheckAt 31 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 27 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 27) 31 27:=by decide +kernel
  exact strictAtFast_sound (row 31 27) 31 27 hvalid hfast

theorem sr31p28:∀ i ∈ List.range 1,StrictCheckAt 31 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 28 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 28) 31 28:=by decide +kernel
  exact strictAtFast_sound (row 31 28) 31 28 hvalid hfast

theorem sr31p29:∀ i ∈ List.range 1,StrictCheckAt 31 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 29 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 29) 31 29:=by decide +kernel
  exact strictAtFast_sound (row 31 29) 31 29 hvalid hfast

theorem sr31p30:∀ i ∈ List.range 1,StrictCheckAt 31 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 30 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 30) 31 30:=by decide +kernel
  exact strictAtFast_sound (row 31 30) 31 30 hvalid hfast

theorem sr31p31:∀ i ∈ List.range 1,StrictCheckAt 31 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 31 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 31 31) 31 31:=by decide +kernel
  exact strictAtFast_sound (row 31 31) 31 31 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
