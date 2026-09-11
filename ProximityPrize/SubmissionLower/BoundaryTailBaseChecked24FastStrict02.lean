import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked24FastStrict01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr24p16:∀ i ∈ List.range 1,StrictCheckAt 24 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 16 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 16) 24 16:=by decide +kernel
  exact strictAtFast_sound (row 24 16) 24 16 hvalid hfast

theorem sr24p17:∀ i ∈ List.range 1,StrictCheckAt 24 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 17 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 17) 24 17:=by decide +kernel
  exact strictAtFast_sound (row 24 17) 24 17 hvalid hfast

theorem sr24p18:∀ i ∈ List.range 1,StrictCheckAt 24 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 18 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 18) 24 18:=by decide +kernel
  exact strictAtFast_sound (row 24 18) 24 18 hvalid hfast

theorem sr24p19:∀ i ∈ List.range 1,StrictCheckAt 24 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 19 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 19) 24 19:=by decide +kernel
  exact strictAtFast_sound (row 24 19) 24 19 hvalid hfast

theorem sr24p20:∀ i ∈ List.range 1,StrictCheckAt 24 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 20 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 20) 24 20:=by decide +kernel
  exact strictAtFast_sound (row 24 20) 24 20 hvalid hfast

theorem sr24p21:∀ i ∈ List.range 1,StrictCheckAt 24 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 21 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 21) 24 21:=by decide +kernel
  exact strictAtFast_sound (row 24 21) 24 21 hvalid hfast

theorem sr24p22:∀ i ∈ List.range 1,StrictCheckAt 24 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 22 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 22) 24 22:=by decide +kernel
  exact strictAtFast_sound (row 24 22) 24 22 hvalid hfast

theorem sr24p23:∀ i ∈ List.range 1,StrictCheckAt 24 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 23 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 23) 24 23:=by decide +kernel
  exact strictAtFast_sound (row 24 23) 24 23 hvalid hfast

theorem sr24p24:∀ i ∈ List.range 1,StrictCheckAt 24 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 24 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 24) 24 24:=by decide +kernel
  exact strictAtFast_sound (row 24 24) 24 24 hvalid hfast

theorem sr24p25:∀ i ∈ List.range 1,StrictCheckAt 24 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 25 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 25) 24 25:=by decide +kernel
  exact strictAtFast_sound (row 24 25) 24 25 hvalid hfast

theorem sr24p26:∀ i ∈ List.range 1,StrictCheckAt 24 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 26 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 26) 24 26:=by decide +kernel
  exact strictAtFast_sound (row 24 26) 24 26 hvalid hfast

theorem sr24p27:∀ i ∈ List.range 1,StrictCheckAt 24 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 27 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 27) 24 27:=by decide +kernel
  exact strictAtFast_sound (row 24 27) 24 27 hvalid hfast

theorem sr24p28:∀ i ∈ List.range 1,StrictCheckAt 24 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 28 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 28) 24 28:=by decide +kernel
  exact strictAtFast_sound (row 24 28) 24 28 hvalid hfast

theorem sr24p29:∀ i ∈ List.range 1,StrictCheckAt 24 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 29 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 29) 24 29:=by decide +kernel
  exact strictAtFast_sound (row 24 29) 24 29 hvalid hfast

theorem sr24p30:∀ i ∈ List.range 1,StrictCheckAt 24 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 30 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 30) 24 30:=by decide +kernel
  exact strictAtFast_sound (row 24 30) 24 30 hvalid hfast

theorem sr24p31:∀ i ∈ List.range 1,StrictCheckAt 24 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 31 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 24 31) 24 31:=by decide +kernel
  exact strictAtFast_sound (row 24 31) 24 31 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
