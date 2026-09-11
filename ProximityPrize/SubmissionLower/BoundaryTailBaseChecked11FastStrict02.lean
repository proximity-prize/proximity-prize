import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked11FastStrict01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr11p16:∀ i ∈ List.range 1,StrictCheckAt 11 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 16 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 16) 11 16:=by decide +kernel
  exact strictAtFast_sound (row 11 16) 11 16 hvalid hfast

theorem sr11p17:∀ i ∈ List.range 1,StrictCheckAt 11 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 17 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 17) 11 17:=by decide +kernel
  exact strictAtFast_sound (row 11 17) 11 17 hvalid hfast

theorem sr11p18:∀ i ∈ List.range 1,StrictCheckAt 11 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 18 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 18) 11 18:=by decide +kernel
  exact strictAtFast_sound (row 11 18) 11 18 hvalid hfast

theorem sr11p19:∀ i ∈ List.range 1,StrictCheckAt 11 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 19 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 19) 11 19:=by decide +kernel
  exact strictAtFast_sound (row 11 19) 11 19 hvalid hfast

theorem sr11p20:∀ i ∈ List.range 1,StrictCheckAt 11 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 20 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 20) 11 20:=by decide +kernel
  exact strictAtFast_sound (row 11 20) 11 20 hvalid hfast

theorem sr11p21:∀ i ∈ List.range 1,StrictCheckAt 11 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 21 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 21) 11 21:=by decide +kernel
  exact strictAtFast_sound (row 11 21) 11 21 hvalid hfast

theorem sr11p22:∀ i ∈ List.range 1,StrictCheckAt 11 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 22 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 22) 11 22:=by decide +kernel
  exact strictAtFast_sound (row 11 22) 11 22 hvalid hfast

theorem sr11p23:∀ i ∈ List.range 1,StrictCheckAt 11 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 23 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 23) 11 23:=by decide +kernel
  exact strictAtFast_sound (row 11 23) 11 23 hvalid hfast

theorem sr11p24:∀ i ∈ List.range 1,StrictCheckAt 11 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 24 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 24) 11 24:=by decide +kernel
  exact strictAtFast_sound (row 11 24) 11 24 hvalid hfast

theorem sr11p25:∀ i ∈ List.range 1,StrictCheckAt 11 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 25 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 25) 11 25:=by decide +kernel
  exact strictAtFast_sound (row 11 25) 11 25 hvalid hfast

theorem sr11p26:∀ i ∈ List.range 1,StrictCheckAt 11 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 26 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 26) 11 26:=by decide +kernel
  exact strictAtFast_sound (row 11 26) 11 26 hvalid hfast

theorem sr11p27:∀ i ∈ List.range 1,StrictCheckAt 11 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 27 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 27) 11 27:=by decide +kernel
  exact strictAtFast_sound (row 11 27) 11 27 hvalid hfast

theorem sr11p28:∀ i ∈ List.range 1,StrictCheckAt 11 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 28 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 28) 11 28:=by decide +kernel
  exact strictAtFast_sound (row 11 28) 11 28 hvalid hfast

theorem sr11p29:∀ i ∈ List.range 1,StrictCheckAt 11 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 29 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 29) 11 29:=by decide +kernel
  exact strictAtFast_sound (row 11 29) 11 29 hvalid hfast

theorem sr11p30:∀ i ∈ List.range 1,StrictCheckAt 11 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 30 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 30) 11 30:=by decide +kernel
  exact strictAtFast_sound (row 11 30) 11 30 hvalid hfast

theorem sr11p31:∀ i ∈ List.range 1,StrictCheckAt 11 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 31 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 31) 11 31:=by decide +kernel
  exact strictAtFast_sound (row 11 31) 11 31 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
