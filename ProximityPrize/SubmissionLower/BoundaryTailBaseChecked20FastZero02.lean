import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked20FastZero01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr20p16:∀ i ∈ List.range 1,ZeroCheckAt 20 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 16:=by decide +kernel
  exact zeroAtFast_sound 20 16 hfast

theorem zr20p17:∀ i ∈ List.range 1,ZeroCheckAt 20 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 17:=by decide +kernel
  exact zeroAtFast_sound 20 17 hfast

theorem zr20p18:∀ i ∈ List.range 1,ZeroCheckAt 20 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 18:=by decide +kernel
  exact zeroAtFast_sound 20 18 hfast

theorem zr20p19:∀ i ∈ List.range 1,ZeroCheckAt 20 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 19:=by decide +kernel
  exact zeroAtFast_sound 20 19 hfast

theorem zr20p20:∀ i ∈ List.range 1,ZeroCheckAt 20 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 20:=by decide +kernel
  exact zeroAtFast_sound 20 20 hfast

theorem zr20p21:∀ i ∈ List.range 1,ZeroCheckAt 20 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 21:=by decide +kernel
  exact zeroAtFast_sound 20 21 hfast

theorem zr20p22:∀ i ∈ List.range 1,ZeroCheckAt 20 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 22:=by decide +kernel
  exact zeroAtFast_sound 20 22 hfast

theorem zr20p23:∀ i ∈ List.range 1,ZeroCheckAt 20 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 23:=by decide +kernel
  exact zeroAtFast_sound 20 23 hfast

theorem zr20p24:∀ i ∈ List.range 1,ZeroCheckAt 20 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 24:=by decide +kernel
  exact zeroAtFast_sound 20 24 hfast

theorem zr20p25:∀ i ∈ List.range 1,ZeroCheckAt 20 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 25:=by decide +kernel
  exact zeroAtFast_sound 20 25 hfast

theorem zr20p26:∀ i ∈ List.range 1,ZeroCheckAt 20 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 26:=by decide +kernel
  exact zeroAtFast_sound 20 26 hfast

theorem zr20p27:∀ i ∈ List.range 1,ZeroCheckAt 20 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 27:=by decide +kernel
  exact zeroAtFast_sound 20 27 hfast

theorem zr20p28:∀ i ∈ List.range 1,ZeroCheckAt 20 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 28:=by decide +kernel
  exact zeroAtFast_sound 20 28 hfast

theorem zr20p29:∀ i ∈ List.range 1,ZeroCheckAt 20 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 29:=by decide +kernel
  exact zeroAtFast_sound 20 29 hfast

theorem zr20p30:∀ i ∈ List.range 1,ZeroCheckAt 20 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 30:=by decide +kernel
  exact zeroAtFast_sound 20 30 hfast

theorem zr20p31:∀ i ∈ List.range 1,ZeroCheckAt 20 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 31:=by decide +kernel
  exact zeroAtFast_sound 20 31 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
