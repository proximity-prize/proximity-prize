import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18FastZero01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr18p16:∀ i ∈ List.range 1,ZeroCheckAt 18 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 16:=by decide +kernel
  exact zeroAtFast_sound 18 16 hfast

theorem zr18p17:∀ i ∈ List.range 1,ZeroCheckAt 18 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 17:=by decide +kernel
  exact zeroAtFast_sound 18 17 hfast

theorem zr18p18:∀ i ∈ List.range 1,ZeroCheckAt 18 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 18:=by decide +kernel
  exact zeroAtFast_sound 18 18 hfast

theorem zr18p19:∀ i ∈ List.range 1,ZeroCheckAt 18 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 19:=by decide +kernel
  exact zeroAtFast_sound 18 19 hfast

theorem zr18p20:∀ i ∈ List.range 1,ZeroCheckAt 18 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 20:=by decide +kernel
  exact zeroAtFast_sound 18 20 hfast

theorem zr18p21:∀ i ∈ List.range 1,ZeroCheckAt 18 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 21:=by decide +kernel
  exact zeroAtFast_sound 18 21 hfast

theorem zr18p22:∀ i ∈ List.range 1,ZeroCheckAt 18 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 22:=by decide +kernel
  exact zeroAtFast_sound 18 22 hfast

theorem zr18p23:∀ i ∈ List.range 1,ZeroCheckAt 18 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 23:=by decide +kernel
  exact zeroAtFast_sound 18 23 hfast

theorem zr18p24:∀ i ∈ List.range 1,ZeroCheckAt 18 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 24:=by decide +kernel
  exact zeroAtFast_sound 18 24 hfast

theorem zr18p25:∀ i ∈ List.range 1,ZeroCheckAt 18 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 25:=by decide +kernel
  exact zeroAtFast_sound 18 25 hfast

theorem zr18p26:∀ i ∈ List.range 1,ZeroCheckAt 18 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 26:=by decide +kernel
  exact zeroAtFast_sound 18 26 hfast

theorem zr18p27:∀ i ∈ List.range 1,ZeroCheckAt 18 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 27:=by decide +kernel
  exact zeroAtFast_sound 18 27 hfast

theorem zr18p28:∀ i ∈ List.range 1,ZeroCheckAt 18 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 28:=by decide +kernel
  exact zeroAtFast_sound 18 28 hfast

theorem zr18p29:∀ i ∈ List.range 1,ZeroCheckAt 18 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 29:=by decide +kernel
  exact zeroAtFast_sound 18 29 hfast

theorem zr18p30:∀ i ∈ List.range 1,ZeroCheckAt 18 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 30:=by decide +kernel
  exact zeroAtFast_sound 18 30 hfast

theorem zr18p31:∀ i ∈ List.range 1,ZeroCheckAt 18 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 31:=by decide +kernel
  exact zeroAtFast_sound 18 31 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
