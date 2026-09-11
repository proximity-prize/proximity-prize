import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked30FastZero01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr30p16:∀ i ∈ List.range 1,ZeroCheckAt 30 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 16:=by decide +kernel
  exact zeroAtFast_sound 30 16 hfast

theorem zr30p17:∀ i ∈ List.range 1,ZeroCheckAt 30 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 17:=by decide +kernel
  exact zeroAtFast_sound 30 17 hfast

theorem zr30p18:∀ i ∈ List.range 1,ZeroCheckAt 30 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 18:=by decide +kernel
  exact zeroAtFast_sound 30 18 hfast

theorem zr30p19:∀ i ∈ List.range 1,ZeroCheckAt 30 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 19:=by decide +kernel
  exact zeroAtFast_sound 30 19 hfast

theorem zr30p20:∀ i ∈ List.range 1,ZeroCheckAt 30 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 20:=by decide +kernel
  exact zeroAtFast_sound 30 20 hfast

theorem zr30p21:∀ i ∈ List.range 1,ZeroCheckAt 30 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 21:=by decide +kernel
  exact zeroAtFast_sound 30 21 hfast

theorem zr30p22:∀ i ∈ List.range 1,ZeroCheckAt 30 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 22:=by decide +kernel
  exact zeroAtFast_sound 30 22 hfast

theorem zr30p23:∀ i ∈ List.range 1,ZeroCheckAt 30 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 23:=by decide +kernel
  exact zeroAtFast_sound 30 23 hfast

theorem zr30p24:∀ i ∈ List.range 1,ZeroCheckAt 30 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 24:=by decide +kernel
  exact zeroAtFast_sound 30 24 hfast

theorem zr30p25:∀ i ∈ List.range 1,ZeroCheckAt 30 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 25:=by decide +kernel
  exact zeroAtFast_sound 30 25 hfast

theorem zr30p26:∀ i ∈ List.range 1,ZeroCheckAt 30 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 26:=by decide +kernel
  exact zeroAtFast_sound 30 26 hfast

theorem zr30p27:∀ i ∈ List.range 1,ZeroCheckAt 30 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 27:=by decide +kernel
  exact zeroAtFast_sound 30 27 hfast

theorem zr30p28:∀ i ∈ List.range 1,ZeroCheckAt 30 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 28:=by decide +kernel
  exact zeroAtFast_sound 30 28 hfast

theorem zr30p29:∀ i ∈ List.range 1,ZeroCheckAt 30 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 29:=by decide +kernel
  exact zeroAtFast_sound 30 29 hfast

theorem zr30p30:∀ i ∈ List.range 1,ZeroCheckAt 30 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 30:=by decide +kernel
  exact zeroAtFast_sound 30 30 hfast

theorem zr30p31:∀ i ∈ List.range 1,ZeroCheckAt 30 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 31:=by decide +kernel
  exact zeroAtFast_sound 30 31 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
