import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked31FastZero01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr31p16:∀ i ∈ List.range 1,ZeroCheckAt 31 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 16:=by decide +kernel
  exact zeroAtFast_sound 31 16 hfast

theorem zr31p17:∀ i ∈ List.range 1,ZeroCheckAt 31 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 17:=by decide +kernel
  exact zeroAtFast_sound 31 17 hfast

theorem zr31p18:∀ i ∈ List.range 1,ZeroCheckAt 31 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 18:=by decide +kernel
  exact zeroAtFast_sound 31 18 hfast

theorem zr31p19:∀ i ∈ List.range 1,ZeroCheckAt 31 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 19:=by decide +kernel
  exact zeroAtFast_sound 31 19 hfast

theorem zr31p20:∀ i ∈ List.range 1,ZeroCheckAt 31 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 20:=by decide +kernel
  exact zeroAtFast_sound 31 20 hfast

theorem zr31p21:∀ i ∈ List.range 1,ZeroCheckAt 31 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 21:=by decide +kernel
  exact zeroAtFast_sound 31 21 hfast

theorem zr31p22:∀ i ∈ List.range 1,ZeroCheckAt 31 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 22:=by decide +kernel
  exact zeroAtFast_sound 31 22 hfast

theorem zr31p23:∀ i ∈ List.range 1,ZeroCheckAt 31 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 23:=by decide +kernel
  exact zeroAtFast_sound 31 23 hfast

theorem zr31p24:∀ i ∈ List.range 1,ZeroCheckAt 31 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 24:=by decide +kernel
  exact zeroAtFast_sound 31 24 hfast

theorem zr31p25:∀ i ∈ List.range 1,ZeroCheckAt 31 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 25:=by decide +kernel
  exact zeroAtFast_sound 31 25 hfast

theorem zr31p26:∀ i ∈ List.range 1,ZeroCheckAt 31 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 26:=by decide +kernel
  exact zeroAtFast_sound 31 26 hfast

theorem zr31p27:∀ i ∈ List.range 1,ZeroCheckAt 31 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 27:=by decide +kernel
  exact zeroAtFast_sound 31 27 hfast

theorem zr31p28:∀ i ∈ List.range 1,ZeroCheckAt 31 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 28:=by decide +kernel
  exact zeroAtFast_sound 31 28 hfast

theorem zr31p29:∀ i ∈ List.range 1,ZeroCheckAt 31 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 29:=by decide +kernel
  exact zeroAtFast_sound 31 29 hfast

theorem zr31p30:∀ i ∈ List.range 1,ZeroCheckAt 31 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 30:=by decide +kernel
  exact zeroAtFast_sound 31 30 hfast

theorem zr31p31:∀ i ∈ List.range 1,ZeroCheckAt 31 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 31:=by decide +kernel
  exact zeroAtFast_sound 31 31 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
