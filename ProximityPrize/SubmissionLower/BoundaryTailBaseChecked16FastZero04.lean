import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked16FastZero03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr16p48:∀ i ∈ List.range 1,ZeroCheckAt 16 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 48:=by decide +kernel
  exact zeroAtFast_sound 16 48 hfast

theorem zr16p49:∀ i ∈ List.range 1,ZeroCheckAt 16 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 49:=by decide +kernel
  exact zeroAtFast_sound 16 49 hfast

theorem zr16p50:∀ i ∈ List.range 1,ZeroCheckAt 16 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 50:=by decide +kernel
  exact zeroAtFast_sound 16 50 hfast

theorem zr16p51:∀ i ∈ List.range 1,ZeroCheckAt 16 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 51:=by decide +kernel
  exact zeroAtFast_sound 16 51 hfast

theorem zr16p52:∀ i ∈ List.range 1,ZeroCheckAt 16 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 52:=by decide +kernel
  exact zeroAtFast_sound 16 52 hfast

theorem zr16p53:∀ i ∈ List.range 1,ZeroCheckAt 16 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 53:=by decide +kernel
  exact zeroAtFast_sound 16 53 hfast

theorem zr16p54:∀ i ∈ List.range 1,ZeroCheckAt 16 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 54:=by decide +kernel
  exact zeroAtFast_sound 16 54 hfast

theorem zr16p55:∀ i ∈ List.range 1,ZeroCheckAt 16 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 55:=by decide +kernel
  exact zeroAtFast_sound 16 55 hfast

theorem zr16p56:∀ i ∈ List.range 1,ZeroCheckAt 16 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 56:=by decide +kernel
  exact zeroAtFast_sound 16 56 hfast

theorem zr16p57:∀ i ∈ List.range 1,ZeroCheckAt 16 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 57:=by decide +kernel
  exact zeroAtFast_sound 16 57 hfast

theorem zr16p58:∀ i ∈ List.range 1,ZeroCheckAt 16 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 58:=by decide +kernel
  exact zeroAtFast_sound 16 58 hfast

theorem zr16p59:∀ i ∈ List.range 1,ZeroCheckAt 16 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 59:=by decide +kernel
  exact zeroAtFast_sound 16 59 hfast

theorem zr16p60:∀ i ∈ List.range 1,ZeroCheckAt 16 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 60:=by decide +kernel
  exact zeroAtFast_sound 16 60 hfast

theorem zr16p61:∀ i ∈ List.range 1,ZeroCheckAt 16 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 61:=by decide +kernel
  exact zeroAtFast_sound 16 61 hfast

theorem zr16p62:∀ i ∈ List.range 1,ZeroCheckAt 16 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 62:=by decide +kernel
  exact zeroAtFast_sound 16 62 hfast

theorem zr16p63:∀ i ∈ List.range 1,ZeroCheckAt 16 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 63:=by decide +kernel
  exact zeroAtFast_sound 16 63 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
