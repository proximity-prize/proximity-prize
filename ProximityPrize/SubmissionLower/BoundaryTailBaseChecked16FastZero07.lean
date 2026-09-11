import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked16FastZero06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr16p96:∀ i ∈ List.range 1,ZeroCheckAt 16 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 96:=by decide +kernel
  exact zeroAtFast_sound 16 96 hfast

theorem zr16p97:∀ i ∈ List.range 1,ZeroCheckAt 16 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 97:=by decide +kernel
  exact zeroAtFast_sound 16 97 hfast

theorem zr16p98:∀ i ∈ List.range 1,ZeroCheckAt 16 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 98:=by decide +kernel
  exact zeroAtFast_sound 16 98 hfast

theorem zr16p99:∀ i ∈ List.range 1,ZeroCheckAt 16 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 99:=by decide +kernel
  exact zeroAtFast_sound 16 99 hfast

theorem zr16p100:∀ i ∈ List.range 1,ZeroCheckAt 16 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 100:=by decide +kernel
  exact zeroAtFast_sound 16 100 hfast

theorem zr16p101:∀ i ∈ List.range 1,ZeroCheckAt 16 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 101:=by decide +kernel
  exact zeroAtFast_sound 16 101 hfast

theorem zr16p102:∀ i ∈ List.range 1,ZeroCheckAt 16 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 102:=by decide +kernel
  exact zeroAtFast_sound 16 102 hfast

theorem zr16p103:∀ i ∈ List.range 1,ZeroCheckAt 16 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 103:=by decide +kernel
  exact zeroAtFast_sound 16 103 hfast

theorem zr16p104:∀ i ∈ List.range 1,ZeroCheckAt 16 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 104:=by decide +kernel
  exact zeroAtFast_sound 16 104 hfast

theorem zr16p105:∀ i ∈ List.range 1,ZeroCheckAt 16 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 105:=by decide +kernel
  exact zeroAtFast_sound 16 105 hfast

theorem zr16p106:∀ i ∈ List.range 1,ZeroCheckAt 16 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 106:=by decide +kernel
  exact zeroAtFast_sound 16 106 hfast

theorem zr16p107:∀ i ∈ List.range 1,ZeroCheckAt 16 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 107:=by decide +kernel
  exact zeroAtFast_sound 16 107 hfast

theorem zr16p108:∀ i ∈ List.range 1,ZeroCheckAt 16 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 108:=by decide +kernel
  exact zeroAtFast_sound 16 108 hfast

theorem zr16p109:∀ i ∈ List.range 1,ZeroCheckAt 16 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 109:=by decide +kernel
  exact zeroAtFast_sound 16 109 hfast

theorem zr16p110:∀ i ∈ List.range 1,ZeroCheckAt 16 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 110:=by decide +kernel
  exact zeroAtFast_sound 16 110 hfast

theorem zr16p111:∀ i ∈ List.range 1,ZeroCheckAt 16 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 111:=by decide +kernel
  exact zeroAtFast_sound 16 111 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
