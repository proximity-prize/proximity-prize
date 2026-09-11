import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10FastZero06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr10p96:∀ i ∈ List.range 1,ZeroCheckAt 10 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 96:=by decide +kernel
  exact zeroAtFast_sound 10 96 hfast

theorem zr10p97:∀ i ∈ List.range 1,ZeroCheckAt 10 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 97:=by decide +kernel
  exact zeroAtFast_sound 10 97 hfast

theorem zr10p98:∀ i ∈ List.range 1,ZeroCheckAt 10 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 98:=by decide +kernel
  exact zeroAtFast_sound 10 98 hfast

theorem zr10p99:∀ i ∈ List.range 1,ZeroCheckAt 10 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 99:=by decide +kernel
  exact zeroAtFast_sound 10 99 hfast

theorem zr10p100:∀ i ∈ List.range 1,ZeroCheckAt 10 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 100:=by decide +kernel
  exact zeroAtFast_sound 10 100 hfast

theorem zr10p101:∀ i ∈ List.range 1,ZeroCheckAt 10 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 101:=by decide +kernel
  exact zeroAtFast_sound 10 101 hfast

theorem zr10p102:∀ i ∈ List.range 1,ZeroCheckAt 10 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 102:=by decide +kernel
  exact zeroAtFast_sound 10 102 hfast

theorem zr10p103:∀ i ∈ List.range 1,ZeroCheckAt 10 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 103:=by decide +kernel
  exact zeroAtFast_sound 10 103 hfast

theorem zr10p104:∀ i ∈ List.range 1,ZeroCheckAt 10 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 104:=by decide +kernel
  exact zeroAtFast_sound 10 104 hfast

theorem zr10p105:∀ i ∈ List.range 1,ZeroCheckAt 10 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 105:=by decide +kernel
  exact zeroAtFast_sound 10 105 hfast

theorem zr10p106:∀ i ∈ List.range 1,ZeroCheckAt 10 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 106:=by decide +kernel
  exact zeroAtFast_sound 10 106 hfast

theorem zr10p107:∀ i ∈ List.range 1,ZeroCheckAt 10 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 107:=by decide +kernel
  exact zeroAtFast_sound 10 107 hfast

theorem zr10p108:∀ i ∈ List.range 1,ZeroCheckAt 10 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 108:=by decide +kernel
  exact zeroAtFast_sound 10 108 hfast

theorem zr10p109:∀ i ∈ List.range 1,ZeroCheckAt 10 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 109:=by decide +kernel
  exact zeroAtFast_sound 10 109 hfast

theorem zr10p110:∀ i ∈ List.range 1,ZeroCheckAt 10 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 110:=by decide +kernel
  exact zeroAtFast_sound 10 110 hfast

theorem zr10p111:∀ i ∈ List.range 1,ZeroCheckAt 10 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 111:=by decide +kernel
  exact zeroAtFast_sound 10 111 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
