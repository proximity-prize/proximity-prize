/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense

/-!
Permitted flat proof port of Mathlib.Topology.Algebra.Group.ClosedSubgroup.
Model label: gpt-5.
Original Mathlib revision: 905b95818eb32af7874a58b427f50c1711a5e96c.
Original source SHA256: 5a71602286bf388aefa13a33d538d79e286113e2e4cf6b5f8ff3a58f5b90d0ce.
Original copyright and author notices are retained above.
Modifications: module/public visibility packaging is removed; imports
are replaced by the trusted target and the necessary flat proof ports.
All mathematical declarations and proof bodies are retained, except
any explicitly documented ordinary-term expansion below.
The full Apache 2.0 license is in LocalMathlibPortLicense.lean.
-/

/-! .














 -/

section ProximityFlatProofPort

section

universe u v

/-- . -/
@[ext]
structure ClosedSubgroup (G : Type u) [Group G] [TopologicalSpace G] extends Subgroup G where
  isClosed' : IsClosed carrier

/-- . -/
@[ext]
structure ClosedAddSubgroup (G : Type u) [AddGroup G] [TopologicalSpace G] extends
    AddSubgroup G where
  isClosed' : IsClosed carrier

attribute [to_additive] ClosedSubgroup

attribute [coe] ClosedSubgroup.toSubgroup ClosedAddSubgroup.toAddSubgroup

namespace ClosedSubgroup

variable (G : Type u) [Group G] [TopologicalSpace G]

variable {G} in
@[to_additive]
theorem toSubgroup_injective : Function.Injective
    (ClosedSubgroup.toSubgroup : ClosedSubgroup G → Subgroup G) :=
  fun A B h ↦ by
  ext
  rw [h]

@[to_additive]
instance : SetLike (ClosedSubgroup G) G where
  coe U := U.1
  coe_injective _ _ h := toSubgroup_injective <| SetLike.ext' h

@[to_additive] instance : PartialOrder (ClosedSubgroup G) := .ofSetLike (ClosedSubgroup G) G

@[to_additive]
instance : SubgroupClass (ClosedSubgroup G) G where
  mul_mem := Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

@[to_additive]
instance : Coe (ClosedSubgroup G) (Subgroup G) where
  coe := toSubgroup

@[to_additive]
instance instInfClosedSubgroup : Min (ClosedSubgroup G) :=
  ⟨fun U V ↦ ⟨U ⊓ V, U.isClosed'.inter V.isClosed'⟩⟩

@[to_additive]
instance instSemilatticeInfClosedSubgroup : SemilatticeInf (ClosedSubgroup G) :=
  SetLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ ↦ rfl

@[to_additive]
instance [CompactSpace G] (H : ClosedSubgroup G) : CompactSpace H :=
  isCompact_iff_compactSpace.mp (IsClosed.isCompact H.isClosed')

end ClosedSubgroup

open scoped Pointwise

namespace Subgroup

variable {G : Type u} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]

@[to_additive]
lemma normalCore_isClosed (H : Subgroup G) (h : IsClosed (H : Set G)) :
    IsClosed (H.normalCore : Set G) := by
  rw [normalCore_eq_iInf_comap_conj]
  push_cast
  apply isClosed_iInter
  intro g
  exact h.preimage (IsTopologicalGroup.continuous_conj g)

@[to_additive]
lemma isOpen_of_isClosed_of_finiteIndex (H : Subgroup G) [H.FiniteIndex]
    (h : IsClosed (H : Set G)) : IsOpen (H : Set G) := by
  rw [← QuotientGroup.t1Space_iff] at h
  rw [← QuotientGroup.discreteTopology_iff]
  infer_instance

end Subgroup

end
