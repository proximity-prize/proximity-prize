import ProximityPrize.SubmissionLower.Koala6831IntrinsicPowers
import Mathlib.FieldTheory.PurelyInseparable.Exponent


namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]

theorem isSeparable_of_adjoin_powerField_eq_top (p : ℕ) [ExpChar E p]
    (hgen : IntermediateField.adjoin K (powerField E p : Set E) = ⊤) :
    Algebra.IsSeparable K E := by
  let S := separableClosure K E
  letI : FiniteDimensional S E := FiniteDimensional.right K S E
  letI : ExpChar S p := (algebraMap S E).expChar (algebraMap S E).injective p
  let e := IsPurelyInseparable.exponent S E
  have hexp (x : E) : x ^ p ^ e ∈ S := by
    obtain ⟨y, hy⟩ := IsPurelyInseparable.exponent_def' S p x
    rw [← hy]
    exact y.property
  apply (separableClosure.eq_top_iff K E).mp
  by_cases he : e = 0
  · apply top_unique
    intro x _
    have hx := hexp x
    rwa [he, pow_zero, pow_one] at hx
  let C : IntermediateField K E :=
    { S.toSubfield.comap (iterateFrobenius E p (e - 1)) with
      algebraMap_mem' := fun a => by
        change (algebraMap K E a) ^ p ^ (e - 1) ∈ S
        have hm : algebraMap K E a ∈ S := S.algebraMap_mem a
        exact S.toSubfield.toSubring.pow_mem hm (p ^ (e - 1)) }
  have hCsubset : (powerField E p : Set E) ⊆ C := by
    intro x hx
    obtain ⟨y, rfl⟩ := mem_powerField_iff.mp hx
    change (y ^ p) ^ p ^ (e - 1) ∈ S
    rw [← pow_mul, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero he)]
    exact hexp y
  have htop : C = ⊤ := by
    apply top_unique
    simpa only [hgen] using (IntermediateField.adjoin_le_iff.mpr hCsubset)
  obtain ⟨x, hx⟩ := IsPurelyInseparable.exponent_min' (K := S) (L := E) p
    (show e - 1 < IsPurelyInseparable.exponent S E by omega)
  have hxC : x ∈ C := htop ▸ (IntermediateField.mem_top : x ∈ (⊤ : IntermediateField K E))
  change x ^ p ^ (e - 1) ∈ S at hxC
  exact (hx ⟨⟨_, hxC⟩, rfl⟩).elim

theorem isSeparable_of_powerField_single_generator (p : ℕ) [ExpChar E p] (x : K)
    (hgen : IntermediateField.adjoin (powerField E p) ({algebraMap K E x} : Set E) = ⊤) :
    Algebra.IsSeparable K E := by
  let S := powerField E p
  let C := IntermediateField.adjoin K (S : Set E)
  let D : IntermediateField S E :=
    { C.toSubfield with
      algebraMap_mem' := fun a => by
        change (a : E) ∈ C
        exact IntermediateField.subset_adjoin K (S : Set E) a.property }
  have hx : algebraMap K E x ∈ D := C.algebraMap_mem x
  have hd : IntermediateField.adjoin S ({algebraMap K E x} : Set E) ≤ D :=
    IntermediateField.adjoin_simple_le_iff.mpr hx
  rw [hgen] at hd
  apply isSeparable_of_adjoin_powerField_eq_top p
  apply top_unique
  intro a ha
  exact hd (show a ∈ (⊤ : IntermediateField S E) from IntermediateField.mem_top)

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
