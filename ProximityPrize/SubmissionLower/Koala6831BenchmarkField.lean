import Mathlib.FieldTheory.Finite.Basic
import ProximityPrize.SubmissionLower.LowerFoundation

namespace ProximityPrize.SubmissionLower.Koala6831BenchmarkField

open ProximityPrize.Benchmark

abbrev prime : ℕ := 2130706433

theorem characteristic : CharP IRSProfile.Field prime :=
  RCN128.challenge_field_characteristic6600

private def baseFrobenius : IRSProfile.Field →ₐ[_root_.KoalaBear.Field] IRSProfile.Field :=
  FiniteField.frobeniusAlgHom _root_.KoalaBear.Field IRSProfile.Field

private noncomputable def baseFrobeniusEquiv : IRSProfile.Field ≃+* IRSProfile.Field :=
  RingEquiv.ofBijective baseFrobenius.toRingHom
    ⟨baseFrobenius.injective, Finite.surjective_of_injective baseFrobenius.injective⟩

private theorem exists_frobenius : ∃ σ : IRSProfile.Field ≃+* IRSProfile.Field,
    (∀ value : IRSProfile.Field, σ value = value ^ prime) ∧
    (∀ i : IRSProfile.Index, σ (IRSProfile.domain i) = IRSProfile.domain i) := by
  refine ⟨baseFrobeniusEquiv, ?_, ?_⟩
  · intro value
    have hcard : Fintype.card _root_.KoalaBear.Field = prime := ZMod.card prime
    rw [← hcard]
    change baseFrobenius value = _
    exact congrFun (FiniteField.coe_frobeniusAlgHom _root_.KoalaBear.Field IRSProfile.Field) value
  · intro i
    change baseFrobenius (algebraMap _root_.KoalaBear.Field IRSProfile.Field
      (IRSProfile.baseNttDomain.node i)) = _
    exact baseFrobenius.commutes (IRSProfile.baseNttDomain.node i)

noncomputable def frobenius : IRSProfile.Field ≃+* IRSProfile.Field :=
  Classical.choose exists_frobenius

theorem frobenius_apply (value : IRSProfile.Field) : frobenius value = value ^ prime :=
  (Classical.choose_spec exists_frobenius).1 value

@[simp] theorem domain_fixed (i : IRSProfile.Index) :
    frobenius (IRSProfile.domain i) = IRSProfile.domain i :=
  (Classical.choose_spec exists_frobenius).2 i

end ProximityPrize.SubmissionLower.Koala6831BenchmarkField
