import ProximityPrize.SubmissionLower.Koala6844VirtualShortInterpolant
import ProximityPrize.SubmissionLower.Koala6844VirtualShortSeedlessRank


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped BigOperators
open SecondJetLocal

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2500000

variable {K : Type*} [Field K]

def scaleContact (m : ℕ) (W : Target (K := K)) : Target (K := K) →ₗ[K] Target (K := K) :=
  ((Polynomial.modByMonicHom (Polynomial.X^m : Target (K := K))).restrictScalars K).comp
    (LinearMap.mulLeft K W)

theorem scaleContact_eq_of_shorter_remainder (m k : ℕ) (W P : Target (K := K))
    (hW : Polynomial.X^k ∣ W) :
    scaleContact m W (P %ₘ Polynomial.X^(m-k)) = scaleContact m W P := by
  have hP : (Polynomial.X : Target (K := K))^(m-k) ∣ P - P %ₘ Polynomial.X^(m-k) := by
    rw [Polynomial.modByMonic_eq_sub_mul_div]
    exact ⟨P /ₘ Polynomial.X^(m-k), by ring⟩
  have hprod := mul_dvd_mul hW hP
  rw [← pow_add] at hprod
  have hm : (Polynomial.X : Target (K := K))^m ∣ W * (P - P %ₘ Polynomial.X^(m-k)) :=
    (pow_dvd_pow Polynomial.X (by omega : m ≤ k+(m-k))).trans hprod
  have hz := (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow m)).mpr hm
  have hs : scaleContact m W (P - P %ₘ Polynomial.X^(m-k)) = 0 := hz
  rw [map_sub, sub_eq_zero] at hs
  exact hs.symm

private theorem finrank_sup_le_sum {V : Type*} [AddCommGroup V] [Module K V]
    {I : Type*} (indices : Finset I) (W : I → Submodule K V)
    (hW : ∀ i, FiniteDimensional K (W i)) :
    Module.finrank K (indices.sup W : Submodule K V) ≤ ∑ i ∈ indices, Module.finrank K (W i) := by
  classical
  letI : ∀ i, FiniteDimensional K (W i) := hW
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sup_insert, Finset.sum_insert hi]
    have hadd := Submodule.finrank_sup_add_finrank_inf_eq (W i) (s.sup W)
    omega

theorem rank_le_sum_of_pole_spans {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (T : (I → K) →ₗ[K] Target (K := K))
    (W : J → Submodule K (Target (K := K))) (hW : ∀ j, FiniteDimensional K (W j))
    (g : J → Target (K := K) →ₗ[K] Target (K := K))
    (hcolumn : ∀ i, T (Pi.single i 1) ∈ Finset.univ.sup fun j => (W j).map (g j))
    (b : J → ℕ) (hbound : ∀ j, Module.finrank K (W j) ≤ b j) :
    Module.finrank K T.range ≤ ∑ j, b j := by
  classical
  let V (j : J) := (W j).map (g j)
  letI : ∀ j, FiniteDimensional K (W j) := hW
  have hV : ∀ j, FiniteDimensional K (V j) := fun j => inferInstance
  letI : ∀ j, FiniteDimensional K (V j) := hV
  have hle : T.range ≤ Finset.univ.sup V := by
    rintro _ ⟨c,rfl⟩
    rw [← (Pi.basisFun K I).sum_repr c, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul, Pi.basisFun_apply]
    exact Submodule.smul_mem _ _ (hcolumn i)
  calc
    _ ≤ Module.finrank K (Finset.univ.sup V : Submodule K (Target (K := K))) :=
      Submodule.finrank_mono hle
    _ ≤ ∑ j, Module.finrank K (V j) := finrank_sup_le_sum Finset.univ V hV
    _ ≤ _ := Finset.sum_le_sum fun j _ => (Submodule.finrank_map_le _ _).trans (hbound j)

theorem scaleContact_injOn_remainders (m : ℕ) (W : Target (K := K))
    (hW : IsCoprime W (Polynomial.X^m)) :
    Set.InjOn (scaleContact m W)
      {P : Target (K := K) | P %ₘ Polynomial.X^m = P} := by
  intro P hP Q hQ heq
  have hZ : scaleContact m W (P-Q) = 0 := by rw [map_sub, heq, sub_self]
  have hH : (W*(P-Q)) %ₘ Polynomial.X^m = 0 := hZ
  have hdiv := (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow m)).mp hH
  have hdiff := hW.symm.dvd_of_dvd_mul_left hdiv
  have hz := (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow m)).mpr hdiff
  change P %ₘ Polynomial.X^m = P at hP
  change Q %ₘ Polynomial.X^m = Q at hQ
  rw [Polynomial.sub_modByMonic, hP, hQ, sub_eq_zero] at hz
  exact hz

theorem rank_le_scaledContact_rank {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (m : ℕ) (W : Target (K := K)) (f : V →ₗ[K] Target (K := K))
    (hW : IsCoprime W (Polynomial.X^m)) (htrunc : ∀ v, (f v) %ₘ Polynomial.X^m = f v) :
    Module.finrank K f.range ≤ Module.finrank K ((scaleContact m W).comp f).range := by
  let G := (scaleContact m W).comp f
  let g : f.range →ₗ[K] G.range :=
    ((scaleContact m W).comp f.range.subtype).codRestrict G.range (by
      intro x
      obtain ⟨v,hv⟩ := x.property
      exact ⟨v,congrArg (scaleContact m W) hv⟩)
  have hI : Function.Injective g := by
    intro x y heq
    apply Subtype.ext
    apply scaleContact_injOn_remainders m W hW
    · obtain ⟨v,hv⟩ := x.property
      rw [← hv]
      exact htrunc v
    · obtain ⟨v,hv⟩ := y.property
      rw [← hv]
      exact htrunc v
    · exact congrArg Subtype.val heq
  exact LinearMap.finrank_le_finrank_of_injective hI

end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort
