import ProximityPrize.SubmissionLower.Koala6844VirtualHighSpecialization
import Mathlib.Algebra.MvPolynomial.PDeriv


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Polynomial Koala6844Normalization
open scoped BigOperators Classical

noncomputable section

set_option autoImplicit false

variable {K E : Type} [Field K] [Field E]

def germSeedDerivative (j : Fin 3) : Derivation E (GermCarrier E) (GermCarrier E) where
  toLinearMap := (MvPolynomial.finSuccEquiv E 3).toLinearMap.comp
    ((MvPolynomial.pderiv j.succ).toLinearMap.comp (MvPolynomial.finSuccEquiv E 3).symm.toLinearMap)
  map_one_eq_zero' := by simp
  leibniz' a b := by
    simp [Derivation.leibniz, smul_eq_mul]

theorem germSeedDerivative_apply (j : Fin 3) (F : GermCarrier E) :
    germSeedDerivative j F = MvPolynomial.finSuccEquiv E 3
      (MvPolynomial.pderiv j.succ ((MvPolynomial.finSuccEquiv E 3).symm F)) := rfl

theorem germSeedDerivative_lift (j : Fin 3) (Q : Polynomial E) :
    germSeedDerivative j (liftPolynomial Q) = 0 := by
  induction Q using Polynomial.induction_on' with
  | add P Q hp hq => simp [hp, hq]
  | monomial n a =>
    have hX : germSeedDerivative j (Polynomial.X : GermCarrier E) = 0 := by
      rw [germSeedDerivative_apply, ← MvPolynomial.finSuccEquiv_X_zero,
        AlgEquiv.symm_apply_apply, MvPolynomial.pderiv_X_of_ne, map_zero]
      exact (Fin.succ_ne_zero j).symm
    have hC : germSeedDerivative j (Polynomial.C (MvPolynomial.C a)) = 0 := by
      rw [germSeedDerivative_apply]
      have h := DFunLike.congr_fun (MvPolynomial.finSuccEquiv_comp_C_eq_C (R := E) 3) a
      change (MvPolynomial.finSuccEquiv E 3).symm (Polynomial.C (MvPolynomial.C a)) = _ at h
      rw [h, MvPolynomial.pderiv_C, map_zero]
    change germSeedDerivative j ((Polynomial.monomial n a).map MvPolynomial.C) = _
    rw [Polynomial.map_monomial, ← Polynomial.C_mul_X_pow_eq_monomial, Derivation.leibniz,
      Derivation.leibniz_pow, hX, hC]
    simp

theorem germSeedDerivative_coordinate_of_ne {j k : Fin 3} (h : k ≠ j) :
    germSeedDerivative (E := E) j (coordinatePolynomial k) = 0 := by
  rw [germSeedDerivative_apply, coordinatePolynomial, ← MvPolynomial.finSuccEquiv_X_succ,
    AlgEquiv.symm_apply_apply, MvPolynomial.pderiv_X_of_ne, map_zero]
  exact fun h' => h (Fin.succ_injective _ h')

theorem germSeedDerivative_stable_ordinary (j : Fin 3) (hj : j ≠ 0) (a u : E) :
    ∀ F ∈ ordinaryIdeal a u, germSeedDerivative j F ∈ ordinaryIdeal a u := by
  unfold ordinaryIdeal
  apply derivation_preserves_contact_ideal
  · rw [germSeedDerivative_lift]
    exact Ideal.zero_mem _
  · have hsub : germSeedDerivative j (coordinatePolynomial 0 - liftPolynomial (Polynomial.C u)) =
        germSeedDerivative j (coordinatePolynomial 0) -
          germSeedDerivative j (liftPolynomial (Polynomial.C u)) :=
      (germSeedDerivative j).toLinearMap.map_sub _ _
    rw [hsub, germSeedDerivative_coordinate_of_ne (Ne.symm hj), germSeedDerivative_lift, sub_zero]
    exact Ideal.zero_mem _

theorem germSeedDerivative_stable_other_virtual (j z : Fin 3) (hj : j ≠ 0) (h : z ≠ j)
    (d : Polynomial E) (A : Fin 2 → Polynomial E) (B : Polynomial E) :
    ∀ F ∈ divisorIdeal d (virtualEquation A B z),
      germSeedDerivative j F ∈ divisorIdeal d (virtualEquation A B z) := by
  unfold divisorIdeal
  apply derivation_preserves_contact_ideal
  · rw [germSeedDerivative_lift]
    exact Ideal.zero_mem _
  · have eq : germSeedDerivative j (virtualEquation A B z) = 0 := by
      simp [virtualEquation, Derivation.leibniz, germSeedDerivative_lift,
        germSeedDerivative_coordinate_of_ne h, germSeedDerivative_coordinate_of_ne (Ne.symm hj)]
    rw [eq]
    exact Ideal.zero_mem _

theorem pderiv_mem_globalBox (j : Fin 4) (D w y b c : ℕ) {F : MvPolynomial (Fin 4) E}
    (hF : F ∈ globalBox E D w y b c) :
    MvPolynomial.pderiv j F ∈ globalBox E D w y b c := by
  have sum_eq : MvPolynomial.pderiv j F =
      ∑ e ∈ F.support, MvPolynomial.pderiv j (MvPolynomial.monomial e (F.coeff e)) := by
    rw [← map_sum, MvPolynomial.support_sum_monomial_coeff]
  rw [sum_eq]
  apply Submodule.sum_mem
  intro e he
  rw [MvPolynomial.pderiv_monomial]
  apply (mem_globalBox E D w y b c _).mpr
  intro d hd
  have h := (mem_globalBox E D w y b c F).mp hF e he
  have hd' := MvPolynomial.support_monomial_subset hd
  rw [Finset.mem_singleton] at hd'
  subst d
  have hle (i : Fin 4) : ((e - Finsupp.single j 1 : Fin 4 →₀ ℕ) i) ≤ e i := by
    rw [Finsupp.tsub_apply]
    exact Nat.sub_le _ _
  exact ⟨(Nat.add_le_add (hle 0) (Nat.mul_le_mul_left w (hle 1))).trans_lt h.1,
    (hle 1).trans h.2.1, (hle 2).trans h.2.2.1, (hle 3).trans h.2.2.2⟩

theorem iterated_pderiv_mem_globalBox (j : Fin 4) (D w y b c r : ℕ)
    {F : MvPolynomial (Fin 4) E} (hF : F ∈ globalBox E D w y b c) :
    ((MvPolynomial.pderiv j : MvPolynomial (Fin 4) E → MvPolynomial (Fin 4) E)^[r]) F ∈
      globalBox E D w y b c := by
  induction r with
  | zero => simpa
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact pderiv_mem_globalBox j D w y b c ih

theorem finSuccEquiv_iterated_pderiv (j : Fin 3) (r : ℕ) (F : MvPolynomial (Fin 4) E) :
    MvPolynomial.finSuccEquiv E 3
      (((MvPolynomial.pderiv j.succ : MvPolynomial (Fin 4) E → MvPolynomial (Fin 4) E)^[r]) F) =
    ((germSeedDerivative j : GermCarrier E → GermCarrier E)^[r]) (MvPolynomial.finSuccEquiv E 3 F) := by
  have h : Function.Semiconj (MvPolynomial.finSuccEquiv E 3)
      (MvPolynomial.pderiv j.succ) (germSeedDerivative j) := by
    intro Q
    rw [germSeedDerivative_apply, AlgEquiv.symm_apply_apply]
  exact h.iterate_right r F


theorem iterate_derivation_drops_power_saturating
    (D : Derivation E (GermCarrier E) (GermCarrier E)) (J : Ideal (GermCarrier E))
    (n r : ℕ) {F : GermCarrier E} (h : F ∈ J^n) :
    ((D : GermCarrier E → GermCarrier E)^[r]) F ∈ J^(n-r) := by
  by_cases hr : r ≤ n
  · exact iterate_derivation_drops_power D J n r hr h
  · have hz : n-r = 0 := by omega
    simp [hz, Submodule.pow_zero, Ideal.one_eq_top]


section Centered

variable {I : Type} [DecidableEq K] [DecidableEq I]
variable {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K}
variable {w agreement errors excess : ℕ}

theorem iterated_seed_derivative_vanishes_at_cutoff
    (D : CenteredVirtualData x nodes σ w agreement errors excess)
    (embed : K →+* E) (cut w' y b c m M0 M1 r : ℕ)
    (second : Bool) (hcut : 0 < cut)
    (hdegree : w + D.d0.natDegree - affineDegree D.A0 ≤ w')
    (room : cut ≤ agreement * m + (M0+M1-r) * D.d0.natDegree)
    (F : globalBox E cut w' y b c)
    (ordinary : ∀ i ∈ nodes, MvPolynomial.finSuccEquiv E 3 F.val ∈
      ordinaryIdeal (embed (x i)) (embed (D.fixedWord i)) ^ m)
    (virtual0 : MvPolynomial.finSuccEquiv E 3 F.val ∈ divisorIdeal (D.d0.map embed)
      (virtualEquation (fun j => (D.A0 j).map embed) (D.C1.map embed) 1) ^ M0)
    (virtual1 : MvPolynomial.finSuccEquiv E 3 F.val ∈ divisorIdeal (D.d1.map embed)
      (virtualEquation (fun j => ((D.A0 j).map σ.toRingHom).map embed) (D.D1.map embed) 2) ^ M1) :
    ∀ g ∈ D.seeds, specializeGerm ((D.normalized g).map embed) (embed g) (embed (σ g))
      (MvPolynomial.finSuccEquiv E 3
        (((MvPolynomial.pderiv (if second then 3 else 2) :
          MvPolynomial (Fin 4) E → MvPolynomial (Fin 4) E)^[r]) F.val)) = 0 := by
  let j : Fin 3 := if second then 2 else 1
  let G := MvPolynomial.finSuccEquiv E 3 F.val
  let deriv : Derivation E (GermCarrier E) (GermCarrier E) := germSeedDerivative j
  let dF := ((deriv : GermCarrier E → GermCarrier E)^[r]) G
  have hJ : j.succ = (if second then 3 else 2 : Fin 4) := by cases second <;> decide
  rw [← hJ, finSuccEquiv_iterated_pderiv]
  change ∀ g ∈ D.seeds, specializeGerm ((D.normalized g).map embed) (embed g) (embed (σ g)) dF = 0
  have hj : j ≠ 0 := by cases second <;> decide
  have ord (i : I) (hi : i ∈ nodes) : dF ∈ ordinaryIdeal (embed (x i)) (embed (D.fixedWord i)) ^ m :=
    iterate_derivation_preserves_power deriv _ (germSeedDerivative_stable_ordinary j hj _ _) m r
      (ordinary i hi)
  have deg (g : K) (hg : g ∈ D.seeds) :
      (specializeGerm ((D.normalized g).map embed) (embed g) (embed (σ g)) dF).natDegree < cut := by
    let dBox : globalBox E cut w' y b c := ⟨_, iterated_pderiv_mem_globalBox j.succ cut w' y b c r F.property⟩
    have hp : ((D.normalized g).map embed).natDegree ≤ w' := by
      rw [Polynomial.natDegree_map]
      exact (D.normalized_degree g hg).trans hdegree
    have h := natDegree_specialize_globalBox cut w' y b c hcut dBox
      ((D.normalized g).map embed) hp (embed g) (embed (σ g))
    change (specializeGerm _ _ _ (MvPolynomial.finSuccEquiv E 3
      (((MvPolynomial.pderiv j.succ : MvPolynomial (Fin 4) E → MvPolynomial (Fin 4) E)^[r]) F.val))).natDegree < cut at h
    rw [finSuccEquiv_iterated_pderiv] at h
    exact h
  cases second with
  | false =>
    have left := iterate_derivation_drops_power_saturating deriv _ M0 r virtual0
    have stable := germSeedDerivative_stable_other_virtual (1 : Fin 3) 2 (by decide) (by decide)
      (D.d1.map embed) (fun j => ((D.A0 j).map σ.toRingHom).map embed) (D.D1.map embed)
    have right := iterate_derivation_preserves_power deriv _ stable M1 r virtual1
    apply vanishes_on_mapped_centered_virtual D embed dF m (M0-r) M1 ord left right
    intro g hg
    refine (deg g hg).trans_le ?_
    refine room.trans ?_
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_right
    omega
  | true =>
    have stable := germSeedDerivative_stable_other_virtual (2 : Fin 3) 1 (by decide) (by decide)
      (D.d0.map embed) (fun j => (D.A0 j).map embed) (D.C1.map embed)
    have left := iterate_derivation_preserves_power deriv _ stable M0 r virtual0
    have right := iterate_derivation_drops_power_saturating deriv _ M1 r virtual1
    apply vanishes_on_mapped_centered_virtual D embed dF m M0 (M1-r) ord left right
    intro g hg
    refine (deg g hg).trans_le ?_
    refine room.trans ?_
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_right
    omega

theorem iterated_seed_derivative_vanishes
    (D : CenteredVirtualData x nodes σ w agreement errors excess)
    (embed : K →+* E) (cut w' y b c m M0 M1 r : ℕ)
    (second : Bool) (hcut : 0 < cut)
    (hdegree : w + D.d0.natDegree - affineDegree D.A0 ≤ w')
    (_trim : r ≤ (if second then M1 else M0))
    (room : cut ≤ agreement * m + (M0+M1-r) * D.d0.natDegree)
    (F : globalBox E cut w' y b c)
    (ordinary : ∀ i ∈ nodes, MvPolynomial.finSuccEquiv E 3 F.val ∈
      ordinaryIdeal (embed (x i)) (embed (D.fixedWord i)) ^ m)
    (virtual0 : MvPolynomial.finSuccEquiv E 3 F.val ∈ divisorIdeal (D.d0.map embed)
      (virtualEquation (fun j => (D.A0 j).map embed) (D.C1.map embed) 1) ^ M0)
    (virtual1 : MvPolynomial.finSuccEquiv E 3 F.val ∈ divisorIdeal (D.d1.map embed)
      (virtualEquation (fun j => ((D.A0 j).map σ.toRingHom).map embed) (D.D1.map embed) 2) ^ M1) :
    ∀ g ∈ D.seeds, specializeGerm ((D.normalized g).map embed) (embed g) (embed (σ g))
      (MvPolynomial.finSuccEquiv E 3
        (((MvPolynomial.pderiv (if second then 3 else 2) :
          MvPolynomial (Fin 4) E → MvPolynomial (Fin 4) E)^[r]) F.val)) = 0 := by
  exact iterated_seed_derivative_vanishes_at_cutoff D embed cut w' y b c m M0 M1 r second
    hcut hdegree room F ordinary virtual0 virtual1

end Centered

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
