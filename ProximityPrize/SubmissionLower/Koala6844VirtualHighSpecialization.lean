import ProximityPrize.SubmissionLower.Koala6844VirtualHighGlobalBox
import ProximityPrize.SubmissionLower.Koala6844VirtualHighWitness


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Polynomial Koala6844Normalization
open scoped BigOperators Classical Matrix

noncomputable section

set_option autoImplicit false

variable {K E : Type} [Field K] [Field E]

theorem specialize_finSuccEquiv (P : Polynomial E) (s t : E) :
    (specializeGerm P s t).comp (MvPolynomial.finSuccEquiv E 3).toRingHom =
      MvPolynomial.eval₂Hom Polynomial.C ![X, P, Polynomial.C s, Polynomial.C t] := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [specializeGerm, MvPolynomial.finSuccEquiv_apply]
  · intro j
    fin_cases j
    · simp [specializeGerm, MvPolynomial.finSuccEquiv_X_zero]
    · change specializeGerm P s t (MvPolynomial.finSuccEquiv E 3
        (MvPolynomial.X (Fin.succ (0 : Fin 3)))) = _
      rw [MvPolynomial.finSuccEquiv_X_succ]
      simp [specializeGerm]
    · change specializeGerm P s t (MvPolynomial.finSuccEquiv E 3
        (MvPolynomial.X (Fin.succ (1 : Fin 3)))) = _
      rw [MvPolynomial.finSuccEquiv_X_succ]
      simp [specializeGerm, Matrix.cons_val_two]
    · change specializeGerm P s t (MvPolynomial.finSuccEquiv E 3
        (MvPolynomial.X (Fin.succ (2 : Fin 3)))) = _
      rw [MvPolynomial.finSuccEquiv_X_succ]
      simp [specializeGerm, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem degree_monomial_specialization (P : Polynomial E) (s t : E)
    (e : Fin 4 →₀ ℕ) (a : E) :
    (MvPolynomial.eval₂Hom Polynomial.C ![X, P, Polynomial.C s, Polynomial.C t]
      (MvPolynomial.monomial e a)).natDegree ≤ e 0 + P.natDegree * e 1 := by
  rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [Fin.prod_univ_succ]
  have hprod :
      (∏ i : Fin 3, ![X, P, Polynomial.C s, Polynomial.C t] i.succ ^ e i.succ) =
        P ^ e 1 * (Polynomial.C s ^ e 2 * Polynomial.C t ^ e 3) := by
    simp [Fin.prod_univ_three, Matrix.cons_val_two, Matrix.cons_val_three, mul_assoc]
  simp only [Matrix.cons_val_zero]
  rw [hprod]
  calc
    _ ≤ (Polynomial.C a).natDegree +
        ((X : Polynomial E) ^ e 0 *
          (P ^ e 1 * (Polynomial.C s ^ e 2 * Polynomial.C t ^ e 3))).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ e 0 + P.natDegree * e 1 := by
      have h := Polynomial.natDegree_mul_le
        (p := (X : Polynomial E) ^ e 0)
        (q := P ^ e 1 * (Polynomial.C s ^ e 2 * Polynomial.C t ^ e 3))
      have h' := Polynomial.natDegree_mul_le (p := P ^ e 1)
        (q := Polynomial.C s ^ e 2 * Polynomial.C t ^ e 3)
      have h'' := Polynomial.natDegree_mul_le (p := Polynomial.C s ^ e 2)
        (q := Polynomial.C t ^ e 3)
      simp only [Polynomial.natDegree_C, Polynomial.natDegree_pow, Polynomial.natDegree_X,
        mul_one, add_zero, zero_add] at *
      rw [Nat.mul_comm P.natDegree]
      omega

theorem natDegree_specialize_globalBox
    (D w y b c : ℕ) (hD : 0 < D) (F : globalBox E D w y b c)
    (P : Polynomial E) (hp : P.natDegree ≤ w) (s t : E) :
    (specializeGerm P s t (MvPolynomial.finSuccEquiv E 3 F.val)).natDegree < D := by
  let ev := MvPolynomial.eval₂Hom Polynomial.C ![X, P, Polynomial.C s, Polynomial.C t]
  have he : specializeGerm P s t (MvPolynomial.finSuccEquiv E 3 F.val) = ev F.val :=
    DFunLike.congr_fun (specialize_finSuccEquiv P s t) F.val
  rw [he]
  have eqsum : ev F.val = ∑ e ∈ F.val.support, ev (MvPolynomial.monomial e (F.val.coeff e)) := by
    rw [← map_sum, MvPolynomial.support_sum_monomial_coeff]
  rw [eqsum]
  apply (Polynomial.natDegree_sum_le_of_forall_le _ _ ?_).trans_lt (Nat.sub_lt hD Nat.one_pos)
  intro e he
  have h := ((mem_globalBox E D w y b c F.val).mp F.property) e he
  have hdeg := (degree_monomial_specialization P s t e (F.val.coeff e)).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right (e 1) hp) (e 0))
  exact hdeg.trans (by omega)

section Centered

variable {I : Type} [DecidableEq K] [DecidableEq I]
variable {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K}
variable {w agreement errors excess : ℕ}

theorem vanishes_on_mapped_centered_virtual
    (D : CenteredVirtualData x nodes σ w agreement errors excess)
    (embed : K →+* E) (F : GermCarrier E) (m M0 M1 : ℕ)
    (ordinary : ∀ i ∈ nodes, F ∈ ordinaryIdeal (embed (x i)) (embed (D.fixedWord i)) ^ m)
    (virtual0 : F ∈ divisorIdeal (D.d0.map embed)
      (virtualEquation (fun j => (D.A0 j).map embed) (D.C1.map embed) 1) ^ M0)
    (virtual1 : F ∈ divisorIdeal (D.d1.map embed)
      (virtualEquation (fun j => ((D.A0 j).map σ.toRingHom).map embed) (D.D1.map embed) 2) ^ M1)
    (hdegree : ∀ g ∈ D.seeds,
      (specializeGerm ((D.normalized g).map embed) (embed g) (embed (σ g)) F).natDegree <
        agreement * m + (M0+M1) * D.d0.natDegree) :
    ∀ g ∈ D.seeds, specializeGerm ((D.normalized g).map embed) (embed g) (embed (σ g)) F = 0 := by
  intro g hg
  let P := D.normalized g
  let f := specializeGerm (P.map embed) (embed g) (embed (σ g))
  let agreeing := nodes.filter fun i => P.eval (x i) = D.fixedWord i
  have hagree : agreement ≤ agreeing.card := D.normalized_agreements g hg
  have h0 : (D.d0.map embed)^M0 ∣ f F := by
    apply virtual_power_dvd_specialization f M0 virtual0
    · simp [f]
    · have e := congrArg (fun Q : Polynomial K => Q.map embed) (D.equation0 g hg)
      simp only [specializeAffine, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at e
      have hh : f (virtualEquation (fun j => (D.A0 j).map embed) (D.C1.map embed) 1) =
          D.d0.map embed * (D.selected g).map embed := by
        simp only [f, virtualEquation, map_sub, map_add, map_mul, specialize_liftPolynomial,
          specialize_value, specialize_first_seed, P]
        rw [e, add_sub_cancel_right]
      rw [hh]
      exact dvd_mul_right _ _
  have h1 : (D.d1.map embed)^M1 ∣ f F := by
    apply virtual_power_dvd_specialization f M1 virtual1
    · simp [f]
    · have e := congrArg (fun Q : Polynomial K => Q.map embed) (D.equation1 g hg)
      simp only [specializeAffine, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at e
      rw [show σ.toRingHom g = σ g from rfl] at e
      have hh : f (virtualEquation (fun j => ((D.A0 j).map σ.toRingHom).map embed)
          (D.D1.map embed) 2) = D.d1.map embed * ((D.selected g).map σ.toRingHom).map embed := by
        simp only [f, virtualEquation, map_sub, map_add, map_mul, specialize_liftPolynomial,
          specialize_value, specialize_second_seed, P]
        rw [e, add_sub_cancel_right]
      rw [hh]
      exact dvd_mul_right _ _
  have off (d : Polynomial K) (hoff : ∀ i ∈ nodes, d.eval (x i) ≠ 0) :
      ∀ i ∈ agreeing, (d.map embed).eval (embed (x i)) ≠ 0 := by
    intro i hi
    rw [Polynomial.eval_map_apply]
    intro h
    exact hoff i (Finset.mem_filter.mp hi).1 (embed.injective (by simpa using h))
  refine eq_zero_of_mixed_contact_divisibility agreeing (fun i => embed (x i))
    (embed.injective.comp x.injective).injOn (f F) (D.d0.map embed) (D.d1.map embed)
    m M0 M1 (Polynomial.map_ne_zero D.d0_ne) (Polynomial.map_ne_zero D.d1_ne)
    (D.coprime_content.map (Polynomial.mapRingHom embed)) (off _ D.content0_off_domain)
    (off _ D.content1_off_domain) ?_ h0 h1 ?_
  · intro i hi
    obtain ⟨hn, hv⟩ := Finset.mem_filter.mp hi
    apply virtual_power_dvd_specialization f m (ordinary i hn)
    · simp [f]
    · rw [show f (coordinatePolynomial 0 - liftPolynomial (Polynomial.C (embed (D.fixedWord i)))) =
          P.map embed - Polynomial.C (embed (D.fixedWord i)) by simp [f]]
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C,
        Polynomial.eval_map_apply, hv, sub_self]
  · refine (hdegree g hg).trans_le ?_
    rw [Polynomial.natDegree_map, Polynomial.natDegree_map, D.degree_content]
    rw [Nat.add_mul, Nat.add_assoc]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right m hagree) _

end Centered

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
