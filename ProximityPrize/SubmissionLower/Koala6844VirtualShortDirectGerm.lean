import ProximityPrize.SubmissionLower.Koala6844VirtualShortGerm
import ProximityPrize.SubmissionLower.Koala6844VirtualShortGermDigit


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open Polynomial Koala6844Normalization
open scoped BigOperators Classical Matrix

noncomputable section
set_option autoImplicit false

variable {K E I : Type} [Field K] [Field E]

def collectTaylor (embed : K →+* E) (ζ : E) :
    MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 2) (Polynomial E) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (Polynomial.C.comp embed))
    ![MvPolynomial.C (Polynomial.X + Polynomial.C ζ), MvPolynomial.X 0, MvPolynomial.X 1]

theorem collectTaylor_injective (embed : K →+* E) (ζ : E) :
    Function.Injective (collectTaylor embed ζ) := by
  let R := MvPolynomial (Fin 3) E
  let p : Polynomial E →+* R := Polynomial.eval₂RingHom MvPolynomial.C
    (MvPolynomial.X 0 - MvPolynomial.C ζ)
  let rev : MvPolynomial (Fin 2) (Polynomial E) →+* R :=
    MvPolynomial.eval₂Hom p ![MvPolynomial.X 1, MvPolynomial.X 2]
  have h : rev.comp (collectTaylor embed ζ) = MvPolynomial.map embed := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [collectTaylor, p, rev]
      exact (MvPolynomial.map_C embed a).symm
    · intro i
      fin_cases i <;> simp [collectTaylor, p, rev, Matrix.cons_val_two] <;>
        exact (MvPolynomial.map_X embed _).symm
  intro F G e
  have h' := congrArg rev e
  apply MvPolynomial.map_injective embed embed.injective
  change (rev.comp (collectTaylor embed ζ)) F = (rev.comp (collectTaylor embed ζ)) G at h'
  simpa only [h] using h'

private theorem collectTaylor_monomial (embed : K →+* E) (ζ : E)
    (e : Fin 3 →₀ ℕ) (a : K) :
    collectTaylor embed ζ (MvPolynomial.monomial e a) =
      MvPolynomial.C (Polynomial.C (embed a) * (Polynomial.X + Polynomial.C ζ)^e 0) *
        ((MvPolynomial.X (0 : Fin 2))^e 1 * (MvPolynomial.X (1 : Fin 2))^e 2) := by
  rw [collectTaylor, MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [Fin.prod_univ_three]
  simp only [RingHom.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    map_mul, map_pow, mul_assoc]
  rfl

theorem collectTaylor_caps (embed : K →+* E) (ζ : E)
    (J : MvPolynomial (Fin 3) K) (u v : ℕ) (hy : J.degreeOf 1 ≤ u)
    (hT : J.weightedTotalDegree ![0,1,1] ≤ v) :
    (collectTaylor embed ζ J).degreeOf 0 ≤ u ∧ (collectTaylor embed ζ J).totalDegree ≤ v := by
  classical
  have hJ : collectTaylor embed ζ J =
    ∑ e ∈ J.support, collectTaylor embed ζ (MvPolynomial.monomial e (J.coeff e)) := by
    rw [← map_sum, MvPolynomial.support_sum_monomial_coeff]
  rw [hJ]
  refine ⟨?_,?_⟩
  · apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
    apply Finset.sup_le
    intro e he
    rw [collectTaylor_monomial]
    apply (MvPolynomial.degreeOf_C_mul_le _ _ _).trans
    apply (MvPolynomial.degreeOf_mul_le _ _ _).trans
    have h0 : (((MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) (Polynomial E))^(e 1)).degreeOf 0)
        ≤ e 1 := by
      simpa only [MvPolynomial.degreeOf_X, if_pos rfl, if_true, mul_one] using
        MvPolynomial.degreeOf_pow_le (0 : Fin 2)
          (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) (Polynomial E)) (e 1)
    have h1 : (((MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) (Polynomial E))^(e 2)).degreeOf 0)
        ≤ 0 :=
      (MvPolynomial.degreeOf_X_pow_of_ne (e 2) (by decide : (0 : Fin 2) ≠ 1)).le
    have hh := (MvPolynomial.degreeOf_le_iff.mp hy) e he
    exact (Nat.add_le_add h0 h1).trans (by simpa only [add_zero] using hh)
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro e he
    rw [collectTaylor_monomial]
    apply (MvPolynomial.totalDegree_mul _ _).trans
    rw [MvPolynomial.totalDegree_C, zero_add]
    apply (MvPolynomial.totalDegree_mul _ _).trans
    simp only [MvPolynomial.totalDegree_X_pow]
    have h := (MvPolynomial.le_weightedTotalDegree ![0,1,1] he).trans hT
    rw [Finsupp.weight_eq_sum, Fin.sum_univ_three] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      nsmul_eq_mul, mul_zero, mul_one, zero_add] at h
    simp only [show Matrix.vecHead (Matrix.vecTail (![1,1] : Fin 2 → ℕ)) = 1 from rfl,
      mul_one, Nat.cast_id] at h
    exact h

theorem eval_collectTaylor (embed : K →+* E) (ζ : E)
    (J : MvPolynomial (Fin 3) K) (P : Polynomial K) (g : K) :
    MvPolynomial.eval ![Polynomial.taylor ζ (P.map embed), Polynomial.C (embed g)]
      (collectTaylor embed ζ J) =
      Polynomial.taylor ζ ((MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X,P,Polynomial.C g] J).map embed) := by
  let h := (MvPolynomial.eval ![Polynomial.taylor ζ (P.map embed), Polynomial.C (embed g)])
  let f := (Polynomial.taylorAlgHom ζ).toRingHom.comp (Polynomial.mapRingHom embed)
  have hh : h.comp (collectTaylor embed ζ) =
      f.comp (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X,P,Polynomial.C g]) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [h, f, collectTaylor, Polynomial.taylorAlgHom_apply]
    · intro i
      fin_cases i <;> simp [h, f, collectTaylor, Polynomial.taylorAlgHom_apply,
        Polynomial.taylor_X, Matrix.cons_val_two]
  exact DFunLike.congr_fun hh J

variable [DecidableEq K] [DecidableEq I]
variable {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K}
variable {w agreement errors excess : ℕ}

theorem direct_germ_card_le
    (D : CenteredVirtualData x nodes σ w agreement errors excess)
    (embed : K →+* E) (G : ActiveResultantGerm D embed)
    (p u v : ℕ) (hp : v < p)
    (σpow : ∀ g ∈ D.seeds, embed (σ g) = (embed g)^p)
    (J : MvPolynomial (Fin 3) K) (hJ : J ≠ 0)
    (hy : J.degreeOf 1 ≤ u) (ht : J.weightedTotalDegree ![0,1,1] ≤ v)
    (S : Finset K) (hS : S ⊆ D.seeds)
    (roots : ∀ g ∈ S, MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X,D.selected g,Polynomial.C g] J = 0) :
    S.card ≤ v+p*u := by
  classical
  let ζ := G.center
  let T0 := Polynomial.taylor ζ (D.d0.map embed)
  let C1 := Polynomial.taylor ζ (D.C1.map embed)
  let J' := collectTaylor embed ζ J
  let V := affineGermNumerator J' (Polynomial.X^G.order) (-C1) T0
  have hnJ : J' ≠ 0 := fun hz =>
    hJ (collectTaylor_injective embed ζ (hz.trans (map_zero _).symm))
  have hnV : V ≠ 0 := affineGermNumerator_ne_zero J' hnJ _ _ _
    (pow_ne_zero _ Polynomial.X_ne_zero)
  obtain ⟨hY,hT⟩ := collectTaylor_caps embed ζ J u v hy ht
  obtain ⟨hVY,hVT⟩ := affineGermNumerator_caps J' (Polynomial.X^G.order) (-C1) T0 u v hY hT
  obtain ⟨n,hn,hlow⟩ := exists_firstCoeffLayer V hnV
  let J0 := coeffLayer n V
  have hj0 : J0.degreeOf 0 ≤ u := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    exact (MvPolynomial.degreeOf_le_iff.mp hVY) e (support_coeffLayer_subset n V he)
  have hj1 : J0.totalDegree ≤ v := by
    rw [MvPolynomial.totalDegree]
    exact Finset.sup_le (fun e he => (MvPolynomial.le_totalDegree (support_coeffLayer_subset n V he)).trans hVT)
  choose U hU heU using fun (g : K) (hg : g ∈ S) => G.relation g (hS hg)
  let y : K → E := fun g => if hg : g ∈ S then (U g hg).eval 0 else 0
  have hroot (g : K) (hg : g ∈ S) : MvPolynomial.eval ![y g,embed g] J0 = 0 := by
    let P' := Polynomial.taylor ζ ((D.selected g).map embed)
    have hz : MvPolynomial.eval ![P', Polynomial.C (embed g)] J' = 0 := by
      rw [show MvPolynomial.eval ![P', Polynomial.C (embed g)] J' = _ from
        eval_collectTaylor embed ζ J (D.selected g) g, roots g hg, Polynomial.map_zero, map_zero]
    have he : Polynomial.X^G.order * U g hg + (-C1)*Polynomial.C (embed g) = T0*P' := by
      have hh := hU g hg
      change Polynomial.taylor ζ ((D.d0 * D.selected g + Polynomial.C g * D.C1).map embed) =
        Polynomial.X ^ G.order * U g hg at hh
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, map_add,
        Polynomial.taylor_mul, Polynomial.taylor_C] at hh
      change T0*P' + Polynomial.C (embed g)*C1 = _ at hh
      linear_combination -hh
    have hvzero : MvPolynomial.eval ![U g hg, Polynomial.C (embed g)] V = 0 := by
      rw [show MvPolynomial.eval ![U g hg, Polynomial.C (embed g)] V = _ from
        affineGermNumerator_eval J' (Polynomial.X^G.order) (-C1) T0
          (U g hg) (Polynomial.C (embed g)) P' he, hz, mul_zero]
    have h := eval_firstCoeffLayer_zero V n hlow (U g hg) (embed g) hvzero
    simpa [y, hg, J0] using h
  apply card_le_of_active_germ_equation embed p u v J0 hn hj0 hj1 hp
    (germFirst D embed ζ 0) (germFirst D embed ζ 1) G.c
    (germSecond D embed ζ 0) (germSecond D embed ζ 1)
    G.first_ne G.c_ne G.second_zero_ne S y hroot
  intro g hg
  rw [← σpow g (hS hg)]
  simpa [y,hg,ζ] using heU g hg

end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort
