import ProximityPrize.SubmissionLower.Fast068
import ProximityPrize.SubmissionLower.Fast069
import ProximityPrize.SubmissionLower.Fast070
set_option Elab.async false
set_option autoImplicit true
section
namespace K1_13_3
noncomputable section
open Polynomial K1 K1_13
open scoped BigOperators
def c1 : Prop :=
  ∀ (w : I → K) (T : ℕ) (P : Row 4), T ≤ terminal → BankRow w T P →
    ∀ S : Geom[X], S.natDegree ≤ 133671 →
      (∃ H : Finset I, 180265 ≤ H.card ∧
        ∀ i ∈ H, S.eval (embed (node i)) = embed (w i)) →
      OrderAt P S (requiredOrder T)
end
end K1_13_3
end
section
set_option maxRecDepth 12000
namespace K1_13_3_1
noncomputable section
open Polynomial K1 K1_13 K1_13_3 FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators
def line (P : Row 4) (S U : Geom[X]) : Polynomial Geom[X] :=
  MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (jet S i) + Polynomial.C (jet U i) * Polynomial.X) P
private theorem eval_line (P : Row 4) (S U : Geom[X]) (c : Geom) :
    (line P S U).eval (Polynomial.C c) = atJet P (S + c • U) := by
  change (evalRingHom (Polynomial.C c))
    (MvPolynomial.eval₂ Polynomial.C
      (fun i => Polynomial.C (jet S i) + Polynomial.C (jet U i) * Polynomial.X) P) = _
  rw [MvPolynomial.hom_eval₂]
  have hC : (evalRingHom (C c)).comp C = RingHom.id Geom[X] := RingHom.ext fun f => by simp
  rw [hC]
  change MvPolynomial.eval _ P = MvPolynomial.eval (jet (S + c • U)) P
  have heq : (fun i : Fin 4 => (evalRingHom (C c))
      (Polynomial.C (jet S i) + Polynomial.C (jet U i) * Polynomial.X)) =
      jet (S + c • U) := by
    funext i
    simp only [coe_evalRingHom, eval_mul, eval_C, eval_X, jet, map_add]
    rw [(hasseDeriv i.val).map_smul, Algebra.smul_def, algebraMap_eq, mul_comm]
  rw [heq]
private theorem swapped_coeff (Q : Polynomial Geom[X]) (i j : ℕ) :
    ((Bivariate.swap Q).coeff i).coeff j = (Q.coeff j).coeff i := by
  induction Q using Polynomial.induction_on' with
  | add P Q hp hq => simp [hp, hq]
  | monomial n P =>
    induction P using Polynomial.induction_on' with
    | add P Q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
    | monomial m c =>
      rw [Bivariate.swap_monomial_monomial]
      by_cases hi : m = i <;> by_cases hj : n = j <;> simp [Polynomial.coeff_monomial, hi, hj]
theorem eval_swap (Q : Polynomial Geom[X]) (c : Geom) :
    (Bivariate.swap Q).map (evalRingHom c) = Q.eval (Polynomial.C c) := by
  simpa [Polynomial.aeval_def]
    using (Bivariate.aveal_eq_map_swap c Q).symm
private theorem coeff_contact (Q : Polynomial Geom[X]) (x : Geom) (r : ℕ)
    (h : ∀ c : Geom, (Polynomial.X - C x) ^ r ∣ Q.eval (C c)) (j : ℕ) :
    (Polynomial.X - C x) ^ r ∣ Q.coeff j := by
  let f : Geom[X] →+* Geom[X] := (taylorAlgHom x).toRingHom
  let A := Q.map f
  have heval (c : Geom) : A.eval (C c) = taylor x (Q.eval (C c)) := by
    change (Q.map f).eval (C c) = f (Q.eval (C c))
    have hC : f (C c) = C c := taylor_C _ _
    rw [← hC, eval_map, eval₂_at_apply]
    rw [hC]
  have hzero (i : ℕ) (hi : i < r) : (Bivariate.swap A).coeff i = 0 := by
    apply eq_zero_of_infinite_isRoot
    have hz (c : Geom) : ((Bivariate.swap A).coeff i).eval c = 0 := by
      change evalRingHom c ((Bivariate.swap A).coeff i) = 0
      rw [← Polynomial.coeff_map, eval_swap, heval]
      exact X_pow_dvd_iff.mp ((X_pow_dvd_taylor_iff_X_sub_C_pow_dvd _ _ _).mpr (h c)) i hi
    simpa [IsRoot, hz] using (Set.infinite_univ : (Set.univ : Set Geom).Infinite)
  apply (X_pow_dvd_taylor_iff_X_sub_C_pow_dvd _ _ _).mp
  apply X_pow_dvd_iff.mpr
  intro i hi
  change (f (Q.coeff j)).coeff i = 0
  rw [← Polynomial.coeff_map, ← swapped_coeff, hzero i hi, Polynomial.coeff_zero]
private theorem line_contacts_zero (Q : Polynomial Geom[X]) (A : Finset I)
    (x : I → Geom) (hx : Function.Injective x) (r : ℕ)
    (h : ∀ i ∈ A, ∀ c : Geom, (Polynomial.X - C (x i)) ^ r ∣ Q.eval (C c))
    (j : ℕ) (hdeg : (Q.coeff j).natDegree < r * A.card) : Q.coeff j = 0 := by
  exact K1_11.eq_zero_of_many_contacts A x hx r (Q.coeff j)
    (fun i hi => coeff_contact Q (x i) r (h i hi) j) hdeg
end
end K1_13_3_1
end
section
set_option maxRecDepth 12000
namespace K1_13_3_1
noncomputable section
open Polynomial K1 K1_13 K1_13_3 FrobeniusLocator
open scoped BigOperators
private theorem exists_direction (L : Geom[X]) (x : Geom) (hx : L.eval x ≠ 0)
    (v : Fin 4 → Geom) :
    ∃ V : Geom[X], V.natDegree ≤ 3 ∧ ∀ i : Fin 4, (jet (L * V) i).eval x = v i := by
  classical
  let B := (Polynomial.X - C x) ^ 4
  have hB : B.Monic := (monic_X_sub_C x).pow _
  have hdeg : B.natDegree = 4 := by simp [B, natDegree_pow]
  have hcop : IsCoprime L B := by
    apply (irreducible_X_sub_C x).coprime_pow_of_not_dvd
    simpa [dvd_iff_isRoot, IsRoot] using hx
  obtain ⟨a, b, hab⟩ := hcop
  let F := taylor (-x) (ofFn 4 v)
  let V := (a * F) %ₘ B
  have hdiv : B ∣ L * V - F := by
    refine ⟨-(b * F + L * ((a * F) /ₘ B)), ?_⟩
    dsimp only [V]
    rw [modByMonic_eq_sub_mul_div]
    linear_combination F * hab
  have hjet := (X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero (L * V - F) x 4).mp hdiv
  refine ⟨V, ?_, fun i => ?_⟩
  · have hne : B ≠ 1 := by
      intro h
      rw [h, natDegree_one] at hdeg
      omega
    have hsmall := natDegree_modByMonic_lt (a * F) hB hne
    rw [hdeg] at hsmall
    exact Nat.le_of_lt_succ hsmall
  · have h := hjet i.val i.isLt
    rw [map_sub, eval_sub, sub_eq_zero] at h
    change (hasseDeriv i.val (L * V)).eval x = v i
    rw [h, ← taylor_coeff, show F = taylor (-x) (ofFn 4 v) from rfl, taylor_taylor,
      add_neg_cancel, taylor_zero, ofFn_coeff_eq_val_of_lt v i.isLt]
private theorem coeff_line_through_zero (P : Symbol) (v : Fin 4 → Geom) (j : ℕ) :
    (MvPolynomial.eval₂ Polynomial.C (fun i => Polynomial.C (v i) * Polynomial.X) P).coeff j =
      MvPolynomial.eval v (MvPolynomial.homogeneousComponent j P) := by
  classical
  rw [MvPolynomial.eval₂_eq, Polynomial.finsetSum_coeff, MvPolynomial.homogeneousComponent_apply]
  change _ = MvPolynomial.eval₂Hom (RingHom.id _) v _
  rw [map_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  rw [MvPolynomial.eval₂Hom_monomial]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, ← map_pow Polynomial.C,
    ← map_prod Polynomial.C, ← map_mul Polynomial.C, ← mul_assoc, Finset.prod_pow_eq_pow_sum,
    Polynomial.coeff_C_mul_X_pow, RingHom.id_apply, Finsupp.degree_apply]
  split_ifs <;> simp_all
private theorem line_at_abscissa (P : Row 4) (S U : Geom[X]) (x : Geom) :
    (line P S U).map (evalRingHom x) =
      MvPolynomial.eval₂ Polynomial.C (fun i : Fin 4 => Polynomial.C ((jet U i).eval x) *
        Polynomial.X) (symbolAt x (shiftJet P S)) := by
  let f := evalRingHom x
  let g (i : Fin 4) : Geom[X] := Polynomial.C (f (jet U i)) * Polynomial.X
  change (mapRingHom f) (MvPolynomial.eval₂ Polynomial.C
    (fun i : Fin 4 => Polynomial.C (jet S i) + Polynomial.C (jet U i) * Polynomial.X) P) =
    MvPolynomial.eval₂Hom Polynomial.C g
      (MvPolynomial.map f (MvPolynomial.eval₂ MvPolynomial.C
        (fun i => MvPolynomial.X i + MvPolynomial.C (jet S i)) P))
  rw [MvPolynomial.hom_eval₂, MvPolynomial.eval₂Hom_map_hom]
  change _ = MvPolynomial.eval₂Hom (Polynomial.C.comp f) g
    (MvPolynomial.eval₂Hom MvPolynomial.C
      (fun i => MvPolynomial.X i + MvPolynomial.C (jet S i)) P)
  rw [MvPolynomial.map_eval₂Hom]
  have hl : (mapRingHom f).comp Polynomial.C = Polynomial.C.comp f := RingHom.ext fun p => by simp
  have hr : (MvPolynomial.eval₂Hom (Polynomial.C.comp f) g).comp MvPolynomial.C =
      Polynomial.C.comp f := RingHom.ext fun p => by simp
  rw [hl, hr]
  congr 1
  funext i
  simp [g, add_comm]
private theorem order_of_locator_lines (P : Row 4) (S L : Geom[X]) (hL : L ≠ 0) (d : ℕ)
    (h : ∀ (V : Geom[X]), V.natDegree ≤ 3 → ∀ j < d, (line P S (L * V)).coeff j = 0) :
    OrderAt P S d := by
  intro m hm
  change d ≤ m.degree
  by_contra! hlt
  have hz (x : Geom) (hx : L.eval x ≠ 0) : ((shiftJet P S).coeff m).eval x = 0 := by
    let A := symbolAt x (shiftJet P S)
    let Q := MvPolynomial.homogeneousComponent m.degree A
    have hQ : Q = 0 := by
      apply (MvPolynomial.homogeneousComponent_isHomogeneous _ _).eq_zero_of_forall_eval_eq_zero
      intro v
      obtain ⟨V, hV, hv⟩ := exists_direction L x hx v
      have heval := congrArg (evalRingHom x) (h V hV m.degree hlt)
      rw [map_zero, ← Polynomial.coeff_map, line_at_abscissa] at heval
      let along (u : Fin 4 → Geom) :=
        (MvPolynomial.eval₂ Polynomial.C (fun i => Polynomial.C (u i) * Polynomial.X) A).coeff
          m.degree
      have hdir := congrArg along (funext hv)
      have hvanish : along v = 0 := hdir.symm.trans heval
      simpa only [along, coeff_line_through_zero] using hvanish
    have hcoeff := congrArg (fun F : Symbol => F.coeff m) hQ
    simpa [Q, MvPolynomial.coeff_homogeneousComponent, A, symbolAt, MvPolynomial.coeff_map]
      using hcoeff
  have hzero : (shiftJet P S).coeff m = 0 := by
    apply eq_zero_of_infinite_isRoot
    refine (finite_setOfPred_isRoot hL).infinite_compl.mono ?_
    intro x hx
    exact hz x hx
  exact MvPolynomial.mem_support_iff.mp hm hzero
end
end K1_13_3_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_4_3
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_4 Polynomial
def c1 : Prop :=
  ∀ (I : Ideal Ambient) (hI : Active I) (f : Equation),
    dual I → Irreducible f → 0 < f.natDegree → f.natDegree < p →
    I.comap ordinaryIncl = Ideal.span {f} →
    letI : I.IsPrime := hI.prime
    let a := parentLocalMap I
    Prime (a (ordinaryIncl f)) ∧ ∃ t, I.map a = Ideal.span {a (ordinaryIncl f), t}
def c2 : Prop :=
  ∀ (I : Ideal Ambient) (hI : Active I) (f : Equation),
    ¬ dual I → Irreducible f → 0 < f.natDegree → seedDegree f < p →
    I.comap ordinaryIncl = Ideal.span {f} →
    letI : I.IsPrime := hI.prime
    let a := parentLocalMap I
    let q := jetQuotientMap I
    let f' := q (a (ordinaryIncl f))
    Function.Injective (fun x : JetQuotient I => f' * x) ∧
      (I.map a).map q = Ideal.span {f'}
theorem of_children (h1 : c1) (h2 : c2) : K1_14_2_2_4.c3 := by
  intro H P I m r hH hs hy hI hr hrm hhigh ho
  by_cases hmem : ordinaryIncl H ∈ I
  · obtain ⟨f, g, e, hfac, he, hf, hpos, hdeg, hseed, hcontract, hg⟩ :=
      ordinary_factorization hI hH hhigh hmem
    have hpow : orderOn I (C (f ^ e) * P) m := by
      have hrow : C H * P = C g * (C (f ^ e) * P) := by
        rw [hfac, map_mul, mul_comm (C (f ^ e)) (C g), mul_assoc]
      apply cancel_unit hI.prime hg
      rwa [← hrow]
    refine cancel_power (f := f) ?_ he hrm hpow
    have : I.IsPrime := hI.prime
    intro Q n hQ
    by_cases hd : dual I
    · obtain ⟨hprime, t, ht⟩ := h1 I hI f hd hf hpos (hdeg.trans_lt hy) hcontract
      apply (order_dual_iff I hd Q n).mpr
      apply cancel_pair hprime ht
      simpa only [map_mul, ordinaryIncl_apply] using
        (order_dual_iff I hd (C f * Q) (n + 1)).mp hQ
    · obtain ⟨hinj, hgen⟩ := h2 I hI f hd hf hpos (hseed.trans_lt hs) hcontract
      apply (order_rankOne_iff I hd Q n).mpr
      apply cancel_principal hgen hinj
      simpa only [map_mul, ordinaryIncl_apply] using
        (order_rankOne_iff I hd (C f * Q) (n + 1)).mp hQ
  · exact lower_order (by omega) (cancel_unit hI.prime hmem ho)
end
end K1_14_2_2_4_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace K1_14_2_2_4_3_2
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_3 K1_14_2_2_4_3
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
abbrev Reduction (I : Ideal Ambient) := MvPolynomial (Fin 2) (JetImageRing I)
abbrev GenericFibre (I : Ideal Ambient) := MvPolynomial (Fin 2) (JetImageField I)
def reduceJets (I : Ideal Ambient) : Ambient →+* Reduction I :=
  specializeJets (Ideal.Quotient.mk (I.comap jetInclude))
abbrev fibreDenominators (I : Ideal Ambient) : Submonoid (Reduction I) :=
  (JetImageRing I)⁰.map (MvPolynomial.C (σ := Fin 2))
private theorem presentation_jetInclude : seedPresentation.toRingHom.comp jetInclude = MvPolynomial.C := by
  apply MvPolynomial.ringHom_ext
  · simp [jetInclude]
  · intro i
    change seedPresentation (MvPolynomial.rename (Fin.natAdd 2) (MvPolynomial.X i)) = _
    rw [MvPolynomial.rename_X]
    exact seedPresentation_jet i
theorem specialize_jetInclude {A : Type*} [CommRing A] (q : Seeds →+* A) (s : Seeds) :
    specializeJets q (jetInclude s) = MvPolynomial.C (q s) := by
  change MvPolynomial.map q (seedPresentation (jetInclude s)) = _
  rw [show seedPresentation (jetInclude s) = MvPolynomial.C s from
      RingHom.congr_fun presentation_jetInclude s,
    MvPolynomial.map_C]
theorem reduce_surjective (I : Ideal Ambient) : Function.Surjective (reduceJets I) :=
  (MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective).comp seedPresentation.surjective
theorem reduce_kernel (I : Ideal Ambient) : RingHom.ker (reduceJets I) = jetImageIdeal I := by
  rw [reduceJets, specializeJets, ← RingHom.comap_ker, MvPolynomial.ker_map,
    ← presentation_jetInclude, ← Ideal.map_map,
    Ideal.comap_map_of_bijective seedPresentation.toRingHom seedPresentation.bijective, Ideal.mk_ker]
  exact (imageIdeal_eq I).symm
theorem fibre_comp (I : Ideal Ambient) :
    imageFibreMap I = (algebraMap (Reduction I) (GenericFibre I)).comp (reduceJets I) := by
  apply RingHom.ext
  intro z
  change MvPolynomial.map ((algebraMap (JetImageRing I) (JetImageField I)).comp
    (Ideal.Quotient.mk (I.comap jetInclude))) (seedPresentation z) = _
  rw [← MvPolynomial.map_map]
  rfl
theorem image_le (I : Ideal Ambient) : jetImageIdeal I ≤ I :=
  Ideal.map_le_iff_le_comap.mpr le_rfl
theorem disjoint_denominators (I : Ideal Ambient) [I.IsPrime] :
    Disjoint (fibreDenominators I : Set (Reduction I)) (I.map (reduceJets I) : Set (Reduction I)) := by
  have : (I.comap jetInclude).IsPrime := Ideal.IsPrime.comap jetInclude
  rw [Set.disjoint_left]
  rintro _ ⟨d, hd, rfl⟩ hm
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective (I := I.comap jetInclude) d
  have hs : reduceJets I (jetInclude s) = MvPolynomial.C (Ideal.Quotient.mk (I.comap jetInclude) s) :=
    specialize_jetInclude _ s
  rw [← hs] at hm
  change jetInclude s ∈ (I.map (reduceJets I)).comap (reduceJets I) at hm
  rw [Ideal.comap_map_of_surjective _ (reduce_surjective I), ← RingHom.ker_eq_comap_bot, reduce_kernel,
    sup_eq_left.mpr (image_le I)] at hm
  exact (nonZeroDivisors.ne_zero hd) (Ideal.Quotient.eq_zero_iff_mem.mpr hm)
theorem fibre_prime (I : Ideal Ambient) [I.IsPrime] : (I.map (imageFibreMap I)).IsPrime := by
  have : (I.comap jetInclude).IsPrime := Ideal.IsPrime.comap jetInclude
  have hp : (I.map (reduceJets I)).IsPrime :=
    Ideal.map_isPrime_of_surjective (reduce_surjective I) (reduce_kernel I ▸ image_le I)
  rw [fibre_comp, ← Ideal.map_map]
  exact IsLocalization.isPrime_of_isPrime_disjoint (fibreDenominators I) (GenericFibre I)
    _ hp (disjoint_denominators I)
theorem fibre_comap (I : Ideal Ambient) [I.IsPrime] :
    (I.map (imageFibreMap I)).comap (imageFibreMap I) = I := by
  have : (I.comap jetInclude).IsPrime := Ideal.IsPrime.comap jetInclude
  have hp : (I.map (reduceJets I)).IsPrime :=
    Ideal.map_isPrime_of_surjective (reduce_surjective I) (reduce_kernel I ▸ image_le I)
  have hu := IsLocalization.under_map_of_isPrime_disjoint (fibreDenominators I)
    (GenericFibre I) hp (disjoint_denominators I)
  rw [Ideal.under_def] at hu
  rw [fibre_comp, ← Ideal.map_map, ← Ideal.comap_comap, hu,
    Ideal.comap_map_of_surjective _ (reduce_surjective I), ← RingHom.ker_eq_comap_bot, reduce_kernel,
    sup_eq_left.mpr (image_le I)]
theorem image_ne_bot (I : Ideal Ambient) (hI : Active I) (hd : ¬ dual I) :
    jetImageIdeal I ≠ ⊥ := by
  have : I.IsPrime := hI.prime
  intro hJ
  let S := Seeds⁰.map (MvPolynomial.C (σ := Fin 2))
  let e := seedPresentation.toRingHom
  have hdisj : Disjoint (S : Set (MvPolynomial (Fin 2) Seeds)) (I.map e : Set _) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ h
    rw [← show e (jetInclude s) = MvPolynomial.C s from RingHom.congr_fun presentation_jetInclude s] at h
    change jetInclude s ∈ (I.map e).comap e at h
    rw [Ideal.comap_map_of_bijective e seedPresentation.bijective] at h
    have hj : jetInclude s ∈ jetImageIdeal I := by
      rw [jetImageIdeal, imageIdeal_eq]
      exact Ideal.mem_map_of_mem jetInclude h
    have hz : jetInclude s = 0 := Ideal.mem_bot.mp (hJ ▸ hj)
    have hinj : Function.Injective jetInclude := MvPolynomial.rename_injective _ (Fin.natAdd_injective 2 2)
    exact nonZeroDivisors.ne_zero hs (hinj (hz.trans (map_zero jetInclude).symm))
  have he : mapGenericJets = (algebraMap (MvPolynomial (Fin 2) Seeds) FibreRing).comp e := by
    rw [mapGenericJets_eq]
    rfl
  have hp : (I.map e).IsPrime := by
    exact Ideal.map_isPrime_of_surjective (f := e) seedPresentation.surjective (by
      rw [(RingHom.injective_iff_ker_eq_bot e).mp seedPresentation.injective]
      exact bot_le)
  have hprime : (I.map mapGenericJets).IsPrime := by
    rw [he, ← Ideal.map_map]
    exact IsLocalization.isPrime_of_isPrime_disjoint S FibreRing _ hp hdisj
  have : Nontrivial (OverJets I) := Ideal.Quotient.nontrivial_iff.mpr hprime.ne_top
  have := hI.jet_finite
  exact hd Module.finrank_pos
theorem fibre_height_le_one (I : Ideal Ambient) (hI : Active I) (hd : ¬ dual I) :
    (I.map (imageFibreMap I)).height ≤ 1 := by
  have : I.IsPrime := hI.prime
  have : (I.comap jetInclude).IsPrime := Ideal.IsPrime.comap jetInclude
  let F := imageFibreMap I
  let J := I.map F
  have hprime : J.IsPrime := fibre_prime I
  let E : Ideal (GenericFibre I) ↪o Ideal Ambient :=
    (IsLocalization.orderEmbedding (fibreDenominators I) (GenericFibre I)).comp
      (Ideal.orderEmbeddingOfSurjective (reduceJets I) (reduce_surjective I))
  have hE (P : Ideal (GenericFibre I)) : E P = P.comap F := by
    change (P.comap (algebraMap (Reduction I) (GenericFibre I))).comap (reduceJets I) =
      P.comap (imageFibreMap I)
    rw [Ideal.comap_comap, fibre_comp]
  rw [show (I.map (imageFibreMap I)).height = Order.height (⟨J, hprime⟩ : PrimeSpectrum _) from
    PrimeSpectrum.height_eq_orderHeight ⟨J, hprime⟩]
  by_contra! hh
  obtain ⟨P, Q, hQP, hPJ⟩ := Order.one_lt_height_iff.mp hh
  have : (E Q.asIdeal).IsPrime := (hE Q.asIdeal).symm ▸ Ideal.comap_isPrime F Q.asIdeal
  have : (E P.asIdeal).IsPrime := (hE P.asIdeal).symm ▸ Ideal.comap_isPrime F P.asIdeal
  have hQP' : E Q.asIdeal < E P.asIdeal := E.strictMono (show Q.asIdeal < P.asIdeal from hQP)
  have hPI : E P.asIdeal < I := by
    have h := E.strictMono (show P.asIdeal < J from hPJ)
    rwa [hE J, fibre_comap I] at h
  have hQ : (⊥ : Ideal Ambient) < E Q.asIdeal := by
    refine (bot_lt_iff_ne_bot.mpr (image_ne_bot I hI hd)).trans_le ?_
    rw [hE, show F = imageFibreMap I from rfl, fibre_comp, ← Ideal.comap_comap,
      ← reduce_kernel, RingHom.ker_eq_comap_bot]
    exact Ideal.comap_mono bot_le
  have hdim : ringKrullDim Ambient = 4 := by simp [Ambient, ringKrullDim_eq_zero_of_field]
  have hbad : (5 : WithBot ℕ∞) ≤ 4 := calc
    5 = ((ringKrullDim (CoordinateRing I) + 1) + 1) + 1 := by rw [hI.dimension]; decide
    _ ≤ (ringKrullDim (Ambient ⧸ E P.asIdeal) + 1) + 1 :=
      add_le_add (add_le_add (Ideal.ringKrullDim_quotient_succ_le_of_lt hPI) le_rfl) le_rfl
    _ ≤ ringKrullDim (Ambient ⧸ E Q.asIdeal) + 1 :=
      add_le_add (Ideal.ringKrullDim_quotient_succ_le_of_lt hQP') le_rfl
    _ ≤ ringKrullDim (Ambient ⧸ (⊥ : Ideal Ambient)) :=
      Ideal.ringKrullDim_quotient_succ_le_of_lt hQ
    _ = 4 := (RingEquiv.quotientBot Ambient).ringKrullDim.trans hdim
  exact (by decide : ¬ (5 : WithBot ℕ∞) ≤ 4) hbad
theorem fibre_principal (I : Ideal Ambient) (hI : Active I) (hd : ¬ dual I)
    (hne : I.map (imageFibreMap I) ≠ ⊥) :
    ∃ g : GenericFibre I, I.map (imageFibreMap I) = Ideal.span {g} := by
  have : I.IsPrime := hI.prime
  have : (I.comap jetInclude).IsPrime := Ideal.IsPrime.comap jetInclude
  have : UniqueFactorizationMonoid (JetImageField I) := PrincipalIdealRing.to_uniqueFactorizationMonoid
  have : UniqueFactorizationMonoid (GenericFibre I) := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  have := fibre_prime I
  have hlt : (⊥ : Ideal (GenericFibre I)) < I.map (imageFibreMap I) := bot_lt_iff_ne_bot.mpr hne
  have hlo : 1 ≤ (I.map (imageFibreMap I)).height := by
    simpa only [Ideal.height_bot, zero_add] using Ideal.height_add_one_le_of_lt_of_isPrime hlt
  exact (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
    (le_antisymm (fibre_height_le_one I hI hd) hlo)).principal
end
end K1_14_2_2_4_3_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_4_3_1
noncomputable section
open K1_14 K1_14_2 K1_14_2_2_4_3 Polynomial
private def lastEquiv (n : ℕ) :
    Polynomial (MvPolynomial (Fin n) FX) ≃+* MvPolynomial (Fin (n + 1)) FX :=
  (MvPolynomial.optionEquivLeft FX (Fin n)).symm.toRingEquiv.trans
    (MvPolynomial.renameEquiv FX (finSuccEquivLast (n := n)).symm).toRingEquiv
private theorem lastEquiv_X (n : ℕ) :
    lastEquiv n Polynomial.X = MvPolynomial.X (Fin.last n) := by
  change MvPolynomial.rename _ ((MvPolynomial.optionEquivLeft FX (Fin n)).symm Polynomial.X) = _
  simp
private theorem lastEquiv_C (n : ℕ) (x : MvPolynomial (Fin n) FX) :
    lastEquiv n (C x) = MvPolynomial.rename Fin.castSucc x := by
  have h : (MvPolynomial.optionEquivLeft FX (Fin n)).symm (C x) =
      MvPolynomial.rename some x := by
    change (Polynomial.aevalTower (MvPolynomial.rename some) (MvPolynomial.X none)) (C x) = _
    simp
  change MvPolynomial.rename _ ((MvPolynomial.optionEquivLeft FX (Fin n)).symm (C x)) = _
  have he : (finSuccEquivLast (n := n)).symm ∘ some = Fin.castSucc := by
    funext i
    simp
  rw [h, MvPolynomial.rename_rename, he]
private theorem castLE_succ (n : ℕ) :
    (Fin.castLE (Nat.le_succ n) : Fin n → Fin (n + 1)) = Fin.castSucc := by
  funext i
  apply Fin.ext
  rfl
private def jetEquiv : Jet ≃+* Ambient :=
  (Polynomial.mapEquiv (lastEquiv 2)).trans (lastEquiv 3)
theorem jetEquiv_toRingHom : jetEquiv.toRingHom = toJet := by
  have hroot : (lastEquiv 2).toRingHom = toRoot := by
    apply Polynomial.ringHom_ext
    · intro x
      simpa [toRoot, rootSeeds, castLE_succ] using lastEquiv_C 2 x
    · simpa [toRoot, Polynomial.coe_eval₂RingHom] using lastEquiv_X 2
  apply Polynomial.ringHom_ext
  · intro x
    change lastEquiv 3 ((C x).map (lastEquiv 2).toRingHom) = toJet (C x)
    rw [Polynomial.map_C, lastEquiv_C, hroot]
    simp [toJet, rootIncl, castLE_succ]
  · change lastEquiv 3 (Polynomial.X.map (lastEquiv 2).toRingHom) = toJet Polynomial.X
    rw [Polynomial.map_X, lastEquiv_X]
    simp [toJet]
attribute [local instance] Polynomial.algebra in
theorem generators_of_contraction {R T : Type*} [CommRing R] [CommRing T]
    (P : Ideal R[X]) [P.IsPrime] (f : R) (hf : P.comap C = Ideal.span {f})
    (b : R[X] →+* T) (hb : ∀ x ∉ P, IsUnit (b x)) :
    ∃ t, P.map b = Ideal.span {b (C f), t} := by
  let q := P.comap C
  let Rq := Localization.AtPrime q
  let M := q.primeCompl.map (C : R →+* R[X])
  let g : R[X] →+* Rq[X] := algebraMap R[X] Rq[X]
  have : IsLocalization M Rq[X] := Polynomial.isLocalization q.primeCompl Rq
  let J := P.map g
  have hdisjoint : Disjoint (M : Set R[X]) (P : Set R[X]) := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  let : J.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M Rq[X] P inferInstance hdisjoint
  have hqspan : q.map (algebraMap R Rq) = Ideal.span {algebraMap R Rq f} := by
    change (P.comap C).map _ = _
    rw [hf, Ideal.map_span, Set.image_singleton]
  have hm : IsLocalRing.maximalIdeal Rq = Ideal.span {algebraMap R Rq f} :=
    (IsLocalization.AtPrime.map_eq_maximalIdeal q Rq).symm.trans hqspan
  have hCg : g (C f) = C (algebraMap R Rq f) := by
    change (C f).map (algebraMap R Rq) = _
    rw [Polynomial.map_C]
  have hfP : C f ∈ P := by
    change f ∈ P.comap C
    rw [hf]
    exact Ideal.mem_span_singleton_self f
  have hcontract : J.comap C = IsLocalRing.maximalIdeal Rq := by
    refine le_antisymm (IsLocalRing.le_maximalIdeal_of_isPrime (J.comap C)) ?_
    rw [hm, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, ← hCg]
    exact Ideal.mem_map_of_mem g hfP
  have hbase : (J.comap C).map C = Ideal.span {g (C f)} := by
    rw [hcontract, hm, Ideal.map_span, Set.image_singleton, hCg]
  obtain ⟨v, hv⟩ : ∃ v : Rq[X], J = Ideal.span {g (C f), v} := by
    by_cases he : J = (J.comap C).map C
    · exact ⟨0, by rw [he, hbase, Ideal.span_pair_zero]⟩
    · have hmax : (J.comap C).IsMaximal :=
        hcontract.symm ▸ IsLocalRing.maximalIdeal.isMaximal Rq
      obtain ⟨v, _, hv⟩ := Polynomial.exists_monic_span_sup_map_eq Rq J hmax he
      exact ⟨v, by rw [hv, hbase, Ideal.span_insert]⟩
  have hu : ∀ y : M, IsUnit (b y) := by
    rintro ⟨_, x, hx, rfl⟩
    exact hb _ hx
  let l := IsLocalization.lift (S := Rq[X]) hu
  have hl (x : R[X]) : l (g x) = b x := IsLocalization.lift_eq hu x
  have hcomp : l.comp g = b := RingHom.ext hl
  refine ⟨l v, ?_⟩
  calc
    P.map b = J.map l := by
      change P.map b = (P.map g).map l
      rw [Ideal.map_map, hcomp]
    _ = Ideal.span {b (C f), l v} := by
      rw [hv, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, hl]
theorem proof : K1_14_2_2_4_3.c1 := by
  intro I hI f _ hirr _ _ hcon
  let : I.IsPrime := hI.prime
  let a := parentLocalMap I
  change Prime (a (ordinaryIncl f)) ∧ ∃ t, I.map a = Ideal.span {a (ordinaryIncl f), t}
  have he : jetEquiv.toRingHom.comp (C : Equation →+* Jet) = ordinaryIncl := by
    rw [jetEquiv_toRingHom, ordinaryIncl]
  have heval : jetEquiv (C f) = ordinaryIncl f := RingHom.congr_fun he f
  have hfPrime : Prime f := by
    apply (Ideal.span_singleton_prime hirr.ne_zero).mp
    rw [← hcon]
    infer_instance
  have hfAmbient : Prime (ordinaryIncl f) := by
    rw [← heval]
    exact (MulEquiv.prime_iff jetEquiv).mpr (Polynomial.prime_C_iff.mpr hfPrime)
  have hle : Ideal.span {ordinaryIncl f} ≤ I := by
    rw [Ideal.span_singleton_le_iff_mem]
    change f ∈ I.comap ordinaryIncl
    rw [hcon]
    exact Ideal.mem_span_singleton_self f
  have hprime : Prime (a (ordinaryIncl f)) := by
    have hne : a (ordinaryIncl f) ≠ 0 := by
      simpa only [a, map_zero] using
        (IsLocalization.injective (ParentLocal I) I.primeCompl_le_nonZeroDivisors).ne
          hfAmbient.ne_zero
    apply (Ideal.span_singleton_prime hne).mp
    rw [← Set.image_singleton, ← Ideal.map_span]
    have : (Ideal.span {ordinaryIncl f}).IsPrime :=
      (Ideal.span_singleton_prime hfAmbient.ne_zero).mpr hfAmbient
    exact Ideal.isPrime_map_of_isLocalizationAtPrime I hle
  refine ⟨hprime, ?_⟩
  let P := I.comap jetEquiv.toRingHom
  let b := a.comp jetEquiv.toRingHom
  have hp : P.comap C = Ideal.span {f} := by
    change (I.comap jetEquiv.toRingHom).comap C = _
    rw [Ideal.comap_comap, he, hcon]
  have hb (x : Jet) (hx : x ∉ P) : IsUnit (b x) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (ParentLocal I) I (jetEquiv x)).mpr hx
  obtain ⟨t, ht⟩ := generators_of_contraction P f hp b hb
  refine ⟨t, ?_⟩
  have hmap : P.map b = I.map a := by
    change P.map (a.comp jetEquiv.toRingHom) = _
    rw [← Ideal.map_map]
    congr 1
    exact Ideal.map_comap_of_surjective jetEquiv.toRingHom jetEquiv.surjective I
  rw [← hmap, ht]
  change Ideal.span {a (jetEquiv (C f)), t} = _
  rw [heval]
end
end K1_14_2_2_4_3_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace K1_14_2_2_4_3_2
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_3 K1_14_2_2_4_3
open MvPolynomial
open scoped Polynomial
private def seedView : Equation ≃ₐ[FX] MvPolynomial (Fin 2) FX[X] :=
  (optionEquivLeft FX (Fin 2)).symm.trans (optionEquivRight FX (Fin 2))
private theorem seedView_C (a : Seeds) : seedView (Polynomial.C a) = map Polynomial.C a := by
  have h : seedView.toRingHom.comp (Polynomial.C : Seeds →+* Equation) =
      map (Polynomial.C : FX →+* FX[X]) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [seedView, optionEquivLeft_symm_C_C]
    · intro i
      simp [seedView, optionEquivLeft_symm_C_X]
  exact RingHom.congr_fun h a
private theorem seedView_X : seedView Polynomial.X = C (Polynomial.X : FX[X]) := by
  simp [seedView, optionEquivLeft_symm_X]
private theorem seedView_coeff (f : Equation) (j : ℕ) (d : Fin 2 →₀ ℕ) :
    ((seedView f).coeff d).coeff j = (f.coeff j).coeff d := by
  change ((optionEquivRight FX (Fin 2) ((optionEquivLeft FX (Fin 2)).symm f)).coeff d).coeff j = _
  rw [optionEquivRight_coeff_coeff, ← optionEquivLeft_coeff_coeff]
  simp
theorem seedView_degree_le (f : Equation) :
    (seedView f).totalDegree ≤ K1_14_2_2_4.seedDegree f := by
  rw [totalDegree, Finset.sup_le_iff]
  intro d hd
  obtain ⟨j, hj⟩ := Polynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp hd)
  rw [Polynomial.mem_support_iff, seedView_coeff, ← MvPolynomial.mem_support_iff] at hj
  have hle := le_totalDegree hj
  exact hle.trans (Finset.le_sup (f := fun j => (f.coeff j).totalDegree)
    (Polynomial.mem_support_iff.mpr (fun hz => MvPolynomial.mem_support_iff.mp hj (by simp [hz]))))
def ordinateSeed : FX[X] →+* Seeds :=
  Polynomial.eval₂RingHom C (MvPolynomial.X 0)
theorem ordinateSeed_include : jetInclude.comp ordinateSeed = ordinateIncl := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [ordinateSeed, ordinateIncl, jetInclude]
  · simp [ordinateSeed, ordinateIncl, jetInclude]
theorem specialize_ordinary {A : Type*} [CommRing A] (q : Seeds →+* A) (f : Equation) :
    specializeJets q (ordinaryIncl f) = map (q.comp ordinateSeed) (seedView f) := by
  have hs : (specializeJets q).comp (rootIncl.comp rootSeeds) =
      MvPolynomial.map (q.comp MvPolynomial.C) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rootIncl, rootSeeds, specializeJets]
    · intro i
      simp only [RingHom.comp_apply, rootIncl, rootSeeds, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, MvPolynomial.rename_X, MvPolynomial.map_X]
      exact specialize_seed_var q i
  have ho : (specializeJets q).comp ordinaryIncl =
      (map (q.comp ordinateSeed)).comp seedView.toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, ordinaryIncl_apply, toJet, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C]
      change specializeJets q (rootIncl (toRoot (Polynomial.C a))) =
        map (q.comp ordinateSeed) (seedView (Polynomial.C a))
      rw [seedView_C, map_map]
      have hc : (q.comp ordinateSeed).comp (Polynomial.C : FX →+* FX[X]) = q.comp C := by
        ext c
        simp [ordinateSeed]
      rw [hc]
      simpa only [RingHom.comp_apply, toRoot, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C] using
        RingHom.congr_fun hs a
    · simp only [RingHom.comp_apply, ordinaryIncl_apply, toJet, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C]
      change specializeJets q (rootIncl (toRoot Polynomial.X)) =
        map (q.comp ordinateSeed) (seedView Polynomial.X)
      rw [seedView_X, map_C]
      simp only [toRoot, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, rootIncl,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.rename_X,
        RingHom.comp_apply, ordinateSeed]
      rw [show Fin.castLE (by decide : 3 ≤ 4) (2 : Fin 3) = Fin.natAdd 2 (0 : Fin 2) from rfl]
      exact specialize_jet_var q 0
  exact RingHom.congr_fun ho f
private theorem ordinate_injective (I : Ideal Ambient) (hI : Active I) :
    Function.Injective ((jetImageMap I).comp ordinateSeed) := by
  have : I.IsPrime := hI.prime
  have : (I.comap jetInclude).IsPrime := Ideal.IsPrime.comap jetInclude
  refine (IsFractionRing.injective (JetImageRing I) (JetImageField I)).comp ?_
  change Function.Injective ((Ideal.Quotient.mk (I.comap jetInclude)).comp ordinateSeed)
  rw [injective_iff_map_eq_zero]
  intro f hf
  have hm : ordinateSeed f ∈ I.comap jetInclude := Ideal.Quotient.eq_zero_iff_mem.mp hf
  change jetInclude (ordinateSeed f) ∈ I at hm
  rw [← RingHom.comp_apply, ordinateSeed_include] at hm
  exact (injective_iff_map_eq_zero _).mp hI.ordinate_dominant f
    (Ideal.Quotient.eq_zero_iff_mem.mpr hm)
theorem separant (I : Ideal Ambient) (hI : Active I) (f : Equation) (hf : f ≠ 0)
    (hdeg : K1_14_2_2_4.seedDegree f < p) (hcontract : I.comap ordinaryIncl = Ideal.span {f}) :
    ∃ i : Fin 2, pderiv i (imageFibreMap I (ordinaryIncl f)) ∉ I.map (imageFibreMap I) := by
  have : I.IsPrime := hI.prime
  have : (I.comap jetInclude).IsPrime := Ideal.IsPrime.comap jetInclude
  let F := imageFibreMap I
  let P := I.map F
  have hP : P.IsPrime := fibre_prime I
  let v := seedView f
  let e := (jetImageMap I).comp ordinateSeed
  have hv : v ≠ 0 := map_ne_zero_iff seedView seedView.injective |>.mpr hf
  have hfe (a : Equation) : F (ordinaryIncl a) = map e (seedView a) :=
    specialize_ordinary (jetImageMap I) a
  have hfI : ordinaryIncl f ∈ I := by
    change f ∈ I.comap ordinaryIncl
    rw [hcontract]
    exact Ideal.mem_span_singleton_self f
  have hvars : v.vars.Nonempty := by
    by_contra! h
    have hc := vars_eq_empty_iff_eq_C.mp h
    have hn : v.coeff 0 ≠ 0 := fun hz => hv (by rw [hc, hz, map_zero])
    have hu : IsUnit (F (ordinaryIncl f)) := by
      rw [hfe f, ← show v = seedView f from rfl, hc, map_C]
      exact (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff e (ordinate_injective I hI)).mpr hn)).map C
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem F hfI) hu)
  obtain ⟨i, hi⟩ := hvars
  have hi' : 0 < v.degreeOf i := Nat.pos_of_ne_zero (mem_vars_iff_degreeOf_ne_zero.mp hi)
  have hlt : v.degreeOf i < p :=
    ((degreeOf_le_totalDegree v i).trans (seedView_degree_le f)).trans_lt hdeg
  let : CharP FX p := charP_of_injective_ringHom seedEmbedding.injective p
  let : CharP FX[X] p :=
    charP_of_injective_ringHom (Polynomial.C_injective (R := FX)) p
  have hcast : (v.degreeOf i : FX[X]) ≠ 0 := by
    intro h
    exact (not_le_of_gt hlt) (Nat.le_of_dvd hi' ((CharP.cast_eq_zero_iff _ _ _).mp h))
  have hn := pderiv_ne_zero_of_natCast_ne_zero i v hcast
  have hb := degreeOf_pderiv_le_sub_one i v
  let g := seedView.symm (pderiv i v)
  have hg : seedView g = pderiv i v := seedView.apply_symm_apply _
  refine ⟨i, ?_⟩
  intro hm
  change pderiv i (F (ordinaryIncl f)) ∈ P at hm
  rw [hfe, show seedView f = v from rfl, pderiv_map, ← hg, ← hfe] at hm
  change ordinaryIncl g ∈ P.comap F at hm
  rw [fibre_comap I] at hm
  change g ∈ I.comap ordinaryIncl at hm
  rw [hcontract, Ideal.mem_span_singleton] at hm
  obtain ⟨k, hk⟩ := hm
  have heq : pderiv i v = v * seedView k := by simpa only [hk, map_mul] using hg.symm
  have hkn : seedView k ≠ 0 := fun hz => hn (by rw [heq, hz, mul_zero])
  rw [heq, degreeOf_mul_eq hv hkn] at hb
  omega
end
end K1_14_2_2_4_3_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace K1_14_2_2_4_3_2
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_3 K1_14_2_2_4_3
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem proof : K1_14_2_2_4_3.c2 := by
  intro I hI f hd hf _ hdeg hcontract
  let : I.IsPrime := hI.prime
  let : (I.comap jetInclude).IsPrime := Ideal.IsPrime.comap jetInclude
  dsimp only
  let a := parentLocalMap I
  letI : CommRing (JetQuotient I) := Ideal.Quotient.commRing ((jetImageIdeal I).map a)
  let q := jetQuotientMap I
  let φ := q.comp a
  let F := imageFibreMap I
  let P := I.map F
  have hF : F = (algebraMap (Reduction I) (GenericFibre I)).comp (reduceJets I) :=
    fibre_comp I
  have hfi : ordinaryIncl f ∈ I := by
    change f ∈ I.comap ordinaryIncl
    rw [hcontract]
    exact Ideal.mem_span_singleton_self f
  have hfe : F (ordinaryIncl f) ∈ P := Ideal.mem_map_of_mem F hfi
  obtain ⟨i, hi⟩ := separant I hI f hf.ne_zero hdeg hcontract
  have hnonzero : F (ordinaryIncl f) ≠ 0 := by
    intro hz
    apply hi
    rw [hz, map_zero]
    exact P.zero_mem
  have hP : P ≠ ⊥ := fun he => hnonzero (Ideal.mem_bot.mp (he ▸ hfe))
  obtain ⟨g, hg⟩ := fibre_principal I hI hd hP
  change P = Ideal.span {g} at hg
  obtain ⟨b, hb⟩ : g ∣ F (ordinaryIncl f) := Ideal.mem_span_singleton.mp (hg ▸ hfe)
  have hbP : b ∉ P := by
    intro h
    apply hi
    change MvPolynomial.pderiv i (F (ordinaryIncl f)) ∈ P
    rw [hb, MvPolynomial.pderiv_mul]
    have hgP : g ∈ P := hg.symm ▸ Ideal.mem_span_singleton_self g
    exact P.add_mem (P.mul_mem_left _ h) (P.mul_mem_right _ hgP)
  have : (jetImageIdeal I).IsPrime := by
    rw [← reduce_kernel]
    exact RingHom.ker_isPrime _
  have : ((jetImageIdeal I).map a).IsPrime :=
    Ideal.isPrime_map_of_isLocalizationAtPrime (S := ParentLocal I) I (image_le I)
  have : IsDomain (JetQuotient I) := Ideal.Quotient.isDomain _
  have hker : RingHom.ker φ = jetImageIdeal I := by
    change RingHom.ker ((Ideal.Quotient.mk ((jetImageIdeal I).map a)).comp a) = _
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    exact Ideal.under_map_of_isLocalizationAtPrime (S := ParentLocal I) I (image_le I)
  have hf' : φ (ordinaryIncl f) ≠ 0 := by
    intro hzero
    have hm := RingHom.mem_ker.mpr hzero
    rw [hker, ← reduce_kernel] at hm
    exact hnonzero (by rw [hF, RingHom.comp_apply, RingHom.mem_ker.mp hm, map_zero])
  change Function.Injective (fun x : JetQuotient I => φ (ordinaryIncl f) * x) ∧
    (I.map a).map q = Ideal.span {φ (ordinaryIncl f)}
  refine ⟨fun _ _ h => mul_left_cancel₀ hf' h, ?_⟩
  have hunit (x : Ambient) (hx : x ∉ I) : IsUnit (φ x) :=
    ((IsLocalization.AtPrime.isUnit_to_map_iff (ParentLocal I) I x).mpr hx).map q
  let φ₀ : Reduction I →+* JetQuotient I :=
    (reduceJets I).liftOfSurjective (reduce_surjective I) ⟨φ, by rw [hker, reduce_kernel]⟩
  have hφ₀ (x : Ambient) : φ₀ (reduceJets I x) = φ x :=
    RingHom.liftOfSurjective_comp_apply _ _ _ _
  have hu (s : fibreDenominators I) : IsUnit (φ₀ s) := by
    obtain ⟨d, hd, hds⟩ := s.property
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := I.comap jetInclude) d
    have hs : (s : Reduction I) = reduceJets I (jetInclude y) := by
      rw [← hds, reduceJets, specialize_jetInclude]
    rw [hs, hφ₀]
    exact hunit _ (fun hy => nonZeroDivisors.ne_zero hd (Ideal.Quotient.eq_zero_iff_mem.mpr hy))
  let l := IsLocalization.lift (S := GenericFibre I) (P := JetQuotient I) hu
  have hl (y : Ambient) : l (F y) = φ y := by
    rw [hF, RingHom.comp_apply]
    exact (IsLocalization.lift_eq (S := GenericFibre I) (P := JetQuotient I) hu _).trans (hφ₀ y)
  have hbunit : IsUnit (l b) := by
    obtain ⟨n, s, hs⟩ := IsLocalization.exists_mk'_eq (fibreDenominators I) b
    obtain ⟨x, rfl⟩ := reduce_surjective I n
    have hx : x ∉ I := by
      intro h
      apply hbP
      rw [← hs, IsLocalization.mk'_mem_iff]
      have hfx := Ideal.mem_map_of_mem F h
      change F x ∈ P at hfx
      rwa [hF, RingHom.comp_apply] at hfx
    have heq : l b * l (algebraMap (Reduction I) (GenericFibre I) s) = φ x := by
      rw [← map_mul, ← hs, IsLocalization.mk'_spec]
      exact (congrArg l (RingHom.congr_fun hF x).symm).trans (hl x)
    exact isUnit_of_mul_isUnit_left (heq.symm ▸ hunit x hx)
  have hφ : l.comp F = φ := RingHom.ext hl
  rw [Ideal.map_map, show q.comp a = l.comp F from hφ.symm, ← Ideal.map_map]
  change P.map l = _
  rw [hg, Ideal.map_span, Set.image_singleton, ← hl, hb, map_mul,
    Ideal.span_singleton_mul_right_unit hbunit]
end
end K1_14_2_2_4_3_2
end
section
namespace K1_13_7_1_1_1_2
noncomputable section
open K1_13_6 K1_13_7_1_1_1 K1_13_6_2_4_1 MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
abbrev Grid := ℕ × Grades
def multigrade (a : Grid) : Grade :=
  Finsupp.equivFunOnFinite.symm (Fin.snoc a.2 a.1)
def gridOf (t : Grade) : Grid :=
  (t (Fin.last 4), fun i => t i.castSucc)
@[simp] theorem multigrade_castSucc (a : Grid) (i : Fin 4) :
    multigrade a i.castSucc = a.2 i := by simp [multigrade]
@[simp] theorem multigrade_last (a : Grid) : multigrade a (Fin.last 4) = a.1 := by
  simp only [multigrade, Finsupp.coe_equivFunOnFinite_symm, Fin.snoc_last]
theorem multigrade_add (a v : Grid) : multigrade (a + v) = multigrade a + multigrade v := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [multigrade_last, Finsupp.add_apply, Prod.fst_add]
  · simp
@[simp] theorem multigrade_gridOf (t : Grade) : multigrade (gridOf t) = t := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · exact multigrade_last _
  · exact multigrade_castSucc _ _
def advance (i : Fin 4) : Grid := (0, Pi.single i 1)
@[simp] theorem multigrade_advance (i : Fin 4) :
    multigrade (advance i) = unitGrade i.castSucc := by
  ext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · rw [multigrade_last, unitGrade, Finsupp.single_apply, ite_eq_right (Fin.castSucc_ne_last i)]
    rfl
  · by_cases he : i = k <;> simp [advance, unitGrade, he, eq_comm]
def supportIn (A : Fin 4 → Set Exponent) (B : Set Exponent) : Fin 5 → Set Exponent :=
  Fin.snoc A B
@[simp] theorem supportIn_last (A : Fin 4 → Set Exponent) (B : Set Exponent) :
    supportIn A B (Fin.last 4) = B := by simp only [supportIn, Fin.snoc_last]
@[simp] theorem supportIn_castSucc (A : Fin 4 → Set Exponent) (B : Set Exponent) (i : Fin 4) :
    supportIn A B i.castSucc = A i := Fin.snoc_castSucc _ _ _
abbrev Generator (A : Fin 4 → Set Exponent) (B : Set Exponent) :=
  (j : Fin 5) × supportIn A B j
abbrev SectionRing (A : Fin 4 → Set Exponent) (B : Set Exponent) :=
  MvPolynomial (Generator A B) GeoField
abbrev slot (A : Fin 4 → Set Exponent) (B : Set Exponent) : Generator A B → Fin 5 :=
  Sigma.fst
theorem finite_generator {A : Fin 4 → Set Exponent} {B : Set Exponent}
    (hAB : admissible A B) : Finite (Generator A B) := by
  have (j : Fin 5) : Finite (supportIn A B j) := by
    apply Set.Finite.to_subtype
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [supportIn_last] using hAB.2.1
    · simpa only [supportIn_castSucc] using (hAB.1 i).1
  infer_instance
def dehom (A : Fin 4 → Set Exponent) (B : Set Exponent) : SectionRing A B →ₐ[GeoField] GeoJets :=
  aeval fun v => monomial v.2.val 1
def liftIdeal (A : Fin 4 → Set Exponent) (B : Set Exponent)
    (J : Ideal GeoJets) : Ideal (SectionRing A B) :=
  ((J.comap (dehom A B)).homogeneousCore (piece (slot A B))).toIdeal
def rankAt {σ : Type} (s : σ → Fin 5) (J : Ideal (MvPolynomial σ GeoField))
    (a : Grid) : ℝ :=
  gradedHilbert s J (multigrade a)
def difference (dirs : List (Fin 4)) (H : Grid → ℝ) (a : Grid) : ℝ :=
  gradeDifferences dirs 1 (fun w => H (a.1, w)) a.2
end
end K1_13_7_1_1_1_2
end
section
namespace K1_13_7_1_1_1_2
noncomputable section
open K1_13_6 K1_13_6_3_6 K1_13_6_2_4_1 MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
theorem homogeneous_cut_exact {σ : Type} [Finite σ] (s : σ → Fin 5)
    (J : Ideal (MvPolynomial σ GeoField)) (hJ : J.IsHomogeneous (piece s))
    (e : Grade) (g : MvPolynomial σ GeoField) (hg : g ∈ piece s e) :
    (J ⊔ Ideal.span {g}).IsHomogeneous (piece s) ∧
      ∀ t : Grade, gradedHilbert s (J ⊔ Ideal.span {g}) (t + e) +
        gradedHilbert s (J.colon {g}) t = gradedHilbert s J (t + e) := by
  have hspan : (Ideal.span {g}).IsHomogeneous (piece s) :=
    Ideal.homogeneous_span _ _ (by
      intro x hx
      obtain rfl : x = g := hx
      exact ⟨e, hg⟩)
  refine ⟨hJ.sup hspan, ?_⟩
  intro t
  let K := J ⊔ Ideal.span {g}
  let A := J.colon {g}
  let q := Ideal.Quotient.factorₐ GeoField (show J ≤ K from le_sup_left)
  let cut : quotientPiece s J (t + e) →ₗ[GeoField] quotientPiece s K (t + e) :=
    (q.toLinearMap.domRestrict _).codRestrict _ fun y => by
      obtain ⟨b, hb, hby⟩ := y.property
      exact ⟨b, hb, by simpa [q] using congrArg q hby⟩
  have hsurj : Function.Surjective cut := by
    intro y
    obtain ⟨b, hb, hby⟩ := y.property
    exact ⟨⟨Ideal.Quotient.mk J b, ⟨b, hb, rfl⟩⟩, Subtype.ext (by simpa [cut, q] using hby)⟩
  let mu := (quotientMul J g).restrictScalars GeoField
  let emb : quotientPiece s A t →ₗ[GeoField] quotientPiece s J (t + e) :=
    (mu.domRestrict _).codRestrict _ fun y => by
      obtain ⟨b, hb, hby⟩ := y.property
      have hbg : b * g ∈ piece s (t + e) :=
        IsWeightedHomogeneous.mul hb hg
      refine ⟨b * g, hbg, ?_⟩
      change Ideal.Quotient.mk J (b * g) = mu y.val
      change Ideal.Quotient.mk A b = y.val at hby
      rw [← hby]
      exact (quotientMul_mk J g b).symm
  have hInj : Function.Injective emb := fun y z h =>
    Subtype.ext (quotientMul_injective J g (congrArg Subtype.val h))
  have hker : LinearMap.ker cut = LinearMap.range emb := by
    ext y
    obtain ⟨b, hb, hby⟩ := y.property
    have hy : y = ⟨Ideal.Quotient.mk J b, ⟨b, hb, rfl⟩⟩ := Subtype.ext hby.symm
    rw [hy, LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hz
      have hkb : b ∈ K := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        simpa [cut, q] using congrArg Subtype.val hz
      obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp hkb
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      let m := weightedHomogeneousComponent (slotWeight s) t d
      have hm : m ∈ piece s t := weightedHomogeneousComponent_mem _ _ _
      have ha' := weightedHomogeneousComponent_mem_of_mem _ _ hJ ha (t + e)
      have hb' : b.IsWeightedHomogeneous (slotWeight s) (t + e) := hb
      have hdecomp := congrArg (weightedHomogeneousComponent (slotWeight s) (t + e)) hac
      rw [map_add, component_mul_of_grade s hg, weightedHomogeneousComponent_eq_self hb'] at hdecomp
      refine ⟨⟨Ideal.Quotient.mk A m, ⟨m, hm, rfl⟩⟩, Subtype.ext ?_⟩
      change quotientMul J g (Ideal.Quotient.mk A m) = Ideal.Quotient.mk J b
      rw [quotientMul_mk, ← hdecomp, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha', zero_add]
    · rintro ⟨z, hz⟩
      obtain ⟨a, _, haz⟩ := z.property
      apply Subtype.ext
      change Ideal.Quotient.mk K b = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hm : a * g ∈ K :=
        Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩)
      have he := congrArg Subtype.val hz
      change mu z.val = Ideal.Quotient.mk J b at he
      rw [← haz] at he
      change quotientMul J g (Ideal.Quotient.mk A a) = Ideal.Quotient.mk J b at he
      rw [quotientMul_mk, Ideal.Quotient.eq] at he
      have hsub : a * g - (a * g - b) ∈ K := K.sub_mem hm ((show J ≤ K from le_sup_left) he)
      rwa [sub_sub_cancel] at hsub
  have hrank := cut.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker, LinearMap.finrank_range_of_inj hInj] at hrank
  exact hrank
end
end K1_13_7_1_1_1_2
end
section
namespace K1_13_7_1_1_1_2
noncomputable section
open K1_13_6 K1_13_7_1_1_1 K1_13_6_2_4_1 MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {A : Fin 4 → Set Exponent} {B : Set Exponent}
theorem liftIdeal_homogeneous (J : Ideal GeoJets) :
    (liftIdeal A B J).IsHomogeneous (piece (slot A B)) :=
  ((J.comap (dehom A B)).homogeneousCore (piece (slot A B))).isHomogeneous
theorem liftIdeal_mono {J K : Ideal GeoJets} (h : J ≤ K) :
    liftIdeal A B J ≤ liftIdeal A B K :=
  Ideal.homogeneousCore_mono _ (Ideal.comap_mono h)
theorem mem_liftIdeal_of_piece {J : Ideal GeoJets} {g : SectionRing A B} {t : Grade}
    (hg : g ∈ piece (slot A B) t) : g ∈ liftIdeal A B J ↔ dehom A B g ∈ J := by
  constructor
  · intro h
    exact Ideal.toIdeal_homogeneousCore_le (piece (slot A B)) (J.comap (dehom A B)) h
  · intro h
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨t, hg⟩ h
theorem cut_le_lift {J K : Ideal GeoJets} (hJK : J ≤ K) {g : SectionRing A B} {t : Grade}
    (hg : g ∈ piece (slot A B) t) (h : dehom A B g ∈ K) :
    liftIdeal A B J ⊔ Ideal.span {g} ≤ liftIdeal A B K :=
  sup_le (liftIdeal_mono hJK) ((Ideal.span_singleton_le_iff_mem _).mpr
    ((mem_liftIdeal_of_piece hg).mpr h))
theorem liftIdeal_colon {J K : Ideal GeoJets} {g : SectionRing A B} {t : Grade}
    (hg : g ∈ piece (slot A B) t)
    (h : ∀ x : GeoJets, x * dehom A B g ∈ J ↔ x ∈ K) :
    (liftIdeal A B J).colon {g} = liftIdeal A B K := by
  have hc : ((liftIdeal A B J).colon {g}).IsHomogeneous (piece (slot A B)) := by
    intro v a ha
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at ha ⊢
    have hp : (DirectSum.decompose (piece (slot A B)) a v : SectionRing A B) =
        weightedHomogeneousComponent (slotWeight (slot A B)) v a :=
      weightedDecomposition.decompose'_apply GeoField (slotWeight (slot A B)) a v
    rw [hp, ← component_mul_of_grade (slot A B) hg a v]
    exact weightedHomogeneousComponent_mem_of_mem _ _ (liftIdeal_homogeneous J) ha _
  ext a
  rw [mem_iff_weightedHomogeneousComponent_mem _ _ hc,
    mem_iff_weightedHomogeneousComponent_mem _ _ (liftIdeal_homogeneous K)]
  apply forall_congr'
  intro v
  let z := weightedHomogeneousComponent (slotWeight (slot A B)) v a
  have hz : z ∈ piece (slot A B) v := weightedHomogeneousComponent_mem _ _ _
  have hzg : z * g ∈ piece (slot A B) (v + t) := IsWeightedHomogeneous.mul hz hg
  change z ∈ (liftIdeal A B J).colon {g} ↔ z ∈ liftIdeal A B K
  rw [Submodule.mem_colon_singleton, smul_eq_mul, mem_liftIdeal_of_piece hzg,
    mem_liftIdeal_of_piece hz, map_mul, h]
theorem exists_slot_lift (j : Fin 5) (f : GeoJets)
    (hf : (f.support : Set Exponent) ⊆ supportIn A B j) :
    ∃ g : SectionRing A B, g ∈ piece (slot A B) (unitGrade j) ∧ dehom A B g = f := by
  classical
  let gen (m : f.support) : Generator A B := ⟨j, ⟨m, hf m.property⟩⟩
  refine ⟨∑ m : f.support, C (f.coeff m) * MvPolynomial.X (gen m), ?_, ?_⟩
  · apply Submodule.sum_mem
    intro m _
    exact (isWeightedHomogeneous_X GeoField (slotWeight (slot A B)) (gen m)).C_mul _
  · simp only [map_sum, map_mul, dehom, aeval_C, algebraMap_eq, aeval_X,
      C_mul_monomial, mul_one, gen]
    rw [Finset.sum_coe_sort f.support (fun m => monomial m (f.coeff m))]
    exact f.support_sum_monomial_coeff
theorem exists_affine_lift (hAB : admissible A B) (f : GeoJets) :
    ∃ t : Grade, ∃ g : SectionRing A B, g ∈ piece (slot A B) t ∧ dehom A B g = f := by
  let j := Fin.last 4
  let u : Generator A B := ⟨j, ⟨0, by simpa only [j, supportIn_last] using hAB.2.2.1⟩⟩
  let v (i : Fin 4) : Generator A B :=
    ⟨j, ⟨Finsupp.single i 1, by simpa only [j, supportIn_last] using hAB.2.2.2 i⟩⟩
  have hu : dehom A B (MvPolynomial.X u) = 1 := by simp [dehom, u]
  have hv (i : Fin 4) : dehom A B (MvPolynomial.X (v i)) = MvPolynomial.X i := by
    rw [dehom, aeval_X]
    rfl
  have hex :
      ∃ n : ℕ, ∃ g : SectionRing A B,
        g ∈ piece (slot A B) (n • unitGrade j) ∧ dehom A B g = f := by
    induction f using MvPolynomial.induction_on with
    | C r =>
        refine ⟨0, C r, ?_, by simp [dehom]⟩
        simpa only [mem_weightedHomogeneousSubmodule, zero_nsmul] using isWeightedHomogeneous_C (slotWeight (slot A B)) r
    | add p q hp hq =>
        obtain ⟨n, g, hg, hgm⟩ := hp
        obtain ⟨m, h, hh, hhm⟩ := hq
        let x : SectionRing A B := MvPolynomial.X u
        have hx : x.IsWeightedHomogeneous (slotWeight (slot A B)) (unitGrade j) :=
          isWeightedHomogeneous_X GeoField _ _
        refine ⟨n + m, g * x ^ m + h * x ^ n, Submodule.add_mem _ ?_ ?_, ?_⟩
        · simpa only [mem_weightedHomogeneousSubmodule, add_nsmul] using IsWeightedHomogeneous.mul hg (hx.pow m)
        · simpa only [mem_weightedHomogeneousSubmodule, add_nsmul, Nat.add_comm n m] using IsWeightedHomogeneous.mul hh (hx.pow n)
        · simp [x, hu, hgm, hhm]
    | mul_X p i hp =>
        obtain ⟨n, g, hg, hgm⟩ := hp
        have hx : (MvPolynomial.X (v i) : SectionRing A B).IsWeightedHomogeneous
            (slotWeight (slot A B)) (unitGrade j) := isWeightedHomogeneous_X GeoField _ _
        refine ⟨n + 1, g * MvPolynomial.X (v i), ?_, by rw [map_mul, hgm, hv]⟩
        simpa only [mem_weightedHomogeneousSubmodule, add_nsmul, one_nsmul] using IsWeightedHomogeneous.mul hg hx
  obtain ⟨n, g, hg, hm⟩ := hex
  exact ⟨_, g, hg, hm⟩
abbrev cut (P : Ideal GeoJets) (f : GeoJets) : Ideal GeoJets := P ⊔ Ideal.span {f}
theorem cut_self_mem (P : Ideal GeoJets) (f : GeoJets) : f ∈ cut P f :=
  (le_sup_right : Ideal.span {f} ≤ cut P f) (Ideal.mem_span_singleton_self _)
theorem cut_sq_le (P : Ideal GeoJets) (f : GeoJets) : cut P (f ^ 2) ≤ cut P f := by
  refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
  exact (pow_two f).symm ▸ (cut P f).mul_mem_right f (cut_self_mem P f)
theorem square_colon {P : Ideal GeoJets} {f : GeoJets} (hp : P.IsPrime) (hf : f ∉ P)
    (a : GeoJets) : a * f ∈ cut P (f ^ 2) ↔ a ∈ cut P f := by
  constructor
  · intro ha
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ha
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hy
    have he : (a - c * f) * f = x := by
      rw [sub_mul, ← hxy, ← hc]
      ring
    have hm : a - c * f ∈ P := (hp.mem_or_mem (he.symm ▸ hx)).resolve_right hf
    exact Submodule.mem_sup.mpr
      ⟨a - c * f, hm, c * f, Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩, sub_add_cancel _ _⟩
  · intro ha
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    exact Submodule.mem_sup.mpr ⟨x * f, P.mul_mem_right f hx, c * f * f,
      Ideal.mem_span_singleton'.mpr ⟨c, by ring⟩, by rw [← add_mul, hxy]⟩
def intersection (Q : Finset (Ideal GeoJets)) : Ideal GeoJets := Q.inf id
theorem separating_element {I q : Ideal GeoJets} {Q : Finset (Ideal GeoJets)}
    (hq : I.IsMinimalPrime q) (hQ : ∀ r ∈ Q, I.IsMinimalPrime r) (hn : q ∉ Q) :
    ∃ f ∈ intersection Q, f ∉ q := by
  apply SetLike.not_le_iff_exists.mp
  intro hle
  obtain ⟨r, hr, hrq⟩ := hq.isPrime.inf_le'.mp hle
  have he : r = q := le_antisymm hrq (hq.2 (hQ r hr).1 hrq)
  exact hn (he ▸ hr)
theorem intersection_insert (q : Ideal GeoJets) (Q : Finset (Ideal GeoJets))
    [DecidableEq (Ideal GeoJets)] : intersection (insert q Q) = q ⊓ intersection Q := by
  simp [intersection]
theorem separator_colon {q J : Ideal GeoJets} {f : GeoJets}
    (hq : q.IsPrime) (hf : f ∉ q) (hJ : f ∈ J) (a : GeoJets) :
    a * f ∈ q ⊓ J ↔ a ∈ q := by
  constructor
  · intro h
    exact (hq.mem_or_mem ((Ideal.mem_inf.mp h).1)).resolve_right hf
  · intro h
    exact Ideal.mem_inf.mpr ⟨q.mul_mem_right f h, J.mul_mem_left a hJ⟩
end
end K1_13_7_1_1_1_2
end
section
namespace K1_13_7_1_1_1_2
noncomputable section
open K1_13_6 K1_13_7_1_1_1 K1_13_6_2_4_1 MvPolynomial Filter
open scoped BigOperators
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def c1 : Prop :=
  ∀ {σ : Type} [Finite σ] (s : σ → Fin 5) (I J : Ideal (MvPolynomial σ GeoField)),
    I.IsHomogeneous (piece s) → J.IsHomogeneous (piece s) → I ≤ J →
      ∀ k : ℕ, ∀ᶠ a in (atTop : Filter Grid),
        0 ≤ difference (remainingDirections k) (fun x => rankAt s I x - rankAt s J x) a
def c2 : Prop :=
  ∀ (A : Fin 4 → Set Exponent) (B : Set Exponent), admissible A B →
    ∀ (P : Ideal GeoJets) (a : Grid),
      rankAt (slot A B) (liftIdeal A B P) a = hilbert A B P a.1 a.2
theorem difference_cons (i : Fin 4) (dirs : List (Fin 4)) (H : Grid → ℝ) (a : Grid) :
    difference (i :: dirs) H a = difference dirs (fun x => H (x + advance i) - H x) a := rfl
private theorem difference_sub (dirs : List (Fin 4)) (H K : Grid → ℝ) (a : Grid) :
    difference dirs (fun x => H x - K x) a = difference dirs H a - difference dirs K a := by
  induction dirs generalizing H K with
  | nil => rfl
  | cons i dirs ih =>
      simp only [difference_cons]
      rw [show (fun x => (H (x + advance i) - K (x + advance i)) - (H x - K x)) =
        (fun x => (H (x + advance i) - H x) - (K (x + advance i) - K x)) by
          funext x; ring]
      exact ih _ _
theorem difference_shift (dirs : List (Fin 4)) (H : Grid → ℝ) (a v : Grid) :
    difference dirs (fun x => H (x + v)) a = difference dirs H (a + v) := by
  induction dirs generalizing H with
  | nil => rfl
  | cons i dirs ih =>
      simp only [difference_cons, add_right_comm _ (advance i) v]
      exact ih (fun x => H (x + advance i) - H x)
theorem difference_zero (dirs : List (Fin 4)) (a : Grid) :
    difference dirs (fun _ => 0) a = 0 := by
  induction dirs with
  | nil => rfl
  | cons i dirs ih => simpa only [difference_cons, sub_self] using ih
private theorem eventually_shift {F : Grid → Prop} (v : Grid)
    (h : ∀ᶠ a in atTop, F a) : ∀ᶠ a in atTop, F (a + v) := by
  obtain ⟨u, hu⟩ := eventually_atTop.mp h
  exact eventually_atTop.mpr ⟨u, fun a ha => hu (a + v)
    (ha.trans (le_add_of_nonneg_right zero_le))⟩
theorem eventually_unshift {F : Grid → Prop} (v : Grid)
    (h : ∀ᶠ a in atTop, F (a + v)) : ∀ᶠ a in atTop, F a := by
  obtain ⟨u, hu⟩ := eventually_atTop.mp h
  refine eventually_atTop.mpr ⟨u + v, fun a ha => ?_⟩
  obtain ⟨b, rfl⟩ := exists_add_of_le ha
  have hb := hu (u + b) (le_add_of_nonneg_right zero_le)
  rwa [add_right_comm] at hb
theorem mixed_stable (hr : c2) {A : Fin 4 → Set Exponent} {B : Set Exponent}
    (hAB : admissible A B) {P : Ideal GeoJets} {k : ℕ} {d : ℝ}
    (hd : IsMixedDegree A B P k d) :
    ∀ᶠ a in (atTop : Filter Grid),
      difference (remainingDirections k) (rankAt (slot A B) (liftIdeal A B P)) a = d := by
  obtain ⟨N, hN⟩ := hd
  refine eventually_atTop.mpr ⟨(N, fun _ => N), fun a ha => ?_⟩
  have he : rankAt (slot A B) (liftIdeal A B P) = fun x => hilbert A B P x.1 x.2 :=
    funext (hr A B hAB P)
  rw [he, difference]
  simpa only [Nat.cast_one, one_pow, one_mul] using hN a.1 a.2 1 ha.1 ha.2
theorem rankAt_top {σ : Type} (s : σ → Fin 5) :
    rankAt s (⊤ : Ideal (MvPolynomial σ GeoField)) = fun _ => 0 := by
  funext a
  have : Subsingleton (MvPolynomial σ GeoField ⧸ (⊤ : Ideal (MvPolynomial σ GeoField))) :=
    (Ideal.Quotient.subsingleton_iff).mpr rfl
  simp [rankAt, gradedHilbert, Module.finrank_eq_zero_of_subsingleton]
theorem liftIdeal_top (A : Fin 4 → Set Exponent) (B : Set Exponent) :
    liftIdeal A B (⊤ : Ideal GeoJets) = ⊤ := by
  rw [liftIdeal, show (⊤ : Ideal GeoJets).comap (dehom A B) = ⊤ from Ideal.comap_top]
  exact (show (⊤ : Ideal (SectionRing A B)).IsHomogeneous (piece (slot A B)) from
    fun _ _ _ => Submodule.mem_top).toIdeal_homogeneousCore_eq_self
theorem difference_mono (hpos : c1) {σ : Type} [Finite σ]
    (s : σ → Fin 5) {I J : Ideal (MvPolynomial σ GeoField)}
    (hI : I.IsHomogeneous (piece s)) (hJ : J.IsHomogeneous (piece s)) (hIJ : I ≤ J) (k : ℕ) :
    ∀ᶠ a in (atTop : Filter Grid),
      difference (remainingDirections k) (rankAt s J) a ≤
        difference (remainingDirections k) (rankAt s I) a := by
  filter_upwards [hpos s I J hI hJ hIJ k] with a ha
  rw [difference_sub] at ha
  exact sub_nonneg.mp ha
private theorem spend (hpos : c1) {σ : Type} [Finite σ] (s : σ → Fin 5)
    {I J L : Ideal (MvPolynomial σ GeoField)}
    (hI : I.IsHomogeneous (piece s)) (hJ : J.IsHomogeneous (piece s))
    (v : Grid) {g : MvPolynomial σ GeoField} (hg : g ∈ piece s (multigrade v))
    (hcol : I.colon {g} = L) (hle : I ⊔ Ideal.span {g} ≤ J) (k : ℕ) :
    ∀ᶠ a in (atTop : Filter Grid),
      difference (remainingDirections k) (rankAt s J) (a + v) +
          difference (remainingDirections k) (rankAt s L) a ≤
        difference (remainingDirections k) (rankAt s I) (a + v) := by
  obtain ⟨hcut, hex⟩ := homogeneous_cut_exact s I hI (multigrade v) g hg
  let D := remainingDirections k
  have he : (fun a => rankAt s (I ⊔ Ideal.span {g}) (a + v)) =
      fun a => rankAt s I (a + v) - rankAt s L a := by
    funext a
    have hn := hex (multigrade a)
    rw [hcol] at hn
    simp only [rankAt, multigrade_add]
    exact eq_sub_of_add_eq (by exact_mod_cast hn)
  have hm := eventually_shift v (difference_mono hpos s hcut hJ hle k)
  filter_upwards [hm] with a ha
  have hd :
      difference D (rankAt s (I ⊔ Ideal.span {g})) (a + v) =
        difference D (rankAt s I) (a + v) - difference D (rankAt s L) a := by
    rw [← difference_shift D (rankAt s (I ⊔ Ideal.span {g})), he, difference_sub, difference_shift]
  change difference D (rankAt s J) (a + v) ≤ _ at ha
  rw [hd] at ha
  exact le_sub_iff_add_le.mp ha
theorem selected_components (hpos : c1) (hr : c2)
    {A : Fin 4 → Set Exponent} {B : Set Exponent} (hAB : admissible A B)
    (I : Ideal GeoJets) (k : ℕ) (e : Ideal GeoJets → ℝ)
    (Q : Finset (Ideal GeoJets)) (hQ : ∀ q ∈ Q, I.IsMinimalPrime q)
    (he : ∀ q ∈ Q, IsMixedDegree A B q k (e q)) :
    ∀ᶠ a in (atTop : Filter Grid),
      ∑ q ∈ Q, e q ≤
        difference (remainingDirections k) (rankAt (slot A B) (liftIdeal A B I)) a := by
  classical
  have : Finite (Generator A B) := finite_generator hAB
  let R := rankAt (slot A B) ∘ liftIdeal A B
  let D := remainingDirections k
  have hcomp (S : Finset (Ideal GeoJets)) (hS : ∀ q ∈ S, I.IsMinimalPrime q)
      (hdeg : ∀ q ∈ S, IsMixedDegree A B q k (e q)) :
      ∀ᶠ a in (atTop : Filter Grid), ∑ q ∈ S, e q ≤ difference D (R (intersection S)) a := by
    induction S using Finset.induction_on with
    | empty =>
        simp [intersection, R, liftIdeal_top, rankAt_top, difference_zero]
    | insert q S hq ih =>
        have hhead := hS q (Finset.mem_insert_self _ _)
        have htail r hr := hS r (Finset.mem_insert_of_mem hr)
        obtain ⟨f, hfS, hfq⟩ := separating_element hhead htail hq
        obtain ⟨t, g, hg, hgm⟩ := exists_affine_lift hAB f
        let v := gridOf t
        have hg' : g ∈ piece (slot A B) (multigrade v) := by simpa [v] using hg
        have hl : (liftIdeal A B (q ⊓ intersection S)).colon {g} = liftIdeal A B q :=
          liftIdeal_colon hg fun x => by rw [hgm]; exact separator_colon hhead.isPrime hfq hfS x
        have hle : liftIdeal A B (q ⊓ intersection S) ⊔ Ideal.span {g} ≤
            liftIdeal A B (intersection S) := cut_le_lift inf_le_right hg (by rwa [hgm])
        have hcut := spend hpos (slot A B) (liftIdeal_homogeneous _) (liftIdeal_homogeneous _)
          v hg' hl hle k
        have hi := eventually_shift v (ih htail (fun r hr => hdeg r (Finset.mem_insert_of_mem hr)))
        have hqdeg := mixed_stable hr hAB (hdeg q (Finset.mem_insert_self _ _))
        apply eventually_unshift v
        filter_upwards [hcut, hi, hqdeg] with a ha hs hd
        rw [Finset.sum_insert hq, intersection_insert]
        change difference D (R (intersection S)) (a + v) + difference D (R q) a ≤
          difference D (R (q ⊓ intersection S)) (a + v) at ha
        change difference D (R q) a = e q at hd
        linarith
  have hle : I ≤ intersection Q := Finset.le_inf fun q hq => (hQ q hq).le
  have hm := difference_mono hpos (slot A B) (liftIdeal_homogeneous I)
    (liftIdeal_homogeneous (intersection Q)) (liftIdeal_mono hle) k
  filter_upwards [hcomp Q hQ he, hm] with a ha hb using ha.trans hb
theorem remaining_succ (i : Fin 4) :
    remainingDirections i.val = i :: remainingDirections (i.val + 1) := by
  fin_cases i <;> rfl
theorem of_children (hpos : c1) (hr : c2) : K1_13_7_1_1_1.c2 := by
  classical
  intro A B hAB i P hp _ f hf hs Q hQ d e hd he
  have : Finite (Generator A B) := finite_generator hAB
  let R := rankAt (slot A B) ∘ liftIdeal A B
  let k := i.val + 1
  let D := remainingDirections k
  let v := advance i
  obtain ⟨g, hg, hgm⟩ := exists_slot_lift (A := A) (B := B) i.castSucc (f ^ 2)
    (by simpa [supportIn] using hs)
  have hg' : g ∈ piece (slot A B) (multigrade v) := by simpa [v] using hg
  have hgcol : (liftIdeal A B P).colon {g} = liftIdeal A B P := by
    apply liftIdeal_colon hg
    intro x
    rw [hgm, pow_two]
    exact ⟨fun hx => (hp.mem_or_mem hx).resolve_right
      (fun h => hf ((hp.mem_or_mem h).elim id id)), P.mul_mem_right _⟩
  have hgle : liftIdeal A B P ⊔ Ideal.span {g} ≤ liftIdeal A B (cut P (f ^ 2)) :=
    cut_le_lift le_sup_left hg (by rw [hgm]; exact cut_self_mem P (f ^ 2))
  have hfirst := spend hpos (slot A B) (liftIdeal_homogeneous _) (liftIdeal_homogeneous _)
    v hg' hgcol hgle k
  obtain ⟨t, u, hu, hum⟩ := exists_affine_lift hAB f
  let z := gridOf t
  have hu' : u ∈ piece (slot A B) (multigrade z) := by simpa [z] using hu
  have hucol : (liftIdeal A B (cut P (f ^ 2))).colon {u} = liftIdeal A B (cut P f) :=
    liftIdeal_colon hu fun x => by rw [hum]; exact square_colon hp hf x
  have hule : liftIdeal A B (cut P (f ^ 2)) ⊔ Ideal.span {u} ≤ liftIdeal A B (cut P f) :=
    cut_le_lift (cut_sq_le P f) hu (by rw [hum]; exact cut_self_mem P f)
  have hsecond := spend hpos (slot A B) (liftIdeal_homogeneous _) (liftIdeal_homogeneous _)
    z hu' hucol hule k
  have hsel := selected_components hpos hr hAB (cut P f) k e Q hQ he
  have hparent := mixed_stable hr hAB hd
  have hbudget : ∀ᶠ a in (atTop : Filter Grid), 2 * ∑ q ∈ Q, e q ≤ d := by
    filter_upwards [eventually_shift z hfirst, eventually_shift v hsecond,
      eventually_shift v hsel, eventually_shift (v + z) hsel, eventually_shift z hparent]
      with a h₁ h₂ hb hc h₀
    change difference D (R (cut P (f ^ 2))) (a + z + v) + difference D (R P) (a + z) ≤
      difference D (R P) (a + z + v) at h₁
    change difference D (R (cut P f)) (a + v + z) + difference D (R (cut P f)) (a + v) ≤
      difference D (R (cut P (f ^ 2))) (a + v + z) at h₂
    change difference (remainingDirections i.val) (R P) (a + z) = d at h₀
    rw [remaining_succ, difference_cons, difference_sub, difference_shift] at h₀
    rw [add_right_comm a z v] at h₁ h₀
    rw [← add_assoc a v z] at hc
    change ∑ q ∈ Q, e q ≤ difference D (R (cut P f)) (a + v) at hb
    change ∑ q ∈ Q, e q ≤ difference D (R (cut P f)) (a + v + z) at hc
    change difference D (R P) (a + v + z) - difference D (R P) (a + z) = d at h₀
    linarith only [h₁, h₂, hb, hc, h₀]
  obtain ⟨_, hb⟩ := hbudget.exists
  exact hb
end
end K1_13_7_1_1_1_2
end
section
set_option autoImplicit false
namespace K1_13_7_1_1_1_2_2
noncomputable section
open K1_13_6 K1_13_6_2_4_1 K1_13_7_1_1_1 K1_13_7_1_1_1_2 MvPolynomial
open scoped BigOperators Pointwise
variable {A : Fin 4 → Set Exponent} {B : Set Exponent}
private abbrev affineWeight (A : Fin 4 → Set Exponent) (B : Set Exponent) :
    (Generator A B →₀ ℕ) →+ Exponent :=
  Finsupp.weight fun v : Generator A B => v.2.val
abbrev supportWeight (A : Fin 4 → Set Exponent) (B : Set Exponent) :
    Grade →+ Set Exponent :=
  Finsupp.weight (supportIn A B)
theorem supportWeight_unit (j : Fin 5) :
    supportWeight A B (unitGrade j) = supportIn A B j := by
  rw [unitGrade, Finsupp.weight_single, one_nsmul]
theorem supportWeight_multigrade (a : Grid) :
    supportWeight A B (multigrade a) = gradedExponents A B a.1 a.2 := by
  rw [Finsupp.weight_eq_sum, Fin.sum_univ_castSucc]
  simp only [multigrade_castSucc, supportIn_castSucc, multigrade_last, supportIn_last,
    Fin.sum_univ_four, gradedExponents]
  ac_rfl
theorem affineWeight_mem (e : Generator A B →₀ ℕ) :
    affineWeight A B e ∈ supportWeight A B (Finsupp.weight (slotWeight (slot A B)) e) := by
  induction e using Finsupp.induction_linear with
  | zero => simp
  | add e f he hf =>
      rw [map_add, map_add, map_add]
      exact Set.add_mem_add he hf
  | single v n =>
      rw [Finsupp.weight_single, Finsupp.weight_single, map_nsmul]
      change n • v.2.val ∈ n • supportWeight A B (unitGrade v.1)
      rw [supportWeight_unit]
      exact Set.nsmul_mem_nsmul v.2.property
theorem realize_slot (j : Fin 5) (n : ℕ) {m : Exponent}
    (hm : m ∈ n • supportIn A B j) :
    ∃ e : Generator A B →₀ ℕ,
      Finsupp.weight (slotWeight (slot A B)) e = n • unitGrade j ∧ affineWeight A B e = m := by
  induction n generalizing m with
  | zero =>
      have hm0 : m = 0 := by simpa using hm
      exact ⟨0, by simp, by simp [hm0]⟩
  | succ n ih =>
      rw [succ_nsmul] at hm ⊢
      obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.mp hm
      obtain ⟨e, he, hxe⟩ := ih hx
      let v : Generator A B := ⟨j, ⟨y, hy⟩⟩
      refine ⟨e + Finsupp.single v 1, ?_, ?_⟩
      · rw [map_add, he, Finsupp.weight_single, one_nsmul]
        rfl
      · rw [map_add, hxe, Finsupp.weight_single, one_nsmul]
theorem realize_grade (t : Grade) {m : Exponent} (hm : m ∈ supportWeight A B t) :
    ∃ e : Generator A B →₀ ℕ,
      Finsupp.weight (slotWeight (slot A B)) e = t ∧ affineWeight A B e = m := by
  induction t using Finsupp.induction_linear generalizing m with
  | zero =>
      have hm0 : m = 0 := by simpa using hm
      exact ⟨0, by simp, by simp [hm0]⟩
  | add t u ht hu =>
      rw [map_add] at hm
      obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.mp hm
      obtain ⟨e, he, hxe⟩ := ht hx
      obtain ⟨f, hf, hyf⟩ := hu hy
      exact ⟨e + f, by rw [map_add, he, hf], by rw [map_add, hxe, hyf]⟩
  | single j n =>
      rw [Finsupp.weight_single] at hm
      simpa only [unitGrade, Finsupp.smul_single_one] using realize_slot j n hm
theorem mem_gradedExponents (a : Grid) (m : Exponent) :
    m ∈ gradedExponents A B a.1 a.2 ↔
      ∃ e : Generator A B →₀ ℕ,
        Finsupp.weight (slotWeight (slot A B)) e = multigrade a ∧ affineWeight A B e = m := by
  rw [← supportWeight_multigrade a]
  refine ⟨realize_grade (multigrade a), ?_⟩
  rintro ⟨e, he, rfl⟩
  rw [← he]
  exact affineWeight_mem e
private theorem dehom_monomial_one (e : Generator A B →₀ ℕ) :
    dehom A B (monomial e 1) = monomial (affineWeight A B e) 1 := by
  induction e using Finsupp.induction_linear with
  | zero => simp [monomial_zero']
  | add e f he hf =>
      rw [← one_mul (1 : GeoField), ← monomial_mul_monomial, map_mul, he, hf,
        monomial_mul_monomial, one_mul, map_add]
  | single v n =>
      rw [← X_pow_eq_monomial, map_pow, dehom, aeval_X, monomial_pow, one_pow,
        Finsupp.weight_single]
theorem dehom_map_piece (a : Grid) :
    (piece (slot A B) (multigrade a)).map (dehom A B).toLinearMap =
      restrictSupport GeoField (gradedExponents A B a.1 a.2) := by
  rw [show piece (slot A B) (multigrade a) = restrictSupport GeoField
        {e | Finsupp.weight (slotWeight (slot A B)) e = multigrade a} from
      weightedHomogeneousSubmodule_eq_finsupp_supported _ _ _,
    restrictSupport_eq_span, restrictSupport_eq_span, Submodule.map_span]
  apply congrArg (Submodule.span GeoField)
  ext p
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
    refine ⟨affineWeight A B e, (mem_gradedExponents a _).2 ⟨e, he, rfl⟩, ?_⟩
    exact (dehom_monomial_one e).symm
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨e, he, rfl⟩ := (mem_gradedExponents a m).1 hm
    exact ⟨monomial e 1, ⟨e, he, rfl⟩, dehom_monomial_one e⟩
theorem proof : K1_13_7_1_1_1_2.c2 := by
  intro A B _ P a
  let S := piece (slot A B) (multigrade a)
  let q := (Ideal.Quotient.mkₐ GeoField (liftIdeal A B P)).toLinearMap.domRestrict S
  let p := (((Ideal.Quotient.mkₐ GeoField P).toLinearMap).comp
    (dehom A B).toLinearMap).domRestrict S
  have hk : LinearMap.ker q = LinearMap.ker p := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    change Ideal.Quotient.mk (liftIdeal A B P) x.val = 0 ↔
      Ideal.Quotient.mk P (dehom A B x.val) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem]
    exact mem_liftIdeal_of_piece x.property
  have hr := ((q.quotKerEquivRange.symm.trans (Submodule.quotEquivOfEq _ _ hk)).trans
    p.quotKerEquivRange).finrank_eq
  dsimp only [q, p] at hr
  rw [LinearMap.range_domRestrict, LinearMap.range_domRestrict, Submodule.map_comp,
    show S.map (dehom A B).toLinearMap = _ from dehom_map_piece a] at hr
  exact congrArg (fun n : ℕ => (n : ℝ)) hr
end
end K1_13_7_1_1_1_2_2
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_3_1
open K1_13 K1_13_6_2_4 K1_13_6_2_4_3
open scoped BigOperators Pointwise
theorem latticePoints_coords (a : Shape × ℕ) (e : Exponent) :
    e ∈ latticePoints a ↔
      e 0 + e 1 + e 2 + e 3 ≤ 2 * a.1.b ∧
      e 1 + 2 * e 2 + 3 * e 3 ≤ 2 * a.1.j ∧
      e 3 ≤ 2 * a.1.t ∧ e 4 ≤ 2 * a.2 := by
  change Allowed (a.1.scale 2, 2 * a.2) e ↔ _
  simp only [Allowed, Fin.sum_univ_four, Shape.scale]
  change (_ ∧ (0 * e 0 + 1 * e 1 + 2 * e 2 + 3 * e 3 ≤ _) ∧ _ ∧ _) ↔ _
  simp
theorem latticePoints_add (p q : Shape) (r s : ℕ) (hp : Chamber p) (hq : Chamber q) :
    latticePoints (p, r) + latticePoints (q, s) = latticePoints (p.plus q, r + s) := by
  ext e
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    simp only [latticePoints_coords, Shape.plus, Finsupp.add_apply] at *
    omega
  · intro he
    obtain ⟨hpb, hpj⟩ := hp
    obtain ⟨hqb, hqj⟩ := hq
    simp only [latticePoints_coords, Shape.plus] at he
    let z := min (e 3) (2 * p.t)
    let z' := e 3 - z
    have hz : z + z' = e 3 ∧ z ≤ 2 * p.t ∧ z' ≤ 2 * q.t := by dsimp [z, z']; omega
    let w := 2 * p.j - 3 * z
    let w' := 2 * q.j - 3 * z'
    have hw : w + 3 * z = 2 * p.j ∧ w' + 3 * z' = 2 * q.j := by
      dsimp [w, w']
      omega
    have hhalf : (w + w') / 2 = w / 2 + w' / 2 := by
      by_cases h : e 3 ≤ 2 * p.t
      · have hz' : z' = 0 := by dsimp [z, z']; omega
        omega
      · have hze : z = 2 * p.t := min_eq_right (by omega)
        omega
    let y := min (e 2) (w / 2)
    let y' := e 2 - y
    have hy : y + y' = e 2 ∧ 2 * y ≤ w ∧ 2 * y' ≤ w' := by dsimp [y, y']; omega
    let x := min (e 1) (w - 2 * y)
    let x' := e 1 - x
    have hx : x + x' = e 1 ∧ x + 2 * y ≤ w ∧ x' + 2 * y' ≤ w' := by
      dsimp [x, x']
      omega
    let u := min (e 0) (2 * p.b - (x + y + z))
    let u' := e 0 - u
    have hu : u + u' = e 0 ∧ u + x + y + z ≤ 2 * p.b ∧ u' + x' + y' + z' ≤ 2 * q.b := by
      dsimp [u, u']
      omega
    let v := min (e 4) (2 * r)
    let v' := e 4 - v
    have hv : v + v' = e 4 ∧ v ≤ 2 * r ∧ v' ≤ 2 * s := by dsimp [v, v']; omega
    let a : Exponent := Finsupp.equivFunOnFinite.symm ![u, x, y, z, v]
    let b : Exponent := Finsupp.equivFunOnFinite.symm ![u', x', y', z', v']
    refine ⟨a, (latticePoints_coords (p, r) a).2 ?_, b,
      (latticePoints_coords (q, s) b).2 ?_, ?_⟩
    · change u + x + y + z ≤ 2 * p.b ∧ x + 2 * y + 3 * z ≤ 2 * p.j ∧
        z ≤ 2 * p.t ∧ v ≤ 2 * r
      omega
    · change u' + x' + y' + z' ≤ 2 * q.b ∧ x' + 2 * y' + 3 * z' ≤ 2 * q.j ∧
        z' ≤ 2 * q.t ∧ v' ≤ 2 * s
      omega
    · ext i
      fin_cases i
      · exact hu.1
      · exact hx.1
      · exact hy.1
      · exact hz.1
      · exact hv.1
theorem latticePoints_zero : latticePoints (⟨0, 0, 0⟩, 0) = 0 := by
  ext e
  rw [latticePoints_coords, Set.mem_zero]
  constructor
  · rintro ⟨h, _, _, hlast⟩
    change e 0 + e 1 + e 2 + e 3 ≤ 0 at h
    change e 4 ≤ 0 at hlast
    have h0 : e 0 = 0 := by omega
    have h1 : e 1 = 0 := by omega
    have h2 : e 2 = 0 := by omega
    have h3 : e 3 = 0 := by omega
    have h4 : e 4 = 0 := by omega
    ext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  · rintro rfl
    simp
theorem sum_latticePoints {ι : Type*} (I : Finset ι) (A : ι → Shape × ℕ)
    (hA : ∀ i, Chamber (A i).1) :
    (∑ i ∈ I, latticePoints (A i)) = latticePoints
      (⟨∑ i ∈ I, (A i).1.b, ∑ i ∈ I, (A i).1.j, ∑ i ∈ I, (A i).1.t⟩, ∑ i ∈ I, (A i).2) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, latticePoints_zero]
  | insert i I hi ih =>
    have hI : Chamber ⟨∑ k ∈ I, (A k).1.b, ∑ k ∈ I, (A k).1.j, ∑ k ∈ I, (A k).1.t⟩ := by
      constructor
      · exact Finset.sum_le_sum fun k _ => (hA k).1
      · change 3 * (∑ k ∈ I, (A k).1.t) ≤ ∑ k ∈ I, (A k).1.j
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun k _ => (hA k).2
    simp only [Finset.sum_insert hi]
    rw [ih, latticePoints_add _ _ _ _ (hA i) hI]
    rfl
theorem nsmul_latticePoints (a : Shape × ℕ) (ha : Chamber a.1) (n : ℕ) :
    n • latticePoints a = latticePoints (scaleCap a n) := by
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul,
    scaleCap, Shape.scale] using
    sum_latticePoints (Finset.univ : Finset (Fin n)) (fun _ => a) (fun _ => ha)
private theorem chamber_scale (a : Shape × ℕ) (ha : Chamber a.1) (n : ℕ) :
    Chamber (scaleCap a n).1 := by
  refine ⟨Nat.mul_le_mul_left n ha.1, ?_⟩
  change 3 * (n * a.1.t) ≤ n * a.1.j
  rw [Nat.mul_left_comm 3 n]
  exact Nat.mul_le_mul_left n ha.2
theorem diagonal_eq_sum (B : Boxes) (t : Fin 5 → ℕ) :
    diagonalExponents B t = ∑ i, ∑ _j : Fin (t i), latticePoints (B i) := by
  classical
  ext e
  rw [Set.mem_fintype_sum]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨fun i => ∑ j, u i j, fun i => (Set.mem_fintype_sum _ _).2 ⟨u i, hu i, rfl⟩, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    have h (i : Fin 5) : ∃ u : Fin (t i) → Exponent,
        (∀ j, u j ∈ latticePoints (B i)) ∧ ∑ j, u j = v i := by
      obtain ⟨u, hu, hs⟩ := (Set.mem_fintype_sum _ _).1 (hv i)
      exact ⟨u, hu, hs⟩
    choose u hu hs using h
    exact ⟨u, hu, by simp only [hs]⟩
theorem proof : K1_13_6_2_4_3.c1 := by
  intro B hB t n
  have hdiag : diagonalExponents B t = latticePoints (sumCap B t) := calc
    _ = ∑ i, ∑ _j : Fin (t i), latticePoints (B i) := diagonal_eq_sum B t
    _ = ∑ i, latticePoints (scaleCap (B i) (t i)) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using
        nsmul_latticePoints (B i) (hB i) (t i)
    _ = latticePoints (sumCap B t) :=
      sum_latticePoints Finset.univ (fun i => scaleCap (B i) (t i))
        (fun i => chamber_scale (B i) (hB i) (t i))
  rw [hdiag]
  exact nsmul_latticePoints (sumCap B t) (sumCap_chamber B hB t) n
end K1_13_6_2_4_3_1
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_3_2
open K1_13 K1_13_6_2_3 K1_13_6_2_3_1 K1_13_6_2_4 Finset
open scoped BigOperators
noncomputable section
def flatSlices (b j : ℕ) :=
  Σ y : Fin (j + 1), Σ x : Fin (2 * j - 2 * y.val + 1),
    Fin (2 * b - (y.val + x.val) + 1)
def flatCapEquiv (p : Shape) (hb : p.j ≤ p.b) (ht : p.t = 0) :
    capExponents p ≃ flatSlices p.b p.j where
  toFun e := by
    have he := (cap_coords p e.val).mp e.property
    have hdeg := he.1
    have hweight := he.2.1
    have htop := he.2.2
    let y : Fin (p.j + 1) := ⟨e.val 2, by omega⟩
    let x : Fin (2 * p.j - 2 * y.val + 1) := ⟨e.val 1, by dsimp [y]; omega⟩
    exact ⟨y, x, ⟨e.val 0, by dsimp [y, x]; omega⟩⟩
  invFun a := by
    rcases a with ⟨y, x, u⟩
    have hy := y.isLt
    have hx := x.isLt
    have hu := u.isLt
    refine ⟨Finsupp.equivFunOnFinite.symm ![u.val, x.val, y.val, 0], (cap_coords p _).mpr ?_⟩
    change u.val + x.val + y.val + 0 ≤ 2 * p.b ∧
      x.val + 2 * y.val + 3 * 0 ≤ 2 * p.j ∧ 0 ≤ 2 * p.t
    omega
  left_inv e := by
    have hz : e.val 3 = 0 := by
      have h := ((cap_coords p e.val).mp e.property).2.2
      omega
    apply Subtype.ext
    ext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · exact hz.symm
  right_inv a := by
    rcases a with ⟨⟨y, hy⟩, ⟨x, hx⟩, ⟨u, hu⟩⟩
    rfl
private theorem sum_affine (a d : ℚ) (n : ℕ) :
    (∑ x ∈ range n, (a + d * (x : ℚ))) = n * a + d * n * ((n : ℚ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring
theorem zero_top_count (p : Shape) (hb : p.j ≤ p.b) (ht : p.t = 0) :
    ((capExponents p).ncard : ℚ) =
      ((p.j : ℚ) + 1) ^ 2 * (2 * (p.b : ℚ) + 1 - (p.j : ℚ)) := by
  classical
  let : Fintype (flatSlices p.b p.j) := by unfold flatSlices; infer_instance
  rw [← Nat.card_coe_set_eq, Nat.card_congr (flatCapEquiv p hb ht), Nat.card_eq_fintype_card]
  change (Fintype.card (Σ y : Fin (p.j + 1), Σ x : Fin (2 * p.j - 2 * y.val + 1),
    Fin (2 * p.b - (y.val + x.val) + 1)) : ℚ) = _
  simp only [Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
  rw [Fin.sum_univ_eq_sum_range (fun y => ∑ x : Fin (2 * p.j - 2 * y + 1),
    ((2 * p.b - (y + x.val) + 1 : ℕ) : ℚ))]
  calc
    _ = ∑ y ∈ range (p.j + 1),
        (2 * (p.b : ℚ) + 1 - p.j) * (2 * (p.j : ℚ) + 1 + (-2) * (y : ℚ)) := by
      apply sum_congr rfl
      intro y hy
      have hy' := mem_range.mp hy
      have hyj : 2 * y ≤ 2 * p.j := by omega
      rw [Fin.sum_univ_eq_sum_range (fun x => ((2 * p.b - (y + x) + 1 : ℕ) : ℚ))]
      calc
        _ = ∑ x ∈ range (2 * p.j - 2 * y + 1),
            (2 * (p.b : ℚ) - y + 1 + (-1) * (x : ℚ)) := by
          apply sum_congr rfl
          intro x hx
          have hx' := mem_range.mp hx
          have hxy : y + x ≤ 2 * p.b := by omega
          push_cast [Nat.cast_sub hxy]
          ring
        _ = _ := by
          rw [sum_affine]
          push_cast [Nat.cast_sub hyj]
          ring
    _ = _ := by
      rw [← mul_sum, sum_affine]
      push_cast
      ring
theorem lattice_degree (p : Shape) : (latticePolynomial p).natDegree ≤ 4 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  have hne (m : ℕ) (hm : m ≤ 4) : k ≠ m := by omega
  simp only [latticePolynomial, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C, ite_eq_right (hne 4 (by decide)), ite_eq_right (hne 3 (by decide)),
    ite_eq_right (hne 2 (by decide)), ite_eq_right (hne 1 (by decide)),
    ite_eq_right (hne 0 (by decide)), add_zero]
theorem proof : K1_13_6_2_4_3.c2 := by
  intro p hp
  refine ⟨latticePolynomial p, lattice_degree p, ?_, ?_⟩
  · rw [latticePolynomial_coeff]
    ring
  · intro n
    cases n with
    | zero =>
      rw [zero_top_count (p.scale 0) (by simp [Shape.scale]) (by simp [Shape.scale])]
      simp [latticePolynomial, Shape.scale]
    | succ n =>
      by_cases ht : p.t = 0
      · rw [zero_top_count (p.scale (n + 1)) (Nat.mul_le_mul_left _ hp.1)
          (by simp [Shape.scale, ht])]
        simp only [latticePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_C, Polynomial.eval_X, Shape.scale, volume32, ht, Nat.cast_zero, mul_zero]
        push_cast
        ring
      · exact latticePolynomial_eval p ⟨hp.1, hp.2, Nat.pos_of_ne_zero ht⟩ _ (Nat.succ_pos _)
end
end K1_13_6_2_4_3_2
end
section
set_option autoImplicit false
namespace K1_13_7_2_4_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 MvPolynomial
open scoped Polynomial
theorem jet_dimension (P : JetIdeal) [P.IsPrime] (hP : P.height = 2) :
    (affineHilbertPolynomial P).natDegree = 2 := by
  have hPne : P ≠ ⊥ := by
    intro he
    have hz := Ideal.height_eq_zero_iff_eq_bot.mpr he
    rw [hP] at hz
    exact (by decide : (2 : ℕ∞) ≠ 0) hz
  obtain ⟨f, hfP, hf⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hPne)
  have hf0 : f ≠ 0 := fun he => hf (he.symm ▸ Ideal.zero_mem _)
  have hfspan : Ideal.span {f} ≤ P := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfP)
  obtain ⟨D, hD, hDP⟩ := Ideal.exists_minimalPrimes_le hfspan
  let := hD.isPrime
  have hDne : D ≠ ⊥ := fun he => hf (he ▸ hD.le (Ideal.subset_span (by simp)))
  have hDheight : D.height = 1 :=
    le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ D hD)
      (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hDne))
  have hDlt : D < P := lt_of_le_of_ne hDP fun he => by
    rw [he, hP] at hDheight
    exact (by decide : (2 : ℕ∞) ≠ 1) hDheight
  obtain ⟨g, hgP, hgD⟩ := SetLike.exists_of_lt hDlt
  have hcut : (D ⊔ Ideal.span {g}).IsMinimalPrime P := by
    have hgspan : Ideal.span {g} ≤ P := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgP)
    refine ⟨⟨inferInstance, sup_le hDP hgspan⟩, ?_⟩
    intro J hJ hJP
    by_contra hPJ
    let : J.IsPrime := hJ.1
    have hgJ : g ∈ J :=
      (le_sup_right.trans hJ.2 : Ideal.span {g} ≤ J) (Ideal.subset_span (by simp))
    have hDJ : D < J :=
      lt_of_le_of_ne (le_sup_left.trans hJ.2) (fun he => hgD (he.symm ▸ hgJ))
    have hJheight : (2 : ℕ∞) ≤ J.height := by
      simpa only [hDheight, one_add_one_eq_two] using Ideal.height_add_one_le_of_lt_of_isPrime hDJ
    have hlt := Ideal.height_strict_mono_of_isPrime_of_isPrime (lt_of_le_not_ge hJP hPJ)
    rw [hP] at hlt
    exact (not_lt_of_ge hJheight) hlt
  have hDdeg := natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hf0 hD
  have hPdeg := principalCut_natDegree_affineHilbertPolynomial_add_one hgD hcut
  rw [Nat.card_fin] at hDdeg
  omega
private def componentScalars (P : JetIdeal) : GeoField →+* JetField P :=
  (onComponent P).comp MvPolynomial.C
def coefficientEval (P : JetIdeal) (U : (JetField P)[X]) :
    FreshCoeffRing →+* JetField P :=
  MvPolynomial.eval₂Hom (componentScalars P) (fun j => U.coeff j.val)
theorem coefficientEval_jetLinear (P : JetIdeal) [P.IsPrime] {U : (JetField P)[X]}
    (hd : U.natDegree < taylorLength) (i : ℕ) :
    coefficientEval P U (jetLinear genericArgument i) =
      (Polynomial.hasseDeriv i U).eval (componentScalars P genericArgument) := by
  have hsum : U = ∑ j : Fin taylorLength, Polynomial.monomial j.val (U.coeff j.val) := by
    rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => Polynomial.monomial n (U.coeff n))]
    exact U.as_sum_range' _ hd
  rw [congrArg (fun V => (Polynomial.hasseDeriv i V).eval (componentScalars P genericArgument)) hsum]
  simp only [jetLinear, map_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Polynomial.hasseDeriv_monomial, Polynomial.eval_monomial, map_mul, coefficientEval,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', map_natCast, map_pow]
  ring
theorem freshImage_le_source (P : JetIdeal) [P.IsPrime] (U : (JetField P)[X])
    (hd : U.natDegree < taylorLength)
    (hjet : ∀ i : Fin 4, (Polynomial.hasseDeriv i.val U).eval
      (onComponent P (MvPolynomial.C genericArgument)) = onComponent P (MvPolynomial.X i)) :
    freshImage (coefficientKernel (componentConstants P) U) ≤ P := by
  have hmap : (coefficientEval P U).comp (MvPolynomial.map geomConstants) =
      MvPolynomial.eval₂Hom (componentConstants P) (fun j : Fin taylorLength => U.coeff j.val) := by
    ext a <;> simp [coefficientEval, componentScalars, componentConstants]
  have hkill : extendIdeal (coefficientKernel (componentConstants P) U) ≤
      RingHom.ker (coefficientEval P U) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    exact (DFunLike.congr_fun hmap a).trans ha
  have hcomp : (coefficientEval P U).comp freshJetMap = onComponent P := by
    ext a
    · simp [coefficientEval, freshJetMap, componentScalars]
    · rw [RingHom.comp_apply, freshJetMap, MvPolynomial.eval₂Hom_X',
        coefficientEval_jetLinear P hd]
      exact hjet a
  intro a ha
  have hz : onComponent P a = 0 :=
    (DFunLike.congr_fun hcomp a).symm.trans (hkill ha)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply IsFractionRing.injective (GeoJets ⧸ P) (JetField P)
  exact hz.trans (map_zero _).symm
theorem image_dimension_le (A : CoeffIdeal) :
    (affineHilbertPolynomial (freshImage A)).natDegree ≤ (affineHilbertPolynomial A).natDegree := by
  let f : (GeoJets ⧸ freshImage A) →ₐ[GeoField] (FreshCoeffRing ⧸ extendIdeal A) :=
    Ideal.quotientMapₐ (extendIdeal A) K1_13_6_3_5.freshProjection (by intro p hp; exact hp)
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro x hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk (extendIdeal A) (freshJetMap p) = 0 at hx
    rw [Ideal.Quotient.eq_zero_iff_mem] at hx ⊢
    exact hx
  have h := natDegree_affineHilbertPolynomial_le_of_injective f hf
  let : Algebra Geom GeoField := geomConstants.toAlgebra
  have hbase : affineHilbertPolynomial (extendIdeal A) = affineHilbertPolynomial A :=
    K1_13_5_5_2.hilbertPolynomial_map (E := GeoField) A
  exact hbase ▸ h
theorem proof : K1_13_7_2_4.c3 := by
  intro P hp U hheight hdegree hjet
  let := hp
  let A := coefficientKernel (componentConstants P) U
  calc
    2 = (affineHilbertPolynomial P).natDegree := (jet_dimension P hheight).symm
    _ ≤ (affineHilbertPolynomial (freshImage A)).natDegree :=
      natDegree_affineHilbertPolynomial_le_of_le (freshImage_le_source P U hdegree hjet)
    _ ≤ (affineHilbertPolynomial A).natDegree := image_dimension_le A
end
end K1_13_7_2_4_3
end
section
namespace K1_13_4_2_4_1
noncomputable section
open K1_13 K1_13_4 K1_13_4_2_4 Polynomial
open scoped Polynomial
def constCoeff : Geom →+* ShiftSeed := (C : Geom[X] →+* ShiftSeed).comp C
private def constant (p : Geom[X]) : ShiftSeed[X] := p.map constCoeff
@[simp] private theorem specialize_C (ε : Geom) (u : Geom[X]) :
    specializeShift ε (C u) = C (u.eval ε) := by
  simp [specializeShift]
@[simp] private theorem specialize_X (ε : Geom) :
    specializeShift ε (Polynomial.X : ShiftSeed) = Polynomial.X := by
  simp [specializeShift]
@[simp] private theorem specialize_constant (p : Geom[X]) (ε : Geom) :
    (constant p).map (specializeShift ε) = p.map C := by
  rw [constant, Polynomial.map_map]
  have h : (specializeShift ε).comp constCoeff = (C : Geom →+* Geom[X]) := by
    ext x
    simp [constCoeff]
  rw [h]
@[simp] private theorem map_seed_eval (p : Geom[X]) (z : Geom) :
    (p.map C).map (evalRingHom z) = p := by
  rw [Polynomial.map_map]
  have h : (evalRingHom z).comp C = RingHom.id Geom := by
    ext x
    simp
  rw [h, Polynomial.map_id]
@[simp] private theorem map_seed_generic (p : Geom[X]) :
    (p.map C).map (algebraMap Geom[X] GenericSeed) = liftX p := by
  rw [liftX, Polynomial.map_map,
    ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_eq Geom Geom[X] GenericSeed]
theorem regular_resultant {F : Type*} [Field F] {H A : F[X]}
    (hH : H.Monic) {n : ℕ} (hA : A.natDegree ≤ n) (hc : IsCoprime A H) :
    H.resultant A H.natDegree n ≠ 0 := by
  have e := resultant_add_right_deg H A H.natDegree A.natDegree
    (n - A.natDegree) le_rfl
  rw [Nat.add_sub_of_le hA, coeff_natDegree, hH.leadingCoeff, one_pow, one_mul] at e
  rw [e]
  exact ((isUnit_resultant_iff_isCoprime hH).mpr hc.symm).ne_zero
theorem scaled_inverse {F : Type*} [Field F] {H A U V : F[X]} {d : F}
    (hd : d ≠ 0) (h : H * U + A * V = C d) : IsCoprime A H := by
  refine ⟨C d⁻¹ * V, C d⁻¹ * U, ?_⟩
  calc
    _ = C d⁻¹ * (H * U + A * V) := by ring
    _ = 1 := by rw [h, ← C_mul, inv_mul_cancel₀ hd, C_1]
theorem unscale {F : Type*} [Field F] {H A B N : F[X]} {d : F}
    (hd : d ≠ 0) (h : H ∣ A * N + C d * B) :
    H ∣ A * (C d⁻¹ * N) + B := by
  have hunit : C d⁻¹ * C d = (1 : F[X]) := by
    rw [← C_mul, inv_mul_cancel₀ hd, C_1]
  calc
    H ∣ C d⁻¹ * (A * N + C d * B) := h.mul_left _
    _ = A * (C d⁻¹ * N) + B := by
      calc
        _ = A * (C d⁻¹ * N) + (C d⁻¹ * C d) * B := by ring
        _ = _ := by rw [hunit, one_mul]
theorem proof : K1_13_4_2_4.c1 := by
  intro H c q a₀ a₁ hH hpos
  let block : ShiftSeed[X] := constant H + C (C (Polynomial.X : Geom[X]))
  let A : ShiftSeed[X] := constant c * (constant a₀ + C (Polynomial.X : ShiftSeed) * constant a₁)
  let B : ShiftSeed[X] := C (Polynomial.X : ShiftSeed) * constant q
  let den := block.resultant A block.natDegree A.natDegree
  have hconst : (constant H).Monic := hH.map constCoeff
  have hconst_deg : (constant H).natDegree = H.natDegree := hH.natDegree_map constCoeff
  have hdeg : block.natDegree = H.natDegree := by
    dsimp only [block]
    rw [natDegree_add_C, hconst_deg]
  have hblock : block.Monic :=
    hconst.add_of_left (degree_C_le.trans_lt
      (natDegree_pos_iff_degree_pos.mp (by rwa [hconst_deg])))
  have hblock_pos : 0 < block.natDegree := by rwa [hdeg]
  have hblock_ne : block ≠ 1 := by
    intro h
    simp [h] at hblock_pos
  obtain ⟨U, V, _, _, hbezout⟩ := exists_mul_add_mul_eq_C_resultant block A le_rfl le_rfl
    (Or.inl (Nat.ne_of_gt hblock_pos))
  change block * U + A * V = C den at hbezout
  let num := (-B * V) %ₘ block
  have hcleared : block ∣ A * num + C den * B := by
    obtain ⟨W, hW⟩ := dvd_modByMonic_sub (-B * V) block
    refine ⟨A * W + B * U, ?_⟩
    change num - (-B * V) = block * W at hW
    calc
      A * num + C den * B = A * (num - (-B * V)) + B * (block * U) := by
        rw [← hbezout]
        ring
      _ = block * (A * W + B * U) := by
        rw [hW]
        ring
  refine ⟨num, den, ?_⟩
  intro ε hc ha
  let s := specializeShift ε
  let e := evalRingHom (0 : Geom)
  let f := algebraMap Geom[X] GenericSeed
  have hHs : block.map s = (shiftedBlock H ε).map C := by
    simp only [block, s, shiftedBlock, Polynomial.map_add, Polynomial.map_C,
      specialize_constant, specialize_C, eval_X]
  have hAs : A.map s = c.map C * (a₀.map C + C (Polynomial.X : Geom[X]) * a₁.map C) := by
    simp only [A, s, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C,
      specialize_constant, specialize_X]
  have hBs : B.map s = C (Polynomial.X : Geom[X]) * q.map C := by
    simp only [B, s, Polynomial.map_mul, Polynomial.map_C, specialize_constant, specialize_X]
  have hHe : block.map (e.comp s) = shiftedBlock H ε := by
    rw [← Polynomial.map_map, hHs, map_seed_eval]
  have hAe : A.map (e.comp s) = c * a₀ := by
    rw [← Polynomial.map_map, hAs]
    simp [e]
  have hd : (s den).eval 0 ≠ 0 := by
    have hdegree : (block.map (e.comp s)).natDegree = block.natDegree := by
      rw [hHe, shiftedBlock_natDegree, hdeg]
    change (e.comp s) (block.resultant A block.natDegree A.natDegree) ≠ 0
    rw [← resultant_map_map, ← hdegree]
    exact regular_resultant (hblock.map (e.comp s)) natDegree_map_le (by
      rw [hHe, hAe]
      exact hc.mul_left ha)
  have hden : s den ≠ 0 := by
    intro h
    exact hd (by simp [h])
  have hf : f (s den) ≠ 0 :=
    (map_ne_zero_iff f (IsFractionRing.injective Geom[X] GenericSeed)).mpr hden
  have hHf : block.map (f.comp s) = liftX (shiftedBlock H ε) := by
    rw [← Polynomial.map_map, hHs, map_seed_generic]
  have hAf : A.map (f.comp s) = residueMultiplier c a₀ a₁ := by
    rw [← Polynomial.map_map, hAs]
    simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C,
      map_seed_generic, residueMultiplier, f]
  have hBf : B.map (f.comp s) = residueOffset q := by
    rw [← Polynomial.map_map, hBs]
    simp only [Polynomial.map_mul, Polynomial.map_C, map_seed_generic, residueOffset, f]
  refine ⟨hd, ?_, ?_, ?_⟩
  · rw [shiftedBlock_natDegree, ← hdeg]
    exact natDegree_map_le.trans_lt (natDegree_modByMonic_lt _ hblock hblock_ne)
  · have hm := congrArg (Polynomial.mapRingHom (f.comp s)) hbezout
    simp only [coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      hHf, hAf, RingHom.comp_apply] at hm
    exact scaled_inverse hf hm
  · have hm := Polynomial.map_dvd (f.comp s) hcleared
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hHf, hAf, hBf,
      RingHom.comp_apply] at hm
    have h := unscale hf hm
    simpa only [residueAtShift, genericResidue, Polynomial.map_map, f, s] using h
end
end K1_13_4_2_4_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K1_13_5_4_3_4
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 K1_13_5_4_3 MvPolynomial
open scoped BigOperators Polynomial
private abbrev Coord (P : Ideal (GeoRow 3)) := GeoRow 3 ⧸ P
private abbrev sep (f : Row 3) := genericRow (separant f)
private abbrev Chart (f : Row 3) (P : Ideal (GeoRow 3)) :=
  Localization.Away (Ideal.Quotient.mk P (sep f))
def intoChart (f : Row 3) (P : Ideal (GeoRow 3)) :
    GeoRow 3 →ₐ[GeometricX] Chart f P :=
  (IsScalarTower.toAlgHom GeometricX (Coord P) (Chart f P)).comp
    (Ideal.Quotient.mkₐ GeometricX P)
def pointQuotientEval {f : Row 3} {P : Ideal (GeoRow 3)} {y : Fin 3 → GeometricX}
    (hy : y ∈ regularLocus f P) : Coord P →ₐ[GeometricX] GeometricX :=
  Ideal.Quotient.liftₐ P (aeval y) (fun p hp => hy.1 p hp)
def pointChartEval {f : Row 3} {P : Ideal (GeoRow 3)} {y : Fin 3 → GeometricX}
    (hy : y ∈ regularLocus f P) : Chart f P →ₐ[GeometricX] GeometricX :=
  IsLocalization.Away.liftAlgHom (f := pointQuotientEval hy) (Ideal.Quotient.mk P (sep f))
    (isUnit_iff_ne_zero.mpr hy.2)
theorem pointChartEval_coord {f : Row 3} {P : Ideal (GeoRow 3)}
    {y : Fin 3 → GeometricX} (hy : y ∈ regularLocus f P) (p : GeoRow 3) :
    pointChartEval hy (intoChart f P p) = eval y p := by
  change pointChartEval hy
    (algebraMap (Coord P) (Chart f P) (Ideal.Quotient.mk P p)) = _
  rw [pointChartEval, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq] <;> rfl
theorem chart_eq_zero {f : Row 3} {P : Ideal (GeoRow 3)} (hp : P.IsPrime)
    (hsep : sep f ∉ P) {z : Chart f P}
    (hz : ∀ y (hy : y ∈ regularLocus f P), pointChartEval hy z = 0) : z = 0 := by
  let := hp
  let s := Ideal.Quotient.mk P (sep f)
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj s z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  change z * intoChart f P (sep f) ^ n = intoChart f P p at h
  have hm : sep f * p ∈ P := by
    rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := GeometricX) P]
    intro y hy
    change eval y (sep f * p) = 0
    rw [map_mul]
    by_cases hs : eval y (sep f) = 0
    · rw [hs, zero_mul]
    · have hr : y ∈ regularLocus f P := ⟨hy, hs⟩
      have he := congrArg (pointChartEval hr) h
      rw [map_mul, hz y hr, zero_mul, pointChartEval_coord] at he
      rw [← he, mul_zero]
  have hmem := (hp.mem_or_mem hm).resolve_left hsep
  have hzero : intoChart f P p = 0 := by
    change algebraMap (Coord P) (Chart f P) (Ideal.Quotient.mk P p) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
  have hu : IsUnit (intoChart f P (sep f) ^ n) :=
    IsLocalization.Away.algebraMap_pow_isUnit (S := Chart f P) s n
  exact hu.mul_right_cancel (by rw [h, hzero, zero_mul])
private def invSep (f : Row 3) (P : Ideal (GeoRow 3)) : Chart f P :=
  IsLocalization.Away.invSelf (Ideal.Quotient.mk P (sep f))
theorem pointChartEval_invSep {f : Row 3} {P : Ideal (GeoRow 3)}
    {y : Fin 3 → GeometricX} (hy : y ∈ regularLocus f P) :
    pointChartEval hy (invSep f P) = (eval y (sep f))⁻¹ := by
  have h : intoChart f P (sep f) * invSep f P = 1 :=
    IsLocalization.Away.mul_invSelf (Ideal.Quotient.mk P (sep f))
  have he := congrArg (pointChartEval hy) h
  rw [map_mul, pointChartEval_coord, map_one] at he
  exact (inv_eq_of_mul_eq_one_right he).symm
private def chartJet (f : Row 3) (P : Ideal (GeoRow 3)) : ℕ → Chart f P
  | 0 => intoChart f P (MvPolynomial.X 0)
  | 1 => intoChart f P (MvPolynomial.X 1)
  | 2 => intoChart f P (MvPolynomial.X 2)
  | k + 3 => 2 * intoChart f P (genericRow (compatibilityNumerator f k)) *
      algebraMap GeometricX (Chart f P) (((k + 3).factorial : GeometricX)⁻¹) *
      invSep f P ^ (2 * k + 1)
theorem pointEval_apply {y : Fin 3 → GeometricX} (p : Row 3) :
    pointEval y p = eval y (genericRow p) := rfl
theorem pointChartEval_chartJet {f : Row 3} {P : Ideal (GeoRow 3)}
    {y : Fin 3 → GeometricX} (hy : y ∈ regularLocus f P) (j : ℕ) :
    pointChartEval hy (chartJet f P j) = centredJet f (pointEval y) j := by
  match j with
  | 0 => simp [chartJet, centredJet, pointEval, pointChartEval_coord]
  | 1 => simp [chartJet, centredJet, pointEval, pointChartEval_coord]
  | 2 => simp [chartJet, centredJet, pointEval, pointChartEval_coord]
  | k + 3 =>
    simp only [chartJet, centredJet, map_mul, map_ofNat, map_pow, AlgHom.commutes,
      Algebra.algebraMap_self_apply, pointChartEval_coord, pointChartEval_invSep, pointEval_apply]
    rw [div_eq_mul_inv, mul_inv, ← inv_pow, mul_assoc (2 * _)]
private def chartTaylor (f : Row 3) (P : Ideal (GeoRow 3)) : (Chart f P)[X] :=
  Polynomial.taylor (-(algebraMap GeometricX (Chart f P) (genericCoeff Polynomial.X)))
    (∑ j : Fin taylorLength, Polynomial.monomial j.val (chartJet f P j.val))
theorem pointChartEval_chartTaylor {f : Row 3} {P : Ideal (GeoRow 3)}
    {y : Fin 3 → GeometricX} (hy : y ∈ regularLocus f P) :
    (chartTaylor f P).map (pointChartEval hy).toRingHom = taylorAt f (pointEval y) := by
  have hc : centre (pointEval y) = genericCoeff Polynomial.X := by simp [centre, pointEval]
  have hmap (z : Chart f P) : (pointChartEval hy).toRingHom z = pointChartEval hy z := rfl
  simp only [chartTaylor, taylorAt, hc, Polynomial.map_taylor, map_neg, hmap,
    AlgHom.commutes, Algebra.algebraMap_self_apply, Polynomial.map_sum, Polynomial.map_monomial,
    pointChartEval_chartJet]
def chartCoefficientMap (f : Row 3) (P : Ideal (GeoRow 3)) :
    GeoRow taylorLength →ₐ[GeometricX] Chart f P :=
  aeval (fun j : Fin taylorLength => (chartTaylor f P).coeff j.val)
theorem pointChartEval_coefficientMap {f : Row 3} {P : Ideal (GeoRow 3)}
    {y : Fin 3 → GeometricX} (hy : y ∈ regularLocus f P) (p : GeoRow taylorLength) :
    pointChartEval hy (chartCoefficientMap f P p) = eval (reconstructAt f y) p := by
  rw [chartCoefficientMap, comp_aeval_apply]
  have hj (j : Fin taylorLength) : pointChartEval hy ((chartTaylor f P).coeff j.val) =
      (taylorAt f (pointEval y)).coeff j.val := by
    change (pointChartEval hy).toRingHom ((chartTaylor f P).coeff j.val) = _
    rw [← Polynomial.coeff_map (f := (pointChartEval hy).toRingHom),
      pointChartEval_chartTaylor hy]
  exact congrArg (fun a : Coefficients => eval a p) (funext hj)
theorem curveIdeal_eq_ker {f : Row 3} {P : Ideal (GeoRow 3)}
    (hp : P.IsPrime) (hsep : sep f ∉ P) :
    curveIdeal f P = RingHom.ker (chartCoefficientMap f P).toRingHom := by
  ext p
  rw [RingHom.mem_ker]
  change (∀ a ∈ coefficientImage f P, eval a p = 0) ↔ chartCoefficientMap f P p = 0
  constructor
  · intro h
    apply chart_eq_zero hp hsep
    intro y hy
    rw [pointChartEval_coefficientMap hy]
    exact h _ ⟨y, hy, rfl⟩
  · rintro h _ ⟨y, hy, rfl⟩
    rw [← pointChartEval_coefficientMap hy, h, map_zero]
def initialJetForm (i : Fin 3) : GeoRow taylorLength :=
  (Polynomial.hasseDeriv i.val (∑ j : Fin taylorLength,
    Polynomial.monomial j.val (MvPolynomial.X j))).eval
      (MvPolynomial.C (genericCoeff Polynomial.X))
theorem eval_initialJetForm (a : Coefficients) (i : Fin 3) :
    eval a (initialJetForm i) =
      (Polynomial.hasseDeriv i.val (coefficientPolynomial a)).eval
        (genericCoeff Polynomial.X) := by
  rw [initialJetForm, ← Polynomial.eval_map_apply, ← Polynomial.hasseDeriv_map]
  simp only [Polynomial.map_sum, Polynomial.map_monomial, eval_X, eval_C, coefficientPolynomial]
theorem coord_in_range {f : Row 3} {P : Ideal (GeoRow 3)}
    (hp : P.IsPrime) (hsep : sep f ∉ P) (p : GeoRow 3) :
    intoChart f P p ∈ Set.range (chartCoefficientMap f P) := by
  have he : (chartCoefficientMap f P).comp (aeval initialJetForm) = intoChart f P := by
    apply algHom_ext
    intro i
    rw [AlgHom.comp_apply, aeval_X]
    apply sub_eq_zero.mp
    apply chart_eq_zero hp hsep
    intro y hy
    rw [map_sub, pointChartEval_coefficientMap hy, eval_initialJetForm,
      coefficientPolynomial_reconstructAt, recover_initial, pointChartEval_coord, eval_X, sub_self]
  exact ⟨aeval initialJetForm p, DFunLike.congr_fun he p⟩
theorem proof : K1_13_5_4_3.c4 := by
  intro f P hp hsep hdim
  let := hp
  have hs : Ideal.Quotient.mk P (sep f) ≠ 0 :=
    mt Ideal.Quotient.eq_zero_iff_mem.mp hsep
  let : IsDomain (Chart f P) := Localization.Away.isDomain hs
  let Φ := chartCoefficientMap f P
  have hk : curveIdeal f P = RingHom.ker Φ.toRingHom := curveIdeal_eq_ker hp hsep
  rw [hk]
  refine ⟨RingHom.ker_isPrime Φ.toRingHom, ?_⟩
  rw [← hdim]
  apply le_antisymm
  · let e := awayPresentationEquiv P (sep f)
    exact (natDegree_affineHilbertPolynomial_le_of_injective
      (e.symm.toAlgHom.comp (Ideal.kerLiftAlg Φ))
      (e.symm.injective.comp (Ideal.kerLiftAlg_injective Φ))).trans
        (natDegree_affineHilbertPolynomial_awayPresentationIdeal_le P (sep f))
  · have hregular : IsLeftRegular (Ideal.Quotient.mk P (sep f)) :=
      IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hs
    exact natDegree_affineHilbertPolynomial_le_of_away_range P (sep f) hregular Φ
      (coord_in_range hp hsep) le_rfl
end
end K1_13_5_4_3_4
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_4_2_2
noncomputable section
open K1_13_5_4 K1_13_5_4_2_4 K1_13_5_4_2_4_2 MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev Index (A : Fin 4 → Finset Exponent) := Σ i : Fin 4, ↥(A i)
abbrev IntegralRow (A : Fin 4 → Finset Exponent) :=
  MvPolynomial (Fin 4) (CoefficientRing A)
abbrev Spatial := MvPolynomial (Fin 4) GeometricX
private abbrev Rest {A : Fin 4 → Finset Exponent} (v : Index A) :=
  MvPolynomial {w : Index A // w ≠ v} Spatial
variable {A : Fin 4 → Finset Exponent}
private def pivotEquiv (v : Index A) : IntegralRow A ≃+* Polynomial (Rest v) := by
  classical
  exact (commAlgEquiv GeometricX (Fin 4) (Index A)).toRingEquiv.trans
    ((renameEquiv Spatial (Equiv.optionSubtypeNe v).symm).toRingEquiv.trans
      (optionEquivLeft Spatial {w : Index A // w ≠ v}).toRingEquiv)
private theorem pivotEquiv_pivot (v : Index A) :
    pivotEquiv v (C (MvPolynomial.X v)) = Polynomial.X := by
  classical
  simp [pivotEquiv, renameEquiv_apply]
private theorem pivotEquiv_other (v w : Index A) (h : w ≠ v) :
    pivotEquiv v (C (MvPolynomial.X w)) = Polynomial.C (MvPolynomial.X ⟨w, h⟩) := by
  classical
  simp [pivotEquiv, renameEquiv_apply, Equiv.optionSubtypeNe_symm_of_ne h]
private theorem pivotEquiv_X (v : Index A) (j : Fin 4) :
    pivotEquiv v (MvPolynomial.X j) = Polynomial.C (C (MvPolynomial.X j)) := by
  classical
  simp [pivotEquiv, renameEquiv_apply]
private theorem pivotEquiv_monomial (v : Index A) (a : Exponent) :
    pivotEquiv v (monomial a 1) = Polynomial.C (C (monomial a 1)) := by
  simp only [monic_monomial_eq, Finsupp.prod, map_prod, map_pow, pivotEquiv_X]
private def integralTerm (A : Fin 4 → Finset Exponent) (j : Fin 4) (a : ↥(A j)) :
    IntegralRow A :=
  C (MvPolynomial.X (⟨j, a⟩ : Index A)) * monomial a.1 1
private def integralEquation (A : Fin 4 → Finset Exponent) (j : Fin 4) : IntegralRow A :=
  ∑ a : ↥(A j), integralTerm A j a
private def integralPrefix (A : Fin 4 → Finset Exponent) (i : Fin 4) :
    Ideal (IntegralRow A) :=
  Ideal.span (integralEquation A '' {j : Fin 4 | (j : ℕ) < i.val})
private def restTerm (v : Index A) (j : Fin 4) (a : ↥(A j)) : Rest v := by
  classical
  exact if h : (⟨j, a⟩ : Index A) = v then 0
    else MvPolynomial.X ⟨⟨j, a⟩, h⟩ * C (monomial a.1 1)
private def restEquation (v : Index A) (j : Fin 4) : Rest v :=
  ∑ a : ↥(A j), restTerm v j a
private theorem pivotEquiv_integralTerm (v : Index A) (j : Fin 4) (a : ↥(A j))
    (h : (⟨j, a⟩ : Index A) ≠ v) :
    pivotEquiv v (integralTerm A j a) = Polynomial.C (restTerm v j a) := by
  simp [integralTerm, restTerm, h, pivotEquiv_other v _ h, pivotEquiv_monomial]
private theorem pivotEquiv_previous (i j : Fin 4) (hi : 0 ∈ A i) (hji : j.val < i.val) :
    pivotEquiv (⟨i, ⟨0, hi⟩⟩ : Index A) (integralEquation A j) =
      Polynomial.C (restEquation ⟨i, ⟨0, hi⟩⟩ j) := by
  rw [integralEquation, restEquation, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => pivotEquiv_integralTerm _ _ _ ?_
  exact fun h => (ne_of_lt hji) (congrArg (fun w : Index A => w.1.val) h)
private theorem pivotEquiv_current (i : Fin 4) (hi : 0 ∈ A i) :
    pivotEquiv (⟨i, ⟨0, hi⟩⟩ : Index A) (integralEquation A i) =
      Polynomial.X + Polynomial.C (restEquation ⟨i, ⟨0, hi⟩⟩ i) := by
  classical
  let a₀ : ↥(A i) := ⟨0, hi⟩
  let v : Index A := ⟨i, a₀⟩
  change pivotEquiv v (integralEquation A i) = Polynomial.X + Polynomial.C (restEquation v i)
  have h₀ : pivotEquiv v (integralTerm A i a₀) = Polynomial.X := by
    simp [integralTerm, a₀, v, pivotEquiv_pivot]
  have hr₀ : restTerm v i a₀ = 0 := by simp [restTerm, v]
  rw [integralEquation, restEquation, map_sum, map_sum,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ a₀),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ a₀), h₀, hr₀, map_zero, zero_add]
  congr 1
  refine Finset.sum_congr rfl fun a ha => pivotEquiv_integralTerm _ _ _ ?_
  intro h
  apply (Finset.mem_erase.mp ha).1
  exact Subtype.ext (congrArg (fun w : Index A => (w.2 : Exponent)) h)
private theorem cancel_monic_linear {B : Type*} [CommRing B] (J : Ideal B) (b : B)
    (q : Polynomial B) (h : (Polynomial.X + Polynomial.C b) * q ∈ J.map Polynomial.C) :
    q ∈ J.map Polynomial.C := by
  let f := Polynomial.mapRingHom (Ideal.Quotient.mk J)
  have hf : RingHom.ker f = J.map Polynomial.C := by
    dsimp only [f]
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker]
  rw [← hf, RingHom.mem_ker, map_mul] at h
  rw [← hf, RingHom.mem_ker]
  apply (Polynomial.monic_X_add_C (Ideal.Quotient.mk J b)).mul_right_eq_zero_iff.mp
  simpa [f] using h
private theorem integral_cancel (i : Fin 4) (hi : 0 ∈ A i) (q : IntegralRow A)
    (h : integralEquation A i * q ∈ integralPrefix A i) :
    q ∈ integralPrefix A i := by
  let v : Index A := ⟨i, ⟨0, hi⟩⟩
  let e := pivotEquiv v
  let J : Ideal (Rest v) := Ideal.span (restEquation v '' {j : Fin 4 | (j : ℕ) < i.val})
  have hJ : (integralPrefix A i).map e.toRingHom = J.map Polynomial.C := by
    dsimp only [J]
    rw [integralPrefix, Ideal.map_span, Ideal.map_span, Set.image_image, Set.image_image]
    exact congrArg Ideal.span (Set.image_congr fun j hj => pivotEquiv_previous i j hi hj)
  have hq := Ideal.mem_map_of_mem e.toRingHom h
  change e (integralEquation A i * q) ∈ (integralPrefix A i).map e.toRingHom at hq
  rw [hJ, map_mul, show e (integralEquation A i) =
    Polynomial.X + Polynomial.C (restEquation v i) from pivotEquiv_current i hi] at hq
  have hq' := cancel_monic_linear J (restEquation v i) (e q) hq
  rw [← hJ] at hq'
  obtain ⟨r, hr, he⟩ := (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hq'
  exact (e.injective he) ▸ hr
private theorem map_integralEquation (A : Fin 4 → Finset Exponent) (j : Fin 4) :
    algebraMap (IntegralRow A) (Row A) (integralEquation A j) = genericEquation A j := by
  simp only [integralEquation, integralTerm, genericEquation, MvPolynomial.algebraMap_def,
    map_sum, MvPolynomial.map_monomial, C_mul_monomial, mul_one]
theorem proof : K1_13_5_4_2_4_2.c2 := by
  intro A hA i p hp
  let M : Submonoid (IntegralRow A) := (CoefficientRing A)⁰.map (C (σ := Fin 4))
  let J := integralPrefix A i
  let f := algebraMap (IntegralRow A) (Row A)
  have hJ : J.map f = prefixIdeal A i.val := by
    dsimp only [J]
    rw [integralPrefix, prefixIdeal, Ideal.map_span, Set.image_image]
    exact congrArg Ideal.span (Set.image_congr fun j _ => map_integralEquation A j)
  obtain ⟨⟨q, s⟩, hs⟩ := IsLocalization.surj M p
  change p * f s = f q at hs
  have h : f (integralEquation A i * q) ∈ J.map f := by
    rw [map_mul, show f (integralEquation A i) = genericEquation A i from
      map_integralEquation A i, ← hs, ← mul_assoc, hJ]
    exact (prefixIdeal A i.val).mul_mem_right _ hp
  obtain ⟨t, ht, htq⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff M (Row A) J _).mp h
  have hq : t * q ∈ J := by
    apply integral_cancel i (hA i)
    rw [mul_left_comm]
    exact htq
  have hfp : f q ∈ J.map f :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff M (Row A) J q).mpr ⟨t, ht, hq⟩
  rw [hJ, ← hs] at hfp
  exact (Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units (Row A) s)).mp hfp
end
end K1_13_5_4_2_4_2_2
end
section
set_option autoImplicit false
namespace K1_13_6_2_3_2_1
noncomputable section
open K1_13_6_2_3_2
open scoped BigOperators Function
variable {ι σ : Type} [DecidableEq ι]
abbrev Cell (T : σ → ℕ) := ∀ x, Fin (T x + 1)
def cellOf (T : σ → ℕ) (e : σ →₀ ℕ) : Cell T :=
  fun x => ⟨min (T x) (e x), Nat.lt_succ_of_le (min_le_left _ _)⟩
def base [Finite σ] {T : σ → ℕ} (p : Cell T) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun x => (p x : ℕ))
@[simp] theorem base_apply [Finite σ] {T : σ → ℕ} (p : Cell T) (x : σ) :
    base p x = (p x : ℕ) :=
  rfl
theorem cellOf_eq_iff [Finite σ] {T : σ → ℕ} (p : Cell T) (e : σ →₀ ℕ) :
    cellOf T e = p ↔ base p ≤ e ∧ ∀ x, (p x : ℕ) < T x → e x = base p x := by
  constructor
  · intro h
    have hx (x : σ) : min (T x) (e x) = (p x : ℕ) :=
      congrArg (fun q : Cell T => (q x : ℕ)) h
    refine ⟨fun x => ?_, ?_⟩
    · rw [base_apply, ← hx x]
      exact min_le_right _ _
    · intro x hlt
      simp only [base_apply]
      have he := hx x
      omega
  · rintro ⟨h, hf⟩
    funext x
    apply Fin.ext
    change min (T x) (e x) = (p x : ℕ)
    have hle : (p x : ℕ) ≤ T x := Nat.le_of_lt_succ (p x).isLt
    have he : (p x : ℕ) ≤ e x := by simpa using h x
    by_cases hlt : (p x : ℕ) < T x
    · have hfix : e x = (p x : ℕ) := by simpa using hf x hlt
      omega
    · omega
theorem le_base_cellOf [Finite σ] {T : σ → ℕ} {b e : σ →₀ ℕ} (hb : ∀ x, b x ≤ T x) :
    b ≤ base (cellOf T e) ↔ b ≤ e := by
  simp only [Finsupp.le_def, base_apply, cellOf, le_min_iff]
  exact ⟨fun h x => (h x).2, fun h x => ⟨hb x, h x⟩⟩
abbrev grade (slot : σ → ι) : (σ →₀ ℕ) →+ (ι → ℕ) :=
  Finsupp.weight (step ∘ slot)
theorem grade_apply [Fintype σ] (slot : σ → ι) (e : σ →₀ ℕ) (i : ι) :
    grade slot e i = ∑ x ∈ Finset.univ.filter (fun x => slot x = i), e x := by
  rw [Finsupp.weight_eq_sum, Finset.sum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : slot x = i
  · simp [h, step]
  · simp [h, Ne.symm h, step]
theorem finite_grade [Fintype σ] (slot : σ → ι) (a : ι → ℕ) :
    {e : σ →₀ ℕ | grade slot e = a}.Finite := by
  classical
  let f (e : {e : σ →₀ ℕ | grade slot e = a}) (x : σ) : Fin (a (slot x) + 1) :=
    ⟨e.1 x, Nat.lt_succ_of_le (by
      have h := Finset.single_le_sum (f := fun y : σ => e.1 y)
        (s := Finset.univ.filter (fun y => slot y = slot x))
        (fun _ _ => Nat.zero_le _) (Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩)
      rwa [← grade_apply, e.2] at h)⟩
  have : Finite {e : σ →₀ ℕ | grade slot e = a} := Finite.of_injective f (by
    intro e g h
    exact Subtype.ext (Finsupp.ext fun x => congrArg (fun z => (z x : ℕ)) h))
  exact Set.toFinite _
def cellSlice {T : σ → ℕ} (slot : σ → ι) (p : Cell T) (a : ι → ℕ) : Set (σ →₀ ℕ) :=
  {e | cellOf T e = p ∧ grade slot e = a}
theorem sliceCount_sub [Fintype σ] (slot : σ → ι) (A B : Finset (σ →₀ ℕ))
    (hn : outside B ⊆ outside A) (T : σ → ℕ)
    (hT : ∀ b, b ∈ A ∨ b ∈ B → ∀ x, b x ≤ T x) (a : ι → ℕ) :
    sliceCount slot A a - sliceCount slot B a =
      ∑ᶠ p : {p : Cell T // base p ∈ outside A ∧ base p ∉ outside B},
        ((cellSlice slot p.1 a).ncard : ℚ) := by
  classical
  let P := {p : Cell T // base p ∈ outside A ∧ base p ∉ outside B}
  let SA : Set (σ →₀ ℕ) := {e | e ∈ outside A ∧ grade slot e = a}
  let SB : Set (σ →₀ ℕ) := {e | e ∈ outside B ∧ grade slot e = a}
  have ho (e : σ →₀ ℕ) (C : Finset (σ →₀ ℕ)) (hC : ∀ b ∈ C, b ∈ A ∨ b ∈ B) :
      base (cellOf T e) ∈ outside C ↔ e ∈ outside C := by
    change (∀ b ∈ C, ¬ b ≤ base (cellOf T e)) ↔ (∀ b ∈ C, ¬ b ≤ e)
    exact ⟨fun h b hb he => h b hb ((le_base_cellOf (hT b (hC b hb))).mpr he),
      fun h b hb he => h b hb ((le_base_cellOf (hT b (hC b hb))).mp he)⟩
  have hu : SA \ SB = ⋃ p : P, cellSlice slot p.1 a := by
    ext e
    simp only [Set.mem_sdiff, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨heA, hw⟩, heB⟩
      refine ⟨⟨cellOf T e, (ho e A (fun _ hb => Or.inl hb)).mpr heA, ?_⟩, rfl, hw⟩
      exact fun h => heB ⟨(ho e B (fun _ hb => Or.inr hb)).mp h, hw⟩
    · rintro ⟨p, he, hw⟩
      have hp := p.2
      rw [← he] at hp
      exact ⟨⟨(ho e A (fun _ hb => Or.inl hb)).mp hp.1, hw⟩,
        fun h => hp.2 ((ho e B (fun _ hb => Or.inr hb)).mpr h.1)⟩
  have hcard := Set.ncard_sdiff_add_ncard_of_subset
    (s := SB) (t := SA) (fun _ he => ⟨hn he.1, he.2⟩)
    ((finite_grade slot a).subset fun _ he => he.2)
  rw [hu, Set.ncard_iUnion_of_finite
    (fun p => (finite_grade slot a).subset fun _ he => he.2) ?_] at hcard
  · let _ : Fintype P := Fintype.ofFinite P
    change (SA.ncard : ℚ) - (SB.ncard : ℚ) = ∑ᶠ p : P, _
    rw [finsum_eq_sum_of_fintype] at hcard ⊢
    push_cast [← hcard]
    ring
  · intro p q hpq
    refine Set.disjoint_left.mpr fun e hp hq => hpq (Subtype.ext ?_)
    exact hp.1.symm.trans hq.1
end
end K1_13_6_2_3_2_1
end
section
set_option autoImplicit false
namespace K1_13_6_2_3_2_1
noncomputable section
open scoped BigOperators
variable {ι σ : Type} [DecidableEq ι] [Fintype σ] {T : σ → ℕ}
def free (slot : σ → ι) (p : Cell T) (i : ι) : Finset σ :=
  Finset.univ.filter (fun x => (p x : ℕ) = T x ∧ slot x = i)
private theorem mem_free {slot : σ → ι} {p : Cell T} {i : ι} {x : σ} :
    x ∈ free slot p i ↔ (p x : ℕ) = T x ∧ slot x = i := by
  simp [free]
def extras (slot : σ → ι) (p : Cell T) (e : σ →₀ ℕ)
    (i : ι) (x : free slot p i) : ℕ := e x - p x
private def extend (slot : σ → ι) (p : Cell T)
    (d : ∀ i, free slot p i → ℕ) (x : σ) : ℕ :=
  if h : (p x : ℕ) = T x then d (slot x) ⟨x, mem_free.mpr ⟨h, rfl⟩⟩ else 0
private def restore (slot : σ → ι) (p : Cell T)
    (d : ∀ i, free slot p i → ℕ) : σ →₀ ℕ :=
  base p + Finsupp.equivFunOnFinite.symm (extend slot p d)
theorem restore_cell (slot : σ → ι) (p : Cell T) (d : ∀ i, free slot p i → ℕ) :
    cellOf T (restore slot p d) = p := by
  apply (cellOf_eq_iff _ _).mpr
  refine ⟨le_add_right (le_refl _), ?_⟩
  intro x hx
  simp [restore, extend, ne_of_lt hx]
theorem restore_extras (slot : σ → ι) (p : Cell T) (e : σ →₀ ℕ)
    (h : cellOf T e = p) :
    restore slot p (extras slot p e) = e := by
  obtain ⟨hle, hfix⟩ := (cellOf_eq_iff _ _).mp h
  ext x
  by_cases hx : (p x : ℕ) = T x
  · have hpx : (p x : ℕ) ≤ e x := by simpa using hle x
    simp [restore, extend, extras, hx]
    omega
  · have hlt : (p x : ℕ) < T x :=
      lt_of_le_of_ne (Nat.le_of_lt_succ (p x).isLt) hx
    simpa [restore, extend, hx] using (hfix x hlt).symm
theorem extend_free (slot : σ → ι) (p : Cell T) (d : ∀ i, free slot p i → ℕ)
    (i : ι) (x : free slot p i) : extend slot p d x = d i x := by
  obtain ⟨hT, hi⟩ := mem_free.mp x.2
  let y : free slot p (slot x) := ⟨x, mem_free.mpr ⟨hT, rfl⟩⟩
  have hh (j : ι) (z : free slot p j) (h : j = i) (hz : (z : σ) = x) : d j z = d i x := by
    subst j
    exact congrArg (d i) (Subtype.ext hz)
  rw [extend, dite_eq_left hT]
  exact hh _ y hi rfl
theorem restore_grade (slot : σ → ι) (p : Cell T)
    (d : ∀ i, free slot p i → ℕ) (i : ι) :
    grade slot (restore slot p d) i = grade slot (base p) i + ∑ x : free slot p i, d i x := by
  rw [restore, map_add, Pi.add_apply]
  congr 1
  rw [grade_apply slot _ i]
  have hsub : free slot p i ⊆ Finset.univ.filter (fun x => slot x = i) :=
    fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ x, (mem_free.mp hx).2⟩
  have hz (x : σ) (hx : x ∈ Finset.univ.filter (fun x => slot x = i))
      (hn : x ∉ free slot p i) : extend slot p d x = 0 := by
    have hne : (p x : ℕ) ≠ T x := fun he => hn (mem_free.mpr ⟨he, (Finset.mem_filter.mp hx).2⟩)
    simp [extend, hne]
  change (∑ x ∈ Finset.univ.filter (fun x => slot x = i), extend slot p d x) = _
  rw [← Finset.sum_subset hsub hz, ← Finset.sum_attach (free slot p i) (extend slot p d)]
  exact Finset.sum_congr rfl fun x _ => extend_free slot p d i x
def cellEquiv (slot : σ → ι) (p : Cell T) (a : ι → ℕ)
    (ha : grade slot (base p) ≤ a) :
    cellSlice slot p a ≃
      (∀ i, {d : free slot p i → ℕ // ∑ x, d x = a i - grade slot (base p) i}) where
  toFun e i := ⟨extras slot p e i, by
    have h := (restore_grade slot p (extras slot p e) i).symm
    rw [restore_extras slot p e e.2.1, e.2.2] at h
    omega⟩
  invFun d := ⟨restore slot p (fun i => (d i).1), restore_cell slot p _, by
    funext i
    rw [restore_grade, (d i).2]
    exact Nat.add_sub_of_le (ha i)⟩
  left_inv e := Subtype.ext (restore_extras slot p e e.2.1)
  right_inv d := by
    funext i
    apply Subtype.ext
    funext x
    change restore slot p (fun j => (d j).1) x - (p x : ℕ) = (d i).1 x
    rw [restore, Finsupp.add_apply, base_apply]
    change (p x : ℕ) + extend slot p (fun j => (d j).1) x - (p x : ℕ) = (d i).1 x
    rw [extend_free, Nat.add_sub_cancel_left]
theorem cellSlice_ncard [Fintype ι] (slot : σ → ι) (p : Cell T) (a : ι → ℕ)
    (ha : grade slot (base p) ≤ a) :
    (cellSlice slot p a).ncard =
      ∏ i, (free slot p i).card.multichoose (a i - grade slot (base p) i) := by
  classical
  rw [← Nat.card_coe_set_eq, Nat.card_congr (cellEquiv slot p a ha), Nat.card_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Nat.card_congr (Sym.equivNatSumOfFintype (free slot p i)
    (a i - grade slot (base p) i)), Sym.natCard_sym_eq_multichoose, Nat.card_eq_fintype_card]
  exact congrArg (fun n => n.multichoose (a i - grade slot (base p) i)) (Fintype.card_coe _)
end
end K1_13_6_2_3_2_1
end
section
set_option autoImplicit false
namespace K1_13_6_2_3_2_1
noncomputable section
open K1_13_6_2_3_2 Filter
open scoped BigOperators
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def binom (n d : ℕ) : ℚ :=
  if d = 0 then 0 else (n.choose (d - 1) : ℚ)
private def model (w c d a : ι → ℕ) : ℚ :=
  ∏ i, binom (a i + c i - w i) (d i)
theorem binom_step (n d : ℕ) :
    binom (n + 1) d - binom n d = binom n (d - 1) := by
  cases d with
  | zero => simp [binom]
  | succ d =>
    cases d with
    | zero => simp [binom]
    | succ d =>
      simp only [binom, Nat.succ_ne_zero, ite_false, Nat.succ_sub_one, Nat.choose_succ_succ']
      push_cast
      ring
theorem model_step (w c d : ι → ℕ) (i : ι) :
    (fun a => model w c d (a + step i) - model w c d a) =ᶠ[atTop]
      model w c (Function.update d i (d i - 1)) := by
  filter_upwards [eventually_ge_atTop w] with a ha
  let rest (d' a' : ι → ℕ) :=
    ∏ j ∈ Finset.univ.erase i, binom (a' j + c j - w j) (d' j)
  have hfactor (d' a' : ι → ℕ) :
      model w c d' a' = binom (a' i + c i - w i) (d' i) * rest d' a' :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hshift : rest d (a + step i) = rest d a := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hne := (Finset.mem_erase.mp hj).1
    simp [step, hne]
  have hupdate : rest (Function.update d i (d i - 1)) a = rest d a := by
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  have htop : (a + step i) i + c i - w i = (a i + c i - w i) + 1 := by
    simp only [Pi.add_apply, step, Pi.single_eq_same]
    have h : w i ≤ a i := ha i
    omega
  simp only [hfactor, hshift, hupdate, htop, Function.update_self]
  rw [← sub_mul, binom_step]
omit [Fintype ι] in
theorem eventual_shift {p : (ι → ℕ) → Prop} (h : ∀ᶠ a in atTop, p a) (i : ι) :
    ∀ᶠ a in atTop, p (a + step i) := by
  obtain ⟨a, h⟩ := eventually_atTop.mp h
  refine eventually_atTop.mpr ⟨a, fun b hb => h _ (hb.trans ?_)⟩
  exact fun j => Nat.le_add_right _ _
omit [Fintype ι] in
theorem deltas_congr (used : List ι) {H G : (ι → ℕ) → ℚ} (h : H =ᶠ[atTop] G) :
    deltas used H =ᶠ[atTop] deltas used G := by
  induction used with
  | nil => exact h
  | cons i used ih =>
    filter_upwards [eventual_shift ih i, ih] with a h₁ h₂
    exact congrArg₂ (· - ·) h₁ h₂
omit [Fintype ι] in
theorem deltas_comm (used : List ι) (H : (ι → ℕ) → ℚ) (i : ι) (a : ι → ℕ) :
    deltas used (fun b => H (b + step i) - H b) a =
      deltas used H (a + step i) - deltas used H a := by
  induction used generalizing a with
  | nil => rfl
  | cons j used ih =>
    simp only [deltas, ih]
    rw [add_right_comm a (step j) (step i)]
    ring
theorem model_deltas_nonneg (used : List ι) (w c d : ι → ℕ) :
    ∀ᶠ a in atTop, 0 ≤ deltas used (model w c d) a := by
  induction used generalizing d with
  | nil =>
    exact Eventually.of_forall fun a =>
      Finset.prod_nonneg fun j _ => by unfold binom; split <;> positivity
  | cons i used ih =>
    filter_upwards [deltas_congr used (model_step w c d i), ih (Function.update d i (d i - 1))]
      with a he hn
    rw [deltas_comm] at he
    change 0 ≤ deltas used (model w c d) (a + step i) - deltas used (model w c d) a
    rwa [he]
def cellPoly (w d : ι → ℕ) : MvPolynomial ι ℚ :=
  ∏ i, if d i = 0 then 0 else
    (Polynomial.preHilbertPoly ℚ (d i - 1) (w i)).eval₂ MvPolynomial.C (MvPolynomial.X i)
omit [DecidableEq ι] in
theorem eval_cellPoly (w d : ι → ℕ) {a : ι → ℕ} (ha : w ≤ a) :
    MvPolynomial.eval (fun i => (a i : ℚ)) (cellPoly w d) =
      model w (fun i => d i - 1) d a := by
  let E := MvPolynomial.eval (fun i => (a i : ℚ))
  have hC : E.comp MvPolynomial.C = RingHom.id ℚ := by
    apply RingHom.ext
    intro q
    simp [E]
  simp only [cellPoly, map_prod, model]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : d i = 0
  · simp [binom, hi]
  · simp only [binom, hi, ite_false]
    change E (_ : MvPolynomial ι ℚ) = _
    rw [Polynomial.hom_eval₂, hC, MvPolynomial.eval_X]
    exact Polynomial.preHilbertPoly_eq_choose_add_sub ℚ _
      ((ha i).trans (Nat.le_add_right _ _))
theorem binom_multichoose (d a w : ℕ) (h : w < a) :
    (d.multichoose (a - w) : ℚ) = binom (a + (d - 1) - w) d := by
  cases d with
  | zero =>
    rw [show a - w = (a - w - 1) + 1 by omega, Nat.multichoose_zero_succ]
    simp [binom]
  | succ d =>
    simp only [Nat.multichoose_eq, binom, Nat.succ_ne_zero, ite_false, Nat.succ_sub_one]
    rw [show d + 1 + (a - w) - 1 = (a - w) + d by omega, Nat.choose_symm_add,
      show (a - w) + d = a + d - w by omega]
omit [Fintype ι] in
theorem deltas_sum {β : Type} (s : Finset β) (H : β → (ι → ℕ) → ℚ)
    (used : List ι) (a : ι → ℕ) :
    deltas used (fun b => ∑ p ∈ s, H p b) a = ∑ p ∈ s, deltas used (H p) a := by
  induction used generalizing a with
  | nil => rfl
  | cons i used ih => simp only [deltas, ih, Finset.sum_sub_distrib]
theorem proof : K1_13_6_2_3_2.c1 := by
  intro ι σ _ _ _ slot A B hn
  classical
  let _ : Fintype σ := Fintype.ofFinite σ
  let T (x : σ) := max (A.sup fun b => b x) (B.sup fun b => b x)
  have hT (b : σ →₀ ℕ) (hb : b ∈ A ∨ b ∈ B) (x : σ) : b x ≤ T x :=
    hb.elim (fun h => (Finset.le_sup (f := fun z : σ →₀ ℕ => z x) h).trans (le_max_left _ _))
      (fun h => (Finset.le_sup (f := fun z : σ →₀ ℕ => z x) h).trans (le_max_right _ _))
  let P := {p : Cell T // base p ∈ outside A ∧ base p ∉ outside B}
  let _ : Fintype P := Fintype.ofFinite P
  let w (p : P) := grade slot (base p.1)
  let d (p : P) (i : ι) := (free slot p.1 i).card
  let F (p : P) := model (w p) (fun i => d p i - 1) (d p)
  have hcell (p : P) : ∀ᶠ a in atTop, ((cellSlice slot p.1 a).ncard : ℚ) = F p a := by
    filter_upwards [eventually_ge_atTop (fun i => w p i + 1)] with a ha
    have hl (i : ι) : w p i < a i := ha i
    rw [cellSlice_ncard slot p.1 a (fun i => (hl i).le), Nat.cast_prod]
    exact Finset.prod_congr rfl fun i _ => binom_multichoose _ _ _ (hl i)
  have hsum : (fun a => sliceCount slot A a - sliceCount slot B a) =ᶠ[atTop]
      (fun a => ∑ p : P, F p a) := by
    filter_upwards [eventually_all.mpr hcell] with a ha
    rw [sliceCount_sub slot A B hn T hT]
    change (∑ᶠ p : P, _) = _
    rw [finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun p _ => ha p
  refine ⟨⟨∑ p : P, cellPoly (w p) (d p), ?_⟩, ?_⟩
  · filter_upwards [hsum, eventually_all.mpr fun p : P => eventually_ge_atTop (w p)] with a h ha
    rw [h, map_sum]
    exact Finset.sum_congr rfl fun p _ => eval_cellPoly _ _ (ha p)
  · intro used
    filter_upwards [deltas_congr used hsum,
      eventually_all.mpr fun p : P => model_deltas_nonneg used (w p) _ (d p)] with a h ha
    rw [h, deltas_sum]
    exact Finset.sum_nonneg fun p _ => ha p
end
end K1_13_6_2_3_2_1
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_1
noncomputable section
open K1_13_6 MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
theorem standard_piece_rank {σ : Type} (s : σ → Fin 5) (m : MonomialOrder σ)
    (J : Ideal (MvPolynomial σ GeoField)) (hJ : J.IsHomogeneous (piece s)) (t : Grade) :
    gradedHilbert s J t =
      {a ∈ m.standardExponents J | Finsupp.weight (slotWeight s) a = t}.ncard := by
  let A := {a ∈ m.standardExponents J | Finsupp.weight (slotWeight s) a = t}
  let S := restrictSupport GeoField A
  let T := (piece s t).map (Ideal.Quotient.mkₐ GeoField J).toLinearMap
  let L : S →ₗ[GeoField] T :=
    ((Ideal.Quotient.mkₐ GeoField J).toLinearMap.domRestrict S).codRestrict T fun z =>
      ⟨z.val, fun _ he => (z.property (mem_support_iff.mpr he)).2, rfl⟩
  have hinj : Function.Injective L := by
    intro x y h
    apply Subtype.ext
    apply m.eq_of_mem_standardSpace_of_sub_mem
    · exact fun _ ha => (x.property ha).1
    · exact fun _ ha => (y.property ha).1
    · exact Ideal.Quotient.eq.mp (congrArg Subtype.val h)
  have hsurj : Function.Surjective L := by
    intro y
    obtain ⟨b, hb, hby⟩ := y.property
    obtain ⟨q, hq, hbq, _⟩ := m.exists_mem_standardSpace_sub_mem J b
    let r := weightedHomogeneousComponent (slotWeight s) t q
    have hr : r ∈ S := by
      intro a ha
      have hw : r.IsWeightedHomogeneous (slotWeight s) t :=
        weightedHomogeneousComponent_isWeightedHomogeneous t q
      refine ⟨hq ?_, hw (mem_support_iff.mp ha)⟩
      change a ∈ (weightedHomogeneousComponent (slotWeight s) t q).support at ha
      rw [support_weightedHomogeneousComponent] at ha
      exact (Finset.mem_filter.mp ha).1
    have hbr : b - r ∈ J := by
      have hc := weightedHomogeneousComponent_mem_of_mem _ _ hJ hbq t
      rwa [map_sub, weightedHomogeneousComponent_eq_self (show
        b.IsWeightedHomogeneous (slotWeight s) t from hb)] at hc
    exact ⟨⟨r, hr⟩, Subtype.ext ((Ideal.Quotient.eq.mpr hbr).symm.trans hby)⟩
  let e := LinearEquiv.ofBijective L ⟨hinj, hsurj⟩
  change Module.finrank GeoField T = A.ncard
  rw [← e.finrank_eq, Module.finrank_eq_nat_card_basis (basisRestrictSupport GeoField A),
    Nat.card_coe_set_eq]
theorem forms_of_counts
    (hc : ∀ (σ : Type) [Finite σ] (s : σ → Fin 5) (A C : Finset (σ →₀ ℕ)),
      outside C ⊆ outside A → ∃ p q : Form,
        Represents p (fun t => sliceCount s A t) ∧
        Represents q (fun t => sliceCount s C t) ∧ TopNonnegative (p - q))
    (σ : Type) [Finite σ] (s : σ → Fin 5) (J K : Ideal (MvPolynomial σ GeoField))
    (hJ : J.IsHomogeneous (piece s)) (hK : K.IsHomogeneous (piece s)) (hJK : J ≤ K) :
    ∃ p q : Form, Represents p (fun t => gradedHilbert s J t) ∧
      Represents q (fun t => gradedHilbert s K t) ∧ TopNonnegative (p - q) := by
  let _ := Fintype.ofFinite σ
  let _ : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  let m : MonomialOrder σ := MonomialOrder.degLex
  obtain ⟨A, hA⟩ := m.exists_finset_standardExponents_iff J
  obtain ⟨C, hC⟩ := m.exists_finset_standardExponents_iff K
  have hJA : m.standardExponents J = outside A := Set.ext hA
  have hKC : m.standardExponents K = outside C := Set.ext hC
  have hsub : outside C ⊆ outside A := by
    rw [← hJA, ← hKC]
    intro a ha p hp
    exact ha p (hJK hp)
  obtain ⟨p, q, hp, hq, hpq⟩ := hc σ s A C hsub
  have hilbertJ (t : Grade) : gradedHilbert s J t = sliceCount s A t := by
    rw [standard_piece_rank s m J hJ t, hJA]
    rfl
  have hilbertK (t : Grade) : gradedHilbert s K t = sliceCount s C t := by
    rw [standard_piece_rank s m K hK t, hKC]
    rfl
  exact ⟨p, q, by simpa only [hilbertJ] using hp, by simpa only [hilbertK] using hq, hpq⟩
end
end K1_13_6_2_4_1
end
section
set_option autoImplicit false
namespace K1_13_7_1_1_1_2_1
noncomputable section
open K1_13_6 K1_13_6_2_4_1 K1_13_7_1_1_1 K1_13_7_1_1_1_2
open K1_13_6_2_3_2 (step deltas)
open MvPolynomial Filter
attribute [local instance] MvPolynomial.weightedGradedAlgebra
private abbrev coords (a : Grid) : Fin 5 → ℕ := multigrade a
theorem coords_advance (a : Grid) (i : Fin 4) :
    coords (a + advance i) = coords a + step i.castSucc := by
  funext j
  change multigrade (a + advance i) j = multigrade a j + step i.castSucc j
  rw [multigrade_add, multigrade_advance, Finsupp.add_apply]
  simp [unitGrade, step, Finsupp.single_apply, Pi.single_apply, eq_comm]
theorem eventually_coords {p : (Fin 5 → ℕ) → Prop}
    (h : ∀ᶠ t in atTop, p t) : ∀ᶠ a in atTop, p (coords a) := by
  obtain ⟨t, ht⟩ := eventually_atTop.mp h
  refine eventually_atTop.mpr ⟨(t (Fin.last 4), fun i => t i.castSucc), fun a ha => ht _ ?_⟩
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa only [coords, multigrade_last] using ha.1
  · simpa only [coords, multigrade_castSucc] using ha.2 i
theorem deltas_comm (dirs : List (Fin 5)) (H : (Fin 5 → ℕ) → ℚ)
    (i : Fin 5) (t : Fin 5 → ℕ) :
    deltas dirs (fun u => H (u + step i) - H u) t =
      deltas dirs H (t + step i) - deltas dirs H t := by
  induction dirs generalizing t with
  | nil => rfl
  | cons j dirs ih =>
    simp only [deltas, ih]
    rw [add_right_comm t (step j) (step i)]
    ring
theorem difference_cast (dirs : List (Fin 4)) (H : (Fin 5 → ℕ) → ℚ)
    (a : Grid) :
    difference dirs (fun b => (H (coords b) : ℝ)) a =
      (deltas (dirs.map Fin.castSucc) H (coords a) : ℝ) := by
  induction dirs generalizing H with
  | nil => rfl
  | cons i dirs ih =>
    change difference dirs (fun b => (H (coords (b + advance i)) : ℝ) - (H (coords b) : ℝ)) a = _
    simp only [coords_advance, ← Rat.cast_sub]
    rw [ih (fun t => H (t + step i.castSucc) - H t), deltas_comm, List.map_cons, deltas]
theorem weight_coe {σ : Type} [Fintype σ] (s : σ → Fin 5) (e : σ →₀ ℕ) :
    (⇑(Finsupp.weight (slotWeight s) e) : Fin 5 → ℕ) = Finsupp.weight (step ∘ s) e := by
  funext j
  rw [Finsupp.weight_eq_sum, Finsupp.weight_eq_sum, Finsupp.finsetSum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [slotWeight, unitGrade, step, Pi.smul_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]
theorem rankAt_eq_slice {σ : Type} [Fintype σ] (s : σ → Fin 5) (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ GeoField)) (hI : I.IsHomogeneous (piece s))
    (A : Finset (σ →₀ ℕ)) (hA : m.standardExponents I = K1_13_6_2_3_2.outside A)
    (a : Grid) : rankAt s I a = (K1_13_6_2_3_2.sliceCount s A (coords a) : ℝ) := by
  rw [rankAt, standard_piece_rank s m I hI, hA]
  simp only [K1_13_6_2_3_2.sliceCount, Rat.cast_natCast]
  apply congrArg (fun S : Set (σ →₀ ℕ) => (S.ncard : ℝ))
  ext e
  change (_ ∧ Finsupp.weight (slotWeight s) e = multigrade a) ↔
    (_ ∧ Finsupp.weight (step ∘ s) e = coords a)
  refine and_congr_right fun _ => ?_
  rw [← weight_coe s e]
  exact ⟨fun h => congrArg (fun t : Grade => (⇑t : Fin 5 → ℕ)) h,
    fun h => DFunLike.coe_injective h⟩
theorem proof : K1_13_7_1_1_1_2.c1 := by
  classical
  intro σ _ s I J hI hJ hIJ k
  let _ := Fintype.ofFinite σ
  let _ : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  let m : MonomialOrder σ := MonomialOrder.degLex
  obtain ⟨A, hA⟩ := m.exists_finset_standardExponents_iff I
  obtain ⟨B, hB⟩ := m.exists_finset_standardExponents_iff J
  have hIA : m.standardExponents I = K1_13_6_2_3_2.outside A := Set.ext hA
  have hJB : m.standardExponents J = K1_13_6_2_3_2.outside B := Set.ext hB
  have hBA : K1_13_6_2_3_2.outside B ⊆ K1_13_6_2_3_2.outside A := by
    rw [← hIA, ← hJB]
    intro e he f hf
    exact he f (hIJ hf)
  let H (t : Fin 5 → ℕ) := K1_13_6_2_3_2.sliceCount s A t - K1_13_6_2_3_2.sliceCount s B t
  let dirs := remainingDirections k
  have hH : (fun a => rankAt s I a - rankAt s J a) = fun a => (H (coords a) : ℝ) := by
    funext a
    rw [rankAt_eq_slice s m I hI A hIA, rankAt_eq_slice s m J hJ B hJB]
    exact (Rat.cast_sub _ _).symm
  have hp : ∀ᶠ t in atTop, 0 ≤ deltas (dirs.map Fin.castSucc) H t :=
    (K1_13_6_2_3_2_1.proof s A B hBA).2 _
  rw [hH]
  filter_upwards [eventually_coords hp] with a ha
  rw [difference_cast]
  exact_mod_cast ha
end
end K1_13_7_1_1_1_2_1
end
section
namespace K1_13_7_4_2_1
open K1_13_7 K1_13_7_4_2
open Ideal IsLocalRing MvPolynomial RingTheory.Sequence
open CategoryTheory Abelian
open scoped Pointwise
private noncomputable abbrev coord : Fin 3 → Lower := MvPolynomial.X
private theorem variable_cancel {s : Set (Fin 3)} {i : Fin 3} (hi : i ∉ s)
    (p : Lower) (hp : coord i * p ∈ span (coord '' s)) : p ∈ span (coord '' s) := by
  rw [mem_ideal_span_X_image] at hp ⊢
  intro m hm
  have hcoeff := coeff_X_mul m i p
  have hmem : Finsupp.single i 1 + m ∈ (coord i * p).support :=
    mem_support_iff.mpr (hcoeff.trans_ne (mem_support_iff.mp hm))
  obtain ⟨j, hj, hne⟩ := hp _ hmem
  have hji : i ≠ j := fun e => hi (e.symm ▸ hj)
  exact ⟨j, hj, by simpa [Finsupp.add_apply, Finsupp.single_apply, hji] using hne⟩
private theorem variables_weaklyRegular :
    IsWeaklyRegular Lower ([coord 0, coord 1, coord 2] : List Lower) := by
  classical
  have step (s : Set (Fin 3)) (i : Fin 3) (hi : i ∉ s) :
      IsSMulRegular (Lower ⧸ span (coord '' s)) (coord i) :=
    (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr (variable_cancel hi)
  have h₀ : (Ideal.ofList ([] : List Lower) • (⊤ : Submodule Lower Lower)) =
      span (coord '' (∅ : Set (Fin 3))) := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.ofList_nil, Set.image_empty, Ideal.span_empty]
  have h₁ : (Ideal.ofList [coord 0] • (⊤ : Submodule Lower Lower)) =
      span (coord '' ({0} : Set (Fin 3))) := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.ofList_singleton, Set.image_singleton]
  have h₂ : (Ideal.ofList [coord 0, coord 1] • (⊤ : Submodule Lower Lower)) =
      span (coord '' ({0, 1} : Set (Fin 3))) := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.ofList_cons, Ideal.ofList_singleton,
      Set.image_insert_eq, Set.image_singleton, Ideal.span_insert]
  refine ⟨?_⟩
  intro i hi
  have hib : i < 3 := hi
  interval_cases i
  · change IsSMulRegular (Lower ⧸ (Ideal.ofList [] • (⊤ : Submodule Lower Lower))) (coord 0)
    exact ((Submodule.quotEquivOfEq _ _ h₀).isSMulRegular_congr (coord 0)).mpr
      (step ∅ 0 (by simp))
  · change IsSMulRegular (Lower ⧸ (Ideal.ofList [coord 0] • (⊤ : Submodule Lower Lower)))
      (coord 1)
    exact ((Submodule.quotEquivOfEq _ _ h₁).isSMulRegular_congr (coord 1)).mpr
      (step {0} 1 (by simp))
  · change IsSMulRegular (Lower ⧸ (Ideal.ofList [coord 0, coord 1] • (⊤ : Submodule Lower Lower)))
      (coord 2)
    exact ((Submodule.quotEquivOfEq _ _ h₂).isSMulRegular_congr (coord 2)).mpr
      (step {0, 1} 2 (by simp))
private noncomputable def translation (y : LowerPoint) : Lower ≃ₐ[GeometricX] Lower :=
  AlgEquiv.ofAlgHom (aeval (fun i => coord i - C (y i))) (aeval (fun i => coord i + C (y i)))
    (MvPolynomial.algHom_ext (fun i => by simp))
    (MvPolynomial.algHom_ext (fun i => by simp))
set_option maxHeartbeats 1000000 in
theorem exists_regular_three (q : PrimeSpectrum Lower) (hh : q.asIdeal.height = 3) :
    ∃ rs : List (Local q), rs.length = 3 ∧
      (∀ x ∈ rs, x ∈ maximalIdeal (Local q)) ∧ IsRegular (Local q) rs := by
  classical
  have hd : ringKrullDim Lower = 3 := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite]
    simp
  have hd' : ringKrullDim Lower = ((3 : ℕ∞) : WithBot ℕ∞) := hd
  have : FiniteRingKrullDim Lower := finiteRingKrullDim_iff_ne_bot_and_top.mpr (by
    rw [hd']
    refine ⟨WithBot.coe_ne_bot, ?_⟩
    rw [← WithBot.coe_top]
    exact fun h => ENat.natCast_ne_top 3 (WithBot.coe_inj.mp h))
  have hq : q.asIdeal.IsMaximal := Ideal.isMaximal_of_height_eq_ringKrullDim (by
    rw [hd, hh]
    rfl)
  obtain ⟨y, hy⟩ :=
    MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal (K := GeometricX) hq
  let e := (translation y).toRingEquiv
  let rs : List Lower := [coord 0, coord 1, coord 2]
  have hcongr : List.Forall₂ (fun (r s : Lower) => ∀ x : Lower, e (r • x) = s • e x)
      rs (rs.map e) :=
    List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun r _ x => e.map_mul r x)
  have hwr : IsWeaklyRegular Lower (rs.map e) :=
    (e.toAddEquiv.isWeaklyRegular_congr hcongr).mp variables_weaklyRegular
  have hm (x : Lower) (hx : x ∈ rs.map e) : x ∈ q.asIdeal := by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
    have hw' : ∃ i : Fin 3, w = coord i := by
      simp only [rs, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    obtain ⟨i, rfl⟩ := hw'
    rw [hy, mem_vanishingIdeal_singleton_iff]
    change aeval y (aeval (fun j => coord j - C (y j)) (coord i)) = 0
    simp
  have hreg := hwr.isRegular_of_isLocalization_of_mem (Local q) q.asIdeal hm
  refine ⟨(rs.map e).map (algebraMap Lower (Local q)), by simp [rs], ?_, hreg⟩
  intro x hx
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Local q) q.asIdeal w).mpr (hm w hw)
universe u
private theorem ext_after_regular {R : Type u} [CommRing R] (N M : ModuleCat.{u} R)
    {a : R} (ha : IsSMulRegular M a) {n : ℕ}
    (h : ∀ i < n + 1, Subsingleton (Ext N M i)) :
    ∀ i < n, Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop a M)) i) := by
  intro i hi
  have h₀ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h i (by omega))
  have h₁ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h (i + 1) (by omega))
  exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
    (Ext.covariant_sequence_exact₃' N ha.smulShortComplex_shortExact i (i + 1) rfl)
    (h₀.eq_zero_of_src _) (h₁.eq_zero_of_tgt _)
theorem regular_on_pair_quotient {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {a b : R} (ha : IsSMulRegular R a) (hb : IsSMulRegular (QuotSMulTop a R) b)
    (rs : List R) (hlen : rs.length = 3) (hmem : ∀ x ∈ rs, x ∈ maximalIdeal R)
    (hreg : IsRegular R rs) :
    ∃ r ∈ maximalIdeal R, IsSMulRegular (R ⧸ span ({a, b} : Set R)) r := by
  let N := ModuleCat.of R (R ⧸ maximalIdeal R)
  let M := ModuleCat.of R R
  let M₁ := ModuleCat.of R (QuotSMulTop a R)
  let M₂ := ModuleCat.of R (QuotSMulTop b (QuotSMulTop a R))
  have hAnn : Module.annihilator R N = maximalIdeal R := Ideal.annihilator_quotient
  have hSupp : Module.support R N ⊆ PrimeSpectrum.zeroLocus (maximalIdeal R) := by
    rw [Module.support_eq_zeroLocus, hAnn]
  have hlt : maximalIdeal R • (⊤ : Submodule R M) < ⊤ := by
    change maximalIdeal R • (⊤ : Ideal R) < ⊤
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top.lt_top
  have h₀ : ∀ i < 3, Subsingleton (Ext N M i) := by
    rw [← hlen]
    exact ModuleCat.subsingleton_ext_of_exists_isRegular _ N hSupp M hlt rs hmem hreg
  have h₁ : ∀ i < 2, Subsingleton (Ext N M₁ i) := ext_after_regular N M ha h₀
  have h₂ : ∀ i < 1, Subsingleton (Ext N M₂ i) := ext_after_regular N M₁ hb h₁
  have hHom : Subsingleton (N →ₗ[R] M₂) :=
    (Ext.addEquiv₀.trans ModuleCat.homAddEquiv).subsingleton_congr.mp (h₂ 0 (by decide))
  obtain ⟨r, hr, hreg₂⟩ := IsSMulRegular.subsingleton_linearMap_iff.mp hHom
  have e : (R ⧸ span ({a, b} : Set R)) ≃ₗ[R] QuotSMulTop b (QuotSMulTop a R) := by
    have hfirst : (Ideal.ofList [a, b] • (⊤ : Submodule R R)) = span ({a, b} : Set R) := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.ofList_cons, Ideal.ofList_singleton,
        Ideal.span_insert]
    have hsecond : (Ideal.ofList [b] • (⊤ : Submodule R (QuotSMulTop a R))) = b • ⊤ := by
      rw [Ideal.ofList_singleton, Submodule.ideal_span_singleton_smul]
    have e' := Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner R a [b]
    rwa [hfirst, hsecond] at e'
  exact ⟨r, hAnn ▸ hr, (e.isSMulRegular_congr r).mpr hreg₂⟩
end K1_13_7_4_2_1
end
section
namespace K1_13_7_4_2_1
open K1_13_7 K1_13_7_4_2
open Ideal IsLocalRing
open scoped Pointwise
section LocalRing
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
private theorem height_bound {I : Ideal R} (hI : I.radical = maximalIdeal R)
    (s : Finset R) (hs : (↑s : Set R) ⊆ maximalIdeal R) (hle : I ≤ span (↑s : Set R)) :
    (maximalIdeal R).height ≤ s.card := by
  apply Ideal.height_le_card_of_mem_minimalPrimes_span_finset
  refine ⟨⟨inferInstance, span_le.mpr hs⟩, ?_⟩
  intro p hp _
  exact hI ▸ hp.1.radical_le_iff.mpr (hle.trans hp.2)
omit [IsNoetherianRing R] [IsLocalRing R] in
theorem principal_smul_top (a : R) :
    a • (⊤ : Submodule R R) = (span {a} : Ideal R) := by
  rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
theorem parameter_pair [IsDomain R] [UniqueFactorizationMonoid R] {a b : R}
    (s : Finset R) (hrad : (span (insert a (insert b (↑s : Set R)))).radical = maximalIdeal R)
    (hheight : (↑(s.card + 1) : ℕ∞) < (maximalIdeal R).height) :
    IsSMulRegular R a ∧ IsSMulRegular (QuotSMulTop a R) b := by
  classical
  let I := span (insert a (insert b (↑s : Set R)))
  have hm : (insert a (insert b (↑s : Set R))) ⊆ maximalIdeal R := fun _ hx =>
    hrad ▸ I.le_radical (subset_span hx)
  have hsmall (x : R) (hx : x ∈ maximalIdeal R) (hle : I ≤ span (↑(insert x s) : Set R)) :
      False := by
    have hs : (↑(insert x s) : Set R) ⊆ maximalIdeal R := by
      intro z hz
      simp only [Finset.coe_insert, Set.mem_insert_iff] at hz
      rcases hz with rfl | hz
      · exact hx
      · exact hm (by simp [hz])
    exact hheight.not_ge ((height_bound hrad (insert x s) hs hle).trans
      (by exact_mod_cast Finset.card_insert_le x s))
  have ha : a ≠ 0 := by
    intro hzero
    apply hsmall b (hm (by simp))
    simp [I, hzero]
  have hab : IsRelPrime a b := by
    apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors ha).mpr
    intro d hda hdb hd
    apply hsmall d ((IsLocalRing.mem_maximalIdeal d).mpr hd.not_isUnit)
    apply span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff] at hz
    have hdmem : d ∈ span (↑(insert d s) : Set R) := subset_span (by simp)
    rcases hz with rfl | rfl | hz
    · exact Ideal.mem_of_dvd _ hda hdmem
    · exact Ideal.mem_of_dvd _ hdb hdmem
    · exact subset_span (by simp [hz])
  refine ⟨(IsLeftCancelMulZero.mul_left_cancel_of_ne_zero ha).isSMulRegular, ?_⟩
  apply ((Submodule.quotEquivOfEq _ _ (principal_smul_top a)).isSMulRegular_congr b).mpr
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro x hx
  exact mem_span_singleton.mpr (hab.dvd_of_dvd_mul_left (mem_span_singleton.mp hx))
private theorem cancel_pair [IsDomain R] [UniqueFactorizationMonoid R] {a b x : R}
    (hh : (maximalIdeal R).height = 2) (hrad : (span ({a, b} : Set R)).radical = maximalIdeal R)
    (hx : b * x ∈ span ({a} : Set R)) : x ∈ span ({a} : Set R) := by
  have hp := (parameter_pair (a := a) (b := b) ∅ (by simpa using hrad)
    (by rw [hh]; norm_num)).2
  have hq := ((Submodule.quotEquivOfEq _ _ (principal_smul_top a)).isSMulRegular_congr b).mp hp
  exact mem_of_isSMulRegular_quotient_of_smul_mem hq hx
theorem cancel_triple [IsDomain R] [UniqueFactorizationMonoid R] {a b c x : R}
    (hh : (maximalIdeal R).height = 3) (hrad : (span ({a, b, c} : Set R)).radical = maximalIdeal R)
    (href : ∃ rs : List R, rs.length = 3 ∧
      (∀ z ∈ rs, z ∈ maximalIdeal R) ∧ RingTheory.Sequence.IsRegular R rs)
    (hx : c * x ∈ span ({a, b} : Set R)) : x ∈ span ({a, b} : Set R) := by
  classical
  obtain ⟨ha, hb⟩ := parameter_pair (a := a) (b := b) {c} (by simpa using hrad)
    (by rw [hh]; norm_num)
  obtain ⟨rs, hlen, hmem, hreg⟩ := href
  obtain ⟨r, hr, hregular⟩ := regular_on_pair_quotient ha hb rs hlen hmem hreg
  have hrad' : (span (insert c ({a, b} : Set R))).radical = maximalIdeal R := by
    rw [Set.insert_comm c a, Set.pair_comm c b]
    exact hrad
  have hr' : r ∈ (span (insert c ({a, b} : Set R))).radical := hrad'.symm ▸ hr
  obtain ⟨k, hk⟩ := Ideal.mem_radical_iff.mp hr'
  rw [Ideal.span_insert] at hk
  obtain ⟨v, hv, w, hw, hsum⟩ := Submodule.mem_sup.mp hk
  obtain ⟨t, rfl⟩ := mem_span_singleton.mp hv
  apply mem_of_isSMulRegular_quotient_of_smul_mem (hregular.pow k)
  change r ^ k * x ∈ span ({a, b} : Set R)
  rw [← hsum, add_mul, mul_comm c t, mul_assoc]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ hw)
end LocalRing
theorem remaining_zero {R : Type*} [CommRing R] {n : ℕ}
    (g : Fin (n + 1) → R) : remainingIdeal g 0 = span (Set.range (Fin.tail g)) := by
  unfold remainingIdeal
  congr 1
  ext z
  simp [Set.mem_image, Set.mem_range, Fin.exists_fin_succ, Fin.tail]
theorem reindex_remaining {R ι : Type*} [CommRing R] (f : ι → R)
    (e : ι ≃ ι) (j : ι) : remainingIdeal (f ∘ e) j = remainingIdeal f (e j) := by
  unfold remainingIdeal
  congr 1
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨e k, fun he => hk (e.injective he), rfl⟩
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨l, rfl⟩ := e.surjective k
    exact ⟨l, fun he => hk (congrArg e he), rfl⟩
theorem indexed_cancel {R : Type*} [CommRing R] [IsLocalRing R] {n : ℕ}
    (h : ∀ (g : Fin (n + 1) → R), (span (Set.range g)).radical = maximalIdeal R →
      ∀ x, g 0 * x ∈ remainingIdeal g 0 → x ∈ remainingIdeal g 0)
    (f : Fin (n + 1) → R) (hf : (span (Set.range f)).radical = maximalIdeal R)
    (i : Fin (n + 1)) (x : R) (hx : f i * x ∈ remainingIdeal f i)
    : x ∈ remainingIdeal f i := by
  classical
  let e := Equiv.swap (0 : Fin (n + 1)) i
  have he : e 0 = i := Equiv.swap_apply_left _ _
  have hrem : remainingIdeal (f ∘ e) 0 = remainingIdeal f i := by
    rw [reindex_remaining, he]
  rw [← hrem] at hx ⊢
  exact h (f ∘ e) (by rw [EquivLike.range_comp]; exact hf) x (by simpa only [Function.comp_apply, he] using hx)
theorem proof : K1_13_7_4_2.c1 := by
  classical
  intro n hn q hh f hf i x hx
  have hheight : (maximalIdeal (Local q)).height = n := by
    apply WithBot.coe_inj.mp
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
      IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (Local q), hh]
  rcases hn with rfl | rfl
  · refine indexed_cancel (n := 1) (fun g hg y hy => ?_) f hf i x hx
    rw [remaining_zero, Fin.range_fin_succ] at hy ⊢
    rw [Fin.range_fin_succ, Fin.range_fin_succ] at hg
    simp only [Set.range_eq_empty, ← Set.singleton_def] at hg hy ⊢
    change y ∈ span ({g 1} : Set (Local q))
    apply cancel_pair hheight (a := g 1) (b := g 0) ?_ hy
    change (span ({g 1, g 0} : Set (Local q))).radical = _
    rw [show ({g 1, g 0} : Set (Local q)) = {g 0, g 1} from Set.pair_comm _ _]
    exact hg
  · refine indexed_cancel (n := 2) (fun g hg y hy => ?_) f hf i x hx
    rw [remaining_zero, Fin.range_fin_succ, Fin.range_fin_succ] at hy ⊢
    rw [Fin.range_fin_succ, Fin.range_fin_succ, Fin.range_fin_succ] at hg
    simp only [Set.range_eq_empty, ← Set.singleton_def] at hg hy ⊢
    change y ∈ span ({g 1, g 2} : Set (Local q))
    apply cancel_triple hheight (a := g 1) (b := g 2) (c := g 0) ?_
      (exists_regular_three q hh) hy
    change (span ({g 1, g 2, g 0} : Set (Local q))).radical = _
    rw [Set.pair_comm (g 2) (g 0), Set.insert_comm (g 1) (g 0)]
    exact hg
end K1_13_7_4_2_1
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_3_2_2
open K1_13_6_3_5_3 K1_13_6_3_5_3_2 IsDedekindDomain WithZero
open scoped WithZero
noncomputable section
variable {k L : Type} [Field k] [Field L] [Algebra k L] {x : L}
local notation "A" => ParameterRing k L x
local notation "B" => Normalization k L x
local notation "p" => origin k L x
private abbrev parameter : A := ⟨x, Algebra.self_mem_adjoin_singleton k x⟩
theorem zeroOrder_ne_zero_iff (v : Valuation L ℤᵐ⁰) (hx : x ≠ 0) :
    zeroOrder v x ≠ 0 ↔ v x < 1 := by
  have h := log_lt_iff_lt_exp (a := (0 : ℤ)) (v.ne_zero_iff.mpr hx)
  rw [exp_zero] at h
  unfold zeroOrder
  exact (show (-log (v x)).toNat ≠ 0 ↔ log (v x) < 0 by omega).trans h
private theorem valuation_eq_of_equiv {v w : Valuation L ℤᵐ⁰}
    (hv : Function.Surjective v) (hw : Function.Surjective w) (h : v.IsEquiv w) :
    v = w := by
  have hsmall {z : ℤᵐ⁰} (hz : z < 1) : z ≤ exp (-1 : ℤ) := by
    apply (lt_mul_exp_iff_le (y := exp (-1 : ℤ)) exp_ne_zero).mp
    simpa only [← exp_add, neg_add_cancel, exp_zero] using hz
  obtain ⟨π, hπ⟩ := hv (exp (-1 : ℤ))
  obtain ⟨τ, hτ⟩ := hw (exp (-1 : ℤ))
  have hπw : w π = exp (-1 : ℤ) := by
    apply le_antisymm
    · apply hsmall
      apply h.lt_one_iff_lt_one.mp
      simp [hπ]
    · rw [← hτ, ← h.le_iff_le, hπ]
      apply hsmall
      apply h.lt_one_iff_lt_one.mpr
      simp [hτ]
  ext a
  by_cases ha : a = 0
  · simp [ha]
  · have hpow (u : Valuation L ℤᵐ⁰) (hu : u π = exp (-1 : ℤ)) :
        u (π ^ (-log (v a))) = v a := by
      rw [map_zpow₀, hu, ← exp_zsmul]
      have hs : (-log (v a)) • (-1 : ℤ) = log (v a) := by simp
      rw [hs, exp_log (v.ne_zero_iff.mpr ha)]
    exact (hpow w hπw).symm.trans (h.eq_iff.mp (hpow v hπ))
theorem curvePlace_value_injective :
    Function.Injective (CurvePlace.value (k := k) (L := L)) := by
  rintro ⟨v, hv, hc⟩ ⟨w, hw, hd⟩ h
  change v = w at h
  subst w
  rfl
private theorem chart_le_one (v : ZeroPlaces k L x) (hx : x ≠ 0) (a : A) :
    v.val.value (algebraMap A L a) ≤ 1 := by
  let w := v.val.value
  obtain ⟨a, ha⟩ := a
  change w a ≤ 1
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    have hy' : y = x := Set.mem_singleton_iff.mp hy
    subst y
    exact ((zeroOrder_ne_zero_iff w hx).mp v.property).le
  | algebraMap c =>
    by_cases hc : c = 0
    · simp [hc]
    · exact (v.val.on_constants c hc).le
  | add a b ha hb hwa hwb =>
    exact (w.map_add _ _).trans (max_le hwa hwb)
  | mul a b ha hb hwa hwb =>
    rw [map_mul]
    exact mul_le_one' hwa hwb
private theorem normalization_le_one (v : ZeroPlaces k L x) (hx : x ≠ 0) (b : B) :
    v.val.value (algebraMap B L b) ≤ 1 := by
  let w := v.val.value
  let f : A →+* w.valuationSubring :=
    (algebraMap A L).codRestrict w.valuationSubring.toSubring (chart_le_one v hx)
  let : Algebra A w.valuationSubring := f.toAlgebra
  let : IsScalarTower A w.valuationSubring L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hvalInt : w.Integers w.valuationSubring := Valuation.integer.integers w
  have hb : IsIntegral w.valuationSubring (b.val : L) := IsIntegral.tower_top b.property
  exact hvalInt.isIntegral_iff_v_le_one.mp hb
private def centerMap (v : ZeroPlaces k L x) (hx : x ≠ 0) :
    B →+* v.val.value.valuationSubring :=
  (algebraMap B L).codRestrict v.val.value.valuationSubring.toSubring
    (normalization_le_one v hx)
private def centerIdeal (v : ZeroPlaces k L x) (hx : x ≠ 0) : Ideal B :=
  (IsLocalRing.maximalIdeal v.val.value.valuationSubring).comap (centerMap v hx)
private theorem mem_centerIdeal (v : ZeroPlaces k L x) (hx : x ≠ 0) (b : B) :
    b ∈ centerIdeal v hx ↔ v.val.value (algebraMap B L b) < 1 :=
  v.val.value.mem_maximalIdeal_iff (a := centerMap v hx b)
private def center (v : ZeroPlaces k L x) (hx : Transcendental k x) :
    Ideal.primesOver p B := by
  let P := centerIdeal v hx.ne_zero
  letI : P.IsPrime := (inferInstance :
    (IsLocalRing.maximalIdeal v.val.value.valuationSubring).IsPrime).comap (centerMap v hx.ne_zero)
  refine ⟨P, inferInstance, ⟨(origin_isMaximal hx).eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩⟩
  change Ideal.span {parameter (x := x) (k := k)} ≤ P.under A
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  change algebraMap A B (parameter (x := x) (k := k)) ∈ P
  apply (mem_centerIdeal v hx.ne_zero _).mpr
  exact (zeroOrder_ne_zero_iff v.val.value hx.ne_zero).mp v.property
variable [IsDedekindDomain (Normalization k L x)] [IsFractionRing (Normalization k L x) L]
private def heightOne (hx : Transcendental k x) (P : Ideal.primesOver p B) :
    HeightOneSpectrum B := by
  refine ⟨P.val, P.property.1, ?_⟩
  intro h
  have hmem : algebraMap A B (parameter (x := x) (k := k)) ∈ P.val :=
    (P.val.mem_of_liesOver p _).mp (Ideal.mem_span_singleton_self _)
  rw [h, Ideal.mem_bot] at hmem
  exact hx.ne_zero (congrArg Subtype.val hmem)
def placeOfPrime (hx : Transcendental k x) (P : Ideal.primesOver p B) :
    ZeroPlaces k L x := by
  let w := heightOne hx P
  have hconst : (w.valuation L).IsTrivialOn k :=
    Valuation.IsTrivialOn.of_le_one (w.valuation L)
      (fun c => by
        rw [IsScalarTower.algebraMap_apply k B L c]
        exact w.valuation_le_one (algebraMap k B c))
  refine ⟨⟨w.valuation L, w.valuation_surjective L, hconst.eq_one⟩,
    (zeroOrder_ne_zero_iff (w.valuation L) hx.ne_zero).mpr ?_⟩
  change w.valuation L (algebraMap B L (algebraMap A B (parameter (x := x) (k := k)))) < 1
  exact (w.valuation_lt_one_iff_mem _).mpr
    ((P.val.mem_of_liesOver p _).mp (Ideal.mem_span_singleton_self _))
theorem placeOfPrime_injective (hx : Transcendental k x) :
    Function.Injective (placeOfPrime hx) := by
  intro P Q h
  have hval : (heightOne hx P).valuation L = (heightOne hx Q).valuation L :=
    congrArg (fun v : ZeroPlaces k L x => v.val.value) h
  exact Subtype.ext (congrArg HeightOneSpectrum.asIdeal
    (HeightOneSpectrum.valuation_injective L hval))
theorem placeOfPrime_surjective (hx : Transcendental k x) :
    Function.Surjective (placeOfPrime hx) := by
  intro z
  let v := z.val.value
  let w := heightOne hx (center z hx)
  have hbelow : w.valuationSubringAtPrime L ≤ v.valuationSubring := by
    intro y hy
    rw [w.valuationSubringAtPrime_eq_valuationSubring] at hy
    obtain ⟨a, s, hs⟩ := w.exists_primeCompl_mul_eq_of_integer y hy
    have hsV : v (algebraMap B L s) = 1 :=
      le_antisymm (normalization_le_one z hx.ne_zero s)
        (le_of_not_gt fun h => s.property ((mem_centerIdeal z hx.ne_zero s).mpr h))
    change v y ≤ 1
    have hval := congrArg (fun b : L => v b) hs
    rw [map_mul, hsV, mul_one] at hval
    exact hval.trans_le (normalization_le_one z hx.ne_zero a)
  have hproper : v.valuationSubring ≠ ⊤ := by
    rw [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
    exact (Valuation.isNontrivial_iff_exists_lt_one v).mpr
      ⟨x, hx.ne_zero, (zeroOrder_ne_zero_iff v hx.ne_zero).mp z.property⟩
  have hring := (w.valuationSubringAtPrime_eq_valuationSubring (K := L)).symm.trans
    (ValuationSubring.eq_of_le_of_ne_top _ hbelow hproper)
  have heq := (Valuation.isEquiv_iff_valuationSubring (w.valuation L) v).mpr hring
  refine ⟨center z hx, Subtype.ext (curvePlace_value_injective ?_)⟩
  exact valuation_eq_of_equiv (w.valuation_surjective L) z.val.normalized heq
theorem placeOfPrime_order (hx : Transcendental k x) (P : Ideal.primesOver p B) :
    zeroOrder (placeOfPrime hx P).val.value x = P.val.ramificationIdx A := by
  let w := heightOne hx P
  let b : B := algebraMap A B (parameter (x := x) (k := k))
  have hb : b ≠ 0 := by
    intro h
    exact hx.ne_zero (congrArg Subtype.val h)
  have hspan : Ideal.map (algebraMap A B) p = Ideal.span {b} := by
    simp only [origin, Ideal.map_span, Set.image_singleton, b, parameter]
  have hmap : Ideal.map (algebraMap A B) p ≠ ⊥ := by
    rw [hspan, ne_eq, Ideal.span_singleton_eq_bot]
    exact hb
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity p P.val hmap, hspan]
  change (-log (w.valuation L (algebraMap B L b))).toNat =
    multiplicity w.asIdeal (Ideal.span {b})
  simp only [w.valuation_of_algebraMap, w.intValuation_eq_exp_neg_multiplicity hb,
    log_exp, neg_neg, Int.toNat_natCast]
theorem proof : K1_13_6_3_5_3_2.c2 := by
  intro k L _ _ _ x hx _ _
  let e := Equiv.ofBijective (placeOfPrime hx)
    ⟨placeOfPrime_injective hx, placeOfPrime_surjective hx⟩
  refine ⟨e.symm, fun v => ?_⟩
  have h := placeOfPrime_order hx (e.symm v)
  change zeroOrder (e (e.symm v)).val.value x = _ at h
  simpa only [Equiv.apply_symm_apply] using h
end
end K1_13_6_3_5_3_2_2
end
section
namespace K1_13_4_2_1
open K1_13_4 K1_13_4_2 Finset
open scoped BigOperators
set_option maxHeartbeats 1500000
private def moment (B c a d e : ℕ) : ℕ :=
  jetSum B fun q k l => c + a * (l + 2 * k) + d * (B - q) + e * (B - q) ^ 2
private def raw (b : Bank) : ℕ := moment b.box.b (rawBase b) 1 131071 0
private def extra (B : ℕ) : ℕ := moment B 0 0 2300 1
private def credit (B : ℕ) : ℕ := jetSum B fun q _ _ => 2300 + (B - q)
private theorem grade_sum (B : ℕ) (f : ℕ → ℕ) :
    jetSum B (fun q _ _ => f q) =
      ∑ q ∈ range (B + 1), gradeCount ⟨B, 2300, 1150⟩ q * f q := by
  simp only [jetSum, gradeCount, Nat.reduceDiv, min_self, sum_mul, sum_const,
    card_range, Nat.nsmul_eq_mul]
private theorem pole_eq (b : Bank) : poleDebit b.box = 70001 * credit b.box.b + extra b.box.b := by
  have hb : b.box = ⟨b.box.b, 2300, 1150⟩ := by cases b <;> rfl
  have hgrade (q : ℕ) : gradeCount b.box q = gradeCount ⟨b.box.b, 2300, 1150⟩ q :=
    congrArg (fun a => gradeCount a q) hb
  calc
    _ = jetSum b.box.b (fun q _ _ => (2300 + (b.box.b - q)) * (70001 + (b.box.b - q))) := by
      rw [grade_sum, poleDebit]
      apply sum_congr rfl
      intro q hq
      have hq' := mem_range.mp hq
      have he : b.box.b + b.box.j - q = 2300 + (b.box.b - q) := by
        rw [box_index]
        omega
      rw [hgrade, he]
      ring
    _ = _ := by
      simp only [credit, extra, moment, jetSum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun q _ => sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
      ring
private abbrev Triple := Σ _ : ℕ, Σ _ : ℕ, ℕ
def byGrade (B : ℕ) : Finset Triple :=
  (range (B + 1)).sigma fun q => (range (min q 1150 + 1)).sigma fun k =>
    range (min (q - k) (2300 - 2 * k) + 1)
def byDeficit (B : ℕ) : Finset Triple :=
  (range 1151).sigma fun k => (range (2300 - 2 * k + 1)).sigma fun l =>
    range (B - (k + l) + 1)
set_option linter.constructorNameAsVariable false in
theorem jetSum_deficit {M : Type*} [AddCommMonoid M] {B : ℕ} (hB : 2300 ≤ B)
    (f : ℕ → ℕ → ℕ → M) :
    jetSum B (fun q k l => f k l (B - q)) =
      ∑ k ∈ range 1151, ∑ l ∈ range (2300 - 2 * k + 1),
        ∑ r ∈ range (B - (k + l) + 1), f k l r := by
  calc
    _ = ∑ t ∈ byGrade B, f t.2.1 t.2.2 (B - t.1) := by
      simp only [jetSum, byGrade, sum_sigma]
    _ = ∑ t ∈ byDeficit B, f t.1 t.2.1 t.2.2 := by
      refine sum_nbij' (fun t : Triple => ⟨t.2.1, t.2.2, B - t.1⟩)
        (fun t : Triple => ⟨B - t.2.2, t.1, t.2.1⟩) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
      · rintro ⟨q, k, l⟩ h
        simp only [byGrade, byDeficit, mem_sigma, mem_range, Nat.lt_succ_iff, le_min_iff] at *
        omega
      · rintro ⟨k, l, r⟩ h
        simp only [byGrade, byDeficit, mem_sigma, mem_range, Nat.lt_succ_iff, le_min_iff] at *
        omega
      · rintro ⟨q, k, l⟩ h
        simp only [byGrade, mem_sigma, mem_range] at h
        rw [show B - (B - q) = q by omega]
      · rintro ⟨k, l, r⟩ h
        simp only [byDeficit, mem_sigma, mem_range] at h
        rw [show B - (B - r) = r by omega]
    _ = _ := by simp only [byDeficit, sum_sigma]
def cubicSum (c d e f n : ℤ) : ℤ :=
  12 * c * n + 6 * d * n * (n - 1) + 2 * e * n * (n - 1) * (2 * n - 1) +
    3 * f * n ^ 2 * (n - 1) ^ 2
theorem sum_cubic (c d e f : ℤ) (n : ℕ) :
    12 * (∑ i ∈ range n, (c + d * (i : ℤ) + e * i ^ 2 + f * i ^ 3)) =
      cubicSum c d e f n := by
  induction n with
  | zero => simp [cubicSum]
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    push_cast
    unfold cubicSum
    ring
private def slice (B c a d e k : ℤ) : ℤ :=
  let N := B - k + 1
  let C := c + 2 * a * k
  cubicSum
    (12 * N * C + 6 * d * N * (N - 1) + 2 * e * N * (N - 1) * (2 * N - 1))
    (12 * N * a - 12 * C + 6 * d * (1 - 2 * N) + 2 * e * (-6 * N ^ 2 + 6 * N - 1))
    (-12 * a + 6 * d + 2 * e * (6 * N - 3))
    (-4 * e)
    (2301 - 2 * k)
private theorem sum_slice {B k : ℕ} (hB : 2300 ≤ B) (hk : k < 1151) (c a d e : ℤ) :
    144 * (∑ l ∈ range (2300 - 2 * k + 1), ∑ r ∈ range (B - (k + l) + 1),
      (c + a * ((l : ℤ) + 2 * k) + d * (r : ℤ) + e * (r : ℤ) ^ 2)) =
      slice B c a d e k := by
  let N : ℤ := (B : ℤ) - k + 1
  let C : ℤ := c + 2 * a * k
  have hn : ((2300 - 2 * k + 1 : ℕ) : ℤ) = 2301 - 2 * (k : ℤ) := by omega
  unfold slice
  rw [← hn, ← sum_cubic]
  rw [show (144 : ℤ) = 12 * 12 by decide, mul_assoc, mul_sum]
  congr 1
  apply sum_congr rfl
  intro l hl
  have hl' := mem_range.mp hl
  have hlen : ((B - (k + l) + 1 : ℕ) : ℤ) = N - l := by dsimp [N]; omega
  have hi := sum_cubic (c + a * ((l : ℤ) + 2 * k)) d e 0 (B - (k + l) + 1)
  simp only [zero_mul, add_zero] at hi
  rw [hi, hlen]
  dsimp [N, C, cubicSum]
  ring
private def antidifference (f : ℤ → ℤ) (n : ℤ) : ℤ :=
  n * (120 * f 0 + (n - 1) * (60 * (f 1 - f 0) +
    (n - 2) * (20 * (f 2 - 2 * f 1 + f 0) +
      (n - 3) * (5 * (f 3 - 3 * f 2 + 3 * f 1 - f 0) +
        (n - 4) * (f 4 - 4 * f 3 + 6 * f 2 - 4 * f 1 + f 0)))))
private theorem sum_slices (B c a d e : ℤ) (n : ℕ) :
    120 * (∑ k ∈ range n, slice B c a d e k) =
      antidifference (slice B c a d e) n := by
  have hstep (x : ℤ) :
      antidifference (slice B c a d e) (x + 1) =
        antidifference (slice B c a d e) x + 120 * slice B c a d e x := by
    unfold antidifference slice cubicSum
    ring
  induction n with
  | zero => simp [antidifference]
  | succ n ih => rw [Nat.cast_succ, hstep, sum_range_succ, mul_add, ih]
private theorem evaluate (B c a d e : ℕ) (hB : 2300 ≤ B) :
    17280 * (moment B c a d e : ℤ) =
      antidifference (slice B c a d e) 1151 := by
  have hs : 144 * (moment B c a d e : ℤ) = ∑ k ∈ range 1151, slice B c a d e k := by
    unfold moment
    rw [jetSum_deficit hB (fun k l r => c + a * (l + 2 * k) + d * r + e * r ^ 2)]
    simp only [Nat.cast_sum, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [mul_sum]
    exact sum_congr rfl fun k hk => sum_slice hB (mem_range.mp hk) _ _ _ _
  rw [show (17280 : ℤ) = 120 * 144 by decide, mul_assoc, hs, sum_slices]
  exact congrArg (antidifference (slice B c a d e))
    (show ((1151 : ℕ) : ℤ) = 1151 from by decide)
private theorem moment_eq (B c a d e value : ℕ) (hB : 2300 ≤ B)
    (cert : antidifference (slice B c a d e) 1151 = 17280 * (value : ℤ)) :
    moment B c a d e = value := by
  have h := (evaluate B c a d e hB).trans cert
  omega
set_option maxHeartbeats 300000 in
private theorem bank_moments :
    raw .first = 2823319580182079460 ∧ raw .second = 2845830394728456187 ∧
      extra 6789 = 129644787051371740 ∧ extra 6820 = 131501361258434295 := by
  have h₁ := moment_eq 6789 5737627 1 131071 0 2823319580182079460 (by decide) (by decide)
  have h₂ := moment_eq 6820 4650787 1 131071 0 2845830394728456187 (by decide) (by decide)
  have h₃ := moment_eq 6789 0 0 2300 1 129644787051371740 (by decide) (by decide)
  have h₄ := moment_eq 6820 0 0 2300 1 131501361258434295 (by decide) (by decide)
  have r₁ : rawBase .first = 5737627 := by decide
  have r₂ : rawBase .second = 4650787 := by decide
  have e₁ : raw .first = moment 6789 5737627 1 131071 0 :=
    congrArg (fun base => moment 6789 base 1 131071 0) r₁
  have e₂ : raw .second = moment 6820 4650787 1 131071 0 :=
    congrArg (fun base => moment 6820 base 1 131071 0) r₂
  exact ⟨e₁.trans h₁, e₂.trans h₂, h₃, h₄⟩
set_option maxHeartbeats 300000 in
private theorem endpoint (b : Bank) :
    b.targetRank + 262144 * (70001 * b.nodeRank) + 2600 * extra b.box.b ≤ 70001 * raw b := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := bank_moments
  cases b
  · have hB : Bank.first.box.b = 6789 := rfl
    have he := (congrArg extra hB).trans h₃
    have ha : (1 : ℕ) + 262144 * (70001 * 10697571688375) + 2600 * 129644787051371740 ≤
        70001 * 2823319580182079460 := by decide
    exact (congrArg₂ (fun x y : ℕ =>
      Bank.first.targetRank + 262144 * (70001 * Bank.first.nodeRank) + 2600 * x ≤ 70001 * y)
      he h₁).mpr ha
  · have hB : Bank.second.box.b = 6820 := rfl
    have he := (congrArg extra hB).trans h₄
    have ha : (2561085868844197170227 : ℕ) + 262144 * (70001 * 10697783317215) +
        2600 * 131501361258434295 ≤ 70001 * 2845830394728456187 := by decide
    exact (congrArg₂ (fun x y : ℕ =>
      Bank.second.targetRank + 262144 * (70001 * Bank.second.nodeRank) + 2600 * x ≤ 70001 * y)
      he h₂).mpr ha
end K1_13_4_2_1
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_5_4
noncomputable section
open K1_13_6_3_5_5
variable {S ι : Type} [CommRing S] (P : ι → Ideal S) [∀ i, (P i).IsPrime]
def denominators : Submonoid S := ⨅ i, (P i).primeCompl
theorem mem_denominators {s : S} :
    s ∈ denominators P ↔ ∀ i, s ∉ P i :=
  Submonoid.mem_iInf
abbrev Semilocal := Localization (denominators P)
def toChart (i : ι) : Semilocal P →+* Localization.AtPrime (P i) :=
  IsLocalization.lift (M := denominators P)
    (g := algebraMap S (Localization.AtPrime (P i)))
    (fun s => IsLocalization.map_units _ (⟨s, (mem_denominators P).mp s.2 i⟩ : (P i).primeCompl))
@[simp]
theorem toChart_algebraMap (i : ι) (s : S) :
    toChart P i (algebraMap S (Semilocal P) s) =
      algebraMap S (Localization.AtPrime (P i)) s :=
  IsLocalization.lift_eq _ s
def toSection (J : Ideal S) (i : ι) : Semilocal P →+* LocalSection J (P i) :=
  (Ideal.Quotient.mk _).comp (toChart P i)
theorem disjoint_selected (i : ι) :
    Disjoint (denominators P : Set S) (P i : Set S) :=
  Set.disjoint_left.mpr fun _ hs hp => (mem_denominators P).mp hs i hp
theorem under_selected (i : ι) :
    ((P i).map (algebraMap S (Semilocal P))).under S = P i :=
  IsLocalization.under_map_of_isPrime_disjoint (denominators P) _
    (inferInstance : (P i).IsPrime) (disjoint_selected P i)
theorem selected_maximal [Fintype ι] {J : Ideal S}
    (hP : ∀ i, J.IsMinimalPrime (P i)) (i : ι) :
    ((P i).map (algebraMap S (Semilocal P))).IsMaximal := by
  classical
  let M := denominators P
  let A := Semilocal P
  let E := (P i).map (algebraMap S A)
  have hE : E.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M A (P i) (hP i).isPrime (disjoint_selected P i)
  apply Ideal.isMaximal_def.mpr
  refine ⟨hE.ne_top, Ideal.maximal_of_no_maximal ?_⟩
  intro N hEN hN
  have hd := ((IsLocalization.isPrime_iff_isPrime_disjoint M A N).mp hN.isPrime).2
  have hcover : (N.under S : Set S) ⊆ ⋃ j ∈ (Finset.univ : Finset ι), (P j : Set S) := by
    intro s hs
    have hnot : s ∉ M := fun hm => Set.disjoint_left.mp hd hm hs
    have hex : ∃ j, s ∈ P j := by
      by_contra! hnone
      exact hnot ((mem_denominators P).mpr hnone)
    obtain ⟨j, hj⟩ := hex
    exact Set.mem_iUnion₂.mpr ⟨j, Finset.mem_univ j, hj⟩
  obtain ⟨j, _, hNj⟩ :=
    (Ideal.subset_union_prime (s := Finset.univ) i i
      (f := P) (fun k _ _ _ => (hP k).isPrime)).mp hcover
  have hiN : P i ≤ N.under S :=
    (under_selected P i).symm.trans_le (Ideal.comap_mono hEN.le)
  have hji : P j ≤ P i := (hP j).2 (hP i).1 (hiN.trans hNj)
  exact hEN.not_ge ((IsLocalization.under_le_under_iff M A).mp
    ((hNj.trans hji).trans_eq (under_selected P i).symm))
theorem radical_ker_toSection {J : Ideal S} (i : ι) (h : J.IsMinimalPrime (P i)) :
    (RingHom.ker (toSection P J i)).radical = (P i).map (algebraMap S (Semilocal P)) := by
  let T := Localization.AtPrime (P i)
  let A := Semilocal P
  have hk : RingHom.ker (toSection P J i) =
      (J.map (algebraMap S T)).comap (toChart P i) := by
    unfold toSection
    rw [← RingHom.comap_ker, Ideal.mk_ker]
  rw [hk, ← Ideal.comap_radical, IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
    T (P i) J h, IsLocalization.AtPrime.map_eq_maximalIdeal]
  apply (IsLocalization.orderEmbedding (denominators P) A).injective
  change ((IsLocalRing.maximalIdeal T).comap (toChart P i)).under S =
    ((P i).map (algebraMap S (Semilocal P))).under S
  rw [under_selected P i]
  apply Ideal.ext
  intro s
  change toChart P i (algebraMap S (Semilocal P) s) ∈ IsLocalRing.maximalIdeal T ↔ s ∈ P i
  rw [toChart_algebraMap]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff T (P i) s
theorem toSection_surjective [Fintype ι] {J : Ideal S}
    (hP : ∀ i, J.IsMinimalPrime (P i)) (i : ι) :
    Function.Surjective (toSection P J i) := by
  let A := Semilocal P
  let T := Localization.AtPrime (P i)
  let E := (P i).map (algebraMap S A)
  let g := toSection P J i
  have hE : E.IsMaximal := selected_maximal P hP i
  have hg : (RingHom.ker g).radical = E := radical_ker_toSection P i (hP i)
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (P i).primeCompl (S := T) y
  let d : A := algebraMap S A s
  have hd : d ∉ E := by
    change (s : S) ∉ E.under S
    rw [under_selected P i]
    exact s.2
  have hc : IsCoprime (RingHom.ker g) (Ideal.span {d}) := by
    apply Ideal.coprime_of_no_prime_ge
    intro N hKN hDN hN
    have hEN : E ≤ N := hg ▸ hN.radical_le_iff.mpr hKN
    exact hd (hE.eq_of_le hN.ne_top hEN ▸ hDN (Ideal.mem_span_singleton_self d))
  obtain ⟨r, hr, u, hu, hsum⟩ := hc.exists
  obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.mp hu
  have hv : g v * g d = 1 := by
    simpa only [map_add, map_mul, RingHom.mem_ker.mp hr, zero_add, map_one]
      using congrArg g hsum
  have hfrac : Ideal.Quotient.mk _ (IsLocalization.mk' T a s) * g d =
      g (algebraMap S A a) := by
    change Ideal.Quotient.mk _ (IsLocalization.mk' T a s) *
        Ideal.Quotient.mk _ (toChart P i (algebraMap S (Semilocal P) (s : S))) =
      Ideal.Quotient.mk _ (toChart P i (algebraMap S (Semilocal P) a))
    simpa only [toChart_algebraMap, map_mul]
      using congrArg (Ideal.Quotient.mk (J.map (algebraMap S T))) (IsLocalization.mk'_spec T a s)
  refine ⟨algebraMap S A a * v, ?_⟩
  rw [map_mul, ← hfrac, mul_assoc, mul_comm (g d) (g v), hv, mul_one]
theorem sections_surjective [Fintype ι] {J : Ideal S} (hP : ∀ i, J.IsMinimalPrime (P i))
    (hinj : Function.Injective P) :
    Function.Surjective (fun a : Semilocal P => fun i => toSection P J i a) := by
  let K := fun i => RingHom.ker (toSection P J i)
  let E := fun i => (P i).map (algebraMap S (Semilocal P))
  have hk (i : ι) : (K i).radical = E i := radical_ker_toSection P i (hP i)
  have hm (i : ι) : (E i).IsMaximal := selected_maximal P hP i
  have hc : Pairwise (fun i j => IsCoprime (K i) (K j)) := by
    intro i j hij
    apply Ideal.coprime_of_no_prime_ge
    intro N hKi hKj hN
    have hi : E i ≤ N := hk i ▸ hN.radical_le_iff.mpr hKi
    have hj : E j ≤ N := hk j ▸ hN.radical_le_iff.mpr hKj
    have he : E i = E j :=
      (hm i).eq_of_le hN.ne_top hi |>.trans ((hm j).eq_of_le hN.ne_top hj).symm
    apply hij (hinj ?_)
    exact (under_selected P i).symm.trans
      ((congrArg (fun I : Ideal (Semilocal P) => I.under S) he).trans (under_selected P j))
  intro z
  choose a ha using fun i => toSection_surjective P hP i (z i)
  obtain ⟨r, hr⟩ := Ideal.pi_quotient_surjective hc (fun i => Ideal.Quotient.mk (K i) (a i))
  refine ⟨r, funext fun i => ?_⟩
  let lift := Ideal.Quotient.lift (K i) (toSection P J i) (fun _ h => RingHom.mem_ker.mp h)
  exact (congrArg lift (hr i)).trans (ha i)
end
end K1_13_6_3_5_5_4
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_5_4
noncomputable section
open K1_13_6_3_5_5
theorem proof : K1_13_6_3_5_5.c4 := by
  classical
  intro R S F _ _ _ _ _ _ _ f e he hcomp w q _
  let L := Localization.AtPrime q
  let x : L := algebraMap R L w
  let J : Ideal S := Ideal.span {f w}
  let ι := ↥(fibrePrimes f J q)
  let P : ι → Ideal S := Subtype.val
  let _ : ∀ i : ι, (P i).IsPrime := fibre_prime
  rcases isEmpty_or_nonempty ι with hempty | hnonempty
  · let _ := hempty
    refine ⟨⊥, ?_⟩
    change (∑ i : ι, branchLength f J q i) ≤ _
    simp
  obtain ⟨i₀⟩ := hnonempty
  have hP (i : ι) : J.IsMinimalPrime (P i) :=
    Ideal.mem_minimalPrimesFinset.mp (Finset.mem_filter.mp i.property).1
  let A := Semilocal P
  have hden : q.primeCompl ≤ (denominators P).comap f.toMonoidHom := by
    intro r hr
    apply (mem_denominators P).mpr
    intro i hi
    apply hr
    change r ∈ q
    rw [fibre_comap i]
    exact hi
  let g : L →+* A := IsLocalization.map A f hden
  let _ : Algebra L A := g.toAlgebra
  have hg r : g (algebraMap R L r) = algebraMap S A (f r) :=
    IsLocalization.map_eq _ _
  let lF : L →ₐ[R] F :=
    Localization.mapToFractionRing F q.primeCompl L q.primeCompl_le_nonZeroDivisors
  let _ : Algebra L F := lF.toRingHom.toAlgebra
  let _ : IsScalarTower R L F := IsScalarTower.of_algebraMap_eq fun r => (lF.commutes r).symm
  let _ : IsFractionRing L F :=
    IsFractionRing.isFractionRing_of_isLocalization q.primeCompl L F
      q.primeCompl_le_nonZeroDivisors
  have hu (s : denominators P) : IsUnit (e s) := by
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    have hs : (s : S) = 0 := he (hzero.trans e.map_zero.symm)
    exact (mem_denominators P).mp s.2 i₀ (hs.symm ▸ (P i₀).zero_mem)
  let k : A →+* F := IsLocalization.lift hu
  have hk s : k (algebraMap S A s) = e s := IsLocalization.lift_eq hu s
  have hkinj : Function.Injective k := by
    apply (IsLocalization.lift_injective_iff hu).mpr
    intro s t
    exact ⟨fun hst => (hk s).symm.trans ((congrArg k hst).trans (hk t)),
      fun hst => congrArg _ (he hst)⟩
  let aF : A →ₐ[L] F := {
    __ := k
    commutes' := by
      have hc : k.comp (algebraMap L A) = algebraMap L F := by
        apply IsLocalization.ringHom_ext q.primeCompl
        apply RingHom.ext
        intro r
        change k (g (algebraMap R L r)) = lF (algebraMap R L r)
        rw [hg, hk, lF.commutes]
        exact RingHom.congr_fun hcomp r
      exact RingHom.congr_fun hc }
  let _ : Algebra L (FractionRing L) := OreLocalization.instAlgebra
  let equiv := (FractionRing.algEquiv L F).symm
  let j := equiv.toAlgHom.comp aF
  let B : FractionSubalgebra L := j.range
  let bEquiv : A ≃ₐ[L] B := AlgEquiv.ofInjective j (equiv.injective.comp hkinj)
  let T (i : ι) := Localization.AtPrime (P i)
  let t (i : ι) : L →+* T i := Localization.localRingHom q (P i) f (fibre_comap i)
  let _ : ∀ i : ι, Algebra L (T i) := fun i => (t i).toAlgebra
  let π (i : ι) : A →ₐ[L] LocalSection J (P i) := {
    __ := toSection P J i
    commutes' := by
      have hchart : (toChart P i).comp g = t i := by
        apply IsLocalization.ringHom_ext q.primeCompl
        apply RingHom.ext
        intro r
        change toChart P i (g (algebraMap R L r)) = t i (algebraMap R L r)
        rw [hg, toChart_algebraMap]
        exact (Localization.localRingHom_to_map q (P i) f (fibre_comap i) r).symm
      intro y
      exact congrArg (Ideal.Quotient.mk _) (RingHom.congr_fun hchart y) }
  let φ : B →ₐ[L] (∀ i : ι, LocalSection J (P i)) :=
    (AlgHom.pi π).comp bEquiv.symm.toAlgHom
  have hφ : Function.Surjective φ :=
    (sections_surjective P hP Subtype.val_injective).comp bEquiv.symm.surjective
  have hx : φ (algebraMap L B x) = 0 := by
    rw [φ.commutes]
    funext i
    change Ideal.Quotient.mk (J.map (algebraMap S (T i))) (t i x) = 0
    have hw : t i x = algebraMap S (T i) (f w) :=
      Localization.localRingHom_to_map q (P i) f (fibre_comap i) w
    rw [hw, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
  have hker : Ideal.span {algebraMap L B x} ≤ RingHom.ker φ :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (RingHom.mem_ker.mpr hx))
  let ψ : SectionQuotient x B →ₐ[L] (∀ i : ι, LocalSection J (P i)) :=
    Ideal.Quotient.liftₐ _ φ (fun _ h => RingHom.mem_ker.mp (hker h))
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨b, hb⟩ := hφ z
    exact ⟨Ideal.Quotient.mk _ b, hb⟩
  refine ⟨B, ?_⟩
  change (∑ i : ι, Module.length L (LocalSection J (P i))) ≤
    Module.length L (SectionQuotient x B)
  rw [← Module.length_pi_of_fintype L]
  exact Module.length_le_of_surjective ψ.toLinearMap hψ
end
end K1_13_6_3_5_5_4
end
section
namespace K1_13_4_4_1
noncomputable section
open Polynomial K1 K1_13 K1_13_4
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
private def Bound (d : ℕ) (F : RawRow) : Prop := ∀ m, (F.coeff m).natDegree ≤ d
theorem bound_C {p : GenericSeed[X]} {d : ℕ} (hp : p.natDegree ≤ d) :
    Bound d (MvPolynomial.C p) := by
  classical
  intro m
  rw [MvPolynomial.coeff_C]
  split
  · exact hp
  · simp
theorem bound_mul {d e : ℕ} {F G : RawRow} (hF : Bound d F) (hG : Bound e G) :
    Bound (d + e) (F * G) := by
  classical
  intro m
  rw [MvPolynomial.coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro p _
  exact natDegree_mul_le.trans (Nat.add_le_add (hF p.1) (hG p.2))
theorem bound_sum {ι : Type*} (S : Finset ι) (F : ι → RawRow) {d : ℕ}
    (hF : ∀ i ∈ S, Bound d (F i)) : Bound d (∑ i ∈ S, F i) := by
  intro m
  rw [MvPolynomial.coeff_sum]
  apply natDegree_sum_le_of_forall_le
  exact fun i hi => hF i hi m
theorem bound_pow {d : ℕ} {F : RawRow} (hF : Bound d F) (n : ℕ) :
    Bound (n * d) (F ^ n) := by
  induction n with
  | zero => simpa only [pow_zero, Nat.zero_mul, ← MvPolynomial.C_1] using
      (bound_C (p := (1 : GenericSeed[X])) (by simp) : Bound 0 _)
  | succ n ih => simpa only [pow_succ, Nat.succ_mul] using bound_mul ih hF
theorem bound_prod {ι : Type*} (S : Finset ι) (d : ι → ℕ) (F : ι → RawRow)
    (hF : ∀ i ∈ S, Bound (d i) (F i)) : Bound (∑ i ∈ S, d i) (∏ i ∈ S, F i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, Finset.prod_empty, ← MvPolynomial.C_1] using
      (bound_C (p := (1 : GenericSeed[X])) (by simp) : Bound 0 _)
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact bound_mul (hF i (Finset.mem_insert_self ..))
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))
theorem bound_X (j : Fin 3) : Bound 0 (MvPolynomial.X j) := by
  classical
  intro m
  rw [MvPolynomial.coeff_X]
  split <;> simp
theorem lift_degree (p : Geom[X]) : (K1_13_4.liftX p).natDegree = p.natDegree :=
  natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective Geom GenericSeed) p
private theorem restore_degree {Γ s} (P : PoleData Γ s) (L : ResidueChart P)
    {T : ℕ} {F : PhysicalRow} (hF : TrueCut P.H.natDegree T F) :
    Bound T (restore P L F) := by
  classical
  let h := P.H.natDegree
  have hres : (genericResidue L.numerator L.denominator).natDegree ≤ h :=
    ((natDegree_C_mul_le _ _).trans (natDegree_map_le.trans (Nat.le_of_lt L.small)))
  let v : SeedVar → ℕ := fun i => i.elim 0 (fun _ => h)
  let g : SeedVar → RawRow := fun i => i.elim
    (MvPolynomial.C (Polynomial.C (algebraMap Geom[X] GenericSeed Polynomial.X)))
    (restoredJet P L)
  have hg (i : SeedVar) : Bound (v i) (g i) := by
    cases i with
    | none => exact bound_C (by simp)
    | some i =>
      change Bound h (restoredJet P L i)
      unfold restoredJet
      have hs : Bound h (∑ j : Fin 3, if j.val ≤ i.val then
          MvPolynomial.C (hasseDeriv (i.val - j.val) (K1_13_4.liftX P.H)) *
            MvPolynomial.X j else 0) := by
        apply bound_sum
        intro j _
        split
        · simpa only [Nat.add_zero] using bound_mul
            (bound_C ((natDegree_hasseDeriv_le _ _).trans (by rw [lift_degree]; omega)))
            (bound_X j)
        · intro m
          simp
      intro m
      change ((MvPolynomial.C _ + _ : RawRow).coeff m).natDegree ≤ h
      simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
      exact natDegree_add_le _ _ |>.trans (max_le
        (bound_C ((natDegree_hasseDeriv_le _ _).trans ((Nat.sub_le _ _).trans hres)) m) (hs m))
  change Bound T (MvPolynomial.eval₂ _ g F)
  rw [MvPolynomial.eval₂_eq]
  apply bound_sum
  intro a ha m
  have hp := bound_prod a.support (fun i => a i * v i) (fun i => g i ^ a i)
    (fun i _ => bound_pow (hg i) (a i))
  have hdeg := bound_mul (bound_C (p := (F.coeff a).map (algebraMap Geom GenericSeed))
    (d := (F.coeff a).natDegree) natDegree_map_le) hp m
  apply hdeg.trans
  refine (Nat.add_le_add_left ?_ _).trans (hF a ha)
  change _ ≤ weight h a
  unfold weight Finsupp.sum
  apply Finset.sum_le_sum
  intro i _
  cases i with
  | none => simp [v]
  | some i =>
    change a (some i) * h ≤ (131071 + h - i.val) * a (some i)
    rw [Nat.mul_comm (a (some i))]
    exact Nat.mul_le_mul_right _ (by omega)
abbrev RestoredField := FractionRing (GenericSeed[X])
private abbrev A := MvPolynomial (Fin 3) RestoredField
abbrev intoField : GenericSeed[X] →+* RestoredField := algebraMap _ _
def beforeJets : PhysicalRow →+* A :=
  (MvPolynomial.map intoField).comp
    ((MvPolynomial.map ((Polynomial.mapRingHom (algebraMap Geom[X] GenericSeed)).comp
      (Bivariate.swap (R := Geom)).toRingHom)).comp
      (MvPolynomial.optionEquivRight Geom[X] (Fin 3)).toRingHom)
theorem beforeJets_injective : Function.Injective beforeJets := by
  have hcoeff : Function.Injective ((Polynomial.mapRingHom (algebraMap Geom[X] GenericSeed)).comp
      (Bivariate.swap (R := Geom)).toRingHom) :=
    (Polynomial.map_injective _ (IsFractionRing.injective Geom[X] GenericSeed)).comp
      Bivariate.swap.injective
  exact (MvPolynomial.map_injective _ (IsFractionRing.injective GenericSeed[X] RestoredField)).comp
    ((MvPolynomial.map_injective _ hcoeff).comp
      (MvPolynomial.optionEquivRight Geom[X] (Fin 3)).injective)
theorem restored_injective {Γ s} (P : PoleData Γ s) (L : ResidueChart P) :
    Function.Injective (restored P L) := by
  let c (p : GenericSeed[X]) : A := MvPolynomial.C (intoField p)
  let cInv : A := MvPolynomial.C ((intoField (K1_13_4.liftX P.H))⁻¹)
  let H (i : ℕ) := c (hasseDeriv i (K1_13_4.liftX P.H))
  let R (i : ℕ) := c (hasseDeriv i (genericResidue L.numerator L.denominator))
  let u₀ := cInv * (MvPolynomial.X 0 - R 0)
  let u₁ := cInv * (MvPolynomial.X 1 - R 1 - H 1 * u₀)
  let u₂ := cInv * (MvPolynomial.X 2 - R 2 - H 2 * u₀ - H 1 * u₁)
  let u : Fin 3 → A := ![u₀, u₁, u₂]
  let back : RawRow →+* A := MvPolynomial.eval₂Hom (MvPolynomial.C.comp intoField) u
  have hH : intoField (K1_13_4.liftX P.H) ≠ 0 := by
    simpa only [intoField, K1_13_4.liftX, map_zero] using
      (IsFractionRing.injective GenericSeed[X] RestoredField).ne
        ((P.monic.map (algebraMap Geom GenericSeed)).ne_zero)
  have hc : H 0 * cInv = 1 := by
    simp [H, c, cInv, ← map_mul, hH]
  have hcancel (y : A) : H 0 * (cInv * y) = y := by rw [← mul_assoc, hc, one_mul]
  have hc_back (p : GenericSeed[X]) : back (MvPolynomial.C p) = c p := by
    simp [back, c]
  have hu (i : Fin 3) : back (restoredJet P L i) = MvPolynomial.X i := by
    have hterm (j : Fin 3) : back (if j.val ≤ i.val then
        MvPolynomial.C (hasseDeriv (i.val - j.val) (K1_13_4.liftX P.H)) * MvPolynomial.X j
        else 0) = if j.val ≤ i.val then H (i.val - j.val) * u j else 0 := by
      split
      · rw [map_mul, hc_back]
        simp [back, H]
      · simp
    simp only [restoredJet, map_add, map_sum, hterm, hc_back]
    change R i.val + (∑ j : Fin 3, if j.val ≤ i.val then H (i.val - j.val) * u j else 0) = _
    fin_cases i <;> norm_num [Fin.sum_univ_three, u, u₀, u₁, u₂, hcancel]
  have hopt (F : PhysicalRow) :
      (MvPolynomial.optionEquivRight Geom[X] (Fin 3)).toRingHom F =
        MvPolynomial.optionEquivRight Geom[X] (Fin 3) F := rfl
  have hswap (p : Geom[X][X]) :
      (Bivariate.swap (R := Geom)).toRingHom p = Bivariate.swap p := rfl
  have hcomp : back.comp (restored P L) = beforeJets := by
    apply MvPolynomial.ringHom_ext
    · intro p
      simp only [beforeJets, RingHom.comp_apply, hopt, hswap, MvPolynomial.optionEquivRight_C,
        MvPolynomial.map_C, Polynomial.Bivariate.swap_C, Polynomial.coe_mapRingHom,
        Polynomial.map_map, restored, MvPolynomial.eval₂Hom_C, hc_back]
      rfl
    · rintro (_ | i)
      · simp [beforeJets, restored, hc_back, c, Bivariate.swap_Y]
      · simp only [RingHom.comp_apply, restored, MvPolynomial.eval₂Hom_X', Option.elim_some, hu,
          beforeJets, hopt, MvPolynomial.optionEquivRight_X_some, MvPolynomial.map_X]
  intro F G h
  apply beforeJets_injective
  rw [← hcomp]
  exact congrArg back h
set_option maxRecDepth 4096 in
private theorem endpoint (Γ : Finset K) (s : K → K[X]) (P : PoleData Γ s) (L : ResidueChart P)
    (F : PhysicalRow) (hcut : ∀ m ∈ F.support, (F.coeff m).natDegree + weight P.H.natDegree m <
      polePower * P.H.natDegree)
    (hpole : (MvPolynomial.C (K1_13_4.liftX P.H)) ^ polePower ∣ restore P L F) : F = 0 := by
  apply restored_injective P L
  rw [map_zero, restored_apply]
  have hd := restore_degree P L (T := polePower * P.H.natDegree - 1)
    (F := F) (fun m hm => Nat.le_sub_one_of_lt (hcut m hm))
  rw [← map_pow] at hpole
  obtain ⟨Q, hQ⟩ := hpole
  apply MvPolynomial.ext
  intro m
  change (restore P L F).coeff m = 0
  by_contra hn
  have hcoeff : K1_13_4.liftX P.H ^ polePower ∣ (restore P L F).coeff m := by
    rw [hQ, MvPolynomial.coeff_C_mul]
    exact dvd_mul_right _ _
  have hle := natDegree_le_of_dvd hcoeff hn
  have hmon : (K1_13_4.liftX P.H).Monic := P.monic.map (algebraMap Geom GenericSeed)
  rw [hmon.natDegree_pow, lift_degree] at hle
  have hpos : 0 < polePower * P.H.natDegree :=
    Nat.mul_pos (by decide) P.small.1
  exact (Nat.not_le_of_lt (Nat.sub_lt hpos Nat.zero_lt_one)) (hle.trans (hd m))
end
end K1_13_4_4_1
end
section
set_option autoImplicit false
namespace K1_14_6_1
noncomputable section
open K1 K1_14 K1_14_6 MvPolynomial
open scoped Polynomial BigOperators
local notation "Y" => MvPolynomial.X (R := FX) (none : Option (Fin 2))
private abbrev incl := algebraMap L[X] FX
private abbrev center : FX := incl Polynomial.X
private theorem eval_center (S : K[X]) : (S.map seedEmbedding).eval center = atX S := by
  rw [Polynomial.eval_map]
  change S.eval₂ (incl.comp (Polynomial.C.comp (algebraMap K L))) (incl Polynomial.X) =
    incl (S.map (algebraMap K L))
  rw [← Polynomial.hom_eval₂, ← Polynomial.eval₂_map, Polynomial.eval₂_C_X]
private theorem factorial_ne_zero {n : ℕ} (hn : n < p) : (n.factorial : FX) ≠ 0 := by
  let : CharP FX p := charP_of_injective_ringHom seedEmbedding.injective p
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : ((n+1 : ℕ) : FX) ≠ 0 := by
      intro h
      exact (not_le_of_gt hn) (Nat.le_of_dvd (Nat.succ_pos n) ((CharP.cast_eq_zero_iff FX p _).mp h))
    simpa only [Nat.factorial_succ, Nat.cast_mul] using mul_ne_zero hc (ih (Nat.lt_of_succ_lt hn))
private def weight (x : K) (n : ℕ) : FX :=
  (n.factorial : FX)⁻¹ * (seedEmbedding x - center)^n
private theorem taylor_term (S : K[X]) (x : K) (n : ℕ) (hn : n < p) :
    (Polynomial.taylor center (S.map seedEmbedding)).coeff n * (seedEmbedding x - center)^n =
      derivativeAt S n * weight x n := by
  rw [Polynomial.taylor_coeff, Polynomial.hasseDeriv_map, eval_center]
  have h := congrFun (Polynomial.factorial_smul_hasseDeriv (R := K) n) S
  have hfactor : derivativeAt S n = (n.factorial : FX) * atX (Polynomial.hasseDeriv n S) := by
    dsimp only [derivativeAt]
    rw [← h, LinearMap.smul_apply]
    simp only [nsmul_eq_mul, atX, liftPoly, Polynomial.map_mul,
      Polynomial.map_natCast, map_mul, map_natCast]
  rw [hfactor, weight]
  symm
  calc
    _ = (atX (Polynomial.hasseDeriv n S) * (seedEmbedding x - center)^n) *
        ((n.factorial : FX) * (n.factorial : FX)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ (factorial_ne_zero hn), mul_one]
private theorem eval_taylor {d : ℕ} (hdp : d < p) (S : K[X]) (hS : S.natDegree ≤ d) (x : K) :
    seedEmbedding (S.eval x) = atX S +
      ∑ n ∈ Finset.range d, derivativeAt S (n+1) * weight x (n+1) := by
  have hd : (Polynomial.taylor center (S.map seedEmbedding)).natDegree < d+1 := by
    rw [Polynomial.natDegree_taylor]
    exact (Polynomial.natDegree_map_le.trans hS).trans_lt (Nat.lt_succ_self _)
  calc
    _ = (Polynomial.taylor center (S.map seedEmbedding)).eval (seedEmbedding x - center) := by
      rw [Polynomial.taylor_eval_sub, Polynomial.eval_map_apply]
    _ = _ := by
      rw [Polynomial.eval_eq_sum_range' hd, Finset.sum_range_succ']
      simp only [Polynomial.taylor_coeff_zero, eval_center, pow_zero, mul_one]
      rw [add_comm]
      refine congrArg (fun v : FX => atX S + v) (Finset.sum_congr rfl ?_)
      intro n hn
      exact taylor_term S x _ ((Nat.succ_le_of_lt (Finset.mem_range.mp hn)).trans_lt hdp)
private theorem padding {d n : ℕ} (hn : n ∈ Finset.range d) :
    taylorPower d - (2*n+1) + (2*n+1) = taylorPower d := by
  have hnd := Finset.mem_range.mp hn
  unfold taylorPower
  omega
def valueNumerator (d : ℕ) (f : Biform) (x : K) : Biform :=
  separant f ^ taylorPower d * Y +
    ∑ n ∈ Finset.range d, weight x (n+1) •
      (separant f ^ (taylorPower d - (2*n+1)) * cleared f n)
theorem valueNumerator_bound {d e b : ℕ} {f : Equation}
    (he : 0 < e) (hfe : f.natDegree ≤ e) (hb : SeedBound f b) (x : K) :
    valueNumerator d (flatten f) x ∈ box (ordinateBound d e) (parameterBound d b) := by
  have ha := separant_bound hfe hb
  unfold valueNumerator
  apply (box _ _).add_mem
  · simpa only [ordinateBound, parameterBound, Nat.add_comm, Nat.add_zero] using
      mul_mem_restrictBidegree (box_pow ha (taylorPower d)) ordinate_mem
  · apply sum_mem
    intro n hn
    apply (box _ _).smul_mem
    have hpad := padding hn
    have h := mul_mem_restrictBidegree
      (box_pow ha (taylorPower d - (2*n+1))) (cleared_bound he hfe hb n)
    have hy : (taylorPower d - (2*n+1))*(e-1) + (1+(2*n+1)*(e-1)) = ordinateBound d e := by
      calc
        _ = 1+(taylorPower d - (2*n+1)+(2*n+1))*(e-1) := by ring
        _ = _ := by rw [hpad, ordinateBound]
    rwa [hy, ← Nat.add_mul, hpad, ← parameterBound] at h
theorem eval_valueNumerator {d : ℕ} (hdp : d < p) (f : Biform)
    (z : K) (S : K[X]) (hS : S.natDegree ≤ d) (hf : markEval z S f = 0) (x : K) :
    markEval z S (valueNumerator d f x) =
      markEval z S (separant f ^ taylorPower d) * seedEmbedding (S.eval x) := by
  let ev := markEval z S
  let a := ev (separant f)
  have h : markEval z S Y = atX S := eval_X _
  simp only [valueNumerator, map_add, map_mul, map_pow, map_sum]
  rw [h, eval_taylor hdp S hS, mul_add, Finset.mul_sum]
  refine congrArg (_ + ·) (Finset.sum_congr rfl ?_)
  intro n hn
  rw [MvPolynomial.smul_eq_C_mul, map_mul, eval_C, map_mul, map_pow, eval_cleared _ _ _ hf]
  have hpad := padding hn
  change weight x (n+1) * (a ^ (taylorPower d - (2*n+1)) *
    (a ^ (2*n+1) * derivativeAt S (n+1))) = a ^ taylorPower d * _
  have hp : a ^ (taylorPower d - (2*n+1)) * a ^ (2*n+1) = a ^ taylorPower d := by
    rw [← pow_add, hpad]
  calc
    _ = (a ^ (taylorPower d - (2*n+1)) * a ^ (2*n+1)) *
        (derivativeAt S (n+1) * weight x (n+1)) := by ring
    _ = _ := by rw [hp]
theorem proof : K1_14_6.c1 := by
  intro d e b _hd hdp f hf hfe hb
  have he := hf.trans_le hfe
  refine ⟨⟨separant (flatten f) ^ taylorPower d, valueNumerator d (flatten f), ?_,
    valueNumerator_bound he hfe hb⟩, ?_⟩
  · exact mem_restrictBidegree_mono (box_pow (separant_bound hfe hb) (taylorPower d))
      (by unfold ordinateBound; omega) le_rfl
  · intro z S hS hz hsep
    constructor
    · change markEval z S (separant (flatten f) ^ taylorPower d) ≠ 0
      rw [map_pow, eval_separant]
      exact pow_ne_zero _ hsep
    · exact eval_valueNumerator hdp (flatten f) z S hS ((eval_flatten z S f).trans hz)
end
end K1_14_6_1
end
section
set_option autoImplicit false
namespace K1_13_5_4_3_3
noncomputable section
open K1_13 K1_13_5 K1_13_5_4 Polynomial
open RingTheory.Sequence
open scoped Pointwise
private theorem mem_smul_top_iff_dvd {R : Type*} [CommRing R] (f x : R) :
    x ∈ f • (⊤ : Submodule R R) ↔ f ∣ x := by
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and, smul_eq_mul]
  exact exists_congr fun _ => eq_comm
attribute [local instance] MvPolynomial.algebraMvPolynomial in
private theorem generic_cut_regular {f g : Row 3} (hf : Irreducible f) (hg : ¬ f ∣ g) :
    ∀ x : GeoRow 3, genericRow f ∣ genericRow g * x → genericRow f ∣ x := by
  have hfPrime : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.mp hf
  have hreg : IsWeaklyRegular (Row 3) [f, g] := by
    rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff]
    refine ⟨mul_right_injective₀ hf.ne_zero, ?_⟩
    apply (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr
    intro x hx
    exact (mem_smul_top_iff_dvd f x).mpr
      ((hfPrime.dvd_mul.mp ((mem_smul_top_iff_dvd f (g * x)).mp hx)).resolve_left hg)
  let _ : Algebra Geom[X] GeometricX := genericCoeff.toAlgebra
  let _ : Module.IsTorsionFree Geom[X] GeometricX :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr genericCoeff_injective
  have : Module.Flat (Row 3) (GeoRow 3) :=
    Module.Flat.of_linearEquiv
      (Algebra.IsPushout.equiv Geom[X] (Row 3) GeometricX (GeoRow 3)).symm.toLinearEquiv
  have hgeo := hreg.of_flat (S := GeoRow 3)
  change IsWeaklyRegular (GeoRow 3) [genericRow f, genericRow g] at hgeo
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff] at hgeo
  intro x hx
  exact (mem_smul_top_iff_dvd _ _).mp
    (mem_of_isSMulRegular_quotient_of_smul_mem hgeo.2 ((mem_smul_top_iff_dvd _ _).mpr hx))
end
end K1_13_5_4_3_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
namespace K1_14_3R_3_4
noncomputable section
open Polynomial
def lineSubstitution {k D : Type*} [Field k] [CommRing D] [Algebra k D]
    (y v : D) : Polynomial (Polynomial k) →+* Polynomial D :=
  eval₂RingHom
    (eval₂RingHom (C.comp (algebraMap k D)) (C y + Polynomial.X * C v)) Polynomial.X
@[simp] private theorem lineSubstitution_C {k D : Type*} [Field k] [CommRing D] [Algebra k D]
    (y v : D) (p : Polynomial k) :
    lineSubstitution (k := k) y v (C p) =
      p.eval₂ (C.comp (algebraMap k D)) (C y + Polynomial.X * C v) := by
  simp [lineSubstitution]
@[simp] private theorem lineSubstitution_X {k D : Type*} [Field k] [CommRing D] [Algebra k D]
    (y v : D) : lineSubstitution (k := k) y v Polynomial.X = Polynomial.X := by
  simp [lineSubstitution]
private def parameterIndex : Fin 4 ≃ Fin 2 ⊕ Fin 2 :=
  Equiv.ofBijective ![.inl 0, .inr 1, .inl 1, .inr 0] (by constructor <;> decide)
def parameterEquiv :
    MvPolynomial (Fin 4) K1_14.FX ≃ₐ[K1_14.FX]
      MvPolynomial (Fin 2) (Polynomial (Polynomial K1_14.FX)) :=
  ((MvPolynomial.renameEquiv _ parameterIndex).trans
    (MvPolynomial.sumAlgEquiv _ _ _)).trans
    (MvPolynomial.mapAlgEquiv _ (Bivariate.equivMvPolynomial _).symm)
def parameterMap {D : Type*} [CommRing D] [Algebra K1_14.FX D] (y v : D) :
    MvPolynomial (Fin 4) K1_14.FX →+* MvPolynomial (Fin 2) (Polynomial D) :=
  (MvPolynomial.map (lineSubstitution y v)).comp parameterEquiv.toRingHom
@[simp] theorem parameterMap_C {D : Type*} [CommRing D] [Algebra K1_14.FX D]
    (y v : D) (x : K1_14.FX) :
    parameterMap y v (MvPolynomial.C x) = MvPolynomial.C (C (algebraMap K1_14.FX D x)) := by
  simp [parameterMap, parameterEquiv, lineSubstitution]
@[simp] theorem parameterMap_slope {D : Type*} [CommRing D] [Algebra K1_14.FX D] (y v : D) :
    parameterMap y v (MvPolynomial.X 1) = MvPolynomial.C Polynomial.X := by
  have h : parameterIndex 1 = .inr 1 := rfl
  simp [parameterMap, parameterEquiv, h]
@[simp] theorem parameterMap_offset {D : Type*} [CommRing D] [Algebra K1_14.FX D] (y v : D) :
    parameterMap y v (MvPolynomial.X 3) = MvPolynomial.C (C y + Polynomial.X * C v) := by
  have h : parameterIndex 3 = .inr 0 := rfl
  simp [parameterMap, parameterEquiv, h]
end
end K1_14_3R_3_4
end
section
set_option autoImplicit false
set_option maxRecDepth 1500
namespace K1_13_6_3_3_2
noncomputable section
open Polynomial K1_13 K1_13_6 K1_13_6_3
open scoped BigOperators
private def universalPolynomial : CoeffRing[X] :=
  ∑ j : Fin taylorLength, monomial j.val (MvPolynomial.X j)
def universalJets : Row 4 →+* CoeffRing[X] :=
  MvPolynomial.eval₂Hom (Polynomial.mapRingHom MvPolynomial.C)
    (fun i : Fin 4 => hasseDeriv i.val universalPolynomial)
private def evaluateFresh : CoeffRing[X] →+* FreshCoeffRing :=
  Polynomial.eval₂RingHom (MvPolynomial.map geomConstants) (MvPolynomial.C genericArgument)
private theorem evaluateFresh_hasse (i : ℕ) :
    evaluateFresh (hasseDeriv i universalPolynomial) = jetLinear genericArgument i := by
  classical
  simp only [universalPolynomial, map_sum, jetLinear]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hasseDeriv_monomial]
  simp only [evaluateFresh, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
    map_mul, map_natCast, MvPolynomial.map_X, map_pow]
  ac_rfl
private theorem evaluateFresh_row (R : Row 4) :
    evaluateFresh (universalJets R) = freshJetMap (toGeneric R) := by
  change (evaluateFresh.comp universalJets) R =
    (freshJetMap.comp (MvPolynomial.map genericCoeffs)) R
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, universalJets, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C,
      freshJetMap]
    change Polynomial.eval₂ (MvPolynomial.map geomConstants) (MvPolynomial.C genericArgument)
        (a.map MvPolynomial.C) = MvPolynomial.C (genericCoeffs a)
    have hm : (MvPolynomial.map geomConstants).comp (MvPolynomial.C : Geom →+* CoeffRing) =
        (MvPolynomial.C : GeoField →+* FreshCoeffRing).comp geomConstants := by
      ext b
      simp
    rw [Polynomial.eval₂_map, hm, ← Polynomial.hom_eval₂]
    have hx : Polynomial.eval₂RingHom geomConstants genericArgument = genericCoeffs := by
      apply Polynomial.ringHom_ext
      · intro b
        exact Polynomial.eval₂_C _ _
      · exact Polynomial.eval₂_X _ _
    change MvPolynomial.C ((Polynomial.eval₂RingHom geomConstants genericArgument) a) = _
    rw [hx]
  · intro i
    simpa only [RingHom.comp_apply, universalJets, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X,
      freshJetMap] using evaluateFresh_hasse i.val
private def pointPolynomial {n : ℕ} (a : Fin n → Geom) : Geom[X] :=
  ∑ j : Fin n, monomial j.val (a j)
private theorem pointPolynomial_coeff {n : ℕ} (a : Fin n → Geom) (i : Fin n) :
    (pointPolynomial a).coeff i.val = a i := by
  classical
  rw [pointPolynomial, Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
  · exact coeff_monomial_same _ _
  · intro j _ hj
    exact coeff_monomial_of_ne _ (fun he => hj (Fin.ext he.symm))
  · simp
theorem pointPolynomial_degree (a : Fin taylorLength → Geom) :
    (pointPolynomial a).natDegree < taylorLength := by
  apply (natDegree_sum_le_of_forall_le _ _ (n := taylorLength - 1) ?_).trans_lt
    (by decide : taylorLength - 1 < taylorLength)
  intro j _
  exact (natDegree_monomial_le _).trans (by have := j.isLt; omega)
theorem map_universal_row (a : Fin taylorLength → Geom) (R : Row 4) :
    (universalJets R).map (MvPolynomial.eval a) = atJet R (pointPolynomial a) := by
  have hU : universalPolynomial.map (MvPolynomial.eval a) = pointPolynomial a := by
    simp [universalPolynomial, pointPolynomial, Polynomial.map_sum]
  change ((Polynomial.mapRingHom (MvPolynomial.eval a)).comp universalJets) R =
    MvPolynomial.eval (jet (pointPolynomial a)) R
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply, universalJets, MvPolynomial.eval₂Hom_C,
      MvPolynomial.eval_C, Polynomial.coe_mapRingHom, Polynomial.map_map]
    have h : (MvPolynomial.eval a).comp (MvPolynomial.C : Geom →+* CoeffRing) =
        RingHom.id Geom := RingHom.ext fun x => MvPolynomial.eval_C x
    rw [h, Polynomial.map_id]
  · intro i
    simp only [RingHom.comp_apply, universalJets, MvPolynomial.eval₂Hom_X', MvPolynomial.eval_X,
      Polynomial.coe_mapRingHom, ← hasseDeriv_map, hU, jet]
def freshPoint (a : Fin taylorLength → Geom) : FreshCoeffRing →+* GeoField :=
  MvPolynomial.eval (geomConstants ∘ a)
theorem freshPoint_comp (a : Fin taylorLength → Geom) :
    (freshPoint a).comp (MvPolynomial.map geomConstants) =
      geomConstants.comp (MvPolynomial.eval a) := by
  apply MvPolynomial.ringHom_ext <;> intro b <;> simp [freshPoint]
theorem freshPoint_evaluateFresh (a : Fin taylorLength → Geom) :
    (freshPoint a).comp evaluateFresh =
      genericCoeffs.comp (Polynomial.mapRingHom (MvPolynomial.eval a)) := by
  apply Polynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply, evaluateFresh, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C, Polynomial.coe_mapRingHom, Polynomial.map_C]
    exact RingHom.congr_fun (freshPoint_comp a) b
  · simp [evaluateFresh, freshPoint, genericArgument]
theorem extend_le_point_ker {A : CoeffIdeal} {a : Fin taylorLength → Geom}
    (ha : a ∈ MvPolynomial.zeroLocus Geom A) : extendIdeal A ≤ RingHom.ker (freshPoint a) := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro b hb
  change ((freshPoint a).comp (MvPolynomial.map geomConstants)) b = 0
  rw [freshPoint_comp, RingHom.comp_apply]
  have h : MvPolynomial.eval a b = 0 := ha b hb
  rw [h, map_zero]
theorem point_chart {A : CoeffIdeal} {g : Row 4}
    (hg : toGeneric g ∈ freshImage A) {a : Fin taylorLength → Geom}
    (ha : a ∈ MvPolynomial.zeroLocus Geom A) : atJet g (pointPolynomial a) = 0 := by
  change freshJetMap (toGeneric g) ∈ extendIdeal A at hg
  rw [← evaluateFresh_row] at hg
  have hz : ((freshPoint a).comp evaluateFresh) (universalJets g) = 0 :=
    extend_le_point_ker ha hg
  rw [freshPoint_evaluateFresh, RingHom.comp_apply, Polynomial.coe_mapRingHom,
    map_universal_row] at hz
  have hinj : Function.Injective genericCoeffs :=
    (algebraMap GenericField GeoField).injective.comp (IsFractionRing.injective Geom[X] GenericField)
  exact hinj (hz.trans (map_zero _).symm)
theorem fresh_mem_of_points {A : CoeffIdeal} (hA : A.IsPrime) (T : CoeffRing[X])
    (hT : ∀ a ∈ MvPolynomial.zeroLocus Geom A, T.map (MvPolynomial.eval a) = 0) :
    evaluateFresh T ∈ extendIdeal A := by
  have hc (n : ℕ) : T.coeff n ∈ A := by
    rw [← hA.radical, ← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := Geom)]
    intro a ha
    change MvPolynomial.eval a (T.coeff n) = 0
    rw [← Polynomial.coeff_map, hT a ha, coeff_zero]
  rw [congrArg evaluateFresh T.as_sum_range, map_sum]
  apply Ideal.sum_mem
  intro n _
  rw [evaluateFresh, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hc n))
private def exponent : ℕ := 2 * taylorLength
private def clearedJet (g : Row 4) (j : Fin taylorLength) : Row 4 :=
  MvPolynomial.C (Polynomial.C (↑j.val.factorial : Geom)⁻¹) *
    (separant g ^ (2 * (taylorLength - j.val)) * jetNumerator g j.val)
theorem atJet_clearedJet (g : Row 4) (S : Geom[X]) (hg : atJet g S = 0)
    (j : Fin taylorLength) :
    atJet (clearedJet g j) S = atJet (separant g) S ^ exponent * hasseDeriv j.val S := by
  have hOrd : derivative^[j.val] S = Polynomial.C (j.val.factorial : Geom) * hasseDeriv j.val S := by
    have h := congrFun (factorial_smul_hasseDeriv (R := Geom) (k := j.val)) S
    change j.val.factorial • (hasseDeriv j.val S) = derivative^[j.val] S at h
    simpa only [nsmul_eq_mul, C_eq_natCast] using h.symm
  have hFact : (j.val.factorial : Geom) ≠ 0 :=
    K1_13_7_1.factorial_cast_ne_zero (j.isLt.trans (by decide : taylorLength < K1.p))
  have hinv : Polynomial.C (↑j.val.factorial : Geom)⁻¹ *
      Polynomial.C (↑j.val.factorial : Geom) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hFact, map_one]
  let E := MvPolynomial.eval (jet S : Fin 4 → Geom[X])
  change E (_ * (_ ^ _ * _)) = _
  rw [map_mul, map_mul, map_pow, MvPolynomial.eval_C]
  change _ * (atJet (separant g) S ^ (2 * (taylorLength - j.val)) *
    atJet (jetNumerator g j.val) S) = _
  rw [eval_jetNumerator _ _ hg, hOrd]
  calc
    _ = (Polynomial.C (↑j.val.factorial : Geom)⁻¹ * Polynomial.C (↑j.val.factorial : Geom)) *
        ((atJet (separant g) S ^ (2 * (taylorLength - j.val)) *
          atJet (separant g) S ^ (2 * j.val)) * hasseDeriv j.val S) := by ac_rfl
    _ = _ := by
      rw [hinv, one_mul, ← pow_add, ← Nat.mul_add, Nat.sub_add_cancel j.isLt.le, exponent]
def translatedCoefficient {L : ℕ} (b : Fin L → Row 4) (i : Fin L) : Row 4 :=
  (taylor (-MvPolynomial.C (Polynomial.X : Geom[X]))
    (∑ j : Fin L, monomial j.val (b j))).coeff i.val
theorem atJet_translatedCoefficient {L : ℕ} (b : Fin L → Row 4) {S : Geom[X]}
    (hd : S.natDegree < L) (d : Geom[X])
    (hb : ∀ j, atJet (b j) S = d * hasseDeriv j.val S) (i : Fin L) :
    atJet (translatedCoefficient b i) S = Polynomial.C (S.coeff i.val) * d := by
  let E := MvPolynomial.eval (jet S : Fin 4 → Geom[X])
  let T := taylor (Polynomial.X : Geom[X]) (S.map (Polynomial.C : Geom →+* Geom[X]))
  have hcoeff (n : ℕ) : T.coeff n = hasseDeriv n S := by
    change (taylor _ _).coeff n = _
    rw [taylor_coeff, hasseDeriv_map, eval_map, eval₂_C_X]
  have hT : T.natDegree < L := by
    change (taylor _ _).natDegree < _
    rw [natDegree_taylor]
    exact natDegree_map_le.trans_lt hd
  have hsum : (∑ j : Fin L, monomial j.val (hasseDeriv j.val S)) = T := by
    simp only [← hcoeff]
    rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => monomial n (T.coeff n))]
    exact (T.as_sum_range' _ hT).symm
  have hmap : (∑ j : Fin L, monomial j.val (b j)).map E =
      Polynomial.C d * T := by
    rw [← hsum, Finset.mul_sum, Polynomial.map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    calc
      _ = monomial j.val (atJet (b j) S) := Polynomial.map_monomial E
      _ = monomial j.val (d * hasseDeriv j.val S) := congrArg (monomial j.val) (hb j)
      _ = _ := Polynomial.C_mul_monomial.symm
  change E (translatedCoefficient b i) = _
  rw [translatedCoefficient, ← Polynomial.coeff_map, Polynomial.map_taylor, map_neg,
    MvPolynomial.eval_C, hmap, taylor_mul, taylor_C]
  dsimp only [T]
  rw [taylor_taylor, neg_add_cancel,
    taylor_zero, Polynomial.coeff_C_mul, Polynomial.coeff_map, mul_comm]
theorem evaluateFresh_relation (i : Fin taylorLength) (D U : Row 4) (n : ℕ) :
    evaluateFresh (Polynomial.C (MvPolynomial.X i) * universalJets D ^ n - universalJets U) =
      MvPolynomial.X i * freshJetMap (toGeneric D) ^ n - freshJetMap (toGeneric U) := by
  have hx : evaluateFresh (Polynomial.C (MvPolynomial.X i)) = MvPolynomial.X i := by
    rw [evaluateFresh, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, MvPolynomial.map_X]
  simp only [map_sub, map_mul, map_pow, evaluateFresh_row, hx]
theorem recovery_of_trajectory (g D U : Row 4) (i : Fin taylorLength) (n : ℕ)
    (hU : ∀ S : Geom[X], S.natDegree < taylorLength → atJet g S = 0 →
      atJet U S = Polynomial.C (S.coeff i.val) * atJet D S ^ n)
    {A : CoeffIdeal} (hp : A.IsPrime) (hg : toGeneric g ∈ freshImage A) :
    MvPolynomial.X i * freshJetMap (toGeneric D) ^ n - freshJetMap (toGeneric U) ∈
      extendIdeal A := by
  let T : CoeffRing[X] :=
    Polynomial.C (MvPolynomial.X i) * universalJets D ^ n - universalJets U
  have hEq : evaluateFresh T =
      MvPolynomial.X i * freshJetMap (toGeneric D) ^ n - freshJetMap (toGeneric U) :=
    evaluateFresh_relation i D U n
  rw [← hEq]
  apply fresh_mem_of_points hp
  intro a ha
  change (Polynomial.mapRingHom (MvPolynomial.eval a)) T = 0
  simp only [T, map_sub, map_mul, map_pow, Polynomial.coe_mapRingHom, Polynomial.map_C,
    MvPolynomial.eval_X, map_universal_row]
  rw [hU _ (pointPolynomial_degree a) (point_chart hg ha), pointPolynomial_coeff, sub_self]
theorem proof : K1_13_6_3_3.c2 := by
  intro g i
  let u := translatedCoefficient (clearedJet g) i
  refine ⟨toGeneric u, exponent, fun A hp _ hg _ => ?_⟩
  apply recovery_of_trajectory g (separant g) u i exponent _ hp hg
  intro S hd hS
  exact atJet_translatedCoefficient (clearedJet g) hd _
    (atJet_clearedJet g S hS) i
end
end K1_13_6_3_3_2
end
section
set_option autoImplicit false
namespace K1_13_7_2_3_1_2_2
open K1_13 K1_13_6_2_3 K1_13_6_2_3_1 K1_13_6_2_3_2 K1_13_7_1
open K1_13_6_2_3_2_5 (shapeSum_add shapeSum_step)
open scoped BigOperators Pointwise
theorem cap_add_weak {p q : Shape} (hp : Chamber p) (hq : Chamber q) :
    capExponents p + capExponents q = capExponents (p.plus q) := by
  ext e
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    simp only [cap_coords, Shape.plus, Finsupp.add_apply] at *
    omega
  · intro he
    obtain ⟨hpb, hpj⟩ := hp
    obtain ⟨hqb, hqj⟩ := hq
    rw [cap_coords] at he
    simp only [Shape.plus] at he
    let z := min (e 3) (2 * p.t)
    let z' := e 3 - z
    have hz : z + z' = e 3 ∧ z ≤ 2 * p.t ∧ z' ≤ 2 * q.t := by dsimp [z, z']; omega
    let w := 2 * p.j - 3 * z
    let w' := 2 * q.j - 3 * z'
    have hw : w + 3 * z = 2 * p.j ∧ w' + 3 * z' = 2 * q.j := by
      dsimp [w, w']
      omega
    have hhalf : (w + w') / 2 = w / 2 + w' / 2 := by
      by_cases h : e 3 ≤ 2 * p.t
      · have hz' : z' = 0 := by dsimp [z, z']; omega
        omega
      · have hze : z = 2 * p.t := min_eq_right (by omega)
        omega
    let y := min (e 2) (w / 2)
    let y' := e 2 - y
    have hy : y + y' = e 2 ∧ 2 * y ≤ w ∧ 2 * y' ≤ w' := by dsimp [y, y']; omega
    let x := min (e 1) (w - 2 * y)
    let x' := e 1 - x
    have hx : x + x' = e 1 ∧ x + 2 * y ≤ w ∧ x' + 2 * y' ≤ w' := by
      dsimp [x, x']
      omega
    let u := min (e 0) (2 * p.b - (x + y + z))
    let u' := e 0 - u
    have hu : u + u' = e 0 ∧ u + x + y + z ≤ 2 * p.b ∧
        u' + x' + y' + z' ≤ 2 * q.b := by
      dsimp [u, u']
      omega
    let a : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![u, x, y, z]
    let b : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![u', x', y', z']
    refine ⟨a, (cap_coords p a).mpr ?_, b, (cap_coords q b).mpr ?_, ?_⟩
    · change u + x + y + z ≤ 2 * p.b ∧ x + 2 * y + 3 * z ≤ 2 * p.j ∧ z ≤ 2 * p.t
      omega
    · change u' + x' + y' + z' ≤ 2 * q.b ∧ x' + 2 * y' + 3 * z' ≤ 2 * q.j ∧ z' ≤ 2 * q.t
      omega
    · ext i
      fin_cases i
      · exact hu.1
      · exact hx.1
      · exact hy.1
      · exact hz.1
private theorem slot_degree_ne_zero {ι : Type} [DecidableEq ι] (shapes : ι → Shape)
    (e : CapVar shapes →₀ ℕ) (i : ι) :
    Finsupp.weight (step ∘ capSlot shapes) e i ≠ 0 ↔
      ∃ v : CapVar shapes, v.1 = i ∧ e v ≠ 0 := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Function.comp_apply,
    capSlot, step, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, Nat.cast_id]
  rw [← Nat.pos_iff_ne_zero, Finset.sum_pos_iff]
  constructor
  · rintro ⟨v, _, hv⟩
    by_cases hvi : v.1 = i
    · exact ⟨v, hvi, Nat.ne_of_gt (by simpa [hvi] using hv)⟩
    · rw [Pi.single_eq_of_ne (Ne.symm hvi)] at hv
      simp at hv
  · rintro ⟨v, hvi, hv⟩
    exact ⟨v, Finsupp.mem_support_iff.mpr hv, by simpa [hvi] using Nat.pos_of_ne_zero hv⟩
private theorem productExponents_zero {ι : Type} [DecidableEq ι] (shapes : ι → Shape) :
    productExponents shapes 0 = 0 := by
  ext m
  simp only [Set.mem_zero, productExponents, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨e, hdeg, hexp⟩
    have he : e = 0 := by
      ext v
      rw [Finsupp.zero_apply]
      by_contra hv
      have hslot := (slot_degree_ne_zero shapes e v.1).mpr ⟨v, rfl, hv⟩
      simp [hdeg] at hslot
    simpa [he] using hexp.symm
  · rintro rfl
    exact ⟨0, map_zero _, map_zero _⟩
private theorem productExponents_add_step {ι : Type} [DecidableEq ι] (shapes : ι → Shape)
    (a : ι → ℕ) (i : ι) :
    productExponents shapes (a + step i) =
      productExponents shapes a + capExponents (shapes i) := by
  ext m
  constructor
  · rintro ⟨e, hdeg, hexp⟩
    have hne : Finsupp.weight (step ∘ capSlot shapes) e i ≠ 0 := by
      simp [hdeg, step]
    obtain ⟨v, hvi, hv⟩ := (slot_degree_ne_zero shapes e i).mp hne
    let e' := e - Finsupp.single v 1
    have hdeg' : Finsupp.weight (step ∘ capSlot shapes) e' + step i = a + step i := by
      have h := Finsupp.weight_sub_single_add (w := step ∘ capSlot shapes) hv
      calc
        _ = Finsupp.weight (step ∘ capSlot shapes) e := by
          simpa only [e', Function.comp_apply, capSlot, hvi] using h
        _ = _ := hdeg
    refine ⟨Finsupp.weight (fun u : CapVar shapes => u.2.val) e',
      ⟨e', add_right_cancel hdeg', rfl⟩, v.2.val, ?_, ?_⟩
    · simpa only [hvi] using v.2.property
    · exact (Finsupp.weight_sub_single_add hv).trans hexp
  · rintro ⟨m', ⟨e, hdeg, hexp⟩, w, hw, rfl⟩
    let v : CapVar shapes := ⟨i, ⟨w, hw⟩⟩
    refine ⟨e + Finsupp.single v 1, ?_, ?_⟩
    · rw [map_add, Finsupp.weight_single, one_smul, hdeg]
      rfl
    · simp only [map_add, Finsupp.weight_single, one_smul, hexp, v]
private theorem capExponents_zero : capExponents ⟨0, 0, 0⟩ = 0 := by
  ext m
  simp only [cap_coords, Set.mem_zero, Nat.mul_zero]
  constructor
  · intro hm
    have h := hm.1
    ext k
    fin_cases k
    · change m 0 = 0; omega
    · change m 1 = 0; omega
    · change m 2 = 0; omega
    · change m 3 = 0; omega
  · rintro rfl
    simp
theorem shapeSum_chamber {ι : Type} [Fintype ι] (s : ι → Shape)
    (hs : ∀ i, Chamber (s i)) (a : ι → ℕ) : Chamber (shapeSum s a) := by
  refine ⟨Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left (a i) (hs i).1), ?_⟩
  change 3 * (∑ i, a i * (s i).t) ≤ ∑ i, a i * (s i).j
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Nat.mul_left_comm 3]
  exact Nat.mul_le_mul_left (a i) (hs i).2
theorem weak_packing {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι → Shape) (hs : ∀ i, Chamber (s i)) (a : ι → ℕ) :
    productExponents s a = capExponents (shapeSum s a) := by
  induction a using WellFounded.induction (measure (fun b : ι → ℕ => ∑ i, b i)).wf with
  | h a ih =>
    by_cases ha : a = 0
    · rw [ha, productExponents_zero]
      simpa [shapeSum] using capExponents_zero.symm
    · obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
        by_contra! h
        exact ha (funext h)
      let b := a - step i
      have hab : b + step i = a := by
        funext k
        change a k - step i k + step i k = a k
        apply Nat.sub_add_cancel
        by_cases hki : k = i
        · subst k
          simpa [step] using Nat.one_le_iff_ne_zero.mpr hi
        · simp [step, Pi.single_eq_of_ne hki]
      have hone : (∑ k, step i k) = 1 := by
        rw [Fintype.sum_eq_single i]
        · simp [step]
        · intro k hk
          simp [step, Pi.single_eq_of_ne hk]
      have hsum : (∑ k, a k) = (∑ k, b k) + 1 := by
        rw [← hab]
        simp only [Pi.add_apply, Finset.sum_add_distrib, hone]
      have hlt : (∑ k, b k) < ∑ k, a k := by omega
      rw [← hab, productExponents_add_step, shapeSum_add, shapeSum_step, ih b hlt,
        cap_add_weak (shapeSum_chamber s hs b) (hs i)]
end K1_13_7_2_3_1_2_2
end
section
set_option autoImplicit false
namespace K1_13_7_2_3_1_2_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_2_3 K1_13_6_2_3_2 K1_13_7_1 MvPolynomial Filter
open K1_13_6_2_3_2_5 (ray ray_eval shapeSum_add)
open scoped BigOperators
variable {ι : Type} [Fintype ι]
theorem affine_eq_rank (J : Ideal GeoJets) (q : Shape) (hq : ChamberBox q) (n : ℕ) :
    affineHilbertFunction (J.comap (monomialMap GeoField (capExponents q)).toRingHom) n =
      supportRank J (capExponents (q.scale n)) := by
  rw [K1_13_6_2_3_2_4.proof, K1_13_6_2_3_2_2.proof (fun _ : Unit => q) (fun _ => hq)]
  simp [shapeSum, Shape.scale]
private theorem shapeSum_scale (shapes : ι → Shape) (n : ℕ) (v : ι → ℕ) :
    shapeSum shapes (fun i => n * v i) = (shapeSum shapes v).scale n := by
  simp [shapeSum, Shape.scale, mul_assoc, Finset.mul_sum]
private theorem cap_surjective (p : Shape) (hp : ChamberBox p) :
    Function.Surjective (monomialMap GeoField (capExponents p)) := by
  apply monomialMap_surjective
  intro i
  have ⟨hb, hj, ht⟩ := hp
  fin_cases i <;>
    norm_num [K1_13_6_2_3_1.cap_coords, Finsupp.single_apply] <;> omega
private theorem supportRank_le (J : Ideal GeoJets) {p q : Shape} (h : InBox p q) :
    supportRank J (capExponents p) ≤ supportRank J (capExponents q) := by
  have hsub : capExponents p ⊆ capExponents q := fun _ he =>
    ⟨he.1.trans (Nat.mul_le_mul_left _ h.1), he.2.1.trans (Nat.mul_le_mul_left _ h.2.1),
      he.2.2.trans (Nat.mul_le_mul_left _ h.2.2)⟩
  have : Module.Finite GeoField (restrictSupport GeoField (capExponents q)) :=
    Module.Finite.of_basis (basisRestrictSupport GeoField _)
  exact Submodule.finrank_mono (Submodule.map_mono (restrictSupport_mono GeoField hsub))
private theorem shape_bounds (p q : Shape) (hq : ChamberBox q) :
    ∃ C : ℕ, ∀ n, InBox (q.scale n) (p.plus (q.scale n)) ∧
      InBox (p.plus (q.scale n)) (q.scale (n + C)) := by
  let C := p.b + p.j + p.t
  have ⟨hb, hj, ht⟩ := hq
  have bound (a b : ℕ) (ha : a ≤ C) (hpos : 0 < b) (n : ℕ) :
      a + n * b ≤ (n + C) * b := by
    rw [Nat.add_mul, add_comm a]
    exact Nat.add_le_add_left (ha.trans (Nat.le_mul_of_pos_right _ hpos)) _
  refine ⟨C, fun n => ⟨⟨Nat.le_add_left _ _, Nat.le_add_left _ _, Nat.le_add_left _ _⟩,
    ⟨bound p.b q.b (by dsimp [C]; omega) (by omega) n,
     bound p.j q.j (by dsimp [C]; omega) (by omega) n,
     bound p.t q.t (by dsimp [C]; omega) ht n⟩⟩⟩
theorem weak_ray_compare (shapes : ι → Shape) (J : Ideal GeoJets) (base : ι)
    (hs : ∀ i, Chamber (shapes i)) (hbase : 0 < (shapes base).t)
    (P : MvPolynomial ι ℚ) (u : ι → ℕ)
    (hu : ∀ a ≥ u, MvPolynomial.eval (fun i => (a i : ℚ)) P =
      (supportRank J (capExponents (shapeSum shapes a)) : ℚ))
    (v : ι → ℕ) (hv : 0 < v base) (d : ℕ) (hd : dimension J ≤ d) :
    (ray P u v).natDegree ≤ dimension J ∧
    (ray P u v).coeff d = capCoeff J d (shapeSum shapes v) := by
  let q := shapeSum shapes v
  have hch : Chamber q := shapeSum_chamber shapes hs v
  have htop : 0 < q.t :=
    (Nat.mul_pos hv hbase).trans_le
      (Finset.single_le_sum (f := fun i => v i * (shapes i).t)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ base))
  have hq : ChamberBox q := ⟨hch.1, hch.2, htop⟩
  let I := J.comap (monomialMap GeoField (capExponents q)).toRingHom
  let Q := affineHilbertPolynomial I
  have hfil (n : ℕ) : affineHilbertFunction I n = supportRank J (capExponents (q.scale n)) :=
    affine_eq_rank J q hq n
  have hQ : Q.natDegree = dimension J :=
    natDegree_affineHilbertPolynomial_comap_of_surjective _ (cap_surjective q hq) J
  obtain ⟨C, hC⟩ := shape_bounds (shapeSum shapes u) q hq
  have hR (n : ℕ) : (ray P u v).eval (n : ℚ) =
      (supportRank J (capExponents ((shapeSum shapes u).plus (q.scale n))) : ℚ) := by
    rw [ray_eval]
    change MvPolynomial.eval (fun i => (((u + fun j => n * v j) i : ℕ) : ℚ)) P = _
    rw [hu (u + fun i => n * v i) (fun i => Nat.le_add_right _ _), shapeSum_add, shapeSum_scale]
  have hshift : Tendsto (fun n : ℕ => n + C) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n C) tendsto_id
  have hlo : ∀ᶠ n : ℕ in atTop, Q.eval (n : ℚ) ≤ (ray P u v).eval (n : ℚ) := by
    filter_upwards [eventually_eval_affineHilbertPolynomial I] with n hn
    rw [show Q.eval (n : ℚ) = (affineHilbertFunction I n : ℚ) from hn, hfil n, hR]
    exact_mod_cast supportRank_le J (hC n).1
  have hhi : ∀ᶠ n : ℕ in atTop,
      (ray P u v).eval (n : ℚ) ≤ (Polynomial.taylor (C : ℚ) Q).eval (n : ℚ) := by
    filter_upwards [hshift.eventually (eventually_eval_affineHilbertPolynomial I)] with n hn
    rw [Polynomial.taylor_eval, ← Nat.cast_add, show Q.eval ((n + C : ℕ) : ℚ) =
      (affineHilbertFunction I (n + C) : ℚ) from hn, hfil (n + C), hR]
    exact_mod_cast supportRank_le J (hC n).2
  have hT : (Polynomial.taylor (C : ℚ) Q).natDegree = dimension J :=
    (Polynomial.natDegree_taylor Q _).trans hQ
  have hdeg : (ray P u v).natDegree ≤ dimension J :=
    (Polynomial.natDegree_le_of_eventually_eval_natCast_le
      (Eventually.of_forall fun n => by rw [hR]; positivity) hhi).1.trans_eq hT
  have hl := Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le
    (hQ.trans_le hd) (hdeg.trans hd) hlo
  have hh := Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le
    (hdeg.trans hd) (hT.trans_le hd) hhi
  rw [Polynomial.coeff_taylor_of_natDegree_le _ (hQ.trans_le hd)] at hh
  exact ⟨hdeg, le_antisymm hh hl⟩
end
end K1_13_7_2_3_1_2_2
end
section
namespace K1_13_4_1
noncomputable section
open Polynomial K1_13 K1_13_4
def overSeed (p : Geom[X]) : Geom[X][X] := p.map C
@[simp] private theorem overSeed_eval (p : Geom[X]) (z : Geom) :
    (overSeed p).map (evalRingHom z) = p := by
  rw [overSeed, Polynomial.map_map]
  have h : (evalRingHom z).comp C = RingHom.id Geom := by
    ext x
    simp
  rw [h, Polynomial.map_id]
@[simp] private theorem overSeed_generic (p : Geom[X]) :
    (overSeed p).map (algebraMap Geom[X] GenericSeed) = liftX p := by
  rw [overSeed, liftX, Polynomial.map_map,
    ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_eq Geom Geom[X] GenericSeed]
theorem regular_resultant {F : Type*} [Field F] {H A : F[X]}
    (hH : H.Monic) {n : ℕ} (hA : A.natDegree ≤ n) (hc : IsCoprime A H) :
    H.resultant A H.natDegree n ≠ 0 := by
  have e := resultant_add_right_deg H A H.natDegree A.natDegree
    (n - A.natDegree) le_rfl
  rw [Nat.add_sub_of_le hA, coeff_natDegree, hH.leadingCoeff, one_pow, one_mul] at e
  rw [e]
  exact ((isUnit_resultant_iff_isCoprime hH).mpr hc.symm).ne_zero
theorem scaled_inverse {F : Type*} [Field F] {H A U V : F[X]} {d : F}
    (hd : d ≠ 0) (h : H * U + A * V = C d) : IsCoprime A H := by
  refine ⟨C d⁻¹ * V, C d⁻¹ * U, ?_⟩
  calc
    _ = C d⁻¹ * (H * U + A * V) := by ring
    _ = 1 := by rw [h, ← C_mul, inv_mul_cancel₀ hd, C_1]
theorem unscale {F : Type*} [Field F] {H A B N : F[X]} {d : F}
    (hd : d ≠ 0) (h : H ∣ A * N + C d * B) :
    H ∣ A * (C d⁻¹ * N) + B := by
  have hunit : C d⁻¹ * C d = (1 : F[X]) := by
    rw [← C_mul, inv_mul_cancel₀ hd, C_1]
  calc
    H ∣ C d⁻¹ * (A * N + C d * B) := h.mul_left _
    _ = A * (C d⁻¹ * N) + B := by
      calc
        _ = A * (C d⁻¹ * N) + (C d⁻¹ * C d) * B := by ring
        _ = _ := by rw [hunit, one_mul]
theorem proof : K1_13_4.c1 := by
  intro Γ s P
  let H := overSeed P.H
  let A := overSeed P.c * (overSeed P.a₀ + C (Polynomial.X : Geom[X]) * overSeed P.a₁)
  let B := C (Polynomial.X : Geom[X]) * overSeed P.q
  let den := H.resultant A H.natDegree A.natDegree
  have hH : H.Monic := P.monic.map C
  have hdeg : H.natDegree = P.H.natDegree := natDegree_map_eq_of_injective C_injective _
  have hpos : 0 < H.natDegree := by rw [hdeg]; exact P.small.1
  have hHne : H ≠ 1 := by
    intro e
    simp [e] at hpos
  have hregular (z : Geom) (hc : IsCoprime (P.a₀ + C z * P.a₁) P.H) : den.eval z ≠ 0 := by
    let e := evalRingHom z
    have heH : H.map e = P.H := overSeed_eval _ _
    have heA : A.map e = P.c * (P.a₀ + C z * P.a₁) := by
      simp [A, e]
    have hedeg : (H.map e).natDegree = H.natDegree := by rw [heH, hdeg]
    change e (H.resultant A H.natDegree A.natDegree) ≠ 0
    rw [← resultant_map_map, ← hedeg]
    exact regular_resultant (hH.map e) natDegree_map_le (by
      rw [heH, heA]
      exact P.c_unit.mul_left hc)
  have hzero : den.eval 0 ≠ 0 := hregular 0 (by simpa using P.a₀_unit)
  have hden : den ≠ 0 := by
    intro hz
    exact hzero (by simp [hz])
  obtain ⟨U, V, _, _, hbezout⟩ := exists_mul_add_mul_eq_C_resultant H A le_rfl le_rfl
    (Or.inl (Nat.ne_of_gt hpos))
  change H * U + A * V = C den at hbezout
  let num := (-B * V) %ₘ H
  have hsmall : num.natDegree < P.H.natDegree := by
    rw [← hdeg]
    exact natDegree_modByMonic_lt _ hH hHne
  have hcleared : H ∣ A * num + C den * B := by
    obtain ⟨W, hW⟩ := dvd_modByMonic_sub (-B * V) H
    refine ⟨A * W + B * U, ?_⟩
    change num - (-B * V) = H * W at hW
    linear_combination A * hW - B * hbezout
  let f := algebraMap Geom[X] GenericSeed
  have hf : f den ≠ 0 :=
    (map_ne_zero_iff f (IsFractionRing.injective Geom[X] GenericSeed)).mpr hden
  refine ⟨{ numerator := num
            denominator := den
            at_zero := hzero
            small := hsmall
            generic_unit := ?_
            generic_congruence := ?_
            regular := fun γ hγ => hregular (P.z γ) (P.regular γ hγ)
            quotient := ?_ }⟩
  · have hm := congrArg (Polynomial.mapRingHom f) hbezout
    simp only [coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at hm
    have hc := scaled_inverse hf hm
    simpa [H, A, f] using hc
  · have hm := Polynomial.map_dvd f hcleared
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at hm
    have hc := unscale hf hm
    simpa [H, A, B, f, genericResidue] using hc
  · intro γ hγ
    let z := P.z γ
    let e := evalRingHom z
    have hz : e den ≠ 0 := hregular z (P.regular γ hγ)
    have hm := Polynomial.map_dvd e hcleared
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at hm
    have hc : P.H ∣ P.c * (P.a₀ + C z * P.a₁) * residueAt num den z + C z * P.q := by
      simpa [H, A, B, e, residueAt] using unscale hz hm
    have hu := (P.c_unit.mul_left (P.regular γ hγ)).symm
    have hd : P.H ∣ extend (s γ) - residueAt num den z := by
      apply hu.dvd_of_dvd_mul_left
      simpa [mul_sub, z] using dvd_sub (P.residue γ hγ) hc
    obtain ⟨T, hT⟩ := hd
    refine ⟨T, ?_, sub_eq_iff_eq_add.mp hT⟩
    by_cases hTzero : T = 0
    · simp [hTzero]
    have hres : (residueAt num den z).natDegree < P.H.natDegree :=
      ((natDegree_C_mul_le _ _).trans natDegree_map_le).trans_lt hsmall
    have hS : (extend (s γ)).natDegree ≤ 131071 + P.H.natDegree := by
      simpa only [extend, natDegree_map] using P.degree γ hγ
    have hb := (natDegree_sub_le (extend (s γ)) (residueAt num den z)).trans
      (max_le hS (by omega))
    rw [hT, P.monic.natDegree_mul' hTzero] at hb
    omega
end
end K1_13_4_1
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_1_1
open K1_13_6_2_4_1 MvPolynomial
open scoped BigOperators
theorem degree_add_eq_max {p q : Form} (hp : TopNonnegative p)
    (hq : TopNonnegative q) : (p + q).totalDegree = max p.totalDegree q.totalDegree := by
  classical
  rcases lt_trichotomy p.totalDegree q.totalDegree with h | h | h
  · rw [totalDegree_add_eq_right_of_totalDegree_lt h, max_eq_right h.le]
  · rw [← h, max_self]
    refine le_antisymm ((totalDegree_add p q).trans_eq (by rw [← h, max_self])) ?_
    by_cases he : p = 0
    · simp [he]
    obtain ⟨a, ha, hd⟩ := p.support.exists_mem_eq_sup (by simpa using he)
      (fun m : Grade => m.degree)
    change p.totalDegree = a.degree at hd
    have hpa : 0 < p.coeff a :=
      lt_of_le_of_ne (hp a hd.le) (Ne.symm (mem_support_iff.mp ha))
    have hqa := hq a (h.symm.trans_le hd.le)
    have hsum : a ∈ (p + q).support := mem_support_iff.mpr (by
      change p.coeff a + q.coeff a ≠ 0
      exact (add_pos_of_pos_of_nonneg hpa hqa).ne')
    exact hd.le.trans (le_totalDegree hsum)
  · rw [totalDegree_add_eq_left_of_totalDegree_lt h, max_eq_left h.le]
private theorem top_add {p q : Form} (hp : TopNonnegative p) (hq : TopNonnegative q) :
    TopNonnegative (p + q) := by
  intro a ha
  rw [degree_add_eq_max hp hq] at ha
  change 0 ≤ p.coeff a + q.coeff a
  exact add_nonneg (hp a ((le_max_left _ _).trans ha)) (hq a ((le_max_right _ _).trans ha))
theorem top_sum {ι : Type} (S : Finset ι) (f : ι → Form)
    (h : ∀ i ∈ S, TopNonnegative (f i)) : TopNonnegative (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [TopNonnegative]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact top_add (h _ (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
private theorem top_mul {p q : Form} (hp : TopNonnegative p) (hq : TopNonnegative q) :
    TopNonnegative (p * q) := by
  classical
  by_cases hpn : p = 0
  · simp [hpn, TopNonnegative]
  by_cases hqn : q = 0
  · simp [hqn, TopNonnegative]
  intro a ha
  rw [totalDegree_mul_of_isDomain hpn hqn] at ha
  rw [coeff_mul]
  apply Finset.sum_nonneg
  intro bc hbc
  have hd := congrArg Finsupp.degree (Finset.HasAntidiagonal.mem_antidiagonal.mp hbc)
  rw [map_add] at hd
  by_cases hb : p.totalDegree < bc.1.degree
  · rw [coeff_eq_zero_of_totalDegree_lt hb, zero_mul]
  by_cases hc : q.totalDegree < bc.2.degree
  · rw [coeff_eq_zero_of_totalDegree_lt hc, mul_zero]
  exact mul_nonneg (hp _ (by omega)) (hq _ (by omega))
private theorem top_C {r : ℚ} (hr : 0 ≤ r) : TopNonnegative (C r : Form) := by
  intro a _
  rw [coeff_C]
  split <;> simp_all
theorem top_prod {ι : Type} (S : Finset ι) (f : ι → Form)
    (h : ∀ i ∈ S, TopNonnegative (f i)) : TopNonnegative (∏ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (top_C (r := 1) zero_le_one)
  | insert a S ha ih =>
    rw [Finset.prod_insert ha]
    exact top_mul (h _ (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
theorem top_linear (j : Fin 5) (r : ℚ) : TopNonnegative (MvPolynomial.X j + C r : Form) := by
  classical
  intro a ha
  rw [totalDegree_add_eq_left_of_totalDegree_lt (by simp), totalDegree_X] at ha
  have hr : (C r : Form).totalDegree < a.degree := by
    simpa only [totalDegree_C] using Nat.lt_of_succ_le ha
  change 0 ≤ (MvPolynomial.X j : Form).coeff a + (C r : Form).coeff a
  rw [coeff_eq_zero_of_totalDegree_lt hr, add_zero, coeff_X]
  split <;> simp
noncomputable def slotForm (j : Fin 5) (d k : ℕ) : Form :=
  C ((d.factorial : ℚ)⁻¹) *
    ∏ r ∈ Finset.range d, (MvPolynomial.X j + C ((r : ℚ) + 1 - (k : ℚ)))
theorem slotForm_top (j : Fin 5) (d k : ℕ) : TopNonnegative (slotForm j d k) := by
  exact top_mul (top_C (by positivity))
    (top_prod _ _ fun r _ => top_linear j _)
theorem asc_eval (d : ℕ) (z : ℚ) :
    (ascPochhammer ℚ d).eval z = ∏ r ∈ Finset.range d, (z + (r : ℚ)) := by
  induction d with
  | zero => simp [ascPochhammer_zero]
  | succ d ih =>
    rw [ascPochhammer_succ_eval, Finset.prod_range_succ, ih]
theorem slotForm_eval (j : Fin 5) (d k : ℕ) (t : Grade) (h : k ≤ t j + d) :
    eval (fun i => (t i : ℚ)) (slotForm j d k) = ((t j + d - k).choose d : ℚ) := by
  rw [← Polynomial.preHilbertPoly_eq_choose_add_sub ℚ d h]
  simp only [slotForm, map_mul, eval_C, map_prod, map_add, eval_X, Polynomial.preHilbertPoly,
    Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, asc_eval]
  congr 1
  exact Finset.prod_congr rfl fun _ _ => by ring
theorem top_product (f : Fin 5 → Form) (h : ∀ i, TopNonnegative (f i)) :
    TopNonnegative (∏ i, f i) :=
  top_prod _ _ fun i _ => h i
end K1_13_6_2_4_1_1
end
section
namespace K1_13_4_6
noncomputable section
open K1_13 K1_13_4 Polynomial
open scoped Polynomial
set_option maxRecDepth 4000
private abbrev Fiber := FractionRing Lower
abbrev toFiber : Lower →+* Fiber := algebraMap _ _
abbrev embedConstant : Geom →+* Lower := MvPolynomial.C.comp inclConst
theorem toFiber_injective : Function.Injective toFiber :=
  IsFractionRing.injective Lower Fiber
theorem asSeedPoly_pad (F : GenericRow) (a : Geom[X]) :
    asSeedPoly (pad F a) = asSeedPoly F * a.map embedConstant := by
  let e := (MvPolynomial.optionEquivLeft GenericX (Fin 3)).toRingHom
  let l := e.comp (eval₂RingHom MvPolynomial.C (MvPolynomial.X none))
  let r := mapRingHom (MvPolynomial.C : GenericX →+* Lower)
  have h : l = r := by
    apply Polynomial.ringHom_ext
    · intro x
      simp [l, r, e, MvPolynomial.optionEquivLeft_C]
    · simp [l, r, e, MvPolynomial.optionEquivLeft_X_none]
  change e (F * (eval₂RingHom MvPolynomial.C (MvPolynomial.X none)) (a.map inclConst)) = _
  rw [map_mul]
  congr 1
  change l (a.map inclConst) = _
  rw [h, coe_mapRingHom, map_map]
theorem coprime_in_fiber {f g : Lower[X]} (hf : f ≠ 0)
    (hfg : IsRelPrime f g) : IsCoprime (f.map toFiber) (g.map toFiber) := by
  classical
  let : NormalizedGCDMonoid Lower := Nonempty.some inferInstance
  apply IsRelPrime.isCoprime
  intro d hdf hdg
  have hd : d ≠ 0 := by
    intro he
    exact (Polynomial.map_ne_zero_iff toFiber_injective).mpr hf (zero_dvd_iff.mp (he ▸ hdf))
  let D := IsLocalization.integerNormalization (nonZeroDivisors Lower) d
  obtain ⟨b, hb, hbD⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors Lower) d
  change D.map toFiber = b • d at hbD
  rw [Algebra.smul_def, Polynomial.algebraMap_apply] at hbD
  have hscale : IsUnit (C (toFiber b)) :=
    isUnit_C.mpr ((map_ne_zero_iff toFiber toFiber_injective).mpr (nonZeroDivisors.ne_zero hb)).isUnit
  have hD : D.primPart.map toFiber ∣ d := by
    apply (IsUnit.dvd_mul_left hscale).mp
    have hfac := congrArg (Polynomial.map toFiber) D.eq_C_content_mul_primPart
    rw [Polynomial.map_mul] at hfac
    rw [← hbD, hfac]
    exact dvd_mul_left _ _
  have hu : IsUnit D.primPart :=
    hfg (D.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map (hD.trans hdf))
      (D.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map (hD.trans hdg))
  have hdeg : d.natDegree = D.natDegree := by
    rw [← natDegree_map_eq_of_injective toFiber_injective, hbD]
    rw [natDegree_C_mul ((map_ne_zero_iff toFiber toFiber_injective).mpr
      (nonZeroDivisors.ne_zero hb))]
  have he : d = C (d.coeff 0) := eq_C_of_natDegree_eq_zero (by
    rw [hdeg, ← D.natDegree_primPart, natDegree_eq_zero_of_isUnit hu])
  have hc : d.coeff 0 ≠ 0 := fun hz => hd (he.trans (by simp [hz]))
  exact he.symm ▸ isUnit_C.mpr hc.isUnit
theorem exists_constant_nonroot (f : Fiber[X]) (hf : f ≠ 0) (avoid : Finset Fiber) :
    ∃ a : Geom, let x := toFiber (embedConstant a); f.eval x ≠ 0 ∧ x ∉ avoid := by
  classical
  let emb : Geom → Fiber := fun a => toFiber (embedConstant a)
  have he : Function.Injective emb := by
    intro a b h
    exact inclConst.injective ((MvPolynomial.C_injective (Fin 3) GenericX) (toFiber_injective h))
  obtain ⟨_, ⟨a, rfl⟩, ha⟩ :=
    (Set.infinite_range_of_injective he).exists_notMem_finset (f.roots.toFinset ∪ avoid)
  refine ⟨a, ?_⟩
  change f.eval (emb a) ≠ 0 ∧ emb a ∉ avoid
  simp only [Finset.mem_union, Multiset.mem_toFinset, mem_roots hf, not_or] at ha
  exact ⟨ha.1, ha.2⟩
theorem coprime_linear (f : Fiber[X]) {a : Fiber} (h : f.eval a ≠ 0) :
    IsCoprime ((Polynomial.X : Fiber[X]) - C a) f :=
  ((monic_X_sub_C a).irreducible_of_degree_eq_one (degree_X_sub_C a)).coprime_iff_not_dvd.mpr
    (fun hd => h (dvd_iff_isRoot.mp hd))
theorem asSeedPoly_ne_zero {F : GenericRow} (hF : F ≠ 0) : asSeedPoly F ≠ 0 :=
  (map_ne_zero_iff (MvPolynomial.optionEquivLeft GenericX (Fin 3))
    (MvPolynomial.optionEquivLeft GenericX (Fin 3)).injective).mpr hF
private theorem pad_degree (F : GenericRow) (hF : F ≠ 0)
    (hcap : seedDegree F ≤ 70000) (a : Geom) :
    (asSeedPoly (pad F (((Polynomial.X : Geom[X]) - C a) ^
      (70000 - (asSeedPoly F).natDegree)))).natDegree = 70000 := by
  have hcap' : (asSeedPoly F).natDegree ≤ 70000 := by
    simpa only [asSeedPoly, MvPolynomial.natDegree_optionEquivLeft, seedDegree] using hcap
  rw [asSeedPoly_pad, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    natDegree_mul (asSeedPoly_ne_zero hF) (pow_ne_zero _ (X_sub_C_ne_zero _)),
    natDegree_pow, natDegree_X_sub_C, mul_one, Nat.add_sub_of_le hcap']
theorem padding_exists {F G : GenericRow} (hF : F ≠ 0) (hG : G ≠ 0)
    (hfg : IsRelPrime F G) (hf : seedDegree F ≤ 70000) (hg : seedDegree G ≤ 70000) :
    ∃ a b : Geom[X], (asSeedPoly (pad F a)).natDegree = 70000 ∧
      (asSeedPoly (pad G b)).natDegree = 70000 ∧ seedResultant (pad F a) (pad G b) ≠ 0 := by
  classical
  let f := (asSeedPoly F).map toFiber
  let g := (asSeedPoly G).map toFiber
  have hf0 : f ≠ 0 := (Polynomial.map_ne_zero_iff toFiber_injective).mpr (asSeedPoly_ne_zero hF)
  have hg0 : g ≠ 0 := (Polynomial.map_ne_zero_iff toFiber_injective).mpr (asSeedPoly_ne_zero hG)
  have hcop : IsCoprime f g := by
    apply coprime_in_fiber (asSeedPoly_ne_zero hF)
    intro d hdf hdg
    let e := MvPolynomial.optionEquivLeft GenericX (Fin 3)
    have hu : IsUnit (e.symm d) :=
      hfg (by simpa [e, asSeedPoly] using map_dvd e.symm.toRingHom hdf)
        (by simpa [e, asSeedPoly] using map_dvd e.symm.toRingHom hdg)
    have he := hu.map e.toRingHom
    change IsUnit (e (e.symm d)) at he
    rwa [e.apply_symm_apply] at he
  obtain ⟨a, ha, _⟩ := exists_constant_nonroot g hg0 ∅
  obtain ⟨b, hb, hba⟩ := exists_constant_nonroot f hf0 {toFiber (embedConstant a)}
  let p := ((Polynomial.X : Geom[X]) - C a) ^ (70000 - (asSeedPoly F).natDegree)
  let q := ((Polynomial.X : Geom[X]) - C b) ^ (70000 - (asSeedPoly G).natDegree)
  have hp : (asSeedPoly (pad F p)).natDegree = 70000 := pad_degree F hF hf a
  have hq : (asSeedPoly (pad G q)).natDegree = 70000 := pad_degree G hG hg b
  refine ⟨p, q, hp, hq, ?_⟩
  have hab : toFiber (embedConstant a) ≠ toFiber (embedConstant b) := by
    simpa using (Finset.notMem_singleton.mp hba).symm
  have hpad : IsCoprime ((asSeedPoly (pad F p)).map toFiber)
      ((asSeedPoly (pad G q)).map toFiber) := by
    simp only [asSeedPoly_pad, Polynomial.map_mul, p, q, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C]
    exact (hcop.mul_right (coprime_linear f hb).symm.pow_right).mul_left
      ((coprime_linear g ha).pow_left.mul_right
        (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit).pow)
  have hn := resultant_ne_zero _ _ hpad
  rw [natDegree_map_eq_of_injective toFiber_injective,
    natDegree_map_eq_of_injective toFiber_injective, hp, hq, resultant_map_map] at hn
  intro hz
  exact hn ((congrArg toFiber hz).trans (map_zero _))
end
end K1_13_4_6
end
section
namespace K1_13_4_6
noncomputable section
open K1_13 K1_13_4 Polynomial
open scoped Polynomial BigOperators Pointwise
set_option maxRecDepth 4000
private abbrev deg {σ : Type*} (w : σ → ℕ) (P : MvPolynomial σ GenericX) : ℕ :=
  P.weightedTotalDegree w
theorem deg_sum_le {σ ι : Type*} (w : σ → ℕ) {s : Finset ι}
    {p : ι → MvPolynomial σ GenericX} {B : ℕ} (h : ∀ i ∈ s, deg w (p i) ≤ B) :
    deg w (∑ i ∈ s, p i) ≤ B := by
  classical
  apply (AddMonoidAlgebra.supDegree_sum_le (D := Finsupp.weight w)).trans
  exact Finset.sup_le h
theorem deg_prod_le {σ ι : Type*} (w : σ → ℕ) (s : Finset ι)
    (p : ι → MvPolynomial σ GenericX) :
    deg w (∏ i ∈ s, p i) ≤ ∑ i ∈ s, deg w (p i) :=
  AddMonoidAlgebra.supDegree_prod_le (D := Finsupp.weight w) (map_zero _) (map_add _)
theorem deg_mul_le {σ : Type*} (w : σ → ℕ) (p q : MvPolynomial σ GenericX) :
    deg w (p * q) ≤ deg w p + deg w q :=
  AddMonoidAlgebra.supDegree_mul_le (D := Finsupp.weight w) (map_add _)
theorem deg_neg {σ : Type*} (w : σ → ℕ) (p : MvPolynomial σ GenericX) :
    deg w (-p) = deg w p :=
  AddMonoidAlgebra.supDegree_neg (D := Finsupp.weight w)
theorem deg_C {σ : Type*} (w : σ → ℕ) (a : GenericX) :
    deg w (MvPolynomial.C a) = 0 := by
  classical
  change (MvPolynomial.C a : MvPolynomial σ GenericX).support.sup (Finsupp.weight w) = 0
  rw [MvPolynomial.support_C]
  split <;> simp
theorem deg_coeff (w : Fin 3 → ℕ) (F : GenericRow) (i : ℕ) :
    deg w ((asSeedPoly F).coeff i) ≤ deg (fun o => o.elim 0 w) F := by
  apply Finset.sup_le
  intro m hm
  have hs : m.optionElim i ∈ F.support := by
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    simpa only [asSeedPoly, MvPolynomial.optionEquivLeft_coeff_coeff] using hm
  have h := MvPolynomial.le_weightedTotalDegree (fun o => o.elim 0 w) hs
  rw [Finsupp.weight_apply, Finsupp.sum_option_index_smul] at h
  simpa only [Option.elim_none, Option.elim_some, smul_zero, zero_add, Finsupp.some_optionElim,
    Finsupp.weight_apply] using h
theorem deg_pad_coeff (w : Fin 3 → ℕ) (F : GenericRow) (a : Geom[X]) (i : ℕ) :
    deg w ((asSeedPoly (pad F a)).coeff i) ≤ deg (fun o => o.elim 0 w) F := by
  rw [asSeedPoly_pad, Polynomial.coeff_mul]
  apply deg_sum_le
  intro j _
  rw [coeff_map]
  refine (deg_mul_le _ _ _).trans ?_
  change deg w ((asSeedPoly F).coeff j.1) +
    deg w (MvPolynomial.C (inclConst (a.coeff j.2))) ≤ _
  rw [deg_C, add_zero]
  exact deg_coeff w F j.1
theorem deg_resultant (w : Fin 3 → ℕ) (f g : Lower[X]) (m n B D : ℕ)
    (hf : ∀ i, deg w (f.coeff i) ≤ B) (hg : ∀ i, deg w (g.coeff i) ≤ D) :
    deg w (f.resultant g m n) ≤ m * D + n * B := by
  classical
  let A := f.sylvester g m n
  have hl (i : Fin (m + n)) (j : Fin m) : deg w (A i (j.castAdd n)) ≤ D := by
    simp only [A, sylvester, Matrix.of_apply, Fin.addCases_left]
    split
    · apply hg
    · simp [MvPolynomial.weightedTotalDegree_zero]
  have hr (i : Fin (m + n)) (j : Fin n) : deg w (A i (j.natAdd m)) ≤ B := by
    simp only [A, sylvester, Matrix.of_apply, Fin.addCases_right]
    split
    · apply hf
    · simp [MvPolynomial.weightedTotalDegree_zero]
  change deg w A.det ≤ _
  rw [Matrix.det_apply]
  apply deg_sum_le
  intro π _
  have hp : deg w (∏ i, A (π i) i) ≤ m * D + n * B := by
    apply (deg_prod_le w Finset.univ _).trans
    rw [Fin.sum_univ_add]
    have h₁ : ∑ j : Fin m, deg w (A (π (j.castAdd n)) (j.castAdd n)) ≤ ∑ _j : Fin m, D :=
      Finset.sum_le_sum fun j _ => hl _ j
    have h₂ : ∑ j : Fin n, deg w (A (π (j.natAdd m)) (j.natAdd m)) ≤ ∑ _j : Fin n, B :=
      Finset.sum_le_sum fun j _ => hr _ j
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
      using Nat.add_le_add h₁ h₂
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hh | hh <;>
    simpa [hh, deg_neg] using hp
private theorem mixedWeight_add (a b : SeedVar →₀ ℕ) :
    mixedWeight (a + b) = mixedWeight a + mixedWeight b := by
  have hsum (m : Fin 3 →₀ ℕ) :
      m.sum (fun _ e => e) = Finsupp.weight (fun _ : Fin 3 => (1 : ℕ)) m := by
    simp [Finsupp.weight_apply]
  simp only [mixedWeight, hsum, Finsupp.add_apply, Finsupp.some_add, map_add, Nat.mul_add]
  ac_rfl
private theorem mixedOrder_pad {F : GenericRow} {z : GenericX} {y : Fin 3 → GenericX}
    {d : ℕ} (a : Geom[X]) (h : MixedOrder F z y d) :
    MixedOrder (pad F a) z y d := by
  classical
  intro m hm
  rw [pad, map_mul] at hm
  obtain ⟨u, hu, v, _, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
  exact (h u hu).trans (by rw [mixedWeight_add]; exact Nat.le_add_right _ _)
theorem proof : K1_13_4.c6 := by
  intro F G hF hG hp hf hg
  obtain ⟨a, b, ha, hb, hn⟩ := padding_exists hF hG hp hf.2.2.2 hg.2.2.2
  refine ⟨⟨a, b, ha, hb, hn, ?_, ?_, ?_⟩⟩
  · have h := deg_resultant (1 : Fin 3 → ℕ) (asSeedPoly (pad F a)) (asSeedPoly (pad G b))
      70000 70000 6789 6820 (fun i => (deg_pad_coeff _ F a i).trans hf.1)
      (fun i => (deg_pad_coeff _ G b i).trans hg.1)
    simpa only [MvPolynomial.weightedTotalDegree_one, seedResultant,
      ← Nat.mul_add, Nat.add_comm 6820 6789, native_degree_arithmetic.1] using h
  · have h := deg_resultant Fin.val (asSeedPoly (pad F a)) (asSeedPoly (pad G b))
      70000 70000 2300 2300 (fun i => (deg_pad_coeff _ F a i).trans hf.2.1)
      (fun i => (deg_pad_coeff _ G b i).trans hg.2.1)
    simpa only [MvPolynomial.weightedTotalDegree, Finsupp.weight_apply, Nat.nsmul_eq_mul,
      Nat.mul_comm, lowerIndex, seedResultant, ← Nat.mul_add, native_degree_arithmetic.2.1]
      using h
  · intro z y h
    exact ⟨mixedOrder_pad a h.1, mixedOrder_pad b h.2⟩
end
end K1_13_4_6
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_1_1
open K1_13_6_2_4_1
open scoped BigOperators
abbrev Cell {σ : Type} (b : σ →₀ ℕ) := (x : σ) → Fin (b x + 1)
def clip {σ : Type} (b a : σ →₀ ℕ) : Cell b :=
  fun x => ⟨min (a x) (b x), Nat.lt_succ_of_le (min_le_right _ _)⟩
noncomputable def base {σ : Type} [Finite σ] {b : σ →₀ ℕ} (u : Cell b) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun x => (u x).val
@[simp] theorem base_apply {σ : Type} [Finite σ] {b : σ →₀ ℕ} (u : Cell b) (x : σ) :
    base u x = (u x).val := rfl
theorem outside_clip {σ : Type} [Finite σ] {b : σ →₀ ℕ}
    {A : Finset (σ →₀ ℕ)} (hA : ∀ d ∈ A, d ≤ b) (a : σ →₀ ℕ) :
    base (clip b a) ∈ outside A ↔ a ∈ outside A := by
  change (∀ d ∈ A, ¬ d ≤ base (clip b a)) ↔ (∀ d ∈ A, ¬ d ≤ a)
  have hd (d : σ →₀ ℕ) (hm : d ∈ A) : d ≤ base (clip b a) ↔ d ≤ a := by
    constructor
    · intro h x
      exact (h x).trans (min_le_left _ _)
    · intro h x
      exact le_min (h x) (hA d hm x)
  exact ⟨fun h d hm hle => h d hm ((hd d hm).mpr hle),
    fun h d hm hle => h d hm ((hd d hm).mp hle)⟩
theorem weight_apply_slot {σ : Type} [Fintype σ] (s : σ → Fin 5) (a : σ →₀ ℕ)
    (j : Fin 5) : Finsupp.weight (slotWeight s) a j =
      ∑ x ∈ Finset.univ.filter (fun x => s x = j), a x := by
  rw [Finsupp.weight_eq_sum, Finsupp.finsetSum_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : s x = j
  · simp [slotWeight, unitGrade, h]
  · simp [slotWeight, unitGrade, h, Ne.symm h]
theorem finite_weight_fiber {σ : Type} [Fintype σ] (s : σ → Fin 5) (t : Grade) :
    {a : σ →₀ ℕ | Finsupp.weight (slotWeight s) a = t}.Finite := by
  classical
  apply (Finsupp.finite_of_degree_le (σ := σ) (∑ x : σ, t (s x))).subset
  intro a ha
  change Finsupp.weight (slotWeight s) a = t at ha
  rw [Set.mem_ofPred_eq, Finsupp.degree_eq_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← ha, weight_apply_slot]
  exact Finset.single_le_sum (f := fun v => a v) (fun _ _ => Nat.zero_le _)
    (by simp)
def cellSlice {σ : Type} (s : σ → Fin 5) {b : σ →₀ ℕ} (u : Cell b)
    (t : Grade) : Set (σ →₀ ℕ) :=
  {a | clip b a = u ∧ Finsupp.weight (slotWeight s) a = t}
noncomputable def cells {σ : Type} [Fintype σ] {b : σ →₀ ℕ}
    (A : Finset (σ →₀ ℕ)) : Finset (Cell b) := by
  classical
  exact Finset.univ.filter fun u => base u ∈ outside A
theorem cells_mono {σ : Type} [Fintype σ] {b : σ →₀ ℕ} {A C : Finset (σ →₀ ℕ)}
    (h : outside C ⊆ outside A) : cells (b := b) C ⊆ cells A := by
  classical
  intro u hu
  simp only [cells, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  exact h hu
theorem sliceCount_eq_sum {σ : Type} [Fintype σ] (s : σ → Fin 5)
    (b : σ →₀ ℕ) (A : Finset (σ →₀ ℕ)) (hA : ∀ d ∈ A, d ≤ b) (t : Grade) :
    sliceCount s A t = ∑ u ∈ cells (b := b) A, (cellSlice s u t).ncard := by
  classical
  let S := cells (b := b) A
  have heq : {a ∈ outside A | Finsupp.weight (slotWeight s) a = t} =
      ⋃ u ∈ (S : Set (Cell b)), cellSlice s u t := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_coe, cellSlice]
    constructor
    · rintro ⟨ha, ht⟩
      exact ⟨clip b a, by simpa [S, cells] using (outside_clip hA a).mpr ha, rfl, ht⟩
    · rintro ⟨u, hu, rfl, ht⟩
      exact ⟨(outside_clip hA a).mp (by simpa [S, cells] using hu), ht⟩
  have hf (u : Cell b) : (cellSlice s u t).Finite :=
    (finite_weight_fiber s t).subset fun _ ha => ha.2
  have hd : (S : Set (Cell b)).PairwiseDisjoint (fun u => cellSlice s u t) := by
    intro u _ v _ huv
    exact Set.disjoint_left.mpr fun _ ha hb => huv (ha.1.symm.trans hb.1)
  rw [sliceCount, heq,
    (Finset.finite_toSet S).ncard_biUnion (fun u _ => hf u) hd,
    finsum_mem_eq_finite_toFinset_sum _ (Finset.finite_toSet S)]
  have hS : (Finset.finite_toSet S).toFinset = S := by
    ext u
    rw [Set.Finite.mem_toFinset, Finset.mem_coe]
  rw [hS]
end K1_13_6_2_4_1_1
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_1_1
open K1_13_6_2_4_1 MvPolynomial
open scoped BigOperators
section
variable {σ : Type} [Fintype σ] {b : σ →₀ ℕ}
theorem clip_eq_iff (u : Cell b) (a : σ →₀ ℕ) :
    clip b a = u ↔ base u ≤ a ∧ ∀ x, (u x).val < b x → a x = base u x := by
  constructor
  · intro h
    have hx (x : σ) : min (a x) (b x) = (u x).val :=
      congrArg (fun v : Cell b => (v x).val) h
    refine ⟨fun x => (hx x).symm.le.trans (min_le_left _ _), fun x hlt => ?_⟩
    have hm := hx x
    change a x = (u x).val
    rw [min_def] at hm
    split at hm <;> omega
  · rintro ⟨hle, hfix⟩
    funext x
    apply Fin.ext
    change min (a x) (b x) = (u x).val
    have hcap := Nat.le_of_lt_succ (u x).isLt
    by_cases hlt : (u x).val < b x
    · have hfixx : a x = (u x).val := hfix x hlt
      rw [hfixx, min_eq_left hcap]
    · have he : (u x).val = b x := by omega
      have hlex : (u x).val ≤ a x := hle x
      rw [he, min_eq_right (he ▸ hlex)]
private def free (s : σ → Fin 5) (u : Cell b) (j : Fin 5) : Finset σ :=
  Finset.univ.filter fun x => s x = j ∧ (u x).val = b x
private theorem mem_free {s : σ → Fin 5} {u : Cell b} {j : Fin 5} {x : σ} :
    x ∈ free s u j ↔ s x = j ∧ (u x).val = b x := by
  simp [free]
private noncomputable def offset (s : σ → Fin 5) (u : Cell b) : Grade :=
  Finsupp.weight (slotWeight s) (base u)
omit [Fintype σ] in
theorem zero_off {S : Finset σ} {r : σ →₀ ℕ} (hs : r.support ⊆ S)
    {x : σ} (hx : x ∉ S) : r x = 0 :=
  Finsupp.notMem_support_iff.mp (fun hm => hx (hs hm))
abbrev Choices [DecidableEq σ] (s : σ → Fin 5) (u : Cell b) (t : Grade) :=
  ∀ j : Fin 5, (free s u j).finsuppAntidiag (t j - offset s u j)
private noncomputable def toChoices [DecidableEq σ] (s : σ → Fin 5) (u : Cell b)
    (t : Grade) (a : cellSlice s u t) : Choices s u t := by
  let r := a.val - base u
  have hc := (clip_eq_iff u a.val).mp a.prop.1
  have hrt : r + base u = a.val := tsub_add_cancel_of_le hc.1
  have hw := congrArg (fun e : σ →₀ ℕ => Finsupp.weight (slotWeight s) e) hrt
  rw [map_add, a.prop.2] at hw
  intro j
  refine ⟨r.filter (fun x => s x = j), Finset.mem_finsuppAntidiag.mpr ⟨?_, ?_⟩⟩
  · have h := congrArg (fun g : Grade => g j) hw
    change Finsupp.weight (slotWeight s) r j + offset s u j = t j at h
    have hrj : Finsupp.weight (slotWeight s) r j = t j - offset s u j := by omega
    rw [← hrj, weight_apply_slot]
    calc
      _ = ∑ x ∈ free s u j, r x := by
        exact Finset.sum_congr rfl fun x hx =>
          Finsupp.filter_apply_pos _ _ (mem_free.mp hx).1
      _ = _ := Finset.sum_subset
        (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_free.mp hx).1⟩)
        (fun x hx hn => by
          have he : (u x).val ≠ b x := fun he =>
            hn (mem_free.mpr ⟨(Finset.mem_filter.mp hx).2, he⟩)
          have hlt : (u x).val < b x :=
            lt_of_le_of_ne (Nat.le_of_lt_succ (u x).isLt) he
          change (a.val - base u) x = 0
          rw [Finsupp.tsub_apply, hc.2 x hlt, tsub_self])
  · intro x hx
    rw [Finsupp.support_filter, Finset.mem_filter] at hx
    refine mem_free.mpr ⟨hx.2, ?_⟩
    by_contra he
    have hlt : (u x).val < b x := lt_of_le_of_ne (Nat.le_of_lt_succ (u x).isLt) he
    exact (Finsupp.mem_support_iff.mp hx.1) (by
      change (a.val - base u) x = 0
      rw [Finsupp.tsub_apply, hc.2 x hlt, tsub_self])
private noncomputable def fromChoices [DecidableEq σ] (s : σ → Fin 5) (u : Cell b)
    (t : Grade) (ht : ∀ j, offset s u j ≤ t j) (v : Choices s u t) : cellSlice s u t := by
  let r : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun x => (v (s x)).val x)
  have hv (j : Fin 5) := Finset.mem_finsuppAntidiag.mp (v j).prop
  refine ⟨base u + r, (clip_eq_iff u _).mpr ⟨le_add_right le_rfl, ?_⟩, ?_⟩
  · intro x hx
    have hr : r x = 0 := zero_off (hv (s x)).2 (fun h => hx.ne (mem_free.mp h).2)
    simp [hr]
  · rw [map_add]
    ext j
    change offset s u j + Finsupp.weight (slotWeight s) r j = t j
    rw [weight_apply_slot]
    have hs : (∑ x ∈ Finset.univ.filter (fun x => s x = j), r x) =
        ∑ x ∈ free s u j, (v j).val x := by
      calc
        _ = ∑ x ∈ Finset.univ.filter (fun x => s x = j), (v j).val x := by
          apply Finset.sum_congr rfl
          intro x hx
          change (v (s x)).val x = (v j).val x
          rw [(Finset.mem_filter.mp hx).2]
        _ = _ := (Finset.sum_subset
          (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_free.mp hx).1⟩)
          (fun _ _ h => zero_off (hv j).2 h)).symm
    rw [hs, (hv j).1]
    exact Nat.add_sub_of_le (ht j)
private noncomputable def cellEquiv [DecidableEq σ] (s : σ → Fin 5) (u : Cell b)
    (t : Grade) (ht : ∀ j, offset s u j ≤ t j) : cellSlice s u t ≃ Choices s u t where
  toFun := toChoices s u t
  invFun := fromChoices s u t ht
  left_inv a := by
    apply Subtype.ext
    ext x
    change base u x + (toChoices s u t a (s x)).val x = a.val x
    change base u x + ((a.val - base u).filter fun y => s y = s x) x = a.val x
    rw [Finsupp.filter_apply, ite_eq_left (rfl : s x = s x), Finsupp.tsub_apply]
    exact Nat.add_sub_of_le ((clip_eq_iff u a.val).mp a.prop.1 |>.1 x)
  right_inv v := by
    funext j
    apply Subtype.ext
    ext x
    let r : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun y => (v (s y)).val y)
    change ((base u + r - base u).filter fun y => s y = j) x = (v j).val x
    rw [add_comm (base u) r, add_tsub_cancel_right, Finsupp.filter_apply]
    split
    · rename_i hx
      change (v (s x)).val x = (v j).val x
      rw [hx]
    · rename_i hx
      exact (zero_off (Finset.mem_finsuppAntidiag.mp (v j).prop).2
        (fun h => hx (mem_free.mp h).1)).symm
theorem cellSlice_ncard (s : σ → Fin 5) (u : Cell b) (t : Grade)
    (ht : ∀ j, offset s u j ≤ t j) :
    (cellSlice s u t).ncard = ∏ j, (free s u j).card.multichoose (t j - offset s u j) := by
  classical
  rw [← Nat.card_coe_set_eq, Nat.card_congr (cellEquiv s u t ht),
    Nat.card_eq_fintype_card, Fintype.card_pi]
  simp only [Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_multichoose]
noncomputable def cellForm (s : σ → Fin 5) (u : Cell b) : Form :=
  ∏ j : Fin 5, if (free s u j).card = 0 then 0
    else slotForm j ((free s u j).card - 1) (offset s u j)
theorem cellForm_top (s : σ → Fin 5) (u : Cell b) : TopNonnegative (cellForm s u) := by
  apply top_product
  intro j
  split
  · simp [TopNonnegative]
  · exact slotForm_top _ _ _
theorem offset_le (s : σ → Fin 5) (u : Cell b) (j : Fin 5) :
    offset s u j ≤ b.degree := by
  rw [offset, weight_apply_slot, Finsupp.degree_eq_sum]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_ |>.trans ?_
  · exact fun _ _ _ => Nat.zero_le _
  · exact Finset.sum_le_sum fun x _ => Nat.le_of_lt_succ (u x).isLt
theorem cellForm_eval (s : σ → Fin 5) (u : Cell b) (t : Grade)
    (ht : ∀ j, b.degree < t j) :
    eval (fun j => (t j : ℚ)) (cellForm s u) = ((cellSlice s u t).ncard : ℚ) := by
  have ho (j : Fin 5) : offset s u j < t j := (offset_le s u j).trans_lt (ht j)
  rw [cellSlice_ncard s u t (fun j => (ho j).le), Nat.cast_prod, cellForm, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  cases hk : (free s u j).card with
  | zero =>
    have hh : t j - offset s u j = (t j - offset s u j - 1) + 1 := by
      have := ho j
      omega
    rw [ite_eq_left rfl, map_zero, hh, Nat.multichoose_zero_succ, Nat.cast_zero]
  | succ d =>
    have hh := ho j
    rw [ite_eq_right (Nat.succ_ne_zero _), Nat.succ_sub_one, slotForm_eval _ _ _ _ (by omega),
      Nat.multichoose_eq]
    congr 1
    rw [show d.succ + (t j - offset s u j) - 1 = t j + d - offset s u j by omega]
    exact Nat.choose_symm_of_eq_add (by omega : t j + d - offset s u j =
      d + (t j - offset s u j))
end
end K1_13_6_2_4_1_1
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_5_3
noncomputable section
open K1_13_6_3_5_5
open scoped Pointwise
theorem length_range_le_ord {L M : Type} [CommRing L] [IsDomain L]
    [IsNoetherianRing L] [Ring.KrullDimLE 1 L] [AddCommGroup M] [Module L M]
    {x d : L} (hx : x ≠ 0) (hd : d ≠ 0) (I : Ideal L) (hdI : d ∈ I)
    (f : I →ₗ[L] M) (hf : ∀ a : I, f (x • a) = 0) :
    Module.length L (LinearMap.range f) ≤ Ring.ord L x := by
  let J : Ideal L := x • I
  have hJI : J ≤ I := Submodule.smul_le_self_of_tower x I
  let g : (L ⧸ J) →ₗ[L] (L ⧸ I) := Submodule.factor hJI
  have hmul : Module.length L (L ⧸ J) = Module.length L (L ⧸ I) + Ring.ord L x :=
    Module.length_eq_add_of_exact (Ideal.mulQuot x I) (Ideal.quotOfMul x I)
      (Ideal.mulQuot_injective I (mem_nonZeroDivisors_iff_ne_zero.mpr hx))
      (Ideal.quotOfMul_surjective I) (Ideal.exact_mulQuot_quotOfMul I)
  have hfactor : Module.length L (L ⧸ J) =
      Module.length L (LinearMap.ker g) + Module.length L (L ⧸ I) :=
    Module.length_eq_add_of_exact (LinearMap.ker g).subtype g
      (Submodule.subtype_injective _) (Submodule.factor_surjective hJI)
      (LinearMap.exact_subtype_ker_map g)
  have hfinite : Module.length L (L ⧸ I) ≠ ⊤ := by
    have hle : Ideal.span {d} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hdI
    have hlen : Module.length L (L ⧸ I) ≤ Ring.ord L d :=
      Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
    exact (hlen.trans_lt (Ring.ord_lt_top (mem_nonZeroDivisors_iff_ne_zero.mpr hd))).ne
  have hkernel : Module.length L (LinearMap.ker g) = Ring.ord L x := by
    apply ENat.add_left_injective_of_ne_top hfinite
    exact hfactor.symm.trans (hmul.trans (add_comm _ _))
  let p : I →ₗ[L] (L ⧸ J) := J.mkQ.comp I.subtype
  have hp : LinearMap.range p ≤ LinearMap.ker g := by
    rintro _ ⟨a, rfl⟩
    rw [LinearMap.mem_ker]
    change I.mkQ (a : L) = 0
    exact (Submodule.Quotient.mk_eq_zero I).mpr a.property
  have hker : LinearMap.ker p ≤ LinearMap.ker f := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    have haJ : (a : L) ∈ J := (Submodule.Quotient.mk_eq_zero J).mp ha
    obtain ⟨b, hb, hba⟩ := (Submodule.mem_smul_pointwise_iff_exists (a : L) x I).mp haJ
    have hab : a = x • (⟨b, hb⟩ : I) := Subtype.ext hba.symm
    rw [hab, hf]
  let q := (LinearMap.ker p).liftQ f hker
  calc
    Module.length L (LinearMap.range f) = Module.length L (LinearMap.range q) :=
      congrArg (fun N : Submodule L M => Module.length L N)
        (Submodule.range_liftQ _ f hker).symm
    _ ≤ Module.length L (I ⧸ LinearMap.ker p) :=
      Module.length_le_of_surjective q.rangeRestrict q.surjective_rangeRestrict
    _ = Module.length L (LinearMap.range p) := p.quotKerEquivRange.length_eq
    _ ≤ Module.length L (LinearMap.ker g) :=
      Module.length_le_of_injective (Submodule.inclusion hp) (Submodule.inclusion_injective hp)
    _ = Ring.ord L x := hkernel
theorem proof : K1_13_6_3_5_5.c3 := by
  classical
  intro L _ _ _ _ _ x hx B s
  let Q : Ideal B := Ideal.span {algebraMap L B x}
  have hlift (i : s) : ∃ b : B, Ideal.Quotient.mk Q b = (i : SectionQuotient x B) :=
    Ideal.Quotient.mk_surjective (I := Q) (i : SectionQuotient x B)
  choose lift hlift using hlift
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors L) (fun i : s => (lift i : FractionRing L))
  let a := algebraMap L (FractionRing L) (d : L)
  have hd0 : (d : L) ≠ 0 := nonZeroDivisors.ne_zero d.property
  have ha0 : a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective L (FractionRing L))).mpr hd0
  let t : L →ₗ[L] FractionRing L :=
    (LinearMap.mul L (FractionRing L) a⁻¹).comp (Algebra.ofId L (FractionRing L)).toLinearMap
  have ht (r : L) : t r = a⁻¹ * algebraMap L (FractionRing L) r := rfl
  let I : Ideal L := B.toSubmodule.comap t
  have hdI : (d : L) ∈ I := by
    change t (d : L) ∈ B
    rw [ht, show algebraMap L (FractionRing L) (d : L) = a from rfl, inv_mul_cancel₀ ha0]
    exact B.one_mem
  let j : I →ₗ[L] B := B.toSubmoduleEquiv.toLinearMap.comp
    (t.restrict (p := I) (q := B.toSubmodule) (fun _ hr => hr))
  let f : I →ₗ[L] SectionQuotient x B := (Ideal.Quotient.mkₐ L Q).toLinearMap.comp j
  have hzero (r : I) : f (x • r) = 0 := by
    change Ideal.Quotient.mk Q (j (x • r)) = 0
    rw [j.map_smul, Ideal.Quotient.eq_zero_iff_mem, Algebra.smul_def]
    exact Ideal.mem_span_singleton.mpr ⟨j r, rfl⟩
  have hspan : Submodule.span L (s : Set (SectionQuotient x B)) ≤ LinearMap.range f := by
    apply Submodule.span_le.mpr
    intro y hy
    let i : s := ⟨y, hy⟩
    obtain ⟨r, hr⟩ := hd i
    have hr' : t r = (lift i : FractionRing L) := by
      rw [ht, hr, Algebra.smul_def]
      change a⁻¹ * (a * (lift i : FractionRing L)) = _
      rw [← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
    have hrI : r ∈ I := by
      change t r ∈ B
      rw [hr']
      exact (lift i).property
    have hj : j ⟨r, hrI⟩ = lift i := Subtype.ext hr'
    refine ⟨⟨r, hrI⟩, ?_⟩
    change Ideal.Quotient.mk Q (j ⟨r, hrI⟩) = y
    rw [hj]
    exact hlift i
  exact (Module.length_le_of_injective (Submodule.inclusion hspan)
    (Submodule.inclusion_injective hspan)).trans (length_range_le_ord hx hd0 I hdI f hzero)
end
end K1_13_6_3_5_5_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_4_5_1
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_4 K1_14_2_2_4_5
open scoped BigOperators
theorem minimal_of_section {F : Type} [Field F] {φ : Ambient →+* Plane F}
    {k : Fin 4} (chart : SectionChart F φ k) {J I : Ideal Ambient}
    [Module.Finite F (PlaneSection φ J)] (hI : I.IsPrime) (hIJ : J ≤ I)
    (hsurv : I.map φ ≠ ⊤) : I ∈ J.minimalPrimes := by
  refine ⟨⟨hI, hIJ⟩, ?_⟩
  intro H hH hHI
  have hmap : H.map φ ≤ I.map φ := Ideal.map_mono hHI
  have hHsurv : H.map φ ≠ ⊤ := ne_top_of_le_ne_top hsurv hmap
  obtain ⟨hHprime, hHcomap⟩ := chart.prime_over H hH.1 hHsurv
  have hIcomap := (chart.prime_over I hI hsurv).2
  have hle : J.map φ ≤ H.map φ := Ideal.map_mono hH.2
  let : Module.Finite F (PlaneSection φ H) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ F hle).toLinearMap
      (Ideal.Quotient.factor_surjective hle)
  let : (H.map φ).IsPrime := hHprime
  let : IsArtinianRing (PlaneSection φ H) := IsArtinianRing.of_finite F _
  have hmax : (H.map φ).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (IsArtinianRing.isField_of_isDomain _)
  have heq : H.map φ = I.map φ := hmax.eq_of_le hsurv hmap
  exact ((hIcomap.symm.trans (congrArg (Ideal.comap φ) heq.symm)).trans hHcomap).le
theorem proof : K1_14_2_2_4_5.c1 := by
  classical
  intro F _ φ k chart P Q S d hfin hd hlocal
  let : Algebra Ambient (Plane F) := φ.toAlgebra
  let : Module.Flat Ambient (Plane F) := chart.flat
  let J := RowIdeal P Q
  let : Module.Finite F (PlaneSection φ J) := hfin
  let T := S.filter fun I => sectionDegree I k ≠ 0
  have active (I : T) : Active (I : Ideal Ambient) :=
    (hlocal I (Finset.mem_filter.mp I.property).1).choose
  let point : T ↪ PrimeSpectrum Ambient :=
    ⟨fun I => ⟨I, (active I).prime⟩, fun _ _ h => Subtype.ext (congrArg PrimeSpectrum.asIdeal h)⟩
  have rank_eq (I : T) : Module.finrank F (PlaneSection φ I) = sectionDegree I k :=
    (chart.finite_rank I (active I)).2
  have length_ge (I : T) : (d : ℕ∞) ≤ K1_14_3_4_4.localColength (point I) J := by
    exact (hlocal I (Finset.mem_filter.mp I.property).1).choose_spec
      (Finset.mem_filter.mp I.property).2
  have survives (I : T) : (I : Ideal Ambient).map φ ≠ ⊤ := by
    intro htop
    let : Subsingleton (PlaneSection φ I) := Ideal.Quotient.subsingleton_iff.mpr htop
    exact (Finset.mem_filter.mp I.property).2
      ((rank_eq I).symm.trans (Module.finrank_eq_zero_of_subsingleton F _))
  have minimal (I : T) : (point I).asIdeal ∈ J.minimalPrimes := by
    have hle : J ≤ (point I).asIdeal := by
      by_contra hn
      have h := length_ge I
      rw [K1_14_3_4_4.localColength_eq_zero_of_not_le hn] at h
      exact hd.not_ge (ENat.natCast_le_natCast.mp (show (d : ℕ∞) ≤ (0 : ℕ) from h))
    exact minimal_of_section chart (active I).prime hle (survives I)
  let qs := T.attach.map point
  have hmin (q : PrimeSpectrum Ambient) (hq : q ∈ qs) : q.asIdeal ∈ J.minimalPrimes := by
    obtain ⟨I, _, rfl⟩ := Finset.mem_map.mp hq
    exact minimal I
  have hweighted := K1_14_3_4_4.weighted_lengths
    (S := Plane F) (k := F) J qs hmin J le_rfl
  change (∑ q ∈ qs, K1_14_3_4_4.localColength q J *
    Module.length F (PlaneSection φ q.asIdeal)) ≤ Module.length F (PlaneSection φ J)
    at hweighted
  rw [Module.length_eq_finrank F (PlaneSection φ J),
    show qs = T.attach.map point from rfl, Finset.sum_map] at hweighted
  have hsum : (∑ I ∈ T.attach, (d : ℕ∞) * (sectionDegree (I : Ideal Ambient) k : ℕ∞)) ≤
      (Module.finrank F (PlaneSection φ J) : ℕ∞) := by
    refine (Finset.sum_le_sum fun I _ => ?_).trans hweighted
    change _ ≤ K1_14_3_4_4.localColength (point I) J * Module.length F (PlaneSection φ I)
    let : Module.Finite F (PlaneSection φ I) := (chart.finite_rank I (active I)).1
    rw [Module.length_eq_finrank, rank_eq I]
    exact mul_le_mul_left (length_ge I) _
  rw [Finset.sum_attach T (fun I => (d : ℕ∞) * (sectionDegree I k : ℕ∞)),
    ← Finset.mul_sum] at hsum
  have hmass : (∑ I ∈ T, sectionDegree I k) = mass S k := Finset.sum_filter_ne_zero _
  rw [← Nat.cast_sum, hmass, ← Nat.cast_mul] at hsum
  exact ENat.natCast_le_natCast.mp hsum
end
end K1_14_2_2_4_5_1
end
section
set_option autoImplicit false
namespace K1_13_6_2_3_3_2_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_2_3 K1_13_6_2_3_1 K1_13_6_2_3_3_2 MvPolynomial
open scoped Pointwise
attribute [local instance] MvPolynomial.weightedGradedAlgebra
private abbrev Generator {k : ℕ} (boxes : Fin k → Shape) :=
  (i : Fin k) × capExponents (boxes i)
private abbrev slotWeight {k m : ℕ} {boxes : Fin k → Shape}
    (u : Fin m ≃ Generator boxes) (j : Fin m) : Fin k →₀ ℕ :=
  Finsupp.single (u j).1 1
private abbrev slotDegree {k m : ℕ} {boxes : Fin k → Shape}
    (u : Fin m ≃ Generator boxes) : (Fin m →₀ ℕ) →+ (Fin k →₀ ℕ) :=
  Finsupp.weight (slotWeight u)
abbrev exponentMap {k m : ℕ} {boxes : Fin k → Shape}
    (u : Fin m ≃ Generator boxes) : (Fin m →₀ ℕ) →+ (Fin 4 →₀ ℕ) :=
  Finsupp.weight (fun j => (u j).2.val)
private def taggedMap {k m : ℕ} {boxes : Fin k → Shape}
    (u : Fin m ≃ Generator boxes) : MvPolynomial (Fin m) GeoField →ₐ[GeoField] GeoJets :=
  aeval (fun j => monomial (u j).2.val 1)
private abbrev piece {k m : ℕ} {boxes : Fin k → Shape}
    (u : Fin m ≃ Generator boxes) :=
  weightedHomogeneousSubmodule GeoField (slotWeight u)
theorem slotDegree_apply {k m : ℕ} {boxes : Fin k → Shape}
    (u : Fin m ≃ Generator boxes) (a : Fin m →₀ ℕ) (i : Fin k) :
    slotDegree u a i = ∑ j ∈ Finset.univ.filter (fun j => (u j).1 = i), a j := by
  rw [Finsupp.weight_eq_sum, Finset.sum_filter]
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply, smul_eq_mul]
theorem cap_sum_zero {k : ℕ} (boxes : Fin k → Shape) :
    capExponents (sumShape boxes (0 : Fin k → ℕ)) = 0 := by
  simpa [sumShape, Shape.scale] using
    (nsmul_cap ⟨3, 3, 1⟩ ⟨by decide, by decide, by decide⟩ 0).symm
theorem sumShape_single {k : ℕ} (boxes : Fin k → Shape) (i : Fin k) (n : ℕ) :
    sumShape boxes (Finsupp.single i n) = (boxes i).scale n := by
  simp [sumShape, Finsupp.single_apply, Shape.scale, ite_mul]
private theorem sumShape_chamber {k : ℕ} (boxes : Fin k → Shape)
    (hb : ∀ i, ChamberBox (boxes i)) (a : Fin k →₀ ℕ) (ha : a ≠ 0) :
    ChamberBox (sumShape boxes a) := by
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra! h
    exact ha (Finsupp.ext h)
  refine ⟨?_, ?_, ?_⟩
  · change (∑ j, a j * (boxes j).j) ≤ ∑ j, a j * (boxes j).b
    exact Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_left (a j) (hb j).1)
  · change 3 * (∑ j, a j * (boxes j).t) ≤ ∑ j, a j * (boxes j).j
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => by
      rw [Nat.mul_left_comm]
      exact Nat.mul_le_mul_left _ (hb j).2.1)
  · exact (Nat.mul_pos (Nat.pos_of_ne_zero hi) (hb i).2.2).trans_le
      (Finset.single_le_sum (fun j _ => Nat.zero_le (a j * (boxes j).t))
        (Finset.mem_univ i))
theorem cap_sum_add {k : ℕ} (boxes : Fin k → Shape)
    (hb : ∀ i, ChamberBox (boxes i)) (a b : Fin k →₀ ℕ) :
    capExponents (sumShape boxes (⇑(a + b : Fin k →₀ ℕ))) =
      capExponents (sumShape boxes a) + capExponents (sumShape boxes b) := by
  by_cases ha : a = 0
  · simp [ha, cap_sum_zero]
  by_cases hb' : b = 0
  · simp [hb', cap_sum_zero]
  rw [cap_add (sumShape_chamber boxes hb a ha) (sumShape_chamber boxes hb b hb')]
  simp [sumShape, Shape.plus, Nat.add_mul, Finset.sum_add_distrib]
theorem exponentMap_mem_cap {k m : ℕ} {boxes : Fin k → Shape}
    (u : Fin m ≃ Generator boxes) (hb : ∀ i, ChamberBox (boxes i))
    (a : Fin m →₀ ℕ) : exponentMap u a ∈ capExponents (sumShape boxes (slotDegree u a)) := by
  induction a using Finsupp.induction_linear with
  | zero => simp [cap_sum_zero]
  | add a b ha hb' =>
    rw [map_add, map_add, cap_sum_add boxes hb (slotDegree u a) (slotDegree u b)]
    exact Set.add_mem_add ha hb'
  | single j n =>
    rw [Finsupp.weight_single, Finsupp.weight_single, Finsupp.smul_single_one,
      sumShape_single, ← nsmul_cap _ (hb (u j).1)]
    exact Set.nsmul_mem_nsmul (u j).2.property
theorem exists_exponent_lift {k m : ℕ} {boxes : Fin k → Shape}
    (u : Fin m ≃ Generator boxes) (hb : ∀ i, ChamberBox (boxes i)) (w : Fin k →₀ ℕ) :
    ∀ x ∈ capExponents (sumShape boxes w),
      ∃ a, slotDegree u a = w ∧ exponentMap u a = x := by
  induction w using Finsupp.induction_linear with
  | zero =>
    intro x hx
    change x ∈ capExponents (sumShape boxes (0 : Fin k → ℕ)) at hx
    rw [cap_sum_zero, Set.mem_zero] at hx
    exact ⟨0, map_zero _, (map_zero _).trans hx.symm⟩
  | add v w hv hw =>
    intro x hx
    rw [cap_sum_add boxes hb v w] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    obtain ⟨a, ha, hay⟩ := hv y hy
    obtain ⟨b, hb', hbz⟩ := hw z hz
    exact ⟨a + b, by rw [map_add, ha, hb'], by rw [map_add, hay, hbz]⟩
  | single i n =>
    simp only [sumShape_single, ← nsmul_cap _ (hb i)]
    induction n with
    | zero =>
      intro x hx
      rw [zero_smul, Set.mem_zero] at hx
      exact ⟨0, by simp, (map_zero _).trans hx.symm⟩
    | succ n ih =>
      intro x hx
      rw [succ_nsmul] at hx
      obtain ⟨y, hy, z, hz, rfl⟩ := hx
      obtain ⟨a, ha, hay⟩ := ih y hy
      let j := u.symm ⟨i, ⟨z, hz⟩⟩
      have hj : u j = ⟨i, ⟨z, hz⟩⟩ := u.apply_symm_apply _
      refine ⟨a + Finsupp.single j 1, ?_, ?_⟩
      · rw [map_add, ha, Finsupp.weight_single, one_smul]
        simp only [slotWeight, hj, ← Finsupp.single_add]
      · rw [map_add, hay, Finsupp.weight_single, one_smul, hj]
theorem taggedMap_monomial {k m : ℕ} {boxes : Fin k → Shape}
    (u : Fin m ≃ Generator boxes) (a : Fin m →₀ ℕ) :
    taggedMap u (monomial a 1) = monomial (exponentMap u a) 1 := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [← show monomial a (1 : GeoField) * monomial b 1 = monomial (a + b) 1 by simp,
      map_mul, ha, hb, monomial_mul_monomial, mul_one, map_add]
  | single j n =>
    rw [← X_pow_eq_monomial, map_pow, taggedMap, aeval_X, monomial_pow, one_pow,
      Finsupp.weight_single]
theorem piece_map {k m : ℕ} {boxes : Fin k → Shape}
    (u : Fin m ≃ Generator boxes) (hb : ∀ i, ChamberBox (boxes i)) (w : Fin k →₀ ℕ) :
    (piece u w).map (taggedMap u).toLinearMap =
      restrictSupport GeoField (capExponents (sumShape boxes w)) := by
  rw [show piece u w = restrictSupport GeoField {a | slotDegree u a = w} from
    weightedHomogeneousSubmodule_eq_finsupp_supported _ _ _]
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap,
      restrictSupport_eq_span GeoField {a | slotDegree u a = w}, Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    change taggedMap u (monomial a 1) ∈ restrictSupport GeoField _
    rw [taggedMap_monomial]
    exact (monomial_mem_restrictSupport _).mpr (Or.inl
      (show exponentMap u a ∈ capExponents (sumShape boxes w) from
        (show slotDegree u a = w from ha) ▸ exponentMap_mem_cap u hb a))
  · rw [restrictSupport_eq_span, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha, hax⟩ := exists_exponent_lift u hb w x hx
    exact ⟨monomial a 1, (monomial_mem_restrictSupport _).mpr (Or.inl ha), by
      change taggedMap u (monomial a 1) = _
      rw [taggedMap_monomial, hax]⟩
private theorem standard_rank {k m : ℕ} {boxes : Fin k → Shape}
    (u : Fin m ≃ Generator boxes) (hb : ∀ i, ChamberBox (boxes i)) (P : Ideal GeoJets)
    (o : MonomialOrder (Fin m)) :
    ∃ I : Ideal (MvPolynomial (Fin m) GeoField), ∀ w : Fin k →₀ ℕ,
      Module.finrank GeoField (capPiece P (sumShape boxes w)) =
        {a | a ∈ o.standardExponents I ∧ slotDegree u a = w}.ncard := by
  let J := P.comap (taggedMap u).toRingHom
  let I := (J.homogeneousCore (piece u)).toIdeal
  have hIJ : I ≤ J := Ideal.toIdeal_homogeneousCore_le (piece u) J
  have hI : I.IsHomogeneous (piece u) := (J.homogeneousCore (piece u)).isHomogeneous
  refine ⟨I, fun w => ?_⟩
  let mk := (Ideal.Quotient.mkₐ GeoField P).toLinearMap
  let φ := mk.comp (taggedMap u).toLinearMap
  let T := capPiece P (sumShape boxes w)
  let A := {a | a ∈ o.standardExponents I ∧ slotDegree u a = w}
  let S := restrictSupport GeoField A
  have hmap : (piece u w).map φ = T := by
    change (piece u w).map (mk.comp (taggedMap u).toLinearMap) =
      (restrictSupport GeoField (capExponents (sumShape boxes w))).map mk
    rw [Submodule.map_comp, piece_map u hb w]
  have hST : S ≤ piece u w := by
    intro f hf a ha
    exact (hf (mem_support_iff.mpr ha)).2
  let L : S →ₗ[GeoField] T := (φ.domRestrict S).codRestrict T (fun f =>
    hmap ▸ Submodule.mem_map.mpr ⟨f, hST f.2, rfl⟩)
  have hinj : Function.Injective L := by
    intro f g hfg
    have heq : φ f = φ g := congrArg Subtype.val hfg
    have hf : (f : MvPolynomial (Fin m) GeoField) ∈ piece u w := hST f.2
    have hg : (g : MvPolynomial (Fin m) GeoField) ∈ piece u w := hST g.2
    have hsub : (f : MvPolynomial (Fin m) GeoField) - g ∈ J := by
      change Ideal.Quotient.mk P (taggedMap u f) = Ideal.Quotient.mk P (taggedMap u g) at heq
      change taggedMap u ((f : MvPolynomial (Fin m) GeoField) - g) ∈ P
      rw [map_sub]
      exact Ideal.Quotient.eq.mp heq
    apply Subtype.ext
    exact o.eq_of_mem_standardSpace_of_sub_mem
      (fun a ha => (f.2 ha).1) (fun a ha => (g.2 ha).1)
      (Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨w, (piece u w).sub_mem hf hg⟩ hsub)
  have hsurj : Function.Surjective L := by
    intro y
    have hy : y.val ∈ (piece u w).map φ := by
      rw [hmap]
      exact y.property
    obtain ⟨f, hf, hfy⟩ := Submodule.mem_map.mp hy
    obtain ⟨q, hq, hfq, _⟩ := o.exists_mem_standardSpace_sub_mem I f
    let r := weightedHomogeneousComponent (slotWeight u) w q
    have hr : r ∈ S := by
      intro a ha
      have hw : r.IsWeightedHomogeneous (slotWeight u) w :=
        weightedHomogeneousComponent_isWeightedHomogeneous w q
      refine ⟨hq ?_, hw (mem_support_iff.mp ha)⟩
      change a ∈ (weightedHomogeneousComponent (slotWeight u) w q).support at ha
      rw [support_weightedHomogeneousComponent] at ha
      exact (Finset.mem_filter.mp ha).1
    have hfr : f - r ∈ I := by
      have hc := weightedHomogeneousComponent_mem_of_mem _ _ hI hfq w
      rwa [map_sub, weightedHomogeneousComponent_eq_self (show
        f.IsWeightedHomogeneous (slotWeight u) w from hf)] at hc
    have hzero : φ (f - r) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hfr)
    rw [map_sub, sub_eq_zero] at hzero
    exact ⟨⟨r, hr⟩, Subtype.ext (hzero.symm.trans hfy)⟩
  change Module.finrank GeoField T = A.ncard
  rw [← (LinearEquiv.ofBijective L ⟨hinj, hsurj⟩).finrank_eq,
    Module.finrank_eq_nat_card_basis (basisRestrictSupport GeoField A), Nat.card_coe_set_eq]
theorem proof : K1_13_6_2_3_3_2.c1 := by
  classical
  intro P k boxes _ hb
  let _ : Fintype (Generator boxes) := Fintype.ofFinite _
  let u := (Fintype.equivFin (Generator boxes)).symm
  let slot := fun j => (u j).1
  let o : MonomialOrder (Fin (Fintype.card (Generator boxes))) := MonomialOrder.degLex
  obtain ⟨I, hI⟩ := standard_rank u hb P o
  obtain ⟨bad, hbad⟩ := o.exists_finset_standardExponents_iff I
  refine ⟨_, slot, bad, fun w => ?_⟩
  let v : Fin k →₀ ℕ := Finsupp.equivFunOnFinite.symm w
  change Module.finrank GeoField (capPiece P (sumShape boxes v)) = standardCount slot bad w
  rw [hI v]
  unfold standardCount
  congr 1
  ext a
  simp only [Set.mem_ofPred_eq, hbad]
  apply and_congr_right'
  constructor
  · intro ha i
    rw [← slotDegree_apply u a i, ha]
    rfl
  · intro ha
    ext i
    rw [slotDegree_apply]
    exact ha i
end
end K1_13_6_2_3_3_2_1
end
section
namespace K1_13_6_2_2_1
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_1 K1_13_6 K1_13_6_2 K1_13_6_2_2
open scoped BigOperators
local notation "W" => MvPolynomial.weightedTotalDegree
theorem const_mul_bound {n : ℕ} (w : Fin n → ℕ) (a : Geom[X]) (P : Row n) :
    W w (MvPolynomial.C a * P) ≤ W w P := by
  simpa only [weightedTotalDegree_C, zero_add] using
    weightedTotalDegree_mul_le w (MvPolynomial.C a) P
theorem var_bound {n : ℕ} (w : Fin n → ℕ) (i : Fin n) :
    W w (MvPolynomial.X i : Row n) ≤ w i :=
  mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    (X_mem_restrictWeightedDegree _ _ _ le_rfl)
private theorem coefficient_bound {n : ℕ} (w : Fin n → ℕ) (P : Row n) :
    W w (∑ m ∈ P.support, MvPolynomial.monomial m (derivative (P.coeff m))) ≤ W w P := by
  classical
  apply Finset.sup_mono
  intro m hm
  obtain ⟨j, hj, hmj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  have h : j = m := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hmj)
      (by rw [MvPolynomial.coeff_monomial, ite_eq_right hne])
  exact h ▸ hj
theorem shift_bound {n : ℕ} (w : Fin n → ℕ) (i j : Fin n) (P : Row n)
    (δ : ℕ) (h : w j ≤ w i + δ) :
    W w (MvPolynomial.X j * pderiv i P) ≤ W w P + δ := by
  apply Finset.sup_le
  intro m hm
  rw [MvPolynomial.mem_support_iff, coeff_X_mul'] at hm
  split_ifs at hm with hj
  · have hn : m - Finsupp.single j 1 + Finsupp.single i 1 ∈ P.support := by
      rw [coeff_pderiv] at hm
      exact MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hm)
    have hw := le_weightedTotalDegree w hn
    have he := Finsupp.weight_sub_single_add (w := w) (Finsupp.mem_support_iff.mp hj)
    rw [map_add, Finsupp.weight_single, one_smul] at hw
    omega
  · exact (hm rfl).elim
private theorem flow_bound {n : ℕ} (w : Fin (n + 1) → ℕ) (δ : ℕ)
    (hshift : ∀ i : Fin n, w i.succ ≤ w i.castSucc + δ) (P : Row (n + 1))
    {d : ℕ} (hP : W w P ≤ d) :
    W w ((∑ m ∈ P.support, MvPolynomial.monomial m (derivative (P.coeff m))) +
      ∑ i : Fin n, MvPolynomial.C (Polynomial.C ((i.val + 1 : ℕ) : Geom)) *
        MvPolynomial.X i.succ * pderiv i.castSucc P) ≤ d + δ := by
  classical
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.add_mem
  · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
      ((coefficient_bound w P).trans (hP.trans (Nat.le_add_right _ _)))
  · apply Submodule.sum_mem
    intro i _
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    rw [mul_assoc]
    exact (const_mul_bound w _ _).trans
      ((shift_bound w _ _ P δ (hshift i)).trans (Nat.add_le_add_right hP δ))
private theorem lift_weight (w : Fin 5 → ℕ) (P : Row 4) :
    W w (lift4 P) = W (w ∘ Fin.castSucc) P :=
  weightedTotalDegree_rename_of_injective (Fin.castSucc_injective 4)
private theorem separant_bound (w : Fin 5 → ℕ) {g : Row 4} {B : ℕ}
    (hg : W (w ∘ Fin.castSucc) g ≤ B) :
    W w (lift4 (separant g)) ≤ B - w ((3 : Fin 4).castSucc) := by
  rw [lift_weight, separant]
  exact (weightedTotalDegree_pderiv_le_sub _ _ _).trans (Nat.sub_le_sub_right hg _)
theorem graph_bound (w : Fin 5 → ℕ) (δ : ℕ)
    (hshift : ∀ i : Fin 4, w i.succ ≤ w i.castSucc + δ)
    {g : Row 4} {B : ℕ} (hg : W (w ∘ Fin.castSucc) g ≤ B)
    (hB : w ((3 : Fin 4).castSucc) ≤ B) :
    W w (rawGraph g) ≤ B + δ := by
  have hshift' (i : Fin 3) :
      (w ∘ Fin.castSucc) i.succ ≤ (w ∘ Fin.castSucc) i.castSucc + δ := by
    exact hshift i.castSucc
  have hlast : w (Fin.last 4) ≤ w ((3 : Fin 4).castSucc) + δ := hshift 3
  unfold rawGraph
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.add_mem
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    rw [lift_weight]
    exact flow_bound _ δ hshift' g hg
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    rw [mul_assoc]
    exact (const_mul_bound w _ _).trans ((weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add (separant_bound w hg) (var_bound w _)).trans (by omega)))
private theorem numerator_bound (w : Fin 5 → ℕ) (δ : ℕ)
    (hshift : ∀ i : Fin 4, w i.succ ≤ w i.castSucc + δ)
    (hlast : w (Fin.last 4) = w ((3 : Fin 4).castSucc) + δ)
    {g : Row 4} {B : ℕ} (hg : W (w ∘ Fin.castSucc) g ≤ B)
    (hB : w ((3 : Fin 4).castSucc) ≤ B) (k : ℕ) :
    W w (numerator g k) ≤ w (Fin.last 4) + k * (B - w ((3 : Fin 4).castSucc) + δ) := by
  let s := B - w ((3 : Fin 4).castSucc)
  have hS : W w (lift4 (separant g)) ≤ s := separant_bound w hg
  have hU : W w (fifthFlow g) ≤ B + δ + δ :=
    (const_mul_bound w _ _).trans (flow_bound w δ hshift _ (graph_bound w δ hshift hg hB))
  have hDS : W w (fixedFlow (lift4 (separant g))) ≤ s + δ :=
    flow_bound w δ hshift _ hS
  change W w (numerator g k) ≤ w (Fin.last 4) + k * (s + δ)
  induction k with
  | zero =>
    simpa only [numerator, zero_mul, add_zero] using
      (const_mul_bound w _ _).trans (var_bound w (Fin.last 4))
  | succ k ih =>
    let d := w (Fin.last 4) + k * (s + δ)
    rw [numerator, Nat.succ_mul, ← Nat.add_assoc]
    change W w (_ + _ - _) ≤ d + (s + δ)
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply Submodule.sub_mem
    · apply Submodule.add_mem
      · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        have hDP : W w (fixedFlow (numerator g k)) ≤ d + δ := flow_bound w δ hshift _ ih
        exact (weightedTotalDegree_mul_le _ _ _).trans
          ((Nat.add_le_add hS hDP).trans (by omega))
      · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        have hP : W w (pderiv (Fin.last 4) (numerator g k)) ≤ k * (s + δ) := by
          simpa only [Nat.add_sub_cancel_left] using
            (weightedTotalDegree_pderiv_le_sub w (Fin.last 4) (numerator g k)).trans
              (Nat.sub_le_sub_right ih (w (Fin.last 4)))
        have hu : B + δ + δ = w (Fin.last 4) + (s + δ) := by
          dsimp only [s]
          omega
        exact (weightedTotalDegree_mul_le _ _ _).trans
          ((Nat.add_le_add hU hP).trans (by rw [hu]; dsimp only [d]; omega))
    · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
      apply (weightedTotalDegree_mul_le _ _ _).trans
      rw [← map_natCast (MvPolynomial.C : Geom[X] →+* Row 5)]
      exact (Nat.add_le_add ((const_mul_bound w _ _).trans hDS) ih).trans (by omega)
private theorem denominator_bound (w : Fin 5 → ℕ) {g : Row 4} {B : ℕ}
    (hg : W (w ∘ Fin.castSucc) g ≤ B) (k : ℕ) :
    W w (denominator g k) ≤ k * (B - w ((3 : Fin 4).castSucc)) :=
  (weightedTotalDegree_pow_le _ _ _).trans (Nat.mul_le_mul_left _ (separant_bound w hg))
private theorem padded_bound (w : Fin 5 → ℕ) (δ : ℕ)
    (hshift : ∀ i : Fin 4, w i.succ ≤ w i.castSucc + δ)
    (hlast : w (Fin.last 4) = w ((3 : Fin 4).castSucc) + δ)
    (hw : ∀ i : Fin 4, w i.castSucc ≤ w (Fin.last 4))
    {g : Row 4} {B : ℕ} (hg : W (w ∘ Fin.castSucc) g ≤ B)
    (hB : w ((3 : Fin 4).castSucc) ≤ B) (k i : ℕ) (hi : i ≤ k + 4) :
    W w (padded g k i) ≤ w (Fin.last 4) + k * (B - w ((3 : Fin 4).castSucc) + δ) := by
  let s := B - w ((3 : Fin 4).castSucc)
  change W w (padded g k i) ≤ w (Fin.last 4) + k * (s + δ)
  unfold padded
  split_ifs with hinit
  · apply (weightedTotalDegree_mul_le _ _ _).trans
    have hx : W w (lift4 (MvPolynomial.X ⟨i, hinit⟩)) ≤ w (Fin.last 4) := by
      rw [lift_weight]
      exact (var_bound _ _).trans (hw ⟨i, hinit⟩)
    exact Nat.add_le_add ((const_mul_bound w _ _).trans hx)
      ((denominator_bound w hg k).trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)))
  · let a := i - 4
    have ha : a ≤ k := by dsimp [a]; omega
    apply (weightedTotalDegree_mul_le _ _ _).trans
    calc
      _ ≤ (w (Fin.last 4) + a * (s + δ)) + (k - a) * s :=
        Nat.add_le_add (numerator_bound w δ hshift hlast hg hB a)
          (denominator_bound w hg (k - a))
      _ ≤ (w (Fin.last 4) + a * (s + δ)) + (k - a) * (s + δ) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)) _
      _ = _ := by rw [Nat.add_assoc, ← Nat.add_mul, Nat.add_sub_of_le ha]
private theorem support_bounds (w : Fin 5 → ℕ) (δ : ℕ)
    (hshift : ∀ i : Fin 4, w i.succ ≤ w i.castSucc + δ)
    (hlast : w (Fin.last 4) = w ((3 : Fin 4).castSucc) + δ)
    (hw : ∀ i : Fin 4, w i.castSucc ≤ w (Fin.last 4))
    {g : Row 4} {B : ℕ} (hg : W (w ∘ Fin.castSucc) g ≤ B)
    (hB : w ((3 : Fin 4).castSucc) ≤ B) :
    W w (rawGraph g) ≤ B + δ ∧
      ∀ k : ℕ, let d := w (Fin.last 4) + k * (B - w ((3 : Fin 4).castSucc) + δ)
        W w (denominator g k) ≤ d ∧ ∀ i ≤ k + 4, W w (padded g k i) ≤ d := by
  refine ⟨graph_bound w δ hshift hg hB, fun k => ⟨?_, padded_bound w δ hshift hlast hw hg hB k⟩⟩
  exact (denominator_bound w hg k).trans
    ((Nat.mul_le_mul_left _ (Nat.le_add_right _ _)).trans (Nat.le_add_left _ _))
private def topWeight : Fin 5 → ℕ := Fin.lastCases 2 (Pi.single (3 : Fin 4) 1)
private def fifthWeight : Fin 5 → ℕ := Pi.single (Fin.last 4) 1
private theorem box_of_weights (P : Row 5) {b j t d : ℕ}
    (hb : W 1 P ≤ b) (hj : W Fin.val P ≤ j) (ht : W topWeight P ≤ t)
    (hd : W fifthWeight P ≤ d) :
    Box5 ⟨b, j, min t (j / 3)⟩ d (generic5 P) := by
  have source (m : Fin 5 →₀ ℕ) (hm : m ∈ (generic5 P).support) : m ∈ P.support :=
    MvPolynomial.support_map_subset genericCoeffs P hm
  constructor
  · intro m hm
    have hb' := (le_weightedTotalDegree (1 : Fin 5 → ℕ) (source m hm)).trans hb
    have hj' := (le_weightedTotalDegree Fin.val (source m hm)).trans hj
    have ht' := (le_weightedTotalDegree topWeight (source m hm)).trans ht
    rw [Finsupp.weight_eq_sum, Fin.sum_univ_castSucc] at hb' hj' ht'
    simp only [Pi.one_apply, smul_eq_mul, mul_one] at hb'
    simp only [Fin.val_castSucc, smul_eq_mul] at hj'
    simp [topWeight, Pi.single_apply] at ht'
    have hIndex : (∑ i : Fin 4, i.val * m i.castSucc) ≤ j := by
      simpa only [Nat.mul_comm] using (Nat.le_add_right _ _).trans hj'
    have hThree : 3 * m (3 : Fin 4).castSucc ≤ (∑ i : Fin 4, i.val * m i.castSucc) :=
      Finset.single_le_sum (f := fun i : Fin 4 => i.val * m i.castSucc)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (3 : Fin 4))
    refine ⟨(Nat.le_add_right _ _).trans hb', hIndex, le_min ?_ ?_⟩
    · exact (Nat.le_add_right _ _).trans ht'
    · exact (Nat.le_div_iff_mul_le (by decide : 0 < 3)).mpr
        (by simpa only [Nat.mul_comm] using hThree.trans hIndex)
  · intro m hm
    simpa only [fifthWeight, Finsupp.weight_single_one_apply] using
      (le_weightedTotalDegree fifthWeight (source m hm)).trans hd
end
end K1_13_6_2_2_1
end
