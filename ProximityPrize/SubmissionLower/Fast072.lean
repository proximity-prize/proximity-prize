import ProximityPrize.SubmissionLower.Fast068
import ProximityPrize.SubmissionLower.Fast069
import ProximityPrize.SubmissionLower.Fast070
import ProximityPrize.SubmissionLower.Fast071
set_option Elab.async false
set_option autoImplicit true
section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace K1_11_3
noncomputable section
open K1 K1_11 MvPolynomial
def c1 : Prop :=
  ∀ {F : Type} [Field F] (G : MvPolynomial (Fin 4) F) (w E : ℕ),
    2 ≤ E → G.weightedTotalDegree scalarWeightTotal ≤ E →
    ∀ n ≤ w, (paddedTaylorCoeff G w n).weightedTotalDegree scalarWeightTotal ≤
      (2 * w - 1) * (E - 1) + 1
def c2 : Prop :=
  ∀ {F : Type} [Field F] (G : MvPolynomial (Fin 4) F) (w : ℕ)
    (D : Polynomial F) (s t : F),
    aeval (scalarImages D s t) G = 0 →
    ∀ n ≤ w, (↑(Nat.factorial n) : F) ≠ 0 →
      aeval (scalarImages D s t) (paddedTaylorCoeff G w n) =
        aeval (scalarImages D s t) (pderiv 1 G) ^ (2 * w - 1) *
          Polynomial.hasseDeriv n D
section Field
variable {F : Type} [Field F]
abbrev XF (F : Type) [Field F] := FractionRing (Polynomial F)
private def ξ : XF F := algebraMap (Polynomial F) (XF F) Polynomial.X
def centerImages : Fin 4 → MvPolynomial (Fin 3) (XF F) :=
  ![C (ξ (F := F)), MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2]
private def atCenter : MvPolynomial (Fin 4) F →ₐ[F] MvPolynomial (Fin 3) (XF F) :=
  aeval centerImages
private def centerPoint (D : Polynomial F) (s t : F) : Fin 3 → XF F :=
  ![algebraMap (Polynomial F) (XF F) D, algebraMap F (XF F) s, algebraMap F (XF F) t]
private theorem atCenter_degree (G : MvPolynomial (Fin 4) F) :
    (atCenter G).totalDegree ≤ G.weightedTotalDegree scalarWeightTotal := by
  let ι := algebraMap F (XF F)
  have hm : aeval (R := XF F) (centerImages (F := F)) (MvPolynomial.map ι G) =
      atCenter G := MvPolynomial.aeval_map_algebraMap (A := XF F) _ _
  rw [← hm, ← weightedTotalDegree_one]
  refine (weightedTotalDegree_aeval_le_of_le scalarWeightTotal (1 : Fin 3 → ℕ)
    centerImages (MvPolynomial.map ι G) ?_).trans ?_
  · intro i
    fin_cases i <;> simp [centerImages, scalarWeightTotal, weightedTotalDegree_one]
  · exact Finset.sup_mono (support_map_subset _ _)
private theorem pderiv_atCenter (G : MvPolynomial (Fin 4) F) :
    pderiv (0 : Fin 3) (atCenter G) = atCenter (pderiv 1 G) := by
  classical
  induction G using MvPolynomial.induction_on with
  | C a => simp [atCenter]
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul_X a j ha =>
    simp only [map_mul, pderiv_mul, map_add, ha]
    fin_cases j <;> simp [atCenter, centerImages]
theorem emb_C (a : F) :
    algebraMap (Polynomial F) (XF F) (Polynomial.C a) = algebraMap F (XF F) a := by
  rw [IsScalarTower.algebraMap_apply F (Polynomial F) (XF F), Polynomial.algebraMap_eq]
private theorem eval_atCenter (G : MvPolynomial (Fin 4) F)
    (D : Polynomial F) (s t : F) :
    MvPolynomial.eval (centerPoint D s t) (atCenter G) =
      algebraMap (Polynomial F) (XF F) (aeval (scalarImages D s t) G) := by
  have h : (MvPolynomial.eval (centerPoint D s t)).comp atCenter.toRingHom =
      (algebraMap (Polynomial F) (XF F)).comp (aeval (scalarImages D s t)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [atCenter, Polynomial.algebraMap_eq, emb_C]
    · intro i
      fin_cases i <;> simp [atCenter, centerImages, centerPoint, scalarImages, ξ, emb_C]
  exact RingHom.congr_fun h G
theorem eval_at_ξ (D : Polynomial F) :
    (D.map (algebraMap F (XF F))).eval (ξ (F := F)) =
      algebraMap (Polynomial F) (XF F) D := by
  rw [Polynomial.eval_map]
  have h : Polynomial.eval₂RingHom (algebraMap F (XF F)) ξ =
      algebraMap (Polynomial F) (XF F) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [emb_C]
    · simp [ξ]
  exact RingHom.congr_fun h D
private theorem derivativeChart_degree (G : MvPolynomial (Fin 4) F) (j : ℕ) :
    (derivativeChart G j).weightedTotalDegree scalarWeightTotal ≤
      G.weightedTotalDegree scalarWeightTotal := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
      unfold derivativeChart at *
      rw [Function.iterate_succ_apply']
      exact (weightedTotalDegree_pderiv_le _ _ _).trans ih
private def denominator (G : MvPolynomial (Fin 4) F) (w : ℕ) :
    MvPolynomial (Fin 3) (XF F) :=
  atCenter (pderiv 1 G) ^ (2 * w - 1)
private def numerator (G : MvPolynomial (Fin 4) F) (w : ℕ) :
    Polynomial (MvPolynomial (Fin 3) (XF F)) :=
  Polynomial.centeredCoefficientPrefix (C ξ) (fun n => atCenter (paddedTaylorCoeff G w n)) (w + 1)
private theorem natDegree_le_of_degree_lt_succ {R : Type} [Semiring R]
    {D : Polynomial R} {w : ℕ} (h : D.degree < ↑(w + 1)) : D.natDegree ≤ w := by
  by_cases hz : D = 0
  · simp [hz]
  · exact Nat.le_of_lt_succ ((Polynomial.natDegree_lt_iff_degree_lt hz).mpr h)
private theorem numerator_degree (G : MvPolynomial (Fin 4) F) (w : ℕ) :
    (numerator G w).natDegree ≤ w :=
  natDegree_le_of_degree_lt_succ
    (Polynomial.degree_centeredCoefficientPrefix_lt
      (C ξ) (fun n => atCenter (paddedTaylorCoeff G w n)) (w + 1))
private theorem numerator_eval_degree (h1 : c1) (G : MvPolynomial (Fin 4) F) (w E : ℕ)
    (hE : 2 ≤ E) (hG : G.weightedTotalDegree scalarWeightTotal ≤ E) (x : XF F) :
    ((numerator G w).eval (C x)).totalDegree ≤ (2 * w - 1) * (E - 1) + 1 := by
  unfold numerator Polynomial.centeredCoefficientPrefix
  rw [Polynomial.taylor_eval, Polynomial.eval_finsetSum]
  apply totalDegree_finsetSum_le
  intro n _
  rw [Polynomial.eval_monomial, ← map_neg, ← map_add, ← map_pow]
  exact (totalDegree_mul _ _).trans (by
    rw [totalDegree_C, add_zero]
    exact (atCenter_degree _).trans (h1 G w E hE hG n (Nat.le_of_lt_succ n.isLt)))
private theorem denominator_degree (G : MvPolynomial (Fin 4) F) (w E : ℕ)
    (hG : G.weightedTotalDegree scalarWeightTotal ≤ E) :
    (denominator G w).totalDegree ≤ (2 * w - 1) * (E - 1) := by
  apply (totalDegree_pow _ _).trans
  apply Nat.mul_le_mul_left
  exact (atCenter_degree _).trans
    ((weightedTotalDegree_pderiv_le_sub scalarWeightTotal 1 G).trans
      (Nat.sub_le_sub_right hG 1))
private theorem reconstruct (h2 : c2) (G : MvPolynomial (Fin 4) F) (w : ℕ)
    (D : Polynomial F) (s t : F) (hD : D.natDegree ≤ w)
    (hroot : aeval (scalarImages D s t) G = 0)
    (hfactor : ∀ n ≤ w, (↑(Nat.factorial n) : F) ≠ 0) :
    (numerator G w).map (MvPolynomial.eval (centerPoint D s t)) =
      Polynomial.C (MvPolynomial.eval (centerPoint D s t) (denominator G w)) *
        D.map (algebraMap F (XF F)) := by
  let ev := MvPolynomial.eval (centerPoint D s t)
  change (numerator G w).map ev = Polynomial.C (ev (denominator G w)) * _
  apply Polynomial.taylor_injective ξ
  ext n
  have hm := Polynomial.map_taylor (numerator G w) (C (ξ (F := F))) ev
  change _ = Polynomial.taylor (ev (C ξ)) _ at hm
  rw [MvPolynomial.eval_C] at hm
  rw [← hm, Polynomial.coeff_map, numerator, Polynomial.coeff_taylor_centeredCoefficientPrefix]
  rw [show Polynomial.taylor ξ (Polynomial.C (ev (denominator G w)) *
      D.map (algebraMap F (XF F))) =
      Polynomial.C (ev (denominator G w)) *
        Polynomial.taylor ξ (D.map (algebraMap F (XF F))) by
    calc
      _ = Polynomial.taylor ξ (Polynomial.C (ev (denominator G w))) *
          Polynomial.taylor ξ (D.map (algebraMap F (XF F))) :=
        map_mul (Polynomial.taylorAlgHom ξ) _ _
      _ = _ := by rw [Polynomial.taylor_C]]
  rw [Polynomial.coeff_C_mul]
  split_ifs with hn
  · have h := h2 G w D s t hroot n (Nat.le_of_lt_succ hn) (hfactor n (Nat.le_of_lt_succ hn))
    rw [show ev (atCenter (paddedTaylorCoeff G w n)) = _ from eval_atCenter _ D s t,
      h, map_mul, map_pow, Polynomial.taylor_coeff, Polynomial.hasseDeriv_map, eval_at_ξ]
    simp only [denominator, map_pow, ev, eval_atCenter]
  · have hd : (Polynomial.taylor ξ (D.map (algebraMap F (XF F)))).natDegree < n := by
      rw [Polynomial.natDegree_taylor]
      exact Polynomial.natDegree_map_le.trans_lt (hD.trans_lt (by omega))
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hd, mul_zero, map_zero]
end Field
end
end K1_11_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace K1_11_1
noncomputable section
open Polynomial Matrix FrobeniusLocator K1
def c1 : Prop :=
  ∀ (F : Type) [Field F] (h L s : ℕ)
    (Q : Fin 2 × Fin (h + 1) → Seeds F),
    h + s = L → 0 < s → Q ≠ 0 → coefficientPrimitive Q →
    let W := K1_6.shifts (planePair Q) L s
    coefficientPrimitive (K1_6.maximalMinors W) ∧
      ∀ b i : Fin 2, 0 < blockDegree Q b i →
        ∃ rows : Fin s → Fin L,
          (K1_6.maximalMinors W (fun j => (b, rows j))).degreeOf i =
            s * blockDegree Q b i
def c2 : Prop :=
  ∀ (F : Type) [Field F] (L w s : ℕ)
    (M : Matrix (Fin 2 × Fin L) (Fin w) (Seeds F))
    (W : Matrix (Fin 2 × Fin L) (Fin s) (Seeds F)),
    0 < s → s ≤ L →
    (M.map (algebraMap (Seeds F) (PlaneField F))).rank + s = 2 * L →
    W.transpose * M = 0 →
    (∀ b j (i : Fin 2), (M b j).degreeOf i ≤ if b.1 = i then 1 else 0) →
    coefficientPrimitive (K1_6.maximalMinors W) →
    ∀ (b i : Fin 2) (rows : Fin s → Fin L),
      (K1_6.maximalMinors W (fun j => (b, rows j))).degreeOf i ≤
        if b = i then L - s else L
end
end K1_11_1
end
section
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace K1_11_2_1
noncomputable section
open K1 K1_11 K1_11_2 MvPolynomial FrobeniusLocator
variable {F : Type*} [Field F]
def coefficientGraph (q : ℕ) : MvPolynomial (Fin 4) F →ₐ[F] Polynomial F :=
  aeval ![0, 0, Polynomial.X, Polynomial.X ^ q]
theorem graph_eq_map (q : ℕ) (P : MvPolynomial (Fin 5) F) :
    graph q P = (finSuccEquiv F 4 P).map (coefficientGraph q).toRingHom := by
  have h : graph (F := F) q =
      (Polynomial.mapAlgHom (coefficientGraph q)).comp (finSuccEquiv F 4).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change graph q (MvPolynomial.X 0) =
        (finSuccEquiv F 4 (MvPolynomial.X 0)).map (coefficientGraph q).toRingHom
      simp [graph, finSuccEquiv_X_zero]
    · change graph q (MvPolynomial.X j.succ) =
        (finSuccEquiv F 4 (MvPolynomial.X j.succ)).map (coefficientGraph q).toRingHom
      rw [finSuccEquiv_X_succ, Polynomial.map_C]
      fin_cases j <;> simp [graph, coefficientGraph]
  exact DFunLike.congr_fun h P
def coefficientVars : Fin 2 → Fin 4 := ![2, 3]
theorem coefficientVars_injective : Function.Injective coefficientVars := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | contradiction
theorem coefficientGraph_ne_zero (q : ℕ) (hq : 0 < q) (Q : MvPolynomial (Fin 4) F)
    (hQ : Q ≠ 0) (h0 : Q.degreeOf 0 = 0) (h1 : Q.degreeOf 1 = 0)
    (hS : Q.degreeOf 2 < q) : coefficientGraph q Q ≠ 0 := by
  classical
  obtain ⟨R, rfl⟩ := exists_rename_eq_of_vars_subset_range Q coefficientVars
    coefficientVars_injective (by
      intro i hi
      have hi' := mem_vars_iff_degreeOf_ne_zero.mp hi
      fin_cases i
      · exact (hi' h0).elim
      · exact (hi' h1).elim
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩)
  have hR : R ≠ 0 := fun h => hQ (by rw [h, map_zero])
  have hdeg : R.degreeOf 0 < q := by
    rw [← degreeOf_rename_of_injective coefficientVars_injective (0 : Fin 2)]
    exact hS
  have he : coefficientGraph (F := F) q (rename coefficientVars R) =
      K1_14.frobeniusGraph q R := by
    have hv : (![0, 0, Polynomial.X, Polynomial.X ^ q] : Fin 4 → Polynomial F) ∘
        coefficientVars = ![Polynomial.X, Polynomial.X ^ q] := by
      funext i
      fin_cases i <;> rfl
    rw [coefficientGraph, aeval_rename, hv, K1_14.frobeniusGraph]
  rw [he]
  exact K1_14.frobeniusGraph_ne_zero q hq R hR hdeg
theorem coefficientGraph_coeff_ne_zero (q : ℕ) (hq : 0 < q)
    (P : MvPolynomial (Fin 5) F) (hP : OmitsMessages P)
    (hS : P.degreeOf 3 < q) (i : ℕ) (hi : (finSuccEquiv F 4 P).coeff i ≠ 0) :
    coefficientGraph q ((finSuccEquiv F 4 P).coeff i) ≠ 0 := by
  apply coefficientGraph_ne_zero q hq _ hi
  · exact Nat.eq_zero_of_le_zero ((degreeOf_coeff_finSuccEquiv P 0 i).trans hP.1.le)
  · exact Nat.eq_zero_of_le_zero ((degreeOf_coeff_finSuccEquiv P 1 i).trans hP.2.le)
  · exact (degreeOf_coeff_finSuccEquiv P 2 i).trans_lt hS
theorem graph_natDegree (q : ℕ) (hq : 0 < q) (P : MvPolynomial (Fin 5) F)
    (hP : OmitsMessages P) (hS : P.degreeOf 3 < q) :
    (graph q P).natDegree = P.degreeOf 0 := by
  by_cases hz : P = 0
  · simp [hz]
  have hv : finSuccEquiv F 4 P ≠ 0 := by
    intro h
    exact hz ((finSuccEquiv F 4).injective (h.trans (map_zero _).symm))
  rw [graph_eq_map, Polynomial.natDegree_map_of_leadingCoeff_ne_zero, natDegree_finSuccEquiv]
  exact coefficientGraph_coeff_ne_zero q hq P hP hS _
    (Polynomial.leadingCoeff_ne_zero.mpr hv)
theorem x_eval_zero_of_graph (q : ℕ) (hq : 0 < q) (P : MvPolynomial (Fin 5) F)
    (hP : OmitsMessages P) (hS : P.degreeOf 3 < q) (x : F)
    (h : (graph q P).eval (Polynomial.C x) = 0) :
    (finSuccEquiv F 4 P).eval (C x) = 0 := by
  let Q := (finSuccEquiv F 4 P).eval (C x)
  have hQ (j : Fin 4) : Q.degreeOf j ≤ P.degreeOf j.succ := by
    let V := finSuccEquiv F 4 P
    change (V.eval (C x)).degreeOf j ≤ _
    rw [Polynomial.eval_eq_sum_range]
    apply (degreeOf_sum_le _ _ _).trans
    apply Finset.sup_le
    intro i _
    exact (degreeOf_mul_le j _ _).trans (by
      simpa only [← map_pow, degreeOf_C, add_zero] using degreeOf_coeff_finSuccEquiv P j i)
  have h0 : coefficientGraph q Q = 0 := by
    have hc : coefficientGraph q (C x : MvPolynomial (Fin 4) F) = Polynomial.C x := by
      simp [coefficientGraph]
    have he := Polynomial.eval_map_apply (coefficientGraph q).toRingHom (C x)
      (p := finSuccEquiv F 4 P)
    change ((finSuccEquiv F 4 P).map (coefficientGraph q).toRingHom).eval
      (coefficientGraph q (C x)) = coefficientGraph q Q at he
    rw [hc, ← graph_eq_map] at he
    exact he.symm.trans h
  by_contra hn
  exact coefficientGraph_ne_zero q hq Q hn
    (Nat.eq_zero_of_le_zero ((hQ 0).trans hP.1.le))
    (Nat.eq_zero_of_le_zero ((hQ 1).trans hP.2.le))
    ((hQ 2).trans_lt hS) h0
theorem locator_dvd (S : Finset I) (P : Polynomial (MvPolynomial (Fin 4) K))
    (h : ∀ i ∈ S, P.eval (C (node i)) = 0) :
    (locator node S).map C ∣ P := by
  classical
  let R := MvPolynomial (Fin 4) K
  let f : R →+* FractionRing R := algebraMap R (FractionRing R)
  have hf : Function.Injective f := IsFractionRing.injective R (FractionRing R)
  apply (Polynomial.map_dvd_map f hf ((locator_monic node S).map C)).mp
  rw [Polynomial.map_map, locator_map]
  apply Strata.locator_dvd_of_eval_zero _
    ((hf.comp (MvPolynomial.C_injective (Fin 4) K)).comp
      ProximityPrize.Benchmark.IRSProfile.domain.injective)
  intro i hi
  change (P.map f).eval (f (C (node i))) = 0
  rw [Polynomial.eval_map_apply, h i hi, map_zero]
private def planeLocator (S : Finset I) : MvPolynomial (Fin 5) K :=
  (finSuccEquiv K 4).symm ((locator node S).map C)
theorem graph_planeLocator (S : Finset I) : graph p (planeLocator S) =
    liftX (locator node S) := by
  rw [graph_eq_map, planeLocator, AlgEquiv.apply_symm_apply, Polynomial.map_map]
  congr 1
  ext a
  simp [coefficientGraph]
private theorem degreeOf_le_of_dvd {Q P : MvPolynomial (Fin 5) F} (hP : P ≠ 0)
    (h : Q ∣ P) (j : Fin 5) : Q.degreeOf j ≤ P.degreeOf j := by
  obtain ⟨E, hE⟩ := h
  have hQ : Q ≠ 0 := fun hz => hP (by rw [hE, hz, zero_mul])
  have hEn : E ≠ 0 := fun hz => hP (by rw [hE, hz, mul_zero])
  rw [hE, degreeOf_mul_eq hQ hEn]
  exact Nat.le_add_right _ _
private theorem omits_of_dvd {Q P : MvPolynomial (Fin 5) F} (hP : P ≠ 0)
    (ho : OmitsMessages P) (h : Q ∣ P) : OmitsMessages Q :=
  ⟨Nat.eq_zero_of_le_zero ((degreeOf_le_of_dvd hP h 1).trans ho.1.le),
    Nat.eq_zero_of_le_zero ((degreeOf_le_of_dvd hP h 2).trans ho.2.le)⟩
private theorem native_p_pos : 0 < p := by decide
private theorem divide_plane (S : Finset I) (P : MvPolynomial (Fin 5) K)
    (Q : Bivar) (content : Polynomial K) (hQ : Q ≠ 0) (hc : content ≠ 0)
    (hP : OmitsMessages P) (hS : P.degreeOf 3 < p)
    (h : graph p P = Polynomial.C content * (liftX (locator node S) * Q)) :
    ∃ E : MvPolynomial (Fin 5) K, P = planeLocator S * E ∧ E ≠ 0 ∧
      graph p E = Polynomial.C content * Q := by
  have hd := locator_dvd S (finSuccEquiv K 4 P) (fun i hi => by
    apply x_eval_zero_of_graph p native_p_pos P hP hS
    rw [h, Polynomial.eval_mul, Polynomial.eval_mul, K1_8.eval_liftX,
      locator_eval_zero node S i hi, Polynomial.C_0, zero_mul, mul_zero])
  obtain ⟨E', hE'⟩ := hd
  let E := (finSuccEquiv K 4).symm E'
  have he : P = planeLocator S * E := by
    apply (finSuccEquiv K 4).injective
    simpa [planeLocator, E, map_mul] using hE'
  have hm : liftX (locator node S) ≠ 0 :=
    ((locator_monic node S).map (Polynomial.C : K →+* Polynomial K)).ne_zero
  have hgE : graph p E = Polynomial.C content * Q := by
    apply mul_left_cancel₀ hm
    calc
      liftX (locator node S) * graph p E = graph p P := by
        rw [he, map_mul, graph_planeLocator]
      _ = liftX (locator node S) * (Polynomial.C content * Q) := h.trans (mul_left_comm _ _ _)
  have hen : E ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hgE
    exact (mul_ne_zero (Polynomial.C_ne_zero.mpr hc) hQ) hgE.symm
  exact ⟨E, he, hen, hgE⟩
private theorem seedRelPrime {U V : Bivar} (hUV : IsCoprime (extendSeed U) (extendSeed V))
    {content : Polynomial K} (hc : content ≠ 0) :
    IsRelPrime (extendSeed (Polynomial.C content * U))
      (extendSeed (Polynomial.C content * V)) := by
  have hu : IsUnit (Polynomial.C (K1_8.seedInclusion content)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff _ K1_8.seedInclusion_injective).mpr hc))
  have hmap (Q : Bivar) : extendSeed (Polynomial.C content * Q) =
      Polynomial.C (K1_8.seedInclusion content) * extendSeed Q := by
    change (Polynomial.C content * Q).map K1_8.seedInclusion = _ * Q.map K1_8.seedInclusion
    rw [Polynomial.map_mul, Polynomial.map_C]
  intro d hdU hdV
  rw [hmap, hu.dvd_mul_left] at hdU hdV
  exact hUV.isRelPrime hdU hdV
private theorem parameter_only {d : MvPolynomial (Fin 5) K}
    (ho : OmitsMessages d) (hx : d.degreeOf 0 = 0) :
    ∃ q : MvPolynomial (Fin 2) K, rename (![3, 4] : Fin 2 → Fin 5) q = d := by
  classical
  apply exists_rename_eq_of_vars_subset_range
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | contradiction
  · intro i hi
    have hi' := mem_vars_iff_degreeOf_ne_zero.mp hi
    fin_cases i
    · exact (hi' hx).elim
    · exact (hi' ho.1).elim
    · exact (hi' ho.2).elim
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
end
end K1_11_2_1
end
section
set_option autoImplicit false
namespace K1_11_3_2
open K1_11 K1_11_3 MvPolynomial
variable {F : Type} [Field F]
theorem derivative_specialize (H : MvPolynomial (Fin 4) F)
    (D : Polynomial F) (s t : F) :
    Polynomial.derivative (aeval (scalarImages D s t) H) =
      aeval (scalarImages D s t) (pderiv 0 H) +
        aeval (scalarImages D s t) (pderiv 1 H) * Polynomial.derivative D := by
  induction H using MvPolynomial.induction_on with
  | C a => simp [Polynomial.algebraMap_eq]
  | add P Q hP hQ =>
    simp only [map_add, hP, hQ]
    ring
  | mul_X P i hP =>
    simp only [map_mul, aeval_X, Polynomial.derivative_mul, pderiv_mul, map_add, hP]
    fin_cases i <;> simp [scalarImages] <;> ring
theorem first_derivative (G : MvPolynomial (Fin 4) F)
    (D : Polynomial F) (s t : F) (hroot : aeval (scalarImages D s t) G = 0) :
    -aeval (scalarImages D s t) (pderiv 0 G) =
      aeval (scalarImages D s t) (pderiv 1 G) * Polynomial.derivative D := by
  have h := derivative_specialize G D s t
  rw [hroot, Polynomial.derivative_zero] at h
  exact neg_eq_of_add_eq_zero_right h.symm
theorem specialize_implicitDeriv (G : MvPolynomial (Fin 4) F)
    (D : Polynomial F) (s t : F) (hroot : aeval (scalarImages D s t) G = 0)
    (H : MvPolynomial (Fin 4) F) :
    aeval (scalarImages D s t) (implicitDeriv G H) =
      aeval (scalarImages D s t) (pderiv 1 G) *
        Polynomial.derivative (aeval (scalarImages D s t) H) := by
  simp only [implicitDeriv, map_sub, map_mul]
  rw [derivative_specialize, sub_eq_add_neg, ← neg_mul, first_derivative G D s t hroot]
  ring
theorem cleared_step (A V : Polynomial F) (m : ℕ) :
    A * (A * Polynomial.derivative (A ^ (m + 1) * V)) -
      Polynomial.C (↑(m + 1) : F) * (A ^ (m + 1) * V) *
        (A * Polynomial.derivative A) =
      A ^ (m + 1 + 2) * Polynomial.derivative V := by
  rw [Polynomial.derivative_mul, Polynomial.derivative_pow_succ,
    pow_succ A (m + 1 + 1), pow_succ A (m + 1), pow_succ A m]
  simp only [Nat.cast_add, Nat.cast_one]
  ring
theorem specialize_implicitNumerator (G : MvPolynomial (Fin 4) F)
    (D : Polynomial F) (s t : F) (hroot : aeval (scalarImages D s t) G = 0) (n : ℕ) :
    aeval (scalarImages D s t) (implicitNumerator G n) =
      aeval (scalarImages D s t) (pderiv 1 G) ^ (2 * n + 1) *
        (Polynomial.derivative^[n + 1]) D := by
  induction n with
  | zero => simpa [implicitNumerator] using first_derivative G D s t hroot
  | succ n ih =>
    have hm : 2 * (n + 1) + 1 = 2 * n + 1 + 2 := by omega
    simp only [implicitNumerator, map_sub, map_mul, aeval_C, Polynomial.algebraMap_eq,
      specialize_implicitDeriv G D s t hroot, ih]
    rw [hm, Function.iterate_succ_apply' Polynomial.derivative (n + 1) D]
    exact cleared_step _ _ (2 * n)
theorem proof : K1_11_3.c2 := by
  intro F _ G w D s t hroot n hn hfactor
  cases n with
  | zero =>
    simp [paddedTaylorCoeff, aeval_X, scalarImages, mul_comm]
  | succ n =>
    have hfactorial : (Polynomial.derivative^[n + 1]) D =
        Polynomial.C (↑(n + 1).factorial : F) * Polynomial.hasseDeriv (n + 1) D := by
      rw [← Polynomial.factorial_smul_hasseDeriv]
      rw [LinearMap.smul_apply, nsmul_eq_mul, Polynomial.C_eq_natCast]
    have hpad : (2 * n + 1) + (2 * w - 1 - (2 * n + 1)) = 2 * w - 1 := by omega
    simp only [paddedTaylorCoeff, map_mul, map_pow, aeval_C, Polynomial.algebraMap_eq,
      specialize_implicitNumerator G D s t hroot, hfactorial]
    set A := aeval (scalarImages D s t) (pderiv 1 G)
    set f : F := ↑(n + 1).factorial
    set H := Polynomial.hasseDeriv (n + 1) D
    have hcancel : Polynomial.C f⁻¹ * Polynomial.C f = 1 := by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ hfactor, Polynomial.C_1]
    calc
      _ = (Polynomial.C f⁻¹ * Polynomial.C f) *
          (A ^ (2 * n + 1) * A ^ (2 * w - 1 - (2 * n + 1))) * H := by ring
      _ = _ := by rw [hcancel, one_mul, ← pow_add, hpad]
end K1_11_3_2
end
section
set_option autoImplicit false
namespace K1_11_3_1
open K1_11 K1_11_3 MvPolynomial
local notation "deg" => weightedTotalDegree scalarWeightTotal
section DegreeBounds
variable {F : Type} [Field F]
variable {P Q : MvPolynomial (Fin 4) F} {a b : ℕ}
private theorem degree_mul_le (hP : deg P ≤ a) (hQ : deg Q ≤ b) :
    deg (P * Q) ≤ a + b :=
  (weightedTotalDegree_mul_le scalarWeightTotal P Q).trans (Nat.add_le_add hP hQ)
private theorem degree_sub_le (hP : deg P ≤ a) (hQ : deg Q ≤ a) :
    deg (P - Q) ≤ a := by
  rw [← mem_restrictWeightedDegree_iff_weightedTotalDegree_le] at hP hQ ⊢
  exact (restrictWeightedDegree (R := F) scalarWeightTotal a).sub_mem hP hQ
theorem degree_const_mul_le (c : F) (P : MvPolynomial (Fin 4) F) :
    deg (C c * P) ≤ deg P := by
  simpa only [weightedTotalDegree_C, zero_add] using
    weightedTotalDegree_mul_le scalarWeightTotal (C c) P
theorem degree_pderiv_y_le (hP : deg P ≤ a) :
    deg (pderiv 1 P) ≤ a - 1 :=
  (weightedTotalDegree_pderiv_le_sub scalarWeightTotal 1 P).trans
    (Nat.sub_le_sub_right hP 1)
theorem implicitDeriv_degree {G H : MvPolynomial (Fin 4) F} {d m : ℕ}
    (hY : deg (pderiv 1 G) ≤ d) (hX : deg (pderiv 0 G) ≤ d + 1)
    (hH : deg H ≤ m) (hm : 1 ≤ m) :
    deg (implicitDeriv G H) ≤ m + d := by
  unfold implicitDeriv
  apply degree_sub_le
  · have hx := (weightedTotalDegree_pderiv_le scalarWeightTotal 0 H).trans hH
    exact (degree_mul_le hY hx).trans_eq (Nat.add_comm d m)
  · exact (degree_mul_le hX (degree_pderiv_y_le hH)).trans (by omega)
theorem implicitNumerator_degree {G : MvPolynomial (Fin 4) F} {d : ℕ}
    (hd : 1 ≤ d) (hY : deg (pderiv 1 G) ≤ d) (hX : deg (pderiv 0 G) ≤ d + 1)
    (n : ℕ) : deg (implicitNumerator G n) ≤ (2 * n + 1) * d + 1 := by
  have hFlow := implicitDeriv_degree hY hX hY hd
  induction n with
  | zero =>
    simpa only [implicitNumerator, weightedTotalDegree, support_neg, mul_zero, zero_add, one_mul]
      using hX
  | succ n ih =>
    rw [implicitNumerator]
    apply degree_sub_le
    · have hN := implicitDeriv_degree hY hX ih (by omega)
      exact (degree_mul_le hY hN).trans_eq (by ring)
    · have hN := (degree_const_mul_le (↑(2 * n + 1) : F) _).trans ih
      exact (degree_mul_le hN hFlow).trans_eq (by ring)
end DegreeBounds
theorem proof : K1_11_3.c1 := by
  intro F _ G w E hE hG n hn
  let d := E - 1
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hY : deg (pderiv 1 G) ≤ d := degree_pderiv_y_le hG
  have hX : deg (pderiv 0 G) ≤ d + 1 :=
    (weightedTotalDegree_pderiv_le scalarWeightTotal 0 G).trans (by dsimp [d]; omega)
  have hPow (k : ℕ) : deg (pderiv 1 G ^ k) ≤ k * d :=
    (weightedTotalDegree_pow_le scalarWeightTotal _ k).trans (Nat.mul_le_mul_left k hY)
  change deg (paddedTaylorCoeff G w n) ≤ (2 * w - 1) * d + 1
  cases n with
  | zero =>
    rw [paddedTaylorCoeff]
    have h₀ : deg (MvPolynomial.X 1 : MvPolynomial (Fin 4) F) ≤ 1 :=
      mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
        (X_mem_restrictWeightedDegree scalarWeightTotal 1 1 (by rfl))
    exact (degree_mul_le h₀ (hPow _)).trans_eq (Nat.add_comm _ _)
  | succ n =>
    rw [paddedTaylorCoeff]
    have hN := (degree_const_mul_le ((↑(Nat.factorial (n + 1)) : F)⁻¹) _).trans
      (implicitNumerator_degree hd hY hX n)
    apply (degree_mul_le hN (hPow _)).trans_eq
    have hpad : 2 * n + 1 ≤ 2 * w - 1 := by omega
    calc
      _ = ((2 * n + 1) + (2 * w - 1 - (2 * n + 1))) * d + 1 := by ring
      _ = _ := by rw [Nat.add_comm (2 * n + 1), Nat.sub_add_cancel hpad]
end K1_11_3_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_11_1_2
open Matrix MvPolynomial FrobeniusLocator K1_11_1
open scoped BigOperators
private theorem exists_pivot {E row col : Type} [Field E] [Fintype row] [Fintype col]
    (N : Matrix row col E) :
    ∃ (rows : Fin N.rank → row) (cols : Fin N.rank → col),
      (N.submatrix rows cols).det ≠ 0 := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' E N.col
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hc : Fintype.card κ = N.rank := by
    rw [← finrank_span_eq_card hli, hspan, Matrix.rank_eq_finrank_span_cols]
  let e := (Fintype.equivFinOfCardEq hc).symm
  let cols : Fin N.rank → col := a ∘ e
  have hcols : LinearIndependent E (fun j : Fin N.rank => N.col (cols j)) :=
    hli.comp e e.injective
  obtain ⟨rows, hpivot⟩ := GenericRank.exists_rows_det_ne_zero (N.submatrix id cols) (by
    intro v hv
    have hsum : (∑ j, v j • N.col (cols j)) = 0 := by
      funext i
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm,
        Matrix.col, Matrix.transpose_apply, Pi.zero_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply,
        id_eq] using congrFun hv i
    funext j
    exact Fintype.linearIndependent_iff.mp hcols v hsum j)
  exact ⟨rows, cols, hpivot⟩
private def unitColumns {R row col : Type} [Zero R] [One R] [DecidableEq row]
    (I : col → row) : Matrix row col R :=
  fun i j => (Pi.single (I j) 1 : row → R) i
private theorem transpose_mul_unitColumns {R row col pick : Type}
    [CommRing R] [Fintype row] [DecidableEq row]
    (W : Matrix row col R) (I : pick → row) :
    W.transpose * unitColumns I = (W.submatrix I id).transpose := by
  ext i j
  change W.transpose.mulVec (Pi.single (I j) 1) i = _
  rw [Matrix.mulVec_single_one]
  rfl
theorem augmentation_identity {R : Type} [CommRing R] {r s : ℕ}
    (C : Matrix (Fin r ⊕ Fin s) (Fin r) R)
    (W : Matrix (Fin r ⊕ Fin s) (Fin s) R)
    (hWC : W.transpose * C = 0)
    (pivot : Fin r → Fin r ⊕ Fin s) (I : Fin s → Fin r ⊕ Fin s) :
    (Matrix.fromRows (unitColumns pivot : Matrix _ _ R).transpose W.transpose).det *
        (Matrix.fromCols C (unitColumns I)).det =
      (C.submatrix pivot id).det * (W.submatrix I id).det := by
  have htop : (unitColumns pivot : Matrix _ _ R).transpose * C =
      C.submatrix pivot id := by
    have h := congrArg Matrix.transpose (transpose_mul_unitColumns C pivot)
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using h
  rw [← Matrix.det_mul, Matrix.fromRows_mul_fromCols, htop, hWC,
    transpose_mul_unitColumns W I, Matrix.det_fromBlocks_zero₂₁, Matrix.det_transpose]
theorem factor_of_primitive {R ι : Type} [CommRing R] [IsDomain R]
    [NormalizedGCDMonoid R] [Fintype ι] (P A : ι → R) (t d : R)
    (ht : t ≠ 0) (hprim : coefficientPrimitive P)
    (hdet : ∀ I, t * A I = d * P I) :
    ∃ q : R, ∀ I, A I = q * P I := by
  let g := Finset.univ.gcd P
  have hg : IsUnit g := hprim g (fun I => Finset.gcd_dvd (Finset.mem_univ I))
  have hd : t ∣ Finset.univ.gcd (fun I => d * P I) :=
    Finset.dvd_gcd (fun I _ => ⟨A I, (hdet I).symm⟩)
  have hgd : t ∣ d * g := hd.trans (Finset.gcd_mul_left' Finset.univ P d).dvd
  obtain ⟨q, hq⟩ : t ∣ d := hgd.trans (by
    simpa only [mul_one] using mul_dvd_mul (dvd_refl d) (isUnit_iff_dvd_one.mp hg))
  refine ⟨q, fun I => mul_left_cancel₀ ht ?_⟩
  rw [hdet I, hq, mul_assoc]
theorem augmented_degree {F : Type} [Field F] {r s : ℕ}
    (C : Matrix (Fin r ⊕ Fin s) (Fin r) (Seeds F))
    (block : Fin r ⊕ Fin s → Fin 2) (b i : Fin 2)
    (I : Fin s → Fin r ⊕ Fin s) (hI : ∀ j, block (I j) = b)
    (hC : ∀ u j, (C u j).degreeOf i ≤ if block u = i then 1 else 0)
    (L : ℕ) (htotal : (∑ u, if block u = i then 1 else 0) = L) :
    (Matrix.fromCols C (unitColumns I)).det.degreeOf i ≤ if b = i then L - s else L := by
  classical
  let A := Matrix.fromCols C (unitColumns I)
  let weight (u : Fin r ⊕ Fin s) : ℕ := if block u = i then 1 else 0
  let saving : Fin r ⊕ Fin s → ℕ := Sum.elim (fun _ => 0) (fun _ => if b = i then 1 else 0)
  change A.det.degreeOf i ≤ _
  rw [Matrix.det_apply']
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro σ _
  by_cases hz : (∏ j, A (σ j) j) = 0
  · simp [hz]
  have hsign : ((↑↑(Equiv.Perm.sign σ) : Seeds F)).degreeOf i = 0 := by
    rw [← map_intCast (MvPolynomial.C : F →+* Seeds F), degreeOf_C]
  have hpoint (j : Fin r ⊕ Fin s) :
      (A (σ j) j).degreeOf i + saving j ≤ weight (σ j) := by
    cases j with
    | inl j => simpa only [A, Matrix.fromCols_apply_inl, saving, Sum.elim_inl, add_zero]
        using hC (σ (Sum.inl j)) j
    | inr j =>
      have he : I j = σ (Sum.inr j) := by
        by_contra h
        apply hz
        apply Finset.prod_eq_zero (Finset.mem_univ (Sum.inr j))
        simp [A, unitColumns, h]
      simp [A, unitColumns, ← he, weight, hI, saving]
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpoint j)
  have hsave : (∑ j, saving j) = if b = i then s else 0 := by
    by_cases h : b = i <;> simp [saving, Fintype.sum_sum_type, h]
  rw [Finset.sum_add_distrib, hsave, Equiv.sum_comp σ weight, htotal] at hsum
  apply (degreeOf_mul_le _ _ _).trans
  rw [hsign, zero_add]
  apply (degreeOf_prod_le _ _ _).trans
  by_cases h : b = i
  · simp only [ite_eq_left h] at hsum ⊢
    omega
  · simpa only [ite_eq_right h, Nat.add_zero] using hsum
theorem proof : K1_11_1.c2 := by
  intro F _ L w s M W _ _ hrank hWM hdegree hprim b i rows
  classical
  by_cases hzero : K1_6.maximalMinors W (fun j => (b, rows j)) = 0
  · simp [hzero]
  let φ := algebraMap (Seeds F) (PlaneField F)
  let r := (M.map φ).rank
  obtain ⟨pivot, cols, hpivot⟩ := exists_pivot (M.map φ)
  let e : (Fin r ⊕ Fin s) ≃ Fin 2 × Fin L :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
      using hrank)
  let C := M.submatrix e cols
  let V := W.submatrix e id
  let p : Fin r → Fin r ⊕ Fin s := e.symm ∘ pivot
  let I : Fin s → Fin r ⊕ Fin s := fun j => e.symm (b, rows j)
  have hpmap : (C.submatrix p id).map φ = (M.map φ).submatrix pivot cols := by
    ext u j
    simp only [C, p, Matrix.map_apply, Matrix.submatrix_apply, Function.comp_apply,
      Equiv.apply_symm_apply, id_eq]
  have hp : (C.submatrix p id).det ≠ 0 := by
    intro h
    apply hpivot
    rw [← hpmap, ← RingHom.mapMatrix_apply, ← φ.map_det, h, map_zero]
  have hVC : V.transpose * C = 0 := by
    apply Matrix.ext
    intro u j
    change (∑ t : Fin r ⊕ Fin s, W (e t) u * M (e t) (cols j)) = 0
    rw [Equiv.sum_comp e (fun t => W t u * M t (cols j))]
    exact congrFun (congrFun hWM u) (cols j)
  let P (J : Fin s → Fin r ⊕ Fin s) := (V.submatrix J id).det
  let A (J : Fin s → Fin r ⊕ Fin s) := (Matrix.fromCols C (unitColumns J)).det
  let t := (Matrix.fromRows (unitColumns p : Matrix _ _ (Seeds F)).transpose V.transpose).det
  have hminor (J : Fin s → Fin 2 × Fin L) :
      P (e.symm ∘ J) = K1_6.maximalMinors W J := by
    change K1_6.maximalMinors W (e ∘ (e.symm ∘ J)) = _
    congr 1
    funext j
    exact e.apply_symm_apply (J j)
  have hP : P I ≠ 0 := by
    change P (e.symm ∘ (fun j => (b, rows j))) ≠ 0
    rwa [hminor]
  have hdet (J : Fin s → Fin r ⊕ Fin s) : t * A J = (C.submatrix p id).det * P J :=
    augmentation_identity C V hVC p J
  have ht : t ≠ 0 := by
    intro hz
    have he := hdet I
    rw [hz, zero_mul] at he
    exact mul_ne_zero hp hP he.symm
  have hprimP : coefficientPrimitive P := by
    intro q hq
    apply hprim q
    intro J
    rw [← hminor J]
    exact hq _
  let := UniqueFactorizationMonoid.strongNormalizationMonoid (α := Seeds F)
  let := UniqueFactorizationMonoid.toNormalizedGCDMonoid (Seeds F)
  obtain ⟨q, hq⟩ := factor_of_primitive P A t _ ht hprimP hdet
  have hq0 : q ≠ 0 := by
    intro hz
    have he := hdet I
    rw [hq I, hz, zero_mul, mul_zero] at he
    exact mul_ne_zero hp hP he.symm
  let block (u : Fin r ⊕ Fin s) := (e u).1
  have hblock (j : Fin s) : block (I j) = b := by
    simp only [block, I, Equiv.apply_symm_apply]
  have htotal : (∑ u, if block u = i then 1 else 0) = L := by
    dsimp only [block]
    rw [Equiv.sum_comp e (fun u : Fin 2 × Fin L => if u.1 = i then (1 : ℕ) else 0)]
    rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    fin_cases i <;> simp
  have hbound := augmented_degree C block b i I hblock (fun u j => hdegree (e u) (cols j) i)
    L htotal
  change (A I).degreeOf i ≤ _ at hbound
  rw [hq I, degreeOf_mul_eq hq0 hP] at hbound
  rw [← hminor (fun j => (b, rows j))]
  exact (Nat.le_add_left (degreeOf i (P I)) (degreeOf i q)).trans hbound
end K1_11_1_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_11_1_1
noncomputable section
open Polynomial Matrix FrobeniusLocator K1_6 K1_11_1
private theorem exists_shift_minor {A R : Type} [CommRing A] [CommRing R] [IsDomain R]
    (P : Fin 2 → A[X]) (h s : ℕ) (hdegree : ∀ b, (P b).natDegree ≤ h)
    (f : A → R) (hf : f 0 = 0) (b : Fin 2) (j : Fin (h + 1))
    (hj : f ((P b).coeff j.val) ≠ 0) :
    ∃ rows : Fin s → Fin (h + s),
      (((shifts P (h + s) s).submatrix (fun k => (b, rows k)) id).map f).det ≠ 0 := by
  classical
  let S := (Finset.range (h + 1)).filter (fun d => f ((P b).coeff d) ≠ 0)
  have hS : S.Nonempty := ⟨j.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt, hj⟩⟩
  let d := S.max' hS
  have hd : d ∈ S := S.max'_mem hS
  have hdle : d ≤ h := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hd).1)
  have hdne : f ((P b).coeff d) ≠ 0 := (Finset.mem_filter.mp hd).2
  have hlarge (k : ℕ) (hk : d < k) : f ((P b).coeff k) = 0 := by
    by_cases hkh : k < h + 1
    · by_contra hne
      exact (not_le_of_gt hk) (S.le_max' k (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkh, hne⟩))
    · have hk' : (P b).natDegree < k := (hdegree b).trans_lt (by omega)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk', hf]
  let rows (k : Fin s) : Fin (h + s) := ⟨d + k.val, by omega⟩
  let M := ((shifts P (h + s) s).submatrix (fun k => (b, rows k)) id).map f
  have htri : M.IsUpperTriangular := by
    intro k l hkl
    change l.val < k.val at hkl
    change f ((P b * Polynomial.X ^ l.val).coeff (d + k.val)) = 0
    rw [Polynomial.coeff_mul_X_pow', ite_eq_left (by omega)]
    exact hlarge _ (by omega)
  have hdiag (k : Fin s) : M k k = f ((P b).coeff d) := by
    change f ((P b * Polynomial.X ^ k.val).coeff (d + k.val)) = _
    rw [Polynomial.coeff_mul_X_pow]
  refine ⟨rows, ?_⟩
  change M.det ≠ 0
  rw [Matrix.det_of_isUpperTriangular htri]
  simp only [hdiag, Fin.prod_const]
  exact pow_ne_zero _ hdne
theorem planePair_degree {F : Type} [Field F] {h : ℕ}
    (Q : Fin 2 × Fin (h + 1) → Seeds F) (b : Fin 2) : (planePair Q b).natDegree ≤ h :=
  Principal.assemble_natDegree_le _
theorem planePair_coeff {F : Type} [Field F] {h : ℕ}
    (Q : Fin 2 × Fin (h + 1) → Seeds F) (b : Fin 2) (j : Fin (h + 1)) :
    (planePair Q b).coeff j.val = Q (b, j) :=
  Principal.assemble_coeff _ _
private theorem primitive_shift_minors {F : Type} [Field F] (h s : ℕ)
    (Q : Fin 2 × Fin (h + 1) → Seeds F) (hQ : Q ≠ 0) (hprim : coefficientPrimitive Q) :
    coefficientPrimitive (maximalMinors (shifts (planePair Q) (h + s) s)) := by
  classical
  intro q hq
  have hqne : q ≠ 0 := by
    intro hz
    obtain ⟨⟨b, j⟩, hj⟩ := Function.ne_iff.mp hQ
    have hj' : id ((planePair Q b).coeff j.val) ≠ 0 := by
      simpa only [id_eq, planePair_coeff, Pi.zero_apply] using hj
    obtain ⟨rows, hr⟩ := exists_shift_minor (planePair Q) h s (planePair_degree Q)
      id rfl b j hj'
    have he := hq (fun k => (b, rows k))
    rw [hz, zero_dvd_iff] at he
    apply hr
    change (((shifts (planePair Q) (h + s) s).submatrix (fun k => (b, rows k)) id).map id).det = 0
    rw [Matrix.map_id]
    exact he
  by_contra hqnu
  obtain ⟨p, hp, hpq⟩ := WfDvdMonoid.exists_irreducible_factor hqnu hqne
  let I : Ideal (Seeds F) := Ideal.span {p}
  let : I.IsPrime :=
    (Ideal.span_singleton_prime hp.ne_zero).mpr (UniqueFactorizationMonoid.irreducible_iff_prime.mp hp)
  let φ := Ideal.Quotient.mk I
  have hsurvives : ∃ k, φ (Q k) ≠ 0 := by
    by_contra! hall
    exact hp.not_isUnit (hprim p (fun k =>
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp (hall k))))
  obtain ⟨⟨b, j⟩, hj⟩ := hsurvives
  obtain ⟨rows, hr⟩ := exists_shift_minor (planePair Q) h s (planePair_degree Q)
    φ (map_zero φ) b j (by rwa [planePair_coeff])
  let M := (shifts (planePair Q) (h + s) s).submatrix (fun k => (b, rows k)) id
  have hz : φ M.det = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton.mpr (hpq.trans (hq (fun k => (b, rows k)))))
  rw [φ.map_det, RingHom.mapMatrix_apply] at hz
  exact hr hz
private theorem coeff_det_uniform {R : Type} [CommRing R] {s : ℕ}
    (M : Matrix (Fin s) (Fin s) R[X]) (H : ℕ) (hdegree : ∀ k l, (M k l).natDegree ≤ H) :
    M.det.coeff (s * H) = (M.map (fun q => q.coeff H)).det := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Polynomial.coeff_smul]
  congr 1
  simpa only [Finset.card_univ, Fintype.card_fin, Matrix.map_apply] using
    Polynomial.coeff_prod_of_natDegree_le (Finset.univ : Finset (Fin s))
      (fun k => M (σ k) k) H (fun k _ => hdegree (σ k) k)
theorem natDegree_det_uniform {R : Type} [CommRing R] {s : ℕ}
    (M : Matrix (Fin s) (Fin s) R[X]) (H : ℕ) (hdegree : ∀ k l, (M k l).natDegree ≤ H) :
    M.det.natDegree ≤ s * H := by
  classical
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  have hprod : (∏ k, M (σ k) k).natDegree ≤ s * H := by
    calc
      _ ≤ ∑ k, (M (σ k) k).natDegree := Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _ : Fin s, H := Finset.sum_le_sum (fun k _ => hdegree (σ k) k)
      _ = _ := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign
  · simpa only [hsign, one_smul] using hprod
  · simpa only [hsign, Units.neg_smul, one_smul, Polynomial.natDegree_neg] using hprod
set_option maxHeartbeats 600000 in
theorem shift_minor_degree {F : Type} [Field F] (h s : ℕ)
    (Q : Fin 2 × Fin (h + 1) → Seeds F) (b i : Fin 2) (hpos : 0 < blockDegree Q b i) :
    ∃ rows : Fin s → Fin (h + s),
      (maximalMinors (shifts (planePair Q) (h + s) s) (fun k => (b, rows k))).degreeOf i =
        s * blockDegree Q b i := by
  classical
  let R := MvPolynomial {j : Fin 2 // j ≠ i} F
  let φ : Seeds F →+* R[X] :=
    ((MvPolynomial.renameEquiv F (Equiv.optionSubtypeNe i).symm).trans
      (MvPolynomial.optionEquivLeft F {j : Fin 2 // j ≠ i})).toRingHom
  have hφ (q : Seeds F) : (φ q).natDegree = q.degreeOf i :=
    (MvPolynomial.degreeOf_eq_natDegree i q).symm
  let H := blockDegree Q b i
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin (h + 1)))
    Finset.univ_nonempty (fun k => (Q (b, k)).degreeOf i)
  have hj' : (φ (Q (b, j))).natDegree = H := (hφ _).trans hj.symm
  have htop : (φ ((planePair Q b).coeff j.val)).coeff H ≠ 0 := by
    rw [planePair_coeff, ← hj', Polynomial.coeff_natDegree]
    apply Polynomial.leadingCoeff_ne_zero.mpr
    intro hz
    rw [hz, Polynomial.natDegree_zero] at hj'
    exact (Nat.ne_of_gt hpos) hj'.symm
  obtain ⟨rows, hr⟩ := exists_shift_minor (planePair Q) h s (planePair_degree Q)
    (fun q => (φ q).coeff H) (by rw [map_zero, Polynomial.coeff_zero]) b j htop
  let A := (shifts (planePair Q) (h + s) s).submatrix (fun k => (b, rows k)) id
  let M := A.map φ
  have hcoeff (k : ℕ) : (φ ((planePair Q b).coeff k)).natDegree ≤ H := by
    by_cases hk : k < h + 1
    · let j' : Fin (h + 1) := ⟨k, hk⟩
      change (φ ((planePair Q b).coeff j'.val)).natDegree ≤ H
      rw [planePair_coeff, hφ]
      exact degreeOf_coordinate Q b i j'
    · have hk' : (planePair Q b).natDegree < k := (planePair_degree Q b).trans_lt (by omega)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk', map_zero, Polynomial.natDegree_zero]
      exact Nat.zero_le H
  have hM (k l : Fin s) : (M k l).natDegree ≤ H := by
    simp only [M, A, Matrix.map_apply, Matrix.submatrix_apply, K1_6.shifts, id_eq]
    rw [Polynomial.coeff_mul_X_pow']
    split_ifs
    · exact hcoeff _
    · rw [map_zero, Polynomial.natDegree_zero]
      exact Nat.zero_le H
  have htopDet : M.det.coeff (s * H) ≠ 0 := by
    rw [coeff_det_uniform M H hM]
    exact hr
  refine ⟨rows, ?_⟩
  change A.det.degreeOf i = s * H
  have hdet : φ A.det = M.det := φ.map_det A
  rw [← hφ, hdet]
  exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (natDegree_det_uniform M H hM) htopDet
theorem proof : K1_11_1.c1 := by
  intro F inst h L s Q hL _ hQ hprim
  subst L
  exact ⟨primitive_shift_minors h s Q hQ hprim, shift_minor_degree h s Q⟩
end
end K1_11_1_1
end
section
set_option autoImplicit false
namespace K1_13_6_3_4_2
noncomputable section
open K1_13_6_3 K1_13_6_3_4 MvPolynomial Filter
variable {k σ : Type*} [Field k]
private theorem homogeneous_representative (I : Ideal (MvPolynomial σ k)) (i : σ)
    (N : ℕ) {p : MvPolynomial σ k} (hp : p.totalDegree ≤ N) :
    ∃ q : MvPolynomial σ k, q.IsHomogeneous N ∧
      Ideal.Quotient.mk (boundaryChart I i) q = Ideal.Quotient.mk (boundaryChart I i) p := by
  classical
  let J := boundaryChart I i
  have hi : Ideal.Quotient.mk J (MvPolynomial.X i) = 1 := by
    apply sub_eq_zero.mp
    rw [← (Ideal.Quotient.mk J).map_one, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact (le_sup_right : Ideal.span {MvPolynomial.X i - 1} ≤ J)
      (Ideal.subset_span (Set.mem_singleton _))
  refine ⟨∑ d ∈ Finset.range (p.totalDegree + 1),
    MvPolynomial.X i ^ (N - d) * homogeneousComponent d p, IsHomogeneous.sum _ _ _ ?_, ?_⟩
  · intro d hd
    have hdN : d ≤ N := (Nat.le_of_lt_succ (Finset.mem_range.mp hd)).trans hp
    have hform := (isHomogeneous_X_pow (R := k) i (N - d)).mul
      (homogeneousComponent_isHomogeneous d p)
    simpa only [Nat.sub_add_cancel hdN] using hform
  · change Ideal.Quotient.mk J _ = Ideal.Quotient.mk J p
    rw [map_sum]
    simp only [map_mul, map_pow, hi, one_pow, one_mul]
    rw [← map_sum, sum_homogeneousComponent]
theorem chart_hilbert_step [Finite σ] (I : Ideal (MvPolynomial σ k)) (i : σ)
    (N : ℕ) (hN : 0 < N) :
    affineHilbertFunction (boundaryChart I i) N + affineHilbertFunction I (N - 1) ≤
      affineHilbertFunction I N := by
  let J := boundaryChart I i
  let V := restrictTotalDegree σ k N
  let proj : V →ₗ[k] quotientDegreeLE I N :=
    ((Ideal.Quotient.mkₐ k I).toLinearMap.domRestrict V).codRestrict _ fun p ↦
      mk_mem_quotientDegreeLE ((mem_restrictTotalDegree σ N p.val).mp p.property)
  have hproj : Function.Surjective proj := by
    intro z
    obtain ⟨p, hp, hz⟩ := mem_quotientDegreeLE.mp z.property
    exact ⟨⟨p, (mem_restrictTotalDegree σ N p).mpr hp⟩, Subtype.ext hz⟩
  let top : V →ₗ[k] quotientDegreeLE J N :=
    (((Ideal.Quotient.mkₐ k J).toLinearMap.comp (homogeneousComponent N)).domRestrict V).codRestrict _
      fun p ↦ mk_mem_quotientDegreeLE (homogeneousComponent_isHomogeneous N p.val).totalDegree_le
  have hker : LinearMap.ker proj ≤ LinearMap.ker top := by
    intro p hp
    rw [LinearMap.mem_ker] at hp ⊢
    have hpI : p.val ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val hp)
    apply Subtype.ext
    change Ideal.Quotient.mk J (homogeneousComponent N p.val) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (le_sup_left : boundaryIdeal I ≤ J) (Ideal.subset_span
      ⟨p.val, N, hpI, (mem_restrictTotalDegree σ N p.val).mp p.property, rfl⟩)
  let cut : quotientDegreeLE I N →ₗ[k] quotientDegreeLE J N :=
    ((LinearMap.ker proj).liftQ top hker).comp
      (proj.quotKerEquivOfSurjective hproj).symm.toLinearMap
  have hcut (p : V) : cut (proj p) = top p := by
    change (LinearMap.ker proj).liftQ top hker
      ((proj.quotKerEquivOfSurjective hproj).symm (proj p)) = _
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  have hsurj : Function.Surjective cut := by
    intro z
    obtain ⟨p, hp, hz⟩ := mem_quotientDegreeLE.mp z.property
    obtain ⟨q, hform, hq⟩ := homogeneous_representative I i N hp
    let v : V := ⟨q, (mem_restrictTotalDegree σ N q).mpr hform.totalDegree_le⟩
    refine ⟨proj v, ?_⟩
    rw [hcut]
    apply Subtype.ext
    change Ideal.Quotient.mk J (homogeneousComponent N q) = z.val
    rw [homogeneousComponent_eq_self hform]
    exact hq.trans hz
  let incl := Submodule.inclusion (quotientDegreeLE_mono I (Nat.sub_le N 1))
  have hincl (z : quotientDegreeLE I (N - 1)) : incl z ∈ LinearMap.ker cut := by
    obtain ⟨p, hp, hz⟩ := mem_quotientDegreeLE.mp z.property
    have hlt : p.totalDegree < N := lt_of_le_of_lt hp (by omega)
    let v : V := ⟨p, (mem_restrictTotalDegree σ N p).mpr hlt.le⟩
    have he : incl z = proj v := Subtype.ext hz.symm
    rw [he, LinearMap.mem_ker, hcut]
    apply Subtype.ext
    change Ideal.Quotient.mk J (homogeneousComponent N p) = 0
    rw [homogeneousComponent_eq_zero N p hlt, map_zero]
  have hinj : Function.Injective (incl.codRestrict (LinearMap.ker cut) hincl) := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z ↦ z.val.val) hxy)
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hdim := cut.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hdim
  change affineHilbertFunction J N + affineHilbertFunction I (N - 1) ≤ _
  unfold affineHilbertFunction
  omega
private theorem chart_dimension [Finite σ] (I : Ideal (MvPolynomial σ k)) (i : σ)
    (hI : dimension I = 1) : dimension (boundaryChart I i) = 0 := by
  let J := boundaryChart I i
  obtain ⟨M, hM⟩ := exists_eval_affineHilbertPolynomial I
  have hbound : ∀ᶠ N : ℕ in atTop,
      (affineHilbertPolynomial J).eval (N : ℚ) ≤
        (Polynomial.backwardDifference 1 (affineHilbertPolynomial I)).eval (N : ℚ) := by
    filter_upwards [eventually_eval_affineHilbertPolynomial J, eventually_ge_atTop (M + 1)]
      with N hJ hN
    have hpos : 0 < N := by omega
    have hprev : M ≤ N - 1 := by omega
    have hcast : ((N - 1 : ℕ) : ℚ) = (N : ℚ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ N by omega), Nat.cast_one]
    rw [Polynomial.eval_backwardDifference, ← hcast, hM N (by omega), hM (N - 1) hprev, hJ]
    apply le_sub_iff_add_le.mpr
    exact_mod_cast chart_hilbert_step I i N hpos
  have h := (Polynomial.natDegree_le_and_coeff_le_of_eventually_eval_natCast_le_backwardDifference
    (eventually_eval_affineHilbertPolynomial_nonneg J) hbound).1
  change dimension J ≤ dimension I - 1 at h
  rw [hI] at h
  exact Nat.eq_zero_of_le_zero h
theorem proof : K1_13_6_3_4.c2 := by
  intro A _ hA i
  exact chart_dimension A i hA
end
end K1_13_6_3_4_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_5_2_1_1
noncomputable section
open K1_13_5_4_2 K1_13_5_4_2_5_2_1
open scoped BigOperators
def faceHull {α : Type} (v : α → ExponentSpace) (S : Finset α) : Set ExponentSpace :=
  convexHull ℝ (v '' (S : Set α))
theorem center_mem_faceHull {α : Type} (v : α → ExponentSpace) {S : Finset α}
    (hS : S.Nonempty) : faceCenter v S ∈ faceHull v S := by
  have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  unfold faceCenter faceHull
  rw [Finset.smul_sum]
  apply (convex_convexHull ℝ _).sum_mem (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  · simp [nsmul_eq_mul, hcard]
  · intro a ha
    exact subset_convexHull ℝ _ (Set.mem_image_of_mem v ha)
theorem direction_le_ker {α : Type} {v : α → ExponentSpace} {S : Finset α}
    {g : ExponentSpace →ₗ[ℝ] ℝ} {a : α} (ha : a ∈ S)
    (hc : ∀ b ∈ S, g (v b) = g (v a)) :
    vectorSpan ℝ (v '' (S : Set α)) ≤ LinearMap.ker g := by
  rw [vectorSpan_eq_span_vsub_set_right ℝ (Set.mem_image_of_mem v ha), Submodule.span_le]
  rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
  simp [vsub_eq_sub, map_sub, hc b hb]
theorem exposed_lt {α : Type} {v : α → ExponentSpace} {S : Finset α}
    {g : ExponentSpace →ₗ[ℝ] ℝ} (hg : Exposes v S g) {a b : α}
    (ha : a ∈ S) (hb : b ∉ S) : g (v b) < g (v a) := by
  refine lt_of_le_of_ne ((hg a).1 ha b) (fun he => hb ((hg b).2 (fun c => ?_)))
  rw [he]
  exact (hg a).1 ha c
theorem face_span_lt {α : Type} {v : α → ExponentSpace} {S T : Finset α}
    (hT : IsFaceLabels v T) (hTS : T < S) :
    vectorSpan ℝ (v '' (T : Set α)) < vectorSpan ℝ (v '' (S : Set α)) := by
  obtain ⟨⟨a, ha⟩, g, hg⟩ := hT
  obtain ⟨b, hb, hbT⟩ := Finset.not_subset.mp (not_le_of_gt hTS)
  have hker := direction_le_ker ha (g := g)
    (fun c hc => le_antisymm ((hg a).1 ha c) ((hg c).1 hc a))
  have hle := vectorSpan_mono ℝ (Set.image_mono (f := v) (show (T : Set α) ⊆ S from hTS.le))
  refine lt_of_le_not_ge hle (fun h => ?_)
  have hmem : v b - v a ∈ vectorSpan ℝ (v '' (S : Set α)) :=
    vsub_mem_vectorSpan ℝ (Set.mem_image_of_mem v hb) (Set.mem_image_of_mem v (hTS.le ha))
  have heq := LinearMap.mem_ker.mp (hker (h hmem))
  rw [map_sub] at heq
  exact (exposed_lt hg ha hbT).ne (sub_eq_zero.mp heq)
theorem exists_boundary_on_ray {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Set E} (hH : IsCompact H) {c x : E} (hx : x ∈ H) (hne : x ≠ c) :
    ∃ y ∈ H, y ∉ interior H ∧ Wbtw ℝ c x y := by
  obtain ⟨R, hR⟩ := (hH.image (continuous_id.sub continuous_const : Continuous (fun z : E => z - c))).isBounded.exists_norm_le
  have hn : 0 < ‖x - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  let t := max 1 (R / ‖x - c‖ + 1)
  have ht : 1 ≤ t := le_max_left _ _
  let p := t • (x - c) + c
  have hp : p ∉ H := by
    intro hpH
    have hnorm := hR (p - c) (Set.mem_image_of_mem (fun z => z - c) hpH)
    have hlt : R / ‖x - c‖ < t :=
      lt_of_lt_of_le (lt_add_of_pos_right _ zero_lt_one) (le_max_right _ _)
    have hmul := (div_lt_iff₀ hn).mp hlt
    exact (not_le_of_gt hmul) (by
      simpa [p, norm_smul, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans ht)] using hnorm)
  have hcx : Wbtw ℝ c x p := by
    simpa [p, vadd_eq_add] using
      (wbtw_smul_vadd_smul_vadd_of_nonneg_of_le c (x - c) zero_le_one ht)
  obtain ⟨y, hy, hpyx, hv⟩ := hH.isClosed.exists_wbtw_isVisible hx p
  refine ⟨y, hy, fun hyi => hp ((hv.eq_of_mem_interior hyi).symm ▸ hy), ?_⟩
  exact hcx.trans_right_left hpyx.symm
theorem relative_support {α : Type} {v : α → ExponentSpace} {S : Finset α}
    (hS : S.Nonempty) {x : ExponentSpace} (hx : x ∈ faceHull v S) (hne : x ≠ faceCenter v S) :
    ∃ (y : ExponentSpace) (g : ExponentSpace →ₗ[ℝ] ℝ),
      y ∈ faceHull v S ∧ Wbtw ℝ (faceCenter v S) x y ∧
      (∀ a ∈ S, g (v a) ≤ g y) ∧ ∃ a ∈ S, g (v a) < g y := by
  let H := faceHull v S
  let A := affineSpan ℝ H
  let xA : A := ⟨x, subset_affineSpan ℝ H hx⟩
  let : Nonempty A := ⟨xA⟩
  let e : A.direction ≃ᵃ[ℝ] A := AffineEquiv.vaddConst ℝ xA
  let u : A.direction →ᵃ[ℝ] ExponentSpace := A.subtype.comp e.toAffineMap
  let C := u ⁻¹' H
  have hu (z : A.direction) : u z = (z : ExponentSpace) + x := rfl
  have hcv : Convex ℝ C := (convex_convexHull ℝ _).affine_preimage u
  have hspan : affineSpan ℝ C = ⊤ := by
    let : Nonempty H := ⟨⟨x, hx⟩⟩
    change affineSpan ℝ (e ⁻¹' (((↑) : A → ExponentSpace) ⁻¹' H)) = ⊤
    rw [← AffineSubspace.comap_span, affineSpan_coe_preimage_eq_top, AffineSubspace.comap_top]
  have hcompactH : IsCompact H := (S.finite_toSet.image v).isCompact_convexHull ℝ
  have hclosed : IsClosed C := hcompactH.isClosed.preimage u.continuous_of_finiteDimensional
  have hbounded : Bornology.IsBounded C := by
    obtain ⟨R, hR⟩ := (hcompactH.image
      (continuous_id.sub continuous_const : Continuous (fun z : ExponentSpace => z - x))).isBounded.exists_norm_le
    apply (isBounded_iff_forall_norm_le).2
    refine ⟨R, fun z hz => ?_⟩
    have hz' := hR (u z - x)
      (Set.mem_image_of_mem (fun p => p - x) (show u z ∈ H from hz))
    simpa only [hu, add_sub_cancel_right, Submodule.norm_coe] using hz'
  have hcompact : IsCompact C := Metric.isCompact_of_isClosed_isBounded hclosed hbounded
  have hc := center_mem_faceHull v hS
  let cA : A := ⟨faceCenter v S, subset_affineSpan ℝ H hc⟩
  have hxc : e.symm xA ∈ C := by change (e (e.symm xA) : ExponentSpace) ∈ H; simpa using hx
  have hcc : e.symm cA ∈ C := by change (e (e.symm cA) : ExponentSpace) ∈ H; simpa using hc
  have hne' : e.symm xA ≠ e.symm cA := by
    intro he
    exact hne (congrArg Subtype.val (e.symm.injective he))
  obtain ⟨z, hz, hzi, hbtw⟩ := exists_boundary_on_ray hcompact (c := e.symm cA) hxc hne'
  obtain ⟨f, hf, hmax⟩ := geometric_hahn_banach_of_nonempty_interior_point hcv hzi
    (hcv.interior_nonempty_iff_affineSpan_eq_top.mpr hspan)
  obtain ⟨g, hg⟩ := f.toLinearMap.exists_extend
  have hg' (z' : A.direction) : g (u z') = f z' + g x := by
    rw [hu, map_add]
    exact congrArg (· + g x) (LinearMap.congr_fun hg z')
  have hmap (p : A) : u (e.symm p) = (p : ExponentSpace) := by
    change (e (e.symm p) : ExponentSpace) = _
    rw [e.apply_symm_apply]
  let y := u z
  have haH (a : α) (ha : a ∈ S) : v a ∈ H :=
    subset_convexHull ℝ _ (Set.mem_image_of_mem v ha)
  have hle (a : α) (ha : a ∈ S) : g (v a) ≤ g y := by
    let aA : A := ⟨v a, subset_affineSpan ℝ H (haH a ha)⟩
    have haC : e.symm aA ∈ C := by
      change u (e.symm aA) ∈ H
      rw [hmap]
      exact haH a ha
    have he := add_le_add (hmax _ haC) (le_refl (g x))
    rw [← hg' (e.symm aA), ← hg' z, hmap] at he
    exact he
  refine ⟨y, g, hz, by simpa only [hmap] using hbtw.map u, hle, ?_⟩
  by_contra! hn
  obtain ⟨a, ha⟩ := hS
  have hker := direction_le_ker ha (g := g) (fun b hb =>
    (le_antisymm (hle b hb) (hn b hb)).trans (le_antisymm (hle a ha) (hn a ha)).symm)
  apply hf
  ext q
  have hq : (q : ExponentSpace) ∈ vectorSpan ℝ (v '' (S : Set α)) := by
    have hm : (q : ExponentSpace) ∈ (affineSpan ℝ (convexHull ℝ (v '' (S : Set α)))).direction :=
      q.property
    simpa only [affineSpan_convexHull, direction_affineSpan] using hm
  have hqg := LinearMap.mem_ker.mp (hker hq)
  simpa using (LinearMap.congr_fun hg q).symm.trans hqg
theorem mem_maximizing_hull {α : Type} {v : α → ExponentSpace} {S : Finset α}
    {y : ExponentSpace} (hy : y ∈ faceHull v S) {g : ExponentSpace →ₗ[ℝ] ℝ}
    (hle : ∀ a ∈ S, g (v a) ≤ g y) [DecidablePred (fun a => g (v a) = g y)] :
    y ∈ faceHull v (S.filter (fun a => g (v a) = g y)) := by
  classical
  obtain ⟨ι, _, w, p, hw, hsum, hp, hcomb⟩ := mem_convexHull_iff_exists_fintype.mp hy
  have hle' (i : ι) : g (p i) ≤ g y := by
    obtain ⟨a, ha, he⟩ := hp i
    rw [← he]
    exact hle a ha
  have he0 : ∑ i, w i * (g y - g (p i)) = 0 := by
    have he := congrArg g hcomb
    simp only [map_sum, map_smul, smul_eq_mul] at he
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, he, hsum, one_mul, sub_self]
  let I := Finset.univ.filter (fun i => w i ≠ 0)
  have hcomb' : (∑ i ∈ I, w i • p i) = y := by
    rw [← hcomb]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hwi : w i = 0 := by simpa [I] using hi
    simp [hwi]
  refine (congrArg (fun q => q ∈ faceHull v (S.filter (fun a => g (v a) = g y))) hcomb').mp ?_
  refine (convex_convexHull ℝ _).sum_mem (fun i _ => hw i) ?_ ?_
  · dsimp only [I]
    rw [Finset.sum_filter_ne_zero]
    exact hsum
  · intro i hi
    have hwi := (Finset.mem_filter.mp hi).2
    have his := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hw j) (sub_nonneg.mpr (hle' j)))).mp he0 i (Finset.mem_univ _)
    have heq := (sub_eq_zero.mp ((mul_eq_zero.mp his).resolve_left hwi)).symm
    obtain ⟨a, ha, hea⟩ := hp i
    exact subset_convexHull ℝ _ ⟨a, Finset.mem_filter.mpr ⟨ha, by rwa [hea]⟩, hea⟩
theorem promote_exposure {α : Type} [Fintype α]
    {v : α → ExponentSpace} {S T : Finset α} (hS : IsFaceLabels v S) (hT : T.Nonempty)
    {g : ExponentSpace →ₗ[ℝ] ℝ} {m : ℝ}
    (hTmem : ∀ b, b ∈ T ↔ b ∈ S ∧ g (v b) = m)
    (hle : ∀ b ∈ S, g (v b) ≤ m) : IsFaceLabels v T := by
  classical
  obtain ⟨a, ha⟩ := hT
  obtain ⟨haS, hag⟩ := (hTmem a).mp ha
  obtain ⟨f, hf⟩ := hS.2
  let r (b : α) := (g (v b) - m) / (f (v a) - f (v b))
  obtain ⟨b₀, -, hmax⟩ := Finset.exists_max_image Finset.univ r ⟨a, Finset.mem_univ _⟩
  let M := r b₀ + 1
  let G := M • f + g
  have hG (b : α) : G (v b) = M * f (v b) + g (v b) := rfl
  have hinside (b : α) (hb : b ∈ S) : f (v b) = f (v a) :=
    le_antisymm ((hf a).1 haS b) ((hf b).1 hb a)
  have hout (b : α) (hb : b ∉ S) : G (v b) < G (v a) := by
    have hden := sub_pos.mpr (exposed_lt hf haS hb)
    have hr : r b < M := (hmax b (Finset.mem_univ _)).trans_lt (lt_add_of_pos_right _ zero_lt_one)
    have h := (div_lt_iff₀ hden).mp hr
    rw [hG, hG, hag]
    rw [mul_sub] at h
    linarith
  have hmaxG (b : α) : G (v b) ≤ G (v a) := by
    by_cases hb : b ∈ S
    · simp only [hG, hinside b hb, hag, add_le_add_iff_left]
      exact hle b hb
    · exact (hout b hb).le
  refine ⟨⟨a, ha⟩, G, fun b => ?_⟩
  rw [hTmem]
  constructor
  · rintro ⟨hb, hbg⟩ c
    have he : G (v b) = G (v a) := by rw [hG, hG, hinside b hb, hbg, hag]
    exact (hmaxG c).trans_eq he.symm
  · intro hb
    have hbS : b ∈ S := by
      by_contra hn
      exact (hout b hn).not_ge (hb a)
    refine ⟨hbS, le_antisymm (hle b hbS) ?_⟩
    have h := hb a
    simpa only [hG, hinside b hbS, hag, add_le_add_iff_left] using h
theorem cone_to_proper_face {α : Type} [Fintype α] {v : α → ExponentSpace}
    {S : Finset α} (hS : IsFaceLabels v S) {x : ExponentSpace} (hx : x ∈ faceHull v S)
    (hne : x ≠ faceCenter v S) :
    ∃ (T : Finset α) (y : ExponentSpace), T < S ∧ IsFaceLabels v T ∧
      y ∈ faceHull v T ∧ Wbtw ℝ (faceCenter v S) x y := by
  classical
  obtain ⟨y, g, hy, hbtw, hle, a, ha, halt⟩ := relative_support hS.1 hx hne
  let T := S.filter (fun b => g (v b) = g y)
  have hyT : y ∈ faceHull v T := mem_maximizing_hull hy hle
  obtain ⟨_, b, hb, _⟩ := convexHull_nonempty_iff.mp ⟨y, hyT⟩
  have hTmem (b : α) : b ∈ T ↔ b ∈ S ∧ g (v b) = g y := Finset.mem_filter
  have hlt : T < S :=
    lt_of_le_not_ge (Finset.filter_subset _ _) (fun h => halt.ne ((hTmem a).mp (h ha)).2)
  exact ⟨T, y, hlt, promote_exposure hS ⟨b, hb⟩ hTmem hle, hyT, hbtw⟩
end
end K1_13_5_4_2_5_2_1_1
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_5_2_1_1
noncomputable section
open K1_13_5_4_2 K1_13_5_4_2_5_2_1
open MeasureTheory
def chainHull {α : Type} {n : ℕ} (v : α → ExponentSpace)
    (F : Fin (n + 1) → Finset α) : Set ExponentSpace :=
  convexHull ℝ (Set.range (fun j => faceCenter v (F j)))
theorem cover_from_face {α : Type} [Fintype α] (v : α → ExponentSpace)
    (k : ℕ) (S : Finset α) (x : ExponentSpace) (hk : S.card = k)
    (hS : IsFaceLabels v S) (hx : x ∈ faceHull v S) :
    ∃ (n : ℕ) (F : Fin (n + 1) → Finset α),
      n ≤ Module.finrank ℝ (vectorSpan ℝ (v '' (S : Set α))) ∧
      StrictMono F ∧ (∀ j, IsFaceLabels v (F j)) ∧ F (Fin.last n) = S ∧
      x ∈ chainHull v F := by
  induction k using Nat.strong_induction_on generalizing S x with
  | h k ih =>
    by_cases he : x = faceCenter v S
    · refine ⟨0, fun _ => S, Nat.zero_le _, ?_, fun _ => hS, rfl, ?_⟩
      · intro i j hij
        exfalso
        omega
      · exact subset_convexHull ℝ _ ⟨0, he.symm⟩
    obtain ⟨T, y, hTS, hT, hy, hbtw⟩ := cone_to_proper_face hS hx he
    have hc : T.card < k := hk ▸ Finset.card_lt_card hTS
    obtain ⟨n, F, hn, hmono, hface, hlast, hyF⟩ := ih T.card hc T y rfl hT hy
    have hd := Submodule.finrank_lt_finrank_of_lt (face_span_lt hT hTS)
    let G : Fin (n + 1 + 1) → Finset α := Fin.snoc F S
    have hG (j : Fin (n + 1)) : G j.castSucc = F j := by simp [G]
    have hlastG : G (Fin.last (n + 1)) = S := by simp [G]
    refine ⟨n + 1, G, Nat.succ_le_of_lt (hn.trans_lt hd), ?_, ?_, hlastG, ?_⟩
    · refine Fin.strictMono_iff_lt_succ.mpr (fun i => ?_)
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [hG, Fin.succ_last, hlastG, hlast]
        exact hTS
      · rw [hG, ← Fin.castSucc_succ, hG]
        exact hmono j.castSucc_lt_succ
    · intro j
      refine Fin.lastCases ?_ (fun j' => ?_) j
      · rw [hlastG]
        exact hS
      · rw [hG]
        exact hface j'
    · have hcy : faceCenter v S ∈ chainHull v G :=
        subset_convexHull ℝ _ ⟨Fin.last (n + 1), congrArg (faceCenter v) hlastG⟩
      have hsub : chainHull v F ⊆ chainHull v G := by
        apply convexHull_mono
        rintro _ ⟨i, rfl⟩
        exact ⟨i.castSucc, congrArg (faceCenter v) (hG i)⟩
      exact (convex_convexHull ℝ _).mem_of_wbtw hbtw hcy (hsub hyF)
theorem flag_subset_hull {α : Type} [Fintype α] (v : α → ExponentSpace)
    {F : Fin 5 → Finset α} (hF : F ∈ flags v) :
    flagSimplex v F ⊆ convexHull ℝ (Set.range v) := by
  apply convexHull_min _ (convex_convexHull ℝ _)
  rintro _ ⟨j, rfl⟩
  have hj := center_mem_faceHull v (((mem_flags v F).mp hF).2 j).1
  apply convexHull_mono _ hj
  rintro _ ⟨a, _, rfl⟩
  exact Set.mem_range_self a
theorem short_chain_null {α : Type} (v : α → ExponentSpace) (n : Fin 4)
    (F : Fin (n.val + 1) → Finset α) : volume (chainHull v F) = 0 := by
  let p (i : Fin (n.val + 1)) := faceCenter v (F i)
  have hdim := finrank_vectorSpan_range_le ℝ p (n := n.val) (Fintype.card_fin _)
  have hproper : affineSpan ℝ (Set.range p) ≠ ⊤ := by
    intro he
    rw [← direction_affineSpan, he, AffineSubspace.direction_top, finrank_top,
      Module.finrank_fin_fun] at hdim
    exact (not_le_of_gt n.isLt) hdim
  exact measure_mono_null (convexHull_min (subset_affineSpan ℝ _) (affineSpan ℝ _).convex)
    (Measure.addHaar_affineSubspace volume _ hproper)
theorem proof : K1_13_5_4_2_5_2_1.c1 := by
  classical
  intro α _ v
  let H := convexHull ℝ (Set.range v)
  let U := ⋃ F ∈ flags v, flagSimplex v F
  let N := ⋃ (n : Fin 4) (F : Fin (n.val + 1) → Finset α), chainHull v F
  have hN : volume N = 0 :=
    measure_iUnion_null fun n => measure_iUnion_null fun F => short_chain_null v n F
  have hUH : U ⊆ H := by
    refine Set.iUnion₂_subset fun F hF => ?_
    exact flag_subset_hull v hF
  have hHU : H \ U ⊆ N := by
    rintro x ⟨hx, hxU⟩
    have hlabels : v '' ((Finset.univ : Finset α) : Set α) = Set.range v := by simp
    have hx' : x ∈ faceHull v Finset.univ := by simpa only [faceHull, hlabels] using hx
    have hne : (Finset.univ : Finset α).Nonempty := by
      obtain ⟨_, a, ha, _⟩ := convexHull_nonempty_iff.mp ⟨x, hx'⟩
      exact ⟨a, ha⟩
    have hface : IsFaceLabels v Finset.univ := ⟨hne, 0, by intro a; simp⟩
    obtain ⟨n, F, hn, hmono, hf, _, hxF⟩ :=
      cover_from_face v _ Finset.univ x rfl hface hx'
    have hd : n ≤ 4 := hn.trans (Submodule.finrank_le _ |>.trans_eq (Module.finrank_fin_fun ℝ))
    by_cases hshort : n < 4
    · exact Set.mem_iUnion.2 ⟨⟨n, hshort⟩, Set.mem_iUnion.2 ⟨F, hxF⟩⟩
    · have he : n = 4 := le_antisymm hd (Nat.le_of_not_lt hshort)
      subst n
      exact (hxU (Set.mem_iUnion₂.2 ⟨F, (mem_flags v F).2 ⟨hmono, hf⟩, hxF⟩)).elim
  have hle : H ≤ᵐ[volume] U := ae_le_set.mpr (measure_mono_null hHU hN)
  have hge : U ≤ᵐ[volume] H := Filter.Eventually.of_forall fun _ hx => hUH hx
  exact hle.antisymm hge
end
end K1_13_5_4_2_5_2_1_1
end
section
set_option autoImplicit false
namespace K1_13_7_5_3_3_3_1
noncomputable section
open K1_13_5_4_2_4 K1_13_5_4_2_4_2 K1_13_7_5_3_3_3 MvPolynomial
open K1_13_5_4_2_4_2_3 hiding cutIdeal
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {A : Fin 4 → Finset Exponent}
theorem chartPower_mem (a : Chart A) (m : ℕ) :
    chartProduct A a ^ m ∈ slotPiece A (fun _ => m) := by
  classical
  have hsum : (∑ j : Fin 4, (Pi.single j 1 : Degree)) = (fun _ => 1) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hpow : m • (fun _ : Fin 4 => (1 : ℕ)) = (fun _ => m) := by
    funext j
    change m • (1 : ℕ) = m
    simp
  have hchart := IsWeightedHomogeneous.prod (w := slotWeight A) Finset.univ
    (fun j : Fin 4 => (MvPolynomial.X ⟨j, a j⟩ : SlotRing A))
    (fun j => Pi.single j 1)
    (fun j _ => isWeightedHomogeneous_X (CoefficientField A) (slotWeight A) (⟨j, a j⟩ : Slot A))
  rw [hsum] at hchart
  rw [← hpow]
  exact hchart.pow m
theorem dehom_chartPower (a : Chart A) (m : ℕ) :
    dehom A (chartProduct A a ^ m) = chartPower a m := by
  classical
  rw [map_pow, chartProduct, map_prod]
  simp only [dehom, aeval_X]
  rw [← monomial_sum_one, monomial_pow, one_pow, chartPower]
private theorem component_mul {g : SlotRing A} {e : Degree}
    (hg : g ∈ slotPiece A e) (f : SlotRing A) (d : Degree) :
    weightedHomogeneousComponent (slotWeight A) (d + e) (f * g) =
      weightedHomogeneousComponent (slotWeight A) d f * g := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial a c =>
    have ha := isWeightedHomogeneous_monomial (slotWeight A) a c rfl
    have hg' : g.IsWeightedHomogeneous (slotWeight A) e := hg
    simp only [weightedHomogeneousComponent_of_mem (ha.mul hg'),
      weightedHomogeneousComponent_of_mem ha, add_right_cancel_iff]
    split <;> simp_all
  | add p q hp hq => simp [add_mul, hp, hq]
theorem cutIdeal_le (i : Fin 4) :
    K1_13_5_4_2_4_2_3.cutIdeal A (i.val + 1) ≤
      relationIdeal A i.val ⊔ Ideal.span {homogeneousEquation A i} := by
  apply sup_le
  · have hprefix : prefixIdeal A 0 ≤ prefixIdeal A i.val := by simp [prefixIdeal]
    have hrel : relationIdeal A 0 ≤ relationIdeal A i.val := by
      apply Ideal.span_mono
      intro f hf
      exact ⟨hf.1, hprefix hf.2⟩
    exact hrel.trans le_sup_left
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    change j.val < i.val + 1 at hj
    by_cases hji : j = i
    · subst j
      exact Submodule.mem_sup_right (Ideal.mem_span_singleton_self _)
    · have hlt : j.val < i.val := by
        have hn : j.val ≠ i.val := fun he => hji (Fin.ext he)
        omega
      apply Submodule.mem_sup_left
      apply Ideal.subset_span
      exact ⟨⟨_, homogeneousEquation_mem j⟩, by
        rw [dehom_equation]
        exact Ideal.subset_span ⟨j, hlt, rfl⟩⟩
theorem extract_multiplier (i : Fin 4) (d : Degree) (f : SlotRing A)
    (hf : f ∈ slotPiece A (shift d i 1))
    (hcut : f ∈ K1_13_5_4_2_4_2_3.cutIdeal A (i.val + 1)) :
    ∃ r ∈ piece A d, dehom A f - genericEquation A i * r ∈ prefixIdeal A i.val := by
  classical
  let J := relationIdeal A i.val
  have hJ : f ∈ Ideal.span {homogeneousEquation A i} ⊔ J := by
    rw [sup_comm]
    exact cutIdeal_le i hcut
  obtain ⟨u, v, hv, hsum⟩ := Ideal.mem_span_singleton_sup.mp hJ
  let r := weightedHomogeneousComponent (slotWeight A) d u
  let s := weightedHomogeneousComponent (slotWeight A) (shift d i 1) v
  have hhom : J.IsHomogeneous (slotPiece A) :=
    Ideal.homogeneous_span _ _ fun _ h => h.1
  have hs : s ∈ J := weightedHomogeneousComponent_mem_of_mem _ _ hhom hv _
  have hrel : r * homogeneousEquation A i + s = f := by
    have he := congrArg (weightedHomogeneousComponent (slotWeight A) (shift d i 1)) hsum
    rw [map_add, weightedHomogeneousComponent_eq_self (show f.IsWeightedHomogeneous _ _ from hf)]
      at he
    change weightedHomogeneousComponent (slotWeight A) (d + Pi.single i 1)
      (u * homogeneousEquation A i) + s = f at he
    rwa [component_mul (homogeneousEquation_mem i)] at he
  have hle : J ≤ (prefixIdeal A i.val).comap (dehom A).toRingHom :=
    Ideal.span_le.mpr fun _ h => h.2
  refine ⟨dehom A r, ?_, ?_⟩
  · rw [← map_slotPiece]
    exact ⟨r, weightedHomogeneousComponent_mem _ _ _, rfl⟩
  · have he := congrArg (dehom A) hrel
    rw [map_add, map_mul, dehom_equation] at he
    rw [← he, mul_comm (genericEquation A i), add_sub_cancel_left]
    exact hle hs
theorem proof : K1_13_7_5_3_3_3.c1 := by
  intro A hz hv i d p hp hprefix a
  have hp' : p ∈ (slotPiece A (shift d i 1)).map (dehom A).toLinearMap := by
    rwa [map_slotPiece]
  obtain ⟨f, hf, hfp⟩ := hp'
  change dehom A f = p at hfp
  obtain ⟨n, hn⟩ := K1_13_5_4_2_4_2_3_1.proof A hz hv i f ⟨⟨_, hf⟩, hfp ▸ hprefix⟩
  obtain ⟨m, hm⟩ := K1_13_5_4_2_4_2_3_2.proof A hz i a f n hn
  have hshift : shift d i 1 + (fun _ => m) = shift (d + fun _ => m) i 1 := by
    unfold shift
    ac_rfl
  have hdeg : chartProduct A a ^ m * f ∈ slotPiece A (shift (d + fun _ => m) i 1) := by
    rw [← hshift, mul_comm]
    exact IsWeightedHomogeneous.mul hf (chartPower_mem a m)
  obtain ⟨r, hr, hrel⟩ := extract_multiplier i (d + fun _ => m) _ hdeg hm
  rw [map_mul, dehom_chartPower, hfp] at hrel
  exact ⟨m, r, hr, hrel⟩
end
end K1_13_7_5_3_3_3_1
end
section
namespace K1_13_7_5_2
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_1 K1_13_6 K1_13_7 K1_13_7_1
open scoped BigOperators
local notation "W" => MvPolynomial.weightedTotalDegree
def linearStep (f : Row 4) (n : ℕ) (P : Row 4) : Row 4 :=
  flowNumerator f P - (n : Row 4) * partialFlow (separant f) * P
private def linearJet (f : Row 4) : ℕ → Row 4
  | 0 => MvPolynomial.X 0
  | n+1 => linearStep f n (linearJet f n)
private theorem pderiv_zero_of_weight_lt (w : Fin 4 → ℕ) (i : Fin 4) (P : Row 4)
    (h : W w P < w i) : pderiv i P = 0 := by
  apply MvPolynomial.ext
  intro m
  rw [coeff_pderiv]
  have hz : P.coeff (m + Finsupp.single i 1) = 0 := by
    by_contra hn
    have hm := le_weightedTotalDegree w (MvPolynomial.mem_support_iff.mpr hn)
    rw [map_add, Finsupp.weight_single, one_smul] at hm
    omega
  simp [hz]
theorem sep_sep_zero {f : Row 4} (hf : (shape f).t = 1) :
    separant (separant f) = 0 := by
  let w : Fin 4 → ℕ := Pi.single 3 1
  have h := weightedTotalDegree_pderiv_le_sub w 3 f
  have h₁ : W w f = 1 := by simpa only [w, weightedTotalDegree_piSingle, shape] using hf
  have h₂ : w 3 = 1 := by decide
  rw [h₁, h₂] at h
  exact pderiv_zero_of_weight_lt w 3 _ (h.trans_lt (by decide))
theorem one_power_product_rule (n : ℕ) (U V : Geom[X]) :
    U * derivative (U ^ n * V) - (n : Geom[X]) * derivative U * (U ^ n * V) =
      U ^ (n + 1) * derivative V := by
  cases n with
  | zero => simp
  | succ n =>
    rw [derivative_mul, derivative_pow, Nat.succ_sub_one,
      pow_succ U n, pow_succ U (n+1)]
    simp only [C_eq_natCast, pow_succ U n]
    ring
private theorem eval_linearJet {f : Row 4} (hf : (shape f).t = 1) (S : Geom[X])
    (hon : atJet f S = 0) (hr : RegularAt f S) (n : ℕ) :
    atJet (linearJet f n) S = atJet (separant f) S ^ n * (derivative^[n]) S := by
  have hnz : atJet (separant f) S ≠ 0 := hr
  have hflow := eval_flowNumerator f (separant f) S hon
  have hsep : atJet (partialFlow (separant f)) S = derivative (atJet (separant f) S) := by
    simp only [flowNumerator, sep_sep_zero hf, atJet, map_mul, mul_zero,
      sub_zero] at hflow
    exact mul_left_cancel₀ hnz hflow
  induction n with
  | zero => simp [linearJet, atJet, jet]
  | succ n ih =>
    let e := MvPolynomial.eval (jet S : Fin 4 → Geom[X])
    change e (linearStep f n (linearJet f n)) = _
    unfold linearStep
    rw [map_sub, map_mul, map_mul, map_natCast]
    change atJet (flowNumerator f (linearJet f n)) S -
      (n : Geom[X]) * atJet (partialFlow (separant f)) S * atJet (linearJet f n) S = _
    rw [eval_flowNumerator _ _ _ hon, hsep, ih, one_power_product_rule,
      Function.iterate_succ_apply']
private theorem weight_coeff_deriv (w : Fin 4 → ℕ) (P : Row 4) :
    W w (coefficientDerivative P) ≤ W w P := by
  classical
  apply weight_le_of_support_subset
  intro m hm
  obtain ⟨j, hj, hmj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  have h : j = m := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hmj) (by rw [MvPolynomial.coeff_monomial, ite_eq_right hne])
  exact h ▸ hj
private theorem partialFlow_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    (P : Row 4) {d : ℕ} (hP : W w P ≤ d) : W w (partialFlow P) ≤ d + Δ := by
  classical
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.add_mem
  · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
      ((weight_coeff_deriv w P).trans (hP.trans (Nat.le_add_right _ _)))
  · apply Submodule.sum_mem
    intro i _
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    rw [mul_assoc]
    apply (weight_const_mul_le w _ _).trans
    by_cases h : w i.castSucc ≤ d
    · have hp := (weightedTotalDegree_pderiv_le_sub w i.castSucc P).trans
        (Nat.sub_le_sub_right hP (w i.castSucc))
      have he := hshift i
      exact (weightedTotalDegree_mul_le _ _ _).trans
        ((Nat.add_le_add (weight_X_le w _) hp).trans (by omega))
    · rw [pderiv_zero_of_weight_lt w _ P (hP.trans_lt (Nat.lt_of_not_ge h)), mul_zero,
        weightedTotalDegree_zero]
      exact Nat.zero_le _
private theorem separant_bound (w : Fin 4 → ℕ) {f : Row 4} {B : ℕ} (hf : W w f ≤ B) :
    W w (separant f) ≤ B - w 3 :=
  (weightedTotalDegree_pderiv_le_sub w 3 f).trans (Nat.sub_le_sub_right hf _)
theorem linearStep_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    {f P : Row 4} {B d : ℕ} (hB : w 3 ≤ B) (hf : W w f ≤ B) (hP : W w P ≤ d) (n : ℕ) :
    W w (linearStep f n P) ≤ d + (B - w 3 + Δ) := by
  have hsep := separant_bound w hf
  unfold linearStep flowNumerator
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sub_mem
  · apply Submodule.sub_mem
    · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
      exact (weightedTotalDegree_mul_le _ _ _).trans
        ((Nat.add_le_add hsep (partialFlow_bound w Δ hshift P hP)).trans (by omega))
    · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
      by_cases h : w 3 ≤ d
      · exact (weightedTotalDegree_mul_le _ _ _).trans
          ((Nat.add_le_add (partialFlow_bound w Δ hshift f hf) (separant_bound w hP)).trans (by omega))
      · rw [separant, pderiv_zero_of_weight_lt w _ P (hP.trans_lt (Nat.lt_of_not_ge h)),
          mul_zero, weightedTotalDegree_zero]
        exact Nat.zero_le _
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    rw [mul_assoc, ← map_natCast (MvPolynomial.C : Geom[X] →+* Row 4)]
    exact (weight_const_mul_le w _ _).trans
      ((weightedTotalDegree_mul_le _ _ _).trans
        ((Nat.add_le_add (partialFlow_bound w Δ hshift (separant f) hsep) hP).trans (by omega)))
private theorem linearJet_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ) {f : Row 4} {B : ℕ}
    (hB : w 3 ≤ B) (hf : W w f ≤ B) (n : ℕ) :
    W w (linearJet f n) ≤ w 0 + n * (B - w 3 + Δ) := by
  induction n with
  | zero => simpa only [linearJet, zero_mul, add_zero] using weight_X_le (R := Geom[X]) w 0
  | succ n ih =>
    simpa only [linearJet, Nat.add_mul, one_mul, Nat.add_assoc] using
      linearStep_bound w Δ hshift hB hf ih n
private def denominator (L : ℕ) (f : Row 4) : Row 4 := separant f ^ L
private theorem ordinary_eq_hasse (S : Geom[X]) (n : ℕ) :
    derivative^[n] S = Polynomial.C (n.factorial : Geom) * hasseDeriv n S := by
  ext m
  rw [coeff_iterate_derivative, Polynomial.coeff_C_mul, hasseDeriv_coeff,
    Nat.descFactorial_eq_factorial_mul_choose]
  simp only [nsmul_eq_mul, Nat.cast_mul, mul_assoc]
end
end K1_13_7_5_2
end
section
namespace K1_13_6_2_4_5
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_4
private theorem length_le_of_surjection {A B : Type*} [CommRing A] [CommRing B]
    (ψ : A →+* B) (hψ : Function.Surjective ψ) {I : Ideal A} {J : Ideal B}
    (hIJ : I ≤ J.comap ψ) : Module.length B (B ⧸ J) ≤ Module.length A (A ⧸ I) := by
  rw [Module.length_quotient, Module.length_quotient]
  apply WithBot.coe_le_coe.mp
  rw [Order.coheight_eq_krullDim_Ici, Order.coheight_eq_krullDim_Ici]
  let F : Set.Ici J → Set.Ici I := fun K => ⟨K.1.comap ψ, hIJ.trans (Ideal.comap_mono K.2)⟩
  apply Order.krullDim_le_of_strictMono F
  intro K L hKL
  change K.1.comap ψ < L.1.comap ψ
  exact lt_of_le_of_ne (Ideal.comap_mono hKL.le)
    (fun h => hKL.ne (Subtype.ext (Ideal.comap_injective_of_surjective ψ hψ h)))
theorem dim_of_finite_polynomial {R : Type*} [CommRing R] [IsDomain R] {d : ℕ}
    (g : MvPolynomial (Fin d) GeoField →+* R) (hinj : Function.Injective g)
    (hfin : g.Finite) : ringKrullDim R = (d : WithBot ℕ∞) := by
  let B := MvPolynomial (Fin d) GeoField
  let algebra := g.toAlgebra
  let := algebra
  let faithful : FaithfulSMul B R := (faithfulSMul_iff_algebraMap_injective B R).mpr hinj
  let finite : Module.Finite B R := hfin
  have hB : ringKrullDim B = (d : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    simp
  rw [← hB]
  apply le_antisymm
  · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap B R))
    intro x y hxy
    exact Ideal.IsIntegral.under_lt_under (show x.asIdeal < y.asIdeal from hxy)
  · obtain ⟨q, hq, hheight⟩ := Ideal.exists_isPrime_le_height (n := d) hB.ge
    obtain ⟨z, hz⟩ := Algebra.IsIntegral.comap_surjective B R (⟨q, hq⟩ : PrimeSpectrum B)
    have hunder : z.asIdeal.under B = q := congrArg PrimeSpectrum.asIdeal hz
    have hle := Ideal.height_under_le_height (R := B) z.asIdeal
    rw [hunder] at hle
    calc
      ringKrullDim B = (d : WithBot ℕ∞) := hB
      _ ≤ (z.asIdeal.height : WithBot ℕ∞) := WithBot.coe_le_coe.mpr (hheight.trans hle)
      _ ≤ ringKrullDim R := Ideal.height_le_ringKrullDim_of_isPrime
theorem dim_eq_hilbert (P : Ideal GeoJets5) [P.IsPrime] :
    ringKrullDim (GeoJets5 ⧸ P) =
      ((MvPolynomial.affineHilbertPolynomial P).natDegree : WithBot ℕ∞) := by
  obtain ⟨d, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg GeoField (GeoJets5 ⧸ P)
  rw [MvPolynomial.natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective g hfin hinj,
    Nat.card_fin]
  exact dim_of_finite_polynomial g.toRingHom hinj hfin
private theorem dim_after_proper_cut {P C : Ideal GeoJets5} {D : GeoJets5} {d : ℕ}
    (hP : P.IsPrime) (hd : OfDim P (d + 1)) (hD : D ∉ P)
    (hC : (sectionIdeal P D).IsMinimalPrime C) : OfDim C d := by
  let := hP
  let := hC.isPrime
  have hp : (MvPolynomial.affineHilbertPolynomial P).natDegree = d + 1 := by
    exact ENat.natCast_inj.mp (WithBot.coe_injective ((dim_eq_hilbert P).symm.trans hd))
  have hc := MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one hD hC
  rw [hp] at hc
  simpa [OfDim, Nat.add_right_cancel hc] using dim_eq_hilbert C
end
end K1_13_6_2_4_5
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_3_3_2
noncomputable section
open K1_13_6_3_5_3 K1_13_6_3_5_3_3
open scoped Polynomial
variable {k L σ : Type} [Field k] [Field L] [Algebra k L]
private def planePolynomial :
    MvPolynomial (Fin 2) k →+* (k[X])[X] :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C)
    ![Polynomial.X, Polynomial.C Polynomial.X * Polynomial.X]
theorem planePolynomial_monomial (m : Fin 2 →₀ ℕ) (c : k) :
    planePolynomial (MvPolynomial.monomial m c) =
      Polynomial.monomial (m 0 + m 1) (Polynomial.monomial (m 1) c) := by
  rw [planePolynomial, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial,
    Finsupp.prod_pow, Fin.prod_univ_two]
  change Polynomial.C (Polynomial.C c) * (Polynomial.X ^ m 0 *
    (Polynomial.C Polynomial.X * Polynomial.X) ^ m 1) = _
  rw [mul_pow, ← map_pow, ← Polynomial.C_mul_X_pow_eq_monomial,
    ← Polynomial.C_mul_X_pow_eq_monomial, pow_add, map_mul]
  rw [mul_left_comm (Polynomial.X ^ m 0) (Polynomial.C ((Polynomial.X : k[X]) ^ m 1)),
    mul_assoc]
theorem planePolynomial_coeff (p : MvPolynomial (Fin 2) k) (m : Fin 2 →₀ ℕ) :
    ((planePolynomial p).coeff (m 0 + m 1)).coeff (m 1) = p.coeff m := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, Polynomial.coeff_add, AddMonoidAlgebra.coeff_add, hp, hq]
    rfl
  | monomial n c =>
    rw [planePolynomial_monomial, Polynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases h : n = m
    · simp [h]
    · rw [ite_eq_right h]
      by_cases hd : n 0 + n 1 = m 0 + m 1
      · rw [ite_eq_left hd, Polynomial.coeff_monomial]
        apply ite_eq_right
        intro h1
        apply h
        have h0 : n 0 = m 0 := by omega
        ext j
        fin_cases j
        · exact h0
        · exact h1
      · simp [hd]
theorem planePolynomial_injective :
    Function.Injective (planePolynomial (k := k)) := by
  intro p q h
  ext m
  rw [← planePolynomial_coeff p m, ← planePolynomial_coeff q m, h]
theorem planeEval_injective {b z : L} (hb : b ≠ 0) (hz : Transcendental k z) :
    Function.Injective
      (MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap k L))
        ![Polynomial.C b * Polynomial.X, (Polynomial.C b * Polynomial.X) * Polynomial.C z]) := by
  let f := Polynomial.mapRingHom (Polynomial.aeval (R := k) z).toRingHom
  let g := Polynomial.compRingHom (Polynomial.C b * Polynomial.X)
  have hg : Function.Injective g := by
    let e : L[X] ≃ₐ[L] L[X] :=
      Polynomial.algEquivOfCompEqX (Polynomial.C b * Polynomial.X)
        (Polynomial.C b⁻¹ * Polynomial.X)
        (by simp [← Polynomial.C_mul, ← mul_assoc, hb])
        (by simp [← Polynomial.C_mul, ← mul_assoc, hb])
    exact e.injective
  have hf : Function.Injective f :=
    Polynomial.map_injective _ (transcendental_iff_injective.mp hz)
  have heq : MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap k L))
      ![Polynomial.C b * Polynomial.X, (Polynomial.C b * Polynomial.X) * Polynomial.C z] =
      g.comp (f.comp planePolynomial) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [f, g, planePolynomial, Polynomial.aeval_C]
    · intro j
      fin_cases j
      · simp [f, g, planePolynomial]
      · simp [f, g, planePolynomial, mul_assoc, Polynomial.X_mul_C,
          mul_left_comm (Polynomial.C b) (Polynomial.C z)]
  rw [heq]
  exact hg.comp (hf.comp planePolynomial_injective)
theorem coneEval_X (u : σ → L) (j : σ) :
    coneEval k u (MvPolynomial.X j) = Polynomial.C (u j) * Polynomial.X := by
  simp [coneEval]
theorem coneEval_C (u : σ → L) (c : k) :
    coneEval k u (MvPolynomial.C c) = Polynomial.C (algebraMap k L c) := by
  simp [coneEval]
theorem projection_eval [Fintype σ] (u : σ → L) (i : σ) (a : σ → k)
    (hi : u i ≠ 0) :
    (coneEval k u).comp (lineProjection i a).toRingHom =
      MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap k L))
        ![Polynomial.C (u i) * Polynomial.X,
          (Polynomial.C (u i) * Polynomial.X) * Polynomial.C (linearValue a (ratios u i))] := by
  have hlinear : ∑ j, algebraMap k L (a j) * u j =
      u i * linearValue a (ratios u i) := by
    rw [linearValue, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Algebra.smul_def, ratios]
    field_simp
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [lineProjection, coneEval_C, MvPolynomial.algebraMap_eq]
  · intro j
    rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
    change coneEval k u ((lineProjection i a) (MvPolynomial.X j)) = _
    rw [lineProjection, MvPolynomial.aeval_X]
    have hcases : ∀ l : Fin 2, l = 0 ∨ l = 1 :=
      Fin.forall_fin_two.2 ⟨Or.inl rfl, Or.inr rfl⟩
    rcases hcases j with rfl | rfl
    · exact coneEval_X (k := k) u i
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      calc
        _ = (∑ l, Polynomial.C (algebraMap k L (a l) * u l)) * Polynomial.X := by
          rw [map_sum, Finset.sum_mul]
          simp only [map_mul, coneEval_C, coneEval_X, ← mul_assoc]
        _ = _ := by
          rw [← map_sum, hlinear, map_mul, mul_right_comm]
theorem mem_of_chart {F : Type} [Field F] (C : L →+* F) (V : ValuationSubring F)
    (hc : ∀ c : k, C (algebraMap k L c) ∈ V) {z r : L}
    (hz : C z ∈ V) (hr : IsIntegral (Algebra.adjoin k {z}) r) : C r ∈ V := by
  let S := Algebra.adjoin k ({z} : Set L)
  have hS (x : S) : C (x : L) ∈ V := by
    refine Algebra.adjoin_induction (p := fun y _ => C y ∈ V) ?_ hc ?_ ?_ x.property
    · intro y hy
      simpa [Set.mem_singleton_iff.mp hy] using hz
    · intro x y _ _ hx hy
      simpa only [map_add] using V.add_mem _ _ hx hy
    · intro x y _ _ hx hy
      simpa only [map_mul] using V.mul_mem _ _ hx hy
  let φ : S →+* V.toSubring := (C.comp S.val.toRingHom).codRestrict V.toSubring hS
  have h : IsIntegral V.toSubring (C r) := IsIntegral.map_of_comp_eq φ C rfl hr
  exact (Subring.isIntegrallyClosedIn_iff.mp
    (inferInstanceAs (IsIntegrallyClosedIn V F))) h
theorem integral_scaled {A F : Type} [CommRing A] [Field F]
    (f : A →+* F) (C : L →+* F) (hc : ∀ c : k, C (algebraMap k L c) ∈ f.range)
    {s : F} {r z : L} (hz : z ≠ 0) (hs : s ∈ f.range) (ht : s * C z ∈ f.range)
    (hr : IsIntegral (Algebra.adjoin k {z}) r)
    (hr' : IsIntegral (Algebra.adjoin k {z⁻¹}) (r / z)) :
    f.IsIntegralElem (s * C r) := by
  let : Algebra A F := f.toAlgebra
  let B := (integralClosure A F).toSubring
  by_contra h
  obtain ⟨V, hBV, hn⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (R := B) (show s * C r ∉ B from h)
  have hm {x : F} (hx : x ∈ f.range) : x ∈ V := by
    obtain ⟨y, rfl⟩ := hx
    exact hBV (show f y ∈ B from f.isIntegralElem_map)
  apply hn
  rcases V.mem_or_inv_mem (C z) with hV | hV
  · exact V.mul_mem _ _ (hm hs) (mem_of_chart C V (fun c => hm (hc c)) hV hr)
  · have hz' : C z⁻¹ ∈ V := by simpa only [map_inv₀] using hV
    have hp := V.mul_mem _ _ (hm ht) (mem_of_chart C V (fun c => hm (hc c)) hz' hr')
    rwa [mul_assoc, ← map_mul, mul_div_cancel₀ _ hz] at hp
theorem proof : K1_13_6_3_5_3_3.c2 := by
  classical
  intro k L σ _ _ _ _ u i a hi
  dsimp only
  intro hz hchart
  let z := linearValue a (ratios u i)
  let P := coneIdeal k u
  let φ := lineProjection i a
  let Q := P.comap φ.toRingHom
  have hp := projection_eval u i a hi
  constructor
  · change RingHom.ker ((coneEval k u).comp φ.toRingHom) = ⊥
    rw [show φ = lineProjection i a from rfl, hp, ← RingHom.injective_iff_ker_eq_bot]
    exact planeEval_injective hi hz
  · let ι := algebraMap L[X] (RatFunc L)
    let g := ι.comp (coneEval k u)
    have hg : RingHom.ker g = P :=
      RingHom.ker_comp_of_injective _ (RatFunc.algebraMap_injective L)
    let e := Ideal.Quotient.lift P g (fun _ hx => RingHom.mem_ker.mp (hg.symm ▸ hx))
    have he : Function.Injective e := RingHom.lift_injective_of_ker_le_ideal _ _ hg.le
    let β : (MvPolynomial (Fin 2) k ⧸ Q) →ₐ[k] (MvPolynomial σ k ⧸ P) :=
      onCoordinateRings P φ
    let f := e.comp β.toRingHom
    let s := RatFunc.C (u i) * RatFunc.X
    have hf (p : MvPolynomial (Fin 2) k) :
        f (Ideal.Quotient.mk Q p) =
          ι (MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap k L))
            ![Polynomial.C (u i) * Polynomial.X,
              (Polynomial.C (u i) * Polynomial.X) * Polynomial.C z] p) := by
      change e (Ideal.Quotient.mk P (φ p)) = _
      rw [Ideal.Quotient.lift_mk]
      exact congrArg ι (RingHom.congr_fun hp p)
    have hc (c : k) : RatFunc.C (algebraMap k L c) ∈ f.range := by
      refine ⟨Ideal.Quotient.mk Q (MvPolynomial.C c), ?_⟩
      rw [hf, MvPolynomial.eval₂Hom_C]
      rfl
    have hs : s ∈ f.range := by
      refine ⟨Ideal.Quotient.mk Q (MvPolynomial.X 0), ?_⟩
      rw [hf, MvPolynomial.eval₂Hom_X']
      simp [ι, s]
    have ht : s * RatFunc.C z ∈ f.range := by
      refine ⟨Ideal.Quotient.mk Q (MvPolynomial.X 1), ?_⟩
      rw [hf, MvPolynomial.eval₂Hom_X']
      simp [ι, s]
    have hgen (j : σ) : β.toRingHom.IsIntegralElem (Ideal.Quotient.mk P (MvPolynomial.X j)) := by
      apply RingHom.IsIntegralElem.of_map he
      have hvalue : e (Ideal.Quotient.mk P (MvPolynomial.X j)) =
          s * RatFunc.C (ratios u i j) := by
        rw [Ideal.Quotient.lift_mk, show g (MvPolynomial.X j) = ι (coneEval k u (MvPolynomial.X j))
          from rfl, coneEval_X]
        have hu : u i * ratios u i j = u j := mul_div_cancel₀ _ hi
        simp only [s, ι, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
        rw [mul_right_comm, ← map_mul, hu]
      rw [hvalue]
      exact integral_scaled f RatFunc.C hc hz.ne_zero hs ht (hchart.1 j) (hchart.2 j)
    change β.toRingHom.Finite
    apply RingHom.IsIntegral.to_finite
    · intro x
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      let : Algebra (MvPolynomial (Fin 2) k ⧸ Q) (MvPolynomial σ k ⧸ P) := β.toRingHom.toAlgebra
      change Ideal.Quotient.mk P p ∈ integralClosure (MvPolynomial (Fin 2) k ⧸ Q) _
      induction p using MvPolynomial.induction_on with
      | C c =>
        have h : β.toRingHom (Ideal.Quotient.mk Q (MvPolynomial.C c)) =
            Ideal.Quotient.mk P (MvPolynomial.C c) := by
          change Ideal.Quotient.mk P (φ (MvPolynomial.C c)) = _
          simp [φ, lineProjection, MvPolynomial.algebraMap_eq]
        rw [← h]
        exact β.toRingHom.isIntegralElem_map
      | add p q hp hq =>
        rw [map_add]
        exact (integralClosure _ _).add_mem hp hq
      | mul_X p j hp =>
        rw [map_mul]
        exact (integralClosure _ _).mul_mem hp (hgen j)
    · apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap k (MvPolynomial (Fin 2) k ⧸ Q))
      have hcomp : β.toRingHom.comp (algebraMap k (MvPolynomial (Fin 2) k ⧸ Q)) =
          algebraMap k (MvPolynomial σ k ⧸ P) :=
        RingHom.ext fun c => β.commutes c
      rw [hcomp]
      exact RingHom.finiteType_algebraMap.mpr inferInstance
end
end K1_13_6_3_5_3_3_2
end
section
namespace K1_13_4_5_2
noncomputable section
open K1_13_4 K1_13_4_5 Polynomial
open scoped Polynomial BigOperators
private abbrev jetWeight (w : Fin 3 → ℕ) : SeedVar → ℕ :=
  fun i => i.elim 0 w
theorem weighted_coeff_le (w : Fin 3 → ℕ) (F : GenericRow) (i : ℕ) :
    ((asSeedPoly F).coeff i).weightedTotalDegree w ≤ F.weightedTotalDegree (jetWeight w) := by
  apply Finset.sup_le
  intro a ha
  have hs : a.optionElim i ∈ F.support := by
    rw [MvPolynomial.mem_support_iff] at ha ⊢
    simpa only [asSeedPoly, MvPolynomial.optionEquivLeft_coeff_coeff] using ha
  have h := MvPolynomial.le_weightedTotalDegree (jetWeight w) hs
  rw [Finsupp.weight_apply, Finsupp.sum_option_index_smul] at h
  simpa only [jetWeight, Option.elim_none, Option.elim_some, smul_zero, zero_add,
    Finsupp.some_optionElim, Finsupp.weight_apply] using h
theorem weighted_resultant_le (w : Fin 3 → ℕ) (F G : GenericRow) (m n : ℕ) :
    ((asSeedPoly F).resultant (asSeedPoly G) m n).weightedTotalDegree w ≤
      n * F.weightedTotalDegree (jetWeight w) + m * G.weightedTotalDegree (jetWeight w) := by
  classical
  let A := (asSeedPoly F).sylvester (asSeedPoly G) m n
  let B := F.weightedTotalDegree (jetWeight w)
  let D := G.weightedTotalDegree (jetWeight w)
  have hleft (i : Fin (m + n)) (j : Fin m) : (A i (j.castAdd n)).weightedTotalDegree w ≤ D := by
    simp only [A, sylvester, Matrix.of_apply, Fin.addCases_left]
    split
    · exact weighted_coeff_le w G _
    · simp [MvPolynomial.weightedTotalDegree_zero]
  have hright (i : Fin (m + n)) (j : Fin n) : (A i (j.natAdd m)).weightedTotalDegree w ≤ B := by
    simp only [A, sylvester, Matrix.of_apply, Fin.addCases_right]
    split
    · exact weighted_coeff_le w F _
    · simp [MvPolynomial.weightedTotalDegree_zero]
  change A.det.weightedTotalDegree w ≤ n * B + m * D
  rw [Nat.add_comm (n * B), Matrix.det_apply]
  refine (AddMonoidAlgebra.supDegree_sum_le (D := Finsupp.weight w)).trans (Finset.sup_le ?_)
  intro π _
  have hprod : (∏ i, A (π i) i).weightedTotalDegree w ≤ m * D + n * B := by
    have hbound : (∏ i, A (π i) i).weightedTotalDegree w ≤
        ∑ i, (A (π i) i).weightedTotalDegree w :=
      AddMonoidAlgebra.supDegree_prod_le (D := Finsupp.weight w) (map_zero _) (map_add _)
    apply hbound.trans
    rw [Fin.sum_univ_add]
    have h₁ : (∑ j : Fin m, (A (π (j.castAdd n)) (j.castAdd n)).weightedTotalDegree w) ≤
        ∑ _j : Fin m, D := Finset.sum_le_sum fun j _ => hleft _ j
    have h₂ : (∑ j : Fin n, (A (π (j.natAdd m)) (j.natAdd m)).weightedTotalDegree w) ≤
        ∑ _j : Fin n, B := Finset.sum_le_sum fun j _ => hright _ j
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
      using Nat.add_le_add h₁ h₂
  change (Equiv.Perm.sign π • (∏ i, A (π i) i)).weightedTotalDegree w ≤ m * D + n * B
  have hneg (p : Lower) : (-p).weightedTotalDegree w = p.weightedTotalDegree w :=
    AddMonoidAlgebra.supDegree_neg (D := Finsupp.weight w)
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs | hs <;>
    simpa [hs, hneg] using hprod
theorem proof : K1_13_4_5.c2 := by
  intro F G
  constructor
  · have h := weighted_resultant_le (fun _ : Fin 3 => 1) F G (seedDegree F) (seedDegree G)
    change (actualSeedResultant F G).weightedTotalDegree (fun _ => 1) ≤
      seedDegree G * jetTotal F + seedDegree F * jetTotal G at h
    have hw : (fun _ : Fin 3 => (1 : ℕ)) = 1 := by
      funext i
      simp only [Pi.one_apply]
    rwa [hw, MvPolynomial.weightedTotalDegree_one] at h
  · simpa only [actualSeedResultant, lowerIndex_eq_weighted, jetIndex, jetWeight]
      using weighted_resultant_le Fin.val F G (seedDegree F) (seedDegree G)
end
end K1_13_4_5_2
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_5_2
noncomputable section
open K1_13_6_3_5_5
variable {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
theorem minimalPrimes_ker (a : A →+* C) (ha : Function.Surjective a) :
    (RingHom.ker a).minimalPrimes = Ideal.comap a '' (⊥ : Ideal C).minimalPrimes := by
  rw [RingHom.ker_eq_comap_bot, Ideal.comap_minimalPrimes_eq_of_surjective ha]
theorem weight_ker_comap (a : A →+* C) (ha : Function.Surjective a)
    (p : Ideal C) [p.IsPrime] :
    weight (RingHom.ker a) (p.comap a) = weight ⊥ p := by
  let aₚ := Localization.localRingHom (p.comap a) p a rfl
  have hsurj : Function.Surjective aₚ :=
    RingHom.surjective_localRingHom_of_surjective a ha p
  have hcompl : (p.comap a).primeCompl.map a = p.primeCompl :=
    Submonoid.map_comap_eq_of_surjective ha p.primeCompl
  have hker : RingHom.ker aₚ = (RingHom.ker a).map
      (algebraMap A (Localization.AtPrime (p.comap a))) :=
    IsLocalization.ker_map (Localization.AtPrime p) a hcompl
  have h := Ideal.coheight_comap_of_surjective aₚ hsurj
    (⊥ : Ideal (Localization.AtPrime p))
  rw [← RingHom.ker_eq_comap_bot, hker] at h
  unfold weight
  rw [dite_eq_left (show (p.comap a).IsPrime from inferInstance),
    dite_eq_left (show p.IsPrime from inferInstance), Module.length_quotient,
    Module.length_quotient, Ideal.map_bot]
  exact congrArg ENat.toNat h
theorem comap_square (g : A →+* B) (m : C →+* D) (a : A →+* C) (b : B →+* D)
    (h : m.comp a = b.comp g) (p : Ideal D) :
    (p.comap b).comap g = (p.comap m).comap a := by
  rw [Ideal.comap_comap, Ideal.comap_comap, h]
theorem fractionMap_algebraMap [IsDomain B] (g : A →+* B)
    (hg : Function.Injective g) (x : A) :
    IsFractionRing.map hg (algebraMap A (FractionRing A) x) =
      algebraMap B (FractionRing B) (g x) := by
  change IsLocalization.map _ g _ _ = _
  rw [IsLocalization.map_eq]
theorem fraction_finrank_eq [IsDomain A] [IsDomain B] [IsDomain C] [IsDomain D]
    (g : A →+* B) (m : C →+* D) (hg : Function.Injective g) (hm : Function.Injective m)
    (a : A ≃+* C) (b : B ≃+* D) (h : m.comp a.toRingHom = b.toRingHom.comp g) :
    letI := (IsFractionRing.map hg : FractionRing A →+* FractionRing B).toAlgebra
    letI := (IsFractionRing.map hm : FractionRing C →+* FractionRing D).toAlgebra
    Module.finrank (FractionRing A) (FractionRing B) =
      Module.finrank (FractionRing C) (FractionRing D) := by
  let G : FractionRing A →+* FractionRing B := IsFractionRing.map hg
  let M : FractionRing C →+* FractionRing D := IsFractionRing.map hm
  let aK : FractionRing A ≃+* FractionRing C := IsFractionRing.ringEquivOfRingEquiv a
  let bK : FractionRing B ≃+* FractionRing D := IsFractionRing.ringEquivOfRingEquiv b
  let _ := G.toAlgebra
  let _ := M.toAlgebra
  have hsquare : M.comp aK.toRingHom = bK.toRingHom.comp G := by
    apply IsFractionRing.ringHom_ext (A := A)
    intro x
    change M (aK (algebraMap A (FractionRing A) x)) =
      bK (G (algebraMap A (FractionRing A) x))
    simp only [aK, bK, G, M, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
      fractionMap_algebraMap]
    exact congrArg (algebraMap D (FractionRing D)) (RingHom.congr_fun h x)
  exact congrArg Cardinal.toNat (Algebra.rank_eq_of_equiv_equiv aK bK hsquare)
theorem degree_comap (g : A →+* B) (m : C →+* D) (a : A →+* C) (b : B →+* D)
    (ha : Function.Surjective a) (hb : Function.Surjective b)
    (h : m.comp a = b.comp g) (p : Ideal D) [p.IsPrime] :
    degree g (p.comap b) = degree m p := by
  let e := comap_square g m a b h p
  let aq : (A ⧸ (p.comap b).comap g) ≃+* (C ⧸ p.comap m) :=
    RingEquiv.ofBijective (Ideal.quotientMap (p.comap m) a e.le)
      ⟨Ideal.quotientMap_injective' e.ge, Ideal.quotientMap_surjective ha⟩
  let bp : (B ⧸ p.comap b) ≃+* (D ⧸ p) :=
    RingEquiv.ofBijective (Ideal.quotientMap p b le_rfl)
      ⟨Ideal.quotientMap_injective, Ideal.quotientMap_surjective hb⟩
  let gq := Ideal.quotientMap (p.comap b) g le_rfl
  let mq := Ideal.quotientMap p m le_rfl
  have hq : mq.comp aq.toRingHom = bp.toRingHom.comp gq :=
    (Ideal.comp_quotientMap_eq_of_comp_eq h p).symm
  unfold degree
  rw [dite_eq_left (show (p.comap b).IsPrime from inferInstance),
    dite_eq_left (show p.IsPrime from inferInstance)]
  exact fraction_finrank_eq gq mq Ideal.quotientMap_injective Ideal.quotientMap_injective aq bp hq
theorem fibreWeight_ker_comap [IsNoetherianRing B] [IsNoetherianRing D]
    (g : A →+* B) (m : C →+* D) (a : A →+* C) (b : B →+* D)
    (ha : Function.Surjective a) (hb : Function.Surjective b)
    (h : m.comp a = b.comp g) (q : Ideal C) :
    fibreWeight g (RingHom.ker b) (q.comap a) = fibreWeight m ⊥ q := by
  have hb_inj := Ideal.comap_injective_of_surjective b hb
  have ha_inj := Ideal.comap_injective_of_surjective a ha
  have hmem (p : Ideal D) :
      p.comap b ∈ fibrePrimes g (RingHom.ker b) (q.comap a) ↔ p ∈ fibrePrimes m ⊥ q := by
    simp only [fibrePrimes, Finset.mem_filter, Ideal.mem_minimalPrimesFinset,
      minimalPrimes_ker b hb, comap_square g m a b h, ha_inj.eq_iff]
    constructor
    · rintro ⟨⟨p', hp', he⟩, hq⟩
      exact ⟨hb_inj he ▸ hp', hq⟩
    · rintro ⟨hp, hq⟩
      exact ⟨⟨p, hp, rfl⟩, hq⟩
  unfold fibreWeight
  symm
  refine Finset.sum_nbij (Ideal.comap b) (fun p hp => (hmem p).2 hp) hb_inj.injOn ?_ ?_
  · intro P hP
    have hmin : P ∈ (RingHom.ker b).minimalPrimes :=
      Ideal.mem_minimalPrimesFinset.mp (Finset.mem_filter.mp hP).1
    rw [minimalPrimes_ker b hb] at hmin
    obtain ⟨p, _, rfl⟩ := hmin
    exact ⟨p, (hmem p).1 hP, rfl⟩
  · intro p hp
    let _ := fibre_prime (⟨p, hp⟩ : fibrePrimes m ⊥ q)
    rw [weight_ker_comap b hb, degree_comap g m a b ha hb h]
theorem proof : K1_13_6_3_5_5.c2 := by
  intro U V R S _ _ _ _ _ _ g f J I w r s hc Q hQ
  obtain ⟨m, hg, hf⟩ := hc
  change Q ∈ J.minimalPrimes at hQ
  rw [Ideal.minimalPrimes_eq_comap] at hQ
  obtain ⟨p, hp, rfl⟩ := hQ
  let _ := hp.isPrime
  refine ⟨p.comap r.toQuotient, ?_, ?_, ?_⟩
  · change p.comap r.toQuotient ∈ (Ideal.span {w}).minimalPrimes
    rw [← r.ker_eq, minimalPrimes_ker r.toQuotient r.surjective]
    exact ⟨p, hp, rfl⟩
  · have hJ := weight_ker_comap (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective p
    have hw := weight_ker_comap r.toQuotient r.surjective p
    rw [Ideal.mk_ker] at hJ
    rw [r.ker_eq] at hw
    exact hJ.trans hw.symm
  · have hI := fibreWeight_ker_comap g m (Ideal.Quotient.mk J) (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective hg p
    have hw := fibreWeight_ker_comap f m r.toQuotient s.toQuotient
      r.surjective s.surjective hf p
    rw [Ideal.mk_ker] at hI
    rw [s.ker_eq] at hw
    exact hI.trans hw.symm
end
end K1_13_6_3_5_5_2
end
section
namespace K1_13_4_3_1
noncomputable section
open K1_13 K1_13_4 K1_13_4_3
open scoped Polynomial PowerSeries
private def restoreHom {Γ s} (P : PoleData Γ s) (L : ResidueChart P) :
    PhysicalRow →+* Restored :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (Polynomial.mapRingHom (algebraMap Geom GenericSeed)))
    (fun i => i.elim (MvPolynomial.C (Polynomial.C seed)) (restoredJet P L))
theorem restoreHom_C {Γ s} (P : PoleData Γ s) (L : ResidueChart P) (p : Geom[X]) :
    restoreHom P L (MvPolynomial.C p) = MvPolynomial.C (liftX p) := by
  simp [restoreHom, liftX]
def coeffExpansion (a : RawCoeff) : RawCoeff →+* PowerSeries Restored :=
  (PowerSeries.map MvPolynomial.C).comp ((PowerSeries.rescale a).comp expand)
def trueMotion {Γ s} (P : PoleData Γ s) (L : ResidueChart P) :
    PhysicalRow →+* PowerSeries Restored :=
  (PowerSeries.rescale (MvPolynomial.C (liftX P.H ^ 3))).comp
    ((PowerSeries.map (restoreHom P L)).comp (Polynomial.coeToPowerSeries.ringHom.comp seedTaylor))
theorem coeffExpansion_liftX (a : RawCoeff) (p : Geom[X]) :
    coeffExpansion a (liftX p) = PowerSeries.C (MvPolynomial.C (liftX p)) := by
  simp [coeffExpansion, expand_liftX, PowerSeries.map_C]
theorem coeffExpansion_hasse (a : RawCoeff) (p : Geom[X]) (j : ℕ) :
    coeffExpansion a (Polynomial.hasseDeriv j (liftX p)) =
      PowerSeries.C (MvPolynomial.C (Polynomial.hasseDeriv j (liftX p))) := by
  rw [show Polynomial.hasseDeriv j (liftX p) = liftX (Polynomial.hasseDeriv j p) from
    Polynomial.hasseDeriv_map (algebraMap Geom GenericSeed) j p]
  exact coeffExpansion_liftX _ _
def compensation {A : Type*} [CommRing A] (a b c : A) (D : Fin 3 → A)
    (j : Fin 3) : A :=
  if j = 0 then -a ^ 2 * D 0
  else if j = 1 then a * b * D 0 - a ^ 2 * D 1
  else (a * c - b ^ 2) * D 0 + a * b * D 1 - a ^ 2 * D 2
set_option maxHeartbeats 800000 in
theorem motion_lift {Γ s} (P : PoleData Γ s) (L : ResidueChart P) :
    ∃ M : Restored →+* PowerSeries Restored,
      M.comp (restoreHom P L) = trueMotion P L ∧
        M (MvPolynomial.C (liftX P.H)) = PowerSeries.C (MvPolynomial.C (liftX P.H)) := by
  classical
  let H := liftX P.H
  let R := genericResidue L.numerator L.denominator
  choose d hd using fun j : Fin 3 =>
    expand_scaled_sub (H ^ 3) (Polynomial.hasseDeriv j.val R)
  let D : Fin 3 → PowerSeries Restored := fun j => PowerSeries.map MvPolynomial.C (d j)
  let A := fun p : RawCoeff => PowerSeries.C (MvPolynomial.C (σ := Fin 3) p)
  let Δ := compensation (A H) (A (Polynomial.hasseDeriv 1 H))
    (A (Polynomial.hasseDeriv 2 H)) D
  let M := MvPolynomial.eval₂Hom (coeffExpansion (H ^ 3))
    (fun j => PowerSeries.C (MvPolynomial.X j) + Δ j)
  have hres (j : Fin 3) :
      coeffExpansion (H ^ 3) (Polynomial.hasseDeriv j.val R) =
        A (Polynomial.hasseDeriv j.val R) + (A H) ^ 3 * D j := by
    have hj := congrArg (PowerSeries.map (MvPolynomial.C (σ := Fin 3))) (hd j)
    simpa [coeffExpansion, A, D, PowerSeries.map_C] using hj
  have hMC (p : RawCoeff) : M (MvPolynomial.C p) = coeffExpansion (H ^ 3) p := by
    simp only [M, MvPolynomial.eval₂Hom_C]
  have hMX (j : Fin 3) : M (MvPolynomial.X j) = PowerSeries.C (MvPolynomial.X j) + Δ j := by
    simp only [M, MvPolynomial.eval₂Hom_X']
  have hH (j : ℕ) : coeffExpansion (H ^ 3) (Polynomial.hasseDeriv j H) =
      A (Polynomial.hasseDeriv j H) := coeffExpansion_hasse _ P.H j
  have hH₀ : coeffExpansion (H ^ 3) H = A H := coeffExpansion_liftX _ P.H
  have hH₁ : coeffExpansion (H ^ 3) (Polynomial.derivative H) = A (Polynomial.derivative H) := by
    simpa only [Polynomial.hasseDeriv_one'] using hH 1
  refine ⟨M, ?_, ?_⟩
  · apply MvPolynomial.ringHom_ext
    · intro p
      simp only [RingHom.comp_apply, trueMotion, restoreHom_C, hMC, coeffExpansion_liftX,
        seedTaylor_C, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
        PowerSeries.map_C, rescale_const]
    · intro j
      cases j with
      | none =>
        simp only [RingHom.comp_apply, trueMotion, restoreHom, MvPolynomial.eval₂Hom_X',
          Option.elim, hMC, coeffExpansion, expand_seed, seedTaylor_none, map_add, map_mul,
          Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, Polynomial.coe_C,
          PowerSeries.map_C, PowerSeries.map_X, rescale_const, rescale_var]
        exact add_comm _ _
      | some j =>
        have hjet : M (restoredJet P L j) = PowerSeries.C (restoredJet P L j) := by
          simp only [restoredJet, ← show R = genericResidue L.numerator L.denominator from rfl,
            ← show H = liftX P.H from rfl, map_add, map_sum, apply_ite, map_zero, map_mul]
          simp only [hMC, hMX, hres, hH]
          fin_cases j <;>
            norm_num [Fin.sum_univ_three, Δ, compensation, A, hH₀, hH₁,
              Polynomial.hasseDeriv_zero'] <;> ring
        simpa only [RingHom.comp_apply, trueMotion, restoreHom, MvPolynomial.eval₂Hom_X',
          Option.elim, seedTaylor_some, Polynomial.coeToPowerSeries.ringHom_apply,
          Polynomial.coe_C, PowerSeries.map_C, rescale_const] using hjet
  · rw [hMC, coeffExpansion_liftX]
theorem coeff_trueMotion {Γ s} (P : PoleData Γ s) (L : ResidueChart P)
    (i : ℕ) (F : PhysicalRow) :
    PowerSeries.coeff i (trueMotion P L F) = restore P L (clearedSeed P.H i F) := by
  simp only [trueMotion, RingHom.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_map,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe, coeff_seedTaylor]
  change _ = restoreHom P L (clearedSeed P.H i F)
  simp only [clearedSeed, ← partial_eq_mixedHasse, map_mul, restoreHom_C, liftX, map_pow, pow_mul]
theorem pole_seed {Γ s} (P : PoleData Γ s) (L : ResidueChart P)
    (r i : ℕ) (F : PhysicalRow)
    (hF : MvPolynomial.C (liftX P.H) ^ r ∣ restore P L F) :
    MvPolynomial.C (liftX P.H) ^ r ∣ restore P L (clearedSeed P.H i F) := by
  obtain ⟨M, hM, hH⟩ := motion_lift P L
  change MvPolynomial.C (liftX P.H) ^ r ∣ restoreHom P L F at hF
  obtain ⟨Q, hQ⟩ := hF
  refine ⟨PowerSeries.coeff i (M Q), ?_⟩
  rw [← coeff_trueMotion, ← DFunLike.congr_fun hM F]
  change PowerSeries.coeff i (M (restoreHom P L F)) = _
  rw [hQ, map_mul, map_pow, hH, ← map_pow, PowerSeries.coeff_C_mul]
end
end K1_13_4_3_1
end
section
set_option autoImplicit false
namespace K1_13_6_2_3_2_5
noncomputable section
open K1_13_6_2_3_2 MvPolynomial
open scoped BigOperators
variable {ι : Type} [DecidableEq ι]
private def factor (used : List ι) (f : ι → ℕ → ℚ) (i : ι) (a : ℕ) : ℚ :=
  if i ∈ used then f i (a + 1) - f i a else f i a
theorem deltas_prod [Fintype ι] (used : List ι) (hn : used.Nodup)
    (f : ι → ℕ → ℚ) (a : ι → ℕ) :
    deltas used (fun b => ∏ i, f i (b i)) a = ∏ i, factor used f i (a i) := by
  induction used generalizing a with
  | nil => simp [deltas, factor]
  | cons i rest ih =>
    obtain ⟨hi, hr⟩ := List.nodup_cons.mp hn
    let R := ∏ j ∈ Finset.univ.erase i, factor rest f j (a j)
    have same (b : ι → ℕ) (hb : ∀ j ≠ i, b j = a j) :
        (∏ j, factor rest f j (b j)) = R * f i (b i) := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      have hR : (∏ j ∈ Finset.univ.erase i, factor rest f j (b j)) = R :=
        Finset.prod_congr rfl fun j hj => by rw [hb j (Finset.ne_of_mem_erase hj)]
      rw [hR]
      simp [factor, hi]
    have hR : (∏ j ∈ Finset.univ.erase i, factor (i :: rest) f j (a j)) = R := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [factor, List.mem_cons, Finset.ne_of_mem_erase hj]
    simp only [deltas, ih hr]
    rw [same (a + step i) (fun j hj => by simp [step, hj]),
      same a (fun _ _ => rfl), ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), hR]
    simp only [Pi.add_apply, step, Pi.single_eq_same, factor, List.mem_cons, true_or, ite_true]
    ring
theorem deltas_mul (used : List ι) (c : ℚ) (f : (ι → ℕ) → ℚ) (a : ι → ℕ) :
    deltas used (fun b => c * f b) a = c * deltas used f a := by
  induction used generalizing a with
  | nil => rfl
  | cons i rest ih => simp only [deltas, ih, mul_sub]
def differenceEval : List ι → (ι → ℕ) → MvPolynomial ι ℚ →ₗ[ℚ] ℚ
  | [], a => (MvPolynomial.aeval fun i => (a i : ℚ)).toLinearMap
  | i :: rest, a => differenceEval rest (a + step i) - differenceEval rest a
theorem differenceEval_apply (used : List ι) (a : ι → ℕ) (P : MvPolynomial ι ℚ) :
    differenceEval used a P = deltas used (fun b => MvPolynomial.eval (fun i => (b i : ℚ)) P) a := by
  induction used generalizing a with
  | nil => rfl
  | cons i rest ih => simp only [differenceEval, LinearMap.sub_apply, deltas, ih]
theorem difference_monomial [Fintype ι] (used : List ι) (hn : used.Nodup)
    (e : ι →₀ ℕ) (c : ℚ) (hd : e.degree ≤ used.length) (a b : ι → ℕ) :
    differenceEval used a (monomial e c) =
      if e.degree = used.length then differenceEval used b (monomial e c) else 0 := by
  have heval (z : ι → ℕ) :
      MvPolynomial.eval (fun i => (z i : ℚ)) (monomial e c) = c * ∏ i, (z i : ℚ) ^ e i := by
    rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  let f (i : ι) (x : ℕ) : ℚ := (x : ℚ) ^ e i
  have hcalc (z : ι → ℕ) :
      differenceEval used z (monomial e c) = c * ∏ i, factor used f i (z i) := by
    rw [differenceEval_apply]
    simp_rw [heval]
    change deltas used (fun b => c * ∏ i, f i (b i)) z = _
    rw [deltas_mul, deltas_prod used hn f]
  rw [hcalc a, hcalc b]
  by_cases hz : ∃ i ∈ used, e i = 0
  · obtain ⟨i, hi, he⟩ := hz
    have hzero (z : ι → ℕ) : (∏ j, factor used f j (z j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [factor, hi, f, he])
    simp [hzero]
  · let m (i : ι) : ℕ := if i ∈ used then 1 else 0
    have hm : ∑ i, m i = used.length := by
      rw [← List.toFinset_card_of_nodup hn, Finset.card_eq_sum_ite (Finset.subset_univ _)]
      simp [m]
    have hme (i : ι) : m i ≤ e i := by
      by_cases hi : i ∈ used
      · simpa [m, hi] using Nat.one_le_iff_ne_zero.mpr (fun he => hz ⟨i, hi, he⟩)
      · simp [m, hi]
    have heq (i : ι) : e i = m i := by
      by_contra hne
      have hlt : (∑ j, m j) < ∑ j, e j :=
        Finset.sum_lt_sum (fun j _ => hme j) ⟨i, Finset.mem_univ _, lt_of_le_of_ne (hme i) (Ne.symm hne)⟩
      rw [hm, ← Finsupp.degree_eq_sum] at hlt
      exact (not_lt_of_ge hd) hlt
    have he : e.degree = used.length := by
      simp only [Finsupp.degree_eq_sum, heq, hm]
    rw [ite_eq_left he]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ used <;> simp [factor, hi, f, heq i, m]
theorem deltas_top [Fintype ι] (used : List ι) (hn : used.Nodup) (P : MvPolynomial ι ℚ)
    (hd : P.totalDegree ≤ used.length) (a b : ι → ℕ) :
    deltas used (fun z => MvPolynomial.eval (fun i => (z i : ℚ)) P) a =
    deltas used (fun z => MvPolynomial.eval (fun i => (z i : ℚ))
      (homogeneousComponent used.length P)) b := by
  classical
  rw [← differenceEval_apply, ← differenceEval_apply, homogeneousComponent_apply, map_sum,
    Finset.sum_filter]
  conv_lhs => rw [P.as_sum, map_sum]
  apply Finset.sum_congr rfl fun e he => ?_
  exact difference_monomial used hn e _ ((MvPolynomial.le_totalDegree he).trans hd) a b
end
end K1_13_6_2_3_2_5
end
section
set_option autoImplicit false
namespace K1_13_6_2_3_2_5
noncomputable section
open K1_13 K1_13_6 K1_13_6_2_3 K1_13_6_2_3_2 MvPolynomial Filter
variable {ι : Type} [DecidableEq ι]
private theorem deltas_congr_of_ge (used : List ι) {F G : (ι → ℕ) → ℚ} {u : ι → ℕ}
    (h : ∀ a ≥ u, F a = G a) (a : ι → ℕ) (ha : u ≤ a) :
    deltas used F a = deltas used G a := by
  induction used generalizing a with
  | nil => exact h a ha
  | cons i rest ih =>
    simp only [deltas, ih a ha, ih (a + step i) (ha.trans fun j => Nat.le_add_right _ _)]
theorem deltas_polarize [Fintype ι] (shapes : ι → Shape) (base : ι)
    (F : (ι → ℕ) → ℚ) (G : Shape → ℚ)
    (hFG : ∀ v, 0 < v base → F v = G (shapeSum shapes v))
    (used : List ι) (v : ι → ℕ) (hv : 0 < v base) :
    deltas used F v = polarize G (used.map shapes) (shapeSum shapes v) := by
  induction used generalizing v with
  | nil => exact hFG v hv
  | cons i rest ih =>
    have hv' : 0 < (v + step i) base := hv.trans_le (Nat.le_add_right _ _)
    simp only [deltas, List.map_cons, polarize, ih v hv, ih _ hv', shapeSum_add, shapeSum_step]
theorem proof : K1_13_6_2_3_2.c5 := by
  intro ι _ _ shapes J base used hs _ hn hd hfil
  dsimp only
  intro P hP
  obtain ⟨u, hu⟩ := eventually_atTop.mp hP
  have hcompare (v : ι → ℕ) (hv : 0 < v base) :=
    ray_compare shapes J base hs hfil P u hu v hv used.length hd
  have hdegree : P.totalDegree ≤ used.length :=
    (totalDegree_le_of_ray_degree P u (dimension J)
      (fun v hv => (hcompare v (hv base)).1)).trans hd
  let F := fun v : ι → ℕ => MvPolynomial.eval (fun i => (v i : ℚ))
    (homogeneousComponent used.length P)
  have hFG (v : ι → ℕ) (hv : 0 < v base) : F v = capCoeff J used.length (shapeSum shapes v) :=
    (ray_top P u v hdegree).symm.trans (hcompare v hv).2
  filter_upwards [eventually_ge_atTop u] with a ha
  calc
    _ = deltas used (fun v => MvPolynomial.eval (fun i => (v i : ℚ)) P) a :=
      (deltas_congr_of_ge used hu a ha).symm
    _ = deltas used F (step base) := deltas_top used hn P hdegree a (step base)
    _ = polarize (capCoeff J used.length) (used.map shapes) (shapes base) := by
      rw [deltas_polarize shapes base F _ hFG used _ (by simp [step]), shapeSum_step]
end
end K1_13_6_2_3_2_5
end
section
namespace K1_14_2_2_7_3_3_1_2
theorem proof : K1_14_2_2_7_3_3_1.c2 :=
  K1_14_3R_3_1_3_2.proof
end K1_14_2_2_7_3_3_1_2
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_4
noncomputable section
open MvPolynomial K1_13_6_3 K1_13_6_3_5
open scoped BigOperators
variable {k σ τ : Type*} [Field k]
theorem project_homogeneous (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (hφ : IsLinearProjection φ) {n : ℕ} {p : MvPolynomial τ k} (hp : p.IsHomogeneous n) :
    (φ p).IsHomogeneous n := by
  rw [aeval_unique φ]
  simpa only [one_mul, Function.comp_apply] using hp.aeval (φ ∘ MvPolynomial.X) hφ
theorem project_component (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (hφ : IsLinearProjection φ) (n : ℕ) (p : MvPolynomial τ k) :
    φ (homogeneousComponent n p) = homogeneousComponent n (φ p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    have hd : (monomial d c).IsHomogeneous d.degree := isHomogeneous_monomial c rfl
    rw [homogeneousComponent_of_mem hd, homogeneousComponent_of_mem (project_homogeneous φ hφ hd)]
    split_ifs <;> simp
  | add p q hp hq =>
    simp only [map_add, hp, hq]
theorem project_totalDegree_le (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (hφ : IsLinearProjection φ) (p : MvPolynomial τ k) : (φ p).totalDegree ≤ p.totalDegree := by
  calc
    (φ p).totalDegree =
        (∑ n ∈ Finset.range (p.totalDegree + 1), φ (homogeneousComponent n p)).totalDegree := by
      rw [← map_sum, sum_homogeneousComponent]
    _ ≤ p.totalDegree := by
      apply totalDegree_finsetSum_le
      intro n hn
      exact (project_homogeneous φ hφ (homogeneousComponent_isHomogeneous n p)).totalDegree_le.trans
        (Nat.le_of_lt_succ (Finset.mem_range.mp hn))
theorem boundary_le_comap (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (hφ : IsLinearProjection φ) (I : Ideal (MvPolynomial σ k)) :
    boundaryIdeal (I.comap φ) ≤ (boundaryIdeal I).comap φ := by
  apply Ideal.span_le.mpr
  rintro _ ⟨p, hp, rfl⟩
  change φ (homogeneousComponent p.totalDegree p) ∈ boundaryIdeal I
  rw [project_component φ hφ]
  exact component_mem_boundary (show φ p ∈ I from hp) (project_totalDegree_le φ hφ p)
variable [Finite σ] [Finite τ]
theorem birational_dimension (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (A : Ideal (MvPolynomial σ k)) (hA : A.IsPrime) (hb : IsBirationalOn φ A) :
    dimension (A.comap φ) = dimension A := by
  classical
  let _ := Fintype.ofFinite σ
  have : A.IsPrime := hA
  let J := A.comap φ
  let g : (MvPolynomial τ k ⧸ J) →ₐ[k] (MvPolynomial σ k ⧸ A) :=
    Ideal.quotientMapₐ A φ le_rfl
  have hg : Function.Injective g :=
    Ideal.quotientMap_injective (I := A) (f := φ.toRingHom)
  apply le_antisymm (natDegree_affineHilbertPolynomial_le_of_injective g hg)
  choose u v hv huv using fun i : σ ↦ hb (MvPolynomial.X i)
  let t := ∏ i, v i
  let a := Ideal.Quotient.mk J t
  let b := Ideal.Quotient.mk A (φ t)
  have hgb : g a = b := rfl
  have hb0 : b ≠ 0 := by
    change Ideal.Quotient.mk A (φ (∏ i, v i)) ≠ 0
    rw [map_prod, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦
      mt Ideal.Quotient.eq_zero_iff_mem.mp (hv i)
  have hx (i : σ) : ∃ q, g q = b * Ideal.Quotient.mk A (MvPolynomial.X i) := by
    let w := ∏ j ∈ Finset.univ.erase i, v j
    have ht : w * v i = t := Finset.prod_erase_mul _ _ (Finset.mem_univ i)
    have hi : Ideal.Quotient.mk A (φ (u i)) =
        Ideal.Quotient.mk A (φ (v i)) * Ideal.Quotient.mk A (MvPolynomial.X i) := by
      have hz := Ideal.Quotient.eq_zero_iff_mem.mpr (huv i)
      simp only [map_sub, map_mul, sub_eq_zero] at hz
      exact hz.symm.trans (mul_comm _ _)
    refine ⟨Ideal.Quotient.mk J (w * u i), ?_⟩
    change Ideal.Quotient.mk A (φ (w * u i)) =
      Ideal.Quotient.mk A (φ t) * Ideal.Quotient.mk A (MvPolynomial.X i)
    rw [← ht, map_mul, map_mul, map_mul, map_mul, hi, mul_assoc]
  have hrec (p : MvPolynomial σ k) :
      ∃ q m, g q = b ^ m * Ideal.Quotient.mk A p := by
    induction p using MvPolynomial.induction_on with
    | C c =>
      refine ⟨algebraMap k (MvPolynomial τ k ⧸ J) c, 0, ?_⟩
      rw [AlgHom.commutes, pow_zero, one_mul]
      rfl
    | add p r hp hr =>
      obtain ⟨q, m, hq⟩ := hp
      obtain ⟨s, n, hs⟩ := hr
      refine ⟨a ^ n * q + a ^ m * s, m + n, ?_⟩
      simp only [map_add, map_mul, map_pow, hgb, hq, hs, pow_add]
      ring
    | mul_X p i hp =>
      obtain ⟨q, m, hq⟩ := hp
      obtain ⟨s, hs⟩ := hx i
      refine ⟨q * s, m + 1, ?_⟩
      simp only [map_mul, hq, hs, pow_succ]
      ring
  let U := Localization.Away a
  let V := Localization.Away b
  have : IsLocalization.Away (g a) V := by rw [hgb]; infer_instance
  let ψ : U →ₐ[k] V := IsLocalization.Away.mapₐ U V g a
  have hψ : Function.Surjective ψ := by
    apply (IsLocalization.Away.map_surjective_iff U V g.toRingHom a).mpr
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hgb] using hrec p
  exact natDegree_affineHilbertPolynomial_le_of_surjective_away_away
    (s := φ t) (t := t) (IsRegular.of_ne_zero hb0).1 ψ hψ
theorem minimalPrime_of_dimension {I Q : Ideal (MvPolynomial τ k)}
    (hQ : Q.IsPrime) (hIQ : I ≤ Q) (hdim : dimension Q = 2) (hI : dimension I ≤ 2) :
    I.IsMinimalPrime Q := by
  refine ⟨⟨hQ, hIQ⟩, ?_⟩
  intro R hR hRQ
  by_contra hn
  obtain ⟨f, hfQ, hfR⟩ := SetLike.exists_of_lt (lt_of_le_not_ge hRQ hn)
  have hbound := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hR.1 hfR (b := f.totalDegree) le_rfl).1
  have hQle : R ⊔ Ideal.span {f} ≤ Q :=
    sup_le hRQ (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfQ))
  have hle := natDegree_affineHilbertPolynomial_le_of_le hQle
  have hRI : dimension R ≤ dimension I := natDegree_affineHilbertPolynomial_le_of_le hR.2
  have hRbound : dimension R ≤ 2 := hRI.trans hI
  change dimension (R ⊔ Ideal.span {f}) ≤ dimension R - 1 at hbound
  change dimension Q ≤ dimension (R ⊔ Ideal.span {f}) at hle
  omega
theorem proof : K1_13_6_3_5.c4 := by
  intro k σ τ _ _ _ φ hφ A hA hdim hbir
  have hdim' : dimension (A.comap φ) = 2 := (birational_dimension φ A hA hbir).trans hdim
  refine ⟨hdim', ?_⟩
  intro P hP hPd
  have : P.IsPrime := hP.isPrime
  exact minimalPrime_of_dimension (Ideal.IsPrime.comap φ)
    ((boundary_le_comap φ hφ A).trans (Ideal.comap_mono hP.le)) hPd
    ((boundary_dimension_le (A.comap φ)).trans_eq hdim')
end
end K1_13_6_3_5_4
end
section
set_option autoImplicit false
namespace K1_13_6_2_3_3_2_2
noncomputable section
open K1_13_6_2_3_3_2
open scoped BigOperators
variable {k m : ℕ}
private def limit (bad : Finset (Fin m →₀ ℕ)) (j : Fin m) : ℕ :=
  ∑ b ∈ bad, b j
theorem le_limit {bad : Finset (Fin m →₀ ℕ)} {b : Fin m →₀ ℕ}
    (hb : b ∈ bad) (j : Fin m) : b j ≤ limit bad j :=
  Finset.single_le_sum (f := fun b => b j) (fun _ _ => Nat.zero_le _) hb
private def threshold (bad : Finset (Fin m →₀ ℕ)) : ℕ :=
  (∑ j, limit bad j) + 1
private abbrev Vars (slot : Fin m → Fin k) (i : Fin k) := {j : Fin m // slot j = i}
theorem sum_vars (slot : Fin m → Fin k) (i : Fin k) (a : Fin m → ℕ) :
    (∑ j : Vars slot i, a j.val) = ∑ j ∈ Finset.univ.filter (fun j => slot j = i), a j :=
  (Finset.sum_subtype _ (by simp) a).symm
abbrev Standard (slot : Fin m → Fin k) (bad : Finset (Fin m →₀ ℕ))
    (w : Fin k → ℕ) :=
  {e : Fin m →₀ ℕ // (∀ b ∈ bad, ¬ b ≤ e) ∧
    ∀ i, ∑ j ∈ Finset.univ.filter (fun j => slot j = i), e j = w i}
private abbrev Cell (slot : Fin m → Fin k) (bad : Finset (Fin m →₀ ℕ)) :=
  {c : ∀ j, Fin (limit bad j + 1) //
    (∀ b ∈ bad, ¬ ∀ j, b j ≤ (c j).val) ∧
    ∀ i, ∃ j : Vars slot i, (c j.val).val = limit bad j.val}
private abbrev Fibre (slot : Fin m → Fin k) (bad : Finset (Fin m →₀ ℕ))
    (c : Cell slot bad) (i : Fin k) (n : ℕ) :=
  {a : Vars slot i → ℕ //
    (∀ j, min (a j) (limit bad j.val) = (c.val j.val).val) ∧ ∑ j, a j = n}
private instance fibreFinite (slot : Fin m → Fin k) (bad : Finset (Fin m →₀ ℕ))
    (c : Cell slot bad) (i : Fin k) (n : ℕ) : Finite (Fibre slot bad c i n) := by
  classical
  let encode (a : Fibre slot bad c i n) (j : Vars slot i) : Fin (n + 1) :=
    ⟨a.val j, Nat.lt_succ_of_le (by
      calc
        a.val j ≤ ∑ l, a.val l :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
        _ = n := a.property.2)⟩
  apply Finite.of_injective encode
  intro a b hab
  apply Subtype.ext
  funext j
  exact congrArg (fun f : Vars slot i → Fin (n + 1) => (f j).val) hab
theorem fibre_monotone (slot : Fin m → Fin k) (bad : Finset (Fin m →₀ ℕ))
    (c : Cell slot bad) (i : Fin k) :
    Monotone (fun n => Nat.card (Fibre slot bad c i n)) := by
  classical
  intro p q hpq
  obtain ⟨j, hj⟩ := c.property.2 i
  let lift (a : Fibre slot bad c i p) : Fibre slot bad c i q :=
    ⟨Function.update a.val j (a.val j + (q - p)), by
      constructor
      · intro l
        by_cases h : l = j
        · subst l
          rw [Function.update_self, hj]
          have ha := a.property.1 j
          rw [hj] at ha
          have hle : limit bad j.val ≤ a.val j := ha.symm.trans_le (min_le_left _ _)
          exact min_eq_right (hle.trans (Nat.le_add_right _ _))
        · rw [Function.update_of_ne h]
          exact a.property.1 l
      · have hsum := Finset.sum_update_of_mem (Finset.mem_univ j) a.val (a.val j)
        rw [Function.update_eq_self, a.property.2] at hsum
        rw [Finset.sum_update_of_mem (Finset.mem_univ j)]
        omega⟩
  apply Nat.card_le_card_of_injective lift
  intro a b hab
  apply Subtype.ext
  funext l
  have he := congrArg (fun f : Fibre slot bad c i q => f.val l) hab
  change Function.update a.val j (a.val j + (q - p)) l =
    Function.update b.val j (b.val j + (q - p)) l at he
  by_cases hl : l = j
  · subst l
    simp only [Function.update_self] at he
    exact Nat.add_right_cancel he
  · simpa only [Function.update_of_ne hl] using he
private def clip {slot : Fin m → Fin k} {bad : Finset (Fin m →₀ ℕ)} {w : Fin k → ℕ}
    (hw : ∀ i, threshold bad ≤ w i) (e : Standard slot bad w) : Cell slot bad := by
  classical
  refine ⟨fun j => ⟨min (e.val j) (limit bad j),
    Nat.lt_succ_of_le (min_le_right _ _)⟩, ?_, ?_⟩
  · intro b hb h
    exact e.property.1 b hb (Finsupp.le_def.mpr (fun j => (h j).trans (min_le_left _ _)))
  · intro i
    by_contra h
    have hle (j : Fin m) (hj : j ∈ Finset.univ.filter (fun j => slot j = i)) :
        e.val j ≤ limit bad j := by
      by_contra hlt
      have hge : limit bad j ≤ e.val j := (Nat.lt_of_not_ge hlt).le
      exact h ⟨⟨j, (Finset.mem_filter.mp hj).2⟩, min_eq_right hge⟩
    have hweight : w i ≤ ∑ j, limit bad j := calc
      w i = ∑ j ∈ Finset.univ.filter (fun j => slot j = i), e.val j := (e.property.2 i).symm
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j => slot j = i), limit bad j := Finset.sum_le_sum hle
      _ ≤ ∑ j, limit bad j := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    exact (Nat.not_succ_le_self _) ((hw i).trans hweight)
def join {slot : Fin m → Fin k} {bad : Finset (Fin m →₀ ℕ)} (w : Fin k → ℕ)
    (x : Σ c : Cell slot bad, ∀ i, Fibre slot bad c i (w i)) : Standard slot bad w := by
  let ex (j : Fin m) : ℕ := (x.2 (slot j)).val ⟨j, rfl⟩
  refine ⟨Finsupp.equivFunOnFinite.symm ex, ?_, ?_⟩
  · intro b hb he
    apply x.1.property.1 b hb
    intro j
    rw [← (x.2 (slot j)).property.1 ⟨j, rfl⟩]
    exact le_min (Finsupp.le_def.mp he j) (le_limit hb j)
  · intro i
    change ∑ j ∈ Finset.univ.filter (fun j => slot j = i), ex j = w i
    rw [← sum_vars slot i ex, ← (x.2 i).property.2]
    apply Finset.sum_congr rfl
    intro j _
    obtain ⟨j, hj⟩ := j
    subst i
    rfl
theorem join_bijective {slot : Fin m → Fin k} {bad : Finset (Fin m →₀ ℕ)}
    {w : Fin k → ℕ} (hw : ∀ i, threshold bad ≤ w i) :
    Function.Bijective (join (slot := slot) (bad := bad) w) := by
  constructor
  · rintro ⟨c, x⟩ ⟨d, y⟩ h
    have he (j : Fin m) : (x (slot j)).val ⟨j, rfl⟩ = (y (slot j)).val ⟨j, rfl⟩ :=
      congrArg (fun e : Standard slot bad w => e.val j) h
    have hc : c = d := by
      apply Subtype.ext
      funext j
      apply Fin.ext
      exact ((x (slot j)).property.1 ⟨j, rfl⟩).symm.trans
        ((congrArg (fun a => min a (limit bad j)) (he j)).trans
          ((y (slot j)).property.1 ⟨j, rfl⟩))
    subst d
    apply congrArg (Sigma.mk c)
    funext i
    apply Subtype.ext
    funext j
    obtain ⟨j, hj⟩ := j
    subst i
    exact he j
  · intro e
    let c := clip hw e
    refine ⟨⟨c, fun i => ⟨fun j => e.val j.val, ?_, ?_⟩⟩, ?_⟩
    · intro j
      rfl
    · rw [sum_vars slot i (fun j => e.val j)]
      exact e.property.2 i
    · apply Subtype.ext
      apply Finsupp.ext
      intro j
      rfl
theorem proof : K1_13_6_2_3_3_2.c2 := by
  classical
  intro k m slot bad
  let : Fintype (Cell slot bad) := Fintype.ofFinite _
  let e := (Fintype.equivFin (Cell slot bad)).symm
  refine ⟨threshold bad, Fintype.card (Cell slot bad),
    fun a i n => (Nat.card (Fibre slot bad (e a) i n) : ℚ), ?_, ?_, ?_⟩
  · intro a i p q hpq
    exact Nat.cast_le.mpr (fibre_monotone slot bad (e a) i hpq)
  · intro a i n
    exact Nat.cast_nonneg _
  · intro w hw
    have h := Nat.card_eq_of_bijective (join (slot := slot) (bad := bad) w) (join_bijective hw)
    change Nat.card (Σ c : Cell slot bad, ∀ i, Fibre slot bad c i (w i)) =
      standardCount slot bad w at h
    rw [← h, Nat.card_sigma]
    simp only [Nat.card_pi, Nat.cast_sum, Nat.cast_prod]
    apply Fintype.sum_equiv e.symm
    intro c
    rw [e.apply_symm_apply]
end
end K1_13_6_2_3_3_2_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_2_5_2_1_2
open K1_13_5_4_2 K1_13_5_4_2_5_2_1 MeasureTheory
open scoped BigOperators
theorem faceCenter_le {α : Type} {v : α → ExponentSpace} {S T : Finset α}
    {f : ExponentSpace →ₗ[ℝ] ℝ} (hf : Exposes v S f) {a : α} (ha : a ∈ S)
    (hT : T.Nonempty) : f (faceCenter v T) ≤ f (v a) := by
  by_cases hsub : T ⊆ S
  · exact (faceCenter_expose_eq hf ha hT hsub).le
  · exact (faceCenter_expose_lt hf ha hsub).le
theorem sum_gaps_eq {ι : Type} [Fintype ι] {x y : ι → ExponentSpace}
    {w u : ι → ℝ} (hmass : ∑ i, w i = ∑ i, u i)
    (hsum : ∑ i, w i • x i = ∑ i, u i • y i)
    (f : ExponentSpace →ₗ[ℝ] ℝ) (m : ℝ) :
    ∑ i, w i * (m - f (x i)) = ∑ i, u i * (m - f (y i)) := by
  have hf := congrArg f hsum
  simp only [map_sum, map_smul, smul_eq_mul] at hf
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, hf]
theorem centers_subset {α ι : Type} [Fintype ι] {v : α → ExponentSpace}
    {F G : ι → Finset α} {S : Finset α} (hS : IsFaceLabels v S)
    (hF : ∀ i, (F i).Nonempty) (hsub : ∀ i, F i ⊆ S) (hG : ∀ i, (G i).Nonempty)
    {w u : ι → ℝ} (hu : ∀ i, 0 < u i)
    (hmass : ∑ i, w i = ∑ i, u i)
    (hsum : ∑ i, w i • faceCenter v (F i) = ∑ i, u i • faceCenter v (G i)) :
    ∀ i, G i ⊆ S := by
  obtain ⟨a, ha⟩ := hS.1
  obtain ⟨f, hf⟩ := hS.2
  have he := sum_gaps_eq hmass hsum f (f (v a))
  have hzero : ∑ i, w i * (f (v a) - f (faceCenter v (F i))) = 0 :=
    Finset.sum_eq_zero fun i _ => by
      rw [faceCenter_expose_eq hf ha (hF i) (hsub i), sub_self, mul_zero]
  rw [hzero] at he
  have hg := (Fintype.sum_eq_zero_iff_of_nonneg (fun i =>
    mul_nonneg (hu i).le (sub_nonneg.mpr (faceCenter_le hf ha (hG i))))).mp he.symm
  intro i
  by_contra h
  exact (mul_pos (hu i) (sub_pos.mpr (faceCenter_expose_lt hf ha h))).ne' (congrFun hg i)
theorem last_face_eq {α : Type} {v : α → ExponentSpace} {n : ℕ}
    {F G : Fin (n + 1) → Finset α}
    (hF : Monotone F) (hG : Monotone G)
    (hfaceF : ∀ i, IsFaceLabels v (F i)) (hfaceG : ∀ i, IsFaceLabels v (G i))
    {w u : Fin (n + 1) → ℝ} (hw : ∀ i, 0 < w i) (hu : ∀ i, 0 < u i)
    (hmass : ∑ i, w i = ∑ i, u i)
    (hsum : ∑ i, w i • faceCenter v (F i) = ∑ i, u i • faceCenter v (G i)) :
    F (Fin.last n) = G (Fin.last n) := by
  apply Finset.Subset.antisymm
  · exact centers_subset (hfaceG _) (fun i => (hfaceG i).1)
      (fun i => hG (Fin.le_last i)) (fun i => (hfaceF i).1) hw hmass.symm hsum.symm _
  · exact centers_subset (hfaceF _) (fun i => (hfaceF i).1)
      (fun i => hF (Fin.le_last i)) (fun i => (hfaceG i).1) hu hmass hsum _
theorem last_weight_le {α : Type} {v : α → ExponentSpace} {n : ℕ}
    {F G : Fin (n + 2) → Finset α}
    (hF : StrictMono F)
    (hfaceF : ∀ i, IsFaceLabels v (F i)) (hfaceG : ∀ i, IsFaceLabels v (G i))
    (htop : F (Fin.last (n + 1)) = G (Fin.last (n + 1)))
    {w u : Fin (n + 2) → ℝ} (hu : ∀ i, 0 < u i)
    (hmass : ∑ i, w i = ∑ i, u i)
    (hsum : ∑ i, w i • faceCenter v (F i) = ∑ i, u i • faceCenter v (G i)) :
    u (Fin.last (n + 1)) ≤ w (Fin.last (n + 1)) := by
  let p : Fin (n + 2) := (Fin.last n).castSucc
  obtain ⟨a, ha⟩ := (hfaceF p).1
  obtain ⟨f, hf⟩ := (hfaceF p).2
  let gap (T : Finset α) : ℝ := f (v a) - f (faceCenter v T)
  have he : (∑ i, w i * gap (F i)) = ∑ i, u i * gap (G i) :=
    sum_gaps_eq hmass hsum f (f (v a))
  have hzero : ∑ i : Fin (n + 1), w i.castSucc * gap (F i.castSucc) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : i.castSucc ≤ p := Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last i)
    simp only [gap, faceCenter_expose_eq hf ha (hfaceF _).1 (hF.monotone hi), sub_self, mul_zero]
  have hnonneg : 0 ≤ ∑ i : Fin (n + 1), u i.castSucc * gap (G i.castSucc) :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (hu _).le (sub_nonneg.mpr (faceCenter_le hf ha (hfaceG _).1))
  have hpos : 0 < gap (F (Fin.last (n + 1))) :=
    sub_pos.mpr (faceCenter_expose_lt hf ha
      (not_le_of_gt (hF (Fin.castSucc_lt_last (Fin.last n)))))
  rw [Fin.sum_univ_castSucc (n := n + 1), Fin.sum_univ_castSucc (n := n + 1),
    hzero, zero_add, ← htop] at he
  apply le_of_mul_le_mul_right _ hpos
  rw [he]
  exact le_add_of_nonneg_left hnonneg
theorem chain_eq {α : Type} {v : α → ExponentSpace} {n : ℕ}
    {F G : Fin (n + 1) → Finset α}
    (hF : StrictMono F) (hG : StrictMono G)
    (hfaceF : ∀ i, IsFaceLabels v (F i)) (hfaceG : ∀ i, IsFaceLabels v (G i))
    {w u : Fin (n + 1) → ℝ} (hw : ∀ i, 0 < w i) (hu : ∀ i, 0 < u i)
    (hmass : ∑ i, w i = ∑ i, u i)
    (hsum : ∑ i, w i • faceCenter v (F i) = ∑ i, u i • faceCenter v (G i)) : F = G := by
  induction n with
  | zero =>
    have htop := last_face_eq hF.monotone hG.monotone hfaceF hfaceG hw hu hmass hsum
    funext i
    exact Fin.lastCases htop (fun j => Fin.elim0 j) i
  | succ n ih =>
    have htop := last_face_eq hF.monotone hG.monotone hfaceF hfaceG hw hu hmass hsum
    have hlast : w (Fin.last (n + 1)) = u (Fin.last (n + 1)) :=
      le_antisymm (last_weight_le hG hfaceG hfaceF htop.symm hw hmass.symm hsum.symm)
        (last_weight_le hF hfaceF hfaceG htop hu hmass hsum)
    have hpre := ih
      (F := fun i => F i.castSucc) (G := fun i => G i.castSucc)
      (w := fun i => w i.castSucc) (u := fun i => u i.castSucc)
      (fun _ _ hij => hF (Fin.castSucc_lt_castSucc_iff.mpr hij))
      (fun _ _ hij => hG (Fin.castSucc_lt_castSucc_iff.mpr hij))
      (fun i => hfaceF i.castSucc) (fun i => hfaceG i.castSucc)
      (fun i => hw i.castSucc) (fun i => hu i.castSucc)
      (by
        rw [Fin.sum_univ_castSucc (n := n + 1), Fin.sum_univ_castSucc (n := n + 1),
          hlast] at hmass
        exact add_right_cancel hmass)
      (by
        rw [Fin.sum_univ_castSucc (n := n + 1), Fin.sum_univ_castSucc (n := n + 1),
          hlast, htop] at hsum
        exact add_right_cancel hsum)
    funext i
    exact Fin.lastCases htop (congrFun hpre) i
theorem interior_weights {α : Type} [Fintype α] {v : α → ExponentSpace}
    {F : Fin 5 → Finset α} (hF : F ∈ flags v) {x : ExponentSpace}
    (hx : x ∈ interior (flagSimplex v F)) :
    ∃ w : Fin 5 → ℝ, (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
      ∑ i, w i • faceCenter v (F i) = x := by
  have hi := flag_affineIndependent v F hF
  have htop := hi.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)
  let b : AffineBasis (Fin 5) ℝ ExponentSpace :=
    ⟨fun i => faceCenter v (F i), hi, htop⟩
  change x ∈ interior (convexHull ℝ (Set.range b)) at hx
  rw [b.interior_convexHull] at hx
  exact ⟨fun i => b.coord i x, hx, b.sum_coord_apply_eq_one x, b.linear_combination_coord_eq_self x⟩
theorem proof : K1_13_5_4_2_5_2_1.c2 := by
  intro α _ v F hF G hG hne
  change F ∈ flags v at hF
  change G ∈ flags v at hG
  obtain ⟨hmonoF, hfaceF⟩ := (mem_flags v F).mp hF
  obtain ⟨hmonoG, hfaceG⟩ := (mem_flags v G).mp hG
  have hinterior {x : ExponentSpace} (hx : x ∈ interior (flagSimplex v F))
      (hy : x ∈ interior (flagSimplex v G)) : False := by
    obtain ⟨w, hw, hmassF, hsumF⟩ := interior_weights hF hx
    obtain ⟨u, hu, hmassG, hsumG⟩ := interior_weights hG hy
    exact hne (chain_eq hmonoF hmonoG hfaceF hfaceG hw hu
      (hmassF.trans hmassG.symm) (hsumF.trans hsumG.symm))
  unfold AEDisjoint
  refine measure_mono_null
    (t := frontier (flagSimplex v F) ∪ frontier (flagSimplex v G)) ?_ ?_
  · intro x hx
    by_cases h : x ∈ interior (flagSimplex v F)
    · exact Or.inr ((mem_frontier_iff_notMem_interior hx.2).mpr (hinterior h))
    · exact Or.inl ((mem_frontier_iff_notMem_interior hx.1).mpr h)
  · exact measure_union_null ((convex_convexHull ℝ _).addHaar_frontier volume)
      ((convex_convexHull ℝ _).addHaar_frontier volume)
end K1_13_5_4_2_5_2_1_2
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_3_3_1
noncomputable section
open K1_13_6_3_5_3 Polynomial
open scoped WithZero
theorem constants_value {k L : Type*} [Field k] [Field L] [Algebra k L]
    (V : ValuationSubring L) (hV : ∀ c : k, algebraMap k L c ∈ V)
    (c : k) (hc : c ≠ 0) : V.valuation (algebraMap k L c) = 1 := by
  have hle := (V.valuation_le_one_iff _).2 (hV c)
  have hinv : (algebraMap k L c)⁻¹ ∈ V := by
    rw [← map_inv₀]
    exact hV c⁻¹
  have hge := (V.valuation.one_le_val_iff ((_root_.map_ne_zero (algebraMap k L)).2 hc)).2
    ((V.valuation_le_one_iff _).2 hinv)
  exact le_antisymm hle hge
theorem linear_values {k L Γ : Type*} [Field k] [Field L] [Algebra k L]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ)
    (hc : ∀ c : k, c ≠ 0 → v (algebraMap k L c) = 1)
    {t : L} (ht : Transcendental k t) :
    ∃ g : Γ, g ≠ 0 ∧ ∀ a : k, ∃ n : ℤ, v (t - algebraMap k L a) = g ^ n := by
  have hline (a : k) : t - algebraMap k L a ≠ 0 := by
    intro ha
    exact ht ⟨Polynomial.X - C a, X_sub_C_ne_zero a, by simpa using ha⟩
  have hconst (a : k) : v (algebraMap k L a) ≤ 1 := by
    by_cases ha : a = 0
    · simp [ha]
    · exact (hc a ha).le
  by_cases hhigh : 1 < v t
  · refine ⟨v t, v.ne_zero_iff.mpr ht.ne_zero, fun a => ⟨1, ?_⟩⟩
    rw [zpow_one]
    exact v.map_sub_eq_of_lt_left ((hconst a).trans_lt hhigh)
  have hle (a : k) : v (t - algebraMap k L a) ≤ 1 :=
    v.map_sub_le (le_of_not_gt hhigh) (hconst a)
  by_cases hlow : ∃ a : k, v (t - algebraMap k L a) < 1
  · obtain ⟨a, ha⟩ := hlow
    refine ⟨v (t - algebraMap k L a), v.ne_zero_iff.mpr (hline a), fun b => ?_⟩
    by_cases hab : b = a
    · subst b
      exact ⟨1, by rw [zpow_one]⟩
    refine ⟨0, ?_⟩
    rw [zpow_zero]
    apply le_antisymm (hle b)
    by_contra! hb
    have hdiff : (t - algebraMap k L a) - (t - algebraMap k L b) =
        algebraMap k L (b - a) := by rw [map_sub]; ring
    have hlt := v.map_sub_lt ha hb
    rw [hdiff, hc _ (sub_ne_zero.mpr hab)] at hlt
    exact (lt_irrefl 1) hlt
  · refine ⟨1, one_ne_zero, fun a => ⟨0, ?_⟩⟩
    rw [zpow_zero]
    exact le_antisymm (hle a) (le_of_not_gt fun ha => hlow ⟨a, ha⟩)
theorem adjoin_values {k L Γ : Type*} [Field k] [IsAlgClosed k]
    [Field L] [Algebra k L] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) (hc : ∀ c : k, c ≠ 0 → v (algebraMap k L c) = 1)
    {t : L} (ht : Transcendental k t) :
    ∃ g : Γ, g ≠ 0 ∧ ∀ y : IntermediateField.adjoin k {t}, y ≠ 0 →
      ∃ n : ℤ, v (y : L) = g ^ n := by
  obtain ⟨g, hg, hlin⟩ := linear_values v hc ht
  have hprod (m : Multiset k) :
      ∃ n : ℤ, v (aeval t (m.map (fun a => Polynomial.X - C a)).prod) = g ^ n := by
    induction m using Multiset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | cons a m ih =>
      obtain ⟨i, hi⟩ := hlin a
      obtain ⟨j, hj⟩ := ih
      refine ⟨i + j, ?_⟩
      rw [Multiset.map_cons, Multiset.prod_cons, map_mul, map_mul, hj,
        map_sub, aeval_X, aeval_C, hi, zpow_add₀ hg]
  have hpoly (p : k[X]) (hp : p ≠ 0) : ∃ n : ℤ, v (aeval t p) = g ^ n := by
    obtain ⟨n, hn⟩ := hprod p.roots
    refine ⟨n, ?_⟩
    conv_lhs => rw [(IsAlgClosed.splits p).eq_prod_roots]
    rw [map_mul, aeval_C, map_mul, hc _ (leadingCoeff_ne_zero.mpr hp), one_mul, hn]
  refine ⟨g, hg, fun y hy => ?_⟩
  let e := RatFunc.algEquivOfTranscendental t ht
  obtain ⟨r, rfl⟩ := e.surjective y
  have hr : r ≠ 0 := fun h => hy (h ▸ e.map_zero)
  obtain ⟨i, hi⟩ := hpoly r.num (RatFunc.num_ne_zero hr)
  obtain ⟨j, hj⟩ := hpoly r.denom r.denom_ne_zero
  exact ⟨i - j, by rw [RatFunc.algEquivOfTranscendental_apply, map_div₀, hi, hj,
    zpow_sub₀ hg]⟩
theorem two_terms {L Γ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) (s : Finset ℕ) (f : ℕ → L)
    (hsum : ∑ i ∈ s, f i = 0) (hpos : ∃ i ∈ s, v (f i) ≠ 0) :
    ∃ i ∈ s, ∃ j ∈ s, i < j ∧ v (f i) = v (f j) ∧ v (f j) ≠ 0 := by
  obtain ⟨a, ha, ha0⟩ := hpos
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image s (fun j => v (f j)) ⟨a, ha⟩
  have ha' : 0 < v (f a) := v.pos_iff.mpr (v.ne_zero_iff.mp ha0)
  have hi0 : v (f i) ≠ 0 := (ha'.trans_le (hmax a ha)).ne'
  have hother : ∃ j ∈ s, j ≠ i ∧ v (f j) = v (f i) := by
    by_contra! h
    have heq := v.map_sum_eq_of_lt hi (f := f) (fun j hj => by
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
      exact lt_of_le_of_ne (hmax j hj.1) (h j hj.1 hj.2))
    rw [hsum, map_zero] at heq
    exact hi0 heq.symm
  obtain ⟨j, hj, hji, heq⟩ := hother
  rcases lt_or_gt_of_ne hji with hlt | hlt
  · exact ⟨j, hj, i, hi, hlt, heq, hi0⟩
  · exact ⟨i, hi, j, hj, hlt, heq.symm, heq.trans_ne hi0⟩
theorem value_pow_factorial {F L Γ : Type*} [Field F] [Field L] [Algebra F L]
    [Module.Finite F L] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) {x : L} (hx : x ≠ 0) :
    ∃ y : F, y ≠ 0 ∧ v x ^ (Module.finrank F L).factorial = v (algebraMap F L y) := by
  let p := minpoly F x
  let f : ℕ → L := fun i => algebraMap F L (p.coeff i) * x ^ i
  have hp : p.Monic := minpoly.monic (IsIntegral.of_finite F x)
  have hxv := v.ne_zero_iff.mpr hx
  have hsum : ∑ i ∈ Finset.range (p.natDegree + 1), f i = 0 := by
    simpa only [aeval_eq_sum_range, Algebra.smul_def] using minpoly.aeval F x
  have htop : ∃ i ∈ Finset.range (p.natDegree + 1), v (f i) ≠ 0 := by
    refine ⟨p.natDegree, Finset.mem_range.mpr (Nat.lt_succ_self _), ?_⟩
    simp [f, hp.coeff_natDegree, hxv]
  obtain ⟨i, _, j, hj, hij, heq, hj0⟩ := two_terms v _ f hsum htop
  simp only [f, map_mul, map_pow] at heq hj0
  have hjc : v (algebraMap F L (p.coeff j)) ≠ 0 := fun hz => hj0 (by rw [hz, zero_mul])
  have hic : v (algebraMap F L (p.coeff i)) ≠ 0 := fun hz => hj0 (by rw [← heq, hz, zero_mul])
  have hpow : v x ^ (j - i) = v (algebraMap F L (p.coeff i / p.coeff j)) := by
    rw [pow_sub₀ _ hxv hij.le, ← div_eq_mul_inv, map_div₀, map_div₀]
    exact (div_eq_div_iff (pow_ne_zero _ hxv) hjc).2 (by simpa only [mul_comm] using heq.symm)
  have hdeg : j - i ≤ Module.finrank F L :=
    (Nat.sub_le _ _).trans ((Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans (minpoly.natDegree_le x))
  obtain ⟨m, hm⟩ := Nat.dvd_factorial (Nat.sub_pos_of_lt hij) hdeg
  have hcoeff (a : F) (ha : v (algebraMap F L a) ≠ 0) : a ≠ 0 :=
    fun hz => ha (by rw [hz, map_zero, map_zero])
  refine ⟨(p.coeff i / p.coeff j) ^ m, pow_ne_zero _ (div_ne_zero (hcoeff _ hic)
    (hcoeff _ hjc)), ?_⟩
  rw [hm, pow_mul, hpow, map_pow, map_pow]
theorem cyclic_of_curve {k L Γ : Type*} [Field k] [IsAlgClosed k]
    [Field L] [Algebra k L] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) (hv : Function.Surjective v)
    (hc : ∀ c : k, c ≠ 0 → v (algebraMap k L c) = 1)
    {t : L} (ht : Transcendental k t)
    [Module.Finite (IntermediateField.adjoin k {t}) L] : IsCyclic Γˣ := by
  let F := IntermediateField.adjoin k {t}
  let N := (Module.finrank F L).factorial
  obtain ⟨g, hg, hbase⟩ := adjoin_values v hc ht
  let G := Subgroup.zpowers (Units.mk0 g hg)
  have hmem (u : Γˣ) : u ^ N ∈ G := by
    obtain ⟨x, hx⟩ := hv (u : Γ)
    have hx0 : x ≠ 0 := v.ne_zero_iff.mp (hx ▸ Units.ne_zero u)
    obtain ⟨y, hy, hyval⟩ := value_pow_factorial (F := F) v hx0
    obtain ⟨n, hn⟩ := hbase y hy
    have hp : (u : Γ) ^ N = g ^ n := by
      rw [← hx, show v x ^ N = v (algebraMap F L y) from hyval]
      exact hn
    refine ⟨n, Units.ext ?_⟩
    rw [Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, Units.val_mk0, hp]
  exact isCyclic_of_injective ((powMonoidHom N).codRestrict G hmem)
    ((MonoidHom.injective_codRestrict _ _ _).2
      (pow_left_strictMono (Nat.factorial_ne_zero (Module.finrank F L))).injective)
theorem proof : K1_13_6_3_5_3_3.c1 := by
  intro k L _ _ _ _ hL V hproper hconst
  obtain ⟨t, ht, hfin⟩ := hL
  let := hfin
  let v := V.valuation
  have hnontriv : v.IsNontrivial := by
    by_contra h
    apply hproper
    simpa only [v, ValuationSubring.valuationSubring_valuation] using
      (Valuation.valuationSubring_eq_top_iff v).2 h
  let : IsCyclic V.ValueGroupˣ := cyclic_of_curve v V.valuation_surjective
    (constants_value V hconst) ht
  let : v.IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' v
  let e := Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v
  let w := v.restrict.map (.ofClass e) e.toOrderIso.monotone
  have hw (x : L) : w x = e (v.restrict x) := rfl
  have hsurj : Function.Surjective v.restrict :=
    MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective (.ofClass v)
  refine ⟨⟨w, e.surjective.comp hsurj, fun c hc => ?_⟩, ?_⟩
  · rw [hw, v.restrict_eq_one_iff.mpr (constants_value V hconst c hc), map_one]
  · ext x
    rw [Valuation.mem_valuationSubring_iff, hw, ← map_one e]
    change e.toOrderIso (v.restrict x) ≤ e.toOrderIso 1 ↔ x ∈ V
    rw [e.toOrderIso.le_iff_le, v.restrict_le_one_iff]
    exact V.valuation_le_one_iff x
end
end K1_13_6_3_5_3_3_1
end
section
namespace K1_13_6_2_2_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_2 MvPolynomial
open scoped Polynomial
theorem quotient_rule (g : Row 4) (n : ℕ) (a : Chart g) :
    S g * D g (S g ^ n * a) - (n : Chart g) * D g (S g) * (S g ^ n * a) =
      S g ^ (n + 1) * D g a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' (S g) n, pow_succ' (S g) (n+1), mul_assoc (S g) (S g ^ n) a,
      D_mul, Nat.cast_succ]
    linear_combination S g * ih
theorem old_numerator (g : Row 4) (n : ℕ) :
    incl g (jetNumerator g n) = S g ^ (2*n) * (D g)^[n] (incl g (MvPolynomial.X 0)) := by
  induction n with
  | zero => simp [jetNumerator]
  | succ n ih =>
    rw [jetNumerator, clearedStep, map_sub, map_mul, map_mul, map_mul, map_natCast,
      ← D_incl, ← D_incl, ih, Function.iterate_succ_apply',
      show 2*(n+1) = (2*n+1)+1 by omega]
    let a := (D g)^[n] (incl g (MvPolynomial.X 0))
    change S g * (S g * D g (S g ^ (2*n) * a)) -
      (↑(2*n) : Chart g) * (S g * D g (S g)) * (S g ^ (2*n) * a) =
        S g ^ ((2*n+1)+1) * D g a
    calc
      _ = S g * (S g * D g (S g ^ (2*n) * a) -
          (↑(2*n) : Chart g) * D g (S g) * (S g ^ (2*n) * a)) := by ring
      _ = _ := by rw [quotient_rule, pow_succ' (S g) (2*n+1), mul_assoc]
theorem lifted_numerator (g : Row 4) (n : ℕ) :
    graphMap g (numerator g n) = S g ^ n * (D g)^[n] (24 * W g) := by
  induction n with
  | zero =>
    rw [numerator, map_mul, graphMap_X_last, graphMap_C, map_ofNat, pow_zero, one_mul,
      Function.iterate_zero_apply]
  | succ n ih =>
    rw [numerator, lifted_step, ih, Function.iterate_succ_apply', quotient_rule]
theorem iterate_four (g : Row 4) : (D g)^[4] (incl g (MvPolynomial.X 0)) = 24 * W g := by
  have h0 : D g (incl g (MvPolynomial.X 0)) = incl g (MvPolynomial.X 1) := by simpa using D_X_old g 0
  have h1 : D g (incl g (MvPolynomial.X 1)) = 2 * incl g (MvPolynomial.X 2) := by simpa using D_X_old g 1
  have h2 : D g (incl g (MvPolynomial.X 2)) = 3 * incl g (MvPolynomial.X 3) := by simpa using D_X_old g 2
  have h3 : D g (incl g (MvPolynomial.X 3)) = 4 * W g := D_X_last g
  have hnat (n : ℕ) (a : Chart g) : D g ((n : Chart g) * a) = (n : Chart g) * D g a := by
    rw [D_mul, D_natCast, zero_mul, add_zero]
  have htwo (a : Chart g) : D g (2 * a) = 2 * D g a := by
    simpa only [Nat.cast_ofNat] using hnat 2 a
  have hsix (a : Chart g) : D g (6 * a) = 6 * D g a := by
    simpa only [Nat.cast_ofNat] using hnat 6 a
  change D g (D g (D g (D g (incl g (MvPolynomial.X 0))))) = _
  rw [h0, h1, htwo, h2, ← mul_assoc]
  rw [show (2 : Chart g) * 3 = 6 by norm_num, hsix, h3]
  ring
private theorem compare_numerators (g : Row 4) (k : ℕ) :
    graphMap g (numerator g k) * S g ^ (k + 8) = incl g (jetNumerator g (k + 4)) := by
  rw [lifted_numerator, old_numerator, Function.iterate_add_apply, iterate_four,
    mul_right_comm, ← pow_add, show k+(k+8) = 2*(k+4) by omega]
variable {f Q : Row 4} {l : ℕ}
private def toBranch (b : Branch f Q l) : Chart b.g →+* b.Local :=
  IsLocalization.Away.lift (separant b.g)
    (g := b.localMap.comp (MvPolynomial.map genericCoeffs))
    (IsLocalization.Away.algebraMap_isUnit b.sigma)
@[simp] private theorem toBranch_incl (b : Branch f Q l) (P : Row 4) :
    toBranch b (incl b.g P) = b.localMap (toGeneric P) :=
  IsLocalization.Away.lift_eq _ _ _
end
end K1_13_6_2_2_2
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_2_1_1_1
open K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_4 K1_13_6_1_4_2_1 MvPolynomial
theorem sectionWith_eval_ne_zero {σ : Type*} (p : Shape)
    (label : SectionIndex p → σ) (hinj : Function.Injective label) (x : Fin 4 → GeoField) :
    eval (fun i => algebraMap GeoField (FractionRing (MvPolynomial σ GeoField)) (x i))
      (sectionWith p label) ≠ 0 := by
  classical
  let m₀ : SectionIndex p := fun _ => 0
  have hm₀ : m₀ ∈ boxMonomials p := by
    simp [boxMonomials, m₀]
  let P : MvPolynomial σ GeoField :=
    ∑ m ∈ boxMonomials p, MvPolynomial.X (label m) * C (∏ i : Fin 4, x i ^ (m i).val)
  let F := FractionRing (MvPolynomial σ GeoField)
  let ρ := algebraMap (MvPolynomial σ GeoField) F
  have hmap : algebraMap GeoField F = ρ.comp (C (σ := σ)) :=
    IsScalarTower.algebraMap_eq GeoField (MvPolynomial σ GeoField) F
  have heval : eval (fun i => algebraMap GeoField F (x i)) (sectionWith p label) = ρ P := by
    simp only [sectionWith, P, ρ, F, map_sum, map_mul, map_prod, map_pow,
      eval_C, eval_X, hmap, RingHom.comp_apply]
  let c : σ → GeoField := fun j => if j = label m₀ then 1 else 0
  have hspecialize : eval c P = 1 := by
    simp only [P, map_sum, map_mul, eval_X, eval_C]
    rw [Finset.sum_eq_single_of_mem m₀ hm₀]
    · simp [c, m₀]
    · intro m _ hm
      simp [c, hinj.ne hm]
  change eval (fun i => algebraMap GeoField F (x i)) (sectionWith p label) ≠ 0
  rw [heval]
  intro hz
  have hP : P = 0 := (IsFractionRing.injective (K := F) _) (hz.trans (map_zero ρ).symm)
  rw [hP, map_zero] at hspecialize
  exact zero_ne_one hspecialize
theorem sectionWith_not_mem {σ : Type*} (surface : Ideal GeoJets)
    [surface.IsPrime] (p : Shape) (label : SectionIndex p → σ)
    (hinj : Function.Injective label) :
    sectionWith p label ∉ surface.map
      (MvPolynomial.map (algebraMap GeoField (FractionRing (MvPolynomial σ GeoField)))) := by
  have hex : (zeroLocus GeoField surface).Nonempty := by
    by_contra h
    apply (inferInstance : surface.IsPrime).ne_top
    rw [← IsPrime.vanishingIdeal_zeroLocus (K := GeoField) surface,
      Set.not_nonempty_iff_eq_empty.mp h, vanishingIdeal_empty]
  obtain ⟨x, hx⟩ := hex
  let F := FractionRing (MvPolynomial σ GeoField)
  let ι := algebraMap GeoField F
  let e : MvPolynomial (Fin 4) F →+* F := eval (ι ∘ x)
  have hle : surface.map (MvPolynomial.map ι) ≤ RingHom.ker e := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro f hf
    change eval (ι ∘ x) (MvPolynomial.map ι f) = 0
    have hz : eval x f = 0 := by simpa only [aeval_eq_eval] using hx f hf
    rw [eval_map, ← eval₂_comp, hz, map_zero]
  exact fun hm => sectionWith_eval_ne_zero p label hinj x (hle hm)
theorem proof : K1_13_6_1_4_2_1_1.c1 := by
  intro surface a h hs _ _ _
  let : surface.IsPrime := hs
  let : (extendIdeal surface a h).IsPrime := K1_13_6_3_5_2.isPrime_map surface hs
  constructor
  · unfold leftMul leftSection
    apply mul_right_injective₀
    exact fun hz => sectionWith_not_mem surface (a.scale 6) Sum.inl Sum.inl_injective
      (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  · unfold rightMul rightSection
    apply mul_right_injective₀
    exact fun hz => sectionWith_not_mem surface (h.scale 6) Sum.inr Sum.inr_injective
      (Ideal.Quotient.eq_zero_iff_mem.mp hz)
end K1_13_6_1_4_2_1_1_1
end
section
set_option autoImplicit false
namespace K1_13_6_1_5_2_1
open K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_5_2 MvPolynomial
theorem genericSection_eval_ne_zero (a : Shape) (x : Fin 4 → GeoField) :
    eval (fun i => algebraMap GeoField (SectionField a) (x i)) (genericSection a) ≠ 0 := by
  classical
  let m₀ : SectionIndex a := fun _ => 0
  have hm₀ : m₀ ∈ boxMonomials a := by
    simp [boxMonomials, m₀]
  let P : MvPolynomial (SectionIndex a) GeoField :=
    ∑ m ∈ boxMonomials a, MvPolynomial.X m * C (∏ i : Fin 4, x i ^ (m i).val)
  let ρ := algebraMap (MvPolynomial (SectionIndex a) GeoField) (SectionField a)
  have hmap : (algebraMap GeoField (SectionField a)) =
      ρ.comp (C (σ := SectionIndex a) : GeoField →+* _) :=
    IsScalarTower.algebraMap_eq GeoField (MvPolynomial (SectionIndex a) GeoField) (SectionField a)
  have heq : eval (fun i => algebraMap GeoField (SectionField a) (x i)) (genericSection a) =
      ρ P := by
    simp only [genericSection, P, ρ, map_sum, map_mul, map_prod, map_pow,
      MvPolynomial.eval_C, MvPolynomial.eval_X, hmap, RingHom.comp_apply]
  let c : SectionIndex a → GeoField := fun m => if m = m₀ then 1 else 0
  have he : MvPolynomial.eval c P = 1 := by
    simp only [P, map_sum, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]
    rw [Finset.sum_eq_single_of_mem m₀ hm₀]
    · simp [c, m₀]
    · intro m _ hm
      simp [c, hm]
  rw [heq]
  intro hz
  have hP : P = 0 := (IsFractionRing.injective (K := SectionField a) _)
    (hz.trans (map_zero ρ).symm)
  rw [hP, map_zero] at he
  exact zero_ne_one he
theorem genericSection_not_mem (C₀ : Ideal GeoJets) [hC₀ : C₀.IsPrime] (a : Shape) :
    genericSection a ∉ C₀.map (MvPolynomial.map (algebraMap GeoField (SectionField a))) := by
  have hex : (zeroLocus GeoField C₀).Nonempty := by
    by_contra h
    apply hC₀.ne_top
    rw [← IsPrime.vanishingIdeal_zeroLocus (K := GeoField) C₀,
      Set.not_nonempty_iff_eq_empty.mp h, vanishingIdeal_empty]
  obtain ⟨x, hx⟩ := hex
  let ι := algebraMap GeoField (SectionField a)
  let e : SectionJets a →+* SectionField a := eval (ι ∘ x)
  have hle : C₀.map (MvPolynomial.map ι) ≤ RingHom.ker e := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    change eval (ι ∘ x) (MvPolynomial.map ι p) = 0
    have hz : eval x p = 0 := by simpa only [aeval_eq_eval] using hx p hp
    rw [eval_map, ← eval₂_comp, hz, map_zero]
  exact fun h => genericSection_eval_ne_zero a x (hle h)
theorem proof : K1_13_6_1_5_2.c1 := by
  intro C₀ a hC₀ hdim
  let : C₀.IsPrime := hC₀
  let I := C₀.map (MvPolynomial.map (algebraMap GeoField (SectionField a)))
  have hI : I.IsPrime := K1_13_6_3_5_2.isPrime_map C₀ hC₀
  have hdeg : (affineHilbertPolynomial I).natDegree ≤ 1 := by
    rw [show I = _ from rfl, K1_13_5_5_2.hilbertPolynomial_map]
    exact K1_13_6_2_4_2.hilbert_degree_le (d := 1) (P := C₀) (by simpa using hdim.le)
  have hcut := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hI (genericSection_not_mem C₀ a) le_rfl).1
  apply moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero
  exact Nat.eq_zero_of_le_zero (hcut.trans (Nat.sub_eq_zero_of_le hdeg).le)
end K1_13_6_1_5_2_1
end
section
namespace K1_13_2_3_4
private def certificate : List ℕ := rowsA ++ rowsB ++ rowsC ++ rowsD
theorem certificate_fits : certificate.length ≤ 589 := by
  simpa only [certificate, List.length_append, Nat.reduceAdd,
    rowsA_length, rowsB_length, rowsC_length, rowsD_length] using (le_rfl : 589 ≤ 589)
theorem certificate_sum : rowsSum 1419 certificate = 9573892230 := by
  simp only [certificate, rowsSum_append, List.length_append, rowsA_length, rowsB_length, rowsC_length,
    Nat.reduceAdd, rowsA_sum, rowsB_sum, rowsC_sum, rowsD_sum]
theorem proof : K1_13_2_3.c4 := by
  obtain ⟨p, hp⟩ := rows_bound certificate certificate_fits
  rw [certificate_sum] at hp
  exact ⟨p, hp⟩
end K1_13_2_3_4
end
section
namespace K1_14_4
noncomputable section
open K1_14 Finset
open scoped BigOperators
private theorem shapeSum_swap (s : Shape) (g : ℕ → ℕ → ℕ) :
    (∑ j ∈ range (s.J + 1), ∑ q ∈ Ico j (s.B + 1), g q j) = shapeSum s g := by
  have h (j : ℕ) : (range (s.B + 1)).filter (j ≤ ·) = Ico j (s.B + 1) := by
    ext q
    simp [and_comm]
  simp_rw [← h, sum_filter, shapeSum]
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  rw [← sum_filter]
  congr 1
  ext j
  simp
  omega
private theorem gradeWidth_card (k B W j : ℕ) (hk : 0 < k) :
    gradeWidth k B W j = ∑ q ∈ Ico j (B + 1), if q * k ≤ W + j then 1 else 0 := by
  rw [← card_filter]
  have heq : (Ico j (B + 1)).filter (fun q => q * k ≤ W + j) =
      Ico j (min (B + 1) ((W + j) / k + 1)) := by
    ext q
    simp only [mem_filter, mem_Ico, lt_min_iff, ← Nat.le_div_iff_mul_le hk]
    omega
  rw [heq, Nat.card_Ico, gradeWidth]
private theorem slots_antitone (U : ℕ) : Antitone (slots U) := by
  intro a b hab
  by_cases hb : b ≤ U
  · have ha := hab.trans hb
    rw [slots, ite_eq_left hb, slots, ite_eq_left ha]
    unfold triangle
    have h := Nat.sub_le_sub_left hab U
    exact Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))
  · simp [slots, hb]
private theorem sum_slot_drops (A : ℕ → ℕ) (hm : Antitone A) (n L : ℕ) :
    (∑ r ∈ range n, if r < L then A r - A (r + 1) else 0) + A (min n L) = A 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    by_cases h : n < L
    · rw [min_eq_left h.le] at ih
      rw [ite_eq_left h, min_eq_left (by omega : n + 1 ≤ L)]
      rw [add_assoc, Nat.sub_add_cancel (hm (show n ≤ n + 1 by omega))]
      exact ih
    · rw [min_eq_right (by omega : L ≤ n)] at ih
      rwa [ite_eq_right h, add_zero, min_eq_right (by omega : L ≤ n + 1)]
private theorem sum_interval (top j t d c : ℕ) (hj : j ≤ t) :
    (∑ W ∈ range top, if t ≤ W + j ∧ W + d < top then c else 0) =
      c * (top + j - t - d) := by
  have hI : (range top).filter (fun W => t ≤ W + j ∧ W + d < top) =
      Ico (t - j) (top - d) := by
    ext W
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [← sum_filter, hI]
  have hwidth : top - d - (t - j) = top + j - t - d := by omega
  simp [hwidth, Nat.mul_comm]
private theorem power_threshold (top step W j r : ℕ) (hW : W < top) (hs : 0 < step) :
    r < 1 + (top - 1 - W) / step - j ↔ W + step * (j + r) < top := by
  have h : r < 1 + (top - 1 - W) / step - j ↔ j + r ≤ (top - 1 - W) / step := by omega
  rw [h, Nat.le_div_iff_mul_le hs, Nat.mul_comm (j + r)]
  omega
private theorem position_sum (top step t j U v : ℕ) (hj : j ≤ t)
    (hs : 0 < step) (hv : 0 < v) :
    (∑ W ∈ range top, if t ≤ W + j then
      slots U ((1 + (top - 1 - W) / step - j) * v) else 0) +
    (∑ r ∈ range (U / v + 1),
      (slots U (r * v) - slots U ((r + 1) * v)) * (top + j - t - step * (j + r))) =
      triangle U * (top + j - t) := by
  let A r := slots U (r * v)
  let n := U / v + 1
  let L W := 1 + (top - 1 - W) / step - j
  have hmono : Antitone A := fun _ _ h => slots_antitone U (Nat.mul_le_mul_right v h)
  have hz {r : ℕ} (hr : n ≤ r) : A r = 0 := by
    have h := (Nat.div_lt_iff_lt_mul hv).1 (show U / v < r by omega)
    simp [A, slots, Nat.not_le.mpr h]
  have hmin (l : ℕ) : A (min n l) = A l := by
    by_cases hl : l ≤ n
    · rw [min_eq_right hl]
    · rw [min_eq_left (by omega), hz le_rfl, hz (by omega)]
  change (∑ W ∈ range top, if t ≤ W + j then A (L W) else 0) +
      (∑ r ∈ range n, (A r - A (r + 1)) * (top + j - t - step * (j + r))) = _
  have hzero : A 0 = triangle U := by simp [A, slots]
  rw [← hzero]
  simp_rw [← sum_interval top j t _ _ hj]
  rw [sum_comm (s := range n), ← sum_add_distrib]
  have hbase : A 0 * (top + j - t) =
      ∑ W ∈ range top, if t ≤ W + j ∧ W + 0 < top then A 0 else 0 := by
    rw [sum_interval top j t 0 _ hj, Nat.sub_zero]
  rw [hbase]
  apply sum_congr rfl
  intro W hW
  have hWt := mem_range.mp hW
  by_cases h : t ≤ W + j
  · simp only [h, true_and, Nat.add_zero, hWt, ite_true]
    have hsum := sum_slot_drops A hmono n (L W)
    rw [hmin, add_comm] at hsum
    rw [← hsum]
    congr 1
    apply sum_congr rfl
    intro r _
    simp only [show r < L W ↔ W + step * (j + r) < top from power_threshold _ _ _ _ _ hWt hs]
  · simp [h]
end
end K1_14_4
end
section
namespace K1_13_7_5_2
noncomputable section
open Polynomial K1 K1_13 K1_13_6 K1_13_7 K1_13_7_1 K1_13_7_5
open scoped BigOperators
private theorem supported_of_fits {P : Jets} {H : Shape} (h : GeoFits P H) :
    Supported H P := by
  intro m hm
  refine ⟨?_, ?_, ?_⟩
  · exact (Finset.le_sup (f := fun a => a.sum fun _ e => e) hm).trans h.1
  · have hw := (MvPolynomial.le_weightedTotalDegree Fin.val hm).trans h.2.1
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using hw
  · exact (MvPolynomial.le_degreeOf_of_mem_support _ hm).trans h.2.2
private abbrev constants : Geom →+* GeometricX := genericCoeff.comp Polynomial.C
private abbrev center : GeometricX := genericCoeff Polynomial.X
private theorem eval_center (P : Geom[X]) : (P.map constants).eval center = genericCoeff P := by
  rw [Polynomial.eval_map]
  change P.eval₂ (genericCoeff.comp Polynomial.C) (genericCoeff Polynomial.X) = genericCoeff P
  rw [← Polynomial.hom_eval₂, Polynomial.eval₂_C_X]
end
end K1_13_7_5_2
end
section
set_option autoImplicit false
namespace K1_13_7_2_3_2
open K1_13 K1_13_6 K1_13_6_1 K1_13_7_1
def c1 : Prop := K1_13_6_1_5_2.c1
def c2 : Prop := K1_13_6_1_5_2.c2
theorem of_children (h₁ : c1) (h₂ : c2) : K1_13_7_2_3.c2 := by
  classical
  have count : K1_13_6_1_5.c2 := K1_13_6_1_5_2.of_children h₁ h₂
  intro a ha ht surface P C hC
  obtain ⟨hp, hdim⟩ := component_curve hC
  have hunit := chamber_has_simplex ha ht
  have bound (U : GeoJets) (points : Finset GeoPoint) (hU : GeoFits U a) (hne : U ∉ C)
      (hpoints : ∀ y ∈ points,
        C ≤ RingHom.ker (MvPolynomial.eval y) ∧ MvPolynomial.eval y U = 0) :
      6 * points.card ≤ sectionDegree C (a.scale 6) :=
    count C a hp hdim hunit U hU hne points hpoints
  refine ⟨?_, bound⟩
  obtain ⟨y, U, hy, hU, hne, hzero⟩ := K1_13_6_1_5.coordinate_cut hp hdim
  have hfit : GeoFits U a :=
    ⟨hU.1.trans hunit.1, hU.2.1.trans hunit.2.1, hU.2.2.trans hunit.2.2⟩
  simpa only [Finset.card_singleton, Nat.mul_one] using
    bound U {y} hfit hne (by
      intro z hz
      rw [Finset.mem_singleton.mp hz]
      exact ⟨hy, hzero⟩)
end K1_13_7_2_3_2
end
section
namespace K1_13_2_3_6
private def rows : List (List ℕ) :=
  rowsA ++ rowsB ++ rowsC ++ rowsD ++ rowsE ++ rowsF ++ rowsG ++ rowsH ++ rowsI ++ rowsJ ++ rowsK ++ rowsL ++ rowsM
theorem rows_length : rows.length = 502 := by
  simp only [rows, List.length_append, checkA.1, checkB.1, checkC.1, checkD.1,
    checkE.1, checkF.1, checkG.1, checkH.1, checkI.1, checkJ.1,
    checkK.1, checkL.1, checkM.1, Nat.reduceAdd]
theorem rows_fit : fits 3012 rows = true := by
  simp only [rows, fits_append, List.length_append, checkA.1, checkB.1, checkC.1, checkD.1,
    checkE.1, checkF.1, checkG.1, checkH.1, checkI.1, checkJ.1,
    checkK.1, checkL.1, checkA.2.1, checkB.2.1, checkC.2.1,
    checkD.2.1, checkE.2.1, checkF.2.1, checkG.2.1, checkH.2.1, checkI.2.1,
    checkJ.2.1, checkK.2.1, checkL.2.1, checkM.2.1, Nat.reduceAdd, Bool.true_and]
theorem rows_value : value 3012 rows = 100540921280 := by
  simp only [rows, value_append, List.length_append, checkA.1, checkB.1, checkC.1, checkD.1,
    checkE.1, checkF.1, checkG.1, checkH.1, checkI.1, checkJ.1,
    checkK.1, checkL.1, checkA.2.2, checkB.2.2, checkC.2.2,
    checkD.2.2, checkE.2.2, checkF.2.2, checkG.2.2, checkH.2.2, checkI.2.2,
    checkJ.2.2, checkK.2.2, checkL.2.2, checkM.2.2, Nat.reduceAdd]
theorem proof : K1_13_2_3.c6 := by
  have hc := value_le_savingsSum 3012 rows (by decide)
    (by rw [rows_length]) rows_fit
  rw [rows_value] at hc
  exact hc
end K1_13_2_3_6
end
