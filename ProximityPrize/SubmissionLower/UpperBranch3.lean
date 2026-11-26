import ProximityPrize.SubmissionLower.Fast076
import ProximityPrize.SubmissionLower.ListProofA
import ProximityPrize.SubmissionLower.PortHighFinish
import ProximityPrize.SubmissionLower.Fast077

set_option Elab.async false

-- merged module RungSplit
section Merged_RungSplit
set_option Elab.async false
set_option autoImplicit true
section
namespace CJ0_5
noncomputable section
open CJ0 Polynomial PolynomialDifferential MvPolynomial Sol1.C57
def eliminate (G : DifferentialPolynomial K 2) : DifferentialPolynomial K 1 :=
  let P := topPresentation 1 G
  let c := P.natDegree
  if c = 0 then P.coeff 0 else P.resultant P.derivative c (c - 1)
def inputWeight (a : ℕ) (w : JetVariable 1 → ℕ) (v : JetVariable 2) : ℕ :=
  (topVariableEquiv 1 v).elim a w
private def coeffMap : K →+* (Polynomial K1_13.Geom) :=
  Polynomial.C.comp K1_13.embed
private theorem coeffMap_injective : Function.Injective coeffMap :=
  Polynomial.C_injective.comp (RingHom.injective K1_13.embed)
private def lowerEquiv : JetVariable 1 ≃ Fin 3 := (finSuccEquiv 2).symm
private def higherEquiv : JetVariable 2 ≃ Fin 4 :=
  ((topVariableEquiv 1).trans (Equiv.optionCongr lowerEquiv)).trans finSuccEquivLast.symm
private def lowerMap : DifferentialPolynomial K 1 →+* K1_13.Row 3 :=
  (MvPolynomial.map coeffMap).comp (rename (R := K) lowerEquiv).toRingHom
private theorem lowerMap_injective : Function.Injective lowerMap :=
  (MvPolynomial.map_injective coeffMap coeffMap_injective).comp (rename_injective _ lowerEquiv.injective)
private def row (G : DifferentialPolynomial K 2) : K1_13.Row 4 :=
  MvPolynomial.map coeffMap (rename higherEquiv G)
private def rowWeight (a : ℕ) (w : JetVariable 1 → ℕ) (j : Fin 4) : ℕ :=
  (finSuccEquivLast j).elim a (w ∘ lowerEquiv.symm)
private theorem rowWeight_last (a : ℕ) (w : JetVariable 1 → ℕ) :
    rowWeight a w (Fin.last 3) = a := by simp only [rowWeight, finSuccEquivLast_last, Option.elim_none]
private theorem row_weight (a : ℕ) (w : JetVariable 1 → ℕ) (G : DifferentialPolynomial K 2) :
    (row G).weightedTotalDegree (rowWeight a w) = G.weightedTotalDegree (inputWeight a w) := by
  have hm : (row G).weightedTotalDegree (rowWeight a w) =
      (rename higherEquiv G).weightedTotalDegree (rowWeight a w) := by
    rw [row]; simp only [weightedTotalDegree, MvPolynomial.support_map_of_injective _ coeffMap_injective]
  rw [hm, weightedTotalDegree_rename_of_injective higherEquiv.injective]
  congr 1
  funext v
  change (finSuccEquivLast (finSuccEquivLast.symm
    (Equiv.optionCongr lowerEquiv (topVariableEquiv 1 v)))).elim a (w ∘ lowerEquiv.symm) = _
  rw [Equiv.apply_symm_apply]
  unfold inputWeight
  cases topVariableEquiv 1 v <;> simp
private theorem lower_weight (a : ℕ) (w : JetVariable 1 → ℕ) (R : DifferentialPolynomial K 1) :
    (lowerMap R).weightedTotalDegree (fun j => rowWeight a w j.castSucc) = R.weightedTotalDegree w := by
  have hm : (lowerMap R).weightedTotalDegree (fun j => rowWeight a w j.castSucc) =
      (rename lowerEquiv R).weightedTotalDegree (fun j => rowWeight a w j.castSucc) := by
    change (MvPolynomial.map coeffMap (rename lowerEquiv R)).weightedTotalDegree _ = _
    simp only [weightedTotalDegree, MvPolynomial.support_map_of_injective _ coeffMap_injective]
  rw [hm, weightedTotalDegree_rename_of_injective lowerEquiv.injective]
  congr 1
  funext v
  simp [rowWeight, finSuccEquivLast_castSucc]
private theorem view_row (G : DifferentialPolynomial K 2) :
    K1_13_5_1.view (row G) = (topPresentation 1 G).map lowerMap := by
  have he : K1_13_5_1.view.toRingHom.comp ((MvPolynomial.map coeffMap).comp (rename (R := K) higherEquiv).toRingHom) =
      (Polynomial.mapRingHom lowerMap).comp (topPresentation 1).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [K1_13_5_1.view, topPresentation, topReindex, lowerMap]
    · intro v
      change K1_13_5_1.view (row (MvPolynomial.X v)) =
        (topPresentation 1 (MvPolynomial.X v)).map lowerMap
      have hX : row (MvPolynomial.X v) = MvPolynomial.X (higherEquiv v) := by simp [row]
      rw [hX]
      change optionEquivLeft (Polynomial K1_13.Geom) (Fin 3)
          (rename finSuccEquivLast (MvPolynomial.X (higherEquiv v))) =
        (optionEquivLeft K (JetVariable 1) (rename (topVariableEquiv 1) (MvPolynomial.X v))).map
          lowerMap
      simp only [rename_X]
      rw [show finSuccEquivLast (higherEquiv v) = Equiv.optionCongr lowerEquiv
        (topVariableEquiv 1 v) from Equiv.apply_symm_apply _ _]
      cases topVariableEquiv 1 v with
      | none => simp
      | some j =>
        simp only [Equiv.optionCongr_apply, Option.map_some, optionEquivLeft_X_some, Polynomial.map_C]
        congr 1
        change MvPolynomial.X (lowerEquiv j) = MvPolynomial.map coeffMap
          (rename lowerEquiv (MvPolynomial.X j))
        simp
  exact DFunLike.congr_fun he G
private theorem row_degree (G : DifferentialPolynomial K 2) :
    (K1_13_5_1.view (row G)).natDegree = (topPresentation 1 G).natDegree := by
  rw [view_row, natDegree_map_eq_of_injective lowerMap_injective]
private theorem row_elimination (G : DifferentialPolynomial K 2) :
    K1_13_5_1.elimination (row G) = lowerMap (eliminate G) := by
  unfold K1_13_5_1.elimination eliminate
  simp only [row_degree]
  split_ifs
  · rw [view_row, Polynomial.coeff_map]
  · rw [view_row, derivative_map, resultant_map_map]
theorem eliminate_weight (a : ℕ) (w : JetVariable 1 → ℕ) (G : DifferentialPolynomial K 2) :
    let c := jetDegree G (Fin.last 2)
    a * c ≤ G.weightedTotalDegree (inputWeight a w) ∧
    (c = 0 → (eliminate G).weightedTotalDegree w ≤ G.weightedTotalDegree (inputWeight a w)) ∧
    (0 < c → (eliminate G).weightedTotalDegree w + a * c^2 ≤
      (2*c-1) * G.weightedTotalDegree (inputWeight a w)) := by
  have hc := row_degree G
  rw [topPresentation_degree] at hc
  have hb := K1_13_5_1.view_coeff_weight (rowWeight a w) (row G)
    (K1_13_5_1.view (row G)).natDegree le_rfl
  rw [rowWeight_last, hc, row_weight] at hb
  refine ⟨(Nat.le_add_left _ _).trans hb, ?_, ?_⟩
  · intro hz
    have h := K1_13_5_1.elimination_weight_zero (rowWeight a w) (row G) (hc.trans hz)
    rwa [row_elimination, lower_weight, row_weight] at h
  · intro hp
    have h := K1_13_5_1.elimination_weight_positive (rowWeight a w) (row G) (hc.symm ▸ hp)
    dsimp only at h
    rwa [row_elimination, lower_weight, rowWeight_last, hc, row_weight] at h
end
end CJ0_5
end
section
namespace CJ0_5
noncomputable section
open scoped BigOperators
private theorem increase_budget {a b c C t d : ℕ} (hc : 0 < c) (hC : c ≤ C)
    (ht : a * t ≤ 2 * b) (hd : d + a * c ^ 2 ≤ (2 * c - 1) * b) :
    d + a * c ^ 2 + a * ((C - c) * t) ≤ (2 * C - 1) * b := by
  have hincr := Nat.mul_le_mul_left (C - c) ht
  have he : 2 * C - 1 = (2 * c - 1) + 2 * (C - c) := by omega
  rw [he, Nat.add_mul]
  rw [show a * ((C - c) * t) = (C - c) * (a * t) by ring,
    show 2 * (C - c) * b = (C - c) * (2 * b) by ring]
  exact Nat.add_le_add hd hincr
theorem aggregate {ι : Type*} (T : Finset ι) (b c d : ι → ℕ) (B a cap : ℕ)
    (hb : ∑ i ∈ T, b i ≤ B) (hc : ∑ i ∈ T, c i ≤ cap) (hB : a * cap ≤ B)
    (hbase : ∀ i ∈ T, a * c i ≤ b i)
    (hzero : ∀ i ∈ T, c i = 0 → d i ≤ b i)
    (hpos : ∀ i ∈ T, 0 < c i → d i + a * (c i)^2 ≤ (2 * c i - 1) * b i) :
    ∑ i ∈ T, d i ≤ max B ((2 * cap - 1) * B - a * cap^2) := by
  let C := ∑ i ∈ T, c i
  have hci (i : ι) (hi : i ∈ T) : c i ≤ C := Finset.single_le_sum (fun j _ => Nat.zero_le (c j)) hi
  by_cases hC : C = 0
  · have h := (Finset.sum_le_sum fun i hi => hzero i hi (by have := hci i hi; omega)).trans hb
    exact h.trans (le_max_left _ _)
  have hCpos := Nat.pos_of_ne_zero hC
  have hterm (i : ι) (hi : i ∈ T) : d i + a * (C * c i) ≤ (2 * C - 1) * b i := by
    by_cases hi₀ : c i = 0
    · rw [hi₀, Nat.mul_zero, Nat.mul_zero, Nat.add_zero]
      exact (hzero i hi hi₀).trans (by
        simpa using Nat.mul_le_mul_right (b i) (show 1 ≤ 2 * C - 1 by omega))
    · have h := increase_budget (Nat.pos_of_ne_zero hi₀) (hci i hi)
        ((hbase i hi).trans (by omega : b i ≤ 2 * b i)) (hpos i hi (Nat.pos_of_ne_zero hi₀))
      have he : C = c i + (C - c i) := by have := hci i hi; omega
      have hweight : a * (C * c i) = a * (c i)^2 + a * ((C - c i) * c i) := by
        calc
          _ = a * ((c i + (C - c i)) * c i) := congrArg (fun n => a * (n * c i)) he
          _ = _ := by ring
      rw [hweight, ← Nat.add_assoc]
      exact h
  have hs : (∑ i ∈ T, (d i + a * (C * c i))) ≤ (2 * C - 1) * B :=
    (Finset.sum_le_sum hterm).trans (by
      rw [← Finset.mul_sum]
      exact Nat.mul_le_mul_left _ hb)
  have hjoint : (∑ i ∈ T, d i) + a * C ^ 2 ≤ (2 * C - 1) * B := by
    simp only [Finset.sum_add_distrib, ← Nat.mul_assoc, ← Finset.mul_sum] at hs
    change (∑ i ∈ T, d i) + (a * C) * C ≤ _ at hs
    rwa [Nat.mul_assoc, ← pow_two] at hs
  have ha : a * (cap + C) ≤ 2 * B := by
    calc
      _ ≤ a * (cap + cap) := Nat.mul_le_mul_left _ (Nat.add_le_add_left hc cap)
      _ = 2 * (a * cap) := by ring
      _ ≤ _ := Nat.mul_le_mul_left 2 hB
  have hfinal := increase_budget hCpos hc ha hjoint
  have he : cap = C + (cap - C) := by omega
  have hsq : a * C ^ 2 + a * ((cap - C) * (cap + C)) = a * cap ^ 2 := by
    calc
      _ = a * C ^ 2 + a * ((cap - C) * ((C + (cap - C)) + C)) := by
        exact congrArg (fun n => a * C ^ 2 + a * ((cap - C) * (n + C))) he
      _ = a * (C + (cap - C)) ^ 2 := by ring
      _ = _ := by rw [← he]
  exact (Nat.le_sub_of_add_le (by simpa only [Nat.add_assoc, hsq] using hfinal)).trans
    (le_max_right _ _)
end
end CJ0_5
end
section
namespace CJ0_5
noncomputable section
open CJ0 Polynomial PolynomialDifferential MvPolynomial Sol1.C57 UniqueFactorizationMonoid
open scoped BigOperators
private theorem eliminate_ne_zero {G : DifferentialPolynomial K 2} (hG : Irreducible G)
    (hchar : jetDegree G (Fin.last 2) < p) : eliminate G ≠ 0 := by
  let P := topPresentation 1 G
  let c := P.natDegree
  have hi : Irreducible P := (MulEquiv.irreducible_iff (topPresentation 1).toMulEquiv).mpr hG
  change (if c = 0 then P.coeff 0 else P.resultant P.derivative c (c-1)) ≠ 0
  by_cases h : c = 0
  · have hn := leadingCoeff_ne_zero.mpr hi.ne_zero
    change P.coeff c ≠ 0 at hn
    simpa only [h, ite_true] using hn
  · have hlt : c < p := (topPresentation_degree 1 G).trans_lt hchar
    have hcast : (c : K) ≠ 0 := by
      intro hz
      exact (not_le_of_gt hlt) (Nat.le_of_dvd (Nat.pos_of_ne_zero h)
        ((CharP.cast_eq_zero_iff K p c).mp hz))
    have hc : (c : DifferentialPolynomial K 1) ≠ 0 := by
      simpa only [map_natCast, map_zero] using (MvPolynomial.C_injective _ K).ne hcast
    have hder : P.derivative ≠ 0 := by
      intro hz
      have hindex : c - 1 + 1 = c := by omega
      have hz' := congrArg (fun R : Polynomial (DifferentialPolynomial K 1) => R.coeff (c-1)) hz
      rw [coeff_derivative, ← Nat.cast_succ, Nat.succ_eq_add_one, hindex, coeff_zero] at hz'
      exact mul_ne_zero (leadingCoeff_ne_zero.mpr hi.ne_zero) hc hz'
    simpa only [ite_eq_right h] using resultant_derivative_ne_zero_of_irreducible P hi hder
private theorem eliminate_root (G : DifferentialPolynomial K 2) (f : (Polynomial K))
    (hG : differentialSpecialization G f = 0)
    (hsep : differentialSpecialization (separant G (Fin.last 2)) f = 0) :
    differentialSpecialization (eliminate G) f = 0 := by
  let P := topPresentation 1 G
  let ψ := (differentialSpecializationHom (d := 1) f).toRingHom
  have he : P.eval₂ ψ (hasseDeriv 2 f) = 0 := (topPresentation_eval 1 G f).trans hG
  change ψ (if P.natDegree = 0 then P.coeff 0 else
    P.resultant P.derivative P.natDegree (P.natDegree - 1)) = 0
  by_cases hc : P.natDegree = 0
  · rw [ite_eq_left hc]
    have h := congrArg (fun R : Polynomial (DifferentialPolynomial K 1) =>
      R.eval₂ ψ (hasseDeriv 2 f)) (eq_C_of_natDegree_eq_zero hc)
    change P.eval₂ ψ (hasseDeriv 2 f) = _ at h
    rw [Polynomial.eval₂_C] at h
    exact h.symm.trans he
  · rw [ite_eq_right hc]
    have hd : P.derivative.eval₂ ψ (hasseDeriv 2 f) = 0 := by
      change (topPresentation 1 G).derivative.eval₂ ψ _ = 0
      rw [topPresentation_derivative, topPresentation_eval]
      exact hsep
    exact map_resultant_eq_zero_of_common_root ψ P P.derivative le_rfl
      (natDegree_derivative_le P) (Or.inl hc) (hasseDeriv 2 f)
      ((Polynomial.eval₂_eq_eval_map ψ).symm.trans he) ((Polynomial.eval₂_eq_eval_map ψ).symm.trans hd)
private theorem input_total : inputWeight 1 jetDegreeWeight = jetDegreeWeight := by
  funext v
  rcases v with _ | j
  · simp [inputWeight]
  · induction j using Fin.lastCases with
    | last => simp only [inputWeight, topVariableEquiv_top, Option.elim_none, jetDegreeWeight_some]
    | cast j => simp [inputWeight]
private theorem input_index : inputWeight 2 CJ0.indexWeight = CJ0.indexWeight := by
  funext v
  rcases v with _ | j
  · simp [inputWeight, CJ0.indexWeight]
  · induction j using Fin.lastCases with
    | last =>
      rw [inputWeight, topVariableEquiv_top]
      rfl
    | cast j => simp [inputWeight, CJ0.indexWeight]
private theorem output_index : CJ0.indexWeight = (Pi.single (some (Fin.last 1)) 1 : JetVariable 1 → ℕ) := by
  funext v
  rcases v with _ | j
  · simp [CJ0.indexWeight]
  · induction j using Fin.lastCases with
    | last =>
      change 1 = (Pi.single (some (Fin.last 1)) 1 : JetVariable 1 → ℕ) (some (Fin.last 1))
      simp only [Pi.single_eq_same]
    | cast j =>
      have hne : some j.castSucc ≠ some (Fin.last 1) :=
        (Option.some_injective _).ne (Fin.castSucc_ne_last j)
      rw [Pi.single_eq_of_ne hne]
      change j.val = 0
      omega
theorem proof : CJ0.c5 := by
  classical
  intro s hs Q hQ
  obtain ⟨hq, hb, hj, hc⟩ := hQ
  let _ : StrongNormalizationMonoid (DifferentialPolynomial K 2) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let A := normalizedFactors Q
  let T := A.toFinset
  let c (G : DifferentialPolynomial K 2) := jetDegree G (Fin.last 2)
  let Q₁ : DifferentialPolynomial K 1 := ∏ G ∈ T, eliminate G
  have hmem (G) (hG : G ∈ T) : G ∈ A := Multiset.mem_toFinset.mp hG
  have hirr (G) (hG : G ∈ T) : Irreducible G :=
    irreducible_of_normalized_factor G (hmem G hG)
  have hdvd : (∏ G ∈ T, G) ∣ Q :=
    (Multiset.toFinset_prod_dvd_prod A).trans (prod_normalizedFactors hq).dvd
  have hcSum : ∑ G ∈ T, c G ≤ s.C := by
    let w : JetVariable 2 → ℕ := Pi.single (some (Fin.last 2)) 1
    have hh := sum_weightedTotalDegree_le_of_prod_dvd w T id hq hdvd
    exact (by simpa only [w, id_eq, weightedTotalDegree_piSingle, jetDegree, c] using hh :
      (∑ G ∈ T, c G) ≤ jetDegree Q (Fin.last 2)).trans hc
  have h2 : 2 ≤ s.B := by have := hs.top_pos; have := hs.index_top; have := hs.total_index; omega
  have hC : s.C < p := calc
    s.C ≤ s.B := by have := hs.index_top; have := hs.total_index; omega
    _ = s.B * 1 := (Nat.mul_one _).symm
    _ ≤ s.B * (s.B - 1) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ max N (s.B*(s.B-1)) := le_max_right _ _
    _ < p := hs.characteristic
  have he (G) (hG : G ∈ T) : eliminate G ≠ 0 :=
    eliminate_ne_zero (hirr G hG)
      (((Finset.single_le_sum (fun i _ => Nat.zero_le (c i)) hG).trans hcSum).trans_lt hC)
  have hweight (a B : ℕ) (w : JetVariable 1 → ℕ)
      (hB : a*s.C ≤ B) (hQw : Q.weightedTotalDegree (inputWeight a w) ≤ B) :
      Q₁.weightedTotalDegree w ≤ max B ((2*s.C-1)*B-a*s.C^2) := by
    rw [show Q₁ = ∏ G ∈ T, eliminate G from rfl, weightedTotalDegree_prod w T _ he]
    apply aggregate T (fun G => G.weightedTotalDegree (inputWeight a w)) c
      (fun G => (eliminate G).weightedTotalDegree w) B a s.C
      ((sum_weightedTotalDegree_le_of_prod_dvd _ T id hq hdvd).trans hQw) hcSum hB
    · exact fun G _ => (eliminate_weight a w G).1
    · exact fun G _ => (eliminate_weight a w G).2.1
    · exact fun G _ => (eliminate_weight a w G).2.2
  refine ⟨Q₁, ⟨Finset.prod_ne_zero_iff.mpr he, ?_, ?_⟩, ?_⟩
  · simpa only [jetTotalDegree, H, one_mul] using
      hweight 1 s.B jetDegreeWeight (by have := hs.index_top; have := hs.total_index; omega)
        (by simpa only [input_total, jetTotalDegree] using hb)
  · have hh := hweight 2 s.J CJ0.indexWeight hs.index_top (by rwa [input_index])
    simpa only [output_index, weightedTotalDegree_piSingle, jetDegree, I₁] using hh
  · intro f _ hf hsing
    let ψ := (differentialSpecializationHom (d := 2) f).toRingHom
    change ψ Q = 0 at hf
    have hz := map_dvd ψ (prod_normalizedFactors hq).symm.dvd
    change ψ Q ∣ ψ A.prod at hz
    rw [hf, zero_dvd_iff, map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hz
    obtain ⟨G, hG, hg⟩ := hz
    have hgT : G ∈ T := Multiset.mem_toFinset.mpr hG
    have hsep : differentialSpecialization (separant G (Fin.last 2)) f = 0 := by
      by_contra hne
      exact hsing ⟨G, hirr G hgT, dvd_of_mem_normalizedFactors hG, hg, hne⟩
    have hroot := eliminate_root G f hg hsep
    change (differentialSpecializationHom (d := 1) f).toRingHom (∏ G ∈ T, eliminate G) = 0
    rw [map_prod]
    exact Finset.prod_eq_zero hgT hroot
end
end CJ0_5
end
section
namespace CJ0_6
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open CJ0 Polynomial PolynomialDifferential
open scoped BigOperators
def centeredEquation (G : DifferentialPolynomial K 1) : DifferentialPolynomial Geo 1 :=
  MvPolynomial.map embed G
def initial : DifferentialPolynomial K 1 →+* InitialRing 1 :=
  (MvPolynomial.aeval (R := Geo) (fun i : Option (Fin 2) =>
    i.elim (MvPolynomial.C center) MvPolynomial.X)).toRingHom.comp
    (MvPolynomial.map embed)
def sep (G : DifferentialPolynomial K 1) : InitialRing 1 :=
  initialJetSeparant center (centeredEquation G)
def denominator (G : DifferentialPolynomial K 1) : InitialRing 1 :=
  sep G ^ t₁
private def centerMap : (Polynomial K) →+* Geo :=
  (algebraMap FX Geo).comp (algebraMap (Polynomial K) FX)
private theorem centerMap_injective : Function.Injective centerMap :=
  (algebraMap FX Geo).injective.comp (IsFractionRing.injective (Polynomial K) FX)
theorem initial_injective : Function.Injective initial := by
  have h : initial = (MvPolynomial.map centerMap).comp
      (MvPolynomial.optionEquivRight K (Fin 2)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [initial, centerMap, embed]
    · intro j
      cases j <;> simp [initial, centerMap, center]
  rw [h]
  exact (MvPolynomial.map_injective _ centerMap_injective).comp
    (MvPolynomial.optionEquivRight K (Fin 2)).injective
theorem initial_total (G : DifferentialPolynomial K 1) :
    (initial G).totalDegree ≤ jetTotalDegree G :=
  (totalDegree_initialJetEquation_le center (centeredEquation G)).trans
    (jetTotalDegree_map_le embed G)
theorem initial_top (G : DifferentialPolynomial K 1) :
    (initial G).degreeOf (Fin.last 1) ≤ jetDegree G (Fin.last 1) := by
  apply (degreeOf_initialJetEquation_le center (centeredEquation G)).trans
  simpa only [centeredEquation, jetDegree, MvPolynomial.degreeOf_def] using
    Multiset.count_le_of_le (some (Fin.last 1))
      (MvPolynomial.degrees_map_le (p := G) (f := embed))
private theorem exponent_sufficient : TaylorExponentSufficient 1 k t₁ :=
  taylorExponentSufficient_firstOrder_tight N
private def shiftedWeight (z : Geo) (l i : ℕ) : Geo :=
  (l.choose i : Geo) * z ^ (l-i)
private theorem coeff_taylor_sum {m : ℕ} (z : Geo) (a : Fin m → Geo) (i : ℕ) :
    (taylor z (∑ l : Fin m, monomial l.val (a l))).coeff i =
      ∑ l : Fin m, shiftedWeight z l.val i * a l := by
  rw [map_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro l _
  rw [Polynomial.taylor_coeff, Polynomial.hasseDeriv_monomial, Polynomial.eval_monomial]
  unfold shiftedWeight
  ring
private theorem readJet_coeff {P : (Polynomial Geo)} (hP : P.degree < k) (i : ℕ) :
    readJet (fun j => P.coeff j.val) i = (taylor center P).coeff i := by
  have hnat : P.natDegree < k := by
    by_cases hz : P = 0
    · simpa only [hz, Polynomial.natDegree_zero] using (by decide : 0 < k)
    · exact (Polynomial.natDegree_lt_iff_degree_lt hz).2 hP
  have hsum : P = ∑ l : Fin k, monomial l.val (P.coeff l.val) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => monomial j (P.coeff j))]
    exact P.as_sum_range' _ hnat
  exact (coeff_taylor_sum center (fun j : Fin k => P.coeff j.val) i).symm.trans
    (congrArg (fun P : (Polynomial Geo) => (taylor center P).coeff i) hsum.symm)
private def padded (G : DifferentialPolynomial K 1) (l : Fin k) : InitialRing 1 :=
  commonTaylorNumerator center (centeredEquation G) t₁ l.val
private def combine {m : ℕ} (P : Fin m → InitialRing 1) (i : ℕ) : InitialRing 1 :=
  ∑ l : Fin m, MvPolynomial.C (shiftedWeight (-center) l.val i) * P l
def chart (G : DifferentialPolynomial K 1) (g : InitialRing 1) : Chart 1 :=
  ⟨g, denominator G, fun i => combine (padded G) i.val⟩
private theorem denominator_band (s : Source) (G : DifferentialPolynomial K 1)
    (hT : jetTotalDegree G ≤ H s) (hI : jetDegree G (Fin.last 1) ≤ I₁ s) :
    inBand₁ s (denominator G) := by
  have ht : (sep G).totalDegree ≤ H s - 1 :=
    (totalDegree_initialJetSeparant_le center (centeredEquation G)).trans
      (Nat.sub_le_sub_right ((jetTotalDegree_map_le embed G).trans hT) 1)
  have hi : (sep G).degreeOf (Fin.last 1) ≤ I₁ s - 1 := by
    rw [sep, ← pderiv_last_initialJetEquation]
    exact (MvPolynomial.degreeOf_pderiv_le_sub_one _ _).trans
      (Nat.sub_le_sub_right ((initial_top G).trans hI) 1)
  have hdt : (denominator G).totalDegree ≤ a₁ s :=
    (MvPolynomial.totalDegree_pow _ _).trans
      ((Nat.mul_le_mul_left _ ht).trans (Nat.le_add_left _ _))
  refine ⟨hdt, le_min ((MvPolynomial.degreeOf_le_totalDegree _ _).trans hdt) ?_⟩
  exact (MvPolynomial.degreeOf_pow_le _ _ _).trans
    ((Nat.mul_le_mul_left _ hi).trans (by unfold k; omega))
private theorem padded_band (s : Source) (G : DifferentialPolynomial K 1)
    (hIpos : 0 < I₁ s) (hT : jetTotalDegree G ≤ H s)
    (hI : jetDegree G (Fin.last 1) ≤ I₁ s) (l : Fin k) :
    inBand₁ s (padded G l) := by
  have htd : (padded G l).totalDegree ≤ a₁ s :=
    (totalDegree_commonTaylorNumerator_le center (centeredEquation G) (exponent_sufficient l)).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left t₁
        (Nat.sub_le_sub_right ((jetTotalDegree_map_le embed G).trans hT) 1)) 1)
  refine ⟨htd, le_min ((MvPolynomial.degreeOf_le_totalDegree _ _).trans htd) ?_⟩
  have hm : (centeredEquation G).degreeOf (some (1 : Fin 2)) ≤ I₁ s := by
    rw [show (1 : Fin 2) = Fin.last 1 from rfl]
    apply le_trans _ hI
    simpa only [centeredEquation, jetDegree, MvPolynomial.degreeOf_def] using
      (Multiset.count_le_of_le (some (Fin.last 1))
        (MvPolynomial.degrees_map_le (p := G) (f := embed)))
  exact (degreeOf_commonTaylorNumerator_firstOrder_le center (centeredEquation G)
    (I₁ s) k t₁ exponent_sufficient hm l).trans (by
      have hl := l.isLt
      omega)
private theorem combine_band (s : Source) {m : ℕ} (P : Fin m → InitialRing 1)
    (h : ∀ l, inBand₁ s (P l)) (i : ℕ) : inBand₁ s (combine P i) := by
  unfold inBand₁ combine
  constructor
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro l _
    exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simpa only [MvPolynomial.totalDegree_C, zero_add] using (h l).1)
  · apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
    apply Finset.sup_le
    intro l _
    exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (by
      simpa only [MvPolynomial.degreeOf_C, zero_add] using (h l).2)
theorem chart_bands (s : Source) (G : DifferentialPolynomial K 1)
    (hIpos : 0 < I₁ s) (hT : jetTotalDegree G ≤ H s)
    (hI : jetDegree G (Fin.last 1) ≤ I₁ s) (g : InitialRing 1) :
    inBand₁ s (chart G g).denominator ∧ ∀ i, inBand₁ s ((chart G g).numerator i) := by
  simp only [chart]
  exact ⟨denominator_band s G hT hI, fun i : Fin k =>
    combine_band s (m := k) (padded G) (padded_band s G hIpos hT hI) i.val⟩
private theorem eval_combine {m : ℕ} (u : Fin 2 → Geo) (P : Fin m → InitialRing 1)
    (d : Geo) (hd : d ≠ 0) (a : Fin m → Geo) (h : ∀ l, MvPolynomial.eval u (P l) = d * a l)
    (i : ℕ) : MvPolynomial.eval u (combine P i) / d =
      (taylor (-center) (∑ l : Fin m, monomial l.val (a l))).coeff i := by
  rw [coeff_taylor_sum, combine, map_sum, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  rw [map_mul, MvPolynomial.eval_C, h]
  field_simp
set_option maxRecDepth 200000 in
private theorem output_coeff (G : DifferentialPolynomial K 1) (g : InitialRing 1)
    (u : Fin 2 → Geo) (hu : MvPolynomial.eval u (denominator G) ≠ 0) (i : Fin k) :
    (chart G g).output u i =
      (rationalTaylorPolynomial center (centeredEquation G) k u).coeff i.val := by
  have hS : MvPolynomial.aeval u (sep G) ≠ 0 := by
    intro hz
    apply hu
    change MvPolynomial.eval u (sep G ^ t₁) = 0
    rw [map_pow, ← MvPolynomial.aeval_eq_eval, hz, zero_pow (by decide : t₁ ≠ 0)]
  have he (l : Fin k) : MvPolynomial.eval u (padded G l) =
      MvPolynomial.eval u (denominator G) *
        rationalTaylorCoefficient center (centeredEquation G) u l.val := by
    simpa only [padded, denominator, sep, map_pow, MvPolynomial.aeval_eq_eval] using
      aeval_commonTaylorNumerator center (centeredEquation G) u (exponent_sufficient l) hS
  simp only [Chart.output, chart, rationalTaylorPolynomial, Polynomial.centeredCoefficientPrefix]
  exact eval_combine (m := k) u (padded G) (MvPolynomial.eval u (denominator G)) hu
    (fun l : Fin k => rationalTaylorCoefficient center (centeredEquation G) u l.val) he i.val
set_option maxRecDepth 200000 in
theorem chart_ok (G : DifferentialPolynomial K 1) {g : InitialRing 1}
    (hg : Irreducible g) (hS : ¬ g ∣ denominator G) : ChartOK (chart G g) := by
  refine ⟨hg, hS, ?_⟩
  intro u hu j
  have hd : MvPolynomial.eval u (denominator G) ≠ 0 := hu.2
  let P := rationalTaylorPolynomial center (centeredEquation G) k u
  have hout : (chart G g).output u = fun i => P.coeff i.val := by
    funext i
    exact output_coeff G g u hd i
  have hP : P.degree < k := Polynomial.degree_centeredCoefficientPrefix_lt _ _ _
  rw [hout, readJet_coeff hP]
  have h := congrFun (polynomialJet_rationalTaylorPolynomial center (centeredEquation G)
    (show 1 < k by decide) u) j
  change Polynomial.hasseCoeffAt center j.val P = u j at h
  rw [Polynomial.hasseCoeffAt_apply, ← Polynomial.taylor_coeff] at h
  exact h
def mark (f : (Polynomial K)) : Fin 2 → Geo :=
  polynomialJet center (f.map embed)
private theorem eval_mapped_at_center (f : (Polynomial K)) : (f.map embed).eval center = centerMap f := by
  rw [Polynomial.eval_map]
  change Polynomial.eval₂RingHom embed center f = centerMap f
  congr 1
  apply Polynomial.ringHom_ext
  · intro a
    simp [centerMap, embed]
  · simp [centerMap, center]
private theorem eval_mark (G : DifferentialPolynomial K 1) (f : (Polynomial K)) :
    jetEvaluation (centeredEquation G) center (mark f) =
      centerMap (differentialSpecialization G f) := by
  rw [mark, ← eval_differentialSpecialization, centeredEquation,
    ← map_differentialSpecialization, eval_mapped_at_center]
theorem initial_mark (G : DifferentialPolynomial K 1) (f : (Polynomial K))
    (h : differentialSpecialization G f = 0) : MvPolynomial.eval (mark f) (initial G) = 0 := by
  change MvPolynomial.eval (mark f) (initialJetEquation center (centeredEquation G)) = 0
  rw [← MvPolynomial.aeval_eq_eval, aeval_initialJetEquation, eval_mark, h, map_zero]
private theorem sep_mark (G : DifferentialPolynomial K 1) (f : (Polynomial K))
    (h : differentialSpecialization (separant G (Fin.last 1)) f ≠ 0) :
    MvPolynomial.eval (mark f) (sep G) ≠ 0 := by
  rw [← MvPolynomial.aeval_eq_eval, sep, aeval_initialJetSeparant, centeredEquation, ← map_separant]
  exact fun hz => h (centerMap_injective ((eval_mark _ _).symm.trans (hz.trans (map_zero _).symm)))
theorem denominator_mark (G : DifferentialPolynomial K 1) (f : (Polynomial K))
    (h : differentialSpecialization (separant G (Fin.last 1)) f ≠ 0) :
    MvPolynomial.eval (mark f) (denominator G) ≠ 0 := by
  rw [denominator, map_pow]
  exact pow_ne_zero _ (sep_mark G f h)
theorem chart_contains (G : DifferentialPolynomial K 1) (g : InitialRing 1) (f : (Polynomial K))
    (hf : f.degree < k) (h : differentialSpecialization G f = 0)
    (hs : differentialSpecialization (separant G (Fin.last 1)) f ≠ 0)
    (hg : MvPolynomial.eval (mark f) g = 0) : coeffPoint f ∈ (chart G g).imageSet := by
  let _ : CharP Geo p := charP_of_injective_ringHom embed.injective p
  have hpiv : ∀ i : ℕ, 1 < i → i < k → (i.choose 1 : Geo) ≠ 0 := by
    intro i hlo hhi hz
    rw [Nat.choose_one_right] at hz
    have hdiv := (CharP.cast_eq_zero_iff Geo p i).mp hz
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (hhi.trans (by decide : k < p))) hdiv
  have hsol : differentialSpecialization (centeredEquation G) (f.map embed) = 0 := by
    rw [centeredEquation, ← map_differentialSpecialization, h, Polynomial.map_zero]
  have hsep : jetEvaluation (separant (centeredEquation G) (Fin.last 1)) center (mark f) ≠ 0 := by
    rw [← aeval_initialJetSeparant, MvPolynomial.aeval_eq_eval]
    exact sep_mark G f hs
  have hdeg : (f.map embed).degree < k := Polynomial.degree_map_le.trans_lt hf
  have hr := rationalTaylorPolynomial_polynomialJet center (centeredEquation G) (f.map embed)
    hsol hsep hdeg hpiv
  refine ⟨mark f, ⟨hg, denominator_mark G f hs⟩, ?_⟩
  funext i
  rw [output_coeff G g (mark f) (denominator_mark G f hs), mark, hr, Polynomial.coeff_map]
  rfl
end
end CJ0_6
end
section
namespace CJ0_6
noncomputable section
open CJ0 Polynomial PolynomialDifferential UniqueFactorizationMonoid
open scoped BigOperators
local instance : StrongNormalizationMonoid (DifferentialPolynomial K 1) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
local instance : StrongNormalizationMonoid (InitialRing 1) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
private theorem root_of_associated {G G' : DifferentialPolynomial K 1} {f : (Polynomial K)}
    (ha : Associated G G') (hG : differentialSpecialization G f = 0)
    (hS : differentialSpecialization (separant G (Fin.last 1)) f ≠ 0) :
    differentialSpecialization G' f = 0 ∧
      differentialSpecialization (separant G' (Fin.last 1)) f ≠ 0 := by
  obtain ⟨u, rfl⟩ := ha
  let ev := differentialSpecializationHom f (d := 1)
  have hu : ev (u : DifferentialPolynomial K 1) ≠ 0 :=
    (u.isUnit.map ev).ne_zero
  change ev G = 0 at hG
  change ev (separant G (Fin.last 1)) ≠ 0 at hS
  change ev (G * u) = 0 ∧ ev (separant (G * u) (Fin.last 1)) ≠ 0
  refine ⟨by rw [map_mul, hG, zero_mul], ?_⟩
  rw [separant, MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, hG, zero_mul, add_zero]
  exact mul_ne_zero hS hu
private theorem root_in_factor {P : InitialRing 1} (hP : P ≠ 0) (u : Fin 2 → Geo)
    (h : MvPolynomial.eval u P = 0) :
    ∃ g ∈ normalizedFactors P, MvPolynomial.eval u g = 0 := by
  have hd := map_dvd (MvPolynomial.eval u) (prod_normalizedFactors hP).symm.dvd
  rw [h, zero_dvd_iff, map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hd
  exact hd
private theorem positive_total {g : InitialRing 1} (hg : Irreducible g) :
    1 ≤ g.totalDegree := by
  by_contra! h
  have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.lt_one_iff.mp h)
  have hcoef : g.coeff 0 ≠ 0 := fun hz => hg.ne_zero (by rw [hc, hz, map_zero])
  exact hg.not_isUnit (MvPolynomial.isUnit_iff_eq_C_of_isReduced.mpr
    ⟨g.coeff 0, isUnit_iff_ne_zero.mpr hcoef, hc⟩)
theorem proof : CJ0.c6 := by
  classical
  intro s hs Q hQ
  have hIpos : 0 < I₁ s := by
    have hC := hs.top_pos
    have hJ := hs.index_top
    exact (show 0 < s.J by omega).trans_le (le_max_left _ _)
  let A := (normalizedFactors Q).toFinset
  let B (G : DifferentialPolynomial K 1) :=
    (normalizedFactors (initial G)).toFinset.filter fun g => ¬ g ∣ denominator G
  let T := A.sigma B
  let n := T.card
  let e : Fin n ≃ ↥T := (Fintype.equivFinOfCardEq (Fintype.card_coe T)).symm
  let entry (i : Fin n) := (e i).val
  let F : Family 1 := ⟨n, fun i => chart (entry i).1 (entry i).2⟩
  have hmember (i : Fin n) : (entry i).1 ∈ A ∧ (entry i).2 ∈ B (entry i).1 :=
    Finset.mem_sigma.mp (e i).property
  have hG (i : Fin n) : (entry i).1 ∣ Q :=
    dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (hmember i).1)
  have hg (i : Fin n) : Irreducible (entry i).2 ∧ ¬ (entry i).2 ∣ denominator (entry i).1 := by
    obtain ⟨hm, hd⟩ := Finset.mem_filter.mp (hmember i).2
    exact ⟨irreducible_of_normalized_factor _ (Multiset.mem_toFinset.mp hm), hd⟩
  have hQ' : initial Q ≠ 0 :=
    fun hz => hQ.1 (initial_injective (hz.trans (map_zero initial).symm))
  have hd : (∏ a ∈ T, a.2) ∣ initial Q := by
    have hA : (∏ G ∈ A, G) ∣ Q :=
      (Multiset.toFinset_prod_dvd_prod _).trans (prod_normalizedFactors hQ.1).dvd
    have hm := map_dvd initial hA
    rw [map_prod] at hm
    change (∏ a ∈ A.sigma B, a.2) ∣ initial Q
    rw [Finset.prod_sigma]
    refine (Finset.prod_dvd_prod_of_dvd _ _ (fun G hGA => ?_)).trans hm
    have hne : initial G ≠ 0 := ne_zero_of_dvd_ne_zero hQ'
      (map_dvd initial (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hGA)))
    exact (Finset.prod_dvd_prod_of_subset _ _ id (Finset.filter_subset _ _)).trans
      ((Multiset.toFinset_prod_dvd_prod _).trans (prod_normalizedFactors hne).dvd)
  have heq (d : InitialRing 1 → ℕ) :
      (∑ i : Fin n, d (entry i).2) = ∑ a ∈ T, d a.2 := by
    calc
      _ = ∑ a : ↥T, d a.val.2 := e.sum_comp (fun a : ↥T => d a.val.2)
      _ = _ := Finset.sum_coe_sort T (fun a => d a.2)
  have ht : (∑ i : Fin n, (entry i).2.totalDegree) ≤ H s := by
    rw [heq]
    have h := MvPolynomial.sum_weightedTotalDegree_le_of_prod_dvd
      (1 : Fin 2 → ℕ) T (fun a => a.2) hQ' hd
    simp only [MvPolynomial.weightedTotalDegree_one] at h
    exact h.trans ((initial_total Q).trans hQ.2.1)
  have hi : (∑ i : Fin n, (entry i).2.degreeOf (Fin.last 1)) ≤ I₁ s := by
    rw [heq]
    have h := MvPolynomial.sum_weightedTotalDegree_le_of_prod_dvd
      (Pi.single (Fin.last 1) 1) T (fun a => a.2) hQ' hd
    simp only [MvPolynomial.weightedTotalDegree_piSingle] at h
    exact h.trans ((initial_top Q).trans hQ.2.2)
  have hn : n ≤ H s := by
    calc
      n = ∑ _ : Fin n, 1 := by simp
      _ ≤ ∑ i : Fin n, (entry i).2.totalDegree :=
        Finset.sum_le_sum fun i _ => positive_total (hg i).1
      _ ≤ H s := ht
  refine ⟨F, ⟨hn, fun i => chart_ok _ (hg i).1 (hg i).2, ht, hi, ?_⟩, ?_⟩
  · intro i
    have hT : jetTotalDegree (entry i).1 ≤ H s :=
      (MvPolynomial.weightedTotalDegree_le_of_dvd jetDegreeWeight (hG i) hQ.1).trans hQ.2.1
    have hI : jetDegree (entry i).1 (Fin.last 1) ≤ I₁ s := by
      have hb := MvPolynomial.weightedTotalDegree_le_of_dvd
        (Pi.single (some (Fin.last 1)) 1) (hG i) hQ.1
      simp only [MvPolynomial.weightedTotalDegree_piSingle] at hb
      exact hb.trans hQ.2.2
    exact chart_bands s _ hIpos hT hI _
  · intro f hf hreg
    obtain ⟨G, hGir, hGdvd, hGroot, hGsep⟩ := hreg
    obtain ⟨G', hGA, hGassoc⟩ := exists_mem_normalizedFactors_of_dvd hQ.1 hGir hGdvd
    obtain ⟨hroot, hsep⟩ := root_of_associated hGassoc hGroot hGsep
    have hne : initial G' ≠ 0 := ne_zero_of_dvd_ne_zero hQ'
      (map_dvd initial (dvd_of_mem_normalizedFactors hGA))
    obtain ⟨g, hgM, hgroot⟩ := root_in_factor hne (mark f) (initial_mark G' f hroot)
    have hgden : ¬ g ∣ denominator G' := by
      intro hdvd
      have hm := map_dvd (MvPolynomial.eval (mark f)) hdvd
      rw [hgroot, zero_dvd_iff] at hm
      exact denominator_mark G' f hsep hm
    have ht : (⟨G', g⟩ : Sigma fun _ : DifferentialPolynomial K 1 => InitialRing 1) ∈ T :=
      Finset.mem_sigma.mpr ⟨Multiset.mem_toFinset.mpr hGA,
        Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hgM, hgden⟩⟩
    let a : ↥T := ⟨⟨G', g⟩, ht⟩
    refine ⟨e.symm a, ?_⟩
    change coeffPoint f ∈ (chart (e (e.symm a)).val.1 (e (e.symm a)).val.2).imageSet
    rw [e.apply_symm_apply]
    exact chart_contains G' g f hf hroot hsep hgroot
end
end CJ0_6
end
section
set_option autoImplicit false
namespace CJ0_7
noncomputable section
open CJ0 MvPolynomial
open scoped BigOperators
open K1_13_5_4_2 (ratio_image_degree)
open K1_14_6 (curve_degree_nat)
def equationIdeal {r : ℕ} (T : Chart r) : Ideal (InitialRing r) :=
  Ideal.span {T.equation}
theorem equationIdeal_prime {r : ℕ} {T : Chart r} (hT : ChartOK T) :
    (equationIdeal T).IsPrime :=
  (Ideal.span_singleton_prime hT.irreducible.ne_zero).mpr hT.irreducible.prime
private theorem mem_locus_iff {r : ℕ} (T : Chart r) (u : Fin (r+1) → Geo) :
    u ∈ T.locus ↔ u ∈ zeroLocus Geo (equationIdeal T) ∧ aeval u T.denominator ≠ 0 := by
  rw [equationIdeal, zeroLocus_span]
  simp only [Chart.locus, Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq, aeval_eq_eval]
theorem locus_ideal {r : ℕ} {T : Chart r} (hT : ChartOK T) :
    vanishingIdeal Geo T.locus = equationIdeal T := by
  have hp := equationIdeal_prime hT
  ext g
  rw [mem_vanishingIdeal_iff]
  constructor
  · intro hg
    have hmul : T.denominator * g ∈ vanishingIdeal Geo (zeroLocus Geo (equationIdeal T)) := by
      apply mem_vanishingIdeal_iff.mpr
      intro u hu
      rw [map_mul]
      by_cases hd : aeval u T.denominator = 0
      · rw [hd, zero_mul]
      · rw [hg u ((mem_locus_iff T u).2 ⟨hu, hd⟩), mul_zero]
    rw [vanishingIdeal_zeroLocus_eq_radical, hp.isRadical.radical] at hmul
    exact (hp.mem_or_mem hmul).resolve_left
      (fun hd => hT.nonvanishing (Ideal.mem_span_singleton.mp hd))
  · intro hg u hu
    exact ((mem_locus_iff T u).1 hu).1 g hg
private def jetForm {r : ℕ} (j : Fin (r+1)) : CoeffRing :=
  ∑ i : Fin CJ0.k, C ((i.val.choose j.val : Geo) * center^(i.val-j.val)) * MvPolynomial.X i
private def jetMap (r : ℕ) : InitialRing r →ₐ[Geo] CoeffRing :=
  aeval jetForm
private theorem aeval_jetMap {r : ℕ} (y : Fin CJ0.k → Geo) (g : InitialRing r) :
    aeval y (jetMap r g) = aeval (fun j => readJet y j.val) g := by
  have h : (aeval y).comp (jetMap r) = aeval (fun j => readJet y j.val) := by
    apply algHom_ext
    intro j
    simp only [AlgHom.comp_apply, jetMap, aeval_X, jetForm, map_sum, map_mul, aeval_C,
      Algebra.algebraMap_self, RingHom.id_apply, readJet]
  exact DFunLike.congr_fun h g
theorem image_dimension_lower {r : ℕ} {T : Chart r} (hT : ChartOK T) :
    r ≤ (affineHilbertPolynomial T.ideal).natDegree := by
  have heq : T.ideal.comap (jetMap r) = equationIdeal T := by
    rw [← locus_ideal hT]
    ext g
    change jetMap r g ∈ vanishingIdeal Geo T.imageSet ↔ g ∈ vanishingIdeal Geo T.locus
    simp only [mem_vanishingIdeal_iff]
    constructor
    · intro h u hu
      have hjet : (fun j : Fin (r+1) => readJet (T.output u) j.val) = u :=
        funext (hT.recover u hu)
      simpa only [aeval_jetMap, hjet] using h (T.output u) ⟨u, hu, rfl⟩
    · rintro h _ ⟨u, hu, rfl⟩
      rw [aeval_jetMap, funext (hT.recover u hu)]
      exact h u hu
  have hdim := natDegree_affineHilbertPolynomial_span_singleton_add_one
    hT.irreducible.ne_zero (equationIdeal_prime hT).ne_top
  rw [Nat.card_fin] at hdim
  have h := natDegree_affineHilbertPolynomial_le_of_injective
    (Ideal.quotientMapₐ T.ideal (jetMap r) le_rfl) Ideal.quotientMap_injective
  rw [heq] at h
  change (affineHilbertPolynomial (equationIdeal T)).natDegree + 1 = r+1 at hdim
  omega
private theorem curve_image {T : Chart 1} (hT : ChartOK T) {a d : ℕ}
    (ha : 0 < a) (hd : 0 < d)
    (hD : T.denominator ∈ restrictCappedDegree (Fin 2) Geo 1 a d)
    (hN : ∀ j, T.numerator j ∈ restrictCappedDegree (Fin 2) Geo 1 a d) :
    T.ideal.IsPrime ∧ (affineHilbertPolynomial T.ideal).natDegree = 1 ∧
      affineDegree T.ideal ≤ (cappedDegreeMixedVolume T.equation.totalDegree
        (T.equation.degreeOf (Fin.last 1)) a d : ℕ) := by
  let E := cappedDegreeExponents (Fin 2) 1 a d
  let φ := monomialMap Geo E
  let P := (equationIdeal T).comap φ
  let A := monomialPoint E '' T.locus
  have hA : P = vanishingIdeal Geo A := by
    ext g
    change φ g ∈ equationIdeal T ↔ g ∈ vanishingIdeal Geo A
    rw [← locus_ideal hT, mem_vanishingIdeal_iff, mem_vanishingIdeal_iff]
    constructor
    · rintro h _ ⟨u, hu, rfl⟩
      rw [aeval_monomialPoint]
      exact h u hu
    · intro h u hu
      simpa only [aeval_monomialPoint] using h (monomialPoint E u) ⟨u, hu, rfl⟩
  have hp : P.IsPrime := (equationIdeal_prime hT).comap φ.toRingHom
  have hdim : (affineHilbertPolynomial P).natDegree = 1 := by
    have h := natDegree_affineHilbertPolynomial_comap_span_singleton_add_one_of_surjective
      φ (monomialMap_cappedDegreeExponents_surjective ha hd) hT.irreducible.ne_zero
      (equationIdeal_prime hT).ne_top
    rw [Nat.card_fin] at h
    change (affineHilbertPolynomial P).natDegree + 1 = 2 at h
    omega
  obtain ⟨δ, hδ, hdeg⟩ := curve_degree_nat P hp hdim
  have hone : 1 ≤ affineDegree P := by
    rw [hdeg]
    exact_mod_cast hδ
  let D := monomialLift T.denominator hD
  let N (j : Fin CJ0.k) := monomialLift (T.numerator j) (hN j)
  have eval_lift (u : Fin 2 → Geo) (g : InitialRing 1) (hg : g ∈ restrictSupport Geo E) :
      eval (monomialPoint E u) (monomialLift g hg) = eval u g := by
    simpa only [aeval_eq_eval, monomialMap_monomialLift] using
      aeval_monomialPoint u (monomialLift g hg)
  have eval_D (u : Fin 2 → Geo) :
      eval (monomialPoint E u) D = eval u T.denominator :=
    eval_lift u T.denominator hD
  have eval_N (u : Fin 2 → Geo) (j : Fin CJ0.k) :
      eval (monomialPoint E u) (N j) = eval u (T.numerator j) :=
    eval_lift u (T.numerator j) (hN j)
  have hden (z) (hz : z ∈ A) : eval z D ≠ 0 := by
    obtain ⟨u, hu, rfl⟩ := hz
    rw [eval_D]
    exact hu.2
  obtain ⟨Q, hQ, hdQ, hbQ, hcover⟩ :=
    ratio_image_degree A P hA hp hdim hone D N
      (totalDegree_monomialLift_le_one _ _) (fun j => totalDegree_monomialLift_le_one _ _) hden
  have hle : Q ≤ T.ideal := by
    intro g hg
    rw [Chart.ideal, mem_vanishingIdeal_iff]
    rintro _ ⟨u, hu, rfl⟩
    have hz := hcover (monomialPoint E u) ⟨u, hu, rfl⟩ g hg
    change aeval (fun i => eval u (T.numerator i) / eval u T.denominator) g = 0
    simpa only [eval_D, eval_N] using hz
  have hlower := image_dimension_lower hT
  have heq : Q = T.ideal := by
    refine le_antisymm hle fun g hg => ?_
    by_contra hn
    have hdrop := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
      hQ hn le_rfl).1
    have hsub : Q ⊔ Ideal.span {g} ≤ T.ideal :=
      sup_le hle ((Ideal.span_singleton_le_iff_mem T.ideal).mpr hg)
    have h := natDegree_affineHilbertPolynomial_le_of_le hsub
    omega
  subst Q
  refine ⟨hQ, le_antisymm hdQ hlower, hbQ.trans ?_⟩
  exact affineDegree_comap_cappedDegree_span_singleton_le ha hd hT.irreducible.ne_zero
    (K1_13_5_3.mem_capped T.equation le_rfl le_rfl)
private theorem chart_caps (s : Source) :
    0 < a₁ s ∧ 0 < d₁ s ∧ d₁ s ≤ a₁ s := by
  have ha : 0 < a₁ s := by unfold a₁; omega
  have hk : 1 < CJ0.k := by decide
  have h : 0 < t₁ * (I₁ s - 1) + CJ0.k - 1 := by omega
  exact ⟨ha, by rw [d₁]; exact lt_min ha h, min_le_left _ _⟩
theorem proof : CJ0.c7 := by
  intro s _ F hF
  obtain ⟨ha, hd, hda⟩ := chart_caps s
  have hlocal (i : Fin F.count) := curve_image (hF.chart_ok i) ha hd
    (K1_13_5_3.mem_capped _ (hF.bands i).1.1 (hF.bands i).1.2)
    (fun j => K1_13_5_3.mem_capped _ ((hF.bands i).2 j).1 ((hF.bands i).2 j).2)
  refine ⟨fun i => (hlocal i).1, fun i => (hlocal i).2.1, ?_⟩
  let cap (i : Fin F.count) := cappedDegreeMixedVolume (F.chart i).equation.totalDegree
    ((F.chart i).equation.degreeOf (Fin.last 1)) (a₁ s) (d₁ s)
  have hsum : ∑ i, cap i ≤ R₁ s := by
    simp only [cap, cappedDegreeMixedVolume, Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [R₁, Nat.add_sub_assoc (Nat.mul_le_mul_left _ hda), ← Nat.mul_sub_left_distrib]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ hF.total) (Nat.mul_le_mul_right _ hF.index)
  calc
    (∑ i, affineDegree (F.chart i).ideal) ≤ ∑ i, (cap i : ℚ) :=
      Finset.sum_le_sum fun i _ => (hlocal i).2.2
    _ = ((∑ i, cap i : ℕ) : ℚ) := by rw [Nat.cast_sum]
    _ ≤ (R₁ s : ℚ) := Nat.cast_le.mpr hsum
end
end CJ0_7
end
section
namespace CJ0_8
open Polynomial PolynomialDifferential MvPolynomial
open CJ0 Sol1.C57
private theorem regularRoot_of_simple (Q : DifferentialPolynomial K 1) (f : (Polynomial K)) :
    differentialSpecialization Q f = 0 →
    differentialSpecialization (separant Q (Fin.last 1)) f ≠ 0 →
    RegularRoot Q f := by
  let φ := differentialSpecializationHom (d := 1) f
  induction Q using WfDvdMonoid.induction_on_irreducible with
  | zero =>
    intro _ hsep
    change φ (pderiv (some (Fin.last 1)) 0) ≠ 0 at hsep
    exact (hsep (by simp only [map_zero])).elim
  | unit u hu =>
    intro hroot _
    change φ u = 0 at hroot
    exact ((hu.map φ.toRingHom).ne_zero hroot).elim
  | mul a i _ hi ih =>
    intro hroot hsep
    change φ (i * a) = 0 at hroot
    change φ (pderiv (some (Fin.last 1)) (i * a)) ≠ 0 at hsep
    rw [map_mul, mul_eq_zero] at hroot
    rw [pderiv_mul, map_add, map_mul, map_mul] at hsep
    rcases hroot with h_i | h_a
    · have hiSep : φ (pderiv (some (Fin.last 1)) i) ≠ 0 := by
        intro hz
        exact hsep (by rw [hz, h_i, zero_mul, zero_mul, add_zero])
      exact ⟨i, hi, dvd_mul_right i a, h_i, hiSep⟩
    · have haSep : φ (pderiv (some (Fin.last 1)) a) ≠ 0 := by
        intro hz
        exact hsep (by rw [hz, h_a, mul_zero, mul_zero, add_zero])
      obtain ⟨g, hg, hdvd, hzero, hnonzero⟩ := ih h_a haSep
      exact ⟨g, hg, hdvd.trans (dvd_mul_left a i), hzero, hnonzero⟩
private theorem height_bounds {s : Source} (hs : ShapeOK s) :
    2 ≤ H s ∧ H s < p := by
  have hB : 2 ≤ s.B := by
    have := hs.top_pos
    have := hs.index_top
    have := hs.total_index
    omega
  have hC : 2 * s.C - 1 ≤ s.B - 1 := by
    have := hs.index_top
    have := hs.total_index
    omega
  have hBprod : s.B ≤ s.B * (s.B - 1) := by
    calc
      s.B = s.B * 1 := (Nat.mul_one _).symm
      _ ≤ s.B * (s.B - 1) := Nat.mul_le_mul_left _ (by omega)
  have hc := (le_max_right N (s.B * (s.B - 1))).trans_lt hs.characteristic
  have hmax : H s ≤ s.B * (s.B - 1) := by
    unfold H
    apply max_le hBprod
    exact (Nat.sub_le _ _).trans
      ((Nat.mul_le_mul_right s.B hC).trans_eq (Nat.mul_comm _ _))
  exact ⟨hB.trans (le_max_left _ _), hmax.trans_lt hc⟩
theorem proof : CJ0.c8 := by
  classical
  intro s hs Q hQ
  obtain ⟨hQ, hweight, _⟩ := hQ
  obtain ⟨hH, hHp⟩ := height_bounds hs
  suffices ∃ R : DifferentialPolynomial K 0, R ≠ 0 ∧ jetTotalDegree R ≤ H s * (H s - 1) ∧
      ∀ f : (Polynomial K), differentialSpecialization Q f = 0 → ¬RegularRoot Q f →
        differentialSpecialization R f = 0 by
    obtain ⟨R, hR, hRdeg, hRroot⟩ := this
    refine ⟨orderZeroAsPolynomial R, ?_, ?_, ?_⟩
    · intro hz
      apply hR
      apply orderZeroAsPolynomial_injective
      simpa only [orderZeroAsPolynomial, map_zero, Polynomial.map_zero] using hz
    · exact (orderZeroAsPolynomial_degree R).trans_le hRdeg
    · intro f _ hroot hnreg
      exact (orderZeroAsPolynomial_eval R f).trans (hRroot f hroot hnreg)
  by_cases hb : jetDegree (regularPart 0 Q) (Fin.last 1) = 0
  · have hGone := regular_eq_one_of_degree_zero 0 Q hb
    have hsplit := (split_weight 0 Q).trans hweight
    have hlow : jetTotalDegree (lowerPart 0 Q) ≤ H s := by omega
    have hbudget : H s ≤ H s * (H s - 1) :=
      (Nat.mul_one _).symm.le.trans (Nat.mul_le_mul_left _ (by omega))
    refine ⟨lowerPart 0 Q, lower_ne_zero 0 Q, hlow.trans hbudget, ?_⟩
    intro f hroot _
    rcases root_split 0 Q hQ f hroot with hc | hr
    · exact hc
    · rw [hGone] at hr
      exact (one_ne_zero (by simpa only [differentialSpecialization, map_one] using hr)).elim
  · have hbpos : 0 < jetDegree (regularPart 0 Q) (Fin.last 1) := Nat.pos_of_ne_zero hb
    have hchar : ringChar K = 0 ∨ jetDegree Q (Fin.last 1) < ringChar K := by
      right
      rw [ringChar.eq K p]
      exact (jetDegree_le_total Q (Fin.last 1)).trans_lt (hweight.trans_lt hHp)
    refine ⟨exceptionalEquation 0 Q, exceptional_ne_zero 0 Q hchar,
      exceptional_weight_sharp 0 Q (H s) hweight
        (hbpos.trans_le (jetDegree_le_total (regularPart 0 Q) (Fin.last 1))), ?_⟩
    intro f hroot hnreg
    rcases root_regular_or_exceptional 0 Q hQ f hroot hbpos with hreg | hex
    · have hdvd : regularPart 0 Q ∣ Q := by
        obtain ⟨R, hR⟩ := radicalPrimPart_dvd_self none (topReindex 0 Q)
        refine ⟨(topReindex 0).symm R, ?_⟩
        simpa [regularPart] using congrArg (topReindex 0).symm hR
      obtain ⟨g, hg, hgdvd, hzero, hsep⟩ :=
        regularRoot_of_simple (regularPart 0 Q) f hreg.1 hreg.2
      exact (hnreg ⟨g, hg, hgdvd.trans hdvd, hzero, hsep⟩).elim
    · exact hex
end CJ0_8
end
section
namespace P1
noncomputable section
open Finset
open CJ0 (ShapeOK mem_fullBox Jet fullBox Surplus AgreementOK SilentTail)
open scoped BigOperators
end
end P1
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace P1
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
theorem anchored_list_count {A h cap} (hlist : CJ0.ScalarList A cap) {u deleted} (M : ModelAt h u deleted)
    (Γ : Finset K) (F : FamilyAt A M Γ) (hw : M.overhead ≤ 0) :
    Γ.card ≤ cap := by
  classical
  obtain ⟨hfinite, hprice⟩ := hlist M.word
  have hsub : Γ.image F.scalar ⊆ hfinite.toFinset := by
    intro P hP
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hP
    have mark := F.mark γ hγ
    apply hfinite.mem_toFinset.mpr
    constructor
    · rcases mark.scalar_degree with hz | hd
      · rw [hz, Polynomial.degree_zero]
        exact WithBot.bot_lt_coe k
      · have hn : (F.scalar γ).natDegree < k := by omega
        exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hn)
    · apply mark.bad.agreement.trans
      apply Finset.card_le_card
      intro i hi
      simp only [ReedSolomon.polynomialAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact mark.scalar_hits i hi
  calc
    Γ.card = (Γ.image F.scalar).card := (Finset.card_image_of_injOn F.distinct).symm
    _ ≤ hfinite.toFinset.card := Finset.card_le_card hsub
    _ = _ := (Set.ncard_eq_toFinset_card _ hfinite).symm
    _ ≤ cap := hprice
end
end P1
end

end Merged_RungSplit

-- merged module UpperBranch3
section Merged_UpperBranch3

set_option Elab.async false

-- merged module UpperBase
section Merged_UpperBase
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_7
open P1 (HighBand)
open K1_14 (Shape)
structure Bank where
  shape : Shape
  nodeRows : ℕ
  poleMoment : ℕ
structure Stage where
  reserve : ℕ
  free : Bank
  moving : Bank
structure Grade where
  seedCap : ℕ
  slots : ℕ
def terminal : HighBand → Bank
  | .h2370 => ⟨⟨7550,10506,2218,234728⟩,0x2cfea55aa80000,327528160189452⟩
  | .h2390 => ⟨⟨7550,10506,2218,234728⟩,0x2cfea55aa80000,327528160189452⟩
  | .h2410 => ⟨⟨8000,11132,2339,232545⟩,0x3554eecaf80000,411294790663700⟩
  | .h2420 => ⟨⟨7550,10506,2218,234728⟩,0x2cfea55aa80000,327528160189452⟩
  | .h2440 => ⟨⟨7550,10506,2218,234728⟩,0x2cfea55aa80000,327528160189452⟩
  | .h2460 => ⟨⟨6500,9061,1924,217087⟩,8129289859891200,0xa595a9fe5605⟩
  | .h2480 => ⟨⟨6400,8911,1880,168072⟩,7714756723998720,0x9a1ce5e33829⟩
  | .h2500 => ⟨⟨6400,8911,1880,168072⟩,7714756723998720,0x9a1ce5e33829⟩
  | .h2520 => ⟨⟨6400,8911,1880,168072⟩,7714756723998720,0x9a1ce5e33829⟩
  | .h2530 => ⟨⟨6400,8911,1880,168072⟩,7714756723998720,0x9a1ce5e33829⟩
  | .h2540 => ⟨⟨6400,8911,1880,168072⟩,7714756723998720,0x9a1ce5e33829⟩
  | .h2550 => ⟨⟨6500,9020,1917,171112⟩,8106660550410240,0xa2b8cc152232⟩
  | .h2560 => ⟨⟨6500,9020,1917,171112⟩,8106660550410240,0xa2b8cc152232⟩
  | .h2570 => ⟨⟨6500,9020,1917,171112⟩,8106660550410240,0xa2b8cc152232⟩
  | .h2585 => ⟨⟨6500,9020,1917,171112⟩,8106660550410240,0xa2b8cc152232⟩
  | .h2590 => ⟨⟨6500,9020,1917,171112⟩,8106660550410240,0xa2b8cc152232⟩
  | .h2600 => ⟨⟨6500,9020,1917,171112⟩,8106660550410240,0xa2b8cc152232⟩
  | .h2601 => ⟨⟨6500,9020,1917,171112⟩,8106660550410240,0xa2b8cc152232⟩
  | .h2611 => ⟨⟨6500,9020,1917,171112⟩,8106660550410240,0xa2b8cc152232⟩
  | .h2621 => ⟨⟨6500,9015,1885,158852⟩,8002773617213440,0xa04e1e8be28f⟩
  | .h2640 => ⟨⟨6500,9016,1885,136084⟩,8002773617213440,0xa05cc1f7753a⟩
  | .h2670 => ⟨⟨6500,9016,1885,136084⟩,8002773617213440,0xa05cc1f7753a⟩
  | .h2700 => ⟨⟨6500,9016,1885,136084⟩,8002773617213440,0xa05cc1f7753a⟩
  | .h2750 => ⟨⟨6500,9016,1885,136084⟩,8002773617213440,0xa05cc1f7753a⟩
  | .h2800 => ⟨⟨6500,9024,1885,121313⟩,8002773617213440,0xa0d1fe03ba36⟩
  | .h2900 => ⟨⟨4100,5688,1209,82080⟩,0x73aeffed40000,28309856493724⟩
  | .h2950 => ⟨⟨4100,5688,1209,82080⟩,0x73aeffed40000,28309856493724⟩
  | .h2980 => ⟨⟨4100,5688,1209,82080⟩,0x73aeffed40000,28309856493724⟩
  | .h3000 => ⟨⟨4100,5688,1209,82080⟩,0x73aeffed40000,28309856493724⟩
  | .h3050 => ⟨⟨3200,4436,940,47634⟩,965073932124160,0x98198c13649⟩
  | .h3100 => ⟨⟨3200,4436,940,47634⟩,965073932124160,0x98198c13649⟩
  | .h3200 => ⟨⟨3000,4189,858,50872⟩,779135648792576,8094070384976⟩
  | .h3400 => ⟨⟨1360,1890,386,23288⟩,72306230820864,335491349509⟩
  | .h3555 => ⟨⟨1360,1890,386,23288⟩,72306230820864,335491349509⟩
  | .h4000 => ⟨⟨1024,1426,290,13976⟩,30849337917440,108520269689⟩
  | .h4800 => ⟨⟨492,686,138,6001⟩,3414278537216,5800691370⟩
  | .h7773 => ⟨⟨124,173,32,946⟩,52879163392,22832869⟩
  | .h8000 => ⟨⟨124,173,32,946⟩,52879163392,22832869⟩
  | .h14500 => ⟨⟨40,56,8,289⟩,1610612736,230946⟩
  | .h21473 => ⟨⟨30,42,6,207⟩,711983104,77331⟩
  | .h24000 => ⟨⟨30,42,6,207⟩,711983104,77331⟩
  | .h28323 => ⟨⟨30,42,6,207⟩,711983104,77331⟩
  | .h32433 => ⟨⟨8,11,1,55⟩,17039360,517⟩
def subbank (b : HighBand) (g : Grade) : Bank :=
  let t := terminal b
  { t with shape := { t.shape with U := g.slots } }
def grades : HighBand → List Grade
  | .h2370 =>
    [⟨360,187260⟩,⟨355,188905⟩,⟨350,190909⟩,⟨344,192500⟩,⟨338,194588⟩,⟨332,197324⟩,
     ⟨325,199963⟩,⟨318,203726⟩,⟨310,208092⟩,⟨302,215122⟩,⟨292,224801⟩,⟨279,234728⟩,
     ⟨265,234728⟩,⟨249,234728⟩,⟨230,234728⟩,⟨209,234728⟩,⟨186,234728⟩,⟨161,234728⟩,
     ⟨133,234728⟩,⟨103,234728⟩,⟨71,234728⟩,⟨38,234728⟩,⟨2,234728⟩]
  | .h2390 =>
    [⟨335,180936⟩,⟨330,182459⟩,⟨325,184351⟩,⟨319,185812⟩,⟨313,187793⟩,⟨307,190463⟩,
     ⟨301,194084⟩,⟨294,198002⟩,⟨286,202748⟩,⟨277,209534⟩,⟨267,222151⟩,⟨254,234728⟩,
     ⟨238,234728⟩,⟨220,234728⟩,⟨199,234728⟩,⟨176,234728⟩,⟨151,234728⟩,⟨123,234728⟩,
     ⟨93,234728⟩,⟨61,234728⟩,⟨26,234728⟩]
  | .h2410 =>
    [⟨323,188283⟩,⟨318,189821⟩,⟨313,191754⟩,⟨308,194184⟩,⟨302,196250⟩,⟨296,199074⟩,
     ⟨289,201844⟩,⟨282,206028⟩,⟨275,212500⟩,⟨266,220373⟩,⟨255,232545⟩,⟨243,232545⟩,
     ⟨228,232545⟩,⟨212,232545⟩,⟨193,232545⟩,⟨172,232545⟩,⟨149,232545⟩,⟨123,232545⟩,
     ⟨96,232545⟩,⟨66,232545⟩,⟨35,232545⟩,⟨1,232545⟩]
  | .h2420 =>
    [⟨302,171783⟩,⟨297,173105⟩,⟨292,174809⟩,⟨287,176997⟩,⟨282,179818⟩,⟨276,182458⟩,
     ⟨269,185091⟩,⟨262,189227⟩,⟨255,195920⟩,⟨246,204902⟩,⟨235,224545⟩,⟨219,234728⟩,
     ⟨201,234728⟩,⟨180,234728⟩,⟨156,234728⟩,⟨130,234728⟩,⟨102,234728⟩,⟨70,234728⟩,
     ⟨37,234728⟩,⟨1,234728⟩]
  | .h2440 =>
    [⟨283,166297⟩,⟨279,168400⟩,⟨274,170014⟩,⟨269,172131⟩,⟨263,173890⟩,⟨258,177539⟩,
     ⟨251,180208⟩,⟨244,184576⟩,⟨237,192009⟩,⟨228,203270⟩,⟨215,229192⟩,⟨198,234728⟩,
     ⟨178,234728⟩,⟨155,234728⟩,⟨130,234728⟩,⟨102,234728⟩,⟨71,234728⟩,⟨38,234728⟩,
     ⟨2,234728⟩]
  | .h2460 =>
    [⟨270,140544⟩,⟨265,141516⟩,⟨260,142833⟩,⟨255,144598⟩,⟨250,146964⟩,⟨244,149204⟩,
     ⟨238,152556⟩,⟨231,156597⟩,⟨223,162523⟩,⟨214,174614⟩,⟨200,207594⟩,⟨179,217087⟩,
     ⟨155,217087⟩,⟨128,217087⟩,⟨97,217087⟩,⟨64,217087⟩,⟨27,217087⟩]
  | .h2480 =>
    [⟨254,134193⟩,⟨249,135033⟩,⟨245,137070⟩,⟨240,138744⟩,⟨235,141040⟩,⟨229,143231⟩,
     ⟨223,146620⟩,⟨216,150876⟩,⟨208,157595⟩,⟨198,168072⟩,⟨186,168072⟩,⟨172,168072⟩,
     ⟨155,168072⟩,⟨137,168072⟩,⟨116,168072⟩,⟨92,168072⟩,⟨67,168072⟩,⟨39,168072⟩,
     ⟨10,168072⟩]
  | .h2500 =>
    [⟨240,130495⟩,⟨236,132076⟩,⟨231,133197⟩,⟨226,134788⟩,⟨221,137028⟩,⟨215,139178⟩,
     ⟨209,142631⟩,⟨203,148391⟩,⟨195,156407⟩,⟨184,168072⟩,⟨171,168072⟩,⟨156,168072⟩,
     ⟨138,168072⟩,⟨118,168072⟩,⟨95,168072⟩,⟨70,168072⟩,⟨43,168072⟩,⟨14,168072⟩]
  | .h2520 =>
    [⟨227,126791⟩,⟨223,128284⟩,⟨219,130203⟩,⟨214,131741⟩,⟨209,133962⟩,⟨203,136122⟩,
     ⟨197,139717⟩,⟨191,145978⟩,⟨182,154117⟩,⟨171,168072⟩,⟨157,168072⟩,⟨140,168072⟩,
     ⟨121,168072⟩,⟨100,168072⟩,⟨76,168072⟩,⟨49,168072⟩,⟨21,168072⟩]
  | .h2530 =>
    [⟨221,125072⟩,⟨217,126523⟩,⟨213,128404⟩,⟨208,129899⟩,⟨203,132088⟩,⟨198,135314⟩,
     ⟨192,139046⟩,⟨185,144347⟩,⟨177,155069⟩,⟨165,168072⟩,⟨150,168072⟩,⟨133,168072⟩,
     ⟨113,168072⟩,⟨91,168072⟩,⟨66,168072⟩,⟨39,168072⟩,⟨10,168072⟩]
  | .h2540 =>
    [⟨216,124034⟩,⟨212,125467⟩,⟨207,126408⟩,⟨203,128823⟩,⟨198,131023⟩,⟨192,133195⟩,
     ⟨186,136948⟩,⟨180,143801⟩,⟨171,154186⟩,⟨159,168072⟩,⟨144,168072⟩,⟨126,168072⟩,
     ⟨105,168072⟩,⟨83,168072⟩,⟨57,168072⟩,⟨29,168072⟩]
  | .h2550 =>
    [⟨210,123329⟩,⟨206,124710⟩,⟨202,126534⟩,⟨197,127952⟩,⟨193,131158⟩,⟨187,133345⟩,
     ⟨181,137196⟩,⟨174,142958⟩,⟨166,156109⟩,⟨153,171112⟩,⟨137,171112⟩,⟨119,171112⟩,
     ⟨98,171112⟩,⟨74,171112⟩,⟨47,171112⟩,⟨18,171112⟩]
  | .h2560 =>
    [⟨205,121955⟩,⟨201,123303⟩,⟨197,125098⟩,⟨193,127500⟩,⟨188,129690⟩,⟨182,131880⟩,
     ⟨176,135814⟩,⟨170,143369⟩,⟨161,156802⟩,⟨148,171112⟩,⟨131,171112⟩,⟨112,171112⟩,
     ⟨90,171112⟩,⟨66,171112⟩,⟨39,171112⟩,⟨9,171112⟩]
  | .h2570 =>
    [⟨200,120431⟩,⟨196,121738⟩,⟨192,123496⟩,⟨188,125870⟩,⟨183,128033⟩,⟨178,131389⟩,
     ⟨172,135512⟩,⟨165,142110⟩,⟨156,157496⟩,⟨142,171112⟩,⟨125,171112⟩,⟨105,171112⟩,
     ⟨83,171112⟩,⟨58,171112⟩,⟨30,171112⟩,⟨0,171112⟩]
  | .h2585 =>
    [⟨193,118329⟩,⟨190,120535⟩,⟨185,121285⟩,⟨181,123623⟩,⟨176,125752⟩,⟨171,129132⟩,
     ⟨165,133387⟩,⟨158,140565⟩,⟨149,159797⟩,⟨134,171112⟩,⟨116,171112⟩,⟨96,171112⟩,
     ⟨72,171112⟩,⟨46,171112⟩,⟨18,171112⟩]
  | .h2590 =>
    [⟨191,117868⟩,⟨187,119107⟩,⟨183,120808⟩,⟨179,123146⟩,⟨174,125281⟩,⟨169,128690⟩,
     ⟨163,133026⟩,⟨156,140484⟩,⟨147,161502⟩,⟨132,171112⟩,⟨114,171112⟩,⟨93,171112⟩,
     ⟨69,171112⟩,⟨43,171112⟩,⟨14,171112⟩]
  | .h2600 =>
    [⟨187,116855⟩,⟨183,118069⟩,⟨179,119752⟩,⟨175,122084⟩,⟨170,124222⟩,⟨165,127683⟩,
     ⟨159,132171⟩,⟨152,140213⟩,⟨142,162483⟩,⟨127,171112⟩,⟨108,171112⟩,⟨87,171112⟩,
     ⟨62,171112⟩,⟨35,171112⟩,⟨6,171112⟩]
  | .h2601 =>
    [⟨187,117121⟩,⟨183,118349⟩,⟨179,120048⟩,⟨174,121324⟩,⟨169,123418⟩,⟨164,126825⟩,
     ⟨158,131238⟩,⟨151,139159⟩,⟨142,164008⟩,⟨126,171112⟩,⟨107,171112⟩,⟨86,171112⟩,
     ⟨62,171112⟩,⟨35,171112⟩,⟨5,171112⟩]
  | .h2611 =>
    [⟨182,115033⟩,⟨179,117178⟩,⟨175,118851⟩,⟨170,120098⟩,⟨166,123348⟩,⟨160,125623⟩,
     ⟨154,130168⟩,⟨147,138684⟩,⟨137,165217⟩,⟨121,171112⟩,⟨102,171112⟩,⟨80,171112⟩,
     ⟨55,171112⟩,⟨27,171112⟩]
  | .h2621 =>
    [⟨179,114257⟩,⟨175,115385⟩,⟨171,116987⟩,⟨167,119250⟩,⟨162,121318⟩,⟨157,124773⟩,
     ⟨151,129399⟩,⟨144,138349⟩,⟨134,158852⟩,⟨120,158852⟩,⟨103,158852⟩,⟨83,158852⟩,
     ⟨61,158852⟩,⟨36,158852⟩,⟨9,158852⟩]
  | .h2640 =>
    [⟨172,112240⟩,⟨168,113311⟩,⟨164,114864⟩,⟨160,117101⟩,⟨155,119155⟩,⟨150,122691⟩,
     ⟨144,127626⟩,⟨137,136084⟩,⟨128,136084⟩,⟨117,136084⟩,⟨104,136084⟩,⟨89,136084⟩,
     ⟨72,136084⟩,⟨52,136084⟩,⟨31,136084⟩,⟨7,136084⟩]
  | .h2670 =>
    [⟨162,109262⟩,⟨158,110242⟩,⟨154,111721⟩,⟨150,113918⟩,⟨146,117221⟩,⟨140,119637⟩,
     ⟨135,126780⟩,⟨127,136084⟩,⟨117,136084⟩,⟨105,136084⟩,⟨91,136084⟩,⟨74,136084⟩,
     ⟨56,136084⟩,⟨35,136084⟩,⟨12,136084⟩]
  | .h2700 =>
    [⟨152,105428⟩,⟨149,107356⟩,⟨145,108759⟩,⟨141,110914⟩,⟨137,114256⟩,⟨132,118252⟩,
     ⟨126,124784⟩,⟨118,136084⟩,⟨107,136084⟩,⟨94,136084⟩,⟨79,136084⟩,⟨61,136084⟩,
     ⟨41,136084⟩,⟨18,136084⟩]
  | .h2750 =>
    [⟨139,101227⟩,⟨136,103059⟩,⟨132,104341⟩,⟨128,106435⟩,⟨124,109864⟩,⟨119,114251⟩,
     ⟨113,122694⟩,⟨104,136084⟩,⟨92,136084⟩,⟨77,136084⟩,⟨60,136084⟩,⟨40,136084⟩,
     ⟨18,136084⟩]
  | .h2800 =>
    [⟨128,97769⟩,⟨124,98323⟩,⟨121,100703⟩,⟨117,102764⟩,⟨113,106337⟩,⟨108,111307⟩,
     ⟨101,120802⟩,⟨93,121313⟩,⟨82,121313⟩,⟨69,121313⟩,⟨54,121313⟩,⟨36,121313⟩,
     ⟨16,121313⟩]
  | .h2900 =>
    [⟨112,57619⟩,⟨109,58603⟩,⟨105,59196⟩,⟨102,61346⟩,⟨98,63811⟩,⟨93,67890⟩,
     ⟨85,79524⟩,⟨73,82080⟩,⟨59,82080⟩,⟨41,82080⟩,⟨21,82080⟩]
  | .h2950 =>
    [⟨104,55313⟩,⟨101,56209⟩,⟨98,57594⟩,⟨95,59784⟩,⟨90,61295⟩,⟨85,65923⟩,
     ⟨77,82080⟩,⟨64,82080⟩,⟨48,82080⟩,⟨29,82080⟩,⟨7,82080⟩]
  | .h2980 =>
    [⟨100,54283⟩,⟨98,56003⟩,⟨94,56502⟩,⟨91,58700⟩,⟨87,61411⟩,⟨81,65412⟩,
     ⟨73,82080⟩,⟨59,82080⟩,⟨42,82080⟩,⟨22,82080⟩,⟨0,82080⟩]
  | .h3000 =>
    [⟨98,54041⟩,⟨95,54901⟩,⟨92,56276⟩,⟨88,57496⟩,⟨84,60190⟩,⟨79,65975⟩,
     ⟨70,82080⟩,⟨56,82080⟩,⟨38,82080⟩,⟨18,82080⟩]
  | .h3050 =>
    [⟨93,40951⟩,⟨90,41570⟩,⟨87,42597⟩,⟨84,44334⟩,⟨80,46610⟩,⟨75,47634⟩,
     ⟨68,47634⟩,⟨60,47634⟩,⟨49,47634⟩,⟨37,47634⟩,⟨23,47634⟩,⟨7,47634⟩]
  | .h3100 =>
    [⟨88,39983⟩,⟨85,40565⟩,⟨82,41575⟩,⟨79,43347⟩,⟨75,45808⟩,⟨69,47634⟩,
     ⟨62,47634⟩,⟨53,47634⟩,⟨42,47634⟩,⟨29,47634⟩,⟨13,47634⟩]
  | .h3200 =>
    [⟨80,36401⟩,⟨77,36900⟩,⟨74,37841⟩,⟨71,39620⟩,⟨67,42453⟩,⟨60,50872⟩,
     ⟨50,50872⟩,⟨37,50872⟩,⟨21,50872⟩,⟨2,50872⟩]
  | .h3400 =>
    [⟨70,15376⟩,⟨67,15544⟩,⟨65,16311⟩,⟨61,16745⟩,⟨57,18358⟩,⟨49,23288⟩,
     ⟨37,23288⟩,⟨21,23288⟩,⟨3,23288⟩]
  | .h3555 =>
    [⟨62,14578⟩,⟨59,14704⟩,⟨57,15484⟩,⟨53,15961⟩,⟨49,18488⟩,⟨39,23288⟩,
     ⟨25,23288⟩,⟨7,23288⟩]
  | .h4000 =>
    [⟨48,9762⟩,⟨46,10103⟩,⟨43,10378⟩,⟨40,11382⟩,⟨34,13976⟩,⟨24,13976⟩,
     ⟨11,13976⟩]
  | .h4800 =>
    [⟨37,4167⟩,⟨35,4310⟩,⟨33,4657⟩,⟨29,5474⟩,⟨22,6001⟩,⟨11,6001⟩]
  | .h7773 =>
    [⟨25,886⟩,⟨23,913⟩,⟨21,946⟩,⟨18,946⟩,⟨13,946⟩,⟨7,946⟩]
  | .h8000 =>
    [⟨24,863⟩,⟨23,946⟩,⟨20,946⟩,⟨17,946⟩,⟨12,946⟩,⟨5,946⟩]
  | .h14500 =>
    [⟨18,254⟩,⟨17,284⟩,⟨14,289⟩,⟨10,289⟩,⟨4,289⟩]
  | .h21473 =>
    [⟨14,170⟩,⟨13,196⟩,⟨10,207⟩,⟨5,207⟩]
  | .h24000 =>
    [⟨13,164⟩,⟨12,190⟩,⟨9,207⟩,⟨4,207⟩]
  | .h28323 =>
    [⟨12,160⟩,⟨11,188⟩,⟨8,207⟩,⟨2,207⟩]
  | .h32433 =>
    [⟨13,47⟩,⟨12,55⟩,⟨9,55⟩,⟨4,55⟩]
def stages : HighBand → List Stage
  | .h2370 =>
    [⟨0, ⟨⟨73,101,22,832⟩,12438470656,3108650⟩, ⟨⟨352,489,103,11428⟩,1296449929216,1560122533⟩⟩,
     ⟨1, ⟨⟨78,108,24,956⟩,15341977600,4103823⟩, ⟨⟨345,480,101,14068⟩,1221414354944,1447711168⟩⟩,
     ⟨2, ⟨⟨86,119,26,1020⟩,20190855168,5931589⟩, ⟨⟨385,535,112,14906⟩,1686840279040,2221379895⟩⟩,
     ⟨3, ⟨⟨94,130,29,1070⟩,26637762560,8531244⟩, ⟨⟨411,572,120,16350⟩,2056243380224,2904427648⟩⟩,
     ⟨4, ⟨⟨102,141,31,1137⟩,33533460480,11621252⟩, ⟨⟨438,609,128,17802⟩,2488618188800,3734056387⟩⟩,
     ⟨5, ⟨⟨108,150,33,1232⟩,39862927360,14840297⟩, ⟨⟨522,726,153,17048⟩,4214585819136,7540240839⟩⟩,
     ⟨6, ⟨⟨108,149,33,1546⟩,39862927360,14526868⟩, ⟨⟨570,792,167,17881⟩,5481425797120,10673329627⟩⟩,
     ⟨10, ⟨⟨142,197,43,1669⟩,89085444096,43318982⟩, ⟨⟨696,968,204,22575⟩,9967068774400,23761225895⟩⟩,
     ⟨16, ⟨⟨163,226,50,3081⟩,135467106304,75401397⟩, ⟨⟨851,1183,249,30804⟩,18172149760000,52867790342⟩⟩,
     ⟨18, ⟨⟨221,306,68,1936⟩,335886942208,251865996⟩, ⟨⟨952,1324,279,31969⟩,25456515481600,82958819253⟩⟩,
     ⟨24, ⟨⟨212,294,65,4042⟩,295979712512,214017359⟩, ⟨⟨1115,1550,329,39973⟩,41081354321920,156562227172⟩⟩,
     ⟨32, ⟨⟨261,362,82,4925⟩,560158474240,498527994⟩, ⟨⟨1463,2034,430,46812⟩,92429551140864,462204056864⟩⟩,
     ⟨36, ⟨⟨246,341,75,62625⟩,459094360064,384291762⟩, ⟨⟨1220,1696,357,82384⟩,53453923287040,222859445142⟩⟩,
     ⟨42, ⟨⟨279,386,85,59316⟩,667877376000,629746567⟩, ⟨⟨1240,1725,359,182030⟩,55666189271040,236367501665⟩⟩,
     ⟨54, ⟨⟨534,740,167,4095⟩,4737851195392,8580372579⟩, ⟨⟨2252,3131,661,70633⟩,336378654883840,2588552103973⟩⟩,
     ⟨81, ⟨⟨637,883,197,7240⟩,7963588165632,17210339526⟩, ⟨⟨3474,4830,1019,96525⟩,0x461aa92080000,0xd5013df2ef9⟩⟩,
     ⟨100, ⟨⟨774,1072,239,8656⟩,0xcf60ca00000,37305519000⟩, ⟨⟨4170,5798,1223,116879⟩,0x7934721300000,30381132426145⟩⟩,
     ⟨135, ⟨⟨1042,1443,329,10848⟩,35306242048000,124373325152⟩, ⟨⟨5487,7630,1607,154160⟩,4851195216658432,90974896361155⟩⟩]
  | .h2390 =>
    [⟨0, ⟨⟨73,101,22,787⟩,12438470656,3108650⟩, ⟨⟨352,489,103,10290⟩,1296449929216,1560122533⟩⟩,
     ⟨1, ⟨⟨78,108,24,902⟩,15341977600,4103823⟩, ⟨⟨345,480,101,12353⟩,1221414354944,1447711168⟩⟩,
     ⟨2, ⟨⟨86,119,26,966⟩,20190855168,5931589⟩, ⟨⟨385,535,112,13182⟩,1686840279040,2221379895⟩⟩,
     ⟨3, ⟨⟨94,130,29,1017⟩,26637762560,8531244⟩, ⟨⟨411,572,120,14433⟩,2056243380224,2904427648⟩⟩,
     ⟨4, ⟨⟨102,141,31,1083⟩,33533460480,11621252⟩, ⟨⟨438,609,128,15685⟩,2488618188800,3734056387⟩⟩,
     ⟨5, ⟨⟨108,150,33,1174⟩,39862927360,14840297⟩, ⟨⟨522,726,153,15407⟩,4214585819136,7540240839⟩⟩,
     ⟨6, ⟨⟨108,149,33,1455⟩,39862927360,14526868⟩, ⟨⟨570,792,167,16230⟩,5481425797120,10673329627⟩⟩,
     ⟨10, ⟨⟨142,197,43,1593⟩,89085444096,43318982⟩, ⟨⟨696,968,204,20458⟩,9967068774400,23761225895⟩⟩,
     ⟨16, ⟨⟨163,226,50,2870⟩,135467106304,75401397⟩, ⟨⟨851,1183,249,27645⟩,18172149760000,52867790342⟩⟩,
     ⟨18, ⟨⟨221,306,68,1876⟩,335886942208,251865996⟩, ⟨⟨952,1324,279,28925⟩,25456515481600,82958819253⟩⟩,
     ⟨24, ⟨⟨212,294,65,3777⟩,295979712512,214017359⟩, ⟨⟨1115,1550,329,35970⟩,41081354321920,156562227172⟩⟩,
     ⟨32, ⟨⟨261,362,82,4615⟩,560158474240,498527994⟩, ⟨⟨1463,2034,430,42617⟩,92429551140864,462204056864⟩⟩,
     ⟨36, ⟨⟨246,341,75,32779⟩,459094360064,384291762⟩, ⟨⟨1220,1696,357,68115⟩,53453923287040,222859445142⟩⟩,
     ⟨42, ⟨⟨279,386,85,33956⟩,667877376000,629746567⟩, ⟨⟨1240,1725,359,124946⟩,55666189271040,236367501665⟩⟩,
     ⟨54, ⟨⟨534,740,167,3995⟩,4737851195392,8580372579⟩, ⟨⟨2252,3131,661,64481⟩,336378654883840,2588552103973⟩⟩,
     ⟨81, ⟨⟨637,883,197,6986⟩,7963588165632,17210339526⟩, ⟨⟨3474,4830,1019,89054⟩,0x461aa92080000,0xd5013df2ef9⟩⟩,
     ⟨100, ⟨⟨774,1072,239,8360⟩,0xcf60ca00000,37305519000⟩, ⟨⟨4170,5798,1223,107779⟩,0x7934721300000,30381132426145⟩⟩,
     ⟨135, ⟨⟨1042,1443,329,10507⟩,35306242048000,124373325152⟩, ⟨⟨5487,7630,1607,142158⟩,4851195216658432,90974896361155⟩⟩]
  | .h2410 =>
    [⟨0, ⟨⟨70,97,21,830⟩,10960502784,2641452⟩, ⟨⟨345,480,101,9902⟩,1221414354944,1447711168⟩⟩,
     ⟨1, ⟨⟨76,105,23,935⟩,14043578368,3635193⟩, ⟨⟨331,460,97,12195⟩,0xfb7d680000,1224067218⟩⟩,
     ⟨2, ⟨⟨83,115,25,1012⟩,18136694784,5166252⟩, ⟨⟨385,535,112,12470⟩,1686840279040,2221379895⟩⟩,
     ⟨4, ⟨⟨98,136,30,1130⟩,29954146304,10105062⟩, ⟨⟨438,609,128,14815⟩,2488618188800,3734056387⟩⟩,
     ⟨5, ⟨⟨104,144,32,1230⟩,35837181952,12729182⟩, ⟨⟨478,665,139,15643⟩,3219466485760,5279846034⟩⟩,
     ⟨6, ⟨⟨112,155,34,1292⟩,44177817600,16852996⟩, ⟨⟨522,726,153,16299⟩,4214585819136,7540240839⟩⟩,
     ⟨10, ⟨⟨139,192,43,1614⟩,84950384640,39899742⟩, ⟨⟨666,926,195,20042⟩,8728652283904,19894196946⟩⟩,
     ⟨16, ⟨⟨180,249,56,2076⟩,183858888704,112129912⟩, ⟨⟨851,1183,249,26313⟩,18172149760000,52867790342⟩⟩,
     ⟨18, ⟨⟨231,320,72,1771⟩,386940272640,303742427⟩, ⟨⟨952,1324,279,27627⟩,25456515481600,82958819253⟩⟩,
     ⟨24, ⟨⟨236,327,73,2668⟩,410097287168,329039284⟩, ⟨⟨1140,1585,333,33833⟩,43566030913536,169805327500⟩⟩,
     ⟨32, ⟨⟨226,313,69,20370⟩,356954931200,273860683⟩, ⟨⟨1306,1816,382,44251⟩,65534843944960,292695731388⟩⟩,
     ⟨36, ⟨⟨285,395,89,4947⟩,724956610560,702503867⟩, ⟨⟨1497,2082,436,46755⟩,98329366364160,503613129746⟩⟩,
     ⟨42, ⟨⟨279,386,85,28037⟩,667877376000,629746567⟩, ⟨⟨1463,2035,430,62378⟩,92429551140864,462934950974⟩⟩,
     ⟨54, ⟨⟨448,621,139,4848⟩,2785670594560,4237643334⟩, ⟨⟨2103,2925,614,64377⟩,0xf82ad4d00000,1963246523288⟩⟩,
     ⟨75, ⟨⟨637,883,197,5789⟩,7963588165632,17210339526⟩, ⟨⟨3029,4213,889,81636⟩,818009438945280,8476646500811⟩⟩,
     ⟨81, ⟨⟨478,662,149,89384⟩,3393264025600,5491466699⟩, ⟨⟨2252,3132,661,153452⟩,336378654883840,2591211293428⟩⟩,
     ⟨135, ⟨⟨996,1380,309,11267⟩,30433810841600,102615872119⟩, ⟨⟨5163,7181,1517,139117⟩,0xe65179a180000,71551444218860⟩⟩]
  | .h2420 =>
    [⟨0, ⟨⟨73,101,22,729⟩,12438470656,3108650⟩, ⟨⟨352,489,103,8976⟩,1296449929216,1560122533⟩⟩,
     ⟨1, ⟨⟨78,108,24,833⟩,15341977600,4103823⟩, ⟨⟨345,480,101,10475⟩,1221414354944,1447711168⟩⟩,
     ⟨2, ⟨⟨86,119,26,896⟩,20190855168,5931589⟩, ⟨⟨385,535,112,11268⟩,1686840279040,2221379895⟩⟩,
     ⟨3, ⟨⟨94,130,29,948⟩,26637762560,8531244⟩, ⟨⟨411,572,120,12312⟩,2056243380224,2904427648⟩⟩,
     ⟨4, ⟨⟨102,141,31,1013⟩,33533460480,11621252⟩, ⟨⟨438,609,128,13352⟩,2488618188800,3734056387⟩⟩,
     ⟨5, ⟨⟨108,150,33,1097⟩,39862927360,14840297⟩, ⟨⟨522,726,153,13498⟩,4214585819136,7540240839⟩⟩,
     ⟨6, ⟨⟨108,149,33,1339⟩,39862927360,14526868⟩, ⟨⟨570,792,167,14291⟩,5481425797120,10673329627⟩⟩,
     ⟨10, ⟨⟨142,197,43,1494⟩,89085444096,43318982⟩, ⟨⟨696,968,204,17981⟩,9967068774400,23761225895⟩⟩,
     ⟨16, ⟨⟨163,226,50,2607⟩,135467106304,75401397⟩, ⟨⟨851,1183,249,24026⟩,18172149760000,52867790342⟩⟩,
     ⟨18, ⟨⟨221,306,68,1794⟩,335886942208,251865996⟩, ⟨⟨952,1324,279,25376⟩,25456515481600,82958819253⟩⟩,
     ⟨24, ⟨⟨212,294,65,3446⟩,295979712512,214017359⟩, ⟨⟨1115,1550,329,31357⟩,41081354321920,156562227172⟩⟩,
     ⟨32, ⟨⟨261,362,82,4225⟩,560158474240,498527994⟩, ⟨⟨1463,2034,430,37659⟩,92429551140864,462204056864⟩⟩,
     ⟨36, ⟨⟨246,341,75,19280⟩,459094360064,384291762⟩, ⟨⟨1220,1696,357,54299⟩,53453923287040,222859445142⟩⟩,
     ⟨42, ⟨⟨279,386,85,20856⟩,667877376000,629746567⟩, ⟨⟨1240,1725,359,85536⟩,55666189271040,236367501665⟩⟩,
     ⟨54, ⟨⟨534,740,167,3857⟩,4737851195392,8580372579⟩, ⟨⟨2252,3131,661,57166⟩,336378654883840,2588552103973⟩⟩,
     ⟨81, ⟨⟨637,883,197,6643⟩,7963588165632,17210339526⟩, ⟨⟨3474,4830,1019,79961⟩,0x461aa92080000,0xd5013df2ef9⟩⟩,
     ⟨100, ⟨⟨774,1072,239,7961⟩,0xcf60ca00000,37305519000⟩, ⟨⟨4170,5798,1223,96717⟩,0x7934721300000,30381132426145⟩⟩,
     ⟨135, ⟨⟨1042,1443,329,10043⟩,35306242048000,124373325152⟩, ⟨⟨5487,7630,1607,127567⟩,4851195216658432,90974896361155⟩⟩]
  | .h2440 =>
    [⟨0, ⟨⟨73,101,22,696⟩,12438470656,3108650⟩, ⟨⟨352,489,103,8285⟩,1296449929216,1560122533⟩⟩,
     ⟨1, ⟨⟨78,108,24,793⟩,15341977600,4103823⟩, ⟨⟨345,480,101,9530⟩,1221414354944,1447711168⟩⟩,
     ⟨2, ⟨⟨86,119,26,856⟩,20190855168,5931589⟩, ⟨⟨385,535,112,10292⟩,1686840279040,2221379895⟩⟩,
     ⟨3, ⟨⟨94,130,29,908⟩,26637762560,8531244⟩, ⟨⟨411,572,120,11233⟩,2056243380224,2904427648⟩⟩,
     ⟨4, ⟨⟨102,141,31,972⟩,33533460480,11621252⟩, ⟨⟨438,609,128,12169⟩,2488618188800,3734056387⟩⟩,
     ⟨5, ⟨⟨108,150,33,1053⟩,39862927360,14840297⟩, ⟨⟨522,726,153,12487⟩,4214585819136,7540240839⟩⟩,
     ⟨6, ⟨⟨108,149,33,1272⟩,39862927360,14526868⟩, ⟨⟨570,792,167,13257⟩,5481425797120,10673329627⟩⟩,
     ⟨10, ⟨⟨142,197,43,1436⟩,89085444096,43318982⟩, ⟨⟨696,968,204,16663⟩,9967068774400,23761225895⟩⟩,
     ⟨16, ⟨⟨163,226,50,2460⟩,135467106304,75401397⟩, ⟨⟨851,1183,249,22134⟩,18172149760000,52867790342⟩⟩,
     ⟨18, ⟨⟨221,306,68,1744⟩,335886942208,251865996⟩, ⟨⟨952,1324,279,23493⟩,25456515481600,82958819253⟩⟩,
     ⟨24, ⟨⟨212,294,65,3259⟩,295979712512,214017359⟩, ⟨⟨1115,1550,329,28934⟩,41081354321920,156562227172⟩⟩,
     ⟨32, ⟨⟨261,362,82,4003⟩,560158474240,498527994⟩, ⟨⟨1463,2034,430,35000⟩,92429551140864,462204056864⟩⟩,
     ⟨36, ⟨⟨246,341,75,15194⟩,459094360064,384291762⟩, ⟨⟨1220,1696,357,47947⟩,53453923287040,222859445142⟩⟩,
     ⟨42, ⟨⟨279,386,85,16659⟩,667877376000,629746567⟩, ⟨⟨1240,1725,359,70925⟩,55666189271040,236367501665⟩⟩,
     ⟨54, ⟨⟨534,740,167,3772⟩,4737851195392,8580372579⟩, ⟨⟨2252,3131,661,53223⟩,336378654883840,2588552103973⟩⟩,
     ⟨81, ⟨⟨637,883,197,6437⟩,7963588165632,17210339526⟩, ⟨⟨3474,4830,1019,74962⟩,0x461aa92080000,0xd5013df2ef9⟩⟩,
     ⟨100, ⟨⟨774,1072,239,7721⟩,0xcf60ca00000,37305519000⟩, ⟨⟨4170,5798,1223,90641⟩,0x7934721300000,30381132426145⟩⟩,
     ⟨135, ⟨⟨1042,1443,329,9761⟩,35306242048000,124373325152⟩, ⟨⟨5487,7630,1607,119553⟩,4851195216658432,90974896361155⟩⟩]
  | .h2460 =>
    [⟨0, ⟨⟨67,93,20,767⟩,9604431872,2228964⟩, ⟨⟨280,389,81,8594⟩,649184149504,622002556⟩⟩,
     ⟨1, ⟨⟨73,101,22,859⟩,12438470656,3108650⟩, ⟨⟨325,452,94,9083⟩,0xebc42c0000,1129274177⟩⟩,
     ⟨2, ⟨⟨73,101,22,1210⟩,12438470656,3108650⟩, ⟨⟨360,501,105,9794⟩,1383041597440,1711611949⟩⟩,
     ⟨4, ⟨⟨96,133,30,1019⟩,28613279744,9411251⟩, ⟨⟨438,609,128,11194⟩,2488618188800,3734056387⟩⟩,
     ⟨6, ⟨⟨106,147,33,1243⟩,38240780288,13913593⟩, ⟨⟨485,674,140,13153⟩,3343671623680,5543427992⟩⟩,
     ⟨10, ⟨⟨134,186,40,1563⟩,74214277120,34121885⟩, ⟨⟨593,825,173,16583⟩,6150084362240,12507204741⟩⟩,
     ⟨16, ⟨⟨171,237,52,2065⟩,155191869440,90459259⟩, ⟨⟨804,1118,239,21189⟩,0xe1c7ba00000,42702576640⟩⟩,
     ⟨24, ⟨⟨208,288,64,3307⟩,280399708160,197963022⟩, ⟨⟨985,1370,289,28781⟩,28216312463360,95160984481⟩⟩,
     ⟨36, ⟨⟨253,351,78,8435⟩,503341383680,434522864⟩, ⟨⟨985,1370,289,81077⟩,28216312463360,95160984481⟩⟩,
     ⟨54, ⟨⟨438,607,139,4558⟩,2648411996160,3938005884⟩, ⟨⟨2009,2793,594,51642⟩,0xda7987240000,1649110555219⟩⟩,
     ⟨81, ⟨⟨593,822,188,7144⟩,6549464678400,13184443531⟩, ⟨⟨2730,3796,810,75579⟩,603993145344000,5637020026038⟩⟩]
  | .h2480 =>
    [⟨0, ⟨⟨60,83,18,967⟩,6978011136,1437938⟩, ⟨⟨261,363,75,8390⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,896⟩,10960502784,2641452⟩, ⟨⟨311,432,91,8541⟩,895738707968,952519333⟩⟩,
     ⟨2, ⟨⟨76,105,23,995⟩,14043578368,3635193⟩, ⟨⟨320,445,93,9837⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨86,119,26,1277⟩,20190855168,5931589⟩, ⟨⟨393,546,113,11154⟩,1777873715200,2387645191⟩⟩,
     ⟨5, ⟨⟨98,136,30,1147⟩,29954146304,10105062⟩, ⟨⟨425,591,124,11738⟩,2271510528000,3308696108⟩⟩,
     ⟨6, ⟨⟨105,145,32,1226⟩,36607098880,13013367⟩, ⟨⟨456,634,132,12549⟩,2786771599360,4351456177⟩⟩,
     ⟨10, ⟨⟨124,172,38,1761⟩,60131901440,25559185⟩, ⟨⟨558,776,163,15945⟩,5131801722880,9809476816⟩⟩,
     ⟨16, ⟨⟨171,237,52,1979⟩,155191869440,90459259⟩, ⟨⟨761,1058,225,20153⟩,0xbebc9480000,34123764741⟩⟩,
     ⟨18, ⟨⟨174,241,53,2475⟩,163628974080,96837455⟩, ⟨⟨796,1107,231,22212⟩,0xd723df00000,40283843827⟩⟩,
     ⟨24, ⟨⟨213,295,65,2927⟩,299102633984,216359809⟩, ⟨⟨1021,1420,296,26130⟩,31133182722048,108791212955⟩⟩,
     ⟨32, ⟨⟨237,328,72,5928⟩,409731858432,328780259⟩, ⟨⟨940,1307,273,50653⟩,24338625724416,78245537261⟩⟩,
     ⟨36, ⟨⟨302,418,94,3458⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,35834⟩,72710491734016,336790759551⟩⟩,
     ⟨42, ⟨⟨284,393,87,9495⟩,707135537152,679182041⟩, ⟨⟨1141,1587,334,66994⟩,43751486259200,170894624907⟩⟩,
     ⟨54, ⟨⟨417,578,129,4887⟩,2243231744000,3176332897⟩, ⟨⟨1895,2635,547,50121⟩,0xb40a7fd00000,1282176341862⟩⟩,
     ⟨81, ⟨⟨616,853,192,6396⟩,7246042890240,15095933357⟩, ⟨⟨2651,3686,769,71684⟩,543617725235200,4924236090842⟩⟩,
     ⟨100, ⟨⟨753,1043,235,7567⟩,0xc085f900000,33710825496⟩, ⟨⟨3390,4714,997,83393⟩,0x41467c9ac0000,0xc1a6e7a2433⟩⟩]
  | .h2500 =>
    [⟨0, ⟨⟨60,83,18,896⟩,6978011136,1437938⟩, ⟨⟨261,363,75,7593⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,845⟩,10960502784,2641452⟩, ⟨⟨311,432,91,7858⟩,895738707968,952519333⟩⟩,
     ⟨2, ⟨⟨76,105,23,939⟩,14043578368,3635193⟩, ⟨⟨320,445,93,8968⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨86,119,26,1200⟩,20190855168,5931589⟩, ⟨⟨393,546,113,10253⟩,1777873715200,2387645191⟩⟩,
     ⟨5, ⟨⟨98,136,30,1094⟩,29954146304,10105062⟩, ⟨⟨425,591,124,10827⟩,2271510528000,3308696108⟩⟩,
     ⟨6, ⟨⟨105,145,32,1171⟩,36607098880,13013367⟩, ⟨⟨456,634,132,11582⟩,2786771599360,4351456177⟩⟩,
     ⟨10, ⟨⟨124,172,38,1671⟩,60131901440,25559185⟩, ⟨⟨558,776,163,14698⟩,5131801722880,9809476816⟩⟩,
     ⟨16, ⟨⟨171,237,52,1902⟩,155191869440,90459259⟩, ⟨⟨761,1058,225,18720⟩,0xbebc9480000,34123764741⟩⟩,
     ⟨18, ⟨⟨174,241,53,2357⟩,163628974080,96837455⟩, ⟨⟨796,1107,231,20547⟩,0xd723df00000,40283843827⟩⟩,
     ⟨24, ⟨⟨213,295,65,2798⟩,299102633984,216359809⟩, ⟨⟨1021,1420,296,24343⟩,31133182722048,108791212955⟩⟩,
     ⟨32, ⟨⟨237,328,72,5476⟩,409731858432,328780259⟩, ⟨⟨940,1307,273,43853⟩,24338625724416,78245537261⟩⟩,
     ⟨36, ⟨⟨302,418,94,3336⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,33334⟩,72710491734016,336790759551⟩⟩,
     ⟨42, ⟨⟨284,393,87,8577⟩,707135537152,679182041⟩, ⟨⟨1141,1587,334,57420⟩,43751486259200,170894624907⟩⟩,
     ⟨54, ⟨⟨417,578,129,4719⟩,2243231744000,3176332897⟩, ⟨⟨1895,2635,547,46649⟩,0xb40a7fd00000,1282176341862⟩⟩,
     ⟨81, ⟨⟨616,853,192,6207⟩,7246042890240,15095933357⟩, ⟨⟨2651,3686,769,66661⟩,543617725235200,4924236090842⟩⟩,
     ⟨100, ⟨⟨753,1043,235,7353⟩,0xc085f900000,33710825496⟩, ⟨⟨3390,4714,997,78097⟩,0x41467c9ac0000,0xc1a6e7a2433⟩⟩]
  | .h2520 =>
    [⟨0, ⟨⟨60,83,18,835⟩,6978011136,1437938⟩, ⟨⟨261,363,75,6944⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,801⟩,10960502784,2641452⟩, ⟨⟨311,432,91,7285⟩,895738707968,952519333⟩⟩,
     ⟨2, ⟨⟨76,105,23,890⟩,14043578368,3635193⟩, ⟨⟨320,445,93,8250⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨86,119,26,1133⟩,20190855168,5931589⟩, ⟨⟨393,546,113,9498⟩,1777873715200,2387645191⟩⟩,
     ⟨5, ⟨⟨98,136,30,1047⟩,29954146304,10105062⟩, ⟨⟨425,591,124,10059⟩,2271510528000,3308696108⟩⟩,
     ⟨6, ⟨⟨105,145,32,1121⟩,36607098880,13013367⟩, ⟨⟨456,634,132,10765⟩,2786771599360,4351456177⟩⟩,
     ⟨10, ⟨⟨124,172,38,1590⟩,60131901440,25559185⟩, ⟨⟨558,776,163,13648⟩,5131801722880,9809476816⟩⟩,
     ⟨16, ⟨⟨171,237,52,1831⟩,155191869440,90459259⟩, ⟨⟨761,1058,225,17495⟩,0xbebc9480000,34123764741⟩⟩,
     ⟨18, ⟨⟨174,241,53,2252⟩,163628974080,96837455⟩, ⟨⟨796,1107,231,19135⟩,0xd723df00000,40283843827⟩⟩,
     ⟨24, ⟨⟨213,295,65,2681⟩,299102633984,216359809⟩, ⟨⟨1021,1420,296,22808⟩,31133182722048,108791212955⟩⟩,
     ⟨32, ⟨⟨237,328,72,5094⟩,409731858432,328780259⟩, ⟨⟨940,1307,273,38736⟩,24338625724416,78245537261⟩⟩,
     ⟨36, ⟨⟨302,418,94,3225⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,31192⟩,72710491734016,336790759551⟩⟩,
     ⟨42, ⟨⟨284,393,87,7832⟩,707135537152,679182041⟩, ⟨⟨1141,1587,334,50339⟩,43751486259200,170894624907⟩⟩,
     ⟨54, ⟨⟨417,578,129,4565⟩,2243231744000,3176332897⟩, ⟨⟨1895,2635,547,43671⟩,0xb40a7fd00000,1282176341862⟩⟩,
     ⟨81, ⟨⟨616,853,192,6031⟩,7246042890240,15095933357⟩, ⟨⟨2651,3686,769,62361⟩,543617725235200,4924236090842⟩⟩,
     ⟨100, ⟨⟨753,1043,235,7154⟩,0xc085f900000,33710825496⟩, ⟨⟨3390,4714,997,73503⟩,0x41467c9ac0000,0xc1a6e7a2433⟩⟩]
  | .h2530 =>
    [⟨0, ⟨⟨60,83,18,808⟩,6978011136,1437938⟩, ⟨⟨261,363,75,6663⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,781⟩,10960502784,2641452⟩, ⟨⟨311,432,91,7031⟩,895738707968,952519333⟩⟩,
     ⟨2, ⟨⟨76,105,23,868⟩,14043578368,3635193⟩, ⟨⟨320,445,93,7936⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨86,119,26,1103⟩,20190855168,5931589⟩, ⟨⟨393,546,113,9165⟩,1777873715200,2387645191⟩⟩,
     ⟨5, ⟨⟨98,136,30,1025⟩,29954146304,10105062⟩, ⟨⟨425,591,124,9718⟩,2271510528000,3308696108⟩⟩,
     ⟨6, ⟨⟨105,145,32,1098⟩,36607098880,13013367⟩, ⟨⟨456,634,132,10402⟩,2786771599360,4351456177⟩⟩,
     ⟨10, ⟨⟨124,172,38,1553⟩,60131901440,25559185⟩, ⟨⟨558,776,163,13182⟩,5131801722880,9809476816⟩⟩,
     ⟨16, ⟨⟨171,237,52,1798⟩,155191869440,90459259⟩, ⟨⟨761,1058,225,16947⟩,0xbebc9480000,34123764741⟩⟩,
     ⟨18, ⟨⟨174,241,53,2203⟩,163628974080,96837455⟩, ⟨⟨796,1107,231,18507⟩,0xd723df00000,40283843827⟩⟩,
     ⟨24, ⟨⟨213,295,65,2627⟩,299102633984,216359809⟩, ⟨⟨1021,1420,296,22119⟩,31133182722048,108791212955⟩⟩,
     ⟨32, ⟨⟨237,328,72,4925⟩,409731858432,328780259⟩, ⟨⟨940,1307,273,36624⟩,24338625724416,78245537261⟩⟩,
     ⟨36, ⟨⟨302,418,94,3172⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,30232⟩,72710491734016,336790759551⟩⟩,
     ⟨42, ⟨⟨284,393,87,7510⟩,707135537152,679182041⟩, ⟨⟨1141,1587,334,47448⟩,43751486259200,170894624907⟩⟩,
     ⟨54, ⟨⟨417,578,129,4492⟩,2243231744000,3176332897⟩, ⟨⟨1895,2635,547,42336⟩,0xb40a7fd00000,1282176341862⟩⟩,
     ⟨81, ⟨⟨616,853,192,5948⟩,7246042890240,15095933357⟩, ⟨⟨2651,3686,769,60434⟩,543617725235200,4924236090842⟩⟩,
     ⟨100, ⟨⟨753,1043,235,7060⟩,0xc085f900000,33710825496⟩, ⟨⟨3390,4714,997,71427⟩,0x41467c9ac0000,0xc1a6e7a2433⟩⟩]
  | .h2540 =>
    [⟨0, ⟨⟨60,83,18,782⟩,6978011136,1437938⟩, ⟨⟨261,363,75,6405⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,762⟩,10960502784,2641452⟩, ⟨⟨311,432,91,6796⟩,895738707968,952519333⟩⟩,
     ⟨2, ⟨⟨76,105,23,847⟩,14043578368,3635193⟩, ⟨⟨320,445,93,7647⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨86,119,26,1074⟩,20190855168,5931589⟩, ⟨⟨393,546,113,8856⟩,1777873715200,2387645191⟩⟩,
     ⟨5, ⟨⟨98,136,30,1004⟩,29954146304,10105062⟩, ⟨⟨425,591,124,9402⟩,2271510528000,3308696108⟩⟩,
     ⟨6, ⟨⟨105,145,32,1076⟩,36607098880,13013367⟩, ⟨⟨456,634,132,10066⟩,2786771599360,4351456177⟩⟩,
     ⟨10, ⟨⟨124,172,38,1518⟩,60131901440,25559185⟩, ⟨⟨558,776,163,12751⟩,5131801722880,9809476816⟩⟩,
     ⟨16, ⟨⟨171,237,52,1767⟩,155191869440,90459259⟩, ⟨⟨761,1058,225,16437⟩,0xbebc9480000,34123764741⟩⟩,
     ⟨18, ⟨⟨174,241,53,2157⟩,163628974080,96837455⟩, ⟨⟨796,1107,231,17923⟩,0xd723df00000,40283843827⟩⟩,
     ⟨24, ⟨⟨213,295,65,2576⟩,299102633984,216359809⟩, ⟨⟨1021,1420,296,21475⟩,31133182722048,108791212955⟩⟩,
     ⟨32, ⟨⟨237,328,72,4767⟩,409731858432,328780259⟩, ⟨⟨940,1307,273,34744⟩,24338625724416,78245537261⟩⟩,
     ⟨36, ⟨⟨302,418,94,3122⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,29337⟩,72710491734016,336790759551⟩⟩,
     ⟨42, ⟨⟨284,393,87,7215⟩,707135537152,679182041⟩, ⟨⟨1141,1587,334,44890⟩,43751486259200,170894624907⟩⟩,
     ⟨54, ⟨⟨417,578,129,4422⟩,2243231744000,3176332897⟩, ⟨⟨1895,2635,547,41089⟩,0xb40a7fd00000,1282176341862⟩⟩,
     ⟨81, ⟨⟨616,853,192,5868⟩,7246042890240,15095933357⟩, ⟨⟨2651,3686,769,58637⟩,543617725235200,4924236090842⟩⟩,
     ⟨100, ⟨⟨753,1043,235,6968⟩,0xc085f900000,33710825496⟩, ⟨⟨3390,4714,997,69480⟩,0x41467c9ac0000,0xc1a6e7a2433⟩⟩]
  | .h2550 =>
    [⟨0, ⟨⟨63,87,19,681⟩,8079278080,1737013⟩, ⟨⟨261,363,75,6169⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,744⟩,10960502784,2641452⟩, ⟨⟨285,396,83,6828⟩,687856418816,671136509⟩⟩,
     ⟨2, ⟨⟨76,105,23,827⟩,14043578368,3635193⟩, ⟨⟨320,445,93,7380⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨88,122,27,984⟩,21840265216,6604929⟩, ⟨⟨360,500,105,8886⟩,1383041597440,1700679003⟩⟩,
     ⟨6, ⟨⟨102,141,31,1113⟩,33533460480,11621252⟩, ⟨⟨430,598,125,9968⟩,2345773301760,3457603226⟩⟩,
     ⟨10, ⟨⟨129,179,39,1378⟩,66930606080,29610973⟩, ⟨⟨563,783,165,12308⟩,5283744579584,10192726271⟩⟩,
     ⟨16, ⟨⟨166,230,51,1825⟩,143178334208,80971087⟩, ⟨⟨716,996,207,16368⟩,0x9c3ace00000,26338011946⟩⟩,
     ⟨24, ⟨⟨226,313,70,2217⟩,360816574464,276897427⟩, ⟨⟨969,1347,281,21186⟩,26626732064768,88168769967⟩⟩,
     ⟨36, ⟨⟨302,418,94,3074⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,28499⟩,72710491734016,336790759551⟩⟩,
     ⟨54, ⟨⟨350,485,108,8349⟩,1326705278976,1576220082⟩, ⟨⟨1355,1884,393,57746⟩,72710491734016,336790759551⟩⟩,
     ⟨81, ⟨⟨598,828,189,6076⟩,6700509429760,13552061015⟩, ⟨⟨2571,3575,748,57500⟩,497025580269568,4367526998142⟩⟩]
  | .h2560 =>
    [⟨0, ⟨⟨63,87,19,665⟩,8079278080,1737013⟩, ⟨⟨261,363,75,5951⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,727⟩,10960502784,2641452⟩, ⟨⟨285,396,83,6587⟩,687856418816,671136509⟩⟩,
     ⟨2, ⟨⟨76,105,23,808⟩,14043578368,3635193⟩, ⟨⟨320,445,93,7134⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨88,122,27,962⟩,21840265216,6604929⟩, ⟨⟨360,500,105,8574⟩,1383041597440,1700679003⟩⟩,
     ⟨6, ⟨⟨102,141,31,1090⟩,33533460480,11621252⟩, ⟨⟨430,598,125,9644⟩,2345773301760,3457603226⟩⟩,
     ⟨10, ⟨⟨129,179,39,1352⟩,66930606080,29610973⟩, ⟨⟨563,783,165,11940⟩,5283744579584,10192726271⟩⟩,
     ⟨16, ⟨⟨166,230,51,1791⟩,143178334208,80971087⟩, ⟨⟨716,996,207,15864⟩,0x9c3ace00000,26338011946⟩⟩,
     ⟨24, ⟨⟨226,313,70,2183⟩,360816574464,276897427⟩, ⟨⟨969,1347,281,20572⟩,26626732064768,88168769967⟩⟩,
     ⟨36, ⟨⟨302,418,94,3027⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,27714⟩,72710491734016,336790759551⟩⟩,
     ⟨54, ⟨⟨350,485,108,8066⟩,1326705278976,1576220082⟩, ⟨⟨1355,1884,393,54612⟩,72710491734016,336790759551⟩⟩,
     ⟨81, ⟨⟨598,828,189,5990⟩,6700509429760,13552061015⟩, ⟨⟨2571,3575,748,55849⟩,497025580269568,4367526998142⟩⟩]
  | .h2570 =>
    [⟨0, ⟨⟨63,87,19,649⟩,8079278080,1737013⟩, ⟨⟨261,363,75,5749⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,711⟩,10960502784,2641452⟩, ⟨⟨285,396,83,6365⟩,687856418816,671136509⟩⟩,
     ⟨2, ⟨⟨76,105,23,790⟩,14043578368,3635193⟩, ⟨⟨320,445,93,6905⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨88,122,27,941⟩,21840265216,6604929⟩, ⟨⟨360,500,105,8285⟩,1383041597440,1700679003⟩⟩,
     ⟨6, ⟨⟨102,141,31,1068⟩,33533460480,11621252⟩, ⟨⟨430,598,125,9343⟩,2345773301760,3457603226⟩⟩,
     ⟨10, ⟨⟨129,179,39,1327⟩,66930606080,29610973⟩, ⟨⟨563,783,165,11597⟩,5283744579584,10192726271⟩⟩,
     ⟨16, ⟨⟨166,230,51,1760⟩,143178334208,80971087⟩, ⟨⟨716,996,207,15393⟩,0x9c3ace00000,26338011946⟩⟩,
     ⟨24, ⟨⟨226,313,70,2150⟩,360816574464,276897427⟩, ⟨⟨969,1347,281,19996⟩,26626732064768,88168769967⟩⟩,
     ⟨36, ⟨⟨302,418,94,2982⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,26976⟩,72710491734016,336790759551⟩⟩,
     ⟨54, ⟨⟨350,485,108,7803⟩,1326705278976,1576220082⟩, ⟨⟨1355,1884,393,51821⟩,72710491734016,336790759551⟩⟩,
     ⟨81, ⟨⟨598,828,189,5908⟩,6700509429760,13552061015⟩, ⟨⟨2571,3575,748,54301⟩,497025580269568,4367526998142⟩⟩]
  | .h2585 =>
    [⟨0, ⟨⟨63,87,19,627⟩,8079278080,1737013⟩, ⟨⟨261,363,75,5473⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,688⟩,10960502784,2641452⟩, ⟨⟨285,396,83,6061⟩,687856418816,671136509⟩⟩,
     ⟨2, ⟨⟨76,105,23,765⟩,14043578368,3635193⟩, ⟨⟨320,445,93,6591⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨88,122,27,912⟩,21840265216,6604929⟩, ⟨⟨360,500,105,7889⟩,1383041597440,1700679003⟩⟩,
     ⟨6, ⟨⟨102,141,31,1037⟩,33533460480,11621252⟩, ⟨⟨430,598,125,8929⟩,2345773301760,3457603226⟩⟩,
     ⟨10, ⟨⟨129,179,39,1292⟩,66930606080,29610973⟩, ⟨⟨563,783,165,11122⟩,5283744579584,10192726271⟩⟩,
     ⟨16, ⟨⟨166,230,51,1715⟩,143178334208,80971087⟩, ⟨⟨716,996,207,14743⟩,0x9c3ace00000,26338011946⟩⟩,
     ⟨24, ⟨⟨226,313,70,2103⟩,360816574464,276897427⟩, ⟨⟨969,1347,281,19198⟩,26626732064768,88168769967⟩⟩,
     ⟨36, ⟨⟨302,418,94,2918⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,25951⟩,72710491734016,336790759551⟩⟩,
     ⟨54, ⟨⟨350,485,108,7442⟩,1326705278976,1576220082⟩, ⟨⟨1355,1884,393,48165⟩,72710491734016,336790759551⟩⟩,
     ⟨81, ⟨⟨598,828,189,5790⟩,6700509429760,13552061015⟩, ⟨⟨2571,3575,748,52154⟩,497025580269568,4367526998142⟩⟩]
  | .h2590 =>
    [⟨0, ⟨⟨63,87,19,620⟩,8079278080,1737013⟩, ⟨⟨261,363,75,5388⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,681⟩,10960502784,2641452⟩, ⟨⟨285,396,83,5967⟩,687856418816,671136509⟩⟩,
     ⟨2, ⟨⟨76,105,23,757⟩,14043578368,3635193⟩, ⟨⟨320,445,93,6493⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨88,122,27,903⟩,21840265216,6604929⟩, ⟨⟨360,500,105,7767⟩,1383041597440,1700679003⟩⟩,
     ⟨6, ⟨⟨102,141,31,1027⟩,33533460480,11621252⟩, ⟨⟨430,598,125,8800⟩,2345773301760,3457603226⟩⟩,
     ⟨10, ⟨⟨129,179,39,1281⟩,66930606080,29610973⟩, ⟨⟨563,783,165,10973⟩,5283744579584,10192726271⟩⟩,
     ⟨16, ⟨⟨166,230,51,1700⟩,143178334208,80971087⟩, ⟨⟨716,996,207,14540⟩,0x9c3ace00000,26338011946⟩⟩,
     ⟨24, ⟨⟨226,313,70,2089⟩,360816574464,276897427⟩, ⟨⟨969,1347,281,18948⟩,26626732064768,88168769967⟩⟩,
     ⟨36, ⟨⟨302,418,94,2898⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,25628⟩,72710491734016,336790759551⟩⟩,
     ⟨54, ⟨⟨350,485,108,7330⟩,1326705278976,1576220082⟩, ⟨⟨1355,1884,393,47067⟩,72710491734016,336790759551⟩⟩,
     ⟨81, ⟨⟨598,828,189,5752⟩,6700509429760,13552061015⟩, ⟨⟨2571,3575,748,51481⟩,497025580269568,4367526998142⟩⟩]
  | .h2600 =>
    [⟨0, ⟨⟨63,87,19,606⟩,8079278080,1737013⟩, ⟨⟨261,363,75,5226⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,667⟩,10960502784,2641452⟩, ⟨⟨285,396,83,5787⟩,687856418816,671136509⟩⟩,
     ⟨2, ⟨⟨76,105,23,741⟩,14043578368,3635193⟩, ⟨⟨320,445,93,6307⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨88,122,27,885⟩,21840265216,6604929⟩, ⟨⟨360,500,105,7534⟩,1383041597440,1700679003⟩⟩,
     ⟨6, ⟨⟨102,141,31,1008⟩,33533460480,11621252⟩, ⟨⟨430,598,125,8555⟩,2345773301760,3457603226⟩⟩,
     ⟨10, ⟨⟨129,179,39,1259⟩,66930606080,29610973⟩, ⟨⟨563,783,165,10689⟩,5283744579584,10192726271⟩⟩,
     ⟨16, ⟨⟨166,230,51,1672⟩,143178334208,80971087⟩, ⟨⟨716,996,207,14153⟩,0x9c3ace00000,26338011946⟩⟩,
     ⟨24, ⟨⟨226,313,70,2059⟩,360816574464,276897427⟩, ⟨⟨969,1347,281,18469⟩,26626732064768,88168769967⟩⟩,
     ⟨36, ⟨⟨302,418,94,2858⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,25010⟩,72710491734016,336790759551⟩⟩,
     ⟨54, ⟨⟨350,485,108,7117⟩,1326705278976,1576220082⟩, ⟨⟨1355,1884,393,45025⟩,72710491734016,336790759551⟩⟩,
     ⟨81, ⟨⟨598,828,189,5677⟩,6700509429760,13552061015⟩, ⟨⟨2571,3575,748,50193⟩,497025580269568,4367526998142⟩⟩]
  | .h2601 =>
    [⟨0, ⟨⟨63,87,19,605⟩,8079278080,1737013⟩, ⟨⟨261,363,75,5210⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,665⟩,10960502784,2641452⟩, ⟨⟨285,396,83,5770⟩,687856418816,671136509⟩⟩,
     ⟨2, ⟨⟨76,105,23,740⟩,14043578368,3635193⟩, ⟨⟨320,445,93,6289⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨88,122,27,883⟩,21840265216,6604929⟩, ⟨⟨360,500,105,7512⟩,1383041597440,1700679003⟩⟩,
     ⟨6, ⟨⟨102,141,31,1006⟩,33533460480,11621252⟩, ⟨⟨430,598,125,8531⟩,2345773301760,3457603226⟩⟩,
     ⟨10, ⟨⟨129,179,39,1257⟩,66930606080,29610973⟩, ⟨⟨563,783,165,10661⟩,5283744579584,10192726271⟩⟩,
     ⟨16, ⟨⟨166,230,51,1669⟩,143178334208,80971087⟩, ⟨⟨716,996,207,14115⟩,0x9c3ace00000,26338011946⟩⟩,
     ⟨24, ⟨⟨226,313,70,2056⟩,360816574464,276897427⟩, ⟨⟨969,1347,281,18423⟩,26626732064768,88168769967⟩⟩,
     ⟨36, ⟨⟨302,418,94,2854⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,24951⟩,72710491734016,336790759551⟩⟩,
     ⟨54, ⟨⟨350,485,108,7096⟩,1326705278976,1576220082⟩, ⟨⟨1355,1884,393,44831⟩,72710491734016,336790759551⟩⟩,
     ⟨81, ⟨⟨598,828,189,5670⟩,6700509429760,13552061015⟩, ⟨⟨2571,3575,748,50068⟩,497025580269568,4367526998142⟩⟩]
  | .h2611 =>
    [⟨0, ⟨⟨63,87,19,592⟩,8079278080,1737013⟩, ⟨⟨261,363,75,5060⟩,523794120704,469552476⟩⟩,
     ⟨1, ⟨⟨70,97,21,652⟩,10960502784,2641452⟩, ⟨⟨285,396,83,5604⟩,687856418816,671136509⟩⟩,
     ⟨2, ⟨⟨76,105,23,725⟩,14043578368,3635193⟩, ⟨⟨320,445,93,6116⟩,970346725376,1065292442⟩⟩,
     ⟨4, ⟨⟨88,122,27,866⟩,21840265216,6604929⟩, ⟨⟨360,500,105,7295⟩,1383041597440,1700679003⟩⟩,
     ⟨6, ⟨⟨102,141,31,988⟩,33533460480,11621252⟩, ⟨⟨430,598,125,8302⟩,2345773301760,3457603226⟩⟩,
     ⟨10, ⟨⟨129,179,39,1236⟩,66930606080,29610973⟩, ⟨⟨563,783,165,10395⟩,5283744579584,10192726271⟩⟩,
     ⟨16, ⟨⟨166,230,51,1643⟩,143178334208,80971087⟩, ⟨⟨716,996,207,13753⟩,0x9c3ace00000,26338011946⟩⟩,
     ⟨24, ⟨⟨226,313,70,2028⟩,360816574464,276897427⟩, ⟨⟨969,1347,281,17974⟩,26626732064768,88168769967⟩⟩,
     ⟨36, ⟨⟨302,418,94,2815⟩,859675033600,878663322⟩, ⟨⟨1355,1884,393,24369⟩,72710491734016,336790759551⟩⟩,
     ⟨54, ⟨⟨350,485,108,6898⟩,1326705278976,1576220082⟩, ⟨⟨1355,1884,393,42990⟩,72710491734016,336790759551⟩⟩,
     ⟨81, ⟨⟨598,828,189,5598⟩,6700509429760,13552061015⟩, ⟨⟨2571,3575,748,48859⟩,497025580269568,4367526998142⟩⟩]
  | .h2621 =>
    [⟨0, ⟨⟨61,84,18,627⟩,7237009408,1493513⟩, ⟨⟨241,335,70,5022⟩,416374063104,344250867⟩⟩,
     ⟨1, ⟨⟨67,93,20,689⟩,9604431872,2228964⟩, ⟨⟨280,389,81,5479⟩,649184149504,622002556⟩⟩,
     ⟨2, ⟨⟨73,101,22,762⟩,12438470656,3108650⟩, ⟨⟨325,452,94,5946⟩,0xebc42c0000,1129274177⟩⟩,
     ⟨4, ⟨⟨84,116,26,935⟩,19164561408,5468512⟩, ⟨⟨360,501,105,7094⟩,1383041597440,1711611949⟩⟩,
     ⟨6, ⟨⟨96,133,30,1082⟩,28613279744,9411251⟩, ⟨⟨397,552,116,8294⟩,1855024005120,2523691858⟩⟩,
     ⟨10, ⟨⟨122,169,38,1331⟩,57995165696,24161620⟩, ⟨⟨564,784,164,10144⟩,5280188334080,10186247915⟩⟩,
     ⟨16, ⟨⟨163,226,51,1663⟩,137473556480,76546979⟩, ⟨⟨690,960,205,13589⟩,9812777369600,23224363038⟩⟩,
     ⟨24, ⟨⟨208,288,64,2335⟩,280399708160,197963022⟩, ⟨⟨890,1237,263,17921⟩,20938983735296,63680038117⟩⟩,
     ⟨36, ⟨⟨294,407,91,2912⟩,790165454848,786685883⟩, ⟨⟨1207,1678,356,24374⟩,52079031746560,214874896611⟩⟩,
     ⟨54, ⟨⟨342,474,102,8477⟩,1206829187072,1401097857⟩, ⟨⟨1270,1767,376,46896⟩,60830096031744,264766178555⟩⟩,
     ⟨81, ⟨⟨593,821,188,5608⟩,6549464678400,13132884772⟩, ⟨⟨2465,3428,730,48272⟩,444072230912000,3743926465787⟩⟩]
  | .h2640 =>
    [⟨0, ⟨⟨58,80,17,663⟩,6215172096,1227093⟩, ⟨⟨241,335,70,4744⟩,416374063104,344250867⟩⟩,
     ⟨1, ⟨⟨67,93,20,662⟩,9604431872,2228964⟩, ⟨⟨280,389,81,5199⟩,649184149504,622002556⟩⟩,
     ⟨2, ⟨⟨73,101,22,732⟩,12438470656,3108650⟩, ⟨⟨280,389,81,5907⟩,649184149504,622002556⟩⟩,
     ⟨4, ⟨⟨84,116,26,898⟩,19164561408,5468512⟩, ⟨⟨325,452,94,7028⟩,0xebc42c0000,1129274177⟩⟩,
     ⟨6, ⟨⟨96,133,30,1040⟩,28613279744,9411251⟩, ⟨⟨397,552,116,7865⟩,1855024005120,2523691858⟩⟩,
     ⟨10, ⟨⟨122,169,38,1285⟩,57995165696,24161620⟩, ⟨⟨485,674,140,10117⟩,3343671623680,5543427992⟩⟩,
     ⟨16, ⟨⟨171,237,52,1513⟩,155191869440,90459259⟩, ⟨⟨656,912,194,13114⟩,8405942272000,18868434791⟩⟩,
     ⟨24, ⟨⟨208,288,64,2262⟩,280399708160,197963022⟩, ⟨⟨890,1237,263,17081⟩,20938983735296,63680038117⟩⟩,
     ⟨36, ⟨⟨241,334,76,5761⟩,442881015808,363216208⟩, ⟨⟨846,1177,251,37254⟩,18044378677248,52336361555⟩⟩,
     ⟨54, ⟨⟨417,577,129,3857⟩,2243231744000,3158702492⟩, ⟨⟨1557,2166,459,33665⟩,0x658b06900000,595336955222⟩⟩,
     ⟨81, ⟨⟨564,782,178,5997⟩,5617949081600,10765253509⟩, ⟨⟨2342,3257,695,46983⟩,381495224041472,3056207072401⟩⟩]
  | .h2670 =>
    [⟨0, ⟨⟨58,80,17,616⟩,6215172096,1227093⟩, ⟨⟨241,335,70,4370⟩,416374063104,344250867⟩⟩,
     ⟨1, ⟨⟨67,93,20,623⟩,9604431872,2228964⟩, ⟨⟨280,389,81,4818⟩,649184149504,622002556⟩⟩,
     ⟨2, ⟨⟨73,101,22,690⟩,12438470656,3108650⟩, ⟨⟨280,389,81,5420⟩,649184149504,622002556⟩⟩,
     ⟨4, ⟨⟨84,116,26,846⟩,19164561408,5468512⟩, ⟨⟨325,452,94,6447⟩,0xebc42c0000,1129274177⟩⟩,
     ⟨6, ⟨⟨96,133,30,982⟩,28613279744,9411251⟩, ⟨⟨397,552,116,7281⟩,1855024005120,2523691858⟩⟩,
     ⟨10, ⟨⟨122,169,38,1219⟩,57995165696,24161620⟩, ⟨⟨485,674,140,9340⟩,3343671623680,5543427992⟩⟩,
     ⟨16, ⟨⟨171,237,52,1453⟩,155191869440,90459259⟩, ⟨⟨656,912,194,12176⟩,8405942272000,18868434791⟩⟩,
     ⟨24, ⟨⟨208,288,64,2158⟩,280399708160,197963022⟩, ⟨⟨890,1237,263,15924⟩,20938983735296,63680038117⟩⟩,
     ⟨36, ⟨⟨241,334,76,5218⟩,442881015808,363216208⟩, ⟨⟨846,1177,251,31934⟩,18044378677248,52336361555⟩⟩,
     ⟨54, ⟨⟨417,577,129,3719⟩,2243231744000,3158702492⟩, ⟨⟨1557,2166,459,31173⟩,0x658b06900000,595336955222⟩⟩,
     ⟨81, ⟨⟨564,782,178,5758⟩,5617949081600,10765253509⟩, ⟨⟨2342,3257,695,43777⟩,381495224041472,3056207072401⟩⟩]
  | .h2700 =>
    [⟨0, ⟨⟨58,80,17,576⟩,6215172096,1227093⟩, ⟨⟨241,335,70,4057⟩,416374063104,344250867⟩⟩,
     ⟨1, ⟨⟨67,93,20,590⟩,9604431872,2228964⟩, ⟨⟨280,389,81,4496⟩,649184149504,622002556⟩⟩,
     ⟨2, ⟨⟨73,101,22,653⟩,12438470656,3108650⟩, ⟨⟨280,389,81,5016⟩,649184149504,622002556⟩⟩,
     ⟨4, ⟨⟨84,116,26,800⟩,19164561408,5468512⟩, ⟨⟨325,452,94,5965⟩,0xebc42c0000,1129274177⟩⟩,
     ⟨6, ⟨⟨96,133,30,931⟩,28613279744,9411251⟩, ⟨⟨397,552,116,6788⟩,1855024005120,2523691858⟩⟩,
     ⟨10, ⟨⟨122,169,38,1161⟩,57995165696,24161620⟩, ⟨⟨485,674,140,8687⟩,3343671623680,5543427992⟩⟩,
     ⟨16, ⟨⟨171,237,52,1399⟩,155191869440,90459259⟩, ⟨⟨656,912,194,11380⟩,8405942272000,18868434791⟩⟩,
     ⟨24, ⟨⟨208,288,64,2064⟩,280399708160,197963022⟩, ⟨⟨890,1237,263,14936⟩,20938983735296,63680038117⟩⟩,
     ⟨36, ⟨⟨241,334,76,4777⟩,442881015808,363216208⟩, ⟨⟨846,1177,251,28020⟩,18044378677248,52336361555⟩⟩,
     ⟨54, ⟨⟨417,577,129,3593⟩,2243231744000,3158702492⟩, ⟨⟨1557,2166,459,29070⟩,0x658b06900000,595336955222⟩⟩,
     ⟨81, ⟨⟨564,782,178,5541⟩,5617949081600,10765253509⟩, ⟨⟨2342,3257,695,41040⟩,381495224041472,3056207072401⟩⟩]
  | .h2750 =>
    [⟨0, ⟨⟨58,80,17,521⟩,6215172096,1227093⟩, ⟨⟨241,335,70,3635⟩,416374063104,344250867⟩⟩,
     ⟨1, ⟨⟨67,93,20,543⟩,9604431872,2228964⟩, ⟨⟨280,389,81,4057⟩,649184149504,622002556⟩⟩,
     ⟨2, ⟨⟨73,101,22,602⟩,12438470656,3108650⟩, ⟨⟨280,389,81,4476⟩,649184149504,622002556⟩⟩,
     ⟨4, ⟨⟨84,116,26,736⟩,19164561408,5468512⟩, ⟨⟨325,452,94,5321⟩,0xebc42c0000,1129274177⟩⟩,
     ⟨6, ⟨⟨96,133,30,858⟩,28613279744,9411251⟩, ⟨⟨397,552,116,6117⟩,1855024005120,2523691858⟩⟩,
     ⟨10, ⟨⟨122,169,38,1079⟩,57995165696,24161620⟩, ⟨⟨485,674,140,7804⟩,3343671623680,5543427992⟩⟩,
     ⟨16, ⟨⟨171,237,52,1320⟩,155191869440,90459259⟩, ⟨⟨656,912,194,10291⟩,8405942272000,18868434791⟩⟩,
     ⟨24, ⟨⟨208,288,64,1929⟩,280399708160,197963022⟩, ⟨⟨890,1237,263,13572⟩,20938983735296,63680038117⟩⟩,
     ⟨36, ⟨⟨241,334,76,4203⟩,442881015808,363216208⟩, ⟨⟨846,1177,251,23383⟩,18044378677248,52336361555⟩⟩,
     ⟨54, ⟨⟨417,577,129,3406⟩,2243231744000,3158702492⟩, ⟨⟨1557,2166,459,26208⟩,0x658b06900000,595336955222⟩⟩,
     ⟨81, ⟨⟨564,782,178,5224⟩,5617949081600,10765253509⟩, ⟨⟨2342,3257,695,37268⟩,381495224041472,3056207072401⟩⟩]
  | .h2800 =>
    [⟨0, ⟨⟨54,75,16,521⟩,5084807168,957077⟩, ⟨⟨208,289,59,3341⟩,263771914240,188037891⟩⟩,
     ⟨1, ⟨⟨61,84,18,580⟩,7237009408,1493513⟩, ⟨⟨241,335,70,3682⟩,416374063104,344250867⟩⟩,
     ⟨2, ⟨⟨64,89,19,693⟩,8365015040,1866743⟩, ⟨⟨253,352,72,4126⟩,473877446656,412256635⟩⟩,
     ⟨4, ⟨⟨84,116,26,683⟩,19164561408,5468512⟩, ⟨⟨325,452,94,4820⟩,0xebc42c0000,1129274177⟩⟩,
     ⟨6, ⟨⟨96,133,30,798⟩,28613279744,9411251⟩, ⟨⟨360,501,105,5608⟩,1383041597440,1711611949⟩⟩,
     ⟨10, ⟨⟨128,177,39,962⟩,65782415360,28566713⟩, ⟨⟨485,675,140,7111⟩,3343671623680,5569859382⟩⟩,
     ⟨16, ⟨⟨148,205,45,1550⟩,101033181184,50931776⟩, ⟨⟨593,825,173,9459⟩,6150084362240,12507204741⟩⟩,
     ⟨24, ⟨⟨171,237,52,3316⟩,155191869440,90459259⟩, ⟨⟨564,784,164,17020⟩,5280188334080,10186247915⟩⟩,
     ⟨36, ⟨⟨280,388,88,2508⟩,690965446656,657571316⟩, ⟨⟨1090,1516,321,17105⟩,38326569795584,143016000830⟩⟩,
     ⟨54, ⟨⟨593,821,188,2796⟩,6549464678400,13132884772⟩, ⟨⟨1814,2523,537,24095⟩,0xa10619640000,0xffe856d21a⟩⟩,
     ⟨81, ⟨⟨564,781,178,4956⟩,5617949081600,10721014375⟩, ⟨⟨2225,3095,660,34356⟩,327058085642240,2491104440193⟩⟩]
  | .h2900 =>
    [⟨0, ⟨⟨57,79,17,411⟩,5981601792,1179228⟩, ⟨⟨190,264,55,2760⟩,204603392000,133373011⟩⟩,
     ⟨1, ⟨⟨63,87,19,465⟩,8079278080,1737013⟩, ⟨⟨210,291,61,3114⟩,276307902464,197239731⟩⟩,
     ⟨2, ⟨⟨70,97,21,512⟩,10960502784,2641452⟩, ⟨⟨233,323,68,3448⟩,377887129600,299518730⟩⟩,
     ⟨4, ⟨⟨82,113,25,621⟩,17656184832,4885777⟩, ⟨⟨263,365,76,4158⟩,538134446080,482812069⟩⟩,
     ⟨5, ⟨⟨86,119,26,691⟩,20190855168,5931589⟩, ⟨⟨267,371,79,4677⟩,573046784000,524154366⟩⟩,
     ⟨6, ⟨⟨92,127,28,747⟩,24752685056,7713813⟩, ⟨⟨311,432,91,4812⟩,895738707968,952519333⟩⟩,
     ⟨10, ⟨⟨117,162,36,948⟩,50775982080,20261980⟩, ⟨⟨360,500,105,6434⟩,1383041597440,1700679003⟩⟩,
     ⟨16, ⟨⟨152,210,47,1288⟩,110731722752,56864480⟩, ⟨⟨477,662,139,8553⟩,3204474470400,5203785784⟩⟩,
     ⟨18, ⟨⟨146,202,44,1841⟩,96396902400,47762018⟩, ⟨⟨416,578,117,12802⟩,2071969136640,2944634929⟩⟩,
     ⟨24, ⟨⟨208,288,64,1631⟩,280399708160,197963022⟩, ⟨⟨635,882,186,11342⟩,7570694078464,16399828679⟩⟩,
     ⟨32, ⟨⟨214,296,65,3248⟩,302242856960,218719650⟩, ⟨⟨616,856,174,21430⟩,6723698688000,14142442253⟩⟩,
     ⟨54, ⟨⟨377,521,117,3404⟩,1663607242752,2110154682⟩, ⟨⟨1182,1642,341,22416⟩,48093513646080,193780511162⟩⟩,
     ⟨81, ⟨⟨563,779,173,4572⟩,5476835655680,10401501082⟩, ⟨⟨1729,2402,504,31549⟩,0x89d0bdc40000,893089263594⟩⟩]
  | .h2950 =>
    [⟨0, ⟨⟨57,79,17,386⟩,5981601792,1179228⟩, ⟨⟨190,264,55,2530⟩,204603392000,133373011⟩⟩,
     ⟨1, ⟨⟨63,87,19,436⟩,8079278080,1737013⟩, ⟨⟨210,291,61,2854⟩,276307902464,197239731⟩⟩,
     ⟨2, ⟨⟨70,97,21,482⟩,10960502784,2641452⟩, ⟨⟨233,323,68,3166⟩,377887129600,299518730⟩⟩,
     ⟨4, ⟨⟨82,113,25,585⟩,17656184832,4885777⟩, ⟨⟨263,365,76,3802⟩,538134446080,482812069⟩⟩,
     ⟨5, ⟨⟨86,119,26,651⟩,20190855168,5931589⟩, ⟨⟨267,371,79,4242⟩,573046784000,524154366⟩⟩,
     ⟨6, ⟨⟨92,127,28,703⟩,24752685056,7713813⟩, ⟨⟨311,432,91,4420⟩,895738707968,952519333⟩⟩,
     ⟨10, ⟨⟨117,162,36,896⟩,50775982080,20261980⟩, ⟨⟨360,500,105,5845⟩,1383041597440,1700679003⟩⟩,
     ⟨16, ⟨⟨152,210,47,1220⟩,110731722752,56864480⟩, ⟨⟨477,662,139,7789⟩,3204474470400,5203785784⟩⟩,
     ⟨18, ⟨⟨146,202,44,1699⟩,96396902400,47762018⟩, ⟨⟨416,578,117,10906⟩,2071969136640,2944634929⟩⟩,
     ⟨24, ⟨⟨208,288,64,1556⟩,280399708160,197963022⟩, ⟨⟨635,882,186,10356⟩,7570694078464,16399828679⟩⟩,
     ⟨32, ⟨⟨214,296,65,2973⟩,302242856960,218719650⟩, ⟨⟨616,856,174,18018⟩,6723698688000,14142442253⟩⟩,
     ⟨54, ⟨⟨377,521,117,3240⟩,1663607242752,2110154682⟩, ⟨⟨1182,1642,341,20408⟩,48093513646080,193780511162⟩⟩,
     ⟨81, ⟨⟨563,779,173,4381⟩,5476835655680,10401501082⟩, ⟨⟨1729,2402,504,28866⟩,0x89d0bdc40000,893089263594⟩⟩]
  | .h2980 =>
    [⟨0, ⟨⟨57,79,17,372⟩,5981601792,1179228⟩, ⟨⟨190,264,55,2413⟩,204603392000,133373011⟩⟩,
     ⟨1, ⟨⟨63,87,19,421⟩,8079278080,1737013⟩, ⟨⟨210,291,61,2721⟩,276307902464,197239731⟩⟩,
     ⟨2, ⟨⟨70,97,21,466⟩,10960502784,2641452⟩, ⟨⟨233,323,68,3022⟩,377887129600,299518730⟩⟩,
     ⟨4, ⟨⟨82,113,25,566⟩,17656184832,4885777⟩, ⟨⟨263,365,76,3622⟩,538134446080,482812069⟩⟩,
     ⟨5, ⟨⟨86,119,26,629⟩,20190855168,5931589⟩, ⟨⟨267,371,79,4024⟩,573046784000,524154366⟩⟩,
     ⟨6, ⟨⟨92,127,28,680⟩,24752685056,7713813⟩, ⟨⟨311,432,91,4219⟩,895738707968,952519333⟩⟩,
     ⟨10, ⟨⟨117,162,36,869⟩,50775982080,20261980⟩, ⟨⟨360,500,105,5548⟩,1383041597440,1700679003⟩⟩,
     ⟨16, ⟨⟨152,210,47,1184⟩,110731722752,56864480⟩, ⟨⟨477,662,139,7402⟩,3204474470400,5203785784⟩⟩,
     ⟨18, ⟨⟨146,202,44,1626⟩,96396902400,47762018⟩, ⟨⟨416,578,117,10038⟩,2071969136640,2944634929⟩⟩,
     ⟨24, ⟨⟨208,288,64,1515⟩,280399708160,197963022⟩, ⟨⟨635,882,186,9856⟩,7570694078464,16399828679⟩⟩,
     ⟨32, ⟨⟨214,296,65,2833⟩,302242856960,218719650⟩, ⟨⟨616,856,174,16485⟩,6723698688000,14142442253⟩⟩,
     ⟨54, ⟨⟨377,521,117,3151⟩,1663607242752,2110154682⟩, ⟨⟨1182,1642,341,19394⟩,48093513646080,193780511162⟩⟩,
     ⟨81, ⟨⟨563,779,173,4277⟩,5476835655680,10401501082⟩, ⟨⟨1729,2402,504,27501⟩,0x89d0bdc40000,893089263594⟩⟩]
  | .h3000 =>
    [⟨0, ⟨⟨57,79,17,364⟩,5981601792,1179228⟩, ⟨⟨190,264,55,2341⟩,204603392000,133373011⟩⟩,
     ⟨1, ⟨⟨63,87,19,412⟩,8079278080,1737013⟩, ⟨⟨210,291,61,2640⟩,276307902464,197239731⟩⟩,
     ⟨2, ⟨⟨70,97,21,456⟩,10960502784,2641452⟩, ⟨⟨233,323,68,2934⟩,377887129600,299518730⟩⟩,
     ⟨4, ⟨⟨82,113,25,554⟩,17656184832,4885777⟩, ⟨⟨263,365,76,3512⟩,538134446080,482812069⟩⟩,
     ⟨5, ⟨⟨86,119,26,615⟩,20190855168,5931589⟩, ⟨⟨267,371,79,3893⟩,573046784000,524154366⟩⟩,
     ⟨6, ⟨⟨92,127,28,666⟩,24752685056,7713813⟩, ⟨⟨311,432,91,4097⟩,895738707968,952519333⟩⟩,
     ⟨10, ⟨⟨117,162,36,852⟩,50775982080,20261980⟩, ⟨⟨360,500,105,5370⟩,1383041597440,1700679003⟩⟩,
     ⟨16, ⟨⟨152,210,47,1161⟩,110731722752,56864480⟩, ⟨⟨477,662,139,7169⟩,3204474470400,5203785784⟩⟩,
     ⟨18, ⟨⟨146,202,44,1581⟩,96396902400,47762018⟩, ⟨⟨416,578,117,9540⟩,2071969136640,2944634929⟩⟩,
     ⟨24, ⟨⟨208,288,64,1490⟩,280399708160,197963022⟩, ⟨⟨635,882,186,9553⟩,7570694078464,16399828679⟩⟩,
     ⟨32, ⟨⟨214,296,65,2748⟩,302242856960,218719650⟩, ⟨⟨616,856,174,15614⟩,6723698688000,14142442253⟩⟩,
     ⟨54, ⟨⟨377,521,117,3096⟩,1663607242752,2110154682⟩, ⟨⟨1182,1642,341,18782⟩,48093513646080,193780511162⟩⟩,
     ⟨81, ⟨⟨563,779,173,4211⟩,5476835655680,10401501082⟩, ⟨⟨1729,2402,504,26673⟩,0x89d0bdc40000,893089263594⟩⟩]
  | .h3050 =>
    [⟨0, ⟨⟨61,84,18,339⟩,7237009408,1493513⟩, ⟨⟨163,226,47,2188⟩,129348141056,71917600⟩⟩,
     ⟨1, ⟨⟨60,83,18,404⟩,6978011136,1437938⟩, ⟨⟨180,250,52,2471⟩,173948272640,107314266⟩⟩,
     ⟨2, ⟨⟨67,93,20,449⟩,9604431872,2228964⟩, ⟨⟨198,275,58,2773⟩,233389424640,158318504⟩⟩,
     ⟨4, ⟨⟨76,105,23,565⟩,14043578368,3635193⟩, ⟨⟨238,330,69,3323⟩,400554721280,324441038⟩⟩,
     ⟨5, ⟨⟨91,126,27,568⟩,23524802560,7319461⟩, ⟨⟨267,371,79,3605⟩,573046784000,524154366⟩⟩,
     ⟨6, ⟨⟨88,122,27,658⟩,21840265216,6604929⟩, ⟨⟨263,365,76,3946⟩,538134446080,482812069⟩⟩,
     ⟨10, ⟨⟨111,153,34,871⟩,43306188800,16168606⟩, ⟨⟨325,451,94,5190⟩,0xebc42c0000,1121285152⟩⟩,
     ⟨16, ⟨⟨144,199,44,1197⟩,93483171840,45530198⟩, ⟨⟨430,597,126,6984⟩,2360023711744,3460443224⟩⟩,
     ⟨18, ⟨⟨131,181,39,2203⟩,69258444800,30680913⟩, ⟨⟨352,489,98,12676⟩,1248242958336,1500908090⟩⟩,
     ⟨32, ⟨⟨239,330,74,1982⟩,426141286400,342375034⟩, ⟨⟨690,958,195,12100⟩,9445098127360,22186492210⟩⟩,
     ⟨54, ⟨⟨378,523,117,2955⟩,1673490333696,2136298939⟩, ⟨⟨1090,1513,321,18349⟩,38326569795584,142108334350⟩⟩,
     ⟨81, ⟨⟨530,734,165,4358⟩,4616711045120,8281195601⟩, ⟨⟨1589,2206,462,25928⟩,0x6aca9e4c0000,634629047724⟩⟩]
  | .h3100 =>
    [⟨0, ⟨⟨61,84,18,324⟩,7237009408,1493513⟩, ⟨⟨163,226,47,2028⟩,129348141056,71917600⟩⟩,
     ⟨1, ⟨⟨60,83,18,383⟩,6978011136,1437938⟩, ⟨⟨180,250,52,2291⟩,173948272640,107314266⟩⟩,
     ⟨2, ⟨⟨67,93,20,427⟩,9604431872,2228964⟩, ⟨⟨198,275,58,2571⟩,233389424640,158318504⟩⟩,
     ⟨4, ⟨⟨76,105,23,535⟩,14043578368,3635193⟩, ⟨⟨238,330,69,3088⟩,400554721280,324441038⟩⟩,
     ⟨5, ⟨⟨91,126,27,544⟩,23524802560,7319461⟩, ⟨⟨267,371,79,3365⟩,573046784000,524154366⟩⟩,
     ⟨6, ⟨⟨88,122,27,626⟩,21840265216,6604929⟩, ⟨⟨263,365,76,3653⟩,538134446080,482812069⟩⟩,
     ⟨10, ⟨⟨111,153,34,829⟩,43306188800,16168606⟩, ⟨⟨325,451,94,4793⟩,0xebc42c0000,1121285152⟩⟩,
     ⟨16, ⟨⟨144,199,44,1139⟩,93483171840,45530198⟩, ⟨⟨430,597,126,6460⟩,2360023711744,3460443224⟩⟩,
     ⟨18, ⟨⟨131,181,39,1995⟩,69258444800,30680913⟩, ⟨⟨352,489,98,10663⟩,1248242958336,1500908090⟩⟩,
     ⟨32, ⟨⟨239,330,74,1897⟩,426141286400,342375034⟩, ⟨⟨690,958,195,11144⟩,9445098127360,22186492210⟩⟩,
     ⟨54, ⟨⟨378,523,117,2842⟩,1673490333696,2136298939⟩, ⟨⟨1090,1513,321,17012⟩,38326569795584,142108334350⟩⟩,
     ⟨81, ⟨⟨530,734,165,4190⟩,4616711045120,8281195601⟩, ⟨⟨1589,2206,462,24107⟩,0x6aca9e4c0000,634629047724⟩⟩]
  | .h3200 =>
    [⟨0, ⟨⟨44,61,13,369⟩,2798387200,428950⟩, ⟨⟨137,191,38,1822⟩,75017486336,35709156⟩⟩,
     ⟨1, ⟨⟨47,65,14,465⟩,3407872000,552788⟩, ⟨⟨153,213,43,2057⟩,105135472640,55592342⟩⟩,
     ⟨2, ⟨⟨52,72,16,527⟩,4679270400,841239⟩, ⟨⟨171,238,48,2303⟩,146151047168,86226612⟩⟩,
     ⟨4, ⟨⟨63,87,19,638⟩,8079278080,1737013⟩, ⟨⟨208,290,58,2804⟩,260378460160,187629114⟩⟩,
     ⟨5, ⟨⟨70,97,21,657⟩,10960502784,2641452⟩, ⟨⟨239,333,67,2994⟩,395393892352,326459980⟩⟩,
     ⟨6, ⟨⟨76,105,23,700⟩,14043578368,3635193⟩, ⟨⟨254,354,72,3226⟩,478049206272,419800747⟩⟩,
     ⟨10, ⟨⟨99,137,30,888⟩,30636769280,10343855⟩, ⟨⟨340,473,96,4161⟩,1137596432384,1327710081⟩⟩,
     ⟨16, ⟨⟨137,190,42,1112⟩,80832888832,37902732⟩, ⟨⟨443,617,127,5585⟩,2537151266816,3870016120⟩⟩,
     ⟨18, ⟨⟨131,181,39,1691⟩,69258444800,30680913⟩, ⟨⟨393,547,109,6966⟩,1729602519040,2335147916⟩⟩,
     ⟨24, ⟨⟨269,373,84,1191⟩,610154577920,559058208⟩, ⟨⟨738,1028,211,7528⟩,0xa9980180000,29591361675⟩⟩,
     ⟨32, ⟨⟨239,331,74,1745⟩,426141286400,345715284⟩, ⟨⟨772,1075,216,9452⟩,0xbee14380000,34787713530⟩⟩,
     ⟨54, ⟨⟨360,499,110,2840⟩,1432542248960,1751700680⟩, ⟨⟨1200,1672,344,14510⟩,50076691988480,206796824881⟩⟩]
  | .h3400 =>
    [⟨0, ⟨⟨50,69,15,267⟩,4099932160,701658⟩, ⟨⟨122,169,35,1424⟩,54567370752,22700544⟩⟩,
     ⟨1, ⟨⟨56,77,17,307⟩,5752750080,1087341⟩, ⟨⟨141,196,41,1626⟩,84641579008,41100650⟩⟩,
     ⟨2, ⟨⟨58,80,17,366⟩,6215172096,1227093⟩, ⟨⟨148,205,42,1858⟩,95960170496,48317762⟩⟩,
     ⟨4, ⟨⟨73,101,22,427⟩,12438470656,3108650⟩, ⟨⟨189,262,55,2245⟩,202217881600,130167655⟩⟩,
     ⟨5, ⟨⟨78,108,23,477⟩,14874050560,3975609⟩, ⟨⟨203,282,58,2437⟩,246690611200,171576630⟩⟩,
     ⟨6, ⟨⟨84,116,26,508⟩,19164561408,5468512⟩, ⟨⟨208,289,59,2694⟩,263771914240,188037891⟩⟩,
     ⟨10, ⟨⟨106,147,32,681⟩,37385666560,13594640⟩, ⟨⟨267,371,79,3611⟩,573046784000,524154366⟩⟩,
     ⟨16, ⟨⟨141,195,44,917⟩,89201049600,42666368⟩, ⟨⟨360,500,105,4821⟩,1383041597440,1700679003⟩⟩,
     ⟨18, ⟨⟨124,171,38,1529⟩,60131901440,25087376⟩, ⟨⟨282,392,79,9433⟩,647128678400,625249766⟩⟩,
     ⟨32, ⟨⟨239,330,74,1539⟩,426141286400,342375034⟩, ⟨⟨582,808,165,8399⟩,5689291046912,11274483946⟩⟩]
  | .h3555 =>
    [⟨0, ⟨⟨50,69,15,239⟩,4099932160,701658⟩, ⟨⟨122,169,35,1208⟩,54567370752,22700544⟩⟩,
     ⟨1, ⟨⟨56,77,17,275⟩,5752750080,1087341⟩, ⟨⟨141,196,41,1390⟩,84641579008,41100650⟩⟩,
     ⟨2, ⟨⟨58,80,17,324⟩,6215172096,1227093⟩, ⟨⟨148,205,42,1569⟩,95960170496,48317762⟩⟩,
     ⟨4, ⟨⟨73,101,22,386⟩,12438470656,3108650⟩, ⟨⟨189,262,55,1930⟩,202217881600,130167655⟩⟩,
     ⟨5, ⟨⟨78,108,23,431⟩,14874050560,3975609⟩, ⟨⟨203,282,58,2094⟩,246690611200,171576630⟩⟩,
     ⟨6, ⟨⟨84,116,26,459⟩,19164561408,5468512⟩, ⟨⟨208,289,59,2290⟩,263771914240,188037891⟩⟩,
     ⟨10, ⟨⟨106,147,32,618⟩,37385666560,13594640⟩, ⟨⟨267,371,79,3077⟩,573046784000,524154366⟩⟩,
     ⟨16, ⟨⟨141,195,44,836⟩,89201049600,42666368⟩, ⟨⟨360,500,105,4136⟩,1383041597440,1700679003⟩⟩,
     ⟨18, ⟨⟨124,171,38,1286⟩,60131901440,25087376⟩, ⟨⟨282,392,79,6571⟩,647128678400,625249766⟩⟩,
     ⟨32, ⟨⟨239,330,74,1419⟩,426141286400,342375034⟩, ⟨⟨582,808,165,7161⟩,5689291046912,11274483946⟩⟩]
  | .h4000 =>
    [⟨0, ⟨⟨34,47,10,213⟩,1326448640,156979⟩, ⟨⟨74,103,20,891⟩,11955077120,3080759⟩⟩,
     ⟨1, ⟨⟨40,55,12,248⟩,2146959360,292447⟩, ⟨⟨92,128,25,1008⟩,22767992832,7261007⟩⟩,
     ⟨2, ⟨⟨44,61,13,293⟩,2798387200,428950⟩, ⟨⟨101,140,28,1182⟩,30431510528,10519447⟩⟩,
     ⟨4, ⟨⟨56,77,17,358⟩,5752750080,1087341⟩, ⟨⟨128,178,36,1463⟩,61978705920,27365980⟩⟩,
     ⟨5, ⟨⟨61,84,18,401⟩,7237009408,1493513⟩, ⟨⟨138,192,39,1631⟩,77736181760,37038913⟩⟩,
     ⟨6, ⟨⟨67,93,20,427⟩,9604431872,2228964⟩, ⟨⟨148,206,42,1804⟩,95960170496,49074132⟩⟩,
     ⟨16, ⟨⟨111,154,34,879⟩,43306188800,16508386⟩, ⟨⟨253,352,72,3541⟩,473877446656,412256635⟩⟩,
     ⟨18, ⟨⟨96,133,28,3504⟩,27200585728,8935438⟩, ⟨⟨203,282,58,13680⟩,246690611200,171576630⟩⟩,
     ⟨24, ⟨⟨208,288,64,916⟩,280399708160,197963022⟩, ⟨⟨417,580,119,4232⟩,2110206771200,3017027973⟩⟩,
     ⟨32, ⟨⟨182,252,55,1699⟩,185930350592,114923195⟩, ⟨⟨440,612,121,6126⟩,2408228061184,3630535593⟩⟩]
  | .h4800 =>
    [⟨0, ⟨⟨24,33,7,175⟩,489684992,40841⟩, ⟨⟨50,70,13,573⟩,3701211136,661273⟩⟩,
     ⟨2, ⟨⟨34,47,10,242⟩,1326448640,156979⟩, ⟨⟨74,103,20,778⟩,11955077120,3080759⟩⟩,
     ⟨5, ⟨⟨50,69,15,328⟩,4099932160,701658⟩, ⟨⟨111,155,30,1087⟩,39462109184,15324191⟩⟩,
     ⟨10, ⟨⟨70,97,21,544⟩,10960502784,2641452⟩, ⟨⟨155,216,41,1739⟩,104371585024,56031580⟩⟩,
     ⟨18, ⟨⟨118,163,37,704⟩,52800782336,21096205⟩, ⟨⟨267,372,72,2462⟩,534023503872,491959495⟩⟩,
     ⟨32, ⟨⟨182,252,55,1197⟩,185930350592,114923195⟩, ⟨⟨440,613,121,3908⟩,2408228061184,3649568203⟩⟩]
  | .h7773 =>
    [⟨0, ⟨⟨11,15,3,125⟩,55574528,2194⟩, ⟨⟨20,28,4,256⟩,230686720,17031⟩⟩,
     ⟨2, ⟨⟨21,29,6,151⟩,332136448,24733⟩, ⟨⟨38,53,9,375⟩,1568931840,211909⟩⟩,
     ⟨5, ⟨⟨34,47,10,230⟩,1326448640,156979⟩, ⟨⟨64,89,15,587⟩,7035944960,1564938⟩⟩,
     ⟨10, ⟨⟨54,75,16,378⟩,5084807168,957077⟩, ⟨⟨101,141,24,985⟩,27099136000,9562298⟩⟩]
  | .h8000 =>
    [⟨0, ⟨⟨11,15,3,107⟩,55574528,2194⟩, ⟨⟨20,28,4,226⟩,230686720,17031⟩⟩,
     ⟨2, ⟨⟨21,29,6,141⟩,332136448,24733⟩, ⟨⟨38,53,9,350⟩,1568931840,211909⟩⟩,
     ⟨5, ⟨⟨34,47,10,219⟩,1326448640,156979⟩, ⟨⟨64,89,15,557⟩,7035944960,1564938⟩⟩,
     ⟨10, ⟨⟨54,75,16,363⟩,5084807168,957077⟩, ⟨⟨101,141,24,938⟩,27099136000,9562298⟩⟩]
  | .h14500 =>
    [⟨0, ⟨⟨6,8,1,45⟩,9699328,212⟩, ⟨⟨8,11,1,81⟩,17039360,517⟩⟩]
  | .h21473 =>
    [⟨0, ⟨⟨6,8,1,22⟩,9699328,212⟩, ⟨⟨8,11,1,38⟩,17039360,517⟩⟩]
  | .h24000 =>
    [⟨0, ⟨⟨6,8,1,20⟩,9699328,212⟩, ⟨⟨8,11,1,34⟩,17039360,517⟩⟩]
  | .h28323 =>
    [⟨0, ⟨⟨6,8,1,18⟩,9699328,212⟩, ⟨⟨8,11,1,30⟩,17039360,517⟩⟩]
  | .h32433 =>
    [⟨0, ⟨⟨4,5,1,14⟩,4456448,60⟩, ⟨⟨5,7,1,26⟩,6815744,147⟩⟩]
end P1_7
end
section
namespace P1_7
open P1 (HighBand agreement p blockLength)
def degreeAt (hi : ℕ) := 131071 + hi
def quotientOrder (lo : ℕ) := 131071 - lo
def ceilRatio (num den : ℕ) := (num + (den - 1)) / den
def singularDegree (e v : ℕ) := (2 * e - 1) * v
def singularFee (e v : ℕ) := (p + 1) * singularDegree e v
end P1_7
end
section
namespace P1_7
open P1 (K HighBand)
structure PrefixFees where
  loss : ℕ
  point : ℕ
  lowSeed : ℕ
  lowJet : ℕ
  fixedODE : ℕ
  content : ℕ
def fees : HighBand → PrefixFees
  | .h2370 => ⟨0xc6a60444d57233,110347699758,807260748688063,0x49c391ad48aba2,38151568667564,0xa8fac932a93da⟩
  | .h2390 => ⟨0xad0e9cb84106fe,101844575642,753396489791997,0x404c70834b7a2d,38157285932502,0x91b8d2e24b7a4⟩
  | .h2410 => ⟨0xa4592bc487b096,100703867234,744183315127696,0x3e6cfc4d0caf9b,34639023803659,0x907956e246724⟩
  | .h2420 => ⟨0x927ce371ebf0f2,91594376922,687299845220311,0x358ff95dcec3bd,38165861829904,0x7ea3e9a1fe8cc⟩
  | .h2440 => ⟨0x84e1047dab8c51,85961568190,650562204734357,0x30050a31ccf51d,38171579094840,0x7605b8c1dbce8⟩
  | .h2460 => ⟨0x73ba7c80b95863,84217000829,671070254549873,0x332d93dab13c8d,0xf2afde1ff8d,0x45c114a11936c⟩
  | .h2480 => ⟨0x5cf21f7a0ef20a,70537136826,681749355329214,0x337000ce20d5e3,20443388263367,0x5806783162dfa⟩
  | .h2500 => ⟨0x547bcbcb3fb565,64458497223,632342534292825,0x2c548159d631c5,20446449317333,0x525c7b014c0a0⟩
  | .h2520 => ⟨0x4d8211ee91b0f3,59457295665,590778843691473,0x26bf3c38259503,20447979844314,0x4dbce4d139666⟩
  | .h2530 => ⟨0x4a80525d206791,57262402424,572356755779870,0x24644eb3f07072,20449510371303,0x4bb94c213147c⟩
  | .h2540 => ⟨0x477f2c0b8b033a,55211229824,555002151798380,9637633761418008,20451040898286,0x49df774129d18⟩
  | .h2550 => ⟨0x46a3f4995b8fd6,52390771172,530494766196727,9047161062313886,0xe5ccf81b349,918798967056612⟩
  | .h2560 => ⟨0x4415769e682c73,50815858420,516962649580271,8596687047024448,0xe5d15f1b746,899614086324876⟩
  | .h2570 => ⟨0x41cfbce1456dc9,49368621684,504235940002851,8183057889704051,0xe5d7f99bd3b,881967575638488⟩
  | .h2585 => ⟨0x3ecfad4ba758ed,47342338200,486408319203654,7619632267393302,0xe5da2d1bf38,857986474723818⟩
  | .h2590 => ⟨0x3ddbf64c2de37f,46727268268,480855698217897,7448537958469074,0xe5de941c338,850582269865668⟩
  | .h2600 => ⟨0x3c0892eb813761,45514591560,470033840201518,7119452096500071,0xe5df04cf6cf,836534522346306⟩
  | .h2601 => ⟨0x3bdadc2c07431d,45397438500,468968486981015,7088005214142854,0xe5e36bcfaca,835181523760716⟩
  | .h2611 => ⟨0x3a1a64418cf374,44266082336,458822062907216,6787278376039194,0xe5e7d2cfec8,822175691687580⟩
  | .h2621 => ⟨0x3704331aa297e6,42651660131,463680073650785,6989669646479868,0xde4306494d7,806054766807936⟩
  | .h2640 => ⟨0x320cb369a009dc,38169443284,459753181773049,6828943281952988,0xdb6e50e29b6,745131477740574⟩
  | .h2670 => ⟨0x2dd1e2f336e0d8,34947228484,427238601463149,5906960449490045,0xdb7aeaaa411,707449934455284⟩
  | .h2700 => ⟨0x2a30a4eb4a70aa,32314722916,400003911724706,5185894946170917,0xdb8feaf7001,676763500392816⟩
  | .h2750 => ⟨0x257067f07b32a4,28775347756,362720810414116,0xf2dd79cc4261b,0xdba4eb43bef,636307777330458⟩
  | .h2800 => ⟨9093726817038345,24991110784,347185829760584,0xdc3ff7f2c5048,0xdd7763d8336,578271595481166⟩
  | .h2900 => ⟨5800060782617944,12539815200,0xf20a9b09f30a,0x8212c7e161040,6695612273307,511271531664036⟩
  | .h2950 => ⟨5251864540529474,11584012536,0xe241ec08ee21,0x71c724995fa57,6697111057144,478322287368660⟩
  | .h2980 => ⟨4971435888722683,11091161880,0xd9f99e086b31,0x69a87d0ae55b4,6698110246367,462180055424676⟩
  | .h3000 => ⟨4808343218601775,10795377096,0xd4f3be081deb,0x64e6746b02e86,6700608219427,452570569407336⟩
  | .h3050 => ⟨0xcd039cd6bab1a,6249680530,0xc955a907a517,0x5906af5a97884,4462596830147,348830734548744⟩
  | .h3100 => ⟨0xbbe0053b6dc4c,5830722884,0xbe01fe06fbac,0x4f74fa6284757,4465922884135,329279372310360⟩
  | .h3200 => ⟨0xa0f91d38e7687,5636634553,0xa6e90d07332b,0x3dd9f68bfc0ae,3536290028064,0xf64f0103e0fe⟩
  | .h3400 => ⟨0x545b8e3e69741,1947582964,0x87c35604b096,717834524435316,773734060273,0x856e0a0219ec⟩
  | .h3555 => ⟨0x4619db63a2418,1691496130,0x780f7d03e603,563861988263093,776291603630,0x762f4501dc76⟩
  | .h4000 => ⟨743586206940527,1227219168,0x7baab8058920,0xbf14e33eae07,480665860027,0x714f9801c8d0⟩
  | .h4800 => ⟨0xeb7c4625bd00,276782559,66390681907906,70249005898163,170947324145,42055883594292⟩
  | .h7773 => ⟨667673328253744,15469025,0xe395400f361,6889255177790,9221741856,8593139048322⟩
  | .h8000 => ⟨612724080874576,12205319,0xc600e00bd13,5470898523783,9652754077,8196827651598⟩
  | .h14500 => ⟨43453627014996,647847,2435397459732,120681348985,366898459,884243170110⟩
  | .h21473 => ⟨19521532348308,168462,1163365714284,27839763319,212128976,568898617878⟩
  | .h24000 => ⟨18370950873948,147204,0xf414000810,23196140876,218042600,556114379274⟩
  | .h28323 => ⟨0xfa96e003f24,126954,933249418956,18817884470,223664856,543330140670⟩
  | .h32433 => ⟨2627161033122,18700,485801067512,7906309075,14370002,202417111230⟩
structure PrefixBooks (b : HighBand) where
  loss : Finset K
  point : Finset K
  lowSeed : Finset K
  lowJet : Finset K
  fixedODE : Finset K
  content : Finset K
  loss_le : loss.card ≤ (fees b).loss
  point_le : point.card ≤ (fees b).point
  lowSeed_le : lowSeed.card ≤ (fees b).lowSeed
  lowJet_le : lowJet.card ≤ (fees b).lowJet
  fixedODE_le : fixedODE.card ≤ (fees b).fixedODE
  content_le : content.card ≤ (fees b).content
noncomputable def PrefixBooks.union {b} (B : PrefixBooks b) : Finset K := by
  classical exact B.loss ∪ B.point ∪ B.lowSeed ∪ B.lowJet ∪ B.fixedODE ∪ B.content
end P1_7
end
section
namespace P1_7
open P1 (HighBand)
set_option maxRecDepth 4000
end P1_7
end
section
namespace P1_7
open P1 (HighBand)
set_option maxRecDepth 4000
end P1_7
end
section
namespace P1_7
open P1 (HighBand)
set_option maxRecDepth 4000
end P1_7
end
section
namespace P1_7
open P1 (HighBand)
set_option maxRecDepth 4000
end P1_7
end
section
namespace P1_7
open P1 (HighBand p agreement)
end P1_7
end
section
namespace P1_7
noncomputable section
open Polynomial
open P1 (HighBand AnchorModel AnchoredFamily K p node twist agreement)
open K1_14 (L FX Seeds Equation Shape Jet Banks SeedBound liftPoly graphEval atX atMark
  jetAt triangle slots shapeSum)
open K1_14_3 (Surface Parent)
open scoped BigOperators
def AdjacentChart {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (H : (Polynomial L)) : Prop :=
  let σ := frobenius L p
  let H' := H.map σ
  H.Monic ∧ H.natDegree = M.overhead.toNat ∧ H ∣ liftPoly M.E ∧
  H'.Monic ∧ H'.natDegree = M.overhead.toNat ∧ H' ∣ liftPoly (M.E.map twist) ∧
  IsCoprime H H' ∧
  (∀ i, H.eval (algebraMap K L (node i)) ≠ 0 ∧ H'.eval (algebraMap K L (node i)) ≠ 0) ∧
  IsCoprime (liftPoly (M.Q * M.factor * M.A₀)) H ∧
  IsCoprime ((liftPoly (M.Q * M.factor * M.A₀)).map σ) H' ∧
  ∀ γ ∈ Γ,
    let z := algebraMap K L (M.label γ)
    let D := liftPoly (M.factor * M.amplitude γ)
    let S := liftPoly (F.scalar γ)
    IsCoprime D H ∧ IsCoprime (D.map σ) H' ∧
    H ∣ D * S + C z * liftPoly M.Q ∧
    H' ∣ D.map σ * S + C (z ^ p) * (liftPoly M.Q).map σ
abbrev GradeIndex (b : HighBand) := Fin (grades b).length
def fullCutoff (s : Shape) := s.m * agreement - 1
def buffered (h r : ℕ) (s : Shape) := fullCutoff s - 2*h*r
def debit (h : ℕ) (t : Bank) :=
  triangle t.shape.U * t.nodeRows + 2*h*(t.shape.U+1)*t.poleMoment
structure BufferedPair (h : ℕ) (rows : Banks) (s : Stage) where
  free : Jet
  moving : Jet
  free_ne : free ≠ 0
  moving_ne : moving ≠ 0
  free_mem : free ∈ rows s.free.shape (buffered h s.reserve s.free.shape)
  moving_mem : moving ∈ rows s.moving.shape (buffered h s.reserve s.moving.shape)
  no_moving : K1_14_3.NoMovingCommon free moving
abbrev Pairs (b : HighBand) (h : ℕ) (rows : Banks) :=
  ∀ s ∈ stages b, BufferedPair h rows s
def BankPass (rows : Banks) (s : Shape) (q : Surface) : Prop :=
  ∀ P ∈ rows s (fullCutoff s), P ∈ q.asIdeal
def PairPass {h rows s} (pair : BufferedPair h rows s) (q : Surface) : Prop :=
  BankPass rows s.free.shape q ∧ BankPass rows s.moving.shape q ∧
    K1_14_3R.compatible pair.free pair.moving q
def MarkOn {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (q : Surface) (γ : K) : Prop :=
  q.asIdeal ≤ RingHom.ker
    (eval₂RingHom (eval₂RingHom (graphEval (M.label γ)) (atX (F.scalar γ)))
      (atX (F.scalar γ).derivative))
structure PrefixInventory (b : HighBand) {u del} (M : AnchorModel u del) {Γ}
    (F : AnchoredFamily M Γ) {rows : Banks} (pairs : Pairs b M.overhead.toNat rows) where
  books : PrefixBooks b
  parents : Finset Surface
  geometric : ∀ q ∈ parents, Parent q
  stage_pass : ∀ q ∈ parents, ∀ s (hs : s ∈ stages b), 0 < s.reserve →
    PairPass (pairs s hs) q
  terminal_pass : ∀ q ∈ parents, BankPass rows (terminal b).shape q
  covers : ∀ γ ∈ Γ, γ ∈ books.union ∨ ∃ q ∈ parents, MarkOn M F q γ
abbrev Test (b : HighBand) := Option (GradeIndex b)
def tested (b : HighBand) : Test b → Bank
  | none => terminal b
  | some i => subbank b ((grades b).get i)
def Reduced (f : Equation) : Prop :=
  0 < f.natDegree ∧ f.IsPrimitive ∧ (f.map (algebraMap Seeds (FractionRing Seeds))).Separable
def regularRoot (f : Equation) (z : K) (S : (Polynomial K)) : Prop :=
  atMark f z S = 0 ∧ graphEval z (f.resultant f.derivative) ≠ 0 ∧
    atMark f.derivative z S ≠ 0
end
end P1_7
end
section
namespace P1_7
noncomputable section
open Polynomial
open P1 (AnchorModel AnchoredFamily K p node twist)
open K1_14 (FX L Seeds Equation liftPoly graphEval atX atMark SeedBound)
end
end P1_7
end
section
namespace P1_7
noncomputable section
open Polynomial
open P1 (HighBand AnchorModel AnchoredFamily agreement p)
open K1_14 (Banks Jet Equation SeedBound)
open K1_14_3 (Surface Parent ProjectedProduct OrderAt)
open K1_14_4 (seedDegree seedDegree_le_iff)
end
end P1_7
end

end Merged_UpperBase

-- merged module UpperBranch3
section Merged_UpperBranch3
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_7_3
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_4
open K1_14_2_4_1 
open scoped Polynomial
open K1_14_2_4_1 (chartEvaluation)
open P0_10R.Bridge (donor_1_1 donor_1_2 donor_1_3 donor_1_4 donor_1_5)
private theorem generic_separability {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J g}
    (R : PrimitiveRoot C₀ J g) (hg : 0 < g) (hgp : g < p) :
    (R.equation.map (insertX C₀)).Separable := by
  let F := R.equation.map (insertX C₀)
  let : CharP (ConstantSeedX C₀) p :=
    charP_of_injective_ringHom ((extendX C₀).comp seedEmbedding).injective p
  have hdeg : F.natDegree = g :=
    (Polynomial.natDegree_map_eq_of_injective
      (IsFractionRing.injective (Polynomial (ConstantSeedField C₀)) (ConstantSeedX C₀)) _).trans R.degree
  have hgc : (g : ConstantSeedX C₀) ≠ 0 := by
    intro hz
    have hp := (CharP.cast_eq_zero_iff (ConstantSeedX C₀) p g).mp hz
    exact (not_le_of_gt hgp) (Nat.le_of_dvd hg hp)
  refine (Polynomial.separable_iff_derivative_ne_zero R.irreducible).mpr ?_
  intro hd
  have hz := congrArg (fun Q : (Polynomial (ConstantSeedX C₀)) => Q.coeff (g - 1)) hd
  have hsucc : g - 1 + 1 = g := Nat.sub_add_cancel hg
  have hcast : (↑(g - 1) + 1 : ConstantSeedX C₀) = (g : ConstantSeedX C₀) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun k : ℕ => (k : ConstantSeedX C₀)) hsucc
  rw [Polynomial.coeff_derivative, Polynomial.coeff_zero, hcast, hsucc] at hz
  change F.coeff g * (g : ConstantSeedX C₀) = 0 at hz
  rw [show F.coeff g = F.leadingCoeff by rw [← hdeg, Polynomial.coeff_natDegree]] at hz
  exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr R.irreducible.ne_zero) hgc) hz
theorem chartResultant_proper {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J g n}
    {R : PrimitiveRoot C₀ J g} (A : CoefficientChart R n) (hg : 0 < g) (hgp : g < p) :
    parameterInclusion n (chartResultant A.equation g) ∉ chartBase A := by
  let ev := (chartBaseMap A).comp (parameterInclusion n)
  let F := R.equation.map (insertX C₀)
  let a := insertConstant C₀ (A.scale : ConstantSeedField C₀)
  have ha : IsUnit (Polynomial.C a) :=
    (show IsUnit (A.scale : ConstantSeedField C₀) from A.scale.isUnit).map
      (Polynomial.C.comp (insertConstant C₀))
  have hFdeg : F.natDegree = g :=
    (Polynomial.natDegree_map_eq_of_injective
      (IsFractionRing.injective (Polynomial (ConstantSeedField C₀)) (ConstantSeedX C₀)) _).trans R.degree
  have hG : (equationAtX A.equation).map ev = Polynomial.C a * F := by
    rw [equationAtX, Polynomial.map_map, chartEvaluation A, ← Polynomial.map_map,
      A.generic_eq, Polynomial.map_mul, Polynomial.map_C]
    rfl
  have hGdeg : (Polynomial.C a * F).natDegree = g :=
    (Polynomial.natDegree_C_mul (isUnit_iff_ne_zero.mp (Polynomial.isUnit_C.mp ha))).trans hFdeg
  have hsep := (generic_separability R hg hgp).unit_mul ha
  have hres := Polynomial.resultant_derivative_ne_zero_of_separable _ hsep
  rw [hGdeg, ← hG, Polynomial.derivative_map, Polynomial.resultant_map_map] at hres
  exact fun h => hres (RingHom.mem_ker.mp h)
theorem regular_chart (T : Finset K) (z : K → K) (s : K → (Polynomial K))
    (J : Ideal RootAmbient) (g H : ℕ) (hg : 0 < g) (hgp : g < p)
    (hcurve : SmallRootCurve J g H) (hinj : Set.InjOn z (T : Set K))
    (hmark : ∀ γ ∈ T, OnRoot J (z γ) (s γ)) :
    ∃ U ⊆ T, (T \ U).card ≤ taylorPower g * H ∧
      ∃ n : ℕ, Nonempty (RegularChart U s g H n) := by
  classical
  obtain ⟨hJ, C₀, hC₀, hseed, hsf, hs, hyf, hy⟩ := hcurve
  let : Fact (Irreducible C₀) := ⟨hC₀⟩
  obtain ⟨R⟩ := donor_1_1 C₀ J g hJ hseed hsf hs hg
  obtain ⟨n, A, t, hbase, hpoints, hroots⟩ := donor_1_2 C₀ J g R T z s hmark
  have hheight := donor_1_3 C₀ J g H n R A hg hyf hy
  obtain ⟨hdim, hslices⟩ := donor_1_4 C₀ J g H n R A hheight hyf hy
  let q := chartResultant A.equation g
  let point (γ : K) := baseMark (z γ) (t γ)
  let U := T.filter fun γ => MvPolynomial.aeval (point γ) (parameterInclusion n q) ≠ 0
  have hU : U ⊆ T := Finset.filter_subset _ _
  have hpt : Set.InjOn point (T : Set K) := by
    intro γ hγ η hη heq
    apply hinj hγ hη
    apply seedEmbedding.injective
    exact congrFun heq (Sum.inl 0)
  have hbad_inj : Set.InjOn point ((T \ U : Finset K) : Set K) :=
    hpt.mono (by
      intro γ hγ
      exact (Finset.mem_sdiff.mp hγ).1)
  have hbudget := donor_1_5 n H (chartBase A) (RingHom.ker_isPrime (chartBaseMap A)) hheight q
    (chartResultant_proper A hg hgp) (T \ U) point hbad_inj (by
      intro γ hγ
      obtain ⟨hγT, hγU⟩ := Finset.mem_sdiff.mp hγ
      refine ⟨hbase γ hγT, ?_⟩
      by_contra hn
      exact hγU (Finset.mem_filter.mpr ⟨hγT, hn⟩))
  have hsrc : (chartSource A).IsPrime :=
    ((Ideal.span_singleton_prime R.irreducible.ne_zero).mpr
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp R.irreducible)).comap (chartRootMap A)
  refine ⟨U, hU, hbudget.trans (Nat.mul_le_mul_right H (chartResultant_degree A.degree hg)),
    n, ⟨{
      equation := A.equation
      equation_degree := A.degree
      parameter := t
      source := chartSource A
      source_prime := hsrc
      source_dim := hdim
      slices := hslices
      lies_on := fun γ hγ => hpoints γ (hU hγ)
      root := fun γ hγ => hroots γ (hU hγ)
      simple := ?_ }⟩⟩
  intro γ hγ
  exact simple_of_resultant A.degree hg (hroots γ (hU hγ)) (Finset.mem_filter.mp hγ).2
end
end P1_7_3
end
section
namespace P1_7_3
noncomputable section
open P1 (K I node agreement blockLength)
open K1_14 (FX L seedEmbedding)
open K1_14_2_4 hiding specialize
open Polynomial MvPolynomial Finset ProximityPrize.Benchmark
open scoped BigOperators
open K1_14_2_4 (proper_section_card)
def persistentNodes (w : I → K) (U : Finset K) (s : K → (Polynomial K)) : Finset I := by
  classical
  exact univ.filter fun i => ∀ γ ∈ U, (s γ).eval (node i) = w i
theorem hits_persistent {w U s} {γ : K} (hγ : γ ∈ U) {i : I}
    (hi : i ∈ persistentNodes w U s) : (s γ).eval (node i) = w i := by
  classical
  exact (mem_filter.mp hi).2 γ hγ
theorem section_bounds {n g H t : ℕ} {U : Finset K} {s : K → (Polynomial K)} {w : I → K}
    (A : RegularChart U s g H n) (ht : 0 < t) (hdistinct : Set.InjOn s (U : Set K))
    (C : TaylorForms n (ordinateBound t g) (taylorPower t))
    (hrec : ∀ γ ∈ U, C.Recovers (A.parameter γ) (s γ)) :
    ∀ i : I, (∃ γ ∈ U, (s γ).eval (node i) ≠ w i) →
      (U.filter fun γ => (s γ).eval (node i) = w i).card ≤
        taylorPower t * (g * H) + ordinateBound t g * H := by
  classical
  let a := ordinateBound t g
  let b := taylorPower t
  let D := b * (g * H) + a * H
  have ha : 0 < a := by simp [a, ordinateBound]
  have hb : 0 < b := by dsimp [b, taylorPower]; omega
  let P := linearIdeal a b A.source
  let M := bidegreeMap (Fin n) FX a b
  let v (γ : K) := markedPoint (A.parameter γ) (s γ)
  let point (γ : K) := monomialPoint (bidegreeExponents (Fin n) a b) (v γ)
  have hP : P.IsPrime := A.source_prime.comap M
  let _ : P.IsPrime := hP
  have hdim_eq : (affineHilbertPolynomial P).natDegree =
      (affineHilbertPolynomial A.source).natDegree :=
    natDegree_affineHilbertPolynomial_comap_bidegreeMap ha hb _
  have hdim := hdim_eq.trans_le A.source_dim
  have hdeg (h : (affineHilbertPolynomial P).natDegree = 1) : affineDegree P ≤ (D : ℚ) :=
    P0_10R.Bridge.root_embedding n a b (g * H) H ha hb A.source A.source_prime (hdim_eq.symm.trans h) A.slices
  have eval_linear (γ : K) (F : LinearRing n a b) :
      MvPolynomial.aeval (point γ) F = MvPolynomial.aeval (v γ) (M F) := by
    rw [show M = monomialMap FX (bidegreeExponents (Fin n) a b) from
      bidegreeMap_eq_monomialMap a b]
    exact aeval_monomialPoint _ _
  have hpoints (γ : K) (hγ : γ ∈ U) : point γ ∈ zeroLocus FX P := by
    intro F hF
    rw [eval_linear]
    exact A.lies_on γ hγ _ hF
  have hinj : Set.InjOn point (U : Set K) := by
    intro γ hγ η hη heq
    have hv := (monomialPoint_injective (fun i =>
      single_mem_bidegreeExponents ha hb i) : Function.Injective
      (monomialPoint (E := FX) (bidegreeExponents (Fin n) a b))) heq
    exact hdistinct hγ hη (Polynomial.map_injective _ (algebraMap K L).injective
      (IsFractionRing.injective (Polynomial L) FX (congrFun hv none)))
  have hsection (i : I) (hmiss : ∃ γ ∈ U, (s γ).eval (node i) ≠ w i) :
      (U.filter fun γ => (s γ).eval (node i) = w i).card ≤ D := by
    let x := node i
    let y := w i
    let q := C.numerator x - MvPolynomial.C (seedEmbedding y) * C.denominator
    have hq : q ∈ restrictBidegree (Fin n) FX a b := by
      refine Submodule.sub_mem _ (C.numerator_bound x) ?_
      rw [← MvPolynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ _ C.denominator_bound
    let Q := bidegreeLift q hq
    have hcut (γ : K) (hγ : γ ∈ U) :
        MvPolynomial.aeval (point γ) Q = 0 ↔ (s γ).eval x = y := by
      have hr := hrec γ hγ
      change MvPolynomial.aeval (v γ) C.denominator ≠ 0 ∧
        (∀ x, MvPolynomial.aeval (v γ) (C.numerator x) =
          MvPolynomial.aeval (v γ) C.denominator * seedEmbedding ((s γ).eval x)) at hr
      rw [eval_linear, show M Q = q from bidegreeMap_bidegreeLift q hq]
      dsimp only [q]
      rw [map_sub, map_mul, MvPolynomial.aeval_C, Algebra.algebraMap_self_apply, hr.2 x,
        sub_eq_zero, mul_comm (seedEmbedding y), mul_right_inj' hr.1]
      exact seedEmbedding.injective.eq_iff
    have hproper : Q ∉ P := by
      obtain ⟨γ, hγ, hγmiss⟩ := hmiss
      exact fun hQ => hγmiss ((hcut γ hγ).mp (hpoints γ hγ Q hQ))
    refine proper_section_card _ point (hinj.mono (filter_subset _ _)) hproper
      (totalDegree_bidegreeLift_le_one q hq) (fun γ hγ => ?_) hdim hdeg
    obtain ⟨hγU, hγhit⟩ := mem_filter.mp hγ
    exact mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hpoints γ hγU, (hcut γ hγU).mpr hγhit⟩
  exact hsection
end
end P1_7_3
end
section
namespace P1_7_3
noncomputable section
open K1 (K I node)
open K1_14 (FX L seedEmbedding)
open K1_14_2_4_2 (center)
open Polynomial Finset ProximityPrize.Benchmark
open scoped BigOperators
private theorem mapped_node_ne_center (x : K) : seedEmbedding x ≠ center := by
  intro h
  exact (Polynomial.X_ne_C (algebraMap K L x))
    ((IsFractionRing.injective (Polynomial L) FX) h.symm)
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem linear_interpolation_weights {E : Type} [Field E]
    (nodes : I → E) (hnodesInj : Function.Injective nodes)
    (ξ : E) (hne : ∀ i, nodes i ≠ ξ)
    (sites : Finset I) (d t : ℕ) (hdt : d ≤ sites.card + t)
    (w : I → E) (x : E) :
    ∃ c : E, ∃ a : Fin (t+1) → E, ∀ P : (Polynomial E), P.natDegree ≤ d →
      (∀ i ∈ sites, P.eval (nodes i) = w i) →
      P.eval (x) = c + ∑ j, a j * (taylor ξ P).coeff j := by
  classical
  let V := degreeLE E (d : WithBot ℕ)
  let evalAtNodes : V →ₗ[E] (sites → E) := LinearMap.pi fun i =>
    (leval (nodes i)).comp V.subtype
  let jets : V →ₗ[E] (Fin (t+1) → E) := LinearMap.pi fun j =>
    ((lcoeff E (j : ℕ)).comp (taylor ξ)).comp V.subtype
  let data : V →ₗ[E] (sites → E) × (Fin (t+1) → E) := evalAtNodes.prod jets
  have hker : LinearMap.ker data = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro P hP
    have hn (i : sites) : P.1.eval (nodes i) = 0 := by
      exact congrFun (congrArg Prod.fst hP) i
    have hj (j : Fin (t+1)) : (taylor ξ P.1).coeff j = 0 := by
      exact congrFun (congrArg Prod.snd hP) j
    have hdvd : Polynomial.X^(t+1) ∣ taylor ξ P.1 :=
      X_pow_dvd_iff.mpr fun j hj' => hj ⟨j,hj'⟩
    obtain ⟨Q, hQ⟩ := hdvd
    by_cases hQ0 : Q = 0
    · apply Subtype.ext
      have hz : taylor ξ P.1 = 0 := by rw [hQ, hQ0, mul_zero]
      rw [← taylor_zero P.1, ← neg_add_cancel ξ, ← taylor_taylor, hz, map_zero]
      rfl
    · have hdeg : t+1 + Q.natDegree ≤ d := by
        have hd := natDegree_le_iff_degree_le.mpr (mem_degreeLE.mp P.2)
        rwa [← natDegree_taylor P.1 ξ, hQ, natDegree_mul (pow_ne_zero _ X_ne_zero) hQ0,
          natDegree_X_pow] at hd
      let site (i : I) := nodes i - ξ
      have hinj : Function.Injective site := fun i j h =>
        hnodesInj (sub_left_inj.mp h)
      have hroots (i : I) (hi : i ∈ sites) : Q.eval (site i) = 0 := by
        have h := hn ⟨i, hi⟩
        rw [← sub_add_cancel (nodes i) ξ, ← taylor_eval, hQ,
          eval_mul, eval_pow, eval_X] at h
        exact (mul_eq_zero.mp h).resolve_left
          (pow_ne_zero _ (sub_ne_zero.mpr (hne i)))
      have hc := FrobeniusLocator.Strata.root_nodes_card_le site hinj Q hQ0 sites hroots
      omega
  have hleft : ∃ lift : ((sites → E) × (Fin (t+1) → E)) →ₗ[E] V,
      lift.comp data = LinearMap.id := by
    apply LinearMap.exists_leftInverse_of_injective
    exact hker
  obtain ⟨lift, hlift⟩ := hleft
  let value := ((leval (x)).comp V.subtype).comp lift
  let fixed : sites → E := fun i => w i
  let unit (j : Fin (t+1)) : Fin (t+1) → E := Pi.single j 1
  refine ⟨value (fixed, 0), (fun j => value (0, unit j)), ?_⟩
  intro P hP hnodes
  let P' : V := ⟨P, mem_degreeLE.mpr (natDegree_le_iff_degree_le.mp hP)⟩
  let v := jets P'
  have hdata : data P' = (fixed, 0) + ∑ j, v j • ((0 : sites → E), unit j) := by
    have hsum : (∑ j, v j • unit j) = v := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i]
      · simp [unit]
      · intro j _ hji
        simp [unit, Pi.single_eq_of_ne hji.symm]
      · simp
    have hpairs : (∑ j, v j • ((0 : sites → E), unit j)) = ((0 : sites → E), v) := by
      apply Prod.ext
      · change (LinearMap.fst E (sites → E) (Fin (t+1) → E))
            (∑ j, v j • ((0 : sites → E), unit j)) = 0
        rw [map_sum]
        simp
      · change (LinearMap.snd E (sites → E) (Fin (t+1) → E))
            (∑ j, v j • ((0 : sites → E), unit j)) = v
        rw [map_sum]
        exact hsum
    rw [hpairs]
    change (evalAtNodes P', v) = _
    rw [show evalAtNodes P' = fixed from funext fun i => hnodes i i.property]
    simp
  have hval : value (data P') = P.eval (x) := by
    change (lift (data P')).1.eval (x) = _
    rw [show lift (data P') = P' from DFunLike.congr_fun hlift P']
  rw [hdata, map_add, map_sum] at hval
  rw [← hval]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [map_smul, smul_eq_mul, mul_comm]
  rfl
theorem interpolation_weights (sites : Finset I) (d t : ℕ) (hdt : d ≤ sites.card + t)
    (w : I → K) (x : K) :
    ∃ c : FX, ∃ a : Fin (t+1) → FX, ∀ P : (Polynomial FX), P.natDegree ≤ d →
      (∀ i ∈ sites, P.eval (seedEmbedding (node i)) = seedEmbedding (w i)) →
      P.eval (seedEmbedding x) = c + ∑ j, a j * (taylor center P).coeff j :=
  linear_interpolation_weights (seedEmbedding ∘ node)
    (seedEmbedding.injective.comp IRSProfile.domain.injective) center
    (fun i => mapped_node_ne_center (node i)) sites d t hdt (seedEmbedding ∘ w) (seedEmbedding x)
end
end P1_7_3
end
section
namespace P1_7_3
noncomputable section
open K1 (K I node p)
open K1_14 (L FX seedEmbedding liftPoly atX)
open K1_14_2_4 K1_14_2_4_2 MvPolynomial
open K1_14_6_1 (derivativeAt)
open scoped Polynomial BigOperators
open K1_14_2_4_2 (eval_center factorial_ne_zero)
private def jetNumerator {n : ℕ} (f : SourceRing n) (t : ℕ) :
    Fin (t+1) → SourceRing n :=
  Fin.cases (separant f ^ taylorPower t * ordinate) fun i =>
    (((i.val+1).factorial : FX)⁻¹) •
      (separant f ^ (taylorPower t - (2*i.val+1)) * cleared f i.val)
private theorem jet_pad {t : ℕ} (i : Fin t) :
    taylorPower t - (2*i.val+1) + (2*i.val+1) = taylorPower t := by
  have hi := i.isLt
  unfold taylorPower
  omega
private theorem jet_bound {n g t : ℕ} {f : SourceRing n} (hg : 0 < g)
    (hf : f ∈ box n g 1) (j : Fin (t+1)) :
    jetNumerator f t j ∈ box n (ordinateBound t g) (taylorPower t) := by
  have hsep := separant_bound hf
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa only [jetNumerator, Fin.cases_zero, ordinateBound, Nat.add_comm, Nat.add_zero,
      Nat.mul_one] using
      mul_mem_restrictBidegree (box_pow hsep (taylorPower t)) (ordinate_mem (n := n))
  · simp only [jetNumerator, Fin.cases_succ]
    apply (box _ _ _).smul_mem
    have hpad := jet_pad i
    have h := mul_mem_restrictBidegree (box_pow hsep (taylorPower t - (2*i.val+1)))
      (cleared_bound hg hf i.val)
    have hy : (taylorPower t - (2*i.val+1))*(g-1) + (1+(2*i.val+1)*(g-1)) =
        ordinateBound t g := by
      calc
        _ = 1+(taylorPower t - (2*i.val+1)+(2*i.val+1))*(g-1) := by ring
        _ = _ := by rw [hpad, ordinateBound]
    rwa [hy, ← Nat.add_mul, hpad, Nat.mul_one] at h
private theorem jet_eval {n t : ℕ} (htp : t < p) (f : SourceRing n)
    (v : Fin n → L) (S : (Polynomial K)) (hroot : markEval v S f = 0) (j : Fin (t+1)) :
    markEval v S (jetNumerator f t j) =
      markEval v S (separant f ^ taylorPower t) *
        (Polynomial.taylor center (S.map seedEmbedding)).coeff j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [jetNumerator, Fin.cases_zero, map_mul, Fin.val_zero,
      Polynomial.taylor_coeff_zero, eval_center]
    rw [show markEval v S ordinate = atX S from eval_X _]
  · let a := markEval v S (separant f)
    let j' := i.val+1
    have hjp : j' < p := (Nat.succ_le_of_lt i.isLt).trans_lt htp
    have hfactor : derivativeAt S j' =
        (j'.factorial : FX) * (Polynomial.taylor center (S.map seedEmbedding)).coeff j' := by
      rw [Polynomial.taylor_coeff, Polynomial.hasseDeriv_map, eval_center]
      have h := congrFun (Polynomial.factorial_smul_hasseDeriv (R := K) j') S
      dsimp only [derivativeAt]
      rw [← h, LinearMap.smul_apply]
      simp only [nsmul_eq_mul, atX, liftPoly, Polynomial.map_mul,
        Polynomial.map_natCast, map_mul, map_natCast]
    simp only [jetNumerator, Fin.cases_succ, MvPolynomial.smul_eq_C_mul, map_mul, map_pow,
      MvPolynomial.eval_C, eval_cleared _ _ _ hroot, Fin.val_succ]
    change (j'.factorial : FX)⁻¹ *
      (a ^ (taylorPower t - (2*i.val+1)) * (a ^ (2*i.val+1) * derivativeAt S j')) =
        a ^ taylorPower t * _
    rw [hfactor]
    calc
      _ = ((j'.factorial : FX) * (j'.factorial : FX)⁻¹) *
          (a ^ (taylorPower t - (2*i.val+1)) * a ^ (2*i.val+1)) *
          (Polynomial.taylor center (S.map seedEmbedding)).coeff j' := by ring
      _ = _ := by rw [mul_inv_cancel₀ (factorial_ne_zero hjp), one_mul, ← pow_add, jet_pad i]
theorem persistent_taylor {n d t g : ℕ} (sites : Finset I) (w : I → K)
    (hdt : d ≤ sites.card + t) (htp : t < p) (hg : 0 < g)
    (f : FamilyEquation n) (hf : FamilyDegree f g) :
    ∃ C : TaylorForms n (ordinateBound t g) (taylorPower t),
      ∀ (v : Fin n → L) (S : (Polynomial K)), S.natDegree ≤ d →
        (∀ i ∈ sites, S.eval (node i) = w i) →
        (specialize f v).eval (liftPoly S) = 0 →
        (specialize f v).derivative.eval (liftPoly S) ≠ 0 → C.Recovers v S := by
  classical
  choose c a hweights using fun x => interpolation_weights sites d t hdt w x
  let F := flatten f
  let D := separant F ^ taylorPower t
  have hF := flatten_bound hf
  have hD : D ∈ box n (ordinateBound t g) (taylorPower t) := by
    have hb := box_pow (separant_bound hF) (taylorPower t)
    rw [Nat.mul_one] at hb
    exact mem_restrictBidegree_mono hb (Nat.le_add_left _ _) le_rfl
  let N (x : K) := c x • D + ∑ j, a x j • jetNumerator F t j
  have hN (x : K) : N x ∈ box n (ordinateBound t g) (taylorPower t) := by
    apply Submodule.add_mem _ (Submodule.smul_mem _ _ hD)
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (jet_bound hg hF j)
  refine ⟨⟨D, N, hD, hN⟩, ?_⟩
  intro v S hS hnodes hroot hsep
  have hroot' : markEval v S F = 0 := by rw [eval_flatten, hroot, map_zero]
  constructor
  · change markEval v S (separant F ^ taylorPower t) ≠ 0
    rw [map_pow, eval_separant]
    exact pow_ne_zero _ (by
      simpa only [map_zero] using (IsFractionRing.injective (Polynomial L) FX).ne hsep)
  · intro x
    change markEval v S (N x) = markEval v S D * seedEmbedding (S.eval x)
    have hv := hweights x (S.map seedEmbedding) (Polynomial.natDegree_map_le.trans hS)
      (fun i hi => by rw [Polynomial.eval_map_apply, hnodes i hi])
    rw [Polynomial.eval_map_apply] at hv
    rw [hv, mul_add, Finset.mul_sum]
    simp only [N, map_add, map_sum, MvPolynomial.smul_eq_C_mul, map_mul,
      MvPolynomial.eval_C, jet_eval htp F v S hroot']
    rw [mul_comm (c x)]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by dsimp only [D]; ring
end
end P1_7_3
end
section
namespace P1_7_3
noncomputable section
open P1 (K p agreement blockLength AnchorModel AnchoredFamily)
open P1_7 (  degreeAt  )
open K1_14_2_4 (taylorPower ordinateBound)
open Finset
open scoped Polynomial
end
end P1_7_3
end

end Merged_UpperBranch3

end Merged_UpperBranch3
