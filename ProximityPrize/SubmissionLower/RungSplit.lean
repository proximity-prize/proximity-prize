import ProximityPrize.SubmissionLower.Fast076
import ProximityPrize.SubmissionLower.ListProofA
import ProximityPrize.SubmissionLower.RungFront
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
private def coeffMap : K →+* K1_13.Geom[X] :=
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
      change optionEquivLeft K1_13.Geom[X] (Fin 3)
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
private theorem eliminate_root (G : DifferentialPolynomial K 2) (f : K[X])
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
private def centerMap : K[X] →+* Geo :=
  (algebraMap FX Geo).comp (algebraMap K[X] FX)
private theorem centerMap_injective : Function.Injective centerMap :=
  (algebraMap FX Geo).injective.comp (IsFractionRing.injective K[X] FX)
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
private theorem readJet_coeff {P : Geo[X]} (hP : P.degree < k) (i : ℕ) :
    readJet (fun j => P.coeff j.val) i = (taylor center P).coeff i := by
  have hnat : P.natDegree < k := by
    by_cases hz : P = 0
    · simpa only [hz, Polynomial.natDegree_zero] using (by decide : 0 < k)
    · exact (Polynomial.natDegree_lt_iff_degree_lt hz).2 hP
  have hsum : P = ∑ l : Fin k, monomial l.val (P.coeff l.val) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => monomial j (P.coeff j))]
    exact P.as_sum_range' _ hnat
  exact (coeff_taylor_sum center (fun j : Fin k => P.coeff j.val) i).symm.trans
    (congrArg (fun P : Geo[X] => (taylor center P).coeff i) hsum.symm)
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
    (I₁ s) k t₁ exponent_sufficient hIpos hm l).trans (by
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
def mark (f : K[X]) : Fin 2 → Geo :=
  polynomialJet center (f.map embed)
private theorem eval_mapped_at_center (f : K[X]) : (f.map embed).eval center = centerMap f := by
  rw [Polynomial.eval_map]
  change Polynomial.eval₂RingHom embed center f = centerMap f
  congr 1
  apply Polynomial.ringHom_ext
  · intro a
    simp [centerMap, embed]
  · simp [centerMap, center]
private theorem eval_mark (G : DifferentialPolynomial K 1) (f : K[X]) :
    jetEvaluation (centeredEquation G) center (mark f) =
      centerMap (differentialSpecialization G f) := by
  rw [mark, ← eval_differentialSpecialization, centeredEquation,
    ← map_differentialSpecialization, eval_mapped_at_center]
theorem initial_mark (G : DifferentialPolynomial K 1) (f : K[X])
    (h : differentialSpecialization G f = 0) : MvPolynomial.eval (mark f) (initial G) = 0 := by
  change MvPolynomial.eval (mark f) (initialJetEquation center (centeredEquation G)) = 0
  rw [← MvPolynomial.aeval_eq_eval, aeval_initialJetEquation, eval_mark, h, map_zero]
private theorem sep_mark (G : DifferentialPolynomial K 1) (f : K[X])
    (h : differentialSpecialization (separant G (Fin.last 1)) f ≠ 0) :
    MvPolynomial.eval (mark f) (sep G) ≠ 0 := by
  rw [← MvPolynomial.aeval_eq_eval, sep, aeval_initialJetSeparant, centeredEquation, ← map_separant]
  exact fun hz => h (centerMap_injective ((eval_mark _ _).symm.trans (hz.trans (map_zero _).symm)))
theorem denominator_mark (G : DifferentialPolynomial K 1) (f : K[X])
    (h : differentialSpecialization (separant G (Fin.last 1)) f ≠ 0) :
    MvPolynomial.eval (mark f) (denominator G) ≠ 0 := by
  rw [denominator, map_pow]
  exact pow_ne_zero _ (sep_mark G f h)
theorem chart_contains (G : DifferentialPolynomial K 1) (g : InitialRing 1) (f : K[X])
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
private theorem root_of_associated {G G' : DifferentialPolynomial K 1} {f : K[X]}
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
open private ratio_image_degree from ProximityPrize.SubmissionLower.Fast048
open private curve_degree_nat from ProximityPrize.SubmissionLower.Fast055
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
private theorem regularRoot_of_simple (Q : DifferentialPolynomial K 1) (f : K[X]) :
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
      ∀ f : K[X], differentialSpecialization Q f = 0 → ¬RegularRoot Q f →
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
private theorem curve_johnson : CJ0.Main :=
  CJ0.of_children CJ0_1.proof CJ0_2.proof
    (CJ0_3.of_children CJ0_3_1.proof CJ0_3_2.proof)
    (CJ0_4.of_children CJ0_4_1.proof CJ0_4_2.proof)
    CJ0_5.proof CJ0_6.proof CJ0_7.proof CJ0_8.proof
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
