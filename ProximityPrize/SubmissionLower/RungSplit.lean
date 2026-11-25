import ProximityPrize.SubmissionLower.Fast076
import ProximityPrize.SubmissionLower.ListProofA
import ProximityPrize.SubmissionLower.PortHighFinish
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
set_option maxRecDepth 200000 in
set_option maxRecDepth 200000 in
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
end
end CJ0_7
end
section
namespace CJ0_8
open Polynomial PolynomialDifferential MvPolynomial
open CJ0 Sol1.C57
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
