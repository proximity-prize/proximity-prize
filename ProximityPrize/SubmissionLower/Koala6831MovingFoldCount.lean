import ProximityPrize.SubmissionLower.Koala6831MovingFoldGeometry
import ProximityPrize.SubmissionLower.Koala6831MovingPairIncidence

namespace ProximityPrize.SubmissionLower.Koala6831MovingFoldCount

open scoped Classical BigOperators
open Koala6831Moving Koala6831MovingPairIncidence
open Koala6831OrdinaryIncidence (lengthAverage nodeAverage)
open RCN081 RCN095 RCN130 RCN135 RCN136 RCN137 RCN138 RCN156 RCN167 RCN222 RCN234 RCN243
open RCN238 RCN263 RCN266 RCN267 RCN275 RCN293 RCN319
open LocatorDerivativeChain

noncomputable section

variable {K E : Type} [Field K] [Field E] [IsAlgClosed E]

theorem folded_carrier_seed_card_le
    (φ : Polynomial K →+* E) (hφ : Function.Injective φ)
    (F : MvPolynomial (Fin 4) K) (support : ResidualSupportParameters)
    (hData : ResidualSupportData support F) (hs : 2 ≤ support.s) (hy : 3 ≤ support.ys)
    (G : MvPolynomial (Fin 3) E) (left : FlagDegree)
    (hdiv : G ∣ surfaceMap φ F) (hG : Irreducible G) (hproper : ¬ G ∣ surfaceMap φ (dR 1 F))
    (hdep : 0 < G.degreeOf (1 : Fin 3)) (hderiv : MvPolynomial.pderiv (1 : Fin 3) G ≠ 0)
    (hGflag : PolynomialInFlag left G)
    (selected : K → Polynomial K) (Γ : Finset K)
    {Node : Type*} (nodes : Finset Node) (x u₀ u₁ : Node → K) (hx : Set.InjOn x nodes)
    (p w A e : ℕ) [CharP E p] (hw : 1 ≤ w) (hchar : w < p) (hwA : w < A) (hAn : A ≤ nodes.card)
    (hleft : left.zOnly + left.yz + left.all < p)
    (hmixed : (support.ys - 1) * left.all + (left.yz + left.all) * (support.s - 1) < p)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hGpoint : ∀ γ ∈ Γ, MvPolynomial.eval (selectedPoint φ selected γ) G = 0)
    (hfold : ∀ γ ∈ Γ, MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ (dR 1 F)) = 0)
    (htail : ∀ γ ∈ Γ, MvPolynomial.eval (selectedPoint φ selected γ)
      (surfaceMap φ (dR (chainLength F) F)) ≠ 0)
    (hagreement : ∀ γ ∈ Γ, A ≤ (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w e) :
    let right := decreasedFlag support 1
    let sharp := decreasedFlag support 2
    let shift := shiftedSupport support hs hy
    (Γ.card : ℚ) ≤ (flagMixed left right (reducedAgreementDirection shift) : ℚ) *
      lengthAverage nodes.card w A + flagMixed left right unitYZFlag * nodeAverage nodes.card w A +
      (e + 1) * flagMixed left right unitZFlag + flagMixed left right sharp := by
  classical
  let right := decreasedFlag support 1
  let sharp := decreasedFlag support 2
  let shift := shiftedSupport support hs hy
  let T := surfaceMap φ (dR 1 F)
  let H := surfaceMap φ (dR (chainLength F) F)
  have hT : dR 1 F ≠ 0 := by
    intro hz
    apply hproper
    rw [hz, map_zero]
    exact dvd_zero _
  have hTflag : PolynomialInFlag right T :=
    derivative_in_decreasedFlag φ support hData 1 1 le_rfl hT
  have hmix : (right.yz + right.all) * left.all + (left.yz + left.all) * right.all < p := by
    obtain ⟨h₁, h₂, _⟩ := decreasedFlag_cumulative support 1
    rw [show right.yz + right.all = support.ys - 1 from h₂,
      show right.all = support.s - 1 from h₁]
    exact hmixed
  obtain ⟨budget, hz⟩ := exists_pair_budget_of_active_coordinates G T H p left right
    hG hproper hdep hderiv hGflag hTflag hleft hmix
    (fold_component_y_or_z_transcendental φ F G hdiv)
  have hcarrier (C : FoldComponent φ F G) : ∃ D : MvPolynomial (Fin 4) K,
      ResidualSupportData shift D ∧ surfaceMap φ D ∈ C.1 ∧
      surfaceMap φ (RCN313.polyH K D) ∉ C.1 ∧
      PolynomialInFlag sharp (surfaceMap φ (RCN313.polyH K D)) := by
    obtain ⟨j, hj, _, hD, hsep, _⟩ := fold_component_exists_shifted_carrier φ F G hdiv C
    have hsep₀ : dR (j + 1) F ≠ 0 := by
      intro hzero
      rw [hzero, map_zero] at hsep
      exact hsep C.1.zero_mem
    refine ⟨dR j F, fold_shifted_support_data support hs hy hData hj hsep₀, hD, ?_, ?_⟩
    · simpa only [dR_succ, RCN313.polyH] using hsep
    · simpa only [sharp, dR_succ, RCN313.polyH] using
        fold_separant_in_decreasedFlag φ support hData hj hsep₀
  exact fold_pair_seed_card_le_of_component_carriers φ hφ shift G T H left right sharp
    budget hz hcarrier selected Γ nodes x u₀ u₁ hx p w A e hw hchar hwA hAn
    hdegree hGpoint hfold htail hagreement hnoPencil

def scaledFoldFlag (support : ResidualSupportParameters) (hs : 2 ≤ support.s) (hy : 3 ≤ support.ys)
    (n w A e : ℕ) : FlagDegree :=
  scaledPairFlag (shiftedSupport support hs hy) n w A e + (A * (A - w)) • decreasedFlag support 2

private theorem mul_scale_le_of_fold_bound
    (support : ResidualSupportParameters) (hs : 2 ≤ support.s) (hy : 3 ≤ support.ys)
    (n w A e count : ℕ) (left : FlagDegree) (hwA : w < A) (hAn : A ≤ n)
    (hcount : let right := decreasedFlag support 1
      let shift := shiftedSupport support hs hy
      (count : ℚ) ≤ (flagMixed left right (reducedAgreementDirection shift) : ℚ) *
        lengthAverage n w A + flagMixed left right unitYZFlag * nodeAverage n w A +
        (e + 1) * flagMixed left right unitZFlag + flagMixed left right (decreasedFlag support 2)) :
    count * (A * (A - w)) ≤ flagMixed left (decreasedFlag support 1) (scaledFoldFlag support hs hy n w A e) := by
  let right := decreasedFlag support 1
  let shift := shiftedSupport support hs hy
  let sharp := decreasedFlag support 2
  let denom := A * (A - w)
  let raw := flagMixed left right sharp
  have hpos : 0 ≤ nodeAverage n w A := by
    unfold nodeAverage
    apply div_nonneg <;> apply sub_nonneg.mpr
    · exact_mod_cast hwA.le.trans hAn
    · exact_mod_cast hwA.le
  have hlength : 0 ≤ lengthAverage n w A := by unfold lengthAverage; positivity
  have hrem : ((count - raw : ℕ) : ℚ) ≤
      (flagMixed left right (reducedAgreementDirection shift) : ℚ) * lengthAverage n w A +
      flagMixed left right unitYZFlag * nodeAverage n w A + (e + 1) * flagMixed left right unitZFlag := by
    by_cases hh : raw ≤ count
    · rw [Nat.cast_sub hh]
      exact sub_le_iff_le_add.mpr hcount
    · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hh), Nat.cast_zero]
      positivity
  have hcut := mul_scale_le_of_pair_bound shift n w A e (count - raw) left right hwA hAn hrem
  calc
    _ ≤ (count - raw + raw) * denom := Nat.mul_le_mul_right _ (by omega)
    _ ≤ flagMixed left right (scaledPairFlag shift n w A e) + raw * denom := by
      rw [Nat.add_mul]
      exact Nat.add_le_add hcut (le_refl _)
    _ = _ := by
      change _ = flagMixed left right (scaledPairFlag shift n w A e + denom • sharp)
      simp only [raw, flagMixed, add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all]
      ring

theorem folded_original_carrier_seed_card_mul_le
    (support : ResidualSupportParameters) (hs : 2 ≤ support.s) (hy : 3 ≤ support.ys)
    (F : MvPolynomial (Fin 4) K) (hF : Irreducible F) (p : ℕ) [CharP K p]
    (hRpos : 0 < F.degreeOf (2 : Fin 4)) (hRsmall : F.degreeOf (2 : Fin 4) < p)
    (hData : ResidualSupportData support F)
    (selected : K → Polynomial K) (Γ : Finset K)
    {Node : Type*} (nodes : Finset Node) (x u₀ u₁ : Node → K) (hx : Set.InjOn x nodes)
    (w A e : ℕ) (hw : 1 ≤ w) (hchar : w < p) (hwA : w < A) (hAn : A ≤ nodes.card)
    (htotal : support.total < p)
    (hmixed : (support.ys - 1) * support.s + support.ys * (support.s - 1) < p)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0)
    (hfold : ∀ γ ∈ Γ, specialization K (selected γ) γ (dR 1 F) = 0)
    (htail : ∀ γ ∈ Γ, specialization K (selected γ) γ (dR (chainLength F) F) ≠ 0)
    (hagreement : ∀ γ ∈ Γ, A ≤ (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w e) :
    Γ.card * (A * (A - w)) ≤ flagMixed (originalCumulativeFlag F) (decreasedFlag support 1)
      (scaledFoldFlag support hs hy nodes.card w A e) := by
  classical
  let E := GenericField K
  let φ := polynomialEmbedding K
  let _ : CharP E p := genericField_charP K p
  let seeds := geometricSeeds K F selected Γ
  let left := geometricCumulativeFlag K (F := F)
  let right := decreasedFlag support 1
  let cut := scaledFoldFlag support hs hy nodes.card w A e
  have hcomp (g : GeometricFactor K F) : (seeds g).card * (A * (A - w)) ≤ flagMixed (left g) right cut := by
    obtain ⟨hirr, hgdiv⟩ := surfaceFactors_spec φ F g.1 g.2
    have hdivGeo : g.1 ∣ geometricSurfaceMap K E F := by
      change g.1 ∣ geometricSurfaceMap K (GenericField K) F
      rw [canonical_geometricSurfaceMap]
      exact hgdiv
    have hgate := geometric_factor_regular_gate K E F hF p hRpos hRsmall g.1 hirr hdivGeo
    have hproper : ¬ g.1 ∣ surfaceMap φ (dR 1 F) := by
      have h := hgate.2.2.2.2
      change ¬ g.1 ∣ geometricSurfaceMap K (GenericField K) (MvPolynomial.pderiv (2 : Fin 4) F) at h
      rw [canonical_geometricSurfaceMap] at h
      exact h
    have hcap := geometricCumulativeFlag_le_support F hF.ne_zero hData g
    have hleft : (left g).zOnly + (left g).yz + (left g).all < p := hcap.2.2.trans_lt htotal
    have hmix : (support.ys - 1) * (left g).all + ((left g).yz + (left g).all) * (support.s - 1) < p :=
      (Nat.add_le_add (Nat.mul_le_mul_left _ hcap.1) (Nat.mul_le_mul_right _ hcap.2.1)).trans_lt hmixed
    have hsub := geometricSeeds_subset K F selected Γ g
    have hcount := folded_carrier_seed_card_le φ (polynomialEmbedding_injective K) F support hData hs hy
      g.1 (left g) hgdiv hirr hproper hgate.1 hgate.2.2.2.1
      (polynomialIn_surfaceCumulativeFlag g.1) selected (seeds g) nodes x u₀ u₁ hx
      p w A e hw hchar hwA hAn hleft hmix
      (fun γ hγ => hdegree γ (hsub hγ)) (fun γ hγ => (Finset.mem_filter.mp hγ).2)
      (fun γ hγ => by rw [selectedPoint_surface_evaluation K, hfold γ (hsub hγ), map_zero])
      (fun γ hγ => by
        rw [selectedPoint_surface_evaluation K]
        exact (polynomialEmbedding_eq_zero_iff K _).not.mpr (htail γ (hsub hγ)))
      (fun γ hγ => hagreement γ (hsub hγ))
      (noLargeSelectedPencil_mono selected Γ _ w e hsub hnoPencil)
    exact mul_scale_le_of_fold_bound support hs hy nodes.card w A e (seeds g).card (left g) hwA hAn hcount
  have ⟨hr, hm, ht⟩ := geometricCumulativeFlag_budgets F hF.ne_zero
  calc
    _ ≤ (∑ g, (seeds g).card) * (A * (A - w)) :=
      Nat.mul_le_mul_right _ (card_le_sum_geometricSeeds K F hF.ne_zero selected Γ hsolution)
    _ = ∑ g, (seeds g).card * (A * (A - w)) := Finset.sum_mul _ _ _
    _ ≤ ∑ g, flagMixed (left g) right cut := Finset.sum_le_sum fun g _ => hcomp g
    _ ≤ _ := RCN084.sum_flagMixed_le_of_cumulative left _ _ _ hr hm ht

private def foldedSeedsAt (Γ : Finset K) (selected : K → Polynomial K) (F : MvPolynomial (Fin 4) K) :
    Finset K := by
  classical
  exact Γ.filter fun γ => specialization K (selected γ) γ F = 0 ∧
    specialization K (selected γ) γ (dR 1 F) = 0 ∧
    specialization K (selected γ) γ (dR (chainLength F) F) ≠ 0

def foldedSeeds (H : MvPolynomial (Fin 4) K) (Γ : Finset K) (selected : K → Polynomial K) :
    Finset K := by
  classical
  exact Finset.univ.biUnion fun F : RegularIndex H => foldedSeedsAt Γ selected F.1

theorem mem_foldedSeeds {H : MvPolynomial (Fin 4) K} {Γ : Finset K}
    {selected : K → Polynomial K} {γ : K} :
    γ ∈ foldedSeeds H Γ selected ↔ γ ∈ Γ ∧ ∃ F : RegularIndex H,
      specialization K (selected γ) γ F.1 = 0 ∧
      specialization K (selected γ) γ (dR 1 F.1) = 0 ∧
      specialization K (selected γ) γ (dR (chainLength F.1) F.1) ≠ 0 := by
  classical
  simp only [foldedSeeds, Finset.mem_biUnion, Finset.mem_univ, true_and, foldedSeedsAt, Finset.mem_filter]
  exact exists_and_left

theorem folded_seed_card_le
    (support : ResidualSupportParameters) (hs : 2 ≤ support.s) (hy : 3 ≤ support.ys)
    (H : MvPolynomial (Fin 4) K) (hH : H ≠ 0) (hData : ResidualSupportData support H)
    (p : ℕ) [CharP K p] (selected : K → Polynomial K) (Γ : Finset K)
    {Node : Type*} (nodes : Finset Node) (x u₀ u₁ : Node → K) (hx : Set.InjOn x nodes)
    (w A e : ℕ) (hw : 1 ≤ w) (hchar : w < p) (hwA : w < A) (hAn : A ≤ nodes.card)
    (htotal : support.total < p)
    (hmixed : (support.ys - 1) * support.s + support.ys * (support.s - 1) < p)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hagreement : ∀ γ ∈ Γ, A ≤ (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w e) :
    (foldedSeeds H Γ selected).card ≤
      flagMixed (decreasedFlag support 0) (decreasedFlag support 1)
        (scaledFoldFlag support hs hy nodes.card w A e) / (A * (A - w)) := by
  classical
  let cut := scaledFoldFlag support hs hy nodes.card w A e
  let right := decreasedFlag support 1
  let denom := A * (A - w)
  let seeds (F : RegularIndex H) := foldedSeedsAt Γ selected F.1
  have hdenom : 0 < denom := Nat.mul_pos (Nat.zero_le w |>.trans_lt hwA) (Nat.sub_pos_of_lt hwA)
  apply (Nat.le_div_iff_mul_le hdenom).mpr
  have hlocal (F : RegularIndex H) : (seeds F).card * denom ≤
      flagMixed (originalCumulativeFlag F.1) right cut := by
    obtain ⟨hirr, hdiv, hRpos⟩ := positiveRFactors_spec H F.1 F.2
    have hsupport : ResidualSupportData support F.1 :=
      ⟨(weightedTotalDegree_le_of_dvd residualSWeights F.1 H hdiv hH).trans hData.s_weight,
        (weightedTotalDegree_le_of_dvd residualYSWeights F.1 H hdiv hH).trans hData.ys_weight,
        (weightedTotalDegree_le_of_dvd residualTotalWeights F.1 H hdiv hH).trans hData.total_weight⟩
    have hRsmall : F.1.degreeOf 2 < p :=
      (hsupport.coordinate_bounds.2.1.trans (support.s_le_ys.trans support.ys_le_total)).trans_lt htotal
    have hsub : seeds F ⊆ Γ := Finset.filter_subset _ _
    have hmem (γ : K) (hγ : γ ∈ seeds F) :=
      (Finset.mem_filter.mp hγ).2
    exact folded_original_carrier_seed_card_mul_le support hs hy F.1 hirr p hRpos hRsmall hsupport
      selected (seeds F) nodes x u₀ u₁ hx w A e hw hchar hwA hAn htotal hmixed
      (fun γ hγ => hdegree γ (hsub hγ))
      (fun γ hγ => (hmem γ hγ).1)
      (fun γ hγ => (hmem γ hγ).2.1)
      (fun γ hγ => (hmem γ hγ).2.2)
      (fun γ hγ => hagreement γ (hsub hγ))
      (noLargeSelectedPencil_mono selected Γ _ w e hsub hnoPencil)
  have hsum (weights : Fin 4 → ℕ) : (∑ F : RegularIndex H, wt weights F.1) ≤ wt weights H := by
    rw [Finset.sum_coe_sort]
    exact sum_weighted_degrees_le_of_prod_dvd weights _ id H hH (positiveRFactors_product_dvd H hH)
  have ⟨hr, hm, ht⟩ := decreasedFlag_cumulative support 0
  have hbudget : (∑ F : RegularIndex H, flagMixed (originalCumulativeFlag F.1) right cut) ≤
      flagMixed (decreasedFlag support 0) right cut := by
    apply RCN084.sum_flagMixed_le_of_cumulative
    · simp only [(originalCumulativeFlag_cumulative _).1, hr, Nat.sub_zero]
      exact (hsum residualSWeights).trans hData.s_weight
    · simp only [(originalCumulativeFlag_cumulative _).2.1, hm, Nat.sub_zero]
      exact (hsum residualYSWeights).trans hData.ys_weight
    · simp only [(originalCumulativeFlag_cumulative _).2.2, ht, Nat.sub_zero]
      exact (hsum residualTotalWeights).trans hData.total_weight
  calc
    _ ≤ (∑ F : RegularIndex H, (seeds F).card) * denom :=
      Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ F : RegularIndex H, (seeds F).card * denom := Finset.sum_mul _ _ _
    _ ≤ ∑ F : RegularIndex H, flagMixed (originalCumulativeFlag F.1) right cut :=
      Finset.sum_le_sum fun F _ => hlocal F
    _ ≤ _ := hbudget

private def primaryFoldSupport : ResidualSupportParameters :=
  ⟨93, 418, 41882, by decide, by decide, by decide, by decide⟩

open Koala6831MovingSources LocatorLowQuotient

theorem primary_folded_seed_card_le [CharP K 2130706433]
    (H : MvPolynomial (Fin 4) K) (hH : H ≠ 0)
    (hbox : H ∈ nestedCoefficientBox K Stage.primary.cutoff weight 41882 418 93)
    (Γ : Finset K) (selected : K → Polynomial K)
    {Node : Type*} (nodes : Finset Node) (x u₀ u₁ : Node → K) (hx : Set.InjOn x nodes)
    (hnodes : nodes.card = 262144)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ weight)
    (hagreement : ∀ γ ∈ Γ, agreement ≤
      (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ weight 81066) :
    (foldedSeeds H Γ selected).card ≤ 3237004435680818 := by
  have hweights := nested_mem_weights hbox hH
  have hData : ResidualSupportData primaryFoldSupport H :=
    ⟨hweights.2.2.1, hweights.2.1, hweights.1⟩
  have hAn : agreement ≤ nodes.card := by rw [hnodes]; decide +kernel
  have h := folded_seed_card_le primaryFoldSupport (by decide +kernel) (by decide +kernel)
    H hH hData 2130706433 selected Γ nodes x u₀ u₁ hx weight agreement 81066
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hAn
    (by decide +kernel) (by decide +kernel) hdegree hagreement hnoPencil
  rw [hnodes] at h
  exact h.trans (by decide +kernel)

theorem exists_primary_regular_seeds [CharP K 2130706433]
    (H : MvPolynomial (Fin 4) K) (hH : H ≠ 0)
    (hbox : H ∈ nestedCoefficientBox K Stage.primary.cutoff weight 41882 418 93)
    (Γ : Finset K) (selected : K → Polynomial K)
    {Node : Type} (nodes : Finset Node) (x u₀ u₁ : Node → K) (hx : Set.InjOn x nodes)
    (hnodes : nodes.card = 262144)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ weight)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ H = 0)
    (hagreement : ∀ γ ∈ Γ, agreement ≤
      (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ weight 81066) :
    ∃ Γreg : Finset K, Γreg ⊆ Γ ∧ Γ.card ≤ Γreg.card + 3273094414201559 ∧
      ∀ γ ∈ Γreg, ∃ F : RegularIndex H, specialization K (selected γ) γ F.1 = 0 ∧
        specialization K (selected γ) γ (RCN313.polyH K F.1) ≠ 0 := by
  classical
  let free := Γ.filter fun γ => specialization K (selected γ) γ (freeAndTailCarrier H) = 0
  let fold := foldedSeeds H Γ selected
  let discarded := free ∪ fold
  let regular := Γ \ discarded
  have hfreeSub : free ⊆ Γ := Finset.filter_subset _ _
  have hfoldSub : fold ⊆ Γ := fun γ hγ => (mem_foldedSeeds.mp hγ).1
  have hdiscSub : discarded ⊆ Γ := Finset.union_subset hfreeSub hfoldSub
  have hfree := freeAndTailCarrier_seed_count H hH hbox free selected nodes x u₀ u₁ hx hnodes
    (fun γ hγ => hdegree γ (hfreeSub hγ)) (fun γ hγ => (Finset.mem_filter.mp hγ).2)
    (fun γ hγ => hagreement γ (hfreeSub hγ))
    (noLargeSelectedPencil_mono selected Γ free weight 81066 hfreeSub hnoPencil)
  have hfold := primary_folded_seed_card_le H hH hbox Γ selected nodes x u₀ u₁ hx hnodes
    hdegree hagreement hnoPencil
  have hdisc : discarded.card ≤ 3273094414201559 :=
    (Finset.card_union_le free fold).trans (Nat.add_le_add hfree hfold)
  refine ⟨regular, Finset.sdiff_subset, ?_, ?_⟩
  · have h := Finset.card_sdiff_of_subset hdiscSub
    have hle := Finset.card_le_card hdiscSub
    change regular.card = Γ.card - discarded.card at h
    omega
  · intro γ hγ
    obtain ⟨hΓ, hdis⟩ := Finset.mem_sdiff.mp hγ
    rcases primary_regular_fold_or_free H hH (selected γ) γ (hsolution γ hΓ) with h | ⟨F, hF, h⟩
    · exact (hdis (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hΓ, h⟩))).elim
    · rcases h with h | ⟨hfold, htail⟩
      · exact ⟨F, hF, h⟩
      · exact (hdis (Finset.mem_union_right _ (mem_foldedSeeds.mpr ⟨hΓ, F, hF, hfold, htail⟩))).elim

end

end ProximityPrize.SubmissionLower.Koala6831MovingFoldCount

/- Retuned for the full 68.32 domain and the m=303 primary, November 2026. -/

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
