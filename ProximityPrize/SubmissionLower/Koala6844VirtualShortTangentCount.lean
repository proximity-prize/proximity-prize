import ProximityPrize.SubmissionLower.Koala6831MovingTangentClear
import ProximityPrize.SubmissionLower.Koala6844VirtualShortTangentList
import ProximityPrize.SubmissionLower.Koala6844VirtualShortFlowPartner
import ProximityPrize.SubmissionLower.Koala6844ActiveGerm


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped Classical BigOperators Matrix
open Koala6831Moving Koala6844Normalization
open Polynomial

noncomputable section

set_option maxHeartbeats 3500000
set_option maxRecDepth 12000

variable {K I : Type} [Field K] [CharP K TangentList.prime]
variable [Fintype I] [DecidableEq K] [DecidableEq I]

omit [CharP K TangentList.prime] [DecidableEq K] in
private theorem degreeOf_le_normalized_weight
    (c : NormalizedCoeff K) (i : Fin 2) (weights : Fin 2 → ℕ) (hi : weights i = 1) :
    c.degreeOf i ≤ c.weightedTotalDegree weights := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree weights hd
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at h
  simp only [nsmul_eq_mul, Nat.cast_id] at h
  change d 0 * weights 0 + d 1 * weights 1 ≤ c.weightedTotalDegree weights at h
  fin_cases i
  · change weights 0 = 1 at hi
    rw [hi, mul_one] at h
    change d 0 ≤ c.weightedTotalDegree weights
    omega
  · change weights 1 = 1 at hi
    rw [hi, mul_one] at h
    change d 1 ≤ c.weightedTotalDegree weights
    omega


theorem centered_tangent_seed_count
    {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K} {errors excess : ℕ}
    (data : CenteredVirtualData x nodes σ 131071 180959 errors excess)
    (support : data.d0.natDegree + affineDegree data.A0 ≤ 6677)
    (primary : P4 K) (hprimary : primary ≠ 0)
    (factors : Finset (P4 K)) (hproduct : (∏ F ∈ factors, F) ∣ primary)
    (tangent : ∀ F ∈ factors, F ∣ (centeredFlow data).flow F)
    (hcap : primary.weightedTotalDegree ![0,1,1,1] < TangentList.prime)
    (hy : primary.weightedTotalDegree ![0,1,1,0] ≤ TangentList.yTotalCap)
    (hr : primary.weightedTotalDegree ![0,0,1,0] ≤ TangentList.slopeCap)
    (seeds : Finset K) (hsub : seeds ⊆ data.seeds) (hnodes : nodes.card ≤ TangentList.n)
    (vanishes : ∀ g ∈ seeds, ∃ F ∈ factors, RCN319.specialization K (data.selected g) g F = 0) :
    seeds.card ≤ TangentList.listBudget := by
  let B : FlowData K := ⟨data.d0, data.A0 0, data.A0 1, 0, data.C1⟩
  have hd0 : B.d0 ≠ 0 := data.d0_ne
  have hden (g : K) : B.a0 + Polynomial.C g * B.a1 = specializeAffine data.A0 g := rfl
  have hoff (g : K) : B.c0 + Polynomial.C g * B.c1 = Polynomial.C g * data.C1 := by
    simp [B]
  have ha : B.A ≠ 0 := by
    have specLift (Q : Polynomial K) :
        RCN319.specialization K (0 : Polynomial K) 0 (Koala6831Moving.liftX Q) = Q := by
      have h : (RCN319.specialization K (0 : Polynomial K) 0).comp
          (Polynomial.aeval (MvPolynomial.X (0 : Fin 4) : P4 K)) =
          AlgHom.id K (Polynomial K) := by
        apply Polynomial.algHom_ext
        simp [RCN319.specialization]
      exact DFunLike.congr_fun h Q
    have spec : RCN319.specialization K (0 : Polynomial K) 0 B.A = data.A0 0 := by
      have hz : RCN319.specialization K (0 : Polynomial K) 0 (MvPolynomial.X 3) = 0 := by
        simp [RCN319.specialization]
      simp only [FlowData.A, Koala6831Moving.affine, map_add, map_mul, specLift, hz,
        zero_mul, add_zero]
      rfl
    intro hz
    rw [hz, map_zero] at spec
    exact data.denominator_ne 0 data.zero_mem (by simpa [specializeAffine] using spec.symm)
  have htangent (F : P4 K) (hF : F ∈ factors) : F ∣ B.flow F :=
    tangent F hF
  classical
  have hfamily (F : ↥factors) :
      ∃ n : ℕ, ∃ c : NormalizedCoeff K,
        B.normalize F.1 = (Polynomial.X - Polynomial.C B.normalizedRoot)^n * Polynomial.C c ∧
        c ≠ 0 ∧ (B.a1 = 0 → n = 0) ∧
        ∀ weights : Fin 2 → ℕ, weights 0 ≤ weights 1 →
          c.weightedTotalDegree weights ≤ F.1.weightedTotalDegree ![0, weights 0, weights 1, 0] := by
    have hdiv : F.1 ∣ primary := (Finset.dvd_prod_of_mem id F.2).trans hproduct
    have hF : F.1 ≠ 0 := by
      intro hz
      exact hprimary (zero_dvd_iff.mp (hz ▸ hdiv))
    have hw := RCN081.weightedTotalDegree_le_of_dvd ![0, 1, 1, 1] F.1 primary hdiv hprimary
    exact (B.transverse_or_seed_independent hd0 ha hF (hw.trans_lt hcap)).resolve_left
      (fun hn => hn (htangent F.1 F.2))
  choose power coefficient hform hnonzero hconstant hweights using hfamily
  let c := ∏ F : ↥factors, coefficient F
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun F _ => hnonzero F)
  have hyc : c.degreeOf 0 ≤ TangentList.yTotalCap := by
    calc
      c.degreeOf 0 ≤ ∑ F : ↥factors, (coefficient F).degreeOf 0 :=
        MvPolynomial.degreeOf_prod_le _ _ _
      _ ≤ ∑ F : ↥factors, F.1.weightedTotalDegree ![0, 1, 1, 0] := by
        apply Finset.sum_le_sum
        intro F _
        exact (degreeOf_le_normalized_weight (coefficient F) 0 ![1, 1] rfl).trans
          (hweights F ![1, 1] (by decide))
      _ ≤ primary.weightedTotalDegree ![0, 1, 1, 0] := by
        simpa only [Finset.sum_coe_sort, id_eq] using
          RCN293.sum_weighted_degrees_le_of_prod_dvd ![0, 1, 1, 0] factors id primary hprimary hproduct
      _ ≤ TangentList.yTotalCap := hy
  have hrc : c.degreeOf 1 ≤ TangentList.slopeCap := by
    calc
      c.degreeOf 1 ≤ ∑ F : ↥factors, (coefficient F).degreeOf 1 :=
        MvPolynomial.degreeOf_prod_le _ _ _
      _ ≤ ∑ F : ↥factors, F.1.weightedTotalDegree ![0, 0, 1, 0] := by
        apply Finset.sum_le_sum
        intro F _
        exact (degreeOf_le_normalized_weight (coefficient F) 1 ![0, 1] rfl).trans
          (hweights F ![0, 1] (by decide))
      _ ≤ primary.weightedTotalDegree ![0, 0, 1, 0] := by
        simpa only [Finset.sum_coe_sort, id_eq] using
          RCN293.sum_weighted_degrees_le_of_prod_dvd ![0, 0, 1, 0] factors id primary hprimary hproduct
      _ ≤ TangentList.slopeCap := hr

  obtain ⟨F, hF, hFY, hFR, hFZ, specialize⟩ := clear_seed_independent_carrier c hc
  have hvanish (g : K) (hg : g ∈ seeds) : evalNormalizedCoefficient (data.normalized g) c = 0 := by
    obtain ⟨P, hP, hz⟩ := vanishes g hg
    let member : ↥factors := ⟨P,hP⟩
    rw [show c = ∏ P : ↥factors, coefficient P from rfl, map_prod]
    refine Finset.prod_eq_zero_iff.mpr ⟨member, Finset.mem_univ _, ?_⟩
    apply B.seed_independent_specializes g hd0 (by rw [hden]; exact data.denominator_ne g (hsub hg))
      _ (hform member) (hconstant member) hz
    rw [hoff, hden]
    exact (data.equation0 g (hsub hg)).symm
  rw [← Finset.card_image_of_injOn (f := data.normalized)
      ((Koala6844ActiveGerm.normalized_injOn data).mono hsub)]
  have hagree : 180959 ≤ nodes.card :=
    (data.normalized_agreements 0 data.zero_mem).trans (Finset.card_filter_le _ _)
  apply TangentList.seedless_list_card_le K F hF (hFY.trans hyc) (hFR.trans hrc) hFZ
    (seeds.image data.normalized) nodes x data.fixedWord x.injective.injOn hnodes hagree
  · intro Q hQ
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hQ
    have h := data.normalized_degree g (hsub hg)
    change (data.normalized g).natDegree ≤ 137748
    omega
  · intro Q hQ
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hQ
    exact specialize _ (hvanish g hg)
  · intro Q hQ
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hQ
    convert data.normalized_agreements g (hsub hg) using 1
    all_goals
      first
      | rfl
      | congr 1
        ext i
        simp

end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort
