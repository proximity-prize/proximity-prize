/- Apache-2.0. Bome2017, price one live seed per normalized polynomial using the full hard-case hypotheses. -/
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adapted from the independent full-domain primary proof of Bome2017 after Lucieno (PR 618) and BitWonka. Exact 68.33 constants and physical hypotheses are new. -/
import ProximityPrize.SubmissionLower.Koala6831MovingTangentClear
import ProximityPrize.SubmissionLower.Left6836List
import ProximityPrize.SubmissionLower.Aligned
import ProximityPrize.SubmissionLower.Koala6831MovingNormalizedWords

namespace ProximityPrize.SubmissionLower.Koala6831Moving

open scoped Classical BigOperators

noncomputable section

variable {K I : Type} [Field K] [CharP K Left6836List.prime] [Fintype I]

abbrev left6836_tangentSeedBudget : ℕ := Left6836List.listBudget

theorem left6836_normalized_word_card_le_of_seed_independent_carrier
    (c : NormalizedCoeff K) (hc : c ≠ 0)
    (hy : c.degreeOf 0 ≤ Left6836List.yTotalCap) (hr : c.degreeOf 1 ≤ Left6836List.slopeCap)
    (words : Finset (Polynomial K)) (nodes : Finset I) (points received : I → K)
    (hinj : Set.InjOn points nodes) (hnodes : nodes.card = Left6836List.n)
    (hdegree : ∀ q ∈ words, q.natDegree ≤ Left6836List.w)
    (hagreement : ∀ q ∈ words,
      Left6836List.agreements ≤ (nodes.filter (fun i => q.eval (points i) = received i)).card)
    (hvanishes : ∀ q ∈ words, evalNormalizedCoefficient q c = 0) :
    words.card ≤ Left6836List.listBudget := by
  classical
  obtain ⟨F, hF, hFY, hFR, hFZ, hspec⟩ := clear_seed_independent_carrier c hc
  exact Left6836List.seedless_list_card_le K F hF (hFY.trans hy) (hFR.trans hr) hFZ
    words nodes points received hinj hnodes hdegree (fun q hq => hspec q (hvanishes q hq))
    hagreement

theorem FlowData.left6836_seed_card_le_of_seed_independent_carrier
    (B : FlowData K) (c : NormalizedCoeff K) (hc : c ≠ 0)
    (hy : c.degreeOf 0 ≤ Left6836List.yTotalCap) (hr : c.degreeOf 1 ≤ Left6836List.slopeCap)
    (seeds : Finset K) (selected normalized : K → Polynomial K)
    (nodes : Finset I) (points received : I → K)
    (hinj : Set.InjOn points nodes) (hnodes : nodes.card = Left6836List.n)
    (hd0 : B.d0 ≠ 0)
    (hselected : ∀ g ∈ seeds, (selected g).natDegree ≤ 131071)
    (hnorm : ∀ g ∈ seeds,
      B.d0 * selected g + B.seedOffset g = B.seedDenominator g * normalized g)
    (hdegree : ∀ g ∈ seeds, (normalized g).natDegree ≤ Left6836List.w)
    (hagreement : ∀ g ∈ seeds, Left6836List.agreements ≤
      (nodes.filter (fun i => (normalized g).eval (points i) = received i)).card)
    (hvanishes : ∀ g ∈ seeds, evalNormalizedCoefficient (normalized g) c = 0)
    (nondiv : ¬ B.d0 ∣ B.a0*B.c1-B.a1*B.c0) :
    seeds.card ≤ left6836_tangentSeedBudget := by
  classical
  have hwords := left6836_normalized_word_card_le_of_seed_independent_carrier c hc hy hr
    (seeds.image normalized) nodes points received hinj hnodes
    (fun q hq => by
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hq
      exact hdegree g hg)
    (fun q hq => by
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hq
      exact hagreement g hg)
    (fun q hq => by
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hq
      exact hvanishes g hg)
  exact KoalaNight.Aligned.seeds_le_word_list seeds B.d0 B.a0 B.a1 B.c0 B.c1 selected normalized
    nondiv hnorm _ hwords

private theorem left6836_degreeOf_le_normalized_weight
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

theorem FlowData.left6836_tangent_seed_card_le
    (B : FlowData K) (primary : P4 K) (hprimary : primary ≠ 0)
    (factors : Finset (P4 K))
    (hproduct : (∏ F ∈ factors, F) ∣ primary)
    (htangent : ∀ F ∈ factors, F ∣ B.flow F)
    (hcap : primary.weightedTotalDegree ![0, 1, 1, 1] < Left6836List.prime)
    (hy : primary.weightedTotalDegree ![0, 1, 1, 0] ≤ Left6836List.yTotalCap)
    (hr : primary.weightedTotalDegree ![0, 0, 1, 0] ≤ Left6836List.slopeCap)
    (seeds : Finset K) (selected normalized : K → Polynomial K)
    (nodes : Finset I) (points received : I → K)
    (hinj : Set.InjOn points nodes) (hnodes : nodes.card = Left6836List.n)
    (hd0 : B.d0 ≠ 0) (ha : B.A ≠ 0)
    (hden : ∀ g ∈ seeds, B.seedDenominator g ≠ 0)
    (hselected : ∀ g ∈ seeds, (selected g).natDegree ≤ 131071)
    (hnorm : ∀ g ∈ seeds,
      B.d0 * selected g + B.seedOffset g = B.seedDenominator g * normalized g)
    (hdegree : ∀ g ∈ seeds, (normalized g).natDegree ≤ Left6836List.w)
    (hagreement : ∀ g ∈ seeds, Left6836List.agreements ≤
      (nodes.filter (fun i => (normalized g).eval (points i) = received i)).card)
    (hvanishes : ∀ g ∈ seeds, ∃ F ∈ factors, RCN319.specialization K (selected g) g F = 0)
    (nondiv : ¬ B.d0 ∣ B.a0*B.c1-B.a1*B.c0) :
    seeds.card ≤ left6836_tangentSeedBudget := by
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
  have hyc : c.degreeOf 0 ≤ Left6836List.yTotalCap := by
    calc
      c.degreeOf 0 ≤ ∑ F : ↥factors, (coefficient F).degreeOf 0 :=
        MvPolynomial.degreeOf_prod_le _ _ _
      _ ≤ ∑ F : ↥factors, F.1.weightedTotalDegree ![0, 1, 1, 0] := by
        apply Finset.sum_le_sum
        intro F _
        exact (left6836_degreeOf_le_normalized_weight (coefficient F) 0 ![1, 1] rfl).trans
          (hweights F ![1, 1] (by decide))
      _ ≤ primary.weightedTotalDegree ![0, 1, 1, 0] := by
        simpa only [Finset.sum_coe_sort, id_eq] using
          RCN293.sum_weighted_degrees_le_of_prod_dvd ![0, 1, 1, 0] factors id primary hprimary hproduct
      _ ≤ Left6836List.yTotalCap := hy
  have hrc : c.degreeOf 1 ≤ Left6836List.slopeCap := by
    calc
      c.degreeOf 1 ≤ ∑ F : ↥factors, (coefficient F).degreeOf 1 :=
        MvPolynomial.degreeOf_prod_le _ _ _
      _ ≤ ∑ F : ↥factors, F.1.weightedTotalDegree ![0, 0, 1, 0] := by
        apply Finset.sum_le_sum
        intro F _
        exact (left6836_degreeOf_le_normalized_weight (coefficient F) 1 ![0, 1] rfl).trans
          (hweights F ![0, 1] (by decide))
      _ ≤ primary.weightedTotalDegree ![0, 0, 1, 0] := by
        simpa only [Finset.sum_coe_sort, id_eq] using
          RCN293.sum_weighted_degrees_le_of_prod_dvd ![0, 0, 1, 0] factors id primary hprimary hproduct
      _ ≤ Left6836List.slopeCap := hr
  apply B.left6836_seed_card_le_of_seed_independent_carrier c hc hyc hrc seeds selected normalized
    nodes points received hinj hnodes hd0 hselected hnorm hdegree hagreement _ nondiv
  intro g hg
  obtain ⟨F, hF, hsol⟩ := hvanishes g hg
  let member : ↥factors := ⟨F, hF⟩
  rw [show c = ∏ F : ↥factors, coefficient F from rfl, map_prod]
  exact Finset.prod_eq_zero_iff.mpr ⟨member, Finset.mem_univ _,
    B.seed_independent_specializes g hd0 (hden g hg) (hnorm g hg) (hform member)
      (hconstant member) hsol⟩

end

end ProximityPrize.SubmissionLower.Koala6831Moving
#print axioms ProximityPrize.SubmissionLower.Koala6831Moving.FlowData.left6836_tangent_seed_card_le
