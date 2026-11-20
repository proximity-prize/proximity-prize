/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Derived from Lucieno's PR 618 and the credited 68.32 release.
   Specialization to a primary square of degree five, November 2026. -/
import ProximityPrize.SubmissionLower.Koala6831PrimitiveDimension
import ProximityPrize.SubmissionLower.Koala6831BivariateSeeds

namespace ProximityPrize.SubmissionLower.K6969Discard
open Koala6831Comparison

open Polynomial
open scoped BigOperators Classical

noncomputable section

variable {K I : Type*} [Field K]

def conjugateWord (σ : K →+* K) (u : I → K) (j : Fin 2) (i : I) : K :=
  if j = 0 then u i else σ (u i)

def primitiveSelected (σ : K →+* K) (p : ℕ) (q : SymbolicRow (SeedRing K))
    (selected : K → Polynomial K) (g : K) : Polynomial K :=
  let E := MvPolynomial.eval (Koala6831BivariateSeeds.coordinates g (g ^ p))
  q.beta.map E + q.first.map E * selected g + q.second.map E * (selected g).map σ

private theorem seedDegree_right_factor (m q r : SeedCoefficients K) (j : Fin 2) (d : ℕ)
    (hm : m ≠ 0) (hr : r = m * q) (hd : ∀ n, (r.coeff n).degreeOf j ≤ d) :
    ∀ n, (q.coeff n).degreeOf j ≤ d := by
  by_cases hz : r = 0
  · have hq : q = 0 := (mul_eq_zero.mp (hr.symm.trans hz)).resolve_left hm
    simp [hq]
  · exact multiplier_seed_coeff_degree_le q m r j d (hr.trans (mul_comm _ _)) hz hd

private theorem x_degree_right_factor (m q r : SeedCoefficients K)
    (hm : m ≠ 0) (hr : r = m * q) : q.natDegree ≤ r.natDegree := by
  by_cases hz : r = 0
  · have hq : q = 0 := (mul_eq_zero.mp (hr.symm.trans hz)).resolve_left hm
    simp [hq, hz]
  · exact Polynomial.natDegree_le_of_dvd ⟨m, hr.trans (mul_comm _ _)⟩ hz

theorem primitive_x_degree_caps {A a d : ℕ} (θ : RowIndex A a d → K)
    (q : SymbolicRow (SeedRing K)) (m : SeedCoefficients K)
    (hm : m ≠ 0) (h : RowFactors q (rankRow θ) m) :
    q.beta.natDegree ≤ A - 1 ∧ q.first.natDegree ≤ a - 1 ∧ q.second.natDegree ≤ a - 1 :=
  ⟨(x_degree_right_factor m _ _ hm h.beta).trans (rankRow_degrees θ).1,
    (x_degree_right_factor m _ _ hm h.first).trans (rankRow_degrees θ).2.1,
    (x_degree_right_factor m _ _ hm h.second).trans (rankRow_degrees θ).2.2⟩

theorem primitive_seed_degree_caps {A a d : ℕ} (θ : RowIndex A a d → K)
    (q : SymbolicRow (SeedRing K)) (m : SeedCoefficients K)
    (hm : m ≠ 0) (h : RowFactors q (rankRow θ) m) (n : ℕ) :
    ((q.beta.coeff n).degreeOf 0 ≤ d + 1 ∧ (q.beta.coeff n).degreeOf 1 ≤ d + 1) ∧
      ((q.first.coeff n).degreeOf 0 ≤ d ∧ (q.first.coeff n).degreeOf 1 ≤ d + 1) ∧
      ((q.second.coeff n).degreeOf 0 ≤ d + 1 ∧ (q.second.coeff n).degreeOf 1 ≤ d) :=
  ⟨⟨seedDegree_right_factor _ _ _ _ _ hm h.beta
        (fun j => (symbolicRow_seed_degree_bounds θ j).1.1) n,
      seedDegree_right_factor _ _ _ _ _ hm h.beta
        (fun j => (symbolicRow_seed_degree_bounds θ j).1.2) n⟩,
    ⟨seedDegree_right_factor _ _ _ _ _ hm h.first
        (fun j => (symbolicRow_seed_degree_bounds θ j).2.1.1) n,
      seedDegree_right_factor _ _ _ _ _ hm h.first
        (fun j => (symbolicRow_seed_degree_bounds θ j).2.1.2) n⟩,
    ⟨seedDegree_right_factor _ _ _ _ _ hm h.second
        (fun j => (symbolicRow_seed_degree_bounds θ j).2.2.1) n,
      seedDegree_right_factor _ _ _ _ _ hm h.second
        (fun j => (symbolicRow_seed_degree_bounds θ j).2.2.2) n⟩⟩

private theorem lowMultiplier_seed_degree_caps {A a : ℕ} (θ : RowIndex A a 5 → K)
    (q : SymbolicRow (SeedRing K)) (m : SeedCoefficients K)
    (hm : m ≠ 0) (ha : q.first ≠ 0 ∨ q.second ≠ 0)
    (h : RowFactors q (rankRow θ) m) (n : ℕ) :
    (m.coeff n).degreeOf 0 < 7 ∧ (m.coeff n).degreeOf 1 < 7 := by
  rcases ha with ha | ha
  · have hr : (rankRow θ).first ≠ 0 := h.first ▸ mul_ne_zero hm ha
    have h₀ := multiplier_seed_coeff_degree_le m q.first _ (0 : Fin 2) 5 h.first hr
      (fun j => (symbolicRow_seed_degree_bounds θ j).2.1.1) n
    have h₁ := multiplier_seed_coeff_degree_le m q.first _ (1 : Fin 2) 6 h.first hr
      (fun j => (symbolicRow_seed_degree_bounds θ j).2.1.2) n
    omega
  · have hr : (rankRow θ).second ≠ 0 := h.second ▸ mul_ne_zero hm ha
    have h₀ := multiplier_seed_coeff_degree_le m q.second _ (0 : Fin 2) 6 h.second hr
      (fun j => (symbolicRow_seed_degree_bounds θ j).2.2.1) n
    have h₁ := multiplier_seed_coeff_degree_le m q.second _ (1 : Fin 2) 5 h.second hr
      (fun j => (symbolicRow_seed_degree_bounds θ j).2.2.2) n
    omega

private theorem seedDegree_at_base (P : SeedCoefficients K) (x : K) (j : Fin 2) (d : ℕ)
    (ha : ∀ n, (P.coeff n).degreeOf j ≤ d) :
    (P.eval (MvPolynomial.C x)).degreeOf j ≤ d := by
  rw [P.eval_eq_sum_range' (Nat.lt_succ_self P.natDegree)]
  apply (MvPolynomial.degreeOf_sum_le j _ _).trans
  apply Finset.sup_le
  intro n _
  apply (MvPolynomial.degreeOf_mul_le j _ _).trans
  simpa only [← map_pow, MvPolynomial.degreeOf_C, Nat.add_zero] using ha n

private theorem affineSeedWord_degree (u v : Fin 2 → I → K) (i : I) (j k : Fin 2) :
    (affineSeedWord u v k i).degreeOf j ≤ if j = k then 1 else 0 := by
  unfold affineSeedWord
  apply (MvPolynomial.degreeOf_add_le j _ _).trans
  apply max_le
  · simp
  · apply (MvPolynomial.degreeOf_mul_le j _ _).trans
    by_cases h : j = k
    · subst j
      simp
    · simp [MvPolynomial.degreeOf_X_of_ne h, h]

theorem lowPrimitiveNode_degree {A a : ℕ} (θ : RowIndex A a 5 → K)
    (q : SymbolicRow (SeedRing K)) (m : SeedCoefficients K)
    (hm : m ≠ 0) (h : RowFactors q (rankRow θ) m)
    (x : I ↪ K) (u v : Fin 2 → I → K) (i : I) :
    let P := q.atNode (seedNode x i) (affineSeedWord u v 0 i) (affineSeedWord u v 1 i)
    P.degreeOf 0 < 7 ∧ P.degreeOf 1 < 7 := by
  have hβ (j : Fin 2) : ((q.beta.eval (MvPolynomial.C (x i))).degreeOf j) ≤ 6 := by
    apply seedDegree_at_base
    intro n
    fin_cases j
    · exact (primitive_seed_degree_caps θ q m hm h n).1.1
    · exact (primitive_seed_degree_caps θ q m hm h n).1.2
  have hfirst (j : Fin 2) : ((q.first.eval (MvPolynomial.C (x i))).degreeOf j) ≤
      if j = 0 then 5 else 6 := by
    apply seedDegree_at_base
    intro n
    fin_cases j
    · exact (primitive_seed_degree_caps θ q m hm h n).2.1.1
    · exact (primitive_seed_degree_caps θ q m hm h n).2.1.2
  have hsecond (j : Fin 2) : ((q.second.eval (MvPolynomial.C (x i))).degreeOf j) ≤
      if j = 1 then 5 else 6 := by
    apply seedDegree_at_base
    intro n
    fin_cases j
    · exact (primitive_seed_degree_caps θ q m hm h n).2.2.1
    · exact (primitive_seed_degree_caps θ q m hm h n).2.2.2
  have hout (j : Fin 2) :
      (q.atNode (seedNode x i) (affineSeedWord u v 0 i) (affineSeedWord u v 1 i)).degreeOf j ≤ 6 := by
    change (q.beta.eval (MvPolynomial.C (x i)) +
      q.first.eval (MvPolynomial.C (x i)) * affineSeedWord u v 0 i +
      q.second.eval (MvPolynomial.C (x i)) * affineSeedWord u v 1 i).degreeOf j ≤ 6
    apply (MvPolynomial.degreeOf_add_le j _ _).trans
    apply max_le
    · apply (MvPolynomial.degreeOf_add_le j _ _).trans
      apply max_le (hβ j)
      apply (MvPolynomial.degreeOf_mul_le j _ _).trans
      have hb := Nat.add_le_add (hfirst j) (affineSeedWord_degree u v i j 0)
      exact hb.trans (by fin_cases j <;> decide)
    · apply (MvPolynomial.degreeOf_mul_le j _ _).trans
      have hb := Nat.add_le_add (hsecond j) (affineSeedWord_degree u v i j 1)
      exact hb.trans (by fin_cases j <;> decide)
  exact ⟨Nat.lt_succ_of_le (hout 0), Nat.lt_succ_of_le (hout 1)⟩

private theorem eval_seedNode (P : SeedCoefficients K) (x : K) (z : Fin 2 → K) :
    MvPolynomial.eval z (P.eval (MvPolynomial.C x)) =
      (P.map (MvPolynomial.eval z)).eval x := by
  have h : (P.map (MvPolynomial.eval z)).eval (MvPolynomial.eval z (MvPolynomial.C x)) =
      MvPolynomial.eval z (P.eval (MvPolynomial.C x)) :=
    Polynomial.eval_map_apply (MvPolynomial.eval z) (MvPolynomial.C x)
  simpa only [MvPolynomial.eval_C] using h.symm

private theorem eval_conjugate_polynomial (σ : K →+* K) (x : I ↪ K)
    (hfixed : ∀ i, σ (x i) = x i) (P : Polynomial K) (i : I) :
    (P.map σ).eval (x i) = σ (P.eval (x i)) := by
  have h : (P.map σ).eval (σ (x i)) = σ (P.eval (x i)) := Polynomial.eval_map_apply σ (x i)
  simpa only [hfixed i] using h

theorem retain_primitive_rows [Fintype I] {A a w p : ℕ}
    (x : I ↪ K) (σ : K →+* K) (hfixed : ∀ i, σ (x i) = x i)
    (hsigma : ∀ g, σ g = g ^ p) (hp : 7 ≤ p)
    (U : Fin 2 → I → K) (ha : 0 < a) (hA : a + w = A)
    (θ : ComparisonSpace A a 5 x (conjugateWord σ (U 0)) (conjugateWord σ (U 1)))
    (q : SymbolicRow (SeedRing K)) (m : SeedCoefficients K) (hm : m ≠ 0)
    (hq : q.first ≠ 0 ∨ q.second ≠ 0) (hf : RowFactors q (rankRow θ.1) m)
    (seeds : Finset K) (agree : K → Finset I) (selected : K → Polynomial K)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hcard : ∀ g ∈ seeds, A ≤ (agree g).card)
    (hagree : ∀ g ∈ seeds, ∀ i ∈ agree g, (selected g).eval (x i) = U 0 i + g * U 1 i) :
    let bad := primitiveBadNodes x (conjugateWord σ (U 0)) (conjugateWord σ (U 1)) q
    ∃ retained : Finset K, retained ⊆ seeds ∧
      seeds.card ≤ retained.card + (bad.card + 1) * (6 * (p + 1)) ∧
      ∀ g ∈ retained, primitiveSelected σ p q selected g = 0 ∧ Disjoint (agree g) bad := by
  let u := conjugateWord σ (U 0)
  let v := conjugateWord σ (U 1)
  let bad := primitiveBadNodes x u v q
  let test (i : I) := q.atNode (seedNode x i) (affineSeedWord u v 0 i) (affineSeedWord u v 1 i)
  have hproduct (g : K) (hg : g ∈ seeds) :
      m.map (MvPolynomial.eval (Koala6831BivariateSeeds.coordinates g (g ^ p))) *
        primitiveSelected σ p q selected g = 0 := by
    let z := Koala6831BivariateSeeds.coordinates g (g ^ p)
    let E := MvPolynomial.eval z
    have hr := specialize_selected_eq_zero x U σ hfixed ha hA θ g (selected g)
      (hdegree g hg) (agree g) (hcard g hg) (hagree g hg)
    obtain ⟨hb, h₀, h₁⟩ := symbolicRow_map_seedEval θ.1 z
    have hraw : (rankRow θ.1).beta.map E +
        (rankRow θ.1).first.map E * selected g +
        (rankRow θ.1).second.map E * (selected g).map σ = 0 := by
      change (symbolicRow θ.1).beta.map E + (symbolicRow θ.1).first.map E * selected g +
        (symbolicRow θ.1).second.map E * (selected g).map σ = 0
      rw [hb, h₀, h₁]
      simpa [z, Koala6831BivariateSeeds.coordinates, hsigma g] using hr
    change m.map E * primitiveSelected σ p q selected g = 0
    calc
      _ = (rankRow θ.1).beta.map E +
          (rankRow θ.1).first.map E * selected g +
          (rankRow θ.1).second.map E * (selected g).map σ := by
        simp only [primitiveSelected, hf.beta, hf.first, hf.second, Polynomial.map_mul, E]
        ring
      _ = _ := hraw
  have hnodeZero (i : I) (g : K) (hg : g ∈ seeds) (hgi : i ∈ agree g)
      (hmE : m.map (MvPolynomial.eval (Koala6831BivariateSeeds.coordinates g (g ^ p))) ≠ 0) :
      MvPolynomial.eval (Koala6831BivariateSeeds.coordinates g (g ^ p)) (test i) = 0 := by
    let z := Koala6831BivariateSeeds.coordinates g (g ^ p)
    have hprim := (mul_eq_zero.mp (hproduct g hg)).resolve_left hmE
    have hroot := congrArg (Polynomial.eval (x i)) hprim
    have hcEval := eval_conjugate_polynomial σ x hfixed (selected g) i
    have hAgree := hagree g hg i hgi
    have hConj : ((selected g).map σ).eval (x i) = σ (U 0 i) + g ^ p * σ (U 1 i) := by
      rw [hcEval, hAgree, map_add, map_mul, hsigma g]
    have hroot' : ((primitiveSelected σ p q selected g).eval (x i)) = 0 := by
      simpa only [Polynomial.eval_zero] using hroot
    simpa [test, SymbolicRow.atNode, seedNode, affineSeedWord, u, v, conjugateWord,
      z, Koala6831BivariateSeeds.coordinates, eval_seedNode, primitiveSelected,
      Polynomial.eval_mul, Polynomial.eval_add, hAgree, hConj] using hroot'
  let multiplier (g : K) := m.map (MvPolynomial.eval (Koala6831BivariateSeeds.coordinates g (g ^ p)))
  let singular := seeds.filter fun g => multiplier g = 0
  let regular := seeds \ singular
  let atBad (i : I) := regular.filter fun g => i ∈ agree g
  let badSeeds := bad.biUnion atBad
  let retained := regular \ badSeeds
  have hmultNonzero (g : K) (hg : g ∈ regular) : multiplier g ≠ 0 := by
    intro hz
    exact (Finset.mem_sdiff.mp hg).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hg).1, hz⟩)
  have hsingularSubset : singular ⊆ seeds := Finset.filter_subset _ _
  have hbadSubset : badSeeds ⊆ regular := by
    intro g hg
    obtain ⟨i, _, hgi⟩ := Finset.mem_biUnion.mp hg
    exact (Finset.mem_filter.mp hgi).1
  let limit := 6 + p * 6
  have hsingular : singular.card ≤ limit := by
    have hcap := lowMultiplier_seed_degree_caps θ.1 q m hm hq hf m.natDegree
    have hcoeff : m.coeff m.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hm
    apply Koala6831BivariateSeeds.card_le_of_vanishing (b := 7) (c := 7)
      (by omega : 0 < p) hp hcoeff hcap.1 hcap.2
    intro g hg
    have hz : multiplier g = 0 := (Finset.mem_filter.mp hg).2
    have he := congrArg (fun P : Polynomial K => P.coeff m.natDegree) hz
    simpa only [multiplier, Polynomial.coeff_map, Polynomial.coeff_zero] using he
  have hbadSeeds : badSeeds.card ≤ bad.card * limit := by
    calc
      _ ≤ ∑ i ∈ bad, (atBad i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ bad, limit := by
        apply Finset.sum_le_sum
        intro i hi
        have hcap := lowPrimitiveNode_degree θ.1 q m hm hf x u v i
        have hnonzero : test i ≠ 0 := (Finset.mem_filter.mp hi).2
        apply Koala6831BivariateSeeds.card_le_of_vanishing (b := 7) (c := 7)
          (by omega : 0 < p) hp hnonzero hcap.1 hcap.2
        intro g hg
        obtain ⟨hreg, hgi⟩ := Finset.mem_filter.mp hg
        exact hnodeZero i g (Finset.sdiff_subset hreg) hgi (hmultNonzero g hreg)
      _ = _ := by simp [Nat.mul_comm]
  have hsum : seeds.card = regular.card + singular.card := by
    change _ = (seeds \ singular).card + singular.card
    rw [Finset.card_sdiff_of_subset hsingularSubset]
    exact (Nat.sub_add_cancel (Finset.card_le_card hsingularSubset)).symm
  have hsum' : regular.card = retained.card + badSeeds.card := by
    change _ = (regular \ badSeeds).card + badSeeds.card
    rw [Finset.card_sdiff_of_subset hbadSubset]
    exact (Nat.sub_add_cancel (Finset.card_le_card hbadSubset)).symm
  refine ⟨retained, Finset.sdiff_subset.trans Finset.sdiff_subset, ?_, ?_⟩
  · calc
      seeds.card = retained.card + badSeeds.card + singular.card := by rw [hsum, hsum']
      _ ≤ retained.card + bad.card * limit + limit :=
        Nat.add_le_add (Nat.add_le_add_left hbadSeeds _) hsingular
      _ = _ := by dsimp [limit]; ring
  · intro g hg
    obtain ⟨hreg, hkeep⟩ := Finset.mem_sdiff.mp hg
    refine ⟨(mul_eq_zero.mp (hproduct g (Finset.sdiff_subset hreg))).resolve_left
      (hmultNonzero g hreg), ?_⟩
    rw [Finset.disjoint_left]
    intro i hgi hi
    exact hkeep (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hreg, hgi⟩⟩)

#print axioms retain_primitive_rows
end

end ProximityPrize.SubmissionLower.K6969Discard
