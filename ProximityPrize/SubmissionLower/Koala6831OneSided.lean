import ProximityPrize.SubmissionLower.Koala6831RankTwo

namespace ProximityPrize.SubmissionLower.Koala6831OneSided

open Koala6831Comparison Koala6831BivariateSeeds
open Polynomial
open scoped Classical BigOperators

noncomputable section

set_option autoImplicit false

variable {K I : Type} [Field K]

private theorem map_eval_at_fixed_node (x : I ↪ K) (τ : K →+* K)
    (hfixed : ∀ i, τ (x i) = x i) (P : K[X]) (i : I) :
    (P.map τ).eval (x i) = τ (P.eval (x i)) := by
  rw [← hfixed i, Polynomial.eval_map_apply, hfixed i]

private theorem identity_nodes_card_le
    (x : I ↪ K) (u₀ u₁ : I → K) (τ : K →+* K)
    (hfixed : ∀ i, τ (x i) = x i)
    (selected : K → K[X]) (D N : K → K[X]) (hD : ∀ x, D x ≠ 0)
    (seeds : Finset K) (identities : Finset I) (w e denCap : ℕ)
    (hDdegree : ∀ x, (D x).natDegree ≤ denCap)
    (hcard : w < identities.card)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hidentity : ∀ i ∈ identities, ∀ g ∈ seeds,
      (N (x i)).eval g = (D (x i)).eval g * τ (u₀ i + g * u₁ i))
    (hchart : ∀ g ∈ seeds, ∀ i,
      (D (x i)).eval g * ((selected g).map τ).eval (x i) = (N (x i)).eval g)
    (hpencil : ∀ q₀ q₁ : K[X], q₀.natDegree ≤ w → q₁.natDegree ≤ w →
      (RCN050.pencilSeeds seeds selected q₀ q₁).card ≤ e + 1) :
    seeds.card ≤ (w + 1) * denCap + (e + 1) := by
  obtain ⟨testNodes, hnodes, htestCard⟩ :=
    Finset.exists_subset_card_eq (show w + 1 ≤ identities.card by omega)
  let failing (i : I) := seeds.filter (fun g => (D (x i)).eval g = 0)
  let excluded := testNodes.biUnion failing
  let retained := seeds \ excluded
  have hexcluded : excluded ⊆ seeds := by
    intro g hg
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hg
    exact (Finset.mem_filter.mp hi).1
  have hfail (i : I) : (failing i).card ≤ denCap := by
    apply le_trans _ (hDdegree (x i))
    apply Polynomial.card_le_degree_of_subset_roots
    intro g hg
    exact (Polynomial.mem_roots (hD (x i))).mpr (Finset.mem_filter.mp hg).2
  have hexcludedCard : excluded.card ≤ (w + 1) * denCap := by
    calc
      excluded.card ≤ ∑ i ∈ testNodes, (failing i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ testNodes, denCap := Finset.sum_le_sum fun i _ => hfail i
      _ = (w + 1) * denCap := by simp [htestCard]
  have hretainedValues (g : ↥retained) (i : I) (hi : i ∈ testNodes) :
      (selected (g : K)).eval (x i) = u₀ i + (g : K) * u₁ i := by
    obtain ⟨hg, hv⟩ := Finset.mem_sdiff.mp g.property
    have hnonzero : (D (x i)).eval (g : K) ≠ 0 := by
      intro h
      apply hv
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hg, h⟩⟩
    apply τ.injective
    apply mul_left_cancel₀ hnonzero
    calc
      _ = (D (x i)).eval (g : K) * ((selected (g : K)).map τ).eval (x i) := by
        rw [map_eval_at_fixed_node x τ hfixed]
      _ = (N (x i)).eval (g : K) := hchart (g : K) hg i
      _ = _ := hidentity i (hnodes hi) (g : K) hg
  obtain ⟨q₀, q₁, h₀, h₁, hfit⟩ := RCN147.exists_basefield_affine_pencil_of_identity_nodes
    (RingHom.id K) testNodes x u₀ u₁ w (by omega) x.injective.injOn
    (fun g : ↥retained => (g : K)) (fun g => selected g)
    (fun g => hdegree (g : K) (Finset.mem_sdiff.mp g.property).1)
    (fun g i hi => by simpa only [RingHom.id_apply] using hretainedValues g i hi)
  have hretainedCard : retained.card ≤ e + 1 := by
    apply (Finset.card_le_card (t := RCN050.pencilSeeds seeds selected q₀ q₁) ?_).trans
      (hpencil q₀ q₁ h₀ h₁)
    intro g hg
    apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_sdiff.mp hg).1, ?_⟩
    simpa only [Polynomial.map_id] using hfit ⟨g, hg⟩
  have hsum : retained.card + excluded.card = seeds.card := by
    rw [show retained.card = seeds.card - excluded.card from Finset.card_sdiff_of_subset hexcluded]
    exact Nat.sub_add_cancel (Finset.card_le_card hexcluded)
  omega

private theorem encoded_chart_card_le
    (x : I ↪ K) (u₀ u₁ : I → K) (τ : K →+* K)
    (hfixed : ∀ i, τ (x i) = x i) (power : ℕ) (hpower : ∀ g, τ g = g ^ power)
    (selected : K → K[X]) (denominator numerator : Polynomial K[X]) (hne : denominator ≠ 0)
    (seeds : Finset K) (nodes : Finset I) (w A e denCap numCap : ℕ)
    (hw : w < A) (hA : A ≤ nodes.card)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hagreement : ∀ g ∈ seeds,
      A ≤ (nodes.filter (fun i => (selected g).eval (x i) = u₀ i + g * u₁ i)).card)
    (hDdegree : ∀ j, (denominator.coeff j).natDegree ≤ denCap)
    (hNdegree : ∀ j, (numerator.coeff j).natDegree ≤ numCap)
    (heq : ∀ g ∈ seeds, denominator.map (evalRingHom g) * (selected g).map τ =
      numerator.map (evalRingHom g))
    (hpencil : ∀ q₀ q₁ : K[X], q₀.natDegree ≤ w → q₁.natDegree ≤ w →
      (RCN050.pencilSeeds seeds selected q₀ q₁).card ≤ e + 1) :
    seeds.card ≤ max ((nodes.card - w) * max numCap (denCap + power) / (A - w))
      ((w + 1) * denCap + (e + 1)) := by
  obtain ⟨D, N, hD, hDcap, hNcap, hnode⟩ :=
    Koala6831ChartNormalization.exists_node_tests denominator numerator hne denCap numCap
      hDdegree hNdegree
  let word (i : I) : Polynomial K := C (τ (u₀ i)) + (Polynomial.X : Polynomial K) ^ power * C (τ (u₁ i))
  let test (i : I) := N (x i) - D (x i) * word i
  let identities := nodes.filter (fun i => test i = 0)
  have hWordEval (i : I) (g : K) : (word i).eval g = τ (u₀ i + g * u₁ i) := by
    simp only [word, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, map_add, map_mul, hpower g]
  have hWordDegree (i : I) : (word i).natDegree ≤ power := by
    dsimp only [word]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
    exact (Polynomial.natDegree_mul_C_le _ _).trans (by simp)
  have htestDegree (i : I) : (test i).natDegree ≤ max numCap (denCap + power) := by
    unfold test
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le_max (hNcap (x i)) ?_)
    exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hDcap (x i)) (hWordDegree i))
  have hnodeChart (g : K) (hg : g ∈ seeds) (i : I) :
      (D (x i)).eval g * ((selected g).map τ).eval (x i) = (N (x i)).eval g :=
    hnode (x i) g ((selected g).map τ) (heq g hg)
  have htestEval (i : I) (g : K) :
      (test i).eval g = (N (x i)).eval g - (D (x i)).eval g * τ (u₀ i + g * u₁ i) := by
    simp only [test, Polynomial.eval_sub, Polynomial.eval_mul, hWordEval i]
  by_cases hsmall : identities.card ≤ w
  · apply le_trans _ (le_max_left _ _)
    apply (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hw)).mpr
    apply RCN173.sharp_incidence_bound
      (fun g i => (selected g).eval (x i) = u₀ i + g * u₁ i)
      seeds nodes identities A w (max numCap (denCap + power)) (Finset.filter_subset _ _)
      hsmall hw hA hagreement
    intro i hi
    have hnonzero : test i ≠ 0 := by
      intro hz
      obtain ⟨hmem, hnot⟩ := Finset.mem_sdiff.mp hi
      exact hnot (Finset.mem_filter.mpr ⟨hmem, hz⟩)
    apply le_trans _ (htestDegree i)
    apply Polynomial.card_le_degree_of_subset_roots
    intro g hg
    obtain ⟨hseed, hfit⟩ := Finset.mem_filter.mp hg
    apply (Polynomial.mem_roots hnonzero).mpr
    rw [Polynomial.IsRoot, htestEval, ← hnodeChart g hseed i,
      map_eval_at_fixed_node x τ hfixed, hfit, sub_self]
  · apply le_trans _ (le_max_right _ _)
    refine identity_nodes_card_le x u₀ u₁ τ hfixed selected D N hD seeds identities
      w e denCap hDcap (Nat.lt_of_not_ge hsmall) hdegree ?_ hnodeChart hpencil
    intro i hi g _
    have hz : test i = 0 := (Finset.mem_filter.mp hi).2
    have h := congrArg (Polynomial.eval g) hz
    rw [htestEval, Polynomial.eval_zero] at h
    exact sub_eq_zero.mp h

def SeedDegreeFive (F : Polynomial (SeedPolynomial K)) : Prop :=
  ∀ j, (F.coeff j).degreeOf 0 ≤ 5 ∧ (F.coeff j).degreeOf 1 ≤ 5

private theorem map_frobenius_eval (F : Polynomial (SeedPolynomial K)) (p : ℕ) (g : K) :
    (F.map (frobeniusHom p)).map (evalRingHom g) =
      F.map (MvPolynomial.eval (coordinates g (g ^ p))) := by
  have h : (evalRingHom g).comp (frobeniusHom p) =
      MvPolynomial.eval (coordinates g (g ^ p)) := by
    apply RingHom.ext
    intro S
    exact eval_frobeniusHom p S g
  rw [Polynomial.map_map, h]

private theorem map_frobenius_coeff_degree (F : Polynomial (SeedPolynomial K))
    (hF : SeedDegreeFive F) (p j : ℕ) :
    ((F.map (frobeniusHom p)).coeff j).natDegree ≤ 5 * (p + 1) := by
  rw [Polynomial.coeff_map]
  have h := hF j
  refine (natDegree_frobeniusHom_le (b := 6) (c := 6) p _
    (Nat.lt_succ_of_le h.1) (Nat.lt_succ_of_le h.2)).trans_eq ?_
  simp
  omega

private theorem map_frobenius_ne_zero {p : ℕ} (hp : 0 < p) (hwidth : 6 ≤ p)
    (F : Polynomial (SeedPolynomial K)) (hF : SeedDegreeFive F) (hne : F ≠ 0) :
    F.map (frobeniusHom p) ≠ 0 := by
  obtain ⟨j, hj⟩ := Polynomial.support_nonempty.mpr hne
  intro hz
  apply frobeniusHom_nonzero hp hwidth (Polynomial.mem_support_iff.mp hj)
    (b := 6) (c := 6) (Nat.lt_succ_of_le (hF j).1) (Nat.lt_succ_of_le (hF j).2)
  simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using
    congrArg (fun q : Polynomial K[X] => q.coeff j) hz

theorem primitive_rows_card_le {p w A e : ℕ} (hp : 0 < p) (hwidth : 6 ≤ p)
    (x : I ↪ K) (u₀ u₁ : I → K) (σ : K →+* K)
    (hfixed : ∀ i, σ (x i) = x i) (hσ : ∀ g, σ g = g ^ p)
    (β α₀ α₁ : Polynomial (SeedPolynomial K))
    (hβ : SeedDegreeFive β) (h₀ : SeedDegreeFive α₀) (h₁ : SeedDegreeFive α₁)
    (hone : (α₀ ≠ 0 ∧ α₁ = 0) ∨ (α₀ = 0 ∧ α₁ ≠ 0))
    (seeds : Finset K) (nodes : Finset I) (selected : K → K[X])
    (hwa : w < A) (han : A ≤ nodes.card)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hagreement : ∀ g ∈ seeds,
      A ≤ (nodes.filter (fun i => (selected g).eval (x i) = u₀ i + g * u₁ i)).card)
    (hrow : ∀ g ∈ seeds,
      let f := MvPolynomial.eval (coordinates g (g ^ p))
      β.map f + α₀.map f * selected g + α₁.map f * (selected g).map σ = 0)
    (hpencil : ∀ q₀ q₁ : K[X], q₀.natDegree ≤ w → q₁.natDegree ≤ w →
      (RCN050.pencilSeeds seeds selected q₀ q₁).card ≤ e + 1) :
    seeds.card ≤ max ((nodes.card - w) * (6 * (p + 1)) / (A - w))
      ((w + 1) * (5 * (p + 1)) + (e + 1)) := by
  let N := (-β).map (frobeniusHom p)
  have hNdegree : ∀ j, (N.coeff j).natDegree ≤ 5 * (p + 1) := by
    intro j
    simpa only [N, Polynomial.map_neg, Polynomial.coeff_neg, Polynomial.natDegree_neg]
      using map_frobenius_coeff_degree β hβ p j
  have count (α : Polynomial (SeedPolynomial K)) (hα : SeedDegreeFive α) (hne : α ≠ 0)
      (τ : K →+* K) (hτfixed : ∀ i, τ (x i) = x i) (power : ℕ)
      (hpower : ∀ g, τ g = g ^ power) (hpowerLe : power ≤ p)
      (hproduct : ∀ g ∈ seeds,
        let f := MvPolynomial.eval (coordinates g (g ^ p))
        α.map f * (selected g).map τ = (-β).map f) :
      seeds.card ≤ max ((nodes.card - w) * (6 * (p + 1)) / (A - w))
        ((w + 1) * (5 * (p + 1)) + (e + 1)) := by
    have hChart : ∀ g ∈ seeds, ((α.map (frobeniusHom p)).map (evalRingHom g)) * (selected g).map τ =
        N.map (evalRingHom g) := by
      intro g hg
      dsimp only [N]
      rw [map_frobenius_eval, map_frobenius_eval]
      exact hproduct g hg
    apply (encoded_chart_card_le x u₀ u₁ τ hτfixed power hpower selected _ N
      (map_frobenius_ne_zero hp hwidth α hα hne) seeds nodes w A e _ _
      hwa han hdegree hagreement (map_frobenius_coeff_degree α hα p) hNdegree hChart hpencil).trans
    apply max_le_max _ le_rfl
    exact Nat.div_le_div_right (Nat.mul_le_mul_left _ (max_le (by omega) (by omega)))
  rcases hone with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
  · apply count α₀ h₀ hfirst (RingHom.id K) (fun _ => rfl) 1 (fun g => by simp) (by omega)
    intro g hg
    have hh := hrow g hg
    simp only [hsecond, Polynomial.map_zero, zero_mul, add_zero] at hh
    simp only [Polynomial.map_neg, Polynomial.map_id]
    linear_combination hh
  · apply count α₁ h₁ hsecond σ hfixed p hσ le_rfl
    intro g hg
    have hh := hrow g hg
    simp only [hfirst, Polynomial.map_zero, zero_mul, add_zero] at hh
    simp only [Polynomial.map_neg]
    linear_combination hh

theorem one_sided_of_nonzero_multiplier
    {m a₀ a₁ : Polynomial (SeedPolynomial K)} (hm : m ≠ 0)
    (hone : (a₀ ≠ 0 ∧ a₁ = 0) ∨ (a₀ = 0 ∧ a₁ ≠ 0)) :
    (m * a₀ ≠ 0 ∧ m * a₁ = 0) ∨ (m * a₀ = 0 ∧ m * a₁ ≠ 0) := by
  rcases hone with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
  · exact Or.inl ⟨mul_ne_zero hm h₀, by rw [h₁, mul_zero]⟩
  · exact Or.inr ⟨by rw [h₀, mul_zero], mul_ne_zero hm h₁⟩

theorem one_sided_comparison_card_le [Fintype I]
    {p w A a e : ℕ} (hp : 0 < p) (hwidth : 6 ≤ p)
    (x : I ↪ K) (U : Fin 2 → I → K) (σ : K →+* K)
    (hfixed : ∀ i, σ (x i) = x i) (hσ : ∀ g, σ g = g ^ p)
    (haPos : 0 < a) (ha : a + w = A) (han : A ≤ Fintype.card I)
    (θ : ComparisonSpace A a 4 x (fun j i => if j = 0 then U 0 i else σ (U 0 i))
      (fun j i => if j = 0 then U 1 i else σ (U 1 i)))
    (hone : let q := symbolicRow θ.1
      (q.first ≠ 0 ∧ q.second = 0) ∨ (q.first = 0 ∧ q.second ≠ 0))
    (seeds : Finset K) (selected : K → K[X])
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hagreement : ∀ g ∈ seeds,
      A ≤ (Finset.univ.filter (fun i => (selected g).eval (x i) = U 0 i + g * U 1 i)).card)
    (hpencil : ∀ q₀ q₁ : K[X], q₀.natDegree ≤ w → q₁.natDegree ≤ w →
      (RCN050.pencilSeeds seeds selected q₀ q₁).card ≤ e + 1) :
    seeds.card ≤ max ((Fintype.card I - w) * (6 * (p + 1)) / (A - w))
      ((w + 1) * (5 * (p + 1)) + (e + 1)) := by
  rw [← Finset.card_univ (α := I)]
  refine primitive_rows_card_le hp hwidth x (U 0) (U 1) σ hfixed hσ
    (symbolicRow θ.1).beta (symbolicRow θ.1).first (symbolicRow θ.1).second
    ?_ ?_ ?_ hone seeds Finset.univ selected (by omega) (by simpa using han)
    hdegree hagreement ?_ hpencil
  · intro j
    exact (symbolicRow_seed_degree_bounds θ.1 j).1
  · intro j
    have hb := (symbolicRow_seed_degree_bounds θ.1 j).2.1
    exact ⟨hb.1.trans (by decide), hb.2⟩
  · intro j
    have hb := (symbolicRow_seed_degree_bounds θ.1 j).2.2
    exact ⟨hb.1, hb.2.trans (by decide)⟩
  · intro g hg
    dsimp only
    obtain ⟨hb, h₀, h₁⟩ := symbolicRow_map_seedEval θ.1 (coordinates g (g ^ p))
    rw [hb, h₀, h₁]
    simpa [coordinates, ← hσ g] using
      specialize_selected_eq_zero x U σ hfixed haPos ha θ g (selected g) (hdegree g hg)
        _ (hagreement g hg) (fun _ hi => (Finset.mem_filter.mp hi).2)

theorem koala_one_sided_budget :
    max ((262144 - 131071 : ℕ) * (6 * (2130706433 + 1)) / (181078 - 131071))
      ((131071 + 1) * (5 * (2130706433 + 1)) + (81066 + 1)) =
      1396379768667307 := by
  decide +kernel

end

end ProximityPrize.SubmissionLower.Koala6831OneSided

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
