import ProximityPrize.SubmissionLower.LowerFoundation
import ProximityPrize.SubmissionLower.Koala6831ChartNormalization

namespace ProximityPrize.SubmissionLower.Koala6831CramerIncidence

open scoped Classical BigOperators

noncomputable section

set_option autoImplicit false

theorem first_coordinate_cramer {R : Type*} [CommRing R]
    (a₀ a₁ b c₀ c₁ d P Q : R)
    (h₀ : b + a₀ * P + a₁ * Q = 0) (h₁ : d + c₀ * P + c₁ * Q = 0) :
    (a₀ * c₁ - a₁ * c₀) * P = a₁ * d - b * c₁ := by
  linear_combination c₁ * h₀ - a₁ * h₁

variable {K I : Type} [Field K] [DecidableEq K] [DecidableEq I]

omit [DecidableEq I] in
private theorem identity_nodes_bound
    (x : I ↪ K) (u₀ u₁ : I → K) (selected : K → Polynomial K)
    (denominator numerator : I → Polynomial K)
    (seeds : Finset K) (identities : Finset I) (w e denominatorBudget : ℕ)
    (hcard : w < identities.card)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hidentity : ∀ i ∈ identities, ∀ g ∈ seeds,
      (numerator i).eval g = (denominator i).eval g * (u₀ i + g * u₁ i))
    (hcramer : ∀ g ∈ seeds, ∀ i,
      (denominator i).eval g * (selected g).eval (x i) = (numerator i).eval g)
    (hzero : ∀ i ∈ identities,
      (seeds.filter (fun g => (denominator i).eval g = 0)).card ≤ denominatorBudget)
    (hpencil : ∀ p₀ p₁ : Polynomial K, p₀.natDegree ≤ w → p₁.natDegree ≤ w →
      (RCN050.pencilSeeds seeds selected p₀ p₁).card ≤ e + 1) :
    seeds.card ≤ (w + 1) * denominatorBudget + (e + 1) := by
  obtain ⟨testNodes, hnodes, htestCard⟩ :=
    Finset.exists_subset_card_eq (show w + 1 ≤ identities.card by omega)
  let failing (i : I) := seeds.filter (fun g => (denominator i).eval g = 0)
  let excluded := testNodes.biUnion failing
  let retained := seeds \ excluded
  have hexcluded : excluded ⊆ seeds := by
    intro g hg
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hg
    exact (Finset.mem_filter.mp hi).1
  have hexcludedCard : excluded.card ≤ (w + 1) * denominatorBudget := by
    calc
      excluded.card ≤ ∑ i ∈ testNodes, (failing i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ testNodes, denominatorBudget := Finset.sum_le_sum fun i hi =>
        hzero i (hnodes hi)
      _ = (w + 1) * denominatorBudget := by simp [htestCard]
  have hretainedValues (g : ↥retained) (i : I) (hi : i ∈ testNodes) :
      (selected (g : K)).eval (x i) = u₀ i + (g : K) * u₁ i := by
    obtain ⟨hg, hv⟩ := Finset.mem_sdiff.mp g.property
    have hnonzero : (denominator i).eval (g : K) ≠ 0 := by
      intro h
      apply hv
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hg, h⟩⟩
    apply mul_left_cancel₀ hnonzero
    calc
      _ = (numerator i).eval (g : K) := hcramer (g : K) hg i
      _ = _ := hidentity i (hnodes hi) (g : K) hg
  obtain ⟨p₀, p₁, h₀, h₁, hfit⟩ := RCN147.exists_basefield_affine_pencil_of_identity_nodes
    (RingHom.id K) testNodes x u₀ u₁ w (by omega) x.injective.injOn
    (fun g : ↥retained => (g : K)) (fun g => selected g)
    (fun g => hdegree (g : K) (Finset.mem_sdiff.mp g.property).1)
    (fun g i hi => by simpa only [RingHom.id_apply] using hretainedValues g i hi)
  have hretainedCard : retained.card ≤ e + 1 := by
    apply (Finset.card_le_card (t := RCN050.pencilSeeds seeds selected p₀ p₁) ?_).trans
      (hpencil p₀ p₁ h₀ h₁)
    intro g hg
    apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_sdiff.mp hg).1, ?_⟩
    simpa only [Polynomial.map_id] using hfit ⟨g, hg⟩
  have hsum : retained.card + excluded.card = seeds.card := by
    rw [show retained.card = seeds.card - excluded.card from Finset.card_sdiff_of_subset hexcluded]
    exact Nat.sub_add_cancel (Finset.card_le_card hexcluded)
  omega

theorem normalized_chart_bound
    (x : I ↪ K) (u₀ u₁ : I → K) (selected : K → Polynomial K)
    (denominator numerator : I → Polynomial K)
    (seeds : Finset K) (nodes identities : Finset I)
    (w a e agreementBudget denominatorBudget : ℕ)
    (hwa : w < a) (han : a ≤ nodes.card) (hsubset : identities ⊆ nodes)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hagreement : ∀ g ∈ seeds,
      a ≤ (nodes.filter (fun i => (selected g).eval (x i) = u₀ i + g * u₁ i)).card)
    (hidentity : ∀ i ∈ identities, ∀ g ∈ seeds,
      (numerator i).eval g = (denominator i).eval g * (u₀ i + g * u₁ i))
    (hcramer : ∀ g ∈ seeds, ∀ i,
      (denominator i).eval g * (selected g).eval (x i) = (numerator i).eval g)
    (hcut : ∀ i ∈ nodes \ identities,
      (seeds.filter (fun g => (numerator i).eval g =
        (denominator i).eval g * (u₀ i + g * u₁ i))).card ≤ agreementBudget)
    (hzero : ∀ i ∈ identities,
      (seeds.filter (fun g => (denominator i).eval g = 0)).card ≤ denominatorBudget)
    (hpencil : ∀ p₀ p₁ : Polynomial K, p₀.natDegree ≤ w → p₁.natDegree ≤ w →
      (RCN050.pencilSeeds seeds selected p₀ p₁).card ≤ e + 1) :
    seeds.card ≤ max ((nodes.card - w) * agreementBudget / (a - w))
      ((w + 1) * denominatorBudget + (e + 1)) := by
  by_cases hsmall : identities.card ≤ w
  · apply le_trans _ (le_max_left _ _)
    apply (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hwa)).mpr
    apply RCN173.sharp_incidence_bound
      (fun g i => (selected g).eval (x i) = u₀ i + g * u₁ i)
      seeds nodes identities a w agreementBudget hsubset hsmall hwa han hagreement
    intro i hi
    refine (Finset.card_le_card (t := seeds.filter (fun g => (numerator i).eval g =
      (denominator i).eval g * (u₀ i + g * u₁ i))) ?_).trans (hcut i hi)
    intro g hg
    obtain ⟨hseed, hfit⟩ := Finset.mem_filter.mp hg
    apply Finset.mem_filter.mpr
    refine ⟨hseed, ?_⟩
    rw [← hcramer g hseed i, hfit]
  · apply le_trans _ (le_max_right _ _)
    exact identity_nodes_bound x u₀ u₁ selected denominator numerator seeds identities
      w e denominatorBudget (Nat.lt_of_not_ge hsmall) hdegree hidentity hcramer hzero hpencil

theorem encoded_chart_bound
    (x : I ↪ K) (u₀ u₁ : I → K) (selected : K → Polynomial K)
    (denominator numerator : Polynomial (Polynomial K)) (hden : denominator ≠ 0)
    (seeds : Finset K) (nodes : Finset I)
    (w a e denominatorDegree numeratorDegree : ℕ)
    (hwa : w < a) (han : a ≤ nodes.card)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hagreement : ∀ g ∈ seeds,
      a ≤ (nodes.filter (fun i => (selected g).eval (x i) = u₀ i + g * u₁ i)).card)
    (hdenDegree : ∀ j, (denominator.coeff j).natDegree ≤ denominatorDegree)
    (hnumDegree : ∀ j, (numerator.coeff j).natDegree ≤ numeratorDegree)
    (hcramer : ∀ g ∈ seeds, denominator.map (Polynomial.evalRingHom g) * selected g =
      numerator.map (Polynomial.evalRingHom g))
    (hpencil : ∀ p₀ p₁ : Polynomial K, p₀.natDegree ≤ w → p₁.natDegree ≤ w →
      (RCN050.pencilSeeds seeds selected p₀ p₁).card ≤ e + 1) :
    seeds.card ≤ max
      ((nodes.card - w) * max numeratorDegree (denominatorDegree + 1) / (a - w))
      ((w + 1) * denominatorDegree + (e + 1)) := by
  obtain ⟨D, N, hD, hDdegree, hNdegree, hnode⟩ := Koala6831ChartNormalization.exists_node_tests
    denominator numerator hden denominatorDegree numeratorDegree hdenDegree hnumDegree
  let test (i : I) := N (x i) - D (x i) * (Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (u₁ i))
  let identities := nodes.filter (fun i => test i = 0)
  have htestDegree (i : I) : (test i).natDegree ≤ max numeratorDegree (denominatorDegree + 1) := by
    unfold test
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le_max (hNdegree _) ?_)
    refine (Polynomial.natDegree_mul_le).trans (Nat.add_le_add (hDdegree _) ?_)
    refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
    exact (Polynomial.natDegree_mul_C_le _ _).trans (by simp)
  apply normalized_chart_bound x u₀ u₁ selected (fun i => D (x i)) (fun i => N (x i))
    seeds nodes identities w a e (max numeratorDegree (denominatorDegree + 1))
    denominatorDegree hwa han (Finset.filter_subset _ _) hdegree hagreement
  · intro i hi g _
    have htest : test i = 0 := (Finset.mem_filter.mp hi).2
    have h := congrArg (Polynomial.eval g) htest
    simpa only [test, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_zero, sub_eq_zero] using h
  · intro g hg i
    exact hnode (x i) g (selected g) (hcramer g hg)
  · intro i hi
    have hnonzero : test i ≠ 0 := by
      intro hz
      obtain ⟨hIn, hOut⟩ := Finset.mem_sdiff.mp hi
      exact hOut (Finset.mem_filter.mpr ⟨hIn, hz⟩)
    apply le_trans _ (htestDegree i)
    apply Polynomial.card_le_degree_of_subset_roots
    intro g hg
    have heq := (Finset.mem_filter.mp hg).2
    exact (Polynomial.mem_roots hnonzero).mpr (by
      simpa only [test, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_C, Polynomial.IsRoot, sub_eq_zero] using heq)
  · intro i _
    apply le_trans _ (hDdegree (x i))
    apply Polynomial.card_le_degree_of_subset_roots
    intro g hg
    exact (Polynomial.mem_roots (hD (x i))).mpr (Finset.mem_filter.mp hg).2
  · exact hpencil

omit [DecidableEq K] in
private theorem coefficient_degree_mul (f g : Polynomial (Polynomial K)) (b c : ℕ)
    (hf : ∀ j, (f.coeff j).natDegree ≤ b) (hg : ∀ j, (g.coeff j).natDegree ≤ c) :
    ∀ j, ((f * g).coeff j).natDegree ≤ b + c := by
  intro j
  rw [Polynomial.coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro ij _
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hf ij.1) (hg ij.2))

omit [DecidableEq K] in
private theorem coefficient_degree_sub (f g : Polynomial (Polynomial K)) (b : ℕ)
    (hf : ∀ j, (f.coeff j).natDegree ≤ b) (hg : ∀ j, (g.coeff j).natDegree ≤ b) :
    ∀ j, ((f - g).coeff j).natDegree ≤ b := by
  intro j
  rw [Polynomial.coeff_sub]
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le (hf j) (hg j))

structure EncodedRow (K : Type) [Field K] (d p : ℕ) where
  beta : Polynomial (Polynomial K)
  first : Polynomial (Polynomial K)
  second : Polynomial (Polynomial K)
  betaCap : ∀ j, (beta.coeff j).natDegree ≤ (d + 1) + p * (d + 1)
  firstCap : ∀ j, (first.coeff j).natDegree ≤ d + p * (d + 1)
  secondCap : ∀ j, (second.coeff j).natDegree ≤ (d + 1) + p * d

def EncodedRow.satisfied {d p : ℕ} (row : EncodedRow K d p)
    (seed : K) (firstValue secondValue : Polynomial K) : Prop :=
  row.beta.map (Polynomial.evalRingHom seed) +
    row.first.map (Polynomial.evalRingHom seed) * firstValue +
    row.second.map (Polynomial.evalRingHom seed) * secondValue = 0

theorem two_encoded_rows_card_le {d p : ℕ} (hp : 0 < p)
    (x : I ↪ K) (u₀ u₁ : I → K) (selected secondValue : K → Polynomial K)
    (row₀ row₁ : EncodedRow K d p)
    (hnonzero : row₀.first * row₁.second - row₀.second * row₁.first ≠ 0)
    (seeds : Finset K) (nodes : Finset I) (w a e : ℕ)
    (hwa : w < a) (han : a ≤ nodes.card)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hagreement : ∀ g ∈ seeds,
      a ≤ (nodes.filter (fun i => (selected g).eval (x i) = u₀ i + g * u₁ i)).card)
    (h₀ : ∀ g ∈ seeds, row₀.satisfied g (selected g) (secondValue g))
    (h₁ : ∀ g ∈ seeds, row₁.satisfied g (selected g) (secondValue g))
    (hpencil : ∀ p₀ p₁ : Polynomial K, p₀.natDegree ≤ w → p₁.natDegree ≤ w →
      (RCN050.pencilSeeds seeds selected p₀ p₁).card ≤ e + 1) :
    seeds.card ≤ max ((nodes.card - w) * ((2*d + 2) * (p + 1)) / (a - w))
      ((w + 1) * ((2*d + 1) * (p + 1)) + (e + 1)) := by
  let denominator := row₀.first * row₁.second - row₀.second * row₁.first
  let numerator := row₀.second * row₁.beta - row₀.beta * row₁.second
  let denCap := (2*d + 1) * (p + 1)
  let numCap := (2*d + 2) * (p + 1)
  have hD : ∀ j, (denominator.coeff j).natDegree ≤ denCap := by
    apply coefficient_degree_sub
    · intro j
      have h := coefficient_degree_mul row₀.first row₁.second _ _ row₀.firstCap row₁.secondCap j
      exact h.trans_eq (by dsimp [denCap]; ring)
    · intro j
      have h := coefficient_degree_mul row₀.second row₁.first _ _ row₀.secondCap row₁.firstCap j
      exact h.trans_eq (by dsimp [denCap]; ring)
  have hN : ∀ j, (numerator.coeff j).natDegree ≤ numCap := by
    apply coefficient_degree_sub
    · intro j
      have h := coefficient_degree_mul row₀.second row₁.beta _ _ row₀.secondCap row₁.betaCap j
      have hcompare : (d + 1) + p * d + ((d + 1) + p * (d + 1)) + p = numCap := by
        dsimp [numCap]
        ring
      exact h.trans (by omega)
    · intro j
      have h := coefficient_degree_mul row₀.beta row₁.second _ _ row₀.betaCap row₁.secondCap j
      have hcompare : (d + 1) + p * (d + 1) + ((d + 1) + p * d) + p = numCap := by
        dsimp [numCap]
        ring
      exact h.trans (by omega)
  have hEq : ∀ g ∈ seeds, denominator.map (Polynomial.evalRingHom g) * selected g =
      numerator.map (Polynomial.evalRingHom g) := by
    intro g hg
    simp only [denominator, numerator, Polynomial.map_sub, Polynomial.map_mul]
    exact first_coordinate_cramer _ _ _ _ _ _ _ _ (h₀ g hg) (h₁ g hg)
  have hmax : max numCap (denCap + 1) = numCap := by
    apply max_eq_left
    have hstep : denCap + (p + 1) = numCap := by dsimp [denCap, numCap]; ring
    omega
  simpa only [hmax, denCap, numCap] using
    encoded_chart_bound x u₀ u₁ selected denominator numerator hnonzero seeds nodes
      w a e denCap numCap hwa han hdegree hagreement hD hN hEq hpencil

end

end ProximityPrize.SubmissionLower.Koala6831CramerIncidence
