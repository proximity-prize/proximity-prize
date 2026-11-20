import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Polynomial.Roots
import ProximityPrize.SubmissionLower.Koala6844Protocol





namespace ProximityPrize.SubmissionLower.Koala6844SeedEncoding

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K] {b c : ℕ}

abbrev SeedIndex (b c : ℕ) := Fin b × Fin c

def exponent (p : ℕ) (index : SeedIndex b c) : ℕ :=
  index.1.val + p * index.2.val

theorem exponent_injective {p : ℕ} (hp : 0 < p) (hb : b ≤ p) :
    Function.Injective (exponent (b := b) (c := c) p) := by
  intro i j hij
  have hi := Nat.lt_of_lt_of_le i.1.isLt hb
  have hj := Nat.lt_of_lt_of_le j.1.isLt hb
  have hfirst : i.1.val = j.1.val := by
    simpa only [exponent, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
      using congrArg (fun n : ℕ => n % p) hij
  have hmul : p * i.2.val = p * j.2.val := by
    apply Nat.add_left_cancel (n := j.1.val)
    simpa only [exponent, hfirst] using hij
  exact Prod.ext (Fin.ext hfirst) (Fin.ext (Nat.eq_of_mul_eq_mul_left hp hmul))

noncomputable def encode (p : ℕ) (a : SeedIndex b c → K) : K[X] :=
  ∑ index, monomial (exponent p index) (a index)


theorem coeff_encode {p : ℕ} (hp : 0 < p) (hb : b ≤ p)
    (a : SeedIndex b c → K) (index : SeedIndex b c) :
    (encode p a).coeff (exponent p index) = a index := by
  rw [encode, Polynomial.finsetSum_coeff]
  calc
    (∑ k, (monomial (exponent p k) (a k)).coeff (exponent p index)) =
        (monomial (exponent p index) (a index)).coeff (exponent p index) := by
      apply Finset.sum_eq_single index
      · intro k _ hk
        have hne : exponent p k ≠ exponent p index :=
          fun heq => hk (exponent_injective hp hb heq)
        simp [Polynomial.coeff_monomial, hne]
      · intro hnot
        exact (hnot (Finset.mem_univ index)).elim
    _ = a index := by simp

theorem encode_injective {p : ℕ} (hp : 0 < p) (hb : b ≤ p) :
    Function.Injective (encode (K := K) (b := b) (c := c) p) := by
  intro a a' heq
  funext index
  have hcoeff := congrArg (fun q : K[X] => q.coeff (exponent p index)) heq
  simpa only [coeff_encode hp hb] using hcoeff

@[simp] theorem encode_zero (p : ℕ) : encode (K := K) (b := b) (c := c) p 0 = 0 := by
  simp [encode]

theorem encode_nonzero {p : ℕ} (hp : 0 < p) (hb : b ≤ p)
    {a : SeedIndex b c → K} (ha : a ≠ 0) : encode p a ≠ 0 := by
  intro hz
  have heq : encode p a = encode p (0 : SeedIndex b c → K) := by
    simpa only [encode_zero] using hz
  exact ha (encode_injective hp hb heq)


theorem natDegree_encode_le (p : ℕ) (a : SeedIndex b c → K) :
    (encode p a).natDegree ≤ (b - 1) + p * (c - 1) := by
  unfold encode
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro index _
  apply (Polynomial.natDegree_monomial_le (a index) (m := exponent p index)).trans
  have hfirst : index.1.val ≤ b - 1 := Nat.le_sub_one_of_lt index.1.isLt
  have hsecond : index.2.val ≤ c - 1 := Nat.le_sub_one_of_lt index.2.isLt
  exact Nat.add_le_add hfirst (Nat.mul_le_mul_left p hsecond)


end ProximityPrize.SubmissionLower.Koala6844SeedEncoding


namespace ProximityPrize.SubmissionLower.Koala6844BivariateSeeds

open Polynomial Koala6844SeedEncoding
open scoped Classical BigOperators

variable {K : Type*} [Field K] {b c : ℕ}

abbrev SeedPolynomial (K : Type*) [Field K] := MvPolynomial (Fin 2) K

def coordinates {R : Type*} (z₀ z₁ : R) (i : Fin 2) : R :=
  if i = 0 then z₀ else z₁

private noncomputable def seedExponent (i : SeedIndex b c) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i.1.val + Finsupp.single 1 i.2.val

@[simp] private theorem seedExponent_zero (i : SeedIndex b c) :
    seedExponent i 0 = i.1.val := by
  simp [seedExponent]

@[simp] private theorem seedExponent_one (i : SeedIndex b c) :
    seedExponent i 1 = i.2.val := by
  simp [seedExponent]

private theorem seedExponent_injective :
    Function.Injective (seedExponent : SeedIndex b c → Fin 2 →₀ ℕ) := by
  intro i j h
  exact Prod.ext (Fin.ext (by simpa using congrArg (fun d : Fin 2 →₀ ℕ => d 0) h))
    (Fin.ext (by simpa using congrArg (fun d : Fin 2 →₀ ℕ => d 1) h))

noncomputable def coefficients (P : SeedPolynomial K) (i : SeedIndex b c) : K :=
  P.coeff (seedExponent i)

private noncomputable def reconstruct (a : SeedIndex b c → K) : SeedPolynomial K :=
  ∑ i, MvPolynomial.monomial (seedExponent i) (a i)

private theorem coeff_reconstruct (a : SeedIndex b c → K) (i : SeedIndex b c) :
    (reconstruct a).coeff (seedExponent i) = a i := by
  rw [reconstruct, MvPolynomial.coeff_sum]
  refine (Finset.sum_eq_single i ?_ ?_).trans ?_
  · intro j _ hji
    have hne : seedExponent j ≠ seedExponent i := fun h => hji (seedExponent_injective h)
    simp [MvPolynomial.coeff_monomial, hne]
  · simp
  · simp

private theorem reconstruct_coefficients (P : SeedPolynomial K)
    (h₀ : P.degreeOf 0 < b) (h₁ : P.degreeOf 1 < c) :
    reconstruct (coefficients (b := b) (c := c) P) = P := by
  apply MvPolynomial.ext
  intro d
  by_cases h : ∃ i : SeedIndex b c, seedExponent i = d
  · obtain ⟨i, rfl⟩ := h
    exact coeff_reconstruct (coefficients P) i
  · have hz : P.coeff d = 0 := by
      by_contra hne
      have hd := MvPolynomial.mem_support_iff.mpr hne
      let i : SeedIndex b c :=
        (⟨d 0, (MvPolynomial.monomial_le_degreeOf 0 hd).trans_lt h₀⟩,
         ⟨d 1, (MvPolynomial.monomial_le_degreeOf 1 hd).trans_lt h₁⟩)
      apply h
      refine ⟨i, Finsupp.ext ?_⟩
      rw [Fin.forall_fin_two]
      simp [i]
    rw [hz, reconstruct, MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro i _
    have hne : seedExponent i ≠ d := fun heq => h ⟨i, heq⟩
    simp [MvPolynomial.coeff_monomial, hne]

theorem coefficients_nonzero {P : SeedPolynomial K} (hP : P ≠ 0)
    (h₀ : P.degreeOf 0 < b) (h₁ : P.degreeOf 1 < c) :
    coefficients (b := b) (c := c) P ≠ 0 := by
  intro hz
  apply hP
  calc
    P = reconstruct (coefficients (b := b) (c := c) P) :=
      (reconstruct_coefficients P h₀ h₁).symm
    _ = 0 := by simp [hz, reconstruct]

noncomputable def frobeniusHom (p : ℕ) : SeedPolynomial K →+* K[X] :=
  MvPolynomial.eval₂Hom Polynomial.C (coordinates Polynomial.X (Polynomial.X ^ p))

theorem eval_frobeniusHom (p : ℕ) (P : SeedPolynomial K) (g : K) :
    (frobeniusHom p P).eval g = MvPolynomial.eval (coordinates g (g ^ p)) P := by
  change ((Polynomial.evalRingHom g).comp (frobeniusHom p)) P = _
  unfold frobeniusHom MvPolynomial.eval
  rw [MvPolynomial.comp_eval₂Hom]
  have hC : (Polynomial.evalRingHom g).comp (Polynomial.C : K →+* K[X]) = RingHom.id K := by
    apply RingHom.ext
    intro a
    simp
  have hpoint : (fun i => Polynomial.evalRingHom g
      (coordinates Polynomial.X (Polynomial.X ^ p) i)) = coordinates g (g ^ p) := by
    funext i
    by_cases hi : i = 0 <;> simp [coordinates, hi, map_pow]
  rw [hC, hpoint]

theorem frobeniusHom_eq_encode (p : ℕ) (P : SeedPolynomial K)
    (h₀ : P.degreeOf 0 < b) (h₁ : P.degreeOf 1 < c) :
    frobeniusHom p P = encode p (coefficients (b := b) (c := c) P) := by
  calc
    frobeniusHom p P = frobeniusHom p (reconstruct (coefficients (b := b) (c := c) P)) :=
      congrArg (frobeniusHom p) (reconstruct_coefficients P h₀ h₁).symm
    _ = encode p (coefficients (b := b) (c := c) P) := by
      rw [reconstruct, encode, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [frobeniusHom, MvPolynomial.eval₂Hom_monomial,
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two,
        ← Polynomial.C_mul_X_pow_eq_monomial]
      simp [coordinates, exponent, pow_add, pow_mul]


theorem frobeniusHom_nonzero {p : ℕ} (hp : 0 < p) (hb : b ≤ p)
    {P : SeedPolynomial K} (hP : P ≠ 0) (h₀ : P.degreeOf 0 < b) (h₁ : P.degreeOf 1 < c) :
    frobeniusHom p P ≠ 0 := by
  rw [frobeniusHom_eq_encode p P h₀ h₁]
  exact encode_nonzero hp hb (coefficients_nonzero hP h₀ h₁)

theorem natDegree_frobeniusHom_le (p : ℕ) (P : SeedPolynomial K)
    (h₀ : P.degreeOf 0 < b) (h₁ : P.degreeOf 1 < c) :
    (frobeniusHom p P).natDegree ≤ (b - 1) + p * (c - 1) := by
  rw [frobeniusHom_eq_encode p P h₀ h₁]
  exact natDegree_encode_le p _

theorem card_le_of_vanishing {p : ℕ} (hp : 0 < p) (hb : b ≤ p)
    {P : SeedPolynomial K} (hP : P ≠ 0) (h₀ : P.degreeOf 0 < b) (h₁ : P.degreeOf 1 < c)
    (seeds : Finset K) (hzero : ∀ g ∈ seeds, MvPolynomial.eval (coordinates g (g ^ p)) P = 0) :
    seeds.card ≤ (b - 1) + p * (c - 1) := by
  have hcard : seeds.card ≤ (frobeniusHom p P).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro g hg
    exact (Polynomial.mem_roots (frobeniusHom_nonzero hp hb hP h₀ h₁)).mpr
      ((eval_frobeniusHom p P g).trans (hzero g hg))
  exact hcard.trans (natDegree_frobeniusHom_le p P h₀ h₁)

end ProximityPrize.SubmissionLower.Koala6844BivariateSeeds


namespace ProximityPrize.SubmissionLower.Koala6844ChartNormalization

open Polynomial
open scoped BigOperators

noncomputable section

set_option autoImplicit false

variable {K : Type*} [Field K]

private theorem coeff_mul_of_lower_vanish {f g : Polynomial K} {n : ℕ}
    (hlower : ∀ k < n, f.coeff k = 0) : (f * g).coeff n = f.coeff n * g.coeff 0 := by
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_single (n, 0)
  · intro ij hij hne
    have hsum : ij.1 + ij.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hlt : ij.1 < n := by
      by_contra hn
      exact hne (Prod.ext (by omega) (by omega))
    rw [hlower _ hlt, zero_mul]
  · simp

private theorem map_taylor_eval (f : Polynomial (Polynomial K)) (x z : K) :
    (taylor (C x) f).map (evalRingHom z) = taylor x (f.map (evalRingHom z)) := by
  simp only [taylor_apply, map_comp, Polynomial.map_add, Polynomial.map_X,
    Polynomial.map_C, coe_evalRingHom, eval_C]

private theorem taylor_coeff_natDegree_le (f : Polynomial (Polynomial K)) (x : K)
    (k bound : ℕ) (hbound : ∀ j, (f.coeff j).natDegree ≤ bound) :
    ((taylor (C x) f).coeff k).natDegree ≤ bound := by
  rw [taylor_coeff, eval_eq_sum]
  unfold Polynomial.sum
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  change (((hasseDeriv k f).coeff j) * (C x)^j).natDegree ≤ bound
  rw [hasseDeriv_coeff]
  have hchoose : ((j + k).choose k : Polynomial K) = C (((j + k).choose k : ℕ) : K) := by
    simp
  have hpower : (C x)^j = C (x^j) := (map_pow Polynomial.C x j).symm
  rw [hchoose, hpower]
  apply (Polynomial.natDegree_mul_C_le _ _).trans
  exact (Polynomial.natDegree_C_mul_le _ _).trans (hbound _)

theorem exists_node_tests (denominator numerator : Polynomial (Polynomial K))
    (hnonzero : denominator ≠ 0) (denominatorDegree numeratorDegree : ℕ)
    (hdenDegree : ∀ j, (denominator.coeff j).natDegree ≤ denominatorDegree)
    (hnumDegree : ∀ j, (numerator.coeff j).natDegree ≤ numeratorDegree) :
    ∃ denominatorAt numeratorAt : K → Polynomial K,
      (∀ x, denominatorAt x ≠ 0) ∧
      (∀ x, (denominatorAt x).natDegree ≤ denominatorDegree) ∧
      (∀ x, (numeratorAt x).natDegree ≤ numeratorDegree) ∧
      ∀ (x seed : K) (selected : Polynomial K),
        denominator.map (evalRingHom seed) * selected = numerator.map (evalRingHom seed) →
        (denominatorAt x).eval seed * selected.eval x = (numeratorAt x).eval seed := by
  classical
  have hexists (x : K) : ∃ k, (taylor (C x) denominator).coeff k ≠ 0 := by
    have ht : taylor (C x) denominator ≠ 0 :=
      fun h => hnonzero ((taylor_eq_zero (C x) denominator).mp h)
    obtain ⟨k, hk⟩ := Polynomial.support_nonempty.mpr ht
    exact ⟨k, Polynomial.mem_support_iff.mp hk⟩
  let order (x : K) := Nat.find (hexists x)
  refine ⟨fun x => (taylor (C x) denominator).coeff (order x),
    fun x => (taylor (C x) numerator).coeff (order x),
    fun x => Nat.find_spec (hexists x),
    fun x => taylor_coeff_natDegree_le denominator x (order x) _ hdenDegree,
    fun x => taylor_coeff_natDegree_le numerator x (order x) _ hnumDegree, ?_⟩
  intro x seed selected hEq
  have hlower (k : ℕ) (hk : k < order x) :
      (taylor x (denominator.map (evalRingHom seed))).coeff k = 0 := by
    have hz : (taylor (C x) denominator).coeff k = 0 := by
      by_contra hne
      exact Nat.find_min (hexists x) hk hne
    rw [← map_taylor_eval, coeff_map, hz, map_zero]
  have heq := congrArg (fun f => (taylor x f).coeff (order x)) hEq
  rw [taylor_mul, coeff_mul_of_lower_vanish hlower, taylor_coeff_zero,
    ← map_taylor_eval denominator x seed, ← map_taylor_eval numerator x seed,
    coeff_map, coeff_map] at heq
  exact heq

end

end ProximityPrize.SubmissionLower.Koala6844ChartNormalization


namespace ProximityPrize.SubmissionLower.Koala6844CramerIncidence

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
  obtain ⟨D, N, hD, hDdegree, hNdegree, hnode⟩ := Koala6844ChartNormalization.exists_node_tests
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

end ProximityPrize.SubmissionLower.Koala6844CramerIncidence



namespace ProximityPrize.SubmissionLower.Koala6844Comparison

open Polynomial
open scoped BigOperators

noncomputable section

variable {K I : Type*} [CommRing K]

abbrev SeedIndex (b c : ℕ) := Fin b × Fin c

abbrev CoefficientIndex (h b c : ℕ) := Fin h × SeedIndex b c

abbrev RowIndex (A a d : ℕ) :=
  CoefficientIndex A (d + 2) (d + 2) ⊕
    (CoefficientIndex a (d + 1) (d + 2) ⊕ CoefficientIndex a (d + 2) (d + 1))

abbrev TargetIndex (I : Type*) (d : ℕ) := I × SeedIndex (d + 2) (d + 2)

private def emit {b c : ℕ} (j : SeedIndex b c) (v : K) (t : SeedIndex b c) : K :=
  if t = j then v else 0

private def betaConstraint {A d : ℕ} (x : K)
    (j : CoefficientIndex A (d + 2) (d + 2)) (t : SeedIndex (d + 2) (d + 2)) : K :=
  emit j.2 (x ^ j.1.val) t

private def firstConstraint {a d : ℕ} (x u v : K)
    (j : CoefficientIndex a (d + 1) (d + 2)) (t : SeedIndex (d + 2) (d + 2)) : K :=
  emit (j.2.1.castSucc, j.2.2) (x ^ j.1.val * u) t +
    emit (j.2.1.succ, j.2.2) (x ^ j.1.val * v) t

private def secondConstraint {a d : ℕ} (x u v : K)
    (j : CoefficientIndex a (d + 2) (d + 1)) (t : SeedIndex (d + 2) (d + 2)) : K :=
  emit (j.2.1, j.2.2.castSucc) (x ^ j.1.val * u) t +
    emit (j.2.1, j.2.2.succ) (x ^ j.1.val * v) t

def constraintMap (A a d : ℕ) (x : I → K) (u v : Fin 2 → I → K) :
    (RowIndex A a d → K) →ₗ[K] (TargetIndex I d → K) where
  toFun θ point :=
    (∑ j : CoefficientIndex A (d + 2) (d + 2),
      θ (.inl j) * betaConstraint (x point.1) j point.2) +
    (∑ j : CoefficientIndex a (d + 1) (d + 2),
      θ (.inr (.inl j)) * firstConstraint (x point.1) (u 0 point.1) (v 0 point.1) j point.2) +
    (∑ j : CoefficientIndex a (d + 2) (d + 1),
      θ (.inr (.inr j)) * secondConstraint (x point.1) (u 1 point.1) (v 1 point.1) j point.2)
  map_add' θ η := by
    funext point
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    abel
  map_smul' scalar θ := by
    funext point
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum, mul_add]

abbrev ComparisonSpace (A a d : ℕ) (x : I → K) (u v : Fin 2 → I → K) :=
  (constraintMap A a d x u v).ker

theorem comparisonSpace_finrank_lower_bound {F : Type*} [Field F] [Fintype I]
    (A a d e : ℕ) (x : I → F) (u v : Fin 2 → I → F)
    (hcard : Fintype.card I = A + e) :
    (d + 2) * (2 * (d + 1) * a - e * (d + 2)) ≤
      Module.finrank F (ComparisonSpace A a d x u v) := by
  let f := constraintMap A a d x u v
  have hnull := f.finrank_range_add_finrank_ker
  have hdom : Module.finrank F (RowIndex A a d → F) =
      A * (d + 2) * (d + 2) + (d + 2) * (2 * (d + 1) * a) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [RowIndex, CoefficientIndex, SeedIndex, Fintype.card_sum,
      Fintype.card_prod, Fintype.card_fin]
    ring
  have htarget : Module.finrank F (TargetIndex I d → F) =
      A * (d + 2) * (d + 2) + (d + 2) * (e * (d + 2)) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [TargetIndex, SeedIndex, Fintype.card_prod, Fintype.card_fin, hcard]
    ring
  have hrange := f.range.finrank_le
  rw [hdom] at hnull
  rw [htarget] at hrange
  change _ ≤ Module.finrank F f.ker
  rw [Nat.mul_sub]
  omega

theorem exists_nonzero_comparison_row {F : Type*} [Field F] [Fintype I]
    (A a d e : ℕ) (x : I → F) (u v : Fin 2 → I → F)
    (hcard : Fintype.card I = A + e)
    (hgate : 0 < (d + 2) * (2 * (d + 1) * a - e * (d + 2))) :
    ∃ θ : ComparisonSpace A a d x u v, θ.1 ≠ 0 := by
  have hdim := hgate.trans_le (comparisonSpace_finrank_lower_bound A a d e x u v hcard)
  obtain ⟨θ, hθ⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hdim
  exact ⟨θ, fun h => hθ (Subtype.ext h)⟩

private def seedMonomial {b c : ℕ} (z : K × K) (j : SeedIndex b c) : K :=
  z.1 ^ j.1.val * z.2 ^ j.2.val

private theorem sum_weighted_emit {b c : ℕ} (z : K × K)
    (j : SeedIndex b c) (value coefficient : K) :
    (∑ t : SeedIndex b c, coefficient * emit j value t * seedMonomial z t) =
      coefficient * value * seedMonomial z j := by
  simp [emit, mul_ite, ite_mul]

private theorem sum_weighted_columns
    {C : Type*} [Fintype C] {b c : ℕ} (z : K × K)
    (f w : C → K) (s : C → SeedIndex b c) :
    (∑ t : SeedIndex b c, (∑ j, f j * emit (s j) (w j) t) * seedMonomial z t) =
      ∑ j, f j * w j * seedMonomial z (s j) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact sum_weighted_emit z (s j) (w j) (f j)

def specializePiece {h b c : ℕ}
    (coefficients : CoefficientIndex h b c → K) (z : K × K) : Polynomial K :=
  ∑ j : CoefficientIndex h b c,
    monomial j.1.val (coefficients j * seedMonomial z j.2)

private theorem specializePiece_eval {h b c : ℕ}
    (coefficients : CoefficientIndex h b c → K) (z : K × K) (x : K) :
    (specializePiece coefficients z).eval x =
      ∑ j : CoefficientIndex h b c, coefficients j * x ^ j.1.val * seedMonomial z j.2 := by
  change (Polynomial.evalRingHom x) (specializePiece coefficients z) = _
  unfold specializePiece
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (monomial _ _).eval x = _
  rw [eval_monomial]
  ring

private theorem specializePiece_natDegree_le {h b c : ℕ}
    (coefficients : CoefficientIndex h b c → K) (z : K × K) :
    (specializePiece coefficients z).natDegree ≤ h - 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  refine (Polynomial.natDegree_monomial_le
    (coefficients j * seedMonomial z j.2)).trans ?_
  have hj := j.1.isLt
  omega

structure SpecializedRow (K : Type*) [CommRing K] where
  beta : Polynomial K
  first : Polynomial K
  second : Polynomial K

def specialize {A a d : ℕ} (θ : RowIndex A a d → K) (z : K × K) :
    SpecializedRow K where
  beta := specializePiece (fun j => θ (.inl j)) z
  first := specializePiece (fun j => θ (.inr (.inl j))) z
  second := specializePiece (fun j => θ (.inr (.inr j))) z

theorem specialize_degrees {A a d : ℕ} (θ : RowIndex A a d → K) (z : K × K) :
    let q := specialize θ z
    q.beta.natDegree ≤ A - 1 ∧ q.first.natDegree ≤ a - 1 ∧ q.second.natDegree ≤ a - 1 :=
  ⟨specializePiece_natDegree_le _ _, specializePiece_natDegree_le _ _,
    specializePiece_natDegree_le _ _⟩

private theorem first_total {a d : ℕ} (z : K × K) (x u v : K)
    (f : CoefficientIndex a (d + 1) (d + 2) → K) :
    (∑ t : SeedIndex (d + 2) (d + 2),
      (∑ j, f j * firstConstraint x u v j t) * seedMonomial z t) =
      (specializePiece f z).eval x * (u + z.1 * v) := by
  conv_lhs =>
    simp only [firstConstraint, mul_add, Finset.sum_add_distrib, add_mul]
  rw [sum_weighted_columns, sum_weighted_columns, specializePiece_eval, Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [seedMonomial, Fin.val_castSucc, Fin.val_succ, pow_succ]
  ring

private theorem second_total {a d : ℕ} (z : K × K) (x u v : K)
    (f : CoefficientIndex a (d + 2) (d + 1) → K) :
    (∑ t : SeedIndex (d + 2) (d + 2),
      (∑ j, f j * secondConstraint x u v j t) * seedMonomial z t) =
      (specializePiece f z).eval x * (u + z.2 * v) := by
  conv_lhs =>
    simp only [secondConstraint, mul_add, Finset.sum_add_distrib, add_mul]
  rw [sum_weighted_columns, sum_weighted_columns, specializePiece_eval, Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [seedMonomial, Fin.val_castSucc, Fin.val_succ, pow_succ]
  ring

theorem specialize_eval_received_eq_zero {A a d : ℕ}
    (x : I → K) (u v : Fin 2 → I → K)
    (θ : ComparisonSpace A a d x u v) (z : K × K) (i : I) :
    let q := specialize θ.1 z
    q.beta.eval (x i) +
      q.first.eval (x i) * (u 0 i + z.1 * v 0 i) +
      q.second.eval (x i) * (u 1 i + z.2 * v 1 i) = 0 := by
  have hker : constraintMap A a d x u v θ.1 = 0 := LinearMap.mem_ker.mp θ.2
  have hzero :
      (∑ t : SeedIndex (d + 2) (d + 2),
        constraintMap A a d x u v θ.1 (i, t) * seedMonomial z t) = 0 := by
    simp [hker]
  change
      (∑ t : SeedIndex (d + 2) (d + 2),
        ((∑ j, θ.1 (.inl j) * betaConstraint (x i) j t) +
          (∑ j, θ.1 (.inr (.inl j)) * firstConstraint (x i) (u 0 i) (v 0 i) j t) +
          (∑ j, θ.1 (.inr (.inr j)) * secondConstraint (x i) (u 1 i) (v 1 i) j t)) *
            seedMonomial z t) = 0 at hzero
  simp only [add_mul, Finset.sum_add_distrib] at hzero
  rw [first_total, second_total] at hzero
  have hbeta :
      (∑ t : SeedIndex (d + 2) (d + 2),
        (∑ j, θ.1 (.inl j) * betaConstraint (x i) j t) * seedMonomial z t) =
          (specialize θ.1 z).beta.eval (x i) := by
    unfold betaConstraint
    rw [sum_weighted_columns]
    exact (specializePiece_eval _ _ _).symm
  rw [hbeta] at hzero
  exact hzero

private theorem constraintMap_baseChange {R : Type*} [CommRing R]
    (φ : K →+* R) {A a d : ℕ} (x : I → K) (u v : Fin 2 → I → K)
    (θ : RowIndex A a d → K) (t : TargetIndex I d) :
    constraintMap A a d (φ ∘ x) (fun j i => φ (u j i)) (fun j i => φ (v j i))
        (fun j => φ (θ j)) t =
      φ (constraintMap A a d x u v θ t) := by
  have mapEmit (i j : SeedIndex (d + 2) (d + 2)) (v : K) :
      φ (emit i v j) = emit i (φ v) j := by
    by_cases h : j = i <;> simp [emit, h]
  simp only [constraintMap, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
    betaConstraint, firstConstraint, secondConstraint, map_add, map_mul, map_sum, map_pow,
    mapEmit]

abbrev SeedRing (K : Type*) [CommRing K] := MvPolynomial (Fin 2) K

def symbolicRow {A a d : ℕ} (θ : RowIndex A a d → K) : SpecializedRow (SeedRing K) :=
  specialize (fun j => MvPolynomial.C (θ j)) (MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2))

private theorem symbolicPiece_map_seedEval {h b c : ℕ}
    (θ : CoefficientIndex h b c → K) (f : Fin 2 → K) :
    (specializePiece (fun j => MvPolynomial.C (θ j))
        (MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2))).map (MvPolynomial.eval f) =
      specializePiece θ (f 0, f 1) := by
  simp [specializePiece, seedMonomial, Polynomial.map_sum, Polynomial.map_monomial,
    MvPolynomial.eval_C, MvPolynomial.eval_X]

theorem symbolicRow_map_seedEval {A a d : ℕ} (θ : RowIndex A a d → K) (f : Fin 2 → K) :
    let q := symbolicRow θ
    let p := specialize θ (f 0, f 1)
    q.beta.map (MvPolynomial.eval f) = p.beta ∧ q.first.map (MvPolynomial.eval f) = p.first ∧
      q.second.map (MvPolynomial.eval f) = p.second :=
  ⟨symbolicPiece_map_seedEval _ f, symbolicPiece_map_seedEval _ f,
    symbolicPiece_map_seedEval _ f⟩

theorem symbolicRow_eval_received_eq_zero {A a d : ℕ}
    (x : I → K) (u v : Fin 2 → I → K) (θ : ComparisonSpace A a d x u v) (i : I) :
    let q := symbolicRow θ.1
    q.beta.eval (MvPolynomial.C (x i)) +
      q.first.eval (MvPolynomial.C (x i)) *
        (MvPolynomial.C (u 0 i) + MvPolynomial.X 0 * MvPolynomial.C (v 0 i)) +
      q.second.eval (MvPolynomial.C (x i)) *
        (MvPolynomial.C (u 1 i) + MvPolynomial.X 1 * MvPolynomial.C (v 1 i)) = 0 := by
  let C : K →+* SeedRing K := MvPolynomial.C
  have h : constraintMap A a d (C ∘ x) (fun j i => C (u j i)) (fun j i => C (v j i))
      (fun j => C (θ.1 j)) = 0 := by
    funext t
    rw [constraintMap_baseChange]
    simp [LinearMap.mem_ker.mp θ.2]
  let lifted : ComparisonSpace A a d (C ∘ x) (fun j i => C (u j i)) (fun j i => C (v j i)) :=
    ⟨fun j => C (θ.1 j), LinearMap.mem_ker.mpr h⟩
  exact specialize_eval_received_eq_zero (C ∘ x) _ _ lifted (MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)) i

private def seedExponent {b c : ℕ} (j : SeedIndex b c) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 j.1.val + Finsupp.single 1 j.2.val

private theorem seedExponent_injective {b c : ℕ} :
    Function.Injective (seedExponent : SeedIndex b c → Fin 2 →₀ ℕ) := by
  intro j k h
  have h₀ := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
  have h₁ := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
  have hOne : (1 : Fin 2) ≠ 0 := by decide
  have hZero : (0 : Fin 2) ≠ 1 := Ne.symm hOne
  apply Prod.ext
  · apply Fin.ext
    simpa [seedExponent, Finsupp.single_apply, hOne, hZero] using h₀
  · apply Fin.ext
    simpa [seedExponent, Finsupp.single_apply, hOne, hZero] using h₁

private theorem symbolicMonomial {b c : ℕ} (z : SeedIndex b c) (v : K) :
    MvPolynomial.C v * seedMonomial (MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)) z =
      MvPolynomial.monomial (seedExponent z) v := by
  simp [seedMonomial, seedExponent, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul_monomial, MvPolynomial.C_mul_monomial]

private theorem symbolicPiece_coeff {h b c : ℕ}
    (θ : CoefficientIndex h b c → K) (j : CoefficientIndex h b c) :
    ((specializePiece (fun k => MvPolynomial.C (θ k))
        (MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2))).coeff j.1.val).coeff
      (seedExponent j.2) = θ j := by
  classical
  rw [specializePiece, Polynomial.finsetSum_coeff, MvPolynomial.coeff_sum]
  refine (Finset.sum_eq_single j ?_ ?_).trans ?_
  · intro k _ hkj
    by_cases hx : k.1 = j.1
    · have hseed : seedExponent k.2 ≠ seedExponent j.2 := by
        intro he
        exact hkj (Prod.ext hx (seedExponent_injective he))
      simp [hx, symbolicMonomial, MvPolynomial.coeff_monomial, hseed]
    · have hval : k.1.val ≠ j.1.val := fun he => hx (Fin.ext he)
      simp [Polynomial.coeff_monomial, hval]
  · simp
  · simp [symbolicMonomial, MvPolynomial.coeff_monomial]

private theorem symbolicPiece_seed_degree_bounds {h b c : ℕ}
    (θ : CoefficientIndex h b c → K) (n : ℕ) :
    let P := (specializePiece (fun j => MvPolynomial.C (θ j))
      (MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2))).coeff n
    P.degreeOf 0 ≤ b - 1 ∧ P.degreeOf 1 ≤ c - 1 := by
  let P := (specializePiece (fun j => MvPolynomial.C (θ j))
    (MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2))).coeff n
  have hOne : (1 : Fin 2) ≠ 0 := by decide
  have hZero : (0 : Fin 2) ≠ 1 := Ne.symm hOne
  have supported {m : Fin 2 →₀ ℕ} (hm : m ∈ P.support) :
      ∃ j : CoefficientIndex h b c, seedExponent j.2 = m := by
    by_contra hNone
    apply (MvPolynomial.mem_support_iff.mp hm)
    unfold P specializePiece
    rw [Polynomial.finsetSum_coeff, MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro j _
    have hne : seedExponent j.2 ≠ m := fun he => hNone ⟨j, he⟩
    by_cases hn : j.1.val = n
    · simp [hn, symbolicMonomial, MvPolynomial.coeff_monomial, hne]
    · simp [Polynomial.coeff_monomial, hn]
  constructor
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    obtain ⟨j, rfl⟩ := supported hm
    have hj := j.2.1.isLt
    simp [seedExponent, hZero]
    omega
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    obtain ⟨j, rfl⟩ := supported hm
    have hj := j.2.2.isLt
    simp [seedExponent, hOne]
    omega

theorem symbolicRow_seed_degree_bounds {A a d : ℕ} (θ : RowIndex A a d → K) (n : ℕ) :
    let q := symbolicRow θ
    ((q.beta.coeff n).degreeOf 0 ≤ d + 1 ∧ (q.beta.coeff n).degreeOf 1 ≤ d + 1) ∧
      ((q.first.coeff n).degreeOf 0 ≤ d ∧ (q.first.coeff n).degreeOf 1 ≤ d + 1) ∧
      ((q.second.coeff n).degreeOf 0 ≤ d + 1 ∧ (q.second.coeff n).degreeOf 1 ≤ d) :=
  ⟨symbolicPiece_seed_degree_bounds _ n, symbolicPiece_seed_degree_bounds _ n,
    symbolicPiece_seed_degree_bounds _ n⟩

theorem symbolicRow_injective (A a d : ℕ) :
    Function.Injective (symbolicRow : (RowIndex A a d → K) → SpecializedRow (SeedRing K)) := by
  intro θ η heq
  funext j
  rcases j with j | j
  · have h := congrArg (fun q : SpecializedRow (SeedRing K) =>
        (q.beta.coeff j.1.val).coeff (seedExponent j.2)) heq
    simpa only [symbolicRow, specialize, symbolicPiece_coeff] using h
  · rcases j with j | j
    · have h := congrArg (fun q : SpecializedRow (SeedRing K) =>
          (q.first.coeff j.1.val).coeff (seedExponent j.2)) heq
      simpa only [symbolicRow, specialize, symbolicPiece_coeff] using h
    · have h := congrArg (fun q : SpecializedRow (SeedRing K) =>
          (q.second.coeff j.1.val).coeff (seedExponent j.2)) heq
      simpa only [symbolicRow, specialize, symbolicPiece_coeff] using h

theorem specialize_selected_eq_zero [IsDomain K] {A a d w : ℕ}
    (x : I ↪ K) (U : Fin 2 → I → K) (σ : K →+* K)
    (hfixed : ∀ i, σ (x i) = x i) (haPos : 0 < a) (ha : a + w = A)
    (θ : ComparisonSpace A a d x (fun j i => if j = 0 then U 0 i else σ (U 0 i))
      (fun j i => if j = 0 then U 1 i else σ (U 1 i)))
    (γ : K) (P : Polynomial K) (hP : P.natDegree ≤ w)
    (S : Finset I) (hS : A ≤ S.card)
    (hagree : ∀ i ∈ S, P.eval (x i) = U 0 i + γ * U 1 i) :
    let q := specialize θ.1 (γ, σ γ)
    q.beta + q.first * P + q.second * P.map σ = 0 := by
  classical
  let q := specialize θ.1 (γ, σ γ)
  let Q := q.beta + q.first * P + q.second * P.map σ
  change Q = 0
  have hdegrees : q.beta.natDegree ≤ A - 1 ∧
      q.first.natDegree ≤ a - 1 ∧ q.second.natDegree ≤ a - 1 :=
    specialize_degrees θ.1 (γ, σ γ)
  obtain ⟨hb, h0, h1⟩ := hdegrees
  have h0w : (q.first * P).natDegree ≤ A - 1 := calc
    _ ≤ q.first.natDegree + P.natDegree := Polynomial.natDegree_mul_le
    _ ≤ A - 1 := by omega
  have hmap : (P.map σ).natDegree ≤ w := Polynomial.natDegree_map_le.trans hP
  have h1w : (q.second * P.map σ).natDegree ≤ A - 1 := calc
    _ ≤ q.second.natDegree + (P.map σ).natDegree := Polynomial.natDegree_mul_le
    _ ≤ A - 1 := by omega
  have hQ : Q.natDegree ≤ A - 1 :=
    (Polynomial.natDegree_add_le _ _).trans
      (max_le ((Polynomial.natDegree_add_le _ _).trans (max_le hb h0w)) h1w)
  have hroots : ∀ i ∈ S, Q.eval (x i) = 0 := by
    intro i hi
    have hOne : (1 : Fin 2) ≠ 0 := by decide
    have h : q.beta.eval (x i) +
        q.first.eval (x i) * (U 0 i + γ * U 1 i) +
        q.second.eval (x i) * (σ (U 0 i) + σ γ * σ (U 1 i)) = 0 := by
      simpa [q, hOne] using
        specialize_eval_received_eq_zero x _ _ θ (γ, σ γ) i
    have hconjugate : (P.map σ).eval (x i) = σ (P.eval (x i)) := by
      calc
        (P.map σ).eval (x i) = (P.map σ).eval (σ (x i)) := by rw [hfixed i]
        _ = σ (P.eval (x i)) := by rw [Polynomial.eval_map_apply]
    simpa only [Q, Polynomial.eval_add, Polynomial.eval_mul, hconjugate,
      hagree i hi, map_add, map_mul] using h
  by_contra hne
  have hcount : (S.image x).card ≤ Q.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    exact (Polynomial.mem_roots hne).mpr (hroots i hi)
  rw [Finset.card_image_of_injective _ x.injective] at hcount
  omega

end

end ProximityPrize.SubmissionLower.Koala6844Comparison


namespace ProximityPrize.SubmissionLower.Koala6844RankTwo

open Koala6844Comparison Koala6844CramerIncidence Koala6844BivariateSeeds
open scoped Classical BigOperators

noncomputable section

set_option autoImplicit false

variable {K : Type} [Field K]

private def encodeRow {A a d D : ℕ} (θ : RowIndex A a d → K) (p : ℕ)
    (hle : d ≤ D) : EncodedRow K D p where
  beta := (symbolicRow θ).beta.map (frobeniusHom p)
  first := (symbolicRow θ).first.map (frobeniusHom p)
  second := (symbolicRow θ).second.map (frobeniusHom p)
  betaCap j := by
    rw [Polynomial.coeff_map]
    have h := (symbolicRow_seed_degree_bounds θ j).1
    exact (natDegree_frobeniusHom_le (b := d + 2) (c := d + 2) p _
      (Nat.lt_succ_of_le h.1) (Nat.lt_succ_of_le h.2)).trans
      (Nat.add_le_add (Nat.succ_le_succ hle) (Nat.mul_le_mul_left p (Nat.succ_le_succ hle)))
  firstCap j := by
    rw [Polynomial.coeff_map]
    have h := (symbolicRow_seed_degree_bounds θ j).2.1
    exact (natDegree_frobeniusHom_le (b := d + 1) (c := d + 2) p _
      (Nat.lt_succ_of_le h.1) (Nat.lt_succ_of_le h.2)).trans
      (Nat.add_le_add hle (Nat.mul_le_mul_left p (Nat.succ_le_succ hle)))
  secondCap j := by
    rw [Polynomial.coeff_map]
    have h := (symbolicRow_seed_degree_bounds θ j).2.2
    exact (natDegree_frobeniusHom_le (b := d + 2) (c := d + 1) p _
      (Nat.lt_succ_of_le h.1) (Nat.lt_succ_of_le h.2)).trans
      (Nat.add_le_add (Nat.succ_le_succ hle) (Nat.mul_le_mul_left p hle))

private theorem map_frobenius_eval (F : Polynomial (SeedPolynomial K)) (p : ℕ) (g : K) :
    (F.map (frobeniusHom p)).map (Polynomial.evalRingHom g) =
      F.map (MvPolynomial.eval (coordinates g (g ^ p))) := by
  have hEval : (Polynomial.evalRingHom g).comp (frobeniusHom p) =
      MvPolynomial.eval (coordinates g (g ^ p)) := by
    apply RingHom.ext
    intro P
    exact eval_frobeniusHom p P g
  rw [Polynomial.map_map, hEval]

private theorem satisfied_of_specialize {A a d D : ℕ} (θ : RowIndex A a d → K)
    (p : ℕ) (hle : d ≤ D) (g : K) (P Q : Polynomial K)
    (h : let row := specialize θ (g, g ^ p)
      row.beta + row.first * P + row.second * Q = 0) : (encodeRow θ p hle).satisfied g P Q := by
  obtain ⟨hβ, h₀, h₁⟩ := symbolicRow_map_seedEval θ (coordinates g (g ^ p))
  dsimp only [EncodedRow.satisfied, encodeRow]
  rw [map_frobenius_eval, map_frobenius_eval, map_frobenius_eval, hβ, h₀, h₁]
  simpa [coordinates] using h

private theorem coefficient_bidegree_mul (F G : Polynomial (SeedPolynomial K))
    (i : Fin 2) (b c : ℕ) (hF : ∀ j, (F.coeff j).degreeOf i ≤ b)
    (hG : ∀ j, (G.coeff j).degreeOf i ≤ c) (j : ℕ) :
    ((F * G).coeff j).degreeOf i ≤ b + c := by
  rw [Polynomial.coeff_mul]
  refine (MvPolynomial.degreeOf_sum_le _ _ _).trans ?_
  apply Finset.sup_le
  intro index _
  exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (Nat.add_le_add (hF _) (hG _))

private theorem encoded_det_nonzero {A a d₀ d₁ D p : ℕ} (hp : 0 < p) (hwidth : 2*D + 2 ≤ p)
    (hle₀ : d₀ ≤ D) (hle₁ : d₁ ≤ D)
    (θ : RowIndex A a d₀ → K) (η : RowIndex A a d₁ → K)
    (hdet : (symbolicRow θ).first * (symbolicRow η).second -
      (symbolicRow θ).second * (symbolicRow η).first ≠ 0) :
    (encodeRow θ p hle₀).first * (encodeRow η p hle₁).second -
      (encodeRow θ p hle₀).second * (encodeRow η p hle₁).first ≠ 0 := by
  let δ := (symbolicRow θ).first * (symbolicRow η).second -
      (symbolicRow θ).second * (symbolicRow η).first
  have hDegree₀ (j : ℕ) : (δ.coeff j).degreeOf 0 ≤ 2*D + 1 := by
    dsimp only [δ]
    rw [Polynomial.coeff_sub]
    refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
    · refine (coefficient_bidegree_mul _ _ 0 d₀ (d₁+1)
        (fun l => (symbolicRow_seed_degree_bounds θ l).2.1.1)
        (fun l => (symbolicRow_seed_degree_bounds η l).2.2.1) j).trans (by omega)
    · refine (coefficient_bidegree_mul _ _ 0 (d₀+1) d₁
        (fun l => (symbolicRow_seed_degree_bounds θ l).2.2.1)
        (fun l => (symbolicRow_seed_degree_bounds η l).2.1.1) j).trans (by omega)
  have hDegree₁ (j : ℕ) : (δ.coeff j).degreeOf 1 ≤ 2*D + 1 := by
    dsimp only [δ]
    rw [Polynomial.coeff_sub]
    refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
    · refine (coefficient_bidegree_mul _ _ 1 (d₀+1) d₁
        (fun l => (symbolicRow_seed_degree_bounds θ l).2.1.2)
        (fun l => (symbolicRow_seed_degree_bounds η l).2.2.2) j).trans (by omega)
    · refine (coefficient_bidegree_mul _ _ 1 d₀ (d₁+1)
        (fun l => (symbolicRow_seed_degree_bounds θ l).2.2.2)
        (fun l => (symbolicRow_seed_degree_bounds η l).2.1.2) j).trans (by omega)
  have hmap : δ.map (frobeniusHom p) ≠ 0 := by
    intro hz
    apply hdet
    change δ = 0
    apply Polynomial.ext
    intro j
    simp only [Polynomial.coeff_zero]
    by_contra hne
    have hDegree₀' : (δ.coeff j).degreeOf 0 < 2*D + 2 := by
      have := hDegree₀ j
      omega
    have hDegree₁' : (δ.coeff j).degreeOf 1 < 2*D + 2 := by
      have := hDegree₁ j
      omega
    apply frobeniusHom_nonzero hp hwidth hne hDegree₀' hDegree₁'
    have hcoeff := congrArg (fun f : Polynomial (Polynomial K) => f.coeff j) hz
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using hcoeff
  simpa only [δ, Polynomial.map_sub, Polynomial.map_mul, encodeRow] using hmap

theorem independent_mixed_rows_card_le {I : Type} [Fintype I]
    {A a d₀ d₁ D p w e : ℕ} (hp : 0 < p) (hwidth : 2*D + 2 ≤ p)
    (hle₀ : d₀ ≤ D) (hle₁ : d₁ ≤ D)
    (x : I ↪ K) (U : Fin 2 → I → K) (σ : K →+* K)
    (hfixed : ∀ i, σ (x i) = x i) (hσ : ∀ g, σ g = g ^ p)
    (haPos : 0 < a) (ha : a + w = A) (han : A ≤ Fintype.card I)
    (θ : ComparisonSpace A a d₀ x (fun j i => if j = 0 then U 0 i else σ (U 0 i))
      (fun j i => if j = 0 then U 1 i else σ (U 1 i)))
    (η : ComparisonSpace A a d₁ x (fun j i => if j = 0 then U 0 i else σ (U 0 i))
      (fun j i => if j = 0 then U 1 i else σ (U 1 i)))
    (hdet : (symbolicRow θ.1).first * (symbolicRow η.1).second -
      (symbolicRow θ.1).second * (symbolicRow η.1).first ≠ 0)
    (seeds : Finset K) (selected : K → Polynomial K)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hagreement : ∀ g ∈ seeds,
      A ≤ (Finset.univ.filter (fun i => (selected g).eval (x i) = U 0 i + g * U 1 i)).card)
    (hpencil : ∀ p₀ p₁ : Polynomial K, p₀.natDegree ≤ w → p₁.natDegree ≤ w →
      (RCN050.pencilSeeds seeds selected p₀ p₁).card ≤ e + 1) :
    seeds.card ≤ max ((Fintype.card I - w) * ((2*D + 2) * (p + 1)) / (A - w))
      ((w + 1) * ((2*D + 1) * (p + 1)) + (e + 1)) := by
  rw [← Finset.card_univ (α := I)]
  apply two_encoded_rows_card_le hp x (U 0) (U 1) selected (fun g => (selected g).map σ)
    (encodeRow θ.1 p hle₀) (encodeRow η.1 p hle₁)
    (encoded_det_nonzero hp hwidth hle₀ hle₁ θ.1 η.1 hdet)
    seeds Finset.univ w A e (by omega) (by simpa using han) hdegree hagreement
  · intro g hg
    apply satisfied_of_specialize
    rw [← hσ g]
    exact specialize_selected_eq_zero x U σ hfixed haPos ha θ g (selected g) (hdegree g hg)
      _ (hagreement g hg) (fun _ hi => (Finset.mem_filter.mp hi).2)
  · intro g hg
    apply satisfied_of_specialize
    rw [← hσ g]
    exact specialize_selected_eq_zero x U σ hfixed haPos ha η g (selected g) (hdegree g hg)
      _ (hagreement g hg) (fun _ hi => (Finset.mem_filter.mp hi).2)
  · exact hpencil


end

end ProximityPrize.SubmissionLower.Koala6844RankTwo


namespace ProximityPrize.SubmissionLower.Koala6844BenchmarkField

open ProximityPrize.Benchmark

abbrev prime : ℕ := 2130706433

theorem characteristic : CharP IRSProfile.Field prime :=
  RCN128.challenge_field_characteristic6600

theorem field_card : Fintype.card IRSProfile.Field = prime ^ 6 :=
  RCN284.field_cardinality

private def baseFrobenius : IRSProfile.Field →ₐ[_root_.KoalaBear.Field] IRSProfile.Field :=
  FiniteField.frobeniusAlgHom _root_.KoalaBear.Field IRSProfile.Field

private noncomputable def baseFrobeniusEquiv : IRSProfile.Field ≃+* IRSProfile.Field :=
  RingEquiv.ofBijective baseFrobenius.toRingHom
    ⟨baseFrobenius.injective, Finite.surjective_of_injective baseFrobenius.injective⟩

private theorem exists_frobenius : ∃ σ : IRSProfile.Field ≃+* IRSProfile.Field,
    (∀ value : IRSProfile.Field, σ value = value ^ prime) ∧
    (∀ i : IRSProfile.Index, σ (IRSProfile.domain i) = IRSProfile.domain i) := by
  refine ⟨baseFrobeniusEquiv, ?_, ?_⟩
  · intro value
    have hcard : Fintype.card _root_.KoalaBear.Field = prime := ZMod.card prime
    rw [← hcard]
    change baseFrobenius value = _
    exact congrFun (FiniteField.coe_frobeniusAlgHom _root_.KoalaBear.Field IRSProfile.Field) value
  · intro i
    change baseFrobenius (algebraMap _root_.KoalaBear.Field IRSProfile.Field
      (IRSProfile.baseNttDomain.node i)) = _
    exact baseFrobenius.commutes (IRSProfile.baseNttDomain.node i)

noncomputable def frobenius : IRSProfile.Field ≃+* IRSProfile.Field :=
  Classical.choose exists_frobenius

theorem frobenius_apply (value : IRSProfile.Field) : frobenius value = value ^ prime :=
  (Classical.choose_spec exists_frobenius).1 value

@[simp] theorem domain_fixed (i : IRSProfile.Index) :
    frobenius (IRSProfile.domain i) = IRSProfile.domain i :=
  (Classical.choose_spec exists_frobenius).2 i

end ProximityPrize.SubmissionLower.Koala6844BenchmarkField


namespace ProximityPrize.SubmissionLower.Koala6844BenchmarkCases

open ProximityPrize.Benchmark
open Koala6844BenchmarkField Koala6844Comparison Koala6844Protocol
open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _

abbrev ReceivedWords := Fin 2 → IRSProfile.Index → IRSProfile.Field

abbrev conjugateWord (received : ReceivedWords) (which : Fin 2) : ReceivedWords :=
  fun j i => if j = 0 then received which i else frobenius (received which i)

abbrev ComparisonRows (received : ReceivedWords) (d : ℕ) :=
  ComparisonSpace 180961 49890 d IRSProfile.domain
    (conjugateWord received 0) (conjugateWord received 1)

def rowDeterminant {K : Type*} [Field K] {A a d₀ d₁ : ℕ}
    (first : RowIndex A a d₀ → K) (second : RowIndex A a d₁ → K) :=
  (symbolicRow first).first * (symbolicRow second).second -
    (symbolicRow first).second * (symbolicRow second).first

abbrev coefficientDeterminant {received : ReceivedWords} {d₀ d₁ : ℕ}
    (first : ComparisonRows received d₀) (second : ComparisonRows received d₁) :=
  rowDeterminant first.1 second.1

def agreementSet (received : ReceivedWords)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field) (g : IRSProfile.Field) :
    Finset IRSProfile.Index :=
  @Finset.filter _ (fun i => (selected g).eval (IRSProfile.domain i) =
    received 0 i + g * received 1 i) (fun _ => Classical.propDecidable _) Finset.univ

structure Selection (received : ReceivedWords) (seeds : Finset IRSProfile.Field)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field) : Prop where
  degree_le : ∀ g ∈ seeds, (selected g).natDegree ≤ 131071
  agreement : ∀ g ∈ seeds, 180961 ≤ (agreementSet received selected g).card
  pencil : ∀ p₀ p₁ : Polynomial IRSProfile.Field,
    p₀.natDegree ≤ 131071 → p₁.natDegree ≤ 131071 →
    (RCN050.pencilSeeds seeds selected p₀ p₁).card ≤ 81184

theorem exists_comparison_rows (received : ReceivedWords) :
    (∃ θ : ComparisonRows received 4, θ.1 ≠ 0) ∧
    (∃ θ : ComparisonRows received 200, θ.1 ≠ 0) := by
  constructor
  · exact exists_nonzero_comparison_row 180961 49890 4 81183 IRSProfile.domain
      (conjugateWord received 0) (conjugateWord received 1) IRSProfile.card_index (by decide)
  · exact exists_nonzero_comparison_row 180961 49890 200 81183 IRSProfile.domain
      (conjugateWord received 0) (conjugateWord received 1) IRSProfile.card_index (by decide)

theorem independent_rows_le_seed_budget
    {received : ReceivedWords} {d₀ d₁ : ℕ} (hle₀ : d₀ ≤ 200) (hle₁ : d₁ ≤ 200)
    (first : ComparisonRows received d₀) (second : ComparisonRows received d₁)
    (hdet : coefficientDeterminant (received := received) (d₀ := d₀) (d₁ := d₁) first second ≠ 0)
    (seeds : Finset IRSProfile.Field) (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (support : Selection received seeds selected) : seeds.card ≤ mcaBudget := by
  unfold coefficientDeterminant rowDeterminant at hdet
  have h := Koala6844RankTwo.independent_mixed_rows_card_le
    (K := IRSProfile.Field) (I := IRSProfile.Index)
    (A := 180961) (a := 49890) (d₀ := d₀) (d₁ := d₁)
    (p := prime) (D := 200) (w := 131071) (e := 81183)
    (by decide) (by decide) hle₀ hle₁ IRSProfile.domain received frobenius.toRingHom
    domain_fixed frobenius_apply (by decide) (by decide)
    (by rw [IRSProfile.card_index]; decide)
    first second hdet seeds selected support.degree_le
    (by exact support.agreement) (by exact support.pencil)
  rw [IRSProfile.card_index] at h
  exact h.trans (by decide +kernel)

def RankOneSeedBound : Prop :=
  ∀ (received : ReceivedWords) (seeds : Finset IRSProfile.Field)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field),
    Selection received seeds selected →
    ∀ first : ComparisonRows received 4, first.1 ≠ 0 →
      (∀ second : ComparisonRows received 200,
        coefficientDeterminant (received := received) (d₀ := 4) (d₁ := 200) first second = 0) →
      seeds.card ≤ mcaBudget

theorem seed_bound_of_rank_one (hRankOne : RankOneSeedBound) : ScalarSeedBound := by
  unfold ScalarSeedBound RCN050.SelectedNoLargePencilBound
  intro received seeds A selected hdegree hnear hvalue hpencil
  have hthreshold : Fintype.card IRSProfile.Index - errors = 180961 := by
    rw [IRSProfile.card_index]
    decide
  have hagree : ∀ g ∈ seeds, 180961 ≤ (agreementSet received selected g).card := by
    intro g hg
    have hn := hnear g hg
    rw [hthreshold] at hn
    refine hn.trans (Finset.card_le_card ?_)
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvalue g hg i hi⟩
  have hselection : Selection received seeds selected := ⟨hdegree, hagree, hpencil⟩
  obtain ⟨first, hfirst⟩ := (exists_comparison_rows received).1
  by_cases hdet : ∃ second : ComparisonRows received 200,
      coefficientDeterminant (received := received) (d₀ := 4) (d₁ := 200) first second ≠ 0
  · obtain ⟨second, hsecond⟩ := hdet
    exact independent_rows_le_seed_budget (received := received) (d₀ := 4) (d₁ := 200) (by decide) (by decide)
      first second hsecond seeds selected hselection
  · exact hRankOne received seeds selected hselection first hfirst
      (fun second => not_ne_iff.mp (fun h => hdet ⟨second, h⟩))

end

end ProximityPrize.SubmissionLower.Koala6844BenchmarkCases

