import ProximityPrize.SubmissionLower.GH
import ProximityPrize.SubmissionLower.EM
import ProximityPrize.SubmissionLower.W

/-!
# Derivative chain for singular seeds

For an irreducible factor `F` with positive `R`-degree, a seed at which both `F`
and `∂_R F` specialise to zero is either a regular seed of some iterated
`R`-derivative `∂_R^j F` (`1 ≤ j`), or a zero of the `R`-free polynomial
`∂_R^m F` obtained when the `R`-degree is exhausted.  Regular seeds of a
derivative are counted by the coprime pair `(∂_R^j F, F)`; the `R`-free tail is
counted by the singular-seed bound at slope cap `1`, whose characteristic gate is
`2 * ((D - 1) / w) * L < p`.
-/

namespace ProximityPrize.SubmissionLower.LocatorDerivativeChain

open scoped Classical BigOperators
open RCN174 RCN319 RCN081 RCN082 RCN167 RCN286 RCN052 RCN260 RCN318 RCN267 RCN313 RCN135 RCN138 RCN136 RCN238 RCN293 RCN231 RCN243

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

/-- Iterated `R`-derivative. -/
def dR (j : ℕ) (F : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  (MvPolynomial.pderiv (2 : Fin 4))^[j] F

@[simp] theorem dR_zero (F : MvPolynomial (Fin 4) K) : dR 0 F = F := rfl

theorem dR_succ (j : ℕ) (F : MvPolynomial (Fin 4) K) :
    dR (j + 1) F = MvPolynomial.pderiv (2 : Fin 4) (dR j F) := by
  unfold dR
  exact Function.iterate_succ_apply' _ _ _

/-- The `R`-derivative stays inside every coefficient box. -/
theorem pderiv_R_mem_box (Q : MvPolynomial (Fin 4) K) (D w L s : ℕ)
    (hbox : Q ∈ globalCoefficientBox K D w L s) :
    MvPolynomial.pderiv (2 : Fin 4) Q ∈ globalCoefficientBox K D w L s := by
  intro d hd
  have hmem := support_before_pderiv (2 : Fin 4) Q d hd
  obtain ⟨ht, hs, hc⟩ := hbox hmem
  have h0 : ((d + Finsupp.single (2 : Fin 4) 1 : Fin 4 →₀ ℕ) : Fin 4 → ℕ) 0 = d 0 := by
    simp [Finsupp.single_apply]
  have h1 : ((d + Finsupp.single (2 : Fin 4) 1 : Fin 4 →₀ ℕ) : Fin 4 → ℕ) 1 = d 1 := by
    simp [Finsupp.single_apply]
  have h2 : ((d + Finsupp.single (2 : Fin 4) 1 : Fin 4 →₀ ℕ) : Fin 4 → ℕ) 2 = d 2 + 1 := by
    simp [Finsupp.single_apply]
  have h3 : ((d + Finsupp.single (2 : Fin 4) 1 : Fin 4 →₀ ℕ) : Fin 4 → ℕ) 3 = d 3 := by
    simp [Finsupp.single_apply]
  simp only [h0, h1, h2, h3] at ht hs hc
  have hw1 : (w - 1) * d 2 ≤ (w - 1) * (d 2 + 1) := Nat.mul_le_mul_left _ (by omega)
  exact ⟨by omega, by omega, by omega⟩

theorem dR_mem_box (j : ℕ) (Q : MvPolynomial (Fin 4) K) (D w L s : ℕ)
    (hbox : Q ∈ globalCoefficientBox K D w L s) :
    dR j Q ∈ globalCoefficientBox K D w L s := by
  induction j with
  | zero => simpa using hbox
  | succ k ih =>
      rw [dR_succ]
      exact pderiv_R_mem_box _ D w L s ih

theorem dR_R_degree_le (j : ℕ) (F : MvPolynomial (Fin 4) K) :
    (dR j F).degreeOf 2 ≤ F.degreeOf 2 - j := by
  induction j with
  | zero => simp
  | succ k ih =>
      rw [dR_succ]
      have h := pderiv_same_degree_bound (2 : Fin 4) (dR k F) (F.degreeOf 2 - k) ih
      omega

/-- A box with slope cap `s` and no `R`-dependence lies in the slope-`1` box. -/
theorem mem_box_slope_one (Q : MvPolynomial (Fin 4) K) (D w L s : ℕ)
    (hbox : Q ∈ globalCoefficientBox K D w L s) (hR : Q.degreeOf 2 = 0) :
    Q ∈ globalCoefficientBox K D w L 1 := by
  intro d hd
  obtain ⟨ht, _, hc⟩ := hbox hd
  have hd2 : d 2 ≤ Q.degreeOf 2 := MvPolynomial.monomial_le_degreeOf (2 : Fin 4) hd
  exact ⟨ht, by omega, hc⟩

/-- Exhaustion index of the `R`-degree along the derivative chain. -/
theorem exists_dR_R_degree_zero (F : MvPolynomial (Fin 4) K) :
    ∃ j, (dR j F).degreeOf 2 = 0 :=
  ⟨F.degreeOf 2, Nat.eq_zero_of_le_zero (by simpa using dR_R_degree_le (F.degreeOf 2) F)⟩

def chainLength (F : MvPolynomial (Fin 4) K) : ℕ :=
  Nat.find (exists_dR_R_degree_zero F)

theorem chainLength_spec (F : MvPolynomial (Fin 4) K) :
    (dR (chainLength F) F).degreeOf 2 = 0 :=
  Nat.find_spec (exists_dR_R_degree_zero F)

theorem chainLength_le (F : MvPolynomial (Fin 4) K) : chainLength F ≤ F.degreeOf 2 :=
  Nat.find_min' (exists_dR_R_degree_zero F)
    (Nat.eq_zero_of_le_zero (by simpa using dR_R_degree_le (F.degreeOf 2) F))

theorem dR_R_degree_pos_of_lt_chainLength (F : MvPolynomial (Fin 4) K) (j : ℕ)
    (hj : j < chainLength F) : 0 < (dR j F).degreeOf 2 :=
  Nat.pos_of_ne_zero (Nat.find_min (exists_dR_R_degree_zero F) hj)

theorem chainLength_pos (F : MvPolynomial (Fin 4) K) (hpos : 0 < F.degreeOf 2) :
    1 ≤ chainLength F := by
  by_contra h
  have h0 : chainLength F = 0 := by omega
  have := chainLength_spec F
  rw [h0] at this
  simp at this
  omega

theorem dR_ne_zero (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0) (p : ℕ) [CharP K p]
    (hsmall : F.degreeOf 2 < p) (j : ℕ) (hj : j ≤ chainLength F) : dR j F ≠ 0 := by
  induction j with
  | zero => simpa using hF
  | succ k ih =>
      rw [dR_succ]
      have hk : k < chainLength F := by omega
      have hpos := dR_R_degree_pos_of_lt_chainLength F k hk
      have hle : (dR k F).degreeOf 2 < p := by
        have := dR_R_degree_le k F
        omega
      exact R_derivative_nonzero (dR k F) p hpos hle

/-- Seeds along the chain: either some derivative is regular, or every
derivative up to the exhaustion index vanishes. -/
theorem chain_split (F : MvPolynomial (Fin 4) K) (P : Polynomial K) (γ : K)
    (h0 : specialization K P γ F = 0)
    (h1 : specialization K P γ (MvPolynomial.pderiv (2 : Fin 4) F) = 0)
    (m : ℕ) (hm : 1 ≤ m) :
    (∃ j, 1 ≤ j ∧ j < m ∧ RegularSolution (dR j F) P γ) ∨
      (∀ i ≤ m, specialization K P γ (dR i F) = 0) := by
  induction m with
  | zero => omega
  | succ k ih =>
      by_cases hk : k = 0
      · subst hk
        right
        intro i hi
        interval_cases i
        · simpa using h0
        · rw [dR_succ]; simpa using h1
      · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk
        rcases ih hk1 with ⟨j, hj1, hjk, hreg⟩ | hall
        · exact Or.inl ⟨j, hj1, by omega, hreg⟩
        · by_cases hnext : specialization K P γ (dR (k + 1) F) = 0
          · right
            intro i hi
            rcases Nat.lt_or_ge i (k + 1) with hlt | hge
            · exact hall i (by omega)
            · have : i = k + 1 := by omega
              subst this
              exact hnext
          · left
            refine ⟨k, hk1, by omega, hall k le_rfl, ?_⟩
            rw [← dR_succ]
            exact hnext

/-- A regular seed of `G` is a regular seed of one of its irreducible factors
of positive `R`-degree. -/
theorem exists_regular_positive_factor (G : MvPolynomial (Fin 4) K) (hG : G ≠ 0)
    (P : Polynomial K) (γ : K) (hreg : RegularSolution G P γ) :
    ∃ F' ∈ positiveRFactors G, RegularSolution F' P γ := by
  classical
  let ψ : MvPolynomial (Fin 4) K →+* Polynomial K := (specialization K P γ).toRingHom
  obtain ⟨F', hmem, hzero⟩ := exists_normalized_factor_of_map_zero ψ G hG hreg.1
  have hdiv : F' ∣ G := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmem
  have hregF' : ψ (MvPolynomial.pderiv (2 : Fin 4) F') ≠ 0 :=
    factor_derivative_regular_at_zero ψ G F' hdiv hzero hreg.2
  have hpos : 0 < F'.degreeOf 2 := by
    apply Nat.pos_of_ne_zero
    intro hzeroDeg
    apply hregF'
    rw [pderiv_zero_of_degree_zero (2 : Fin 4) F' hzeroDeg, map_zero]
  have hactive : F' ∈ activeFactors G := by
    unfold activeFactors
    exact Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hmem, by omega⟩
  refine ⟨F', ?_, hzero, hregF'⟩
  unfold positiveRFactors
  exact Finset.mem_filter.mpr ⟨hactive, hpos⟩

/-- Every seed of `Q` is a seed of an active irreducible factor of `Q`. -/
theorem exists_active_factor_of_solution (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (P : Polynomial K) (γ : K) (hsol : specialization K P γ Q = 0) :
    ∃ F ∈ activeFactors Q, specialization K P γ F = 0 := by
  classical
  let φ := polynomialEmbedding K
  let v : Fin 3 → GenericField K := fun i => initialPoint K P γ i.succ
  have heval (F : MvPolynomial (Fin 4) K) :
      MvPolynomial.eval v (surfaceMap φ F) = 0 ↔ specialization K P γ F = 0 := by
    simpa only [canonical_geometricSurfaceMap] using
      (actual_generic_initial_zero_iff K P γ F)
  obtain ⟨F, hF, hz⟩ := exists_active_factor_of_surface_zero φ
    (polynomialEmbedding_injective K) Q hQ v ((heval Q).mpr hsol)
  exact ⟨F, hF, (heval F).mp hz⟩

theorem irreducible_not_dvd_dR (F : MvPolynomial (Fin 4) K) (hF : Irreducible F)
    (p : ℕ) [CharP K p] (hpos : 0 < F.degreeOf 2) (hsmall : F.degreeOf 2 < p)
    (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ chainLength F) : ¬ F ∣ dR j F := by
  intro hdiv
  have hne : dR j F ≠ 0 := dR_ne_zero F hF.ne_zero p hsmall j hj
  have hle := degreeOf_le_of_dvd (2 : Fin 4) F (dR j F) hdiv hne
  have hdeg := dR_R_degree_le j F
  omega

theorem isRelPrime_dR (F : MvPolynomial (Fin 4) K) (hF : Irreducible F)
    (p : ℕ) [CharP K p] (hpos : 0 < F.degreeOf 2) (hsmall : F.degreeOf 2 < p)
    (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ chainLength F) : IsRelPrime (dR j F) F :=
  (hF.isRelPrime_iff_not_dvd.mpr (irreducible_not_dvd_dR F hF p hpos hsmall j hj1 hj)).symm

section Counting

variable {Iota : Type}
local instance : DecidableEq Iota := Classical.decEq Iota

/-- Seeds that are regular for `dR j F` and at which `F` vanishes. -/
def chainSeeds (F : MvPolynomial (Fin 4) K) (j : ℕ)
    (selected : K → Polynomial K) (Gamma : Finset K) : Finset K :=
  Gamma.filter fun γ => RegularSolution (dR j F) (selected γ) γ ∧
    specialization K (selected γ) γ F = 0

/-- Seeds of the `R`-free tail of the chain of `F`. -/
def tailSeeds (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) : Finset K :=
  Gamma.filter fun γ => specialization K (selected γ) γ (dR (chainLength F) F) = 0

/-- Product of the `R`-free active factors of `Q`. -/
def rfreeProduct (Q : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  ∏ F ∈ (activeFactors Q).filter (fun F => F.degreeOf 2 = 0), F

def rfreeSeeds (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) : Finset K :=
  Gamma.filter fun γ => specialization K (selected γ) γ (rfreeProduct Q) = 0

theorem chainSeeds_subset (F : MvPolynomial (Fin 4) K) (j : ℕ)
    (selected : K → Polynomial K) (Gamma : Finset K) :
    chainSeeds F j selected Gamma ⊆ Gamma := Finset.filter_subset _ _

theorem tailSeeds_subset (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) :
    tailSeeds F selected Gamma ⊆ Gamma := Finset.filter_subset _ _

theorem rfreeSeeds_subset (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) :
    rfreeSeeds Q selected Gamma ⊆ Gamma := Finset.filter_subset _ _

theorem rfreeProduct_dvd (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) :
    rfreeProduct Q ∣ Q := by
  classical
  unfold rfreeProduct
  exact (Finset.prod_dvd_prod_of_subset _ (activeFactors Q) id
    (Finset.filter_subset _ _)).trans (activeFactors_product_dvd Q hQ)

theorem rfreeProduct_ne_zero (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) :
    rfreeProduct Q ≠ 0 :=
  ne_zero_of_dvd_ne_zero hQ (rfreeProduct_dvd Q hQ)

theorem rfreeProduct_R_degree (Q : MvPolynomial (Fin 4) K) :
    (rfreeProduct Q).degreeOf 2 = 0 := by
  classical
  unfold rfreeProduct
  apply Nat.eq_zero_of_le_zero
  refine (MvPolynomial.degreeOf_prod_le _ _ _).trans ?_
  apply Nat.le_of_eq
  apply Finset.sum_eq_zero
  intro F hF
  exact (Finset.mem_filter.mp hF).2

/-- Every seed of `Q` lies in the regular pair seeds, the chain seeds, the tail
seeds or the `R`-free seeds. -/
theorem cover (Q T : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (p : ℕ) [CharP K p] (s : ℕ) (hsmall : s < p)
    (hR : ∀ F ∈ positiveRFactors Q, F.degreeOf 2 ≤ s)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hQsolution : ∀ γ ∈ Gamma, specialization K (selected γ) γ Q = 0)
    (hTsolution : ∀ γ ∈ Gamma, specialization K (selected γ) γ T = 0) :
    Gamma ⊆
      (Finset.univ.biUnion fun F : RegularIndex Q =>
          regularPairSeeds Q T selected Gamma F) ∪
        ((positiveRFactors Q).biUnion fun F =>
          (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma) ∪
        ((positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma) ∪
        rfreeSeeds Q selected Gamma := by
  classical
  intro γ hγ
  obtain ⟨F, hFactive, hFzero⟩ :=
    exists_active_factor_of_solution Q hQ (selected γ) γ (hQsolution γ hγ)
  by_cases hRfree : F.degreeOf 2 = 0
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr ⟨hγ, ?_⟩
    have hdiv : F ∣ rfreeProduct Q := by
      unfold rfreeProduct
      exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨hFactive, hRfree⟩)
    obtain ⟨c, hc⟩ := hdiv
    rw [hc, map_mul, hFzero, zero_mul]
  · have hpos : 0 < F.degreeOf 2 := Nat.pos_of_ne_zero hRfree
    have hFpos : F ∈ positiveRFactors Q := by
      unfold positiveRFactors
      exact Finset.mem_filter.mpr ⟨hFactive, hpos⟩
    by_cases hreg : specialization K (selected γ) γ (MvPolynomial.pderiv (2 : Fin 4) F) = 0
    · have hm := chainLength_pos F hpos
      rcases chain_split F (selected γ) γ hFzero hreg (chainLength F) hm with
        ⟨j, hj1, hjm, hjreg⟩ | hall
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr ⟨F, hFpos, ?_⟩
        apply Finset.mem_biUnion.mpr ⟨j, Finset.mem_Ico.mpr ⟨hj1, hjm⟩, ?_⟩
        exact Finset.mem_filter.mpr ⟨hγ, hjreg, hFzero⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr ⟨F, hFpos, ?_⟩
        exact Finset.mem_filter.mpr ⟨hγ, hall (chainLength F) le_rfl⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr ⟨⟨F, hFpos⟩, Finset.mem_univ _, ?_⟩
      exact Finset.mem_filter.mpr ⟨hγ, ⟨hFzero, hreg⟩, hTsolution γ hγ⟩

/-- The chain seeds at stage `j` are covered by the regular pair seeds of
`(dR j F, F)`. -/
theorem chainSeeds_subset_regularPairSeeds (F : MvPolynomial (Fin 4) K) (j : ℕ)
    (hne : dR j F ≠ 0) (selected : K → Polynomial K) (Gamma : Finset K) :
    chainSeeds F j selected Gamma ⊆
      Finset.univ.biUnion fun F' : RegularIndex (dR j F) =>
        regularPairSeeds (dR j F) F selected Gamma F' := by
  classical
  intro γ hγ
  obtain ⟨hγΓ, hreg, hFzero⟩ := Finset.mem_filter.mp hγ
  obtain ⟨F', hF'mem, hF'reg⟩ :=
    exists_regular_positive_factor (dR j F) hne (selected γ) γ hreg
  apply Finset.mem_biUnion.mpr ⟨⟨F', hF'mem⟩, Finset.mem_univ _, ?_⟩
  exact Finset.mem_filter.mpr ⟨hγΓ, hF'reg, hFzero⟩

theorem chainSeeds_card_le
    (Pc : UnequalParameters) (Q F : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hF : F ∈ positiveRFactors Q) (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ chainLength F)
    (D w L s p : ℕ) [CharP K p] (hsmall : s < p) (hw : 1 ≤ w)
    (hbox : Q ∈ globalCoefficientBox K D w L s)
    (hcgap : 0 < Pc.gap)
    (hcY : (D - 1) / w ≤ Pc.leftY) (hcR : s ≤ Pc.leftR) (hcZ : L ≤ Pc.leftZ)
    (hcY' : (D - 1) / w ≤ Pc.rightY) (hcR' : s ≤ Pc.rightR) (hcZ' : L ≤ Pc.rightZ)
    (hleftR : 1 ≤ Pc.leftR)
    (hleftYSmall : Pc.leftY < p) (hleftRSmall : Pc.leftR < p) (hleftZSmall : Pc.leftZ < p)
    (hmixedYSmall : Pc.mixedCost.y < p) (hmixedRSmall : Pc.mixedCost.r < p)
    (hmixedZSmall : Pc.mixedCost.z < p)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K) (hinj : Set.InjOn x nodes)
    (hnodes : nodes.card = Pc.n)
    (hPw : 1 ≤ Pc.w) (hchar : Pc.w < p) (hwa : Pc.w < Pc.a) (han : Pc.a ≤ Pc.n)
    (hdegree : ∀ γ ∈ Gamma, (selected γ).natDegree ≤ Pc.w)
    (hagreement : ∀ γ ∈ Gamma, Pc.a ≤ (nodes.filter (fun i =>
      (selected γ).eval (x i) = u0 i + γ * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma Pc.w Pc.errors) :
    (chainSeeds F j selected Gamma).card ≤ Pc.regularCountCap := by
  classical
  obtain ⟨hFirr, hFpos, hFbox⟩ := directFactor_data Q F hQ D w L s hbox hF
  have hFsmall : F.degreeOf 2 < p := by
    have := degreeOf_R_le_of_mem_box F D w L s hFbox
    omega
  have hne : dR j F ≠ 0 := dR_ne_zero F hFirr.ne_zero p hFsmall j hj
  have hrel : IsRelPrime (dR j F) F := isRelPrime_dR F hFirr p hFpos hFsmall j hj1 hj
  have hbox' : dR j F ∈ globalCoefficientBox K D w L s := dR_mem_box j F D w L s hFbox
  have hFcaps := degree_bounds_of_mem_box F D w L s (by omega) hFbox
  have hsub := chainSeeds_subset_regularPairSeeds F j hne selected Gamma
  have hcount := all_regularPairSeeds_bound Pc (dR j F) F hne hrel D w L s p hbox' hw
    hcY hcR hcZ (hFcaps.1.trans hcY') (hFcaps.2.1.trans hcR') (hFcaps.2.2.trans hcZ')
    hleftR hleftYSmall hleftRSmall hleftZSmall hmixedYSmall hmixedRSmall hmixedZSmall
    selected Gamma nodes x u0 u1 hinj hnodes hPw hchar hwa han hdegree hagreement hnoPencil
  have hsum := sum_regular_counts_bound Pc (dR j F) F selected Gamma
    (regularVector_budgets Pc (dR j F) hne D w L s (by omega) hbox' hcY hcR hcZ) hcount
  have hcap : (∑ F' : RegularIndex (dR j F),
      (regularPairSeeds (dR j F) F selected Gamma F').card) ≤ Pc.regularCountCap :=
    Pc.regular_count_le _ hcgap hsum
  calc (chainSeeds F j selected Gamma).card
      ≤ (Finset.univ.biUnion fun F' : RegularIndex (dR j F) =>
          regularPairSeeds (dR j F) F selected Gamma F').card := Finset.card_le_card hsub
    _ ≤ ∑ F' : RegularIndex (dR j F),
          (regularPairSeeds (dR j F) F selected Gamma F').card := Finset.card_biUnion_le
    _ ≤ Pc.regularCountCap := hcap

/-- Seeds of a nonzero `R`-free polynomial in the slope-`1` box are bounded by
the singular-seed count of the slope-`1` Tight parameters. -/
theorem rfree_seed_count_le
    (S : TightParameters) (J : MvPolynomial (Fin 4) K) (hJ : J ≠ 0)
    (p : ℕ) [CharP K p]
    (hbox : J ∈ globalCoefficientBox K S.D S.w S.L S.s) (hJR : J.degreeOf 2 = 0) (hSs : S.s = 1)
    (hp : 1 < p) (hw : 1 ≤ S.w) (hchar : S.w < p) (hDw : S.w < S.kappa * S.D)
    (hj : 1 ≤ S.algebraicCap) (hjYSmall : S.implicitYCap < p) (hjZSmall : S.algebraicCap < p)
    (hmixedSmall : 2 * S.implicitYCap * S.algebraicCap < p)
    (hwa : S.w < S.a) (han : S.a ≤ S.n)
    (selected : K → Polynomial K) (Delta : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K) (hinj : Set.InjOn x nodes)
    (hnodes : nodes.card = S.n)
    (hdegree : ∀ γ ∈ Delta, (selected γ).natDegree ≤ S.w)
    (hsol : ∀ γ ∈ Delta, specialization K (selected γ) γ J = 0)
    (hagreement : ∀ γ ∈ Delta, S.a ≤ (nodes.filter (fun i =>
      (selected γ).eval (x i) = u0 i + γ * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Delta S.w S.errors) :
    Delta.card ≤ S.countCap := by
  classical
  have hs1 : 1 ≤ S.s := by omega
  have hsp : S.s < p := by omega
  have hcover := card_le_regular_sum_add_singular J J hJ S.D S.w S.L S.s p
    hs1 hsp hw (by simpa [TightParameters.kappa] using hDw)
    (by simpa [TightParameters.algebraicCap, TightParameters.kappa] using hj)
    (by simpa [TightParameters.algebraicCap, TightParameters.kappa] using hjZSmall)
    hbox selected Delta hsol hsol
  have hregZero : (∑ F' : RegularIndex J, (regularPairSeeds J J selected Delta F').card) = 0 := by
    apply Finset.sum_eq_zero
    intro F' _
    exfalso
    obtain ⟨_, hdvd, hpos⟩ := positiveRFactors_spec J F'.1 F'.2
    have := degreeOf_le_of_dvd (2 : Fin 4) F'.1 J hdvd hJ
    omega
  have hsingularOld := RCN292.TightParameters.singularSeeds_count_le_countCap
    S J hJ hbox hs1 hsp hw hchar hDw hj hjYSmall hjZSmall hmixedSmall
    hwa han selected Delta nodes x u0 u1 hinj hnodes hdegree hagreement hnoPencil
  have hsingular : (RCN052.singularSeeds J selected Delta).card ≤ S.countCap := by
    change (RCN291.singularSeeds J selected Delta).card ≤ S.countCap
    exact hsingularOld
  omega

end Counting

section Assembly

variable {Iota : Type}
local instance : DecidableEq Iota := Classical.decEq Iota

theorem sum_chainLength_sub_one_le (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (D w L s : ℕ) (hw : 0 < w) (hs : 1 ≤ s)
    (hbox : Q ∈ globalCoefficientBox K D w L s) :
    (∑ F ∈ positiveRFactors Q, (chainLength F - 1)) ≤ s - 1 ∧
      (positiveRFactors Q).card ≤ s := by
  classical
  have hbudget := (directFactor_input_budgets Q hQ D w L s hw hbox).2.1
  have hpos : ∀ F ∈ positiveRFactors Q, 1 ≤ F.degreeOf 2 :=
    fun F hF => (positiveRFactors_spec Q F hF).2.2
  have hcard : (positiveRFactors Q).card ≤ ∑ F ∈ positiveRFactors Q, F.degreeOf 2 := by
    calc (positiveRFactors Q).card = ∑ _F ∈ positiveRFactors Q, (1 : ℕ) := by simp
      _ ≤ ∑ F ∈ positiveRFactors Q, F.degreeOf 2 := Finset.sum_le_sum hpos
  have hsub : (∑ F ∈ positiveRFactors Q, (chainLength F - 1)) + (positiveRFactors Q).card ≤
      ∑ F ∈ positiveRFactors Q, F.degreeOf 2 := by
    calc (∑ F ∈ positiveRFactors Q, (chainLength F - 1)) + (positiveRFactors Q).card
        = ∑ F ∈ positiveRFactors Q, ((chainLength F - 1) + 1) := by
          rw [Finset.sum_add_distrib]; simp
      _ ≤ ∑ F ∈ positiveRFactors Q, F.degreeOf 2 := by
          apply Finset.sum_le_sum
          intro F hF
          have h1 := hpos F hF
          have h2 := chainLength_le F
          omega
  refine ⟨?_, hcard.trans hbudget⟩
  by_cases hempty : (positiveRFactors Q).card = 0
  · rw [Finset.card_eq_zero] at hempty
    simp [hempty]
  · omega

theorem residual_chain_count_le
    (P Pc : UnequalParameters) (S : TightParameters)
    (Q T : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) (hrel : IsRelPrime Q T)
    (D w L s p : ℕ) [CharP K p]
    (hs : 1 ≤ s) (hsmall : s < p) (hw : 1 ≤ w) (hp : 1 < p)
    (hbox : Q ∈ globalCoefficientBox K D w L s)
    (hgap : 0 < P.gap) (hY : (D - 1) / w ≤ P.leftY) (hR : s ≤ P.leftR) (hZ : L ≤ P.leftZ)
    (hTY : T.degreeOf 1 ≤ P.rightY) (hTR : T.degreeOf 2 ≤ P.rightR) (hTZ : T.degreeOf 3 ≤ P.rightZ)
    (hleftR : 1 ≤ P.leftR) (hleftYSmall : P.leftY < p) (hleftRSmall : P.leftR < p)
    (hleftZSmall : P.leftZ < p) (hmixedYSmall : P.mixedCost.y < p)
    (hmixedRSmall : P.mixedCost.r < p) (hmixedZSmall : P.mixedCost.z < p)
    (hcgap : 0 < Pc.gap) (hcY : (D - 1) / w ≤ Pc.leftY) (hcR : s ≤ Pc.leftR) (hcZ : L ≤ Pc.leftZ)
    (hcY' : (D - 1) / w ≤ Pc.rightY) (hcR' : s ≤ Pc.rightR) (hcZ' : L ≤ Pc.rightZ)
    (hcleftR : 1 ≤ Pc.leftR) (hcleftYSmall : Pc.leftY < p) (hcleftRSmall : Pc.leftR < p)
    (hcleftZSmall : Pc.leftZ < p) (hcmixedYSmall : Pc.mixedCost.y < p)
    (hcmixedRSmall : Pc.mixedCost.r < p) (hcmixedZSmall : Pc.mixedCost.z < p)
    (hSD : S.D = D) (hSw : S.w = w) (hSL : S.L = L) (hSs : S.s = 1)
    (hSchar : S.w < p) (hSDw : S.w < S.kappa * S.D) (hSj : 1 ≤ S.algebraicCap)
    (hSY : S.implicitYCap < p) (hSZ : S.algebraicCap < p)
    (hSmixed : 2 * S.implicitYCap * S.algebraicCap < p) (hSwa : S.w < S.a) (hSan : S.a ≤ S.n)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K) (hinj : Set.InjOn x nodes)
    (hnodesP : nodes.card = P.n) (hnodesC : nodes.card = Pc.n) (hnodesS : nodes.card = S.n)
    (hPw : 1 ≤ P.w) (hPchar : P.w < p) (hPwa : P.w < P.a) (hPan : P.a ≤ P.n)
    (hCw : 1 ≤ Pc.w) (hCchar : Pc.w < p) (hCwa : Pc.w < Pc.a) (hCan : Pc.a ≤ Pc.n)
    (hdegreeP : ∀ γ ∈ Gamma, (selected γ).natDegree ≤ P.w)
    (hdegreeC : ∀ γ ∈ Gamma, (selected γ).natDegree ≤ Pc.w)
    (hdegreeS : ∀ γ ∈ Gamma, (selected γ).natDegree ≤ S.w)
    (hagreementP : ∀ γ ∈ Gamma, P.a ≤ (nodes.filter (fun i =>
      (selected γ).eval (x i) = u0 i + γ * u1 i)).card)
    (hagreementC : ∀ γ ∈ Gamma, Pc.a ≤ (nodes.filter (fun i =>
      (selected γ).eval (x i) = u0 i + γ * u1 i)).card)
    (hagreementS : ∀ γ ∈ Gamma, S.a ≤ (nodes.filter (fun i =>
      (selected γ).eval (x i) = u0 i + γ * u1 i)).card)
    (hnoPencilP : NoLargeSelectedPencil selected Gamma P.w P.errors)
    (hnoPencilC : NoLargeSelectedPencil selected Gamma Pc.w Pc.errors)
    (hnoPencilS : NoLargeSelectedPencil selected Gamma S.w S.errors)
    (hQsolution : ∀ γ ∈ Gamma, specialization K (selected γ) γ Q = 0)
    (hTsolution : ∀ γ ∈ Gamma, specialization K (selected γ) γ T = 0) :
    Gamma.card ≤ P.regularCountCap + (s - 1) * Pc.regularCountCap + (s + 1) * S.countCap := by
  classical
  -- regular pairs
  have hregular := all_regularPairSeeds_bound P Q T hQ hrel D w L s p hbox hw hY hR hZ
    hTY hTR hTZ hleftR hleftYSmall hleftRSmall hleftZSmall hmixedYSmall hmixedRSmall
    hmixedZSmall selected Gamma nodes x u0 u1 hinj hnodesP hPw hPchar hPwa hPan
    hdegreeP hagreementP hnoPencilP
  have hregSum := sum_regular_counts_bound P Q T selected Gamma
    (regularVector_budgets P Q hQ D w L s (by omega) hbox hY hR hZ) hregular
  have hregCap : (∑ F : RegularIndex Q, (regularPairSeeds Q T selected Gamma F).card) ≤
      P.regularCountCap := P.regular_count_le _ hgap hregSum
  -- cover
  have hRcap : ∀ F ∈ positiveRFactors Q, F.degreeOf 2 ≤ s := fun F hF =>
    degreeOf_R_le_of_mem_box F D w L s (directFactor_data Q F hQ D w L s hbox hF).2.2
  have hcover := cover Q T hQ p s hsmall hRcap selected Gamma hQsolution hTsolution
  -- chain seeds
  have hchain : ∀ F ∈ positiveRFactors Q, ∀ j ∈ Finset.Ico 1 (chainLength F),
      (chainSeeds F j selected Gamma).card ≤ Pc.regularCountCap := by
    intro F hF j hj
    obtain ⟨hj1, hjm⟩ := Finset.mem_Ico.mp hj
    exact chainSeeds_card_le Pc Q F hQ hF j hj1 hjm.le D w L s p hsmall hw hbox hcgap
      hcY hcR hcZ hcY' hcR' hcZ' hcleftR hcleftYSmall hcleftRSmall hcleftZSmall
      hcmixedYSmall hcmixedRSmall hcmixedZSmall selected Gamma nodes x u0 u1 hinj hnodesC
      hCw hCchar hCwa hCan hdegreeC hagreementC hnoPencilC
  -- tail seeds
  have htail : ∀ F ∈ positiveRFactors Q, (tailSeeds F selected Gamma).card ≤ S.countCap := by
    intro F hF
    obtain ⟨hFirr, hFpos, hFbox⟩ := directFactor_data Q F hQ D w L s hbox hF
    have hFsmall : F.degreeOf 2 < p := by
      have := degreeOf_R_le_of_mem_box F D w L s hFbox
      omega
    have hJ : dR (chainLength F) F ≠ 0 := dR_ne_zero F hFirr.ne_zero p hFsmall _ le_rfl
    have hJbox : dR (chainLength F) F ∈ globalCoefficientBox K S.D S.w S.L S.s := by
      rw [hSD, hSw, hSL, hSs]
      exact mem_box_slope_one _ D w L s (dR_mem_box _ F D w L s hFbox) (chainLength_spec F)
    refine rfree_seed_count_le S _ hJ p hJbox (chainLength_spec F) hSs hp (by omega) hSchar
      hSDw hSj hSY hSZ hSmixed hSwa hSan selected (tailSeeds F selected Gamma) nodes x u0 u1
      hinj hnodesS ?_ ?_ ?_ ?_
    · intro γ hγ; exact hdegreeS γ (tailSeeds_subset F selected Gamma hγ)
    · intro γ hγ; exact (Finset.mem_filter.mp hγ).2
    · intro γ hγ; exact hagreementS γ (tailSeeds_subset F selected Gamma hγ)
    · exact noLargeSelectedPencil_mono selected Gamma _ S.w S.errors
        (tailSeeds_subset F selected Gamma) hnoPencilS
  -- R-free seeds
  have hrfree : (rfreeSeeds Q selected Gamma).card ≤ S.countCap := by
    have hJ := rfreeProduct_ne_zero Q hQ
    have hJbox : rfreeProduct Q ∈ globalCoefficientBox K S.D S.w S.L S.s := by
      rw [hSD, hSw, hSL, hSs]
      exact mem_box_slope_one _ D w L s
        (mem_globalCoefficientBox_of_dvd _ Q D w L s hQ (rfreeProduct_dvd Q hQ) hbox)
        (rfreeProduct_R_degree Q)
    refine rfree_seed_count_le S _ hJ p hJbox (rfreeProduct_R_degree Q) hSs hp (by omega)
      hSchar hSDw hSj hSY hSZ hSmixed hSwa hSan selected (rfreeSeeds Q selected Gamma) nodes
      x u0 u1 hinj hnodesS ?_ ?_ ?_ ?_
    · intro γ hγ; exact hdegreeS γ (rfreeSeeds_subset Q selected Gamma hγ)
    · intro γ hγ; exact (Finset.mem_filter.mp hγ).2
    · intro γ hγ; exact hagreementS γ (rfreeSeeds_subset Q selected Gamma hγ)
    · exact noLargeSelectedPencil_mono selected Gamma _ S.w S.errors
        (rfreeSeeds_subset Q selected Gamma) hnoPencilS
  -- budgets
  obtain ⟨hsumChain, hcardPos⟩ := sum_chainLength_sub_one_le Q hQ D w L s (by omega) hs hbox
  -- cardinalities of the four parts
  have hA : (Finset.univ.biUnion fun F : RegularIndex Q =>
      regularPairSeeds Q T selected Gamma F).card ≤ P.regularCountCap :=
    Finset.card_biUnion_le.trans hregCap
  have hB : ((positiveRFactors Q).biUnion fun F =>
      (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma).card ≤
      (s - 1) * Pc.regularCountCap := by
    calc ((positiveRFactors Q).biUnion fun F =>
          (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma).card
        ≤ ∑ F ∈ positiveRFactors Q,
            ((Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ F ∈ positiveRFactors Q, ∑ j ∈ Finset.Ico 1 (chainLength F),
            (chainSeeds F j selected Gamma).card :=
          Finset.sum_le_sum fun F _ => Finset.card_biUnion_le
      _ ≤ ∑ F ∈ positiveRFactors Q, ∑ _j ∈ Finset.Ico 1 (chainLength F), Pc.regularCountCap :=
          Finset.sum_le_sum fun F hF => Finset.sum_le_sum fun j hj => hchain F hF j hj
      _ = ∑ F ∈ positiveRFactors Q, (chainLength F - 1) * Pc.regularCountCap := by
          apply Finset.sum_congr rfl
          intro F _
          simp [Finset.sum_const, Nat.card_Ico]
      _ = (∑ F ∈ positiveRFactors Q, (chainLength F - 1)) * Pc.regularCountCap := by
          rw [Finset.sum_mul]
      _ ≤ (s - 1) * Pc.regularCountCap := Nat.mul_le_mul_right _ hsumChain
  have hC : ((positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma).card ≤
      s * S.countCap := by
    calc ((positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma).card
        ≤ ∑ F ∈ positiveRFactors Q, (tailSeeds F selected Gamma).card := Finset.card_biUnion_le
      _ ≤ ∑ _F ∈ positiveRFactors Q, S.countCap := Finset.sum_le_sum fun F hF => htail F hF
      _ = (positiveRFactors Q).card * S.countCap := by simp [Finset.sum_const]
      _ ≤ s * S.countCap := Nat.mul_le_mul_right _ hcardPos
  have hunion := Finset.card_le_card hcover
  have h1 := Finset.card_union_le
    ((Finset.univ.biUnion fun F : RegularIndex Q => regularPairSeeds Q T selected Gamma F) ∪
      ((positiveRFactors Q).biUnion fun F =>
        (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma) ∪
      ((positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma))
    (rfreeSeeds Q selected Gamma)
  have h2 := Finset.card_union_le
    ((Finset.univ.biUnion fun F : RegularIndex Q => regularPairSeeds Q T selected Gamma F) ∪
      ((positiveRFactors Q).biUnion fun F =>
        (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma))
    ((positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma)
  have h3 := Finset.card_union_le
    (Finset.univ.biUnion fun F : RegularIndex Q => regularPairSeeds Q T selected Gamma F)
    ((positiveRFactors Q).biUnion fun F =>
      (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma)
  have hfinal : (s + 1) * S.countCap = s * S.countCap + S.countCap := by ring
  omega

end Assembly

end

end ProximityPrize.SubmissionLower.LocatorDerivativeChain
