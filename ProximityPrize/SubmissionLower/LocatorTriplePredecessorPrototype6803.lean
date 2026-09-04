import ProximityPrize.SubmissionLower.LocatorPredecessorIncidence6803

/-!
# Proper triple-predecessor components

This prototype packages the already available prime-curve zero bound and its
mixed-volume aggregation.  It deliberately counts only components on which
the second predecessor is proper; components containing that predecessor are
the precise remaining derivative-chain obstruction.
-/

namespace ProximityPrize.SubmissionLower.LocatorTriplePredecessorPrototype6803

open scoped Classical BigOperators
open RCN001 RCN007 RCN066 RCN072 RCN095 RCN135 RCN136 RCN219 RCN231 RCN237 RCN238 RCN243 RCN264 RCN267 RCN319 RCN336
open LocatorDerivativeChain
open LocatorExactDerivativeChain6803 LocatorPredecessorIncidence6803

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {Omega Seed : Type} [Field Omega]
  {G T1 T2 H : MvPolynomial (Fin 3) Omega}
  {surfaceFlag firstFlag secondFlag : FlagDegree}

/-- The union of seed sets on curve components where `T2` is a proper cut is
bounded by the triple mixed volume.  No agreement-incidence argument occurs
in this branch. -/
theorem proper_component_seed_union_card_le
    [DecidableEq Seed]
    (B : PrimeFlagBudgetFamily (G := G) (T := T1) (H := H)
      surfaceFlag firstFlag)
    (S : Finset Seed) (point : Seed → Fin 3 → Omega)
    (hpoint : Function.Injective point)
    (hflag : ∀ C : RegularComponent Omega G T1 H,
      PolynomialInFlagMod C.1 secondFlag T2)
    (hzero : ∀ C : RegularComponent Omega G T1 H,
      ∀ gamma ∈ componentSeeds Omega G T1 H S point C,
        MvPolynomial.aeval (point gamma) T2 = 0) :
    ((Finset.univ.filter fun C : RegularComponent Omega G T1 H ↦
        T2 ∉ C.1).biUnion
      (componentSeeds Omega G T1 H S point)).card ≤
      flagMixed surfaceFlag firstFlag secondFlag := by
  classical
  calc
    ((Finset.univ.filter fun C : RegularComponent Omega G T1 H ↦
          T2 ∉ C.1).biUnion
        (componentSeeds Omega G T1 H S point)).card
        ≤ ∑ C ∈ (Finset.univ.filter fun C :
            RegularComponent Omega G T1 H ↦ T2 ∉ C.1),
            (componentSeeds Omega G T1 H S point C).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ C ∈ (Finset.univ.filter fun C :
            RegularComponent Omega G T1 H ↦ T2 ∉ C.1),
            B.weightedCost secondFlag C := by
      apply Finset.sum_le_sum
      intro C hC
      have hproper : T2 ∉ C.1 := (Finset.mem_filter.mp hC).2
      exact component_secondTail_card_le_mod B C S point hpoint
        (hflag C) hproper (hzero C)
    _ ≤ ∑ C : RegularComponent Omega G T1 H,
          B.weightedCost secondFlag C := by
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ ≤ flagMixed surfaceFlag firstFlag secondFlag :=
      B.sum_weightedCost_le secondFlag

/-- Every predecessor retained by an exact chain stratum vanishes after the
geometric surface map.  This discharges the zero hypothesis of
`component_secondTail_card_le_mod` for any earlier derivative. -/
theorem exact_chain_mapped_predecessor_zero
    {K Omega : Type} [Field K] [Field Omega]
    (phi : Polynomial K →+* Omega)
    (F : MvPolynomial (Fin 4) K) (j k : ℕ) (hk : k ≤ j)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (gamma : K) (hgamma : gamma ∈ exactChainSeeds F j selected Gamma) :
    MvPolynomial.aeval (selectedPoint phi selected gamma)
      (surfaceMap phi (dR k F)) = 0 := by
  obtain ⟨_, _, hall⟩ := Finset.mem_filter.mp hgamma
  exact selected_surface_zero phi (dR k F) selected gamma (hall k hk)

/-- Backwards component recursion has only two outcomes: some earlier
predecessor is a proper cut, or both `F` and `dR 1 F` belong to the curve
prime. -/
theorem predecessor_escape_or_initial_mem
    {K Omega : Type} [Field K] [Field Omega]
    (phi : Polynomial K →+* Omega)
    (F : MvPolynomial (Fin 4) K) (j : ℕ) (hj : 2 ≤ j)
    (P : Ideal (MvPolynomial (Fin 3) Omega))
    (hT1 : surfaceMap phi (dR (j - 1) F) ∈ P) :
    (∃ k < j - 1, surfaceMap phi (dR k F) ∉ P) ∨
      (surfaceMap phi F ∈ P ∧ surfaceMap phi (dR 1 F) ∈ P) := by
  by_cases h : ∀ k < j - 1, surfaceMap phi (dR k F) ∈ P
  · right
    constructor
    · simpa using h 0 (by omega)
    · by_cases hlt : 1 < j - 1
      · exact h 1 hlt
      · have hj2 : j = 2 := by omega
        simpa [hj2] using hT1
  · left
    push Not at h
    exact h

private theorem prime_height_eq_two_of_irreducible_pair
    {Omega : Type} [Field Omega]
    (G T : MvPolynomial (Fin 3) Omega) (hG : Irreducible G)
    (hproper : ¬ G ∣ T)
    (P : Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
    (hPheight : P.height ≤ 2) (hGmem : G ∈ P) (hTmem : T ∈ P) :
    P.height = 2 := by
  let I : Ideal (MvPolynomial (Fin 3) Omega) := Ideal.span {G}
  letI : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hG.prime
  have hIP : I ≤ P := by
    apply Ideal.span_le.mpr
    simpa using hGmem
  have hTnot : T ∉ I := by
    intro h
    exact hproper (Ideal.mem_span_singleton.mp h)
  have hIne : I ≠ P := by
    intro h
    exact hTnot (h ▸ hTmem)
  have hIlt : I < P := lt_of_le_of_ne hIP hIne
  have hIbot : I ≠ ⊥ := by
    intro h
    have hzero : G = 0 := by
      have : G ∈ (⊥ : Ideal (MvPolynomial (Fin 3) Omega)) :=
        h ▸ Ideal.subset_span (by simp)
      simpa using this
    exact hG.ne_zero hzero
  have hbotlt : (⊥ : Ideal (MvPolynomial (Fin 3) Omega)) < I :=
    lt_of_le_of_ne bot_le hIbot.symm
  have hone : (1 : ℕ∞) ≤ I.height := by
    calc
      1 = (0 : ℕ∞) + 1 := by simp
      _ ≤ (⊥ : Ideal (MvPolynomial (Fin 3) Omega)).height + 1 := by
        gcongr
        exact zero_le
      _ ≤ I.height := Ideal.height_add_one_le_of_lt_of_isPrime hbotlt
  have htwo : (2 : ℕ∞) ≤ P.height := by
    calc
      2 = (1 : ℕ∞) + 1 := by norm_num
      _ ≤ I.height + 1 := by gcongr
      _ ≤ P.height := Ideal.height_add_one_le_of_lt_of_isPrime hIlt
  exact le_antisymm hPheight htwo

/-- Generic height-rigidity transfer to an irreducible initial surface
factor.  This is the form needed after geometrically factoring `surfaceMap F`.
-/
theorem regular_component_mem_irreducible_initial_family
    {Omega : Type} [Field Omega]
    (G0 T0 : MvPolynomial (Fin 3) Omega) (hG0 : Irreducible G0)
    (hproper : ¬ G0 ∣ T0)
    {G T H : MvPolynomial (Fin 3) Omega}
    (C : RegularComponent Omega G T H)
    (hG0mem : G0 ∈ C.1) (hT0mem : T0 ∈ C.1) :
    C.1 ∈ componentFamily Omega G0 T0 := by
  let I := cutIdeal Omega G0 T0
  have hcut : I ≤ C.1 := by
    apply Ideal.span_le.mpr
    intro A hA
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with rfl | rfl
    · exact hG0mem
    · exact hT0mem
  obtain ⟨P, hPmin, hPC⟩ := Ideal.exists_minimalPrimes_le hcut
  have hPfamily : P ∈ componentFamily Omega G0 T0 :=
    (mem_componentFamily Omega G0 T0 P).mpr hPmin
  letI : P.IsPrime := hPmin.isPrime
  have hPG0mem : G0 ∈ P :=
    cutIdeal_le_component Omega G0 T0 P hPfamily
      (Ideal.subset_span (Set.mem_insert G0 {T0}))
  have hPT0mem : T0 ∈ P :=
    cutIdeal_le_component Omega G0 T0 P hPfamily
      (Ideal.subset_span (Set.mem_insert_of_mem G0 (Set.mem_singleton T0)))
  have hPheight := prime_height_eq_two_of_irreducible_pair G0 T0 hG0
    hproper P (component_height_le_two Omega G0 T0 P hPfamily)
    hPG0mem hPT0mem
  have hCheight := prime_height_eq_two_of_irreducible_pair G0 T0 hG0
    hproper C.1
    (component_height_le_two Omega G T C.1
      (regularComponent_mem Omega G T H C)) hG0mem hT0mem
  letI : P.FiniteHeight := P.finiteHeight_iff.mpr (by
    rw [hPheight]
    norm_num)
  have hPCeq : P = C.1 := Ideal.eq_of_le_of_height_le
    (I := P) (J := C.1) hPC (by rw [hCheight, hPheight])
  rw [← hPCeq]
  exact hPfamily

/-- All minimal components of an irreducible proper initial pair, represented
as regular components with the harmless filter polynomial `1`, have the
standard finite/separable projection gates. -/
theorem initial_component_projections
    {Omega : Type} [Field Omega]
    (G T : MvPolynomial (Fin 3) Omega) (p : ℕ) [CharP Omega p]
    (hG : Irreducible G) (hproper : ¬ G ∣ T)
    (hGdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hcutDegree : ∀ j k : Fin 3, j ≠ k →
      T.degreeOf j * G.degreeOf k + G.degreeOf j * T.degreeOf k < p)
    (C : RegularComponent Omega G T 1) :
    ProjectionsFiniteSeparable Omega C.1 := by
  exact RCN001.projectionsFiniteSeparable_of_original_gates Omega C.1 p G T hG
    (regularComponent_G_mem Omega G T 1 C)
    (regularComponent_T_mem Omega G T 1 C)
    hproper hGdegree hcutDegree

/-- The complete initial component family consumes only the mixed-degree
budget of the one pair `(G,T)`. -/
theorem initial_components_degree_budget
    {Omega : Type} [Field Omega]
    (G T : MvPolynomial (Fin 3) Omega) (p : ℕ) [CharP Omega p]
    (hG : Irreducible G) (hproper : ¬ G ∣ T)
    (hGdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hcutDegree : ∀ j k : Fin 3, j ≠ k →
      T.degreeOf j * G.degreeOf k + G.degreeOf j * T.degreeOf k < p) :
    ∀ i, (∑ C : RegularComponent Omega G T 1,
      actualCoordinateDegree Omega C.1 i) ≤
        coordinateMixedDegree Omega G T i := by
  intro i
  letI : ∀ C : RegularComponent Omega G T 1, C.1.IsPrime :=
    fun C ↦ regularComponent_isPrime Omega G T 1 C
  have hneq : (Equiv.swap (0 : Fin 3) i) 1 ≠
      (Equiv.swap (0 : Fin 3) i) 2 :=
    (Equiv.swap (0 : Fin 3) i).injective.ne (by decide)
  have hmixed : coordinateMixedDegree Omega G T i < p :=
    hcutDegree ((Equiv.swap (0 : Fin 3) i) 1)
      ((Equiv.swap (0 : Fin 3) i) 2) hneq
  exact sum_actualCoordinateDegree_at_le Omega
    (fun C : RegularComponent Omega G T 1 ↦ C.1)
    Subtype.val_injective i p G T hG
    (regularComponent_G_mem Omega G T 1)
    (regularComponent_T_mem Omega G T 1)
    hproper hGdegree hmixed

/-- Aggregate one regular-incidence population and one exceptional zero
population for every component of a fixed initial curve family.  The carrier
polynomial may vary with the component (it will be the derivative immediately
before that component's first escaping derivative), while both populations
are charged to the coordinate-degree budget of the initial family. -/
theorem grouped_first_escape_card_le
    {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
    (phi : Polynomial K →+* Omega)
    {G0 T0 H0 : MvPolynomial (Fin 3) Omega}
    (selected : K → Polynomial K) (Gamma : Finset K)
    (main exceptional : RegularComponent Omega G0 T0 H0 → Finset K)
    (carrier : RegularComponent Omega G0 T0 H0 →
      MvPolynomial (Fin 4) K)
    [DecidableEq K]
    (hcover : Gamma ⊆ Finset.univ.biUnion fun C ↦ main C ∪ exceptional C)
    (hmain_sub : ∀ C, main C ⊆ Gamma)
    (hproj : ∀ C : RegularComponent Omega G0 T0 H0,
      ProjectionsFiniteSeparable Omega C.1)
    (hcarrier_mem : ∀ C, (main C ∪ exceptional C).Nonempty →
      surfaceMap phi (carrier C) ∈ C.1)
    (hescape_not_mem : ∀ C, (main C ∪ exceptional C).Nonempty →
      surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) (carrier C)) ∉ C.1)
    (hmain_solution : ∀ C, ∀ gamma ∈ main C,
      specialization K (selected gamma) gamma (carrier C) = 0)
    (hmain_regular : ∀ C, ∀ gamma ∈ main C,
      MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
        (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
          (phi Polynomial.X))
        (MvPolynomial.pderiv (2 : Fin 4) (carrier C)) ≠ 0)
    (hmain_point : ∀ C, ∀ gamma ∈ main C,
      C.1 ≤ RingHom.ker
        (MvPolynomial.aeval (selectedPoint phi selected gamma)).toRingHom)
    (hexceptional_zero : ∀ C, ∀ gamma ∈ exceptional C,
      specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) (carrier C)) = 0)
    (hexceptional_point : ∀ C, ∀ gamma ∈ exceptional C,
      C.1 ≤ RingHom.ker
        (MvPolynomial.aeval (selectedPoint phi selected gamma)).toRingHom)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes)
    (p w a errors : ℕ) [CharP Omega p]
    (hw : 1 ≤ w) (hchar : w < p) (hwa : w < a)
    (han : a ≤ nodes.card)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma,
      a ≤ (nodes.filter fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (agreementCap escapeCap budget : Fin 3 → ℕ)
    (hagreementCap : ∀ C, (main C ∪ exceptional C).Nonempty → ∀ i ∈ nodes, ∀ j,
      (agreementPolynomial phi (carrier C) w (x i) (u0 i) (u1 i)).degreeOf j ≤
        agreementCap j)
    (hescapeCap : ∀ C, (main C ∪ exceptional C).Nonempty → ∀ j,
      (surfaceMap phi
        (MvPolynomial.pderiv (2 : Fin 4) (carrier C))).degreeOf j ≤
          escapeCap j)
    (hbudget : ∀ j,
      (∑ C : RegularComponent Omega G0 T0 H0,
        actualCoordinateDegree Omega C.1 j) ≤ budget j) :
    Gamma.card * (a - w) ≤
      (nodes.card - w) * (∑ j, agreementCap j * budget j) +
        (errors + 1) * (a - w) * budget 2 +
        (a - w) * (∑ j, escapeCap j * budget j) := by
  classical
  let gap := a - w
  let degree : RegularComponent Omega G0 T0 H0 → Fin 3 → ℕ :=
    fun C j ↦ actualCoordinateDegree Omega C.1 j
  have hmain (C : RegularComponent Omega G0 T0 H0) :
      (main C).card * gap ≤
        (nodes.card - w) * (∑ j, agreementCap j * degree C j) +
          (errors + 1) * gap * degree C 2 := by
    by_cases hactive : (main C ∪ exceptional C).Nonempty
    · exact prime_seed_incidence_sharp phi C.1 (hproj C)
        (regularComponent_ne_point Omega G0 T0 H0 C)
        (carrier C) (hcarrier_mem C hactive) (hescape_not_mem C hactive)
        selected (main C) nodes x u0 u1 hinj p w a errors hw hchar hwa han
        (fun gamma hgamma ↦ hdegree gamma (hmain_sub C hgamma))
        (hmain_solution C) (hmain_regular C) (hmain_point C)
        (fun gamma hgamma ↦ by
          apply (hagreement gamma (hmain_sub C hgamma)).trans
          apply Finset.card_le_card
          intro i hi
          simpa only [Finset.mem_filter] using hi)
        (noLargeSelectedPencil_mono selected Gamma (main C) w errors
          (hmain_sub C) hnoPencil)
        agreementCap (hagreementCap C hactive)
    · have hmnot : ¬ (main C).Nonempty := by
        intro hm
        exact hactive (hm.mono (Finset.subset_union_left))
      rw [Finset.not_nonempty_iff_eq_empty.mp hmnot]
      simp
  have hexceptional (C : RegularComponent Omega G0 T0 H0) :
      (exceptional C).card ≤ ∑ j, escapeCap j * degree C j := by
    by_cases hactive : (main C ∪ exceptional C).Nonempty
    · have hcount := predecessor_component_card_le phi C.1 (hproj C)
        (regularComponent_ne_point Omega G0 T0 H0 C)
        (MvPolynomial.pderiv (2 : Fin 4) (carrier C)) selected
        (exceptional C) (hexceptional_zero C) (hexceptional_point C)
        (hescape_not_mem C hactive) escapeCap (hescapeCap C hactive)
      simpa only [componentCost, degree] using hcount
    · have henot : ¬ (exceptional C).Nonempty := by
        intro he
        exact hactive (he.mono (Finset.subset_union_right))
      rw [Finset.not_nonempty_iff_eq_empty.mp henot]
      simp
  have hcard : Gamma.card ≤
      ∑ C : RegularComponent Omega G0 T0 H0,
        ((main C).card + (exceptional C).card) := by
    calc
      Gamma.card ≤
          (Finset.univ.biUnion fun C ↦ main C ∪ exceptional C).card :=
        Finset.card_le_card hcover
      _ ≤ ∑ C : RegularComponent Omega G0 T0 H0,
          (main C ∪ exceptional C).card := Finset.card_biUnion_le
      _ ≤ ∑ C : RegularComponent Omega G0 T0 H0,
          ((main C).card + (exceptional C).card) := by
        apply Finset.sum_le_sum
        intro C _
        exact Finset.card_union_le _ _
  have hsum :
      Gamma.card * gap ≤
        (nodes.card - w) *
            (∑ j, agreementCap j *
              (∑ C : RegularComponent Omega G0 T0 H0, degree C j)) +
          (errors + 1) * gap *
            (∑ C : RegularComponent Omega G0 T0 H0, degree C 2) +
          gap * (∑ j, escapeCap j *
            (∑ C : RegularComponent Omega G0 T0 H0, degree C j)) := by
    calc
      Gamma.card * gap ≤
          (∑ C : RegularComponent Omega G0 T0 H0,
            ((main C).card + (exceptional C).card)) * gap :=
        Nat.mul_le_mul_right gap hcard
      _ = ∑ C : RegularComponent Omega G0 T0 H0,
          ((main C).card * gap + (exceptional C).card * gap) := by
        rw [Finset.sum_mul]
        simp only [Nat.add_mul]
      _ ≤ ∑ C : RegularComponent Omega G0 T0 H0,
          ((nodes.card - w) * (∑ j, agreementCap j * degree C j) +
            (errors + 1) * gap * degree C 2 +
            gap * (∑ j, escapeCap j * degree C j)) := by
        apply Finset.sum_le_sum
        intro C _
        exact Nat.add_le_add (hmain C) (by
          simpa only [Nat.mul_comm] using
            Nat.mul_le_mul_right gap (hexceptional C))
      _ =
          (nodes.card - w) *
              (∑ j, agreementCap j *
                (∑ C : RegularComponent Omega G0 T0 H0, degree C j)) +
            (errors + 1) * gap *
              (∑ C : RegularComponent Omega G0 T0 H0, degree C 2) +
            gap * (∑ j, escapeCap j *
              (∑ C : RegularComponent Omega G0 T0 H0, degree C j)) := by
        have hswap (cap : Fin 3 → ℕ) :
            (∑ C : RegularComponent Omega G0 T0 H0,
              ∑ j, cap j * degree C j) =
              ∑ j, cap j *
                (∑ C : RegularComponent Omega G0 T0 H0, degree C j) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
          hswap agreementCap, hswap escapeCap]
  dsimp only [gap] at hsum ⊢
  exact hsum.trans (Nat.add_le_add
    (Nat.add_le_add
      (Nat.mul_le_mul_left (nodes.card - w)
        (Finset.sum_le_sum fun j _ ↦
          Nat.mul_le_mul_left (agreementCap j) (hbudget j)))
      (Nat.mul_le_mul_left ((errors + 1) * (a - w)) (hbudget 2)))
    (Nat.mul_le_mul_left (a - w)
      (Finset.sum_le_sum fun j _ ↦
        Nat.mul_le_mul_left (escapeCap j) (hbudget j))))

/-- A height-two stage component which contains the original polynomial and
its first derivative is already one of the initial singular-curve components.
This is the algebraic transfer needed by the terminal (all predecessors
identically zero) branch of a backwards derivative recursion. -/
theorem regular_component_mem_initial_family
    {K : Type} [Field K]
    (F D1 : MvPolynomial (Fin 4) K) (hF : Irreducible F)
    (hproper : ¬ F ∣ D1)
    {G T H : MvPolynomial (Fin 3) (GenericField K)}
    (C : RegularComponent (GenericField K) G T H)
    (hFmem : surfaceMap (polynomialEmbedding K) F ∈ C.1)
    (hD1mem : surfaceMap (polynomialEmbedding K) D1 ∈ C.1) :
    C.1 ∈ componentFamily (GenericField K)
      (surfaceMap (polynomialEmbedding K) F)
      (surfaceMap (polynomialEmbedding K) D1) := by
  let F0 := surfaceMap (polynomialEmbedding K) F
  let D10 := surfaceMap (polynomialEmbedding K) D1
  let I := cutIdeal (GenericField K) F0 D10
  have hcut : I ≤ C.1 := by
    apply Ideal.span_le.mpr
    intro A hA
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with rfl | rfl
    · exact hFmem
    · exact hD1mem
  obtain ⟨P, hPmin, hPC⟩ := Ideal.exists_minimalPrimes_le hcut
  have hPfamily : P ∈ componentFamily (GenericField K) F0 D10 := by
    exact (mem_componentFamily (GenericField K) F0 D10 P).mpr hPmin
  letI : P.IsPrime := hPmin.isPrime
  have hPheight_le : P.height ≤ 2 :=
    component_height_le_two (GenericField K) F0 D10 P hPfamily
  have hPFmem : F0 ∈ P :=
    cutIdeal_le_component (GenericField K) F0 D10 P hPfamily
      (Ideal.subset_span (Set.mem_insert F0 {D10}))
  have hPD1mem : D10 ∈ P :=
    cutIdeal_le_component (GenericField K) F0 D10 P hPfamily
      (Ideal.subset_span (Set.mem_insert_of_mem F0 (Set.mem_singleton D10)))
  have hPoriginal : (originalPrime P).height = 2 :=
    originalPrime_height_eq_two P hPheight_le F D1 hF
      hPFmem hPD1mem hproper
  have hPheight : P.height = 2 := by
    apply le_antisymm hPheight_le
    calc
      2 = (originalPrime P).height := hPoriginal.symm
      _ ≤ P.height := originalPrime_height_le P
  have hCheight_le : C.1.height ≤ 2 :=
    component_height_le_two (GenericField K) G T C.1
      (regularComponent_mem (GenericField K) G T H C)
  have hCoriginal : (originalPrime C.1).height = 2 :=
    originalPrime_height_eq_two C.1 hCheight_le F D1 hF
      hFmem hD1mem hproper
  have hCheight : C.1.height = 2 := by
    apply le_antisymm hCheight_le
    calc
      2 = (originalPrime C.1).height := hCoriginal.symm
      _ ≤ C.1.height := originalPrime_height_le C.1
  letI : P.FiniteHeight := P.finiteHeight_iff.mpr (by
    rw [hPheight]
    norm_num)
  have hPCeq : P = C.1 := Ideal.eq_of_le_of_height_le
      (I := P) (J := C.1) hPC (by
    rw [hCheight, hPheight])
  rw [← hPCeq]
  exact hPfamily

end

end ProximityPrize.SubmissionLower.LocatorTriplePredecessorPrototype6803
