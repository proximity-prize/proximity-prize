import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSurfaceSeedCount
import ProximityPrize.SubmissionLower.ContactSparseProjectionBridge
import ProximityPrize.SubmissionLower.ContactSparseSurfaceCaps
import ProximityPrize.SubmissionLower.ContactPrimeSeedIncidenceSmall
import ProximityPrize.SubmissionLower.ContactProjectionFiniteSmall

/-!
# Proper-cut aggregation with small characteristic-free projections

The component cover and global degree budgets are unchanged.  Each
component now consumes the small-projection zero count and the sharp
proper-node coefficient.
-/

namespace ProximityPrize.SubmissionLower.ContactSparseProperCutSmall

open scoped Classical BigOperators
open ActualCurveCoordinateField ActualCurveRationalProjection ActualCurveZeroCount
  ActualCurveZeroCountSmall ActualCoordinateDegreeSum
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
  ContactPrimeSeedIncidence ContactPrimeSeedIncidenceSmall
  ContactRegularComponentCover ContactProperCutSeedCount ContactSurfaceSeedCount
  ContactProjectionFiniteSmall ActualCurveProjectionBounds
  ContactSparseResultant ContactSparseProjectionBridge
  ContactSparseSurfaceCaps ContactAlignmentParameters ContactCountingCaps
  ContactInterpolation ContactComponentPencils TrivariateRationalCollection

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

variable {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
variable (φ : Polynomial K →+* Ω)

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Ω := Classical.decEq Ω

variable {ι : Type*}
local instance : DecidableEq ι := Classical.decEq ι

theorem proper_cut_seed_bound_of_small_projection_data
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) Ω)
    (hG : Irreducible G) (hdiv : G ∣ surfaceMap φ F)
    (hproper : ¬ G ∣ T)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset ι) (x u₀ u₁ : ι → K)
    (hinj : Set.InjOn x nodes)
    (p w a e : ℕ) [CharP Ω p] (hp : p.Prime)
    (hw : 1 ≤ w) (hchar : w < p) (hwa : w < a) (han : a ≤ nodes.card)
    (hproj : ∀ C : RegularComponent Ω G T (regularitySurface φ F),
      ProjectionsFiniteSmall Ω C.1 p)
    (hseparator : ∀ C : RegularComponent Ω G T (regularitySurface φ F),
      ∃ (i : Fin 3) (hi : Transcendental Ω (coordinate Ω C.1 i)),
        letI : Algebra (RatFunc Ω) (CoordinateField Ω C.1) :=
          rationalBaseAlgebra Ω C.1 i hi
        Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1))
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0)
    (hregular : ∀ γ ∈ Γ, MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hGpoint : ∀ γ ∈ Γ, MvPolynomial.eval (selectedPoint φ selected γ) G = 0)
    (hTpoint : ∀ γ ∈ Γ, MvPolynomial.eval (selectedPoint φ selected γ) T = 0)
    (hagreement : ∀ γ ∈ Γ,
      a ≤ (nodes.filter (fun i ↦
        (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w e)
    (cap budget : Fin 3 → ℕ)
    (hcap : ∀ i ∈ nodes, ∀ j,
      (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j)
    (hbudget : ∀ i,
      (∑ C : RegularComponent Ω G T (regularitySurface φ F),
        actualCoordinateDegree Ω C.1 i) ≤ budget i) :
    Γ.card * (a - w) ≤
      (nodes.card - w) * (∑ i, cap i * budget i) +
        (e + 1) * (a - w) * budget 2 := by
  classical
  let H := regularitySurface φ F
  have hHp : ∀ γ ∈ Γ,
      MvPolynomial.eval (selectedPoint φ selected γ) H ≠ 0 := by
    intro γ hγ
    change MvPolynomial.eval (selectedPoint φ selected γ)
      (surfaceMap φ (MvPolynomial.pderiv (2 : Fin 4) F)) ≠ 0
    rw [selectedPoint_evaluation]
    exact hregular γ hγ
  let degree : RegularComponent Ω G T H → Fin 3 → ℕ :=
    fun C i ↦ actualCoordinateDegree Ω C.1 i
  have hcomponent : ∀ C : RegularComponent Ω G T H,
      (componentSeeds Ω G T H Γ (selectedPoint φ selected) C).card * (a - w) ≤
        (nodes.card - w) * (∑ i, cap i * degree C i) +
          (e + 1) * (a - w) * degree C 2 := by
    intro C
    have hsub := componentSeeds_subset Ω G T H Γ (selectedPoint φ selected) C
    have hgmem := regularComponent_G_mem Ω G T H C
    have hFmem : surfaceMap φ F ∈ C.1 :=
      ((Ideal.span_singleton_le_iff_mem (I := C.1)).mpr hgmem)
        (Ideal.mem_span_singleton.mpr hdiv)
    obtain ⟨i₀, hi₀, hsep₀⟩ := hseparator C
    exact prime_seed_incidence_sharp_small φ C.1 p hp (hproj C)
      i₀ hi₀ hsep₀ (regularComponent_ne_point Ω G T H C)
      F hFmem (regularComponent_H_not_mem Ω G T H C)
      selected (componentSeeds Ω G T H Γ (selectedPoint φ selected) C)
      nodes x u₀ u₁ hinj w a e hw hchar hwa han
      (fun γ hγ ↦ hdegree γ (hsub hγ))
      (fun γ hγ ↦ hsolution γ (hsub hγ))
      (fun γ hγ ↦ hregular γ (hsub hγ))
      (fun γ hγ ↦ componentSeeds_on_prime Ω G T H Γ
        (selectedPoint φ selected) C γ hγ)
      (fun γ hγ ↦ hagreement γ (hsub hγ))
      (noLargeSelectedPencil_mono selected Γ _ w e hsub hnoPencil)
      cap hcap
  exact aggregate_component_incidence Ω G T H Γ (selectedPoint φ selected)
    hGpoint hTpoint hHp (a - w) (nodes.card - w) (e + 1)
    cap budget degree hcomponent hbudget

/-- Summed coordinate degrees for every regular component, retaining the
established rectangular mixed-degree ledger while allowing the base-R
projection to be inseparable of degree below `2p`. -/
theorem regularComponents_degree_budget_sparse_rBase_small
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) Ω)
    (p : ℕ) [CharP Ω p] (hG : Irreducible G) (hproper : ¬ G ∣ T)
    (hGdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hmixed0 : coordinateMixedDegree Ω G T 0 < p)
    (hmixed2 : coordinateMixedDegree Ω G T 2 < p)
    (gy ty g t : ℕ)
    (hGY : G.degreeOf 0 ≤ gy) (hTY : T.degreeOf 0 ≤ ty)
    (hGtotalY : (rationalMap Ω rBaseYOuterOrder G).totalDegree ≤ g)
    (hTtotalY : (rationalMap Ω rBaseYOuterOrder T).totalDegree ≤ t)
    (hGtotalZ : (rationalMap Ω rBaseZOuterOrder G).totalDegree ≤ g)
    (hyg : gy ≤ g) (hyt : ty ≤ t) :
    ∀ i, (∑ C : RegularComponent Ω G T (regularitySurface φ F),
      actualCoordinateDegree Ω C.1 i) ≤ coordinateMixedDegree Ω G T i := by
  classical
  let H := regularitySurface φ F
  letI : ∀ C : RegularComponent Ω G T H, C.1.IsPrime :=
    fun C ↦ regularComponent_isPrime Ω G T H C
  intro i
  fin_cases i
  · exact sum_actualCoordinateDegree_at_le Ω
      (fun C : RegularComponent Ω G T H ↦ C.1) Subtype.val_injective 0 p G T hG
      (regularComponent_G_mem Ω G T H) (regularComponent_T_mem Ω G T H)
      hproper hGdegree hmixed0
  · exact sum_actualCoordinateDegree_rBase_le_mixed_charfree Ω
      (fun C : RegularComponent Ω G T H ↦ C.1) Subtype.val_injective G T hG
      (regularComponent_G_mem Ω G T H) (regularComponent_T_mem Ω G T H)
      hproper gy ty g t hGY hTY hGtotalY hTtotalY hGtotalZ hyg hyt
  · exact sum_actualCoordinateDegree_at_le Ω
      (fun C : RegularComponent Ω G T H ↦ C.1) Subtype.val_injective 2 p G T hG
      (regularComponent_G_mem Ω G T H) (regularComponent_T_mem Ω G T H)
      hproper hGdegree hmixed2

/-- Full proper-cut theorem with a small characteristic-free base-R
projection and an explicitly chosen separable normalization coordinate on
each component. -/
theorem proper_cut_seed_bound_sparse_rBase_small
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) Ω)
    (hG : Irreducible G) (hdiv : G ∣ surfaceMap φ F) (hproper : ¬ G ∣ T)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (hinj : Set.InjOn x nodes)
    (p w a e : ℕ) [CharP Ω p] (hp : p.Prime) (hw : 1 ≤ w)
    (hchar : w < p) (hwa : w < a) (han : a ≤ nodes.card)
    (hGdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hmixed0 : coordinateMixedDegree Ω G T 0 < p)
    (hmixed2 : coordinateMixedDegree Ω G T 2 < p)
    (gy ty g t : ℕ)
    (hGY : G.degreeOf 0 ≤ gy) (hTY : T.degreeOf 0 ≤ ty)
    (hGtotalY : (rationalMap Ω rBaseYOuterOrder G).totalDegree ≤ g)
    (hTtotalY : (rationalMap Ω rBaseYOuterOrder T).totalDegree ≤ t)
    (hGtotalZ : (rationalMap Ω rBaseZOuterOrder G).totalDegree ≤ g)
    (hyg : gy ≤ g) (hyt : ty ≤ t)
    (hsparse : gy * t + ty * g - gy * ty < 2 * p)
    (hcollapsed : g * ty < 2 * p)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0)
    (hregular : ∀ γ ∈ Γ, MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hGpoint : ∀ γ ∈ Γ, MvPolynomial.eval (selectedPoint φ selected γ) G = 0)
    (hTpoint : ∀ γ ∈ Γ, MvPolynomial.eval (selectedPoint φ selected γ) T = 0)
    (hagreement : ∀ γ ∈ Γ,
      a ≤ (nodes.filter (fun i ↦
        (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w e)
    (cap : Fin 3 → ℕ)
    (hcap : ∀ i ∈ nodes, ∀ j,
      (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j) :
    Γ.card * (a - w) ≤
      (nodes.card - w) * (∑ i, cap i * coordinateMixedDegree Ω G T i) +
        (e + 1) * (a - w) * coordinateMixedDegree Ω G T 2 := by
  apply proper_cut_seed_bound_of_small_projection_data φ F G T hG hdiv hproper
    selected Γ nodes x u₀ u₁ hinj p w a e hp hw hchar hwa han
    (fun C ↦ projectionsFiniteSmall_of_sparse_rBase_gates Ω C.1 p hp G T hG
      (regularComponent_G_mem Ω G T (regularitySurface φ F) C)
      (regularComponent_T_mem Ω G T (regularitySurface φ F) C)
      hproper hGdegree hmixed0 hmixed2 gy ty g t hGY hTY hGtotalY hTtotalY
      hGtotalZ hyg hyt hsparse hcollapsed)
    (fun C ↦ exists_separable_separator Ω C.1
      (regularComponent_ne_point Ω G T (regularitySurface φ F) C)
      p G T hG
      (regularComponent_G_mem Ω G T (regularitySurface φ F) C)
      (regularComponent_T_mem Ω G T (regularitySurface φ F) C)
      hproper hGdegree hmixed0 hmixed2)
    hdegree hsolution hregular hGpoint hTpoint hagreement hnoPencil cap
    (coordinateMixedDegree Ω G T) hcap
    (regularComponents_degree_budget_sparse_rBase_small φ F G T p hG hproper
      hGdegree hmixed0 hmixed2 gy ty g t hGY hTY hGtotalY hTtotalY
      hGtotalZ hyg hyt)

/-- Frozen regular-surface count using the sharp incidence coefficient and
the characteristic-free small base-R projection. -/
theorem whole_surface_seed_bound_fixed_sparse_small
    (F : MvPolynomial (Fin 4) K) (G : MvPolynomial (Fin 3) Ω)
    (hG : Irreducible G) (hdiv : G ∣ surfaceMap φ F)
    (hr : 0 < G.degreeOf 1)
    (hHproper : ¬ G ∣ surfaceMap φ (MvPolynomial.pderiv (2 : Fin 4) F))
    (hbox : F ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (hsurface : surfaceMap φ F ≠ 0)
    (hGcaps : HasCaps G ContactProjectionParameters.surfaceVector)
    (hY : F.degreeOf 1 ≤ yCap) (hR : F.degreeOf 2 ≤ slopeCap)
    (hZ : F.degreeOf 3 ≤ seedTotalCap)
    (hHY : (ContactTaylorNumerators.polyH K F).degreeOf (1 : Fin 4) ≤ yCap - 1)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (hinj : Set.InjOn x nodes)
    (hnodes : nodes.card = n) [CharP Ω prime]
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0)
    (hregular : ∀ γ ∈ Γ, MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hGpoint : ∀ γ ∈ Γ, MvPolynomial.eval (selectedPoint φ selected γ) G = 0)
    (hagreement : ∀ γ ∈ Γ,
      agreements ≤ (nodes.filter (fun i ↦
        (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w errors) :
    Γ.card * gap ^ 2 ≤ wholeNumerator (degreeVector G) := by
  classical
  have hcap (j : ι) : HasCaps
      (agreementPolynomial φ F w (x j) (u₀ j) (u₁ j)) agreementVector :=
    fixed_agreement_caps φ F hY hR hZ hHY (x j) (u₀ j) (u₁ j)
  let P : Ideal (MvPolynomial (Fin 3) Ω) := Ideal.span {G}
  letI : P.IsPrime := Ideal.isPrime_span_singleton_of_prime hG.prime
  have hFmem : surfaceMap φ F ∈ P := Ideal.mem_span_singleton.mpr hdiv
  have hHmem : surfaceMap φ (MvPolynomial.pderiv (2 : Fin 4) F) ∉ P := by
    intro h
    exact hHproper (Ideal.mem_span_singleton.mp h)
  let identities := identityNodes φ P F nodes x u₀ u₁ w
  have hidentities : identities ⊆ nodes := identityNodes_subset φ P F nodes x u₀ u₁ w
  have hicard : identities.card ≤ w :=
    identityNodes_card_le_of_r_dependent_principal φ P F hFmem hHmem
      nodes x u₀ u₁ w (by norm_num [w]) hinj G rfl hr
  suffices hraw : Γ.card * (agreements - w) ^ 2 ≤
      (nodes.card - w) * fiberNumerator (nodes.card - w) w agreements errors
        (degreeVector G) agreementVector by
    calc
      Γ.card * gap ^ 2 = Γ.card * (agreements - w) ^ 2 := rfl
      _ ≤ (nodes.card - w) * fiberNumerator (nodes.card - w) w agreements errors
          (degreeVector G) agreementVector := hraw
      _ = wholeNumerator (degreeVector G) := by
        rw [hnodes]
        unfold fiberNumerator wholeNumerator gap
        ring
  apply scaled_sharp_incidence_bound
    (fun γ i ↦ (selected γ).eval (x i) = u₀ i + γ * u₁ i)
    Γ nodes identities agreements w
      (fiberNumerator (nodes.card - w) w agreements errors
        (degreeVector G) agreementVector)
    hidentities hicard (by norm_num [w, agreements])
    (by rw [hnodes]; norm_num [agreements, n]) hagreement
  intro i hi
  obtain ⟨hinode, hnotid⟩ := Finset.mem_sdiff.mp hi
  let T := agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)
  have hproper : ¬ G ∣ T := by
    intro hd
    apply hnotid
    exact Finset.mem_filter.mpr ⟨hinode, Ideal.mem_span_singleton.mpr hd⟩
  let fiber := Γ.filter (fun γ ↦ (selected γ).eval (x i) = u₀ i + γ * u₁ i)
  have hsub : fiber ⊆ Γ := Finset.filter_subset _ _
  have hTpoint : ∀ γ ∈ fiber, MvPolynomial.eval (selectedPoint φ selected γ) T = 0 := by
    intro γ hγ
    have hΓ := hsub hγ
    exact (selected_agreement_zero_iff φ F selected prime w
      (by norm_num [w, prime]) γ (hdegree γ hΓ) (hsolution γ hΓ)
      (hregular γ hΓ) (x i) (u₀ i) (u₁ i)).mpr (Finset.mem_filter.mp hγ).2
  have hTcaps : HasCaps T agreementVector := hcap i
  have hGjoint : MvPolynomial.weightedTotalDegree seedPairWeights G ≤ seedTotalCap :=
    fixed_surface_factor_joint_seed_cap φ F G hbox hdiv hsurface
  have hTjoint : MvPolynomial.weightedTotalDegree seedPairWeights T ≤
      1 + 2 * w * seedTotalCap := by
    simpa [T, agreementPolynomial] using
      fixed_factorialAgreementSurface_joint_seed_cap φ F hbox (x i) (u₀ i) (u₁ i)
  have hGtotalY : (rationalMap Ω rBaseYOuterOrder G).totalDegree ≤ seedTotalCap :=
    (rationalMap_totalDegree_le_seedPair_yOuter Ω G).trans hGjoint
  have hGtotalZ : (rationalMap Ω rBaseZOuterOrder G).totalDegree ≤ seedTotalCap :=
    (rationalMap_totalDegree_le_seedPair_zOuter Ω G).trans hGjoint
  have hTtotalY : (rationalMap Ω rBaseYOuterOrder T).totalDegree ≤
      1 + 2 * w * seedTotalCap :=
    (rationalMap_totalDegree_le_seedPair_yOuter Ω T).trans hTjoint
  have hδ (j : Fin 3) : coordinateMixedDegree Ω G T j ≤
      mixed (degreeVector G) agreementVector (unitAt j) :=
    coordinateMixedDegree_le_caps G T (degreeVector G) agreementVector
      (degreeVector_hasCaps G) hTcaps j
  have hδfixed (j : Fin 3) : coordinateMixedDegree Ω G T j ≤
      mixed ContactProjectionParameters.surfaceVector agreementVector (unitAt j) :=
    coordinateMixedDegree_le_caps G T ContactProjectionParameters.surfaceVector
      agreementVector hGcaps hTcaps j
  rcases ContactProjectionParameters.projection_caps_below_characteristic with
    ⟨_, _, hrect0, hrect2, _⟩
  have hmixed0 : coordinateMixedDegree Ω G T 0 < prime :=
    (hδfixed 0).trans_lt hrect0
  have hmixed2 : coordinateMixedDegree Ω G T 2 < prime :=
    (hδfixed 2).trans_lt hrect2
  have hsparse' :
      yCap * (1 + 2 * w * seedTotalCap) + agreementVector.y * seedTotalCap -
          yCap * agreementVector.y < 2 * prime := by
    norm_num [agreementVector, yCap, weightedCap,
      ContactAlignmentParameters.multiplicity, agreements, w, seedTotalCap, prime]
  have hcollapsed : seedTotalCap * agreementVector.y < 2 * prime := by
    norm_num [agreementVector, yCap, weightedCap,
      ContactAlignmentParameters.multiplicity, agreements, w, seedTotalCap, prime]
  have hcount := proper_cut_seed_bound_sparse_rBase_small φ F G T hG hdiv hproper
    selected fiber nodes x u₀ u₁ hinj prime w agreements errors
    (by simpa [prime, KoalaBear.fieldSize] using KoalaBear.is_prime)
    (by norm_num [w]) (by norm_num [w, prime])
    (by norm_num [w, agreements]) (by rw [hnodes]; norm_num [agreements, n])
    (fun j ↦ (hGcaps j).trans_lt (fixed_surface_caps_below_characteristic j))
    hmixed0 hmixed2 yCap agreementVector.y seedTotalCap
      (1 + 2 * w * seedTotalCap)
    (hGcaps 0) (hTcaps 0) hGtotalY hTtotalY hGtotalZ
    (by norm_num [yCap, weightedCap, ContactAlignmentParameters.multiplicity,
      agreements, w, seedTotalCap])
    (by norm_num [agreementVector, yCap, weightedCap,
      ContactAlignmentParameters.multiplicity, agreements, w, seedTotalCap])
    hsparse' hcollapsed
    (fun γ hγ ↦ hdegree γ (hsub hγ))
    (fun γ hγ ↦ hsolution γ (hsub hγ))
    (fun γ hγ ↦ hregular γ (hsub hγ))
    (fun γ hγ ↦ hGpoint γ (hsub hγ)) hTpoint
    (fun γ hγ ↦ hagreement γ (hsub hγ))
    (noLargeSelectedPencil_mono selected Γ fiber w errors hsub hnoPencil)
    (capAt agreementVector) (fun j _ ↦ hcap j)
  have hsum : (∑ j, capAt agreementVector j * coordinateMixedDegree Ω G T j) ≤
      mixed (degreeVector G) agreementVector agreementVector := by
    calc
      _ ≤ ∑ j, capAt agreementVector j *
          mixed (degreeVector G) agreementVector (unitAt j) := by
        apply Finset.sum_le_sum
        intro j _
        exact Nat.mul_le_mul_left _ (hδ j)
      _ = _ := mixed_cap_sum (degreeVector G) agreementVector agreementVector
  have hscaled := hcount.trans (Nat.add_le_add (Nat.mul_le_mul_left _ hsum)
    (Nat.mul_le_mul_left _ (hδ 2)))
  change fiber.card * (agreements - w) ≤
    fiberNumerator (nodes.card - w) w agreements errors
      (degreeVector G) agreementVector
  simpa only [fiberNumerator, show unitAt (2 : Fin 3) = unitZ by rfl] using hscaled

end

end ProximityPrize.SubmissionLower.ContactSparseProperCutSmall

#print axioms ProximityPrize.SubmissionLower.ContactSparseProperCutSmall.proper_cut_seed_bound_of_small_projection_data
