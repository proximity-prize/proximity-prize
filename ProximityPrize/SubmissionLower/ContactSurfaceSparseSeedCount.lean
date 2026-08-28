import ProximityPrize.SubmissionLower.ContactSurfaceSeedCount
import ProximityPrize.SubmissionLower.ContactProperCutSparseSeedCount
import ProximityPrize.SubmissionLower.ContactAgreementJointSeedCap

/-!
# Whole-surface counting with the sparse middle projection

This is the agreement-first surface count with only its middle-coordinate
characteristic proof changed.  Incidence and mixed-degree costs are identical
to the established whole-surface theorem.
-/

namespace ProximityPrize.SubmissionLower.ContactSurfaceSparseSeedCount

open scoped Classical BigOperators
open ContactAlignmentParameters ContactCountingCaps ContactGenericSurface
open ContactPrimeSeedIncidence ContactComponentPencils ContactPolynomialSolutions
open ContactTranslation ActualCoordinateDegreeSum ContactSurfaceSeedCount
open ContactProperCutSeedCount ContactProperCutSparseSeedCount
open ContactAgreementJointSeedCap ContactFactorCaps

noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

variable {K Ω : Type} [Field K] [Field Ω]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Ω := Classical.decEq Ω

variable [IsAlgClosed Ω]
variable (φ : Polynomial K →+* Ω)
variable {ι : Type*}
local instance : DecidableEq ι := Classical.decEq ι

theorem whole_surface_seed_bound_sparse
    (F : MvPolynomial (Fin 4) K) (G : MvPolynomial (Fin 3) Ω)
    (hG : Irreducible G) (hdiv : G ∣ surfaceMap φ F)
    (hr : 0 < G.degreeOf 1)
    (hHproper : ¬ G ∣ surfaceMap φ (MvPolynomial.pderiv (2 : Fin 4) F))
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (hinj : Set.InjOn x nodes)
    (p w a e : ℕ) [CharP Ω p] (hw : 1 ≤ w) (hchar : w < p)
    (hwa : w < a) (han : a ≤ nodes.card)
    (hGdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hmixed0 : ∀ i ∈ nodes,
      coordinateMixedDegree Ω G (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)) 0 < p)
    (hmixed2 : ∀ i ∈ nodes,
      coordinateMixedDegree Ω G (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)) 2 < p)
    (NG MH LG LH NZ : ℕ)
    (hNG : G.degreeOf 0 ≤ NG) (hNZ : G.degreeOf 2 ≤ NZ)
    (hNGjoint : NG ≤ LG) (hMHjoint : MH ≤ LH)
    (hGcapJoint : ∀ d ∈ G.support, d 0 + d 2 ≤ LG)
    (hTdegree : ∀ i ∈ nodes,
      (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf 0 ≤ MH)
    (hTcapJoint : ∀ i ∈ nodes, ∀ d ∈
      (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).support,
        d 0 + d 2 ≤ LH)
    (hsparse : MH * LG + NG * LH < p + NG * MH)
    (hswap : NZ * MH < p)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0)
    (hregular : ∀ γ ∈ Γ, MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hGpoint : ∀ γ ∈ Γ, MvPolynomial.eval (selectedPoint φ selected γ) G = 0)
    (hagreement : ∀ γ ∈ Γ,
      a ≤ (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w e)
    (E : DegreeVector)
    (hcap : ∀ i ∈ nodes, HasCaps (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)) E) :
    Γ.card * (a - w) ^ 2 ≤
      (nodes.card - w) * fiberNumerator nodes.card w a e (degreeVector G) E := by
  classical
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
      nodes x u₀ u₁ w hw hinj G rfl hr
  apply scaled_sharp_incidence_bound
    (fun γ i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)
    Γ nodes identities a w (fiberNumerator nodes.card w a e (degreeVector G) E)
    hidentities hicard hwa han hagreement
  intro i hi
  obtain ⟨hinode, hnotid⟩ := Finset.mem_sdiff.mp hi
  let T := agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)
  have hproper : ¬ G ∣ T := by
    intro hd
    apply hnotid
    exact Finset.mem_filter.mpr ⟨hinode, Ideal.mem_span_singleton.mpr hd⟩
  let fiber := Γ.filter (fun γ => (selected γ).eval (x i) = u₀ i + γ * u₁ i)
  have hsub : fiber ⊆ Γ := Finset.filter_subset _ _
  have hTpoint : ∀ γ ∈ fiber, MvPolynomial.eval (selectedPoint φ selected γ) T = 0 := by
    intro γ hγ
    have hΓ := hsub hγ
    exact (selected_agreement_zero_iff φ F selected p w hchar γ
      (hdegree γ hΓ) (hsolution γ hΓ) (hregular γ hΓ) (x i) (u₀ i) (u₁ i)).mpr
        (Finset.mem_filter.mp hγ).2
  have hcount := proper_cut_seed_bound_sparse φ F G T hG hdiv hproper selected fiber
    nodes x u₀ u₁ hinj p w a e hw hchar hwa han hGdegree
    (hmixed0 i hinode) (hmixed2 i hinode) NG MH LG LH NZ hNG (hTdegree i hinode)
    hNZ hNGjoint hMHjoint hGcapJoint (hTcapJoint i hinode) hsparse hswap
    (fun γ hγ => hdegree γ (hsub hγ))
    (fun γ hγ => hsolution γ (hsub hγ))
    (fun γ hγ => hregular γ (hsub hγ))
    (fun γ hγ => hGpoint γ (hsub hγ)) hTpoint
    (fun γ hγ => hagreement γ (hsub hγ))
    (noLargeSelectedPencil_mono selected Γ fiber w e hsub hnoPencil) (capAt E) hcap
  have hδ (j : Fin 3) : coordinateMixedDegree Ω G T j ≤ mixed (degreeVector G) E (unitAt j) :=
    coordinateMixedDegree_le_caps G T (degreeVector G) E (degreeVector_hasCaps G)
      (hcap i hinode) j
  have hsum : (∑ j, capAt E j * coordinateMixedDegree Ω G T j) ≤
      mixed (degreeVector G) E E := by
    calc
      _ ≤ ∑ j, capAt E j * mixed (degreeVector G) E (unitAt j) := by
        apply Finset.sum_le_sum
        intro j _
        exact Nat.mul_le_mul_left _ (hδ j)
      _ = _ := mixed_cap_sum (degreeVector G) E E
  exact hcount.trans (Nat.add_le_add (Nat.mul_le_mul_left _ hsum)
    (Nat.mul_le_mul_left _ (hδ 2)))

/-- Fixed witness wrapper.  The joint support caps are supplied explicitly;
the next layer derives them from the original coefficient box and factorhood. -/
theorem whole_surface_seed_bound_fixed_sparse
    (F : MvPolynomial (Fin 4) K) (G : MvPolynomial (Fin 3) Ω)
    (hG : Irreducible G) (hdiv : G ∣ surfaceMap φ F)
    (hr : 0 < G.degreeOf 1)
    (hHproper : ¬ G ∣ surfaceMap φ (MvPolynomial.pderiv (2 : Fin 4) F))
    (hGcaps : HasCaps G ContactProjectionParameters.surfaceVector)
    (hGjoint : ∀ d ∈ G.support, d 0 + d 2 ≤ seedTotalCap)
    (hFseed : MvPolynomial.weightedTotalDegree seedWeights F ≤ seedTotalCap)
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
      agreements ≤ (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w errors) :
    Γ.card * gap ^ 2 ≤ wholeNumerator (degreeVector G) := by
  have hcap (i : ι) : HasCaps (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i))
      agreementVector := fixed_agreement_caps φ F hY hR hZ hHY (x i) (u₀ i) (u₁ i)
  have hTjoint (i : ι) : ∀ d ∈
      (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).support,
        d 0 + d 2 ≤ agreementVector.z := by
    apply surfaceMap_joint_seed_cap φ _ agreementVector.z
    simpa [agreementVector] using agreementNumerator_joint_seed_support_cap
      F seedTotalCap w hFseed (fun j => (j.factorial : K)⁻¹) (x i) (u₀ i) (u₁ i)
  have hcount := whole_surface_seed_bound_sparse φ F G hG hdiv hr hHproper selected Γ
    nodes x u₀ u₁ hinj prime w agreements errors
    (by norm_num [w]) (by norm_num [w, prime]) (by norm_num [w, agreements])
    (by rw [hnodes]; norm_num [agreements, n])
    (fun j => (hGcaps j).trans_lt (fixed_surface_caps_below_characteristic j))
    (fun i _ => by
      exact (coordinateMixedDegree_le_caps G _ _ _ hGcaps (hcap i) 0).trans_lt
        ContactProjectionParameters.outer_agreement_projection_caps_below_characteristic.1)
    (fun i _ => by
      exact (coordinateMixedDegree_le_caps G _ _ _ hGcaps (hcap i) 2).trans_lt
        ContactProjectionParameters.outer_agreement_projection_caps_below_characteristic.2)
    yCap agreementVector.y seedTotalCap agreementVector.z seedTotalCap
    (hGcaps 0) (hGcaps 2) (by norm_num [yCap, weightedCap, ContactAlignmentParameters.multiplicity,
      agreements, w, seedTotalCap])
    (by norm_num [agreementVector, yCap, weightedCap, ContactAlignmentParameters.multiplicity,
      agreements, w, seedTotalCap]) hGjoint
    (fun i _ => hcap i 0) (fun i _ => hTjoint i)
    (by norm_num [agreementVector, yCap, weightedCap, ContactAlignmentParameters.multiplicity,
      agreements, w, seedTotalCap, prime])
    (by norm_num [agreementVector, yCap, weightedCap, ContactAlignmentParameters.multiplicity,
      agreements, w, seedTotalCap, prime])
    hdegree hsolution hregular hGpoint hagreement hnoPencil agreementVector
    (fun i _ => hcap i)
  calc
    Γ.card * gap ^ 2 = Γ.card * (agreements - w) ^ 2 := rfl
    _ ≤ (nodes.card - w) * fiberNumerator nodes.card w agreements errors
        (degreeVector G) agreementVector := hcount
    _ = wholeNumerator (degreeVector G) := by
      rw [hnodes]
      unfold fiberNumerator wholeNumerator gap
      ring

end

end ProximityPrize.SubmissionLower.ContactSurfaceSparseSeedCount

#print axioms ProximityPrize.SubmissionLower.ContactSurfaceSparseSeedCount.whole_surface_seed_bound_fixed_sparse
