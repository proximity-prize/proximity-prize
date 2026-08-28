import ProximityPrize.SubmissionLower.ContactProperCutSeedCount
import ProximityPrize.SubmissionLower.ActualCoordinateSparseDegreeSum

/-!
# Proper-cut counting with one sparse characteristic projection

The geometric incidence and mixed-degree budgets are unchanged.  Only the
middle-coordinate separability gate uses the joint `Y+Z` Newton caps.
-/

namespace ProximityPrize.SubmissionLower.ContactProperCutSparseSeedCount

open ActualCurveCoordinateField ActualCurveZeroCount ActualCurveProjectionBounds
open ActualCoordinateDegreeSum ActualCoordinateSparseDegreeSum ActualPlanePositiveOrder
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount

noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
variable (φ : Polynomial K →+* Ω)

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Ω := Classical.decEq Ω

variable {ι : Type*}
local instance : DecidableEq ι := Classical.decEq ι

theorem proper_cut_seed_bound_of_projection_sum_sparse
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) Ω)
    (hG : Irreducible G) (hdiv : G ∣ surfaceMap φ F) (hproper : ¬ G ∣ T)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (hinj : Set.InjOn x nodes)
    (p w a e : ℕ) [CharP Ω p] (hw : 1 ≤ w) (hchar : w < p)
    (hwa : w < a) (han : a ≤ nodes.card)
    (hGdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hmixed0 : coordinateMixedDegree Ω G T 0 < p)
    (hmixed2 : coordinateMixedDegree Ω G T 2 < p)
    (NG MH LG LH NZ : ℕ)
    (hNG : G.degreeOf 0 ≤ NG) (hMH : T.degreeOf 0 ≤ MH)
    (hNZ : G.degreeOf 2 ≤ NZ)
    (hNGjoint : NG ≤ LG) (hMHjoint : MH ≤ LH)
    (hGcapJoint : ∀ d ∈ G.support, d 0 + d 2 ≤ LG)
    (hTcapJoint : ∀ d ∈ T.support, d 0 + d 2 ≤ LH)
    (hsparse : MH * LG + NG * LH < p + NG * MH)
    (hswap : NZ * MH < p)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0)
    (hregular : ∀ γ ∈ Γ, MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hGpoint : ∀ γ ∈ Γ, MvPolynomial.eval (selectedPoint φ selected γ) G = 0)
    (hTpoint : ∀ γ ∈ Γ, MvPolynomial.eval (selectedPoint φ selected γ) T = 0)
    (hagreement : ∀ γ ∈ Γ,
      a ≤ (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w e)
    (cap budget : Fin 3 → ℕ)
    (hcap : ∀ i ∈ nodes, ∀ j,
      (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j)
    (hbudget : ∀ i,
      (∑ C : RegularComponent Ω G T (regularitySurface φ F),
        actualCoordinateDegree Ω C.1 i) ≤ budget i) :
    Γ.card * (a - w) ≤ nodes.card * (∑ i, cap i * budget i) +
      (e + 1) * (a - w) * budget 2 := by
  classical
  let H := regularitySurface φ F
  have hHp : ∀ γ ∈ Γ, MvPolynomial.eval (selectedPoint φ selected γ) H ≠ 0 := by
    intro γ hγ
    change MvPolynomial.eval (selectedPoint φ selected γ)
      (surfaceMap φ (MvPolynomial.pderiv (2 : Fin 4) F)) ≠ 0
    rw [selectedPoint_evaluation]
    exact hregular γ hγ
  let degree : RegularComponent Ω G T H → Fin 3 → ℕ :=
    fun C i => actualCoordinateDegree Ω C.1 i
  have hcomponent : ∀ C : RegularComponent Ω G T H,
      (componentSeeds Ω G T H Γ (selectedPoint φ selected) C).card * (a - w) ≤
        nodes.card * (∑ i, cap i * degree C i) + (e + 1) * (a - w) * degree C 2 := by
    intro C
    have hsub := componentSeeds_subset Ω G T H Γ (selectedPoint φ selected) C
    have hgmem := regularComponent_G_mem Ω G T H C
    have htmem := regularComponent_T_mem Ω G T H C
    have hFmem : surfaceMap φ F ∈ C.1 :=
      ((Ideal.span_singleton_le_iff_mem (I := C.1)).mpr hgmem)
        (Ideal.mem_span_singleton.mpr hdiv)
    have hproj : ProjectionsFiniteSeparable Ω C.1 :=
      projectionsFiniteSeparable_of_middle_sparse_gates Ω C.1 p G T hG hgmem htmem
        hproper hGdegree hmixed0 hmixed2 NG MH LG LH NZ hNG hMH hNZ
        hNGjoint hMHjoint hGcapJoint hTcapJoint hsparse hswap
    have hcount := prime_seed_incidence φ C.1 hproj
      (regularComponent_ne_point Ω G T H C) F hFmem
      (regularComponent_H_not_mem Ω G T H C) selected
      (componentSeeds Ω G T H Γ (selectedPoint φ selected) C)
      nodes x u₀ u₁ hinj p w a e hw hchar hwa han
      (fun γ hγ => hdegree γ (hsub hγ))
      (fun γ hγ => hsolution γ (hsub hγ))
      (fun γ hγ => hregular γ (hsub hγ))
      (fun γ hγ => componentSeeds_on_prime Ω G T H Γ (selectedPoint φ selected) C γ hγ)
      (fun γ hγ => hagreement γ (hsub hγ))
      (noLargeSelectedPencil_mono selected Γ _ w e hsub hnoPencil) cap hcap
    exact hcount
  exact aggregate_component_incidence Ω G T H Γ (selectedPoint φ selected)
    hGpoint hTpoint hHp (a - w) nodes.card (e + 1) cap budget degree hcomponent hbudget

theorem regularComponents_degree_budget_sparse
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) Ω)
    (p : ℕ) [CharP Ω p] (hG : Irreducible G) (hproper : ¬ G ∣ T)
    (hGdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hmixed0 : coordinateMixedDegree Ω G T 0 < p)
    (hmixed2 : coordinateMixedDegree Ω G T 2 < p)
    (NG MH LG LH NZ : ℕ)
    (hNG : G.degreeOf 0 ≤ NG) (hMH : T.degreeOf 0 ≤ MH)
    (hNZ : G.degreeOf 2 ≤ NZ)
    (hNGjoint : NG ≤ LG) (hMHjoint : MH ≤ LH)
    (hGcapJoint : ∀ d ∈ G.support, d 0 + d 2 ≤ LG)
    (hTcapJoint : ∀ d ∈ T.support, d 0 + d 2 ≤ LH)
    (hsparse : MH * LG + NG * LH < p + NG * MH)
    (hswap : NZ * MH < p) :
    ∀ i, (∑ C : RegularComponent Ω G T (regularitySurface φ F),
      actualCoordinateDegree Ω C.1 i) ≤ coordinateMixedDegree Ω G T i := by
  intro i
  letI : ∀ C : RegularComponent Ω G T (regularitySurface φ F), C.1.IsPrime :=
    fun C => regularComponent_isPrime Ω G T (regularitySurface φ F) C
  fin_cases i
  · exact sum_actualCoordinateDegree_at_le Ω
      (fun C : RegularComponent Ω G T (regularitySurface φ F) => C.1)
      Subtype.val_injective 0 p G T hG
      (regularComponent_G_mem Ω G T (regularitySurface φ F))
      (regularComponent_T_mem Ω G T (regularitySurface φ F))
      hproper hGdegree hmixed0
  · let order : Fin 3 ≃ Fin 3 := Equiv.swap 0 1
    have h1 : G.degreeOf (order 1) < p := by simpa [order] using hGdegree 0
    have h2 : G.degreeOf (order 2) < p := by
      change G.degreeOf 2 < p
      exact hGdegree 2
    have hsum := sum_actualCoordinateDegree_le_original_sparse Ω
      (fun C : RegularComponent Ω G T (regularitySurface φ F) => C.1)
      order Subtype.val_injective p G T hG
      (regularComponent_G_mem Ω G T (regularitySurface φ F))
      (regularComponent_T_mem Ω G T (regularitySurface φ F))
      hproper h1 h2 NG MH LG LH NZ
      (by simpa [order] using hNG) (by simpa [order] using hMH)
      (by change G.degreeOf 2 ≤ NZ; exact hNZ) hNGjoint hMHjoint
      (by simpa [order, Equiv.swap_apply_def] using hGcapJoint)
      (by simpa [order, Equiv.swap_apply_def] using hTcapJoint) hsparse hswap
    simpa [order, coordinateMixedDegree] using hsum
  · exact sum_actualCoordinateDegree_at_le Ω
      (fun C : RegularComponent Ω G T (regularitySurface φ F) => C.1)
      Subtype.val_injective 2 p G T hG
      (regularComponent_G_mem Ω G T (regularitySurface φ F))
      (regularComponent_T_mem Ω G T (regularitySurface φ F))
      hproper hGdegree hmixed2

theorem proper_cut_seed_bound_sparse
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) Ω)
    (hG : Irreducible G) (hdiv : G ∣ surfaceMap φ F) (hproper : ¬ G ∣ T)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (hinj : Set.InjOn x nodes)
    (p w a e : ℕ) [CharP Ω p] (hw : 1 ≤ w) (hchar : w < p)
    (hwa : w < a) (han : a ≤ nodes.card)
    (hGdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hmixed0 : coordinateMixedDegree Ω G T 0 < p)
    (hmixed2 : coordinateMixedDegree Ω G T 2 < p)
    (NG MH LG LH NZ : ℕ)
    (hNG : G.degreeOf 0 ≤ NG) (hMH : T.degreeOf 0 ≤ MH)
    (hNZ : G.degreeOf 2 ≤ NZ)
    (hNGjoint : NG ≤ LG) (hMHjoint : MH ≤ LH)
    (hGcapJoint : ∀ d ∈ G.support, d 0 + d 2 ≤ LG)
    (hTcapJoint : ∀ d ∈ T.support, d 0 + d 2 ≤ LH)
    (hsparse : MH * LG + NG * LH < p + NG * MH)
    (hswap : NZ * MH < p)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0)
    (hregular : ∀ γ ∈ Γ, MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hGpoint : ∀ γ ∈ Γ, MvPolynomial.eval (selectedPoint φ selected γ) G = 0)
    (hTpoint : ∀ γ ∈ Γ, MvPolynomial.eval (selectedPoint φ selected γ) T = 0)
    (hagreement : ∀ γ ∈ Γ,
      a ≤ (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w e)
    (cap : Fin 3 → ℕ)
    (hcap : ∀ i ∈ nodes, ∀ j,
      (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j) :
    Γ.card * (a - w) ≤ nodes.card * (∑ i, cap i * coordinateMixedDegree Ω G T i) +
      (e + 1) * (a - w) * coordinateMixedDegree Ω G T 2 :=
  proper_cut_seed_bound_of_projection_sum_sparse φ F G T hG hdiv hproper selected Γ
    nodes x u₀ u₁ hinj p w a e hw hchar hwa han hGdegree hmixed0 hmixed2
    NG MH LG LH NZ hNG hMH hNZ hNGjoint hMHjoint hGcapJoint hTcapJoint hsparse hswap
    hdegree hsolution hregular hGpoint hTpoint hagreement hnoPencil cap
    (coordinateMixedDegree Ω G T) hcap
    (regularComponents_degree_budget_sparse φ F G T p hG hproper hGdegree
      hmixed0 hmixed2 NG MH LG LH NZ hNG hMH hNZ hNGjoint hMHjoint
      hGcapJoint hTcapJoint hsparse hswap)

end

end ProximityPrize.SubmissionLower.ContactProperCutSparseSeedCount

#print axioms ProximityPrize.SubmissionLower.ContactProperCutSparseSeedCount.proper_cut_seed_bound_sparse
