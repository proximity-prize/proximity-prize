import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactGlobalShearProperCutResearch
import ProximityPrize.SubmissionLower.ContactOriginalRegularSeedCount
import ProximityPrize.SubmissionLower.ContactCountingCaps6533
import ProximityPrize.SubmissionLower.ContactShearLedger6533
import ProximityPrize.SubmissionLower.ContactFullTriangleAgreement

/-!
# Agreement-first whole-surface count for the 65.67 global shear

This is the outer sharp-incidence wrapper around the characteristic-free
proper-cut theorem.  It records explicitly that the effective agreement box
is the old mixed box plus exactly `2 * capR * degreeZ`.
-/

namespace ProximityPrize.SubmissionLower.ContactGlobalShearSurfaceSeedCount6533

open scoped Classical BigOperators
open ContactParameters6533 ContactShearParameters6533 ContactShearLedger6533
open ContactGenericSurface ContactPrimeSeedIncidence ContactComponentPencils
open ContactPolynomialSolutions ContactTranslation ContactInterpolation
open ContactGlobalShearProperCutResearch ContactAdaptiveShearConditional
open ActualCoordinateDegreeSum
open ContactFullTriangleAgreement ContactTaylorNumerators

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {K Omega : Type} [Field K] [Field Omega]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega

def capAt (v : DegreeVector) : Fin 3 → ℕ := ![v.y, v.r, v.z]

def unitAt : Fin 3 → DegreeVector := ![unitY, unitR, unitZ]

def degreeVector (G : MvPolynomial (Fin 3) Omega) : DegreeVector :=
  ⟨G.degreeOf 0, G.degreeOf 1, G.degreeOf 2⟩

def HasCaps (G : MvPolynomial (Fin 3) Omega) (v : DegreeVector) : Prop :=
  ∀ i, G.degreeOf i ≤ capAt v i

theorem degreeVector_hasCaps (G : MvPolynomial (Fin 3) Omega) :
    HasCaps G (degreeVector G) := by
  intro i
  fin_cases i <;> exact le_rfl

theorem coordinateMixedDegree_le_caps
    (G T : MvPolynomial (Fin 3) Omega) (g t : DegreeVector)
    (hG : HasCaps G g) (hT : HasCaps T t) (i : Fin 3) :
    coordinateMixedDegree Omega G T i ≤ mixed g t (unitAt i) := by
  fin_cases i
  · have h := Nat.add_le_add
      (Nat.mul_le_mul (hT 1) (hG 2)) (Nat.mul_le_mul (hG 1) (hT 2))
    simpa [coordinateMixedDegree_zero, HasCaps, capAt, mixed, unitAt,
      unitY, Nat.mul_comm, Nat.add_comm] using h
  · have h := Nat.add_le_add
      (Nat.mul_le_mul (hT 0) (hG 2)) (Nat.mul_le_mul (hG 0) (hT 2))
    simpa [coordinateMixedDegree_one, HasCaps, capAt, mixed, unitAt,
      unitR, Nat.mul_comm, Nat.add_comm] using h
  · have h := Nat.add_le_add
      (Nat.mul_le_mul (hT 0) (hG 1)) (Nat.mul_le_mul (hG 0) (hT 1))
    simpa [coordinateMixedDegree_two, HasCaps, capAt, mixed, unitAt,
      unitZ, Nat.mul_comm, Nat.add_comm] using h

theorem adaptive_mixed_sum (g e : DegreeVector) :
    (∑ i : Fin 3, adaptiveShearCap (capAt e) i * mixed g e (unitAt i)) =
      mixed g e e + 2 * e.r * mixed g e unitZ := by
  simp [Fin.sum_univ_three, adaptiveShearCap, capAt, unitAt,
    mixed, unitY, unitR, unitZ]
  ring

variable [IsAlgClosed Omega]
variable (phi : Polynomial K →+* Omega)
variable {ι : Type*}
local instance : DecidableEq ι := Classical.decEq ι

/-- Agreement-first incidence using the characteristic-free global shear at
every proper agreement cut. -/
theorem whole_surface_seed_bound_global_shear
    (F : MvPolynomial (Fin 4) K) (G : MvPolynomial (Fin 3) Omega)
    (hG : Irreducible G) (hdiv : G ∣ surfaceMap phi F)
    (hr : 0 < G.degreeOf 1)
    (hHproper : ¬ G ∣ surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) F))
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset ι) (x u0 u1 : ι → K) (hinj : Set.InjOn x nodes)
    (p w agreementCount e : ℕ) [CharP Omega p] (hp : p ≠ 0)
    (hw : 1 ≤ w) (hchar : w < p)
    (hwa : w < agreementCount) (han : agreementCount ≤ nodes.card)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma,
      MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
        (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
          (phi Polynomial.X))
        (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hGpoint : ∀ gamma ∈ Gamma,
      MvPolynomial.eval (selectedPoint phi selected gamma) G = 0)
    (hagreement : ∀ gamma ∈ Gamma,
      agreementCount ≤ (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w e)
    (E : DegreeVector)
    (hcap : ∀ i ∈ nodes,
      HasCaps (agreementPolynomial phi F w (x i) (u0 i) (u1 i)) E)
    (hcapY : 1 ≤ E.y) (hcapS : 1 ≤ E.r)
    (hmixedY : ∀ i ∈ nodes,
      coordinateMixedDegree Omega G
        (agreementPolynomial phi F w (x i) (u0 i) (u1 i)) 0 < p)
    (hmixedZ : ∀ i ∈ nodes,
      coordinateMixedDegree Omega G
        (agreementPolynomial phi F w (x i) (u0 i) (u1 i)) 2 < p) :
    Gamma.card * (agreementCount - w) ^ 2 ≤
      (nodes.card - w) *
        ((nodes.card - w) *
          (mixed (degreeVector G) E E +
            2 * E.r * mixed (degreeVector G) E unitZ) +
          (e + 1) * (agreementCount - w) *
            mixed (degreeVector G) E unitZ) := by
  classical
  let P : Ideal (MvPolynomial (Fin 3) Omega) := Ideal.span {G}
  letI : P.IsPrime := Ideal.isPrime_span_singleton_of_prime hG.prime
  have hFmem : surfaceMap phi F ∈ P := Ideal.mem_span_singleton.mpr hdiv
  have hHmem : surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) F) ∉ P := by
    intro h
    exact hHproper (Ideal.mem_span_singleton.mp h)
  let identities := identityNodes phi P F nodes x u0 u1 w
  have hidentities : identities ⊆ nodes := identityNodes_subset phi P F nodes x u0 u1 w
  have hicard : identities.card ≤ w :=
    identityNodes_card_le_of_r_dependent_principal phi P F hFmem hHmem
      nodes x u0 u1 w hw hinj G rfl hr
  apply ContactSurfaceSeedCount.scaled_sharp_incidence_bound
    (fun gamma i => (selected gamma).eval (x i) = u0 i + gamma * u1 i)
    Gamma nodes identities agreementCount w
    ((nodes.card - w) *
      (mixed (degreeVector G) E E +
        2 * E.r * mixed (degreeVector G) E unitZ) +
      (e + 1) * (agreementCount - w) * mixed (degreeVector G) E unitZ)
    hidentities hicard hwa han hagreement
  intro i hi
  obtain ⟨hinode, hnotid⟩ := Finset.mem_sdiff.mp hi
  let T := agreementPolynomial phi F w (x i) (u0 i) (u1 i)
  have hproper : ¬ G ∣ T := by
    intro hd
    apply hnotid
    exact Finset.mem_filter.mpr ⟨hinode, Ideal.mem_span_singleton.mpr hd⟩
  let fiber := Gamma.filter (fun gamma =>
    (selected gamma).eval (x i) = u0 i + gamma * u1 i)
  have hsub : fiber ⊆ Gamma := Finset.filter_subset _ _
  have hTpoint : ∀ gamma ∈ fiber,
      MvPolynomial.eval (selectedPoint phi selected gamma) T = 0 := by
    intro gamma hgamma
    have hGamma := hsub hgamma
    exact (selected_agreement_zero_iff phi F selected p w hchar gamma
      (hdegree gamma hGamma) (hsolution gamma hGamma) (hregular gamma hGamma)
      (x i) (u0 i) (u1 i)).mpr (Finset.mem_filter.mp hgamma).2
  have hcount := proper_cut_seed_bound_global_shear_charfree
    phi F G T hG hdiv hproper selected fiber nodes x u0 u1 hinj
    p w agreementCount e hp hw hchar hwa han
    (fun gamma hgamma => hdegree gamma (hsub hgamma))
    (fun gamma hgamma => hsolution gamma (hsub hgamma))
    (fun gamma hgamma => hregular gamma (hsub hgamma))
    (fun gamma hgamma => hGpoint gamma (hsub hgamma)) hTpoint
    (fun gamma hgamma => hagreement gamma (hsub hgamma))
    (ContactProperCutSeedCount.noLargeSelectedPencil_mono
      selected Gamma fiber w e hsub hnoPencil)
    (capAt E) (fun j hj => hcap j hj) hcapY hcapS
    (hmixedY i hinode) (hmixedZ i hinode)
  have hdelta (j : Fin 3) : coordinateMixedDegree Omega G T j ≤
      mixed (degreeVector G) E (unitAt j) :=
    coordinateMixedDegree_le_caps G T (degreeVector G) E
      (degreeVector_hasCaps G) (hcap i hinode) j
  have hsum : (∑ j, adaptiveShearCap (capAt E) j *
      coordinateMixedDegree Omega G T j) ≤
      mixed (degreeVector G) E E +
        2 * E.r * mixed (degreeVector G) E unitZ := by
    calc
      _ ≤ ∑ j, adaptiveShearCap (capAt E) j *
          mixed (degreeVector G) E (unitAt j) :=
        Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_left _ (hdelta j))
      _ = _ := adaptive_mixed_sum (degreeVector G) E
  exact hcount.trans (Nat.add_le_add
    (Nat.mul_le_mul_left (nodes.card - w) hsum)
    (Nat.mul_le_mul_left ((e + 1) * (agreementCount - w)) (hdelta 2)))

/-- Sharp agreement caps for the 65.67 interpolating surface. -/
theorem sharp_agreement_caps
    (F : MvPolynomial (Fin 4) K)
    (hbox : F ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (hfull : MvPolynomial.weightedTotalDegree fullSurfaceWeights F ≤ seedTotalCap)
    (hY : F.degreeOf 1 ≤ yCap) (hR : F.degreeOf 2 ≤ slopeCap)
    (hZ : F.degreeOf 3 ≤ seedTotalCap) (x u0 u1 : K) :
    HasCaps (agreementPolynomial phi F w x u0 u1) sharpAgreement := by
  have hold := ContactCountingCaps.surface_agreement_caps phi F yCap slopeCap
    seedTotalCap (by norm_num [slopeCap]) hY hR hZ w
      (fun j ↦ (j.factorial : K)⁻¹) x u0 u1
  have hsharp := ContactSharpYRecurrence.sharp_Y_bounds_of_mem_box
    F weightedCap w seedTotalCap slopeCap yCap
    (by norm_num [w]) (by norm_num [yCap, weightedCap,
      ContactParameters6533.multiplicity, agreements, n, errors, w])
    (by norm_num [weightedCap, ContactParameters6533.multiplicity,
      agreements, n, errors, w, yCap]) hbox 0 w
      (fun j ↦ (j.factorial : K)⁻¹) x u0 u1
  intro i
  fin_cases i
  · have hy := (surfaceMap_degreeOf_le phi _ 0).trans hsharp.2
    simpa [agreementPolynomial, HasCaps, capAt, sharpAgreement] using hy
  · simpa [agreementPolynomial, HasCaps, capAt, sharpAgreement,
      ContactCountingCaps.agreementCaps, ContactCountingCaps.capAt] using hold 1
  · have hz : (agreementPolynomial phi F w x u0 u1).degreeOf 2 ≤
        1 + 2 * w * (seedTotalCap - 1) := by
      simpa only [agreementPolynomial] using
        (surface_agreement_seed_degree_cap_full_triangle phi F seedTotalCap w
          (by norm_num [seedTotalCap]) hfull
          (fun j ↦ (j.factorial : K)⁻¹) x u0 u1)
    simpa [agreementPolynomial, HasCaps, capAt, sharpAgreement] using hz

/-- Exact 65.67 whole-surface wrapper. -/
theorem whole_surface_seed_bound_fixed
    (F : MvPolynomial (Fin 4) K) (G : MvPolynomial (Fin 3) Omega)
    (hG : Irreducible G) (hdiv : G ∣ surfaceMap phi F)
    (hr : 0 < G.degreeOf 1)
    (hHproper : ¬ G ∣ surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) F))
    (hbox : F ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (hfull : MvPolynomial.weightedTotalDegree fullSurfaceWeights F ≤ seedTotalCap)
    (hGY : G.degreeOf 0 ≤ yCap) (hGR : G.degreeOf 1 ≤ slopeCap)
    (hGZ : G.degreeOf 2 ≤ seedTotalCap)
    (hY : F.degreeOf 1 ≤ yCap) (hR : F.degreeOf 2 ≤ slopeCap)
    (hZ : F.degreeOf 3 ≤ seedTotalCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset ι) (x u0 u1 : ι → K) (hinj : Set.InjOn x nodes)
    (hnodes : nodes.card = n) [CharP Omega prime]
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma,
      MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
        (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
          (phi Polynomial.X))
        (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hGpoint : ∀ gamma ∈ Gamma,
      MvPolynomial.eval (selectedPoint phi selected gamma) G = 0)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    Gamma.card * gap ^ 2 ≤ shearedWholeNumerator (degreeVector G) := by
  have hcap (i : ι) := sharp_agreement_caps phi F hbox hfull hY hR hZ
    (x i) (u0 i) (u1 i)
  have hmixedY (i : ι) : coordinateMixedDegree Omega G
      (agreementPolynomial phi F w (x i) (u0 i) (u1 i)) 0 < prime := by
    have hdelta := coordinateMixedDegree_le_caps G _ (degreeVector G) sharpAgreement
      (degreeVector_hasCaps G) (hcap i) 0
    have hboxMixed : mixed (degreeVector G) sharpAgreement unitY ≤
        sharpAgreementYProjection := by
      simpa [degreeVector, mixed, unitY, sharpAgreementYProjection, surfaceVector]
        using Nat.add_le_add
          (Nat.mul_le_mul_right sharpAgreement.z hGR)
          (Nat.mul_le_mul_right sharpAgreement.r hGZ)
    exact hdelta.trans_lt (hboxMixed.trans_lt
      transverse_projection_budgets_below_characteristic.1)
  have hmixedZ (i : ι) : coordinateMixedDegree Omega G
      (agreementPolynomial phi F w (x i) (u0 i) (u1 i)) 2 < prime := by
    have hdelta := coordinateMixedDegree_le_caps G _ (degreeVector G) sharpAgreement
      (degreeVector_hasCaps G) (hcap i) 2
    have hboxMixed : mixed (degreeVector G) sharpAgreement unitZ ≤
        sharpAgreementZProjection := by
      simpa [degreeVector, mixed, unitZ, sharpAgreementZProjection, surfaceVector]
        using Nat.add_le_add
          (Nat.mul_le_mul_right sharpAgreement.r hGY)
          (Nat.mul_le_mul_right sharpAgreement.y hGR)
    exact hdelta.trans_lt (hboxMixed.trans_lt
      transverse_projection_budgets_below_characteristic.2)
  have hcount := whole_surface_seed_bound_global_shear phi F G hG hdiv hr hHproper
    selected Gamma nodes x u0 u1 hinj prime w agreements errors
    (by norm_num [prime]) (by norm_num [w]) (by norm_num [w, prime])
    (by norm_num [w, agreements, n, errors])
    (by rw [hnodes]; norm_num [agreements, n, errors])
    hdegree hsolution hregular hGpoint hagreement hnoPencil sharpAgreement
    (fun i _ => hcap i)
    (by norm_num [sharpAgreement, yCap, weightedCap,
      ContactParameters6533.multiplicity, agreements, n, errors, w])
    (by norm_num [sharpAgreement, w, slopeCap])
    (fun i _ => hmixedY i) (fun i _ => hmixedZ i)
  rw [hnodes] at hcount
  calc
    Gamma.card * gap ^ 2 = Gamma.card * (agreements - w) ^ 2 := rfl
    _ ≤ (n - w) * ((n - w) *
        (mixed (degreeVector G) sharpAgreement sharpAgreement +
          2 * sharpAgreement.r * mixed (degreeVector G) sharpAgreement unitZ) +
        (errors + 1) * (agreements - w) *
          mixed (degreeVector G) sharpAgreement unitZ) := hcount
    _ = shearedWholeNumerator (degreeVector G) := by
      simp only [shearedWholeNumerator, gap]
      ring

end
end ProximityPrize.SubmissionLower.ContactGlobalShearSurfaceSeedCount6533

#print axioms ProximityPrize.SubmissionLower.ContactGlobalShearSurfaceSeedCount6533.whole_surface_seed_bound_global_shear
#print axioms ProximityPrize.SubmissionLower.ContactGlobalShearSurfaceSeedCount6533.sharp_agreement_caps
#print axioms ProximityPrize.SubmissionLower.ContactGlobalShearSurfaceSeedCount6533.whole_surface_seed_bound_fixed
