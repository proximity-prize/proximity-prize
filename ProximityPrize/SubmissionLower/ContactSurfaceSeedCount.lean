import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactProperCutSeedCount
import ProximityPrize.SubmissionLower.ContactCountingCaps

/-!
# Every regular positive-R surface is counted by agreement-first cuts

Model label: gpt-5.

An irreducible regular positive-R surface has at most w identity agreement
nodes, without any first-tail or all-tail assumption. Each nonidentity
agreement equation is a genuine proper cut. The actual proper-cut theorem
bounds its selected-seed fiber; sharp finite incidence then counts the
entire surface. The cost is linear in the ACTUAL surface-factor degrees.

The fixed-witness wrapper concludes exactly wholeNumerator of those
degrees. It does not replace every factor by the entire interpolant's cap.
-/

namespace ProximityPrize.SubmissionLower.ContactSurfaceSeedCount

open scoped Classical BigOperators
open ContactAlignmentParameters ContactCountingCaps ContactGenericSurface
open ContactPrimeSeedIncidence ContactProperCutSeedCount ContactComponentPencils
open ContactPolynomialSolutions ContactTranslation ActualCoordinateDegreeSum

noncomputable section

variable {K Ω : Type} [Field K] [Field Ω]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Ω := Classical.decEq Ω

def unitAt : Fin 3 → DegreeVector := ![unitY, unitR, unitZ]

def degreeVector (G : MvPolynomial (Fin 3) Ω) : DegreeVector :=
  ⟨G.degreeOf 0, G.degreeOf 1, G.degreeOf 2⟩

theorem degreeVector_hasCaps (G : MvPolynomial (Fin 3) Ω) :
    HasCaps G (degreeVector G) := by
  intro i
  fin_cases i <;> exact le_rfl

theorem coordinateMixedDegree_le_caps
    (G T : MvPolynomial (Fin 3) Ω) (g t : DegreeVector)
    (hG : HasCaps G g) (hT : HasCaps T t) (i : Fin 3) :
    coordinateMixedDegree Ω G T i ≤ mixed g t (unitAt i) := by
  fin_cases i
  · simpa [unitAt, capAt, mixed, unitY, Nat.mul_comm, Nat.add_comm] using
      actual_pair_degree_le G T g t hG hT 1 2
  · simpa [unitAt, capAt, mixed, unitR, Nat.mul_comm, Nat.add_comm] using
      actual_pair_degree_le G T g t hG hT 0 2
  · simpa [unitAt, capAt, mixed, unitZ, Nat.mul_comm, Nat.add_comm] using
      actual_pair_degree_le G T g t hG hT 0 1

theorem mixed_cap_sum (g t e : DegreeVector) :
    (∑ i : Fin 3, capAt e i * mixed g t (unitAt i)) = mixed g t e := by
  simp [Fin.sum_univ_three, capAt, unitAt, mixed, unitY, unitR, unitZ]
  ring

def fiberNumerator (n w a e : ℕ) (g E : DegreeVector) : ℕ :=
  n * mixed g E E + (e + 1) * (a - w) * mixed g E unitZ

/-- The integer floor in a scaled fiber bound introduces no loss in the
cross-multiplied sharp-incidence conclusion. -/
theorem scaled_sharp_incidence_bound
    {Seed Node : Type*} [DecidableEq Seed] [DecidableEq Node]
    (relation : Seed → Node → Prop) [∀ seed node, Decidable (relation seed node)]
    (seeds : Finset Seed) (nodes identities : Finset Node) (a w M : ℕ)
    (hidentities : identities ⊆ nodes) (hcard : identities.card ≤ w)
    (hwa : w < a) (han : a ≤ nodes.card)
    (hagreement : ∀ seed ∈ seeds, a ≤ (nodes.filter (relation seed)).card)
    (hfiber : ∀ node ∈ nodes \ identities,
      (seeds.filter (fun seed => relation seed node)).card * (a - w) ≤ M) :
    seeds.card * (a - w) ^ 2 ≤ (nodes.card - w) * M := by
  have hcount := ContactIncidence.sharp_incidence_bound relation seeds nodes identities
    a w (M / (a - w)) hidentities hcard hwa han hagreement
    (fun node hnode => (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hwa)).mpr
      (hfiber node hnode))
  calc
    seeds.card * (a - w) ^ 2 = (seeds.card * (a - w)) * (a - w) := by ring
    _ ≤ ((nodes.card - w) * (M / (a - w))) * (a - w) :=
      Nat.mul_le_mul_right _ hcount
    _ = (nodes.card - w) * ((M / (a - w)) * (a - w)) := Nat.mul_assoc _ _ _
    _ ≤ (nodes.card - w) * M :=
      Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)

variable [IsAlgClosed Ω]
variable (φ : Polynomial K →+* Ω)
variable {ι : Type*}
local instance : DecidableEq ι := Classical.decEq ι

/-- Agreement-first incidence counts ANY regular positive-R geometric
factor. No Taylor-tail equation or assumed curve-count inequality occurs
among the inputs. All cut costs use the actual degrees of G. -/
theorem whole_surface_seed_bound
    (F : MvPolynomial (Fin 4) K) (G : MvPolynomial (Fin 3) Ω)
    (hG : Irreducible G) (hdiv : G ∣ surfaceMap φ F)
    (hr : 0 < G.degreeOf 1)
    (hHproper : ¬ G ∣ surfaceMap φ (MvPolynomial.pderiv (2 : Fin 4) F))
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (hinj : Set.InjOn x nodes)
    (p w a e : ℕ) [CharP Ω p] (hw : 1 ≤ w) (hchar : w < p)
    (hwa : w < a) (han : a ≤ nodes.card)
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
      (nodes.card - w) *
        fiberNumerator (nodes.card - w) w a e (degreeVector G) E := by
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
    Γ nodes identities a w
      (fiberNumerator (nodes.card - w) w a e (degreeVector G) E)
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
  have hcount := proper_cut_seed_bound φ F G T hG hdiv hproper selected fiber
    nodes x u₀ u₁ hinj p w a e hw hchar hwa han
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

/-- Exact fixed-witness interface for factor summation: the right side
is linear in this geometric factor's own Y/R/Z degrees. The full surface
cap is used only to justify the strict characteristic gates. -/
theorem whole_surface_seed_bound_fixed
    (F : MvPolynomial (Fin 4) K) (G : MvPolynomial (Fin 3) Ω)
    (hG : Irreducible G) (hdiv : G ∣ surfaceMap φ F)
    (hr : 0 < G.degreeOf 1)
    (hHproper : ¬ G ∣ surfaceMap φ (MvPolynomial.pderiv (2 : Fin 4) F))
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
      agreements ≤ (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w errors) :
    Γ.card * gap ^ 2 ≤ wholeNumerator (degreeVector G) := by
  have hcap (i : ι) : HasCaps (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i))
      agreementVector := fixed_agreement_caps φ F hY hR hZ hHY (x i) (u₀ i) (u₁ i)
  have hcount := whole_surface_seed_bound φ F G hG hdiv hr hHproper selected Γ
    nodes x u₀ u₁ hinj prime w agreements errors
    (by norm_num [w]) (by norm_num [w, prime]) (by norm_num [w, agreements])
    (by rw [hnodes]; norm_num [agreements, n])
    hdegree hsolution hregular hGpoint hagreement hnoPencil agreementVector (fun i _ => hcap i)
  calc
    Γ.card * gap ^ 2 = Γ.card * (agreements - w) ^ 2 := rfl
    _ ≤ (nodes.card - w) * fiberNumerator (nodes.card - w) w agreements errors
        (degreeVector G) agreementVector := hcount
    _ = wholeNumerator (degreeVector G) := by
      rw [hnodes]
      unfold fiberNumerator wholeNumerator gap
      ring

end

end ProximityPrize.SubmissionLower.ContactSurfaceSeedCount

#print axioms ProximityPrize.SubmissionLower.ContactSurfaceSeedCount.coordinateMixedDegree_le_caps
#print axioms ProximityPrize.SubmissionLower.ContactSurfaceSeedCount.mixed_cap_sum
#print axioms ProximityPrize.SubmissionLower.ContactSurfaceSeedCount.scaled_sharp_incidence_bound
#print axioms ProximityPrize.SubmissionLower.ContactSurfaceSeedCount.whole_surface_seed_bound
#print axioms ProximityPrize.SubmissionLower.ContactSurfaceSeedCount.whole_surface_seed_bound_fixed
