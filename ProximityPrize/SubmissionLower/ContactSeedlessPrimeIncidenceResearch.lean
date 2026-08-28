import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactProperCutSeedCount
import ProximityPrize.SubmissionLower.ContactIdentityResidualSurfaceResearch

/-! .








 -/

namespace ProximityPrize.SubmissionLower.ContactSeedlessPrimeIncidenceResearch

open scoped Classical BigOperators
open ActualCurveCoordinateField ActualCurveZeroCount ActualCurveProjectionBounds
open ActualCoordinateDegreeSum ActualPlanePositiveOrder
open ContactGenericSurface ContactPolynomialSolutions ContactPolynomialRecovery
open ContactComponentPencils ContactPrimeSeedIncidence ContactIncidence
open ContactRegularComponentCover ContactProperCutSeedCount ContactTranslation
open ContactIdentityResidualSurfaceResearch

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

variable {K Omega : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable (phi : Polynomial K →+* Omega)

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega

def seedlessPoint (S : Polynomial K) : Fin 3 → Omega :=
  fun i => polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X) i.succ

theorem seedlessPoint_value (S : Polynomial K) :
    seedlessPoint phi S = ![phi S, phi S.derivative, 0] := by
  funext i
  fin_cases i <;>
    simp [seedlessPoint, polynomialPoint, polynomial_eval₂_comp_C_X]

theorem seedlessPoint_injective (hphi : Function.Injective phi) :
    Function.Injective (seedlessPoint phi) := by
  intro S T h
  apply hphi
  have h0 := congrFun h (0 : Fin 3)
  simpa only [seedlessPoint_value, Matrix.cons_val_zero] using h0

theorem seedlessPoint_surface_evaluation (S : Polynomial K)
    (Q : MvPolynomial (Fin 4) K) :
    MvPolynomial.eval (seedlessPoint phi S) (surfaceMap phi Q) =
      MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
        (polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X)) Q := by
  rw [eval_surfaceMap]
  have hv : Fin.cases (phi Polynomial.X) (seedlessPoint phi S) =
      polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X) := by
    funext i
    fin_cases i <;> rfl
  rw [hv]

theorem seedless_agreement_zero_iff
    (F : MvPolynomial (Fin 4) K) (S : Polynomial K)
    (p w : ℕ) [CharP Omega p] (hchar : w < p)
    (hdegree : S.natDegree ≤ w)
    (hsolution : specialization K S 0 F = 0)
    (hregular : MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
      (polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (x u : K) :
    MvPolynomial.aeval (seedlessPoint phi S)
      (agreementPolynomial phi F w x u 0) = 0 ↔ S.eval x = u := by
  have hpoint : seedlessPoint phi S = selectedPoint phi (fun _ : K => S) 0 := rfl
  rw [hpoint]
  simpa only [zero_mul, add_zero] using
    (selected_agreement_zero_iff phi F (fun _ : K => S) p w hchar 0
      hdegree hsolution hregular x u 0)

variable (P : Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]

theorem seedless_agreement_fiber_card_le
    (hphi : Function.Injective phi)
    (hproj : ProjectionsFiniteSeparable Omega P)
    (hnonpoint : ∀ v : Fin 3 → Omega,
      P ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (F : MvPolynomial (Fin 4) K) (Gamma : Finset (Polynomial K))
    (p w : ℕ) [CharP Omega p] (hchar : w < p)
    (hdegree : ∀ S ∈ Gamma, S.natDegree ≤ w)
    (hsolution : ∀ S ∈ Gamma, specialization K S 0 F = 0)
    (hregular : ∀ S ∈ Gamma, MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
      (polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hpoint : ∀ S ∈ Gamma, P ≤ RingHom.ker
      (MvPolynomial.aeval (seedlessPoint phi S)).toRingHom)
    (x u : K) (hproper : agreementPolynomial phi F w x u 0 ∉ P)
    (cap : Fin 3 → ℕ)
    (hcap : ∀ j, (agreementPolynomial phi F w x u 0).degreeOf j ≤ cap j) :
    (Gamma.filter (fun S => S.eval x = u)).card ≤ componentCost P cap := by
  classical
  let fiber := Gamma.filter (fun S => S.eval x = u)
  let points := fiber.image (seedlessPoint phi)
  have hpointsP : ∀ v ∈ points,
      P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom := by
    intro v hv
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hv
    exact hpoint S (Finset.mem_filter.mp hS).1
  have hpointsF : ∀ v ∈ points,
      MvPolynomial.aeval v (agreementPolynomial phi F w x u 0) = 0 := by
    intro v hv
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hGamma, hagree⟩ := Finset.mem_filter.mp hS
    exact (seedless_agreement_zero_iff phi F S p w hchar
      (hdegree S hGamma) (hsolution S hGamma) (hregular S hGamma) x u).mpr hagree
  have hcount := ActualCurveZeroCount.finite_zero_points_le_box Omega P hproj
    hnonpoint (agreementPolynomial phi F w x u 0) hproper cap hcap
    points hpointsP hpointsF
  have hcard : points.card = fiber.card :=
    Finset.card_image_of_injective _ (seedlessPoint_injective phi hphi)
  rw [hcard] at hcount
  unfold componentCost
  exact_mod_cast hcount

theorem coordinate_two_eq_zero (hZ : MvPolynomial.X (2 : Fin 3) ∈ P) :
    coordinate Omega P 2 = 0 := by
  change coordinateEvaluation Omega P (MvPolynomial.X (2 : Fin 3)) = 0
  change MvPolynomial.X (2 : Fin 3) ∈
    RingHom.ker (coordinateEvaluation Omega P).toRingHom
  rwa [coordinateEvaluation_ker]

theorem identityNodes_card_le_of_seedless_cut
    (F : MvPolynomial (Fin 4) K)
    (hF : surfaceMap phi F ∈ P)
    (hH : surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) F) ∉ P)
    (hZ : MvPolynomial.X (2 : Fin 3) ∈ P)
    {Iota : Type} (nodes : Finset Iota) (x u : Iota → K)
    (w : ℕ) (hw : 1 ≤ w) (hinj : Set.InjOn x nodes)
    (hnonpoint : ∀ v : Fin 3 → Omega,
      P ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom) :
    (identityNodes phi P F nodes x u (fun _ => 0) w).card ≤ w := by
  classical
  by_contra hnot
  have hmany : w < (identityNodes phi P F nodes x u (fun _ => 0) w).card :=
    Nat.lt_of_not_ge hnot
  have htrans := seed_transcendental_of_many_identities phi P F hF hH
    nodes x u (fun _ => 0) w hw hinj hmany hnonpoint
  have hz0 := coordinate_two_eq_zero P hZ
  rw [hz0] at htrans
  exact htrans isAlgebraic_zero

variable {Iota : Type}
local instance : DecidableEq Iota := Classical.decEq Iota

/-- .

 -/
theorem seedless_prime_incidence
    (hphi : Function.Injective phi)
    (hproj : ProjectionsFiniteSeparable Omega P)
    (hnonpoint : ∀ v : Fin 3 → Omega,
      P ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (F : MvPolynomial (Fin 4) K)
    (hF : surfaceMap phi F ∈ P)
    (hH : surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) F) ∉ P)
    (hZ : MvPolynomial.X (2 : Fin 3) ∈ P)
    (Gamma : Finset (Polynomial K))
    (nodes : Finset Iota) (x u : Iota → K) (hinj : Set.InjOn x nodes)
    (p w a : ℕ) [CharP Omega p] (hw : 1 ≤ w) (hchar : w < p)
    (hwa : w < a) (han : a ≤ nodes.card)
    (hdegree : ∀ S ∈ Gamma, S.natDegree ≤ w)
    (hsolution : ∀ S ∈ Gamma, specialization K S 0 F = 0)
    (hregular : ∀ S ∈ Gamma, MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
      (polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hpoint : ∀ S ∈ Gamma, P ≤ RingHom.ker
      (MvPolynomial.aeval (seedlessPoint phi S)).toRingHom)
    (hagreement : ∀ S ∈ Gamma,
      a ≤ (nodes.filter (fun i => S.eval (x i) = u i)).card)
    (cap : Fin 3 → ℕ)
    (hcap : ∀ i ∈ nodes, ∀ j,
      (agreementPolynomial phi F w (x i) (u i) 0).degreeOf j ≤ cap j) :
    Gamma.card * (a - w) ≤ (nodes.card - w) * componentCost P cap := by
  classical
  let I := identityNodes phi P F nodes x u (fun _ => 0) w
  let relation : Polynomial K → Iota → Prop := fun S i => S.eval (x i) = u i
  have hI : I.card ≤ w := identityNodes_card_le_of_seedless_cut phi P F hF hH
    hZ nodes x u w hw hinj hnonpoint
  have hfiber : ∀ i ∈ nodes \ I,
      (Gamma.filter (fun S => relation S i)).card ≤ componentCost P cap := by
    intro i hi
    obtain ⟨hinodes, hnotI⟩ := Finset.mem_sdiff.mp hi
    have hproper : agreementPolynomial phi F w (x i) (u i) 0 ∉ P := by
      intro hmem
      apply hnotI
      exact Finset.mem_filter.mpr ⟨hinodes, hmem⟩
    exact seedless_agreement_fiber_card_le phi P hphi hproj hnonpoint F Gamma
      p w hchar hdegree hsolution hregular hpoint (x i) (u i) hproper cap
      (hcap i hinodes)
  exact sharp_incidence_bound relation Gamma nodes I a w (componentCost P cap)
    (identityNodes_subset phi P F nodes x u (fun _ => 0) w) hI hwa han
    hagreement hfiber

end

end ProximityPrize.SubmissionLower.ContactSeedlessPrimeIncidenceResearch
