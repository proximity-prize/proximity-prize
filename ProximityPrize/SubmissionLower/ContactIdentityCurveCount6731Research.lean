import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactCoefficientPole6731Research
import ProximityPrize.SubmissionLower.ContactPrimeSeedIncidence
namespace ProximityPrize.SubmissionLower.ContactIdentityCurveCount6731Research
open scoped Classical BigOperators
open ActualCurveCoordinateField ContactGenericSurface ContactPolynomialSolutions
open ContactTranslation ContactPrimeSeedIncidence ContactComponentPencils
open ContactRegularZeroBudget6676Research ContactCoefficientPole6731Research
open ContactWeakSeparableSeparatorResearch CoordinateBoxZeroCount
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 300000
variable {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
variable (φ:Polynomial K →+*Ω) (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
variable (F:MvPolynomial (Fin 4) K)
variable (hF:surfaceMap φ F∈P)
variable (hH:surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)∉P)
theorem prime_curve_card_le_of_coefficientPoleProfile
    (base:SeparableLiteralCoordinate P) (p w a e cost:ℕ) [CharP Ω p]
    (hchar:w < p) (hwa:w < a) (hcost:1 ≤ cost)
    (hprofile:CoefficientPoleProfile φ P F hF hH w cost)
    (selected:K → Polynomial K) (Γ:Finset K)
    {ι:Type*} (nodes:Finset ι) (x u0 u1:ι → K) (hinj:Set.InjOn x nodes)
    (hsize:nodes.card=a+e)
    (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
    (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
    (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
      (MvPolynomial.pderiv (2:Fin 4) F)≠0)
    (hpoint:∀ γ∈Γ,P ≤ RingHom.ker (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
    (hagreement:∀ γ∈Γ,a ≤ (nodes.filter (fun i↦
      (selected γ).eval (x i)=u0 i+γ*u1 i)).card)
    (hnoPencil:NoLargeSelectedPencil selected Γ w e):Γ.card ≤ (e+1)*cost:=by
  classical
  letI:DecidableEq ι:=Classical.decEq ι
  let I:=identityNodes φ P F nodes x u0 u1 w
  let relation:K → ι → Prop:=fun γ i↦(selected γ).eval (x i)=u0 i+γ*u1 i
  by_cases hI:I.card ≤ w
  · have hfiber:∀ i∈nodes \ I,(Γ.filter (fun γ↦relation γ i)).card ≤ cost:=by
      intro i hi
      obtain ⟨hinodes,hnotI⟩:=Finset.mem_sdiff.mp hi
      have hproper:agreementPolynomial φ F w (x i) (u0 i) (u1 i)∉P:=by
        intro hmem
        apply hnotI
        exact Finset.mem_filter.mpr ⟨hinodes,hmem⟩
      exact agreement_fiber_card_le_of_regular_zero_bound φ P F selected Γ p w hchar
        hdegree hsolution hregular hpoint (x i) (u0 i) (u1 i) cost
        (agreement_regular_zero_le φ P F hF hH base w cost hprofile _ _ _ hproper)
    have hcount:=ContactIncidence.sharp_incidence_bound relation Γ nodes I a w cost
      (identityNodes_subset φ P F nodes x u0 u1 w) hI hwa (by omega) hagreement hfiber
    have hg:0 < a-w:=Nat.sub_pos_of_lt hwa
    have hu:nodes.card-w ≤ (e+1)*(a-w):=by
      have he:=Nat.mul_le_mul_left e (show 1 ≤ a-w by omega)
      calc
        nodes.card-w=(a-w)+e:=by omega
        _ ≤ (a-w)+e*(a-w):=by simpa only [Nat.mul_one] using Nat.add_le_add_left he (a-w)
        _=_:=by ring
    have hscaled:Γ.card*(a-w) ≤ ((e+1)*cost)*(a-w):=by
      calc
        _ ≤ (nodes.card-w)*cost:=hcount
        _ ≤ ((e+1)*(a-w))*cost:=Nat.mul_le_mul_right cost hu
        _=_:=by ring
    exact Nat.le_of_mul_le_mul_right hscaled hg
  · have hi:w < I.card:=Nat.lt_of_not_ge hI
    have hvalues:∀ (t:{γ:K//γ∈Γ}) i,i∈I →
        (selected t.1).eval (x i)=u0 i+t.1*u1 i:=by
      intro t
      exact selected_agrees_on_identity_nodes φ P F nodes x u0 u1 p w hchar
        (selected t.1) t.1 (hdegree t.1 t.2) (hsolution t.1 t.2)
        (hregular t.1 t.2) (hpoint t.1 t.2)
    obtain ⟨P0,P1,h0,h1,_,hpencil⟩:=exists_common_pencil_of_many_identities
      φ P F hF hH nodes x u0 u1 w hinj hi
      (fun t:{γ:K//γ∈Γ}↦t.1) (fun t↦selected t.1)
      (fun t↦hdegree t.1 t.2) hvalues
    have hfilter:Γ.filter (fun γ↦selected γ=P0+Polynomial.C γ*P1)=Γ:=
      Finset.filter_eq_self.mpr (fun γ hγ↦hpencil ⟨γ,hγ⟩)
    have hsmall:Γ.card ≤ e+1:=by
      simpa only [hfilter] using hnoPencil P0 P1 h0 h1
    exact hsmall.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (e+1) hcost)
theorem prime_curve_card_le_projection_degree
    (base:SeparableLiteralCoordinate P) (J:SeparableCoordinate Ω (CoordinateField Ω P))
    (p w a e:ℕ) [CharP Ω p] (hchar:w < p) (hwa:w < a)
    (hprofile:CoefficientPoleProfile φ P F hF hH w
      (SeparableCoordinate.degree Ω (CoordinateField Ω P) J))
    (selected:K → Polynomial K) (Γ:Finset K)
    {ι:Type*} (nodes:Finset ι) (x u0 u1:ι → K) (hinj:Set.InjOn x nodes)
    (hsize:nodes.card=a+e)
    (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
    (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
    (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
      (MvPolynomial.pderiv (2:Fin 4) F)≠0)
    (hpoint:∀ γ∈Γ,P ≤ RingHom.ker (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
    (hagreement:∀ γ∈Γ,a ≤ (nodes.filter (fun i↦
      (selected γ).eval (x i)=u0 i+γ*u1 i)).card)
    (hnoPencil:NoLargeSelectedPencil selected Γ w e):
    Γ.card ≤ (e+1)*SeparableCoordinate.degree Ω (CoordinateField Ω P) J:=by
  have hcost:1 ≤ SeparableCoordinate.degree Ω (CoordinateField Ω P) J:=by
    letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=J.embedding.toRingHom.toAlgebra
    letI:FiniteDimensional (RatFunc Ω) (CoordinateField Ω P):=J.finite
    exact Module.finrank_pos
  exact prime_curve_card_le_of_coefficientPoleProfile φ P F hF hH base p w a e _
    hchar hwa hcost hprofile selected Γ nodes x u0 u1 hinj hsize hdegree hsolution hregular
    hpoint hagreement hnoPencil
end
end ProximityPrize.SubmissionLower.ContactIdentityCurveCount6731Research
