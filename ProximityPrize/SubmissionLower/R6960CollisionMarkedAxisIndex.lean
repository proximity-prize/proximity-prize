import ProximityPrize.SubmissionLower.R6960CollisionMarkedCommonAxis
import ProximityPrize.SubmissionLower.R6960ChartIntegrality
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Squarefree.Basic
import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxisField

set_option Elab.async false

-- merged module R6960CollisionMarkedInfinitySeeds
section Merged_R6960CollisionMarkedInfinitySeeds
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open Algebra Polynomial NormalizedFiber Module CollisionTame UniqueFactorizationMonoid
open scoped Polynomial TensorProduct
variable {k : Type} [Field k] [DecidableEq k]
theorem branch_squarefree (P:(Polynomial (Polynomial k))) : Squarefree (branchProduct P) := by
  let S := branchFactors P
  have eq : branchProduct P=S.val.prod := by
    calc branchProduct P = ∏ i∈S,i := Finset.prod_coe_sort S id
         _ = S.val.prod := by simp only [Finset.prod,Multiset.map_id']
  have nz : branchProduct P≠0 := Finset.prod_ne_zero_iff.mpr fun i _=>(branchFactor_prime P i).ne_zero
  apply (squarefree_iff_nodup_normalizedFactors nz).mpr
  rw [eq,normalizedFactors_prod_eq _ (fun x hx=>irreducible_of_normalized_factor x
    (Multiset.mem_toFinset.mp (show x∈S from hx)))]
  have norm : S.val.map normalize=S.val := by
    calc S.val.map normalize = S.val.map id :=
           Multiset.map_congr rfl fun x hx=>normalize_normalized_factor x
             (Multiset.mem_toFinset.mp (show x∈S from hx))
         _ = S.val := Multiset.map_id' _
  rw [norm]
  exact S.nodup
theorem branch_dvd (P:(Polynomial (Polynomial k))) (nz:P≠0) : branchProduct P∣P := by
  apply Dvd.dvd.trans _ (branch_weighted_product P nz).dvd
  apply Finset.prod_dvd_prod_of_dvd
  intro i _
  exact dvd_pow_self _ (branch_weight_pos P i).ne'
private theorem map_trailing {A B:Type*} [Semiring A] [Semiring B] [Nontrivial B]
    (j:A→+*B) (p:(Polynomial A)) (keep:j p.trailingCoeff≠0) :
    p.map j≠0 ∧ (p.map j).natTrailingDegree=p.natTrailingDegree := by
  have c : (p.map j).coeff p.natTrailingDegree≠0 := by
    rw [coeff_map]
    exact keep
  have n : p.map j≠0 := by intro h; rw [h,coeff_zero] at c; exact c rfl
  refine ⟨n,le_antisymm (natTrailingDegree_le_of_ne_zero c) ?_⟩
  by_contra! lt
  have h : p.coeff (p.map j).natTrailingDegree=0 := coeff_eq_zero_of_lt_natTrailingDegree lt
  exact (coeff_natTrailingDegree_ne_zero.mpr n) (by rw [coeff_map,h,map_zero])
theorem boundary_seed_polynomial (δ : Plane k) (nz : δ≠0) :
    let avoid := (Bivariate.swap δ).trailingCoeff
    avoid≠0 ∧ avoid.natDegree≤δ.natDegree ∧
      ∀ z:k, avoid.eval z≠0 →
        ((branchProduct (Bivariate.swap δ)).map (evalRingHom z))≠0 ∧
        ((branchProduct (Bivariate.swap δ)).map (evalRingHom z)).rootMultiplicity 0≤1 := by
  let P := Bivariate.swap δ
  have np : P≠0 := (map_ne_zero_iff Bivariate.swap.toRingHom Bivariate.swap.injective).mpr nz
  have degree : P.trailingCoeff.natDegree≤δ.natDegree := by
    have h := CurvatureSquares.coeff_height P P.natTrailingDegree
    change P.trailingCoeff.natDegree≤(Bivariate.swap (Bivariate.swap δ)).natDegree at h
    rwa [Bivariate.swap_swap_apply] at h
  refine ⟨coeff_natTrailingDegree_ne_zero.mpr np,degree,?_⟩
  intro z keep
  let B := branchProduct P
  let j := evalRingHom z
  obtain ⟨Q,eq⟩ := branch_dvd P np
  have keepB : j B.trailingCoeff≠0 := by
    intro zero
    change j P.trailingCoeff≠0 at keep
    apply keep
    rw [eq,trailingCoeff_mul,map_mul,zero,zero_mul]
  obtain ⟨good,tr⟩ := map_trailing j B keepB
  refine ⟨good,?_⟩
  rw [rootMultiplicity_eq_natTrailingDegree',tr]
  by_contra! large
  have div : (Polynomial.X:(Polynomial (Polynomial k)))^2∣B :=
    X_pow_dvd_iff.mpr fun i hi=>coeff_eq_zero_of_lt_natTrailingDegree (hi.trans_le large)
  exact (irreducible_X.not_isUnit) ((branch_squarefree P) _ (by simpa only [pow_two] using div))
#print axioms boundary_seed_polynomial
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedInfinitySeeds

-- merged module R6960CollisionMarkedInfinityIndex
section Merged_R6960CollisionMarkedInfinityIndex
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open Algebra Polynomial NormalizedFiber Module CollisionTame UniqueFactorizationMonoid
open scoped Polynomial TensorProduct Lower6960.CollisionMarked
variable {k : Type} [Field k] [DecidableEq k]
variable {E : Type} [Field E] [Algebra (Plane k) E]
  [Algebra (FractionRing (Plane k)) E] [IsScalarTower (Plane k) (FractionRing (Plane k)) E]
  [FiniteDimensional (FractionRing (Plane k)) E] [Algebra.IsSeparable (FractionRing (Plane k)) E]
local instance infinityFibreRing (z:k) : CommRing (Fiber E z) :=
  @Ideal.Quotient.commRing (↥(Order k E)) ((Order k E).toCommRing) (sliceIdeal E z)
theorem boundary_index (p : ℕ) [CharP k p] [CharP (FractionRing (Polynomial k)) p]
    (small : finrank (FractionRing (Plane k)) E<p)
    (δ:Plane k) (nz:δ≠0)
    (principal : normalizationDiscriminant (A:=Plane k) (E:=E) (FractionRing (Plane k))=Ideal.span {δ})
    (z:k) [IsReduced (FibreGeneric (E:=E) z)]
    (keep : (Bivariate.swap δ).trailingCoeff.eval z≠0) :
    ∃ d:(Polynomial k), d.eval 0≠0 ∧
      ∀ v:FibreGeneric (E:=E) z, IsIntegral (Polynomial k) v →
        ∃ u:Fiber E z,(1 ⊗ₜ[(Polynomial k)] u : FibreGeneric (E:=E) z)=algebraMap (Polynomial k) (FibreGeneric (E:=E) z) d*v := by
  obtain ⟨_,_,test⟩ := boundary_seed_polynomial δ nz
  obtain ⟨_,small0⟩ := test z keep
  obtain ⟨_,d,dn,_,support,clear⟩ := fibre_index_supported p small z δ nz principal
  refine ⟨d,?_,clear⟩
  intro zero
  have bad := support 0 ((mem_roots dn).mpr zero)
  omega
#print axioms boundary_index
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedInfinityIndex

-- merged module R6960CollisionMarkedAxisIndex
section Merged_R6960CollisionMarkedAxisIndex
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4500000
set_option synthInstance.maxHeartbeats 95000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open MonicChart (ChartField)
open NormalizedFiber RetainedSurfaceClass LineEuler Polynomial Algebra CollisionTame Module
open scoped Lower6960.CollisionMarked Lower6960.RetainedSurfaceClass Polynomial TensorProduct
variable {E : Type} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E]
  [Algebra.IsSeparable ChartField E]
local instance indexedAxisRing (z:L) : CommRing (Axis E true z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E true z)
local instance indexedFibreRing [Algebra (Plane L) E] (z:L) : CommRing (Fiber E z) :=
  @Ideal.Quotient.commRing (↥(Order L E)) ((Order L E).toCommRing) (sliceIdeal E z)
theorem axisFractionFinite (b:Bool) :
    let : Algebra (FractionRing (Plane L)) E := axisFractionAlgebra b
    FiniteDimensional (FractionRing (Plane L)) E := by
  let : Algebra (FractionRing (Plane L)) E := axisFractionAlgebra b
  exact Module.Finite.of_basis (axisFractionBasis (E:=E) b (Module.finBasis ChartField E)).val
theorem axisFractionRank (b:Bool) :
    let : Algebra (FractionRing (Plane L)) E := axisFractionAlgebra b
    finrank (FractionRing (Plane L)) E = finrank ChartField E := by
  let : Algebra (FractionRing (Plane L)) E := axisFractionAlgebra b
  exact (finrank_eq_card_basis (axisFractionBasis (E:=E) b (Module.finBasis ChartField E)).val).trans
    (Fintype.card_fin _)
def axisDiscriminant (b:Bool) : Ideal (Plane L) :=
  let : Algebra (Plane L) E := axisPlaneAlgebra b
  let : Algebra (FractionRing (Plane L)) E := axisFractionAlgebra b
  let : SMul (Plane L) (FractionRing (Plane L)) :=
    (inferInstance : Algebra (Plane L) (FractionRing (Plane L))).toSMul
  let : IsScalarTower (Plane L) (FractionRing (Plane L)) E := axisPlaneTower b
  let : FiniteDimensional (FractionRing (Plane L)) E := axisFractionFinite b
  let : Algebra.IsSeparable (FractionRing (Plane L)) E := axisFraction_separable b
  normalizationDiscriminant (A:=Plane L) (E:=E) (FractionRing (Plane L))
omit [Algebra.IsSeparable ChartField E] in
private theorem reducedOnChart (b:Bool) (z:L) (nz:z≠0) [IsReduced (AxisGeneric (E:=E) z)] :
    let : Algebra (Plane L) E := axisPlaneAlgebra b
    IsReduced (FibreGeneric (E:=E) z) := by
  let : Algebra (Plane L) E := axisPlaneAlgebra b
  let g := (axisGenericData (E:=E) b z nz).val
  constructor
  intro x hx
  apply g.injective
  rw [map_zero]
  exact IsReduced.eq_zero _ (hx.map g.toRingHom)
omit [Algebra.IsSeparable ChartField E] in
private theorem chartClear (b:Bool) (z:L) (nz:z≠0)
    (d:(Polynomial L)) (η:AxisGeneric (E:=E) z) (idem:η^2=η)
    (clear : let : Algebra (Plane L) E := axisPlaneAlgebra b
      ∀ x:FibreGeneric (E:=E) z,IsIntegral (Polynomial L) x →
        ∃ u:Fiber E z,(1 ⊗ₜ[(Polynomial L)] u : FibreGeneric (E:=E) z)=
          algebraMap (Polynomial L) (FibreGeneric (E:=E) z) d*x) :
    ∃ v∈chartImage E true z b,
      axisToGeneric (E:=E) z v=axisToGeneric (E:=E) z (polyMap E true z b d)*η := by
  let : Algebra (Plane L) E := axisPlaneAlgebra b
  let V := FibreGeneric (E:=E) z
  let G := axisGenericData (E:=E) b z nz
  let g := G.val
  let x : V := g.symm η
  have idemx : x^2=x :=
    (map_pow g.symm η 2).symm.trans (congrArg g.symm idem)
  obtain ⟨u,hu⟩ := clear x (idempotent_integral (A:=(Polynomial L)) x idemx)
  let φ := axisFibreData (E:=E) b z nz
  refine ⟨φ.val u,(φ.property.2.2 _).mp ⟨u,rfl⟩,?_⟩
  have m := congrArg g hu
  rw [G.property.1,map_mul,axisGenericData_scalar] at m
  change axisToGeneric (E:=E) z (φ.val u)=axisToGeneric (E:=E) z (polyMap E true z b d)*g (g.symm η) at m
  rw [RingEquiv.apply_symm_apply] at m
  exact m
theorem actual_axis_finite_index (p:ℕ) [CharP L p] [CharP (FractionRing (Polynomial L)) p]
    (small:finrank ChartField E<p) (z:L) (nz:z≠0) [IsReduced (AxisGeneric (E:=E) z)]
    (δ:Plane L) (nonzero:δ≠0) (principal:axisDiscriminant (E:=E) false=Ideal.span {δ})
    [DecidableEq L] :
    (branchProduct (Bivariate.swap δ)).map (evalRingHom z)≠0 ∧
    ∃ d:(Polynomial L), d≠0 ∧ d^2∣δ.eval (C z) ∧
      (∀ x∈d.roots,2≤((branchProduct (Bivariate.swap δ)).map (evalRingHom z)).rootMultiplicity x) ∧
      ∀ η:AxisGeneric (E:=E) z, η^2=η →
        ∃ v∈chartImage E true z false,
          axisToGeneric (E:=E) z v=axisToGeneric (E:=E) z (polyMap E true z false d)*η := by
  let : Algebra (Plane L) E := axisPlaneAlgebra false
  let : Algebra (FractionRing (Plane L)) E := axisFractionAlgebra false
  let : SMul (Plane L) (FractionRing (Plane L)) :=
    (inferInstance : Algebra (Plane L) (FractionRing (Plane L))).toSMul
  let : IsScalarTower (Plane L) (FractionRing (Plane L)) E := axisPlaneTower false
  let : FiniteDimensional (FractionRing (Plane L)) E := axisFractionFinite false
  let : Algebra.IsSeparable (FractionRing (Plane L)) E := axisFraction_separable false
  let : IsReduced (FibreGeneric (E:=E) z) := reducedOnChart false z nz
  have degree : finrank (FractionRing (Plane L)) E<p :=
    (axisFractionRank (E:=E) false).symm ▸ small
  obtain ⟨good,d,dn,dvd,support,clear⟩ := fibre_index_supported p degree z δ nonzero principal
  exact ⟨good,d,dn,dvd,support,fun η idem=>chartClear false z nz d η idem clear⟩
theorem actual_axis_infinity_index (p:ℕ) [CharP L p] [CharP (FractionRing (Polynomial L)) p]
    (small:finrank ChartField E<p) (z:L) (nz:z≠0) [IsReduced (AxisGeneric (E:=E) z)]
    (δ:Plane L) (nonzero:δ≠0) (principal:axisDiscriminant (E:=E) true=Ideal.span {δ})
    [DecidableEq L] (good:(Bivariate.swap δ).trailingCoeff.eval z≠0) :
    ∃ d:(Polynomial L),d.eval 0≠0 ∧
      ∀ η:AxisGeneric (E:=E) z,η^2=η →
        ∃ v∈chartImage E true z true,
          axisToGeneric (E:=E) z v=axisToGeneric (E:=E) z (polyMap E true z true d)*η := by
  let : Algebra (Plane L) E := axisPlaneAlgebra true
  let : Algebra (FractionRing (Plane L)) E := axisFractionAlgebra true
  let : SMul (Plane L) (FractionRing (Plane L)) :=
    (inferInstance : Algebra (Plane L) (FractionRing (Plane L))).toSMul
  let : IsScalarTower (Plane L) (FractionRing (Plane L)) E := axisPlaneTower true
  let : FiniteDimensional (FractionRing (Plane L)) E := axisFractionFinite true
  let : Algebra.IsSeparable (FractionRing (Plane L)) E := axisFraction_separable true
  let : IsReduced (FibreGeneric (E:=E) z) := reducedOnChart true z nz
  have degree : finrank (FractionRing (Plane L)) E<p :=
    (axisFractionRank (E:=E) true).symm ▸ small
  obtain ⟨d,d0,clear⟩ := boundary_index p degree δ nonzero principal z good
  exact ⟨d,d0,fun η idem=>chartClear true z nz d η idem clear⟩
#print axioms actual_axis_finite_index
#print axioms actual_axis_infinity_index
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedAxisIndex
