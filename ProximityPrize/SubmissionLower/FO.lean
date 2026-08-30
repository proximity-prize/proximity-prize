import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.AA
namespace ProximityPrize.SubmissionLower.ContactPost6464ShearSupportResearch
open scoped BigOperators Matrix
open ProximityPrize.SubmissionLower.ContactPost6464MinkowskiRecurrenceResearch
noncomputable section
variable {K:Type*} [Field K]
abbrev Poly4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
def shearImage (i:Fin 4):Poly4 K:=
 ![MvPolynomial.X 0,MvPolynomial.X 1,
   MvPolynomial.X 2-MvPolynomial.X 3,MvPolynomial.X 3] i
def shearMap:Poly4 K →+*Poly4 K:=
 MvPolynomial.eval₂Hom MvPolynomial.C shearImage
def pullShearWeights (weights:Fin 4 → ℕ):Fin 4 → ℕ:=
 ![weights 0,weights 1,max (weights 2) (weights 3),weights 3]
theorem shearImage_wt_le (weights:Fin 4 → ℕ) (i:Fin 4):
   wt weights (shearImage (K:=K) i) ≤ pullShearWeights weights i:=by
 fin_cases i
 · simp [shearImage,pullShearWeights,wt_X]
 · simp [shearImage,pullShearWeights,wt_X]
 · dsimp [shearImage,pullShearWeights]
   exact (wt_sub_le weights _ _).trans (by rw [wt_X,wt_X])
 · simp [shearImage,pullShearWeights,wt_X]
theorem wt_finset_prod_le_sum {ι:Type*} [DecidableEq ι]
   (weights:Fin 4 → ℕ) (I:Finset ι) (f:ι → Poly4 K):
   wt weights (∏ i∈I,f i) ≤ ∑ i∈I,wt weights (f i):=by
 induction I using Finset.induction_on with
 | empty =>
     simp only [Finset.prod_empty,Finset.sum_empty]
     unfold wt MvPolynomial.weightedTotalDegree
     simp
 | @insert i I hi ih =>
     simp only [Finset.prod_insert hi,Finset.sum_insert hi]
     exact (wt_mul_le weights _ _).trans (Nat.add_le_add le_rfl ih)
theorem wt_finset_sum_le {ι:Type*} [DecidableEq ι]
   (weights:Fin 4 → ℕ) (I:Finset ι) (f:ι → Poly4 K) (cap:ℕ)
   (hf:∀ i∈I,wt weights (f i) ≤ cap):
   wt weights (∑ i∈I,f i) ≤ cap:=by
 unfold wt
 rw [←ContactFactorCaps.degree_weightedLift,map_sum]
 apply (MvPolynomial.degreeOf_sum_le (4:Fin 5) I
   (fun i => ContactFactorCaps.weightedLift K weights (f i))).trans
 apply Finset.sup_le
 intro i hi
 rw [ContactFactorCaps.degree_weightedLift]
 exact hf i hi
theorem shear_monomial_product_wt_le
   (weights:Fin 4 → ℕ) (d:Fin 4 →₀ ℕ):
   wt weights (∏ i∈d.support,shearImage (K:=K) i^d i) ≤
     Finsupp.weight (pullShearWeights weights) d:=by
 apply (wt_finset_prod_le_sum weights d.support
   (fun i => shearImage (K:=K) i^d i)).trans
 calc
   (∑ i∈d.support,wt weights (shearImage (K:=K) i^d i)) ≤
       ∑ i∈d.support,d i*pullShearWeights weights i:=by
     apply Finset.sum_le_sum
     intro i hi
     exact (wt_pow_le weights (shearImage (K:=K) i) (d i)).trans
       (Nat.mul_le_mul_left _ (shearImage_wt_le weights i))
   _=Finsupp.weight (pullShearWeights weights) d:=by
     rw [Finsupp.weight_apply]
     simp only [Finsupp.sum,nsmul_eq_mul]
     simp
theorem shearMap_wt_le_pulled (weights:Fin 4 → ℕ) (P:Poly4 K):
   wt weights (shearMap P) ≤ wt (pullShearWeights weights) P:=by
 change wt weights
     (MvPolynomial.eval₂ MvPolynomial.C (shearImage (K:=K)) P) ≤ _
 rw [MvPolynomial.eval₂_eq]
 apply wt_finset_sum_le
 intro d hd
 have hprod:=shear_monomial_product_wt_le (K:=K) weights d
 have hcoeff:wt weights (MvPolynomial.C (P.coeff d):Poly4 K)=0:=
   wt_C weights _
 have hmul:=wt_mul_le weights (MvPolynomial.C (P.coeff d):Poly4 K)
   (∏ i∈d.support,shearImage (K:=K) i^d i)
 rw [hcoeff,Nat.zero_add] at hmul
 exact hmul.trans (hprod.trans
   (MvPolynomial.le_weightedTotalDegree (pullShearWeights weights) hd))
end
end ProximityPrize.SubmissionLower.ContactPost6464ShearSupportResearch
