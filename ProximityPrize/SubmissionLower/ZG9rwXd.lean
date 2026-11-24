import ProximityPrize.SubmissionLower.Z62SyBc
set_option Elab.async false
namespace qFD8jve
noncomputable section
open Finset Polynomial
open P5 (p)


open qb0hmCe (cLN specialize zD)
open cu (L)
open E7 (CurvePlace axV poleOrder Tq)
open scoped Classical WithZero
def c2 :Prop :=
  ∀ (E :Type) [Field E] [Algebra L E] (a :E →ₐ[L] LaurentSeries L) (F:E[X][X]),
    let v :=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰).comap a.toRingHom
    0<F.natDegree→F.natDegree<p→F.leadingCoeff.coeff 0≠0 →
    polarResultant F≠0→ aFA v F 0→v (guard F)=1 →
    ∀ P Q:L[X],P.coeff 0=0→Q.coeff 0≠0 →
      specialize (cLN a 0 F) P Q=0 →
      specialize (cLN a 0 F).derivative P Q≠0 →
      Vanishes (zD a F P Q)
private theorem sum_le_all {α:Type} (f :α→ℕ) (hf :f.HasFiniteSupport) (s :Finset α) :
  ∑ i∈s,f i ≤ ∑ᶠ i,f i:= by
 rw [finsum_eq_finsetSum_of_support_subset f (s :=hf.toFinset∪s) (by
  intro i hi
  exact mem_union_left _ ((Set.Finite.mem_toFinset _).mpr hi))]
 exact sum_le_sum_of_subset_of_nonneg subset_union_right fun _ _ _=>Nat.zero_le _
private theorem finite_tuple {E σ:Type} [Field E] [Algebra L E] [Fintype σ]
  (h:axV L E) (u:σ→E) :
  (fun v :CurvePlace L E=>Tq v.value u).HasFiniteSupport:= by
 have hf : (⋃ i:σ,Function.support (fun v :CurvePlace L E =>
    poleOrder v.value (u i))).Finite :=Set.finite_iUnion fun i=>(h (u i)).1
 apply hf.subset
 intro v hv
 simp only [Set.mem_iUnion,Function.mem_support] at hv ⊢
 by_contra! hz
 exact hv (Finset.sup_eq_bot_iff _ _ |>.mpr fun i _=>hz i)
end
end qFD8jve
