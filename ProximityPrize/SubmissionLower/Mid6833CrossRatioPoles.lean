/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import Mathlib.Algebra.Polynomial.Lifts
import ProximityPrize.SubmissionLower.Mid6833CrossRatio
import ProximityPrize.SubmissionLower.Mid6833SaturatedLines
namespace Genuine.CrossRatio
open Polynomial Finset Function
open scoped Polynomial Classical BigOperators
noncomputable section
variable {F K E L : Type*} [Field F] [Field K] [Field E] [Field L]

/-- Evaluating the actual divisibility requirement for a normalized family at
a pole gives a visible fractional-linear chart when the displayed determinant
is nonzero. The coefficients of the varying polynomial lie in the base. -/
def chartFromDivisor (S : Finset K) (bK : F →+* K) (bL : F →+* L)
    (ι : K →+* E) (l : L →+* E) (comm : ι.comp bK=l.comp bL) (α : L)
    (D A B C₀ C₁ T H : K[X]) (Q : K → F[X])
    (root : D.eval₂ ι (l α)=0)
    (res : ∀g∈S, D∣ (A+Polynomial.C g*B)*(T+H*(Q g).map bK)-(C₀+Polynomial.C g*C₁))
    (visible : (H*(A*C₁-B*C₀)).eval₂ ι (l α) ≠ 0) : Chart S ι l := by
  let ev := Polynomial.eval₂RingHom ι (l α)
  refine ⟨ev (H*A),ev (H*B),ev (C₀-T*A),ev (C₁-T*B),?_,
    fun g => (Q g).eval₂ bL α,?_⟩
  · have h : ev (H*(A*C₁-B*C₀))≠0 := visible
    convert h using 1
    simp only [map_mul,map_sub]; ring
  · intro g hg
    have ez := map_dvd ev (res g hg)
    have rr : ev D=0 := root
    rw [rr,zero_dvd_iff] at ez
    have eq : ev ((Q g).map bK) = l ((Q g).eval₂ bL α) := by
      change ((Q g).map bK).eval₂ ι (l α) = _
      rw [Polynomial.eval₂_map,Polynomial.hom_eval₂,comm]
    have cons : ev (Polynomial.C g)=ι g := by simp [ev]
    simp only [map_add,map_sub,map_mul,cons,eq] at ez ⊢
    linear_combination ez

/-- A quotient fixed by coefficient Frobenius comes from a base-field polynomial.
This converts the normalized comparison output to the input for chartFromDivisor. -/
theorem lift_fixed [Fintype F] [Algebra F K] (Q : K[X])
    (fixed : Q.map (FiniteField.frobeniusAlgHom F K).toRingHom=Q) :
    ∃ R : F[X], R.map (algebraMap F K)=Q := by
  classical
  let p := Fintype.card F
  let f : F →+* K := algebraMap F K
  let P : K[X] := (Polynomial.X:K[X])^p-Polynomial.X
  have qp : 1<p := Fintype.one_lt_card
  have np : P≠0 := FiniteField.X_pow_card_sub_X_ne_zero K qp
  let image : Finset K := (univ : Finset F).image f
  let roots := P.roots.toFinset
  have incl : image⊆roots := by
    intro x hx
    obtain ⟨t,_,rfl⟩ := mem_image.mp hx
    apply Multiset.mem_toFinset.mpr ((mem_roots np).mpr ?_)
    change P.eval (f t)=0
    simp only [P,eval_sub,eval_pow,eval_X,←map_pow,p,FiniteField.pow_card,sub_self]
  have cap : roots.card ≤ image.card := by
    have h := P.roots.toFinset_card_le.trans (card_roots' P)
    rw [show P.natDegree=p from FiniteField.X_pow_card_sub_X_natDegree_eq K qp] at h
    simpa only [image,card_image_of_injective _ f.injective,card_univ] using h
  have same := eq_of_subset_of_card_le incl cap
  apply (Polynomial.mem_lifts (f:=f) Q).mp
  apply (Polynomial.lifts_iff_coeff_lifts (f:=f) Q).mpr
  intro n
  have h : (Q.coeff n)^p=Q.coeff n := by
    have hh := congrArg (fun U : K[X] => U.coeff n) fixed
    rw [coeff_map] at hh
    change (FiniteField.frobeniusAlgHom F K) (Q.coeff n)=Q.coeff n at hh
    rw [FiniteField.coe_frobeniusAlgHom] at hh
    exact hh
  have hr : Q.coeff n∈roots := by
    apply Multiset.mem_toFinset.mpr ((mem_roots np).mpr ?_)
    simp [Polynomial.IsRoot,P,h]
  rw [←same] at hr
  obtain ⟨u,_,hu⟩ := mem_image.mp hr
  exact ⟨u,hu⟩

/-- A directly usable chart for normalized quotients. Only the quotients
belonging to retained seeds have to satisfy the Frobenius equation. -/
def chartFromFixed [Fintype F] [Algebra F K] (S : Finset K)
    (bL : F →+* L) (ι : K →+* E) (l : L →+* E)
    (comm : ι.comp (algebraMap F K)=l.comp bL) (α : L)
    (D A B C₀ C₁ T H : K[X]) (Q : K → K[X])
    (root : D.eval₂ ι (l α)=0)
    (fixed : ∀g∈S, (Q g).map (FiniteField.frobeniusAlgHom F K).toRingHom=Q g)
    (res : ∀g∈S, D∣ (A+Polynomial.C g*B)*(T+H*Q g)-(C₀+Polynomial.C g*C₁))
    (visible : (H*(A*C₁-B*C₀)).eval₂ ι (l α) ≠ 0) : Chart S ι l := by
  classical
  let R (g:K) : F[X] := if hg:g∈S then (lift_fixed (Q g) (fixed g hg)).choose else 0
  apply chartFromDivisor S (algebraMap F K) bL ι l comm α D A B C₀ C₁ T H R root _ visible
  intro g hg
  have eq : (R g).map (algebraMap F K)=Q g := by
    simpa only [R,dif_pos hg] using (lift_fixed (Q g) (fixed g hg)).choose_spec
  rw [eq]
  exact res g hg

/-- For the saturated benchmark denominator, every pole field already has
degree divisible by six. Its Frobenius power fixes the sextic generator
because the generator is a power of that pole. -/
theorem saturated_six_dvd {L E : Type*} [Field L] [Field E] [Fintype L]
    (ι : KoalaBear.Ext6 →+* E) (l : L →+* E) (α:L) (m:ℕ)
    (size : Fintype.card L=KoalaBear.fieldSize^m)
    (root : (l α)^9554=ι KoalaBear.ext6Gen) : 6∣m := by
  let τ := FiniteField.frobeniusAlgHom KoalaBear.Field KoalaBear.Ext6
  have fe : (ι KoalaBear.ext6Gen)^(KoalaBear.fieldSize^m)=ι KoalaBear.ext6Gen := by
    rw [←root, ←map_pow, ←map_pow,←size,FiniteField.pow_card]
  have τm : τ^m=1 := by
    apply Genuine.SaturatedLines.eq_of_generator
    change (τ^m) KoalaBear.ext6Gen=KoalaBear.ext6Gen
    rw [AlgHom.coe_pow,FiniteField.coe_frobeniusAlgHom,pow_iterate]
    apply ι.injective
    rw [map_pow,show Fintype.card KoalaBear.Field=KoalaBear.fieldSize from ZMod.card _]
    exact fe
  have h := orderOf_dvd_of_pow_eq_one τm
  rw [FiniteField.orderOf_frobeniusAlgHom] at h
  have six : Module.finrank KoalaBear.Field KoalaBear.Ext6=6 := Genuine.SaturatedLines.field_degree
  rw [six] at h
  exact h

end
#print axioms chartFromDivisor
#print axioms lift_fixed
#print axioms chartFromFixed
#print axioms saturated_six_dvd
end Genuine.CrossRatio
