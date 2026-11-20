/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833ResidueRank
namespace Frontier.ResidueOrbit
open Polynomial Finset Submodule
open scoped Polynomial Classical BigOperators Pointwise
noncomputable section
variable {F K I J : Type*} [Field F] [Field K] [Algebra F K] [Fintype J]
local instance mid6833Local_ResidueAnchors_7  : DecidableEq K := Classical.decEq _

/-- A nonzero multiple of a pole polynomial can vanish at no more than
its surplus degree many distinct actual nodes disjoint from the poles. -/
theorem physical_zeros (P Λ : K[X]) (nz : P≠0) (div : Λ∣P)
    (x : I ↪ K) (A : Finset I) (regular : ∀i∈A, Λ.eval (x i)≠0)
    (van : ∀i∈A, P.eval (x i)=0) : Λ.natDegree+A.card≤P.natDegree := by
  classical
  obtain ⟨Q,rfl⟩ := div
  have zn : Λ≠0 := left_ne_zero_of_mul nz
  have qn : Q≠0 := right_ne_zero_of_mul nz
  rw [natDegree_mul zn qn]
  apply Nat.add_le_add_left
  by_contra! fails
  apply qn
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q
    (f:=fun i:A => x i.val) (x.injective.comp Subtype.val_injective) (fun i => ?_)
    (by simpa only [Fintype.card_coe] using fails)
  have h := van i.val i.property
  rw [eval_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (regular i.val i.property)

/-- The kernel additionally vanishes at a genuine packet of agreement nodes
after subtracting one common representative. -/
def anchored (θ : J → K →ₐ[F] K) (D H L : K[X]) (W : ℕ) (x : I ↪ K)
    (A : Finset I) : Submodule F (K × K[X]) where
  carrier := {z | z ∈ pairs θ D H L W ∧ ∀ i∈A, z.2.eval (x i)=0}
  zero_mem' := ⟨Submodule.zero_mem _,by simp⟩
  add_mem' := by
    rintro u v ⟨hu,zu⟩ ⟨hv,zv⟩
    exact ⟨Submodule.add_mem _ hu hv,by intro i hi; simp [zu i hi,zv i hi]⟩
  smul_mem' := by
    rintro t u ⟨hu,zu⟩
    exact ⟨Submodule.smul_mem _ t hu,by intro i hi; simp [zu i hi]⟩

theorem anchored_kernel (θ : J → K →ₐ[F] K) (D D' H L : K[X]) (W : ℕ)
    (part : D'∣D) (cop : IsCoprime D' H) (x : I ↪ K) (A : Finset I)
    (regular : ∀i∈A, (univ.lcm (fun j => D'.map (θ j).toRingHom)).eval (x i)≠0)
    (enough : W < (univ.lcm (fun j => D'.map (θ j).toRingHom)).natDegree+A.card) :
    Function.Injective ((LinearMap.fst F K K[X]).comp (anchored θ D H L W x A).subtype) := by
  apply LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_)
  rintro ⟨⟨g,P⟩,⟨deg,fix,res⟩,van⟩ zero
  change g=0 at zero
  subst g
  have dp : D'∣P := cop.dvd_of_dvd_mul_left (part.trans (by simpa using res))
  have all : univ.lcm (fun j => D'.map (θ j).toRingHom) ∣ P := by
    apply Finset.lcm_dvd_iff.mpr
    intro j _
    simpa only [fix j] using Polynomial.map_dvd (θ j).toRingHom dp
  have hp : P=0 := by
    by_contra hn
    have lim := physical_zeros P _ hn all x A regular van
    exact (not_lt.mpr (lim.trans deg)) enough
  exact Subtype.ext (Prod.ext rfl hp)

theorem anchored_rank [FiniteDimensional F K] (θ : J → K →ₐ[F] K)
    (D D' H L : K[X]) (W : ℕ) (part : D'∣D) (cop : IsCoprime D' H)
    (x : I ↪ K) (A : Finset I)
    (regular : ∀i∈A, (univ.lcm (fun j => D'.map (θ j).toRingHom)).eval (x i)≠0)
    (enough : W < (univ.lcm (fun j => D'.map (θ j).toRingHom)).natDegree+A.card)
    (S : Finset K[X]) (realized : ∀ P∈S, ∃ g:K, (g,P)∈anchored θ D H L W x A) :
    Pruning.rank K S ≤ Module.finrank F K := by
  classical
  let M := anchored θ D H L W x A
  let first := (LinearMap.fst F K K[X]).comp M.subtype
  let second := (LinearMap.snd F K K[X]).comp M.subtype
  have hi := anchored_kernel θ D D' H L W part cop x A regular enough
  let _ : FiniteDimensional F M := FiniteDimensional.of_injective first hi
  have linearF : span F (S:Set K[X]) ≤ LinearMap.range second := by
    apply span_le.mpr
    intro P hp
    obtain ⟨g,hg⟩ := realized P hp
    exact ⟨⟨(g,P),hg⟩,rfl⟩
  let _ : FiniteDimensional K (span K (S:Set K[X])) := .span_of_finite K S.finite_toSet
  have aff : (affineSpan K (S:Set K[X])).direction ≤ span K (S:Set K[X]) := by
    rw [direction_affineSpan]
    apply span_le.mpr
    rintro _ ⟨x,hx,y,hy,rfl⟩
    exact Submodule.sub_mem _ (subset_span hx) (subset_span hy)
  exact (Submodule.finrank_mono aff).trans
    ((Submodule.finrank_span_le_finrank_span (R:=F) (K:=K) S.finite_toSet).trans
      ((Submodule.finrank_mono linearF).trans
        ((LinearMap.finrank_range_le second).trans (LinearMap.finrank_le_finrank_of_injective hi))))


#print axioms physical_zeros
#print axioms anchored_kernel
#print axioms anchored_rank
end
end Frontier.ResidueOrbit
