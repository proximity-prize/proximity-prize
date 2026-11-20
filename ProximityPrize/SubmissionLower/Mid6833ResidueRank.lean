/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833ResidueOrbit
import ProximityPrize.SubmissionLower.Mid6833Pruning
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.Algebra.GCDMonoid.Finset
namespace Frontier.ResidueOrbit
open Polynomial Finset Submodule
open scoped Polynomial Classical BigOperators Pointwise
noncomputable section
variable {F K J : Type*} [Field F] [Field K] [Algebra F K] [Fintype J]
local instance mid6833Local_ResidueRank_10  : DecidableEq K := Classical.decEq _

/-- The space of polynomial/seed pairs obeying a congruence at the virtual
poles. Each conjugation is linear over F. -/
def pairs (θ : J → K →ₐ[F] K) (D H L : K[X]) (W : ℕ) : Submodule F (K × K[X]) where
  carrier := {z | z.2.natDegree ≤ W ∧ (∀ j, z.2.map (θ j).toRingHom = z.2) ∧
    D ∣ H*z.2 + C z.1*L}
  zero_mem' := by simp
  add_mem' := by
    rintro ⟨g,P⟩ ⟨h,Q⟩ ⟨dp,fp,rp⟩ ⟨dq,fq,rq⟩
    refine ⟨(natDegree_add_le P Q).trans (max_le dp dq),?_,?_⟩
    · intro j
      simp only [Prod.snd_add,Polynomial.map_add,fp j,fq j]
    · change D ∣ H*(P+Q)+C (g+h)*L
      convert dvd_add rp rq using 1
      simp only [map_add]
      ring
  smul_mem' := by
    rintro t ⟨g,P⟩ ⟨dp,fp,rp⟩
    have scalarpoly : t • P = C (algebraMap F K t)*P := by
      rw [← Polynomial.smul_eq_C_mul,algebraMap_smul]
    refine ⟨(natDegree_smul_le t P).trans dp,?_,?_⟩
    · intro j
      change (t • P).map (θ j).toRingHom=t • P
      rw [scalarpoly,Polynomial.map_mul,Polynomial.map_C,fp j,AlgHom.toRingHom_eq_coe]
      exact congrArg (fun x:K => C x*P) ((θ j).commutes t)
    · change D∣H*(t•P)+C (t•g)*L
      rw [scalarpoly,Algebra.smul_def,map_mul]
      convert dvd_mul_of_dvd_right rp (C (algebraMap F K t)) using 1 <;> ring

/-- A complete orbit of virtual residues determines the polynomial when the
orbit lcm has degree above the message bound. -/
theorem seed_injective (θ : J → K →ₐ[F] K) (D D' H L : K[X]) (W : ℕ)
    (part : D'∣D) (cop : IsCoprime D' H)
    (large : W < (univ.lcm (fun j => D'.map (θ j).toRingHom)).natDegree) :
    Function.Injective ((LinearMap.fst F K K[X]).comp (pairs θ D H L W).subtype) := by
  apply LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_)
  rintro ⟨⟨g,P⟩, deg, fix, res⟩ hzero
  change g=0 at hzero
  subst g
  have dp : D' ∣ P := cop.dvd_of_dvd_mul_left (part.trans (by simpa using res))
  have all : univ.lcm (fun j => D'.map (θ j).toRingHom) ∣ P := by
    apply Finset.lcm_dvd_iff.mpr
    intro j _
    have eq : P.map (θ j).toRingHom = P := fix j
    have bound := Polynomial.map_dvd (θ j).toRingHom dp
    rw [eq] at bound
    exact bound
  have hp : P=0 := by
    by_contra hn
    have bound := natDegree_le_of_dvd all hn
    exact (not_lt.mpr (bound.trans deg)) large
  exact Subtype.ext (Prod.ext rfl hp)

/-- Extension-linear rank is bounded by the field-extension degree,
even though the residues vary with the seed. -/
theorem short_orbit_rank [FiniteDimensional F K] (θ : J → K →ₐ[F] K)
    (D D' H L : K[X]) (W : ℕ) (part : D'∣D) (cop : IsCoprime D' H)
    (large : W < (univ.lcm (fun j => D'.map (θ j).toRingHom)).natDegree)
    (S : Finset K[X]) (realized : ∀ P∈S, ∃ g:K, (g,P)∈pairs θ D H L W) :
    Pruning.rank K S ≤ Module.finrank F K := by
  classical
  let M := pairs θ D H L W
  let first := (LinearMap.fst F K K[X]).comp M.subtype
  let second := (LinearMap.snd F K K[X]).comp M.subtype
  have hi := seed_injective θ D D' H L W part cop large
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

/-- On the Koala parameter range, a dimension-six scalar carrier has
fewer than 100,000 close words even with a conservative enlarged degree. -/
theorem small_carrier_count {K I : Type*} [Field K] [Fintype I]
    (x : I ↪ K) (han : Fintype.card I=262144) (word : I → K) (S : Finset K[X])
    (rank : Pruning.rank K S ≤ 6)
    (deg : ∀P∈S, P.natDegree ≤ 164806)
    (ag : ∀P∈S, 179740 ≤ (univ.filter (fun i => P.eval (x i)=word i)).card) :
    S.card ≤ 70308 := by
  have h := Pruning.scalar x word 179740 164806 6 (by decide) (by omega) S rank deg ag
  rw [han] at h
  exact h.trans (by decide +kernel)

#print axioms seed_injective
#print axioms short_orbit_rank
#print axioms small_carrier_count
end
end Frontier.ResidueOrbit
