/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833RationalLines
import ProximityPrize.SubmissionLower.Mid6833ResidueInstances
import ProximityPrize.SubmissionLower.Mid6833SaturatedRow
import ProximityPrize.SubmissionLower.Mid6833ResidueCode
namespace Genuine.SaturatedLines
open Polynomial Finset KoalaBear Frontier.ResidueOrbit Frontier.LinearKernel.Saturation
open ProximityPrize.Benchmark.IRSProfile
open scoped Polynomial BigOperators Classical Function
noncomputable section
set_option maxRecDepth 24000
set_option maxHeartbeats 600000
local instance : DecidableEq K := Classical.decEq _

private abbrev τ := FiniteField.frobeniusAlgHom F K
private abbrev r := Module.finrank F K
private abbrev θ (j : Fin r) : K →ₐ[F] K := τ^j.val
private abbrev pole := D 9554

theorem field_degree : r=6 := by
  have eq := Module.card_eq_pow_finrank (K:=F) (V:=K)
  rw [KoalaBear.card_ext6,show Fintype.card F = fieldSize from ZMod.card _] at eq
  exact pow_right_injective₀ (by decide : 0<fieldSize) (by decide : fieldSize≠1) eq.symm

theorem eq_of_generator (f g : K →ₐ[F] K) (eq : f ext6Gen=g ext6Gen) : f=g := by
  ext z
  have saved := rep_value z
  rw [←saved]
  simp only [rep,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,
    map_sum,map_mul,map_pow,AlgHom.commutes,eq]

private theorem gen_distinct : Function.Injective (fun j: Fin r => θ j ext6Gen) := by
  intro a b h
  exact (FiniteField.bijective_frobeniusAlgHom_pow F K).1 (eq_of_generator _ _ h)

private theorem theta_pole (j : Fin r) :
    pole.map (θ j).toRingHom = (Polynomial.X : K[X])^9554-C (θ j ext6Gen) := by simp [pole,D]

private theorem shifted_coprime {E : Type*} [Field E] (U:E[X]) {a b:E} (ne : a≠b) :
    IsCoprime (U-C a) (U-C b) := by
  have bn := sub_ne_zero.mpr ne.symm
  refine ⟨C (b-a)⁻¹,-(C (b-a)⁻¹),?_⟩
  calc
    _ = C ((b-a)⁻¹) * (C b-C a) := by ring
    _ = 1 := by rw [←map_sub,←map_mul,inv_mul_cancel₀ bn,map_one]

private theorem orbit_coprime : Pairwise (IsCoprime on fun j : Fin r => pole.map (θ j).toRingHom) := by
  intro i j ne
  rw [Function.onFun,theta_pole,theta_pole]
  exact shifted_coprime _ (gen_distinct.ne ne)

private theorem degP : pole.natDegree=9554 := by
  unfold pole D
  rw [natDegree_sub_eq_left_of_natDegree_lt (by simp : (C ext6Gen).natDegree < ((Polynomial.X:K[X])^9554).natDegree),natDegree_X_pow]

/-- At the actual excess-9554 parameter, every prime-field affine seed line
has at most 596 true qualifying seeds for an arbitrary base-valued received word. -/
theorem actual_line {G : Type*} [Fintype G] (c : G ↪ F) (origin v : K) (vn : v≠0)
    (word : Index → F)
    (ag : ∀g : G, ∃P : K[X], P.natDegree≤131071 ∧
      179740 ≤ (univ.filter (fun i => P.eval (domain i)=
        (algebraMap F K (word i) + (origin+c g • v))/(pole.eval (domain i)))).card) :
    Fintype.card G≤596 := by
  apply Genuine.OrbitLines.actual_pole_line domain (Fintype.card_fin (2^18)) τ (fun j:Fin r => j.val)
    ((Fintype.card_fin r).trans field_degree) pole degP orbit_coprime actual_domain_nonzero
    (fun _ => τ.commutes _) c origin v vn word
  intro g
  obtain ⟨P,dp,good⟩ := ag g
  refine ⟨P,dp,?_⟩
  apply good.trans
  apply Finset.card_le_card
  intro i hi
  exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩

/-- The same received pair has at most p times the line cap throughout an
affine plane. The coordinate maps only have to distinguish its selected seeds. -/
theorem actual_plane {G : Type*} [Fintype G] (c : G ↪ F × F) (o u v : K) (vn : v≠0)
    (w : Index → F)
    (ag : ∀g : G, ∃P : K[X], P.natDegree≤131071 ∧
      179740 ≤ (univ.filter (fun i => P.eval (domain i)=
        (algebraMap F K (w i) + ((o+(c g).1 • u)+(c g).2 • v))/(pole.eval (domain i)))).card) :
    Fintype.card G ≤ 1269901034068 := by
  classical
  let b (g:G) := (c g).1
  let fiber (t:F) := univ.filter (fun g => b g=t)
  have local_cap (t:F) : (fiber t).card≤596 := by
    let e : fiber t ↪ F := ⟨fun g => (c g.val).2,by
      intro g h eq
      apply Subtype.ext
      apply c.injective
      exact Prod.ext (((mem_filter.mp g.property).2).trans ((mem_filter.mp h.property).2).symm) eq⟩
    have rr := actual_line e (o+t • u) v vn w (by
      intro g
      have cg : (c g.val).1=t := (mem_filter.mp g.property).2
      obtain ⟨P,dP,good⟩ := ag g.val
      refine ⟨P,dP,?_⟩
      change 179740 ≤ (univ.filter (fun i => P.eval (domain i) =
        (algebraMap F K (w i) + ((o+t • u)+(c g.val).2 • v))/(pole.eval (domain i)))).card
      rw [cg] at good
      exact good)
    simpa only [Fintype.card_coe] using rr
  have total := sum_le_sum (s:=univ) (fun t _ => local_cap t)
  have eq := sum_card_fiberwise_eq_card_filter (univ:Finset G) (univ:Finset F) b
  change ∑ t, (fiber t).card = _ at eq
  simp at eq
  rw [eq] at total
  simpa [show Fintype.card F=2130706433 from ZMod.card _] using total

end
#print axioms actual_line
#print axioms actual_plane
end Genuine.SaturatedLines
