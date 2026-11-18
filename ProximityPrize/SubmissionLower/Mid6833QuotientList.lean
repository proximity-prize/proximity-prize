/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833LinearCount
import ProximityPrize.SubmissionLower.Mid6833HeadroomScalar
namespace Frontier.LinearKernel
open Polynomial Finset KoalaFrontier ReedSolomon
open scoped Polynomial Classical
noncomputable section
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
variable {K I : Type*} [Field K]
theorem normalized_injection (σ : K →+* K) (x : I ↪ K) (fixed : ∀ i, σ (x i)=x i)
    (u v : I → K) (a b B L R : K[X]) (E : Finset K) (P : K → K[X])
    (S : K → Finset I) (w δ k : ℕ) (hb : b≠0)
    (da : a.natDegree≤δ) (dl : L.natDegree≤w+δ)
    (compatible : a.map σ*R=b*L.map σ)
    (row : ∀ g∈E, a*P g+b*(P g).map σ=B+C g*L+C (σ g)*R)
    (deg : ∀ g∈E, (P g).natDegree≤w)
    (value : ∀ g∈E, ∀ i∈S g, (P g).eval (x i)=u i+g*v i)
    (slope : ∀ g∈E, ∀ i∈S g, a.eval (x i)*v i=L.eval (x i))
    (noSlope : ¬∃ V : K[X], V.natDegree≤w ∧ a*V=L)
    (save : ∀ H : K[X], H≠0 → Solves σ b (-(a.map σ)) H → k≤H.natDegree)
    (g₀ g₁ : E) (ne : g₁ ≠ g₀) :
    ∃ (T : E ↪ K[X]) (word : I → K), ∀ g : E, (T g).natDegree≤w+δ-k ∧
       ∀ i∈S g, (T g).eval (x i)=word i := by
  let Q : E → K[X] := fun g => a*(P g-P g₀)-C ((g:K)-(g₀:K))*L
  have rows (g : E) : b*(Q g).map σ = -(a.map σ)*Q g+0 := by
    dsimp [Q]
    simp only [Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,map_sub]
    linear_combination (a.map σ)*(row g g.property) - (a.map σ)*(row g₀ g₀.property) + (C (σ g)-C (σ g₀))*compatible
  have inj : Function.Injective Q := by
    intro g h eq
    by_contra ne'
    have ne' : (g:K)-(h:K)≠0 := sub_ne_zero.mpr (fun eq => ne' (Subtype.ext eq))
    have hh : a*(P g - P h) = C ((g:K)-(h:K))*L := by
      dsimp [Q] at eq
      simp only [C_sub] at eq ⊢
      linear_combination eq
    apply noSlope
    refine ⟨C ((g:K)-(h:K))⁻¹*(P g-P h), (natDegree_C_mul_le ..).trans ((natDegree_sub_le ..).trans (max_le (deg _ g.property) (deg _ h.property))),?_⟩
    rw [mul_left_comm a _ _,hh,← mul_assoc,← C_mul,inv_mul_cancel₀ ne', C_1,one_mul]
  have dc (g : E) : (Q g-Q g₀).natDegree≤w+δ := by
    have sd : (P g-P g₀).natDegree≤w := (natDegree_sub_le ..).trans (max_le (deg _ g.property) (deg _ g₀.property))
    have ad : (a*(P g-P g₀)).natDegree≤a.natDegree+(P g-P g₀).natDegree := natDegree_mul_le
    have cc : (C ((g:K)-(g₀:K))*L).natDegree≤L.natDegree := natDegree_C_mul_le _ _
    have hq : Q g₀=0 := by simp [Q]
    rw [hq,sub_zero]
    exact (natDegree_sub_le ..).trans (max_le (by omega) (cc.trans dl))
  obtain ⟨H,T,word,hn,hs,_,fac,fits⟩ := normalized_affine_family σ b (-(a.map σ)) Q g₀ x (fun i => a.eval (x i)*(u i+(g₀:K)*v i-(P g₀).eval (x i))) fixed hb 0 rows ⟨g₁,fun eq => ne (inj eq)⟩
  refine ⟨⟨T,?_⟩,word,?_⟩
  · intro g h eq
    apply inj
    have z := (fac g).2
    rw [eq,← (fac h).2] at z
    exact sub_left_inj.mp z
  · intro g
    have d := dc g
    rw [(fac g).2] at d
    refine ⟨(quotient_degree_bound hn _ d).trans (Nat.sub_le_sub_left (save H hn hs) _),?_⟩
    intro i hi
    apply (fits g i).mp
    simp only [Q,eval_sub,eval_mul,eval_C,value g g.property i hi,← slope g g.property i hi]
    ring

local instance : DecidableEq KoalaBear.Ext6 := Classical.decEq _

theorem high_cap (x : Fin 262144 ↪ KoalaBear.Ext6) (E : Finset KoalaBear.Ext6)
    (S : KoalaBear.Ext6 → Finset (Fin 262144)) (A : ∀ g∈E, 179740≤(S g).card)
    (T : E ↪ KoalaBear.Ext6[X]) (word : Fin 262144 → KoalaBear.Ext6)
    (d : ∀ g : E, (T g).natDegree≤131543 ∧ ∀ i∈S g, (T g).eval (x i)=word i) :
    E.card ≤ 214887237245589756 := by
  classical
  let L := closePolynomialSet x word 131544 179740
  have hf : L.Finite := (closePolynomialSet_finite_and_ncard_mul_choose_le x word (show 131544≤179740 by decide)).1
  have sub : (univ.map T) ⊆ hf.toFinset := by
    intro z hz
    obtain ⟨g,_,rfl⟩ := mem_map.mp hz
    apply hf.mem_toFinset.mpr
    refine ⟨(Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le (d g).1)),(A _ g.property).trans (card_le_card ?_)⟩
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _,(d g).2 i hi⟩
  have bound := Frontier.SeedFreeze.scalar_list_headroom x word
  change L.ncard ≤ _ at bound
  rw [Set.ncard_eq_toFinset_card _ hf] at bound
  simpa using (card_le_card sub).trans bound

#print axioms normalized_injection
#print axioms high_cap
end
end Frontier.LinearKernel
