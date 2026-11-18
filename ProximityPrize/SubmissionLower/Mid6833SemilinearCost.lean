/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Extends the retained common-divisor and FrobeniusModule arguments in the
prior Bome2017 research, which credits Lucieno and BitWonka. -/
import ProximityPrize.SubmissionLower.Mid6833IntermediateDivisorBase
namespace ProximityPrize.SubmissionLower.Genuine6969.IntermediateDivisor
open Koala6831Comparison K6969Global Koala6831Separation Koala6831Moving
open Koala6831BenchmarkPrimitive (Received SelectionMap agreementSet)
open Frontier6969.GenuineMoving Polynomial Finset ReedSolomon ProximityPrize.Benchmark KoalaFrontier
open scoped Polynomial Classical
noncomputable section
local instance mid6833Local_SemilinearCost_10  : DecidableEq KoalaBear.Ext6 := Classical.decEq _
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

/-- Clearing the two conjugate products gives an explicit divisor of every homogeneous
solution. Distinct powers of Frobenius expose different portions of a pole orbit. -/
theorem orbit_divisor {K : Type*} [Field K] (s : K →+* K) (l r J common left right : K[X])
    (n : ℕ) (nc : common≠0) (lc : Frontier.LinearKernel.conjugateProduct s l n=common*left)
    (rc : Frontier.LinearKernel.conjugateProduct s r n=common*right)
    (jl : J ∣ left) (cop : IsCoprime J right) (V : K[X]) (v : Solves s l r V) : J ∣ V := by
  have p := Frontier.LinearKernel.iterate_row s r l V v.symm n
  rw [lc,rc,mul_assoc,mul_assoc] at p
  have eq := mul_left_cancel₀ nc p
  apply cop.dvd_of_dvd_mul_left
  rw [eq]
  exact dvd_mul_of_dvd_left jl _

/-- A whole family fits the same word after division by the minimal generator of
its semilinear kernel. Its roots avoid every fixed domain node. -/
theorem high_semilinear {d A C W k : ℕ} (ha : d+1≤A) (hc : 1≤C)
    (cap : ScalarAt d A C) (reduce : W≤d+k)
    (x : Fin 262144 ↪ KoalaBear.Ext6) (fixed : ∀i,σ (x i)=x i) (E : Finset KoalaBear.Ext6)
    (S : KoalaBear.Ext6 → Finset (Fin 262144)) (agree : ∀g∈E,A≤(S g).card)
    (V : E ↪ F[X]) (word : Fin 262144 → F) (l r : F[X]) (nl : l≠0)
    (sol : ∀g : E,Solves σ l r (V g))
    (divisor : ∀H : F[X], H≠0 → Solves σ l r H → k≤H.natDegree)
    (fit : ∀g : E,(V g).natDegree≤W ∧ ∀i∈S g,(V g).eval (x i)=word i) : E.card≤C := by
  classical
  by_cases ex : ∃g : E,V g≠0
  swap
  · push Not at ex
    have sub : univ.map V ⊆ ({0} : Finset F[X]) := by
      intro v h
      obtain ⟨g,_,rfl⟩ := mem_map.mp h
      simpa using ex g
    simpa using (card_le_card sub).trans (by simpa using hc)
  obtain ⟨v,nv⟩ := ex
  obtain ⟨H,nh,solH,minimum⟩ := exists_minimal σ l r ⟨_,nv,sol v⟩
  choose Q _ eq using fun g => (minimal_generator σ l r H nh nl solH minimum (V g)).mp (sol g)
  have inj : Function.Injective Q := by
    intro s t st
    apply V.injective
    rw [eq s,eq t,st]
  have units i := generator_avoids_fixed_nodes σ l r H nh solH minimum (x i) (fixed i)
  have hk := divisor H nh solH
  let L := closePolynomialSet x (fun i => word i/H.eval (x i)) (d+1) A
  have finite : L.Finite := (closePolynomialSet_finite_and_ncard_mul_choose_le x _ ha).1
  let f : E ↪ F[X] := ⟨Q,inj⟩
  have sub : univ.map f ⊆ finite.toFinset := by
    intro z hz
    obtain ⟨g,_,rfl⟩ := mem_map.mp hz
    apply finite.mem_toFinset.mpr
    have qd : (Q g).natDegree≤d := by
      by_cases z : Q g=0
      · simp [z]
      · have t := (fit g).1
        rw [eq g,natDegree_mul nh z] at t
        omega
    refine ⟨Polynomial.degree_le_natDegree.trans_lt (by change ((Q g).natDegree : WithBot ℕ)<(↑(d+1):WithBot ℕ); exact_mod_cast Nat.lt_succ_of_le qd),(agree _ g.property).trans (card_le_card ?_)⟩
    intro i hi
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    change (Q g).eval (x i)=word i/H.eval (x i)
    apply (eq_div_iff (units i)).mpr
    have hi' := (fit g).2 i hi
    rw [eq g,eval_mul,mul_comm] at hi'
    exact hi'
  have b := cap x (fun i => word i/H.eval (x i))
  change L.ncard ≤ C at b
  rw [Set.ncard_eq_toFinset_card _ finite] at b
  simpa using (card_le_card sub).trans b
#print axioms high_semilinear
#print axioms orbit_divisor
end
end ProximityPrize.SubmissionLower.Genuine6969.IntermediateDivisor
