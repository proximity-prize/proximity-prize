/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833LinearKernel
import ProximityPrize.SubmissionLower.Mid6833FrobeniusCounting
namespace Frontier.LinearKernel
open Polynomial Finset KoalaFrontier
open scoped Polynomial Classical
noncomputable section
variable {K I : Type*} [Field K] [Fintype I]

/-- From a degree-one two-sided seed row to a single received word. A
nonpolynomial rational slope makes the normalized seed-to-polynomial map injective. -/
theorem normalized_moment (σ : K →+* K) (x : I ↪ K) (fixed : ∀ i, σ (x i)=x i)
    (u v : I → K) (a b B L R : K[X]) (E : Finset K) (P : K → K[X])
    (S : K → Finset I) (A w δ k : ℕ) (hb : b≠0)
    (da : a.natDegree≤δ) (dl : L.natDegree≤w+δ)
    (compatible : a.map σ*R=b*L.map σ)
    (row : ∀ g∈E, a*P g+b*(P g).map σ=B+C g*L+C (σ g)*R)
    (ags : ∀ g∈E, A≤(S g).card)
    (deg : ∀ g∈E, (P g).natDegree≤w)
    (value : ∀ g∈E, ∀ i∈S g, (P g).eval (x i)=u i+g*v i)
    (slope : ∀ g∈E, ∀ i∈S g, a.eval (x i)*v i=L.eval (x i))
    (noSlope : ¬∃ V : K[X], V.natDegree≤w ∧ a*V=L)
    (save : ∀ H : K[X], H≠0 → Solves σ b (-(a.map σ)) H → k≤H.natDegree)
    (g₀ g₁ : E) (ne : g₁ ≠ g₀) :
    (E.card*A)^2 ≤ Fintype.card I*(E.card*A+E.card*(E.card-1)*(w+δ-k)) := by
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
  have agree (g : E) : ∃ T : Finset I, A≤T.card ∧ ∀ i∈T,
      (Q g).eval (x i)=a.eval (x i)*(u i+(g₀:K)*v i-(P g₀).eval (x i)) := by
    refine ⟨S g,ags _ g.property,?_⟩
    intro i hi
    simp only [Q,eval_sub,eval_mul,eval_C,value g g.property i hi,← slope g g.property i hi]
    ring
  simpa only [Fintype.card_coe] using frobenius_list_bound σ b (-(a.map σ)) 0 x fixed Q inj g₀ 
    ⟨g₁,fun eq => ne (inj eq)⟩ _ A (w+δ) k hb rows save dc agree

theorem target_cap (M δ k : ℕ) (hk : 7832+δ ≤ k)
    (moment : (M*179740)^2 ≤ 262144*(M*179740+M*(M-1)*(131071+δ-k))) : M ≤ 143543 := by
  apply integer_list_cap M 262144 179740 123239 143543 (by decide) (by decide) (by decide)
  exact moment.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _))
#print axioms normalized_moment
#print axioms target_cap
end
end Frontier.LinearKernel
