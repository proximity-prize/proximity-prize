/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833OrbitChain
import ProximityPrize.SubmissionLower.Mid6833Johnson

namespace KoalaFrontier
open Polynomial Finset
open scoped Polynomial BigOperators
variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]

/-- Combines translation, division by a minimum-degree solution, and list counting
    for any injective family satisfying one affine semilinear equation. -/
theorem frobenius_list_bound (σ : K →+* K) (L R O : K[X])
    (x : I ↪ K) (fixed : ∀ i, σ (x i)=x i) (Q : J → K[X]) (inj : Function.Injective Q)
    (r : J) (varies : ∃ g, Q g≠Q r) (W : I → K) (A B k : ℕ)
    (hL : L≠0) (rows : ∀ g, L*(Q g).map σ=R*Q g+O)
    (save : ∀ H : K[X], H≠0 → Solves σ L R H → k≤H.natDegree)
    (degree : ∀ g, (Q g-Q r).natDegree≤B)
    (good : ∀ g, ∃ E : Finset I, A≤E.card ∧ ∀ i∈E, (Q g).eval (x i)=W i) :
    (Fintype.card J*A)^2 ≤ Fintype.card I*
      (Fintype.card J*A+Fintype.card J*(Fintype.card J-1)*(B-k)) := by
  classical
  obtain ⟨H,T,u,hn,hs,_,fac,agree⟩ :=
    normalized_affine_family σ L R Q r x W fixed hL O rows varies
  apply polynomial_witness_bound x T _ u A (B-k)
  · intro j
    have v := degree j
    rw [(fac j).2] at v
    exact (quotient_degree_bound hn B v).trans (Nat.sub_le_sub_left (save H hn hs) _)
  · intro j
    obtain ⟨E,cap,ev⟩ := good j
    exact ⟨E,cap,fun i hi => (agree j i).mp (ev i hi)⟩
  · intro j j' eqt
    apply inj
    have e := (fac j).2
    rw [eqt,← (fac j').2] at e
    exact sub_left_inj.mp e

/-- A uniform m-step pole-chain class of affine rows. The comparison degree
    B may be furnished by any argument, including the leading-term bound. -/
theorem chain_list_bound (σ : K →+* K) (m d : ℕ) (a : ℕ → K)
    (fresh : ∀ i ≤ m, ∀ j ≤ m, i ≠ j → a i ≠ a j)
    (step : ∀ i < m, σ (a i)=a (i+1))
    (O : K[X]) (x : I ↪ K) (fixed : ∀ i, σ (x i)=x i)
    (Q : J → K[X]) (inj : Function.Injective Q) (r : J) (varies : ∃ g, Q g≠Q r)
    (W : I → K) (A B : ℕ)
    (rows : ∀ g, (X-C (a 0))^d*(Q g).map σ=(X-C (a m))^d*Q g+O)
    (degree : ∀ g, (Q g-Q r).natDegree ≤ B)
    (good : ∀ g, ∃ E : Finset I, A≤E.card ∧ ∀ i∈E, (Q g).eval (x i)=W i) :
    (Fintype.card J*A)^2 ≤ Fintype.card I*
      (Fintype.card J*A+Fintype.card J*(Fintype.card J-1)*(B-m*d)) := by
  have h := orbit_chain σ m d a fresh step
  exact frobenius_list_bound σ _ _ O x fixed Q inj r varies W A B (m*d)
    (pow_ne_zero d (X_sub_C_ne_zero _)) rows
    (fun Z hz sol => h.2.1.symm.trans_le (natDegree_le_of_dvd (h.2.2 Z sol) hz)) degree good

#print axioms chain_list_bound

/-- Convert the second moment into a concrete list cap without trusting a division
    or a floating-point Johnson radius. -/
theorem integer_list_cap (M n A D L : ℕ) (ad : D≤A) (slope : n*D<A^2)
    (limit : n*(A-D)<(L+1)*(A^2-n*D))
    (moment : (M*A)^2≤n*(M*A+M*(M-1)*D)) : M≤L := by
  by_cases mz : M=0
  · simp [mz]
  obtain ⟨t,ht⟩ := Nat.exists_eq_succ_of_ne_zero mz
  subst M
  simp only [Nat.add_one_sub_one] at moment
  have reduced : (t+1)*A^2 ≤ n*(A+t*D) := by
    apply Nat.le_of_mul_le_mul_left (c := t+1) _ (by omega)
    calc
      (t+1)*((t+1)*A^2) = ((t+1)*A)^2 := by ring
      _ ≤ _ := moment
      _ = (t+1)*(n*(A+t*D)) := by simp only [Nat.succ_eq_add_one]; ring
  by_contra! tooBig
  have contra := calc
    n*(A-D) < (L+1)*(A^2-n*D) := limit
    _ ≤ (t+1)*(A^2-n*D) := Nat.mul_le_mul_right _ tooBig
  zify [ad,slope.le] at contra reduced
  nlinarith

#print axioms frobenius_list_bound
#print axioms integer_list_cap
end KoalaFrontier
