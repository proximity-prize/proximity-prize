/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import Mathlib.Tactic

namespace Genuine.Triple
open Finset
open scoped BigOperators Classical
noncomputable section
variable {G I : Type*} [Fintype G] [Fintype I]

private theorem moment (b : G → I → ℕ) :
    ∑ i, (∑ g, b g i)^3 =
      ∑ g, ∑ h, ∑ k, ∑ i, b g i * b h i * b k i := by
  calc
    _ = ∑ i, ∑ g, ∑ h, ∑ k, b g i * b h i * b k i := by
      apply sum_congr rfl
      intro i _
      simp only [pow_succ, pow_zero, one_mul, sum_mul, mul_sum]
      apply sum_congr rfl; intro x _
      apply sum_congr rfl; intro y _
      apply sum_congr rfl; intro z _
      ring
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro g _
      rw [sum_comm]
      apply sum_congr rfl
      intro h _
      rw [sum_comm]

/-- A tangent minorant at any integer u gives an exact finite-list obstruction.
A triple may exceed d common nodes only for a pencil exception. Each distinct
ordered pair has at most B such completions. -/
theorem cubic (b : G → I → ℕ) (a d B u : ℕ)
    (ag : ∀g, a ≤ ∑ i, b g i)
    (exc : G → G → G → Prop)
    (pencil : ∀g h, g≠h → (univ.filter (fun k => exc g h k)).card ≤ B)
    (triple : ∀g h k, g≠h → ¬exc g h k → ∑ i, b g i*b h i*b k i ≤ d)
    (triv : ∀g h k, ∑ i, b g i*b h i*b k i ≤ Fintype.card I)
    (hd : d ≤ Fintype.card I) :
    3*u^2*(Fintype.card G*a) ≤
      2*u^3*Fintype.card I + (Fintype.card G)^3*d +
        (B+1)*(Fintype.card G)^2*(Fintype.card I-d) := by
  classical
  let n := Fintype.card I
  let m := Fintype.card G
  let s (i:I) := ∑ g, b g i
  let r (g h k:G) := ∑ i, b g i*b h i*b k i
  have cap1 (g h : G) : ∑ k, r g h k ≤ m*d +
      B*(n-d) + (if g=h then m*(n-d) else 0) := by
    by_cases e : g=h
    · have hr : ∑ k, r g h k ≤ ∑ _k:G, n := sum_le_sum (fun k _ => triv g h k)
      have hs : n=d+(n-d) := by dsimp [n]; omega
      simp only [sum_const,card_univ,nsmul_eq_mul] at hr
      rw [if_pos e]; dsimp [m]
      nlinarith only [hr, congrArg (fun z => Fintype.card G*z) hs, Nat.zero_le (B*(n-d))]
    · let C := univ.filter (fun k => exc g h k)
      have hp : C.card ≤ B := pencil g h e
      have local_bound (k:G) : r g h k ≤ d+(if k∈C then n-d else 0) := by
        by_cases hk : k∈C
        · rw [if_pos hk, Nat.add_sub_of_le hd]; exact triv g h k
        · rw [if_neg hk, add_zero]
          exact triple g h k e (by simpa [C] using hk)
      have hr := sum_le_sum (s:=univ) (fun k _ => local_bound k)
      rw [if_neg e,add_zero]
      calc
        _ ≤ _ := hr
        _ = m*d+C.card*(n-d) := by
          rw [sum_add_distrib]
          simp [m]
        _ ≤ _ := by gcongr
  have cap2 (g:G) : ∑ h, ∑ k, r g h k ≤ m*(m*d+B*(n-d)) + m*(n-d) := by
    apply (sum_le_sum (s:=univ) (fun h _ => cap1 g h)).trans_eq
    simp [sum_add_distrib,m]
  have cap3 : ∑ g, ∑ h, ∑ k, r g h k ≤ m^3*d+(B+1)*m^2*(n-d) := by
    apply (sum_le_sum (s:=univ) (fun g _ => cap2 g)).trans_eq
    simp [m]; ring
  have mass : m*a ≤ ∑ i, s i := by
    simp only [s,sum_comm (f:=fun i g => b g i)]
    exact (by simpa [m] using sum_le_sum (s:=univ) (fun g _ => ag g))
  have point (i:I) : 3*u^2*s i ≤ (s i)^3+2*u^3 := by
    have sq := sq_nonneg ((s i:ℤ)-(u:ℤ))
    have mul := mul_nonneg sq (show (0:ℤ)≤s i+2*(u:ℤ) by positivity)
    zify
    nlinarith only [mul]
  have low : 3*u^2*(m*a) ≤ ∑ i, (s i)^3 + 2*u^3*n := by
    apply (Nat.mul_le_mul_left _ mass).trans
    rw [mul_sum]
    apply (sum_le_sum (s:=univ) (fun i _ => point i)).trans_eq
    simp [sum_add_distrib,n,Nat.mul_comm]
  have eqm : ∑ i, (s i)^3 = ∑ g, ∑ h, ∑ k, r g h k := moment b
  dsimp only [m,n] at *
  omega

end
#print axioms cubic
end Genuine.Triple
