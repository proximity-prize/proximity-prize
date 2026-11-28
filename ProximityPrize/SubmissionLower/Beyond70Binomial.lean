import ProximityPrize.SubmissionLower.Pack_K1_14_3_2_7Proof
import Mathlib.Data.Nat.Prime.Factorial

namespace Beyond70Binomial
open CJ0

local instance : Fact (Nat.Prime CJ0.p) := ⟨KoalaBear.is_prime⟩
abbrev F := ZMod CJ0.p

private theorem fact_ne_zero {a : ℕ} (ha : a < CJ0.p) : ((a.factorial : ℕ) : F) ≠ 0 := by
  intro hz
  have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz
  exact (not_le_of_gt ha) (KoalaBear.is_prime.dvd_factorial.mp hd)

def totalFact (r : Jet) : ℕ := r.a.factorial * r.b.factorial * r.c.factorial

private theorem fact_product (r s : Jet) (hq : r.q = s.q)
    (hb : s.b ≤ r.b) (hc : s.c ≤ r.c) :
    s.a.choose r.a * (s.a-r.a).choose (r.b-s.b) * totalFact r =
      totalFact s * r.b.choose s.b * r.c.choose s.c := by
  have eq : r.a + (r.b-s.b) + (r.c-s.c) = s.a := by unfold Jet.q at hq; omega
  have ha : r.a ≤ s.a := by omega
  have hd : r.b-s.b ≤ s.a-r.a := by omega
  have hrem : s.a-r.a-(r.b-s.b)=r.c-s.c := by omega
  have hA := Nat.choose_mul_factorial_mul_factorial ha
  have hD := Nat.choose_mul_factorial_mul_factorial hd
  have hB := Nat.choose_mul_factorial_mul_factorial hb
  have hC := Nat.choose_mul_factorial_mul_factorial hc
  rw [hrem] at hD
  apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (r.b-s.b))
  apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (r.c-s.c))
  unfold totalFact
  calc
    _ = (s.a.choose r.a * r.a.factorial *
        ((s.a-r.a).choose (r.b-s.b) * (r.b-s.b).factorial * (r.c-s.c).factorial)) *
          r.b.factorial * r.c.factorial := by ring
    _ = s.a.factorial * r.b.factorial * r.c.factorial := by rw [hD, hA]
    _ = _ := by rw [← hB, ← hC]; ring

theorem scaled_entry (r s : Jet) (hq : r.q = s.q) :
    CJ0.blockEntry r s * (totalFact r : F) * (-1 : F)^s.c =
      (totalFact s : F) * (-1 : F)^r.c * (r.b.choose s.b : F) * (r.c.choose s.c : F) := by
  by_cases hb : s.b ≤ r.b
  · by_cases hc : s.c ≤ r.c
    · have heq : r.a + (r.b-s.b) + (r.c-s.c) = s.a := by unfold Jet.q at hq; omega
      have hp := congrArg (fun n : ℕ => (n : F)) (fact_product r s hq hb hc)
      push_cast at hp
      simp [CJ0.blockEntry, hb, hc, heq]
      have hsign : (-1 : F)^(r.c-s.c) * (-1 : F)^s.c = (-1 : F)^r.c := by
        rw [← pow_add, Nat.sub_add_cancel hc]
      calc
        _ = (-1 : F)^r.c * ((s.a.choose r.a : F) *
            ((s.a-r.a).choose (r.b-s.b) : F) * (totalFact r : F)) := by
          rw [← hsign]
          ring
        _ = _ := by rw [hp]; ring
    · simp [CJ0.blockEntry, hc, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hc)]
  · simp [CJ0.blockEntry, hb, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hb)]


/-- On one row fiber, only the third coordinates of contributing columns determine
the dimension. -/
theorem fiber_rank {R S : Type*} [Fintype R] [Fintype S]
    (r : R → Jet) (s : S → Jet) (q b c₀ width : ℕ)
    (hp : q < CJ0.p) (hrq : ∀ i, (r i).q = q) (hsq : ∀ j, (s j).q = q)
    (hb : ∀ i, (r i).b = b)
    (hwidth : ∀ i j, CJ0.blockEntry (r i) (s j) ≠ 0 →
        c₀ ≤ (s j).c ∧ (s j).c < c₀ + width) :
    (Matrix.of (fun i j => CJ0.blockEntry (r i) (s j))).rank ≤ width := by
  classical
  let L : Matrix R (Fin width) F := fun i k =>
    (-1 : F)^(r i).c * ((r i).c.choose (c₀ + k) : F) / (totalFact (r i) : F)
  let M : Matrix (Fin width) S F := fun k j =>
    if c₀ + k.val = (s j).c then
      (totalFact (s j) : F) * (b.choose (s j).b : F) / (-1 : F)^(s j).c
    else 0
  have hfac : L * M = Matrix.of (fun i j => CJ0.blockEntry (r i) (s j)) := by
    ext i j
    change (L * M) i j = CJ0.blockEntry (r i) (s j)
    rw [Matrix.mul_apply]
    by_cases h : c₀ ≤ (s j).c ∧ (s j).c < c₀ + width
    · let j₀ : Fin width := ⟨(s j).c - c₀, by omega⟩
      have hj₀ : c₀ + j₀.val = (s j).c := by dsimp [j₀]; omega
      rw [Finset.sum_eq_single j₀]
      · simp [L, M, hj₀]
        have hscale := scaled_entry (r i) (s j) ((hrq i).trans (hsq j).symm)
        rw [hb i] at hscale
        have hr : (totalFact (r i) : F) ≠ 0 := by
          have hdeg := hrq i
          unfold Jet.q at hdeg
          simp only [totalFact, Nat.cast_mul]
          exact mul_ne_zero (mul_ne_zero (fact_ne_zero (by omega))
            (fact_ne_zero (by omega))) (fact_ne_zero (by omega))
        have hs : (-1 : F)^(s j).c ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
        field_simp
        linear_combination -hscale
      · intro k _ hk
        have hne : c₀ + k.val ≠ (s j).c := by
          intro he
          apply hk
          apply Fin.ext
          omega
        simp [M, hne]
      · simp
    · have hz : CJ0.blockEntry (r i) (s j) = 0 := by
        by_contra hn
        exact h (hwidth i j hn)
      rw [hz]
      apply Finset.sum_eq_zero
      intro k _
      have hk := k.isLt
      have hn : c₀ + k.val ≠ (s j).c := by omega
      simp [M, hn]
  rw [← hfac]
  exact (Matrix.rank_mul_le_left _ _).trans (by simpa using L.rank_le_card_width)

#print axioms fiber_rank

end Beyond70Binomial
