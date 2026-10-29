import ProximityPrize.SubmissionBinaryLower.P64C6Flat

/-!
# Finite coefficient boxes for flat interpolation

Exponent triples are `(a,b,l)` for `X^a Y^b Z^l`. The parameter `q` is the
weight of `Y` in the `(Y,Z)` cap, including the Frobenius-twisted case.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6Boxes

private def tag (b : ℕ) : ℕ × ℕ ↪ ℕ × ℕ × ℕ where
  toFun p := (p.1, b, p.2)
  inj' p r h := Prod.ext
    (congrArg (fun t : ℕ × ℕ × ℕ => t.1) h)
    (congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) h)

def slice (b A L : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range A ×ˢ Finset.range L).map (tag b)

lemma mem_slice (b A L a b' l : ℕ) :
    (a, b', l) ∈ slice b A L ↔ b' = b ∧ a < A ∧ l < L := by
  simp only [slice, Finset.mem_map, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨a', l'⟩, ⟨ha, hl⟩, he⟩
    have h := Prod.mk.inj he
    have h' := Prod.mk.inj h.2
    exact ⟨h'.1.symm, h.1 ▸ ha, h'.2 ▸ hl⟩
  · rintro ⟨rfl, ha, hl⟩
    exact ⟨(a, l), ⟨ha, hl⟩, rfl⟩

lemma card_slice (b A L : ℕ) : (slice b A L).card = A * L := by
  simp [slice]

def box (h : ℕ) (A L : ℕ → ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range h).biUnion fun b => slice b (A b) (L b)

lemma mem_box (h : ℕ) (A L : ℕ → ℕ) (a b l : ℕ) :
    (a, b, l) ∈ box h A L ↔ b < h ∧ a < A b ∧ l < L b := by
  simp only [box, Finset.mem_biUnion, Finset.mem_range, mem_slice]
  constructor
  · rintro ⟨b', hb, he, ha, hl⟩
    subst b'
    exact ⟨hb, ha, hl⟩
  · rintro ⟨hb, ha, hl⟩
    exact ⟨b, hb, rfl, ha, hl⟩

theorem card_box (h : ℕ) (A L : ℕ → ℕ) :
    (box h A L).card = ∑ b ∈ Finset.range h, A b * L b := by
  rw [box, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun b _ => card_slice b (A b) (L b)
  · intro b _ b' _ hne
    apply Finset.disjoint_left.mpr
    rintro ⟨a, c, l⟩ h1 h2
    have he1 := (mem_slice b (A b) (L b) a c l).mp h1
    have he2 := (mem_slice b' (A b') (L b') a c l).mp h2
    exact hne (he1.1.symm.trans he2.1)

/-- Global auxiliary: outer degree `< h`, spatial weight `≤ W`, parameter weight `≤ e`. -/
def auxiliary (D W q e h : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  box h (fun b => W + 1 - D * b) (fun b => e + 1 - q * b)

lemma mem_auxiliary (D W q e h a b l : ℕ) :
    (a, b, l) ∈ auxiliary D W q e h ↔
      b < h ∧ a + D * b ≤ W ∧ q * b + l ≤ e := by
  rw [auxiliary, mem_box]
  omega

theorem card_auxiliary (D W q e h : ℕ) :
    (auxiliary D W q e h).card =
      ∑ b ∈ Finset.range h, (W + 1 - D * b) * (e + 1 - q * b) := card_box _ _ _

/-- Line equations: total normal order `< s`, parameter weight `≤ e`. -/
def conditions (s q e : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  box s (fun b => s - b) (fun b => e + 1 - q * b)

lemma mem_conditions (s q e a b l : ℕ) :
    (a, b, l) ∈ conditions s q e ↔ a + b < s ∧ q * b + l ≤ e := by
  rw [conditions, mem_box]
  omega

theorem card_conditions (s q e : ℕ) :
    (conditions s q e).card = ∑ b ∈ Finset.range s, (s - b) * (e + 1 - q * b) :=
  card_box _ _ _

/-- A rectangle inside the auxiliary box gives its leading quadratic lower bound. -/
theorem auxiliary_lower (D W q e h : ℕ) :
    h * (W - h * D) * (e - q * h) ≤ (auxiliary D W q e h).card := by
  rw [card_auxiliary]
  calc h * (W - h * D) * (e - q * h) =
        ∑ b ∈ Finset.range h, (W - h * D) * (e - q * h) := by simp [Nat.mul_assoc]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro b hb
      have hbh : b ≤ h := Nat.le_of_lt (Finset.mem_range.mp hb)
      have hD := Nat.mul_le_mul_left D hbh
      have hq := Nat.mul_le_mul_left q hbh
      apply Nat.mul_le_mul
      · rw [Nat.mul_comm h D]
        omega
      · omega

end P64C6Boxes
end ProximityPrize.SubmissionBinaryLower
