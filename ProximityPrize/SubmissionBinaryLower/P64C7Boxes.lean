import ProximityPrize.SubmissionBinaryLower.P64C7Truncation
import ProximityPrize.SubmissionBinaryLower.P64C6Boxes
import ProximityPrize.SubmissionBinaryLower.P64C6Weights

/-!
# Coefficient boxes in the bounded-pole rank comparison
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C7Boxes

open P64C6Boxes P64Found

def inputBox (s h q e : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  box h (fun _ => s) (fun b => e + 1 - q * b)

def broadBox (s h q e : ℕ) : Finset (ℕ × ℕ × ℕ) := inputBox s (h + s) q (e + q * s)

def multiplesBox (s q d e : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  box s (fun _ => s) (fun b => e + q * s + 1 - (d + q * b))

lemma mem_input (s h q e a b l : ℕ) :
    (a, b, l) ∈ inputBox s h q e ↔ a < s ∧ b < h ∧ q * b + l ≤ e := by
  rw [inputBox, mem_box]
  omega

lemma mem_broad (s h q e a b l : ℕ) :
    (a, b, l) ∈ broadBox s h q e ↔ a < s ∧ b < h + s ∧ q * b + l ≤ e + q * s :=
  mem_input s (h + s) q (e + q * s) a b l

lemma mem_multiples (s q d e a b l : ℕ) :
    (a, b, l) ∈ multiplesBox s q d e ↔ a < s ∧ b < s ∧ d + q * b + l ≤ e + q * s := by
  rw [multiplesBox, mem_box]
  omega

lemma card_input (s h q e : ℕ) :
    (inputBox s h q e).card = ∑ b ∈ Finset.range h, s * (e + 1 - q * b) := card_box _ _ _

lemma card_multiples (s q d e : ℕ) :
    (multiplesBox s q d e).card =
      ∑ b ∈ Finset.range s, s * (e + q * s + 1 - (d + q * b)) := card_box _ _ _

private def liftTag (p : ℕ × ℕ) : ℕ ↪ ℕ × ℕ × ℕ where
  toFun l := (p.1, p.2, l)
  inj' _ _ he := congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) he

def liftSlice (p : ℕ × ℕ) (L : ℕ) : Finset (ℕ × ℕ × ℕ) := (Finset.range L).map (liftTag p)

lemma mem_liftSlice (p : ℕ × ℕ) (L a b l : ℕ) :
    (a, b, l) ∈ liftSlice p L ↔ (a, b) = p ∧ l < L := by
  simp only [liftSlice, Finset.mem_map, Finset.mem_range]
  constructor
  · rintro ⟨l', hl, he⟩
    have h1 : p.1 = a := congrArg (fun t : ℕ × ℕ × ℕ => t.1) he
    have h2 : p.2 = b := congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) he
    have h3 : l' = l := congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) he
    exact ⟨Prod.ext h1.symm h2.symm, h3 ▸ hl⟩
  · rintro ⟨he, hl⟩
    subst p
    exact ⟨l, hl, rfl⟩

def lifted (Λ : Finset (ℕ × ℕ)) (q E : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  Λ.biUnion fun p => liftSlice p (E + 1 - q * p.2)

lemma mem_lifted (Λ : Finset (ℕ × ℕ)) (q E a b l : ℕ) :
    (a, b, l) ∈ lifted Λ q E ↔ (a, b) ∈ Λ ∧ q * b + l ≤ E := by
  simp only [lifted, Finset.mem_biUnion, mem_liftSlice]
  constructor
  · rintro ⟨p, hp, he, hl⟩
    subst p
    exact ⟨hp, by change l < E + 1 - q * b at hl; omega⟩
  · rintro ⟨hp, hl⟩
    exact ⟨(a, b), hp, rfl, by change l < E + 1 - q * b; omega⟩

theorem card_lifted (Λ : Finset (ℕ × ℕ)) (q E : ℕ) :
    (lifted Λ q E).card = ∑ p ∈ Λ, (E + 1 - q * p.2) := by
  rw [lifted, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro p _
    simp [liftSlice]
  · intro p _ p' _ hne
    apply Finset.disjoint_left.mpr
    rintro ⟨a, b, l⟩ h1 h2
    exact hne (((mem_liftSlice _ _ _ _ _).mp h1).1.symm.trans
      ((mem_liftSlice _ _ _ _ _).mp h2).1)

theorem lifted_lower (Λ : Finset (ℕ × ℕ)) (q E ν : ℕ)
    (hΛ : ∀ p ∈ Λ, p.2 < ν) :
    Λ.card * (E + 1 - q * (ν - 1)) ≤ (lifted Λ q E).card := by
  rw [card_lifted]
  calc Λ.card * (E + 1 - q * (ν - 1)) = ∑ _ ∈ Λ, (E + 1 - q * (ν - 1)) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      have hmul := Nat.mul_le_mul_left q (show p.2 ≤ ν - 1 by have := hΛ p hp; omega)
      omega

variable {F : Type*} [Field F]

lemma lifted_support (Λ : Finset (ℕ × ℕ)) (q E : ℕ)
    (R : Polynomial (Polynomial (Polynomial F))) (hR : R ∈ supp (lifted Λ q E))
    (a b : ℕ) (hp : (a, b) ∉ Λ) : (R.coeff b).coeff a = 0 := by
  ext l
  exact hR a b l (fun ht => hp ((mem_lifted Λ q E a b l).mp ht).1)

end P64C7Boxes
end ProximityPrize.SubmissionBinaryLower
