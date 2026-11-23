import Mathlib.Tactic

set_option autoImplicit false

namespace KoalaH2430Contact

/-- A finite partition with an integer threshold on each cell. -/
inductive Tree where
  | leaf (threshold : ℕ)
  | splitX (mid : ℕ) (left right : Tree)
  | splitZ (mid : ℕ) (left right : Tree)

def Tree.Checked (P : ℕ → ℕ → ℕ → ℕ → ℕ → Prop) :
    Tree → ℕ → ℕ → ℕ → ℕ → Prop
  | .leaf r, a,b,c,d => P a b c d r
  | .splitX m l h, a,b,c,d => l.Checked P a m c d ∧ h.Checked P (m+1) b c d
  | .splitZ m l h, a,b,c,d => l.Checked P a b c m ∧ h.Checked P a b (m+1) d

private def Tree.decidable {P : ℕ → ℕ → ℕ → ℕ → ℕ → Prop}
    [∀ a b c d r, Decidable (P a b c d r)] :
    (T : Tree) → (a b c d : ℕ) → Decidable (T.Checked P a b c d)
  | .leaf r, a,b,c,d => inferInstanceAs (Decidable (P a b c d r))
  | .splitX m l h, a,b,c,d =>
    @instDecidableAnd _ _ (l.decidable a m c d) (h.decidable (m+1) b c d)
  | .splitZ m l h, a,b,c,d =>
    @instDecidableAnd _ _ (l.decidable a b c m) (h.decidable a b (m+1) d)

instance {P : ℕ → ℕ → ℕ → ℕ → ℕ → Prop}
    [∀ a b c d r, Decidable (P a b c d r)] (T : Tree) (a b c d : ℕ) :
    Decidable (T.Checked P a b c d) := T.decidable a b c d

theorem Tree.locate {P : ℕ → ℕ → ℕ → ℕ → ℕ → Prop} (T : Tree)
    {a b c d x z : ℕ} (h : T.Checked P a b c d)
    (hax:a≤x) (hxb:x≤b) (hcz:c≤z) (hzd:z≤d) :
    ∃ A B C D r, P A B C D r ∧ A≤x ∧ x≤B ∧ C≤z ∧ z≤D := by
  induction T generalizing a b c d with
  | leaf r => exact ⟨a,b,c,d,r,h,hax,hxb,hcz,hzd⟩
  | splitX m l r hl hr =>
    by_cases hm : x≤m
    · exact hl h.1 hax hm hcz hzd
    · exact hr h.2 (by omega) hxb hcz hzd
  | splitZ m l r hl hr =>
    by_cases hm : z≤m
    · exact hl h.1 hax hxb hcz hm
    · exact hr h.2 hax hxb (by omega) hzd

#print axioms Tree.locate
end KoalaH2430Contact
