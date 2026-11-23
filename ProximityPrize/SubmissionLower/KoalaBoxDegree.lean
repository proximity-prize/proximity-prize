import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertComap
import ArkLib.ToMathlib.RingTheory.MvPolynomial.MonomialMap

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace SplitCut.BoxDegree
noncomputable section
open MvPolynomial Filter
open scoped BigOperators Pointwise Polynomial
abbrev Idx := Option (Fin 2)
abbrev Exp := Idx →₀ ℕ

def exps (a b c : ℕ) : Set Exp :=
  {m | m none ≤ a ∧ m (some 0) ≤ b ∧ m (some 1) ≤ c}

def slots (a b c : ℕ) : exps a b c ≃ Fin (a+1) × Fin (b+1) × Fin (c+1) where
  toFun m := ⟨⟨_, Nat.lt_succ_of_le m.2.1⟩, ⟨_, Nat.lt_succ_of_le m.2.2.1⟩,
    ⟨_, Nat.lt_succ_of_le m.2.2.2⟩⟩
  invFun p := ⟨Finsupp.equivFunOnFinite.symm (fun i : Idx => i.elim p.1.val ![p.2.1.val,p.2.2.val]),
    ⟨Nat.le_of_lt_succ p.1.isLt, Nat.le_of_lt_succ p.2.1.isLt,
      Nat.le_of_lt_succ p.2.2.isLt⟩⟩
  left_inv m := by
    apply Subtype.ext
    ext i
    cases i with
    | none => rfl
    | some i => fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨a,b,c⟩; rfl

noncomputable instance (a b c : ℕ) : Fintype (exps a b c) := Fintype.ofEquiv _ (slots a b c).symm

variable {F : Type*} [Field F]
abbrev space (F : Type*) [Field F] (a b c : ℕ) :=
  MvPolynomial.restrictSupport (σ := Idx) F (exps a b c)

instance spaceFinite (a b c : ℕ) : Module.Finite F (space F a b c) :=
  Module.Finite.of_basis (basisRestrictSupport F (exps a b c))

theorem size (a b c : ℕ) : Module.finrank F (space F a b c) = (a+1)*(b+1)*(c+1) := by
  rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport F (exps a b c)),
    Nat.card_congr (slots a b c)]
  simp [Nat.card_eq_fintype_card, Nat.mul_assoc]

theorem add_box {a b c u v w : ℕ} :
    exps a b c + exps u v w ⊆ exps (a+u) (b+v) (c+w) := by
  rintro _ ⟨m, hm, n, hn, rfl⟩
  exact ⟨Nat.add_le_add hm.1 hn.1, Nat.add_le_add hm.2.1 hn.2.1, Nat.add_le_add hm.2.2 hn.2.2⟩

theorem mul_box {a b c u v w : ℕ} {f g : MvPolynomial Idx F}
    (hf : f ∈ space F a b c) (hg : g ∈ space F u v w) :
    f*g ∈ space F (a+u) (b+v) (c+w) := by
  apply restrictSupport_mono F add_box
  rw [restrictSupport_add]
  exact Submodule.mul_mem_mul hf hg


theorem axis {a b c : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c) (i : Idx) :
    Finsupp.single i 1 ∈ exps a b c := by
  unfold exps
  simp only [Set.mem_ofPred_eq, Finsupp.single_apply]
  split_ifs <;> omega





end
end SplitCut.BoxDegree
