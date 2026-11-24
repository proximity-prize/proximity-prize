import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertComap
import ArkLib.ToMathlib.RingTheory.MvPolynomial.MonomialMap
import ProximityPrize.SubmissionLower.KoalaCutGeometry
import ArkLib.Data.MvPolynomial.WeightAtMost
import Mathlib.LinearAlgebra.Matrix.Rank
set_option Elab.async false

-- merged module KoalaBoxDegree
section Merged_KoalaBoxDegree

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

end Merged_KoalaBoxDegree

-- merged module KoalaCompression
section Merged_KoalaCompression
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace SplitCut.Compression
noncomputable section
open Polynomial Matrix MvPolynomial
open scoped BigOperators
variable {F : Type*} [Field F]
abbrev Rational (F : Type*) [Field F] := FractionRing (Polynomial F)
theorem compress_matrix {α ι : Type*} [Finite α] [Fintype ι]
    (A : Matrix α ι (Polynomial F)) (p D k : ℕ) (hk : k ≤ Fintype.card ι)
    (hA : ∀ i j, (A i j).natDegree ≤ D) (hguard : Fintype.card ι * D < k * p)
    (hker : k ≤ Module.finrank (Rational F)
      (LinearMap.ker (A.map (algebraMap (Polynomial F) (Rational F))).mulVecLin)) :
    ∃ w : ι → degreeLT F (p-D), w ≠ 0 ∧ ∀ i, ∑ j, A i j * (w j : (Polynomial F)) = 0 := by
  classical
  let E := Rational F
  let a : (Polynomial F) →+* E := algebraMap (Polynomial F) E
  let M : Matrix α ι E := A.map a
  let R := Submodule.span E (Set.range M.row)
  let m := Module.finrank E R
  let n := Fintype.card ι
  change k ≤ n at hk
  change n * D < k * p at hguard
  have hdim := M.mulVecLin.finrank_range_add_finrank_ker
  change M.rank + _ = _ at hdim
  rw [M.rank_eq_finrank_span_row, Module.finrank_pi_fintype] at hdim
  have hn : m + Module.finrank E (LinearMap.ker M.mulVecLin) = n := by
    simpa [m, n, R] using hdim
  have hm : m ≤ n-k := by
    change k ≤ Module.finrank E (LinearMap.ker M.mulVecLin) at hker
    omega
  have hD : D < p := by
    by_contra! h
    have h₁ := Nat.mul_le_mul_left n h
    have h₂ := Nat.mul_le_mul_right p hk
    omega
  obtain ⟨B, hmem, hspan, _⟩ := Submodule.exists_fun_fin_finrank_span_eq E (Set.range M.row)
  change Fin m → (ι → E) at B
  choose row hrow using hmem
  let j := Fintype.equivFin ι
  have hmargin := SplitCut.compression_guard hk hD.le hm hguard
  obtain ⟨v, hv, hvA⟩ := SplitCut.compress_rows n m p D hD hmargin
    (fun i l => A (row i) (j.symm l)) (fun _ _ => hA _ _)
  let w : ι → degreeLT F (p-D) := fun l => v (j l)
  have hw : w ≠ 0 := by
    intro h
    apply hv
    ext i : 1
    simpa [w] using congrFun h (j.symm i)
  refine ⟨w, hw, fun i => ?_⟩
  have hB (i : Fin m) : B i ⬝ᵥ (fun l => a (w l : (Polynomial F))) = 0 := by
    rw [← hrow i]
    have he : (∑ l : Fin n, A (row i) (j.symm l) * (v l : (Polynomial F))) =
        ∑ l : ι, A (row i) l * (w l : (Polynomial F)) := by
      rw [← j.sum_comp]
      simp [w]
    have hh := congrArg a ((he.symm.trans (hvA i)))
    simpa only [map_sum, map_mul, map_zero, M, Matrix.row, Matrix.map_apply, dotProduct] using hh
  let vE : ι → E := fun l => a (w l : (Polynomial F))
  have hbi : M.row i ⬝ᵥ vE = 0 := by
    have hi : M.row i ∈ Submodule.span E (Set.range B) := by
      rw [hspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    refine Submodule.span_induction (p := fun x _ => x ⬝ᵥ vE = 0) ?_ ?_ ?_ ?_ hi
    · rintro _ ⟨b, rfl⟩
      exact hB b
    · exact zero_dotProduct _
    · intro x y _ _ hx hy
      simp [add_dotProduct, hx, hy]
    · intro c x _ hx
      simp [smul_dotProduct, hx]
  apply IsFractionRing.injective (Polynomial F) E
  simpa only [map_sum, map_mul, map_zero, M, Matrix.row, Matrix.map_apply, vE, dotProduct] using hbi
open BoxDegree
private theorem card_exps (a b c : ℕ) : Fintype.card (exps a b c) = (a+1)*(b+1)*(c+1) := by
  rw [Fintype.card_congr (slots a b c)]
  simp [Nat.mul_assoc]
def evalRow {α : Type*} (S : α → (Polynomial F)) (z : α → Fin 2 → F)
    (g : α) (m : Exp) : (Polynomial F) :=
  S g ^ m none * Polynomial.C ((z g 0)^m (some 0) * (z g 1)^m (some 1))
private theorem eval_monomial_row {α : Type*} (S : α → (Polynomial F)) (z : α → Fin 2 → F)
    (g : α) (m : Exp) (a : Rational F) :
    MvPolynomial.eval (fun i : Idx => i.elim (algebraMap (Polynomial F) (Rational F) (S g))
      (fun j => algebraMap (Polynomial F) (Rational F) (Polynomial.C (z g j)))) (monomial m a) =
      algebraMap (Polynomial F) (Rational F) (evalRow S z g m) * a := by
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_option, Fin.prod_univ_two]
  simp only [Option.elim_none, Option.elim_some, evalRow, map_mul, map_pow]
  ring
theorem compress_box {α : Type*} [Finite α] (S : α → (Polynomial F)) (z : α → Fin 2 → F)
    {f : MvPolynomial Idx (Rational F)} (hf : f ≠ 0) {e v w b d p : ℕ}
    (hfit : f ∈ space (Rational F) e v w)
    (hS : ∀ g, (S g).natDegree ≤ d)
    (hroot : ∀ g, MvPolynomial.eval (fun i : Idx => i.elim (algebraMap (Polynomial F) (Rational F) (S g))
      (fun j => algebraMap (Polynomial F) (Rational F) (Polynomial.C (z g j)))) f = 0)
    (hguard : Fintype.card (exps e (v+b) (w+b))*(e*d) < ((b+1)*(b+1))*p) :
    ∃ W : exps e (v+b) (w+b) → degreeLT F (p-e*d), W ≠ 0 ∧
      ∀ g, ∑ m : exps e (v+b) (w+b), evalRow S z g m * (W m : (Polynomial F)) = 0 := by
  classical
  let E := Rational F
  let u : (Polynomial F) →+* E := algebraMap (Polynomial F) E
  let ι := exps e (v+b) (w+b)
  let A : Matrix α ι (Polynomial F) := Matrix.of (fun g m => evalRow S z g m)
  let B := space E e (v+b) (w+b)
  let C := space E 0 b b
  let coords : (ι → E) ≃ₗ[E] B := (basisRestrictSupport E ι).equivFun.symm
  let mul : C →ₗ[E] B := ((LinearMap.mulLeft E f).domRestrict _).codRestrict _ (by
    intro g
    change f * g.val ∈ _
    simpa only [Nat.add_zero] using mul_box hfit g.property)
  have hm (x : ι → E) (g : α) : (A.map u).mulVecLin x g =
      MvPolynomial.eval (fun i : Idx => i.elim (u (S g)) (fun j => u (Polynomial.C (z g j))))
        ((coords x).val) := by
    change (∑ m : ι, u (evalRow S z g m) * x m) = _
    have hx : ((coords x).val) = ∑ m : ι, monomial m.val (x m) := by
      change ((basisRestrictSupport E ι).equivFun.symm x : B).val = _
      rw [Module.Basis.equivFun_symm_apply]
      simp [MvPolynomial.coe_basisRestrictSupport_apply, MvPolynomial.smul_monomial]
    rw [hx, map_sum]
    exact Finset.sum_congr rfl fun m _ => (eval_monomial_row S z g m.val (x m)).symm
  let L := coords.symm.toLinearMap.comp mul
  have hL (x : C) : L x ∈ LinearMap.ker (A.map u).mulVecLin := by
    rw [LinearMap.mem_ker]
    funext g
    rw [hm]
    change MvPolynomial.eval _ ((coords (coords.symm (mul x))).val) = 0
    rw [LinearEquiv.apply_symm_apply]
    change MvPolynomial.eval _ (f*x.val) = 0
    rw [map_mul, hroot g, zero_mul]
  have hi : Function.Injective (L.codRestrict _ hL) := by
    intro x y hxy
    have h := congrArg (fun a : LinearMap.ker (A.map u).mulVecLin => a.val) hxy
    have he : mul x = mul y := coords.symm.injective h
    apply Subtype.ext
    exact mul_left_cancel₀ hf (congrArg Subtype.val he)
  have hker := LinearMap.finrank_le_finrank_of_injective hi
  change Module.finrank E C ≤ _ at hker
  rw [size (F:=E) 0 b b, zero_add, one_mul] at hker
  refine compress_matrix A p (e*d) ((b+1)*(b+1)) ?_ ?_ hguard hker
  · change _ ≤ Fintype.card (exps e (v+b) (w+b))
    rw [card_exps]
    have h : b+1 ≤ (e+1)*(v+b+1) := by
      simpa only [one_mul] using Nat.mul_le_mul (by omega : 1 ≤ e+1) (by omega : b+1 ≤ v+b+1)
    exact Nat.mul_le_mul h
      (by omega : b+1 ≤ w+b+1)
  · intro i j
    have h := natDegree_mul_le (p := S i ^ j.val none)
      (q := Polynomial.C ((z i 0)^j.val (some 0) * (z i 1)^j.val (some 1)))
    rw [natDegree_C, add_zero] at h
    exact h.trans (natDegree_pow_le_of_le _ (hS i) |>.trans (Nat.mul_le_mul_right _ j.2.1))
end
end SplitCut.Compression
#print axioms SplitCut.Compression.compress_matrix
#print axioms SplitCut.Compression.compress_box

end Merged_KoalaCompression
