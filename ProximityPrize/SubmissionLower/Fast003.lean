import ArkLib.Data.MvPolynomial.WeightedOrder
import ArkLib.Data.Polynomial.SpecializationAvoidance
import ArkLib.ToMathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.FLT.MasonStothers
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import ProximityPrize.SubmissionLower.Fast002
set_option Elab.async false

section PackSource_MasonSparsePlaceCore
set_option autoImplicit true
/-!
Mason height guards for a conditional few-place S-unit mechanism.

No finite S-unit/divisor count or component-cover theorem is asserted.
The all-constant case is separate: degree bounds below the characteristic
alone do not imply that one of the three derivatives is nonzero.
-/

namespace Sol1.MasonSparsePlace

open Polynomial UniqueFactorizationMonoid

variable {E : Type*} [Field E]

open Classical in
/-- A finite radical-degree bound gives all three Mason degree bounds,
provided at least one formal derivative is nonzero. -/
theorem mason_degree_add_one_le
    (a b c : E[X]) (h : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (hsum : a + b + c = 0)
    (hrad : (radical (a * b * c)).natDegree ≤ h)
    (hder : a.derivative ≠ 0 ∨ b.derivative ≠ 0 ∨ c.derivative ≠ 0) :
    a.natDegree + 1 ≤ h ∧ b.natDegree + 1 ≤ h ∧ c.natDegree + 1 ≤ h := by
  rcases Polynomial.abc ha hb hc hab hsum with hbound | hzero
  · exact ⟨hbound.1.trans hrad, hbound.2.1.trans hrad, hbound.2.2.trans hrad⟩
  · rcases hder with hda | hdb | hdc
    · exact (hda hzero.1).elim
    · exact (hdb hzero.2.1).elim
    · exact (hdc hzero.2.2).elim

/-- Explicit characteristic guard, proved from the leading coefficient:
a nonconstant polynomial of degree below p cannot have zero derivative. -/
theorem derivative_ne_zero_of_natDegree_pos_lt_char
    (p : ℕ) [CharP E p] (f : E[X])
    (hpos : 0 < f.natDegree) (hlt : f.natDegree < p) : f.derivative ≠ 0 := by
  intro hzero
  have hf : f ≠ 0 := by
    intro heq
    simp [heq] at hpos
  have hn : f.natDegree - 1 + 1 = f.natDegree := by omega
  have hcoeff : f.coeff f.natDegree * (f.natDegree : E) = 0 := by
    have heq := congrArg (fun q : E[X] ↦ q.coeff (f.natDegree - 1)) hzero
    simpa only [coeff_derivative, coeff_zero, ← Nat.cast_add_one, hn] using heq
  have hlead : f.coeff f.natDegree ≠ 0 := by
    simpa only [coeff_natDegree] using leadingCoeff_ne_zero.mpr hf
  have hcast : (f.natDegree : E) ≠ 0 := by
    intro hz
    have hdiv : p ∣ f.natDegree := (CharP.cast_eq_zero_iff E p _).mp hz
    have hd : f.natDegree = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hlt
    omega
  exact (mul_ne_zero hlead hcast) hcoeff

open Classical in
/-- Below characteristic p, the only derivative-degenerate alternative is
that all three polynomials are constant. -/
theorem mason_low_degree_or_constant
    (p : ℕ) [CharP E p] (a b c : E[X]) (h : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (hsum : a + b + c = 0)
    (hrad : (radical (a * b * c)).natDegree ≤ h)
    (hda : a.natDegree < p) (hdb : b.natDegree < p) (hdc : c.natDegree < p) :
    (a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0) ∨
      (a.natDegree + 1 ≤ h ∧ b.natDegree + 1 ≤ h ∧ c.natDegree + 1 ≤ h) := by
  by_cases hconstant : a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0
  · exact Or.inl hconstant
  · right
    apply mason_degree_add_one_le a b c h ha hb hc hab hsum hrad
    have hpositive : 0 < a.natDegree ∨ 0 < b.natDegree ∨ 0 < c.natDegree := by omega
    rcases hpositive with hpa | hpb | hpc
    · exact Or.inl (derivative_ne_zero_of_natDegree_pos_lt_char p a hpa hda)
    · exact Or.inr (Or.inl (derivative_ne_zero_of_natDegree_pos_lt_char p b hpb hdb))
    · exact Or.inr (Or.inr (derivative_ne_zero_of_natDegree_pos_lt_char p c hpc hdc))

open Classical in
/-- For h>=1 both the Mason alternative and the constant alternative give
the expected height at most h-1. -/
theorem mason_low_degree_height_le
    (p : ℕ) [CharP E p] (a b c : E[X]) (h : ℕ) (hh : 0 < h)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (hsum : a + b + c = 0)
    (hrad : (radical (a * b * c)).natDegree ≤ h)
    (hda : a.natDegree < p) (hdb : b.natDegree < p) (hdc : c.natDegree < p) :
    max a.natDegree (max b.natDegree c.natDegree) ≤ h - 1 := by
  rcases mason_low_degree_or_constant p a b c h ha hb hc hab hsum hrad hda hdb hdc
    with hconstant | hbound
  · obtain ⟨ha0, hb0, hc0⟩ := hconstant
    simp [ha0, hb0, hc0]
  · obtain ⟨ha1, hb1, hc1⟩ := hbound
    omega

open Classical in
/-- Finite roots supported in B control the radical degree over an
algebraically closed field. No separability assumption on f is required. -/
theorem radical_natDegree_le_card_of_roots_subset [IsAlgClosed E]
    (f : E[X]) (B : Finset E)
    (hroots : ∀ x : E, f.eval x = 0 → x ∈ B) :
    (radical f).natDegree ≤ B.card := by
  have hsep : (radical f).Separable :=
    PerfectField.separable_iff_squarefree.mpr squarefree_radical
  have hsubset : (radical f).roots.toFinset ⊆ B := by
    intro x hx
    have hxroot : (radical f).eval x = 0 :=
      (mem_roots radical_ne_zero).mp (Multiset.mem_toFinset.mp hx)
    apply hroots x
    obtain ⟨q, hq⟩ := (radical_dvd_self : radical f ∣ f)
    rw [hq, eval_mul, hxroot, zero_mul]
  calc
    (radical f).natDegree = (radical f).roots.card :=
      IsAlgClosed.card_roots_eq_natDegree.symm
    _ = (radical f).roots.toFinset.card :=
      (Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep)).symm
    _ ≤ B.card := Finset.card_le_card hsubset

open Classical in
/-- Mason's explicit finite-place degree bound in arbitrary characteristic. -/
theorem mason_degree_add_one_le_of_roots_subset [IsAlgClosed E]
    (a b c : E[X]) (B : Finset E)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (hsum : a + b + c = 0)
    (hroots : ∀ x : E, (a * b * c).eval x = 0 → x ∈ B)
    (hder : a.derivative ≠ 0 ∨ b.derivative ≠ 0 ∨ c.derivative ≠ 0) :
    a.natDegree + 1 ≤ B.card ∧ b.natDegree + 1 ≤ B.card ∧ c.natDegree + 1 ≤ B.card := by
  exact mason_degree_add_one_le a b c B.card ha hb hc hab hsum
    (radical_natDegree_le_card_of_roots_subset (a * b * c) B hroots) hder

open Classical in
/-- Reduced u-v=w form of Mason, with no hidden sign convention. -/
theorem mason_difference_degree_add_one_le
    (u v w : E[X]) (h : ℕ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (huv : IsCoprime u v) (hrel : u - v = w)
    (hrad : (radical (u * v * w)).natDegree ≤ h)
    (hder : u.derivative ≠ 0 ∨ v.derivative ≠ 0 ∨ w.derivative ≠ 0) :
    u.natDegree + 1 ≤ h ∧ v.natDegree + 1 ≤ h ∧ w.natDegree + 1 ≤ h := by
  have hsum : u + (-v) + (-w) = 0 := by
    simpa only [sub_eq_add_neg] using (sub_eq_zero.mpr hrel : u - v - w = 0)
  have hder' : u.derivative ≠ 0 ∨ (-v).derivative ≠ 0 ∨ (-w).derivative ≠ 0 := by
    simpa only [derivative_neg, neg_ne_zero] using hder
  have hrad' : (radical (u * (-v) * (-w))).natDegree ≤ h := by
    simpa only [mul_neg, neg_mul, neg_neg] using hrad
  have hbound := mason_degree_add_one_le u (-v) (-w) h hu (neg_ne_zero.mpr hv)
    (neg_ne_zero.mpr hw) huv.neg_right hsum hrad' hder'
  simpa only [natDegree_neg] using hbound

open Classical in
/-- Difference-form height bound below the characteristic, including the
separate all-constant case when h>=1. -/
theorem mason_difference_low_degree_height_le
    (p : ℕ) [CharP E p] (u v w : E[X]) (h : ℕ) (hh : 0 < h)
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (huv : IsCoprime u v) (hrel : u - v = w)
    (hrad : (radical (u * v * w)).natDegree ≤ h)
    (hdu : u.natDegree < p) (hdv : v.natDegree < p) (hdw : w.natDegree < p) :
    max u.natDegree (max v.natDegree w.natDegree) ≤ h - 1 := by
  have hsum : u + (-v) + (-w) = 0 := by
    simpa only [sub_eq_add_neg] using (sub_eq_zero.mpr hrel : u - v - w = 0)
  have hrad' : (radical (u * (-v) * (-w))).natDegree ≤ h := by
    simpa only [mul_neg, neg_mul, neg_neg] using hrad
  have hbound := mason_low_degree_height_le p u (-v) (-w) h hh hu (neg_ne_zero.mpr hv)
    (neg_ne_zero.mpr hw) huv.neg_right hsum hrad' hdu
    (by simpa only [natDegree_neg] using hdv) (by simpa only [natDegree_neg] using hdw)
  simpa only [natDegree_neg] using hbound

theorem native_degree_lt_characteristic : (131071 : ℕ) < 2130706433 := by norm_num

theorem native_derivative_ne_zero [CharP E 2130706433] (f : E[X])
    (hpos : 0 < f.natDegree) (hdegree : f.natDegree ≤ 131071) : f.derivative ≠ 0 :=
  derivative_ne_zero_of_natDegree_pos_lt_char 2130706433 f hpos
    (hdegree.trans_lt native_degree_lt_characteristic)

open Classical in
/-- Conditional native five-finite-place height bound. This is a polynomial
height statement, not a count of solutions or a component-cover theorem. -/
theorem native_five_place_difference_height_le_four
    [IsAlgClosed E] [CharP E 2130706433]
    (u v w : E[X]) (B : Finset E)
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (huv : IsCoprime u v) (hrel : u - v = w)
    (hroots : ∀ x : E, (u * v * w).eval x = 0 → x ∈ B)
    (hB : B.card ≤ 5)
    (hdu : u.natDegree ≤ 131071) (hdv : v.natDegree ≤ 131071)
    (hdw : w.natDegree ≤ 131071) :
    max u.natDegree (max v.natDegree w.natDegree) ≤ 4 := by
  exact mason_difference_low_degree_height_le 2130706433 u v w 5 (by norm_num)
    hu hv hw huv hrel
    ((radical_natDegree_le_card_of_roots_subset (u * v * w) B hroots).trans hB)
    (hdu.trans_lt native_degree_lt_characteristic)
    (hdv.trans_lt native_degree_lt_characteristic)
    (hdw.trans_lt native_degree_lt_characteristic)

/-- Only the arithmetic identity, not a count of S-unit solutions. -/
theorem h5_divisor_count_identity : (6 : ℕ) * 9 ^ 6 + 6 = 3188652 := by norm_num

/-- Exact native incidence rounding, for every positive integer s. -/
theorem native_incidence_rounding (s : ℕ) (hs : 1 ≤ s) :
    (262144 - 5) * (s + 1) < (177505 - 5) * (2 * s + 1) := by omega


end Sol1.MasonSparsePlace
end PackSource_MasonSparsePlaceCore

section PackSource_K1_11ContactOrder
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K1_11
noncomputable section
open MvPolynomial
variable {F σ : Type*} [Field F]

def contactExponent (v : σ → ℕ) : (σ →₀ ℕ) →+ (Option σ →₀ ℕ) where
  toFun e := e.optionElim (e.weight v)
  map_zero' := by ext i; cases i <;> simp
  map_add' e f := by ext i; cases i <;> simp

theorem contactExponent_injective (v : σ → ℕ) : Function.Injective (contactExponent v) := by
  intro e f h
  have := congrArg Finsupp.some h
  simpa [contactExponent] using this

/-- Insert a formal contact scale and retain every original monomial.
Unlike numeric specialization, this embedding cannot cancel leading jets. -/
def contactLift (v : σ → ℕ) : MvPolynomial σ F →+* Polynomial (MvPolynomial σ F) :=
  (optionEquivLeft F σ).toRingHom.comp (AddMonoidAlgebra.mapDomainRingHom F (contactExponent v))

theorem contactLift_injective (v : σ → ℕ) : Function.Injective (contactLift (F:=F) v) :=
  (optionEquivLeft F σ).injective.comp
    (AddMonoidAlgebra.mapDomain_injective (contactExponent_injective v))

theorem contactLift_monomial (v : σ → ℕ) (e : σ →₀ ℕ) (a : F) :
    contactLift v (monomial e a)=Polynomial.monomial (e.weight v) (monomial e a) := by
  change (optionEquivLeft F σ) (AddMonoidAlgebra.mapDomain (contactExponent v) (monomial e a))=_
  change (optionEquivLeft F σ) (AddMonoidAlgebra.mapDomain (contactExponent v) (AddMonoidAlgebra.single e a))=_
  rw [AddMonoidAlgebra.mapDomain_single]
  change (optionEquivLeft F σ) (monomial ((contactExponent v) e) a)=_
  rw [optionEquivLeft_monomial]
  simp [contactExponent]

theorem contactLift_coeff (v : σ → ℕ) (P : MvPolynomial σ F) (n : ℕ) (e : σ →₀ ℕ) :
    ((contactLift v P).coeff n).coeff e=if e.weight v=n then P.coeff e else 0 := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial f a =>
    rw [contactLift_monomial]
    by_cases hfe : f=e
    · subst f
      split_ifs <;> simp_all [Polynomial.coeff_monomial]
    · by_cases hw : f.weight v=n <;> by_cases he : e.weight v=n <;> simp [Polynomial.coeff_monomial,MvPolynomial.coeff_monomial,hfe,Ne.symm hfe,hw,he]
  | add P Q hP hQ =>
    simp only [map_add,Polynomial.coeff_add,MvPolynomial.coeff_add,hP,hQ]
    split_ifs <;> simp

/-- Actual order filtration is exactly divisibility by the scale variable. -/
theorem contactLift_X_pow_dvd_iff (v : σ → ℕ) (m : ℕ) (P : MvPolynomial σ F) :
    Polynomial.X^m ∣ contactLift v P ↔ P∈restrictWeightedOrder v m := by
  rw [Polynomial.X_pow_dvd_iff,mem_restrictWeightedOrder]
  constructor
  · intro h e he
    by_contra hh
    have hc := congrArg (fun Q : MvPolynomial σ F => Q.coeff e) (h (e.weight v) (by omega))
    rw [contactLift_coeff,if_pos rfl] at hc
    exact (mem_support_iff.mp he) hc
  · intro h n hn
    ext e
    rw [contactLift_coeff]
    by_cases he : e.weight v=n
    · rw [if_pos he]
      by_contra hc
      have := h e (mem_support_iff.mpr hc)
      omega
    · simp [he]

/-- Exact first order follows from vanishing contact constant and one
nonzero linear contact coefficient; parameter coefficients remain intact. -/
theorem contact_order_one_of_coefficient (v : σ → ℕ) (L : MvPolynomial σ F)
    (horder : L∈restrictWeightedOrder v 1) (e : σ →₀ ℕ)
    (he : e.weight v=1) (hc : L.coeff e≠0) :
    (contactLift v L).natTrailingDegree=1 := by
  have hLn : L≠0 := by intro hz; exact hc (by rw [hz]; rfl)
  have hLn' : contactLift v L≠0 := fun hz => hLn (contactLift_injective v (hz.trans (map_zero _).symm))
  have hlow := Polynomial.le_natTrailingDegree hLn'
    (Polynomial.X_pow_dvd_iff.mp ((contactLift_X_pow_dvd_iff v 1 L).mpr horder))
  have hc' : (contactLift v L).coeff 1≠0 := by
    intro hz
    have hh := congrArg (fun P : MvPolynomial σ F => P.coeff e) hz
    rw [contactLift_coeff,if_pos he] at hh
    exact hc hh
  have hup := Polynomial.natTrailingDegree_le_of_ne_zero hc'
  omega

/-- If L has exact contact order one, truncated multiplication by L
injects jets of contact degree below m-1 into jets below m. This theorem
keeps the full coefficient polynomial ring, so parameter zeros are harmless. -/
theorem contact_product_not_high_order (v : σ → ℕ) (m : ℕ)
    (L H : MvPolynomial σ F)
    (hL : (contactLift v L).natTrailingDegree=1) (hLn : L≠0)
    (hH : H≠0) (hHlow : ∀ e∈H.support,e.weight v<m-1) :
    L*H ∉ restrictWeightedOrder v m := by
  intro hh
  have hLn' : contactLift v L≠0 := fun hz => hLn (contactLift_injective v (hz.trans (map_zero _).symm))
  have hHn' : contactLift v H≠0 := fun hz => hH (contactLift_injective v (hz.trans (map_zero _).symm))
  have hmul : contactLift v (L*H)≠0 := by rw [map_mul]; exact mul_ne_zero hLn' hHn'
  have hhigh := Polynomial.le_natTrailingDegree hmul
    (Polynomial.X_pow_dvd_iff.mp ((contactLift_X_pow_dvd_iff v m (L*H)).mpr hh))
  rw [map_mul,Polynomial.natTrailingDegree_mul hLn' hHn',hL] at hhigh
  obtain ⟨e,he⟩ := support_nonempty.mpr hH
  have hc : (contactLift v H).coeff (e.weight v)≠0 := by
    intro hz
    have hz' := congrArg (fun Q : MvPolynomial σ F => Q.coeff e) hz
    rw [contactLift_coeff,if_pos rfl] at hz'
    exact (mem_support_iff.mp he) hz'
  have hmin := Polynomial.natTrailingDegree_le_of_ne_zero hc
  have := hHlow e he
  omega

end
end K1_11
end PackSource_K1_11ContactOrder

section PackSource_K1_2_4Projection
set_option autoImplicit true
set_option autoImplicit false

/-! Verbatim R5Bez projection-resultant argument, repackaged with a direct
Mathlib root bound to avoid importing the unrelated old campaign tree.
Provenance: moonshots/r5/leanM/src/R5Bez.lean (existing theorem).
This counts DISTINCT first coordinates, as required by gamma -> (gamma,gamma^p). -/
namespace K1_2_4
open Polynomial Finset

variable {F : Type*} [Field F]

theorem natDegree_det_le_col {R : Type*} [CommRing R] {k : ℕ} (M : Matrix (Fin k) (Fin k) R[X]) (d : Fin k → ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ d j) : M.det.natDegree ≤ ∑ j, d j := by
  rw [Matrix.det_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  rw [Units.smul_def]
  refine (natDegree_smul_le _ _).trans ?_
  refine (natDegree_prod_le _ _).trans ?_
  exact Finset.sum_le_sum fun i _ => hM _ _

theorem resultant_natDegree_le {R : Type*} [CommRing R] (f g : Polynomial (Polynomial R)) (m n df dg : ℕ)
    (hdf : ∀ k, (f.coeff k).natDegree ≤ df) (hdg : ∀ k, (g.coeff k).natDegree ≤ dg) :
    (resultant f g m n).natDegree ≤ m * dg + n * df := by
  unfold resultant
  have h := natDegree_det_le_col (sylvester f g m n) (fun j => if (j : ℕ) < m then dg else df) ?_
  · refine h.trans (le_of_eq ?_)
    rw [Fin.sum_univ_add]
    simp [Finset.sum_const, Finset.card_univ]
  · intro i j
    induction j using Fin.addCases with
    | left j₁ =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_left, Fin.val_castAdd, j₁.isLt, ↓reduceIte]
      split_ifs
      · exact hdg _
      · simp
    | right j₁ =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_right, Fin.val_natAdd,
        show ¬ (m + (j₁ : ℕ) < m) by omega, ↓reduceIte]
      split_ifs
      · exact hdf _
      · simp

open Classical in
theorem bez_proj (f g : Polynomial (Polynomial F)) (m n df dg : ℕ) (hfm : f.natDegree ≤ m) (hgn : g.natDegree ≤ n)
    (hmn : m ≠ 0 ∨ n ≠ 0) (hdf : ∀ k, (f.coeff k).natDegree ≤ df) (hdg : ∀ k, (g.coeff k).natDegree ≤ dg)
    (hres : resultant f g m n ≠ 0) (Γ : Finset F)
    (hΓ : ∀ β ∈ Γ, ∃ ρ : F, (f.map (evalRingHom β)).eval ρ = 0 ∧ (g.map (evalRingHom β)).eval ρ = 0) :
    Γ.card ≤ m * dg + n * df := by
  obtain ⟨p, q, _, _, e⟩ := exists_mul_add_mul_eq_C_resultant f g (m := m) (n := n) hfm hgn hmn
  have hroot : ∀ β ∈ Γ, (resultant f g m n).eval β = 0 := by
    intro β hβ
    obtain ⟨ρ, hf0, hg0⟩ := hΓ β hβ
    have e2 := congrArg (fun P => (P.map (evalRingHom β)).eval ρ) e
    simp only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, hf0, hg0, zero_mul, add_zero,
      Polynomial.map_C, eval_C] at e2
    rw [coe_evalRingHom] at e2
    exact e2.symm
  calc Γ.card = (Γ.filter fun β => (resultant f g m n).eval β = 0).card := by
        rw [Finset.filter_true_of_mem hroot]
    _ ≤ (resultant f g m n).natDegree := by
      by_contra h
      apply hres
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ Γ
      · intro β hβ
        exact hroot β hβ
      · simpa only [Finset.filter_true_of_mem hroot] using (Nat.lt_of_not_ge h)
    _ ≤ m * dg + n * df := resultant_natDegree_le f g m n df dg hdf hdg

theorem resultant_ne_zero_of_coprime (f g : Polynomial (Polynomial F))
    (hcop : IsCoprime (f.map (algebraMap F[X] (FractionRing F[X]))) (g.map (algebraMap F[X] (FractionRing F[X])))) :
    resultant f g ≠ 0 := by
  have hinj : Function.Injective (algebraMap F[X] (FractionRing F[X])) := IsFractionRing.injective F[X] (FractionRing F[X])
  have h := Polynomial.resultant_ne_zero _ _ hcop
  rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj, resultant_map_map] at h
  intro h0
  apply h
  rw [h0, map_zero]

/-- bidegree Bezout on P¹ × P¹, counted over distinct β -/
theorem bez_proj_coprime (f g : Polynomial (Polynomial F)) (df dg : ℕ)
    (hdf : ∀ k, (f.coeff k).natDegree ≤ df) (hdg : ∀ k, (g.coeff k).natDegree ≤ dg)
    (hcop : IsCoprime (f.map (algebraMap F[X] (FractionRing F[X]))) (g.map (algebraMap F[X] (FractionRing F[X]))))
    (hpos : f.natDegree ≠ 0 ∨ g.natDegree ≠ 0) (Γ : Finset F)
    (hΓ : ∀ β ∈ Γ, ∃ ρ : F, (f.map (evalRingHom β)).eval ρ = 0 ∧ (g.map (evalRingHom β)).eval ρ = 0) :
    Γ.card ≤ f.natDegree * dg + g.natDegree * df :=
  bez_proj f g f.natDegree g.natDegree df dg le_rfl le_rfl hpos hdf hdg (resultant_ne_zero_of_coprime f g hcop) Γ hΓ

end K1_2_4
end PackSource_K1_2_4Projection
