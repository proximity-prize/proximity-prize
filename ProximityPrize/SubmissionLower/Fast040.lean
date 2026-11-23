import ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.NumberTheory.RatFunc.Ostrowski
import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Localization.NormTrace
import ProximityPrize.SubmissionLower.Fast035
set_option Elab.async false
set_option autoImplicit true
section
namespace K1_13_1
noncomputable section
open K1_13 PolynomialDifferential ReedSolomon.HiddenDerivative
def AnchorEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 120 ∧
    u.some.weight (fun i => i.val) ≤ 48 ∧
    u (some 3) ≤ 10 ∧
    u (some 1) + u (some 2) + u (some 3) ≤ 48 - (u.some.degree - 113 + 1) / 2 ∧
    u.weight (differentialWeight 133671) ≤ 90 * 180265 - 1
end
end K1_13_1
end
section
namespace K1_13_1
noncomputable section
section Evaluation
open K1 K1_13 PolynomialDifferential Polynomial ReedSolomon.HiddenDerivative
open scoped BigOperators
private theorem coeff_flatten {n : ℕ} (P : Row n) (m : Fin n →₀ ℕ) (i : ℕ) :
    ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).coeff (m.optionElim i) =
      (P.coeff m).coeff i := by
  rw [← MvPolynomial.optionEquivRight_coeff_coeff, AlgEquiv.apply_symm_apply]
private theorem atJet_unflatten (Q : DifferentialPolynomial Geom 3) (S : Geom[X]) :
    atJet (MvPolynomial.optionEquivRight Geom (Fin 4) Q) S =
      differentialSpecialization Q S := by
  let x : Option (Fin 4) → Geom[X] := fun
    | none => Polynomial.X
    | some i => jet S i
  have h := MvPolynomial.aeval_map_optionEquivRight (R := Geom) x Q
  have hx : x none = Polynomial.X := rfl
  have hj : (fun j => x (some j)) = jet S := rfl
  rw [hx, hj, Polynomial.aeval_X_left] at h
  rw [show (AlgHom.id Geom Geom[X]).toRingHom = RingHom.id (Geom[X]) from rfl,
    MvPolynomial.map_id] at h
  rw [MvPolynomial.aeval_eq_eval] at h
  unfold atJet differentialSpecialization
  refine h.trans (AlgHom.congr_fun ?_ Q)
  apply MvPolynomial.algHom_ext
  intro v
  rw [differentialSpecializationHom, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  cases v <;> rfl
end Evaluation
section LeadingCoefficient
open K1_13 MvPolynomial
open scoped Polynomial
def topView : Row 4 ≃ₐ[Geom[X]] Polynomial (Row 3) :=
  (renameEquiv Geom[X] finSuccEquivLast).trans (optionEquivLeft Geom[X] (Fin 3))
def anchorLead (P : Row 4) : Row 3 := (topView P).leadingCoeff
theorem topView_degree (P : Row 4) : (topView P).natDegree = (shape P).t := by
  change (optionEquivLeft _ _ (rename finSuccEquivLast P)).natDegree = P.degreeOf 3
  rw [natDegree_optionEquivLeft]
  exact degreeOf_rename_of_injective finSuccEquivLast.injective (Fin.last 3)
theorem anchorLead_ne {P : Row 4} (hP : P ≠ 0) : anchorLead P ≠ 0 :=
  Polynomial.leadingCoeff_ne_zero.mpr (fun h => hP (topView.injective (h.trans (map_zero _).symm)))
theorem anchorLead_mul (P Q : Row 4) : anchorLead (P * Q) = anchorLead P * anchorLead Q := by
  rw [anchorLead, map_mul, Polynomial.leadingCoeff_mul]
  rfl
private def partialEval (S : Geom[X]) : Row 4 →+* Geom[X][X] :=
  eval₂Hom Polynomial.C fun i : Fin 4 =>
    if i = 3 then Polynomial.X else Polynomial.C (jet S i)
private theorem partialEval_eq_map (P : Row 4) (S : Geom[X]) :
    partialEval S P = (topView P).map (eval (jet S)) := by
  have hlast : finSuccEquivLast (3 : Fin 4) = none := finSuccEquivLast_last
  have h : partialEval S = (Polynomial.mapRingHom (eval (jet S))).comp topView.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro p
      simp [partialEval, topView, optionEquivLeft_C]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [partialEval, topView, hlast, optionEquivLeft_X_none, show Fin.last 3 = (3 : Fin 4) by rfl]
      · have hj : j.castSucc ≠ (3 : Fin 4) := Fin.castSucc_ne_last j
        simp [partialEval, topView, optionEquivLeft_X_some, hj, jet]
  exact RingHom.congr_fun h P
theorem eval_anchorLead (P : Row 4) (S : Geom[X]) :
    atJet (anchorLead P) S = topLead P S := by
  change eval (jet S) (topView P).leadingCoeff =
    (partialEval S P).coeff (shape P).t
  rw [partialEval_eq_map, Polynomial.coeff_map, ← topView_degree, Polynomial.leadingCoeff]
theorem atJet_eq_anchorLead_of_top_zero (P : Row 4) (S : Geom[X]) (ht : (shape P).t = 0) :
    atJet P S = atJet (anchorLead P) S := by
  have he : atJet P S = (partialEval S P).eval (jet S (3 : Fin 4)) := by
    have h : eval (jet S) =
        (Polynomial.evalRingHom (jet S (3 : Fin 4))).comp (partialEval S) := by
      apply MvPolynomial.ringHom_ext
      · intro p
        simp [partialEval]
      · intro i
        by_cases hi : i = 3
        · subst i
          simp [partialEval]
        · simp [partialEval, hi]
    exact RingHom.congr_fun h P
  have hd : (partialEval S P).natDegree ≤ 0 := by
    rw [partialEval_eq_map]
    exact Polynomial.natDegree_map_le.trans (by rw [topView_degree, ht])
  rw [he, eval_anchorLead]
  change (partialEval S P).eval _ = (partialEval S P).coeff (shape P).t
  rw [ht, Polynomial.eq_C_of_natDegree_le_zero hd, Polynomial.eval_C, Polynomial.coeff_C_zero]
theorem indexDegree_eq {n : ℕ} (P : Row n) :
    indexDegree P = P.weightedTotalDegree (fun i => i.val) := by
  simp only [indexDegree, weightedTotalDegree, Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm]
private theorem anchorLead_term (P : Row 4) (m : Fin 3 →₀ ℕ) (hm : m ∈ (anchorLead P).support) :
    ∃ u ∈ P.support, P.coeff u = (anchorLead P).coeff m ∧
      ∀ w : Fin 4 → ℕ, m.weight (fun i => w i.castSucc) ≤ u.weight w := by
  classical
  let k := (topView P).natDegree
  let c := rename finSuccEquivLast P
  have hc : c.coeff (m.optionElim k) = (anchorLead P).coeff m := by
    exact (optionEquivLeft_coeff_coeff _ _ _ _).symm
  have hs : m.optionElim k ∈ c.support :=
    mem_support_iff.mpr (by rw [hc]; exact mem_support_iff.mp hm)
  rw [show c = rename finSuccEquivLast P from rfl,
    support_rename_of_injective finSuccEquivLast.injective] at hs
  obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hs
  refine ⟨u, hu, ?_, fun w => ?_⟩
  · rw [← hc, ← he, coeff_rename_mapDomain _ finSuccEquivLast.injective]
  · let w' : Option (Fin 3) → ℕ := fun v => v.elim (w 3) (fun i => w i.castSucc)
    have hlast : finSuccEquivLast (3 : Fin 4) = none := finSuccEquivLast_last
    have hw : ∀ i : Fin 4, w' (finSuccEquivLast i) = w i := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [w', hlast, show Fin.last 3 = (3 : Fin 4) by rfl]
      · simp [w']
    have hweight : (m.optionElim k).weight w' = u.weight w := by
      rw [← he]
      simp only [Finsupp.weight_apply, smul_eq_mul]
      rw [Finsupp.sum_mapDomain_index (by simp) (by intros; rw [Nat.add_mul])]
      simp only [hw]
    rw [Finsupp.weight_optionElim] at hweight
    exact hweight ▸ Nat.le_add_left _ _
end LeadingCoefficient
section FactorCover
open K1 K1_13 MvPolynomial UniqueFactorizationMonoid
open scoped BigOperators Polynomial
private theorem index_bounds (P : Row 4) :
    3 * (shape P).t ≤ (shape P).j ∧ (shape P).j ≤ 3 * (shape P).b := by
  classical
  change 3 * P.degreeOf 3 ≤ indexDegree P ∧ indexDegree P ≤ 3 * P.totalDegree
  rw [indexDegree_eq]
  constructor
  · rw [MvPolynomial.degreeOf_eq_sup]
    have h : P.support.sup (fun m => m (3 : Fin 4)) ≤
        P.weightedTotalDegree (fun i => i.val) / 3 := by
      apply Finset.sup_le
      intro m hm
      have hterm := Finsupp.apply_smul_le_weight (fun i : Fin 4 => i.val) m (3 : Fin 4)
      have hthree : (3 : Fin 4).val = 3 := rfl
      have hle := le_weightedTotalDegree (fun i : Fin 4 => i.val) hm
      have hmul : 3 * m (3 : Fin 4) ≤ P.weightedTotalDegree (fun i => i.val) :=
        (by simpa only [smul_eq_mul, Nat.mul_comm, hthree] using hterm :
          3 * m (3 : Fin 4) ≤ m.weight (fun i => i.val)).trans hle
      omega
    omega
  · rw [weightedTotalDegree, Finset.sup_le_iff]
    intro m hm
    have hle := Finsupp.weight_le_weight
      (w := fun i : Fin 4 => i.val) (w' := fun _ => 3) (fun i => Nat.le_of_lt_succ i.isLt) m
    have he : m.weight (fun _ => 3) = 3 * m.degree := by
      simp only [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum, smul_eq_mul,
        Finset.mul_sum, Nat.mul_comm]
    have hdeg : m.degree ≤ P.totalDegree := le_totalDegree hm
    exact hle.trans (he.trans_le (Nat.mul_le_mul_left 3 hdeg))
end FactorCover
section Composition
open K1_13
end Composition
end
end K1_13_1
end
section
namespace K1_13_1_1
open K1_13 K1_13_1 MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
def residualDegree (s : ℕ) : ℕ :=
  min s (48 - (s - 113 + 1) / 2)
def orderCutoff (s : ℕ) (g : ℤ) : ℤ := 90 - (s : ℤ) - g
def jetIndex : Fin 4 → ℕ := Fin.val
def targetOrder : Fin 4 → ℕ := ![3,0,1,2]
def BandExponent (d : ℕ) (lo hi : ℤ) (f : ℕ) (m : Fin 4 →₀ ℕ) : Prop :=
  m.degree = d ∧ lo ≤ (m.weight jetIndex : ℤ) ∧ (m.weight jetIndex : ℤ) ≤ hi ∧ m 3 ≤ f
def intervalSize (lo hi : ℤ) : ℕ := (hi + 1 - lo).toNat
def sumRange (n : ℕ) (f : ℕ → ℕ) : ℕ :=
  Nat.rec 0 (fun i a => a + f i) n
theorem sumRange_eq_sum (n : ℕ) (f : ℕ → ℕ) :
    sumRange n f = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    rfl
def bandCount (d : ℕ) (lo hi : ℤ) (top : ℕ) : ℕ :=
  sumRange (min d top + 1) fun f =>
    sumRange (min (d - f) ((hi - 3 * f) / 2).toNat + 1) fun c =>
      intervalSize (max 0 (lo - 2 * c - 3 * f))
        (min ((d : ℤ) - f - c) (hi - 2 * c - 3 * f))
def lineBound (d : ℕ) (lo order : ℤ) (b c : ℕ) : ℕ :=
  let fmin := max 0 ((lo - b - 2 * (min c 24 : ℕ) + 2) / 3)
  let rowMin := max fmin (3 * (d : ℤ) - 3 * b - 2 * c - order + 1)
  min (intervalSize fmin (min d 10)) (intervalSize rowMin ((d : ℤ) - b - c))
def pairBound (d : ℕ) (lo : ℤ) (b : ℕ) : ℕ :=
  sumRange (min d 10 + 1) fun f =>
    intervalSize (max 0 ((lo - b - 3 * f + 1) / 2))
      (min ((d : ℤ) - f) ((48 - 3 * f) / 2))
structure FactorPowers where
  value : ℕ
  jetTwo : ℕ
  quad : ℕ
  cubic : ℕ
noncomputable section
abbrev Form := MvPolynomial (Fin 4) Geom
def bandSpace (d : ℕ) (lo hi : ℤ) (f : ℕ) : Submodule Geom Form :=
  restrictSupport Geom {m | BandExponent d lo hi f m}
def valueForm : Form := MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.X 2 + MvPolynomial.X 3
def backShift : Form →ₐ[Geom] Form :=
  bind₁ fun j => if j = 0 then valueForm else MvPolynomial.X j
def blockMap (s : ℕ) (g : ℤ) : bandSpace (residualDegree s) (-g) 48 10 →ₗ[Geom] Form :=
  ((weightedTruncation targetOrder (orderCutoff s g).toNat).comp
    backShift.toLinearMap).domRestrict _
def projectJet (j : Fin 4) (k : ℕ) : Form →ₗ[Geom] Form :=
  filterSupport fun m => m j = k
def pascalRowScale (e : Fin 4 →₀ ℕ) : Geom :=
  (-1 : Geom) ^ (e 2) / ∏ j : Fin 4, ((e j).factorial : Geom)
def pascalColScale (m : Fin 4 →₀ ℕ) : Geom :=
  (-1 : Geom) ^ (m 2) * ∏ j : Fin 4, ((m j).factorial : Geom)
def PascalEntries : Prop :=
  ∀ (m e : Fin 4 →₀ ℕ), m.degree = e.degree → m.degree ≤ 48 →
    (backShift (monomial m 1)).coeff e =
      pascalRowScale e * pascalColScale m *
        ((e 1).choose (m 1) : Geom) * ((e 2).choose (m 2) : Geom) *
          ((e 3).choose (m 3) : Geom)
end
end K1_13_1_1
end
section
namespace K1_13_1_1
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
end K1_13_1_1
end
