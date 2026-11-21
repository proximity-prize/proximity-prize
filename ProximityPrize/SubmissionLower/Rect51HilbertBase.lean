import ProximityPrize.SubmissionLower.HighCore82706TangentDeps

set_option autoImplicit false
set_option Elab.async false

namespace Rect51Hilbert
noncomputable section
open K1_14 (FX)
open HighCore82706Tangent_3 (JetRing ordinate seedVar)
open MvPolynomial
open scoped BigOperators

abbrev Degree := ℕ × ℕ × ℕ × ℕ
def nefDegree (h t s₀ s₁ : ℕ) : Degree := (h + 2*t, t, s₀, s₁)

abbrev CoxVar := Fin 2 ⊕ (Fin 2 ⊕ (Fin 2 ⊕ Fin 2))
abbrev Cox := MvPolynomial CoxVar FX
abbrev Exponent := CoxVar →₀ ℕ
def h₀ : CoxVar := .inl 0
def h₁ : CoxVar := .inl 1
def v₀ : CoxVar := .inr (.inl 0)
def v₁ : CoxVar := .inr (.inl 1)
def seed₀ (i : Fin 2) : CoxVar := .inr (.inr (.inl i))
def seed₁ (i : Fin 2) : CoxVar := .inr (.inr (.inr i))

def coxWeight : CoxVar → Degree
  | .inl _ => (1, 0, 0, 0)
  | .inr (.inl i) => (2*i.val, 1, 0, 0)
  | .inr (.inr (.inl _)) => (0, 0, 1, 0)
  | .inr (.inr (.inr _)) => (0, 0, 0, 1)

def affineCoord : CoxVar → JetRing
  | .inl i => if i = 0 then 1 else ordinate
  | .inr (.inl i) => if i = 0 then 1 else Polynomial.X
  | .inr (.inr (.inl i)) => if i = 0 then 1 else seedVar 0
  | .inr (.inr (.inr i)) => if i = 0 then 1 else seedVar 1

def dehom : Cox →ₐ[FX] JetRing := MvPolynomial.aeval affineCoord
def qmap (Q : Ideal JetRing) : Cox →ₐ[FX] JetRing ⧸ Q :=
  (Ideal.Quotient.mkₐ FX Q).comp dehom

abbrev Layer := Degree → Submodule FX Cox
def homogeneous : Layer := weightedHomogeneousSubmodule FX coxWeight

def gradedPiece (Q : Ideal JetRing) (d : Degree) : Submodule FX (JetRing ⧸ Q) :=
  (homogeneous d).map (qmap Q).toLinearMap

def hilbert (Q : Ideal JetRing) (h t s₀ s₁ : ℕ) : ℕ :=
  Module.finrank FX (gradedPiece Q (nefDegree h t s₀ s₁))
def EventuallyInChamber (p : ℕ → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∃ N : ℕ, ∀ h t s₀ s₁, N ≤ h → N ≤ t → N ≤ s₀ → N ≤ s₁ → p h t s₀ s₁
abbrev HilbertPoly := MvPolynomial (Fin 4) ℚ
def evalHilbert (p : HilbertPoly) (h t s₀ s₁ : ℕ) : ℚ :=
  MvPolynomial.eval ![(h : ℚ), (t : ℚ), (s₀ : ℚ), (s₁ : ℚ)] p
def IsProfile (Q : Ideal JetRing) (p : HilbertPoly) : Prop :=
  EventuallyInChamber fun h t s₀ s₁ => (hilbert Q h t s₀ s₁ : ℚ) = evalHilbert p h t s₀ s₁
def NonnegativeTop (p : HilbertPoly) : Prop :=
  ∀ m : Fin 4 →₀ ℕ, m.degree = p.totalDegree → 0 ≤ p.coeff m
def difference (p : HilbertPoly) (a : Fin 4 → ℕ) : HilbertPoly :=
  p - MvPolynomial.bind₁ (fun i => MvPolynomial.X i - MvPolynomial.C (a i : ℚ)) p
def ambient : HilbertPoly :=
  let H : HilbertPoly := MvPolynomial.X 0
  let T : HilbertPoly := MvPolynomial.X 1
  let S₀ : HilbertPoly := MvPolynomial.X 2
  let S₁ : HilbertPoly := MvPolynomial.X 3
  (T+1)*(H+T+1)*(S₀+1)*(S₁+1)

theorem weight_coordinates (m : Exponent) :
    Finsupp.weight coxWeight m = (m h₀ + m h₁ + 2*m v₁, m v₀ + m v₁,
      m (seed₀ 0) + m (seed₀ 1), m (seed₁ 0) + m (seed₁ 1)) := by
  rw [Finsupp.weight_eq_sum, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type,
    Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [coxWeight, h₀, h₁, v₀, v₁, seed₀, seed₁, Prod.mk_add_mk, Prod.smul_mk,
    Nat.mul_comm, Nat.add_assoc]

theorem cox_piece_finite (d : Degree) : Module.Finite FX (homogeneous d) := by
  have hle : homogeneous d ≤
      restrictTotalDegree CoxVar FX (d.1 + d.2.1 + d.2.2.1 + d.2.2.2) := by
    intro p hp
    apply (mem_restrictTotalDegree _ _ _).mpr
    apply Finset.sup_le
    intro m hm
    have h := hp (mem_support_iff.mp hm)
    rw [weight_coordinates] at h
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sum_type, Fintype.sum_sum_type,
      Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    rw [← h]
    change _ ≤ (m h₀ + m h₁ + 2*m v₁) + (m v₀ + m v₁) +
      (m (seed₀ 0) + m (seed₀ 1)) + (m (seed₁ 0) + m (seed₁ 1))
    change m h₀ + m h₁ + (m v₀ + m v₁ +
      (m (seed₀ 0) + m (seed₀ 1) + (m (seed₁ 0) + m (seed₁ 1)))) ≤ _
    omega
  exact Submodule.finiteDimensional_of_le hle

instance gradedPiece_finite (Q : Ideal JetRing) (d : Degree) :
    Module.Finite FX (gradedPiece Q d) := by
  have := cox_piece_finite d
  unfold gradedPiece
  infer_instance

theorem finite_weight (d : Degree) : {m : Exponent | Finsupp.weight coxWeight m = d}.Finite := by
  let total := d.1 + d.2.1 + d.2.2.1 + d.2.2.2
  let bound : Exponent := Finsupp.equivFunOnFinite.symm fun _ => total
  refine (Set.finite_Iic bound).subset (fun m hm => ?_)
  have he := (weight_coordinates m).symm.trans hm
  have hh := congrArg Prod.fst he
  have ht := congrArg (fun d : Degree => d.2.1) he
  have h₀s := congrArg (fun d : Degree => d.2.2.1) he
  have h₁s := congrArg (fun d : Degree => d.2.2.2) he
  change m h₀ + m h₁ + 2 * m v₁ = d.1 at hh
  change m v₀ + m v₁ = d.2.1 at ht
  change m (seed₀ 0) + m (seed₀ 1) = d.2.2.1 at h₀s
  change m (seed₁ 0) + m (seed₁ 1) = d.2.2.2 at h₁s
  intro i
  change m i ≤ total
  rcases i with i | (i | (i | i)) <;> fin_cases i <;>
    dsimp [h₀, h₁, v₀, v₁, seed₀, seed₁, total] at * <;> omega

end
end Rect51Hilbert
