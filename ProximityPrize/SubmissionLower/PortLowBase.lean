import ProximityPrize.SubmissionLower.Fast072
import ProximityPrize.SubmissionLower.PortBase
set_option Elab.async false
set_option autoImplicit true
section
namespace P0_9
noncomputable section
open Polynomial
open P0 (I K k node agreement)
open K1_13 (Geom embed extend Row Shape shape InBox Fits Contact remaining
  chart liftedChart mixed32 ceilDiv)
open scoped BigOperators
abbrev physicalDegree : ℕ := k - 1 + P0.lowCutoff.toNat
abbrev taylorLength : ℕ := physicalDegree + 1
abbrev anchorCutoff : ℕ := 90 * agreement - 1
abbrev primaryCutoff : ℕ := 3000 * agreement - 1
abbrev primaryBox : Shape := ⟨4012, 1650, 550⟩
def TrueWeightLE {n : ℕ} (P : Row n) (D : ℕ) : Prop :=
  ∀ m ∈ P.support, (P.coeff m).natDegree +
    m.sum (fun i a => (physicalDegree - i.val) * a) ≤ D
structure PoleData (Γ : Finset K) (s : K → (Polynomial K)) where
  H : (Polynomial Geom)
  monic : H.Monic
  small : 1 ≤ H.natDegree ∧ H.natDegree ≤ P0.lowCutoff.toNat
  nodes : ∀ i, H.eval (embed (node i)) ≠ 0
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ k - 1 + H.natDegree
  z : K → Geom
  injective : Function.Injective z
  c : (Polynomial Geom)
  q : (Polynomial Geom)
  a₀ : (Polynomial Geom)
  a₁ : (Polynomial Geom)
  c_unit : IsCoprime c H
  q_unit : IsCoprime q H
  a₀_unit : IsCoprime a₀ H
  regular : ∀ γ ∈ Γ, IsCoprime (a₀ + C (z γ) * a₁) H
  residue : ∀ γ ∈ Γ, H ∣ c * (a₀ + C (z γ) * a₁) * extend (s γ) + C (z γ) * q
def SmallFactor (f : Row 4) : Prop :=
  Irreducible f ∧ 0 < (shape f).t ∧ InBox (shape f) ⟨120, 48, 10⟩ ∧
    TrueWeightLE f anchorCutoff
def linearChart (p : Shape) : Shape :=
  let i := 3 + taylorLength * (p.j - 2)
  ⟨max (1 + taylorLength * (p.b - 1)) i, i, min (taylorLength + 1) (i / 3)⟩
end
end P0_9
end
section
namespace P0_9_1
noncomputable section
open K1_13 (Geom)
open P0_9 (physicalDegree anchorCutoff)
open PolynomialDifferential ReedSolomon.HiddenDerivative
def AnchorEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 120 ∧
    u.some.weight (fun i => i.val) ≤ 48 ∧
    u (some 3) ≤ 10 ∧
    u (some 1) + u (some 2) + u (some 3) ≤ 48 - (u.some.degree - 113 + 1) / 2 ∧
    u.weight (differentialWeight physicalDegree) ≤ anchorCutoff
end
end P0_9_1
end
section
namespace P0_9_1
noncomputable section
open K1_13 (Geom)
open PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial
open scoped BigOperators
open K1_13_1_1 (exponent_le_of_mem_translation_monomial)
private def truncateX : DifferentialPolynomial Geom 3 →ₗ[Geom] DifferentialPolynomial Geom 3 :=
  filterSupport (fun u => u none < 90)
private theorem origin_monomial_zero (u : JetVariable 3 →₀ ℕ) (a : Geom)
    (hu : 90 ≤ u none) :
    localConstraintAt 90 0 0 (monomial u a) = 0 := by
  have hm : (MvPolynomial.X none ^ u none * monomial (u.erase none) a :
      DifferentialPolynomial Geom 3) = monomial u a := by
    rw [MvPolynomial.X_pow_eq_monomial, monomial_mul_monomial, one_mul, Finsupp.single_add_erase]
  rw [← hm]
  apply (satisfiesLocalConstraints_iff_coeff_eq_zero 90 0 0 _).mpr
  intro e he
  rw [map_mul, map_pow, unscaledLocalSubstitution, bind₁_X_right]
  simp only [unscaledLocalImage, C_0, zero_add, MvPolynomial.X_pow_eq_monomial]
  rw [coeff_monomial_mul', ite_eq_right]
  rw [Finsupp.single_le_iff]
  rw [localContactOrder_eq] at he
  change u none ≤ e (localT 3) → False
  omega
private theorem origin_truncateX (Q : DifferentialPolynomial Geom 3) :
    localConstraintAt 90 0 0 (truncateX Q) = localConstraintAt 90 0 0 Q := by
  rw [Q.as_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro u _
  have hfilter : truncateX (monomial u (Q.coeff u)) =
      if u none < 90 then monomial u (Q.coeff u) else 0 := by
    ext v
    rw [truncateX, coeff_filterSupport]
    by_cases h : u = v
    · subst v
      by_cases hx : u none < 90 <;> simp [hx]
    · by_cases hx : u none < 90 <;> simp [hx, coeff_monomial, h]
  rw [hfilter]
  split
  · rfl
  · rw [map_zero, origin_monomial_zero _ _ (by omega)]
end
end P0_9_1
end
section
set_option autoImplicit false
set_option maxRecDepth 2000
namespace P0_9_1
open K1_13 (Geom)
open PolynomialDifferential
open scoped BigOperators
private abbrev Exponent := JetVariable 3 →₀ ℕ
private def gradeCeiling (a b c : ℕ) : ℕ :=
  min 120 (113 + 2 * (48 - (a + b + c)))
private def gradeSlots (a b c : ℕ) : ℕ :=
  gradeCeiling a b c + 1 - (a + b + c)
private noncomputable def exponent (x v a b c : ℕ) : Exponent :=
  (Finsupp.equivFunOnFinite.symm ![v, a, b, c]).optionElim x
@[simp] private theorem exponent_none (x v a b c : ℕ) : exponent x v a b c none = x := by
  simp [exponent]
@[simp] private theorem exponent_some (x v a b c : ℕ) (i : Fin 4) :
    exponent x v a b c (some i) = ![v, a, b, c] i := by
  simp [exponent]
private theorem jet_weight (m : Fin 4 →₀ ℕ) (w : Fin 4 → ℕ) :
    m.weight w = m 0 * w 0 + m 1 * w 1 + m 2 * w 2 + m 3 * w 3 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_succ, smul_eq_mul, add_assoc]
private def sumRange (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumRange f n + f n
private theorem sumRange_eq (f : ℕ → ℕ) (n : ℕ) :
    sumRange f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => rw [sumRange, Finset.sum_range_succ, ih]
end P0_9_1
end
section
namespace P0_9_2
noncomputable section
open K1_13 Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open K1_13_2 (SourcePolynomial SourceExponent Local topWeight toRow)
open P0 (I K node)
open MvPolynomial (mem_support_iff)
def SourceEligible (e : SourceExponent) : Prop :=
  e.weight jetDegreeWeight ≤ 4012 ∧
  e.weight jetDerivativeWeight ≤ 1650 ∧
  e.weight topWeight ≤ 550 ∧
  e.weight (differentialWeight 133551) ≤ 3000 * 180217 - 1
def sourceExponents : Set SourceExponent := { e | SourceEligible e }
theorem sourceExponents_finite : sourceExponents.Finite := by
  refine (Finsupp.finite_of_nat_weight_le (differentialWeight (d := 3) 133551)
    ?_ (3000 * 180217 - 1)).subset (fun e he => he.2.2.2)
  intro v
  cases v with
  | none => decide
  | some j =>
    exact (differentialWeight_some_pos_of_order_lt_degree (by decide : 3 < 133551) j).ne'
def SourceSpace : Submodule Geom SourcePolynomial :=
  MvPolynomial.restrictSupport Geom sourceExponents
instance : Module.Finite Geom SourceSpace :=
  MvPolynomial.restrictSupport_finite sourceExponents_finite
theorem weight_eq_sum (m : Fin 4 →₀ ℕ) (weight : Fin 4 → ℕ) :
    m.weight weight = m.sum (fun i a => weight i * a) := by
  simp only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm]
theorem pointContact {m : ℕ} (x y : Geom) (Q : SourcePolynomial) (S : (Polynomial Geom))
    (hS : S.eval x = y) (hQ : SatisfiesLocalConstraints m x y Q) :
    (Polynomial.X - Polynomial.C x) ^ m ∣ differentialSpecialization Q S := by
  exact X_sub_C_pow_dvd_differentialSpecialization_of_contact Q S x y hS hQ
end
end P0_9_2
end
section
namespace P0_9_2
noncomputable section
open K1_13_2 (SourceExponent topWeight)
open PolynomialDifferential ReedSolomon.HiddenDerivative Finset
open scoped BigOperators
end
end P0_9_2
end
section
namespace P0_9_2
noncomputable section
open K1_13 PolynomialDifferential ReedSolomon.HiddenDerivative
open K1_13_2 (SourceExponent Local toRow)
open P0 (I K node)
open scoped BigOperators
theorem high_monomial_vanishes (e : SourceExponent) (c : Geom) (he : 3000 ≤ e none) :
    localConstraintAt 3000 0 0 (MvPolynomial.monomial e c) = 0 := by
  change MvPolynomial.weightedTruncation (localContactWeight 3) 3000
    (MvPolynomial.bind₁ (unscaledLocalImage 3 0 0) (MvPolynomial.monomial e c)) = 0
  apply (MvPolynomial.weightedTruncation_eq_zero_iff _ _ _).mpr
  refine MvPolynomial.bind₁_mem_restrictWeightedOrder
    (w := fun v : JetVariable 3 => v.elim 1 (fun _ => 0)) ?_ ?_
  · intro v
    cases v with
    | none =>
      simpa only [unscaledLocalImage, map_zero, zero_add, Option.elim_none] using
        (MvPolynomial.X_mem_restrictWeightedOrder (R := Geom)
          (localContactWeight 3) (localT 3) (m := 1) (by rfl))
    | some j => simp
  · exact (MvPolynomial.monomial_mem_restrictWeightedOrder _ _ _ _).mpr
      (Or.inl (by simpa only [Finsupp.weight_elim_one_zero] using he))
theorem map_independent_family {V W : Type*} [AddCommGroup V] [Module Geom V]
    [AddCommGroup W] [Module Geom W] {n : ℕ} (f : V →ₗ[Geom] W)
    (hf : Function.Injective f) (P : W → Prop) (hP : ∀ x, P (f x))
    (hn : n ≤ Module.finrank Geom V) :
    ∃ e : Fin n → W, LinearIndependent Geom e ∧ ∀ i, P (e i) := by
  obtain ⟨e, he⟩ := exists_linearIndependent_of_le_finrank hn
  exact ⟨f ∘ e, he.map' f (LinearMap.ker_eq_bot_of_injective hf), fun i => hP (e i)⟩
end
end P0_9_2
end
section
namespace P0_9_3
noncomputable section
open P0 (I K)
open P0_9 (TrueWeightLE primaryBox primaryCutoff )
open K1_13 (Row InBox shape Contact)
def BankRow (w : I → K) (T : ℕ) (P : Row 4) : Prop :=
  InBox (shape P) primaryBox ∧ TrueWeightLE P T ∧ Contact w P
end
end P0_9_3
end
section
namespace P0_9_3
noncomputable section
open Polynomial
open P0 (I K node)
open P0_9 (TrueWeightLE physicalDegree primaryBox primaryCutoff  )
open K1_13 (Geom embed Row InBox shape indexDegree Contact jet atJet)
open K1_13_3 (Symbol symbolAt)
open scoped BigOperators
set_option maxRecDepth 1024
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
private abbrev Exponent := Fin 4 →₀ ℕ
private def jetWeight (m : Exponent) : ℕ :=
  m.sum (fun i a => (physicalDegree - i.val) * a)
private theorem bankRow_iff {w : I → K} {T : ℕ} {P : Row 4} :
    BankRow w T P ↔
      (∀ m ∈ P.support, m.sum (fun _ a => a) ≤ 4012 ∧
        m.sum (fun i a => i.val * a) ≤ 1650 ∧ m 3 ≤ 550 ∧
        (P.coeff m).natDegree + jetWeight m ≤ T) ∧ Contact w P := by
  simp only [BankRow, InBox, shape, indexDegree, MvPolynomial.totalDegree,
    MvPolynomial.degreeOf_le_iff, Finset.sup_le_iff, TrueWeightLE]
  constructor
  · rintro ⟨⟨hb, hj, ht⟩, hT, hc⟩
    exact ⟨fun m hm => ⟨hb m hm, hj m hm, ht m hm, hT m hm⟩, hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨fun m hm => (h m hm).1, fun m hm => (h m hm).2.1, fun m hm => (h m hm).2.2.1⟩,
      fun m hm => (h m hm).2.2.2, hc⟩
def jetEval (S : (Polynomial Geom)) : Row 4 →ₗ[Geom] (Polynomial Geom) :=
  (MvPolynomial.aeval (jet S)).toLinearMap.restrictScalars Geom
theorem jetEval_apply (S : (Polynomial Geom)) (P : Row 4) : jetEval S P = atJet P S := by
  rfl
theorem dvd_smul_poly (d P : (Polynomial Geom)) (c : Geom) (h : d ∣ P) :
    d ∣ c • P := by
  rw [Polynomial.smul_eq_C_mul]
  exact h.mul_left _
private def bank (w : I → K) (T : ℕ) : Submodule Geom (Row 4) where
  carrier := {P | BankRow w T P}
  zero_mem' := by
    apply bankRow_iff.mpr
    simp [Contact, atJet]
  add_mem' {P Q} hP hQ := by
    obtain ⟨hP, hp⟩ := bankRow_iff.mp hP
    obtain ⟨hQ, hq⟩ := bankRow_iff.mp hQ
    apply bankRow_iff.mpr
    constructor
    · intro m hm
      have hor := Finset.mem_union.mp (MvPolynomial.support_add hm)
      have bounds :
          m.sum (fun _ a => a) ≤ 4012 ∧ m.sum (fun i a => i.val * a) ≤ 1650 ∧
            m 3 ≤ 550 ∧ jetWeight m ≤ T := by
        rcases hor with h | h
        · obtain ⟨hb, hj, ht, hw⟩ := hP m h
          exact ⟨hb, hj, ht, by omega⟩
        · obtain ⟨hb, hj, ht, hw⟩ := hQ m h
          exact ⟨hb, hj, ht, by omega⟩
      obtain ⟨hb, hj, ht, hw⟩ := bounds
      refine ⟨hb, hj, ht, ?_⟩
      have hsum : ((P + Q).coeff m).natDegree ≤
          max (P.coeff m).natDegree (Q.coeff m).natDegree := by
        change ((P.coeff m) + (Q.coeff m)).natDegree ≤ _
        exact natDegree_add_le _ _
      have hdegree (R : Row 4) (hR : m ∈ R.support → (R.coeff m).natDegree + jetWeight m ≤ T) :
          (R.coeff m).natDegree ≤ T - jetWeight m := by
        by_cases h : m ∈ R.support
        · have := hR h
          omega
        · have hz : R.coeff m = 0 := by
            by_contra hnz
            exact h (MvPolynomial.mem_support_iff.mpr hnz)
          rw [hz, natDegree_zero]
          exact Nat.zero_le _
      have hp' := hdegree P (fun h => (hP m h).2.2.2)
      have hq' := hdegree Q (fun h => (hQ m h).2.2.2)
      have := hsum.trans (max_le hp' hq')
      omega
    · intro i S hS
      rw [← jetEval_apply, map_add, jetEval_apply, jetEval_apply]
      exact dvd_add (hp i S hS) (hq i S hS)
  smul_mem' c P hP := by
    obtain ⟨hP, hp⟩ := bankRow_iff.mp hP
    apply bankRow_iff.mpr
    constructor
    · intro m hm
      obtain ⟨hb, hj, ht, hw⟩ := hP m (MvPolynomial.support_smul hm)
      refine ⟨hb, hj, ht, ?_⟩
      rw [MvPolynomial.coeff_smul]
      exact (Nat.add_le_add_right (natDegree_smul_le c (P.coeff m)) _).trans hw
    · intro i S hS
      have h : jetEval S (c • P) = c • jetEval S P := (jetEval S).map_smul c P
      rw [jetEval_apply, jetEval_apply] at h
      rw [h]
      exact dvd_smul_poly _ _ c (hp i S hS)
def coefficientArray (T : ℕ) :
    Row 4 →ₗ[Geom] (((Fin 4 → Fin 4013) × Fin (T + 1)) → Geom) :=
  LinearMap.pi fun u =>
    (Polynomial.lcoeff Geom u.2.val).comp
      ((MvPolynomial.lcoeff (Polynomial Geom) (Finsupp.equivFunOnFinite.symm (fun i => (u.1 i).val))
        : Row 4 →ₗ[(Polynomial Geom)] (Polynomial Geom)).restrictScalars Geom)
private instance finiteBank (w : I → K) (T : ℕ) : Module.Finite Geom (bank w T) := by
  classical
  let f : bank w T →ₗ[Geom] (((Fin 4 → Fin 4013) × Fin (T + 1)) → Geom) :=
    (coefficientArray T).comp (bank w T).subtype
  have hzero (Q : bank w T) (hQ : f Q = 0) : Q = 0 := by
    obtain ⟨P, hP⟩ := Q
    change BankRow w T P at hP
    apply Subtype.ext
    change P = 0
    apply MvPolynomial.ext
    intro m
    change _ = 0
    by_contra hnz
    have hm := MvPolynomial.mem_support_iff.mpr hnz
    have hT : (P.coeff m).natDegree ≤ T := (Nat.le_add_right _ _).trans (hP.2.1 m hm)
    let u : Fin 4 → Fin 4013 := fun i => ⟨m i, Nat.lt_succ_of_le <|
      (MvPolynomial.le_degreeOf_of_mem_support i hm).trans <|
        (P.degreeOf_le_totalDegree i).trans hP.1.1⟩
    apply hnz
    ext k
    rw [Polynomial.coeff_zero]
    by_cases hk : k < T + 1
    · have hval := congrFun hQ (u, ⟨k, hk⟩)
      change (P.coeff (Finsupp.equivFunOnFinite.symm (fun i => (u i).val))).coeff k = 0 at hval
      have heq : Finsupp.equivFunOnFinite.symm (fun i => (u i).val) = m :=
        Finsupp.equivFunOnFinite.symm_apply_apply m
      rwa [heq] at hval
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  apply Module.Finite.of_injective f
  intro P Q h
  apply sub_eq_zero.mp
  have hz := f.map_sub P Q
  rw [h, sub_self] at hz
  exact hzero (P - Q) hz
def symbolLinear (x : Geom) : Row 4 →ₗ[Geom] Symbol :=
  ({ symbolAt x with
      commutes' := by
        intro a
        change MvPolynomial.map (evalRingHom x) (MvPolynomial.C (Polynomial.C a)) =
          MvPolynomial.C a
        simp } : Row 4 →ₐ[Geom] Symbol).toLinearMap
def linearFactor (x : Geom) : (Polynomial Geom) := (Polynomial.X : (Polynomial Geom)) - Polynomial.C x
theorem linearFactor_ne (x : Geom) : linearFactor x ≠ 0 := X_sub_C_ne_zero x
theorem linearFactor_degree (x : Geom) : (linearFactor x).natDegree = 1 :=
  natDegree_X_sub_C x
theorem divide_specialization (P : Row 4) (x : Geom) (hP : symbolAt x P = 0) :
    ∃ Q : Row 4, MvPolynomial.C (linearFactor x) * Q = P := by
  let Q : Row 4 := AddMonoidAlgebra.ofCoeff
    (Finsupp.mapRange.linearMap (divByMonicHom (linearFactor x)) (AddMonoidAlgebra.coeff P))
  refine ⟨Q, MvPolynomial.ext _ _ fun m => ?_⟩
  have hroot : (P.coeff m).eval x = 0 := by
    have h := congrArg (fun B : Symbol => B.coeff m) hP
    change (symbolAt x P).coeff m = (0 : Symbol).coeff m at h
    rw [symbolAt, MvPolynomial.coeff_map] at h
    exact h
  rw [MvPolynomial.coeff_C_mul]
  change (linearFactor x) * ((P.coeff m) /ₘ (linearFactor x)) = P.coeff m
  exact mul_divByMonic_eq_iff_isRoot.mpr hroot
theorem support_linear_mul (x : Geom) (P : Row 4) :
    (MvPolynomial.C (linearFactor x) * P).support = P.support := by
  ext m
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul]
  exact mul_ne_zero_iff.trans (and_iff_right (linearFactor_ne x))
end
end P0_9_3
end
section
namespace P0_9_3
noncomputable section
open Polynomial
open P0 (I K node agreement)
open P0_9 ( SmallFactor  TrueWeightLE physicalDegree primaryBox
  primaryCutoff   )
open K1_13 (Geom embed extend Row shape InBox OrderAt indexDegree remaining)
open K1_13_3 (symbolAt symbolIndex cofactor_rank)
open scoped BigOperators
theorem exists_fresh {n : ℕ} (f : Fin n → Row 4) :
    ∃ x : Geom, (∀ i : I, x ≠ embed (node i)) ∧
      ∀ i, (symbolAt x (f i)).support = (f i).support := by
  classical
  let nodes : Finset Geom := Finset.univ.image (fun i : I => embed (node i))
  let roots : Finset Geom := Finset.univ.biUnion (fun i : Fin n =>
    (f i).support.biUnion (fun m => ((f i).coeff m).roots.toFinset))
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (nodes ∪ roots)
  rw [Finset.mem_union, not_or] at hx
  refine ⟨x, ?_, fun i => Finset.Subset.antisymm (MvPolynomial.support_map_subset _ _) ?_⟩
  · intro i h
    exact hx.1 (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩)
  · intro m hm
    rw [MvPolynomial.mem_support_iff] at ⊢
    change (MvPolynomial.map (evalRingHom x) (f i)).coeff m ≠ 0
    rw [MvPolynomial.coeff_map]
    intro heval
    have hroot : x ∈ ((f i).coeff m).roots :=
      (Polynomial.mem_roots (MvPolynomial.mem_support_iff.mp hm)).mpr heval
    exact hx.2 (Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨m, hm, Multiset.mem_toFinset.mpr hroot⟩⟩)
theorem specialization_bounds (x : Geom) (P : Row 4)
    (hP : InBox (shape P) primaryBox) :
    (symbolAt x P).totalDegree ≤ 4012 ∧ symbolIndex (symbolAt x P) ≤ 1650 := by
  have h : (symbolAt x P).support ⊆ P.support := MvPolynomial.support_map_subset _ _
  exact ⟨(Finset.sup_mono h).trans hP.1, (Finset.sup_mono h).trans hP.2.1⟩
theorem sum_by_layer (W E : ℕ) (hE : 0 < E) (cost : ℕ → ℕ) :
    (∑ T ∈ Finset.range (W + 1), cost ((W - T) / E)) ≤
      E * ∑ k ∈ Finset.range (1 + W / E), cost k := by
  let S := Finset.range (W + 1)
  let R := Finset.range (1 + W / E)
  let U := Finset.range E
  let pair (T : ℕ) : ℕ × ℕ := ((W - T) / E, (W - T) % E)
  have hmem : ∀ T ∈ S, pair T ∈ R ×ˢ U := by
    intro T _
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_range.mpr (by
        change (W - T) / E < 1 + W / E
        have h : (W - T) / E ≤ W / E := Nat.div_le_div_right (Nat.sub_le W T)
        omega),
      Finset.mem_range.mpr (Nat.mod_lt _ hE)⟩
  have hinj : Set.InjOn pair (↑S : Set ℕ) := by
    intro T hT V hV h
    have hT' : T < W + 1 := Finset.mem_range.mp hT
    have hV' : V < W + 1 := Finset.mem_range.mp hV
    have he : W - T = W - V := by
      have ht := Nat.mod_add_div (W - T) E
      have hv := Nat.mod_add_div (W - V) E
      have hfst := congrArg Prod.fst h
      have hsnd := congrArg Prod.snd h
      change (W - T) / E = (W - V) / E at hfst
      change (W - T) % E = (W - V) % E at hsnd
      rw [hsnd, hfst, hv] at ht
      exact ht.symm
    omega
  calc
    _ ≤ ∑ p ∈ R ×ˢ U, cost p.1 := by
      refine Finset.sum_le_sum_of_injOn pair hinj ?_ (fun _ _ => le_rfl) (fun _ _ _ => Nat.zero_le _)
      intro p hp
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hp
      exact hmem T hT
    _ = _ := by rw [Finset.sum_product, Finset.mul_sum]; simp [U, R]
end
end P0_9_3
end
section
namespace P0_9_3_2
noncomputable section
open Polynomial
open P0_9 (SmallFactor  TrueWeightLE physicalDegree primaryBox primaryCutoff)
open K1_13 (Geom embed extend Row shape InBox OrderAt indexDegree shiftJet jet)
private abbrev Exponent := Fin 4 →₀ ℕ
def translateTop : Row 4 →+* Polynomial (Row 4) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C) fun i =>
    Polynomial.C (MvPolynomial.X i) + if i = 3 then Polynomial.X else 0
def topHasse (a : ℕ) (P : Row 4) : Row 4 :=
  (translateTop P).coeff a
private theorem translate_independent (m : Exponent) (c : (Polynomial Geom)) (hm : m 3 = 0) :
    translateTop (MvPolynomial.monomial m c) = Polynomial.C (MvPolynomial.monomial m c) := by
  rw [translateTop, MvPolynomial.eval₂Hom_monomial, MvPolynomial.monomial_eq, map_mul]
  simp only [RingHom.comp_apply]
  congr 1
  unfold Finsupp.prod
  rw [map_prod]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hne : i ≠ 3 := by
    intro he
    subst i
    exact (Finsupp.mem_support_iff.mp hi) hm
  simp [hne]
private theorem translate_top_pow_coeff (n a : ℕ) :
    ((Polynomial.C (MvPolynomial.X (3 : Fin 4) : Row 4) + Polynomial.X) ^ n).coeff a =
      MvPolynomial.C (↑(n.choose a) : (Polynomial Geom)) * MvPolynomial.X 3 ^ (n - a) := by
  rw [add_comm, ← Polynomial.taylor_X_pow, Polynomial.taylor_coeff,
    Polynomial.X_pow_eq_monomial, Polynomial.hasseDeriv_monomial]
  simp [Polynomial.eval_monomial]
theorem erase_top_add (u : Exponent) :
    u.erase 3 + Finsupp.single 3 (u 3) = u := by
  ext i
  by_cases hi : i = 3
  · subst i
    simp
  · simp [Finsupp.erase_ne hi, Finsupp.single_eq_of_ne hi]
private theorem topHasse_monomial (a : ℕ) (u : Exponent) (c : (Polynomial Geom)) :
    topHasse a (MvPolynomial.monomial u c) =
      MvPolynomial.monomial (u.erase 3 + Finsupp.single 3 (u 3 - a)) (↑((u 3).choose a) * c) := by
  have hu : MvPolynomial.monomial u c =
      MvPolynomial.monomial (u.erase 3) c * MvPolynomial.X 3 ^ (u 3) := by
    rw [← MvPolynomial.monomial_add_single, erase_top_add]
  have hx : translateTop (MvPolynomial.X 3) =
      Polynomial.C (MvPolynomial.X 3) + Polynomial.X := by simp [translateTop]
  unfold topHasse
  rw [hu, map_mul, map_pow, translate_independent _ _ Finsupp.erase_same, hx,
    Polynomial.coeff_C_mul, translate_top_pow_coeff, ← mul_assoc]
  rw [mul_comm (MvPolynomial.monomial (u.erase 3) c), MvPolynomial.C_mul_monomial,
    ← MvPolynomial.monomial_add_single]
theorem apply_add_top (m : Exponent) (a : ℕ) :
    (m + Finsupp.single 3 a : Exponent) 3 = m 3 + a := by simp
theorem topHasse_coeff (a : ℕ) (P : Row 4) (m : Exponent) :
    (topHasse a P).coeff m =
      ↑((m 3 + a).choose a) * P.coeff (m + Finsupp.single 3 a) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [topHasse_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases ha : a ≤ u 3
    · have hcancel : (u.erase 3 + Finsupp.single 3 (u 3 - a)) + Finsupp.single 3 a = u := by
        rw [add_assoc, ← Finsupp.single_add, Nat.sub_add_cancel ha, erase_top_add]
      have heq : u.erase 3 + Finsupp.single 3 (u 3 - a) = m ↔
          u = m + Finsupp.single 3 a := by
        constructor
        · intro h
          rw [← h, hcancel]
        · intro h
          exact add_right_cancel (hcancel.trans h)
      simp only [heq]
      by_cases h : u = m + Finsupp.single 3 a
      · have h3 : u 3 = m 3 + a := by rw [h, apply_add_top]
        simp only [h3, ite_eq_left h]
      · simp [h]
    · have hne : u ≠ m + Finsupp.single 3 a := by
        intro h
        have h3 : u 3 = m 3 + a := by rw [h, apply_add_top]
        omega
      rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge ha)]
      simp [hne]
  | add P Q hP hQ =>
    simp only [topHasse, map_add, Polynomial.coeff_add, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply] at hP hQ ⊢
    rw [hP, hQ, mul_add]
theorem source_support {a : ℕ} {P : Row 4} {m : Exponent}
    (hm : m ∈ (topHasse a P).support) : m + Finsupp.single 3 a ∈ P.support := by
  rw [MvPolynomial.mem_support_iff, topHasse_coeff] at hm
  exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hm)
theorem sum_add_top (w : Fin 4 → ℕ) (m : Exponent) (a : ℕ) :
    (m + Finsupp.single 3 a).sum (fun i k => w i * k) =
      m.sum (fun i k => w i * k) + w 3 * a := by
  rw [Finsupp.sum_add_index' (fun i => Nat.mul_zero (w i)) (fun i b c => Nat.mul_add (w i) b c),
    Finsupp.sum_single_index (h := fun i k => w i * k) (Nat.mul_zero _)]
theorem total_add_top (m : Exponent) (a : ℕ) :
    (m + Finsupp.single 3 a).sum (fun _ k => k) = m.sum (fun _ k => k) + a := by
  simpa only [one_mul] using sum_add_top (fun _ => 1) m a
private def shiftHom (S : (Polynomial Geom)) : Row 4 →+* Row 4 :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X i + MvPolynomial.C (jet S i))
private theorem translate_shift (S : (Polynomial Geom)) :
    translateTop.comp (shiftHom S) = (Polynomial.mapRingHom (shiftHom S)).comp translateTop := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [translateTop, shiftHom]
  · intro i
    simp only [RingHom.comp_apply, shiftHom, translateTop, MvPolynomial.eval₂Hom_X',
      MvPolynomial.eval₂Hom_C, map_add, Polynomial.coe_mapRingHom, Polynomial.map_C]
    by_cases hi : i = 3
    · simp only [hi, ite_true, Polynomial.map_X]
      exact add_right_comm _ _ _
    · simp only [hi, ite_false, Polynomial.map_zero, add_zero]
theorem topHasse_order (a d : ℕ) (P : Row 4) (S : (Polynomial Geom))
    (h : OrderAt P S d) : OrderAt (topHasse a P) S (d - a) := by
  have he := RingHom.congr_fun (translate_shift S) P
  change translateTop (shiftJet P S) = (translateTop P).map (shiftHom S) at he
  have hs : topHasse a (shiftJet P S) = shiftJet (topHasse a P) S := by
    change (translateTop (shiftJet P S)).coeff a =
      shiftHom S ((translateTop P).coeff a)
    rw [he, Polynomial.coeff_map]
  intro m hm
  rw [← hs] at hm
  have hd := h _ (source_support hm)
  rw [total_add_top] at hd
  omega
theorem topHasse_zero (P : Row 4) : topHasse 0 P = P := by
  ext m
  simp [topHasse_coeff]
private theorem coeff_X_mul_pow {R : Type*} [CommSemiring R]
    (V W : Polynomial R) (a : ℕ) :
    ((Polynomial.X * V) ^ a * W).coeff a = (V.coeff 0) ^ a * W.coeff 0 := by
  rw [mul_pow, mul_assoc]
  calc
    _ = (V ^ a * W).coeff 0 := by
      simpa only [zero_add] using Polynomial.coeff_X_pow_mul (V ^ a * W) a 0
    _ = _ := by
      change Polynomial.constantCoeff (V ^ a * W) =
        Polynomial.constantCoeff V ^ a * Polynomial.constantCoeff W
      rw [map_mul, map_pow]
theorem exact_hasse_not_dvd {R : Type*} [CommRing R]
    (T : R →+* Polynomial R) (T0 : ∀ G, (T G).coeff 0 = G)
    (f P : R) (a : ℕ) (hf : Prime f) (hsep : ¬ f ∣ (T f).coeff 1)
    (hdiv : f ^ a ∣ P) (hexact : ¬ f ^ (a + 1) ∣ P) : ¬ f ∣ (T P).coeff a := by
  obtain ⟨U, rfl⟩ := hdiv
  have hu : ¬ f ∣ U := by
    rintro ⟨V, rfl⟩
    exact hexact ⟨V, by rw [pow_succ, mul_assoc]⟩
  let J := Ideal.span ({f} : Set R)
  have : J.IsPrime := Ideal.isPrime_span_singleton_of_prime hf
  let reduce := Ideal.Quotient.mk J
  let tr := (Polynomial.mapRingHom reduce).comp T
  have hzero (G : R) : reduce G = 0 ↔ f ∣ G :=
    Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton
  have hcoeff (G : R) (n : ℕ) : (tr G).coeff n = reduce ((T G).coeff n) :=
    Polynomial.coeff_map _ _
  have hconstant (G : R) : (tr G).coeff 0 = reduce G := by rw [hcoeff, T0]
  obtain ⟨V, hV⟩ := Polynomial.X_dvd_iff.mpr
    (show (tr f).coeff 0 = 0 by rw [hconstant]; exact (hzero _).mpr dvd_rfl)
  have hfirst : V.coeff 0 = reduce ((T f).coeff 1) := by
    rw [← hcoeff, hV]
    exact (Polynomial.coeff_X_mul V 0).symm
  have hr : reduce ((T (f ^ a * U)).coeff a) = reduce ((T f).coeff 1) ^ a * reduce U := by
    calc
      _ = (tr (f ^ a * U)).coeff a := (hcoeff _ _).symm
      _ = (V.coeff 0) ^ a * (tr U).coeff 0 := by
        rw [map_mul, map_pow, hV]
        exact coeff_X_mul_pow V (tr U) a
      _ = _ := by rw [hfirst, hconstant]
  intro h
  exact (mul_ne_zero (pow_ne_zero _ ((hzero _).not.mpr hsep))
    ((hzero _).not.mpr hu)) (hr.symm.trans ((hzero _).mpr h))
end
end P0_9_3_2
end
