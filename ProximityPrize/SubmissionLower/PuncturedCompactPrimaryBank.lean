import ProximityPrize.SubmissionLower.PuncturedCompactPrimaryOrder

set_option Elab.async false

namespace PuncturedCompactPrimary
noncomputable section
open Polynomial
open P3 (I K node)
open K1_13 (Geom embed Row InBox shape indexDegree atJet)
open K1_13_3 (Symbol symbolAt)

/-- Compact interpolation rows filtered by weight, with constraints on the kept nodes. -/
def BankRow (D : ℕ) (w : I → K) (deleted : Finset I) (T : ℕ) (P : Row 4) : Prop :=
  InBox (shape P) PrimaryTaper.primaryBox ∧ PrimaryTaper.TrueWeightLE D P T ∧
    PrimaryTaper.JetsBounded P ∧ Contact w deleted P

open private jetEval jetEval_apply dvd_smul_poly coefficientArray symbolLinear linearFactor
  linearFactor_ne linearFactor_degree divide_specialization support_linear_mul from ProximityPrize.SubmissionLower.PortLowBase
open scoped BigOperators
set_option maxRecDepth 1024
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
private abbrev Exponent := Fin 4 →₀ ℕ
private def jetWeight (D : ℕ) (m : Exponent) : ℕ :=
  m.sum (fun i a => (D - i.val) * a)
private theorem bankRow_iff {D : ℕ} {w : I → K} {deleted : Finset I} {T : ℕ} {P : Row 4} :
    BankRow D w deleted T P ↔
      (∀ m ∈ P.support, m.sum (fun _ a => a) ≤ 4012 ∧
        m.sum (fun i a => i.val * a) ≤ 1650 ∧ m 3 ≤ 550 ∧
        (P.coeff m).natDegree + jetWeight D m ≤ T ∧ m ∈ TaperColumns.jetExponents) ∧ Contact w deleted P := by
  simp only [BankRow, InBox, shape, indexDegree, MvPolynomial.totalDegree,
    MvPolynomial.degreeOf_le_iff, Finset.sup_le_iff, PrimaryTaper.TrueWeightLE, PrimaryTaper.JetsBounded]
  constructor
  · rintro ⟨⟨hb, hj, ht⟩, hT, hs, hc⟩
    exact ⟨fun m hm => ⟨hb m hm, hj m hm, ht m hm, hT m hm, hs m hm⟩, hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨fun m hm => (h m hm).1, fun m hm => (h m hm).2.1, fun m hm => (h m hm).2.2.1⟩,
      fun m hm => (h m hm).2.2.2.1, fun m hm => (h m hm).2.2.2.2, hc⟩
private def bank (D : ℕ) (w : I → K) (deleted : Finset I) (T : ℕ) : Submodule Geom (Row 4) where
  carrier := {P | BankRow D w deleted T P}
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
            m 3 ≤ 550 ∧ jetWeight D m ≤ T ∧ m ∈ TaperColumns.jetExponents := by
        rcases hor with h | h
        · obtain ⟨hb, hj, ht, hw, hjets⟩ := hP m h
          exact ⟨hb, hj, ht, by omega, hjets⟩
        · obtain ⟨hb, hj, ht, hw, hjets⟩ := hQ m h
          exact ⟨hb, hj, ht, by omega, hjets⟩
      obtain ⟨hb, hj, ht, hw, hjets⟩ := bounds
      refine ⟨hb, hj, ht, ?_, hjets⟩
      have hsum : ((P + Q).coeff m).natDegree ≤
          max (P.coeff m).natDegree (Q.coeff m).natDegree := by
        change ((P.coeff m) + (Q.coeff m)).natDegree ≤ _
        exact natDegree_add_le _ _
      have hdegree (R : Row 4) (hR : m ∈ R.support → (R.coeff m).natDegree + jetWeight D m ≤ T) :
          (R.coeff m).natDegree ≤ T - jetWeight D m := by
        by_cases h : m ∈ R.support
        · have := hR h
          omega
        · have hz : R.coeff m = 0 := by
            by_contra hnz
            exact h (MvPolynomial.mem_support_iff.mpr hnz)
          rw [hz, natDegree_zero]
          exact Nat.zero_le _
      have hp' := hdegree P (fun h => (hP m h).2.2.2.1)
      have hq' := hdegree Q (fun h => (hQ m h).2.2.2.1)
      have := hsum.trans (max_le hp' hq')
      omega
    · intro i hi S hS
      rw [← jetEval_apply, map_add, jetEval_apply, jetEval_apply]
      exact dvd_add (hp i hi S hS) (hq i hi S hS)
  smul_mem' c P hP := by
    obtain ⟨hP, hp⟩ := bankRow_iff.mp hP
    apply bankRow_iff.mpr
    constructor
    · intro m hm
      obtain ⟨hb, hj, ht, hw, hjets⟩ := hP m (MvPolynomial.support_smul hm)
      refine ⟨hb, hj, ht, ?_, hjets⟩
      rw [MvPolynomial.coeff_smul]
      exact (Nat.add_le_add_right (natDegree_smul_le c (P.coeff m)) _).trans hw
    · intro i hi S hS
      have h : jetEval S (c • P) = c • jetEval S P := (jetEval S).map_smul c P
      rw [jetEval_apply, jetEval_apply] at h
      rw [h]
      exact dvd_smul_poly _ _ c (hp i hi S hS)
private instance finiteBank (D : ℕ) (w : I → K) (deleted : Finset I) (T : ℕ) : Module.Finite Geom (bank D w deleted T) := by
  classical
  let f : bank D w deleted T →ₗ[Geom] (((Fin 4 → Fin 4013) × Fin (T + 1)) → Geom) :=
    (coefficientArray T).comp (bank D w deleted T).subtype
  have hzero (Q : bank D w deleted T) (hQ : f Q = 0) : Q = 0 := by
    obtain ⟨P, hP⟩ := Q
    change BankRow D w deleted T P at hP
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
private def bankEval (D : ℕ) (w : I → K) (deleted : Finset I) (x : Geom) (T : ℕ) : bank D w deleted T →ₗ[Geom] Symbol :=
  (symbolLinear x).comp (bank D w deleted T).subtype
private theorem mul_cutoff_iff (D : ℕ) (w : I → K) (deleted : Finset I) (x : Geom) (hx : ∀ i : I, x ≠ embed (node i))
    (T : ℕ) (P : Row 4) :
    BankRow D w deleted (T + 1) (MvPolynomial.C (linearFactor x) * P) ↔ BankRow D w deleted T P := by
  rw [bankRow_iff, bankRow_iff, support_linear_mul]
  apply and_congr
  · refine forall_congr' fun m => forall_congr' fun hm => ?_
    rw [MvPolynomial.coeff_C_mul, natDegree_mul (linearFactor_ne x)
      (MvPolynomial.mem_support_iff.mp hm), linearFactor_degree]
    constructor <;> rintro ⟨hb, hj, ht, hw, hJets⟩ <;>
      exact ⟨hb, hj, ht, by omega, hJets⟩
  · simp only [Contact, atJet, map_mul, MvPolynomial.eval_C]
    apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    apply forall_congr'
    intro S
    apply forall_congr'
    intro hS
    generalize (3000 : ℕ) = m
    have hc : IsCoprime (linearFactor (embed (node i))) (linearFactor x) :=
      isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (hx i).symm).isUnit
    have hd : IsCoprime (linearFactor (embed (node i)) ^ m) (linearFactor x) := hc.pow_left
    exact hd.dvd_mul_left_iff
private theorem zero_cutoff_kernel (D : ℕ) (w : I → K) (deleted : Finset I) (x : Geom) :
    LinearMap.ker (bankEval D w deleted x 0) = ⊥ := by
  apply LinearMap.ker_eq_bot'.mpr
  intro P hP
  change symbolAt x P.val = 0 at hP
  obtain ⟨Q, hQ⟩ := divide_specialization P.val x hP
  have hp : PrimaryTaper.TrueWeightLE D P.val 0 := P.property.2.1
  apply Subtype.ext
  change P.val = 0
  rw [← hQ]
  suffices Q = 0 by simp [this]
  apply MvPolynomial.ext
  intro m
  change _ = 0
  by_contra hnz
  have hm : m ∈ P.val.support := by
    rw [← hQ, support_linear_mul]
    exact MvPolynomial.mem_support_iff.mpr hnz
  have h := hp m hm
  rw [← hQ, MvPolynomial.coeff_C_mul, natDegree_mul (linearFactor_ne x) hnz,
    linearFactor_degree] at h
  omega
private theorem kernel_finrank (D : ℕ) (w : I → K) (deleted : Finset I) (x : Geom) (hx : ∀ i : I, x ≠ embed (node i))
    (T : ℕ) : Module.finrank Geom (LinearMap.ker (bankEval D w deleted x (T + 1))) =
      Module.finrank Geom (bank D w deleted T) := by
  let L : bank D w deleted T →ₗ[Geom] (LinearMap.ker (bankEval D w deleted x (T + 1))) :=
    LinearMap.codRestrict _ (LinearMap.codRestrict (bank D w deleted (T + 1))
      ((LinearMap.mulLeft Geom (MvPolynomial.C (linearFactor x))).comp (bank D w deleted T).subtype)
      (fun P => (mul_cutoff_iff D w deleted x hx T P.val).mpr P.property)) (fun P => by
        rw [LinearMap.mem_ker]
        change symbolAt x (MvPolynomial.C (linearFactor x) * P.val) = 0
        simp [symbolAt, linearFactor])
  have hL : Function.Bijective L := by
    have hnz : (MvPolynomial.C (linearFactor x) : Row 4) ≠ 0 := by
      simpa only [ne_eq, MvPolynomial.C_eq_zero] using linearFactor_ne x
    constructor
    · intro P Q h
      apply Subtype.ext
      have heq := congrArg (fun V : LinearMap.ker (bankEval D w deleted x (T + 1)) => V.val.val) h
      change MvPolynomial.C (linearFactor x) * P.val = MvPolynomial.C (linearFactor x) * Q.val at heq
      exact mul_left_cancel₀ hnz heq
    · intro P
      have h : symbolAt x P.val.val = 0 := LinearMap.mem_ker.mp P.property
      obtain ⟨Q, hQ⟩ := divide_specialization P.val.val x h
      have hmem : BankRow D w deleted (T + 1) (MvPolynomial.C (linearFactor x) * Q) := by
        rw [hQ]
        exact P.val.property
      refine ⟨⟨Q, (mul_cutoff_iff D w deleted x hx T Q).mp hmem⟩, Subtype.ext (Subtype.ext hQ)⟩
  exact (LinearEquiv.ofBijective L hL).finrank_eq.symm
/-- At a fresh abscissa, each unit increase in weight adds the rank of that layer's symbols. -/
theorem symbol_layers (D : ℕ) (w : I → K) (deleted : Finset I) (x : Geom)
    (hx : ∀ i : I, x ≠ embed (node i)) {Tmax n : ℕ}
    (hr : ∃ e : Fin n → Row 4, LinearIndependent Geom e ∧
      ∀ i, BankRow D w deleted Tmax (e i)) :
    ∃ r : ℕ → ℕ, n ≤ ∑ T ∈ Finset.range (Tmax + 1), r T ∧
      ∀ T ≤ Tmax, ∃ e : Fin (r T) → Row 4,
        (∀ i, BankRow D w deleted T (e i)) ∧
        LinearIndependent Geom (fun i => symbolAt x (e i)) := by
  classical
  let r (T : ℕ) := Module.finrank Geom (LinearMap.range (bankEval D w deleted x T))
  refine ⟨r, ?_, fun T _ => ?_⟩
  · have heq (T : ℕ) : Module.finrank Geom (bank D w deleted T) =
        ∑ V ∈ Finset.range (T + 1), r V := by
      induction T with
      | zero =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := Geom) (V := bank D w deleted 0) (V₂ := Symbol) (bankEval D w deleted x 0)
        rw [zero_cutoff_kernel, finrank_bot, Nat.add_zero] at h
        simpa only [Nat.zero_add, Finset.sum_range_one] using h.symm
      | succ T ih =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := Geom) (V := bank D w deleted (T + 1)) (V₂ := Symbol) (bankEval D w deleted x (T + 1))
        rw [kernel_finrank D w deleted x hx, ih, Nat.add_comm] at h
        rw [Finset.sum_range_succ]
        exact h.symm
    obtain ⟨e, he, hmem⟩ := hr
    have hi : LinearIndependent Geom (fun i => (⟨e i, hmem i⟩ : bank D w deleted Tmax)) :=
      LinearIndependent.of_comp (bank D w deleted Tmax).subtype he
    rw [← heq]
    simpa only [Fintype.card_fin] using hi.fintype_card_le_finrank
  · let b := Module.finBasis Geom (LinearMap.range (bankEval D w deleted x T))
    choose e he using fun i : Fin (r T) => LinearMap.mem_range.mp (b i).property
    refine ⟨fun i => (e i).val, fun i => (e i).property, ?_⟩
    have h : LinearIndependent Geom (fun i => (b i).val) :=
      b.linearIndependent.map' (LinearMap.range (bankEval D w deleted x T)).subtype
        (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have heq : (fun i => symbolAt x (e i).val) = fun i => (b i).val := funext he
    rwa [heq]

#print axioms symbol_layers
end
end PuncturedCompactPrimary
