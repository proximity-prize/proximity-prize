import ProximityPrize.SubmissionLower.GoldBranch6
import ProximityPrize.SubmissionLower.UpperBranch3
set_option Elab.async false
set_option autoImplicit true
section
namespace P3_6_2
noncomputable section
open K1_13 Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open K1_13_2 (SourcePolynomial SourceExponent Local topWeight toRow)
open P3 (I K node)
open MvPolynomial (mem_support_iff)
open private weight_eq_sum pointContact from ProximityPrize.SubmissionLower.PortLowBase
def SourceEligible (e : SourceExponent) : Prop :=
  e.weight jetDegreeWeight ≤ 4012 ∧
  e.weight jetDerivativeWeight ≤ 1650 ∧
  e.weight topWeight ≤ 550 ∧
  e.weight (differentialWeight 133344) ≤ 3000 * 179983 - 1
def sourceExponents : Set SourceExponent := { e | SourceEligible e }
theorem sourceExponents_finite : sourceExponents.Finite := by
  refine (Finsupp.finite_of_nat_weight_le (differentialWeight (d := 3) 133344)
    ?_ (3000 * 179983 - 1)).subset (fun e he => he.2.2.2)
  intro v
  cases v with
  | none => decide
  | some j =>
    exact (differentialWeight_some_pos_of_order_lt_degree (by decide : 3 < 133344) j).ne'
def SourceSpace : Submodule Geom SourcePolynomial :=
  MvPolynomial.restrictSupport Geom sourceExponents
instance : Module.Finite Geom SourceSpace :=
  MvPolynomial.restrictSupport_finite sourceExponents_finite
theorem translate_mem_source (x y : Geom) (Q : SourceSpace) :
    globalPointTranslation x y Q.1 ∈ SourceSpace := by
  have preserve (wt : JetVariable 3 → ℕ) (B : ℕ)
      (h : ∀ e ∈ Q.1.support, e.weight wt ≤ B) :
      ∀ e ∈ (globalPointTranslation x y Q.1).support, e.weight wt ≤ B :=
    MvPolynomial.mem_restrictWeightAtMost.mp
      (globalPointTranslation_mem_restrictWeightAtMost (Nat.zero_le _) (Nat.zero_le _)
        x y (MvPolynomial.mem_restrictWeightAtMost.mpr h))
  have h : ∀ e ∈ Q.1.support, SourceEligible e :=
    Q.2
  exact fun e he =>
    ⟨preserve jetDegreeWeight 4012 (fun t ht => (h t ht).1) e he,
      preserve jetDerivativeWeight 1650 (fun t ht => (h t ht).2.1) e he,
      preserve topWeight 550 (fun t ht => (h t ht).2.2.1) e he,
      preserve (differentialWeight 133344) (3000 * 179983 - 1)
        (fun t ht => (h t ht).2.2.2) e he⟩
def nodeMap (x y : Geom) : SourceSpace →ₗ[Geom] Local :=
  (localConstraintAt 3000 x y).domRestrict SourceSpace
def wordMap (w : I → K) : SourceSpace →ₗ[Geom] (I → Local) :=
  LinearMap.pi fun i => nodeMap (embed (node i)) (embed (w i))
theorem contact_of_word_kernel (w : I → K) (Q : SourceSpace) (hQ : wordMap w Q = 0) :
    Contact w (toRow Q.1) := by
  intro i S hS
  rw [K1_13_2.atJet_toRow]
  have hi : SatisfiesLocalConstraints (d := 3) 3000 (embed (node i)) (embed (w i)) Q.1 := by
    exact congrFun hQ i
  have hd := pointContact (embed (node i)) (embed (w i)) Q.1 S hS hi
  with_reducible exact hd
end
end P3_6_2
end
section
namespace P3_6_2
noncomputable section
open K1_13 PolynomialDifferential ReedSolomon.HiddenDerivative
open K1_13_2 (SourceExponent Local toRow)
open P3 (I K node)
open scoped BigOperators
open private high_monomial_vanishes origin_rank map_independent_family from ProximityPrize.SubmissionLower.PortLowBase
theorem old_eligible (e : SourceExponent) (he : SourceEligible e)
    (hx : e none < 3000) : K1_13_2.SourceEligible e := by
  have hw := weight_le_add_mul_totalJetDegree 133671 e
  change e.weight (differentialWeight 133671) ≤ e none + 133671 * e.weight jetDegreeWeight at hw
  refine ⟨he.1, he.2.1, he.2.2.1, ?_⟩
  have hb := he.1
  omega
private theorem node_range_le (x y : Geom) :
    LinearMap.range (nodeMap x y) ≤ LinearMap.range (K1_13_2.nodeMap 0 0) := by
  rintro _ ⟨Q, rfl⟩
  let R := globalPointTranslation x y Q.1
  have hR : R ∈ SourceSpace := translate_mem_source x y Q
  change localConstraintAt 3000 x y Q.1 ∈ _
  rw [localConstraintAt_eq_zero_globalPointTranslation]
  change localConstraintAt 3000 0 0 R ∈ _
  rw [congrArg (localConstraintAt 3000 0 0) R.as_sum, map_sum]
  refine Submodule.sum_mem _ fun e he => ?_
  by_cases hx : e none < 3000
  · have hOld : e ∈ K1_13_2.sourceExponents := old_eligible e (hR he) hx
    have hMono : MvPolynomial.monomial e (R.coeff e) ∈ K1_13_2.SourceSpace :=
      (MvPolynomial.monomial_mem_restrictSupport Geom).mpr (Or.inl hOld)
    exact ⟨⟨_, hMono⟩, rfl⟩
  · rw [high_monomial_vanishes _ _ (Nat.le_of_not_gt hx)]
    exact Submodule.zero_mem _
theorem word_rank_le (w : I → K) {b : ℕ}
    (h : Module.finrank Geom (LinearMap.range (K1_13_2.nodeMap 0 0)) ≤ b) :
    Module.finrank Geom (LinearMap.range (wordMap w)) ≤ 262144 * b := by
  let nmap (i : I) := nodeMap (embed (node i)) (embed (w i))
  let B (i : I) := LinearMap.range (nmap i)
  let f : SourceSpace →ₗ[Geom] (∀ i, B i) := LinearMap.pi fun i => (nmap i).rangeRestrict
  let g : (∀ i, B i) →ₗ[Geom] (I → Local) :=
    LinearMap.pi fun i => (B i).subtype.comp (LinearMap.proj i)
  have hw : wordMap w = g.comp f := rfl
  rw [hw]
  calc
    Module.finrank Geom (LinearMap.range (g.comp f)) ≤
        Module.finrank Geom (LinearMap.range g) :=
      Submodule.finrank_mono (LinearMap.range_comp_le_range f g)
    _ ≤ Module.finrank Geom (∀ i, B i) := g.finrank_range_le
    _ = ∑ i, Module.finrank Geom (B i) := Module.finrank_pi_fintype Geom
    _ ≤ ∑ _ : I, b := Finset.sum_le_sum fun i _ =>
      (Submodule.finrank_mono (node_range_le (embed (node i)) (embed (w i)))).trans h
    _ = 262144 * b := by simp [I, FrobeniusLocator.Native.I, ProximityPrize.Benchmark.IRSProfile.Index]
end
end P3_6_2
end
section
namespace P3_6_3
noncomputable section
open P3 (I K)
open P3_6 (TrueWeightLE primaryBox primaryCutoff layerWidth)
open K1_13 (Row InBox shape Contact)
def requiredOrder (T : ℕ) : ℕ :=
  (primaryCutoff - T) / layerWidth + 1
def BankRow (w : I → K) (T : ℕ) (P : Row 4) : Prop :=
  InBox (shape P) primaryBox ∧ TrueWeightLE P T ∧ Contact w P
end
end P3_6_3
end
section
namespace P3_6_3_3
noncomputable section
open Polynomial
open P3 (I K node)
open P3_6 (TrueWeightLE physicalDegree primaryCutoff)
open P3_6_3 (BankRow)
open K1_13 (Geom embed Row InBox shape indexDegree Contact atJet)
open K1_13_3 (Symbol symbolAt)
open private jetEval jetEval_apply dvd_smul_poly coefficientArray symbolLinear linearFactor
  linearFactor_ne linearFactor_degree divide_specialization support_linear_mul from ProximityPrize.SubmissionLower.PortLowBase
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
end
end P3_6_3_3
end
section
namespace P3_6_8
open K1_13 (Shape)
open K1_13_8_2 (Threshold orderFor)
abbrev oneReserve : ℕ := 0x572a200a42ce14
abbrev twoReserve : ℕ := 0xf915c8e214a19b
abbrev twoOrder : ℕ := 72
def emptyThresholds : List Threshold :=
  [⟨107, 46, 56⟩, ⟨14, 41, 53⟩, ⟨61, 31, 52⟩, ⟨8, 13, 32⟩,
    ⟨9, 7, 9⟩, ⟨22, 4, 8⟩, ⟨3, 7, 4⟩, ⟨4, 10, 22⟩,
    ⟨10, 28, 48⟩]
def emptyOrder (a : Shape) : ℕ := orderFor a.b a.j emptyThresholds
def RetainedBox (a : Shape) : Prop :=
  a.b ≤ 20 ∧ a.j ≤ 6 ∧
    (4 ≤ a.j → a.b ≤ 17) ∧ (5 ≤ a.j → a.b ≤ 14) ∧ (6 ≤ a.j → a.b ≤ 7)
end P3_6_8
end
section
namespace P3_6_8
open K1_13 (Shape Fits InBox FatEligible remaining)
open K1_13_8 (Valid zeroShape fullCap zeroMass availableMass layerTerm layerCount)
open K1_13_8_2 (orderFor)
open P0_9_8 (oneStart twoStart oneOrder indexBudget symbol_count availableMass_anti_prefix
  orderFor_select orderFor_mono oneOrder_pos oneOrder_mono)
open P3_6 (factorCap)
open scoped BigOperators
private def shapeSum {ι : Type*} (a : ι → Shape) (s : Finset ι) : Shape :=
  ⟨∑ i ∈ s, (a i).b, ∑ i ∈ s, (a i).j, ∑ i ∈ s, (a i).t⟩
private theorem shapeSum_empty {ι : Type*} (a : ι → Shape) :
    shapeSum a ∅ = zeroShape := by simp [shapeSum, zeroShape]
private theorem shapeSum_insert {ι : Type*} [DecidableEq ι] (a : ι → Shape)
    {i : ι} {s : Finset ι} (hi : i ∉ s) :
    shapeSum a (insert i s) = (shapeSum a s).plus (a i) := by
  simp [shapeSum, Shape.plus, Finset.sum_insert hi, Nat.add_comm]
private theorem shapeSum_union {ι : Type*} [DecidableEq ι] (a : ι → Shape)
    {s t : Finset ι} (h : Disjoint s t) :
    shapeSum a (s ∪ t) = (shapeSum a s).plus (shapeSum a t) := by
  simp [shapeSum, Shape.plus, Finset.sum_union h]
private theorem shapeSum_mono {ι : Type*} (a : ι → Shape) {s t : Finset ι}
    (h : s ⊆ t) : InBox (shapeSum a s) (shapeSum a t) :=
  ⟨Finset.sum_le_sum_of_subset h, Finset.sum_le_sum_of_subset h, Finset.sum_le_sum_of_subset h⟩
private theorem inBox_trans {a b c : Shape} (hab : InBox a b) (hbc : InBox b c) :
    InBox a c :=
  ⟨hab.1.trans hbc.1, hab.2.1.trans hbc.2.1, hab.2.2.trans hbc.2.2⟩
private theorem inBox_shapeSum {ι : Type*} (a : ι → Shape) {i : ι} {s : Finset ι}
    (hi : i ∈ s) : InBox (a i) (shapeSum a s) :=
  ⟨Finset.single_le_sum (f := fun i => (a i).b) (fun _ _ => Nat.zero_le _) hi,
    Finset.single_le_sum (f := fun i => (a i).j) (fun _ _ => Nat.zero_le _) hi,
    Finset.single_le_sum (f := fun i => (a i).t) (fun _ _ => Nat.zero_le _) hi⟩
private theorem shapeSum_valid_or_empty {ι : Type*} {a : ι → Shape}
    (ha : ∀ i, Valid (a i)) (s : Finset ι) :
    s = ∅ ∨ Valid (shapeSum a s) := by
  by_cases he : s.Nonempty
  · obtain ⟨i, hi⟩ := he
    refine Or.inr ⟨(ha i).1.trans (inBox_shapeSum a hi).2.2, ?_, ?_⟩
    · change 3 * (∑ i ∈ s, (a i).t) ≤ ∑ i ∈ s, (a i).j
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => (ha i).2.1
    · change (∑ i ∈ s, (a i).j) ≤ 3 * ∑ i ∈ s, (a i).b
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => (ha i).2.2
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp he)
private theorem spend_le {ι : Type*} [DecidableEq ι] [Fintype ι] {l : ι → ℕ}
    (f : ι → ℕ) {z s : Finset ι} {q d L : ℕ}
    (hz : ∀ i ∈ z, l i = 0) (hs : ∀ i ∈ s, l i ≤ L) (hdisj : Disjoint z s)
    (hq : q ≤ ∑ i ∈ z, f i) :
    d * q + (d - L) * (∑ i ∈ s, f i) ≤ ∑ i, (d - l i) * f i := by
  calc
    _ ≤ d * (∑ i ∈ z, f i) + (d - L) * (∑ i ∈ s, f i) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ hq) _
    _ = (∑ i ∈ z, d * f i) + ∑ i ∈ s, (d - L) * f i := by
      rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ (∑ i ∈ z, (d - l i) * f i) + ∑ i ∈ s, (d - l i) * f i := by
      apply Nat.add_le_add
      · exact Finset.sum_le_sum fun i hi => by rw [hz i hi, Nat.sub_zero]
      · exact Finset.sum_le_sum fun i hi =>
          Nat.mul_le_mul_right _ (Nat.sub_le_sub_left (hs i hi) _)
    _ = ∑ i ∈ z ∪ s, (d - l i) * f i := (Finset.sum_union hdisj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
end P3_6_8
end
section
namespace P3_6_8_1
open K1_13_8 (fastRemaining zeroMass)
open scoped BigOperators
private def sumBelow (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumBelow f n + f n
private theorem sumBelow_eq (f : ℕ → ℕ) (n : ℕ) :
    sumBelow f n = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih => rw [sumBelow, Finset.sum_range_succ, ih]
private theorem sumBelow_add (f : ℕ → ℕ) (m n : ℕ) :
    sumBelow f (m + n) = sumBelow f m + sumBelow (fun k => f (m + k)) n := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih =>
    change sumBelow f (m + n) + f (m + n) =
      sumBelow f m + (sumBelow (fun k => f (m + k)) n + f (m + n))
    rw [ih, Nat.add_assoc]
private def term (b j k : ℕ) : ℕ :=
  fastRemaining ((k + 1) * b) ((k + 1) * j)
private theorem mass_eq {b j m : ℕ} (hm : m ≤ 1650 / j)
    (hb : 4012 < (m + 1) * b ∨ m = 1650 / j) :
    zeroMass b j = sumBelow (term b j) m := by
  unfold zeroMass
  rw [sumBelow_eq]
  rcases hb with hb | h
  · apply K1_13_8.sum_range_truncate _ hm
    intro k hk
    have h := hb.trans_le (Nat.mul_le_mul_right b (Nat.succ_le_succ hk))
    simp [term, fastRemaining, Nat.not_le_of_gt h]
  · rw [h] <;> rfl
private theorem extend {f : ℕ → ℕ} {m n N x y total : ℕ}
    (hleft : sumBelow f m = x)
    (hright : sumBelow (fun k => f (m + k)) n = y)
    (hlen : m + n = N) (hvalue : x + y = total) :
    sumBelow f N = total := by
  rw [← hlen, sumBelow_add, hleft, hright, hvalue]
local notation "row!" h "," len "," nxt "," v "," z =>
  extend (n := len) (N := nxt) (y := v) (total := z) h rfl rfl rfl
end P3_6_8_1
end
section
namespace P3_6_8_2
open K1_13 (Shape chart ceilDiv mixed32)
open K1_13_8 (Valid)
open K1_13_8_4 (TotalLE IndexFits mixed_mono_total)
open P3_6 (fatPrice linearChart taylorLength physicalDegree incidenceGap
  resultantBox commonBox fatOrder divisorOrder isolatedOrder)
open P3_6_8 (RetainedBox oneReserve twoReserve)
private def fatChart (x : Shape) : Shape :=
  if x.t = 1 then linearChart x.chamber else chart (taylorLength + 4) x.chamber
private abbrev divisorBox : Shape :=
  ⟨commonBox.b + resultantBox.b / divisorOrder, commonBox.j + resultantBox.j / divisorOrder, 0⟩
private theorem shape_eq {x y : Shape}
    (hb : x.b = y.b) (hj : x.j = y.j) (ht : x.t = y.t) : x = y := by
  cases x
  cases y
  simp_all
local notation "shape!" => shape_eq (by decide) (by decide) (by decide)
private theorem divisorBox_eq : divisorBox = ⟨22994,7683,0⟩ := shape!
private def divisorCut (h : Shape) : Shape :=
  ⟨max (max h.b divisorBox.b) (max h.j (divisorBox.j + 1)),
    max h.j (divisorBox.j + 1), max 1 h.t⟩
private def divisorFee (p h : Shape) (md mp : ℕ) : ℕ :=
  ceilDiv (P3.t * md) (32 * incidenceGap) + ceilDiv mp 32 +
    20 * p.b * h.b ^ 2 + 5 * physicalDegree * p.b * h.b + 1
private def singularFee (x : Shape) (ms : ℕ) : ℕ :=
  if 1 < x.t then ceilDiv (4 * x.t * ms) 32 + x.t * x.b ^ 2 + 1 else 0
private def curveFee (mc mq : ℕ) : ℕ :=
  let length := (fatOrder - isolatedOrder + 1) * (fatOrder - divisorOrder + 2 - isolatedOrder)
  ceilDiv (P3.t * mc + incidenceGap * mq) (32 * incidenceGap * length)
private def isolatedFee : ℕ :=
  ceilDiv (3 * resultantBox.j ^ 2 * (2 * resultantBox.b - resultantBox.j))
    (4 * fatOrder * (fatOrder - divisorOrder + 1) * isolatedOrder)
private theorem fatPrice_expand (x : Shape) :
    fatPrice x =
      divisorFee x.chamber (fatChart x)
        (mixed32 x.chamber divisorBox (divisorCut (fatChart x)) (fatChart x))
        (mixed32 x.chamber divisorBox (divisorCut (fatChart x)) x.chamber) +
      singularFee x (mixed32 x.chamber x.chamber (fatChart x) (fatChart x)) +
      curveFee (mixed32 x.chamber resultantBox resultantBox (fatChart x))
        (mixed32 x.chamber resultantBox resultantBox x.chamber) + isolatedFee := rfl
def fromSlack (p : Shape) : Shape :=
  ⟨p.b + p.j + 3 * p.t, p.j + 3 * p.t, p.t⟩
def degreeCoeff (p q r : Shape) : ℕ :=
  16 * (p.j * q.j * r.t + p.j * q.t * r.j + p.t * q.j * r.j) +
  48 * (p.j * q.t * r.t + p.t * q.j * r.t + p.t * q.t * r.j) + 144 * p.t * q.t * r.t
def degreePart (p q r s : Shape) : ℕ :=
  p.b * degreeCoeff q r s + q.b * degreeCoeff p r s +
  r.b * degreeCoeff p q s + s.b * degreeCoeff p q r
def indexPart (p q r s : Shape) : ℕ :=
  24 * (p.j * q.j * r.j * s.t + p.j * q.j * r.t * s.j +
    p.j * q.t * r.j * s.j + p.t * q.j * r.j * s.j) +
  104 * (p.j * q.j * r.t * s.t + (p.j * q.t + p.t * q.j) * (r.j * s.t + r.t * s.j) +
    p.t * q.t * r.j * s.j) +
  312 * ((p.j * q.t + p.t * q.j) * r.t * s.t + p.t * q.t * (r.j * s.t + r.t * s.j)) +
  936 * p.t * q.t * r.t * s.t
set_option maxHeartbeats 2000000 in
theorem mixed_from_parts (p q r s : Shape) (d i : ℕ)
    (hd : degreePart p q r s = d) (hi : indexPart p q r s = i) :
    mixed32 (fromSlack p) (fromSlack q) (fromSlack r) (fromSlack s) = d + i := by
  have h :
      K1_13.difference (K1_13.difference (K1_13.difference
        (K1_13.difference K1_13.volume32 (fromSlack p)) (fromSlack q)) (fromSlack r))
        (fromSlack s) ⟨0,0,0⟩ = (↑(degreePart p q r s + indexPart p q r s) : ℤ) := by
    simp only [K1_13.difference, K1_13.volume32, Shape.plus, fromSlack,
      degreePart, degreeCoeff, indexPart, Nat.cast_add, Nat.cast_mul, Nat.cast_zero, Nat.cast_ofNat]
    ring
  unfold mixed32
  rw [h, Int.toNat_natCast, hd, hi]
abbrev divisorSlack : Shape := ⟨15311,7683,0⟩
abbrev resultantSlack : Shape := ⟨0x2596a670,0x13315480,0⟩
theorem isolated_value : isolatedFee = 0x4a9107dde10a := by decide
theorem fee_of_parts {x h : Shape} {md mp mc mq divs singular curves cap : ℕ}
    (hx : x.chamber = x) (hh : fatChart x = h) (hc : divisorCut h = h)
    (hd : mixed32 x ⟨22994,7683,0⟩ h h = md)
    (hp : mixed32 x ⟨22994,7683,0⟩ h x = mp)
    (hcurve : mixed32 x resultantBox resultantBox h = mc)
    (hpoint : mixed32 x resultantBox resultantBox x = mq)
    (hdivs : divisorFee x h md mp = divs)
    (hsingular : singularFee x (mixed32 x.chamber x.chamber (fatChart x) (fatChart x)) = singular)
    (hcurves : curveFee mc mq = curves) (hcap : divs + singular + curves + 0x4a9107dde10a ≤ cap) :
    fatPrice x ≤ cap := by
  rw [fatPrice_expand, hsingular, hx, hh, hc, divisorBox_eq, hd, hp,
    hcurve, hpoint, hdivs, hcurves, isolated_value]
  exact hcap
local notation "mix!" p "," q "," r "," s "," d "," i =>
  mixed_from_parts p q r s d i (by decide) (by decide)
local notation "row!" p "," w "," limit "," sf "," sg "," dv "," cv ","
    dd "," di "," pd "," pi "," cd "," ci "," qd "," qi =>
  fee_of_parts (x := fromSlack p) (h := fromSlack w) (cap := limit)
    (divs := dv) (singular := sf) (curves := cv) rfl shape! shape!
    (mix! p, divisorSlack, w, w, dd, di) (mix! p, divisorSlack, w, p, pd, pi)
    (mix! p, resultantSlack, resultantSlack, w, cd, ci)
    (mix! p, resultantSlack, resultantSlack, p, qd, qi)
    (by decide) sg (by decide) (by decide)
end P3_6_8_2
end
section
namespace P3_6_8_3
open K1_13_8 (zeroShape availableMass zeroMass fastRemaining)
open K1_13_8_2 (Threshold)
open scoped BigOperators
private def sumBelow (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumBelow f n + f n
private theorem sumBelow_add (f : ℕ → ℕ) (m n : ℕ) :
    sumBelow f (m + n) = sumBelow f m + sumBelow (fun k => f (m + k)) n := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih =>
    change sumBelow f (m + n) + f (m + n) =
      sumBelow f m + (sumBelow (fun k => f (m + k)) n + f (m + n))
    rw [ih, Nat.add_assoc]
private theorem extend {f : ℕ → ℕ} {m n N x total : ℕ}
    (hleft : sumBelow f m = x)
    (hright : sumBelow (fun k => f (m + k)) n = total - x)
    (hlen : m + n = N) (hle : x ≤ total) :
    sumBelow f N = total := by
  rw [← hlen, sumBelow_add, hleft, hright, Nat.add_sub_of_le hle]
local notation "block!" h "," len "," k "," t =>
  extend h (n := len) (N := k) (total := t) rfl rfl (by decide)
end P3_6_8_3
end
section
namespace P3_6_8_4
open K1_13 (Shape chart mixed32 ceilDiv)
open K1_13_8 (zeroShape)
open P0_9_8 (indexBudget)
open P3_6_8 (emptyOrder)
open P3_6 (physicalPrice physicalDegree incidenceGap primaryBox surfaceNumerator32 taylorLength factorCap)
def peak (b j : ℕ) : Shape := ⟨b, j, min 10 (j / 3)⟩
def mainFee (x : Shape) : ℕ :=
  ceilDiv (surfaceNumerator32 x.chamber primaryBox) 32 +
    ceilDiv ((P3.t + 2 * incidenceGap) * x.b * primaryBox.b *
      (chart (taylorLength + 1) x.chamber).b) incidenceGap
def auxFee (x : Shape) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let z := q.plus (p.scale 4)
  let curves := mixed32 p q z h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q z p + 2 * x.t * mixed32 p p p p
  2 * physicalDegree * x.b * q.b +
    ceilDiv (P3.t * curves + 2 * incidenceGap * points) (32 * incidenceGap)
private theorem price_eq (x : Shape) (l : ℕ) :
    physicalPrice x l = ceilDiv (mainFee x) l + auxFee x := by
  simp only [physicalPrice, mainFee, auxFee, Nat.add_assoc]
abbrev RowBound (b j : ℕ) : Prop :=
  physicalPrice (peak b j) (emptyOrder (peak b j)) ≤ indexBudget zeroShape factorCap j
private theorem row (b j l main aux : ℕ)
    (horder : emptyOrder (peak b j) = l) (hmain : mainFee (peak b j) = main)
    (haux : auxFee (peak b j) = aux)
    (hle : ceilDiv main l + aux ≤ indexBudget zeroShape factorCap j) :
    RowBound b j := by
  change physicalPrice (peak b j) (emptyOrder (peak b j)) ≤ indexBudget zeroShape factorCap j
  rwa [price_eq, horder, hmain, haux]
local notation "row!" b "," j "," l "," m "," a => row b j l m a rfl rfl rfl (by decide)
end P3_6_8_4
end
section
namespace P3_6_8_5
open K1_13 (Shape)
open K1_13_8 (availableMass availableMass_eq_sum availableMass_mono fastRemaining
  remaining_anti)
open P0_9_8 (availableMass_anti_prefix oneOrder oneStart symbol_count)
open scoped BigOperators
def capacity (j L k : ℕ) : ℕ :=
  fastRemaining (k + 1) ((k + 1) * 3 + (k + 1 - L) * j)
theorem capacity_anti (j L : ℕ) : Antitone (capacity j L) := by
  intro a b hab
  simp only [capacity, ← symbol_count]
  exact remaining_anti (by omega) <|
    Nat.add_le_add (Nat.mul_le_mul_right 3 (by omega))
      (Nat.mul_le_mul_right j (by omega))
def layerMass (j L s n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, capacity j L (s + k)
theorem add_block (width count rest : ℕ) {j L s n cap : ℕ}
    (hw : width ≤ n) (hcount : capacity j L s ≤ count)
    (hrest : layerMass j L (s + width) (n - width) ≤ rest)
    (htotal : width * count + rest ≤ cap) : layerMass j L s n ≤ cap := by
  have hsplit : layerMass j L s n =
      layerMass j L s width + layerMass j L (s + width) (n - width) := by
    conv_lhs => rw [layerMass, ← Nat.add_sub_of_le hw, Finset.sum_range_add]
    simp only [layerMass, Nat.add_assoc]
  have hblock : layerMass j L s width ≤ width * count := by
    calc
      _ ≤ ∑ _k ∈ Finset.range width, count :=
        Finset.sum_le_sum fun k _ =>
          ((capacity_anti j L) (Nat.le_add_right s k)).trans hcount
      _ = _ := by simp
  rw [hsplit]
  exact (Nat.add_le_add hblock hrest).trans htotal
theorem bounded_block (width rest : ℕ) {j L s n cap : ℕ}
    (hw : width ≤ n) (hr : rest ≤ cap)
    (hcount : capacity j L s ≤ (cap - rest) / width)
    (hrest : layerMass j L (s + width) (n - width) ≤ rest) :
    layerMass j L s n ≤ cap := by
  refine add_block width _ rest hw hcount hrest ?_
  calc
    width * ((cap - rest) / width) + rest ≤ (cap - rest) + rest := by
      rw [Nat.mul_comm width]
      exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
    _ = cap := Nat.sub_add_cancel hr
local notation "row!" w "," r => bounded_block w r (by decide) (by decide) (by decide) ?_
end P3_6_8_5
end
section
namespace P3_6_8_6
open K1_13 (Shape InBox chart liftedChart mixed32 ceilDiv)
open K1_13_8_2 (Chamber mixed_mono)
open P0_9_8 (oneStart oneOrder indexBudget)
open P0_9_8_5 (ceil_mono)
open P3_6 (physicalPrice physicalDegree incidenceGap primaryBox taylorLength surfaceNumerator32)
open P3_6_8 (oneReserve)
open private P0_9_8_5.box_refl P0_9_8_5.normalize_mono P0_9_8_5.normalize_chamber P0_9_8_5.plus_mono P0_9_8_5.plus_chamber P0_9_8_5.scale_mono
  P0_9_8_5.scale_chamber P0_9_8_5.chart_chamber P0_9_8_5.lifted_chamber P0_9_8_5.chart_mono P0_9_8_5.lifted_mono P0_9_8_5.graphShape P0_9_8_5.graph_chamber
  P0_9_8_5.graph_mono from ProximityPrize.SubmissionLower.PortLow8
private def peak (j : ℕ) : Shape := ⟨119, j, min 9 (j / 3)⟩
private def budget (j : ℕ) : ℕ := indexBudget oneStart (P3_6.factorCap - oneReserve) j
abbrev PeakBound (j : ℕ) : Prop :=
  physicalPrice (peak j) (oneOrder (peak j)) ≤ budget j
def mainFee (x : Shape) : ℕ :=
  ceilDiv (surfaceNumerator32 x.chamber primaryBox) 32 +
    ceilDiv ((P3.t + 2 * incidenceGap) * x.b * primaryBox.b *
      (chart (taylorLength + 1) x.chamber).b) incidenceGap
def auxFee (x : Shape) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let z := q.plus (p.scale 4)
  let curves := mixed32 p q z h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q z p + 2 * x.t * mixed32 p p p p
  2 * physicalDegree * x.b * q.b +
    ceilDiv (P3.t * curves + 2 * incidenceGap * points) (32 * incidenceGap)
private theorem price_eq (x : Shape) (l : ℕ) :
    physicalPrice x l = ceilDiv (mainFee x) l + auxFee x := by
  simp only [physicalPrice, mainFee, auxFee, Nat.add_assoc]
private theorem row (j l main aux fee allowance : ℕ)
    (horder : oneOrder (peak j) = l) (hmain : mainFee (peak j) = main)
    (haux : auxFee (peak j) = aux) (hfee : ceilDiv main l + aux = fee)
    (hbudget : budget j = allowance) (hle : fee ≤ allowance) : PeakBound j := by
  change physicalPrice (peak j) (oneOrder (peak j)) ≤ budget j
  rw [price_eq, horder, hmain, haux, hfee, hbudget]
  exact hle
local notation "paid[" j "," l "," main "," aux "," fee "," cap "]" =>
  row j l main aux fee cap rfl rfl rfl rfl rfl (by decide)
section
set_option maxRecDepth 4096
end
end P3_6_8_6
end
section
namespace P3_6_8_8
open K1_13 (Shape InBox chart liftedChart mixed32 ceilDiv)
open K1_13_8_2 (Chamber mixed_mono)
theorem ceil_mono {a b : ℕ} (h : a ≤ b) (l : ℕ) : ceilDiv a l ≤ ceilDiv b l :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h l) 1)
end P3_6_8_8
end
section
namespace P3_6_8_8
open K1_13 (Shape InBox chart liftedChart mixed32 ceilDiv)
open K1_13_8 (Valid fullCap)
open P0_9_8 (twoStart indexBudget)
open P3_6_8 (twoOrder twoReserve)
open P3_6 (physicalPrice factorCap)
private def budget (j : ℕ) : ℕ := indexBudget twoStart (factorCap - twoReserve) j
def priceFromParts (f m₀ m₁ m₂ c₀ c₁ p₀ p₁ : ℕ) : ℕ :=
  ceilDiv (ceilDiv (m₀ + 133346 * m₁ + 133347 * m₂) 32 +
    ceilDiv ((82161 + 2 * 46639) * 118 * 4012 * 31202965) 46639) 72 +
  2 * 133344 * 118 * 4012 +
  ceilDiv (82161 * (c₀ + 2 * f * c₁) + 93278 * (p₀ + 2 * f * p₁)) 1492448
theorem row_le (lo j f m₀ m₁ m₂ c₀ c₁ p₀ p₁ price allowance : ℕ) :
    let a : Shape := ⟨118, j, f⟩
    let p := a.chamber
    let q := P3_6.primaryBox
    let L := P3_6.taylorLength
    let g : Shape := ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
    let e₁ := liftedChart (L + 1) p
    let e₂ := liftedChart (L + 2) p
    let h := chart L p
    let z := q.plus (p.scale 4)
    mixed32 p q e₁ e₂ = m₀ → mixed32 p q g e₂ = m₁ → mixed32 p q g e₁ = m₂ →
    mixed32 p q z h = c₀ → mixed32 p p p h = c₁ →
    mixed32 p q z p = p₀ → mixed32 p p p p = p₁ →
    (chart (L + 1) p).b = 31202965 →
    priceFromParts f m₀ m₁ m₂ c₀ c₁ p₀ p₁ = price → budget lo = allowance →
    price ≤ allowance → P3_6.physicalPrice a twoOrder ≤ budget lo := by
  intro a p q L g e₁ e₂ h z hm₀ hm₁ hm₂ hc₀ hc₁ hp₀ hp₁ hb hprice hbudget hle
  have hsurface : P3_6.surfaceNumerator32 p q ≤ m₀ + 133346 * m₁ + 133347 * m₂ := by
    unfold P3_6.surfaceNumerator32
    change min _ (mixed32 p q e₁ e₂ + 133346 * mixed32 p q g e₂ +
      133347 * mixed32 p q g e₁) ≤ _
    rw [hm₀, hm₁, hm₂]
    exact min_le_right _ _
  have hpaid : P3_6.physicalPrice a twoOrder ≤ priceFromParts f m₀ m₁ m₂ c₀ c₁ p₀ p₁ := by
    unfold P3_6.physicalPrice priceFromParts
    change ceilDiv (ceilDiv (P3_6.surfaceNumerator32 p q) 32 +
          ceilDiv ((82161 + 2 * 46639) * 118 * 4012 * (chart (L + 1) p).b) 46639) 72 +
        2 * 133344 * 118 * 4012 +
        ceilDiv (82161 * (mixed32 p q z h + 2 * f * mixed32 p p p h) +
          93278 * (mixed32 p q z p + 2 * f * mixed32 p p p p)) 1492448 ≤ _
    rw [hb, hc₀, hc₁, hp₀, hp₁]
    exact Nat.add_le_add_right (Nat.add_le_add_right
      (ceil_mono (Nat.add_le_add_right (ceil_mono hsurface _) _) _) _) _
  rw [← hprice] at hle
  rw [hbudget]
  exact hpaid.trans hle
section
set_option maxRecDepth 4096
local notation "row!" lo "," hi "," f "," m₀ "," m₁ "," m₂ "," c₀ "," c₁ "," p₀ "," p₁
    "," price "," allowance =>
  row_le lo hi f m₀ m₁ m₂ c₀ c₁ p₀ p₁ price allowance
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)
end
end P3_6_8_8
end
