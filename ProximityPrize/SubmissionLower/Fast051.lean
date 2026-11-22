import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
import ArkLib.Data.Finset.PairwiseIntersection
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Visible
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Sym.NatCard
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.Topology.Algebra.MvPolynomial
import ProximityPrize.SubmissionLower.Fast042
import ProximityPrize.SubmissionLower.Pack_K1_14_2_1Split
import ProximityPrize.SubmissionLower.Pack_K1_14_2_2Split
import ProximityPrize.SubmissionLower.SoloK1_13_1_1ArithmeticLogic
import ProximityPrize.SubmissionLower.Fast052 -- serialize candidate build
set_option autoImplicit true
section
namespace K1_13_8
open K1_13
open scoped BigOperators
def zeroShape : Shape := ⟨0,0,0⟩
def fullCap : Shape := ⟨120,48,10⟩
def need : ℕ := 26124168665121
def layerCount : ℕ := 1 + (3000 * 180265 - 1) / 46597
def Valid (a : Shape) : Prop := 1 ≤ a.t ∧ 3 * a.t ≤ a.j ∧ a.j ≤ 3 * a.b
def RetainedBox (a : Shape) : Prop :=
  a.b ≤ 19 ∧ a.j ≤ 6 ∧
  (4 ≤ a.j → a.b ≤ 17) ∧ (5 ≤ a.j → a.b ≤ 13) ∧ (6 ≤ a.j → a.b ≤ 6)
instance (a : Shape) : Decidable (Valid a) := by unfold Valid; infer_instance
instance (a : Shape) : Decidable (RetainedBox a) := by unfold RetainedBox; infer_instance
instance (a : Shape) : Decidable (FatEligible a) := by unfold FatEligible; infer_instance
def coefficients (r s : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  match r, s with
  | 0,0 => (1,22,57,36,0)
  | 0,1 => (2,29,63,36,0)
  | 0,2 => (4,37,69,36,0)
  | 0,3 => (7,46,75,36,0)
  | 0,4 => (11,56,81,36,0)
  | 0, _ => (16,67,87,36,0)
  | 1,0 => (1,63,314,468,216)
  | 1,1 => (3,92,377,504,216)
  | 1,2 => (7,129,446,540,216)
  | 1,3 => (14,175,521,576,216)
  | 1,4 => (25,231,602,612,216)
  | 1, _ => (41,298,689,648,216)
  | 2,0 => (1,38,172,243,108)
  | 2,1 => (2,54,205,261,108)
  | 2,2 => (5,75,241,279,108)
  | 2,3 => (9,100,280,297,108)
  | 2,4 => (16,131,322,315,108)
  | 2, _ => (25,167,367,333,108)
  | _, 0 => (1,30,125,168,72)
  | _, 1 => (2,42,148,180,72)
  | _, 2 => (4,57,173,192,72)
  | _, 3 => (8,76,200,204,72)
  | _, 4 => (13,98,229,216,72)
  | _, _ => (20,124,260,228,72)
def coefficient (r j : ℕ) : ℕ :=
  let q := j / 6
  let (a, b, c, d, e) := coefficients r (j % 6)
  let p₂ := q * (q - 1)
  let p₃ := p₂ * (q - 2)
  a + b * q + c * (p₂ / 2) + d * (p₃ / 6) + e * (p₃ * (q - 3) / 24)
def shifted (r j v : ℕ) : ℕ := if v ≤ j then coefficient r (j - v) else 0
def across (b r j v : ℕ) : ℕ :=
  shifted r j v - shifted r j (v + r * (b + 1))
def fastSymbols (b j : ℕ) : ℕ :=
  (b + 1) * coefficient 0 j + across b 2 j 3 + across b 2 j 4 + across b 2 j 5 -
    (across b 1 j 1 + across b 1 j 2 + across b 1 j 3 + across b 3 j 6)
def fastRemaining (b j : ℕ) : ℕ :=
  if b ≤ 4012 ∧ j ≤ 1650 then fastSymbols (4012 - b) (1650 - j) else 0
def zeroMass (b j : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (1650 / j), fastRemaining ((k + 1) * b) ((k + 1) * j)
def availableMass (r y : Shape) (L : ℕ) : ℕ :=
  (if r.j = 0 then L * fastRemaining 0 0
    else ∑ k ∈ Finset.range (min L (1650 / r.j)),
      fastRemaining ((k + 1) * r.b) ((k + 1) * r.j)) +
  ∑ k ∈ Finset.range (1650 / (r.j + y.j)),
    fastRemaining (L * r.b + (k + 1) * (r.b + y.b))
      (L * r.j + (k + 1) * (r.j + y.j))
def edgePrice (a : Shape) (L : ℕ) : ℕ :=
  if FatEligible a then min (physicalPrice a L) (fatPrice a) else physicalPrice a L
def Bellman (r : Shape) (cap : ℕ) : Prop :=
  ∃ (B order : Shape → ℕ), B zeroShape ≤ cap ∧
    (∀ x, Valid x → InBox (r.plus x) fullCap →
      0 < order x ∧ (order x = 1 ∨ availableMass r x (order x - 1) < need)) ∧
    (∀ (y a : Shape), (y = zeroShape ∨ Valid y) → Valid a →
      InBox (r.plus (y.plus a)) fullCap →
      edgePrice a (order (y.plus a)) + B (y.plus a) ≤ B y)
end K1_13_8
end
section
namespace K1_13_8
open K1_13
open scoped BigOperators
theorem sum_range_mono {k m : ℕ} {f g : ℕ → ℕ} (hkm : k ≤ m)
    (hfg : ∀ i < k, f i ≤ g i) :
    (∑ i ∈ Finset.range k, f i) ≤ ∑ i ∈ Finset.range m, g i :=
  (Finset.sum_le_sum fun i hi => hfg i (Finset.mem_range.mp hi)).trans
    (Finset.sum_le_sum_of_subset (Finset.range_mono hkm))
theorem symbols_mono {b₁ b₂ j₁ j₂ : ℕ} (hb : b₁ ≤ b₂) (hj : j₁ ≤ j₂) :
    symbols b₁ j₁ ≤ symbols b₂ j₂ := by
  unfold symbols
  apply sum_range_mono (by omega)
  intro z _
  apply sum_range_mono (by omega)
  intro y _
  apply sum_range_mono (by omega)
  intro x _
  omega
theorem remaining_anti {b₁ b₂ j₁ j₂ : ℕ} (hb : b₁ ≤ b₂) (hj : j₁ ≤ j₂) :
    remaining b₂ j₂ ≤ remaining b₁ j₁ := by
  by_cases h : b₂ ≤ 4012 ∧ j₂ ≤ 1650
  · have h' : b₁ ≤ 4012 ∧ j₁ ≤ 1650 := ⟨hb.trans h.1, hj.trans h.2⟩
    simpa [remaining, h, h'] using
      (symbols_mono (b₁ := 4012 - b₂) (b₂ := 4012 - b₁)
        (j₁ := 1650 - j₂) (j₂ := 1650 - j₁) (by omega) (by omega))
  · simp [remaining, h]
theorem fastRemaining_zero {b j : ℕ} (h : 1650 < j) : fastRemaining b j = 0 := by
  simp [fastRemaining, show ¬ j ≤ 1650 by omega]
theorem sum_range_truncate {f : ℕ → ℕ} {k m : ℕ}
    (hz : ∀ i, m ≤ i → f i = 0) (h : m ≤ k) :
    (∑ i ∈ Finset.range k, f i) = ∑ i ∈ Finset.range m, f i := by
  symm
  apply Finset.sum_subset (Finset.range_mono h)
  intro i _ hi
  exact hz i (by simpa using hi)
theorem sum_range_min {f : ℕ → ℕ} (k m : ℕ)
    (hz : ∀ i, m ≤ i → f i = 0) :
    (∑ i ∈ Finset.range k, f i) = ∑ i ∈ Finset.range (min k m), f i := by
  by_cases h : m ≤ k
  · rw [min_eq_right h]
    exact sum_range_truncate hz h
  · rw [min_eq_left (by omega : k ≤ m)]
theorem index_over {j k : ℕ} (hj : 0 < j) (hk : 1650 / j ≤ k) :
    1650 < (k + 1) * j :=
  (Nat.div_lt_iff_lt_mul hj).mp (by omega)
theorem zeroMass_upper (hcount : ∀ b j, remaining b j = fastRemaining b j)
    {b j : ℕ} (hj : 0 < j) :
    (∑ k ∈ Finset.range layerCount, remaining ((k + 1) * b) ((k + 1) * j)) ≤
      zeroMass b j := by
  unfold zeroMass
  simp only [hcount]
  rw [sum_range_min layerCount (1650 / j)
    (fun k hk => fastRemaining_zero (index_over hj hk))]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (min_le_right _ _))
section
set_option maxRecDepth 8192
set_option maxHeartbeats 0
theorem aux8_exclude_20_3 : zeroMass 20 3 < need := by decide
theorem aux8_exclude_18_4 : zeroMass 18 4 < need := by decide
theorem aux8_exclude_14_5 : zeroMass 14 5 < need := by decide
theorem aux8_exclude_7_6 : zeroMass 7 6 < need := by decide
theorem aux8_exclude_3_7 : zeroMass 3 7 < need := by decide
end
theorem retained_exclusions :
    zeroMass 20 3 < need ∧ zeroMass 18 4 < need ∧ zeroMass 14 5 < need ∧
    zeroMass 7 6 < need ∧ zeroMass 3 7 < need :=
  ⟨aux8_exclude_20_3, aux8_exclude_18_4, aux8_exclude_14_5,
    aux8_exclude_7_6, aux8_exclude_3_7⟩
theorem retained_bound (hcount : ∀ b j, remaining b j = fastRemaining b j)
    {r : Shape} (hr : Valid r)
    (hmass : need ≤ ∑ k ∈ Finset.range layerCount,
      remaining ((k + 1) * r.b) ((k + 1) * r.j)) : RetainedBox r := by
  have reject {b j : ℕ} (hb : b ≤ r.b) (hj : j ≤ r.j) (hjpos : 0 < j)
      (hsmall : zeroMass b j < need) : False := by
    have hle : need ≤ zeroMass b j := hmass.trans <|
      (Finset.sum_le_sum fun k _ => remaining_anti
        (Nat.mul_le_mul_left _ hb) (Nat.mul_le_mul_left _ hj)).trans
        (zeroMass_upper hcount hjpos)
    omega
  obtain ⟨ht, hjt, hjb⟩ := hr
  obtain ⟨h20, h18, h14, h7, hj7⟩ := retained_exclusions
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_contra! h; exact reject (by omega) (by omega) (by decide) h20
  · by_contra! h; exact reject (by omega) (by omega) (by decide) hj7
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) h18
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) h14
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) h7
theorem retainedBox_down {a r : Shape} (h : InBox a r) (hr : RetainedBox r) : RetainedBox a := by
  rcases h with ⟨hb, hj, _⟩
  rcases hr with ⟨hrb, hrj, h4, h5, h6⟩
  exact ⟨hb.trans hrb, hj.trans hrj, fun k => hb.trans (h4 (k.trans hj)),
    fun k => hb.trans (h5 (k.trans hj)), fun k => hb.trans (h6 (k.trans hj))⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem retained_prices_finite :
    ∀ (b : Fin 20) (j : Fin 7) (t : Fin 3),
      let a : Shape := ⟨b.val, j.val, t.val⟩
      Valid a → RetainedBox a →
      fatPrice a ≤ (if a.t = 1 then 37000000000000000 else 48500000000000000) * a.t :=
  by decide
theorem retained_price {a : Shape} (ha : Valid a) (hb : RetainedBox a) :
    fatPrice a ≤ (if a.t = 1 then 37000000000000000 else 48500000000000000) * a.t := by
  obtain ⟨b, j, t⟩ := a
  have hb' : b ≤ 19 := hb.1
  have hj' : j ≤ 6 := hb.2.1
  have ht : 3 * t ≤ j := ha.2.1
  exact retained_prices_finite ⟨b, by omega⟩ ⟨j, by omega⟩ ⟨t, by omega⟩ ha hb
def layerTerm (r y : Shape) (L k : ℕ) : ℕ :=
  remaining ((k + 1) * r.b + (k + 1 - L) * y.b)
    ((k + 1) * r.j + (k + 1 - L) * y.j)
theorem availableMass_eq_sum (hcount : ∀ b j, remaining b j = fastRemaining b j)
    {r y : Shape} {L N : ℕ} (hr : r = zeroShape ∨ 0 < r.j)
    (hj : 0 < r.j + y.j) (hN : L + 1650 / (r.j + y.j) ≤ N) :
    (∑ k ∈ Finset.range N, layerTerm r y L k) = availableMass r y L := by
  have hL : L ≤ N := (Nat.le_add_right _ _).trans hN
  conv_lhs => rw [← Nat.add_sub_of_le hL, Finset.sum_range_add]
  unfold availableMass
  congr 1
  · have hfirst : (∑ k ∈ Finset.range L, layerTerm r y L k) =
        ∑ k ∈ Finset.range L, fastRemaining ((k + 1) * r.b) ((k + 1) * r.j) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hz : k + 1 - L = 0 := by
        have := Finset.mem_range.mp hk
        omega
      simp [layerTerm, hz, hcount]
    rw [hfirst]
    rcases hr with rfl | hp
    · simp [zeroShape]
    · simp only [ite_eq_right (Nat.ne_of_gt hp)]
      exact sum_range_min L (1650 / r.j)
        (fun k hk => fastRemaining_zero (index_over hp hk))
  · have htail (k : ℕ) :
        layerTerm r y L (L + k) = fastRemaining (L * r.b + (k + 1) * (r.b + y.b))
          (L * r.j + (k + 1) * (r.j + y.j)) := by
      have hz : L + k + 1 - L = k + 1 := by omega
      rw [layerTerm, hz, hcount]
      congr 1 <;> ring
    simp_rw [htail]
    apply sum_range_truncate _ (by omega)
    intro k hk
    apply fastRemaining_zero
    exact (index_over hj hk).trans_le (Nat.le_add_left _ _)
theorem layerSum_le_available (hcount : ∀ b j, remaining b j = fastRemaining b j)
    {r y : Shape} {L : ℕ} (hr : r = zeroShape ∨ 0 < r.j) (hj : 0 < r.j + y.j) :
    (∑ k ∈ Finset.range layerCount, layerTerm r y L k) ≤ availableMass r y L := by
  let N := max layerCount (L + 1650 / (r.j + y.j))
  rw [← availableMass_eq_sum hcount hr hj (N := N) (le_max_right _ _)]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (le_max_left _ _))
theorem availableMass_mono (hcount : ∀ b j, remaining b j = fastRemaining b j)
    {r y : Shape} {L₁ L₂ : ℕ} (hr : r = zeroShape ∨ 0 < r.j)
    (hj : 0 < r.j + y.j) (hL : L₁ ≤ L₂) :
    availableMass r y L₁ ≤ availableMass r y L₂ := by
  let N := L₂ + 1650 / (r.j + y.j)
  rw [← availableMass_eq_sum hcount hr hj (N := N) (Nat.add_le_add_right hL _),
    ← availableMass_eq_sum hcount hr hj (N := N) le_rfl]
  exact Finset.sum_le_sum fun k _ => remaining_anti
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : k + 1 - L₂ ≤ k + 1 - L₁)) _)
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : k + 1 - L₂ ≤ k + 1 - L₁)) _)
theorem ceilDiv_anti (a : ℕ) {l u : ℕ} (hl : 0 < l) (h : l ≤ u) :
    ceilDiv a u ≤ ceilDiv a l := by
  have hu : 0 < u := hl.trans_le h
  have hceil (d q : ℕ) (hd : 0 < d) : ceilDiv a d ≤ q ↔ a ≤ q * d := by
    rw [ceilDiv, ← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hd, Nat.succ_mul]
    omega
  exact (hceil u _ hu).mpr <|
    ((hceil l _ hl).mp le_rfl).trans (Nat.mul_le_mul_left _ h)
theorem edgePrice_anti (a : Shape) {l u : ℕ} (hl : 0 < l) (h : l ≤ u) :
    edgePrice a u ≤ edgePrice a l := by
  have hp : physicalPrice a u ≤ physicalPrice a l := by
    unfold physicalPrice
    exact Nat.add_le_add_right (Nat.add_le_add_right (ceilDiv_anti _ hl h) _) _
  unfold edgePrice
  split <;> first | exact min_le_min hp le_rfl | exact hp
end K1_13_8
end
section
namespace K1_13_8
open K1_13
open scoped BigOperators
def c1 : Prop := ∀ b j, remaining b j = fastRemaining b j
def c2 : Prop := Bellman zeroShape 222142013343379695
def c3 : Prop := Bellman ⟨1, 3, 1⟩ 185142013343379695
def c4 : Prop := Bellman ⟨2, 6, 2⟩ 125142013343379695
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
theorem mass_le {n : ℕ} {a : Fin n → Shape} {l : Fin n → ℕ}
    (hlayers : LayerBudget a l) {z s : Finset (Fin n)} {q : Shape} {L : ℕ}
    (hz : ∀ i ∈ z, l i = 0) (hs : ∀ i ∈ s, l i ≤ L)
    (hdisj : Disjoint z s) (hq : InBox q (shapeSum a z)) :
    need ≤ ∑ k ∈ Finset.range layerCount, layerTerm q (shapeSum a s) L k := by
  refine hlayers.trans (Finset.sum_le_sum fun k _ => remaining_anti ?_ ?_)
  · exact spend_le (fun i => (a i).b) hz hs hdisj hq.1
  · exact spend_le (fun i => (a i).j) hz hs hdisj hq.2.1
theorem retained_cost {ι : Type*} {a : ι → Shape} {cost : ι → ℕ}
    {z : Finset ι} (ha : ∀ i, Valid (a i)) (hbox : RetainedBox (shapeSum a z))
    (hfat : ∀ i, FatEligible (a i) → cost i ≤ fatPrice (a i)) :
    (∑ i ∈ z, cost i) ≤
      (if (shapeSum a z).t = 1 then 37000000000000000 else 48500000000000000) *
        (shapeSum a z).t := by
  let r := shapeSum a z
  let rate : ℕ := if r.t = 1 then 37000000000000000 else 48500000000000000
  change (∑ i ∈ z, cost i) ≤ rate * ∑ i ∈ z, (a i).t
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hle : InBox (a i) r := inBox_shapeSum a hi
  have hsmall := retainedBox_down hle hbox
  have hcheap : FatEligible (a i) :=
    ⟨hsmall.1.trans (by decide), hsmall.2.1.trans (by decide)⟩
  refine (hfat i hcheap).trans ((retained_price (ha i) hsmall).trans ?_)
  apply Nat.mul_le_mul_right
  have ht := (ha i).1
  have hti := hle.2.2
  by_cases h : r.t = 1
  · have hai : (a i).t = 1 := by omega
    simp [rate, h, hai]
  · split <;> simp [rate, h]
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) : K1_13.c8 := by
  intro n a l cost hfits hlayers hphys hfat
  let z := Finset.univ.filter (fun i => l i = 0)
  let pos := Finset.univ.filter (fun i => ¬ l i = 0)
  let r := shapeSum a z
  have ha (i : Fin n) : Valid (a i) := hfits.1 i
  have hz (i : Fin n) (hi : i ∈ z) : l i = 0 := (Finset.mem_filter.mp hi).2
  have hpos (i : Fin n) (hi : i ∈ pos) : 0 < l i :=
    Nat.pos_of_ne_zero (Finset.mem_filter.mp hi).2
  have hdisj {s : Finset (Fin n)} (hs : s ⊆ pos) : Disjoint z s :=
    Finset.disjoint_left.mpr fun i hi his => (Nat.ne_of_gt (hpos i (hs his))) (hz i hi)
  have account : ∃ (q : Shape) (cap : ℕ), InBox q r ∧ (q = zeroShape ∨ 0 < q.j) ∧
      Bellman q cap ∧ (∑ i ∈ z, cost i) + cap ≤ 222142013343379695 := by
    rcases shapeSum_valid_or_empty ha z with hempty | hr
    · have hr0 : r = zeroShape := by simp [r, hempty, shapeSum_empty]
      refine ⟨zeroShape, 222142013343379695, ?_, Or.inl rfl, h2, ?_⟩
      · rw [hr0]
        exact ⟨le_rfl, le_rfl, le_rfl⟩
      · simp [hempty]
    · have hmass := mass_le hlayers (s := ∅) (q := r) (L := 0) hz (by simp) (by simp)
        (show InBox r r from ⟨le_rfl, le_rfl, le_rfl⟩)
      have hret : RetainedBox r := retained_bound h1 hr (by simpa [layerTerm, shapeSum_empty,
        zeroShape] using hmass)
      have hcost := retained_cost ha hret hfat
      have htr : 1 ≤ r.t := hr.1
      have hjr : 3 * r.t ≤ r.j := hr.2.1
      have hbr : r.j ≤ 3 * r.b := hr.2.2
      have hrj : r.j ≤ 6 := hret.2.1
      have ht : r.t = 1 ∨ r.t = 2 := by omega
      rcases ht with ht | ht
      · refine ⟨⟨1, 3, 1⟩, 185142013343379695, ?_, Or.inr (by decide), h3, ?_⟩
        · change 1 ≤ r.b ∧ 3 ≤ r.j ∧ 1 ≤ r.t
          omega
        · change (∑ i ∈ z, cost i) ≤ (if r.t = 1 then _ else _) * r.t at hcost
          rw [ite_eq_left ht, ht, Nat.mul_one] at hcost
          omega
      · refine ⟨⟨2, 6, 2⟩, 125142013343379695, ?_, Or.inr (by decide), h4, ?_⟩
        · change 2 ≤ r.b ∧ 6 ≤ r.j ∧ 2 ≤ r.t
          omega
        · change (∑ i ∈ z, cost i) ≤ (if r.t = 1 then _ else _) * r.t at hcost
          rw [ite_eq_right (by omega : r.t ≠ 1), ht] at hcost
          omega
  obtain ⟨q, cap, hqr, hq, ⟨B, order, hB0, horder, hB⟩, haccount⟩ := account
  have hall : InBox (shapeSum a Finset.univ) fullCap := hfits.2
  have hcap {s : Finset (Fin n)} (hs : s ⊆ pos) : InBox (q.plus (shapeSum a s)) fullCap := by
    have hb := shapeSum_mono a (Finset.subset_univ (z ∪ s))
    rw [shapeSum_union a (hdisj hs)] at hb
    have hle : InBox (q.plus (shapeSum a s)) (r.plus (shapeSum a s)) :=
      ⟨Nat.add_le_add_right hqr.1 _, Nat.add_le_add_right hqr.2.1 _,
        Nat.add_le_add_right hqr.2.2 _⟩
    exact inBox_trans hle (inBox_trans hb hall)
  have positive_bound (s : Finset (Fin n)) : s ⊆ pos →
      (∑ i ∈ s, cost i) + B (shapeSum a s) ≤ B zeroShape := by
    refine Finset.strongInductionOn s fun s ih hs => ?_
    by_cases he : s.Nonempty
    · obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image s l he
      let t := s.erase i
      have hti : i ∉ t := Finset.notMem_erase i s
      have hin : insert i t = s := Finset.insert_erase hi
      have hts : t ⊆ s := Finset.erase_subset i s
      have hprev := ih t (Finset.erase_ssubset hi) (hts.trans hs)
      have hvalid : shapeSum a t = zeroShape ∨ Valid (shapeSum a t) := by
        rcases shapeSum_valid_or_empty ha t with ht | ht
        · exact Or.inl (ht ▸ shapeSum_empty a)
        · exact Or.inr ht
      have hsvalid : Valid (shapeSum a s) := by
        rcases shapeSum_valid_or_empty ha s with hempty | hv
        · exact (he.ne_empty hempty).elim
        · exact hv
      have hL : 0 < l i := hpos i (hs hi)
      have hj : 0 < q.j + (shapeSum a s).j := by
        obtain ⟨ht, hidx, _⟩ := hsvalid
        omega
      have hmass : need ≤ availableMass q (shapeSum a s) (l i) :=
        (mass_le hlayers hz hmax (hdisj hs) hqr).trans (layerSum_le_available h1 hq hj)
      have hc := hcap hs
      obtain ⟨horderPos, horderTest⟩ := horder _ hsvalid hc
      have hord : order (shapeSum a s) ≤ l i := by
        rcases horderTest with heq | htest
        · omega
        · by_contra! h
          have hmono : availableMass q (shapeSum a s) (l i) ≤
              availableMass q (shapeSum a s) (order (shapeSum a s) - 1) :=
            availableMass_mono h1 hq hj (by omega)
          exact (not_lt_of_ge (hmass.trans hmono)) htest
      have hstep : edgePrice (a i) (l i) + B (shapeSum a s) ≤ B (shapeSum a t) := by
        have hshape : shapeSum a s = (shapeSum a t).plus (a i) :=
          hin ▸ shapeSum_insert a hti
        refine (Nat.add_le_add_right (edgePrice_anti _ horderPos hord) _).trans ?_
        rw [hshape] at hc ⊢
        exact hB _ _ hvalid (ha i) hc
      have hfee : cost i ≤ edgePrice (a i) (l i) := by
        unfold edgePrice
        split
        · exact le_min (hphys i hL) (hfat i ‹FatEligible (a i)›)
        · exact hphys i hL
      rw [← hin, Finset.sum_insert hti, hin]
      omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp he, shapeSum_empty]
  have hpaid := positive_bound pos (Finset.Subset.rfl)
  have hpartition : (∑ i ∈ z, cost i) + (∑ i ∈ pos, cost i) = ∑ i, cost i :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  omega
end K1_13_8
end
section
namespace K1_13_8_2
open K1_13 K1_13_8
def limit : ℕ := 0x31534fbf305b0ef
structure Threshold where
  b : ℕ
  j : ℕ
  l : ℕ
def thresholds : List Threshold :=
  [⟨118,48,58⟩,⟨103,43,57⟩,⟨67,30,52⟩,⟨11,16,34⟩,
   ⟨4,11,17⟩,⟨48,4,15⟩,⟨5,9,7⟩,⟨27,6,3⟩,
   ⟨19,7,2⟩,⟨36,4,2⟩,⟨9,8,2⟩,⟨26,6,2⟩]
def orderFor (b j : ℕ) : List Threshold → ℕ
  | [] => 1
  | s :: rest =>
      max (if s.b ≤ b ∧ s.j ≤ j then s.l else 1) (orderFor b j rest)
def indexBudget (j : ℕ) : ℕ := limit * j / 48
end K1_13_8_2
end
section
namespace K1_13_8_2
open K1_13
def Chamber (p : Shape) : Prop := p.j ≤ p.b ∧ 3 * p.t ≤ p.j
private def signedMixed (p q r s : Shape) : ℤ :=
  difference (difference (difference (difference volume32 p) q) r) s ⟨0, 0, 0⟩
theorem signed_add (p a q r s : Shape) :
    signedMixed (p.plus a) q r s = signedMixed p q r s + signedMixed a q r s := by
  simp only [signedMixed, difference, volume32, Shape.plus, Nat.cast_add, Nat.cast_zero]
  ring
private theorem signed_rotate (p q r s : Shape) :
    signedMixed p q r s = signedMixed q r s p := by
  simp only [signedMixed, difference, volume32, Shape.plus, Nat.cast_add, Nat.cast_zero]
  ring
theorem chamber_coords (p : Shape) (h : Chamber p) :
    (p.b : ℤ) = (↑(p.b - p.j) : ℤ) + ↑(p.j - 3 * p.t) + 3 * p.t ∧
    (p.j : ℤ) = (↑(p.j - 3 * p.t) : ℤ) + 3 * p.t := by
  obtain ⟨hb, hj⟩ := h
  constructor <;> exact_mod_cast (by omega : _)
private theorem signed_nonneg (d q r s : Shape) (hq : Chamber q) (hr : Chamber r)
    (hs : Chamber s) : 0 ≤ signedMixed d q r s := by
  obtain ⟨hqb, hqj⟩ := chamber_coords q hq
  obtain ⟨hrb, hrj⟩ := chamber_coords r hr
  obtain ⟨hsb, hsj⟩ := chamber_coords s hs
  simp only [signedMixed, difference, volume32, Shape.plus, Nat.cast_add, Nat.cast_zero]
  rw [hqb, hqj, hrb, hrj, hsb, hsj]
  ring_nf
  positivity
theorem mixed_mono_first {p p' : Shape} (h : InBox p p') {q r s : Shape}
    (hq : Chamber q) (hr : Chamber r) (hs : Chamber s) :
    mixed32 p q r s ≤ mixed32 p' q r s := by
  let d : Shape := ⟨p'.b - p.b, p'.j - p.j, p'.t - p.t⟩
  have hp : p.plus d = p' := by
    obtain ⟨pb, pj, pt⟩ := p
    obtain ⟨qb, qj, qt⟩ := p'
    obtain ⟨hb, hj, ht⟩ := h
    simp [Shape.plus, d, Nat.add_sub_of_le hb, Nat.add_sub_of_le hj, Nat.add_sub_of_le ht]
  change (signedMixed p q r s).toNat ≤ (signedMixed p' q r s).toNat
  apply Int.toNat_le_toNat
  rw [← hp, signed_add]
  exact le_add_of_nonneg_right (signed_nonneg d q r s hq hr hs)
theorem mixed_rotate (p q r s : Shape) :
    mixed32 p q r s = mixed32 q r s p := congrArg Int.toNat (signed_rotate p q r s)
theorem mixed_mono {p q r s p' q' r' s' : Shape}
    (hp : InBox p p') (hq : InBox q q') (hr : InBox r r') (hs : InBox s s')
    (hp' : Chamber p') (hq' : Chamber q') (hr' : Chamber r')
    (hqs : Chamber q) (hrs : Chamber r) (hss : Chamber s) :
    mixed32 p q r s ≤ mixed32 p' q' r' s' := by
  calc
    mixed32 p q r s ≤ mixed32 p' q r s := mixed_mono_first hp hqs hrs hss
    _ = mixed32 q r s p' := mixed_rotate _ _ _ _
    _ ≤ mixed32 q' r s p' := mixed_mono_first hq hrs hss hp'
    _ = mixed32 r s p' q' := mixed_rotate _ _ _ _
    _ ≤ mixed32 r' s p' q' := mixed_mono_first hr hss hp' hq'
    _ = mixed32 s p' q' r' := mixed_rotate _ _ _ _
    _ ≤ mixed32 s' p' q' r' := mixed_mono_first hs hp' hq' hr'
    _ = mixed32 p' q' r' s' := mixed_rotate _ _ _ _
end K1_13_8_2
end
section
namespace K1_13_8_4
open K1_13
def TotalLE (a A : Shape) : Prop := a.b ≤ A.b ∧ a.j = A.j ∧ a.t = A.t
def IndexFits (a : Shape) : Prop := 3 * a.t ≤ a.j
theorem TotalLE.refl (a : Shape) : TotalLE a a := ⟨le_rfl, rfl, rfl⟩
def mixedZ (p q r s : Shape) : ℤ :=
  difference (difference (difference (difference volume32 p) q) r) s ⟨0, 0, 0⟩
def indexCubic (a : Shape) : ℤ :=
  let j : ℤ := a.j
  let t : ℤ := a.t
  8*j^2*t - 24*j*t^2 + 24*t^3
def unusedIndex (a : Shape) : ℤ := (a.j : ℤ) - 3 * (a.t : ℤ)
def totalCoeff (q r s : Shape) : ℤ :=
  let u := unusedIndex q
  let v := unusedIndex r
  let w := unusedIndex s
  let x : ℤ := q.t
  let y : ℤ := r.t
  let z : ℤ := s.t
  16 * (u*v*z + u*y*w + x*v*w) + 48 * (u*y*z + x*v*z + x*y*w) + 144*x*y*z
theorem totalCoeff_nonneg {q r s : Shape}
    (hq : IndexFits q) (hr : IndexFits r) (hs : IndexFits s) : 0 ≤ totalCoeff q r s := by
  have nonneg {a : Shape} (ha : IndexFits a) : 0 ≤ unusedIndex a := by
    have h : 3 * a.t ≤ a.j := ha
    unfold unusedIndex
    omega
  have hq' := nonneg hq
  have hr' := nonneg hr
  have hs' := nonneg hs
  unfold totalCoeff
  positivity
private theorem difference_sub (f g : Shape → ℤ) (a x : Shape) :
    difference f a x - difference g a x = difference (fun y => f y - g y) a x := by
  unfold difference
  ring
private theorem difference_comm (f : Shape → ℤ) (a b : Shape) :
    difference (difference f a) b = difference (difference f b) a := by
  funext x
  have h : (x.plus b).plus a = (x.plus a).plus b := by
    cases x
    cases a
    cases b
    simp [Shape.plus, Nat.add_right_comm]
  simp only [difference, h]
  ring
set_option maxHeartbeats 2000000 in
theorem mixed_first {p P q r s : Shape}
    (hp : TotalLE p P) (hq : IndexFits q) (hr : IndexFits r) (hs : IndexFits s) :
    mixed32 p q r s ≤ mixed32 P q r s := by
  rcases hp with ⟨hb, hj, ht⟩
  let d : ℤ := (P.b : ℤ) - (p.b : ℤ)
  have hd : 0 ≤ d := by
    dsimp [d]
    omega
  have hfirst (x : Shape) :
      difference volume32 P x - difference volume32 p x = d * indexCubic (x.plus p) := by
    simp only [difference, volume32, indexCubic, Shape.plus, hj, ht, Nat.cast_add, d]
    ring
  change (mixedZ p q r s).toNat ≤ (mixedZ P q r s).toNat
  apply Int.toNat_le_toNat
  apply sub_nonneg.mp
  unfold mixedZ
  simp only [difference_sub, hfirst]
  have hcoeff :
      difference (difference (difference (fun x => d * indexCubic (x.plus p)) q) r)
        s ⟨0, 0, 0⟩ = d * totalCoeff q r s := by
    simp only [difference, indexCubic, totalCoeff, unusedIndex,
      Shape.plus, Nat.cast_add, Nat.cast_zero]
    ring
  rw [hcoeff]
  exact mul_nonneg hd (totalCoeff_nonneg hq hr hs)
theorem swap12 (a b c d : Shape) : mixed32 a b c d = mixed32 b a c d := by
  unfold mixed32
  rw [difference_comm volume32 a b]
theorem swap23 (a b c d : Shape) : mixed32 a b c d = mixed32 a c b d := by
  unfold mixed32
  rw [difference_comm (difference volume32 a) b c]
theorem swap34 (a b c d : Shape) : mixed32 a b c d = mixed32 a b d c := by
  unfold mixed32
  rw [difference_comm (difference (difference volume32 a) b) c d]
theorem mixed_totalLE {p P q Q r R s S : Shape}
    (hp : TotalLE p P) (hq : TotalLE q Q) (hr : TotalLE r R) (hs : TotalLE s S)
    (hP : IndexFits P) (hQ : IndexFits Q) (hR : IndexFits R)
    (hq' : IndexFits q) (hr' : IndexFits r) (hs' : IndexFits s) :
    mixed32 p q r s ≤ mixed32 P Q R S := by
  calc
    _ ≤ mixed32 P q r s := mixed_first hp hq' hr' hs'
    _ ≤ mixed32 P Q r s := by
      rw [swap12 P q, swap12 P Q]
      exact mixed_first hq hP hr' hs'
    _ ≤ mixed32 P Q R s := by
      rw [swap23 P Q r, swap12 P r, swap23 P Q R, swap12 P R]
      exact mixed_first hr hP hQ hs'
    _ ≤ _ := by
      rw [swap34 P Q R s, swap23 P Q s, swap12 P s,
        swap34 P Q R S, swap23 P Q S, swap12 P S]
      exact mixed_first hs hP hQ hR
theorem TotalLE.indexFits {a A : Shape} (h : TotalLE a A) (ha : IndexFits a) :
    IndexFits A := by
  unfold IndexFits at *
  rw [← h.2.1, ← h.2.2]
  exact ha
theorem mixed_mono_total {p P q Q r R s S : Shape}
    (hp : TotalLE p P) (hq : TotalLE q Q) (hr : TotalLE r R) (hs : TotalLE s S)
    (hp' : IndexFits p) (hq' : IndexFits q) (hr' : IndexFits r) (hs' : IndexFits s) :
    mixed32 p q r s ≤ mixed32 P Q R S :=
  mixed_totalLE hp hq hr hs (hp.indexFits hp') (hq.indexFits hq') (hr.indexFits hr') hq' hr' hs'
end K1_13_8_4
end
section
namespace K1_13_8_1
open K1_13_8
def row (r : ℕ) (j : ℤ) : ℤ :=
  if 0 ≤ j then coefficient r j.toNat else 0
theorem row_neg (r : ℕ) {j : ℤ} (h : j < 0) : row r j = 0 := by
  simp [row, not_le.mpr h]
theorem row_nonneg (r : ℕ) (j : ℤ) : 0 ≤ row r j := by
  unfold row
  split <;> omega
theorem row_nat (r j : ℕ) : row r j = coefficient r j := by simp [row]
def difference (w : ℤ) (f : ℤ → ℤ) (j : ℤ) : ℤ := f j - f (j - w)
def step (j : ℤ) : ℤ := if 0 ≤ j then 1 else 0
private def polynomial (r s : ℕ) (q : ℤ) : ℤ :=
  let (a, b, c, d, e) := coefficients r s
  24 * a + 24 * b * q + 12 * c * q * (q - 1) +
    4 * d * q * (q - 1) * (q - 2) + e * q * (q - 1) * (q - 2) * (q - 3)
theorem scaled_coefficient (r q s : ℕ) (hq : 3 ≤ q) (hs : s < 6) :
    24 * (coefficient r (6 * q + s) : ℤ) = polynomial r s q := by
  have hdiv : (6 * q + s) / 6 = q := by omega
  have hmod : (6 * q + s) % 6 = s := by omega
  unfold coefficient polynomial
  rw [hdiv, hmod]
  generalize coefficients r s = t
  rcases t with ⟨a, b, c, d, e⟩
  have hd₂ : 2 ∣ q * (q - 1) := by
    simpa [Nat.descFactorial_succ, mul_comm] using Nat.factorial_dvd_descFactorial q 2
  have hd₃ : 6 ∣ q * (q - 1) * (q - 2) := by
    simpa [Nat.descFactorial_succ, Nat.factorial_succ, mul_comm, mul_left_comm, mul_assoc] using
      Nat.factorial_dvd_descFactorial q 3
  have hd₄ : 24 ∣ q * (q - 1) * (q - 2) * (q - 3) := by
    simpa [Nat.descFactorial_succ, Nat.factorial_succ, mul_comm, mul_left_comm, mul_assoc] using
      Nat.factorial_dvd_descFactorial q 4
  have h₂ := congrArg (fun n : ℕ => (n : ℤ)) (Nat.mul_div_cancel' hd₂)
  have h₃ := congrArg (fun n : ℕ => (n : ℤ)) (Nat.mul_div_cancel' hd₃)
  have h₄ := congrArg (fun n : ℕ => (n : ℤ)) (Nat.mul_div_cancel' hd₄)
  simp only [Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, Int.ofNat_sub (show 1 ≤ q by omega),
    Int.ofNat_sub (show 2 ≤ q by omega), Int.ofNat_sub hq] at h₂ h₃ h₄
  simp only [Nat.cast_add, Nat.cast_mul]
  linear_combination 12 * (c : ℤ) * h₂ + 4 * (d : ℤ) * h₃ + (e : ℤ) * h₄
private theorem scaled_shift (r q i v : ℕ) (hq : 3 ≤ q) (hv : v ≤ i) :
    24 * row r (6 * (q : ℤ) + i - v) = polynomial r ((i - v) % 6)
      ((q : ℤ) + ((i - v) / 6 : ℕ)) := by
  have h : 6 * (q : ℤ) + i - v =
      ((6 * (q + (i - v) / 6) + (i - v) % 6 : ℕ) : ℤ) := by omega
  rw [h, row_nat, scaled_coefficient r _ _ (by omega) (by omega), Nat.cast_add]
theorem core_step (j : ℤ) :
    difference 1 (difference 2 (difference 3 (row 0))) j = step j := by
  by_cases hn : j < 0
  · simp [difference, step, not_le.mpr hn, row_neg _ hn, row_neg, show j - 3 < 0 by omega,
      show j - 2 < 0 by omega, show j - 2 - 3 < 0 by omega,
      show j - 1 < 0 by omega, show j - 1 - 3 < 0 by omega,
      show j - 1 - 2 < 0 by omega, show j - 1 - 2 - 3 < 0 by omega]
  by_cases hs : j < 24
  · interval_cases j <;> decide
  let q := j.toNat / 6 - 1
  let s := j.toNat % 6
  have hq : 3 ≤ q := by dsimp [q]; omega
  have hsr : s < 6 := by dsimp [s]; omega
  have hj : j = 6 * (q : ℤ) + ((6 + s : ℕ) : ℤ) := by dsimp [q, s]; omega
  have hstep : step j = 1 := by simp [step, show 0 ≤ j by omega]
  have h := scaled_shift 0 q (6 + s) 0 hq (by omega)
  have h₁ := scaled_shift 0 q (6 + s) 1 hq (by omega)
  have h₂ := scaled_shift 0 q (6 + s) 2 hq (by omega)
  have h₄ := scaled_shift 0 q (6 + s) 4 hq (by omega)
  have h₅ := scaled_shift 0 q (6 + s) 5 hq (by omega)
  have h₆ := scaled_shift 0 q (6 + s) 6 hq (by omega)
  have hp : polynomial 0 ((6 + s - 0) % 6) ((q : ℤ) + ((6 + s - 0) / 6 : ℕ)) -
      polynomial 0 ((6 + s - 1) % 6) ((q : ℤ) + ((6 + s - 1) / 6 : ℕ)) -
      polynomial 0 ((6 + s - 2) % 6) ((q : ℤ) + ((6 + s - 2) / 6 : ℕ)) +
      polynomial 0 ((6 + s - 4) % 6) ((q : ℤ) + ((6 + s - 4) / 6 : ℕ)) +
      polynomial 0 ((6 + s - 5) % 6) ((q : ℤ) + ((6 + s - 5) / 6 : ℕ)) -
      polynomial 0 ((6 + s - 6) % 6) ((q : ℤ) + ((6 + s - 6) / 6 : ℕ)) = 24 := by
    clear_value q s
    interval_cases s <;> norm_num [polynomial, coefficients] <;> ring
  rw [← h, ← h₁, ← h₂, ← h₄, ← h₅, ← h₆] at hp
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, sub_zero, ← hj] at hp
  simp only [difference, hstep]
  rw [show j - 2 - 3 = j - 5 by omega, show j - 1 - 3 = j - 4 by omega,
    show j - 1 - 2 = j - 3 by omega, show j - 3 - 3 = j - 6 by omega]
  omega
theorem extra_step (r : ℕ) (hr : 1 ≤ r) (hr' : r ≤ 3) (j : ℤ) :
    difference r (row r) j = row 0 j := by
  by_cases hn : j < 0
  · simp [difference, row_neg _ hn, row_neg _ (show j - r < 0 by omega)]
  by_cases hs : j < 24
  · interval_cases r <;> interval_cases j <;> decide
  let q := j.toNat / 6 - 1
  let s := j.toNat % 6
  have hq : 3 ≤ q := by dsimp [q]; omega
  have hsr : s < 6 := by dsimp [s]; omega
  have hj : j = 6 * (q : ℤ) + ((6 + s : ℕ) : ℤ) := by dsimp [q, s]; omega
  have h₁ := scaled_shift r q (6 + s) 0 hq (by omega)
  have h₂ := scaled_shift r q (6 + s) r hq (by omega)
  have h₃ := scaled_shift 0 q (6 + s) 0 hq (by omega)
  have hp : polynomial r ((6 + s - 0) % 6) ((q : ℤ) + ((6 + s - 0) / 6 : ℕ)) -
      polynomial r ((6 + s - r) % 6) ((q : ℤ) + ((6 + s - r) / 6 : ℕ)) =
      polynomial 0 ((6 + s - 0) % 6) ((q : ℤ) + ((6 + s - 0) / 6 : ℕ)) := by
    clear_value q s
    interval_cases r <;> interval_cases s <;> norm_num [polynomial, coefficients] <;> ring
  rw [← h₁, ← h₂, ← h₃] at hp
  simp only [Nat.cast_zero, sub_zero, ← hj] at hp
  unfold difference
  omega
end K1_13_8_1
end
section
namespace K1_13_8_1
open scoped BigOperators
private def count (base : ℕ → ℤ → ℤ) : ℕ → ℕ → ℤ → ℤ
  | 0, b, j => base b j
  | k + 1, b, j =>
      ∑ i ∈ Finset.range (b + 1), count base k (b - i) (j - ((k : ℤ) + 1) * i)
def exactBase (_ : ℕ) (j : ℤ) : ℤ := step j
def boxBase (b : ℕ) (j : ℤ) : ℤ := ((b : ℤ) + 1) * step j
theorem count_zero_degree (base : ℕ → ℤ → ℤ) (k : ℕ) (j : ℤ) :
    count base k 0 j = base 0 j := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [count] using ih
theorem count_succ_degree (base : ℕ → ℤ → ℤ) (k b : ℕ) (j : ℤ) :
    count base (k + 1) (b + 1) j =
      count base k (b + 1) j + count base (k + 1) b (j - ((k : ℤ) + 1)) := by
  simp only [count]
  rw [Finset.sum_range_succ', add_comm]
  simp only [Nat.sub_zero, Nat.cast_zero, mul_zero, sub_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show b + 1 - (i + 1) = b - i by omega]
  congr 1
  push_cast
  ring
theorem count_neg (base : ℕ → ℤ → ℤ)
    (hn : ∀ b j, j < 0 → base b j = 0) (k b : ℕ) (j : ℤ) (hj : j < 0) :
    count base k b j = 0 := by
  induction k generalizing b j with
  | zero => exact hn b j hj
  | succ k ih =>
      apply Finset.sum_eq_zero
      intro i _
      apply ih
      have h : 0 ≤ ((k : ℤ) + 1) * (i : ℤ) := by positivity
      omega
theorem count_clip (base : ℕ → ℤ → ℤ)
    (hn : ∀ b j, j < 0 → base b j = 0) (k b j : ℕ) :
    count base (k + 1) b j =
      ∑ i ∈ Finset.range (min b (j / (k + 1)) + 1),
        count base k (b - i) (j - (k + 1) * i : ℕ) := by
  let w := k + 1
  let f := fun i : ℕ => count base k (b - i) ((j : ℤ) - (w : ℤ) * i)
  change (∑ i ∈ Finset.range (b + 1), f i) = _
  have hw : 0 < w := by dsimp [w]; omega
  calc
    _ = ∑ i ∈ Finset.range (min b (j / w) + 1), f i := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (min_le_left _ _)))
      intro i hi hout
      have hib := Finset.mem_range.mp hi
      have hij : j / w < i := by
        have h := mt Finset.mem_range.mpr hout
        omega
      have hs := (Nat.div_lt_iff_lt_mul hw).mp hij
      unfold f
      apply count_neg base hn
      rw [← Nat.cast_mul, mul_comm w i]
      exact sub_neg.mpr (by exact_mod_cast hs)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      have hm := Finset.mem_range.mp hi
      have hij : i ≤ j / w := by omega
      have hs := (Nat.le_div_iff_mul_le hw).mp hij
      rw [mul_comm] at hs
      unfold f
      rw [← Nat.cast_mul, Int.ofNat_sub hs]
theorem boxBase_neg (b : ℕ) (j : ℤ) (h : j < 0) : boxBase b j = 0 := by
  simp [boxBase, step, not_le.mpr h]
theorem symbols_count (b j : ℕ) :
    (K1_13.symbols b j : ℤ) = count boxBase 3 b j := by
  rw [count_clip boxBase boxBase_neg 2]
  simp_rw [count_clip boxBase boxBase_neg 1, count_clip boxBase boxBase_neg 0]
  simp [K1_13.symbols, count, boxBase, step, Nat.cast_sum, Nat.cast_add]
theorem box_eq_sum (k b : ℕ) (j : ℤ) :
    count boxBase k b j = ∑ d ∈ Finset.range (b + 1), count exactBase k d j := by
  induction k generalizing b j with
  | zero => simp [count, boxBase, exactBase, Nat.cast_add]
  | succ k ihk =>
      induction b generalizing j with
      | zero => simp [count_zero_degree, boxBase, exactBase]
      | succ b ihb =>
          rw [count_succ_degree, ihk, ihb]
          conv_rhs => rw [Finset.sum_range_succ']
          simp_rw [count_succ_degree exactBase, Finset.sum_add_distrib]
          rw [Finset.sum_range_succ' (fun d => count exactBase k d j) (b + 1)]
          simp only [count_zero_degree]
          abel
private def shift (w : ℤ) (f : ℤ → ℤ) (j : ℤ) : ℤ := f (j - w)
private def factors (a : ℤ) : ℕ → (ℤ → ℤ) → (ℤ → ℤ)
  | 0, f => f
  | k + 1, f => factors a k (difference (a + k) f)
theorem factors_first (a : ℤ) (k : ℕ) (f : ℤ → ℤ) :
    factors a (k + 1) f = factors (a + 1) k (difference a f) := by
  induction k generalizing f with
  | zero => simp [factors]
  | succ k ih =>
      rw [factors, ih, factors]
      have h : a + ((k + 1 : ℕ) : ℤ) = a + 1 + k := by omega
      rw [h]
      congr 1
      funext j
      simp only [difference]
      rw [show j - a - (a + 1 + k) = j - (a + 1 + k) - a by ring]
      ring
theorem factors_sub (a : ℤ) (k : ℕ) (f g : ℤ → ℤ) :
    factors a k (fun j => f j - g j) = fun j => factors a k f j - factors a k g j := by
  induction k generalizing f g with
  | zero => rfl
  | succ k ih =>
      have h : difference (a + k) (fun j => f j - g j) =
          fun j => difference (a + k) f j - difference (a + k) g j := by
        funext j
        simp only [difference]
        ring
      simpa only [factors, h] using ih (difference (a + k) f) (difference (a + k) g)
theorem factors_shift (a w : ℤ) (k : ℕ) (f : ℤ → ℤ) :
    factors a k (shift w f) = shift w (factors a k f) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
      have h : difference (a + k) (shift w f) = shift w (difference (a + k) f) := by
        funext j
        simp only [difference, shift]
        rw [show j - (a + k) - w = j - w - (a + k) by ring]
      simpa only [factors, h] using ih (difference (a + k) f)
private def denominator : ℕ → ℤ → ℤ
  | 0 => difference 1 (difference 2 (difference 3 (row 0)))
  | 1 => difference 2 (difference 3 (row 0))
  | 2 => difference 3 (row 0)
  | _ => row 0
theorem denominator_diff (k : ℕ) (hk : k < 3) :
    difference ((k : ℤ) + 1) (denominator (k + 1)) = denominator k := by
  interval_cases k <;> rfl
def gaussian (k b : ℕ) : ℤ → ℤ := factors ((b : ℤ) + 1) k (denominator k)
theorem gaussian_zero (k : ℕ) (hk : k ≤ 3) (j : ℤ) : gaussian k 0 j = step j := by
  induction k with
  | zero => exact core_step j
  | succ k ih =>
      have hd := denominator_diff k (by omega)
      simpa only [gaussian, factors, Nat.cast_zero, zero_add, add_comm (1 : ℤ) k, hd] using
        ih (by omega)
theorem gaussian_succ (k b : ℕ) (hk : k < 3) (j : ℤ) :
    gaussian (k + 1) (b + 1) j =
      gaussian k (b + 1) j + gaussian (k + 1) b (j - ((k : ℤ) + 1)) := by
  let a := (b : ℤ) + 1
  let w := (k : ℤ) + 1
  let f := denominator (k + 1)
  have ha : ((b + 1 : ℕ) : ℤ) + 1 = a + 1 := by rfl
  simp only [gaussian, ha]
  change factors (a + 1) (k + 1) f j =
    factors (a + 1) k (denominator k) j + factors a (k + 1) f (j - w)
  rw [factors_first a k]
  apply sub_eq_iff_eq_add.mp
  change factors (a + 1) k (difference (a + 1 + k) f) j -
      shift w (factors (a + 1) k (difference a f)) j = _
  rw [← factors_shift, ← congrFun (factors_sub _ _ _ _) j]
  have h : (fun j => difference (a + 1 + k) f j - shift w (difference a f) j) =
      difference w f := by
    funext j
    simp only [difference, shift, w]
    rw [show j - (a + 1 + k) = j - ((k : ℤ) + 1) - a by ring]
    ring
  rw [h, denominator_diff k hk]
theorem exact_gaussian (k b : ℕ) (hk : k ≤ 3) (j : ℤ) :
    count exactBase k b j = gaussian k b j := by
  induction k generalizing b j with
  | zero => exact (core_step j).symm
  | succ k ihk =>
      induction b generalizing j with
      | zero => exact (count_zero_degree _ _ _).trans (gaussian_zero _ hk _).symm
      | succ b ihb =>
          rw [count_succ_degree, gaussian_succ k b (by omega), ihk _ (by omega), ihb]
theorem symbols_gaussian (b j : ℕ) :
    (K1_13.symbols b j : ℤ) = ∑ d ∈ Finset.range (b + 1), gaussian 3 d j := by
  rw [symbols_count, box_eq_sum]
  exact Finset.sum_congr rfl fun d _ => exact_gaussian 3 d (by omega) j
theorem gaussian_expand (d : ℕ) (j : ℤ) :
    gaussian 3 d j =
      row 0 j - (row 0 (j - (1 + d)) + row 0 (j - (2 + d)) + row 0 (j - (3 + d))) +
        (row 0 (j - (3 + 2 * d)) + row 0 (j - (4 + 2 * d)) + row 0 (j - (5 + 2 * d))) -
        row 0 (j - (6 + 3 * d)) := by
  simp only [gaussian, factors, denominator, difference]
  push_cast
  ring_nf
end K1_13_8_1
end
section
namespace K1_13_8_1
open K1_13_8
open scoped BigOperators
theorem sum_shifted (b r : ℕ) (hr : 1 ≤ r) (hr' : r ≤ 3) (j v : ℤ) :
    (∑ d ∈ Finset.range (b + 1), row 0 (j - (v + (r : ℤ) * d))) =
      row r (j - v) - row r (j - (v + (r : ℤ) * ((b : ℤ) + 1))) := by
  induction b with
  | zero =>
      simpa [difference, sub_sub] using (extra_step r hr hr' (j - v)).symm
  | succ b ih =>
      rw [Finset.sum_range_succ, ih]
      have h := extra_step r hr hr' (j - (v + (r : ℤ) * ((b : ℤ) + 1)))
      simp only [difference] at h
      simp only [Nat.cast_succ]
      rw [show j - (v + (r : ℤ) * ((b : ℤ) + 1)) - r =
        j - (v + (r : ℤ) * ((b : ℤ) + 1 + 1)) by ring] at h
      omega
theorem shifted_cast (r j v : ℕ) :
    (shifted r j v : ℤ) = row r ((j : ℤ) - v) := by
  unfold shifted
  split
  · rw [← Int.ofNat_sub ‹v ≤ j›, row_nat]
  · have h : (j : ℤ) - v < 0 := by omega
    simp [row_neg _ h]
theorem across_cast (b r j v : ℕ) (hr : 1 ≤ r) (hr' : r ≤ 3) :
    (across b r j v : ℤ) = row r ((j : ℤ) - v) -
      row r ((j : ℤ) - (v + (r : ℤ) * ((b : ℤ) + 1))) := by
  have h₁ := shifted_cast r j v
  have h₂ := shifted_cast r j (v + r * (b + 1))
  push_cast at h₂
  have hn : 0 ≤ row r ((j : ℤ) - v) - row r ((j : ℤ) - (v + (r : ℤ) * ((b : ℤ) + 1))) := by
    rw [← sum_shifted b r hr hr']
    exact Finset.sum_nonneg fun _ _ => row_nonneg _ _
  unfold across
  rw [Int.ofNat_sub (by omega), h₁, h₂]
theorem cast_sub_of_eq {count positive negative : ℕ}
    (h : (count : ℤ) = (positive : ℤ) - (negative : ℤ)) :
    count = positive - negative := by omega
theorem symbols_eq_fast (b j : ℕ) : K1_13.symbols b j = fastSymbols b j := by
  unfold fastSymbols
  apply cast_sub_of_eq
  rw [symbols_gaussian]
  simp only [gaussian_expand, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    across_cast b 1 j _ (by decide) (by decide),
    across_cast b 2 j _ (by decide) (by decide),
    across_cast b 3 j _ (by decide) (by decide), ← row_nat]
  have h (v : ℤ) :
      (∑ d ∈ Finset.range (b + 1), row 0 (j - (v + (d : ℤ)))) =
        row 1 (j - v) - row 1 (j - (v + ((b : ℤ) + 1))) := by
    simpa only [Nat.cast_one, one_mul] using sum_shifted b 1 (by decide) (by decide) j v
  have h₂ (v : ℤ) :
      (∑ d ∈ Finset.range (b + 1), row 0 (j - (v + 2 * d))) =
        row 2 (j - v) - row 2 (j - (v + 2 * ((b : ℤ) + 1))) := by
    simpa only [Nat.cast_ofNat] using sum_shifted b 2 (by decide) (by decide) j v
  have h₃ :
      (∑ d ∈ Finset.range (b + 1), row 0 (j - (6 + 3 * d))) =
        row 3 (j - 6) - row 3 (j - (6 + 3 * ((b : ℤ) + 1))) := by
    simpa only [Nat.cast_ofNat] using sum_shifted b 3 (by decide) (by decide) j 6
  rw [h 1, h 2, h 3, h₂ 3, h₂ 4, h₂ 5, h₃]
  norm_num
  ring
theorem proof : K1_13_8.c1 := by
  intro b j
  simp only [K1_13.remaining, fastRemaining, symbols_eq_fast]
end K1_13_8_1
end
section
namespace K1_14_2_2_2
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 K1_14_3_2
open scoped BigOperators
def afterGcd (s : Shape) (x y : ℕ) : Shape :=
  ⟨s.m, s.B-y, min s.J (s.B-y), s.U-x⟩
abbrev cheapZero : Shape := (stageAt 0).cheap
abbrev layeredZero : Shape := (stageAt 0).layered
structure PreparedPair (P Q : Jet) (G H : ODE) where
  seedContent : Seeds
  cheap : Jet
  layered : Jet
  ordinary : Finset Equation
  gcdSeed : ℕ
  gcdY : ℕ
  seedContent_ne : seedContent ≠ 0
  seedContent_degree : seedContent.totalDegree ≤ 1899+8441
  gcdSeed_le : gcdSeed ≤ 1899
  gcdY_le : gcdY ≤ 82
  cheap_caps : RowCaps cheap (afterGcd cheapZero gcdSeed gcdY)
  layered_caps : RowCaps layered (afterGcd layeredZero gcdSeed gcdY)
  proper : ProperPair cheap layered
  ordinary_factors : ∀ f ∈ ordinary, Irreducible f ∧ 0 < f.natDegree
  ordinary_seed : ∑ f ∈ ordinary, ordinarySeedDegree f ≤ gcdSeed
  ordinary_y : ∑ f ∈ ordinary, f.natDegree ≤ gcdY
  cover : ∀ z S, jetAt P z S = 0 → jetAt Q z S = 0 →
    fixedAt G S = 0 ∨ fixedAt H S = 0 ∨ graphEval z seedContent = 0 ∨
    (jetAt cheap z S = 0 ∧ jetAt layered z S = 0) ∨ ∃ f ∈ ordinary, atMark f z S = 0
structure FiniteSections (I : Ideal Ambient) : Prop where
  seeds : Module.Finite SeedField (OverSeeds I)
  ordinate : Module.Finite SectionField (OverOrdinate I)
  mixed : Module.Finite SectionField (OverMixed I)
  jets : Module.Finite SeedField (OverJets I)
def ComponentsOn (P Q : Jet) (S : Finset (Ideal Ambient)) : Prop :=
  ∀ I ∈ S, I.IsPrime ∧ ringKrullDim (CoordinateRing I) = 2 ∧ toJet P ∈ I ∧ toJet Q ∈ I
def residualBudget (s t : Shape) : Fin 4 → ℕ :=
  ![s.B*t.J + t.B*s.J - s.J*t.J,
    s.U*t.J + t.U*s.J, s.U*t.B + t.U*s.B, s.U*t.U]
def ordinaryBudget (x y : ℕ) : Fin 4 → ℕ := ![y, x, 2*x*y, x*x]
end
end K1_14_2_2_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
namespace K1_14_2_2_2
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 K1_14_3_2 Polynomial
open scoped BigOperators Classical
private theorem split_mul {u x b a d : ℕ} (hx : x ≤ u) (ha : a ≤ b) (hd : d ≤ b) :
    (u-x)*a + x*d ≤ u*b := by
  calc
    _ ≤ (u-x)*b + x*b :=
      Nat.add_le_add (Nat.mul_le_mul_left _ ha) (Nat.mul_le_mul_left _ hd)
    _ = _ := by rw [← Nat.add_mul, Nat.sub_add_cancel hx]
theorem ledger (x y : ℕ) (hx : x ≤ 1899) (hy : y ≤ 82) (k : Fin 4) :
    residualBudget (afterGcd cheapZero x y) (afterGcd layeredZero x y) k +
      ordinaryBudget x y k ≤ budget 0 k := by
  have hj : min 40 (190-y) = 40 := min_eq_left (by omega)
  fin_cases k
  · change ((82-y)*min 40 (190-y) + (190-y)*min 18 (82-y) -
        min 18 (82-y)*min 40 (190-y)) + y ≤ 5980
    rw [hj]
    by_cases h : y ≤ 64
    · rw [min_eq_left (show 18 ≤ 82-y by omega)]
      omega
    · have hs : 82-y ≤ 18 := by omega
      rw [min_eq_right hs]
      have hm : (190-y)*(82-y) ≤ 190*18 := Nat.mul_le_mul (Nat.sub_le _ _) hs
      omega
  · change (1899-x)*min 40 (190-y) + (8441-x)*min 18 (82-y) + x ≤ 227898
    rw [hj]
    have hm := Nat.mul_le_mul_left (8441-x) (min_le_left 18 (82-y))
    omega
  · change (1899-x)*(190-y) + (8441-x)*(82-y) + 2*x*y ≤ 1052972
    have h₁ : (1899-x)*(190-y) + x*y ≤ 1899*190 :=
      split_mul hx (Nat.sub_le _ _) (by omega)
    have h₂ : (8441-x)*(82-y) + x*y ≤ 8441*82 :=
      split_mul (by omega) (Nat.sub_le _ _) hy
    calc
      _ = ((1899-x)*(190-y) + x*y) + ((8441-x)*(82-y) + x*y) := by ring
      _ ≤ 1899*190 + 8441*82 := Nat.add_le_add h₁ h₂
      _ = _ := by decide
  · change (1899-x)*(8441-x) + x*x ≤ 16029459
    calc
      _ ≤ 1899*8441 := split_mul hx (Nat.sub_le _ _) (by omega)
      _ = _ := by decide
theorem ordinary_sum (D : Finset Equation) (x y : ℕ)
    (hx : ∑ f ∈ D, ordinarySeedDegree f ≤ x) (hy : ∑ f ∈ D, f.natDegree ≤ y)
    (k : Fin 4) :
    (∑ f ∈ D, ordinaryBudget (ordinarySeedDegree f) f.natDegree k) ≤ ordinaryBudget x y k := by
  fin_cases k
  · exact hy
  · exact hx
  · change (∑ f ∈ D, 2 * ordinarySeedDegree f * f.natDegree) ≤ 2*x*y
    calc
      _ ≤ ∑ f ∈ D, 2 * ordinarySeedDegree f * y := by
        apply Finset.sum_le_sum
        intro f hf
        exact Nat.mul_le_mul_left _ ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf).trans hy)
      _ = (2 * ∑ f ∈ D, ordinarySeedDegree f) * y := by rw [Finset.mul_sum, Finset.sum_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hx)
  · change (∑ f ∈ D, ordinarySeedDegree f * ordinarySeedDegree f) ≤ x*x
    calc
      _ ≤ ∑ f ∈ D, ordinarySeedDegree f * x := by
        apply Finset.sum_le_sum
        intro f hf
        exact Nat.mul_le_mul_left _ ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf).trans hx)
      _ = (∑ f ∈ D, ordinarySeedDegree f) * x := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ hx
theorem length_le_mass {S : Finset (Ideal Ambient)} {I : Ideal Ambient} (hI : I ∈ S)
    (k : Fin 4) : sectionDegree I k ≤ mass S k :=
  Finset.single_le_sum (f := fun J => sectionDegree J k) (fun _ _ => Nat.zero_le _) hI
theorem eval_ordinate (z : K) (R : K[X]) (f : FX[X]) :
    jetMarkHom z R (ordinateIncl f) = f.eval (atX R) := by
  have hC : (jetMarkHom z R).comp MvPolynomial.C = RingHom.id FX :=
    RingHom.ext fun c => by simp [jetMarkHom]
  have hY : jetMarkHom z R (MvPolynomial.X 2) = atX R := by simp [jetMarkHom]
  change jetMarkHom z R (f.eval₂ MvPolynomial.C (MvPolynomial.X 2)) = f.eval (atX R)
  rw [Polynomial.hom_eval₂, hC, hY, Polynomial.eval₂_id]
theorem ordinate_eq {I : Ideal Ambient} (hI : I.IsPrime)
    (hn : ¬ Function.Injective ((Ideal.Quotient.mk I).comp ordinateIncl))
    {z z' : K} {R R' : K[X]} (h : OnJet I z R) (h' : OnJet I z' R') : atX R = atX R' := by
  let : I.IsPrime := hI
  let φ := (Ideal.Quotient.mk I).comp ordinateIncl
  let J := RingHom.ker φ
  have hJ : J.IsMaximal :=
    (RingHom.ker_isPrime φ).isMaximal_of_ne_bot
      (fun eq => hn ((RingHom.injective_iff_ker_eq_bot φ).mpr eq))
  have heval {w : K} {S : K[X]} (hS : OnJet I w S) :
      J ≤ RingHom.ker (evalRingHom (atX S)) := by
    intro f hf
    have hm : ordinateIncl f ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (RingHom.mem_ker.mp hf)
    exact RingHom.mem_ker.mpr ((eval_ordinate w S f).symm.trans (RingHom.mem_ker.mp (hS hm)))
  have heq := hJ.eq_of_le (RingHom.ker_ne_top _) (heval h)
  have hlin : (Polynomial.X (R := FX) - Polynomial.C (atX R)) ∈ J := by
    rw [heq]
    apply RingHom.mem_ker.mpr
    simp
  have hv := RingHom.mem_ker.mp (heval h' hlin)
  simpa [sub_eq_zero, eq_comm] using hv
theorem cover_count {u del} (M : AnchorModel u del) (T : Finset K)
    (C : K1_14_3.SeedCover) (U E : ℕ) (hU : C.curve.totalDegree ≤ U)
    (hp : U < p) (hE : C.points.card ≤ E) (hcov : ∀ γ ∈ T, C.Covers (M.label γ)) :
    T.card ≤ (p+1)*U + E :=
  (K1_14_3.seed_count (K1_14_3.label_injective M).injOn C (hU.trans_lt hp) hcov).trans
    (Nat.add_le_add (Nat.mul_le_mul_left _ hU) hE)
end
end K1_14_2_2_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
namespace K1_14_2_2_2
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 K1_14_3_2 Polynomial
open scoped BigOperators Classical
def c1 : Prop :=
  ∀ w rows (B : RowPair w rows 0) (A : FixedPair B),
    Nonempty (PreparedPair B.cheap B.layered A.cheap.equation A.layered.equation)
def c2 : Prop :=
  ∀ f : Equation, Irreducible f → 0 < f.natDegree → f.natDegree < p →
    ∃ g a, K1_14_3.IsClearing f g a ∧ ProperPair (C f) (K1_14_3.ordinaryCutter g) ∧
      ∀ z S, atMark f z S = 0 → jetAt (K1_14_3.ordinaryCutter g) z S = 0
def c3 : Prop :=
  ∀ P Q : Jet, ProperPair P Q →
    ∃ S : Finset (Ideal Ambient), ComponentsOn P Q S ∧
      ∀ z R, jetAt P z R = 0 → jetAt Q z R = 0 → ∃ I ∈ S, OnJet I z R
def c4 : Prop :=
  ∀ P Q : Jet, ProperPair P Q → ∀ s t,
    s.J ≤ s.B → t.J ≤ t.B → RowCaps P s → RowCaps Q t →
    ∀ S, ComponentsOn P Q S →
      (∀ I ∈ S, FiniteSections I) ∧ Fits S (residualBudget s t)
def c5 : Prop :=
  ∀ (f : Equation) g (a : L[X]), Irreducible f → 0 < f.natDegree → f.natDegree < p →
    K1_14_3.IsClearing f g a → ProperPair (C f) (K1_14_3.ordinaryCutter g) →
    ∀ S, ComponentsOn (C f) (K1_14_3.ordinaryCutter g) S →
      (∀ I ∈ S, FiniteSections I) ∧ Fits S (ordinaryBudget (ordinarySeedDegree f) f.natDegree)
def c6 : Prop :=
  ∀ I : Ideal Ambient, I.IsPrime → ringKrullDim (CoordinateRing I) = 2 →
    FiniteSections I → sectionDegree I 0 = 0 →
    ∃ C : K1_14_3.SeedCover, C.curve.totalDegree ≤ sectionDegree I 2 ∧
      C.points.card ≤ sectionDegree I 3 ∧ ∀ z R, OnJet I z R → C.Covers z
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) (h6 : c6) :
    K1_14_2_2.c2 := by
  classical
  intro u del M Γ F rows B A hrows
  obtain ⟨prep⟩ := h1 _ rows B A
  obtain ⟨residual, hresidual, hresCover⟩ := h3 _ _ prep.proper
  obtain ⟨hresFinite, hresCap⟩ := h4 _ _ prep.proper _ _
    (min_le_right _ _) (min_le_right _ _) prep.cheap_caps prep.layered_caps residual hresidual
  have ordinary_exists (f : Equation) (hf : f ∈ prep.ordinary) :
      ∃ S : Finset (Ideal Ambient),
        (∀ I ∈ S, I.IsPrime ∧ ringKrullDim (CoordinateRing I) = 2 ∧ FiniteSections I) ∧
        Fits S (ordinaryBudget (ordinarySeedDegree f) f.natDegree) ∧
        ∀ z R, atMark f z R = 0 → ∃ I ∈ S, OnJet I z R := by
    obtain ⟨hirr, hpos⟩ := prep.ordinary_factors f hf
    have hdeg : f.natDegree ≤ prep.gcdY :=
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf).trans prep.ordinary_y
    have hp := hdeg.trans_lt (prep.gcdY_le.trans_lt (by decide : 82 < p))
    obtain ⟨g, a, hclear, hproper, hdiff⟩ := h2 f hirr hpos hp
    obtain ⟨S, hS, hScov⟩ := h3 _ _ hproper
    obtain ⟨hfinite, hcap⟩ := h5 f g a hirr hpos hp hclear hproper S hS
    refine ⟨S, fun I hi => ⟨(hS I hi).1, (hS I hi).2.1, hfinite I hi⟩, hcap, ?_⟩
    intro z R hzero
    exact hScov z R (by simpa [jetAt, atMark] using hzero) (hdiff z R hzero)
  let ordinary (f : Equation) : Finset (Ideal Ambient) :=
    if hf : f ∈ prep.ordinary then Classical.choose (ordinary_exists f hf) else ∅
  have hord (f : Equation) (hf : f ∈ prep.ordinary) :
      (∀ I ∈ ordinary f, I.IsPrime ∧ ringKrullDim (CoordinateRing I) = 2 ∧ FiniteSections I) ∧
      Fits (ordinary f) (ordinaryBudget (ordinarySeedDegree f) f.natDegree) ∧
      ∀ z R, atMark f z R = 0 → ∃ I ∈ ordinary f, OnJet I z R := by
    simpa only [ordinary, dite_eq_left hf] using Classical.choose_spec (ordinary_exists f hf)
  let S := residual ∪ prep.ordinary.biUnion ordinary
  have hgeom (I : Ideal Ambient) (hi : I ∈ S) :
      I.IsPrime ∧ ringKrullDim (CoordinateRing I) = 2 ∧ FiniteSections I := by
    rcases Finset.mem_union.mp hi with hr | ho
    · exact ⟨(hresidual I hr).1, (hresidual I hr).2.1, hresFinite I hr⟩
    · obtain ⟨f, hf, hif⟩ := Finset.mem_biUnion.mp ho
      exact (hord f hf).1 I hif
  have hfit : Fits S (budget 0) := by
    intro k
    have hOrdCap : mass (prep.ordinary.biUnion ordinary) k ≤ ordinaryBudget prep.gcdSeed prep.gcdY k := by
      calc
        _ ≤ ∑ f ∈ prep.ordinary, mass (ordinary f) k :=
          sum_biUnion_le prep.ordinary ordinary (fun I => sectionDegree I k)
        _ ≤ ∑ f ∈ prep.ordinary, ordinaryBudget (ordinarySeedDegree f) f.natDegree k :=
          Finset.sum_le_sum fun f hf => (hord f hf).2.1 k
        _ ≤ _ := ordinary_sum _ _ _ prep.ordinary_seed prep.ordinary_y k
    exact (sum_union_le (fun I => sectionDegree I k) _ _).trans
      ((Nat.add_le_add (hresCap k) hOrdCap).trans (ledger _ _ prep.gcdSeed_le prep.gcdY_le k))
  let noSeeds := S.filter (fun I => sectionDegree I 0 = 0)
  let constY := S.filter (fun I => 0 < sectionDegree I 0 ∧
    ¬ Function.Injective ((Ideal.Quotient.mk I).comp ordinateIncl))
  let parents := S.filter (fun I => 0 < sectionDegree I 0 ∧
    Function.Injective ((Ideal.Quotient.mk I).comp ordinateIncl))
  have hparents (I : Ideal Ambient) (hi : I ∈ parents) : Active I := by
    obtain ⟨hI, ha, hy⟩ := Finset.mem_filter.mp hi
    obtain ⟨hprime, hdim, hfinite⟩ := hgeom I hI
    have hbudget (k : Fin 4) : budget 0 k < p := by fin_cases k <;> decide
    have hsmall (k : Fin 4) : sectionDegree I k < p :=
      (length_le_mass hI k).trans_lt ((hfit k).trans_lt (hbudget k))
    exact ⟨hprime, hdim, hfinite.seeds, hfinite.ordinate, hfinite.mixed, hfinite.jets,
      ⟨ha, hsmall 0⟩, hsmall 2, hsmall 3, hy⟩
  have seed_exists (I : Ideal Ambient) (hi : I ∈ noSeeds) :
      ∃ C : K1_14_3.SeedCover, C.curve.totalDegree ≤ sectionDegree I 2 ∧
        C.points.card ≤ sectionDegree I 3 ∧ ∀ z R, OnJet I z R → C.Covers z := by
    obtain ⟨hI, hz⟩ := Finset.mem_filter.mp hi
    obtain ⟨hprime, hdim, hfinite⟩ := hgeom I hI
    exact h6 I hprime hdim hfinite hz
  let seedImage (I : Ideal Ambient) : K1_14_3.SeedCover :=
    if hi : I ∈ noSeeds then Classical.choose (seed_exists I hi) else ⟨1, one_ne_zero, ∅⟩
  have hseedImage (I : Ideal Ambient) (hi : I ∈ noSeeds) :
      (seedImage I).curve.totalDegree ≤ sectionDegree I 2 ∧
      (seedImage I).points.card ≤ sectionDegree I 3 ∧
      ∀ z R, OnJet I z R → (seedImage I).Covers z := by
    simpa only [seedImage, dite_eq_left hi] using Classical.choose_spec (seed_exists I hi)
  let imageCover := K1_14_3.joinCovers noSeeds seedImage
  let seedExits := Γ.filter (fun γ => imageCover.Covers (M.label γ))
  have hseedExits : seedExits.card ≤ (p+1)*1052972+19635660 := by
    apply cover_count M _ _ _ _ _ (by decide) _ (fun γ hγ => (Finset.mem_filter.mp hγ).2)
    · calc
        _ ≤ ∑ I ∈ noSeeds, (seedImage I).curve.totalDegree := K1_14_3.joinCovers_degree _ _
        _ ≤ mass noSeeds 2 := Finset.sum_le_sum (fun I hi => (hseedImage I hi).1)
        _ ≤ mass S 2 := mass_mono (Finset.filter_subset _ _) 2
        _ ≤ _ := hfit 2
    · calc
        _ ≤ ∑ I ∈ noSeeds, (seedImage I).points.card := K1_14_3.joinCovers_points _ _
        _ ≤ mass noSeeds 3 := Finset.sum_le_sum (fun I hi => (hseedImage I hi).2.1)
        _ ≤ mass S 3 := mass_mono (Finset.filter_subset _ _) 3
        _ ≤ budget 0 3 := hfit 3
        _ ≤ _ := by decide
  let onY (I : Ideal Ambient) := Γ.filter (OnParent M F I)
  let yExits := constY.biUnion onY
  have hyExits : yExits.card ≤ 5980 := by
    calc
      _ ≤ ∑ I ∈ constY, (onY I).card := Finset.card_biUnion_le
      _ ≤ mass constY 0 := by
        apply Finset.sum_le_sum
        intro I hi
        obtain ⟨hI, ha, hy⟩ := Finset.mem_filter.mp hi
        have hcard : (onY I).card ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro γ hγ δ hδ
          obtain ⟨hg, hgon⟩ := Finset.mem_filter.mp hγ
          obtain ⟨hd, hdon⟩ := Finset.mem_filter.mp hδ
          exact F.distinct hg hd (K1_14_3.scalar_atX_injective
            (ordinate_eq (hgeom I hI).1 hy hgon hdon))
        exact hcard.trans ha
      _ ≤ mass S 0 := mass_mono (Finset.filter_subset _ _) 0
      _ ≤ _ := hfit 0
  let contentCover : K1_14_3.SeedCover := ⟨prep.seedContent, prep.seedContent_ne, ∅⟩
  let contentExits := Γ.filter (fun γ => graphEval (M.label γ) prep.seedContent = 0)
  have hcontentExits : contentExits.card ≤ (p+1)*(1899+8441) := by
    have h := cover_count M contentExits contentCover (1899+8441) 0 prep.seedContent_degree
      (by decide) (by simp [contentCover]) (fun γ hγ => Or.inl (Finset.mem_filter.mp hγ).2)
    simpa using h
  let direct := (contentExits ∪ seedExits) ∪ yExits
  have place (γ : K) (hγ : γ ∈ Γ) {I : Ideal Ambient} (hi : I ∈ S) (hon : OnParent M F I γ) :
      γ ∈ direct ∨ ∃ J ∈ parents, OnParent M F J γ := by
    by_cases ha : sectionDegree I 0 = 0
    · have hI : I ∈ noSeeds := Finset.mem_filter.mpr ⟨hi, ha⟩
      have hc : imageCover.Covers (M.label γ) := K1_14_3.joinCovers_covers hI
        ((hseedImage I hI).2.2 _ _ hon)
      exact Or.inl (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hc⟩)))
    · have hp := Nat.pos_of_ne_zero ha
      by_cases hy : Function.Injective ((Ideal.Quotient.mk I).comp ordinateIncl)
      · exact Or.inr ⟨I, Finset.mem_filter.mpr ⟨hi, hp, hy⟩, hon⟩
      · have hI : I ∈ constY := Finset.mem_filter.mpr ⟨hi, hp, hy⟩
        exact Or.inl (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨I, hI, Finset.mem_filter.mpr ⟨hγ, hon⟩⟩))
  refine ⟨⟨parents, hparents, fits_mono (Finset.filter_subset _ _) hfit, direct, ?_, ?_⟩⟩
  · calc
      direct.card ≤ (contentExits ∪ seedExits).card + yExits.card := Finset.card_union_le _ _
      _ ≤ contentExits.card + seedExits.card + yExits.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ (p+1)*(1899+8441) + ((p+1)*1052972+19635660) + 5980 :=
        Nat.add_le_add (Nat.add_le_add hcontentExits hseedExits) hyExits
      _ = initialPrice := by unfold initialPrice; ac_rfl
  · intro γ hγ
    obtain ⟨hP, hQ⟩ := hrows γ hγ
    have fromSurface (I : Ideal Ambient) (hi : I ∈ S) (hon : OnParent M F I γ) :
        γ ∈ direct ∨ fixedAt A.cheap.equation (F.scalar γ) = 0 ∨
          fixedAt A.layered.equation (F.scalar γ) = 0 ∨ ∃ J ∈ parents, OnParent M F J γ := by
      rcases place γ hγ hi hon with hd | hp
      · exact Or.inl hd
      · exact Or.inr (Or.inr (Or.inr hp))
    rcases prep.cover _ _ hP hQ with hg | hh | hc | hr | ⟨f, hf, hz⟩
    · exact Or.inr (Or.inl hg)
    · exact Or.inr (Or.inr (Or.inl hh))
    · exact Or.inl (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hc⟩)))
    · obtain ⟨I, hI, hon⟩ := hresCover _ _ hr.1 hr.2
      exact fromSurface I (Finset.mem_union_left _ hI) hon
    · obtain ⟨I, hI, hon⟩ := (hord f hf).2.2 _ _ hz
      exact fromSurface I (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨f, hf, hI⟩)) hon
end
end K1_14_2_2_2
end
section
namespace K1_14_2_2_2_5
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 Polynomial
open K1_14_3 (Slice)
abbrev SliceField : Slice → Type
  | .seed | .jets => SeedField
  | .ordinate | .mixed => SectionField
instance (s : Slice) : Field (SliceField s) := by
  cases s <;> infer_instance
abbrev Plane (F : Type) [Field F] := MvPolynomial (Fin 2) F
def lineElim (mixed : Bool) : SectionAmbient →ₐ[SectionField] Plane SectionField :=
  MvPolynomial.aeval
    ![MvPolynomial.C (sliceParameter 2) - MvPolynomial.C (sliceParameter 0) * MvPolynomial.X 0,
      MvPolynomial.X 0,
      MvPolynomial.C (sliceParameter 3) -
        MvPolynomial.C (if mixed then sliceParameter 1 else 0) * MvPolynomial.X 1,
      MvPolynomial.X 1]
def sliceEval : (s : Slice) → Ambient →+* Plane (SliceField s)
  | .seed => mapGenericSeed
  | .ordinate => (lineElim false).toRingHom.comp sectionBase
  | .mixed => (lineElim true).toRingHom.comp sectionBase
  | .jets => mapGenericJets
abbrev SliceQuotient (s : Slice) (I : Ideal Ambient) :=
  CoordinateRing (I.map (sliceEval s))
end
end K1_14_2_2_2_5
end
section
set_option autoImplicit false
namespace K1_14_2_2_2_4
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2
open K1_14_3 (Slice)
def SliceField : Slice → Type
  | .seed | .jets => SeedField
  | .ordinate | .mixed => SectionField
instance (s : Slice) : Field (SliceField s) := by
  cases s <;> unfold SliceField <;> infer_instance
def coefficients (s : Slice) : FX →+* SliceField s :=
  match s with
  | .seed | .jets => algebraMap FX SeedField
  | .ordinate | .mixed => algebraMap FX SectionField
abbrev Plane (F : Type) [Field F] := MvPolynomial (Fin 2) F
def seedCoordinates (s : Slice) : Fin 2 → Plane (SliceField s) :=
  match s with
  | .seed => fun i => MvPolynomial.C (generic i)
  | .ordinate | .mixed =>
    ![MvPolynomial.C (sliceParameter 2) - MvPolynomial.C (sliceParameter 0) * MvPolynomial.X 0,
      MvPolynomial.X 0]
  | .jets => MvPolynomial.X
def ordinateCoordinate (s : Slice) : Plane (SliceField s) :=
  match s with
  | .seed => MvPolynomial.X 0
  | .ordinate => MvPolynomial.C (sliceParameter 3)
  | .mixed => MvPolynomial.C (sliceParameter 3) - MvPolynomial.C (sliceParameter 1) * MvPolynomial.X 1
  | .jets => MvPolynomial.C (generic 0)
def derivativeCoordinate (s : Slice) : Plane (SliceField s) :=
  match s with
  | .jets => MvPolynomial.C (generic 1)
  | .seed | .ordinate | .mixed => MvPolynomial.X 1
def coordinates (s : Slice) : Fin 4 → Plane (SliceField s) :=
  ![seedCoordinates s 0, seedCoordinates s 1, ordinateCoordinate s, derivativeCoordinate s]
def planeMap (s : Slice) : Ambient →+* Plane (SliceField s) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (coefficients s)) (coordinates s)
def rowMap (s : Slice) : Jet →+* Plane (SliceField s) := (planeMap s).comp toJet
def PrimeTransport (s : Slice) : Prop :=
  ∀ I : Ideal Ambient, I.IsPrime →
    I.map (planeMap s) = ⊤ ∨
      (I.map (planeMap s)).IsPrime ∧ (I.map (planeMap s)).comap (planeMap s) = I
structure PlaneProper {F : Type} [Field F] (P Q : Plane F) : Prop where
  left_ne : P ≠ 0
  right_ne : Q ≠ 0
  no_common : ∀ D : Plane F, Irreducible D → D ∣ P → ¬ D ∣ Q
def PlaneCaps (s : Slice) (d : Shape) (P : Plane (SliceField s)) : Prop :=
  match s with
  | .seed => P.totalDegree ≤ d.B ∧ P.degreeOf 1 ≤ d.J
  | .ordinate => P.degreeOf 0 ≤ d.U ∧ P.degreeOf 1 ≤ d.J
  | .mixed => P.degreeOf 0 ≤ d.U ∧ P.degreeOf 1 ≤ d.B
  | .jets => P.totalDegree ≤ d.U
abbrev PairQuotient {F : Type} [Field F] (P Q : Plane F) :=
  Plane F ⧸ Ideal.span ({P, Q} : Set (Plane F))
def ColengthAtMost {F : Type} [Field F] (P Q : Plane F) (n : ℕ) : Prop :=
  Module.Finite F (PairQuotient P Q) ∧ Module.finrank F (PairQuotient P Q) ≤ n
end
end K1_14_2_2_2_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_2_5
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2 Polynomial
open K1_14_3 (Slice)
open scoped BigOperators
private def lineCut (mixed : Bool) : Ideal SectionAmbient :=
  Ideal.span {sectionSeedLine, if mixed then sectionJetLine else
    MvPolynomial.X 2 - MvPolynomial.C (sliceParameter 3)}
def freeIncl : Plane SectionField →ₐ[SectionField] SectionAmbient :=
  MvPolynomial.rename ![1, 3]
theorem lineElim_surjective (mixed : Bool) : Function.Surjective (lineElim mixed) := by
  have h : (lineElim mixed).comp freeIncl = AlgHom.id _ _ := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [lineElim, freeIncl]
  intro q
  exact ⟨freeIncl q, DFunLike.congr_fun h q⟩
theorem lineElim_ker (mixed : Bool) :
    RingHom.ker (lineElim mixed).toRingHom = lineCut mixed := by
  let π := Ideal.Quotient.mkₐ SectionField (lineCut mixed)
  have hconst (a : SectionField) :
      π (MvPolynomial.C a) = algebraMap SectionField (SectionAmbient ⧸ lineCut mixed) a :=
    π.commutes a
  have hseed : π sectionSeedLine = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hjet : π (if mixed then sectionJetLine else
      MvPolynomial.X 2 - MvPolynomial.C (sliceParameter 3)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have h : (π.comp freeIncl).comp (lineElim mixed) = π := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [lineElim, freeIncl]
      simp only [sectionSeedLine, map_sub, map_add, map_mul, hconst] at hseed
      linear_combination -hseed
    · simp [lineElim, freeIncl]
    · cases mixed <;> simp [lineElim, freeIncl]
      · simp only [Bool.false_eq_true, ite_false, map_sub, hconst] at hjet
        linear_combination -hjet
      · simp only [ite_true, sectionJetLine, map_sub, map_add, map_mul, hconst] at hjet
        linear_combination -hjet
    · simp [lineElim, freeIncl]
  apply le_antisymm
  · intro q hq
    have hq' : lineElim mixed q = 0 := hq
    have he := DFunLike.congr_fun h q
    simp only [AlgHom.comp_apply, hq', map_zero] at he
    exact Ideal.Quotient.eq_zero_iff_mem.mp he.symm
  · apply Ideal.span_le.mpr
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · change lineElim mixed sectionSeedLine = 0
      simp [sectionSeedLine, lineElim]
    · change lineElim mixed (if mixed then sectionJetLine else _) = 0
      cases mixed <;> simp [sectionJetLine, lineElim]
private def lineQuotientEquiv (mixed : Bool) (I : Ideal Ambient) :
    CoordinateRing (I.map sectionBase ⊔ lineCut mixed) ≃ₐ[SectionField]
      CoordinateRing (I.map ((lineElim mixed).toRingHom.comp sectionBase)) := by
  let e := lineElim mixed
  let J := I.map sectionBase
  let J' := J.map e.toRingHom
  have he : Function.Surjective e.toRingHom := lineElim_surjective mixed
  have hh : J'.comap e.toRingHom = J ⊔ lineCut mixed := by
    change (J.map e.toRingHom).comap e.toRingHom = _
    rw [Ideal.comap_map_of_surjective _ he, ← RingHom.ker_eq_comap_bot]
    exact congrArg (J ⊔ ·) (lineElim_ker mixed)
  let g := Ideal.quotientMapₐ J' e hh.ge
  have hg : Function.Bijective g := ⟨Ideal.quotientMap_injective' (H := hh.ge) hh.le,
    Ideal.quotientMap_surjective (H := hh.ge) he⟩
  change CoordinateRing (J ⊔ lineCut mixed) ≃ₐ[SectionField]
    CoordinateRing (I.map (e.toRingHom.comp sectionBase))
  rw [← Ideal.map_map]
  exact AlgEquiv.ofBijective g hg
def ordinateEquiv (I : Ideal Ambient) :
    OverOrdinate I ≃ₐ[SectionField] SliceQuotient .ordinate I :=
  lineQuotientEquiv false I
def mixedEquiv (I : Ideal Ambient) :
    OverMixed I ≃ₐ[SectionField] SliceQuotient .mixed I :=
  lineQuotientEquiv true I
end
end K1_14_2_2_2_5
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
set_option maxHeartbeats 1000000
namespace K1_14_2_2_2_4
noncomputable section
open K1 K1_14 K1_14_2 K1_14_3_2 Polynomial
open K1_14_3 (Slice)
theorem toJet_seed (A : Seeds) : toJet (C (C A)) = rootIncl (rootSeeds A) := by
  simp [toJet, toRoot]
theorem toJet_ordinate : toJet (C (Polynomial.X (R := Seeds))) = MvPolynomial.X 2 := by
  simp [toJet, toRoot, rootIncl]
theorem toJet_derivative : toJet (Polynomial.X (R := Equation)) = MvPolynomial.X 3 := by
  simp [toJet]
def fromAmbient : Ambient →+* Jet :=
  MvPolynomial.eval₂Hom (C.comp (C.comp MvPolynomial.C))
    ![C (C (MvPolynomial.X 0)), C (C (MvPolynomial.X 1)), C Polynomial.X, Polynomial.X]
theorem fromAmbient_seed :
    fromAmbient.comp (rootIncl.comp rootSeeds) =
      (C : Equation →+* Jet).comp (C : Seeds →+* Equation) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [fromAmbient, rootIncl, rootSeeds]
  · intro i
    fin_cases i <;> simp [fromAmbient, rootIncl, rootSeeds]
theorem left_inverse : fromAmbient.comp toJet = RingHom.id Jet := by
  apply Polynomial.ringHom_ext
  · intro A
    change ((fromAmbient.comp toJet).comp (C : Equation →+* Jet)) A = (C : Equation →+* Jet) A
    suffices h : (fromAmbient.comp toJet).comp (C : Equation →+* Jet) = C from
      RingHom.congr_fun h A
    apply Polynomial.ringHom_ext
    · intro B
      change fromAmbient (toJet (C (C B))) = C (C B)
      rw [toJet_seed]
      exact RingHom.congr_fun fromAmbient_seed B
    · simp [RingHom.comp_apply, toJet_ordinate, fromAmbient]
  · simp [RingHom.comp_apply, toJet_derivative, fromAmbient]
theorem right_inverse : toJet.comp fromAmbient = RingHom.id Ambient := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [fromAmbient, toJet_seed, rootIncl, rootSeeds]
  · intro i
    fin_cases i <;> simp [fromAmbient, toJet_seed, toJet_ordinate, toJet_derivative,
      rootIncl, rootSeeds]
private def jetEquiv : Jet ≃+* Ambient :=
  { toJet with
    invFun := fromAmbient
    left_inv := RingHom.congr_fun left_inverse
    right_inv := RingHom.congr_fun right_inverse }
theorem transport_injective {A T : Type} [CommRing A] [IsDomain A]
    [CommRing T] [Nontrivial T] (g : A →+* T)
    (ht : ∀ I : Ideal A, I.IsPrime →
      I.map g = ⊤ ∨ (I.map g).IsPrime ∧ (I.map g).comap g = I) :
    Function.Injective g := by
  have h := ht ⊥ Ideal.isPrime_bot
  rw [Ideal.map_bot] at h
  exact (RingHom.injective_iff_ker_eq_bot g).mpr (h.resolve_left bot_ne_top).2
theorem map_proper {R A T : Type}
    [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    [CommRing T] [IsDomain T] [UniqueFactorizationMonoid T]
    (e : R ≃+* A) (g : A →+* T)
    (ht : ∀ I : Ideal A, I.IsPrime →
      I.map g = ⊤ ∨ (I.map g).IsPrime ∧ (I.map g).comap g = I)
    (P Q : R) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hcop : ∀ a : R, Irreducible a → a ∣ P → ¬ a ∣ Q) :
    let f := g.comp e.toRingHom
    f P ≠ 0 ∧ f Q ≠ 0 ∧ ∀ D : T, Irreducible D → D ∣ f P → ¬ D ∣ f Q := by
  let f := g.comp e.toRingHom
  change f P ≠ 0 ∧ f Q ≠ 0 ∧ ∀ D : T, Irreducible D → D ∣ f P → ¬ D ∣ f Q
  have hf : Function.Injective f := (transport_injective g ht).comp e.injective
  refine ⟨(map_ne_zero_iff f hf).mpr hP, (map_ne_zero_iff f hf).mpr hQ, ?_⟩
  intro D hD hdP hdQ
  have hprime := hD.prime
  have hex : ∀ B : R, B ≠ 0 → D ∣ f B → ∃ a : R, Irreducible a ∧ a ∣ B ∧ D ∣ f a := by
    intro B
    induction B using WfDvdMonoid.induction_on_irreducible with
    | zero => simp
    | unit B hB =>
      intro _ h
      exact (hD.not_isUnit (isUnit_of_dvd_unit h (hB.map f))).elim
    | mul B a hB ha ih =>
      intro _ h
      rw [map_mul] at h
      rcases hprime.dvd_mul.mp h with h | h
      · exact ⟨a, ha, dvd_mul_right a B, h⟩
      · obtain ⟨b, hb, hba, hbd⟩ := ih hB h
        exact ⟨b, hb, hba.trans ⟨a, mul_comm a B⟩, hbd⟩
  obtain ⟨a, ha, haP, hDa⟩ := hex P hP hdP
  have ha' : Irreducible (e a) := ha.map e.toMulEquiv
  let I : Ideal A := Ideal.span {e a}
  have hI : I.IsPrime := Ideal.isPrime_span_singleton_of_prime ha'.prime
  have hspan : I.map g = Ideal.span {f a} := by
    change (Ideal.span {e a}).map g = _
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have hnt : I.map g ≠ ⊤ := by
    rw [hspan]
    exact fun h => hD.not_isUnit (isUnit_of_dvd_unit hDa (Ideal.span_singleton_eq_top.mp h))
  have htrans := (ht I hI).resolve_left hnt
  have hJ : (Ideal.span {f a}).IsPrime := hspan ▸ htrans.1
  have hfa : f a ≠ 0 := (map_ne_zero_iff f hf).mpr ha.ne_zero
  have haf : Prime (f a) := (Ideal.span_singleton_prime hfa).mp hJ
  have had : f a ∣ D := (hD.associated_of_dvd haf.irreducible hDa).dvd'
  have hQmem : e Q ∈ I := by
    rw [← htrans.2]
    change f Q ∈ I.map g
    rw [hspan, Ideal.mem_span_singleton]
    exact had.trans hdQ
  have hdiv : e a ∣ e Q := Ideal.mem_span_singleton.mp hQmem
  exact hcop a ha haP ((map_dvd_iff e).mp hdiv)
theorem rowMap_proper (s : Slice) (ht : PrimeTransport s) (P Q : Jet)
    (hp : ProperPair P Q) : PlaneProper (rowMap s P) (rowMap s Q) := by
  let : CommRing Equation := @Polynomial.commRing Seeds inferInstance
  let : CommRing Jet := @Polynomial.commRing Equation inferInstance
  let : UniqueFactorizationMonoid FX := PrincipalIdealRing.to_uniqueFactorizationMonoid
  let : UniqueFactorizationMonoid Ambient := MvPolynomial.uniqueFactorizationMonoid (Fin 4)
  let : UniqueFactorizationMonoid Seeds := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  let : UniqueFactorizationMonoid (Plane (SliceField s)) :=
    MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  obtain ⟨hP, hQ, hcop⟩ :=
    map_proper jetEquiv (planeMap s) ht P Q hp.left_ne hp.right_ne hp.no_common
  exact ⟨hP, hQ, hcop⟩
end
end K1_14_2_2_2_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace K1_14_2_2_2_4
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 Polynomial
open K1_14_3 (Slice)
open scoped BigOperators
abbrev baseMap (s : Slice) :=
  (MvPolynomial.C : SliceField s →+* Plane (SliceField s)).comp (coefficients s)
private theorem eval_seed (s : Slice) (A : Seeds) :
    rowMap s (C (C A)) = MvPolynomial.eval₂Hom (baseMap s) (seedCoordinates s) A := by
  have h : (planeMap s).comp (rootIncl.comp rootSeeds) =
      MvPolynomial.eval₂Hom (baseMap s) (seedCoordinates s) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rootSeeds, rootIncl, planeMap, MvPolynomial.eval₂Hom_C]
    · intro i
      fin_cases i <;> simp [rootSeeds, rootIncl, planeMap, coordinates, MvPolynomial.eval₂Hom_X']
  change planeMap s (toJet (C (C A))) = _
  rw [toJet_seed]
  exact RingHom.congr_fun h A
theorem eval_y (s : Slice) :
    rowMap s (C (Polynomial.X (R := Seeds))) = ordinateCoordinate s := by
  simp [rowMap, toJet_ordinate, planeMap, coordinates]
theorem eval_v (s : Slice) :
    rowMap s (Polynomial.X (R := Equation)) = derivativeCoordinate s := by
  simp [rowMap, toJet_derivative, planeMap, coordinates]
theorem sum_degree_le {F ι : Type} [Field F] (D : Plane F → ℕ)
    (h0 : D 0 = 0) (hadd : ∀ f g, D (f + g) ≤ max (D f) (D g))
    (T : Finset ι) (a : ι → Plane F) (N : ℕ) (h : ∀ i ∈ T, D (a i) ≤ N) :
    D (∑ i ∈ T, a i) ≤ N := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [h0]
  | @insert i T hi ih =>
    rw [Finset.sum_insert hi]
    exact (hadd _ _).trans (max_le (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj))))
private theorem degree_bound (s : Slice) (P : Jet) (d : Shape) (h : RowCaps P d)
    (D : Plane (SliceField s) → ℕ) (h0 : D 0 = 0) (h1 : D 1 = 0)
    (hadd : ∀ f g, D (f + g) ≤ max (D f) (D g))
    (hmul : ∀ f g, D (f * g) ≤ D f + D g)
    (hpow : ∀ f n, D (f ^ n) ≤ n * D f)
    (hconst : ∀ a : SliceField s, D (MvPolynomial.C a) = 0)
    (u e j N : ℕ)
    (hu : ∀ i, D (seedCoordinates s i) ≤ u)
    (he : D (ordinateCoordinate s) ≤ e) (hj : D (derivativeCoordinate s) ≤ j)
    (hN : ∀ v y, y + v ≤ d.B → v ≤ d.J → d.U * u + y * e + v * j ≤ N) :
    D (rowMap s P) ≤ N := by
  classical
  have hseed (A : Seeds) : D (rowMap s (C (C A))) ≤ A.totalDegree * u := by
    rw [eval_seed]
    conv_lhs => rw [A.as_sum]
    rw [map_sum]
    apply sum_degree_le D h0 hadd
    intro m hm
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial]
    apply (hmul _ _).trans
    rw [show baseMap s (A.coeff m) =
      MvPolynomial.C (coefficients s (A.coeff m)) from rfl, hconst, zero_add]
    unfold Finsupp.prod
    refine (m.support.apply_prod_le_sum_apply D (by rw [h1]) hmul).trans ?_
    calc
      _ ≤ ∑ i ∈ m.support, m i * u :=
        Finset.sum_le_sum fun i _ => (hpow _ _).trans (Nat.mul_le_mul_left _ (hu i))
      _ = m.degree * u := by rw [← Finset.sum_mul, Finsupp.degree_apply]
      _ ≤ _ := Nat.mul_le_mul_right u (MvPolynomial.le_totalDegree hm)
  conv_lhs => rw [P.as_sum_support_C_mul_X_pow]
  rw [map_sum]
  apply sum_degree_le D h0 hadd
  intro v hv
  rw [map_mul, map_pow, eval_v]
  refine (hmul _ _).trans ?_
  have hv' := (hpow (derivativeCoordinate s) v).trans (Nat.mul_le_mul_left v hj)
  have hc : D (rowMap s (C (P.coeff v))) ≤ N - v * j := by
    conv_lhs => rw [(P.coeff v).as_sum_support_C_mul_X_pow]
    rw [map_sum, map_sum]
    apply sum_degree_le D h0 hadd
    intro y hy
    rw [map_mul, map_mul, map_pow, map_pow, eval_y]
    have hrow := h v y (mem_support_iff.mp hy)
    have hs := (hseed ((P.coeff v).coeff y)).trans (Nat.mul_le_mul_right u hrow.2.2)
    have ht := (hpow (ordinateCoordinate s) y).trans (Nat.mul_le_mul_left y he)
    have hn := hN v y hrow.1 hrow.2.1
    exact (hmul _ _).trans (by omega)
  obtain ⟨y, hy⟩ := support_nonempty.mpr (mem_support_iff.mp hv)
  have hrow := h v y (mem_support_iff.mp hy)
  have hn := hN v y hrow.1 hrow.2.1
  omega
theorem totalDegree_bound (s : Slice) (P : Jet) (d : Shape) (h : RowCaps P d)
    (u e j N : ℕ)
    (hu : ∀ i, (seedCoordinates s i).totalDegree ≤ u)
    (he : (ordinateCoordinate s).totalDegree ≤ e) (hj : (derivativeCoordinate s).totalDegree ≤ j)
    (hN : ∀ v y, y + v ≤ d.B → v ≤ d.J → d.U * u + y * e + v * j ≤ N) :
    (rowMap s P).totalDegree ≤ N :=
  degree_bound s P d h MvPolynomial.totalDegree MvPolynomial.totalDegree_zero
    MvPolynomial.totalDegree_one MvPolynomial.totalDegree_add MvPolynomial.totalDegree_mul
    MvPolynomial.totalDegree_pow MvPolynomial.totalDegree_C u e j N hu he hj hN
theorem degreeOf_bound (i : Fin 2) (s : Slice) (P : Jet) (d : Shape) (h : RowCaps P d)
    (u e j N : ℕ)
    (hu : ∀ a, (seedCoordinates s a).degreeOf i ≤ u)
    (he : (ordinateCoordinate s).degreeOf i ≤ e) (hj : (derivativeCoordinate s).degreeOf i ≤ j)
    (hN : ∀ v y, y + v ≤ d.B → v ≤ d.J → d.U * u + y * e + v * j ≤ N) :
    (rowMap s P).degreeOf i ≤ N :=
  degree_bound s P d h (MvPolynomial.degreeOf i) (MvPolynomial.degreeOf_zero i)
    (MvPolynomial.degreeOf_one i) (MvPolynomial.degreeOf_add_le i) (MvPolynomial.degreeOf_mul_le i)
    (MvPolynomial.degreeOf_pow_le i) (fun a => MvPolynomial.degreeOf_C a i) u e j N hu he hj hN
theorem seed_line_total :
    (MvPolynomial.C (sliceParameter 2) -
      MvPolynomial.C (sliceParameter 0) * MvPolynomial.X (0 : Fin 2)).totalDegree ≤ 1 :=
  (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp)
    ((MvPolynomial.totalDegree_mul _ _).trans (by simp)))
theorem ordinate_line_degree :
    (MvPolynomial.C (sliceParameter 3) -
      MvPolynomial.C (sliceParameter 1) * MvPolynomial.X (1 : Fin 2)).totalDegree ≤ 1 :=
  (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp)
    ((MvPolynomial.totalDegree_mul _ _).trans (by simp)))
theorem rowMap_caps (s : Slice) (P : Jet) (d : Shape) (h : RowCaps P d) :
    PlaneCaps s d (rowMap s P) := by
  classical
  have seed_deg0 : ∀ i, (seedCoordinates .ordinate i).degreeOf 0 ≤ 1 := by
    rw [Fin.forall_fin_two]
    constructor
    · apply (MvPolynomial.degreeOf_le_totalDegree _ _).trans
      simpa only [seedCoordinates, Matrix.cons_val_zero] using seed_line_total
    · simp [seedCoordinates]
  have seed_deg1 : ∀ i, (seedCoordinates .ordinate i).degreeOf 1 ≤ 0 := by
    rw [Fin.forall_fin_two]
    constructor
    · change (MvPolynomial.C (sliceParameter 2) -
          MvPolynomial.C (sliceParameter 0) * MvPolynomial.X (0 : Fin 2)).degreeOf 1 ≤ 0
      apply (MvPolynomial.degreeOf_sub_le _ _ _).trans
      apply max_le
      · simp
      · exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (by simp [MvPolynomial.degreeOf_X])
    · simp [seedCoordinates, MvPolynomial.degreeOf_X]
  have ordinate_deg0 : (ordinateCoordinate .mixed).degreeOf 0 ≤ 0 := by
    change (MvPolynomial.C (sliceParameter 3) -
      MvPolynomial.C (sliceParameter 1) * MvPolynomial.X (1 : Fin 2)).degreeOf 0 ≤ 0
    apply (MvPolynomial.degreeOf_sub_le _ _ _).trans
    apply max_le
    · simp
    · exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (by simp [MvPolynomial.degreeOf_X])
  cases s
  · refine ⟨totalDegree_bound .seed P d h 0 1 1 d.B ?_ (by simp [ordinateCoordinate])
        (by simp [derivativeCoordinate]) (by intro v y hB hJ; omega),
      degreeOf_bound 1 .seed P d h 0 0 1 d.J ?_
        (by simp [ordinateCoordinate, MvPolynomial.degreeOf_X])
        (by simp [derivativeCoordinate]) (by intro v y hB hJ; omega)⟩
    all_goals intro i; fin_cases i <;> simp [seedCoordinates]
  · exact ⟨degreeOf_bound 0 .ordinate P d h 1 0 0 d.U seed_deg0
        (by simp [ordinateCoordinate]) (by simp [derivativeCoordinate, MvPolynomial.degreeOf_X])
        (by intro v y hB hJ; omega),
      degreeOf_bound 1 .ordinate P d h 0 0 1 d.J seed_deg1
        (by simp [ordinateCoordinate]) (by simp [derivativeCoordinate]) (by intro v y hB hJ; omega)⟩
  · exact ⟨degreeOf_bound 0 .mixed P d h 1 0 0 d.U seed_deg0 ordinate_deg0
        (by simp [derivativeCoordinate, MvPolynomial.degreeOf_X]) (by intro v y hB hJ; omega),
      degreeOf_bound 1 .mixed P d h 0 1 1 d.B seed_deg1
        ((MvPolynomial.degreeOf_le_totalDegree _ _).trans
          (by simpa only [ordinateCoordinate] using ordinate_line_degree))
        (by simp [derivativeCoordinate]) (by intro v y hB hJ; omega)⟩
  · exact totalDegree_bound .jets P d h 1 0 0 d.U (by simp [seedCoordinates])
      (by simp [ordinateCoordinate]) (by simp [derivativeCoordinate]) (by intro v y hB hJ; omega)
end
end K1_14_2_2_2_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace K1_14_2_2_2_4
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2
section LinearCuts
variable {k : Type} [CommRing k]
private abbrev Four (F : Type) [CommSemiring F] := MvPolynomial (Fin 4) F
def cutValues (a b u v : k) : Fin 4 → MvPolynomial (Fin 2) k :=
  ![MvPolynomial.C u - MvPolynomial.C a * MvPolynomial.X 0, MvPolynomial.X 0,
    MvPolynomial.C v - MvPolynomial.C b * MvPolynomial.X 1, MvPolynomial.X 1]
def cutMap (a b u v : k) : Four k →ₐ[k] MvPolynomial (Fin 2) k :=
  MvPolynomial.aeval (cutValues a b u v)
private def seedEquation (a u : k) : Four k :=
  MvPolynomial.X (0 : Fin 4) + MvPolynomial.C a * MvPolynomial.X 1 - MvPolynomial.C u
private def jetEquation (b v : k) : Four k :=
  MvPolynomial.X (2 : Fin 4) + MvPolynomial.C b * MvPolynomial.X 3 - MvPolynomial.C v
private def lineIdeal (a b u v : k) : Ideal (Four k) :=
  Ideal.span {seedEquation a u, jetEquation b v}
theorem cut_surjective (a b u v : k) : Function.Surjective (cutMap a b u v) := by
  let restore : MvPolynomial (Fin 2) k →ₐ[k] Four k := MvPolynomial.aeval ![MvPolynomial.X 1, MvPolynomial.X 3]
  have h : (cutMap a b u v).comp restore = AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [cutMap, cutValues, restore]
  intro f
  exact ⟨restore f, AlgHom.congr_fun h f⟩
theorem cut_ker (a b u v : k) :
    RingHom.ker (cutMap a b u v).toRingHom = lineIdeal a b u v := by
  let q := Ideal.Quotient.mkₐ k (lineIdeal a b u v)
  let restore : MvPolynomial (Fin 2) k →ₐ[k] (Four k ⧸ lineIdeal a b u v) :=
    MvPolynomial.aeval ![q (MvPolynomial.X 1), q (MvPolynomial.X 3)]
  have hs : q (seedEquation a u) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))
  have hj : q (jetEquation b v) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have h : restore.comp (cutMap a b u v) = q := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, cutMap, MvPolynomial.aeval_X]
    fin_cases i
    · rw [show cutValues a b u v (⟨0, by decide⟩ : Fin 4) =
        MvPolynomial.C u - MvPolynomial.C a * MvPolynomial.X 0 from rfl]
      simp only [map_sub, map_mul, restore, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
        Matrix.cons_val_zero]
      apply sub_eq_iff_eq_add.mpr
      symm
      apply sub_eq_zero.mp
      change q (MvPolynomial.X (0 : Fin 4)) + _ - _ = 0
      simpa only [seedEquation, map_sub, map_add, map_mul, ← MvPolynomial.algebraMap_eq,
        AlgHom.commutes] using hs
    · rw [show cutValues a b u v (⟨1, by decide⟩ : Fin 4) = MvPolynomial.X 0 from rfl]
      simp [restore]
    · rw [show cutValues a b u v (⟨2, by decide⟩ : Fin 4) =
        MvPolynomial.C v - MvPolynomial.C b * MvPolynomial.X 1 from rfl]
      simp only [map_sub, map_mul, restore, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
        Matrix.cons_val_one, Matrix.cons_val_zero]
      apply sub_eq_iff_eq_add.mpr
      symm
      apply sub_eq_zero.mp
      change q (MvPolynomial.X (2 : Fin 4)) + _ - _ = 0
      simpa only [jetEquation, map_sub, map_add, map_mul, ← MvPolynomial.algebraMap_eq,
        AlgHom.commutes] using hj
    · rw [show cutValues a b u v (⟨3, by decide⟩ : Fin 4) = MvPolynomial.X 1 from rfl]
      simp [restore]
  apply le_antisymm
  · intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hx' := AlgHom.congr_fun h x
    have hx0 : cutMap a b u v x = 0 := RingHom.mem_ker.mp hx
    rw [AlgHom.comp_apply, hx0, map_zero] at hx'
    exact hx'.symm
  · apply Ideal.span_le.mpr
    intro x hx
    apply RingHom.mem_ker.mpr
    rcases (Set.mem_insert_iff.mp hx) with rfl | hx
    · simp [cutMap, cutValues, seedEquation, ← MvPolynomial.algebraMap_eq]
    · obtain rfl := Set.mem_singleton_iff.mp hx
      simp [cutMap, cutValues, jetEquation, ← MvPolynomial.algebraMap_eq]
private def cutEquiv {F : Type} [CommRing F] (g : F →+* k)
    (I : Ideal (MvPolynomial (Fin 4) F)) (a b u v : k) :
    (Four k ⧸ (I.map (MvPolynomial.map g) ⊔ lineIdeal a b u v)) ≃ₐ[k]
      (MvPolynomial (Fin 2) k ⧸ I.map ((cutMap a b u v).toRingHom.comp (MvPolynomial.map g))) := by
  let cut := cutMap a b u v
  let J := I.map (cut.toRingHom.comp (MvPolynomial.map g))
  have h : I.map (MvPolynomial.map g) ⊔ lineIdeal a b u v = J.comap cut.toRingHom := by
    unfold J
    rw [← Ideal.map_map, Ideal.comap_map_of_surjective cut.toRingHom (cut_surjective a b u v)]
    exact congrArg (I.map (MvPolynomial.map g) ⊔ ·) (cut_ker a b u v).symm
  let f := Ideal.quotientMapₐ J cut h.le
  exact AlgEquiv.ofBijective f
    ⟨Ideal.quotientMap_injective' (H := h.le) h.ge,
      Ideal.quotientMap_surjective (H := h.le) (cut_surjective a b u v)⟩
theorem cut_on_map {F : Type} [CommRing F] (g : F →+* k) (a b u v : k) :
    (cutMap a b u v).toRingHom.comp (MvPolynomial.map g) =
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp g) (cutValues a b u v) := by
  apply RingHom.ext
  intro p
  change MvPolynomial.aeval (cutValues a b u v) (MvPolynomial.map g p) = _
  rw [MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.eval₂Hom_map_hom, MvPolynomial.algebraMap_eq]
end LinearCuts
def ordinateEquiv (I : Ideal Ambient) :
    OverOrdinate I ≃ₐ[SectionField] (Plane SectionField ⧸ I.map (planeMap .ordinate)) := by
  have hcoords : cutValues (sliceParameter 0) (0 : SectionField)
      (sliceParameter 2) (sliceParameter 3) = coordinates .ordinate := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · change MvPolynomial.C (sliceParameter 3) -
        MvPolynomial.C (0 : SectionField) * MvPolynomial.X (1 : Fin 2) =
          MvPolynomial.C (sliceParameter 3)
      simp
    · rfl
  have hmap : (cutMap (sliceParameter 0) 0 (sliceParameter 2) (sliceParameter 3)).toRingHom.comp
      (MvPolynomial.map (algebraMap FX SectionField)) = planeMap .ordinate := by
    rw [cut_on_map, hcoords]
    rfl
  rw [← hmap]
  have hline : jetEquation (0 : SectionField) (sliceParameter 3) =
      MvPolynomial.X (2 : Fin 4) - MvPolynomial.C (sliceParameter 3) := by
    simp [jetEquation, MvPolynomial.C_0]
  have hsrc : I.map sectionBase ⊔ Ideal.span
      {sectionSeedLine, MvPolynomial.X 2 - MvPolynomial.C (sliceParameter 3)} =
      I.map (MvPolynomial.map (algebraMap FX SectionField)) ⊔
        lineIdeal (sliceParameter 0) 0 (sliceParameter 2) (sliceParameter 3) := by
    unfold lineIdeal
    rw [hline]
    rfl
  exact (Ideal.quotientEquivAlgOfEq SectionField hsrc).trans
    (cutEquiv (algebraMap FX SectionField) I (sliceParameter 0) 0 (sliceParameter 2)
      (sliceParameter 3))
def mixedEquiv (I : Ideal Ambient) :
    OverMixed I ≃ₐ[SectionField] (Plane SectionField ⧸ I.map (planeMap .mixed)) := by
  have hcoords : cutValues (sliceParameter 0) (sliceParameter 1)
      (sliceParameter 2) (sliceParameter 3) = coordinates .mixed := by
    funext i
    fin_cases i <;> rfl
  have hmap : (cutMap (sliceParameter 0) (sliceParameter 1) (sliceParameter 2)
      (sliceParameter 3)).toRingHom.comp (MvPolynomial.map (algebraMap FX SectionField)) =
      planeMap .mixed := by
    rw [cut_on_map, hcoords]
    rfl
  rw [← hmap]
  exact cutEquiv (algebraMap FX SectionField) I (sliceParameter 0) (sliceParameter 1)
    (sliceParameter 2) (sliceParameter 3)
end
end K1_14_2_2_2_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace K1_14_2_2_2_4
noncomputable section
open K1_14 K1_14_2 K1_14_2_2_2
open K1_14_3 (Slice)
open scoped BigOperators
theorem sum_quotient_le {k R ι : Type} [Field k] [CommRing R] [Algebra k R]
    (L : Ideal R) (J : ι → Ideal R) (qs : Finset ι) [Module.Finite k (R ⧸ L)]
    (hcont : ∀ q ∈ qs, L ≤ J q)
    (hprime : ∀ q ∈ qs, J q = ⊤ ∨ (J q).IsPrime)
    (hdisjoint : ∀ q ∈ qs, ∀ r ∈ qs, J q ≠ ⊤ → J r ≠ ⊤ → J q = J r → q = r) :
    (∑ q ∈ qs, Module.finrank k (R ⧸ J q)) ≤ Module.finrank k (R ⧸ L) := by
  classical
  let T := qs.filter fun q => J q ≠ ⊤
  let J' : T → Ideal R := fun q => J q
  have hT (q : T) : (q : ι) ∈ qs := (Finset.mem_filter.mp q.property).1
  have hne (q : T) : J q ≠ ⊤ := (Finset.mem_filter.mp q.property).2
  have hle (q : T) : L ≤ J q := hcont q (hT q)
  let (q : T) : Module.Finite k (R ⧸ J' q) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ k (hle q)).toLinearMap
      (Ideal.Quotient.factor_surjective (hle q))
  have hJM (q : T) : (J q).IsMaximal := by
    let : (J' q).IsPrime := (hprime q (hT q)).resolve_left (hne q)
    let : IsArtinianRing (R ⧸ J' q) := IsArtinianRing.of_finite k _
    exact Ideal.Quotient.maximal_of_isField (J' q) (IsArtinianRing.isField_of_isDomain _)
  have hcop : Pairwise fun q r => IsCoprime (J' q) (J' r) := by
    intro q r hqr
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply (hJM q).coprime_of_ne
    · exact hJM r
    · exact fun h => hqr (Subtype.ext (hdisjoint q (hT q) r (hT r) (hne q) (hne r) h))
  let f : R ⧸ L →ₗ[k] ∀ q : T, R ⧸ J' q :=
    LinearMap.pi fun q => (Ideal.Quotient.factorₐ k (hle q)).toLinearMap
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨y, hy⟩ := Ideal.quotientInfToPiQuotient_surj hcop x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨Ideal.Quotient.mk L a, ?_⟩
    funext q
    exact congrFun hy q
  have hd := LinearMap.finrank_le_finrank_of_surjective hsurj
  rw [Module.finrank_pi_fintype] at hd
  change (∑ q : T, Module.finrank k (R ⧸ J q)) ≤ _ at hd
  rw [Finset.sum_coe_sort T (fun q => Module.finrank k (R ⧸ J q))] at hd
  change (∑ q ∈ qs.filter (fun q => J q ≠ ⊤), Module.finrank k (R ⧸ J q)) ≤ _ at hd
  rw [Finset.sum_filter] at hd
  convert hd using 1
  symm
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : J q = ⊤
  · let : Subsingleton (R ⧸ J q) := Ideal.Quotient.subsingleton_iff.mpr h
    have hzero : Module.finrank k (R ⧸ J q) = 0 := Module.finrank_eq_zero_of_subsingleton k _
    simp only [hzero, ite_self]
  · simp [h]
abbrev ComponentQuotient (s : Slice) (I : Ideal Ambient) :=
  Plane (SliceField s) ⧸ I.map (planeMap s)
abbrev ComponentFinite (s : Slice) (I : Ideal Ambient) :=
  Module.Finite (SliceField s) (ComponentQuotient s I)
def componentLength (s : Slice) (I : Ideal Ambient) : ℕ :=
  Module.finrank (SliceField s) (ComponentQuotient s I)
theorem plane_lengths (s : Slice) (P Q : Jet) (S : Finset (Ideal Ambient))
    (hS : ComponentsOn P Q S) (ht : PrimeTransport s) (n : ℕ)
    (hB : ColengthAtMost (rowMap s P) (rowMap s Q) n) :
    (∀ I ∈ S, ComponentFinite s I) ∧ (∑ I ∈ S, componentLength s I) ≤ n := by
  let L := Ideal.span ({rowMap s P, rowMap s Q} : Set (Plane (SliceField s)))
  let J (I : Ideal Ambient) := I.map (planeMap s)
  let : Module.Finite (SliceField s) (Plane (SliceField s) ⧸ L) := hB.1
  have hcont (I : Ideal Ambient) (hi : I ∈ S) : L ≤ J I := by
    change Ideal.span ({rowMap s P, rowMap s Q} : Set (Plane (SliceField s))) ≤ J I
    rw [Ideal.span_insert, sup_le_iff]
    exact ⟨(Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem _ (hS I hi).2.2.1),
      (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem _ (hS I hi).2.2.2)⟩
  refine ⟨fun I hi => Module.Finite.of_surjective
    (Ideal.Quotient.factorₐ (SliceField s) (hcont I hi)).toLinearMap
    (Ideal.Quotient.factor_surjective (hcont I hi)), ?_⟩
  refine (sum_quotient_le L J S hcont (fun I hi => (ht I (hS I hi).1).imp_right And.left) ?_)
    |>.trans hB.2
  intro I hi I' hi' hn hn' heq
  rw [← ((ht I (hS I hi).1).resolve_left hn).2,
    ← ((ht I' (hS I' hi').1).resolve_left hn').2, show I.map (planeMap s) = I'.map (planeMap s) from heq]
end
end K1_14_2_2_2_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_2_4
noncomputable section
open K1 K1_14 K1_14_2
theorem seed_planeMap : planeMap .seed = mapGenericSeed := rfl
theorem jets_planeMap : planeMap .jets = mapGenericJets := rfl
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev Iterated := MvPolynomial (Fin 2) Seeds
private def chart (e : Fin 4 ≃ Fin 2 ⊕ Fin 2) : Ambient ≃+* Iterated :=
  ((MvPolynomial.renameEquiv FX e).trans
    (MvPolynomial.sumAlgEquiv FX (Fin 2) (Fin 2))).toRingEquiv
theorem chart_map (e : Fin 4 ≃ Fin 2 ⊕ Fin 2) :
    (algebraMap Iterated FibreRing).comp (chart e).toRingHom =
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap FX SeedField))
        (Sum.elim MvPolynomial.X (fun i => MvPolynomial.C (generic i)) ∘ e) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [chart]
    rfl
  · intro i
    rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', Function.comp_apply]
    change algebraMap Iterated FibreRing
      (MvPolynomial.sumAlgEquiv FX (Fin 2) (Fin 2)
        (MvPolynomial.renameEquiv FX e (MvPolynomial.X i))) = _
    rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, MvPolynomial.algebraMap_def]
    cases e i <;> simp [generic]
theorem localize_plane (e : Fin 4 ≃ Fin 2 ⊕ Fin 2)
    (I : Ideal Ambient) (hI : I.IsPrime) :
    let f := (algebraMap Iterated FibreRing).comp (chart e).toRingHom
    I.map f = ⊤ ∨ (I.map f).IsPrime ∧ (I.map f).comap f = I := by
  dsimp only
  let S : Submonoid Iterated := (nonZeroDivisors Seeds).map MvPolynomial.C
  let J := I.map (chart e).toRingHom
  rw [← Ideal.map_map]
  by_cases ht : J.map (algebraMap Iterated FibreRing) = ⊤
  · exact Or.inl ht
  have hJ : J.IsPrime := by
    change (I.map (chart e : Ambient →+* Iterated)).IsPrime
    rw [Ideal.map_comap_of_equiv (chart e)]
    exact hI.comap _
  have hd := (IsLocalization.map_algebraMap_ne_top_iff_disjoint S FibreRing J).mp ht
  refine Or.inr ⟨IsLocalization.isPrime_of_isPrime_disjoint S FibreRing J hJ hd, ?_⟩
  rw [← Ideal.comap_comap]
  have hcontract : (J.map (algebraMap Iterated FibreRing)).comap (algebraMap Iterated FibreRing) = J :=
    IsLocalization.under_map_of_isPrime_disjoint S FibreRing hJ hd
  change ((J.map (algebraMap Iterated FibreRing)).comap (algebraMap Iterated FibreRing)).comap
    (chart e).toRingHom = I
  rw [hcontract]
  exact Ideal.comap_map_of_bijective _ (chart e).bijective
theorem seed_transport : PrimeTransport .seed := by
  intro I hI
  rw [seed_planeMap]
  let e : Fin 4 ≃ Fin 2 ⊕ Fin 2 := (finSumFinEquiv (m := 2) (n := 2)).symm.trans (Equiv.sumComm (Fin 2) (Fin 2))
  have h : (algebraMap Iterated FibreRing).comp (chart e).toRingHom = mapGenericSeed := by
    rw [chart_map]
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [mapGenericSeed]
    · intro i
      simp only [mapGenericSeed, MvPolynomial.eval₂Hom_X', Function.comp_apply]
      fin_cases i <;> rfl
  exact h ▸ localize_plane e I hI
theorem jets_transport : PrimeTransport .jets := by
  intro I hI
  rw [jets_planeMap]
  let e : Fin 4 ≃ Fin 2 ⊕ Fin 2 := (finSumFinEquiv (m := 2) (n := 2)).symm
  have h : (algebraMap Iterated FibreRing).comp (chart e).toRingHom = mapGenericJets := by
    rw [chart_map]
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [mapGenericJets]
    · intro i
      simp only [mapGenericJets, MvPolynomial.eval₂Hom_X', Function.comp_apply]
      fin_cases i <;> rfl
  exact h ▸ localize_plane e I hI
end
end K1_14_2_2_2_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace K1_14_2_2_2_4
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2
open K1_14_3 (Slice)
open scoped BigOperators
def c1 : Prop := PrimeTransport .ordinate ∧ PrimeTransport .mixed
def c2 : Prop :=
  ∀ (F : Type) [Field F] (P Q : Plane F) (b j c k : ℕ),
    j ≤ b → k ≤ c → PlaneProper P Q →
    P.totalDegree ≤ b → P.degreeOf 1 ≤ j → Q.totalDegree ≤ c → Q.degreeOf 1 ≤ k →
    ColengthAtMost P Q (b*k + c*j - j*k)
def c3 : Prop :=
  ∀ (F : Type) [Field F] (P Q : Plane F) (u j v k : ℕ),
    PlaneProper P Q →
    P.degreeOf 0 ≤ u → P.degreeOf 1 ≤ j → Q.degreeOf 0 ≤ v → Q.degreeOf 1 ≤ k →
    ColengthAtMost P Q (u*k + v*j)
theorem quotient_properties {F : Type} [CommRing F]
    (I : Ideal (MvPolynomial (Fin 4) F)) (J : Ideal (MvPolynomial (Fin 2) F))
    (e : (MvPolynomial (Fin 4) F ⧸ I) ≃ₐ[F] (MvPolynomial (Fin 2) F ⧸ J)) :
    (Module.Finite F (MvPolynomial (Fin 2) F ⧸ J) →
      Module.Finite F (MvPolynomial (Fin 4) F ⧸ I)) ∧
    Module.finrank F (MvPolynomial (Fin 4) F ⧸ I) =
      Module.finrank F (MvPolynomial (Fin 2) F ⧸ J) := by
  refine ⟨?_, e.toLinearEquiv.finrank_eq⟩
  intro h
  let : Module.Finite F (MvPolynomial (Fin 2) F ⧸ J) := h
  exact Module.Finite.of_surjective e.symm.toLinearEquiv.toLinearMap e.symm.surjective
theorem seed_rank (I : Ideal Ambient) :
    Module.finrank SeedField (OverSeeds I) = componentLength .seed I := rfl
theorem ordinate_rank (I : Ideal Ambient) :
    Module.finrank SectionField (OverOrdinate I) = componentLength .ordinate I := by
  have h := (quotient_properties (F := SectionField) _ _ (ordinateEquiv I)).2
  exact h
theorem mixed_rank (I : Ideal Ambient) :
    Module.finrank SectionField (OverMixed I) = componentLength .mixed I := by
  have h := (quotient_properties (F := SectionField) _ _ (mixedEquiv I)).2
  exact h
theorem jets_rank (I : Ideal Ambient) :
    Module.finrank SeedField (OverJets I) = componentLength .jets I := rfl
private theorem ordinate_finite (I : Ideal Ambient) (h : ComponentFinite .ordinate I) :
    Module.Finite SectionField (OverOrdinate I) := by
  have hf := (quotient_properties (F := SectionField) _ _ (ordinateEquiv I)).1
  exact hf h
private theorem mixed_finite (I : Ideal Ambient) (h : ComponentFinite .mixed I) :
    Module.Finite SectionField (OverMixed I) := by
  have hf := (quotient_properties (F := SectionField) _ _ (mixedEquiv I)).1
  exact hf h
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_14_2_2_2.c4 := by
  intro P Q hp s t hs ht hP hQ S hS
  have hcap (k : Slice) (R : Jet) (d : Shape) (hR : RowCaps R d) := rowMap_caps k R d hR
  have hseed := plane_lengths .seed P Q S hS seed_transport _
    (h2 (SliceField .seed) _ _ s.B s.J t.B t.J hs ht (rowMap_proper .seed seed_transport P Q hp)
      (hcap .seed P s hP).1 (hcap .seed P s hP).2
      (hcap .seed Q t hQ).1 (hcap .seed Q t hQ).2)
  have hord := plane_lengths .ordinate P Q S hS h1.1 _
    (h3 (SliceField .ordinate) _ _ s.U s.J t.U t.J (rowMap_proper .ordinate h1.1 P Q hp)
      (hcap .ordinate P s hP).1 (hcap .ordinate P s hP).2
      (hcap .ordinate Q t hQ).1 (hcap .ordinate Q t hQ).2)
  have hmix := plane_lengths .mixed P Q S hS h1.2 _
    (h3 (SliceField .mixed) _ _ s.U s.B t.U t.B (rowMap_proper .mixed h1.2 P Q hp)
      (hcap .mixed P s hP).1 (hcap .mixed P s hP).2
      (hcap .mixed Q t hQ).1 (hcap .mixed Q t hQ).2)
  have hjcap (R : Jet) (d : Shape) (hR : RowCaps R d) :
      (rowMap .jets R).totalDegree ≤ d.U := hcap .jets R d hR
  have hj : ColengthAtMost (rowMap .jets P) (rowMap .jets Q) (s.U * t.U) := by
    have h := h2 (SliceField .jets) _ _ s.U s.U t.U t.U le_rfl le_rfl (rowMap_proper .jets jets_transport P Q hp)
      (hjcap P s hP) ((MvPolynomial.degreeOf_le_totalDegree _ _).trans (hjcap P s hP))
      (hjcap Q t hQ) ((MvPolynomial.degreeOf_le_totalDegree _ _).trans (hjcap Q t hQ))
    rw [Nat.mul_comm t.U s.U, Nat.add_sub_cancel] at h
    exact h
  have hjets := plane_lengths .jets P Q S hS jets_transport _ hj
  constructor
  · intro I hI
    exact ⟨hseed.1 I hI, ordinate_finite I (hord.1 I hI), mixed_finite I (hmix.1 I hI),
      hjets.1 I hI⟩
  intro i
  fin_cases i
  · change (∑ I ∈ S, Module.finrank SeedField (OverSeeds I)) ≤ s.B*t.J + t.B*s.J - s.J*t.J
    simpa only [seed_rank] using hseed.2
  · change (∑ I ∈ S, Module.finrank SectionField (OverOrdinate I)) ≤ s.U*t.J + t.U*s.J
    simpa only [ordinate_rank] using hord.2
  · change (∑ I ∈ S, Module.finrank SectionField (OverMixed I)) ≤ s.U*t.B + t.U*s.B
    simpa only [mixed_rank] using hmix.2
  · change (∑ I ∈ S, Module.finrank SeedField (OverJets I)) ≤ s.U*t.U
    simpa only [jets_rank] using hjets.2
end
end K1_14_2_2_2_4
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_2_4_1
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2_4 MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
abbrev Indices := Fin 2 ⊕ Fin 4
private abbrev Coefficients := MvPolynomial (Fin 4) FX
private abbrev Extended := MvPolynomial (Fin 2) Ambient
private abbrev Flat := MvPolynomial Indices FX
private abbrev Target := Plane SectionField
private abbrev nest : Flat ≃ₐ[FX] Extended := sumAlgEquiv FX (Fin 2) (Fin 4)
private def shifted (op : Flat → Flat → Flat) (a b : FX) : Fin 4 → Flat :=
  ![op (MvPolynomial.X (.inr 0)) (C a * MvPolynomial.X (.inl 0) * MvPolynomial.X (.inr 1)),
    MvPolynomial.X (.inr 1),
    op (MvPolynomial.X (.inr 2)) (C b * MvPolynomial.X (.inl 1) * MvPolynomial.X (.inr 3)),
    MvPolynomial.X (.inr 3)]
def shearMap (op : Flat → Flat → Flat) (a b : FX) : Flat →ₐ[FX] Flat :=
  aeval (Sum.elim (fun i => MvPolynomial.X (.inl i)) (shifted op a b))
private def shear (a b : FX) : Flat ≃ₐ[FX] Flat := by
  refine AlgEquiv.ofAlgHom (shearMap (· - ·) a b) (shearMap (· + ·) a b) ?_ ?_
  · apply algHom_ext
    rintro (i | i)
    · simp [shearMap]
    · fin_cases i <;> simp [shearMap, shifted, algebraMap_eq]
  · apply algHom_ext
    rintro (i | i)
    · simp [shearMap]
    · fin_cases i <;> simp [shearMap, shifted, algebraMap_eq]
private def indices : Indices ≃ Indices where
  toFun := Sum.elim ![Sum.inr 0, Sum.inr 1] ![Sum.inr 2, Sum.inl 0, Sum.inr 3, Sum.inl 1]
  invFun := Sum.elim ![Sum.inr 1, Sum.inr 3] ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 2]
  left_inv := by rintro (i | i) <;> fin_cases i <;> rfl
  right_inv := by rintro (i | i) <;> fin_cases i <;> rfl
private def regroup : Flat ≃ₐ[FX] Extended :=
  (renameEquiv FX indices).trans nest
private def chart (b : FX) : Extended ≃+* Extended :=
  ((nest.symm.trans (shear 1 b)).trans regroup).toRingEquiv
private def finish : Flat →+* Target :=
  (algebraMap Extended Target).comp regroup.toRingEquiv.toRingHom
theorem finish_X (i : Indices) :
    finish (MvPolynomial.X i) = Sum.elim MvPolynomial.X (fun j => C (sliceParameter j)) (indices i) := by
  change algebraMap Extended Target (nest (renameEquiv FX indices (MvPolynomial.X i))) = _
  rw [renameEquiv_apply, rename_X, MvPolynomial.algebraMap_def]
  cases indices i <;> simp [sliceParameter]
theorem finish_C (c : FX) : finish (C c) = C (algebraMap FX SectionField c) := by
  change algebraMap Extended Target (nest (renameEquiv FX indices (C c))) = _
  rw [renameEquiv_apply, rename_C, sumAlgEquiv_C_inl, MvPolynomial.algebraMap_def, map_C]
  rfl
private def lineMap (b : FX) : Ambient →+* Target :=
  ((algebraMap Extended Target).comp (chart b).toRingHom).comp C
theorem lineMap_eval (b : FX) :
    lineMap b = eval₂Hom (C.comp (algebraMap FX SectionField))
      (![C (sliceParameter 2) - C (sliceParameter 0) * MvPolynomial.X 0, MvPolynomial.X 0,
         C (sliceParameter 3) - C (algebraMap FX SectionField b) * C (sliceParameter 1) * MvPolynomial.X 1,
         MvPolynomial.X 1] : Fin 4 → Target) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change finish (shear 1 b (nest.symm (C (C c)))) = _
    rw [sumAlgEquiv_symm_C_C]
    change finish (shearMap (· - ·) 1 b (C c)) = _
    rw [show shearMap (· - ·) 1 b (C c) = C c by simp [algebraMap_eq]]
    rw [finish_C, eval₂Hom_C, RingHom.comp_apply]
  · intro i
    change finish (shear 1 b (nest.symm (C (MvPolynomial.X i)))) = _
    rw [sumAlgEquiv_symm_C_X]
    change finish (shearMap (· - ·) 1 b (MvPolynomial.X (.inr i))) = _
    rw [shearMap, aeval_X, Sum.elim_inr, eval₂Hom_X']
    fin_cases i <;> simp [shifted, finish_X, finish_C, indices]
theorem ordinate_lineMap : lineMap 0 = planeMap .ordinate := by
  change lineMap 0 = eval₂Hom (C.comp (algebraMap FX SectionField))
    (coordinates .ordinate : Fin 4 → Target)
  rw [lineMap_eval]
  apply congrArg (eval₂Hom (C.comp (algebraMap FX SectionField)))
  funext i
  fin_cases i <;> simp [coordinates, seedCoordinates, ordinateCoordinate, derivativeCoordinate] <;> rfl
theorem mixed_lineMap : lineMap 1 = planeMap .mixed := by
  change lineMap 1 = eval₂Hom (C.comp (algebraMap FX SectionField))
    (coordinates .mixed : Fin 4 → Target)
  rw [lineMap_eval]
  apply congrArg (eval₂Hom (C.comp (algebraMap FX SectionField)))
  funext i
  fin_cases i <;> simp [coordinates, seedCoordinates, ordinateCoordinate, derivativeCoordinate]
private theorem polynomial_prime {R σ : Type} [CommRing R] (I : Ideal R) (hI : I.IsPrime) :
    (I.map (C : R →+* MvPolynomial σ R)).IsPrime := by
  let : I.IsPrime := hI
  let q : MvPolynomial σ R →+* MvPolynomial σ (R ⧸ I) :=
    MvPolynomial.map (Ideal.Quotient.mk I)
  have hq : RingHom.ker q = I.map C := by
    dsimp only [q]
    rw [MvPolynomial.ker_map, Ideal.mk_ker]
  rw [← hq]
  exact RingHom.ker_isPrime q
theorem line_transport (b : FX) (I : Ideal Ambient) (hI : I.IsPrime) :
    I.map (lineMap b) = ⊤ ∨
      (I.map (lineMap b)).IsPrime ∧ (I.map (lineMap b)).comap (lineMap b) = I := by
  let C₀ : Ambient →+* Extended := C
  let e := chart b
  let L := algebraMap Extended Target
  let E := I.map C₀
  let J := E.map e.toRingHom
  let S : Submonoid Extended := (nonZeroDivisors Coefficients).map C
  have hE : E.IsPrime := polynomial_prime I hI
  have hEback : E.comap C₀ = I := by
    ext p
    constructor
    · intro hp
      change C p ∈ I.map C₀ at hp
      simpa using (MvPolynomial.mem_map_C_iff.mp hp 0)
    · exact Ideal.mem_map_of_mem C₀
  have hJ : J.IsPrime := by
    change (E.map (e : Extended →+* Extended)).IsPrime
    rw [Ideal.map_comap_of_equiv e]
    exact hE.comap _
  have hmap : I.map (lineMap b) = J.map L := by
    change I.map ((L.comp e.toRingHom).comp C₀) = _
    rw [← Ideal.map_map, ← Ideal.map_map]
  rw [hmap]
  by_cases ht : J.map L = ⊤
  · exact Or.inl ht
  have hd := (IsLocalization.map_algebraMap_ne_top_iff_disjoint S Target J).mp ht
  refine Or.inr ⟨IsLocalization.isPrime_of_isPrime_disjoint S Target J hJ hd, ?_⟩
  have hback : (J.map L).comap L = J :=
    IsLocalization.under_map_of_isPrime_disjoint S Target hJ hd
  change (J.map L).comap ((L.comp e.toRingHom).comp C₀) = I
  rw [← Ideal.comap_comap, ← Ideal.comap_comap, hback]
  have heback : J.comap e.toRingHom = E := Ideal.comap_map_of_bijective _ e.bijective
  rw [heback, hEback]
theorem proof : K1_14_2_2_2_4.c1 := by
  constructor
  · intro I hI
    rw [← ordinate_lineMap]
    exact line_transport 0 I hI
  · intro I hI
    rw [← mixed_lineMap]
    exact line_transport 1 I hI
end
end K1_14_2_2_2_4_1
end
section
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_2_3
noncomputable section
open K1_14 K1_14_2 K1_14_3_2
open scoped BigOperators
private def lastEquiv (F : Type*) [CommRing F] (n : ℕ) :
    Polynomial (MvPolynomial (Fin n) F) ≃+* MvPolynomial (Fin (n + 1)) F :=
  (MvPolynomial.optionEquivLeft F (Fin n)).symm.toRingEquiv.trans
    (MvPolynomial.renameEquiv F (finSuccEquivLast (n := n)).symm).toRingEquiv
private theorem lastEquiv_X (F : Type*) [CommRing F] (n : ℕ) :
    lastEquiv F n Polynomial.X = MvPolynomial.X (Fin.last n) := by
  change MvPolynomial.rename _ ((MvPolynomial.optionEquivLeft F (Fin n)).symm Polynomial.X) = _
  simp
private theorem lastEquiv_C (F : Type*) [CommRing F] (n : ℕ)
    (a : MvPolynomial (Fin n) F) :
    lastEquiv F n (Polynomial.C a) = MvPolynomial.rename Fin.castSucc a := by
  have h : (MvPolynomial.optionEquivLeft F (Fin n)).symm (Polynomial.C a) =
      MvPolynomial.rename some a := by
    change (Polynomial.aevalTower (MvPolynomial.rename some) (MvPolynomial.X none))
      (Polynomial.C a) = _
    simp
  change MvPolynomial.rename _
    ((MvPolynomial.optionEquivLeft F (Fin n)).symm (Polynomial.C a)) = _
  have he : (finSuccEquivLast (n := n)).symm ∘ some = Fin.castSucc := by
    funext i
    simp
  rw [h, MvPolynomial.rename_rename, he]
private theorem castLE_succ (n : ℕ) :
    (Fin.castLE (Nat.le_succ n) : Fin n → Fin (n + 1)) = Fin.castSucc := by
  funext i
  apply Fin.ext
  rfl
private def jetEquiv : Jet ≃+* Ambient :=
  (Polynomial.mapEquiv (lastEquiv FX 2)).trans (lastEquiv FX 3)
private theorem jetEquiv_apply (P : Jet) : jetEquiv P = toJet P := by
  have hroot : (lastEquiv FX 2).toRingHom = toRoot := by
    apply Polynomial.ringHom_ext
    · intro a
      simpa [toRoot, rootSeeds, castLE_succ] using lastEquiv_C FX 2 a
    · simpa [toRoot, Polynomial.coe_eval₂RingHom] using lastEquiv_X FX 2
  have hjet : jetEquiv.toRingHom = toJet := by
    apply Polynomial.ringHom_ext
    · intro a
      change lastEquiv FX 3 ((Polynomial.C a).map (lastEquiv FX 2).toRingHom) =
        toJet (Polynomial.C a)
      rw [Polynomial.map_C, lastEquiv_C, hroot]
      simp [toJet, rootIncl, castLE_succ]
    · change lastEquiv FX 3 (Polynomial.X.map (lastEquiv FX 2).toRingHom) =
        toJet Polynomial.X
      rw [Polynomial.map_X, lastEquiv_X]
      simp [toJet]
  exact RingHom.congr_fun hjet P
theorem maximal_height (F : Type*) [Field F] (n : ℕ)
    (m : Ideal (MvPolynomial (Fin n) F)) [m.IsMaximal] : m.height = n := by
  induction n with
  | zero =>
    have hd : ringKrullDim (MvPolynomial (Fin 0) F) = 0 := by
      rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.isEmptyRingEquiv F (Fin 0)),
        ringKrullDim_eq_zero_of_field]
    have h := Ideal.height_le_ringKrullDim_of_isPrime (I := m)
    rw [hd] at h
    exact le_antisymm (by exact_mod_cast h) (by simp)
  | succ n ih =>
    let e := (MvPolynomial.finSuccEquiv F n).toRingEquiv
    let M := m.map e
    have : M.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let p := M.comap (Polynomial.C : MvPolynomial (Fin n) F →+* _)
    have : p.IsMaximal :=
      Polynomial.isMaximal_comap_C_of_isJacobsonRing M
    have : M.LiesOver p := ⟨rfl⟩
    rw [← e.height_map m, Polynomial.height_eq_height_add_one p M, ih p]
    simp
theorem isolating_maximal {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsJacobsonRing R] {J I : Ideal R} (hI : I ∈ J.minimalPrimes) :
    ∃ m : Ideal R, m.IsMaximal ∧ I ≤ m ∧
      ∀ q ∈ J.minimalPrimes, q ≤ m → q = I := by
  classical
  let fmin := J.finite_minimalPrimes_of_isNoetherianRing
  let s := fmin.toFinset.erase I
  have hs (q : s) : ∃ x : R, x ∈ q.val ∧ x ∉ I := by
    obtain ⟨hne, hq⟩ := Finset.mem_erase.mp q.property
    have hmin : q.val ∈ J.minimalPrimes := fmin.mem_toFinset.mp hq
    by_contra! h
    exact hne (le_antisymm h (hI.2 hmin.1 h))
  choose f hf hfi using hs
  let x : R := ∏ q : s, f q
  have : I.IsPrime := hI.isPrime
  have hxI : x ∉ I := by
    intro hx
    obtain ⟨q, _, hq⟩ := Ideal.IsPrime.prod_mem_iff.mp hx
    exact hfi q hq
  have hrad : I.jacobson = I := (isJacobsonRing_iff_prime_eq.mp inferInstance) _ hI.isPrime
  have hm : ∃ m : Ideal R, m.IsMaximal ∧ I ≤ m ∧ x ∉ m := by
    by_contra! h
    apply hxI
    rw [← hrad, Ideal.jacobson, Ideal.mem_sInf]
    intro m hm
    exact h m hm.2 hm.1
  obtain ⟨m, hm, hIm, hxm⟩ := hm
  refine ⟨m, hm, hIm, fun q hq hqm => ?_⟩
  by_contra hne
  let i : s := ⟨q, Finset.mem_erase.mpr ⟨hne, fmin.mem_toFinset.mpr hq⟩⟩
  exact hxm (hqm (q.mem_of_dvd (Finset.dvd_prod_of_mem f (Finset.mem_univ i)) (hf i)))
theorem quotient_dim_lower {a b : Ambient} {I : Ideal Ambient}
    (hI : I ∈ (Ideal.span {a, b}).minimalPrimes) :
    2 ≤ ringKrullDim (CoordinateRing I) := by
  classical
  let J : Ideal Ambient := Ideal.span {a, b}
  obtain ⟨m, hm, hIm, honly⟩ := isolating_maximal hI
  have : m.IsPrime := hm.isPrime
  have hJm : J ≤ m := hI.le.trans hIm
  let M : Ideal (Ambient ⧸ J) := m.map (Ideal.Quotient.mk J)
  let m' : PrimeSpectrum (Ambient ⧸ J) :=
    ⟨M, Ideal.isPrime_map_quotientMk_of_isPrime hJm⟩
  have henc : ({a, b} : Set Ambient).encard ≤ 2 := by
    simpa [one_add_one_eq_two] using Set.encard_insert_le ({b} : Set Ambient) a
  have hmheight : m.height = (4 : ℕ∞) := by
    simpa only [Nat.cast_ofNat] using maximal_height FX 4 m
  have hquot : (4 : ℕ∞) ≤ Ideal.height (R := Ambient ⧸ J) M + 2 := by
    rw [← hmheight]
    exact (Ideal.height_le_height_add_encard_of_subset {a, b}
      (show ({a, b} : Set Ambient) ⊆ m from Ideal.span_le.mp hJm)).trans
        (add_le_add le_rfl henc)
  have htall : 1 < Order.height m' := by
    rw [← PrimeSpectrum.height_eq_orderHeight (R := Ambient ⧸ J) m']
    by_contra! h
    have hbad : (4 : ℕ∞) ≤ 1 + 2 := hquot.trans (add_le_add h le_rfl)
    exact (by decide : ¬ (4 : ℕ∞) ≤ 1 + 2) hbad
  obtain ⟨q, p, hpq, hqm⟩ := Order.one_lt_height_iff.mp htall
  let e := J.primeSpectrumQuotientOrderIsoZeroLocus
  have hm' : (e m').val.asIdeal = m := by
    change (m.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = m
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, J.mk_ker,
      sup_eq_left.mpr hJm]
  have habove (r : PrimeSpectrum (Ambient ⧸ J)) (hr : r ≤ m') :
      I ≤ (e r).val.asIdeal := by
    have hrm : (e r).val.asIdeal ≤ m := hm' ▸ e.monotone hr
    have : (e r).val.asIdeal.IsPrime := (e r).val.isPrime
    obtain ⟨u, hu, hule⟩ := Ideal.exists_minimalPrimes_le
      (show J ≤ (e r).val.asIdeal from (e r).property)
    exact honly u hu (hule.trans hrm) ▸ hule
  let liftPrime (r : PrimeSpectrum (Ambient ⧸ J)) (hr : r ≤ m') :
      PrimeSpectrum (CoordinateRing I) :=
    I.primeSpectrumQuotientOrderIsoZeroLocus.symm ⟨(e r).val, habove r hr⟩
  have hmono {r t : PrimeSpectrum (Ambient ⧸ J)} {hr : r ≤ m'} {ht : t ≤ m'}
      (hlt : r < t) : liftPrime r hr < liftPrime t ht :=
    I.primeSpectrumQuotientOrderIsoZeroLocus.symm.strictMono (e.strictMono hlt)
  let p₀ := liftPrime p (hpq.trans hqm).le
  let p₁ := liftPrime q hqm.le
  let p₂ := liftPrime m' le_rfl
  have h₀₁ : p₀ < p₁ := hmono (hr := (hpq.trans hqm).le) (ht := hqm.le) hpq
  have h₁₂ : p₁ < p₂ := hmono (hr := hqm.le) (ht := le_rfl) hqm
  have htall' : 1 < Order.height p₂ :=
    Order.one_lt_height_iff.mpr ⟨p₁, p₀, h₀₁, h₁₂⟩
  have htwo : (2 : ℕ∞) ≤ Order.height p₂ := by
    simpa only [one_add_one_eq_two] using (ENat.add_one_le_iff ENat.one_ne_top).mpr htall'
  exact (WithBot.coe_le_coe.mpr htwo).trans (Order.height_le_krullDim p₂)
theorem quotient_dim_upper {a b : Ambient} (ha : a ≠ 0)
    (hcop : ∀ D : Ambient, Irreducible D → D ∣ a → ¬ D ∣ b)
    {I : Ideal Ambient} [I.IsPrime] (haI : a ∈ I) (hbI : b ∈ I) :
    ringKrullDim (CoordinateRing I) ≤ 2 := by
  have hI₀ : I ≠ ⊥ := fun h => ha (by simpa [h] using haI)
  obtain ⟨D, hD, hprime⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot ‹I.IsPrime› hI₀
  let T : Ideal Ambient := Ideal.span {D}
  have : T.IsPrime := (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  have hT₀ : (⊥ : Ideal Ambient) < T :=
    bot_lt_iff_ne_bot.mpr (fun h => hprime.ne_zero (Ideal.span_singleton_eq_bot.mp h))
  have hTI : T < I := by
    refine lt_of_le_of_ne ((Ideal.span_singleton_le_iff_mem I).mpr hD) ?_
    intro he
    exact hcop D hprime.irreducible
      (Ideal.mem_span_singleton.mp (he ▸ haI : a ∈ T))
      (Ideal.mem_span_singleton.mp (he ▸ hbI : b ∈ T))
  have hd : ringKrullDim Ambient = 4 := by simp [Ambient, ringKrullDim_eq_zero_of_field]
  have hbound : ringKrullDim (CoordinateRing I) + 2 ≤ 4 := by
    calc
      _ = (ringKrullDim (CoordinateRing I) + 1) + 1 := by rw [add_assoc]; norm_num
      _ ≤ ringKrullDim (CoordinateRing T) + 1 :=
        add_le_add (Ideal.ringKrullDim_quotient_succ_le_of_lt hTI) le_rfl
      _ ≤ ringKrullDim (Ambient ⧸ (⊥ : Ideal Ambient)) :=
        Ideal.ringKrullDim_quotient_succ_le_of_lt hT₀
      _ = 4 := (RingEquiv.quotientBot Ambient).ringKrullDim.trans hd
  exact (ENat.WithBot.add_le_add_natCast_right_iff (c := 2)).mp
    (by simpa only [Nat.cast_ofNat, show (2 : WithBot ℕ∞) + 2 = 4 by decide] using hbound)
theorem proof : K1_14_2_2_2.c3 := by
  classical
  intro P Q h
  let a := toJet P
  let b := toJet Q
  have ha : a ≠ 0 := by
    rw [show a = jetEquiv P from (jetEquiv_apply P).symm]
    exact map_ne_zero_iff jetEquiv jetEquiv.injective |>.mpr h.left_ne
  have hcop (D : Ambient) (hD : Irreducible D) (hDa : D ∣ a) : ¬ D ∣ b := by
    obtain ⟨d, rfl⟩ := jetEquiv.surjective D
    rw [show a = jetEquiv P from (jetEquiv_apply P).symm, map_dvd_iff] at hDa
    rw [show b = jetEquiv Q from (jetEquiv_apply Q).symm, map_dvd_iff]
    exact h.no_common d ((MulEquiv.irreducible_iff jetEquiv).mp hD) hDa
  let J : Ideal Ambient := Ideal.span {a, b}
  let fmin := J.finite_minimalPrimes_of_isNoetherianRing
  let S := fmin.toFinset
  refine ⟨S, ?_, ?_⟩
  · intro I hI
    have hmin : I ∈ J.minimalPrimes := fmin.mem_toFinset.mp hI
    have : I.IsPrime := hmin.isPrime
    have haI : a ∈ I := hmin.le (Ideal.subset_span (by simp))
    have hbI : b ∈ I := hmin.le (Ideal.subset_span (by simp))
    exact ⟨hmin.isPrime, le_antisymm (quotient_dim_upper ha hcop haI hbI)
      (quotient_dim_lower hmin), haI, hbI⟩
  · intro z R hP hQ
    let e := jetMarkHom z R
    have : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
    have hJ : J ≤ RingHom.ker e := by
      refine Ideal.span_le.mpr ?_
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact (eval_toJet z R P).trans hP
      · exact (eval_toJet z R Q).trans hQ
    obtain ⟨I, hI, hIe⟩ := Ideal.exists_minimalPrimes_le hJ
    exact ⟨I, fmin.mem_toFinset.mpr hI, hIe⟩
end
end K1_14_2_2_2_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_2_1
noncomputable section
open K1_14 K1_14_2_2 K1_14_3_2 Polynomial
private def jetVariables : Jet →+* MvPolynomial (Fin 2) Seeds :=
  (MvPolynomial.finSuccEquiv Seeds 1).symm.toRingHom.comp
    (Polynomial.mapRingHom (MvPolynomial.uniqueAlgEquiv Seeds (Fin 1)).symm.toRingHom)
theorem coeff_jetVariables (P : Jet) (d : Fin 2 →₀ ℕ) :
    (jetVariables P).coeff d = (P.coeff (d 0)).coeff (d 1) := by
  let Q := P.map (MvPolynomial.uniqueAlgEquiv Seeds (Fin 1)).symm.toRingHom
  change ((MvPolynomial.finSuccEquiv Seeds 1).symm Q).coeff d = _
  rw [← Finsupp.cons_tail d, ← MvPolynomial.finSuccEquiv_coeff_coeff,
    AlgEquiv.apply_symm_apply]
  simp only [Q, Polynomial.coeff_map]
  change ((MvPolynomial.uniqueAlgEquiv Seeds (Fin 1)).symm (P.coeff (d 0))).coeff d.tail = _
  rw [MvPolynomial.coeff_uniqueAlgEquiv_symm]
  rfl
theorem jetVariables_injective : Function.Injective jetVariables :=
  (MvPolynomial.finSuccEquiv Seeds 1).symm.injective.comp
    (Polynomial.map_injective _ (MvPolynomial.uniqueAlgEquiv Seeds (Fin 1)).symm.injective)
private def seedVariables : Jet →+* MvPolynomial (Fin 2) (MvPolynomial (Fin 2) FX) :=
  (MvPolynomial.commAlgEquiv FX (Fin 2) (Fin 2)).toRingHom.comp jetVariables
theorem coeff_seedVariables (P : Jet) (e d : Fin 2 →₀ ℕ) :
    ((seedVariables P).coeff e).coeff d = ((P.coeff (d 0)).coeff (d 1)).coeff e := by
  rw [← coeff_jetVariables]
  change ((MvPolynomial.commAlgEquiv FX (Fin 2) (Fin 2) (jetVariables P)).coeff e).coeff d =
    ((jetVariables P).coeff d).coeff e
  simp [MvPolynomial.commAlgEquiv, AddMonoidAlgebra.commAlgEquiv,
    AddMonoidAlgebra.curryAlgEquiv, AddMonoidAlgebra.curryRingEquiv,
    AddMonoidAlgebra.curryAddEquiv, AddMonoidAlgebra.coeff_domCongr]
theorem seedVariables_injective : Function.Injective seedVariables :=
  (MvPolynomial.commAlgEquiv FX (Fin 2) (Fin 2)).injective.comp jetVariables_injective
def jetDegree (P : Jet) : ℕ := (jetVariables P).totalDegree
def seedDegree (P : Jet) : ℕ := (seedVariables P).totalDegree
theorem jetDegree_mul {P Q : Jet} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    jetDegree (P * Q) = jetDegree P + jetDegree Q := by
  unfold jetDegree
  rw [map_mul, MvPolynomial.totalDegree_mul_of_isDomain
    ((map_ne_zero_iff _ jetVariables_injective).mpr hP)
    ((map_ne_zero_iff _ jetVariables_injective).mpr hQ)]
theorem seedDegree_mul {P Q : Jet} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    seedDegree (P * Q) = seedDegree P + seedDegree Q := by
  unfold seedDegree
  rw [map_mul, MvPolynomial.totalDegree_mul_of_isDomain
    ((map_ne_zero_iff _ seedVariables_injective).mpr hP)
    ((map_ne_zero_iff _ seedVariables_injective).mpr hQ)]
private theorem sum_exponents (d : Fin 2 →₀ ℕ) : (d.sum fun _ e => e) = d 1 + d 0 := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two, Nat.add_comm]
theorem jetDegree_le (P : Jet) (b : ℕ) :
    jetDegree P ≤ b ↔ ∀ j i, (P.coeff j).coeff i ≠ 0 → i+j ≤ b := by
  constructor
  · intro h j i hji
    let d : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![j, i]
    have hd : d ∈ (jetVariables P).support := by
      rw [MvPolynomial.mem_support_iff, coeff_jetVariables]
      exact hji
    have hsum := (MvPolynomial.le_totalDegree hd).trans h
    rw [sum_exponents] at hsum
    exact hsum
  · intro h
    apply Finset.sup_le
    intro d hd
    rw [sum_exponents]
    rw [MvPolynomial.mem_support_iff, coeff_jetVariables] at hd
    exact h _ _ hd
theorem seedDegree_le (P : Jet) (u : ℕ) :
    seedDegree P ≤ u ↔ ∀ j i, ((P.coeff j).coeff i).totalDegree ≤ u := by
  constructor
  · intro h j i
    apply Finset.sup_le
    intro e he
    apply (MvPolynomial.le_totalDegree (p := seedVariables P) ?_).trans h
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    let d : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![j, i]
    have hzero := congrArg (fun a : MvPolynomial (Fin 2) FX => a.coeff d) hz
    rw [coeff_seedVariables, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hzero
    exact (MvPolynomial.mem_support_iff.mp he) hzero
  · intro h
    apply Finset.sup_le
    intro e he
    obtain ⟨d, hd⟩ : ∃ d, ((seedVariables P).coeff e).coeff d ≠ 0 := by
      by_contra! hz
      apply MvPolynomial.mem_support_iff.mp he
      ext d
      rw [hz, AddMonoidAlgebra.coeff_zero]
      rfl
    rw [coeff_seedVariables] at hd
    exact (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hd)).trans (h _ _)
theorem rowCaps_iff (P : Jet) (s : K1_14.Shape) :
    RowCaps P s ↔ jetDegree P ≤ s.B ∧ P.natDegree ≤ s.J ∧ seedDegree P ≤ s.U := by
  rw [jetDegree_le, seedDegree_le]
  constructor
  · intro h
    refine ⟨fun j i hji => (h j i hji).1, natDegree_le_iff_coeff_eq_zero.mpr ?_, ?_⟩
    · intro j hj
      apply Polynomial.ext
      intro i
      rw [coeff_zero]
      by_contra hi
      exact (Nat.not_le_of_lt hj) (h j i hi).2.1
    · intro j i
      by_cases hz : (P.coeff j).coeff i = 0
      · simp [hz]
      · exact (h j i hz).2.2
  · rintro ⟨hB, hJ, hU⟩ j i hi
    have hj : P.coeff j ≠ 0 := by intro hz; simp [hz] at hi
    exact ⟨hB j i hi, (le_natDegree_of_ne_zero hj).trans hJ, hU j i⟩
theorem jetDegree_C (f : Equation) : jetDegree (C f) = f.natDegree := by
  apply le_antisymm
  · apply (jetDegree_le _ _).mpr
    intro j i hi
    cases j with
    | zero => simpa using le_natDegree_of_ne_zero (by simpa using hi : f.coeff i ≠ 0)
    | succ j => simp at hi
  · by_cases hf : f = 0
    · simp [hf]
    · have hc : ((C f : Jet).coeff 0).coeff f.natDegree ≠ 0 := by
        simpa [coeff_natDegree] using leadingCoeff_ne_zero.mpr hf
      simpa using (jetDegree_le _ _).mp le_rfl 0 f.natDegree hc
theorem seedDegree_C (f : Equation) : seedDegree (C f) = ordinarySeedDegree f := by
  apply le_antisymm
  · apply (seedDegree_le _ _).mpr
    intro j i
    cases j with
    | zero =>
      simp only [coeff_C_zero]
      by_cases hi : f.coeff i = 0
      · simp [hi]
      · exact Finset.le_sup (f := fun y => (f.coeff y).totalDegree) (mem_support_iff.mpr hi)
    | succ j => simp
  · apply Finset.sup_le
    intro i _
    simpa using (seedDegree_le (C f) _).mp le_rfl 0 i
theorem seedDegree_seed (a : Seeds) : seedDegree (C (C a)) = a.totalDegree := by
  rw [seedDegree_C]
  by_cases ha : a = 0
  · simp [ha, ordinarySeedDegree]
  · simp [ordinarySeedDegree, support_C ha]
end
end K1_14_2_2_2_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_2_1
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_3_2 Polynomial
theorem extractSeed (P : Jet) (hP : P ≠ 0) :
    ∃ (a : Seeds) (R : Jet), P = C (C a) * R ∧
      ∀ b : Seeds, C (C b) ∣ R → IsUnit b := by
  classical
  revert hP
  refine (wellFounded_dvdNotUnit (α := Jet)).induction
    (C := fun P => P ≠ 0 → ∃ (a : Seeds) (R : Jet), P = C (C a) * R ∧
      ∀ b : Seeds, C (C b) ∣ R → IsUnit b) P ?_
  intro P ih hP
  by_cases h : ∃ b : Seeds, ¬ IsUnit b ∧ C (C b) ∣ P
  · obtain ⟨b, hb, Q, hQ⟩ := h
    have hQ0 : Q ≠ 0 := fun hz => hP (by simpa [hz] using hQ)
    have hlt : DvdNotUnit Q P :=
      ⟨hQ0, C (C b), fun hu => hb (isUnit_C.mp (isUnit_C.mp hu)), hQ.trans (mul_comm _ _)⟩
    obtain ⟨a, R, hR, hstrip⟩ := ih Q hlt hQ0
    exact ⟨b*a, R, by rw [C_mul, C_mul, mul_assoc, ← hR, ← hQ], hstrip⟩
  · exact ⟨1, P, by simp, fun b hb => by by_contra hu; exact h ⟨b, hu, hb⟩⟩
private theorem exists_fixedIncl (D : Jet) (h : ¬ UsesSeed D) : ∃ G : ODE, D = fixedIncl G := by
  let e : Seeds →+* FX := MvPolynomial.eval (fun _ => 0)
  refine ⟨D.map (Polynomial.mapRingHom e), ?_⟩
  apply Polynomial.ext
  intro j
  apply Polynomial.ext
  intro i
  simp only [fixedIncl, K1_14_3.fixedEmbedding, Polynomial.coe_mapRingHom, coeff_map]
  have hzero : ((D.coeff j).coeff i).totalDegree = 0 :=
    Nat.eq_zero_of_not_pos (fun hp => h ⟨j,i,hp⟩)
  obtain hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hzero
  rw [hc]
  simp [e]
theorem commonOrdinary {w rows i} {B : RowPair w rows i} (A : FixedPair B)
    {D : Jet} (hD : Irreducible D) (hP : D ∣ A.cheap.residual) (hQ : D ∣ A.layered.residual) :
    D.natDegree = 0 := by
  by_contra hpos
  have hdP : D ∣ B.cheap := hP.trans ⟨_, A.cheap.factorization.trans (mul_comm _ _)⟩
  have hdQ : D ∣ B.layered := hQ.trans ⟨_, A.layered.factorization.trans (mul_comm _ _)⟩
  have hseed : ¬ UsesSeed D := fun hs => B.no_moving D hD hdP (Nat.pos_of_ne_zero hpos) hs hdQ
  obtain ⟨G, rfl⟩ := exists_fixedIncl D hseed
  exact A.cheap.stripped G hD hP
theorem extractOrdinary (P Q : Jet) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hseed : ∀ b : Seeds, C (C b) ∣ P → IsUnit b)
    (hord : ∀ D : Jet, Irreducible D → D ∣ P → D ∣ Q → D.natDegree = 0) :
    ∃ (M : Multiset Equation) (L T : Jet), P = C M.prod * L ∧ Q = C M.prod * T ∧
      ProperPair L T ∧ ∀ f ∈ M, Irreducible f ∧ 0 < f.natDegree := by
  classical
  revert Q
  revert hP hseed
  refine (wellFounded_dvdNotUnit (α := Jet)).induction
    (C := fun P => P ≠ 0 → (∀ b : Seeds, C (C b) ∣ P → IsUnit b) →
      ∀ Q : Jet, Q ≠ 0 →
      (∀ D : Jet, Irreducible D → D ∣ P → D ∣ Q → D.natDegree = 0) →
      ∃ (M : Multiset Equation) (L T : Jet), P = C M.prod * L ∧ Q = C M.prod * T ∧
        ProperPair L T ∧ ∀ f ∈ M, Irreducible f ∧ 0 < f.natDegree) P ?_
  intro P ih hP hseed Q hQ hord
  by_cases h : ∃ D : Jet, Irreducible D ∧ D ∣ P ∧ D ∣ Q
  · obtain ⟨D, hD, hDP, hDQ⟩ := h
    let f := D.coeff 0
    have hd : D = C f := eq_C_of_natDegree_eq_zero (hord D hD hDP hDQ)
    have hf : Irreducible f := by
      rw [hd] at hD
      refine ⟨fun hu => hD.not_isUnit (isUnit_C.mpr hu), ?_⟩
      intro a b hab
      have he : (C f : Jet) = C a * C b := by rw [← C_mul, ← hab]
      exact (hD.isUnit_or_isUnit he).imp isUnit_C.mp isUnit_C.mp
    have hfpos : 0 < f.natDegree := by
      by_contra! hzero
      have hc := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hzero)
      have hdiv : C f ∣ P := hd ▸ hDP
      rw [hc] at hdiv
      apply hf.not_isUnit
      rw [hc]
      exact isUnit_C.mpr (hseed _ hdiv)
    obtain ⟨P', hP'⟩ := hDP
    obtain ⟨Q', hQ'⟩ := hDQ
    have hP'0 : P' ≠ 0 := fun hz => hP (by simpa [hz] using hP')
    have hQ'0 : Q' ≠ 0 := fun hz => hQ (by simpa [hz] using hQ')
    have hPdiv : P' ∣ P := ⟨D, hP'.trans (mul_comm _ _)⟩
    have hQdiv : Q' ∣ Q := ⟨D, hQ'.trans (mul_comm _ _)⟩
    have hlt : DvdNotUnit P' P := ⟨hP'0, D, hD.not_isUnit, hP'.trans (mul_comm _ _)⟩
    obtain ⟨M, L, T, hL, hT, hproper, hM⟩ :=
      ih P' hlt hP'0 (fun b hb => hseed b (hb.trans hPdiv)) Q' hQ'0
        (fun D hD hdP hdQ => hord D hD (hdP.trans hPdiv) (hdQ.trans hQdiv))
    refine ⟨f ::ₘ M, L, T, ?_, ?_, hproper, ?_⟩
    · rw [hP', hd, Multiset.prod_cons, C_mul, mul_assoc, ← hL]
    · rw [hQ', hd, Multiset.prod_cons, C_mul, mul_assoc, ← hT]
    · intro g hg
      rcases Multiset.mem_cons.mp hg with rfl | hg
      · exact ⟨hf, hfpos⟩
      · exact hM g hg
  · exact ⟨0,P,Q,by simp,by simp,⟨hP,hQ,fun D hD hdP hdQ => h ⟨D,hD,hdP,hdQ⟩⟩,by simp⟩
end
end K1_14_2_2_2_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_2_1
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2 K1_14_3_2 Polynomial
open scoped BigOperators
private theorem divisor_caps {P R : Jet} {s : Shape} (hP : P ≠ 0)
    (h : RowCaps P s) (hd : R ∣ P) : RowCaps R s := by
  obtain ⟨V, hV⟩ := hd
  have hmul : R * V ≠ 0 := hV ▸ hP
  obtain ⟨hb, hj, hu⟩ := (rowCaps_iff P s).mp h
  rw [hV, jetDegree_mul (left_ne_zero_of_mul hmul) (right_ne_zero_of_mul hmul)] at hb
  rw [hV, natDegree_mul (left_ne_zero_of_mul hmul) (right_ne_zero_of_mul hmul)] at hj
  rw [hV, seedDegree_mul (left_ne_zero_of_mul hmul) (right_ne_zero_of_mul hmul)] at hu
  exact (rowCaps_iff R s).mpr ⟨by omega, by omega, by omega⟩
private theorem seedContent_cap {P : Jet} {a : Seeds} {s : Shape}
    (hP : P ≠ 0) (h : RowCaps P s) (hd : C (C a) ∣ P) : a.totalDegree ≤ s.U := by
  have hu := ((rowCaps_iff _ _).mp (divisor_caps hP h hd)).2.2
  rwa [seedDegree_seed] at hu
private theorem gcd_caps {F : Equation} {R : Jet} {s : Shape}
    (hF : F ≠ 0) (hR : R ≠ 0) (h : RowCaps (C F * R) s) :
    ordinarySeedDegree F ≤ s.U ∧ F.natDegree ≤ s.B ∧
      RowCaps R (afterGcd s (ordinarySeedDegree F) F.natDegree) := by
  have hC : (C F : Jet) ≠ 0 := C_ne_zero.mpr hF
  obtain ⟨hB, hJ, hU⟩ := (rowCaps_iff _ _).mp h
  rw [jetDegree_mul hC hR, jetDegree_C] at hB
  rw [natDegree_mul hC hR, natDegree_C, zero_add] at hJ
  rw [seedDegree_mul hC hR, seedDegree_C] at hU
  have hJR : R.natDegree ≤ jetDegree R := by
    have hv := leadingCoeff_ne_zero.mpr hR
    have hc : (R.coeff R.natDegree).coeff R.leadingCoeff.natDegree ≠ 0 := by
      rw [coeff_natDegree, coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hv
    have htop := (jetDegree_le _ _).mp le_rfl _ _ hc
    omega
  refine ⟨by omega, by omega, (rowCaps_iff _ _).mpr ?_⟩
  change jetDegree R ≤ s.B - F.natDegree ∧
    R.natDegree ≤ min s.J (s.B - F.natDegree) ∧ seedDegree R ≤ s.U - ordinarySeedDegree F
  exact ⟨by omega, le_min hJ (by omega), by omega⟩
private theorem multiset_prod_ne_zero (M : Multiset Equation) (hM : ∀ f ∈ M, f ≠ 0) :
    M.prod ≠ 0 :=
  Multiset.prod_ne_zero (fun he => hM 0 he rfl)
private theorem distinct_le_degree [DecidableEq Equation] (d : Equation → ℕ) (h1 : d 1 = 0)
    (hmul : ∀ {f g}, f ≠ 0 → g ≠ 0 → d (f * g) = d f + d g)
    (M : Multiset Equation) (hM : ∀ f ∈ M, f ≠ 0) :
    (∑ f ∈ M.toFinset, d f) ≤ d M.prod := by
  induction M using Multiset.induction_on with
  | empty => simp [h1]
  | cons f M ih =>
    have hrest : ∀ g ∈ M, g ≠ 0 := fun g hg => hM g (Multiset.mem_cons_of_mem hg)
    rw [Multiset.prod_cons, hmul (hM f (by simp)) (multiset_prod_ne_zero M hrest),
      Multiset.toFinset_cons]
    by_cases hf : f ∈ M.toFinset
    · rw [Finset.insert_eq_of_mem hf]
      exact (ih hrest).trans (Nat.le_add_left _ _)
    · rw [Finset.sum_insert hf]
      exact Nat.add_le_add_left (ih hrest) _
private theorem seed_degree_mul {f g : Equation} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordinarySeedDegree (f * g) = ordinarySeedDegree f + ordinarySeedDegree g := by
  simpa only [← seedDegree_C, C_mul] using
    seedDegree_mul (C_ne_zero.mpr hf) (C_ne_zero.mpr hg)
private theorem atMark_prod_eq_zero {M : Multiset Equation} {z : K} {S : K[X]}
    (h : atMark M.prod z S = 0) : ∃ f ∈ M, atMark f z S = 0 := by
  let e := eval₂RingHom (graphEval z) (atX S)
  change e M.prod = 0 at h
  rw [map_multiset_prod] at h
  exact Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp h)
private theorem jetAt_mul (z : K) (S : K[X]) (P Q : Jet) :
    jetAt (P * Q) z S = jetAt P z S * jetAt Q z S :=
  (markEval z S).map_mul P Q
private theorem jetAt_ordinary (z : K) (S : K[X]) (f : Equation) :
    jetAt (C f) z S = atMark f z S := by
  simp [jetAt, atMark]
theorem jetAt_seed (z : K) (S : K[X]) (a : Seeds) :
    jetAt (C (C a)) z S = graphEval z a := by
  simp [jetAt]
theorem jetAt_fixed (z : K) (S : K[X]) (G : ODE) :
    jetAt (fixedIncl G) z S = fixedAt G S := by
  rw [← eval_toJet, eval_fixed]
theorem row_at_mark {P R : Jet} {G : ODE} {a : Seeds} {F : Equation}
    (h : P = fixedIncl G * (C (C a) * (C F * R))) (z : K) (S : K[X]) :
    jetAt P z S = fixedAt G S * (graphEval z a * (atMark F z S * jetAt R z S)) := by
  rw [h, jetAt_mul, jetAt_mul, jetAt_mul, jetAt_fixed, jetAt_seed, jetAt_ordinary]
theorem proof : K1_14_2_2_2.c1 := by
  classical
  intro w rows B A
  have hpr : A.cheap.residual ≠ 0 := fun hz =>
    B.cheap_ne (by rw [A.cheap.factorization, hz, mul_zero])
  have hqr : A.layered.residual ≠ 0 := fun hz =>
    B.layered_ne (by rw [A.layered.factorization, hz, mul_zero])
  obtain ⟨a, P, ha, hpa⟩ := extractSeed A.cheap.residual hpr
  obtain ⟨b, Q, hb, _⟩ := extractSeed A.layered.residual hqr
  have hpa0 : (C (C a) * P : Jet) ≠ 0 := ha ▸ hpr
  have hqb0 : (C (C b) * Q : Jet) ≠ 0 := hb ▸ hqr
  have hP : P ∣ A.cheap.residual := ⟨_, ha.trans (mul_comm _ _)⟩
  have hQ : Q ∣ A.layered.residual := ⟨_, hb.trans (mul_comm _ _)⟩
  obtain ⟨M, L, T, hL, hT, hproper, hM⟩ := extractOrdinary P Q
    (right_ne_zero_of_mul hpa0) (right_ne_zero_of_mul hqb0) hpa
    (fun D hD hdP hdQ => commonOrdinary A hD (hdP.trans hP) (hdQ.trans hQ))
  have ha0 : a ≠ 0 := by intro hz; simp [hz] at hpa0
  have hb0 : b ≠ 0 := by intro hz; simp [hz] at hqb0
  have haP : C (C a) ∣ B.cheap :=
    (show C (C a) ∣ A.cheap.residual from ⟨P, ha⟩).trans
      ⟨_, A.cheap.factorization.trans (mul_comm _ _)⟩
  have hbQ : C (C b) ∣ B.layered :=
    (show C (C b) ∣ A.layered.residual from ⟨Q, hb⟩).trans
      ⟨_, A.layered.factorization.trans (mul_comm _ _)⟩
  have hau : a.totalDegree ≤ 1899 := seedContent_cap B.cheap_ne B.cheap_caps haP
  have hbu : b.totalDegree ≤ 8441 := seedContent_cap B.layered_ne B.layered_caps hbQ
  have hM0 : ∀ f ∈ M, f ≠ 0 := fun f hf => (hM f hf).1.ne_zero
  have hF := multiset_prod_ne_zero M hM0
  have hp : B.cheap = fixedIncl A.cheap.equation * (C (C a) * (C M.prod * L)) :=
    A.cheap.factorization.trans (by rw [ha, hL])
  have hq : B.layered = fixedIncl A.layered.equation * (C (C b) * (C M.prod * T)) :=
    A.layered.factorization.trans (by rw [hb, hT])
  have hl : C M.prod * L ∣ B.cheap :=
    ⟨fixedIncl A.cheap.equation * C (C a), hp.trans (by rw [← mul_assoc, mul_comm])⟩
  have ht : C M.prod * T ∣ B.layered :=
    ⟨fixedIncl A.layered.equation * C (C b), hq.trans (by rw [← mul_assoc, mul_comm])⟩
  obtain ⟨hx, hy, hc⟩ := gcd_caps hF hproper.left_ne (divisor_caps B.cheap_ne B.cheap_caps hl)
  have htCaps := (gcd_caps hF hproper.right_ne (divisor_caps B.layered_ne B.layered_caps ht)).2.2
  have hs1 : ordinarySeedDegree (1 : Equation) = 0 := by
    rw [← seedDegree_C]
    simpa only [C_1, MvPolynomial.totalDegree_one] using seedDegree_seed (1 : Seeds)
  refine ⟨{
    seedContent := a*b
    cheap := L
    layered := T
    ordinary := M.toFinset
    gcdSeed := ordinarySeedDegree M.prod
    gcdY := M.prod.natDegree
    seedContent_ne := mul_ne_zero ha0 hb0
    seedContent_degree := (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hau hbu)
    gcdSeed_le := hx
    gcdY_le := hy
    cheap_caps := hc
    layered_caps := htCaps
    proper := hproper
    ordinary_factors := fun f hf => hM f (Multiset.mem_toFinset.mp hf)
    ordinary_seed := distinct_le_degree ordinarySeedDegree hs1 (fun hf hg => seed_degree_mul hf hg) M hM0
    ordinary_y := distinct_le_degree natDegree natDegree_one (fun hf hg => natDegree_mul hf hg) M hM0
    cover := ?_ }⟩
  intro z S hzP hzQ
  by_cases h1 : fixedAt A.cheap.equation S = 0
  · exact Or.inl h1
  by_cases h2 : fixedAt A.layered.equation S = 0
  · exact Or.inr (Or.inl h2)
  by_cases h3 : graphEval z (a*b) = 0
  · exact Or.inr (Or.inr (Or.inl h3))
  by_cases h4 : atMark M.prod z S = 0
  · obtain ⟨f, hf, hzero⟩ := atMark_prod_eq_zero h4
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨f, Multiset.mem_toFinset.mpr hf, hzero⟩)))
  · rw [map_mul] at h3
    rw [row_at_mark hp, mul_eq_zero, mul_eq_zero, mul_eq_zero] at hzP
    rw [row_at_mark hq, mul_eq_zero, mul_eq_zero, mul_eq_zero] at hzQ
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨((hzP.resolve_left h1).resolve_left (left_ne_zero_of_mul h3)).resolve_left h4,
       ((hzQ.resolve_left h2).resolve_left (right_ne_zero_of_mul h3)).resolve_left h4⟩)))
end
end K1_14_2_2_2_1
end
section
namespace K1_14_3_8
open K1_14 K1_14_3 Finset
open scoped BigOperators
def lostWidth (h q j : ℕ) : ℕ :=
  fullShape.m*180265 + j - q*(131071-h) - 2*h*(j+(q-j)/5)
def intShapeSum (f : ℕ → ℕ → ℤ) : ℤ :=
  ∑ q ∈ range (fullShape.B+1), ∑ j ∈ range (min q fullShape.J+1), f q j
private def widthSlope (q j : ℕ) : ℤ :=
  (q : ℤ) - 2 * (j + ((q-j)/5 : ℕ))
private def signedWidth (h : ℤ) (q j : ℕ) : ℤ :=
  (fullShape.m : ℤ)*180265 + j - q*131071 + h * widthSlope q j
def supportSum (f : ℕ → ℕ → ℤ) : ℤ :=
  intShapeSum (fun q j => if 0 < signedWidth 3555 q j then f q j else 0)
def supportBase : ℤ :=
  (triangle fullShape.U : ℤ) * supportSum (signedWidth 3555)
def supportSlope : ℤ :=
  (triangle fullShape.U : ℤ) * supportSum widthSlope
def nodeDebitOf (s : Shape) : ℕ :=
  triangle s.U * 262144 * shapeSum s (fun q i => s.m + min q s.J - (q+2*i))
def poleSlopeOf (s : Shape) : ℕ :=
  2*(s.U+1) * shapeSum s (fun q _ => (s.B+s.J-q)*(s.B-q))
def nodeDebit : ℕ := nodeDebitOf fullShape
private def poleSlope : ℕ := poleSlopeOf fullShape
theorem debit_eq_shape (h : ℕ) (s : Shape) :
    sourceDebit h s = nodeDebitOf s + h * poleSlopeOf s := by
  unfold sourceDebit nodeDebitOf poleSlopeOf
  ring
private theorem debit_eq (h : ℕ) :
    sourceDebit h fullShape = nodeDebit + h * poleSlope :=
  debit_eq_shape h fullShape
theorem signedWidth_le (h q j : ℕ) (hh : h ≤ 131071) :
    signedWidth h q j ≤ (lostWidth h q j : ℤ) := by
  have hcast : (↑(131071-h : ℕ) : ℤ) = 131071 - h := Nat.cast_sub hh
  calc
    signedWidth h q j =
        (↑(fullShape.m*180265 + j : ℕ) : ℤ) -
        (↑(q*(131071-h) : ℕ) : ℤ) - (↑(2*h*(j+(q-j)/5) : ℕ) : ℤ) := by
      simp only [signedWidth, widthSlope, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hcast]
      ring
    _ ≤ (lostWidth h q j : ℤ) := by unfold lostWidth; omega
theorem support_line (h : ℤ) :
    supportBase + (h-3555)*supportSlope =
      (triangle fullShape.U : ℤ) * supportSum (signedWidth h) := by
  unfold supportBase supportSlope supportSum intShapeSum
  rw [mul_left_comm (h-3555), ← mul_add]
  apply congrArg ((triangle fullShape.U : ℤ) * ·)
  simp only [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro j _
  split_ifs
  · unfold signedWidth
    ring
  · simp
private theorem support_le (h : ℕ) (hh : h ≤ 131071) :
    supportBase + ((h : ℤ)-3555)*supportSlope ≤
      ((triangle fullShape.U * shapeSum fullShape (lostWidth h) : ℕ) : ℤ) := by
  rw [support_line]
  simp only [Nat.cast_mul, shapeSum, Nat.cast_sum, supportSum, intShapeSum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sum_le_sum
  intro q _
  apply sum_le_sum
  intro j _
  split_ifs
  · exact signedWidth_le h q j hh
  · positivity
theorem cert_twice_index (n : ℕ) :
    2 * (∑ j ∈ range n, (j : ℤ)) = (n : ℤ)*((n : ℤ)-1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, mul_add, ih, Nat.cast_succ]; ring
def certDivPrefix (n : ℕ) : ℤ :=
  let k : ℤ := (n/5 : ℕ)
  let r : ℤ := (n%5 : ℕ)
  5*k*(k-1) + 2*k*r
theorem cert_div_prefix_step (n : ℕ) :
    certDivPrefix (n+1) = certDivPrefix n + 2 * ((n/5 : ℕ) : ℤ) := by
  by_cases h : n%5 = 4
  · have hd : (n+1)/5 = n/5+1 := by omega
    have hr : (n+1)%5 = 0 := by omega
    simp only [certDivPrefix, hd, hr, h, Nat.cast_add, Nat.cast_ofNat, Nat.cast_zero]
    ring
  · have hd : (n+1)/5 = n/5 := by omega
    have hr : (n+1)%5 = n%5+1 := by omega
    simp only [certDivPrefix, hd, hr, Nat.cast_add]
    ring
theorem cert_twice_desc_div (q n : ℕ) (hn : n ≤ q+1) :
    2 * (∑ j ∈ range n, (((q-j)/5 : ℕ) : ℤ)) =
      certDivPrefix (q+1) - certDivPrefix (q+1-n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih (by omega)]
    have hs : q+1-n = q-n+1 := by omega
    have ht : q+1-(n+1) = q-n := by omega
    rw [hs, ht, cert_div_prefix_step (q-n)]
    ring
def certSlopeRow (q n : ℕ) : ℤ :=
  2 * (n : ℤ) * q - 2 * (n : ℤ) * ((n : ℤ)-1) -
    2 * (certDivPrefix (q+1) - certDivPrefix (q+1-n))
theorem cert_slope_row (q n : ℕ) (hn : n ≤ q+1) :
    2 * (∑ j ∈ range n, widthSlope q j) = certSlopeRow q n := by
  calc
    _ = 2 * (n : ℤ) * q - 2 * (2 * (∑ j ∈ range n, (j : ℤ))) -
          2 * (2 * (∑ j ∈ range n, (((q-j)/5 : ℕ) : ℤ))) := by
      simp only [widthSlope, sum_sub_distrib, ← mul_sum, sum_add_distrib,
        sum_const, card_range, nsmul_eq_mul]
      ring
    _ = _ := by rw [cert_twice_index, cert_twice_desc_div q n hn]; unfold certSlopeRow; ring
def certBaseRow (q n : ℕ) : ℤ :=
  2 * (n : ℤ) * ((fullShape.m : ℤ)*180265 - q*131071) +
    (n : ℤ)*((n : ℤ)-1) + 3555 * certSlopeRow q n
theorem cert_base_row (q n : ℕ) (hn : n ≤ q+1) :
    2 * (∑ j ∈ range n, signedWidth 3555 q j) = certBaseRow q n := by
  calc
    _ = 2 * (n : ℤ) * ((fullShape.m : ℤ)*180265 - q*131071) +
          2 * (∑ j ∈ range n, (j : ℤ)) +
          3555 * (2 * (∑ j ∈ range n, widthSlope q j)) := by
      simp only [signedWidth, sum_sub_distrib, ← mul_sum, sum_add_distrib,
        sum_const, card_range, nsmul_eq_mul]
      ring
    _ = _ := by rw [cert_twice_index, cert_slope_row q n hn]; rfl
theorem cert_full_support (q j : ℕ) (hq : q < 496)
    (hj : j < min q fullShape.J+1) : 0 < signedWidth 3555 q j := by
  have hjq := (Nat.le_of_lt_succ hj).trans (min_le_left _ _)
  have hjmax : j ≤ 105 := (Nat.le_of_lt_succ hj).trans (min_le_right _ _)
  have hd : 5 * ((q-j)/5) ≤ q-j := Nat.mul_div_le _ _
  unfold signedWidth widthSlope
  change 0 < (358 : ℤ)*180265 + j - q*131071 +
    3555 * ((q : ℤ) - 2 * (j + (((q-j)/5 : ℕ) : ℤ)))
  omega
def certRowLength (q : ℕ) : ℕ := min q fullShape.J+1
def certKeptRow (f : ℕ → ℕ → ℤ) (q : ℕ) : ℤ :=
  ∑ j ∈ range (certRowLength q), if 0 < signedWidth 3555 q j then f q j else 0
theorem cert_sum_split {α : Type} [AddCommMonoid α] (f : ℕ → α) (m n : ℕ) :
    (∑ q ∈ range (m+n), f q) = (∑ q ∈ range m, f q) + ∑ q ∈ range n, f (m+q) := by
  simpa only [Nat.add_comm] using sum_range_add f m n
theorem cert_twice_support (f : ℕ → ℕ → ℤ) (row : ℕ → ℤ)
    (hrow : ∀ q, 2 * (∑ j ∈ range (certRowLength q), f q j) = row q) :
    2 * supportSum f = (∑ q ∈ range 496, row q) +
      2 * (∑ q ∈ range 5, certKeptRow f (496+q)) := by
  change 2 * (∑ q ∈ range (496+5), certKeptRow f q) = _
  rw [cert_sum_split _ 496 5, mul_add]
  refine congrArg (fun s : ℤ => s + 2 * (∑ q ∈ range 5, certKeptRow f (496+q))) ?_
  rw [mul_sum]
  apply sum_congr rfl
  intro q hq
  rw [← hrow q]
  refine congrArg (fun s : ℤ => 2 * s) ?_
  apply sum_congr rfl
  intro j hj
  exact ite_eq_left (cert_full_support q j (mem_range.mp hq) (mem_range.mp hj))
def certNodeProgression (n d : ℕ) : ℕ :=
  let k := min n ((d+1)/2)
  k*(d+1-k)
theorem cert_node_progression (n d : ℕ) :
    (∑ j ∈ range n, (d-2*j)) = certNodeProgression n d := by
  let k := min n ((d+1)/2)
  have hk : k ≤ (d+1)/2 := min_le_right _ _
  have htrim : (∑ j ∈ range n, (d-2*j)) = ∑ j ∈ range k, (d-2*j) := by
    symm
    apply sum_subset (range_mono (min_le_left _ _))
    intro j hj hjk
    have h1 := mem_range.mp hj
    have h2 : k ≤ j := Nat.le_of_not_gt fun h => hjk (mem_range.mpr h)
    dsimp [k] at h2
    omega
  have hcast : ((∑ j ∈ range k, (d-2*j) : ℕ) : ℤ) =
      ∑ j ∈ range k, ((d : ℤ)-2*(j : ℤ)) := by
    rw [Nat.cast_sum]
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    rw [Nat.cast_sub (by omega : 2*j ≤ d)]
    push_cast
    rfl
  apply Int.ofNat_inj.mp
  change _ = (↑(k*(d+1-k)) : ℤ)
  rw [htrim, hcast, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum,
    cert_twice_index]
  push_cast [Nat.cast_sub (show k ≤ d+1 by omega)]
  ring
def certNodeRow (s : Shape) (q : ℕ) : ℕ :=
  certNodeProgression (min q s.J+1) (s.m + min q s.J - q)
def certPoleRow (s : Shape) (q : ℕ) : ℕ :=
  (min q s.J+1) * ((s.B+s.J-q)*(s.B-q))
theorem cert_node_shape (s : Shape) :
    nodeDebitOf s = triangle s.U * 262144 * (∑ q ∈ range (s.B+1), certNodeRow s q) := by
  unfold nodeDebitOf shapeSum
  refine congrArg (fun n : ℕ => triangle s.U * 262144 * n) ?_
  apply sum_congr rfl
  intro q _
  simpa only [certNodeRow, Nat.sub_sub] using
    cert_node_progression (min q s.J+1) (s.m+min q s.J-q)
theorem cert_pole_shape (s : Shape) :
    poleSlopeOf s = 2*(s.U+1) * (∑ q ∈ range (s.B+1), certPoleRow s q) := by
  simp only [poleSlopeOf, shapeSum, certPoleRow, sum_const, card_range, Nat.nsmul_eq_mul]
theorem cert_full_range {α : Type} [AddCommMonoid α] (row : ℕ → α) :
    (∑ q ∈ range (fullShape.B+1), row q) = (∑ q ∈ range 501, row q) :=
  congrArg (fun n : ℕ => ∑ q ∈ range n, row q) (show fullShape.B+1 = 501 from rfl)
theorem cert_node_rewrite :
    nodeDebit = triangle fullShape.U * 262144 * (∑ q ∈ range 501, certNodeRow fullShape q) :=
  (cert_node_shape fullShape).trans
    (congrArg (fun n : ℕ => triangle fullShape.U * 262144 * n)
      (cert_full_range (certNodeRow fullShape)))
theorem cert_pole_rewrite :
    poleSlope = 2*(fullShape.U+1) * (∑ q ∈ range 501, certPoleRow fullShape q) :=
  (cert_pole_shape fullShape).trans
    (congrArg (fun n : ℕ => 2*(fullShape.U+1) * n)
      (cert_full_range (certPoleRow fullShape)))
def certFullBaseRow (q : ℕ) : ℤ := certBaseRow q (certRowLength q)
def certFullSlopeRow (q : ℕ) : ℤ := certSlopeRow q (certRowLength q)
theorem cert_sum_append {α : Type} [AddCommMonoid α]
    (f : ℕ → α) (m n k : ℕ) (hk : m+n = k) {a b : α}
    (ha : (∑ q ∈ range m, f q) = a)
    (hb : (∑ q ∈ range n, f (m+q)) = b) :
    (∑ q ∈ range k, f q) = a+b :=
  (congrArg (fun s : ℕ => ∑ q ∈ range s, f q) hk.symm).trans
    ((cert_sum_split f m n).trans (congrArg₂ (· + ·) ha hb))
section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem cert_node_000 :
    (∑ q ∈ range 125, certNodeRow fullShape q) = 2122650 := by
  decide +kernel
theorem cert_node_125 :
    (∑ q ∈ range 125, certNodeRow fullShape (125+q)) = 2265750 := by
  decide +kernel
theorem cert_node_250 :
    (∑ q ∈ range 125, certNodeRow fullShape (250+q)) = 762671 := by
  decide +kernel
theorem cert_node_375 :
    (∑ q ∈ range 125, certNodeRow fullShape (375+q)) = 59730 := by
  decide +kernel
theorem cert_node_500 :
    (∑ q ∈ range 1, certNodeRow fullShape (500+q)) = 0 := by
  decide +kernel
theorem cert_pole_000 :
    (∑ q ∈ range 125, certPoleRow fullShape q) = 1688187800 := by
  decide +kernel
theorem cert_pole_125 :
    (∑ q ∈ range 125, certPoleRow fullShape (125+q)) = 1750802000 := by
  decide +kernel
theorem cert_pole_250 :
    (∑ q ∈ range 125, certPoleRow fullShape (250+q)) = 747114500 := by
  decide +kernel
theorem cert_pole_375 :
    (∑ q ∈ range 125, certPoleRow fullShape (375+q)) = 157489500 := by
  decide +kernel
theorem cert_pole_500 :
    (∑ q ∈ range 1, certPoleRow fullShape (500+q)) = 0 := by
  decide +kernel
theorem cert_base_000 :
    (∑ q ∈ range 124, certFullBaseRow q) = 816158989978 := by
  decide +kernel
theorem cert_base_124 :
    (∑ q ∈ range 124, certFullBaseRow (124+q)) = 1059962322636 := by
  decide +kernel
theorem cert_base_248 :
    (∑ q ∈ range 124, certFullBaseRow (248+q)) = 639661579624 := by
  decide +kernel
theorem cert_base_372 :
    (∑ q ∈ range 124, certFullBaseRow (372+q)) = 219360836612 := by
  decide +kernel
theorem cert_slope_000 :
    (∑ q ∈ range 124, certFullSlopeRow q) = -205216 := by
  decide +kernel
theorem cert_slope_124 :
    (∑ q ∈ range 124, certFullSlopeRow (124+q)) = 738692 := by
  decide +kernel
theorem cert_slope_248 :
    (∑ q ∈ range 124, certFullSlopeRow (248+q)) = 2694520 := by
  decide +kernel
theorem cert_slope_372 :
    (∑ q ∈ range 124, certFullSlopeRow (372+q)) = 4650348 := by
  decide +kernel
theorem cert_base_tail :
    (∑ q ∈ range 5, certKeptRow (signedWidth 3555) (496+q)) = 62325013 := by
  decide +kernel
theorem cert_slope_tail :
    (∑ q ∈ range 5, certKeptRow (widthSlope) (496+q)) = 69817 := by
  decide +kernel
end
theorem cert_node_total :
    (∑ q ∈ range 501, certNodeRow fullShape q) = 5210801 := by
  have h250 := cert_sum_append (certNodeRow fullShape) 125 125 250 (by rfl) cert_node_000 cert_node_125
  have h375 := cert_sum_append (certNodeRow fullShape) 250 125 375 (by rfl) h250 cert_node_250
  have h500 := cert_sum_append (certNodeRow fullShape) 375 125 500 (by rfl) h375 cert_node_375
  exact cert_sum_append (certNodeRow fullShape) 500 1 501 (by rfl) h500 cert_node_500
theorem cert_pole_total :
    (∑ q ∈ range 501, certPoleRow fullShape q) = 4343593800 := by
  have h250 := cert_sum_append (certPoleRow fullShape) 125 125 250 (by rfl) cert_pole_000 cert_pole_125
  have h375 := cert_sum_append (certPoleRow fullShape) 250 125 375 (by rfl) h250 cert_pole_250
  have h500 := cert_sum_append (certPoleRow fullShape) 375 125 500 (by rfl) h375 cert_pole_375
  exact cert_sum_append (certPoleRow fullShape) 500 1 501 (by rfl) h500 cert_pole_500
theorem cert_base_total :
    (∑ q ∈ range 496, certFullBaseRow q) = 2735143728850 := by
  have h248 := cert_sum_append certFullBaseRow 124 124 248 (by rfl) cert_base_000 cert_base_124
  have h372 := cert_sum_append certFullBaseRow 248 124 372 (by rfl) h248 cert_base_248
  exact cert_sum_append certFullBaseRow 372 124 496 (by rfl) h372 cert_base_372
theorem cert_slope_total :
    (∑ q ∈ range 496, certFullSlopeRow q) = 7878344 := by
  have h248 := cert_sum_append certFullSlopeRow 124 124 248 (by rfl) cert_slope_000 cert_slope_124
  have h372 := cert_sum_append certFullSlopeRow 248 124 372 (by rfl) h248 cert_slope_248
  exact cert_sum_append certFullSlopeRow 372 124 496 (by rfl) h372 cert_slope_372
theorem cert_base_value : supportBase = 3001542485805639174564 := by
  have h := cert_twice_support (signedWidth 3555) certFullBaseRow
    (fun q => cert_base_row q _ (Nat.succ_le_succ (min_le_left _ _)))
  rw [cert_base_total, cert_base_tail] at h
  have hsum : supportSum (signedWidth 3555) = 1367634189438 := by omega
  rw [supportBase, hsum]
  rfl
theorem cert_slope_value : supportSlope = 8798515642236342 := by
  have h := cert_twice_support widthSlope certFullSlopeRow
    (fun q => cert_slope_row q _ (Nat.succ_le_succ (min_le_left _ _)))
  rw [cert_slope_total, cert_slope_tail] at h
  have hsum : supportSum widthSlope = 4008989 := by omega
  rw [supportSlope, hsum]
  rfl
theorem support_left :
    (nodeDebit : ℤ) + 3555 * (poleSlope : ℤ) < supportBase := by
  rw [cert_node_rewrite, cert_node_total, cert_pole_rewrite, cert_pole_total, cert_base_value]
  decide +kernel
theorem support_rises : (poleSlope : ℤ) ≤ supportSlope := by
  rw [cert_pole_rewrite, cert_pole_total, cert_slope_value]
  decide +kernel
theorem debit_lt_loss (h : ℕ) (hl : 3555 ≤ h) (hu : h ≤ 32680) :
    sourceDebit h fullShape < triangle fullShape.U * shapeSum fullShape (lostWidth h) := by
  have hstep : (0 : ℤ) ≤ (h : ℤ)-3555 := by omega
  have hslope := mul_le_mul_of_nonneg_left support_rises hstep
  apply Int.ofNat_lt.mp
  calc
    (sourceDebit h fullShape : ℤ) =
        (nodeDebit : ℤ) + 3555 * (poleSlope : ℤ) + ((h : ℤ)-3555) * (poleSlope : ℤ) := by
      rw [debit_eq]
      push_cast
      ring
    _ < supportBase + ((h : ℤ)-3555)*supportSlope :=
      add_lt_add_of_lt_of_le support_left hslope
    _ ≤ _ := support_le h (by omega)
end K1_14_3_8
end
section
namespace K1_14_3_8
noncomputable section
open K1_14 K1_14_3 Polynomial
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
def Allowed (h W q j : ℕ) : Prop :=
  q * (131071 - h) ≤ W + j ∧ contactPower h fullShape W ≤ j + (q-j)/5
instance (h W q j : ℕ) : Decidable (Allowed h W q j) := by
  unfold Allowed
  infer_instance
private abbrev SeedIndex (U : ℕ) := Σ t : Fin (U+1), Fin (t.val+1)
private def seedExponent {U : ℕ} (b : SeedIndex U) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![b.1.val-b.2.val, b.2.val]
private theorem exists_seedIndex {U : ℕ} (a : Seeds) {e : Fin 2 →₀ ℕ}
    (he : AddMonoidAlgebra.coeff a e ≠ 0) (hU : a.totalDegree ≤ U) :
    ∃ b : SeedIndex U, seedExponent b = e := by
  have ht := (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr he)).trans hU
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at ht
  let t : Fin (U+1) := ⟨e 0 + e 1, by omega⟩
  let b : Fin (t.val+1) := ⟨e 1, by dsimp [t]; omega⟩
  refine ⟨⟨t,b⟩, Finsupp.ext fun k => ?_⟩
  fin_cases k <;> simp [seedExponent, t, b]
private theorem card_seedIndex (U : ℕ) : Fintype.card (SeedIndex U) = triangle U := by
  simp only [SeedIndex, Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => t + 1)]
  have hsum := Finset.sum_range_succ' (fun t : ℕ => t) (U + 1)
  simp only [add_zero] at hsum
  rw [← hsum]
  simp [Finset.sum_range_id, triangle, Nat.mul_comm]
private abbrev Coordinate (h W : ℕ) :=
  Σ q : Fin (fullShape.B+1), Σ j : Fin (min q.val fullShape.J+1),
    Fin (if Allowed h W q.val j.val then 1 else 0) × SeedIndex fullShape.U
private def coordinates (h W : ℕ) (V : Submodule FX Jet) :
    V →ₗ[FX] (Coordinate h W → FX) where
  toFun P k := AddMonoidAlgebra.coeff
    ((P.val.coeff k.2.1.val).coeff (k.1.val-k.2.1.val)) (seedExponent k.2.2.2)
  map_add' P Q := by
    funext k
    simp [Polynomial.coeff_add]
  map_smul' a P := by
    funext k
    simp [Polynomial.coeff_smul]
theorem card_coordinates (h W : ℕ) :
    Fintype.card (Coordinate h W) =
      triangle fullShape.U * shapeSum fullShape (fun q j => if Allowed h W q j then 1 else 0) := by
  have hcard : Fintype.card (Coordinate h W) =
      ∑ q : Fin (fullShape.B+1), ∑ j : Fin (min q.val fullShape.J+1),
        triangle fullShape.U * (if Allowed h W q.val j.val then 1 else 0) := by
    unfold Coordinate
    rw [Fintype.card_sigma]
    apply Finset.sum_congr rfl
    intro q _
    rw [Fintype.card_sigma]
    apply Finset.sum_congr rfl
    intro j _
    rw [Fintype.card_prod, card_seedIndex, Fintype.card_fin, Nat.mul_comm]
  rw [hcard]
  unfold shapeSum
  simp only [Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun q => ∑ j : Fin (min q fullShape.J+1),
    triangle fullShape.U * (if Allowed h W q j then 1 else 0))]
  apply Finset.sum_congr rfl
  intro q _
  exact Fin.sum_univ_eq_sum_range
    (fun j => triangle fullShape.U * (if Allowed h W q j then 1 else 0)) _
theorem cutoff_finrank_le (h W : ℕ) (V : Submodule FX Jet)
    (hcaps : ∀ P ∈ V, RowCaps P fullShape)
    (hlead : ∀ P ∈ V, P ≠ 0 →
      (P.leadingCoeff.natDegree + P.natDegree) * (131071-h) ≤ W + P.natDegree)
    (hfive : ∀ P ∈ V, P ≠ 0 →
      5 * (contactPower h fullShape W - P.natDegree) ≤ P.leadingCoeff.natDegree) :
    Module.finrank FX V ≤
      triangle fullShape.U * shapeSum fullShape (fun q j => if Allowed h W q j then 1 else 0) := by
  rw [← card_coordinates, ← Module.finrank_fintype_fun_eq_card FX]
  apply (coordinates h W V).finrank_le_finrank_of_injective
  apply (LinearMap.ker_eq_bot.mp ?_)
  apply bot_unique
  intro P hp
  by_contra hne
  have hn : P.val ≠ 0 := by
    intro hz
    rw [Submodule.mem_bot] at hne
    exact hne (Subtype.ext hz)
  let j := P.val.natDegree
  let i := P.val.leadingCoeff.natDegree
  let a := (P.val.coeff j).coeff i
  have ha : a ≠ 0 := by
    change (P.val.coeff P.val.natDegree).coeff P.val.leadingCoeff.natDegree ≠ 0
    rw [coeff_natDegree, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn)
  obtain ⟨hB, hJ, hU⟩ := hcaps _ P.property j i ha
  have hwidth : (i+j) * (131071-h) ≤ W+j := hlead _ P.property hn
  have horder : 5 * (contactPower h fullShape W - j) ≤ i := hfive _ P.property hn
  let q : Fin (fullShape.B+1) := ⟨i+j, Nat.lt_succ_of_le hB⟩
  let v : Fin (min q.val fullShape.J+1) :=
    ⟨j, Nat.lt_succ_of_le (le_min (by dsimp [q]; omega) hJ)⟩
  have hel : Allowed h W q.val v.val := by
    change (i+j) * (131071-h) ≤ W+j ∧ contactPower h fullShape W ≤ j + (i+j-j)/5
    exact ⟨hwidth, by omega⟩
  obtain ⟨e, he⟩ : ∃ e, AddMonoidAlgebra.coeff a e ≠ 0 := by
    contrapose! ha
    apply MvPolynomial.ext
    intro e
    simpa using ha e
  obtain ⟨b, hb⟩ := exists_seedIndex a he hU
  let k : Coordinate h W := ⟨q, v, ⟨0, by simp [hel]⟩, b⟩
  have hz := congrFun (LinearMap.mem_ker.mp hp) k
  change AddMonoidAlgebra.coeff ((P.val.coeff j).coeff (i+j-j)) (seedExponent b) = 0 at hz
  rw [hb, Nat.add_sub_cancel] at hz
  exact he hz
end
end K1_14_3_8
end
section
namespace K1_14_3_8
open K1_14 K1_14_3 Finset Polynomial
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
private theorem cutoff_interval_card (top j t d : ℕ) (hj : j ≤ t) :
    (∑ W ∈ range top, if t ≤ W+j ∧ W+d < top then 1 else 0) = top+j-t-d := by
  rw [← card_filter]
  have hr : (range top).filter (fun W => t ≤ W+j ∧ W+d < top) =
      Ico (t-j) (top-d) := by
    ext W
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [hr, Nat.card_Ico]
  omega
theorem contact_le_iff (h W n : ℕ) (hh : 0 < 2*h)
    (hW : W < fullShape.m*180265) :
    contactPower h fullShape W ≤ n ↔ fullShape.m*180265 ≤ W + 2*h*n := by
  unfold contactPower
  rw [show (1 + (fullShape.m*180265-1-W)/(2*h) ≤ n) ↔
      (fullShape.m*180265-1-W)/(2*h) < n by omega,
    Nat.div_lt_iff_lt_mul hh, Nat.mul_comm n (2*h)]
  omega
private theorem position_sum (h q j : ℕ) (hh : 0 < 2*h) (hj : j ≤ q*(131071-h)) :
    (∑ W ∈ range (fullShape.m*180265), if Allowed h W q j then 1 else 0) +
      lostWidth h q j = fullShape.m*180265+j-q*(131071-h) := by
  let top := fullShape.m*180265
  let t := q*(131071-h)
  let d := 2*h*(j+(q-j)/5)
  change (∑ W ∈ range top, if Allowed h W q j then 1 else 0) +
    (top+j-t-d) = top+j-t
  rw [← cutoff_interval_card top j t d hj, ← sum_add_distrib]
  have hraw := cutoff_interval_card top j t 0 hj
  rw [Nat.sub_zero] at hraw
  rw [← hraw]
  apply sum_congr rfl
  intro W hW
  have hw := mem_range.mp hW
  have hel : Allowed h W q j ↔ t ≤ W+j ∧ top ≤ W+d :=
    and_congr_right fun _ => contact_le_iff h W _ hh hw
  by_cases ht : t ≤ W+j
  · by_cases hcut : W+d < top
    · have ha : ¬ Allowed h W q j := fun ha => (Nat.not_le_of_lt hcut) (hel.mp ha).2
      simp [ha, ht, hcut, hw]
    · have ha : Allowed h W q j := hel.mpr ⟨ht, Nat.le_of_not_gt hcut⟩
      simp [ha, ht, hcut, hw]
  · have ha : ¬ Allowed h W q j := fun ha => ht (hel.mp ha).1
    simp [ha, ht]
private theorem cutoff_total (h : ℕ) (hh : 0 < 2*h) (hk : 1 ≤ 131071-h) :
    (∑ W ∈ range (fullShape.m*180265),
      shapeSum fullShape (fun q j => if Allowed h W q j then 1 else 0)) +
      shapeSum fullShape (lostWidth h) =
      shapeSum fullShape (fun q j => fullShape.m*180265+j-q*(131071-h)) := by
  have hswap :
      (∑ W ∈ range (fullShape.m*180265),
        shapeSum fullShape (fun q j => if Allowed h W q j then 1 else 0)) =
      shapeSum fullShape (fun q j => ∑ W ∈ range (fullShape.m*180265),
        if Allowed h W q j then 1 else 0) := by
    unfold shapeSum
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    rw [sum_comm]
  rw [hswap]
  simp only [shapeSum, ← sum_add_distrib]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro j hj
  have hjq : j ≤ q := (Nat.le_of_lt_succ (mem_range.mp hj)).trans (min_le_left _ _)
  have hq : q ≤ q*(131071-h) := by simpa using Nat.mul_le_mul_left q hk
  exact position_sum h q j hh (hjq.trans hq)
theorem proof : K1_14_3.c8 := by
  intro h rows hl hu hcaps hlead hfloor
  by_contra hbad
  let top := fullShape.m*180265
  have htop : top = 64534870 := rfl
  have htopSub : top-1+1 = top := by omega
  have hwidth : ∀ q ≤ fullShape.B, ∀ j ≤ min q fullShape.J,
      q*(131071-h) ≤ top-1+1+j := by
    intro q hq j _
    have hq' : q ≤ 500 := hq
    have hm := Nat.mul_le_mul hq' (show 131071-h ≤ 127516 by omega)
    omega
  have hmin := hfloor (top-1) (by omega) hwidth
  change triangle fullShape.U *
    shapeSum fullShape (fun q j => top-1+1+j-q*(131071-h)) ≤
      sourceDebit h fullShape + ∑ W ∈ range (top-1+1), Module.finrank FX (rows fullShape W)
    at hmin
  rw [htopSub] at hmin
  have hfive : ∀ W < top, ∀ P ∈ rows fullShape W, P ≠ 0 →
      5*(contactPower h fullShape W-P.natDegree) ≤ P.leadingCoeff.natDegree := by
    intro W hW P hP hn
    by_contra! hsmall
    exact hbad ⟨W,hW,P,hP,hn,hsmall⟩
  have hmax : (∑ W ∈ range top, Module.finrank FX (rows fullShape W)) ≤
      triangle fullShape.U *
      (∑ W ∈ range top, shapeSum fullShape (fun q j => if Allowed h W q j then 1 else 0)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro W hW
    exact cutoff_finrank_le h W _ (hcaps W) (hlead W) (hfive W (mem_range.mp hW))
  have hcount := congrArg (triangle fullShape.U * ·) (cutoff_total h (by omega) (by omega))
  rw [Nat.mul_add] at hcount
  have hstrict := debit_lt_loss h hl hu
  change triangle fullShape.U *
    (∑ W ∈ range top, shapeSum fullShape (fun q j => if Allowed h W q j then 1 else 0)) +
      triangle fullShape.U * shapeSum fullShape (lostWidth h) =
      triangle fullShape.U * shapeSum fullShape (fun q j => top+j-q*(131071-h)) at hcount
  omega
end K1_14_3_8
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace K1_6
open K1 Polynomial
open FrobeniusLocator ProximityPrize.Benchmark
private theorem lift_common_divisor {G : Frac[X]} {U V : Bivar} (hG : G ≠ 0)
    (hU : G ∣ extendSeed U) (hV : G ∣ extendSeed V) :
    ∃ D : Bivar, D ≠ 0 ∧ G.natDegree ≤ D.natDegree ∧ D ∣ U ∧ D ∣ V := by
  let φ : K[X] →+* Frac := algebraMap K[X] Frac
  have hφ : Function.Injective φ := IsFractionRing.injective K[X] Frac
  let Q : Bivar := IsLocalization.integerNormalization (nonZeroDivisors K[X]) G
  let D := Q.primPart
  obtain ⟨a, ha, hQ⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors K[X]) G
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hscale : C (φ Q.content) * D.map φ = C (φ a) * G := by
    calc
      C (φ Q.content) * D.map φ = Q.map φ := by
        rw [← Polynomial.map_C, ← Polynomial.map_mul, ← Q.eq_C_content_mul_primPart]
      _ = C (φ a) * G := by
        simpa only [Algebra.smul_def, Polynomial.algebraMap_apply] using hQ
  have hscale0 : C (φ a) * G ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr (fun hz => ha0 (hφ (hz.trans (map_zero φ).symm)))) hG
  have hDmap : D.map φ ≠ 0 := by
    intro hz
    exact hscale0 (by rw [← hscale, hz, mul_zero])
  have hcontent : φ Q.content ≠ 0 := by
    intro hz
    exact hscale0 (by rw [← hscale, hz, map_zero, zero_mul])
  have hD : D ≠ 0 := fun hz => hDmap (by rw [hz, Polynomial.map_zero])
  have hGtoD : G ∣ D.map φ := by
    apply (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcontent)).dvd_mul_left.mp
    rw [hscale]
    exact dvd_mul_left _ _
  have hDtoG : D.map φ ∣ G := by
    have ha' : φ a ≠ 0 := fun hz => ha0 (hφ (hz.trans (map_zero φ).symm))
    apply (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha')).dvd_mul_left.mp
    rw [← hscale]
    exact dvd_mul_left _ _
  have hdeg := natDegree_le_of_dvd hGtoD hDmap
  rw [natDegree_map_eq_of_injective hφ] at hdeg
  exact ⟨D, hD, hdeg,
    Q.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map (hDtoG.trans hU),
    Q.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map (hDtoG.trans hV)⟩
private theorem specialize_factor {D P A : Bivar} {γ : K} (hD : D ≠ 0)
    (hP : P = D * A) (hγ : atSlope P γ ≠ 0) :
    atSlope P γ = atSlope D γ * atSlope A γ ∧
      (atSlope P γ).natDegree + D.natDegree ≤ P.natDegree + (atSlope D γ).natDegree := by
  have heq : atSlope P γ = atSlope D γ * atSlope A γ := by rw [hP, atSlope, Polynomial.map_mul]; rfl
  have hDγ : atSlope D γ ≠ 0 := by
    intro hz
    exact hγ (by rw [heq, hz, zero_mul])
  have hAγ : atSlope A γ ≠ 0 := by
    intro hz
    exact hγ (by rw [heq, hz, mul_zero])
  have hA : A ≠ 0 := fun hz => hAγ (by rw [hz, atSlope, Polynomial.map_zero])
  refine ⟨heq, ?_⟩
  have hdeg : (atSlope A γ).natDegree ≤ A.natDegree := natDegree_map_le
  rw [heq, natDegree_mul hDγ hAγ, hP, natDegree_mul hD hA]
  omega
private theorem eval_atSlope (P : Bivar) (γ x : K) :
    (atSlope P γ).eval x = (P.eval (C x)).eval γ := by
  simpa only [atSlope, coe_evalRingHom, eval_C] using
    (Polynomial.eval_map_apply (evalRingHom γ) (C x) (p := P))
private theorem root_outside_of_dvd_locator {F ι : Type} [Field F] [Fintype ι]
    [DecidableEq ι] (x : ι → F) (hx : Function.Injective x) (errors fixed : Finset ι) (D : F[X])
    (hD : D ∣ locator x errors) (hdeg : fixed.card < D.natDegree) :
    ∃ i ∉ fixed, D.eval (x i) = 0 := by
  classical
  let S := Finset.univ.filter (fun i : ι => D.eval (x i) = 0)
  have hcard : D.natDegree = S.card := Principal.divisor_domain_roots x hx errors D hD
  have hNot : ¬ S ⊆ fixed := fun h => by
    have := Finset.card_le_card h
    omega
  obtain ⟨i, hiS, hiFixed⟩ := Finset.not_subset.mp hNot
  exact ⟨i, hiFixed, (Finset.mem_filter.mp hiS).2⟩
theorem moving_has_new_node {u : Words} {T : TwoActive u} (R : Relation T)
    (hMoving : MovingGCD R) {γ : K} {M : BadMark u γ} (hSat : SaturatedAt R M) :
    ∃ i ∉ fixedNodes R,
      (atSlope (leftU R) γ).eval (node i) = 0 ∧ (atSlope (leftV R) γ).eval (node i) = 0 := by
  classical
  obtain ⟨G, hG, hGU, hGV, hg⟩ := hMoving.2
  obtain ⟨D, hD, hd, hDU, hDV⟩ := lift_common_divisor hG hGU hGV
  obtain ⟨A, hA⟩ := hDU
  obtain ⟨B, hB⟩ := hDV
  obtain ⟨hAU, hAUdeg⟩ := specialize_factor hD hA hSat.U_ne
  obtain ⟨hBV, hBVdeg⟩ := specialize_factor hD hB hSat.V_ne
  have hdeg : D.natDegree ≤ (atSlope D γ).natDegree := by
    have hU := R.x_degree 0
    have hV := R.x_degree 1
    change (leftU R).natDegree ≤ T.height at hU
    change (leftV R).natDegree ≤ T.height at hV
    have hMax := hSat.degree_eq
    rcases le_total (atSlope (leftU R) γ).natDegree (atSlope (leftV R) γ).natDegree with h | h
    · rw [max_eq_right h] at hMax
      omega
    · rw [max_eq_left h] at hMax
      omega
  obtain ⟨errors, _, hGCD⟩ := hSat.gcd_errors
  have hDvd := hGCD.2.2.2 (atSlope D γ) ⟨atSlope A γ, hAU⟩ ⟨atSlope B γ, hBV⟩
  have hCard : (fixedNodes R).card < (atSlope D γ).natDegree := by omega
  obtain ⟨i, hiFixed, hi⟩ := root_outside_of_dvd_locator (F := K) (ι := I)
    node IRSProfile.domain.injective errors (fixedNodes R) (atSlope D γ) hDvd hCard
  exact ⟨i, hiFixed, by rw [hAU, eval_mul, hi, zero_mul], by rw [hBV, eval_mul, hi, zero_mul]⟩
private theorem common_node_count {F ι : Type} [Field F] [Fintype ι]
    (U V : ι → F[X]) (H : ℕ) (Γ : Finset F)
    (hU : ∀ i, (U i).natDegree ≤ H) (hV : ∀ i, (V i).natDegree ≤ H)
    (hNew : ∀ γ ∈ Γ, ∃ i, ¬ (U i = 0 ∧ V i = 0) ∧ (U i).eval γ = 0 ∧ (V i).eval γ = 0) :
    Γ.card ≤ Fintype.card ι * H := by
  classical
  let Q (i : ι) := if U i = 0 then V i else U i
  have hCover : Γ ⊆ (Finset.univ : Finset ι).biUnion (fun i => (Q i).roots.toFinset) := by
    intro γ hγ
    obtain ⟨i, hNZ, hu, hv⟩ := hNew γ hγ
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩
    rw [Multiset.mem_toFinset]
    by_cases h : U i = 0
    · rw [show Q i = V i by simp [Q, h]]
      exact (mem_roots (fun hz => hNZ ⟨h, hz⟩)).mpr hv
    · rw [show Q i = U i by simp [Q, h]]
      exact (mem_roots h).mpr hu
  refine (Finset.card_le_card hCover).trans
    ((Finset.card_biUnion_le_card_mul _ _ H ?_).trans_eq (by rw [Finset.card_univ]))
  intro i _
  refine (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans ?_)
  change (if U i = 0 then V i else U i).natDegree ≤ H
  split_ifs
  · exact hV i
  · exact hU i
theorem k16Aux2_count_bound {c n n' H b : ℕ}
    (hn : n = n') (hc : c ≤ n * H) (hb : n' * H = b) : c ≤ b :=
  hb ▸ hn ▸ hc
theorem normal_growth_count {u : Words} {T : TwoActive u} (R : Relation T)
    (hHeight : ∀ i, (R.coefficients i).natDegree ≤ 6347474207)
    (hMoving : MovingGCD R) (hSat : NormalSaturation R) (Γ : Finset K)
    (hBad : BadFamily u Γ) (hNormal : ∀ γ ∈ Γ, Normal u γ) :
    Γ.card ≤ 1663952278519808 := by
  classical
  let U (i : I) := (leftU R).eval (C (node i))
  let V (i : I) := (leftV R).eval (C (node i))
  have hU (i) : (U i).natDegree ≤ 6347474207 := by
    dsimp only [U, leftU]
    rw [Strata.assemble_nodePolynomial]
    exact Principal.nodePolynomial_natDegree_le _ (fun j => hHeight (0, j)) _
  have hV (i) : (V i).natDegree ≤ 6347474207 := by
    dsimp only [V, leftV]
    rw [Strata.assemble_nodePolynomial]
    exact Principal.nodePolynomial_natDegree_le _ (fun j => hHeight (1, j)) _
  have hNew (γ : K) (hγ : γ ∈ Γ) :
      ∃ i, ¬ (U i = 0 ∧ V i = 0) ∧ (U i).eval γ = 0 ∧ (V i).eval γ = 0 := by
    refine (K1.bad_mark u Γ hBad γ hγ).elim (fun M => ?_)
    obtain ⟨i, hi, hu, hv⟩ := moving_has_new_node R hMoving (hSat γ (hNormal γ hγ) M)
    rw [eval_atSlope] at hu hv
    have hNZ : ¬ (U i = 0 ∧ V i = 0) := by
      simpa only [fixedNodes, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    exact ⟨i, hNZ, hu, hv⟩
  exact k16Aux2_count_bound (c := Γ.card) (n := Fintype.card I) (n' := 262144)
    (H := 6347474207) (b := 1663952278519808) IRSProfile.card_index
    (common_node_count U V 6347474207 Γ hU hV hNew) rfl
end K1_6
end
section
namespace K1_13_7_1
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_1 K1_13_6
theorem weight_le_of_support_subset {R S : Type*} [CommSemiring R] [CommSemiring S]
    (w : Fin 4 → ℕ) {P : MvPolynomial (Fin 4) R} {Q : MvPolynomial (Fin 4) S}
    (h : P.support ⊆ Q.support) :
    P.weightedTotalDegree w ≤ Q.weightedTotalDegree w :=
  Finset.sup_mono h
theorem weight_const_mul_le {R : Type*} [CommSemiring R] (w : Fin 4 → ℕ)
    (a : R) (P : MvPolynomial (Fin 4) R) :
    (MvPolynomial.C a * P).weightedTotalDegree w ≤ P.weightedTotalDegree w := by
  simpa only [weightedTotalDegree_C, zero_add] using
    weightedTotalDegree_mul_le w (MvPolynomial.C a) P
theorem weight_X_le {R : Type*} [CommSemiring R] (w : Fin 4 → ℕ) (i : Fin 4) :
    (MvPolynomial.X i : MvPolynomial (Fin 4) R).weightedTotalDegree w ≤ w i :=
  mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp (X_mem_restrictWeightedDegree _ _ _ le_rfl)
theorem TaylorChart.pullback_fits (C : TaylorChart) {h : Shape} (hC : C.Fits h) (a : AffineForm) :
    GeoFits (C.pullback a) h := by
  classical
  have hw (w : Fin 4 → ℕ) (d : ℕ) (hD : C.denom.weightedTotalDegree w ≤ d)
      (hN : ∀ i, (C.numerator i).weightedTotalDegree w ≤ d) :
      (C.pullback a).weightedTotalDegree w ≤ d := by
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply Submodule.add_mem
    · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        ((weight_const_mul_le _ _ _).trans hD)
    · apply Submodule.sum_mem
      intro i _
      exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        ((weight_const_mul_le _ _ _).trans (hN i))
  refine ⟨?_, hw Fin.val h.j hC.1.2.1 (fun i => (hC.2 i).2.1), ?_⟩
  · simpa only [weightedTotalDegree_one] using hw 1 h.b
      (by simpa only [weightedTotalDegree_one] using hC.1.1)
      (fun i => by simpa only [weightedTotalDegree_one] using (hC.2 i).1)
  · simpa only [weightedTotalDegree_piSingle] using hw (Pi.single (3 : Fin 4) 1) h.t
      (by simpa only [weightedTotalDegree_piSingle] using hC.1.2.2)
      (fun i => by simpa only [weightedTotalDegree_piSingle] using (hC.2 i).2.2)
theorem toGeneric_fits {P : Row 4} {p : Shape} (hP : InBox (shape P) p) :
    GeoFits (toGeneric P) p := by
  classical
  have hw (w : Fin 4 → ℕ) :=
    weight_le_of_support_subset w (MvPolynomial.support_map_subset genericCoeffs P)
  refine ⟨?_, ?_, ?_⟩
  · exact (by simpa only [toGeneric, weightedTotalDegree_one] using hw 1 :
      (toGeneric P).totalDegree ≤ P.totalDegree).trans hP.1
  · exact (hw Fin.val).trans (by simpa only [shape, indexDegree_eq] using hP.2.1)
  · exact (by simpa only [toGeneric, weightedTotalDegree_piSingle] using hw (Pi.single (3 : Fin 4) 1) :
      (toGeneric P).degreeOf 3 ≤ P.degreeOf 3).trans hP.2.2
theorem top_le_index {R : Type*} [CommSemiring R] (P : MvPolynomial (Fin 4) R) :
    3 * P.degreeOf 3 ≤ P.weightedTotalDegree Fin.val := by
  classical
  rw [MvPolynomial.degreeOf_eq_sup, Nat.mul_comm 3, ← Nat.le_div_iff_mul_le (by decide : 0 < 3)]
  apply Finset.sup_le
  intro m hm
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 3)]
  have h := Finsupp.apply_smul_le_weight (fun i : Fin 4 => i.val) m (3 : Fin 4)
  have hm' := le_weightedTotalDegree (fun i : Fin 4 => i.val) hm
  have hthree : (3 : Fin 4).val = 3 := rfl
  simpa only [smul_eq_mul, hthree, Nat.mul_comm] using h.trans hm'
theorem shape_chamber (P : Row 4) : Chamber (shape P).chamber := by
  refine ⟨le_max_right _ _, ?_⟩
  change 3 * P.degreeOf 3 ≤ indexDegree P
  rw [indexDegree_eq]
  exact top_le_index P
theorem chart_chamber (L : ℕ) (p : Shape) : Chamber (chart L p) := by
  let i := 2*L*(p.j - 3) + L + 3
  refine ⟨le_max_right _ _, ?_⟩
  change 3 * min _ (i / 3) ≤ i
  have h := min_le_right (2 * L * (p.t - 1) + L + 1) (i / 3)
  omega
end
end K1_13_7_1
end
section
namespace K1_13_7_1_1
noncomputable section
open K1_13 K1_13_6 K1_13_7_1 MvPolynomial
private def translate (a : GeoPoint) : GeoJets →ₐ[GeoField] GeoJets :=
  bind₁ (fun i => MvPolynomial.X i - C (a i))
theorem translate_inverse (a : GeoPoint) (f : GeoJets) :
    translate (-a) (translate a f) = f := by
  unfold translate
  rw [bind₁_bind₁]
  have hi (i : Fin 4) :
      bind₁ (fun j => MvPolynomial.X j - C ((-a) j)) (MvPolynomial.X i - C (a i)) = MvPolynomial.X i := by
    simp
  simp only [hi, bind₁_X_left, AlgHom.id_apply]
theorem eval_translate (a y : GeoPoint) (f : GeoJets) :
    eval (y + a) (translate a f) = eval y f := by
  change aeval (y + a) (bind₁ (fun i => MvPolynomial.X i - C (a i)) f) = aeval y f
  rw [aeval_bind₁]
  simp
theorem translate_fits (a : GeoPoint) {f : GeoJets} {p : Shape}
    (hf : GeoFits f p) : GeoFits (translate a f) p := by
  have hw (w : Fin 4 → ℕ) :
      (translate a f).weightedTotalDegree w ≤ f.weightedTotalDegree w := by
    apply weightedTotalDegree_bind₁_le_of_le w w
    intro i
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    exact Submodule.sub_mem _
      (X_mem_restrictWeightedDegree _ _ _ le_rfl)
      (C_mem_restrictWeightedDegree _ _ _)
  refine ⟨?_, (hw Fin.val).trans hf.2.1, ?_⟩
  · simpa only [weightedTotalDegree_one] using (hw 1).trans
      (show f.weightedTotalDegree 1 ≤ p.b by simpa only [weightedTotalDegree_one] using hf.1)
  · simpa only [weightedTotalDegree_piSingle] using (hw (Pi.single (3 : Fin 4) 1)).trans
      (show f.weightedTotalDegree (Pi.single (3 : Fin 4) 1) ≤ p.t by
        simpa only [weightedTotalDegree_piSingle] using hf.2.2)
theorem isolated_translate (a y : GeoPoint) {f g u v : GeoJets}
    (hy : Isolated f g u v y) :
    Isolated (translate a f) (translate a g) (translate a u) (translate a v) (y + a) := by
  let T : GeoJets →+* GeoJets := (translate a).toRingHom
  let J : Ideal GeoJets := Ideal.span ({f, g, u, v} : Set GeoJets)
  have hsurj : Function.Surjective T := by
    intro z
    refine ⟨translate (-a) z, ?_⟩
    change translate a (translate (-a) z) = z
    simpa only [neg_neg] using (translate_inverse (-a) z)
  have hinj : Function.Injective T :=
    (show Function.LeftInverse (translate (-a)) T from translate_inverse a).injective
  have hcomap : (J.map T).comap T = J := by
    rw [Ideal.comap_map_of_surjective T hsurj]
    rw [Ideal.comap_bot_of_injective T hinj, sup_bot_eq]
  have hk : (RingHom.ker (eval (y + a))).comap T = RingHom.ker (eval y) := by
    ext z
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    change eval (y + a) (translate a z) = 0 ↔ eval y z = 0
    rw [eval_translate]
  have h' : RingHom.ker (eval y) ∈ (Ideal.comap T (J.map T)).minimalPrimes := by
    rw [hcomap]
    exact hy
  rw [← hk, Ideal.comap_minimalPrimes_eq_of_surjective hsurj] at h'
  obtain ⟨P, hP, heq⟩ := h'
  have heq' : P = RingHom.ker (eval (y + a)) :=
    Ideal.comap_injective_of_surjective T hsurj heq
  change RingHom.ker (eval (y + a)) ∈
    (Ideal.span ({T f, T g, T u, T v} : Set GeoJets)).minimalPrimes
  rw [← heq']
  simpa only [J, Ideal.map_span, Set.image_insert_eq, Set.image_singleton] using hP
theorem move_to_torus {p h : Shape} {f g u v : GeoJets}
    (hf : GeoFits f p) (hg : GeoFits g p) (hu : GeoFits u h) (hv : GeoFits v h)
    (points : Finset GeoPoint) (hpts : ∀ y ∈ points, Isolated f g u v y) :
    ∃ f' g' u' v', GeoFits f' p ∧ GeoFits g' p ∧ GeoFits u' h ∧ GeoFits v' h ∧
      ∃ points' : Finset GeoPoint, points'.card = points.card ∧
        ∀ y ∈ points', Isolated f' g' u' v' y ∧ ∀ i, y i ≠ 0 := by
  classical
  have ha (i : Fin 4) : ∃ a : GeoField, a ∉ points.image (fun y => -y i) :=
    Infinite.exists_notMem_finset _
  choose a ha using ha
  let e : GeoPoint ↪ GeoPoint :=
    ⟨fun y => y + a, fun _ _ h => add_right_cancel h⟩
  refine ⟨translate a f, translate a g, translate a u, translate a v,
    translate_fits a hf, translate_fits a hg, translate_fits a hu, translate_fits a hv,
    points.map e, Finset.card_map e, ?_⟩
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
  refine ⟨isolated_translate a z (hpts z hz), ?_⟩
  intro i hi
  apply ha i
  exact Finset.mem_image.mpr ⟨z, hz, (eq_neg_of_add_eq_zero_right hi).symm⟩
end
end K1_13_7_1_1
end
section
namespace K1_14_3R
noncomputable section
open K1 K1_14 K1_14_3 Polynomial
def chainCutter (g : ClearedEquation) : Jet :=
  C (liftEquation (clearedDx g)) +
    Polynomial.X (R := Equation) * C (liftEquation g.derivative)
def compatible (P Q : Jet) (q : Surface) : Prop :=
  ∀ f : Equation, Irreducible f → 0 < f.natDegree → C f ∣ P → C f ∣ Q →
    C f ∈ q.asIdeal → ∀ g a, IsClearing f g a →
      chainCutter g ∈ q.asIdeal
def OrdinaryGraphs (P Q : Jet) (qs : Finset Surface) : Prop :=
  ∀ f : Equation, Irreducible f → 0 < f.natDegree → f.natDegree < p →
    C f ∣ P → C f ∣ Q →
    ∃ g a, IsClearing f g a ∧ K1_14_3_2.ProperPair (C f) (chainCutter g) ∧
      ∀ q ∈ qs, C f ∈ q.asIdeal → chainCutter g ∈ q.asIdeal
def stagePass {h : ℕ} (rows : Banks) (pairs : ∀ i : Fin 4, BufferedPair h rows i)
    (i : Fin 5) (q : Surface) : Prop :=
  if hi : i.val < 4 then
    let j : Fin 4 := ⟨i.val, hi⟩
    BankVanishes rows (cheapShape j) q ∧ BankVanishes rows (layeredShape j) q ∧
      compatible (pairs j).cheap (pairs j).layered q
  else BankVanishes rows fullShape q
end
end K1_14_3R
end
section
set_option maxSynthPendingDepth 8
namespace K1_14_3R
noncomputable section
open K1 K1_14 K1_14_3 Polynomial
open K1_14_2_1 (cutoffCount rawVolume movingCeiling)
open private worstBase worstSlope surplusBase surplusSlope volume_eq debit_eq
  from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic
open private bank_nonzero avoids_one from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Split
open private pair_membership from ProximityPrize.SubmissionLower.Pack_K1_14_3Split
private def Certificate (s : Shape) (r mode : ℕ) : Prop :=
  0 < worstBase s + 3555 * worstSlope s r ∧
  0 < worstBase s + 32680 * worstSlope s r ∧
  0 < surplusBase s + 3555 * surplusSlope s r mode ∧
  0 < surplusBase s + 32680 * surplusSlope s r mode
def stageCheck (i : Fin 4) : Prop :=
  Certificate (cheapShape i) (reserve i) 0 ∧
  Certificate (layeredShape i) (reserve i) 1
private instance (i : Fin 4) : Decidable (stageCheck i) := by
  unfold stageCheck Certificate
  infer_instance
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem certificates : ∀ i : Fin 4, stageCheck i := by decide +kernel
private theorem affine_positive {a b h : ℤ} (hlo : 3555 ≤ h) (hhi : h ≤ 32680)
    (ha : 0 < a + 3555 * b) (hb : 0 < a + 32680 * b) : 0 < a + h * b := by
  by_cases hb0 : 0 ≤ b
  · nlinarith only [ha, mul_nonneg (sub_nonneg.mpr hlo) hb0]
  · nlinarith only [hb, mul_nonneg (sub_nonneg.mpr hhi) (neg_nonneg.mpr (le_of_not_ge hb0))]
private theorem test (h r mode : ℕ) (s : Shape) (hlo : 3555 ≤ h) (hhi : h ≤ 32680)
    (hc : Certificate s r mode) :
    s.B * (131071 - h) < cutoffCount h r s ∧
      sourceDebit h s + mode * movingCeiling h s < rawVolume h r s := by
  have hh : h ≤ 131071 := by omega
  have hloI : (3555 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hlo
  have hhiI : (h : ℤ) ≤ 32680 := by exact_mod_cast hhi
  obtain ⟨ha, hb, hc, hd⟩ := hc
  have hw := affine_positive hloI hhiI ha hb
  unfold worstBase worstSlope at hw
  have hpos : (s.B : ℤ) * (131071 - (h : ℤ)) <
      (s.m : ℤ) * 180265 - 2 * (h : ℤ) * r := by nlinarith only [hw]
  have hbuf : 2 * h * r ≤ s.m * 180265 := by
    have hn : 0 ≤ (s.B : ℤ) * (131071 - (h : ℤ)) := by
      exact mul_nonneg (Int.natCast_nonneg _) (by omega)
    have ht : 2 * (h : ℤ) * r ≤ (s.m : ℤ) * 180265 := by linarith only [hpos, hn]
    exact_mod_cast ht
  have hwidth : s.B * (131071 - h) < cutoffCount h r s := by
    unfold cutoffCount
    have ht : ((s.B * (131071 - h) : ℕ) : ℤ) <
        ((s.m * 180265 - 2 * h * r : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hh, Nat.cast_sub hbuf]
      exact hpos
    exact_mod_cast ht
  have hs := affine_positive hloI hhiI hc hd
  have heq := volume_eq h r mode s hh hwidth
  unfold surplusBase surplusSlope at hs
  refine ⟨hwidth, ?_⟩
  have ht : ((sourceDebit h s + mode * movingCeiling h s : ℕ) : ℤ) <
      (rawVolume h r s : ℤ) := by
    rw [debit_eq]
    push_cast
    nlinarith only [hs, heq]
  exact_mod_cast ht
private theorem fixed_of_no_seed (G : Jet) (hn : ¬ K1_14_2.UsesSeed G) :
    G ∈ Set.range fixedEmbedding := by
  let ev := MvPolynomial.eval (fun _ : Fin 2 => (0 : FX))
  refine ⟨G.map (Polynomial.mapRingHom ev), ?_⟩
  ext j y e
  have hd : ((G.coeff j).coeff y).totalDegree = 0 :=
    Nat.eq_zero_of_not_pos fun hp => hn ⟨j, y, hp⟩
  have he := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd
  have hid : MvPolynomial.C (ev ((G.coeff j).coeff y)) = (G.coeff j).coeff y := by
    conv_lhs => rw [he]
    simpa [ev] using he.symm
  exact congrArg (fun a : Seeds => a.coeff e)
    (by simpa only [fixedEmbedding, Polynomial.coe_mapRingHom, coeff_map] using hid :
      (((fixedEmbedding (G.map (Polynomial.mapRingHom ev))).coeff j).coeff y) =
        (G.coeff j).coeff y)
theorem bufferedPairs (power : K1_14_2_1.c1) (rankBound : K1_14_2_1.c2)
    {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : JetSource M F rows) (hl : 3555 ≤ M.overhead)
    (hu : M.overhead ≤ 32680) (i : Fin 4) :
    Nonempty (BufferedPair M.overhead.toNat rows i) := by
  let h := M.overhead.toNat
  have hlo : 3555 ≤ h := by dsimp [h]; omega
  have hhi : h ≤ 32680 := by dsimp [h]; omega
  obtain ⟨hc, hd⟩ := certificates i
  obtain ⟨cw, cv⟩ := test h (reserve i) 0 _ hlo hhi hc
  obtain ⟨lw, lv⟩ := test h (reserve i) 1 _ hlo hhi hd
  simp only [zero_mul, add_zero] at cv
  simp only [one_mul] at lv
  have hcs := pair_membership hl i (s := cheapShape i) (by simp)
  have hls := pair_membership hl i (s := layeredShape i) (by simp)
  have hp : (cheapShape i).U < p := by fin_cases i <;> decide
  obtain ⟨P, hPm, hP⟩ := bank_nonzero src hcs (reserve i) cw cv
  have hLn := bank_nonzero src hls (reserve i) lw (lt_of_le_of_lt (Nat.le_add_right _ _) lv)
  have hseed (j y : ℕ) : ((P.coeff j).coeff y).totalDegree ≤ (cheapShape i).U := by
    by_cases hz : (P.coeff j).coeff y = 0
    · simp [hz]
    · exact (src.shape _ hcs _ P hPm j y hz).2.2
  obtain ⟨Q, hQm, hQ, havoid⟩ := K1_14_2_1.exists_layered P hP _ hLn
    (fun G hi hdiv hv hm => avoids_one src power rankBound (by dsimp [h] at hlo; omega)
      hls (reserve i) lw lv hi hv hm hP hdiv hp hseed)
  have hcut (s : Shape) : reserveCutoff h s i = cutoffCount h (reserve i) s - 1 := by
    unfold reserveCutoff cutoffCount
    omega
  exact ⟨⟨P, Q, hP, hQ, (hcut _).symm ▸ hPm, (hcut _).symm ▸ hQm,
    src.shape _ hcs _ _ hPm, src.shape _ hls _ _ hQm,
    fun G hi hdiv hdiv' hv => fixed_of_no_seed G (fun hm => havoid G hi hdiv hv hm hdiv')⟩⟩
end
end K1_14_3R
end
section
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
namespace K1_14_3R
noncomputable section
open K1 K1_14 K1_14_3 Polynomial
open scoped BigOperators
private def seedValues (z : K) : Fin 2 → L :=
  ![algebraMap K L z, (algebraMap K L z) ^ p]
def specializeSeeds (z : K) : ClearedSeeds →+* L[X] :=
  MvPolynomial.eval (fun i => C (seedValues z i))
theorem specialize_monomial (z : K) (e : Fin 2 →₀ ℕ) (a : L[X]) :
    specializeSeeds z (MvPolynomial.monomial e a) =
      a * C (e.prod fun i n => seedValues z i ^ n) := by
  simp [specializeSeeds, MvPolynomial.eval_monomial, Finsupp.prod, map_prod, map_pow]
theorem specialize_dxSeed (z : K) (c : ClearedSeeds) :
    specializeSeeds z (∑ e ∈ c.support, MvPolynomial.monomial e (c.coeff e).derivative) =
      (specializeSeeds z c).derivative := by
  conv_rhs => rw [c.as_sum]
  simp only [map_sum, specialize_monomial, derivative_mul, derivative_C,
    mul_zero, add_zero]
theorem specialize_chain (g : ClearedEquation) (z : K) (T : L[X]) :
    (g.eval₂ (specializeSeeds z) T).derivative =
      (clearedDx g).eval₂ (specializeSeeds z) T +
        T.derivative * g.derivative.eval₂ (specializeSeeds z) T := by
  conv_lhs => rw [eval₂_eq_sum]
  rw [clearedDx, derivative_apply g]
  simp only [eval₂_sum, eval₂_monomial, eval₂_mul, eval₂_C, eval₂_X_pow,
    map_mul, map_natCast, specialize_dxSeed]
  simp only [Polynomial.sum, derivative_sum,
    derivative_mul, derivative_pow, Finset.sum_add_distrib, Finset.mul_sum]
  apply congrArg (_ + ·)
  apply Finset.sum_congr rfl
  intro j hj
  simp only [eval₂_natCast, map_natCast]
  ring
theorem specialize_lift (g : ClearedEquation) (z : K) (S : K[X]) :
    atMark (liftEquation g) z S =
      algebraMap L[X] FX (g.eval₂ (specializeSeeds z) (liftPoly S)) := by
  unfold atMark liftEquation atX
  rw [coe_mapRingHom, eval₂_map, hom_eval₂]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [specializeSeeds, graphEval]
  · intro i
    fin_cases i <;> simp [specializeSeeds, graphEval, seedValues, seedEmbedding]
theorem chainCutter_zero {f : Equation} {g : ClearedEquation} {a : L[X]}
    (ha : IsClearing f g a) {z : K} {S : K[X]} (hzero : atMark f z S = 0) :
    jetAt (chainCutter g) z S = 0 := by
  have hg : atMark (liftEquation g) z S = 0 := by
    rw [ha.2]
    simpa [atMark, eval₂_mul] using
      mul_eq_zero_of_right ((graphEval z) (MvPolynomial.C (algebraMap L[X] FX a))) hzero
  rw [specialize_lift] at hg
  have ht : g.eval₂ (specializeSeeds z) (liftPoly S) = 0 :=
    (IsFractionRing.injective L[X] FX) (by simpa only [map_zero] using hg)
  have hd := specialize_chain g z (liftPoly S)
  rw [ht, derivative_zero] at hd
  have hn := congrArg (algebraMap L[X] FX) hd.symm
  rw [map_add, map_mul, map_zero, ← specialize_lift, ← specialize_lift] at hn
  simpa only [chainCutter, jetAt, eval₂_add, eval₂_mul, eval₂_C, eval₂_X,
    coe_eval₂RingHom, atMark, atX, liftPoly, derivative_map] using hn
end
end K1_14_3R
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 600000
namespace K1_14_3R
noncomputable section
open K1 K1_14 K1_14_3 Polynomial
open scoped BigOperators
private def asSeedPoly : Equation →+* MvPolynomial (Fin 2) (Polynomial FX) :=
  eval₂RingHom (MvPolynomial.map C) (MvPolynomial.C (Polynomial.X (R := FX)))
theorem asSeedPoly_coeff (f : Equation) (e : Fin 2 →₀ ℕ) (y : ℕ) :
    ((asSeedPoly f).coeff e).coeff y = (f.coeff y).coeff e := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_add, hf, hg]
  | monomial n c =>
    simp only [asSeedPoly, coe_eval₂RingHom, eval₂_monomial, ← map_pow]
    rw [mul_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, mul_comm,
      C_mul_X_pow_eq_monomial, coeff_monomial, coeff_monomial]
    split <;> simp
theorem total_asSeedPoly_le (f : Equation) (U : ℕ)
    (hs : ∀ y, (f.coeff y).totalDegree ≤ U) : (asSeedPoly f).totalDegree ≤ U := by
  apply Finset.sup_le
  intro e he
  obtain ⟨y, hy⟩ : ∃ y, ((asSeedPoly f).coeff e).coeff y ≠ 0 := by
    by_contra! hz
    exact (MvPolynomial.mem_support_iff.mp he) (Polynomial.ext (by simpa using hz))
  rw [asSeedPoly_coeff] at hy
  exact (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hy)).trans (hs y)
theorem seed_cap_of_dvd {f A : Equation} (hdiv : f ∣ A) (hn : A ≠ 0)
    {U : ℕ} (hA : ∀ y, (A.coeff y).totalDegree ≤ U) (y : ℕ) :
    (f.coeff y).totalDegree ≤ U := by
  have hn' : asSeedPoly A ≠ 0 := by
    intro hz
    apply hn
    ext n e
    simp [← asSeedPoly_coeff A e n, hz]
  have h := (MvPolynomial.totalDegree_le_of_dvd_of_isDomain (map_dvd asSeedPoly hdiv) hn').trans
    (total_asSeedPoly_le A U hA)
  apply Finset.sup_le
  intro e he
  apply (MvPolynomial.le_totalDegree (p := asSeedPoly f) ?_).trans h
  apply MvPolynomial.mem_support_iff.mpr
  intro hz
  exact (MvPolynomial.mem_support_iff.mp he) (by rw [← asSeedPoly_coeff, hz, coeff_zero])
private def liftSeed : ClearedSeeds →+* Seeds := MvPolynomial.map (algebraMap L[X] FX)
theorem liftSeed_injective : Function.Injective liftSeed :=
  MvPolynomial.map_injective _ (IsFractionRing.injective L[X] FX)
theorem liftSeed_degree (b : ClearedSeeds) :
    (liftSeed b).totalDegree = b.totalDegree := by
  unfold liftSeed MvPolynomial.totalDegree
  rw [MvPolynomial.support_map_of_injective _ (IsFractionRing.injective L[X] FX)]
theorem lift_coeff (g : ClearedEquation) (y : ℕ) :
    (liftEquation g).coeff y = liftSeed (g.coeff y) := coeff_map _ _
theorem clearing_coeff {f : Equation} {g : ClearedEquation} {a : L[X]}
    (ha : IsClearing f g a) (y : ℕ) :
    liftSeed (g.coeff y) = MvPolynomial.C (algebraMap L[X] FX a) * f.coeff y := by
  rw [← lift_coeff, ha.2, coeff_C_mul]
def dxSeed (b : ClearedSeeds) : ClearedSeeds :=
  ∑ e ∈ b.support, MvPolynomial.monomial e (b.coeff e).derivative
theorem dxSeed_degree (b : ClearedSeeds) : (dxSeed b).totalDegree ≤ b.totalDegree :=
  MvPolynomial.totalDegree_finsetSum_le fun _ he =>
    (MvPolynomial.totalDegree_monomial_le _ _).trans (MvPolynomial.le_totalDegree he)
theorem dx_coeff (g : ClearedEquation) (y : ℕ) :
    (clearedDx g).coeff y = dxSeed (g.coeff y) := by
  classical
  unfold clearedDx
  rw [coeff_sum, Polynomial.sum_def, Finset.sum_eq_single y]
  · simp [dxSeed]
  · intro j _ hj
    exact coeff_monomial_of_ne _ (Ne.symm hj)
  · intro hy
    have hzero : g.coeff y = 0 := by simpa [Polynomial.mem_support_iff] using hy
    simp [hzero]
theorem lift_derivative {f : Equation} {g : ClearedEquation} {a : L[X]}
    (ha : IsClearing f g a) :
    liftEquation g.derivative = C (MvPolynomial.C (algebraMap L[X] FX a)) * f.derivative := by
  have hmap : liftEquation g.derivative = (liftEquation g).derivative :=
    (derivative_map g liftSeed).symm
  rw [hmap, ha.2, derivative_mul, derivative_C, zero_mul, zero_add]
theorem degree_scalar (x : FX) (b : Seeds) :
    (MvPolynomial.C x * b).totalDegree ≤ b.totalDegree := by
  simpa using MvPolynomial.totalDegree_mul (MvPolynomial.C x) b
theorem chainCutter_caps_of_dvd {s : Shape} {Q : Jet} (hQ : Q ≠ 0)
    (hc : RowCaps Q s) (hj : 1 ≤ s.J) {f : Equation} (hf : C f ∣ Q)
    {g : ClearedEquation} {a : L[X]} (ha : IsClearing f g a) :
    RowCaps (chainCutter g) s := by
  have hn := leadingCoeff_ne_zero.mpr hQ
  have hfQ : f ∣ Q.leadingCoeff := (C_dvd_iff_dvd_coeff _ _).mp hf Q.natDegree
  have ht : (Q.coeff Q.natDegree).coeff Q.leadingCoeff.natDegree ≠ 0 := by
    rw [coeff_natDegree, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hn
  have hy : f.natDegree ≤ s.B := (natDegree_le_of_dvd hfQ hn).trans
    ((Nat.le_add_right _ _).trans (hc _ _ ht).1)
  have hu (y : ℕ) : (f.coeff y).totalDegree ≤ s.U := by
    apply seed_cap_of_dvd hfQ hn _ y
    intro j
    by_cases hz : (Q.coeff Q.natDegree).coeff j = 0
    · simpa only [← coeff_natDegree, hz, MvPolynomial.totalDegree_zero] using Nat.zero_le s.U
    · exact (hc _ _ hz).2.2
  intro v y hv
  cases v with
  | zero =>
    simp only [chainCutter, coeff_add, coeff_C_zero, coeff_X_mul_zero, add_zero,
      lift_coeff, dx_coeff] at hv ⊢
    have hfy : f.coeff y ≠ 0 := by
      intro hz
      have hg : g.coeff y = 0 := liftSeed_injective (by simp [clearing_coeff ha y, hz])
      exact hv (by simp [hg, dxSeed])
    refine ⟨(le_natDegree_of_ne_zero hfy).trans hy, Nat.zero_le _, ?_⟩
    rw [liftSeed_degree]
    refine (dxSeed_degree _).trans ?_
    rw [← liftSeed_degree, clearing_coeff ha y]
    exact (degree_scalar _ _).trans (hu y)
  | succ v =>
    simp only [chainCutter, coeff_add, coeff_C_succ, coeff_X_mul, zero_add] at hv ⊢
    cases v with
    | zero =>
      rw [coeff_C_zero, lift_derivative ha, coeff_C_mul] at hv ⊢
      have hdy : f.derivative.coeff y ≠ 0 := fun hz => hv (by simp [hz])
      have hdegree := le_natDegree_of_ne_zero hdy
      have hpos : f.natDegree ≠ 0 := by
        intro hz
        exact hdy (by rw [eq_C_of_natDegree_eq_zero hz, derivative_C, coeff_zero])
      have hlt := natDegree_derivative_lt hpos
      refine ⟨by omega, hj, (degree_scalar _ _).trans ?_⟩
      rw [coeff_derivative]
      have hcast : (↑y + 1 : Seeds) = MvPolynomial.C (↑y + 1 : FX) := by simp
      rw [hcast, mul_comm]
      exact (degree_scalar _ _).trans (hu (y+1))
    | succ v => simp [coeff_C_succ] at hv
attribute [local instance] MvPolynomial.algebraMvPolynomial Polynomial.algebra
  Polynomial.isLocalization in
theorem exists_clearing (f : Equation) : ∃ g a, IsClearing f g a := by
  let D := (nonZeroDivisors (L[X])).map (MvPolynomial.C : L[X] →+* ClearedSeeds)
  obtain ⟨⟨g, ⟨_, d, hd, rfl⟩⟩, he⟩ := IsLocalization.surj (D.map C) f
  obtain ⟨a, ha, rfl⟩ := hd
  refine ⟨g, a, mem_nonZeroDivisors_iff_ne_zero.mp ha, ?_⟩
  change f * liftEquation (C (MvPolynomial.C a)) = liftEquation g at he
  simpa [liftEquation, mul_comm] using he.symm
theorem derivative_nonzero {f : Equation} (hd : 0 < f.natDegree)
    (hp : f.natDegree < p) (hf : f ≠ 0) : f.derivative ≠ 0 := by
  let _ : CharP FX p := charP_of_injective_algebraMap (IsFractionRing.injective L[X] FX) p
  let _ : CharP Seeds p := charP_of_injective_ringHom (f := (MvPolynomial.C : FX →+* Seeds))
    (MvPolynomial.C_injective (Fin 2) FX) p
  have hc : (f.natDegree : Seeds) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff Seeds p]
    exact fun h => (not_le_of_gt hp) (Nat.le_of_dvd hd h)
  intro hzero
  have h := congrArg (fun A : Equation => A.coeff (f.natDegree - 1)) hzero
  have hs : f.natDegree - 1 + 1 = f.natDegree := by omega
  rw [coeff_zero, coeff_derivative, ← Nat.cast_succ, Nat.succ_eq_add_one, hs, coeff_natDegree] at h
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr hf) hc h
theorem chainCutter_proper {f : Equation} (hi : Irreducible f) (hd : 0 < f.natDegree)
    (hp : f.natDegree < p) {g : ClearedEquation} {a : L[X]} (ha : IsClearing f g a) :
    K1_14_3_2.ProperPair (C f) (chainCutter g) := by
  have hC : (C f : Jet) ≠ 0 := C_ne_zero.mpr hi.ne_zero
  have ha' : algebraMap L[X] FX a ≠ 0 := by
    intro hz
    exact ha.1 ((IsFractionRing.injective L[X] FX) (by simpa only [map_zero] using hz))
  have hu : IsUnit (C (MvPolynomial.C (algebraMap L[X] FX a)) : Equation) :=
    ((isUnit_iff_ne_zero.mpr ha').map (MvPolynomial.C : FX →+* Seeds)).map
      (C : Seeds →+* Equation)
  have hder := derivative_nonzero hd hp hi.ne_zero
  have hCutter : (chainCutter g).coeff 1 = liftEquation g.derivative := by
    simp [chainCutter]
  have hder' : liftEquation g.derivative ≠ 0 := by
    rw [lift_derivative ha]
    exact mul_ne_zero hu.ne_zero hder
  have hOrd : IsRelPrime f (liftEquation g.derivative) := by
    apply hi.isRelPrime_iff_not_dvd.mpr
    rw [lift_derivative ha, hu.dvd_mul_left]
    exact fun hf => (not_le_of_gt (natDegree_derivative_lt hd.ne')) (natDegree_le_of_dvd hf hder)
  refine ⟨hC, fun h => hder' (hCutter.symm.trans (by simp [h])), ?_⟩
  intro D hD hleft hright
  have hdeg : D.natDegree ≤ 0 := by simpa using natDegree_le_of_dvd hleft hC
  have heq := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hdeg)
  rw [heq] at hleft hright
  have h0 : D.coeff 0 ∣ f := by simpa using (C_dvd_iff_dvd_coeff _ _).mp hleft 0
  have h1 := (C_dvd_iff_dvd_coeff _ _).mp hright 1
  rw [hCutter] at h1
  apply hD.not_isUnit
  rw [heq]
  exact (hOrd h0 h1).map (C : Equation →+* Jet)
theorem ordinary_graph (f : Equation) (hi : Irreducible f) (hd : 0 < f.natDegree)
    (hp : f.natDegree < p) :
    ∃ g a, IsClearing f g a ∧ K1_14_3_2.ProperPair (C f) (chainCutter g) ∧
      ∀ z S, atMark f z S = 0 → jetAt (chainCutter g) z S = 0 := by
  obtain ⟨g, a, ha⟩ := exists_clearing f
  exact ⟨g, a, ha, chainCutter_proper hi hd hp ha, fun _ _ => chainCutter_zero ha⟩
end
end K1_14_3R
end
section
namespace K1_14_2_2R
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 Polynomial
def chainCompatible (P Q : Jet) (I : Ideal Ambient) : Prop :=
  ∀ f : Equation, Irreducible f → 0 < f.natDegree → C f ∣ P → C f ∣ Q →
    toJet (C f) ∈ I → ∀ g a, K1_14_3.IsClearing f g a →
      toJet (K1_14_3R.chainCutter g) ∈ I
def pairPass {w rows i} (B : RowPair w rows i) (I : Ideal Ambient) : Prop :=
  bankVanishes rows (stageAt i).cheap I ∧ bankVanishes rows (stageAt i).layered I ∧
    chainCompatible B.cheap B.layered I
def stagePass {w rows} (pairs : ∀ i : Fin 10, RowPair w rows i)
    (n : ℕ) (I : Ideal Ambient) : Prop :=
  if hn : n < 10 then pairPass (pairs ⟨n, hn⟩) I else bankVanishes rows full I
end
end K1_14_2_2R
end
section
namespace K1_13_6_1
noncomputable section
open Polynomial K1 K1_13 K1_13_6
open scoped BigOperators
theorem mem_markIdeal {P : Row 4} {S : Geom[X]} :
    toGeneric P ∈ markIdeal S ↔ atJet P S = 0 := by
  unfold markIdeal
  rw [RingHom.mem_ker]
  change MvPolynomial.eval _ (MvPolynomial.map genericCoeffs P) = 0 ↔ _
  rw [MvPolynomial.eval_map]
  change MvPolynomial.eval₂ genericCoeffs (⇑genericCoeffs ∘ jet S) P = 0 ↔ _
  rw [← MvPolynomial.eval₂_comp]
  have injective : Function.Injective genericCoeffs :=
    (algebraMap GenericField GeoField).injective.comp
      (IsFractionRing.injective Geom[X] GenericField)
  exact map_eq_zero_iff _ injective
theorem atJet_eq_shift_constant (P : Row 4) (S : Geom[X]) :
    atJet P S = (shiftJet P S).coeff 0 := by
  let f := MvPolynomial.C (σ := Fin 4) (R := Geom[X])
  let g : Fin 4 → Row 4 := fun i => MvPolynomial.X i + MvPolynomial.C (jet S i)
  change (MvPolynomial.eval (jet S)) P =
    (MvPolynomial.constantCoeff.comp (MvPolynomial.eval₂Hom f g)) P
  congr 1
  ext <;> simp [f, g]
theorem orderAt_vanishes {P : Row 4} {S : Geom[X]} {l : ℕ}
    (hl : 0 < l) (h : OrderAt P S l) : atJet P S = 0 := by
  rw [atJet_eq_shift_constant]
  by_contra he
  have h0 := h 0 (MvPolynomial.mem_support_iff.mpr he)
  simp at h0
  omega
theorem mark_surface {f Q : Row 4} {S : Geom[X]} {l : ℕ}
    (hl : 0 < l) (hf : OnFactor f S) (hQ : OrderAt Q S l) :
    ∃ surface, (intersectionIdeal f Q).IsMinimalPrime surface ∧ surface ≤ markIdeal S := by
  have h : intersectionIdeal f Q ≤ markIdeal S := by
    apply Ideal.span_le.mpr
    intro P hP
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
    rcases hP with rfl | rfl
    · exact mem_markIdeal.mpr hf.1
    · exact mem_markIdeal.mpr (orderAt_vanishes hl hQ)
  have : (markIdeal S).IsPrime := RingHom.ker_isPrime (evalGeneric S)
  exact Ideal.exists_minimalPrimes_le h
theorem mark_curve {surface : Ideal GeoJets} {P : Row 4} {S : Geom[X]}
    (hZ : surface ≤ markIdeal S) (hP : atJet P S = 0) :
    ∃ C, (divisorIdeal surface P).IsMinimalPrime C ∧ C ≤ markIdeal S := by
  have h : divisorIdeal surface P ≤ markIdeal S :=
    sup_le hZ ((Ideal.span_singleton_le_iff_mem _).2 (mem_markIdeal.mpr hP))
  have : (markIdeal S).IsPrime := RingHom.ker_isPrime (evalGeneric S)
  exact Ideal.exists_minimalPrimes_le h
theorem tangentCut_vanishes (g P : Row 4) (S : Geom[X]) (a : ℕ)
    (hg : atJet g S = 0) (hP : atJet P S = 0) : atJet (tangentCut g P a) S = 0 := by
  induction a with
  | zero => exact hP
  | succ a ih =>
    rw [tangentCut, Function.iterate_succ_apply']
    rw [eval_flowNumerator _ _ _ hg]
    change atJet (separant g) S * derivative (atJet (tangentCut g P a) S) = 0
    rw [ih, map_zero, mul_zero]
theorem box_charge {f P : Row 4} {k j : ℕ}
    (hP : InBox (shape P) ((anchorBox f).scale k))
    (hkj : k ≤ j) :
    InBox (shape P) (cutterBox.plus ((anchorBox f).scale j)) := by
  rcases hP with ⟨h1, h2, h3⟩
  exact ⟨h1.trans ((Nat.mul_le_mul_right _ hkj).trans (Nat.le_add_left _ _)),
    h2.trans ((Nat.mul_le_mul_right _ hkj).trans (Nat.le_add_left _ _)),
    h3.trans ((Nat.mul_le_mul_right _ hkj).trans (Nat.le_add_left _ _))⟩
theorem box_cutter_charge {f P : Row 4} {k j : ℕ}
    (hP : InBox (shape P) (cutterBox.plus ((anchorBox f).scale k))) (hkj : k ≤ j) :
    InBox (shape P) (cutterBox.plus ((anchorBox f).scale j)) := by
  rcases hP with ⟨h1, h2, h3⟩
  exact ⟨h1.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hkj) _),
    h2.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hkj) _),
    h3.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hkj) _)⟩
end
end K1_13_6_1
end
section
namespace K1_13_6_1
noncomputable section
open Polynomial K1 K1_13 K1_13_6
open scoped BigOperators
def c1 : Prop :=
  ∀ f surface S, SmallFactor f → OnFactor f S → toGeneric f ∈ surface → surface ≤ markIdeal S →
    ∃ r, CanonicalChart f surface r ∧
      InBox (shape (separant ((separant^[r]) f))) (anchorBox f)
def c2 : Prop :=
  ∀ f Q l surface (hZ : (intersectionIdeal f Q).IsMinimalPrime surface),
    SmallFactor f → (¬ f ∣ Q) → InBox (shape Q) cutterBox →
    ∃ v : ℕ, 0 < v ∧ v ≤ (shape f).b * cutterBox.b ∧
      cycleLength (intersectionIdeal f Q) surface hZ.isPrime = (v : ℕ∞) ∧
      (v < l → ∃ P : Row 4, toGeneric P ∉ surface ∧ InBox (shape P) cutterBox ∧
        ∀ S, OrderAt Q S l → atJet P S = 0)
def c3 : Prop :=
  ∀ f Q surface (hZ : (intersectionIdeal f Q).IsMinimalPrime surface) v r,
    SmallFactor f → (¬ f ∣ Q) → InBox (shape Q) cutterBox →
    0 < v → v ≤ (shape f).b * cutterBox.b →
    cycleLength (intersectionIdeal f Q) surface hZ.isPrime = (v : ℕ∞) →
    CanonicalChart f surface r → ¬ Invariant ((separant^[r]) f) surface →
    let g := (separant^[r]) f
    (r = 0 ∧ toGeneric (tangentCut g Q v) ∉ surface ∧
      InBox (shape (tangentCut g Q v)) (cutterBox.plus ((anchorBox f).scale (2*v)))) ∨
    (0 < r ∧ ∃ w, DerivativeWeight f surface r w ∧ toGeneric (tangentCut g f w) ∉ surface ∧
      InBox (shape (tangentCut g f w)) ((anchorBox f).plus ((anchorBox f).scale (2*w))))
def c4 : Prop :=
  ∀ f Q (surfaces : Finset (Ideal GeoJets)) (P : Ideal GeoJets → Row 4),
    SmallFactor f → (¬ f ∣ Q) → InBox (shape Q) cutterBox →
    (∀ surface ∈ surfaces, SurfaceCut f Q surface (P surface)) →
    ∃ curves : Finset (Ideal GeoJets),
      (∀ surface ∈ surfaces, ∀ C, (divisorIdeal surface (P surface)).IsMinimalPrime C → C ∈ curves) ∧
      (∀ C ∈ curves, CurveOnFactor f C) ∧
      32 * (∑ C ∈ curves, sectionDegree C ((chart taylorLength (anchorBox f)).scale 6)) ≤
        6 * auxCurves32 (shape f) ∧
      32 * (∑ C ∈ curves, sectionDegree C ((anchorBox f).scale 6)) ≤
        6 * auxPoints32 (shape f)
def c5 : Prop :=
  ∀ (Γ : Finset K) s f C r, SmallFactor f → CurveOnFactor f C → CanonicalChart f C r →
    InBox (shape (separant ((separant^[r]) f))) (anchorBox f) →
    Set.InjOn s (Γ : Set K) → (∀ γ ∈ Γ, (s γ).natDegree ≤ 133671) →
    ∃ (A B : Finset K) (d : ℕ),
      A ⊆ Γ ∧ CurveSections A s d ∧
      (∀ γ ∈ Γ, C ≤ markIdeal (extend (s γ)) → γ ∈ A ∪ B) ∧
      6*d ≤ sectionDegree C ((chart taylorLength (anchorBox f)).scale 6) ∧
      6*B.card ≤ sectionDegree C ((anchorBox f).scale 6) ∧
      6 ≤ sectionDegree C ((anchorBox f).scale 6)
theorem factor_mem {f Q : Row 4} {surface : Ideal GeoJets}
    (hZ : (intersectionIdeal f Q).IsMinimalPrime surface) :
    toGeneric f ∈ surface :=
  hZ.le (Ideal.subset_span (Set.mem_insert _ _))
theorem one_surface (h1 : c1) (h2 : c2) (h3 : c3)
    {Γ s f Q l surface} (input : CutInput Γ s f Q l)
    (hZ : (intersectionIdeal f Q).IsMinimalPrime surface) (active : HasMark Γ s surface) :
    ∃ P, SurfaceCut f Q surface P ∧
      ∀ γ ∈ Γ, surface ≤ markIdeal (extend (s γ)) →
        ¬ HighMark f Q l (extend (s γ)) → atJet P (extend (s γ)) = 0 := by
  have hbox : InBox (shape Q) cutterBox :=
    ⟨input.box.1.trans (by decide), input.box.2⟩
  obtain ⟨v, hv, hvmax, hlen, hlow⟩ := h2 f Q l surface hZ input.small input.proper hbox
  by_cases low : v < l
  · obtain ⟨P, hP, hPb, hvan⟩ := hlow low
    have hPb' : InBox (shape P) (cutterBox.plus ((anchorBox f).scale 0)) := by
      simpa [InBox, Shape.plus, Shape.scale] using hPb
    exact ⟨P, ⟨hZ, v, 0, hv, hlen, Or.inl rfl, hP,
      box_cutter_charge hPb' (Nat.zero_le _)⟩,
      fun γ hγ _ _ => hvan _ (input.order γ hγ)⟩
  obtain ⟨γ₀, hγ₀, hmark₀⟩ := active
  obtain ⟨r, hr, hrBox⟩ := h1 f surface (extend (s γ₀)) input.small
    (input.onFactor γ₀ hγ₀) (factor_mem hZ) hmark₀
  let g := (separant^[r]) f
  have on_g : ∀ S, surface ≤ markIdeal S → atJet g S = 0 :=
    fun S hS => mem_markIdeal.mp (hS (hr.2.1 r le_rfl))
  have high : (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) surface hZ.isPrime := by
    rw [hlen]
    exact_mod_cast Nat.le_of_not_gt low
  by_cases inv : Invariant g surface
  · have hsep : InBox (shape (separant g)) ((anchorBox f).scale 1) := by
      simpa [InBox, Shape.scale] using hrBox
    refine ⟨separant g, ⟨hZ, v, 0, hv, hlen, Or.inl rfl, hr.2.2,
      box_charge hsep (by omega)⟩, ?_⟩
    intro γ _ hpoint hnot
    by_contra hregular
    exact hnot ⟨surface, r, hZ, high, hpoint, hr, hregular, inv⟩
  rcases h3 f Q surface hZ v r input.small input.proper hbox hv hvmax hlen hr inv with
    ⟨_, hP, hPb⟩ | ⟨hrPos, w, hw, hP, hPb⟩
  · exact ⟨tangentCut g Q v, ⟨hZ, v, 0, hv, hlen, Or.inl rfl, hP,
      box_cutter_charge hPb (by omega)⟩,
      fun γ hγ hpoint _ => tangentCut_vanishes g Q _ v (on_g _ hpoint)
        (orderAt_vanishes input.positive (input.order γ hγ))⟩
  · have hPb' : InBox (shape (tangentCut g f w)) ((anchorBox f).scale (2*w+1)) := by
      simpa [InBox, Shape.plus, Shape.scale, Nat.add_mul, Nat.add_comm] using hPb
    exact ⟨tangentCut g f w, ⟨hZ, v, w, hv, hlen, Or.inr ⟨r, hrPos, hr.1, hw⟩, hP,
      box_charge hPb' (by omega)⟩,
      fun γ hγ hpoint _ => tangentCut_vanishes g f _ w (on_g _ hpoint)
        (input.onFactor γ hγ).1⟩
private theorem assemble {Γ s f Q l} (curves : Finset (Ideal GeoJets))
    (marks : ∀ γ ∈ Γ, ¬ HighMark f Q l (extend (s γ)) →
      ∃ C ∈ curves, C ≤ markIdeal (extend (s γ)))
    (recover : ∀ C : curves, ∃ (A B : Finset K) (d : ℕ),
      A ⊆ Γ ∧ CurveSections A s d ∧
      (∀ γ ∈ Γ, C.val ≤ markIdeal (extend (s γ)) → γ ∈ A ∪ B) ∧
      6*d ≤ sectionDegree C.val ((chart taylorLength (anchorBox f)).scale 6) ∧
      6*B.card ≤ sectionDegree C.val ((anchorBox f).scale 6) ∧
      6 ≤ sectionDegree C.val ((anchorBox f).scale 6))
    (hcurves : 32 * (∑ C ∈ curves,
      sectionDegree C ((chart taylorLength (anchorBox f)).scale 6)) ≤
      6 * auxCurves32 (shape f))
    (hpoints : 32 * (∑ C ∈ curves, sectionDegree C ((anchorBox f).scale 6)) ≤
      6 * auxPoints32 (shape f)) :
    ∃ (C : Pieces Γ) (B : Finset K),
      C.curves s ∧
      (∀ γ ∈ Γ, ¬ HighMark f Q l (extend (s γ)) → γ ∈ C.union ∪ B) ∧
      32 * C.total ≤ auxCurves32 (shape f) ∧
      32 * (B.card + C.n) ≤ 2 * auxPoints32 (shape f) := by
  classical
  choose A B d hd using recover
  let e := curves.equivFin.symm
  let cover : Pieces Γ :=
    ⟨curves.card, fun i => A (e i), fun i => (hd (e i)).1, fun i => d (e i)⟩
  let points := curves.attach.biUnion B
  refine ⟨cover, points, fun i => (hd (e i)).2.1, ?_, ?_, ?_⟩
  · intro γ hγ hn
    obtain ⟨C, hC, hm⟩ := marks γ hγ hn
    let i := curves.equivFin ⟨C, hC⟩
    have hi : e i = ⟨C, hC⟩ := e.apply_symm_apply ⟨C, hC⟩
    rcases Finset.mem_union.mp ((hd ⟨C, hC⟩).2.2.1 γ hγ hm) with ha | hb
    · exact Finset.mem_union_left _ <| Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ i, by change γ ∈ A (e i); rwa [hi]⟩
    · exact Finset.mem_union_right _ <| Finset.mem_biUnion.mpr
        ⟨⟨C, hC⟩, Finset.mem_attach _ _, hb⟩
  · let degree := fun C => sectionDegree C ((chart taylorLength (anchorBox f)).scale 6)
    have hsum : 6 * cover.total ≤ ∑ C ∈ curves, degree C := by
      change 6 * (∑ i, d (e i)) ≤ _
      rw [Finset.mul_sum]
      calc
        _ ≤ ∑ i, degree (e i).val := Finset.sum_le_sum fun i _ => (hd (e i)).2.2.2.1
        _ = _ := by
          rw [← Finset.sum_attach curves degree]
          exact Fintype.sum_equiv e _ _ (fun _ => rfl)
    change 32 * (∑ C ∈ curves, degree C) ≤ _ at hcurves
    omega
  · let degree := fun C => sectionDegree C ((anchorBox f).scale 6)
    have hB : 6 * points.card ≤ ∑ C ∈ curves, degree C := by
      calc
        _ ≤ 6 * (∑ C ∈ curves.attach, (B C).card) :=
          Nat.mul_le_mul_left _ Finset.card_biUnion_le
        _ = ∑ C ∈ curves.attach, 6 * (B C).card := by rw [Finset.mul_sum]
        _ ≤ ∑ C ∈ curves.attach, degree C.val :=
          Finset.sum_le_sum fun C _ => (hd C).2.2.2.2.1
        _ = _ := Finset.sum_attach curves degree
    have hN : 6 * cover.n ≤ ∑ C ∈ curves, degree C := by
      calc
        _ = ∑ _ ∈ curves.attach, 6 := by simp [cover, Nat.mul_comm]
        _ ≤ ∑ C ∈ curves.attach, degree C.val :=
          Finset.sum_le_sum fun C _ => (hd C).2.2.2.2.2
        _ = _ := Finset.sum_attach curves degree
    change 32 * (∑ C ∈ curves, degree C) ≤ _ at hpoints
    omega
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) :
    K1_13_6.c1 := by
  classical
  intro Γ s f Q l input
  let hs := (intersectionIdeal f Q).finite_minimalPrimes_of_isNoetherianRing
  let zs := hs.toFinset.filter (HasMark Γ s)
  have selected : ∀ surface ∈ zs, ∃ P, SurfaceCut f Q surface P ∧
      ∀ γ ∈ Γ, surface ≤ markIdeal (extend (s γ)) →
        ¬ HighMark f Q l (extend (s γ)) → atJet P (extend (s γ)) = 0 := by
    intro surface hZ
    rcases Finset.mem_filter.mp hZ with ⟨hbase, hmark⟩
    exact one_surface h1 h2 h3 input (hs.mem_toFinset.mp hbase) hmark
  have all : ∀ surface, ∃ P : Row 4, surface ∈ zs →
      SurfaceCut f Q surface P ∧
      ∀ γ ∈ Γ, surface ≤ markIdeal (extend (s γ)) →
        ¬ HighMark f Q l (extend (s γ)) → atJet P (extend (s γ)) = 0 := by
    intro surface
    by_cases hz : surface ∈ zs
    · obtain ⟨P, hP⟩ := selected surface hz
      exact ⟨P, fun _ => hP⟩
    · exact ⟨0, fun h => (hz h).elim⟩
  choose P hP using all
  have hbox : InBox (shape Q) cutterBox :=
    ⟨input.box.1.trans (by decide), input.box.2⟩
  obtain ⟨cs, hdiv, hcurve, hc, hp⟩ := h4 f Q zs P input.small input.proper hbox
    (fun surface hZ => (hP surface hZ).1)
  let curves := cs.filter (HasMark Γ s)
  apply assemble curves
  · intro γ hγ hn
    obtain ⟨surface, hZ, hmark⟩ := mark_surface input.positive
      (input.onFactor γ hγ) (input.order γ hγ)
    have hz : surface ∈ zs := Finset.mem_filter.mpr ⟨hs.mem_toFinset.mpr hZ, γ, hγ, hmark⟩
    obtain ⟨C, hC, hcmark⟩ := mark_curve hmark ((hP surface hz).2 γ hγ hmark hn)
    exact ⟨C, Finset.mem_filter.mpr ⟨hdiv surface hz C hC, γ, hγ, hcmark⟩, hcmark⟩
  · intro C
    obtain ⟨hC, γ, hγ, hmark⟩ := Finset.mem_filter.mp C.property
    have hcf := hcurve C.val hC
    obtain ⟨r, hr, hsep⟩ := h1 f C.val (extend (s γ)) input.small
      (input.onFactor γ hγ) hcf.contains hmark
    exact h5 Γ s f C.val r input.small hcf hr hsep input.distinct input.degree
  · exact (Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))).trans hc
  · exact (Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))).trans hp
end
end K1_13_6_1
end
section
namespace K1_13_6_1_4
noncomputable section
open K1_13 K1_13_6 K1_13_6_1 K1_13_7_1
open scoped BigOperators
def c1 : Prop :=
  ∀ (surface : Ideal GeoJets) (P : GeoJets) (a h : Shape),
    surface.IsPrime → ringKrullDim (GeoJets ⧸ surface) = 2 →
    FullChamber a → FullChamber h → P ∉ surface → GeoFits P a →
    6 * (∑ C ∈ (surface ⊔ Ideal.span {P}).minimalPrimesFinset,
      sectionDegree C (h.scale 6)) ≤ surfaceDegree surface (a.scale 6) (h.scale 6)
def c2 : Prop :=
  ∀ (surface : Ideal GeoJets) (a b h : Shape) (m n : ℕ),
    surface.IsPrime → ringKrullDim (GeoJets ⧸ surface) = 2 →
    FullChamber a → FullChamber b → FullChamber h → 0 < m →
    surfaceDegree surface (((a.scale m).plus (b.scale n)).scale 6) (h.scale 6) ≤
      m * surfaceDegree surface (a.scale 6) (h.scale 6) +
      n * surfaceDegree surface (b.scale 6) (h.scale 6)
def c3 : Prop :=
  ∀ (F G : GeoJets) (p q a h : Shape),
    F ≠ 0 → G ≠ 0 → IsRelPrime F G →
    FullChamber p → FullChamber q → FullChamber a → FullChamber h →
    GeoFits F p → GeoFits G q →
    ∀ (surfaces : Finset (Ideal GeoJets)) (v : Ideal GeoJets → ℕ),
      (∀ surface ∈ surfaces, ∃ hs : (pairIdeal F G).IsMinimalPrime surface,
        cycleLength (pairIdeal F G) surface hs.isPrime = (v surface : ℕ∞)) →
      32 * (∑ surface ∈ surfaces, v surface *
        surfaceDegree surface (a.scale 6) (h.scale 6)) ≤ 36 * mixed32 p q a h
private theorem full_plus {a b : Shape} (ha : FullChamber a) (hb : Chamber b) :
    FullChamber (a.plus b) := by
  obtain ⟨⟨ha₁, ha₂⟩, ha₃⟩ := ha
  obtain ⟨hb₁, hb₂⟩ := hb
  change (a.j + b.j ≤ a.b + b.b ∧ 3 * (a.t + b.t) ≤ a.j + b.j) ∧ 0 < a.t + b.t
  exact ⟨⟨by omega, by omega⟩, by omega⟩
private theorem chamber_scale {a : Shape} (ha : Chamber a) (k : ℕ) :
    Chamber (a.scale k) := by
  refine ⟨Nat.mul_le_mul_left k ha.1, ?_⟩
  simpa [Shape.scale, Nat.mul_left_comm 3 k] using Nat.mul_le_mul_left k ha.2
private theorem full_scale {a : Shape} (ha : FullChamber a) {k : ℕ} (hk : 0 < k) :
    FullChamber (a.scale k) :=
  ⟨chamber_scale ha.1 k, Nat.mul_pos hk ha.2⟩
private theorem charge_coord (q p v w : ℕ) (hv : 0 < v) :
    q + (4*v + 2*w) * p ≤ v*(q + 4*p) + (2*w)*p := by
  calc
    _ = q + v*(4*p) + (2*w)*p := by ring
    _ ≤ v*q + v*(4*p) + (2*w)*p := by
      have hq : q ≤ v*q := Nat.le_mul_of_pos_left q hv
      exact Nat.add_le_add_right (Nat.add_le_add_right hq _) _
    _ = _ := by ring
private theorem supported_charge {f P : Row 4} {v w : ℕ} (hv : 0 < v)
    (h : InBox (shape P) (cutterBox.plus ((anchorBox f).scale (4*v + 2*w)))) :
    GeoFits (toGeneric P)
      (((cutterBox.plus ((anchorBox f).scale 4)).scale v).plus ((anchorBox f).scale (2*w))) :=
  toGeneric_fits ⟨h.1.trans (charge_coord _ _ _ _ hv),
    h.2.1.trans (charge_coord _ _ _ _ hv), h.2.2.trans (charge_coord _ _ _ _ hv)⟩
private theorem sum_biUnion_bound {α β : Type*} [DecidableEq β]
    (s : Finset α) (pieces : α → Finset β) (d : β → ℕ) :
    (∑ b ∈ s.biUnion pieces, d b) ≤ ∑ a ∈ s, ∑ b ∈ pieces a, d b := by
  rw [← Finset.sup_eq_biUnion]
  refine s.apply_sup_le_sum (f := fun t => ∑ b ∈ t, d b) (by simp) ?_
  intro u v
  change (∑ b ∈ u ∪ v, d b) ≤ _
  have heq := Finset.sum_union_inter (s₁ := u) (s₂ := v) (f := d)
  omega
private theorem toGeneric_ne_zero {F : Row 4} (hF : F ≠ 0) : toGeneric F ≠ 0 := by
  intro h
  apply hF
  apply toGeneric_injective
  simpa only [toGeneric, map_zero] using h
theorem choose_charge {f Q : Row 4} {surface : Ideal GeoJets} {P : Row 4}
    (hf : SmallFactor f) (h : SurfaceCut f Q surface P) :
    ∃ v w r : ℕ,
      (∃ hs : (intersectionIdeal f Q).IsMinimalPrime surface,
        cycleLength (intersectionIdeal f Q) surface hs.isPrime = (v : ℕ∞)) ∧
      0 < v ∧ r < (shape f).t ∧ (w = 0 ∨ DerivativeWeight f surface r w) ∧
      toGeneric P ∉ surface ∧
      InBox (shape P) (cutterBox.plus ((anchorBox f).scale (4*v + 2*w))) := by
  obtain ⟨hs, v, w, hv, hlen, hderiv, hP, hb⟩ := h
  rcases hderiv with hzero | ⟨r, _, hr, hd⟩
  · exact ⟨v, w, 0, ⟨hs, hlen⟩, hv, hf.2.1, Or.inl hzero, hP, hb⟩
  · exact ⟨v, w, r, ⟨hs, hlen⟩, hv, hr, Or.inr hd, hP, hb⟩
private theorem derivative_sum (h3 : c3) {f : Row 4} (hf : SmallFactor f)
    (hp : FullChamber (anchorBox f)) {h : Shape} (hh : FullChamber h)
    (surfaces : Finset (Ideal GeoJets)) (r w : Ideal GeoJets → ℕ)
    (hr : ∀ surface ∈ surfaces, r surface < (shape f).t)
    (hw : ∀ surface ∈ surfaces, w surface = 0 ∨ DerivativeWeight f surface (r surface) (w surface)) :
    32 * (∑ surface ∈ surfaces, w surface *
      surfaceDegree surface ((anchorBox f).scale 6) (h.scale 6)) ≤
      36 * ((shape f).t * mixed32 (anchorBox f) (anchorBox f) (anchorBox f) h) := by
  classical
  let p := anchorBox f
  let value := fun surface => w surface * surfaceDegree surface (p.scale 6) (h.scale 6)
  let paid := surfaces.filter fun surface => w surface ≠ 0
  let orders := Finset.range (shape f).t
  have hmaps : ∀ surface ∈ paid, r surface ∈ orders := by
    intro surface hs
    exact Finset.mem_range.mpr (hr surface (Finset.mem_filter.mp hs).1)
  have hpaid : (∑ surface ∈ paid, value surface) = ∑ surface ∈ surfaces, value surface := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro surface _
    by_cases hv : w surface = 0 <;> simp [value, hv]
  have group (j : ℕ) :
      32 * (∑ surface ∈ paid.filter (fun surface => r surface = j), value surface) ≤
        36 * mixed32 p p p h := by
    let fibre := paid.filter fun surface => r surface = j
    by_cases he : fibre.Nonempty
    · have data (surface : Ideal GeoJets) (hs : surface ∈ fibre) :
          DerivativeWeight f surface j (w surface) := by
        obtain ⟨hpaid, htag⟩ := Finset.mem_filter.mp hs
        obtain ⟨hs, hpos⟩ := Finset.mem_filter.mp hpaid
        rw [← htag]
        exact (hw surface hs).resolve_left hpos
      obtain ⟨surface, hs⟩ := he
      let g := (separant^[j]) f
      have hgproper : ¬ f ∣ g := (data surface hs).1
      have hgfit : InBox (shape g) p := (data surface hs).2.1
      have hf0 := toGeneric_ne_zero hf.1.ne_zero
      have hg0 : toGeneric g ≠ 0 := toGeneric_ne_zero fun hg =>
        hgproper (hg.symm ▸ dvd_zero f)
      exact h3 _ _ p p p h hf0 hg0 (proper_generic f g hf.1 hgproper)
        hp hp hp hh (toGeneric_fits ⟨le_max_left _ _, le_rfl, le_rfl⟩) (toGeneric_fits hgfit)
        fibre w (fun t ht => (data t ht).2.2.2)
    · rw [show paid.filter (fun surface => r surface = j) = ∅ from
        Finset.not_nonempty_iff_eq_empty.mp he, Finset.sum_empty, mul_zero]
      exact Nat.zero_le _
  change 32 * (∑ surface ∈ surfaces, value surface) ≤ 36 * ((shape f).t * mixed32 p p p h)
  calc
    _ = ∑ j ∈ orders, 32 * (∑ surface ∈ paid.filter (fun surface => r surface = j), value surface) := by
      rw [← hpaid, ← Finset.sum_fiberwise_of_maps_to hmaps value]
      simp only [Finset.mul_sum]
    _ ≤ ∑ _j ∈ orders, 36 * mixed32 p p p h := Finset.sum_le_sum fun j _ => group j
    _ = _ := by simp [orders, Nat.mul_left_comm]
private theorem degree_bound (h1 : c1) (h2 : c2) (h3 : c3)
    {f Q : Row 4} {surfaces : Finset (Ideal GeoJets)} {P : Ideal GeoJets → Row 4}
    (hf : SmallFactor f) (hq : ¬ f ∣ Q) (hQ : InBox (shape Q) cutterBox)
    (cuts : ∀ surface ∈ surfaces, SurfaceCut f Q surface (P surface))
    {h : Shape} (hh : FullChamber h) :
    32 * (∑ C ∈ surfaces.biUnion (fun surface => (divisorIdeal surface (P surface)).minimalPrimesFinset),
      sectionDegree C (h.scale 6)) ≤
    6 * (mixed32 (anchorBox f) cutterBox (cutterBox.plus ((anchorBox f).scale 4)) h +
      2*(shape f).t * mixed32 (anchorBox f) (anchorBox f) (anchorBox f) h) := by
  classical
  let p := anchorBox f
  let a := cutterBox.plus (p.scale 4)
  let base := fun surface => surfaceDegree surface (a.scale 6) (h.scale 6)
  let extra := fun surface => surfaceDegree surface (p.scale 6) (h.scale 6)
  let components := fun surface => (divisorIdeal surface (P surface)).minimalPrimesFinset
  let d := fun C => sectionDegree C (h.scale 6)
  let total := ∑ C ∈ surfaces.biUnion components, d C
  have hp : FullChamber p := ⟨shape_chamber f, hf.2.1⟩
  have hqBox : FullChamber cutterBox := ⟨⟨by decide, by decide⟩, by decide⟩
  have ha : FullChamber a := full_plus hqBox (chamber_scale hp.1 4)
  have only_on_selected (surface : Ideal GeoJets) :
    ∃ v w r : ℕ, surface ∈ surfaces →
      (∃ hs : (intersectionIdeal f Q).IsMinimalPrime surface,
        cycleLength (intersectionIdeal f Q) surface hs.isPrime = (v : ℕ∞)) ∧
      0 < v ∧ r < (shape f).t ∧ (w = 0 ∨ DerivativeWeight f surface r w) ∧
      toGeneric (P surface) ∉ surface ∧
      InBox (shape (P surface)) (cutterBox.plus ((anchorBox f).scale (4*v + 2*w))) := by
    by_cases hs : surface ∈ surfaces
    · obtain ⟨v, w, r, hd⟩ := choose_charge hf (cuts surface hs)
      exact ⟨v, w, r, fun _ => hd⟩
    · exact ⟨0, 0, 0, fun hn => (hs hn).elim⟩
  choose v w r hdata using only_on_selected
  have hf0 := toGeneric_ne_zero hf.1.ne_zero
  have hQ0 : toGeneric Q ≠ 0 := toGeneric_ne_zero fun hzero =>
    hq (hzero.symm ▸ dvd_zero f)
  have hproper := proper_generic f Q hf.1 hq
  have single (surface : Ideal GeoJets) (hs : surface ∈ surfaces) :
      6 * (∑ C ∈ components surface, d C) ≤ v surface * base surface + (2*w surface) * extra surface := by
    obtain ⟨⟨hz, _⟩, hv, _, _, hP, hfit⟩ := hdata surface hs
    have hdim := pair_dimension hf0 hproper hz
    have hab := full_plus (full_scale ha hv) (chamber_scale hp.1 (2*w surface))
    exact (h1 surface _ _ h hz.isPrime hdim hab hh hP (supported_charge hv hfit)).trans
      (h2 surface a p h _ _ hz.isPrime hdim ha hp hh hv)
  have hsum : 6 * total ≤
      (∑ surface ∈ surfaces, v surface * base surface) +
        2 * (∑ surface ∈ surfaces, w surface * extra surface) := by
    calc
      _ ≤ 6 * (∑ surface ∈ surfaces, ∑ C ∈ components surface, d C) :=
        Nat.mul_le_mul_left _ (sum_biUnion_bound surfaces components d)
      _ = ∑ surface ∈ surfaces, 6 * (∑ C ∈ components surface, d C) := Finset.mul_sum ..
      _ ≤ ∑ surface ∈ surfaces, (v surface * base surface + (2*w surface) * extra surface) :=
        Finset.sum_le_sum single
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]; simp only [Nat.mul_assoc]
  have hbase := h3 _ _ p cutterBox a h hf0 hQ0 hproper hp hqBox ha hh
    (toGeneric_fits ⟨le_max_left _ _, le_rfl, le_rfl⟩) (toGeneric_fits hQ)
    surfaces v (fun surface hs => (hdata surface hs).1)
  have hextra := derivative_sum h3 hf hp hh surfaces r w
    (fun surface hs => (hdata surface hs).2.2.1)
    (fun surface hs => (hdata surface hs).2.2.2.1)
  change 32 * (∑ surface ∈ surfaces, v surface * base surface) ≤
    36 * mixed32 p cutterBox a h at hbase
  change 32 * (∑ surface ∈ surfaces, w surface * extra surface) ≤
    36 * ((shape f).t * mixed32 p p p h) at hextra
  change 32 * total ≤ 6 * (mixed32 p cutterBox a h + 2*(shape f).t * mixed32 p p p h)
  rw [Nat.mul_assoc 2]
  omega
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_13_6_1.c4 := by
  classical
  intro f Q surfaces P hf hq hQ cuts
  let curves := surfaces.biUnion fun surface => (divisorIdeal surface (P surface)).minimalPrimesFinset
  have hf0 := toGeneric_ne_zero hf.1.ne_zero
  have hproper := proper_generic f Q hf.1 hq
  have hp : FullChamber (anchorBox f) := ⟨shape_chamber f, hf.2.1⟩
  have hchart : FullChamber (chart taylorLength (anchorBox f)) := by
    refine ⟨chart_chamber _ _, ?_⟩
    change 0 < min (2*taylorLength*((anchorBox f).t-1)+taylorLength+1)
      ((2*taylorLength*((anchorBox f).j-3)+taylorLength+3)/3)
    omega
  refine ⟨curves, ?_, ?_, ?_, ?_⟩
  · intro surface hs C hC
    exact Finset.mem_biUnion.mpr ⟨surface, hs, Ideal.mem_minimalPrimesFinset.mpr hC⟩
  · intro C hC
    obtain ⟨surface, hs, hc⟩ := Finset.mem_biUnion.mp hC
    obtain ⟨hz, _, _, _, _, _, hP, _⟩ := cuts surface hs
    exact curve_of_proper_cut hz.isPrime (pair_dimension hf0 hproper hz)
      (hz.le (Ideal.subset_span (by simp))) hP (Ideal.mem_minimalPrimesFinset.mp hc)
  · exact degree_bound h1 h2 h3 hf hq hQ cuts hchart
  · exact degree_bound h1 h2 h3 hf hq hQ cuts hp
end
end K1_13_6_1_4
end
section
namespace K1_13_6_1_4_2
noncomputable section
open K1_13 K1_13_6
def exponents (p : Shape) : Set (Fin 4 → ℕ) :=
  {e | e 0 + e 1 + e 2 + e 3 ≤ p.b ∧
    e 1 + 2 * e 2 + 3 * e 3 ≤ p.j ∧ e 3 ≤ p.t}
def latticeIndices (p : Shape) : Set (Fin 4 →₀ ℕ) :=
  {e | (fun i => e i) ∈ exponents (p.scale 6)}
instance (p : Shape) : Finite (latticeIndices p) := by
  refine ((Finsupp.finite_of_degree_le (6 * p.b)).subset ?_).to_subtype
  intro e he
  change e.degree ≤ 6 * p.b
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_four]
  have he' : e 0 + e 1 + e 2 + e 3 ≤ 6 * p.b := he.1
  simpa only [Nat.add_assoc] using he'
def topCoeff (surface : Ideal GeoJets) (p : Shape) : ℚ :=
  (MvPolynomial.affineHilbertPolynomial
    (surface.comap (MvPolynomial.monomialMap GeoField (latticeIndices p)).toRingHom)).coeff 2
end
end K1_13_6_1_4_2
end
section
namespace K1_13_6_1_4_2
open K1_13 K1_13_6 K1_13_6_1 K1_13_7_1 K1_13_6_1_4
open scoped BigOperators Pointwise
theorem mem_exponents_iff (p : Shape) (m : SectionIndex p) :
    (fun i => (m i).val) ∈ exponents p ↔ m ∈ boxMonomials p := by
  norm_num [exponents, boxMonomials, Fin.sum_univ_four]
theorem exponents_eq_image (p : Shape) :
    exponents p = (fun m : SectionIndex p => fun i => (m i).val) ''
      (boxMonomials p : Set (SectionIndex p)) := by
  ext e
  constructor
  · intro he
    have hsum : (∑ i, e i) ≤ p.b := by
      have hb : e 0 + e 1 + e 2 + e 3 ≤ p.b := he.1
      simpa [Fin.sum_univ_four, Nat.add_assoc] using hb
    let m : SectionIndex p := fun i => ⟨e i, Nat.lt_succ_of_le
      ((Finset.single_le_sum (f := e) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hsum)⟩
    exact ⟨m, (mem_exponents_iff p m).mp he, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact (mem_exponents_iff p m).mpr hm
theorem exponents_zero : exponents ⟨0, 0, 0⟩ = ({0} : Set (Fin 4 → ℕ)) := by
  ext e
  constructor
  · intro he
    have hb : e 0 + e 1 + e 2 + e 3 ≤ 0 := he.1
    apply Set.mem_singleton_iff.mpr
    funext i
    fin_cases i
    · change e 0 = 0
      omega
    · change e 1 = 0
      omega
    · change e 2 = 0
      omega
    · change e 3 = 0
      omega
  · rintro rfl
    simp [exponents]
private theorem split_cap {x a b : ℕ} (h : x ≤ a + b) :
    ∃ u v : ℕ, u ≤ a ∧ v ≤ b ∧ u + v = x := by
  refine ⟨min x a, x - min x a, min_le_right _ _, ?_, ?_⟩
  · omega
  · omega
theorem exponents_plus (p q : Shape) (hp : Chamber p) (hq : Chamber q)
    (hpj : p.j % 2 = 0) (hqj : q.j % 2 = 0)
    (hpt : p.t % 2 = 0) :
    exponents (p.plus q) = exponents p + exponents q := by
  ext e
  change _ ↔ ∃ u ∈ exponents p, ∃ v ∈ exponents q, u + v = e
  constructor
  · intro he
    obtain ⟨htotal, hindex, htop⟩ : e 0 + e 1 + e 2 + e 3 ≤ p.b + q.b ∧
        e 1 + 2 * e 2 + 3 * e 3 ≤ p.j + q.j ∧ e 3 ≤ p.t + q.t := he
    obtain ⟨hpb, hpc⟩ := hp
    obtain ⟨hqb, hqc⟩ := hq
    let u3 := min (e 3) p.t
    let v3 := e 3 - u3
    have hu3 : u3 ≤ p.t := min_le_right _ _
    have hv3 : v3 ≤ q.t := by dsimp [u3, v3]; omega
    have huv3 : u3 + v3 = e 3 := by dsimp [u3, v3]; omega
    let jp := p.j - 3 * u3
    let jq := q.j - 3 * v3
    have hjp : jp + 3 * u3 = p.j := by dsimp [jp]; omega
    have hjq : jq + 3 * v3 = q.j := by dsimp [jq]; omega
    have hweight : e 1 + 2 * e 2 ≤ jp + jq := by omega
    have hparity : jp % 2 = 0 ∨ jq % 2 = 0 := by
      by_cases h : e 3 ≤ p.t
      · have hz : v3 = 0 := by simp [v3, u3, min_eq_left h]
        right
        omega
      · have ht : u3 = p.t := min_eq_right (by omega)
        left
        omega
    have hcapacity : e 2 ≤ jp / 2 + jq / 2 := by
      rcases hparity with h | h <;> omega
    obtain ⟨u2, v2, hu2, hv2, huv2⟩ := split_cap hcapacity
    have hindex1 : e 1 ≤ (jp - 2 * u2) + (jq - 2 * v2) := by omega
    obtain ⟨u1, v1, hu1, hv1, huv1⟩ := split_cap hindex1
    have hspentP : u1 + 2 * u2 + 3 * u3 ≤ p.j := by omega
    have hspentQ : v1 + 2 * v2 + 3 * v3 ≤ q.j := by omega
    have htotal0 : e 0 ≤ (p.b - (u1 + u2 + u3)) + (q.b - (v1 + v2 + v3)) := by omega
    obtain ⟨u0, v0, hu0, hv0, huv0⟩ := split_cap htotal0
    refine ⟨![u0, u1, u2, u3], ?_, ![v0, v1, v2, v3], ?_, ?_⟩
    · change u0 + u1 + u2 + u3 ≤ p.b ∧ u1 + 2 * u2 + 3 * u3 ≤ p.j ∧ u3 ≤ p.t
      exact ⟨by omega, hspentP, hu3⟩
    · change v0 + v1 + v2 + v3 ≤ q.b ∧ v1 + 2 * v2 + 3 * v3 ≤ q.j ∧ v3 ≤ q.t
      exact ⟨by omega, hspentQ, hv3⟩
    · funext i
      fin_cases i
      · exact huv0
      · exact huv1
      · exact huv2
      · exact huv3
  · rintro ⟨u, hu, v, hv, rfl⟩
    obtain ⟨hub, huj, hut⟩ : u 0 + u 1 + u 2 + u 3 ≤ p.b ∧
        u 1 + 2 * u 2 + 3 * u 3 ≤ p.j ∧ u 3 ≤ p.t := hu
    obtain ⟨hvb, hvj, hvt⟩ : v 0 + v 1 + v 2 + v 3 ≤ q.b ∧
        v 1 + 2 * v 2 + 3 * v 3 ≤ q.j ∧ v 3 ≤ q.t := hv
    change (u 0 + v 0) + (u 1 + v 1) + (u 2 + v 2) + (u 3 + v 3) ≤ p.b + q.b ∧
      (u 1 + v 1) + 2 * (u 2 + v 2) + 3 * (u 3 + v 3) ≤ p.j + q.j ∧
      u 3 + v 3 ≤ p.t + q.t
    exact ⟨by omega, by omega, by omega⟩
theorem chamber_scale {p : Shape} (hp : Chamber p) (k : ℕ) :
    Chamber (p.scale k) := by
  refine ⟨Nat.mul_le_mul_left k hp.1, ?_⟩
  change 3 * (k * p.t) ≤ k * p.j
  rw [Nat.mul_left_comm 3 k]
  exact Nat.mul_le_mul_left k hp.2
theorem chamber_plus {p q : Shape} (hp : Chamber p) (hq : Chamber q) :
    Chamber (p.plus q) := by
  obtain ⟨hpb, hpt⟩ := hp
  obtain ⟨hqb, hqt⟩ := hq
  change p.j + q.j ≤ p.b + q.b ∧ 3 * (p.t + q.t) ≤ p.j + q.j
  omega
theorem exponents_plus_scaled {p q : Shape} (hp : Chamber p) (hq : Chamber q) :
    exponents ((p.plus q).scale 6) = exponents (p.scale 6) + exponents (q.scale 6) := by
  rw [show (p.plus q).scale 6 = (p.scale 6).plus (q.scale 6) from by
    cases p
    cases q
    simp [Shape.plus, Shape.scale, Nat.mul_add]]
  apply exponents_plus _ _ (chamber_scale hp 6) (chamber_scale hq 6) <;>
    change 6 * _ % 2 = 0 <;> omega
theorem latticeIndices_zero (p : Shape) : (0 : Fin 4 →₀ ℕ) ∈ latticeIndices p := by
  simp [latticeIndices, exponents]
theorem latticeIndices_single {p : Shape} (hp : FullChamber p) (i : Fin 4) :
    Finsupp.single i 1 ∈ latticeIndices p := by
  obtain ⟨⟨hpb, hpj⟩, hpt⟩ := hp
  fin_cases i <;> norm_num [latticeIndices, exponents, Shape.scale, Finsupp.single_apply] <;> omega
theorem latticeIndices_plus {p q : Shape} (hp : Chamber p) (hq : Chamber q) :
    latticeIndices (p.plus q) = latticeIndices p + latticeIndices q := by
  ext e
  change (fun i => e i) ∈ exponents ((p.plus q).scale 6) ↔
    ∃ u ∈ latticeIndices p, ∃ v ∈ latticeIndices q, u + v = e
  rw [exponents_plus_scaled hp hq]
  constructor
  · rintro ⟨u, hu, v, hv, he⟩
    refine ⟨Finsupp.equivFunOnFinite.symm u, hu, Finsupp.equivFunOnFinite.symm v, hv, ?_⟩
    ext i
    exact congrFun he i
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨fun i => u i, hu, fun i => v i, hv, rfl⟩
theorem latticeIndices_scale {p : Shape} (hp : Chamber p) (n : ℕ) :
    latticeIndices (p.scale n) = n • latticeIndices p := by
  induction n with
  | zero =>
    rw [show p.scale 0 = ⟨0, 0, 0⟩ from by simp [Shape.scale]]
    ext e
    change (fun i => e i) ∈ exponents ⟨0, 0, 0⟩ ↔ e ∈ (0 : ℕ) • latticeIndices p
    rw [exponents_zero, zero_smul, Set.mem_zero, Set.mem_singleton_iff]
    constructor
    · intro he
      ext i
      exact congrFun he i
    · rintro rfl
      rfl
  | succ n ih =>
    rw [show p.scale (n + 1) = (p.scale n).plus p from by
      cases p
      simp [Shape.scale, Shape.plus, Nat.add_mul]]
    rw [latticeIndices_plus (chamber_scale hp n) hp, ih, succ_nsmul]
private theorem monomial_preimage {S : Set (Fin 4 →₀ ℕ)} {n : ℕ}
    {e : Fin 4 →₀ ℕ} (he : e ∈ n • S) :
    ∃ P : MvPolynomial S GeoField, P.totalDegree ≤ n ∧
      MvPolynomial.monomialMap GeoField S P = MvPolynomial.monomial e 1 := by
  induction n generalizing e with
  | zero =>
    rw [zero_smul, Set.mem_zero] at he
    subst e
    exact ⟨1, by simp, by simp⟩
  | succ n ih =>
    rw [succ_nsmul] at he
    obtain ⟨u, hu, v, hv, rfl⟩ := he
    obtain ⟨P, hP, hmap⟩ := ih hu
    refine ⟨P * MvPolynomial.X ⟨v, hv⟩, ?_, ?_⟩
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by
        rw [MvPolynomial.totalDegree_X]
        omega)
    · rw [map_mul, hmap, MvPolynomial.monomialMap_X, MvPolynomial.monomial_mul_monomial, mul_one]
theorem monomialMap_filtration {p : Shape} (hp : Chamber p) (n : ℕ) :
    (MvPolynomial.restrictTotalDegree (latticeIndices p) GeoField n).map
      (MvPolynomial.monomialMap GeoField (latticeIndices p)).toLinearMap =
      MvPolynomial.restrictSupport GeoField (latticeIndices (p.scale n)) := by
  rw [latticeIndices_scale hp n]
  apply le_antisymm
  · rintro _ ⟨P, hP, rfl⟩
    exact MvPolynomial.monomialMap_mem_restrictSupport_nsmul (latticeIndices_zero p)
      ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp hP)
  · rw [MvPolynomial.restrictSupport_eq_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨P, hP, hmap⟩ := monomial_preimage he
    exact ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hP, hmap⟩
end K1_13_6_1_4_2
end
section
namespace K1_13_6_1_4_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_1_4
def c1 : Prop :=
  ∀ (surface : Ideal GeoJets) (a h : Shape),
    surface.IsPrime → ringKrullDim (GeoJets ⧸ surface) = 2 →
    FullChamber a → FullChamber h →
    (surfaceDegree surface (a.scale 6) (h.scale 6) : ℚ) =
      topCoeff surface (a.plus h) - topCoeff surface a - topCoeff surface h
def c2 : Prop :=
  ∀ (surface : Ideal GeoJets) (a b h : Shape),
    surface.IsPrime → ringKrullDim (GeoJets ⧸ surface) = 2 →
    FullChamber a → FullChamber b → FullChamber h →
    ∃ (aa bb hh ab ah bh : ℚ), ∀ i j k : ℕ, 0 < i + j + k →
      topCoeff surface (((a.scale i).plus (b.scale j)).plus (h.scale k)) =
        aa * (i : ℚ)^2 + bb * (j : ℚ)^2 + hh * (k : ℚ)^2 +
        ab * (i : ℚ) * (j : ℚ) + ah * (i : ℚ) * (k : ℚ) + bh * (j : ℚ) * (k : ℚ)
theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_1_4.c2 := by
  intro surface a b h m n hs hdim ha hb hh hm
  let p := (a.scale m).plus (b.scale n)
  have hp : FullChamber p := by
    refine ⟨chamber_plus (chamber_scale ha.1 m) (chamber_scale hb.1 n), ?_⟩
    change 0 < m * a.t + n * b.t
    have hpos := Nat.mul_pos hm ha.2
    omega
  obtain ⟨qa, qb, qh, qab, qah, qbh, hquad⟩ := h2 surface a b h hs hdim ha hb hh
  have htest : topCoeff surface h = qh := by
    simpa [Shape.scale, Shape.plus] using hquad 0 0 1 (by decide)
  have mixed (i j : ℕ) (hij : 0 < i + j) :
      topCoeff surface (((a.scale i).plus (b.scale j)).plus h) -
        topCoeff surface ((a.scale i).plus (b.scale j)) - topCoeff surface h =
        (i : ℚ) * qah + (j : ℚ) * qbh := by
    have hbase := hquad i j 0 (by omega)
    have hsum := hquad i j 1 (by omega)
    simp [Shape.scale, Shape.plus] at hbase hsum ⊢
    rw [hbase, hsum, htest]
    ring
  have hA : (surfaceDegree surface (a.scale 6) (h.scale 6) : ℚ) = qah := by
    refine (h1 surface a h hs hdim ha hh).trans ?_
    simpa [Shape.scale, Shape.plus] using mixed 1 0 (by decide)
  have hB : (surfaceDegree surface (b.scale 6) (h.scale 6) : ℚ) = qbh := by
    refine (h1 surface b h hs hdim hb hh).trans ?_
    simpa [Shape.scale, Shape.plus] using mixed 0 1 (by decide)
  have htotal :
      (surfaceDegree surface (p.scale 6) (h.scale 6) : ℚ) =
        (m : ℚ) * (surfaceDegree surface (a.scale 6) (h.scale 6) : ℚ) +
        (n : ℚ) * (surfaceDegree surface (b.scale 6) (h.scale 6) : ℚ) := by
    rw [hA, hB, h1 surface p h hs hdim hp hh]
    exact mixed m n (by omega)
  exact le_of_eq (by exact_mod_cast htotal)
end
end K1_13_6_1_4_2
end
section
namespace K1_13_6_1_4_2_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_1 K1_13_7_1 K1_13_6_1_4 K1_13_6_1_4_2
def piece {k : Type*} [Field k] (I : Ideal (MvPolynomial (Fin 4) k)) (p : Shape) :
    Submodule k (MvPolynomial (Fin 4) k ⧸ I) :=
  (MvPolynomial.restrictSupport k (latticeIndices p)).map (Ideal.Quotient.mkₐ k I).toLinearMap
abbrev Coeff (a h : Shape) := PairSectionField (a.scale 6) (h.scale 6)
def extendIdeal (surface : Ideal GeoJets) (a h : Shape) :
    Ideal (MvPolynomial (Fin 4) (Coeff a h)) :=
  surface.map (MvPolynomial.map (algebraMap GeoField (Coeff a h)))
abbrev SurfaceRing (surface : Ideal GeoJets) (a h : Shape) :=
  MvPolynomial (Fin 4) (Coeff a h) ⧸ extendIdeal surface a h
def leftSection (a h : Shape) : MvPolynomial (Fin 4) (Coeff a h) :=
  sectionWith (a.scale 6) (Sum.inl : SectionIndex (a.scale 6) → PairSectionIndex (a.scale 6) (h.scale 6))
def rightSection (a h : Shape) : MvPolynomial (Fin 4) (Coeff a h) :=
  sectionWith (h.scale 6) (Sum.inr : SectionIndex (h.scale 6) → PairSectionIndex (a.scale 6) (h.scale 6))
def cutIdeal (surface : Ideal GeoJets) (a h : Shape) :
    Ideal (MvPolynomial (Fin 4) (Coeff a h)) :=
  extendIdeal surface a h ⊔ Ideal.span {leftSection a h, rightSection a h}
abbrev CutRing (surface : Ideal GeoJets) (a h : Shape) :=
  MvPolynomial (Fin 4) (Coeff a h) ⧸ cutIdeal surface a h
def cutMap (surface : Ideal GeoJets) (a h : Shape) :
    SurfaceRing surface a h →ₐ[Coeff a h] CutRing surface a h :=
  Ideal.quotientMapₐ _ (AlgHom.id _ _) (by
    change extendIdeal surface a h ≤ cutIdeal surface a h
    exact le_sup_left)
def biPiece (surface : Ideal GeoJets) (a h : Shape) (i j : ℕ) :
    Submodule (Coeff a h) (SurfaceRing surface a h) :=
  piece (extendIdeal surface a h) ((a.scale i).plus (h.scale j))
def leftMul (surface : Ideal GeoJets) (a h : Shape) :
    SurfaceRing surface a h →ₗ[Coeff a h] SurfaceRing surface a h :=
  LinearMap.mulLeft _ (Ideal.Quotient.mk (extendIdeal surface a h) (leftSection a h))
def rightMul (surface : Ideal GeoJets) (a h : Shape) :
    SurfaceRing surface a h →ₗ[Coeff a h] SurfaceRing surface a h :=
  LinearMap.mulLeft _ (Ideal.Quotient.mk (extendIdeal surface a h) (rightSection a h))
end
end K1_13_6_1_4_2_1
end
section
namespace K1_13_6_1_4_2_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_1_4 K1_13_6_1_4_2 MvPolynomial
instance {k : Type*} [Field k] (I : Ideal (MvPolynomial (Fin 4) k)) (p : Shape) :
    Module.Finite k (piece I p) := by
  let := Module.Finite.of_basis (basisRestrictSupport k (latticeIndices p))
  unfold piece
  infer_instance
instance (surface : Ideal GeoJets) (a h : Shape) (i j : ℕ) :
    Module.Finite (Coeff a h) (biPiece surface a h i j) := by
  unfold biPiece
  infer_instance
theorem quotientDegreeLE_le_cutPiece (surface : Ideal GeoJets) (a h : Shape)
    (ha : FullChamber a) {N i j : ℕ} (hi : N ≤ i) :
    quotientDegreeLE (cutIdeal surface a h) N ≤
      (biPiece surface a h i j).map (cutMap surface a h).toLinearMap := by
  intro x hx
  obtain ⟨P, hP, rfl⟩ := mem_quotientDegreeLE.mp hx
  have hat := ha.2
  have haj := ha.1.2
  have hab := ha.1.1
  have haT : i ≤ i * a.t := Nat.le_mul_of_pos_right i hat
  have haJ : 3 * i ≤ i * a.j := by
    rw [Nat.mul_comm 3 i]
    exact Nat.mul_le_mul_left _ (by omega)
  have haB : i ≤ i * a.b := by
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hmem : P ∈ restrictSupport (Coeff a h) (latticeIndices ((a.scale i).plus (h.scale j))) := by
    intro e he
    have hdeg := (le_totalDegree he).trans hP
    change e.degree ≤ N at hdeg
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_four] at hdeg
    change e 0 + e 1 + e 2 + e 3 ≤ 6 * (i * a.b + j * h.b) ∧
      e 1 + 2 * e 2 + 3 * e 3 ≤ 6 * (i * a.j + j * h.j) ∧
      e 3 ≤ 6 * (i * a.t + j * h.t)
    exact ⟨by omega, by omega, by omega⟩
  refine ⟨Ideal.Quotient.mk (extendIdeal surface a h) P, ⟨P, hmem, rfl⟩, ?_⟩
  rfl
theorem mixed_difference (surface : Ideal GeoJets) (a h : Shape) (i j : ℕ)
    (hl : Function.Injective (leftMul surface a h))
    (hr : Function.Injective (rightMul surface a h))
    (hinter : (biPiece surface a h i (j + 1)).map (leftMul surface a h) ⊓
        (biPiece surface a h (i + 1) j).map (rightMul surface a h) =
      (biPiece surface a h i j).map ((leftMul surface a h).comp (rightMul surface a h)))
    (hker : biPiece surface a h (i + 1) (j + 1) ⊓ LinearMap.ker (cutMap surface a h).toLinearMap =
        (biPiece surface a h i (j + 1)).map (leftMul surface a h) ⊔
          (biPiece surface a h (i + 1) j).map (rightMul surface a h)) :
    (Module.finrank (Coeff a h) (biPiece surface a h (i + 1) (j + 1)) : ℚ) -
      (Module.finrank (Coeff a h) (biPiece surface a h i (j + 1)) : ℚ) -
      (Module.finrank (Coeff a h) (biPiece surface a h (i + 1) j) : ℚ) +
      (Module.finrank (Coeff a h) (biPiece surface a h i j) : ℚ) =
      (Module.finrank (Coeff a h)
        ((biPiece surface a h (i + 1) (j + 1)).map (cutMap surface a h).toLinearMap) : ℚ) := by
  let W := biPiece surface a h (i + 1) (j + 1)
  let q := (cutMap surface a h).toLinearMap
  let f := q.comp W.subtype
  let U := (biPiece surface a h i (j + 1)).map (leftMul surface a h)
  let V := (biPiece surface a h (i + 1) j).map (rightMul surface a h)
  have hmap : (LinearMap.ker f).map W.subtype = U ⊔ V := by
    rw [← hker]
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, hz⟩
    · rintro ⟨hx, hqx⟩
      exact ⟨⟨x, hx⟩, hqx, rfl⟩
  have hrange : LinearMap.range f = W.map q := by
    dsimp only [f]
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hK : Module.finrank (Coeff a h) (LinearMap.ker f) = Module.finrank (Coeff a h) ↑(U ⊔ V) := by
    rw [← hmap]
    exact (Submodule.equivMapOfInjective _ Subtype.val_injective _).finrank_eq
  have hsum := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, hK] at hsum
  have huv := Submodule.finrank_sup_add_finrank_inf_eq U V
  change Module.finrank (Coeff a h) ↑(U ⊔ V) + Module.finrank (Coeff a h)
    ↑((biPiece surface a h i (j + 1)).map (leftMul surface a h) ⊓
      (biPiece surface a h (i + 1) j).map (rightMul surface a h)) =
    Module.finrank (Coeff a h) U + Module.finrank (Coeff a h) V at huv
  have hcomp : Function.Injective ((leftMul surface a h).comp (rightMul surface a h)) :=
    fun _ _ hxy => hr (hl hxy)
  rw [hinter, ← (Submodule.equivMapOfInjective _ hcomp (biPiece surface a h i j)).finrank_eq] at huv
  have hu := (Submodule.equivMapOfInjective _ hl (biPiece surface a h i (j + 1))).finrank_eq
  have hv := (Submodule.equivMapOfInjective _ hr (biPiece surface a h (i + 1) j)).finrank_eq
  change Module.finrank (Coeff a h) (biPiece surface a h i (j + 1)) = _ at hu
  change Module.finrank (Coeff a h) (biPiece surface a h (i + 1) j) = _ at hv
  rw [show Module.finrank (Coeff a h) U = _ from hu.symm,
    show Module.finrank (Coeff a h) V = _ from hv.symm] at huv
  have hnat : Module.finrank (Coeff a h) W + Module.finrank (Coeff a h) (biPiece surface a h i j) =
      Module.finrank (Coeff a h) (W.map q) +
        Module.finrank (Coeff a h) (biPiece surface a h i (j + 1)) +
        Module.finrank (Coeff a h) (biPiece surface a h (i + 1) j) := by omega
  have hrat := congrArg (fun x : ℕ => (x : ℚ)) hnat
  push_cast at hrat
  change (Module.finrank (Coeff a h) W : ℚ) - _ - _ + _ = (Module.finrank (Coeff a h) (W.map q) : ℚ)
  linarith
end
end K1_13_6_1_4_2_1
end
section
namespace K1_13_6_1_4_2_1
noncomputable section
open K1_13 K1_13_6 K1_13_7_1 K1_13_6_1_4 K1_13_6_1_4_2 MvPolynomial
open scoped TensorProduct Polynomial
section ScalarExtension
variable {k L : Type*} [Field k] [Field L] [Algebra k L]
abbrev mapIdeal (I : Ideal (MvPolynomial (Fin 4) k)) : Ideal (MvPolynomial (Fin 4) L) :=
  I.map (MvPolynomial.map (algebraMap k L))
private def baseQuot (I : Ideal (MvPolynomial (Fin 4) k)) :
    L ⊗[k] (MvPolynomial (Fin 4) k ⧸ I) ≃ₐ[L] MvPolynomial (Fin 4) L ⧸ mapIdeal I := by
  let e := algebraTensorAlgEquiv (σ := Fin 4) k L
  refine (Algebra.TensorProduct.tensorQuotientEquiv L (MvPolynomial (Fin 4) k) L I).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  change I.map (MvPolynomial.map (algebraMap k L)) =
    (I.map (Algebra.TensorProduct.includeRight (A := L)).toRingHom).map
      e.toRingEquiv.toRingHom
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro P
  change MvPolynomial.map (algebraMap k L) P = e (1 ⊗ₜ[k] P)
  simp [e]
private theorem baseQuot_tmul (I : Ideal (MvPolynomial (Fin 4) k)) (c : L)
    (P : MvPolynomial (Fin 4) k) :
    baseQuot I (c ⊗ₜ[k] Ideal.Quotient.mk I P) =
      c • Ideal.Quotient.mk (mapIdeal I) (MvPolynomial.map (algebraMap k L) P) := by
  unfold baseQuot
  simp only [AlgEquiv.trans_apply, Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
    Ideal.quotientEquivAlg_mk, MvPolynomial.algebraTensorAlgEquiv_tmul]
  exact map_smul (Ideal.Quotient.mkₐ L (mapIdeal I)) c _
theorem finrank_piece_baseChange (I : Ideal (MvPolynomial (Fin 4) k)) (p : Shape) :
    Module.finrank L (piece (mapIdeal (L := L) I) p) = Module.finrank k (piece I p) := by
  classical
  let W := piece I p
  let V := piece (mapIdeal (L := L) I) p
  let f : L ⊗[k] W →ₗ[L] MvPolynomial (Fin 4) L ⧸ mapIdeal I :=
    (baseQuot I).toLinearEquiv.toLinearMap.comp
      (TensorProduct.AlgebraTensorModule.lTensor L L W.subtype)
  have hcalc (c : L) (z : W) : f (c ⊗ₜ[k] z) = baseQuot I (c ⊗ₜ[k] z.val) := rfl
  have hinj : Function.Injective f := (baseQuot I).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap W.subtype Subtype.val_injective)
  have hrange : LinearMap.range f = V := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      induction z using TensorProduct.inductionOn with
      | tmul c z =>
        obtain ⟨P, hP, he⟩ := z.property
        have hval : Ideal.Quotient.mk I P = z.val := he
        rw [hcalc, ← hval, baseQuot_tmul]
        apply V.smul_mem
        refine ⟨_, ?_, rfl⟩
        intro e he
        exact hP (support_map_subset (algebraMap k L) P he)
      | add x y hx hy => simpa only [map_add] using V.add_mem hx hy
    · change piece (mapIdeal (L := L) I) p ≤ _
      unfold piece
      rw [restrictSupport_eq_span, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
      let z : W := ⟨Ideal.Quotient.mk I (monomial e 1),
        ⟨monomial e 1, by
          rw [restrictSupport_eq_span]
          exact Submodule.subset_span ⟨e, he, rfl⟩, rfl⟩⟩
      refine ⟨(1 : L) ⊗ₜ[k] z, ?_⟩
      rw [hcalc, show z.val = Ideal.Quotient.mk I (monomial e 1) from rfl, baseQuot_tmul]
      simp [MvPolynomial.map_monomial]
  let e := (LinearEquiv.ofInjective f hinj).trans (LinearEquiv.ofEq _ _ hrange)
  exact e.finrank_eq.symm.trans Module.finrank_baseChange
end ScalarExtension
abbrev hilbertIdeal (surface : Ideal GeoJets) (p : Shape) :=
  surface.comap (monomialMap GeoField (latticeIndices p)).toRingHom
abbrev hilbertPoly (surface : Ideal GeoJets) (p : Shape) :=
  affineHilbertPolynomial (hilbertIdeal surface p)
theorem hilbertFunction_eq_piece (surface : Ideal GeoJets) {p : Shape}
    (hp : Chamber p) (n : ℕ) :
    affineHilbertFunction (hilbertIdeal surface p) n =
      Module.finrank GeoField (piece surface (p.scale n)) := by
  let φ := (Ideal.Quotient.mkₐ GeoField surface).comp (monomialMap GeoField (latticeIndices p))
  have hker : RingHom.ker φ.toRingHom = hilbertIdeal surface p := by
    ext x
    simp [φ, RingHom.mem_ker, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem]
  let j := Ideal.kerLiftAlg φ
  let V := quotientDegreeLE (RingHom.ker φ.toRingHom) n
  have hmap : V.map j.toLinearMap = piece surface (p.scale n) := by
    change ((restrictTotalDegree (latticeIndices p) GeoField n).map
      (Ideal.Quotient.mkₐ _ _).toLinearMap).map _ = _
    rw [← Submodule.map_comp, show j.toLinearMap.comp (Ideal.Quotient.mkₐ _ _).toLinearMap =
      φ.toLinearMap from rfl]
    change (restrictTotalDegree (latticeIndices p) GeoField n).map
      ((Ideal.Quotient.mkₐ GeoField surface).toLinearMap.comp
        (monomialMap GeoField (latticeIndices p)).toLinearMap) = _
    rw [Submodule.map_comp, monomialMap_filtration hp]
    rfl
  rw [← hker]
  exact (Submodule.equivMapOfInjective _ (Ideal.kerLiftAlg_injective φ) V).finrank_eq.trans
    (congrArg (fun S : Submodule GeoField (GeoJets ⧸ surface) => Module.finrank GeoField S) hmap)
theorem ringKrullDim_ge_of_finite_injective {k A : Type*}
    [Field k] [CommRing A] [IsDomain A] {d : ℕ}
    (f : MvPolynomial (Fin d) k →+* A) (hf : Function.Injective f) (hfin : f.Finite) :
    (d : WithBot ℕ∞) ≤ ringKrullDim A := by
  let B := MvPolynomial (Fin d) k
  let algebra := f.toAlgebra
  let := algebra
  let faithful : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective _ _).mpr hf
  let finite : Module.Finite B A := hfin
  have hB : ringKrullDim B = (d : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    simp
  obtain ⟨b, hb, hbheight⟩ := Ideal.exists_isPrime_le_height (n := d) hB.ge
  obtain ⟨z, hz⟩ := Algebra.IsIntegral.comap_surjective B A (⟨b, hb⟩ : PrimeSpectrum B)
  have hzb : z.asIdeal.under B = b := congrArg PrimeSpectrum.asIdeal hz
  have hzheight := Ideal.height_under_le_height (R := B) z.asIdeal
  rw [hzb] at hzheight
  calc
    _ ≤ (z.asIdeal.height : WithBot ℕ∞) := WithBot.coe_le_coe.mpr (hbheight.trans hzheight)
    _ ≤ ringKrullDim A := Ideal.height_le_ringKrullDim_of_isPrime
theorem hilbertPoly_degree_le (surface : Ideal GeoJets) (hs : surface.IsPrime)
    (hdim : ringKrullDim (GeoJets ⧸ surface) = 2) (p : Shape) :
    (hilbertPoly surface p).natDegree ≤ 2 := by
  let := hs
  obtain ⟨d, f, hf, hfin⟩ :=
    exists_finite_inj_algHom_of_fg GeoField (GeoJets ⧸ surface)
  have hdeg := natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective f hfin hf
  rw [Nat.card_fin] at hdeg
  have hd₀ := ringKrullDim_ge_of_finite_injective f.toRingHom hf hfin
  rw [hdim] at hd₀
  have hd : d ≤ 2 := by exact_mod_cast hd₀
  let f₀ := monomialMap GeoField (latticeIndices p)
  have hmono : Function.Injective (Ideal.quotientMapₐ surface f₀ le_rfl) :=
    Ideal.quotientMap_injective (I := surface) (f := f₀.toRingHom)
  exact (natDegree_affineHilbertPolynomial_le_of_injective _ hmono).trans (hdeg.trans_le hd)
theorem piece_le {k : Type*} [Field k] (I : Ideal (MvPolynomial (Fin 4) k)) {p q : Shape}
    (hb : p.b ≤ q.b) (hj : p.j ≤ q.j) (ht : p.t ≤ q.t) :
    piece I p ≤ piece I q := by
  apply Submodule.map_mono
  apply restrictSupport_mono
  intro e he
  exact ⟨he.1.trans (Nat.mul_le_mul_left 6 hb), he.2.1.trans (Nat.mul_le_mul_left 6 hj),
    he.2.2.trans (Nat.mul_le_mul_left 6 ht)⟩
theorem axis_bounds {k : Type*} [Field k] (I : Ideal (MvPolynomial (Fin 4) k))
    {p : Shape} (hp : FullChamber p) (q : Shape) (N : ℕ) :
    ∃ s : ℕ, ∀ n : ℕ,
      piece I (p.scale n) ≤ piece I ((p.scale n).plus (q.scale N)) ∧
      piece I ((p.scale n).plus (q.scale N)) ≤ piece I (p.scale (n + s)) := by
  let s := N * (q.b + q.j + q.t)
  have hpb := hp.1.1
  have hpj := hp.1.2
  have hpt := hp.2
  have hb : N * q.b ≤ s * p.b :=
    (Nat.mul_le_mul_left N (by omega : q.b ≤ q.b + q.j + q.t)).trans
      (Nat.le_mul_of_pos_right s (by omega))
  have hj : N * q.j ≤ s * p.j :=
    (Nat.mul_le_mul_left N (by omega : q.j ≤ q.b + q.j + q.t)).trans
      (Nat.le_mul_of_pos_right s (by omega))
  have ht : N * q.t ≤ s * p.t :=
    (Nat.mul_le_mul_left N (by omega : q.t ≤ q.b + q.j + q.t)).trans
      (Nat.le_mul_of_pos_right s hp.2)
  refine ⟨s, fun n => ⟨piece_le I (Nat.le_add_right ..) (Nat.le_add_right ..)
    (Nat.le_add_right ..), piece_le I ?_ ?_ ?_⟩⟩
  · simpa [Shape.scale, Shape.plus, Nat.add_mul] using Nat.add_le_add_left hb (n * p.b)
  · simpa [Shape.scale, Shape.plus, Nat.add_mul] using Nat.add_le_add_left hj (n * p.j)
  · simpa [Shape.scale, Shape.plus, Nat.add_mul] using Nat.add_le_add_left ht (n * p.t)
private theorem rectangle (H : ℕ → ℕ → ℚ) (d : ℚ) (N : ℕ)
    (hd : ∀ i j : ℕ, N ≤ i → N ≤ j →
      H (i + 1) (j + 1) - H i (j + 1) - H (i + 1) j + H i j = d) :
    ∀ i j : ℕ,
      H (N + i) (N + j) + H N N = H (N + i) N + H N (N + j) + d * (i : ℚ) * (j : ℚ) := by
  intro i
  induction i with
  | zero => intro j; simp [add_comm]
  | succ i ih =>
    intro j
    induction j with
    | zero => simp
    | succ j ihj =>
      have hstep := hd (N + i) (N + j) (by omega) (by omega)
      have h₁ := ih (j + 1)
      have h₂ := ih j
      simp only [← Nat.add_assoc, Nat.cast_add, Nat.cast_one] at h₁ ihj ⊢
      linear_combination hstep + h₁ + ihj - h₂
private def shift (P : ℚ[X]) (n : ℕ) : ℚ[X] :=
  P.comp (Polynomial.X + Polynomial.C (n : ℚ))
private theorem shift_degree (P : ℚ[X]) (n : ℕ) :
    (shift P n).natDegree ≤ P.natDegree := by
  have hh := Polynomial.natDegree_comp_le (p := P) (q := Polynomial.X + Polynomial.C (n : ℚ))
  rw [Polynomial.natDegree_X_add_C, mul_one] at hh
  exact hh
theorem shift_coeff (P : ℚ[X]) (n : ℕ) (h : P.natDegree ≤ 2) :
    (shift P n).coeff 2 = P.coeff 2 := by
  by_cases he : P.natDegree = 2
  · have hl : P.leadingCoeff = P.coeff 2 := by rw [← Polynomial.coeff_natDegree, he]
    have hh := Polynomial.coeff_comp_degree_mul_degree (p := P)
      (q := Polynomial.X + Polynomial.C (n : ℚ)) (by rw [Polynomial.natDegree_X_add_C]; decide)
    rw [he, Polynomial.natDegree_X_add_C, Polynomial.leadingCoeff_X_add_C, mul_one,
      one_pow, mul_one, hl] at hh
    exact hh
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((shift_degree P n).trans_lt (by omega)),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < 2)]
private theorem left_axis (a h : Shape) (n : ℕ) :
    (a.scale n).plus (h.scale 0) = a.scale n := by
  cases a
  cases h
  simp [Shape.scale, Shape.plus]
private theorem right_axis (a h : Shape) (n : ℕ) :
    (a.scale 0).plus (h.scale n) = h.scale n := by
  cases a
  cases h
  simp [Shape.scale, Shape.plus]
theorem plus_comm (a h : Shape) : a.plus h = h.plus a := by
  cases a
  cases h
  simp [Shape.plus, Nat.add_comm]
private theorem scale_plus (a h : Shape) (n : ℕ) :
    (a.plus h).scale n = (a.scale n).plus (h.scale n) := by
  cases a
  cases h
  simp [Shape.scale, Shape.plus, Nat.mul_add]
def pieceRank {k : Type*} [Field k] (I : Ideal (MvPolynomial (Fin 4) k))
    (p : Shape) : ℕ :=
  Module.finrank k (piece I p)
theorem exists_eval_finrank_piece (surface : Ideal GeoJets) (a h : Shape)
    {p : Shape} (hp : Chamber p) :
    ∃ M : ℕ, ∀ n ≥ M, (hilbertPoly surface p).eval (n : ℚ) =
      (pieceRank (extendIdeal surface a h) (p.scale n) : ℚ) := by
  obtain ⟨M, hM⟩ := exists_eval_affineHilbertPolynomial (hilbertIdeal surface p)
  exact ⟨M, fun n hn => by
    rw [hM n hn, hilbertFunction_eq_piece surface hp n]
    unfold pieceRank
    exact_mod_cast (finrank_piece_baseChange (L := Coeff a h) surface (p.scale n)).symm⟩
theorem polarize (surface : Ideal GeoJets) (a h : Shape) (hs : surface.IsPrime)
    (hdim : ringKrullDim (GeoJets ⧸ surface) = 2) (ha : FullChamber a) (hh : FullChamber h)
    (hmix : ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j →
      (Module.finrank (Coeff a h) (biPiece surface a h (i + 1) (j + 1)) : ℚ) -
        (Module.finrank (Coeff a h) (biPiece surface a h i (j + 1)) : ℚ) -
        (Module.finrank (Coeff a h) (biPiece surface a h (i + 1) j) : ℚ) +
        (Module.finrank (Coeff a h) (biPiece surface a h i j) : ℚ) =
        (surfaceDegree surface (a.scale 6) (h.scale 6) : ℚ)) :
    (surfaceDegree surface (a.scale 6) (h.scale 6) : ℚ) =
      topCoeff surface (a.plus h) - topCoeff surface a - topCoeff surface h := by
  let I := extendIdeal surface a h
  let H (i j : ℕ) : ℚ :=
    pieceRank (extendIdeal surface a h) ((a.scale i).plus (h.scale j))
  let d : ℚ := surfaceDegree surface (a.scale 6) (h.scale 6)
  obtain ⟨N, hN⟩ := hmix
  have hrect := rectangle H d N hN
  obtain ⟨r, hr⟩ := axis_bounds I ha h N
  obtain ⟨s, ht⟩ := axis_bounds I hh a N
  have hre (n : ℕ) : H n 0 ≤ H n N ∧ H n N ≤ H (n + r) 0 := by
    simp only [H, left_axis]
    unfold pieceRank
    exact ⟨by exact_mod_cast Submodule.finrank_mono (hr n).1,
      by exact_mod_cast Submodule.finrank_mono (hr n).2⟩
  have hse (n : ℕ) : H 0 n ≤ H N n ∧ H N n ≤ H 0 (n + s) := by
    simp only [H, right_axis]
    rw [plus_comm (a.scale N) (h.scale n)]
    unfold pieceRank
    exact ⟨by exact_mod_cast Submodule.finrank_mono (ht n).1,
      by exact_mod_cast Submodule.finrank_mono (ht n).2⟩
  let P := hilbertPoly surface a
  let Q := hilbertPoly surface h
  let R := hilbertPoly surface (a.plus h)
  obtain ⟨MP, hMP⟩ := exists_eval_finrank_piece surface a h ha.1
  obtain ⟨MQ, hMQ⟩ := exists_eval_finrank_piece surface a h hh.1
  obtain ⟨MR, hMR⟩ := exists_eval_finrank_piece surface a h (chamber_plus ha.1 hh.1)
  have hPe (n : ℕ) (hn : MP ≤ n) : P.eval (n : ℚ) = H n 0 := by
    simpa only [P, H, left_axis] using hMP n hn
  have hQe (n : ℕ) (hn : MQ ≤ n) : Q.eval (n : ℚ) = H 0 n := by
    simpa only [Q, H, right_axis] using hMQ n hn
  have hRe (n : ℕ) (hn : MR ≤ n) : R.eval (n : ℚ) = H n n := by
    simpa only [R, H, scale_plus] using hMR n hn
  have hshift (A : ℚ[X]) (b n : ℕ) :
      (shift A b).eval (n : ℚ) = A.eval ((n + b : ℕ) : ℚ) := by
    simp [shift, Polynomial.eval_comp, Nat.cast_add]
  let C0 := Polynomial.C (H N N)
  let S := Polynomial.C d * Polynomial.X ^ 2
  let lower := shift P N + shift Q N + S - C0
  let upper := shift P (N + r) + shift Q (N + s) + S - C0
  let diag := shift R N
  have hbounds : ∀ᶠ n : ℕ in Filter.atTop,
      lower.eval (n : ℚ) ≤ diag.eval (n : ℚ) ∧ diag.eval (n : ℚ) ≤ upper.eval (n : ℚ) := by
    refine Filter.eventually_atTop.mpr ⟨max MP (max MQ MR), fun n hn => ?_⟩
    have hL := hre (N + n)
    have hU := hse (N + n)
    have hrec := hrect n n
    have hnP : MP ≤ n + N := by omega
    have hnQ : MQ ≤ n + N := by omega
    have hnR : MR ≤ n + N := by omega
    have hnPr : MP ≤ n + (N + r) := by omega
    have hnQs : MQ ≤ n + (N + s) := by omega
    simp only [lower, upper, diag, C0, S, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C, hshift,
      hPe _ hnP, hQe _ hnQ, hRe _ hnR, hPe _ hnPr, hQe _ hnQs, pow_two]
    rw [show n + N = N + n by omega, show n + (N + r) = N + n + r by omega,
      show n + (N + s) = N + n + s by omega]
    exact ⟨by nlinarith only [hL.1, hU.1, hrec], by nlinarith only [hL.2, hU.2, hrec]⟩
  have hp := hilbertPoly_degree_le surface hs hdim a
  have hq := hilbertPoly_degree_le surface hs hdim h
  have hd := hilbertPoly_degree_le surface hs hdim (a.plus h)
  have hdeg (i j : ℕ) : (shift P i + shift Q j + S - C0).natDegree ≤ 2 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · exact (Polynomial.natDegree_add_le _ _).trans
          (max_le ((shift_degree P i).trans hp) ((shift_degree Q j).trans hq))
      · exact Polynomial.natDegree_C_mul_X_pow_le _ _
    · simp [C0]
  have hlo := Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le
    (hdeg N N) ((shift_degree R N).trans hd) (hbounds.mono fun _ h => h.1)
  have hhi := Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le
    ((shift_degree R N).trans hd) (hdeg (N + r) (N + s)) (hbounds.mono fun _ h => h.2)
  have hc (i j : ℕ) : (shift P i + shift Q j + S - C0).coeff 2 = P.coeff 2 + Q.coeff 2 + d := by
    simp [S, C0, shift_coeff P i hp, shift_coeff Q j hq]
  change (shift P N + shift Q N + S - C0).coeff 2 ≤ (shift R N).coeff 2 at hlo
  change (shift R N).coeff 2 ≤ (shift P (N + r) + shift Q (N + s) + S - C0).coeff 2 at hhi
  rw [hc, shift_coeff R N hd] at hlo
  rw [hc, shift_coeff R N hd] at hhi
  change d = R.coeff 2 - P.coeff 2 - Q.coeff 2
  linarith
abbrev cutPiece (surface : Ideal GeoJets) (a h : Shape) (i j : ℕ) :=
  (biPiece surface a h i j).map (cutMap surface a h).toLinearMap
theorem cutPiece_mono (surface : Ideal GeoJets) (a h : Shape)
    {i j i' j' : ℕ} (hi : i ≤ i') (hj : j ≤ j') :
    cutPiece surface a h i j ≤ cutPiece surface a h i' j' := by
  apply Submodule.map_mono
  exact piece_le _ (Nat.add_le_add (Nat.mul_le_mul_right _ hi) (Nat.mul_le_mul_right _ hj))
    (Nat.add_le_add (Nat.mul_le_mul_right _ hi) (Nat.mul_le_mul_right _ hj))
    (Nat.add_le_add (Nat.mul_le_mul_right _ hi) (Nat.mul_le_mul_right _ hj))
theorem rectangle_le (H : ℕ → ℕ → ℚ) (d : ℚ) (N : ℕ)
    (hle : ∀ i j : ℕ, N ≤ i → N ≤ j →
      d ≤ H (i + 1) (j + 1) - H i (j + 1) - H (i + 1) j + H i j) :
    ∀ i j : ℕ, H (N + i) N + H N (N + j) + d * (j : ℚ) * (i : ℚ) ≤
      H (N + i) (N + j) + H N N := by
  have vertical (i j : ℕ) :
      d * (j : ℚ) ≤ H (N + i + 1) (N + j) - H (N + i) (N + j) -
        H (N + i + 1) N + H (N + i) N := by
    induction j with
    | zero => simp
    | succ j hj =>
      have hstep := hle (N + i) (N + j) (by omega) (by omega)
      simp only [← Nat.add_assoc, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      linarith only [hj, hstep]
  intro i j
  induction i with
  | zero => simp [add_comm]
  | succ i hi =>
    have hstep := vertical i j
    simp only [← Nat.add_assoc, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
    linarith only [hi, hstep]
theorem exists_stable_cutPiece (surface : Ideal GeoJets) (a h : Shape)
    (hprime : surface.IsPrime) (hdim : ringKrullDim (GeoJets ⧸ surface) = 2)
    (ha : FullChamber a) (hh : FullChamber h) (N : ℕ)
    (hdiff : ∀ i j : ℕ, N ≤ i → N ≤ j →
      (Module.finrank (Coeff a h) (biPiece surface a h (i + 1) (j + 1)) : ℚ) -
        (Module.finrank (Coeff a h) (biPiece surface a h i (j + 1)) : ℚ) -
        (Module.finrank (Coeff a h) (biPiece surface a h (i + 1) j) : ℚ) +
        (Module.finrank (Coeff a h) (biPiece surface a h i j) : ℚ) =
        (Module.finrank (Coeff a h)
          ((biPiece surface a h (i + 1) (j + 1)).map (cutMap surface a h).toLinearMap) : ℚ)) :
    ∃ M : ℕ, ∀ i j : ℕ, M ≤ i → M ≤ j →
      (biPiece surface a h i j).map (cutMap surface a h).toLinearMap = ⊤ := by
  classical
  let H (i j : ℕ) : ℚ :=
    pieceRank (extendIdeal surface a h) ((a.scale i).plus (h.scale j))
  let E (n : ℕ) := Module.finrank (Coeff a h) (cutPiece surface a h n n)
  let R := hilbertPoly surface (a.plus h)
  obtain ⟨MR, hMR⟩ := exists_eval_finrank_piece surface a h (chamber_plus ha.1 hh.1)
  have hRe (n : ℕ) (hn : MR ≤ n) : R.eval (n : ℚ) = H n n := by
    simpa only [R, H, scale_plus] using hMR n hn
  have hr := hilbertPoly_degree_le surface hprime hdim (a.plus h)
  have hbound (k : ℕ) : (E k : ℚ) ≤ R.coeff 2 := by
    let T := max N k
    have hTk : k ≤ T := le_max_right _ _
    have hTN : N ≤ T := le_max_left _ _
    have hl (i j : ℕ) (hi : T ≤ i) (hj : T ≤ j) :
        (E k : ℚ) ≤ H (i + 1) (j + 1) - H i (j + 1) - H (i + 1) j + H i j := by
      have heq : H (i + 1) (j + 1) - H i (j + 1) - H (i + 1) j + H i j =
          (Module.finrank (Coeff a h) (cutPiece surface a h (i + 1) (j + 1)) : ℚ) :=
        hdiff i j (hTN.trans hi) (hTN.trans hj)
      rw [heq]
      exact_mod_cast Submodule.finrank_mono
        (cutPiece_mono surface a h (hTk.trans (hi.trans (Nat.le_succ _)))
          (hTk.trans (hj.trans (Nat.le_succ _))))
    have hev : ∀ᶠ n : ℕ in Filter.atTop,
        (Polynomial.C (E k : ℚ) * Polynomial.X ^ 2).eval (n : ℚ) ≤
          (shift R T + Polynomial.C (H T T)).eval (n : ℚ) := by
      refine Filter.eventually_atTop.mpr ⟨MR, fun n hn => ?_⟩
      have hrec := rectangle_le H (E k : ℚ) T hl n n
      have hnonneg (i j : ℕ) : 0 ≤ H i j := Nat.cast_nonneg _
      have hRn := hRe (T + n) (by omega)
      simp only [shift, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, ← Nat.cast_add]
      rw [Nat.add_comm n T, hRn, pow_two]
      nlinarith only [hrec, hnonneg (T + n) T, hnonneg T (T + n)]
    have hdeg : (shift R T + Polynomial.C (H T T)).natDegree ≤ 2 :=
      (Polynomial.natDegree_add_le _ _).trans <| max_le ((shift_degree R T).trans hr) (by simp)
    have hcompare := Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le
      (Polynomial.natDegree_C_mul_X_pow_le (E k : ℚ) 2) hdeg hev
    simpa [Polynomial.coeff_C_mul_X_pow, shift_coeff R T hr] using hcompare
  obtain ⟨B, hB⟩ := exists_nat_gt (R.coeff 2)
  have hB' (n : ℕ) : E n ≤ B := by exact_mod_cast (hbound n).trans hB.le
  let S := (Finset.range (B + 1)).filter fun k => ∃ n, E n = k
  have hmem (n : ℕ) : E n ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hB' n)), ⟨n, rfl⟩⟩
  have hS : S.Nonempty := ⟨E 0, hmem 0⟩
  obtain ⟨M, hM⟩ := (Finset.mem_filter.mp (Finset.max'_mem S hS)).2
  have hmax (n : ℕ) : E n ≤ E M := by
    rw [hM]
    exact Finset.le_max' S (E n) (hmem n)
  have htop : cutPiece surface a h M M = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨n, hx⟩ := exists_mem_quotientDegreeLE (cutIdeal surface a h) x
    let m := max n M
    have hm : cutPiece surface a h M M = cutPiece surface a h m m :=
      Submodule.eq_of_le_of_finrank_le
        (cutPiece_mono surface a h (le_max_right _ _) (le_max_right _ _)) (hmax m)
    rw [hm]
    exact quotientDegreeLE_le_cutPiece surface a h ha (le_max_left _ M) hx
  exact ⟨M, fun i j hi hj => top_unique (htop ▸ cutPiece_mono surface a h hi hj)⟩
end
end K1_13_6_1_4_2_1
end
section
namespace K1_13_6_1_4_2_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_1_4 K1_13_6_1_4_2
def c1 : Prop :=
  ∀ (surface : Ideal GeoJets) (a h : Shape),
    surface.IsPrime → ringKrullDim (GeoJets ⧸ surface) = 2 →
    FullChamber a → FullChamber h →
    Function.Injective (leftMul surface a h) ∧ Function.Injective (rightMul surface a h) ∧
    ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j →
      (biPiece surface a h i (j + 1)).map (leftMul surface a h) ⊓
        (biPiece surface a h (i + 1) j).map (rightMul surface a h) =
      (biPiece surface a h i j).map ((leftMul surface a h).comp (rightMul surface a h))
def c2 : Prop :=
  ∀ (surface : Ideal GeoJets) (a h : Shape),
    surface.IsPrime → ringKrullDim (GeoJets ⧸ surface) = 2 →
    FullChamber a → FullChamber h →
    ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j →
      biPiece surface a h (i + 1) (j + 1) ⊓ LinearMap.ker (cutMap surface a h).toLinearMap =
      (biPiece surface a h i (j + 1)).map (leftMul surface a h) ⊔
        (biPiece surface a h (i + 1) j).map (rightMul surface a h)
theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_1_4_2.c1 := by
  intro surface a h hprime hdim ha hh
  obtain ⟨hl, hr, N₁, hN₁⟩ := h1 surface a h hprime hdim ha hh
  obtain ⟨N₂, hN₂⟩ := h2 surface a h hprime hdim ha hh
  let N := max N₁ N₂
  have difference (i j : ℕ) (hi : N ≤ i) (hj : N ≤ j) :=
    mixed_difference surface a h i j hl hr
      (hN₁ i j ((le_max_left _ _).trans hi) ((le_max_left _ _).trans hj))
      (hN₂ i j ((le_max_right _ _).trans hi) ((le_max_right _ _).trans hj))
  obtain ⟨M, hM⟩ := exists_stable_cutPiece surface a h hprime hdim ha hh N difference
  apply polarize surface a h hprime hdim ha hh
  refine ⟨max N M, fun i j hi hj => ?_⟩
  have hcut := difference i j ((le_max_left _ _).trans hi) ((le_max_left _ _).trans hj)
  rw [hM (i + 1) (j + 1) ((le_max_right _ _).trans (hi.trans (Nat.le_succ _)))
    ((le_max_right _ _).trans (hj.trans (Nat.le_succ _))), finrank_top] at hcut
  exact hcut
end
end K1_13_6_1_4_2_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace K1_13_6_1_4_2_1_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_1 K1_13_7_1 K1_13_6_1_4
  K1_13_6_1_4_2 K1_13_6_1_4_2_1 MvPolynomial
open scoped Pointwise
variable {k : Type*} [Field k]
abbrev Affine (I : Ideal (MvPolynomial (Fin 4) k)) :=
  MvPolynomial (Fin 4) k ⧸ I
abbrev box (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape) (d : ℕ × ℕ) :=
  piece I ((a.scale d.1).plus (h.scale d.2))
theorem monomial_mem_box {I : Ideal (MvPolynomial (Fin 4) k)} {a h : Shape}
    {d : ℕ × ℕ} {e : Fin 4 →₀ ℕ} (he : e ∈ latticeIndices ((a.scale d.1).plus (h.scale d.2)))
    (c : k) : Ideal.Quotient.mk I (monomial e c) ∈ box I a h d :=
  ⟨_, (monomial_mem_restrictSupport k).mpr (Or.inl he), rfl⟩
theorem scalar_mem_box (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape)
    (d : ℕ × ℕ) (c : k) : algebraMap k (Affine I) c ∈ box I a h d := by
  change Ideal.Quotient.mk I (MvPolynomial.C c) ∈ box I a h d
  simpa only [monomial_zero'] using
    (monomial_mem_box (I := I) (d := d) (latticeIndices_zero ((a.scale d.1).plus (h.scale d.2))) c)
theorem one_mem_box (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape)
    (d : ℕ × ℕ) : (1 : Affine I) ∈ box I a h d := by
  simpa only [map_one] using scalar_mem_box I a h d 1
theorem box_mul {I : Ideal (MvPolynomial (Fin 4) k)} {a h : Shape}
    {d e : ℕ × ℕ} {x y : Affine I} (hx : x ∈ box I a h d) (hy : y ∈ box I a h e) :
    x * y ∈ box I a h (d + e) := by
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hy
  refine ⟨p * q, ?_, map_mul (Ideal.Quotient.mk I) _ _⟩
  have hm := Submodule.mul_mem_mul hp hq
  rw [← restrictSupport_add k] at hm
  refine restrictSupport_mono k ?_ hm
  rintro _ ⟨u, hu, v, hv, rfl⟩
  obtain ⟨hub, huj, hut⟩ := hu
  obtain ⟨hvb, hvj, hvt⟩ := hv
  simp only [latticeIndices, Set.mem_ofPred_eq, exponents, Finsupp.add_apply,
    Shape.scale, Shape.plus, Prod.fst_add, Prod.snd_add, Nat.add_mul, Nat.mul_add] at *
  exact ⟨by omega, by omega, by omega⟩
def rees (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape) :
    Subalgebra k (AddMonoidAlgebra (Affine I) (ℕ × ℕ)) where
  carrier := {p | ∀ d, p.coeff d ∈ box I a h d}
  zero_mem' d := (box I a h d).zero_mem
  add_mem' hx hy d := (box I a h d).add_mem (hx d) (hy d)
  one_mem' := by
    classical
    intro d
    change (AddMonoidAlgebra.single 0 1 : AddMonoidAlgebra (Affine I) (ℕ × ℕ)).coeff d ∈ _
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split
    · exact one_mem_box I a h d
    · exact (box I a h d).zero_mem
  mul_mem' {p q} hp hq := by
    classical
    intro d
    change (p * q).coeff d ∈ box I a h d
    simp only [AddMonoidAlgebra.coeff_mul, Finsupp.sum]
    refine (box I a h d).sum_mem fun i _ => (box I a h d).sum_mem fun j _ => ?_
    split
    · rename_i he
      rw [← he]
      exact box_mul (hp i) (hq j)
    · exact (box I a h d).zero_mem
  algebraMap_mem' c := by
    classical
    intro d
    change (AddMonoidAlgebra.single 0 (algebraMap k (Affine I) c)).coeff d ∈ _
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split
    · exact scalar_mem_box I a h d c
    · exact (box I a h d).zero_mem
def homogeneous {I : Ideal (MvPolynomial (Fin 4) k)} {a h : Shape} (d : ℕ × ℕ)
    (x : Affine I) (hx : x ∈ box I a h d) : rees I a h :=
  ⟨AddMonoidAlgebra.single d x, by
    classical
    intro e
    change (AddMonoidAlgebra.single d x).coeff e ∈ box I a h e
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split
    · rename_i he
      subst e
      exact hx
    · exact (box I a h e).zero_mem⟩
@[simp] theorem val_homogeneous {I : Ideal (MvPolynomial (Fin 4) k)} {a h : Shape}
    {d : ℕ × ℕ} {x : Affine I} (hx : x ∈ box I a h d) :
    (rees I a h).val (homogeneous d x hx) = AddMonoidAlgebra.single d x := rfl
theorem left_axis (a h : Shape) : (a.scale 1).plus (h.scale 0) = a := by
  cases a
  cases h
  simp [Shape.scale, Shape.plus]
theorem right_axis (a h : Shape) : (a.scale 0).plus (h.scale 1) = h := by
  cases a
  cases h
  simp [Shape.scale, Shape.plus]
def leftGen (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape) (e : latticeIndices a) :
    rees I a h :=
  homogeneous (1, 0) (Ideal.Quotient.mk I (monomial e.val 1))
    (monomial_mem_box (by simpa only [left_axis] using e.property) 1)
def rightGen (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape) (e : latticeIndices h) :
    rees I a h :=
  homogeneous (0, 1) (Ideal.Quotient.mk I (monomial e.val 1))
    (monomial_mem_box (by simpa only [right_axis] using e.property) 1)
def pairGen (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape)
    (e : latticeIndices a × latticeIndices h) : rees I a h :=
  leftGen I a h e.1 * rightGen I a h e.2
def irrelevant (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape) : Ideal (rees I a h) :=
  Ideal.span (Set.range (pairGen I a h))
def shift (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape) : rees I a h :=
  homogeneous (1, 1) 1 (one_mem_box I a h _)
theorem section_mem_support {σ : Type*} (p : Shape) (f : SectionIndex (p.scale 6) → σ) :
    sectionWith (p.scale 6) f ∈ restrictSupport _ (latticeIndices p) := by
  classical
  unfold sectionWith
  apply Submodule.sum_mem
  intro m hm
  let e : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => (m i).val
  have he : e ∈ latticeIndices p := (mem_exponents_iff (p.scale 6) m).mpr hm
  have hprod : (∏ i : Fin 4, MvPolynomial.X i ^ (m i).val : MvPolynomial (Fin 4)
      (FractionRing (MvPolynomial σ GeoField))) = monomial e 1 := by
    rw [monic_monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
    rfl
  rw [hprod, C_mul_monomial]
  exact (monomial_mem_restrictSupport _).mpr (Or.inl he)
abbrev baseIdeal (surface : Ideal GeoJets) (a h : Shape) := extendIdeal surface a h
abbrev Rees (surface : Ideal GeoJets) (a h : Shape) := rees (baseIdeal surface a h) a h
abbrev leftClass (surface : Ideal GeoJets) (a h : Shape) :=
  Ideal.Quotient.mk (baseIdeal surface a h) (leftSection a h)
abbrev rightClass (surface : Ideal GeoJets) (a h : Shape) :=
  Ideal.Quotient.mk (baseIdeal surface a h) (rightSection a h)
theorem leftClass_mem (surface : Ideal GeoJets) (a h : Shape) :
    leftClass surface a h ∈ box (baseIdeal surface a h) a h (1, 0) := by
  rw [show box (baseIdeal surface a h) a h (1, 0) = piece (baseIdeal surface a h) a
    from congrArg (piece (baseIdeal surface a h)) (left_axis a h)]
  exact ⟨_, section_mem_support a Sum.inl, rfl⟩
theorem rightClass_mem (surface : Ideal GeoJets) (a h : Shape) :
    rightClass surface a h ∈ box (baseIdeal surface a h) a h (0, 1) := by
  rw [show box (baseIdeal surface a h) a h (0, 1) = piece (baseIdeal surface a h) h
    from congrArg (piece (baseIdeal surface a h)) (right_axis a h)]
  exact ⟨_, section_mem_support h Sum.inr, rfl⟩
def leftHom (surface : Ideal GeoJets) (a h : Shape) : Rees surface a h :=
  homogeneous (1, 0) (leftClass surface a h) (leftClass_mem surface a h)
def rightHom (surface : Ideal GeoJets) (a h : Shape) : Rees surface a h :=
  homogeneous (0, 1) (rightClass surface a h) (rightClass_mem surface a h)
def homCutIdeal (surface : Ideal GeoJets) (a h : Shape) : Ideal (Rees surface a h) :=
  Ideal.span {leftHom surface a h, rightHom surface a h}
def homBoundaryIdeal (surface : Ideal GeoJets) (a h : Shape) : Ideal (Rees surface a h) :=
  homCutIdeal surface a h ⊔ Ideal.span ({shift (baseIdeal surface a h) a h} : Set (Rees surface a h))
end
end K1_13_6_1_4_2_1_2
end
section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace K1_13_6_1_4_2_1_2
noncomputable section
open K1_13 K1_13_6 K1_13_7_1 K1_13_6_1_4
  K1_13_6_1_4_2 K1_13_6_1_4_2_1 MvPolynomial
theorem sup_pow_le {R : Type*} [CommRing R] (J P : Ideal R) (m : ℕ) :
    (J ⊔ P) ^ m ≤ J ⊔ P ^ m := by
  induction m with
  | zero => exact le_sup_right
  | succ m ih =>
    rw [pow_succ, pow_succ P]
    refine (Ideal.mul_mono_left ih).trans ?_
    rw [Ideal.mul_sup, Ideal.sup_mul, Ideal.sup_mul]
    exact sup_le (sup_le (Ideal.mul_le_left.trans le_sup_left)
      (Ideal.mul_le_right.trans le_sup_left))
      (sup_le (Ideal.mul_le_left.trans le_sup_left) le_sup_right)
theorem exists_pow_saturation_le {R T : Type*} [CommRing R] [IsNoetherianRing R]
    (g : T → R) (J : Ideal R) (s : R)
    (hg : ∀ t, ∃ m : ℕ, g t ^ m ∈ J ⊔ Ideal.span {s}) :
    ∃ N : ℕ, ∀ x ∈ Ideal.span (Set.range g) ^ N, (∃ m : ℕ, s ^ m * x ∈ J) → x ∈ J := by
  let B := Ideal.span (Set.range g)
  have hb : B ≤ (J ⊔ Ideal.span {s}).radical := by
    apply Ideal.span_le.mpr
    rintro _ ⟨t, rfl⟩
    exact hg t
  let C : ℕ →o Submodule R R :=
    ⟨fun m => J.colon {s ^ m}, by
      intro i j hij x hx
      simp only [Submodule.mem_colon_singleton, smul_eq_mul] at hx ⊢
      rw [show j = j - i + i by omega, pow_add]
      simpa only [mul_comm x, mul_assoc] using J.mul_mem_left (s ^ (j - i)) (by
        simpa only [mul_comm x] using hx)⟩
  obtain ⟨m, hm⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance C
  have hC (i : ℕ) : C i ≤ C m := by
    rcases le_total i m with h | h
    · exact C.monotone h
    · exact (hm i h).ge
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hb B.fg_of_isNoetherianRing
  have hpow : B ^ (n * m) ≤ J ⊔ Ideal.span {s ^ m} := by
    rw [pow_mul, ← Ideal.span_singleton_pow]
    exact (Ideal.pow_right_mono hn m).trans (sup_pow_le J _ m)
  have hmul : B ^ (n * m) * (C m : Ideal R) ≤ J := by
    refine (Ideal.mul_mono_left hpow).trans ?_
    rw [Ideal.sup_mul]
    refine sup_le Ideal.mul_le_left (Ideal.mul_le.mpr ?_)
    intro p hp x hx
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    have hx' : x * s ^ m ∈ J := Submodule.mem_colon_singleton.mp hx
    simpa only [mul_assoc, mul_comm (s ^ m) x] using J.mul_mem_left t hx'
  obtain ⟨k, hk⟩ := B.exists_pow_inf_eq_pow_smul (C m)
  refine ⟨k + n * m, fun x hx ⟨i, hi⟩ => ?_⟩
  have hxi : x ∈ C i := by
    apply Submodule.mem_colon_singleton.mpr
    change x * s ^ i ∈ J
    rwa [mul_comm]
  have h := hk (k + n * m) (Nat.le_add_right _ _)
  simp only [Ideal.smul_eq_mul, Ideal.mul_top, Nat.add_sub_cancel_left] at h
  have hx' : x ∈ B ^ (k + n * m) ⊓ C m := ⟨hx, hC i hxi⟩
  rw [h] at hx'
  exact hmul (Ideal.mul_mono_right inf_le_right hx')
variable {surface : Ideal GeoJets} {a h : Shape}
theorem cut_eq_zero_iff (x : SurfaceRing surface a h) :
    cutMap surface a h x = 0 ↔ x ∈ Ideal.span {leftClass surface a h, rightClass surface a h} := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk (cutIdeal surface a h) p = 0 ↔ _
  have hspan : (Ideal.span {leftSection a h, rightSection a h}).map
      (Ideal.Quotient.mk (baseIdeal surface a h)) =
      Ideal.span {leftClass surface a h, rightClass surface a h} := by
    rw [Ideal.map_span]
    simp
  rw [← hspan, Ideal.mem_quotient_iff_mem_sup, Ideal.Quotient.eq_zero_iff_mem, cutIdeal, sup_comm]
theorem left_coeff (r : Rees surface a h) (i j : ℕ) :
    ((rees (baseIdeal surface a h) a h).val (r * leftHom surface a h)).coeff (i + 1, j + 1) =
      leftMul surface a h (r.val.coeff (i, j + 1)) := by
  simp only [map_mul, leftHom, val_homogeneous]
  rw [show (i + 1, j + 1) = (i, j + 1) + (1, 0) by rfl,
    AddMonoidAlgebra.coeff_mul_single_add]
  exact mul_comm _ _
theorem right_coeff (r : Rees surface a h) (i j : ℕ) :
    ((rees (baseIdeal surface a h) a h).val (r * rightHom surface a h)).coeff (i + 1, j + 1) =
      rightMul surface a h (r.val.coeff (i + 1, j)) := by
  simp only [map_mul, rightHom, val_homogeneous]
  rw [show (i + 1, j + 1) = (i + 1, j) + (0, 1) by rfl,
    AddMonoidAlgebra.coeff_mul_single_add]
  exact mul_comm _ _
theorem hom_mem_cut_iff (i j : ℕ) (x : SurfaceRing surface a h)
    (hx : x ∈ box (baseIdeal surface a h) a h (i + 1, j + 1)) :
    homogeneous (I := baseIdeal surface a h) (a := a) (h := h) (i + 1, j + 1) x hx ∈
        homCutIdeal surface a h ↔
      x ∈ (biPiece surface a h i (j + 1)).map (leftMul surface a h) ⊔
        (biPiece surface a h (i + 1) j).map (rightMul surface a h) := by
  constructor
  · intro hxJ
    obtain ⟨r, t, he⟩ := Ideal.mem_span_pair.mp hxJ
    have hc := congrArg (fun z : Rees surface a h =>
      ((rees (baseIdeal surface a h) a h).val z).coeff (i + 1, j + 1)) he
    change ((rees (baseIdeal surface a h) a h).val
      (r * leftHom surface a h + t * rightHom surface a h)).coeff (i + 1, j + 1) =
      ((rees (baseIdeal surface a h) a h).val
        (homogeneous (i + 1, j + 1) x hx)).coeff (i + 1, j + 1) at hc
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, left_coeff, right_coeff,
      val_homogeneous, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at hc
    have hr : r.val.coeff (i, j + 1) ∈ biPiece surface a h i (j + 1) :=
      r.property (i, j + 1)
    have ht : t.val.coeff (i + 1, j) ∈ biPiece surface a h (i + 1) j :=
      t.property (i + 1, j)
    exact Submodule.mem_sup.mpr ⟨_, Submodule.mem_map_of_mem (f := leftMul surface a h) hr,
      _, Submodule.mem_map_of_mem (f := rightMul surface a h) ht, hc⟩
  · intro hm
    obtain ⟨_, ⟨y, hy, rfl⟩, _, ⟨z, hz, rfl⟩, he⟩ := Submodule.mem_sup.mp hm
    change y ∈ box (baseIdeal surface a h) a h (i, j + 1) at hy
    change z ∈ box (baseIdeal surface a h) a h (i + 1, j) at hz
    refine Ideal.mem_span_pair.mpr
      ⟨homogeneous (i, j + 1) y hy, homogeneous (i + 1, j) z hz, Subtype.ext ?_⟩
    change (rees (baseIdeal surface a h) a h).val
      (homogeneous (i, j + 1) y hy * leftHom surface a h +
        homogeneous (i + 1, j) z hz * rightHom surface a h) =
      (rees (baseIdeal surface a h) a h).val (homogeneous (i + 1, j + 1) x hx)
    simp only [map_add, map_mul, leftHom, rightHom, val_homogeneous,
      AddMonoidAlgebra.single_mul_single]
    change AddMonoidAlgebra.single (i + 1, j + 1) (y * leftClass surface a h) +
      AddMonoidAlgebra.single (i + 1, j + 1) (z * rightClass surface a h) =
      AddMonoidAlgebra.single (i + 1, j + 1) x
    rw [← AddMonoidAlgebra.singleAddHom_apply, ← AddMonoidAlgebra.singleAddHom_apply,
      ← map_add, AddMonoidAlgebra.singleAddHom_apply]
    rw [mul_comm y, mul_comm z]
    exact congrArg (AddMonoidAlgebra.single (i + 1, j + 1)) he
theorem degreeLE_le_box (ha : FullChamber a) {N i j : ℕ} (hi : N ≤ i) :
    quotientDegreeLE (baseIdeal surface a h) N ≤ biPiece surface a h i j := by
  intro x hx
  obtain ⟨P, hP, rfl⟩ := mem_quotientDegreeLE.mp hx
  have haT : i ≤ i * a.t := Nat.le_mul_of_pos_right i ha.2
  have haJ : 3 * i ≤ i * a.j := by
    rw [Nat.mul_comm 3 i]
    exact Nat.mul_le_mul_left _ (by have := ha.1.2; have := ha.2; omega)
  have haB : i ≤ i * a.b := by
    exact Nat.le_mul_of_pos_right _ (by have := ha.1.1; have := ha.1.2; have := ha.2; omega)
  refine ⟨P, ?_, rfl⟩
  intro e he
  have hd := (le_totalDegree he).trans hP
  change e.degree ≤ N at hd
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_four] at hd
  change e 0 + e 1 + e 2 + e 3 ≤ 6 * (i * a.b + j * h.b) ∧
    e 1 + 2 * e 2 + 3 * e 3 ≤ 6 * (i * a.j + j * h.j) ∧
    e 3 ≤ 6 * (i * a.t + j * h.t)
  exact ⟨by omega, by omega, by omega⟩
theorem val_shift_pow (n : ℕ) :
    (rees (baseIdeal surface a h) a h).val (shift (baseIdeal surface a h) a h ^ n) =
      AddMonoidAlgebra.single (n, n) 1 := by
  induction n with
  | zero => simp only [pow_zero, map_one, AddMonoidAlgebra.one_def]; rfl
  | succ n ih =>
    rw [pow_succ, map_mul, ih]
    change (AddMonoidAlgebra.single (n, n) 1 : AddMonoidAlgebra
      (SurfaceRing surface a h) (ℕ × ℕ)) * AddMonoidAlgebra.single (1, 1) 1 = _
    rw [AddMonoidAlgebra.single_mul_single, mul_one, Prod.mk_add_mk]
theorem exists_shift_pow_mem_cut (ha : FullChamber a) (i j : ℕ)
    (x : SurfaceRing surface a h) (hx : x ∈ box (baseIdeal surface a h) a h (i + 1, j + 1))
    (hzero : cutMap surface a h x = 0) :
    ∃ n : ℕ, shift (baseIdeal surface a h) a h ^ n *
      homogeneous (i + 1, j + 1) x hx ∈ homCutIdeal surface a h := by
  obtain ⟨u, v, he⟩ := Ideal.mem_span_pair.mp ((cut_eq_zero_iff x).mp hzero)
  obtain ⟨nu, hu⟩ := exists_mem_quotientDegreeLE (baseIdeal surface a h) u
  obtain ⟨nv, hv⟩ := exists_mem_quotientDegreeLE (baseIdeal surface a h) v
  let n := max nu nv
  let f : Rees surface a h :=
    shift (baseIdeal surface a h) a h ^ n * homogeneous (i + 1, j + 1) x hx
  have hf : (rees (baseIdeal surface a h) a h).val f =
      AddMonoidAlgebra.single (n + i + 1, n + j + 1) x := by
    dsimp only [f]
    rw [map_mul, val_shift_pow, val_homogeneous, AddMonoidAlgebra.single_mul_single,
      one_mul, Prod.mk_add_mk, Nat.add_assoc, Nat.add_assoc]
  have hfx : x ∈ box (baseIdeal surface a h) a h (n + i + 1, n + j + 1) := by
    have hc := f.property (n + i + 1, n + j + 1)
    change ((rees (baseIdeal surface a h) a h).val f).coeff (n + i + 1, n + j + 1) ∈
      box (baseIdeal surface a h) a h (n + i + 1, n + j + 1) at hc
    simpa only [hf, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] using hc
  have hf' : f = homogeneous (n + i + 1, n + j + 1) x hfx := Subtype.ext hf
  refine ⟨n, ?_⟩
  change f ∈ _
  rw [hf', hom_mem_cut_iff]
  have hui : nu ≤ n + i := (le_max_left _ _).trans (Nat.le_add_right _ _)
  have hvi : nv ≤ n + i + 1 :=
    (le_max_right nu nv).trans ((Nat.le_add_right n i).trans (Nat.le_succ _))
  exact Submodule.mem_sup.mpr ⟨_, ⟨u, degreeLE_le_box ha hui hu, rfl⟩,
    _, ⟨v, degreeLE_le_box ha hvi hv, rfl⟩, by
      change leftClass surface a h * u + rightClass surface a h * v = x
      rwa [mul_comm (leftClass surface a h) u, mul_comm (rightClass surface a h) v]⟩
end
end K1_13_6_1_4_2_1_2
end
section
namespace K1_13_6_1_4_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_1
open MvPolynomial
def sliceMap (h : Shape) : GeoJets →+* SectionJets h :=
  MvPolynomial.map (algebraMap GeoField (SectionField h))
def sliceIdeal (J : Ideal GeoJets) (h : Shape) : Ideal (SectionJets h) :=
  J.map (sliceMap h) ⊔ Ideal.span {genericSection h}
def FitsBox {k : Type} [Field k] (Q : MvPolynomial (Fin 4) k) (a : Shape) : Prop :=
  Q.totalDegree ≤ a.b ∧ Q.weightedTotalDegree Fin.val ≤ a.j ∧ Q.degreeOf 3 ≤ a.t
abbrev CutField (k : Type) [Field k] (a : Shape) :=
  FractionRing (MvPolynomial (SectionIndex a) k)
def cutPolynomial (k : Type) [Field k] (a : Shape) :
    MvPolynomial (Fin 4) (CutField k a) :=
  ∑ m ∈ boxMonomials a,
    MvPolynomial.C (algebraMap (MvPolynomial (SectionIndex a) k) (CutField k a) (MvPolynomial.X m)) *
      ∏ i : Fin 4, MvPolynomial.X i ^ (m i).val
def genericCutLength {k : Type} [Field k] (I : Ideal (MvPolynomial (Fin 4) k))
    (a : Shape) : ℕ :=
  Module.finrank (CutField k a) (MvPolynomial (Fin 4) (CutField k a) ⧸
    (I.map (MvPolynomial.map (algebraMap k (CutField k a))) ⊔
      Ideal.span {cutPolynomial k a}))
end
end K1_13_6_1_4_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_13_6_1_4_2_1_2
noncomputable section
open K1_13 K1_13_6 K1_13_7_1 K1_13_6_1_4
  K1_13_6_1_4_2 K1_13_6_1_4_2_1 MvPolynomial
def c1 : Prop :=
  ∀ {k : Type} [Field k] (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape),
    Chamber a → Chamber h →
    IsNoetherianRing (rees I a h) ∧
    ∀ (i j : ℕ) (x : Affine I) (hx : x ∈ box I a h (i, j)) (n : ℕ),
      n ≤ i → n ≤ j → homogeneous (i, j) x hx ∈ irrelevant I a h ^ n
def c2 : Prop :=
  ∀ (surface : Ideal GeoJets) (a h : Shape),
    surface.IsPrime → ringKrullDim (GeoJets ⧸ surface) = 2 →
    FullChamber a → FullChamber h →
    ∀ e : latticeIndices a × latticeIndices h,
      ∃ m : ℕ, pairGen (baseIdeal surface a h) a h e ^ m ∈ homBoundaryIdeal surface a h
theorem image_sum_le (surface : Ideal GeoJets) (a h : Shape) (i j : ℕ) :
    (biPiece surface a h i (j + 1)).map (leftMul surface a h) ⊔
      (biPiece surface a h (i + 1) j).map (rightMul surface a h) ≤
    biPiece surface a h (i + 1) (j + 1) ⊓ LinearMap.ker (cutMap surface a h).toLinearMap := by
  intro x hx
  obtain ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hx
  change u ∈ box (baseIdeal surface a h) a h (i, j + 1) at hu
  change v ∈ box (baseIdeal surface a h) a h (i + 1, j) at hv
  have hu' := box_mul hu (leftClass_mem surface a h)
  have hv' := box_mul hv (rightClass_mem surface a h)
  have hsum : leftClass surface a h * u + rightClass surface a h * v ∈
      biPiece surface a h (i + 1) (j + 1) := by
    rw [mul_comm (leftClass surface a h) u, mul_comm (rightClass surface a h) v]
    exact (biPiece surface a h (i + 1) (j + 1)).add_mem hu' hv'
  refine ⟨hsum, (cut_eq_zero_iff _).mpr ?_⟩
  apply Ideal.mem_span_pair.mpr
  refine ⟨u, v, ?_⟩
  change u * leftClass surface a h + v * rightClass surface a h =
    leftClass surface a h * u + rightClass surface a h * v
  rw [mul_comm u, mul_comm v]
theorem boundary_bound (surface : Ideal GeoJets) (a h : Shape)
    (hNoeth : IsNoetherianRing (Rees surface a h))
    (hchart : ∀ e : latticeIndices a × latticeIndices h,
      ∃ m : ℕ, pairGen (baseIdeal surface a h) a h e ^ m ∈ homBoundaryIdeal surface a h) :
    ∃ N : ℕ, ∀ f ∈ irrelevant (baseIdeal surface a h) a h ^ N,
      (∃ m : ℕ, shift (baseIdeal surface a h) a h ^ m * f ∈ homCutIdeal surface a h) →
      f ∈ homCutIdeal surface a h :=
  @exists_pow_saturation_le (Rees surface a h) (latticeIndices a × latticeIndices h)
    inferInstance hNoeth (pairGen (baseIdeal surface a h) a h)
    (homCutIdeal surface a h) (shift (baseIdeal surface a h) a h) hchart
theorem ker_le_image_sum (surface : Ideal GeoJets) (a h : Shape) (ha : FullChamber a)
    (i j N : ℕ)
    (hpower : ∀ (x : SurfaceRing surface a h) (hx : x ∈ box (baseIdeal surface a h) a h (i + 1, j + 1)),
      homogeneous (i + 1, j + 1) x hx ∈ irrelevant (baseIdeal surface a h) a h ^ N)
    (hbound : ∀ f ∈ irrelevant (baseIdeal surface a h) a h ^ N,
      (∃ m : ℕ, shift (baseIdeal surface a h) a h ^ m * f ∈ homCutIdeal surface a h) →
      f ∈ homCutIdeal surface a h) :
    biPiece surface a h (i + 1) (j + 1) ⊓ LinearMap.ker (cutMap surface a h).toLinearMap ≤
      (biPiece surface a h i (j + 1)).map (leftMul surface a h) ⊔
        (biPiece surface a h (i + 1) j).map (rightMul surface a h) := by
  rintro x ⟨hx, hxzero⟩
  change x ∈ box (baseIdeal surface a h) a h (i + 1, j + 1) at hx
  apply (hom_mem_cut_iff i j x hx).mp
  exact hbound _ (hpower x hx) (exists_shift_pow_mem_cut ha i j x hx hxzero)
theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_1_4_2_1.c2 := by
  intro surface a h hs hdim ha hh
  obtain ⟨hNoeth, hpower⟩ := h1 (baseIdeal surface a h) a h ha.1 hh.1
  obtain ⟨N, hbound⟩ := boundary_bound surface a h hNoeth (h2 surface a h hs hdim ha hh)
  refine ⟨N, fun i j hi hj => le_antisymm ?_ (image_sum_le surface a h i j)⟩
  exact ker_le_image_sum surface a h ha i j N
    (fun x hx => hpower (i + 1) (j + 1) x hx N
      (hi.trans (Nat.le_succ i)) (hj.trans (Nat.le_succ j))) hbound
end
end K1_13_6_1_4_2_1_2
end
section
namespace K1_13_7_2_3
open K1_13_6
structure ProperComponent (surface : Ideal GeoJets) (P : GeoJets) (C : Ideal GeoJets) : Prop where
  prime : surface.IsPrime
  height : surface.height = 2
  proper : P ∉ surface
  component : (surface ⊔ Ideal.span {P}).IsMinimalPrime C
end K1_13_7_2_3
end
