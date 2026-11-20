import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
import ProximityPrize.SubmissionLower.Fast005
import ProximityPrize.SubmissionLower.Fast006
import ProximityPrize.SubmissionLower.Fast014
import ProximityPrize.SubmissionLower.Pack_K1Defs
import ProximityPrize.SubmissionLower.Fast017
import ProximityPrize.SubmissionLower.Fast018
import ProximityPrize.SubmissionLower.Fast019
import ProximityPrize.SubmissionLower.Fast020
import ProximityPrize.SubmissionLower.Pack_K1_13_6_1_4Geometry
import ProximityPrize.SubmissionLower.Fast023
import ProximityPrize.SubmissionLower.Fast029
import ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic
import ProximityPrize.SubmissionLower.Pack_K1_14_2_1Split
import ProximityPrize.SubmissionLower.Pack_K1_14_2_2Split
import ProximityPrize.SubmissionLower.Pack_K1_14_3Split
import ProximityPrize.SubmissionLower.Fast040
import ProximityPrize.SubmissionLower.Pack_K1_14_3_2_3Split
set_option Elab.async false

section PackSource_K1_13_8Defs
set_option autoImplicit true
namespace K1_13_8

open K1_13
open scoped BigOperators

def zeroShape : Shape := ⟨0, 0, 0⟩
def fullCap : Shape := ⟨120, 48, 10⟩
def need : ℕ := 26124168665121
def layerCount : ℕ := 1 + (3000 * 180265 - 1) / 46597

/-- The additive inequalities on a nonempty product. -/
def Valid (a : Shape) : Prop := 1 ≤ a.t ∧ 3 * a.t ≤ a.j ∧ a.j ≤ 3 * a.b

/-- The finite region for a nonempty retained product. -/
def RetainedBox (a : Shape) : Prop :=
  a.b ≤ 19 ∧ a.j ≤ 6 ∧
  (4 ≤ a.j → a.b ≤ 17) ∧ (5 ≤ a.j → a.b ≤ 13) ∧ (6 ≤ a.j → a.b ≤ 6)

instance (a : Shape) : Decidable (Valid a) := by unfold Valid; infer_instance
instance (a : Shape) : Decidable (RetainedBox a) := by unfold RetainedBox; infer_instance
instance (a : Shape) : Decidable (FatEligible a) := by unfold FatEligible; infer_instance

/-- Newton coefficients of the period-six subsequences. Row zero is
the coefficient series of 1/((1-X)^2(1-X^2)(1-X^3)); the other rows
include the extra denominator (1-X^r). -/
def coefficients (r s : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  match r, s with
  | 0, 0 => (1, 22, 57, 36, 0)
  | 0, 1 => (2, 29, 63, 36, 0)
  | 0, 2 => (4, 37, 69, 36, 0)
  | 0, 3 => (7, 46, 75, 36, 0)
  | 0, 4 => (11, 56, 81, 36, 0)
  | 0, _ => (16, 67, 87, 36, 0)
  | 1, 0 => (1, 63, 314, 468, 216)
  | 1, 1 => (3, 92, 377, 504, 216)
  | 1, 2 => (7, 129, 446, 540, 216)
  | 1, 3 => (14, 175, 521, 576, 216)
  | 1, 4 => (25, 231, 602, 612, 216)
  | 1, _ => (41, 298, 689, 648, 216)
  | 2, 0 => (1, 38, 172, 243, 108)
  | 2, 1 => (2, 54, 205, 261, 108)
  | 2, 2 => (5, 75, 241, 279, 108)
  | 2, 3 => (9, 100, 280, 297, 108)
  | 2, 4 => (16, 131, 322, 315, 108)
  | 2, _ => (25, 167, 367, 333, 108)
  | _, 0 => (1, 30, 125, 168, 72)
  | _, 1 => (2, 42, 148, 180, 72)
  | _, 2 => (4, 57, 173, 192, 72)
  | _, 3 => (8, 76, 200, 204, 72)
  | _, 4 => (13, 98, 229, 216, 72)
  | _, _ => (20, 124, 260, 228, 72)

def coefficient (r j : ℕ) : ℕ :=
  let q := j / 6
  let (a, b, c, d, e) := coefficients r (j % 6)
  let p₂ := q * (q - 1)
  let p₃ := p₂ * (q - 2)
  a + b * q + c * (p₂ / 2) + d * (p₃ / 6) + e * (p₃ * (q - 3) / 24)

/-- A shift by more than the requested index yields the zero coefficient. -/
def shifted (r j v : ℕ) : ℕ := if v ≤ j then coefficient r (j - v) else 0

def across (b r j v : ℕ) : ℕ :=
  shifted r j v - shifted r j (v + r * (b + 1))

/-- The cumulative Gaussian-binomial count in the two budgets.
The positive terms are added before the negative terms are subtracted. -/
def fastSymbols (b j : ℕ) : ℕ :=
  (b + 1) * coefficient 0 j + across b 2 j 3 + across b 2 j 4 + across b 2 j 5 -
    (across b 1 j 1 + across b 1 j 2 + across b 1 j 3 + across b 3 j 6)

def fastRemaining (b j : ℕ) : ℕ :=
  if b ≤ 4012 ∧ j ≤ 1650 then fastSymbols (4012 - b) (1650 - j) else 0

def zeroMass (b j : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (1650 / j), fastRemaining ((k + 1) * b) ((k + 1) * j)

/-- The fixed retained resource is r. The new positive prefix has resource y.
For d ≤ L pay d*r; for d = L+i pay L*r+i*(r+y). Terms outside the
index budget vanish. The zero-index start below is the empty retained set. -/
def availableMass (r y : Shape) (L : ℕ) : ℕ :=
  (if r.j = 0 then L * fastRemaining 0 0
    else ∑ k ∈ Finset.range (min L (1650 / r.j)),
      fastRemaining ((k + 1) * r.b) ((k + 1) * r.j)) +
  ∑ k ∈ Finset.range (1650 / (r.j + y.j)),
    fastRemaining (L * r.b + (k + 1) * (r.b + y.b))
      (L * r.j + (k + 1) * (r.j + y.j))

def edgePrice (a : Shape) (L : ℕ) : ℕ :=
  if FatEligible a then min (physicalPrice a L) (fatPrice a) else physicalPrice a L

/-- A reverse Bellman potential, with zero always allowed as a stopping cost.
The state y records only the positive factors chosen so far. Each proposed order
is certified once per endpoint by testing its predecessor, unless it is one. -/
def Bellman (r : Shape) (cap : ℕ) : Prop :=
  ∃ (B order : Shape → ℕ), B zeroShape ≤ cap ∧
    (∀ x, Valid x → InBox (r.plus x) fullCap →
      0 < order x ∧ (order x = 1 ∨ availableMass r x (order x - 1) < need)) ∧
    (∀ (y a : Shape), (y = zeroShape ∨ Valid y) → Valid a →
      InBox (r.plus (y.plus a)) fullCap →
      edgePrice a (order (y.plus a)) + B (y.plus a) ≤ B y)

end K1_13_8
end PackSource_K1_13_8Defs

section PackSource_K1_13_8Aux
set_option autoImplicit true
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

-- Check each boundary point separately so replay can release the preceding sum.
section
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private theorem aux8_exclude_20_3 : zeroMass 20 3 < need := by decide

private theorem aux8_exclude_18_4 : zeroMass 18 4 < need := by decide

private theorem aux8_exclude_14_5 : zeroMass 14 5 < need := by decide

private theorem aux8_exclude_7_6 : zeroMass 7 6 < need := by decide

private theorem aux8_exclude_3_7 : zeroMass 3 7 < need := by decide

end

theorem retained_exclusions :
    zeroMass 20 3 < need ∧ zeroMass 18 4 < need ∧ zeroMass 14 5 < need ∧
    zeroMass 7 6 < need ∧ zeroMass 3 7 < need :=
  ⟨aux8_exclude_20_3, aux8_exclude_18_4, aux8_exclude_14_5,
    aux8_exclude_7_6, aux8_exclude_3_7⟩

theorem corner_order_test :
    availableMass zeroShape fullCap 57 < need ∧
      need ≤ availableMass zeroShape fullCap 58 := by decide

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
private theorem retained_prices_finite :
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

/-- The spending lower bound in a layer, using only the retained factors and
a subset of positive factors whose orders have maximum at most L. -/
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
end PackSource_K1_13_8Aux

section PackSource_K1_13_8Split
set_option autoImplicit true
namespace K1_13_8

open K1_13
open scoped BigOperators

/-- Exact two-budget symbol counts for the clipped primary bank. -/
def c1 : Prop := ∀ b j, remaining b j = fastRemaining b j

/-- The positive phase with an empty retained product. -/
def c2 : Prop := Bellman zeroShape 222142013343379695

/-- The positive phase when the retained product has top degree one. -/
def c3 : Prop := Bellman ⟨1, 3, 1⟩ 185142013343379695

/-- The positive phase when the retained product has top degree two. -/
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

private theorem mass_le {n : ℕ} {a : Fin n → Shape} {l : Fin n → ℕ}
    (hlayers : LayerBudget a l) {z s : Finset (Fin n)} {q : Shape} {L : ℕ}
    (hz : ∀ i ∈ z, l i = 0) (hs : ∀ i ∈ s, l i ≤ L)
    (hdisj : Disjoint z s) (hq : InBox q (shapeSum a z)) :
    need ≤ ∑ k ∈ Finset.range layerCount, layerTerm q (shapeSum a s) L k := by
  refine hlayers.trans (Finset.sum_le_sum fun k _ => remaining_anti ?_ ?_)
  · exact spend_le (fun i => (a i).b) hz hs hdisj hq.1
  · exact spend_le (fun i => (a i).j) hz hs hdisj hq.2.1

private theorem retained_cost {ι : Type*} {a : ι → Shape} {cost : ι → ℕ}
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
end PackSource_K1_13_8Split

section PackSource_K1_13_8_2Defs
set_option autoImplicit true
namespace K1_13_8_2

open K1_13 K1_13_8

def limit : ℕ := 222142013343379695

/-- Lower degree and index thresholds for certifying a positive order. -/
structure Threshold where
  b : ℕ
  j : ℕ
  l : ℕ

def thresholds : List Threshold :=
  [⟨118, 48, 58⟩, ⟨103, 43, 57⟩, ⟨67, 30, 52⟩, ⟨11, 16, 34⟩,
   ⟨4, 11, 17⟩, ⟨48, 4, 15⟩, ⟨5, 9, 7⟩, ⟨27, 6, 3⟩,
   ⟨19, 7, 2⟩, ⟨36, 4, 2⟩, ⟨9, 8, 2⟩, ⟨26, 6, 2⟩]

def orderFor (b j : ℕ) : List Threshold → ℕ
  | [] => 1
  | s :: rest =>
      max (if s.b ≤ b ∧ s.j ≤ j then s.l else 1) (orderFor b j rest)

def orderAt (x : Shape) : ℕ := orderFor x.b x.j thresholds

/-- The cost of spending the remaining index, rounded down once. -/
def potential (x : Shape) : ℕ := limit * (48 - x.j) / 48

def indexBudget (j : ℕ) : ℕ := limit * j / 48

/-- Boolean bounded universal quantification for the finite certificates. -/
def allBelow (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => p n && allBelow p n

theorem allBelow_spec {p : ℕ → Bool} {n : ℕ} (h : allBelow p n = true)
    {k : ℕ} (hk : k < n) : p k = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    have h' := Bool.and_eq_true_iff.mp h
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
    · exact ih h'.2 hlt
    · exact h'.1

end K1_13_8_2
end PackSource_K1_13_8_2Defs

section PackSource_K1_13_8_2Mixed
set_option autoImplicit true
namespace K1_13_8_2

open K1_13

def Chamber (p : Shape) : Prop := p.j ≤ p.b ∧ 3 * p.t ≤ p.j

private def signedMixed (p q r s : Shape) : ℤ :=
  difference (difference (difference (difference volume32 p) q) r) s ⟨0, 0, 0⟩

private theorem signed_add (p a q r s : Shape) :
    signedMixed (p.plus a) q r s = signedMixed p q r s + signedMixed a q r s := by
  simp only [signedMixed, difference, volume32, Shape.plus, Nat.cast_add, Nat.cast_zero]
  ring

private theorem signed_rotate (p q r s : Shape) :
    signedMixed p q r s = signedMixed q r s p := by
  simp only [signedMixed, difference, volume32, Shape.plus, Nat.cast_add, Nat.cast_zero]
  ring

private theorem chamber_coords (p : Shape) (h : Chamber p) :
    (p.b : ℤ) = (↑(p.b - p.j) : ℤ) + ↑(p.j - 3 * p.t) + 3 * p.t ∧
    (p.j : ℤ) = (↑(p.j - 3 * p.t) : ℤ) + 3 * p.t := by
  obtain ⟨hb, hj⟩ := h
  constructor <;> exact_mod_cast (by omega : _)

/-- Polarizing the chamber volume gives nonnegative coefficients when the
first slot has arbitrary nonnegative coordinates and the other slots are in
the chamber.  The first slot can therefore be a coordinate increment. -/
private theorem signed_nonneg (d q r s : Shape) (hq : Chamber q) (hr : Chamber r)
    (hs : Chamber s) : 0 ≤ signedMixed d q r s := by
  obtain ⟨hqb, hqj⟩ := chamber_coords q hq
  obtain ⟨hrb, hrj⟩ := chamber_coords r hr
  obtain ⟨hsb, hsj⟩ := chamber_coords s hs
  simp only [signedMixed, difference, volume32, Shape.plus, Nat.cast_add, Nat.cast_zero]
  rw [hqb, hqj, hrb, hrj, hsb, hsj]
  ring_nf
  positivity

private theorem mixed_mono_first {p p' : Shape} (h : InBox p p') {q r s : Shape}
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

private theorem mixed_rotate (p q r s : Shape) :
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
end PackSource_K1_13_8_2Mixed

section PackSource_K1_13_8_2Tariff
set_option autoImplicit true
namespace K1_13_8_2

open K1_13

private theorem box_refl (x : Shape) : InBox x x := ⟨le_rfl, le_rfl, le_rfl⟩

private theorem normalize_mono {x y : Shape} (h : InBox x y) :
    InBox x.chamber y.chamber := ⟨max_le_max h.1 h.2.1, h.2.1, h.2.2⟩

private theorem normalize_chamber (x : Shape) (h : 3 * x.t ≤ x.j) :
    Chamber x.chamber := ⟨le_max_right _ _, h⟩

private theorem plus_mono {x y u v : Shape} (h : InBox x y) (h' : InBox u v) :
    InBox (x.plus u) (y.plus v) :=
  ⟨Nat.add_le_add h.1 h'.1, Nat.add_le_add h.2.1 h'.2.1, Nat.add_le_add h.2.2 h'.2.2⟩

private theorem plus_chamber {x y : Shape} (hx : Chamber x) (hy : Chamber y) :
    Chamber (x.plus y) := by
  exact ⟨Nat.add_le_add hx.1 hy.1, by simp only [Shape.plus, Nat.mul_add]; exact Nat.add_le_add hx.2 hy.2⟩

private theorem scale_mono {x y : Shape} (h : InBox x y) (k : ℕ) :
    InBox (x.scale k) (y.scale k) :=
  ⟨Nat.mul_le_mul_left k h.1, Nat.mul_le_mul_left k h.2.1, Nat.mul_le_mul_left k h.2.2⟩

private theorem scale_chamber {x : Shape} (hx : Chamber x) (k : ℕ) :
    Chamber (x.scale k) :=
  ⟨Nat.mul_le_mul_left k hx.1, by simpa [Shape.scale, Nat.mul_left_comm 3 k] using Nat.mul_le_mul_left k hx.2⟩

private theorem min_fits_index (a i : ℕ) : 3 * min a (i / 3) ≤ i := by
  have h := min_le_right a (i / 3)
  omega

private theorem chart_chamber (L : ℕ) (x : Shape) : Chamber (chart L x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩

private theorem lifted_chamber (L : ℕ) (x : Shape) : Chamber (liftedChart L x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩

private theorem chart_mono (L : ℕ) {x y : Shape} (h : InBox x y) :
    InBox (chart L x) (chart L y) := by
  obtain ⟨hb, hj, ht⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [chart] <;> gcongr

private theorem lifted_mono (L : ℕ) {x y : Shape} (h : InBox x y) :
    InBox (liftedChart L x) (liftedChart L y) := by
  obtain ⟨hb, hj, ht⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [liftedChart] <;> gcongr

private def graphShape (p : Shape) : Shape :=
  ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩

private theorem graph_chamber (x : Shape) : Chamber (graphShape x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩

private theorem graph_mono {x y : Shape} (h : InBox x y) :
    InBox (graphShape x) (graphShape y) := by
  obtain ⟨hb, hj, ht⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [graphShape] <;> gcongr

private theorem surface_mono {p p' q : Shape} (hp : InBox p p') (hp' : Chamber p') (hq : Chamber q) :
    surfaceNumerator32 p q ≤ surfaceNumerator32 p' q := by
  let L := taylorLength
  have hchart : mixed32 p q (chart (L+1) p) (chart (L+2) p) ≤
      mixed32 p' q (chart (L+1) p') (chart (L+2) p') :=
    mixed_mono hp (box_refl q) (chart_mono _ hp) (chart_mono _ hp) hp' hq
      (chart_chamber _ _) hq (chart_chamber _ _) (chart_chamber _ _)
  have hlift : mixed32 p q (liftedChart (L+1) p) (liftedChart (L+2) p) ≤
      mixed32 p' q (liftedChart (L+1) p') (liftedChart (L+2) p') :=
    mixed_mono hp (box_refl q) (lifted_mono _ hp) (lifted_mono _ hp) hp' hq
      (lifted_chamber _ _) hq (lifted_chamber _ _) (lifted_chamber _ _)
  have hgraph (M : ℕ) :
      mixed32 p q (graphShape p) (liftedChart M p) ≤ mixed32 p' q (graphShape p') (liftedChart M p') :=
    mixed_mono hp (box_refl q) (graph_mono hp) (lifted_mono _ hp) hp' hq
      (graph_chamber _) hq (graph_chamber _) (lifted_chamber _ _)
  exact min_le_min hchart (Nat.add_le_add (Nat.add_le_add hlift (Nat.mul_le_mul_left _ (hgraph _)))
    (Nat.mul_le_mul_left _ (hgraph _)))

private theorem ceil_mono {a b : ℕ} (h : a ≤ b) (l : ℕ) : ceilDiv a l ≤ ceilDiv b l :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h l) 1)

theorem physical_mono {x y : Shape} (h : InBox x y) (hx : 3 * x.t ≤ x.j)
    (hy : 3 * y.t ≤ y.j) (l : ℕ) : physicalPrice x l ≤ physicalPrice y l := by
  let p := x.chamber
  let p' := y.chamber
  let q : Shape := ⟨4013, 1650, 550⟩
  let L := taylorLength
  let A := q.plus (p.scale 4)
  let A' := q.plus (p'.scale 4)
  have hp := normalize_mono h
  have hpc : Chamber p := normalize_chamber x hx
  have hp'c : Chamber p' := normalize_chamber y hy
  have hqc : Chamber q := by dsimp [Chamber, q]; omega
  have ha : InBox A A' := plus_mono (box_refl q) (scale_mono hp 4)
  have hac : Chamber A := plus_chamber hqc (scale_chamber hpc 4)
  have ha'c : Chamber A' := plus_chamber hqc (scale_chamber hp'c 4)
  have hs := surface_mono hp hp'c hqc
  have hb := (chart_mono (L+1) hp).1
  have hmain : (81879 + 2*46594) * x.b * q.b * (chart (L+1) p).b ≤
      (81879 + 2*46594) * y.b * q.b * (chart (L+1) p').b := by
    have := h.1
    gcongr
  have hcurve := mixed_mono hp (box_refl q) ha (chart_mono L hp) hp'c hqc ha'c hqc hac (chart_chamber L p)
  have hpoint := mixed_mono hp (box_refl q) ha hp hp'c hqc ha'c hqc hac hpc
  have hcurve' := mixed_mono hp hp hp (chart_mono L hp) hp'c hp'c hp'c hpc hpc (chart_chamber L p)
  have hpoint' := mixed_mono hp hp hp hp hp'c hp'c hp'c hpc hpc hpc
  have htc := Nat.mul_le_mul_left 2 h.2.2
  have hc := Nat.add_le_add hcurve (Nat.mul_le_mul htc hcurve')
  have hn := Nat.add_le_add hpoint (Nat.mul_le_mul htc hpoint')
  have hgeom := Nat.add_le_add (Nat.mul_le_mul_left 81879 hc) (Nat.mul_le_mul_left (2*46594) hn)
  have hraw := Nat.mul_le_mul_right q.b (Nat.mul_le_mul_left (2*133671) h.1)
  exact Nat.add_le_add
    (Nat.add_le_add (ceil_mono (Nat.add_le_add (ceil_mono hs _) (ceil_mono hmain _)) l) hraw)
    (ceil_mono hgeom _)

end K1_13_8_2
end PackSource_K1_13_8_2Tariff

section PackSource_K1_13_8_3Mass
set_option autoImplicit true
namespace K1_13_8_3

open K1_13 K1_13_8
open scoped BigOperators

def start : Shape := ⟨1, 3, 1⟩

def indexOrder (j : ℕ) : ℕ :=
  if j < 4 then 1 else if j < 5 then 4 else if j < 14 then 17 else
    if j < 40 then 54 else 68

theorem indexOrder_pos (j : ℕ) : 0 < indexOrder j := by
  unfold indexOrder
  split_ifs <;> omega

theorem indexOrder_mono : Monotone indexOrder := by
  intro j k hjk
  unfold indexOrder
  split_ifs <;> omega

private def positive (j : ℕ) : ℕ := shifted 2 j 3 + shifted 2 j 4 + shifted 2 j 5
private def negative (j : ℕ) : ℕ :=
  shifted 1 j 1 + shifted 1 j 2 + shifted 1 j 3 + shifted 3 j 6

private theorem across_unshifted {b r j v : ℕ} (h : j < v + r * (b + 1)) :
    across b r j v = shifted r j v := by
  simp [across, shifted, show ¬ v + r * (b + 1) ≤ j by omega]

private theorem symbols_unshifted {b j : ℕ} (h : j ≤ b) :
    fastSymbols b j = (b + 1) * coefficient 0 j + positive j - negative j := by
  simp only [fastSymbols, positive, negative]
  rw [across_unshifted (by omega), across_unshifted (by omega),
    across_unshifted (by omega), across_unshifted (by omega),
    across_unshifted (by omega), across_unshifted (by omega),
    across_unshifted (by omega)]
  omega

private theorem symbols_upper (b j : ℕ) :
    fastSymbols b j ≤ (b + 1) * coefficient 0 j + positive j := by
  unfold fastSymbols positive across
  have h₁ := Nat.sub_le (shifted 2 j 3) (shifted 2 j (3 + 2 * (b + 1)))
  have h₂ := Nat.sub_le (shifted 2 j 4) (shifted 2 j (4 + 2 * (b + 1)))
  have h₃ := Nat.sub_le (shifted 2 j 5) (shifted 2 j (5 + 2 * (b + 1)))
  omega

private abbrev massIndexWindow (a n : ℕ) : Prop :=
  ∀ i : Fin n,
    negative (a + i.val) ≤ 2363 * coefficient 0 (a + i.val) ∧
      fastSymbols 4012 (a + i.val) ≤ fastSymbols 4012 (a + i.val + 1)

private theorem massIndexBisect {a n : ℕ}
    (lo : massIndexWindow a (n / 2))
    (hi : massIndexWindow (a + n / 2) (n - n / 2)) : massIndexWindow a n := by
  intro i
  by_cases h : i.val < n / 2
  · exact lo ⟨i.val, h⟩
  · rw [show a + i.val = a + n / 2 + (i.val - n / 2) by omega]
    exact hi ⟨i.val - n / 2, by have := i.isLt; omega⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem index_checks : ∀ j : Fin 1651,
    negative j.val ≤ 2363 * coefficient 0 j.val ∧
      fastSymbols 4012 j.val ≤ fastSymbols 4012 (j.val + 1) := by
  have allChecks : massIndexWindow 0 1651 := by
    -- Each leaf covers 25 or 26 consecutive indices.
    iterate 6 (all_goals apply massIndexBisect)
    all_goals as_aux_lemma => decide +kernel
  intro j
  simpa only [Nat.zero_add] using allChecks j

/-- Relax the spent total-degree budget to zero while retaining the spent index. -/
private def indexBudget (j : ℕ) : ℕ :=
  if j ≤ 1650 then fastSymbols 4012 (1650 - j) else 0

private theorem remaining_le_index (b j : ℕ) : fastRemaining b j ≤ indexBudget j := by
  unfold fastRemaining indexBudget
  split
  next h =>
    obtain ⟨hb, hj⟩ := h
    rw [ite_eq_left hj, symbols_unshifted (by omega : 1650 - j ≤ 4012)]
    by_cases hlarge : 1650 - j ≤ 4012 - b
    · rw [symbols_unshifted hlarge]
      exact Nat.sub_le_sub_right
        (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _) _
    · apply (symbols_upper _ _).trans
      have hneg : negative (1650 - j) ≤ 2363 * coefficient 0 (1650 - j) :=
        (index_checks ⟨1650 - j, by omega⟩).1
      have hmul := Nat.mul_le_mul_right (coefficient 0 (1650 - j))
        (show (4012 - b) + 1 ≤ 1650 by omega)
      rw [show 4012 + 1 = 1650 + 2363 by decide, Nat.add_mul]
      simp only [Nat.add_mul, Nat.one_mul] at hmul ⊢
      omega
  next => exact Nat.zero_le _

private theorem symbols_mono_index {i j : ℕ} (hij : i ≤ j) (hj : j ≤ 1650) :
    fastSymbols 4012 i ≤ fastSymbols 4012 j := by
  induction j with
  | zero => rw [show i = 0 by omega]
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hij with he | hl
    · rw [he]
    · exact (ih (by omega) (by omega)).trans (index_checks ⟨j, by omega⟩).2

private theorem indexBudget_anti : Antitone indexBudget := by
  intro i j hij
  unfold indexBudget
  by_cases hj : j ≤ 1650
  · rw [ite_eq_left (hij.trans hj), ite_eq_left hj]
    exact symbols_mono_index (by omega) (by omega)
  · rw [ite_eq_right hj]
    exact Nat.zero_le _

private def indexMass (j L : ℕ) : ℕ :=
  (∑ k ∈ Finset.range (min L 550), indexBudget ((k + 1) * 3)) +
    ∑ k ∈ Finset.range (1650 / (3 + j)), indexBudget (L * 3 + (k + 1) * (3 + j))

private theorem available_le_index (x : Shape) (L : ℕ) :
    availableMass start x L ≤ indexMass x.j L := by
  simp only [availableMass, start, indexMass, show ¬ 3 = 0 by decide,
    ite_false, show 1650 / 3 = 550 by decide]
  exact Nat.add_le_add (Finset.sum_le_sum fun _ _ => remaining_le_index _ _)
    (Finset.sum_le_sum fun _ _ => remaining_le_index _ _)

private theorem indexMass_anti {i j : ℕ} (hij : i ≤ j) (L : ℕ) :
    indexMass j L ≤ indexMass i L := by
  unfold indexMass
  apply Nat.add_le_add_left
  apply sum_range_mono (Nat.div_le_div_left (by omega) (by omega))
  intro k _
  apply indexBudget_anti
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem order_tests :
    indexMass 4 3 < need ∧ indexMass 5 16 < need ∧
    indexMass 14 53 < need ∧ indexMass 40 67 < need := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals as_aux_lemma => decide +kernel

theorem checked_order (x : Shape) :
    0 < indexOrder x.j ∧
      (indexOrder x.j = 1 ∨ availableMass start x (indexOrder x.j - 1) < need) := by
  refine ⟨indexOrder_pos _, ?_⟩
  obtain ⟨h₄, h₅, h₁₄, h₄₀⟩ := order_tests
  unfold indexOrder
  split_ifs with ha hb hc hd
  · exact Or.inl rfl
  · exact Or.inr ((available_le_index _ _).trans_lt ((indexMass_anti (by omega) _).trans_lt h₄))
  · exact Or.inr ((available_le_index _ _).trans_lt ((indexMass_anti (by omega) _).trans_lt h₅))
  · exact Or.inr ((available_le_index _ _).trans_lt ((indexMass_anti (by omega) _).trans_lt h₁₄))
  · exact Or.inr ((available_le_index _ _).trans_lt ((indexMass_anti (by omega) _).trans_lt h₄₀))

end K1_13_8_3
end PackSource_K1_13_8_3Mass

section PackSource_K1_13_8_2Prices
set_option autoImplicit true
namespace K1_13_8_2

open K1_13 K1_13_8

private def peak (b j : ℕ) : Shape := ⟨b, j, min 10 (j / 3)⟩

/-- For each index, check the right end of each constant-order degree interval. -/
private def endpoint (b j : ℕ) : Prop :=
  b = 120 ∨ orderAt (peak b j) ≠ orderAt (peak (b + 1) j)

private instance (b j : ℕ) : Decidable (endpoint b j) := by unfold endpoint; infer_instance

private def peakCheck (b j : ℕ) : Bool :=
  if j ≤ 3 * b ∧ endpoint b j then
    decide (physicalPrice (peak b j) (orderAt (peak b j)) ≤ indexBudget j)
  else true

private def priceBand (start count : ℕ) : Bool :=
  allBelow (fun i => allBelow (fun b => peakCheck b (start + i)) 121) count

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- Extend a checked band by a single index, keeping the previous rows opaque. -/
private theorem priceBand_succ (start count : ℕ)
    (prev : priceBand start count = true)
    (row : allBelow (fun b => peakCheck b (start + count)) 121 = true) :
    priceBand start (count + 1) = true :=
  Bool.and_eq_true_iff.mpr ⟨row, prev⟩

private theorem pricesThrough3 : priceBand 3 1 = true :=
  priceBand_succ 3 0 rfl (by decide +kernel)

private theorem pricesThrough4 : priceBand 3 2 = true :=
  priceBand_succ 3 1 pricesThrough3 (by decide +kernel)

private theorem pricesThrough5 : priceBand 3 3 = true :=
  priceBand_succ 3 2 pricesThrough4 (by decide +kernel)

private theorem pricesThrough6 : priceBand 3 4 = true :=
  priceBand_succ 3 3 pricesThrough5 (by decide +kernel)

private theorem pricesThrough7 : priceBand 3 5 = true :=
  priceBand_succ 3 4 pricesThrough6 (by decide +kernel)

private theorem pricesThrough8 : priceBand 3 6 = true :=
  priceBand_succ 3 5 pricesThrough7 (by decide +kernel)

private theorem pricesThrough9 : priceBand 3 7 = true :=
  priceBand_succ 3 6 pricesThrough8 (by decide +kernel)

private theorem pricesThrough10 : priceBand 3 8 = true :=
  priceBand_succ 3 7 pricesThrough9 (by decide +kernel)

private theorem pricesThrough11 : priceBand 3 9 = true :=
  priceBand_succ 3 8 pricesThrough10 (by decide +kernel)

private theorem pricesThrough12 : priceBand 3 10 = true :=
  priceBand_succ 3 9 pricesThrough11 (by decide +kernel)

private theorem pricesThrough13 : priceBand 3 11 = true :=
  priceBand_succ 3 10 pricesThrough12 (by decide +kernel)

private theorem pricesThrough14 : priceBand 3 12 = true :=
  priceBand_succ 3 11 pricesThrough13 (by decide +kernel)

private theorem pricesThrough15 : priceBand 3 13 = true :=
  priceBand_succ 3 12 pricesThrough14 (by decide +kernel)

private theorem pricesThrough16 : priceBand 3 14 = true :=
  priceBand_succ 3 13 pricesThrough15 (by decide +kernel)

private theorem pricesThrough17 : priceBand 3 15 = true :=
  priceBand_succ 3 14 pricesThrough16 (by decide +kernel)

private theorem pricesThrough18 : priceBand 3 16 = true :=
  priceBand_succ 3 15 pricesThrough17 (by decide +kernel)

private theorem pricesThrough19 : priceBand 3 17 = true :=
  priceBand_succ 3 16 pricesThrough18 (by decide +kernel)

private theorem pricesThrough20 : priceBand 3 18 = true :=
  priceBand_succ 3 17 pricesThrough19 (by decide +kernel)

private theorem pricesThrough21 : priceBand 3 19 = true :=
  priceBand_succ 3 18 pricesThrough20 (by decide +kernel)

private theorem pricesThrough22 : priceBand 3 20 = true :=
  priceBand_succ 3 19 pricesThrough21 (by decide +kernel)

private theorem pricesThrough23 : priceBand 3 21 = true :=
  priceBand_succ 3 20 pricesThrough22 (by decide +kernel)

private theorem pricesThrough24 : priceBand 3 22 = true :=
  priceBand_succ 3 21 pricesThrough23 (by decide +kernel)

private theorem pricesThrough25 : priceBand 3 23 = true :=
  priceBand_succ 3 22 pricesThrough24 (by decide +kernel)

private theorem pricesThrough26 : priceBand 3 24 = true :=
  priceBand_succ 3 23 pricesThrough25 (by decide +kernel)

private theorem pricesThrough27 : priceBand 3 25 = true :=
  priceBand_succ 3 24 pricesThrough26 (by decide +kernel)

private theorem pricesThrough28 : priceBand 3 26 = true :=
  priceBand_succ 3 25 pricesThrough27 (by decide +kernel)

private theorem pricesThrough29 : priceBand 3 27 = true :=
  priceBand_succ 3 26 pricesThrough28 (by decide +kernel)

private theorem pricesThrough30 : priceBand 3 28 = true :=
  priceBand_succ 3 27 pricesThrough29 (by decide +kernel)

private theorem pricesThrough31 : priceBand 3 29 = true :=
  priceBand_succ 3 28 pricesThrough30 (by decide +kernel)

private theorem pricesThrough32 : priceBand 3 30 = true :=
  priceBand_succ 3 29 pricesThrough31 (by decide +kernel)

private theorem pricesThrough33 : priceBand 3 31 = true :=
  priceBand_succ 3 30 pricesThrough32 (by decide +kernel)

private theorem pricesThrough34 : priceBand 3 32 = true :=
  priceBand_succ 3 31 pricesThrough33 (by decide +kernel)

private theorem pricesThrough35 : priceBand 3 33 = true :=
  priceBand_succ 3 32 pricesThrough34 (by decide +kernel)

private theorem pricesThrough36 : priceBand 3 34 = true :=
  priceBand_succ 3 33 pricesThrough35 (by decide +kernel)

private theorem pricesThrough37 : priceBand 3 35 = true :=
  priceBand_succ 3 34 pricesThrough36 (by decide +kernel)

private theorem pricesThrough38 : priceBand 3 36 = true :=
  priceBand_succ 3 35 pricesThrough37 (by decide +kernel)

private theorem pricesThrough39 : priceBand 3 37 = true :=
  priceBand_succ 3 36 pricesThrough38 (by decide +kernel)

private theorem pricesThrough40 : priceBand 3 38 = true :=
  priceBand_succ 3 37 pricesThrough39 (by decide +kernel)

private theorem pricesThrough41 : priceBand 3 39 = true :=
  priceBand_succ 3 38 pricesThrough40 (by decide +kernel)

private theorem pricesThrough42 : priceBand 3 40 = true :=
  priceBand_succ 3 39 pricesThrough41 (by decide +kernel)

private theorem pricesThrough43 : priceBand 3 41 = true :=
  priceBand_succ 3 40 pricesThrough42 (by decide +kernel)

private theorem pricesThrough44 : priceBand 3 42 = true :=
  priceBand_succ 3 41 pricesThrough43 (by decide +kernel)

private theorem pricesThrough45 : priceBand 3 43 = true :=
  priceBand_succ 3 42 pricesThrough44 (by decide +kernel)

private theorem pricesThrough46 : priceBand 3 44 = true :=
  priceBand_succ 3 43 pricesThrough45 (by decide +kernel)

private theorem pricesThrough47 : priceBand 3 45 = true :=
  priceBand_succ 3 44 pricesThrough46 (by decide +kernel)

private theorem allPrices : priceBand 3 46 = true :=
  priceBand_succ 3 45 pricesThrough47 (by decide +kernel)

private theorem priceBand_spec {start count b j : ℕ}
    (h : priceBand start count = true) (hlo : start ≤ j) (hhi : j < start + count)
    (hb : b ≤ 120) (hshape : j ≤ 3 * b) (he : endpoint b j) :
    physicalPrice (peak b j) (orderAt (peak b j)) ≤ indexBudget j := by
  have hc := allBelow_spec (allBelow_spec h (k := j - start) (by omega)) (k := b) (by omega)
  rwa [Nat.add_sub_of_le hlo, peakCheck, ite_eq_left ⟨hshape, he⟩, decide_eq_true_eq] at hc

private theorem peak_bound (b j : ℕ) (hb : b ≤ 120) (hshape : j ≤ 3 * b)
    (hend : ∀ k ≤ 120, j ≤ 3 * k → endpoint k j →
      physicalPrice (peak k j) (orderAt (peak k j)) ≤ indexBudget j) :
    physicalPrice (peak b j) (orderAt (peak b j)) ≤ indexBudget j := by
  induction hb using Nat.decreasingInduction with
  | self => exact hend _ le_rfl hshape (Or.inl rfl)
  | of_succ b hb ih =>
    by_cases he : endpoint b j
    · exact hend b (by omega) hshape he
    · have horder : orderAt (peak b j) = orderAt (peak (b + 1) j) := by
        by_contra h
        exact he (Or.inr h)
      have ht : 3 * (peak b j).t ≤ j := by dsimp [peak]; omega
      have hmono : InBox (peak b j) (peak (b + 1) j) := ⟨by dsimp [peak]; omega, le_rfl, le_rfl⟩
      rw [horder]
      exact (physical_mono hmono ht ht _).trans (ih (by omega))

theorem price_upper {a : Shape} (ha : Valid a) (hbox : InBox a fullCap) :
    physicalPrice a (orderAt a) ≤ indexBudget a.j := by
  have hj : 3 ≤ a.j := (Nat.mul_le_mul_left 3 ha.1).trans ha.2.1
  have hmax : a.j ≤ 48 := hbox.2.1
  have ht : a.t ≤ (peak a.b a.j).t :=
    le_min hbox.2.2 ((Nat.le_div_iff_mul_le (by decide : 0 < 3)).mpr
      (by simpa [Nat.mul_comm] using ha.2.1))
  have htop : 3 * (peak a.b a.j).t ≤ a.j := by dsimp [peak]; omega
  have hmono : InBox a (peak a.b a.j) := ⟨le_rfl, le_rfl, ht⟩
  have horder : orderAt a = orderAt (peak a.b a.j) := rfl
  rw [horder]
  exact (physical_mono hmono ha.2.1 htop _).trans <|
    peak_bound _ _ hbox.1 ha.2.2 fun b hb hvalid he =>
      priceBand_spec allPrices hj (by omega) hb hvalid he

end K1_13_8_2
end PackSource_K1_13_8_2Prices

section PackSource_K1_13_8_4Mixed
set_option autoImplicit true
namespace K1_13_8_4

open K1_13

/-- Increasing only total degree leaves the index and top-degree constraints fixed. -/
def TotalLE (a A : Shape) : Prop := a.b ≤ A.b ∧ a.j = A.j ∧ a.t = A.t

def IndexFits (a : Shape) : Prop := 3 * a.t ≤ a.j

theorem TotalLE.refl (a : Shape) : TotalLE a a := ⟨le_rfl, rfl, rfl⟩

private def mixedZ (p q r s : Shape) : ℤ :=
  difference (difference (difference (difference volume32 p) q) r) s ⟨0, 0, 0⟩

private def indexCubic (a : Shape) : ℤ :=
  let j : ℤ := a.j
  let t : ℤ := a.t
  8*j^2*t - 24*j*t^2 + 24*t^3

private def unusedIndex (a : Shape) : ℤ := (a.j : ℤ) - 3 * (a.t : ℤ)

/-- The triple difference of the coefficient of total degree in the volume. -/
private def totalCoeff (q r s : Shape) : ℤ :=
  let u := unusedIndex q
  let v := unusedIndex r
  let w := unusedIndex s
  let x : ℤ := q.t
  let y : ℤ := r.t
  let z : ℤ := s.t
  16 * (u*v*z + u*y*w + x*v*w) + 48 * (u*y*z + x*v*z + x*y*w) + 144*x*y*z

private theorem totalCoeff_nonneg {q r s : Shape}
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
private theorem mixed_first {p P q r s : Shape}
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

private theorem swap12 (a b c d : Shape) : mixed32 a b c d = mixed32 b a c d := by
  unfold mixed32
  rw [difference_comm volume32 a b]

private theorem swap23 (a b c d : Shape) : mixed32 a b c d = mixed32 a c b d := by
  unfold mixed32
  rw [difference_comm (difference volume32 a) b c]

private theorem swap34 (a b c d : Shape) : mixed32 a b c d = mixed32 a b d c := by
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
end PackSource_K1_13_8_4Mixed

section PackSource_K1_13_8_4Tariff
set_option autoImplicit true
namespace K1_13_8_4

open K1_13 K1_13_8

def indexRate : ℕ := 2960000000000000

private theorem chamber_mono {a A : Shape} (h : TotalLE a A) :
    TotalLE a.chamber A.chamber :=
  ⟨max_le_max h.1 (le_of_eq h.2.1), h.2⟩

private theorem chart_mono (L : ℕ) {a A : Shape} (h : TotalLE a A) :
    TotalLE (chart L a) (chart L A) := by
  rcases h with ⟨hb, hj, ht⟩
  refine ⟨?_, by simp [chart, hj], by simp [chart, hj, ht]⟩
  dsimp only [chart]
  rw [hj]
  gcongr

private theorem lifted_mono (L : ℕ) {a A : Shape} (h : TotalLE a A) :
    TotalLE (liftedChart L a) (liftedChart L A) := by
  rcases h with ⟨hb, hj, ht⟩
  refine ⟨?_, by simp [liftedChart, hj], by simp [liftedChart, hj, ht]⟩
  dsimp only [liftedChart]
  rw [hj]
  gcongr

private def liftedInput (a : Shape) : Shape :=
  ⟨max a.b (a.j + 1), a.j + 1, min (a.t + 1) ((a.j + 1) / 3)⟩

private theorem liftedInput_mono {a A : Shape} (h : TotalLE a A) :
    TotalLE (liftedInput a) (liftedInput A) := by
  rcases h with ⟨hb, hj, ht⟩
  refine ⟨?_, by simp [liftedInput, hj], by simp [liftedInput, hj, ht]⟩
  dsimp only [liftedInput]
  rw [hj]
  exact max_le_max hb le_rfl

private theorem capped_fits (b j t : ℕ) : IndexFits ⟨b, j, min t (j / 3)⟩ := by
  change 3 * min t (j / 3) ≤ j
  exact (Nat.mul_le_mul_left 3 (min_le_right _ _)).trans (by omega)

private theorem surface_mono {p P q : Shape} (hp : TotalLE p P)
    (hp' : IndexFits p) (hq : IndexFits q) :
    surfaceNumerator32 p q ≤ surfaceNumerator32 P q := by
  let L := taylorLength
  have hqle := TotalLE.refl q
  have hold := mixed_mono_total hp hqle (chart_mono (L+1) hp) (chart_mono (L+2) hp)
    hp' hq (capped_fits _ _ _) (capped_fits _ _ _)
  have hnew := mixed_mono_total hp hqle (lifted_mono (L+1) hp) (lifted_mono (L+2) hp)
    hp' hq (capped_fits _ _ _) (capped_fits _ _ _)
  have hg₁ := mixed_mono_total hp hqle (liftedInput_mono hp) (lifted_mono (L+2) hp)
    hp' hq (capped_fits _ _ _) (capped_fits _ _ _)
  have hg₂ := mixed_mono_total hp hqle (liftedInput_mono hp) (lifted_mono (L+1) hp)
    hp' hq (capped_fits _ _ _) (capped_fits _ _ _)
  exact min_le_min hold (Nat.add_le_add
    (Nat.add_le_add hnew (Nat.mul_le_mul_left (L+1) hg₁)) (Nat.mul_le_mul_left (L+2) hg₂))

private theorem ceilDiv_mono {a b l : ℕ} (h : a ≤ b) : ceilDiv a l ≤ ceilDiv b l :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h _) _)

private theorem physical_mono {x y : Shape} (hx : TotalLE x y) (hv : IndexFits x) (l : ℕ) :
    physicalPrice x l ≤ physicalPrice y l := by
  let p := x.chamber
  let P := y.chamber
  let q : Shape := ⟨4013, 1650, 550⟩
  have hp : TotalLE p P := chamber_mono hx
  have hp' : IndexFits p := hv
  have hq := TotalLE.refl q
  have hq' : IndexFits q := le_rfl
  have hH := chart_mono taylorLength hp
  have hH' : IndexFits (chart taylorLength p) := capped_fits _ _ _
  have haux : TotalLE (q.plus (p.scale 4)) (q.plus (P.scale 4)) := by
    rcases hp with ⟨hb, hj, ht⟩
    exact ⟨Nat.add_le_add_left (Nat.mul_le_mul_left 4 hb) _, by simp [Shape.plus, Shape.scale, hj],
      by simp [Shape.plus, Shape.scale, ht]⟩
  have haux' : IndexFits (q.plus (p.scale 4)) := by
    change 3 * (q.t + 4 * p.t) ≤ q.j + 4 * p.j
    have h₁ : 3 * p.t ≤ p.j := hp'
    have h₂ : 3 * q.t ≤ q.j := hq'
    omega
  have hcurves₁ := mixed_mono_total hp hq haux hH hp' hq' haux' hH'
  have hcurves₂ := mixed_mono_total hp hp hp hH hp' hp' hp' hH'
  have hpoints₁ := mixed_mono_total hp hq haux hp hp' hq' haux' hp'
  have hpoints₂ := mixed_mono_total hp hp hp hp hp' hp' hp' hp'
  have hchart := (chart_mono (taylorLength+1) hp).1
  dsimp only [physicalPrice]
  rw [hx.2.2]
  refine Nat.add_le_add (Nat.add_le_add (ceilDiv_mono ?_) ?_) (ceilDiv_mono ?_)
  · exact Nat.add_le_add (ceilDiv_mono (surface_mono hp hp' hq'))
      (ceilDiv_mono (Nat.mul_le_mul
        (Nat.mul_le_mul_right q.b (Nat.mul_le_mul_left _ hx.1)) hchart))
  · exact Nat.mul_le_mul_right q.b (Nat.mul_le_mul_left _ hx.1)
  · exact Nat.add_le_add
      (Nat.mul_le_mul_left _ (Nat.add_le_add hcurves₁ (Nat.mul_le_mul_left _ hcurves₂)))
      (Nat.mul_le_mul_left _ (Nat.add_le_add hpoints₁ (Nat.mul_le_mul_left _ hpoints₂)))

section

set_option maxRecDepth 8192
set_option maxHeartbeats 0

-- Each closed decision checks the nine t values for a single derivative index.
private def tariffBoundaryRow (j : ℕ) : Prop :=
  ∀ t : Fin 9,
    let a : Shape := ⟨118, j, t.val⟩
    Valid a → physicalPrice a 78 ≤ indexRate * a.j

private theorem tariffBoundaryRow0 : tariffBoundaryRow 0 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow1 : tariffBoundaryRow 1 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow2 : tariffBoundaryRow 2 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow3 : tariffBoundaryRow 3 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow4 : tariffBoundaryRow 4 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow5 : tariffBoundaryRow 5 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow6 : tariffBoundaryRow 6 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow7 : tariffBoundaryRow 7 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow8 : tariffBoundaryRow 8 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow9 : tariffBoundaryRow 9 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow10 : tariffBoundaryRow 10 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow11 : tariffBoundaryRow 11 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow12 : tariffBoundaryRow 12 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow13 : tariffBoundaryRow 13 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow14 : tariffBoundaryRow 14 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow15 : tariffBoundaryRow 15 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow16 : tariffBoundaryRow 16 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow17 : tariffBoundaryRow 17 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow18 : tariffBoundaryRow 18 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow19 : tariffBoundaryRow 19 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow20 : tariffBoundaryRow 20 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow21 : tariffBoundaryRow 21 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow22 : tariffBoundaryRow 22 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow23 : tariffBoundaryRow 23 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow24 : tariffBoundaryRow 24 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow25 : tariffBoundaryRow 25 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow26 : tariffBoundaryRow 26 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow27 : tariffBoundaryRow 27 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow28 : tariffBoundaryRow 28 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow29 : tariffBoundaryRow 29 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow30 : tariffBoundaryRow 30 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow31 : tariffBoundaryRow 31 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow32 : tariffBoundaryRow 32 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow33 : tariffBoundaryRow 33 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow34 : tariffBoundaryRow 34 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow35 : tariffBoundaryRow 35 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow36 : tariffBoundaryRow 36 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow37 : tariffBoundaryRow 37 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow38 : tariffBoundaryRow 38 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow39 : tariffBoundaryRow 39 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow40 : tariffBoundaryRow 40 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow41 : tariffBoundaryRow 41 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariffBoundaryRow42 : tariffBoundaryRow 42 := by
  unfold tariffBoundaryRow
  decide +kernel

private theorem tariff_boundary :
    ∀ (j : Fin 43) (t : Fin 9),
      let a : Shape := ⟨118, j.val, t.val⟩
      Valid a → physicalPrice a 78 ≤ indexRate * a.j := by
  change ∀ j : Fin 43, tariffBoundaryRow j.val
  intro j
  fin_cases j
  · exact tariffBoundaryRow0
  · exact tariffBoundaryRow1
  · exact tariffBoundaryRow2
  · exact tariffBoundaryRow3
  · exact tariffBoundaryRow4
  · exact tariffBoundaryRow5
  · exact tariffBoundaryRow6
  · exact tariffBoundaryRow7
  · exact tariffBoundaryRow8
  · exact tariffBoundaryRow9
  · exact tariffBoundaryRow10
  · exact tariffBoundaryRow11
  · exact tariffBoundaryRow12
  · exact tariffBoundaryRow13
  · exact tariffBoundaryRow14
  · exact tariffBoundaryRow15
  · exact tariffBoundaryRow16
  · exact tariffBoundaryRow17
  · exact tariffBoundaryRow18
  · exact tariffBoundaryRow19
  · exact tariffBoundaryRow20
  · exact tariffBoundaryRow21
  · exact tariffBoundaryRow22
  · exact tariffBoundaryRow23
  · exact tariffBoundaryRow24
  · exact tariffBoundaryRow25
  · exact tariffBoundaryRow26
  · exact tariffBoundaryRow27
  · exact tariffBoundaryRow28
  · exact tariffBoundaryRow29
  · exact tariffBoundaryRow30
  · exact tariffBoundaryRow31
  · exact tariffBoundaryRow32
  · exact tariffBoundaryRow33
  · exact tariffBoundaryRow34
  · exact tariffBoundaryRow35
  · exact tariffBoundaryRow36
  · exact tariffBoundaryRow37
  · exact tariffBoundaryRow38
  · exact tariffBoundaryRow39
  · exact tariffBoundaryRow40
  · exact tariffBoundaryRow41
  · exact tariffBoundaryRow42

end

set_option maxHeartbeats 1000000 in
theorem tariff_le (a : Shape) (ha : Valid a)
    (hb : a.b ≤ 118) (hj : a.j ≤ 42) (ht : a.t ≤ 8) :
    edgePrice a 78 ≤ indexRate * a.j := by
  let A : Shape := ⟨118, a.j, a.t⟩
  have hA : Valid A :=
    ⟨ha.1, ha.2.1, ha.2.2.trans (Nat.mul_le_mul_left 3 hb)⟩
  have htotal : TotalLE a A := ⟨hb, rfl, rfl⟩
  have hboundary : physicalPrice A 78 ≤ indexRate * a.j :=
    tariff_boundary ⟨a.j, Nat.lt_succ_of_le hj⟩ ⟨a.t, Nat.lt_succ_of_le ht⟩ hA
  calc
    edgePrice a 78 ≤ physicalPrice a 78 := by
      unfold edgePrice
      split
      · exact min_le_left _ _
      · exact le_rfl
    _ ≤ physicalPrice A 78 := physical_mono htotal ha.2.1 78
    _ ≤ indexRate * a.j := hboundary

end K1_13_8_4
end PackSource_K1_13_8_4Tariff

section PackSource_K1_13_8_4Mass
set_option autoImplicit true
namespace K1_13_8_4

open K1_13 K1_13_8
open scoped BigOperators

def start : Shape := ⟨2, 6, 2⟩
def lowerOrder : ℕ := 78

private def coarseCount (b j : ℕ) : ℕ :=
  (b + 1) * coefficient 0 j + shifted 2 j 3 + shifted 2 j 4 + shifted 2 j 5

/-- When the total-degree budget dominates the index budget, every upper
shift in the Gaussian-binomial formula vanishes. -/
private def saturatedCount (b j : ℕ) : ℕ :=
  coarseCount b j - (shifted 1 j 1 + shifted 1 j 2 + shifted 1 j 3 + shifted 3 j 6)

private theorem count_of_index_le {b j : ℕ} (h : j ≤ b) :
    fastSymbols b j = saturatedCount b j := by
  have erase (r v : ℕ) (hr : 0 < r) : shifted r j (v + r * (b + 1)) = 0 := by
    have hmul : b + 1 ≤ r * (b + 1) := by
      simpa using Nat.mul_le_mul_right (b + 1) hr
    simp [shifted, show ¬ v + r * (b + 1) ≤ j by omega]
  have eraseOne (v : ℕ) : shifted 1 j (v + (b + 1)) = 0 := by
    simpa using erase 1 v (by decide)
  simp [fastSymbols, saturatedCount, coarseCount, across, erase, eraseOne]

private theorem count_le_coarse (b j : ℕ) : fastSymbols b j ≤ coarseCount b j := by
  have hacross (v : ℕ) : across b 2 j v ≤ shifted 2 j v := Nat.sub_le _ _
  unfold fastSymbols coarseCount
  exact (Nat.sub_le _ _).trans
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left (hacross 3) _) (hacross 4)) (hacross 5))

section

set_option maxRecDepth 8192
set_option maxHeartbeats 0

-- Check the two inequalities over short intervals, then join the intervals
-- using only their endpoints. The last coarse bound is checked separately.
private abbrev envelopeAt (j : ℕ) : Prop :=
  coarseCount j j ≤ saturatedCount 4012 j ∧
    saturatedCount 4012 j ≤ saturatedCount 4012 (j + 1)

private theorem joinEnvelopeBlocks {s a b : ℕ}
    (left : ∀ i : Fin a, envelopeAt (i.val + s))
    (right : ∀ i : Fin b, envelopeAt (i.val + (s + a)))
    (i : Fin (a + b)) : envelopeAt (i.val + s) := by
  by_cases h : i.val < a
  · exact left ⟨i.val, h⟩
  · have hi := i.isLt
    have hr := right ⟨i.val - a, by omega⟩
    change envelopeAt (i.val - a + (s + a)) at hr
    rwa [show i.val - a + (s + a) = i.val + s by omega] at hr

private theorem envelopeBlock0 : ∀ i : Fin 32, envelopeAt (i.val + 0) := by
  decide +kernel

private theorem envelopeBlock32 : ∀ i : Fin 32, envelopeAt (i.val + 32) := by
  decide +kernel

private theorem envelopeBlock64 : ∀ i : Fin 32, envelopeAt (i.val + 64) := by
  decide +kernel

private theorem envelopeBlock96 : ∀ i : Fin 32, envelopeAt (i.val + 96) := by
  decide +kernel

private theorem envelopeBlock128 : ∀ i : Fin 32, envelopeAt (i.val + 128) := by
  decide +kernel

private theorem envelopeBlock160 : ∀ i : Fin 32, envelopeAt (i.val + 160) := by
  decide +kernel

private theorem envelopeBlock192 : ∀ i : Fin 32, envelopeAt (i.val + 192) := by
  decide +kernel

private theorem envelopeBlock224 : ∀ i : Fin 32, envelopeAt (i.val + 224) := by
  decide +kernel

private theorem envelopeBlock256 : ∀ i : Fin 32, envelopeAt (i.val + 256) := by
  decide +kernel

private theorem envelopeBlock288 : ∀ i : Fin 32, envelopeAt (i.val + 288) := by
  decide +kernel

private theorem envelopeBlock320 : ∀ i : Fin 32, envelopeAt (i.val + 320) := by
  decide +kernel

private theorem envelopeBlock352 : ∀ i : Fin 32, envelopeAt (i.val + 352) := by
  decide +kernel

private theorem envelopeBlock384 : ∀ i : Fin 32, envelopeAt (i.val + 384) := by
  decide +kernel

private theorem envelopeBlock416 : ∀ i : Fin 32, envelopeAt (i.val + 416) := by
  decide +kernel

private theorem envelopeBlock448 : ∀ i : Fin 32, envelopeAt (i.val + 448) := by
  decide +kernel

private theorem envelopeBlock480 : ∀ i : Fin 32, envelopeAt (i.val + 480) := by
  decide +kernel

private theorem envelopeBlock512 : ∀ i : Fin 32, envelopeAt (i.val + 512) := by
  decide +kernel

private theorem envelopeBlock544 : ∀ i : Fin 32, envelopeAt (i.val + 544) := by
  decide +kernel

private theorem envelopeBlock576 : ∀ i : Fin 32, envelopeAt (i.val + 576) := by
  decide +kernel

private theorem envelopeBlock608 : ∀ i : Fin 32, envelopeAt (i.val + 608) := by
  decide +kernel

private theorem envelopeBlock640 : ∀ i : Fin 32, envelopeAt (i.val + 640) := by
  decide +kernel

private theorem envelopeBlock672 : ∀ i : Fin 32, envelopeAt (i.val + 672) := by
  decide +kernel

private theorem envelopeBlock704 : ∀ i : Fin 32, envelopeAt (i.val + 704) := by
  decide +kernel

private theorem envelopeBlock736 : ∀ i : Fin 32, envelopeAt (i.val + 736) := by
  decide +kernel

private theorem envelopeBlock768 : ∀ i : Fin 32, envelopeAt (i.val + 768) := by
  decide +kernel

private theorem envelopeBlock800 : ∀ i : Fin 32, envelopeAt (i.val + 800) := by
  decide +kernel

private theorem envelopeBlock832 : ∀ i : Fin 32, envelopeAt (i.val + 832) := by
  decide +kernel

private theorem envelopeBlock864 : ∀ i : Fin 32, envelopeAt (i.val + 864) := by
  decide +kernel

private theorem envelopeBlock896 : ∀ i : Fin 32, envelopeAt (i.val + 896) := by
  decide +kernel

private theorem envelopeBlock928 : ∀ i : Fin 32, envelopeAt (i.val + 928) := by
  decide +kernel

private theorem envelopeBlock960 : ∀ i : Fin 32, envelopeAt (i.val + 960) := by
  decide +kernel

private theorem envelopeBlock992 : ∀ i : Fin 32, envelopeAt (i.val + 992) := by
  decide +kernel

private theorem envelopeBlock1024 : ∀ i : Fin 32, envelopeAt (i.val + 1024) := by
  decide +kernel

private theorem envelopeBlock1056 : ∀ i : Fin 32, envelopeAt (i.val + 1056) := by
  decide +kernel

private theorem envelopeBlock1088 : ∀ i : Fin 32, envelopeAt (i.val + 1088) := by
  decide +kernel

private theorem envelopeBlock1120 : ∀ i : Fin 32, envelopeAt (i.val + 1120) := by
  decide +kernel

private theorem envelopeBlock1152 : ∀ i : Fin 32, envelopeAt (i.val + 1152) := by
  decide +kernel

private theorem envelopeBlock1184 : ∀ i : Fin 32, envelopeAt (i.val + 1184) := by
  decide +kernel

private theorem envelopeBlock1216 : ∀ i : Fin 32, envelopeAt (i.val + 1216) := by
  decide +kernel

private theorem envelopeBlock1248 : ∀ i : Fin 32, envelopeAt (i.val + 1248) := by
  decide +kernel

private theorem envelopeBlock1280 : ∀ i : Fin 32, envelopeAt (i.val + 1280) := by
  decide +kernel

private theorem envelopeBlock1312 : ∀ i : Fin 32, envelopeAt (i.val + 1312) := by
  decide +kernel

private theorem envelopeBlock1344 : ∀ i : Fin 32, envelopeAt (i.val + 1344) := by
  decide +kernel

private theorem envelopeBlock1376 : ∀ i : Fin 32, envelopeAt (i.val + 1376) := by
  decide +kernel

private theorem envelopeBlock1408 : ∀ i : Fin 32, envelopeAt (i.val + 1408) := by
  decide +kernel

private theorem envelopeBlock1440 : ∀ i : Fin 32, envelopeAt (i.val + 1440) := by
  decide +kernel

private theorem envelopeBlock1472 : ∀ i : Fin 32, envelopeAt (i.val + 1472) := by
  decide +kernel

private theorem envelopeBlock1504 : ∀ i : Fin 32, envelopeAt (i.val + 1504) := by
  decide +kernel

private theorem envelopeBlock1536 : ∀ i : Fin 32, envelopeAt (i.val + 1536) := by
  decide +kernel

private theorem envelopeBlock1568 : ∀ i : Fin 32, envelopeAt (i.val + 1568) := by
  decide +kernel

private theorem envelopeBlock1600 : ∀ i : Fin 32, envelopeAt (i.val + 1600) := by
  decide +kernel

private theorem envelopeBlock1632 : ∀ i : Fin 18, envelopeAt (i.val + 1632) := by
  decide +kernel

private theorem envelopeBlocks (i : Fin 1650) : envelopeAt i.val :=
  (joinEnvelopeBlocks (s := 0) (a := 832) (b := 818)
    (joinEnvelopeBlocks (s := 0) (a := 416) (b := 416)
      (joinEnvelopeBlocks (s := 0) (a := 192) (b := 224)
        (joinEnvelopeBlocks (s := 0) (a := 96) (b := 96)
          (joinEnvelopeBlocks (s := 0) (a := 32) (b := 64)
            envelopeBlock0
            (joinEnvelopeBlocks (s := 32) (a := 32) (b := 32)
              envelopeBlock32
              envelopeBlock64))
          (joinEnvelopeBlocks (s := 96) (a := 32) (b := 64)
            envelopeBlock96
            (joinEnvelopeBlocks (s := 128) (a := 32) (b := 32)
              envelopeBlock128
              envelopeBlock160)))
        (joinEnvelopeBlocks (s := 192) (a := 96) (b := 128)
          (joinEnvelopeBlocks (s := 192) (a := 32) (b := 64)
            envelopeBlock192
            (joinEnvelopeBlocks (s := 224) (a := 32) (b := 32)
              envelopeBlock224
              envelopeBlock256))
          (joinEnvelopeBlocks (s := 288) (a := 64) (b := 64)
            (joinEnvelopeBlocks (s := 288) (a := 32) (b := 32)
              envelopeBlock288
              envelopeBlock320)
            (joinEnvelopeBlocks (s := 352) (a := 32) (b := 32)
              envelopeBlock352
              envelopeBlock384))))
      (joinEnvelopeBlocks (s := 416) (a := 192) (b := 224)
        (joinEnvelopeBlocks (s := 416) (a := 96) (b := 96)
          (joinEnvelopeBlocks (s := 416) (a := 32) (b := 64)
            envelopeBlock416
            (joinEnvelopeBlocks (s := 448) (a := 32) (b := 32)
              envelopeBlock448
              envelopeBlock480))
          (joinEnvelopeBlocks (s := 512) (a := 32) (b := 64)
            envelopeBlock512
            (joinEnvelopeBlocks (s := 544) (a := 32) (b := 32)
              envelopeBlock544
              envelopeBlock576)))
        (joinEnvelopeBlocks (s := 608) (a := 96) (b := 128)
          (joinEnvelopeBlocks (s := 608) (a := 32) (b := 64)
            envelopeBlock608
            (joinEnvelopeBlocks (s := 640) (a := 32) (b := 32)
              envelopeBlock640
              envelopeBlock672))
          (joinEnvelopeBlocks (s := 704) (a := 64) (b := 64)
            (joinEnvelopeBlocks (s := 704) (a := 32) (b := 32)
              envelopeBlock704
              envelopeBlock736)
            (joinEnvelopeBlocks (s := 768) (a := 32) (b := 32)
              envelopeBlock768
              envelopeBlock800)))))
    (joinEnvelopeBlocks (s := 832) (a := 416) (b := 402)
      (joinEnvelopeBlocks (s := 832) (a := 192) (b := 224)
        (joinEnvelopeBlocks (s := 832) (a := 96) (b := 96)
          (joinEnvelopeBlocks (s := 832) (a := 32) (b := 64)
            envelopeBlock832
            (joinEnvelopeBlocks (s := 864) (a := 32) (b := 32)
              envelopeBlock864
              envelopeBlock896))
          (joinEnvelopeBlocks (s := 928) (a := 32) (b := 64)
            envelopeBlock928
            (joinEnvelopeBlocks (s := 960) (a := 32) (b := 32)
              envelopeBlock960
              envelopeBlock992)))
        (joinEnvelopeBlocks (s := 1024) (a := 96) (b := 128)
          (joinEnvelopeBlocks (s := 1024) (a := 32) (b := 64)
            envelopeBlock1024
            (joinEnvelopeBlocks (s := 1056) (a := 32) (b := 32)
              envelopeBlock1056
              envelopeBlock1088))
          (joinEnvelopeBlocks (s := 1120) (a := 64) (b := 64)
            (joinEnvelopeBlocks (s := 1120) (a := 32) (b := 32)
              envelopeBlock1120
              envelopeBlock1152)
            (joinEnvelopeBlocks (s := 1184) (a := 32) (b := 32)
              envelopeBlock1184
              envelopeBlock1216))))
      (joinEnvelopeBlocks (s := 1248) (a := 192) (b := 210)
        (joinEnvelopeBlocks (s := 1248) (a := 96) (b := 96)
          (joinEnvelopeBlocks (s := 1248) (a := 32) (b := 64)
            envelopeBlock1248
            (joinEnvelopeBlocks (s := 1280) (a := 32) (b := 32)
              envelopeBlock1280
              envelopeBlock1312))
          (joinEnvelopeBlocks (s := 1344) (a := 32) (b := 64)
            envelopeBlock1344
            (joinEnvelopeBlocks (s := 1376) (a := 32) (b := 32)
              envelopeBlock1376
              envelopeBlock1408)))
        (joinEnvelopeBlocks (s := 1440) (a := 96) (b := 114)
          (joinEnvelopeBlocks (s := 1440) (a := 32) (b := 64)
            envelopeBlock1440
            (joinEnvelopeBlocks (s := 1472) (a := 32) (b := 32)
              envelopeBlock1472
              envelopeBlock1504))
          (joinEnvelopeBlocks (s := 1536) (a := 64) (b := 50)
            (joinEnvelopeBlocks (s := 1536) (a := 32) (b := 32)
              envelopeBlock1536
              envelopeBlock1568)
            (joinEnvelopeBlocks (s := 1600) (a := 32) (b := 18)
              envelopeBlock1600
              envelopeBlock1632)))))) i

private theorem coarse_le_envelope (j : Fin 1651) :
    coarseCount j.val j.val ≤ saturatedCount 4012 j.val := by
  by_cases h : j.val < 1650
  · exact (envelopeBlocks ⟨j.val, h⟩).1
  · have hj := j.isLt
    rw [show j.val = 1650 by omega]
    decide +kernel

private theorem envelope_step (j : Fin 1650) :
    saturatedCount 4012 j.val ≤ saturatedCount 4012 (j.val + 1) :=
  (envelopeBlocks j).2

end

private theorem envelope_mono {j J : ℕ} (h : j ≤ J) (hJ : J ≤ 1650) :
    saturatedCount 4012 j ≤ saturatedCount 4012 J := by
  induction J with
  | zero =>
    have : j = 0 := by omega
    subst j
    exact le_rfl
  | succ n ih =>
    by_cases hj : j = n + 1
    · subst j
      exact le_rfl
    · exact (ih (by omega) (by omega)).trans (envelope_step ⟨n, by omega⟩)

private theorem count_le_envelope {b j : ℕ} (hb : b ≤ 4012) (hj : j ≤ 1650) :
    fastSymbols b j ≤ saturatedCount 4012 j := by
  have hmono {a b : ℕ} (h : a ≤ b) : coarseCount a j ≤ coarseCount b j := by
    unfold coarseCount
    gcongr
  by_cases h : j ≤ b
  · rw [count_of_index_le h]
    exact Nat.sub_le_sub_right (hmono hb) _
  · exact (count_le_coarse _ _).trans ((hmono (by omega : b ≤ j)).trans
      (coarse_le_envelope ⟨j, by omega⟩))

private def tailUpper (k : ℕ) : ℕ :=
  if 462 + (k + 1) * 9 ≤ 1650
  then saturatedCount 4012 (1650 - (462 + (k + 1) * 9)) else 0

private theorem remaining_le_tail (b j k : ℕ) (h : 462 + (k + 1) * 9 ≤ j) :
    fastRemaining b j ≤ tailUpper k := by
  by_cases hbox : b ≤ 4012 ∧ j ≤ 1650
  · have hk : 462 + (k + 1) * 9 ≤ 1650 := h.trans hbox.2
    simp only [fastRemaining, hbox, tailUpper, ite_eq_left, hk]
    exact (count_le_envelope (Nat.sub_le _ _) (Nat.sub_le _ _)).trans
      (envelope_mono (by omega) (Nat.sub_le _ _))
  · simp [fastRemaining, hbox]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem mass_envelope_test :
    (∑ k ∈ Finset.range 77, fastRemaining ((k + 1) * 2) ((k + 1) * 6)) +
      (∑ k ∈ Finset.range (1650 / 9), tailUpper k) < need := by
  decide +kernel

theorem mass_lt_need (x : Shape) (hx : Valid x) :
    availableMass start x (lowerOrder - 1) < need := by
  have hj : 9 ≤ 6 + x.j := by
    rcases hx with ⟨ht, hj, _⟩
    omega
  change (∑ k ∈ Finset.range 77, fastRemaining ((k + 1) * 2) ((k + 1) * 6)) +
    (∑ k ∈ Finset.range (1650 / (6 + x.j)),
      fastRemaining (154 + (k + 1) * (2 + x.b)) (462 + (k + 1) * (6 + x.j))) < need
  refine lt_of_le_of_lt (Nat.add_le_add_left ?_ _) mass_envelope_test
  apply sum_range_mono (Nat.div_le_div_left hj (by decide))
  intro k _
  exact remaining_le_tail _ _ _ (Nat.add_le_add_left (Nat.mul_le_mul_left (k + 1) hj) _)

end K1_13_8_4
end PackSource_K1_13_8_4Mass

section PackSource_K1_13_8_2Order
set_option autoImplicit true
namespace K1_13_8_2

open K1_13 K1_13_8
open scoped BigOperators

private def sumBelow (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumBelow f n + f n

private theorem sumBelow_eq (f : ℕ → ℕ) (n : ℕ) :
    sumBelow f n = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih => rw [sumBelow, Finset.sum_range_succ, ih]

private def positiveTerms (b j : ℕ) : ℕ :=
  (b + 1) * coefficient 0 j + shifted 2 j 3 + shifted 2 j 4 + shifted 2 j 5

private def negativeTerms (j : ℕ) : ℕ :=
  shifted 1 j 1 + shifted 1 j 2 + shifted 1 j 3 + shifted 3 j 6

private def upperRemaining (b j : ℕ) : ℕ :=
  if b ≤ 4012 ∧ j ≤ 1650 then positiveTerms (4012 - b) (1650 - j) else 0

private def upperMass (b j : ℕ) : ℕ :=
  sumBelow (fun k => upperRemaining ((k + 1) * b) ((k + 1) * j)) (1650 / j)

private def correction (k : ℕ) : ℕ := negativeTerms (1650 - (k + 1) * 48)

private def correctionTotal : ℕ := sumBelow correction 12

private def coefficientCheck (r : ℕ) : Bool :=
  allBelow (fun j => decide (coefficient r j ≤ coefficient r (j + 1))) 1650

-- Check the four monotonicity rows separately so the kernel can release each reduction.
section
set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem orderCoefficientRow0 : coefficientCheck 0 = true := by decide +kernel

private theorem orderCoefficientRow1 : coefficientCheck 1 = true := by decide +kernel

private theorem orderCoefficientRow2 : coefficientCheck 2 = true := by decide +kernel

private theorem orderCoefficientRow3 : coefficientCheck 3 = true := by decide +kernel

end

private theorem coefficientChecks :
    coefficientCheck 0 = true ∧ coefficientCheck 1 = true ∧
    coefficientCheck 2 = true ∧ coefficientCheck 3 = true :=
  ⟨orderCoefficientRow0, orderCoefficientRow1, orderCoefficientRow2, orderCoefficientRow3⟩

private theorem coefficient_mono {r j k : ℕ} (hr : r ≤ 3) (hjk : j ≤ k) (hk : k ≤ 1650) :
    coefficient r j ≤ coefficient r k := by
  have hcheck : coefficientCheck r = true := by
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with rfl | rfl | rfl | rfl
    · exact coefficientChecks.1
    · exact coefficientChecks.2.1
    · exact coefficientChecks.2.2.1
    · exact coefficientChecks.2.2.2
  induction k with
  | zero => simp [Nat.eq_zero_of_le_zero hjk]
  | succ k ih =>
    rcases Nat.lt_or_eq_of_le hjk with hlt | rfl
    · have hs : coefficient r k ≤ coefficient r (k + 1) :=
        of_decide_eq_true (allBelow_spec hcheck (by omega))
      exact (ih (by omega) (by omega)).trans hs
    · exact le_rfl

private theorem shifted_mono {r j k : ℕ} (hr : r ≤ 3) (hjk : j ≤ k) (hk : k ≤ 1650)
    (v : ℕ) : shifted r j v ≤ shifted r k v := by
  by_cases hv : v ≤ j
  · simpa [shifted, hv, hv.trans hjk] using
      (coefficient_mono hr (show j - v ≤ k - v by omega) (show k - v ≤ 1650 by omega))
  · simp [shifted, hv]

private theorem upperRemaining_anti {b c j k : ℕ} (hb : b ≤ c) (hj : j ≤ k) :
    upperRemaining c k ≤ upperRemaining b j := by
  by_cases h : c ≤ 4012 ∧ k ≤ 1650
  · have h' : b ≤ 4012 ∧ j ≤ 1650 := ⟨hb.trans h.1, hj.trans h.2⟩
    simp only [upperRemaining, h, h', positiveTerms]
    have hidx : 1650 - k ≤ 1650 - j := by omega
    have hcap : 1650 - j ≤ 1650 := Nat.sub_le _ _
    exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
      (Nat.mul_le_mul (by omega) (coefficient_mono (by decide : 0 ≤ 3) hidx hcap))
      (shifted_mono (by decide : 2 ≤ 3) hidx hcap 3))
      (shifted_mono (by decide : 2 ≤ 3) hidx hcap 4))
      (shifted_mono (by decide : 2 ≤ 3) hidx hcap 5)
  · simp [upperRemaining, h]

private theorem positive_part_le (b j : ℕ) :
    (b + 1) * coefficient 0 j + across b 2 j 3 + across b 2 j 4 + across b 2 j 5
      ≤ positiveTerms b j := by
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add le_rfl (Nat.sub_le _ _))
    (Nat.sub_le _ _)) (Nat.sub_le _ _)

private theorem remaining_le_upper (b j : ℕ) :
    fastRemaining b j ≤ upperRemaining b j := by
  by_cases h : b ≤ 4012 ∧ j ≤ 1650
  · simp only [fastRemaining, upperRemaining, h, fastSymbols]
    exact (Nat.sub_le _ _).trans (positive_part_le _ _)
  · simp [fastRemaining, upperRemaining, h]

private def correctionCheck : Bool :=
  allBelow (fun k => decide (correction k ≤ upperRemaining ((k + 1) * 120) ((k + 1) * 48))) 12

private theorem corrections_fit : correctionCheck = true := by decide +kernel

/-- On the first twelve layers all the delayed negative shifts vanish.
Charge the negative contribution of the full-box endpoint as a common deduction. -/
private theorem layer_add_correction {b j k : ℕ} (hb : b ≤ 120) (hj : j ≤ 48) (hk : k < 12) :
    fastRemaining ((k + 1) * b) ((k + 1) * j) + correction k ≤
      upperRemaining ((k + 1) * b) ((k + 1) * j) := by
  let d := k + 1
  let B := 4012 - d * b
  let J := 1650 - d * j
  have hdb := Nat.mul_le_mul_left d hb
  have hdj := Nat.mul_le_mul_left d hj
  have hB : d * b ≤ 4012 := by omega
  have hJ : d * j ≤ 1650 := by omega
  have hlarge : J < B := by dsimp [B, J]; omega
  have hz (r v : ℕ) (h : J < v + r * (B + 1)) :
      shifted r J (v + r * (B + 1)) = 0 := by
    simp [shifted, Nat.not_le.mpr h]
  have hneg (r v : ℕ) (h : J < v + r * (B + 1)) :
      across B r J v = shifted r J v := by simp [across, hz r v h]
  have h1 := hneg 1 1 (by omega)
  have h2 := hneg 1 2 (by omega)
  have h3 := hneg 1 3 (by omega)
  have h6 := hneg 3 6 (by omega)
  have hidx : 1650 - d * 48 ≤ J := by dsimp [J]; omega
  have hJcap : J ≤ 1650 := Nat.sub_le _ _
  have hc : correction k ≤ negativeTerms J :=
    Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
      (shifted_mono (by decide : 1 ≤ 3) hidx hJcap 1)
      (shifted_mono (by decide : 1 ≤ 3) hidx hJcap 2))
      (shifted_mono (by decide : 1 ≤ 3) hidx hJcap 3))
      (shifted_mono (by decide : 3 ≤ 3) hidx hJcap 6)
  have hc' : correction k ≤ upperRemaining (d * b) (d * j) :=
    (of_decide_eq_true (allBelow_spec corrections_fit hk)).trans (upperRemaining_anti hdb hdj)
  change fastRemaining (d * b) (d * j) + correction k ≤ upperRemaining (d * b) (d * j)
  rw [fastRemaining, ite_eq_left ⟨hB, hJ⟩]
  rw [upperRemaining, ite_eq_left ⟨hB, hJ⟩] at hc' ⊢
  change fastSymbols B J + correction k ≤ positiveTerms B J
  have hp := positive_part_le B J
  unfold fastSymbols
  rw [h1, h2, h3, h6]
  change _ - negativeTerms J + correction k ≤ positiveTerms B J
  change correction k ≤ positiveTerms B J at hc'
  omega

private theorem mass_le_upper {b j b₀ j₀ : ℕ} (hb : b ≤ 120) (hj : j ≤ 48)
    (hj₀ : 0 < j₀) (hb₀ : b₀ ≤ b) (hjj : j₀ ≤ j) :
    zeroMass b j + correctionTotal ≤ upperMass b₀ j₀ := by
  have hpos : 0 < j := hj₀.trans_le hjj
  have hn : 12 ≤ 1650 / j := (Nat.le_div_iff_mul_le hpos).mpr (by omega)
  let extra := fun k => if k < 12 then correction k else 0
  have hsum : correctionTotal = ∑ k ∈ Finset.range (1650 / j), extra k := by
    unfold correctionTotal
    rw [sumBelow_eq, sum_range_truncate (m := 12)
      (fun k hk => ite_eq_right (Nat.not_lt.mpr hk)) hn]
    exact Finset.sum_congr rfl fun k hk => (ite_eq_left (Finset.mem_range.mp hk)).symm
  rw [zeroMass, hsum, ← Finset.sum_add_distrib, upperMass, sumBelow_eq]
  have hlen : 1650 / j ≤ 1650 / j₀ := Nat.div_le_div_left hjj hj₀
  apply sum_range_mono hlen
  intro k _
  refine le_trans ?_ (upperRemaining_anti (Nat.mul_le_mul_left _ hb₀) (Nat.mul_le_mul_left _ hjj))
  by_cases hk : k < 12
  · simpa [extra, hk] using layer_add_correction hb hj hk
  · simpa [extra, hk] using remaining_le_upper ((k + 1) * b) ((k + 1) * j)

private def thresholdCheck (s : Threshold) : Bool :=
  decide (0 < s.j ∧ (s.l - 1) * fastRemaining 0 0 + upperMass s.b s.j < need + correctionTotal)

-- Each endpoint has its own mass sum. Replay those sums independently.
section
set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem orderThreshold118_48 : thresholdCheck ⟨118, 48, 58⟩ = true := by
  decide +kernel

private theorem orderThreshold103_43 : thresholdCheck ⟨103, 43, 57⟩ = true := by
  decide +kernel

private theorem orderThreshold67_30 : thresholdCheck ⟨67, 30, 52⟩ = true := by
  decide +kernel

private theorem orderThreshold11_16 : thresholdCheck ⟨11, 16, 34⟩ = true := by
  decide +kernel

private theorem orderThreshold4_11 : thresholdCheck ⟨4, 11, 17⟩ = true := by
  decide +kernel

private theorem orderThreshold48_4 : thresholdCheck ⟨48, 4, 15⟩ = true := by
  decide +kernel

private theorem orderThreshold5_9 : thresholdCheck ⟨5, 9, 7⟩ = true := by
  decide +kernel

private theorem orderThreshold27_6 : thresholdCheck ⟨27, 6, 3⟩ = true := by
  decide +kernel

private theorem orderThreshold19_7 : thresholdCheck ⟨19, 7, 2⟩ = true := by
  decide +kernel

private theorem orderThreshold36_4 : thresholdCheck ⟨36, 4, 2⟩ = true := by
  decide +kernel

private theorem orderThreshold9_8 : thresholdCheck ⟨9, 8, 2⟩ = true := by
  decide +kernel

private theorem orderThreshold26_6 : thresholdCheck ⟨26, 6, 2⟩ = true := by
  decide +kernel

end

private theorem thresholdChecks : thresholds.all thresholdCheck = true := by
  simp only [thresholds, List.all_cons, List.all_nil, Bool.true_and,
    orderThreshold118_48, orderThreshold103_43, orderThreshold67_30, orderThreshold11_16,
    orderThreshold4_11, orderThreshold48_4, orderThreshold5_9, orderThreshold27_6,
    orderThreshold19_7, orderThreshold36_4, orderThreshold9_8, orderThreshold26_6]

private theorem orderFor_select (b j : ℕ) (ss : List Threshold) :
    1 ≤ orderFor b j ss ∧
    (orderFor b j ss = 1 ∨ ∃ s ∈ ss, s.b ≤ b ∧ s.j ≤ j ∧ orderFor b j ss = s.l) := by
  induction ss with
  | nil => simp [orderFor]
  | cons s ss ih =>
    unfold orderFor
    let p := if s.b ≤ b ∧ s.j ≤ j then s.l else 1
    change 1 ≤ max p (orderFor b j ss) ∧
      (max p (orderFor b j ss) = 1 ∨ ∃ q ∈ s :: ss,
        q.b ≤ b ∧ q.j ≤ j ∧ max p (orderFor b j ss) = q.l)
    refine ⟨ih.1.trans (le_max_right _ _), ?_⟩
    rcases le_total p (orderFor b j ss) with h | h
    · rw [max_eq_right h]
      rcases ih.2 with h1 | ⟨q, hq, hb, hj, hl⟩
      · exact Or.inl h1
      · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hb, hj, hl⟩
    · rw [max_eq_left h]
      by_cases hbox : s.b ≤ b ∧ s.j ≤ j
      · exact Or.inr ⟨s, List.mem_cons_self, hbox.1, hbox.2, ite_eq_left hbox⟩
      · exact Or.inl (ite_eq_right hbox)

private theorem orderFor_mono {b b' j j' : ℕ} (hb : b ≤ b') (hj : j ≤ j') (ss : List Threshold) :
    orderFor b j ss ≤ orderFor b' j' ss := by
  induction ss with
  | nil => exact le_rfl
  | cons s ss ih =>
    unfold orderFor
    by_cases h : s.b ≤ b ∧ s.j ≤ j
    · rw [ite_eq_left h, ite_eq_left ⟨h.1.trans hb, h.2.trans hj⟩]
      exact max_le_max le_rfl ih
    · rw [ite_eq_right h, max_eq_right (orderFor_select b j ss).1]
      exact ih.trans (le_max_right _ _)

theorem orderAt_pos (x : Shape) : 0 < orderAt x := (orderFor_select x.b x.j thresholds).1

theorem orderAt_mono {x y : Shape} (hb : x.b ≤ y.b) (hj : x.j ≤ y.j) :
    orderAt x ≤ orderAt y := orderFor_mono hb hj thresholds

theorem orderAt_certified (x : Shape) (hb : x.b ≤ 120) (hj : x.j ≤ 48) :
    orderAt x = 1 ∨ availableMass zeroShape x (orderAt x - 1) < need := by
  rcases (orderFor_select x.b x.j thresholds).2 with he | ⟨s, hs, hsb, hsj, he⟩
  · exact Or.inl he
  · have hcheck := of_decide_eq_true (List.all_eq_true.mp thresholdChecks s hs)
    have hm := mass_le_upper hb hj hcheck.1 hsb hsj
    have hlt := hcheck.2
    change orderAt x = s.l at he
    right
    rw [he]
    simp only [availableMass, zeroShape, Nat.zero_add, Nat.mul_zero, ite_true]
    change (s.l - 1) * fastRemaining 0 0 + zeroMass x.b x.j < need
    omega

end K1_13_8_2
end PackSource_K1_13_8_2Order

section PackSource_K1_13_8_1Coefficients
set_option autoImplicit true
namespace K1_13_8_1

open K1_13_8

/-- Extend each coefficient row by zero to negative indices. -/
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

private theorem scaled_coefficient (r q s : ℕ) (hq : 3 ≤ q) (hs : s < 6) :
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

/-- The denominator factors of row zero leave the cumulative unit series. -/
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

/-- Row r includes the additional denominator factor of weight r. -/
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
end PackSource_K1_13_8_1Coefficients

section PackSource_K1_13_8_1Counting
set_option autoImplicit true
namespace K1_13_8_1

open scoped BigOperators

/-- Add an exponent of weight `k + 1` to a count using weights zero through `k`. -/
private def count (base : ℕ → ℤ → ℤ) : ℕ → ℕ → ℤ → ℤ
  | 0, b, j => base b j
  | k + 1, b, j =>
      ∑ i ∈ Finset.range (b + 1), count base k (b - i) (j - ((k : ℤ) + 1) * i)

private def exactBase (_ : ℕ) (j : ℤ) : ℤ := step j
private def boxBase (b : ℕ) (j : ℤ) : ℤ := ((b : ℤ) + 1) * step j

private theorem count_zero_degree (base : ℕ → ℤ → ℤ) (k : ℕ) (j : ℤ) :
    count base k 0 j = base 0 j := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [count] using ih

private theorem count_succ_degree (base : ℕ → ℤ → ℤ) (k b : ℕ) (j : ℤ) :
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

private theorem count_neg (base : ℕ → ℤ → ℤ)
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

private theorem count_clip (base : ℕ → ℤ → ℤ)
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

private theorem boxBase_neg (b : ℕ) (j : ℤ) (h : j < 0) : boxBase b j = 0 := by
  simp [boxBase, step, not_le.mpr h]

private theorem symbols_count (b j : ℕ) :
    (K1_13.symbols b j : ℤ) = count boxBase 3 b j := by
  rw [count_clip boxBase boxBase_neg 2]
  simp_rw [count_clip boxBase boxBase_neg 1, count_clip boxBase boxBase_neg 0]
  simp [K1_13.symbols, count, boxBase, step, Nat.cast_sum, Nat.cast_add]

private theorem box_eq_sum (k b : ℕ) (j : ℤ) :
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

/-- Apply the numerator factors with shifts `a, a+1, ..., a+k-1`. -/
private def factors (a : ℤ) : ℕ → (ℤ → ℤ) → (ℤ → ℤ)
  | 0, f => f
  | k + 1, f => factors a k (difference (a + k) f)

private theorem factors_first (a : ℤ) (k : ℕ) (f : ℤ → ℤ) :
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

private theorem factors_sub (a : ℤ) (k : ℕ) (f g : ℤ → ℤ) :
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

private theorem factors_shift (a w : ℤ) (k : ℕ) (f : ℤ → ℤ) :
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

private theorem denominator_diff (k : ℕ) (hk : k < 3) :
    difference ((k : ℤ) + 1) (denominator (k + 1)) = denominator k := by
  interval_cases k <;> rfl

/-- The degree-`b` Gaussian-binomial numerator acting on its cumulative denominator. -/
def gaussian (k b : ℕ) : ℤ → ℤ := factors ((b : ℤ) + 1) k (denominator k)

private theorem gaussian_zero (k : ℕ) (hk : k ≤ 3) (j : ℤ) : gaussian k 0 j = step j := by
  induction k with
  | zero => exact core_step j
  | succ k ih =>
      have hd := denominator_diff k (by omega)
      simpa only [gaussian, factors, Nat.cast_zero, zero_add, add_comm (1 : ℤ) k, hd] using
        ih (by omega)

private theorem gaussian_succ (k b : ℕ) (hk : k < 3) (j : ℤ) :
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

private theorem exact_gaussian (k b : ℕ) (hk : k ≤ 3) (j : ℤ) :
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
end PackSource_K1_13_8_1Counting

section PackSource_K1_13_8_4Proof
set_option autoImplicit true
namespace K1_13_8_4

open K1_13 K1_13_8

/-- Each factor pays from the unspent derivative-index budget. -/
private def potential (x : Shape) : ℕ := indexRate * (42 - x.j)

theorem proof : K1_13_8.c4 := by
  change Bellman start 125142013343379695
  refine ⟨potential, fun _ => lowerOrder, by decide, ?_, ?_⟩
  · intro x hx _
    exact ⟨by change 0 < lowerOrder; decide, Or.inr (mass_lt_need x hx)⟩
  · intro y a _ ha hbox
    change 2 + (y.b + a.b) ≤ 120 ∧ 6 + (y.j + a.j) ≤ 48 ∧
      2 + (y.t + a.t) ≤ 10 at hbox
    rcases hbox with ⟨hb, hj, ht⟩
    have hprice := tariff_le a ha (by omega) (by omega) (by omega)
    have hunspent : a.j + (42 - (y.j + a.j)) = 42 - y.j := by omega
    calc
      edgePrice a lowerOrder + potential (y.plus a) ≤
          indexRate * a.j + indexRate * (42 - (y.j + a.j)) :=
        Nat.add_le_add_right hprice _
      _ = potential y := by rw [← Nat.mul_add, hunspent, potential]

end K1_13_8_4
end PackSource_K1_13_8_4Proof

section PackSource_K1_13_8_2Proof
set_option autoImplicit true
namespace K1_13_8_2

open K1_13 K1_13_8

private theorem edge_le_physical (a : Shape) (l : ℕ) : edgePrice a l ≤ physicalPrice a l := by
  unfold edgePrice
  split
  · exact min_le_left _ _
  · exact le_rfl

private theorem zero_plus (x : Shape) : zeroShape.plus x = x := by
  cases x
  simp [zeroShape, Shape.plus]

theorem proof : K1_13_8.c2 := by
  refine ⟨potential, orderAt, by decide, ?_, ?_⟩
  · intro x _ hx
    rw [zero_plus] at hx
    exact ⟨orderAt_pos x, orderAt_certified x hx.1 hx.2.1⟩
  · intro y a _ ha hbox
    let x := y.plus a
    have hcap : InBox x fullCap := by simpa only [zero_plus] using hbox
    have haBox : InBox a x := ⟨Nat.le_add_left _ _, Nat.le_add_left _ _, Nat.le_add_left _ _⟩
    have hb : InBox a fullCap :=
      ⟨haBox.1.trans hcap.1, haBox.2.1.trans hcap.2.1, haBox.2.2.trans hcap.2.2⟩
    have hl := orderAt_mono haBox.1 haBox.2.1
    have hprice : edgePrice a (orderAt x) ≤ indexBudget a.j :=
      (edgePrice_anti a (orderAt_pos a) hl).trans
        ((edge_le_physical a _).trans (price_upper ha hb))
    have hidx : a.j + (48 - x.j) = 48 - y.j := by
      have h := hcap.2.1
      change _ + _ ≤ 48 at h
      dsimp [x, Shape.plus]
      omega
    calc
      edgePrice a (orderAt x) + potential x ≤ indexBudget a.j + potential x :=
        Nat.add_le_add_right hprice _
      _ ≤ potential y := by
        have hdiv : limit * a.j / 48 + limit * (48 - x.j) / 48 ≤
            (limit * a.j + limit * (48 - x.j)) / 48 := Nat.div_add_div_le_add_div
        rw [← Nat.mul_add, hidx] at hdiv
        exact hdiv

end K1_13_8_2
end PackSource_K1_13_8_2Proof

section PackSource_K1_13_8_1Proof
set_option autoImplicit true
namespace K1_13_8_1

open K1_13_8
open scoped BigOperators

/-- Summation over degrees turns each train of numerator shifts into two endpoint coefficients. -/
private theorem sum_shifted (b r : ℕ) (hr : 1 ≤ r) (hr' : r ≤ 3) (j v : ℤ) :
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

private theorem shifted_cast (r j v : ℕ) :
    (shifted r j v : ℤ) = row r ((j : ℤ) - v) := by
  unfold shifted
  split
  · rw [← Int.ofNat_sub ‹v ≤ j›, row_nat]
  · have h : (j : ℤ) - v < 0 := by omega
    simp [row_neg _ h]

private theorem across_cast (b r j v : ℕ) (hr : 1 ≤ r) (hr' : r ≤ 3) :
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

private theorem cast_sub_of_eq {count positive negative : ℕ}
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
end PackSource_K1_13_8_1Proof

section PackSource_K1_13_1_1BudgetH
set_option autoImplicit true
namespace K1_13_1_1

set_option maxRecDepth 30000
set_option Elab.async false
set_option maxHeartbeats 4000000

private theorem grade110 : fastGrade 110 = 5032 := by decide +kernel
private theorem grade111 : fastGrade 111 = 4448 := by decide +kernel
private theorem grade112 : fastGrade 112 = 3884 := by decide +kernel
private theorem grade113 : fastGrade 113 = 3384 := by decide +kernel
private theorem grade114 : fastGrade 114 = 2936 := by decide +kernel
private theorem grade115 : fastGrade 115 = 2520 := by decide +kernel
private theorem grade116 : fastGrade 116 = 2145 := by decide +kernel
private theorem grade117 : fastGrade 117 = 1825 := by decide +kernel
private theorem grade118 : fastGrade 118 = 1520 := by decide +kernel
private theorem grade119 : fastGrade 119 = 1270 := by decide +kernel
private theorem grade120 : fastGrade 120 = 1030 := by decide +kernel

private theorem sumStep (f : ℕ → ℕ) (n a b : ℕ)
    (ha : sumRange n f = a) (hb : f n = b) :
    sumRange (n + 1) f = a + b :=
  (show sumRange (n + 1) f = sumRange n f + f n from rfl).trans (congrArg₂ Nat.add ha hb)

private def gradeFrom (i : ℕ) : ℕ := fastGrade (i + 110)

private theorem prefix110 : sumRange 1 gradeFrom = 5032 :=
  sumStep gradeFrom 0 0 5032 rfl grade110
private theorem prefix111 : sumRange 2 gradeFrom = 9480 :=
  sumStep gradeFrom 1 5032 4448 prefix110 grade111
private theorem prefix112 : sumRange 3 gradeFrom = 13364 :=
  sumStep gradeFrom 2 9480 3884 prefix111 grade112
private theorem prefix113 : sumRange 4 gradeFrom = 16748 :=
  sumStep gradeFrom 3 13364 3384 prefix112 grade113
private theorem prefix114 : sumRange 5 gradeFrom = 19684 :=
  sumStep gradeFrom 4 16748 2936 prefix113 grade114
private theorem prefix115 : sumRange 6 gradeFrom = 22204 :=
  sumStep gradeFrom 5 19684 2520 prefix114 grade115
private theorem prefix116 : sumRange 7 gradeFrom = 24349 :=
  sumStep gradeFrom 6 22204 2145 prefix115 grade116
private theorem prefix117 : sumRange 8 gradeFrom = 26174 :=
  sumStep gradeFrom 7 24349 1825 prefix116 grade117
private theorem prefix118 : sumRange 9 gradeFrom = 27694 :=
  sumStep gradeFrom 8 26174 1520 prefix117 grade118
private theorem prefix119 : sumRange 10 gradeFrom = 28964 :=
  sumStep gradeFrom 9 27694 1270 prefix118 grade119
theorem budgetH : sumRange 11 (fun i => fastGrade (i + 110)) = 29994 :=
  sumStep gradeFrom 10 28964 1030 prefix119 grade120

end K1_13_1_1
end PackSource_K1_13_1_1BudgetH

section PackSource_K1_6Aux2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace K1_6

open K1 Polynomial
open FrobeniusLocator ProximityPrize.Benchmark

/-- Clear denominators and remove seed content before applying Gauss's lemma. -/
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

/-- Saturation preserves the common divisor degree and splits that many distinct
domain roots. More roots than fixed nodes gives a new common zero. -/
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

-- Transport the bound with symbolic factors so checking it does not enumerate the index type.
private theorem k16Aux2_count_bound {c n n' H b : ℕ}
    (hn : n = n') (hc : c ≤ n * H) (hb : n' * H = b) : c ≤ b :=
  hb ▸ hn ▸ hc

/-- Cover the marked slopes by one nonzero seed polynomial per nonfixed node. -/
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
end PackSource_K1_6Aux2

section PackSource_K1_13_7_1Weights
set_option autoImplicit true
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
end PackSource_K1_13_7_1Weights

section PackSource_K1_13_7_1_1Translate
set_option autoImplicit true
namespace K1_13_7_1_1

noncomputable section
open K1_13 K1_13_6 K1_13_7_1 MvPolynomial

private def translate (a : GeoPoint) : GeoJets →ₐ[GeoField] GeoJets :=
  bind₁ (fun i => MvPolynomial.X i - C (a i))

private theorem translate_inverse (a : GeoPoint) (f : GeoJets) :
    translate (-a) (translate a f) = f := by
  unfold translate
  rw [bind₁_bind₁]
  have hi (i : Fin 4) :
      bind₁ (fun j => MvPolynomial.X j - C ((-a) j)) (MvPolynomial.X i - C (a i)) = MvPolynomial.X i := by
    simp
  simp only [hi, bind₁_X_left, AlgHom.id_apply]

private theorem eval_translate (a y : GeoPoint) (f : GeoJets) :
    eval (y + a) (translate a f) = eval y f := by
  change aeval (y + a) (bind₁ (fun i => MvPolynomial.X i - C (a i)) f) = aeval y f
  rw [aeval_bind₁]
  simp

private theorem translate_fits (a : GeoPoint) {f : GeoJets} {p : Shape}
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

private theorem isolated_translate (a y : GeoPoint) {f g u v : GeoJets}
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

/-- Translate the whole finite set off the coordinate hyperplanes while
retaining its cardinality, all three degree bounds, and each isolation
certificate. -/
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
end PackSource_K1_13_7_1_1Translate

section PackSource_K1_13_6_1Cuts
set_option autoImplicit true
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

private theorem atJet_eq_shift_constant (P : Row 4) (S : Geom[X]) :
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
end PackSource_K1_13_6_1Cuts

section PackSource_K1_13_6_1Split
set_option autoImplicit true
namespace K1_13_6_1
noncomputable section
open Polynomial K1 K1_13 K1_13_6
open scoped BigOperators

/-- The leading-coefficient test gives a first regular derivative on any
component containing a mark. -/
def c1 : Prop :=
  ∀ f surface S, SmallFactor f → OnFactor f S → toGeneric f ∈ surface → surface ≤ markIdeal S →
    ∃ r, CanonicalChart f surface r ∧
      InBox (shape (separant ((separant^[r]) f))) (anchorBox f)

/-- The low local colength bounds the least proper ambient Hasse partial. -/
def c2 : Prop :=
  ∀ f Q l surface (hZ : (intersectionIdeal f Q).IsMinimalPrime surface),
    SmallFactor f → (¬ f ∣ Q) → InBox (shape Q) cutterBox →
    ∃ v : ℕ, 0 < v ∧ v ≤ (shape f).b * cutterBox.b ∧
      cycleLength (intersectionIdeal f Q) surface hZ.isPrime = (v : ℕ∞) ∧
      (v < l → ∃ P : Row 4, toGeneric P ∉ surface ∧ InBox (shape P) cutterBox ∧
        ∀ S, OrderAt Q S l → atJet P S = 0)

/-- A noninvariant surface has a proper tangent cut. Higher chart orders
charge the genuine local length on the anchor/derivative cycle. -/
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

/-- Sparse degree for adaptive proper cuts. Distinct primary surfaces
spend their local weights, with each higher derivative cycle counted once. -/
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

/-- A single auxiliary curve gives a recovered coefficient slice and a
finite set of marks where its chart fails. -/
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

private theorem factor_mem {f Q : Row 4} {surface : Ideal GeoJets}
    (hZ : (intersectionIdeal f Q).IsMinimalPrime surface) :
    toGeneric f ∈ surface :=
  hZ.le (Ideal.subset_span (Set.mem_insert _ _))

private theorem one_surface (h1 : c1) (h2 : c2) (h3 : c3)
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
end PackSource_K1_13_6_1Split

section PackSource_K1_13_6_1_4Split
set_option autoImplicit true
namespace K1_13_6_1_4

noncomputable section

open K1_13 K1_13_6 K1_13_6_1 K1_13_7_1
open scoped BigOperators

/-- A proper supported divisor debits its integral surface once.
Scale the fixed cutter by taking its sixth power. -/
def c1 : Prop :=
  ∀ (surface : Ideal GeoJets) (P : GeoJets) (a h : Shape),
    surface.IsPrime → ringKrullDim (GeoJets ⧸ surface) = 2 →
    FullChamber a → FullChamber h → P ∉ surface → GeoFits P a →
    6 * (∑ C ∈ (surface ⊔ Ideal.span {P}).minimalPrimesFinset,
      sectionDegree C (h.scale 6)) ≤ surfaceDegree surface (a.scale 6) (h.scale 6)

/-- The degree bound from adding section classes in the common chamber. -/
def c2 : Prop :=
  ∀ (surface : Ideal GeoJets) (a b h : Shape) (m n : ℕ),
    surface.IsPrime → ringKrullDim (GeoJets ⧸ surface) = 2 →
    FullChamber a → FullChamber b → FullChamber h → 0 < m →
    surfaceDegree surface (((a.scale m).plus (b.scale n)).scale 6) (h.scale 6) ≤
      m * surfaceDegree surface (a.scale 6) (h.scale 6) +
      n * surfaceDegree surface (b.scale 6) (h.scale 6)

/-- Weighted degree for the distinct surface components of one fixed proper pair.
The two generic sections are lattice-scaled and the whole bound is scaled by 36. -/
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

/-- Choose one tag for each charged derivative weight. The zero tag needs no derivative. -/
private theorem choose_charge {f Q : Row 4} {surface : Ideal GeoJets} {P : Row 4}
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
end PackSource_K1_13_6_1_4Split

section PackSource_K1_13_6_1_4_2Defs
set_option autoImplicit true
namespace K1_13_6_1_4_2

noncomputable section

open K1_13 K1_13_6

/-- The integer exponents of the full monomial system, independently of the
shape-dependent bounds in the coefficient index type. -/
def exponents (p : Shape) : Set (Fin 4 → ℕ) :=
  {e | e 0 + e 1 + e 2 + e 3 ≤ p.b ∧
    e 1 + 2 * e 2 + 3 * e 3 ≤ p.j ∧ e 3 ≤ p.t}

/-- The sixfold system in the exponent type used by the monomial map. -/
def latticeIndices (p : Shape) : Set (Fin 4 →₀ ℕ) :=
  {e | (fun i => e i) ∈ exponents (p.scale 6)}

instance (p : Shape) : Finite (latticeIndices p) := by
  refine ((Finsupp.finite_of_degree_le (6 * p.b)).subset ?_).to_subtype
  intro e he
  change e.degree ≤ 6 * p.b
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_four]
  have he' : e 0 + e 1 + e 2 + e 3 ≤ 6 * p.b := he.1
  simpa only [Nat.add_assoc] using he'

/-- The quadratic Hilbert coefficient in the sixfold monomial embedding.
The associated degree of a surface is twice this coefficient. -/
def topCoeff (surface : Ideal GeoJets) (p : Shape) : ℚ :=
  (MvPolynomial.affineHilbertPolynomial
    (surface.comap (MvPolynomial.monomialMap GeoField (latticeIndices p)).toRingHom)).coeff 2

end
end K1_13_6_1_4_2
end PackSource_K1_13_6_1_4_2Defs

section PackSource_K1_13_6_1_4_2Lattice
set_option autoImplicit true
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

theorem exponents_finite (p : Shape) : (exponents p).Finite := by
  rw [exponents_eq_image]
  exact (boxMonomials p).finite_toSet.image _

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

/-- Four-jet chamber caps add on lattice points when the index and top caps
are even. Spend the index-two exponents before the index-one exponents. -/
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

theorem exponents_scale_succ {p : Shape} (hp : Chamber p) (i : ℕ) :
    exponents ((p.scale (i + 1)).scale 6) =
      exponents ((p.scale i).scale 6) + exponents (p.scale 6) := by
  rw [show p.scale (i + 1) = (p.scale i).plus p from by
    cases p
    simp [Shape.scale, Shape.plus, Nat.add_mul]]
  exact exponents_plus_scaled (chamber_scale hp i) hp

theorem exponents_multidegree {a b h : Shape} (ha : Chamber a) (hb : Chamber b)
    (hh : Chamber h) (i j k : ℕ) :
    exponents ((((a.scale i).plus (b.scale j)).plus (h.scale k)).scale 6) =
      (exponents ((a.scale i).scale 6) + exponents ((b.scale j).scale 6)) +
        exponents ((h.scale k).scale 6) := by
  rw [exponents_plus_scaled (chamber_plus (chamber_scale ha i) (chamber_scale hb j))
    (chamber_scale hh k), exponents_plus_scaled (chamber_scale ha i) (chamber_scale hb j)]

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

/-- The diagonal embedding's filtration has exactly the sixfold box at
each dilation. This identifies its Hilbert function by taking quotient images. -/
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
end PackSource_K1_13_6_1_4_2Lattice

section PackSource_K1_13_6_1_4_2Split
set_option autoImplicit true
namespace K1_13_6_1_4_2

noncomputable section

open K1_13 K1_13_6 K1_13_6_1_4

/-- A mixed affine section length is the polarized diagonal Hilbert coefficient. -/
def c1 : Prop :=
  ∀ (surface : Ideal GeoJets) (a h : Shape),
    surface.IsPrime → ringKrullDim (GeoJets ⧸ surface) = 2 →
    FullChamber a → FullChamber h →
    (surfaceDegree surface (a.scale 6) (h.scale 6) : ℚ) =
      topCoeff surface (a.plus h) - topCoeff surface a - topCoeff surface h

/-- The quadratic coefficient on the diagonals of the common monomial
embedding is a single homogeneous quadratic form in their multidegrees. -/
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
end PackSource_K1_13_6_1_4_2Split

section PackSource_K1_13_6_1_4_2_1Defs
set_option autoImplicit true
namespace K1_13_6_1_4_2_1

noncomputable section

open K1_13 K1_13_6 K1_13_6_1 K1_13_7_1 K1_13_6_1_4 K1_13_6_1_4_2

/-- The image of a full sixfold shape in an affine coordinate algebra. -/
def piece {k : Type*} [Field k] (I : Ideal (MvPolynomial (Fin 4) k)) (p : Shape) :
    Submodule k (MvPolynomial (Fin 4) k ⧸ I) :=
  (MvPolynomial.restrictSupport k (latticeIndices p)).map (Ideal.Quotient.mkₐ k I).toLinearMap

abbrev Coeff (a h : Shape) := PairSectionField (a.scale 6) (h.scale 6)

/-- The ideal of the original surface after adjoining the section coefficients. -/
def extendIdeal (surface : Ideal GeoJets) (a h : Shape) :
    Ideal (MvPolynomial (Fin 4) (Coeff a h)) :=
  surface.map (MvPolynomial.map (algebraMap GeoField (Coeff a h)))

abbrev SurfaceRing (surface : Ideal GeoJets) (a h : Shape) :=
  MvPolynomial (Fin 4) (Coeff a h) ⧸ extendIdeal surface a h

def leftSection (a h : Shape) : MvPolynomial (Fin 4) (Coeff a h) :=
  sectionWith (a.scale 6) (Sum.inl : SectionIndex (a.scale 6) → PairSectionIndex (a.scale 6) (h.scale 6))

def rightSection (a h : Shape) : MvPolynomial (Fin 4) (Coeff a h) :=
  sectionWith (h.scale 6) (Sum.inr : SectionIndex (h.scale 6) → PairSectionIndex (a.scale 6) (h.scale 6))

/-- The affine section ideal keeps the quotient scheme structure. -/
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

/-- The bidegree piece with its homogenizing factors suppressed. -/
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
end PackSource_K1_13_6_1_4_2_1Defs

section PackSource_K1_13_6_1_4_2_1Dimensions
set_option autoImplicit true
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

/-- The box piece contains the image of every affine polynomial of bounded
ordinary total degree once the first weight is sufficiently large. -/
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

/-- Rank nullity for the cut map on one bidegree, followed by the dimension
formula for the two images of multiplication. -/
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
end PackSource_K1_13_6_1_4_2_1Dimensions

section PackSource_K1_13_6_1_4_2_1Hilbert
set_option autoImplicit true
namespace K1_13_6_1_4_2_1

noncomputable section

open K1_13 K1_13_6 K1_13_7_1 K1_13_6_1_4 K1_13_6_1_4_2 MvPolynomial
open scoped TensorProduct Polynomial

section ScalarExtension

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

private abbrev mapIdeal (I : Ideal (MvPolynomial (Fin 4) k)) : Ideal (MvPolynomial (Fin 4) L) :=
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

private theorem finrank_piece_baseChange (I : Ideal (MvPolynomial (Fin 4) k)) (p : Shape) :
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

private abbrev hilbertIdeal (surface : Ideal GeoJets) (p : Shape) :=
  surface.comap (monomialMap GeoField (latticeIndices p)).toRingHom

private abbrev hilbertPoly (surface : Ideal GeoJets) (p : Shape) :=
  affineHilbertPolynomial (hilbertIdeal surface p)

private theorem hilbertFunction_eq_piece (surface : Ideal GeoJets) {p : Shape}
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

private theorem ringKrullDim_ge_of_finite_injective {k A : Type*}
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

private theorem hilbertPoly_degree_le (surface : Ideal GeoJets) (hs : surface.IsPrime)
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

private theorem piece_le {k : Type*} [Field k] (I : Ideal (MvPolynomial (Fin 4) k)) {p q : Shape}
    (hb : p.b ≤ q.b) (hj : p.j ≤ q.j) (ht : p.t ≤ q.t) :
    piece I p ≤ piece I q := by
  apply Submodule.map_mono
  apply restrictSupport_mono
  intro e he
  exact ⟨he.1.trans (Nat.mul_le_mul_left 6 hb), he.2.1.trans (Nat.mul_le_mul_left 6 hj),
    he.2.2.trans (Nat.mul_le_mul_left 6 ht)⟩

private theorem axis_bounds {k : Type*} [Field k] (I : Ideal (MvPolynomial (Fin 4) k))
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

private theorem shift_coeff (P : ℚ[X]) (n : ℕ) (h : P.natDegree ≤ 2) :
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

private theorem plus_comm (a h : Shape) : a.plus h = h.plus a := by
  cases a
  cases h
  simp [Shape.plus, Nat.add_comm]

private theorem scale_plus (a h : Shape) (n : ℕ) :
    (a.plus h).scale n = (a.scale n).plus (h.scale n) := by
  cases a
  cases h
  simp [Shape.scale, Shape.plus, Nat.mul_add]

private def pieceRank {k : Type*} [Field k] (I : Ideal (MvPolynomial (Fin 4) k))
    (p : Shape) : ℕ :=
  Module.finrank k (piece I p)

private theorem exists_eval_finrank_piece (surface : Ideal GeoJets) (a h : Shape)
    {p : Shape} (hp : Chamber p) :
    ∃ M : ℕ, ∀ n ≥ M, (hilbertPoly surface p).eval (n : ℚ) =
      (pieceRank (extendIdeal surface a h) (p.scale n) : ℚ) := by
  obtain ⟨M, hM⟩ := exists_eval_affineHilbertPolynomial (hilbertIdeal surface p)
  exact ⟨M, fun n hn => by
    rw [hM n hn, hilbertFunction_eq_piece surface hp n]
    unfold pieceRank
    exact_mod_cast (finrank_piece_baseChange (L := Coeff a h) surface (p.scale n)).symm⟩

/-- The quadratic coefficient on the sum diagonal equals the two axial
coefficients plus the eventual mixed difference. -/
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

private abbrev cutPiece (surface : Ideal GeoJets) (a h : Shape) (i j : ℕ) :=
  (biPiece surface a h i j).map (cutMap surface a h).toLinearMap

private theorem cutPiece_mono (surface : Ideal GeoJets) (a h : Shape)
    {i j i' j' : ℕ} (hi : i ≤ i') (hj : j ≤ j') :
    cutPiece surface a h i j ≤ cutPiece surface a h i' j' := by
  apply Submodule.map_mono
  exact piece_le _ (Nat.add_le_add (Nat.mul_le_mul_right _ hi) (Nat.mul_le_mul_right _ hj))
    (Nat.add_le_add (Nat.mul_le_mul_right _ hi) (Nat.mul_le_mul_right _ hj))
    (Nat.add_le_add (Nat.mul_le_mul_right _ hi) (Nat.mul_le_mul_right _ hj))

private theorem rectangle_le (H : ℕ → ℕ → ℚ) (d : ℚ) (N : ℕ)
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

/-- A bounded quadratic diagonal and the stable mixed-difference identity
bound all ranks of the cut filtration. A maximal rank then exhausts the cut. -/
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
end PackSource_K1_13_6_1_4_2_1Hilbert

section PackSource_K1_13_6_1_4_2_1Split
set_option autoImplicit true
namespace K1_13_6_1_4_2_1

noncomputable section

open K1_13 K1_13_6 K1_13_6_1_4 K1_13_6_1_4_2

/-- The two sections are nonzerodivisors on the uncut surface, and the
first Koszul homology vanishes in sufficiently high bidegrees. -/
def c1 : Prop :=
  ∀ (surface : Ideal GeoJets) (a h : Shape),
    surface.IsPrime → ringKrullDim (GeoJets ⧸ surface) = 2 →
    FullChamber a → FullChamber h →
    Function.Injective (leftMul surface a h) ∧ Function.Injective (rightMul surface a h) ∧
    ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j →
      (biPiece surface a h i (j + 1)).map (leftMul surface a h) ⊓
        (biPiece surface a h (i + 1) j).map (rightMul surface a h) =
      (biPiece surface a h i j).map ((leftMul surface a h).comp (rightMul surface a h))

/-- Dehomogenizing the cut introduces no extra relations in sufficiently high bidegrees. -/
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
end PackSource_K1_13_6_1_4_2_1Split

section PackSource_K1_13_6_1_4_2_1_2Defs
set_option autoImplicit true
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

private theorem scalar_mem_box (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape)
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

/-- The bidegree Rees algebra of the two sixfold monomial filtrations. -/
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

/-- The ideal generated by the products indexing the standard product charts. -/
def irrelevant (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape) : Ideal (rees I a h) :=
  Ideal.span (Set.range (pairGen I a h))

/-- The product of the two constant coordinates. -/
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
end PackSource_K1_13_6_1_4_2_1_2Defs

section PackSource_K1_13_6_1_4_2_1_2Aux
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace K1_13_6_1_4_2_1_2

noncomputable section

open K1_13 K1_13_6 K1_13_7_1 K1_13_6_1_4
  K1_13_6_1_4_2 K1_13_6_1_4_2_1 MvPolynomial

private theorem sup_pow_le {R : Type*} [CommRing R] (J P : Ideal R) (m : ℕ) :
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

/-- Once the chart generators vanish on the boundary, the saturated part of
the cut ideal contributes no elements of sufficiently high ideal power. -/
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

private theorem left_coeff (r : Rees surface a h) (i j : ℕ) :
    ((rees (baseIdeal surface a h) a h).val (r * leftHom surface a h)).coeff (i + 1, j + 1) =
      leftMul surface a h (r.val.coeff (i, j + 1)) := by
  simp only [map_mul, leftHom, val_homogeneous]
  rw [show (i + 1, j + 1) = (i, j + 1) + (1, 0) by rfl,
    AddMonoidAlgebra.coeff_mul_single_add]
  exact mul_comm _ _

private theorem right_coeff (r : Rees surface a h) (i j : ℕ) :
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

private theorem degreeLE_le_box (ha : FullChamber a) {N i j : ℕ} (hi : N ≤ i) :
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

private theorem val_shift_pow (n : ℕ) :
    (rees (baseIdeal surface a h) a h).val (shift (baseIdeal surface a h) a h ^ n) =
      AddMonoidAlgebra.single (n, n) 1 := by
  induction n with
  | zero => simp only [pow_zero, map_one, AddMonoidAlgebra.one_def]; rfl
  | succ n ih =>
    rw [pow_succ, map_mul, ih]
    change (AddMonoidAlgebra.single (n, n) 1 : AddMonoidAlgebra
      (SurfaceRing surface a h) (ℕ × ℕ)) * AddMonoidAlgebra.single (1, 1) 1 = _
    rw [AddMonoidAlgebra.single_mul_single, mul_one, Prod.mk_add_mk]

/-- A relation on the affine cut can be homogenized after multiplying by
enough copies of the product of the two constant coordinates. -/
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
end PackSource_K1_13_6_1_4_2_1_2Aux

section PackSource_K1_13_6_1_4_1Defs
set_option autoImplicit true
namespace K1_13_6_1_4_1

noncomputable section

open K1_13 K1_13_6 K1_13_6_1
open MvPolynomial

/-- The coefficient extension for the test section. -/
def sliceMap (h : Shape) : GeoJets →+* SectionJets h :=
  MvPolynomial.map (algebraMap GeoField (SectionField h))

/-- The ideal of the affine generic test section, with its scheme structure. -/
def sliceIdeal (J : Ideal GeoJets) (h : Shape) : Ideal (SectionJets h) :=
  J.map (sliceMap h) ⊔ Ideal.span {genericSection h}

/-- The three support caps, over an arbitrary coefficient field. -/
def FitsBox {k : Type} [Field k] (Q : MvPolynomial (Fin 4) k) (a : Shape) : Prop :=
  Q.totalDegree ≤ a.b ∧ Q.weightedTotalDegree Fin.val ≤ a.j ∧ Q.degreeOf 3 ≤ a.t

abbrev CutField (k : Type) [Field k] (a : Shape) :=
  FractionRing (MvPolynomial (SectionIndex a) k)

/-- The independent cutter coefficients over the field of the test section. -/
def cutPolynomial (k : Type) [Field k] (a : Shape) :
    MvPolynomial (Fin 4) (CutField k a) :=
  ∑ m ∈ boxMonomials a,
    MvPolynomial.C (algebraMap (MvPolynomial (SectionIndex a) k) (CutField k a) (MvPolynomial.X m)) *
      ∏ i : Fin 4, MvPolynomial.X i ^ (m i).val

/-- The length of one more generic section after fixing the base field. -/
def genericCutLength {k : Type} [Field k] (I : Ideal (MvPolynomial (Fin 4) k))
    (a : Shape) : ℕ :=
  Module.finrank (CutField k a) (MvPolynomial (Fin 4) (CutField k a) ⧸
    (I.map (MvPolynomial.map (algebraMap k (CutField k a))) ⊔
      Ideal.span {cutPolynomial k a}))

end

end K1_13_6_1_4_1
end PackSource_K1_13_6_1_4_1Defs

section PackSource_K1_13_6_1_4_2_1_2Split
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace K1_13_6_1_4_2_1_2

noncomputable section

open K1_13 K1_13_6 K1_13_7_1 K1_13_6_1_4
  K1_13_6_1_4_2 K1_13_6_1_4_2_1 MvPolynomial

/-- Exact lattice addition gives standard generation in the two degrees. -/
def c1 : Prop :=
  ∀ {k : Type} [Field k] (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape),
    Chamber a → Chamber h →
    IsNoetherianRing (rees I a h) ∧
    ∀ (i j : ℕ) (x : Affine I) (hx : x ∈ box I a h (i, j)) (n : ℕ),
      n ≤ i → n ≤ j → homogeneous (i, j) x hx ∈ irrelevant I a h ^ n

/-- The generic pair has empty intersection with the boundary on all
standard product charts. -/
def c2 : Prop :=
  ∀ (surface : Ideal GeoJets) (a h : Shape),
    surface.IsPrime → ringKrullDim (GeoJets ⧸ surface) = 2 →
    FullChamber a → FullChamber h →
    ∀ e : latticeIndices a × latticeIndices h,
      ∃ m : ℕ, pairGen (baseIdeal surface a h) a h e ^ m ∈ homBoundaryIdeal surface a h

private theorem image_sum_le (surface : Ideal GeoJets) (a h : Shape) (i j : ℕ) :
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

private theorem boundary_bound (surface : Ideal GeoJets) (a h : Shape)
    (hNoeth : IsNoetherianRing (Rees surface a h))
    (hchart : ∀ e : latticeIndices a × latticeIndices h,
      ∃ m : ℕ, pairGen (baseIdeal surface a h) a h e ^ m ∈ homBoundaryIdeal surface a h) :
    ∃ N : ℕ, ∀ f ∈ irrelevant (baseIdeal surface a h) a h ^ N,
      (∃ m : ℕ, shift (baseIdeal surface a h) a h ^ m * f ∈ homCutIdeal surface a h) →
      f ∈ homCutIdeal surface a h :=
  @exists_pow_saturation_le (Rees surface a h) (latticeIndices a × latticeIndices h)
    inferInstance hNoeth (pairGen (baseIdeal surface a h) a h)
    (homCutIdeal surface a h) (shift (baseIdeal surface a h) a h) hchart

private theorem ker_le_image_sum (surface : Ideal GeoJets) (a h : Shape) (ha : FullChamber a)
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
end PackSource_K1_13_6_1_4_2_1_2Split

section PackSource_K1_13_7_2_3Defs
set_option autoImplicit true
namespace K1_13_7_2_3

open K1_13_6

/-- A curve obtained by a proper principal cut on a geometric surface. -/
structure ProperComponent (surface : Ideal GeoJets) (P : GeoJets) (C : Ideal GeoJets) : Prop where
  prime : surface.IsPrime
  height : surface.height = 2
  proper : P ∉ surface
  component : (surface ⊔ Ideal.span {P}).IsMinimalPrime C

end K1_13_7_2_3
end PackSource_K1_13_7_2_3Defs
