import ProximityPrize.SubmissionLower.Z6969Pack0836
import ProximityPrize.SubmissionLower.Z6970H2307AllocWeight
import ProximityPrize.SubmissionLower.R6966ProofLowTierWeight

set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
set_option Elab.async false

namespace Research6969.Low6969RetainedTariffs

open K1_13 (Shape)
open Low6969CubicTariff (fatPrice)

def splitFee (b j b₁ j₁ : ℕ) : ℕ :=
  let b₂ := b - b₁
  let j₂ := j - j₁
  if 0 < b₁ ∧ b₁ < b ∧ 3 ≤ j₁ ∧ j₁ + 3 ≤ j ∧
      j₁ ≤ 3 * b₁ ∧ j₂ ≤ 3 * b₂ then
    fatPrice ⟨b₁, j₁, 1⟩ + fatPrice ⟨b₂, j₂, 1⟩
  else 0

/-- The retained tariff takes the largest fee over the single-factor and two-factor possibilities. -/
def price (x : Shape) : ℕ :=
  if x.t = 0 then 0
  else if x.t = 1 then fatPrice x
  else
    (List.range x.b).foldl
      (fun p b => (List.range x.j).foldl (fun q j => max q (splitFee x.b x.j b j)) p)
      (fatPrice x)

end Research6969.Low6969RetainedTariffs

namespace Research6969.Low6969RetainedTariffs

open Finset
open K1_13 (Shape shape)
open K1_13_8 (Valid zeroShape)
open Low6969CubicTariff (fatPrice)
open scoped BigOperators

private theorem fold_base {α : Type} (f : ℕ → α → ℕ) (increase : ∀ a x, a ≤ f a x)
    (xs : List α) (a : ℕ) : a ≤ xs.foldl f a := by
  induction xs generalizing a with
  | nil => exact le_rfl
  | cons x xs ih => exact (increase a x).trans (ih (f a x))

private theorem fold_at {α : Type} (f : ℕ → α → ℕ) (increase : ∀ a x, a ≤ f a x)
    (xs : List α) {x : α} (mem : x ∈ xs) (d a : ℕ) (step : ∀ k, d ≤ f k x) :
    d ≤ xs.foldl f a := by
  induction xs generalizing a with
  | nil => exact (List.not_mem_nil mem).elim
  | cons u us ih =>
    rcases List.mem_cons.mp mem with h | h
    · subst u
      exact (step a).trans (fold_base f increase us (f a x))
    · exact ih h (f a u)

theorem single_le_price (x : Shape) (hx : 0 < x.t) : fatPrice x ≤ price x := by
  unfold price
  rw [ite_eq_right hx.ne']
  split
  · exact le_rfl
  · exact fold_base _ (fun k b => fold_base _ (fun _ _ => le_max_left _ _) _ k) _ _

theorem pair_le_price (b c j k : ℕ) (hj : 3 ≤ j) (hk : 3 ≤ k)
    (hb : j ≤ 3 * b) (hc : k ≤ 3 * c) :
    fatPrice ⟨b, j, 1⟩ + fatPrice ⟨c, k, 1⟩ ≤ price ⟨b + c, j + k, 2⟩ := by
  unfold price
  simp only [show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ite_false]
  apply fold_at _ (fun a b => fold_base _ (fun _ _ => le_max_left _ _) _ a)
    _ (List.mem_range.mpr (show b < b + c by omega))
  intro a
  apply fold_at _ (fun _ _ => le_max_left _ _) _
    (List.mem_range.mpr (show j < j + k by omega))
  intro v
  apply le_trans _ (le_max_right v (splitFee (b + c) (j + k) b j))
  unfold splitFee
  rw [show b + c - b = c by omega, show j + k - j = k by omega]
  rw [ite_eq_left ⟨by omega, by omega, hj, by omega, hb, hc⟩]

theorem retained_family_fee (n : ℕ) (a : Fin n → Shape) (hv : ∀ i, Valid (a i))
    (hj : (∑ i, (a i).j) ≤ 8) :
    (∑ i, fatPrice (a i)) ≤ price ⟨∑ i, (a i).b, ∑ i, (a i).j, ∑ i, (a i).t⟩ := by
  have hsum : 3 * (∑ i, (a i).t) ≤ ∑ i, (a i).j := by
    rw [Finset.mul_sum]
    exact sum_le_sum fun i _ => (hv i).2.1
  have hn' : n ≤ ∑ i, (a i).t := calc
    n = ∑ _ : Fin n, 1 := by simp
    _ ≤ ∑ i, (a i).t := sum_le_sum fun i _ => (hv i).1
  have hn : n ≤ 2 := by omega
  interval_cases n
  · simp
  · simp only [Fin.sum_univ_one]
    have h : a 0 = ⟨(a 0).b, (a 0).j, (a 0).t⟩ := by cases a 0; rfl
    rw [← h]
    exact single_le_price _ (hv 0).1
  · simp only [Fin.sum_univ_two] at hsum hj ⊢
    have ht0 : (a 0).t = 1 := by have := (hv 0).1; have := (hv 1).1; omega
    have ht1 : (a 1).t = 1 := by have := (hv 0).1; have := (hv 1).1; omega
    have he (i : Fin 2) : a i = ⟨(a i).b, (a i).j, (a i).t⟩ := by cases a i; rfl
    have h0 : a 0 = ⟨(a 0).b, (a 0).j, 1⟩ := (he 0).trans
      (congrArg (fun t => (⟨(a 0).b, (a 0).j, t⟩ : Shape)) ht0)
    have h1 : a 1 = ⟨(a 1).b, (a 1).j, 1⟩ := (he 1).trans
      (congrArg (fun t => (⟨(a 1).b, (a 1).j, t⟩ : Shape)) ht1)
    have hj0 : 3 ≤ (a 0).j := by simpa only [ht0, Nat.mul_one] using (hv 0).2.1
    have hj1 : 3 ≤ (a 1).j := by simpa only [ht1, Nat.mul_one] using (hv 1).2.1
    have bound := pair_le_price _ _ _ _ hj0 hj1 (hv 0).2.2 (hv 1).2.2
    rw [← h0, ← h1] at bound
    rw [ht0, ht1]
    exact bound

end Research6969.Low6969RetainedTariffs

namespace Height2307Bands
open K1_13 (Shape InBox FatEligible)
open K1_13_8 (zeroShape Valid)
open Low6969Prices (fatPrice)
open scoped BigOperators Classical

def Box (r : Shape) : Prop := r.b ≤ 27 ∧ r.j ≤ 8 ∧ (4 ≤ r.j → r.b ≤ 25) ∧ (5 ≤ r.j → r.b ≤ 22) ∧ (6 ≤ r.j → r.b ≤ 19) ∧ (7 ≤ r.j → r.b ≤ 14) ∧ (8 ≤ r.j → r.b ≤ 7)

abbrev Band := Fin 42
abbrev empty : Band := 0

structure BandData where
  lo : ℕ
  hi : ℕ
  index : ℕ
  top : ℕ
  charge : ℕ

private def bands : List BandData := [
  ⟨0,0,0,0,3600⟩,
  ⟨1,1,3,1,2737630379455418⟩,
  ⟨2,2,3,1,2737630379455418⟩,
  ⟨3,3,3,1,2737630379455418⟩,
  ⟨4,4,3,1,3103860754598621⟩,
  ⟨5,5,3,1,3477385021711164⟩,
  ⟨6,6,3,1,3860337975709967⟩,
  ⟨7,7,3,1,4254854411511950⟩,
  ⟨8,8,3,1,4663069124034033⟩,
  ⟨9,9,3,1,5087116908193137⟩,
  ⟨2,2,4,1,5822691297450578⟩,
  ⟨3,3,4,1,5822691297450578⟩,
  ⟨4,4,4,1,5822691297450578⟩,
  ⟨5,13,4,1,14338172199522175⟩,
  ⟨10,20,3,1,11407176608225709⟩,
  ⟨21,27,3,1,17861098478276211⟩,
  ⟨14,25,4,1,29301018719073678⟩,
  ⟨2,9,5,1,18448850903682516⟩,
  ⟨10,16,5,1,30839168593007429⟩,
  ⟨17,22,5,1,42715234372142844⟩,
  ⟨2,19,6,1,51998776885494106⟩,
  ⟨2,4,6,2,53929942490006472⟩,
  ⟨5,7,6,2,72411213246108535⟩,
  ⟨8,10,6,2,99276654671927540⟩,
  ⟨11,12,6,2,117572991129981897⟩,
  ⟨13,14,6,2,136257860337607950⟩,
  ⟨15,16,6,2,155399575732147138⟩,
  ⟨17,18,6,2,175066450750940902⟩,
  ⟨19,19,6,2,185118171068602451⟩,
  ⟨3,14,7,1,52142344636314462⟩,
  ⟨3,5,7,2,99542612326625679⟩,
  ⟨6,8,7,2,127361125601285902⟩,
  ⟨9,10,7,2,154270351410983541⟩,
  ⟨11,11,7,2,167840776968084867⟩,
  ⟨12,12,7,2,181499796532911438⟩,
  ⟨13,13,7,2,195255949285130932⟩,
  ⟨14,14,7,2,209117774404411030⟩,
  ⟨3,6,8,1,43456252904164308⟩,
  ⟨3,3,8,2,161390690580418976⟩,
  ⟨4,6,8,2,161390690580419030⟩,
  ⟨7,7,8,1,43456252904164308⟩,
  ⟨7,7,8,2,167814171473015373⟩]

def band (k : Band) : BandData := bands.get ⟨k.val,k.isLt⟩

def start (k : Band) : Shape := ⟨(band k).lo,(band k).index,(band k).top⟩

def endWidth (k : Band) : ℕ := (band k).hi

def reserve (k : Band) : ℕ := (band k).charge

def Admits (k : Band) (r : Shape) : Prop :=
  (start k).b≤r.b ∧ r.b≤endWidth k ∧ r.j=(start k).j ∧ r.t=(start k).t

instance (k : Band) (r : Shape) : Decidable (Admits k r) := by unfold Admits; infer_instance


theorem empty_admits : Admits empty zeroShape := by decide +kernel

theorem admits_floor {k : Band} {r : Shape} (hr : Admits k r) : InBox (start k) r :=
  ⟨hr.1,hr.2.2.1.symm.le,hr.2.2.2.symm.le⟩

private instance retainedBoxDecidable (x : Shape) : Decidable (Box x) := by
  unfold Box
  infer_instance

private theorem checked_cover (b : Fin 28) :
    ∀ (j : Fin 9) (t : Fin 3), 1≤t.val → 3*t.val≤j.val → j.val≤3*b.val →
      Box ⟨b.val,j.val,t.val⟩ → ∃ k : Band, Admits k ⟨b.val,j.val,t.val⟩ := by
  fin_cases b <;> decide +kernel

theorem choose_band (r : Shape) (v : Valid r) (box : Box r) : ∃ k : Band,Admits k r := by
  rcases r with ⟨b,j,t⟩
  have hb : b<28 := Nat.lt_succ_of_le box.1
  have hj : j<9 := Nat.lt_succ_of_le box.2.1
  have ht : t<3 := by have := v.2.1; change 3*t≤j at this; omega
  exact checked_cover ⟨b,hb⟩ ⟨j,hj⟩ ⟨t,ht⟩ v.1 v.2.1 v.2.2 box

private theorem checked_reserve (k : Band) :
    ∀ b : Fin 28,(start k).b≤b.val → b.val≤endWidth k →
      Research6969.Low6969RetainedTariffs.price ⟨b.val,(start k).j,(start k).t⟩≤reserve k := by
  fin_cases k <;> decide +kernel

theorem admits_fee {k : Band} {r : Shape} (hr : Admits k r) :
    Research6969.Low6969RetainedTariffs.price r≤reserve k := by
  have hm : endWidth k<28 := by fin_cases k <;> decide +kernel
  have eq : r = ⟨r.b,(start k).j,(start k).t⟩ := by
    cases r with
    | mk b j t => exact congrArg₂ (fun a c => (⟨b,a,c⟩ : Shape)) hr.2.2.1 hr.2.2.2
  rw [eq]
  exact checked_reserve k ⟨r.b,hr.2.1.trans_lt hm⟩ hr.1 hr.2.1

abbrev budget : ℕ := 274779381265980820

def factorCap (top : ℕ) : ℕ := budget-Low6969Prices.lowerCap top

def tiered (k : Band) : Bool := k.val == 1 || k.val == 38

def pricingWeight (k : Band) (b j t : ℕ) : ℕ :=
  if k=empty then Low6969AllocWeight.weight b j t else if tiered k then Research6966.LowTierWeight.weight (60-(start k).j) j else j

def pricingDenom (k : Band) : ℕ := if k=empty then 383 else if tiered k then 5*(60-(start k).j) else 60-(start k).j

def allowance (k : Band) (top b j t : ℕ) : ℕ :=
  (factorCap top-reserve k)*pricingWeight k b j t/pricingDenom k

theorem denom_pos (k : Band) : 0<pricingDenom k := by fin_cases k <;> decide +kernel

theorem reserve_fits (top : ℕ) (ht : top≤16) (k : Band) : reserve k≤factorCap top := by
  have hreserve : reserve k ≤ 209117774404411030 := by fin_cases k <;> decide +kernel
  have hcap : 209117774404411030 ≤ factorCap top := by interval_cases top <;> decide +kernel
  exact hreserve.trans hcap

theorem weight_mono (k : Band) {b j t B J T : ℕ} (hb : b≤B) (hj : j≤J) (ht : t≤T) :
    pricingWeight k b j t≤pricingWeight k B J T := by
  by_cases h : k=empty
  · simpa only [pricingWeight,ite_eq_left h] using Low6969AllocWeight.mono hb hj ht
  · by_cases t : tiered k
    · simpa [pricingWeight,h,t] using Research6966.LowTierWeight.mono (60-(start k).j) hj
    · simpa [pricingWeight,h,t] using hj

theorem factorCap_mono {a b : ℕ} (h : a≤b) (hb : b≤16) : factorCap a≤factorCap b := by
  have ha := h.trans hb
  interval_cases a <;> interval_cases b <;> decide +kernel

theorem allowance_mono {a b w j t : ℕ} (k : Band) (h : a≤b) (hb : b≤16) :
    allowance k a w j t≤allowance k b w j t := by
  exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (factorCap_mono h hb) _))

theorem retained_cost {ι : Type*} [DecidableEq ι] {a : ι → Shape} {cost : ι → ℕ}
    {z : Finset ι} {k : Band} (ha : ∀ i, Valid (a i)) (hr : Valid (P3_6_8.shapeSum a z))
    (hbox : Box (P3_6_8.shapeSum a z)) (hk : Admits k (P3_6_8.shapeSum a z))
    (hfat : ∀ i, FatEligible (a i) → cost i ≤ fatPrice (a i)) :
    (∑ i ∈ z, cost i) ≤ reserve k := by
  let r := P3_6_8.shapeSum a z
  let er := z.equivFin.symm
  let ar : Fin z.card → Shape := fun i => a (er i).val
  have sums (g : Shape → ℕ) : (∑ i, g (ar i)) = ∑ i ∈ z, g (a i) := by
    rw [← Finset.sum_attach z (fun i => g (a i))]
    exact Fintype.sum_equiv er _ _ fun _ => rfl
  have hj : (∑ i, (ar i).j) ≤ 8 := by rw [sums]; exact hbox.2.1
  have hp := Research6969.Low6969RetainedTariffs.retained_family_fee z.card ar
    (fun i => ha (er i).val) hj
  rw [sums, sums, sums, sums] at hp
  refine (Finset.sum_le_sum fun i hi => hfat i ?_).trans (hp.trans (admits_fee hk))
  have h := P3_6_8.inBox_shapeSum a hi
  exact ⟨(h.1.trans hbox.1).trans (by decide), (h.2.1.trans hbox.2.1).trans (by decide)⟩

end Height2307Bands
