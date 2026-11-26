import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

set_option Elab.async false
set_option maxHeartbeats 800000

/-!
# Exact weighted Sylvester resultant order bounds (`res_ord_exact` and `res_ord_weighted`)

Proves the universal Sylvester determinant valuation lower bound over any commutative ring `R`
(applied to `R = K[s]` at `s = 0`) using only the Leibniz expansion of `Polynomial.sylvester`:

If `f(s, V) = ∑_{i=0}^{d_f} a_i(s) V^i` satisfies `s^{max(0, m_f - w·i)} ∣ a_i(s)` and
`g(s, V) = ∑_{j=0}^{d_g} b_j(s) V^j` satisfies `s^{max(0, m_g - w·j)} ∣ b_j(s)`, then
`s^{resOrdWeighted d_f m_f d_g m_g w} ∣ Polynomial.resultant f g d_f d_g`.

Zero Puiseux series or Newton polygons required!
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6401ResultantOrd

open Polynomial Matrix
open scoped BigOperators

/-- Step gain `max(0, m - w·i) - max(0, m - w·(i + 1))` in `ℕ`. -/
def stepGain (m w i : ℕ) : ℕ :=
  (m - w * i) - (m - w * (i + 1))

lemma stepGain_sum (m w k : ℕ) :
    ∑ i ∈ Finset.range k, stepGain m w i = m - (m - w * k) := by
  induction k with
  | zero => simp [stepGain]
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      unfold stepGain
      have h1 : m - w * (k + 1) ≤ m - w * k := Nat.sub_le_sub_left (Nat.mul_le_mul_left w (Nat.le_succ k)) m
      have h2 : m - w * k ≤ m := Nat.sub_le m (w * k)
      omega

lemma max_sub_eq_sub_sum_stepGain (m w k : ℕ) :
    m - w * k + ∑ i ∈ Finset.range k, stepGain m w i = m := by
  rw [stepGain_sum]
  have : m - w * k ≤ m := Nat.sub_le m (w * k)
  omega

/-- List of all `2 * d_f * d_g` gains sorted in descending order. -/
def allGainsSorted (df mf dg mg w : ℕ) : List ℕ :=
  let gf : List ℕ := (List.range df).flatMap fun i => List.replicate dg (stepGain mf w i)
  let gg : List ℕ := (List.range dg).flatMap fun j => List.replicate df (stepGain mg w j)
  (gf ++ gg).mergeSort (· ≥ ·)

/-- Exact weighted resultant order lower bound `d_g·m_f + d_f·m_g - sum(top d_f·d_g gains)`. -/
def resOrdWeighted (df mf dg mg w : ℕ) : ℕ :=
  if df = 0 then dg * mf
  else if dg = 0 then df * mg
  else dg * mf + df * mg - ((allGainsSorted df mf dg mg w).take (df * dg)).sum

/-- Exact unweighted (`w = 1`) resultant order lower bound in closed form.
Note: add `(df - mf) * (dg - mg)` BEFORE subtracting `df * dg` so `ℕ` subtraction never truncates! -/
def resOrdExact (df mf dg mg : ℕ) : ℕ :=
  if df = 0 then dg * mf
  else if dg = 0 then df * mg
  else dg * mf + df * mg + (df - mf) * (dg - mg) - df * dg

private lemma list_flatMap_sublist {α β : Type*} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, (f x).Sublist (g x)) : (l.flatMap f).Sublist (l.flatMap g) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      exact (h x (by simp)).append (ih fun y hy => h y (by simp [hy]))

private lemma list_sum_map_range (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
      simp

private lemma list_sum_flatMap {α : Type*} (l : List α) (f : α → List ℕ) :
    (l.flatMap f).sum = (l.map fun x => (f x).sum).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp [List.flatMap_cons, List.sum_append, ih]

/-- The sum of any `k`-element sub-multiset of `l` is at most the sum of the top `k` elements of
`l.mergeSort (· ≥ ·)`. -/
lemma sum_sublist_le_sum_take_sorted {s l : List ℕ} (hsub : s.Sublist l) :
    s.sum ≤ ((l.mergeSort (· ≥ ·)).take s.length).sum := by
  have hperm : (l.mergeSort (· ≥ ·)).Perm l := List.mergeSort_perm l (· ≥ ·)
  have hsorted : (l.mergeSort (· ≥ ·)).Pairwise (· ≥ ·) :=
    List.pairwise_mergeSort' (· ≥ ·) l
  have haux : ∀ (L : List ℕ), L.Pairwise (· ≥ ·) →
      ∀ (S : Multiset ℕ), S ≤ (L : Multiset ℕ) → S.sum ≤ (L.take (Multiset.card S)).sum := by
    intro L hL
    induction L with
    | nil =>
        intro S hS
        have : S = 0 := Multiset.le_zero.mp hS
        simp [this]
    | cons a t ih =>
        intro S hS
        have ht : t.Pairwise (· ≥ ·) := (List.pairwise_cons.mp hL).2
        have ha : ∀ x ∈ t, a ≥ x := (List.pairwise_cons.mp hL).1
        by_cases hS0 : S = 0
        · simp [hS0]
        · by_cases haS : a ∈ S
          · obtain ⟨S', rfl⟩ := Multiset.exists_cons_of_mem haS
            have hS'le : S' ≤ (t : Multiset ℕ) := by
              rw [← Multiset.cons_le_cons_iff a]
              exact hS
            have hcard : Multiset.card (a ::ₘ S') = Multiset.card S' + 1 := Multiset.card_cons a S'
            rw [hcard, List.take_succ_cons, List.sum_cons, Multiset.sum_cons]
            exact Nat.add_le_add_left (ih ht S' hS'le) a
          · obtain ⟨b, hb⟩ := Multiset.exists_mem_of_ne_zero hS0
            obtain ⟨S', rfl⟩ := Multiset.exists_cons_of_mem hb
            have hSle_t : b ::ₘ S' ≤ (t : Multiset ℕ) := by
              have hle : ∀ x, Multiset.count x (b ::ₘ S') ≤ Multiset.count x (t : Multiset ℕ) := by
                intro x
                have hcx := Multiset.le_iff_count.mp hS x
                change Multiset.count x (b ::ₘ S') ≤ Multiset.count x (a ::ₘ (t : Multiset ℕ)) at hcx
                by_cases hxa : x = a
                · subst hxa
                  have h0 : Multiset.count x (b ::ₘ S') = 0 := Multiset.count_eq_zero.mpr haS
                  omega
                · rw [Multiset.count_cons_of_ne hxa] at hcx
                  exact hcx
              exact Multiset.le_iff_count.mpr hle
            have hS'le_t : S' ≤ (t : Multiset ℕ) := (Multiset.le_cons_self S' b).trans hSle_t
            have hb_mem_t : b ∈ t := by
              have : b ∈ (t : Multiset ℕ) := Multiset.mem_of_le hSle_t (Multiset.mem_cons_self b S')
              simpa using this
            have hba : b ≤ a := ha b hb_mem_t
            have hcard : Multiset.card (b ::ₘ S') = Multiset.card S' + 1 := Multiset.card_cons b S'
            rw [hcard, List.take_succ_cons, List.sum_cons, Multiset.sum_cons]
            exact Nat.add_le_add hba (ih ht S' hS'le_t)
  have hle : (s : Multiset ℕ) ≤ ((l.mergeSort (· ≥ ·)) : Multiset ℕ) := by
    rw [Multiset.coe_eq_coe.mpr hperm]
    exact Multiset.coe_le.mpr hsub.subperm
  simpa using haux (l.mergeSort (· ≥ ·)) hsorted (s : Multiset ℕ) hle

/-- Every valid Sylvester permutation tuple `(i_r, j_{r'})` with `0 ≤ i_r ≤ d_f`, `0 ≤ j_{r'} ≤ d_g`,
and `∑ i_r + ∑ j_{r'} = d_f · d_g` satisfies
`∑ (m_f - w·i_r) + ∑ (m_g - w·j_{r'}) ≥ resOrdWeighted d_f m_f d_g m_g w`. -/
theorem sylvester_tuple_val_ge (df mf dg mg w : ℕ)
    (ir : Fin dg → ℕ) (jr : Fin df → ℕ)
    (hi : ∀ r, ir r ≤ df) (hj : ∀ r', jr r' ≤ dg)
    (hsum : (∑ r : Fin dg, ir r) + (∑ r' : Fin df, jr r') = df * dg) :
    resOrdWeighted df mf dg mg w ≤
      (∑ r : Fin dg, (mf - w * ir r)) + (∑ r' : Fin df, (mg - w * jr r')) := by
  by_cases hdf : df = 0
  · subst hdf
    simp only [resOrdWeighted, ↓reduceIte, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    have hi0 : ∀ r : Fin dg, ir r = 0 := fun r => Nat.eq_zero_of_le_zero (hi r)
    simp [hi0]
  by_cases hdg : dg = 0
  · subst hdg
    simp only [resOrdWeighted, hdf, ↓reduceIte, Finset.univ_eq_empty, Finset.sum_empty, zero_add]
    have hj0 : ∀ r' : Fin df, jr r' = 0 := fun r' => Nat.eq_zero_of_le_zero (hj r')
    simp [hj0]
  unfold resOrdWeighted
  simp only [hdf, hdg, ↓reduceIte]
  have hEqF : (∑ r : Fin dg, (mf - w * ir r)) +
      (∑ r : Fin dg, ∑ u ∈ Finset.range (ir r), stepGain mf w u) = dg * mf := by
    rw [← Finset.sum_add_distrib]
    simp_rw [max_sub_eq_sub_sum_stepGain]
    simp
  have hEqG : (∑ r' : Fin df, (mg - w * jr r')) +
      (∑ r' : Fin df, ∑ v ∈ Finset.range (jr r'), stepGain mg w v) = df * mg := by
    rw [← Finset.sum_add_distrib]
    simp_rw [max_sub_eq_sub_sum_stepGain]
    simp
  let sF : List ℕ := (List.range df).flatMap fun u =>
    List.replicate ((Finset.univ.filter fun r : Fin dg => u < ir r).card) (stepGain mf w u)
  let sG : List ℕ := (List.range dg).flatMap fun v =>
    List.replicate ((Finset.univ.filter fun r' : Fin df => v < jr r').card) (stepGain mg w v)
  let gF : List ℕ := (List.range df).flatMap fun u => List.replicate dg (stepGain mf w u)
  let gG : List ℕ := (List.range dg).flatMap fun v => List.replicate df (stepGain mg w v)
  have hsubF : sF.Sublist gF := list_flatMap_sublist fun u _ =>
    (List.replicate_sublist_replicate _).mpr (by
      have := Finset.card_le_univ (Finset.univ.filter fun r : Fin dg => u < ir r)
      simpa using this)
  have hsubG : sG.Sublist gG := list_flatMap_sublist fun v _ =>
    (List.replicate_sublist_replicate _).mpr (by
      have := Finset.card_le_univ (Finset.univ.filter fun r' : Fin df => v < jr r')
      simpa using this)
  have hsub : (sF ++ sG).Sublist (gF ++ gG) := hsubF.append hsubG
  have hlenF : sF.length = ∑ r : Fin dg, ir r := by
    have h1 : sF.length = ∑ u ∈ Finset.range df, (Finset.univ.filter fun r : Fin dg => u < ir r).card := by
      simp only [sF, List.length_flatMap, List.length_replicate]
      exact list_sum_map_range df _
    rw [h1]
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    have : (∑ u ∈ Finset.range df, if u < ir r then 1 else 0) = (Finset.range (ir r)).card := by
      rw [← Finset.card_filter]
      congr 1
      ext u
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · intro h; exact h.2
      · intro h; exact ⟨lt_of_lt_of_le h (hi r), h⟩
    rw [this, Finset.card_range]
  have hlenG : sG.length = ∑ r' : Fin df, jr r' := by
    have h1 : sG.length = ∑ v ∈ Finset.range dg, (Finset.univ.filter fun r' : Fin df => v < jr r').card := by
      simp only [sG, List.length_flatMap, List.length_replicate]
      exact list_sum_map_range dg _
    rw [h1]
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r' _
    have : (∑ v ∈ Finset.range dg, if v < jr r' then 1 else 0) = (Finset.range (jr r')).card := by
      rw [← Finset.card_filter]
      congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · intro h; exact h.2
      · intro h; exact ⟨lt_of_lt_of_le h (hj r'), h⟩
    rw [this, Finset.card_range]
  have hsumF : sF.sum = ∑ r : Fin dg, ∑ u ∈ Finset.range (ir r), stepGain mf w u := by
    have h1 : sF.sum = ∑ u ∈ Finset.range df,
        (Finset.univ.filter fun r : Fin dg => u < ir r).card * stepGain mf w u := by
      rw [show sF.sum = ((List.range df).map fun u =>
            (List.replicate ((Finset.univ.filter fun r : Fin dg => u < ir r).card) (stepGain mf w u)).sum).sum from
          list_sum_flatMap _ _]
      simp only [List.sum_replicate, smul_eq_mul]
      exact list_sum_map_range df _
    rw [h1]
    have h2 : ∀ u, (Finset.univ.filter fun r : Fin dg => u < ir r).card * stepGain mf w u =
        ∑ r : Fin dg, if u < ir r then stepGain mf w u else 0 := by
      intro u
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    simp_rw [h2]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [← Finset.sum_filter]
    congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le h (hi r), h⟩⟩
  have hsumG : sG.sum = ∑ r' : Fin df, ∑ v ∈ Finset.range (jr r'), stepGain mg w v := by
    have h1 : sG.sum = ∑ v ∈ Finset.range dg,
        (Finset.univ.filter fun r' : Fin df => v < jr r').card * stepGain mg w v := by
      rw [show sG.sum = ((List.range dg).map fun v =>
            (List.replicate ((Finset.univ.filter fun r' : Fin df => v < jr r').card) (stepGain mg w v)).sum).sum from
          list_sum_flatMap _ _]
      simp only [List.sum_replicate, smul_eq_mul]
      exact list_sum_map_range dg _
    rw [h1]
    have h2 : ∀ v, (Finset.univ.filter fun r' : Fin df => v < jr r').card * stepGain mg w v =
        ∑ r' : Fin df, if v < jr r' then stepGain mg w v else 0 := by
      intro v
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    simp_rw [h2]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r' _
    rw [← Finset.sum_filter]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le h (hj r'), h⟩⟩
  have hbound := sum_sublist_le_sum_take_sorted hsub
  rw [List.length_append, hlenF, hlenG, hsum, List.sum_append, hsumF, hsumG] at hbound
  change (∑ r : Fin dg, ∑ u ∈ Finset.range (ir r), stepGain mf w u) +
      (∑ r' : Fin df, ∑ v ∈ Finset.range (jr r'), stepGain mg w v) ≤
      ((allGainsSorted df mf dg mg w).take (df * dg)).sum at hbound
  omega

/-- **Main Sylvester Resultant Valuation Theorem (over any commutative ring `R` and any `t ∈ R`):**
If `f, g ∈ R[V]` satisfy `t^{m_f - w·i} ∣ f.coeff i` and `t^{m_g - w·j} ∣ g.coeff j`, then
`t^{resOrdWeighted d_f m_f d_g m_g w} ∣ Polynomial.resultant f g d_f d_g`! -/
theorem pow_dvd_resultant_of_weighted_ord {R : Type*} [CommRing R] (t : R)
    (f g : R[X]) (df mf dg mg w : ℕ)
    (hfd : f.natDegree ≤ df) (hgd : g.natDegree ≤ dg)
    (hf : ∀ i, t ^ (mf - w * i) ∣ f.coeff i)
    (hg : ∀ j, t ^ (mg - w * j) ∣ g.coeff j) :
    t ^ resOrdWeighted df mf dg mg w ∣ Polynomial.resultant f g df dg := by
  classical
  rw [Polynomial.resultant, Matrix.det_apply]
  apply Finset.dvd_sum
  intro σ _
  rw [Units.smul_def, zsmul_eq_mul]
  apply dvd_mul_of_dvd_right
  by_cases hzero : ∃ j : Fin (df + dg), Polynomial.sylvester f g df dg (σ j) j = 0
  · obtain ⟨j, hj⟩ := hzero
    have h0 : (∏ i : Fin (df + dg), Polynomial.sylvester f g df dg (σ i) i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) hj
    rw [h0]
    exact dvd_zero _
  · push Not at hzero
    let jr : Fin df → ℕ := fun r' => (σ (Fin.castAdd dg r')).val - r'.val
    let ir : Fin dg → ℕ := fun r => (σ (Fin.natAdd df r)).val - r.val
    have hbounds :
      (∀ r' : Fin df, r'.val ≤ (σ (Fin.castAdd dg r')).val ∧
        (σ (Fin.castAdd dg r')).val ≤ r'.val + dg ∧
        Polynomial.sylvester f g df dg (σ (Fin.castAdd dg r')) (Fin.castAdd dg r') = g.coeff (jr r')) ∧
      (∀ r : Fin dg, r.val ≤ (σ (Fin.natAdd df r)).val ∧
        (σ (Fin.natAdd df r)).val ≤ r.val + df ∧
        Polynomial.sylvester f g df dg (σ (Fin.natAdd df r)) (Fin.natAdd df r) = f.coeff (ir r)) := by
      constructor
      · intro r'
        have hne := hzero (Fin.castAdd dg r')
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Set.mem_Icc] at hne ⊢
        split_ifs at hne ⊢ with hc
        · exact ⟨hc.1, hc.2, rfl⟩
        · exact absurd rfl hne
      · intro r
        have hne := hzero (Fin.natAdd df r)
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, Set.mem_Icc] at hne ⊢
        split_ifs at hne ⊢ with hc
        · exact ⟨hc.1, hc.2, rfl⟩
        · exact absurd rfl hne
    have hi : ∀ r, ir r ≤ df := fun r => by
      have h1 := (hbounds.2 r).1; have h2 := (hbounds.2 r).2.1; dsimp [ir]; omega
    have hj : ∀ r', jr r' ≤ dg := fun r' => by
      have h1 := (hbounds.1 r').1; have h2 := (hbounds.1 r').2.1; dsimp [jr]; omega
    have hsum : (∑ r : Fin dg, ir r) + (∑ r' : Fin df, jr r') = df * dg := by
      have hperm_sum : ∑ k : Fin (df + dg), (σ k).val = ∑ k : Fin (df + dg), k.val :=
        Equiv.sum_comp σ (fun k : Fin (df + dg) => k.val)
      have hsplit_σ : ∑ k : Fin (df + dg), (σ k).val =
          (∑ r' : Fin df, (σ (Fin.castAdd dg r')).val) +
          (∑ r : Fin dg, (σ (Fin.natAdd df r)).val) := Fin.sum_univ_add _
      have hsplit_id : ∑ k : Fin (df + dg), k.val =
          (∑ r' : Fin df, r'.val) + (∑ r : Fin dg, (df + r.val)) := by
        rw [Fin.sum_univ_add]; rfl
      have hG : (∑ r' : Fin df, jr r') + (∑ r' : Fin df, r'.val) =
          ∑ r' : Fin df, (σ (Fin.castAdd dg r')).val := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro r' _
        have h1 := (hbounds.1 r').1; dsimp [jr]; omega
      have hF : (∑ r : Fin dg, ir r) + (∑ r : Fin dg, r.val) =
          ∑ r : Fin dg, (σ (Fin.natAdd df r)).val := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro r _
        have h1 := (hbounds.2 r).1; dsimp [ir]; omega
      have hadd_id : ∑ r : Fin dg, (df + r.val) = dg * df + ∑ r : Fin dg, r.val := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      have hcomm : dg * df = df * dg := mul_comm dg df
      omega
    have hdvd_prod : t ^ ((∑ r : Fin dg, (mf - w * ir r)) + (∑ r' : Fin df, (mg - w * jr r'))) ∣
        ∏ j : Fin (df + dg), Polynomial.sylvester f g df dg (σ j) j := by
      rw [Fin.prod_univ_add, add_comm, pow_add, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum]
      apply mul_dvd_mul
      · apply Finset.prod_dvd_prod_of_dvd
        intro r' _
        simpa [(hbounds.1 r').2.2] using hg (jr r')
      · apply Finset.prod_dvd_prod_of_dvd
        intro r _
        simpa [(hbounds.2 r).2.2] using hf (ir r)
    exact (pow_dvd_pow t (sylvester_tuple_val_ge df mf dg mg w ir jr hi hj hsum)).trans hdvd_prod

/-- **Exact unweighted (`w = 1`) Sylvester Resultant Valuation Theorem (with `+(df - mf)*(dg - mg)`!):**
If `t^{mf - i} ∣ f.coeff i` and `t^{mg - j} ∣ g.coeff j`, then
`t^{resOrdExact df mf dg mg} ∣ Polynomial.resultant f g df dg`!
Uses the exact Sylvester permutation identity `(k - a)^2 + a*b ≥ a*b` on the top `a + b` rows! -/
theorem pow_dvd_resultant_exact {R : Type*} [CommRing R] (t : R)
    (f g : R[X]) (df mf dg mg : ℕ)
    (hfd : f.natDegree ≤ df) (hgd : g.natDegree ≤ dg)
    (hf : ∀ i, t ^ (mf - i) ∣ f.coeff i)
    (hg : ∀ j, t ^ (mg - j) ∣ g.coeff j) :
    t ^ resOrdExact df mf dg mg ∣ Polynomial.resultant f g df dg := by
  classical
  rw [Polynomial.resultant, Matrix.det_apply]
  apply Finset.dvd_sum
  intro σ _
  rw [Units.smul_def, zsmul_eq_mul]
  apply dvd_mul_of_dvd_right
  by_cases hzero : ∃ j : Fin (df + dg), Polynomial.sylvester f g df dg (σ j) j = 0
  · obtain ⟨j, hj⟩ := hzero
    have h0 : (∏ i : Fin (df + dg), Polynomial.sylvester f g df dg (σ i) i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) hj
    rw [h0]
    exact dvd_zero _
  · push Not at hzero
    let jr : Fin df → ℕ := fun r' => (σ (Fin.castAdd dg r')).val - r'.val
    let ir : Fin dg → ℕ := fun r => (σ (Fin.natAdd df r)).val - r.val
    have hbounds :
      (∀ r' : Fin df, r'.val ≤ (σ (Fin.castAdd dg r')).val ∧
        (σ (Fin.castAdd dg r')).val ≤ r'.val + dg ∧
        Polynomial.sylvester f g df dg (σ (Fin.castAdd dg r')) (Fin.castAdd dg r') = g.coeff (jr r')) ∧
      (∀ r : Fin dg, r.val ≤ (σ (Fin.natAdd df r)).val ∧
        (σ (Fin.natAdd df r)).val ≤ r.val + df ∧
        Polynomial.sylvester f g df dg (σ (Fin.natAdd df r)) (Fin.natAdd df r) = f.coeff (ir r)) := by
      constructor
      · intro r'
        have hne := hzero (Fin.castAdd dg r')
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Set.mem_Icc] at hne ⊢
        split_ifs at hne ⊢ with hc
        · exact ⟨hc.1, hc.2, rfl⟩
        · exact absurd rfl hne
      · intro r
        have hne := hzero (Fin.natAdd df r)
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, Set.mem_Icc] at hne ⊢
        split_ifs at hne ⊢ with hc
        · exact ⟨hc.1, hc.2, rfl⟩
        · exact absurd rfl hne
    have hsum : (∑ r : Fin dg, ir r) + (∑ r' : Fin df, jr r') = df * dg := by
      have hperm_sum : ∑ k : Fin (df + dg), (σ k).val = ∑ k : Fin (df + dg), k.val :=
        Equiv.sum_comp σ (fun k : Fin (df + dg) => k.val)
      have hsplit_σ : ∑ k : Fin (df + dg), (σ k).val =
          (∑ r' : Fin df, (σ (Fin.castAdd dg r')).val) +
          (∑ r : Fin dg, (σ (Fin.natAdd df r)).val) := Fin.sum_univ_add _
      have hsplit_id : ∑ k : Fin (df + dg), k.val =
          (∑ r' : Fin df, r'.val) + (∑ r : Fin dg, (df + r.val)) := by
        rw [Fin.sum_univ_add]; rfl
      have hG : (∑ r' : Fin df, jr r') + (∑ r' : Fin df, r'.val) =
          ∑ r' : Fin df, (σ (Fin.castAdd dg r')).val := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro r' _
        have h1 := (hbounds.1 r').1; dsimp [jr]; omega
      have hF : (∑ r : Fin dg, ir r) + (∑ r : Fin dg, r.val) =
          ∑ r : Fin dg, (σ (Fin.natAdd df r)).val := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro r _
        have h1 := (hbounds.2 r).1; dsimp [ir]; omega
      have hadd_id : ∑ r : Fin dg, (df + r.val) = dg * df + ∑ r : Fin dg, r.val := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      have hcomm : dg * df = df * dg := mul_comm dg df
      omega
    have hdvd_prod : t ^ ((∑ r : Fin dg, (mf - ir r)) + (∑ r' : Fin df, (mg - jr r'))) ∣
        ∏ j : Fin (df + dg), Polynomial.sylvester f g df dg (σ j) j := by
      rw [Fin.prod_univ_add, add_comm, pow_add, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum]
      apply mul_dvd_mul
      · apply Finset.prod_dvd_prod_of_dvd; intro r' _
        simpa [(hbounds.1 r').2.2] using hg (jr r')
      · apply Finset.prod_dvd_prod_of_dvd; intro r _
        simpa [(hbounds.2 r).2.2] using hf (ir r)
    have hexp : resOrdExact df mf dg mg ≤ (∑ r : Fin dg, (mf - ir r)) + (∑ r' : Fin df, (mg - jr r')) := by
      by_cases hdf : df = 0
      · subst hdf; simp only [resOrdExact, ↓reduceIte, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
        have hi0 : ∀ r : Fin dg, ir r = 0 := fun r => by
          have h1 := (hbounds.2 r).1; have h2 := (hbounds.2 r).2.1; dsimp [ir]; omega
        simp [hi0]
      by_cases hdg : dg = 0
      · subst hdg; simp only [resOrdExact, hdf, ↓reduceIte, Finset.univ_eq_empty, Finset.sum_empty, zero_add]
        have hj0 : ∀ r' : Fin df, jr r' = 0 := fun r' => by
          have h1 := (hbounds.1 r').1
          have h2 := (hbounds.1 r').2.1
          change (σ (Fin.castAdd 0 r')).val - r'.val = 0
          omega
        simp [hj0]
      unfold resOrdExact; simp only [hdf, hdg, ↓reduceIte]
      have hZ_split : ((∑ r : Fin dg, (mf - ir r)) + (∑ r' : Fin df, (mg - jr r')) : ℤ) =
          (dg * mf + df * mg - df * dg : ℤ) +
          ((∑ r : Fin dg, (ir r - mf)) + (∑ r' : Fin df, (jr r' - mg)) : ℤ) := by
        have hF : (∑ r : Fin dg, ((mf - ir r : ℕ) : ℤ)) - (∑ r : Fin dg, ((ir r - mf : ℕ) : ℤ)) =
            (dg : ℤ) * mf - ∑ r : Fin dg, (ir r : ℤ) := by
          rw [← Finset.sum_sub_distrib]
          have : ∀ r : Fin dg, ((mf - ir r : ℕ) : ℤ) - ((ir r - mf : ℕ) : ℤ) = (mf : ℤ) - ir r := fun r => by omega
          simp_rw [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hG : (∑ r' : Fin df, ((mg - jr r' : ℕ) : ℤ)) - (∑ r' : Fin df, ((jr r' - mg : ℕ) : ℤ)) =
            (df : ℤ) * mg - ∑ r' : Fin df, (jr r' : ℤ) := by
          rw [← Finset.sum_sub_distrib]
          have : ∀ r' : Fin df, ((mg - jr r' : ℕ) : ℤ) - ((jr r' - mg : ℕ) : ℤ) = (mg : ℤ) - jr r' := fun r' => by omega
          simp_rw [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hsumZ : (∑ r : Fin dg, (ir r : ℤ)) + (∑ r' : Fin df, (jr r' : ℤ)) = (df : ℤ) * dg := by
          exact_mod_cast hsum
        push_cast at hF hG ⊢; linarith only [hF, hG, hsumZ]
      by_cases hsmall : mf < df ∧ mg < dg
      · rcases hsmall with ⟨hmf, hmg⟩
        let a := df - mf
        let b := dg - mg
        let Aset := Finset.univ.filter fun r' : Fin df => mf + mg ≤ (σ (Fin.castAdd dg r')).val
        let Bset := Finset.univ.filter fun r : Fin dg => mf + mg ≤ (σ (Fin.natAdd df r)).val
        let Top := Finset.univ.filter fun i : Fin (df + dg) => mf + mg ≤ i.val
        have hcard_top : Top.card = a + b := by
          have : Top = (Finset.Ico (mf + mg) (df + dg)).attach.image (fun x => ⟨x.1, (Finset.mem_Ico.mp x.2).2⟩) := by
            ext i; simp only [Top, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
              Finset.mem_attach, true_and, Subtype.exists, Finset.mem_Ico]
            constructor
            · intro h; exact ⟨i.val, ⟨h, i.isLt⟩, rfl⟩
            · rintro ⟨v, ⟨hv, _⟩, rfl⟩; exact hv
          rw [this, Finset.card_image_of_injective _ (fun x y h => Subtype.ext (congrArg Fin.val h)),
            Finset.card_attach, Nat.card_Ico]; omega
        have hsum_top : 2 * (∑ i ∈ Top, i.val) = (a + b) * (2 * (mf + mg) + (a + b) - 1) := by
          have hbij : ∑ i ∈ Top, i.val = ∑ t ∈ Finset.range (a + b), (mf + mg + t) := by
            refine Finset.sum_bij (fun i _ => i.val - (mf + mg)) ?_ ?_ ?_ ?_
            · intro i hi; rw [Finset.mem_range]; have h1 := (Finset.mem_filter.mp hi).2; dsimp only [a, b]; omega
            · intro i1 hi1 i2 hi2 h; apply Fin.ext
              have h1 := (Finset.mem_filter.mp hi1).2; have h2 := (Finset.mem_filter.mp hi2).2; omega
            · intro t ht; rw [Finset.mem_range] at ht
              refine ⟨⟨mf + mg + t, by dsimp only [a, b] at ht; omega⟩, ?_, by simp⟩
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩
            · intro i hi; have h1 := (Finset.mem_filter.mp hi).2; omega
          rw [hbij, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
          have htri : 2 * ∑ t ∈ Finset.range (a + b), t = (a + b) * (a + b - 1) := by
            have := Finset.sum_range_id_mul_two (a + b); linarith only [this]
          have h1 : 1 ≤ a + b := by dsimp only [a, b]; omega
          have h2 : 1 ≤ 2 * (mf + mg) + (a + b) := by omega
          zify [h1, h2] at htri ⊢
          nlinarith only [htri]
        let Pre := Finset.univ.filter fun j : Fin (df + dg) => mf + mg ≤ (σ j).val
        have hPre_eq : Pre = Aset.image (Fin.castAdd dg) ∪ Bset.image (Fin.natAdd df) := by
          ext j; induction j using Fin.addCases with
          | left r' =>
              simp only [Pre, Aset, Bset, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
                Finset.mem_univ, true_and]
              constructor
              · intro h; left; exact ⟨r', h, rfl⟩
              · rintro (⟨r'', hr'', heq⟩ | ⟨r, _, heq⟩)
                · have : r'' = r' := Fin.castAdd_injective df dg heq; subst this; exact hr''
                · exfalso; have := congrArg Fin.val heq; simp at this; omega
          | right r =>
              simp only [Pre, Aset, Bset, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
                Finset.mem_univ, true_and]
              constructor
              · intro h; right; exact ⟨r, h, rfl⟩
              · rintro (⟨r', _, heq⟩ | ⟨r'', hr'', heq⟩)
                · exfalso; have := congrArg Fin.val heq; simp at this; omega
                · have : r'' = r := Fin.natAdd_injective dg df heq; subst this; exact hr''
        have hPre_disj : Disjoint (Aset.image (Fin.castAdd dg)) (Bset.image (Fin.natAdd df)) := by
          rw [Finset.disjoint_left]; intro j h1 h2
          rcases Finset.mem_image.mp h1 with ⟨r', _, rfl⟩
          rcases Finset.mem_image.mp h2 with ⟨r, _, heq⟩
          have := congrArg Fin.val heq; simp at this; omega
        have hPre_card : Pre.card = Aset.card + Bset.card := by
          rw [hPre_eq, Finset.card_union_of_disjoint hPre_disj,
            Finset.card_image_of_injective _ (Fin.castAdd_injective df dg),
            Finset.card_image_of_injective _ (Fin.natAdd_injective dg df)]
        have hPre_top : Pre.image σ = Top := by
          ext i; simp only [Pre, Top, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨j, hj, rfl⟩; exact hj
          · intro hi; exact ⟨σ.symm i, by simpa using hi, by simp⟩
        have hkl : Aset.card + Bset.card = a + b := by
          rw [← hPre_card, ← Finset.card_image_of_injective Pre σ.injective, hPre_top, hcard_top]
        have hsum_AB : (∑ r' ∈ Aset, (σ (Fin.castAdd dg r')).val) +
            (∑ r ∈ Bset, (σ (Fin.natAdd df r)).val) = ∑ i ∈ Top, i.val := by
          rw [← hPre_top, Finset.sum_image (fun _ _ _ _ h => σ.injective h), hPre_eq,
            Finset.sum_union hPre_disj,
            Finset.sum_image (fun _ _ _ _ h => Fin.castAdd_injective df dg h),
            Finset.sum_image (fun _ _ _ _ h => Fin.natAdd_injective dg df h)]
        have hsum_sub_max : ∀ (n : ℕ) (S : Finset (Fin n)),
            2 * (∑ x ∈ S, x.val) + S.card * (S.card + 1) ≤ 2 * S.card * n := by
          intro n S
          have hrev : ∑ t ∈ Finset.range S.card, t ≤ ∑ x ∈ S, (n - 1 - x.val) := by
            have hT : (S.image (fun x : Fin n => n - 1 - x.val)).card = S.card :=
              Finset.card_image_of_injective _ (fun x y h => Fin.ext (by omega))
            have hsum_img : ∑ y ∈ S.image (fun x : Fin n => n - 1 - x.val), y = ∑ x ∈ S, (n - 1 - x.val) :=
              Finset.sum_image (fun x _ y _ h => Fin.ext (by omega))
            rw [← hsum_img]
            generalize hU : S.image (fun x : Fin n => n - 1 - x.val) = U
            rw [hU] at hT; rw [← hT]
            clear hT hsum_img hU S n
            induction U using Finset.strongInduction with
            | H U ih =>
                by_cases hU0 : U = ∅
                · subst hU0; simp
                · have hne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hU0
                  let m := U.max' hne
                  have hm : m ∈ U := Finset.max'_mem U hne
                  let U' := U.erase m
                  have hsub : U' ⊂ U := Finset.erase_ssubset hm
                  have hcard : U.card = U'.card + 1 := (Finset.card_erase_add_one hm).symm
                  have hge : U'.card ≤ m := by
                    have hsub_range : U' ⊆ Finset.range m := by
                      intro x hx
                      rw [Finset.mem_range]
                      have hxU : x ∈ U := Finset.mem_of_mem_erase hx
                      have hne' : x ≠ m := (Finset.mem_erase.mp hx).1
                      exact lt_of_le_of_ne (Finset.le_max' U x hxU) hne'
                    exact (Finset.card_le_card hsub_range).trans (by simp)
                  rw [hcard, Finset.sum_range_succ, ← Finset.add_sum_erase U (fun y => y) hm]
                  have := ih U' hsub
                  dsimp only [U', m] at this hge ⊢; omega
          have htri : 2 * ∑ t ∈ Finset.range S.card, t = S.card * (S.card - 1) := by
            have := Finset.sum_range_id_mul_two S.card; linarith only [this]
          have hadd : (∑ x ∈ S, x.val) + (∑ x ∈ S, (n - 1 - x.val)) = S.card * (n - 1) := by
            rw [← Finset.sum_add_distrib]
            have : ∀ x ∈ S, x.val + (n - 1 - x.val) = n - 1 := fun x _ => by omega
            rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]
          by_cases hS0 : S.card = 0
          · have hSe : S = ∅ := Finset.card_eq_zero.mp hS0; subst hSe; simp
          · have hn1 : 1 ≤ n := by
              obtain ⟨x, _⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hS0)
              have hx := x.isLt; omega
            zify [hn1, show 1 ≤ S.card by omega] at hrev htri hadd ⊢
            nlinarith only [hrev, htri, hadd]
        have hA_bound := hsum_sub_max df Aset
        have hB_bound := hsum_sub_max dg Bset
        have hge_AB : (∑ r ∈ Bset, ((ir r : ℤ) - mf)) + (∑ r' ∈ Aset, ((jr r' : ℤ) - mg)) ≤
            ((∑ r : Fin dg, (ir r - mf)) + (∑ r' : Fin df, (jr r' - mg)) : ℤ) := by
          have h1 : ∑ r ∈ Bset, ((ir r : ℤ) - mf) ≤ ∑ r : Fin dg, ((ir r - mf : ℕ) : ℤ) := by
            refine (Finset.sum_le_sum fun r _ => (by omega : ((ir r : ℤ) - mf) ≤ ((ir r - mf : ℕ) : ℤ))).trans ?_
            exact Finset.sum_le_univ_sum_of_nonneg fun r => Nat.cast_nonneg _
          have h2 : ∑ r' ∈ Aset, ((jr r' : ℤ) - mg) ≤ ∑ r' : Fin df, ((jr r' - mg : ℕ) : ℤ) := by
            refine (Finset.sum_le_sum fun r' _ => (by omega : ((jr r' : ℤ) - mg) ≤ ((jr r' - mg : ℕ) : ℤ))).trans ?_
            exact Finset.sum_le_univ_sum_of_nonneg fun r' => Nat.cast_nonneg _
          push_cast; linarith only [h1, h2]
        have hAB_val : (∑ r ∈ Bset, ((ir r : ℤ) - mf)) + (∑ r' ∈ Aset, ((jr r' : ℤ) - mg)) =
            (∑ i ∈ Top, (i.val : ℤ)) - (∑ r ∈ Bset, (r.val : ℤ)) - (∑ r' ∈ Aset, (r'.val : ℤ)) -
            (Bset.card : ℤ) * mf - (Aset.card : ℤ) * mg := by
          have h1 : ∑ r ∈ Bset, ((ir r : ℤ) - mf) =
              (∑ r ∈ Bset, ((σ (Fin.natAdd df r)).val : ℤ)) - (∑ r ∈ Bset, (r.val : ℤ)) - (Bset.card : ℤ) * mf := by
            have : ∀ r ∈ Bset, ((ir r : ℤ) - mf) = ((σ (Fin.natAdd df r)).val : ℤ) - r.val - mf := fun r _ => by
              have h1 := (hbounds.2 r).1; dsimp [ir]; omega
            rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
              Finset.sum_const, nsmul_eq_mul]
          have h2 : ∑ r' ∈ Aset, ((jr r' : ℤ) - mg) =
              (∑ r' ∈ Aset, ((σ (Fin.castAdd dg r')).val : ℤ)) - (∑ r' ∈ Aset, (r'.val : ℤ)) - (Aset.card : ℤ) * mg := by
            have : ∀ r' ∈ Aset, ((jr r' : ℤ) - mg) = ((σ (Fin.castAdd dg r')).val : ℤ) - r'.val - mg := fun r' _ => by
              have h1 := (hbounds.1 r').1; dsimp [jr]; omega
            rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
              Finset.sum_const, nsmul_eq_mul]
          have hsumZ : (∑ r' ∈ Aset, ((σ (Fin.castAdd dg r')).val : ℤ)) +
              (∑ r ∈ Bset, ((σ (Fin.natAdd df r)).val : ℤ)) = ∑ i ∈ Top, (i.val : ℤ) := by
            exact_mod_cast hsum_AB
          linarith only [h1, h2, hsumZ]
        have hexcess : (a : ℤ) * b ≤ ((∑ r : Fin dg, (ir r - mf)) + (∑ r' : Fin df, (jr r' - mg)) : ℤ) := by
          have hsq : (0 : ℤ) ≤ ((Aset.card : ℤ) - a) ^ 2 := sq_nonneg _
          have htopZ : 2 * (∑ i ∈ Top, (i.val : ℤ)) = ((a : ℤ) + b) * (2 * ((mf : ℤ) + mg) + ((a : ℤ) + b) - 1) := by
            have h2 : 1 ≤ 2 * (mf + mg) + (a + b) := by dsimp only [a, b]; omega
            zify [h2] at hsum_top
            push_cast at hsum_top ⊢
            exact hsum_top
          have hAZ : 2 * (∑ r' ∈ Aset, (r'.val : ℤ)) + (Aset.card : ℤ) * ((Aset.card : ℤ) + 1) ≤ 2 * (Aset.card : ℤ) * df := by
            exact_mod_cast hA_bound
          have hBZ : 2 * (∑ r ∈ Bset, (r.val : ℤ)) + (Bset.card : ℤ) * ((Bset.card : ℤ) + 1) ≤ 2 * (Bset.card : ℤ) * dg := by
            exact_mod_cast hB_bound
          have hklZ : (Aset.card : ℤ) + (Bset.card : ℤ) = (a : ℤ) + b := by exact_mod_cast hkl
          have hdfZ : (df : ℤ) = mf + a := by dsimp only [a]; omega
          have hdgZ : (dg : ℤ) = mg + b := by dsimp only [b]; omega
          nlinarith only [hsq, htopZ, hAZ, hBZ, hklZ, hdfZ, hdgZ, hAB_val, hge_AB]
        have hsub_ge : df * dg ≤ dg * mf + df * mg + a * b := by
          have hmf_le : mf ≤ df := le_of_lt hmf
          have hmg_le : mg ≤ dg := le_of_lt hmg
          have hdfZ : (df : ℤ) = mf + a := by dsimp only [a]; omega
          have hdgZ : (dg : ℤ) = mg + b := by dsimp only [b]; omega
          zify
          nlinarith only [hdfZ, hdgZ]
        have hgoalZ : ((dg * mf + df * mg + (df - mf) * (dg - mg) - df * dg : ℕ) : ℤ) ≤
            ((∑ r : Fin dg, (mf - ir r)) + (∑ r' : Fin df, (mg - jr r')) : ℤ) := by
          rw [Nat.cast_sub hsub_ge]
          push_cast at hZ_split hexcess ⊢
          dsimp only [a, b] at hexcess
          linarith only [hZ_split, hexcess]
        exact_mod_cast hgoalZ
      · have hprod0 : (df - mf) * (dg - mg) = 0 := by
          rcases not_and_or.mp hsmall with h1 | h2
          · rw [Nat.sub_eq_zero_of_le (not_lt.mp h1), zero_mul]
          · rw [Nat.sub_eq_zero_of_le (not_lt.mp h2), mul_zero]
        rw [hprod0, add_zero]
        have hnn : (0 : ℤ) ≤ ((∑ r : Fin dg, (ir r - mf)) + (∑ r' : Fin df, (jr r' - mg)) : ℤ) := by positivity
        by_cases hsub : df * dg ≤ dg * mf + df * mg
        · have hgoalZ : ((dg * mf + df * mg - df * dg : ℕ) : ℤ) ≤
              ((∑ r : Fin dg, (mf - ir r)) + (∑ r' : Fin df, (mg - jr r')) : ℤ) := by
            rw [Nat.cast_sub hsub]
            push_cast at hZ_split hnn ⊢
            linarith only [hZ_split, hnn]
          exact_mod_cast hgoalZ
        · rw [Nat.sub_eq_zero_of_le (le_of_not_ge hsub)]; exact Nat.zero_le _
    exact (pow_dvd_pow t hexp).trans hdvd_prod

end B6401ResultantOrd
end ProximityPrize.SubmissionBinaryLower
