import ProximityPrize.SubmissionLower.RankRows82190

set_option Elab.async false

namespace Final50RankCore
open K1_13 (Geom)
open K1_13_1_1 (Form bandSpace bandCount backShift targetOrder bandSpace_finite finrank_bandSpace)
open AnchorPivot82180 (encode)
open MvPolynomial
open scoped BigOperators
open RankRows82190 (band_mono)
open AnchorPivot82180 (independent)

abbrev Row := RankRows82190.Row

def orderCutoff (s : ℕ) (g : ℤ) : ℤ := 99 - (s : ℤ) - g

private def accept (s : ℕ) (g : ℤ) (r : Row) : Bool :=
  decide (-g ≤ (r.index : ℤ) ∧ (orderCutoff s g).toNat ≤ r.ord)

noncomputable def blockAt (d s : ℕ) (g : ℤ) : bandSpace d (-g) 55 14 →ₗ[Geom] Form :=
  ((weightedTruncation targetOrder (orderCutoff s g).toNat).comp
    backShift.toLinearMap).domRestrict _

def good (d : ℕ) (r : Row) : Bool :=
  let x := r.bounds
  decide (x.deg = d ∧ r.index ≤ x.lo ∧ x.hi ≤ 55 ∧ x.top ≤ 14 ∧ r.ord ≤ x.ord ∧ x.tag = r.tag)

def gradeFee (s : ℕ) (rows : List Row) : ℕ :=
  (rows.map (fun r => 99 + r.index - (s + r.ord))).sum

def covers (d : ℕ) (rows : List Row) : Prop :=
  ∀ i : Fin 56, bandCount d (i.val : ℤ) 55 14 ≤
    (rows.filter (fun r => decide (i.val ≤ r.index))).length

private theorem row_kernel (d s : ℕ) (g : ℤ) (r : Row) (hv : good d r = true)
    (ha : accept s g r = true) :
    ∃ w : LinearMap.ker (blockAt d s g), ((w.val : Form) = r.form) ∧
      (encode (w.val : Form)).degree = (r.tag : ℕ) := by
  obtain ⟨hd,hl,hh,ht,ho,hk⟩ := of_decide_eq_true hv
  obtain ⟨hl',ho'⟩ := of_decide_eq_true ha
  have hb := r.sound.band
  rw [hd] at hb
  let w : bandSpace d (-g) 55 14 := ⟨r.form,
    band_mono (hl'.trans (Int.ofNat_le.mpr hl)) (by exact_mod_cast hh) ht hb⟩
  have hw : w ∈ LinearMap.ker (blockAt d s g) := by
    apply (weightedTruncation_eq_zero_iff _ _ _).mpr
    exact restrictWeightedOrder_anti _ (ho'.trans ho) r.sound.contact
  exact ⟨⟨w,hw⟩,rfl,r.sound.degree.trans (congrArg (fun n : ℕ => (n : WithBot ℕ)) hk)⟩



theorem count_bound (rows : List Row) (d s : ℕ) (g : ℤ)
    (good : ∀ r ∈ rows, good d r = true)
    (sorted : rows.Pairwise fun a b => a.tag < b.tag) :
    Module.finrank Geom (LinearMap.range (blockAt d s g)) + (rows.filter (accept s g)).length ≤
      bandCount d (-g) 55 14 := by
  classical
  let use := rows.filter (accept s g)
  have memb (i : Fin use.length) : use.get i ∈ rows ∧ accept s g (use.get i) = true :=
    List.mem_filter.mp (List.get_mem use i)
  have hsort : use.Pairwise (fun a b => a.tag < b.tag) := sorted.sublist (List.filter_sublist ..)
  have hmono : StrictMono (fun i : Fin use.length => (use.get i).tag) :=
    fun _ _ h => hsort.rel_get_of_lt h
  have h (i : Fin use.length) := row_kernel d s g (use.get i) (good _ (memb i).1) (memb i).2
  let w (i : Fin use.length) := Classical.choose (h i)
  let embed : LinearMap.ker (blockAt d s g) →ₗ[Geom] Polynomial Geom :=
    encode.toLinearMap.comp ((bandSpace d (-g) 55 14).subtype.comp (LinearMap.ker (blockAt d s g)).subtype)
  have hw := independent embed w _ hmono.injective (fun i => (Classical.choose_spec (h i)).2)
  let : Module.Finite Geom (bandSpace d (-g) 55 14) := bandSpace_finite _ _ _ _
  have hc := hw.fintype_card_le_finrank
  have hd := (blockAt d s g).finrank_range_add_finrank_ker
  rw [finrank_bandSpace] at hd
  simpa only [Fintype.card_fin] using
    ((Nat.add_le_add_left hc (Module.finrank Geom (LinearMap.range (blockAt d s g)))).trans_eq hd)


private def charge (s : ℕ) (g : ℤ) (r : Row) : ℕ :=
  if -g ≤ (r.index : ℤ) ∧ r.ord < (orderCutoff s g).toNat then 1 else 0

private theorem filter_split (s : ℕ) (g : ℤ) (rows : List Row) :
    (rows.filter (fun r => decide (-g ≤ (r.index : ℤ)))).length =
      (rows.filter (accept s g)).length + (rows.map (charge s g)).sum := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    by_cases hi : -g ≤ (r.index : ℤ) <;> by_cases ho : (orderCutoff s g).toNat ≤ r.ord <;>
      simp [hi,ho,accept,charge,lt_iff_not_ge,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private theorem coverage_at {d : ℕ} {rows : List Row} (hc : covers d rows)
    (g : ℤ) (hg : -55 ≤ g) :
    bandCount d (-g) 55 14 ≤ (rows.filter (fun r => decide (-g ≤ (r.index : ℤ)))).length := by
  let i : Fin 56 := ⟨(-g).toNat,by omega⟩
  have hn (c f : ℕ) : max (0 : ℤ) (-g - 2*c - 3*f) =
      max 0 ((i.val : ℤ) - 2*c - 3*f) := by dsimp [i]; omega
  have hh : bandCount d (-g) 55 14 = bandCount d (i.val : ℤ) 55 14 := by
    simp only [bandCount,hn]
  have he (r : Row) : (-g ≤ (r.index : ℤ)) ↔ (i.val ≤ r.index) := by dsimp [i]; omega
  simp_rw [hh,he]
  exact hc i

private theorem charge_offsets (s : ℕ) (r : Row) :
    (∑ i : Fin 154, charge s ((i.val : ℤ) - 55) r) ≤ 99 + r.index - (s + r.ord) := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => charge s ((i : ℤ) - 55) r)]
  unfold charge
  rw [Finset.sum_boole]
  have hs : (Finset.range 154).filter (fun i : ℕ => -((i : ℤ) - 55) ≤ r.index ∧
      r.ord < (orderCutoff s ((i : ℤ) - 55)).toNat) ⊆
      Finset.Ico (55 - r.index) (154 - (s + r.ord)) := by
    intro i hi
    obtain ⟨_,a,b⟩ := Finset.mem_filter.mp hi
    unfold orderCutoff at b
    exact Finset.mem_Ico.mpr ⟨by omega,by omega⟩
  have h := Finset.card_le_card hs
  rw [Nat.card_Ico] at h
  exact h.trans (by omega)

private theorem list_charge_offsets (s : ℕ) (rows : List Row) :
    (∑ i : Fin 154, (rows.map (charge s ((i.val : ℤ) - 55))).sum) ≤ gradeFee s rows := by
  induction rows with
  | nil => simp [gradeFee]
  | cons r rows ih =>
    simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib]
    exact Nat.add_le_add (charge_offsets s r) ih

/-- Sum the individual rank charges once per pivot across all offsets of one grade. -/
theorem grade_bound (s d : ℕ) (rows : List Row) (hg : ∀ r ∈ rows, good d r = true)
    (hs : rows.Pairwise fun a b => a.tag < b.tag) (hc : covers d rows) :
    (∑ i : Fin 154, Module.finrank Geom (LinearMap.range (blockAt d s ((i.val : ℤ) - 55)))) ≤
      gradeFee s rows := by
  apply le_trans (Finset.sum_le_sum (g := fun i : Fin 154 =>
    (rows.map (charge s ((i.val : ℤ) - 55))).sum) ?_) (list_charge_offsets s rows)
  intro i _
  let g := (i.val : ℤ) - 55
  have h := count_bound rows d s g hg hs
  have u := coverage_at hc g (by dsimp [g]; omega)
  rw [filter_split s g rows] at u
  change Module.finrank Geom (LinearMap.range (blockAt d s g)) ≤ (rows.map (charge s g)).sum
  omega

#print axioms grade_bound

end Final50RankCore
