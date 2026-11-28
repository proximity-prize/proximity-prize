import ProximityPrize.SubmissionLower.Pack_K1_14_3_2_7Proof
import ProximityPrize.SubmissionLower.Beyond70Binomial

section RankPartition

open scoped BigOperators

namespace Beyond70RankPartition
open Module

private theorem finrank_iSup_le {F V E : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (P : E → Submodule F V) (T : Finset E) :
    finrank F (↑(⨆ e ∈ T, P e) : Type _) ≤ ∑ e ∈ T, finrank F (P e) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert e T he ih =>
    rw [Finset.iSup_insert, Finset.sum_insert he]
    have h := Submodule.finrank_sup_add_finrank_inf_eq (P e) (⨆ e ∈ T, P e)
    omega

theorem rank_le_partition {F R C E : Type*} [Field F] [Fintype R] [Fintype C] [Fintype E]
    (A : Matrix R C F) (tag : R → E) [DecidableEq E] :
    A.rank ≤ ∑ e : E, (A.submatrix (Subtype.val : {i // tag i = e} → R) id).rank := by
  classical
  let P (e : E) : Submodule F (C → F) :=
    Submodule.span F (Set.range (A.submatrix (Subtype.val : {i // tag i = e} → R) id).row)
  have h : Submodule.span F (Set.range A.row) = ⨆ e ∈ (Finset.univ : Finset E), P e := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      apply (le_iSup₂ (f := fun e (_ : e ∈ (Finset.univ : Finset E)) => P e)
        (tag i) (Finset.mem_univ _))
      apply Submodule.subset_span
      exact ⟨⟨i,rfl⟩,rfl⟩
    · refine iSup₂_le fun e _ => Submodule.span_mono ?_
      rintro _ ⟨i, rfl⟩
      exact ⟨i.val,rfl⟩
  rw [A.rank_eq_finrank_span_row, h]
  simpa only [Matrix.rank_eq_finrank_span_row, P] using finrank_iSup_le P Finset.univ

#print axioms rank_le_partition

end Beyond70RankPartition
end RankPartition

section

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Beyond70Slice
open CJ0
open scoped BigOperators

local instance : Fact (Nat.Prime CJ0.p) := ⟨KoalaBear.is_prime⟩

def colLower (g : ℤ) (b : ℕ) : ℕ := ((-g - b + 1) / 2).toNat
def colUpper (s : Source) (q : ℕ) (g : ℤ) : ℕ := min s.C ((s.m : ℤ) - q - g - 1).toNat
def rowLower (s : Source) (q b : ℕ) (g : ℤ) : ℕ :=
  max (colLower g b) ((3*q-(2*b : ℤ)+g+1)-s.m).toNat
def rowUpper (q b : ℕ) (g : ℤ) : ℕ :=
  min (q-b+1) (3*q-(2*b : ℤ)+g+1).toNat

private theorem row_data {s : Source} {q : ℕ} {g : ℤ} (r : ↥(blockRows s.m q g)) :
    r.val.q = q ∧ 0 ≤ g + (r.val.v : ℤ) + 3*(r.val.a : ℤ) ∧
      g + (r.val.v : ℤ) + 3*(r.val.a : ℤ) < s.m := by
  rcases r with ⟨⟨c,b,a⟩,hr⟩
  change (⟨c,b,a⟩ : Jet) ∈ blockRows s.m q g at hr
  rw [blockRows, Finset.mem_filter] at hr
  refine ⟨?_, hr.2.1, hr.2.2⟩
  have hh := hr.1
  rw [Finset.mem_sigma, Finset.mem_sigma, Finset.mem_range, Finset.mem_range,
    Finset.mem_singleton] at hh
  change c < q+1 ∧ b < q-c+1 ∧ a = q-(b+c) at hh

  change a + b + c = q
  omega

private theorem col_q {s : Source} {q : ℕ} {g : ℤ} (j : ↥(blockCols s q g)) :
    j.val.q = q := (Finset.mem_filter.mp j.property).2.1

private theorem col_bounds {s : Source} (hs : ShapeOK s) {q : ℕ} {g : ℤ}
    (r : ↥(blockRows s.m q g)) (j : ↥(blockCols s q g))
    (h : blockEntry r.val j.val ≠ 0) :
    colLower g r.val.b ≤ j.val.c ∧ j.val.c ≤ colUpper s q g ∧ j.val.c ≤ r.val.c := by
  have hguard : j.val.b ≤ r.val.b ∧ j.val.c ≤ r.val.c ∧
      r.val.a + (r.val.b-j.val.b) + (r.val.c-j.val.c) = j.val.a := by
    by_contra hg
    exact h (by simp [blockEntry, hg])
  have hr := row_data r
  have hj := (Finset.mem_filter.mp j.property)
  have hc := (hs.support j.val hj.1).2.2
  have hv := hj.2.2
  simp only [Jet.v, Jet.q, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hv hr
  unfold colLower colUpper
  refine ⟨?_, le_min hc ?_, hguard.2.1⟩
  all_goals omega

private theorem row_bounds {s : Source} {q : ℕ} {g : ℤ}
    (r : ↥(blockRows s.m q g)) (hl : colLower g r.val.b ≤ r.val.c) :
    rowLower s q r.val.b g ≤ r.val.c ∧ r.val.c < rowUpper q r.val.b g := by
  have hr := row_data r
  simp only [Jet.q, Jet.v, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hr
  unfold rowLower rowUpper
  refine ⟨max_le hl ?_, lt_min ?_ ?_⟩
  all_goals omega

private theorem jet_eq {r s : Jet} (hq : r.q = s.q) (hb : r.b = s.b) (hc : r.c = s.c) : r = s := by
  rcases r with ⟨rc,rb,ra⟩
  rcases s with ⟨sc,sb,sa⟩
  simp only [Jet.b, Jet.c] at hb hc
  subst sc
  subst sb
  congr
  simp only [Jet.q, Jet.b, Jet.c, Jet.a] at hq
  omega

theorem block_rank_le_slices (s : Source) (hs : ShapeOK s) (q : ℕ) (g : ℤ) (hp : q < CJ0.p) :
    (blockMatrix s q g).rank ≤ ∑ b ∈ Finset.range (q+1),
      min (rowUpper q b g - rowLower s q b g) (colUpper s q g + 1 - colLower g b) := by
  classical
  let R := ↥(blockRows s.m q g)
  let S := ↥(blockCols s q g)
  let tag (r : R) : Fin (q+1) := ⟨r.val.b, by
    have h := (row_data r).1
    unfold Jet.q at h
    omega⟩
  apply (Beyond70RankPartition.rank_le_partition (blockMatrix s q g) tag).trans
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_le_sum
  intro b _
  let U := {r : R // tag r = b}
  let M := (blockMatrix s q g).submatrix (Subtype.val : U → R) id
  have hb (r : U) : r.val.val.b = b := congrArg Fin.val r.property
  have hwidth : M.rank ≤ colUpper s q g + 1 - colLower g b := by
    apply Beyond70Binomial.fiber_rank (fun r : U => r.val.val) (fun c : S => c.val) q b
      (colLower g b) _ hp (fun r => (row_data r.val).1) col_q hb
    intro r j hj
    have h := col_bounds hs r.val j hj
    rw [hb r] at h
    omega
  apply le_min _ hwidth
  let rows : Finset U := Finset.univ.filter fun r => colLower g b ≤ r.val.val.c
  apply (M.rank_le_card_of_support_subset rows ?_).trans
  · rw [← Fintype.card_coe]
    let f (r : ↥rows) : Fin (rowUpper q b g - rowLower s q b g) :=
      ⟨r.val.val.val.c - rowLower s q b g, by
        have hl := (Finset.mem_filter.mp r.property).2
        have h := row_bounds r.val.val (by rwa [hb r.val])
        rw [hb r.val] at h
        omega⟩
    have hinj : Function.Injective f := by
      intro r j h
      have hr := row_bounds r.val.val (by
        rw [hb r.val]
        exact (Finset.mem_filter.mp r.property).2)
      have hj := row_bounds j.val.val (by
        rw [hb j.val]
        exact (Finset.mem_filter.mp j.property).2)
      rw [hb r.val] at hr
      rw [hb j.val] at hj
      have hc := congrArg Fin.val h
      change r.val.val.val.c - rowLower s q b g = j.val.val.val.c - rowLower s q b g at hc
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact jet_eq ((row_data r.val.val).1.trans (row_data j.val.val).1.symm)
        ((hb r.val).trans (hb j.val).symm) (by omega)
    simpa using Fintype.card_le_of_injective f hinj
  · intro r h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Function.mem_support] at h
    by_contra hn
    apply h
    funext j
    change blockEntry r.val.val j.val = 0
    by_contra hann
    have z := col_bounds hs r.val j hann
    rw [hb r] at z
    omega

def sliceCap (s : Source) (q u b : ℕ) : ℕ :=
  let cmin := (s.J+1-(u+b))/2
  let cmax := min s.C (s.m+s.J-(q+u+1))
  let rmin := max cmin (3*q+u+1-(2*b+s.J+s.m))
  let rmax := min (q-b+1) (3*q+u+1-(2*b+s.J))
  min (rmax-rmin) (cmax+1-cmin)

theorem block_rank_le_slices_nat (s : Source) (hs : ShapeOK s) (q u : ℕ) (hp : q < CJ0.p) :
    (blockMatrix s q ((u : ℤ)-s.J)).rank ≤ CJ1.total (sliceCap s q u) (q+1) := by
  apply (block_rank_le_slices s hs q _ hp).trans
  rw [CJ1.total_eq_sum]
  apply Finset.sum_le_sum
  intro b _
  have hc : colLower ((u : ℤ)-s.J) b = (s.J+1-(u+b))/2 := by unfold colLower; omega
  have hu : colUpper s q ((u : ℤ)-s.J) = min s.C (s.m+s.J-(q+u+1)) := by
    unfold colUpper
    congr 1
    omega
  have hr : rowLower s q b ((u : ℤ)-s.J) = max ((s.J+1-(u+b))/2) (3*q+u+1-(2*b+s.J+s.m)) := by
    unfold rowLower
    rw [hc]
    congr 1
    omega
  have hh : rowUpper q b ((u : ℤ)-s.J) = min (q-b+1) (3*q+u+1-(2*b+s.J)) := by
    unfold rowUpper
    congr 1
    omega
  rw [hc, hu, hr, hh]
  exact le_rfl

#print axioms block_rank_le_slices_nat

end Beyond70Slice
end
