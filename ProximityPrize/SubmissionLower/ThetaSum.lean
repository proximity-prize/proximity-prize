import ProximityPrize.SubmissionLower.ThetaBlock
import ProximityPrize.SubmissionLower.ThetaSumTotal

/-!
The theta savings of the primary blocks, summed over the strip of grades 1354..3011.
-/

set_option Elab.async false

namespace ThetaSum
open K1_13 hiding chart
open K1_13_2 K1_13_2_2 K1_13_2_3 ThetaBlock
open scoped BigOperators
open private fastCum_eq oldCount_eq kernel_eq chart zero_residual blockBound_eq
  from ProximityPrize.SubmissionLower.Fast060

theorem fastDen_eq' (u : ℤ) : fastDen u = K1_13_2_3_7.fastDen u := rfl

theorem fastCum_eq' (d u : ℤ) : fastCum d u = K1_13_2_3_7.fastCum d u := by
  first
    | rfl
    | simp only [fastCum, K1_13_2_3_7.fastCum, fastDen_eq']

theorem signedKernel_eq' (d j h : ℤ) :
    signedKernel d j h = K1_13_2_3_7.signedKernel d j h := by
  first
    | rfl
    | simp only [signedKernel, K1_13_2_3_7.signedKernel, fastCum_eq']

/-- The theta bound of a block, where it applies. -/
def thetaBound (i : BlockIndex) : ℕ :=
  if 2999 ≤ i.1.val + i.2.val ∧ i.1.val + i.2.val ≤ 4650 then
    (thetaCount (activeFlag i)).toNat
  else baseline i

/-- The saving of the theta bound over the block bound without products. -/
def thetaSave (i : BlockIndex) : ℕ := baseline i - min (baseline i) (thetaBound i)

theorem thetaSave_eq (i : BlockIndex) (h1 : 3000 ≤ i.1.val + i.2.val)
    (h2 : i.1.val + i.2.val ≤ 3500) (hj : i.2.val ≤ 1646) :
    thetaSave i = tsFast i.1.val i.2.val := by
  have hf : initialFlag i = chart (min (i.1.val : ℤ) 1650) (i.2.val : ℤ)
      (4649 - (i.1.val : ℤ) - i.2.val) := by
    unfold initialFlag chart offset
    congr 1 <;> omega
  have horder : 0 < (initialFlag i).order := by
    rw [hf]
    change (0 : ℤ) < (4649 - (i.1.val : ℤ) - i.2.val) + 1
    omega
  have hu : (initialFlag i).upper ≤ 2999 - offset i := by
    rw [hf]
    change (1650 : ℤ) ≤ 2999 - ((i.2.val : ℤ) - 1650)
    omega
  have hj₀ : (0 : ℤ) ≤ (i.2.val : ℤ) := Int.natCast_nonneg _
  have hbase : baseline i =
      (K1_13_2_3_7.fastCum (min (i.1.val : ℤ) 1650) 1650 -
        K1_13_2_3_7.fastCum (min (i.1.val : ℤ) 1650) (1649 - (i.2.val : ℤ)) -
        max 0 (K1_13_2_3_7.signedKernel (min (i.1.val : ℤ) 1650) (i.2.val : ℤ)
          (4649 - (i.1.val : ℤ) - i.2.val))).toNat := by
    unfold baseline
    rw [blockBound_eq _ _ horder hu, zero_residual, max_self, hf, oldCount_eq _ _ _ hj₀,
      kernel_eq _ _ _ (by omega) hj₀]
  have hth : thetaCount (activeFlag i) =
      cumulative (min (i.1.val : ℤ) 1650) (3000 - (i.1.val : ℤ) - ((i.2.val : ℤ) - 1650) - 1) -
      cumulative (min (i.1.val : ℤ) 1650)
        (-((i.2.val : ℤ) - 1650) - 3 * (min (1650 : ℤ) (2999 - ((i.2.val : ℤ) - 1650)) + 1 -
          (3000 - (i.1.val : ℤ) - ((i.2.val : ℤ) - 1650))) - 1) := rfl
  have e1 : 3000 - (i.1.val : ℤ) - ((i.2.val : ℤ) - 1650) - 1 =
      4649 - (i.1.val : ℤ) - i.2.val := by omega
  have e2 : -((i.2.val : ℤ) - 1650) - 3 * (min (1650 : ℤ) (2999 - ((i.2.val : ℤ) - 1650)) + 1 -
      (3000 - (i.1.val : ℤ) - ((i.2.val : ℤ) - 1650))) - 1 =
      1649 - (i.2.val : ℤ) - 3 * ((i.1.val : ℤ) + i.2.val - 2999) := by omega
  have hbound : thetaBound i =
      (K1_13_2_3_7.fastCum (min (i.1.val : ℤ) 1650) (4649 - (i.1.val : ℤ) - i.2.val) -
        K1_13_2_3_7.fastCum (min (i.1.val : ℤ) 1650)
          (1649 - (i.2.val : ℤ) - 3 * ((i.1.val : ℤ) + i.2.val - 2999))).toNat := by
    unfold thetaBound
    rw [if_pos ⟨by omega, by omega⟩, hth, e1, e2, fastCum_eq, fastCum_eq]
  unfold thetaSave tsFast
  rw [hbase, hbound]
  simp only [fastCum_eq', signedKernel_eq']

/-- The strip of blocks summed by the certificate. -/
def embed : Fin 1658 × Fin 1647 ↪ BlockIndex where
  toFun x := (⟨1354 + x.1.val, by have := x.1.isLt; omega⟩, x.2.castLE (by decide))
  inj' := by
    intro x y h
    apply Prod.ext <;> apply Fin.ext
    · have e := congrArg (fun i : BlockIndex => i.1.val) h
      change 1354 + x.1.val = 1354 + y.1.val at e
      omega
    · exact congrArg (fun i : BlockIndex => i.2.val) h

theorem rangeSum_eq (f : ℕ → ℕ) (n : ℕ) :
    rangeSum f n = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp [rangeSum]
  | succ n ih => rw [rangeSum, Finset.sum_range_succ, ih]

theorem rangeSum_fin (f : ℕ → ℕ) (n : ℕ) :
    rangeSum f n = ∑ k : Fin n, f k.val := by
  rw [rangeSum_eq, Fin.sum_univ_eq_sum_range]

theorem sum_embed_le {α β : Type*} [Fintype α] [Fintype β] (e : α ↪ β) (f : β → ℕ) :
    (∑ i : α, f (e i)) ≤ ∑ i : β, f i := calc
  _ = ∑ i ∈ Finset.univ.map e, f i := by rw [Finset.sum_map]
  _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun _ _ _ => Nat.zero_le _)

/-- Savings counted by the certificate: the theta savings on the grades below 3012. -/
def stripSave (i : BlockIndex) : ℕ := if i.1.val < 3012 then thetaSave i else 0

theorem entry_le (x : Fin 1658 × Fin 1647) :
    entry (1354 + x.1.val) x.2.val ≤ stripSave (embed x) := by
  have ha := x.1.isLt
  have hb := x.2.isLt
  have hs : (embed x).1.val = 1354 + x.1.val := rfl
  have hj : (embed x).2.val = x.2.val := rfl
  unfold entry stripSave
  by_cases hreg : 3000 ≤ 1354 + x.1.val + x.2.val ∧
      4 * (1354 + x.1.val + x.2.val - 3000) ≤ 1354 + x.1.val - 1354 ∧
      9 * (1354 + x.1.val - 2304) ≤ 20 * (1354 + x.1.val + x.2.val - 3000) + 19
  · have hlt : (embed x).1.val < 3012 := by rw [hs]; omega
    have h := thetaSave_eq (embed x) (by rw [hs, hj]; omega) (by rw [hs, hj]; omega)
      (by rw [hj]; omega)
    rw [if_pos hreg, if_pos hlt, h]
    exact le_refl _
  · rw [if_neg hreg]
    exact Nat.zero_le _

theorem total_le : 288366984459 ≤ ∑ i : BlockIndex, stripSave i := by
  rw [← total]
  unfold chunk
  simp only [rangeSum_fin, row]
  rw [← Finset.sum_product Finset.univ Finset.univ
    (fun x : Fin 1658 × Fin 1647 => entry (1354 + x.1.val) x.2.val), Finset.univ_product_univ]
  exact (Finset.sum_le_sum fun x _ => entry_le x).trans (sum_embed_le embed stripSave)

#print axioms total_le

end ThetaSum
