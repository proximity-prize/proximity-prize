import ProximityPrize.SubmissionBinaryLower.Binary6402Table4K
import ProximityPrize.SubmissionBinaryLower.Binary6402IntSmallCerts

/-! Transport native geometry to the selected 6402 grid cell and extract
the strict ordinary quotient surplus on the carried entries. Adapted from PR 694. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402RowTransport
open Polynomial
open B6401Params hiding A
open B6402HybridP64 (A)
open B6401ContactKerD B6401QuotInterp B6401KerDOrders B6401ResultantOrd
open B6402FarkasVerifier B6402IntFarkas B6402T4Rows B6402IntSmallCerts
open B6402Table4Common B6402Table4NonK B6402Table4K
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open scoped BigOperators
set_option maxHeartbeats 2400000
local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index
lemma baseT4Rows_transport {nv ic : ℕ} (hic_lt : ic < nv) (x : Fin nv → ℚ)
    {cLo1 cLoD1 cHi1 cHiD1 loG1 loGD1 hiG1 hiGD1 : ℕ}
    {cLo2 cLoD2 cHi2 cHiD2 loG2 loGD2 hiG2 hiGD2 : ℕ}
    (hcLoD2 : 0 < cLoD2) (hcHiD2 : 0 < cHiD2)
    (hcLo2 : (cLo2 : ℚ) / (cLoD2 : ℚ) ≤ x ⟨ic, hic_lt⟩)
    (hcHi2 : x ⟨ic, hic_lt⟩ ≤ (cHi2 : ℚ) / (cHiD2 : ℚ))
    (hG_case : (loG2 = loG1 ∧ loGD2 = loGD1 ∧ hiG2 = hiG1 ∧ hiGD2 = hiGD1) ∨
               (loG2 = 0 ∧ loGD2 = 1 ∧ hiG2 = 1 ∧ hiGD2 = 1))
    (hub_old : ∀ r ∈ (baseT4Rows ic cLo1 cLoD1 cHi1 cHiD1 loG1 loGD1 hiG1 hiGD1).1,
      RowValid nv r ∧ RowSatLe x r)
    (heq_old : ∀ r ∈ (baseT4Rows ic cLo1 cLoD1 cHi1 cHiD1 loG1 loGD1 hiG1 hiGD1).2,
      RowValid nv r ∧ RowSatEq x r) :
    (∀ r ∈ (baseT4Rows ic cLo2 cLoD2 cHi2 cHiD2 loG2 loGD2 hiG2 hiGD2).1,
      RowValid nv r ∧ RowSatLe x r) ∧
    (∀ r ∈ (baseT4Rows ic cLo2 cLoD2 cHi2 cHiD2 loG2 loGD2 hiG2 hiGD2).2,
      RowValid nv r ∧ RowSatEq x r) := by
  have hBpos : (0 : ℚ) < (BASE_DEN : ℚ) := by exact_mod_cast base_den_pos
  constructor
  · intro r hr
    unfold baseT4Rows at hr
    dsimp only at hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    have hmem_old : ∀ row : SparseRow,
        row ∈ (baseT4Rows ic cLo1 cLoD1 cHi1 cHiD1 loG1 loGD1 hiG1 hiGD1).1 →
        RowValid nv row ∧ RowSatLe x row := hub_old
    rcases hr with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hr) | hr
    · exact hmem_old _ (by unfold baseT4Rows; simp)
    · exact hmem_old _ (by unfold baseT4Rows; simp)
    · exact hmem_old _ (by unfold baseT4Rows; simp)
    · exact hmem_old _ (by unfold baseT4Rows; simp)
    · exact hmem_old _ (by unfold baseT4Rows; simp)
    · refine ⟨⟨by dsimp; exact_mod_cast hcLoD2, by intro e he; simp at he; rcases he with rfl; exact hic_lt⟩, ?_⟩
      unfold RowSatLe
      simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hic_lt, ↓reduceDIte]
      rw [show (cI (-1) : ℚ) = -(BASE_DEN : ℚ) by unfold cI; push_cast; ring]
      push_cast
      have hmul := mul_le_mul_of_nonneg_left hcLo2 hBpos.le
      linarith [show (BASE_DEN : ℚ) * -(cLo2 : ℚ) / (cLoD2 : ℚ) = -((BASE_DEN : ℚ) * ((cLo2 : ℚ) / (cLoD2 : ℚ))) by ring]
    · refine ⟨⟨by dsimp; exact_mod_cast hcHiD2, by intro e he; simp at he; rcases he with rfl; exact hic_lt⟩, ?_⟩
      unfold RowSatLe
      simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hic_lt, ↓reduceDIte]
      rw [show (cI 1 : ℚ) = (BASE_DEN : ℚ) by unfold cI; push_cast; ring]
      push_cast
      have hmul := mul_le_mul_of_nonneg_left hcHi2 hBpos.le
      linarith [show (BASE_DEN : ℚ) * (cHi2 : ℚ) / (cHiD2 : ℚ) = (BASE_DEN : ℚ) * ((cHi2 : ℚ) / (cHiD2 : ℚ)) by ring]
    · exact hmem_old _ (by unfold baseT4Rows; simp)
    · exact hmem_old _ (by unfold baseT4Rows; simp)
    · rcases hG_case with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · exact hmem_old _ (by unfold baseT4Rows; simp [hr])
      · simp at hr
    · rcases hG_case with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · exact hmem_old _ (by unfold baseT4Rows; simp [hr])
      · simp at hr
  · intro r hr
    exact heq_old r (by unfold baseT4Rows at hr ⊢; simpa using hr)

lemma buildT4ARows_transport (br : T4ABranch) (x : Fin (t4aNumVars br) → ℚ)
    {cLo1 cLoD1 cHi1 cHiD1 loG1 loGD1 hiG1 hiGD1 : ℕ}
    {cLo2 cLoD2 cHi2 cHiD2 loG2 loGD2 hiG2 hiGD2 : ℕ}
    (hcLoD2 : 0 < cLoD2) (hcHiD2 : 0 < cHiD2)
    (hcLo2 : (cLo2 : ℚ) / (cLoD2 : ℚ) ≤ x ⟨t4aNumVars br - 1, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩)
    (hcHi2 : x ⟨t4aNumVars br - 1, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ ≤ (cHi2 : ℚ) / (cHiD2 : ℚ))
    (hG_case : (loG2 = loG1 ∧ loGD2 = loGD1 ∧ hiG2 = hiG1 ∧ hiGD2 = hiGD1) ∨
               (loG2 = 0 ∧ loGD2 = 1 ∧ hiG2 = 1 ∧ hiGD2 = 1))
    (hub_old : ∀ r ∈ (buildT4ARows br cLo1 cLoD1 cHi1 cHiD1 loG1 loGD1 hiG1 hiGD1).1.toList,
      RowValid (t4aNumVars br) r ∧ RowSatLe x r)
    (heq_old : ∀ r ∈ (buildT4ARows br cLo1 cLoD1 cHi1 cHiD1 loG1 loGD1 hiG1 hiGD1).2.toList,
      RowValid (t4aNumVars br) r ∧ RowSatEq x r) :
    (∀ r ∈ (buildT4ARows br cLo2 cLoD2 cHi2 cHiD2 loG2 loGD2 hiG2 hiGD2).1.toList,
      RowValid (t4aNumVars br) r ∧ RowSatLe x r) ∧
    (∀ r ∈ (buildT4ARows br cLo2 cLoD2 cHi2 cHiD2 loG2 loGD2 hiG2 hiGD2).2.toList,
      RowValid (t4aNumVars br) r ∧ RowSatEq x r) := by
  have htr := baseT4Rows_transport (nv := t4aNumVars br) (ic := t4aNumVars br - 1)
    (by cases br <;> dsimp only [t4aNumVars] <;> omega) x hcLoD2 hcHiD2 hcLo2 hcHi2 hG_case
    (fun r hr => hub_old r (by simp only [buildT4ARows, List.toList_toArray, List.mem_append]; exact Or.inl hr))
    (fun r hr => heq_old r (by simp only [buildT4ARows, List.toList_toArray, List.mem_append]; exact Or.inl hr))
  constructor
  · intro r hr
    simp only [buildT4ARows, List.toList_toArray, List.mem_append] at hr
    rcases hr with hr | hr
    · exact htr.1 r hr
    · exact hub_old r (by simp only [buildT4ARows, List.toList_toArray, List.mem_append]; exact Or.inr hr)
  · intro r hr
    simp only [buildT4ARows, List.toList_toArray, List.mem_append] at hr
    rcases hr with hr | hr
    · exact htr.2 r hr
    · exact heq_old r (by simp only [buildT4ARows, List.toList_toArray, List.mem_append]; exact Or.inr hr)

lemma buildT4BRows_transport (br : T4BBranch) (x : Fin 49 → ℚ)
    {cLo1 cLoD1 cHi1 cHiD1 loG1 loGD1 hiG1 hiGD1 : ℕ}
    {cLo2 cLoD2 cHi2 cHiD2 loG2 loGD2 hiG2 hiGD2 : ℕ}
    (hcLoD2 : 0 < cLoD2) (hcHiD2 : 0 < cHiD2)
    (hcLo2 : (cLo2 : ℚ) / (cLoD2 : ℚ) ≤ x ⟨48, by decide⟩)
    (hcHi2 : x ⟨48, by decide⟩ ≤ (cHi2 : ℚ) / (cHiD2 : ℚ))
    (hG_case : (loG2 = loG1 ∧ loGD2 = loGD1 ∧ hiG2 = hiG1 ∧ hiGD2 = hiGD1) ∨
               (loG2 = 0 ∧ loGD2 = 1 ∧ hiG2 = 1 ∧ hiGD2 = 1))
    (hub_old : ∀ r ∈ (buildT4BRows br cLo1 cLoD1 cHi1 cHiD1 loG1 loGD1 hiG1 hiGD1).1.toList,
      RowValid 49 r ∧ RowSatLe x r)
    (heq_old : ∀ r ∈ (buildT4BRows br cLo1 cLoD1 cHi1 cHiD1 loG1 loGD1 hiG1 hiGD1).2.toList,
      RowValid 49 r ∧ RowSatEq x r) :
    (∀ r ∈ (buildT4BRows br cLo2 cLoD2 cHi2 cHiD2 loG2 loGD2 hiG2 hiGD2).1.toList,
      RowValid 49 r ∧ RowSatLe x r) ∧
    (∀ r ∈ (buildT4BRows br cLo2 cLoD2 cHi2 cHiD2 loG2 loGD2 hiG2 hiGD2).2.toList,
      RowValid 49 r ∧ RowSatEq x r) := by
  have htr := baseT4Rows_transport (nv := 49) (ic := 48)
    (by decide) x hcLoD2 hcHiD2 hcLo2 hcHi2 hG_case
    (fun r hr => hub_old r (by simp only [buildT4BRows, List.toList_toArray, List.mem_append]; exact Or.inl hr))
    (fun r hr => heq_old r (by simp only [buildT4BRows, List.toList_toArray, List.mem_append]; exact Or.inl hr))
  constructor
  · intro r hr
    simp only [buildT4BRows, List.toList_toArray, List.mem_append] at hr
    rcases hr with hr | hr
    · exact htr.1 r hr
    · exact hub_old r (by simp only [buildT4BRows, List.toList_toArray, List.mem_append]; exact Or.inr hr)
  · intro r hr
    simp only [buildT4BRows, List.toList_toArray, List.mem_append] at hr
    rcases hr with hr | hr
    · exact htr.2 r hr
    · exact heq_old r (by simp only [buildT4BRows, List.toList_toArray, List.mem_append]; exact Or.inr hr)

/-- Concavity linearization: `(∑ i, rankDiffQ 1 m s (D.k i)) / N ≤ ∑_{j < 4} rankDiffQ(j) x_j + (rd3 - rd2) x_4`. -/
lemma sum_rankDiffQ_le_linearized (D : KerD45Data) {nv : ℕ} (h5 : 5 < nv) (m s : ℕ) (hm : 0 < m)
    (x : Fin nv → ℚ)
    (hx0 : x ⟨0, by omega⟩ = (D.n0 : ℚ) / (N : ℚ))
    (hx1 : x ⟨1, by omega⟩ = (D.n1 : ℚ) / (N : ℚ))
    (hx2 : x ⟨2, by omega⟩ = (D.n2 : ℚ) / (N : ℚ))
    (hx3 : x ⟨3, by omega⟩ = (D.n3 : ℚ) / (N : ℚ))
    (hx4 : x ⟨4, by omega⟩ = (D.nt : ℚ) / (N : ℚ)) :
    (∑ i : Idx, rankDiffQ 1 m s (D.k i)) / (N : ℚ) ≤
      (∑ j : Fin 4, rankDiffQ 1 m s j.val * x ⟨j.val, by omega⟩) +
      (rankDiffQ 1 m s 3 - rankDiffQ 1 m s 2) * x ⟨4, by omega⟩ := by
  have hNpos : (0 : ℚ) < (N : ℚ) := by norm_num [N]
  have hm2pos : (0 : ℚ) < (m : ℚ) * (m : ℚ) := by
    have hmQ : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
    positivity
  have hpt : ∀ i : Idx,
      rankDiffQ 1 m s (D.k i) ≤
        (if D.k i = 0 then rankDiffQ 1 m s 0 else 0) +
        (if D.k i = 1 then rankDiffQ 1 m s 1 else 0) +
        (if D.k i = 2 then rankDiffQ 1 m s 2 else 0) +
        (if 3 ≤ D.k i then rankDiffQ 1 m s 3 else 0) +
        (rankDiffQ 1 m s 3 - rankDiffQ 1 m s 2) * ((D.k i - 3 : ℕ) : ℚ) := by
    intro i
    by_cases h0 : D.k i = 0
    · simp [h0]
    by_cases h1 : D.k i = 1
    · simp [h1]
    by_cases h2 : D.k i = 2
    · simp [h2]
    have h3 : 3 ≤ D.k i := by omega
    simp only [h0, h1, h2, h3, ↓reduceIte, zero_add, add_zero]
    unfold rankDiffQ
    have hnat := rankKerD_diff_le_linear_tail m s 1 3 (D.k i) (by omega) h3
    have hle23 : rankKerD m s - rankKerD (m - 2) (s - 1) ≤ rankKerD m s - rankKerD (m - 3) (s - 1) := by
      have hmono : rankKerD (m - 3) (s - 1) ≤ rankKerD (m - 2) (s - 1) :=
        rankKerD_mono_left (s - 1) (by omega)
      omega
    have hQ : ((rankKerD m s - rankKerD (m - D.k i) (s - 1) : ℕ) : ℚ) ≤
        ((rankKerD m s - rankKerD (m - 3) (s - 1) : ℕ) : ℚ) +
        (((rankKerD m s - rankKerD (m - 3) (s - 1) : ℕ) : ℚ) -
         ((rankKerD m s - rankKerD (m - 2) (s - 1) : ℕ) : ℚ)) * ((D.k i - 3 : ℕ) : ℚ) := by
      have hcast : ((rankKerD m s - rankKerD (m - D.k i) (s - 1) : ℕ) : ℚ) ≤
          (((rankKerD m s - rankKerD (m - 3) (s - 1)) +
            (D.k i - 3) * ((rankKerD m s - rankKerD (m - 3) (s - 1)) -
              (rankKerD m s - rankKerD (m - 2) (s - 1))) : ℕ) : ℚ) := by
        exact_mod_cast hnat
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hle23] at hcast
      linarith
    have hdiv := div_le_div_of_nonneg_right hQ hm2pos.le
    calc _ ≤ _ := hdiv
      _ = _ := by ring
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpt i
  have hrhs_eq :
      (∑ i : Idx, ((if D.k i = 0 then rankDiffQ 1 m s 0 else 0) +
        (if D.k i = 1 then rankDiffQ 1 m s 1 else 0) +
        (if D.k i = 2 then rankDiffQ 1 m s 2 else 0) +
        (if 3 ≤ D.k i then rankDiffQ 1 m s 3 else 0) +
        (rankDiffQ 1 m s 3 - rankDiffQ 1 m s 2) * ((D.k i - 3 : ℕ) : ℚ))) / (N : ℚ) =
      (∑ j : Fin 4, rankDiffQ 1 m s j.val * x ⟨j.val, by omega⟩) +
      (rankDiffQ 1 m s 3 - rankDiffQ 1 m s 2) * x ⟨4, by omega⟩ := by
    have hgen : ∀ S0 : Finset Idx,
        (∑ i ∈ S0, ((if D.k i = 0 then rankDiffQ 1 m s 0 else 0) +
          (if D.k i = 1 then rankDiffQ 1 m s 1 else 0) +
          (if D.k i = 2 then rankDiffQ 1 m s 2 else 0) +
          (if 3 ≤ D.k i then rankDiffQ 1 m s 3 else 0) +
          (rankDiffQ 1 m s 3 - rankDiffQ 1 m s 2) * ((D.k i - 3 : ℕ) : ℚ))) =
        ((S0.filter fun i => D.k i = 0).card : ℚ) * rankDiffQ 1 m s 0 +
        ((S0.filter fun i => D.k i = 1).card : ℚ) * rankDiffQ 1 m s 1 +
        ((S0.filter fun i => D.k i = 2).card : ℚ) * rankDiffQ 1 m s 2 +
        ((S0.filter fun i => 3 ≤ D.k i).card : ℚ) * rankDiffQ 1 m s 3 +
        (rankDiffQ 1 m s 3 - rankDiffQ 1 m s 2) * (∑ i ∈ S0, ((D.k i - 3 : ℕ) : ℚ)) := by
      intro S0
      simp only [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [hgen Finset.univ]
    have hnt_cast : (∑ i : Idx, ((D.k i - 3 : ℕ) : ℚ)) = (D.nt : ℚ) := by
      unfold KerD45Data.nt; rw [Nat.cast_sum]
    rw [hnt_cast]
    have hfc : ∀ {P : Idx → Prop} (i1 i2 : DecidablePred P),
        (@Finset.filter Idx P i1 Finset.univ).card = (@Finset.filter Idx P i2 Finset.univ).card :=
      fun _ _ => congrArg Finset.card (by ext i; simp only [Finset.mem_filter])
    have hn0 : (Finset.univ.filter fun i : Idx => D.k i = 0).card = D.n0 := by
      unfold KerD45Data.n0; exact hfc _ _
    have hn1 : (Finset.univ.filter fun i : Idx => D.k i = 1).card = D.n1 := by
      unfold KerD45Data.n1; exact hfc _ _
    have hn2 : (Finset.univ.filter fun i : Idx => D.k i = 2).card = D.n2 := by
      unfold KerD45Data.n2; exact hfc _ _
    have hn3 : (Finset.univ.filter fun i : Idx => 3 ≤ D.k i).card = D.n3 := by
      unfold KerD45Data.n3; exact hfc _ _
    rw [hn0, hn1, hn2, hn3]
    simp only [Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two,
      show (3 : Fin 4).val = 3 from rfl, hx0, hx1, hx2, hx3, hx4]
    ring
  rw [← hrhs_eq]
  exact div_le_div_of_nonneg_right hsum hNpos.le

/-- Extract strict quotient surplus + `CapWitness` checks from a satisfied `checkT4Bucket = true`. -/
lemma table4_surplus_from_bucket (D : KerD45Data) {nv : ℕ} (h5 : 5 < nv)
    (rows : Array SparseRow × Array SparseRow)
    (cLoNum cLoDen cHiNum cHiDen : ℕ) (b : T4BucketCert)
    (hchk : checkT4Bucket nv rows.1 rows.2 cLoNum cLoDen cHiNum cHiDen b = true)
    (hcLo : (cLoNum : ℚ) / (cLoDen : ℚ) ≤ (D.W_F : ℚ) / (wY : ℚ))
    (hcHi : (D.W_F : ℚ) / (wY : ℚ) ≤ (cHiNum : ℚ) / (cHiDen : ℚ))
    (x : Fin nv → ℚ) (hx_nn : ∀ j, 0 ≤ x j)
    (hx0 : x ⟨0, by omega⟩ = (D.n0 : ℚ) / (N : ℚ))
    (hx1 : x ⟨1, by omega⟩ = (D.n1 : ℚ) / (N : ℚ))
    (hx2 : x ⟨2, by omega⟩ = (D.n2 : ℚ) / (N : ℚ))
    (hx3 : x ⟨3, by omega⟩ = (D.n3 : ℚ) / (N : ℚ))
    (hx4 : x ⟨4, by omega⟩ = (D.nt : ℚ) / (N : ℚ))
    (hxic : x ⟨nv - 1, by omega⟩ = (D.W_F : ℚ) / (wY : ℚ))
    (hub : ∀ r ∈ rows.1.toList, RowValid nv r ∧ RowSatLe x r)
    (heq : ∀ r ∈ rows.2.toList, RowValid nv r ∧ RowSatEq x r) :
    0 < b.m ∧ 1 ≤ b.s ∧ 0 < cHiDen ∧ 0 < b.δNum ∧ 0 < b.δDen ∧ 0 < b.hiGDen ∧
    (b.δNum : ℚ) / (b.δDen : ℚ) <
      vquotLbQ 1 b.m b.s ((D.W_F : ℚ) / (wY : ℚ)) - (∑ i : Idx, rankDiffQ 1 b.m b.s (D.k i)) / (N : ℚ) ∧
    checkCapWitness 1 b.m b.s cHiNum cHiDen b.δNum b.δDen b.hiGNum b.hiGDen 1 b.cap1 = true ∧
    checkCapWitness 1 b.m b.s cHiNum cHiDen b.δNum b.δDen b.hiGNum b.hiGDen 2 b.cap2 = true := by
  have hmem1 : ∀ i (hi : i < rows.1.size), rows.1[i] ∈ rows.1.toList := fun i hi =>
    Array.mem_toList_iff.mpr (Array.getElem_mem hi)
  have hmem2 : ∀ i (hi : i < rows.2.size), rows.2[i] ∈ rows.2.toList := fun i hi =>
    Array.mem_toList_iff.mpr (Array.getElem_mem hi)
  have ⟨hm0, hm_pos_fn⟩ := checkT4Bucket_sound rows.1 rows.2 cLoNum cLoDen cHiNum cHiDen b hchk
    (fun i hi => (hub _ (hmem1 i hi)).1.1)
    (fun i hi => (heq _ (hmem2 i hi)).1.1)
    (fun i hi => (hub _ (hmem1 i hi)).1.2)
    (fun i hi => (heq _ (hmem2 i hi)).1.2)
    x hx_nn
    (fun i hi => (hub _ (hmem1 i hi)).2)
    (fun i hi => (heq _ (hmem2 i hi)).2)
  have hmpos : 0 < b.m := Nat.pos_of_ne_zero hm0
  obtain ⟨h5', hfn⟩ := hm_pos_fn hmpos
  have ⟨hsurp_lin, hcap1, hcap2⟩ := hfn (by rw [hxic]; exact hcLo) (by rw [hxic]; exact hcHi)
  have hlin_le := sum_rankDiffQ_le_linearized D h5' b.m b.s hmpos x hx0 hx1 hx2 hx3 hx4
  have hsurp : (b.δNum : ℚ) / (b.δDen : ℚ) <
      vquotLbQ 1 b.m b.s ((D.W_F : ℚ) / (wY : ℚ)) - (∑ i : Idx, rankDiffQ 1 b.m b.s (D.k i)) / (N : ℚ) := by
    rw [hxic] at hsurp_lin; linarith
  have hpars : 1 ≤ b.s ∧ 0 < cHiDen ∧ 0 < b.δNum ∧ 0 < b.δDen ∧ 0 < b.hiGDen := by
    unfold checkCapWitness at hcap1
    by_contra hbad
    have hif : (b.m == 0 || b.s < 1 || cHiDen == 0 || b.δNum == 0 || b.δDen == 0 || b.hiGDen == 0) = true := by
      push Not at hbad
      rcases lt_or_ge b.s 1 with hs | hs
      · simp [hs]
      · rcases Nat.eq_zero_or_pos cHiDen with hc | hc
        · simp [hc]
        · rcases Nat.eq_zero_or_pos b.δNum with hd1 | hd1
          · simp [hd1]
          · rcases Nat.eq_zero_or_pos b.δDen with hd2 | hd2
            · simp [hd2]
            · have h0 : b.hiGDen = 0 := by have := hbad hs hc hd1 hd2; omega
              simp [h0]
    rw [if_pos hif] at hcap1; cases hcap1
  exact ⟨hmpos, hpars.1, hpars.2.1, hpars.2.2.1, hpars.2.2.2.1, hpars.2.2.2.2, hsurp, hcap1, hcap2⟩


#print axioms buildT4ARows_transport
#print axioms table4_surplus_from_bucket
end ProximityPrize.SubmissionBinaryLower.B6402RowTransport
