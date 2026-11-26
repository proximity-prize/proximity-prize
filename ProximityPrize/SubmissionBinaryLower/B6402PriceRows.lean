import ProximityPrize.SubmissionBinaryLower.Binary6402Table4CommonPart0
import ProximityPrize.SubmissionBinaryLower.B6402LinearCertificate

/-! Normalize the actual 6402 geometric rows and extend a profile by its
exceptional order-two fraction. These are the inputs of the rational checker. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402PriceRows
open B6402LinearCertificate B6402IntFarkas B6402Table4Common
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000

def extend {n : ℕ} (x : Fin n → ℚ) (v : ℚ) (j : Fin (n+1)) : ℚ :=
  if hj : j.val<n then x ⟨j.val,hj⟩ else v

def normalize (t : ℚ) (r : SparseRow) : Row :=
  ⟨r.entries.map (fun e => (e.1,t*(e.2 : ℚ)/(BASE_DEN : ℚ))),
    t*(r.rhsNum : ℚ)/(r.rhsDen : ℚ)⟩

private theorem linearize {n : ℕ} (x : Fin n → ℚ) (ls : List (ℕ × ℚ)) (b : ℚ) :
    lhs ⟨ls,b⟩ x=(ls.map (fun e => if h : e.1<n then e.2*x ⟨e.1,h⟩ else 0)).sum := by
  induction ls with
  | nil => simp [lhs,dot,coeff]
  | cons e es ih =>
    simp only [lhs,dot,coeff,List.map_cons,List.sum_cons,add_mul,Finset.sum_add_distrib] at ih ⊢
    rw [ih]
    congr 1
    by_cases hi : e.1<n
    · rw [dif_pos hi,Finset.sum_eq_single (⟨e.1,hi⟩ : Fin n)]
      · simp
      · intro j _ hne
        have h : e.1≠j.val := fun h => hne (Fin.ext h.symm)
        simp [h]
      · simp
    · rw [dif_neg hi]
      apply Finset.sum_eq_zero
      intro j _
      have h : e.1≠j.val := fun h => hi (h ▸ j.isLt)
      simp [h]

theorem normalized_lhs {n : ℕ} (r : SparseRow) (x : Fin n → ℚ) (v t : ℚ)
    (hvalid : RowValid n r) :
    lhs (normalize t r) (extend x v)=t*evalRow x r/(BASE_DEN : ℚ) := by
  unfold normalize
  rw [linearize]
  unfold evalRow
  simp only [List.map_map]
  have go (ls : List (ℕ×ℤ)) (hv : ∀ z∈ls,z.1<n) :
      (ls.map (fun z => if h : z.1<n+1 then t*(z.2 : ℚ)/(BASE_DEN : ℚ)*extend x v ⟨z.1,h⟩ else 0)).sum =
      (t * (ls.map fun z => if h : z.1<n then (z.2 : ℚ)*x ⟨z.1,h⟩ else 0).sum) * (BASE_DEN : ℚ)⁻¹ := by
    induction ls with
    | nil => simp
    | cons p rest ih =>
      have hp := hv p List.mem_cons_self
      have hp' : p.1<n+1 := by omega
      simp only [List.map_cons,List.sum_cons,dite_eq_left hp',dite_eq_left hp]
      rw [ih (fun z hz => hv z (List.mem_cons_of_mem _ hz))]
      simp only [extend,dite_eq_left hp]
      ring
  exact go _ hvalid.2

theorem pos_row {n : ℕ} (r : SparseRow) (x : Fin n → ℚ) (v : ℚ)
    (hvalid : RowValid n r) (h : RowSatLe x r) :
    lhs (normalize 1 r) (extend x v) ≤ (normalize 1 r).bound := by
  rw [normalized_lhs _ _ _ _ hvalid]
  change _ ≤ 1*(r.rhsNum : ℚ)/(r.rhsDen : ℚ)
  have hb : (0:ℚ)<BASE_DEN := by norm_num [BASE_DEN,B6401Params.N]
  apply (div_le_iff₀ hb).mpr
  unfold RowSatLe at h
  simp only [one_mul]
  convert h using 1 <;> ring

theorem neg_eq_row {n : ℕ} (r : SparseRow) (x : Fin n → ℚ) (v : ℚ)
    (hvalid : RowValid n r) (h : RowSatEq x r) :
    lhs (normalize (-1) r) (extend x v) ≤ (normalize (-1) r).bound := by
  rw [normalized_lhs _ _ _ _ hvalid]
  change _ ≤ (-1)*(r.rhsNum : ℚ)/(r.rhsDen : ℚ)
  unfold RowSatEq at h
  rw [h]
  have hn : (BASE_DEN : ℚ)≠0 := by norm_num [BASE_DEN,B6401Params.N]
  apply le_of_eq; field_simp

def baseRows (ub eq : Array SparseRow) : Array Row :=
  (ub.map (normalize 1)) ++ ((eq.toList.flatMap fun r => [normalize 1 r,normalize (-1) r]).toArray)

theorem baseRows_sound {n : ℕ} (x : Fin n → ℚ) (v : ℚ) (ub eq : Array SparseRow)
    (hu : ∀ r∈ub.toList, RowValid n r ∧ RowSatLe x r)
    (he : ∀ r∈eq.toList, RowValid n r ∧ RowSatEq x r) :
    ∀ r∈(baseRows ub eq).toList, lhs r (extend x v) ≤ r.bound := by
  intro r hr
  simp only [baseRows,Array.toList_append,Array.toList_map,List.toList_toArray,List.mem_append,
    List.mem_map,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with ⟨a,ha,rfl⟩ | ⟨a,ha,h⟩
  · exact pos_row a x v (hu _ ha).1 (hu _ ha).2
  · rcases h with rfl|rfl
    · exact pos_row a x v (he _ ha).1 (le_of_eq (he _ ha).2)
    · exact neg_eq_row a x v (he _ ha).1 (he _ ha).2

theorem row_lhs {n : ℕ} (r : Row) (x : Fin n → ℚ) :
    lhs r x=(r.entries.map (fun e => if hi : e.1<n then e.2*x ⟨e.1,hi⟩ else 0)).sum := by
  cases r with | mk l b => exact linearize x l b

#print axioms baseRows_sound
end ProximityPrize.SubmissionBinaryLower.B6402PriceRows
