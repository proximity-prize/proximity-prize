import ProximityPrize.SubmissionBinaryLower.B6402PriceRows
import ProximityPrize.SubmissionBinaryLower.B6402RectCover

/-! The eight added inequalities come from the exceptional-fibre count
and membership in a rectangle of the price subdivision. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402PriceCells
open B6402PriceRows B6402RectCover B6402LinearCertificate B6402IntFarkas
set_option autoImplicit false
set_option maxHeartbeats 1500000

def one (j : ℕ) (a b : ℚ) : Row := ⟨[(j,a)],b⟩
def two (i j : ℕ) (a b d : ℚ) : Row := ⟨[(i,a),(j,b)],d⟩

private theorem singleton {n : ℕ} (x : Fin n → ℚ) (i : ℕ) (hi : i<n) (a : ℚ) :
    (∑ t : Fin n,(if i=t.val then a else 0)*x t)=a*x ⟨i,hi⟩ := by
  rw [Finset.sum_eq_single (⟨i,hi⟩ : Fin n)]
  · simp
  · intro j _ h
    have ne : i≠j.val := fun hz => h (Fin.ext hz.symm)
    simp [ne]
  · simp

private theorem value_one {n : ℕ} (x : Fin n → ℚ) (i : ℕ) (a b : ℚ) (hi : i<n) :
    lhs (one i a b) x=a*x ⟨i,hi⟩ := by
  simpa only [lhs,dot,one,coeff,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    using singleton x i hi a

private theorem value_two {n : ℕ} (x : Fin n → ℚ) (i j : ℕ) (a b c : ℚ) (hi : i<n) (hj : j<n) :
    lhs (two i j a b c) x=a*x ⟨i,hi⟩+b*x ⟨j,hj⟩ := by
  simp only [lhs,dot,two,coeff,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    add_mul,Finset.sum_add_distrib,singleton x i hi,singleton x j hj]

def extra (n : ℕ) (b : Box) : List Row :=
  [two 2 n (-1) 1 0, two (n-1) n (-1048575) 2097152 (1-5*1048575),
   one 2 (-1) (-b.p.lo),one 2 1 b.p.hi,one (n-1) (-1) (-b.c.lo),one (n-1) 1 b.c.hi,
   one n (-1) (-b.v.lo),one n 1 b.v.hi]

def cell (ub eq : Array SparseRow) (n : ℕ) (b : Box) := baseRows ub eq ++ (extra n b).toArray

theorem sat {n : ℕ} (big : 2<n) (x : Fin n → ℚ) (v : ℚ) (b : Box)
    (inside : Contains b (x ⟨2,big⟩) (x ⟨n-1,by omega⟩) v)
    (order : v≤x ⟨2,big⟩) (degree : 2097152*v≤(x ⟨n-1,by omega⟩-5)*1048575+1) :
    ∀ r∈extra n b,lhs r (extend x v)≤r.bound := by
  have h2 : 2<n+1 := by omega
  have hlast : n-1<n := by omega
  have hlast' : n-1<n+1 := by omega
  have hn : n<n+1 := by omega
  intro r hr
  simp only [extra,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases inside with ⟨⟨pl,ph⟩,⟨cl,ch⟩,vl,vh⟩
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first
    | rw [value_two _ _ _ _ _ _ h2 hn]
    | rw [value_two _ _ _ _ _ _ hlast' hn]
    | rw [value_one _ _ _ _ h2]
    | rw [value_one _ _ _ _ hlast']
    | rw [value_one _ _ _ _ hn]
  all_goals simp only [extend,dite_eq_left big,dite_eq_left hlast,dite_eq_right (lt_irrefl n),one,two,one_mul,neg_one_mul]
  all_goals linarith

theorem cell_sound {n : ℕ} (big : 2<n) (x : Fin n → ℚ) (v : ℚ) (b : Box)
    (ub eq : Array SparseRow) (hu : ∀ r∈ub.toList,B6402Table4Common.RowValid n r ∧ B6402Table4Common.RowSatLe x r)
    (he : ∀ r∈eq.toList,B6402Table4Common.RowValid n r ∧ B6402Table4Common.RowSatEq x r)
    (inside : Contains b (x ⟨2,big⟩) (x ⟨n-1,by omega⟩) v)
    (order : v≤x ⟨2,big⟩) (degree : 2097152*v≤(x ⟨n-1,by omega⟩-5)*1048575+1) :
    ∀ r∈(cell ub eq n b).toList,lhs r (extend x v)≤r.bound := by
  intro r hr
  simp only [cell,Array.toList_append,List.toList_toArray,List.mem_append] at hr
  exact hr.elim (baseRows_sound x v ub eq hu he r) (sat big x v b inside order degree r)

#print axioms cell_sound
end ProximityPrize.SubmissionBinaryLower.B6402PriceCells
