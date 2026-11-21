import ProximityPrize.SubmissionLower.PoleBlocks

namespace PoleFamily

open PoleBlocks MvPolynomial
open scoped BigOperators Matrix

noncomputable section

/-- The passive seed degree, followed by the joint active grade and the shifted offset. -/
abbrev Label (U B J : ℕ) :=
  (u : Fin (U+1)) × (_n : Fin (B+(U-u.val)+1)) × Fin (B+2*J)

def offset {U B J : ℕ} (i : Label U B J) : ℤ := (i.2.2.val : ℤ) - J

abbrev Columns {U B J : ℕ} (i : Label U B J) :=
  BlockColumn i.2.1.val B (U-i.1.val) (offset i) J

abbrev Rows {U B J : ℕ} (i : Label U B J) :=
  (s : Fin (min i.2.1.val B+1)) × BlockRow (B+J) (offset i) s.val

def rowExponent {U B J : ℕ} (r : Sigma (@Rows U B J)) : Fin 4 →₀ ℕ :=
  blockOutput (n := r.1.2.1.val) r.2.1.val r.2.2

def colInput {U B J : ℕ} (c : Sigma (@Columns U B J)) : Input := blockInput c.2

/-- The actual normalized coefficients. The passive variable is unchanged, so
different passive exponents have zero coefficient independently of the active chart. -/
def matrix (F : Type*) [Field F] (U B J : ℕ) :
    Matrix (Sigma (@Rows U B J)) (Sigma (@Columns U B J)) F :=
  Matrix.of fun r c ↦
    if r.1.1 = c.1.1 then (chartMonomial F (colInput c)).coeff (rowExponent r) else 0

private theorem label_eq_of_tags {U B J : ℕ} (i j : Label U B J)
    (hu : i.1 = j.1) (hn : i.2.1.val = j.2.1.val) (hg : offset i = offset j) : i = j := by
  rcases i with ⟨u,n,g⟩
  rcases j with ⟨v,m,h⟩
  dsimp only at hu hn
  subst v
  have he : n = m := Fin.ext hn
  subst m
  have hh : g = h := Fin.ext (by unfold offset at hg; dsimp at hg; omega)
  subst h
  rfl

theorem row_tag {U B J : ℕ} (r : Sigma (@Rows U B J)) :
    outputTag (rowExponent r) = (r.1.2.1.val, offset r.1) := by
  let s := r.2.1
  let l := r.2.2
  have hs := s.isLt
  have hl := l.property.1
  have hx := l.property.2
  change outputTag (blockOutput (n := r.1.2.1.val) s.val l) = _
  simp [blockOutput, outputTag, exponent]
  constructor <;> omega

theorem col_tag {U B J : ℕ} (c : Sigma (@Columns U B J)) :
    (colInput c).tag = (c.1.2.1.val, offset c.1) := by
  have hq := c.2.1.val.isLt
  let j := (-(offset c.1)).toNat + c.2.2.val
  have hj : (-(offset c.1)).toNat ≤ j := Nat.le_add_right _ _
  change (c.1.2.1.val - c.2.1.val.val + c.2.1.val.val,
    ((offset c.1 + j).toNat : ℤ) - j) = (c.1.2.1.val, offset c.1)
  congr 1 <;> omega

theorem matrix_zero_off_label {F : Type*} [Field F] {U B J : ℕ}
    (r : Sigma (@Rows U B J)) (c : Sigma (@Columns U B J)) (hne : r.1 ≠ c.1) :
    matrix F U B J r c = 0 := by
  unfold matrix
  change (if r.1.1 = c.1.1 then (chartMonomial F (colInput c)).coeff (rowExponent r) else 0) = _
  split
  · rename_i hu
    apply coeff_eq_zero_of_tag_ne
    rw [row_tag, col_tag]
    intro he
    exact hne (label_eq_of_tags _ _ hu (congrArg Prod.fst he) (congrArg Prod.snd he))
  · rfl

/-- Summing diagonal ranks for finite dependent row and column fibers. -/
theorem rank_matched_sigma_le {F I : Type*} [Field F] [Fintype I]
    {R C : I → Type*} [∀ i, Fintype (R i)] [∀ i, Fintype (C i)]
    (A : Matrix (Sigma R) (Sigma C) F)
    (hzero : ∀ r c, r.1 ≠ c.1 → A r c = 0) :
    A.rank ≤ ∑ i, (A.submatrix (Sigma.mk i) (Sigma.mk i)).rank := by
  refine (rank_sigma_rows_le_sum A).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  apply Sol1.C52.rank_le_col_representatives _ (Sigma.mk i)
  rintro ⟨j,c⟩
  by_cases h : j = i
  · subst j
    exact Or.inr ⟨c,rfl⟩
  · left
    funext r
    exact hzero ⟨i,r⟩ ⟨j,c⟩ (Ne.symm h)

def blockBound {U B J : ℕ} (i : Label U B J) : ℕ :=
  let n := i.2.1.val
  let g := offset i
  min (∑ q : ColumnGrade n B (U-i.1.val), slotCount g J q.val.val)
    (∑ s : Fin (min n B+1), min (slotCount g J s.val) (((B+J : ℕ) : ℤ)-g-s.val).toNat)

/-- The finite full normalized matrix rank, summing passive exponents,
joint grades and offsets from -J through B+J-1. -/
theorem matrix_rank_le {F : Type*} [Field F] (U B J : ℕ) :
    (matrix F U B J).rank ≤
      ∑ u : Fin (U+1), ∑ n : Fin (B+(U-u.val)+1), ∑ h : Fin (B+2*J), blockBound ⟨u,n,h⟩ := by
  have h := rank_matched_sigma_le (matrix F U B J) matrix_zero_off_label
  rw [Fintype.sum_sigma] at h
  simp_rw [Fintype.sum_sigma] at h
  refine h.trans (Finset.sum_le_sum fun u _ ↦ Finset.sum_le_sum fun n _ ↦ Finset.sum_le_sum fun h _ ↦ ?_)
  let i : Label U B J := ⟨u,n,h⟩
  change ((matrix F U B J).submatrix (Sigma.mk i) (Sigma.mk i)).rank ≤ blockBound i
  have he : (matrix F U B J).submatrix (Sigma.mk i) (Sigma.mk i) =
      (Matrix.of fun (r : Rows i) (c : Columns i) ↦
        (chartMonomial F (blockInput c)).coeff (blockOutput (n := n.val) r.1.val r.2)) := by
    ext r c
    simp [Matrix.submatrix, matrix, rowExponent, colInput, i]
  rw [he]
  exact rank_concrete_block_le (B+J) n.val B (U-u.val) J (offset i)

/-- Every finite source monomial below the X cutoff has a normalized column.
The block model may keep extra columns whose X power is already too large,
which can only enlarge the ambient coefficient matrix. -/
theorem column_exists {U B J : ℕ} (u : Fin (U+1)) (i : Input)
    (hseed : i.b ≤ U-u.val) (hq : i.q ≤ B) (hj : i.j ≤ J) (hx : i.a < B+J) :
    ∃ c : Sigma (@Columns U B J), c.1.1 = u ∧ colInput c = i := by
  obtain ⟨a,q,j,b,hjq⟩ := i
  dsimp at hseed hq hj hx
  let n : Fin (B+(U-u.val)+1) := ⟨b+q, by omega⟩
  let h : Fin (B+2*J) := ⟨((a : ℤ)-j+J).toNat, by omega⟩
  let l : Label U B J := ⟨u,n,h⟩
  have hg : offset l = (a : ℤ)-j := by
    dsimp [offset,l,h]
    omega
  let q' : ColumnGrade n.val B (U-u.val) :=
    ⟨⟨q, by dsimp [n]; omega⟩, by dsimp [n]; omega⟩
  have hlo : (-(offset l)).toNat ≤ j := by rw [hg]; omega
  let j' : Fin (slotCount (offset l) J q'.val.val) :=
    ⟨j - (-(offset l)).toNat, by dsimp [slotCount,q']; omega⟩
  refine ⟨⟨l,⟨q',j'⟩⟩,rfl,?_⟩
  let j'' := (-(offset l)).toNat + (j - (-(offset l)).toNat)
  change Input.mk ((offset l + j'').toNat) q j'' (b+q-q) _ = Input.mk a q j b hjq
  have he : j'' = j := by dsimp [j'']; omega
  simp [he,hg]

/-- Every truncated output satisfying the finite active bounds has a row. -/
theorem row_exists {U B J : ℕ} (u : Fin (U+1)) (e : Fin 4 →₀ ℕ)
    (hx : e 0 < B+J) (hs : e 1 + e 2 ≤ B)
    (hn : (outputTag e).1 ≤ B+(U-u.val)) (hg : -(J : ℤ) ≤ (outputTag e).2) :
    ∃ r : Sigma (@Rows U B J), r.1.1 = u ∧ rowExponent r = e := by
  let n : Fin (B+(U-u.val)+1) := ⟨(outputTag e).1, Nat.lt_succ_of_le hn⟩
  let h : Fin (B+2*J) := ⟨((outputTag e).2+J).toNat, by
    dsimp [outputTag] at hg ⊢
    omega⟩
  let t : Label U B J := ⟨u,n,h⟩
  have hgap : offset t = (outputTag e).2 := by dsimp [offset,t,h]; omega
  let s : Fin (min n.val B+1) := ⟨e 1 + e 2, by dsimp [n,outputTag]; omega⟩
  let l : BlockRow (B+J) (offset t) s.val :=
    ⟨⟨e 2, by rw [hgap]; dsimp [s,outputTag]; omega⟩,
      by
        change e 2 ≤ s.val ∧ 0 ≤ offset t + s.val + e 2
        rw [hgap]
        dsimp [s,outputTag]
        constructor <;> omega⟩
  refine ⟨⟨t,⟨s,l⟩⟩,rfl,?_⟩
  change blockOutput (n := n.val) s.val l = e
  ext v
  fin_cases v <;> simp [blockOutput, l, s, exponent, hgap, n, outputTag]
  omega

/-- A nonzero truncated chart coefficient is represented by the full matrix. -/
theorem coefficient_represented {F : Type*} [Field F] {U B J : ℕ}
    (u : Fin (U+1)) (i : Input) (e : Fin 4 →₀ ℕ)
    (hseed : i.b ≤ U-u.val) (hq : i.q ≤ B) (hj : i.j ≤ J)
    (hcolx : i.a < B+J) (hrowx : e 0 < B+J)
    (hne : (chartMonomial F i).coeff e ≠ 0) :
    ∃ (r : Sigma (@Rows U B J)) (c : Sigma (@Columns U B J)),
      r.1.1 = u ∧ c.1.1 = u ∧ rowExponent r = e ∧ colInput c = i ∧
        matrix F U B J r c = (chartMonomial F i).coeff e := by
  have ht : outputTag e = i.tag := by
    by_contra h
    exact hne (coeff_eq_zero_of_tag_ne i e h)
  let s := e 1 + e 2
  have hs : s ≤ i.q := by
    by_contra! hsq
    apply hne
    have hij := i.hj
    rw [coeff_fixed_output_grade i e s rfl ht, ite_eq_left (by omega),
      Nat.choose_eq_zero_of_lt (by omega : i.q-i.j < s-i.j), Nat.cast_zero, zero_mul]
  have hn : (outputTag e).1 ≤ B+(U-u.val) := by
    rw [ht]
    change i.b + i.q ≤ _
    omega
  have hg : -(J : ℤ) ≤ (outputTag e).2 := by
    rw [ht]
    change -(J : ℤ) ≤ (i.a : ℤ)-i.j
    omega
  obtain ⟨r, hr, hre⟩ := row_exists u e hrowx (hs.trans hq) hn hg
  obtain ⟨c, hc, hce⟩ := column_exists u i hseed hq hj hcolx
  refine ⟨r,c,hr,hc,hre,hce,?_⟩
  change (if r.1.1 = c.1.1 then (chartMonomial F (colInput c)).coeff (rowExponent r) else 0) = _
  rw [ite_eq_left (hr.trans hc.symm), hre, hce]

/-- High-X source columns vanish at every retained output. -/
theorem coeff_zero_below_source_X {F : Type*} [Field F] (i : Input) (e : Fin 4 →₀ ℕ)
    (hx : e 0 < i.a) : (chartMonomial F i).coeff e = 0 := by
  rw [chartMonomial_eq_sum, coeff_sum]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [coeff_sum]
  refine Finset.sum_eq_zero fun l _ ↦ ?_
  rw [coeff_monomial, ite_eq_right]
  intro he
  have he0 := congrArg (fun f : Fin 4 →₀ ℕ ↦ f 0) he
  simp [monomialExponent, exponent] at he0
  omega

end
end PoleFamily
