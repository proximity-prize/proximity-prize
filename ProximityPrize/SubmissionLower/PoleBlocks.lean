import ProximityPrize.SubmissionLower.Fast005

namespace PoleBlocks

noncomputable section

open scoped BigOperators

/-- The two binomial choices are the number of xT and xZ terms. -/
theorem expansion {R : Type*} [CommSemiring R] (x T Z z : R) (a q j b : ℕ) (hjq : j ≤ q) :
    x^a * (z+x*T)^(q-j) * (T+x*Z)^j * z^b =
      ∑ k ∈ Finset.range (q-j+1), ∑ l ∈ Finset.range (j+1),
        x^(a+k+l) * T^(j+k-l) * Z^l * z^(b+q-j-k) *
          ((q-j).choose k : R) * (j.choose l : R) := by
  rw [add_comm z, add_comm T, add_pow (x*T) z, add_pow (x*Z) T]
  conv_lhs => simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  refine Finset.sum_congr rfl fun l hl => ?_
  have hk' := Finset.mem_range.mp hk
  have hl' := Finset.mem_range.mp hl
  have ht : j+k-l = k+(j-l) := by omega
  have hz : b+q-j-k = (q-j-k)+b := by omega
  simp only [mul_pow, ht, hz, pow_add]
  ring

/-- Both binomial choices preserve the joint grade and the abscissa offset. -/
theorem conserved {a q j b k l : ℕ} (hj : j ≤ q) (hk : k ≤ q-j) (hl : l ≤ j) :
    (j+k-l) + l + (b+q-j-k) = b+q ∧
    ((a+k+l : ℕ) : ℤ) - (j+k-l : ℕ) - 2*(l : ℤ) = (a : ℤ) - j := by
  omega

open MvPolynomial

/-- Output variables in order x, T, Z, z. -/
def exponent (a t u b : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 t + Finsupp.single 2 u + Finsupp.single 3 b

def outputTag (e : Fin 4 →₀ ℕ) : ℕ × ℤ :=
  (e 1 + e 2 + e 3, (e 0 : ℤ) - e 1 - 2 * e 2)

structure Input where
  a : ℕ
  q : ℕ
  j : ℕ
  b : ℕ
  hj : j ≤ q

def Input.tag (i : Input) : ℕ × ℤ := (i.b+i.q, (i.a : ℤ)-i.j)

def chartMonomial (F : Type*) [CommSemiring F] (i : Input) : MvPolynomial (Fin 4) F :=
  X 0 ^ i.a * (X 3 + X 0 * X 1)^(i.q-i.j) * (X 1 + X 0 * X 2)^i.j * X 3 ^ i.b

def monomialExponent (i : Input) (k l : ℕ) : Fin 4 →₀ ℕ :=
  exponent (i.a+k+l) (i.j+k-l) l (i.b+i.q-i.j-k)

theorem monomialExponent_injective (i : Input) :
    Function.Injective (fun p : ℕ × ℕ ↦ monomialExponent i p.1 p.2) := by
  rintro ⟨k,l⟩ ⟨k',l'⟩ h
  have hl := congrArg (fun e : Fin 4 →₀ ℕ ↦ e 2) h
  have hk := congrArg (fun e : Fin 4 →₀ ℕ ↦ e 0) h
  simp [monomialExponent, exponent] at hl hk
  exact Prod.ext (by omega) hl

theorem chartMonomial_eq_sum {F : Type*} [CommSemiring F] (i : Input) :
    chartMonomial F i =
      ∑ k ∈ Finset.range (i.q-i.j+1), ∑ l ∈ Finset.range (i.j+1),
        monomial (monomialExponent i k l)
          (((i.q-i.j).choose k : F) * (i.j.choose l : F)) := by
  unfold chartMonomial
  rw [expansion _ _ _ _ _ _ _ _ i.hj]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_assoc, ← map_natCast (C : F →+* MvPolynomial (Fin 4) F) ((i.q-i.j).choose k),
    ← map_natCast (C : F →+* MvPolynomial (Fin 4) F) (i.j.choose l), ← map_mul]
  simp only [X_pow_eq_monomial, monomial_mul_monomial, monomialExponent, exponent, one_mul]
  rw [mul_comm _ (C _), C_mul_monomial, mul_one]

/-- A displayed term's coefficient is its binomial product, since its
abscissa and Z exponents recover the two summation indices. -/
theorem coeff_monomialExponent {F : Type*} [CommSemiring F] (i : Input) {k l : ℕ}
    (hk : k ≤ i.q-i.j) (hl : l ≤ i.j) :
    (chartMonomial F i).coeff (monomialExponent i k l) =
      ((i.q-i.j).choose k : F) * (i.j.choose l : F) := by
  classical
  rw [chartMonomial_eq_sum, coeff_sum, Finset.sum_eq_single k]
  · rw [coeff_sum, Finset.sum_eq_single l]
    · simp
    · intro l' _ hne
      rw [coeff_monomial, ite_eq_right]
      intro he
      have h := monomialExponent_injective i (a₁ := (k,l)) (a₂ := (k,l')) he.symm
      exact hne (congrArg Prod.snd h).symm
    · exact fun h => (h (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))).elim
  · intro k' _ hne
    rw [coeff_sum]
    refine Finset.sum_eq_zero fun l' _ => ?_
    rw [coeff_monomial, ite_eq_right]
    intro he
    have h := monomialExponent_injective i (a₁ := (k,l)) (a₂ := (k',l')) he.symm
    exact hne (congrArg Prod.fst h).symm
  · exact fun h => (h (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))).elim

theorem outputTag_exponent {i : Input} {k l : ℕ} (hk : k ≤ i.q-i.j) (hl : l ≤ i.j) :
    outputTag (exponent (i.a+k+l) (i.j+k-l) l (i.b+i.q-i.j-k)) = i.tag := by
  rcases conserved (a := i.a) (b := i.b) i.hj hk hl with ⟨hg, ho⟩
  unfold outputTag exponent Input.tag
  simp [hg]
  exact_mod_cast ho

theorem coeff_eq_zero_of_tag_ne {F : Type*} [CommSemiring F] (i : Input) (e : Fin 4 →₀ ℕ)
    (hne : outputTag e ≠ i.tag) : (chartMonomial F i).coeff e = 0 := by
  rw [chartMonomial_eq_sum, coeff_sum]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [coeff_sum]
  refine Finset.sum_eq_zero fun l hl => ?_
  have h : outputTag (exponent (i.a+k+l) (i.j+k-l) l (i.b+i.q-i.j-k)) = i.tag :=
    outputTag_exponent (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
      (Nat.le_of_lt_succ (Finset.mem_range.mp hl))
  rw [coeff_monomial, ite_eq_right]
  intro he
  exact hne (he ▸ h)

/-- Any finite selection of rows and columns in the compatible fibers has
rank bounded by the sum of its block-size minima. -/
theorem chart_rank_le_sum_min {F B : Type*} [Field F] [Fintype B]
    {R C : B → Type*} [∀ b, Fintype (R b)] [∀ b, Fintype (C b)]
    (tag : B → ℕ × ℤ) (htag : Function.Injective tag)
    (row : (b : B) → R b → Fin 4 →₀ ℕ) (col : (b : B) → C b → Input)
    (hr : ∀ b r, outputTag (row b r) = tag b) (hc : ∀ b c, (col b c).tag = tag b) :
    (Matrix.of fun (r : Sigma R) (c : Sigma C) ↦
      (chartMonomial F (col c.1 c.2)).coeff (row r.1 r.2)).rank ≤
      ∑ b, min (Fintype.card (R b)) (Fintype.card (C b)) := by
  apply Sol1.C52.rank_le_sum_min_dependent
  intro r c hne
  exact coeff_eq_zero_of_tag_ne _ _ (by rw [hr, hc]; exact fun h => hne (htag h))

private theorem coeff_eq_zero_of_no_term {F : Type*} [CommSemiring F] (i : Input)
    (e : Fin 4 →₀ ℕ)
    (h : ∀ k ≤ i.q-i.j, ∀ l ≤ i.j, monomialExponent i k l ≠ e) :
    (chartMonomial F i).coeff e = 0 := by
  rw [chartMonomial_eq_sum, coeff_sum]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [coeff_sum]
  refine Finset.sum_eq_zero fun l hl => ?_
  rw [coeff_monomial, ite_eq_right]
  exact h k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    l (Nat.le_of_lt_succ (Finset.mem_range.mp hl))

theorem coeff_fixed_output_grade {F : Type*} [CommSemiring F] (i : Input)
    (e : Fin 4 →₀ ℕ) (s : ℕ) (hs : e 1 + e 2 = s) (hg : outputTag e = i.tag) :
    (chartMonomial F i).coeff e =
      if i.j ≤ s then ((i.q-i.j).choose (s-i.j) : F) * (i.j.choose (e 2) : F) else 0 := by
  have hij := i.hj
  have vanish (hbad : ¬ (i.j ≤ s ∧ s ≤ i.q ∧ e 2 ≤ i.j)) :
      (chartMonomial F i).coeff e = 0 := by
    apply coeff_eq_zero_of_no_term
    intro k hk l hl he
    have ht := congrArg (fun e : Fin 4 →₀ ℕ ↦ e 1) he
    have hu := congrArg (fun e : Fin 4 →₀ ℕ ↦ e 2) he
    simp [monomialExponent, exponent] at ht hu
    exact hbad ⟨by omega, by have := i.hj; omega, by omega⟩
  by_cases hjs : i.j ≤ s
  · rw [ite_eq_left hjs]
    by_cases hsq : s ≤ i.q
    · by_cases hlj : e 2 ≤ i.j
      · have he : monomialExponent i (s-i.j) (e 2) = e := by
          have hgrade := congrArg Prod.fst hg
          have hoff := congrArg Prod.snd hg
          dsimp [outputTag, Input.tag] at hgrade hoff
          ext t
          fin_cases t <;> simp [monomialExponent, exponent] <;> omega
        rw [← he, coeff_monomialExponent i (by omega) hlj]
        simp [monomialExponent, exponent]
      · rw [vanish (by omega), Nat.choose_eq_zero_of_lt (by omega : i.j < e 2),
          Nat.cast_zero, mul_zero]
    · rw [vanish (by omega), Nat.choose_eq_zero_of_lt (by omega : i.q-i.j < s-i.j),
        Nat.cast_zero, zero_mul]
  · rw [ite_eq_right hjs, vanish (by omega)]

/-- Stacking dependent row fibers bounds rank by the sum of the fiber ranks. -/
theorem rank_sigma_rows_le_sum {F S C : Type*} [Field F] [Fintype S] [Fintype C]
    {R : S → Type*} [∀ s, Fintype (R s)] (A : Matrix (Sigma R) C F) :
    A.rank ≤ ∑ s, (A.submatrix (Sigma.mk s) id).rank := by
  classical
  let part : S → Matrix (Sigma R) C F := fun s r c ↦ if r.1 = s then A r c else 0
  let M : Matrix (S × Sigma R) C F := fun sr c ↦ part sr.1 sr.2 c
  have hrecover : M.submatrix (fun r ↦ (r.1,r)) id = A := by
    ext r c
    simp [Matrix.submatrix, M, part]
  have hpart (s : S) : (part s).rank ≤ (A.submatrix (Sigma.mk s) id).rank := by
    have hsub : (part s).submatrix (Sigma.mk s) id = A.submatrix (Sigma.mk s) id := by
      ext r c
      simp [Matrix.submatrix, part]
    rw [← hsub]
    apply Sol1.C52.rank_le_row_representatives (part s) (Sigma.mk s)
    rintro ⟨r,i⟩
    by_cases h : r = s
    · subst r
      exact Or.inr ⟨i,rfl⟩
    · left
      funext c
      simp [part,h]
    -- The surviving rows are exactly the true submatrix.
  calc
    A.rank = (M.submatrix (fun r ↦ (r.1,r)) id).rank := by rw [hrecover]
    _ ≤ M.rank := Matrix.rank_submatrix_le _ _ _
    _ ≤ ∑ s, (part s).rank := Matrix.rank_prod_rows_le_sum M
    _ ≤ ∑ s, (A.submatrix (Sigma.mk s) id).rank := Finset.sum_le_sum fun s _ ↦ hpart s

/-- The indices j available at a given grade and offset. -/
def slotCount (g : ℤ) (J s : ℕ) : ℕ :=
  min J s + 1 - (-g).toNat

private def slot {g : ℤ} {J s : ℕ} (u : Fin (slotCount g J s)) : ℕ :=
  (-g).toNat + u.val

private theorem slot_le {g : ℤ} {J s : ℕ} (u : Fin (slotCount g J s)) :
    slot u ≤ min J s := by
  have hu := u.isLt
  unfold slotCount at hu
  unfold slot
  omega

theorem rank_output_grade_le {F R C : Type*} [Field F] [Fintype R] [Fintype C]
    (n : ℕ) (g : ℤ) (J s : ℕ)
    (row : R → Fin 4 →₀ ℕ) (col : C → Input)
    (hr : ∀ r, outputTag (row r) = (n,g)) (hc : ∀ c, (col c).tag = (n,g))
    (hs : ∀ r, row r 1 + row r 2 = s) (hJ : ∀ c, (col c).j ≤ J) :
    (Matrix.of fun r c ↦ (chartMonomial F (col c)).coeff (row r)).rank ≤
      min (slotCount g J s) (Fintype.card R) := by
  classical
  let A : Matrix R C F := Matrix.of fun r c ↦ (chartMonomial F (col c)).coeff (row r)
  let L : Matrix R (Fin (slotCount g J s)) F := Matrix.of fun r u ↦ (slot u).choose (row r 2)
  let H : Matrix (Fin (slotCount g J s)) C F := Matrix.of fun u c ↦
    if (col c).j = slot u then ((col c).q-(col c).j).choose (s-(col c).j) else 0
  have hfactor : A = L * H := by
    ext r c
    rw [Matrix.mul_apply]
    change (chartMonomial F (col c)).coeff (row r) = ∑ u, L r u * H u c
    rw [coeff_fixed_output_grade _ _ s (hs r) ((hr r).trans (hc c).symm)]
    by_cases hj : (col c).j ≤ s
    · have htop : (col c).j ≤ min J s := le_min (hJ c) hj
      have hg := congrArg Prod.snd (hc c)
      dsimp [Input.tag] at hg
      have hlo : (-g).toNat ≤ (col c).j := by omega
      let u : Fin (slotCount g J s) := ⟨(col c).j-(-g).toNat, by
        unfold slotCount
        omega⟩
      have hu : slot u = (col c).j := by dsimp [u,slot]; omega
      rw [ite_eq_left hj, Finset.sum_eq_single u]
      · simp [L,H,hu,mul_comm]
      · intro v _ hne
        have hv : (col c).j ≠ slot v := by
          intro he
          apply hne
          apply Fin.ext
          unfold slot at hu he
          omega
        simp [H,hv]
      · simp
    · rw [ite_eq_right hj]
      symm
      apply Finset.sum_eq_zero
      intro u _
      have hv : (col c).j ≠ slot u := by have := slot_le u; omega
      simp [H,hv]
  change A.rank ≤ _
  refine le_min ?_ A.rank_le_card_height
  rw [hfactor]
  exact (Matrix.rank_mul_le_left _ _).trans (by simpa using L.rank_le_card_width)

theorem rank_normalized_block_le {F C S : Type*} [Field F] [Fintype C] [Fintype S]
    {R : S → Type*} [∀ s, Fintype (R s)]
    (n : ℕ) (g : ℤ) (J M : ℕ) (grade : S → ℕ)
    (row : (s : S) → R s → Fin 4 →₀ ℕ) (col : C → Input)
    (hr : ∀ s r, outputTag (row s r) = (n,g)) (hc : ∀ c, (col c).tag = (n,g))
    (hs : ∀ s r, row s r 1 + row s r 2 = grade s) (hJ : ∀ c, (col c).j ≤ J)
    (hrows : ∀ s, Fintype.card (R s) ≤ ((M : ℤ)-g-grade s).toNat) :
    (Matrix.of fun (r : Sigma R) c ↦ (chartMonomial F (col c)).coeff (row r.1 r.2)).rank ≤
      min (Fintype.card C) (∑ s, min (slotCount g J (grade s)) ((M : ℤ)-g-grade s).toNat) := by
  refine le_min (Matrix.rank_le_card_width _) ((rank_sigma_rows_le_sum _).trans ?_)
  refine Finset.sum_le_sum fun s _ ↦ ?_
  exact (rank_output_grade_le n g J (grade s) (row s) col (hr s) hc (hs s) hJ).trans
    (min_le_min le_rfl (hrows s))

/-- Input grades are constrained both by the seed degree and by the source box. -/
abbrev ColumnGrade (n B active : ℕ) :=
  {q : Fin (min n B+1) // n-active ≤ q.val}

abbrev BlockColumn (n B active : ℕ) (g : ℤ) (J : ℕ) :=
  (q : ColumnGrade n B active) × Fin (slotCount g J q.val.val)

abbrev BlockRow (M : ℕ) (g : ℤ) (s : ℕ) :=
  {l : Fin ((M : ℤ)-g-s).toNat // l.val ≤ s ∧ 0 ≤ g+s+l.val}

def blockInput {n B active : ℕ} {g : ℤ} {J : ℕ} (c : BlockColumn n B active g J) : Input :=
  let j := slot c.2
  ⟨(g+j).toNat, c.1.val.val, j, n-c.1.val.val, (slot_le c.2).trans (min_le_right _ _)⟩

def blockOutput {M n : ℕ} {g : ℤ} (s : ℕ) (r : BlockRow M g s) : Fin 4 →₀ ℕ :=
  exponent (g+s+r.val.val).toNat (s-r.val.val) r.val.val (n-s)

/-- The concrete finite normalized block has one column slot per admissible
input (q,j), and each output grade has at most M-g-s rows. -/
theorem rank_concrete_block_le {F : Type*} [Field F] (M n B active J : ℕ) (g : ℤ) :
    (Matrix.of fun (r : (s : Fin (min n B+1)) × BlockRow M g s.val)
      (c : BlockColumn n B active g J) ↦
        (chartMonomial F (blockInput c)).coeff (blockOutput (n := n) r.1.val r.2)).rank ≤
      min (∑ q : ColumnGrade n B active, slotCount g J q.val.val)
        (∑ s : Fin (min n B+1), min (slotCount g J s.val) ((M : ℤ)-g-s.val).toNat) := by
  have hcol : Fintype.card (BlockColumn n B active g J) =
      ∑ q : ColumnGrade n B active, slotCount g J q.val.val := by
    simp [Fintype.card_sigma]
  rw [← hcol]
  apply rank_normalized_block_le n g J M Fin.val (fun s ↦ blockOutput s.val) blockInput
  · intro s r
    have h := s.isLt
    have hr := r.property.1
    have hx := r.property.2
    simp [blockOutput, outputTag, exponent]
    constructor <;> omega
  · intro c
    have hq := c.1.val.isLt
    have hslot : (-g).toNat ≤ slot c.2 := by simp [slot]
    simp [blockInput, Input.tag]
    constructor <;> omega
  · intro s r
    have hr := r.property.1
    simp [blockOutput, exponent]
    omega
  · intro c
    exact (slot_le c.2).trans (min_le_left _ _)
  · intro s
    simpa using (Fintype.card_le_of_injective Subtype.val
      (Subtype.val_injective : Function.Injective (Subtype.val : BlockRow M g s.val → _)))

end
end PoleBlocks
