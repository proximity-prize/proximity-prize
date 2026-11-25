import ProximityPrize.SubmissionLower.PortHighBase
set_option Elab.async false
set_option autoImplicit true
section
namespace CJ0
noncomputable section
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
end
end CJ0
end
section
namespace CJ0
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark
open K1_14_6 (occupancy)
open P0_10 (incidence_arithmetic)
end
end CJ0
end
section
namespace CJ0
noncomputable section
open Finset MvPolynomial
open scoped Polynomial BigOperators
open K1_14_6 (curve_degree_nat)
end
end CJ0
end
section
namespace CJ0
noncomputable section
open Polynomial PolynomialDifferential Finset
open scoped BigOperators
def c1 : Prop :=
  ∀ A s cut, ShapeOK s → s.m ≤ s.m*A - N*s.B → cut ≤ s.B+1 → SilentTail s cut →
    originRank A s ≤ prefixRank s cut
def c2 : Prop :=
  ∀ A s, ShapeOK s → s.m ≤ s.m*A - N*s.B → ∀ w : Node → K,
    stackRank A s w ≤ n * originRank A s
end
end CJ0
end
section
namespace CJ0_1
noncomputable section
open CJ0 (Jet blockEntry)
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
abbrev LocalExponent := LocalVariable 2 →₀ ℕ
def rowJet (e : LocalExponent) : Jet :=
  ⟨e (localY (1 : Fin 2)), e (localY (0 : Fin 2)), e (localE 2)⟩
def rowBalance (e : LocalExponent) : ℤ :=
  (e (localT 2) : ℤ) - (rowJet e).a - (rowJet e).v
def colBalance (x : ℕ) (j : Jet) : ℤ := (x : ℤ) - j.v
private def exponent (t h d l : ℕ) : LocalExponent :=
  Finsupp.single (localT 2) t + Finsupp.single (localE 2) h +
    Finsupp.single (localY (0 : Fin 2)) d + Finsupp.single (localY (1 : Fin 2)) l
private theorem exponent_eq_iff (t h d l : ℕ) (e : LocalExponent) :
    exponent t h d l = e ↔
      t = e (localT 2) ∧ h = (rowJet e).a ∧ d = (rowJet e).b ∧ l = (rowJet e).c := by
  classical
  constructor
  · intro he
    have atVar (v : LocalVariable 2) := DFunLike.congr_fun he v
    exact ⟨by simpa [exponent, localT, localE, localAux, localY] using atVar (localT 2),
      by simpa [exponent, rowJet, Jet.a, localT, localE, localAux, localY] using atVar (localE 2),
      by simpa [exponent, rowJet, Jet.b, localT, localE, localAux, localY] using
        atVar (localY (0 : Fin 2)),
      by simpa [exponent, rowJet, Jet.c, localT, localE, localAux, localY] using
        atVar (localY (1 : Fin 2))⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    ext v
    rcases v with _ | (_ | j)
    · simp [exponent, localT, localE, localAux, localY]
    · simp [exponent, rowJet, Jet.a, localT, localE, localAux, localY]
    · fin_cases j <;> simp [exponent, rowJet, Jet.b, Jet.c, localT, localE, localAux, localY]
variable {F : Type*} [CommRing F]
private theorem origin_substitution (x a b c : ℕ) :
    unscaledLocalSubstitution 2 (0 : F) 0 (sourceMonomial x a ![b,c]) =
      ∑ h ∈ Finset.range (a+1), ∑ j ∈ Finset.range (a-h+1),
        monomial (exponent (x+h+j+2*(a-h-j)) h (b+j) (c+(a-h-j)))
          ((-1 : F)^(a-h-j) * (a.choose h : F) * ((a-h).choose j : F)) := by
  classical
  let localX : LocalPolynomial F 2 := MvPolynomial.X (localT 2)
  let hiddenTerm : LocalPolynomial F 2 := localX * MvPolynomial.X (localE 2)
  let jetOne : LocalPolynomial F 2 := MvPolynomial.X (localY (0 : Fin 2))
  let jetTwo : LocalPolynomial F 2 := MvPolynomial.X (localY (1 : Fin 2))
  let firstTerm := localX * jetOne
  let secondTerm := -(localX^2 * jetTwo)
  have h₀ : unscaledLocalSubstitution 2 (0 : F) 0 (MvPolynomial.X (some 0)) = hiddenTerm + (firstTerm + secondTerm) := by
    simp [localCorrection, Fin.sum_univ_two, hiddenTerm, firstTerm, secondTerm, localX, jetOne, jetTwo]
    ac_rfl
  rw [sourceMonomial, Fin.prod_univ_two, map_mul, map_mul, map_mul,
    map_pow, map_pow, map_pow, map_pow, h₀]
  simp only [unscaledLocalSubstitution_X, unscaledLocalSubstitution_Y_succ, C_0, zero_add,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  change localX^x * (hiddenTerm+(firstTerm+secondTerm))^a * (jetOne^b*jetTwo^c) = _
  rw [add_pow hiddenTerm (firstTerm+secondTerm), Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [add_pow firstTerm secondTerm]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hW : secondTerm = monomial (Finsupp.single (localT 2) 2 +
      Finsupp.single (localY (1 : Fin 2)) 1) (-1) := by
    change -(MvPolynomial.X (localT 2)^2 * MvPolynomial.X (localY (1 : Fin 2))) = _
    rw [ X_pow_eq_monomial]
    simp only [MvPolynomial.X, monomial_mul_monomial, one_mul, map_neg]
  have hE : hiddenTerm = monomial (Finsupp.single (localT 2) 1 +
      Finsupp.single (localE 2) 1) 1 := by simp [hiddenTerm, localX, MvPolynomial.X]
  have hV : firstTerm = monomial (Finsupp.single (localT 2) 1 +
      Finsupp.single (localY (0 : Fin 2)) 1) 1 := by simp [firstTerm, localX, jetOne, MvPolynomial.X]
  have hcast (n : ℕ) : (n : LocalPolynomial F 2) = monomial 0 (n : F) := by
    rw [monomial_zero', map_natCast]
  rw [hE, hV, hW]
  simp only [localX, jetOne, jetTwo, X_pow_eq_monomial, monomial_pow,
    hcast, monomial_mul_monomial, one_mul, mul_one, one_pow]
  apply congrArg₂ (fun a b => (monomial a b : LocalPolynomial F 2))
  · apply Finsupp.ext
    intro v
    rcases v with _ | (_ | u)
    · simp [exponent, localT, localE, localAux, localY, Nat.mul_comm, Nat.add_assoc]
    · simp [exponent, localT, localE, localAux, localY]
    · fin_cases u <;>
        simp [exponent, localT, localE, localAux, localY, Nat.add_comm]
  · ring
theorem origin_coefficient (x : ℕ) (j : Jet) (e : LocalExponent) :
    (unscaledLocalSubstitution 2 (0 : ZMod CJ0.p) 0
       (sourceMonomial x j.a ![j.b,j.c])).coeff e =
      if rowBalance e = colBalance x j then blockEntry (rowJet e) j else 0 := by
  classical
  let r := rowJet e
  let P : Prop := rowBalance e = colBalance x j ∧
    (j.b ≤ r.b ∧ j.c ≤ r.c ∧ r.a + (r.b-j.b) + (r.c-j.c) = j.a)
  have hexp (h u : ℕ) (hh : h ≤ j.a) (hu : u ≤ j.a-h) :
      exponent (x+h+u+2*(j.a-h-u)) h (j.b+u) (j.c+(j.a-h-u)) = e ↔
        P ∧ h = r.a ∧ u = r.b-j.b := by
    rw [exponent_eq_iff]
    change (x+h+u+2*(j.a-h-u) = e (localT 2) ∧
      h = r.a ∧ j.b+u = r.b ∧ j.c+(j.a-h-u) = r.c) ↔
      ((e (localT 2) : ℤ) - r.a - (r.b+2*r.c : ℕ) =
       (x : ℤ) - (j.b+2*j.c : ℕ) ∧
         (j.b ≤ r.b ∧ j.c ≤ r.c ∧ r.a + (r.b-j.b) + (r.c-j.c) = j.a)) ∧
       h = r.a ∧ u = r.b-j.b
    omega
  rw [origin_substitution]
  simp_rw [coeff_sum, coeff_monomial]
  by_cases hp : P
  · obtain ⟨hg, hb, hc, ha⟩ := hp
    have hh : r.a ≤ j.a := by omega
    have hu : r.b-j.b ≤ j.a-r.a := by omega
    rw [Finset.sum_eq_single_of_mem r.a (Finset.mem_range.mpr (by omega))]
    · rw [Finset.sum_eq_single_of_mem (r.b-j.b) (Finset.mem_range.mpr (by omega))]
      · rw [ite_eq_left ((hexp _ _ hh hu).2 ⟨⟨hg, hb, hc, ha⟩, rfl, rfl⟩), ite_eq_left hg]
        change _ = blockEntry r j
        rw [blockEntry, ite_eq_left ⟨hb, hc, ha⟩, show j.a-r.a-(r.b-j.b) = r.c-j.c by omega]
      · intro u hmem hne
        rw [ite_eq_right (fun he => hne ((hexp _ _ hh (Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem))).1 he).2.2)]
    · intro h hmem hne
      apply Finset.sum_eq_zero
      intro u humem
      rw [ite_eq_right (fun he => hne ((hexp _ _ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem))
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp humem))).1 he).2.1)]
  · have hz := fun h u (hh : h ≤ j.a) (hu : u ≤ j.a-h) he =>
      hp ((hexp h u hh hu).1 he).1
    have hzero : (if rowBalance e = colBalance x j then blockEntry r j else 0) = 0 := by
      split
      · rename_i hg
        exact ite_eq_right (fun hb => hp ⟨hg, hb⟩)
      · rfl
    rw [hzero]
    apply Finset.sum_eq_zero
    intro h hmem
    apply Finset.sum_eq_zero
    intro u humem
    rw [ite_eq_right (hz h u (Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem)) (Nat.lt_succ_iff.mp (Finset.mem_range.mp humem)))]
end
end CJ0_1
end
section
namespace CJ0_1
noncomputable section
open scoped BigOperators Matrix
theorem rank_blockDiagonal_le {F I : Type*} [Field F] [Fintype I]
    {R C : I → Type*} [∀ i, Fintype (C i)] [DecidableEq I]
    (M : ∀ i, Matrix (R i) (C i) F) :
    (Matrix.blockDiagonal' M).rank ≤ ∑ i, (M i).rank := by
  let Φ := (Matrix.blockDiagonal' M).mulVecLin
  let φ := fun i => (M i).mulVecLin
  let project : Φ.range →ₗ[F] ∀ i, (φ i).range :=
    { toFun y i := ⟨fun r => y.val ⟨i,r⟩, by
        obtain ⟨v, hv⟩ := y.property
        refine ⟨fun c => v ⟨i,c⟩, ?_⟩
        rw [← hv]
        funext r
        change (∑ c : C i, M i r c * v ⟨i,c⟩) =
          ∑ j : Sigma C, Matrix.blockDiagonal' M ⟨i,r⟩ j * v j
        rw [← Finset.univ_sigma_univ, Finset.sum_sigma, Finset.sum_eq_single i]
        · simp [Matrix.blockDiagonal'_apply_eq]
        · intro j _ hji
          apply Finset.sum_eq_zero
          intro c _
          rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hji), zero_mul]
        · simp⟩
      map_add' x y := by ext i r; rfl
      map_smul' t x := by ext i r; rfl }
  have hinj : Function.Injective project := by
    intro x y h
    apply Subtype.ext
    funext ⟨i,r⟩
    exact congrFun (congrArg Subtype.val (congrFun h i)) r
  change Module.finrank F Φ.range ≤ ∑ i, Module.finrank F (φ i).range
  exact (LinearMap.finrank_le_finrank_of_injective hinj).trans_eq
    (Module.finrank_pi_fintype F)
end
end CJ0_1
end
section
namespace CJ0_1
noncomputable section
open CJ0 (Source ShapeOK SilentTail Jet ColumnIndex column blockRows blockCols blockMatrix
  blockEntry prefixRank p)
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators Matrix
local instance : Fact (Nat.Prime p) := ⟨KoalaBear.is_prime⟩
abbrev OriginRow (s : Source) := Unit × LowContactIndex 2 s.m
abbrev OriginCol (A : ℕ) (s : Source) := ColumnIndex A s
private def origin (A : ℕ) (s : Source) : Matrix (OriginRow s) (OriginCol A s) (ZMod p) :=
  localConstraintMatrix s.m (fun _ : Unit => 0) (fun _ => 0) (column A s)
private theorem origin_entry {A s} (r : OriginRow s) (j : OriginCol A s) :
    origin A s r j =
      if rowBalance r.2.val = colBalance j.2.val j.1.val then
        blockEntry (rowJet r.2.val) j.1.val else 0 := by
  rw [origin, localConstraintMatrix_apply, SourceColumn.polynomial_eq_sourceMonomial]
  exact origin_coefficient j.2.val j.1.val r.2.val
abbrev BlockIndex (s : Source) (cut : ℕ) := (q : Fin cut) × Fin (s.m+s.J-q.val)
private def balance {s cut} (i : BlockIndex s cut) : ℤ := (i.2.val : ℤ) - s.J
private structure InPrefix (s : Source) (cut q : ℕ) (g : ℤ) : Prop where
  grade : q < cut
  lower : -(s.J : ℤ) ≤ g
  upper : g + q < (s.m : ℤ)
private def blockIndex {s cut q g} (h : InPrefix s cut q g) : BlockIndex s cut :=
  ⟨⟨q, h.grade⟩, ⟨(g + s.J).toNat, by
    change (g + s.J).toNat < s.m+s.J-q
    have := h.lower
    have := h.upper
    omega⟩⟩
private theorem balance_blockIndex {s cut q g} (h : InPrefix s cut q g) :
    balance (blockIndex h) = g := by
  have := h.lower
  simp only [balance, blockIndex]
  omega
private theorem blockIndex_ext {s cut} {i j : BlockIndex s cut}
    (hq : i.1.val = j.1.val) (hg : balance i = balance j) : i = j := by
  rcases i with ⟨qi, ui⟩
  rcases j with ⟨qj, uj⟩
  have hgrade : qi = qj := Fin.ext hq
  subst qj
  have hoffset : ui = uj := Fin.ext (by simp only [balance] at hg; omega)
  subst uj
  rfl
private theorem row_mem {s : Source} (r : OriginRow s) :
    rowJet r.2.val ∈ blockRows s.m (rowJet r.2.val).q (rowBalance r.2.val) := by
  let j := rowJet r.2.val
  have hcontact := r.2.property
  rw [localContactOrder_eq] at hcontact
  change r.2.val (localT 2) + 2*j.a < s.m at hcontact
  have hweight : rowBalance r.2.val + (j.v : ℤ) + 3*(j.a : ℤ) =
      (r.2.val (localT 2) : ℤ) + 2*(j.a : ℤ) := by
    change (r.2.val (localT 2) : ℤ) - j.a - j.v + j.v + 3*j.a = _
    omega
  refine Finset.mem_filter.mpr ⟨?_, by rw [hweight]; omega⟩
  change j ∈ (Finset.range (j.q+1)).sigma
    (fun c => (Finset.range (j.q-c+1)).sigma fun b => {j.q-(b+c)})
  generalize j = i
  rcases i with ⟨c,b,a⟩
  simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_singleton, Jet.q, Jet.a, Jet.b, Jet.c]
  omega
private theorem origin_support {A s cut} (hs : ShapeOK s) (htail : SilentTail s cut)
    (r : OriginRow s) (j : OriginCol A s) (hn : origin A s r j ≠ 0) :
    (rowJet r.2.val).q = j.1.val.q ∧ rowBalance r.2.val = colBalance j.2.val j.1.val ∧
      InPrefix s cut j.1.val.q (colBalance j.2.val j.1.val) := by
  let i := rowJet r.2.val
  let c := j.1.val
  have hg : rowBalance r.2.val = colBalance j.2.val c := by
    by_contra hn'
    exact hn (by rw [origin_entry, ite_eq_right hn'])
  have hbc : c.b ≤ i.b ∧ c.c ≤ i.c ∧ i.a + (i.b-c.b) + (i.c-c.c) = c.a := by
    by_contra hn'
    exact hn (by rw [origin_entry, ite_eq_left hg, blockEntry, ite_eq_right hn'])
  obtain ⟨hb, hc, ha⟩ := hbc
  have hq : i.q = c.q := by simp only [Jet.q]; omega
  have hcontact := r.2.property
  rw [localContactOrder_eq] at hcontact
  change r.2.val (localT 2) + 2*i.a < s.m at hcontact
  have heq : (r.2.val (localT 2) : ℤ) - i.a - (i.b + 2*i.c : ℕ) =
      (j.2.val : ℤ) - (c.b + 2*c.c : ℕ) := hg
  have hsmall : c.a < s.m := by omega
  have hgrade : c.q < cut := by
    by_contra! hbig
    exact (Nat.not_le_of_gt hsmall) (htail c j.1.property hbig)
  have hv := (hs.support c j.1.property).2.1
  refine ⟨hq, hg, hgrade, ?_, ?_⟩
  · change -(s.J : ℤ) ≤ (j.2.val : ℤ) - c.v
    change c.v ≤ s.J at hv
    omega
  · change (j.2.val : ℤ) - (c.b+2*c.c : ℕ) + (c.a+c.b+c.c : ℕ) < (s.m : ℤ)
    omega
private def activeRows (A : ℕ) (s : Source) : Finset (OriginRow s) :=
  localConstraintSupportedRows s.m (fun _ : Unit => (0 : ZMod p)) (fun _ => 0) (column A s)
private def activeCols (A : ℕ) (s : Source) : Finset (OriginCol A s) := by
  classical
  exact Finset.univ.filter fun j => ∃ r, origin A s r j ≠ 0
private theorem active_row_inPrefix {A s cut} (hs : ShapeOK s) (htail : SilentTail s cut)
    (r : activeRows A s) :
    InPrefix s cut (rowJet r.val.2.val).q (rowBalance r.val.2.val) := by
  obtain ⟨j, hj⟩ := (mem_localConstraintSupportedRows_iff _ _ _ _ _).mp r.property
  obtain ⟨hq, hg, h⟩ := origin_support hs htail r.val j hj
  rwa [hq, hg]
private theorem active_col_inPrefix {A s cut} (hs : ShapeOK s) (htail : SilentTail s cut)
    (j : activeCols A s) :
    InPrefix s cut j.val.1.val.q (colBalance j.val.2.val j.val.1.val) := by
  classical
  obtain ⟨r, hr⟩ := (Finset.mem_filter.mp j.property).2
  exact (origin_support hs htail r j.val hr).2.2
private abbrev BlockRow {s cut} (i : BlockIndex s cut) : Type := ↥(blockRows s.m i.1.val (balance i))
private abbrev BlockCol {s cut} (i : BlockIndex s cut) : Type := ↥(blockCols s i.1.val (balance i))
private def rowRep {A s cut} (hs : ShapeOK s) (htail : SilentTail s cut) (r : activeRows A s) :
    Sigma (BlockRow (s := s) (cut := cut)) :=
  let h := active_row_inPrefix hs htail r
  ⟨blockIndex h, ⟨rowJet r.val.2.val, by
    change rowJet r.val.2.val ∈
      blockRows s.m (rowJet r.val.2.val).q (balance (blockIndex h))
    rw [balance_blockIndex]
    exact row_mem r.val⟩⟩
private def colRep {A s cut} (hs : ShapeOK s) (htail : SilentTail s cut) (j : activeCols A s) :
    Sigma (BlockCol (s := s) (cut := cut)) :=
  let h := active_col_inPrefix hs htail j
  ⟨blockIndex h, ⟨j.val.1.val, by
    apply Finset.mem_filter.mpr
    refine ⟨j.val.1.property, rfl, ?_⟩
    rw [balance_blockIndex]
    simp [colBalance]⟩⟩
private def packet (s : Source) (cut : ℕ) :
    Matrix (Sigma (BlockRow (s := s) (cut := cut))) (Sigma (BlockCol (s := s) (cut := cut)))
      (ZMod p) :=
  Matrix.blockDiagonal' fun i => blockMatrix s i.1.val (balance i)
private theorem packet_entry {s cut} (r : Sigma (BlockRow (s := s) (cut := cut)))
    (c : Sigma (BlockCol (s := s) (cut := cut))) (h : r.1 = c.1) :
    packet s cut r c = blockEntry r.2.val c.2.val := by
  rcases r with ⟨i,r⟩
  rcases c with ⟨j,c⟩
  change i = j at h
  subst j
  exact Matrix.blockDiagonal'_apply_eq _ _ _ _
private theorem origin_submatrix {A s cut} (hs : ShapeOK s) (htail : SilentTail s cut) :
    (origin A s).submatrix (Subtype.val : activeRows A s → _) (Subtype.val : activeCols A s → _) =
      (packet s cut).submatrix (rowRep hs htail) (colRep hs htail) := by
  ext r c
  let i := rowRep hs htail r
  let j := colRep hs htail c
  change origin A s r.val c.val = packet s cut i j
  have hr : balance i.1 = rowBalance r.val.2.val :=
    balance_blockIndex (active_row_inPrefix hs htail r)
  have hc : balance j.1 = colBalance c.val.2.val c.val.1.val :=
    balance_blockIndex (active_col_inPrefix hs htail c)
  by_cases hij : i.1 = j.1
  · rw [packet_entry i j hij, origin_entry, ite_eq_left (hr.symm.trans ((congrArg balance hij).trans hc))]
    rfl
  · have hz : origin A s r.val c.val = 0 := by
      by_contra hn
      obtain ⟨hq, hg, _⟩ := origin_support hs htail r.val c.val hn
      exact hij (blockIndex_ext hq (hr.trans (hg.trans hc.symm)))
    rw [hz]
    exact (Matrix.blockDiagonal'_apply_ne _ _ _ hij).symm
private theorem origin_rank_eq_supported (A : ℕ) (s : Source) :
    (origin A s).rank =
      ((origin A s).submatrix (Subtype.val : activeRows A s → _) id).rank := by
  symm
  apply Matrix.rank_submatrix_eq_of_ne_zero_mem_range
  exact localConstraintMatrix_ne_zero_mem_range _ _ _ _
private theorem supported_rank_le (A : ℕ) (s : Source) :
    ((origin A s).submatrix (Subtype.val : activeRows A s → _) id).rank ≤
      ((origin A s).submatrix (Subtype.val : activeRows A s → _)
        (Subtype.val : activeCols A s → _)).rank := by
  classical
  apply Sol1.C52.rank_le_col_representatives
  intro j
  by_cases hj : j ∈ activeCols A s
  · exact Or.inr ⟨⟨j, hj⟩, rfl⟩
  · left
    funext r
    change origin A s r.val j = 0
    by_contra hn
    exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, r.val, hn⟩)
private theorem packet_rank_le (s : Source) (cut : ℕ) : (packet s cut).rank ≤ prefixRank s cut := by
  calc
    (packet s cut).rank ≤ ∑ i : BlockIndex s cut, (blockMatrix s i.1.val (balance i)).rank :=
      rank_blockDiagonal_le (fun i : BlockIndex s cut => blockMatrix s i.1.val (balance i))
    _ = prefixRank s cut := by
      rw [Fintype.sum_sigma]
      simp only [prefixRank, balance, Finset.sum_fin_eq_sum_range]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [dite_eq_left (Finset.mem_range.mp hq)]
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [dite_eq_left (Finset.mem_range.mp hu)]
      rfl
theorem proof : CJ0.c1 := by
  intro A s cut hs _ _ htail
  change (origin A s).rank ≤ prefixRank s cut
  rw [origin_rank_eq_supported]
  apply (supported_rank_le A s).trans
  rw [origin_submatrix hs htail]
  exact (Matrix.rank_submatrix_le _ _ _).trans (packet_rank_le s cut)
end
end CJ0_1
end
section
namespace CJ0_2
noncomputable section
open CJ0 MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
private theorem lower_mem {s : Source} (hs : ShapeOK s) {c b a : ℕ}
    (h : (⟨c, b, a⟩ : Jet) ∈ s.E) {a' : ℕ} (ha : a' ≤ a) :
    (⟨c, b, a'⟩ : Jet) ∈ s.E := by
  induction a with
  | zero =>
    rw [Nat.eq_zero_of_le_zero ha]
    exact h
  | succ a ih =>
    rcases Nat.eq_or_lt_of_le ha with hEq | hlt
    · rw [hEq]
      exact h
    · exact ih (hs.lower _ h (Nat.succ_pos a)) (Nat.le_of_lt_succ hlt)
private def sourceSpan (F : Type*) [Field F] (A : ℕ) (s : Source) :
    Submodule F (DifferentialPolynomial F 2) :=
  Submodule.span F (Set.range fun i : ColumnIndex A s => (column A s i).polynomial)
private theorem column_mem_sourceSpan {F : Type*} [Field F] {A : ℕ} {s : Source}
    (i : ColumnIndex A s) : (column A s i).polynomial ∈ sourceSpan F A s :=
  Submodule.subset_span (Set.mem_range_self i)
private theorem translated_column_mem {F : Type*} [Field F] {A : ℕ} {s : Source}
    (hs : ShapeOK s) (center received : F) (i : ColumnIndex A s) :
    globalPointTranslation center received (column A s i).polynomial ∈ sourceSpan F A s := by
  classical
  let col := column A s i
  change globalPointTranslation center received col.polynomial ∈ sourceSpan F A s
  rw [SourceColumn.polynomial_eq_sourceMonomial]
  simp only [sourceMonomial, map_mul, map_pow, map_prod, globalPointTranslation_X,
    globalPointTranslation_Y_zero, globalPointTranslation_Y_succ]
  rw [add_comm (MvPolynomial.C center), add_comm (MvPolynomial.C received), add_pow, add_pow,
    Finset.sum_mul, Finset.sum_mul]
  apply Submodule.sum_mem
  intro x hx
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Submodule.sum_mem
  intro a ha
  have hx' : x ≤ i.2.val := Nat.le_of_lt_succ (Finset.mem_range.mp hx)
  have ha' : a ≤ i.1.val.a := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
  let j : Jet := ⟨i.1.val.c, i.1.val.b, a⟩
  have hj : j ∈ s.E := by
    rcases i with ⟨⟨⟨c, b, a₀⟩, hi⟩, i⟩
    exact lower_mem hs hi ha'
  have hq : j.q ≤ i.1.val.q :=
    Nat.add_le_add_right (Nat.add_le_add_right ha' _) _
  have hwidth : width A s i.1.val ≤ width A s j :=
    Nat.add_le_add_right (Nat.sub_le_sub_left (Nat.mul_le_mul_left N hq) _) _
  let l : ColumnIndex A s := ⟨⟨j, hj⟩, ⟨x, (hx'.trans_lt i.2.isLt).trans_le hwidth⟩⟩
  let coeff : F := center ^ (col.x - x) * (col.x.choose x : F) *
    received ^ (col.y₀ - a) * (col.y₀.choose a : F)
  have hterm :
      (MvPolynomial.X none ^ x * MvPolynomial.C center ^ (col.x - x) * (col.x.choose x : DifferentialPolynomial F 2) *
        (MvPolynomial.X (some 0) ^ a * MvPolynomial.C received ^ (col.y₀ - a) *
          (col.y₀.choose a : DifferentialPolynomial F 2))) *
        (∏ j, MvPolynomial.X (some j.succ) ^ col.higher j) =
      coeff • (column A s l).polynomial := by
    rw [smul_eq_C_mul, SourceColumn.polynomial_eq_sourceMonomial]
    change _ = MvPolynomial.C coeff * sourceMonomial x a col.higher
    simp only [coeff, sourceMonomial, map_mul, map_pow, map_natCast]
    ac_rfl
  rw [hterm]
  exact (sourceSpan F A s).smul_mem coeff (column_mem_sourceSpan l)
private def pointMatrix {F : Type*} [Field F] (A : ℕ) (s : Source)
    (center received : F) : Matrix (LowContactIndex 2 s.m) (ColumnIndex A s) F :=
  fun row i => localConstraintCoordinatesAt s.m center received (column A s i).polynomial row
private theorem point_rank_le_origin {F : Type*} [Field F] {A : ℕ} {s : Source}
    (hs : ShapeOK s) (center received : F) :
    (pointMatrix A s center received).rank ≤ (pointMatrix A s (0 : F) 0).rank := by
  classical
  let L := localConstraintCoordinatesAt (R := F) (d := 2) s.m 0 0
  have hmap : (sourceSpan F A s).map L =
      Submodule.span F (Set.range (pointMatrix A s (0 : F) 0).col) := by
    rw [sourceSpan, Submodule.map_span, ← Set.range_comp]
    rfl
  have hspan : Submodule.span F (Set.range (pointMatrix A s center received).col) ≤
      Submodule.span F (Set.range (pointMatrix A s (0 : F) 0).col) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [← hmap]
    exact ⟨globalPointTranslation center received (column A s i).polynomial,
      translated_column_mem hs center received i,
      (Sol1.C42.coordinates_translation s.m center received (column A s i).polynomial).symm⟩
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  have := FiniteDimensional.span_of_finite (K := F)
    (Set.finite_range (pointMatrix A s (0 : F) 0).col)
  exact Submodule.finrank_mono hspan
private theorem constraint_matrix_map {R S ι κ : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (m : ℕ) (centers received : ι → R) (cols : κ → SourceColumn 2) :
    (localConstraintMatrix m centers received cols).map φ =
      localConstraintMatrix m (fun i => φ (centers i)) (fun i => φ (received i)) cols := by
  ext row j
  simp only [Matrix.map_apply, localConstraintMatrix_apply]
  rw [← MvPolynomial.coeff_map, map_unscaledLocalSubstitution]
  simp [SourceColumn.polynomial]
set_option maxHeartbeats 800000 in
private theorem native_origin_rank (A : ℕ) (s : Source) :
    (pointMatrix A s (0 : K) 0).rank ≤ originRank A s := by
  let φ : KoalaBear.Field →+* K := algebraMap KoalaBear.Field K
  let P := localConstraintMatrix s.m
    (fun _ : Unit => (0 : KoalaBear.Field)) (fun _ => 0) (column A s)
  let row : LowContactIndex 2 s.m → Unit × LowContactIndex 2 s.m := fun r => ((), r)
  have hmap : P.map φ =
      localConstraintMatrix s.m (fun _ : Unit => (0 : K)) (fun _ => 0) (column A s) := by
    simpa only [map_zero] using
      constraint_matrix_map φ s.m (fun _ : Unit => (0 : KoalaBear.Field)) (fun _ => 0) (column A s)
  calc
    _ = ((P.map φ).submatrix row (id : ColumnIndex A s → ColumnIndex A s)).rank := by
      rw [hmap]
      rfl
    _ ≤ (P.map φ).rank := Matrix.rank_submatrix_le _ _ _
    _ ≤ P.rank := Matrix.rank_map_le φ P
    _ = _ := rfl
private theorem sum_const_card {ι : Type*} [Fintype ι] (r : ℕ) :
    (∑ _ : ι, r) = Fintype.card ι * r := by
  simp
theorem proof : CJ0.c2 := by
  intro A s hs _ w
  let M := localConstraintMatrix s.m (fun i => node i) w (column A s)
  change M.rank ≤ n * originRank A s
  apply (Matrix.rank_prod_rows_le_sum M).trans
  calc
    _ ≤ ∑ _ : Node, originRank A s := by
      apply Finset.sum_le_sum
      intro i _
      change (pointMatrix A s (node i) (w i)).rank ≤ originRank A s
      exact (point_rank_le_origin hs (node i) (w i)).trans (native_origin_rank A s)
    _ = _ := by rw [sum_const_card, ProximityPrize.Benchmark.IRSProfile.card_index]
end
end CJ0_2
end
section
namespace CJ0_3
noncomputable section
open CJ0 PolynomialDifferential
open scoped BigOperators Polynomial
abbrev Equation := DifferentialPolynomial K 2
def centerMap : (Polynomial K) →+* Geo :=
  (algebraMap FX Geo).comp (algebraMap (Polynomial K) FX)
def lifted (G : Equation) : DifferentialPolynomial Geo 2 :=
  MvPolynomial.map embed G
def initial (G : Equation) : InitialRing 2 :=
  initialJetEquation center (lifted G)
def initialSep (G : Equation) : InitialRing 2 :=
  initialJetSeparant center (lifted G)
def nativeJet (f : (Polynomial K)) : Fin 3 → Geo :=
  polynomialJet center (f.map embed)
structure FactorFamily (Q : Equation) where
  count : ℕ
  source : Fin count → Equation
  equation : Fin count → InitialRing 2
  source_irreducible : ∀ i, Irreducible (source i)
  source_dvd : ∀ i, source i ∣ Q
  irreducible : ∀ i, Irreducible (equation i)
  component : ∀ i, equation i ∣ initial (source i)
  regular : ∀ i, ¬ equation i ∣ initialSep (source i)
  product_dvd : (∏ i, equation i) ∣ initial Q
  covers : ∀ f : (Polynomial K), RegularRoot Q f →
    ∃ i, differentialSpecialization (source i) f = 0 ∧
      MvPolynomial.eval (nativeJet f) (equation i) = 0 ∧
      MvPolynomial.eval (nativeJet f) (initialSep (source i)) ≠ 0
end
end CJ0_3
end
section
namespace CJ0_3
noncomputable section
open CJ0 Polynomial PolynomialDifferential
open scoped BigOperators
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
theorem centerMap_injective : Function.Injective centerMap :=
  (algebraMap FX Geo).injective.comp (IsFractionRing.injective (Polynomial K) FX)
theorem initial_eq_map (G : Equation) :
    initial G = MvPolynomial.map centerMap (MvPolynomial.optionEquivRight K (Fin 3) G) := by
  let a : Equation →+* InitialRing 2 :=
    (MvPolynomial.aeval (fun j : Option (Fin 3) => j.elim (MvPolynomial.C center)
      MvPolynomial.X)).toRingHom.comp (MvPolynomial.map embed)
  let b : Equation →+* InitialRing 2 := (MvPolynomial.map centerMap).comp
    (MvPolynomial.optionEquivRight K (Fin 3)).toAlgHom.toRingHom
  have he : a = b := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change a (MvPolynomial.C c) = b (MvPolynomial.C c)
      simp [a, b]
      rfl
    · intro j
      cases j with
      | none =>
        simp [a, b]
        rfl
      | some j => simp [a, b]
  exact DFunLike.congr_fun he G
theorem initial_injective : Function.Injective initial := by
  intro P Q h
  rw [initial_eq_map, initial_eq_map] at h
  exact (MvPolynomial.optionEquivRight K (Fin 3)).injective
    (MvPolynomial.map_injective _ centerMap_injective h)
theorem initial_ne_zero {G : Equation} (hG : G ≠ 0) : initial G ≠ 0 := by
  intro h
  apply hG
  exact initial_injective (h.trans (by simp [initial, lifted, initialJetEquation]))
theorem eval_at_center (P : (Polynomial K)) : (P.map embed).eval center = centerMap P := by
  rw [eval_map]
  change eval₂RingHom embed center P = centerMap P
  have h : eval₂RingHom embed center = centerMap := by
    apply Polynomial.ringHom_ext
    · intro a
      change eval₂ embed center (Polynomial.C a) = centerMap (Polynomial.C a)
      rw [eval₂_C]
      rfl
    · change eval₂ embed center Polynomial.X = centerMap Polynomial.X
      rw [eval₂_X]
      rfl
  rw [h]
theorem initial_eval (G : Equation) (f : (Polynomial K)) :
    MvPolynomial.eval (nativeJet f) (initial G) =
      centerMap (differentialSpecialization G f) := by
  rw [initial, ← MvPolynomial.aeval_eq_eval, aeval_initialJetEquation, nativeJet,
    ← eval_differentialSpecialization, lifted, ← map_differentialSpecialization, eval_at_center]
theorem initialSep_eval (G : Equation) (f : (Polynomial K)) :
    MvPolynomial.eval (nativeJet f) (initialSep G) =
      centerMap (differentialSpecialization (separant G (Fin.last 2)) f) := by
  have he : initialSep G = initial (separant G (Fin.last 2)) := by
    rw [initialSep, initialJetSeparant, initial, lifted, lifted, map_separant]
    rfl
  rw [he, initial_eval]
theorem readJet_eq {L : ℕ} (P : (Polynomial Geo)) (hp : P.degree < L) (j : ℕ) :
    (∑ i : Fin L, (i.val.choose j : Geo) * center^(i.val-j) * P.coeff i.val) =
      (hasseDeriv j P).eval center := by
  rw [hasseDeriv_apply, ← Polynomial.sum_fin
    (fun i c => monomial (i - j) ((i.choose j : Geo) * c)) (by simp) hp, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [eval_monomial]
  ring
end
end CJ0_3
end
section
namespace CJ0_3
noncomputable section
open CJ0 PolynomialDifferential MvPolynomial
open scoped BigOperators
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
private theorem weighted_map_eq {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (hφ : Function.Injective φ) (w : σ → ℕ) (P : MvPolynomial σ R) :
    (MvPolynomial.map φ P).weightedTotalDegree w = P.weightedTotalDegree w := by
  unfold weightedTotalDegree
  rw [support_map_of_injective P hφ]
theorem initial_weight (w : Fin 3 → ℕ) (G : Equation) :
    (initial G).weightedTotalDegree w = G.weightedTotalDegree (fun j => j.elim 0 w) := by
  rw [initial_eq_map, weighted_map_eq _ centerMap_injective, weightedTotalDegree_optionEquivRight]
theorem lifted_weight (w : Option (Fin 3) → ℕ) (G : Equation) :
    (lifted G).weightedTotalDegree w = G.weightedTotalDegree w :=
  weighted_map_eq embed embed.injective w G
theorem lifted_total (G : Equation) : jetTotalDegree (lifted G) = jetTotalDegree G :=
  lifted_weight jetDegreeWeight G
theorem lifted_top (G : Equation) :
    jetDegree (lifted G) (Fin.last 2) = jetDegree G (Fin.last 2) := by
  simpa only [jetDegree, weightedTotalDegree_piSingle] using
    lifted_weight (Pi.single (some (Fin.last 2)) 1) G
theorem orderTwo_of_dvd {s : Source} {G Q : Equation} (hQ : OrderTwo s Q) (h : G ∣ Q) :
    OrderTwo s G := by
  refine ⟨ne_zero_of_dvd_ne_zero hQ.1 h,
    (weightedTotalDegree_le_of_dvd jetDegreeWeight h hQ.1).trans hQ.2.1,
    (weightedTotalDegree_le_of_dvd CJ0.indexWeight h hQ.1).trans hQ.2.2.1, ?_⟩
  have htop := weightedTotalDegree_le_of_dvd (Pi.single (some (Fin.last 2)) 1) h hQ.1
  rw [weightedTotalDegree_piSingle, weightedTotalDegree_piSingle] at htop
  exact htop.trans hQ.2.2.2
theorem totalWeight_eq : (fun j : Option (Fin 3) => j.elim 0 (1 : Fin 3 → ℕ)) =
    jetDegreeWeight := by
  funext j
  cases j <;> rfl
private theorem topWeight_eq : (fun j : Option (Fin 3) =>
    j.elim 0 (Pi.single (Fin.last 2) 1)) = Pi.single (some (Fin.last 2)) (1 : ℕ) := by
  funext j
  cases j <;> simp [Pi.single_apply]
theorem factor_weights {s : Source} {Q : Equation} (hQ : OrderTwo s Q) (F : FactorFamily Q) :
    (∑ i, (F.equation i).totalDegree) ≤ s.B ∧
    (∑ i, (F.equation i).weightedTotalDegree Fin.val) ≤ s.J ∧
    (∑ i, (F.equation i).degreeOf (Fin.last 2)) ≤ s.C := by
  have hn := initial_ne_zero hQ.1
  have h (w : Fin 3 → ℕ) :
      (∑ i, (F.equation i).weightedTotalDegree w) ≤ (initial Q).weightedTotalDegree w :=
    sum_weightedTotalDegree_le_of_prod_dvd w Finset.univ F.equation hn F.product_dvd
  have ht := h (1 : Fin 3 → ℕ)
  have hi := h Fin.val
  have hc := h (Pi.single (Fin.last 2) 1)
  rw [initial_weight, totalWeight_eq] at ht
  rw [initial_weight] at hi
  rw [initial_weight, topWeight_eq, weightedTotalDegree_piSingle] at hc
  simp only [weightedTotalDegree_one] at ht
  simp only [weightedTotalDegree_piSingle] at hc
  exact ⟨ht.trans hQ.2.1, hi.trans hQ.2.2.1, hc.trans hQ.2.2.2⟩
theorem factor_count {Q : Equation} (F : FactorFamily Q) :
    F.count ≤ ∑ i, (F.equation i).totalDegree := by
  classical
  have h (i : Fin F.count) : 1 ≤ (F.equation i).totalDegree := by
    by_contra! hh
    have hdeg : (F.equation i).totalDegree = 0 := by omega
    have he := totalDegree_eq_zero_iff_eq_C.mp hdeg
    have hz : (F.equation i).coeff 0 ≠ 0 := fun hz =>
      (F.irreducible i).ne_zero (he.trans (by rw [hz, map_zero]))
    exact (F.irreducible i).not_isUnit (he.symm ▸ (isUnit_iff_ne_zero.mpr hz).map MvPolynomial.C)
  calc
    F.count = ∑ _ : Fin F.count, (1 : ℕ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun i _ => h i
theorem degreeOf_top_of_index {P : InitialRing 2} {d : ℕ}
    (hP : P.weightedTotalDegree Fin.val ≤ d) : P.degreeOf (Fin.last 2) ≤ d / 2 := by
  classical
  apply degreeOf_le_iff.mpr
  intro m hm
  have hweight : 2 * m (Fin.last 2) ≤ Finsupp.weight Fin.val m := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    have hsum : m (Fin.last 2) • (Fin.last 2).val ≤ ∑ i, m i • Fin.val i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (m i • Fin.val i))
        (Finset.mem_univ (Fin.last 2))
    simpa only [Fin.val_last, smul_eq_mul, Nat.mul_comm 2] using hsum
  have h := hweight.trans ((le_weightedTotalDegree Fin.val hm).trans hP)
  omega
theorem indexWeight_eq : Astra7.jetWeight 0 1 3 = CJ0.indexWeight := by
  funext i
  cases i <;> simp [Astra7.jetWeight, CJ0.indexWeight]
theorem coeffWeight_eq : Astra7.coeffWeight 0 1 (2 + 1) = Fin.val := by
  funext i
  simp [Astra7.coeffWeight]
end
end CJ0_3
end
section
namespace CJ0_3
noncomputable section
open CJ0 PolynomialDifferential
open scoped BigOperators
set_option maxRecDepth 4000
def c1 : Prop :=
  ∀ Q : Equation, Q ≠ 0 → Nonempty (FactorFamily Q)
end
end CJ0_3
end
section
namespace CJ0_3_1
noncomputable section
open CJ0 CJ0_3 Polynomial PolynomialDifferential UniqueFactorizationMonoid
open scoped BigOperators
local instance : StrongNormalizationMonoid Equation :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
local instance : StrongNormalizationMonoid (InitialRing 2) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
private def initialHom : Equation →+* InitialRing 2 :=
  (MvPolynomial.aeval (fun j : Option (Fin 3) =>
    j.elim (MvPolynomial.C center) MvPolynomial.X)).toRingHom.comp (MvPolynomial.map embed)
private theorem root_of_associated {G G' : Equation} {f : (Polynomial K)}
    (ha : Associated G G') (hG : differentialSpecialization G f = 0)
    (hS : differentialSpecialization (separant G (Fin.last 2)) f ≠ 0) :
    differentialSpecialization G' f = 0 ∧
      differentialSpecialization (separant G' (Fin.last 2)) f ≠ 0 := by
  obtain ⟨u, rfl⟩ := ha
  let ev := differentialSpecializationHom f (d := 2)
  have hu : ev (u : Equation) ≠ 0 := (u.isUnit.map ev).ne_zero
  change ev G = 0 at hG
  change ev (separant G (Fin.last 2)) ≠ 0 at hS
  change ev (G * u) = 0 ∧ ev (separant (G * u) (Fin.last 2)) ≠ 0
  refine ⟨by rw [map_mul, hG, zero_mul], ?_⟩
  rw [separant, MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, hG, zero_mul, add_zero]
  exact mul_ne_zero hS hu
private theorem root_in_factor {P : InitialRing 2} (hP : P ≠ 0) (u : Fin 3 → Geo)
    (h : MvPolynomial.eval u P = 0) :
    ∃ g ∈ normalizedFactors P, MvPolynomial.eval u g = 0 := by
  have hd := map_dvd (MvPolynomial.eval u) (prod_normalizedFactors hP).symm.dvd
  rw [h, zero_dvd_iff, map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hd
  exact hd
theorem proof : CJ0_3.c1 := by
  classical
  intro Q hQ
  let native := (normalizedFactors Q).toFinset
  let geometric (G : Equation) :=
    (normalizedFactors (initial G)).toFinset.filter fun g => ¬ g ∣ initialSep G
  let pairs := native.sigma geometric
  let n := pairs.card
  let e : Fin n ≃ ↥pairs := (Fintype.equivFinOfCardEq (Fintype.card_coe pairs)).symm
  let entry (i : Fin n) := (e i).val
  have hmember (i : Fin n) : (entry i).1 ∈ native ∧ (entry i).2 ∈ geometric (entry i).1 :=
    Finset.mem_sigma.mp (e i).property
  have hnative (i : Fin n) : (entry i).1 ∈ normalizedFactors Q :=
    Multiset.mem_toFinset.mp (hmember i).1
  have hgeometric (i : Fin n) :
      (entry i).2 ∈ normalizedFactors (initial (entry i).1) ∧
        ¬ (entry i).2 ∣ initialSep (entry i).1 := by
    obtain ⟨hm, hd⟩ := Finset.mem_filter.mp (hmember i).2
    exact ⟨Multiset.mem_toFinset.mp hm, hd⟩
  have hprod : (∏ a ∈ pairs, a.2) ∣ initial Q := by
    have hnativeProd : (∏ G ∈ native, G) ∣ Q :=
      (Multiset.toFinset_prod_dvd_prod _).trans (prod_normalizedFactors hQ).dvd
    have hm := map_dvd initialHom hnativeProd
    rw [map_prod] at hm
    change (∏ a ∈ native.sigma geometric, a.2) ∣ initialHom Q
    rw [Finset.prod_sigma]
    refine (Finset.prod_dvd_prod_of_dvd _ _ (fun G hG => ?_)).trans hm
    have hGne := initial_ne_zero (ne_zero_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hG))
    change (∏ g ∈ geometric G, g) ∣ initial G
    exact (Finset.prod_dvd_prod_of_subset _ _ id (Finset.filter_subset _ _)).trans
      ((Multiset.toFinset_prod_dvd_prod _).trans (prod_normalizedFactors hGne).dvd)
  refine ⟨⟨n, fun i => (entry i).1, fun i => (entry i).2,
    fun i => irreducible_of_normalized_factor _ (hnative i),
    fun i => dvd_of_mem_normalizedFactors (hnative i),
    fun i => irreducible_of_normalized_factor _ (hgeometric i).1,
    fun i => dvd_of_mem_normalizedFactors (hgeometric i).1,
    fun i => (hgeometric i).2, ?_, ?_⟩⟩
  · have heq : (∏ i : Fin n, (entry i).2) = ∏ a ∈ pairs, a.2 := by
      calc
        _ = ∏ a : ↥pairs, a.val.2 := e.prod_comp (fun a : ↥pairs => a.val.2)
        _ = _ := Finset.prod_coe_sort pairs (fun a => a.2)
    rw [heq]
    exact hprod
  · intro f hreg
    obtain ⟨G, hGir, hGdvd, hGroot, hGsep⟩ := hreg
    obtain ⟨G', hGnative, hGassoc⟩ := exists_mem_normalizedFactors_of_dvd hQ hGir hGdvd
    obtain ⟨hroot, hsep⟩ := root_of_associated hGassoc hGroot hGsep
    have hinitial : MvPolynomial.eval (nativeJet f) (initial G') = 0 := by
      rw [initial_eval, hroot, map_zero]
    have hinitialSep : MvPolynomial.eval (nativeJet f) (initialSep G') ≠ 0 := by
      rw [initialSep_eval]
      exact map_ne_zero_iff centerMap centerMap_injective |>.mpr hsep
    have hne := initial_ne_zero (ne_zero_of_mem_normalizedFactors hGnative)
    obtain ⟨g, hgmem, hgroot⟩ := root_in_factor hne (nativeJet f) hinitial
    have hgreg : ¬ g ∣ initialSep G' := by
      intro hdvd
      have hm := map_dvd (MvPolynomial.eval (nativeJet f)) hdvd
      rw [hgroot, zero_dvd_iff] at hm
      exact hinitialSep hm
    have hpair : (⟨G', g⟩ : Sigma fun _ : Equation => InitialRing 2) ∈ pairs :=
      Finset.mem_sigma.mpr ⟨Multiset.mem_toFinset.mpr hGnative,
        Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hgmem, hgreg⟩⟩
    let a : ↥pairs := ⟨⟨G', g⟩, hpair⟩
    refine ⟨e.symm a, ?_⟩
    change differentialSpecialization (e (e.symm a)).val.1 f = 0 ∧
      MvPolynomial.eval (nativeJet f) (e (e.symm a)).val.2 = 0 ∧
      MvPolynomial.eval (nativeJet f) (initialSep (e (e.symm a)).val.1) ≠ 0
    rw [e.apply_symm_apply]
    exact ⟨hroot, hgroot, hinitialSep⟩
end
end CJ0_3_1
end
section
namespace CJ0_3_2
noncomputable section
open CJ0 PolynomialDifferential MvPolynomial
open scoped BigOperators
set_option maxRecDepth 4000
private def coeffWeight {L : ℕ} (i : Fin L) : ℕ := i.val - 1
private def jetWeight (L : ℕ) : Option (Fin L) → ℕ :=
  fun i => i.elim 0 coeffWeight
private theorem jetWeight_initial :
    jetWeight 3 = Pi.single (some (Fin.last 2)) 1 := by
  funext i
  cases i with
  | none => simp [jetWeight]
  | some j => fin_cases j <;> decide
section Field
variable {F : Type*} [Field F]
private theorem universalJet_offset (L j : ℕ) :
    SupportWeightOffset (Finsupp.weight (jetWeight L))
      (Finsupp.weight (Astra7.displacementWeight 1 L)) (j - 1)
      (universalTaylorJet (F := F) L j) := by
  classical
  apply SupportWeightOffset.sum
  intro i hi
  apply SupportWeightOffset.monomial
  have hj := (Finset.mem_filter.mp hi).2
  simp only [map_add, Finsupp.weight_single, smul_eq_mul, jetWeight,
    Astra7.displacementWeight, coeffWeight, Option.elim_some, Option.elim_none,
    mul_zero, zero_add, one_mul, add_zero, mul_one]
  omega
private theorem residual_coeff_weight (L h : ℕ) (x : F) (Q : DifferentialPolynomial F 2)
    {c : ℕ} (hQ : Q.degreeOf (some (Fin.last 2)) ≤ c)
    {m : Fin L →₀ ℕ}
    (hm : m ∈ ((optionEquivLeft F (Fin L) (universalTaylorResidual L x Q)).coeff h).support) :
    Finsupp.weight coeffWeight m ≤ h + c := by
  have hres : SupportWeightOffset (Finsupp.weight (jetWeight L))
      (Finsupp.weight (Astra7.displacementWeight 1 L))
      (Q.weightedTotalDegree (jetWeight 3)) (universalTaylorResidual L x Q) := by
    apply supportWeightOffset_aeval
    intro i
    cases i with
    | none =>
      apply SupportWeightOffset.add
      · exact SupportWeightOffset.C x
      · apply SupportWeightOffset.monomial
        simp [jetWeight, Astra7.displacementWeight, Finsupp.weight_single]
    | some j => exact universalJet_offset L j.val
  have hw := hres (m.optionElim h) ((mem_support_coeff_optionEquivLeft F).mp hm)
  change Finsupp.weight (fun i : Option (Fin L) => i.elim 0 coeffWeight) (m.optionElim h) ≤
    Finsupp.weight (fun i : Option (Fin L) => i.elim 1 (fun _ => 0)) (m.optionElim h) +
      Q.weightedTotalDegree (jetWeight 3) at hw
  rw [Finsupp.weight_elim_one_zero, Finsupp.optionElim_apply_none,
    Finsupp.weight_optionElim, zero_mul, zero_add, jetWeight_initial,
    weightedTotalDegree_piSingle] at hw
  exact hw.trans (Nat.add_le_add_left hQ h)
private theorem initial_coord_bound (l : ℕ) (hl : l < 3) :
    (MvPolynomial.X (⟨l, hl⟩ : Fin 3) : MvPolynomial (Fin 3) F).degreeOf (Fin.last 2) ≤ l - 1 := by
  rw [degreeOf_X]
  split
  · rename_i he
    have he' := congrArg Fin.val he
    change 2 = l at he'
    omega
  · exact Nat.zero_le _
private theorem rationalTaylor_top (x : F) (Q : DifferentialPolynomial F 2) {c : ℕ}
    (hc : 0 < c) (hQ : Q.degreeOf (some (Fin.last 2)) ≤ c) (l : ℕ) :
    (rationalTaylorNumerator x Q l).degreeOf (Fin.last 2) ≤
      (2 * (l - 2) - 1) * (c - 1) + (l - 1) := by
  have hsep := (degreeOf_initialJetSeparant_le x Q).trans (Nat.sub_le_sub_right hQ 1)
  induction l using Nat.strong_induction_on with
  | ind l ih =>
    rw [rationalTaylorNumerator]
    split_ifs with hl
    · exact (initial_coord_bound (F := F) l hl).trans (Nat.le_add_left _ _)
    · let R := (optionEquivLeft F (Fin l) (universalTaylorResidual l x Q)).coeff (l - 2)
      have hden : ∀ m ∈ R.support,
          Finsupp.weight (fun i : Fin l => 2 * (i.val - 2) - 1) m ≤ 2 * (l - 2) - 2 :=
        fun m hm => denominator_weight_le_of_mem_universalTaylorResidual_coeff
          (r := 2) (K := l) (h := l - 2) (by omega) x Q m hm
      have hw : ∀ m ∈ R.support, Finsupp.weight coeffWeight m ≤ (l - 2) + c :=
        fun _ hm => residual_coeff_weight l (l - 2) x Q hQ hm
      have hd := degreeOf_clearedSubstitution (Fin.last 2) (initialJetSeparant x Q)
        (fun i : Fin l => rationalTaylorNumerator x Q i.val)
        (fun i => 2 * (i.val - 2) - 1) coeffWeight (2 * (l - 2) - 2) (c - 1)
        ((l - 2) + c) R hsep (fun i => ih i.val i.isLt) hden hw
      have hstep : 2 * (l - 2) - 1 = (2 * (l - 2) - 2) + 1 := by omega
      have hbudget : (l - 2) + c = (c - 1) + (l - 1) := by omega
      refine (degreeOf_mul_le _ _ _).trans ?_
      simp only [degreeOf_neg, degreeOf_C, zero_add]
      apply hd.trans
      rw [hstep, Nat.add_mul, one_mul, hbudget, Nat.add_assoc]
theorem commonTaylor_top (x : F) (Q : DifferentialPolynomial F 2) {c L τ : ℕ}
    (hc : 0 < c) (hQ : Q.degreeOf (some (Fin.last 2)) ≤ c) (hτ : TaylorExponentSufficient 2 L τ)
    (l : Fin L) :
    (commonTaylorNumerator x Q τ l.val).degreeOf (Fin.last 2) ≤ τ * (c - 1) + (l.val - 1) := by
  have hsep := (degreeOf_initialJetSeparant_le x Q).trans (Nat.sub_le_sub_right hQ 1)
  let d := 2 * (l.val - 2) - 1
  have he : τ - d + d = τ := Nat.sub_add_cancel (hτ l)
  unfold commonTaylorNumerator
  apply (degreeOf_mul_le _ _ _).trans
  apply (Nat.add_le_add (rationalTaylor_top x Q hc hQ l.val)
    ((degreeOf_pow_le _ _ _).trans (Nat.mul_le_mul_left (τ - d) hsep))).trans
  change d * (c - 1) + (l.val - 1) + (τ - d) * (c - 1) ≤ _
  rw [Nat.add_right_comm, ← Nat.add_mul, Nat.add_comm d (τ - d), he]
end Field
end
end CJ0_3_2
end
section
set_option autoImplicit false
namespace CJ0_4
noncomputable section
open CJ0 MvPolynomial
def sourceIdeal {r : ℕ} (T : Chart r) : Ideal (InitialRing r) :=
  Ideal.span {T.equation}
def bandSpace (a d e : ℕ) : Submodule Geo (InitialRing 2) :=
  restrictSupport Geo
    {u : Fin 3 →₀ ℕ | u.degree ≤ a ∧ u.weight Fin.val ≤ d ∧ u (Fin.last 2) ≤ e}
theorem mem_bandSpace {a d e : ℕ} {P : InitialRing 2} :
    P ∈ bandSpace a d e ↔
      P.totalDegree ≤ a ∧ P.weightedTotalDegree Fin.val ≤ d ∧ P.degreeOf (Fin.last 2) ≤ e := by
  rw [bandSpace, mem_restrictSupport_iff, totalDegree, weightedTotalDegree,
    Finset.sup_le_iff, Finset.sup_le_iff, degreeOf_le_iff]
  exact ⟨fun h => ⟨fun _ hu => (h hu).1, fun _ hu => (h hu).2.1, fun _ hu => (h hu).2.2⟩,
    fun ⟨ha, hd, he⟩ _ hu => ⟨ha _ hu, hd _ hu, he _ hu⟩⟩
theorem bandSpace_mono {a d e a' d' e' : ℕ} (ha : a ≤ a') (hd : d ≤ d') (he : e ≤ e') :
    bandSpace a d e ≤ bandSpace a' d' e' := by
  intro P hP
  obtain ⟨h₁, h₂, h₃⟩ := mem_bandSpace.mp hP
  exact mem_bandSpace.mpr ⟨h₁.trans ha, h₂.trans hd, h₃.trans he⟩
instance (a d e : ℕ) : Module.Finite Geo (bandSpace a d e) :=
  Module.Finite.of_injective
    (Submodule.inclusion (show bandSpace a d e ≤ restrictTotalDegree (Fin 3) Geo a from
      fun _ hP => (mem_restrictTotalDegree _ _ _).mpr (mem_bandSpace.mp hP).1))
    (Submodule.inclusion_injective _)
theorem mul_mem_bandSpace {a d e b j c : ℕ} {P Q : InitialRing 2}
    (hP : P ∈ bandSpace a d e) (hQ : Q ∈ bandSpace b j c) :
    P * Q ∈ bandSpace (a + b) (d + j) (e + c) := by
  obtain ⟨hP₁, hP₂, hP₃⟩ := mem_bandSpace.mp hP
  obtain ⟨hQ₁, hQ₂, hQ₃⟩ := mem_bandSpace.mp hQ
  exact mem_bandSpace.mpr
    ⟨(totalDegree_mul _ _).trans (Nat.add_le_add hP₁ hQ₁),
     (weightedTotalDegree_mul_le _ _ _).trans (Nat.add_le_add hP₂ hQ₂),
     (degreeOf_mul_le _ _ _).trans (Nat.add_le_add hP₃ hQ₃)⟩
def quotientBand (T : Chart 2) (a d e : ℕ) :
    Submodule Geo (InitialRing 2 ⧸ sourceIdeal T) :=
  (bandSpace a d e).map (Ideal.Quotient.mkₐ Geo (sourceIdeal T)).toLinearMap
instance (T : Chart 2) (a d e : ℕ) : Module.Finite Geo (quotientBand T a d e) := by
  unfold quotientBand
  infer_instance
def bandCount (a d e : ℚ) : ℚ :=
  (e + 1) * (d + 1 - e) * (2 * a + 2 - d) / 2
end
end CJ0_4
end
section
set_option autoImplicit false
namespace CJ0_4
noncomputable section
open CJ0 MvPolynomial
section
variable {r : ℕ}
abbrev ChartOpen (T : Chart r) :=
  Localization.Away (Ideal.Quotient.mk (sourceIdeal T) T.denominator)
def localize (T : Chart r) : InitialRing r →ₐ[Geo] ChartOpen T :=
  (IsScalarTower.toAlgHom Geo (InitialRing r ⧸ sourceIdeal T) (ChartOpen T)).comp
    (Ideal.Quotient.mkₐ Geo (sourceIdeal T))
def invDenom (T : Chart r) : ChartOpen T :=
  IsLocalization.Away.invSelf (Ideal.Quotient.mk (sourceIdeal T) T.denominator)
theorem denom_mul_inv (T : Chart r) :
    localize T T.denominator * invDenom T = 1 :=
  IsLocalization.Away.mul_invSelf (Ideal.Quotient.mk (sourceIdeal T) T.denominator)
def chartMap (T : Chart r) : CoeffRing →ₐ[Geo] ChartOpen T :=
  aeval fun i => localize T (T.numerator i) * invDenom T
private theorem in_zeroLocus {T : Chart r} {y : Fin (r+1) → Geo}
    (hy : y ∈ T.locus) : y ∈ zeroLocus Geo (sourceIdeal T) := by
  apply mem_zeroLocus_iff_le_ker_aeval.mpr
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  exact RingHom.mem_ker.mpr hy.1
private def pointEval {T : Chart r} {y : Fin (r+1) → Geo} (hy : y ∈ T.locus) :
    (InitialRing r ⧸ sourceIdeal T) →ₐ[Geo] Geo :=
  Ideal.Quotient.liftₐ (sourceIdeal T) (aeval y) fun q hq => in_zeroLocus hy q hq
def openEval {T : Chart r} {y : Fin (r+1) → Geo} (hy : y ∈ T.locus) :
    ChartOpen T →ₐ[Geo] Geo :=
  IsLocalization.Away.liftAlgHom (f := pointEval hy)
    (Ideal.Quotient.mk (sourceIdeal T) T.denominator) (isUnit_iff_ne_zero.mpr hy.2)
theorem openEval_localize {T : Chart r} {y : Fin (r+1) → Geo} (hy : y ∈ T.locus)
    (q : InitialRing r) : openEval hy (localize T q) = eval y q :=
  IsLocalization.Away.lift_eq (g := (pointEval hy).toRingHom)
    (Ideal.Quotient.mk (sourceIdeal T) T.denominator) (isUnit_iff_ne_zero.mpr hy.2)
    (Ideal.Quotient.mk (sourceIdeal T) q)
theorem openEval_chartMap {T : Chart r} {y : Fin (r+1) → Geo} (hy : y ∈ T.locus)
    (q : CoeffRing) : openEval hy (chartMap T q) = eval (T.output y) q := by
  have hu := congrArg (openEval hy) (denom_mul_inv T)
  rw [map_mul, openEval_localize, map_one] at hu
  have hi : openEval hy (invDenom T) = (eval y T.denominator)⁻¹ := by
    rw [← one_div]
    exact (eq_div_iff hy.2).mpr ((mul_comm _ _).trans hu)
  have h : (openEval hy).comp (chartMap T) = aeval (T.output y) := by
    apply MvPolynomial.algHom_ext
    intro i
    change openEval hy (chartMap T (MvPolynomial.X i)) = aeval (T.output y) (MvPolynomial.X i)
    rw [chartMap, aeval_X, map_mul, openEval_localize, hi, aeval_X, Chart.output, div_eq_mul_inv]
  exact DFunLike.congr_fun h q
private theorem eq_zero_of_openEval {T : Chart r} [(sourceIdeal T).IsPrime]
    (hD : T.denominator ∉ sourceIdeal T) {z : ChartOpen T}
    (hz : ∀ y (hy : y ∈ T.locus), openEval hy z = 0) : z = 0 := by
  obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj
    (Ideal.Quotient.mk (sourceIdeal T) T.denominator) z
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  change z * localize T T.denominator ^ m = localize T q at ha
  have hq : q ∈ sourceIdeal T := by
    have hmul : T.denominator * q ∈ sourceIdeal T := by
      rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := Geo) (sourceIdeal T)]
      intro y hy
      change eval y (T.denominator * q) = 0
      by_cases hyD : eval y T.denominator = 0
      · rw [map_mul, hyD, zero_mul]
      · have hy' : y ∈ T.locus := ⟨hy _ (Ideal.subset_span (by simp)), hyD⟩
        have he := congrArg (openEval hy') ha
        rw [map_mul, map_pow, openEval_localize, openEval_localize, hz y hy', zero_mul] at he
        rw [map_mul, ← he, mul_zero]
    exact (‹(sourceIdeal T).IsPrime›.mem_or_mem hmul).resolve_left hD
  have hq0 : localize T q = 0 := by
    change algebraMap (InitialRing r ⧸ sourceIdeal T) (ChartOpen T)
      (Ideal.Quotient.mk (sourceIdeal T) q) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq, map_zero]
  rw [hq0] at ha
  exact ((IsLocalization.Away.algebraMap_isUnit (S := ChartOpen T)
    (Ideal.Quotient.mk (sourceIdeal T) T.denominator)).pow m).mul_right_cancel
      (ha.trans (zero_mul _).symm)
theorem imageIdeal_eq_ker (T : Chart r) [(sourceIdeal T).IsPrime]
    (hD : T.denominator ∉ sourceIdeal T) : T.ideal = RingHom.ker (chartMap T).toRingHom := by
  ext q
  change q ∈ vanishingIdeal Geo T.imageSet ↔ chartMap T q = 0
  constructor
  · intro hq
    apply eq_zero_of_openEval hD
    intro y hy
    rw [openEval_chartMap hy]
    exact hq _ ⟨y, hy, rfl⟩
  · intro hq
    rintro _ ⟨y, hy, rfl⟩
    change eval (T.output y) q = 0
    rw [← openEval_chartMap hy, hq, map_zero]
end
end
end CJ0_4
end
section
set_option autoImplicit false
namespace CJ0_4
noncomputable section
open CJ0 MvPolynomial Filter
open scoped BigOperators
def c1 : Prop :=
  ∀ (T : Chart 2) (a d e : ℕ), ChartOK T →
    T.denominator ∈ bandSpace a d e →
    (∀ i, T.numerator i ∈ bandSpace a d e) →
    ∀ m : ℕ, affineHilbertFunction T.ideal m ≤
      Module.finrank Geo (quotientBand T (m * a) (m * d) (m * e))
def c2 : Prop :=
  ∀ (a d e : ℕ), d ≤ a → 2 * e ≤ d →
    (Module.finrank Geo (bandSpace a d e) : ℚ) = bandCount a d e
def surfaceBound (a d e b j c : ℚ) : ℚ :=
  2 * e * (d-e) * b + e * (2*a-2*d+e) * j + (d-2*e) * (2*a-d) * c
end
end CJ0_4
end
section
set_option autoImplicit false
namespace CJ0_4_1
noncomputable section
open CJ0 CJ0_4 MvPolynomial
theorem proof : CJ0_4.c1 := by
  intro T a d e hT hD hN m
  let : (sourceIdeal T).IsPrime :=
    (Ideal.span_singleton_prime hT.irreducible.ne_zero).mpr hT.irreducible.prime
  have hD' : T.denominator ∉ sourceIdeal T :=
    fun h => hT.nonvanishing (Ideal.mem_span_singleton.mp h)
  rw [imageIdeal_eq_ker T hD']
  let j := IsScalarTower.toAlgHom Geo (InitialRing 2 ⧸ sourceIdeal T) (ChartOpen T)
  let δ := localize T T.denominator
  have hδ : IsUnit δ :=
    IsLocalization.Away.algebraMap_isUnit (S := ChartOpen T)
      (Ideal.Quotient.mk (sourceIdeal T) T.denominator)
  let y (i : Fin k) := localize T (T.numerator i) * invDenom T
  have hy (i : Fin k) : δ * y i = localize T (T.numerator i) := by
    change localize T T.denominator * (localize T (T.numerator i) * invDenom T) = _
    rw [mul_left_comm _ (localize T (T.numerator i)), denom_mul_inv, mul_one]
  let V (n : ℕ) : Submodule Geo (ChartOpen T) :=
    (quotientBand T (n * a) (n * d) (n * e)).map j.toLinearMap
  let W (n : ℕ) : Submodule Geo (ChartOpen T) :=
    (V n).comap (LinearMap.mulLeft Geo (δ ^ n))
  have hW (n : ℕ) (z : ChartOpen T) :
      z ∈ W n ↔ ∃ P ∈ bandSpace (n * a) (n * d) (n * e), localize T P = δ ^ n * z := by
    change δ ^ n * z ∈ V n ↔ _
    simp only [V, quotientBand, ← Submodule.map_comp, ← AlgHom.comp_toLinearMap,
      Submodule.mem_map, AlgHom.toLinearMap_apply, localize, j]
  have hOne : (1 : InitialRing 2) ∈ bandSpace 0 0 0 := by
    have hw : weightedTotalDegree Fin.val (1 : InitialRing 2) = 0 := by
      rw [← C_1, weightedTotalDegree_C]
    exact mem_bandSpace.mpr ⟨totalDegree_one.le, hw.le, (degreeOf_one _).le⟩
  have hpow (n : ℕ) :
      T.denominator ^ n ∈ bandSpace (n * a) (n * d) (n * e) := by
    induction n with
    | zero => simpa only [pow_zero, Nat.zero_mul] using hOne
    | succ n ih => simpa only [pow_succ, Nat.succ_mul] using mul_mem_bandSpace ih hD
  have hmono : Monotone W := by
    intro n l hnl z hz
    obtain ⟨P, hP, heq⟩ := (hW _ _).mp hz
    refine (hW _ _).mpr ⟨T.denominator ^ (l - n) * P, ?_, ?_⟩
    · simpa only [← Nat.add_mul, Nat.sub_add_cancel hnl] using
        mul_mem_bandSpace (hpow (l - n)) hP
    · rw [map_mul, map_pow, heq, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hnl]
  have hmul (i : Fin k) (n : ℕ) (z : ChartOpen T) (hz : z ∈ W n) :
      y i * z ∈ W (n + 1) := by
    obtain ⟨P, hP, heq⟩ := (hW _ _).mp hz
    refine (hW _ _).mpr ⟨P * T.numerator i, ?_, ?_⟩
    · simpa only [Nat.add_mul, Nat.one_mul] using mul_mem_bandSpace hP (hN i)
    · rw [map_mul, heq, ← hy i, pow_succ]
      ac_rfl
  have h0 : (1 : ChartOpen T) ∈ W 0 :=
    (hW _ _).mpr ⟨1, by simpa only [Nat.zero_mul] using hOne, by simp⟩
  have hclear (P : CoeffRing) (hP : P.totalDegree ≤ m) : chartMap T P ∈ W m := by
    change aeval y P ∈ W m
    simpa only [Nat.one_mul] using
      (aeval_mem_of_forall_mul_mem y hmono h0 hmul hP)
  let Q := RingHom.ker (chartMap T).toRingHom
  let ι : (CoeffRing ⧸ Q) →ₐ[Geo] ChartOpen T := Ideal.kerLiftAlg (chartMap T)
  have hmem (x : quotientDegreeLE Q m) : δ ^ m * ι x.val ∈ V m := by
    obtain ⟨P, hP, heq⟩ := mem_quotientDegreeLE.mp x.property
    change ι x.val ∈ W m
    rw [← heq]
    change chartMap T P ∈ W m
    exact hclear P hP
  let L : quotientDegreeLE Q m →ₗ[Geo] V m :=
    (((LinearMap.mulLeft Geo (δ ^ m)).comp ι.toLinearMap).domRestrict
      (quotientDegreeLE Q m)).codRestrict (V m) hmem
  have hL : Function.Injective L := by
    intro x z hxz
    have h : δ ^ m * ι x.val = δ ^ m * ι z.val := congrArg Subtype.val hxz
    exact Subtype.ext (Ideal.kerLiftAlg_injective (chartMap T) ((hδ.pow m).mul_left_cancel h))
  exact (LinearMap.finrank_le_finrank_of_injective hL).trans (Submodule.finrank_map_le _ _)
end
end CJ0_4_1
end
section
set_option autoImplicit false
namespace CJ0_4_2
noncomputable section
open CJ0 CJ0_4 MvPolynomial
open scoped BigOperators
private abbrev BandExponents (a d e : ℕ) : Set (Fin 3 →₀ ℕ) :=
  {u | u.degree ≤ a ∧ u.weight Fin.val ≤ d ∧ u (Fin.last 2) ≤ e}
private theorem degree_fin_three (u : Fin 3 →₀ ℕ) :
    u.degree = u 0 + u 1 + u 2 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three, add_assoc]
private theorem degree_fin_two (u : Fin 2 →₀ ℕ) : u.degree = u 0 + u 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
private theorem index_fin_three (u : Fin 3 →₀ ℕ) :
    u.weight Fin.val = u 1 + 2 * u 2 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_three, Nat.mul_comm]
private def bandFibers (a d e : ℕ) (hda : d ≤ a) (hed : 2 * e ≤ d) :
    BandExponents a d e ≃ Σ z : Fin (e + 1),
      cappedDegreeExponents (Fin 2) 1 (a - z) (d - 2 * z) where
  toFun u := by
    have htotal := u.property.1
    have hindex := u.property.2.1
    have htop := u.property.2.2
    rw [degree_fin_three] at htotal
    rw [index_fin_three] at hindex
    change u.val 2 ≤ e at htop
    let z : Fin (e + 1) := ⟨u.val 2, Nat.lt_succ_of_le htop⟩
    refine ⟨z, ⟨Finsupp.equivFunOnFinite.symm ![u.val 0, u.val 1], ?_⟩⟩
    rw [mem_cappedDegreeExponents, degree_fin_two]
    change u.val 0 + u.val 1 ≤ a - u.val 2 ∧ u.val 1 ≤ d - 2 * u.val 2
    omega
  invFun p := by
    obtain ⟨z, u⟩ := p
    have htotal := u.property.1
    rw [degree_fin_two] at htotal
    have hindex := u.property.2
    have hz := z.isLt
    let v : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![u.val 0, u.val 1, z.val]
    refine ⟨v, ?_⟩
    change v.degree ≤ a ∧ v.weight Fin.val ≤ d ∧ v (Fin.last 2) ≤ e
    rw [degree_fin_three, index_fin_three]
    change u.val 0 + u.val 1 + z.val ≤ a ∧ u.val 1 + 2 * z.val ≤ d ∧ z.val ≤ e
    omega
  left_inv u := by
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨⟨z, hz⟩, u⟩
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl
private theorem sum_widths (d e : ℕ) (hed : 2 * e ≤ d) :
    (∑ z ∈ Finset.range (e + 1), (d - 2 * z + 1)) = (e + 1) * (d + 1 - e) := by
  calc
    _ = ∑ z ∈ Finset.range (e + 1), (d - 2 * (e - z) + 1) := by
      symm
      simpa only [Nat.add_sub_cancel] using
        Finset.sum_range_reflect (fun z => d - 2 * z + 1) (e + 1)
    _ = ∑ z ∈ Finset.range (e + 1), ((d - 2 * e + 1) + 2 * z) := by
      apply Finset.sum_congr rfl
      intro z hz
      have hz' := Finset.mem_range.mp hz
      omega
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul,
        ← Finset.mul_sum, mul_comm 2 (∑ z ∈ Finset.range (e + 1), z),
        Finset.sum_range_id_mul_two, Nat.add_sub_cancel, ← Nat.mul_add]
      congr 1
      omega
private theorem two_mul_finrank_band (a d e : ℕ) (hda : d ≤ a) (hed : 2 * e ≤ d) :
    2 * Module.finrank Geo (bandSpace a d e) = (e + 1) * (d + 1 - e) * (2 * a + 2 - d) := by
  rw [bandSpace, Module.finrank_eq_nat_card_basis (basisRestrictSupport Geo _),
    Nat.card_congr (bandFibers a d e hda hed), Nat.card_sigma, Finset.mul_sum]
  calc
    _ = ∑ z : Fin (e + 1), (d - 2 * z.val + 1) * (2 * a + 2 - d) := by
      apply Finset.sum_congr rfl
      intro z _
      have hz := z.isLt
      have hcap : d - 2 * z.val ≤ a - z.val := by omega
      rw [Nat.card_coe_set_eq, two_mul_ncard_cappedDegreeExponents_fin_two _ _ hcap]
      congr 1
      omega
    _ = _ := by
      rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun z => d - 2 * z + 1),
        sum_widths d e hed]
theorem proof : CJ0_4.c2 := by
  intro a d e hda hed
  have he : e ≤ d + 1 := by omega
  have hd : d ≤ 2 * a + 2 := by omega
  have h := congrArg (fun n : ℕ => (n : ℚ)) (two_mul_finrank_band a d e hda hed)
  push_cast [Nat.cast_sub he, Nat.cast_sub hd] at h
  unfold bandCount
  apply (eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)).2
  rw [mul_comm]
  exact h
end
end CJ0_4_2
end
