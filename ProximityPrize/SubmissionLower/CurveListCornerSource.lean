import ProximityPrize.SubmissionLower.CurveListJointWeight

set_option Elab.async false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

namespace CurveListCornerSource
open CJ0 MvPolynomial Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open CurveListJointWeight
open scoped BigOperators Polynomial
open private column_injective from ProximityPrize.SubmissionLower.ListProofA

noncomputable section


private theorem exists_interpolant {A V : ℕ} {s : Source} {ι : Type*} [Fintype ι]
    (e : ι ↪ ColumnIndex A s) (hs : ShapeOK s)
    (hf : ∀ j ∈ s.E, j.b+3*j.c ≤ V) (hw : s.m ≤ s.m*A-N*s.B)
    (w : Node → K)
    (hr : (localConstraintMatrix s.m (fun i => node i) w (column A s ∘ e)).rank < Fintype.card ι) :
    ∃ Q : DifferentialPolynomial K 2, OrderTwo s Q ∧
      Q.weightedTotalDegree (jetWeight 3) ≤ V ∧ differentialWeightedDegree N Q < s.m*A ∧
      (∀ i, SatisfiesLocalConstraints s.m (node i) (w i) Q) ∧
      ∀ u ∈ Q.support, ∃ i : ι, u = (column A s (e i)).exponent := by
  classical
  let cols := column A s ∘ e
  let M := localConstraintMatrix s.m (fun i => node i) w cols
  have hdep : ¬ LinearIndependent K M.col := by
    intro hi
    have he : M.rank = Fintype.card ι :=
      M.rank_eq_finrank_span_cols.trans (finrank_span_eq_card hi)
    exact (Nat.ne_of_lt hr) he
  obtain ⟨v, hv, j, hj⟩ := Fintype.not_linearIndependent_iff.mp hdep
  let Q := SourceColumn.interpolant cols v
  have hQ : Q ≠ 0 := fun hz => hj (congrFun ((SourceColumn.interpolant_eq_zero_iff
    ((column_injective A s).comp e.injective)).mp hz) j)
  have hker : M.mulVec v = 0 := by
    funext row
    have h := congrFun hv row
    simpa only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, mul_comm, Matrix.col_apply] using h
  have hlocal := (localConstraintMatrix_mulVec_eq_zero_iff _ _ _ _ _).mp hker
  have hbase : N*s.B ≤ s.m*A := by have := hs.multiplicity; omega
  have hpos : 0 < s.m*A := by have := hs.multiplicity; omega
  have hsupp (u) (hu : u ∈ Q.support) : ∃ i, u = (cols i).exponent := by
    apply Astra7.generic_source_support (RingHom.id K) cols v u
    simpa only [MvPolynomial.map_id] using hu
  have ht : jetTotalDegree Q ≤ s.B := by
    apply (jetTotalDegree_le_iff _ _).mpr
    intro u hu
    obtain ⟨i,rfl⟩ := hsupp u hu
    simpa [cols, column, Jet.q, Fin.sum_univ_two, Nat.add_assoc] using (hs.support _ (e i).1.property).1
  have hi : Q.weightedTotalDegree indexWeight ≤ s.J := by
    apply Finset.sup_le
    intro u hu
    obtain ⟨i,rfl⟩ := hsupp u hu
    simpa [cols, column, CJ0.indexWeight, SourceColumn.weight_exponent, Fin.sum_univ_two,
      Jet.v, Nat.mul_comm] using (hs.support _ (e i).1.property).2.1
  have hc : jetDegree Q (Fin.last 2) ≤ s.C := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro u hu
    obtain ⟨i,rfl⟩ := hsupp u hu
    change (cols i).exponent (some (1 : Fin 2).succ) ≤ s.C
    rw [SourceColumn.exponent_succ]
    exact (hs.support _ (e i).1.property).2.2
  have hf' : Q.weightedTotalDegree (jetWeight 3) ≤ V := by
    apply Finset.sup_le
    intro u hu
    obtain ⟨i,rfl⟩ := hsupp u hu
    simpa [cols, column, jetWeight, weight, SourceColumn.weight_exponent, Fin.sum_univ_two,
      Nat.mul_comm] using hf _ (e i).1.property
  refine ⟨Q, ⟨hQ,ht,hi,hc⟩, hf', ?_, hlocal, hsupp⟩
  apply (Finset.sup_lt_iff hpos).mpr
  intro u hu
  obtain ⟨i,rfl⟩ := hsupp u hu
  have hx := (e i).2.isLt
  have hq := (Nat.mul_le_mul_left N (hs.support _ (e i).1.property).1).trans hbase
  simp only [width, Jet.q, Jet.v, N] at hx hq
  rw [SourceColumn.weight_exponent]
  simp [cols, column, differentialWeight, Fin.sum_univ_two, N]
  omega

private theorem stack_le_of_prefix {A R : ℕ} {s : Source} (hs : ShapeOK s)
    (hw : s.m ≤ s.m*A-N*s.B) (hp : prefixRank s (s.B+1) ≤ R) (w : Node → K) :
    stackRank A s w ≤ n*R := by
  have htail : SilentTail s (s.B+1) := by
    intro j hj hcut
    have hq := (hs.support j hj).1
    omega
  have horig : originRank A s ≤ R :=
    (CJ0_1.proof A s (s.B+1) hs hw le_rfl htail).trans hp
  exact (CJ0_2.proof A s hs hw w).trans (Nat.mul_le_mul_left n horig)

theorem interpolation_in_columns {A V R : ℕ} {s : Source} {ι : Type*} [Fintype ι]
    (e : ι ↪ ColumnIndex A s) (hs : ShapeOK s)
    (hf : ∀ j ∈ s.E, j.b+3*j.c ≤ V) (hw : s.m ≤ s.m*A-N*s.B)
    (hp : prefixRank s (s.B+1) ≤ R) (hcard : n*R < Fintype.card ι) (w : Node → K) :
    ∃ Q : DifferentialPolynomial K 2, OrderTwo s Q ∧
      Q.weightedTotalDegree (jetWeight 3) ≤ V ∧
      (∀ f ∈ close A w, differentialSpecialization Q f = 0) ∧
      ∀ u ∈ Q.support, ∃ i : ι, u = (column A s (e i)).exponent := by
  let M := localConstraintMatrix s.m (fun i => node i) w (column A s)
  have hsmall : (M.submatrix id e).rank < Fintype.card ι :=
    ((Matrix.rank_submatrix_le M id e).trans (stack_le_of_prefix hs hw hp w)).trans_lt hcard
  obtain ⟨Q,hQ,hQ',hwt,hloc,hsupp⟩ := exists_interpolant e hs hf hw w hsmall
  exact ⟨Q,hQ,hQ',specializes hwt hloc,hsupp⟩

end
end CurveListCornerSource
