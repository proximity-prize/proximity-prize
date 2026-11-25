import ProximityPrize.SubmissionLower.ListProofA
import ProximityPrize.SubmissionLower.Fast017

set_option Elab.async false
namespace ScalarRootRows
noncomputable section
open CJ0 Polynomial PolynomialDifferential Finset
open K1_13 (Geom Row atJet extend jet)
open scoped BigOperators Polynomial

private theorem specialize (Q : DifferentialPolynomial Geom 2) (S : Geom[X]) :
    atJet (MvPolynomial.optionEquivRight Geom (Fin 3) Q) S = differentialSpecialization Q S := by
  let x : Option (Fin 3) → Geom[X] := fun
    | none => Polynomial.X
    | some i => jet S i
  have h := MvPolynomial.aeval_map_optionEquivRight (R := Geom) x Q
  have hx : x none = Polynomial.X := rfl
  have hj : (fun j => x (some j)) = jet S := rfl
  rw [hx, hj, Polynomial.aeval_X_left] at h
  rw [show (AlgHom.id Geom Geom[X]).toRingHom = RingHom.id (Geom[X]) from rfl,
    MvPolynomial.map_id, MvPolynomial.aeval_eq_eval] at h
  unfold atJet differentialSpecialization
  refine h.trans (AlgHom.congr_fun ?_ Q)
  apply MvPolynomial.algHom_ext
  intro v
  rw [differentialSpecializationHom, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  cases v <;> rfl

/-- Extend the coefficients of a native equation while preserving its physical and jet bounds. -/
theorem row_of_native {s : Source} {W : ℕ} {Q : DifferentialPolynomial K 2}
    (hQ : OrderTwo s Q) (hwt : differentialWeightedDegree N Q < W) :
    ∃ P : Row 3, P ≠ 0 ∧ P.totalDegree ≤ s.B ∧ K1_13.indexDegree P ≤ s.J ∧
      P.degreeOf 2 ≤ s.C ∧
      (∀ m ∈ P.support, (P.coeff m).natDegree + m.sum (fun i a => (N-i.val)*a) < W) ∧
      ∀ f : K[X], differentialSpecialization Q f = 0 → atJet P (extend f) = 0 := by
  classical
  let Q' := MvPolynomial.map K1_13.embed Q
  let P := MvPolynomial.optionEquivRight Geom (Fin 3) Q'
  have hne : Q' ≠ 0 := fun h => hQ.1 (MvPolynomial.map_injective K1_13.embed
    K1_13.embed.injective (h.trans (map_zero _).symm))
  have top (m : Fin 3 →₀ ℕ) (hm : m ∈ P.support) :
      m.optionElim (P.coeff m).natDegree ∈ Q.support := by
    have leading := Polynomial.leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hm)
    have hs' : m.optionElim (P.coeff m).natDegree ∈ Q'.support := by
      apply MvPolynomial.mem_support_iff.mpr
      rwa [← MvPolynomial.optionEquivRight_coeff_coeff]
    exact MvPolynomial.support_map_subset _ _ hs'
  refine ⟨P,fun h => hne ((MvPolynomial.optionEquivRight Geom (Fin 3)).injective
    (h.trans (map_zero _).symm)), ?_, ?_, ?_, ?_, ?_⟩
  · apply Finset.sup_le
    intro m hm
    have h := (jetTotalDegree_le_iff Q _).mp hQ.2.1 _ (top m hm)
    simpa only [totalJetDegree_eq_degree_some, Finsupp.some_optionElim,
      Finsupp.degree_apply, Finsupp.sum] using h
  · apply Finset.sup_le
    intro m hm
    have h := (Finset.sup_le_iff.mp hQ.2.2.1) _ (top m hm)
    change (m.optionElim (P.coeff m).natDegree).weight
      (fun j : Option (Fin 3) => j.elim 0 Fin.val) ≤ s.J at h
    rw [Finsupp.weight_optionElim, zero_mul, zero_add] at h
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using h
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    simpa only [Finsupp.optionElim_apply_some, show Fin.last 2 = (2 : Fin 3) from by decide] using
      MvPolynomial.degreeOf_le_iff.mp hQ.2.2.2 _ (top m hm)
  · intro m hm
    have h := (MvPolynomial.le_weightedTotalDegree (differentialWeight N) (top m hm)).trans_lt hwt
    have wh : differentialWeight (d := 2) N = fun j => j.elim 1 (fun i => N-i.val) := by
      funext j
      cases j <;> rfl
    rw [wh, Finsupp.weight_optionElim, one_mul] at h
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using h
  · intro f hf
    rw [show P = MvPolynomial.optionEquivRight Geom (Fin 3) Q' from rfl,
      specialize, ← map_differentialSpecialization, hf, Polynomial.map_zero]

theorem exists_row_with_top {A R : ℕ} (s : Source) (hs : ShapeOK s)
    (hw : s.m ≤ s.m*A - N*s.B) (surplus : Surplus A s R) (rank : RankCertificate A s R)
    (w : Node → K) : ∃ P : Row 3, P ≠ 0 ∧ P.totalDegree ≤ s.B ∧ K1_13.indexDegree P ≤ s.J ∧
      P.degreeOf 2 ≤ s.C ∧
      (∀ m ∈ P.support, (P.coeff m).natDegree + m.sum (fun i a => (N-i.val)*a) < s.m*A) ∧
      ∀ f ∈ close A w, atJet P (extend f) = 0 := by
  have horig : originRank A s ≤ R := by
    rcases rank with h | ⟨cut,hcut,htail,hpre⟩
    · exact h
    · exact (CJ0_1.proof A s cut hs hw hcut htail).trans hpre
  have hr := (CJ0_2.proof A s hs hw w).trans (Nat.mul_le_mul_left n horig)
  have hdim := source_dimension A s hs hw
  unfold Surplus at surplus
  have hsmall : stackRank A s w < Fintype.card (ColumnIndex A s) := by omega
  obtain ⟨Q,hQ,hwt,hloc⟩ := interpolant hs hw w hsmall
  obtain ⟨P,hP,hB,hJ,hC,hweight,hroot⟩ := row_of_native hQ hwt
  exact ⟨P,hP,hB,hJ,hC,hweight,fun f hf => hroot f (specializes hwt hloc f hf)⟩

theorem exists_row {A R : ℕ} (s : Source) (hs : ShapeOK s)
    (hw : s.m ≤ s.m*A - N*s.B) (surplus : Surplus A s R) (rank : RankCertificate A s R)
    (w : Node → K) : ∃ P : Row 3, P ≠ 0 ∧ P.totalDegree ≤ s.B ∧ K1_13.indexDegree P ≤ s.J ∧
      (∀ m ∈ P.support, (P.coeff m).natDegree + m.sum (fun i a => (N-i.val)*a) < s.m*A) ∧
      ∀ f ∈ close A w, atJet P (extend f) = 0 := by
  obtain ⟨P,hP,hB,hJ,_,hw',hz⟩ := exists_row_with_top s hs hw surplus rank w
  exact ⟨P,hP,hB,hJ,hw',hz⟩

theorem close_data {A : ℕ} {w : Node → K} {f : K[X]} (h : f ∈ close A w) :
    f.natDegree ≤ N ∧ ∃ T : Finset Node, A ≤ T.card ∧ ∀ i ∈ T, f.eval (node i) = w i := by
  refine ⟨?_, ReedSolomon.polynomialAgreementSet node w f, h.2, fun _ hi => (Finset.mem_filter.mp hi).2⟩
  by_cases hz : f = 0
  · simp [hz]
  · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt hz).mpr h.1)

/-- A scalar family exceeding the proposed cap contains exactly cap+1 messages.
Use field elements as distinct labels for just those messages. -/
theorem list_of_indexed {A cap : ℕ} (hA : k ≤ A) (room : cap+1 ≤ Fintype.card K)
    (bound : ∀ (w : Node → K) (Γ : Finset K) (s : K → K[X]), Set.InjOn s (Γ : Set K) →
      (∀ γ ∈ Γ, s γ ∈ close A w) → Γ.card ≤ cap) : ScalarList A cap := by
  classical
  intro w
  have hf := ReedSolomon.closePolynomialSet_finite node w hA
  refine ⟨hf,?_⟩
  rw [Set.ncard_eq_toFinset_card _ hf]
  by_contra! h
  obtain ⟨T,hT,hTcard⟩ := Finset.exists_subset_card_eq (s := hf.toFinset) (show cap+1 ≤ _ by omega)
  obtain ⟨Γ,_,hΓ⟩ := Finset.exists_subset_card_eq (s := (univ : Finset K))
    (by simpa only [Finset.card_univ] using room)
  let e : Γ ≃ T := Fintype.equivOfCardEq (by simp only [Fintype.card_coe,hTcard,hΓ])
  let s (γ : K) : K[X] := if hg : γ ∈ Γ then (e ⟨γ,hg⟩).val else 0
  have inj : Set.InjOn s (Γ : Set K) := by
    intro x hx y hy eq
    change x ∈ Γ at hx
    change y ∈ Γ at hy
    have z : e ⟨x,hx⟩ = e ⟨y,hy⟩ := Subtype.ext (by simpa only [s,dite_eq_left hx,dite_eq_left hy] using eq)
    exact congrArg Subtype.val (e.injective z)
  have close' (γ : K) (hg : γ ∈ Γ) : s γ ∈ close A w := by
    simp only [s,dite_eq_left hg]
    exact hf.mem_toFinset.mp (hT (e ⟨γ,hg⟩).property)
  have := bound w Γ s inj close'
  omega

#print axioms exists_row
#print axioms exists_row_with_top
#print axioms list_of_indexed
end
end ScalarRootRows
