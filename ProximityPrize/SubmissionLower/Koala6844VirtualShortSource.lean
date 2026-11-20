import ProximityPrize.SubmissionLower.Koala6844VirtualShortPhysical
import ProximityPrize.SubmissionLower.Koala6844NormalizationData


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped BigOperators
open SecondJetSupport SecondJetSpecialize SecondJetGlobalSupport SecondJetGlobalDifferentiation
open SecondJetCoefficients SecondJetCoefficientSpecialization SecondJetRelaxedDifferentiation
open Koala6844Normalization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4600000

variable {K I : Type*} [Field K] [DecidableEq K] [DecidableEq I]

def normalizedRankBudget (D : ℕ → ℕ) (w m L B s U q : ℕ) : ℕ :=
  SecondJetRelaxedGlobalMap.rankBound m L B s U (fun h => (D h+B-1)/w) +
    ∑ j : Fin q, seedlessRankBudget (m-(j.val+1)) B s (U-(j.val+1))

theorem exists_physical_source
    {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K} {w a errors excess : ℕ}
    (data : CenteredVirtualData x nodes σ w a errors excess)
    (hLead : ∀ i ∈ nodes, (data.A0 1).eval (x i) ≠ 0)
    (D : ℕ → ℕ) (wQ m L B s U q k n0 : ℕ)
    (hQ : ∀ g ∈ data.seeds, (data.normalized g).natDegree ≤ wQ)
    (ha : 0 < a) (hwa : w-2 ≤ a) (hsB : 2*s ≤ B) (hUL : U ≤ L)
    (hqU : q ≤ U) (hks : k ≤ s) (hsm : s < m)
    (hfact : ∀ d ≤ s, (d.factorial : K) ≠ 0)
    (hcaps : ∀ h ≤ s, U ≤ (D h+B-1)/w)
    (hweight : ∀ h v, v < D h → v+reserve k n0 h*(a-(w-2)) < m*a)
    (hgap : nodes.card * normalizedRankBudget D w m L B s U q <
      Fintype.card (NormalizedIndex D w wQ L B s U q)) :
    ∃ F : Poly (K := K), F ≠ 0 ∧
      (∀ e ∈ F.support, 2*e 1+e 3 ≤ B ∧ e 1 ≤ s ∧ e 1+e 2+e 3 ≤ U ∧
        e 1+e 2+e 3+e 4 ≤ L+q) ∧
      (∀ g ∈ data.seeds, ∀ d ≤ k,
        specialize (data.selected g) g ((MvPolynomial.pderiv 1)^[d] F) = 0) ∧
      ((asS F).natDegree < n0 → ∀ g ∈ data.seeds,
        coefficientSpecialize (data.selected g) g (asS F).leadingCoeff = 0) := by
  classical
  let A := normalizedDenominator (data.A0 0) (data.A0 1)
  let N := normalizedNumerator data.d0 data.C1
  let caps := fun h => (D h+B-1)/w
  let J := {i // i ∈ nodes}
  have hnodes : nodes.Nonempty := by
    apply Finset.card_pos.mp
    exact (ha.trans_le (data.agreements 0 data.zero_mem)).trans_le (Finset.card_filter_le _ _)
  have hA : data.A0 1 ≠ 0 := by
    obtain ⟨i,hi⟩ := hnodes
    intro hz
    exact hLead i hi (by rw [hz,Polynomial.eval_zero])
  obtain ⟨a₀,a₁,b₀,b₁,hAaff,hBaff,ha₁,hdet⟩ :=
    normalized_affine_elimination (data.A0 0) (data.A0 1) data.d0 data.C1 hA data.d0_ne
  have hlocal (i : J) : Module.finrank K (normalizedContactMap D w wQ L B s U q m A N
      (x i.val) (data.received 0 i.val) (data.received 1 i.val)).range ≤
      normalizedRankBudget D w m L B s U q := by
    have h0 := data.received_equation i.val i.property 0
    have h1 := data.received_equation i.val i.property 1
    norm_num at h0 h1
    obtain ⟨pole⟩ := exists_nodePoleData (x i.val) (data.received 0 i.val)
      (data.received 1 i.val) (data.fixedWord i.val) m (data.A0 0) (data.A0 1) data.d0 data.C1
      h0 h1 (hLead i.val i.property)
    exact normalized_local_rank_bound D w wQ L B s U q m hsB hUL hqU caps hcaps A N
      (x i.val) (data.received 0 i.val) (data.received 1 i.val) pole
  obtain ⟨P,hP,hclear,hsupp,hcontact⟩ := exists_normalized_global_contact D w wQ L B s U q m
    (normalizedRankBudget D w m L B s U q) hsB hUL hqU A N
    (fun i : J => x i.val) (fun i => data.received 0 i.val) (fun i => data.received 1 i.val)
    a₀ a₁ b₀ b₁ hAaff hBaff ha₁ hdet hlocal (by simpa only [J,Fintype.card_coe] using hgap)
  let F := clearAux A N q P
  have hshape := clear_normalized_support (data.A0 0) (data.A0 1) data.d0 data.C1 B s U L q P
    (fun j e he => ⟨(hsupp j e he).1,(hsupp j e he).2.1,(hsupp j e he).2.2.1,(hsupp j e he).2.2.2.1⟩)
  have hsweight := fun j e he => hweight (e 1) _ (hsupp j e he).2.2.2.2.1
  have hflat (i : I) (hi : i ∈ nodes) : MvPolynomial.X 0^m ∣
      SecondJetDifferentiation.substitute (localize (x i) (data.received 0 i) (data.received 1 i) F) :=
    nested_to_flat_contact _ m (hcontact ⟨i,hi⟩)
  let good (g : K) := nodes.filter fun i => (data.selected g).eval (x i) =
    data.received 0 i + g*data.received 1 i
  have hvals (g : K) (i : I) (hi : i ∈ good g) : (data.selected g).eval (x i) =
      data.received 0 i+data.received 1 i*g := by
    rw [mul_comm (data.received 1 i)]
    exact (Finset.mem_filter.mp hi).2
  have hden (g : K) (hg : g ∈ data.seeds) (i : I) (hi : i ∈ good g) :
      (specialize (data.selected g) g A).eval (x i) ≠ 0 := by
    simpa only [A,specialize_normalizedDenominator,specializeAffine] using
      data.denominator_on_domain g hg i (Finset.mem_filter.mp hi).1
  have heq (g : K) (hg : g ∈ data.seeds) :
      specialize (data.selected g) g N = specialize (data.selected g) g A*data.normalized g := by
    simpa only [N,A,specialize_normalizedDenominator,specialize_normalizedNumerator,specializeAffine] using
      (data.equation0 g hg).symm
  refine ⟨F,hclear,hshape,?_,?_⟩
  · intro g hg d hdk
    exact normalized_derivative_vanish P A N m a w wQ k n0 q d ha hwa
      ((hdk.trans hks).trans_lt hsm) hP (pderiv_normalizedDenominator _ _)
      (pderiv_normalizedNumerator _ _) hsweight (fun _ e _ hde => reserve_ge_order k n0 (e 1) d hdk hde)
      x (data.received 0) (data.received 1) (data.selected g) (data.normalized g)
      (data.selected_degree g hg) (hQ g hg) g (good g) (data.agreements g hg)
      (hvals g) (hden g hg) (heq g hg) (fun i hi => hflat i (Finset.mem_filter.mp hi).1)
  · intro hsmall g hg
    let d := (asS F).natDegree
    have hds : d ≤ s := by
      apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro j hj
      apply MvPolynomial.support_eq_empty.mp
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      have hk := (hshape (liftExponent j e) (coefficient_support F j e he)).2.1
      rw [(lift_coordinates j e).2.1] at hk
      omega
    have hjet j e he := normalized_jet_index_le (data.A0 0) (data.A0 1) data.d0 data.C1
      hA data.d0_ne q P hP (fun i v hv => (hsupp i v hv).2.2.2.2.2) j e he
    exact normalized_leading_coefficient_vanish P A N m a w wQ k n0 q d
      ha hwa (hds.trans_lt hsm) hsmall (hfact d hds) hP hjet rfl
      (pderiv_normalizedDenominator _ _) (pderiv_normalizedNumerator _ _) hsweight
      x (data.received 0) (data.received 1) (data.selected g) (data.normalized g)
      (data.selected_degree g hg) (hQ g hg) g (good g) (data.agreements g hg)
      (hvals g) (hden g hg) (heq g hg) (fun i hi => hflat i (Finset.mem_filter.mp hi).1)

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
