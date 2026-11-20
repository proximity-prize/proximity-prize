import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Fast002
import ProximityPrize.SubmissionLower.Fast008
import ProximityPrize.SubmissionLower.Fast009
import ProximityPrize.SubmissionLower.Fast010
import ProximityPrize.SubmissionLower.Fast012
set_option Elab.async false

section PackSource_C42NativeAdmission
set_option autoImplicit true
/-!
Exact typed C42 admission interfaces. The two unproved hypotheses are named:
GlobalBlockRankGate (the coefficient-map/block support bridge) and
C40ConsumerGate (full irreducible/resultant/singular-root consumer assembly).
They are definitions of propositions, not axioms. No unconditional scalar list
theorem, MCA count, or ProtocolClaim is asserted by this module.
-/

namespace Sol1.C42

set_option maxRecDepth 10000

noncomputable section
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open ProximityPrize.Benchmark

universe u
variable {E : Type u} [Field E]

open Classical in
def GlobalBlockRankGate (domain : Fin 262144 ↪ E) (received : Fin 262144 → E) : Prop :=
  ((supportedLocalConstraintMatrix 48 (fun i ↦ Polynomial.C (domain i))
      (fun i ↦ Polynomial.C (received i)) columns).map
    (algebraMap (Polynomial E) (FractionRing (Polynomial E)))).rank ≤ 262144 * blockUpper

open Classical in
def UniformAnnihilator (domain : Fin 262144 ↪ E) (received : Fin 262144 → E) : Prop :=
  ∃ Q : DifferentialPolynomial E 2, Q ≠ 0 ∧ jetTotalDegree Q ≤ 65 ∧
    ∀ P ∈ ReedSolomon.closePolynomialSet domain received 131073 180265,
      differentialSpecialization Q P = 0

open Classical in
def C40ConsumerGate (domain : Fin 262144 ↪ E) (received : Fin 262144 → E) : Prop :=
  ∀ Q : DifferentialPolynomial E 2, Q ≠ 0 → jetTotalDegree Q ≤ 65 →
    ∀ S : Finset E[X],
      (∀ P ∈ S, P ∈ ReedSolomon.closePolynomialSet domain received 131073 180265 ∧
        differentialSpecialization Q P = 0) →
      (S.card : ℚ) ≤ secondOrderCharge 64

-- Keep the rank and cardinality symbolic while simplifying the challenge degree.
private theorem certificate_at_zero_degree {P : ℕ → Prop} (r n ν : ℕ)
    (h : P (r * (0 * ν) / (n - r))) : P 0 := by
  simpa only [Nat.zero_mul, Nat.mul_zero, Nat.zero_div] using h

open Classical in
/-- The finite source family, exact cardinal surplus and all eligibility
conditions are proved. Only the actual block-to-matrix rank bound is a premise. -/
theorem certificate_of_block_rank
    (domain : Fin 262144 ↪ E) (received : Fin 262144 → E)
    (hrank : GlobalBlockRankGate domain received) :
    Nonempty (SymbolicReceivedCurve.Certificate 180265 131073 0 65 2 0 domain
      (fun i ↦ Polynomial.C (received i))) := by
  classical
  have h := SymbolicReceivedCurve.exists_certificate_of_monomial_rank_bound
    (F := E) (K := FractionRing (Polynomial E))
    (d := 2) (D := 131072) (m := 48) (A := 180265) (k := 131073)
    (ℓ := 0) (ν := 65) (r := 262144 * blockUpper)
    (by norm_num) (by norm_num) domain (fun i ↦ Polynomial.C (received i))
    (by intro i; simp) columns columns_injective columns_y0_le columns_total_le columns_weight_lt
    (algebraMap (Polynomial E) (FractionRing (Polynomial E)))
    (IsFractionRing.injective (Polynomial E) (FractionRing (Polynomial E))) hrank strict_source_surplus
  exact certificate_at_zero_degree
    (P := fun b ↦ Nonempty (SymbolicReceivedCurve.Certificate 180265 131073 0 65 2 b
      domain (fun i ↦ Polynomial.C (received i))))
    (262144 * blockUpper) (Fintype.card SourceIndex) 65 h

open Classical in
/-- The pinned certificate/contact/multiplicity machinery supplies a GLOBAL
annihilator for the entire close list, conditional on the named rank gate. -/
theorem annihilator_of_block_rank
    (domain : Fin 262144 ↪ E) (received : Fin 262144 → E)
    (hrank : GlobalBlockRankGate domain received) : UniformAnnihilator domain received := by
  classical
  obtain ⟨cert⟩ := certificate_of_block_rank domain received hrank
  let Q : DifferentialPolynomial E 2 :=
    MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id E) 0) cert.Q
  obtain ⟨hQ, hdegree, hsound⟩ := cert.specialization_sound (RingHom.id E) (0 : E)
  refine ⟨Q, hQ, hdegree, ?_⟩
  intro P hP
  let indices := ReedSolomon.polynomialAgreementSet domain received P
  apply hsound indices P hP.1 hP.2
  intro i hi
  simpa only [Polynomial.eval₂_C, RingHom.id_apply] using (Finset.mem_filter.mp hi).2

open Classical in
/-- No finiteness premise is hidden: the full list is bounded by the finite-
subset principle from an annihilator and the explicitly supplied full consumer. -/
theorem list_cap_of_annihilator_and_consumer
    (domain : Fin 262144 ↪ E) (received : Fin 262144 → E)
    (hsource : UniformAnnihilator domain received)
    (hconsumer : C40ConsumerGate domain received) :
    (ReedSolomon.closePolynomialSet domain received 131073 180265).Finite ∧
      (ReedSolomon.closePolynomialSet domain received 131073 180265).ncard ≤ listCap := by
  classical
  obtain ⟨Q, hQ, hweight, hsound⟩ := hsource
  have hfinite_subsets : ∀ S : Finset E[X],
      (S : Set E[X]) ⊆ ReedSolomon.closePolynomialSet domain received 131073 180265 →
      S.card ≤ listCap := by
    intro S hS
    apply integer_count_le_cap
    exact hconsumer Q hQ hweight S (fun P hP ↦ ⟨hS hP, hsound P (hS hP)⟩)
  have hfinite : (ReedSolomon.closePolynomialSet domain received 131073 180265).Finite := by
    by_contra hinfinite
    obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinfinite (listCap + 1)
    have h := hfinite_subsets S hS
    omega
  refine ⟨hfinite, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  exact hfinite_subsets hfinite.toFinset (fun P hP ↦ hfinite.mem_toFinset.mp hP)

open Classical in
theorem list_cap_of_named_gates
    (domain : Fin 262144 ↪ E) (received : Fin 262144 → E)
    (hrank : GlobalBlockRankGate domain received)
    (hconsumer : C40ConsumerGate domain received) :
    (ReedSolomon.closePolynomialSet domain received 131073 180265).Finite ∧
      (ReedSolomon.closePolynomialSet domain received 131073 180265).ncard ≤ listCap :=
  list_cap_of_annihilator_and_consumer domain received
    (annihilator_of_block_rank domain received hrank) hconsumer

abbrev NativeK := IRSProfile.Field
abbrev NativeIndex := IRSProfile.Index
local instance : DecidableEq NativeK := Classical.decEq NativeK
def nativeRadius6915 : ℝ := 81879 / 262144

theorem native_characteristic : ringChar NativeK = 2130706433 := by
  have : CharP NativeK 2130706433 := charP_of_injective_ringHom
    (f := algebraMap KoalaBear.Field NativeK) (algebraMap KoalaBear.Field NativeK).injective 2130706433
  exact ringChar.eq NativeK 2130706433

theorem native_charP : CharP NativeK 2130706433 := ringChar.of_eq native_characteristic

theorem native_candidate_degree_iff (P : NativeK[X]) :
    P.degree < 131073 ↔ P.natDegree ≤ 131072 := by
  change P.degree < ((131073 : ℕ) : WithBot ℕ) ↔ P.natDegree ≤ 131072
  by_cases hP : P = 0
  · rw [hP, degree_zero, natDegree_zero]
    exact ⟨fun _ ↦ by norm_num, fun _ ↦ WithBot.bot_lt_coe _⟩
  · exact (Polynomial.natDegree_lt_iff_degree_lt (n := 131073) hP).symm.trans (by omega)

open Classical in
/-- The EXACT native ordinary scalar list target, over arbitrary K-valued
words. This definition is not an assertion of its truth. -/
def NativeOrdinaryKList6915 : Prop :=
  ∀ received : NativeIndex → NativeK,
    (ReedSolomon.closePolynomialSet IRSProfile.domain received 131073 180265).Finite ∧
      (ReedSolomon.closePolynomialSet IRSProfile.domain received 131073 180265).ncard ≤ listCap

theorem native_support_threshold (T : Finset NativeIndex) :
    (T.card : ℝ) ≥ Fintype.card NativeIndex * (1 - nativeRadius6915) ↔ 180265 ≤ T.card := by
  have heq : (Fintype.card NativeIndex : ℝ) * (1 - nativeRadius6915) = (180265 : ℝ) := by
    norm_num [NativeIndex, IRSProfile.Index, nativeRadius6915]
  rw [heq]
  exact_mod_cast (Iff.rfl : 180265 ≤ T.card ↔ 180265 ≤ T.card)

open Classical in
/-- Conditional admission with BOTH missing proofs visible in the arguments. -/
theorem native_ordinary_list_6915_of_named_gates
    (hrank : ∀ received : NativeIndex → NativeK, GlobalBlockRankGate IRSProfile.domain received)
    (hconsumer : ∀ received : NativeIndex → NativeK, C40ConsumerGate IRSProfile.domain received) :
    NativeOrdinaryKList6915 := by
  intro received
  exact list_cap_of_named_gates (E := NativeK) IRSProfile.domain received
    (hrank received) (hconsumer received)


end
end Sol1.C42
end PackSource_C42NativeAdmission

section PackSource_C42RankTransport
set_option autoImplicit true
/-! The actual global symbolic matrix rank follows from one static origin
rank bound. That numerical origin-rank application remains an explicit gate. -/
namespace Sol1.C42

noncomputable section
set_option maxRecDepth 10000
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative

theorem constraint_matrix_map {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (centers received : Fin 262144 → R) :
    (localConstraintMatrix 48 centers received columns).map phi =
      localConstraintMatrix 48 (fun i ↦ phi (centers i)) (fun i ↦ phi (received i)) columns := by
  ext row j
  simp only [Matrix.map_apply, localConstraintMatrix_apply]
  rw [← MvPolynomial.coeff_map, map_unscaledLocalSubstitution]
  simp [SourceColumn.polynomial]

-- Keep the finite cardinality and the summand symbolic during simplification.
private theorem rankTransport_sum_const (n bound : ℕ) :
    (∑ _i : Fin n, bound) = n * bound := by
  simp

open Classical in
/-- Uniformity and the global sum of local ranks are now proved. Only the
single origin rank bound is assumed, over the relevant coefficient field. -/
theorem global_block_rank_of_origin {E : Type*} [Field E]
    (domain : Fin 262144 ↪ E) (received : Fin 262144 → E)
    (horigin : (pointMatrix (F := FractionRing (Polynomial E)) 48 0 0).rank ≤ blockUpper) :
    GlobalBlockRankGate domain received := by
  classical
  let F := FractionRing (Polynomial E)
  let phi : Polynomial E →+* F := algebraMap (Polynomial E) F
  change ((supportedLocalConstraintMatrix 48 (fun i ↦ C (domain i))
    (fun i ↦ C (received i)) columns).map phi).rank ≤ 262144 * blockUpper
  rw [rank_map_supportedLocalConstraintMatrix, constraint_matrix_map]
  apply (Matrix.rank_prod_rows_le_sum _).trans
  calc
    (∑ i : Fin 262144, Matrix.rank (fun row j ↦
      localConstraintMatrix 48 (fun k ↦ phi (C (domain k)))
        (fun k ↦ phi (C (received k))) columns (i,row) j)) ≤
        ∑ _i : Fin 262144, blockUpper := by
      apply Finset.sum_le_sum
      intro i _
      change (pointMatrix 48 (phi (C (domain i))) (phi (C (received i)))).rank ≤ blockUpper
      exact (point_rank_le_origin 48 (phi (C (domain i))) (phi (C (received i)))).trans horigin
    _ = 262144 * blockUpper := rankTransport_sum_const 262144 blockUpper

open Classical in
theorem annihilator_of_origin_rank {E : Type*} [Field E]
    (domain : Fin 262144 ↪ E) (received : Fin 262144 → E)
    (horigin : (pointMatrix (F := FractionRing (Polynomial E)) 48 0 0).rank ≤ blockUpper) :
    UniformAnnihilator domain received :=
  annihilator_of_block_rank domain received (global_block_rank_of_origin domain received horigin)

open Classical in
theorem list_cap_of_origin_rank_and_consumer {E : Type*} [Field E]
    (domain : Fin 262144 ↪ E) (received : Fin 262144 → E)
    (horigin : (pointMatrix (F := FractionRing (Polynomial E)) 48 0 0).rank ≤ blockUpper)
    (hconsumer : C40ConsumerGate domain received) :
    (ReedSolomon.closePolynomialSet domain received 131073 180265).Finite ∧
      (ReedSolomon.closePolynomialSet domain received 131073 180265).ncard ≤ listCap :=
  list_cap_of_annihilator_and_consumer domain received
    (annihilator_of_origin_rank domain received horigin) hconsumer

def NativeOriginRankGate : Prop :=
  (pointMatrix (F := FractionRing (Polynomial NativeK)) 48 0 0).rank ≤ blockUpper

local instance : DecidableEq NativeK := Classical.decEq NativeK

open Classical in
/-- Exact native admission from the narrowed static-origin gate and the
still-unproved full consumer. No gate is supplied as an axiom. -/
theorem native_list_6915_of_origin_rank_and_consumer
    (horigin : NativeOriginRankGate)
    (hconsumer : ∀ received : NativeIndex → NativeK,
      C40ConsumerGate ProximityPrize.Benchmark.IRSProfile.domain received) :
    NativeOrdinaryKList6915 := by
  intro received
  exact list_cap_of_origin_rank_and_consumer ProximityPrize.Benchmark.IRSProfile.domain received
    horigin (hconsumer received)


end
end Sol1.C42
end PackSource_C42RankTransport

section PackSource_C52NativeOrigin
set_option autoImplicit true
/-! Static C42 source gate, with the previously proved admission plumbing.
The C40 consumer remains a separate unproved gate. -/
namespace Sol1.C52
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open Sol1.C42
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem native_origin_rank_gate : NativeOriginRankGate := origin_rank

open Classical in
theorem uniform_annihilator {E : Type*} [Field E]
    (domain : Fin 262144 ↪ E) (received : Fin 262144 → E) :
    UniformAnnihilator domain received :=
  annihilator_of_origin_rank domain received origin_rank

open Classical in
theorem native_uniform_annihilator (received : NativeIndex → NativeK) :
    UniformAnnihilator ProximityPrize.Benchmark.IRSProfile.domain received :=
  uniform_annihilator ProximityPrize.Benchmark.IRSProfile.domain received

end
end Sol1.C52
end PackSource_C52NativeOrigin

section PackSource_WeightedSource
set_option autoImplicit true
namespace Astra7
universe u
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial
open Sol1.C42
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

theorem generic_source_support {R E κ : Type*} [CommSemiring R] [CommSemiring E] [Fintype κ]
    {d : ℕ} (psi : R →+* E) (cols : κ → SourceColumn d) (v : κ → R)
    (u : JetVariable d →₀ ℕ)
    (hu : u ∈ (MvPolynomial.map psi (SourceColumn.interpolant cols v)).support) :
    ∃ j : κ, u=(cols j).exponent := by
  classical
  have hs := MvPolynomial.support_map_subset psi (SourceColumn.interpolant cols v) hu
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hs)
  exact ⟨j,by simpa [SourceColumn.interpolant] using MvPolynomial.support_monomial_subset hj⟩

theorem generic_source_weight_le {R E κ : Type*} [CommSemiring R] [CommSemiring E] [Fintype κ]
    {d : ℕ} (psi : R →+* E) (cols : κ → SourceColumn d) (v : κ → R)
    (w : JetVariable d → ℕ) (B : ℕ) (hB : ∀ j, Finsupp.weight w (cols j).exponent ≤ B) :
    (MvPolynomial.map psi (SourceColumn.interpolant cols v)).weightedTotalDegree w ≤ B := by
  apply Finset.sup_le
  intro u hu
  obtain ⟨j,rfl⟩ := generic_source_support psi cols v u hu
  exact hB j

theorem generic_source_weight_lt {R E κ : Type*} [CommSemiring R] [CommSemiring E] [Fintype κ]
    {d : ℕ} (psi : R →+* E) (cols : κ → SourceColumn d) (v : κ → R)
    (w : JetVariable d → ℕ) (B : ℕ) (hpos : 0 < B)
    (hB : ∀ j, Finsupp.weight w (cols j).exponent < B) :
    (MvPolynomial.map psi (SourceColumn.interpolant cols v)).weightedTotalDegree w < B := by
  rw [MvPolynomial.weightedTotalDegree,Finset.sup_lt_iff hpos]
  intro u hu
  obtain ⟨j,rfl⟩ := generic_source_support psi cols v u hu
  exact hB j

theorem columns_weight148 (i : SourceIndex) :
    Finsupp.weight (jetWeight 1 4 3) (columns i).exponent ≤ 148 := by
  rw [SourceColumn.weight_exponent]
  have ht := jet_total i.1
  have ho := jet_order i.1
  have hs := i.1.1.isLt
  simp only [columns,jetWeight,Option.elim_none,Option.elim_some,
    smul_eq_mul,mul_zero,zero_add,Fin.sum_univ_two,
    Matrix.cons_val_zero,Matrix.cons_val_one,Fin.val_zero,Fin.val_one,
    Fin.val_succ,Fin.val_castSucc]
  omega

/-- The original, already certified C42 source, retaining its derivative-index
information as weighted degree 148 for jet weights (1,5,9). -/
theorem weighted_uniform_annihilator {F : Type u} [Field F]
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F) :
    ∃ Q : DifferentialPolynomial F 2, Q ≠ 0 ∧ jetTotalDegree Q ≤ 65 ∧
      Q.weightedTotalDegree (jetWeight 1 4 3) ≤ 148 ∧
      ∀ P ∈ ReedSolomon.closePolynomialSet domain received 131073 180265,
        differentialSpecialization Q P=0 := by
  classical
  let K := FractionRing (Polynomial F)
  let phi : Polynomial F →+* K := algebraMap (Polynomial F) K
  have hphi : Function.Injective phi := IsFractionRing.injective (Polynomial F) K
  have hglobal := global_block_rank_of_origin domain received (Sol1.C52.origin_rank (F := K))
  have hrank : ((localConstraintMatrix 48 (fun i => Polynomial.C (domain i))
      (fun i => Polynomial.C (received i)) columns).map phi).rank ≤ 262144*blockUpper := by
    rw [← rank_map_supportedLocalConstraintMatrix phi 48
      (fun i => Polynomial.C (domain i)) (fun i => Polynomial.C (received i)) columns]
    exact hglobal
  obtain ⟨v,_,hvdegree,hspan,_,hconstraints⟩ :=
    exists_primitive_interpolant_of_rank_le.{u,0,0,u,u} 48 0 65 (fun i => domain i)
      (fun i => Polynomial.C (received i)) (by intro i; simp) columns
      columns_injective columns_y0_le phi hphi hrank strict_source_surplus
  let Qs : DifferentialPolynomial (Polynomial F) 2 := SourceColumn.interpolant columns v
  let psi : Polynomial F →+* F := Polynomial.evalRingHom 0
  let Q : DifferentialPolynomial F 2 := MvPolynomial.map psi Qs
  have hQ0 : Q ≠ 0 := by
    exact SourceColumn.map_interpolant_ne_zero columns_injective psi
      (Ideal.comp_ne_zero_of_span_range_eq_top hspan psi)
  have hjet : jetTotalDegree Q ≤ 65 :=
    SourceColumn.map_interpolant_jetTotalDegree_le psi columns columns_total_le v
  have hwt : Q.weightedTotalDegree (jetWeight 1 4 3) ≤ 148 :=
    generic_source_weight_le psi columns v (jetWeight 1 4 3) 148 columns_weight148
  refine ⟨Q,hQ0,hjet,hwt,?_⟩
  intro P hP
  have hPdegree : P.natDegree ≤ 131072 := by
    by_cases hz : P=0
    · simp [hz]
    · have hh := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hP.1
      omega
  have hQweight : differentialWeightedDegree 131072 Q < 48*180265 :=
    generic_source_weight_lt psi columns v (differentialWeight 131072) (48*180265)
      (by decide) columns_weight_lt
  have hlocal : ∀ i, SatisfiesLocalConstraints 48 (domain i) (received i) Q := by
    intro i
    have hh := SatisfiesLocalConstraints.map psi 48 (Polynomial.C (domain i))
      (Polynomial.C (received i)) Qs (hconstraints i)
    simpa [psi,Q] using hh
  let indices := ReedSolomon.polynomialAgreementSet domain received P
  apply differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
    domain received indices hQweight (fun i _ => hlocal i) P hPdegree
    domain.injective.injOn hP.2
  intro i hi
  exact (Finset.mem_filter.mp hi).2

end
end Astra7
end PackSource_WeightedSource

section PackSource_WeightedFullList
set_option autoImplicit true
namespace Astra7
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial
open Sol1.C42 Sol1.C57
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F]

theorem regularPart_dvd (d : ℕ) (Q : DifferentialPolynomial F (d+1)) : regularPart d Q ∣ Q := by
  obtain ⟨R,hR⟩ := radicalPrimPart_dvd_self none (topReindex d Q)
  refine ⟨(topReindex d).symm R,?_⟩
  have hh := congrArg (topReindex d).symm hR
  simpa [regularPart] using hh

def weightedFullCharge : ℚ := weightedRegularCap+firstOrderCharge 4160
def weightedListCap : ℕ := 31911818688068302
def weightedMCAAllowance : ℕ := 243068909423326785

theorem weighted_budget_exact :
    weightedFullCharge=(386125227460262142519790272 : ℚ)/12099756245 ∧
    weightedFullCharge ≤ weightedListCap ∧
    (weightedListCap : ℚ)-1 < weightedFullCharge ∧
    weightedListCap+weightedMCAAllowance=274980728111395087 ∧
    123935685281173519-weightedListCap=92023866593105217 := by
  norm_num [weightedFullCharge,weightedRegularCap,firstOrderCharge,I1,b,
    weightedListCap,weightedMCAAllowance]

/-- All regular, singular, and lower-order branches are included. -/
theorem weighted_second_order_card [CharP F 2130706433]
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F)
    (Q : DifferentialPolynomial F 2) (hQ : Q ≠ 0) (hjet : jetTotalDegree Q ≤ 65)
    (hwt : Q.weightedTotalDegree (jetWeight 1 4 3) ≤ 148)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received 131073 180265) :
    (S.card : ℚ) ≤ weightedFullCharge := by
  classical
  let G := regularPart 1 Q
  have hsplit := split_weight 1 Q
  have hGjet : jetTotalDegree G ≤ 65 := by dsimp [G]; omega
  have hGwt : G.weightedTotalDegree (jetWeight 1 4 3) ≤ 148 :=
    (weightedTotalDegree_le_of_dvd (jetWeight 1 4 3) (regularPart_dvd 1 Q) hQ).trans hwt
  have hchar : ringChar F=0 ∨ jetDegree Q (Fin.last 2) < ringChar F := by
    right
    rw [ringChar.eq F 2130706433]
    have hh := jetDegree_le_total Q (Fin.last 2)
    omega
  have hcost : 0 ≤ weightedRegularCap := by unfold weightedRegularCap; positivity
  by_cases hb : jetDegree G (Fin.last 2)=0
  · have hGone : G=1 := regular_eq_one_of_degree_zero 1 Q hb
    have hlow : ∀ P ∈ S, P ∈ directJetAgreementSolutions (lowerPart 1 Q)
        domain received 131073 180265 := by
      intro P hP
      refine ⟨?_,(hS P hP).2⟩
      rcases root_split 1 Q hQ P (hS P hP).1 with hc | hr
      · exact hc
      · change differentialSpecialization G P=0 at hr
        rw [hGone] at hr
        have hz : (1 : F[X])=0 := by
          simpa only [differentialSpecialization,map_one] using hr
        exact (one_ne_zero hz).elim
    have hlowjet : jetTotalDegree (lowerPart 1 Q) ≤ 4160 := by omega
    have hc := first_order_card_le domain received (lowerPart 1 Q) (lower_ne_zero 1 Q)
      4160 (by decide) hlowjet S hlow
    exact hc.trans (le_add_of_nonneg_left hcost)
  · have hbpos : 0 < jetDegree G (Fin.last 2) := by omega
    let good : F[X] → Prop := fun P => differentialSpecialization G P=0 ∧
      differentialSpecialization (separant G (Fin.last 2)) P ≠ 0
    let regular := S.filter good
    let exceptional := S.filter fun P => ¬good P
    have hr : (regular.card : ℚ) ≤ weightedRegularCap := by
      apply regular64_card domain received G hGwt regular
      · intro P hP
        exact ((Finset.mem_filter.mp hP).2).2
      · intro P hP
        have hp := Finset.mem_filter.mp hP
        exact ⟨hp.2.1,(hS P hp.1).2⟩
    let R := exceptionalEquation 1 Q
    have hR : R ≠ 0 := exceptional_ne_zero 1 Q hchar
    have hRjet : jetTotalDegree R ≤ 4160 := by
      have hh := exceptional_weight_sharp 1 Q 65 hjet
        (hbpos.trans_le (jetDegree_le_total G (Fin.last 2)))
      exact hh
    have he : (exceptional.card : ℚ) ≤ firstOrderCharge 4160 := by
      apply first_order_card_le domain received R hR 4160 (by decide) hRjet exceptional
      intro P hP
      have hp := Finset.mem_filter.mp hP
      refine ⟨?_,(hS P hp.1).2⟩
      rcases root_regular_or_exceptional 1 Q hQ P (hS P hp.1).1 hbpos with hg | he
      · exact (hp.2 hg).elim
      · exact he
    have hc : regular.card+exceptional.card=S.card :=
      Finset.card_filter_add_card_filter_not (s := S) (p := good)
    calc
      (S.card : ℚ)=(regular.card : ℚ)+exceptional.card := by exact_mod_cast hc.symm
      _ ≤ weightedRegularCap+firstOrderCharge 4160 := add_le_add hr he
      _ = weightedFullCharge := rfl

theorem weighted_complete_list [CharP F 2130706433]
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F) :
    (ReedSolomon.closePolynomialSet domain received 131073 180265).Finite ∧
      (ReedSolomon.closePolynomialSet domain received 131073 180265).ncard ≤ weightedListCap := by
  classical
  obtain ⟨Q,hQ,hjet,hwt,hsound⟩ := weighted_uniform_annihilator domain received
  have hf : ∀ S : Finset F[X],
      (S : Set F[X]) ⊆ ReedSolomon.closePolynomialSet domain received 131073 180265 →
      S.card ≤ weightedListCap := by
    intro S hS
    have hh := weighted_second_order_card domain received Q hQ hjet hwt S
      (fun P hP => ⟨hsound P (hS hP),hS hP⟩)
    exact_mod_cast hh.trans weighted_budget_exact.2.1
  have hfin : (ReedSolomon.closePolynomialSet domain received 131073 180265).Finite := by
    by_contra hi
    obtain ⟨S,hS,hcard⟩ := Set.Infinite.exists_subset_card_eq hi (weightedListCap+1)
    have hh := hf S hS
    omega
  refine ⟨hfin,?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact hf hfin.toFinset (fun P hP => hfin.mem_toFinset.mp hP)

local instance : DecidableEq Sol1.C42.NativeK := Classical.decEq _

theorem native_weighted_complete_list (received : Sol1.C42.NativeIndex → Sol1.C42.NativeK) :
    (ReedSolomon.closePolynomialSet ProximityPrize.Benchmark.IRSProfile.domain received 131073 180265).Finite ∧
      (ReedSolomon.closePolynomialSet ProximityPrize.Benchmark.IRSProfile.domain received 131073 180265).ncard ≤
        weightedListCap := by
  let := Sol1.C42.native_charP
  exact weighted_complete_list ProximityPrize.Benchmark.IRSProfile.domain received

end
end Astra7
end PackSource_WeightedFullList
