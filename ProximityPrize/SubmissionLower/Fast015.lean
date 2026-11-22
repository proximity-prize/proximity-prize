import ArkLib.Data.CodingTheory.ListDecodability.AgreementRadius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import ProximityPrize.SubmissionLower.Fast014
set_option autoImplicit true
section
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
  ∃ Q : DifferentialPolynomial E 2, Q ≠ 0 ∧ jetTotalDegree Q ≤ 64 ∧
    ∀ P ∈ ReedSolomon.closePolynomialSet domain received 131073 180265,
      differentialSpecialization Q P = 0
open Classical in
def C40ConsumerGate (domain : Fin 262144 ↪ E) (received : Fin 262144 → E) : Prop :=
  ∀ Q : DifferentialPolynomial E 2, Q ≠ 0 → jetTotalDegree Q ≤ 64 →
    ∀ S : Finset E[X],
      (∀ P ∈ S, P ∈ ReedSolomon.closePolynomialSet domain received 131073 180265 ∧
        differentialSpecialization Q P = 0) →
      (S.card : ℚ) ≤ secondOrderCharge 64
private theorem certificate_at_zero_degree {P : ℕ → Prop} (r n ν : ℕ)
    (h : P (r * (0 * ν) / (n - r))) : P 0 := by
  simpa only [Nat.zero_mul, Nat.mul_zero, Nat.zero_div] using h
open Classical in
theorem certificate_of_block_rank
    (domain : Fin 262144 ↪ E) (received : Fin 262144 → E)
    (hrank : GlobalBlockRankGate domain received) :
    Nonempty (SymbolicReceivedCurve.Certificate 180265 131073 0 64 2 0 domain
      (fun i ↦ Polynomial.C (received i))) := by
  classical
  have h := SymbolicReceivedCurve.exists_certificate_of_monomial_rank_bound
    (F := E) (K := FractionRing (Polynomial E))
    (d := 2) (D := 131072) (m := 48) (A := 180265) (k := 131073)
    (ℓ := 0) (ν := 64) (r := 262144 * blockUpper)
    (by norm_num) (by norm_num) domain (fun i ↦ Polynomial.C (received i))
    (by intro i; simp) columns columns_injective columns_y0_le columns_total_le columns_weight_lt
    (algebraMap (Polynomial E) (FractionRing (Polynomial E)))
    (IsFractionRing.injective (Polynomial E) (FractionRing (Polynomial E))) hrank strict_source_surplus
  exact certificate_at_zero_degree
    (P := fun b ↦ Nonempty (SymbolicReceivedCurve.Certificate 180265 131073 0 64 2 b
      domain (fun i ↦ Polynomial.C (received i))))
    (262144 * blockUpper) (Fintype.card SourceIndex) 64 h
open Classical in
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
open Classical in
def NativeOrdinaryKList6915 : Prop :=
  ∀ received : NativeIndex → NativeK,
    (ReedSolomon.closePolynomialSet IRSProfile.domain received 131073 180265).Finite ∧
      (ReedSolomon.closePolynomialSet IRSProfile.domain received 131073 180265).ncard ≤ listCap
open Classical in
theorem native_ordinary_list_6915_of_named_gates
    (hrank : ∀ received : NativeIndex → NativeK, GlobalBlockRankGate IRSProfile.domain received)
    (hconsumer : ∀ received : NativeIndex → NativeK, C40ConsumerGate IRSProfile.domain received) :
    NativeOrdinaryKList6915 := by
  intro received
  exact list_cap_of_named_gates (E := NativeK) IRSProfile.domain received
    (hrank received) (hconsumer received)
end
end Sol1.C42
end
section
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
private theorem rankTransport_sum_const (n bound : ℕ) :
    (∑ _i : Fin n, bound) = n * bound := by
  simp
open Classical in
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
end
section
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
end
end Astra7
end
section
namespace Astra7
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial
open Sol1.C42 Sol1.C57
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F]
local instance : DecidableEq Sol1.C42.NativeK := Classical.decEq _
end
end Astra7
end
section
namespace Sol1.Reciprocal.Native
set_option maxRecDepth 10000
noncomputable section
open Polynomial Code LinearCode CoreDefinitions
open ProximityPrize.Benchmark
abbrev Base := KoalaBear.Field
abbrev K := IRSProfile.Field
abbrev Index := IRSProfile.Index
local instance : DecidableEq Base := Classical.decEq Base
local instance : DecidableEq K := Classical.decEq K
def nodes : Index ↪ Base where
  toFun i := IRSProfile.baseNttDomain.node i
  inj' := by
    intro i j h
    apply IRSProfile.domain.injective
    change CompPoly.Extension.Ext.ofBase (IRSProfile.baseNttDomain.node i) =
      CompPoly.Extension.Ext.ofBase (IRSProfile.baseNttDomain.node j)
    exact congrArg CompPoly.Extension.Ext.ofBase h
def D : Finset Base := baseNodeSet nodes
def radius : ℝ := 338557 / 1048576
def cap : ℕ := 7 * 262144 ^ 3
open Classical in
def UniversalMCACap : Prop :=
  ∀ U : Fin 2 → Index → Fin 8 → K,
    {gamma | IsMCA (AffineLineGenerator K) IRSProfile.code gamma U radius}.ncard ≤ cap
open Classical in
def OrdinaryBaseListCap : Prop :=
  ∀ w : Base → Base, (baseCloseSet D w 131072 177505).Finite ∧
    (baseCloseSet D w 131072 177505).ncard ≤ cap
def extendWord (w : Index → Base) : Base → Base :=
  Function.extend nodes w (fun _ ↦ 0)
@[simp] theorem extendWord_nodes (w : Index → Base) (i : Index) :
    extendWord w (nodes i) = w i := nodes.injective.extend_apply _ _ _
open Classical in
def indexBaseCloseSet (w : Index → Base) : Set (Polynomial Base) :=
  {P | P.natDegree ≤ 131072 ∧
    177505 ≤ (Finset.univ.filter fun i ↦ P.eval (nodes i) = w i).card}
end
end Sol1.Reciprocal.Native
end
section
namespace Sol1.OneCount
noncomputable section
open Polynomial Code LinearCode CoreDefinitions
open ProximityPrize.Benchmark
open Sol1.Reciprocal Sol1.FiniteRowProjection
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev scalarCode : ModuleCode I K K := ReedSolomon.code IRSProfile.domain 131072
local instance : DecidableEq K := Classical.decEq K
def extendScalarWord (w : I → K) : K → K :=
  Function.extend IRSProfile.domain w (fun _ ↦ 0)
@[simp] theorem extendScalarWord_domain (w : I → K) (i : I) :
    extendScalarWord w (IRSProfile.domain i) = w i :=
  IRSProfile.domain.injective.extend_apply _ _ _
end
end Sol1.OneCount
end
section
namespace Sol1.OneCount
noncomputable section
open Polynomial Code LinearCode CoreDefinitions
open ProximityPrize.Benchmark
open Sol1.FiniteRowProjection
abbrev A16 := Fin 2 → Fin IRSProfile.interleaving → K
abbrev R16 := Fin 2 × Fin 8
def squaredCode : ModuleCode I K A16 := IRSProfile.code ^⋈ (Fin 2)
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq A16 := Classical.decEq A16
def flatten (f : I → A16) : I → R16 → K := fun i r ↦ f i r.1 r.2
theorem flatten_injective : Function.Injective flatten := by
  intro f g h
  funext i j r
  exact congrFun (congrFun h i) (j,r)
theorem flatten_agreement_le (f w : I → A16) :
    agreementCard f w ≤ agreementCard (flatten f) (flatten w) := by
  apply agreementCard_mono f w (flatten f) (flatten w)
  intro i he
  funext r
  exact congrFun (congrFun he r.1) r.2
theorem flatten_rows_mem (f : I → A16) (hf : f ∈ squaredCode) :
    ∀ r : R16, (fun i ↦ flatten f i r) ∈ scalarCode := by
  change ∀ j : Fin 2, ∀ r : Fin 8, (fun i ↦ f i j r) ∈ scalarCode at hf
  intro r
  exact hf r.1 r.2
end
end Sol1.OneCount
end
section
namespace Astra7.NativeBudget
noncomputable section
open Polynomial Code LinearCode CoreDefinitions
open ProximityPrize.Benchmark Sol1.OneCount Sol1.FiniteRowProjection Sol1.C42
set_option maxRecDepth 10000
set_option maxHeartbeats 0
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq A16 := Classical.decEq A16
end
end Astra7.NativeBudget
end
section
namespace Astra7.NativeBudget
noncomputable section
open Code CoreDefinitions ToyProblem
open ProximityPrize.Benchmark Sol1.OneCount Sol1.C42
set_option maxRecDepth 10000
set_option maxHeartbeats 0
local instance : DecidableEq K := Classical.decEq K
end
end Astra7.NativeBudget
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false
namespace FrobeniusLocator.Native
noncomputable section
open Polynomial Finset CoreDefinitions Code
open ProximityPrize.Benchmark
local instance decidableScalarProtocol (P : Prop) : Decidable P := Classical.propDecidable P
end
end FrobeniusLocator.Native
end
