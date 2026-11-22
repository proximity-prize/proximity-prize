import ArkLib.Data.CodingTheory.ListDecodability.AgreementRadius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import ProximityPrize.SubmissionLower.Fast014
set_option Elab.async false
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
abbrev NativeK := IRSProfile.Field
abbrev NativeIndex := IRSProfile.Index
local instance : DecidableEq NativeK := Classical.decEq NativeK
theorem native_characteristic : ringChar NativeK = 2130706433 := by
  have : CharP NativeK 2130706433 := charP_of_injective_ringHom
    (f := algebraMap KoalaBear.Field NativeK) (algebraMap KoalaBear.Field NativeK).injective 2130706433
  exact ringChar.eq NativeK 2130706433
theorem native_charP : CharP NativeK 2130706433 := ringChar.of_eq native_characteristic
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
theorem rankTransport_sum_const (n bound : ℕ) :
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
local instance : DecidableEq NativeK := Classical.decEq NativeK
end
end Sol1.C42
end
section
namespace Sol1.C52
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open Sol1.C42
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
end
end Sol1.C52
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
theorem weighted_uniform_annihilator {F : Type u} [Field F]
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F) :
    ∃ Q : DifferentialPolynomial F 2, Q ≠ 0 ∧ jetTotalDegree Q ≤ 64 ∧
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
    exists_primitive_interpolant_of_rank_le.{u,0,0,u,u} 48 0 64 (fun i => domain i)
      (fun i => Polynomial.C (received i)) (by intro i; simp) columns
      columns_injective columns_y0_le phi hphi hrank strict_source_surplus
  let Qs : DifferentialPolynomial (Polynomial F) 2 := SourceColumn.interpolant columns v
  let psi : Polynomial F →+* F := Polynomial.evalRingHom 0
  let Q : DifferentialPolynomial F 2 := MvPolynomial.map psi Qs
  have hQ0 : Q ≠ 0 := by
    exact SourceColumn.map_interpolant_ne_zero columns_injective psi
      (Ideal.comp_ne_zero_of_span_range_eq_top hspan psi)
  have hjet : jetTotalDegree Q ≤ 64 :=
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
theorem regularPart_dvd (d : ℕ) (Q : DifferentialPolynomial F (d+1)) : regularPart d Q ∣ Q := by
  obtain ⟨R,hR⟩ := radicalPrimPart_dvd_self none (topReindex d Q)
  refine ⟨(topReindex d).symm R,?_⟩
  have hh := congrArg (topReindex d).symm hR
  simpa [regularPart] using hh
def weightedFullCharge : ℚ := weightedRegularCap+firstOrderCharge 4032
def weightedListCap : ℕ := 31911086374011223
def weightedMCAAllowance : ℕ := 243069641737383864
theorem weighted_budget_exact :
    weightedFullCharge=(386116366638676700141991232 : ℚ)/12099756245 ∧
    weightedFullCharge ≤ weightedListCap ∧
    (weightedListCap : ℚ)-1 < weightedFullCharge ∧
    weightedListCap+weightedMCAAllowance=274980728111395087 ∧
    123935685281173519-weightedListCap=92024598907162296 := by
  norm_num [weightedFullCharge,weightedRegularCap,firstOrderCharge,I1,b,
    weightedListCap,weightedMCAAllowance]
theorem weighted_second_order_card [CharP F 2130706433]
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F)
    (Q : DifferentialPolynomial F 2) (hQ : Q ≠ 0) (hjet : jetTotalDegree Q ≤ 64)
    (hwt : Q.weightedTotalDegree (jetWeight 1 4 3) ≤ 148)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received 131073 180265) :
    (S.card : ℚ) ≤ weightedFullCharge := by
  classical
  let G := regularPart 1 Q
  have hsplit := split_weight 1 Q
  have hGjet : jetTotalDegree G ≤ 64 := by dsimp [G]; omega
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
    have hlowjet : jetTotalDegree (lowerPart 1 Q) ≤ 4032 := by omega
    have hc := first_order_card_le domain received (lowerPart 1 Q) (lower_ne_zero 1 Q)
      4032 (by decide) hlowjet S hlow
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
    have hRjet : jetTotalDegree R ≤ 4032 := by
      have hh := exceptional_weight_sharp 1 Q 64 hjet
        (hbpos.trans_le (jetDegree_le_total G (Fin.last 2)))
      exact hh
    have he : (exceptional.card : ℚ) ≤ firstOrderCharge 4032 := by
      apply first_order_card_le domain received R hR 4032 (by decide) hRjet exceptional
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
      _ ≤ weightedRegularCap+firstOrderCharge 4032 := add_le_add hr he
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
def phi : Base →+* K := algebraMap Base K
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
theorem domain_card : D.card = 262144 := by
  rw [D, baseNodeSet_card]
  norm_num [Index, IRSProfile.Index]
theorem field_card : Fintype.card K = 2130706433 ^ 6 := by
  change Fintype.card KoalaBear.Ext6 = 2130706433 ^ 6
  rw [KoalaBear.card_ext6]
  rfl
theorem threshold : (Fintype.card Index : ℝ) * (1 - radius) ≤ (177505 : ℝ) := by
  norm_num [Index, IRSProfile.Index, radius]
theorem room : D.card + 131072 * (cap + 1) ^ 2 < Fintype.card K := by
  rw [domain_card, field_card]
  exact native_evaluation_separation_budget
def extendWord (w : Index → Base) : Base → Base :=
  Function.extend nodes w (fun _ ↦ 0)
@[simp] theorem extendWord_nodes (w : Index → Base) (i : Index) :
    extendWord w (nodes i) = w i := nodes.injective.extend_apply _ _ _
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
abbrev row8 := Fin 8
abbrev scalarCode : ModuleCode I K K := ReedSolomon.code IRSProfile.domain 131072
def radius : ℝ := Sol1.Reciprocal.Native.radius
def scalarDomain : Finset K := baseNodeSet IRSProfile.domain
local instance : DecidableEq K := Classical.decEq K
def ActualMCACap (B : ℕ) : Prop :=
  ∀ U : Fin 2 → I → row8 → K,
    {gamma | IsMCA (AffineLineGenerator K) IRSProfile.code gamma U radius}.ncard ≤ B
theorem lifted_id_domain : liftedDomain (RingHom.id K) IRSProfile.domain = IRSProfile.domain := by
  ext i
  rfl
theorem code_eq_id_repeat : IRSProfile.code =
    repeatedRS (RingHom.id K) IRSProfile.domain 131072 := by
  unfold IRSProfile.code ReedSolomon.Interleaved.irsCode repeatedRS
  rw [lifted_id_domain]
  rfl
theorem scalarDomain_card : scalarDomain.card = 262144 := by
  rw [scalarDomain, baseNodeSet_card]
  norm_num [I, IRSProfile.Index]
theorem separation_room (B : ℕ) (hB : B < 2 ^ 57) :
    scalarDomain.card + 131072 * (B + 1) ^ 2 < Fintype.card K := by
  have hpow : (B + 1) ^ 2 ≤ (2 ^ 57) ^ 2 :=
    Nat.pow_le_pow_left (show B + 1 ≤ 2 ^ 57 by omega) 2
  rw [scalarDomain_card]
  calc
    262144 + 131072 * (B + 1) ^ 2 ≤ 262144 + 131072 * (2 ^ 57) ^ 2 := by gcongr
    _ < Fintype.card K := by rw [Sol1.Reciprocal.Native.field_card]; norm_num
theorem projection_room (B : ℕ) (hB : B < 2 ^ 57) :
    (B + 1) ^ 2 ≤ Fintype.card K := by
  have hpow : (B + 1) ^ 2 ≤ (2 ^ 57) ^ 2 :=
    Nat.pow_le_pow_left (show B + 1 ≤ 2 ^ 57 by omega) 2
  exact hpow.trans (by rw [Sol1.Reciprocal.Native.field_card]; norm_num)
theorem scalar_pole_cap (B : ℕ) (hcap : ActualMCACap B) (w : K → K)
    (alpha : K) (halpha : ∀ x ∈ scalarDomain, x ≠ alpha) :
    (poleMCASet (RingHom.id K) scalarDomain w alpha 131072 177505).ncard ≤ B := by
  classical
  refine pole_cap_of_actual_cap (RingHom.id K) IRSProfile.domain w 131072 177505 B radius
    (by norm_num) (by norm_num) Sol1.Reciprocal.Native.threshold ?_ alpha halpha
  intro U
  rw [← code_eq_id_repeat]
  exact hcap U
theorem scalar_polynomial_list_cap (B : ℕ) (hB : B < 2 ^ 57)
    (hcap : ActualMCACap B) (w : K → K) :
    (baseCloseSet scalarDomain w 131072 177505).Finite ∧
      (baseCloseSet scalarDomain w 131072 177505).ncard ≤ B := by
  apply base_list_finite_ncard_le_of_pole_cap (RingHom.id K) scalarDomain w 131072 177505 B
    (by norm_num) (by norm_num) (separation_room B hB)
  exact scalar_pole_cap B hcap w
def extendScalarWord (w : I → K) : K → K :=
  Function.extend IRSProfile.domain w (fun _ ↦ 0)
@[simp] theorem extendScalarWord_domain (w : I → K) (i : I) :
    extendScalarWord w (IRSProfile.domain i) = w i :=
  IRSProfile.domain.injective.extend_apply _ _ _
theorem scalar_node_agreement_card (w : I → K) (P : K[X]) :
    (scalarDomain.filter fun x ↦ P.eval x = extendScalarWord w x).card =
      agreementCard (fun i ↦ P.eval (IRSProfile.domain i)) w := by
  classical
  symm
  apply Finset.card_bij (fun i _ ↦ IRSProfile.domain i)
  · intro i hi
    obtain ⟨_, hagree⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    exact ⟨(mem_baseNodeSet IRSProfile.domain (IRSProfile.domain i)).mpr ⟨i, rfl⟩,
      by simpa using hagree⟩
  · intro i _ j _ h
    exact IRSProfile.domain.injective h
  · intro x hx
    obtain ⟨hxD, hagree⟩ := Finset.mem_filter.mp hx
    obtain ⟨i, rfl⟩ := (mem_baseNodeSet IRSProfile.domain x).mp hxD
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hagree⟩, rfl⟩
theorem finset_scalar_list_card_le (B : ℕ) (hB : B < 2 ^ 57)
    (hcap : ActualMCACap B) (w : I → K) (P : Finset (I → K))
    (hP : ∀ f ∈ P, f ∈ scalarCode ∧ 177505 ≤ agreementCard f w) : P.card ≤ B := by
  classical
  have : NeZero (131072 : ℕ) := ⟨by norm_num⟩
  choose poly hdegree heval using fun f : P ↦
    ReedSolomon.mem_code_iff_eval_of_ne_zero.mp (hP f.val f.property).1
  have hinj : Function.Injective poly := by
    intro f g hfg
    apply Subtype.ext
    funext i
    calc
      f.val i = (poly f).eval (IRSProfile.domain i) := (heval f i).symm
      _ = (poly g).eval (IRSProfile.domain i) := by rw [hfg]
      _ = g.val i := heval g i
  let polys : Finset K[X] := Finset.univ.image poly
  have hpolyscard : polys.card = P.card := by
    dsimp [polys]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hpolys : (polys : Set K[X]) ⊆
      baseCloseSet scalarDomain (extendScalarWord w) 131072 177505 := by
    intro q hq
    obtain ⟨f, _hf, rfl⟩ := Finset.mem_image.mp hq
    refine ⟨(hdegree f).le, ?_⟩
    rw [scalar_node_agreement_card]
    have hword : (fun i ↦ (poly f).eval (IRSProfile.domain i)) = f.val := funext (heval f)
    rw [hword]
    exact (hP f.val f.property).2
  obtain ⟨hfinite, hbound⟩ := scalar_polynomial_list_cap B hB hcap (extendScalarWord w)
  have hcount := (Set.ncard_le_ncard hpolys hfinite).trans hbound
  have hcount' : polys.card ≤ B := by simpa only [Set.ncard_coe_finset] using hcount
  rwa [hpolyscard] at hcount'
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
theorem finset_squared_list_card_le (B : ℕ) (hB : B < 2 ^ 57)
    (hcap : ActualMCACap B) (w : I → A16) (P : Finset (I → A16))
    (hP : ∀ f ∈ P, f ∈ squaredCode ∧ 177505 ≤ agreementCard f w) : P.card ≤ B := by
  classical
  let flattened := P.image flatten
  have hflat : ∀ f ∈ flattened,
      (∀ r : R16, (fun i ↦ f i r) ∈ scalarCode) ∧
        177505 ≤ agreementCard f (flatten w) := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨hcode, hagree⟩ := hP g hg
    exact ⟨flatten_rows_mem g hcode, hagree.trans (flatten_agreement_le g w)⟩
  have hcount := finset_vector_list_card_le scalarCode 177505 B (projection_room B hB)
    (finset_scalar_list_card_le B hB hcap) (flatten w) flattened hflat
  have hcard : flattened.card = P.card := Finset.card_image_of_injective P flatten_injective
  rwa [hcard] at hcount
theorem close_agreement_ge (f w : I → A16)
    (hd : (δᵣ(w, f) : ℝ) ≤ radius) : 177505 ≤ agreementCard f w := by
  classical
  have hpos : 0 < Fintype.card I := by norm_num [I, IRSProfile.Index]
  have hradius : radius = 1 - ((710019 : ℝ) / 4) / Fintype.card I := by
    norm_num [radius, Sol1.Reciprocal.Native.radius, I, IRSProfile.Index]
  have hagree : (710019 : ℝ) / 4 ≤ Code.agree f w :=
    (Code.relHammingDist_le_one_sub_div_iff hpos).mp (by rwa [← hradius])
  change 177505 ≤ Code.agree f w
  by_contra hsmall
  have hn : Code.agree f w ≤ 177504 := by omega
  have hr : (Code.agree f w : ℝ) ≤ 177504 := by exact_mod_cast hn
  linarith
theorem squared_lambda_le (B : ℕ) (hB : B < 2 ^ 57) (hcap : ActualMCACap B) :
    Code.Lambda (squaredCode : Set (I → A16)) radius ≤ (B : ℕ∞) := by
  classical
  apply Code.Lambda_le_iff_forall_encard_le.mpr
  intro w
  have hfinite : (Code.closeCodewordsRel (squaredCode : Set (I → A16)) w radius).Finite :=
    Set.toFinite _
  have hcard : hfinite.toFinset.card ≤ B := by
    apply finset_squared_list_card_le B hB hcap w hfinite.toFinset
    intro f hf
    obtain ⟨hcode, hclose⟩ := Code.mem_closeCodewordsRel_iff.mp (hfinite.mem_toFinset.mp hf)
    exact ⟨hcode, close_agreement_ge f w hclose⟩
  calc
    (Code.closeCodewordsRel (squaredCode : Set (I → A16)) w radius).encard =
        (hfinite.toFinset.card : ℕ∞) := hfinite.encard_eq_coe_toFinset_card
    _ ≤ (B : ℕ∞) := by exact_mod_cast hcard
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
def radius6915 : ℝ := (queryRadius : ℝ)
theorem finset_scalar_list_card_le (w : I → K) (P : Finset (I → K))
    (hP : ∀ f ∈ P, f ∈ scalarCode ∧ 180265 ≤ agreementCard f w) : P.card ≤ Astra7.weightedListCap := by
  classical
  have : NeZero (131072 : ℕ) := ⟨by norm_num⟩
  choose poly hdegree heval using fun f : P ↦
    ReedSolomon.mem_code_iff_eval_of_ne_zero.mp (hP f.val f.property).1
  have hinj : Function.Injective poly := by
    intro f g hfg
    apply Subtype.ext
    funext i
    calc
      f.val i = (poly f).eval (IRSProfile.domain i) := (heval f i).symm
      _ = (poly g).eval (IRSProfile.domain i) := by rw [hfg]
      _ = g.val i := heval g i
  let polys : Finset K[X] := Finset.univ.image poly
  have hpolyscard : polys.card = P.card := by
    dsimp [polys]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hpolys : (polys : Set K[X]) ⊆
      ReedSolomon.closePolynomialSet IRSProfile.domain w 131073 180265 := by
    intro q hq
    obtain ⟨f,_hf,rfl⟩ := Finset.mem_image.mp hq
    refine ⟨?_, ?_⟩
    · have hd : (poly f).natDegree < 131073 := (hdegree f).trans (by norm_num)
      exact (Polynomial.degree_le_natDegree).trans_lt (by exact_mod_cast hd)
    · have hword : (fun i ↦ (poly f).eval (IRSProfile.domain i)) = f.val := funext (heval f)
      change 180265 ≤ agreementCard (fun i ↦ (poly f).eval (IRSProfile.domain i)) w
      rw [hword]
      exact (hP f.val f.property).2
  obtain ⟨hfinite,hbound⟩ := Astra7.native_weighted_complete_list w
  have hcount := (Set.ncard_le_ncard hpolys hfinite).trans hbound
  have hcount' : polys.card ≤ Astra7.weightedListCap := by simpa only [Set.ncard_coe_finset] using hcount
  rwa [hpolyscard] at hcount'
theorem list_projection_room : (Astra7.weightedListCap + 1) ^ 2 ≤ Fintype.card K :=
  projection_room Astra7.weightedListCap (by norm_num [Astra7.weightedListCap])
theorem finset_squared_list_card_le (w : I → A16) (P : Finset (I → A16))
    (hP : ∀ f ∈ P, f ∈ squaredCode ∧ 180265 ≤ agreementCard f w) : P.card ≤ Astra7.weightedListCap := by
  classical
  let flattened := P.image flatten
  have hflat : ∀ f ∈ flattened,
      (∀ r : R16, (fun i ↦ f i r) ∈ scalarCode) ∧
        180265 ≤ agreementCard f (flatten w) := by
    intro f hf
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨hcode,hagree⟩ := hP g hg
    exact ⟨flatten_rows_mem g hcode,hagree.trans (flatten_agreement_le g w)⟩
  have hcount := finset_vector_list_card_le scalarCode 180265 Astra7.weightedListCap list_projection_room
    finset_scalar_list_card_le (flatten w) flattened hflat
  have hcard : flattened.card = P.card := Finset.card_image_of_injective P flatten_injective
  rwa [hcard] at hcount
theorem close_agreement_ge (f w : I → A16)
    (hd : (δᵣ(w,f) : ℝ) ≤ radius6915) : 180265 ≤ agreementCard f w := by
  classical
  have hpos : 0 < Fintype.card I := by norm_num [I,IRSProfile.Index]
  have hradius : radius6915 = 1 - (180265 : ℝ) / Fintype.card I := by
    norm_num [radius6915,queryRadius,claimedRadius,I,IRSProfile.Index]
  have hagree : (180265 : ℝ) ≤ Code.agree f w :=
    (Code.relHammingDist_le_one_sub_div_iff hpos).mp (by rwa [← hradius])
  exact_mod_cast hagree
theorem squared_lambda_le :
    Code.Lambda (squaredCode : Set (I → A16)) radius6915 ≤ (Astra7.weightedListCap : ℕ∞) := by
  classical
  apply Code.Lambda_le_iff_forall_encard_le.mpr
  intro w
  have hfinite : (Code.closeCodewordsRel (squaredCode : Set (I → A16)) w radius6915).Finite :=
    Set.toFinite _
  have hcard : hfinite.toFinset.card ≤ Astra7.weightedListCap := by
    apply finset_squared_list_card_le w hfinite.toFinset
    intro f hf
    obtain ⟨hcode,hclose⟩ := Code.mem_closeCodewordsRel_iff.mp (hfinite.mem_toFinset.mp hf)
    exact ⟨hcode,close_agreement_ge f w hclose⟩
  calc
    (Code.closeCodewordsRel (squaredCode : Set (I → A16)) w radius6915).encard =
        (hfinite.toFinset.card : ℕ∞) := hfinite.encard_eq_coe_toFinset_card
    _ ≤ (Astra7.weightedListCap : ℕ∞) := by exact_mod_cast hcard
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
def ScalarMCACap6915 : Prop :=
  ∀ (u : Fin 2 → I → K) (Γ : Finset K),
    (∀ γ ∈ Γ, IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u radius) →
    Γ.card ≤ Astra7.weightedMCAAllowance
end
end FrobeniusLocator.Native
end
