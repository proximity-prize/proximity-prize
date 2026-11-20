import ProximityPrize.SubmissionLower.Fast015
import ProximityPrize.SubmissionLower.List6927Rank

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

namespace List6921

open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial
open List6927Source (columns point_rank_le_origin columns_injective columns_y0_le
  columns_total_le columns_weight147 columns_weight_lt)
open List6927Rank (blockUpper origin_rank strict_source_surplus)
open Astra7 (jetWeight generic_source_weight_le generic_source_weight_lt)
open scoped BigOperators


noncomputable section

private theorem constraint_matrix_map {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (centers received : Fin 262144 → R) :
    (localConstraintMatrix 49 centers received columns).map phi =
      localConstraintMatrix 49 (fun i => phi (centers i)) (fun i => phi (received i)) columns := by
  ext row j
  simp only [Matrix.map_apply, localConstraintMatrix_apply]
  rw [← MvPolynomial.coeff_map, map_unscaledLocalSubstitution]
  simp [SourceColumn.polynomial]

private theorem rank_sum_const (n bound : ℕ) : (∑ _i : Fin n, bound) = n * bound := by
  simp

private theorem global_rank_le {R F : Type*} [CommRing R] [Field F]
    (centers received : Fin 262144 → R) (phi : R →+* F) :
    ((localConstraintMatrix 49 centers received columns).map phi).rank ≤ 262144 * blockUpper := by
  classical
  rw [constraint_matrix_map]
  apply (Matrix.rank_prod_rows_le_sum _).trans
  calc
    (∑ i : Fin 262144, Matrix.rank (fun row j =>
      localConstraintMatrix 49 (fun k => phi (centers k))
        (fun k => phi (received k)) columns (i,row) j)) ≤
        ∑ _i : Fin 262144, blockUpper := by
      apply Finset.sum_le_sum
      intro i _
      exact (point_rank_le_origin 49 (phi (centers i)) (phi (received i))).trans origin_rank
    _ = 262144 * blockUpper := rank_sum_const 262144 blockUpper

universe u
attribute [local instance] Classical.propDecidable


theorem extended_uniform_annihilator {F : Type u} [Field F]
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F) :
    ∃ Q : DifferentialPolynomial F 2, Q ≠ 0 ∧ jetTotalDegree Q ≤ 67 ∧
      Q.weightedTotalDegree (jetWeight 1 4 3) ≤ 147 ∧
      ∀ P ∈ ReedSolomon.closePolynomialSet domain received 131073 180139,
        differentialSpecialization Q P=0 := by
  classical
  let K := FractionRing (Polynomial F)
  let phi : Polynomial F →+* K := algebraMap (Polynomial F) K
  have hphi : Function.Injective phi := IsFractionRing.injective (Polynomial F) K
  have hrank : ((localConstraintMatrix 49 (fun i => Polynomial.C (domain i))
      (fun i => Polynomial.C (received i)) columns).map phi).rank ≤ 262144 * blockUpper :=
    global_rank_le (fun i => Polynomial.C (domain i)) (fun i => Polynomial.C (received i)) phi
  obtain ⟨v,_,hvdegree,hspan,_,hconstraints⟩ :=
    exists_primitive_interpolant_of_rank_le.{u,0,0,u,u} 49 0 67 (fun i => domain i)
      (fun i => Polynomial.C (received i)) (by intro i; simp) columns
      columns_injective columns_y0_le phi hphi hrank strict_source_surplus
  let Qs : DifferentialPolynomial (Polynomial F) 2 := SourceColumn.interpolant columns v
  let psi : Polynomial F →+* F := Polynomial.evalRingHom 0
  let Q : DifferentialPolynomial F 2 := MvPolynomial.map psi Qs
  have hQ0 : Q ≠ 0 := by
    exact SourceColumn.map_interpolant_ne_zero columns_injective psi
      (Ideal.comp_ne_zero_of_span_range_eq_top hspan psi)
  have hjet : jetTotalDegree Q ≤ 67 :=
    SourceColumn.map_interpolant_jetTotalDegree_le psi columns columns_total_le v
  have hwt : Q.weightedTotalDegree (jetWeight 1 4 3) ≤ 147 :=
    generic_source_weight_le psi columns v (jetWeight 1 4 3) 147 columns_weight147
  refine ⟨Q,hQ0,hjet,hwt,?_⟩
  intro P hP
  have hPdegree : P.natDegree ≤ 131072 := by
    by_cases hz : P=0
    · simp [hz]
    · have hh := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hP.1
      omega
  have hQweight : differentialWeightedDegree 131072 Q < 49*180139 :=
    generic_source_weight_lt psi columns v (differentialWeight 131072) (49*180139)
      (by decide) columns_weight_lt
  have hlocal : ∀ i, SatisfiesLocalConstraints 49 (domain i) (received i) Q := by
    intro i
    have hh := SatisfiesLocalConstraints.map psi 49 (Polynomial.C (domain i))
      (Polynomial.C (received i)) Qs (hconstraints i)
    simpa [psi,Q] using hh
  let indices := ReedSolomon.polynomialAgreementSet domain received P
  apply differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
    domain received indices hQweight (fun i _ => hlocal i) P hPdegree
    domain.injective.injOn hP.2
  intro i hi
  exact (Finset.mem_filter.mp hi).2


end
end List6921

namespace List6921

open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial
open Sol1.C42 Sol1.C57 Astra7

noncomputable section
variable {F E : Type*} [Field F] [Field E] [CharP E 2130706433]

def I1 : ℚ := 131072 / 49067
def firstOrderCharge (h : ℕ) : ℚ := I1 * h * b h + (h : ℚ) * (h - 1)

def weightedRegularCap : ℚ := (147 : ℚ) / 45 *
  (((131072 : ℚ)*36700437)/49067)^2

private theorem characteristic_not_dvd_weight (j : Fin 3) :
    ¬ 2130706433 ∣ 1 + 4 * j.val := by
  apply Nat.not_dvd_of_pos_of_lt
  · positivity
  · have hj := j.isLt
    omega

theorem weighted_regular_card [CharP F 2130706433]
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F)
    (Q : DifferentialPolynomial F 2)
    (hQ : Q.weightedTotalDegree (jetWeight 1 4 3) ≤ 147)
    (S : Finset (Polynomial F))
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last 2)) P ≠ 0)
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received 131073 180139) :
    (S.card : ℚ) ≤ weightedRegularCap := by
  classical
  have hchar : ∀ j : Fin 3, ((1+4*j.val : ℕ) : F) ≠ 0 := by
    intro j hz
    exact characteristic_not_dvd_weight j
      ((CharP.cast_eq_zero_iff F 2130706433 (1 + 4 * j.val)).mp hz)
  have hh := weighted_regular_polynomial_card (r := 2) (n := 262144) (k := 131073) (A := 180139)
    1 4 147 (by decide) (by decide) hchar Q hQ
    (by decide) (by decide) domain received Astra7.native_choose_two S
    (fun P hP => (hS P hP).2.1) (fun P hP => (hS P hP).1) hsep
    (fun P hP => (hS P hP).2.2)
  norm_num [chartBound,Fin.prod_univ_succ] at hh
  dsimp [weightedRegularCap]
  linarith


theorem regular_top_card_le_at_agreement (d : ℕ) (hd : d ≤ 2)
    (domain : Fin 262144 ↪ E) (received : Fin 262144 → E)
    (Q : DifferentialPolynomial E d) (nu : ℕ)
    (hhighest : highestActiveJet Q = some (Fin.last d)) (hweight : jetTotalDegree Q ≤ nu)
    (S : Finset E[X])
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last d)) P ≠ 0)
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received 131073 180139) :
    (S.card : ℚ) ≤ dimensionSensitiveIncidenceProduct 262144 180139 131073 1 d * nu *
      ((1 + 2 * 131073 * (nu - 1) : ℕ) : ℚ) ^ d := by
  have hactual := finite_actualStage_regularSolutions_card_le_dimensionSensitive Q (Fin.last d)
    hhighest 131073 131073 (by omega) le_rfl domain received (by norm_num) (by norm_num)
    (fun r hr ↦ Sol1.C40Primitives.native_binomial_guard r (hr.trans hd)) S hsep hS
  exact hactual.trans (directJetStageCharge_le_weight_order (Q, Fin.last d)
    262144 180139 131073 131073 nu d (by norm_num) hweight (by simp))
theorem incidence_one : dimensionSensitiveIncidenceProduct 262144 180139 131073 1 1 = I1 := by
  norm_num [dimensionSensitiveIncidenceProduct, I1]
theorem firstOrderCharge_ge (h : ℕ) : (h : ℚ) ≤ firstOrderCharge h := by
  have hi : (1 : ℚ) ≤ I1 := by norm_num [I1]
  have hI : 0 ≤ I1 := by norm_num [I1]
  have hb : (1 : ℚ) ≤ (b h : ℚ) := by
    exact_mod_cast (by unfold b; omega : 1 ≤ b h)
  have hprod : 0 ≤ (h : ℚ) * (h - 1) := by
    rw [← Sol1.C57.cast_mul_pred]
    positivity
  have h1 : (h : ℚ) ≤ I1 * h := by nlinarith [Nat.cast_nonneg (α := ℚ) h]
  have h2 : I1 * h ≤ I1 * h * b h :=
    le_mul_of_one_le_right (mul_nonneg hI (Nat.cast_nonneg _)) hb
  exact (h1.trans h2).trans (le_add_of_nonneg_right hprod)

/-- Sharp whole first-order fixed-word consumer, including every singular/lower-order root. -/
theorem first_order_card_le_at_agreement
    (domain : Fin 262144 ↪ E) (received : Fin 262144 → E)
    (Q : DifferentialPolynomial E 1) (hQ : Q ≠ 0) (h : ℕ) (hbound : h < 2130706433)
    (hweight : jetTotalDegree Q ≤ h) (S : Finset E[X])
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received 131073 180139) :
    (S.card : ℚ) ≤ firstOrderCharge h := by
  classical
  let G := regularPart 0 Q
  have hsplit := split_weight 0 Q
  have hGweight : jetTotalDegree G ≤ h := by dsimp [G]; omega
  have hchar : ringChar E = 0 ∨ jetDegree Q (Fin.last 1) < ringChar E := by
    right
    rw [ringChar.eq E 2130706433]
    have hh := jetDegree_le_total Q (Fin.last 1)
    omega
  by_cases hb : jetDegree G (Fin.last 1) = 0
  · have hGone : G = 1 := regular_eq_one_of_degree_zero 0 Q hb
    have hlow : ∀ P ∈ S, differentialSpecialization (lowerPart 0 Q) P = 0 := by
      intro P hP
      rcases root_split 0 Q hQ P (hS P hP).1 with hc | hr
      · exact hc
      · change differentialSpecialization G P = 0 at hr
        rw [hGone] at hr
        have hz : (1 : E[X]) = 0 := by
          simpa only [differentialSpecialization, map_one] using hr
        exact (one_ne_zero hz).elim
    have hc := order_zero_card_le (lowerPart 0 Q) (lower_ne_zero 0 Q) S hlow
    have hch : S.card ≤ h := by omega
    exact (by exact_mod_cast hch : (S.card : ℚ) ≤ h).trans (firstOrderCharge_ge h)
  · have hbpos : 0 < jetDegree G (Fin.last 1) := by omega
    let good : E[X] → Prop := fun P ↦ differentialSpecialization G P = 0 ∧
      differentialSpecialization (separant G (Fin.last 1)) P ≠ 0
    let regular := S.filter good
    let exceptional := S.filter fun P ↦ ¬ good P
    have hreg : (regular.card : ℚ) ≤ I1 * h * b h := by
      have hx := regular_top_card_le_at_agreement 1 (by norm_num) domain received G h
        (highestActiveJet_last_of_pos G hbpos) hGweight regular
        (by intro P hP; exact ((Finset.mem_filter.mp hP).2).2)
        (by
          intro P hP
          have hp := Finset.mem_filter.mp hP
          exact ⟨hp.2.1,(hS P hp.1).2⟩)
      simpa only [incidence_one, pow_one, b] using hx
    let R := exceptionalEquation 0 Q
    have hR : R ≠ 0 := exceptional_ne_zero 0 Q hchar
    have hRweight : jetTotalDegree R ≤ h * (h - 1) :=
      exceptional_weight_sharp 0 Q h hweight
        (hbpos.trans_le (jetDegree_le_total G (Fin.last 1)))
    have hexc : exceptional.card ≤ h * (h - 1) := by
      apply (order_zero_card_le R hR exceptional ?_).trans hRweight
      intro P hP
      have hp := Finset.mem_filter.mp hP
      rcases root_regular_or_exceptional 0 Q hQ P (hS P hp.1).1 hbpos with hg | he
      · exact (hp.2 hg).elim
      · exact he
    have hcard : regular.card + exceptional.card = S.card :=
      Finset.card_filter_add_card_filter_not (s := S) (p := good)
    calc
      (S.card : ℚ) = (regular.card : ℚ) + exceptional.card := by exact_mod_cast hcard.symm
      _ ≤ I1 * h * b h + ((h * (h - 1) : ℕ) : ℚ) :=
        add_le_add hreg (by exact_mod_cast hexc)
      _ = firstOrderCharge h := by rw [Sol1.C57.cast_mul_pred]; rfl
def weightedFullCharge : ℚ := weightedRegularCap + firstOrderCharge 4422
def weightedListCap : ℕ := 31410688579691704

theorem weighted_budget_exact : weightedFullCharge ≤ weightedListCap := by
  norm_num [weightedFullCharge, weightedRegularCap, firstOrderCharge, I1, b, weightedListCap]

theorem weighted_second_order_card [CharP F 2130706433]
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F)
    (Q : DifferentialPolynomial F 2) (hQ : Q ≠ 0) (hjet : jetTotalDegree Q ≤ 67)
    (hwt : Q.weightedTotalDegree (jetWeight 1 4 3) ≤ 147)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received 131073 180139) :
    (S.card : ℚ) ≤ weightedFullCharge := by
  classical
  let G := regularPart 1 Q
  have hsplit := split_weight 1 Q
  have hGjet : jetTotalDegree G ≤ 67 := by dsimp [G]; omega
  have hGwt : G.weightedTotalDegree (jetWeight 1 4 3) ≤ 147 :=
    (weightedTotalDegree_le_of_dvd (jetWeight 1 4 3) (Astra7.regularPart_dvd 1 Q) hQ).trans hwt
  have hchar : ringChar F=0 ∨ jetDegree Q (Fin.last 2) < ringChar F := by
    right
    rw [ringChar.eq F 2130706433]
    have hh := jetDegree_le_total Q (Fin.last 2)
    omega
  have hcost : 0 ≤ weightedRegularCap := by unfold weightedRegularCap; positivity
  by_cases hb : jetDegree G (Fin.last 2)=0
  · have hGone : G=1 := regular_eq_one_of_degree_zero 1 Q hb
    have hlow : ∀ P ∈ S, P ∈ directJetAgreementSolutions (lowerPart 1 Q)
        domain received 131073 180139 := by
      intro P hP
      refine ⟨?_,(hS P hP).2⟩
      rcases root_split 1 Q hQ P (hS P hP).1 with hc | hr
      · exact hc
      · change differentialSpecialization G P=0 at hr
        rw [hGone] at hr
        have hz : (1 : F[X])=0 := by
          simpa only [differentialSpecialization,map_one] using hr
        exact (one_ne_zero hz).elim
    have hlowjet : jetTotalDegree (lowerPart 1 Q) ≤ 4422 := by omega
    have hc := first_order_card_le_at_agreement domain received (lowerPart 1 Q) (lower_ne_zero 1 Q)
      4422 (by decide) hlowjet S hlow
    exact hc.trans (le_add_of_nonneg_left hcost)
  · have hbpos : 0 < jetDegree G (Fin.last 2) := by omega
    let good : F[X] → Prop := fun P => differentialSpecialization G P=0 ∧
      differentialSpecialization (separant G (Fin.last 2)) P ≠ 0
    let regular := S.filter good
    let exceptional := S.filter fun P => ¬good P
    have hr : (regular.card : ℚ) ≤ weightedRegularCap := by
      apply weighted_regular_card domain received G hGwt regular
      · intro P hP
        exact ((Finset.mem_filter.mp hP).2).2
      · intro P hP
        have hp := Finset.mem_filter.mp hP
        exact ⟨hp.2.1,(hS P hp.1).2⟩
    let R := exceptionalEquation 1 Q
    have hR : R ≠ 0 := exceptional_ne_zero 1 Q hchar
    have hRjet : jetTotalDegree R ≤ 4422 := by
      have hh := exceptional_weight_sharp 1 Q 67 hjet
        (hbpos.trans_le (jetDegree_le_total G (Fin.last 2)))
      exact hh
    have he : (exceptional.card : ℚ) ≤ firstOrderCharge 4422 := by
      apply first_order_card_le_at_agreement domain received R hR 4422 (by decide) hRjet exceptional
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
      _ ≤ weightedRegularCap+firstOrderCharge 4422 := add_le_add hr he
      _ = weightedFullCharge := rfl

attribute [local instance] Classical.propDecidable

theorem weighted_complete_list [CharP F 2130706433]
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F) :
    (ReedSolomon.closePolynomialSet domain received 131073 180139).Finite ∧
      (ReedSolomon.closePolynomialSet domain received 131073 180139).ncard ≤ weightedListCap := by
  classical
  obtain ⟨Q,hQ,hjet,hwt,hsound⟩ := extended_uniform_annihilator domain received
  have hf : ∀ S : Finset F[X],
      (S : Set F[X]) ⊆ ReedSolomon.closePolynomialSet domain received 131073 180139 →
      S.card ≤ weightedListCap := by
    intro S hS
    have hh := weighted_second_order_card domain received Q hQ hjet hwt S
      (fun P hP => ⟨hsound P (hS hP),hS hP⟩)
    exact_mod_cast hh.trans weighted_budget_exact
  have hfin : (ReedSolomon.closePolynomialSet domain received 131073 180139).Finite := by
    by_contra hi
    obtain ⟨S,hS,hcard⟩ := Set.Infinite.exists_subset_card_eq hi (weightedListCap+1)
    have hh := hf S hS
    omega
  refine ⟨hfin,?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact hf hfin.toFinset (fun P hP => hfin.mem_toFinset.mp hP)

local instance : DecidableEq Sol1.C42.NativeK := Classical.decEq _

theorem native_weighted_complete_list (received : Sol1.C42.NativeIndex → Sol1.C42.NativeK) :
    (ReedSolomon.closePolynomialSet ProximityPrize.Benchmark.IRSProfile.domain received 131073 180139).Finite ∧
      (ReedSolomon.closePolynomialSet ProximityPrize.Benchmark.IRSProfile.domain received 131073 180139).ncard ≤
        weightedListCap := by
  let := Sol1.C42.native_charP
  exact weighted_complete_list ProximityPrize.Benchmark.IRSProfile.domain received

end
end List6921

namespace List6921.Native
noncomputable section
open Polynomial Code LinearCode CoreDefinitions
open ProximityPrize.Benchmark Sol1.OneCount Sol1.FiniteRowProjection Sol1.C42
set_option maxRecDepth 10000
set_option maxHeartbeats 0

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq A16 := Classical.decEq A16

def radius6921 : ℝ := (335893008 : ℝ) / 1073741824

/-- Original scalar RS words lie in the proved augmented ordinary polynomial list. -/
theorem finset_scalar_list_card_le (w : I → K) (P : Finset (I → K))
    (hP : ∀ f ∈ P, f ∈ scalarCode ∧ 180139 ≤ agreementCard f w) : P.card ≤ List6921.weightedListCap := by
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
      ReedSolomon.closePolynomialSet IRSProfile.domain w 131073 180139 := by
    intro q hq
    obtain ⟨f,_hf,rfl⟩ := Finset.mem_image.mp hq
    refine ⟨?_, ?_⟩
    · have hd : (poly f).natDegree < 131073 := (hdegree f).trans (by norm_num)
      exact (Polynomial.degree_le_natDegree).trans_lt (by exact_mod_cast hd)
    · have hword : (fun i ↦ (poly f).eval (IRSProfile.domain i)) = f.val := funext (heval f)
      change 180139 ≤ agreementCard (fun i ↦ (poly f).eval (IRSProfile.domain i)) w
      rw [hword]
      exact (hP f.val f.property).2
  obtain ⟨hfinite,hbound⟩ := List6921.native_weighted_complete_list w
  have hcount := (Set.ncard_le_ncard hpolys hfinite).trans hbound
  have hcount' : polys.card ≤ List6921.weightedListCap := by simpa only [Set.ncard_coe_finset] using hcount
  rwa [hpolyscard] at hcount'

theorem list_projection_room : (List6921.weightedListCap + 1) ^ 2 ≤ Fintype.card K :=
  projection_room List6921.weightedListCap (by norm_num [List6921.weightedListCap])

/-- The actual alphabet is Fin2 -> Fin8 -> K; flattening only reindexes its rows. -/
theorem finset_squared_list_card_le (w : I → A16) (P : Finset (I → A16))
    (hP : ∀ f ∈ P, f ∈ squaredCode ∧ 180139 ≤ agreementCard f w) : P.card ≤ List6921.weightedListCap := by
  classical
  let flattened := P.image flatten
  have hflat : ∀ f ∈ flattened,
      (∀ r : R16, (fun i ↦ f i r) ∈ scalarCode) ∧
        180139 ≤ agreementCard f (flatten w) := by
    intro f hf
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨hcode,hagree⟩ := hP g hg
    exact ⟨flatten_rows_mem g hcode,hagree.trans (flatten_agreement_le g w)⟩
  have hcount := finset_vector_list_card_le scalarCode 180139 List6921.weightedListCap list_projection_room
    finset_scalar_list_card_le (flatten w) flattened hflat
  have hcard : flattened.card = P.card := Finset.card_image_of_injective P flatten_injective
  rwa [hcard] at hcount

theorem close_agreement_ge (f w : I → A16)
    (hd : (δᵣ(w,f) : ℝ) ≤ radius6921) : 180139 ≤ agreementCard f w := by
  classical
  have hpos : 0 < Fintype.card I := by norm_num [I,IRSProfile.Index]
  have hradius : radius6921 ≤ 1 - (360277 / 2 : ℝ) / Fintype.card I := by
    norm_num [radius6921,I,IRSProfile.Index]
  have hagree : (360277 / 2 : ℝ) ≤ Code.agree f w :=
    (Code.relHammingDist_le_one_sub_div_iff hpos).mp (hd.trans hradius)
  have hcast : (180138 : ℝ) < (agreementCard f w : ℝ) := by
    change (360277 / 2 : ℝ) ≤ (agreementCard f w : ℝ) at hagree
    linarith
  exact Nat.succ_le_of_lt (by exact_mod_cast hcast)
/-- Actual maximized independent IRS16 list term, with no MCA or list hypothesis. -/
theorem squared_lambda_le :
    Code.Lambda (squaredCode : Set (I → A16)) radius6921 ≤ (List6921.weightedListCap : ℕ∞) := by
  classical
  apply Code.Lambda_le_iff_forall_encard_le.mpr
  intro w
  have hfinite : (Code.closeCodewordsRel (squaredCode : Set (I → A16)) w radius6921).Finite :=
    Set.toFinite _
  have hcard : hfinite.toFinset.card ≤ List6921.weightedListCap := by
    apply finset_squared_list_card_le w hfinite.toFinset
    intro f hf
    obtain ⟨hcode,hclose⟩ := Code.mem_closeCodewordsRel_iff.mp (hfinite.mem_toFinset.mp hf)
    exact ⟨hcode,close_agreement_ge f w hclose⟩
  calc
    (Code.closeCodewordsRel (squaredCode : Set (I → A16)) w radius6921).encard =
        (hfinite.toFinset.card : ℕ∞) := hfinite.encard_eq_coe_toFinset_card
    _ ≤ (List6921.weightedListCap : ℕ∞) := by exact_mod_cast hcard

/-- Expanded actual-code benchmark form. -/
theorem actual_squared_lambda_le :
    Code.Lambda
      ((IRSProfile.code ^⋈ (Fin 2) : ModuleCode I K A16) : Set (I → A16)) radius6921 ≤ (List6921.weightedListCap : ℕ∞) := squared_lambda_le

end
end List6921.Native
