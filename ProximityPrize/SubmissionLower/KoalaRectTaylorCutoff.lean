import ProximityPrize.SubmissionLower.KoalaRectTaylorEval
import ProximityPrize.SubmissionLower.KoalaRuledEmbedding
import ProximityPrize.SubmissionLower.KoalaTwoCutStable -- serialize candidate build

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace KoalaRectTaylor
noncomputable section

open P1 (K p)
open K1_14 (FX)
open HighCore82219Upper (Input ResidueLift Factors rootOn)
open HighCore82219Upper_3 (JetRing RelativeSection graphIdeal jetDegree markPoint
  oldNumerator oldDenominator jetDenominator residueInJet openFactor rootIdeal tangentEquation)
open HighCore82219Upper_3_2 (CutoffAgreement cutoff_le_mark graph_le_prime mark_regular)
open private HighCore82219Upper_2.jet_poly
  HighCore82219Upper_5_1.marked_coefficient HighCore82219Upper_3_3_1.mark_biform
  HighCore82219Upper_3.oldDenominator_eq
  HighCore82219Upper_3_1.represent_quotient
  HighCore82219Upper_3_2_1.regular_of_kernel
  from ProximityPrize.SubmissionLower.HighCore82219UpperGeometry

def firstCut (J : Input) (B : ResidueLift J) : JetRing :=
  taylorNumerator J B (J.ell + 1) (J.ell + 1)

def secondCut (J : Input) (B : ResidueLift J) : JetRing :=
  taylorNumerator J B (J.ell + 2) (J.ell + 2)

theorem mark_graph_le (J : Input) (B : ResidueLift J) (D : Factors J B) {γ : K}
    (hγ : γ ∈ J.marks) (hproper : rootOn J D.proper γ) :
    graphIdeal J B D ≤ RingHom.ker (markPoint J γ).toRingHom :=
  graph_le_prime (RingHom.ker_isPrime (markPoint J γ).toRingHom)
    (cutoff_le_mark J B D hγ hproper) (mark_regular J B hγ)

theorem mark_open_ne_zero (J : Input) (B : ResidueLift J) {γ : K} (hγ : γ ∈ J.marks) :
    markPoint J γ (openFactor J B) ≠ 0 :=
  mark_regular J B hγ

theorem mark_oldNumerator_zero (J : Input) (B : ResidueLift J) {γ : K} (hγ : γ ∈ J.marks)
    {r : ℕ} (hell : J.ell < r) (hp : r < p) :
    markPoint J γ (oldNumerator J B r) = 0 := by
  obtain ⟨T, hdegree, hT⟩ := HighCore82219Upper_2.marked_quotient J B γ hγ
  rw [oldNumerator, HighCore82219Upper_3_3_1.mark_biform,
    HighCore82219Upper_5_1.marked_coefficient J B γ hγ T hT hp,
    HighCore82219Upper_2.jet_poly T hp]
  have h : (Polynomial.taylor HighCore82219Upper.center
      (T.map HighCore82219Upper.constantAbscissa)).coeff r = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [Polynomial.natDegree_taylor]
    exact Polynomial.natDegree_map_le.trans_lt (hdegree.trans_lt hell)
  rw [h, mul_zero]

theorem mark_cutoff_zero (J : Input) (B : ResidueLift J) (D : Factors J B) {γ : K}
    (hγ : γ ∈ J.marks) (hproper : rootOn J D.proper γ) {r : ℕ} (hell : J.ell < r) (hp : r < p) :
    markPoint J γ (taylorNumerator J B r r) = 0 := by
  apply (numerator_zero_iff J B D (markPoint J γ)
    (fun _ h => mark_graph_le J B D hγ hproper h)
    (mark_open_ne_zero J B hγ) le_rfl).mpr
  exact mark_oldNumerator_zero J B hγ hell hp

theorem second_order_lt_char (J : Input) : J.ell + 2 < p := by
  change 131071 - J.w + 2 < 2130706433
  omega

theorem mark_firstCut (J : Input) (B : ResidueLift J) (D : Factors J B) {γ : K}
    (hγ : γ ∈ J.marks) (hproper : rootOn J D.proper γ) :
    markPoint J γ (firstCut J B) = 0 := by
  have hp := second_order_lt_char J
  exact mark_cutoff_zero J B D hγ hproper (by omega) (by omega)

theorem mark_secondCut (J : Input) (B : ResidueLift J) (D : Factors J B) {γ : K}
    (hγ : γ ∈ J.marks) (hproper : rootOn J D.proper γ) :
    markPoint J γ (secondCut J B) = 0 :=
  mark_cutoff_zero J B D hγ hproper (by omega) (second_order_lt_char J)

theorem denominator_notMem {J : Input} {B : ResidueLift J} {P : Ideal JetRing}
    (hP : P.IsPrime) (hopen : openFactor J B ∉ P) (n : ℕ) :
    residueInJet B * Polynomial.C J.f.derivative ^ n ∉ P := by
  have hB : residueInJet B ∉ P := fun hm => hopen (Ideal.mul_mem_right _ _ hm)
  have hs : Polynomial.C J.f.derivative ∉ P := fun hm => hopen (P.mul_mem_left _ hm)
  intro hm
  exact (hP.mul_mem_iff_mem_or_mem.mp hm).elim hB (fun hn => hs (hP.mem_of_pow_mem n hn))

theorem oldDenominator_notMem {J : Input} {B : ResidueLift J} {P : Ideal JetRing}
    (hP : P.IsPrime) (hopen : openFactor J B ∉ P) (j : ℕ) :
    oldDenominator J B j ∉ P := by
  rw [HighCore82219Upper_3.oldDenominator_eq]
  exact denominator_notMem hP hopen _

/-- The denominator comparison is valid on every prime of the regular graph. -/
theorem numerator_mem_iff (J : Input) (B : ResidueLift J) (D : Factors J B)
    {P : Ideal JetRing} (hP : P.IsPrime) (hG : graphIdeal J B D ≤ P) (hopen : openFactor J B ∉ P)
    {r j : ℕ} (hj : j ≤ r) :
    taylorNumerator J B r j ∈ P ↔ oldNumerator J B j ∈ P := by
  have hnew : jetDenominator J B r ∉ P := denominator_notMem hP hopen _
  have hold : oldDenominator J B j ∉ P := oldDenominator_notMem hP hopen j
  have h := hG (taylor_agrees J B D hj)
  constructor
  · intro hm
    have ho := P.sub_mem (P.mul_mem_left (oldDenominator J B j) hm) h
    rw [sub_sub_cancel] at ho
    exact (hP.mul_mem_iff_mem_or_mem.mp ho).resolve_right hnew
  · intro hm
    have hn := P.add_mem h (Ideal.mul_mem_right _ _ hm :
      oldNumerator J B j * jetDenominator J B r ∈ P)
    rw [sub_add_cancel] at hn
    exact (hP.mul_mem_iff_mem_or_mem.mp hn).resolve_left hold

theorem firstCut_mem_iff (J : Input) (B : ResidueLift J) (D : Factors J B)
    {P : Ideal JetRing} (hP : P.IsPrime) (hG : graphIdeal J B D ≤ P) (hopen : openFactor J B ∉ P) :
    firstCut J B ∈ P ↔ Polynomial.C (HighCore82219Upper.cutoff J B) ∈ P :=
  numerator_mem_iff J B D hP hG hopen le_rfl

theorem firstCut_agreement (J : Input) (B : ResidueLift J) (D : Factors J B)
    {S : RelativeSection (graphIdeal J B D) (jetDegree J (J.ell + 1))}
    (hS : S.affine = firstCut J B) : CutoffAgreement J B D S := by
  intro P hP hG hopen
  rw [hS]
  exact firstCut_mem_iff J B D hP hG hopen

theorem firstCut_relative (J : Input) (B : ResidueLift J) (D : Factors J B) :
    ∃ S : RelativeSection (graphIdeal J B D) (jetDegree J (J.ell + 1)),
      S.affine = firstCut J B ∧ CutoffAgreement J B D S := by
  obtain ⟨S, hS⟩ := HighCore82219Upper_3_1.represent_quotient HighCore82219GeometryCert_1.proof
    J B D (r := J.ell + 1) (j := J.ell + 1) le_rfl le_rfl
  exact ⟨S, hS, firstCut_agreement J B D hS⟩

theorem cutoff_regularities (J : Input) (B : ResidueLift J) (D : Factors J B) :
    IsLeftRegular (Ideal.Quotient.mk (rootIdeal D) (tangentEquation J.f)) ∧
      IsLeftRegular (Ideal.Quotient.mk (graphIdeal J B D) (firstCut J B)) := by
  obtain ⟨S, hS, hAgree⟩ := firstCut_relative J B D
  rw [← hS]
  exact HighCore82219Upper_3_2_1.proof J B D S hAgree

end
end KoalaRectTaylor
