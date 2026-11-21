import ProximityPrize.SubmissionLower.Rect51TangentGraph
import ProximityPrize.SubmissionLower.Rect51TangentInverse

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace Rect51Tangent
noncomputable section
open HighCore82706Tangent (Input ResidueLift Factors liftSeeds liftTaylor)
open HighCore82706Tangent_3 (JetRing ordinate graphIdeal openFactor proper_mem_graph
  oldDenominator oldNumerator jetDenominator residueInJet rootInJet)
open HighCore82706Tangent_3_1 (jetSeparant pureDen pureOrdinate)
open K1_14 (FX Equation Seeds)
open K1_14_6 (Biform)
open K1_14_6_1 (box)
open scoped BigOperators
open private inversePart inversePart_bound shortQuotient agree_quotient liftTaylor_box
  separant_glue oldDenominator_eq represent_quotient
  from ProximityPrize.SubmissionLower.HighCore82706TangentDeps

private theorem separant_section (J : Input) (B : ResidueLift J) (D : Factors J B)
    {v : Axes} (hf : SeedBound J.f v) :
    Represented (graphIdeal J B D) (J.e-2) 0 v (jetSeparant J.f) := by
  have e : J.e-2+2*0+1 = J.e-1 := by have hs : 3 ≤ J.e := J.sheets; omega
  have wsep : Weighted (jetSeparant J.f) (J.e-1) := Weighted.C (Polynomial.natDegree_derivative_le _)
  have winv : Weighted (Polynomial.C (inversePart J)) (J.e-1) := Weighted.C (inversePart_bound J).1
  refine ⟨⟨1,jetSeparant J.f,Polynomial.C (inversePart J),
    Bounded.C hf.derivative,Bounded.C (inversePart_seedBound J hf),e ▸ wsep,e ▸ winv,?_⟩,rfl⟩
  have hf0 : Polynomial.C J.f ∈ graphIdeal J B D := by
    rw [D.product, Polynomial.C_mul]
    exact (graphIdeal J B D).mul_mem_right _ (proper_mem_graph J B D)
  rw [pow_one]
  have eq : ordinate * jetSeparant J.f - Polynomial.C (inversePart J) =
      Polynomial.C (Polynomial.C (J.e : Seeds)) * Polynomial.C J.f :=
    @separant_glue Equation JetRing (@Polynomial.commRing Seeds inferInstance)
      HighCore82706Tangent_3.jetCommRing Polynomial.C Polynomial.X J.f.derivative
      (Polynomial.C (J.e : Seeds)) J.f
  rw [eq]
  exact (graphIdeal J B D).mul_mem_left _ hf0

private theorem raw_degree (J : Input) (r : ℕ) : baseDegree J r + 2*r = 1+r*(J.e-1) := by
  have he : J.e-3+2 = J.e-1 := by have hs : 3 ≤ J.e := J.sheets; omega
  unfold baseDegree
  rw [Nat.add_assoc, ← Nat.add_mul, he, Nat.mul_comm (J.e-1)]

private theorem sep_room (J : Input) (r : ℕ) : (r-1)*(J.e-2) ≤ r*(J.e-1) :=
  Nat.mul_le_mul (Nat.sub_le r 1) (Nat.sub_le_sub_left (by decide : 1 ≤ 2) J.e)

private theorem pure_denominator (J : Input) (B : ResidueLift J) (D : Factors J B)
    {v : Axes} (hf : SeedBound J.f v) (r : ℕ) :
    Represented (graphIdeal J B D) (baseDegree J r) r (r • v) (pureDen J r) := by
  have hh := (separant_section J B D hf).pow (r-1)
  apply hh.pad
  · rw [raw_degree]
    have := sep_room J r
    omega
  · simp
  · intro i
    exact Nat.mul_le_mul_right (v i) (Nat.sub_le r 1)

private theorem pure_ordinate_zero (J : Input) (B : ResidueLift J) (D : Factors J B)
    {v : Axes} (hf : SeedBound J.f v) (r : ℕ) :
    Represented (graphIdeal J B D) (baseDegree J r) r (r • v) (pureOrdinate J r 0) := by
  have ho : Represented (graphIdeal J B D) 1 0 0 ordinate :=
    Represented.absolute Bounded.ordinate Weighted.ordinate
  have hh := ((separant_section J B D hf).pow (r-1)).mul ho
  apply hh.pad
  · rw [raw_degree]
    have := sep_room J r
    omega
  · simp
  · intro i
    change (r-1)*v i+0 ≤ r*v i
    simp only [add_zero]
    exact Nat.mul_le_mul_right (v i) (Nat.sub_le r 1)

theorem seed_section {Q : Ideal JetRing} {s : HighCore82706Tangent.SeedConstants} {c : ℕ}
    (hc : s.totalDegree ≤ c) :
    Represented Q 0 0 (fun _ => c) (Polynomial.C (Polynomial.C (liftSeeds s))) := by
  have hb : SeedBound (Polynomial.C (liftSeeds s)) (fun _ => c) := by
    intro k i
    by_cases h : k = 0
    · subst k
      rw [Polynomial.coeff_C_zero]
      have hmap : (liftSeeds s).totalDegree ≤ s.totalDegree :=
        Finset.sup_mono (MvPolynomial.support_map_subset HighCore82706Tangent.constantAbscissa s)
      exact (MvPolynomial.degreeOf_le_totalDegree _ i).trans (hmap.trans hc)
    · rw [Polynomial.coeff_C_of_ne_zero h, MvPolynomial.degreeOf_zero]
      exact Nat.zero_le _
  exact Represented.absolute (Bounded.C hb) (Weighted.C (Polynomial.natDegree_C _).le)

private theorem biform_constant {Q : Ideal JetRing} {q : Biform} {c : ℕ}
    (hq : q ∈ box 0 c) : Represented Q 0 0 (fun _ => c) (rootInJet q) := by
  let f := MvPolynomial.optionEquivLeft FX (Fin 2) q
  have hm := MvPolynomial.mem_restrictBidegree.mp hq
  have hzero (k : ℕ) (hk : 0 < k) : f.coeff k = 0 := by
    ext m
    rw [show (0 : Seeds).coeff m = 0 by simp]
    have eq := MvPolynomial.optionEquivLeft_coeff_coeff FX q k m
    change ((MvPolynomial.optionEquivLeft FX (Fin 2) q).coeff k).coeff m = 0
    rw [eq]
    by_contra ne
    have he := (hm _ (MvPolynomial.mem_support_iff.mpr ne)).1
    rw [Finsupp.optionElim_apply_none] at he
    omega
  have hdeg : f.natDegree ≤ 0 := Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hzero
  have hseed : SeedBound f (fun _ => c) := by
    intro k i
    apply (MvPolynomial.degreeOf_le_totalDegree _ i).trans
    apply Finset.sup_le
    intro m mm
    have eq := MvPolynomial.optionEquivLeft_coeff_coeff FX q k m
    have he : m.optionElim k ∈ q.support := by
      apply MvPolynomial.mem_support_iff.mpr
      rw [← eq]
      exact MvPolynomial.mem_support_iff.mp mm
    have hs := (hm _ he).2
    change (m.optionElim k).some.sum (fun _ n => n) ≤ c at hs
    rwa [Finsupp.some_optionElim] at hs
  exact Represented.absolute (Bounded.C hseed) (Weighted.C hdeg)

/-- The bound holds independently for each seed. -/
def taylorAxis (J : Input) (v : Axes) (r : ℕ) : Axes :=
  r • v + fun _ => 2*J.w

@[simp] theorem taylorAxis_apply (J : Input) (v : Axes) (r : ℕ) (i : Fin 2) :
    taylorAxis J v r i = r*v i + 2*J.w := rfl

structure TaylorSections (J : Input) (B : ResidueLift J) (D : Factors J B) (v : Axes) (r : ℕ) where
  denominator : Section (graphIdeal J B D) (baseDegree J r) r (taylorAxis J v r)
  numerator : Fin (r+1) → Section (graphIdeal J B D) (baseDegree J r) r (taylorAxis J v r)
  den_eq : denominator.affine = jetDenominator J B r
  num_eq : ∀ j, (numerator j).affine = shortQuotient J B r j.val
  agrees : ∀ j : Fin (r+1),
    oldDenominator J B j.val * (numerator j).affine -
      oldNumerator J B j.val * denominator.affine ∈ graphIdeal J B D

theorem taylor_sections (J : Input) (B : ResidueLift J) (D : Factors J B) {v : Axes}
    (hf : SeedBound J.f v) (r : ℕ) (hr : r ≤ J.ell+1) : Nonempty (TaylorSections J B D v r) := by
  classical
  let Q := graphIdeal J B D
  let H := baseDegree J r
  have hD := pure_denominator J B D hf r
  have hB : Represented Q 0 0 (fun _ => 2*J.w) (residueInJet B) :=
    seed_section B.denominator_degree
  have hDen : Represented Q H r (taylorAxis J v r) (jetDenominator J B r) := by
    change Represented Q H r (r • v + fun _ => 2*J.w) (residueInJet B * pureDen J r)
    simpa only [Nat.zero_add, add_comm (fun _ : Fin 2 => 2*J.w) (r • v)] using hB.mul hD
  have hNum (j : Fin (r+1)) : Represented Q H r (taylorAxis J v r) (shortQuotient J B r j.val) := by
    unfold shortQuotient
    apply Represented.sum
    intro i hi
    have hir : i ≤ r := by
      have h := Finset.mem_range.mp hi
      have ht := j.isLt
      omega
    have hOrd : Represented Q H r (r • v) (pureOrdinate J r i) := by
      cases i with
      | zero => exact pure_ordinate_zero J B D hf r
      | succ k => exact represent_ordinate_succ J B D hf hir
    apply Represented.smul
    apply Represented.sub
    · simpa only [Nat.zero_add, taylorAxis, add_comm (fun _ : Fin 2 => 2*J.w) (r • v)] using
        hB.mul hOrd
    · simpa only [Nat.add_zero, taylorAxis] using hD.mul
        (biform_constant (Q := Q) (liftTaylor_box J B i))
  obtain ⟨den,hden⟩ := hDen
  choose nums hnums using hNum
  refine ⟨⟨den,nums,hden,hnums,?_⟩⟩
  intro j
  rw [hden,hnums j]
  exact agree_quotient HighCore82706Tangent_3_1_1.proof J B D (by have := j.isLt; omega) hr

theorem cutoff_agrees {J : Input} {B : ResidueLift J} {D : Factors J B} {v : Axes}
    (T : TaylorSections J B D v (J.ell+1)) (P : Ideal JetRing) (hp : P.IsPrime)
    (hg : graphIdeal J B D ≤ P) (hu : openFactor J B ∉ P) :
    (T.numerator (Fin.last (J.ell+1))).affine ∈ P ↔
      Polynomial.C (HighCore82706Tangent.cutoff J B) ∈ P := by
  have hB : residueInJet B ∉ P := fun h => hu (P.mul_mem_right _ h)
  have hsep : Polynomial.C J.f.derivative ∉ P := fun h => hu (P.mul_mem_left _ h)
  have not_mem (m : ℕ) : residueInJet B * Polynomial.C J.f.derivative ^ m ∉ P := by
    intro h
    exact ((hp.mul_mem_iff_mem_or_mem.mp h).resolve_left hB |> hp.mem_of_pow_mem m) |> hsep
  have hO : oldDenominator J B (J.ell+1) ∉ P := by rw [oldDenominator_eq]; exact not_mem _
  have hD : T.denominator.affine ∉ P := by rw [T.den_eq,jetDenominator]; exact not_mem _
  have h := hg (T.agrees (Fin.last (J.ell+1)))
  change oldDenominator J B (J.ell+1) * (T.numerator (Fin.last (J.ell+1))).affine -
    Polynomial.C (HighCore82706Tangent.cutoff J B) * T.denominator.affine ∈ P at h
  have hp' {a b : JetRing} (hab : a - b ∈ P) : a ∈ P ↔ b ∈ P := by
    constructor
    · intro ha
      convert P.sub_mem ha hab using 1
      abel
    · intro hb
      convert P.add_mem hab hb using 1
      abel
  calc
    _ ↔ oldDenominator J B (J.ell+1) * (T.numerator (Fin.last (J.ell+1))).affine ∈ P := by
      rw [hp.mul_mem_iff_mem_or_mem,or_iff_right hO]
    _ ↔ Polynomial.C (HighCore82706Tangent.cutoff J B) * T.denominator.affine ∈ P := hp' h
    _ ↔ _ := by rw [hp.mul_mem_iff_mem_or_mem,or_iff_left hD]

theorem regular_graph_cut {J : Input} {B : ResidueLift J} {D : Factors J B} {v : Axes}
    (T : TaylorSections J B D v (J.ell+1)) :
    IsLeftRegular (Ideal.Quotient.mk (HighCore82706Tangent_3.rootIdeal D)
      (HighCore82706Tangent_3.tangentEquation J.f)) ∧
    IsLeftRegular (Ideal.Quotient.mk (graphIdeal J B D) (T.numerator (Fin.last (J.ell+1))).affine) := by
  obtain ⟨U,hU⟩ := represent_quotient HighCore82706_5_1.proof J B D
    (r := J.ell+1) (j := J.ell+1) le_rfl le_rfl
  have eq : U.affine = (T.numerator (Fin.last (J.ell+1))).affine :=
    hU.trans (T.num_eq (Fin.last (J.ell+1))).symm
  rw [← eq]
  exact HighCore82706Tangent_3_2_1.proof J B D U (fun P hp hg hu => by
    rw [eq]
    exact cutoff_agrees T P hp hg hu)

theorem cutoff_at_mark {J : Input} {B : ResidueLift J} {D : Factors J B} {v : Axes}
    (T : TaylorSections J B D v (J.ell+1)) {γ : P1.K} (hγ : γ ∈ J.marks)
    (hroot : HighCore82706Tangent.rootOn J D.proper γ) :
    HighCore82706Tangent_3.markPoint J γ (T.numerator (Fin.last (J.ell+1))).affine = 0 := by
  have hcut := HighCore82706Tangent_3_2.cutoff_le_mark J B D hγ hroot
  have hopen := HighCore82706Tangent_3_2.mark_regular J B hγ
  have hprime := RingHom.ker_isPrime (HighCore82706Tangent_3.markPoint J γ).toRingHom
  have hgraph := HighCore82706Tangent_3_2.graph_le_prime hprime hcut hopen
  exact (cutoff_agrees T _ hprime hgraph hopen).mpr (hcut (Ideal.subset_span (by simp)))

#print axioms taylor_sections
#print axioms cutoff_agrees
#print axioms regular_graph_cut
#print axioms cutoff_at_mark
end
end Rect51Tangent
