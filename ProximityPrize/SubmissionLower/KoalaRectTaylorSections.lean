import ProximityPrize.SubmissionLower.KoalaRectTaylorCharts
import ProximityPrize.SubmissionLower.HighCore82229UpperCertificates

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace KoalaRectTaylor
noncomputable section

open P1 (I)
open K1_14 (FX Equation Seeds)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten cleared box)
open HighCore82229Upper (Input ResidueLift Factors liftTaylor liftSeeds SeedConstants
  constantAbscissa inverseBlockCoeff ordinateTaylorNum)
open HighCore82229Upper_3 (JetRing ordinate rootInJet graphIdeal proper_mem_graph
  residueInJet jetDenominator oldDenominator oldNumerator le_saturate
  tangentEquation openFactor)
open HighCore82229Upper_3_1 (jetSeparant velocityNumerator pureDegree pureDen pureOrdinate
  embed_separant)
open HighCore82229Upper_3_1_2 (finite reciprocal inverseEval mul_reciprocal)
open HighCore82229Upper_3_3 (residueCut residueAtNode seedInJet wordAt prefixLength sectionIndex)
open private HighCore82229Upper_3.inversePart HighCore82229Upper_3.inversePart_bound
  HighCore82229Upper_3.oldDenominator_eq HighCore82229Upper_3_1.embed_C
  HighCore82229Upper_3_1.pureOrdinate_bound HighCore82229Upper_3_1.root_degree
  HighCore82229Upper_3_1.separant_glue
  HighCore82229Upper_3_1.liftTaylor_box HighCore82229Upper_3_1.embed_oldNumerator
  HighCore82229Upper_3_1.comparison_of_powers HighCore82229Upper_3_1.crt_comparison
  HighCore82229Upper_3_1.shortQuotient
  HighCore82229Upper_3_1_2.coord_transition HighCore82229Upper_3_1_2.inverseOrdinate
  HighCore82229Upper_3_1_2.inverseOrdinate_bound
  HighCore82229Upper_3_1_1.tangentIdeal HighCore82229Upper_3_1_1.comparison
  HighCore82229Upper_3_3.residue_degree
  from ProximityPrize.SubmissionLower.HighCore82229UpperGeometry
open private HighCore82229GeometryCert_1.inverse_flow
  from ProximityPrize.SubmissionLower.HighCore82229UpperCertificates
open HighCore82229Upper_3 (inversePart inversePart_bound oldDenominator_eq)
open HighCore82229Upper_3_1 (pureOrdinate_bound root_degree liftTaylor_box embed_oldNumerator
  comparison_of_powers crt_comparison shortQuotient embed_C separant_glue)
open HighCore82229Upper_3_1_2 (coord_transition inverseOrdinate inverseOrdinate_bound)
open HighCore82229Upper_3_1_1 (tangentIdeal comparison)
open HighCore82229Upper_3_3 (residue_degree)
open HighCore82229GeometryCert_1 (finite_flow inverse_flow)
open SplitCut.Rect (Box Section space)
open scoped BigOperators

theorem equationAxis_iff {z : Fin 2} {q : Equation} {s : ℕ} :
    EquationAxis z q s ↔ (jetToRect (Polynomial.C q)).degreeOf z.succ.succ ≤ s := by
  rw [MvPolynomial.degreeOf_le_iff]
  constructor
  · intro h m hm
    have hc := MvPolynomial.mem_support_iff.mp hm
    rw [coeff_jetToRect] at hc
    have hvel : m 1 = 0 := by
      by_contra hv
      rw [Polynomial.coeff_C_of_ne_zero hv,Polynomial.coeff_zero,AddMonoidAlgebra.coeff_zero] at hc
      exact hc rfl
    rw [hvel,Polynomial.coeff_C_zero] at hc
    exact MvPolynomial.degreeOf_le_iff.mp (h (m 0)) _
      (MvPolynomial.mem_support_iff.mpr hc)
  · intro h j
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    let m : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![j,0,e 0,e 1]
    have hs : seedExponent m = e := by
      ext i
      fin_cases i <;> rfl
    have hm : m ∈ (jetToRect (Polynomial.C q)).support := by
      apply MvPolynomial.mem_support_iff.mpr
      rw [coeff_jetToRect,hs,show m 1 = 0 from rfl,show m 0 = j from rfl,Polynomial.coeff_C_zero]
      exact MvPolynomial.mem_support_iff.mp he
    have h' := h m hm
    fin_cases z <;> exact h'

def pureBox (J : Input) (v : Fin 2 → ℕ) (r : ℕ) : Box :=
  ⟨1+(J.e-3)*r, r, r*v 0, r*v 1⟩

def residueBox (J : Input) : Box := ⟨0,0,2*J.w,2*J.w⟩

def taylorBox (J : Input) (v : Fin 2 → ℕ) (r : ℕ) : Box :=
  (pureBox J v r).add (residueBox J)

theorem jetToRect_C_mem_box {q : Equation} {d : Box}
    (hy : q.natDegree ≤ d.base+2*d.velocity)
    (h₀ : EquationAxis 0 q d.seed₀) (h₁ : EquationAxis 1 q d.seed₁) :
    jetToRect (Polynomial.C q) ∈ space FX d := by
  apply jetToRect_mem_box (d := d) ((Polynomial.natDegree_C q).le.trans (Nat.zero_le _)) _
    (JetAxis.C h₀) (JetAxis.C h₁)
  intro j hj
  have hz : j = 0 := Nat.eq_zero_of_le_zero
    ((Polynomial.le_natDegree_of_mem_supp _ hj).trans (Polynomial.natDegree_C q).le)
  subst j
  simpa only [Polynomial.coeff_C_zero,Nat.mul_zero,Nat.add_zero] using hy

private theorem equation_nat_axis {z : Fin 2} (n : ℕ) :
    EquationAxis z (n : Equation) 0 := by
  rw [← map_natCast (Polynomial.C : Seeds →+* Equation),← map_natCast (MvPolynomial.C : FX →+* Seeds)]
  exact EquationAxis.scalar _

private theorem inverse_part_axis (J : Input) {v : Fin 2 → ℕ}
    (hf : ∀ z, EquationAxis z J.f (v z)) (z : Fin 2) :
    EquationAxis z (inversePart J) (v z) := by
  have h1 : EquationAxis z (Polynomial.X*J.f.derivative) (v z) :=
    by simpa only [Nat.zero_add] using EquationAxis.variableX.mul (hf z).derivative
  have h2 : EquationAxis z (Polynomial.C (J.e : Seeds)*J.f) (v z) := by
    rw [map_natCast]
    simpa only [Nat.zero_add] using (equation_nat_axis (z := z) J.e).mul (hf z)
  intro i
  rw [inversePart,Polynomial.coeff_sub,sub_eq_add_neg]
  apply (MvPolynomial.degreeOf_add_le _ _ _).trans
  have hneg : (-(Polynomial.C (J.e : Seeds)*J.f).coeff i).degreeOf z =
      ((Polynomial.C (J.e : Seeds)*J.f).coeff i).degreeOf z := by
    rw [MvPolynomial.degreeOf_eq_sup,MvPolynomial.support_neg,← MvPolynomial.degreeOf_eq_sup]
  rw [hneg]
  exact max_le (h1 i) (h2 i)

private theorem separant_section (J : Input) (B : ResidueLift J) (D : Factors J B)
    {v : Fin 2 → ℕ} (hf : ∀ z, EquationAxis z J.f (v z)) :
    Represented (graphIdeal J B D) ⟨J.e-2,0,v 0,v 1⟩ (jetSeparant J.f) := by
  have he : 3 ≤ J.e := J.sheets
  have hdeg : (J.e-2)+1+2*0 = J.e-1 := by omega
  apply represented_of_charts (n := 1) (q := Polynomial.C (inversePart J))
  · apply jetToRect_C_mem_box _ (hf 0).derivative (hf 1).derivative
    exact (Polynomial.natDegree_derivative_le _).trans hdeg.ge
  · apply jetToRect_C_mem_box _ (inverse_part_axis J hf 0) (inverse_part_axis J hf 1)
    exact (inversePart_bound J).1.trans hdeg.ge
  · have h := proper_mem_graph J B D
    have hf' : Polynomial.C J.f ∈ graphIdeal J B D := by
      rw [D.product,Polynomial.C_mul]
      exact (graphIdeal J B D).mul_mem_right _ h
    have heq : ordinate^1 * jetSeparant J.f - Polynomial.C (inversePart J) =
        Polynomial.C (Polynomial.C (J.e : Seeds)) * Polynomial.C J.f := by
      rw [pow_one]
      exact @separant_glue Equation JetRing (@Polynomial.commRing Seeds inferInstance)
        HighCore82229Upper_3.jetCommRing Polynomial.C Polynomial.X J.f.derivative
        (Polynomial.C (J.e : Seeds)) J.f
    rw [heq]
    exact (graphIdeal J B D).mul_mem_left _ hf'

private theorem pure_sep_room (J : Input) (r : ℕ) :
    (r-1)*(J.e-2) ≤ r*(J.e-1) :=
  Nat.mul_le_mul (Nat.sub_le r 1) (Nat.sub_le_sub_left (by decide : 1 ≤ 2) J.e)

private theorem pureDen_section (J : Input) (B : ResidueLift J) (D : Factors J B)
    {v : Fin 2 → ℕ} (hf : ∀ z, EquationAxis z J.f (v z)) (r : ℕ) :
    Represented (graphIdeal J B D) (pureBox J v r) (pureDen J r) := by
  have h := (separant_section J B D hf).pow (r-1)
  apply h.widen
  · simp [pureBox]
  · change (r-1)*(J.e-2)+0 ≤ (pureDegree J r).1
    rw [root_degree,Nat.add_zero]
    exact (pure_sep_room J r).trans (Nat.le_add_left _ _)
  · exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  · exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)

private theorem ordinate_section (Q : Ideal JetRing) :
    Represented Q (⟨1,0,0,0⟩ : Box) ordinate := by
  apply represented_of_mem
  exact jetToRect_C_mem_box (by simp) EquationAxis.variableX EquationAxis.variableX

private theorem pureOrdinate_zero_section (J : Input) (B : ResidueLift J) (D : Factors J B)
    {v : Fin 2 → ℕ} (hf : ∀ z, EquationAxis z J.f (v z)) (r : ℕ) :
    Represented (graphIdeal J B D) (pureBox J v r) (pureOrdinate J r 0) := by
  have h := ((separant_section J B D hf).pow (r-1)).mul (ordinate_section (graphIdeal J B D))
  apply h.widen
  · simp [pureBox,Box.add]
  · change ((r-1)*(J.e-2)+1)+0 ≤ (pureDegree J r).1
    rw [root_degree,Nat.add_zero]
    exact (Nat.add_le_add_right (pure_sep_room J r) 1).trans_eq (Nat.add_comm _ _)
  · simpa [pureBox,Box.add] using Nat.mul_le_mul_right (v 0) (Nat.sub_le r 1)
  · simpa [pureBox,Box.add] using Nat.mul_le_mul_right (v 1) (Nat.sub_le r 1)

private theorem pureOrdinate_section (J : Input) (B : ResidueLift J) (D : Factors J B)
    {v : Fin 2 → ℕ} (hf : ∀ z, EquationAxis z J.f (v z)) {r i : ℕ} (hi : i ≤ r) :
    Represented (graphIdeal J B D) (pureBox J v r) (pureOrdinate J r i) := by
  cases i with
  | zero => exact pureOrdinate_zero_section J B D hf r
  | succ k =>
    obtain ⟨δ,hd⟩ := finite_flow J B D
    obtain ⟨hδ,hc⟩ := inverse_flow J B D δ hd
    apply represented_of_transition J B D (inverse := inverseOrdinate J r k)
    · exact (pureOrdinate_bound J hi).1
    · exact (inverseOrdinate_bound J hi).1
    · exact pureOrdinate_axis J (hf 0) hi
    · exact pureOrdinate_axis J (hf 1) hi
    · exact inverseOrdinate_axis J (hf 0) hi
    · exact inverseOrdinate_axis J (hf 1) hi
    · exact coord_transition J hi (finite J B D) (reciprocal J B D) hd hδ
        (mul_reciprocal J B D) hc

private theorem seed_constant_axis {J : Input} {s : SeedConstants} (hs : s.totalDegree ≤ 2*J.w)
    (z : Fin 2) : (liftSeeds s).degreeOf z ≤ 2*J.w :=
  (MvPolynomial.degreeOf_le_totalDegree _ _).trans
    ((Finset.sup_mono (MvPolynomial.support_map_subset constantAbscissa s)).trans hs)

private theorem seed_section (J : Input) (Q : Ideal JetRing) {s : SeedConstants}
    (hs : s.totalDegree ≤ 2*J.w) : Represented Q (residueBox J) (seedInJet s) :=
  represented_of_mem (jetToRect_C_mem_box (Polynomial.natDegree_C (liftSeeds s)).le
    (EquationAxis.C (seed_constant_axis hs 0)) (EquationAxis.C (seed_constant_axis hs 1)))

private theorem box_C_degree {p : Biform} {a s : ℕ} (hp : p ∈ box a s) :
    (MvPolynomial.optionEquivLeft FX (Fin 2) p).natDegree ≤ a := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.optionEquivLeft_coeff_coeff,AddMonoidAlgebra.coeff_zero]
  by_contra hn
  have h := (MvPolynomial.mem_restrictBidegree.mp hp) _ (MvPolynomial.mem_support_iff.mpr hn)
  exact (not_le_of_gt hi) (by simpa using h.1)

private theorem box_C_axis {p : Biform} {a s : ℕ} (hp : p ∈ box a s) (z : Fin 2) :
    EquationAxis z (MvPolynomial.optionEquivLeft FX (Fin 2) p) s := by
  intro i
  apply (MvPolynomial.degreeOf_le_totalDegree _ z).trans
  apply Finset.sup_le
  intro m hm
  rw [MvPolynomial.mem_support_iff,MvPolynomial.optionEquivLeft_coeff_coeff] at hm
  have h := ((MvPolynomial.mem_restrictBidegree.mp hp) _ (MvPolynomial.mem_support_iff.mpr hm)).2
  change (Finsupp.optionElim i m).some.sum (fun _ n => n) ≤ s at h
  simpa only [Finsupp.some_optionElim] using h

private theorem residue_taylor_section (J : Input) (B : ResidueLift J) (Q : Ideal JetRing)
    (i : ℕ) : Represented Q (residueBox J) (rootInJet (liftTaylor B.numerator i)) := by
  have h := liftTaylor_box J B i
  exact represented_of_mem (jetToRect_C_mem_box (box_C_degree h)
    (box_C_axis h 0) (box_C_axis h 1))

def taylorNumerator (J : Input) (B : ResidueLift J) (r j : ℕ) : JetRing :=
  shortQuotient J B r j

theorem numerator_section (J : Input) (B : ResidueLift J) (D : Factors J B)
    {v : Fin 2 → ℕ} (hf : ∀ z, EquationAxis z J.f (v z)) {r j : ℕ} (hj : j ≤ r) :
    Represented (graphIdeal J B D) (taylorBox J v r) (taylorNumerator J B r j) := by
  unfold taylorNumerator shortQuotient
  apply Represented.sum
  intro i hi
  have hir : i ≤ r := by have := Finset.mem_range.mp hi; omega
  rw [← Algebra.smul_def]
  apply Represented.smul
  apply Represented.sub
  · have h := (seed_section J (graphIdeal J B D) B.denominator_degree).mul
      (pureOrdinate_section J B D hf hir)
    change Represented _ _ (seedInJet B.denominator * pureOrdinate J r i)
    simpa [taylorBox,Box.add,Nat.add_comm] using h
  · exact (pureDen_section J B D hf r).mul (residue_taylor_section J B (graphIdeal J B D) i)

private theorem compare_velocity (J : Input) (B : ResidueLift J) (D : Factors J B) (k : ℕ) :
    jetSeparant J.f^(2*k+1)*velocityNumerator J.f k -
      rootInJet (cleared (flatten J.f) k)*jetSeparant J.f^k ∈ graphIdeal J B D := by
  have hle : tangentIdeal J.f ≤ graphIdeal J B D :=
    (graphIdeal J B D).span_singleton_le_iff_mem.mpr
      (le_saturate _ _ (Ideal.subset_span (by simp)))
  apply hle
  apply Ideal.Quotient.eq.mp
  let φ := Ideal.Quotient.mk (tangentIdeal J.f)
  change φ _ = φ _
  rw [show 2*k+1 = k+(k+1) by omega,pow_add,mul_assoc]
  have h := comparison J.f k
  simp only [map_mul,map_pow] at h ⊢
  rw [h,mul_comm]

private theorem agree_ordinate (J : Input) (B : ResidueLift J) (D : Factors J B) {r j i : ℕ}
    (hij : i ≤ j) (hjr : j ≤ r) :
    let φ := Ideal.Quotient.mk (graphIdeal J B D)
    φ (jetSeparant J.f ^ (2*j-1)) * φ (pureOrdinate J r i) =
      φ (rootInJet (ordinateTaylorNum J.f j i)) * φ (pureDen J r) := by
  let φ := Ideal.Quotient.mk (graphIdeal J B D)
  change φ _ * φ _ = φ _ * φ _
  cases i with
  | zero =>
    simp only [pureOrdinate,ordinateTaylorNum,map_mul,map_pow,embed_separant]
    rw [show rootInJet (MvPolynomial.X none) = ordinate by simp [rootInJet,ordinate]]
    ring
  | succ k =>
    have h := Ideal.Quotient.eq.mpr (compare_velocity J B D k)
    simp only [map_mul,map_pow] at h
    simp only [pureOrdinate,pureDen,ordinateTaylorNum,map_mul,map_pow,embed_separant,embed_C]
    exact comparison_of_powers _ _ _ _ (by omega) (by omega) h

theorem taylor_agrees (J : Input) (B : ResidueLift J) (D : Factors J B) {r j : ℕ}
    (hj : j ≤ r) :
    oldDenominator J B j * taylorNumerator J B r j -
      oldNumerator J B j * jetDenominator J B r ∈ graphIdeal J B D := by
  apply Ideal.Quotient.eq.mp
  have hd : jetDenominator J B r = residueInJet B * pureDen J r := rfl
  rw [oldDenominator_eq,taylorNumerator,shortQuotient,embed_oldNumerator,hd]
  simp only [map_mul,map_sub,map_sum,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply crt_comparison
  exact agree_ordinate J B D (by have := Finset.mem_range.mp hi; omega) hj

theorem numerator_zero_iff {E : Type} [Field E] [Algebra FX E]
    (J : Input) (B : ResidueLift J) (D : Factors J B) (φ : JetRing →ₐ[FX] E)
    (hg : ∀ p ∈ graphIdeal J B D, φ p = 0) (hu : φ (openFactor J B) ≠ 0)
    {r j : ℕ} (hj : j ≤ r) :
    φ (taylorNumerator J B r j) = 0 ↔ φ (oldNumerator J B j) = 0 := by
  have h := hg _ (taylor_agrees J B D hj)
  rw [map_sub,map_mul,map_mul,sub_eq_zero] at h
  have huv : φ (residueInJet B) ≠ 0 ∧ φ (Polynomial.C J.f.derivative) ≠ 0 := by
    simpa only [openFactor,map_mul,mul_ne_zero_iff] using hu
  have hd : φ (jetDenominator J B r) ≠ 0 := by
    rw [jetDenominator,map_mul,map_pow]
    exact mul_ne_zero huv.1 (pow_ne_zero _ huv.2)
  have ho : φ (oldDenominator J B j) ≠ 0 := by
    rw [oldDenominator_eq,map_mul,map_pow]
    exact mul_ne_zero huv.1 (pow_ne_zero _ huv.2)
  constructor
  · intro h₀
    rw [h₀,mul_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hd
  · intro h₀
    rw [h₀,zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_left ho

structure SectionFamily (J : Input) (B : ResidueLift J) (D : Factors J B)
    (v : Fin 2 → ℕ) (r : ℕ) where
  denominator : Section (rectIdeal (graphIdeal J B D)) (taylorBox J v r)
  numerator : Fin (r+1) → Section (rectIdeal (graphIdeal J B D)) (taylorBox J v r)
  den_eq : denominator.finite = jetToRect (jetDenominator J B r)
  num_eq : ∀ i, (numerator i).finite = jetToRect (taylorNumerator J B r i.val)

theorem sections (J : Input) (B : ResidueLift J) (D : Factors J B)
    {v : Fin 2 → ℕ} (hf : ∀ z, EquationAxis z J.f (v z)) (r : ℕ) :
    Nonempty (SectionFamily J B D v r) := by
  have h := (seed_section J (graphIdeal J B D) B.denominator_degree).mul
    (pureDen_section J B D hf r)
  have hden : Represented (graphIdeal J B D) (taylorBox J v r) (jetDenominator J B r) := by
    change Represented _ _ (seedInJet B.denominator * pureDen J r)
    simpa [taylorBox,Box.add,Nat.add_comm] using h
  obtain ⟨den,hden⟩ := hden
  have hnum (i : Fin (r+1)) : Represented (graphIdeal J B D) (taylorBox J v r)
      (taylorNumerator J B r i.val) := numerator_section J B D hf (Nat.le_of_lt_succ i.isLt)
  choose num hnum using hnum
  exact ⟨⟨den,num,hden,hnum⟩⟩

theorem residue_section (J : Input) (B : ResidueLift J) (D : Factors J B)
    {v : Fin 2 → ℕ} (hf : ∀ z, EquationAxis z J.f (v z)) (r : ℕ) (x : I) :
    Represented (graphIdeal J B D) (taylorBox J v r) (residueCut J B r x) := by
  have h := (seed_section J (graphIdeal J B D) (residue_degree B x)).mul
    (pureDen_section J B D hf r)
  simpa [residueCut,pureDen,taylorBox,Box.add,Nat.add_comm] using h

def nodeNumerator (J : Input) (B : ResidueLift J) (sites : Finset I) (x : I)
    (b : I → FX) (a : Fin (prefixLength J sites) → FX) : JetRing :=
  let r := J.ell-sites.card
  let den := jetDenominator J B r
  (residueCut J B r x - wordAt J x • den) +
    (∑ i ∈ sites, b i • (wordAt J i • den - residueCut J B r i)) +
    ∑ j, a j • taylorNumerator J B r (sectionIndex J sites j).val

theorem node_section (J : Input) (B : ResidueLift J) (D : Factors J B)
    {v : Fin 2 → ℕ} (hf : ∀ z, EquationAxis z J.f (v z))
    (sites : Finset I) (x : I) (b : I → FX) (a : Fin (prefixLength J sites) → FX) :
    Represented (graphIdeal J B D) (taylorBox J v (J.ell-sites.card)) (nodeNumerator J B sites x b a) := by
  obtain ⟨T⟩ := sections J B D hf (J.ell-sites.card)
  have den : Represented (graphIdeal J B D) (taylorBox J v (J.ell-sites.card))
      (jetDenominator J B (J.ell-sites.card)) := ⟨T.denominator,T.den_eq⟩
  unfold nodeNumerator
  apply Represented.add
  · apply Represented.add
    · exact (residue_section J B D hf _ x).sub (den.smul (wordAt J x))
    · exact Represented.sum _ _ fun i _ =>
        ((den.smul (wordAt J i)).sub (residue_section J B D hf _ i)).smul (b i)
  · exact Represented.sum _ _ fun j _ =>
      (show Represented _ _ _ from ⟨T.numerator _,T.num_eq _⟩).smul (a j)

def diagonalBox (J : Input) (v : Fin 2 → ℕ) (r : ℕ) : Box :=
  ⟨(J.e-3)*r,r,r*max 1 (v 0),r*max 1 (v 1)⟩

theorem represented_diagonal {J : Input} {v : Fin 2 → ℕ} {r k : ℕ}
    {Q : Ideal JetRing} {p : JetRing} (he : 4 ≤ J.e) (hk : 1 ≤ k)
    (hseed : ∀ z, 2*J.w ≤ k*max 1 (v z))
    (h : Represented Q (taylorBox J v r) p) :
    Represented Q (diagonalBox J v (r+k)) p := by
  apply h.widen
  · exact Nat.le_add_right _ _
  · have h : 1 ≤ (J.e-3)*k := by
      exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
    dsimp [taylorBox,pureBox,residueBox,diagonalBox,Box.add]
    simp only [Nat.mul_add]
    omega
  · exact (Nat.add_le_add (Nat.mul_le_mul_left _ (le_max_right _ _)) (hseed 0)).trans_eq
      (Nat.add_mul _ _ _).symm
  · exact (Nat.add_le_add (Nat.mul_le_mul_left _ (le_max_right _ _)) (hseed 1)).trans_eq
      (Nat.add_mul _ _ _).symm

def diagonalPadding (hi : ℕ) (v : Fin 2 → ℕ) : ℕ :=
  max 1 (max ((2*hi) ⌈/⌉ max 1 (v 0)) ((2*hi) ⌈/⌉ max 1 (v 1)))

theorem one_le_diagonalPadding (hi : ℕ) (v : Fin 2 → ℕ) :
    1 ≤ diagonalPadding hi v := le_max_left _ _

theorem seed_le_diagonalPadding (hi : ℕ) (v : Fin 2 → ℕ) (z : Fin 2) :
    2*hi ≤ diagonalPadding hi v * max 1 (v z) := by
  have hpos : 0 < max 1 (v z) := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hceil : (2*hi) ⌈/⌉ max 1 (v z) ≤ diagonalPadding hi v :=
    (show (2*hi) ⌈/⌉ max 1 (v z) ≤ _ from by
      fin_cases z
      · exact le_max_left _ _
      · exact le_max_right _ _).trans (le_max_right _ _)
  exact ((ceilDiv_le_iff_le_mul hpos).mp hceil).trans_eq (Nat.mul_comm _ _)

theorem represented_diagonal_hi {J : Input} {v : Fin 2 → ℕ} {r : ℕ}
    {Q : Ideal JetRing} {p : JetRing} (he : 4 ≤ J.e)
    (h : Represented Q (taylorBox J v r) p) :
    Represented Q (diagonalBox J v (r+diagonalPadding J.hi v)) p :=
  represented_diagonal he (one_le_diagonalPadding _ _)
    (fun z => (Nat.mul_le_mul_left _ J.upper).trans (seed_le_diagonalPadding _ _ z)) h

end
end KoalaRectTaylor

#print axioms KoalaRectTaylor.sections
#print axioms KoalaRectTaylor.taylor_agrees
#print axioms KoalaRectTaylor.node_section
#print axioms KoalaRectTaylor.represented_diagonal_hi
