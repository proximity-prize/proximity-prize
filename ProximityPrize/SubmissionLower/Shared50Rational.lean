import ProximityPrize.SubmissionLower.Final50Order
import Mathlib.RingTheory.Localization.Integer
import ProximityPrize.SubmissionLower.Shared50TallyOld -- serialize candidate build

set_option maxHeartbeats 800000
namespace Shared50Rational
noncomputable section

open K1_13 (Geom Row)
open K1_13_3 (symbolAt)
open K1_13_6 (GenericField GeoField genericCoeffs toGeneric)
open Polynomial MvPolynomial
open scoped BigOperators nonZeroDivisors

abbrev FractionJet := MvPolynomial (Fin 4) GenericField

def toFraction (P : Row 4) : FractionJet :=
  MvPolynomial.map (algebraMap Geom[X] GenericField) P

def toGeometric : FractionJet →+* K1_13_6.GeoJets :=
  MvPolynomial.map (algebraMap GenericField GeoField)

theorem fraction_geometric (P : Row 4) :
    toGeometric (toFraction P) = toGeneric P := by
  simp [toGeometric,toFraction,toGeneric,genericCoeffs,MvPolynomial.map_map]

theorem fraction_injective : Function.Injective toFraction :=
  MvPolynomial.map_injective _ (IsFractionRing.injective Geom[X] _)

theorem support_fraction (P : Row 4) : (toFraction P).support = P.support :=
  MvPolynomial.support_map_of_injective P (IsFractionRing.injective Geom[X] GenericField)

theorem primitive_relation {ι : Type*} (s : Finset ι) (c : ι → Geom[X])
    (e : ι → Row 4) (h : ∑ i ∈ s, c i • e i = 0)
    (hne : ∃ i ∈ s, c i ≠ 0) (x : Geom) :
    ∃ b : ι → Geom[X], (∑ i ∈ s, b i • e i = 0) ∧ ∃ i ∈ s, (b i).eval x ≠ 0 := by
  classical
  let S := s.filter fun i => c i ≠ 0
  have hS : S.Nonempty := by
    obtain ⟨i, hi, hc⟩ := hne
    exact ⟨i,Finset.mem_filter.mpr ⟨hi,hc⟩⟩
  obtain ⟨i,hi,hmin⟩ := S.exists_min_image (fun i => (c i).rootMultiplicity x) hS
  let k := (c i).rootMultiplicity x
  let D : Geom[X] := (Polynomial.X - Polynomial.C x)^k
  have hd : D ≠ 0 := pow_ne_zero _ (Polynomial.X_sub_C_ne_zero x)
  have hdiv (j : ι) : D ∣ c j ∨ j ∉ s := by
    by_cases hzero : c j = 0
    · exact Or.inl (hzero.symm ▸ dvd_zero D)
    · by_cases hs : j ∈ s
      · exact Or.inl ((pow_dvd_pow _ (hmin j (Finset.mem_filter.mpr ⟨hs,hzero⟩))).trans
          (Polynomial.pow_rootMultiplicity_dvd _ _))
      · exact Or.inr hs
  have hclear (j : ι) : ∃ b : Geom[X], j ∈ s → c j = D*b := by
    rcases hdiv j with ⟨b,hb⟩ | hno
    · exact ⟨b,fun _ => hb⟩
    · exact ⟨0,fun hyes => (hno hyes).elim⟩
  choose b hb using hclear
  have hii := Finset.mem_filter.mp hi
  have hsum : D • (∑ j ∈ s, b j • e j) = 0 := by
    rw [Finset.smul_sum]
    refine (Finset.sum_congr rfl fun j hj => ?_).trans h
    rw [smul_smul,← hb j hj]
  have hz : ∑ j ∈ s, b j • e j = 0 := (smul_eq_zero.mp hsum).resolve_left hd
  refine ⟨b,hz,i,hii.1,?_⟩
  intro he
  obtain ⟨P,hP⟩ := (Polynomial.dvd_iff_isRoot).mpr he
  have hnot : ¬ (Polynomial.X - Polynomial.C x)^(k+1) ∣ c i :=
    Polynomial.pow_rootMultiplicity_not_dvd hii.2 x
  apply hnot
  refine ⟨P, ?_⟩
  calc
    c i = D * b i := hb i hii.1
    _ = _ := by rw [hP]; dsimp only [D]; rw [pow_succ,mul_assoc]


/-- Specialization independence implies function-field independence. -/
theorem independent_fraction {ι : Type*} (x : Geom) (e : ι → Row 4)
    (he : LinearIndependent Geom (fun i => symbolAt x (e i))) :
    LinearIndependent GenericField (fun i => toFraction (e i)) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s a ha i hi
  let R := Geom[X]
  obtain ⟨d,hd⟩ := IsLocalization.exist_integer_multiples (R⁰) s a
  have hd0 : (d : R) ≠ 0 := nonZeroDivisors.ne_zero d.property
  have hc (j : ι) : ∃ c : R, j ∈ s →
      algebraMap R GenericField c = algebraMap R GenericField d * a j := by
    by_cases hm : j ∈ s
    · obtain ⟨c,hc⟩ := hd j hm
      exact ⟨c,fun _ => hc.trans (Algebra.smul_def _ _)⟩
    · exact ⟨0,fun hj => (hm hj).elim⟩
  choose c hc using hc
  have hcleared : ∑ j ∈ s, c j • e j = 0 := by
    apply fraction_injective
    unfold toFraction
    simp only [map_sum,map_zero]
    calc
      _ = ∑ j ∈ s, (algebraMap R GenericField d * a j) •
          MvPolynomial.map (algebraMap R GenericField) (e j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have heq := hc j hj
        change algebraMap Geom[X] GenericField (c j) = _ at heq
        simp only [← MvPolynomial.C_mul', map_mul,MvPolynomial.map_C,heq]
        rw [mul_assoc]
      _ = (algebraMap R GenericField d) • ∑ j ∈ s, a j • toFraction (e j) := by
        rw [Finset.smul_sum]
        simp only [smul_smul, toFraction]
        rfl
      _ = 0 := by rw [ha,smul_zero]
  by_contra ha0
  have hc0 : c i ≠ 0 := by
    intro hz
    have heC := hc i hi
    rw [hz,map_zero] at heC
    have hNZ : algebraMap R GenericField d ≠ 0 := fun hz =>
      hd0 (IsFractionRing.injective R GenericField (hz.trans (map_zero _).symm))
    exact (mul_ne_zero hNZ ha0) heC.symm
  obtain ⟨b,hb,j,hj,hjx⟩ := primitive_relation s c e hcleared ⟨i,hi,hc0⟩ x
  have hx : ∑ j ∈ s, (b j).eval x • symbolAt x (e j) = 0 := by
    have hs := congrArg (symbolAt x) hb
    simp only [map_sum,map_zero,← MvPolynomial.C_mul',map_mul] at hs
    change (∑ j ∈ s, (evalRingHom x) (b j) • symbolAt x (e j)) = 0
    simpa only [symbolAt, MvPolynomial.map_C, MvPolynomial.C_mul'] using hs
  exact hjx (linearIndependent_iff'.mp he s (fun j => (b j).eval x) hx j hj)

theorem clear_denominators (R : FractionJet) :
    ∃ (d : Geom[X]) (Q : Row 4), d ≠ 0 ∧ Q.support = R.support ∧
      toFraction Q = MvPolynomial.C (algebraMap Geom[X] GenericField d) * R := by
  classical
  let M := nonZeroDivisors (Geom[X])
  let d := IsLocalization.commonDenom M R.support R.coeff
  let num := IsLocalization.integerMultiple M R.support R.coeff
  let Q : Row 4 := ∑ a : ↥R.support, MvPolynomial.monomial a.val (num a)
  have hd : (d : Geom[X]) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hi : algebraMap Geom[X] GenericField (d : Geom[X]) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective Geom[X] GenericField)).mpr hd
  have hQ : toFraction Q = MvPolynomial.C (algebraMap Geom[X] GenericField d) * R := by
    unfold toFraction
    ext m
    simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, Q, MvPolynomial.coeff_sum]
    by_cases hm : m ∈ R.support
    · let a : ↥R.support := ⟨m, hm⟩
      rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
      · have hn := IsLocalization.map_integerMultiple M R.support R.coeff a
        change algebraMap Geom[X] GenericField (num a) = (d : Geom[X]) • R.coeff a.val at hn
        rw [Algebra.smul_def] at hn
        simpa [a] using hn
      · intro b _ hba
        have hb : b.val ≠ m := fun h => hba (Subtype.ext h)
        simp [MvPolynomial.coeff_monomial, hb]
    · have hz : R.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
      have hz' : (∑ a : ↥R.support,
          (MvPolynomial.monomial a.val (num a) : Row 4).coeff m) = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        have ha : a.val ≠ m := fun h => hm (h ▸ a.property)
        simp [MvPolynomial.coeff_monomial, ha]
      rw [hz', hz, map_zero, mul_zero]
  refine ⟨d, Q, hd, ?_, hQ⟩
  rw [← support_fraction Q, hQ]
  ext m
  simp [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul, hi]

end
end Shared50Rational
