import ProximityPrize.SubmissionLower.BCHKSFrobeniusProductionOwners6400

/-!
# Counting coordinate-owned Frobenius witnesses

This module packages the finite exceptional sets needed around the
coordinate-owner mechanism.  A direct affine pencil has at most one
degree-drop slope and, at each evaluation coordinate, at most one slope at
which its value vanishes.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial
open ProximityPrize.Benchmark
open BCHKSExactSparsification6400

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000

variable {F D : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype D] [DecidableEq D]

/-- Slopes at which an affine member drops below the maximum endpoint
degree. -/
noncomputable def affineDegreeDropSlopes
    (T : Finset F) (P Q : F[X]) : Finset F := by
  classical
  exact T.filter fun w ↦
    (affinePolynomial P Q w).natDegree < max P.natDegree Q.natDegree

/-- Two distinct specializations cannot both cancel the leading coefficient
of a nontrivial affine pencil. -/
theorem card_affineDegreeDropSlopes_le_one
    (T : Finset F) (P Q : F[X]) (hPQ : IsCoprime P Q) :
    (affineDegreeDropSlopes T P Q).card ≤ 1 := by
  classical
  let d := max P.natDegree Q.natDegree
  have hleading : ¬(P.coeff d = 0 ∧ Q.coeff d = 0) := by
    intro hzero
    by_cases hPzero : P = 0
    · have hQ : Q ≠ 0 := by
        rcases hPQ.ne_zero_or_ne_zero with hP | hQ
        · exact False.elim (hP hPzero)
        · exact hQ
      have hd : d = Q.natDegree := by simp only [d, hPzero,
        Polynomial.natDegree_zero, Nat.zero_le, max_eq_right]
      exact Polynomial.leadingCoeff_ne_zero.mpr hQ
        (by simpa only [hd, Polynomial.coeff_natDegree] using hzero.2)
    · by_cases hQzero : Q = 0
      · have hd : d = P.natDegree := by simp only [d, hQzero,
          Polynomial.natDegree_zero, Nat.zero_le, max_eq_left]
        exact Polynomial.leadingCoeff_ne_zero.mpr hPzero
          (by simpa only [hd, Polynomial.coeff_natDegree] using hzero.1)
      · rcases le_total P.natDegree Q.natDegree with hle | hle
        · have hd : d = Q.natDegree := max_eq_right hle
          exact Polynomial.leadingCoeff_ne_zero.mpr hQzero
            (by simpa only [d, hd, Polynomial.coeff_natDegree] using hzero.2)
        · have hd : d = P.natDegree := max_eq_left hle
          exact Polynomial.leadingCoeff_ne_zero.mpr hPzero
            (by simpa only [d, hd, Polynomial.coeff_natDegree] using hzero.1)
  apply Finset.card_le_one.mpr
  intro u hu v hv
  have huDegree : (affinePolynomial P Q u).natDegree < d := by
    exact (Finset.mem_filter.mp hu).2
  have hvDegree : (affinePolynomial P Q v).natDegree < d := by
    exact (Finset.mem_filter.mp hv).2
  have huCoeff := Polynomial.coeff_eq_zero_of_natDegree_lt huDegree
  have hvCoeff := Polynomial.coeff_eq_zero_of_natDegree_lt hvDegree
  have huEq : P.coeff d + u * Q.coeff d = 0 := by
    simpa only [affinePolynomial, Polynomial.coeff_add,
      Polynomial.coeff_C_mul] using huCoeff
  have hvEq : P.coeff d + v * Q.coeff d = 0 := by
    simpa only [affinePolynomial, Polynomial.coeff_add,
      Polynomial.coeff_C_mul] using hvCoeff
  by_contra huv
  have huvScalar : u - v ≠ 0 := sub_ne_zero.mpr huv
  have hQcoeff : Q.coeff d = 0 := by
    apply (mul_eq_zero.mp (show (u - v) * Q.coeff d = 0 by
      linear_combination huEq - hvEq)).resolve_left huvScalar
  apply hleading
  exact ⟨by simpa only [hQcoeff, mul_zero, add_zero] using huEq, hQcoeff⟩

/-- Slopes for which an affine member vanishes at at least one selected
evaluation coordinate. -/
noncomputable def affineDomainRootSlopes
    (T : Finset F) (P Q : F[X]) (domain : D → F) : Finset F := by
  classical
  exact Finset.univ.biUnion fun i ↦
    T.filter fun w ↦ (affinePolynomial P Q w).eval (domain i) = 0

theorem card_affine_eval_zero_slopes_le_one
    (T : Finset F) (P Q : F[X]) (hPQ : IsCoprime P Q) (x : F) :
    (T.filter fun w ↦ (affinePolynomial P Q w).eval x = 0).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro u hu v hv
  have huEq : P.eval x + u * Q.eval x = 0 := by
    simpa only [affinePolynomial_eval] using (Finset.mem_filter.mp hu).2
  have hvEq : P.eval x + v * Q.eval x = 0 := by
    simpa only [affinePolynomial_eval] using (Finset.mem_filter.mp hv).2
  have hnotBoth := not_both_eval_eq_zero_of_isCoprime P Q hPQ x
  have hQ : Q.eval x ≠ 0 := by
    intro hQzero
    apply hnotBoth
    exact ⟨by simpa only [hQzero, mul_zero, add_zero] using huEq, hQzero⟩
  have hproduct : (u - v) * Q.eval x = 0 := by
    linear_combination huEq - hvEq
  exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right hQ)

theorem card_affineDomainRootSlopes_le
    (T : Finset F) (P Q : F[X]) (hPQ : IsCoprime P Q)
    (domain : D → F) :
    (affineDomainRootSlopes T P Q domain).card ≤ Fintype.card D := by
  classical
  calc
    (affineDomainRootSlopes T P Q domain).card ≤
        (Finset.univ : Finset D).card * 1 := by
      apply Finset.card_biUnion_le_card_mul
      intro i hi
      exact card_affine_eval_zero_slopes_le_one T P Q hPQ (domain i)
    _ = Fintype.card D := by simp

private theorem card_sixfold_union_le
    {A : Type} [DecidableEq A]
    (S₀ S₁ S₂ S₃ S₄ S₅ : Finset A) :
    (S₀ ∪ (S₁ ∪ (S₂ ∪ (S₃ ∪ (S₄ ∪ S₅))))).card ≤
      S₀.card + S₁.card + S₂.card + S₃.card + S₄.card + S₅.card := by
  have h₄ := Finset.card_union_le S₄ S₅
  have h₃ := Finset.card_union_le S₃ (S₄ ∪ S₅)
  have h₂ := Finset.card_union_le S₂ (S₃ ∪ (S₄ ∪ S₅))
  have h₁ := Finset.card_union_le S₁ (S₂ ∪ (S₃ ∪ (S₄ ∪ S₅)))
  have h₀ := Finset.card_union_le S₀
    (S₁ ∪ (S₂ ∪ (S₃ ∪ (S₄ ∪ S₅))))
  omega

/-- The exact hypotheses under which one sparse bad slope is assigned to a
defect coordinate. -/
structure Score6400OwnerEligible
    (e₀ e₁ : Score6400Index → Score6400Field)
    {z₀ : Score6400Field}
    (atom : FrobeniusAmplitudeAtom
      ((pairSupport e₀ e₁).map IRSProfile.domain)
      (score6400ErrorSource e₀) (score6400ErrorSource e₁)
      koalaSexticFrobenius z₀
      ((pairSupport e₀ e₁).card - 54292))
    (w : Score6400Field) : Prop where
  bad : MCABad IRSProfile.baseCode e₀ e₁ 185364 w
  noncancel : w ∉ cancellationSlopes e₀ e₁ (pairSupport e₀ e₁)
  coprimeAmplitude :
    IsCoprime (affinePolynomial atom.direct₀ atom.direct₁ w)
      atom.amplitudeMultiplier
  coprimeConjugate :
    IsCoprime (affinePolynomial atom.direct₀ atom.direct₁ w)
      ((affinePolynomial atom.direct₀ atom.direct₁ w).map
        koalaSexticFrobenius.toRingHom)
  directDegree :
    (affinePolynomial atom.direct₀ atom.direct₁ w).natDegree =
      max atom.direct₀.natDegree atom.direct₁.natDegree
  directNonzero : ∀ i : Score6400Index,
    (affinePolynomial atom.direct₀ atom.direct₁ w).eval
      (IRSProfile.domain i) ≠ 0

noncomputable def score6400OwnerEligibleSlopes
    (e₀ e₁ : Score6400Index → Score6400Field)
    {z₀ : Score6400Field}
    (atom : FrobeniusAmplitudeAtom
      ((pairSupport e₀ e₁).map IRSProfile.domain)
      (score6400ErrorSource e₀) (score6400ErrorSource e₁)
      koalaSexticFrobenius z₀
      ((pairSupport e₀ e₁).card - 54292))
    (Gamma : Finset Score6400Field) : Finset Score6400Field := by
  classical
  exact Gamma.filter fun w ↦ Score6400OwnerEligible e₀ e₁ atom w

/-- Once all explicitly bounded exceptional sets are removed, the remaining
bad slopes are owned by defect coordinates, at most `p` slopes per owner. -/
theorem card_score6400OwnerEligibleSlopes_le
    (e₀ e₁ : Score6400Index → Score6400Field)
    {z₀ : Score6400Field}
    (atom : FrobeniusAmplitudeAtom
      ((pairSupport e₀ e₁).map IRSProfile.domain)
      (score6400ErrorSource e₀) (score6400ErrorSource e₁)
      koalaSexticFrobenius z₀
      ((pairSupport e₀ e₁).card - 54292))
    (normalized : NormalizedPolynomialPair
      atom.denominator atom.amplitudeMultiplier
      ((pairSupport e₀ e₁).card - 54292) atom.baseLoss)
    (Gamma : Finset Score6400Field)
    (hsparse : SparseAt e₀ e₁ 185364)
    (hlarge : 54292 < (pairSupport e₀ e₁).card) :
    (score6400OwnerEligibleSlopes e₀ e₁ atom Gamma).card ≤
      atom.defect.card * 2130706433 := by
  classical
  let Good := score6400OwnerEligibleSlopes e₀ e₁ atom Gamma
  have heligible (w : Score6400Field) (hw : w ∈ Good) :
      Score6400OwnerEligible e₀ e₁ atom w := by
    have hw' : w ∈ Gamma.filter fun u ↦
        Score6400OwnerEligible e₀ e₁ atom u := by
      simpa only [Good, score6400OwnerEligibleSlopes] using hw
    exact (Finset.mem_filter.mp hw').2
  have hdata (w : Score6400Field) (hw : w ∈ Good) :
      Nonempty (Score6400FactoredWitness e₀ e₁ atom w) :=
    exists_score6400FactoredWitness_of_good_sparse_mcaBad
      e₀ e₁ atom w hsparse (heligible w hw).bad
      (heligible w hw).noncancel hlarge (heligible w hw).coprimeAmplitude
      (heligible w hw).coprimeConjugate
  let selected (w : Score6400Field) (hw : w ∈ Good) :
      Score6400FactoredWitness e₀ e₁ atom w :=
    Classical.choice (hdata w hw)
  have howner (w : Score6400Field) (hw : w ∈ Good) :
      ∃ i ∈ (selected w hw).agreementSet,
        IRSProfile.domain i ∈ atom.defect ∧
        (selected w hw).multiplier.eval (IRSProfile.domain i) =
          (e₀ i + w * e₁ i) /
            (atom.direct₀.eval (IRSProfile.domain i) +
              w * atom.direct₁.eval (IRSProfile.domain i)) :=
    (selected w hw).exists_defect_owner e₀ e₁
      (heligible w hw).directDegree (heligible w hw).directNonzero
  let multiplier (w : Score6400Field) : Score6400Field[X] :=
    if hw : w ∈ Good then (selected w hw).multiplier else 0
  let ownerIndex (w : Score6400Field) : Score6400Index :=
    if hw : w ∈ Good then Classical.choose (howner w hw) else 0
  let ownerPoint (w : Score6400Field) : Score6400Field :=
    IRSProfile.domain (ownerIndex w)
  have hownerDefect (w : Score6400Field) (hw : w ∈ Good) :
      ownerPoint w ∈ atom.defect := by
    simpa only [ownerPoint, ownerIndex, dif_pos hw] using
      (Classical.choose_spec (howner w hw)).2.1
  have hownerValue (w : Score6400Field) (hw : w ∈ Good) :
      (multiplier w).eval (ownerPoint w) =
        (score6400ErrorSource e₀ (ownerPoint w) +
            w * score6400ErrorSource e₁ (ownerPoint w)) /
          (atom.direct₀.eval (ownerPoint w) +
            w * atom.direct₁.eval (ownerPoint w)) := by
    simpa only [multiplier, ownerPoint, ownerIndex, dif_pos hw,
      score6400ErrorSource_domain] using
      (Classical.choose_spec (howner w hw)).2.2
  let Owned (x : Score6400Field) : Finset Score6400Field :=
    Good.filter fun w ↦ ownerPoint w = x
  have hownedCap : ∀ x ∈ atom.defect, (Owned x).card ≤ 2130706433 := by
    intro x hxDefect
    have hxSource :
        x ∈ (pairSupport e₀ e₁).map IRSProfile.domain :=
      (Finset.mem_filter.mp hxDefect).1
    obtain ⟨ix, hixSupport, hix⟩ := Finset.mem_map.mp hxSource
    have hfixed : koalaSexticFrobenius x = x := by
      rw [← hix]
      exact koalaSexticFrobenius_fixed_domain ix
    have hcoeff : ¬(
        normalized.first.eval x = 0 ∧
          normalized.second.eval x = 0) :=
      not_both_eval_eq_zero_of_isCoprime
        normalized.first normalized.second normalized.coprime x
    let value : Score6400Field → Score6400Field := fun w ↦
      (multiplier w).eval x
    have hvalueEquation : ∀ w ∈ Owned x,
        normalized.first.eval x * koalaSexticFrobenius (value w) =
          normalized.second.eval x * value w := by
      intro w hw
      have hwGood : w ∈ Good := (Finset.mem_filter.mp hw).1
      have heq := (selected w hwGood).multiplier_eval_semilinear_eq
        e₀ e₁ normalized x hfixed
      simpa only [value, multiplier, dif_pos hwGood] using heq
    have hden : ∀ w ∈ Good,
        atom.direct₀.eval x + w * atom.direct₁.eval x ≠ 0 := by
      intro w hw
      have hel := heligible w hw
      rw [← hix]
      simpa only [affinePolynomial_eval] using hel.directNonzero ix
    have hdefect :
        atom.direct₀.eval x * score6400ErrorSource e₁ x ≠
          atom.direct₁.eval x * score6400ErrorSource e₀ x :=
      (Finset.mem_filter.mp hxDefect).2
    have hmobius := mobiusValue_injectiveOn_of_defect
      (score6400ErrorSource e₀ x) (score6400ErrorSource e₁ x)
      (atom.direct₀.eval x) (atom.direct₁.eval x) Good hdefect hden
    have hvalueInjective : ((Owned x : Finset Score6400Field) :
        Set Score6400Field).InjOn value := by
      intro u hu v hv huv
      have huGood : u ∈ Good := (Finset.mem_filter.mp hu).1
      have hvGood : v ∈ Good := (Finset.mem_filter.mp hv).1
      have huPoint : ownerPoint u = x := (Finset.mem_filter.mp hu).2
      have hvPoint : ownerPoint v = x := (Finset.mem_filter.mp hv).2
      have huFormula : value u =
          (score6400ErrorSource e₀ x +
              u * score6400ErrorSource e₁ x) /
            (atom.direct₀.eval x + u * atom.direct₁.eval x) := by
        simpa only [value, huPoint] using hownerValue u huGood
      have hvFormula : value v =
          (score6400ErrorSource e₀ x +
              v * score6400ErrorSource e₁ x) /
            (atom.direct₀.eval x + v * atom.direct₁.eval x) := by
        simpa only [value, hvPoint] using hownerValue v hvGood
      apply hmobius huGood hvGood
      exact huFormula.symm.trans (huv.trans hvFormula)
    exact card_le_of_injective_frobenius_equation
      (F := Score6400Field) (A := Score6400Field)
      koalaSexticFrobenius 2130706433 (by norm_num)
      (fun y ↦ koalaSexticFrobenius_apply y)
      (normalized.first.eval x) (normalized.second.eval x) hcoeff
      (Owned x) value hvalueEquation hvalueInjective
  have hcover : Good ⊆ atom.defect.biUnion Owned := by
    intro w hw
    exact Finset.mem_biUnion.mpr
      ⟨ownerPoint w, hownerDefect w hw,
        Finset.mem_filter.mpr ⟨hw, rfl⟩⟩
  have hcard : Good.card ≤ atom.defect.card * 2130706433 := by
    calc
      Good.card ≤ (atom.defect.biUnion Owned).card :=
        Finset.card_le_card hcover
      _ ≤ atom.defect.card * 2130706433 := by
        apply Finset.card_biUnion_le_card_mul
        exact hownedCap
  simpa only [Good] using hcard

/-- Complete sparse bad-slope cover from any supplied bound on the conjugate
coprimality exception.  Every bad slope is either coordinate-owned or belongs
to one of five explicit exceptional sets. -/
theorem card_score6400_sparse_mcaBad_slopes_le_of_conjugate_bound
    (e₀ e₁ : Score6400Index → Score6400Field)
    {z₀ : Score6400Field}
    (atom : FrobeniusAmplitudeAtom
      ((pairSupport e₀ e₁).map IRSProfile.domain)
      (score6400ErrorSource e₀) (score6400ErrorSource e₁)
      koalaSexticFrobenius z₀
      ((pairSupport e₀ e₁).card - 54292))
    (normalized : NormalizedPolynomialPair
      atom.denominator atom.amplitudeMultiplier
      ((pairSupport e₀ e₁).card - 54292) atom.baseLoss)
    (Gamma : Finset Score6400Field)
    (hsparse : SparseAt e₀ e₁ 185364)
    (hlarge : 54292 < (pairSupport e₀ e₁).card)
    (conjugateCap : ℕ)
    (hconjugate :
      (nonCoprimeConjugateSlopes Gamma koalaSexticFrobenius
        atom.direct₀ atom.direct₁).card ≤ conjugateCap) :
    (restrictedMCABadSlopes Gamma IRSProfile.baseCode e₀ e₁ 185364).card ≤
      atom.defect.card * 2130706433 +
        (pairSupport e₀ e₁).card +
        atom.amplitudeMultiplier.natDegree +
        conjugateCap + 1 + 262144 := by
  classical
  let Bad := restrictedMCABadSlopes Gamma IRSProfile.baseCode e₀ e₁ 185364
  let Good := score6400OwnerEligibleSlopes e₀ e₁ atom Gamma
  let Cancel := cancellationSlopes e₀ e₁ (pairSupport e₀ e₁)
  let Amp := nonCoprimeAffineSlopes Gamma atom.direct₀ atom.direct₁
    atom.amplitudeMultiplier
  let Conj := nonCoprimeConjugateSlopes Gamma koalaSexticFrobenius
    atom.direct₀ atom.direct₁
  let Drop := affineDegreeDropSlopes Gamma atom.direct₀ atom.direct₁
  let Domain := affineDomainRootSlopes Gamma atom.direct₀ atom.direct₁
    IRSProfile.domain
  let Covered := Good ∪ (Cancel ∪ (Amp ∪ (Conj ∪ (Drop ∪ Domain))))
  have hcover : Bad ⊆ Covered := by
    intro w hwBad
    have hwBad' : w ∈ Gamma ∧
        MCABad IRSProfile.baseCode e₀ e₁ 185364 w := by
      simpa only [Bad, restrictedMCABadSlopes] using
        (Finset.mem_filter.mp hwBad)
    by_cases hcancel : w ∈ Cancel
    · exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_union.mpr (Or.inl hcancel)))
    by_cases hamp : IsCoprime
        (affinePolynomial atom.direct₀ atom.direct₁ w)
        atom.amplitudeMultiplier
    · by_cases hconj : IsCoprime
          (affinePolynomial atom.direct₀ atom.direct₁ w)
          ((affinePolynomial atom.direct₀ atom.direct₁ w).map
            koalaSexticFrobenius.toRingHom)
      · by_cases hdeg :
            (affinePolynomial atom.direct₀ atom.direct₁ w).natDegree =
              max atom.direct₀.natDegree atom.direct₁.natDegree
        · by_cases hdomain : ∀ i : Score6400Index,
              (affinePolynomial atom.direct₀ atom.direct₁ w).eval
                (IRSProfile.domain i) ≠ 0
          · have hwGood : w ∈ Good := by
              change w ∈ score6400OwnerEligibleSlopes e₀ e₁ atom Gamma
              rw [score6400OwnerEligibleSlopes, Finset.mem_filter]
              exact ⟨hwBad'.1,
                { bad := hwBad'.2
                  noncancel := hcancel
                  coprimeAmplitude := hamp
                  coprimeConjugate := hconj
                  directDegree := hdeg
                  directNonzero := hdomain }⟩
            exact Finset.mem_union.mpr (Or.inl hwGood)
          · push Not at hdomain
            obtain ⟨i, hi⟩ := hdomain
            have hwDomain : w ∈ Domain := by
              change w ∈ affineDomainRootSlopes Gamma atom.direct₀
                atom.direct₁ IRSProfile.domain
              rw [affineDomainRootSlopes, Finset.mem_biUnion]
              exact ⟨i, Finset.mem_univ _,
                Finset.mem_filter.mpr ⟨hwBad'.1, hi⟩⟩
            exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr
              (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr
                (Finset.mem_union.mpr (Or.inr hwDomain)))))))))
        · have hwDrop : w ∈ Drop := by
            change w ∈ affineDegreeDropSlopes Gamma atom.direct₀ atom.direct₁
            rw [affineDegreeDropSlopes, Finset.mem_filter]
            refine ⟨hwBad'.1, ?_⟩
            exact lt_of_le_of_ne
              (affinePolynomial_natDegree_le atom.direct₀ atom.direct₁ w) hdeg
          exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr
            (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr
              (Finset.mem_union.mpr (Or.inl hwDrop)))))))))
      · have hwConj : w ∈ Conj := by
          change w ∈ nonCoprimeConjugateSlopes Gamma koalaSexticFrobenius
            atom.direct₀ atom.direct₁
          rw [nonCoprimeConjugateSlopes, Finset.mem_filter]
          exact ⟨hwBad'.1, hconj⟩
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr
          (Finset.mem_union.mpr (Or.inr
            (Finset.mem_union.mpr (Or.inl hwConj)))))))
    · have hwAmp : w ∈ Amp := by
        change w ∈ nonCoprimeAffineSlopes Gamma atom.direct₀ atom.direct₁
          atom.amplitudeMultiplier
        rw [nonCoprimeAffineSlopes, Finset.mem_filter]
        exact ⟨hwBad'.1, hamp⟩
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr
        (Finset.mem_union.mpr (Or.inl hwAmp)))))
  have hGood : Good.card ≤ atom.defect.card * 2130706433 := by
    simpa only [Good] using card_score6400OwnerEligibleSlopes_le
      e₀ e₁ atom normalized Gamma hsparse hlarge
  have hCancel : Cancel.card ≤ (pairSupport e₀ e₁).card := by
    simpa only [Cancel] using card_cancellationSlopes_le
      e₀ e₁ (pairSupport e₀ e₁)
  have hAmp : Amp.card ≤ atom.amplitudeMultiplier.natDegree := by
    simpa only [Amp] using atom.card_bad_amplitude_slopes_le Gamma
  have hConj : Conj.card ≤ conjugateCap := by
    simpa only [Conj] using hconjugate
  have hDrop : Drop.card ≤ 1 := by
    simpa only [Drop] using card_affineDegreeDropSlopes_le_one
      Gamma atom.direct₀ atom.direct₁ atom.direct_coprime
  have hDomain : Domain.card ≤ 262144 := by
    have h := card_affineDomainRootSlopes_le Gamma atom.direct₀ atom.direct₁
      atom.direct_coprime IRSProfile.domain
    change Domain.card ≤ 2 ^ 18 at h
    norm_num at h
    exact h
  have hCovered : Covered.card ≤
      Good.card + Cancel.card + Amp.card + Conj.card + Drop.card + Domain.card := by
    simpa only [Covered] using
      card_sixfold_union_le Good Cancel Amp Conj Drop Domain
  have hBadCovered : Bad.card ≤ Covered.card := Finset.card_le_card hcover
  simpa only [Bad] using
    (show Bad.card ≤ atom.defect.card * 2130706433 +
        (pairSupport e₀ e₁).card +
        atom.amplitudeMultiplier.natDegree +
        conjugateCap + 1 + 262144 by omega)

/-- Positive-direct-degree specialization, using the checked conjugate
resultant bound `d*(p+1)`. -/
theorem card_score6400_sparse_mcaBad_slopes_le_of_directDegree_pos
    (e₀ e₁ : Score6400Index → Score6400Field)
    {z₀ : Score6400Field}
    (atom : FrobeniusAmplitudeAtom
      ((pairSupport e₀ e₁).map IRSProfile.domain)
      (score6400ErrorSource e₀) (score6400ErrorSource e₁)
      koalaSexticFrobenius z₀
      ((pairSupport e₀ e₁).card - 54292))
    (normalized : NormalizedPolynomialPair
      atom.denominator atom.amplitudeMultiplier
      ((pairSupport e₀ e₁).card - 54292) atom.baseLoss)
    (Gamma : Finset Score6400Field)
    (hsparse : SparseAt e₀ e₁ 185364)
    (hlarge : 54292 < (pairSupport e₀ e₁).card)
    (hdegree : 0 < max atom.direct₀.natDegree atom.direct₁.natDegree) :
    (restrictedMCABadSlopes Gamma IRSProfile.baseCode e₀ e₁ 185364).card ≤
      atom.defect.card * 2130706433 +
        (pairSupport e₀ e₁).card +
        atom.amplitudeMultiplier.natDegree +
        max atom.direct₀.natDegree atom.direct₁.natDegree *
          (2130706433 + 1) + 1 + 262144 := by
  apply card_score6400_sparse_mcaBad_slopes_le_of_conjugate_bound
    e₀ e₁ atom normalized Gamma hsparse hlarge
    (max atom.direct₀.natDegree atom.direct₁.natDegree *
      (2130706433 + 1))
  exact card_nonCoprimeConjugateSlopes_le_of_coprime
    Gamma koalaSexticFrobenius 2130706433 atom.direct₀ atom.direct₁
    (by norm_num) atom.direct_coprime hdegree
    (fun w hw ↦ koalaSexticFrobenius_apply w)

/-- When both direct endpoints have degree zero, every conjugate-coprimality
failure makes the affine member vanish on the whole domain.  It is therefore
already covered by the domain-root exception. -/
theorem card_score6400_nonCoprimeConjugateSlopes_le_of_directDegree_zero
    (e₀ e₁ : Score6400Index → Score6400Field)
    {z₀ : Score6400Field}
    (atom : FrobeniusAmplitudeAtom
      ((pairSupport e₀ e₁).map IRSProfile.domain)
      (score6400ErrorSource e₀) (score6400ErrorSource e₁)
      koalaSexticFrobenius z₀
      ((pairSupport e₀ e₁).card - 54292))
    (Gamma : Finset Score6400Field)
    (hdegree : max atom.direct₀.natDegree atom.direct₁.natDegree = 0) :
    (nonCoprimeConjugateSlopes Gamma koalaSexticFrobenius
      atom.direct₀ atom.direct₁).card ≤ 262144 := by
  classical
  let Conj := nonCoprimeConjugateSlopes Gamma koalaSexticFrobenius
    atom.direct₀ atom.direct₁
  let Domain := affineDomainRootSlopes Gamma atom.direct₀ atom.direct₁
    IRSProfile.domain
  have hsubset : Conj ⊆ Domain := by
    intro w hw
    have hw' : w ∈ Gamma ∧ ¬IsCoprime
        (affinePolynomial atom.direct₀ atom.direct₁ w)
        ((affinePolynomial atom.direct₀ atom.direct₁ w).map
          koalaSexticFrobenius.toRingHom) := by
      simpa only [Conj, nonCoprimeConjugateSlopes] using
        (Finset.mem_filter.mp hw)
    by_contra hnotDomain
    have hnonzero :
        (affinePolynomial atom.direct₀ atom.direct₁ w).eval
          (IRSProfile.domain (0 : Score6400Index)) ≠ 0 := by
      intro hzero
      apply hnotDomain
      change w ∈ affineDomainRootSlopes Gamma atom.direct₀ atom.direct₁
        IRSProfile.domain
      rw [affineDomainRootSlopes, Finset.mem_biUnion]
      exact ⟨0, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hw'.1, hzero⟩⟩
    let Cw := affinePolynomial atom.direct₀ atom.direct₁ w
    have hCwNe : Cw ≠ 0 := by
      intro hzero
      change Cw.eval (IRSProfile.domain (0 : Score6400Index)) ≠ 0 at hnonzero
      apply hnonzero
      rw [hzero, Polynomial.eval_zero]
    have hCwNat : Cw.natDegree = 0 := by
      have hle := affinePolynomial_natDegree_le atom.direct₀ atom.direct₁ w
      rw [hdegree] at hle
      exact Nat.eq_zero_of_le_zero hle
    have hCwDegree : Cw.degree = 0 := by
      rw [Polynomial.degree_eq_natDegree hCwNe, hCwNat]
      rfl
    have hCwUnit : IsUnit Cw :=
      Polynomial.isUnit_iff_degree_eq_zero.mpr hCwDegree
    have hcoprime : IsCoprime Cw
        (Cw.map koalaSexticFrobenius.toRingHom) := by
      obtain ⟨u, hu⟩ := isUnit_iff_exists_inv'.mp hCwUnit
      exact ⟨u, 0, by rw [zero_mul, add_zero, hu]⟩
    exact hw'.2 (by simpa only [Cw] using hcoprime)
  have hDomain : Domain.card ≤ 262144 := by
    have h := card_affineDomainRootSlopes_le Gamma atom.direct₀ atom.direct₁
      atom.direct_coprime IRSProfile.domain
    change Domain.card ≤ 2 ^ 18 at h
    norm_num at h
    exact h
  have hcard : Conj.card ≤ 262144 :=
    (Finset.card_le_card hsubset).trans hDomain
  simpa only [Conj] using hcard

/-- Zero-direct-degree sparse branch.  The repeated `262144` terms are the
conjugate set and its containing domain-root cover; this deliberate loose
count remains far below the production budget. -/
theorem card_score6400_sparse_mcaBad_slopes_le_of_directDegree_zero
    (e₀ e₁ : Score6400Index → Score6400Field)
    {z₀ : Score6400Field}
    (atom : FrobeniusAmplitudeAtom
      ((pairSupport e₀ e₁).map IRSProfile.domain)
      (score6400ErrorSource e₀) (score6400ErrorSource e₁)
      koalaSexticFrobenius z₀
      ((pairSupport e₀ e₁).card - 54292))
    (normalized : NormalizedPolynomialPair
      atom.denominator atom.amplitudeMultiplier
      ((pairSupport e₀ e₁).card - 54292) atom.baseLoss)
    (Gamma : Finset Score6400Field)
    (hsparse : SparseAt e₀ e₁ 185364)
    (hlarge : 54292 < (pairSupport e₀ e₁).card)
    (hdegree : max atom.direct₀.natDegree atom.direct₁.natDegree = 0) :
    (restrictedMCABadSlopes Gamma IRSProfile.baseCode e₀ e₁ 185364).card ≤
      atom.defect.card * 2130706433 +
        (pairSupport e₀ e₁).card +
        atom.amplitudeMultiplier.natDegree + 262144 + 1 + 262144 := by
  apply card_score6400_sparse_mcaBad_slopes_le_of_conjugate_bound
    e₀ e₁ atom normalized Gamma hsparse hlarge 262144
  exact card_score6400_nonCoprimeConjugateSlopes_le_of_directDegree_zero
    e₀ e₁ atom Gamma hdegree

/-- Uniform production sparse bound.  The round number `48·10¹²` is a
slight relaxation of the checked worst case (about `4.7914·10¹²`). -/
theorem card_score6400_sparse_mcaBad_slopes_le
    (e₀ e₁ : Score6400Index → Score6400Field)
    {z₀ : Score6400Field}
    (atom : FrobeniusAmplitudeAtom
      ((pairSupport e₀ e₁).map IRSProfile.domain)
      (score6400ErrorSource e₀) (score6400ErrorSource e₁)
      koalaSexticFrobenius z₀
      ((pairSupport e₀ e₁).card - 54292))
    (normalized : NormalizedPolynomialPair
      atom.denominator atom.amplitudeMultiplier
      ((pairSupport e₀ e₁).card - 54292) atom.baseLoss)
    (Gamma : Finset Score6400Field)
    (hsparse : SparseAt e₀ e₁ 185364)
    (hlarge : 54292 < (pairSupport e₀ e₁).card) :
    (restrictedMCABadSlopes Gamma IRSProfile.baseCode e₀ e₁ 185364).card ≤
      48000000000000 := by
  have hsupport : (pairSupport e₀ e₁).card ≤ 76780 := by
    change (pairSupport e₀ e₁).card ≤
      Fintype.card Score6400Index - 185364 at hsparse
    norm_num [Score6400Index, IRSProfile.Index] at hsparse
    exact hsparse
  have hh : (pairSupport e₀ e₁).card - 54292 ≤ 22488 := by omega
  have hdefect := atom.card_defect_le_loss
  have hamp := atom.amplitudeMultiplier_degree
  have hdirect₀ := atom.direct₀_degree
  have hdirect₁ := atom.direct₁_degree
  have hdirectLoss :
      max atom.direct₀.natDegree atom.direct₁.natDegree +
          (atom.baseLoss + atom.gcdLoss) <
        (pairSupport e₀ e₁).card - 54292 := by
    by_cases hle : atom.direct₀.natDegree ≤ atom.direct₁.natDegree
    · rw [max_eq_right hle]
      omega
    · rw [max_eq_left (Nat.le_of_not_ge hle)]
      omega
  by_cases hzero :
      max atom.direct₀.natDegree atom.direct₁.natDegree = 0
  · have hbound := card_score6400_sparse_mcaBad_slopes_le_of_directDegree_zero
      e₀ e₁ atom normalized Gamma hsparse hlarge hzero
    omega
  · have hpositive :
        0 < max atom.direct₀.natDegree atom.direct₁.natDegree :=
      Nat.pos_of_ne_zero hzero
    have hbound := card_score6400_sparse_mcaBad_slopes_le_of_directDegree_pos
      e₀ e₁ atom normalized Gamma hsparse hlarge hpositive
    omega

end ProximityPrize.SubmissionLower
