import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ConstraintMatrix
import ArkLib.Data.Polynomial.Differential.RationalTaylorDerivativeDegree
import ArkLib.Data.Polynomial.ResultantDegree
import ProximityPrize.SubmissionLower.Fast005
import ProximityPrize.SubmissionLower.Fast007
import ProximityPrize.SubmissionLower.Fast008
import ProximityPrize.SubmissionLower.Fast009
set_option Elab.async false

section PackSource_WeightedTaylor
set_option autoImplicit true
/-! Weighted rational Taylor bounds retaining both jet total degree and jet index.
The intended weights of (Y0,Y1,Y2) are (a,a+b,a+2b).
This file alone does not assert a list bound or a protocol claim. -/
namespace Astra7
open MvPolynomial PolynomialDifferential
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 4000

def jetWeight (a b n : ℕ) : Option (Fin n) → ℕ :=
  fun i => i.elim 0 (fun j => a + b * j.val)

def coeffWeight (a b n : ℕ) : Fin n → ℕ := fun j => a + b * j.val

def displacementWeight (b n : ℕ) : Option (Fin n) → ℕ :=
  fun i => i.elim b (fun _ => 0)

variable {F : Type*}
section Semiring
variable [CommSemiring F]

theorem universalJet_offset (a b K j : ℕ) :
    SupportWeightOffset (Finsupp.weight (jetWeight a b K))
      (Finsupp.weight (displacementWeight b K)) (a + b*j)
      (universalTaylorJet (F := F) K j) := by
  classical
  apply SupportWeightOffset.sum
  intro l hl
  apply SupportWeightOffset.monomial
  have hj := (Finset.mem_filter.mp hl).2
  simp only [map_add, Finsupp.weight_single, smul_eq_mul,
    jetWeight, displacementWeight, Option.elim_some, Option.elim_none,
    mul_zero, zero_add, one_mul, add_zero]
  have hsub : l.val - j + j = l.val := Nat.sub_add_cancel hj
  nlinarith

theorem universalResidual_offset {r : ℕ} (a b K : ℕ) (center : F)
    (Q : DifferentialPolynomial F r) :
    SupportWeightOffset (Finsupp.weight (jetWeight a b K))
      (Finsupp.weight (displacementWeight b K))
      (Q.weightedTotalDegree (jetWeight a b (r+1)))
      (universalTaylorResidual K center Q) := by
  apply supportWeightOffset_aeval
  intro i
  cases i with
  | none =>
    apply SupportWeightOffset.add
    · exact SupportWeightOffset.C center
    · apply SupportWeightOffset.monomial
      simp [jetWeight, displacementWeight, Finsupp.weight_single]
  | some j => exact universalJet_offset a b K j.val

theorem residual_coeff_weight {r : ℕ} (a b K : ℕ) (center : F)
    (Q : DifferentialPolynomial F r) (h : ℕ) (m : Fin K →₀ ℕ)
    (hm : m ∈ ((optionEquivLeft F (Fin K)
      (universalTaylorResidual K center Q)).coeff h).support) :
    Finsupp.weight (coeffWeight a b K) m ≤
      b*h + Q.weightedTotalDegree (jetWeight a b (r+1)) := by
  have hb := universalResidual_offset a b K center Q (m.optionElim h)
    ((mem_support_coeff_optionEquivLeft F).mp hm)
  change Finsupp.weight (fun i : Option (Fin K) => i.elim 0 (coeffWeight a b K))
    (m.optionElim h) ≤
    Finsupp.weight (fun i : Option (Fin K) => i.elim b (fun _ => 0))
      (m.optionElim h) + _ at hb
  simp only [Finsupp.weight_optionElim, zero_mul, zero_add] at hb
  simpa [Finsupp.weight_apply, Nat.mul_comm] using hb

theorem initialSeparant_weight {r : ℕ} [Nontrivial F]
    (a b : ℕ) (center : F) (Q : DifferentialPolynomial F r) :
    (initialJetSeparant center Q).weightedTotalDegree (coeffWeight a b (r+1)) ≤
      Q.weightedTotalDegree (jetWeight a b (r+1)) - (a + b*r) := by
  apply le_trans (weightedTotalDegree_aeval_le_of_le
    (jetWeight a b (r+1)) (coeffWeight a b (r+1)) _ _ ?_)
  · simpa [initialJetSeparant, separant, jetWeight] using
      weightedTotalDegree_pderiv_le_sub (jetWeight a b (r+1))
        (some (Fin.last r)) Q
  · intro i
    cases i with
    | none => simp [jetWeight]
    | some j =>
        change (MvPolynomial.X j : MvPolynomial (Fin (r+1)) F).weightedTotalDegree
          (coeffWeight a b (r+1)) ≤ a+b*j.val
        rw [X, weightedTotalDegree_monomial _ _ 1 one_ne_zero]
        simp [Finsupp.weight_single, coeffWeight]

end Semiring

section Field
variable [Field F]

theorem rationalTaylor_weight {r : ℕ} (a b V : ℕ) (center : F)
    (Q : DifferentialPolynomial F r)
    (hV : a + b*r ≤ V)
    (hQ : Q.weightedTotalDegree (jetWeight a b (r+1)) ≤ V) (l : ℕ) :
    (rationalTaylorNumerator center Q l).weightedTotalDegree (coeffWeight a b (r+1)) ≤
      (2*(l-r)-1) * (V-(a+b*r)) + a + b*l := by
  have hs := (initialSeparant_weight a b center Q).trans
    (Nat.sub_le_sub_right hQ (a+b*r))
  induction l using Nat.strong_induction_on with
  | h l ih =>
    rw [rationalTaylorNumerator]
    split_ifs with hl
    · have he : 2*(l-r)-1 = 0 := by omega
      rw [he, X, weightedTotalDegree_monomial _ _ 1 one_ne_zero]
      simp [Finsupp.weight_single, coeffWeight]
    · have hlr : r < l := by omega
      have hden : ∀ m ∈ ((optionEquivLeft F (Fin l)
          (universalTaylorResidual l center Q)).coeff (l-r)).support,
          Finsupp.weight (fun i : Fin l => 2*(i.val-r)-1) m ≤ 2*(l-r)-2 := by
        intro m hm
        exact denominator_weight_le_of_mem_universalTaylorResidual_coeff
          (r := r) (K := l) (h := l-r) (by omega) center Q m hm
      have hw : ∀ m ∈ ((optionEquivLeft F (Fin l)
          (universalTaylorResidual l center Q)).coeff (l-r)).support,
          (C (((optionEquivLeft F (Fin l)
            (universalTaylorResidual l center Q)).coeff (l-r)).coeff m) :
            MvPolynomial (Fin (r+1)) F).weightedTotalDegree (coeffWeight a b (r+1)) +
          Finsupp.weight (coeffWeight a b l) m ≤ b*(l-r)+V := by
        intro m hm
        simpa using (residual_coeff_weight a b l center Q (l-r) m hm).trans
          (Nat.add_le_add_left hQ _)
      have hd := weightedTotalDegree_clearedSubstitution_le_of_coeff C
        (initialJetSeparant center Q)
        (fun i : Fin l => rationalTaylorNumerator center Q i.val)
        (fun i => 2*(i.val-r)-1) (coeffWeight a b l) (coeffWeight a b (r+1))
        (2*(l-r)-2) (V-(a+b*r)) (b*(l-r)+V)
        ((optionEquivLeft F (Fin l) (universalTaylorResidual l center Q)).coeff (l-r))
        hs (fun i => by simpa [coeffWeight, Nat.add_assoc] using ih i.val i.isLt) hden hw
      have hm := weightedTotalDegree_mul_le (coeffWeight a b (r+1))
        (-C ((l.choose r : F)⁻¹))
        (clearedSubstitution C (initialJetSeparant center Q)
          (fun i : Fin l => rationalTaylorNumerator center Q i.val)
          (fun i => 2*(i.val-r)-1) (2*(l-r)-2)
          ((optionEquivLeft F (Fin l) (universalTaylorResidual l center Q)).coeff (l-r)))
      have hc : (-C ((l.choose r : F)⁻¹) : MvPolynomial (Fin (r+1)) F).weightedTotalDegree
          (coeffWeight a b (r+1)) = 0 := by
        rw [← map_neg C]
        exact weightedTotalDegree_C _ _
      rw [hc, zero_add] at hm
      apply hm.trans (hd.trans ?_)
      have he : 2*(l-r)-1 = (2*(l-r)-2)+1 := by omega
      have hsub := Nat.sub_add_cancel hV
      have hlsub : l-r+r=l := Nat.sub_add_cancel (Nat.le_of_lt hlr)
      rw [he]
      nlinarith

theorem commonTaylor_weight {r : ℕ} (a b V K τ : ℕ) (center : F)
    (Q : DifferentialPolynomial F r) (hτ : TaylorExponentSufficient r K τ)
    (hV : a+b*r ≤ V)
    (hQ : Q.weightedTotalDegree (jetWeight a b (r+1)) ≤ V) (l : Fin K) :
    (commonTaylorNumerator center Q τ l.val).weightedTotalDegree (coeffWeight a b (r+1)) ≤
      τ * (V-(a+b*r)) + a + b*l.val := by
  have hd := rationalTaylor_weight a b V center Q hV hQ l.val
  have hs := (initialSeparant_weight a b center Q).trans
    (Nat.sub_le_sub_right hQ (a+b*r))
  have hp := (weightedTotalDegree_pow_le (coeffWeight a b (r+1))
    (initialJetSeparant center Q) (τ-(2*(l.val-r)-1))).trans
      (Nat.mul_le_mul_left _ hs)
  have hm := weightedTotalDegree_mul_le (coeffWeight a b (r+1))
    (rationalTaylorNumerator center Q l.val)
    (initialJetSeparant center Q ^ (τ-(2*(l.val-r)-1)))
  have he := Nat.sub_add_cancel (hτ l)
  unfold commonTaylorNumerator
  nlinarith

end Field
end
end Astra7
end PackSource_WeightedTaylor

section PackSource_FiniteFiberIncidence
set_option autoImplicit true
namespace Astra7
open MvPolynomial
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 4000

variable {F σ ι : Type*} [Field F] [IsAlgClosed F] [Finite σ] [Fintype ι]

/-- A finite fiber, as opposed to a singleton fiber, is enough to rule out
too many persistent cuts on a positive-dimensional principal open. -/
theorem ncard_cuts_lt_of_finite
    {Q : Ideal (MvPolynomial σ F)} [Q.IsPrime] {s : MvPolynomial σ F} (hs : s ∉ Q)
    (cuts : ι → MvPolynomial σ F) {m : ℕ}
    (hd : 0 < (affineHilbertPolynomial Q).natDegree)
    (hfinite : ∀ T : Finset ι, T.card = m →
      {x : σ → F | x ∈ zeroLocus F Q ∧ aeval x s ≠ 0 ∧
        ∀ i ∈ T, aeval x (cuts i) = 0}.Finite) :
    {i | cuts i ∈ Q}.ncard < m := by
  by_contra hm
  obtain ⟨T, hTsub, hTcard⟩ := Set.exists_subset_card_eq (not_lt.mp hm)
  have hreg : IsLeftRegular (Ideal.Quotient.mk Q s) :=
    IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (mt Ideal.Quotient.eq_zero_iff_mem.mp hs)
  have hf : {x : σ → F | x ∈ zeroLocus F Q ∧ aeval x s ≠ 0}.Finite :=
    (hfinite T.toFinite.toFinset (by rw [← Set.ncard_eq_toFinset_card]; exact hTcard)).subset
      (fun x hx => ⟨hx.1, hx.2, fun i hi => hx.1 _ (hTsub (by simpa using hi))⟩)
  have := (finite_principalOpen_iff_natDegree_affineHilbertPolynomial_eq_zero hreg).mp hf
  omega

/-- Sharp fixed-threshold incidence on a hypersurface. Finitely many points
over every m cuts suffice; no uniqueness or degree of the fibers is assumed. -/
theorem hypersurface_card_le_of_finite_fibers
    {g : MvPolynomial σ F} (hg : g ≠ 0) (s : MvPolynomial σ F)
    {v b A m : ℕ} (hv : g.totalDegree ≤ v)
    (cuts : ι → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hb : 0 < b) (hmA : m ≤ A)
    (hfinite : ∀ T : Finset ι, T.card = m →
      {x : σ → F | aeval x g = 0 ∧ aeval x s ≠ 0 ∧
        ∀ i ∈ T, aeval x (cuts i) = 0}.Finite)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, aeval x g = 0 ∧ aeval x s ≠ 0)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (cuts i) = 0}.ncard) :
    (S.card : ℚ) ≤ v *
      ((((Fintype.card ι - m + 1) * b : ℕ) : ℚ) / ((A-m+1 : ℕ) : ℚ)) ^
        (Nat.card σ - 1) := by
  classical
  let T₀ := (Ideal.span {g}).retainedMinimalPrimes s
  have hprime : ∀ P ∈ T₀, P.IsPrime := by
    intro P hP
    exact (Ideal.mem_retainedMinimalPrimes.mp hP).1.isPrime
  have hgP : ∀ P ∈ T₀, g ∈ P := by
    intro P hP
    exact (Ideal.mem_retainedMinimalPrimes.mp hP).1.le (Ideal.mem_span_singleton_self g)
  have hdim : ∀ P ∈ T₀,
      (affineHilbertPolynomial P).natDegree ≤ Nat.card σ - 1 := by
    intro P hP
    letI := hprime P hP
    exact natDegree_affineHilbertPolynomial_le_of_mem hg (hgP P hP)
  have hpot : ∑ P ∈ T₀, affineDegree P * (1 : ℚ) ^
      (affineHilbertPolynomial P).natDegree ≤ (v : ℚ) := by
    have hh := sum_affineDegree_mul_pow_retainedMinimalPrimes_span_singleton_le hg s hv 1
    simpa [T₀] using hh
  apply card_le_of_agreement_off_excluded_sharp_of_iteratedRetainedCutFamily
    hprime hdim s (h := 1) (by decide) (highCuts := [])
    (by simp) hpot cuts hdeg hb hmA (∅ : Set (σ → F)) ?_ S ?_ hA
  · intro P hP Q hPQ hQ hsQ _ hdQ hmQ
    letI := hQ
    have hlt : {i | cuts i ∈ Q}.ncard < m := by
      apply ncard_cuts_lt_of_finite hsQ cuts hdQ
      intro T hT
      apply (hfinite T hT).subset
      intro x hx
      exact ⟨hx.1 _ (hPQ (hgP P hP)), hx.2⟩
    omega
  · intro x hx
    have hxg : x ∈ zeroLocus F (Ideal.span {g}) :=
      mem_zeroLocus_iff_le_ker_aeval.mpr
        ((Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr (hS x hx).1))
    obtain ⟨P,hP,hxP⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus _ s x hxg (hS x hx).2
    exact ⟨⟨P,hP,hxP⟩,(hS x hx).2,by simp,Set.notMem_empty x⟩

end
end Astra7
end PackSource_FiniteFiberIncidence

section PackSource_PowerCover
set_option autoImplicit true
namespace Astra7
open MvPolynomial
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 4000

variable {F σ : Type*} [Field F]

def powerPoint (w : σ → ℕ) (theta : σ → F) (x : σ → F) : σ → F :=
  fun i => x i ^ w i + theta i

def powerSubst (w : σ → ℕ) (theta : σ → F) :
    MvPolynomial σ F →ₐ[F] MvPolynomial σ F :=
  aeval (fun i => X i ^ w i + C (theta i))

theorem eval_powerSubst (w : σ → ℕ) (theta x : σ → F) (Q : MvPolynomial σ F) :
    aeval x (powerSubst w theta Q) = aeval (powerPoint w theta x) Q := by
  rw [powerSubst, comp_aeval_apply]
  simp
  rfl

theorem degree_powerSubst (w : σ → ℕ) (theta : σ → F) (Q : MvPolynomial σ F) :
    (powerSubst w theta Q).totalDegree ≤ Q.weightedTotalDegree w := by
  rw [← weightedTotalDegree_one]
  apply weightedTotalDegree_aeval_le_of_le w (fun _ => 1)
  intro i
  change weightedTotalDegree (1 : σ → ℕ) (X i ^ w i + C (theta i)) ≤ w i
  rw [weightedTotalDegree_one]
  exact (totalDegree_add _ _).trans (by simp [totalDegree_X_pow])

theorem powerPoint_surjective [IsAlgClosed F] (w : σ → ℕ) (theta : σ → F)
    (hw : ∀ i, 0 < w i) : Function.Surjective (powerPoint w theta) := by
  intro y
  choose x hx using fun i => IsAlgClosed.exists_pow_nat_eq (y i-theta i) (hw i)
  refine ⟨x,funext fun i => ?_⟩
  simp [powerPoint,hx]

theorem powerSubst_injective [IsAlgClosed F] (w : σ → ℕ) (theta : σ → F)
    (hw : ∀ i, 0 < w i) : Function.Injective (powerSubst w theta) := by
  intro P Q h
  apply MvPolynomial.funext
  intro y
  obtain ⟨x,rfl⟩ := powerPoint_surjective w theta hw y
  simpa only [← aeval_eq_eval, ← eval_powerSubst] using congrArg (aeval x) h

def rootFinset (n : ℕ) (c : F) : Finset F := by
  classical
  exact (Polynomial.X^n-Polynomial.C c).roots.toFinset

theorem mem_rootFinset (n : ℕ) (hn : 0 < n) (c x : F) :
    x ∈ rootFinset n c ↔ x^n=c := by
  classical
  simp [rootFinset, Polynomial.mem_roots (Polynomial.X_pow_sub_C_ne_zero hn c),
    Polynomial.IsRoot, sub_eq_zero]

theorem card_rootFinset [IsAlgClosed F] (n : ℕ) (c : F)
    (hn : (n : F) ≠ 0) (hc : c ≠ 0) : (rootFinset n c).card = n := by
  classical
  unfold rootFinset
  rw [Multiset.toFinset_card_of_nodup
    (Polynomial.nodup_roots (Polynomial.separable_X_pow_sub_C c hn hc)),
    ← (IsAlgClosed.splits (Polynomial.X^n-Polynomial.C c : Polynomial F)).natDegree_eq_card_roots,
    Polynomial.natDegree_X_pow_sub_C]

section Finite
variable [Fintype σ]

def powerFiber (w : σ → ℕ) (theta y : σ → F) : Finset (σ → F) := by
  classical
  exact Fintype.piFinset (fun i => rootFinset (w i) (y i-theta i))

theorem mem_powerFiber (w : σ → ℕ) (theta y x : σ → F) (hw : ∀ i, 0 < w i) :
    x ∈ powerFiber w theta y ↔ powerPoint w theta x=y := by
  classical
  simp only [powerFiber,Fintype.mem_piFinset,mem_rootFinset _ (hw _),powerPoint,funext_iff]
  exact forall_congr' fun i => eq_sub_iff_add_eq

theorem card_powerFiber [IsAlgClosed F] (w : σ → ℕ) (theta y : σ → F)
    (hw : ∀ i, (w i : F) ≠ 0) (hy : ∀ i, y i ≠ theta i) :
    (powerFiber w theta y).card = ∏ i, w i := by
  classical
  simp only [powerFiber,Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro i _
  exact card_rootFinset (w i) _ (hw i) (sub_ne_zero.mpr (hy i))

theorem finite_powerPoint_preimage (w : σ → ℕ) (theta : σ → F)
    (hw : ∀ i, 0 < w i) {T : Set (σ → F)} (hT : T.Finite) :
    ((powerPoint w theta) ⁻¹' T).Finite := by
  classical
  have heq : (powerPoint w theta) ⁻¹' T =
      ⋃ y ∈ T, ((powerFiber w theta y : Finset (σ → F)) : Set (σ → F)) := by
    ext x
    simp only [Set.mem_preimage,Set.mem_iUnion,Finset.mem_coe,mem_powerFiber _ _ _ _ hw]
    exact ⟨fun hx => ⟨_,hx,rfl⟩,fun ⟨y,hy,hxy⟩ => hxy ▸ hy⟩
  rw [heq]
  exact hT.biUnion (fun y _ => (powerFiber w theta y).finite_toSet)

def liftFinset (w : σ → ℕ) (theta : σ → F) (T : Finset (σ → F)) : Finset (σ → F) := by
  classical
  exact T.biUnion (powerFiber w theta)

theorem mem_liftFinset (w : σ → ℕ) (theta x : σ → F) (T : Finset (σ → F))
    (hw : ∀ i, 0 < w i) :
    x ∈ liftFinset w theta T ↔ powerPoint w theta x ∈ T := by
  classical
  simp only [liftFinset, Finset.mem_biUnion,mem_powerFiber _ _ _ _ hw]
  exact ⟨fun ⟨y,hy,hxy⟩ => hxy ▸ hy,fun hx => ⟨_,hx,rfl⟩⟩

theorem card_liftFinset [IsAlgClosed F] (w : σ → ℕ) (theta : σ → F)
    (T : Finset (σ → F)) (hw : ∀ i, 0 < w i)
    (hchar : ∀ i, (w i : F) ≠ 0) (havoid : ∀ y ∈ T, ∀ i, y i ≠ theta i) :
    (liftFinset w theta T).card = T.card * ∏ i, w i := by
  classical
  rw [liftFinset,Finset.card_biUnion]
  · calc
      ∑ y ∈ T, (powerFiber w theta y).card = ∑ _y ∈ T, ∏ i, w i := by
        apply Finset.sum_congr rfl
        intro y hy
        exact card_powerFiber w theta y hchar (havoid y hy)
      _ = _ := by simp
  · intro y hy z hz hne
    apply Finset.disjoint_left.mpr
    intro x hxy hxz
    apply hne
    exact (mem_powerFiber w theta y x hw).mp hxy |>.symm.trans
      ((mem_powerFiber w theta z x hw).mp hxz)

theorem exists_avoiding_shift [Infinite F] (T : Finset (σ → F)) :
    ∃ theta : σ → F, ∀ y ∈ T, ∀ i, y i ≠ theta i := by
  classical
  choose theta ht using fun i : σ => (T.image (fun y => y i)).exists_notMem
  refine ⟨theta,fun y hy i heq => ht i ?_⟩
  exact Finset.mem_image.mpr ⟨y,hy,heq⟩

end Finite
end
end Astra7
end PackSource_PowerCover

section PackSource_C58WeightedResultant
set_option autoImplicit true
/-! Actual weighted remaining-variable degree bounds for Sylvester resultants.
No irreducibility, root coverage, list count, or MCA theorem is asserted.
The injective grading lift adapts the private construction in pinned ArkLib's
Data/MvPolynomial/WeightedDegree/Products.lean; the determinant bound itself is
the existing pinned ResultantDegree theorem transported along this ring map.
-/
namespace Sol1.C58
open Polynomial

noncomputable section
variable {σ R : Type*} [CommRing R]

def exponentLift (w : σ → ℕ) : (σ →₀ ℕ) →+ (Option σ →₀ ℕ) where
  toFun d := d.optionElim (Finsupp.weight w d)
  map_zero' := by ext i; cases i <;> simp
  map_add' d e := by ext i; cases i <;> simp

theorem exponentLift_injective (w : σ → ℕ) : Function.Injective (exponentLift w) := by
  intro d e h
  have := congrArg Finsupp.some h
  simpa [exponentLift] using this

def weightedLift (w : σ → ℕ) :
    MvPolynomial σ R →+* MvPolynomial (Option σ) R :=
  AddMonoidAlgebra.mapDomainRingHom R (exponentLift w)

theorem degreeOf_weightedLift (w : σ → ℕ) (p : MvPolynomial σ R) :
    (weightedLift w p).degreeOf none = p.weightedTotalDegree w := by
  classical
  have hs : (weightedLift w p).support = p.support.image (exponentLift w) :=
    Finsupp.mapDomain_support_of_injective (exponentLift_injective w) _
  rw [MvPolynomial.degreeOf_eq_sup, hs, Finset.sup_image]
  simp [Function.comp_def, exponentLift, MvPolynomial.weightedTotalDegree]

/-- Keep all original variables as coefficient labels and put their weight
in a new polynomial variable. Thus cancellation cannot lower this degree. -/
def degreeLift (w : σ → ℕ) : MvPolynomial σ R →+* Polynomial (MvPolynomial σ R) :=
  (MvPolynomial.optionEquivLeft R σ).toRingHom.comp (weightedLift w)

theorem natDegree_degreeLift (w : σ → ℕ) (p : MvPolynomial σ R) :
    (degreeLift w p).natDegree = p.weightedTotalDegree w := by
  change (MvPolynomial.optionEquivLeft R σ (weightedLift w p)).natDegree = _
  rw [MvPolynomial.natDegree_optionEquivLeft, degreeOf_weightedLift]

/-- Full weighted Sylvester index-sum bound, including zero weights. -/
theorem weighted_resultant_add_mul_le_of_coeff_add_le
    (w : σ → ℕ) (f g : Polynomial (MvPolynomial σ R)) (m n dF dG : ℕ)
    (hf : ∀ i ≤ m, i + (f.coeff i).weightedTotalDegree w ≤ dF)
    (hg : ∀ i ≤ n, i + (g.coeff i).weightedTotalDegree w ≤ dG) :
    (Polynomial.resultant f g m n).weightedTotalDegree w + m*n ≤ n*dF+m*dG := by
  let phi := degreeLift (R := R) w
  have hf' : ∀ i ≤ m, i + ((f.map phi).coeff i).natDegree ≤ dF := by
    intro i hi
    simpa only [Polynomial.coeff_map, phi, natDegree_degreeLift] using hf i hi
  have hg' : ∀ i ≤ n, i + ((g.map phi).coeff i).natDegree ≤ dG := by
    intro i hi
    simpa only [Polynomial.coeff_map, phi, natDegree_degreeLift] using hg i hi
  have h := Polynomial.natDegree_resultant_add_mul_le_of_coeff_add_le
    (f.map phi) (g.map phi) m n dF dG hf' hg'
  rw [Polynomial.resultant_map_map, natDegree_degreeLift] at h
  exact h

/-- The actual multivariate weighted derivative-resultant bound. -/
theorem weighted_derivative_resultant_add_sq_le
    (w : σ → ℕ) (f : Polynomial (MvPolynomial σ R)) (b nu : ℕ)
    (hf : ∀ i ≤ b, i + (f.coeff i).weightedTotalDegree w ≤ nu) :
    (Polynomial.resultant f f.derivative b (b-1)).weightedTotalDegree w + b^2 ≤
      (2*b-1)*nu := by
  let phi := degreeLift (R := R) w
  have hf' : ∀ i ≤ b, i + ((f.map phi).coeff i).natDegree ≤ nu := by
    intro i hi
    simpa only [Polynomial.coeff_map, phi, natDegree_degreeLift] using hf i hi
  have h := Polynomial.natDegree_resultant_derivative_padded_add_sq_le (f.map phi) b nu hf'
  rw [Polynomial.derivative_map, Polynomial.resultant_map_map, natDegree_degreeLift] at h
  exact h

/-- Uniform nu(nu-1) envelope used by the C40 lower-order consumer. -/
theorem weighted_derivative_resultant_le
    (w : σ → ℕ) (f : Polynomial (MvPolynomial σ R)) (b nu : ℕ)
    (hf : ∀ i ≤ b, i + (f.coeff i).weightedTotalDegree w ≤ nu) :
    (Polynomial.resultant f f.derivative b (b-1)).weightedTotalDegree w ≤ nu*(nu-1) := by
  have h := weighted_derivative_resultant_add_sq_le w f b nu hf
  have hb : b ≤ nu := (Nat.le_add_right b _).trans (hf b le_rfl)
  obtain ⟨c,rfl⟩ := Nat.exists_eq_add_of_le hb
  cases b with
  | zero =>
    have hz : (Polynomial.resultant f f.derivative 0 (0-1)).weightedTotalDegree w ≤ 0 := by
      simpa using h
    exact hz.trans (Nat.zero_le _)
  | succ b =>
    have h1 : 2*(b+1)-1=2*b+1 := by omega
    have h2 : b+1+c-1=b+c := by omega
    simp only [h1, h2] at h ⊢
    nlinarith [Nat.zero_le (c*c)]

end
end Sol1.C58
end PackSource_C58WeightedResultant

section PackSource_AdaptiveRootCount
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace FrobeniusLocator.Strata
noncomputable section
open Finset MvPolynomial
open scoped BigOperators
local instance agDecidable (P : Prop) : Decidable P := Classical.propDecidable P
variable {F K ν : Type} [Field F] [Field K] [Algebra F K] [Finite ν]

/-- Concrete cofactor/root data needed by the adaptive locator induction.
A new deflated cofactor family may be chosen on EVERY child prime. The
properness condition excludes fixed roots; d is both the degree budget
and the number of active roots at each selected point. -/
def AdaptiveRootSupply (ι : Type) [Fintype ι]
    (I : Ideal (MvPolynomial ν F)) (Γ : Finset (ν → K)) : Prop :=
  ∀ (P : Ideal (MvPolynomial ν F)), I≤P → P.IsPrime →
    0<(affineHilbertPolynomial P).natDegree →
    ∀ S : Finset (ν → K), S⊆Γ → (∀ x∈S, x∈zeroLocus K P) → S.Nonempty →
    ∃ (d : ℕ) (cuts : ι → MvPolynomial ν F), 0<d ∧
      (∀ i, cuts i∉P ∧ (cuts i).totalDegree≤d) ∧
      ∀ x∈S, d≤{i | aeval x (cuts i)=0}.ncard

/-- Kernel-checked adaptive root pruning with the ACTUAL pinned ArkLib
proper-intersection and degree theorems. This does not assume Bezout as
an axiom. The unresolved input is the displayed matrix/cofactor root
supply, not a point-count bound in disguise. -/
theorem adaptive_root_count (ι : Type) [Fintype ι]
    (I : Ideal (MvPolynomial ν F)) (Γ : Finset (ν → K))
    (hsupply : AdaptiveRootSupply ι I Γ)
    {P : Ideal (MvPolynomial ν F)} [hP : P.IsPrime] (hIP : I≤P)
    (S : Finset (ν → K)) (hSΓ : S⊆Γ) (hS : ∀ x∈S, x∈zeroLocus K P) :
    (S.card : ℚ)≤affineDegree P*(Fintype.card ι : ℚ)^(affineHilbertPolynomial P).natDegree := by
  classical
  obtain ⟨dim,hdim⟩ : ∃ d, (affineHilbertPolynomial P).natDegree=d := ⟨_,rfl⟩
  rw [hdim]
  induction dim using Nat.strong_induction_on generalizing P S with
  | _ dim ih =>
    rcases S.eq_empty_or_nonempty with rfl | hSne
    · exact mul_nonneg (affineDegree_nonneg P) (pow_nonneg (Nat.cast_nonneg _) _)
    rcases dim with _ | e
    · have hfin := finite_zeroLocus_and_ncard_le_affineDegree (K := K) P hdim
      have hcard : (S.card : ℚ)≤(zeroLocus K P).ncard := by
        have hh := Set.ncard_le_ncard (fun x (hx : x∈(S : Set (ν → K))) => hS x hx) hfin.1
        rw [Set.ncard_coe_finset] at hh
        exact_mod_cast hh
      simpa only [pow_zero,mul_one] using hcard.trans hfin.2
    obtain ⟨d,cuts,hd,hcuts,hroots⟩ := hsupply P hIP hP (by omega) S hSΓ hS hSne
    have hroots' (x : ν → K) (hx : x∈S) : d≤(Finset.univ.filter (fun i => aeval x (cuts i)=0)).card := by
      have heq : {i | aeval x (cuts i)=0}.ncard=(Finset.univ.filter (fun i => aeval x (cuts i)=0)).card := by
        rw [← Set.ncard_coe_finset]
        congr 1
        ext i
        simp
      rw [← heq]
      exact hroots x hx
    have hswap : (∑ x∈S, (Finset.univ.filter (fun i => aeval x (cuts i)=0)).card)=
        ∑ i : ι, (S.filter (fun x => aeval x (cuts i)=0)).card := by
      simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
      exact Finset.sum_comm
    have hlowNat : S.card*d≤∑ i : ι, (S.filter (fun x => aeval x (cuts i)=0)).card := by
      rw [← hswap]
      calc
        _ = ∑ _x∈S, d := by simp
        _ ≤ _ := Finset.sum_le_sum hroots'
    have hcut (i : ι) : ((S.filter (fun x => aeval x (cuts i)=0)).card : ℚ)≤
        (d : ℚ)*affineDegree P*(Fintype.card ι : ℚ)^e := by
      have hh := ncard_inter_cut_le_of_retained_le (K := K) (1 : MvPolynomial ν F)
        (hcuts i).1 (hcuts i).2 S (fun x hx => ⟨hS x hx,by simp⟩)
        (pow_nonneg (Nat.cast_nonneg (Fintype.card ι)) e) (fun Q hQ => ?_)
      · have heq : ((S : Set (ν → K)) ∩ {x | aeval x (cuts i)=0}).ncard=
            (S.filter (fun x => aeval x (cuts i)=0)).card := by
          rw [← Set.ncard_coe_finset,Finset.coe_filter]
          rfl
        simpa only [heq] using hh
      · have hmin := (Ideal.mem_retainedMinimalPrimes.mp hQ).1
        letI : Q.IsPrime := hmin.isPrime
        have hPQ : P≤Q := le_sup_left.trans hmin.le
        have hQdim : (affineHilbertPolynomial Q).natDegree=e := by
          have hpure := principalCut_natDegree_affineHilbertPolynomial_add_one (hcuts i).1 hmin
          omega
        have hind := ih e (by omega) (P := Q) (hIP.trans hPQ)
          (S.filter (fun x => x∈zeroLocus K Q))
          (fun x hx => hSΓ (Finset.mem_filter.mp hx).1)
          (fun x hx => (Finset.mem_filter.mp hx).2) hQdim
        have heq : ((S : Set (ν → K)) ∩ zeroLocus K Q).ncard=
            (S.filter (fun x => x∈zeroLocus K Q)).card := by
          rw [← Set.ncard_coe_finset,Finset.coe_filter]
          rfl
        simpa only [heq] using hind
    have hlow : (S.card : ℚ)*(d : ℚ)≤
        ∑ i : ι, ((S.filter (fun x => aeval x (cuts i)=0)).card : ℚ) := by
      exact_mod_cast hlowNat
    have hhigh : (∑ i : ι, ((S.filter (fun x => aeval x (cuts i)=0)).card : ℚ))≤
        (Fintype.card ι : ℚ)*((d : ℚ)*affineDegree P*(Fintype.card ι : ℚ)^e) := by
      exact (Finset.sum_le_sum (fun i _ => hcut i)).trans_eq (by simp)
    apply le_of_mul_le_mul_right (a := (d : ℚ)) (show _ from ?_) (by exact_mod_cast hd)
    calc
      (S.card : ℚ)*(d : ℚ) ≤ (Fintype.card ι : ℚ)*((d : ℚ)*affineDegree P*(Fintype.card ι : ℚ)^e) := hlow.trans hhigh
      _ = (affineDegree P*(Fintype.card ι : ℚ)^(e+1))*(d : ℚ) := by rw [pow_succ]; ring

end
end FrobeniusLocator.Strata
end PackSource_AdaptiveRootCount

section PackSource_RankLocusCover
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Finset MvPolynomial
open scoped BigOperators
variable {F K ν : Type} [Field F] [Field K] [Algebra F K] [Finite ν]
local instance coverDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- Cutting by a finite family of degree<=n equations preserves the
n^dimension degree potential. The actual ArkLib component cover and
proper hypersurface bounds are used; only adaptive locator-root supply
remains to be constructed by the matrix algebra. -/
theorem polynomial_locus_count_of_adaptive_roots (ι : Type) [Fintype ι]
    (cuts : List (MvPolynomial ν F)) (hdeg : ∀ f∈cuts, f.totalDegree≤Fintype.card ι)
    (Γ : Finset (ν → K)) (hzero : ∀ x∈Γ, ∀ f∈cuts, aeval x f=0)
    (hsupply : AdaptiveRootSupply ι (Ideal.span {f | f∈cuts}) Γ) :
    (Γ.card : ℚ)≤(Fintype.card ι : ℚ)^Nat.card ν := by
  classical
  let Ps : Finset (Ideal (MvPolynomial ν F)) := {⊥}
  let T := Ideal.iteratedRetainedCutFamily Ps (1 : MvPolynomial ν F) cuts
  have hprime : ∀ P∈Ps, P.IsPrime := by
    intro P hP
    have heq : P=⊥ := by simpa only [Ps,Finset.mem_singleton] using hP
    subst P
    infer_instance
  have hcover : ∀ x∈Γ, ∃ Q∈T, x∈zeroLocus K Q := by
    intro x hx
    obtain ⟨Q,hQ,_,hxQ⟩ := exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus
      (Ps := Ps) (P := ⊥) (by simp [Ps]) (s := (1 : MvPolynomial ν F)) (cuts := cuts)
      (x := x) (by simp) (by simp) (hzero x hx)
    exact ⟨Q,hQ,hxQ⟩
  have hbound : ∀ Q∈T, (((Γ : Set (ν → K)) ∩ zeroLocus K Q).ncard : ℚ)≤
      affineDegree Q*(Fintype.card ι : ℚ)^(affineHilbertPolynomial Q).natDegree := by
    intro Q hQ
    letI : Q.IsPrime := Ideal.isPrime_of_mem_iteratedRetainedCutFamily hprime _ _ hQ
    obtain ⟨_,_,_,hcuts⟩ := Ideal.exists_le_of_mem_iteratedRetainedCutFamily hQ
    have hIQ : Ideal.span {f | f∈cuts}≤Q := Ideal.span_le.mpr (fun f hf => hcuts f hf)
    have hh := adaptive_root_count ι (Ideal.span {f | f∈cuts}) Γ hsupply hIQ
      (Γ.filter (fun x => x∈zeroLocus K Q)) (Finset.filter_subset _ _)
      (fun x hx => (Finset.mem_filter.mp hx).2)
    have heq : ((Γ : Set (ν → K)) ∩ zeroLocus K Q).ncard=
        (Γ.filter (fun x => x∈zeroLocus K Q)).card := by
      rw [← Set.ncard_coe_finset,Finset.coe_filter]
      rfl
    simpa only [heq] using hh
  have hcount := card_le_sum_of_forall_mem_zeroLocus T
    (fun Q => affineDegree Q*(Fintype.card ι : ℚ)^(affineHilbertPolynomial Q).natDegree) Γ hcover hbound
  have hpotential := sum_affineDegree_mul_pow_iteratedRetainedCutFamily_le hprime
    (1 : MvPolynomial ν F) hdeg
  have hstart : (∑ P∈Ps, affineDegree P*(Fintype.card ι : ℚ)^(affineHilbertPolynomial P).natDegree)=
      (Fintype.card ι : ℚ)^Nat.card ν := by
    simp only [Ps,Finset.sum_singleton,affineDegree_bot,natDegree_affineHilbertPolynomial_bot,one_mul]
  rw [hstart] at hpotential
  exact hcount.trans hpotential

/-- The cubic independent-parameter regular-locus price, with the exact
remaining matrix/cofactor root-supply obligation exposed. -/
theorem three_parameter_locus_count_of_adaptive_roots (ι : Type) [Fintype ι]
    (cuts : List (MvPolynomial (Fin 3) F)) (hdeg : ∀ f∈cuts, f.totalDegree≤Fintype.card ι)
    (Γ : Finset (Fin 3 → K)) (hzero : ∀ x∈Γ, ∀ f∈cuts, aeval x f=0)
    (hsupply : AdaptiveRootSupply ι (Ideal.span {f | f∈cuts}) Γ) :
    Γ.card≤Fintype.card ι^3 := by
  have hh := polynomial_locus_count_of_adaptive_roots ι cuts hdeg Γ hzero hsupply
  simp only [Nat.card_eq_fintype_card,Fintype.card_fin] at hh
  exact_mod_cast hh

end
end FrobeniusLocator.Strata
end PackSource_RankLocusCover

section PackSource_C42TranslationRank
set_option autoImplicit true
/-! Uniform point-rank transport on the ACTUAL C42 source span.
This does not prove the numerical origin rank bound. -/
namespace Sol1.C42

noncomputable section
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
variable {F : Type*} [Field F]

def sourceOrderWeight : JetVariable 2 → ℕ
  | none => 0
  | some j => j.val

def sourceSpan (F : Type*) [Field F] : Submodule F (DifferentialPolynomial F 2) :=
  Submodule.span F (Set.range fun i : SourceIndex ↦ (columns i).polynomial)

def sourceBand (F : Type*) [Field F] : Submodule F (DifferentialPolynomial F 2) :=
  restrictWeightAtMost (R := F) (differentialWeight 131072) 8652719 ⊓
    (restrictWeightAtMost (R := F) jetDegreeWeight 64 ⊓
      restrictWeightAtMost (R := F) sourceOrderWeight 21)

theorem column_mem_band (i : SourceIndex) : (columns i).polynomial ∈ sourceBand F := by
  classical
  have hs : ∀ u ∈ ((columns i).polynomial : DifferentialPolynomial F 2).support,
      u = (columns i).exponent := by
    intro u hu
    exact Finset.mem_singleton.mp (support_monomial_subset hu)
  refine ⟨?_,?_,?_⟩
  · apply mem_restrictWeightAtMost.mpr
    intro u hu
    rw [hs u hu]
    have h := columns_weight_lt i
    omega
  · apply mem_restrictWeightAtMost.mpr
    intro u hu
    rw [hs u hu]
    exact columns_total_le i
  · apply mem_restrictWeightAtMost.mpr
    intro u hu
    rw [hs u hu]
    simpa [SourceColumn.weight_exponent, columns, sourceOrderWeight, Fin.sum_univ_two,
      Nat.mul_comm] using jet_order i.1

theorem sourceSpan_le_band : sourceSpan F ≤ sourceBand F := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact column_mem_band i

theorem mem_sourceSpan_of_band (Q : DifferentialPolynomial F 2) (hQ : Q ∈ sourceBand F) :
    Q ∈ sourceSpan F := by
  classical
  rw [Q.as_sum]
  apply Submodule.sum_mem
  intro u hu
  let c := SourceColumn.ofExponent u
  have he : c.exponent = u := SourceColumn.exponent_ofExponent u
  have hr := mem_restrictWeightAtMost.mp hQ.1 u hu
  have ht := mem_restrictWeightAtMost.mp hQ.2.1 u hu
  have ho := mem_restrictWeightAtMost.mp hQ.2.2 u hu
  rw [← he] at hr ht ho
  have heligible : Eligible c.x c.y₀ (c.higher 0) (c.higher 1) := by
    simp [SourceColumn.weight_exponent, differentialWeight, jetDegreeWeight,
      sourceOrderWeight, Fin.sum_univ_succ, Nat.mul_comm] at hr ht ho
    unfold Eligible
    omega
  obtain ⟨i,hi⟩ := index_of_eligible c.x c.y₀ (c.higher 0) (c.higher 1) heligible
  have hc : ({x := c.x, y₀ := c.y₀, higher := ![c.higher 0,c.higher 1]} : SourceColumn 2) = c := by
    apply SourceColumn.exponent_injective
    ext v
    rcases v with _ | j
    · simp
    · fin_cases j <;> simp [SourceColumn.exponent, Fin.sum_univ_two]
  have hexp : (columns i).exponent = u := by rw [hi, hc]; exact he
  have hgen : ((columns i).polynomial : DifferentialPolynomial F 2) ∈ sourceSpan F :=
    Submodule.subset_span ⟨i,rfl⟩
  have hmono : monomial u (Q.coeff u) = Q.coeff u • (columns i).polynomial := by
    simp [SourceColumn.polynomial, hexp, smul_monomial, smul_eq_mul]
  rw [hmono]
  exact (sourceSpan F).smul_mem _ hgen

/-- Point translation genuinely preserves the full finite source span. -/
theorem sourceSpan_translation (center received : F) (Q : DifferentialPolynomial F 2)
    (hQ : Q ∈ sourceSpan F) : globalPointTranslation center received Q ∈ sourceSpan F := by
  apply mem_sourceSpan_of_band
  have hb := sourceSpan_le_band hQ
  refine ⟨?_,?_,?_⟩
  · exact globalPointTranslation_mem_restrictWeightAtMost (by exact Nat.zero_le _)
      (by exact Nat.zero_le _) center received hb.1
  · exact globalPointTranslation_mem_restrictWeightAtMost (by exact Nat.zero_le _)
      (by exact Nat.zero_le _) center received hb.2.1
  · exact globalPointTranslation_mem_restrictWeightAtMost (by exact Nat.zero_le _)
      (by exact Nat.zero_le _) center received hb.2.2

def pointMatrix (m : ℕ) (center received : F) : Matrix (LowContactIndex 2 m) SourceIndex F :=
  fun row i ↦ localConstraintCoordinatesAt m center received (columns i).polynomial row

theorem coordinates_translation (m : ℕ) (center received : F) (Q : DifferentialPolynomial F 2) :
    localConstraintCoordinatesAt m center received Q =
      localConstraintCoordinatesAt m 0 0 (globalPointTranslation center received Q) := by
  have he : unscaledLocalSubstitution 2 0 0 (globalPointTranslation center received Q) =
      unscaledLocalSubstitution 2 center received Q := by
    change ((unscaledLocalSubstitution 2 0 0).comp (globalPointTranslation center received)) Q = _
    rw [unscaledLocalSubstitution_comp_globalPointTranslation]
    simp
  ext row
  change (unscaledLocalSubstitution 2 center received Q).coeff row.val =
    (unscaledLocalSubstitution 2 0 0 (globalPointTranslation center received Q)).coeff row.val
  rw [he]

/-- Local rank at arbitrary center/value is at most the origin rank, with
the actual source family and coefficient maps, over every coefficient field. -/
theorem point_rank_le_origin (m : ℕ) (center received : F) :
    (pointMatrix m center received).rank ≤ (pointMatrix (F := F) m 0 0).rank := by
  classical
  let L := localConstraintCoordinatesAt (R := F) (d := 2) m 0 0
  have hmap : (sourceSpan F).map L =
      Submodule.span F (Set.range (pointMatrix (F := F) m 0 0).col) := by
    rw [sourceSpan, Submodule.map_span, ← Set.range_comp]
    rfl
  have hspan : Submodule.span F (Set.range (pointMatrix m center received).col) ≤
      Submodule.span F (Set.range (pointMatrix (F := F) m 0 0).col) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    rw [← hmap]
    refine ⟨globalPointTranslation center received (columns i).polynomial,
      sourceSpan_translation center received _ (Submodule.subset_span ⟨i,rfl⟩), ?_⟩
    exact (coordinates_translation m center received (columns i).polynomial).symm
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  have := FiniteDimensional.span_of_finite (K := F)
    (Set.finite_range (pointMatrix (F := F) m 0 0).col)
  exact Submodule.finrank_mono hspan

end
end Sol1.C42
end PackSource_C42TranslationRank

section PackSource_C52FiniteOrigin
set_option autoImplicit true
namespace Sol1.C52
open scoped BigOperators
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open Sol1.C42
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev Block := Fin 65 × Fin 69
def balance (q : Block) : ℤ := (q.2.val : ℤ) - 21
abbrev ColFiber (q : Block) :=
  (e : Fin (min q.1.val 10 + 1)) ×
    {a : Fin (min (q.1.val - e.val) (21 - 2 * e.val) + 1) //
      0 ≤ balance q + a.val + 2 * e.val ∧ balance q + a.val + 2 * e.val < 48}
abbrev Col := (q : Block) × ColFiber q

abbrev RowFiber (q : Block) :=
  (b : Fin (q.1.val + 1)) × {f : Fin (q.1.val - b.val + 1) //
    (b.val : ℤ) ≤ balance q + q.1.val + f.val ∧
      balance q + q.1.val + f.val + 2 * b.val < 48}
abbrev Row := (q : Block) × RowFiber q

theorem colFiber_card (q : Block) : Fintype.card (ColFiber q) = columnCount q.1.val (balance q) := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_subtype]
  rw [← sourceBlockFiberCount_eq]
  unfold sourceBlockFiberCount
  let f : ℕ → ℕ := fun e ↦ (Finset.univ.filter fun a :
    Fin (min (q.1.val - e) (21 - 2 * e) + 1) ↦
      0 ≤ balance q + a.val + 2 * e ∧ balance q + a.val + 2 * e < 48).card
  change (∑ e : Fin (min q.1.val 10 + 1), f e.val) =
    ∑ e ∈ Finset.range (min q.1.val 10 + 1), f e
  exact Fin.sum_univ_eq_sum_range f _

theorem rowFiber_card (q : Block) : Fintype.card (RowFiber q) =
    rowCountEnvelope q.1.val (balance q) := by
  classical
  rw [Fintype.card_sigma]
  unfold rowCountEnvelope
  apply Finset.sum_congr rfl
  intro b _
  rw [Fintype.card_subtype]
  have hf : (Finset.univ.filter fun f : Fin (q.1.val - b.val + 1) ↦
      (b.val : ℤ) ≤ balance q + q.1.val + f.val ∧
        balance q + q.1.val + f.val + 2 * b.val < 48) =
      (Finset.univ.filter fun f : Fin (q.1.val - b.val + 1) ↦
        max 0 (-(balance q)) - q.1.val + b.val ≤ (f.val : ℤ) ∧
          (f.val : ℤ) ≤ 48 - balance q - q.1.val - 1 - 2 * b.val) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hb := b.isLt
    have hh := f.isLt
    omega
  rw [hf, fin_interval_card]
  have hb := b.isLt
  have hh : ((q.1.val - b.val + 1 : ℕ) : ℤ) - 1 = (q.1.val : ℤ) - b.val := by omega
  rw [hh]

def colOriginal (j : Col) : SourceIndex :=
  let jet : Jet := ⟨j.1.1, j.2.1, j.2.2.1⟩
  ⟨jet, ⟨(balance j.1 + j.2.2.1.val + 2 * j.2.1.val).toNat, by
    have hp := j.2.2.2
    have hw := width_lower jet
    omega⟩⟩

def rowExponent (i : Row) : LocalVariable 2 →₀ ℕ :=
  Finsupp.single (localT 2) (balance i.1 + i.1.1.val + i.2.2.1.val).toNat +
  Finsupp.single (localE 2) i.2.1.val +
  Finsupp.single (localY (0 : Fin 2)) (i.1.1.val - i.2.1.val - i.2.2.1.val) +
  Finsupp.single (localY (1 : Fin 2)) i.2.2.1.val

theorem rowExponent_contact (i : Row) : localContactOrder 2 (rowExponent i) < 48 := by
  have hp := i.2.2.2
  rw [localContactOrder_eq]
  simp [rowExponent, localT, localE, localAux, localY]
  omega

def rowOriginal (i : Row) : LowContactIndex 2 48 := ⟨rowExponent i, rowExponent_contact i⟩

theorem rowExponent_jet (i : Row) :
    (rowExponent i).weight (localJetDegreeWeight 2) = i.1.1.val := by
  have hb := i.2.1.isLt
  have hf := i.2.2.1.isLt
  simp only [rowExponent, map_add, Finsupp.weight_single, localJetDegreeWeight,
    localT, localE, localAux, localY, nsmul_eq_mul, Nat.cast_id, mul_zero, mul_one, zero_add]
  omega

theorem rowExponent_balance (i : Row) : (rowExponent i).weight localBalance = balance i.1 := by
  have hb := i.2.1.isLt
  have hf := i.2.2.1.isLt
  have hp := i.2.2.2
  simp only [rowExponent, map_add, Finsupp.weight_single, localBalance,
    localT, localE, localAux, localY, nsmul_eq_mul]
  omega

theorem row_jet_formula (u : LocalVariable 2 →₀ ℕ) :
    u.weight (localJetDegreeWeight 2) =
      u (localE 2) + u (localY (0 : Fin 2)) + u (localY (1 : Fin 2)) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_two,
    localJetDegreeWeight, localE, localAux, localY, Nat.add_assoc]

theorem row_balance_formula (u : LocalVariable 2 →₀ ℕ) :
    u.weight localBalance = (u (localT 2) : ℤ) - u (localE 2) -
      u (localY (0 : Fin 2)) - 2 * u (localY (1 : Fin 2)) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_two,
    localBalance, localT, localE, localAux, localY]
  ring

theorem colOriginal_grade (j : Col) : (colOriginal j).1.1 = j.1.1 := rfl

theorem colOriginal_balance (j : Col) :
    ((colOriginal j).2.val : ℤ) - e1 (colOriginal j).1 - 2 * e2 (colOriginal j).1 =
      balance j.1 := by
  have hp := j.2.2.2
  simp only [colOriginal, e1, e2]
  omega

theorem low_column_represented (i : SourceIndex) (hx : i.2.val < 48) :
    ∃ j : Col, colOriginal j = i := by
  rcases i with ⟨⟨s,e,a⟩,x⟩
  change x.val < 48 at hx
  have ho := jet_order (⟨s,e,a⟩ : Jet)
  simp only [e1, e2] at ho
  let gi : Fin 69 := ⟨((x.val : ℤ) - a.val - 2 * e.val + 21).toNat, by omega⟩
  let q : Block := ⟨s,gi⟩
  have hgi : balance q = (x.val : ℤ) - a.val - 2 * e.val := by
    dsimp [balance,q,gi]
    omega
  let j : Col := ⟨q,e,⟨a,by rw [hgi]; omega⟩⟩
  refine ⟨j, ?_⟩
  dsimp only [colOriginal, j, q]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  apply Fin.ext
  change (balance q + a.val + 2 * e.val).toNat = x.val
  rw [hgi]
  omega

variable {F : Type*} [Field F]

theorem point_entry_constraint (r : LowContactIndex 2 48) (j : SourceIndex) :
    pointMatrix (F := F) 48 0 0 r j =
      (localConstraintAt 48 0 0 (columns j).polynomial).coeff r.val := by
  change (unscaledLocalSubstitution 2 (0 : F) 0 (columns j).polynomial).coeff r.val = _
  simp only [localConstraintAt, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    coeff_projectLowContact, ite_eq_left r.property]

theorem high_column_zero (j : SourceIndex) (hx : 48 ≤ j.2.val) :
    (pointMatrix (F := F) 48 0 0).col j = 0 := by
  ext r
  rw [Matrix.col_apply, point_entry_constraint, origin_high_X_zero 48 j hx]
  simp

/-- Every actual nonzero coefficient has a representative in the finite envelope. -/
theorem nonzero_row_represented (r : LowContactIndex 2 48) (j : SourceIndex)
    (hne : pointMatrix (F := F) 48 0 0 r j ≠ 0) :
    ∃ i : Row, rowOriginal i = r := by
  have hx : j.2.val < 48 := by
    by_contra hh
    have hz := high_column_zero (F := F) j (by omega)
    exact hne (congrFun hz r)
  have hs : r.val.weight (localJetDegreeWeight 2) = j.1.1.val := by
    by_contra hh
    exact hne ((point_entry_constraint r j).trans
      (origin_coefficient_zero_of_jet_ne 48 j r.val hh))
  have hg : r.val.weight localBalance = (j.2.val : ℤ) - e1 j.1 - 2 * e2 j.1 := by
    by_contra hh
    exact hne ((point_entry_constraint r j).trans
      (origin_coefficient_zero_of_balance_ne 48 j r.val hh))
  have he : r.val (localE 2) ≤ r.val (localT 2) := by
    apply localE_le_localT_of_mem_support (0 : F) 0 (columns j).polynomial
    exact mem_support_iff.mpr hne
  have ht := r.property
  rw [localContactOrder_eq] at ht
  have hsj := row_jet_formula r.val
  have hgj := row_balance_formula r.val
  have ho := jet_order j.1
  let gi : Fin 69 := ⟨((j.2.val : ℤ) - e1 j.1 - 2 * e2 j.1 + 21).toNat, by omega⟩
  let q : Block := ⟨j.1.1,gi⟩
  have hq : balance q = (j.2.val : ℤ) - e1 j.1 - 2 * e2 j.1 := by
    dsimp [balance,q,gi]
    omega
  let b : Fin (q.1.val + 1) := ⟨r.val (localE 2), by dsimp [q]; omega⟩
  let f : Fin (q.1.val - b.val + 1) := ⟨r.val (localY (1 : Fin 2)), by dsimp [q,b]; omega⟩
  have hT : balance q + q.1.val + f.val = (r.val (localT 2) : ℤ) := by
    change balance q + j.1.1.val + (r.val (localY (1 : Fin 2)) : ℤ) = _
    rw [hq]
    omega
  let i : Row := ⟨q,b,⟨f,by rw [hT]; dsimp [b]; omega⟩⟩
  refine ⟨i, ?_⟩
  apply Subtype.ext
  ext v
  rcases v with _ | (_ | v)
  · change rowExponent i (localT 2) = r.val (localT 2)
    have heval : rowExponent i (localT 2) =
        (balance q + q.1.val + f.val).toNat := by
      simp [rowExponent, localT, localE, localAux, localY, i]
    rw [heval, hT]
    simp
  · change rowExponent i (localE 2) = r.val (localE 2)
    simp [rowExponent, localT, localE, localAux, localY, i,b]
  · fin_cases v
    · change rowExponent i (localY (0 : Fin 2)) = r.val (localY (0 : Fin 2))
      have heval : rowExponent i (localY (0 : Fin 2)) =
          j.1.1.val - r.val (localE 2) - r.val (localY (1 : Fin 2)) := by
        simp [rowExponent, localT, localE, localAux, localY, i,b,f,q]
      rw [heval]
      omega
    · change rowExponent i (localY (1 : Fin 2)) = r.val (localY (1 : Fin 2))
      simp [rowExponent, localT, localE, localAux, localY, i,b,f]

end
end Sol1.C52
end PackSource_C52FiniteOrigin

section PackSource_C52OriginRank
set_option autoImplicit true
namespace Sol1.C52
open scoped BigOperators Matrix
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open Sol1.C42
noncomputable section
variable {F : Type*} [Field F]
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def finiteMatrix : Matrix Row Col F :=
  (pointMatrix 48 (0 : F) 0).submatrix rowOriginal colOriginal

/-- Actual origin coefficients vanish between different s,g blocks. -/
theorem finiteMatrix_offblock (i : Row) (j : Col) (hne : i.1 ≠ j.1) :
    finiteMatrix (F := F) i j = 0 := by
  rw [finiteMatrix, Matrix.submatrix_apply, point_entry_constraint]
  by_cases hs : i.1.1 = j.1.1
  · apply origin_coefficient_zero_of_balance_ne
    dsimp only [rowOriginal]
    rw [rowExponent_balance, colOriginal_balance]
    intro hbalance
    apply hne
    apply Prod.ext hs
    apply Fin.ext
    unfold balance at hbalance
    omega
  · apply origin_coefficient_zero_of_jet_ne
    dsimp only [rowOriginal]
    rw [rowExponent_jet, colOriginal_grade]
    exact fun h ↦ hs (Fin.ext h)

/-- The finite semantic block matrix has the exact static C42 rank allowance. -/
theorem finiteMatrix_rank : (finiteMatrix (F := F)).rank ≤ blockUpper := by
  classical
  apply (rank_le_sum_min_dependent (finiteMatrix (F := F)) finiteMatrix_offblock).trans
  simp_rw [rowFiber_card, colFiber_card]
  rw [Fintype.sum_prod_type]
  change (∑ s : Fin 65, ∑ gi : Fin 69,
    min (rowCountEnvelope s.val ((gi.val : ℤ) - 21))
      (columnCount s.val ((gi.val : ℤ) - 21))) ≤ blockUpper
  simp_rw [min_comm]
  exact envelope_upper_eq_block.le

/-- Restrict the actual origin columns to X<48 without increasing the rank. -/
theorem origin_rank_le_low_columns :
    (pointMatrix (F := F) 48 0 0).rank ≤
      ((pointMatrix (F := F) 48 0 0).submatrix id colOriginal).rank := by
  apply rank_le_col_representatives
  intro j
  by_cases hx : j.2.val < 48
  · obtain ⟨c,hc⟩ := low_column_represented j hx
    exact Or.inr ⟨c,by rw [hc]⟩
  · exact Or.inl (high_column_zero j (by omega))

/-- Every nonzero low-column row is represented by the finite target envelope. -/
theorem low_columns_rank_le_finite :
    ((pointMatrix (F := F) 48 0 0).submatrix id colOriginal).rank ≤
      (finiteMatrix (F := F)).rank := by
  classical
  apply rank_le_row_representatives
  intro r
  by_cases hz : ((pointMatrix (F := F) 48 0 0).submatrix id colOriginal) r = 0
  · exact Or.inl hz
  · right
    obtain ⟨c,hc⟩ := Function.ne_iff.mp hz
    have hc' : pointMatrix (F := F) 48 0 0 r (colOriginal c) ≠ 0 := hc
    obtain ⟨i,hi⟩ := nonzero_row_represented r (colOriginal c) hc'
    refine ⟨i, ?_⟩
    exact congrArg (fun r : LowContactIndex 2 48 ↦
      ((pointMatrix (F := F) 48 0 0).submatrix id colOriginal) r) hi.symm

/-- Kernel-checked static origin rank, valid over every coefficient field. -/
theorem origin_rank : (pointMatrix (F := F) 48 0 0).rank ≤ blockUpper :=
  origin_rank_le_low_columns.trans (low_columns_rank_le_finite.trans finiteMatrix_rank)

end
end Sol1.C52
end PackSource_C52OriginRank
