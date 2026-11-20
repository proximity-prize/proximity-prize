import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertBidegree
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertCappedDegree
import ArkLib.ToMathlib.RingTheory.Nullstellensatz.AgreementIncidence
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.RingTheory.Depth.Rees
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.Radical
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Smooth.Field
import Mathlib.Tactic
set_option Elab.async false

section PackSource_C42ConsumerArithmetic
set_option autoImplicit true
/-! Exact native arithmetic for the WRITTEN C40 consumer.
These identities do not assert that the consumer inequality has been proved. -/
namespace Sol1.C42

def listCap : ℕ := 123935685281173519
def I1 : ℚ := 131072 / 49193
def I2 : ℚ := I1 * (131073 / 49194)
def b (v : ℕ) : ℕ := 1 + 2 * 131073 * (v - 1)
def firstOrderCharge (h : ℕ) : ℚ := I1 * h * b h + (h : ℚ) * (h - 1)
def secondOrderCharge (nu : ℕ) : ℚ := I2 * nu * (b nu : ℚ) ^ 2 + firstOrderCharge (nu ^ 2)

theorem consumer_exact : secondOrderCharge 64 =
    (49987402193335468270948352 : ℚ) / 403333407 := by
  norm_num [secondOrderCharge, firstOrderCharge, I2, I1, b]

theorem consumer_le_cap : secondOrderCharge 64 ≤ (listCap : ℚ) := by
  rw [consumer_exact]
  norm_num [listCap]

theorem cap_sub_one_lt_consumer : (listCap : ℚ) - 1 < secondOrderCharge 64 := by
  rw [consumer_exact]
  norm_num [listCap]

theorem listCap_lt_seven_n_cubed : listCap < 7 * 262144 ^ 3 := by norm_num [listCap]
theorem listCap_gap : listCap + 2165104285200369 = 7 * 262144 ^ 3 := by norm_num [listCap]
theorem characteristic_guard : max (131072 : ℕ) (64 ^ 2) < 2130706433 := by norm_num
theorem complete_local_X_blocks : (48 : ℕ) * 180265 - 131072 * 64 = 264112 := by norm_num
theorem complete_local_X_blocks_ge : (48 : ℕ) ≤ 48 * 180265 - 131072 * 64 := by norm_num
theorem radius_agreement_sum : (81879 : ℕ) + 180265 = 262144 := by norm_num

theorem integer_count_le_cap {M : ℕ} (h : (M : ℚ) ≤ secondOrderCharge 64) : M ≤ listCap := by
  exact_mod_cast h.trans consumer_le_cap


end Sol1.C42
end PackSource_C42ConsumerArithmetic

section PackSource_C42ScoreArithmetic
set_option autoImplicit true
/-! Exact integer score separation: at least6915 centibits and below6916.
This is radius arithmetic, not a protocol or list theorem. -/
namespace Sol1.C42
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem score_6915_integer : (180265 : ℕ) ^ 12800 ≤ 2 ^ 223485 := by decide +kernel
theorem score_not_6916_integer : (2 : ℕ) ^ 223484 < 180265 ^ 12800 := by decide +kernel

end Sol1.C42
end PackSource_C42ScoreArithmetic

section PackSource_K1_13_5_3Geometry
set_option autoImplicit true
namespace K1_13_5_3
noncomputable section

open MvPolynomial
open scoped BigOperators

theorem mem_capped {F : Type*} [Field F] (g : MvPolynomial (Fin 2) F) {j r : ℕ}
    (hj : g.totalDegree ≤ j) (hr : g.degreeOf 1 ≤ r) :
    g ∈ restrictCappedDegree (Fin 2) F 1 j r := by
  intro m hm
  exact ⟨(le_totalDegree hm).trans hj, (monomial_le_degreeOf 1 hm).trans hr⟩

/-- A proper capped-degree cut of a prime plane curve. -/
theorem capped_cut_card {F : Type*} [Field F] {b c j r : ℕ}
    (hb : 0 < b) (hc : 0 < c) {g : MvPolynomial (Fin 2) F}
    (hg0 : g ≠ 0) (hprime : (Ideal.span {g}).IsPrime)
    (hg : g ∈ restrictCappedDegree (Fin 2) F 1 j r)
    {q : MvPolynomial (Fin 2) F} (hq : q ∈ restrictCappedDegree (Fin 2) F 1 b c)
    (hproper : q ∉ Ideal.span {g}) (S : Finset (Fin 2 → F))
    (hS : ∀ x ∈ S, aeval x g = 0 ∧ aeval x q = 0) :
    S.card ≤ cappedDegreeMixedVolume j r b c := by
  classical
  let E := cappedDegreeExponents (Fin 2) 1 b c
  let φ := monomialMap F E
  let P := (Ideal.span {g}).comap φ
  have hq' : q ∈ restrictSupport F E := by simpa only [restrictCappedDegree, E] using hq
  let cut := monomialLift q hq'
  let T := S.image (monomialPoint E)
  have hφ : Function.Surjective φ := monomialMap_cappedDegreeExponents_surjective hb hc
  have hE := single_mem_cappedDegreeExponents (σ := Fin 2) (i := 1) hb hc
  have hcut_map : φ cut = q := monomialMap_monomialLift q hq'
  have : P.IsPrime := hprime.comap φ.toRingHom
  have hdim : (affineHilbertPolynomial P).natDegree = 1 := by
    have h := natDegree_affineHilbertPolynomial_comap_span_singleton_add_one_of_surjective
      φ hφ hg0 hprime.ne_top
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
    change (affineHilbertPolynomial P).natDegree + 1 = 2 at h
    omega
  have hcut : cut ∉ P := by
    change φ cut ∉ Ideal.span {g}
    rw [hcut_map]
    exact hproper
  have hT : ∀ z ∈ T, z ∈ zeroLocus F P ∧ aeval z cut = 0 := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    constructor
    · rw [monomialPoint_mem_zeroLocus_comap_iff hE]
      simpa [zeroLocus_span] using (hS x hx).1
    · rw [aeval_monomialPoint]
      change aeval x (φ cut) = 0
      rw [hcut_map]
      exact (hS x hx).2
  have h := ncard_inter_cut_le_of_retained_le (P := P) (1 : MvPolynomial E F) hcut
    (totalDegree_monomialLift_le_one q hq') T
    (fun z hz => ⟨(hT z hz).1, by simp⟩) (c := 1) zero_le_one (by
      intro Q hQ
      have hm := (Ideal.mem_retainedMinimalPrimes.mp hQ).1
      have hz := principalCut_natDegree_affineHilbertPolynomial_add_one hcut hm
      rw [hdim] at hz
      obtain ⟨hf, hbound⟩ := finite_zeroLocus_and_ncard_le_affineDegree (K := F) Q (by omega)
      rw [mul_one]
      have hcard := Set.ncard_le_ncard (s := (T : Set (E → F)) ∩ zeroLocus F Q)
        Set.inter_subset_right hf
      exact le_trans (by exact_mod_cast hcard) hbound)
  have hset : (T : Set (E → F)) ∩ {z | aeval z cut = 0} = T :=
    Set.inter_eq_left.mpr (fun z hz => (hT z hz).2)
  rw [hset, Set.ncard_coe_finset, Nat.cast_one, one_mul, mul_one] at h
  change ((S.image (monomialPoint E)).card : ℚ) ≤ affineDegree P at h
  rw [Finset.card_image_of_injective _ (monomialPoint_injective hE)] at h
  exact_mod_cast h.trans (affineDegree_comap_cappedDegree_span_singleton_le hb hc hg0 hg)

end
end K1_13_5_3
end PackSource_K1_13_5_3Geometry

section PackSource_K1_14_3R_3_2_4Jet
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace K1_14_3R_3_2_4

noncomputable section

open MvPolynomial

variable {k σ : Type} [Field k]

private abbrev Affine := MvPolynomial (Option σ) k
private abbrev A (J : Ideal (Affine (k := k) (σ := σ))) := Affine ⧸ J
private abbrev B (J : Ideal (Affine (k := k) (σ := σ))) := Polynomial (A J)
private abbrev R (k σ : Type) [Field k] := Polynomial (Affine (k := k) (σ := σ))

private def seedEval (J : Ideal (Affine (k := k) (σ := σ))) : Affine (k := k) (σ := σ) →+* B J :=
  MvPolynomial.eval₂Hom
    (Polynomial.C.comp ((Ideal.Quotient.mk J).comp MvPolynomial.C))
    (fun i : Option σ => Polynomial.monomial 1 (i.elim 1 (fun j => Ideal.Quotient.mk J (MvPolynomial.X (some j)))))

private def homogeneousEval (J : Ideal (Affine (k := k) (σ := σ))) : R k σ →+* B J :=
  Polynomial.eval₂RingHom (seedEval J) (Polynomial.C (Ideal.Quotient.mk J (MvPolynomial.X none)))

private theorem prod_polynomial_monomial {S : Type} [CommSemiring S] {ι : Type}
    (s : Finset ι) (d : ι → ℕ) (f : ι → S) :
    (∏ i ∈ s, Polynomial.monomial (d i) (f i)) =
      Polynomial.monomial (∑ i ∈ s, d i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, ih, Finset.sum_insert hi, Finset.prod_insert hi,
      Polynomial.monomial_mul_monomial]

private theorem homogeneousEval_monomial (J : Ideal (Affine (k := k) (σ := σ)))
    (s : σ →₀ ℕ) (n l : ℕ) (c : k) :
    homogeneousEval J (Polynomial.monomial n (MvPolynomial.monomial (s.optionElim l) c)) =
      Polynomial.monomial (l + s.degree)
        (Ideal.Quotient.mk J (MvPolynomial.monomial (s.optionElim n) c)) := by
  classical
  let π := Ideal.Quotient.mk J
  unfold homogeneousEval seedEval
  rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, MvPolynomial.eval₂Hom_monomial,
    Finsupp.prod_option_index _ _ (by simp) (fun _ _ _ => pow_add _ _ _),
    Finsupp.optionElim_apply_none, Finsupp.some_optionElim]
  simp only [Option.elim_none, Option.elim_some, RingHom.comp_apply, Polynomial.monomial_pow,
    one_mul, one_pow]
  rw [show Polynomial.C (π (MvPolynomial.C c)) = Polynomial.monomial 0 (π (MvPolynomial.C c))
    from (Polynomial.monomial_zero_left (a := π (MvPolynomial.C c))).symm]
  rw [show Polynomial.C (π (MvPolynomial.X none)) ^ n = Polynomial.monomial 0 (π (MvPolynomial.X none) ^ n) by
    simp [← Polynomial.monomial_zero_left, Polynomial.monomial_pow]]
  rw [Finsupp.prod]
  simp_rw [Polynomial.monomial_pow, one_mul]
  rw [prod_polynomial_monomial, ← Finsupp.degree_apply]
  simp only [Polynomial.monomial_mul_monomial, zero_add, add_zero]
  congr 1
  rw [MvPolynomial.monomial_eq, Finsupp.prod_option_index _ _ (by simp)
    (fun _ _ _ => pow_add _ _ _), Finsupp.optionElim_apply_none, Finsupp.some_optionElim,
    map_mul, map_mul, map_pow, map_finsuppProd]
  simp only [map_pow, mul_assoc, π, Finsupp.prod]
  ac_rfl

private theorem monomial_box (J : Ideal (Affine (k := k) (σ := σ)))
    (s : σ →₀ ℕ) (n a b : ℕ) (c : k) (hn : n ≤ a) (hs : s.degree ≤ b) :
    Ideal.Quotient.mk J (MvPolynomial.monomial (s.optionElim n) c) ∈
      quotientBidegreeLE J a b := by
  refine mem_quotientBidegreeLE.mpr ⟨_, ?_, rfl⟩
  change MvPolynomial.monomial (s.optionElim n) c ∈
    restrictSupport k (bidegreeExponents σ a b)
  apply (monomial_mem_restrictSupport k).mpr (Or.inl _)
  simpa only [mem_bidegreeExponents, Finsupp.optionElim_apply_none, Finsupp.some_optionElim]
    using And.intro hn hs

private theorem eval_coeff_mem_box (J : Ideal (Affine (k := k) (σ := σ)))
    (P : R k σ) {a : ℕ} (hP : P.natDegree ≤ a) (b : ℕ) :
    (homogeneousEval J P).coeff b ∈ quotientBidegreeLE J a b := by
  classical
  rw [← Polynomial.sum_monomial_eq P, Polynomial.sum, map_sum, Polynomial.finsetSum_coeff]
  apply Submodule.sum_mem
  intro n hn
  have hna : n ≤ a := (Polynomial.le_natDegree_of_mem_supp n hn).trans hP
  induction P.coeff n using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [← Finsupp.optionElim_some m, homogeneousEval_monomial, Polynomial.coeff_monomial]
    split_ifs with h
    · exact monomial_box J _ _ _ _ _ hna (by omega)
    · exact Submodule.zero_mem _
  | add p q hp hq =>
    rw [map_add, map_add, Polynomial.coeff_add]
    exact Submodule.add_mem _ hp hq

private theorem homogeneous_lift (J : Ideal (Affine (k := k) (σ := σ))) {a b : ℕ} {x : A J}
    (hx : x ∈ quotientBidegreeLE J a b) :
    ∃ P : R k σ, P.natDegree ≤ a ∧ homogeneousEval J P = Polynomial.monomial b x := by
  classical
  obtain ⟨p, hp, rfl⟩ := mem_quotientBidegreeLE.mp hx
  let P : R k σ := ∑ m ∈ p.support,
    Polynomial.monomial (m none) (MvPolynomial.monomial (m.some.optionElim (b - m.some.degree))
      (p.coeff m))
  refine ⟨P, ?_, ?_⟩
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    apply Finset.sum_eq_zero
    intro m hm
    rw [ite_eq_right (by have := (mem_restrictBidegree.mp hp m hm).1; omega)]
  · simp only [P, map_sum, homogeneousEval_monomial]
    calc
      _ = ∑ m ∈ p.support,
          Polynomial.monomial b (Ideal.Quotient.mk J (MvPolynomial.monomial m (p.coeff m))) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finsupp.optionElim_some,
          Nat.sub_add_cancel (mem_restrictBidegree.mp hp m hm).2]
      _ = Polynomial.monomial b (Ideal.Quotient.mk J p) := by
        rw [← map_sum, ← map_sum (Ideal.Quotient.mk J), ← MvPolynomial.as_sum]

/-- On the jet-degree boundary, multiplication by the leading jet coordinate is
injective eventually, uniformly in the seed cap and independently of the offset. -/
theorem jetBoundary [Finite σ] (J : Ideal (Affine (k := k) (σ := σ))) (t : k) :
    ∃ N : ℕ, ∀ a b : ℕ, N ≤ a → ∀ x : A J,
      x ∈ quotientBidegreeLE J (a + 1) b →
      Ideal.Quotient.mk J (MvPolynomial.X none - MvPolynomial.C t) * x ∈
        quotientBidegreeLE J (a + 1) b → x ∈ quotientBidegreeLE J a b := by
  let φ := homogeneousEval J
  let L := RingHom.ker φ
  let chain : ℕ →o Ideal (Affine (k := k) (σ := σ)) :=
    ⟨L.leadingCoeffNth, fun _ _ h => L.leadingCoeffNth_mono h⟩
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance chain
  refine ⟨N, ?_⟩
  intro a b ha x hx hgx
  obtain ⟨P, hP, hPx⟩ := homogeneous_lift J hx
  obtain ⟨Q, hQ, hQx⟩ := homogeneous_lift J hgx
  change φ P = _ at hPx
  change φ Q = _ at hQx
  let g : R k σ := Polynomial.X - Polynomial.C (MvPolynomial.C t)
  have hg : φ g = Polynomial.C (Ideal.Quotient.mk J (MvPolynomial.X none - MvPolynomial.C t)) := by
    simp [φ, homogeneousEval, seedEval, g, map_sub]
  let H := g * P - Q
  have hHL : H ∈ L := by
    change φ (g * P - Q) = 0
    rw [map_sub, map_mul, hg, hPx, hQx, Polynomial.C_mul_monomial, sub_self]
  have hHtop : H.coeff (a + 2) = P.coeff (a + 1) := by
    simp only [H, g, sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul,
      Polynomial.coeff_C_mul, Polynomial.coeff_eq_zero_of_natDegree_lt (show P.natDegree < a + 2 by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (show Q.natDegree < a + 2 by omega), mul_zero,
      sub_zero]
  have hH : H.natDegree ≤ a + 2 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    have hp := Polynomial.natDegree_le_iff_coeff_eq_zero.mp hP n (by omega)
    have hp' := Polynomial.natDegree_le_iff_coeff_eq_zero.mp hP (n + 1) (by omega)
    have hq := Polynomial.natDegree_le_iff_coeff_eq_zero.mp hQ (n + 1) (by omega)
    simp only [H, g, sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul,
      Polynomial.coeff_C_mul, hp, hp', hq, mul_zero, sub_zero]
  have hcoeff : P.coeff (a + 1) ∈ L.leadingCoeffNth (a + 2) := by
    rw [← hHtop]
    exact ⟨H, ⟨Polynomial.mem_degreeLE.mpr (Polynomial.degree_le_of_natDegree_le hH), hHL⟩, rfl⟩
  have heq : L.leadingCoeffNth (a + 1) = L.leadingCoeffNth (a + 2) :=
    (hN (a + 1) (by omega)).symm.trans (hN (a + 2) (by omega))
  rw [← heq] at hcoeff
  obtain ⟨D, ⟨hD, hDL⟩, hDP⟩ := hcoeff
  have hDle : D.degree ≤ (a + 1 : ℕ) := Polynomial.mem_degreeLE.mp hD
  change D.coeff (a + 1) = P.coeff (a + 1) at hDP
  have hD' := Polynomial.natDegree_le_of_degree_le hDle
  have hsmall : (P - D).natDegree ≤ a := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    by_cases he : n = a + 1
    · rw [he, Polynomial.coeff_sub, hDP, sub_self]
    · rw [Polynomial.coeff_sub,
        Polynomial.natDegree_le_iff_coeff_eq_zero.mp hP n (by omega),
        Polynomial.natDegree_le_iff_coeff_eq_zero.mp hD' n (by omega), sub_zero]
  have hm := eval_coeff_mem_box J (P - D) hsmall b
  change φ D = 0 at hDL
  change (φ (P - D)).coeff b ∈ _ at hm
  simpa only [map_sub, hPx, hDL, sub_zero, Polynomial.coeff_monomial_same] using hm

end
end K1_14_3R_3_2_4
end PackSource_K1_14_3R_3_2_4Jet

section PackSource_K1_13_7_5_3_3_2_2Parameters
set_option autoImplicit true
namespace K1_13_7_5_3_3_2_2

open Ideal IsLocalRing RingTheory.Sequence CategoryTheory Abelian
open scoped Pointwise

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- Use powers in the maximal ideal to avoid a finite set of associated primes
without any hypothesis on the residue field. -/
private theorem regular_add_mem {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (a : R) (J : Ideal R) (hJ : J ≤ maximalIdeal R)
    (h : ∀ P ∈ associatedPrimes R M, a ∈ P → ¬ J ≤ P) :
    ∃ b ∈ J, IsSMulRegular M (a + b) := by
  classical
  let A := {P ∈ associatedPrimes R M | a ∈ P}
  have hA : A.Finite := (associatedPrimes.finite R M).subset fun _ hP => hP.1
  have hav : ¬ ((J : Set R) ⊆ ⋃ P ∈ A, (P : Set R)) := by
    intro hall
    obtain ⟨P, hP, hJP⟩ :=
      (J.subset_union_prime_finite hA (f := id) ⊥ ⊥
        (fun P hP _ _ => (show IsAssociatedPrime P M from hP.1).isPrime)).mp hall
    exact h P hP.1 hP.2 hJP
  obtain ⟨b, hb, hbA⟩ := Set.not_subset.mp hav
  let bad (P : Ideal R) := {n : ℕ | a + b ^ (n + 1) ∈ P}
  have hbad (P : Ideal R) (hP : P ∈ associatedPrimes R M) : (bad P).Finite := by
    have hp : P.IsPrime := (show IsAssociatedPrime P M from hP).isPrime
    have hlt (i j : ℕ) (hi : i ∈ bad P) (hj : j ∈ bad P) (hij : i < j) : False := by
      have hpos : 0 < j - i := Nat.sub_pos_of_lt hij
      have he : j + 1 = (i + 1) + (j - i) := by omega
      have hd : b ^ (i + 1) * (1 - b ^ (j - i)) ∈ P := by
        rw [mul_sub, mul_one, ← pow_add, ← he]
        simpa only [add_sub_add_left_eq_sub] using P.sub_mem hi hj
      have hu : IsUnit (1 - b ^ (j - i)) :=
        isUnit_one_sub_self_of_mem_nonunits _ ((maximalIdeal R).pow_mem_of_mem (hJ hb) _ hpos)
      have hbP : b ∈ P := hp.mem_of_pow_mem _
        ((hp.mem_or_mem hd).resolve_right fun hm => hp.ne_top (P.eq_top_of_isUnit_mem hm hu))
      have haP : a ∈ P := by
        simpa only [add_sub_cancel_right] using
          P.sub_mem hi (P.pow_mem_of_mem hbP (i + 1) (Nat.succ_pos i))
      exact hbA (Set.mem_iUnion₂.mpr ⟨P, ⟨hP, haP⟩, hbP⟩)
    apply Set.Subsingleton.finite
    intro i hi j hj
    exact (lt_trichotomy i j).elim (fun h => (hlt i j hi hj h).elim)
      (fun h => h.elim id (fun h => (hlt j i hj hi h).elim))
  obtain ⟨n, hn⟩ := ((associatedPrimes.finite R M).biUnion hbad).exists_notMem
  refine ⟨b ^ (n + 1), J.pow_mem_of_mem hb _ (by omega), ?_⟩
  by_contra hreg
  have hh : a + b ^ (n + 1) ∈ ⋃ P ∈ associatedPrimes R M, (P : Set R) := by
    rwa [biUnion_associatedPrimes_eq_compl_regular R M]
  obtain ⟨P, hP, hhP⟩ := Set.mem_iUnion₂.mp hh
  exact hn (Set.mem_iUnion₂.mpr ⟨P, hP, hhP⟩)

private abbrev ResidueModule (R : Type u) [CommRing R] [IsLocalRing R] :=
  ModuleCat.of R (R ⧸ maximalIdeal R)

omit [IsNoetherianRing R] [IsLocalRing R] in
private theorem ext_after_regular (N M : ModuleCat.{u} R) {a : R}
    (ha : IsSMulRegular M a) {n : ℕ} (h : ∀ i < n + 1, Subsingleton (Ext N M i)) :
    ∀ i < n, Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop a M)) i) := by
  intro i hi
  have h₀ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h i (by omega))
  have h₁ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h (i + 1) (by omega))
  exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
    (Ext.covariant_sequence_exact₃' N ha.smulShortComplex_shortExact i (i + 1) rfl)
    (h₀.eq_zero_of_src _) (h₁.eq_zero_of_tgt _)

/-- The Rees argument for parameter lists, with prime avoidance in the local ring. -/
private theorem weaklyRegular_of_ext (rs : List R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hm : ∀ a ∈ rs, a ∈ maximalIdeal R)
    (hI : maximalIdeal R ≤ (Ideal.ofList rs ⊔ Module.annihilator R M).radical)
    (hext : ∀ i < rs.length, Subsingleton (Ext (ResidueModule R) M i)) :
    IsWeaklyRegular M rs := by
  induction rs generalizing M with
  | nil => exact IsWeaklyRegular.nil R M
  | cons a rs ih =>
    have hHom : Subsingleton (ResidueModule R →ₗ[R] M) :=
      (Ext.addEquiv₀.trans ModuleCat.homAddEquiv).subsingleton_congr.mp
        (hext 0 (by simp))
    obtain ⟨r, hr, hreg⟩ := IsSMulRegular.subsingleton_linearMap_iff.mp hHom
    have hAnn : Module.annihilator R (ResidueModule R) = maximalIdeal R :=
      Ideal.annihilator_quotient
    have hrm : r ∈ maximalIdeal R := hAnn ▸ hr
    let J := Ideal.ofList rs
    have hJm : J ≤ maximalIdeal R := Ideal.span_le.mpr
      (fun z hz => hm z (List.mem_cons_of_mem _ hz))
    obtain ⟨b, hb, hab⟩ := regular_add_mem (M := M) a J hJm (by
      intro P hP haP hJP
      have hassoc : IsAssociatedPrime P M := hP
      have hle : Ideal.ofList (a :: rs) ⊔ Module.annihilator R M ≤ P := by
        rw [Ideal.ofList_cons]
        exact sup_le (sup_le ((Ideal.span_singleton_le_iff_mem P).mpr haP) hJP)
          (by simpa only [Submodule.annihilator_top] using hassoc.annihilator_le)
      have hrP := hassoc.isPrime.radical_le_iff.mpr hle (hI hrm)
      have hru : r ∈ ⋃ P ∈ associatedPrimes R M, (P : Set R) :=
        Set.mem_iUnion₂.mpr ⟨P, hP, hrP⟩
      rw [biUnion_associatedPrimes_eq_compl_regular R M] at hru
      exact hru hreg)
    let M' := ModuleCat.of R (QuotSMulTop (a + b) M)
    have habann : a + b ∈ Module.annihilator R M' := QuotSMulTop.mem_annihilator M (a + b)
    have hann : Module.annihilator R M ≤ Module.annihilator R M' :=
      (Submodule.mkQ _).annihilator_le_of_surjective (Submodule.mkQ_surjective _)
    have hle : Ideal.ofList (a :: rs) ⊔ Module.annihilator R M ≤
        J ⊔ Module.annihilator R M' := by
      rw [Ideal.ofList_cons]
      refine sup_le (sup_le ((Ideal.span_singleton_le_iff_mem _).mpr ?_) le_sup_left)
        (hann.trans le_sup_right)
      have hsum : a + b ∈ J ⊔ Module.annihilator R M' := Ideal.mem_sup_right habann
      have hb' : b ∈ J ⊔ Module.annihilator R M' := Ideal.mem_sup_left hb
      simpa only [add_sub_cancel_right] using (J ⊔ Module.annihilator R M').sub_mem hsum hb'
    have htail := ih M' (fun z hz => hm z (List.mem_cons_of_mem _ hz))
      (hI.trans (Ideal.radical_mono hle)) (ext_after_regular _ M hab hext)
    have hcons : IsWeaklyRegular M ((a + b) :: rs) := IsWeaklyRegular.cons hab htail
    have happ : IsWeaklyRegular M (rs ++ [a + b]) :=
      IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal hcons
        (show List.Perm ([a + b] ++ rs) (rs ++ [a + b]) from List.perm_append_comm) (by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact Ideal.add_mem _ (hm a List.mem_cons_self) (hJm hb)
        · exact hm z (List.mem_cons_of_mem _ hz))
    obtain ⟨hrs, hlast⟩ := (isWeaklyRegular_append_iff M rs [a + b]).mp happ
    let T : Submodule R M := J • ⊤
    have hlast' : IsSMulRegular (M ⧸ T) (a + b) := (isWeaklyRegular_singleton_iff _ _).mp hlast
    have ha : IsSMulRegular (M ⧸ T) a := by
      rw [isSMulRegular_quotient_iff_mem_of_smul_mem] at hlast' ⊢
      intro x hx
      apply hlast'
      have hbT : b • x ∈ T := by
        apply (Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem J).mpr hb) :
          Ideal.span {b} • (⊤ : Submodule R M) ≤ T)
        rw [Submodule.ideal_span_singleton_smul]
        exact Submodule.smul_mem_pointwise_smul x b ⊤ trivial
      rw [add_smul]
      exact T.add_mem hx hbT
    have hnew : IsWeaklyRegular M (rs ++ [a]) :=
      (isWeaklyRegular_append_iff M rs [a]).mpr
        ⟨hrs, (isWeaklyRegular_singleton_iff _ _).mpr ha⟩
    have hp : List.Perm (a :: rs) (rs ++ [a]) :=
      show List.Perm ([a] ++ rs) (rs ++ [a]) from List.perm_append_comm
    exact IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal hnew hp.symm
      (fun z hz => hm z (hp.mem_iff.mpr hz))

/-- Compare a system of parameters with a regular sequence of the same length. -/
theorem weaklyRegular_of_parameters (ref rs : List R) (hlen : ref.length = rs.length)
    (hmem : ∀ a ∈ ref, a ∈ maximalIdeal R) (href : IsRegular R ref)
    (hrad : (Ideal.ofList rs).radical = maximalIdeal R) :
    IsWeaklyRegular R rs := by
  let N := ResidueModule R
  have hAnn : Module.annihilator R N = maximalIdeal R := Ideal.annihilator_quotient
  have hSupp : Module.support R N ⊆ PrimeSpectrum.zeroLocus (maximalIdeal R) := by
    rw [Module.support_eq_zeroLocus, hAnn]
  have hlt : maximalIdeal R • (⊤ : Submodule R R) < ⊤ := by
    change maximalIdeal R • (⊤ : Ideal R) < ⊤
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top.lt_top
  have hext := ModuleCat.subsingleton_ext_of_exists_isRegular _ N hSupp
    (ModuleCat.of R R) hlt ref hmem href
  exact weaklyRegular_of_ext rs (ModuleCat.of R R)
    (fun a ha => hrad ▸ (Ideal.ofList rs).le_radical (Ideal.subset_span ha))
    (hrad ▸ Ideal.radical_mono le_sup_left) (fun i hi => hext i (hlen ▸ hi))

end K1_13_7_5_3_3_2_2
end PackSource_K1_13_7_5_3_3_2_2Parameters
