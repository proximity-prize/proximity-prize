import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.GradedRank
import ArkLib.Data.CodingTheory.ProximityGenerator.AffineGenerator
import ArkLib.Data.CodingTheory.ProximityGenerator.Interleaving
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.CurveCertificate
import ArkLib.Data.MvPolynomial.RadicalSplit.Separable
import ArkLib.Data.MvPolynomial.WeightedDegree.Products
import ArkLib.Data.Polynomial.Differential.OrderZeroPresentation
import ArkLib.Data.Polynomial.ResultantDegree
import Mathlib.Data.Int.Star
import ProximityPrize.SubmissionLower.Fast006
import ProximityPrize.SubmissionLower.Fast008
set_option autoImplicit true
section
namespace Sol1.C42
def listCap : ℕ := 123935685281173519
def I1 : ℚ := 131072 / 49193
def b (v : ℕ) : ℕ := 1 + 2 * 131073 * (v - 1)
def firstOrderCharge (h : ℕ) : ℚ := I1 * h * b h + (h : ℚ) * (h - 1)
end Sol1.C42
end
section
namespace Sol1.C42
set_option maxRecDepth 100000
set_option maxHeartbeats 0
end Sol1.C42
end
section
namespace K1_13_5_3
noncomputable section
open MvPolynomial
open scoped BigOperators
theorem mem_capped {F : Type*} [Field F] (g : MvPolynomial (Fin 2) F) {j r : ℕ}
    (hj : g.totalDegree ≤ j) (hr : g.degreeOf 1 ≤ r) :
    g ∈ restrictCappedDegree (Fin 2) F 1 j r := by
  intro m hm
  exact ⟨(le_totalDegree hm).trans hj, (monomial_le_degreeOf 1 hm).trans hr⟩
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
end
section
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
theorem prod_polynomial_monomial {S : Type} [CommSemiring S] {ι : Type}
    (s : Finset ι) (d : ι → ℕ) (f : ι → S) :
    (∏ i ∈ s, Polynomial.monomial (d i) (f i)) =
      Polynomial.monomial (∑ i ∈ s, d i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, ih, Finset.sum_insert hi, Finset.prod_insert hi,
      Polynomial.monomial_mul_monomial]
theorem homogeneousEval_monomial (J : Ideal (Affine (k := k) (σ := σ)))
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
theorem monomial_box (J : Ideal (Affine (k := k) (σ := σ)))
    (s : σ →₀ ℕ) (n a b : ℕ) (c : k) (hn : n ≤ a) (hs : s.degree ≤ b) :
    Ideal.Quotient.mk J (MvPolynomial.monomial (s.optionElim n) c) ∈
      quotientBidegreeLE J a b := by
  refine mem_quotientBidegreeLE.mpr ⟨_, ?_, rfl⟩
  change MvPolynomial.monomial (s.optionElim n) c ∈
    restrictSupport k (bidegreeExponents σ a b)
  apply (monomial_mem_restrictSupport k).mpr (Or.inl _)
  simpa only [mem_bidegreeExponents, Finsupp.optionElim_apply_none, Finsupp.some_optionElim]
    using And.intro hn hs
theorem eval_coeff_mem_box (J : Ideal (Affine (k := k) (σ := σ)))
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
end
section
namespace K1_13_7_5_3_3_2_2
open Ideal IsLocalRing RingTheory.Sequence CategoryTheory Abelian
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
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
end
section
namespace Sol1.MasonSparsePlace
open Polynomial UniqueFactorizationMonoid
variable {E : Type*} [Field E]
end Sol1.MasonSparsePlace
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K1_11
noncomputable section
open MvPolynomial
variable {F σ : Type*} [Field F]
def contactExponent (v : σ → ℕ) : (σ →₀ ℕ) →+ (Option σ →₀ ℕ) where
  toFun e := e.optionElim (e.weight v)
  map_zero' := by ext i; cases i <;> simp
  map_add' e f := by ext i; cases i <;> simp
theorem contactExponent_injective (v : σ → ℕ) : Function.Injective (contactExponent v) := by
  intro e f h
  have := congrArg Finsupp.some h
  simpa [contactExponent] using this
def contactLift (v : σ → ℕ) : MvPolynomial σ F →+* Polynomial (MvPolynomial σ F) :=
  (optionEquivLeft F σ).toRingHom.comp (AddMonoidAlgebra.mapDomainRingHom F (contactExponent v))
theorem contactLift_injective (v : σ → ℕ) : Function.Injective (contactLift (F:=F) v) :=
  (optionEquivLeft F σ).injective.comp
    (AddMonoidAlgebra.mapDomain_injective (contactExponent_injective v))
theorem contactLift_monomial (v : σ → ℕ) (e : σ →₀ ℕ) (a : F) :
    contactLift v (monomial e a)=Polynomial.monomial (e.weight v) (monomial e a) := by
  change (optionEquivLeft F σ) (AddMonoidAlgebra.mapDomain (contactExponent v) (monomial e a))=_
  change (optionEquivLeft F σ) (AddMonoidAlgebra.mapDomain (contactExponent v) (AddMonoidAlgebra.single e a))=_
  rw [AddMonoidAlgebra.mapDomain_single]
  change (optionEquivLeft F σ) (monomial ((contactExponent v) e) a)=_
  rw [optionEquivLeft_monomial]
  simp [contactExponent]
theorem contactLift_coeff (v : σ → ℕ) (P : MvPolynomial σ F) (n : ℕ) (e : σ →₀ ℕ) :
    ((contactLift v P).coeff n).coeff e=if e.weight v=n then P.coeff e else 0 := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial f a =>
    rw [contactLift_monomial]
    by_cases hfe : f=e
    · subst f
      split_ifs <;> simp_all [Polynomial.coeff_monomial]
    · by_cases hw : f.weight v=n <;> by_cases he : e.weight v=n <;> simp [Polynomial.coeff_monomial,MvPolynomial.coeff_monomial,hfe,Ne.symm hfe,hw,he]
  | add P Q hP hQ =>
    simp only [map_add,Polynomial.coeff_add,MvPolynomial.coeff_add,hP,hQ]
    split_ifs <;> simp
theorem contactLift_X_pow_dvd_iff (v : σ → ℕ) (m : ℕ) (P : MvPolynomial σ F) :
    Polynomial.X^m ∣ contactLift v P ↔ P∈restrictWeightedOrder v m := by
  rw [Polynomial.X_pow_dvd_iff,mem_restrictWeightedOrder]
  constructor
  · intro h e he
    by_contra hh
    have hc := congrArg (fun Q : MvPolynomial σ F => Q.coeff e) (h (e.weight v) (by omega))
    rw [contactLift_coeff,if_pos rfl] at hc
    exact (mem_support_iff.mp he) hc
  · intro h n hn
    ext e
    rw [contactLift_coeff]
    by_cases he : e.weight v=n
    · rw [if_pos he]
      by_contra hc
      have := h e (mem_support_iff.mpr hc)
      omega
    · simp [he]
theorem contact_order_one_of_coefficient (v : σ → ℕ) (L : MvPolynomial σ F)
    (horder : L∈restrictWeightedOrder v 1) (e : σ →₀ ℕ)
    (he : e.weight v=1) (hc : L.coeff e≠0) :
    (contactLift v L).natTrailingDegree=1 := by
  have hLn : L≠0 := by intro hz; exact hc (by rw [hz]; rfl)
  have hLn' : contactLift v L≠0 := fun hz => hLn (contactLift_injective v (hz.trans (map_zero _).symm))
  have hlow := Polynomial.le_natTrailingDegree hLn'
    (Polynomial.X_pow_dvd_iff.mp ((contactLift_X_pow_dvd_iff v 1 L).mpr horder))
  have hc' : (contactLift v L).coeff 1≠0 := by
    intro hz
    have hh := congrArg (fun P : MvPolynomial σ F => P.coeff e) hz
    rw [contactLift_coeff,if_pos he] at hh
    exact hc hh
  have hup := Polynomial.natTrailingDegree_le_of_ne_zero hc'
  omega
theorem contact_product_not_high_order (v : σ → ℕ) (m : ℕ)
    (L H : MvPolynomial σ F)
    (hL : (contactLift v L).natTrailingDegree=1) (hLn : L≠0)
    (hH : H≠0) (hHlow : ∀ e∈H.support,e.weight v<m-1) :
    L*H ∉ restrictWeightedOrder v m := by
  intro hh
  have hLn' : contactLift v L≠0 := fun hz => hLn (contactLift_injective v (hz.trans (map_zero _).symm))
  have hHn' : contactLift v H≠0 := fun hz => hH (contactLift_injective v (hz.trans (map_zero _).symm))
  have hmul : contactLift v (L*H)≠0 := by rw [map_mul]; exact mul_ne_zero hLn' hHn'
  have hhigh := Polynomial.le_natTrailingDegree hmul
    (Polynomial.X_pow_dvd_iff.mp ((contactLift_X_pow_dvd_iff v m (L*H)).mpr hh))
  rw [map_mul,Polynomial.natTrailingDegree_mul hLn' hHn',hL] at hhigh
  obtain ⟨e,he⟩ := support_nonempty.mpr hH
  have hc : (contactLift v H).coeff (e.weight v)≠0 := by
    intro hz
    have hz' := congrArg (fun Q : MvPolynomial σ F => Q.coeff e) hz
    rw [contactLift_coeff,if_pos rfl] at hz'
    exact (mem_support_iff.mp he) hz'
  have hmin := Polynomial.natTrailingDegree_le_of_ne_zero hc
  have := hHlow e he
  omega
end
end K1_11
end
section
namespace Sol1.C57
open Polynomial PolynomialDifferential MvPolynomial
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def topVariableEquiv (d : ℕ) : JetVariable (d + 1) ≃ Option (JetVariable d) :=
  (Equiv.optionCongr (finSuccEquiv' (Fin.last (d + 1)))).trans (Equiv.swap none (some none))
@[simp] theorem topVariableEquiv_x (d : ℕ) : topVariableEquiv d none = some none := by
  simp [topVariableEquiv]
@[simp] theorem topVariableEquiv_top (d : ℕ) :
    topVariableEquiv d (some (Fin.last (d + 1))) = none := by
  simp [topVariableEquiv]
@[simp] theorem topVariableEquiv_lower (d : ℕ) (j : Fin (d + 1)) :
    topVariableEquiv d (some j.castSucc) = some (some j) := by
  have hj : j.castSucc < Fin.last (d + 1) := Fin.castSucc_lt_last j
  simp [topVariableEquiv, finSuccEquiv'_below hj, Equiv.swap_apply_def]
variable {E : Type*} [CommRing E]
def topReindex (d : ℕ) : DifferentialPolynomial E (d + 1) ≃ₐ[E]
    MvPolynomial (Option (JetVariable d)) E := renameEquiv E (topVariableEquiv d)
def topPresentation (d : ℕ) : DifferentialPolynomial E (d + 1) ≃ₐ[E]
    Polynomial (DifferentialPolynomial E d) :=
  (topReindex d).trans (optionEquivLeft E (JetVariable d))
def rootJetWeight (d : ℕ) : Option (JetVariable d) → ℕ := fun v ↦ v.elim 1 jetDegreeWeight
theorem topReindex_weight (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    (topReindex d Q).weightedTotalDegree (rootJetWeight d) = jetTotalDegree Q := by
  rw [topReindex, renameEquiv_apply, weightedTotalDegree_rename_of_injective
    (topVariableEquiv d).injective, jetTotalDegree]
  congr 1
  funext v
  rcases v with _ | j
  · simp [rootJetWeight, jetDegreeWeight]
  · induction j using Fin.lastCases with
    | last => simp [rootJetWeight, jetDegreeWeight]
    | cast j => simp [rootJetWeight, jetDegreeWeight]
theorem topReindex_degree (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    degreeOf none (topReindex d Q) = jetDegree Q (Fin.last (d + 1)) := by
  have h := degreeOf_rename_of_injective (p := Q) (topVariableEquiv d).injective
    (some (Fin.last (d + 1)))
  simpa only [topReindex, renameEquiv_apply, topVariableEquiv_top, jetDegree] using h
theorem topPresentation_degree (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    (topPresentation d Q).natDegree = jetDegree Q (Fin.last (d + 1)) := by
  rw [topPresentation, AlgEquiv.trans_apply, natDegree_optionEquivLeft, topReindex_degree]
theorem topReindex_pderiv (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    pderiv none (topReindex d Q) = topReindex d (separant Q (Fin.last (d + 1))) := by
  have h := pderiv_rename (topVariableEquiv d).injective (some (Fin.last (d + 1))) Q
  simpa only [topReindex, renameEquiv_apply, topVariableEquiv_top, separant] using h
theorem topPresentation_derivative (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    (topPresentation d Q).derivative = topPresentation d (separant Q (Fin.last (d + 1))) := by
  change (optionEquivLeft E (JetVariable d) (topReindex d Q)).derivative = _
  rw [← optionEquivLeft_pderiv_none, topReindex_pderiv]
  rfl
theorem coeff_weight_add_le {σ : Type*} (w : σ → ℕ)
    (Q : MvPolynomial (Option σ) E) (i : ℕ) (hi : i ≤ degreeOf none Q) :
    i + ((optionEquivLeft E σ Q).coeff i).weightedTotalDegree w ≤
      Q.weightedTotalDegree (fun v ↦ v.elim 1 w) := by
  classical
  have hiB : i ≤ Q.weightedTotalDegree (fun v ↦ v.elim 1 w) :=
    hi.trans (degreeOf_le_weightedTotalDegree _ none (by simp) Q)
  have hh : ((optionEquivLeft E σ Q).coeff i).weightedTotalDegree w ≤
      Q.weightedTotalDegree (fun v ↦ v.elim 1 w) - i := by
    apply Finset.sup_le_iff.mpr
    intro u hu
    have hs := (mem_support_coeff_optionEquivLeft E).mp hu
    have hw := le_weightedTotalDegree (fun v : Option σ ↦ v.elim 1 w) hs
    rw [Finsupp.weight_optionElim, one_mul] at hw
    omega
  omega
theorem topPresentation_eval (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) (P : E[X]) :
    (topPresentation d Q).eval₂ (differentialSpecializationHom (d := d) P).toRingHom
      (Polynomial.hasseDeriv (d + 1) P) = differentialSpecialization Q P := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [topPresentation, topReindex, differentialSpecialization_C]
  | add Q R hQ hR =>
    simp only [map_add, Polynomial.eval₂_add, differentialSpecialization,
      map_add, hQ, hR]
  | mul_X Q v hQ =>
    have hv : (topPresentation d (MvPolynomial.X v)).eval₂
        (differentialSpecializationHom (d := d) P).toRingHom
        (Polynomial.hasseDeriv (d + 1) P) =
        differentialSpecialization (MvPolynomial.X v) P := by
      rcases v with _ | j
      · simp [topPresentation, topReindex]
      · induction j using Fin.lastCases with
        | last => simp [topPresentation, topReindex]
        | cast j => simp [topPresentation, topReindex]
    simp only [map_mul, Polynomial.eval₂_mul, differentialSpecialization,
      map_mul, hQ, hv]
end
end Sol1.C57
end
section
namespace Sol1.C57
open Polynomial PolynomialDifferential MvPolynomial
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
variable {E : Type*} [Field E]
def regularPart (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    DifferentialPolynomial E (d + 1) :=
  (topReindex d).symm (radicalPrimPart none (topReindex d Q))
def lowerPart (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) : DifferentialPolynomial E d :=
  (optionEquivLeft E (JetVariable d) (radicalContent none (topReindex d Q))).coeff 0
theorem content_presentation (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    optionEquivLeft E (JetVariable d) (radicalContent none (topReindex d Q)) =
      Polynomial.C (lowerPart d Q) := by
  apply Polynomial.eq_C_of_natDegree_eq_zero
  rw [natDegree_optionEquivLeft, degreeOf_radicalContent]
theorem optionEquivLeft_rename_some {σ : Type*} (T : MvPolynomial σ E) :
    optionEquivLeft E σ (rename some T) = Polynomial.C T := by
  induction T using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p j hp => simp [hp]
theorem content_eq_rename (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    radicalContent none (topReindex d Q) = rename some (lowerPart d Q) := by
  apply (optionEquivLeft E (JetVariable d)).injective
  rw [content_presentation, optionEquivLeft_rename_some]
theorem content_weight (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    (radicalContent none (topReindex d Q)).weightedTotalDegree (rootJetWeight d) =
      jetTotalDegree (lowerPart d Q) := by
  rw [content_eq_rename, weightedTotalDegree_rename_of_injective (Option.some_injective (JetVariable d))]
  rfl
theorem regular_weight (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    (radicalPrimPart none (topReindex d Q)).weightedTotalDegree (rootJetWeight d) =
      jetTotalDegree (regularPart d Q) := by
  have h := topReindex_weight d (regularPart d Q)
  simpa only [regularPart, AlgEquiv.apply_symm_apply] using h
theorem split_weight (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    jetTotalDegree (lowerPart d Q) + jetTotalDegree (regularPart d Q) ≤ jetTotalDegree Q := by
  have h := map_radicalContent_add_map_radicalPrimPart_le
    (d := fun T ↦ T.weightedTotalDegree (rootJetWeight d))
    (fun x y hx hy ↦ weightedTotalDegree_mul _ x y hx hy) none (topReindex d Q)
  rwa [content_weight, regular_weight, topReindex_weight] at h
theorem lower_ne_zero (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    lowerPart d Q ≠ 0 := by
  intro hz
  have h := content_presentation d Q
  rw [hz, Polynomial.C_0] at h
  apply radicalContent_ne_zero none (topReindex d Q)
  apply (optionEquivLeft E (JetVariable d)).injective
  simpa only [map_zero] using h
theorem regular_presentation (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    topPresentation d (regularPart d Q) = ordinaryRootPolynomial (topReindex d Q) := by
  simp [topPresentation, regularPart, ordinaryRootPolynomial]
def rootEvaluation (d : ℕ) (P : E[X]) :
    MvPolynomial (Option (JetVariable d)) E →+* E[X] :=
  (differentialSpecializationHom (d := d + 1) P).toRingHom.comp (topReindex d).symm.toRingHom
theorem rootEvaluation_content (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) (P : E[X]) :
    rootEvaluation d P (radicalContent none (topReindex d Q)) =
      differentialSpecialization (lowerPart d Q) P := by
  have h := topPresentation_eval d
    ((topReindex d).symm (radicalContent none (topReindex d Q))) P
  rw [show topPresentation d ((topReindex d).symm (radicalContent none (topReindex d Q))) =
      Polynomial.C (lowerPart d Q) by
        simp only [topPresentation, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply,
          content_presentation]] at h
  change differentialSpecialization
    ((topReindex d).symm (radicalContent none (topReindex d Q))) P = _
  simpa only [Polynomial.eval₂_C, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, differentialSpecialization] using h.symm
theorem root_split (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) (hQ : Q ≠ 0) (P : E[X])
    (hroot : differentialSpecialization Q P = 0) :
    differentialSpecialization (lowerPart d Q) P = 0 ∨
      differentialSpecialization (regularPart d Q) P = 0 := by
  have hQr : topReindex d Q ≠ 0 :=
    (map_ne_zero_iff (topReindex d) (topReindex d).injective).mpr hQ
  have hz := (map_radicalContent_mul_radicalPrimPart_eq_zero_iff
    (rootEvaluation d P) none hQr).mpr (by simpa [rootEvaluation] using hroot)
  rw [map_mul, rootEvaluation_content, mul_eq_zero] at hz
  exact hz
theorem regular_eq_one_of_degree_zero (d : ℕ) (Q : DifferentialPolynomial E (d + 1))
    (hdeg : jetDegree (regularPart d Q) (Fin.last (d + 1)) = 0) :
    regularPart d Q = 1 := by
  have hd : degreeOf none (radicalPrimPart none (topReindex d Q)) = 0 := by
    simpa only [regularPart, AlgEquiv.apply_symm_apply] using
      (topReindex_degree d (regularPart d Q)).trans hdeg
  rw [regularPart, radicalPrimPart_eq_one_of_degreeOf_eq_zero none _ hd, map_one]
def singularEquation (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) : DifferentialPolynomial E d :=
  let f := ordinaryRootPolynomial (topReindex d Q)
  Polynomial.resultant f f.derivative f.natDegree (f.natDegree - 1)
theorem singularEquation_ne_zero (d : ℕ) (Q : DifferentialPolynomial E (d + 1))
    (hchar : ringChar E = 0 ∨ jetDegree Q (Fin.last (d + 1)) < ringChar E) :
    singularEquation d Q ≠ 0 := by
  apply Polynomial.resultant_derivative_ne_zero_ordinaryRootPolynomial
  rwa [topReindex_degree]
end
end Sol1.C57
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K1_11
noncomputable section
open MvPolynomial
variable {F σ ι : Type*} [Field F]
def filtered (v : ι → σ → ℕ) (d : ι → ℕ) : Submodule F (MvPolynomial σ F) :=
  ⨅ i, restrictWeightedDegree (v i) (d i)
@[simp] theorem mem_filtered (v : ι → σ → ℕ) (d : ι → ℕ) (P : MvPolynomial σ F) :
    P ∈ filtered v d ↔ ∀ i, P.weightedTotalDegree (v i) ≤ d i := by
  simp only [filtered, Submodule.mem_iInf, mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
theorem mul_mem_filtered_iff (v : ι → σ → ℕ) (d e : ι → ℕ)
    (L H : MvPolynomial σ F) (hL : L≠0)
    (hdeg : ∀ i, L.weightedTotalDegree (v i)=e i) (hed : ∀ i,e i≤d i) :
    L*H ∈ filtered v d ↔ H ∈ filtered v (fun i => d i-e i) := by
  by_cases hH : H=0
  · simp [hH]
  · simp only [mem_filtered]
    constructor
    · intro h i
      have hi := h i
      rw [weightedTotalDegree_mul _ _ _ hL hH,hdeg i] at hi
      omega
    · intro h i
      have hi := h i
      rw [weightedTotalDegree_mul _ _ _ hL hH,hdeg i]
      have := hed i
      omega
def filteredMul (v : ι → σ → ℕ) (d e : ι → ℕ) (L : MvPolynomial σ F)
    (hL : L≠0) (hdeg : ∀ i,L.weightedTotalDegree (v i)=e i)
    (hed : ∀ i,e i≤d i) :
    filtered (F:=F) v (fun i => d i-e i) →ₗ[F] filtered (F:=F) v d where
  toFun H := ⟨L*H.val,(mul_mem_filtered_iff v d e L H.val hL hdeg hed).mpr H.property⟩
  map_add' H J := by apply Subtype.ext; exact mul_add L H.val J.val
  map_smul' a H := by apply Subtype.ext; exact mul_smul_comm a L H.val
theorem filteredMul_injective (v : ι → σ → ℕ) (d e : ι → ℕ)
    (L : MvPolynomial σ F) (hL : L≠0)
    (hdeg : ∀ i,L.weightedTotalDegree (v i)=e i) (hed : ∀ i,e i≤d i) :
    Function.Injective (filteredMul v d e L hL hdeg hed) := by
  intro H J heq
  apply Subtype.ext
  exact mul_left_cancel₀ hL (congrArg Subtype.val heq)
theorem mem_filteredMul_range_iff (v : ι → σ → ℕ) (d e : ι → ℕ)
    (L : MvPolynomial σ F) (hL : L≠0)
    (hdeg : ∀ i,L.weightedTotalDegree (v i)=e i) (hed : ∀ i,e i≤d i)
    (Q : filtered (F:=F) v d) :
    Q ∈ LinearMap.range (filteredMul v d e L hL hdeg hed) ↔ L ∣ Q.val := by
  constructor
  · rintro ⟨H,hH⟩
    exact ⟨H.val,congrArg Subtype.val hH.symm⟩
  · rintro ⟨H,hH⟩
    have hm : H ∈ filtered v (fun i => d i-e i) :=
      (mul_mem_filtered_iff v d e L H hL hdeg hed).mp (hH ▸ Q.property)
    exact ⟨⟨H,hm⟩,Subtype.ext hH.symm⟩
end
end K1_11
end
section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace K1_11
noncomputable section
open Finset MvPolynomial
def sourceWeights (w : ℕ) : Fin 4 → Fin 5 → ℕ :=
  ![![1,w,w,0,0], ![0,1,1,0,0], ![0,1,0,1,0], ![0,0,1,0,1]]
def sourceBounds (D B s t : ℕ) : Fin 4 → ℕ := ![D,B,s,t]
def tuples (D w B s t : ℕ) : Finset (Σ _ : ℕ, Σ _ : ℕ, ℕ × ℕ × ℕ) :=
  (range (B+1)).sigma fun i => (range (B+1-i)).sigma fun j =>
    (range (D+1-w*(i+j))) ×ˢ ((range (s+1-i)) ×ˢ (range (t+1-j)))
def exponent5 (x i j a b : ℕ) : Fin 5 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![x,i,j,a,b]
def tupleExponent (c : Σ _ : ℕ, Σ _ : ℕ, ℕ × ℕ × ℕ) : Fin 5 →₀ ℕ :=
  exponent5 c.2.2.1 c.1 c.2.1 c.2.2.2.1 c.2.2.2.2
@[simp] theorem exponent5_apply (x i j a b : ℕ) (q : Fin 5) :
    exponent5 x i j a b q = ![x,i,j,a,b] q := by
  simp [exponent5]
theorem tupleExponent_injective : Function.Injective tupleExponent := by
  intro c d h
  have h0 := congrArg (fun e : Fin 5 →₀ ℕ => e 0) h
  have h1 := congrArg (fun e : Fin 5 →₀ ℕ => e 1) h
  have h2 := congrArg (fun e : Fin 5 →₀ ℕ => e 2) h
  have h3 := congrArg (fun e : Fin 5 →₀ ℕ => e 3) h
  have h4 := congrArg (fun e : Fin 5 →₀ ℕ => e 4) h
  simp only [tupleExponent,exponent5_apply,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.head_cons] at h0 h1 h2 h3 h4
  rcases c with ⟨i,j,x,a,b⟩
  rcases d with ⟨i',j',x',a',b'⟩
  dsimp at h0 h1 h2 h3 h4
  subst i'; subst j'; subst x'; subst a'; subst b'
  rfl
@[simp] theorem tuples_card (D w B s t : ℕ) : (tuples D w B s t).card=V D w B s t := by
  simp [tuples,V,card_sigma,Nat.mul_assoc]
def sourceExponents (D w B s t : ℕ) : Finset (Fin 5 →₀ ℕ) :=
  (tuples D w B s t).image tupleExponent
theorem sourceExponents_card (D w B s t : ℕ) :
    (sourceExponents D w B s t).card=V D w B s t := by
  rw [sourceExponents,card_image_of_injective _ tupleExponent_injective,tuples_card]
theorem weight5 (e : Fin 5 →₀ ℕ) (a b c d f : ℕ) :
    e.weight ![a,b,c,d,f]=e 0*a+e 1*b+e 2*c+e 3*d+e 4*f := by
  simp [Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_succ,smul_eq_mul]
  omega
theorem mem_sourceExponents (D w B s t : ℕ) (e : Fin 5 →₀ ℕ) :
    e∈sourceExponents D w B s t ↔
    e 0+w*(e 1+e 2)≤D ∧ e 1+e 2≤B ∧ e 1+e 3≤s ∧ e 2+e 4≤t := by
  constructor
  · rintro he
    obtain ⟨⟨i,j,x,a,b⟩,hc,rfl⟩ := mem_image.mp he
    simp only [tuples,mem_sigma,mem_range,mem_product] at hc
    simp [tupleExponent]
    omega
  · rintro ⟨hX,hY,hS,hT⟩
    apply mem_image.mpr
    refine ⟨⟨e 1,e 2,e 0,e 3,e 4⟩,?_,?_⟩
    · simp only [tuples,mem_sigma,mem_range,mem_product]
      omega
    · ext q
      fin_cases q <;> simp [tupleExponent]
theorem source_filtered_eq {F : Type*} [Field F] (D w B s t : ℕ) :
    filtered (F:=F) (sourceWeights w) (sourceBounds D B s t)=
      restrictSupport F (↑(sourceExponents D w B s t) : Set (Fin 5 →₀ ℕ)) := by
  ext P
  rw [mem_filtered]
  simp only [mem_restrictSupport_iff,Finset.mem_coe]
  constructor
  · intro h e he
    apply (mem_sourceExponents D w B s t e).mpr
    have hh q := (le_weightedTotalDegree (sourceWeights w q) he).trans (h q)
    have h0 := hh 0
    have h1 := hh 1
    have h2 := hh 2
    have h3 := hh 3
    simp [sourceWeights,sourceBounds,weight5] at h0 h1 h2 h3
    constructor
    · nlinarith
    · exact ⟨h1,h2,h3⟩
  · intro h q
    apply Finset.sup_le
    change ∀ e∈P.support, _
    intro e he
    have hh := (mem_sourceExponents D w B s t e).mp (h he)
    fin_cases q <;> simp [sourceWeights,sourceBounds,weight5] <;> nlinarith
instance source_filtered_finite {F : Type*} [Field F] (D w B s t : ℕ) :
    Module.Finite F (filtered (F:=F) (sourceWeights w) (sourceBounds D B s t)) := by
  rw [source_filtered_eq]
  exact restrictSupport_finite (Finset.finite_toSet _)
theorem source_filtered_finrank {F : Type*} [Field F] (D w B s t : ℕ) :
    Module.finrank F (filtered (F:=F) (sourceWeights w) (sourceBounds D B s t))=
      V D w B s t := by
  rw [source_filtered_eq,finrank_restrictSupport_finset,sourceExponents_card]
end
end K1_11
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K1_11
noncomputable section
open Finset MvPolynomial
variable {F σ : Type*} [Field F]
theorem clearedEval_weight_bound (v : σ → ℕ) (B d e aa bb : ℕ)
    (Q : Polynomial (MvPolynomial σ F)) (a b : MvPolynomial σ F)
    (hcoeff : ∀ j≤B,Q.coeff j≠0 → (Q.coeff j).weightedTotalDegree v+j*e≤d)
    (ha : a.weightedTotalDegree v≤aa) (hb : b.weightedTotalDegree v≤bb)
    (hbalance : aa≤e+bb) :
    (clearedEval B Q a b).weightedTotalDegree v≤d+B*bb := by
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  unfold clearedEval
  apply Submodule.sum_mem
  intro j hj
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
  by_cases hc : Q.coeff j=0
  · simp [hc,weightedTotalDegree]
  have hjB : j≤B := by have := mem_range.mp hj; omega
  have hco := hcoeff j hjB hc
  have hpa := (weightedTotalDegree_pow_le v a j).trans (Nat.mul_le_mul_left j ha)
  have hpb := (weightedTotalDegree_pow_le v b (B-j)).trans (Nat.mul_le_mul_left (B-j) hb)
  have hm := (weightedTotalDegree_mul_le v (Q.coeff j*a^j) (b^(B-j))).trans
    (Nat.add_le_add ((weightedTotalDegree_mul_le v _ _).trans (Nat.add_le_add_left hpa _)) hpb)
  have hjadd : j+(B-j)=B := Nat.add_sub_of_le hjB
  have hbal := Nat.mul_le_mul_left j hbalance
  nlinarith
end
end K1_11
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace K1_11
noncomputable section
open MvPolynomial
variable {F : Type*} [Field F]
def decoderPermutation : Fin 5 ≃ Fin 5 :=
  Equiv.ofBijective ![1,2,0,3,4] (by decide)
def polynomialView : MvPolynomial (Fin 5) F ≃ₐ[F] Polynomial (MvPolynomial (Fin 4) F) :=
  (renameEquiv F decoderPermutation).trans (finSuccEquiv F 4)
def scalarWeightY : Fin 4 → ℕ := ![0,1,0,0]
def scalarWeightYS : Fin 4 → ℕ := ![0,1,1,0]
def scalarWeightT : Fin 4 → ℕ := ![0,0,0,1]
theorem polynomialView_coeff_support (Q : MvPolynomial (Fin 5) F) (j : ℕ)
    (f : Fin 4 →₀ ℕ) (hf : f∈((polynomialView Q).coeff j).support) :
    ∃ e∈Q.support,e 0=f 0 ∧ e 1=f 1 ∧ e 2=j ∧ e 3=f 2 ∧ e 4=f 3 := by
  have hc := mem_support_iff.mp hf
  change ((finSuccEquiv F 4 (rename decoderPermutation Q)).coeff j).coeff f≠0 at hc
  rw [finSuccEquiv_coeff_coeff] at hc
  obtain ⟨e,he,hcoeff⟩ := coeff_rename_ne_zero decoderPermutation Q (f.cons j) hc
  refine ⟨e,mem_support_iff.mpr hcoeff,?_⟩
  have hh (i : Fin 5) := congrArg (fun z : Fin 5 →₀ ℕ => z (decoderPermutation i)) he
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  have h3 := hh 3
  have h4 := hh 4
  simp only [Finsupp.mapDomain_apply_of_injective decoderPermutation.injective] at h0 h1 h2 h3 h4
  simp [decoderPermutation] at h0 h1 h2 h3 h4
  exact ⟨h0,h1,h2,h3,h4⟩
theorem weighted_degree_plus_le {σ : Type*} (v : σ → ℕ) (P : MvPolynomial σ F)
    (c d : ℕ) (hP : P≠0) (h : ∀ e∈P.support,e.weight v+c≤d) :
    P.weightedTotalDegree v+c≤d := by
  obtain ⟨e,he⟩ := support_nonempty.mpr hP
  have hcd : c≤d := by have := h e he; omega
  have hdeg : P.weightedTotalDegree v≤d-c := by
    apply Finset.sup_le
    intro e he
    have := h e he
    omega
  omega
theorem polynomialView_source_coefficients (D w B s t : ℕ)
    (Q : MvPolynomial (Fin 5) F)
    (hQ : Q∈filtered (sourceWeights w) (sourceBounds D B s t)) :
    (∀ j≤B,(polynomialView Q).coeff j≠0 →
      ((polynomialView Q).coeff j).weightedTotalDegree scalarWeightY+j≤B) ∧
    (∀ j≤B,(polynomialView Q).coeff j≠0 →
      ((polynomialView Q).coeff j).weightedTotalDegree scalarWeightYS≤s) ∧
    (∀ j≤B,(polynomialView Q).coeff j≠0 →
      ((polynomialView Q).coeff j).weightedTotalDegree scalarWeightT+j≤t) := by
  have hmono (j : ℕ) (f : Fin 4 →₀ ℕ) (hf : f∈((polynomialView Q).coeff j).support) :
      f 1+j≤B ∧ f 1+f 2≤s ∧ j+f 3≤t := by
    obtain ⟨e,he,he0,he1,he2,he3,he4⟩ := polynomialView_coeff_support Q j f hf
    rw [source_filtered_eq,mem_restrictSupport_iff] at hQ
    have hh := (mem_sourceExponents D w B s t e).mp (hQ he)
    omega
  constructor
  · intro j hj hc
    apply weighted_degree_plus_le scalarWeightY _ j B hc
    intro f hf
    have hh := hmono j f hf
    simpa [scalarWeightY,Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_succ,smul_eq_mul] using hh.1
  constructor
  · intro j hj hc
    apply Finset.sup_le
    intro f hf
    have hh := hmono j f hf
    simpa [scalarWeightYS,Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_succ,smul_eq_mul] using hh.2.1
  · intro j hj hc
    apply weighted_degree_plus_le scalarWeightT _ j t hc
    intro f hf
    have hh := hmono j f hf
    simpa [scalarWeightT,Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_succ,smul_eq_mul,Nat.add_comm] using hh.2.2
theorem polynomialView_natDegree (D w B s t : ℕ) (Q : MvPolynomial (Fin 5) F)
    (hQ : Q∈filtered (sourceWeights w) (sourceBounds D B s t)) :
    (polynomialView Q).natDegree≤B := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  by_contra hc
  obtain ⟨f,hf⟩ := support_nonempty.mpr hc
  obtain ⟨e,he,he0,he1,he2,he3,he4⟩ := polynomialView_coeff_support Q j f hf
  rw [source_filtered_eq,mem_restrictSupport_iff] at hQ
  have hh := (mem_sourceExponents D w B s t e).mp (hQ he)
  omega
theorem polynomialView_X (i : Fin 5) :
    polynomialView (F:=F) (X i)=
      ![Polynomial.C (X 0),Polynomial.C (X 1),Polynomial.X,
        Polynomial.C (X 2),Polynomial.C (X 3)] i := by
  fin_cases i <;> simp [polynomialView,decoderPermutation,finSuccEquiv_apply,renameEquiv_apply] <;> rfl
def scalarImages (P : Polynomial F) (s t : F) : Fin 4 → Polynomial F :=
  ![Polynomial.X,P,Polynomial.C s,Polynomial.C t]
theorem polynomialView_eval (P Q : Polynomial F) (s t : F) (G : MvPolynomial (Fin 5) F) :
    Polynomial.eval₂ (aeval (scalarImages P s t)).toRingHom Q (polynomialView G)=
      aeval ![Polynomial.X,P,Q,Polynomial.C s,Polynomial.C t] G := by
  have heq : (Polynomial.eval₂RingHom (aeval (scalarImages P s t)).toRingHom Q).comp
      (polynomialView (F:=F)).toRingHom=(aeval ![Polynomial.X,P,Q,Polynomial.C s,Polynomial.C t]).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [polynomialView,finSuccEquiv_apply]
    · intro i
      change Polynomial.eval₂ (aeval (scalarImages P s t)).toRingHom Q (polynomialView (X i))=_
      rw [polynomialView_X]
      fin_cases i <;> simp [scalarImages]
  exact RingHom.congr_fun heq G
end
end K1_11
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K1_11
noncomputable section
open MvPolynomial Finset
variable {F : Type*} [Field F]
def contactWeight : Fin 5 → ℕ := ![1,1,1,0,0]
abbrev JetSpace (F : Type*) [Field F] (d s t : ℕ) :=
  filtered (F:=F) (sourceWeights 1) (sourceBounds d d s t)
theorem J_eq_V (d s t : ℕ) : J (d+1) s t=V d 1 d s t := by
  unfold J V
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  simp only [one_mul,Nat.sub_sub]
theorem jetSpace_finrank (d s t : ℕ) :
    Module.finrank F (JetSpace F d s t)=J (d+1) s t := by
  rw [J_eq_V]
  exact source_filtered_finrank d 1 d s t
theorem jetSpace_support_bound (d s t : ℕ) (H : JetSpace F d s t) :
    ∀ e∈H.val.support,e.weight contactWeight<d+1 := by
  intro e he
  have hh := (le_weightedTotalDegree (sourceWeights 1 0) he).trans
    ((mem_filtered _ _ _).mp H.property 0)
  simpa [sourceWeights,sourceBounds,contactWeight] using Nat.lt_succ_of_le hh
theorem truncated_mul_mem_jet (d s t dS dT : ℕ) (L : MvPolynomial (Fin 5) F)
    (hS : L.weightedTotalDegree (sourceWeights 1 2)≤dS)
    (hT : L.weightedTotalDegree (sourceWeights 1 3)≤dT)
    (H : JetSpace F d s t) :
    weightedTruncation contactWeight (d+2) (L*H.val) ∈ JetSpace F (d+1) (s+dS) (t+dT) := by
  simp only [JetSpace]
  rw [source_filtered_eq,mem_restrictSupport_iff]
  intro e he
  have hc : e.weight contactWeight<d+2 := by
    have he' := mem_support_iff.mp he
    rw [coeff_weightedTruncation] at he'
    by_contra hh
    exact he' (if_neg hh)
  have heL : e∈(L*H.val).support := by
    apply mem_support_iff.mpr
    have := mem_support_iff.mp he
    simpa only [coeff_weightedTruncation,if_pos hc] using this
  have hHs := (mem_filtered _ _ _).mp H.property 2
  have hHt := (mem_filtered _ _ _).mp H.property 3
  have hs := (le_weightedTotalDegree (sourceWeights 1 2) heL).trans
    ((weightedTotalDegree_mul_le _ _ _).trans (Nat.add_le_add hS hHs))
  have ht := (le_weightedTotalDegree (sourceWeights 1 3) heL).trans
    ((weightedTotalDegree_mul_le _ _ _).trans (Nat.add_le_add hT hHt))
  apply (mem_sourceExponents (d+1) 1 (d+1) (s+dS) (t+dT) e).mpr
  simp [sourceWeights,sourceBounds,contactWeight,weight5] at hc hs ht ⊢
  omega
end
end K1_11
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K1_11
noncomputable section
open MvPolynomial
variable {F : Type*} [Field F]
def shiftImages (x a b c d : F) : Fin 5 → MvPolynomial (Fin 5) F :=
  ![X 0+C x,X 1+C a+X 3*C b,X 2+C c+X 4*C d,X 3,X 4]
def contactShift (x a b c d : F) : MvPolynomial (Fin 5) F →ₐ[F] MvPolynomial (Fin 5) F :=
  aeval (shiftImages x a b c d)
theorem shift_preserves_weight (v : Fin 5 → ℕ) (hv1 : v 1=v 3) (hv2 : v 2=v 4)
    (x a b c d : F) (P : MvPolynomial (Fin 5) F) :
    (contactShift x a b c d P).weightedTotalDegree v≤P.weightedTotalDegree v := by
  apply weightedTotalDegree_aeval_le_of_le v v
  intro i
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  fin_cases i
  · change X 0+C x∈restrictWeightedDegree v (v 0)
    exact Submodule.add_mem _ (X_mem_restrictWeightedDegree v _ _ le_rfl)
      (C_mem_restrictWeightedDegree v _ _)
  · change X 1+C a+X 3*C b∈restrictWeightedDegree v (v 1)
    apply Submodule.add_mem _
      (Submodule.add_mem _ (X_mem_restrictWeightedDegree v _ _ le_rfl)
        (C_mem_restrictWeightedDegree v _ _))
    have hm := mul_mem_restrictWeightedDegree
      (X_mem_restrictWeightedDegree (R:=F) v (v 3) 3 le_rfl)
      (C_mem_restrictWeightedDegree (R:=F) v 0 b)
    simpa [hv1] using hm
  · change X 2+C c+X 4*C d∈restrictWeightedDegree v (v 2)
    apply Submodule.add_mem _
      (Submodule.add_mem _ (X_mem_restrictWeightedDegree v _ _ le_rfl)
        (C_mem_restrictWeightedDegree v _ _))
    have hm := mul_mem_restrictWeightedDegree
      (X_mem_restrictWeightedDegree (R:=F) v (v 4) 4 le_rfl)
      (C_mem_restrictWeightedDegree (R:=F) v 0 d)
    simpa [hv2] using hm
  · change X 3∈restrictWeightedDegree v (v 3)
    exact X_mem_restrictWeightedDegree v _ _ le_rfl
  · change X 4∈restrictWeightedDegree v (v 4)
    exact X_mem_restrictWeightedDegree v _ _ le_rfl
theorem contactShift_parameter_weights (x a b c d : F) (P : MvPolynomial (Fin 5) F) :
    (contactShift x a b c d P).weightedTotalDegree (sourceWeights 1 2)≤
      P.weightedTotalDegree (sourceWeights 1 2) ∧
    (contactShift x a b c d P).weightedTotalDegree (sourceWeights 1 3)≤
      P.weightedTotalDegree (sourceWeights 1 3) := by
  constructor <;> apply shift_preserves_weight <;> decide
theorem trunc_mem_jet_of_parameters (d s t : ℕ) (P : MvPolynomial (Fin 5) F)
    (hS : P.weightedTotalDegree (sourceWeights 1 2)≤s)
    (hT : P.weightedTotalDegree (sourceWeights 1 3)≤t) :
    weightedTruncation contactWeight (d+1) P∈JetSpace F d s t := by
  simp only [JetSpace]
  rw [source_filtered_eq,mem_restrictSupport_iff]
  intro e he
  have hc : e.weight contactWeight<d+1 := by
    have hh := mem_support_iff.mp he
    rw [coeff_weightedTruncation] at hh
    by_contra hn
    exact hh (if_neg hn)
  have heP : e∈P.support := by
    apply mem_support_iff.mpr
    have := mem_support_iff.mp he
    simpa only [coeff_weightedTruncation,if_pos hc] using this
  have hs := (le_weightedTotalDegree (sourceWeights 1 2) heP).trans hS
  have ht := (le_weightedTotalDegree (sourceWeights 1 3) heP).trans hT
  apply (mem_sourceExponents d 1 d s t e).mpr
  simp [sourceWeights,contactWeight,weight5] at hc hs ht ⊢
  omega
def sourceToJet (D w B s t d : ℕ) (x a b c e : F) :
    filtered (F:=F) (sourceWeights w) (sourceBounds D B s t) →ₗ[F] JetSpace F d s t where
  toFun Q := ⟨weightedTruncation contactWeight (d+1) (contactShift x a b c e Q.val),by
    apply trunc_mem_jet_of_parameters
    · exact (contactShift_parameter_weights x a b c e Q.val).1.trans
        ((mem_filtered _ _ _).mp Q.property 2)
    · exact (contactShift_parameter_weights x a b c e Q.val).2.trans
        ((mem_filtered _ _ _).mp Q.property 3)⟩
  map_add' Q R := by apply Subtype.ext; simp
  map_smul' a Q := by apply Subtype.ext; simp
end
end K1_11
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace K1_11
noncomputable section
open MvPolynomial Polynomial
variable {F : Type*} [Field F]
theorem contact_mod_relation_pullback {σ : Type*} (v : σ → ℕ) (m : ℕ)
    (P L H : MvPolynomial σ F) (g : σ → F[X]) (z : F[X])
    (hcontact : P-L*H∈restrictWeightedOrder v m)
    (hg : ∀ i,z^(v i) ∣ g i)
    (hL : eval₂Hom Polynomial.C g L=0) :
    z^m ∣ eval₂Hom Polynomial.C g P := by
  have hd := pow_dvd_eval₂Hom_of_mem_restrictWeightedOrder Polynomial.C hcontact hg
  simpa only [map_sub,map_mul,hL,zero_mul,sub_zero] using hd
end
end K1_11
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace K1_11
noncomputable section
open MvPolynomial Finset
variable {F : Type*} [Field F]
def decoderImages (P Q : Polynomial F) (s t : F) : Fin 5 → Polynomial F :=
  ![Polynomial.X,P,Q,Polynomial.C s,Polynomial.C t]
def contactDecoderImages (x a b c d s t : F) (P Q : Polynomial F) : Fin 5 → Polynomial F :=
  ![Polynomial.X-Polynomial.C x,P-Polynomial.C (a+s*b),
    Q-Polynomial.C (c+t*d),Polynomial.C s,Polynomial.C t]
theorem decoder_contact_composition (x a b c d s t : F) (P Q : Polynomial F)
    (G : MvPolynomial (Fin 5) F) :
    aeval (contactDecoderImages x a b c d s t P Q) (contactShift x a b c d G)=
      aeval (decoderImages P Q s t) G := by
  rw [contactShift,aeval_eq_bind₁,aeval_bind₁]
  have hf : (fun i => aeval (contactDecoderImages x a b c d s t P Q) (shiftImages x a b c d i))=decoderImages P Q s t := by
    funext i
    fin_cases i <;> simp [shiftImages,contactDecoderImages,decoderImages] <;> ring
  rw [hf]
theorem contactDecoderImages_vanish (x a b c d s t : F) (P Q : Polynomial F)
    (hP : P.eval x=a+s*b) (hQ : Q.eval x=c+t*d) :
    ∀ i,(Polynomial.X-Polynomial.C x)^contactWeight i∣
      contactDecoderImages x a b c d s t P Q i := by
  have hp : (Polynomial.X-Polynomial.C x)∣P-Polynomial.C (a+s*b) := by
    apply Polynomial.dvd_iff_isRoot.mpr
    simp [hP]
  have hq : (Polynomial.X-Polynomial.C x)∣Q-Polynomial.C (c+t*d) := by
    apply Polynomial.dvd_iff_isRoot.mpr
    simp [hQ]
  simp only [Polynomial.C_add,Polynomial.C_mul] at hp hq
  intro i
  fin_cases i <;> simp [contactWeight,contactDecoderImages,hp,hq]
theorem decoder_contact_multiplicity (m : ℕ) (x a b c d s t : F)
    (P Q : Polynomial F) (G L H : MvPolynomial (Fin 5) F)
    (hP : P.eval x=a+s*b) (hQ : Q.eval x=c+t*d)
    (hL : aeval (decoderImages P Q s t) L=0)
    (hcontact : contactShift x a b c d G-contactShift x a b c d L*H∈
      restrictWeightedOrder contactWeight m) :
    (Polynomial.X-Polynomial.C x)^m∣aeval (decoderImages P Q s t) G := by
  have hh := contact_mod_relation_pullback contactWeight m
    (contactShift x a b c d G) (contactShift x a b c d L) H
    (contactDecoderImages x a b c d s t P Q) (Polynomial.X-Polynomial.C x)
    hcontact (contactDecoderImages_vanish x a b c d s t P Q hP hQ)
    (by
      change aeval (contactDecoderImages x a b c d s t P Q) (contactShift x a b c d L)=0
      rw [decoder_contact_composition]
      exact hL)
  change (Polynomial.X-Polynomial.C x)^m∣aeval (contactDecoderImages x a b c d s t P Q) (contactShift x a b c d G) at hh
  rwa [decoder_contact_composition] at hh
theorem decoder_eval_degree (w D : ℕ) (G : MvPolynomial (Fin 5) F)
    (hG : G.weightedTotalDegree (sourceWeights w 0)≤D)
    (P Q : Polynomial F) (hP : P.natDegree≤w) (hQ : Q.natDegree≤w) (s t : F) :
    (aeval (decoderImages P Q s t) G).natDegree≤D := by
  apply (natDegree_aeval_le_weightedTotalDegree_of_le (sourceWeights w 0)
    (decoderImages P Q s t) G ?_).trans hG
  intro i
  fin_cases i <;> simp [decoderImages,sourceWeights] <;> assumption
theorem eq_zero_of_many_contacts {ι : Type*} (S : Finset ι) (x : ι → F)
    (hx : Function.Injective x) (m : ℕ) (Q : Polynomial F)
    (hcontact : ∀ i∈S,(Polynomial.X-Polynomial.C (x i))^m∣Q)
    (hdeg : Q.natDegree<m*S.card) : Q=0 := by
  classical
  by_contra hQ
  have hp : (∏ i∈S,(Polynomial.X-Polynomial.C (x i))^m)∣Q := by
    apply Finset.prod_dvd_of_coprime
    · intro i hi j hj hij
      exact (Polynomial.pairwise_coprime_X_sub_C hx hij).pow
    · exact hcontact
  have hd := Polynomial.natDegree_le_of_dvd hp hQ
  have hne : ∀ i∈S,(Polynomial.X-Polynomial.C (x i))^m≠0 := by
    intro i hi
    exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
  rw [Polynomial.natDegree_prod _ _ hne] at hd
  simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C,Nat.mul_one,
    Finset.sum_const,smul_eq_mul] at hd
  nlinarith
end
end K1_11
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 500000
namespace K1_11
noncomputable section
open MvPolynomial
variable {F : Type*} [Field F]
def scalarEliminant (B : ℕ) (G : MvPolynomial (Fin 5) F)
    (a b : MvPolynomial (Fin 4) F) : MvPolynomial (Fin 4) F :=
  clearedEval B (polynomialView G) a b
theorem scalarEliminant_ne_zero (D w B s t : ℕ) (G L : MvPolynomial (Fin 5) F)
    (hG : G∈filtered (sourceWeights w) (sourceBounds D B s t))
    (hnot : ¬ L∣G) (a b : MvPolynomial (Fin 4) F) (hb : b≠0)
    (hlinear : polynomialView L=Polynomial.C b*Polynomial.X-Polynomial.C a)
    (hprimitive : (Polynomial.C b*Polynomial.X-Polynomial.C a).IsPrimitive) :
    scalarEliminant B G a b≠0 := by
  have hnd : ¬ (Polynomial.C b*Polynomial.X-Polynomial.C a)∣polynomialView G := by
    rintro ⟨H,hH⟩
    apply hnot
    refine ⟨polynomialView.symm H,?_⟩
    apply polynomialView.injective
    rw [map_mul,hlinear,AlgEquiv.apply_symm_apply]
    exact hH
  letI : GCDMonoid (MvPolynomial (Fin 4) F) := UniqueFactorizationMonoid.toGCDMonoid _
  exact clearedEval_ne_zero (K:=FractionRing (MvPolynomial (Fin 4) F)) B
    (polynomialView G) (polynomialView_natDegree D w B s t G hG) a b hb hprimitive hnd
theorem scalarEliminant_annihilates (D w B s t : ℕ) (G L : MvPolynomial (Fin 5) F)
    (hG : G∈filtered (sourceWeights w) (sourceBounds D B s t))
    (a b : MvPolynomial (Fin 4) F)
    (hlinear : polynomialView L=Polynomial.C b*Polynomial.X-Polynomial.C a)
    (P Q : Polynomial F) (s0 t0 : F)
    (hL : aeval (decoderImages P Q s0 t0) L=0)
    (hzero : aeval (decoderImages P Q s0 t0) G=0) :
    aeval (scalarImages P s0 t0) (scalarEliminant B G a b)=0 := by
  let φ : MvPolynomial (Fin 4) F →+* Polynomial F := (aeval (scalarImages P s0 t0)).toRingHom
  have hroot : Polynomial.eval Q ((polynomialView G).map φ)=0 := by
    rw [Polynomial.eval_map,polynomialView_eval]
    exact hzero
  have hrel : φ b*Q=φ a := by
    have hh := polynomialView_eval P Q s0 t0 L
    rw [hlinear] at hh
    have hz : Polynomial.eval₂ φ Q (Polynomial.C b*Polynomial.X-Polynomial.C a)=0 :=
      hh.trans hL
    apply sub_eq_zero.mp
    simpa only [Polynomial.eval₂_sub,Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_X] using hz
  have hd : ((polynomialView G).map φ).natDegree≤B :=
    Polynomial.natDegree_map_le.trans (polynomialView_natDegree D w B s t G hG)
  have hh := clearedEval_zero_of_root B ((polynomialView G).map φ) hd (φ a) (φ b) Q hrel hroot
  rw [← map_clearedEval] at hh
  exact hh
end
end K1_11
end
section
namespace Sol1.C42
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
variable {R : Type*} [CommRing R]
def sourceBalance : JetVariable 2 → ℤ
  | none => 1
  | some j => -(j.val : ℤ)
def localBalance : LocalVariable 2 → ℤ
  | none => 1
  | some none => -1
  | some (some j) => -((j.val : ℤ) + 1)
theorem localCorrection_balance :
    (localCorrection (R := R) 2).IsWeightedHomogeneous localBalance 0 := by
  rw [← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  rw [mem_weightedHomogeneousSubmodule]
  have hC := isWeightedHomogeneous_C localBalance ((-1 : R) ^ j.val)
  have hT := (isWeightedHomogeneous_X R localBalance (localT 2)).pow (j.val + 1)
  have hY := isWeightedHomogeneous_X R localBalance (localY j)
  simpa [localBalance, localT, localY, nsmul_eq_mul] using (hC.mul hT).mul hY
theorem origin_image_balance (v : JetVariable 2) :
    (unscaledLocalImage 2 (0 : R) 0 v).IsWeightedHomogeneous localBalance (sourceBalance v) := by
  have hX := isWeightedHomogeneous_X R localBalance
  rcases v with _ | j
  · simpa [unscaledLocalImage, sourceBalance, localBalance, localT] using hX (localT 2)
  · refine Fin.cases ?_ (fun i ↦ ?_) j
    · have hTE : (X (localT 2) * X (localE 2) : LocalPolynomial R 2).IsWeightedHomogeneous
          localBalance 0 := by
        simpa [localBalance, localT, localE, localAux] using (hX (localT 2)).mul (hX (localE 2))
      simpa [unscaledLocalImage, sourceBalance] using localCorrection_balance.add hTE
    · simpa [unscaledLocalImage, sourceBalance, localBalance, localY] using hX (localY i)
theorem origin_substitution_balance {Q : DifferentialPolynomial R 2} {g : ℤ}
    (hQ : Q.IsWeightedHomogeneous sourceBalance g) :
    (unscaledLocalSubstitution 2 0 0 Q).IsWeightedHomogeneous localBalance g :=
  hQ.bind₁ origin_image_balance
theorem origin_constraint_balance (m : ℕ) {Q : DifferentialPolynomial R 2} {g : ℤ}
    (hQ : Q.IsWeightedHomogeneous sourceBalance g) :
    (localConstraintAt m 0 0 Q).IsWeightedHomogeneous localBalance g :=
  (origin_substitution_balance hQ).weightedTruncation _ m
theorem column_balance (i : SourceIndex) :
    ((columns i).polynomial : DifferentialPolynomial R 2).IsWeightedHomogeneous sourceBalance
      ((i.2.val : ℤ) - e1 i.1 - 2 * e2 i.1) := by
  rw [SourceColumn.polynomial_eq_sourceMonomial]
  have h := sourceMonomial_isWeightedHomogeneous (R := R) sourceBalance
    (columns i).x (columns i).y₀ (columns i).higher
  convert h using 1
  simp [sourceBalance, columns, Fin.sum_univ_two]
  ring
theorem origin_coefficient_zero_of_balance_ne
    (m : ℕ) (i : SourceIndex) (row : LocalVariable 2 →₀ ℕ)
    (hne : row.weight localBalance ≠ (i.2.val : ℤ) - e1 i.1 - 2 * e2 i.1) :
    (localConstraintAt (R := R) m 0 0 (columns i).polynomial).coeff row = 0 :=
  (origin_constraint_balance m (column_balance i)).coeff_eq_zero row hne
theorem column_jet_homogeneous (i : SourceIndex) :
    ((columns i).polynomial : DifferentialPolynomial R 2).IsWeightedHomogeneous
      jetDegreeWeight i.1.1.val := by
  rw [SourceColumn.polynomial_eq_sourceMonomial]
  have h := sourceMonomial_isWeightedHomogeneous_jetDegreeWeight (R := R)
    (columns i).x (columns i).y₀ (columns i).higher
  have hdegree : (columns i).y₀ + ∑ j, (columns i).higher j = i.1.1.val := by
    simpa [columns, Fin.sum_univ_two, Nat.add_assoc] using jet_total i.1
  rw [hdegree] at h
  exact h
theorem origin_coefficient_zero_of_jet_ne
    (m : ℕ) (i : SourceIndex) (row : LocalVariable 2 →₀ ℕ)
    (hne : row.weight (localJetDegreeWeight 2) ≠ i.1.1.val) :
    (localConstraintAt (R := R) m 0 0 (columns i).polynomial).coeff row = 0 :=
  (localConstraintAt_isWeightedHomogeneous 0 (column_jet_homogeneous i)).coeff_eq_zero row hne
theorem origin_high_X_zero (m : ℕ) (i : SourceIndex) (hlarge : m ≤ (columns i).x) :
    localConstraintAt (R := R) m 0 0 (columns i).polynomial = 0 := by
  have hsource : (X (none : JetVariable 2) : DifferentialPolynomial R 2) ^ (columns i).x ∣
      (columns i).polynomial := by
    rw [SourceColumn.polynomial_eq_sourceMonomial, sourceMonomial]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hmap := map_dvd (unscaledLocalSubstitution 2 (0 : R) 0).toRingHom hsource
  change unscaledLocalSubstitution 2 0 0
      ((X (none : JetVariable 2)) ^ (columns i).x) ∣
    unscaledLocalSubstitution 2 0 0 (columns i).polynomial at hmap
  simp only [map_pow, unscaledLocalSubstitution_X, C_0, zero_add] at hmap
  obtain ⟨G, hG⟩ := hmap
  rw [localConstraintAt, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    projectLowContact, weightedTruncation_eq_zero_iff, hG]
  have hT := pow_mem_restrictWeightedOrder (R := R)
    (X_mem_restrictWeightedOrder (localContactWeight 2) (localT 2) le_rfl) (columns i).x
  have hrest : G ∈ restrictWeightedOrder (localContactWeight 2) 0 := by simp
  refine restrictWeightedOrder_anti _ ?_ (mul_mem_restrictWeightedOrder hT hrest)
  simpa only [localContactWeight_T, add_zero, one_mul, mul_one] using hlarge
end Sol1.C42
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K1_14
noncomputable section
open MvPolynomial Finset
variable {F : Type*} [Field F]
def graphExponent (p : ℕ) (e : Fin 2 →₀ ℕ) : ℕ := e 0+p*e 1
def frobeniusGraph (p : ℕ) : MvPolynomial (Fin 2) F →ₐ[F] Polynomial F :=
  aeval ![Polynomial.X,Polynomial.X^p]
theorem graphExponent_injOn (p : ℕ) (hp : 0<p) :
    Set.InjOn (graphExponent p) {e : Fin 2 →₀ ℕ | e 0<p} := by
  intro e he f hf h
  have hm := congrArg (fun n : ℕ => n%p) h
  simp only [graphExponent,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt he,Nat.mod_eq_of_lt hf] at hm
  have hmul : p*e 1=p*f 1 := by unfold graphExponent at h; omega
  have h1 : e 1=f 1 := Nat.eq_of_mul_eq_mul_left hp hmul
  ext i
  fin_cases i <;> assumption
theorem frobeniusGraph_monomial (p : ℕ) (e : Fin 2 →₀ ℕ) (a : F) :
    frobeniusGraph p (monomial e a)=Polynomial.monomial (graphExponent p e) a := by
  rw [frobeniusGraph,aeval_monomial]
  simp [Finsupp.prod_fintype,Fin.prod_univ_succ,graphExponent,← pow_mul,← pow_add,Polynomial.C_mul_X_pow_eq_monomial]
theorem frobeniusGraph_coeff (p : ℕ) (hp : 0<p) (Q : MvPolynomial (Fin 2) F)
    (hdegree : Q.degreeOf 0<p) (e : Fin 2 →₀ ℕ) (he : e∈Q.support) :
    (frobeniusGraph p Q).coeff (graphExponent p e)=Q.coeff e := by
  classical
  have hex : frobeniusGraph p Q=∑ f∈Q.support,Polynomial.monomial (graphExponent p f) (Q.coeff f) := by
    conv_lhs => rw [Q.as_sum]
    simp only [map_sum,frobeniusGraph_monomial]
  rw [hex,Polynomial.finsetSum_coeff]
  trans ((Polynomial.monomial (graphExponent p e) (Q.coeff e)).coeff (graphExponent p e))
  · apply Finset.sum_eq_single_of_mem e he
    intro f hf hfe
    rw [Polynomial.coeff_monomial,ite_eq_right]
    intro h
    apply hfe
    apply graphExponent_injOn p hp
    · exact (le_degreeOf_of_mem_support 0 hf).trans_lt hdegree
    · exact (le_degreeOf_of_mem_support 0 he).trans_lt hdegree
    · exact h
  · simp
theorem frobeniusGraph_ne_zero (p : ℕ) (hp : 0<p) (Q : MvPolynomial (Fin 2) F)
    (hQ : Q≠0) (hdegree : Q.degreeOf 0<p) : frobeniusGraph p Q≠0 := by
  obtain ⟨e,he⟩ := support_nonempty.mpr hQ
  intro hz
  have hh := frobeniusGraph_coeff p hp Q hdegree e he
  rw [hz,Polynomial.coeff_zero] at hh
  exact (mem_support_iff.mp he) hh.symm
theorem frobeniusGraph_degree (p a b : ℕ) (Q : MvPolynomial (Fin 2) F)
    (hA : Q.degreeOf 0≤a) (hB : Q.degreeOf 1≤b) :
    (frobeniusGraph p Q).natDegree≤a+p*b := by
  apply (natDegree_aeval_le_weightedTotalDegree ![Polynomial.X,Polynomial.X^p] Q).trans
  apply Finset.sup_le
  intro e he
  have h0 := (le_degreeOf_of_mem_support 0 he).trans hA
  have h1 := (le_degreeOf_of_mem_support 1 he).trans hB
  simp [Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_succ,smul_eq_mul]
  nlinarith
theorem frobenius_coefficient_exception_count (p a b : ℕ) (hp : 0<p)
    (Q : MvPolynomial (Fin 2) F) (hQ : Q≠0) (hA : Q.degreeOf 0≤a) (ha : a<p)
    (hB : Q.degreeOf 1≤b) (Γ : Finset F)
    (hΓ : ∀ γ∈Γ,MvPolynomial.eval ![γ,γ^p] Q=0) : Γ.card≤a+p*b := by
  have hn := frobeniusGraph_ne_zero p hp Q hQ (hA.trans_lt ha)
  have hcard : Γ.card≤(frobeniusGraph p Q).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro γ hγ
    apply (Polynomial.mem_roots hn).mpr
    have he : (frobeniusGraph p Q).eval γ=MvPolynomial.eval ![γ,γ^p] Q := by
      have hmap : (Polynomial.evalRingHom γ).comp (frobeniusGraph (F:=F) p).toRingHom=
          MvPolynomial.eval ![γ,γ^p] := by
        apply MvPolynomial.ringHom_ext
        · intro c
          simp [frobeniusGraph]
        · intro i
          fin_cases i <;> simp [frobeniusGraph]
      exact RingHom.congr_fun hmap Q
    change (frobeniusGraph p Q).eval γ=0
    rw [he]
    exact hΓ γ hγ
  exact hcard.trans (frobeniusGraph_degree p a b Q hA hB)
end
end K1_14
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Strata
noncomputable section
open Finset MvPolynomial
open scoped BigOperators
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
end
end FrobeniusLocator.Strata
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K1_10
noncomputable section
open MvPolynomial Finset
variable {F : Type*} [Field F]
def graphExponent (p : ℕ) (e : Fin 2 →₀ ℕ) : ℕ := e 0+p*e 1
def frobeniusGraph (p : ℕ) : MvPolynomial (Fin 2) F →ₐ[F] Polynomial F :=
  aeval ![Polynomial.X,Polynomial.X^p]
theorem graphExponent_injOn (p : ℕ) (hp : 0<p) :
    Set.InjOn (graphExponent p) {e : Fin 2 →₀ ℕ | e 0<p} := by
  intro e he f hf h
  have hm := congrArg (fun n : ℕ => n%p) h
  simp only [graphExponent,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt he,Nat.mod_eq_of_lt hf] at hm
  have hmul : p*e 1=p*f 1 := by unfold graphExponent at h; omega
  have h1 : e 1=f 1 := Nat.eq_of_mul_eq_mul_left hp hmul
  ext i
  fin_cases i <;> assumption
theorem frobeniusGraph_monomial (p : ℕ) (e : Fin 2 →₀ ℕ) (a : F) :
    frobeniusGraph p (monomial e a)=Polynomial.monomial (graphExponent p e) a := by
  rw [frobeniusGraph,aeval_monomial]
  simp [Finsupp.prod_fintype,Fin.prod_univ_succ,graphExponent,← pow_mul,← pow_add,Polynomial.C_mul_X_pow_eq_monomial]
theorem frobeniusGraph_coeff (p : ℕ) (hp : 0<p) (Q : MvPolynomial (Fin 2) F)
    (hdegree : Q.degreeOf 0<p) (e : Fin 2 →₀ ℕ) (he : e∈Q.support) :
    (frobeniusGraph p Q).coeff (graphExponent p e)=Q.coeff e := by
  classical
  have hex : frobeniusGraph p Q=∑ f∈Q.support,Polynomial.monomial (graphExponent p f) (Q.coeff f) := by
    conv_lhs => rw [Q.as_sum]
    simp only [map_sum,frobeniusGraph_monomial]
  rw [hex,Polynomial.finsetSum_coeff]
  trans ((Polynomial.monomial (graphExponent p e) (Q.coeff e)).coeff (graphExponent p e))
  · apply Finset.sum_eq_single_of_mem e he
    intro f hf hfe
    have hdistinct : graphExponent p f ≠ graphExponent p e := by
      intro h
      apply hfe
      apply graphExponent_injOn p hp
      · exact (le_degreeOf_of_mem_support 0 hf).trans_lt hdegree
      · exact (le_degreeOf_of_mem_support 0 he).trans_lt hdegree
      · exact h
    simp [Polynomial.coeff_monomial, hdistinct]
  · simp
theorem frobeniusGraph_ne_zero (p : ℕ) (hp : 0<p) (Q : MvPolynomial (Fin 2) F)
    (hQ : Q≠0) (hdegree : Q.degreeOf 0<p) : frobeniusGraph p Q≠0 := by
  obtain ⟨e,he⟩ := support_nonempty.mpr hQ
  intro hz
  have hh := frobeniusGraph_coeff p hp Q hdegree e he
  rw [hz,Polynomial.coeff_zero] at hh
  exact (mem_support_iff.mp he) hh.symm
theorem frobeniusGraph_degree (p a b : ℕ) (Q : MvPolynomial (Fin 2) F)
    (hA : Q.degreeOf 0≤a) (hB : Q.degreeOf 1≤b) :
    (frobeniusGraph p Q).natDegree≤a+p*b := by
  apply (natDegree_aeval_le_weightedTotalDegree ![Polynomial.X,Polynomial.X^p] Q).trans
  apply Finset.sup_le
  intro e he
  have h0 := (le_degreeOf_of_mem_support 0 he).trans hA
  have h1 := (le_degreeOf_of_mem_support 1 he).trans hB
  simp [Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_succ,smul_eq_mul]
  nlinarith
theorem frobenius_coefficient_exception_count (p a b : ℕ) (hp : 0<p)
    (Q : MvPolynomial (Fin 2) F) (hQ : Q≠0) (hA : Q.degreeOf 0≤a) (ha : a<p)
    (hB : Q.degreeOf 1≤b) (Γ : Finset F)
    (hΓ : ∀ γ∈Γ,MvPolynomial.eval ![γ,γ^p] Q=0) : Γ.card≤a+p*b := by
  have hn := frobeniusGraph_ne_zero p hp Q hQ (hA.trans_lt ha)
  have hcard : Γ.card≤(frobeniusGraph p Q).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro γ hγ
    apply (Polynomial.mem_roots hn).mpr
    have he : (frobeniusGraph p Q).eval γ=MvPolynomial.eval ![γ,γ^p] Q := by
      have hmap : (Polynomial.evalRingHom γ).comp (frobeniusGraph (F:=F) p).toRingHom=
          MvPolynomial.eval ![γ,γ^p] := by
        apply MvPolynomial.ringHom_ext
        · intro c
          simp [frobeniusGraph]
        · intro i
          fin_cases i <;> simp [frobeniusGraph]
      exact RingHom.congr_fun hmap Q
    change (frobeniusGraph p Q).eval γ=0
    rw [he]
    exact hΓ γ hγ
  exact hcard.trans (frobeniusGraph_degree p a b Q hA hB)
end
end K1_10
end
section
namespace K1_14_2_2_4_4
noncomputable section
open IsLocalRing
theorem linear_length {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x f g : R} {n : ℕ} (hx : x ∈ maximalIdeal R)
    (hd : 1 < (maximalIdeal R).height)
    (hf : f ∈ (maximalIdeal R) ^ n ⊔ Ideal.span {x})
    (hg : g ∈ (maximalIdeal R) ^ n ⊔ Ideal.span {x}) :
    (n : ℕ∞) ≤ Module.length R (R ⧸ Ideal.span {f, g}) := by
  let m := maximalIdeal R
  let A : Ideal R := Ideal.span {x}
  let J (i : ℕ) := A ⊔ m ^ i
  have hno (i : ℕ) : ¬ m ^ i ≤ A := by
    intro h
    have hmin : m ∈ A.minimalPrimes := by
      refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem m).mpr hx⟩, ?_⟩
      intro P hP _
      exact fun z hz => hP.1.mem_of_pow_mem i (hP.2 (h (Ideal.pow_mem_pow hz i)))
    let _ : A.IsPrincipal := ⟨⟨x, rfl⟩⟩
    exact (not_le_of_gt hd)
      (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing A hmin)
  have hstep (i : ℕ) : J (i + 1) < J i := by
    refine lt_of_le_of_ne (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.le_succ i)) _) ?_
    intro he
    apply hno i
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := m) (IsNoetherian.noetherian _)
    · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    · change m ^ i ≤ A ⊔ m • m ^ i
      rw [smul_eq_mul, ← pow_succ']
      change m ^ i ≤ J (i + 1)
      rw [he]
      exact le_sup_right
  have hlength (i : ℕ) : (i : ℕ∞) ≤ Order.coheight (J i : Submodule R R) := by
    induction i with
    | zero => simp
    | succ i ih =>
        rw [Nat.cast_succ]
        exact (add_le_add_left ih 1).trans
          (Order.coheight_add_one_le (show (J (i + 1) : Submodule R R) < J i from hstep i))
  rw [Module.length_quotient]
  apply (hlength n).trans
  apply Order.coheight_anti
  apply Ideal.span_le.mpr
  simpa [J, A, m, Set.insert_subset_iff, Set.singleton_subset_iff, sup_comm] using And.intro hf hg
def triangle : ℕ → ℕ
  | 0 => 0
  | k + 1 => triangle k + (k + 1)
theorem two_mul_triangle (k : ℕ) : 2 * triangle k = k * (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change 2 * (triangle k + (k + 1)) = (k + 1) * (k + 1 + 1)
      nlinarith
theorem triangle_truncation (k : ℕ) :
    triangle (k + k + 1) = (k + 1) ^ 2 + (triangle k + triangle k) := by
  have h := two_mul_triangle k
  have H := two_mul_triangle (k + k + 1)
  nlinarith
def multiplyToQuotient {R : Type*} [CommRing R] (A B : Ideal R) (x : R)
    (hx : ∀ r ∈ A, r * x ∈ B) : (R ⧸ A) →ₗ[R] (R ⧸ B) :=
  A.liftQ ((LinearMap.id : R →ₗ[R] R).smulRight (Ideal.Quotient.mk B x)) (by
    intro r hr
    simpa [Algebra.smul_def, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] using hx r hr)
theorem multiplyToQuotient_mk {R : Type*} [CommRing R] (A B : Ideal R) (x : R)
    (hx : ∀ r ∈ A, r * x ∈ B) (r : R) :
    multiplyToQuotient A B x hx (Ideal.Quotient.mk A r) = Ideal.Quotient.mk B (r * x) := by
  change r • Ideal.Quotient.mk B x = _
  simp [Algebra.smul_def]
theorem square_length_of_hilbert {R : Type*} [CommRing R] (m : Ideal R)
    (hh : ∀ i, Module.length R (R ⧸ m ^ i) = (triangle i : ℕ∞))
    {f g : R} {n : ℕ} (hn : 0 < n) (hf : f ∈ m ^ n) (hg : g ∈ m ^ n) :
    (↑(n ^ 2 : ℕ) : ℕ∞) ≤ Module.length R (R ⧸ Ideal.span {f, g}) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let T := m ^ (k + k + 1)
  let J : Ideal R := Ideal.span {f, g}
  have hmul (x : R) (hx : x ∈ m ^ (k + 1)) (r : R) (hr : r ∈ m ^ k) :
      r * x ∈ T := by
    have h := Ideal.mul_mem_mul hr hx
    rwa [← pow_add, ← Nat.add_assoc] at h
  let F := multiplyToQuotient (m ^ k) T f (hmul f hf)
  let G := multiplyToQuotient (m ^ k) T g (hmul g hg)
  let H := LinearMap.coprod F G
  let q := Submodule.factor (show (T : Submodule R R) ≤ T ⊔ J from le_sup_left)
  have hker : LinearMap.ker q = LinearMap.range H := by
    ext z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    change Ideal.Quotient.mk (T ⊔ J) z = 0 ↔ Ideal.Quotient.mk T z ∈ LinearMap.range H
    rw [Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · rintro hz
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
      obtain ⟨c, d, rfl⟩ := Ideal.mem_span_pair.mp hb
      refine ⟨(Ideal.Quotient.mk _ c, Ideal.Quotient.mk _ d), ?_⟩
      simp [H, F, G, multiplyToQuotient_mk, map_add,
        Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    · rintro ⟨⟨c, d⟩, he⟩
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d
      have he' : Ideal.Quotient.mk T (c * f + d * g) = Ideal.Quotient.mk T z := by
        simpa [H, F, G, multiplyToQuotient_mk, map_add] using he
      rw [Ideal.Quotient.eq] at he'
      have hz : z = (-(c * f + d * g - z)) + (c * f + d * g) := by ring
      rw [hz]
      exact (T ⊔ J).add_mem (Ideal.mem_sup_left (T.neg_mem he'))
        (Ideal.mem_sup_right (Ideal.mem_span_pair.mpr ⟨c, d, rfl⟩))
  have hq := Module.length_eq_add_of_exact (LinearMap.ker q).subtype q
    (Submodule.subtype_injective _) (Submodule.factor_surjective _)
    (LinearMap.exact_subtype_ker_map q)
  have hsmall := Module.length_le_of_surjective H.rangeRestrict H.surjective_rangeRestrict
  rw [← hker, Module.length_prod, hh] at hsmall
  have hsum : (↑((k + 1) ^ 2 : ℕ) : ℕ∞) + ((triangle k : ℕ∞) + triangle k) ≤
      Module.length R (R ⧸ (T ⊔ J : Ideal R)) + ((triangle k : ℕ∞) + triangle k) := by
    rw [← Nat.cast_add, ← Nat.cast_add, ← triangle_truncation, ← hh]
    change Module.length R (R ⧸ T) ≤ _
    rw [hq, Nat.cast_add, add_comm (Module.length R ↥(LinearMap.ker q))]
    exact add_le_add_right hsmall _
  exact ((ENat.add_le_add_iff_right (by rw [← Nat.cast_add]; exact ENat.natCast_ne_top _)).mp hsum).trans
    (Module.length_le_of_surjective (Submodule.factor (show J ≤ T ⊔ J from le_sup_right))
      (Submodule.factor_surjective _))
end
end K1_14_2_2_4_4
end
section
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Strata
noncomputable section
open Finset Matrix MvPolynomial
open scoped BigOperators
variable {F ν c : Type} [Field F] [Fintype c] [DecidableEq c]
end
end FrobeniusLocator.Strata
end
section
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
        rw [MvPolynomial.X, weightedTotalDegree_monomial _ _ 1 one_ne_zero]
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
end
section
namespace Astra7
open MvPolynomial
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 4000
variable {F σ ι : Type*} [Field F] [IsAlgClosed F] [Finite σ] [Fintype ι]
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
end
section
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
end
section
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
def degreeLift (w : σ → ℕ) : MvPolynomial σ R →+* Polynomial (MvPolynomial σ R) :=
  (MvPolynomial.optionEquivLeft R σ).toRingHom.comp (weightedLift w)
theorem natDegree_degreeLift (w : σ → ℕ) (p : MvPolynomial σ R) :
    (degreeLift w p).natDegree = p.weightedTotalDegree w := by
  change (MvPolynomial.optionEquivLeft R σ (weightedLift w p)).natDegree = _
  rw [MvPolynomial.natDegree_optionEquivLeft, degreeOf_weightedLift]
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
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace FrobeniusLocator.Strata
noncomputable section
open Finset MvPolynomial
open scoped BigOperators
local instance agDecidable (P : Prop) : Decidable P := Classical.propDecidable P
variable {F K ν : Type} [Field F] [Field K] [Algebra F K] [Finite ν]
end
end FrobeniusLocator.Strata
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Strata
noncomputable section
open Finset MvPolynomial
open scoped BigOperators
variable {F K ν : Type} [Field F] [Field K] [Algebra F K] [Finite ν]
local instance coverDecidable (P : Prop) : Decidable P := Classical.propDecidable P
end
end FrobeniusLocator.Strata
end
section
namespace K1_14_2_2_4_4
noncomputable section
open IsLocalRing
theorem length_of_colon {R : Type*} [CommRing R] (A B : Ideal R) (x : R)
    (h : ∀ r, r * x ∈ B ↔ r ∈ A) :
    Module.length R (R ⧸ B) =
      Module.length R (R ⧸ A) + Module.length R (R ⧸ (B ⊔ Ideal.span {x} : Ideal R)) := by
  let f := multiplyToQuotient A B x (fun r hr => (h r).mpr hr)
  let q := Submodule.factor (show (B : Submodule R R) ≤ B ⊔ Ideal.span {x} from le_sup_left)
  have hfi : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    apply eq_bot_iff.mpr
    intro u hu
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u
    change f (Ideal.Quotient.mk A u) = 0 at hu
    rw [show f (Ideal.Quotient.mk A u) = Ideal.Quotient.mk B (u * x) from
      multiplyToQuotient_mk _ _ _ _ _, Ideal.Quotient.eq_zero_iff_mem] at hu
    change Ideal.Quotient.mk A u = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((h u).mp hu)
  have hqf : Function.Exact f q := by
    apply LinearMap.exact_iff.mpr
    ext u
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u
    change Ideal.Quotient.mk (B ⊔ Ideal.span {x}) u = 0 ↔
      Ideal.Quotient.mk B u ∈ LinearMap.range f
    rw [Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · rintro hu
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hb
      refine ⟨Ideal.Quotient.mk A c, ?_⟩
      simp [f, multiplyToQuotient_mk, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, mul_comm]
    · rintro ⟨z, hz⟩
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
      have hz' := Ideal.Quotient.eq.mp
        (hz.symm.trans (multiplyToQuotient_mk A B x (fun r hr => (h r).mpr hr) z))
      have hs := (B ⊔ Ideal.span {x}).add_mem (Ideal.mem_sup_left hz')
        (Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr ⟨z, mul_comm _ _⟩))
      rwa [sub_add_cancel] at hs
  exact Module.length_eq_add_of_exact f q hfi (Submodule.factor_surjective _) hqf
theorem power_decompose {R : Type*} [CommRing R]
    {m X Y : Ideal R} (h : m = X ⊔ Y) (k : ℕ) :
    m ^ (k + 1) = X * m ^ k ⊔ Y ^ (k + 1) := by
  have hX : X ≤ m := h ▸ le_sup_left
  have hY : Y ≤ m := h ▸ le_sup_right
  induction k with
  | zero => simpa using h
  | succ k ih =>
      apply le_antisymm
      · calc
          m ^ (k + 1 + 1) = X * m ^ (k + 1) ⊔ Y * m ^ (k + 1) := by
            rw [pow_succ']
            exact (congrArg (fun I => I * m ^ (k + 1)) h).trans (Ideal.sup_mul _ _ _)
          _ = X * m ^ (k + 1) ⊔ (Y * (X * m ^ k) ⊔ Y ^ (k + 1 + 1)) := by
            congr 1
            conv_lhs => rw [ih]
            rw [Ideal.mul_sup, ← pow_succ']
          _ ≤ _ := by
            rw [← sup_assoc]
            apply sup_le_sup_right
            apply sup_le le_rfl
            rw [← mul_assoc, mul_comm Y X, mul_assoc, pow_succ']
            exact Ideal.mul_mono le_rfl (Ideal.mul_mono hY le_rfl)
      · apply sup_le
        · calc
            X * m ^ (k + 1) ≤ m * m ^ (k + 1) := Ideal.mul_mono hX le_rfl
            _ = m ^ (k + 1 + 1) := (pow_succ' _ _).symm
        · exact pow_le_pow_left' hY _
theorem quotient_length_two_generators {R : Type*} [CommRing R] [IsLocalRing R]
    [IsDomain R] {x y : R} (hx : x ≠ 0) (hprime : (Ideal.span {x} : Ideal R).IsPrime)
    (hy : y ∉ (Ideal.span {x} : Ideal R))
    (hmax : maximalIdeal R = (Ideal.span {x} : Ideal R) ⊔ Ideal.span {y}) (k : ℕ) :
    Module.length R (R ⧸ (maximalIdeal R) ^ k) = (triangle k : ℕ∞) := by
  let m := maximalIdeal R
  let X : Ideal R := Ideal.span {x}
  let Y : Ideal R := Ideal.span {y}
  have hxm : x ∈ m := by
    change x ∈ maximalIdeal R
    rw [hmax]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self x)
  have hym : y ∈ m := by
    change y ∈ maximalIdeal R
    rw [hmax]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self y)
  have hyY (i : ℕ) : y ^ i ∈ Y ^ i := Ideal.pow_mem_pow (Ideal.mem_span_singleton_self y) i
  have hpow (i : ℕ) : X ⊔ m ^ i = X ⊔ Y ^ i := by
    cases i with
    | zero => simp
    | succ i =>
        rw [power_decompose hmax, ← sup_assoc,
          sup_eq_left.mpr (Ideal.mul_le_left : X * m ^ i ≤ X)]
  have hcolonX (i : ℕ) (r : R) : r * x ∈ m ^ (i + 1) ↔ r ∈ m ^ i := by
    constructor
    · intro h
      rw [power_decompose hmax] at h
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h
      obtain ⟨c, hc, rfl⟩ := Ideal.mem_span_singleton_mul.mp ha
      rw [Ideal.span_singleton_pow] at hb
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hb
      have hbX : y ^ (i + 1) * d ∈ X := by
        rw [show y ^ (i + 1) * d = r * x - x * c by rw [← hab]; ring]
        apply X.sub_mem <;> exact Ideal.mem_span_singleton.mpr (by
          first | exact ⟨r, mul_comm _ _⟩ | exact ⟨c, rfl⟩)
      have hdX : d ∈ X := (hprime.mem_or_mem hbX).resolve_left
        (fun hp => hy (hprime.mem_of_pow_mem _ hp))
      obtain ⟨e, rfl⟩ := Ideal.mem_span_singleton.mp hdX
      have hr : r = c + y ^ (i + 1) * e := by
        apply mul_left_cancel₀ hx
        calc
          x * r = r * x := mul_comm _ _
          _ = x * c + y ^ (i + 1) * (x * e) := hab.symm
          _ = x * (c + y ^ (i + 1) * e) := by ring
      rw [hr]
      exact (m ^ i).add_mem hc ((m ^ i).mul_mem_right _
        (Ideal.pow_le_pow_right (Nat.le_succ i) (Ideal.pow_mem_pow hym _)))
    · intro hr
      rw [pow_succ]
      exact Ideal.mul_mem_mul hr hxm
  have hcolonY (i : ℕ) (r : R) :
      r * y ∈ X ⊔ Y ^ (i + 1) ↔ r ∈ X ⊔ Y ^ i := by
    constructor
    · intro h
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h
      rw [Ideal.span_singleton_pow] at hb
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hb
      have hh : (r - y ^ i * c) * y ∈ X := by
        have he : a = r * y - y ^ (i + 1) * c := eq_sub_of_add_eq hab
        convert ha using 1
        rw [he, pow_succ]
        ring
      exact (Submodule.mem_sup.mpr
        ⟨r - y ^ i * c, (hprime.mem_or_mem hh).resolve_right hy, y ^ i * c,
          (Y ^ i).mul_mem_right _ (hyY i), sub_add_cancel _ _⟩)
    · intro h
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp h
      rw [add_mul]
      have hbY : b * y ∈ Y ^ (i + 1) := by
        rw [pow_succ]
        exact Ideal.mul_mem_mul hb (Ideal.mem_span_singleton_self y)
      exact (X ⊔ Y ^ (i + 1)).add_mem (Ideal.mem_sup_left (X.mul_mem_right _ ha))
        (Ideal.mem_sup_right hbY)
  have hm_one : Module.length R (R ⧸ m) = 1 := by
    rw [Module.length_quotient]
    have hc : IsCoatom (m : Submodule R R) := Ideal.isMaximal_def.mp (maximalIdeal.isMaximal R)
    apply le_antisymm
    · apply (Order.coheight_le_coe_iff (n := 1)).mpr
      intro z hz
      rw [hc.2 z hz]
      simp
    · simpa using (Order.coheight_add_one_le hc.lt_top)
  have hYLength (i : ℕ) : Module.length R (R ⧸ (X ⊔ Y ^ i : Ideal R)) = (i : ℕ∞) := by
    induction i with
    | zero => simp
    | succ i ih =>
        have he : (X ⊔ Y ^ (i + 1)) ⊔ Y = m := by
          rw [sup_assoc, sup_eq_right.mpr (Ideal.pow_le_pow_right (show 1 ≤ i + 1 by omega)
            |>.trans_eq (pow_one Y)), ← hmax]
        rw [length_of_colon _ _ y (hcolonY i), ih, he, hm_one, Nat.cast_succ]
  induction k with
  | zero => simp [triangle]
  | succ k ih =>
      change Module.length R (R ⧸ m ^ (k + 1)) = _
      rw [length_of_colon _ _ x (hcolonX k), ih, sup_comm, hpow, hYLength, triangle]
      simp only [Nat.cast_add, Nat.cast_succ]
theorem regular_surface_hilbert {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [IsRegularLocalRing R] (hd : ringKrullDim R = 2) (i : ℕ) :
    Module.length R (R ⧸ (maximalIdeal R) ^ i) = (triangle i : ℕ∞) := by
  classical
  let m := maximalIdeal R
  have hdim : m.spanFinrank = 2 := by
    have h := (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).trans hd
    exact_mod_cast h
  have hfg : (m : Submodule R R).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  rw [hdim] at hs
  obtain ⟨x, y, _, rfl⟩ := Finset.card_eq_two.mp hs
  have hmax : m = (Ideal.span {x} : Ideal R) ⊔ Ideal.span {y} := by
    rw [← Ideal.span_insert]
    simpa only [Finset.coe_insert, Finset.coe_singleton] using hspan.symm
  have not_principal (z : R) : m ≠ Ideal.span {z} := by
    intro he
    have ht := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) (Set.finite_singleton z)
    change (Ideal.span {z}).spanFinrank ≤ _ at ht
    rw [← he, hdim, Set.ncard_singleton] at ht
    omega
  have hx : x ∈ m := hmax ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self x)
  have hy' : y ∉ (Ideal.span {x} : Ideal R) := fun hy =>
    not_principal x (hmax.trans (sup_eq_left.mpr (Ideal.span_singleton_le_iff_mem _ |>.mpr hy)))
  have hx' : x ∉ m ^ 2 := by
    intro h
    apply not_principal y
    apply le_antisymm _ (hmax ▸ le_sup_right)
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := m) (IsNoetherian.noetherian _)
    · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    · rw [smul_eq_mul, ← pow_two]
      calc
        m = (Ideal.span {x} : Ideal R) ⊔ Ideal.span {y} := hmax
        _ ≤ _ := sup_le
          ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_sup_right h)) le_sup_left
  have hp : Prime x := irreducible_iff_prime.mp
    ⟨(mem_maximalIdeal _).mp hx, fun a b hab => by
      by_contra! hn
      apply hx'
      simpa [← hab, pow_two] using Ideal.mul_mem_mul
        ((mem_maximalIdeal _).mpr hn.1) ((mem_maximalIdeal _).mpr hn.2)⟩
  exact quotient_length_two_generators hp.ne_zero ((Ideal.span_singleton_prime hp.ne_zero).mpr hp) hy' hmax i
end
end K1_14_2_2_4_4
end
section
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
end
section
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
end
section
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
theorem origin_rank_le_low_columns :
    (pointMatrix (F := F) 48 0 0).rank ≤
      ((pointMatrix (F := F) 48 0 0).submatrix id colOriginal).rank := by
  apply rank_le_col_representatives
  intro j
  by_cases hx : j.2.val < 48
  · obtain ⟨c,hc⟩ := low_column_represented j hx
    exact Or.inr ⟨c,by rw [hc]⟩
  · exact Or.inl (high_column_zero j (by omega))
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
theorem origin_rank : (pointMatrix (F := F) 48 0 0).rank ≤ blockUpper :=
  origin_rank_le_low_columns.trans (low_columns_rank_le_finite.trans finiteMatrix_rank)
end
end Sol1.C52
end
section
namespace Sol1.Reciprocal
open Polynomial
variable {F K : Type*} [Field F] [Field K]
theorem descends_of_many_values (phi : F →+* K) (S : Finset F)
    (f : Polynomial K) (w : F → F) (k : ℕ)
    (hf : f.natDegree ≤ k) (hcard : k < S.card)
    (heval : ∀ x ∈ S, f.eval (phi x) = phi (w x)) :
    ∃ P : Polynomial F, P.map phi = f ∧ P.natDegree ≤ k ∧
      ∀ x ∈ S, P.eval x = w x := by
  classical
  let P : Polynomial F := Lagrange.interpolate S id w
  have hnodes : Set.InjOn (id : F → F) S := fun _ _ _ _ h => h
  have hP : P.degree < (S.card : WithBot ℕ) :=
    Lagrange.degree_interpolate_lt w hnodes
  have hmap : (P.map phi).degree < (S.card : WithBot ℕ) :=
    lt_of_le_of_lt Polynomial.degree_map_le hP
  have hdeg : f.degree < (S.card : WithBot ℕ) := by
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    exact_mod_cast lt_of_le_of_lt hf hcard
  have hphi : Set.InjOn (fun x : F => phi x) S :=
    fun _ _ _ _ h => phi.injective h
  have heq : P.map phi = f := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq S hphi hmap hdeg
    intro x hx
    rw [Polynomial.eval_map_apply, heval x hx]
    congr 1
    exact Lagrange.eval_interpolate_at_node w hnodes hx
  refine ⟨P, heq, ?_, ?_⟩
  · have hnat := congrArg Polynomial.natDegree heq
    rw [Polynomial.natDegree_map_eq_of_injective phi.injective] at hnat
    omega
  · intro x hx
    exact Lagrange.eval_interpolate_at_node w hnodes hx
theorem eq_of_eval_on_base (phi : F →+* K) (S : Finset F)
    (f g : Polynomial K)
    (heval : ∀ x ∈ S, f.eval (phi x) = g.eval (phi x))
    (hcard : max f.natDegree g.natDegree < S.card) : f = g := by
  classical
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq' _ _ (S.image phi)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact heval x hx
  · simpa only [Finset.card_image_of_injective S phi.injective] using hcard
theorem linear_mul_add_const_degree (h : Polynomial K) (alpha gamma : K)
    (k : ℕ) (hh : h.natDegree < k) :
    ((X-C alpha)*h+C gamma).natDegree ≤ k := by
  have hm := Polynomial.natDegree_mul_le (p := X-C alpha) (q := h)
  have ha := Polynomial.natDegree_add_le ((X-C alpha)*h) (C gamma)
  simp only [Polynomial.natDegree_X_sub_C, Polynomial.natDegree_C] at hm ha
  omega
theorem pole_direction_never_extends (phi : F →+* K) (S : Finset F)
    (alpha : K) (k : ℕ) (hcard : k < S.card)
    (halpha : ∀ x ∈ S, phi x ≠ alpha) :
    ¬ ∃ g : Polynomial K, g.natDegree < k ∧
      ∀ x ∈ S, g.eval (phi x) = -1/(phi x-alpha) := by
  rintro ⟨g, hg, heval⟩
  let f : Polynomial K := (X-C alpha)*g+C 1
  have hdegree : f.natDegree ≤ k := linear_mul_add_const_degree g alpha 1 k hg
  have hzero : f = 0 := by
    apply eq_of_eval_on_base phi S f 0
    · intro x hx
      have hden : phi x-alpha ≠ 0 := sub_ne_zero.mpr (halpha x hx)
      simp only [f, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_zero, heval x hx]
      field_simp
      ring
    · simpa only [Polynomial.natDegree_zero, max_eq_left (Nat.zero_le _)] using
        lt_of_le_of_lt hdegree hcard
  have hbad := congrArg (fun q : Polynomial K => q.eval alpha) hzero
  have : (1 : K) = 0 := by simpa [f] using hbad
  exact one_ne_zero this
theorem pole_decoder_iff_base_polynomial (phi : F →+* K) (S : Finset F)
    (w : F → F) (alpha gamma : K) (k : ℕ) (hk : 0 < k)
    (hcard : k < S.card) (halpha : ∀ x ∈ S, phi x ≠ alpha) :
    (∃ h : Polynomial K, h.natDegree < k ∧
      ∀ x ∈ S, h.eval (phi x) = (phi (w x)-gamma)/(phi x-alpha)) ↔
    ∃ P : Polynomial F, P.natDegree ≤ k ∧
      (∀ x ∈ S, P.eval x = w x) ∧ (P.map phi).eval alpha = gamma := by
  constructor
  · rintro ⟨h, hh, heval⟩
    let f : Polynomial K := (X-C alpha)*h+C gamma
    have hf : f.natDegree ≤ k := linear_mul_add_const_degree h alpha gamma k hh
    have he : ∀ x ∈ S, f.eval (phi x) = phi (w x) := by
      intro x hx
      have hden : phi x-alpha ≠ 0 := sub_ne_zero.mpr (halpha x hx)
      simp only [f, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, heval x hx]
      field_simp
      ring
    obtain ⟨P, hmap, hP, hvalues⟩ := descends_of_many_values phi S f w k hf hcard he
    refine ⟨P, hP, hvalues, ?_⟩
    rw [hmap]
    simp [f]
  · rintro ⟨P, hP, hvalues, hgamma⟩
    have hroot : Polynomial.IsRoot (P.map phi-C gamma) alpha := by
      simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C,
        hgamma, sub_self]
    obtain ⟨h, hfactor⟩ := (Polynomial.dvd_iff_isRoot.mpr hroot)
    have hdegree : (P.map phi-C gamma).natDegree ≤ k := by
      apply le_trans (Polynomial.natDegree_sub_le _ _)
      apply max_le
      · exact le_trans Polynomial.natDegree_map_le hP
      · simp
    have hh : h.natDegree < k := by
      by_cases hz : h = 0
      · simpa [hz] using hk
      · rw [hfactor, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero alpha) hz,
          Polynomial.natDegree_X_sub_C] at hdegree
        omega
    refine ⟨h, hh, ?_⟩
    intro x hx
    have hden : phi x-alpha ≠ 0 := sub_ne_zero.mpr (halpha x hx)
    have he := congrArg (fun q : Polynomial K => q.eval (phi x)) hfactor
    simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_map_apply, hvalues x hx] at he
    apply (eq_div_iff hden).mpr
    simpa only [mul_comm] using he.symm
open Classical in
def baseCloseSet (D : Finset F) (w : F → F) (k A : ℕ) : Set (Polynomial F) :=
  {P | P.natDegree ≤ k ∧ A ≤ (D.filter fun x => P.eval x = w x).card}
def poleMCASet (phi : F →+* K) (D : Finset F) (w : F → F)
    (alpha : K) (k A : ℕ) : Set K :=
  {gamma | ∃ S : Finset F, S ⊆ D ∧ A ≤ S.card ∧
    (∃ h : Polynomial K, h.natDegree < k ∧
      ∀ x ∈ S, h.eval (phi x) = (phi (w x)-gamma)/(phi x-alpha)) ∧
    ¬ ∃ u v : Polynomial K, u.natDegree < k ∧ v.natDegree < k ∧
      ∀ x ∈ S, u.eval (phi x) = phi (w x)/(phi x-alpha) ∧
        v.eval (phi x) = -1/(phi x-alpha)}
theorem pole_MCA_set_eq_evaluation_image (phi : F →+* K) (D : Finset F)
    (w : F → F) (alpha : K) (k A : ℕ) (hk : 0 < k) (hkA : k < A)
    (halpha : ∀ x ∈ D, phi x ≠ alpha) :
    poleMCASet phi D w alpha k A =
      (fun P : Polynomial F => (P.map phi).eval alpha) '' baseCloseSet D w k A := by
  classical
  ext gamma
  constructor
  · rintro ⟨S, hSD, hAS, hdecode, _hnonaligned⟩
    obtain ⟨P, hP, hvalues, hgamma⟩ :=
      (pole_decoder_iff_base_polynomial phi S w alpha gamma k hk
        (lt_of_lt_of_le hkA hAS) (fun x hx => halpha x (hSD hx))).mp hdecode
    refine ⟨P, ⟨hP, ?_⟩, hgamma⟩
    apply le_trans hAS
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_filter.mpr ⟨hSD hx, hvalues x hx⟩
  · rintro ⟨P, ⟨hP, hcount⟩, hgamma⟩
    let S : Finset F := D.filter fun x => P.eval x = w x
    have hSD : S ⊆ D := Finset.filter_subset _ _
    have hAS : A ≤ S.card := hcount
    have hcard : k < S.card := lt_of_lt_of_le hkA hAS
    have halphaS : ∀ x ∈ S, phi x ≠ alpha := fun x hx => halpha x (hSD hx)
    have hvalues : ∀ x ∈ S, P.eval x = w x :=
      fun x hx => (Finset.mem_filter.mp hx).2
    have hdecode := (pole_decoder_iff_base_polynomial phi S w alpha gamma k hk
      hcard halphaS).mpr ⟨P, hP, hvalues, hgamma⟩
    refine ⟨S, hSD, hAS, hdecode, ?_⟩
    rintro ⟨u, v, _hu, hv, hboth⟩
    apply pole_direction_never_extends phi S alpha k hcard halphaS
    exact ⟨v, hv, fun x hx => (hboth x hx).2⟩
theorem exists_injective_evaluation (S : Finset (Polynomial K))
    (T : Finset K) (k : ℕ) (hdegree : ∀ f ∈ S, f.natDegree ≤ k)
    (hsize : k*S.card^2 < T.card) :
    ∃ alpha ∈ T, Set.InjOn (fun f : Polynomial K => f.eval alpha) S := by
  classical
  let J : Finset (Polynomial K × Polynomial K) :=
    (S.product S).filter fun fg => fg.1 ≠ fg.2
  let Q : Polynomial K := ∏ fg ∈ J, (fg.1-fg.2)
  have hfactor : ∀ fg ∈ J, fg.1-fg.2 ≠ 0 := by
    intro fg hfg
    exact sub_ne_zero.mpr (Finset.mem_filter.mp hfg).2
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr hfactor
  have hJ : J.card ≤ S.card*S.card := by
    exact le_trans (Finset.card_filter_le _ _)
      (by rw [Finset.product_eq_sprod, Finset.card_product])
  have hQdegree : Q.natDegree ≤ k*S.card^2 := by
    apply le_trans (Polynomial.natDegree_prod_le J (fun fg => fg.1-fg.2))
    calc
      (∑ fg ∈ J, (fg.1-fg.2).natDegree) ≤ ∑ _fg ∈ J, k := by
        apply Finset.sum_le_sum
        intro fg hfg
        have hm := Finset.mem_product.mp (Finset.mem_filter.mp hfg).1
        exact le_trans (Polynomial.natDegree_sub_le _ _)
          (max_le (hdegree _ hm.1) (hdegree _ hm.2))
      _ = J.card*k := by simp
      _ ≤ (S.card*S.card)*k := Nat.mul_le_mul_right k hJ
      _ = k*S.card^2 := by ring
  obtain ⟨alpha, hT, hnonzero⟩ : ∃ alpha ∈ T, Q.eval alpha ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    exact hQ (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Q T
      hnone (lt_of_le_of_lt hQdegree hsize))
  refine ⟨alpha, hT, ?_⟩
  intro f hf g hg heval
  by_contra hne
  have hfg : (f,g) ∈ J := Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hf,hg⟩, hne⟩
  have hprod : (∏ fg ∈ J, (fg.1-fg.2).eval alpha) ≠ 0 := by
    simpa only [Q, Polynomial.eval_prod] using hnonzero
  have hdiff := Finset.prod_ne_zero_iff.mp hprod (f,g) hfg
  exact hdiff (by simp only [Polynomial.eval_sub, heval, sub_self])
theorem native_evaluation_separation_budget :
    262144 + 131072*(7*262144^3+1)^2 < (2130706433 : ℕ)^6 := by norm_num
end Sol1.Reciprocal
end
section
namespace Sol1.Reciprocal
open Polynomial
variable {F K : Type*} [Field F] [Field K] [Fintype K]
open Classical in
theorem finset_card_le_of_pole_cap
    (phi : F →+* K) (D : Finset F) (w : F → F) (k A B : ℕ)
    (hk : 0 < k) (hkA : k < A)
    (P : Finset (Polynomial F)) (hP : (P : Set (Polynomial F)) ⊆ baseCloseSet D w k A)
    (hroom : D.card + k * P.card ^ 2 < Fintype.card K)
    (hcap : ∀ alpha : K, (∀ x ∈ D, phi x ≠ alpha) →
      (poleMCASet phi D w alpha k A).ncard ≤ B) :
    P.card ≤ B := by
  classical
  let mapped : Finset (Polynomial K) := P.image (Polynomial.map phi)
  let candidates : Finset K := Finset.univ \ D.image phi
  have hmapinj : Function.Injective (Polynomial.map phi) :=
    Polynomial.map_injective phi phi.injective
  have hmapped : mapped.card = P.card := Finset.card_image_of_injective P hmapinj
  have hcandidates : candidates.card = Fintype.card K - D.card := by
    dsimp [candidates]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Finset.card_image_of_injective D phi.injective]
  have hdegree : ∀ f ∈ mapped, f.natDegree ≤ k := by
    intro f hf
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hf
    exact Polynomial.natDegree_map_le.trans (hP hq).1
  have hsize : k * mapped.card ^ 2 < candidates.card := by
    rw [hmapped, hcandidates]
    omega
  obtain ⟨alpha, halpha, hinj⟩ :=
    exists_injective_evaluation mapped candidates k hdegree hsize
  have houtside : ∀ x ∈ D, phi x ≠ alpha := by
    intro x hx heq
    have hnot : alpha ∉ D.image phi := (Finset.mem_sdiff.mp halpha).2
    exact hnot (Finset.mem_image.mpr ⟨x, hx, heq⟩)
  have hinjP : Set.InjOn (fun q : Polynomial F ↦ (q.map phi).eval alpha) P := by
    intro q hq r hr heq
    apply hmapinj
    exact hinj (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
      (Finset.mem_image.mpr ⟨r, hr, rfl⟩) heq
  have hmaps : ∀ q ∈ (P : Set (Polynomial F)),
      (q.map phi).eval alpha ∈ poleMCASet phi D w alpha k A := by
    intro q hq
    rw [pole_MCA_set_eq_evaluation_image phi D w alpha k A hk hkA houtside]
    exact ⟨q, hP hq, rfl⟩
  have hcount := Set.ncard_le_ncard_of_injOn
    (fun q : Polynomial F ↦ (q.map phi).eval alpha) hmaps hinjP
  have hcount' : P.card ≤ (poleMCASet phi D w alpha k A).ncard := by
    simpa only [Set.ncard_coe_finset] using hcount
  exact hcount'.trans (hcap alpha houtside)
open Classical in
theorem every_finset_card_le_of_pole_cap
    (phi : F →+* K) (D : Finset F) (w : F → F) (k A B : ℕ)
    (hk : 0 < k) (hkA : k < A)
    (hroom : D.card + k * (B + 1) ^ 2 < Fintype.card K)
    (hcap : ∀ alpha : K, (∀ x ∈ D, phi x ≠ alpha) →
      (poleMCASet phi D w alpha k A).ncard ≤ B)
    (P : Finset (Polynomial F)) (hP : (P : Set (Polynomial F)) ⊆ baseCloseSet D w k A) :
    P.card ≤ B := by
  by_contra hlarge
  have hsize : B + 1 ≤ P.card := by omega
  obtain ⟨Q, hQP, hQcard⟩ := Finset.exists_subset_card_eq hsize
  have hQ := finset_card_le_of_pole_cap phi D w k A B hk hkA Q
    (fun q hq ↦ hP (hQP hq)) (by simpa only [hQcard] using hroom) hcap
  omega
open Classical in
theorem base_list_finite_ncard_le_of_pole_cap
    (phi : F →+* K) (D : Finset F) (w : F → F) (k A B : ℕ)
    (hk : 0 < k) (hkA : k < A)
    (hroom : D.card + k * (B + 1) ^ 2 < Fintype.card K)
    (hcap : ∀ alpha : K, (∀ x ∈ D, phi x ≠ alpha) →
      (poleMCASet phi D w alpha k A).ncard ≤ B) :
    (baseCloseSet D w k A).Finite ∧ (baseCloseSet D w k A).ncard ≤ B := by
  have hfinsets := every_finset_card_le_of_pole_cap phi D w k A B hk hkA hroom hcap
  have hfinite : (baseCloseSet D w k A).Finite := by
    by_contra hinfinite
    obtain ⟨P, hP, hcard⟩ := Set.Infinite.exists_subset_card_eq hinfinite (B + 1)
    have h := hfinsets P hP
    omega
  refine ⟨hfinite, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  apply hfinsets hfinite.toFinset
  intro q hq
  exact hfinite.mem_toFinset.mp hq
end Sol1.Reciprocal
end
section
namespace Sol1
open Finset Module
theorem exists_avoiding_subspaces_card_le
    {K V I : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [Fintype V] [FiniteDimensional K V]
    (s : Finset I) (p : I → Submodule K V)
    (hp : ∀ i ∈ s, p i ≠ ⊤) (hs : s.card ≤ Fintype.card K) :
    ∃ v : V, ∀ i ∈ s, v ∉ p i := by
  classical
  by_cases he : s = ∅
  · subst s
    exact ⟨0, by simp⟩
  obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr he
  let q := Fintype.card K
  let d := Module.finrank K V
  let N := q ^ (d - 1)
  have hq : 1 < q := Fintype.one_lt_card
  have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le _) (Submodule.finrank_lt (hp i₀ hi₀))
  have hN : 0 < N := pow_pos (by omega : 0 < q) _
  have hfull : q * N = Fintype.card V := by
    rw [Module.card_eq_pow_finrank (K := K)]
    exact (mul_comm _ _).trans (Nat.pow_pred_mul hd)
  let A : I → Finset V := fun i => Finset.univ.filter fun x => x ∈ p i
  have hz : ∀ i, (0 : V) ∈ A i := by intro i; simp [A]
  have hA : ∀ i ∈ s, (A i).card ≤ N := by
    intro i hi
    change (Finset.univ.filter fun x : V => x ∈ p i).card ≤ N
    rw [← Fintype.card_subtype (fun x : V => x ∈ p i)]
    rw [Module.card_eq_pow_finrank (K := K)]
    change q ^ Module.finrank K (p i) ≤ q ^ (d - 1)
    have hr := Submodule.finrank_lt (hp i hi)
    gcongr
    omega
  let U := s.biUnion fun i => (A i).erase 0
  have hU : U.card ≤ q * (N - 1) := by
    apply (Finset.card_biUnion_le_card_mul s (fun i => (A i).erase 0) (N - 1) ?_).trans
    · exact Nat.mul_le_mul_right _ hs
    · intro i hi
      have hzero := Finset.card_erase_add_one (hz i)
      have hbound := hA i hi
      omega
  have hcomp : (Finset.univ.erase (0 : V)).card + 1 = Fintype.card V := by
    simpa using (Finset.card_erase_add_one (Finset.mem_univ (0 : V)))
  have hstrict : U.card < (Finset.univ.erase (0 : V)).card := by
    have hprod : q * (N - 1) = q * N - q := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    rw [hprod, hfull] at hU
    have hV : q ≤ Fintype.card V := by
      rw [← hfull]
      nlinarith
    omega
  obtain ⟨v, hv, hvU⟩ := Finset.exists_mem_notMem_of_card_lt_card hstrict
  refine ⟨v, ?_⟩
  intro i hi hvp
  apply hvU
  exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_erase.mpr
    ⟨(Finset.mem_erase.mp hv).1, by simpa [A] using hvp⟩⟩
theorem exists_row_projection
    {K I R : Type*} [Field K] [Fintype K] [Fintype R]
    (s : Finset I) (v : I → R → K)
    (hv : ∀ i ∈ s, v i ≠ 0) (hs : s.card ≤ Fintype.card K) :
    ∃ lambda : R → K, ∀ i ∈ s, (∑ j, lambda j * v i j) ≠ 0 := by
  classical
  let f : I → ((R → K) →ₗ[K] K) := fun i =>
    { toFun := fun lambda => ∑ j, lambda j * v i j
      map_add' := by intro a b; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro a b; simp [Finset.mul_sum, mul_assoc] }
  have hp : ∀ i ∈ s, LinearMap.ker (f i) ≠ ⊤ := by
    intro i hi htop
    obtain ⟨j, hj⟩ : ∃ j, v i j ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hv i hi (funext hn)
    have heval : f i (Pi.single j 1) = v i j := by simp [f, Pi.single_apply]
    have hz : (Pi.single j 1 : R → K) ∈ LinearMap.ker (f i) := by rw [htop]; trivial
    change f i (Pi.single j 1) = 0 at hz
    exact hj (heval.symm.trans hz)
  obtain ⟨lambda, hlambda⟩ := exists_avoiding_subspaces_card_le s
    (fun i => LinearMap.ker (f i)) hp hs
  exact ⟨lambda, by simpa [f] using hlambda⟩
end Sol1
end
section
namespace Sol1.FiniteRowProjection
noncomputable section
open scoped BigOperators
variable {K I R : Type*} [Field K] [Fintype K] [Fintype R]
def project (lambda : R → K) (f : I → R → K) : I → K :=
  fun i ↦ ∑ r, lambda r * f i r
omit [Field K] [Fintype K] [Fintype R] in
theorem exists_coordinate_ne {f g : I → R → K} (hne : f ≠ g) :
    ∃ i, f i ≠ g i := by
  by_contra h
  push Not at h
  exact hne (funext h)
theorem exists_project_injective (P : Finset (I → R → K))
    (hroom : P.card ^ 2 ≤ Fintype.card K) :
    ∃ lambda : R → K, Set.InjOn (project (I := I) lambda) (P : Set (I → R → K)) := by
  classical
  let pairs := (P.product P).filter fun fg ↦ fg.1 ≠ fg.2
  let coordinate : pairs → I := fun fg ↦
    Classical.choose (exists_coordinate_ne (Finset.mem_filter.mp fg.property).2)
  let residual : pairs → R → K := fun fg ↦ fg.val.1 (coordinate fg) - fg.val.2 (coordinate fg)
  have hresidual : ∀ fg : pairs, residual fg ≠ 0 := by
    intro fg
    exact sub_ne_zero.mpr (Classical.choose_spec
      (exists_coordinate_ne (Finset.mem_filter.mp fg.property).2))
  have hpairs : (Finset.univ : Finset pairs).card ≤ Fintype.card K := by
    rw [Finset.card_univ, Fintype.card_coe]
    calc
      pairs.card ≤ (P.product P).card := Finset.card_filter_le _ _
      _ = P.card ^ 2 := by simp [pow_two]
      _ ≤ Fintype.card K := hroom
  obtain ⟨lambda, hlambda⟩ := Sol1.exists_row_projection
    (Finset.univ : Finset pairs) residual (fun fg _ ↦ hresidual fg) hpairs
  refine ⟨lambda, ?_⟩
  intro f hf g hg heq
  by_contra hne
  let fg : pairs := ⟨(f,g), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hf,hg⟩, hne⟩⟩
  apply hlambda fg (Finset.mem_univ _)
  have he := congrFun heq (coordinate fg)
  change (∑ r, lambda r * f (coordinate fg) r) =
    ∑ r, lambda r * g (coordinate fg) r at he
  change (∑ r, lambda r * (f (coordinate fg) r - g (coordinate fg) r)) = 0
  simpa only [mul_sub, Finset.sum_sub_distrib] using sub_eq_zero.mpr he
omit [Fintype K] in
theorem project_mem (C : Submodule K (I → K)) (lambda : R → K)
    (f : I → R → K) (hf : ∀ r, (fun i ↦ f i r) ∈ C) : project lambda f ∈ C := by
  classical
  have hm : (∑ r, lambda r • (fun i ↦ f i r)) ∈ C :=
    C.sum_mem (fun r _ ↦ C.smul_mem (lambda r) (hf r))
  have heq : project lambda f = ∑ r, lambda r • (fun i ↦ f i r) := by
    ext i
    simp [project]
  rw [heq]
  exact hm
open Classical in
def agreementCard [Fintype I] {A : Type*} (f w : I → A) : ℕ :=
  (Finset.univ.filter fun i ↦ f i = w i).card
omit [Field K] [Fintype K] [Fintype R] in
theorem agreementCard_mono [Fintype I] {A B : Type*}
    (f w : I → A) (g z : I → B) (h : ∀ i, f i = w i → g i = z i) :
    agreementCard f w ≤ agreementCard g z := by
  classical
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h i (Finset.mem_filter.mp hi).2⟩
omit [Fintype K] in
theorem agreementCard_le_project [Fintype I] (lambda : R → K) (f w : I → R → K) :
    agreementCard f w ≤ agreementCard (project lambda f) (project lambda w) := by
  classical
  apply agreementCard_mono
  intro i he
  simp only [project, he]
theorem finset_vector_list_card_le [Fintype I]
    (C : Submodule K (I → K)) (A B : ℕ)
    (hroom : (B + 1) ^ 2 ≤ Fintype.card K)
    (hscalar : ∀ w : I → K, ∀ P : Finset (I → K),
      (∀ f ∈ P, f ∈ C ∧ A ≤ agreementCard f w) → P.card ≤ B)
    (w : I → R → K) (P : Finset (I → R → K))
    (hP : ∀ f ∈ P, (∀ r, (fun i ↦ f i r) ∈ C) ∧ A ≤ agreementCard f w) :
    P.card ≤ B := by
  classical
  by_contra hlarge
  have hsize : B + 1 ≤ P.card := by omega
  obtain ⟨Q, hQP, hQcard⟩ := Finset.exists_subset_card_eq hsize
  obtain ⟨lambda, hinj⟩ := exists_project_injective Q (by simpa only [hQcard] using hroom)
  have hprojected : ∀ f ∈ Q.image (project lambda),
      f ∈ C ∧ A ≤ agreementCard f (project lambda w) := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨hcode, hagree⟩ := hP g (hQP hg)
    exact ⟨project_mem C lambda g hcode,
      hagree.trans (agreementCard_le_project lambda g w)⟩
  have hbound := hscalar (project lambda w) (Q.image (project lambda)) hprojected
  rw [Finset.card_image_of_injOn hinj, hQcard] at hbound
  omega
end
end Sol1.FiniteRowProjection
end
section
namespace Astra7
open MvPolynomial
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 4000
variable {F σ ι : Type*} [Field F] [IsAlgClosed F] [Fintype σ] [Fintype ι]
theorem weighted_hypersurface_count
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (hchar : ∀ i, (w i : F) ≠ 0)
    {g : MvPolynomial σ F} (hg : g ≠ 0) (s : MvPolynomial σ F)
    {v b A m : ℕ} (hv : g.weightedTotalDegree w ≤ v)
    (cuts : ι → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).weightedTotalDegree w ≤ b)
    (hb : 0 < b) (hmA : m ≤ A)
    (hfinite : ∀ T : Finset ι, T.card = m →
      {x : σ → F | aeval x g = 0 ∧ aeval x s ≠ 0 ∧
        ∀ i ∈ T, aeval x (cuts i) = 0}.Finite)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, aeval x g = 0 ∧ aeval x s ≠ 0)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (cuts i) = 0}.ncard) :
    ((S.card * ∏ i, w i : ℕ) : ℚ) ≤ v *
      ((((Fintype.card ι - m + 1) * b : ℕ) : ℚ) / ((A-m+1 : ℕ) : ℚ)) ^
        (Nat.card σ - 1) := by
  classical
  obtain ⟨theta,htheta⟩ := exists_avoiding_shift S
  let G := powerSubst w theta g
  let Sep := powerSubst w theta s
  let C := fun i => powerSubst w theta (cuts i)
  have hG : G ≠ 0 := by
    intro hz
    apply hg
    apply powerSubst_injective w theta hw
    simpa [G] using hz
  have hGdeg : G.totalDegree ≤ v := (degree_powerSubst w theta g).trans hv
  have hCdeg : ∀ i, (C i).totalDegree ≤ b := fun i =>
    (degree_powerSubst w theta (cuts i)).trans (hdeg i)
  have hfinite' : ∀ T : Finset ι, T.card = m →
      {x : σ → F | aeval x G = 0 ∧ aeval x Sep ≠ 0 ∧
        ∀ i ∈ T, aeval x (C i) = 0}.Finite := by
    intro T hT
    have hh := finite_powerPoint_preimage w theta hw (hfinite T hT)
    simpa [G,Sep,C,Set.preimage_setOf_eq,eval_powerSubst] using hh
  have hLS : ∀ x ∈ liftFinset w theta S, aeval x G = 0 ∧ aeval x Sep ≠ 0 := by
    intro x hx
    have hh := hS _ ((mem_liftFinset w theta x S hw).mp hx)
    simpa [G,Sep,eval_powerSubst] using hh
  have hLA : ∀ x ∈ liftFinset w theta S, A ≤ {i | aeval x (C i) = 0}.ncard := by
    intro x hx
    have hh := hA _ ((mem_liftFinset w theta x S hw).mp hx)
    simpa [C,eval_powerSubst] using hh
  have hh := hypersurface_card_le_of_finite_fibers hG Sep hGdeg C hCdeg hb hmA
    hfinite' (liftFinset w theta S) hLS hLA
  rwa [card_liftFinset w theta S hw hchar htheta] at hh
end
end Astra7
end
section
namespace Astra7
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 4000
variable {F : Type*} [Field F]
theorem initialEquation_weight {r : ℕ} (a b : ℕ) (center : F)
    (Q : DifferentialPolynomial F r) :
    (initialJetEquation center Q).weightedTotalDegree (coeffWeight a b (r+1)) ≤
      Q.weightedTotalDegree (jetWeight a b (r+1)) := by
  apply weightedTotalDegree_aeval_le_of_le
  intro i
  cases i with
  | none => simp [jetWeight]
  | some j =>
    change (MvPolynomial.X j : MvPolynomial (Fin (r+1)) F).weightedTotalDegree
      (coeffWeight a b (r+1)) ≤ a+b*j.val
    rw [MvPolynomial.X,weightedTotalDegree_monomial _ _ 1 one_ne_zero]
    simp [Finsupp.weight_single,coeffWeight]
def chartBound (r a b V K τ : ℕ) : ℕ := τ*(V-(a+b*r))+a+b*(K-1)
theorem agreementEquation_weight {r : ℕ} (a b V K τ : ℕ) (center : F)
    (Q : DifferentialPolynomial F r) (hτ : TaylorExponentSufficient r K τ)
    (hV : a+b*r ≤ V)
    (hQ : Q.weightedTotalDegree (jetWeight a b (r+1)) ≤ V) (x y : F) :
    (taylorAgreementEquation center Q K τ x y).weightedTotalDegree
      (coeffWeight a b (r+1)) ≤ chartBound r a b V K τ := by
  unfold taylorAgreementEquation
  apply (AddMonoidAlgebra.supDegree_sub_le).trans
  apply max_le
  · apply AddMonoidAlgebra.supDegree_sum_le.trans
    apply Finset.sup_le
    intro l _
    apply (weightedTotalDegree_mul_le _ _ _).trans
    rw [weightedTotalDegree_C,zero_add]
    apply (commonTaylor_weight a b V K τ center Q hτ hV hQ l).trans
    dsimp [chartBound]
    have hl : l.val ≤ K-1 := by omega
    gcongr
  · apply (weightedTotalDegree_mul_le _ _ _).trans
    rw [weightedTotalDegree_C,zero_add]
    apply (weightedTotalDegree_pow_le _ _ _).trans
    have hs := (initialSeparant_weight a b center Q).trans
      (Nat.sub_le_sub_right hQ (a+b*r))
    exact (Nat.mul_le_mul_left τ hs).trans (by dsimp [chartBound]; omega)
theorem weighted_regular_jets_card [IsAlgClosed F] {r n k A : ℕ}
    (a b V : ℕ) (ha : 0 < a) (hV : a+b*r ≤ V)
    (hchar : ∀ j : Fin (r+1), ((a+b*j.val : ℕ) : F) ≠ 0)
    (center : F) (Q : DifferentialPolynomial F r)
    (hQ : Q.weightedTotalDegree (jetWeight a b (r+1)) ≤ V)
    (hrk : r < k) (hkA : k ≤ A)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (S : Finset (Fin (r+1) → F))
    (hS : ∀ jet ∈ S, aeval jet (initialJetEquation center Q) = 0 ∧
      aeval jet (initialJetSeparant center Q) ≠ 0)
    (hA : ∀ jet ∈ S, A ≤ {i | aeval jet
      (taylorAgreementEquation center Q k (2*k) (domain i) (received i)) = 0}.ncard) :
    ((S.card * ∏ j : Fin (r+1), (a+b*j.val) : ℕ) : ℚ) ≤ V *
      ((((n-k+1)*chartBound r a b V k (2*k) : ℕ) : ℚ) / ((A-k+1 : ℕ) : ℚ)) ^ r := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨jet,hjet⟩
  · simp only [Finset.card_empty,zero_mul,Nat.cast_zero]
    positivity
  have hsep : initialJetSeparant center Q ≠ 0 := by
    intro hz
    exact (hS jet hjet).2 (by simp [hz])
  have hinit := initialJetEquation_ne_zero_of_initialJetSeparant_ne_zero center Q hsep
  have hτ := taylorExponentSufficient_two_mul r k
  have hw : ∀ j : Fin (r+1), 0 < coeffWeight a b (r+1) j := by
    intro j
    dsimp [coeffWeight]
    omega
  have hfinite : ∀ T : Finset (Fin n), T.card = k →
      {jet : Fin (r+1) → F | aeval jet (initialJetEquation center Q) = 0 ∧
        aeval jet (initialJetSeparant center Q) ≠ 0 ∧
        ∀ i ∈ T, aeval jet (taylorAgreementEquation center Q k (2*k)
          (domain i) (received i)) = 0}.Finite := by
    intro T hT
    apply Set.Subsingleton.finite
    intro x hx y hy
    apply eq_of_highTaylorCuts_of_agreement center Q (k := k) hτ hrk domain received T
      domain.injective.injOn (by omega) hx.2.1 hy.2.1
      (by intro l hl hl'; omega) (by intro l hl hl'; omega) hx.2.2 hy.2.2
  have hh := weighted_hypersurface_count (coeffWeight a b (r+1)) hw hchar hinit
    (initialJetSeparant center Q) ((initialEquation_weight a b center Q).trans hQ)
    (fun i => taylorAgreementEquation center Q k (2*k) (domain i) (received i))
    (fun i => agreementEquation_weight a b V k (2*k) center Q hτ hV hQ (domain i) (received i))
    (by dsimp [chartBound]; omega) hkA hfinite S hS hA
  simpa [coeffWeight,Nat.card_eq_fintype_card] using hh
end
end Astra7
end
section
namespace Astra7
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 4000
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F]
theorem weighted_regular_polynomial_card {r n k A : ℕ}
    (a b V : ℕ) (ha : 0 < a) (hV : a+b*r ≤ V)
    (hchar : ∀ j : Fin (r+1), ((a+b*j.val : ℕ) : F) ≠ 0)
    (Q : DifferentialPolynomial F r)
    (hQ : Q.weightedTotalDegree (jetWeight a b (r+1)) ≤ V)
    (hrk : r < k) (hkA : k ≤ A)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hbin : ∀ i, r < i → i < k → (i.choose r : F) ≠ 0)
    (S : Finset (Polynomial F))
    (hdegree : ∀ P ∈ S, P.degree < k)
    (hsol : ∀ P ∈ S, differentialSpecialization Q P=0)
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last r)) P ≠ 0)
    (hagree : ∀ P ∈ S,
      A ≤ (Finset.univ.filter fun i => P.eval (domain i)=received i).card) :
    ((S.card * ∏ j : Fin (r+1), (a+b*j.val) : ℕ) : ℚ) ≤ V *
      ((((n-k+1)*chartBound r a b V k (2*k) : ℕ) : ℚ) / ((A-k+1 : ℕ) : ℚ)) ^ r := by
  classical
  let E := AlgebraicClosure F
  let f : F →+* E := algebraMap F E
  have hbinE : ∀ i, r < i → i < k → (i.choose r : E) ≠ 0 := by
    intro i hir hik hz
    apply hbin i hir hik
    exact f.injective (by simpa using hz)
  have hcharE : ∀ j : Fin (r+1), ((a+b*j.val : ℕ) : E) ≠ 0 := by
    intro j hz
    apply hchar j
    apply f.injective
    rw [map_natCast,map_zero]
    exact hz
  obtain ⟨center,J,hcard,hJ⟩ := exists_regular_solution_jet_family_of_exponent f Q k k (2*k)
    (taylorExponentSufficient_two_mul r k) le_rfl S domain received hdegree hsol hsep hbinE hagree
  let QE := MvPolynomial.map f Q
  have hQE : QE.weightedTotalDegree (jetWeight a b (r+1)) ≤ V := by
    apply Finset.sup_le
    intro m hm
    exact (le_weightedTotalDegree _ (MvPolynomial.support_map_subset f Q hm)).trans hQ
  let domainE : Fin n ↪ E := domain.trans ⟨f,f.injective⟩
  have hA : ∀ jet ∈ J, A ≤ {i | aeval jet
      (taylorAgreementEquation center QE k (2*k) (domainE i) (f (received i)))=0}.ncard := by
    intro jet hjet
    have heq : {i | aeval jet (taylorAgreementEquation center QE k (2*k)
        (domainE i) (f (received i)))=0} =
        ((Finset.univ.filter fun i => aeval jet (taylorAgreementEquation center QE k (2*k)
          (f (domain i)) (f (received i)))=0 : Finset (Fin n)) : Set (Fin n)) := by
      ext i
      simp only [Set.mem_setOf_eq,Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and]
      rfl
    rw [heq,Set.ncard_coe_finset]
    exact (hJ jet hjet).2.2.2
  have hh := weighted_regular_jets_card a b V ha hV hcharE center QE hQE hrk hkA domainE
    (fun i => f (received i)) J (fun jet hjet => ⟨(hJ jet hjet).1,(hJ jet hjet).2.1⟩) hA
  rwa [hcard] at hh
theorem native_choose_two [CharP F 2130706433] (i : ℕ) (hi : 2 < i) (hik : i < 131073) :
    (i.choose 2 : F) ≠ 0 := by
  have hh := natCast_choose_ne_zero_of_ringChar (F := F) (D := 131072) (s := 2)
    (Or.inr (by rw [ringChar.eq F 2130706433]; norm_num)) (i-2) (by omega) (by omega)
  simpa only [Nat.sub_add_cancel (by omega : 2 ≤ i)] using hh
def weightedRegularCap : ℚ := (148 : ℚ) / 45 *
  (((131072 : ℚ)*36962583)/49193)^2
theorem regular64_card [CharP F 2130706433]
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F)
    (Q : DifferentialPolynomial F 2)
    (hQ : Q.weightedTotalDegree (jetWeight 1 4 3) ≤ 148)
    (S : Finset (Polynomial F))
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last 2)) P ≠ 0)
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received 131073 180265) :
    (S.card : ℚ) ≤ weightedRegularCap := by
  classical
  have hchar : ∀ j : Fin 3, ((1+4*j.val : ℕ) : F) ≠ 0 := by
    intro j hz
    have hdvd := (CharP.cast_eq_zero_iff F 2130706433 (1+4*j.val)).mp hz
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hdvd
  have hh := weighted_regular_polynomial_card (r := 2) (n := 262144) (k := 131073) (A := 180265)
    1 4 148 (by decide) (by decide) hchar Q hQ
    (by decide) (by decide) domain received native_choose_two S
    (fun P hP => (hS P hP).2.1) (fun P hP => (hS P hP).1) hsep
    (fun P hP => by
      simpa [ReedSolomon.closePolynomialSet,ReedSolomon.polynomialAgreementSet] using
        (hS P hP).2.2)
  norm_num [chartBound,Fin.prod_univ_succ] at hh
  dsimp [weightedRegularCap]
  linarith
end
end Astra7
end
section
noncomputable section
open Polynomial PolynomialDifferential
namespace ReedSolomon.HiddenDerivative
variable {F : Type*} [Field F]
theorem directJetStageCharge_le_weight_order
    {d : ℕ} (stage : SeparantStage F d)
    (n A k K nu r : ℕ) (hAn : A ≤ n)
    (hweight : jetTotalDegree stage.1 ≤ nu) (horder : stage.2.val ≤ r) :
    directJetStageCharge n A k K stage ≤
      dimensionSensitiveIncidenceProduct n A k 1 r * (nu : ℚ) *
        ((1 + 2 * K * (nu - 1) : ℕ) : ℚ) ^ r := by
  have hp := dimensionSensitiveIncidenceProduct_mono_dimension
    (n := n) (A := A) (k := k) (b := 1) hAn Nat.zero_lt_one horder
  have hbase :
      (1 + 2 * K * (jetTotalDegree stage.1 - 1) : ℕ) ≤
        1 + 2 * K * (nu - 1) :=
    Nat.add_le_add_left (Nat.mul_le_mul_left (2 * K)
      (Nat.sub_le_sub_right hweight 1)) 1
  have hb : (1 : ℚ) ≤
      ((1 + 2 * K * (nu - 1) : ℕ) : ℚ) := by
    exact_mod_cast (Nat.le_add_right 1 _)
  unfold directJetStageCharge
  calc
    dimensionSensitiveIncidenceProduct n A k 1 stage.2.val *
        (jetTotalDegree stage.1 : ℚ) *
        (1 + 2 * K * (jetTotalDegree stage.1 - 1) : ℕ) ^ stage.2.val ≤
      dimensionSensitiveIncidenceProduct n A k 1 r * (nu : ℚ) *
        ((1 + 2 * K * (nu - 1) : ℕ) : ℚ) ^ stage.2.val := by
          gcongr
          · exact mul_nonneg (dimensionSensitiveIncidenceProduct_nonneg n A k 1 r)
              (Nat.cast_nonneg _)
          · exact dimensionSensitiveIncidenceProduct_nonneg n A k 1 r
    _ ≤ dimensionSensitiveIncidenceProduct n A k 1 r * (nu : ℚ) *
        ((1 + 2 * K * (nu - 1) : ℕ) : ℚ) ^ r := by
          gcongr
          exact mul_nonneg (dimensionSensitiveIncidenceProduct_nonneg n A k 1 r)
            (Nat.cast_nonneg _)
end ReedSolomon.HiddenDerivative
namespace ReedSolomon
open HiddenDerivative
universe u
variable {F : Type u} [Field F]
end ReedSolomon
end
end
section
namespace Sol1.C40Primitives
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
theorem map_resultant_eq_zero_of_common_root
    {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (f g : R[X]) (m n : ℕ)
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (hsize : m ≠ 0 ∨ n ≠ 0)
    (z : S) (hfroot : f.eval₂ phi z = 0) (hgroot : g.eval₂ phi z = 0) :
    phi (f.resultant g m n) = 0 := by
  obtain ⟨p, q, _hp, _hq, hbezout⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant f g hf hg hsize
  have he := congrArg (fun t : R[X] ↦ t.eval₂ phi z) hbezout
  simpa only [eval₂_add, eval₂_mul, eval₂_C, hfroot, hgroot, zero_mul, zero_add] using he.symm
theorem native_binomial_guard {E : Type*} [Field E] [CharP E 2130706433]
    (r : ℕ) (_hr : r ≤ 2) (i : ℕ) (hri : r < i) (hi : i < 131073) :
    (i.choose r : E) ≠ 0 := by
  have h := natCast_choose_ne_zero_of_ringChar (D := 131072) (s := r)
    (Or.inr (by rw [ringChar.eq E 2130706433]; norm_num)) (i - r)
    (by omega) (by omega)
  simpa only [Nat.sub_add_cancel (Nat.le_of_lt hri)] using h
end Sol1.C40Primitives
end
section
namespace Sol1.C57
open Polynomial PolynomialDifferential MvPolynomial
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
variable {E : Type*} [Field E]
theorem singular_weight (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    jetTotalDegree (singularEquation d Q) ≤
      jetTotalDegree (regularPart d Q) * (jetTotalDegree (regularPart d Q) - 1) := by
  unfold singularEquation jetTotalDegree
  apply Sol1.C58.weighted_derivative_resultant_le
  intro i hi
  have hi' : i ≤ degreeOf none (radicalPrimPart none (topReindex d Q)) := by
    simpa only [ordinaryRootPolynomial, natDegree_optionEquivLeft] using hi
  have h := coeff_weight_add_le jetDegreeWeight
    (radicalPrimPart none (topReindex d Q)) i hi'
  change i + ((optionEquivLeft E (JetVariable d)
    (radicalPrimPart none (topReindex d Q))).coeff i).weightedTotalDegree jetDegreeWeight ≤ _
  exact h.trans_eq (regular_weight d Q)
theorem singular_root (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) (P : E[X])
    (hpos : 0 < jetDegree (regularPart d Q) (Fin.last (d + 1)))
    (hroot : differentialSpecialization (regularPart d Q) P = 0)
    (hsep : differentialSpecialization (separant (regularPart d Q) (Fin.last (d + 1))) P = 0) :
    differentialSpecialization (singularEquation d Q) P = 0 := by
  let f := ordinaryRootPolynomial (topReindex d Q)
  have hb : f.natDegree = jetDegree (regularPart d Q) (Fin.last (d + 1)) := by
    change (ordinaryRootPolynomial (topReindex d Q)).natDegree = _
    rw [← regular_presentation d Q, topPresentation_degree]
  change (differentialSpecializationHom P).toRingHom
    (Polynomial.resultant f f.derivative f.natDegree (f.natDegree - 1)) = 0
  apply Sol1.C40Primitives.map_resultant_eq_zero_of_common_root
    (differentialSpecializationHom P).toRingHom f f.derivative f.natDegree (f.natDegree - 1)
    le_rfl (Polynomial.natDegree_derivative_le f) (Or.inl (by omega))
    (Polynomial.hasseDeriv (d + 1) P)
  · change f.eval₂ _ _ = 0
    rw [show f = topPresentation d (regularPart d Q) from (regular_presentation d Q).symm,
      topPresentation_eval]
    exact hroot
  · change f.derivative.eval₂ _ _ = 0
    rw [show f = topPresentation d (regularPart d Q) from (regular_presentation d Q).symm,
      topPresentation_derivative, topPresentation_eval]
    exact hsep
def exceptionalEquation (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    DifferentialPolynomial E d := lowerPart d Q * singularEquation d Q
theorem exceptional_ne_zero (d : ℕ) (Q : DifferentialPolynomial E (d + 1))
    (hchar : ringChar E = 0 ∨ jetDegree Q (Fin.last (d + 1)) < ringChar E) :
    exceptionalEquation d Q ≠ 0 :=
  mul_ne_zero (lower_ne_zero d Q) (singularEquation_ne_zero d Q hchar)
theorem root_regular_or_exceptional (d : ℕ) (Q : DifferentialPolynomial E (d + 1))
    (hQ : Q ≠ 0) (P : E[X]) (hroot : differentialSpecialization Q P = 0)
    (hpos : 0 < jetDegree (regularPart d Q) (Fin.last (d + 1))) :
    (differentialSpecialization (regularPart d Q) P = 0 ∧
      differentialSpecialization (separant (regularPart d Q) (Fin.last (d + 1))) P ≠ 0) ∨
    differentialSpecialization (exceptionalEquation d Q) P = 0 := by
  rcases root_split d Q hQ P hroot with hc | hr
  · right
    simp only [exceptionalEquation, differentialSpecialization, map_mul]
    change differentialSpecialization (lowerPart d Q) P * _ = 0
    rw [hc, zero_mul]
  · by_cases hs : differentialSpecialization
        (separant (regularPart d Q) (Fin.last (d + 1))) P = 0
    · right
      have hz := singular_root d Q P hpos hr hs
      simp only [exceptionalEquation, differentialSpecialization, map_mul]
      change _ * differentialSpecialization (singularEquation d Q) P = 0
      rw [hz, mul_zero]
    · exact Or.inl ⟨hr,hs⟩
theorem exceptional_weight (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    jetTotalDegree (exceptionalEquation d Q) ≤ jetTotalDegree (lowerPart d Q) +
      jetTotalDegree (regularPart d Q) * (jetTotalDegree (regularPart d Q) - 1) := by
  apply (weightedTotalDegree_mul_le jetDegreeWeight _ _).trans
  exact Nat.add_le_add_left (singular_weight d Q) _
theorem degree_budget_sharp (c v h : ℕ) (hv : 0 < v) (hb : c + v ≤ h) :
    c + v * (v - 1) ≤ h * (h - 1) := by
  have hvh : v ≤ h := by omega
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hvh
  have hct : c ≤ t := by omega
  cases v with
  | zero => omega
  | succ v =>
    have hs : v + 1 + t - 1 = v + t := by omega
    simp only [Nat.succ_sub_one, hs]
    nlinarith [Nat.zero_le (v*t), Nat.zero_le (t*t)]
theorem exceptional_weight_sharp (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) (h : ℕ)
    (hweight : jetTotalDegree Q ≤ h) (hpos : 0 < jetTotalDegree (regularPart d Q)) :
    jetTotalDegree (exceptionalEquation d Q) ≤ h * (h - 1) :=
  (exceptional_weight d Q).trans (degree_budget_sharp _ _ _ hpos ((split_weight d Q).trans hweight))
end
end Sol1.C57
end
section
namespace Sol1.C57
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
variable {E : Type*} [Field E]
theorem orderZeroAsPolynomial_injective :
    Function.Injective (orderZeroAsPolynomial (F := E)) := by
  intro Q R h
  apply (MvPolynomial.renameEquiv E orderZeroVariableEquiv).injective
  apply (MvPolynomial.finSuccEquiv E 1).injective
  apply Polynomial.map_injective (MvPolynomial.uniqueAlgEquiv E (Fin 1)).toRingHom
    (MvPolynomial.uniqueAlgEquiv E (Fin 1)).injective
  exact h
theorem orderZeroAsPolynomial_degree (Q : DifferentialPolynomial E 0) :
    (orderZeroAsPolynomial Q).natDegree = jetTotalDegree Q := by
  have hleft : orderZeroOfPolynomial (orderZeroAsPolynomial Q) = Q := by
    apply orderZeroAsPolynomial_injective
    exact orderZeroAsPolynomial_orderZeroOfPolynomial _
  simpa only [hleft] using (orderZeroOfPolynomial_jetTotalDegree (orderZeroAsPolynomial Q)).symm
theorem order_zero_card_le (Q : DifferentialPolynomial E 0) (hQ : Q ≠ 0)
    (S : Finset E[X]) (hroot : ∀ P ∈ S, differentialSpecialization Q P = 0) :
    S.card ≤ jetTotalDegree Q := by
  have hP : orderZeroAsPolynomial Q ≠ 0 := by
    intro hz
    apply hQ
    apply orderZeroAsPolynomial_injective
    simpa only [orderZeroAsPolynomial, map_zero, Polynomial.map_zero] using hz
  have h := Polynomial.card_le_natDegree_of_injOn_of_eval_eq_zero hP
    (x := id) (s := S) Function.injective_id.injOn
    (fun P hP ↦ (orderZeroAsPolynomial_eval Q P).trans (hroot P hP))
  exact h.trans_eq (orderZeroAsPolynomial_degree Q)
section Native
variable [CharP E 2130706433]
theorem regular_top_card_le (d : ℕ) (hd : d ≤ 2)
    (domain : Fin 262144 ↪ E) (received : Fin 262144 → E)
    (Q : DifferentialPolynomial E d) (nu : ℕ)
    (hhighest : highestActiveJet Q = some (Fin.last d)) (hweight : jetTotalDegree Q ≤ nu)
    (S : Finset E[X])
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last d)) P ≠ 0)
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received 131073 180265) :
    (S.card : ℚ) ≤ dimensionSensitiveIncidenceProduct 262144 180265 131073 1 d * nu *
      ((1 + 2 * 131073 * (nu - 1) : ℕ) : ℚ) ^ d := by
  have hactual := finite_actualStage_regularSolutions_card_le_dimensionSensitive Q (Fin.last d)
    hhighest 131073 131073 (by omega) le_rfl domain received (by norm_num) (by norm_num)
    (fun r hr ↦ Sol1.C40Primitives.native_binomial_guard r (hr.trans hd)) S hsep hS
  exact hactual.trans (directJetStageCharge_le_weight_order (Q, Fin.last d)
    262144 180265 131073 131073 nu d (by norm_num) hweight (by simp))
end Native
theorem highestActiveJet_last_of_pos {d : ℕ} (Q : DifferentialPolynomial E d)
    (hpos : 0 < jetDegree Q (Fin.last d)) : highestActiveJet Q = some (Fin.last d) := by
  cases hh : highestActiveJet Q with
  | none =>
    exact False.elim (((highestActiveJet_eq_none_iff Q).mp hh) _ hpos)
  | some j =>
    have hj := isHighestActiveJet_of_highestActiveJet_eq_some hh
    have heq : j = Fin.last d := by
      by_contra hne
      have hlt : j < Fin.last d := lt_of_le_of_ne (Fin.le_last j) hne
      exact hj.2 _ hlt hpos
    exact congrArg some heq
end
end Sol1.C57
end
section
namespace Sol1.C57
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open Sol1.C42
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
variable {E : Type*} [Field E] [CharP E 2130706433]
theorem incidence_one : dimensionSensitiveIncidenceProduct 262144 180265 131073 1 1 = I1 := by
  norm_num [dimensionSensitiveIncidenceProduct, I1]
theorem cast_mul_pred (h : ℕ) : ((h * (h - 1) : ℕ) : ℚ) = (h : ℚ) * (h - 1) := by
  cases h with
  | zero => norm_num
  | succ h => simp [Nat.cast_add, Nat.cast_mul]
theorem firstOrderCharge_ge (h : ℕ) : (h : ℚ) ≤ firstOrderCharge h := by
  have hi : (1 : ℚ) ≤ I1 := by norm_num [I1]
  have hI : 0 ≤ I1 := by norm_num [I1]
  have hb : (1 : ℚ) ≤ (b h : ℚ) := by
    exact_mod_cast (by unfold b; omega : 1 ≤ b h)
  have hprod : 0 ≤ (h : ℚ) * (h - 1) := by
    rw [← cast_mul_pred]
    positivity
  have h1 : (h : ℚ) ≤ I1 * h := by nlinarith [Nat.cast_nonneg (α := ℚ) h]
  have h2 : I1 * h ≤ I1 * h * b h :=
    le_mul_of_one_le_right (mul_nonneg hI (Nat.cast_nonneg _)) hb
  exact (h1.trans h2).trans (le_add_of_nonneg_right hprod)
theorem first_order_card_le
    (domain : Fin 262144 ↪ E) (received : Fin 262144 → E)
    (Q : DifferentialPolynomial E 1) (hQ : Q ≠ 0) (h : ℕ) (hbound : h ≤ 4096)
    (hweight : jetTotalDegree Q ≤ h) (S : Finset E[X])
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received 131073 180265) :
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
      have hx := regular_top_card_le 1 (by norm_num) domain received G h
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
      _ = firstOrderCharge h := by rw [cast_mul_pred]; rfl
end
end Sol1.C57
end
section
namespace Sol1.Reciprocal
noncomputable section
open Polynomial Code LinearCode CoreDefinitions
variable {F K I : Type} [Field F] [Field K] [Fintype K] [Fintype I]
def liftedDomain (phi : F →+* K) (nodes : I ↪ F) : I ↪ K :=
  nodes.trans ⟨phi, phi.injective⟩
open Classical in
def baseNodeSet (nodes : I ↪ F) : Finset F := Finset.univ.image nodes
omit [Field F] in
theorem baseNodeSet_card (nodes : I ↪ F) : (baseNodeSet nodes).card = Fintype.card I := by
  classical
  unfold baseNodeSet
  rw [Finset.card_image_of_injective _ nodes.injective, Finset.card_univ]
open Classical in
omit [Field F] in
theorem mem_baseNodeSet (nodes : I ↪ F) (x : F) :
    x ∈ baseNodeSet nodes ↔ ∃ i, nodes i = x := by
  simp [baseNodeSet]
def repeatPoleInputs (phi : F →+* K) (nodes : I ↪ F) (w : F → F) (alpha : K) :
    Fin 2 → I → Fin 8 → K :=
  fun j i _ ↦ if j = 0 then phi (w (nodes i)) / (phi (nodes i) - alpha)
    else -1 / (phi (nodes i) - alpha)
noncomputable def repeatedRS (phi : F →+* K) (nodes : I ↪ F) (k : ℕ) :
    ModuleCode I K (Fin 8 → K) :=
  Code.ModuleCode.moduleInterleavedCode K K (Fin 8) I
    (ReedSolomon.code (liftedDomain phi nodes) k)
open Classical in
theorem pole_mca_isMCA_repeat
    (phi : F →+* K) (nodes : I ↪ F) (w : F → F)
    (alpha gamma : K) (k A : ℕ) (delta : ℝ)
    (hk : 0 < k) (hkA : k < A)
    (hthreshold : (Fintype.card I : ℝ) * (1 - delta) ≤ A)
    (halpha : ∀ x ∈ baseNodeSet nodes, phi x ≠ alpha)
    (hgamma : gamma ∈ poleMCASet phi (baseNodeSet nodes) w alpha k A) :
    IsMCA (AffineLineGenerator K) (repeatedRS phi nodes k) gamma
      (repeatPoleInputs phi nodes w alpha) delta := by
  classical
  have : NeZero k := ⟨by omega⟩
  obtain ⟨S, hSD, hAS, hdecode, _⟩ := hgamma
  obtain ⟨h, hh, heval⟩ := hdecode
  let T : Finset I := Finset.univ.filter fun i ↦ nodes i ∈ S
  have himage : T.image nodes = S := by
    ext x
    constructor
    · rintro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hi).2
    · intro hx
      obtain ⟨i, _hi, heq⟩ := Finset.mem_image.mp (hSD hx)
      exact Finset.mem_image.mpr ⟨i,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [heq] using hx⟩, heq⟩
  have hTcard : T.card = S.card := by
    calc
      T.card = (T.image nodes).card :=
        (Finset.card_image_of_injective T nodes.injective).symm
      _ = S.card := congrArg Finset.card himage
  have hnode : ∀ i ∈ T, nodes i ∈ S := fun i hi ↦ (Finset.mem_filter.mp hi).2
  change ∃ T : Finset I, (T.card : ℝ) ≥ Fintype.card I * (1 - delta) ∧ _
  refine ⟨T, hthreshold.trans ?_, ?_, (1 : Fin 2), ?_⟩
  · exact_mod_cast (show A ≤ T.card by omega)
  · apply Submodule.mem_map.mpr
    refine ⟨(fun i (_ : Fin 8) ↦ h.eval (phi (nodes i))), ?_, ?_⟩
    · change ∀ _row : Fin 8,
        (fun i ↦ h.eval (phi (nodes i))) ∈ ReedSolomon.code (liftedDomain phi nodes) k
      intro row
      exact ReedSolomon.evalOnPoints_mem_code_of_natDegree_lt hh
    · ext i row
      change h.eval (phi (nodes i.val)) =
        ∑ j, AffineLineGenerator K gamma j • repeatPoleInputs phi nodes w alpha j i.val row
      rw [heval (nodes i.val) (hnode i.val i.property)]
      simp [Fin.sum_univ_two, AffineLineGenerator, repeatPoleInputs, smul_eq_mul]
      ring
  · intro hbad
    obtain ⟨c, hc, hcT⟩ :=
      (mem_projectedCodeSubmod_iff (repeatedRS phi nodes k) T _).mp hbad
    have hrow : (fun i ↦ c i (0 : Fin 8)) ∈
        ReedSolomon.code (liftedDomain phi nodes) k := hc (0 : Fin 8)
    obtain ⟨g, hg, hgeval⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hrow
    apply pole_direction_never_extends phi S alpha k (hkA.trans_le hAS)
      (fun x hx ↦ halpha x (hSD hx))
    refine ⟨g, hg, ?_⟩
    intro x hx
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp (himage.symm ▸ hx)
    have he := congrFun (congrFun hcT ⟨i, hi⟩) (0 : Fin 8)
    change repeatPoleInputs phi nodes w alpha 1 i 0 = c i 0 at he
    rw [← heq]
    exact (hgeval i).trans (by simpa [repeatPoleInputs] using he.symm)
open Classical in
theorem pole_cap_of_actual_cap
    (phi : F →+* K) (nodes : I ↪ F) (w : F → F) (k A B : ℕ) (delta : ℝ)
    (hk : 0 < k) (hkA : k < A)
    (hthreshold : (Fintype.card I : ℝ) * (1 - delta) ≤ A)
    (hcap : ∀ U : Fin 2 → I → Fin 8 → K,
      {gamma | IsMCA (AffineLineGenerator K) (repeatedRS phi nodes k) gamma U delta}.ncard ≤ B)
    (alpha : K) (halpha : ∀ x ∈ baseNodeSet nodes, phi x ≠ alpha) :
    (poleMCASet phi (baseNodeSet nodes) w alpha k A).ncard ≤ B := by
  apply (Set.ncard_le_ncard (t := {gamma | IsMCA (AffineLineGenerator K)
    (repeatedRS phi nodes k) gamma (repeatPoleInputs phi nodes w alpha) delta}) ?_).trans
      (hcap (repeatPoleInputs phi nodes w alpha))
  intro gamma hgamma
  exact pole_mca_isMCA_repeat phi nodes w alpha gamma k A delta hk hkA
    hthreshold halpha hgamma
end
end Sol1.Reciprocal
end
section
namespace Sol1.C64
open Code LinearCode CoreDefinitions
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 0
variable {K I R : Type} [Field K] [Fintype K] [Fintype I] [Fintype R]
theorem exists_projected_bad_family (C D : ModuleCode I K K) (delta : ℝ)
    (U : Fin 2 → I → R → K) (hU : ∀ j r, (fun i ↦ U j i r) ∈ D)
    (S : Finset K) (hs : (S.card : ℕ∞) ≤ ENat.card K)
    (hbad : ∀ gamma ∈ S, IsMCA (AffineLineGenerator K) (C^⋈R) gamma U delta) :
    ∃ V : Fin 2 → I → K, (∀ j, V j ∈ D) ∧
      ∀ gamma ∈ S, IsMCA (AffineLineGenerator K) C gamma V delta := by
  classical
  choose! T hT using hbad
  obtain ⟨lambda,hlambda⟩ := Code.exists_rowFunctional_forall_notMem C U S T hs
    (fun gamma hg ↦ (hT gamma hg).2.2)
  let V : Fin 2 → I → K := fun j i ↦ ∑ r, lambda r • U j i r
  refine ⟨V,?_,?_⟩
  · intro j
    have heq : V j = ∑ r, lambda r • (fun i ↦ U j i r) := by
      ext i
      simp [V]
    rw [heq]
    exact D.sum_mem (fun r _ ↦ D.smul_mem (lambda r) (hU j r))
  · intro gamma hg
    refine ⟨T gamma,(hT gamma hg).1,?_,hlambda gamma hg⟩
    have hcomb := Code.projectedWord_rowCombination_mem C _ (T gamma) lambda (hT gamma hg).2.1
    have hfun : (fun i ↦ ∑ r, lambda r • (∑ j, (AffineLineGenerator K gamma j) • U j i) r) =
        fun i ↦ ∑ j, (AffineLineGenerator K gamma j) • V j i := by
      funext i
      simp only [V,Finset.sum_apply,Pi.smul_apply,Finset.smul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun r _ ↦ smul_comm _ _ _
    rwa [hfun] at hcomb
theorem restricted_interleaved_card_le (C D : ModuleCode I K K) (delta : ℝ) (B : ℕ)
    (hroom : B+1 ≤ Fintype.card K)
    (hscalar : ∀ V : Fin 2 → I → K, (∀ j, V j ∈ D) → ∀ S : Finset K,
      (∀ gamma ∈ S, IsMCA (AffineLineGenerator K) C gamma V delta) → S.card ≤ B)
    (U : Fin 2 → I → R → K) (hU : ∀ j r, (fun i ↦ U j i r) ∈ D)
    (S : Finset K) (hbad : ∀ gamma ∈ S, IsMCA (AffineLineGenerator K) (C^⋈R) gamma U delta) :
    S.card ≤ B := by
  classical
  by_contra hlarge
  have hsize : B+1 ≤ S.card := by omega
  obtain ⟨Q,hQS,hQcard⟩ := Finset.exists_subset_card_eq hsize
  have hroom' : (Q.card : ℕ∞) ≤ ENat.card K := by
    rw [hQcard,ENat.card_eq_coe_fintype_card]
    exact_mod_cast hroom
  obtain ⟨V,hV,hbadV⟩ := exists_projected_bad_family C D delta U hU Q hroom'
    (fun gamma hg ↦ hbad gamma (hQS hg))
  have hcount := hscalar V hV Q hbadV
  rw [hQcard] at hcount
  omega
end
end Sol1.C64
end
