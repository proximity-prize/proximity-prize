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
