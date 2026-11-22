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
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.SourceColumn
import Mathlib.Data.Int.Interval
set_option autoImplicit true
section
namespace Sol1.C42
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
private theorem two_mul_triangle (k : ℕ) : 2 * triangle k = k * (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change 2 * (triangle k + (k + 1)) = (k + 1) * (k + 1 + 1)
      nlinarith
private theorem triangle_truncation (k : ℕ) :
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
private theorem length_of_colon {R : Type*} [CommRing R] (A B : Ideal R) (x : R)
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
private theorem power_decompose {R : Type*} [CommRing R]
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
private theorem quotient_length_two_generators {R : Type*} [CommRing R] [IsLocalRing R]
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
end
end Sol1.C42
end
section
namespace Sol1.Reciprocal
open Polynomial
variable {F K : Type*} [Field F] [Field K]
end Sol1.Reciprocal
end
section
namespace Sol1.Reciprocal
open Polynomial
variable {F K : Type*} [Field F] [Field K] [Fintype K]
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
private theorem exists_coordinate_ne {f g : I → R → K} (hne : f ≠ g) :
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
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 4000
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F]
end
end Astra7
end
section
noncomputable section
open Polynomial PolynomialDifferential
namespace ReedSolomon.HiddenDerivative
variable {F : Type*} [Field F]
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
section Native
variable [CharP E 2130706433]
end Native
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
noncomputable def repeatedRS (phi : F →+* K) (nodes : I ↪ F) (k : ℕ) :
    ModuleCode I K (Fin 8 → K) :=
  Code.ModuleCode.moduleInterleavedCode K K (Fin 8) I
    (ReedSolomon.code (liftedDomain phi nodes) k)
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
