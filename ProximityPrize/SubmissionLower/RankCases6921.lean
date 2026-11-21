import ProximityPrize.SubmissionLower.Fast068
import ProximityPrize.SubmissionLower.Fast069
import ProximityPrize.SubmissionLower.Fast070
import ProximityPrize.SubmissionLower.Front6921
set_option Elab.async false

/- Profile transport of Dadon's PR 627. -/
section Port_K1_4Proof
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

namespace K21_4

open Polynomial FrobeniusLocator

theorem proof : K21.c4 := by
  intro u Γ hprincipal hΓ
  obtain ⟨a, g, hg, hga, ha, hkernel⟩ := hprincipal
  have hsum : a + (82073 - a) = 82073 := by omega
  have hcertificate : Native6921.PrincipalCert (u 0) (u 1) := by
    refine ⟨a, 82073 - a, hsum, ⟨{
      generator := g
      nonzero := hg
      degree_bound := hga
      kernel_eq := ?_
    }⟩⟩
    intro f
    rw [hsum, Principal.recurrence_kernel_iff_matrix, Principal.recurrenceMatrix_parameter]
    change (f.natDegree ≤ 82073 ∧
      ((K21.twoBlock u).map (algebraMap K21.K[X] K21.Frac)).mulVec
        (fun i => f.coeff i.val) = 0) ↔
      ∃ Q : K21.Frac[X], Q.natDegree ≤ 82073 - a ∧ f = g * Q
    constructor
    · rintro ⟨hf, hker⟩
      exact (hkernel f hf).mp hker
    · rintro ⟨Q, hQ, rfl⟩
      have hdegree : (g * Q).natDegree ≤ 82073 :=
        natDegree_mul_le.trans ((Nat.add_le_add hga hQ).trans_eq hsum)
      exact ⟨hdegree, (hkernel _ hdegree).mpr ⟨Q, hQ, rfl⟩⟩
  exact (Native6921.native_generic_principal_MCA_count u hcertificate Γ hΓ).trans (by norm_num)

end K21_4
end Port_K1_4Proof

section Port_K1_7Proof
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

namespace K21_7
noncomputable section

open Polynomial Matrix FrobeniusLocator K21
open ProximityPrize.Benchmark

private theorem eval_atSlope (P : Bivar) (a γ : K) :
    (atSlope P γ).eval a = (P.eval (C a)).eval γ := by
  simpa only [atSlope, Polynomial.coe_evalRingHom, Polynomial.eval_C] using
    (Polynomial.eval_map_apply (Polynomial.evalRingHom γ) (C a) (p := P))

private theorem atSlope_constant (G : K[X]) (γ : K) :
    atSlope (G.map C) γ = G := by
  rw [atSlope, Polynomial.map_map]
  have h : (Polynomial.evalRingHom γ).comp C = RingHom.id K := by
    ext a
    simp
  rw [h, Polynomial.map_id]

private theorem twoBlock_atSlope (u : Words) (γ : K) :
    ((twoBlock u).map (evalRingHom γ)) =
      Strata.conjugateHankel (Strata.twoConjugations (frobenius K p))
        node (fun i => u 0 i + γ * u 1 i) 48999 82073 := by
  rw [twoBlock, Strata.stacked_eq_frobeniusStacked, Strata.frobeniusStacked_eval]
  have h : (fun b : Fin 2 => iterateFrobenius K p b.val) =
      Strata.twoConjugations (frobenius K p) := by
    funext b
    fin_cases b
    · exact iterateFrobenius_zero K p
    · exact iterateFrobenius_one K p
  rw [h]

private theorem rank_at_normal {u : Words} (T : TwoActive u) {γ : K} (hγ : Normal u γ) :
    ((twoBlock u).map (evalRingHom γ)).rank = 48999 + T.height := by
  change _ = stackRank u at hγ
  rw [hγ, actual_stackRank]
  have := T.degreeSum
  have := T.nullitySum
  have := T.top
  unfold TwoActive.height
  omega

/-- The original stack has the same rank as its two evaluated error blocks. -/
private theorem error_rank {u : Words} {γ : K} (M : BadMark u γ)
    (E : Finset I) (hE : E.card ≤ 82073)
    (hEagree : ∀ i ∉ E, u 0 i + γ * u 1 i = M.decoder.eval (node i)) :
    ((twoBlock u).map (evalRingHom γ)).rank =
      (Strata.errorTwoMatrix (frobenius K p) (fun i : E => node i.val)
        (fun i : E => u 0 i.val + γ * u 1 i.val - M.decoder.eval (node i.val)) 48999).rank := by
  have hfix : ∀ b i, Strata.twoConjugations (frobenius K p) b (node i) = node i := by
    intro b i
    fin_cases b <;> simp [Strata.twoConjugations, frobenius_def, Native.native_domain_fixed]
  have h := Strata.conjugateHankel_error_rank
    (Strata.twoConjugations (frobenius K p)) node (fun i => u 0 i + γ * u 1 i)
    IRSProfile.domain.injective hfix M.decoder 131072 48999 82073 M.degree
    (by rw [IRSProfile.card_index]) E (by omega) hEagree
  rw [Strata.conjugateErrors_two] at h
  rw [twoBlock_atSlope]
  exact h

/-- When the distinct common error roots exhaust the gcd degree, their
monic locator has the same divisors as the gcd. -/
private theorem commonGCD_of_roots (U V : K[X]) (hV : V ≠ 0) (S : Finset I)
    (hroots : ∀ i ∈ S, (GCDMonoid.gcd U V).eval (node i) = 0)
    (hcard : S.card = (GCDMonoid.gcd U V).natDegree) :
    IsCommonGCD (locator node S) U V := by
  have hG : GCDMonoid.gcd U V ≠ 0 := gcd_ne_zero_of_right hV
  have hdiv := Strata.locator_dvd_of_eval_zero node IRSProfile.domain.injective S _ hroots
  have hassoc := Polynomial.associated_of_dvd_of_natDegree_le hdiv hG
    (by rw [locator_natDegree, hcard])
  exact ⟨(locator_monic node S).ne_zero, hdiv.trans (gcd_dvd_left U V),
    hdiv.trans (gcd_dvd_right U V), fun H hHU hHV => (dvd_gcd hHU hHV).trans hassoc.dvd'⟩

private theorem lift_dvd_atSlope {P : Bivar} {G : K[X]} (γ : K) (h : G.map C ∣ P) :
    G ∣ atSlope P γ := by
  have h' := map_dvd (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) h
  change atSlope (G.map C) γ ∣ atSlope P γ at h'
  rwa [atSlope_constant] at h'

private theorem valid_of_saturation {u : Words} {T : TwoActive u} (R : Relation T)
    (γ : K) (S : Finset I)
    (hdegree : max (atSlope (leftU R) γ).natDegree (atSlope (leftV R) γ).natDegree = T.height)
    (hG : IsCommonGCD (locator node S) (atSlope (leftU R) γ) (atSlope (leftV R) γ)) :
    ¬ InvalidLeft R := by
  intro hinvalid
  rcases hinvalid with hlow | ⟨G, _, hGU, hGV, hbad⟩
  · have hle : max (atSlope (leftU R) γ).natDegree (atSlope (leftV R) γ).natDegree ≤
        max (leftU R).natDegree (leftV R).natDegree :=
      max_le_max Polynomial.natDegree_map_le Polynomial.natDegree_map_le
    omega
  · have hS : locator node S ∣ locator node Finset.univ :=
      ⟨locator node (Finset.univ \ S),
        (Principal.locator_mul_sdiff node S Finset.univ (Finset.subset_univ S)).symm⟩
    exact hbad ((hG.2.2.2 G (lift_dvd_atSlope γ hGU) (lift_dvd_atSlope γ hGV)).trans hS)

theorem proof : K21.c7 := by
  classical
  intro u hfront T R γ hγ M
  let U := atSlope (leftU R) γ
  let V := atSlope (leftV R) γ
  let E : Finset I := Finset.univ.filter (fun i => M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i)
  let e : E → K := fun i => u 0 i.val + γ * u 1 i.val - M.decoder.eval (node i.val)
  let x : E → K := fun i => node i.val
  have hEagree (i : I) (hi : i ∉ E) : u 0 i + γ * u 1 i = M.decoder.eval (node i) := by
    by_contra h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Ne.symm h⟩)
  have hEcard : E.card ≤ 82073 := by
    have hsub : E ⊆ Finset.univ \ M.support := by
      intro i hi
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hs => ?_⟩
      exact (Finset.mem_filter.mp hi).2 (M.hits i hs)
    have h := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      IRSProfile.card_index] at h
    have := M.agreement
    omega
  have hH : T.height < 48999 := by
    have := T.degreeSum
    have := T.nullitySum
    have := hfront.1
    unfold TwoActive.height
    omega
  have hfit : 131072 + T.height ≤ M.support.card := by
    have := M.agreement
    omega
  have hfix (i : I) : frobenius K p (node i) = node i := Native.native_domain_fixed i
  obtain ⟨hpair, hrel⟩ :=
    Strata.certificate_specializes p node (u 0) (u 1) 131072 T.height R γ
  have hUle : U.natDegree ≤ T.height := hrel.degree_U
  have hVle : V.natDegree ≤ T.height := hrel.degree_V
  have hx : Function.Injective x := IRSProfile.domain.injective.comp Subtype.val_injective
  have he (i : E) : e i ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (Finset.mem_filter.mp i.property).2)
  have herror (i : E) : U.eval (x i) * e i + V.eval (x i) * frobenius K p (e i) = 0 :=
    Strata.certificate_error_identity p node (u 0) (u 1) IRSProfile.domain.injective
      Native.native_domain_fixed 131072 T.height R γ M.support hfit M.decoder M.degree M.hits i.val
  have hrank : (Strata.errorTwoMatrix (frobenius K p) x e 48999).rank = 48999 + T.height :=
    (error_rank M E hEcard hEagree).symm.trans (rank_at_normal T hγ)
  obtain ⟨hU, hV⟩ := Strata.saturated_coefficients_nonzero (frobenius K p) x e hx U V
    T.height 48999 hUle hVle hpair hH he herror hrank
  let G := GCDMonoid.gcd U V
  let C₀ := (Finset.univ : Finset E).filter (fun i => G.eval (x i) = 0)
  let S := C₀.image (fun i : E => i.val)
  obtain ⟨hC, hsum, _⟩ := Strata.normal_error_three_rank (frobenius K p) x e hx
    (fun i => hfix i.val) U V T.height 48999 hUle hVle hpair hH he herror hrank
  have hmax : max U.natDegree V.natDegree = T.height := by
    obtain ⟨hle, hred⟩ := Strata.gcd_reduction_degrees U V hU hV
    change max (U / G).natDegree (V / G).natDegree + G.natDegree = T.height at hsum
    change G.natDegree ≤ max U.natDegree V.natDegree at hle
    change max (U / G).natDegree (V / G).natDegree =
      max U.natDegree V.natDegree - G.natDegree at hred
    omega
  have hS_card : S.card = G.natDegree :=
    (Finset.card_image_of_injective C₀ Subtype.val_injective).trans hC
  have hS_error (i : I) (hi : i ∈ S) : M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i := by
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp j.property).2
  have hG : IsCommonGCD (locator node S) U V := by
    apply commonGCD_of_roots U V hV S _ hS_card
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp hj).2
  refine ⟨hU, hV, hmax, ⟨S, hS_error, hG⟩, ?_, valid_of_saturation R γ S hmax hG⟩
  intro i hi
  have hzero := (Finset.mem_filter.mp hi).2
  have hu0 : U.eval (node i) = 0 := by
    change (atSlope (leftU R) γ).eval (node i) = 0
    rw [eval_atSlope, hzero.1, eval_zero]
  have hv0 : V.eval (node i) = 0 := by
    change (atSlope (leftV R) γ).eval (node i) = 0
    rw [eval_atSlope, hzero.2, eval_zero]
  have hdiv : (Polynomial.X : K[X]) - C (node i) ∣ locator node S :=
    hG.2.2.2 _ (dvd_iff_isRoot.mpr hu0) (dvd_iff_isRoot.mpr hv0)
  have hroot : (locator node S).eval (node i) = 0 :=
    eval_eq_zero_of_dvd_of_eval_eq_zero hdiv (by rw [eval_sub, eval_X, eval_C, sub_self])
  exact hS_error i ((Principal.locator_eval_zero_iff node IRSProfile.domain.injective S i).mp hroot)

end
end K21_7
end Port_K1_7Proof

section Port_K1_3Proof
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

namespace K21_3
noncomputable section

open Polynomial Matrix Finset FrobeniusLocator
open scoped BigOperators

open K1_3 (deficient_hankel_count)
theorem proof : K21.c3 := by
  intro u Γ hrank hΓ
  have h := deficient_hankel_count K21.node (u 0) (u 1) K21.node.injective
    131072 48999 82073 (K21.firstRank u)
    (by rw [ProximityPrize.Benchmark.IRSProfile.card_index]) hrank rfl Γ
    (fun γ hγ => Native6921.native_IsMCA_badSlope u γ (hΓ γ hγ))
  rw [ProximityPrize.Benchmark.IRSProfile.card_index] at h
  omega

end
end K21_3
end Port_K1_3Proof

section Port_K1_5Proof
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000

namespace K21_5
noncomputable section

open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators

open private constantRankCount coefficientStack from ProximityPrize.SubmissionLower.Fast068
theorem proof : K21.c5 := by
  intro u Γ hu hΓ
  let φ := algebraMap K21.K[X] K21.Frac
  have hrank : ((K21.twoBlock u).map φ).rank = K21.stackRank u := rfl
  have hconstant : (coefficientStack K21.p K21.node (u 0) (u 1) 48999 82073).rank =
      K21.stackRank u := hu.symm
  have hcount := constantRankCount φ (IsFractionRing.injective K21.K[X] K21.Frac)
    K21.p (by norm_num [Native.p]) K21.node IRSProfile.domain.injective Native.native_domain_fixed
    (u 0) (u 1) 131072 180071 48999 82073 (by norm_num) (by norm_num)
    (by norm_num only [IRSProfile.card_index]) (K21.stackRank u) hrank hconstant
    Γ (fun γ hγ => Native6921.native_IsMCA_badSlope u γ (hΓ γ hγ))
  have hr : K21.stackRank u ≤ 82074 := by
    have h := Matrix.rank_le_card_width ((K21.twoBlock u).map φ)
    simpa only [hrank, Fintype.card_fin] using h
  calc
    Γ.card ≤ K21.p * K21.stackRank u := hcount
    _ ≤ K21.p * 82074 := Nat.mul_le_mul_left K21.p hr
    _ = 174875599782042 := by norm_num [Native.p]

end
end K21_5
end Port_K1_5Proof

section Port_K1_1Proof
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000

namespace K21_1
noncomputable section

open K1_1 (IndependentMoments level_profile level_of_profile principal_of_slice sliceDim sliceDim_succ)
open Polynomial Matrix FrobeniusLocator
open ProximityPrize.Benchmark

private def nativeMoments (u : K21.Words) : Fin 2 → ℕ → K21.Frac :=
  fun b j => algebraMap K21.K[X] K21.Frac
    (Principal.parameterSyndromes K21.p K21.node (u 0) (u 1) b j)

private theorem independent_nativeMoments (u : K21.Words)
    (h : ¬ K21.TypeAtMostOne u) : IndependentMoments (nativeMoments u) 131072 := by
  classical
  unfold IndependentMoments
  by_contra! hall
  apply h
  unfold K21.TypeAtMostOne Principal.TypeOneSyndromes
  rw [IRSProfile.card_index]
  intro i j
  apply IsFractionRing.injective K21.K[X] K21.Frac
  simpa [nativeMoments, Principal.parameterSyndromes, map_mul] using hall i j

private theorem locator_matrix (u : K21.Words) :
    Principal.recurrenceMatrix (nativeMoments u) 131072 82073 =
      (K21.twoBlock u).map (algebraMap K21.K[X] K21.Frac) :=
  Principal.recurrenceMatrix_parameter (algebraMap K21.K[X] K21.Frac)
    K21.p K21.node (u 0) (u 1) 131072 82073

private theorem locator_nullity (u : K21.Words) :
    sliceDim (nativeMoments u) 131072 82074 = K21.nullity u := by
  rw [sliceDim_succ (nativeMoments u) 131072 82073, locator_matrix]
  rfl

private theorem principal_of_one_active (u : K21.Words) (a : ℕ) (ha : a ≤ 82073)
    (hone : sliceDim (nativeMoments u) 131072 (a+1) = 1)
    (hnull : K21.nullity u = 82074-a) : K21.HomogeneousPrincipal u := by
  have hpos : 0 < sliceDim (nativeMoments u) 131072 (a+1) := by omega
  have hdim : sliceDim (nativeMoments u) 131072 82074 = (82073-a)+1 := by
    rw [locator_nullity]
    omega
  obtain ⟨g, hg, hdeg, hfac⟩ := principal_of_slice (nativeMoments u) 131072 a 82073
    ha (by decide) hpos hdim
  refine ⟨a, g, hg, hdeg, ha, fun P hP => ?_⟩
  rw [← locator_matrix]
  exact hfac P hP

theorem proof : K21.c1 := by
  intro u hu
  obtain ⟨a, b, c, hab, hbc, hc, hsum, hdim⟩ := level_profile
    (nativeMoments u) 131072 (independent_nativeMoments u hu.2.2.1)
  have hloc := hdim 82074 (by decide)
  rw [locator_nullity] at hloc
  have hpos := hu.1
  have hinactive : 82073 < c := by omega
  have ha : a ≤ 82073 := by omega
  have hb : b ≤ 82073 := by
    by_contra hb
    have hsmall := hdim (a+1) (by omega)
    exact hu.2.2.2.1 (principal_of_one_active u a ha (by omega) (by omega))
  refine ⟨⟨a, b, c, hab, hb, hinactive, hc, hsum, by omega, ?_⟩⟩
  exact level_of_profile _ _ _ _ _ hdim

end
end K21_1
end Port_K1_1Proof
