import ProximityPrize.SubmissionLower.Koala6831MovingShortenedCut
import ProximityPrize.SubmissionLower.Koala6831OrdinaryIncidence

namespace ProximityPrize.SubmissionLower.Koala6831MovingPairIncidence

open scoped Classical BigOperators
open RCN001 RCN002 RCN003 RCN005 RCN037 RCN041 RCN046 RCN065 RCN095 RCN136 RCN165 RCN231 RCN237 RCN238
open RCN243 RCN263 RCN264 RCN265 RCN275 RCN277 RCN313 RCN319 RCN341 RCN344
open Koala6831MovingShortenedCut (exists_prime_shortened_cut)
open Koala6831OrdinaryIncidence (lengthAverage nodeAverage incidence_le_shortened_scaled)

noncomputable section

private def profile (z yz all : ℕ) (r : FlagDegree) : ℕ :=
  r.zOnly * z + r.yz * yz + r.all * all

private theorem shortened_profile (support : ResidualSupportParameters) (u z yz all : ℕ) :
    profile z yz all (reducedResidualAgreementFlag support u) =
      yz + profile z yz all (reducedAgreementDirection support) * u := by
  simp only [profile, reducedResidualAgreementFlag]
  ring

variable {K E : Type} [Field K] [Field E] [IsAlgClosed E]

theorem prime_seed_card_le (φ : Polynomial K →+* E) (hφ : Function.Injective φ)
    (P : Ideal (MvPolynomial (Fin 3) E)) [P.IsPrime]
    (hnonpoint : ∀ q : Fin 3 → E, P ≠ RingHom.ker (MvPolynomial.aeval q).toRingHom)
    (support : ResidualSupportParameters) {F : MvPolynomial (Fin 4) K}
    (hData : ResidualSupportData support F) (hF : surfaceMap φ F ∈ P)
    (hH : surfaceMap φ (polyH K F) ∉ P)
    (selected : K → Polynomial K) (Γ : Finset K)
    {Node : Type*} (nodes : Finset Node) (x u₀ u₁ : Node → K) (hx : Set.InjOn x nodes)
    (p w A e : ℕ) [CharP E p] (hw : 1 ≤ w) (hchar : w < p) (hwA : w < A) (hAn : A ≤ nodes.card)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0)
    (hregular : ∀ γ ∈ Γ, MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X)) (polyH K F) ≠ 0)
    (hpoint : ∀ γ ∈ Γ, P ≤ RingHom.ker (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
    (hagreement : ∀ γ ∈ Γ, A ≤ (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w e)
    (z yz all : ℕ) (budget : PrimeFlagZeroBudget P (profile z yz all))
    (hz : Transcendental E (coordinate E P 2) → 1 ≤ z) :
    (Γ.card : ℚ) ≤ (profile z yz all (reducedAgreementDirection support) : ℚ) *
      lengthAverage nodes.card w A + yz * nodeAverage nodes.card w A + (e + 1) * z := by
  classical
  let I := identityNodes φ P F nodes x u₀ u₁ w
  let agrees (γ : K) (i : Node) := (selected γ).eval (x i) = u₀ i + γ * u₁ i
  have hlengthCoeff : 0 ≤ lengthAverage nodes.card w A := by unfold lengthAverage; positivity
  have hnodeCoeff : 0 ≤ nodeAverage nodes.card w A := by
    unfold nodeAverage
    apply div_nonneg <;> apply sub_nonneg.mpr
    · exact_mod_cast hwA.le.trans hAn
    · exact_mod_cast hwA.le
  by_cases hshort : I.card ≤ w
  · have hfiber (i : Node) (hi : i ∈ nodes \ I) :
        (Γ.filter (fun γ => agrees γ i)).card * 1 ≤
          yz + profile z yz all (reducedAgreementDirection support) * (w - I.card) := by
      obtain ⟨hiNode, hiI⟩ := Finset.mem_sdiff.mp hi
      obtain ⟨cut, hflag, hproper, hvan⟩ := exists_prime_shortened_cut φ hφ P support hData hF hH
        selected Γ nodes x u₀ u₁ hx p w hchar hdegree hsolution hregular hpoint hshort i hiNode hiI
      let points := (Γ.filter (fun γ => agrees γ i)).image (selectedPoint φ selected)
      have hcP (q : Fin 3 → E) (hq : q ∈ points) :
          P ≤ RingHom.ker (MvPolynomial.aeval q).toRingHom := by
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hq
        exact hpoint γ (Finset.mem_filter.mp hγ).1
      have hcZ (q : Fin 3 → E) (hq : q ∈ points) : MvPolynomial.aeval q cut = 0 := by
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hq
        exact hvan γ (Finset.mem_filter.mp hγ).1 (Finset.mem_filter.mp hγ).2
      have hcount := budget.zero_le _ _ hflag hproper points hcP hcZ
      rw [show points.card = (Γ.filter (fun γ => agrees γ i)).card from
        Finset.card_image_of_injective _ (selectedPoint_injective φ selected), shortened_profile] at hcount
      simpa only [Nat.mul_one] using hcount
    have hinc := incidence_le_shortened_scaled agrees Γ nodes I A w 1
      (profile z yz all (reducedAgreementDirection support)) yz Nat.one_pos
      (identityNodes_subset φ P F nodes x u₀ u₁ w) hshort hwA hAn hagreement hfiber
    rw [Nat.cast_one, mul_one] at hinc
    exact hinc.trans (le_add_of_nonneg_right (by positivity))
  · have hlong : w < I.card := Nat.lt_of_not_ge hshort
    have hvalues (t : {γ : K // γ ∈ Γ}) : ∀ i ∈ I,
        (selected t.1).eval (x i) = u₀ i + t.1 * u₁ i :=
      selected_agrees_on_identity_nodes φ P F nodes x u₀ u₁ p w hchar
        (selected t.1) t.1 (hdegree t.1 t.2) (hsolution t.1 t.2) (hregular t.1 t.2) (hpoint t.1 t.2)
    obtain ⟨P₀, P₁, h₀, h₁, _, hpencil⟩ := exists_common_pencil_of_many_identities
      φ P F hF hH nodes x u₀ u₁ w hx hlong (fun t : {γ : K // γ ∈ Γ} => t.1)
      (fun t => selected t.1) (fun t => hdegree t.1 t.2) hvalues
    have hfilter : Γ.filter (fun γ => selected γ = P₀ + Polynomial.C γ * P₁) = Γ :=
      Finset.filter_eq_self.mpr fun γ hγ => hpencil ⟨γ, hγ⟩
    have hf : Γ.card ≤ e + 1 := by simpa only [hfilter] using hnoPencil P₀ P₁ h₀ h₁
    have hzpos := hz (seed_transcendental_of_many_identities φ P F hF hH nodes x u₀ u₁ w hw
      hx hlong hnonpoint)
    have hbound : Γ.card ≤ (e + 1) * z :=
      hf.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (e + 1) hzpos)
    exact (show (Γ.card : ℚ) ≤ (e + 1) * z by exact_mod_cast hbound).trans
      (le_add_of_nonneg_left (by positivity))

private theorem selected_eval_surface (φ : Polynomial K →+* E) (selected : K → Polynomial K)
    (γ : K) (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ F) =
      φ (specialization K (selected γ) γ F) := by
  rw [selectedPoint_evaluation, eval_polynomialPoint_eq_specialization]
  have h : Polynomial.eval₂RingHom (φ.comp Polynomial.C) (φ Polynomial.X) = φ := by
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp
  exact DFunLike.congr_fun h _

theorem prime_fold_seed_card_le (φ : Polynomial K →+* E) (hφ : Function.Injective φ)
    (P : Ideal (MvPolynomial (Fin 3) E)) [P.IsPrime]
    (hnonpoint : ∀ q : Fin 3 → E, P ≠ RingHom.ker (MvPolynomial.aeval q).toRingHom)
    (support : ResidualSupportParameters) {F : MvPolynomial (Fin 4) K}
    (hData : ResidualSupportData support F) (hF : surfaceMap φ F ∈ P)
    (hH : surfaceMap φ (polyH K F) ∉ P)
    (sharp : FlagDegree) (hsharp : PolynomialInFlag sharp (surfaceMap φ (polyH K F)))
    (selected : K → Polynomial K) (Γ : Finset K)
    {Node : Type*} (nodes : Finset Node) (x u₀ u₁ : Node → K) (hx : Set.InjOn x nodes)
    (p w A e : ℕ) [CharP E p] (hw : 1 ≤ w) (hchar : w < p) (hwA : w < A) (hAn : A ≤ nodes.card)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hpoint : ∀ γ ∈ Γ, P ≤ RingHom.ker (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
    (hagreement : ∀ γ ∈ Γ, A ≤ (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w e)
    (z yz all : ℕ) (budget : PrimeFlagZeroBudget P (profile z yz all))
    (hz : Transcendental E (coordinate E P 2) → 1 ≤ z) :
    (Γ.card : ℚ) ≤ (profile z yz all (reducedAgreementDirection support) : ℚ) *
      lengthAverage nodes.card w A + yz * nodeAverage nodes.card w A + (e + 1) * z +
      profile z yz all sharp := by
  classical
  let separant := surfaceMap φ (polyH K F)
  let point := selectedPoint φ selected
  let regular := Γ.filter (fun γ => MvPolynomial.eval (point γ) separant ≠ 0)
  let singular := Γ.filter (fun γ => MvPolynomial.eval (point γ) separant = 0)
  have hsub : regular ⊆ Γ := Finset.filter_subset _ _
  have hreg (γ : K) (hγ : γ ∈ regular) : MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X)) (polyH K F) ≠ 0 := by
    rw [← selectedPoint_evaluation]
    exact (Finset.mem_filter.mp hγ).2
  have hsolution (γ : K) (hγ : γ ∈ Γ) : specialization K (selected γ) γ F = 0 := by
    apply hφ
    rw [map_zero, ← selected_eval_surface]
    exact hpoint γ hγ hF
  have hr := prime_seed_card_le φ hφ P hnonpoint support hData hF hH selected regular
    nodes x u₀ u₁ hx p w A e hw hchar hwA hAn
    (fun γ hγ => hdegree γ (hsub hγ)) (fun γ hγ => hsolution γ (hsub hγ)) hreg
    (fun γ hγ => hpoint γ (hsub hγ)) (fun γ hγ => hagreement γ (hsub hγ))
    (noLargeSelectedPencil_mono selected Γ regular w e hsub hnoPencil) z yz all budget hz
  have hs : singular.card ≤ profile z yz all sharp := by
    let points := singular.image point
    have hcP (q : Fin 3 → E) (hq : q ∈ points) :
        P ≤ RingHom.ker (MvPolynomial.aeval q).toRingHom := by
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hq
      exact hpoint γ (Finset.mem_filter.mp hγ).1
    have hcZ (q : Fin 3 → E) (hq : q ∈ points) : MvPolynomial.aeval q separant = 0 := by
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hq
      exact (Finset.mem_filter.mp hγ).2
    have hcount := budget.zero_le sharp separant hsharp hH points hcP hcZ
    rwa [show points.card = singular.card from
      Finset.card_image_of_injective _ (selectedPoint_injective φ selected)] at hcount
  have hsplit : regular.card + singular.card = Γ.card := by
    simpa only [regular, singular, not_not] using
      Finset.card_filter_add_card_filter_not (s := Γ)
        (fun γ => MvPolynomial.eval (point γ) separant ≠ 0)
  have hsplitRat : (regular.card : ℚ) + singular.card = Γ.card := by exact_mod_cast hsplit
  rw [← hsplitRat]
  exact add_le_add hr (by exact_mod_cast hs)

theorem regular_pair_seed_card_le (φ : Polynomial K →+* E) (hφ : Function.Injective φ)
    (support : ResidualSupportParameters) {F : MvPolynomial (Fin 4) K}
    (hData : ResidualSupportData support F) (G T : MvPolynomial (Fin 3) E)
    (hdiv : G ∣ surfaceMap φ F) (left right : FlagDegree)
    (B : PrimeFlagBudgetFamily (G := G) (T := T) (H := regularitySurface φ F) left right)
    (hz : ∀ C : RegularComponent E G T (regularitySurface φ F),
      Transcendental E (coordinate E C.1 2) → 1 ≤ B.zCost C)
    (selected : K → Polynomial K) (Γ : Finset K)
    {Node : Type*} (nodes : Finset Node) (x u₀ u₁ : Node → K) (hx : Set.InjOn x nodes)
    (p w A e : ℕ) [CharP E p] (hw : 1 ≤ w) (hchar : w < p) (hwA : w < A) (hAn : A ≤ nodes.card)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0)
    (hregular : ∀ γ ∈ Γ, MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X)) (polyH K F) ≠ 0)
    (hGpoint : ∀ γ ∈ Γ, MvPolynomial.eval (selectedPoint φ selected γ) G = 0)
    (hTpoint : ∀ γ ∈ Γ, MvPolynomial.eval (selectedPoint φ selected γ) T = 0)
    (hagreement : ∀ γ ∈ Γ, A ≤ (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w e) :
    (Γ.card : ℚ) ≤ (flagMixed left right (reducedAgreementDirection support) : ℚ) *
      lengthAverage nodes.card w A + flagMixed left right unitYZFlag * nodeAverage nodes.card w A +
      (e + 1) * flagMixed left right unitZFlag := by
  classical
  let H := regularitySurface φ F
  let Comp := RegularComponent E G T H
  let point := selectedPoint φ selected
  let seeds (C : Comp) := componentSeeds E G T H Γ point C
  have hHpoint (γ : K) (hγ : γ ∈ Γ) : MvPolynomial.eval (point γ) H ≠ 0 := by
    change MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ (polyH K F)) ≠ 0
    rw [selectedPoint_evaluation]
    exact hregular γ hγ
  have hcover : (Γ.card : ℚ) ≤ ∑ C : Comp, ((seeds C).card : ℚ) := by
    exact_mod_cast (card_le_sum_componentSeeds E G T H Γ point hGpoint hTpoint hHpoint)
  let D := reducedAgreementDirection support
  let lengthCoeff := lengthAverage nodes.card w A
  let nodeCoeff := nodeAverage nodes.card w A
  have hlengthCoeff : 0 ≤ lengthCoeff := by dsimp [lengthCoeff, lengthAverage]; positivity
  have hnodeCoeff : 0 ≤ nodeCoeff := by
    dsimp [nodeCoeff, nodeAverage]
    apply div_nonneg <;> apply sub_nonneg.mpr
    · exact_mod_cast hwA.le.trans hAn
    · exact_mod_cast hwA.le
  have hcomp (C : Comp) : ((seeds C).card : ℚ) ≤
      (B.weightedCost D C : ℚ) * lengthCoeff + B.yzCost C * nodeCoeff + (e + 1) * B.zCost C := by
    have hsub := componentSeeds_subset E G T H Γ point C
    have hFmem : surfaceMap φ F ∈ C.1 :=
      ((Ideal.span_singleton_le_iff_mem (I := C.1)).mpr (regularComponent_G_mem E G T H C))
        (Ideal.mem_span_singleton.mpr hdiv)
    have count := prime_seed_card_le φ hφ C.1 (regularComponent_ne_point E G T H C)
      support hData hFmem (regularComponent_H_not_mem E G T H C) selected (seeds C)
      nodes x u₀ u₁ hx p w A e hw hchar hwA hAn
      (fun γ hγ => hdegree γ (hsub hγ)) (fun γ hγ => hsolution γ (hsub hγ))
      (fun γ hγ => hregular γ (hsub hγ))
      (fun γ hγ => componentSeeds_on_prime E G T H Γ point C γ hγ)
      (fun γ hγ => hagreement γ (hsub hγ))
      (noLargeSelectedPencil_mono selected Γ _ w e hsub hnoPencil)
      (B.zCost C) (B.yzCost C) (B.allCost C) (B.primeBudget C) (hz C)
    exact count
  have hsumD : (∑ C : Comp, (B.weightedCost D C : ℚ)) ≤ flagMixed left right D := by
    exact_mod_cast B.sum_weightedCost_le D
  have hsumYZ : (∑ C : Comp, (B.yzCost C : ℚ)) ≤ flagMixed left right unitYZFlag := by
    exact_mod_cast B.sum_yzCost_le
  have hsumZ : (∑ C : Comp, (B.zCost C : ℚ)) ≤ flagMixed left right unitZFlag := by
    exact_mod_cast B.sum_zCost_le
  calc
    _ ≤ ∑ C : Comp, ((seeds C).card : ℚ) := hcover
    _ ≤ ∑ C : Comp, ((B.weightedCost D C : ℚ) * lengthCoeff + B.yzCost C * nodeCoeff + (e + 1) * B.zCost C) :=
      Finset.sum_le_sum fun C _ => hcomp C
    _ = (∑ C : Comp, (B.weightedCost D C : ℚ)) * lengthCoeff +
        (∑ C : Comp, (B.yzCost C : ℚ)) * nodeCoeff + (e + 1) * ∑ C : Comp, (B.zCost C : ℚ) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
    _ ≤ _ := add_le_add (add_le_add (mul_le_mul_of_nonneg_right hsumD hlengthCoeff)
      (mul_le_mul_of_nonneg_right hsumYZ hnodeCoeff)) (mul_le_mul_of_nonneg_left hsumZ (by positivity))

theorem fold_pair_seed_card_le_of_component_carriers
    (φ : Polynomial K →+* E) (hφ : Function.Injective φ)
    (support : ResidualSupportParameters) (G T H : MvPolynomial (Fin 3) E)
    (left right sharp : FlagDegree)
    (B : PrimeFlagBudgetFamily (G := G) (T := T) (H := H) left right)
    (hz : ∀ C : RegularComponent E G T H, Transcendental E (coordinate E C.1 2) → 1 ≤ B.zCost C)
    (hcarrier : ∀ C : RegularComponent E G T H, ∃ F : MvPolynomial (Fin 4) K,
      ResidualSupportData support F ∧ surfaceMap φ F ∈ C.1 ∧ surfaceMap φ (polyH K F) ∉ C.1 ∧
      PolynomialInFlag sharp (surfaceMap φ (polyH K F)))
    (selected : K → Polynomial K) (Γ : Finset K)
    {Node : Type*} (nodes : Finset Node) (x u₀ u₁ : Node → K) (hx : Set.InjOn x nodes)
    (p w A e : ℕ) [CharP E p] (hw : 1 ≤ w) (hchar : w < p) (hwA : w < A) (hAn : A ≤ nodes.card)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hGpoint : ∀ γ ∈ Γ, MvPolynomial.eval (selectedPoint φ selected γ) G = 0)
    (hTpoint : ∀ γ ∈ Γ, MvPolynomial.eval (selectedPoint φ selected γ) T = 0)
    (hHpoint : ∀ γ ∈ Γ, MvPolynomial.eval (selectedPoint φ selected γ) H ≠ 0)
    (hagreement : ∀ γ ∈ Γ, A ≤ (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w e) :
    (Γ.card : ℚ) ≤ (flagMixed left right (reducedAgreementDirection support) : ℚ) *
      lengthAverage nodes.card w A + flagMixed left right unitYZFlag * nodeAverage nodes.card w A +
      (e + 1) * flagMixed left right unitZFlag + flagMixed left right sharp := by
  classical
  let Comp := RegularComponent E G T H
  let point := selectedPoint φ selected
  let seeds (C : Comp) := componentSeeds E G T H Γ point C
  have hcover : (Γ.card : ℚ) ≤ ∑ C : Comp, ((seeds C).card : ℚ) := by
    exact_mod_cast (card_le_sum_componentSeeds E G T H Γ point hGpoint hTpoint hHpoint)
  let D := reducedAgreementDirection support
  let a := lengthAverage nodes.card w A
  let b := nodeAverage nodes.card w A
  have ha : 0 ≤ a := by dsimp [a, lengthAverage]; positivity
  have hb : 0 ≤ b := by
    dsimp [b, nodeAverage]
    apply div_nonneg <;> apply sub_nonneg.mpr
    · exact_mod_cast hwA.le.trans hAn
    · exact_mod_cast hwA.le
  have hcomp (C : Comp) : ((seeds C).card : ℚ) ≤ (B.weightedCost D C : ℚ) * a +
      B.yzCost C * b + (e + 1) * B.zCost C + B.weightedCost sharp C := by
    have hsub := componentSeeds_subset E G T H Γ point C
    obtain ⟨F, hData, hFmem, hreg, hsharp⟩ := hcarrier C
    exact prime_fold_seed_card_le φ hφ C.1 (regularComponent_ne_point E G T H C)
      support hData hFmem hreg sharp hsharp selected (seeds C) nodes x u₀ u₁ hx p w A e hw hchar hwA hAn
      (fun γ hγ => hdegree γ (hsub hγ))
      (fun γ hγ => componentSeeds_on_prime E G T H Γ point C γ hγ)
      (fun γ hγ => hagreement γ (hsub hγ))
      (noLargeSelectedPencil_mono selected Γ _ w e hsub hnoPencil)
      (B.zCost C) (B.yzCost C) (B.allCost C) (B.primeBudget C) (hz C)
  have hsumD : (∑ C : Comp, (B.weightedCost D C : ℚ)) ≤ flagMixed left right D := by
    exact_mod_cast B.sum_weightedCost_le D
  have hsumYZ : (∑ C : Comp, (B.yzCost C : ℚ)) ≤ flagMixed left right unitYZFlag := by
    exact_mod_cast B.sum_yzCost_le
  have hsumZ : (∑ C : Comp, (B.zCost C : ℚ)) ≤ flagMixed left right unitZFlag := by
    exact_mod_cast B.sum_zCost_le
  have hsumSharp : (∑ C : Comp, (B.weightedCost sharp C : ℚ)) ≤ flagMixed left right sharp := by
    exact_mod_cast B.sum_weightedCost_le sharp
  calc
    _ ≤ ∑ C : Comp, ((seeds C).card : ℚ) := hcover
    _ ≤ ∑ C : Comp, ((B.weightedCost D C : ℚ) * a + B.yzCost C * b +
        (e + 1) * B.zCost C + B.weightedCost sharp C) := Finset.sum_le_sum fun C _ => hcomp C
    _ = (∑ C : Comp, (B.weightedCost D C : ℚ)) * a +
        (∑ C : Comp, (B.yzCost C : ℚ)) * b + (e + 1) * (∑ C : Comp, (B.zCost C : ℚ)) +
        (∑ C : Comp, (B.weightedCost sharp C : ℚ)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_mul,
        Finset.sum_mul, Finset.mul_sum]
    _ ≤ _ := add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_right hsumD ha)
      (mul_le_mul_of_nonneg_right hsumYZ hb)) (mul_le_mul_of_nonneg_left hsumZ (by positivity))) hsumSharp

theorem exists_pair_budget_of_active_coordinates (G T H : MvPolynomial (Fin 3) E)
    (p : ℕ) [CharP E p] (left right : FlagDegree)
    (hG : Irreducible G) (hproper : ¬ G ∣ T)
    (hdep : 0 < G.degreeOf (1 : Fin 3)) (hderiv : MvPolynomial.pderiv (1 : Fin 3) G ≠ 0)
    (hGflag : PolynomialInFlag left G) (hTflag : PolynomialInFlag right T)
    (hleft : left.zOnly + left.yz + left.all < p)
    (hmixed : (right.yz + right.all) * left.all + (left.yz + left.all) * right.all < p)
    (hYZ : ∀ C : RegularComponent E G T H,
      Transcendental E (coordinate E C.1 0) ∨ Transcendental E (coordinate E C.1 2)) :
    ∃ B : PrimeFlagBudgetFamily (G := G) (T := T) (H := H) left right,
      ∀ C : RegularComponent E G T H,
        Transcendental E (coordinate E C.1 2) → 1 ≤ B.zCost C := by
  classical
  obtain ⟨hGY, hGR, _⟩ := RCN314.degree_bounds_of_polynomialInFlag hGflag
  obtain ⟨hTY, hTR, _⟩ := RCN314.degree_bounds_of_polynomialInFlag hTflag
  have hGdegree (i : Fin 3) : G.degreeOf i < p :=
    (RCN084.degreeOf_le_flag_total G left hGflag i).trans_lt hleft
  have hmixZ : coordinateMixedDegree E G T 2 < p := by
    rw [coordinateMixedDegree_two]
    exact (Nat.add_le_add (Nat.mul_le_mul hTY hGR) (Nat.mul_le_mul hGY hTR)).trans_lt hmixed
  let choiceData (C : RegularComponent E G T H) :=
    exists_separableLiteralCoordinate_y_or_z C.1 p G T hG
      (regularComponent_G_mem E G T H C) (regularComponent_T_mem E G T H C)
      hproper hdep hGdegree hmixZ (hYZ C)
  let base (C : RegularComponent E G T H) : SeparableLiteralCoordinate C.1 := (choiceData C).choose
  have hactive (C : RegularComponent E G T H) :
      KaehlerDifferential.D E (CoordinateField E C.1) (coordinate E C.1 0) ≠ 0 ∨
      KaehlerDifferential.D E (CoordinateField E C.1) (coordinate E C.1 2) ≠ 0 := by
    have hb := base_differential_ne_zero (base C)
    have hc : (base C).index = 0 ∨ (base C).index = 2 := (choiceData C).choose_spec
    rcases hc with h₀ | h₂
    · left
      simpa only [h₀] using hb
    · right
      simpa only [h₂] using hb
  have hZ (C : RegularComponent E G T H) : LiteralProjectionGate C 2 := by
    intro htr
    exact finite_separable_at_of_original_coordinate_gate E C.1 2 htr p G T hG
      (regularComponent_G_mem E G T H C) (regularComponent_T_mem E G T H C)
      hproper hGdegree hmixZ
  obtain ⟨family⟩ := exists_adaptiveUnitProjectionFamilyYZ_of_active_nested left right base hactive hZ
    hderiv hG hproper ((support_subset_flagSupport_iff _ _).mpr hGflag)
    ((support_subset_flagSupport_iff _ _).mpr hTflag)
  exact ⟨family.family.toPrimeFlagBudgetFamily,
    family.family.one_le_toPrimeFlagBudgetFamily_zCost⟩

theorem exists_regular_pair_budget (φ : Polynomial K →+* E)
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) E)
    (p : ℕ) [CharP E p] (left right : FlagDegree) (hdiv : G ∣ surfaceMap φ F)
    (hG : Irreducible G) (hproper : ¬ G ∣ T)
    (hdep : 0 < G.degreeOf (1 : Fin 3)) (hderiv : MvPolynomial.pderiv (1 : Fin 3) G ≠ 0)
    (hGflag : PolynomialInFlag left G) (hTflag : PolynomialInFlag right T)
    (hleft : left.zOnly + left.yz + left.all < p)
    (hmixed : (right.yz + right.all) * left.all + (left.yz + left.all) * right.all < p) :
    ∃ B : PrimeFlagBudgetFamily (G := G) (T := T) (H := regularitySurface φ F) left right,
      ∀ C : RegularComponent E G T (regularitySurface φ F),
        Transcendental E (coordinate E C.1 2) → 1 ≤ B.zCost C :=
  exists_pair_budget_of_active_coordinates G T (regularitySurface φ F) p left right hG hproper
    hdep hderiv hGflag hTflag hleft hmixed (regularComponent_y_or_z_transcendental φ F G T hdiv)

def scaledPairFlag (support : ResidualSupportParameters) (n w A e : ℕ) : FlagDegree :=
  (n * w * (A - w)) • reducedAgreementDirection support + ((n - w) * A) • unitYZFlag +
    ((e + 1) * (A * (A - w))) • unitZFlag

theorem mul_scale_le_of_pair_bound (support : ResidualSupportParameters)
    (n w A e count : ℕ) (left right : FlagDegree) (hwA : w < A) (hAn : A ≤ n)
    (hcount : (count : ℚ) ≤ (flagMixed left right (reducedAgreementDirection support) : ℚ) *
      lengthAverage n w A + flagMixed left right unitYZFlag * nodeAverage n w A +
      (e + 1) * flagMixed left right unitZFlag) :
    count * (A * (A - w)) ≤ flagMixed left right (scaledPairFlag support n w A e) := by
  have hA : (A : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.zero_le w |>.trans_lt hwA)
  have hAw : (A : ℚ) - w ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast Nat.ne_of_gt hwA)
  have hlength : lengthAverage n w A * (↑(A * (A - w)) : ℚ) = (↑(n * w * (A - w)) : ℚ) := by
    unfold lengthAverage
    push_cast [Nat.cast_sub hwA.le]
    field_simp
  have hnode : nodeAverage n w A * (↑(A * (A - w)) : ℚ) = (↑((n - w) * A) : ℚ) := by
    unfold nodeAverage
    push_cast [Nat.cast_sub hwA.le, Nat.cast_sub (hwA.le.trans hAn)]
    field_simp
  have h := mul_le_mul_of_nonneg_right hcount (show (0 : ℚ) ≤ ↑(A * (A - w)) by positivity)
  rw [add_mul, add_mul, mul_assoc (flagMixed left right (reducedAgreementDirection support) : ℚ),
    mul_assoc (flagMixed left right unitYZFlag : ℚ), hlength, hnode] at h
  have hn : count * (A * (A - w)) ≤
      flagMixed left right (reducedAgreementDirection support) * (n * w * (A - w)) +
      flagMixed left right unitYZFlag * ((n - w) * A) +
      (e + 1) * flagMixed left right unitZFlag * (A * (A - w)) := by exact_mod_cast h
  refine hn.trans_eq ?_
  simp only [scaledPairFlag, flagMixed, unitZFlag, unitYZFlag, add_zOnly, add_yz, add_all,
    nsmul_zOnly, nsmul_yz, nsmul_all]
  ring

end

end ProximityPrize.SubmissionLower.Koala6831MovingPairIncidence
