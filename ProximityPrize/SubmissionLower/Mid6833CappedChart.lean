/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833WeightCaps
import ProximityPrize.SubmissionLower.Mid6833MiddleCaps
import ArkLib.ToMathlib.RingTheory.Nullstellensatz.CappedBidegreeIncidence
import ArkLib.ToMathlib.RingTheory.Nullstellensatz.BidegreeIncidence
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.ComponentDimension

namespace KoalaBiJet
open MvPolynomial PolynomialDifferential
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000
variable {F : Type*} [Field F]
private abbrev eC : Fin 3 ≃ Option (Fin 2) := finSuccEquiv' (Fin.last 2)

private theorem rectBase (f : MvPolynomial (Fin 3) F) {a b : ℕ}
    (ha : f.degreeOf 2 ≤ a) (hb : f.totalDegree ≤ b) :
    rename eC f ∈ restrictBidegree (Fin 2) F a b := by
  classical
  let g := rename eC f
  apply mem_restrictBidegree_iff_weightedTotalDegree_le.mpr
  constructor
  · have eqw : (fun v : Option (Fin 2) ↦ v.elim (1:ℕ) fun _ ↦ 0) = Pi.single none 1 := by
      funext i; cases i <;> simp
    rw [eqw,weightedTotalDegree_piSingle]
    have h := degreeOf_rename_of_injective (p:=f) eC.injective (Fin.last 2)
    rw [show eC (Fin.last 2)=none by exact finSuccEquiv'_at _] at h
    exact h.trans_le ha
  · have old : weightedTotalDegree (fun _ : Option (Fin 2) => (1:ℕ)) g ≤ b := by
      classical
      change weightedTotalDegree 1 g ≤ b
      rw [weightedTotalDegree_one]
      exact (totalDegree_rename_le eC f).trans hb
    rw [weightedTotalDegree,Finset.sup_le_iff] at old ⊢
    intro m hm
    refine le_trans ?_ (old m hm)
    rw [Finsupp.weight_apply,Finsupp.weight_apply]
    apply Finset.sum_le_sum
    intro i _
    cases i <;> simp


private theorem degreeOf_initialJetEquation_le_var {r : ℕ} (center : F)
    (Q : DifferentialPolynomial F r) (a : Fin (r+1)) :
    (initialJetEquation center Q).degreeOf a ≤ Q.degreeOf (some a) := by
  rw [← weightedTotalDegree_piSingle, ← weightedTotalDegree_piSingle (some a)]
  apply weightedTotalDegree_aeval_le_of_le
  intro i
  cases i with
  | none => simp
  | some j =>
    by_cases hj : j = a
    · subst j
      simp [weightedTotalDegree_piSingle]
    · simp [weightedTotalDegree_piSingle, degreeOf_X, Ne.symm hj]

private theorem cappedRectangle (f : MvPolynomial (Fin 3) F) {a b c : ℕ}
    (ha : f.degreeOf 2 ≤ a) (hb : f.totalDegree ≤ b) (hc : f.degreeOf 1 ≤ c) :
    rename eC f ∈ restrictCappedBidegree (Fin 2) F 1 a b c := by
  apply mem_restrictCappedBidegree.mpr
  intro m hm
  have old := mem_restrictBidegree.mp (rectBase f ha hb) m hm
  refine ⟨old.1,old.2,?_⟩
  have h := degreeOf_rename_of_injective (p:=f) eC.injective (1:Fin 3)
  rw [show eC 1 = some (1:Fin 2) by decide] at h
  exact (monomial_le_degreeOf _ hm).trans (h.trans_le hc)

/-- Separate the highest initial jet from the other two on the fixed-word
regular chart, using ArkLib's bidegree incidence theorem in three variables. -/
theorem capped_jets [IsAlgClosed F] (center : F) (Q : DifferentialPolynomial F 2)
    {K τ n A h j v a b c r : ℕ} (hK : 2<K) (hkA : K≤A)
    (hτ : TaylorExponentSufficient 2 K τ) (hv : 2≤v) (ha : 0<a) (hb : 0<b)
    (hc : 0<c) (hrc : r≤c) (hlocal : jetDegree Q 1≤r)
    (hcap : Q.weightedTotalDegree (indexWeight 3) ≤ v)
    (hdeg : jetTotalDegree Q ≤ j) (hderiv : jetDegree Q 2 ≤ h)
    (hjb : j ≤ b) (hha : h ≤ a) (hbdeg : rationalTaylorCutDegreeBound Q τ ≤ b)
    (hadeg : (τ*(v-2)+(K-1))/2 ≤ a)
    (hcdeg : τ*(v-2)+(K-1) ≤ c)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (S : Finset (Fin 3 → F))
    (hS : ∀ x∈S, aeval x (initialJetEquation center Q)=0 ∧ aeval x (initialJetSeparant center Q)≠0)
    (hA : ∀ x∈S, A ≤ {i | aeval x (taylorAgreementEquation center Q K τ
      (domain i) (received i))=0}.ncard) :
    (S.card:ℚ) ≤ (cappedBidegreeMixedVolume h j r a b c : ℕ) * (((n-K+1:ℕ):ℚ)/((A-K+1:ℕ):ℚ))^2 := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨x₀,hx₀⟩
  · simp only [Finset.card_empty,Nat.cast_zero]
    positivity
  let g := initialJetEquation center Q
  let s := initialJetSeparant center Q
  let cuts (i : Fin n) := taylorAgreementEquation center Q K τ (domain i) (received i)
  let φ : MvPolynomial (Fin 3) F →ₐ[F] MvPolynomial (Option (Fin 2)) F := rename eC
  have φsurj : Function.Surjective φ := (renameEquiv F eC).surjective
  let lift (x : Fin 3 → F) : Option (Fin 2) → F := x ∘ eC.symm
  have evalEq (x : Fin 3 → F) (f : MvPolynomial (Fin 3) F) :
      aeval (lift x) (φ f) = aeval x f := by
    simp [φ, lift,aeval_rename,Function.comp_assoc]
  have hg0 : φ g ≠ 0 := fun h0 => (initialJetEquation_ne_zero_of_initialJetSeparant_ne_zero
    center Q (fun hs => (hS x₀ hx₀).2 (by rw [hs,map_zero]))) ((renameEquiv F eC).injective (h0.trans (map_zero φ).symm))
  have hproper : Ideal.span ({φ g} : Set _) ≠ ⊤ := by
    intro eq
    have sk : Ideal.span ({φ g} : Set _) ≤ RingHom.ker (aeval (lift x₀) : _ →ₐ[F] F).toRingHom := by
      rw [Ideal.span_singleton_le_iff_mem,RingHom.mem_ker]
      exact (evalEq x₀ g).trans (hS x₀ hx₀).1
    have h1 := sk (eq.symm ▸ (Submodule.mem_top : (1 : MvPolynomial (Option (Fin 2)) F) ∈ (⊤ : Ideal _)))
    simpa [RingHom.mem_ker] using h1
  have hgder : g.degreeOf 2 ≤ h := (degreeOf_initialJetEquation_le center Q).trans hderiv
  have hgt : g.totalDegree ≤ j := (totalDegree_initialJetEquation_le center Q).trans hdeg
  have hsder : s.degreeOf 2 ≤ a := (degreeOf_initialJetSeparant_le center Q).trans
    ((Nat.sub_le _ _).trans (hderiv.trans hha))
  have hst : s.totalDegree ≤ b := (totalDegree_initialJetSeparant_le center Q).trans
    ((Nat.sub_le _ _).trans (hdeg.trans hjb))
  have gmid : g.degreeOf 1 ≤ r := (degreeOf_initialJetEquation_le_var center Q 1).trans hlocal
  have smid : s.degreeOf 1 ≤ c := by
    exact ((degreeOf_initialJetEquation_le_var center (separant Q (Fin.last 2)) 1).trans
      (jetDegree_separant_le Q (Fin.last 2) 1)).trans (hlocal.trans hrc)
  have hcuts (i : Fin n) : φ (cuts i) ∈ restrictCappedBidegree (Fin 2) F 1 a b c :=
    cappedRectangle _ ((degreeOf_agreement_secondOrder_weighted center Q v K τ hτ hv hcap _ _).trans hadeg)
      ((totalDegree_taylorAgreementEquation_le center Q hτ _ _).trans hbdeg)
      (by simpa using (degreeOf_agreement_middle_weighted center Q v K τ hτ hv hcap (domain i) (received i)).trans (by simpa using hcdeg))
  have comp (J : Ideal (MvPolynomial (Option (Fin 2)) F)) (hp : J.IsPrime) (hs0 : φ s ∉ J)
      (hd : 0 < (affineHilbertPolynomial J).natDegree) :
      (affineHilbertPolynomial J).natDegree + {i | φ (cuts i) ∈ J}.ncard ≤ K := by
    let I := J.comap φ
    have dim := natDegree_affineHilbertPolynomial_comap_of_surjective φ φsurj J
    let _ := hp
    have pr : I.IsPrime := Ideal.IsPrime.comap _
    have old := ReedSolomon.chart_dimensionSensitive_component_of_exponent center Q K K n τ
      hτ hK le_rfl I pr hs0 (fun l hl => by omega) domain received (dim.symm ▸ hd)
    change (affineHilbertPolynomial I).natDegree + {i | φ (cuts i) ∈ J}.ncard ≤ K at old
    exact dim ▸ old
  have bound := cappedBidegreeHypersurface_incidence_off_excluded_hybrid_two ha hb hc hkA hkA
    (φ g) (φ s) hg0 hproper (cappedRectangle _ hgder hgt gmid)
    (cappedRectangle _ (hgder.trans hha) (hgt.trans hjb) (gmid.trans hrc)) (cappedRectangle _ hsder hst smid)
    [] (by simp) (fun i => φ (cuts i)) hcuts ∅
    (by intro J hp hs _ _ hd; have := comp J hp hs hd; exact ⟨by omega,fun _ => by omega⟩)
    (by intro J hp hs _ _ hd hk; have := comp J hp hs hd; omega)
    (S.image lift) (by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact ⟨(evalEq x g).trans (hS x hx).1,fun h => (hS x hx).2 ((evalEq x s).symm.trans h),by simp,by simp⟩)
    (by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      simpa only [evalEq] using hA x hx)
  have hinj : Function.Injective lift := fun x y h => by
    funext i
    simpa [lift] using congrFun h (eC i)
  simpa only [Finset.card_image_of_injective _ hinj,pow_two,mul_assoc] using bound

#print axioms capped_jets
end
end KoalaBiJet
