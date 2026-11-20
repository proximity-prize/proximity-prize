/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Regular-solution base change follows Quang Dao's ArkLib DirectJetList.
Modified to transfer the separated second Hasse coordinate bound. -/
import ProximityPrize.SubmissionLower.Mid6833CappedChart
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.DirectJetList
namespace KoalaBiJet
open PolynomialDifferential Polynomial MvPolynomial
noncomputable section
set_option maxHeartbeats 1200000
variable {F : Type*} [Field F]
local instance : DecidableEq F := Classical.decEq _
theorem capped_solutions
    (Q : DifferentialPolynomial F 2)
    {K τ n A h j v a b c r : ℕ} (hK : 2<K) (hkA : K≤A)
    (hτ : TaylorExponentSufficient 2 K τ) (hv : 2≤v) (ha : 0<a) (hb : 0<b)
    (hc : 0<c) (hrc : r≤c) (hlocal : jetDegree Q 1≤r)
    (hcap : Q.weightedTotalDegree (indexWeight 3) ≤ v)
    (hdeg : jetTotalDegree Q ≤ j) (hderiv : jetDegree Q 2 ≤ h)
    (hjb : j ≤ b) (hha : h ≤ a) (hbdeg : rationalTaylorCutDegreeBound Q τ ≤ b)
    (hadeg : (τ*(v-2)+(K-1))/2 ≤ a)
    (hcdeg : τ*(v-2)+(K-1) ≤ c)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (S : Finset F[X]) (hdegree : ∀P∈S, P.degree < K)
    (hsol : ∀P∈S, differentialSpecialization Q P=0)
    (hsep : ∀P∈S, differentialSpecialization (separant Q 2) P≠0)
    (hbin : ∀ i, 2 < i → i < K → (i.choose 2 : F) ≠ 0)
    (hagreement : ∀ P ∈ S, A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (S.card:ℚ) ≤ (cappedBidegreeMixedVolume h j r a b c : ℕ) * (((n-K+1:ℕ):ℚ)/((A-K+1:ℕ):ℚ))^2 := by
  classical
  let E := AlgebraicClosure F
  let f : F →+* E := algebraMap F E
  let QE := MvPolynomial.map f Q
  have hbinE : ∀ i, 2 < i → i < K → (i.choose 2 : E) ≠ 0 := by
    intro i hi hK h
    exact hbin i hi hK (f.injective (by simpa using h))
  let k := K
  have hkK : k≤K := le_rfl
  have hfilter (P : F[X]) :
      Finset.univ.filter (fun i : Fin n ↦ P.eval (domain i) = received i) =
        @Finset.filter (Fin n) (fun i ↦ P.eval (domain i) = received i)
          (fun i ↦ Classical.decEq F (P.eval (domain i)) (received i)) Finset.univ := by
    exact (Finset.filter_congr_decidable Finset.univ
      (fun i : Fin n ↦ P.eval (domain i) = received i)
      (fun i ↦ Classical.decEq F (P.eval (domain i)) (received i))).symm
  have hagree' : ∀ P ∈ S,
      A ≤ (@Finset.filter (Fin n) (fun i ↦ P.eval (domain i) = received i)
        (fun i ↦ Classical.decEq F (P.eval (domain i)) (received i)) Finset.univ).card := by
    intro P hP
    rw [← hfilter P]
    exact hagreement P hP
  obtain ⟨center, J, hcard, hJ⟩ :=
    exists_regular_solution_jet_family_of_exponent
      (f := f) (Q := Q) (K := K) (k := k) (τ := τ)
      (hτ := hτ) (hkK := hkK) (S := S)
      (A := A) (ι := Fin n) (domain := domain) (received := received)
      (hdegree := hdegree)
      (hsol := hsol) (hsep := hsep)
      (hbin := hbinE) (hagree := hagree')

  have capE : QE.weightedTotalDegree (indexWeight 3) ≤ v := by
    rw [weightedTotalDegree,Finset.sup_le_iff] at hcap ⊢
    intro m hm
    exact hcap m (support_map_subset f Q hm)
  let domainE : Fin n ↪ E := domain.trans ⟨f, f.injective⟩
  have bound := capped_jets center QE hK hkA hτ hv ha hb hc hrc (by simpa [QE,jetDegree_map_eq f.injective] using hlocal) capE
    (by simpa [QE,jetTotalDegree_map_eq f.injective] using hdeg)
    (by simpa [QE,jetDegree_map_eq f.injective] using hderiv) hjb hha
    (by simpa [QE,rationalTaylorCutDegreeBound,jetTotalDegree_map_eq f.injective] using hbdeg) hadeg hcdeg
    domainE (fun i => f (received i)) J
    (fun jet hjet => ⟨(hJ jet hjet).1,(hJ jet hjet).2.1⟩) (by
      intro jet hjet
      let agreementSet := Finset.univ.filter (fun i ↦
        aeval jet (taylorAgreementEquation center ((MvPolynomial.map f) Q) K τ
          (f (domain i)) (f (received i))) = 0)
      have hset : ({i | aeval jet (taylorAgreementEquation center QE K τ
          (domainE i) (f (received i))) = 0} : Set (Fin n)) =
          (agreementSet : Set (Fin n)) := by
        ext i
        simp only [Set.mem_ofPred_eq, agreementSet, Finset.mem_coe,
          Finset.mem_filter, Finset.mem_univ, true_and]
        change (aeval jet (taylorAgreementEquation center QE K τ
          (f (domain i)) (f (received i))) = 0) ↔ _
        rfl
      rw [hset, Set.ncard_coe_finset]
      exact (hJ jet hjet).2.2.2)
  simpa only [hcard] using bound
#print axioms capped_solutions
end
end KoalaBiJet
