import ProximityPrize.SubmissionLower.Z4WdLEc
set_option Elab.async false
namespace P4_6_5_1
noncomputable section
open aR (ao af embed)

open we (cH Of)
open aiJ
open bJ (bf)

open MvPolynomial Finset
open scoped BigOperators Polynomial




private theorem b07:aiJ.c1 :=
  aA3.of_children bRk.proof bRl.proof
private def aWB (Q:Bk) :aYJ:=lA Q
private theorem dOq (f :af 3) (S:cH[X]) (k :ℕ)
    (hk :k+3≤aR.bf) (hS:S.natDegree<k+3)
    (hf :Of f S=0) :Of (oR.AR f k) S=0:= by
  have h:=bRl.proof f S (hS.trans_le hk) hf k hk
  rw [Polynomial.hasseDeriv_eq_zero_of_lt_natDegree S (k+3) hS,mul_zero,mul_zero] at h
  have htwo: (2 :cH[X])≠0:= by
    let g:K1.K →+* cH[X] :=
      Polynomial.C.comp ((algebraMap ao cH).comp embed)
    have hne : (2 :K1.K)≠0:= by decide
    exact fun hz=>hne (g.injective (by simpa only [map_ofNat,map_zero] using hz))
  exact (mul_eq_zero.mp h).resolve_left htwo
private theorem c5B {f :af 3} {Q:Bk}
    (h:acU f Q) :
    (aWB Q).IsPrime∧(affineHilbertPolynomial (aWB Q)).natDegree=1 ∧
      affineDegree Q≤affineDegree (aWB Q) := by
  have hc:=(b07 f).1 Q h.solution
  obtain ⟨hdim,hdeg⟩:=YT.proof Q h.solution.prime h.solution.dimension
    hc.extended_prime hc.birational
  exact ⟨hc.extended_prime.comap tO,hdim,hdeg⟩
end
end P4_6_5_1
