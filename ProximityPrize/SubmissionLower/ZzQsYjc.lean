import ProximityPrize.SubmissionLower.ZaQt7ib
set_option Elab.async false
open _root_ renaming Finset.mul_sum→c9,Finset.sum_le_sum→lI,MvPolynomial.affineDegree→aU,mul_le_mul_of_nonneg_left→lz,rW.dimension→cy
set_option maxHeartbeats 1200000
namespace MJ
noncomputable section
open MvPolynomial dN rW
attribute [local instance] MvPolynomial.gradedAlgebra
def c3:Prop :=
  ∀ R:kT,R.IsPrime→(gN R).IsPrime →
    R.IsHomogeneous (homogeneousSubmodule (Fin aR.bf) aR.ao) →
    cy R=2 →
    cy (lA R)=2 ∧
    2*aU (gN R) ≤
      133671*(QZ mS (gN R) :ℚ) *
        aU (lA R)
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) :
    rW.c5:= by
  classical
  intro A hA hAe hdim hbir
  let B:=gN A
  let C:=lA A
  let S:=(lW B).minimalPrimesFinset
  let T:=(lW C).minimalPrimesFinset
  let image (P:Ideal mK) :n8:=P.comap mS
  let weight (P:Ideal mK) :ℕ:=ado (lW B) P
  let rank (P:Ideal mK) :ℕ:= QZ mS P
  obtain ⟨hpoly,hdescend⟩:=h2 A hA
  have hdimB:cy B=2 :=
    (congrArg Polynomial.natDegree hpoly).trans hdim
  have hdegree :aU A=aU B:= by
    change aU A=aU (gN A)
    simp only [aU,hpoly]
  have hbirB:aRK tO B:=hbir
  obtain ⟨hdimC,hproject⟩:=h4 _ _ _ tO cTa B hAe hdimB hbirB
  have hC:C.IsPrime := by
    let _:B.IsPrime :=hAe
    exact Ideal.IsPrime.comap mS
  have hdimC' : cy C=2 :=hdimC
  have hheight (P:Ideal mK) (hP:P∈S) :
      cy (image P)=2 ∧
      2*aU P≤133671*(rank P:ℚ)*aU (image P) := by
    have hp:=Ideal.mem_minimalPrimesFinset.mp hP
    obtain ⟨R,hR,rfl⟩:=hdescend P hp
    obtain ⟨hd,hhom⟩:=(h1 _ _ A hA hdim).1 R hR
    exact h3 R hR.isPrime hp.isPrime hhom hd
  have hmaps (P:Ideal mK) (hP:P∈S) :image P∈T:= by
    apply Ideal.mem_minimalPrimesFinset.mpr
    exact hproject P (Ideal.mem_minimalPrimesFinset.mp hP) (hheight P hP).1
  have hfibre (Q:n8) (hQ:Q∈T) :
      (∑ P∈S.filter (fun P=>image P= Q),weight P*rank P) ≤
        ado (lW C) Q:= by
    exact h5 _ _ _ tO cTa B hAe hbirB Q
      (Ideal.mem_minimalPrimesFinset.mp hQ)
  calc
    2*aU A=2 * ∑ P∈S,(weight P:ℚ)*aU P:= by
      rw [hdegree,(h1 _ _ B hAe hdimB).2]
    _ ≤ ∑ P∈S,133671*((weight P*rank P:ℕ) :ℚ)*aU (image P) := by
      rw [c9]
      apply lI
      intro P hP
      push_cast
      calc
        2*((weight P:ℚ)*aU P) =
            (weight P:ℚ)*(2*aU P) := by ring
        _≤(weight P:ℚ)*(133671*(rank P:ℚ)*aU (image P)) :=
          lz (hheight P hP).2 (by positivity)
        _ = _:= by ring
    _ = ∑ Q∈T,∑ P∈S.filter (fun P=>image P= Q),
        133671*((weight P*rank P:ℕ) :ℚ)*aU (image P) :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ Q∈T,133671*(ado (lW C) Q:ℚ)*aU Q:= by
      apply lI
      intro Q hQ
      calc
        _ = ∑ P∈S.filter (fun P=>image P= Q),
            133671*((weight P*rank P:ℕ) :ℚ)*aU Q:= by
          apply Finset.sum_congr rfl
          intro P hP
          rw [(Finset.mem_filter.mp hP).2]
        _=133671*((∑ P∈S.filter (fun P=>image P= Q),weight P*rank P:ℕ) :ℚ) *
            affineDegree Q:= by
          rw [Nat.cast_sum,c9,Finset.sum_mul]
        _≤_:=mul_le_mul_of_nonneg_right
          (lz (by exact_mod_cast hfibre Q hQ) (by positivity))
          (affineDegree_nonneg Q)
    _=133671*aU C:= by
      rw [(h1 _ _ C hC hdimC').2,c9]
      exact Finset.sum_congr rfl (fun _ _=>mul_assoc ..)
end
end MJ
