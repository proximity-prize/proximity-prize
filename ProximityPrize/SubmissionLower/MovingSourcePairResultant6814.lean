import ProximityPrize.SubmissionLower.MovingSourcePairPrimary6814

/-! A coprime source pair has a nonzero polynomial on every coefficient
fibre in at least one orientation. Swap the resultant when necessary;
no vertical fibre or zero outer-degree factor is discarded. -/
namespace ProximityPrize.SubmissionLower.MovingSourcePairResultant6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators Classical
open RCN143 RCN307 MovingSourcePairPrimary6814
variable {Base : Type} [Field Base]
local instance : DecidableEq Base := Classical.decEq Base

theorem coprime_resultant_ne_zero
    (P Q : Polynomial (Polynomial Base)) (hP : P≠0) (hcop : IsRelPrime P Q) :
    Polynomial.resultant P Q P.natDegree Q.natDegree≠0 := by
  let R := Polynomial Base
  let E := FractionRing R
  let f : R →+* E := algebraMap R E
  letI : Algebra (Polynomial R) (Polynomial E) := Polynomial.algebra R E
  letI : IsLocalization ((nonZeroDivisors R).map (Polynomial.C : R →+* Polynomial R).toMonoidHom)
      (Polynomial E) := Polynomial.isLocalization (nonZeroDivisors R) E
  letI : Module.Flat (Polynomial R) (Polynomial E) := IsLocalization.flat _
    ((nonZeroDivisors R).map (Polynomial.C : R →+* Polynomial R).toMonoidHom)
  have hinj : Function.Injective f := IsFractionRing.injective R E
  have hrel : IsRelPrime (P.map f) (Q.map f) :=
    MovingSourceFlatBaseChange6814.map_isRelPrime_of_flat (A:=Polynomial R) (B:=Polynomial E)
      (Polynomial.map_injective f hinj) P Q hP hcop
  have hr := Polynomial.resultant_ne_zero (P.map f) (Q.map f) hrel.isCoprime
  rw [Polynomial.natDegree_map_eq_of_injective hinj,Polynomial.natDegree_map_eq_of_injective hinj,
    Polynomial.resultant_map_map] at hr
  intro hz
  exact hr (by rw [hz,map_zero])

theorem C_dvd_of_local_residue_zero
    (I : Ideal (Polynomial Base)) [I.IsPrime] (f : Polynomial Base) (hI : I=Ideal.span {f})
    (P : Polynomial (Polynomial Base))
    (hz : (P.map (algebraMap (Polynomial Base) (LocalBase I))).map (IsLocalRing.residue (LocalBase I))=0) :
    Polynomial.C f∣P := by
  apply (Polynomial.C_dvd_iff_dvd_coeff f P).mpr
  intro n
  have he := congrArg (fun Q : Polynomial (IsLocalRing.ResidueField (LocalBase I)) => Q.coeff n) hz
  simp only [Polynomial.coeff_map,Polynomial.coeff_zero] at he
  have hm : algebraMap (Polynomial Base) (LocalBase I) (P.coeff n)∈IsLocalRing.maximalIdeal (LocalBase I) := by
    rw [←IsLocalRing.ker_residue]
    exact he
  have hmem := (IsLocalization.AtPrime.to_map_mem_maximal_iff (LocalBase I) I (P.coeff n)).mp hm
  rw [hI,Ideal.mem_span_singleton] at hmem
  exact hmem

theorem some_local_residue_ne_zero
    (I : Ideal (Polynomial Base)) [I.IsPrime] (f : Polynomial Base)
    (hI : I=Ideal.span {f}) (hf : Irreducible f)
    (P Q : Polynomial (Polynomial Base)) (hcop : IsRelPrime P Q) :
    (P.map (algebraMap (Polynomial Base) (LocalBase I))).map (IsLocalRing.residue (LocalBase I))≠0 ∨
    (Q.map (algebraMap (Polynomial Base) (LocalBase I))).map (IsLocalRing.residue (LocalBase I))≠0 := by
  by_cases hp : (P.map (algebraMap (Polynomial Base) (LocalBase I))).map (IsLocalRing.residue (LocalBase I))=0
  · right
    intro hq
    exact hf.not_isUnit (Polynomial.isUnit_C.mp (hcop
      (C_dvd_of_local_residue_zero I f hI P hp) (C_dvd_of_local_residue_zero I f hI Q hq)))
  · exact Or.inl hp

theorem grouped_pair_power_dvd
    (I : Ideal (Polynomial Base)) [I.IsPrime] (f : Polynomial Base)
    (hI : I=Ideal.span {f}) (hf : Irreducible f) (hfmonic : f.Monic)
    (P Q : Polynomial (Polynomial Base)) (m n : ℕ)
    (hP : P.natDegree≤m) (hQ : Q.natDegree≤n)
    (hcop : IsRelPrime P Q) (hres : Polynomial.resultant P Q m n≠0)
    {A : Type*} [Fintype A] (weight : A → ℕ)
    (C : PrimaryPiecesCertificate
      (P.map (algebraMap (Polynomial Base) (LocalBase I)))
      (Q.map (algebraMap (Polynomial Base) (LocalBase I))) weight)
    [Module.Finite (LocalBase I) (∀ a, Polynomial (LocalBase I) ⧸ C.pieces a)] :
    f^(∑ a, weight a)∣Polynomial.resultant P Q m n := by
  rcases some_local_residue_ne_zero I f hI hf P Q hcop with hp | hq
  · exact grouped_resultant_power_dvd_of_primary_pieces_of_surface_mod_ne_zero
      I f weight hI hf hfmonic P Q m n _ _ rfl rfl
      (Polynomial.natDegree_map_le.trans hP) (Polynomial.natDegree_map_le.trans hQ) hres hp C
  · have hr : Polynomial.resultant Q P n m≠0 := by
      rw [Polynomial.resultant_comm]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hres
    letI : Module.Finite (LocalBase I)
        (∀ a, Polynomial (LocalBase I) ⧸ (swapCertificate C).pieces a) :=
      (inferInstance : Module.Finite (LocalBase I) (∀ a, Polynomial (LocalBase I) ⧸ C.pieces a))
    have hb := grouped_resultant_power_dvd_of_primary_pieces_of_surface_mod_ne_zero
      I f weight hI hf hfmonic Q P n m _ _ rfl rfl
      (Polynomial.natDegree_map_le.trans hQ) (Polynomial.natDegree_map_le.trans hP)
      hr hq (swapCertificate C)
    rw [Polynomial.resultant_comm P Q m n]
    exact dvd_mul_of_dvd_right hb _

#print axioms some_local_residue_ne_zero
#print axioms grouped_pair_power_dvd
end
end ProximityPrize.SubmissionLower.MovingSourcePairResultant6814
