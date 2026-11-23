import ProximityPrize.SubmissionLower.R6960SheetDeterminant
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.RingTheory.Norm.Transitivity

noncomputable section
set_option Elab.async false
namespace Lower6960.SheetNorm
open Polynomial Finset
open scoped Polynomial BigOperators

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
abbrev Infinity (K : Type*) [Field K] [DecidableEq (RatFunc K)] :=
  (RatFunc.inftyValuation K).valuationSubring

variable {E : Type*} [Field E] [Algebra (RatFunc K) E] [FiniteDimensional (RatFunc K) E]
  [Algebra K[X] E] [IsScalarTower K[X] (RatFunc K) E]
  [Algebra (Infinity K) E] [IsScalarTower (Infinity K) (RatFunc K) E]

/-- A nonzero minor integral at finite places, with the specified twist
integral at infinity, has a polynomial norm of the required degree. -/
theorem polynomial_norm (m : E) (nz : m≠0) (finite : IsIntegral K[X] m) (b : ℕ)
    (infty : IsIntegral (Infinity K) (m/algebraMap (RatFunc K) E (RatFunc.X^b))) :
    ∃ P : K[X], P≠0 ∧ algebraMap K[X] (RatFunc K) P=Algebra.norm (RatFunc K) m ∧
      P.natDegree≤Module.finrank (RatFunc K) E*b := by
  let d:=Module.finrank (RatFunc K) E
  obtain ⟨P,hP⟩ := IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_norm (RatFunc K) finite)
  have hn : P≠0 := by
    intro zero
    have ne := (Algebra.norm_ne_zero_iff (R:=RatFunc K)).mpr nz
    exact ne (by rw [←hP,zero,map_zero])
  obtain ⟨v,hv⟩ := IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_norm (RatFunc K) infty)
  have atInfinity : RatFunc.inftyValuation K (algebraMap (Infinity K) (RatFunc K) v)≤1 := v.property
  rw [hv,div_eq_mul_inv,map_mul,Algebra.norm_inv,Algebra.norm_algebraMap,←hP,←pow_mul,
    ←div_eq_mul_inv] at atInfinity
  let W : K[X] := Polynomial.X ^ (b*d)
  have wn : W≠0 := pow_ne_zero _ X_ne_zero
  have we : algebraMap K[X] (RatFunc K) W = RatFunc.X^(b*d) := by simp [W,RatFunc.algebraMap_X]
  change RatFunc.inftyValuation K ((algebraMap K[X] (RatFunc K) P)/(RatFunc.X^(b*d)))≤1 at atInfinity
  rw [←we,map_div₀,div_le_one₀] at atInfinity
  · change RatFunc.inftyValuationDef K (algebraMap K[X] (RatFunc K) P) ≤
        RatFunc.inftyValuationDef K (algebraMap K[X] (RatFunc K) W) at atInfinity
    rw [RatFunc.inftyValuation.polynomial _ hn,RatFunc.inftyValuation.polynomial _ wn,
      WithZero.exp_le_exp,Int.ofNat_le] at atInfinity
    exact ⟨P,hn,hP,by simpa [W,d,Nat.mul_comm b] using atInfinity⟩
  · exact (RatFunc.inftyValuation K).pos_iff.mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr wn)

#print axioms polynomial_norm

abbrev Aut (K E : Type*) [Field K] [Field E] [Algebra (RatFunc K) E] := E ≃ₐ[RatFunc K] E

/-- The determinant of a single nonzero minor supplies the counting polynomial
by descent. Its conjugates can have different reductions above a marked seed. -/
theorem count_quotient_directions [IsGalois (RatFunc K) E] {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [MulAction (Aut K E) I] [MulAction.IsPretransitive (Aut K E) I]
    (B : Matrix I (Option J) E) (row : Option J ↪ I)
    (room : Fintype.card (Option J)<Fintype.card I)
    (equivariant : ∀ (σ : Aut K E) i j, B (σ • i) j=σ (B i j))
    (nz : (B.submatrix row id).det≠0) (finite : IsIntegral K[X] (B.submatrix row id).det)
    (b : ℕ) (infty : IsIntegral (Infinity K)
      ((B.submatrix row id).det/algebraMap (RatFunc K) E (RatFunc.X^b)))
    (T : Finset K) (O : K→Type*) [∀ z,CommRing (O z)] [∀ z,IsDomain (O z)] [∀ z,IsLocalRing (O z)]
    (pull : ∀ z,K[X] →+* O z) (into : ∀ z,O z →+* E)
    (emb : ∀ z,Function.Injective (into z))
    (base : ∀ z,(into z).comp (pull z)=(algebraMap (RatFunc K) E).comp (algebraMap K[X] (RatFunc K)))
    (π : ∀ z,O z) (point : K→I) (A : ∀ z,Matrix I (Option J) (O z))
    (lift : ∀ z∈T, ∀ i j,into z (A z i j)=B i j)
    (V : ∀ z,Submodule (IsLocalRing.ResidueField (O z)) (J→IsLocalRing.ResidueField (O z)))
    (place : ∀ z∈T,π z≠0 ∧ IsLocalRing.maximalIdeal (O z)=Ideal.span {π z} ∧
      pull z (Polynomial.X-C z)=π z)
    (constant : ∀ z∈T,∀ i,IsLocalRing.residue (O z) (A z i none)=1)
    (agree : ∀ z∈T,∀ v∈V z,∀ i j : I, i≠point z → j≠point z →
      (∑ t,IsLocalRing.residue (O z) (A z i (some t))*v t)=
        (∑ t,IsLocalRing.residue (O z) (A z j (some t))*v t)) :
    (∑ z∈T,Module.finrank (IsLocalRing.ResidueField (O z)) (V z)) ≤ Fintype.card I*b := by
  classical
  obtain ⟨P,pnz,pnorm,cap⟩ := polynomial_norm _ nz finite b infty
  have degree : P.natDegree≤Fintype.card (Aut K E)*b := by
    rw [Fintype.card_eq_nat_card,IsGalois.card_aut_eq_finrank]
    exact cap
  apply SheetDeterminant.marked_dimensions (G:=Aut K E) row room T P pnz b degree
    O pull π point A V place _ constant agree
  intro z hz
  suffices eq : SheetDeterminant.orbitProduct (G:=Aut K E) (A z) row = pull z P by
    rw [eq]
  apply emb z
  have hp := DFunLike.congr_fun (base z) P
  change into z (pull z P)=algebraMap (RatFunc K) E _ at hp
  rw [hp,pnorm,Algebra.norm_eq_prod_automorphisms]
  unfold SheetDeterminant.orbitProduct
  rw [map_prod]
  calc _ = ∏ g : Aut K E,g⁻¹ ((B.submatrix row id).det) := by
             apply prod_congr rfl
             intro g _
             rw [RingHom.map_det,AlgEquiv.map_det]
             congr 1
             ext i j
             exact (lift z hz _ _).trans (equivariant g⁻¹ _ _)
       _ = _ := Equiv.prod_comp (Equiv.inv (Aut K E)) (fun g=>g ((B.submatrix row id).det))

#print axioms count_quotient_directions
end Lower6960.SheetNorm
