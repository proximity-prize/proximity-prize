import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DdB6
import ProximityPrize.SubmissionLower.KoalaCompression
import ProximityPrize.SubmissionLower.LibraryArkLib_Data_MvPolynomial_WeightedDegree_Products
import ProximityPrize.SubmissionLower.LibraryArkLib_Data_Polynomial_ResultantSpecialization
import ProximityPrize.SubmissionLower.LibraryArkLib_ToMathlib_MvPolynomial_OptionWeightedDegree
import ProximityPrize.SubmissionLower.LibraryArkLib_ToMathlib_MvPolynomial_SupportWeight
import ProximityPrize.SubmissionLower.LibraryMathlib_FieldTheory_RatFunc_Valuation
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Norm_Transitivity
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Valuation_LocalSubring
import ProximityPrize.SubmissionLower.R6960CollisionMarkedDiscTransport
import ProximityPrize.SubmissionLower.R6960CollisionTameBranchFrame
import ProximityPrize.SubmissionLower.R6960CollisionTameLineDegree
import ProximityPrize.SubmissionLower.R6960Low6960CountCore

section Merged6967_R6960MarkedScalarPlace
set_option Elab.async false









set_option Elab.async false

-- merged module R6960SheetDeterminant
section Merged_R6960SheetDeterminant
noncomputable section
set_option Elab.async false
namespace Lower6960.SheetDeterminant
open Polynomial Finset Matrix
open scoped BigOperators Matrix Polynomial
variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem local_minor (π : R) (gen : IsLocalRing.maximalIdeal R = Ideal.span {π})
    (M : Matrix ι ι R) :
    π^(Fintype.card ι-((IsLocalRing.residue R).mapMatrix M).rank) ∣ M.det := by
  classical
  let k := IsLocalRing.ResidueField R
  let red := IsLocalRing.residue R
  let m := red.mapMatrix M
  let lift (A : Matrix ι ι k) : Matrix ι ι R :=
    fun i j=>(IsLocalRing.residue_surjective (A i j)).choose
  have lifts (A : Matrix ι ι k) : red.mapMatrix (lift A)=A := by
    ext i j
    exact (IsLocalRing.residue_surjective (A i j)).choose_spec
  have unit (A : Matrix ι ι k) (u : IsUnit A) : IsUnit (lift A).det := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    change red (lift A).det≠0
    rw [RingHom.map_det,lifts]
    exact (isUnit_iff_isUnit_det _).mp u |>.ne_zero
  obtain ⟨V,U,e,v,u,normal⟩ := exists_rank_normal_form m
  let D := lift V * M * lift U
  have normal' : red.mapMatrix D=(Matrix.fromBlocks 1 0 0 0).submatrix e e := by
    dsimp only [D]
    rw [map_mul,map_mul,lifts,lifts]
    exact normal
  let idx : Fin (Fintype.card ι-m.rank) ↪ ι :=
    ⟨fun i=>e.symm (Sum.inr i),fun _ _ eq=>Sum.inr.inj (e.symm.injective eq)⟩
  let S := univ.map idx
  have col (j) (hj : j∈S) (i : ι) : π ∣ D i j := by
    obtain ⟨a,_,rfl⟩ := mem_map.mp hj
    apply Ideal.mem_span_singleton.mp
    rw [←gen,←IsLocalRing.residue_eq_zero_iff]
    change red.mapMatrix D i (e.symm (Sum.inr a))=0
    rw [normal']
    simp only [submatrix_apply, Equiv.apply_symm_apply]
    cases e i <;> rfl
  have dv : π^S.card ∣ D.det := by
    rw [det_apply']
    apply Finset.dvd_sum
    intro perm _
    have small : (∏ _j ∈ S,π) ∣ ∏ j∈S,D (perm j) j :=
      prod_dvd_prod_of_dvd _ _ (fun j hj=>col j hj (perm j))
    have large := Finset.prod_dvd_prod_of_subset S univ (fun j=>D (perm j) j) (subset_univ _)
    exact dvd_mul_of_dvd_right (by simpa using small.trans large) _
  have size : S.card=Fintype.card ι-m.rank := by simp [S]
  rw [size] at dv
  change π^_∣(lift V*M*lift U).det at dv
  rw [det_mul,det_mul] at dv
  exact (unit V v).dvd_mul_left.mp ((unit U u).dvd_mul_right.mp dv)
#print axioms local_minor
section
variable {K I J : Type*} [Field K] [Fintype J] [DecidableEq J]
omit [DecidableEq J] in
theorem omitted_corank (A : Matrix I (Option J) K) (constant : ∀ i,A i none=1)
    (p : I) (rows : Option J → I) (outside : ∀ j,rows j≠p)
    (V : Submodule K (J→K))
    (agree : ∀ v∈V, ∀ a b : I, a≠p → b≠p →
      (∑ j,A a (some j)*v j)=(∑ j,A b (some j)*v j)) :
    Module.finrank K V ≤ Fintype.card (Option J)-(A.submatrix rows id).rank := by
  classical
  let S := (A.submatrix rows id).mulVecLin
  let value : (J→K) →ₗ[K] K := (LinearMap.proj (rows none)).comp (A.submatrix id some).mulVecLin
  let put : (J→K) →ₗ[K] (Option J→K) := LinearMap.pi (fun j=>match j with
    | none => -value
    | some i => LinearMap.proj i)
  have subset (v : V) : put v.val ∈ LinearMap.ker S := by
    apply LinearMap.mem_ker.mpr
    funext j
    change (∑ x : Option J, A (rows j) x*(put v.val x)) = 0
    rw [Fintype.sum_option,constant,one_mul]
    change -(∑ i,A (rows none) (some i)*v.val i)+(∑ i,A (rows j) (some i)*v.val i)=0
    rw [agree _ v.property _ _ (outside j) (outside none),neg_add_cancel]
  let embedding := (put.comp V.subtype).codRestrict (LinearMap.ker S) subset
  have inj : Function.Injective embedding := by
    intro v w eq
    apply Subtype.ext
    funext j
    exact congrArg (fun a : LinearMap.ker S=>a.val (some j)) eq
  have dim := LinearMap.finrank_le_finrank_of_injective (f:=embedding) inj
  have rank := S.finrank_range_add_finrank_ker
  change (A.submatrix rows id).rank + _ = _ at rank
  have equality : (A.submatrix rows id).rank + Module.finrank K (LinearMap.ker S) =
      Fintype.card (Option J) := by simpa [Module.finrank_pi_fintype] using rank
  omega
#print axioms omitted_corank
end
section
variable {G I J : Type*} [Group G] [Fintype G] [Fintype I] [DecidableEq I]
    [MulAction G I] [MulAction.IsPretransitive G I] [Fintype J] [DecidableEq J]
def orbitProduct (A : Matrix I (Option J) R) (rows : Option J ↪ I) : R :=
  ∏ g : G,(A.submatrix (fun j=>g⁻¹ • rows j) id).det
theorem orbit_order (π : R) (gen : IsLocalRing.maximalIdeal R=Ideal.span {π})
    (A : Matrix I (Option J) R) (rows : Option J ↪ I)
    (constant : ∀ i,IsLocalRing.residue R (A i none)=1) (p : I)
    (V : Submodule (IsLocalRing.ResidueField R) (J→IsLocalRing.ResidueField R))
    (agree : ∀ v∈V, ∀ a b : I, a≠p → b≠p →
      (∑ j,IsLocalRing.residue R (A a (some j))*v j)=
        (∑ j,IsLocalRing.residue R (A b (some j))*v j)) :
    ∃ n : ℕ, π^n∣orbitProduct (G:=G) A rows ∧
      Fintype.card I*n = Fintype.card G*(Fintype.card I-Fintype.card (Option J))*
        Module.finrank (IsLocalRing.ResidueField R) V := by
  classical
  let S := univ.map rows
  let d := Module.finrank (IsLocalRing.ResidueField R) V
  let e (g : G) := if g • p∉S then 1 else 0
  refine ⟨∑ g : G,e g*d,?_,?_⟩
  · unfold orbitProduct
    rw [←Finset.prod_pow_eq_pow_sum]
    apply prod_dvd_prod_of_dvd
    intro g _
    by_cases misses : g • p∉S
    · have out (j) : g⁻¹ • rows j ≠ p := by
        intro eq
        apply misses
        rw [←eq,smul_inv_smul]
        exact mem_map.mpr ⟨j,mem_univ _,rfl⟩
      have cor := omitted_corank (A.map (IsLocalRing.residue R)) constant p _ out V agree
      have dv := local_minor π gen (A.submatrix (fun j=>g⁻¹ • rows j) id)
      have exponent : e g=1 := by dsimp only [e]; split_ifs; tauto
      rw [exponent,one_mul]
      exact (pow_dvd_pow π cor).trans dv
    · have exponent : e g=0 := by dsimp only [e]; split_ifs <;> tauto
      simp only [exponent,zero_mul,pow_zero,one_dvd]
  · have cnt := MarkedSheet.omission (G:=G) S p
    have card : S.card=Fintype.card (Option J) := by simp [S]
    rw [card] at cnt
    change Fintype.card I*(∑ g : G,e g*d)=_
    rw [←sum_mul,←Nat.mul_assoc]
    exact congrArg (·*d) cnt
#print axioms orbit_order
end
section
variable {K : Type*} [Field K] {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]
theorem base_parameter_order (φ : (Polynomial K) →+* O) (z : K) (π : O) (nonzero : π≠0)
    (rz : IsLocalRing.residue O π=0)
    (uniform : φ (Polynomial.X-C z)=π) {P : (Polynomial K)} (hn : P≠0) (n : ℕ) :
    π^n∣φ P ↔ n≤P.rootMultiplicity z := by
  let ρ := (IsLocalRing.residue O).comp φ
  have ev : ρ=(ρ.comp C).comp (evalRingHom z) := by
    apply Polynomial.ringHom_ext
    · intro c; simp [RingHom.comp_apply]
    · have x : ρ (Polynomial.X-C z)=0 := by change (IsLocalRing.residue O) (φ _)=0; rw [uniform,rz]
      simpa only [RingHom.comp_apply,coe_evalRingHom,eval_X] using sub_eq_zero.mp (map_sub ρ _ _ ▸ x)
  obtain ⟨Q,fac,rest⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hn z
  have value : Q.eval z≠0 := fun root=>rest (dvd_iff_isRoot.mpr root)
  have uq : IsUnit (φ Q) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    change ρ Q≠0
    calc ρ Q = (ρ.comp C) (Q.eval z) := DFunLike.congr_fun ev Q
         _ ≠ 0 := (map_ne_zero_iff _ (ρ.comp C).injective).mpr value
  have φP := congrArg φ fac
  simp only [map_mul,map_pow,uniform] at φP
  have nu : ¬IsUnit π := fun u=>(u.map (IsLocalRing.residue O)).ne_zero rz
  rw [φP,uq.dvd_mul_right,pow_dvd_pow_iff nonzero nu]
theorem base_order (φ : (Polynomial K) →+* O) (z : K) (π : O) (nonzero : π≠0)
    (gen : IsLocalRing.maximalIdeal O=Ideal.span {π})
    (uniform : φ (Polynomial.X-C z)=π) {P : (Polynomial K)} (hn : P≠0) (n : ℕ) :
    π^n∣φ P ↔ n≤P.rootMultiplicity z :=
  base_parameter_order φ z π nonzero ((IsLocalRing.residue_eq_zero_iff _).mpr
    (gen.symm ▸ Ideal.subset_span (by simp))) uniform hn n
#print axioms base_parameter_order
#print axioms base_order
end
section
variable {G I J K : Type*} [Group G] [Fintype G] [Fintype I] [DecidableEq I]
    [MulAction G I] [MulAction.IsPretransitive G I] [Fintype J] [DecidableEq J] [Field K]
theorem marked_dimensions (row : Option J ↪ I) (room : Fintype.card (Option J)<Fintype.card I)
    (T : Finset K) (P : (Polynomial K)) (nonzero : P≠0) (budget : ℕ)
    (deg : P.natDegree≤Fintype.card G*budget)
    (O : K→Type*) [∀ z,CommRing (O z)] [∀ z,IsDomain (O z)] [∀ z,IsLocalRing (O z)]
    (φ : ∀ z,(Polynomial K) →+* O z) (π : ∀ z,O z) (p : K→I)
    (A : ∀ z,Matrix I (Option J) (O z))
    (V : ∀ z,Submodule (IsLocalRing.ResidueField (O z)) (J→IsLocalRing.ResidueField (O z)))
    (place : ∀ z∈T,π z≠0 ∧ IsLocalRing.maximalIdeal (O z)=Ideal.span {π z} ∧
      φ z (Polynomial.X-C z)=π z)
    (norm : ∀ z∈T,Associated (orbitProduct (G:=G) (A z) row) (φ z P))
    (constant : ∀ z∈T,∀ i,IsLocalRing.residue (O z) (A z i none)=1)
    (agree : ∀ z∈T,∀ v∈V z,∀ a b : I, a≠p z → b≠p z →
      (∑ j,IsLocalRing.residue (O z) (A z a (some j))*v j)=
        (∑ j,IsLocalRing.residue (O z) (A z b (some j))*v j)) :
    (∑ z∈T,Module.finrank (IsLocalRing.ResidueField (O z)) (V z)) ≤ Fintype.card I*budget := by
  classical
  let d (z : K) := Module.finrank (IsLocalRing.ResidueField (O z)) (V z)
  have each (z : K) (inT : z∈T) : Fintype.card G*d z≤Fintype.card I*P.rootMultiplicity z := by
    obtain ⟨nz,gen,unram⟩ := place z inT
    obtain ⟨n,div,size⟩ := orbit_order (G:=G) (π z) gen (A z) row (constant z inT)
      (p z) (V z) (agree z inT)
    have ord := (base_order (φ z) z (π z) nz gen unram nonzero n).mp
      (div.trans (norm z inT).dvd)
    calc Fintype.card G*d z ≤ (Fintype.card G*(Fintype.card I-Fintype.card (Option J)))*d z :=
               Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))
         _ = Fintype.card I*n := size.symm
         _ ≤ _ := Nat.mul_le_mul_left _ ord
  have total := sum_le_sum each
  rw [←mul_sum,←mul_sum] at total
  refine Nat.le_of_mul_le_mul_left ?_ (Fintype.card_pos (α:=G))
  calc Fintype.card G*(∑ z∈T,d z) ≤ _ := total
       _ ≤ Fintype.card I*(Fintype.card G*budget) := Nat.mul_le_mul_left _
         ((ProximityPrize.SubmissionLower.MatrixRootMultiplicity.sum_rootMultiplicity_le_natDegree P T).trans deg)
       _ = _ := by ring
#print axioms marked_dimensions
end
end Lower6960.SheetDeterminant

end
end Merged_R6960SheetDeterminant

-- merged module R6960SheetNorm
section Merged_R6960SheetNorm
noncomputable section
set_option Elab.async false
namespace Lower6960.SheetNorm
open Polynomial Finset
open scoped Polynomial BigOperators
variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
abbrev Infinity (K : Type*) [Field K] [DecidableEq (RatFunc K)] :=
  (RatFunc.inftyValuation K).valuationSubring
variable {E : Type*} [Field E] [Algebra (RatFunc K) E] [FiniteDimensional (RatFunc K) E]
  [Algebra (Polynomial K) E] [IsScalarTower (Polynomial K) (RatFunc K) E]
  [Algebra (Infinity K) E] [IsScalarTower (Infinity K) (RatFunc K) E]
theorem polynomial_norm (m : E) (nz : m≠0) (finite : IsIntegral (Polynomial K) m) (b : ℕ)
    (infty : IsIntegral (Infinity K) (m/algebraMap (RatFunc K) E (RatFunc.X^b))) :
    ∃ P : (Polynomial K), P≠0 ∧ algebraMap (Polynomial K) (RatFunc K) P=Algebra.norm (RatFunc K) m ∧
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
  let W : (Polynomial K) := Polynomial.X ^ (b*d)
  have wn : W≠0 := pow_ne_zero _ X_ne_zero
  have we : algebraMap (Polynomial K) (RatFunc K) W = RatFunc.X^(b*d) := by simp [W,RatFunc.algebraMap_X]
  change RatFunc.inftyValuation K ((algebraMap (Polynomial K) (RatFunc K) P)/(RatFunc.X^(b*d)))≤1 at atInfinity
  rw [←we,map_div₀,div_le_one₀] at atInfinity
  · change RatFunc.inftyValuationDef K (algebraMap (Polynomial K) (RatFunc K) P) ≤
        RatFunc.inftyValuationDef K (algebraMap (Polynomial K) (RatFunc K) W) at atInfinity
    rw [RatFunc.inftyValuation.polynomial _ hn,RatFunc.inftyValuation.polynomial _ wn,
      WithZero.exp_le_exp,Int.ofNat_le] at atInfinity
    exact ⟨P,hn,hP,by simpa [W,d,Nat.mul_comm b] using atInfinity⟩
  · exact (RatFunc.inftyValuation K).pos_iff.mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial K) (RatFunc K))).mpr wn)
#print axioms polynomial_norm
abbrev Aut (K E : Type*) [Field K] [Field E] [Algebra (RatFunc K) E] := E ≃ₐ[RatFunc K] E
theorem count_quotient_directions [IsGalois (RatFunc K) E] {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [MulAction (Aut K E) I] [MulAction.IsPretransitive (Aut K E) I]
    (B : Matrix I (Option J) E) (row : Option J ↪ I)
    (room : Fintype.card (Option J)<Fintype.card I)
    (equivariant : ∀ (σ : Aut K E) i j, B (σ • i) j=σ (B i j))
    (nz : (B.submatrix row id).det≠0) (finite : IsIntegral (Polynomial K) (B.submatrix row id).det)
    (b : ℕ) (infty : IsIntegral (Infinity K)
      ((B.submatrix row id).det/algebraMap (RatFunc K) E (RatFunc.X^b)))
    (T : Finset K) (O : K→Type*) [∀ z,CommRing (O z)] [∀ z,IsDomain (O z)] [∀ z,IsLocalRing (O z)]
    (pull : ∀ z,(Polynomial K) →+* O z) (into : ∀ z,O z →+* E)
    (emb : ∀ z,Function.Injective (into z))
    (base : ∀ z,(into z).comp (pull z)=(algebraMap (RatFunc K) E).comp (algebraMap (Polynomial K) (RatFunc K)))
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

end
end Merged_R6960SheetNorm

-- merged module R6960MarkedEvaluationDeterminant
section Merged_R6960MarkedEvaluationDeterminant
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MarkedEvaluation
open Finset Matrix Polynomial
open scoped Matrix BigOperators Polynomial
theorem cleared_rows {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
    (π:R) (A:Matrix J J R) (rows:Finset J) (row : ∀ i∈rows,∀ j,π∣A i j) : π^rows.card∣A.det := by
  classical
  let c (i:J):=if i∈rows then π else 1
  have factors (i j:J) : c i∣A i j := by
    by_cases h:i∈rows
    · simpa [c,h] using row i h j
    · simp [c,h]
  choose B eq using factors
  have mat : A=Matrix.of (fun i j=>c i*B i j) := Matrix.ext (fun i j=>eq i j)
  have product : (∏ i,c i)=π^rows.card := by
    simp [c]
  rw [mat,Matrix.det_mul_column,product]
  exact dvd_mul_right ..
theorem row_average {G J : Type*} [Group G] [Fintype G] [Fintype J] (I:J→Type*)
    [∀ j,Fintype (I j)] [∀ j,DecidableEq (I j)] [∀ j,MulAction G (I j)]
    [∀ j,MulAction.IsPretransitive G (I j)] (e:ℕ) (degree:∀ j,Fintype.card (I j)=e)
    (pick mark:∀ j,I j) :
    e*(∑ g:G,(Finset.univ.filter (fun j=>g • pick j≠mark j)).card)=
      Fintype.card G*((e-1)*Fintype.card J) := by
  classical
  let b (g:G) (j:J):ℕ:=if g • pick j≠mark j then 1 else 0
  have each (j:J) : e*(∑g:G,b g j)=Fintype.card G*(e-1) := by
    have eq:=MarkedSheet.omission (G:=G) ({mark j}:Finset (I j)) (pick j)
    simpa only [degree,Finset.card_singleton,Finset.mem_singleton,b] using eq
  calc _ = e*(∑g:G,∑j:J,b g j) := by simp only [b,Finset.sum_boole, Nat.cast_id]
       _ = ∑j:J,e*(∑g:G,b g j) := by rw [Finset.sum_comm,Finset.mul_sum]
       _ = _ := by simp only [each,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]; ring
theorem pole_degree {K G J : Type*} [Field K] [Group G] [Fintype G] [Fintype J] [DecidableEq J]
    (e d : ℕ) (ep : 0<e) (T:Finset K) (P:(Polynomial K)) (nz:P≠0)
    (cap : P.natDegree+Fintype.card G*d≤Fintype.card G*(T.card*Fintype.card J))
    (O:K→Type*) [∀ z,CommRing (O z)] [∀ z,IsDomain (O z)] [∀ z,IsLocalRing (O z)]
    (φ:∀ z,(Polynomial K)→+*O z) (π:∀z,O z) (place:∀ z∈T,π z≠0 ∧ IsLocalRing.residue _ (π z)=0 ∧ φ z (Polynomial.X-C z)=π z)
    (A:∀ z,G→Matrix J J (O z)) (rows:K→G→Finset J)
    (norm:∀ z∈T,φ z P=∏g:G,(A z g).det)
    (hits:∀ z∈T,∀g,∀i∈rows z g,∀j,π z∣A z g i j)
    (avg:∀ z∈T,e*(∑g:G,(rows z g).card)=Fintype.card G*((e-1)*Fintype.card J)) :
    e*d≤T.card*Fintype.card J := by
  classical
  have atZ (z) (hz:z∈T) : Fintype.card G*((e-1)*Fintype.card J)≤e*P.rootMultiplicity z := by
    have dv : π z^(∑g:G,(rows z g).card)∣φ z P := by
      rw [norm z hz,←Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_dvd_prod_of_dvd _ _ (fun g _=>cleared_rows (π z) _ _ (hits z hz g))
    have pz:=place z hz
    exact (avg z hz) ▸ Nat.mul_le_mul_left e
      ((SheetDeterminant.base_parameter_order (φ z) z (π z) pz.1 pz.2.1 pz.2.2 nz _).mp dv)
  have total := Finset.sum_le_sum atZ
  simp only [Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum] at total
  simp only [Nat.cast_id] at total
  have low:=total.trans (Nat.mul_le_mul_left e
    (ProximityPrize.SubmissionLower.MatrixRootMultiplicity.sum_rootMultiplicity_le_natDegree P T))
  have high:=Nat.mul_le_mul_left e cap
  have es : e-1+1=e := Nat.sub_add_cancel ep
  have sh : Fintype.card G * (e*d) ≤ Fintype.card G*(T.card*Fintype.card J) := by
    have expand : Fintype.card G*(T.card*Fintype.card J)*e =
        T.card*(Fintype.card G*((e-1)*Fintype.card J))+Fintype.card G*(T.card*Fintype.card J) := by
      conv_lhs => rhs; rw [←es]
      ring
    nlinarith only [low,high,expand]
  exact Nat.le_of_mul_le_mul_left sh Fintype.card_pos
#print axioms cleared_rows
#print axioms row_average
#print axioms pole_degree
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedEvaluationDeterminant

-- merged module R6960MarkedEvaluationNorm
section Merged_R6960MarkedEvaluationNorm

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MarkedEvaluation
open Polynomial Algebra Module Finset Matrix
open scoped Polynomial BigOperators
variable {K E : Type*} [Field K] [DecidableEq (RatFunc K)] [Field E]
  [Algebra (RatFunc K) E] [FiniteDimensional (RatFunc K) E]
  [Algebra (Polynomial K) E] [IsScalarTower (Polynomial K) (RatFunc K) E]
  [Algebra (SheetNorm.Infinity K) E] [IsScalarTower (SheetNorm.Infinity K) (RatFunc K) E]

/-- A determinant with a zero of order d at scalar infinity, after its common
degree-b clearing, pays b-d degrees in the base norm. -/
theorem norm_degree (v:E) (nz:v≠0) (finite:IsIntegral (Polynomial K) v) (b d:ℕ)
    (inf:IsIntegral (SheetNorm.Infinity K) ((algebraMap (RatFunc K) E RatFunc.X)^d*v/
      algebraMap (RatFunc K) E (RatFunc.X^b))) :
    ∃ P:(Polynomial K),P≠0 ∧ algebraMap (Polynomial K) (RatFunc K) P=norm (RatFunc K) v ∧
      P.natDegree+finrank (RatFunc K) E*d≤finrank (RatFunc K) E*b := by
  let ι:=algebraMap (RatFunc K) E
  let j:=algebraMap (Polynomial K) (RatFunc K)
  have xi:IsIntegral (Polynomial K) (ι RatFunc.X) := by
    rw [←RatFunc.algebraMap_X,←IsScalarTower.algebraMap_apply]; exact isIntegral_algebraMap
  have xn:ι RatFunc.X≠0 := (map_ne_zero_iff _ ι.injective).mpr RatFunc.X_ne_zero
  obtain ⟨Q,qn,hq,degree⟩:=SheetNorm.polynomial_norm ((ι RatFunc.X)^d*v)
    (mul_ne_zero (pow_ne_zero _ xn) nz) ((xi.pow _).mul finite) b inf
  obtain ⟨P,hP⟩:=IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_norm (RatFunc K) finite)
  have pn:P≠0 := by
    intro zero; apply (Algebra.norm_ne_zero_iff (R:=RatFunc K)).mpr nz; rw [←hP,zero,map_zero]
  have eq : Q=(Polynomial.X:(Polynomial K))^(d*finrank (RatFunc K) E)*P := by
    apply IsFractionRing.injective (Polynomial K) (RatFunc K)
    simp only [hq,ι,map_mul,map_pow,RatFunc.algebraMap_X,hP,Algebra.norm_algebraMap,←pow_mul,Nat.mul_comm d]
  rw [eq,natDegree_mul (pow_ne_zero _ X_ne_zero) pn,natDegree_pow,natDegree_X,mul_one] at degree
  exact ⟨P,pn,hP,by simpa only [Nat.mul_comm d,Nat.add_comm] using degree⟩

theorem conjugate_bound [IsGalois (RatFunc K) E] {J : Type*} [Fintype J] [DecidableEq J]
    (e d:ℕ) (ep:0<e) (T:Finset K) (B:Matrix J J E)
    (det:B.det≠0) (finite:IsIntegral (Polynomial K) B.det)
    (inf:IsIntegral (SheetNorm.Infinity K) ((algebraMap (RatFunc K) E RatFunc.X)^d*B.det/
      algebraMap (RatFunc K) E (RatFunc.X^(T.card*Fintype.card J))))
    (O:K→Type*) [∀ z,CommRing (O z)] [∀ z,IsDomain (O z)] [∀ z,IsLocalRing (O z)]
    (φ:∀z,(Polynomial K)→+*O z) (incl:∀z,O z→+*E) (inj:∀z,Function.Injective (incl z))
    (base:∀z,(incl z).comp (φ z)=(algebraMap (RatFunc K) E).comp (algebraMap (Polynomial K) (RatFunc K)))
    (π:∀z,O z) (place:∀ z∈T,π z≠0 ∧ IsLocalRing.residue _ (π z)=0 ∧ φ z (Polynomial.X-C z)=π z)
    (A:∀z,SheetNorm.Aut K E→Matrix J J (O z)) (row:K→SheetNorm.Aut K E→Finset J)
    (lift:∀ z∈T,∀g i j,incl z (A z g i j)=g (B i j))
    (outside:∀ z∈T,∀g,∀i∈row z g,∀j,π z∣A z g i j)
    (count:∀ z∈T,e*(∑g:SheetNorm.Aut K E,(row z g).card)=
      Fintype.card (SheetNorm.Aut K E)*((e-1)*Fintype.card J)) :
    e*d≤T.card*Fintype.card J := by
  obtain ⟨P,pn,eq,cap⟩:=norm_degree B.det det finite _ _ inf
  have size:Fintype.card (SheetNorm.Aut K E)=finrank (RatFunc K) E := by
    rw [Fintype.card_eq_nat_card,IsGalois.card_aut_eq_finrank]
  apply pole_degree e d ep T P pn (size ▸ cap) O φ π place A row _ outside count
  intro z hz
  apply inj z
  have mapP := DFunLike.congr_fun (base z) P
  change incl z (φ z P)=algebraMap (RatFunc K) E (algebraMap (Polynomial K) (RatFunc K) P) at mapP
  rw [mapP,eq,Algebra.norm_eq_prod_automorphisms,map_prod]
  apply Finset.prod_congr rfl
  intro g _
  rw [RingHom.map_det,AlgEquiv.map_det]
  exact congrArg Matrix.det (Matrix.ext (fun i j=>(lift z hz g i j).symm))

#print axioms norm_degree
#print axioms conjugate_bound
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedEvaluationNorm

-- merged module R6960MarkedPrimitiveMinor
section Merged_R6960MarkedPrimitiveMinor
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MarkedEvaluation
open Polynomial Module Matrix Finset
open scoped Polynomial Matrix BigOperators
variable {k I J : Type} [Field k] [Fintype I] [DecidableEq I] [Fintype J]
local notation "F" => FractionRing (Polynomial k)
local notation "ι" => algebraMap (Polynomial k) F
theorem primitive_minor (M:Matrix I J F) (full:∃ pick:I↪J,(M.submatrix id pick).det≠0)
    (independent:LinearIndependent k M.col) :
    ∃ (Q:Matrix I J (Polynomial k)) (T:Matrix J I (Polynomial k)) (B:Matrix I I F) (pick:I↪J),
      Q*T=1 ∧ M=B*Q.map ι ∧ B=M*T.map ι ∧ (Q.submatrix id pick).det≠0 ∧
      Fintype.card J≤Fintype.card I+(Q.submatrix id pick).det.natDegree := by
  classical
  obtain ⟨Q,T,B,d,idQ,represent,degrees,lead⟩:=
    P1_7_1_1_2.exists_reduced_rows M (P1_7_1_1_2.exists_split_rows M full)
  obtain ⟨pick,nz,maximal⟩:=P1_7_1_1_2.exists_minor_of_degree_sum Q d degrees lead
  have back : B=M*T.map ι := by
    rw [represent,Matrix.mul_assoc,←Matrix.map_mul,idQ,Matrix.map_one _ (map_zero _) (map_one _),Matrix.mul_one]
  let V:=fun i=>degreeLT k (d i+1)
  let col (j:J) (i:I):V i:=⟨Q i j, by
    apply mem_degreeLT.mpr
    exact (degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le (degrees i j)))⟩
  let coeff (i:I) : V i→ₗ[k]F :=
    (IsScalarTower.toAlgHom k (Polynomial k) F).toLinearMap.comp (degreeLT k (d i+1)).subtype
  let values : (∀i,V i)→ₗ[k](I→F):=LinearMap.pi (fun i=>(coeff i).comp (LinearMap.proj i))
  let forward:=((Matrix.toLin' B).restrictScalars k).comp values
  have eq : forward ∘ col=M.col := by
    funext j i
    change (B*ᵥ(fun l=>ι (Q l j))) i=M i j
    rw [represent]; rfl
  have indep : LinearIndependent k col := LinearIndependent.of_comp forward (eq ▸ independent)
  let finite (i:I) : Module.Finite k (V i) := Module.Finite.of_basis (degreeLT.basis k (d i+1))
  have count:=indep.fintype_card_le_finrank
  have dim (i:I):finrank k (V i)=d i+1 := by simpa only [Fintype.card_fin] using finrank_eq_card_basis (degreeLT.basis k (d i+1))
  rw [Module.finrank_pi_fintype] at count
  simp only [dim,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,mul_one] at count
  exact ⟨Q,T,B,pick,idQ,represent,back,nz,by omega⟩
#print axioms primitive_minor
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedPrimitiveMinor

-- merged module R6960MarkedHorizontalRows
section Merged_R6960MarkedHorizontalRows
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MarkedEvaluation
open Polynomial Module Matrix LinearMap Finset
open scoped Polynomial Matrix BigOperators
open P1_7_1_1_2 (exists_full_minor)
variable {k K I J:Type} [Field k] [Infinite k] [Field K] [Algebra k K]
  [Fintype I] [Fintype J] [DecidableEq J]
theorem translated_minor (P:Matrix I J (Polynomial K)) (li:LinearIndependent K P.col) :
    ∃ N:ℕ, ∃ shifts:Fin N ↪ k, ∃ rows:J↪(Fin N×I),
      (Matrix.of (fun u v:J=>Polynomial.taylor (algebraMap k K (shifts (rows u).1)) (P (rows u).2 v))).det≠0 := by
  classical
  let m:=Finset.univ.sup (fun ij:I×J=>(P ij.1 ij.2).natDegree)
  let pts:Fin (m+1)↪k := Fin.valEmbedding.trans (Infinite.natEmbedding k)
  let val:Fin (m+1)↪K := pts.trans ⟨_,(algebraMap k K).injective⟩
  let V:=degreeLT K (m+1)
  let C (j:J) (i:I):V:=⟨P i j,mem_degreeLT.mpr (degree_le_natDegree.trans_lt
    (by exact_mod_cast Nat.lt_succ_of_le (show (P i j).natDegree≤m from Finset.le_sup (f:=fun ij:I×J=>(P ij.1 ij.2).natDegree) (Finset.mem_univ (i,j)))))⟩
  let proj:(I→V) →ₗ[K] (I→(Polynomial K)) := LinearMap.pi (fun i=>V.subtype.comp (LinearMap.proj i))
  have ic:LinearIndependent K C := LinearIndependent.of_comp proj li
  let eval:(I→V) →ₗ[K] ((Fin (m+1)×I)→K) := LinearMap.pi (fun i=>
    (Polynomial.leval (val i.1)).comp (V.subtype.comp (LinearMap.proj i.2)))
  have inj:Function.Injective eval := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro u zero
    funext i;apply Subtype.ext
    by_contra nz
    let S:=Finset.univ.map val
    have roots : S⊆(u i).val.roots.toFinset := by
      intro x hx
      obtain ⟨a,_,rfl⟩:=Finset.mem_map.mp hx
      exact Multiset.mem_toFinset.mpr ((mem_roots nz).mpr (congrFun zero (a,i)))
    have high:= (Finset.card_le_card roots).trans
      ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _))
    have d:=(natDegree_lt_iff_degree_lt nz).mpr (mem_degreeLT.mp (u i).property)
    have card : S.card=m+1 := by simp [S]
    omega
  let test : Matrix (Fin (m+1)×I) J K := fun i j=>(P i.2 j).eval (val i.1)
  have independent : LinearIndependent K test.transpose.row := ic.map' eval (LinearMap.ker_eq_bot.mpr inj)
  obtain ⟨rows,good⟩:=P1_7_1_1_2.exists_full_minor test.transpose independent
  refine ⟨m+1,pts,rows,?_⟩
  intro vanish
  let M := Matrix.of (fun u v:J=>Polynomial.taylor (algebraMap k K (pts (rows u).1)) (P (rows u).2 v))
  have eq:(evalRingHom (0:K)).mapMatrix M=(test.transpose.submatrix _root_.id rows).transpose := by
    ext i j
    change (Polynomial.taylor _ _).eval 0=_
    rw [taylor_eval,zero_add];rfl
  apply good
  rw [←Matrix.det_transpose,←eq,←RingHom.map_det]
  exact (congrArg (evalRingHom (0:K)) vanish).trans (map_zero _)
#print axioms translated_minor
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedHorizontalRows

-- merged module R6960MarkedHorizontalBasis
section Merged_R6960MarkedHorizontalBasis
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MarkedEvaluation
open Polynomial Module Matrix LinearMap
open scoped Polynomial Matrix BigOperators
open P1_7_1_1_2 (exists_full_minor)
variable {k K F E I J:Type} [Field k] [Infinite k] [Field K] [Algebra k K]
  [Field F] [Algebra (Polynomial K) F] [IsFractionRing (Polynomial K) F] [Algebra K F] [IsScalarTower K (Polynomial K) F]
  [Field E] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
def translateField (F:Type) [Field F] [Algebra (Polynomial K) F] [IsFractionRing (Polynomial K) F] (a:K) : F≃+* F :=
  IsFractionRing.ringEquivOfRingEquiv (K:=F) (L:=F) (taylorEquiv a).toRingEquiv
theorem translate_polynomial (a:K) (p:(Polynomial K)) :
    translateField F a (algebraMap (Polynomial K) F p)=algebraMap (Polynomial K) F (taylor a p) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _
theorem section_coordinates (b:Basis I F E) (v:J→E) (li:LinearIndependent K v) :
    ∃ N:ℕ,∃ shifts:Fin N↪k,∃ pick:J↪(Fin N×I),
      (Matrix.of (fun i j:J=>translateField F (algebraMap k K (shifts (pick i).1))
        (b.repr (v j) (pick i).2))).det≠0 := by
  classical
  let inc:=algebraMap (Polynomial K) F
  obtain ⟨d,h⟩:=IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (Polynomial K))
    (fun z:I×J=>b.repr (v z.2) z.1)
  choose q eq using h
  let P:Matrix I J (Polynomial K):=fun i j=>q (i,j)
  have poly (i j):inc (P i j)=inc (d:(Polynomial K))*b.repr (v j) i := by
    simpa only [Algebra.smul_def] using eq (i,j)
  have dn:inc (d:(Polynomial K))≠0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (mem_nonZeroDivisors_iff_ne_zero.mp d.property)
  let lift:(I→(Polynomial K)) →ₗ[K] (I→F) := LinearMap.pi (fun i=>(IsScalarTower.toAlgHom K (Polynomial K) F).toLinearMap.comp (LinearMap.proj i))
  let invert:(I→F) →ₗ[F] E := (inc (d:(Polynomial K)))⁻¹ • b.equivFun.symm.toLinearMap
  let recover:= (invert.restrictScalars K).comp lift
  have coord (j) : lift (P.col j)=inc (d:(Polynomial K)) • b.equivFun (v j) := funext (fun i=>poly i j)
  have vector : recover ∘ P.col =v := by
    funext j
    change (inc (d:(Polynomial K)))⁻¹ • b.equivFun.symm (lift (P.col j))=v j
    rw [coord,map_smul,LinearEquiv.symm_apply_apply,inv_smul_smul₀ dn]
  obtain ⟨N,sh,rows,nonzero⟩:=translated_minor (k:=k) P (LinearIndependent.of_comp recover (vector ▸ li))
  refine ⟨N,sh,rows,?_⟩
  let scale (i:J):=translateField F (algebraMap k K (sh (rows i).1)) (inc (d:(Polynomial K)))
  let V:Matrix J J F:=fun i j=>translateField F (algebraMap k K (sh (rows i).1)) (b.repr (v j) (rows i).2)
  let M:Matrix J J (Polynomial K):=fun i j=>taylor (algebraMap k K (sh (rows i).1)) (P (rows i).2 j)
  have values : inc.mapMatrix M=Matrix.of (fun i j=>scale i*V i j) := by
    ext i j
    change inc (taylor _ _)=_
    rw [←translate_polynomial,poly,map_mul];rfl
  intro vanish
  have zero:=congrArg Matrix.det values
  rw [←RingHom.map_det,Matrix.det_mul_column] at zero
  change V.det=0 at vanish
  exact nonzero ((map_eq_zero_iff _ (IsFractionRing.injective (Polynomial K) F)).mp
    (zero.trans (by rw [vanish,mul_zero])))
theorem sheet_minor {H B C : Type} [Field H] [Field B] [Algebra H B] [Fintype C]
    {e:ℕ} (values:Matrix (C×Fin e) J H) (full:∃ pick:J↪(C×Fin e),(values.submatrix pick _root_.id).det≠0)
    (y:C→Fin e→B) (simple:∀c,Function.Injective (y c)) :
    let A:Matrix (C×Fin e) J B:=fun u j=>∑i:Fin e,algebraMap H B (values (u.1,i) j)*(y u.1 u.2)^i.val
    ∃ pick:J↪(C×Fin e),(A.submatrix pick _root_.id).det≠0 := by
  classical
  let A:Matrix (C×Fin e) J B:=fun u j=>∑i:Fin e,algebraMap H B (values (u.1,i) j)*(y u.1 u.2)^i.val
  obtain ⟨sel,sn⟩:=full
  have st: ((algebraMap H B).mapMatrix (values.submatrix sel _root_.id)).det≠0 := by
    rw [←RingHom.map_det];exact (map_ne_zero_iff _ (algebraMap H B).injective).mpr sn
  have inj : Function.Injective A.mulVec := by
    change Function.Injective A.mulVecLin
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro w hw
    have rows (c:C) (i:Fin e) : ∑ j,algebraMap H B (values (c,i) j)*w j=0 := by
      let coeff (d:Fin e):=∑ j,algebraMap H B (values (c,d) j)*w j
      have atRoot (t:Fin e) : (Matrix.vandermonde (y c)*ᵥcoeff) t=0 := by
        have z:=congrFun hw (c,t)
        change (∑ j,(∑d:Fin e,algebraMap H B (values (c,d) j)*(y c t)^d.val)*w j)=0 at z
        change (∑d:Fin e,(y c t)^d.val*(∑ j,algebraMap H B (values (c,d) j)*w j))=0
        simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
        simp_rw [Finset.sum_mul] at z
        simpa only [mul_left_comm,mul_assoc,mul_comm] using z
      have injV:=Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr
        (Matrix.det_vandermonde_ne_zero_iff.mpr (simple c)).isUnit)
      have eq:coeff=0:=injV ((funext atRoot).trans (Matrix.mulVec_zero _).symm)
      exact congrFun eq i
    have vec:(algebraMap H B).mapMatrix (values.submatrix sel _root_.id) *ᵥ w=0 := funext (fun i=>rows _ _)
    apply ((Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr st.isUnit)))
    rwa [Matrix.mulVec_zero]
  have li : LinearIndependent B A.transpose.row := Matrix.mulVec_injective_iff.mp inj
  obtain ⟨pick,good⟩:=P1_7_1_1_2.exists_full_minor A.transpose li
  refine ⟨pick,?_⟩
  change (A.submatrix pick _root_.id).det≠0
  rw [←Matrix.det_transpose];exact good
#print axioms section_coordinates
#print axioms sheet_minor
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedHorizontalBasis

-- merged module R6960MarkedSheetFrame
section Merged_R6960MarkedSheetFrame
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MarkedEvaluation
open Polynomial Module Matrix Algebra Finset
open scoped Polynomial Matrix BigOperators
variable {F E Ω : Type} [Field F] [Field E] [Algebra F E] [Field Ω]
private def atRoot (b:PowerBasis F E) (h:F→+*Ω) (y:Ω) (hy:(minpoly F b.gen).eval₂ h y=0) : E→+*Ω :=
  letI := h.toAlgebra
  (b.lift y hy).toRingHom
private theorem atRoot_base (b:PowerBasis F E) (h:F→+*Ω) (y:Ω) (hy:(minpoly F b.gen).eval₂ h y=0) (c:F) :
    atRoot b h y hy (algebraMap F E c)=h c := by
  letI:=h.toAlgebra
  exact (b.lift y hy).commutes c
private theorem atRoot_value (b:PowerBasis F E) (h:F→+*Ω) (y:Ω) (hy:(minpoly F b.gen).eval₂ h y=0) (v:E) :
    atRoot b h y hy v=∑ i:Fin b.dim,h (b.basis.repr v i)*y^i.val := by
  letI := h.toAlgebra
  conv_lhs => arg 2; rw [←b.basis.sum_repr v]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Algebra.smul_def,map_mul,atRoot_base,b.basis_eq_pow,map_pow]
  exact congrArg (h (b.basis.repr v i)*·) (congrArg (·^i.val) (b.lift_gen y hy))
variable {k K J:Type} [Field k] [Infinite k] [Field K] [Algebra k K]
  [Algebra (Polynomial K) F] [IsFractionRing (Polynomial K) F] [Algebra K F] [IsScalarTower K (Polynomial K) F]
  [Algebra K E] [IsScalarTower K F E] [Fintype J] [DecidableEq J]
theorem horizontal_frame_over {F' : Type} [Field F'] (exchange:F≃+*F')
    (b:PowerBasis F E) (simple:(minpoly F b.gen).Separable) (v:J→E) (li:LinearIndependent K v) :
    ∃ p:(Polynomial F'),p.Separable ∧ ∃ offsets:J→k, ∃ ev:J→(E→+*p.SplittingField),
      (∀j a,ev j (algebraMap F E a)=algebraMap F' p.SplittingField (exchange (translateField F (algebraMap k K (offsets j)) a))) ∧
      (Matrix.of (fun i j:J=>ev i (v j))).det≠0 := by
  classical
  obtain ⟨N,sh,pick,full⟩:=section_coordinates (k:=k) b.basis v li
  let τ (i:Fin N):=(translateField F (algebraMap k K (sh i))).trans exchange
  let q (i:Fin N):=(minpoly F b.gen).map (τ i).toRingHom
  let polys:=Finset.univ.image q
  let p:=∏ f∈polys,f
  have mon (i) : (q i).Monic := (minpoly.monic b.isIntegral_gen).map _
  have irr (i) : Irreducible (q i) :=
    (MulEquiv.irreducible_iff (Polynomial.mapEquiv (τ i))).mpr (minpoly.irreducible b.isIntegral_gen)
  have sep : p.Separable := by
    apply Polynomial.separable_prod'
    · rintro _ ha _ hb ne
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp ha
      obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hb
      exact (irr i).coprime_iff_not_dvd.mpr
        (fun dv=>ne (eq_of_monic_of_associated (mon i) (mon j) ((irr i).associated_of_dvd (irr j) dv)))
    · rintro _ h
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp h; exact simple.map
  let S:=p.SplittingField
  let incl:=algebraMap F' S
  have splits (i) : ((q i).map incl).Splits := by
    have dvd : q i∣p := Finset.dvd_prod_of_mem _ (Finset.mem_image_of_mem q (Finset.mem_univ i))
    exact Polynomial.Splits.of_dvd (SplittingField.splits p) ((Polynomial.map_ne_zero_iff incl.injective).mpr sep.ne_zero)
      (Polynomial.map_dvd incl dvd)
  have size (i) : Fintype.card ((q i).rootSet S)=b.dim := by
    rw [Polynomial.card_rootSet_eq_natDegree simple.map (splits i),show (q i).natDegree=(minpoly F b.gen).natDegree
      from natDegree_map_eq_of_injective (τ i).injective _,b.natDegree_minpoly]
  let idx (i) := Fintype.equivOfCardEq (show Fintype.card (Fin b.dim)=Fintype.card ((q i).rootSet S) by rw [size,Fintype.card_fin])
  let roots (i:Fin N) (j:Fin b.dim):S:=(idx i j).val
  have distinct (i) : Function.Injective (roots i) := Subtype.val_injective.comp (idx i).injective
  let emb (i:Fin N) := incl.comp (τ i).toRingHom
  have isRoot (i j) : (minpoly F b.gen).eval₂ (emb i) (roots i j)=0 := by
    have h := (Polynomial.mem_rootSet.mp (idx i j).property).2
    change (q i).eval₂ incl (roots i j)=0 at h
    rw [show q i=(minpoly F b.gen).map (τ i).toRingHom from rfl,eval₂_map] at h
    exact h
  let C:Matrix (Fin N×Fin b.dim) J F':=fun r j=>τ r.1 (b.basis.repr (v j) r.2)
  let before:Matrix J J F:=fun i j=>translateField F (algebraMap k K (sh (pick i).1)) (b.basis.repr (v j) (pick i).2)
  have mapped : (C.submatrix pick _root_.id).det≠0 := by
    change (exchange.toRingHom.mapMatrix before).det≠0
    rw [←RingHom.map_det];exact (map_ne_zero_iff _ exchange.injective).mpr full
  obtain ⟨r,det⟩:=sheet_minor C ⟨pick,mapped⟩ roots distinct
  let row (u:J):=atRoot b (emb (r u).1) (roots (r u).1 (r u).2) (isRoot (r u).1 (r u).2)
  refine ⟨p,sep,fun u=>sh (r u).1,row,fun j a=>atRoot_base ..,?_⟩
  let A:Matrix J J S:=fun i j=>∑ h:Fin b.dim, incl (C ((r i).1,h) j)*(roots (r i).1 (r i).2)^h.val
  have eqMat : (Matrix.of (fun i j:J=>row i (v j)))=A := by
    apply Matrix.ext
    intro i j
    exact atRoot_value b (emb (r i).1) (roots (r i).1 (r i).2) (isRoot (r i).1 (r i).2) (v j)
  rw [eqMat];exact det
theorem horizontal_frame (b:PowerBasis F E) (simple:(minpoly F b.gen).Separable) (v:J→E) (li:LinearIndependent K v) :
    ∃ p:(Polynomial F),p.Separable ∧ ∃ offsets:J→k, ∃ ev:J→(E→+*p.SplittingField),
      (∀j a,ev j (algebraMap F E a)=algebraMap F p.SplittingField (translateField F (algebraMap k K (offsets j)) a)) ∧
      (Matrix.of (fun i j:J=>ev i (v j))).det≠0 :=
  horizontal_frame_over (RingEquiv.refl F) b simple v li
#print axioms horizontal_frame_over
#print axioms horizontal_frame
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedSheetFrame

-- merged module R6960MarkedResidueRows
section Merged_R6960MarkedResidueRows
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MarkedEvaluation
open Polynomial Finset MulAction
open scoped BigOperators Polynomial
theorem distinct_residues {R k I:Type*} [CommRing R] [IsDomain R] [Field k]
    (ρ:R→+*k) (q:(Polynomial R)) (sep:(q.map ρ).Separable) (y:I→R) (inj:Function.Injective y)
    (root:∀i,q.eval (y i)=0) : Function.Injective (fun i=>ρ (y i)) := by
  intro i j eq
  by_contra ne
  obtain ⟨h,fac⟩:=dvd_iff_isRoot.mpr (root i)
  have other:h.eval (y j)=0 := by
    have hh:=root j
    rw [fac,eval_mul,eval_sub,eval_X,eval_C] at hh
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr (inj.ne (Ne.symm ne)))
  obtain ⟨g,rest⟩:=dvd_iff_isRoot.mpr other
  have dvd : (Polynomial.X-C (ρ (y i)))^2 ∣ q.map ρ := by
    refine ⟨g.map ρ,?_⟩
    change ρ (y i)=ρ (y j) at eq
    simp only [fac,rest,Polynomial.map_mul,Polynomial.map_sub,map_X,map_C,eq,pow_two,mul_assoc]
  have unit:=sep.squarefree _ (by simpa only [pow_two] using dvd)
  exact (irreducible_X_sub_C _).not_isUnit unit
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [IsGalois F E] [FiniteDimensional F E]
local notation "G" => E ≃ₐ[F] E
private theorem orbit_roots (y:E) : MulAction.orbit G y = (minpoly F y).rootSet E := by
  ext t
  rw [←Normal.minpoly_eq_iff_mem_orbit,Polynomial.mem_rootSet]
  have alg:IsIntegral F y:=Algebra.IsIntegral.isIntegral y
  constructor
  · intro eq
    exact ⟨minpoly.ne_zero alg,eq ▸ minpoly.aeval F t⟩
  · rintro ⟨_,root⟩
    exact minpoly.eq_of_root alg.isAlgebraic root
theorem actual_unmarked_rows {J U:Type*} [Fintype J] [DecidableEq J] (e:ℕ)
    (y:J→E) (degree:∀j,(minpoly F (y j)).natDegree=e)
    {O:Type*} [CommRing O] [IsDomain O] [IsLocalRing O] (incl:O→+*E) (inj:Function.Injective incl)
    (q:J→(Polynomial O)) (sep:∀j,((q j).map (IsLocalRing.residue O)).Separable)
    (lift:∀ j, MulAction.orbit G (y j)→O) (value:∀j i,incl (lift j i)=i.val)
    (root:∀j i,(q j).eval (lift j i)=0) (word:J→O)
    (π:O) (A:G→Matrix J U O)
    (annihilates:∀g i j, π∣(lift i ⟨g (y i),⟨g,rfl⟩⟩-word i)*A g i j) :
    ∃ rows:G→Finset J, (∀g,∀i∈rows g,∀j,π∣A g i j) ∧
      e*(∑g:G,(rows g).card)=Fintype.card G*((e-1)*Fintype.card J) := by
  classical
  let I (j:J):Type _:=↥(MulAction.orbit G (y j))
  let fint (j:J):Fintype (I j) := (Finite.finite_mulAction_orbit (M:=G) (y j)).fintype
  have card (j:J) : Fintype.card (I j)=e := by
    calc _ = Fintype.card ((minpoly F (y j)).rootSet E) := Fintype.card_congr
           (Equiv.cast (congrArg (fun s:Set E=>↥s) (orbit_roots (F:=F) (y j))))
         _ = _ := (Polynomial.card_rootSet_eq_natDegree (IsGalois.separable F (y j))
           ((inferInstance : Normal F E).splits (y j))).trans (degree j)
  let pick (j:J):I j:=⟨y j,MulAction.mem_orbit_self (y j)⟩
  let res:=IsLocalRing.residue O
  have separates (j:J) : Function.Injective (fun a:I j=>res (lift j a)) :=
    distinct_residues res (q j) (sep j) _ (fun a b eq=>Subtype.ext
      ((value j a).symm.trans ((congrArg incl eq).trans (value j b)))) (root j)
  let chosen (j:J) : I j := if h:∃a:I j,res (lift j a)=res (word j) then h.choose else pick j
  have off (j:J) (a:I j) (ne:a≠chosen j) : res (lift j a)≠res (word j) := by
    intro eq
    have existsHit : ∃t:I j,res (lift j t)=res (word j) := ⟨a,eq⟩
    apply ne
    apply separates j
    simpa [chosen,existsHit] using eq.trans existsHit.choose_spec.symm
  let rows (g:G):=Finset.univ.filter (fun j=>g • pick j ≠chosen j)
  refine ⟨rows,fun g i hi j=>?_,row_average I e card pick chosen⟩
  have nz := off i (g • pick i) (Finset.mem_filter.mp hi).2
  have unit : IsUnit (lift i (g • pick i)-word i) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by rw [map_sub];exact sub_ne_zero.mpr nz)
  exact unit.dvd_mul_left.mp (annihilates g i j)
#print axioms distinct_residues
#print axioms actual_unmarked_rows
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedResidueRows

-- merged module R6960MarkedScalarPlace
section Merged_R6960MarkedScalarPlace
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace Lower6960.MarkedEvaluation
open Polynomial IsLocalRing
open scoped Polynomial
variable (K Ω:Type) [Field K] [Field Ω] [Algebra (RatFunc K) Ω]
local notation "j" => algebraMap (Polynomial K) (RatFunc K)
local notation "ι" => algebraMap (RatFunc K) Ω
structure MarkPlace (z:K) where
  V : ValuationSubring Ω
  lift : (Polynomial K)→+*V
  value : ∀p,(lift p:Ω)=ι (j p)
  specialize : ∀p,residue V (lift p)=residue V (lift (C (p.eval z)))
def markPlace (z:K) : MarkPlace K Ω z := by
  apply Classical.choice
  let P:=RingHom.ker (evalRingHom z)
  letI : P.IsPrime:=RingHom.ker_isPrime _
  let A:=Localization.AtPrime P
  let b:=algebraMap (Polynomial K) A
  let f: A→+*Ω:=(algebraMap (RatFunc K) Ω).comp (CollisionTame.branchFractionHom P)
  obtain ⟨V,h,loc⟩:=IsLocalRing.exists_factor_valuationRing f
  let g:A→+*V:=f.codRestrict V.toSubring h
  let l:=g.comp b
  have hπ:residue V (l (Polynomial.X-C z))=0 := by
    apply (residue_eq_zero_iff _).mpr
    change ¬IsUnit (g (b (Polynomial.X-C z)))
    intro u
    have nu:¬IsUnit (b (Polynomial.X-C z)) := by
      intro bunit
      have outside:Polynomial.X-C z ∈ P.primeCompl :=
        (IsLocalization.AtPrime.isUnit_to_map_iff A P _).mp bunit
      apply outside
      change (Polynomial.X-C z).eval z=0
      rw [eval_sub,eval_X,eval_C,sub_self]
    exact nu (IsUnit.of_map g _ u)
  refine ⟨⟨V,l,fun p=>congrArg (algebraMap (RatFunc K) Ω) (CollisionTame.branchFractionHom_apply _ _),fun p=>?_⟩⟩
  have reducing : ((residue V).comp l)=(((residue V).comp l).comp C).comp (evalRingHom z) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply,coe_evalRingHom,eval_C]
    · change residue V (l Polynomial.X)=residue V (l (C (Polynomial.X.eval z)))
      rw [eval_X];rwa [map_sub,map_sub,sub_eq_zero] at hπ
  exact DFunLike.congr_fun reducing p
namespace MarkPlace
variable {K Ω} {z:K} (P:MarkPlace K Ω z)
def pi := P.lift (Polynomial.X-C z)
theorem pi_ne : P.pi≠0 := by
  intro h
  have exactValue:=P.value (Polynomial.X-C z)
  rw [show P.lift (Polynomial.X-C z)=0 from h] at exactValue
  exact ((map_ne_zero_iff _ (algebraMap (RatFunc K) Ω).injective).mpr
    ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial K) (RatFunc K))).mpr (X_sub_C_ne_zero z))) exactValue.symm
theorem pi_residue : residue P.V P.pi=0 := by
  have hz:((Polynomial.X:(Polynomial K))-C z).eval z=0 := by simp
  rw [pi,P.specialize,hz,map_zero,map_zero,map_zero]
theorem lift_unit {p:(Polynomial K)} (nz:p.eval z≠0) : IsUnit (P.lift p) := by
  apply (residue_ne_zero_iff_isUnit _).mp
  rw [P.specialize]
  exact (map_ne_zero_iff _ (((residue P.V).comp P.lift).comp (C:K→+*(Polynomial K))).injective).mpr nz
theorem separable {q:(Polynomial (Polynomial K))} (sep:(q.map (evalRingHom z)).Separable) :
    ((q.map P.lift).map (residue P.V)).Separable := by
  have eq : (residue P.V).comp P.lift=((((residue P.V).comp P.lift).comp C).comp (evalRingHom z)) :=
    RingHom.ext P.specialize
  rw [Polynomial.map_map,eq,←Polynomial.map_map]
  exact sep.map
theorem integral_mem [Algebra (Polynomial K) Ω] [IsScalarTower (Polynomial K) (RatFunc K) Ω]
    {x:Ω} (hx:IsIntegral (Polynomial K) x) : x∈P.V := by
  letI : Algebra (Polynomial K) P.V:=P.lift.toAlgebra
  letI : IsScalarTower (Polynomial K) P.V Ω:=IsScalarTower.of_algebraMap_eq (fun a=>
    (IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) Ω a).trans (P.value a).symm)
  obtain ⟨v,hv⟩:=IsIntegrallyClosed.isIntegral_iff.mp (hx.tower_top (A:=P.V))
  exact hv ▸ v.property
end MarkPlace
#print axioms markPlace
#print axioms MarkPlace.integral_mem
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedScalarPlace

end Merged6967_R6960MarkedScalarPlace

section Merged6967_R6960RetainedCompressionPureNodes
set_option Elab.async false






set_option Elab.async false

-- merged module R6960HeightCompression
section Merged_R6960HeightCompression
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace Lower6960.HeightCompression
open Polynomial Matrix
open scoped BigOperators Polynomial Matrix
variable {F : Type*} [Field F] {ι α : Type*} [Fintype ι]
abbrev Coeffs (F : Type*) [Field F] {ι : Type*} (weight : ι→ℕ) (width : ℕ) :=
  ∀ j,degreeLT F (width-weight j)
def evaluation (A : Matrix α ι (Polynomial F)) (weight : ι→ℕ) (width : ℕ) :
    Coeffs F weight width →ₗ[F] (α→(Polynomial F)) where
  toFun v i := ∑ j,A i j*(v j : (Polynomial F))
  map_add' v w := by funext i; simp [mul_add,Finset.sum_add_distrib]
  map_smul' c v := by funext i; simp [Finset.smul_sum]
theorem weighted_kernel [Finite α] (A : Matrix α ι (Polynomial F)) (weight : ι→ℕ) (width : ℕ)
    (col : ∀ i j,(A i j).natDegree≤weight j) (k : ℕ)
    (ker : k≤Module.finrank (FractionRing (Polynomial F))
      (LinearMap.ker (A.map (algebraMap (Polynomial F) (FractionRing (Polynomial F)))).mulVecLin)) :
    (∑ j : ι, (width-weight j)) ≤ (Fintype.card ι-k)*width+
      Module.finrank F (LinearMap.ker (evaluation A weight width)) := by
  classical
  let E:=FractionRing (Polynomial F)
  let a:=algebraMap (Polynomial F) E
  let M:=A.map a
  let R:=Submodule.span E (Set.range M.row)
  let m:=Module.finrank E R
  have rank : m+Module.finrank E (LinearMap.ker M.mulVecLin)=Fintype.card ι := by
    have h:=M.mulVecLin.finrank_range_add_finrank_ker
    change M.rank+_= _ at h
    rw [M.rank_eq_finrank_span_row,Module.finrank_pi_fintype] at h
    simpa [m,R] using h
  have bound : m≤Fintype.card ι-k := by
    change k≤Module.finrank E (LinearMap.ker M.mulVecLin) at ker
    omega
  obtain ⟨B,mem,span,_⟩:=Submodule.exists_fun_fin_finrank_span_eq E (Set.range M.row)
  change Fin m → (ι→E) at B
  choose row hrow using mem
  have fits (v : Coeffs F weight width) (i : α) :
      (evaluation A weight width v i)∈degreeLT F width := by
    apply Submodule.sum_mem
    intro j _
    by_cases z : (v j : (Polynomial F))=0
    · simp [z]
    by_cases c : A i j=0
    · simp [c]
    apply mem_degreeLT.mpr
    apply (natDegree_lt_iff_degree_lt (mul_ne_zero c z)).mp
    have h:= (natDegree_lt_iff_degree_lt z).mpr (mem_degreeLT.mp (v j).property)
    have u:= (natDegree_mul_le (p:=A i j) (q:=(v j:(Polynomial F)))).trans (Nat.add_le_add_right (col i j) _)
    omega
  let small : Coeffs F weight width →ₗ[F] (Fin m → degreeLT F width) :=
    LinearMap.pi fun i => (((LinearMap.proj (row i)).comp (evaluation A weight width)).codRestrict
      (degreeLT F width) (fun v => fits v (row i)))
  have eq : LinearMap.ker small=LinearMap.ker (evaluation A weight width) := by
    ext v
    simp only [LinearMap.mem_ker]
    constructor
    · intro hv
      let ev : ι→E:=fun j=>a (v j : (Polynomial F))
      have hb (i : Fin m) : B i ⬝ᵥ ev=0 := by
        rw [←hrow i]
        have h:=congrArg (fun g : Fin m → degreeLT F width => (g i : (Polynomial F))) hv
        change (∑ j,A (row i) j*(v j : (Polynomial F)))=0 at h
        simpa [ev,M,Matrix.row,dotProduct] using congrArg a h
      funext i
      apply IsFractionRing.injective (Polynomial F) E
      have hi : M.row i∈Submodule.span E (Set.range B) := by
        rw [span]; exact Submodule.subset_span ⟨i,rfl⟩
      have zero : M.row i ⬝ᵥ ev=0 := by
        refine Submodule.span_induction (p:=fun x _=>x ⬝ᵥ ev=0) ?_ ?_ ?_ ?_ hi
        · rintro _ ⟨j,rfl⟩; exact hb j
        · exact zero_dotProduct _
        · intro x y _ _ hx hy; rw [add_dotProduct,hx,hy,add_zero]
        · intro c x _ hx; rw [smul_dotProduct,hx,smul_zero]
      simpa [evaluation,ev,M,Matrix.row,dotProduct] using zero
    · intro hv
      funext i
      apply Subtype.ext
      exact congrFun hv (row i)
  have source : Module.finrank F (Coeffs F weight width)=∑ j : ι, (width-weight j) := by
    simp [Coeffs,Module.finrank_pi_fintype,(degreeLTEquiv F _).finrank_eq]
  have target : Module.finrank F (Fin m → degreeLT F width)=m*width := by
    simp [Module.finrank_pi_fintype,(degreeLTEquiv F _).finrank_eq]
  have size:=small.finrank_range_add_finrank_ker
  rw [source,eq] at size
  rw [←size]
  exact Nat.add_le_add_right ((Submodule.finrank_le ..).trans
    (target.le.trans (Nat.mul_le_mul_right _ bound))) _
#print axioms weighted_kernel
end Lower6960.HeightCompression

end
end Merged_R6960HeightCompression

-- merged module R6960RetainedCompressionVolume
section Merged_R6960RetainedCompressionVolume
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
namespace Lower6960.RetainedCompression
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators Polynomial Matrix
abbrev Slots (a b : ℕ) := Fin (a+1) × Fin (b+1)
def columnWeight {a b : ℕ} (d : ℕ) (m : Slots a b) : ℕ := d*m.1.val
private theorem twice_width_sum (a b d W : ℕ) (hW : d*a≤W) :
    2*(∑ m : Slots a b, (W - columnWeight d m))+d*(b+1)*a*(a+1) =
      2*((a+1)*(b+1))*W := by
  have split : (∑ m : Slots a b, (W - columnWeight d m)) +
      (∑ m : Slots a b, columnWeight d m) = ((a+1)*(b+1))*W := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _ : Slots a b, W := Finset.sum_congr rfl (fun m _ => Nat.sub_add_cancel
        ((Nat.mul_le_mul_left d (Nat.le_of_lt_succ m.1.isLt)).trans hW))
      _ = _ := by simp
  have weight : 2*(∑ m : Slots a b, columnWeight d m)=d*(b+1)*a*(a+1) := by
    rw [Fintype.sum_prod_type]
    simp only [columnWeight, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
    simp only [← mul_assoc, ← Finset.mul_sum]
    have sum : (∑ i : Fin (a+1), i.val) = ∑ i∈range (a+1), i :=
      Fin.sum_univ_eq_sum_range (fun i => i) (a+1)
    rw [sum]
    calc
      _ = d*(b+1)*((∑ i∈range (a+1), i)*2) := by ring
      _ = _ := by rw [Finset.sum_range_id_mul_two,Nat.add_sub_cancel]; ring
  calc
    _ = 2*((∑ m : Slots a b, (W - columnWeight d m)) +
        (∑ m : Slots a b, columnWeight d m)) := by rw [← weight, ← Nat.mul_add]
    _ = _ := by rw [split]; ring
def paddedSeed (v : ℕ) : ℕ := 10*v
def quotientSeed (v : ℕ) : ℕ := 9*v
def boxOrdinate (e : ℕ) : ℕ := 2*e
def heightCap (e d : ℕ) : ℕ := (2*e-1)*d
def width (e d : ℕ) : ℕ := (3*e-1)*d+1
def quotientWidth (e d : ℕ) : ℕ := e*d+1
abbrev Rect (e v : ℕ) := Slots (boxOrdinate e) (paddedSeed v)
abbrev QuotRect (e v : ℕ) := Slots e (quotientSeed v)
private theorem count_comparison (e v d : ℕ) (he : 2≤e) (hd : 0<d) :
    (Fintype.card (Rect e v)-Fintype.card (QuotRect e v))*width e d +
      (∑ m : QuotRect e v, (quotientWidth e d - columnWeight d m)) <
      ∑ m : Rect e v, (width e d - columnWeight d m) := by
  let N := (2*e+1)*(10*v+1)
  let K := (e+1)*(9*v+1)
  have kN : K≤N := Nat.mul_le_mul (by omega) (by omega)
  have large : d*(2*e)≤(3*e-1)*d+1 := by
    exact (Nat.mul_comm d (2*e)).le.trans ((Nat.mul_le_mul_right d (by omega)).trans (Nat.le_add_right ..))
  have small : d*e≤e*d+1 := by rw [Nat.mul_comm d e]; omega
  let src := ∑ m : Rect e v, (width e d - columnWeight d m)
  let qt := ∑ m : QuotRect e v, (quotientWidth e d - columnWeight d m)
  have dl : 2*src+d*(10*v+1)*(2*e)*(2*e+1)=2*N*width e d :=
    twice_width_sum (2*e) (10*v) d (width e d) large
  have ds : 2*qt+d*(9*v+1)*e*(e+1)=2*K*quotientWidth e d :=
    twice_width_sum e (9*v) d (quotientWidth e d) small
  have total : 2*N*width e d=2*((N-K)*width e d)+2*K*width e d := by
    calc
      _ = 2*(N-K+K)*width e d := by rw [Nat.sub_add_cancel kN]
      _ = _ := by ring
  obtain ⟨u,hu⟩ := Nat.exists_eq_add_of_le he
  have diff : d*(9*v+1)*e*(e+1)+2*K*width e d =
      d*(10*v+1)*(2*e)*(2*e+1)+2*K*quotientWidth e d+
        d*(v*(5*u^2+27*u+16)+u^2+5*u+4) := by
    dsimp only [K,width,quotientWidth]
    rw [hu,show 3*(2+u)-1=3*u+5 by omega]
    ring
  have positive : 0<d*(v*(5*u^2+27*u+16)+u^2+5*u+4) := by positivity
  have cards : Fintype.card (Rect e v)=N ∧ Fintype.card (QuotRect e v)=K := by
    constructor
    · change Fintype.card (Fin (2*e+1) × Fin (10*v+1))=(2*e+1)*(10*v+1)
      rw [Fintype.card_prod, Fintype.card_fin,Fintype.card_fin]
    · change Fintype.card (Fin (e+1) × Fin (9*v+1))=(e+1)*(9*v+1)
      rw [Fintype.card_prod, Fintype.card_fin,Fintype.card_fin]
  rw [cards.1,cards.2]
  change (N-K)*width e d+qt<src
  omega
theorem relation_space_gt {F : Type*} [Field F] {α : Type*} [Finite α]
    {e v d : ℕ} (he : 2≤e) (hd : 0<d) (A : Matrix α (Rect e v) (Polynomial F))
    (columns : ∀ i j,(A i j).natDegree≤columnWeight d j)
    (ker : Fintype.card (QuotRect e v) ≤ Module.finrank (FractionRing (Polynomial F))
      (LinearMap.ker (A.map (algebraMap (Polynomial F) (FractionRing (Polynomial F)))).mulVecLin)) :
    Module.finrank F (HeightCompression.Coeffs F
      (fun j : QuotRect e v => columnWeight d j) (quotientWidth e d)) <
      Module.finrank F (LinearMap.ker (HeightCompression.evaluation A
        (columnWeight d) (width e d))) := by
  have lower := HeightCompression.weighted_kernel A (columnWeight d) (width e d)
    columns (Fintype.card (QuotRect e v)) ker
  have large := count_comparison e v d he hd
  have dim : Module.finrank F (HeightCompression.Coeffs F
      (fun j : QuotRect e v => columnWeight d j) (quotientWidth e d)) =
      ∑ j : QuotRect e v, (quotientWidth e d - columnWeight d j) := by
    simp [HeightCompression.Coeffs,Module.finrank_pi_fintype,(degreeLTEquiv F _).finrank_eq]
  rw [dim]
  omega
theorem tame_height {e d : ℕ} (he : e≤47) (hd : d≤164650) :
    2*((3*e-2)*(e-1)*d+(e-1))<2130706433 :=
  (Nat.mul_le_mul_left 2 (Nat.add_le_add
    (Nat.mul_le_mul (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul_left 3 he) 2)
      (Nat.sub_le_sub_right he 1)) hd)
    (Nat.sub_le_sub_right he 1))).trans_lt (by decide +kernel)
#print axioms relation_space_gt
end
end Lower6960.RetainedCompression

end Merged_R6960RetainedCompressionVolume

-- merged module R6960RetainedCompressionBox
section Merged_R6960RetainedCompressionBox
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
namespace Lower6960.RetainedCompression
noncomputable section
open Polynomial MvPolynomial Finset
open scoped Polynomial BigOperators Pointwise
abbrev Index : Type := Option PUnit
abbrev Exponent := Index →₀ ℕ
abbrev Curve (A : Type*) [CommSemiring A] := MvPolynomial Index A
abbrev ordinate : Index := none
abbrev parameter : Index := some PUnit.unit
def Exponents (a b : ℕ) : Set Exponent :=
  {m | m ordinate≤a ∧ m parameter≤b}
def exponent {a b} (m : Slots a b) : Exponent :=
  Finsupp.equivFunOnFinite.symm (fun i : Index => i.elim m.1.val (fun _ => m.2.val))
@[simp] theorem exponent_y {a b} (m : Slots a b) :
    exponent m ordinate=m.1.val := by simp [exponent]
@[simp] theorem exponent_z {a b} (m : Slots a b) :
    exponent m parameter=m.2.val := by simp [exponent]
theorem exponent_injective {a b} : Function.Injective (exponent (a:=a) (b:=b)) := by
  intro x y h
  apply Prod.ext
  · apply Fin.ext
    simpa only [exponent_y] using congrArg (fun m : Exponent => m ordinate) h
  · apply Fin.ext
    simpa only [exponent_z] using congrArg (fun m : Exponent => m parameter) h
theorem exponent_exhaustive {a b} {t : Exponent} (h : t∈Exponents a b) :
    ∃ m : Slots a b, exponent m=t := by
  refine ⟨⟨⟨_,Nat.lt_succ_of_le h.1⟩,⟨_,Nat.lt_succ_of_le h.2⟩⟩,?_⟩
  ext i
  cases i with
  | none => simp
  | some i => cases i; simp
abbrev Box (A : Type*) [CommSemiring A] (a b : ℕ) :=
  MvPolynomial.restrictSupport A (Exponents a b)
theorem box_iff {A : Type*} [CommSemiring A] (Q : Curve A) (a b : ℕ) :
    Q∈Box A a b ↔ Q.degreeOf ordinate≤a ∧ Q.degreeOf parameter≤b := by
  change (∀ m∈Q.support,m∈Exponents a b) ↔ _
  simp only [MvPolynomial.degreeOf_le_iff,Exponents,Set.mem_setOf_eq]
  exact ⟨fun h => ⟨fun m mQ => (h m mQ).1,fun m mQ => (h m mQ).2⟩,
    fun h m mQ => ⟨h.1 m mQ,h.2 m mQ⟩⟩
private def underlyingWeight (d : ℕ) (i : Option Index) : ℕ :=
  i.elim 1 (fun j => j.elim d (fun _ => 0))
def height {F : Type*} [Field F] (d : ℕ) (Q : Curve (Polynomial F)) : ℕ :=
  ((MvPolynomial.optionEquivRight F Index).symm Q).weightedTotalDegree (underlyingWeight d)
theorem height_mul {F : Type*} [Field F] (d : ℕ) {P Q : Curve (Polynomial F)} (pn : P≠0) (qn : Q≠0) :
    height d (P*Q)=height d P+height d Q := by
  let f := (MvPolynomial.optionEquivRight F Index).symm
  unfold height
  rw [map_mul,MvPolynomial.weightedTotalDegree_mul]
  · exact (map_ne_zero_iff f.toRingHom f.injective).mpr pn
  · exact (map_ne_zero_iff f.toRingHom f.injective).mpr qn
private theorem weight_exp (d i : ℕ) (m : Exponent) :
    (m.optionElim i).weight (underlyingWeight d)=i+d*m ordinate := by
  unfold underlyingWeight
  rw [Finsupp.weight_optionElim, one_mul]
  congr 1
  conv_lhs => rw [← Finsupp.optionElim_some m]
  rw [Finsupp.weight_optionElim]
  simp [Finsupp.weight_apply]
private theorem coeff_split {F : Type*} [Field F] (Q : Curve (Polynomial F)) (m : Exponent) (i : ℕ) :
    ((MvPolynomial.optionEquivRight F Index).symm Q).coeff (m.optionElim i) =
      (Q.coeff m).coeff i := by
  rw [← MvPolynomial.optionEquivRight_coeff_coeff,
    AlgEquiv.apply_symm_apply]
theorem coeff_height {F : Type*} [Field F] (d : ℕ) (Q : Curve (Polynomial F)) (m : Exponent)
    (nz : Q.coeff m≠0) : (Q.coeff m).natDegree+d*m ordinate≤height d Q := by
  have pos : m.optionElim (Q.coeff m).natDegree ∈
      ((MvPolynomial.optionEquivRight F Index).symm Q).support := by
    apply MvPolynomial.mem_support_iff.mpr
    rw [coeff_split,Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr nz
  have bound := MvPolynomial.le_weightedTotalDegree (underlyingWeight d) pos
  rwa [weight_exp] at bound
theorem height_lt_of_coeff {F : Type*} [Field F] {d W : ℕ} (positive : 0<W) (Q : Curve (Polynomial F))
    (caps : ∀ m, Q.coeff m≠0 → (Q.coeff m).natDegree+d*m ordinate<W) :
    height d Q<W := by
  apply Nat.lt_of_le_of_lt _ (Nat.sub_lt positive (by decide : 0 < (1 : ℕ)))
  unfold height MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro m hm
  rw [← Finsupp.optionElim_some m] at hm ⊢
  rw [weight_exp]
  have hn := MvPolynomial.mem_support_iff.mp hm
  rw [coeff_split] at hn
  have hi := Polynomial.le_natDegree_of_ne_zero hn
  have hc := caps m.some (fun z => hn (by rw [z,Polynomial.coeff_zero]))
  have h := (Nat.add_le_add_right hi _).trans_lt hc
  omega
def packed {F : Type*} [Field F] {a b d W : ℕ}
    (v : HeightCompression.Coeffs F (fun m : Slots a b => columnWeight d m) W) :
    Curve (Polynomial F) := ∑ m : Slots a b, MvPolynomial.monomial (exponent m) (v m : (Polynomial F))
def packLinear (F : Type*) [Field F] (a b d W : ℕ) :
    HeightCompression.Coeffs F (fun m : Slots a b => columnWeight d m) W →ₗ[F] Curve (Polynomial F) where
  toFun := packed
  map_add' v u := by
    simp only [packed,Pi.add_apply,Submodule.coe_add,map_add,Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [packed,Pi.smul_apply,Submodule.coe_smul,RingHom.id_apply,
      Finset.smul_sum,MvPolynomial.smul_monomial]
@[simp] theorem coeff_pack {F : Type*} [Field F] {a b d W : ℕ}
    (v : HeightCompression.Coeffs F (fun m : Slots a b => columnWeight d m) W)
    (m : Slots a b) :
    (packLinear F a b d W v).coeff (exponent m)=(v m : (Polynomial F)) := by
  classical
  change (packed v).coeff (exponent m)=_
  rw [packed,MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single_of_mem m (Finset.mem_univ m)]
  · simp
  · intro j _ ne
    rw [MvPolynomial.coeff_monomial, if_neg (exponent_injective.ne ne)]
private theorem coeff_pack_other {F : Type*} [Field F] {a b d W : ℕ}
    (v : HeightCompression.Coeffs F (fun m : Slots a b => columnWeight d m) W)
    {m : Exponent} (no : ∀ j : Slots a b, exponent j≠m) :
    (packLinear F a b d W v).coeff m=0 := by
  change (packed v).coeff m=0
  rw [packed,MvPolynomial.coeff_sum]
  exact Finset.sum_eq_zero (fun j _ => by rw [MvPolynomial.coeff_monomial, if_neg (no j)])
theorem pack_injective {F : Type*} [Field F] (a b d W : ℕ) :
    Function.Injective (packLinear F a b d W) := by
  intro v w eq
  funext i
  apply Subtype.ext
  rw [← coeff_pack v i,← coeff_pack w i,eq]
theorem pack_box {F : Type*} [Field F] {a b d W : ℕ}
    (v : HeightCompression.Coeffs F (fun m : Slots a b => columnWeight d m) W) :
    packLinear F a b d W v∈Box (Polynomial F) a b := by
  classical
  change ∀ m∈(packed v).support,m∈Exponents a b
  intro m pm
  by_contra hm
  have no (j : Slots a b) : exponent j≠m := by
    intro e
    apply hm
    rw [← e]
    exact ⟨by simpa only [exponent_y] using Nat.le_of_lt_succ j.1.isLt,
      by simpa only [exponent_z] using Nat.le_of_lt_succ j.2.isLt⟩
  exact MvPolynomial.mem_support_iff.mp pm (coeff_pack_other v no)
theorem pack_height {F : Type*} [Field F] {a b d W : ℕ} (positive : 0<W)
    (v : HeightCompression.Coeffs F (fun m : Slots a b => columnWeight d m) W) :
    height d (packLinear F a b d W v)<W := by
  apply height_lt_of_coeff positive
  intro m nz
  have fit : m∈Exponents a b := (pack_box v) (MvPolynomial.mem_support_iff.mpr nz)
  obtain ⟨j,rfl⟩ := exponent_exhaustive fit
  rw [coeff_pack] at nz ⊢
  rw [exponent_y]
  have hc := (Polynomial.natDegree_lt_iff_degree_lt nz).mpr (mem_degreeLT.mp (v j).property)
  change (v j : (Polynomial F)).natDegree < W-d*j.1.val at hc
  omega
theorem represented {F : Type*} [Field F] {a b d W : ℕ}
    (Q : Curve (Polynomial F)) (box : Q∈Box (Polynomial F) a b) (cap : height d Q<W) :
    ∃ v, packLinear F a b d W v=Q := by
  classical
  let v (j : Slots a b) : degreeLT F (W-columnWeight d j) :=
    ⟨Q.coeff (exponent j),by
      by_cases h : Q.coeff (exponent j)=0
      · rw [h]; exact Submodule.zero_mem _
      apply mem_degreeLT.mpr
      apply (Polynomial.natDegree_lt_iff_degree_lt h).mp
      have le := (coeff_height d Q (exponent j) h).trans_lt cap
      rw [exponent_y] at le
      change _ < W-d*j.1.val
      omega⟩
  refine ⟨v,?_⟩
  ext m
  by_cases hz : Q.coeff m=0
  · by_cases hi : ∃ j : Slots a b, exponent j=m
    · obtain ⟨j,rfl⟩ := hi
      rw [coeff_pack]
    · rw [coeff_pack_other v (fun j hj => hi ⟨j,hj⟩), hz]
  · obtain ⟨j,rfl⟩ := exponent_exhaustive (box (MvPolynomial.mem_support_iff.mpr hz))
    rw [coeff_pack]
#print axioms height_mul
#print axioms represented
end
end Lower6960.RetainedCompression

end Merged_R6960RetainedCompressionBox

-- merged module R6960RetainedCompressionRelations
section Merged_R6960RetainedCompressionRelations
set_option Elab.async false
set_option maxRecDepth 14000
set_option maxHeartbeats 2500000
namespace Lower6960.RetainedCompression
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators Polynomial Matrix
private def vectorPoly {A : Type*} [CommSemiring A] {a b : ℕ} (v : Slots a b→A) : Curve A :=
  ∑ m : Slots a b, MvPolynomial.monomial (exponent m) (v m)
private theorem coeff_vector {A : Type*} [CommSemiring A] {a b : ℕ}
    (v : Slots a b→A) (j : Slots a b) : (vectorPoly v).coeff (exponent j)=v j := by
  classical
  rw [vectorPoly,MvPolynomial.coeff_sum,Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
  · simp
  · intro k _ neq
    rw [MvPolynomial.coeff_monomial, if_neg (exponent_injective.ne neq)]
private theorem vector_box {A : Type*} [CommSemiring A] {a b : ℕ} (v : Slots a b→A) :
    vectorPoly v∈Box A a b := by
  classical
  change ∀ m∈(vectorPoly v).support,m∈Exponents a b
  intro m mem
  by_contra fit
  apply MvPolynomial.mem_support_iff.mp mem
  rw [vectorPoly,MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [MvPolynomial.coeff_monomial]
  apply if_neg
  intro eq
  apply fit
  rw [← eq]
  exact ⟨by simpa only [exponent_y] using Nat.le_of_lt_succ j.1.isLt,
    by simpa only [exponent_z] using Nat.le_of_lt_succ j.2.isLt⟩
private theorem vector_recover {A : Type*} [CommSemiring A] {a b : ℕ} (Q : Curve A)
    (fit : Q∈Box A a b) : vectorPoly (fun j : Slots a b => Q.coeff (exponent j))=Q := by
  classical
  ext m
  by_cases has : ∃ j : Slots a b, exponent j=m
  · obtain ⟨j,rfl⟩ := has
    exact coeff_vector _ j
  have zero (W : Curve A) (hW : W∈Box A a b) : W.coeff m=0 := by
    by_contra hn
    exact has (exponent_exhaustive (hW (MvPolynomial.mem_support_iff.mpr hn)))
  rw [zero _ (vector_box _), zero _ fit]
def evaluate {F : Type*} [Field F] (z : F) (S : (Polynomial F)) : Curve (Polynomial F) →+* (Polynomial F) :=
  MvPolynomial.eval (fun j : Index => j.elim S (fun _ => C z))
def markMatrix {F α : Type*} [Field F] (z : α→F) (S : α→(Polynomial F)) (a b : ℕ) :
    Matrix α (Slots a b) (Polynomial F) :=
  Matrix.of fun i j => S i ^ j.1.val * C (z i ^ j.2.val)
private theorem mark_degree {F α : Type*} [Field F]
    (z : α→F) (S : α→(Polynomial F)) (d a b : ℕ) (deg : ∀ i,(S i).natDegree≤d) :
    ∀ i j,(markMatrix z S a b i j).natDegree≤columnWeight d j := by
  intro i j
  have h := Polynomial.natDegree_mul_le
    (p:=S i ^ j.1.val) (q:=C (z i ^ j.2.val))
  rw [natDegree_C,add_zero] at h
  exact h.trans ((Polynomial.natDegree_pow_le_of_le _ (deg i)).trans_eq (Nat.mul_comm _ _))
private theorem eval_vector {A : Type*} [CommSemiring A] {a b : ℕ}
    (s z : A) (V : Slots a b→A) :
    MvPolynomial.eval (fun j : Index => j.elim s (fun _ => z)) (vectorPoly V) =
      ∑ j : Slots a b, (s^j.1.val*z^j.2.val)*V j := by
  classical
  rw [vectorPoly,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_option]
  simp only [Option.elim_none,Option.elim_some,exponent_y,Fintype.prod_unique,exponent_z]
  ac_rfl
private theorem eval_map_incl {F : Type*} [Field F] (z : F) (S : (Polynomial F)) (Q : Curve (Polynomial F)) :
    MvPolynomial.eval (fun j : Index => j.elim
        (algebraMap (Polynomial F) (FractionRing (Polynomial F)) S)
        (fun _ => algebraMap (Polynomial F) (FractionRing (Polynomial F)) (C z)))
      (MvPolynomial.map (algebraMap (Polynomial F) (FractionRing (Polynomial F))) Q) =
      algebraMap (Polynomial F) (FractionRing (Polynomial F)) (evaluate z S Q) := by
  let incl := algebraMap (Polynomial F) (FractionRing (Polynomial F))
  have ring : (MvPolynomial.eval (fun j : Index => j.elim (incl S) (fun _ => incl (C z)))).comp
      (MvPolynomial.map incl) = incl.comp (evaluate z S) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [evaluate]
    · intro i; cases i <;> simp [evaluate]
  exact DFunLike.congr_fun ring Q
theorem rational_kernel {F α : Type*} [Field F] [Finite α]
    (z : α→F) (S : α→(Polynomial F)) (f : Curve (Polynomial F)) (fn : f≠0) (e v : ℕ)
    (box : f∈Box (Polynomial F) e v) (marks : ∀ i,evaluate (z i) (S i) f=0) :
    Fintype.card (QuotRect e v)≤Module.finrank (FractionRing (Polynomial F))
      (LinearMap.ker ((markMatrix z S (boxOrdinate e) (paddedSeed v)).map
        (algebraMap (Polynomial F) (FractionRing (Polynomial F)))).mulVecLin) := by
  classical
  let E := FractionRing (Polynomial F)
  let j := algebraMap (Polynomial F) E
  let g := MvPolynomial.map j f
  let W := markMatrix z S (boxOrdinate e) (paddedSeed v)
  have gn : g≠0 := (map_ne_zero_iff _ (MvPolynomial.map_injective _ (IsFractionRing.injective (Polynomial F) E))).mpr fn
  have gbox : g∈Box E e v := by
    change ∀ m∈g.support,m∈Exponents e v
    have supp : g.support=f.support :=
      MvPolynomial.support_map_of_injective f (IsFractionRing.injective (Polynomial F) E)
    rw [supp]
    exact box
  let mulVec : (QuotRect e v→E) →ₗ[E] (Rect e v→E) := {
    toFun := fun u m => (g*vectorPoly u).coeff (exponent m)
    map_add' := fun u w => by
      funext m
      have add : vectorPoly (u+w)=vectorPoly u+vectorPoly w := by
        simp only [vectorPoly, Pi.add_apply, map_add, Finset.sum_add_distrib]
      change (g*vectorPoly (u+w)).coeff (exponent m)=_
      rw [add,mul_add,MvPolynomial.coeff_add]
      rfl
    map_smul' := fun a u => by
      funext m
      have smul : vectorPoly (a • u)=a • vectorPoly u := by
        simp only [vectorPoly,Pi.smul_apply,Finset.smul_sum,MvPolynomial.smul_monomial]
      change (g*vectorPoly (a • u)).coeff (exponent m)=_
      rw [smul,mul_smul_comm,MvPolynomial.coeff_smul]
      rfl }
  have recovered (u : QuotRect e v→E) : vectorPoly (mulVec u)=g*vectorPoly u := by
    apply vector_recover
    have h := (box_iff _ _ _).mp gbox
    have hs := (box_iff _ _ _).mp (vector_box u)
    apply (box_iff _ _ _).mpr
    refine ⟨(MvPolynomial.degreeOf_mul_le _ _ _).trans ?_,(MvPolynomial.degreeOf_mul_le _ _ _).trans ?_⟩
    · exact (Nat.add_le_add h.1 hs.1).trans (by unfold boxOrdinate; omega)
    · exact (Nat.add_le_add h.2 hs.2).trans (by unfold paddedSeed quotientSeed; omega)
  have kernel (u : QuotRect e v→E) : mulVec u∈LinearMap.ker (W.map j).mulVecLin := by
    rw [LinearMap.mem_ker]
    funext i
    have h := eval_vector (j (S i)) (j (C (z i))) (mulVec u)
    have eq : (W.map j).mulVecLin (mulVec u) i =
        MvPolynomial.eval (fun v : Index => v.elim (j (S i)) (fun _ => j (C (z i))))
          (vectorPoly (mulVec u)) := by
      rw [h]
      change (∑ m : Rect e v, j (W i m) * mulVec u m)=_
      simp only [W,markMatrix,Matrix.of_apply,map_mul,map_pow,C_pow]
    rw [eq,recovered,map_mul]
    change MvPolynomial.eval _ (MvPolynomial.map j f) * _ = 0
    rw [eval_map_incl,marks i,map_zero,zero_mul]
  have inject : Function.Injective (mulVec.codRestrict _ kernel) := by
    intro u w eq
    have eu : mulVec u=mulVec w := congrArg Subtype.val eq
    have ew := congrArg vectorPoly eu
    rw [recovered,recovered] at ew
    have V := mul_left_cancel₀ gn ew
    funext j
    exact (coeff_vector _ j).symm.trans ((congrArg (fun P : Curve E => P.coeff (exponent j)) V).trans (coeff_vector _ j))
  have dim := LinearMap.finrank_le_finrank_of_injective inject
  simpa only [Module.finrank_pi_fintype,Module.finrank_self,Finset.sum_const,card_univ,
    nsmul_eq_mul,mul_one,Nat.cast_id,W,j,E] using dim
private theorem eval_packed {F α : Type*} [Field F]
    (z : α→F) (S : α→(Polynomial F)) {a b d W : ℕ}
    (u : HeightCompression.Coeffs F (fun j : Slots a b => columnWeight d j) W) (i : α) :
    evaluate (z i) (S i) (packLinear F a b d W u) =
      HeightCompression.evaluation (markMatrix z S a b) (columnWeight d) W u i := by
  change evaluate (z i) (S i) (vectorPoly (fun j => (u j : (Polynomial F))))=_
  unfold evaluate
  rw [eval_vector]
  simp [HeightCompression.evaluation,markMatrix,C_pow]
theorem escape {F α : Type*} [Field F] [Finite α]
    (z : α→F) (S : α→(Polynomial F)) (d : ℕ) (hd : 0<d) (degree : ∀ i,(S i).natDegree≤d)
    (f : Curve (Polynomial F)) (fn : f≠0) {e v : ℕ} (he : 2≤e)
    (ed : f.degreeOf ordinate=e) (vd : f.degreeOf parameter=v)
    (marks : ∀ i,evaluate (z i) (S i) f=0) (hlarge : heightCap e d<height d f) :
    ∃ G : Curve (Polynomial F), G≠0 ∧ ¬ f∣G ∧ G∈Box (Polynomial F) (boxOrdinate e) (paddedSeed v) ∧
      height d G<width e d ∧ ∀ i,evaluate (z i) (S i) G=0 := by
  classical
  let A := markMatrix z S (boxOrdinate e) (paddedSeed v)
  let ker := LinearMap.ker (HeightCompression.evaluation A (columnWeight d) (width e d))
  let pack := packLinear F (boxOrdinate e) (paddedSeed v) d (width e d)
  let mult := (LinearMap.mulLeft F f).comp (packLinear F e (quotientSeed v) d (quotientWidth e d))
  have ker_size : Module.finrank F (HeightCompression.Coeffs F
      (fun j : QuotRect e v => columnWeight d j) (quotientWidth e d)) < Module.finrank F ker :=
    relation_space_gt he hd A (mark_degree z S d _ _ degree)
      (rational_kernel z S f fn e v ((box_iff _ _ _).mpr ⟨ed.le,vd.le⟩) marks)
  by_contra! h
  have all (u : ker) : f ∣ pack u.val := by
    by_cases zero : pack u.val=0
    · rw [zero]; exact dvd_zero f
    by_contra! bad
    obtain ⟨i,wrong⟩ := h (pack u.val) zero bad (pack_box u.val)
      (pack_height (by unfold width; omega) u.val)
    apply wrong
    change evaluate (z i) (S i) (packLinear F (boxOrdinate e) (paddedSeed v) d (width e d) u.val)=0
    rw [eval_packed]
    exact congrFun (LinearMap.mem_ker.mp u.property) i
  have fits (u : ker) : pack u.val∈LinearMap.range mult := by
    by_cases zero : pack u.val=0
    · exact zero ▸ Submodule.zero_mem _
    obtain ⟨Q,eq⟩ := all u
    have qn : Q≠0 := fun no => zero (by rw [eq,no,mul_zero])
    have dQ : Q∈Box (Polynomial F) e (quotientSeed v) := by
      have fit := (box_iff _ _ _).mp (pack_box u.val)
      change (pack u.val).degreeOf ordinate≤_ ∧ (pack u.val).degreeOf parameter≤_ at fit
      rw [eq,MvPolynomial.degreeOf_mul_eq fn qn,MvPolynomial.degreeOf_mul_eq fn qn,ed,vd] at fit
      apply (box_iff _ _ _).mpr
      unfold boxOrdinate paddedSeed quotientSeed at *
      omega
    have wQ : height d Q<quotientWidth e d := by
      have top := pack_height (by unfold width; omega) u.val
      change height d (pack u.val)<width e d at top
      rw [eq,height_mul d fn qn] at top
      unfold heightCap width quotientWidth at *
      have eq : (3*e-1)*d=(2*e-1)*d+e*d := by
        rw [show 3*e-1=(2*e-1)+e by omega, Nat.add_mul]
      omega
    obtain ⟨w,hw⟩ := represented Q dQ wQ
    refine ⟨w,?_⟩
    change f*(packLinear F e (quotientSeed v) d (quotientWidth e d) w)=_
    rw [hw,eq]
  let emb := (pack.comp ker.subtype).codRestrict _ fits
  have hn : Function.Injective emb := by
    intro u v eq
    apply Subtype.ext
    exact pack_injective _ _ _ _ (congrArg Subtype.val eq)
  have short := LinearMap.finrank_le_finrank_of_injective hn
  exact (not_lt_of_ge (short.trans mult.finrank_range_le)) ker_size
#print axioms rational_kernel
#print axioms escape
end
end Lower6960.RetainedCompression

end Merged_R6960RetainedCompressionRelations

-- merged module R6960RetainedCompressionCut
section Merged_R6960RetainedCompressionCut
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 2300000
namespace Lower6960.RetainedCompression
noncomputable section
open Polynomial Finset
open K1_14 (L)
open CurvatureSquares (Ordinate zView coeff_swap)
open scoped Polynomial
private def raw {A : Type*} [CommSemiring A] : Curve A ≃+* Polynomial (Polynomial A) :=
  (MvPolynomial.optionEquivLeft A PUnit).toRingEquiv.trans
    (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv A PUnit).toRingEquiv)
def view : Curve (Polynomial L) ≃+* Ordinate :=
  raw.trans (Polynomial.mapEquiv Bivariate.swap.toRingEquiv)
private theorem raw_y {A : Type*} [CommSemiring A] (Q : Curve A) :
    (raw Q).natDegree=Q.degreeOf ordinate := by
  change (((MvPolynomial.optionEquivLeft A PUnit Q).map
    (MvPolynomial.uniqueAlgEquiv A PUnit).toRingHom).natDegree)=_
  trans (MvPolynomial.optionEquivLeft A PUnit Q).natDegree
  · exact natDegree_map_eq_of_injective
      (f := (MvPolynomial.uniqueAlgEquiv A PUnit).toRingHom)
      (MvPolynomial.uniqueAlgEquiv A PUnit).injective _
  · exact MvPolynomial.natDegree_optionEquivLeft A Q
theorem view_y (Q : Curve (Polynomial L)) : (view Q).natDegree=Q.degreeOf ordinate := by
  change (((raw Q).map Bivariate.swap.toRingHom).natDegree)=_
  exact (natDegree_map_eq_of_injective (f:=Bivariate.swap.toRingHom)
    Bivariate.swap.injective _).trans (raw_y Q)
private theorem coeff_raw {A : Type*} [CommSemiring A] (Q : Curve A) (i j : ℕ) :
    ((raw Q).coeff i).coeff j =
      Q.coeff ((Finsupp.single (PUnit.unit : PUnit) j).optionElim i) := by
  change (((MvPolynomial.optionEquivLeft A PUnit Q).map
    (MvPolynomial.uniqueAlgEquiv A PUnit).toRingHom).coeff i).coeff j=_
  rw [coeff_map]
  change ((MvPolynomial.uniqueAlgEquiv A PUnit)
    ((MvPolynomial.optionEquivLeft A PUnit Q).coeff i)).coeff j = _
  rw [MvPolynomial.coeff_uniqueAlgEquiv,MvPolynomial.optionEquivLeft_coeff_coeff]
private theorem raw_seed {A : Type*} [CommSemiring A] (Q : Curve A) (i : ℕ) :
    ((raw Q).coeff i).natDegree≤Q.degreeOf parameter := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [coeff_raw]
  by_contra nz
  have deg := MvPolynomial.le_degreeOf_of_mem_support parameter (MvPolynomial.mem_support_iff.mpr nz)
  simp [parameter] at deg
  exact (not_lt_of_ge (show j ≤ Q.degreeOf parameter from deg)) hj
theorem view_z (Q : Curve (Polynomial L)) : (zView (view Q)).natDegree=Q.degreeOf parameter := by
  have swap_twice : (view Q).map Bivariate.swap.toRingHom=raw Q := by
    apply Polynomial.ext
    intro i
    change (((raw Q).map Bivariate.swap.toRingHom).map Bivariate.swap.toRingHom).coeff i=_
    rw [coeff_map,coeff_map]
    exact Bivariate.swap_swap_apply _
  change (Bivariate.swap ((view Q).map Bivariate.swap.toRingHom)).natDegree=_
  rw [swap_twice]
  apply le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    apply Polynomial.ext
    intro i
    rw [coeff_swap,coeff_zero]
    exact coeff_eq_zero_of_natDegree_lt ((raw_seed Q i).trans_lt hj)
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    let i := m ordinate
    let j := m parameter
    have same : (Finsupp.single (PUnit.unit : PUnit) j).optionElim i=m := by
      ext k
      cases k with
      | none => simp [i,ordinate]
      | some l => cases l; simp [j,parameter]
    have h := MvPolynomial.mem_support_iff.mp hm
    rw [← same, ← coeff_raw, ← coeff_swap] at h
    have term : ((Bivariate.swap (raw Q)).coeff j)≠0 := fun hzero => h (by rw [hzero,coeff_zero])
    exact Polynomial.le_natDegree_of_ne_zero term
theorem abscissa_coeff_height (Q : Curve (Polynomial L)) (d i : ℕ)
    (nz : (view Q).coeff i≠0) :
    ((view Q).coeff i).natDegree+d*i≤height d Q := by
  let n := ((view Q).coeff i).natDegree
  have nonzero : ((view Q).coeff i).coeff n≠0 := by
    change ((view Q).coeff i).leadingCoeff≠0
    exact leadingCoeff_ne_zero.mpr nz
  obtain ⟨j,hj⟩ := Polynomial.support_nonempty.mpr nonzero
  have term := Polynomial.mem_support_iff.mp hj
  change (((((raw Q).map Bivariate.swap.toRingHom).coeff i).coeff n).coeff j)≠0 at term
  rw [coeff_map] at term
  change ((Bivariate.swap ((raw Q).coeff i)).coeff n).coeff j≠0 at term
  rw [coeff_swap,coeff_raw] at term
  have cap := coeff_height d Q ((Finsupp.single (PUnit.unit : PUnit) j).optionElim i)
    (fun zero => term (by rw [zero,Polynomial.coeff_zero]))
  rw [Finsupp.optionElim_apply_none] at cap
  exact (Nat.add_le_add_right (Polynomial.le_natDegree_of_ne_zero term) _).trans cap
theorem abscissa_le_height (Q : Curve (Polynomial L)) (d : ℕ) :
    (CurvatureSquares.xView (view Q)).natDegree≤height d Q := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  ext i j
  change (((Bivariate.swap (view Q)).coeff n).coeff i).coeff j=0
  rw [coeff_swap]
  change ((((raw Q).map Bivariate.swap.toRingHom).coeff i).coeff n).coeff j=0
  rw [coeff_map]
  change ((Bivariate.swap ((raw Q).coeff i)).coeff n).coeff j=0
  rw [coeff_swap,coeff_raw]
  by_cases zero : Q.coeff ((Finsupp.single (PUnit.unit : PUnit) j).optionElim i)=0
  · simp [zero]
  apply coeff_eq_zero_of_natDegree_lt
  have h := coeff_height d Q _ zero
  omega
private theorem eval_raw {F : Type*} [Field F] (z : F) (S : (Polynomial F)) (Q : Curve (Polynomial F)) :
    evaluate z S Q=((raw Q).map (evalRingHom (C z))).eval S := by
  rw [evaluate,MvPolynomial.optionEquivLeft_elim_eval]
  change ((MvPolynomial.optionEquivLeft (Polynomial F) PUnit Q).map (MvPolynomial.eval (fun _=>C z))).eval S =
    ((((MvPolynomial.optionEquivLeft (Polynomial F) PUnit Q).map
      (MvPolynomial.uniqueAlgEquiv (Polynomial F) PUnit).toRingHom).map (evalRingHom (C z)))).eval S
  rw [Polynomial.map_map]
  congr 2
  apply RingHom.ext
  intro a
  change MvPolynomial.eval (fun _ : PUnit => C z) a =
    (((MvPolynomial.uniqueAlgEquiv (Polynomial F) PUnit) a : Polynomial (Polynomial F))).eval (C z)
  exact (MvPolynomial.eval₂_const_uniqueAlgEquiv (φ:=RingHom.id (Polynomial F)) (f:=a) (a:=C z)).symm
theorem evaluate_view (z : L) (S : (Polynomial L)) (Q : Curve (Polynomial L)) :
    evaluate z S Q=(specialize (view Q) z).eval S := by
  rw [eval_raw]
  apply congrArg (fun E : Polynomial (Polynomial L) => E.eval S)
  apply Polynomial.ext
  intro i
  change ((raw Q).map (evalRingHom (C z))).coeff i =
    (((raw Q).map Bivariate.swap.toRingHom).map (mapRingHom (evalRingHom z))).coeff i
  rw [coeff_map,coeff_map,coeff_map]
  have eq := eval_swap (Bivariate.swap ((raw Q).coeff i)) z
  rw [Bivariate.swap_swap_apply] at eq
  exact eq
private theorem resultant_ne_of_cut {R : Type*} [CommRing R] [IsDomain R] [IsGCDMonoid R]
    (P Q : (Polynomial R)) (ir : Irreducible P) (positive : 0<P.natDegree) (cut : ¬ P∣Q) :
    P.resultant Q≠0 := by
  let φ := algebraMap R (FractionRing R)
  have ph := ir.isPrimitive (ne_of_gt positive)
  have irr : Irreducible (P.map φ) := ph.irreducible_iff_irreducible_map_fraction_map.mp ir
  have cop : IsCoprime (P.map φ) (Q.map φ) :=
    irr.coprime_iff_not_dvd.mpr (fun dvd=> cut (ph.dvd_of_fraction_map_dvd_fraction_map dvd))
  have rn := Polynomial.resultant_ne_zero _ _ cop
  intro zero
  apply rn
  have injective := IsFractionRing.injective R (FractionRing R)
  rw [natDegree_map_eq_of_injective injective,natDegree_map_eq_of_injective injective,
    Polynomial.resultant_map_map,zero,map_zero]
theorem proper_cut_price {F : Type} [Field F] {ι : Type*} (T : Finset ι)
    (z : ι → F) (S : ι → Polynomial F) (inj : Set.InjOn z (T:Set ι))
    (f g : Curve (Polynomial F)) (ir : Irreducible f) (cut : ¬ f∣g) {e v : ℕ} (he : 0<e)
    (fy : f.degreeOf ordinate=e) (fz : f.degreeOf parameter=v)
    (gy : g.degreeOf ordinate≤2*e) (gz : g.degreeOf parameter≤10*v)
    (fmarks : ∀ i∈T,evaluate (z i) (S i) f=0)
    (gmarks : ∀ i∈T,evaluate (z i) (S i) g=0) :
    T.card≤12*e*v := by
  classical
  let P := raw f
  let Q := raw g
  have pd : P.natDegree=e := (raw_y f).trans fy
  have qd : Q.natDegree≤2*e := (raw_y g).trans_le gy
  have irr : Irreducible P := (MulEquiv.irreducible_iff (raw (A:=(Polynomial F)))).mpr ir
  have notdvd : ¬ P∣Q := by
    rintro ⟨a, h⟩
    apply cut
    refine ⟨(raw (A:=(Polynomial F))).symm a, (raw (A:=(Polynomial F))).injective ?_⟩
    rw [map_mul, RingEquiv.apply_symm_apply]
    exact h
  let R := P.resultant Q
  have rn : R≠0 := resultant_ne_of_cut P Q irr (by rw [pd]; exact he) notdvd
  have rdeg : R.natDegree≤12*e*v := by
    have hp i := (raw_seed f i).trans_eq fz
    have hq i := (raw_seed g i).trans gz
    have bound := natDegree_resultant_le_of_coeff_natDegree_le P Q P.natDegree Q.natDegree v (10*v) hp hq
    calc
      R.natDegree ≤ Q.natDegree*v+P.natDegree*(10*v) := bound
      _ ≤ (2*e)*v+e*(10*v) := Nat.add_le_add (Nat.mul_le_mul_right _ qd) (Nat.mul_le_mul_right _ pd.le)
      _ = _ := by ring
  have sn : Bivariate.swap R≠0 := (map_ne_zero_iff _ Bivariate.swap.injective).mpr rn
  let coeff := (Bivariate.swap R).leadingCoeff
  have cn : coeff≠0 := leadingCoeff_ne_zero.mpr sn
  have cdeg : coeff.natDegree≤R.natDegree := by
    have h := CurvatureSquares.coeff_height (Bivariate.swap R) (Bivariate.swap R).natDegree
    simpa only [CurvatureSquares.height,Bivariate.swap_swap_apply,coeff_natDegree] using h
  have roots : T.image z ⊆ coeff.roots.toFinset := by
    intro u hu
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hu
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots cn).mpr
    have atRoot := Polynomial.map_resultant_eq_zero_of_common_root
      (evalRingHom (C (z i))) P Q (m:=P.natDegree) (n:=Q.natDegree) le_rfl le_rfl
      (Or.inl (by omega)) (S i) ((eval_raw (z i) (S i) f).symm.trans (fmarks i hi))
      ((eval_raw (z i) (S i) g).symm.trans (gmarks i hi))
    change R.eval (C (z i))=0 at atRoot
    have swapped : (Bivariate.swap R).map (evalRingHom (z i))=0 := by
      have e := eval_swap (Bivariate.swap R) (z i)
      rw [Bivariate.swap_swap_apply,atRoot] at e
      exact e.symm
    have killed := congrArg (fun A : (Polynomial F) => A.coeff (Bivariate.swap R).natDegree) swapped
    simpa only [Polynomial.IsRoot,coeff_map,coeff_natDegree,coeff_zero,coe_evalRingHom] using killed
  rw [← card_image_of_injOn inj]
  exact (card_le_card roots).trans ((Multiset.toFinset_card_le ..).trans
    ((Polynomial.card_roots' coeff).trans (cdeg.trans rdeg)))
#print axioms view_z
#print axioms proper_cut_price
end
end Lower6960.RetainedCompression

end Merged_R6960RetainedCompressionCut

-- merged module R6960RetainedCompressionReduction
section Merged_R6960RetainedCompressionReduction
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 2500000
namespace Lower6960.RetainedCompression
noncomputable section
open Polynomial Finset
open K1 (K p)
open K1_14 (L liftPoly)
open RescueGeometry (Model Family)
open RetainedShortening (Word)
open CurvatureSquares (Ordinate ordEval xView zView)
open scoped Polynomial
open CurvatureSquares (degree_two_count)
abbrev wordDegree : ℕ := 164650
def FactorPriceAt (rate:ℕ→ℕ) : Prop :=
  ∀ {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ) (T : Finset K), T⊆Γ →
    Word 179818 wordDegree M.word F.scalar T →
    ∀ f : Curve (Polynomial L), Irreducible f →
      3≤f.degreeOf ordinate → f.degreeOf ordinate<48 → 0<f.degreeOf parameter →
      height wordDegree f≤heightCap (f.degreeOf ordinate) wordDegree →
      (∀ γ∈T, MarkedFiber (view f) (scalar M γ) (liftPoly (F.scalar γ))) →
      T.card≤rate (f.degreeOf ordinate)*(f.degreeOf parameter)+
        (f.degreeOf ordinate-1)*(f.degreeOf ordinate)
abbrev BoundedFactorPrice := FactorPriceAt MarkedSheet.rate
theorem rate_mono {e n : ℕ} (h : e≤n) : MarkedSheet.rate e≤MarkedSheet.rate n := by
  unfold MarkedSheet.rate
  exact Nat.sub_le_sub_right (Nat.add_le_add
    (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul_left 9 h) 6)
      (Nat.sub_le_sub_right h 1))
    (Nat.mul_le_mul_left 2 h)) 1
private theorem vote_scale : CurvatureVotes.VoteScale 179818 wordDegree 18 :=
  Or.inl (by decide +kernel)
private theorem word_roots {u deleted} {M : Model u deleted} {Γ U : Finset K} (F : Family M Γ)
    (Q : Ordinate) (H : ∀ γ∈U, MarkedFiber Q (scalar M γ) (liftPoly (F.scalar γ))) :
    ∀ γ∈U, ordEval (scalar M γ) ((F.scalar γ).map (algebraMap K L)) Q=0 := by
  intro γ hγ
  change Q.eval₂ (mapRingHom (evalRingHom (scalar M γ))) (liftPoly (F.scalar γ))=0
  rw [← eval_map]
  exact (H γ hγ).root
private theorem factor_price (rate:ℕ→ℕ) (mono:Monotone rate) (small:24≤rate 3)
    (proper:∀e,3≤e→e<48→12*e≤rate e) (bounded : FactorPriceAt rate)
    {u deleted} {M : Model u deleted} {Γ U : Finset K} (F : Family M Γ) (sub : U⊆Γ)
    (words : Word 179818 wordDegree M.word F.scalar U)
    {Q : Ordinate} (ir : Irreducible Q) (n : ℕ) (lo : 3≤n) (hi : n<48)
    (degree : Q.natDegree≤n) (mark : ∀ γ∈U, MarkedFiber Q (scalar M γ) (liftPoly (F.scalar γ))) :
    U.card≤rate n*(zView Q).natDegree+(n-1)*Q.natDegree := by
  classical
  rcases U.eq_empty_or_nonempty with empty | ⟨γ,hγ⟩
  · simp [empty]
  let q := view.symm Q
  let e := Q.natDegree
  let v := (zView Q).natDegree
  have qp : Irreducible q := (MulEquiv.irreducible_iff view.symm).mpr ir
  have y : q.degreeOf ordinate=e := by rw [← view_y, RingEquiv.apply_symm_apply]
  have z : q.degreeOf parameter=v := by rw [← view_z, RingEquiv.apply_symm_apply]
  have pos : 0<e := no_zero_degree (mark γ hγ)
  have tRate : 24≤rate n := small.trans (mono lo)
  have vRate : 18≤rate n := (by decide : 18≤24).trans tRate
  have budget : e≤(n-1)*e := Nat.le_mul_of_pos_left _ (by omega)
  have inj : Set.InjOn (scalar M) (U : Set K) := (scalar_injective M).injOn
  by_cases hv : v=0
  · have Sinj : Set.InjOn (fun x=>liftPoly (F.scalar x)) (U:Set K) :=
      (Polynomial.map_injective _ (algebraMap K L).injective).comp_injOn words.distinct
    exact (constant_price Q U (scalar M) (fun x=>liftPoly (F.scalar x)) Sinj hv mark).trans
      (budget.trans (Nat.le_add_left ..))
  have roots := word_roots F Q mark
  by_cases linear : e=1
  · have count := CurvatureSquares.irreducible_linear_node words (algebraMap K L) (scalar M) inj
      (by decide) vote_scale Q ir linear roots
    exact count.trans (Nat.add_le_add (Nat.mul_le_mul_right _ vRate) (pos.trans_le budget))
  have el : 2≤e := by omega
  by_cases tall : heightCap e wordDegree < height wordDegree q
  · let parameter (j : U) := scalar M j.val
    let root (j : U) := liftPoly (F.scalar j.val)
    have d (j : U) : (root j).natDegree≤wordDegree := by
      simpa only [root,liftPoly,natDegree_map_eq_of_injective (algebraMap K L).injective]
        using words.degree j.val j.property
    have rootsF (j : U) : evaluate (parameter j) (root j) q=0 := by
      rw [evaluate_view,RingEquiv.apply_symm_apply]
      exact (mark j.val j.property).root
    obtain ⟨G,_,nondiv,box,_,rootsG⟩ :=
      escape parameter root wordDegree (by decide) d q qp.ne_zero el y z rootsF tall
    have ⟨gy,gz⟩ := (box_iff _ _ _).mp box
    have price := proper_cut_price U (scalar M) (fun w=>liftPoly (F.scalar w))
      inj q G qp nondiv pos y z gy gz (fun γ hγ=>rootsF ⟨γ,hγ⟩)
      (fun γ hγ=>rootsG ⟨γ,hγ⟩)
    have ceiling : 12*e≤rate n := by
      by_cases two : e=2
      · simpa only [two] using tRate
      have three : 3≤e := by omega
      exact (proper e three (degree.trans_lt hi)).trans (mono degree)
    exact (price.trans (Nat.mul_le_mul_right _ ceiling)).trans (Nat.le_add_right ..)
  · have wt := Nat.le_of_not_gt tall
    by_cases two : e=2
    · have D : 2*(xView Q).natDegree<p := by
        have a := abscissa_le_height q wordDegree
        rw [RingEquiv.apply_symm_apply] at a
        exact (Nat.mul_le_mul_left 2 (a.trans wt)).trans_lt (by rw [two]; decide)
      have count := degree_two_count words (algebraMap K L) (scalar M) inj
        (by decide) vote_scale Q ir two D roots
      have add : 2≤(n-1)*e := el.trans budget
      exact count.trans (Nat.add_le_add
        (Nat.mul_le_mul_right _ (show max 8 18≤rate n from vRate)) add)
    have three : 3≤q.degreeOf ordinate := by rw [y]; omega
    have charge := bounded F U sub words q qp three (y.symm ▸ degree.trans_lt hi)
      (Nat.pos_of_ne_zero (z.symm ▸ hv)) (y.symm ▸ wt)
      (fun γ hγ => by simpa only [q,RingEquiv.apply_symm_apply] using mark γ hγ)
    rw [y,z] at charge
    exact charge.trans (Nat.add_le_add (Nat.mul_le_mul_right _ (mono degree))
      (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right degree 1)))
theorem retained_of_tariff (rate:ℕ→ℕ) (mono:Monotone rate) (small:24≤rate 3)
    (proper:∀e,3≤e→e<48→12*e≤rate e)
    (paid:∀e a b,3≤e→e<48→a+b≤2400→b<(TerminalReceipts.witness e).order 1→
      rate e*(a+p*b)+(e-1)*e≤retainedCap) (bounded : FactorPriceAt rate) : RetainedCount := by
  intro u deleted M Γ F lo hi D Crt regular residues T f sub emin emax axes graded marks
  obtain ⟨W,P,pn,deg,seed,fibre⟩ :=
    marked_projection F f sub emin axes hi (fun γ hγ => (marks γ hγ).1)
  have pmin : 3≤P.natDegree := deg.symm ▸ emin
  have pmax : P.natDegree<48 := deg.symm ▸ emax
  have count := aggregate P T (scalar M) (fun γ=>liftPoly (F.scalar γ))
    (rate P.natDegree) (P.natDegree-1) pn fibre (by
      intro Q ir dvd U us qmark
      have words : Word 179818 wordDegree M.word F.scalar U :=
        ⟨W.distinct.mono us,fun γ hγ=>W.degree γ (us hγ),fun γ hγ=>W.hits γ (us hγ)⟩
      exact factor_price rate mono small proper bounded F (us.trans sub) words ir _ pmin pmax
        (natDegree_le_of_dvd dvd pn) qmark)
  rw [deg] at count
  have priced := Nat.add_le_add_right (Nat.mul_le_mul_left (rate f.natDegree) seed)
    ((f.natDegree-1)*f.natDegree)
  exact count.trans (priced.trans (paid f.natDegree _ _ emin emax axes (graded 1)))
theorem retained_of_bounded (bounded : BoundedFactorPrice) : RetainedCount :=
  retained_of_tariff MarkedSheet.rate (fun _ _ h=>rate_mono h) (by decide)
    (fun e h hi=>(MarkedSheet.endpoint.2.1 ⟨e,hi⟩ h).1) graded_budget bounded
#print axioms factor_price
#print axioms retained_of_bounded
end
end Lower6960.RetainedCompression

end Merged_R6960RetainedCompressionReduction

-- merged module R6960RetainedCompressionPureNodes
section Merged_R6960RetainedCompressionPureNodes
set_option Elab.async false
set_option maxRecDepth 14000
set_option maxHeartbeats 2000000
namespace Lower6960.RetainedCompression
noncomputable section
open Polynomial Finset
open K1 (K I node)
open K1_14 (L liftPoly)
open CurvatureSquares (Ordinate zView coeff_caps)
open RetainedShortening (Word)
open RescueGeometry (Model Family)
open scoped Polynomial
open Lower6960.RetainedCompression (rate_mono)
open CurvatureSquares (node_eval node_height node_ne root_count)
private abbrev embed := algebraMap K L
def atNode (P : Ordinate) (i : I) : Polynomial (Polynomial L) :=
  P.map (evalRingHom (C (embed (node i))))
def PureNodes (w : I → K) (P : Ordinate) : Prop :=
  ∀ i, (atNode P i).eval (C (embed (w i))) = 0 →
    atNode P i = C (atNode P i).leadingCoeff * (Polynomial.X-C (C (embed (w i))))^P.natDegree
private theorem node_coefficient (P : Ordinate) (i : I) (j : ℕ) :
    ((atNode P i).coeff j).natDegree≤(zView P).natDegree := by
  rw [atNode,coeff_map,coe_evalRingHom]
  exact (CurvatureSquares.node_height ..).trans (coeff_caps P j).2
private theorem root_at_node {P : Ordinate} {z : L} {S : (Polynomial K)}
    (mark : MarkedFiber P z (liftPoly S)) (i : I) :
    ((atNode P i).map (evalRingHom z)).eval (embed (S.eval (node i)))=0 := by
  let x := embed (node i)
  have commute : (specialize P z).map (evalRingHom x)=(atNode P i).map (evalRingHom z) := by
    apply Polynomial.ext
    intro n
    simp only [specialize,atNode,x,coeff_map,coe_mapRingHom,coe_evalRingHom]
    exact (CurvatureSquares.node_eval (P.coeff n) (embed (node i)) z).symm
  have value : (liftPoly S).eval x=embed (S.eval (node i)) := by
    rw [liftPoly,show x=embed (node i) from rfl,Polynomial.eval_map_apply]
  have h := congrArg (Polynomial.eval x) mark.root
  have eq := Polynomial.eval_map_apply (f:=evalRingHom x)
    (p:=specialize P z) (x:=liftPoly S)
  rw [commute,coe_evalRingHom,value] at eq
  exact eq.trans (h.trans eval_zero)
theorem pure_node_price {w s T} (W : Word 179818 wordDegree w s T)
    (z : K → L) (inj : Set.InjOn z (T:Set K)) (P : Ordinate) (irr : Irreducible P)
    (pos : 0<P.natDegree) (pure : PureNodes w P)
    (marks : ∀ γ∈T, MarkedFiber P (z γ) (liftPoly (s γ))) :
    T.card≤18*(zView P).natDegree+1 := by
  classical
  apply CurvatureVotes.minority_count W (by decide) (Or.inl (by decide))
  intro i
  let Q := atNode P i
  let a := Q.leadingCoeff
  let g := Q.eval (C (embed (w i)))
  have cn (j : ℕ) : (Q.coeff j).natDegree≤(zView P).natDegree := node_coefficient P i j
  have fits : g.natDegree≤(zView P).natDegree := by
    dsimp only [g]
    rw [eval_eq_sum,Polynomial.sum_def]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    rw [← C_pow]
    exact (natDegree_mul_C_le ..).trans (cn j)
  by_cases nonzero : g≠0
  · left
    apply (CurvatureSquares.root_count (inj.mono (filter_subset _ _)) g nonzero _).trans fits
    intro γ hγ
    obtain ⟨active,hit⟩ := mem_filter.mp hγ
    have hz := root_at_node (marks γ active) i
    have eq := Polynomial.eval_map_apply (f:=evalRingHom (z γ))
      (p:=Q) (x:=C (embed (w i)))
    rw [coe_evalRingHom,eval_C] at eq
    rw [hit] at hz
    exact eq.symm.trans hz
  · right
    have qn : Q≠0 := CurvatureSquares.node_ne P irr pos _
    have an : a≠0 := leadingCoeff_ne_zero.mpr qn
    apply (CurvatureSquares.root_count (inj.mono (filter_subset _ _)) a an _).trans
      (by simpa only [a,coeff_natDegree] using cn Q.natDegree)
    intro γ hγ
    obtain ⟨active,miss⟩ := mem_filter.mp hγ
    have hz := root_at_node (marks γ active) i
    have packed := pure i (not_ne_iff.mp nonzero)
    change Q=C a*(Polynomial.X-C (C (embed (w i))))^P.natDegree at packed
    change (Q.map (evalRingHom (z γ))).eval (embed ((s γ).eval (node i)))=0 at hz
    rw [packed,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_sub,
      Polynomial.map_X,Polynomial.map_C,eval_mul,eval_pow,eval_sub,eval_X,eval_C,
      eval_C,coe_evalRingHom,eval_C] at hz
    exact (mul_eq_zero.mp hz).resolve_right (pow_ne_zero _ (sub_ne_zero.mpr (embed.injective.ne miss)))
def NonPureFactorPrice : Prop :=
  ∀ {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ) (T : Finset K), T⊆Γ →
    Word 179818 wordDegree M.word F.scalar T →
    ∀ f : Curve (Polynomial L), Irreducible f →
      3≤f.degreeOf ordinate → f.degreeOf ordinate<48 → 0<f.degreeOf parameter →
      height wordDegree f≤heightCap (f.degreeOf ordinate) wordDegree →
      ¬PureNodes M.word (view f) →
      (∀ γ∈T, MarkedFiber (view f) (scalar M γ) (liftPoly (F.scalar γ))) →
      T.card≤MarkedSheet.rate (f.degreeOf ordinate)*(f.degreeOf parameter)+
        (f.degreeOf ordinate-1)*(f.degreeOf ordinate)
theorem bounded_of_nonpure (other : NonPureFactorPrice) : BoundedFactorPrice := by
  intro u deleted M Γ F T sub W f irr lo hi sv cap marks
  by_cases pure : PureNodes M.word (view f)
  · let P := view f
    have ir : Irreducible P := (MulEquiv.irreducible_iff view).mpr irr
    have positive : 0<P.natDegree := by change 0<(view f).natDegree; rw [view_y]; omega
    have fee := pure_node_price W (scalar M) (scalar_injective M).injOn P ir positive pure marks
    change _≤18*(zView (view f)).natDegree+1 at fee
    rw [view_z] at fee
    have rate : 18≤MarkedSheet.rate (f.degreeOf ordinate) := (by decide :
      18≤MarkedSheet.rate 3).trans (rate_mono lo)
    have additive : 1≤(f.degreeOf ordinate-1)*(f.degreeOf ordinate) :=
      Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
    exact fee.trans (Nat.add_le_add (Nat.mul_le_mul_right _ rate) additive)
  · exact other F T sub W f irr lo hi sv cap pure marks
theorem retained_of_nonpure (other : NonPureFactorPrice) : RetainedCount :=
  retained_of_bounded (bounded_of_nonpure other)
#print axioms pure_node_price
#print axioms retained_of_nonpure
end
end Lower6960.RetainedCompression

end Merged_R6960RetainedCompressionPureNodes

end Merged6967_R6960RetainedCompressionPureNodes

section Merged6967_R6966ProofHelperAvoidance
set_option Elab.async false



set_option Elab.async false

-- merged module R6966ProofRectangularHelperShift
section Merged_R6966ProofRectangularHelperShift

namespace Research6966.RectangularHelperShift
open Polynomial Finset Module
open K1_14 (FX L Jet Shape seedHasse)
open K1_14_1 (SeedPoly PoleData CRTLift centerEval)
open K1_14_1_3 (seedCoeff translation sourceHasse mapCoeffs_coeff cleared sourceX evaluatedHasse evaluatedHasse_eq centerEval_clear)
open KoalaRect (rectComplete rectEvaluated rectShaped)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

theorem seed_axis (i z:Fin 2) (r:ℕ) (P:SeedPoly) : (seedCoeff i r P).degreeOf z≤P.degreeOf z := by
  classical
  let w:Fin 2→ℕ:=Pi.single z 1
  let w':Option (Fin 2)→ℕ:=fun j=>j.elim 0 w
  let g (j:Fin 2):MvPolynomial (Option (Fin 2)) L:=
    MvPolynomial.X (some j)+if j=i then MvPolynomial.X none else 0
  have scalar (Q:SeedPoly) : Q∈MvPolynomial.restrictWeightAtMost w (Q.degreeOf z) := by
    apply MvPolynomial.mem_restrictWeightAtMost.mpr
    intro e he;rw [show e.weight w=e z from Finsupp.weight_single_one_apply _ _]
    exact MvPolynomial.le_degreeOf_of_mem_support z he
  have subst:=MvPolynomial.bind₁_mem_restrictWeightAtMost (w:=w) (v:=w') (f:=g) (by
    intro j
    apply Submodule.add_mem
    · exact MvPolynomial.X_mem_restrictWeightAtMost w' _ le_rfl
    · by_cases yes:j=i
      · rw [ite_eq_left yes];exact MvPolynomial.X_mem_restrictWeightAtMost w' _ (Nat.zero_le _)
      · rw [ite_eq_right yes];exact Submodule.zero_mem _) (scalar P)
  have eq:translation (R:=L) i=(MvPolynomial.optionEquivLeft L (Fin 2)).toAlgHom.comp (MvPolynomial.bind₁ g) := by
    apply MvPolynomial.algHom_ext
    intro j;by_cases yes:j=i <;> simp [translation,g,yes]
  change ((translation i P).coeff r).degreeOf z≤_
  rw [eq]
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro e he
  have h:=MvPolynomial.mem_restrictWeightAtMost.mp subst (e.optionElim r)
    ((MvPolynomial.mem_support_coeff_optionEquivLeft L).mp he)
  change (e.optionElim r).weight (fun j=>j.elim 0 w)≤_ at h
  simpa [Finsupp.weight_optionElim,w,Finsupp.weight_single_one_apply] using h

theorem cleared_rect {h:ℕ} (D:PoleData h) (i:Fin 2) (r:ℕ) {Q:K1_14_1.Source}
    {U:Fin 2→ℕ} (fits:rectShaped U Q) : rectShaped U (cleared D i r Q) := by
  classical
  intro j k a e nz z
  by_contra above
  apply nz
  change K1_14_1.coeffAt (cleared D i r Q) j k a e=0
  simp only [cleared,K1_14_1.coeffAt,K1_14_1.jetConstant,RingHom.comp_apply]
  rw [coeff_C_mul,coeff_C_mul,coeff_mul,MvPolynomial.coeff_sum]
  simp only [sourceX,coeff_map,MvPolynomial.coeff_C_mul,sourceHasse,mapCoeffs_coeff]
  apply sum_eq_zero
  rintro ⟨b,c⟩ _
  let A:=((Q.coeff j).coeff k).coeff c
  change _*(seedCoeff i r A).coeff e=0
  by_contra live
  have cap:A.degreeOf z≤U z:=MvPolynomial.degreeOf_le_iff.mpr
    (fun d hd=>fits j k c d (MvPolynomial.mem_support_iff.mp hd) z)
  have on:=MvPolynomial.le_degreeOf_of_mem_support z (MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul live))
  exact above (on.trans ((seed_axis i z r A).trans cap))

theorem shifted {h} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L) {s:Shape} {W:ℕ} {U:Fin 2→ℕ} {P:Jet}
    (mem:P∈rectEvaluated Crt word s W U) (i:Fin 2) (r:ℕ) :
    seedHasse i r P∈rectEvaluated Crt word s (W+2*h*r) U := by
  let target:=rectEvaluated Crt word s (W+2*h*r) U
  have sub:rectEvaluated Crt word s W U ≤ target.comap (evaluatedHasse i r) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨Q,q,rfl⟩
    have m:cleared D i r Q∈rectComplete Crt word s (W+2*h*r) U :=
      ⟨⟨⟨K1_14_1_3.ambient_cleared D q.1.1.1 i r,K1_14_1_3_1.proof h D word s Q q.1.1.2 i r⟩,
        K1_14_1_3_2.proof h D Crt s Q q.1.2 i r⟩,cleared_rect D i r q.2⟩
    have he:centerEval (cleared D i r Q)∈target:=Submodule.subset_span ⟨_,m,rfl⟩
    rw [centerEval_clear] at he
    have nc:algebraMap L[X] FX ((D.block i)^(2*r))≠0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective L[X] FX)).mpr (pow_ne_zero _ (D.monic i).ne_zero)
    exact (target.smul_mem_iff nc).mp he
  rw [←evaluatedHasse_eq]
  exact sub mem

theorem mono {h} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L) (s:Shape) (U:Fin 2→ℕ)
    {W V:ℕ} (le:W≤V) :rectEvaluated Crt word s W U ≤rectEvaluated Crt word s V U :=
  Submodule.span_mono (Set.image_mono (show rectComplete Crt word s W U≤rectComplete Crt word s V U from
    inf_le_inf_right _ (K1_14_1.complete_mono Crt word rfl rfl rfl le_rfl le)))

theorem all_axes {h} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L) (s:Shape) (W:ℕ) :
    rectEvaluated Crt word s W (fun _=>s.U)=K1_14_1.evaluated Crt word s W := by
  apply le_antisymm (KoalaRect.rectEvaluated_le ..)
  apply Submodule.span_le.mpr
  rintro _ ⟨P,hP,rfl⟩
  apply Submodule.subset_span
  refine ⟨P,⟨hP,?_⟩,rfl⟩
  intro j i a e nz z
  have eligible:K1_14_1.trueEligible h s W j i a e:=by by_contra no;exact nz (hP.1.1 j i a e no)
  have sz:=eligible.2.2.1
  rw [K1_14_1_5.seedWeight_eq] at sz
  change e z≤s.U
  fin_cases z
  · exact (Nat.le_add_right (e 0) (e 1)).trans sz
  · exact (Nat.le_add_left (e 1) (e 0)).trans sz

/-- Absence of an avoiding row at one rectangular cutoff forces the
same seed-dependent prime to the full layer power at every earlier cutoff. -/
theorem common_power {h W top:ℕ} (hp:0<h) (lt:W<top) {D:PoleData h} (Crt:CRTLift D)
    (word:K1.I→L) (s:Shape) (U:Fin 2→ℕ) {G:Jet} (irr:Irreducible G) (slope:0<G.natDegree)
    (uses:K1_14_2.UsesSeed G) (small:s.U<K1.p)
    (common:∀ Q∈rectEvaluated Crt word s (top-1) U,G∣Q) :
    ∀ P∈rectComplete Crt word s W U,G^(1+(top-1-W)/(2*h))∣centerEval P := by
  intro P mem
  have row:centerEval P∈rectEvaluated Crt word s W U:=Submodule.subset_span ⟨P,mem,rfl⟩
  by_cases zero:centerEval P=0
  · rw [zero];exact dvd_zero _
  apply Lower6960.PowerLayers.forced_power hp lt irr slope uses zero
    (common _ (mono Crt word s U (by omega) row)) small
  · intro j i
    by_cases z:((centerEval P).coeff j).coeff i=0
    · simp [z]
    · exact (K1_14_1.evaluated_shape Crt word (KoalaRect.rectEvaluated_le Crt word s W U row) j i z).2.2
  · intro i r cap
    exact common _ (mono Crt word s U cap (shifted Crt word row i r))

#print axioms common_power
end
end Research6966.RectangularHelperShift

end Merged_R6966ProofRectangularHelperShift

-- merged module R6966ProofHelperAvoidance
section Merged_R6966ProofHelperAvoidance

namespace Research6966.HelperAvoidance
open Polynomial Finset Module
open K1_14 (Shape FX L Jet shapeSum triangle)
open K1_14_1 (CRTLift PoleData centerEval)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open KoalaRect (area rectEvaluated rectComplete rectDebit)
open HelperBankRank (cells)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

def power (N h W:ℕ):=1+(N-1-W)/(2*h)

def rectSlots (U widths:Fin 2→ℕ) (k:ℕ):ℕ :=
  if ∀z,k*widths z≤U z then area (fun z=>U z-k*widths z) else 0

def triSlots (U width k:ℕ):ℕ := if k*width≤U then triangle (U-k*width) else 0

def debitAt (s:Shape) (h N W a b L:ℕ) (slots:ℕ→ℕ):ℕ :=
  let t:=power N h W
  (cells s h W t a b L).card*slots t

private theorem cells_mono (s:Shape) (h W k:ℕ) {a A b B L L':ℕ} (aa:a≤A) (bb:b≤B) (ll:L≤L') :
    cells s h W k A B L' ⊆cells s h W k a b L := by
  intro t ht
  have ax:=Nat.mul_le_mul_left k aa
  have bx:=Nat.mul_le_mul_left k bb
  have lx:=Nat.mul_le_mul_left k ll
  unfold cells at ht ⊢
  split at ht
  · rename_i room
    rw [ite_eq_left (by omega)]
    obtain ⟨pos,weight⟩:=mem_filter.mp ht
    apply mem_filter.mpr
    constructor
    · simp [PadeRank.positions] at pos ⊢;omega
    · exact weight.trans (Nat.sub_le_sub_left lx W)
  · simp at ht

private theorem rect_mono (U:Fin 2→ℕ) {a b:Fin 2→ℕ} (axis:∀ z,a z≤b z) (k:ℕ) :
    rectSlots U b k≤rectSlots U a k := by
  unfold rectSlots
  split
  · rename_i room
    rw [ite_eq_left (fun z=>(Nat.mul_le_mul_left k (axis z)).trans (room z))]
    exact Nat.mul_le_mul (Nat.succ_le_succ (Nat.sub_le_sub_left (Nat.mul_le_mul_left k (axis 0)) _))
      (Nat.succ_le_succ (Nat.sub_le_sub_left (Nat.mul_le_mul_left k (axis 1)) _))
  · exact Nat.zero_le _

private theorem tri_mono (U:ℕ) {a b:ℕ} (le:a≤b) (k:ℕ) : triSlots U b k≤triSlots U a k := by
  have less:=Nat.mul_le_mul_left k le
  unfold triSlots
  split
  · rename_i room
    rw [ite_eq_left (less.trans room)]
    unfold triangle
    apply Nat.div_le_div_right
    exact Nat.mul_le_mul (by omega) (by omega)
  · exact Nat.zero_le _

private theorem width {h N:ℕ} {s:Shape} (nz:0<N) (wide:s.B*(131071-h)≤N) :
    K1_14_1.rawWidthCond h s (N-1) := by
  intro q hq j _
  rw [Nat.sub_add_cancel nz]
  exact (Nat.mul_le_mul_right _ hq).trans (wide.trans (Nat.le_add_right N j))

theorem rect_contradiction {h N:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) (s:Shape) (U widths:Fin 2→ℕ) {F:Jet}
    (M:HelperPhysicalModel.Model Crt F) (fn:F≠0) {a b L0 nodes moment:ℕ}
    (aCap:a≤jetDegree F) (bCap:b≤F.natDegree) (lCap:L0≤RawPhysicalDegree.weight (131071-h) (131071-h-1) M.raw)
    (axes:∀ z,widths z≤PadeNativeQuotient.axis F z) (box:U 0+U 1≤s.U) (small:s.B<K1.p)
    (nz:0<N) (wide:s.B*(131071-h)≤N) (num:P1_7_1.nodeRows s≤nodes)
    (pole:P1_7_1.groupedPoleMoment s.B s.J≤moment)
    (positive:rectDebit h nodes moment U + ∑ W∈range N,debitAt s h N W a b L0 (rectSlots U widths) <
      area U*shapeSum s (fun q j=>N+j-q*(131071-h)))
    (force:∀ W<N,∀ P∈rectComplete Crt word s W U,F^(power N h W)∣centerEval P) : False := by
  have floor:=KoalaRect.rectRankFloor hp hl (hl.trans_lt (by decide)) Crt word s (N-1) U box small
    (width nz wide) num pole
  rw [Nat.sub_add_cancel nz] at floor
  have cost (W:ℕ) (hw:W∈range N) : finrank FX (rectEvaluated Crt word s W U)≤debitAt s h N W a b L0 (rectSlots U widths) := by
    have rank:=(HelperBankRank.bank_rank hp hl Crt word s U M fn (force W (mem_range.mp hw))).1
    exact rank.trans (Nat.mul_le_mul (card_le_card (cells_mono s h W _ aCap bCap lCap)) (rect_mono U axes _))
  exact (Nat.not_lt_of_ge (floor.trans (Nat.add_le_add_left (sum_le_sum cost) _))) positive

/-- A positive physical rectangle supplies an avoiding row in that exact
rectangle, with no assumptions on its seed derivatives. -/
theorem rect_avoiding {h N:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) (s:Shape) (U widths:Fin 2→ℕ) {F:Jet}
    (M:HelperPhysicalModel.Model Crt F) (prime:Irreducible F) (slope:0<F.natDegree)
    (seeded:K1_14_2.UsesSeed F) (char:s.U<K1.p) {a b L0 nodes moment:ℕ}
    (aCap:a≤jetDegree F) (bCap:b≤F.natDegree) (lCap:L0≤RawPhysicalDegree.weight (131071-h) (131071-h-1) M.raw)
    (axes:∀ z,widths z≤PadeNativeQuotient.axis F z) (box:U 0+U 1≤s.U) (small:s.B<K1.p)
    (nz:0<N) (wide:s.B*(131071-h)≤N) (num:P1_7_1.nodeRows s≤nodes)
    (pole:P1_7_1.groupedPoleMoment s.B s.J≤moment)
    (positive:rectDebit h nodes moment U + ∑ W∈range N,debitAt s h N W a b L0 (rectSlots U widths) <
      area U*shapeSum s (fun q j=>N+j-q*(131071-h))) :
    ∃ Q∈rectEvaluated Crt word s (N-1) U,¬F∣Q := by
  classical
  by_contra! common
  exact rect_contradiction hp hl Crt word s U widths M prime.ne_zero aCap bCap lCap axes box small
    nz wide num pole positive (fun W hw=>RectangularHelperShift.common_power hp hw Crt word s U prime slope seeded char common)

theorem triangle_contradiction {h N:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) (bank:P1_7.Bank) {F:Jet}
    (M:HelperPhysicalModel.Model Crt F) (fn:F≠0) {a b L0 u:ℕ}
    (aCap:a≤jetDegree F) (bCap:b≤F.natDegree) (lCap:L0≤RawPhysicalDegree.weight (131071-h) (131071-h-1) M.raw)
    (uCap:u≤seedDegree F) (small:bank.shape.B<K1.p)
    (nz:0<N) (wide:bank.shape.B*(131071-h)≤N) (num:P1_7_1.nodeRows bank.shape=bank.nodeRows)
    (pole:P1_7_1.groupedPoleMoment bank.shape.B bank.shape.J≤bank.poleMoment)
    (positive:P1_7.debit h bank + ∑ W∈range N,debitAt bank.shape h N W a b L0 (triSlots bank.shape.U u) <
      triangle bank.shape.U*shapeSum bank.shape (fun q j=>N+j-q*(131071-h)))
    (force:∀ W<N,∀ P∈rectComplete Crt word bank.shape W (fun _=>bank.shape.U),F^(power N h W)∣centerEval P) : False := by
  have floor:=Lower6960.HelperSource.crt_rank_floor Crt word bank hp hl num pole small (N-1) (width nz wide)
  unfold K1_14_1.rawVolumeAt at floor
  rw [Nat.sub_add_cancel nz] at floor
  have cost (W:ℕ) (hw:W∈range N) : finrank FX (K1_14_1.evaluated Crt word bank.shape W) ≤
      debitAt bank.shape h N W a b L0 (triSlots bank.shape.U u) := by
    rw [←RectangularHelperShift.all_axes]
    have rank:=(HelperBankRank.bank_rank hp hl Crt word bank.shape (fun _=>bank.shape.U) M fn (force W (mem_range.mp hw))).2
    exact rank.trans (Nat.mul_le_mul (card_le_card (cells_mono bank.shape h W _ aCap bCap lCap)) (tri_mono _ uCap _))
  exact Nat.not_lt_of_ge (floor.trans (Nat.add_le_add_left (sum_le_sum cost) _)) positive

theorem triangle_avoiding {h N:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) (bank:P1_7.Bank) {F:Jet}
    (M:HelperPhysicalModel.Model Crt F) (prime:Irreducible F) (slope:0<F.natDegree)
    (seeded:K1_14_2.UsesSeed F) (char:bank.shape.U<K1.p) {a b L0 u:ℕ}
    (aCap:a≤jetDegree F) (bCap:b≤F.natDegree) (lCap:L0≤RawPhysicalDegree.weight (131071-h) (131071-h-1) M.raw)
    (uCap:u≤seedDegree F) (small:bank.shape.B<K1.p)
    (nz:0<N) (wide:bank.shape.B*(131071-h)≤N) (num:P1_7_1.nodeRows bank.shape=bank.nodeRows)
    (pole:P1_7_1.groupedPoleMoment bank.shape.B bank.shape.J≤bank.poleMoment)
    (positive:P1_7.debit h bank + ∑ W∈range N,debitAt bank.shape h N W a b L0 (triSlots bank.shape.U u) <
      triangle bank.shape.U*shapeSum bank.shape (fun q j=>N+j-q*(131071-h))) :
    ∃ Q∈K1_14_1.evaluated Crt word bank.shape (N-1),¬F∣Q := by
  classical
  by_contra! common
  rw [←RectangularHelperShift.all_axes] at common
  exact triangle_contradiction hp hl Crt word bank M prime.ne_zero aCap bCap lCap uCap small nz wide num pole
    positive (fun W hw=>RectangularHelperShift.common_power hp hw Crt word bank.shape _
      prime slope seeded char common)

#print axioms rect_avoiding
#print axioms triangle_avoiding
end
end Research6966.HelperAvoidance

end Merged_R6966ProofHelperAvoidance

end Merged6967_R6966ProofHelperAvoidance

section Merged6967_R6966ProofNativeAffineTariff
set_option Elab.async false




set_option Elab.async false

namespace Research6966.NativeAffineTariff
open Polynomial Finset
open K1 (K I p)
open K1_14 (FX Seeds Equation jetAt seedEmbedding)
open K1_14_3 (SeedField Surface ProjectedProduct)
open PadeNativeQuotient (Native)
open NativeAffineRows
open scoped Polynomial Differential Classical
attribute [local instance] GenericPhysicalCentre.physical
noncomputable section
set_option maxHeartbeats 900000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 18

private abbrev side (a d : ℕ) := WordSurfacePrice.side (Fintype.card I) a d

theorem side_explicit (a d h : ℕ) : side a d h=WordSurfacePrice.side (Fintype.card I) a d h := rfl

private theorem add_fee {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt a M Γ) {G : Pade.Row SeedField} (N : Native G) (k bill extra : ℕ)
    (reg : (good F T N).card*k ≤ bill) (exc : (bad F T N).card ≤ extra) :
    T.card*k ≤ extra*k+bill := by
  rw [← sizes F N, Nat.add_mul, Nat.add_comm (extra*k)]
  exact Nat.add_le_add reg (Nat.mul_le_mul_right k exc)

/-- Independent seed widths price the complete family on an actual affine
native graph. Each height is the proved nodal degree in that coordinate. -/
theorem rectangular {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt a M Γ) (sub : T ⊆ Γ) {parents : Finset Surface} {G : Pade.Row SeedField}
    (N : Native G) (gp : G.primitive) (affine : G.graphDegree = 1) (width : Fin 2 → ℕ)
    (axes : ∀ j i z, ((N.poly.coeff j).coeff i).degreeOf z ≤ width z)
    (small : width 0 < p) (d : ℕ) (physical : (131071 : ℤ)+M.overhead ≤ d) (dp : d < p)
    (gap : d < a) (owners : Owned F T parents N) :
    T.card*(a-d)^3 ≤ (width 0+p*width 1)*(a-d)^3+
      6*side a d 1*side a d (d*width 0)*side a d (d*width 1) := by
  obtain ⟨enough, shared⟩ := nodal_count_hypotheses F sub N gp affine d physical dp owners
  have count := WordUnconstrainedPrice.three_axes (fun z : ↥(good F T N) => point F z.val)
    (rows M N d) _ a d gap (row_caps M N width axes d) enough shared
  rw [Fintype.card_coe, Fin.prod_univ_three] at count
  have reg : (good F T N).card*(a-d)^3 ≤ 6*side a d 1*side a d (d*width 0)*side a d (d*width 1) := by
    simpa only [show (1:Fin 3) = (0:Fin 2).succ from rfl, show (2:Fin 3) = (1:Fin 2).succ from rfl,
      Fin.cons_zero, Fin.cons_succ, ← Nat.mul_assoc] using count
  exact add_fee F N _ _ _ reg (fee F N gp affine width axes small owners)

/-- The projected surface can give a lower price than the unconstrained
three-coordinate affine family. Both prices use the same nodal rows. -/
theorem projected {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt a M Γ) (sub : T ⊆ Γ) {parents : Finset Surface} {H : Equation}
    (project : ProjectedProduct parents H) {G : Pade.Row SeedField}
    (N : Native G) (gp : G.primitive) (affine : G.graphDegree = 1) (width : Fin 2 → ℕ)
    (axes : ∀ j i z, ((N.poly.coeff j).coeff i).degreeOf z ≤ width z)
    (small : width 0 < p) (d : ℕ) (physical : (131071 : ℤ)+M.overhead ≤ d) (dp : d < p)
    (gap : d < a) (owners : Owned F T parents N) :
    T.card*(a-d)^2 ≤ (width 0+p*width 1)*(a-d)^2+2*
      (H.natDegree*side a d (d*width 0)*side a d (d*width 1)+
        KoalaRect.axisDegree H 0*side a d 1*side a d (d*width 1)+
        KoalaRect.axisDegree H 1*side a d 1*side a d (d*width 0)) := by
  obtain ⟨enough, shared⟩ := nodal_count_hypotheses F sub N gp affine d physical dp owners
  let H' := OdeSurfaceBridge.coordinates H
  let v : Fin 3 → ℕ := Fin.cons H.natDegree (KoalaRect.axisDegree H)
  have hn : H' ≠ 0 :=
    (map_ne_zero_iff _ (MvPolynomial.finSuccEquiv FX 2).symm.injective).mpr project.primitive.ne_zero
  have vanish (z : ↥(good F T N)) : MvPolynomial.eval (point F z.val) H' = 0 := by
    obtain ⟨q, hq, _, mark⟩ := owners z.val (good_subset F N z.property)
    have killed := mark (C H) (project.vanishes q hq)
    change MvPolynomial.eval (Fin.cons _ _) (OdeSurfaceBridge.coordinates H) = 0
    rw [OdeSurfaceBridge.read]
    simpa only [jetAt, coe_eval₂RingHom, eval₂_C, NonlinearMarkRows.evaluate,
      K1_14.graphEval, seedPoint] using killed
  have cap := OdeSurfaceBridge.degrees H H.natDegree (KoalaRect.axisDegree H) le_rfl
    (fun z => (OdeSurfaceBridge.axis_cap ..).mpr ((KoalaRect.axisDegree_le_iff H z _).mp le_rfl))
  have count := WordSurfacePrice.count (fun z : ↥(good F T N) => point F z.val) (rows M N d)
    H' hn vanish v _ cap (row_caps M N width axes d) a d gap enough shared
  rw [Fintype.card_coe] at count
  apply add_fee F N _ _ _ _ (fee F N gp affine width axes small owners)
  simpa only [WordSurfacePrice.mixed, v, show (1:Fin 3) = (0:Fin 2).succ from rfl,
    show (2:Fin 3) = (1:Fin 2).succ from rfl, Fin.cons_zero, Fin.cons_succ] using count

private def activeAxes (z : Fin 2) : Fin 2 ↪ Fin 3 where
  toFun := Fin.cons 0 (fun _ => z.succ)
  inj' := by
    intro i j eq
    fin_cases i <;> fin_cases j
    · rfl
    · exact (Fin.succ_ne_zero z eq.symm).elim
    · exact (Fin.succ_ne_zero z eq).elim
    · rfl

/-- Removing the unused seed gives a two-coordinate price. The surviving
seed may be the Frobenius coordinate. -/
theorem single_seed {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt a M Γ) (sub : T ⊆ Γ) {parents : Finset Surface} {G : Pade.Row SeedField}
    (N : Native G) (gp : G.primitive) (affine : G.graphDegree = 1) (width : Fin 2 → ℕ)
    (axes : ∀ j i z, ((N.poly.coeff j).coeff i).degreeOf z ≤ width z)
    (small : width 0 < p) (active : Fin 2) (inactive : ∀ z, z ≠ active → width z = 0)
    (d : ℕ) (physical : (131071 : ℤ)+M.overhead ≤ d) (dp : d < p)
    (gap : d < a) (owners : Owned F T parents N) :
    T.card*(a-d)^2 ≤ (width 0+p*width 1)*(a-d)^2+2*side a d 1*side a d (d*width active) := by
  obtain ⟨enough, shared⟩ := nodal_count_hypotheses F sub N gp affine d physical dp owners
  let h := Fin.cons (α := fun _ : Fin 2 => ℕ) 1 (fun _ => d*width active)
  have cap := row_caps M N width axes d
  have selected (i : I) (j : Fin 2) : (rows M N d i).degreeOf (activeAxes active j) ≤ h j := by
    fin_cases j
    · exact cap i 0
    · exact cap i active.succ
  have dropped (i : I) (j : Fin 3) (out : j ∉ Set.range (activeAxes active)) :
      (rows M N d i).degreeOf j = 0 := by
    revert out
    refine Fin.cases ?_ (fun z => ?_) j
    · intro out; exact (out ⟨0, rfl⟩).elim
    · intro out
      have ne : z ≠ active := fun eq => out ⟨1, by subst z; rfl⟩
      exact Nat.eq_zero_of_le_zero (by simpa only [Fin.cons_succ, inactive z ne, Nat.mul_zero] using cap i z.succ)
  have count := WordAxisPrice.two (fun z : ↥(good F T N) => point F z.val)
    (rows M N d) (activeAxes active) h a d gap selected dropped enough shared
  rw [Fintype.card_coe] at count
  exact add_fee F N _ _ _ count (fee F N gp affine width axes small owners)

private def ordinateAxis : Fin 1 ↪ Fin 3 :=
  ⟨fun _ => 0, fun i j _ => Subsingleton.elim i j⟩

/-- A fixed affine graph costs at most one agreement ratio, with no
singular-label fee. -/
theorem fixed {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt a M Γ) (sub : T ⊆ Γ) {parents : Finset Surface} {G : Pade.Row SeedField}
    (N : Native G) (gp : G.primitive) (affine : G.graphDegree = 1)
    (axes : ∀ j i z, ((N.poly.coeff j).coeff i).degreeOf z ≤ 0)
    (d : ℕ) (physical : (131071 : ℤ)+M.overhead ≤ d) (dp : d < p)
    (gap : d < a) (owners : Owned F T parents N) :
    T.card*(a-d) ≤ side a d 1 := by
  obtain ⟨enough, shared⟩ := nodal_count_hypotheses F sub N gp affine d physical dp owners
  have cap := row_caps M N (fun _ => 0) axes d
  have dropped (i : I) (j : Fin 3) (out : j ∉ Set.range ordinateAxis) :
      (rows M N d i).degreeOf j = 0 := by
    revert out
    refine Fin.cases ?_ (fun z _ => ?_) j
    · intro out; exact (out ⟨0, rfl⟩).elim
    · exact Nat.eq_zero_of_le_zero (by simpa only [Fin.cons_succ, Nat.mul_zero] using cap i z.succ)
  have count := WordAxisPrice.one (fun z : ↥(good F T N) => point F z.val)
    (rows M N d) ordinateAxis 1 a d gap (fun i => cap i 0) dropped enough shared
  rw [Fintype.card_coe] at count
  have exc : (bad F T N).card ≤ 0 := by
    simpa only [Nat.mul_zero, Nat.add_zero] using fee F N gp affine (fun _ => 0) axes (by decide) owners
  simpa only [Nat.zero_mul, Nat.zero_add] using add_fee F N _ _ _ count exc

private theorem frobenius_total_count {E : Type*} [Field E] (q width : ℕ) (pos : 0 < q)
    (Q : MvPolynomial (Fin 2) E) (nonzero : Q ≠ 0)
    (total : Q ∈ MvPolynomial.restrictWeightAtMost (fun _ => 1) width) (small : width < q)
    (marks : Finset E) (roots : ∀ t ∈ marks, MvPolynomial.eval ![t,t^q] Q = 0) :
    marks.card ≤ q*width := by
  classical
  let P := K1_10.frobeniusGraph q Q
  have weight (e : Fin 2 →₀ ℕ) (he : e ∈ Q.support) : e 0+e 1 ≤ width := by
    have wt := MvPolynomial.mem_restrictWeightAtMost.mp total e he
    rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum, Fin.sum_univ_two] at wt
    exact wt
  have axis : Q.degreeOf 0 < q := by
    refine lt_of_le_of_lt (MvPolynomial.degreeOf_le_iff.mpr ?_) small
    intro e he
    have := weight e he
    omega
  have nz : P ≠ 0 := K1_10.frobeniusGraph_ne_zero q pos Q nonzero axis
  have deg : P.natDegree ≤ q*width := by
    apply (MvPolynomial.natDegree_aeval_le_weightedTotalDegree_of_le (fun _ => q)
      (![Polynomial.X,Polynomial.X^q] : Fin 2 → Polynomial E) Q ?_).trans
    · apply Finset.sup_le
      intro e he
      rw [Finsupp.weight_eq_sum, Fin.sum_univ_two, smul_eq_mul, smul_eq_mul]
      rw [← Nat.add_mul, Nat.mul_comm]
      exact Nat.mul_le_mul_left q (weight e he)
    · intro i
      fin_cases i
      · change (Polynomial.X : Polynomial E).natDegree ≤ q
        rw [natDegree_X]; exact pos
      · change ((Polynomial.X : Polynomial E)^q).natDegree ≤ q
        rw [natDegree_pow, natDegree_X, mul_one]
  have count : marks.card ≤ P.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro t ht
    apply (Polynomial.mem_roots nz).mpr
    have eval_eq :
        (Polynomial.evalRingHom t).comp (K1_10.frobeniusGraph (F := E) q).toRingHom =
          MvPolynomial.eval ![t,t^q] := by
      apply MvPolynomial.ringHom_ext
      · intro c; simp [K1_10.frobeniusGraph]
      · intro i; fin_cases i <;> simp [K1_10.frobeniusGraph]
    exact ((RingHom.congr_fun eval_eq Q).trans (roots t ht))
  exact count.trans deg

private theorem total_fee {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt a M Γ) {G : Pade.Row SeedField}
    (N : Native G) (gp : G.primitive) (affine : G.graphDegree = 1) (width : ℕ)
    (total : leading N ∈ MvPolynomial.restrictWeightAtMost (fun _ => 1) width) (small : width < p) :
    (bad F T N).card ≤ p*width := by
  classical
  let embeddedLabel (z : K) := seedEmbedding (M.label z)
  have inj : Function.Injective embeddedLabel := seedEmbedding.injective.comp (label_inj M)
  have nonzero : leading N ≠ 0 := fun zero => NativeGraphExceptional.den_ne N gp
    (by rw [den_eq N gp affine, zero, map_zero])
  rw [← card_image_of_injective (bad F T N) inj]
  apply frobenius_total_count p width (by decide) (leading N) nonzero total small
  intro x hx
  obtain ⟨z, badz, rfl⟩ := mem_image.mp hx
  have root : NativeAffineRows.val F z (NativeGraphExceptional.den N) = 0 := (mem_filter.mp badz).2
  rw [den_eq N gp affine] at root
  unfold NativeAffineRows.val at root
  rw [eval₂_C] at root
  exact root

/-- A common total seed-degree ceiling gives the coefficient-three bound.
The singular denominator has at most `p * width` marked labels. -/
theorem price {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt a M Γ) (sub : T ⊆ Γ) {parents : Finset Surface} {G : Pade.Row SeedField}
    (N : Native G) (gp : G.primitive) (affine : G.graphDegree = 1) (width : ℕ)
    (total : ∀ j i, (N.poly.coeff j).coeff i ∈ MvPolynomial.restrictWeightAtMost (fun _ => 1) width)
    (small : width < p) (d : ℕ) (physical : (131071 : ℤ)+M.overhead ≤ d) (dp : d < p)
    (gap : d < a) (owners : Owned F T parents N) :
    T.card*(a-d)^3 ≤ p*width*(a-d)^3+3*side a d 1*(side a d (d*width))^2 := by
  classical
  let S := good F T N
  let W := MvPolynomial.restrictWeightAtMost (R := FX) (fun _ : Fin 2 => 1) width
  have hA : leading N ∈ W := total 1 0
  have hB : linear N ∈ W := by
    change (-N.poly.coeff 0).coeff 1 ∈ W
    rw [coeff_neg]; exact Submodule.neg_mem _ (total 0 1)
  have hC : constant N ∈ W := by
    change (-N.poly.coeff 0).coeff 0 ∈ W
    rw [coeff_neg]; exact Submodule.neg_mem _ (total 0 0)
  let P (z : ↥S) (j : Option (Fin 2)) : FX :=
    j.elim (K1_14.atX (F.scalar z.val)) (seedPoint (M.label z.val))
  let R (i : I) := (MvPolynomial.optionEquivLeft FX (Fin 2)).symm (equation M N d i)
  have bound (i : I) : R i ∈ MvPolynomial.restrictBidegree (Fin 2) FX 1 (d*width) := by
    apply MvPolynomial.mem_restrictBidegree.mpr
    intro e he
    have align : ((equation M N d i).coeff (e none)).coeff e.some = (R i).coeff e := by
      simpa only [R, AlgEquiv.apply_symm_apply] using
        MvPolynomial.optionEquivLeft_coeff_some_coeff_none FX (Fin 2) e (R i)
    have live : ((equation M N d i).coeff (e none)).coeff e.some ≠ 0 :=
      align ▸ MvPolynomial.mem_support_iff.mp he
    have cnz : (equation M N d i).coeff (e none) ≠ 0 := fun zero => live (by rw [zero]; simp)
    refine ⟨(le_natDegree_of_ne_zero cnz).trans (AffineMarkRows.row_degree ..), ?_⟩
    have c := MvPolynomial.mem_restrictWeightAtMost.mp
      (AffineMarkRows.row_cap _ _ _ _ _ _ hA hB hC _ _ _ (e none)) e.some (MvPolynomial.mem_support_iff.mpr live)
    rwa [← Finsupp.degree_eq_weight_one] at c
  have tests (z : ↥S) : WordSurfaceMarks.hits (P z) R = WordSurfaceMarks.hits (point F z.val) (rows M N d) := by
    ext i
    rw [WordSurfaceMarks.hit, WordSurfaceMarks.hit]
    change MvPolynomial.eval (fun j => Option.elim j _ _) (R i) = 0 ↔ _
    rw [MvPolynomial.optionEquivLeft_elim_eval, show MvPolynomial.optionEquivLeft FX (Fin 2) (R i) =
      equation M N d i from AlgEquiv.apply_symm_apply .., Polynomial.eval_map]
    change NonlinearMarkRows.evaluate (seedPoint (M.label z.val)) (K1_14.atX (F.scalar z.val))
      (equation M N d i) = 0 ↔ MvPolynomial.eval (point F z.val) (rows M N d i) = 0
    rw [← OdeSurfaceBridge.read]
    rfl
  obtain ⟨enough, shared⟩ := nodal_count_hypotheses F sub N gp affine d physical dp owners
  have enough' (z : ↥S) : a ≤ (WordSurfaceMarks.hits (P z) R).card := by
    rw [tests z]; exact enough z
  have shared' (x y : ↥S) (ne : x ≠ y) :
      ((WordSurfaceMarks.hits (P x) R) ∩ (WordSurfaceMarks.hits (P y) R)).card ≤ d := by
    rw [tests x, tests y]; exact shared x y ne
  have result := WordUnconstrainedPrice.affine P R 1 (d*width) a d gap bound
    enough' shared'
  rw [Fintype.card_coe] at result
  exact add_fee F N _ _ _ result (total_fee F N gp affine width hA small)

#print axioms rectangular
#print axioms projected
#print axioms single_seed
#print axioms fixed
#print axioms price
theorem price_floor {u deleted maxHeight a} {M:P1.ModelAt maxHeight u deleted} {Γ T:Finset K}
    (F:P1.FamilyAt a M Γ) (sub:T⊆Γ) {parents:Finset Surface} {G:Pade.Row SeedField}
    (N:Native G) (gp:G.primitive) (affine:G.graphDegree=1) (width:ℕ) (wp:0<width)
    (total:∀ j i,(N.poly.coeff j).coeff i∈MvPolynomial.restrictWeightAtMost (fun _=>1) width)
    (small:width<p) (d:ℕ) (physical:(131071:ℤ)+M.overhead≤d) (dp:d<p)
    (pos:0<d) (gap:d<a) (an:a≤262144) (owners:Owned F T parents N) :
    T.card≤p*width+(3*(d*width)^2*(262144-d)^3)/(a-d)^3 := by
  have bound:=price F sub N gp affine width total small d physical dp gap owners
  unfold side at bound
  have card : Fintype.card I=262144 := Fintype.card_fin (2^18)
  rw [card] at bound
  have c:=NativeAffineLedger.three_floor (n:=262144) (a:=a) (d:=d) (marks:=T.card) (fee:=p*width)
    (c:=3) (h₀:=d*width) (h₁:=d*width) gap an (by simpa only [pow_two,Nat.mul_assoc] using bound)
  have positive:1≤d*width:=Nat.mul_le_mul pos wp
  rw [max_eq_right positive] at c
  simpa only [pow_two,Nat.mul_assoc] using c
#print axioms price_floor
end
end Research6966.NativeAffineTariff

end Merged6967_R6966ProofNativeAffineTariff

section Merged6967_R6966ProofNativeSeedSlice
set_option Elab.async false


set_option Elab.async false

-- merged module R6966ProofNativeOrdinateMass
section Merged_R6966ProofNativeOrdinateMass

namespace Research6966.NativeOrdinateMass
open Finset Polynomial Module
open K1_14 (Jet Seeds Equation)
open K1_14_2 (Ambient toJet FibreRing OverSeeds mapGenericSeed)
open K1_14_2_2 (Active sectionDegree mass)
open K1_14_3 (Surface OnSeedFibre SeedField SeedClosure ProjectedProduct)
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false

private def ordinate (J:Ideal Ambient) : OverSeeds J := Ideal.Quotient.mk _ (MvPolynomial.X 0)
private def relation (J:Ideal Ambient) : SeedField[X] := minpoly SeedField (ordinate J)

private theorem info {J:Ideal Ambient} (act:Active J) :
    relation J≠0 ∧ (relation J).natDegree≤sectionDegree J 0 := by
  letI : Module.Finite SeedField (OverSeeds J):=act.seed_finite
  exact ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral (R:=SeedField) (ordinate J)),minpoly.natDegree_le _⟩

private theorem kills {J:Ideal Ambient} {q:Surface} (src:q.asIdeal=J.comap toJet) {y v:SeedClosure}
    (point:OnSeedFibre q y v) (act:Active J) : aeval y (relation J)=0 := by
  letI:Module.Finite SeedField (OverSeeds J):=act.seed_finite
  let ev:FibreRing→ₐ[SeedField]SeedClosure:=MvPolynomial.aeval ![y,v]
  have same:ev.toRingHom.comp mapGenericSeed=K1_14_2_6.genericSeedPoint y v := by
    simpa only [ev,MvPolynomial.aeval_X,Matrix.cons_val_zero,Matrix.cons_val_one]
      using (K1_14_2_6_1.seedPoint ev).symm
  have sign:J≤RingHom.ker (K1_14_2_6.genericSeedPoint y v) := by
    intro x hx
    have onto:Function.Surjective toJet:=by
      rw [K1_14_2_2_4_1.toJet_equiv];exact K1_14_2_2_4_1.ambientToJet.symm.surjective
    obtain ⟨P,rfl⟩:=onto x
    have eq: (RingHom.ker (K1_14_2_6.genericSeedPoint y v)).comap toJet=J.comap toJet:=
      (K1_14_3R_1.seed_chart_ker point).trans src
    exact (show P∈(RingHom.ker (K1_14_2_6.genericSeedPoint y v)).comap toJet from eq ▸ hx)
  have passes:J.map mapGenericSeed ≤ RingHom.ker ev.toRingHom := by
    apply Ideal.map_le_iff_le_comap.mpr
    rw [RingHom.comap_ker,same];exact sign
  let use:OverSeeds J→ₐ[SeedField]SeedClosure:=
    Ideal.Quotient.liftₐ _ ev (fun x hx=>passes hx)
  have value:use (ordinate J)=y := by change ev (MvPolynomial.X 0)=y;simp [ev]
  rw [←value,aeval_algHom_apply]
  simp [relation,minpoly.aeval]

private theorem curve_at_root {F:Type*} [Field F] (D:F[X]) (y v:F) (zero:D.eval y=0) :
    (C D:F[X][X])∈TerminalProjection.fibrePoint y v := by
  obtain ⟨Q,eq⟩:=(dvd_iff_isRoot.mpr zero : Polynomial.X-C y∣D)
  rw [eq,map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))

private theorem order_of_root (D:Equation) {q:Surface}
    (root:∀ y v,OnSeedFibre q y v → (D.map K1_14_3.seedGeneric).eval y=0) : K1_14_3.OrderAt q (C D) 1 := by
  intro y v hv
  simp only [K1_14_3.fibreRow,Polynomial.map_C,coe_mapRingHom]
  have powered:=Ideal.pow_mem_pow (curve_at_root _ y v (root y v hv)) 1
  rw [pow_one (C (D.map K1_14_3.seedGeneric))] at powered
  exact powered

/-- The ordinate characterising polynomial on the union of the retained
surfaces has degree bounded by the already-budgeted seed-fibre dimension.
The argument works for every projected product and for any subset of the
retained parents. -/
theorem projected_degree {parents:Finset Surface} {H:Equation} (pr:ProjectedProduct parents H)
    (sources:Finset (Ideal Ambient)) (active:∀ J∈sources,Active J)
    (covered:∀ q∈parents,∃ J∈sources,q.asIdeal=J.comap toJet) : H.natDegree≤mass sources 0 := by
  let prod:SeedField[X]:=∏J∈sources,relation J
  have pn:prod≠0:=Finset.prod_ne_zero_iff.mpr (fun J hJ=>(info (active J hJ)).1)
  have degree:prod.natDegree≤mass sources 0 := by
    rw [show prod.natDegree=∑J∈sources,(relation J).natDegree from
      natDegree_prod _ _ (fun J hJ=>(info (active J hJ)).1)]
    exact sum_le_sum (fun J hJ=>(info (active J hJ)).2)
  let D:=IsLocalization.integerNormalization (nonZeroDivisors Seeds) prod
  obtain ⟨a,an,scaled⟩:=IsLocalization.integerNormalization_spec (nonZeroDivisors Seeds) prod
  have integral:D.map (algebraMap Seeds SeedField)=C (algebraMap Seeds SeedField a)*prod := by
    simpa only [Algebra.smul_def,Polynomial.algebraMap_apply] using scaled
  have dn:D≠0:=(IsFractionRing.integerNormalization_eq_zero_iff (A:=Seeds) (p:=prod)).not.mpr pn
  have an':algebraMap Seeds SeedField a≠0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective Seeds SeedField)).mpr (nonZeroDivisors.ne_zero an)
  have dd:D.natDegree=prod.natDegree := by
    rw [←natDegree_map_eq_of_injective (IsFractionRing.injective Seeds SeedField) D,integral,natDegree_C_mul an']
  have div:=pr.divides_leading (C D) 1 (C_ne_zero.mpr dn) (fun q hq=>order_of_root D (by
    obtain ⟨J,mem,src⟩:=covered q hq
    intro y v point
    have zero:aeval y prod=0:=by
      rw [show aeval y prod=∏J∈sources,aeval y (relation J) from map_prod ..,prod_eq_zero_iff]
      exact ⟨J,mem,kills src point (active J mem)⟩
    change (D.map ((algebraMap SeedField SeedClosure).comp (algebraMap Seeds SeedField))).eval y=0
    rw [←Polynomial.map_map,integral,Polynomial.map_mul,Polynomial.map_C,eval_mul,eval_C,eval_map]
    change _*aeval y prod=0
    rw [zero,mul_zero]))
  have hd:H∣D:=by simpa only [natDegree_C,Nat.sub_zero,pow_one,leadingCoeff_C] using div
  exact (natDegree_le_of_dvd hd dn).trans (dd ▸ degree)

#print axioms projected_degree

/-- Every native ordinate relation on all selected parents contains their
squarefree projected product. -/
theorem divides_of_member {parents:Finset Surface} {H D:Equation} (pr:ProjectedProduct parents H)
    (vanish:∀ q∈parents,C D∈q.asIdeal) : H∣D := by
  by_cases z:D=0
  · simp [z]
  have hd:=pr.divides_leading (C D) 1 (C_ne_zero.mpr z) (fun q hq=>order_of_root D (by
    intro y v point
    have mem:=vanish q hq
    rw [←point,RingHom.mem_ker] at mem
    simpa only [K1_14_3.seedFibreEval,coe_eval₂RingHom,eval₂_C,eval_map] using mem))
  simpa only [natDegree_C,Nat.sub_zero,pow_one,leadingCoeff_C] using hd

#print axioms divides_of_member
end
end Research6966.NativeOrdinateMass

end Merged_R6966ProofNativeOrdinateMass

-- merged module R6966ProofNativeSeedSlice
section Merged_R6966ProofNativeSeedSlice

namespace Research6966.NativeSeedSlice
open Polynomial
open K1_14 (FX Seeds Equation)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (SectionField SectionAmbient OverOrdinate sectionBase sectionSeedLine sliceParameter Active sectionDegree)
noncomputable section
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

abbrev B := MvPolynomial (Fin 4) FX
abbrev Lift := MvPolynomial (Fin 2) Equation
local instance (priority := 1100) quotientSemiring (J:Ideal Ambient) : CommSemiring (Ambient ⧸ J) :=
  (Ideal.Quotient.commRing J).toCommSemiring
abbrev Source (J:Ideal Ambient) := MvPolynomial (Fin 2) (Ambient ⧸ J)
def z (i:Fin 2) : Equation := C (MvPolynomial.X i)
def scalar : FX →+* Lift := MvPolynomial.C.comp (C.comp MvPolynomial.C)
def parameters : Fin 4 → Lift :=
  ![(MvPolynomial.X 0 : Lift), MvPolynomial.X 1,
    MvPolynomial.C (z 0)+MvPolynomial.X 0*MvPolynomial.C (z 1),MvPolynomial.C (Polynomial.X : Equation)]
def backBase : B →+* Lift := MvPolynomial.eval₂Hom scalar parameters
def back : B[X] →+* Lift := eval₂RingHom backBase (MvPolynomial.C (z 1))
def send (J:Ideal Ambient) : Lift →+* Source J :=
  MvPolynomial.map (((Ideal.Quotient.mk J).comp toJet).comp C)
def place (J:Ideal Ambient) : B →+* Source J := (send J).comp backBase
def denom (J:Ideal Ambient) : Submonoid (Source J) :=
  (nonZeroDivisors B).map (place J).toMonoidHom
abbrev Target (J:Ideal Ambient) := Localization (denom J)
def loc (J:Ideal Ambient) := algebraMap (Source J) (Target J)
private theorem units (J:Ideal Ambient) (s:nonZeroDivisors B) :
    IsUnit (((loc J).comp (place J)) s) :=
  IsLocalization.map_units (Target J) (⟨place J s,⟨s.val,s.property,rfl⟩⟩:denom J)
def fieldMap (J:Ideal Ambient) : SectionField →+* Target J :=
  IsLocalization.lift (M:=nonZeroDivisors B) (g:=(loc J).comp (place J)) (units J)
theorem field_base (J:Ideal Ambient) (s:B) :
    fieldMap J (algebraMap B SectionField s)=loc J (place J s) := IsLocalization.lift_eq (units J) s
def ambient (J:Ideal Ambient) : Ambient →+* Source J := MvPolynomial.C.comp (Ideal.Quotient.mk J)
def chart (J:Ideal Ambient) : SectionAmbient →+* Target J :=
  MvPolynomial.eval₂Hom (fieldMap J) (fun i => loc J (ambient J (MvPolynomial.X i)))
@[simp] private theorem chart_X (J:Ideal Ambient) (i:Fin 4) :
    chart J (MvPolynomial.X i)=loc J (ambient J (MvPolynomial.X i)) := by simp [chart]
@[simp] private theorem chart_C (J:Ideal Ambient) (a:SectionField) :
    chart J (MvPolynomial.C a)=fieldMap J a := by simp [chart]

private theorem place_C (J:Ideal Ambient) (c:FX) : place J (MvPolynomial.C c)=ambient J (MvPolynomial.C c) := by
  simp [place,backBase,send,scalar,ambient,K1_14_2.toJet,K1_14_2.toRoot,K1_14_2.rootIncl,K1_14_2.rootSeeds]
private theorem place_X (J:Ideal Ambient) (i:Fin 4) :
    place J (MvPolynomial.X i) = ![MvPolynomial.X 0,MvPolynomial.X 1,
      ambient J (MvPolynomial.X 0)+MvPolynomial.X 0*ambient J (MvPolynomial.X 1),
      ambient J (MvPolynomial.X 2)] i := by
  fin_cases i <;> simp [place,backBase,send,parameters,z,ambient,
    K1_14_2.toJet,K1_14_2.toRoot,K1_14_2.rootIncl,K1_14_2.rootSeeds]
private theorem chart_base (J:Ideal Ambient) : (chart J).comp sectionBase=(loc J).comp (ambient J) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply,sectionBase,MvPolynomial.map_C,chart_C]
    change fieldMap J (algebraMap B SectionField (MvPolynomial.C c))=_
    rw [field_base,place_C]
  · intro i
    simp [chart,sectionBase]
private theorem chart_parameter (J:Ideal Ambient) (i:Fin 4) :
    fieldMap J (sliceParameter i)=loc J (place J (MvPolynomial.X i)) := field_base J _
theorem quotient_map (J:Ideal Ambient) : ∃ φ:OverOrdinate J →+* Target J,
    (∀ c:SectionField,φ (algebraMap SectionField (OverOrdinate J) c)=fieldMap J c) ∧
    φ (Ideal.Quotient.mk _ (MvPolynomial.X 1))=loc J (ambient J (MvPolynomial.X 1)) := by
  classical
  let I:=J.map sectionBase ⊔ Ideal.span {sectionSeedLine, (MvPolynomial.X 2-MvPolynomial.C (sliceParameter 3))}
  have hI : I≤RingHom.ker (chart J) := by
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap]
      intro q hq
      change chart J (sectionBase q)=0
      rw [←RingHom.comp_apply,chart_base,RingHom.comp_apply]
      simp [ambient,Ideal.Quotient.eq_zero_iff_mem.mpr hq]
    · apply Ideal.span_le.mpr
      intro p hp
      rcases hp with h|h
      · subst p
        change chart J sectionSeedLine=0
        unfold sectionSeedLine
        rw [map_sub,map_add,map_mul,chart_X,chart_X,chart_C,chart_C,chart_parameter,chart_parameter,place_X,place_X]
        simp
      · have eq:p=MvPolynomial.X 2-MvPolynomial.C (sliceParameter 3):=h
        subst p
        change chart J (MvPolynomial.X 2-MvPolynomial.C (sliceParameter 3))=0
        rw [map_sub,chart_X,chart_C,chart_parameter,place_X]
        simp
  refine ⟨Ideal.Quotient.lift I (chart J) hI,?_,?_⟩
  · intro c
    change chart J (MvPolynomial.C c)=_
    simp [chart]
  · change chart J (MvPolynomial.X 1)=_
    simp [chart]

#print axioms quotient_map

/-- Clearing the annihilator and the localization kernel costs no degree
in the moving seed. Both clearing factors are constants in that variable. -/
theorem annihilator (J:Ideal Ambient) (active:Active J) :
    ∃ p:B[X],p≠0 ∧ p.natDegree≤sectionDegree J 1 ∧ send J (back p)=0 := by
  classical
  letI : Module.Finite SectionField (OverOrdinate J):=active.ordinate_finite
  let y : OverOrdinate J:=Ideal.Quotient.mk _ (MvPolynomial.X 1)
  let m:=minpoly SectionField y
  have mn:m≠0:=minpoly.ne_zero (Algebra.IsIntegral.isIntegral (R:=SectionField) y)
  have md:m.natDegree≤sectionDegree J 1:=minpoly.natDegree_le _
  let d:=IsLocalization.integerNormalization (nonZeroDivisors B) m
  obtain ⟨a,ha,scaled⟩:=IsLocalization.integerNormalization_spec (nonZeroDivisors B) m
  have integral:d.map (algebraMap B SectionField)=C (algebraMap B SectionField a)*m := by
    simpa only [Algebra.smul_def,Polynomial.algebraMap_apply] using scaled
  have dn:d≠0:=(IsFractionRing.integerNormalization_eq_zero_iff (A:=B) (p:=m)).not.mpr mn
  have an:algebraMap B SectionField a≠0:=(map_ne_zero_iff _ (IsFractionRing.injective B SectionField)).mpr (nonZeroDivisors.ne_zero ha)
  have degree:d.natDegree=m.natDegree:=by
    rw [←natDegree_map_eq_of_injective (IsFractionRing.injective B SectionField) d,integral,natDegree_C_mul an]
  obtain ⟨φ,hc,hy⟩:=quotient_map J
  have sy : send J (MvPolynomial.C (z 1))=ambient J (MvPolynomial.X 1) := by
    simp [send,z,ambient,K1_14_2.toJet,K1_14_2.toRoot,K1_14_2.rootIncl,K1_14_2.rootSeeds]
  have comm : (loc J).comp ((send J).comp back) =
      (φ.comp (aeval y).toRingHom).comp (mapRingHom (algebraMap B SectionField)) := by
    apply Polynomial.ringHom_ext'
    · apply RingHom.ext
      intro b
      change loc J (send J (back (C b)))=φ (aeval y ((C b).map (algebraMap B SectionField)))
      rw [Polynomial.map_C,aeval_C,hc,field_base]
      simp [place,back]
    · simp only [RingHom.comp_apply,coe_mapRingHom,Polynomial.map_X,AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe,aeval_X]
      calc
        _ = loc J (send J (MvPolynomial.C (z 1))) := by simp [back]
        _ = loc J (ambient J (MvPolynomial.X 1)) := congrArg _ sy
        _ = φ y := hy.symm
  have clear : loc J (send J (back d))=0 := by
    change ((loc J).comp ((send J).comp back)) d=0
    rw [comm]
    change φ (aeval y (d.map (algebraMap B SectionField)))=0
    rw [integral,map_mul,show aeval y m=0 from minpoly.aeval ..,mul_zero,map_zero]
  obtain ⟨s,hs⟩ := (IsLocalization.map_eq_zero_iff (denom J) (Target J) _).mp clear
  obtain ⟨c,hc,he⟩:=s.property
  have cn:c≠0:=nonZeroDivisors.ne_zero hc
  refine ⟨C c*d,mul_ne_zero (C_ne_zero.mpr cn) dn,?_,?_⟩
  · rwa [natDegree_C_mul cn,degree]
  · have hs' : (s:Source J)*send J (back d)=0 := hs
    have ef : (s:Source J)=send J (backBase c) := he.symm
    rw [ef] at hs'
    rw [map_mul,map_mul]
    simpa only [back,coe_eval₂RingHom,eval₂_C] using hs'

#print axioms annihilator

theorem common_relation {parents:Finset K1_14_3.Surface} {H:Equation}
    (proj:K1_14_3.ProjectedProduct parents H) (sources:Finset (Ideal Ambient))
    (active:∀ J∈sources,Active J) (origins:∀ q∈parents,∃ J∈sources,q.asIdeal=J.comap toJet) :
    ∃ D:B[X], D≠0 ∧ D.natDegree≤K1_14_2_2.mass sources 1 ∧ MvPolynomial.C H∣back D := by
  classical
  choose p pn pd vanish using fun J : sources => annihilator J.val (active J.val J.property)
  let D:B[X]:=∏ J:sources,p J
  have dn:D≠0:=Finset.prod_ne_zero_iff.mpr (fun J _=>pn J)
  refine ⟨D,dn,?_,?_⟩
  · calc
      _ = ∑ J:sources,(p J).natDegree := Polynomial.natDegree_prod _ _ (fun J _=>pn J)
      _ ≤ ∑ J:sources,sectionDegree J.val 1 := Finset.sum_le_sum fun J _=>pd J
      _ = _ := by
        simp [K1_14_2_2.mass]
        exact Finset.sum_attach sources (fun J=>sectionDegree J 1)
  · apply (MvPolynomial.C_dvd_iff_dvd_coeff ..).mpr
    intro m
    apply NativeOrdinateMass.divides_of_member proj
    intro q hq
    obtain ⟨J,hJ,eq⟩:=origins q hq
    have zero : send J (back D)=0 := by
      simp only [D,map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ (⟨J,hJ⟩:sources)) (vanish ⟨J,hJ⟩)
    rw [eq]
    change toJet (C ((back D).coeff m))∈J
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have zc:=congrArg (fun f:Source J=>f.coeff m) zero
    simpa only [send,MvPolynomial.coeff_map,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply,RingHom.comp_apply] using zc

#print axioms common_relation
end
end Research6966.NativeSeedSlice

end Merged_R6966ProofNativeSeedSlice

end Merged6967_R6966ProofNativeSeedSlice
