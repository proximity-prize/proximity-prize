import ProximityPrize.SubmissionLower.R6960MarkedSheet
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.RingTheory.Norm.Transitivity
import ProximityPrize.SubmissionLower.R6960MarkedEvaluationLedger
import Mathlib.FieldTheory.Galois.Basic
import ProximityPrize.SubmissionLower.R6960CollisionTameBranch
import Mathlib.RingTheory.Valuation.LocalSubring

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
