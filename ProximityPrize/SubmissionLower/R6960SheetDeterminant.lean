import ProximityPrize.SubmissionLower.R6960MarkedSheet
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

noncomputable section
set_option Elab.async false
namespace Lower6960.SheetDeterminant
open Polynomial Finset Matrix
open scoped BigOperators Matrix Polynomial

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Rank loss in the residue field forces a uniformizer power in the actual
minor. Lifting the two basis changes only uses surjectivity on residues. -/
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
/-- The constant column absorbs the common value on the unmarked sheets.
The kernel injection retains the original coordinates even when all their
evaluations vanish at this specialization. -/
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

/-- Orbit multiplicity in the local determinant product. Only the selected
minor and its translates enter the product. Other coordinate minors may vanish. -/
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

/-- Divisibility by powers of the actual base parameter recovers its base
multiplicity at any place over the scalar, including a ramified place. -/
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

/-- Count all marked quotient directions from one descended determinant
product. A single unramified local ring over each scalar suffices. -/
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
