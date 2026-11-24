import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.BigOperators.Associated
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 5100000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionTame
noncomputable section
open Matrix Module
open scoped Matrix BigOperators
variable {A K ι : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Fintype ι] [DecidableEq ι]
private theorem injective_of_one_layer (π : A) (pir : Irreducible π) (M : Matrix ι ι A)
    (one_layer : ∀ w : ι→A, (∀ i,π^2∣(M *ᵥ w) i) → ∀ i,π∣w i) :
    Function.Injective (Matrix.toLin' M) := by
  classical
  let f := Matrix.toLin' M
  apply (injective_iff_map_eq_zero f).mpr
  intro w zero
  have all (n : ℕ) : ∃ t : ι→A,w=π^n • t ∧ f t=0 := by
    induction n with
    | zero => exact ⟨w,by simp,zero⟩
    | succ n ih =>
      obtain ⟨t,eq,ft⟩ := ih
      have allDvd : ∀ i,π∣t i := one_layer t (fun i=>by
        have e := congrFun ft i
        change (M *ᵥ t) i=0 at e
        rw [e]
        exact dvd_zero _)
      choose u hu using allDvd
      have tu : t=π • u := funext hu
      have fu : f u=0 := by
        rw [tu,f.map_smul] at ft
        funext i
        exact (mul_eq_zero.mp (congrFun ft i)).resolve_left pir.ne_zero
      refine ⟨u,?_ ,fu⟩
      rw [eq,tu,smul_smul,pow_succ]
  funext i
  by_contra nz
  obtain ⟨m,a,ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible nz pir
  obtain ⟨u,eq,_⟩ := all (m+1)
  have dvd : π^(m+1)∣w i := ⟨u i,congrFun eq i⟩
  rw [ha] at dvd
  have c := (IsDiscreteValuationRing.addVal_le_iff_dvd (R:=A)).mpr dvd
  simp only [AddValuation.map_mul,AddValuation.map_pow,IsDiscreteValuationRing.addVal_eq_zero_of_unit,
    IsDiscreteValuationRing.addVal_uniformizer pir,nsmul_eq_mul,mul_one,zero_add,ENat.natCast_le_natCast] at c
  omega
private theorem basis_change_unit {A : Type*} [CommRing A]
    (a b : Basis ι A (ι→A)) : IsUnit (LinearMap.toMatrix a b (LinearMap.id (R:=A))) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨LinearMap.toMatrix b a LinearMap.id,?_⟩
  rw [←LinearMap.toMatrix_comp b a b,LinearMap.id_comp,LinearMap.toMatrix_id]
omit [DecidableEq ι] in
private theorem count_zeros [DecidableEq K] (a : ι → K) :
    (∑ i,if a i=0 then (1:ℕ) else 0)=Fintype.card ι-Fintype.card {i // a i≠0} := by
  classical
  rw [Finset.sum_boole,←Fintype.card_subtype]
  simpa only [Nat.cast_id,ne_eq,not_not] using (Fintype.card_subtype_compl (fun i=>a i≠0))
theorem matrix_order_corank (π : A) (pir : Irreducible π) (M : Matrix ι ι A)
    (red : A→+*K) (ker : ∀ x,red x=0 ↔ π∣x)
    (nonunits : ∀ x:A,¬IsUnit x ↔ π∣x)
    (one_layer : ∀ w : ι→A, (∀ i,π^2∣(M *ᵥ w) i) → ∀ i,π∣w i) :
    Associated M.det (π^(Fintype.card ι-(M.map red).rank)) := by
  classical
  let f := Matrix.toLin' M
  let N := LinearMap.range f
  let e : (ι→A) ≃ₗ[A] N := LinearEquiv.ofInjective f (injective_of_one_layer π pir M one_layer)
  have rank : finrank A N=finrank A (ι→A) := e.finrank_eq.symm
  let b := Pi.basisFun A ι
  let dst := Submodule.smithNormalFormTopBasis b rank
  let bot := Submodule.smithNormalFormBotBasis b rank
  let src := bot.map e.symm
  let a := Submodule.smithNormalFormCoeffs b rank
  have diag_change (i : ι) : f (src i)=a i • dst i := by
    have h : f (src i)=(bot i:N) := congrArg Subtype.val (e.apply_symm_apply (bot i))
    exact h.trans (Submodule.smithNormalFormBotBasis_def b rank i)
  have shallow (i : ι) : ¬π^2∣a i := by
    rintro ⟨c,hc⟩
    have deep (j : ι) : π^2∣(M *ᵥ src i) j := by
      change π^2∣f (src i) j
      rw [diag_change]
      change π^2∣a i * dst i j
      rw [hc,mul_assoc]
      exact dvd_mul_right _ _
    choose u hu using one_layer (src i) deep
    have eq : src i=π • u := funext hu
    have bad := congrArg (fun v=>src.repr v i) eq
    rw [Basis.repr_self,Finsupp.single_eq_same,src.repr.map_smul,Finsupp.smul_apply,smul_eq_mul] at bad
    exact pir.not_isUnit (isUnit_iff_dvd_one.mpr ⟨_,bad⟩)
  have dia : LinearMap.toMatrix src dst f=diagonal a := by
    apply Matrix.ext
    intro i j
    rw [LinearMap.toMatrix_apply,diag_change,dst.repr.map_smul,Finsupp.smul_apply,
      Basis.repr_self,Matrix.diagonal_apply]
    by_cases eq : j=i
    · subst i
      simp only [Finsupp.single_eq_same,smul_eq_mul,mul_one,ite_true]
    · rw [Finsupp.single_eq_of_ne (Ne.symm eq),smul_zero]
      simp only [Ne.symm eq,ite_false]
  let U := LinearMap.toMatrix b dst (LinearMap.id (R:=A))
  let V := LinearMap.toMatrix src b (LinearMap.id (R:=A))
  have uU : IsUnit U := basis_change_unit b dst
  have uV : IsUnit V := basis_change_unit src b
  have std : LinearMap.toMatrix b b f=M := by
    change LinearMap.toMatrix (Pi.basisFun A ι) (Pi.basisFun A ι) (Matrix.toLin' M)=M
    rw [←Matrix.toLin_eq_toLin',LinearMap.toMatrix_toLin]
  have scaled : U*M*V=diagonal a := by
    rw [←dia,←std]
    unfold U V
    rw [←LinearMap.toMatrix_comp b b dst,LinearMap.id_comp,
      ←LinearMap.toMatrix_comp src b dst,LinearMap.comp_id]
  have determinant : Associated M.det (∏ i,a i) := by
    obtain ⟨u,hu⟩ := (Matrix.isUnit_iff_isUnit_det U).mp uU
    obtain ⟨v,hv⟩ := (Matrix.isUnit_iff_isUnit_det V).mp uV
    refine ⟨u*v,?_⟩
    rw [Units.val_mul,hu,hv,←det_diagonal,←scaled,det_mul,det_mul]
    ac_rfl
  have urU : IsUnit ((U.map red).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (uU.map red.mapMatrix)
  have urV : IsUnit ((V.map red).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (uV.map red.mapMatrix)
  have rdiag : (U.map red)*(M.map red)*(V.map red)=diagonal (fun i=>red (a i)) := by
    have h := congrArg red.mapMatrix scaled
    rw [map_mul,map_mul] at h
    refine h.trans ?_
    apply Matrix.ext
    intro i j
    by_cases eq : i=j <;> simp [eq]
  have rr : (M.map red).rank=Fintype.card {i // red (a i)≠0} := by
    rw [←Matrix.rank_mul_eq_right_of_isUnit_det _ _ urU,
      ←Matrix.rank_mul_eq_left_of_isUnit_det _ _ urV,rdiag,rank_diagonal]
  have entries (i : ι) : Associated (a i) (π^(if red (a i)=0 then (1:ℕ) else 0)) := by
    by_cases hz : red (a i)=0
    · obtain ⟨c,hc⟩ := (ker _).mp hz
      have unit : IsUnit c := by
        by_contra hu
        obtain ⟨r,hr⟩ := (nonunits _).mp hu
        exact shallow i ⟨r,by rw [hc,hr,pow_two,mul_assoc]⟩
      obtain ⟨u,hu⟩ := unit
      simp only [hz,ite_true,pow_one]
      exact Associated.symm ⟨u,by rw [hu,hc]⟩
    · have unit : IsUnit (a i) := by
        by_contra nu
        exact hz ((ker _).mpr ((nonunits _).mp nu))
      simpa only [hz,ite_false,pow_zero] using (associated_one_iff_isUnit.mpr unit)
  refine determinant.trans ?_
  have product := Associated.prod Finset.univ _ _ (fun i _=>entries i)
  rw [Finset.prod_pow_eq_pow_sum,count_zeros,←rr] at product
  exact product
#print axioms matrix_order_corank
end
end Lower6960.CollisionTame
