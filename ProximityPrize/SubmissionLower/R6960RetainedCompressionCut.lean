import ProximityPrize.SubmissionLower.R6960RetainedCompressionRelations
import ProximityPrize.SubmissionLower.R6960RetainedCompressionFactors
import ArkLib.Data.Polynomial.ResultantSpecialization

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

/-- View an integral equation as a polynomial in the ordinate with
coefficients in the abscissa and seed variables. -/
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

/-- Every nonzero ordinate coefficient retains its individual abscissa weight. -/
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

/-- The escaping relation supplies one proper resultant for the whole factor.
A nonzero abscissa coefficient counts all of its marked scalar labels. -/
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
