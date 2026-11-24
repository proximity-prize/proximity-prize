import ProximityPrize.SubmissionLower.R6960RetainedCompressionVolume
import ArkLib.ToMathlib.MvPolynomial.OptionWeightedDegree
import ArkLib.Data.MvPolynomial.WeightedDegree.Products

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

/-- Joint weight with one abscissa unit and (d) units for each ordinate power. -/
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

/-- Every integral element in the smaller weighted box is represented by the
coefficient space used in the dimension comparison. -/
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
