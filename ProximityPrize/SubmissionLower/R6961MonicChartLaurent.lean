import ProximityPrize.SubmissionLower.R6961MonicChartProbes
import ProximityPrize.SubmissionLower.R6961ChartOverlapTests
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6961.MonicChartLaurent
noncomputable section
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open Lower6960.PlaneConstants (Plane)
open MonicFourChartDescent (baseChart chartCoordinate constants scalarCoordinate)
open MonicChartProbes (planeMap planeMap_range planeMap_injective)
open Lower6960.ChartSections (Chart Exponent allowed fits overlap)
open scoped Polynomial BigOperators

scoped instance chartConstantsAlgebra : Algebra L ChartField := constants.toAlgebra

abbrev Coefficients := Exponent →₀ L

/-- An actual rational monomial in the signed abscissa and scalar powers. -/
def monomial (m : Exponent) : ChartField := RatFunc.X^m.1 * scalarCoordinate^m.2

theorem monomial_add (m n : Exponent) : monomial (m+n)=monomial m*monomial n := by
  change RatFunc.X^(m.1+n.1) * scalarCoordinate^(m.2+n.2)=_
  rw [zpow_add₀ RatFunc.X_ne_zero,zpow_add₀ ChartOverlapTests.scalar_ne]
  unfold monomial
  ring

@[simp] theorem monomial_zero : monomial 0=1 := by simp [monomial]

theorem monomial_ne_zero (m : Exponent) : monomial m≠0 :=
  mul_ne_zero (zpow_ne_zero _ RatFunc.X_ne_zero) (zpow_ne_zero _ ChartOverlapTests.scalar_ne)

/-- Evaluate a finite Laurent coefficient table in the actual chart field. -/
def eval : Coefficients →ₗ[L] ChartField := Finsupp.linearCombination L monomial

theorem eval_apply (q : Coefficients) : eval q=q.sum fun m c=>constants c*monomial m := by
  simp only [eval,Finsupp.linearCombination_apply,Algebra.smul_def]
  rfl

@[simp] theorem eval_single (m : Exponent) (c : L) :
    eval (Finsupp.single m c)=constants c*monomial m := by
  rw [eval_apply,Finsupp.sum_single_index (by rw [map_zero,zero_mul])]

private def shift (m : Exponent) : Exponent ≃ Exponent where
  toFun n := n+m
  invFun n := n-m
  left_inv _ := add_sub_cancel_right _ _
  right_inv _ := sub_add_cancel _ _

/-- Translate all Laurent exponents by the same integer pair. -/
def translate (m : Exponent) : Coefficients ≃+ Coefficients := Finsupp.domCongr (shift m)

@[simp] theorem translate_apply (m n : Exponent) (q : Coefficients) : translate m q n=q (n-m) := rfl

theorem mem_support_translate (m n : Exponent) (q : Coefficients) :
    n∈(translate m q).support ↔ n-m∈q.support := by
  simp only [Finsupp.mem_support_iff,translate_apply]

theorem forall_support_translate_iff (m : Exponent) (q : Coefficients) (P : Exponent → Prop) :
    (∀ n∈(translate m q).support,P n) ↔ ∀ n∈q.support,P (n+m) := by
  constructor
  · intro h n hn
    apply h
    exact (mem_support_translate m (n+m) q).mpr (by simpa only [add_sub_cancel_right] using hn)
  · intro h n hn
    exact (sub_add_cancel n m) ▸ h (n-m) ((mem_support_translate m n q).mp hn)

theorem eval_translate (m : Exponent) (q : Coefficients) : eval (translate m q)=monomial m*eval q := by
  rw [eval_apply,eval_apply,translate,Finsupp.domCongr_apply,Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.sum_mapDomain_index (fun _=>by rw [map_zero,zero_mul])
      (fun _ _ _=>by rw [map_add,add_mul])]
  unfold Finsupp.sum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  change constants (q n)*monomial (n+m)=monomial m*(constants (q n)*monomial n)
  rw [monomial_add]
  ring

private def signedIndex (inverse : Bool) (n : ℕ) : ℤ := if inverse then -(n:ℤ) else n

private theorem signedIndex_injective (s : Bool) : Function.Injective (signedIndex s) := by
  intro a b eq
  cases s <;> simp [signedIndex] at eq <;> omega

private def chartExponent (s : Chart) : ℕ×ℕ ↪ Exponent where
  toFun n := (signedIndex s.1 n.1,signedIndex s.2 n.2)
  inj' := fun _ _ eq => Prod.ext (signedIndex_injective _ (congrArg Prod.fst eq))
    (signedIndex_injective _ (congrArg Prod.snd eq))

private theorem fits_iff_signed (s : Bool) (m : ℤ) : fits 0 s m ↔ ∃ n : ℕ,signedIndex s n=m := by
  cases s <;> simp only [fits,signedIndex,Nat.cast_zero,neg_zero,Bool.false_eq_true,ite_false,ite_true]
  · exact ⟨fun h=>⟨m.toNat,Int.toNat_of_nonneg h⟩,by rintro ⟨n,rfl⟩; omega⟩
  · exact ⟨fun h=>⟨(-m).toNat,by omega⟩,by rintro ⟨n,rfl⟩; omega⟩

private theorem allowed_iff_range (s : Chart) (m : Exponent) :
    allowed 0 0 s m ↔ m∈Set.range (chartExponent s) := by
  constructor
  · rintro ⟨hx,hz⟩
    obtain ⟨i,hi⟩ := (fits_iff_signed _ _).mp hx
    obtain ⟨j,hj⟩ := (fits_iff_signed _ _).mp hz
    exact ⟨(i,j),Prod.ext hi hj⟩
  · rintro ⟨⟨i,j⟩,rfl⟩
    exact ⟨(fits_iff_signed _ _).mpr ⟨i,rfl⟩,(fits_iff_signed _ _).mpr ⟨j,rfl⟩⟩

private theorem pow_signed (s : Bool) (x : ChartField) (n : ℕ) :
    x^signedIndex s n=(chartCoordinate s x)^n := by
  cases s <;> simp [signedIndex,chartCoordinate,zpow_neg,zpow_natCast,inv_pow]

private def toPlane (q : ℕ×ℕ →₀ L) : Plane L :=
  q.sum fun n c=>Polynomial.monomial n.1 (Polynomial.monomial n.2 c)

private theorem coeff_toPlane (q : ℕ×ℕ →₀ L) (i j : ℕ) : ((toPlane q).coeff i).coeff j=q (i,j) := by
  classical
  unfold toPlane Finsupp.sum
  rw [Polynomial.finsetSum_coeff,Polynomial.finsetSum_coeff]
  have summand (m : ℕ×ℕ) :
      (((Polynomial.monomial m.1 (Polynomial.monomial m.2 (q m)) : Plane L).coeff i).coeff j)=
        if m=(i,j) then q m else 0 := by
    rcases m with ⟨a,b⟩
    by_cases x : a=i <;> by_cases z : b=j <;> simp [Polynomial.coeff_monomial,x,z,Ne.symm]
  simp only [summand,Finset.sum_ite_eq']
  by_cases mem : (i,j)∈q.support
  · simp only [mem,ite_true]
  · simp only [mem,ite_false,Finsupp.notMem_support_iff.mp mem]

private theorem toPlane_injective : Function.Injective toPlane := by
  intro a b eq
  ext ⟨i,j⟩
  simpa only [coeff_toPlane] using congrArg (fun f : Plane L=>(f.coeff i).coeff j) eq

private theorem toPlane_surjective : Function.Surjective toPlane := by
  intro p
  let table : ℕ →₀ ℕ →₀ L := p.coeff.mapRange (fun q : Polynomial L => q.coeff) (by ext i; simp)
  refine ⟨table.uncurry,?_⟩
  apply Polynomial.ext
  intro i
  apply Polynomial.ext
  intro j
  rw [coeff_toPlane,Finsupp.uncurry_apply_pair]
  simp only [table,Finsupp.mapRange_apply]

private theorem eval_chartExponent (s : Chart) (a : ℕ×ℕ →₀ L) :
    eval (a.embDomain (chartExponent s))=planeMap s (toPlane a) := by
  rw [eval_apply,Finsupp.embDomain_eq_mapDomain,
    Finsupp.sum_mapDomain_index (fun _=>by rw [map_zero,zero_mul])
      (fun _ _ _=>by rw [map_add,add_mul])]
  unfold toPlane Finsupp.sum
  rw [map_sum]
  apply Finset.sum_congr rfl
  rintro ⟨i,j⟩ _
  simp only [←Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow,MonicChartProbes.planeMap_constants,
    MonicChartProbes.planeMap_abscissa,MonicChartProbes.planeMap_scalar]
  change constants (a (i,j))*(RatFunc.X^signedIndex s.1 i*scalarCoordinate^signedIndex s.2 j)=_
  rw [pow_signed,pow_signed]
  ring

private theorem in_quadrant {q : Coefficients} (s : Chart) (h : ∀ m∈q.support,allowed 0 0 s m) :
    ∃ a : ℕ×ℕ →₀ L, a.embDomain (chartExponent s)=q := by
  have range : (↑q.support : Set Exponent) ⊆ Set.range (chartExponent s) :=
    fun m hm=>(allowed_iff_range s m).mp (h m hm)
  exact ⟨_,Finsupp.embDomain_comapDomain range⟩

private def magnitude (q : Coefficients) : ℕ := q.support.sup fun m=>max m.1.natAbs m.2.natAbs

private theorem support_bounded (q : Coefficients) {m : Exponent} (hm : m∈q.support) :
    -(magnitude q:ℤ)≤m.1 ∧ m.1≤magnitude q ∧ -(magnitude q:ℤ)≤m.2 ∧ m.2≤magnitude q := by
  have sup : max m.1.natAbs m.2.natAbs≤magnitude q :=
    Finset.le_sup (f:=fun n : Exponent=>max n.1.natAbs n.2.natAbs) hm
  have a := (le_max_left m.1.natAbs m.2.natAbs).trans sup
  have b := (le_max_right m.1.natAbs m.2.natAbs).trans sup
  omega

/-- There are no Laurent coefficient relations in the actual rational field. -/
theorem eval_injective : Function.Injective eval := by
  apply (injective_iff_map_eq_zero eval).mpr
  intro q zero
  let N := (magnitude q : ℤ)
  let m : Exponent := (N,N)
  have standard (n : Exponent) (hn : n∈(translate m q).support) : allowed 0 0 (false,false) n := by
    obtain ⟨loX,_,loZ,_⟩ := support_bounded q ((mem_support_translate m n q).mp hn)
    change 0≤n.1 ∧ 0≤n.2
    change -N≤n.1-N at loX
    change -N≤n.2-N at loZ
    omega
  obtain ⟨a,ha⟩ := in_quadrant (false,false) standard
  have eval_zero : eval (translate m q)=0 := by rw [eval_translate,zero,mul_zero]
  have plane_zero : toPlane a=0 :=
    (map_eq_zero_iff _ (planeMap_injective (false,false))).mp ((eval_chartExponent _ _).symm.trans (ha ▸ eval_zero))
  have az : a=0 := toPlane_injective (plane_zero.trans (by simp [toPlane]))
  apply (translate m).injective
  rw [←ha,az,Finsupp.embDomain_zero,map_zero]

theorem monomial_linearIndependent : LinearIndependent L monomial :=
  linearIndependent_iff_injective_finsuppLinearCombination.mpr eval_injective

/-- Membership in a chart is exactly Laurent representability in its
unshifted quadrant. -/
theorem mem_baseChart_iff (s : Chart) (r : ChartField) : r∈baseChart s ↔
    ∃ q : Coefficients, eval q=r ∧ ∀ m∈q.support, allowed 0 0 s m := by
  constructor
  · intro h
    rw [←planeMap_range s] at h
    obtain ⟨P,hP⟩ := h
    obtain ⟨a,ha⟩ := toPlane_surjective P
    refine ⟨a.embDomain (chartExponent s),by rw [eval_chartExponent,ha,hP],?_⟩
    intro m hm
    rw [Finsupp.support_embDomain,Finset.mem_map] at hm
    obtain ⟨n,_,eq⟩ := hm
    exact (allowed_iff_range s m).mpr ⟨n,eq⟩
  · rintro ⟨q,rfl,hq⟩
    obtain ⟨a,rfl⟩ := in_quadrant s hq
    rw [eval_chartExponent,←planeMap_range s]
    exact ⟨_,rfl⟩

theorem eval_mem_baseChart_iff (s : Chart) (q : Coefficients) : eval q∈baseChart s ↔
    ∀ m∈q.support, allowed 0 0 s m := by
  rw [mem_baseChart_iff]
  exact ⟨fun ⟨p,h,hp⟩=>eval_injective h ▸ hp,fun h=>⟨q,rfl,h⟩⟩

/-- The localization of a chart in its coordinates that change on the overlap. -/
abbrev overlapRing (s t : Chart) : Subring ChartField :=
  ChartOverlapTests.cleared (baseChart s) ⟨ChartOverlapTests.boundary s t,ChartOverlapTests.boundary_mem s t⟩

/-- The exponent of the power used to clear the overlap denominators. -/
def clearingExponent (s t : Chart) (n : ℕ) : Exponent :=
  (if s.1=t.1 then 0 else signedIndex s.1 n,if s.2=t.2 then 0 else signedIndex s.2 n)

theorem monomial_clearingExponent (s t : Chart) (n : ℕ) :
    monomial (clearingExponent s t n)=(ChartOverlapTests.boundary s t)^n := by
  unfold monomial clearingExponent ChartOverlapTests.boundary
  rw [mul_pow]
  by_cases hx : s.1=t.1 <;> by_cases hz : s.2=t.2 <;>
    simp only [hx,hz,ite_true,ite_false,zpow_zero,one_pow,pow_signed]

theorem eval_clear (s t : Chart) (n : ℕ) (q : Coefficients) :
    eval (translate (clearingExponent s t n) q)=(ChartOverlapTests.boundary s t)^n*eval q := by
  rw [eval_translate,monomial_clearingExponent]

private theorem fits_after_clear (s t : Bool) {n : ℕ} {m : ℤ}
    (lo : -(n:ℤ)≤m) (hi : m≤n) (same : s=t → fits 0 s m) :
    fits 0 s (m+(if s=t then 0 else signedIndex s n)) := by
  by_cases h : s=t
  · simpa only [h,ite_true,add_zero] using same h
  · cases s <;> simp only [h,ite_false,fits,signedIndex,Nat.cast_zero,
      neg_zero,Bool.false_eq_true,ite_true] <;> omega

/-- A finite Laurent table fits the overlap exactly when one power of
its boundary moves the whole support into the source chart's quadrant. -/
theorem support_overlap_iff_clear (s t : Chart) (q : Coefficients) :
    (∀ m∈q.support,overlap 0 0 s t m) ↔
      ∃ n : ℕ,∀ m∈(translate (clearingExponent s t n) q).support,allowed 0 0 s m := by
  constructor
  · intro h
    refine ⟨magnitude q,(forall_support_translate_iff _ _ _).mpr ?_⟩
    intro m hm
    obtain ⟨loX,hiX,loZ,hiZ⟩ := support_bounded q hm
    exact ⟨fits_after_clear s.1 t.1 loX hiX (h m hm).1,fits_after_clear s.2 t.2 loZ hiZ (h m hm).2⟩
  · rintro ⟨n,h⟩ m hm
    have yes := (forall_support_translate_iff (clearingExponent s t n) q (allowed 0 0 s)).mp h m hm
    refine ⟨fun hX=>?_,fun hZ=>?_⟩
    · have fst := yes.1
      change fits 0 s.1 (m.1+(if s.1=t.1 then 0 else signedIndex s.1 n)) at fst
      simpa only [hX,ite_true,add_zero] using fst
    · have snd := yes.2
      change fits 0 s.2 (m.2+(if s.2=t.2 then 0 else signedIndex s.2 n)) at snd
      simpa only [hZ,ite_true,add_zero] using snd

theorem eval_mem_overlap_iff (s t : Chart) (q : Coefficients) : eval q∈overlapRing s t ↔
    ∀ m∈q.support,overlap 0 0 s t m := by
  rw [support_overlap_iff_clear]
  change (∃ n : ℕ,(ChartOverlapTests.boundary s t)^n*eval q∈baseChart s) ↔ _
  simp only [←eval_clear,eval_mem_baseChart_iff]

/-- An arbitrary field element belongs to the actual overlap ring if and
only if it has a Laurent expression with the shared quadrant conditions. -/
theorem mem_overlap_iff (s t : Chart) (r : ChartField) : r∈overlapRing s t ↔
    ∃ q : Coefficients,eval q=r ∧ ∀ m∈q.support,overlap 0 0 s t m := by
  constructor
  · rintro ⟨n,h⟩
    change ChartOverlapTests.boundary s t ^ n*r∈baseChart s at h
    obtain ⟨q,hq,_⟩ := (mem_baseChart_iff s _).mp h
    let m := clearingExponent s t n
    have eq : eval (translate (-m) q)=r := by
      apply mul_left_cancel₀ (monomial_ne_zero m)
      rw [eval_translate,←mul_assoc,←monomial_add,add_neg_cancel,monomial_zero,one_mul,hq]
      rw [monomial_clearingExponent]
    exact ⟨_,eq,(eval_mem_overlap_iff s t _).mp (eq.symm ▸ (show r∈overlapRing s t from ⟨n,h⟩))⟩
  · rintro ⟨q,rfl,h⟩
    exact (eval_mem_overlap_iff s t q).mpr h

/-- The monomial accounting for the negative twist of a rational section. -/
def frameExponent (a b : ℕ) (s : Chart) : Exponent :=
  (if s.1 then (a:ℤ) else 0,if s.2 then (b:ℤ) else 0)

theorem frame_eq_monomial (a b : ℕ) (s : Chart) :
    MonicFourChartDescent.frame a b s=monomial (frameExponent a b s) := by
  rcases s with ⟨s,t⟩
  cases s <;> cases t <;> simp [MonicFourChartDescent.frame,frameExponent,monomial]

private theorem fits_frame (d : ℕ) (s : Bool) (m : ℤ) :
    fits 0 s (m+(if s then (d:ℤ) else 0)) ↔ fits d s m := by
  cases s with
  | false => simp [fits]
  | true => simp [fits]; omega

theorem frame_eval_mem_baseChart_iff (a b : ℕ) (s : Chart) (q : Coefficients) :
    MonicFourChartDescent.frame a b s*eval q∈baseChart s ↔ ∀ m∈q.support,allowed a b s m := by
  rw [frame_eq_monomial,←eval_translate,eval_mem_baseChart_iff,forall_support_translate_iff]
  change (∀ m∈q.support, fits 0 s.1 (m.1+(if s.1 then (a:ℤ) else 0)) ∧
    fits 0 s.2 (m.2+(if s.2 then (b:ℤ) else 0))) ↔ _
  simp only [fits_frame,allowed]

theorem frame_eval_mem_overlap_iff (a b : ℕ) (s t : Chart) (q : Coefficients) :
    MonicFourChartDescent.frame a b s*eval q∈overlapRing s t ↔ ∀ m∈q.support,overlap a b s t m := by
  rw [frame_eq_monomial,←eval_translate,eval_mem_overlap_iff,forall_support_translate_iff]
  change (∀ m∈q.support, (s.1=t.1 → fits 0 s.1 (m.1+(if s.1 then (a:ℤ) else 0))) ∧
    (s.2=t.2 → fits 0 s.2 (m.2+(if s.2 then (b:ℤ) else 0)))) ↔ _
  simp only [fits_frame,overlap]

section Relations
variable {I J : Type*} [Fintype I]

/-- A row of Laurent coefficients multiplies coordinate tables by
translating each table by the indicated exponent. -/
def relationCoefficients (column : I→J) (coefficient : I→L) (offset : I→Exponent)
    (q : J→Coefficients) : Coefficients :=
  ∑ i, coefficient i • translate (offset i) (q (column i))

theorem relationCoefficients_apply (column : I→J) (coefficient : I→L) (offset : I→Exponent)
    (q : J→Coefficients) (m : Exponent) :
    relationCoefficients column coefficient offset q m=Lower6960.ChartSections.relation column coefficient offset q m := by
  simp only [relationCoefficients,Lower6960.ChartSections.relation,Finsupp.finsetSum_apply,Finsupp.smul_apply,
    translate_apply,smul_eq_mul]
  rfl

theorem eval_relationCoefficients (column : I→J) (coefficient : I→L) (offset : I→Exponent)
    (q : J→Coefficients) : eval (relationCoefficients column coefficient offset q)=
      ∑ i, constants (coefficient i)*monomial (offset i)*eval (q (column i)) := by
  rw [relationCoefficients,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [eval.map_smul,eval_translate]
  change constants (coefficient i)*(monomial (offset i)*eval (q (column i)))=_
  rw [mul_assoc]

end Relations

#print axioms eval_injective
#print axioms mem_baseChart_iff
#print axioms mem_overlap_iff
#print axioms frame_eval_mem_overlap_iff
#print axioms eval_relationCoefficients
end
end Lower6961.MonicChartLaurent
