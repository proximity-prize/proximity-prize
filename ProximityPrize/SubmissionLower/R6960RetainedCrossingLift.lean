import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Gate6966Gate
import ProximityPrize.SubmissionLower.R6960ChartGlobalTests
import ProximityPrize.SubmissionLower.R6960ChartImage
import ProximityPrize.SubmissionLower.R6960CollisionTameBranchFrame
import ProximityPrize.SubmissionLower.R6960CollisionTameLineDegree
import ProximityPrize.SubmissionLower.R6960Low6960CountCore
import ProximityPrize.SubmissionLower.R6960Low6960Rectangle
import ProximityPrize.SubmissionLower.R6960MarkedMatrixNorm
import ProximityPrize.SubmissionLower.R6966ProofProtocolProfile

section Merged6967_R6960RetainedCrossingLift
set_option Elab.async false






set_option Elab.async false

-- merged module R6960RetainedLineRestriction
section Merged_R6960RetainedLineRestriction

-- merged module R6960MonicChartLaurent
section Merged_R6960MonicChartLaurent
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MonicChartLaurent
noncomputable section
open K1_14 (L)
open MonicChart (ChartField)
open PlaneConstants (Plane)
open MonicFourChartDescent (baseChart chartCoordinate constants scalarCoordinate)
open MonicChartProbes (planeMap planeMap_range planeMap_injective)
open ChartSections (Chart Exponent allowed fits overlap)
open scoped Polynomial BigOperators
scoped instance chartConstantsAlgebra : Algebra L ChartField := constants.toAlgebra
abbrev Coefficients := Exponent →₀ L
def monomial (m : Exponent) : ChartField := RatFunc.X^m.1 * scalarCoordinate^m.2
theorem monomial_add (m n : Exponent) : monomial (m+n)=monomial m*monomial n := by
  change RatFunc.X^(m.1+n.1) * scalarCoordinate^(m.2+n.2)=_
  rw [zpow_add₀ RatFunc.X_ne_zero,zpow_add₀ ChartOverlapTests.scalar_ne]
  unfold monomial
  ring
@[simp] theorem monomial_zero : monomial 0=1 := by simp [monomial]
theorem monomial_ne_zero (m : Exponent) : monomial m≠0 :=
  mul_ne_zero (zpow_ne_zero _ RatFunc.X_ne_zero) (zpow_ne_zero _ ChartOverlapTests.scalar_ne)
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
  let table : ℕ →₀ ℕ →₀ L := p.coeff.mapRange (fun q : (Polynomial L) => q.coeff) (by ext i; simp)
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
abbrev overlapRing (s t : Chart) : Subring ChartField :=
  ChartOverlapTests.cleared (baseChart s) ⟨ChartOverlapTests.boundary s t,ChartOverlapTests.boundary_mem s t⟩
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
def relationCoefficients (column : I→J) (coefficient : I→L) (offset : I→Exponent)
    (q : J→Coefficients) : Coefficients :=
  ∑ i, coefficient i • translate (offset i) (q (column i))
theorem relationCoefficients_apply (column : I→J) (coefficient : I→L) (offset : I→Exponent)
    (q : J→Coefficients) (m : Exponent) :
    relationCoefficients column coefficient offset q m=ChartSections.relation column coefficient offset q m := by
  simp only [relationCoefficients,ChartSections.relation,Finsupp.finsetSum_apply,Finsupp.smul_apply,
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
end Lower6960.MonicChartLaurent

end Merged_R6960MonicChartLaurent

-- merged module R6960MonicScalarCorrection
section Merged_R6960MonicScalarCorrection
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MonicScalarCorrection
noncomputable section
open MonicChart (ChartField)
open MonicFourChartDescent (baseChart frame frame_scale constants)
open MonicChartLaurent
open ChartSections (Chart Exponent overlap allowed)
def Compatible {E : Type*} [Field E] [Algebra ChartField E]
    (a b : ℕ) (u : Chart → E) : Prop :=
  ∀ s t, IsIntegral (overlapRing s t) (algebraMap ChartField E (frame a b s)*(u s-u t))
def ScalarCompatible (a b : ℕ) (u : Chart → ChartField) : Prop :=
  ∀ s t, frame a b s*(u s-u t) ∈ overlapRing s t
theorem scalar_coefficients (a b : ℕ) (u : Chart → ChartField) (h : ScalarCompatible a b u)
    (anchor : Chart) : ∃ q : Chart → Coefficients,
      (∀ s,eval (q s)=u s-u anchor) ∧
      ∀ s t m,¬overlap a b s t m → q s m=q t m := by
  classical
  have exists_laurent (s : Chart) : ∃ q : Coefficients,eval q=u s-u anchor := by
    obtain ⟨v,hv,_⟩ := (mem_overlap_iff s anchor _).mp (h s anchor)
    let m := frameExponent a b s
    have cancel : monomial (-m)*monomial m=1 := by
      rw [←monomial_add,neg_add_cancel,monomial_zero]
    refine ⟨translate (-m) v,?_⟩
    rw [eval_translate,hv,frame_eq_monomial,←mul_assoc,cancel,one_mul]
  choose q eq using exists_laurent
  refine ⟨q,eq,?_⟩
  intro s t m forbidden
  have diff : eval (q s-q t)=u s-u t := by
    rw [map_sub,eq,eq]
    ring
  have support : ∀ n∈(q s-q t).support,overlap a b s t n :=
    (frame_eval_mem_overlap_iff a b s t (q s-q t)).mp (by simpa only [diff] using h s t)
  exact sub_eq_zero.mp (Finsupp.notMem_support_iff.mp (fun hm=>forbidden (support m hm)))
theorem scalar_correction (a b : ℕ) (ha : 0<a) (hb : 0<b) (u : Chart → ChartField)
    (h : ScalarCompatible a b u) :
    ∃ c : ChartField,∀ s,frame a b s*(u s-c)∈baseChart s := by
  let anchor : Chart := (false,false)
  obtain ⟨q,eq,condition⟩ := scalar_coefficients a b u h anchor
  obtain ⟨v,hv⟩ := ChartSections.negative_correction a b ha hb q condition
  refine ⟨eval v+u anchor,fun s=>?_⟩
  have diff : eval (q s-v)=u s-(eval v+u anchor) := by
    rw [map_sub,eq]
    ring
  rw [←diff,frame_eval_mem_baseChart_iff]
  intro m hm
  by_contra bad
  exact Finsupp.mem_support_iff.mp hm (hv s m bad)
theorem compatible_iterate {E : Type*} [Field E] [Algebra ChartField E]
    (a b : ℕ) (u : Chart → E) (h : Compatible a b u) (n : ℕ) :
    Compatible (a*K1.p^n) (b*K1.p^n) (fun s=>u s^(K1.p^n)) := by
  let : Fact K1.p.Prime := ⟨KoalaBear.is_prime⟩
  let : CharP E K1.p := charP_of_injective_ringHom ((algebraMap ChartField E).comp constants).injective K1.p
  intro s t
  have subpow : (u s-u t)^(K1.p^n)=u s^(K1.p^n)-u t^(K1.p^n) :=
    map_sub (iterateFrobenius E K1.p n) (u s) (u t)
  have powered := (h s t).pow (K1.p^n)
  rw [mul_pow,subpow,←map_pow,←frame_scale] at powered
  exact powered
#print axioms scalar_coefficients
#print axioms scalar_correction
#print axioms compatible_iterate
end
end Lower6960.MonicScalarCorrection

end Merged_R6960MonicScalarCorrection

-- merged module R6960RetainedChartGluing
section Merged_R6960RetainedChartGluing
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedChartGluing
open ChartSections (Chart)
open MonicChart MonicFourChartDescent MonicScalarCorrection ChartGlobalTests
open RetainedCompression (Curve ordinate view height heightCap wordDegree)
open Polynomial
open K1_14 (L)
open Lower6960.MonicFourChartDescent (finite_inclusion infinity_inclusion)
private theorem frame_add (a b D : ℕ) (s : Chart) :
    frame (a+D) (b+D) s=frame a b s*frame D D s := by
  simp only [frame,pow_add]; ring
variable {E : Type*} [Field E] [Algebra ChartField E]
theorem high_twist (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0) :
    ∃ H : ℕ, ∀ a b, H<a → H<b →
      ∀ u : Chart→E, Compatible a b u → ∃ c, Correction a b u c := by
  classical
  obtain ⟨n,D,P,tests⟩:=simultaneous_tests f ir lo hi basis root
  let deq : DecidableEq ChartField := Classical.decEq _
  let : DecidableEq (RatFunc Scalar) := deq
  obtain ⟨k,image⟩:=@ChartImage.eventually_in_subspace Scalar (Fin n) _ _ deq (LinearMap.range P)
  refine ⟨k+D,fun a b ha hb u compatible => ?_⟩
  let i:=a-D
  let j:=b-D
  have ia : i+D=a := Nat.sub_add_cancel (by omega)
  have jb : j+D=b := Nat.sub_add_cancel (by omega)
  have ik : k < i := by dsimp [i]; omega
  have jpos : 0<j := by dsimp [j]; omega
  have frames (s) : frame a b s=frame i j s*frame D D s := by
    simpa only [ia,jb] using frame_add i j D s
  have transport (r : Fin n) : ScalarCompatible i j (fun s=>P (u s) r) := by
    intro s t
    let proj:= (LinearMap.proj r).comp P
    let test:= (frame D D s)⁻¹ • proj
    have regular (x:E) (hx:IsIntegral (baseChart s) x) : test x∈baseChart s := by
      simpa only [test,proj,LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.proj_apply,
        smul_eq_mul,div_eq_mul_inv,mul_comm] using (tests s x).mp hx r
    have m:=overlap_test s t test regular _ (compatible s t)
    change test (algebraMap ChartField E (frame a b s)*(u s-u t))∈_ at m
    rw [←Algebra.smul_def,map_smul,smul_eq_mul] at m
    change frame a b s*((frame D D s)⁻¹ * P (u s-u t) r)∈_ at m
    rw [frames,mul_assoc,←mul_assoc (frame D D s),mul_inv_cancel₀ (frame_ne _ _ _),one_mul,
      map_sub,Pi.sub_apply] at m
    exact m
  choose c sol using fun r => scalar_correction i j (by omega) jpos _ (transport r)
  have inField : c∈LinearMap.range P := by
    apply image i ik c (P (u (false,false))) (P (u (true,false))) ⟨_,rfl⟩ ⟨_,rfl⟩
    · intro r
      have h:=Lower6960.MonicFourChartDescent.finite_inclusion (sol r (false,false))
      simpa [frame] using (algebraMap (Polynomial Scalar) ChartField).range.neg_mem h
    · intro r
      have h:=@Lower6960.MonicFourChartDescent.infinity_inclusion deq _ (sol r (true,false))
      obtain ⟨v,eq⟩:=h
      have val : (v:ChartField)=RatFunc.X^i*(P (u (true,false)) r-c r) := by simpa [frame] using eq
      have vin : -(v:ChartField) ∈ @Infinity Scalar _ deq :=
        (@Infinity Scalar _ deq).toSubring.neg_mem v.property
      rw [val] at vin
      simpa only [←mul_neg,neg_sub] using vin
  obtain ⟨v,pv⟩:=inField
  refine ⟨v,fun s => (tests s _).mpr (fun r => ?_)⟩
  rw [←Algebra.smul_def,map_smul,map_sub,pv,Pi.smul_apply,smul_eq_mul,Pi.sub_apply,frames,
    mul_right_comm,mul_div_cancel_right₀ _ (frame_ne D D s)]
  exact sol r s
theorem common_correction (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (bounded : height wordDegree f≤heightCap (f.degreeOf ordinate) wordDegree)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0)
    (a b : ℕ) (ha : 0<a) (hb : 0<b) (u : Chart→E) (compatible : Compatible a b u) :
    ∃ c : E, Correction a b u c := by
  obtain ⟨H,high⟩:=high_twist f ir lo hi basis root
  have large : H<K1.p^H := Nat.lt_pow_self KoalaBear.is_prime.one_lt
  have above {d : ℕ} (pos : 0<d) : H<d*K1.p^H :=
    large.trans_le (Nat.le_mul_of_pos_left _ pos)
  obtain ⟨c,hc⟩:=high _ _ (above ha) (above hb) _ (compatible_iterate a b u compatible H)
  obtain ⟨d,_,hd⟩ := descend_iterate f ir lo hi bounded basis root a b ha u H c hc
  exact ⟨d,hd⟩
#print axioms high_twist
#print axioms common_correction
theorem split_cocycle (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (bounded : height wordDegree f≤heightCap (f.degreeOf ordinate) wordDegree)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0)
    (a b : ℕ) (ha : 0<a) (hb : 0<b) (g : Chart→Chart→E)
    (add : ∀ s t r, g s t+g t r=g s r)
    (regular : ∀ s t, IsIntegral (MonicChartLaurent.overlapRing s t)
      (algebraMap ChartField E (frame a b s)*g s t)) :
    ∃ w : Chart→E, (∀ s, IsIntegral (baseChart s) (algebraMap ChartField E (frame a b s)*w s)) ∧
      ∀ s t, g s t=w s-w t := by
  let u (s : Chart):=g s (false,false)
  have diff (s t) : u s-u t=g s t := sub_eq_of_eq_add (add s t (false,false)).symm
  obtain ⟨c,hc⟩:=common_correction f ir lo hi bounded basis root a b ha hb u
    (fun s t=> by rw [diff]; exact regular s t)
  exact ⟨fun s=>u s-c,hc,fun s t=>by rw [←diff]; ring⟩
#print axioms split_cocycle
end Lower6960.RetainedChartGluing

end
end Merged_R6960RetainedChartGluing

-- merged module R6960RetainedLineRestriction
section Merged_R6960RetainedLineRestriction
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedLineRestriction
open MonicFourChartDescent ChartSections MonicChart RetainedChartGluing
open ChartGlobalTests (frame_ne)
open MonicChartLaurent (overlapRing)
open MonicChartProbes (planeMap planeMap_injective)
open RetainedCompression (Curve ordinate view height heightCap wordDegree)
open Polynomial
open K1_14 (L)
def lines (x z : L) : ChartField :=
  (RatFunc.X-constants x)*(scalarCoordinate-constants z)
private theorem lines_ne (x z : L) : lines x z≠0 := by
  let m := planeMap (false,false)
  have a : (Polynomial.X (R:=(Polynomial L)))-C (C x)≠0 := X_sub_C_ne_zero _
  have b : (C (Polynomial.X (R:=L)) : (Polynomial (Polynomial L)))-C (C z)≠0 := by
    rw [←map_sub]; exact C_ne_zero.mpr (X_sub_C_ne_zero _)
  have good := (map_ne_zero_iff m (planeMap_injective _)).mpr (mul_ne_zero a b)
  simpa only [m,map_mul,map_sub,MonicChartProbes.planeMap_constants,MonicChartProbes.planeMap_scalar,
    MonicChartProbes.planeMap_abscissa,chartCoordinate,Bool.false_eq_true,ite_false,lines] using good
private theorem linear_factor (A : Subring ChartField) (b : Bool) (v c : ChartField) (nz : v≠0)
    (var : chartCoordinate b v∈A) (constant : c∈A) :
    (v-c)/(if b then v else 1)∈A := by
  cases b with
  | false => simpa [chartCoordinate] using A.sub_mem var constant
  | true =>
    change (v-c)/v∈A
    rw [sub_div,div_self nz,div_eq_mul_inv]
    exact A.sub_mem A.one_mem (A.mul_mem constant var)
theorem local_equation (x z : L) (s : Chart) : lines x z / frame 1 1 s∈baseChart s := by
  have constants_mem (c : L) : constants c∈baseChart s := Subring.subset_closure (Or.inl ⟨c,rfl⟩)
  have Xmem : chartCoordinate s.1 RatFunc.X∈baseChart s := Subring.subset_closure (Or.inr (Or.inl rfl))
  have Zmem : chartCoordinate s.2 scalarCoordinate∈baseChart s := Subring.subset_closure (Or.inr (Or.inr rfl))
  rw [lines,frame,pow_one,pow_one,←div_mul_div_comm]
  exact (baseChart s).mul_mem (linear_factor _ _ _ _ RatFunc.X_ne_zero Xmem (constants_mem x))
    (linear_factor _ _ _ _ ChartOverlapTests.scalar_ne Zmem (constants_mem z))
variable {E : Type*} [Field E] [Algebra ChartField E]
theorem split_of_split_on_lines (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (bounded : height wordDegree f≤heightCap (f.degreeOf ordinate) wordDegree)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0)
    (x z : L) (g : Chart→Chart→E) (add : ∀ s t r, g s t+g t r=g s r)
    (v : Chart→E) (localV : ∀ s, IsIntegral (baseChart s) (v s))
    (restricted : ∀ s t, ∃ r : E, IsIntegral (overlapRing s t) r ∧
      g s t-(v s-v t)=algebraMap ChartField E (lines x z / frame 1 1 s)*r) :
    ∃ w : Chart→E, (∀ s,IsIntegral (baseChart s) (w s)) ∧ ∀ s t,g s t=w s-w t := by
  let ι:=algebraMap ChartField E
  let P:=ι (lines x z)
  have pn : P≠0 := (map_ne_zero_iff ι ι.injective).mpr (lines_ne x z)
  let h (s t:Chart):=(g s t-(v s-v t))/P
  have coc (s t r) : h s t+h t r=h s r := by
    dsimp [h]
    rw [←add_div]
    congr 1
    linear_combination add s t r
  have twist (s t) : IsIntegral (overlapRing s t) (ι (frame 1 1 s)*h s t) := by
    obtain ⟨r,hr,eq⟩:=restricted s t
    have nz := (map_ne_zero_iff ι ι.injective).mpr (frame_ne 1 1 s)
    have recover : ι (frame 1 1 s)*h s t=r := by
      dsimp only [h]; rw [eq,map_div₀]
      change ι (frame 1 1 s)*(P/ι (frame 1 1 s)*r/P)=r
      field_simp
    rwa [recover]
  obtain ⟨w,localW,diff⟩:=split_cocycle f ir lo hi bounded basis root 1 1 (by decide) (by decide) h coc twist
  refine ⟨fun s=>v s+P*w s,fun s=>(localV s).add ?_,fun s t=>?_⟩
  · have integral : IsIntegral (baseChart s) (ι (lines x z/frame 1 1 s)) :=
      isIntegral_algebraMap (x:=(⟨_, local_equation x z s⟩ : baseChart s))
    have eq : ι (lines x z / frame 1 1 s)*(ι (frame 1 1 s)*w s)=P*w s := by
      rw [map_div₀,←mul_assoc,div_mul_cancel₀ _ ((map_ne_zero_iff ι ι.injective).mpr (frame_ne _ _ _))]
    exact eq ▸ integral.mul (localW s)
  · have eq := (div_eq_iff pn).mp (diff s t)
    linear_combination eq
#print axioms split_of_split_on_lines
end Lower6960.RetainedLineRestriction

end
end Merged_R6960RetainedLineRestriction

end Merged_R6960RetainedLineRestriction

-- merged module R6960RetainedCrossingLift
section Merged_R6960RetainedCrossingLift

-- merged module R6960TwoRulings
section Merged_R6960TwoRulings
noncomputable section
set_option Elab.async false
namespace Lower6960.TwoRulings
open Polynomial
open scoped Polynomial
variable {k : Type*} [Field k]
abbrev Plane (k : Type*) [Field k] := Polynomial (Polynomial k)
theorem independent_denominators (a b : (Polynomial k)) (an : a≠0) (bn : b≠0) :
    IsRelPrime (C a : Plane k) (b.map (C : k→+*(Polynomial k))) := by
  intro d da db
  have cd := natDegree_le_of_dvd da (C_ne_zero.mpr an)
  rw [natDegree_C] at cd
  have eq := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero cd)
  rw [eq] at db ⊢
  apply isUnit_C.mpr
  have dvd := (C_dvd_iff_dvd_coeff _ _).mp db b.natDegree
  rw [coeff_map,coeff_natDegree] at dvd
  exact isUnit_of_dvd_unit dvd (isUnit_C.mpr (leadingCoeff_ne_zero.mpr bn).isUnit)
variable {E : Type*} [Field E] [Algebra (Plane k) E]
theorem affine_iff (F : Type*) [Field F] [Algebra (Plane k) F] [IsFractionRing (Plane k) F]
    [Algebra F E] [IsScalarTower (Plane k) F E] [FiniteDimensional F E] (x : E) :
    IsIntegral (Plane k) x ↔
      (∃ a:(Polynomial k), a≠0 ∧ IsIntegral (Plane k) (algebraMap (Plane k) E (C a)*x)) ∧
      (∃ b:(Polynomial k), b≠0 ∧ IsIntegral (Plane k) (algebraMap (Plane k) E (b.map (C : k→+*(Polynomial k)))*x)) := by
  constructor
  · intro h
    exact ⟨⟨1,one_ne_zero,by simpa using h⟩,⟨1,one_ne_zero,by simpa using h⟩⟩
  · rintro ⟨⟨a,an,ai⟩,⟨b,bn,bi⟩⟩
    exact NormalizedFiber.integral_of_coprime_clearings F (C_ne_zero.mpr an)
      ((Polynomial.map_ne_zero_iff C_injective).mpr bn) (independent_denominators a b an bn) x ai bi
#print axioms affine_iff
def innerDenominators (k : Type*) [Field k] : Submonoid (Plane k) :=
  (nonZeroDivisors (Polynomial k)).map (C : (Polynomial k)→+*Plane k).toMonoidHom
def outerDenominators (k : Type*) [Field k] : Submonoid (Plane k) :=
  (nonZeroDivisors (Polynomial k)).map (mapRingHom (C : k→+*(Polynomial k))).toMonoidHom
theorem two_generic_lines (F : Type*) [Field F] [Algebra (Plane k) F] [IsFractionRing (Plane k) F]
    [Algebra F E] [IsScalarTower (Plane k) F E] [FiniteDimensional F E]
    (R S : Type*) [CommRing R] [CommRing S] [Algebra (Plane k) R] [Algebra (Plane k) S]
    [IsLocalization (innerDenominators k) R] [IsLocalization (outerDenominators k) S]
    [Algebra R E] [Algebra S E] [IsScalarTower (Plane k) R E] [IsScalarTower (Plane k) S E]
    (x : E) : IsIntegral (Plane k) x ↔ IsIntegral R x ∧ IsIntegral S x := by
  constructor
  · intro i; exact ⟨i.tower_top,i.tower_top⟩
  · rintro ⟨hR,hS⟩
    apply (affine_iff F x).mpr
    obtain ⟨d,good⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (innerDenominators k) x hR
    obtain ⟨a,ha,eq⟩ := d.property
    obtain ⟨d',good'⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (outerDenominators k) x hS
    obtain ⟨b,hb,eq'⟩ := d'.property
    refine ⟨⟨a,mem_nonZeroDivisors_iff_ne_zero.mp ha,?_⟩,
      ⟨b,mem_nonZeroDivisors_iff_ne_zero.mp hb,?_⟩⟩
    · change C a=d.val at eq
      rw [eq]
      simpa only [Submonoid.smul_def,Algebra.smul_def] using good
    · change b.map C=d'.val at eq'
      rw [eq']
      simpa only [Submonoid.smul_def,Algebra.smul_def] using good'
#print axioms two_generic_lines
theorem ruling_basis (A F E : Type*) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [Field F] [Field E] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) F E),n=Module.finrank F E ∧
      ∀ x : E, IsIntegral A x ↔ ∀ i, b.repr x i∈Set.range (algebraMap A F) := by
  classical
  let S:=integralClosure A E
  have : Module.IsTorsionFree A E := .trans_faithfulSMul A F E
  have : Module.Free A S := IsIntegralClosure.module_free A F E S
  have : Module.Finite A S := IsIntegralClosure.finite A F E S
  have : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors A)) E :=
    IsIntegralClosure.isLocalization A F E S
  let j:=Module.Free.ChooseBasisIndex A S
  let a:=(Module.Free.chooseBasis A S).reindex (Fintype.equivFin j)
  let b:=Module.Basis.localizationLocalization F (nonZeroDivisors A) E a
  refine ⟨Fintype.card j,b,by simpa using (Module.finrank_eq_card_basis b).symm,?_⟩
  intro x
  constructor
  · intro hx i
    let y : S:=⟨x,hx⟩
    refine ⟨a.repr y i,?_⟩
    exact (a.localizationLocalization_repr_algebraMap F (nonZeroDivisors A) E y i).symm
  · intro all
    choose c value using all
    rw [←b.sum_repr x]
    apply IsIntegral.sum
    intro i _
    rw [←value i,Algebra.smul_def,←IsScalarTower.algebraMap_apply]
    have int : IsIntegral A (b i) := by
      rw [show b i=algebraMap S E (a i) from a.localizationLocalization_apply F (nonZeroDivisors A) E i]
      exact (a i).property
    exact isIntegral_algebraMap.mul int
#print axioms ruling_basis
end Lower6960.TwoRulings

end
end Merged_R6960TwoRulings

-- merged module R6960RetainedRestrictionTorus
section Merged_R6960RetainedRestrictionTorus

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedRestrictionTorus
open K1_14 (L)
open ChartSections (Chart overlap)
open MonicChart (ChartField)
open MonicFourChartDescent MonicChartLaurent MonicChartProbes ChartOverlapTests
open Polynomial
open scoped Polynomial Lower6960.MonicChartProbes
abbrev torus := overlapRing (false,false) (true,true)
def opposite (s : Chart) : Chart := (!s.1,!s.2)

theorem all_charts (s : Chart) : torus=overlapRing s (opposite s) := by
  ext r
  rw [show (r∈torus) ↔ _ from mem_overlap_iff (false,false) (true,true) r,mem_overlap_iff]
  rcases s with ⟨x,z⟩
  cases x <;> cases z <;> simp [overlap,opposite]

theorem to_torus (s t : Chart) : overlapRing s t≤torus := by
  intro r hr
  obtain ⟨q,hq,_⟩ := (mem_overlap_iff s t r).mp hr
  exact (mem_overlap_iff _ _ r).mpr ⟨q,hq,by simp [overlap]⟩

theorem order_mono {E : Type*} [Field E] [Algebra ChartField E] {R S : Subring ChartField}
    (le : R≤S) {y:E} (h:IsIntegral R y) : IsIntegral S y := by
  let : Algebra R S := (Subring.inclusion le).toAlgebra
  let : IsScalarTower R S E := IsScalarTower.of_algebraMap_eq (R:=R) (S:=S) (A:=E) fun _=>rfl
  exact h.tower_top

def edge (s t : Chart) : baseChart s := ⟨boundary s t,boundary_mem s t⟩

theorem edge_ne (s t : Chart) : boundary s t≠0 := by
  intro eq; have h:=boundaries_cancel s t; simp [eq] at h

theorem clear_torus {E : Type*} [Field E] [Algebra ChartField E] (s : Chart)
    (u : E) (h : IsIntegral torus u) :
    ∃ n : ℕ,IsIntegral (baseChart s) ((algebraMap ChartField E (boundary s (opposite s)))^n*u) := by
  rw [all_charts s] at h
  exact localize_integral _ _ (edge s (opposite s)) (edge_ne s (opposite s)) le_rfl u h

def linear (b : Bool) (c : L) : (Polynomial L) := if b then 1-C c*Polynomial.X else Polynomial.X-C c
private theorem at_zero (b : Bool) (c:L) (nz:c≠0) : (linear b c).eval 0≠0 := by
  cases b <;> simp [linear,nz]
private theorem lne (b : Bool) (c:L) (nz:c≠0) : linear b c≠0 := by
  intro eq; exact at_zero b c nz (by rw [eq,eval_zero])

def xcut (s : Chart) (x : L) : baseChart s := planeEquiv s ((linear s.1 x).map C)
def zcut (s : Chart) (z : L) : baseChart s := planeEquiv s (C (linear s.2 z))

theorem rel_equiv {R S : Type*} [CommRing R] [CommRing S] (e : R≃+*S) {a b : R}
    (h : IsRelPrime a b) : IsRelPrime (e a) (e b) := by
  intro d da db
  have ha : e.symm d ∣ a := by simpa using map_dvd e.symm da
  have hb : e.symm d ∣ b := by simpa using map_dvd e.symm db
  simpa using (h ha hb).map e

theorem cuts_rel (s : Chart) (x z : L) (nx:x≠0) (nz:z≠0) :
    IsRelPrime (xcut s x) (zcut s z) := rel_equiv _ (TwoRulings.independent_denominators
      (linear s.2 z) (linear s.1 x) (lne _ _ nz) (lne _ _ nx)).symm

private theorem prime_axis (a : (Polynomial L)) (hn : a.eval 0≠0) :
    IsCoprime Polynomial.X a := by
  apply (irreducible_X (R:=L)).coprime_iff_not_dvd.mpr
  intro dv
  apply hn
  exact (dvd_iff_isRoot.mp (show Polynomial.X-C (0:L) ∣ a by simpa using dv))

theorem boundary_rel (s : Chart) (x z : L) (nx : x≠0) (nz : z≠0) :
    IsRelPrime (edge s (opposite s)) (xcut s x*zcut s z) := by
  let a:=linear s.1 x
  let b:=linear s.2 z
  have an:=lne s.1 x nx
  have bn:=lne s.2 z nz
  let i:= (Polynomial.mapRingHom (C : L→+*(Polynomial L)))
  let j:= (C : (Polynomial L)→+*(Polynomial (Polynomial L)))
  have e : edge s (opposite s)=planeEquiv s (i Polynomial.X * j Polynomial.X) := by
    apply Subtype.ext
    change boundary s (opposite s)=planeMap s (i Polynomial.X*j Polynomial.X)
    rw [map_mul,show i Polynomial.X=Polynomial.X from map_X _,planeMap_abscissa]
    change _=chartCoordinate s.1 RatFunc.X * planeMap s (C Polynomial.X)
    rw [planeMap_scalar]
    rcases s with ⟨y,v⟩; cases y <;> cases v <;> simp [boundary,opposite]
  rw [e,xcut,zcut,←map_mul]
  apply rel_equiv
  have h₁ := ((prime_axis a (at_zero _ _ nx)).map i).isRelPrime
  have h₂ := ((prime_axis b (at_zero _ _ nz)).map j).isRelPrime
  exact (h₁.mul_right (TwoRulings.independent_denominators b Polynomial.X bn X_ne_zero).symm).mul_left
    ((TwoRulings.independent_denominators Polynomial.X a X_ne_zero an).mul_right h₂)

variable {E : Type*} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E]

/-- Independent divisibility by the two line equations on the torus already gives
divisibility by their product on every actual normalized overlap. -/
theorem cancel_both (s t : Chart) (x z : L) (nx:x≠0) (nz:z≠0) (u : E)
    (localProduct : IsIntegral (overlapRing s t)
      (algebraMap (baseChart s) E (xcut s x*zcut s z)*u))
    (onX : IsIntegral torus (algebraMap (baseChart s) E (xcut s x)*u))
    (onZ : IsIntegral torus (algebraMap (baseChart s) E (zcut s z)*u)) :
    IsIntegral (overlapRing s t) u := by
  let A:=baseChart s
  let : UniqueFactorizationMonoid A := (planeEquiv s).toMulEquiv.uniqueFactorizationMonoid inferInstance
  let a:=xcut s x
  let b:=zcut s z
  let g:=edge s (opposite s)
  let h:=edge s t
  have na : a≠0 := (map_ne_zero_iff _ (planeEquiv s).injective).mpr
    ((Polynomial.map_ne_zero_iff C_injective).mpr (lne s.1 x nx))
  have nb : b≠0 := (map_ne_zero_iff _ (planeEquiv s).injective).mpr (C_ne_zero.mpr (lne _ _ nz))
  obtain ⟨i,hi⟩:=clear_torus s _ onX
  obtain ⟨j,hj⟩:=clear_torus s _ onZ
  obtain ⟨m,hm⟩:=localize_integral A _ h (edge_ne s t) le_rfl _ localProduct
  let ι:=algebraMap A E
  have eqG : ι g=algebraMap ChartField E (boundary s (opposite s)) := rfl
  have eqH : ι h=algebraMap ChartField E (boundary s t) := rfl
  have extra (c:A) (v:E) (hv:IsIntegral A v) : IsIntegral A (ι c*v) := isIntegral_algebraMap.mul hv
  change IsIntegral A (ι g^i*(ι a*u)) at hi
  change IsIntegral A (ι g^j*(ι b*u)) at hj
  change IsIntegral A (ι h^m*(ι (a*b)*u)) at hm
  have bothCleared : IsIntegral A (ι (g^(i+j))*u) := by
    apply NormalizedFiber.integral_of_coprime_clearings ChartField na nb (cuts_rel s x z nx nz) _
    · change IsIntegral A (ι a*(ι (g^(i+j))*u))
      convert extra (g^j) _ hi using 1 <;> simp only [map_pow,pow_add,map_mul] <;> ring
    · change IsIntegral A (ι b*(ι (g^(i+j))*u))
      convert extra (g^i) _ hj using 1 <;> simp only [map_pow,pow_add,map_mul] <;> ring
  have ng : g≠0 := fun eq=>edge_ne s (opposite s) (congrArg Subtype.val eq)
  have clean : IsIntegral A (ι (h^m)*u) := by
    apply NormalizedFiber.integral_of_coprime_clearings ChartField (mul_ne_zero na nb) (pow_ne_zero _ ng)
      ((boundary_rel s x z nx nz).symm.pow_right) _
    · change IsIntegral A (ι (a*b)*(ι (h^m)*u))
      convert hm using 1 <;> simp only [map_pow,map_mul] <;> ring
    · convert extra (h^m) _ bothCleared using 1 <;> ring
  let T:=overlapRing s t
  have inv : (boundary s t)⁻¹∈T := ⟨1,by simp [edge_ne]⟩
  have ai : IsIntegral T (algebraMap ChartField E ((boundary s t)⁻¹)) :=
    isIntegral_algebraMap (x:=(⟨_,inv⟩:T))
  have result := (ai.pow m).mul (order_mono (into_cleared A h) clean)
  change IsIntegral T _ at result
  simpa only [map_inv₀,map_pow,eqH,←mul_assoc,←mul_pow,
    inv_mul_cancel₀ ((map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (edge_ne s t)),one_pow,one_mul] using result

#print axioms cuts_rel
#print axioms boundary_rel
#print axioms cancel_both
end Lower6960.RetainedRestrictionTorus

end
end Merged_R6960RetainedRestrictionTorus

-- merged module R6960RetainedCrossingLift
section Merged_R6960RetainedCrossingLift
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2100000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedRestrictionTorus
open K1_14 (L)
open MonicChart (ChartField)
open ChartSections (Chart)
open MonicFourChartDescent MonicChartProbes ChartOverlapTests Polynomial
open scoped Polynomial
open Lower6960.RetainedRestrictionTorus (linear)
private def cx (s : Chart) : baseChart s := planeEquiv s Polynomial.X
private def cz (s : Chart) : baseChart s := planeEquiv s (C Polynomial.X)
private def kc (s : Chart) : L→+*baseChart s := (planeEquiv s).toRingHom.comp (C.comp C)
private theorem shapeX (s : Chart) (x:L) : xcut s x =
    if s.1 then 1-kc s x*cx s else cx s-kc s x := by
  unfold xcut Lower6960.RetainedRestrictionTorus.linear
  split <;> simp [kc,cx,map_sub,map_one,map_mul]
private theorem shapeZ (s : Chart) (z:L) : zcut s z =
    if s.2 then 1-kc s z*cz s else cz s-kc s z := by
  unfold zcut Lower6960.RetainedRestrictionTorus.linear
  split <;> simp [kc,cz,map_sub,map_one,map_mul]
private theorem edge_eq (s : Chart) : edge s (opposite s)=cx s*cz s := by
  apply Subtype.ext
  change boundary s (opposite s)=planeMap s Polynomial.X*planeMap s (C Polynomial.X)
  rw [planeMap_abscissa,planeMap_scalar]
  rcases s with ⟨i,j⟩; cases i <;> cases j <;> simp [boundary,opposite]
private theorem unit_at_node {R : Type*} [CommRing R] (π : L→+*R) (b : Bool) (c : L) (nc:c≠0)
    (v:R) (zero : (if b then 1-π c*v else v-π c)=0) : IsUnit v := by
  cases b with
  | false =>
    change v-π c=0 at zero
    exact (sub_eq_zero.mp zero) ▸ nc.isUnit.map π
  | true =>
    change 1-π c*v=0 at zero
    exact ⟨⟨v,π c,(mul_comm ..).trans (sub_eq_zero.mp zero).symm,(sub_eq_zero.mp zero).symm⟩,rfl⟩
variable {E : Type*} [Field E] [Algebra ChartField E]
theorem lift_on_chart (s : Chart) (x z : L) (nx:x≠0) (nz:z≠0) (u v : E)
    (hu:IsIntegral (baseChart s) u) (hv:IsIntegral (baseChart s) v)
    (matchPoint : ∃ a b:E,IsIntegral torus a ∧ IsIntegral torus b ∧
      u-v=algebraMap (baseChart s) E (xcut s x)*a+algebraMap (baseChart s) E (zcut s z)*b) :
    ∃ y a b:E,IsIntegral (baseChart s) y ∧ IsIntegral (baseChart s) a ∧
      IsIntegral (baseChart s) b ∧ u-y=algebraMap (baseChart s) E (xcut s x)*a ∧
      y-v=algebraMap (baseChart s) E (zcut s z)*b := by
  let A:=baseChart s
  let S:=integralClosure A E
  let ι:=algebraMap A S
  let p:=ι (xcut s x)
  let q:=ι (zcut s z)
  let I:=Ideal.span ({p}:Set S)⊔Ideal.span {q}
  let π:=Ideal.Quotient.mk I
  let g:=edge s (opposite s)
  have pzero : π p=0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Submodule.mem_sup_left (Ideal.subset_span (Set.mem_singleton p)))
  have qzero : π q=0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton q)))
  have ux : IsUnit (π (ι (cx s))) := by
    apply unit_at_node (R:=↥S ⧸ I) ((π.comp ι).comp (kc s)) s.1 x nx (π (ι (cx s)))
    change π (ι (xcut s x))=0 at pzero
    rw [shapeX] at pzero
    by_cases hs:s.1=true <;> simpa [hs] using pzero
  have uz : IsUnit (π (ι (cz s))) := by
    apply unit_at_node (R:=↥S ⧸ I) ((π.comp ι).comp (kc s)) s.2 z nz (π (ι (cz s)))
    change π (ι (zcut s z))=0 at qzero
    rw [shapeZ] at qzero
    by_cases hs:s.2=true <;> simpa [hs] using qzero
  have unit : IsUnit (π (ι g)) := by
    change IsUnit (π (ι (edge s (opposite s))))
    rw [edge_eq,map_mul,map_mul]; exact ux.mul uz
  obtain ⟨a,b,ia,ib,eq⟩:=matchPoint
  obtain ⟨m,cm⟩:=clear_torus s _ ia
  obtain ⟨n,cn⟩:=clear_torus s _ ib
  let U:S:=⟨u,hu⟩
  let V:S:=⟨v,hv⟩
  let G:=algebraMap A E g
  let ca:S:=⟨G^m*a,cm⟩
  let cb:S:=⟨G^n*b,cn⟩
  have cleared : (ι g)^(m+n)*(U-V)=p*((ι g)^n*ca)+q*((ι g)^m*cb) := by
    apply Subtype.ext
    change G^(m+n)*(u-v)=algebraMap A E (xcut s x)*(G^n*(G^m*a))+
      algebraMap A E (zcut s z)*(G^m*(G^n*b))
    rw [eq,pow_add]; ring
  have zero : π (U-V)=0 := by
    apply (unit.pow (m+n)).mul_right_inj.mp
    rw [mul_zero,←map_pow,←map_mul,cleared,map_add,map_mul,pzero,zero_mul,map_mul,qzero,zero_mul,add_zero]
  obtain ⟨_,hp,_,hq,sum⟩:=Submodule.mem_sup.mp (show U-V ∈ I from Ideal.Quotient.eq_zero_iff_mem.mp zero)
  obtain ⟨a',rfl⟩:=Ideal.mem_span_singleton.mp hp
  obtain ⟨b',rfl⟩:=Ideal.mem_span_singleton.mp hq
  let y:=U-p*a'
  refine ⟨y,a',b',y.property,a'.property,b'.property,?_,?_⟩
  · exact congrArg Subtype.val (show U-y=p*a' from sub_sub_cancel ..)
  · have lift : y-V=q*b' := by
      change U-p*a'-V=q*b'
      calc _ = U-V-p*a' := by abel
           _ = _ := by rw [←sum,add_sub_cancel_left]
    exact congrArg (fun w:S=>(w:E)) lift
#print axioms lift_on_chart
end Lower6960.RetainedRestrictionTorus

end
end Merged_R6960RetainedCrossingLift

end Merged_R6960RetainedCrossingLift

end Merged6967_R6960RetainedCrossingLift

section Merged6967_R6966ProofFarRescueInvoice
set_option Elab.async false



set_option Elab.async false


noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.FarRescueGeometry
open Finset
open K1 (p)
open P1_7_4 (Mass dotQ weightedBill)
open scoped Classical BigOperators

def degreeRates : List (List ℕ) :=
  [[250703355, 257411712, 209004978, 192250090, 151344180, 146945269, 129133574, 108902784, 133169153, 98027804, 107178122, 90561210, 111399090, 159856701, 155401324, 198768055, 150749576], [250703355, 257411712, 209004978, 192250090, 151344180, 146945269, 129133574, 108902784, 133169153, 98027804, 102814332, 87000554, 107157326, 154005122, 149641067, 191596945, 150749576], [250703355, 257411712, 209004978, 192250090, 151344180, 146945269, 129133574, 108902784, 133169153, 98027804, 97959228, 82217852, 103210618, 149781012, 144393038, 187541220, 150749576], [250703355, 257411712, 209004978, 192250090, 151344180, 146945269, 129133574, 108902784, 133169153, 98027804, 88312895, 79543745, 98079150, 149905130, 145594273, 194227079, 257834722]]

def heightRates : List (List ℕ) :=
  [[1780723, 1738358, 2203815, 2424425, 3141111, 3231396, 3713473, 4463927, 3604249, 4984598, 4537835, 5415597, 4356953, 2966396, 3057840, 2327400, 3153315], [1780723, 1738358, 2203815, 2424425, 3141111, 3231396, 3713473, 4463927, 3604249, 4984598, 4735218, 5637248, 4538726, 3086497, 3176066, 2434148, 3153315], [1780723, 1738358, 2203815, 2424425, 3141111, 3231396, 3713473, 4463927, 3604249, 4984598, 4988171, 5987463, 4714571, 3173194, 3300472, 2494521, 3153315], [1780723, 1738358, 2203815, 2424425, 3141111, 3231396, 3713473, 4463927, 3604249, 4984598, 5555555, 6193762, 4981923, 3170647, 3267961, 2394996, 1735687]]

def degreeRate (rect : Fin 4) (i : ℕ) : ℕ := (degreeRates.getD rect.val []).getD i 0

def heightRate (rect : Fin 4) (i : ℕ) : ℕ := (heightRates.getD rect.val []).getD i 0

private def heightTerms (a : ℕ) : List ℚ :=
  (List.range 80).map (fun i : ℕ =>
    let g := i+1
    max 0 (1-(a : ℚ)*(g : ℚ)/((p+1 : ℕ) : ℚ))*curveUnit g)

def heightBound (a : ℕ) : ℚ := (heightTerms a).foldr max 0

private theorem le_max_fold {q : ℚ} {terms : List ℚ} (mem : q∈terms) :
    q ≤ terms.foldr max 0 := by
  induction terms with
  | nil => simp at mem
  | cons a rest ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp mem with eq | h
    · exact eq.symm ▸ le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem height_spec (a g : ℕ) (pos : 0<g) (small : g≤80) :
    max 0 (1-(a : ℚ)*g/((p+1 : ℕ) : ℚ))*curveUnit g≤heightBound a := by
  apply le_max_fold
  unfold heightTerms
  apply List.mem_map.mpr
  refine ⟨g-1,List.mem_range.mpr (by omega),?_⟩
  dsimp only
  rw [Nat.sub_add_cancel (by omega : 1≤g)]

private theorem checked_rates (rect : Fin 4) (i : Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate rect i.val : ℚ) ∧
    min (seedLimit rect) (dotQ (cutWeight rect 0 i.val) (history rect i.val)) ≤ (degreeRate rect i.val : ℚ) ∧
    heightBound (degreeRate rect i.val) ≤ (heightRate rect i.val : ℚ) := by
  fin_cases rect <;> fin_cases i <;> decide +kernel

theorem rate_spec (rect : Fin 4) {i : ℕ} (hi : i<17) :
    RateOK (degreeRate rect i) (heightRate rect i) ∧
      min (seedLimit rect) (dotQ (cutWeight rect 0 i) (history rect i)) ≤ degreeRate rect i := by
  obtain ⟨base,degree,height⟩ := checked_rates rect ⟨i,hi⟩
  exact ⟨⟨base,Nat.cast_nonneg _,fun g hp hg=>(height_spec _ g hp hg).trans height⟩,degree⟩

def lambda : ℚ := ((262144 : ℚ)/179759)*endpointDegree

def mu : ℚ := ((262144-endpointDegree : ℕ) : ℚ)/(179759-endpointDegree : ℕ)

def rankB (rect : Fin 4) : ℕ := initialCap rect 2+2

def rankJ (rect : Fin 4) : ℕ := initialCap rect 1+1

def tau : ℚ := 49/100

def pivot (rect : Fin 4) : ℚ := min (47843/5) (tau*rankB rect)

def rankWeight (rect : Fin 4) : Mass :=
  ![0,4*lambda*rankB rect*tau+mu-4*lambda*pivot rect,
    4*lambda*rankJ rect*(1-tau)+rankB rect,0]

def rankRound (rect : Fin 4) : ℚ :=
  rankWeight rect 1+2*rankWeight rect 2+2*lambda*pivot rect^2+1

def lossWeight (rect : Fin 4) (i : ℕ) : Mass :=
  fun k=>(degreeRate rect i : ℚ)*cutWeight rect 0 i k+(heightRate rect i : ℚ)*cutWeight rect 1 i k

def lossLimit (rect : Fin 4) : ℚ :=
  weightedBill 18 (beforeCuts (rankWeight rect) (lossWeight rect))
    (beforeCuts (initialMass rect) (history rect))+seedLimit rect+rankRound rect

def rescueFee (rect : Fin 4) : ℕ :=
  (lossLimit rect).ceil.toNat+(pointLimit rect).ceil.toNat+initialSeedLimit rect+initialCap rect 0

theorem rescue_fee_bound (rect : Fin 4) : rescueFee rect ≤ 121123436161956842 := by
  fin_cases rect <;> decide +kernel

theorem strict_rescue_fee (rect : Fin 4) : rescueFee rect < 121123436161956843 :=
  (rescue_fee_bound rect).trans_lt (by decide)

theorem rank_guard (rect : Fin 4) :
    rankB rect < p ∧ 0≤rankWeight rect 1 ∧ 0≤rankWeight rect 2 := by
  fin_cases rect <;> decide +kernel

#print axioms rate_spec
#print axioms strict_rescue_fee

end Lower6960.FarRescueGeometry

end
end Merged6967_R6966ProofFarRescueInvoice

section Merged6967_R6966ProofNearLedgerNormalize
set_option Elab.async false



set_option Elab.async false

namespace Research6966.NearLedger

abbrev gap : ℕ := agreement-wordDegree

theorem upper_of_finite {i : Fin 55} (h : i.val<54) : upper i=some (inCap i) := by
  have hi : i.val+1<55 := by omega
  simp only [inCap,upper,dite_eq_left hi,Option.getD_some]

theorem InBin.le_cap {i : Fin 55} {v : ℕ} (mem : InBin i v) (finite : i.val<54) :
    v ≤ inCap i := mem.2 _ (upper_of_finite finite)

private theorem side_mono {h H : ℕ} (hh : h≤H) : side h≤side H :=
  Nat.add_le_add_right (Nat.mul_le_mul_left _ hh) _

/-- Weaken an observed surface and its nodal degrees to the checked
quote, then divide out the squared interpolation gap. -/
theorem Quote.surface_of_scaled (q : Quote) (b : Band) (a : ℕ) (i j : Fin 55)
    (selected : q.method=.surface) {marks g v₀ v₁ h₀ h₁ : ℕ}
    (degree : g≤q.degreeCap b a) (x₀ : v₀≤q.axisCap i j 0) (x₁ : v₁≤q.axisCap i j 1)
    (s₀ : h₀≤seedHeight a (inCap i)) (s₁ : h₁≤seedHeight a (inCap j))
    (price : marks*gap^2≤singular a i j*gap^2+
      2*(g*side h₀*side h₁+v₀*side (yHeight a)*side h₁+v₁*side (yHeight a)*side h₀)) :
    marks≤q.wordPrice b a i j := by
  unfold Quote.wordPrice
  simp only [selected]
  apply NativeAffineLedger.floor (by decide : 0<gap^2)
  refine price.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_)) _)
  · exact Nat.mul_le_mul (Nat.mul_le_mul degree (side_mono s₀)) (side_mono s₁)
  · exact Nat.mul_le_mul (Nat.mul_le_mul_right _ x₀) (side_mono s₁)
  · exact Nat.mul_le_mul (Nat.mul_le_mul_right _ x₁) (side_mono s₀)

theorem Quote.affine_of_scaled (q : Quote) (b : Band) (i j : Fin 55)
    (selected : q.method=.affine) {marks : ℕ}
    (price : marks*gap^3≤singular 1 i j*gap^3+6*side 1*side (wordDegree*inCap i)*side (wordDegree*inCap j)) :
    marks≤q.wordPrice b 1 i j := by
  have counted := NativeAffineLedger.three_floor (n:=nodes) (a:=agreement) (d:=wordDegree)
    (c:=6) (by decide) (by decide) price
  simpa only [Quote.wordPrice,selected,seedHeight,ite_eq_left rfl,ite_true] using counted

theorem Quote.single_affine_of_scaled (q : Quote) (b : Band) (i j : Fin 55)
    (selected : q.method=.single) {marks width : ℕ}
    (cap : width≤max (inCap i) (inCap j))
    (price : marks*gap^2≤singular 1 i j*gap^2+2*side 1*side (wordDegree*width)) :
    marks≤q.wordPrice b 1 i j := by
  have counted := NativeAffineLedger.two_floor (n:=nodes) (a:=agreement) (d:=wordDegree)
    (by decide) (by decide) price
  have widths : max 1 (wordDegree*width)≤max (seedHeight 1 (inCap i)) (seedHeight 1 (inCap j)) := by
    by_cases order : inCap i ≤ inCap j
    · rw [max_eq_right order] at cap
      exact (max_le_max le_rfl (Nat.mul_le_mul_left _ cap)).trans
        (le_max_right (seedHeight 1 (inCap i)) (seedHeight 1 (inCap j)))
    · rw [max_eq_left (by omega : inCap j ≤ inCap i)] at cap
      exact (max_le_max le_rfl (Nat.mul_le_mul_left _ cap)).trans
        (le_max_left (seedHeight 1 (inCap i)) (seedHeight 1 (inCap j)))
  unfold Quote.wordPrice
  simp only [selected,yHeight,Nat.sub_self,Nat.mul_zero,Nat.zero_add,Nat.mul_one]
  exact counted.trans (Nat.add_le_add_left (Nat.div_le_div_right
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 widths))) _)

#print axioms Quote.surface_of_scaled
#print axioms Quote.affine_of_scaled
#print axioms Quote.single_affine_of_scaled
end Research6966.NearLedger

end Merged6967_R6966ProofNearLedgerNormalize

section Merged6967_R6966ProofNearLedgerWordMethods
set_option Elab.async false





set_option Elab.async false

namespace Research6966.NearLedgerWordMethods
open Polynomial Finset NearLedger
open K1 (K I p)
open K1_14 (L FX Equation atX liftPoly graphEval seedEmbedding)
open K1_14_3 (SeedField Surface)
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open NativeAffineRows (Owned seedPoint)
open scoped Polynomial Differential
attribute [local instance] GenericPhysicalCentre.physical
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 18

private theorem constant_power {R : Type*} [Field R] [Differential R] (x : R)
    (fixed : Differential.deriv x=0) (n : ℕ) : Differential.deriv (x^n)=0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ,Derivation.leibniz,fixed,ih,smul_zero,smul_zero,add_zero]

private theorem constant_pair {R : Type*} [Field R] [Differential R] (x : R) (n : ℕ)
    (fixed : Differential.deriv x=0) (i : Fin 2) :
    Differential.deriv ((![x,x^n] : Fin 2→R) i)=0 := by
  fin_cases i
  · exact fixed
  · exact constant_power x fixed n

private theorem fixed_seed (z : K) (i : Fin 2) : Differential.deriv (seedPoint z i)=0 := by
  apply constant_pair (seedEmbedding z) p _ i
  change Differential.deriv (algebraMap L[X] FX (C (algebraMap K L z)))=0
  rw [GenericPhysicalCentre.physical_poly,derivative_C,map_zero]

private abbrev m : ℕ := 2*wordDegree-1
private abbrev gap : ℕ := agreement-wordDegree
private def fee (a : ℕ) (u : Fin 2→ℕ) := (2*a-1)*(u 0+p*u 1)

private structure Rows (T : Finset K) (a : ℕ) (u : Fin 2→ℕ) where
  good : Finset K
  exceptional : T.card≤good.card+fee a u
  test : I→MvPolynomial (Fin 3) FX
  point : ↥good→Fin 3→FX
  caps : ∀ i z, (test i).degreeOf z≤Fin.cons (α:=fun _ : Fin 3 => ℕ) (yHeight a) (fun z=>m*u z) z
  enough : ∀ z, agreement≤(WordSurfaceMarks.hits (point z) test).card
  shared : ∀ x y, x≠y →
    ((WordSurfaceMarks.hits (point x) test)∩(WordSurfaceMarks.hits (point y) test)).card≤wordDegree

private theorem prepare {u deleted maxHeight} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt agreement M Γ) (sub : T⊆Γ) {parents : Finset Surface}
    {G : Pade.Row SeedField} (N : Native G) (gp : G.primitive) (nonlinear : 2≤G.graphDegree)
    (width : Fin 2→ℕ) (axes : ∀ j i z, ((N.poly.coeff j).coeff i).degreeOf z≤width z)
    (small : (2*G.graphDegree-1)*width 0<p)
    (physical : (131071:ℤ)+M.overhead≤wordDegree) (owners : Owned F T parents N) :
    Nonempty (Rows T G.graphDegree width) := by
  classical
  let val (z : K) (P : Equation) := P.eval₂ (graphEval (M.label z)) (atX (F.scalar z))
  have law z (hz : z∈T) : val z (den N)*atX (F.scalar z).derivative=val z (rhs N) := by
    obtain ⟨q,_,own,mark⟩:=owners z hz
    exact NativeGraphMarks.mark_law N gp own mark
  let bad := T.filter (fun z=>val z (den N)=0)
  let good := T\bad
  have gsub : good⊆T := sdiff_subset
  have nz (z : ↥good) : val z (den N)≠0 := fun zero =>
    (mem_sdiff.mp z.property).2 (mem_filter.mpr ⟨gsub z.property,zero⟩)
  have bad_le := NativeGraphExceptional.singular_count N gp width axes small bad M.label
    (NativeAffineRows.label_inj M).injOn (fun z=>atX (F.scalar z))
    (fun z mem=>(mem_filter.mp mem).2) (by
      intro z mem
      obtain ⟨ht,zero⟩:=mem_filter.mp mem
      have vz:=law z ht
      rw [zero,zero_mul] at vz
      exact vz.symm)
  have size : good.card+bad.card=T.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  let words (z : ↥good) := liftPoly (F.scalar z.val)
  have mark (z : ↥good) := F.mark z.val (sub (gsub z.property))
  have deg (z : ↥good) : (words z).natDegree≤wordDegree := by
    change ((F.scalar z.val).map (algebraMap K L)).natDegree≤wordDegree
    rw [natDegree_map_eq_of_injective (algebraMap K L).injective]
    rcases (mark z).scalar_degree with zero | bound
    · simp [zero]
    · change ((F.scalar z.val).natDegree:ℤ)≤131071+M.overhead at bound
      omega
  have distinct : Function.Injective words := fun x z eq => Subtype.ext
    (F.distinct (sub (gsub x.property)) (sub (gsub z.property))
      ((map_injective _ (algebraMap K L).injective) eq))
  let ξ : FX := algebraMap L[X] FX Polynomial.X
  let scalar := algebraMap L FX
  let node (i : I) := scalar (algebraMap K L (K1.node i))
  let recv (i : I) := scalar (algebraMap K L (M.word i))
  let eqn (i : I) : Equation := NonlinearMarkRows.node (den N) (rhs N) wordDegree ξ (node i) (recv i)
  let row (i : I) := OdeSurfaceBridge.coordinates (eqn i)
  let point (z : ↥good) : Fin 3→FX := Fin.cons (atX (F.scalar z.val)) (seedPoint (M.label z.val))
  have detect (z : ↥good) (i : I) :
      MvPolynomial.eval (point z) (row i)=0 ↔ ((words z).map scalar).eval (node i)=recv i := by
    rw [show MvPolynomial.eval (point z) (row i)=
       NonlinearMarkRows.evaluate (seedPoint (M.label z.val)) (atX (F.scalar z.val)) (eqn i)
       from OdeSurfaceBridge.read ..]
    have ode : val z.val (den N)*algebraMap L[X] FX (words z).derivative=val z.val (rhs N) := by
      simpa only [words,liftPoly,derivative_map,atX] using law z.val (gsub z.property)
    exact NonlinearMarkRows.detects _ (fixed_seed (M.label z.val)) _ _ (words z) wordDegree (deg z)
      (fun j hj=>K1_14_2_4_2.factorial_ne_zero (hj.trans_lt (by decide : wordDegree<p))) _ _ ode (nz z)
  have caps (i : I) :
      ∀ j, (row i).degreeOf j≤Fin.cons (α:=fun _ : Fin 3=>ℕ) (yHeight G.graphDegree) (fun z=>m*width z) j := by
    obtain ⟨da,db⟩:=NativeGraphMarks.equation_degrees N gp
    have D₁ : (rhs N).natDegree≤G.graphDegree-1+1 := by
      rw [Nat.sub_add_cancel (by omega : 1≤G.graphDegree)]
      exact db
    apply OdeSurfaceBridge.degrees (eqn i) _ _ (NonlinearMarkDegrees.node_ordinate (by omega) da D₁ ..)
    intro z l
    have A := (OdeSurfaceBridge.axis_cap (den N) z (width z)).mpr (fun j=>axes 1 j z)
    have B := (OdeSurfaceBridge.axis_cap (rhs N) z (width z)).mpr
      (fun j=>by simpa [rhs,coeff_neg] using axes 0 j z)
    exact NonlinearMarkDegrees.node_seeds A B wordDegree ξ (node i) (recv i) l
  refine ⟨⟨good,?_,row,point,caps,?_,?_⟩⟩
  · rw [←size]
    exact Nat.add_le_add_left bad_le _
  · intro z
    let b:=mark z
    apply b.bad.agreement.trans (card_le_card _)
    intro i hi
    apply WordSurfaceMarks.hit.mpr ((detect z i).mpr _)
    exact (Polynomial.eval_map_apply scalar _).trans (congrArg scalar
      ((Polynomial.eval_map_apply (algebraMap K L) _).trans (congrArg _ (b.scalar_hits i hi))))
  · exact WordSurfacePrice.word_overlap point row node
      (scalar.injective.comp ((algebraMap K L).injective.comp ProximityPrize.Benchmark.IRSProfile.domain.injective))
      recv (fun z=>(words z).map scalar) ((map_injective _ scalar.injective).comp distinct)
      wordDegree (fun z=>natDegree_map_le.trans (deg z)) detect

private def keepTwo (seed : Fin 2) : Fin 2↪Fin 3 where
  toFun := Fin.cons 0 (fun _=>seed.succ)
  inj' := by
    intro i j eq
    fin_cases i <;> fin_cases j
    · rfl
    · exact (Fin.succ_ne_zero seed eq.symm).elim
    · exact (Fin.succ_ne_zero seed eq).elim
    · rfl

private def keepOne : Fin 1↪Fin 3 :=
  ⟨fun _=>0,fun i j _=>Subsingleton.elim i j⟩

private theorem side_large (h : ℕ) :
    WordSurfacePrice.side (Fintype.card I) agreement wordDegree h≤max 1 h*(nodes-wordDegree) := by
  rw [ProximityPrize.Benchmark.IRSProfile.card_index]
  exact NativeAffineLedger.side_ratio (by decide) (by decide)

/-- The actual nonlinear slope graph with one active seed uses two
coordinates in the nodal interpolation, including the initial value. -/
theorem single {u deleted maxHeight} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt agreement M Γ) (sub : T⊆Γ) {parents : Finset Surface}
    {G : Pade.Row SeedField} (N : Native G) (gp : G.primitive) (nonlinear : 2≤G.graphDegree)
    (width : Fin 2→ℕ) (axes : ∀ j i z, ((N.poly.coeff j).coeff i).degreeOf z≤width z)
    (small : (2*G.graphDegree-1)*width 0<p)
    (active : Fin 2) (inactive : ∀ z, z≠active → width z=0)
    (physical : (131071:ℤ)+M.overhead≤wordDegree) (owners : Owned F T parents N) :
    T.card≤(2*G.graphDegree-1)*(width 0+p*width 1)+
      2*yHeight G.graphDegree*max (seedHeight G.graphDegree (width 0)) (seedHeight G.graphDegree (width 1))*
        (nodes-wordDegree)^2/gap^2 := by
  obtain ⟨q⟩:=prepare F sub N gp nonlinear width axes small physical owners
  let y:=yHeight G.graphDegree
  let h : Fin 2→ℕ := Fin.cons y (fun _=>m*width active)
  have selected (i:I) (j:Fin 2) : (q.test i).degreeOf (keepTwo active j)≤h j := by
    fin_cases j
    · exact q.caps i 0
    · exact q.caps i active.succ
  have discarded (i:I) (j:Fin 3) (out:j∉Set.range (keepTwo active)) : (q.test i).degreeOf j=0 := by
    revert out
    refine Fin.cases ?_ (fun z=>?_) j
    · intro out; exact (out ⟨0,rfl⟩).elim
    · intro out
      have ne : z≠active := fun eq=>out ⟨1,by subst z;rfl⟩
      exact Nat.eq_zero_of_le_zero (by simpa only [Fin.cons_succ,inactive z ne,Nat.mul_zero] using q.caps i z.succ)
  have count:=WordAxisPrice.two q.point q.test (keepTwo active) h agreement wordDegree
    (by decide) selected discarded q.enough q.shared
  rw [Fintype.card_coe] at count
  have hy : 1≤y:=Nat.le_add_left _ _
  have bycap := side_large y
  rw [max_eq_right hy] at bycap
  have hx : max 1 (m*width active)≤max (seedHeight G.graphDegree (width 0)) (seedHeight G.graphDegree (width 1)) := by
    have one : G.graphDegree≠1:=by omega
    fin_cases active
    · change max 1 ((2*wordDegree-1)*width 0)≤_
      simpa only [seedHeight,ite_eq_right one] using
        le_max_left (seedHeight G.graphDegree (width 0)) (seedHeight G.graphDegree (width 1))
    · change max 1 ((2*wordDegree-1)*width 1)≤_
      simpa only [seedHeight,ite_eq_right one] using
        le_max_right (seedHeight G.graphDegree (width 0)) (seedHeight G.graphDegree (width 1))
  have scaled : q.good.card*gap^2≤
      2*y*max (seedHeight G.graphDegree (width 0)) (seedHeight G.graphDegree (width 1))*(nodes-wordDegree)^2 := by
    refine count.trans ?_
    change 2*WordSurfacePrice.side (Fintype.card I) agreement wordDegree y*
      WordSurfacePrice.side (Fintype.card I) agreement wordDegree (m*width active) ≤ _
    calc
      _ ≤ 2*(y*(nodes-wordDegree))*
          (max (seedHeight G.graphDegree (width 0)) (seedHeight G.graphDegree (width 1))*(nodes-wordDegree)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ bycap)
          ((side_large _).trans (Nat.mul_le_mul_right _ hx))
      _ = _ := by ring
  have good := (Nat.le_div_iff_mul_le (by decide : 0<gap^2)).mpr scaled
  exact q.exceptional.trans ((Nat.add_le_add_right good _).trans_eq (Nat.add_comm _ _))

/-- Seed-independent nonlinear graphs use only the initial-value
coordinate. Their actual differential denominator has no exceptional labels. -/
theorem fixed {u deleted maxHeight} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt agreement M Γ) (sub : T⊆Γ) {parents : Finset Surface}
    {G : Pade.Row SeedField} (N : Native G) (gp : G.primitive) (nonlinear : 2≤G.graphDegree)
    (axes : ∀ j i z, ((N.poly.coeff j).coeff i).degreeOf z≤0)
    (physical : (131071:ℤ)+M.overhead≤wordDegree) (owners : Owned F T parents N) :
    T.card≤yHeight G.graphDegree*(nodes-wordDegree)/gap := by
  obtain ⟨q⟩:=prepare F sub N gp nonlinear (fun _=>0) axes
    (by simpa only [Nat.mul_zero] using (show (0:ℕ)<p by decide)) physical owners
  let y:=yHeight G.graphDegree
  have discarded (i:I) (j:Fin 3) (out:j∉Set.range keepOne) : (q.test i).degreeOf j=0 := by
    revert out
    refine Fin.cases ?_ (fun z _=>?_) j
    · intro out; exact (out ⟨0,rfl⟩).elim
    · exact Nat.eq_zero_of_le_zero (by simpa only [Fin.cons_succ,Nat.mul_zero] using q.caps i z.succ)
  have count:=WordAxisPrice.one q.point q.test keepOne y agreement wordDegree
    (by decide) (fun i=>q.caps i 0) discarded q.enough q.shared
  rw [Fintype.card_coe] at count
  have bycap := side_large y
  have hy : 1≤y := Nat.le_add_left _ _
  rw [max_eq_right hy] at bycap
  have good := (Nat.le_div_iff_mul_le (by decide : 0<gap)).mpr (count.trans bycap)
  have size := q.exceptional
  simp only [fee,Nat.mul_zero,Nat.add_zero] at size
  exact size.trans good

#print axioms single
#print axioms fixed
end
end Research6966.NearLedgerWordMethods

end Merged6967_R6966ProofNearLedgerWordMethods

section Merged6967_R6966ProofQuadraticHelper6966
set_option Elab.async false



set_option Elab.async false

namespace Research6966.QuadraticHelper6966
open Polynomial Finset
open K1 (I K p)
open QuadraticBudget (band budget price fee votes from_votes)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct)

noncomputable section
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 18
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 5000

/-- The low-physical-degree helper receives its paid twelve-quadrillion
word bound throughout the transition. This includes exceptional labels. -/
theorem low_count {u deleted maxHeight} {anchor:P1.ModelAt maxHeight u deleted} {Γ T:Finset K}
    (fam:P1.FamilyAt 179759 anchor Γ) (sub:T⊆Γ) {h:ℕ} (lo:2317≤h) (hi:h≤2522)
    {D:PoleData h} {Crt:CRTLift D} {N:Jet} (M:HelperPhysicalModel.Model Crt N)
    (prime:Prime N) (ns:N.natDegree=1) (quad:K1_14_2_2_2_1.jetDegree N=2)
    (width:ℕ) (sm:width≤92) (cap:∀ j i,((N.coeff j).coeff i).totalDegree≤width)
    (low:RawPhysicalDegree.weight (131071-h) (131071-h-1) M.raw<(band width).2)
    (height:anchor.overhead≤(h:ℤ))
    (nodes:∀i:I,(poleProduct D).eval (algebraMap K K1_14.L (K1.node i))≠0)
    (res:∀ γ∈T,MarkResidues D (anchor.label γ) (fam.scalar γ))
    (belongs:∀ γ∈T,jetAt N (anchor.label γ) (fam.scalar γ)=0) :
    T.card≤budget := by
  obtain ⟨hp,hl,ch,dp,gap,maxD⟩:=QuadraticBudget.numeric lo hi sm
  have height' : (131071:ℤ)+anchor.overhead≤((131071+h:ℕ):ℤ) := by
    rw [Nat.cast_add]
    exact add_le_add (le_refl (131071:ℤ)) height
  apply QuadraticBudget.from_family (length:=Fintype.card I) (char:=p)
    ProximityPrize.Benchmark.IRSProfile.card_index rfl hi sm maxD low
  exact PhysicalHelperTariff.price (a:=179759) fam sub hp hl M prime ns quad width (131071+h)
    cap ch height' le_rfl dp gap nodes res belongs

#print axioms low_count
end
end Research6966.QuadraticHelper6966

end Merged6967_R6966ProofQuadraticHelper6966
