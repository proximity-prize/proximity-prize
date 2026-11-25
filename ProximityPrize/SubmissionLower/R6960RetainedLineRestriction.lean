import ProximityPrize.SubmissionLower.R6960MarkedMatrixNorm
import ProximityPrize.SubmissionLower.R6960ChartGlobalTests
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import ProximityPrize.SubmissionLower.R6960ChartImage

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
open RetainedCompression (Curve ordinate view height heightCap MarkedBand)
open Polynomial
open K1_14 (L)
open Lower6960.MonicFourChartDescent (finite_inclusion infinity_inclusion)
private theorem frame_add (a b D : ℕ) (s : Chart) :
    frame (a+D) (b+D) s=frame a b s*frame D D s := by
  simp only [frame,pow_add]; ring
variable {E : Type*} [Field E] [Algebra ChartField E]
theorem high_twist (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<K1.p) (basis : PowerBasis ChartField E)
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
theorem common_correction (B : MarkedBand) (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<B.maxOrd) (bounded : height B.wordDegree f≤heightCap (f.degreeOf ordinate) B.wordDegree)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0)
    (a b : ℕ) (ha : 0<a) (hb : 0<b) (u : Chart→E) (compatible : Compatible a b u) :
    ∃ c : E, Correction a b u c := by
  obtain ⟨H,high⟩:=high_twist f ir lo (hi.trans B.small_E) basis root
  have large : H<K1.p^H := Nat.lt_pow_self KoalaBear.is_prime.one_lt
  have above {d : ℕ} (pos : 0<d) : H<d*K1.p^H :=
    large.trans_le (Nat.le_mul_of_pos_left _ pos)
  obtain ⟨c,hc⟩:=high _ _ (above ha) (above hb) _ (compatible_iterate a b u compatible H)
  obtain ⟨d,_,hd⟩ := descend_iterate B f ir lo hi bounded basis root a b ha u H c hc
  exact ⟨d,hd⟩
#print axioms high_twist
#print axioms common_correction
theorem split_cocycle (B : MarkedBand) (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<B.maxOrd) (bounded : height B.wordDegree f≤heightCap (f.degreeOf ordinate) B.wordDegree)
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
  obtain ⟨c,hc⟩:=common_correction B f ir lo hi bounded basis root a b ha hb u
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
open RetainedCompression (Curve ordinate view height heightCap MarkedBand)
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
theorem split_of_split_on_lines (B : MarkedBand) (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<B.maxOrd) (bounded : height B.wordDegree f≤heightCap (f.degreeOf ordinate) B.wordDegree)
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
  obtain ⟨w,localW,diff⟩:=split_cocycle B f ir lo hi bounded basis root 1 1 (by decide) (by decide) h coc twist
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
