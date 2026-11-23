import ProximityPrize.SubmissionLower.ZIAMiic
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qX9S3Pd
noncomputable section
open Finset MvPolynomial
open cu (L)
open gT (kM)
open Cu
open E7
open agN (b27)
open qBajpRb
open scoped WithZero
attribute [local instance] gRK
private theorem eval_bound {E σ:Type} [Field E] [Algebra L E] [Fintype σ]
    (w:CurvePlace L E) (u:σ→E) (f :MvPolynomial σ L) {d:ℕ}
    (hf :f.totalDegree≤d) :
    w.value (eval₂ (algebraMap L E) u f)≤WithZero.exp ((d*Tq w.value u:ℕ) :ℤ) := by
  classical
  let b:=Tq w.value u
  let M:ℤᵐ⁰:=WithZero.exp (b:ℤ)
  have hM:1≤M:=WithZero.one_le_exp_iff.mpr (Int.natCast_nonneg _)
  have hc (a :L) :w.value (algebraMap L E a)≤1 := by
    by_cases ha :a=0
    · simp [ha]
    · exact (w.on_constants a ha).le
  have hu (i:σ) :w.value (u i)≤M:= by
    apply WithZero.le_exp_of_log_le
    exact (Int.self_le_toNat _).trans (Int.ofNat_le.mpr
      (Finset.le_sup (f := fun j=>poleOrder w.value (u j)) (mem_univ i)))
  rw [eval₂_eq']
  apply w.value.map_sum_le
  intro a ha
  have h:=(le_totalDegree ha).trans hf
  calc
    _ ≤ ∏ i,M^a i:= by
      rw [map_mul,map_prod,← one_mul (∏ i,M^a i)]
      exact mul_le_mul' (hc _) (prod_le_prod fun i _=> by
        rw [map_pow]
        exact pow_le_pow_left' (hu i) _)
    _=M^a.degree := by rw [prod_pow_eq_pow_sum,← Finsupp.degree_eq_sum]
    _≤M^d:=pow_le_pow_right' hM h
    _ = _:= by rw [show M= _ from rfl,← WithZero.exp_nsmul]; simp [b]
variable {C₀:sQ} [Fact (Irreducible C₀)] {J:Ideal kM}
  {g n:ℕ} {R:wJ C₀ J g} (A:yI R n)
private theorem stock_bound (w:CurvePlace L (oO C₀)) {k j:ℕ}
    {q:CurveRing A} (hq:q∈stock A k j) :
    poleOrder w.value (incl A q) ≤
      k*Tq w.value (Wt C₀)+j*Tq w.value A.coordinate := by
  let d:=k*Tq w.value (Wt C₀)+j*Tq w.value A.coordinate
  have hb:w.value (incl A q)≤WithZero.exp (d:ℤ) := by
    refine Submodule.mul_induction_on (M:=u7 A k) (N :=tuple A j) hq ?_ ?_
    · rintro _ ⟨f,hf,rfl⟩ _ ⟨u,hu,rfl⟩
      have hf' := eval_bound w (Wt C₀) f ((mem_restrictTotalDegree _ _ _).mp hf)
      have hu' := eval_bound w A.coordinate u ((mem_restrictTotalDegree _ _ _).mp hu)
      change w.value (incl A (Yx A f*tupleMap A u))≤_
      rw [(incl A).map_mul,w.value.map_mul,Yx,tupleMap,AlgHom.comp_apply,AlgHom.comp_apply,
        incl_cls,incl_cls,ek,eval₂Hom_rename,eval₂Hom_rename]
      exact (mul_le_mul' hf' hu').trans_eq (by rw [← WithZero.exp_add,Nat.cast_add])
    · intro x y hx hy
      rw [(incl A).map_add]
      exact (w.value.map_add (incl A x) (incl A y)).trans (max_le hx hy)
  by_cases h0:incl A q=0
  · simp [h0,poleOrder]
  exact Int.toNat_le_toNat ((WithZero.log_le_iff_le_exp (w.value.ne_zero_iff.mpr h0)).mpr hb)
theorem pole_budget (hF:CurveField L (oO C₀)) {k j:ℕ}
    {q:CurveRing A} (hq:q∈stock A k j) :
    (∑ᶠ w:CurvePlace L (oO C₀),poleOrder w.value (incl A q)) ≤
      k*Gb L (oO C₀) (Wt C₀) +
        j*Gb L (oO C₀) A.coordinate := by
  have hdiv :=principal hF
  let s (w:CurvePlace L (oO C₀)) :=Tq w.value (Wt C₀)
  let t (w:CurvePlace L (oO C₀)) :=Tq w.value A.coordinate
  have hs :s.HasFiniteSupport:=b27 hdiv _
  have ht:t.HasFiniteSupport:=b27 hdiv _
  have hks : (fun w=>k*s w).HasFiniteSupport:=Function.HasFiniteSupport.mul_right _ hs
  have hjt: (fun w=>j*t w).HasFiniteSupport:=Function.HasFiniteSupport.mul_right _ ht
  calc
    _ ≤ ∑ᶠ w,(k*s w+j*t w) :=
      finsum_le_finsum (hdiv _).1 (hks.add hjt) fun w=>stock_bound A w hq
    _ = _:= by
      rw [finsum_add_distrib hks hjt,← mul_finsum' s k hs,← mul_finsum' t j ht]
      rfl
end
end qX9S3Pd
