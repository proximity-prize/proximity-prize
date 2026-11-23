import ProximityPrize.SubmissionLower.KoalaRawNodes
import ProximityPrize.SubmissionLower.KoalaRootSurface
import ProximityPrize.SubmissionLower.KoalaIncidence

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace SplitCut.RawCount
noncomputable section
open MvPolynomial SplitCut.BoxDegree
open P1 (K I node)
open K1_14 (FX)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten)
open HighCore82258Upper (Input ResidueLift Factors quotientNumerator componentMarks)
open P1_7_3 (persistentNodes hits_persistent)
open HighCore82258Upper_3_3 (prefixLength FixedWeights)
open HighCore82258 (FixedWord agreement degreeAt quotientOrder scale muNum)
open HighCore82258_5 (nodeVelocity)
open scoped BigOperators

abbrev firstDegree (J:Input) (k:ℕ):=2*quotientOrder J.lo+1+k
abbrev weight (J:Input) (k:ℕ):=2*nodeVelocity J+muNum J.hi*k
abbrev rootDegree (J : Input) (v w : ℕ) :=
  2*(J.e*max 1 v*max 1 w+v*(J.e-1)*max 1 w+w*(J.e-1)*max 1 v)

private theorem diagonal_lift {J : Input} {v w k u : ℕ} (hk : 0<k)
    (hv:2*J.hi≤k*max 1 v) (hw:2*J.hi≤k*max 1 w) {f:Biform}
    (hf:f ∈ space FX (1+u*(J.e-1)) (u*v+2*J.w) (u*w+2*J.w)) :
    ∃ p:MvPolynomial (exps (J.e-1) (max 1 v) (max 1 w)) FX,
    proj FX _ _ _ p=f ∧ p.totalDegree≤u+k:=by
  have he:0<J.e-1:=by have hh:3≤J.e:=J.sheets; omega
  have hk' : 1≤k*(J.e-1):=Nat.mul_pos hk he
  have hhi:=Nat.mul_le_mul_left 2 J.upper
  apply lift_box
  apply BoxDegree.mono (a:=1+u*(J.e-1)) (b:=u*v+2*J.w) (c:=u*w+2*J.w) _ _ _ hf
  · rw [Nat.mul_add]; nlinarith only [hk']
  · rw [Nat.mul_add, Nat.mul_comm (max 1 v) u, Nat.mul_comm (max 1 v) k]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (le_max_right _ _)) (hhi.trans hv)
  · rw [Nat.mul_add, Nat.mul_comm (max 1 w) u, Nat.mul_comm (max 1 w) k]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (le_max_right _ _)) (hhi.trans hw)

private theorem lift_eval {J : Input} {a b c : ℕ} {f : Biform}
    {p:MvPolynomial (exps a b c) FX} (hp:proj FX a b c p=f) (γ:K) :
    aeval (RootSurface.liftPoint a b c J γ) p=Raw.ev J γ f:=by
  rw [aeval_monomialPoint,hp]
  rfl

private theorem marked_curve (J : Input) (B : ResidueLift J) {v w k : ℕ} (hk : 0<k)
    (hv:2*J.hi≤k*max 1 v) (hw:2*J.hi≤k*max 1 w)
    (hf:flatten J.f ∈ space FX J.e v w)
    (hword:FixedWord J.model.word J.marks J.family.scalar (degreeAt J.hi))
    (hd:degreeAt J.hi < agreement)
    {Q:Ideal (MvPolynomial (exps (J.e-1) (max 1 v) (max 1 w)) FX)} [hQ:Q.IsPrime]
    (hQd:(affineHilbertPolynomial Q).natDegree=1)
    (T:Finset K) (hT:T ⊆ J.marks)
    (hon : ∀ γ ∈ T,RootSurface.liftPoint (J.e-1) (max 1 v) (max 1 w) J γ ∈ zeroLocus FX Q) :
    (scale J.hi:ℚ)*T.card≤(weight J k:ℚ)*affineDegree Q:=by
  classical
  obtain ⟨δ,hδ,heδ⟩:=PointCount.curve_degree_nat hQ.ne_top hQd
  rw [heδ]
  suffices hn:scale J.hi*T.card≤weight J k*δ by exact_mod_cast hn
  let hwT : FixedWord J.model.word T J.family.scalar (degreeAt J.hi) :=
    ⟨hword.distinct.mono hT,fun γ hγ => hword.degree γ (hT hγ),fun γ hγ => hword.hits γ (hT hγ)⟩
  apply Incidence.curve J hwT hd hk hδ
  intro x hex
  let sites:=persistentNodes J.model.word T J.family.scalar
  let r:=J.ell-sites.card
  obtain ⟨b,a,W⟩:=HighCore82258Upper_3_3_2.proof J sites x
  obtain ⟨p,hp,hpd⟩:=diagonal_lift hk hv hw (Raw.node_fit B sites x b a hf)
  have hnode (γ : K) (hγ : γ ∈ T) :
      aeval (RootSurface.liftPoint (J.e-1) (max 1 v) (max 1 w) J γ) p = 0 ↔
        (J.family.scalar γ).eval (node x)=J.model.word x:=by
    rw [lift_eval hp]
    exact Raw.node_eval B sites x b a W (hT hγ) (fun i hi => hits_persistent hγ hi)
  obtain ⟨η,hη,hnη⟩:=hex
  have hnon:p ∉ Q:=fun h => hnη ((hnode _ hη).mp (hon _ hη p h))
  have ha:0<J.e-1:=by have hh:3≤J.e:=J.sheets; omega
  have hb:0 < max 1 v:=lt_of_lt_of_le (by decide:0<1) (le_max_left _ _)
  have hc:0 < max 1 w:=lt_of_lt_of_le (by decide:0<1) (le_max_left _ _)
  let U:=T.filter (fun γ => (J.family.scalar γ).eval (node x)=J.model.word x)
  have hpd' : p.totalDegree≤2*r+k:=hpd.trans (Nat.add_le_add_right (Nat.sub_le _ _) _)
  have H := PointCount.cut_points hQd hnon hpd' U (RootSurface.injective ha hb hc J).injOn
    (fun γ hγ => hon γ (Finset.mem_filter.mp hγ).1)
    (fun γ hγ => (hnode γ (Finset.mem_filter.mp hγ).1).mpr (Finset.mem_filter.mp hγ).2)
  rw [heδ] at H
  exact_mod_cast H

/-- Count of all regular labels on the proper factor, with independently padded seed axes. -/
theorem proper_count (J : Input) (B : ResidueLift J) (D : Factors J B) (v w k : ℕ) (hk : 0<k)
    (hv:2*J.hi≤k*max 1 v) (hw:2*J.hi≤k*max 1 w)
    (hdeg : ∀ j,(J.f.coeff j).degreeOf 0≤v ∧ (J.f.coeff j).degreeOf 1≤w)
    (hword:FixedWord J.model.word J.marks J.family.scalar (degreeAt J.hi))
    (hd:degreeAt J.hi < agreement) :
    scale J.hi*(componentMarks J D.proper).card ≤
      rootDegree J v w*firstDegree J k*weight J k:=by
  classical
  let a:=J.e-1
  let b:=max 1 v
  let c:=max 1 w
  let y:=RootSurface.liftPoint a b c J
  let G:=RootSurface.rootI D a b c
  let T:=componentMarks J D.proper
  have ha:0<a:=by have hh:3≤J.e:=J.sheets; dsimp [a]; omega
  have hb:0<b:=lt_of_lt_of_le (by decide:0<1) (le_max_left _ _)
  have hc:0<c:=lt_of_lt_of_le (by decide:0<1) (le_max_left _ _)
  have hf:=Raw.root (f:=J.f) le_rfl hdeg
  have hpfit:=RootSurface.proper_fit D hf
  have hnon : flatten D.proper ≠ 0 := by
    simpa only [flatten,map_ne_zero_iff _ (optionEquivLeft FX (Fin 2)).symm.injective] using
      HighCore82258Upper_3_2.proper_ne_zero D
  have hsur:=BoxDegree.surfaces ha hb hc hnon hpfit
  change ∑ P ∈ G.minimalPrimesFinset,affineDegree P≤(rootDegree J v w:ℚ) at hsur
  obtain ⟨p,hp,hpd⟩:=diagonal_lift hk hv hw (Raw.num B hf (J.ell+1))
  have hell:J.ell≤quotientOrder J.lo:=Nat.sub_le_sub_left J.lower _
  have hpd' : p.totalDegree ≤ firstDegree J k := by
    dsimp only [firstDegree]
    omega
  have hT (γ : K) (hγ : γ ∈ T) : y γ ∈ zeroLocus FX G :=
    RootSurface.mark_on_root D (HighCore82258Upper.mem_componentMarks.mp hγ).2
  have hcut (γ : K) (hγ : γ ∈ T) : aeval (y γ) p = 0 := by
    rw [lift_eval hp]
    have hh:=D.cutoff_at_marks γ (HighCore82258Upper.mem_componentMarks.mp hγ).1
    change K1_14.atMark _ _ _=0 at hh
    rw [← K1_14_6_1.eval_flatten] at hh
    simpa only [HighCore82258Upper.cutoff,flatten,AlgEquiv.symm_apply_apply] using hh
  have hcomp (P : Ideal (MvPolynomial (exps a b c) FX)) (hP : P ∈ G.minimalPrimesFinset) :
      (scale J.hi:ℚ)*(T.filter (fun γ => y γ ∈ zeroLocus FX P)).card ≤
        ((weight J k:ℚ)*firstDegree J k)*affineDegree P:=by
    let U:=T.filter (fun γ => y γ ∈ zeroLocus FX P)
    have hmin:=Ideal.mem_minimalPrimesFinset.mp hP
    have:P.IsPrime:=hmin.isPrime
    have hnd:=RootSurface.cutoff_proper D hp hmin
    have hdim:=RootSurface.minimal_dimension ha hb hc hnon hmin
    let I' := P ⊔ Ideal.span {p}
    have hu (γ : K) (hγ : γ ∈ U) : y γ ∈ zeroLocus FX I' := by
      have hγ' := Finset.mem_filter.mp hγ
      have h₁:P≤RingHom.ker (aeval (R:=FX) (y γ)):=fun f hf => RingHom.mem_ker.mpr (hγ'.2 f hf)
      have h₂ : Ideal.span {p} ≤ RingHom.ker (aeval (R:=FX) (y γ)) :=
        (Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr (hcut γ hγ'.1))
      exact fun f h => RingHom.mem_ker.mp (sup_le h₁ h₂ h)
    have hh := Incidence.weighted_cover I' U y hu (scale J.hi) (weight J k) (by positivity)
      (fun Q hQ => by
        have hm:=Ideal.mem_minimalPrimesFinset.mp hQ
        have:Q.IsPrime:=hm.isPrime
        have hqd:=principalCut_natDegree_affineHilbertPolynomial_add_one hnd hm
        apply marked_curve J B hk hv hw hf hword hd (by omega)
        · exact fun _ hγ => (HighCore82258Upper.mem_componentMarks.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hγ).1).1).1
        · exact fun _ hγ => (Finset.mem_filter.mp hγ).2)
    have hbez:=principalCut_sum_affineDegree_minimalPrimes_le hnd hpd'
    calc
      _≤_:=hh
      _≤_:=(mul_le_mul_of_nonneg_left hbez (Nat.cast_nonneg (weight J k))).trans_eq (by ring)
  have HH := Incidence.weighted_cover G T y hT (scale J.hi) ((weight J k:ℚ)*firstDegree J k)
    (by positivity) hcomp
  have H2:=HH.trans (mul_le_mul_of_nonneg_left hsur (by positivity))
  rw [mul_comm (weight J k:ℚ) _,mul_comm _ (rootDegree J v w:ℚ)] at H2
  exact_mod_cast (by simpa only [← mul_assoc] using H2 :
    (scale J.hi:ℚ)*T.card≤(rootDegree J v w:ℚ)*firstDegree J k*weight J k)

end
end SplitCut.RawCount
#print axioms SplitCut.RawCount.proper_count
