import ProximityPrize.SubmissionLower.Zm7WGxe
import ProximityPrize.SubmissionLower.ZSLoCda
set_option Elab.async false
set_option autoImplicit true
namespace qtQA4Je
open Polynomial qWdRihc
open P5 (K)
open cu (L)
open scoped BigOperators
noncomputable section
open private zeros_le from ProximityPrize.SubmissionLower.Zm7WGxe
private theorem common_divisor {F:Type*} [Field F] {f q w:F[X]} {a :F}
    (hf :f≠0) (ha :a≠0) (hq:q≠0)
    (hw:w^2=C a*q^2*f) :
    ∃ D:F[X],D.Monic∧2*D.natDegree=f.natDegree∧D ∣f∧D ∣f.derivative := by
  have hq2 :q^2∣w^2 :=⟨C a*f,by rw [hw]; ring⟩
  obtain ⟨v,hv⟩:=(UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (by decide :2≠0)).mp hq2
  have he :v^2=C a*f := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hq)
    rw [← mul_pow,← hv,hw]
    ring
  have hfv :f=C a⁻¹*v^2 := by
    rw [he,← mul_assoc,← map_mul,inv_mul_cancel₀ ha,map_one,one_mul]
  have hv0:v≠0:= fun hz=>hf (by simp [hfv,hz])
  let D:=v*C v.leadingCoeff⁻¹
  have hDv :D ∣v :=⟨C v.leadingCoeff,by
    rw [show D = _ from rfl,mul_assoc,← map_mul,
      inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hv0),map_one,mul_one]⟩
  have hpow:v^2∣f :=⟨C a⁻¹,by rw [hfv,mul_comm]⟩
  refine ⟨D,monic_mul_leadingCoeff_inv hv0,?_,?_,?_⟩
  · rw [show D = _ from rfl,natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hv0)),
      hfv,natDegree_C_mul (inv_ne_zero ha),natDegree_pow]
  · exact hDv.trans ((dvd_pow_self _ (by decide :2≠0)).trans hpow)
  · exact hDv.trans (by simpa only [Nat.reduceSub,pow_one] using
      pow_sub_one_dvd_derivative_of_pow_dvd hpow)
private theorem mult_count {F:Type*} [Field F] (U:Finset F) {S:F[X]} (hS:S≠0)
    {d:ℕ} (hd:0<d) (hU : ∀ u∈U,((Polynomial.X:F[X]) - C u)^d∣S) :
    d*U.card≤S.natDegree := by
  classical
  have hm (u:F) (hu:u∈U) :d≤S.roots.count u:= by
    rw [count_roots]
    exact (le_rootMultiplicity_iff hS).mpr (hU u hu)
  have hsub:U⊆S.roots.toFinset := by
    intro u hu
    exact Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (hd.trans_le (hm u hu)))
  calc
    _ = ∑ u∈U,d:= by simp [Nat.mul_comm]
    _ ≤ ∑ u∈U,S.roots.count u:=Finset.sum_le_sum hm
    _ ≤ ∑ u∈S.roots.toFinset,S.roots.count u :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>Nat.zero_le _)
    _=S.roots.card:=Multiset.toFinset_sum_count_eq _
    _≤_:=card_roots' S
theorem proof :qWdRihc.c2 := by
  classical
  intro H T z hi s q R hR hm _ hsep hmark
  let U:=T.filter fun γ=>R.leadingCoeff.eval (z γ)≠0
  let V:=T.filter fun γ=>R.leadingCoeff.eval (z γ)=0
  have hpart:U.card+V.card=T.card:= by
    simpa only [U,V,not_ne_iff] using
      Finset.card_filter_add_card_filter_not (s :=T) (fun γ=>R.leadingCoeff.eval (z γ)≠0)
  have hUsub:U⊆T:=Finset.filter_subset _ _
  have hVsub:V⊆T:=Finset.filter_subset _ _
  have hV:V.card≤2*H :=(zeros_le V z (hi.mono hVsub)
    (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hm))
    (fun _ hγ=>(Finset.mem_filter.mp hγ).2)).trans (hR _)
  suffices hU:U.card≤8*H by omega
  by_cases hU:U.Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hU]
  let S:=R.resultant R.derivative
  let d:=R.natDegree/2
  have hS:S≠0:= by
    let e :=algebraMap i5 (FractionRing i5)
    have he :=IsFractionRing.injective i5 (FractionRing i5)
    have h:=resultant_ne_zero _ _ hsep
    change (R.map e).resultant (R.map e).derivative≠0 at h
    rw [derivative_map,natDegree_map_eq_of_injective he,natDegree_map_eq_of_injective he,
      resultant_map_map] at h
    exact fun hz=>h (by rw [show R.resultant R.derivative=S from rfl,hz,map_zero])
  have hdiv (γ:K) (hγ:γ∈U) :
      ∃ D:L[X],D.Monic∧2*D.natDegree=R.natDegree ∧
        D ∣specialize (z γ) R∧D ∣(specialize (z γ) R).derivative := by
    have hd' : (specialize (z γ) R).natDegree=R.natDegree :=
      natDegree_map_eq_iff.mpr (Or.inl ((Finset.mem_filter.mp hγ).2))
    have hf :specialize (z γ) R≠0:=ne_zero_of_natDegree_gt (hd' ▸ hm)
    obtain ⟨hs,hq,w,hw⟩:=hmark γ (hUsub hγ)
    simpa only [hd'] using common_divisor hf hs hq hw
  obtain ⟨γ,hγ⟩:=hU
  obtain ⟨D,_,hDm,_,_⟩:=hdiv γ hγ
  have hd:0<d:= by dsimp [d]; omega
  have hmd:2*d=R.natDegree := by dsimp [d]; omega
  have hpay (γ:K) (hγ:γ∈U) : (Polynomial.X - C (z γ))^d∣S:= by
    obtain ⟨E,hE,hEd,hR',hQ'⟩:=hdiv γ hγ
    have hdeg:E.natDegree=d:= by omega
    have hb:E.natDegree≤R.natDegree+R.derivative.natDegree := by omega
    have hQ'' : E∣R.derivative.map (evalRingHom (z γ)) := by
      simpa only [specialize,coe_mapRingHom,derivative_map] using hQ'
    rw [← hdeg]
    exact cfp R R.derivative (z γ) le_rfl le_rfl hE hb hR' hQ''
  have hsum:d*U.card≤S.natDegree := by
    rw [← Finset.card_image_of_injOn (hi.mono hUsub)]
    apply mult_count (U.image z) hS hd
    intro a ha
    obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp ha
    exact hpay γ hγ
  apply Nat.le_of_mul_le_mul_left _ hd
  refine hsum.trans ?_
  calc
    _≤R.derivative.natDegree*(2*H)+R.natDegree*(2*H) :=
      natDegree_resultant_le_of_coeff_natDegree_le _ _ _ _ _ _ hR
        (fun j=>(coeff_derivative_natDegree_le R j).trans (hR (j+1)))
    _≤R.natDegree*(2*H)+R.natDegree*(2*H) :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ ((natDegree_derivative_le R).trans
        (Nat.sub_le _ _))) _
    _=d*(8*H) := by rw [← hmd]; ring
end
end qtQA4Je
