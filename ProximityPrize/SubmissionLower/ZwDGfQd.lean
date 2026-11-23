import ProximityPrize.SubmissionLower.Zmn8gnb
set_option Elab.async false
open _root_ renaming CommRing → za6, Function.Injective → zq4, Nat.sub_add_cancel → zxt, Polynomial.C → z1z, Polynomial.X → z7y, PowerSeries → zpm
set_option maxHeartbeats 600000
namespace qaJ7jxd
noncomputable section
open Polynomial qAjZDhd
variable {k :Type} [Field k] {p:ℕ}
private theorem coeffDeriv_degree {S R:Type} [za6 S] [za6 R] [Algebra S R]
    (d:Derivation S R R) (f :R[X]) : (Lv d f).natDegree≤f.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  change d (f.coeff i)=0
  rw [coeff_eq_zero_of_natDegree_lt hi,map_zero]
private theorem negC_mul_degree {R:Type} [za6 R] (a :R) (f :R[X]) :
    ((-Polynomial.C a)*f).natDegree≤f.natDegree := by
  rw [← C_neg]
  exact natDegree_C_mul_le _ _
private theorem num_degree (M:LocalMark k p) (b:Bool) :
    (M.numerator b).natDegree≤M.g:= by
  have hs : (seedPartial M.f).natDegree≤M.g:= by
    unfold seedPartial
    exact (coeffDeriv_degree (S:=k) (R:=Physical k) seedDeriv M.f).trans M.degree.le
  have hx : (physicalPartial M.f).natDegree≤M.g:= by
    unfold physicalPartial
    exact (coeffDeriv_degree (S:=zpm k) (R:=Physical k)
      Polynomial.derivative' M.f).trans M.degree.le
  cases b
  · change ((-Polynomial.C M.r)*seedPartial M.f).natDegree≤M.g
    exact (negC_mul_degree M.r (seedPartial M.f)).trans hs
  · change ((-Polynomial.C M.r.derivative)*seedPartial M.f +
      z1z (seedDeriv M.r)*physicalPartial M.f).natDegree≤M.g
    exact (natDegree_add_le_of_le
      ((negC_mul_degree M.r.derivative (seedPartial M.f)).trans hs)
      ((natDegree_C_mul_le (seedDeriv M.r) (physicalPartial M.f)).trans hx)).trans
      (max_self _).le
theorem denom_eq [CharP k p] (M:LocalMark k p) :
    denom M=(-1)^M.g*branchPoly M.f M.g M.a := by
  have hg:0<M.g:= by have :=M.two_le; omega
  have hcast: (M.g:Physical k)≠0:= by
    intro h
    have hk : (M.g:k)=0:= by
      simpa only [map_natCast,map_zero] using
        congrArg (PowerSeries.constantCoeff.comp (Polynomial.constantCoeff :
          (zpm k)[X] →+* zpm k)) h
    exact (not_le.mpr M.tame) (Nat.le_of_dvd hg ((CharP.cast_eq_zero_iff k p _).mp hk))
  have hf0:M.f≠0:= by
    intro h
    exact hg.ne (by simpa only [h,natDegree_zero] using M.degree)
  have hd:M.f.derivative.natDegree=M.g - 1 := by
    apply le_antisymm (natDegree_derivative_le M.f |>.trans (by rw [M.degree]))
    apply le_natDegree_of_ne_zero
    rw [coeff_derivative,← Nat.cast_add_one,zxt hg]
    exact mul_ne_zero (by simpa only [← M.degree,coeff_natDegree] using
      (leadingCoeff_ne_zero.mpr hf0)) hcast
  have hl: (z7y-Polynomial.C (reference M.a)).natDegree=1 :=
    natDegree_X_sub_C _
  have h:=resultant_mul_right M.f M.f.derivative
    (z7y-Polynomial.C (reference M.a)) M.g M.degree.le
  rw [hd,hl,zxt hg,
    resultant_X_sub_C_right _ _ _ M.degree.le] at h
  simpa only [denom,LocalMark.denominator,branchPoly,mul_left_comm] using h
theorem splitMap_injective :zq4 (bL9 (k :=k)) := by
  have h₁:=IsFractionRing.injective (zpm k) (kq k)
  have h₂:=RatFunc.algebraMap_injective (kq k)
  have h₃:=(algebraMap (Generic k) (AlgebraicClosure (Generic k))).injective
  exact h₃.comp (h₂.comp (Polynomial.map_injective _ h₁))
private theorem deg_denom (M:LocalMark k p) :M.denominator.natDegree≤M.g:= by
  have hg:0<M.g:= by have :=M.two_le; omega
  unfold LocalMark.denominator
  refine natDegree_mul_le.trans ?_
  rw [natDegree_X_sub_C,← zxt hg]
  exact Nat.add_le_add_right ((natDegree_derivative_le _).trans (by rw [M.degree])) _
theorem sylvesterNumer_eval₂ {R L:Type} [za6 R] [za6 L]
    (j:R →+* L) (w:L) (f E N :R[X]) (g:ℕ) :
    (sylvesterNumer f E N g).eval₂ j w =
      (f.map j).resultant (z1z w*E.map j-N.map j) g g:= by
  let jW:R[X] →+* L:=eval₂RingHom j w
  have he :jW.comp (z1z:R →+* R[X])=j:= by
    ext z
    simp [jW]
  have hm (T:R[X]) : (T.map z1z).map jW=T.map j:= by
    rw [Polynomial.map_map,he]
  have hw:jW (z7y:R[X])=w:=eval₂_X j w
  unfold sylvesterNumer
  change jW _ = _
  rw [← resultant_map_map,Polynomial.map_sub,Polynomial.map_mul,map_C,hm,hm,hm,hw]
private theorem resultant_product {R L:Type} [za6 R] [Field L] [IsAlgClosed L]
    [Infinite L] (j:R →+* L) (hj:zq4 j) (f E N :R[X]) (g:ℕ)
    (hf :f.natDegree=g) (hE :E.natDegree≤g) (hN :N.natDegree≤g)
    (hd:j (f.resultant E g g)≠0) :
    (sylvesterNumer f E N g).map j =
      z1z (j (f.resultant E g g)) *
        (((f.map j).roots).map fun y =>
          (z7y:L[X])-Polynomial.C ((N.map j).eval y/(E.map j).eval y)).prod:= by
  classical
  let F:=f.map j
  let A:=E.map j
  let B:=N.map j
  let l:=F.leadingCoeff^g
  have hF:F.natDegree=g:=(natDegree_map_eq_of_injective hj f).trans hf
  have hs :F.Splits :=IsAlgClosed.splits _
  have hr (G:L[X]) (hG:G.natDegree≤g) :
      F.resultant G g g=l*(F.roots.map G.eval).prod:= by
    simpa only [hF,l] using resultant_eq_prod_eval F G g hG hs
  have hd' : j (f.resultant E g g)=l*(F.roots.map A.eval).prod:= by
    rw [← resultant_map_map]
    exact hr A (natDegree_map_le.trans hE)
  have hne (y :L) (hy :y∈F.roots) :A.eval y≠0:= by
    intro h
    have hz : (F.roots.map A.eval).prod=0 :=
      Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨y,hy,h⟩)
    exact hd (by rw [hd',hz,mul_zero])
  apply Polynomial.funext
  intro w
  have hleft: ((sylvesterNumer f E N g).map j).eval w =
      F.resultant (z1z w*A - B) g g:= by
    rw [eval_map]
    exact sylvesterNumer_eval₂ j w f E N g
  have hdeg: (z1z w*A - B).natDegree≤g :=
    (natDegree_sub_le_of_le ((natDegree_C_mul_le _ _).trans (natDegree_map_le.trans hE))
      (natDegree_map_le.trans hN)).trans (max_self _).le
  rw [hleft,hr _ hdeg,eval_mul,eval_C,eval_multiset_prod,Multiset.map_map,hd',mul_assoc]
  congr 1
  rw [← Multiset.prod_map_mul]
  congr 1
  apply Multiset.map_congr rfl
  intro y hy
  simp only [Function.comp_apply,eval_sub,eval_mul,eval_C,eval_X]
  change w*A.eval y - B.eval y=A.eval y*(w - B.eval y/A.eval y)
  rw [mul_sub,mul_comm w,mul_div_cancel₀ _ (hne y hy)]
theorem scaled_product (M:LocalMark k p) (b:Bool)
    (h:bL9 (denom M)≠0) :
    (Fr M b).map bL9=z1z (bL9 (denom M)) *
      (((M.f.map bL9).roots).map fun y =>
        (z7y: (AlgebraicClosure (Generic k))[X]) -
          z1z (((M.numerator b).map bL9).eval y /
            (M.denominator.map bL9).eval y)).prod :=
  resultant_product bL9 splitMap_injective M.f M.denominator (M.numerator b) _
    M.degree (deg_denom M) (num_degree M b) h
end
end qaJ7jxd
