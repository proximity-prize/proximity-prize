import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ActualPlanePositiveOrder
import ProximityPrize.SubmissionLower.BCHKSSparseResultantDegree
namespace ProximityPrize.SubmissionLower.ActualPlaneJointProjection
open Polynomial Polynomial.Bivariate
open ActualCurveCoordinateField ActualCurveRationalProjection TrivariateRationalCollection
open ActualPlaneCoordinateKernel ActualPlaneCoordinateCaps
open ActualPlanePositiveOrder
noncomputable section
variable {A:Type} [Field A]
theorem bivariateEquiv_coeff_natDegree_le_of_support
    (f:MvPolynomial (Fin 2) A) (height:ℕ → ℕ)
    (hsupport:∀ d∈f.support,d 1 ≤ height (d 0)) (i:ℕ):
    ((bivariateEquiv A f).coeff i).natDegree ≤ height i:=by
  rw [show (bivariateEquiv A f).coeff i=
      MvPolynomial.uniqueAlgEquiv A (Fin 1)
        ((MvPolynomial.finSuccEquiv A 1 f).coeff i) by
    simp [bivariateEquiv]]
  apply (uniqueAlgEquiv_natDegree_le A _).trans
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have hs:=hsupport (d.cons i)
    (MvPolynomial.mem_support_coeff_finSuccEquiv.mp hd)
  simpa only [show (1:Fin 2)=(0:Fin 1).succ by decide,
    Finsupp.cons_succ,Finsupp.cons_zero] using hs
theorem bivariateEquiv_totalDegree_le_of_support
    (f:MvPolynomial (Fin 2) A) (cap:ℕ)
    (hsupport:∀ d∈f.support,d 0+d 1 ≤ cap):
    totalDegree (bivariateEquiv A f) ≤ cap:=by
  classical
  have houter:f.degreeOf 0 ≤ cap:=by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    exact (Nat.le_add_right (d 0) (d 1)).trans (hsupport d hd)
  unfold totalDegree
  apply Finset.sup_le
  intro i hi
  have hiCap:i ≤ cap:=by
    exact (Polynomial.le_natDegree_of_mem_supp i hi).trans
      ((bivariateEquiv_natDegree A f).trans_le houter)
  have hcoeff:((bivariateEquiv A f).coeff i).natDegree ≤ cap-i:=by
    apply bivariateEquiv_coeff_natDegree_le_of_support f (fun j => cap-j)
    intro d hd
    have hs:=hsupport d hd
    omega
  omega
variable (K:Type) [Field K]
theorem planeMap_coeff_natDegree_le_of_rational_support
    (order:Fin 3 ≃ Fin 3) (F:Original K) (height:ℕ → ℕ)
    (hsupport:∀ d∈(rationalMap K order F).support,
      d 1 ≤ height (d 0)) (i:ℕ):
    ((planeMap K order F).coeff i).natDegree ≤ height i:=by
  exact bivariateEquiv_coeff_natDegree_le_of_support
    (rationalMap K order F) height hsupport i
theorem planeMap_totalDegree_le_of_rational_support
    (order:Fin 3 ≃ Fin 3) (F:Original K) (cap:ℕ)
    (hsupport:∀ d∈(rationalMap K order F).support,
      d 0+d 1 ≤ cap):
    totalDegree (planeMap K order F) ≤ cap:=by
  exact bivariateEquiv_totalDegree_le_of_support
    (rationalMap K order F) cap hsupport
theorem rationalMap_joint_support_of_original
    (order:Fin 3 ≃ Fin 3) (F:Original K) (cap:ℕ)
    (hsupport:∀ d∈F.support,
      d (order 1)+d (order 2) ≤ cap):
    ∀ e∈(rationalMap K order F).support,e 0+e 1 ≤ cap:=by
  classical
  intro e he
  rw [rationalMap_eq_firstMap] at he
  obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp
    (support_firstMap_subset K
      (algebraMap (Polynomial K) (RatFunc K))
      (MvPolynomial.rename order.symm F) he)
  rw [MvPolynomial.support_rename_of_injective order.symm.injective] at hd
  obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hd
  simpa only [Finsupp.tail_apply,Finsupp.mapDomain_equiv_apply,
    Equiv.symm_symm,
    show (0:Fin 2).succ=(1:Fin 3) by decide,
    show (1:Fin 2).succ=(2:Fin 3) by decide] using hsupport u hu
theorem original_joint_support_to_rationalMap
    (F:Original K) (cap:ℕ)
    (hsupport:∀ d∈F.support,d 0+d 2 ≤ cap):
    ∀ e∈(rationalMap K (Equiv.swap 0 1) F).support,
      e 0+e 1 ≤ cap:=by
  apply rationalMap_joint_support_of_original K (Equiv.swap 0 1) F cap
  intro d hd
  simpa [Equiv.swap_apply_def] using hsupport d hd
theorem ordinary_resultant_natDegree_le_totalDegree
    (B H:A[X][Y]) (n mCap totalB totalH cap:ℕ)
    (hHne:H≠0) (hBouter:B.natDegree ≤ n)
    (hHouter:H.natDegree ≤ mCap)
    (hBtotal:totalDegree B ≤ totalB)
    (hHtotal:totalDegree H ≤ totalH)
    (hbudget:∀ m,m ≤ mCap →
      m*totalB+n*totalH-m*n ≤ cap):
    (Polynomial.resultant B H).natDegree ≤ cap:=by
  by_cases hres:Polynomial.resultant B H=0
  · simp [hres]
  · have hfixed:=bivariate_resultant_natDegree_le_totalDegree
      B H n H.natDegree
    have hdegreeCap:
        H.natDegree*totalDegree B+n*totalDegree H-H.natDegree*n ≤
          H.natDegree*totalB+n*totalH-H.natDegree*n:=by
      exact Nat.sub_le_sub_right
        (Nat.add_le_add (Nat.mul_le_mul_left H.natDegree hBtotal)
          (Nat.mul_le_mul_left n hHtotal)) _
    have hfixedCap:
        (Polynomial.resultant B H n H.natDegree).natDegree ≤ cap:=
      hfixed.trans (hdegreeCap.trans (hbudget H.natDegree hHouter))
    have hcoeff:H.coeff H.natDegree≠0:=by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hHne
    let factor:A[X]:=
      (-1)^(H.natDegree*(n-B.natDegree))*
        H.coeff H.natDegree^(n-B.natDegree)
    have hfactor:factor≠0:=by
      apply _root_.mul_ne_zero
      · exact pow_ne_zero _ (by norm_num)
      · exact pow_ne_zero _ hcoeff
    have hpad:=Polynomial.resultant_add_left_deg
      (f:=B) (g:=H) (m:=B.natDegree)
      (k:=n-B.natDegree) (n:=H.natDegree) le_rfl
    have hsum:B.natDegree+(n-B.natDegree)=n:=
      Nat.add_sub_of_le hBouter
    rw [hsum] at hpad
    change Polynomial.resultant B H n H.natDegree=
      factor*Polynomial.resultant B H at hpad
    calc
      (Polynomial.resultant B H).natDegree ≤
          (factor*Polynomial.resultant B H).natDegree:=by
        rw [Polynomial.natDegree_mul hfactor hres]
        omega
      _=(Polynomial.resultant B H n H.natDegree).natDegree:=by rw [hpad]
      _ ≤ cap:=hfixedCap
theorem planeMap_trapezoid_resultant_natDegree_le
    (order:Fin 3 ≃ Fin 3) (G T:Original K)
    (n mCap totalG totalT cap:ℕ) (hTne:T≠0)
    (hGouter:(planeMap K order G).natDegree ≤ n)
    (hTouter:(planeMap K order T).natDegree ≤ mCap)
    (hGsupport:∀ d∈(rationalMap K order G).support,
      d 0+d 1 ≤ totalG)
    (hTsupport:∀ d∈(rationalMap K order T).support,
      d 0+d 1 ≤ totalT)
    (hbudget:∀ m,m ≤ mCap →
      m*totalG+n*totalT-m*n ≤ cap):
    (Polynomial.resultant (planeMap K order G)
      (planeMap K order T)).natDegree ≤ cap:=by
  apply ordinary_resultant_natDegree_le_totalDegree
    (planeMap K order G) (planeMap K order T)
      n mCap totalG totalT cap
  · intro hzero
    apply hTne
    apply planeMap_injective K order
    simpa only [map_zero] using hzero
  · exact hGouter
  · exact hTouter
  · exact planeMap_totalDegree_le_of_rational_support
      K order G totalG hGsupport
  · exact planeMap_totalDegree_le_of_rational_support
      K order T totalT hTsupport
  · exact hbudget
theorem planeMap_corner_resultant_natDegree_le
    (order:Fin 3 ≃ Fin 3) (G T:Original K) (k:ℕ) (hk:1 ≤ k)
    (hTne:T≠0)
    (hGouter:(planeMap K order G).natDegree ≤ 25)
    (hTouter:(planeMap K order T).natDegree ≤ 25*k+1)
    (hGsupport:∀ d∈(rationalMap K order G).support,
      d 1 ≤ CornerStaircase.surfaceHeight (d 0))
    (hTsupport:∀ d∈(rationalMap K order T).support,
      d 1 ≤ CornerStaircase.tailHeight k (d 0)):
    (Polynomial.resultant (planeMap K order G) (planeMap K order T)).natDegree ≤
      8127*k+178:=by
  apply CornerStaircase.ordinary_resultant_natDegree_le
    (planeMap K order G) (planeMap K order T) k hk
  · intro hzero
    apply hTne
    apply planeMap_injective K order
    simpa only [map_zero] using hzero
  · exact hGouter
  · exact hTouter
  · exact planeMap_coeff_natDegree_le_of_rational_support
      K order G CornerStaircase.surfaceHeight hGsupport
  · exact planeMap_coeff_natDegree_le_of_rational_support
      K order T (CornerStaircase.tailHeight k) hTsupport
theorem swapped_planeMap_degreeX_le_outer_natDegree
    (order:Fin 3 ≃ Fin 3) (F:Original K):
    degreeX (planeMap K (swapOtherOrder order) F) ≤
      (planeMap K order F).natDegree:=by
  calc
    degreeX (planeMap K (swapOtherOrder order) F) ≤
        (rationalMap K (swapOtherOrder order) F).degreeOf 1:=
      bivariateEquiv_degreeX_le (RatFunc K)
        (rationalMap K (swapOtherOrder order) F)
    _=(rationalMap K order F).degreeOf 0:=by
      rw [rationalMap_swapOtherOrder]
      change (MvPolynomial.rename (Equiv.swap (0:Fin 2) 1)
        (rationalMap K order F)).degreeOf 1=_
      simpa only [Equiv.swap_apply_left] using
        (MvPolynomial.degreeOf_rename_of_injective
          (p:=rationalMap K order F) (Equiv.swap (0:Fin 2) 1).injective
          (0:Fin 2))
    _=(planeMap K order F).natDegree:=by
      exact (bivariateEquiv_natDegree (RatFunc K)
        (rationalMap K order F)).symm
theorem swapped_resultant_natDegree_le_of_outer_zero
    (order:Fin 3 ≃ Fin 3) (G T:Original K) (gOuter tInner:ℕ)
    (hzero:(planeMap K order G).natDegree=0)
    (hGouter:(planeMap K (swapOtherOrder order) G).natDegree ≤ gOuter)
    (hTinner:degreeX (planeMap K (swapOtherOrder order) T) ≤ tInner):
    (Polynomial.resultant (planeMap K (swapOtherOrder order) G)
      (planeMap K (swapOtherOrder order) T)).natDegree ≤ gOuter*tInner:=by
  have hGinner:degreeX (planeMap K (swapOtherOrder order) G)=0:=by
    apply Nat.eq_zero_of_le_zero
    exact (swapped_planeMap_degreeX_le_outer_natDegree K order G).trans_eq hzero
  have hres:=bivariate_resultant_natDegree_le
    (planeMap K (swapOtherOrder order) G)
    (planeMap K (swapOtherOrder order) T)
    (planeMap K (swapOtherOrder order) G).natDegree
    (planeMap K (swapOtherOrder order) T).natDegree
  rw [hGinner,mul_zero,zero_add] at hres
  exact hres.trans (Nat.mul_le_mul hGouter hTinner)
theorem exists_positive_joint_characteristic_order
    (order:Fin 3 ≃ Fin 3) (P:Ideal (Original K)) [P.IsPrime]
    (G T:Original K) (p n mCap totalG totalT cap gOuter tInner:ℕ)
    (hG:Irreducible G) (hGmem:G∈P)
    (ht:Transcendental K (coordinate K P (order 0)))
    (hTne:T≠0)
    (hGouter:(planeMap K order G).natDegree ≤ n)
    (hTouter:(planeMap K order T).natDegree ≤ mCap)
    (hGsupport:∀ d∈(rationalMap K order G).support,
      d 0+d 1 ≤ totalG)
    (hTsupport:∀ d∈(rationalMap K order T).support,
      d 0+d 1 ≤ totalT)
    (hGswapOuter:(planeMap K (swapOtherOrder order) G).natDegree ≤ gOuter)
    (hTswapInner:degreeX (planeMap K (swapOtherOrder order) T) ≤ tInner)
    (hnp:n < p) (hgOuterP:gOuter < p)
    (hcapP:cap < p) (hswapP:gOuter*tInner < p)
    (hbudget:∀ m,m ≤ mCap →
      m*totalG+n*totalT-m*n ≤ cap):
    ∃ order':Fin 3 ≃ Fin 3,
      (order'=order∨order'=swapOtherOrder order)∧
      order' 0=order 0∧
      originalMixedDegree K order' G T=originalMixedDegree K order G T∧
      0 < (planeMap K order' G).natDegree∧
      (planeMap K order' G).natDegree < p∧
      (Polynomial.resultant (planeMap K order' G)
        (planeMap K order' T)).natDegree < p:=by
  by_cases hpositive:0 < (planeMap K order G).natDegree
  · refine ⟨order,Or.inl rfl,rfl,rfl,hpositive,
      hGouter.trans_lt hnp,?_⟩
    exact (planeMap_trapezoid_resultant_natDegree_le K order G T
      n mCap totalG totalT cap hTne hGouter hTouter hGsupport hTsupport
      hbudget).trans_lt hcapP
  · have hzero:(planeMap K order G).natDegree=0:=
      Nat.eq_zero_of_not_pos hpositive
    obtain ⟨order',hchoice,_hbase,hpos⟩:=
      exists_positive_outer_order K order P G hG hGmem ht
    have hswapPos:0 < (planeMap K (swapOtherOrder order) G).natDegree:=by
      rcases hchoice with hsame | hswap
      · subst order'
        exact (hpositive hpos).elim
      · subst order'
        exact hpos
    refine ⟨swapOtherOrder order,Or.inr rfl,swapOtherOrder_zero order,
      originalMixedDegree_swap K order G T,hswapPos,
      hGswapOuter.trans_lt hgOuterP,?_⟩
    exact (swapped_resultant_natDegree_le_of_outer_zero K order G T
      gOuter tInner hzero hGswapOuter hTswapInner).trans_lt hswapP
theorem first_6463_trapezoid_budget (m:ℕ) (hm:m ≤ 6553601):
    m*175+25*45875201-m*25 ≤ 2129920175:=by
  omega
theorem agreement_6463_trapezoid_budget (m:ℕ) (hm:m ≤ 6553551):
    m*175+25*45874851-m*25 ≤ 2129903925:=by
  omega
theorem first_6463_trapezoid_cap_below_characteristic:
    2129920175 < 2130706433:=by norm_num
theorem agreement_6463_trapezoid_cap_below_characteristic:
    2129903925 < 2130706433:=by norm_num
theorem swapped_6463_cap_below_characteristic:
    175*6553601 < 2130706433:=by norm_num
theorem first_6464_sharpY_trapezoid_budget (m:ℕ) (hm:m ≤ 6422529):
    m*176+25*46137345-m*25 ≤ 2123235504:=by
  omega
theorem agreement_6464_sharpY_trapezoid_budget (m:ℕ) (hm:m ≤ 6422480):
    m*176+25*46136993-m*25 ≤ 2123219305:=by
  omega
theorem first_6464_sharpY_trapezoid_cap_below_characteristic:
    2123235504 < 2130706433:=by norm_num
theorem agreement_6464_sharpY_trapezoid_cap_below_characteristic:
    2123219305 < 2130706433:=by norm_num
theorem swapped_6464_sharpY_cap_below_characteristic:
    176*6422529 < 2130706433:=by norm_num
theorem swapped_6464_cap_below_characteristic:
    178*(25*262144+1) < 2130706433:=by
  norm_num
theorem exists_positive_sparse_characteristic_order
    (order:Fin 3 ≃ Fin 3) (P:Ideal (Original K)) [P.IsPrime]
    (G T:Original K) (p k gOuter tInner:ℕ)
    (hG:Irreducible G) (hGmem:G∈P)
    (ht:Transcendental K (coordinate K P (order 0)))
    (hTne:T≠0) (hk:1 ≤ k)
    (hGouter:(planeMap K order G).natDegree ≤ 25)
    (hTouter:(planeMap K order T).natDegree ≤ 25*k+1)
    (hGsupport:∀ d∈(rationalMap K order G).support,
      d 1 ≤ CornerStaircase.surfaceHeight (d 0))
    (hTsupport:∀ d∈(rationalMap K order T).support,
      d 1 ≤ CornerStaircase.tailHeight k (d 0))
    (hGswapOuter:(planeMap K (swapOtherOrder order) G).natDegree ≤ gOuter)
    (hTswapInner:degreeX (planeMap K (swapOtherOrder order) T) ≤ tInner)
    (h25p:25 < p) (hgOuterP:gOuter < p)
    (hcornerP:8127*k+178 < p) (hswapP:gOuter*tInner < p):
    ∃ order':Fin 3 ≃ Fin 3,
      (order'=order∨order'=swapOtherOrder order)∧
      order' 0=order 0∧
      0 < (planeMap K order' G).natDegree∧
      (planeMap K order' G).natDegree < p∧
      (Polynomial.resultant (planeMap K order' G)
        (planeMap K order' T)).natDegree < p:=by
  by_cases hpositive:0 < (planeMap K order G).natDegree
  · refine ⟨order,Or.inl rfl,rfl,hpositive,
      hGouter.trans_lt h25p,?_⟩
    exact (planeMap_corner_resultant_natDegree_le K order G T k hk hTne
      hGouter hTouter hGsupport hTsupport).trans_lt hcornerP
  · have hzero:(planeMap K order G).natDegree=0:=
      Nat.eq_zero_of_not_pos hpositive
    obtain ⟨order',hchoice,hbase,hpos⟩:=
      exists_positive_outer_order K order P G hG hGmem ht
    have hswapPos:0 < (planeMap K (swapOtherOrder order) G).natDegree:=by
      rcases hchoice with hsame | hswap
      · subst order'
        exact (hpositive hpos).elim
      · subst order'
        exact hpos
    refine ⟨swapOtherOrder order,Or.inr rfl,swapOtherOrder_zero order,
      hswapPos,hGswapOuter.trans_lt hgOuterP,?_⟩
    exact (swapped_resultant_natDegree_le_of_outer_zero K order G T
      gOuter tInner hzero hGswapOuter hTswapInner).trans_lt hswapP
end
end ProximityPrize.SubmissionLower.ActualPlaneJointProjection
