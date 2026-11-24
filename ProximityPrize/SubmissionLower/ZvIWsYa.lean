import ProximityPrize.SubmissionLower.ZYswgKc
set_option Elab.async false
open _root_ renaming Fin.prod_univ_four → zE3, Fin.sum_univ_succ → zCS, Finsupp.tsub_apply → zRK, Finsupp.weight_eq_sum → z1K, MvPolynomial.X → z9v, Nat.add_assoc → zVg, Nat.cast_zero → zQq, Nat.choose → z8H, Nat.choose_eq_zero_of_lt → zsx, Nat.lt_of_not_ge → znR
section
set_option autoImplicit true
namespace qnnEPee
noncomputable section
open aR (ao)
open xE (Flag)
open akL (Jp MI BU Oq oH ahV eAc alM)
open MvPolynomial
open private Certificate bNg aL6 d5W d5O from ProximityPrize.SubmissionLower.B
open private Certificate.mk Certificate.pow Certificate.mul from ProximityPrize.SubmissionLower.B
private def inverseCoord:Fin 4→MI :=
  ![z9v 0,z9v 0-MvPolynomial.X 1,
    z9v 2 - z9v 1,z9v 2 - z9v 3]
private theorem inverseCoord_apply (i:Fin 4) :bind₁ inverseCoord (coord i)=z9v i:= by
  fin_cases i <;> simp [coord,inverseCoord,bind₁_X_right]
theorem tailMap_injective (F:Flag) :Function.Injective (tailMap F) := by
  apply LinearIndependent.fintypeLinearCombination_injective
  apply LinearIndependent.of_comp (bind₁ inverseCoord).toLinearMap
  have he : (bind₁ inverseCoord).toLinearMap ∘ (fun e :Tail F=>tailMonomial e.val) =
      fun e=>(basisMonomials (Fin 4) ao) e.val := by
    funext e
    simp only [Function.comp_apply,AlgHom.toLinearMap_apply,tailMonomial,map_prod,map_pow,
      inverseCoord_apply,coe_basisMonomials]
    rw [monomial_eq,C_1,one_mul,Finsupp.prod_fintype _ _ (fun _=>pow_zero _)]
  rw [he]
  exact (basisMonomials (Fin 4) ao).linearIndependent.comp _ Subtype.val_injective
private theorem cV (e :Jp) :e.weight BU=e 0+e 1+e 2+e 3:= by
  simp [z1K,zCS,BU,zVg]
private theorem weight (e :Jp) :e.weight Oq=e 1+e 2*2+e 3*3:= by
  simp [z1K,zCS,Oq,zVg]
theorem tail_lattice (F:Flag) (e :Tail F) :
    (coordW e.val :ℤ)≤ coordV e.val∧(coordV e.val :ℤ)≤ coordU e.val ∧
      (coordU e.val :ℤ)≤F.degree∧(coordW e.val :ℤ)≤F.cap ∧
      F.order≤(coordU e.val :ℤ)+coordV e.val+coordW e.val ∧
      (coordU e.val :ℤ)+coordV e.val+coordW e.val≤F.upper := by
  obtain ⟨he,ho⟩:=Finset.mem_filter.mp e.property
  obtain ⟨hd,_,hu,ht⟩:=eAc.mp he
  change (e.val.weight BU:ℤ)=F.degree at hd
  change (e.val.weight Oq:ℤ)≤F.upper at hu
  change (e.val 3:ℤ)≤F.cap at ht
  rw [cV] at hd
  rw [weight] at hu ho
  unfold coordU coordV coordW
  exact ⟨by omega,by omega,by omega,ht,by omega,by omega⟩
private theorem monomial_certificate (e :Jp) :
    Certificate ⟨e.weight BU,0,e.weight Oq,e 3,e.weight Oq⟩
      (tailMonomial e) := by
  let h0:Certificate ⟨1,0,0,0,0⟩ (coord 0) :=
    Certificate.mk (d5W 0) (d5O 0)
  let h1 :Certificate ⟨1,0,1,0,1⟩ (coord 1) :=
    Certificate.mk (d5W 5) (d5O 5)
  let h2 :Certificate ⟨1,0,2,0,2⟩ (coord 2) :=
    Certificate.mk (d5W 6) (d5O 6)
  let h3:Certificate ⟨1,0,3,1,3⟩ (coord 3) :=
    Certificate.mk (d5W 4) (d5O 4)
  have h:=Certificate.mul (Certificate.mul (Certificate.mul
    (Certificate.pow h0 (e 0)) (Certificate.pow h1 (e 1))) (Certificate.pow h2 (e 2)))
    (Certificate.pow h3 (e 3))
  simpa only [cV,weight,tailMonomial,zE3,aL6,bNg,
    Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,mul_zero,mul_one,zero_add,add_zero] using h
theorem tailMonomial_support (F:Flag) (e :Tail F) :
    tailMonomial e.val∈ahV (relaxed F) ∧
      alM (tailMonomial e.val)∈restrictWeightedOrder oH F.order.toNat := by
  obtain ⟨he,ho⟩:=Finset.mem_filter.mp e.property
  obtain ⟨hd,hl,hu,ht⟩:=eAc.mp he
  obtain ⟨hp,hc⟩:=monomial_certificate e.val
  constructor
  · intro a ha
    obtain ⟨ha0,ha1,ha2,ha3⟩:=hp ha
    exact ⟨ha0.trans hd,ha1,ha2.trans hu,ha3.trans ht⟩
  · have hcut:F.order.toNat≤e.val.weight Oq:= by omega
    exact restrictWeightedOrder_anti oH hcut hc
end
end qnnEPee
end
section
set_option autoImplicit true
namespace qajFMeb
noncomputable section
open aR (ao)
open akL (MI Jp BU Oq)
open qnnEPee (tailMonomial coord coordU coordV coordW)
open MvPolynomial
local notation "Y" => (MvPolynomial.X:Fin 4→MI)
private abbrev gMZ (j:Fin 4) :=supported ao {i:Fin 4 | i≠j}
private theorem without_X {i j:Fin 4} (h:i≠j) :Y i∈gMZ j :=
  X_mem_supported.mpr h
private theorem peel (j:Fin 4) (A B:MI) (hA:A∈gMZ j) (hB:B∈gMZ j)
    (s :ao) (n:ℕ) (e :Jp) :
    (A*(B+C s*Y j)^n).coeff e =
      s^e j*(n.choose (e j) :ao)*(A*B^(n-e j)).coeff (e.erase j) := by
  classical
  rw [add_comm B,add_pow,Finset.mul_sum,coeff_sum]
  have ht (k :ℕ) :A*((C s*Y j)^k*B^(n - k)*(n.choose k :MI)) =
      (A*B^(n - k))*monomial (Finsupp.single j k) (s^k*(n.choose k :ao)) := by
    rw [← C_mul_X_pow_eq_monomial,mul_pow,← map_pow,← map_natCast (C:ao →+* MI),map_mul]
    ac_rfl
  simp only [ht,coeff_mul_monomial',Finsupp.single_le_iff]
  have herase :e-Finsupp.single j (e j)=e.erase j:= by
    ext i
    by_cases h:i=j
    · subst i
      simp [zRK]
    · simp [zRK,Finsupp.single_eq_of_ne h,Finsupp.erase_ne h]
  rw [Finset.sum_eq_single (e j)]
  · simp only [le_refl,ite_true,herase]
    ac_rfl
  · intro k _ hk
    split_ifs with hke
    · have hno:j∉(A*B^(n - k)).vars := by
        intro hj
        exact (mem_supported.mp ((gMZ j).mul_mem hA ((gMZ j).pow_mem hB _)) hj) rfl
      have hz : (A*B^(n - k)).coeff (e-Finsupp.single j k)=0:= by
        by_contra hne
        have hmem:=mem_support_iff.mpr hne
        have hh:=mem_support_notMem_vars_zero hmem hno
        simp only [zRK,Finsupp.single_eq_same] at hh
        omega
      rw [hz,zero_mul]
    · rfl
  · intro h
    have hk :n<e j:= by simpa [Finset.mem_range,Nat.lt_succ_iff] using h
    simp [zsx hk]
theorem exp_grade (e :Jp) :e.weight BU=e 0+e 1+e 2+e 3:= by
  simp [z1K,zCS,BU,zVg]
theorem exp_weight (e :Jp) :e.weight Oq=e 1+e 2*2+e 3*3:= by
  simp [z1K,zCS,Oq,zVg]
private theorem reorder {R:Type*} [CommMonoid R] (x y i j k :R) :
    y*k*(j*(x*i))=x*y*i*j*k := by ac_rfl
set_option maxHeartbeats 350000 in
theorem tail_coeff (e a :Jp) (hg:a.weight BU=e.weight BU) :
    (tailMonomial e).coeff a=(-1 :ao)^(a 1+a 3) *
      (z8H (coordU e-a 3-a 2) (a 1) :ao) *
      (z8H (coordV e-a 3) (a 2) :ao)*(z8H (coordW e) (a 3) :ao) := by
  let B₁:=Y 0-Y 1
  let B₂:=B₁+Y 2
  have hB₁ (j:Fin 4) (h0: (0:Fin 4)≠j) (h1 : (1 :Fin 4)≠j) :B₁∈gMZ j :=
    (gMZ j).sub_mem (without_X h0) (without_X h1)
  have hB₂:B₂∈gMZ 3:=(gMZ 3).add_mem (hB₁ 3 (by decide) (by decide)) (without_X (by decide))
  have ht:tailMonomial e=Y 0^e 0*B₁^e 1*B₂^e 2*(B₂+C (-1)*Y 3)^e 3:= by
    simp [tailMonomial,zE3,coord,B₁,B₂,sub_eq_add_neg]
  rw [ht,peel 3 _ _ ((gMZ 3).mul_mem
    ((gMZ 3).mul_mem ((gMZ 3).pow_mem (without_X (by decide)) _) ((gMZ 3).pow_mem
      (hB₁ 3 (by decide) (by decide)) _)) ((gMZ 3).pow_mem hB₂ _)) hB₂]
  change _=(-1 :ao)^(a 1+a 3)*_ *_ *(z8H (e 3) (a 3) :ao)
  by_cases h3:a 3≤e 3
  · rw [mul_assoc (Y 0^e 0*B₁^e 1),← pow_add,
      show e 2+(e 3-a 3)=coordV e-a 3 by unfold coordV; omega]
    have hB₁' : B₁+Y 2=B₁+C (1 :ao)*Y 2 := by simp
    change (-1 :ao)^a 3*_ *
      (Y 0^e 0*B₁^e 1*(B₁+Y 2)^(coordV e-a 3)).coeff (a.erase 3)= _
    rw [hB₁',peel 2 _ _ ((gMZ 2).mul_mem ((gMZ 2).pow_mem (without_X (by decide)) _)
      ((gMZ 2).pow_mem (hB₁ 2 (by decide) (by decide)) _)) (hB₁ 2 (by decide) (by decide))]
    simp only [Finsupp.erase_ne (show (2 :Fin 4)≠3 by decide),one_pow,one_mul]
    by_cases h2 :a 2≤ coordV e-a 3
    · rw [mul_assoc (Y 0^e 0),← pow_add,show e 1+(coordV e-a 3-a 2)=coordU e-a 3-a 2 by
        unfold coordV at h2 ⊢; unfold coordU; omega]
      have hB₁'' : B₁=Y 0+C (-1 :ao)*Y 1 := by simp [B₁,sub_eq_add_neg]
      rw [hB₁'',peel 1 _ _ ((gMZ 1).pow_mem (without_X (by decide)) _) (without_X (by decide))]
      simp only [Finsupp.erase_ne (show (1 :Fin 4)≠2 by decide),
        Finsupp.erase_ne (show (1 :Fin 4)≠3 by decide)]
      by_cases h1 :a 1≤ coordU e-a 3-a 2
      · rw [← pow_add,show e 0+(coordU e-a 3-a 2 - a 1)=a 0 by
          rw [exp_grade a,exp_grade e] at hg; unfold coordV at h2; unfold coordU at h1 ⊢; omega]
        have hs :Finsupp.single (0:Fin 4) (a 0)=(((a.erase 3).erase 2).erase 1) := by
          ext i
          fin_cases i <;> simp
        rw [coeff_X_pow,ite_eq_left hs,mul_one,pow_add]
        exact reorder ((-1 :ao)^a 1) ((-1 :ao)^a 3)
          ((coordU e-a 3-a 2).choose (a 1) :ao) ((coordV e-a 3).choose (a 2) :ao)
          ((e 3).choose (a 3) :ao)
      · simp only [zsx (znR h1),zQq,mul_zero,zero_mul]
    · simp only [zsx (znR h2),zQq,mul_zero,zero_mul]
  · simp only [zsx (znR h3),zQq,mul_zero,zero_mul]
end
end qajFMeb
end
