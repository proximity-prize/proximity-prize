import ProximityPrize.SubmissionLower.Z3aw2hc
import ProximityPrize.SubmissionLower.ZocsBpe
import ProximityPrize.SubmissionLower.Zay1XCa
set_option Elab.async false
open _root_ renaming AlgHom.coe_toRingHom → zlv, AlgHom.toRingHom_eq_coe → ziQ, CommRing → za6, Fin.addCases → zOx, Fin.addCases_left → zgb, Fin.addCases_right → z5m, Fintype.card_fin → zgY, Matrix.of_apply → zN9, Nat.add_mul → zNE, Nat.mul_comm → z5A, Nat.sub_add_cancel → zxt, Polynomial.map_injective → zTo, Polynomial.map_map → zoi
set_option maxHeartbeats 650000
namespace qd4QhDd
noncomputable section
open Polynomial Finset qxPDCsa
open scoped Classical WithZero
open P5 (K)
open cu (L j9)
open P5_7_7 (phys)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet atPolynomial)
open qb0hmCe (CurveModel cLN)
open q1kuFjb (IntSeries residue Ua liftAt_reduce coeff_liftAt expansion_coeff)
open qFD8jve (sheetPole)
open qrezXJe (sheet_bound)
open q14iMuc (discr_map discr_ne coeff_nonzero_of_val_eq)
open private efc aMX from ProximityPrize.SubmissionLower.Y
private def last {R:Type*} [za6 R] (f :R[X]) (hd:0<f.natDegree) :
    Fin (f.natDegree-1+f.natDegree) :=
  ⟨2*f.natDegree-2,by omega⟩
private theorem matrix_eq {R:Type*} [za6 R] (f :R[X]) (hd:0<f.natDegree) :
    f.sylvesterDeriv =
      (sylvester f.derivative f (f.natDegree-1) f.natDegree).updateRow (last f hd)
        (fun j=>if j.val=f.natDegree-2 then 1 else
          if j.val = 2*f.natDegree-2 then f.natDegree else 0) := by
  simp only [sylvesterDeriv,hd.ne',dite_false,last]
private theorem discr_degree {E :Type} [Field E] (f :E[X][X]) (D W:ℕ)
    (hd:0<f.natDegree)
    (hw : ∀ i,f.coeff i≠0→(f.coeff i).natDegree+i*D ≤W) :
    f.discr.natDegree≤discDegree D f.natDegree W:= by
  let d:=f.natDegree
  let r :=last f hd
  let M:=f.sylvesterDeriv
  have hD:d*D ≤W :=
    (Nat.le_add_left _ _).trans (hw d (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hd)))
  have hd' : 0<d:=hd
  by_cases h1 :d = 1
  · have hdeg:f.degree=1 :=(degree_eq_iff_natDegree_eq_of_pos one_pos).mpr h1
    rw [discr_of_degree_eq_one hdeg,natDegree_one]
    exact Nat.zero_le _
  have hDW:D ≤W :=
    (by simpa only [one_mul] using Nat.mul_le_mul_right D (show 1≤d from hd') :D ≤d*D).trans hD
  let bonus (i:Fin (d-1+d)) :=if i=r then W-d*D else 0
  let cV (i:Fin (d-1+d)) :=D*i.val+bonus i
  let cap:Fin (d-1+d)→ℕ:=zOx (fun j=>W+D*j.val) (fun j=>W-D+D*j.val)
  have hrow:cV r=W+D*(d-2) := by
    simp only [cV,bonus,r,last]
    change D*(2*d-2)+(W-d*D)= _
    rw [show 2*d-2=d+(d-2) by omega,Nat.mul_add,z5A D d]
    omega
  have hentry (i j:Fin (d-1+d)) (hne :M i j≠0) :
      (M i j).natDegree+cV i≤ cap j:= by
    by_cases hi:i=r
    · subst i
      rw [hrow]
      simp only [M,matrix_eq f hd,r,Matrix.updateRow_self] at hne ⊢
      cases j using zOx with
      | left j =>
        simp only [cap,zgb,Fin.val_castAdd] at hne ⊢
        have hj:=j.isLt
        change (if j.val=d-2 then 1 else if j.val = 2*d-2 then (d:E[X]) else 0).natDegree +
          (W+D*(d-2))≤W+D*j.val
        split_ifs at hne ⊢ with hfirst hlast
        · simp [hfirst]
        · omega
        · exact (hne rfl).elim
      | right j =>
        simp only [cap,z5m,Fin.val_natAdd] at hne ⊢
        have hj:=j.isLt
        change (if d-1+j.val=d-2 then 1 else if d-1+j.val = 2*d-2 then (d:E[X]) else 0).natDegree +
          (W+D*(d-2))≤W-D+D*j.val
        split_ifs at hne ⊢ with hfirst hlast
        · omega
        · rw [natDegree_natCast,zero_add,show j.val=(d-2)+1 by omega,Nat.mul_add,Nat.mul_one]
          omega
        · exact (hne rfl).elim
    · have hn:i≠last f hd:=hi
      have hM:M i j=sylvester f.derivative f (d-1) d i j:= by
        simp only [M,matrix_eq f hd,Matrix.updateRow_ne hn,d]
      rw [hM] at hne ⊢
      simp only [cV,bonus,ite_eq_right hi,add_zero]
      cases j using zOx with
      | left j =>
        simp only [sylvester,zN9,zgb,cap] at hne ⊢
        split_ifs at hne ⊢ with hj
        · have he : (i.val-j.val)*D+D*j.val=D*i.val := by
            rw [z5A D j.val,← zNE,zxt hj.1,z5A]
          have :=hw _ hne
          omega
        · exact (hne rfl).elim
      | right j =>
        simp only [sylvester,zN9,z5m,cap] at hne ⊢
        split_ifs at hne ⊢ with hj
        · have he : (i.val-j.val+1)*D+D*j.val=D*i.val+D:= by
            rw [zNE,one_mul,z5A D j.val,
              add_right_comm,← zNE,zxt hj.1,z5A i.val D]
          have hc:f.coeff (i.val-j.val+1)≠0:= fun hz =>
            hne (by simp [coeff_derivative,hz])
          have :=hw _ hc
          have :=coeff_derivative_natDegree_le f (i.val-j.val)
          omega
        · exact (hne rfl).elim
  let s :=(∑ j:Fin (d-1),D*j.val) + ∑ j:Fin d,D*j.val
  have hcap : ∑ j,cap j=(d-1)*W+d*(W-D)+s := by
    simp only [cap,s,Fin.sum_univ_add,zgb,z5m,
      sum_add_distrib,sum_const,card_univ,zgY,smul_eq_mul]
    ring
  have hbonus : ∑ i,bonus i=W-d*D:= by simp [bonus]
  have hgrade : ∑ i,cV i=D*((d-1)*d)+s+(W-d*D) := by
    simp only [cV,sum_add_distrib,hbonus]
    congr 1
    simp only [s,Fin.sum_univ_add,Fin.val_castAdd,Fin.val_natAdd,Nat.mul_add,
      sum_add_distrib,sum_const,card_univ,zgY,smul_eq_mul]
    ring
  have hsum: (d-1)*W+d*(W-D)=(2*d-2)*W+(W-d*D) := by
    rw [Nat.mul_sub,← Nat.add_sub_assoc (Nat.mul_le_mul_left d hDW),← zNE,
      show (d-1)+d=(2*d-2)+1 by omega,zNE,one_mul]
    omega
  unfold discr discDegree
  change (M.det*(-1 :E[X])^(d*(d-1)/2)).natDegree≤_
  have hsign: (M.det*(-1 :E[X])^(d*(d-1)/2)).natDegree≤M.det.natDegree :=
    natDegree_mul_le.trans (by simp)
  refine hsign.trans ?_
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  refine (natDegree_smul_le _ _).trans ?_
  by_cases hz : ∃ j,M (σ j) j=0
  · obtain ⟨j,hj⟩:=hz
    rw [Finset.prod_eq_zero (f := fun k=>M (σ k) k) (mem_univ j) hj,natDegree_zero]
    exact Nat.zero_le _
  · push Not at hz
    have h:=sum_le_sum (s :=univ) fun j _=>hentry (σ j) j (hz j)
    rw [sum_add_distrib,Equiv.sum_comp σ cV,hgrade,hcap,hsum,
      show D*((d-1)*d)=d*(d-1)*D by ring] at h
    exact (natDegree_prod_le _ _).trans (by change _≤(2*d-2)*W-d*(d-1)*D; omega)
private theorem cast_le_one {R:Type*} [za6 R] (v :Valuation R ℤᵐ⁰) (n:ℕ) :
    v (n:R)≤1 := by
  induction n with
  | zero=>simp
  | succ n ih=>rw [Nat.cast_succ]; exact v.map_add_le ih (by simp)
private theorem discr_val_le {R:Type*} [za6 R] (v :Valuation R ℤᵐ⁰) (f :R[X])
    (hd:0<f.natDegree) (b:ℤᵐ⁰) (hf : ∀ i,v (f.coeff i)≤b) :
    v f.discr≤b^(2*f.natDegree-2) := by
  let d:=f.natDegree
  let r :=last f hd
  let M:=f.sylvesterDeriv
  let cap (i:Fin (d-1+d)) :=if i=r then 1 else b
  have he (i j:Fin (d-1+d)) :v (M i j)≤ cap i:= by
    by_cases hi:i=r
    · subst i
      simp only [cap,ite_eq_left rfl,M,matrix_eq f hd,r,Matrix.updateRow_self]
      split_ifs <;> simp [cast_le_one]
    · have hn:i≠last f hd:=hi
      have hM:M i j=sylvester f.derivative f (d-1) d i j:= by
        simp only [M,matrix_eq f hd,Matrix.updateRow_ne hn,d]
      rw [hM]
      simp only [cap,ite_eq_right hi]
      cases j using zOx with
      | left j =>
        simp only [sylvester,zN9,zgb]
        split
        · exact hf _
        · simp
      | right j =>
        simp only [sylvester,zN9,z5m]
        split
        · rw [coeff_derivative,map_mul,← Nat.cast_succ]
          exact (mul_le_mul' (hf _) (cast_le_one v _)).trans_eq (mul_one _)
        · simp
  have hc : ∏ i,cap i=b^(2*d-2) := by
    rw [← mul_prod_erase univ cap (mem_univ r)]
    simp only [cap,ite_eq_left rfl,one_mul]
    have h : ∀ i∈univ.erase r,cap i=b:= fun i hi=>ite_eq_right (ne_of_mem_erase hi)
    rw [show (∏ i∈univ.erase r,cap i) = ∏ _i∈univ.erase r,b from prod_congr rfl h,
      prod_const,card_erase_of_mem (mem_univ r),card_univ,zgY,
      show d-1+d-1=2*d-2 by omega]
  unfold discr
  rw [map_mul,map_pow,Valuation.map_neg,map_one,one_pow,mul_one]
  change v M.det≤_
  rw [Matrix.det_apply]
  apply v.map_sum_le
  intro σ _
  have ht:v (∏ i,M (σ i) i)≤b^(2*d-2) := by
    rw [map_prod]
    exact (prod_le_prod fun i _=>he (σ i) i).trans_eq ((Equiv.prod_comp σ cap).trans hc)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
    simpa [hs,Valuation.map_neg] using ht
private theorem sheet_discr_bound {q:PlaneCurve} {Cq:CurveModel q}
    {z :K→K} {S:K→K[X]} (F:Sheet Cq z S) :
    Bound F F.f.discr (2*F.d-2) := by
  intro w j
  let b:=sheetPole w.value F.f
  let u:ℤᵐ⁰:=WithZero.exp (b:ℤ)
  have hf (i:ℕ) :efc w.value (F.f.coeff i)≤u :=
    Finset.sup_le fun k _=>sheet_bound w.value F.f i k
  refine (aMX w.value _ j).trans
    ((discr_val_le (efc w.value) F.f F.positive u hf).trans_eq ?_)
  change WithZero.exp (b:ℤ)^(2*F.d-2)= _
  rw [← WithZero.exp_nsmul]
  simp [b]
private theorem simple {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
    (F:Sheet Cq z S) (γ:K) (hγ:γ∈F.marks)
    (hu:UnitAt F γ F.f.discr.leadingCoeff) :
    atPolynomial (specialize F hγ).derivative (S γ)≠0:= by
  let a :=F.atPlace γ hγ
  let g:=Ua a F.f (fun i j=>F.value γ hγ _ ▸ F.integral γ hγ i j)
  let t:=specialize F hγ
  let ρ:=mapRingHom residue
  let ι:IntSeries →+* LaurentSeries L:=IntSeries.subtype
  have hinj:Function.Injective ι:=Subtype.val_injective
  have hmap :g.map (mapRingHom ι)=F.f.map (mapRingHom a.toRingHom) := by
    apply Polynomial.ext
    intro i
    apply Polynomial.ext
    intro j
    simpa only [coeff_map,coe_mapRingHom,ι,Subring.subtype_apply,
      ziQ,zlv,g] using coeff_liftAt a F.f _ i j
  have hred:g.map ρ=t:=liftAt_reduce _ _ _
  have hg:g.natDegree=F.d:= by
    simpa only [natDegree_map_eq_of_injective (f :=mapRingHom ι)
      (zTo ι hinj),
      natDegree_map_eq_of_injective (f :=mapRingHom a.toRingHom)
        (zTo a.toRingHom a.injective)] using
      congrArg natDegree hmap
  have htop:t.coeff F.d≠0:= by
    have hj: (t.coeff F.d).coeff (F.f.coeff F.d).natDegree=1 := by
      change ((cLN a 0 F.f).coeff F.d).coeff (F.f.coeff F.d).natDegree=1
      rw [expansion_coeff,coeff_natDegree,F.normalized,map_one]
      simp
    intro hz
    rw [hz,coeff_zero] at hj
    exact zero_ne_one hj
  have hpos :0<g.natDegree :=hg.symm ▸ F.positive
  have hsub:g.discr.map ι=F.f.discr.map a.toRingHom:= by
    change mapRingHom ι g.discr=mapRingHom a.toRingHom F.f.discr
    rw [← discr_map _ (zTo _ hinj) _ hpos,hmap,
      discr_map _ (zTo _ a.injective) _ F.positive]
  have hne :ρ g.discr≠0:= by
    intro hz
    let j:=F.f.discr.natDegree
    have ha :a F.f.discr.leadingCoeff=ι (g.discr.coeff j) := by
      simpa only [coeff_map,coeff_natDegree,ziQ,zlv,j] using
        (congrArg (fun u: (LaurentSeries L)[X]=>u.coeff j) hsub).symm
    have hv :=coeff_nonzero_of_val_eq ((F.value γ hγ F.f.discr.leadingCoeff).symm.trans hu)
    rw [ha] at hv
    apply hv
    have he :=congrArg (fun u:L[X]=>u.coeff j) hz
    simpa only [ρ,coe_mapRingHom,coeff_map,coeff_zero,q1kuFjb.fWQ,
      ι,Subring.subtype_apply] using he
  have hl:ρ g.leadingCoeff=t.coeff F.d:= by
    rw [← hg,← hred,coeff_map,coeff_natDegree]
  have hr :ρ (g.resultant g.derivative g.natDegree (g.natDegree-1))≠0:= by
    rw [resultant_deriv (natDegree_pos_iff_degree_pos.mp hpos),map_mul,map_mul,map_pow,
      map_neg,map_one,hl]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by simp)) htop) hne
  have hi:=IsFractionRing.injective L[X] cu.FX
  have hn:=eval_derivative_map_ne_zero_of_resultant_derivative_padded_ne_zero (phys.comp ρ) g
    le_rfl hpos ((map_ne_zero_iff phys hi).mpr hr) (phys (j9 (S γ))) (by
      rw [← zoi,hred,← eval₂_eq_eval_map]
      exact F.root γ hγ)
  rw [← zoi,hred] at hn
  rw [derivative_map,← eval₂_eq_eval_map] at hn
  exact hn
theorem proof :qxPDCsa.c1 := by
  intro q Cq z S F D W hp hw
  exact ⟨discr_ne F.f F.irreducible F.positive hp,discr_degree F.f D W F.positive hw,
    sheet_discr_bound F,simple F⟩
end
end qd4QhDd
