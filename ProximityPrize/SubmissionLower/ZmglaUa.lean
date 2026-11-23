import ProximityPrize.SubmissionLower.Z1qPXJc
import ProximityPrize.SubmissionLower.Zfobjva
import ProximityPrize.SubmissionLower.Zmn8gnb
set_option Elab.async false
open _root_ renaming AddSubmonoid → zwd, Finset.sum_const_zero → zWA, Finsupp.weight_eq_sum → z1K, Fintype.sum_sum_type → zbt, MvPolynomial.C → znf, MvPolynomial.eval₂Hom → zOD, MvPolynomial.rename → zHw, MvPolynomial.restrictWeightedDegree → zAp, Nat.add_sub_of_le → zp3, Nat.mul_one → zMo, Nat.mul_zero → zvM, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.sylvester → zco, PowerSeries.C → zMG
section
set_option autoImplicit true
namespace P5_7_3_3_4_1_7R_2
noncomputable section
open Polynomial qL2osVa
open P5_7_3_3_4_1_7 (CutEquation det targetNum targetDen)
open P5_7_3_3_4_1_7R (normalized)
open cu (L)
open DQ (DT)
open Cu (sQ)
open private taylor_degree from ProximityPrize.SubmissionLower.ZFh47Da
open scoped BigOperators
private def coeffs {R:Type*} [Semiring R] (S:zwd R) :zwd R[X] where
  carrier := {f | ∀ i,f.coeff i∈S}
  zero_mem' := fun i=> by rw [coeff_zero]; exact S.zero_mem
  add_mem' hf hg:= fun i=> by rw [coeff_add]; exact S.add_mem (hf i) (hg i)
private theorem coeffs_C {R:Type*} [Semiring R] {S:zwd R} {a :R}
    (ha :a∈S) :z1z a∈coeffs S:= by
  intro i
  rw [coeff_C]
  split_ifs
  · exact ha
  · exact S.zero_mem
private theorem coeffs_X {R:Type*} [Semiring R] {S:zwd R} (h:1∈S) :
    z7y∈coeffs S:= by
  intro i
  rw [coeff_X]
  split_ifs
  · exact h
  · exact S.zero_mem
private theorem coeffs_mul {R:Type*} [Semiring R] {S T U:zwd R}
    (hm : ∀ ⦃a b⦄,a∈S→b∈T→a*b∈U)
    ⦃f g:R[X]⦄ (hf :f∈coeffs S) (hg:g∈coeffs T) :
    f * g∈coeffs U:= by
  intro i
  rw [coeff_mul]
  exact sum_mem fun v _=>hm (hf v.1) (hg v.2)
private abbrev cutBound {n:ℕ} (w:Fin 2 ⊕ Fin n→ℕ) (b:ℕ) :zwd (Cut n) :=
  (zAp (R:=L) w b).toAddSubmonoid
private abbrev physBound {n:ℕ} (w:Fin 2 ⊕ Fin n→ℕ) (b:ℕ) :=coeffs (cutBound w b)
private abbrev eqBound {n:ℕ} (w:Fin 2 ⊕ Fin n→ℕ) (b:ℕ) :=coeffs (physBound w b)
private theorem cut_const {n:ℕ} (w:Fin 2 ⊕ Fin n→ℕ) (b:ℕ) (a :L) :
    znf a∈cutBound w b :=
  MvPolynomial.C_mem_restrictWeightedDegree w b a
private theorem cut_mul {n u v :ℕ} {w:Fin 2 ⊕ Fin n→ℕ} {f g:Cut n}
    (hf :f∈cutBound w u) (hg:g∈cutBound w v) :f * g∈cutBound w (u+v) :=
  MvPolynomial.mul_mem_restrictWeightedDegree hf hg
private theorem phys_mul {n u v :ℕ} {w:Fin 2 ⊕ Fin n→ℕ} {f g: (Cut n)[X]}
    (hf :f∈physBound w u) (hg:g∈physBound w v) :f * g∈physBound w (u+v) :=
  coeffs_mul (by intro a b ha hb; exact cut_mul ha hb) hf hg
private theorem eq_mul {n u v :ℕ} {w:Fin 2 ⊕ Fin n→ℕ} {f g:CutEquation n}
    (hf :f∈eqBound w u) (hg:g∈eqBound w v) :f * g∈eqBound w (u+v) :=
  coeffs_mul (by intro a b ha hb; exact phys_mul ha hb) hf hg
private theorem phys_one {n:ℕ} (w:Fin 2 ⊕ Fin n→ℕ) (b:ℕ) :
    1∈physBound w b:= by
  simpa only [map_one] using coeffs_C (cut_const w b 1)
private theorem eq_one {n:ℕ} (w:Fin 2 ⊕ Fin n→ℕ) (b:ℕ) :
    1∈eqBound w b:= by
  simpa only [map_one] using coeffs_C (phys_one w b)
private theorem eq_pow {n b:ℕ} {w:Fin 2 ⊕ Fin n→ℕ} {f :CutEquation n}
    (hf :f∈eqBound w b) (i:ℕ) :f^i∈eqBound w (i*b) := by
  induction i with
  | zero=>simpa only [pow_zero,zero_mul] using eq_one w 0
  | succ i ih=>simpa only [pow_succ,Nat.succ_mul] using eq_mul ih hf
private theorem phys_prod {n b:ℕ} {w:Fin 2 ⊕ Fin n→ℕ} {ι:Type*}
    (S:Finset ι) (f :ι→(Cut n)[X]) (h : ∀ i∈S,f i∈physBound w b) :
    (∏ i∈S,f i)∈physBound w (S.card*b) := by
  classical
  induction S using Finset.induction_on with
  | empty=>simpa only [Finset.prod_empty,Finset.card_empty,zero_mul] using phys_one w 0
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi,Finset.card_insert_of_notMem hi,Nat.succ_mul,add_comm]
    exact phys_mul (h i (Finset.mem_insert_self _ _))
      (ih fun j hj=>h j (Finset.mem_insert_of_mem hj))
private def block (n s t:ℕ) :Fin 2 ⊕ Fin n→ℕ :=
  Sum.elim (fun _=>s) (fun _=>t)
private theorem target_bound {n:ℕ} (s t:ℕ) (r :Target) :
    targetNum r∈cutBound (block n s t) (r.cost*s) ∧
    targetDen r∈cutBound (block n s t) (r.cost*s) := by
  let w:=block n s t
  cases r with
  | constant v =>
    simp only [targetNum,targetDen,Target.cost,zero_mul]
    exact ⟨cut_const w 0 v,by simpa only [map_one] using cut_const w 0 1⟩
  | projective i a b c =>
    simp only [targetNum,targetDen,Target.cost,one_mul]
    have hX:MvPolynomial.X (Sum.inl i)∈cutBound w s :=
      MvPolynomial.X_mem_restrictWeightedDegree w s _ le_rfl
    exact ⟨by simpa only [zero_add] using cut_mul (cut_const w 0 c) hX,
      (cutBound w s).add_mem (cut_const w s a)
        (by simpa only [add_zero] using cut_mul hX (cut_const w 0 b))⟩
private theorem rename_chart {n:ℕ} (s t:ℕ) {q:DT n}
    (hq:q.totalDegree≤1) :
    zHw (Sum.inr :Fin n→Fin 2 ⊕ Fin n) q∈cutBound (block n s t) t:= by
  change _∈zAp _ _
  rw [MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le,
    MvPolynomial.weightedTotalDegree_rename_of_injective Sum.inr_injective,
    MvPolynomial.weightedTotalDegree,Finset.sup_le_iff]
  intro m hm
  simp only [Finsupp.weight_apply,Function.comp_apply,block,Sum.elim_inr,smul_eq_mul,
    Finsupp.sum,← Finset.sum_mul]
  simpa only [Finsupp.sum,one_mul] using
    Nat.mul_le_mul_right t ((MvPolynomial.le_totalDegree hm).trans hq)
private theorem substitution_bound {n g b t:ℕ} {w:Fin 2 ⊕ Fin n→ℕ}
    {E :ℕ→(Cut n)[X]} {N D:CutEquation n} (he : ∀ i,E i∈physBound w t)
    (hN :N∈eqBound w b) (hD:D∈eqBound w b) :
    (∑ i∈Finset.range (g+1),z1z (E i)*N^i*D^(g - i)) ∈
      eqBound w (t+g*b) := by
  apply sum_mem
  intro i hi
  have hi' : i≤g:=Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h:=eq_mul (eq_mul (coeffs_C (he i)) (eq_pow hN i)) (eq_pow hD (g - i))
  rwa [Nat.add_assoc,← Nat.add_mul,zp3 hi'] at h
private theorem normalized_bound {C₀:sQ} [Fact (Irreducible C₀)]
    (C:MarkedSheet C₀) (x a :L) (r :Target) (s t:ℕ) :
    normalized C x r a∈eqBound (block C.sheet.n s t) (t+C.g*(r.cost*s)) := by
  let w:=block C.sheet.n s t
  let ρ:=zHw (R:=L) (Sum.inr :Fin C.sheet.n→Fin 2 ⊕ Fin C.sheet.n)
  let e :=(taylorAlgHom (znf (σ:=Fin 2 ⊕ Fin C.sheet.n) x)).toRingHom.comp
    (Polynomial.mapRingHom ρ.toRingHom)
  let c:=(z1z: (Cut C.sheet.n)[X] →+* CutEquation C.sheet.n).comp z1z
  let V:CutEquation C.sheet.n:=1+c (znf a)*z7y
  let N :CutEquation C.sheet.n:=c (targetNum r)*V+Polynomial.X
  let D:CutEquation C.sheet.n:=c (targetDen r)*V
  have he (i:ℕ) :e (C.sheet.bY.equation.coeff i)∈physBound w t:= by
    intro k
    change (taylor (znf x) ((C.sheet.bY.equation.coeff i).map ρ.toRingHom)).coeff k∈_
    have hx :ρ.toRingHom (znf x)=znf x :=MvPolynomial.rename_C _ _
    rw [← hx,← map_taylor _ _ ρ.toRingHom,coeff_map]
    exact rename_chart s t (taylor_degree x _ (C.sheet.bY.degree.2 i) k)
  have hX (b:ℕ) : (z7y:CutEquation C.sheet.n)∈eqBound w b :=
    coeffs_X (phys_one w b)
  have hc {b:ℕ} {q:Cut C.sheet.n} (h:q∈cutBound w b) :c q∈eqBound w b :=
    coeffs_C (coeffs_C h)
  have hV:V∈eqBound w 0 :=
    (eqBound w 0).add_mem (eq_one w 0) (eq_mul (u:=0) (v :=0) (hc (cut_const w 0 a)) (hX 0))
  have hr :=target_bound (n:=C.sheet.n) s t r
  have hN :N∈eqBound w (r.cost*s) :=(eqBound w (r.cost*s)).add_mem
    (by simpa only [add_zero] using eq_mul (hc hr.1) hV) (hX (r.cost*s))
  have hD:D∈eqBound w (r.cost*s) := by
    simpa only [add_zero] using eq_mul (hc hr.2) hV
  exact substitution_bound (g:=C.g) (w:=w)
    (E := fun i=>e (C.sheet.bY.equation.coeff i)) (N :=N) (D:=D) he hN hD
private theorem b0v {n g b:ℕ} {w:Fin 2 ⊕ Fin n→ℕ} {F:CutEquation n}
    (hF:F∈eqBound w b) :det F g∈physBound w ((g+(g - 1))*b) := by
  classical
  have hderiv (i:ℕ) :F.derivative.coeff i∈physBound w b:= by
    have hc: ((i+1 :ℕ) : (Cut n)[X])∈physBound w 0:= by
      simpa only [map_natCast] using coeffs_C (cut_const w 0 ((i+1 :ℕ) :L))
    rw [coeff_derivative]
    simpa only [Nat.cast_add,Nat.cast_one,add_zero] using phys_mul (hF (i+1)) hc
  let M:=zco F F.derivative g (g - 1)
  have hentry (i j:Fin (g+(g - 1))) :M i j∈physBound w b:= by
    cases j using Fin.addCases with
    | left j =>
      simp only [M,zco,Matrix.of_apply,Fin.addCases_left]
      split_ifs
      · exact hderiv _
      · exact (physBound w b).zero_mem
    | right j =>
      simp only [M,zco,Matrix.of_apply,Fin.addCases_right]
      split_ifs
      · exact hF _
      · exact (physBound w b).zero_mem
  change M.det∈_
  rw [Matrix.det_apply']
  apply sum_mem
  intro σ _
  have hsign: ((Equiv.Perm.sign σ:ℤ) : (Cut n)[X])∈physBound w 0:= by
    simpa only [map_intCast] using coeffs_C (cut_const w 0 ((Equiv.Perm.sign σ:ℤ) :L))
  have hp:=phys_prod Finset.univ (fun i=>M (σ i) i) (fun i _=>hentry (σ i) i)
  simpa only [zero_add,Finset.card_univ,Fintype.card_fin] using phys_mul hsign hp
private theorem mixed_of_bounds {n u v :ℕ} {q:Cut n}
    (hseed :q∈cutBound (block n 1 0) u) (hchart:q∈cutBound (block n 0 1) v) :
    MixedDegree q u v := by
  intro m hm
  have hs :=MvPolynomial.mem_restrictWeightedDegree.mp hseed m hm
  have ht:=MvPolynomial.mem_restrictWeightedDegree.mp hchart m hm
  constructor
  · simpa only [z1K,zbt,smul_eq_mul,block,
      Sum.elim_inl,Sum.elim_inr,zMo,zvM,zWA,
      add_zero] using hs
  · simpa only [z1K,zbt,smul_eq_mul,block,
      Sum.elim_inl,Sum.elim_inr,zMo,zvM,zWA,
      zero_add] using ht
theorem proof :P5_7_3_3_4_1_7R.c2 := by
  intro C₀ _ C x a r hg d j
  have hseed :=normalized_bound C x a r 1 0
  have hchart:=normalized_bound C x a r 0 1
  have hsize :C.g+(C.g - 1)=2*C.g - 1 := by omega
  have hs :=b0v (g:=C.g) hseed d
  have ht:=b0v (g:=C.g) hchart d
  refine ⟨mixed_of_bounds ?_ ?_,mixed_of_bounds ?_ ?_⟩
  · simpa only [hsize,zMo,zero_add,Nat.mul_assoc] using hs
  · simpa only [hsize,zvM,add_zero,zMo] using ht
  · simpa only [zMo,zero_add] using (hseed j 0)
  · simpa only [zvM,add_zero] using (hchart j 0)
end
end P5_7_3_3_4_1_7R_2
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5_7_3_3_4_1_7R_3
noncomputable section
open Polynomial hiding constantCoeff expand
open TrivSqZeroExt
open qL2osVa
open P5_7_3_3_4_1_7 hiding normalized
open P5_7_3_3_4_1_7R (normalized)
open qAjZDhd (arcParam arcEquation arcEquation_specialize)
open P5 (K)
open cu (L j9)
open DQ (DT)
open Cu (sQ)
open PowerSeries (constantCoeff)
variable {C₀:sQ} [Fact (Irreducible C₀)] {C:MarkedSheet C₀} {γ:K}
private def original (A:Arc C γ) (x :L) :LocalEquation :=
  (arcEquation A).map (aUs x)
private theorem local_rename (A:Arc C γ) (x :L) (f : (DT C.sheet.n)[X]) :
    bfj A ((taylorAlgHom (znf (σ:=Fin 2 ⊕ Fin C.sheet.n) x)).toRingHom
      (f.map (zHw Sum.inr).toRingHom)) =
      aUs x (f.map (arcParam A)) := by
  have h: (arcEval A).comp (zHw Sum.inr).toRingHom=arcParam A:= by
    apply RingHom.ext
    intro q
    change zOD zMG (Sum.elim A.seed A.parameter)
      (zHw Sum.inr q)=zOD zMG A.parameter q
    rw [MvPolynomial.eval₂Hom_rename]
    rfl
  change (↑((taylor _ _).map (arcEval A)) :DoubleSeries) = ↑(taylor (zMG x) _)
  rw [map_taylor,map_map,h]
  simp only [arcEval,MvPolynomial.eval₂Hom_C]
private def targetSeries (A:Arc C γ) (q:Cut C.sheet.n) :DoubleSeries :=
  zMG (arcEval A q)
private theorem normalized_eval {R:Type*} [CommRing R] (A:Arc C γ) (x a :L)
    (r :Target) (φ:DoubleSeries →+* R) (u y :R)
    (h:φ (targetSeries A (targetNum r)) *
        (1+φ (zMG (zMG a))*u)+u =
      (φ (targetSeries A (targetDen r)) *
        (1+φ (zMG (zMG a))*u))*y) :
    (localEquation A (normalized C x r a)).eval₂ φ u =
      (φ (targetSeries A (targetDen r)) *
        (1+φ (zMG (zMG a))*u))^C.g *
        (original A x).eval₂ φ y := by
  rw [localEquation,eval₂_map]
  let E :=eval₂RingHom (φ.comp (bfj A)) u
  change E (normalized C x r a)= _
  have hc (z :Cut C.sheet.n) :bfj A (z1z z)=targetSeries A z := by
    simp [bfj,targetSeries]
  have ha :targetSeries A (znf a)=zMG (zMG a) := by
    simp [targetSeries,arcEval]
  simp only [normalized,map_sum,map_mul,map_pow,map_one,map_add,E,coe_eval₂RingHom,
    eval₂_C,eval₂_X,RingHom.comp_apply,hc,ha,h]
  have hd: (original A x).natDegree≤C.g :=
    natDegree_map_le.trans (natDegree_map_le.trans C.sheet.bY.degree.1)
  rw [eval₂_eq_sum_range' φ (Nat.lt_succ_of_le hd),Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i≤C.g:=Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  simp only [original,arcEquation,coeff_map,coe_mapRingHom]
  rw [local_rename A x (C.sheet.bY.equation.coeff i),mul_pow]
  generalize φ (targetSeries A (targetDen r)) *
    (1+φ (zMG (zMG a))*u)=d
  rw [show d^C.g=d^i*d^(C.g-i) by rw [← pow_add,zp3 hi']]
  ring
private theorem original_fibre (A:Arc C γ) (x :L) :
    seedFibre (original A x)=(C.markedEquation γ).map (expand x) := by
  apply Polynomial.ext
  intro i
  simp only [seedFibre,original,coeff_map,expand_fst]
  simpa only [coeff_map,qAjZDhd.reduce,coe_mapRingHom] using
    congrArg (fun f=>expand x (f.coeff i)) (arcEquation_specialize A)
private theorem original_snd (A:Arc C γ) (x :L) (w:Series) :
    ((original A x).eval₂ jet (pair (expand x (j9 (C.s γ))) w)).snd =
      expand x (markedJet A)+expand x (markedSeparant C γ)*w:= by
  rw [eval_snd,original_fibre]
  congr 1
  · rw [← expand_lift]
    change seedFirst (((arcEquation A).map (aUs x)).eval
      (aUs x ((j9 (C.s γ)).map zMG)))= _
    rw [eval_map_apply]
    exact expand_snd x _
  · rw [derivative_map,eval_map_apply]
    rfl
private def centre :Dual Series →+* Dual L where
  toFun a :=pair (constantCoeff a.fst) (constantCoeff a.snd)
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' a b:= by ext <;> simp
  map_mul' a b:= by ext <;> simp
@[simp] private theorem centre_pair (u v :Series) :
    centre (pair u v)=pair (constantCoeff u) (constantCoeff v) :=rfl
private theorem target_centre (A:ArcFamily C) (hγ:γ∈C.smoothMarks)
    (x :L) (r :Target) (h:r.hit (C:=C) x γ) :
    IsUnit (centre (jet (targetSeries (A ⟨γ,hγ⟩) (targetDen r)))) ∧
      centre (jet (targetSeries (A ⟨γ,hγ⟩) (targetNum r))) =
        centre (jet (targetSeries (A ⟨γ,hγ⟩) (targetDen r))) *
          pair ((j9 (C.s γ)).eval x) (r.slope A γ) := by
  classical
  let B:=A ⟨γ,hγ⟩
  let t:Cut C.sheet.n →+* Dual L:=centre.comp (jet.comp (PowerSeries.C.comp (arcEval B)))
  change IsUnit (t (targetDen r)) ∧
    t (targetNum r)=t (targetDen r)*pair ((j9 (C.s γ)).eval x) (r.slope A γ)
  have hj (u:Series) :centre (jet (zMG u)) =
      pair (constantCoeff u) (PowerSeries.coeff 1 u) := by
    rw [jet_C,centre_pair]
    simp
  have htC (c:L) :t (znf c)=pair c 0:= by
    change centre (jet (targetSeries B _))= _
    simp [targetSeries,arcEval,hj]
  cases r with
  | constant c =>
    change (j9 (C.s γ)).eval x=c at h
    simp [targetNum,targetDen,htC,Target.slope,h]
  | projective i e b c =>
    let u:=quN7Z4a.Z7 (C.z γ) i
    let j:=A.seedJet γ i
    let y :=(j9 (C.s γ)).eval x
    change e+u*b≠0∧(e+u*b)*y=c*u at h
    have htX:t (MvPolynomial.X (Sum.inl i))=pair u j:= by
      change centre (jet (targetSeries B _))= _
      simp only [targetSeries,arcEval,MvPolynomial.eval₂Hom_X',Sum.elim_inl,hj,B.seed_value]
      simp [u,j,ArcFamily.seedJet,hγ,B]
    simp only [targetDen,targetNum,map_add,map_mul,htC,htX]
    refine ⟨isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr h.1),?_⟩
    have hy :y=c*u/(e+u*b) :=(eq_div_iff h.1).2 (by simpa [mul_comm] using h.2)
    apply TrivSqZeroExt.ext
    · exact h.2.symm
    · simp only [snd_add,DualNumber.snd_mul,fst_add,fst_mul,pair_fst,pair_snd,
        mul_zero,zero_mul,zero_add,add_zero,Target.slope]
      change c*j=(e+u*b)*(e*c*j/(e+u*b)^2)+j*b*y
      rw [hy]
      field_simp [h.1]
theorem proof :P5_7_3_3_4_1_7R.c3:= by
  classical
  intro C₀ inst C A x a r γ hγ _ hhit
  let B:=A ⟨γ,hγ⟩
  let f :=localEquation B (normalized C x r a)
  let y :=expand x (j9 (C.s γ))
  let n:=targetSeries B (targetNum r)
  let d:=targetSeries B (targetDen r)
  let ca :DoubleSeries :=zMG (zMG a)
  let a₀:=pO ca
  let n₀:=pO n
  let d₀:=pO d
  let b:=d₀*y-n₀
  obtain ⟨hd,ht⟩:=target_centre A hγ x r hhit
  change IsUnit (centre (jet d)) at hd
  change centre (jet n)=centre (jet d) *
    pair ((j9 (C.s γ)).eval x) (r.slope A γ) at ht
  have hdu:IsUnit d₀:=PowerSeries.isUnit_iff_constantCoeff.mpr
    (isUnit_iff_isUnit_fst.mp hd)
  have hb:constantCoeff b=0:= by
    have h:=congrArg fst ht
    change constantCoeff n₀ =
      constantCoeff d₀*(j9 (C.s γ)).eval x at h
    simpa only [b,y,map_sub,map_mul,expand_centre,sub_eq_zero] using h.symm
  have hunit :IsUnit (1-a₀*b) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    simp only [map_sub,map_one,map_mul,hb,mul_zero,sub_zero,isUnit_one]
  obtain ⟨U,hU⟩:=hunit
  let s :=(↑U⁻¹:Series)*b
  have hs :constantCoeff s=0:= by simp only [s,map_mul,hb,mul_zero]
  have hsu: (1-a₀*b)*s=b:= by
    rw [← hU]
    exact U.mul_inv_cancel_left b
  have hre :n₀*(1+a₀*s)+s=(d₀*(1+a₀*s))*y := by
    dsimp only [b] at hsu
    linear_combination hsu
  have hy : (C.markedEquation γ).eval (j9 (C.s γ))=0 :=
    C.sheet.identity γ (Finset.mem_filter.mp hγ).1
  have hroot : (seedFibre f).eval s=0:= by
    change (f.map pO).eval s=0
    have he :=normalized_eval B x a r pO s y hre
    change f.eval₂ pO s= _ at he
    rw [← eval₂_eq_eval_map,he,eval₂_eq_eval_map]
    change _ *(seedFibre (original B x)).eval y= _
    rw [original_fibre,eval_map_apply,hy,map_zero,mul_zero]
  refine ⟨s,hs,hroot,?_⟩
  intro v hv
  let u:=pair s v
  let k :=jet d*(1+jet ca*u)
  let l:=jet n*(1+jet ca*u)+u
  have hunit₀:IsUnit (1+a₀*s) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    simp only [map_add,map_one,map_mul,hs,mul_zero,add_zero,isUnit_one]
  have hk :IsUnit k :=isUnit_iff_isUnit_fst.mpr (hdu.mul hunit₀)
  obtain ⟨V,hV⟩:=hk
  let inverseJet:=(↑V⁻¹:Dual Series)*l
  have hY:l=k*inverseJet:= by rw [← hV]; exact (V.mul_inv_cancel_left l).symm
  have hfst:inverseJet.fst=y := by
    apply (hdu.mul hunit₀).mul_left_cancel
    exact (congrArg fst hY).symm.trans hre
  have hpair :inverseJet=pair y inverseJet.snd:=TrivSqZeroExt.ext hfst rfl
  have hzero :f.eval₂ jet u=0 :=
    TrivSqZeroExt.ext ((eval_fst f u).trans hroot) ((eval_snd f s v).trans hv.2)
  have hbase : (original B x).eval₂ jet inverseJet=0:= by
    rw [normalized_eval B x a r jet u inverseJet hY] at hzero
    exact ((show IsUnit k from ⟨V,hV⟩).pow C.g).mul_left_cancel
      (hzero.trans (mul_zero _).symm)
  have huc:centre u=0:= by
    exact TrivSqZeroExt.ext hs hv.1
  have hc:centre inverseJet=pair ((j9 (C.s γ)).eval x) (r.slope A γ) := by
    apply hd.mul_left_cancel
    have hh:=congrArg centre hY
    simpa only [l,k,map_add,map_mul,map_one,huc,mul_zero,add_zero,mul_one,ht] using hh.symm
  refine ⟨inverseJet.snd,congrArg snd hc,?_⟩
  rw [hpair] at hbase
  exact (original_snd B x inverseJet.snd).symm.trans (congrArg snd hbase)
end
end P5_7_3_3_4_1_7R_3
end
