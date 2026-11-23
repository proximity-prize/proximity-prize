import ProximityPrize.SubmissionLower.ZhieYVb
import ProximityPrize.SubmissionLower.ZVZMqYa
import ProximityPrize.SubmissionLower.ZUkTKja
set_option Elab.async false
open _root_ renaming Field → zrb, Fin.sum_univ_eq_sum_range → zdx, Fin.sum_univ_two → zs1, Finset.mul_sum → zxw, Finset.range → z4x, Finset.sum_add_distrib → zfW, Finset.sum_congr → zUo, Finset.sum_eq_zero → zYF, Fintype.card_fin → zgY, Fintype.card_prod → zeV, Fintype.card_sigma → zTU, Fintype.linearCombination → z3d, Fintype.linearCombination_apply → zGl, Fintype.sum_prod_type → zsI, Function.Injective → zq4, LinearMap.codRestrict → zTB, LinearMap.finrank_le_finrank_of_injective → zdv, LinearMap.ker → z83, LinearMap.pi → z9H, LinearMap.range → zWl, Module.Finite → zAa, Module.Finite.of_injective → zfv, Module.finrank → zsE, Module.finrank_pi → zJ6, MvPolynomial.monomial → ztt, Nat.add_le_add → z9f, Nat.cast_sub → zjK, Nat.lt_succ_of_le → zB1, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Polynomial.map_mul → zNl, Submodule → zpI, Submodule.finrank_mono → zFM, Submodule.inclusion → zwh, Submodule.inclusion_injective → zaX
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qbbqILc
open cu (ku)
open DP (CI)
open P6_7_1 (Rectangle aWs)
open qqW9Gbd (iL stock)
open aeL (Offset)
open qQCEOid (seedBudget windowBudget)
open scoped BigOperators
open private atOffset atWindow sum_shape_comm count_offsets count_windows from ProximityPrize.SubmissionLower.Z3BnLje
theorem count_budget (s :Rectangle) {u:ℕ} (hu:s.B≤u) :
    (∑ t:Offset s.box,seedBudget s.box t u)=bbE s u:= by
  unfold seedBudget windowBudget bbE
  simp_rw [sum_shape_comm]
  apply zUo rfl
  intro q hq
  apply zUo rfl
  intro j hj
  have hq' : q≤ s.B:=Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
  have hj' : j≤ min q s.J:=Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have ha :q-j≤u:=(Nat.sub_le ..).trans (hq'.trans hu)
  have ht (t:Offset s.box) (k :ℕ) :
      (if s.box.J-j≤t.val∧t.val<s.box.B+2*s.box.J-(q+min q s.box.J)+j ∧
        q-j≤u∧q≤k∧k≤ s.box.B+u-(q-j) then 1 else 0) =
      atOffset s.box q j t.val*atWindow s.box q j u k := by
    simp only [atOffset,atWindow]
    split_ifs <;> simp_all
  simp_rw [ht,← zxw,count_windows s.box hq' u,ite_eq_left ha]
  rw [← Finset.sum_mul,count_offsets s.box hq' hj']
  rfl
private theorem eta_sum (s :Rectangle) {q:ℕ} (hq:q≤ s.B) :
    (∑ j∈z4x (min q s.J+1),eta s q j) =
      ∑ _∈z4x (min q s.J+1),(s.B+s.J-q) := by
  let d:=min q s.J
  let f :=eta s q
  let n:=s.B+s.J-q
  change (∑ j∈z4x (d+1),f j) = ∑ _∈z4x (d+1),n
  have hd:d≤n:= by dsimp [d,n]; have :=min_le_right q s.J; omega
  have h (j:ℕ) (hj:j∈z4x (d+1)) :
      f j+f (d+1-1-j)=n+n:= by
    have hj' := Finset.mem_range.mp hj
    change n-d+2*j+(n-d+2*(d+1-1-j))=n+n
    omega
  have he :=zUo rfl h
  rw [zfW,Finset.sum_range_reflect,zfW] at he
  omega
private theorem active_bound (s :Rectangle) {u:ℕ} (hu:s.B≤u) :
    bbE s u≤(u+1)*ku s.box (fun q _=>s.B+s.J-q)+aWs s := by
  let S := ∑ q∈z4x (s.B+1),∑ j∈z4x (min q s.J+1),
    (eta s q j:ℤ)*((s.B:ℤ)-2*q+j)
  let N :=ku s.box (fun q _=>s.B+s.J-q)
  have he : (bbE s u:ℤ)=((u:ℤ)+1)*N+S:= by
    have hmass : (∑ q∈z4x (s.B+1),
        ∑ j∈z4x (min q s.J+1),(eta s q j:ℤ))=N := by
      unfold N ku
      push_cast
      refine zUo rfl fun q hq => ?_
      exact_mod_cast eta_sum s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hq))
    rw [← hmass]
    unfold bbE ku S
    push_cast only [Nat.cast_sum,Nat.cast_mul]
    change (∑ q∈z4x (s.B+1),∑ j∈z4x (min q s.J+1),_)= _
    simp only [zxw,← zfW]
    refine zUo rfl fun q hq=>zUo rfl fun j hj => ?_
    have hq' : q≤ s.B:=Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
    have hj' : j≤q:=(Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)).trans (min_le_left _ _)
    have hj'' : q-j≤u:=(Nat.sub_le ..).trans (hq'.trans hu)
    push_cast [zjK hq',zjK hj',zjK hj'']
    ring
  change bbE s u≤(u+1)*N+S.toNat
  have hS:S≤(S.toNat :ℤ) := by omega
  have hb: (bbE s u:ℤ)≤(((u+1)*N+S.toNat :ℕ) :ℤ) := by
    push_cast
    rw [he]
    exact add_le_add le_rfl hS
  exact_mod_cast hb
theorem ags (s :Rectangle) (h:ℕ) (hz :s.B≤ s.z) (ht:s.B≤ s.t) :
    h*localRows s 0+h*localRows s 1≤ iL h s+h*aWs s*(s.z+s.t+2) := by
  have h₀:=zBI (h*(s.t+1)) (active_bound s hz)
  have h₁:=zBI (h*(s.z+1)) (active_bound s ht)
  calc
    _=h*(s.t+1)*bbE s s.z+h*(s.z+1)*bbE s s.t:= by
      simp [localRows,cap,CI,Nat.mul_assoc]
    _≤_:=(z9f h₀ h₁).trans_eq (by unfold iL stock; ring)
end qbbqILc
end
section
set_option autoImplicit true
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace qbbqILc
noncomputable section
open Polynomial Matrix
open cu (Shape)
open DP (CI)
open Ge anc aeL qQCEOid
open P6_7_1 (Rectangle)
open scoped BigOperators Matrix Polynomial
open private expAt expAt_same expAt_other dLK from ProximityPrize.SubmissionLower.ZVQ2TVd
open private packed_tests from ProximityPrize.SubmissionLower.ZPoBc3d
private theorem cap_le (s :Rectangle) (side :Fin 2) (hz :s.B≤ s.z) (ht:s.B≤ s.t) :
    s.B≤ cap s side := by
  fin_cases side <;> assumption
private theorem anN (s :Rectangle) (side :Fin 2) :
    cap s side+cap s (CI side)=s.box.U:= by
  fin_cases side
  · rfl
  · exact Nat.add_comm _ _
private theorem input_zero {F:Type} [zrb F] (s :Rectangle) {P:Gm F}
    (hP:Boxed s P) (α:F) {t:Offset s.box} (v :Lh s.box t)
    (side :Fin 2) (i r :ℕ) (hi:cap s side< i∨cap s (CI side)< r) :
    (input α v P).coeff (expAt side i r)=0:= by
  have he :s.z<expAt side i r 0∨s.t<expAt side i r 1 := by
    fin_cases side
    · change s.z<expAt 0 i r 0∨s.t<expAt 0 i r 1
      rw [expAt_same,show expAt 0 i r 1=r from expAt_other 0 i r]
      exact hi
    · change s.z<expAt 1 i r 0∨s.t<expAt 1 i r 1
      rw [expAt_same,show expAt 1 i r 0=r from expAt_other 1 i r]
      exact (show s.t< i∨s.z< r from hi).symm
  change ((beE α P (a2N v) (v.1.val-a2N v)).coeff (dNE v)).coeff _ = _
  rw [beE,taylor_coeff,eval_eq_sum_range,MvPolynomial.coeff_sum]
  apply zYF
  intro k _
  rw [hasseDeriv_coeff]
  have hz :=hP (a2N v) (v.1.val-a2N v) (k+dNE v) _ he
  change (((P.coeff (a2N v)).coeff (v.1.val-a2N v)).coeff
    (k+dNE v)).coeff _=0 at hz
  simp only [MvPolynomial.algebraMap_eq,← map_natCast MvPolynomial.C,
    ← map_pow,mul_right_comm,← map_mul,MvPolynomial.coeff_C_mul,hz,mul_zero]
private def rectVector {F:Type} [zrb F] {s :Shape} {t:Offset s}
    (u:ℕ) (α:F) (side :Fin 2) (r :ℕ) :Gm F →ₗ[F] (SeedCol s t u→F) :=
  z9H fun v=>(MvPolynomial.lcoeff F (expAt side v.2.val r)).comp (input α v.1)
private def term {F:Type} [zrb F] {s :Shape} {t:Offset s}
    (α a b c:F) (side :Fin 2) (P:Gm F) (r d:ℕ)
    (row:Pivot s t) (v :Lh s t) (i:ℕ) :F :=
  (clearedEntry a b c row v).coeff (d-i)*(if i≤d then 1 else 0) *
    (input α v P).coeff (expAt side i r)
private theorem mulVec_rect {F:Type} [zrb F] {s :Shape} {t:Offset s}
    (u:ℕ) (α a b c:F) (side :Fin 2) (P:Gm F) (r :ℕ)
    (row:Pivot s t) (d:Fin (u+s.B+1)) :
    (seedMatrix s t u a b c).mulVec (rectVector u α side r P) (row,d) =
      ∑ v :Lh s t,∑ i∈z4x (u+1),term α a b c side P r d.val row v i:= by
  classical
  rw [Matrix.mulVec,dotProduct,zsI]
  refine zUo rfl fun v _ => ?_
  change (∑ i:Fin (u+1),term α a b c side P r d.val row v i.val)= _
  exact zdx (term α a b c side P r d.val row v) _
private theorem CJ {F:Type} [zrb F] (s :Rectangle)
    (α a b c:F) (side :Fin 2) (P:Gm F) (hP:Boxed s P)
    (h : ∀ (t:Offset s.box) (r :Fin (cap s (CI side)+1)),
      (seedMatrix s.box t (cap s side) a b c).mulVec
        (rectVector (cap s side) α side r.val P)=0)
    (t:Offset s.box) (r :Fin (s.box.U+1)) :
    (seedMatrix s.box t (s.box.U-r.val) a b c).mulVec (sourceVector (t:=t) α side r P)=0:= by
  classical
  let u:=cap s side
  ext ⟨row,d⟩
  change (seedMatrix s.box t (s.box.U-r.val) a b c).mulVec
    (rectVector (s.box.U-r.val) α side r.val P) (row,d)=0
  rw [mulVec_rect]
  by_cases hr :r.val≤ cap s (CI side)
  · have hU:=anN s side
    have hle :u≤ s.box.U-r.val := by dsimp [u]; omega
    have hsum (v :Lh s.box t) :
        (∑ i∈z4x (s.box.U-r.val+1),term α a b c side P r.val d.val row v i) =
        ∑ i∈z4x (u+1),term α a b c side P r.val d.val row v i:= by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hle))
      intro i _ hi
      unfold term
      rw [input_zero s hP α v side i r.val
        (Or.inl (Nat.le_of_not_gt (fun hi' => hi (Finset.mem_range.mpr hi')))),mul_zero]
    simp_rw [hsum]
    by_cases hd:d.val< u+s.B+1
    · have hh:=congrFun (h t ⟨r.val,zB1 hr⟩) (row,⟨d.val,hd⟩)
      rw [mulVec_rect] at hh
      exact hh
    · refine zYF fun v _=>zYF fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      unfold term
      split_ifs with hid
      · rw [coeff_eq_zero_of_natDegree_lt
          ((dLK s.box t a b c row v).trans_lt (by change s.B<d.val-i; omega)),
          zero_mul,zero_mul]
      · simp
  · refine zYF fun v _=>zYF fun i _ => ?_
    unfold term
    rw [input_zero s hP α v side i r.val (Or.inr (Nat.lt_of_not_ge hr)),mul_zero]
theorem O8:LocalPole := by
  classical
  intro F _ _ s hJ hB hz ht α side a b c hb
  let u:=cap s side
  let T:=Fin (cap s (CI side)+1)×Offset s.box
  let M (i:T) :=seedMatrix s.box i.2 u a b c
  let f (i:T) :=(M i).mulVecLin.comp (rectVector (t:=i.2) u α side i.1.val)
  have h (i:T) :zsE F (zWl (f i))≤ seedBudget s.box i.2 u:= by
    refine (zFM (LinearMap.range_comp_le_range _ _)).trans ?_
    change (M i).rank≤_
    exact (qcsMxUc.proof F s.box i.2 u a b c hb).trans
      (Finset.sum_le_sum fun k _=>qCgnalc.proof F s.box i.2 u k hJ hB)
  have hn: (∑ i:T,seedBudget s.box i.2 u)≤localRows s side := by
    rw [zsI]
    change (∑ _:Fin (cap s (CI side)+1),∑ t:Offset s.box,seedBudget s.box t u)≤_
    rw [Finset.sum_const,Finset.card_univ,zgY,
      nsmul_eq_mul,count_budget s (cap_le s side hz ht)]
    exact le_rfl
  obtain ⟨tests,htests⟩:=packed_tests f _ h hn
  exact ⟨tests,fun P hP hbox hzero =>
    normalized s.box α side a b c hb P hP
      (CJ s α a b c side P hbox (fun t r=>htests P hzero (r,t)))⟩
end
end qbbqILc
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace qbbqILc
noncomputable section
open K1 (K)
open cu (L)
open DP (jF zG Source aq7 complete OY Iy)
open Ge aY9 P6_7_1 qqW9Gbd Polynomial
open scoped BigOperators Polynomial
open private cb9 from ProximityPrize.SubmissionLower.Z
open private bqB cTI from ProximityPrize.SubmissionLower.Z
open private cHS from ProximityPrize.SubmissionLower.Z
private theorem ahx {h:ℕ} (hh:0<h) (hp:h<K1.p)
    (D:jF h) (Crt:zG D) :
    ∃ E :cAi D Crt,
      E.H.map genericPoint=adH D 0*adH D 1 ∧
      ∀ i α,(adH D i).eval α=0 →
        ∃ a b c,b≠0∧(Ua genericPoint E.num E.den).eval
          (algebraMap lN (kq lN) α)=residue i a b c:= by
  let B : ∀ i,bQl D Crt i:=a1P hh D Crt
  let den:=(B 0).den*(B 1).den
  let num :=C (B 1).den*(B 0).num+C (B 0).den*(B 1).num
  have hden:Uw den≠0:= by
    rw [show Uw den=Uw (B 0).den*Uw (B 1).den from map_mul _ _ _]
    exact mul_ne_zero (B 0).specialDen (B 1).specialDen
  have hmonic: (bfF D).Monic :=
    (aVZ hh D 0).monic.mul (aVZ hh D 1).monic
  have hc (i:Fin 2) (α:lN) (hr : (adH D i).eval α=0)
      (hb: ((D.constant i).map alL).eval α≠0) : (Ua genericPoint num den).eval
      (algebraMap lN (kq lN) α) =
      residue i (-((D.offset i).map alL).eval α)
        (((D.constant i).map alL).eval α) (((D.slope i).map alL).eval α) := by
    dsimp only [num,den]
    rw [cXv _ _ _ _ _ (bqB (B 0).specialDen) (bqB (B 1).specialDen)]
    simpa only [zs1] using cTI B i α hr hb
  refine ⟨⟨bfF D,num,den,hmonic,?_,hden,?_,bqB hden,
    gq6 hh hp D _ hc⟩,?_,?_⟩
  · rw [bfF,zNl,b9t,b9t,Iy]
  · dsimp only [num,den]
    rw [cXv _ _ _ _ _ (B 0).specialDen (B 1).specialDen,
      (B 0).specialLift,(B 1).specialLift,OY,zs1]
  · exact zNl _
  · intro i α hr
    exact ⟨_,_,_,cHS hh D i hr,hc i α hr (cHS hh D i hr)⟩
private theorem boxed_map {F G:Type} [zrb F] [zrb G] (f :F →+* G)
    {s :Rectangle} {P:Gm F} (hP:Boxed s P) :Boxed s (avv f P) := by
  intro j i d e he
  simpa [aQu,avv,Polynomial.coeff_map,MvPolynomial.coeff_map] using
    (congrArg f (hP j i d e he)).trans (map_zero f)
private theorem boxed_combination {F ι:Type} [zrb F] [Fintype ι] {s :Rectangle}
    {P:ι→Gm F} (hP : ∀ i,Boxed s (P i)) (v :ι→F) :
    Boxed s (z3d F P v) := by
  intro j i d e he
  change c7p j i d e (z3d F P v)=0
  rw [zGl,map_sum]
  exact zYF fun k _=> by rw [map_smul]; exact smul_eq_zero_of_right _ (hP k j i d e he)
private theorem simple_rank {h:ℕ} (hh:0<h) {D:jF h} {Crt:zG D}
    (E :cAi D Crt)
    (hH :E.H.map genericPoint=adH D 0*adH D 1)
    (hc : ∀ i α,(adH D i).eval α=0 →
      ∃ a b c,b≠0∧(Ua genericPoint E.num E.den).eval
        (algebraMap lN (kq lN) α)=residue i a b c)
    (s :Rectangle) (hJ:s.J≤ s.B) (hB:s.B<K1.p) (hz :s.B≤ s.z) (ht:s.B≤ s.t)
    {ι:Type} [Fintype ι] (P:ι→Gm lN)
    (hP : ∀ k,adk s.box (P k)) (hbox : ∀ k,Boxed s (P k))
    {n:ℕ} (M:Matrix (Fin n) ι lN)
    (hM : ∀ v,M.mulVec v=0↔a0X s.box (E.H.map genericPoint)
      (Ua genericPoint E.num E.den) (z3d lN P v)) :
    M.rank≤h*localRows s 0+h*localRows s 1 := by
  classical
  let F:=lN
  let _:CharP L K1.p:=charP_of_injective_ringHom (algebraMap K L).injective K1.p
  let _:CharP F K1.p :=
    charP_of_injective_ringHom (f :=alL) (b4F.comp Polynomial.C_injective) K1.p
  let R (i:Fin 2) :=(adH D i).roots.toFinset
  have hm (i:Fin 2) : (adH D i).Monic:=(aVZ hh D i).monic.map _
  have hR (i:Fin 2) (α:F) :α∈R i↔(adH D i).eval α=0 :=
    Multiset.mem_toFinset.trans (mem_roots (hm i).ne_zero)
  have hcard (i:Fin 2) : (R i).card≤h :=
    (Multiset.toFinset_card_le _).trans ((card_roots' _).trans_eq
      (((aVZ hh D i).monic.natDegree_map _).trans
        (aVZ hh D i).natDegree_eq))
  choose a b c hb hv using fun i (r :R i)=>hc i r.val ((hR i r.val).mp r.property)
  choose tests htests using fun i (r :R i) =>
    O8 F s hJ hB hz ht r.val i (a i r) (b i r) (c i r) (hb i r)
  let T:=Σ i:Fin 2,R i×Fin (localRows s i)
  let f : (ι→F) →ₗ[F] (T→F) :=z9H fun r =>
    (LinearMap.proj r.2.2).comp ((tests r.1 r.2.1).comp (z3d F P))
  have hker :z83 f≤z83 M.mulVecLin:= by
    intro v hfv
    apply LinearMap.mem_ker.mpr
    apply (hM v).mpr
    apply cb9 s.box E.genericPoles
    intro t
    let α:=E.genericPoles.root t
    have hr : (E.H.map genericPoint).eval α=0:=E.genericPoles.aiq t
    rw [hH,eval_mul,mul_eq_zero] at hr
    obtain ⟨i,hi⟩ : ∃ i,(adH D i).eval α=0 :=
      hr.elim (fun e=>⟨0,e⟩) (fun e=>⟨1,e⟩)
    let r :R i:=⟨α,(hR i α).mpr hi⟩
    apply anc.gDE _ _ _ _ _ _ (E.genericPoles.aiq t) (hv i r)
    apply htests i r _ (ddL hP v) (boxed_combination hbox v)
    exact funext fun k=>congrFun (LinearMap.mem_ker.mp hfv) ⟨i,r,k⟩
  have hb:=(zWl f).finrank_le
  simp only [zJ6,zTU,zeV,zgY,
    Fintype.card_coe,zs1,T] at hb
  have hcap:=z9f (ztf (localRows s 0) (hcard 0))
    (ztf (localRows s 1) (hcard 1))
  have hk :=zFM hker
  have hf :=f.finrank_range_add_finrank_ker
  have hm' := M.mulVecLin.finrank_range_add_finrank_ker
  have hle :zsE F (zWl M.mulVecLin) ≤
      zsE F (zWl f) :=
    Nat.le_of_add_le_add_right ((Nat.add_le_add_left hk _).trans_eq (hm'.trans hf.symm))
  exact hle.trans (hb.trans hcap)
theorem proof :qqW9Gbd.c2 := by
  classical
  intro h D Crt word s W hh hp hJ hB hz ht
  obtain ⟨E,hH,hc⟩:=ahx hh hp D Crt
  let A:=rectContacted h word s W
  let C:=complete Crt word s.box W ⊓ seedBox s.z s.t
  have hA:A≤aq7 h word s.box W:=inf_le_left
  have hC:C≤A:=inf_le_inf inf_le_left le_rfl
  let _:zAa L (aq7 h word s.box W) :=dPs h word s.box W
  let _:zAa L A:=zfv _ (zaX hA)
  let _:zAa L C:=zfv _ (zaX hC)
  let d:=zsE L A
  let basis :=Module.finBasis L A
  let P:Fin d→Source := fun k=>basis k
  have hP (k :Fin d) :adk s.box (P k) :=dPt (basis k).property.1
  obtain ⟨n,M,hs,hg⟩:=bzR.proof E s.box (Fin d) P hP
  have hgen:=simple_rank hh E hH hc s hJ hB hz ht _
    (fun k=>gp2 alL (hP k))
    (fun k=>boxed_map alL (show Boxed s (P k) from (basis k).property.2)) _ hg
  have hrank :=((gtP M).trans hgen).trans (ags s h hz ht)
  let f :=(M.map Uv).mulVecLin
  have hf (v :Fin d→L) :
      z3d L P v=((basis.equivFun.symm v :A) :Source) := by
    rw [zGl,Module.Basis.equivFun_symm_apply]
    symm
    simpa only [map_smul,Submodule.subtype_apply,P] using
      map_sum A.subtype (fun k=>v k•basis k) Finset.univ
  have hk (v :z83 f) : ((basis.equivFun.symm v.val :A) :Source)∈C:= by
    have hv :=(hs v.val).mp (LinearMap.mem_ker.mp v.property)
    rw [hf] at hv
    exact ⟨⟨(basis.equivFun.symm v.val).property.1,hv⟩,(basis.equivFun.symm v.val).property.2⟩
  let g:z83 f →ₗ[L] C :=
    zTB _ ((A.subtype.comp basis.equivFun.symm.toLinearMap).comp
      (z83 f).subtype) hk
  have hginj:zq4 g:= fun _ _ he =>
    Subtype.ext (basis.equivFun.symm.injective (Subtype.ext
      (congrArg (fun x :C=>(x :Source)) he)))
  have hkd:=zdv hginj
  have hdf :=f.finrank_range_add_finrank_ker
  rw [zJ6,zgY] at hdf
  change zsE L (zWl f)≤_ at hrank
  change d≤ iL h s+h*aWs s*(s.z+s.t+2)+Module.finrank L C
  omega
end
end qbbqILc
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace qAIJqFa
noncomputable section
open K1 (I)
open cu (L Shape ku)
open DP Polynomial
open P6_7_1 (seedBox)
open scoped BigOperators
open private dPL from ProximityPrize.SubmissionLower.Z
open private X3.mk cut bRG.sx bRG.sy bRG.sv bRG.Sl asn bfk emN b9x c04 b9s dNu gpc c5u bRG.cbD bRG.cbE bRG.cbC bRG.bKs eAb from ProximityPrize.SubmissionLower.Z
private abbrev bk3 (z t:ℕ) :=Fin (z+1)×Fin (t+1)
private def dcI {z t:ℕ} (i:bk3 z t) :Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![i.1.val,i.2.val]
private theorem d4P {z t:ℕ} {e :Fin 2 →₀ ℕ} (hz :e 0≤z) (ht:e 1≤t) :
    ∃ i:bk3 z t,dcI i=e := by
  refine ⟨⟨⟨e 0,zB1 hz⟩,⟨e 1,zB1 ht⟩⟩,?_⟩
  apply Finsupp.ext
  intro k
  fin_cases k <;> rfl
private abbrev width (s :Shape) (q j:ℕ) :=s.m+min q s.J-(q+2*j)
private abbrev bQ2 (s :Shape) (z t:ℕ) :=
  (Σ q:Fin (s.B+1),Σ j:Fin (min q.val s.J+1),Fin (width s q.val j.val))×bk3 z t
private theorem efm (s :Shape) (z t:ℕ) :
    Fintype.card (bQ2 s z t)=ku s (width s)*((z+1)*(t+1)) := by
  unfold bQ2
  rw [zeV,ku]
  simp only [bk3,zeV,zTU,zgY,
    ← zdx]
private def generators (s :Shape) (z t:ℕ) (i:bQ2 s z t) :=
  cut s (bfk i.1.1.val (min i.1.1.val s.J) i.1.2.1.val i.1.2.2.val (dcI i.2))
private def avt (s :Shape) (z t:ℕ) :=Submodule.span L (Set.range (generators s z t))
private abbrev preimage (s :Shape) (z t:ℕ) :zpI L Source :=
  (avt s z t).comap (cut s)
private theorem efo (s :Shape) {z t:ℕ} (q k a :ℕ) (e :Fin 2 →₀ ℕ)
    (hq:q≤ s.B) (hk :k≤ min q s.J) (hz :e 0≤z) (ht:e 1≤t) :
    bfk q (min q s.J) k a e∈preimage s z t:= by
  change cut s _∈avt s z t
  have hd:=min_le_left q s.J
  by_cases ha :a<width s q k
  · obtain ⟨i,rfl⟩:=d4P hz ht
    exact Submodule.subset_span
      ⟨(⟨⟨q,zB1 hq⟩,⟨⟨k,zB1 hk⟩,⟨a,ha⟩⟩⟩,i),rfl⟩
  · unfold width at ha
    rw [LinearMap.mem_ker.mp (emN s q (min q s.J) k a e (by omega))]
    exact (avt s z t).zero_mem
private theorem gqB (s :Shape) {z t:ℕ} (a b j:ℕ) (e :Fin 2 →₀ ℕ)
    (hq:b+j≤ s.B) (hj:j≤ s.J) (hz :e 0≤z) (ht:e 1≤t) :
    bRG.Sl (ztt e 1)*bRG.sx^a*asn^b*bRG.sv^j∈preimage s z t:= by
  let q:=b+j
  let d:=min q s.J
  have hd:d≤q:=min_le_left _ _
  have hjd:j≤d:=le_min (Nat.le_add_left _ _) hj
  let p:=bRG.Sl (ztt e 1)*bRG.sx^a*bRG.sv^j*asn^(q-d)
  have hpow:asn^b=asn^(q-d)*asn^(d-j) := by
    rw [← pow_add,show q-d+(d-j)=b by dsimp only [q] at *; omega]
  have hexpand:p*(bRG.sy+bRG.sx*bRG.sv)^(d-j)∈preimage s z t:= by
    apply b9x
    intro k hk
    have hV:d-k=j+(d-j-k) := by omega
    have hgen:=efo s q k (a+(d-j-k)) e hq (by omega) hz ht
    change bfk q d k (a+(d-j-k)) e∈_ at hgen
    rw [bfk,hV] at hgen
    dsimp only [p]
    rw [dNu]
    exact hgen
  dsimp only [p] at hexpand
  change (bRG.Sl (ztt e 1)*bRG.sx^a*bRG.sv^j*asn^(q-d)) *
    asn^(d-j)∈preimage s z t at hexpand
  rw [b9s (bRG.Sl (ztt e 1)*bRG.sx^a),mul_assoc
    (bRG.Sl (ztt e 1)*bRG.sx^a),← hpow] at hexpand
  exact hexpand
private theorem gDR (s :Shape) {z t:ℕ} (x r :L) (a b j:ℕ) (e :Fin 2 →₀ ℕ)
    (hq:b+j≤ s.B) (hj:j≤ s.J) (hz :e 0≤z) (ht:e 1≤t) :
    bRG.Sl (ztt e 1)*(bRG.sx+algebraMap L Source x)^a *
      (asn+algebraMap L Source r)^b*bRG.sv^j∈preimage s z t:= by
  let p:=bRG.Sl (ztt e 1)*bRG.sv^j
  have h: (p*(asn+algebraMap L Source r)^b) *
      (bRG.sx+algebraMap L Source x)^a∈preimage s z t:= by
    apply c04
    intro l _
    have h' : (p*bRG.sx^l)*(asn+algebraMap L Source r)^b∈preimage s z t:= by
      apply c04
      intro k hk
      dsimp only [p]
      rw [b9s]
      exact gqB s l k j e (by omega) hj hz ht
    rw [mul_right_comm]
    exact h'
  rw [mul_right_comm p] at h
  dsimp only [p] at h
  rw [b9s] at h
  exact h
private theorem duH {h W z t:ℕ} {s :Shape} (x r :L)
    (P: (Aw h s W ⊓ seedBox z t:zpI L Source)) :
    cut s (Km x r P.val)∈avt s z t:= by
  change P.val∈(preimage s z t).comap (Km x r).toLinearMap
  apply eAb
  intro j b a e hne
  have hel:awN h s W j b a e := by
    by_contra hn
    exact hne (P.property.1 j b a e hn)
  have hz :e 0≤z :=le_of_not_gt fun hn=>hne (P.property.2 j b a e (Or.inl hn))
  have ht:e 1≤t:=le_of_not_gt fun hn=>hne (P.property.2 j b a e (Or.inr hn))
  change Km x r _∈preimage s z t
  rw [← c5u,gpc,smul_mul_assoc,smul_mul_assoc,smul_mul_assoc,map_smul]
  apply (preimage s z t).smul_mem
  simp only [map_mul,map_pow,bRG.cbD,bRG.cbE,bRG.cbC,bRG.bKs]
  exact gDR s x r a b j e hel.1 hel.2.1 hz ht
theorem bound (h:ℕ) (word:I→L) (s :Shape) (W z t:ℕ) :
    zsE L (Aw h s W ⊓ seedBox z t:zpI L Source) ≤
      (z+1)*(t+1)*262144*ku s (fun q j=>s.m+min q s.J-(q+2*j)) +
        zsE L (aq7 h word s W ⊓ seedBox z t:zpI L Source) := by
  classical
  let A:=Aw h s W ⊓ seedBox z t
  let C:=aq7 h word s W ⊓ seedBox z t
  let R:=avt s z t
  let _:zAa L (Aw h s W) :=
    zfv (dPL h s W).toLinearMap (dPL h s W).injective
  have hA:A≤Aw h s W:=inf_le_left
  let _:zAa L A:=zfv (zwh hA)
    (zaX hA)
  have hC:C≤A:= fun _ P=>⟨P.1.1,P.2⟩
  let _:zAa L C:=zfv (zwh hC)
    (zaX hC)
  let _:zAa L R:=Module.Finite.span_of_finite L (Set.finite_range (generators s z t))
  let f :A →ₗ[L] (I→R) :=z9H fun i =>
    zTB R
      (((cut s).comp (Km (ad0 i) (word i)).toLinearMap).domRestrict A)
      (duH (ad0 i) (word i))
  let g:f.ker →ₗ[L] C:=zTB C (A.subtype.comp f.ker.subtype) (by
    intro P
    refine ⟨⟨P.val.property.1,?_⟩,P.val.property.2⟩
    intro i a b j e hab
    exact congrArg (fun u:I→R=>(u i).val (X3.mk j b a e hab))
      (LinearMap.mem_ker.mp P.property))
  have hg:zq4 g:= by
    intro P Q hPQ
    exact Subtype.ext (Subtype.ext (congrArg (fun v :C=>v.val) hPQ))
  have hlocal:zsE L R≤ku s (width s)*((z+1)*(t+1)) := by
    rw [← efm]
    exact finrank_range_le_card (R:=L) (generators s z t)
  have htarget :zsE L (I→R)≤(z+1)*(t+1)*262144*ku s (width s) := by
    rw [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,
      ProximityPrize.Benchmark.IRSProfile.card_index,smul_eq_mul]
    exact (zBI _ hlocal).trans_eq (by ac_rfl)
  change zsE L A≤_+Module.finrank L C
  have hrange :=(zWl f).finrank_le.trans htarget
  have hker :=zdv hg
  exact f.finrank_range_add_finrank_ker.symm.le.trans (z9f hrange hker)
theorem proof :qqW9Gbd.c1 := by
  intro h word s W
  exact bound h word s.box W s.z s.t
end
end qAIJqFa
end
section
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qnX77sd
noncomputable section
open cu (ku)

open P6_7_2 (Input Bs rectCutoff cutoff rectVolume poleExtra rankSum)
theorem slope_eq (s :P6_7_1.Rectangle) :P6_7_1.aWs s=poleExtra s.box := by
  have k : ∀ q∈z4x (s.B+1),∀ j∈z4x (min q s.J+1),
      ((s.B+s.J-q-min q s.J+2*j:ℕ) :ℤ)*((s.B:ℤ)-2*q+j) =
        (((s.B+s.J+2*j-(q+min q s.J))*(2*s.B+j+1-2*q) :ℕ) :ℤ) -
          (((s.B+1)*(s.B+s.J+2*j-(q+min q s.J)) :ℕ) :ℤ) := by
    intro q hq j hj
    have :=Finset.mem_range.1 hq
    have :=Finset.mem_range.1 hj
    have :=min_le_left q s.J
    have e2 : ((2*s.B+j+1-2*q:ℕ) :ℤ)=2*s.B+j+1-2*q:= by omega
    rw [show s.B+s.J-q-min q s.J+2*j=s.B+s.J+2*j-(q+min q s.J) by omega]
    push_cast [e2]
    ring
  dsimp only [P6_7_1.aWs,poleExtra,ku,P6_7_1.Rectangle.box]
  rw [zUo rfl fun q hq=>zUo rfl (k q hq)]
  simp only [Finset.sum_sub_distrib,← Nat.cast_sum,zxw]
  omega
private theorem width_calc (h lo m B R:ℕ) (hl:lo≤h) (hu:h≤131071)
    (hb:2*R≤B) (hm:B*(131071-lo)+2*lo*R+1≤ m*P6.dw) :
    ∀ q≤B,∀ j,q*(131071-h)≤ cutoff h R ⟨m,B,0,0⟩+1+j:= by
  intro q hq j
  have hlim:h-lo+ (131071-h)=131071-lo:= by omega
  have hlen:h-lo+lo=h:= by omega
  have hdelta :=zBI (h-lo) hb
  rw [← hlim,Nat.mul_add] at hm
  have hr :2*h*R=2*lo*R+(h-lo)*(2*R) := by
    calc
      2*h*R=h*(2*R) := by ring
      _=(h-lo+lo)*(2*R) := by rw [hlen]
      _ = _:= by ring
  have hq' := ztf (131071-h) hq
  change _≤ m*P6.dw-1-2*h*R+1+j
  rw [hr]
  rw [Nat.mul_comm (h-lo) B] at hdelta
  omega
theorem proof :P6_7_2.c4 := by
  intro b x P r hrect
  obtain ⟨hz,ht,_,_⟩:=hrect
  obtain ⟨hlo,hhi⟩:=x.kA
  change (b.kA.lo:ℤ)≤x.M.iF at hlo
  change x.M.iF≤(b.kA.hi:ℤ) at hhi
  obtain ⟨b1,b2,b3,b4,b5,b6⟩:0<b.kA.lo∧b.kA.hi≤32680 ∧
      (Bs b).terminal.J≤(Bs b).terminal.B∧(Bs b).terminal.B<K1.p ∧
      2*(Bs b).dI≤(Bs b).terminal.B ∧
      (Bs b).terminal.B*(131071-b.kA.lo)+2*b.kA.lo*(Bs b).dI+1 ≤
        (Bs b).terminal.m*P6.dw:= by
    cases b <;> decide
  have hh:x.h≤32680:= by dsimp [Input.h]; omega
  have hl:b.kA.lo≤x.h:= by dsimp [Input.h]; omega
  let R:P6_7_1.Rectangle :=⟨(Bs b).terminal.m,(Bs b).terminal.B,(Bs b).terminal.J,r.z,r.t⟩
  have ha :=qqW9Gbd.bT9 (h:=x.h) (by omega) R (rectCutoff b x.h)
    (fun q hq j _=>width_calc x.h _ _ _ _ hl (by omega) b5 b6 q hq j)
  have h1 :=qAIJqFa.proof x.h x.word R (rectCutoff b x.h)
  have h2 :=qbbqILc.proof x.h P.D P.crt x.word R (rectCutoff b x.h) (by omega)
    (hh.trans_lt (by decide)) b3 b4 hz ht
  have he :=qqW9Gbd.telescope P.crt x.word R.box (P6_7_1.seedBox R.z R.t) (by omega)
    (rectCutoff b x.h)
  change rectVolume b x.h r+_≤_ at ha
  change _≤ rankSum P r at he
  change _≤qqW9Gbd.contactDebit R + x.h*poleExtra R.box*(R.z+R.t+2)+_
  rw [← slope_eq]
  omega
end
end qnX77sd
end
