import ProximityPrize.SubmissionLower.Zmk5EEe
set_option Elab.async false
open _root_ renaming Field → zrb, Fin.cases → zEX, Fin.cons_succ → zVG, Fin.cons_zero → zhe, Fintype.equivFin → z5E, Function.Injective → zq4, Nat.cast_add → z6H, Nat.cast_sub → zjK, Polynomial → zM1, RingHom.id → zz4
section
namespace qvWVeNa
noncomputable section
open Polynomial Finset
variable {E :Type} [zrb E]
private theorem choose_labels [Infinite E] (B:Finset E) (n:ℕ) :
    ∃ v :Fin n→E,zq4 v ∧ ∀ i j,i≠j→v i+v j∉B:= by
  classical
  induction n with
  | zero=>exact ⟨Fin.elim0,fun {i} => Fin.elim0 i,fun i=>Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨v,hv,hB⟩:=ih
    let avoid :=(univ :Finset (Fin n)).biUnion (fun i=>B.image (fun b=>b - v i))
    obtain ⟨u,hu⟩:=((univ.image v)∪avoid).exists_notMem
    have hne (i:Fin n) :u≠v i:= fun e =>
      hu (mem_union_left _ (mem_image.mpr ⟨i,mem_univ _,e.symm⟩))
    have hsum (i:Fin n) :u+v i∉B:= fun h =>
      hu (mem_union_right _ (mem_biUnion.mpr
        ⟨i,mem_univ _,mem_image.mpr ⟨u+v i,h,add_sub_cancel_right _ _⟩⟩))
    refine ⟨Fin.cons u v,?_,?_⟩
    · intro i j
      refine zEX ?_ (fun a => ?_) i <;> refine zEX ?_ (fun b => ?_) j
      · intro _
        rfl
      · simpa only [zhe,zVG] using (hne b).elim
      · simpa only [zVG,zhe] using (Ne.symm (hne a)).elim
      · intro e
        exact congrArg Fin.succ (hv (by simpa only [zVG] using e))
    · intro i j
      refine zEX ?_ (fun a => ?_) i <;> refine zEX ?_ (fun b => ?_) j
      · exact fun e=>(e rfl).elim
      · intro _
        simpa only [zhe,zVG] using hsum b
      · intro _
        simpa only [zhe,zVG,add_comm (v a) u] using hsum a
      · intro e
        simpa only [zVG] using hB a b (fun h=>e (congrArg Fin.succ h))
private theorem choose_Q (s :ℕ) (hs :0<s) :
   ∃ Q:zM1 E,Q.natDegree≤ s∧Q.coeff s=1∧Q.derivative≠0:= by
 rcases s with _ | s
 · omega
 rcases s with _ | s
 · exact ⟨Polynomial.X,by simp,by simp,by simp⟩
 · let Q:zM1 E :=Polynomial.X^(s+2)+Polynomial.X
   refine ⟨Q,?_,?_,?_⟩
   · exact (natDegree_add_le _ _).trans (by simp)
   · simp [Q,coeff_X]
   · intro h
     have hc:=congrArg (fun p:zM1 E=>p.coeff 0) h
     simp [Q,coeff_X_pow] at hc
private theorem choose_graphs [Infinite E] {I:Type} [Fintype I] (s :ℕ) :
    ∃ p:I→zM1 E,
      (∀ i,(p i).natDegree≤ s)∧zq4 (fun i=>(p i).coeff s) ∧
      (∀ i j,i≠j → ∀ x,(p i-p j).eval x=0→(p i-p j).derivative.eval x≠0) ∧
      (∀ i j l,i≠j→i≠l→j≠l → ∀ x,
        (p i).eval x=(p j).eval x→(p i).eval x≠(p l).eval x) := by
  classical
  let e :=z5E I
  by_cases hs :s=0
  · subst s
    let label := fun i:I=>Infinite.natEmbedding E (e i).val
    have hinj:zq4 label :=
      (Infinite.natEmbedding E).injective.comp (Fin.val_injective.comp e.injective)
    refine ⟨fun i=>C (label i),by simp,by simpa,?_,?_⟩
    · intro i j h x hx
      exact (h (hinj (by simpa [eval_sub,sub_eq_zero] using hx))).elim
    · intro i j l h _ _ x hx
      exact (h (hinj (by simpa using hx))).elim
  obtain ⟨Q,hdeg,hcoeff,hder⟩:=choose_Q (E :=E) s (Nat.pos_of_ne_zero hs)
  let B:= Q.derivative.roots.toFinset.image (fun x => -Q.eval x)
  obtain ⟨v,hv,hB⟩:=choose_labels B (Fintype.card I)
  let label :=v ∘ e
  have hinj:zq4 label :=hv.comp e.injective
  let p (i:I) :=C (label i)*Q+C (label i)^2
  have hp (i j:I) :p i - p j=C (label i-label j)*(Q+C (label i+label j)) := by
    simp only [p,map_sub,map_add]
    ring
  have hroot (i j:I) (h:i≠j) (x :E) (hx : (p i-p j).eval x=0) :
      Q.eval x+(label i+label j)=0:= by
    rw [hp,eval_mul,eval_C,eval_add,eval_C] at hx
    exact (mul_eq_zero.mp hx).resolve_left (sub_ne_zero.mpr (hinj.ne h))
  refine ⟨p,?_,?_,?_,?_⟩
  · intro i
    have hc: (C (label i)^2).natDegree=0:= by rw [← map_pow]; simp
    exact (natDegree_add_le _ _).trans
      (max_le ((natDegree_C_mul_le _ _).trans hdeg) (by rw [hc]; exact Nat.zero_le _))
  · intro i j he
    apply hinj
    simpa [p,← map_pow,coeff_add,coeff_C_mul,hcoeff,coeff_C,hs,Ne.symm hs] using he
  · intro i j hij x hx
    have hn (e :Q.derivative.eval x=0) :False := by
      apply hB (z5E I i) (z5E I j) ((z5E I).injective.ne hij)
      exact mem_image.mpr ⟨x,Multiset.mem_toFinset.mpr ((mem_roots hder).mpr e),
        (eq_neg_of_add_eq_zero_right (hroot i j hij x hx)).symm⟩
    rw [hp,derivative_C_mul,derivative_add,derivative_C,add_zero,eval_mul,eval_C]
    exact mul_ne_zero (sub_ne_zero.mpr (hinj.ne hij)) hn
  · intro i j l hij hil hjl x hx hy
    have h₁:=hroot i j hij x (by rw [eval_sub,hx,sub_self])
    have h₂:=hroot i l hil x (by rw [eval_sub,hy,sub_self])
    apply hjl
    apply hinj
    linear_combination h₁ - h₂
theorem exists_model [IsAlgClosed E] (s :ℕ) (n t:Fin 3→ℕ) :
   ∃ m:Model E n t,Good s m:= by
 classical
 obtain ⟨p,hp,hi,ht,h3⟩:=choose_graphs (E :=E) (I:=bzm n) s
 let B:=(univ :Finset (bzm n×bzm n)).biUnion (fun ij=>(p ij.1-p ij.2).roots.toFinset)
 let f :=B.finite_toSet.infinite_compl.natEmbedding _
 let e :=z5E (bzm t)
 let b (i:bzm t) :E :=(f (e i).val).val
 let z (i:Fin 3) :E :=Infinite.natEmbedding E i.val
 refine ⟨⟨b,p,z⟩,⟨(Infinite.natEmbedding E).injective.comp Fin.val_injective,?_,
   hp,hi,?_,ht,h3⟩⟩
 · exact Subtype.val_injective.comp (f.injective.comp (Fin.val_injective.comp e.injective))
 · intro i j hij l h
   have hne :p i-p j≠0:= fun he=>hij (hi (congrArg (fun r :zM1 E=>r.coeff s)
     (sub_eq_zero.mp he)))
   apply (f (e l).val).property
   exact mem_biUnion.mpr ⟨(i,j),mem_univ _,Multiset.mem_toFinset.mpr ((mem_roots hne).mpr h)⟩
end
end qvWVeNa
end
section
namespace qvWVeNa
noncomputable section
open qFwMjQd (aax)
open Finset Polynomial
variable {E :Type} [zrb E] [IsAlgClosed E] {n t:Fin 3→ℕ} {s :ℕ} {m:Model E n t}
theorem pair_points (hm:Good s m) (i j:Fin 3) (hij:i≠j) :
    ∃ C:Finset (E×E),C.card≤pairDegree s (n i) (t i) (n j) (t j) ∧
      (∀ v∈C,arS (zz4 E) s m false false i j (mark v 0)) ∧
      ∀ {F:Type} [zrb F] (k :E →+* F) (q:aax F),
        arS k s m false false i j q → ∃ v∈C,q 0=k v.1∧q 1=k v.2 := by
  classical
  let bp (i j:Fin 3) (u:Fin (t i)×Fin (n j)) :E×E :=
    let x :=m.base ⟨i,u.1⟩
    (x,(m.graph ⟨j,u.2⟩).eval x)
  let B (i j:Fin 3) :=univ.image (bp i j)
  let Δ (u:Fin (n i)×Fin (n j)) :=m.graph ⟨i,u.1⟩ - m.graph ⟨j,u.2⟩
  let pt (u:Fin (n i)×Fin (n j)) (x :E) :E×E :=(x,(m.graph ⟨i,u.1⟩).eval x)
  let G:=univ.biUnion (fun u=>(Δ u).roots.toFinset.image (pt u))
  let U:=(B i j∪B j i)∪G
  have hne (u:Fin (n i)×Fin (n j)) :Δ u≠0 :=
    graph_sub_ne hm (fun e=>hij (congrArg Sigma.fst e))
  have bcard (i j:Fin 3) : (B i j).card≤t i*n j :=
    card_image_le.trans_eq (by simp)
  have gcard:G.card≤n i*n j*s := by
    calc
      G.card ≤ ∑ u:Fin (n i)×Fin (n j),s :=
        card_biUnion_le.trans (sum_le_sum fun u _ =>
          card_image_le.trans ((Multiset.toFinset_card_le _).trans
            ((card_roots' _).trans ((natDegree_sub_le _ _).trans
              (max_le (hm.graph_degree ⟨i,u.1⟩) (hm.graph_degree ⟨j,u.2⟩))))))
      _ = _:= by simp
  have bhit (i j:Fin 3) (u:Fin (t i)×Fin (n j)) :
      arS (zz4 E) s m false false i j (mark (bp i j u) 0) :=
    ⟨(principal_hit _ hm _ _).mpr (Or.inl ⟨u.1,rfl⟩),
      (principal_hit _ hm _ _).mpr (Or.inr ⟨u.2,rfl⟩)⟩
  refine ⟨U,?_,?_,?_⟩
  · exact (card_union_le _ _).trans (add_le_add
      ((card_union_le _ _).trans (add_le_add (bcard i j) (by simpa [Nat.mul_comm] using bcard j i))) gcard)
  · intro v hv
    rcases mem_union.mp hv with hv | hv
    · rcases mem_union.mp hv with hv | hv
      · obtain ⟨u,_,rfl⟩:=mem_image.mp hv
        exact bhit i j u
      · obtain ⟨u,_,rfl⟩:=mem_image.mp hv
        exact ⟨(bhit j i u).2,(bhit j i u).1⟩
    · obtain ⟨u,_,hu⟩:=mem_biUnion.mp hv
      obtain ⟨x,hx,rfl⟩:=mem_image.mp hu
      have hh:=(mem_roots (hne u)).mp (Multiset.mem_toFinset.mp hx)
      change (m.graph ⟨i,u.1⟩ - m.graph ⟨j,u.2⟩).eval x=0 at hh
      rw [eval_sub,sub_eq_zero] at hh
      exact ⟨(principal_hit _ hm _ _).mpr (Or.inr ⟨u.1,rfl⟩),
        (principal_hit _ hm _ _).mpr (Or.inr ⟨u.2,hh⟩)⟩
  · intro F _ k q hq
    have bcover (i j:Fin 3) (r :Fin (t i)) (l:Fin (n j))
        (hx :q 0=k (m.base ⟨i,r⟩)) (hy :q 1=(m.graph ⟨j,l⟩).eval₂ k (q 0)) :
        ∃ v∈B i j,q 0=k v.1∧q 1=k v.2 := by
      refine ⟨bp i j (r,l),mem_image.mpr ⟨(r,l),mem_univ _,rfl⟩,hx,?_⟩
      rw [hy,hx,eval₂_at_apply]
    rcases (principal_hit k hm i q).mp hq.1 with ⟨r,hr⟩ | ⟨r,hr⟩
    · rcases (principal_hit k hm j q).mp hq.2 with ⟨l,hl⟩ | ⟨l,hl⟩
      · exact (hij (congrArg Sigma.fst (hm.base_inj (k.injective (hr.symm.trans hl))))).elim
      · obtain ⟨v,hv,hx,hy⟩:=bcover i j r l hr hl
        exact ⟨v,mem_union_left _ (mem_union_left _ hv),hx,hy⟩
    · rcases (principal_hit k hm j q).mp hq.2 with ⟨l,hl⟩ | ⟨l,hl⟩
      · obtain ⟨v,hv,hx,hy⟩:=bcover j i l r hl hr
        exact ⟨v,mem_union_left _ (mem_union_right _ hv),hx,hy⟩
      · have hzero : (Δ (r,l)).eval₂ k (q 0)=0:= by
          dsimp only [Δ]
          rw [eval₂_sub,← hr,← hl,sub_self]
        obtain ⟨x,hx,he⟩:=roots_descend k (hne (r,l)) hzero
        refine ⟨pt (r,l) x,mem_union_right _ (mem_biUnion.mpr ⟨(r,l),mem_univ _,
          mem_image.mpr ⟨x,Multiset.mem_toFinset.mpr hx,rfl⟩⟩),he,?_⟩
        rw [hr,he,eval₂_at_apply]
end
end qvWVeNa
end
section
namespace qvWVeNa
noncomputable section
open qFwMjQd (aax)
open Polynomial
variable {E F:Type} [zrb E] [zrb F] {n t:Fin 3→ℕ} {s :ℕ} {m:Model E n t}
theorem left_ne_right (i:Fin 3) :i+1≠i+2 :=
 (by decide : ∀ j:Fin 3,j+1≠j+2) i
theorem left_ne (i:Fin 3) :i+1≠i :=
 (by decide : ∀ j:Fin 3,j+1≠j) i
theorem right_ne (i:Fin 3) :i+2≠i :=
 (by decide : ∀ j:Fin 3,j+2≠j) i
def lin (r :Bool) (u z :F) :F:=if r then 1-u*z else z-u
theorem lin_root (r :Bool) {u z :F} (h:lin r u z=0) :
   (if r then z⁻¹ else z)=u:= by
 cases r
 · exact sub_eq_zero.mp h
 · exact inv_eq_of_mul_eq_one_left (sub_eq_zero.mp h).symm
private theorem factor_hit (k :E →+* F) (rx ry :Bool) (i:Fin 3) (q:aax F) :
  Km k s m rx ry i q=0 ↔
   (∃ l:Fin (t i),lin rx (k (m.base ⟨i,l⟩)) (q 0)=0) ∨
   (∃ j:Fin (n i),lin ry (graphAt k s rx (m.graph ⟨i,j⟩) (q 0)) (q 1)=0) := by
 simp only [atPhysical_eq,lin,mul_eq_zero,Finset.prod_eq_zero_iff,Finset.mem_univ,true_and]
private theorem pair_not_boundary (hm:Good s m) (k :E →+* F) (rx ry :Bool)
    (q:aax F) {i j:Fin 3} (hij:i≠j) (h:arS k s m rx ry i j q) :
    (rx=true→q 0≠0)∧(ry=true→q 1≠0) := by
  constructor
  · intro er hx
    subst rx
    have hit (l:Fin 3) (hl:Km k s m true ry l q=0) :
        ∃ u:Fin (n l),(if ry then (q 1)⁻¹ else q 1) =
          k ((m.graph ⟨l,u⟩).coeff s) := by
      rcases (factor_hit k true ry l q).mp hl with ⟨u,hu⟩ | ⟨u,hu⟩
      · simp [lin,hx] at hu
      · exact ⟨u,by simpa only [hx,graphAt_infty] using lin_root ry hu⟩
    obtain ⟨u,hu⟩:=hit i h.1
    obtain ⟨v,hv⟩:=hit j h.2
    exact hij (congrArg Sigma.fst (hm.leading_inj (k.injective (hu.symm.trans hv))))
  · intro er hy
    subst ry
    have hit (l:Fin 3) (hl:Km k s m rx true l q=0) :
        ∃ u:Fin (t l),(if rx then (q 0)⁻¹ else q 0)=k (m.base ⟨l,u⟩) := by
      rcases (factor_hit k rx true l q).mp hl with ⟨u,hu⟩ | ⟨u,hu⟩
      · exact ⟨u,lin_root rx hu⟩
      · simp [lin,hy] at hu
    obtain ⟨u,hu⟩:=hit i h.1
    obtain ⟨v,hv⟩:=hit j h.2
    exact hij (congrArg Sigma.fst (hm.base_inj (k.injective (hu.symm.trans hv))))
private theorem no_three_principal (hm:Good s m) (v :E×E)
    (h : ∀ i,Km (zz4 E) s m false false i (mark v 0)=0) :False := by
  have hit (i:Fin 3) : (∃ l:Fin (t i),v.1=m.base ⟨i,l⟩) ∨
      ∃ u:Fin (n i),v.2=(m.graph ⟨i,u⟩).eval v.1 :=
    (principal_hit (zz4 E) hm i (mark v 0)).mp (h i)
  by_cases hb : ∃ i,∃ l:Fin (t i),v.1=m.base ⟨i,l⟩
  · obtain ⟨i,l,hl⟩:=hb
    have hg (j:Fin 3) (hj:j≠i) : ∃ u:Fin (n j),v.2=(m.graph ⟨j,u⟩).eval v.1 :=
      (hit j).resolve_left fun ⟨u,hu⟩ =>
        hj (congrArg Sigma.fst (hm.base_inj (hu.symm.trans hl)))
    obtain ⟨u,hu⟩:=hg (i+1) (left_ne i)
    obtain ⟨w,hw⟩:=hg (i+2) (right_ne i)
    have hn: (⟨i+1,u⟩:bzm n)≠⟨i+2,w⟩ :=
      fun e=>left_ne_right i (congrArg Sigma.fst e)
    apply hm.base_avoid _ _ hn ⟨i,l⟩
    rw [← hl,eval_sub,← hu,← hw,sub_self]
  · have hg (i:Fin 3) : ∃ u:Fin (n i),v.2=(m.graph ⟨i,u⟩).eval v.1 :=
      (hit i).resolve_left fun h=>hb ⟨i,h⟩
    obtain ⟨u,hu⟩:=hg 0
    obtain ⟨v',hv⟩:=hg 1
    obtain ⟨w,hw⟩:=hg 2
    exact hm.no_three ⟨0,u⟩ ⟨1,v'⟩ ⟨2,w⟩
      (fun e=>(by decide : (0:Fin 3)≠1) (congrArg Sigma.fst e))
      (fun e=>(by decide : (0:Fin 3)≠2) (congrArg Sigma.fst e))
      (fun e=>(by decide : (1 :Fin 3)≠2) (congrArg Sigma.fst e))
      _ (hu.symm.trans hv) (hu.symm.trans hw)
theorem physical_boundary [IsAlgClosed E] (hm:Good s m) (k :E →+* F)
    (rx ry :Bool) (q:aax F) :
    (∀ i j,i≠j→arS k s m rx ry i j q →
      (rx=true→q 0≠0)∧(ry=true→q 1≠0)) ∧
    ¬ (∀ i,Km k s m rx ry i q=0) := by
  refine ⟨fun _ _=>pair_not_boundary hm k rx ry q,?_⟩
  intro hz
  have h01 : (0:Fin 3)≠1 := by decide
  obtain ⟨hx,_⟩:=pair_not_boundary hm k rx ry q h01 ⟨hz 0,hz 1⟩
  let x :=if rx then (q 0)⁻¹ else q 0
  let scale :=if rx then (q 0)^s else 1
  let y :=(if ry then (q 1)⁻¹ else q 1)/scale
  have hn:scale≠0:= by
    cases rx
    · exact one_ne_zero
    · exact pow_ne_zero _ (hx rfl)
  have hp (i:Fin 3) :Km k s m false false i (mark (x,y) 0)=0:= by
    apply (principal_hit k hm i _).mpr
    rcases (factor_hit k rx ry i q).mp (hz i) with ⟨u,hu⟩ | ⟨u,hu⟩
    · exact Or.inl ⟨u,lin_root rx hu⟩
    · refine Or.inr ⟨u,(div_eq_iff hn).mpr ?_⟩
      have hscale :graphAt k s rx (m.graph ⟨i,u⟩) (q 0) =
          scale*(m.graph ⟨i,u⟩).eval₂ k x := by
        cases rx
        · simpa only [scale,x,Bool.false_eq_true,ite_false,one_mul] using
            graphAt_finite k (hm.graph_degree ⟨i,u⟩) (q 0)
        · exact graphAt_invert k (hm.graph_degree ⟨i,u⟩) (hx rfl)
      rw [lin_root ry hu,hscale,mark_x,mul_comm]
  obtain ⟨C,_,_,hC⟩:=pair_points hm 0 1 h01
  obtain ⟨v,_,hvx,hvy⟩:=hC k _ ⟨hp 0,hp 1⟩
  apply no_three_principal hm v
  intro i
  apply (principal_hit (zz4 E) hm i _).mpr
  rcases (principal_hit k hm i _).mp (hp i) with ⟨u,hu⟩ | ⟨u,hu⟩
  · exact Or.inl ⟨u,k.injective (hvx.symm.trans hu)⟩
  · refine Or.inr ⟨u,k.injective (hvy.symm.trans ?_)⟩
    rwa [hvx,eval₂_at_apply] at hu
end
end qvWVeNa
end
section
namespace qvWVeNa
noncomputable section
open q8Z6NHc (rawDegree kK)
open qFwMjQd (LineData aax simple weight_base)
open q9sUlTb (fullChart push b8A zeroAt)
open MvPolynomial Finset
def c1 :Prop :=
  ∀ {E :Type} [zrb E] (n s b:ℕ),n*s≤b →
    ∀ (r :Fin (b-n*s)→E) (p:Fin n→zM1 E),(∀ j,(p j).natDegree≤ s) →
    ∀ z :E,∃ f :LineData E n s b,∀ rx ry rz,
      fullChart rx ry rz f=amm s rx ry r p*seedFactor rz z
def c2 :Prop :=
  ∀ {E :Type} [zrb E] {n t:Fin 3→ℕ} (s :ℕ) (m:Model E n t),
    Good s m → ∀ (i:Fin 3) (v :E×E),
      arS (zz4 E) s m false false (i+1) (i+2) (mark v 0) →
      Km (zz4 E) s m false false i (mark v 0)≠0 →
      simple (splitChart s m false false false 0) (splitChart s m false false false 1)
        (splitChart s m false false false 2) (mark v (m.seed i))
private theorem avN (s n b n' b' : ℕ) (h:n*s≤b) (h' : n'*s≤b') :
  (pairDegree s n (b-n*s) n' (b'-n'*s) :ℤ)=kK s b n b' n' := by
 simp only [pairDegree,kK,z6H,Nat.cast_mul,zjK h,zjK h']
 ring
private theorem degree_total (d s a :ℕ) (hd:2≤d) (ha :d*s≤a)
   (n b:Fin 3→ℕ) (hn:n = ![d,d,d-1]) (hb:b = ![a,a+s+1,a-s])
   (hw : ∀ i,n i*s≤b i) :
   ((∑ i:Fin 3,pairDegree s (n (i+1)) (b (i+1)-n (i+1)*s)
     (n (i+2)) (b (i+2)-n (i+2)*s) :ℕ) :ℤ)=rawDegree d a s := by
 simp only [Fin.sum_univ_three,z6H,avN _ _ _ _ _ (hw _) (hw _)]
 subst n
 subst b
 change kK (s :ℤ) (↑(a+s+1 :ℕ)) d (↑(a-s :ℕ)) (↑(d-1 :ℕ)) +
   kK s (↑(a-s :ℕ)) (↑(d-1 :ℕ)) a d +
   kK s a d (↑(a+s+1 :ℕ)) d= _
 rw [zjK (weight_base hd ha),zjK (by omega :1≤d)]
 simp only [z6H,Nat.cast_one,rawDegree,kK]
 ring
private def aee {E F:Type} [zrb E] [zrb F] (k :E →+* F) (rz :Bool)
  (z :E) (u:F) :F :=
 lin rz (k z) u
private theorem eval_split {E F:Type} [zrb E] [zrb F] {n t:Fin 3→ℕ}
  (k :E →+* F) (s :ℕ) (m:Model E n t) (rx ry rz :Bool) (i:Fin 3) (q:aax F) :
  eval q (map k (splitChart s m rx ry rz i)) =
    Km k s m rx ry i q*aee k rz (m.seed i) (q 2) := by
 cases rz <;> simp [splitChart,Km,aee,lin,seedFactor]
private theorem seed_pair {E F:Type} [zrb E] [zrb F] {n t:Fin 3→ℕ}
  {s :ℕ} {m:Model E n t} (hm:Good s m) (k :E →+* F) (rx ry rz :Bool) (q:aax F)
  (ht : ¬ (∀ i,Km k s m rx ry i q=0))
  (hz : ∀ i,eval q (map k (splitChart s m rx ry rz i))=0) :
  ∃ i,aee k rz (m.seed i) (q 2)=0∧arS k s m rx ry (i+1) (i+2) q:= by
 classical
 have hv (i:Fin 3) :=mul_eq_zero.mp ((eval_split k s m rx ry rz i q).symm.trans (hz i))
 have he : ∃ i,aee k rz (m.seed i) (q 2)=0:= by
  by_contra! h
  exact ht fun i=>(hv i).resolve_right (h i)
 obtain ⟨i,hi⟩:=he
 have hother (j:Fin 3) (hj:j≠i) :Km k s m rx ry j q=0 :=
  (hv j).resolve_right fun h=>hj (hm.seed_inj (k.injective ((lin_root rz h).symm.trans (lin_root rz hi))))
 exact ⟨i,hi,hother _ (left_ne i),hother _ (right_ne i)⟩
theorem of_children (realize :c1) (jac:c2) :
    q9sUlTb.c1 := by
  classical
  intro E _ _ d s a hd ha
  let n:Fin 3→ℕ := ![d,d,d-1]
  let b:Fin 3→ℕ := ![a,a+s+1,a-s]
  let t (i:Fin 3) :=b i - n i*s
  have hw (i:Fin 3) :n i*s≤b i:= by
    fin_cases i
    · exact ha
    · change d*s≤a+s+1
      omega
    · change (d-1)*s≤a-s
      have he : (d-1)*s+s=d*s := by
        rw [← Nat.succ_mul,Nat.succ_eq_add_one,Nat.sub_add_cancel (by omega :1≤d)]
      omega
  obtain ⟨m,hm⟩:=exists_model (E :=E) s n t
  choose f hf using fun i=>realize (n i) s (b i) (hw i)
    (fun l=>m.base ⟨i,l⟩) (fun j=>m.graph ⟨i,j⟩)
    (fun j=>hm.graph_degree ⟨i,j⟩) (m.seed i)
  have hf' {F:Type} [zrb F] (k :E →+* F) (rx ry rz :Bool) (i:Fin 3) :
      fullChart rx ry rz (push k (f i))=map k (splitChart s m rx ry rz i) := by
    rw [← b8A,hf]
    rfl
  choose C hCcard hCmem hCcover using fun i=>pair_points hm (i+1) (i+2) (left_ne_right i)
  let points (i:Fin 3) :=(C i).image (fun v=>mark v (m.seed i))
  let all:=(univ :Finset (Fin 3)).biUnion points
  refine ⟨f 0,f 1,f 2,all,?_,?_,?_⟩
  · have hc:all.card ≤ ∑ i:Fin 3,pairDegree s (n (i+1)) (t (i+1)) (n (i+2)) (t (i+2)) :=
      card_biUnion_le.trans (sum_le_sum fun i _=>card_image_le.trans (hCcard i))
    rw [← degree_total d s a hd ha n b rfl rfl hw]
    exact_mod_cast hc
  · intro q hq
    obtain ⟨i,_,hi⟩:=mem_biUnion.mp hq
    obtain ⟨v,hv,rfl⟩:=mem_image.mp hi
    have hp:=hCmem i v hv
    have hn:Km (zz4 E) s m false false i (mark v 0)≠0:= by
      intro he
      apply (physical_boundary hm (zz4 E) false false (mark v 0)).2
      have hcases : ∀ u w:Fin 3,w=u∨w=u+1∨w=u+2 := by decide
      intro w
      rcases hcases i w with rfl | rfl | rfl
      · exact he
      · exact hp.1
      · exact hp.2
    have hloc (j:Fin 3) :fullChart false false false (f j) =
        splitChart s m false false false j:=hf j false false false
    change simple (fullChart false false false (f 0)) (fullChart false false false (f 1))
      (fullChart false false false (f 2)) (mark v (m.seed i))
    rw [hloc 0,hloc 1,hloc 2]
    exact jac s m hm i v hp hn
  · intro F _ k
    have hzeros (rx ry rz :Bool) (q:aax F)
        (hz :zeroAt (fullChart rx ry rz (push k (f 0))) (fullChart rx ry rz (push k (f 1)))
          (fullChart rx ry rz (push k (f 2))) q) (i:Fin 3) :
        eval q (map k (splitChart s m rx ry rz i))=0:= by
      rw [← hf']
      fin_cases i
      · exact hz.1
      · exact hz.2.1
      · exact hz.2.2
    refine ⟨?_,?_⟩
    · intro rx ry rz q hz
      obtain ⟨hb,ht⟩:=physical_boundary hm k rx ry q
      obtain ⟨i,hi,hp⟩:=seed_pair hm k rx ry rz q ht (hzeros rx ry rz q hz)
      obtain ⟨hx,hy⟩:=hb _ _ (left_ne_right i) hp
      refine ⟨hx,hy,?_⟩
      intro er ez
      simp [aee,lin,er,ez] at hi
    · intro q hz
      obtain ⟨i,hi,hp⟩:=seed_pair hm k false false false q
        (physical_boundary hm k false false q).2 (hzeros false false false q hz)
      obtain ⟨v,hv,hx,hy⟩:=hCcover i k q hp
      refine ⟨mark v (m.seed i),mem_biUnion.mpr ⟨i,mem_univ _,mem_image.mpr ⟨v,hv,rfl⟩⟩,?_⟩
      funext j
      fin_cases j
      · exact hx
      · exact hy
      · exact sub_eq_zero.mp hi
end
end qvWVeNa
end
