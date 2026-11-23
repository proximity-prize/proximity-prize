import ProximityPrize.SubmissionLower.ZNM4IAc
set_option Elab.async false
open _root_ renaming Finset.sum_congr → zUo, Finset.sum_mul → zkq, MvPolynomial.X → z9v, Nat.le_of_lt_succ → zeh, Nat.lt_succ_of_le → zB1, Polynomial.eval_sub → zfY, RingHom.id → zz4
section
namespace qzxonle
noncomputable section
open q8Z6NHc (Slot)
open qFwMjQd (Chart)
open q9sUlTb (fullChart)
open qvWVeNa (baseFactor graphCoeff graphFactor amm seedFactor)
open Finset MvPolynomial
variable {E :Type} [Field E]
private def slot {d s a :ℕ} (i j:ℕ) (hi:i≤d) (hj:j+i*s≤a) :
   Slot d s a :=
 ⟨(⟨i,zB1 hi⟩,⟨j,zB1 (by omega)⟩),hj⟩
private def term {d s a :ℕ} (rx ry :Bool) (c:E) (i:Slot d s a) :Chart E :=
 C c*z9v 0^(if rx then a-i.val.1.val*s-i.val.2.val else i.val.2.val) *
   z9v 1^(if ry then d-i.val.1.val else i.val.1.val)
private def view {d s a :ℕ} (rx ry :Bool) (f :Slot d s a→E) :Chart E :=
 ∑ i,term rx ry (f i) i
private def Realizes (s d a :ℕ) (F:Bool→Bool→Chart E) :Prop :=
 ∃ f :Slot d s a→E,∀ rx ry,view rx ry f=F rx ry
private theorem pack {ι:Type} [Fintype ι] {d s a :ℕ}
   (idx :ι→Slot d s a) (c:ι→E) :
   Realizes s d a (fun rx ry => ∑ j,term rx ry (c j) (idx j)) := by
 classical
 let f (i:Slot d s a) := ∑ j,if idx j=i then c j else 0
 refine ⟨f,fun rx ry => ?_⟩
 simp only [view,f,term,map_sum,zkq]
 rw [Finset.sum_comm]
 refine zUo rfl fun j _ => ?_
 rw [Finset.sum_eq_single (idx j)]
 · simp
 · intro i _ h
   simp [Ne.symm h]
 · simp
private def join {d e s a b:ℕ} (u:Slot d s a) (v :Slot e s b) :
  Slot (d+e) s (a+b) :=
 slot (u.val.1.val+v.val.1.val) (u.val.2.val+v.val.2.val)
  (Nat.add_le_add (zeh u.val.1.isLt) (zeh v.val.1.isLt))
  (by
    have hu:=u.property
    have hv :=v.property
    rw [Nat.add_mul]
    omega)
private theorem term_mul {d e s a b:ℕ} (rx ry :Bool) (u:Slot d s a)
  (v :Slot e s b) (c k :E) :
  term rx ry c u*term rx ry k v=term rx ry (c*k) (join u v) := by
 have hu:=u.property
 have hv :=v.property
 have hdu:=zeh u.val.1.isLt
 have hdv :=zeh v.val.1.isLt
 have hx :a+b-(u.val.1.val+v.val.1.val)*s-(u.val.2.val+v.val.2.val) =
    (a-u.val.1.val*s-u.val.2.val)+(b-v.val.1.val*s-v.val.2.val) := by
  rw [Nat.add_mul]
  omega
 have hy :d+e-(u.val.1.val+v.val.1.val)=(d-u.val.1.val)+(e-v.val.1.val) := by
  omega
 cases rx <;> cases ry <;>
  simp only [term,join,slot,Bool.false_eq_true,ite_false,ite_true,hx,hy,C_mul,pow_add] <;>
  ac_rfl
private theorem realizes_mul {d e s a b:ℕ} {F G:Bool→Bool→Chart E}
  (hF:Realizes s d a F) (hG:Realizes s e b G) :
  Realizes s (d+e) (a+b) (fun rx ry=>F rx ry*G rx ry) := by
 obtain ⟨f,hf⟩:=hF
 obtain ⟨g,hg⟩:=hG
 obtain ⟨h,hh⟩:=pack (fun ij:Slot d s a×Slot e s b=>join ij.1 ij.2)
  (fun ij=>f ij.1*g ij.2)
 refine ⟨h,fun rx ry => ?_⟩
 rw [hh]
 dsimp only
 rw [← hf rx ry,← hg rx ry,Fintype.sum_prod_type]
 simp only [view]
 rw [zkq]
 simp only [Finset.mul_sum,term_mul]
private theorem realizes_one (s :ℕ) :Realizes s 0 0 (fun _ _=>(1 :Chart E)) := by
 obtain ⟨f,hf⟩:=pack (fun _:Unit=>(slot 0 0 (by simp) (by simp) :Slot 0 s 0))
  (fun _=>(1 :E))
 refine ⟨f,fun rx ry => ?_⟩
 rw [hf]
 simp [term,slot]
private theorem realizes_prod (s d a k :ℕ) (F:Fin k→Bool→Bool→Chart E)
   (hF : ∀ j,Realizes s d a (F j)) :
   Realizes s (k*d) (k*a) (fun rx ry => ∏ j,F j rx ry) := by
 induction k with
 | zero =>
     simpa only [zero_mul,Fin.prod_univ_zero] using (realizes_one (E :=E) s)
 | succ k ih =>
     rw [Nat.succ_mul,Nat.succ_mul]
     obtain ⟨f,hf⟩:=realizes_mul (ih (fun j=>F j.succ) fun j=>hF j.succ) (hF 0)
     refine ⟨f,fun rx ry => ?_⟩
     rw [hf]
     dsimp only
     rw [Fin.prod_univ_succ,mul_comm]
private theorem realizes_base (s :ℕ) (r :E) :
  Realizes s 0 1 (fun rx _=>baseFactor rx r) := by
 let idx (j:Bool) :Slot 0 s 1 :=
  if j then slot 0 1 (by simp) (by simp) else slot 0 0 (by simp) (by simp)
 obtain ⟨f,hf⟩:=pack idx (fun j=>if j then 1 else -r)
 refine ⟨f,fun rx ry => ?_⟩
 rw [hf]
 dsimp only
 rw [Fintype.sum_bool]
 cases rx <;> simp [idx,slot,term,baseFactor,C_neg,sub_eq_add_neg]
private theorem realizes_graph (s :ℕ) (p:Polynomial E) :
   Realizes s 1 s (fun rx ry=>graphFactor s rx ry p) := by
 let idx :Option (Fin (s+1))→Slot 1 s s
   | none=>slot 1 0 (by simp) (by simp)
   | some j=>slot 0 j.val (by simp) (by simpa using Nat.le_of_lt_succ j.isLt)
 obtain ⟨f,hf⟩:=pack idx (fun j=>j.elim 1 fun i => -p.coeff i.val)
 refine ⟨f,fun rx ry => ?_⟩
 have hP: (∑ j:Fin (s+1),term rx ry (-p.coeff j.val) (idx (some j))) =
     -(graphCoeff s rx p*z9v 1^(if ry then 1 else 0)) := by
   rw [graphCoeff,zkq,← Finset.sum_neg_distrib]
   refine zUo rfl fun j _ => ?_
   simp only [idx,slot,term,Nat.zero_mul,Nat.sub_zero,C_neg,neg_mul]
 rw [hf]
 dsimp only
 rw [Fintype.sum_option]
 change term rx ry 1 (idx none) +
   (∑ j:Fin (s+1),term rx ry (-p.coeff j.val) (idx (some j)))= _
 rw [hP]
 cases ry <;> simp [idx,slot,term,graphFactor,sub_eq_add_neg]
private theorem seed_coeff (rz :Bool) (c z :E) :
  (C (if rz then c else -z*c)+C (if rz then -z*c else c)*z9v 2 :Chart E) =
    C c*seedFactor rz z := by
 cases rz <;> simp [seedFactor,C_mul,C_neg] <;> ring
theorem proof :qvWVeNa.c1 := by
  intro E _ n s b hb r p _ z
  let t:=b-n*s
  have hr :Realizes s 0 t (fun rx _ => ∏ l,baseFactor rx (r l)) := by
    simpa only [mul_zero,mul_one] using
      (realizes_prod s 0 1 t (fun l rx _=>baseFactor rx (r l)) fun l=>realizes_base s (r l))
  have hp:Realizes s n (n*s) (fun rx ry => ∏ j,graphFactor s rx ry (p j)) := by
    simpa only [mul_one] using
      (realizes_prod s 1 s n (fun j rx ry=>graphFactor s rx ry (p j))
        fun j=>realizes_graph s (p j))
  have h:Realizes s n b (fun rx ry=>amm s rx ry r p) := by
    simpa only [zero_add,t,Nat.sub_add_cancel hb,amm] using realizes_mul hr hp
  obtain ⟨f,hf⟩:=h
  refine ⟨fun i=>(-z*f i,f i),fun rx ry rz => ?_⟩
  have hchart:view rx ry f=amm s rx ry r p:=hf rx ry
  rw [← hchart,fullChart,view,zkq]
  refine zUo rfl fun i _ => ?_
  rw [seed_coeff]
  unfold term
  ac_rfl
end
end qzxonle
end
section
namespace qofhpvd
noncomputable section
open qFwMjQd (Chart aax)
open q9sUlTb (jac)
open qvWVeNa MvPolynomial Finset
variable {E :Type} [Field E] {n t:Fin 3→ℕ} {s :ℕ} {m:Model E n t}
private abbrev Tag (n t:Fin 3→ℕ) :=Sum (bzm t) (bzm n)
private abbrev Local (n t:Fin 3→ℕ) (i:Fin 3) :=Sum (Fin (t i)) (Fin (n i))
private def tag (i:Fin 3) :Local n t i→Tag n t
 | .inl a => .inl ⟨i,a⟩
 | .inr a => .inr ⟨i,a⟩
private theorem tag_inj (i:Fin 3) :Function.Injective (tag (n:=n) (t:=t) i) := by
 intro a b h
 cases a <;> cases b <;> simp_all [tag]
private theorem tag_ne {i j:Fin 3} (h:i≠j) (a :Local n t i) (b:Local n t j) :
  tag i a≠tag j b:= by
 cases a <;> cases b <;> simp [tag,h]
private def factor (s :ℕ) (m:Model E n t) :Tag n t→Chart E
 | .inl a=>baseFactor false (m.base a)
 | .inr a=>graphFactor s false false (m.graph a)
private def hit (m:Model E n t) (v :E×E) :Tag n t→Prop
 | .inl a=>v.1=m.base a
 | .inr a=>v.2=(m.graph a).eval v.1
private theorem factor_zero (hm:Good s m) (v :E×E) (z :E) (a :Tag n t) :
    eval (mark v z) (factor s m a)=0↔hit m v a := by
  cases a with
  | inl a=>simp [factor,hit,baseFactor,sub_eq_zero]
  | inr a =>
    have he :eval (mark v z) (graphCoeff s false (m.graph a)) =
        (m.graph a).eval v.1 := by
      simpa [graphCoeff,graphAt] using
        graphAt_finite (zz4 E) (hm.graph_degree a) v.1
    simp [factor,hit,graphFactor,he,sub_eq_zero]
private theorem two_graphs_at_base (hm:Good s m) {v :E×E}
  {a :bzm t} {b c:bzm n} (hbc:b≠c)
  (ha :v.1=m.base a) (hb:v.2=(m.graph b).eval v.1)
  (hc:v.2=(m.graph c).eval v.1) :False := by
 apply hm.base_avoid b c hbc a
 rw [← ha,zfY,← hb,← hc,sub_self]
private theorem three_hits (hm:Good s m) {v :E×E} {a b c:Tag n t}
   (hab:a≠b) (hac:a≠c) (hbc:b≠c)
   (ha :hit m v a) (hb:hit m v b) (hc:hit m v c) :False := by
 rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
   simp only [hit,ne_eq,Sum.inl.injEq,Sum.inr.injEq] at *
 · exact hab (hm.base_inj (ha.symm.trans hb))
 · exact hab (hm.base_inj (ha.symm.trans hb))
 · exact hac (hm.base_inj (ha.symm.trans hc))
 · exact two_graphs_at_base hm hbc ha hb hc
 · exact hbc (hm.base_inj (hb.symm.trans hc))
 · exact two_graphs_at_base hm hac hb ha hc
 · exact two_graphs_at_base hm hab hc ha hb
 · exact hm.no_three a b c hab hac hbc _ (ha.symm.trans hb) (ha.symm.trans hc)
private abbrev D (q:aax E) (p:Chart E) (j:Fin 3) :=eval q (pderiv j p)
private theorem linear_d (q:aax E) (i j:Fin 3) (z :E) :
   D q (z9v i - C z) j=if j=i then 1 else 0:= by
 by_cases h:j=i
 · subst j
   simp [D]
 · simp [D,h,Ne.symm h]
private theorem coeff_d (q:aax E) (j:Fin 3) {p:Polynomial E} (hp:p.natDegree≤ s) :
   D q (graphCoeff s false p) j=if j=0 then p.derivative.eval (q 0) else 0:= by
 by_cases hj:j=0
 · subst j
   simp only [↓reduceIte]
   rw [Polynomial.derivative_eval,
     p.sum_over_range' (by simp) (s+1) (Nat.lt_succ_iff.mpr hp),← Fin.sum_univ_eq_sum_range]
   simp only [D,graphCoeff,Bool.false_eq_true,ite_false,map_sum,pderiv_C_mul,pderiv_pow,
     pderiv_X_self,mul_one,map_mul,map_pow,map_natCast,eval_C,eval_X]
   exact zUo rfl fun _ _=> by ring
 · simp [D,graphCoeff,pderiv_X_of_ne (Ne.symm hj),hj]
private theorem base_d (q:aax E) (a :bzm t) (j:Fin 3) :
  D q (factor s m (.inl a)) j=if j=0 then 1 else 0 :=
 linear_d q 0 j (m.base a)
private theorem graph_d (hm:Good s m) (q:aax E) (a :bzm n) (j:Fin 3) :
  D q (factor s m (.inr a)) j =
    (if j=1 then 1 else 0)-(if j=0 then (m.graph a).derivative.eval (q 0) else 0) := by
 have hx :D q (z9v 1) j=if j=1 then 1 else 0:= by
  simpa [D] using linear_d q 1 j 0
 change D q (z9v 1 - graphCoeff s false (m.graph a)) j= _
 simpa only [D,map_sub] using
  congrArg₂ (fun x y :E=>x - y) hx (coeff_d q j (hm.graph_degree a))
private theorem minor_ne (hm:Good s m) {v :E×E} (z :E) {a b:Tag n t} (hab:a≠b)
    (ha :hit m v a) (hb:hit m v b) :
    let q:=mark v z
    D q (factor s m a) 0*D q (factor s m b) 1 -
      D q (factor s m a) 1*D q (factor s m b) 0≠0:= by
  dsimp only
  cases a with
  | inl a =>
    cases b with
    | inl b=>exact False.elim (hab (congrArg Sum.inl (hm.base_inj (ha.symm.trans hb))))
    | inr b=>simp [base_d,graph_d hm]
  | inr a =>
    cases b with
    | inl b=>simp [base_d,graph_d hm]
    | inr b =>
      have h:=hm.ct4 a b (fun e=>hab (congrArg Sum.inr e)) v.1
        (by rw [zfY,← show v.2= _ from ha,← show v.2= _ from hb,sub_self])
      simp only [Polynomial.derivative_sub,zfY] at h
      convert neg_ne_zero.mpr h using 1
      simp [graph_d hm]
      ring
private theorem physical_prod (i:Fin 3) :
  physicalChart s m false false i = ∏ a :Local n t i,factor s m (tag i a) := by
 rw [Fintype.prod_sum_type]
 rfl
private theorem at_mark (v :E×E) (z :E) (i:Fin 3) :
   eval (mark v z) (physicalChart s m false false i) =
     Km (zz4 E) s m false false i (mark v 0) := by
 have h:=atPhysical_eq (zz4 E) s m false false i (mark v z)
 simp only [Km,MvPolynomial.map_id] at h
 rw [h,atPhysical_eq]
 rfl
private theorem pair_row (hm:Good s m) (v :E×E) (z :E) {i j:Fin 3} (hij:i≠j)
    (a :Local n t i) (b:Local n t j) (ha :hit m v (tag i a)) (hb:hit m v (tag j b))
    (hz :z≠m.seed i) :
    ∃ u:E,u≠0 ∧ ∀ l,D (mark v z) (splitChart s m false false false i) l =
      u*D (mark v z) (factor s m (tag i a)) l:= by
  let f := fun c:Local n t i=>factor s m (tag i c)
  let q:=mark v z
  let rest:=(∏ c∈univ.erase a,f c)*seedFactor false (m.seed i)
  have he :splitChart s m false false false i=f a*rest:= by
    rw [splitChart,physical_prod,← mul_prod_erase _ f (mem_univ a),mul_assoc]
  have hn:eval q rest≠0:= by
    simp only [rest,map_mul,map_prod]
    refine mul_ne_zero (prod_ne_zero_iff.mpr fun c hc => ?_) ?_
    · have hca :=(mem_erase.mp hc).1
      refine fun hc=>three_hits hm (tag_ne hij a b) (fun e=>hca (tag_inj i e.symm))
        (tag_ne hij.symm b c) ha hb ((factor_zero hm v z _).mp hc)
    · simpa [q,seedFactor,sub_eq_zero] using hz
  refine ⟨eval q rest,hn,fun l => ?_⟩
  have hzero :eval q (f a)=0:=(factor_zero hm v z _).mpr ha
  rw [he]
  change D q (f a*rest) l=eval q rest*D q (f a) l
  simp only [D,pderiv_mul,map_add,map_mul,hzero,zero_mul,add_zero,mul_comm]
private theorem det_cycle (A:Matrix (Fin 3) (Fin 3) E) (i:Fin 3)
  (hx :A i 0=0) (hy :A i 1=0) :
  A.det=A i 2*(A (i+1) 0*A (i+2) 1 - A (i+1) 1*A (i+2) 0) := by
 rcases (by decide : ∀ i:Fin 3,i=0∨i=1∨i=2) i with rfl | rfl | rfl <;>
  simp [Matrix.det_fin_three,hx,hy] <;> ring
theorem proof :qvWVeNa.c2 := by
 classical
 intro E _ n t s m hm i v hp hi
 let q:=mark v (m.seed i)
 let p:=splitChart s m false false false
 have hz (j:Fin 3) :eval q (p j)=0:= by
   simp only [q,p,splitChart,map_mul,at_mark,seedFactor,Bool.false_eq_true,ite_false,
     map_sub,eval_X,mark_z,eval_C]
   rcases (by decide : ∀ i j:Fin 3,j=i∨j=i+1∨j=i+2) i j with rfl | rfl | rfl
   · simp
   · rw [hp.1,zero_mul]
   · rw [hp.2,zero_mul]
 have choose_hit {j:Fin 3}
     (h:Km (zz4 E) s m false false j (mark v 0)=0) :
     ∃ a :Local n t j,hit m v (tag j a) := by
   rcases (principal_hit (zz4 E) hm j (mark v 0)).mp h with ⟨a,ha⟩ | ⟨a,ha⟩
   · exact ⟨.inl a,ha⟩
   · exact ⟨.inr a,by simpa [hit,tag] using ha⟩
 obtain ⟨a,ha⟩:=choose_hit hp.1
 obtain ⟨b,hb⟩:=choose_hit hp.2
 have hs (j:Fin 3) (hj:j≠i) :m.seed i≠m.seed j :=
   fun e=>hj (hm.seed_inj e.symm)
 obtain ⟨u,hu,du⟩:=pair_row hm v (m.seed i) (left_ne_right i) a b ha hb (hs _ (left_ne i))
 obtain ⟨w,hw,dw⟩:=pair_row hm v (m.seed i) (left_ne_right i).symm b a hb ha (hs _ (right_ne i))
 have di (j:Fin 3) :D q (p i) j =
     Km (zz4 E) s m false false i (mark v 0)*(if j=2 then 1 else 0) := by
   have hseed :eval q (seedFactor false (m.seed i))=0:= by simp [q,seedFactor]
   have hlin:D q (seedFactor false (m.seed i)) j=if j=2 then 1 else 0 :=
     linear_d q 2 j (m.seed i)
   have hphys :eval q (physicalChart s m false false i)= _:=at_mark v (m.seed i) i
   simp only [p,splitChart,D,pderiv_mul,map_add,map_mul,hseed,mul_zero,zero_add,hphys,hlin]
 refine ⟨hz 0,hz 1,hz 2,?_⟩
 change (jac (p 0) (p 1) (p 2) q).det≠0
 have hv : (![p 0,p 1,p 2] :Fin 3→Chart E)=p:= by
   funext j
   fin_cases j <;> rfl
 unfold jac
 rw [hv]
 let A:Matrix (Fin 3) (Fin 3) E := fun j l=>D q (p j) l
 have hx :A i 0=0:= by
   change D q (p i) 0=0
   simp [di]
 have hy :A i 1=0:= by
   change D q (p i) 1=0
   simp [di]
 change A.det≠0
 rw [det_cycle A i hx hy]
 change D q (p i) 2 *
   (D q (p (i+1)) 0*D q (p (i+2)) 1 - D q (p (i+1)) 1*D q (p (i+2)) 0)≠0
 rw [di,du,du,dw,dw]
 simp only [↓reduceIte,mul_one]
 apply mul_ne_zero hi
 convert mul_ne_zero (mul_ne_zero hu hw) (minor_ne hm (m.seed i) (tag_ne (left_ne_right i) a b) ha hb)
   using 1
 ring
end
end qofhpvd
end
