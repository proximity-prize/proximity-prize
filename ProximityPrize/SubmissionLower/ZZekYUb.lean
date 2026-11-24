import ProximityPrize.SubmissionLower.Z6gtjnc
import ProximityPrize.SubmissionLower.ZycQTHe
set_option Elab.async false
open _root_ renaming CommRing → za6, Fin.ext → zmq, Fin.sum_univ_eq_sum_range → zdx, Finset.le_sup → zZi, Finset.mem_range → zIR, Finset.range → z4x, Finset.sum_add_distrib → zfW, Finset.sum_congr → zUo, Finset.sum_le_sum → zQk, Finset.sum_subset → zVG, Finsupp.weight_eq_sum → z1K, Fintype.card_sigma → zTU, Function.Injective → zq4, Ideal.Quotient.mk → zVv, Ideal.subset_span → zCn, LinearIndependent → z14, LinearIndependent.of_comp → zCu, Matrix.rank_eq_finrank_span_cols → z0e, Module.Finite → zAa, Module.Finite.map → z2p, Module.Finite.span_of_finite → z3g, Module.finrank → zsE, MvPolynomial → z3y, MvPolynomial.C → znf, MvPolynomial.X → z9v, Nat.add_assoc → zVg, Nat.add_mul → zNE, Nat.choose_eq_zero_of_lt → zsx, Nat.lt_succ_iff → zh4, Nat.lt_succ_of_le → zB1, Nat.mul_comm → z5A, Nat.sub_add_cancel → zxt, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.coeff_C_mul_X_pow → zds, Polynomial.lcoeff → z9j, Set.finite_range → zlS, Set.mem_range_self → zWL, Set.mem_singleton → zT1, Set.range → zxp, Submodule → zpI, Submodule.finrank_map_le → zSE, Submodule.finrank_mono → zFM, Submodule.subset_span → zBO
set_option maxHeartbeats 1500000
section
section
set_option autoImplicit true
namespace qOPkAYa
open aR (Shape)
open qmb8rCe (sumN fullCost)
def lo (q d n:ℕ) :=n-(q-d)
def stop (a :Shape) (n:ℕ) :=min a.t (min n (a.j-n))+1
def width (a :Shape) (q d n:ℕ) :=stop a n-lo q d n
def Fu (w n:ℕ) :ℕ :=
 let k :=min w n
 (k+1)*k/2+(n-k)*k
def fastMass (a :Shape) (q d:ℕ) :ℕ :=
 sumN (fun n=>Fu (width a q d n) (a.j-n)) (min (q+1) (a.j+1-d))
def flags (a :Shape) (q:ℕ) :ℕ:=sumN (fun d=>fastMass a q (d+1)) q
def fastPart (a :Shape) (U q:ℕ) :ℕ :=
 let m:=min q a.j
 qmb8rCe.factor a U q*fastMass a m 0+flags a m
def base (a :Shape) (q:ℕ) :ℕ :=
 sumN (fun c=>(min (q-c) (a.j-2*c)+1)*(a.b+a.j-q)) (min q (min a.t (a.j/2))+1)
def fullRank (a :Shape) (q:ℕ) :ℕ :=
  sumN (fun c=>sumN (fun b=>a.b-q+(b+2*c))
    (min (q-c) (a.j-2*c)+1)) (min q (min a.t (a.j/2))+1)
def countedRank (a :Shape) (q:ℕ) :ℕ:=fullRank a q+fastMass a (min q a.j) 0
def Filed (a :Shape) (j3:ℕ) :Prop :=
  let n:=sumN (base a) (a.b+1)
  sumN (countedRank a) (a.b+1)≤n ∧
    sumN (fullCost a (a.b-1)) (a.b+1)+sumN (fastPart a (a.b-1)) (a.b+1)≤a.b*n+j3
end qOPkAYa
end
section
namespace qOPkAYa
open aR (ao Shape)
open MvPolynomial
open scoped BigOperators
noncomputable section
abbrev Poly :=z3y (Fin 2) ao
abbrev Exp:=Fin 2 →₀ ℕ
def ex (b c:ℕ) :Exp:=(Finsupp.single (0:Fin 1) b).cons c
@[simp] theorem ex_zero (b c:ℕ) :ex b c 0=c:=rfl
@[simp] theorem ex_one (b c:ℕ) :ex b c 1=b :=
  (Finsupp.cons_succ (0:Fin 1) _ _).trans Finsupp.single_eq_same
def Bp (a :Shape) (q d h n:ℕ) :=min (width a q d n) (h-n)
abbrev jJ (a :Shape) (q d:ℕ) :=Fin (min (q+1) (a.j+1-d))
abbrev Stock (a :Shape) (q d:ℕ) :=Σ n:jJ a q d,Fin (width a q d n)
abbrev Bad (a :Shape) (q d h:ℕ) :=
 Σ n:jJ a q d,Fin (width a q d n - Bp a q d h n)
def stockExp {a :Shape} {q d:ℕ} (i:Stock a q d) :Exp :=
 let c:=lo q d i.1.val+i.2.val
 ex (i.1.val-c+(d-c)) c
abbrev Source (a :Shape) (q d:ℕ) :=
 restrictSupport ao (zxp (@stockExp a q d))
theorem stock_injective {a :Shape} {q d:ℕ} :
  zq4 (@stockExp a q d) := by
 intro i j he
 have hc:=congrArg (fun e :Exp=>e 0) he
 have hb:=congrArg (fun e :Exp=>e 1) he
 simp only [stockExp,ex_zero,ex_one] at hc hb
 have hi:=i.2.isLt
 have hj:=j.2.isLt
 dsimp [width,stop] at hi hj
 have hn:i.1=j.1 :=zmq (by omega)
 refine Sigma.ext hn ((Fin.heq_ext_iff (congrArg (fun n:jJ a q d=>width a q d n) hn)).2 ?_)
 have hl:=congrArg (fun n:jJ a q d=>lo q d n.val) hn
 omega
theorem in_stock {a :Shape} {q d:ℕ} {e :Exp}
  (ha :d≤e 1+e 0) (hq:e 1+e 0≤q) (hJ:e 1+2*e 0≤a.j) (hC:e 0≤a.t) :
  e∈zxp (@stockExp a q d) := by
 let n:=e 1+e 0-(d-e 0)
 have hn:n< min (q+1) (a.j+1-d) := by dsimp [n]; omega
 have hc:lo q d n≤e 0∧e 0<stop a n:= by dsimp [n,lo,stop]; omega
 refine ⟨⟨⟨n,hn⟩,⟨e 0-lo q d n,by dsimp [width]; omega⟩⟩,?_⟩
 have he :lo q d n+(e 0-lo q d n)=e 0:= by omega
 ext i
 fin_cases i <;> simp [stockExp,he,n]
 all_goals omega
local notation "u" => (MvPolynomial.X 1 :Poly)
local notation "v" => (MvPolynomial.X 0:Poly)
local notation "D" => (u-1)
local notation "Z" => (v-D)
local notation "Q" => (v-D*u)
local notation "W" => restrictWeightedDegree (R:=ao)
local notation "O" => restrictWeightedOrder (R:=ao)
def Zz (d l c:ℕ) :=min (d-l) (c-l)
def witness (d n l c:ℕ) :Poly :=
 let r :=Zz d l c
 D^(n-c)*v^l*Q^r*Z^(c-l-r)*u^(d-c)
private theorem witness_degrees (d n l c:ℕ) (w:Fin 2→ℕ) :
    witness d n l c∈W w
      ((n-c)*w 1+l*w 0+Zz d l c*max (w 0) (w 1+w 1) +
        (c-l-Zz d l c)*max (w 0) (w 1)+(d-c)*w 1) := by
  have hx (i:Fin 2) :z9v i∈W w (w i) :=
    X_mem_restrictWeightedDegree _ _ _ le_rfl
  have hD:D∈W w (w 1) :=sub_mem (hx 1) (by simpa using C_mem_restrictWeightedDegree w (w 1) (1 :ao))
  have hZ:Z∈W w (max (w 0) (w 1)) :=sub_mem
    (restrictWeightedDegree_mono _ (le_max_left _ _) (hx 0))
    (restrictWeightedDegree_mono _ (le_max_right _ _) hD)
  have hQ:Q∈W w (max (w 0) (w 1+w 1)) :=sub_mem
    (restrictWeightedDegree_mono _ (le_max_left _ _) (hx 0))
    (restrictWeightedDegree_mono _ (le_max_right _ _) (mul_mem_restrictWeightedDegree hD (hx 1)))
  exact mul_mem_restrictWeightedDegree
    (mul_mem_restrictWeightedDegree
      (mul_mem_restrictWeightedDegree
        (mul_mem_restrictWeightedDegree (pow_mem_restrictWeightedDegree hD _) (pow_mem_restrictWeightedDegree (hx 0) _))
        (pow_mem_restrictWeightedDegree hQ _))
      (pow_mem_restrictWeightedDegree hZ _))
    (pow_mem_restrictWeightedDegree (hx 1) _)
private theorem gMf (e :Exp) (w:Fin 2→ℕ) :
  e.weight w=e 0*w 0+e 1*w 1 := by
 simp [z1K,Fin.sum_univ_two,smul_eq_mul]
theorem witness_source {a :Shape} {q d n c:ℕ}
    (hdq:d≤q) (hn:n< min (q+1) (a.j+1-d)) (hc:lo q d n≤ c) (hs :c<stop a n) :
    witness d n (lo q d n) c∈Source a q d:= by
  let l:=lo q d n
  let r :=Zz d l c
  let w:Fin 2→ℕ := ![1,1]
  have hQ:Q∈O w 1 :=sub_mem (X_mem_restrictWeightedOrder w 0 le_rfl)
    (mul_mem_restrictWeightedOrder (show D∈O w 0 by simp)
      (X_mem_restrictWeightedOrder w 1 le_rfl))
  have hO:witness d n l c∈O w ((n-c)*0+l*1+r*1+(c-l-r)*0+(d-c)*1) :=
    mul_mem_restrictWeightedOrder
      (mul_mem_restrictWeightedOrder
        (mul_mem_restrictWeightedOrder
          (mul_mem_restrictWeightedOrder (pow_mem_restrictWeightedOrder (show D∈O w 0 by simp) _)
            (pow_mem_restrictWeightedOrder (X_mem_restrictWeightedOrder w 0 le_rfl) _))
          (pow_mem_restrictWeightedOrder hQ _))
        (pow_mem_restrictWeightedOrder (show Z∈O w 0 by simp) _))
      (pow_mem_restrictWeightedOrder (X_mem_restrictWeightedOrder w 1 le_rfl) _)
  apply (mem_restrictSupport_iff ao).mpr
  intro e he
  have h0:=mem_restrictWeightedOrder.mp hO e he
  have h1 :=mem_restrictWeightedDegree.mp (witness_degrees d n l c ![1,1]) e he
  have h2 :=mem_restrictWeightedDegree.mp (witness_degrees d n l c ![2,1]) e he
  have h3:=mem_restrictWeightedDegree.mp (witness_degrees d n l c ![1,0]) e he
  simp only [w,gMf,Matrix.cons_val_zero,Matrix.cons_val_one,Nat.mul_zero,Nat.mul_one,
    Nat.zero_add,Nat.add_zero] at h0 h1 h2 h3
  norm_num at h1 h2 h3
  dsimp [r,l,lo,Zz,stop] at *
  exact in_stock (by omega) (by omega) (by omega) (by omega)
def bY:Poly →ₐ[ao] Poly :=aeval ![u+v,1+u]
def wt:Fin 2→ℕ := ![2,1]
theorem witness_order (d n l c h:ℕ) (hl:l≤ c) (hc:c≤n)
    (hh:h≤n+(c-l)) :bY (witness d n l c)∈O wt h:= by
  have hu:u∈O wt 1 :=X_mem_restrictWeightedOrder wt 1 le_rfl
  have hv :v∈O wt 2 :=X_mem_restrictWeightedOrder wt 0 le_rfl
  have hW:u+v∈O wt 1 :=add_mem hu (restrictWeightedOrder_anti _ (by decide) hv)
  have hF:v-u^2∈O wt 2 :=sub_mem hv (pow_mem_restrictWeightedOrder hu 2)
  have hU: (1+u)∈O wt 0:= by simp
  have hd:bY D =u:= by simp [bY]
  have hz :bY Z=v := by simp [bY]
  have hq:bY Q=v-u^2 := by simp [bY]; ring
  have hcv :bY v=u+v := by simp [bY]
  have hcu:bY u=1+u:= by simp [bY]
  simp only [witness,map_mul,map_pow,hd,hz,hq,hcv,hcu]
  apply restrictWeightedOrder_anti wt _ (mul_mem_restrictWeightedOrder
    (mul_mem_restrictWeightedOrder
      (mul_mem_restrictWeightedOrder
        (mul_mem_restrictWeightedOrder (pow_mem_restrictWeightedOrder hu _) (pow_mem_restrictWeightedOrder hW _))
        (pow_mem_restrictWeightedOrder hF _))
      (pow_mem_restrictWeightedOrder hv _))
    (pow_mem_restrictWeightedOrder hU _))
  have hr :Zz d l c≤ c-l:=min_le_right _ _
  omega
end
end qOPkAYa
end
section
namespace qOPkAYa
open aR (ao Shape)
open aFN (Slot)
open qzLARrc (derivativeIndex)
open qmb8rCe (cutMatrix rankCut cap sumN_eq)
open MvPolynomial
open scoped Polynomial BigOperators
noncomputable section
local notation "T" => (Polynomial.X:ao[X])
private def nested:Poly →+* ao[X][X] :=
 (Polynomial.mapRingHom (uniqueAlgEquiv ao (Fin 1)).toRingHom).comp
   (finSuccEquiv ao 1).toRingHom
private theorem coeff_chart (b c u v :ℕ) :
   (((1+MvPolynomial.X 1)^b*(z9v 1+MvPolynomial.X 0)^c:Poly).coeff (ex u v)) =
     if v≤ c∧c-v≤u then (c.choose v :ao)*(b.choose (u-(c-v)) :ao) else 0:= by
 have hcoeff (P:Poly) : ((nested P).coeff v).coeff u=P.coeff (ex u v) := by
   change ((Polynomial.map (uniqueAlgEquiv ao (Fin 1)).toRingHom
     (finSuccEquiv ao 1 P)).coeff v).coeff u= _
   rw [Polynomial.coeff_map]
   change ((uniqueAlgEquiv ao (Fin 1) ((finSuccEquiv ao 1 P).coeff v)) :ao[X]).coeff u= _
   rw [coeff_uniqueAlgEquiv,finSuccEquiv_coeff_coeff]
   rfl
 have hx :nested (z9v 1)=z1z T:= by
   have he :=finSuccEquiv_X_succ (R:=ao) (j:=(0:Fin 1))
   rw [show (0:Fin 1).succ=(1 :Fin 2) from rfl] at he
   change Polynomial.map (uniqueAlgEquiv ao (Fin 1)).toRingHom (finSuccEquiv ao 1 (z9v 1))= _
   rw [he,Polynomial.map_C]
   simp [uniqueAlgEquiv_apply]
 have hy :nested (z9v 0)=Polynomial.X:= by simp [nested,finSuccEquiv_X_zero]
 have hprod:nested ((1+MvPolynomial.X 1)^b*(z9v 1+MvPolynomial.X 0)^c)=z1z ((1+T)^b) *
     (z7y+Polynomial.C T)^c:= by
   simp only [map_mul,map_pow,map_add,map_one,hx,hy]
   rw [add_comm (z1z T) z7y]
 rw [← hcoeff,hprod,Polynomial.coeff_C_mul,Polynomial.coeff_X_add_C_pow]
 by_cases hv :v≤ c
 · rw [← mul_assoc,← Polynomial.C_eq_natCast,Polynomial.coeff_mul_C,Polynomial.coeff_mul_X_pow']
   simp [hv,Polynomial.coeff_one_add_X_pow,mul_comm]
 · simp [hv,zsx (Nat.lt_of_not_ge hv)]
private def test (a :Shape) (q d h:ℕ) :Source a q d →ₗ[ao] (Slot a q→ao) :=
 LinearMap.pi fun r =>
  if derivativeIndex r<h then
   (MvPolynomial.lcoeff ao (ex r.2.val r.1.val)).comp (bY.toLinearMap.comp (Source a q d).subtype)
  else 0
private theorem test_apply (a :Shape) (q d h:ℕ) (P:Source a q d) (r :Slot a q) :
  test a q d h P r=if derivativeIndex r<h then (bY P.val).coeff (ex r.2.val r.1.val) else 0:= by
 by_cases hr :derivativeIndex r<h <;> simp [test,hr,lcoeff]
private theorem col_mem (a :Shape) (q d h:ℕ) (s :Slot a q) :
   (cutMatrix a q d h).col s∈(test a q d h).range := by
 classical
 by_cases hd:d≤ s.1.val+s.2.val
 · have he :ex s.2.val s.1.val∈zxp (@stockExp a q d) := by
     have hb:=s.2.isLt
     have hc:=s.1.isLt
     simp only [zh4,le_min_iff] at hb hc
     apply in_stock <;> simp only [ex_zero,ex_one] <;> omega
   let P:Source a q d :=
     ⟨monomial (ex s.2.val s.1.val) 1,(monomial_mem_restrictSupport ao).mpr (Or.inl he)⟩
   refine ⟨P,?_⟩
   have hP:bY P.val=(1+MvPolynomial.X 1)^s.2.val*(z9v 1+MvPolynomial.X 0)^s.1.val := by
     change bY (monomial _ _)= _
     rw [bY,aeval_monomial,Finsupp.prod_fintype _ _ (fun _=>pow_zero _),Fin.prod_univ_two]
     simp [mul_comm]
   funext r
   rw [test_apply,hP,coeff_chart]
   change _=cutMatrix a q d h r s
   by_cases hr :derivativeIndex r<h <;> simp [cutMatrix,hd,hr]
 · refine ⟨0,?_⟩
   funext r
   simp [cutMatrix,hd,Matrix.col]
private theorem test_zero {a :Shape} {q d h:ℕ} (P:Source a q d)
   (hP:bY P.val∈restrictWeightedOrder wt h) :test a q d h P=0:= by
 funext r
 rw [test_apply]
 by_cases hr :derivativeIndex r<h
 · rw [ite_eq_left hr]
   by_contra hn
   have he :=mem_restrictWeightedOrder.mp hP _ (MvPolynomial.mem_support_iff.mpr hn)
   simp [wt,z1K,Fin.sum_univ_two,smul_eq_mul,Nat.add_comm,
     derivativeIndex,z5A] at he hr
   omega
 · exact ite_eq_right hr
private def probe (k :ℕ) :Poly →ₐ[ao] ao[X] :=aeval ![T^k,T]
private theorem mon_sub {p r :ao[X]} {e f :ℕ}
  (hp:p.Monic∧p.natDegree=e) (hr :r.natDegree≤f) (hef :f<e) :
  (p-r).Monic∧(p-r).natDegree=e := by
 have he :r.natDegree<p.natDegree := by omega
 exact ⟨hp.1.sub_of_left (Polynomial.degree_lt_degree he),
  (Polynomial.natDegree_sub_eq_left_of_natDegree_lt he).trans hp.2⟩
private theorem mon_pow {p:ao[X]} {e :ℕ}
   (hp:p.Monic∧p.natDegree=e) (n:ℕ) :
   (p^n).Monic∧(p^n).natDegree=n*e :=
 ⟨hp.1.pow n,by rw [Polynomial.natDegree_pow,hp.2]⟩
private theorem mon_mul {p r :ao[X]} {e f :ℕ}
   (hp:p.Monic∧p.natDegree=e) (hr :r.Monic∧r.natDegree=f) :
   (p*r).Monic∧(p*r).natDegree=e+f :=
 ⟨hp.1.mul hr.1,by rw [Polynomial.natDegree_mul hp.1.ne_zero hr.1.ne_zero,hp.2,hr.2]⟩
private theorem probe_witness (k d n l c:ℕ) (hk :2<k) (hl:l≤ c) :
   let p:=probe k (witness d n l c)
   p.Monic∧p.natDegree=n-c+(d-c)+k*c:= by
 let r :=Zz d l c
 have hU: (probe k (z9v 1)).Monic∧(probe k (z9v 1)).natDegree=1 := by simp [probe]
 have hV: (probe k (z9v 0)).Monic∧(probe k (z9v 0)).natDegree=k := by simp [probe]
 have hD: (probe k (z9v 1-1)).Monic∧(probe k (z9v 1-1)).natDegree=1 := by
   rw [map_sub,map_one]
   exact mon_sub hU (by simp : (1 :ao[X]).natDegree≤0) (by decide)
 have hQ: (probe k (z9v 0-(z9v 1-1)*z9v 1)).Monic ∧
     (probe k (z9v 0-(z9v 1-1)*z9v 1)).natDegree=k := by
   rw [map_sub,map_mul]
   exact mon_sub hV (Polynomial.natDegree_mul_le_of_le hD.2.le hU.2.le) hk
 have hZ: (probe k (z9v 0-(z9v 1-1))).Monic∧(probe k (z9v 0-(z9v 1-1))).natDegree=k := by
   rw [map_sub]
   exact mon_sub hV hD.2.le (by omega)
 have hr :r≤ c-l:=min_le_right _ _
 have he :l+r+(c-l-r)=c:= by omega
 dsimp only
 simp only [witness,map_mul,map_pow]
 have h:=mon_mul (mon_mul (mon_mul (mon_mul (mon_pow hD (n-c)) (mon_pow hV l))
   (mon_pow hQ r)) (mon_pow hZ (c-l-r))) (mon_pow hU (d-c))
 refine ⟨h.1,h.2.trans ?_⟩
 simp only [Nat.mul_one]
 have hm:l*k+r*k+(c-l-r)*k=k*c:= by
   rw [← zNE,← zNE,he,z5A]
 calc
   _=(n-c)+(d-c)+(l*k+r*k+(c-l-r)*k) := by ac_rfl
   _ = _:= by rw [hm]
private theorem independent_of_degree {ι:Type} {f :ι→ao[X]}
   (hm : ∀ i,(f i).Monic) (hi:zq4 (fun i=>(f i).natDegree)) :
   LinearIndependent ao f := by
 classical
 rw [linearIndependent_iff']
 intro s g he i hi'
 by_contra hgi
 obtain ⟨j,hj,hmax⟩:=(s.filter fun j=>g j≠0).exists_max_image (fun j=>(f j).natDegree)
   ⟨i,Finset.mem_filter.mpr ⟨hi',hgi⟩⟩
 have hj' := Finset.mem_filter.mp hj
 have hc:=congrArg (z9j ao (f j).natDegree) he
 simp only [map_sum,map_smul,map_zero,Polynomial.lcoeff_apply] at hc
 rw [Finset.sum_eq_single_of_mem j hj'.1] at hc
 · exact hj'.2 (by simpa [(hm j).coeff_natDegree] using hc)
 · intro l hl hne
   by_cases hgl:g l=0
   · simp [hgl]
   · have hlt:=(hmax l (Finset.mem_filter.mpr ⟨hl,hgl⟩)).lt_of_ne (hi.ne hne)
     simp [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
private def badC {a :Shape} {q d h:ℕ} (i:Bad a q d h) :ℕ :=
 lo q d i.1.val+Bp a q d h i.1.val+i.2.val
private theorem bad_bounds {a :Shape} {q d h:ℕ} (i:Bad a q d h) :
  lo q d i.1.val≤badC i∧badC i<stop a i.1.val ∧
   h≤ i.1.val+(badC i-lo q d i.1.val) := by
 have hi:=i.2.isLt
 dsimp [badC,width,Bp] at hi ⊢
 omega
private theorem bad_independent {a :Shape} {q d h:ℕ} (hd:d≤q) :
   z14 ao (fun i:Bad a q d h =>
     witness d i.1.val (lo q d i.1.val) (badC i)) := by
 let k :=q+3
 apply zCu (probe k).toLinearMap
 have hp (i:Bad a q d h) :=probe_witness k d i.1.val (lo q d i.1.val) (badC i)
   (by dsimp [k]; omega) (bad_bounds i).1
 apply independent_of_degree (fun i=>(hp i).1)
 intro i j he
 let b (i:Bad a q d h) :=i.1.val-badC i+(d-badC i)
 have hb (i:Bad a q d h) :b i<k := by
   have hn:=i.1.isLt
   have hc:=(bad_bounds i).1
   dsimp [b,k,lo] at *
   omega
 change (probe k _).natDegree=(probe k _).natDegree at he
 rw [(hp i).2,(hp j).2] at he
 change b i+k*badC i=b j+k*badC j at he
 have hbe :=congrArg (fun x :ℕ=>x % k) he
 simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (hb i),Nat.mod_eq_of_lt (hb j)] at hbe
 rw [hbe] at he
 have hm:k*badC i=k*badC j:=Nat.add_left_cancel he
 have hce :badC i=badC j:=Nat.eq_of_mul_eq_mul_left (by dsimp [k]; omega) hm
 have hi:=(bad_bounds i).2.1
 have hj:=(bad_bounds j).2.1
 dsimp [stop] at hi hj
 have hn:i.1=j.1 :=zmq (by dsimp [b] at hbe; omega)
 refine Sigma.ext hn ((Fin.heq_ext_iff (congrArg (fun n:jJ a q d =>
   width a q d n - Bp a q d h n) hn)).2 ?_)
 have hh:=congrArg (fun n:jJ a q d=>lo q d n.val+Bp a q d h n.val) hn
 dsimp [badC] at hce
 omega
theorem kept_eq (a :Shape) (q d h:ℕ) :
   (∑ n:jJ a q d,Bp a q d h n.val)=cap a q d h:= by
 rw [zdx,cap,sumN_eq,← min_assoc]
 have hr :z4x (min (min (q+1) (a.j+1-d)) h) =
     (z4x (min (q+1) (a.j+1-d))).filter (· < h) := by
   ext n
   simp [lt_min_iff,and_assoc]
 rw [hr,Finset.sum_filter]
 refine zUo rfl fun n _ => ?_
 by_cases hh:n<h
 · rw [ite_eq_left hh]
   unfold Bp width lo stop
   omega
 · simp [Bp,show h-n=0 by omega,hh]
theorem rank_le_cap (a :Shape) (q d h:ℕ) (hd:d≤q) :rankCut a q d h≤ cap a q d h:= by
 classical
 let e :=Equiv.ofInjective (@stockExp a q d) stock_injective
 let:=Fintype.ofEquiv (Stock a q d) e
 let basis :=basisRestrictSupport ao (zxp (@stockExp a q d))
 let:zAa ao (Source a q d) :=Module.Finite.of_basis basis
 let f :=test a q d h
 let v (i:Bad a q d h) :f.ker :=
   let hi:=bad_bounds i
   ⟨⟨_,witness_source hd i.1.isLt hi.1 hi.2.1⟩,LinearMap.mem_ker.mpr (test_zero _
     (witness_order _ _ _ _ _ hi.1 (by have :=hi.2.1; dsimp [stop] at this; omega) hi.2.2))⟩
 have hv :z14 ao v :=
   zCu ((Source a q d).subtype.comp f.ker.subtype) (bad_independent hd)
 have hk :=hv.fintype_card_le_finrank
 have hn:=f.finrank_range_add_finrank_ker
 have hr :rankCut a q d h≤zsE ao f.range := by
   rw [rankCut,z0e]
   exact zFM (Submodule.span_le.mpr fun _ ⟨s,hs⟩=>hs ▸ col_mem a q d h s)
 have hs :Fintype.card (Bad a q d h)+cap a q d h=Fintype.card (Stock a q d) := by
   rw [← kept_eq,zTU,zTU,← zfW]
   exact zUo rfl fun n _=> by
     simp only [Fintype.card_fin]
     exact zxt (min_le_left _ _)
 rw [Module.finrank_eq_card_basis basis,← Fintype.card_congr e] at hn
 omega
end
end qOPkAYa
end
section
set_option autoImplicit true
namespace qOPkAYa
open Finset
open aR (Shape)
open aFN (Slot)
open P5_7_2 (TopRow)
open qje58fc (box vo windowDebit)
open qzLARrc (derivativeIndex flagMatrix flagRank windowBudget)
open qmb8rCe (rankCut cap sumN fullCost partCost window_le_cost)
private theorem gsR {s :Shape} {q:ℕ} (j:Slot s q) :
  j.2.val+j.1.val≤q:= by
 have hc:=j.1.isLt
 have hb:=j.2.isLt
 simp only [zh4,le_min_iff] at hc hb
 omega
private theorem window_rank (t:TopRow) (q g a :ℕ) (ha :a≤q) :
    (vo t q g a).rank=flagRank (box t) q ((g:ℤ)-(box t).j) (q-a) := by
  have he :vo t q g a=flagMatrix (box t) q ((g:ℤ)-(box t).j) (q-a) := by
    ext r c
    let J:=(box t).j
    let B:=(box t).b
    let i:=derivativeIndex c
    let j:=derivativeIndex r
    change (if a≤ c.1.val+c.2.val∧r.1.val≤ c.1.val ∧
        c.1.val≤ r.2.val+r.1.val∧J≤g+i∧g+i<J+(B+J) ∧
        J≤g+q+j∧g+q+j<J+(B+J) then
        ((c.1.val.choose r.1.val*c.2.val.choose (r.2.val+r.1.val-c.1.val) :ℕ) :cu.L) else 0) =
      flagMatrix (box t) q ((g:ℤ)-J) (q-a) r c
    unfold flagMatrix
    have hc:=gsR c
    have hh: (a≤ c.1.val+c.2.val∧r.1.val≤ c.1.val ∧
        c.1.val≤ r.2.val+r.1.val∧J≤g+i∧g+i<J+(B+J) ∧
        J≤g+q+j∧g+q+j<J+(B+J)) ↔
      (q-c.1.val-c.2.val≤q-a∧0≤(g:ℤ)-J+i ∧
        (g:ℤ)-J+q+j<((B+J:ℕ) :ℤ) ∧
        r.1.val≤ c.1.val∧c.1.val-r.1.val≤ r.2.val) := by
      dsimp only [i,j,derivativeIndex]
      omega
    change _=(if _ then (_:cu.L) else 0)
    by_cases hp:a≤ c.1.val+c.2.val∧r.1.val≤ c.1.val ∧
        c.1.val≤ r.2.val+r.1.val∧J≤g+i∧g+i<J+(B+J) ∧
        J≤g+q+j∧g+q+j<J+(B+J)
    · rw [ite_eq_left hp,ite_eq_left (hh.mp hp),Nat.cast_mul,show r.2.val+r.1.val-c.1.val =
        r.2.val-(c.1.val-r.1.val) by have :=hp.2.1; omega]
    · rw [ite_eq_right hp,ite_eq_right (fun h=>hp (hh.mpr h))]
  rw [he,flagRank]
theorem gMW (t:TopRow) :
   windowDebit t≤windowBudget (box t) t.shape.U:= by
 unfold windowDebit windowBudget
 refine sum_le_sum fun q _=>sum_le_sum fun g _ => ?_
 rw [window_rank t q g 0 (Nat.zero_le q)]
 simp only [Nat.sub_zero]
 rw [show t.shape.U+1+t.shape.B=t.shape.U+(box t).b+1 by
   change t.shape.U+1+t.shape.B=t.shape.U+t.shape.B+1
   omega]
 apply Nat.add_le_add_left
 calc
   _ ≤ ∑ a∈range q,(vo t q g (a+1)).rank :=
     sum_le_sum_of_subset (range_mono (min_le_left _ _))
   _ = _:= by
     rw [← sum_range_reflect (fun a=>flagRank (box t) q ((g:ℤ)-(box t).j) a)]
     refine sum_congr rfl fun a ha => ?_
     have ha' := mem_range.mp ha
     rw [window_rank _ _ _ _ (by omega),show q-(a+1)=q-1-a by omega]
theorem cost_le (t:TopRow)
    (hc : ∀ q d h:ℕ,q≤t.shape.J→d≤q→h≤t.shape.J →
      rankCut (box t) q d h≤ cap (box t) q d h) :
    windowDebit t ≤
      sumN (fun q=>fullCost (box t) t.shape.U q+partCost (box t) t.shape.U q)
        (t.shape.B+1) :=
  (gMW t).trans (window_le_cost _ _ hc)
end qOPkAYa
end
section
namespace qOPkAYa
open Finset
open aR (Shape)
open P5_7_2 (TopRow)
open q7IA62d (ama)
open qje58fc (box)
open qmb8rCe (sumN sumN_eq fullCost partCost mass)
private theorem bK2 (w n:ℕ) : (∑ i∈range n,min w (i+1))=Fu w n:= by
  let k :=min w n
  have hl: (∑ i∈range k,min w (i+1))=(k+1)*k/2 := by
    have hs :=sum_range_id (k+1)
    rw [sum_range_succ'] at hs
    rw [← (show (∑ i∈range k,(i+1))=(k+1)*k/2 by simpa [z5A] using hs)]
    refine sum_congr rfl fun i hi=>min_eq_right ?_
    have hi' := mem_range.mp hi
    dsimp [k] at hi'
    omega
  have hr : (∑ i∈range (n-k),min w (k+i+1))=(n-k)*k := by
    calc
      _ = ∑ i∈range (n-k),k := by
        refine sum_congr rfl fun i hi => ?_
        have hi' := mem_range.mp hi
        dsimp [k] at *
        omega
      _ = _:= by simp
  have hn:k+(n-k)=n:= by dsimp [k]; omega
  calc
    _ = ∑ i∈range (k+(n-k)),min w (i+1) := by rw [hn]
    _ = _:= by rw [sum_range_add,hl,hr]; rfl
private theorem ramp_shift (w J n:ℕ) (hn:n≤J) :
  (∑ i∈range J,min w (i+1-n))=Fu w (J-n) := by
 have hJ:J=n+(J-n) := by omega
 conv_lhs=>rw [hJ]
 rw [sum_range_add]
 have h0: (∑ i∈range n,min w (i+1-n))=0:= by
  refine sum_eq_zero fun i hi => ?_
  have hi' := mem_range.mp hi
  simp [show i+1-n=0 by omega]
 rw [h0,zero_add,← bK2]
 refine sum_congr rfl fun i _ => ?_
 simp [zVg]
theorem mass_eq (a :Shape) (q d:ℕ) :mass a q d=fastMass a q d:= by
 unfold mass fastMass
 simp only [sumN_eq]
 simp_rw [← kept_eq]
 rw [sum_comm,zdx (fun n => ∑ i∈range a.j,Bp a q d (i+1) n)]
 refine sum_congr rfl fun n hn => ?_
 change (∑ i∈range a.j,min (width a q d n) (i+1-n))= _
 exact ramp_shift _ _ _ (by have :=mem_range.mp hn; omega)
theorem part_eq (a :Shape) (U q:ℕ) :partCost a U q=fastPart a U q:= by
 simp only [partCost,fastPart,flags,mass_eq]
theorem b6N (t:TopRow) :
  ama t (fun q _ _=>t.shape.B+t.shape.J-q)=sumN (base (box t)) (t.shape.B+1) := by
 simp only [ama,base,sumN_eq,sum_const,card_range,nsmul_eq_mul]
 rfl
theorem sum_add (f g:ℕ→ℕ) (n:ℕ) :
   sumN (fun i=>f i+g i) n=sumN f n+sumN g n:= by
 induction n with
 | zero=>rfl
 | succ n ih=>simp only [sumN,ih]; ac_rfl
private theorem sum_append (f :ℕ→ℕ) (n k :ℕ) :
   sumN f (n+k)=sumN f n+sumN (fun i=>f (n+i)) k := by
 induction k with
 | zero=>simp [sumN]
 | succ k ih =>
   change sumN f (n+k)+f (n+k) =
    sumN f n+(sumN (fun i=>f (n+i)) k+f (n+k))
   rw [ih,zVg]
theorem checked {f :ℕ→ℕ} {n k x y :ℕ} (hx :sumN f n=x)
  (hy :sumN (fun i=>f (n+i)) k=y) :sumN f (n+k)=x+y := by
 rw [sum_append,hx,hy]
theorem part_tail {a :Shape} {U q k l:ℕ} (hq:a.j≤q)
  (hk :fastMass a a.j 0=k) (hl:flags a a.j=l) :
  fastPart a U q=qmb8rCe.factor a U q*k+l:= by
 simp only [fastPart,min_eq_right hq,hk,hl]
private theorem grade_linear (a :Shape) (U q:ℕ) (hb:0<a.b)
    (hU:a.b≤U+1) (hq:q≤a.b) :
    fullCost a U q+partCost a U q =
      (U+1-a.b)*countedRank a q +
        (fullCost a (a.b-1) q+fastPart a (a.b-1) q) := by
  let k :=U+1-a.b
  have hf :qmb8rCe.factor a U q=k+qmb8rCe.factor a (a.b-1) q:= by
    unfold qmb8rCe.factor k
    omega
  have hadd (c b:ℕ) :
      (a.b-q+(b+2*c))*(qmb8rCe.factor a U q+(b+c)) =
      k*(a.b-q+(b+2*c))+(a.b-q+(b+2*c))*(qmb8rCe.factor a (a.b-1) q+(b+c)) := by
    rw [hf]
    ring
  have hfull:fullCost a U q=k*fullRank a q+fullCost a (a.b-1) q:= by
    unfold fullCost fullRank
    simp only [sumN_eq,hadd,sum_add_distrib,← mul_sum]
  unfold countedRank
  rw [hfull,part_eq]
  unfold fastPart
  rw [hf]
  ring
theorem cost_linear (a :Shape) (U:ℕ) (hb:0<a.b) (hU:a.b≤U+1) :
    sumN (fun q=>fullCost a U q+partCost a U q) (a.b+1) =
      (U+1-a.b)*sumN (countedRank a) (a.b+1) +
        (sumN (fullCost a (a.b-1)) (a.b+1)+sumN (fastPart a (a.b-1)) (a.b+1)) := by
  rw [← sum_add]
  simp only [sumN_eq,← sum_add_distrib,mul_sum]
  exact sum_congr rfl fun q hq=>grade_linear a U q hb hU (by have :=mem_range.mp hq; omega)
end qOPkAYa
end
end
section
section
set_option autoImplicit true
namespace qYur1ad
noncomputable section
open aR (ao Shape)
open jA (mA)
open aFN (aTo)
open qzLARrc (LocalCoeff bjM LocalSlot localColumn localImage)
open qA0rFHd (WindowRow WindowSlot windowColumn seedWindow b3b)
open MvPolynomial
open scoped BigOperators
private def specializeOne (R:Type*) [za6 R] :
   z3y mA R →ₐ[R] z3y (Fin 3) R :=
 ((Polynomial.aeval (1 :z3y (Fin 3) R)).restrictScalars R).comp
   (optionEquivLeft R (Fin 3)).toAlgHom
private def restore (R:Type*) [za6 R] (k :ℕ) :
  z3y (Fin 3) R →ₗ[R] z3y mA R :=
 AddMonoidAlgebra.mapDomainLinearMap R R
  (fun d:Fin 3 →₀ ℕ=>d.optionElim (k - d.degree))
private theorem restore_specialize {R:Type*} [za6 R] {k :ℕ}
  {p:z3y mA R} (hp:p.IsHomogeneous k) :
  restore R k (specializeOne R p)=p:= by
 classical
 rw [p.as_sum,map_sum,map_sum]
 refine zUo rfl fun d hd => ?_
 have hdegree :d.degree=d none+d.some.degree := by
  exact d.sum_option_index (fun _ n=>n) (fun _=>rfl) (fun _ _ _=>rfl)
 have hk :d.degree=k := by
  rw [Finsupp.degree_eq_weight_one]
  exact hp (mem_support_iff.mp hd)
 have hseed :k - d.some.degree=d none := by omega
 simp only [specializeOne,AlgHom.comp_apply,AlgHom.restrictScalars_apply,
  AlgEquiv.coe_toAlgHom,optionEquivLeft_monomial,Polynomial.aeval_monomial,
  Algebra.algebraMap_self_apply,one_pow,mul_one]
 simp only [restore,← single_eq_monomial,AddMonoidAlgebra.mapDomainLinearMap_single,
  hseed,Finsupp.optionElim_some]
private def totalGrade {a :Shape} {U:ℕ} (i:LocalSlot a U) :ℕ :=
 i.2.1.val+i.2.2.1.val
private theorem column_grade (a :Shape) (U:ℕ) (i:LocalSlot a U) :
   (localColumn a U i).IsHomogeneous (totalGrade i) := by
 let R:=LocalCoeff (a.b+a.j)
 let q:=i.2.2.1.val
 let c:=i.2.2.2.1.val
 let b:=i.2.2.2.2.val
 have hc:c≤q:=(le_min_iff.mp (Nat.lt_succ_iff.mp i.2.2.2.1.isLt)).1
 have hb:b≤q - c:=(le_min_iff.mp (Nat.lt_succ_iff.mp i.2.2.2.2.isLt)).1
 have he :0*i.1.val+i.2.1.val+1*(q - c - b)+1*b+1*c =
     totalGrade i:= by
   unfold totalGrade
   change 0*i.1.val+i.2.1.val+1*(q - c - b)+1*b+1*c =
     i.2.1.val+q
   omega
 rw [← he]
 exact (((((isHomogeneous_C mA _).pow _).mul (isHomogeneous_X_pow none _)).mul
   (((isHomogeneous_X R _).add (isHomogeneous_C_mul_X _ _)).pow _)).mul
   (((isHomogeneous_X R _).add (isHomogeneous_C_mul_X _ _)).pow _)).mul
   (((isHomogeneous_X R _).add (isHomogeneous_C_mul_X _ _)).pow _)
private def windowIndex {a :Shape} {U:ℕ} (i:LocalSlot a U) :
  WindowSlot a (totalGrade i-U) (min (totalGrade i) a.b) := by
 have hs :=i.2.1.isLt
 have hq:=i.2.2.1.isLt
 refine ⟨i.1,⟨⟨⟨i.2.2.1.val,?_⟩,?_⟩,i.2.2.2⟩⟩
 all_goals dsimp only [totalGrade]; omega
private theorem specialize_column (a :Shape) (U:ℕ) (i:LocalSlot a U) :
  specializeOne _ (localColumn a U i)=windowColumn a (windowIndex i) := by
 simp [specializeOne,localColumn,windowColumn,windowIndex,aTo]
private theorem finrank_le_sum_maps {E F:Type*}
    [AddCommGroup E] [Module ao E] [AddCommGroup F] [Module ao F]
    (s :Finset ℕ) (Q:zpI ao E) (W:ℕ→zpI ao F)
    (f :ℕ→F →ₗ[ao] E) (hW : ∀ k,zAa ao (W k))
    (hQ:Q≤ s.sup (fun k=>(W k).map (f k))) :
    zsE ao Q ≤ ∑ k∈s,zsE ao (W k) := by
  let P (k :ℕ) :=(W k).map (f k)
  have hP (k :ℕ) :zAa ao (P k) := by
    let:=hW k
    exact z2p _ _
  let:zAa ao ↥(s.sup P) := @Submodule.finite_finset_sup ao E _ _ _ ℕ s P hP
  exact (zFM hQ).trans <|
    (@b3b ℕ E _ _ s P hP).trans <|
      zQk fun k _=> by
        let:=hW k
        exact zSE (f k) (W k)
private def windowLift (a :Shape) (k :ℕ) :WindowRow a →ₗ[ao] bjM (a.b+a.j) :=
 (restore (LocalCoeff (a.b+a.j)) k).restrictScalars ao
private theorem local_le (a :Shape) (U:ℕ) :
    localImage a U≤(z4x (U + a.b+1)).sup
      (fun k=>(seedWindow a (k-U) (min k a.b)).map (windowLift a k)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  have hi:totalGrade i∈z4x (U + a.b+1) := by
    have hs :=i.2.1.isLt
    have hq:=i.2.2.1.isLt
    rw [zIR,totalGrade]
    omega
  have hm:localColumn a U i ∈
      (seedWindow a (totalGrade i-U) (min (totalGrade i) a.b)).map
        (windowLift a (totalGrade i)) := by
    refine ⟨windowColumn a (windowIndex i),zBO ⟨windowIndex i,rfl⟩,?_⟩
    change restore _ (totalGrade i) (windowColumn a (windowIndex i))= _
    rw [← specialize_column,restore_specialize (column_grade a U i)]
  exact (zZi (f := fun k=>(seedWindow a (k-U) (min k a.b)).map
    (windowLift a k)) hi) hm
set_option maxSynthPendingDepth 16 in
theorem proof :qA0rFHd.c1 := by
 classical
 intro a U
 let s :=z4x (U + a.b+1)
 let W (k :ℕ) :=seedWindow a (k-U) (min k a.b)
 have hW (k :ℕ) :zAa ao (W k) := by
  unfold W seedWindow
  exact z3g ao (zlS _)
 change zsE ao (localImage a U) ≤ ∑ k∈s,zsE ao (W k)
 have h := @finrank_le_sum_maps (bjM (a.b+a.j)) (WindowRow a)
  inferInstance inferInstance inferInstance inferInstance
  s (localImage a U) W (windowLift a) hW (local_le a U)
 exact h
end
end qYur1ad
end
section
set_option autoImplicit true
namespace qnKm5Ba
noncomputable section
open aR (ao Shape)
open aFN (Slot aTo)
open qzLARrc (LocalCoeff localParameter)
open qA0rFHd (WindowRow PhysicalExponent seedWindow
 HomogeneousSlot homogeneousColumn homogeneousImage reciprocalImage)
private theorem sub_pow_mem {R:Type*} [za6 R] [Algebra ao R]
   (S:zpI ao R) (z p:R) (n:ℕ) (h : ∀ k≤n,p*z^k∈S) :
   p*(1 - z)^n∈S:= by
 induction n generalizing p with
 | zero=>simpa only [pow_zero,mul_one] using h 0 le_rfl
 | succ n ih =>
   rw [pow_succ',← mul_assoc,mul_sub,mul_one,sub_mul]
   exact S.sub_mem (ih p fun k hk=>h k (by omega)) (ih (p*z) fun k hk=> by
     rw [mul_assoc,← pow_succ']
     exact h (k+1) (by omega))
private theorem preimage_mem (a :Shape) (x :PhysicalExponent a) {lo q hi:ℕ}
   (s :Slot a q) (hl:lo≤q) (hq:q≤hi) :
   let t:=localParameter (a.b+a.j)
   znf t^x.val*aTo t 1^s.2.val*aTo t 2^s.1.val *
     (1-aTo t 0)^(hi - q)∈reciprocalImage a hi (hi-lo) := by
 dsimp only
 refine sub_pow_mem (R:=WindowRow a) (reciprocalImage a hi (hi-lo))
   (aTo (localParameter (a.b+a.j)) 0) _ (hi - q) ?_
 intro k hk
 have hc:=s.1.isLt
 have hb:=s.2.isLt
 simp only [zh4,le_min_iff] at hc hb
 let r :=k+s.2.val+s.1.val
 let c:Fin (min r (min a.t (a.j/2))+1) :=
   ⟨s.1.val,by simp only [zh4,le_min_iff]; dsimp [r]; omega⟩
 let b:Fin (min (r - c.val) (a.j - 2*c.val)+1) :=
   ⟨s.2.val,by
     change s.2.val< min (r - s.1.val) (a.j - 2*s.1.val)+1
     simp only [zh4,le_min_iff]
     dsimp [r]
     omega⟩
 have hv :r - c.val - b.val=k := by
   change r - s.1.val - s.2.val=k
   dsimp [r]
   omega
 have hr :r∈z4x (hi+1) := by
   rw [zIR]
   dsimp [r]
   omega
 let i:HomogeneousSlot a r (min r (hi-lo)) :=
   ⟨x,⟨⟨c,b⟩,by
     change r - c.val - b.val≤_
     rw [hv]
     dsimp [r]
     exact le_min (by omega) (by omega)⟩⟩
 have hm:homogeneousColumn a r i.1 i.2.val∈reciprocalImage a hi (hi-lo) :=
   (zZi (f := fun r=>homogeneousImage a r (min r (hi-lo))) hr)
     (zBO (zWL i))
 unfold homogeneousColumn at hm
 change znf _^x.val*aTo _ 0^(r - c.val - b.val) *
   aTo _ 1^s.2.val*aTo _ 2^s.1.val∈_ at hm
 rw [hv] at hm
 convert hm using 1
 ac_rfl
private theorem collect_factors {R:Type*} [CommMonoid R]
  (d y p V W v :R) (b c j:ℕ) (h:d*v^(b+c+j)=y) :
  d*(p*(V^b*v^b)*(W^c*v^c)*v^j)=p*y*V^b*W^c:= by
 calc
  _=p*V^b*W^c*(d*v^(b+c+j)) := by
    simp only [pow_add]
    ac_rfl
  _ = _:= by rw [h]; ac_rfl
theorem proof :qA0rFHd.c2 := by
 classical
 intro a lo hi _ _
 let L:=a.b+a.j
 let t:=localParameter L
 let J (i:Fin 3) :=aTo t i
 let y :=1+J 0
 have ht:t^L=0:= by
   rw [show t=zVv _ (z7y:Polynomial ao) from rfl,← map_pow]
   exact Ideal.Quotient.eq_zero_iff_mem.mpr (zCn (zT1 _))
 have hnil:IsNilpotent (J 0) := by
   refine ⟨L,?_⟩
   change (znf t*z9v (0:Fin 3))^L=0
   rw [mul_pow,← map_pow,ht,map_zero,zero_mul]
 obtain ⟨u,hu⟩:=hnil.isUnit_one_add
 let v :WindowRow a := ↑(u⁻¹)
 have hy :y*v=1 := by
   change (1+J 0)*v=1
   rw [← hu]
   exact u.mul_inv
 let φ:WindowRow a →ₐ[LocalCoeff L] WindowRow a :=
   MvPolynomial.aeval (fun i=>z9v i*v)
 have hC:φ (znf t)=znf t:=MvPolynomial.aeval_C _ _
 have hj (i:Fin 3) :φ (J i)=J i*v := by
   fin_cases i <;> simp [φ,J,aTo,add_mul,mul_assoc]
 have hv :φ (1-J 0)=v := by
   rw [map_sub,map_one,hj,sub_eq_iff_eq_add]
   simpa only [y,add_mul,one_mul] using hy.symm
 let f :WindowRow a →ₗ[ao] WindowRow a :=
   (LinearMap.mulLeft ao (y ^hi)).comp (φ.restrictScalars ao).toLinearMap
 let S:=reciprocalImage a hi (hi-lo)
 have hle :seedWindow a lo hi≤S.map f := by
   apply Submodule.span_le.mpr
   rintro _ ⟨⟨x,⟨⟨q,hl⟩,s⟩⟩,rfl⟩
   have hq:q.val≤hi:=Nat.lt_succ_iff.mp q.isLt
   have hc:=s.1.isLt
   have hb:=s.2.isLt
   simp only [zh4,le_min_iff] at hc hb
   refine Submodule.mem_map.mpr ⟨_,preimage_mem a x s hl hq,?_⟩
   change y ^hi*φ (znf t^x.val*J 1^s.2.val*J 2^s.1.val *
     (1-J 0)^(hi - q.val)) =
     znf t^x.val*y ^(q.val - s.1.val - s.2.val)*J 1^s.2.val*J 2^s.1.val
   let n:=s.2.val+s.1.val+(hi - q.val)
   let e :=q.val - s.1.val - s.2.val
   have hn:e+n=hi:= by dsimp [e,n]; omega
   have hcancel:y ^hi*v^n=y ^e := calc
     _=y ^(e+n)*v^n:= by rw [hn]
     _=y ^e*(y*v)^n:= by simp only [pow_add,mul_pow,mul_assoc]
     _ = _:= by rw [hy,one_pow,mul_one]
   simp only [map_mul,map_pow,hC,hj,hv,mul_pow]
   exact collect_factors (y ^hi) (y ^e) (znf t^x.val) (J 1) (J 2) v
     s.2.val s.1.val (hi - q.val) hcancel
 let P (r :ℕ) :=homogeneousImage a r (min r (hi-lo))
 have hfinite (r :ℕ) :zAa ao ↥(P r) :=
   z3g ao (zlS _)
 let:zAa ao ↥S:= by
   change zAa ao ↥((z4x (hi+1)).sup P)
   exact @Submodule.finite_finset_sup ao (WindowRow a) _ _ _ ℕ (z4x (hi+1)) P hfinite
 exact (zFM hle).trans (zSE f S)
end
end qnKm5Ba
end
section
set_option autoImplicit true
namespace qWpt85c
noncomputable section
open aR (ao Shape)
open aFN (Slot)
open qzLARrc (LocalCoeff localParameter derivativeIndex flagMatrix flagRank)
open qA0rFHd (WindowRow PhysicalExponent homogeneousColumn homogeneousImage b3b)
open MvPolynomial (C)
open scoped BigOperators Polynomial
private theorem slotBounds {a :Shape} {q:ℕ} (s :Slot a q) :
  s.1.val≤a.t∧s.1.val+s.2.val≤q∧derivativeIndex s≤a.j:= by
 have hc:=s.1.isLt
 have hb:=s.2.isLt
 simp only [zh4,le_min_iff] at hc hb
 unfold derivativeIndex
 omega
private def aQs (a :Shape) (q c b:ℕ) (ht:c≤a.t) (hq:c+b≤q)
  (hj:b+2*c≤a.j) :Slot a q:= by
 let c' : Fin (min q (min a.t (a.j/2))+1) :=
  ⟨c,by simp only [zh4,le_min_iff]; omega⟩
 exact ⟨c',⟨b,by
  change b< min (q - c) (a.j - 2*c)+1
  simp only [zh4,le_min_iff]
  omega⟩⟩
private theorem slot_ext {a :Shape} {q:ℕ} {r s :Slot a q}
  (hc:r.1.val=s.1.val) (hb:r.2.val=s.2.val) :r=s := by
 rcases r with ⟨c,b⟩
 rcases s with ⟨d,e⟩
 have h:c=d:=zmq hc
 subst d
 exact congrArg (Sigma.mk c) (zmq hb)
private abbrev bQv {a :Shape} {q:ℕ} (s :Slot a q) :=
 Fin (s.2.val+1)×Fin (s.1.val+1)
private def output {a :Shape} {q:ℕ} (s :Slot a q) (p:bQv s) :Slot a q :=
 aQs a q p.2.val (p.1.val+(s.1.val - p.2.val))
   (by have :=(slotBounds s).1; have :=p.2.isLt; omega)
   (by have :=(slotBounds s).2.1; have :=p.1.isLt; have :=p.2.isLt; omega)
   (by
     have h:=(slotBounds s).2.2
     have :=p.1.isLt
     have :=p.2.isLt
     unfold derivativeIndex at h
     omega)
private theorem output_injective {a :Shape} {q:ℕ} (s :Slot a q) :
  zq4 (output s) := by
 intro p p' he
 have hg:=congrArg (fun r :Slot a q=>r.1.val) he
 have hf :=congrArg (fun r :Slot a q=>r.2.val) he
 change p.2.val=p'.2.val at hg
 change p.1.val+(s.1.val - p.2.val)=p'.1.val+(s.1.val - p'.2.val) at hf
 exact Prod.ext (zmq (by omega)) (zmq hg)
private def jetTerm (a :Shape) (n i j k :ℕ) :WindowRow a :=
 C (localParameter (a.b+a.j))^n *
   z9v 0^i*z9v 1^j*z9v 2^k
private theorem jetTerm_zero (a :Shape) {n:ℕ} (hn:a.b+a.j≤n) (i j k :ℕ) :
  jetTerm a n i j k=0:= by
 let L:=a.b+a.j
 let f :ao[X] →+* LocalCoeff L:=zVv _
 have h:localParameter L^L=0:= by
  change f z7y ^L=0
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (zCn (zT1 _))
 have hC: (C (localParameter L) :WindowRow a)^L=0:= by
  rw [← map_pow,h,map_zero]
 let T:WindowRow a :=C (localParameter L)
 have hpow:T^n=0:= calc
  T^n=T^(L+(n - L)) :=congrArg (T ^ ·) (by omega)
  _=T^L*T^(n - L) :=pow_add _ _ _
  _=0:=(congrArg (· * T^(n - L)) hC).trans (zero_mul _)
 change T^n*_ *_ *_=0
 simp only [hpow,zero_mul]
private def rowTerm (a :Shape) (q:ℕ) (ν:ℤ) (r :Slot a q) :WindowRow a :=
 jetTerm a (ν+(q:ℤ)+(derivativeIndex r :ℤ)).toNat
  (q - r.1.val - r.2.val) r.2.val r.1.val
private def realize (a :Shape) (q:ℕ) (ν:ℤ) :
  (Slot a q→ao) →ₗ[ao] WindowRow a where
 toFun v := ∑ r,v r•rowTerm a q ν r
 map_add' u v := by simp only [Pi.add_apply,add_smul,zfW]
 map_smul' g v := by simp only [RingHom.id_apply,Pi.smul_apply,Finset.smul_sum,smul_assoc]
private abbrev offset {a :Shape} {q:ℕ} (x :PhysicalExponent a) (s :Slot a q) :ℤ :=
 (x.val :ℤ)-(derivativeIndex s :ℤ)
private def factor {a :Shape} {q:ℕ} {s :Slot a q} (p:bQv s) :ao :=
 (s.1.val.choose p.2.val :ao)*(s.2.val.choose p.1.val :ao)
private def term {a :Shape} {q:ℕ} (x :PhysicalExponent a) (s :Slot a q)
  (p:bQv s) :WindowRow a :=
 jetTerm a (x.val+(q - s.1.val - s.2.val)+p.1.val+p.2.val)
  ((q - s.1.val - s.2.val)+(s.2.val - p.1.val))
  (p.1.val+(s.1.val - p.2.val)) p.2.val
private theorem add_pow_fin {R:Type*} [CommSemiring R] (u v :R) (n:ℕ) :
   (u+v)^n = ∑ i:Fin (n+1),u^i.val*v^(n - i.val)*n.choose i.val :=
 (add_pow u v n).trans
   (zdx (fun i=>u^i*v^(n - i)*n.choose i) (n+1)).symm
private theorem expand {R:Type*} [CommSemiring R] (T A B D:R) (x v b c:ℕ) :
    T^x*(T*A)^v*(A+T*B)^b*(B+T*D)^c =
      ∑ p:Fin (b+1)×Fin (c+1),
        ((c.choose p.2.val :R)*b.choose p.1.val) *
          (T^(x+v+p.1.val+p.2.val)*A^(v+(b - p.1.val)) *
            B^(p.1.val+(c - p.2.val))*D^p.2.val) := by
  rw [add_comm A (T*B),add_comm B (T*D),add_pow_fin,add_pow_fin,
    Fintype.sum_prod_type_right]
  simp only [Finset.mul_sum,Finset.sum_mul,mul_pow]
  apply zUo rfl
  intro g _
  apply zUo rfl
  intro f _
  simp only [pow_add]
  ring
private theorem column_expand (a :Shape) (q:ℕ) (x :PhysicalExponent a) (s :Slot a q) :
  homogeneousColumn a q x s = ∑ p:bQv s,factor p•term x s p:= by
 let T:WindowRow a :=C (localParameter (a.b+a.j))
 let A:WindowRow a :=z9v 0
 let B:WindowRow a :=z9v 1
 let D:WindowRow a :=z9v 2
 change T^x.val*(T*A)^(q - s.1.val - s.2.val) *
  (A+T*B)^s.2.val*(B+T*D)^s.1.val= _
 simpa only [factor,term,jetTerm,Algebra.smul_def,map_mul,map_natCast] using
  expand T A B D x.val (q - s.1.val - s.2.val) s.2.val s.1.val
private theorem row_match {a :Shape} {q:ℕ} (x :PhysicalExponent a) (s :Slot a q)
   (p:bQv s) :
   rowTerm a q (offset x s) (output s p)=term x s p:= by
 have hq:=(slotBounds s).2.1
 have hf :=p.1.isLt
 have hg:=p.2.isLt
 unfold rowTerm term
 change jetTerm a ((offset x s)+(q:ℤ)+(derivativeIndex (output s p) :ℤ)).toNat
   (q - p.2.val-(p.1.val+(s.1.val - p.2.val)))
   (p.1.val+(s.1.val - p.2.val)) p.2.val= _
 have he : (offset x s)+(q:ℤ)+(derivativeIndex (output s p) :ℤ) =
     ((x.val+(q - s.1.val - s.2.val)+p.1.val+p.2.val :ℕ) :ℤ) := by
   change (x.val :ℤ)-((s.2.val+2*s.1.val :ℕ) :ℤ)+(q:ℤ) +
     ((p.1.val+(s.1.val - p.2.val)+2*p.2.val :ℕ) :ℤ)= _
   omega
 rw [he,Int.toNat_natCast,show q - p.2.val-(p.1.val+(s.1.val - p.2.val)) =
   (q - s.1.val - s.2.val)+(s.2.val - p.1.val) by omega]
private theorem matrix_off {a :Shape} {q:ℕ} (ν:ℤ) (w:ℕ) (r s :Slot a q)
    (hr :r∉zxp (output s)) :flagMatrix a q ν w r s=0:= by
  unfold flagMatrix
  split
  · rename_i h
    obtain ⟨_,_,_,hc,hb⟩:=h
    have hf :s.2.val< r.2.val-(s.1.val - r.1.val) := by
      by_contra! hf
      let p:bQv s :=⟨⟨_,zB1 hf⟩,⟨_,zB1 hc⟩⟩
      apply hr
      exact ⟨p,slot_ext rfl (show r.2.val-(s.1.val - r.1.val) +
        (s.1.val - r.1.val)=r.2.val by omega)⟩
    simp [zsx hf]
  · rfl
private theorem realize_col {a :Shape} {q w:ℕ} (x :PhysicalExponent a) (s :Slot a q)
   (hw:q - s.1.val - s.2.val≤w) :
   realize a q (offset x s) ((flagMatrix a q (offset x s) w).col s) =
     homogeneousColumn a q x s := by
 classical
 let ν:=offset x s
 change (∑ r,flagMatrix a q ν w r s•rowTerm a q ν r)= _
 rw [column_expand]
 rw [← zVG (s₁:=Finset.univ.image (output s)) (Finset.subset_univ _)
   (fun r _ hr=> by
     have h:r∉zxp (output s) := by simpa using hr
     rw [matrix_off ν w r s h,zero_smul]),
   Finset.sum_image (output_injective s).injOn]
 apply zUo rfl
 intro p _
 let r :=output s p
 change flagMatrix a q ν w r s•rowTerm a q ν r=factor p•term x s p
 have hc:r.1.val≤ s.1.val :=Nat.lt_succ_iff.mp p.2.isLt
 have hb:s.1.val - r.1.val≤ r.2.val := by
   change s.1.val - p.2.val≤p.1.val+(s.1.val - p.2.val)
   omega
 have hsub:r.2.val-(s.1.val - r.1.val)=p.1.val := by
   change p.1.val+(s.1.val - p.2.val)-(s.1.val - p.2.val)=p.1.val
   omega
 have hx :0≤ν+(derivativeIndex s :ℤ) := by
   change 0≤(x.val :ℤ)-(derivativeIndex s :ℤ)+(derivativeIndex s :ℤ)
   omega
 by_cases h:ν+(q:ℤ)+(derivativeIndex r :ℤ)<((a.b+a.j:ℕ) :ℤ)
 · simp only [flagMatrix,hw,hx,hc,hb,h,and_self,ite_true,hsub]
   rw [row_match x s p]
   rfl
 · have hn:a.b+a.j≤(ν+(q:ℤ)+(derivativeIndex r :ℤ)).toNat := by omega
   have hz :rowTerm a q ν r=0:=jetTerm_zero a hn _ _ _
   rw [← row_match x s p,hz,smul_zero,smul_zero]
private def columns (a :Shape) (q w i:ℕ) :zpI ao (Slot a q→ao) :=
 Submodule.span ao (zxp (flagMatrix a q ((i:ℤ)-(a.j:ℤ)) w).col)
private instance finiteColumns (a :Shape) (q w i:ℕ) :
  zAa ao (columns a q w i) :=
 z3g ao (zlS _)
private def block (a :Shape) (q w i:ℕ) :zpI ao (WindowRow a) :=
 (columns a q w i).map (realize a q ((i:ℤ)-(a.j:ℤ)))
private theorem finiteBlock (a :Shape) (q w i:ℕ) :zAa ao (block a q w i) :=
 z2p (columns a q w i) (realize a q ((i:ℤ)-(a.j:ℤ)))
private theorem block_rank (a :Shape) (q w i:ℕ) :
  zsE ao (block a q w i)≤flagRank a q ((i:ℤ)-(a.j:ℤ)) w:= by
 rw [flagRank,z0e]
 exact zSE (realize a q ((i:ℤ)-(a.j:ℤ))) (columns a q w i)
private theorem cover (a :Shape) (q w:ℕ) :homogeneousImage a q w ≤
   (z4x (a.b+2*a.j)).sup (block a q w) := by
 classical
 let I:=z4x (a.b+2*a.j)
 apply Submodule.span_le.mpr
 rintro _ ⟨⟨x,s⟩,rfl⟩
 let i:=x.val+a.j - derivativeIndex s.val
 have hx :=x.isLt
 have hs :=(slotBounds s.val).2.2
 have hi:i∈I:=Finset.mem_range.mpr (by dsimp [i]; omega)
 have he : (i:ℤ)-(a.j:ℤ)=offset x s.val := by
   change ((x.val+a.j - derivativeIndex s.val :ℕ) :ℤ)-(a.j:ℤ) =
     (x.val :ℤ)-(derivativeIndex s.val :ℤ)
   omega
 apply (zZi hi:block a q w i≤I.sup (block a q w))
 change _∈(columns a q w i).map (realize a q ((i:ℤ)-(a.j:ℤ)))
 refine ⟨(flagMatrix a q ((i:ℤ)-(a.j:ℤ)) w).col s.val,
   zBO (zWL s.val),?_⟩
 simpa only [he] using realize_col x s.val s.property
theorem proof :qA0rFHd.c3:= by
 intro a q w _
 classical
 let I:=z4x (a.b+2*a.j)
 let P:=block a q w
 change zsE ao (homogeneousImage a q w) ≤
  ∑ i∈I,flagRank a q ((i:ℤ)-(a.j:ℤ)) w
 have hfinite : ∀ i,zAa ao (P i) :=finiteBlock a q w
 have :zAa ao ↥(I.sup P) :=
  @Submodule.finite_finset_sup ao (WindowRow a) _ _ _ ℕ I P hfinite
 have h₁:zsE ao (homogeneousImage a q w)≤zsE ao ↥(I.sup P) :=
  zFM (s :=homogeneousImage a q w) (t:=I.sup P) (cover a q w)
 have h₂ := @b3b ℕ (WindowRow a) _ _ I P hfinite
 exact h₁.trans (h₂.trans (zQk fun i _=>block_rank a q w i))
end
end qWpt85c
end
section
set_option autoImplicit true
namespace qVljrgb
noncomputable section
open Finset
open P5_7_2 (TopRow)
open qje58fc (box ModelIndex modelExponent modelImage modelMatrix vo windowDebit)
open qzLARrc (LocalCoeff bjM LocalSlot localParameter localColumn localImage
 derivativeIndex flagMatrix flagRank windowBudget)
open aR (ao)
open jA (mA)

open MvPolynomial
open scoped BigOperators Polynomial
private def varIndex :Fin 5→Option mA :=
 ![none,some none,some (some 0),some (some 1),some (some 2)]
private theorem varIndex_injective :zq4 varIndex := by
 intro i j
 fin_cases i <;> fin_cases j <;> decide
private def unpack :z3y (Fin 5) ao →ₐ[ao] (z3y mA ao)[X] :=
 (optionEquivLeft ao mA).toAlgHom.comp (rename varIndex)
private def cut (n:ℕ) :ao[X] →ₐ[ao] LocalCoeff n :=
 Ideal.Quotient.mkₐ ao _
private def reduce (n:ℕ) : (z3y mA ao)[X] →ₐ[ao] bjM n :=
 Polynomial.aevalTower (mapAlgHom ((cut n).comp (Algebra.ofId ao ao[X])))
  (C (localParameter n))
private def quotientCoeff {n:ℕ} (x :Fin n) :LocalCoeff n →ₗ[ao] ao:= by
 let I:Ideal ao[X] :=Ideal.span {z7y ^n}
 refine (I.restrictScalars ao).liftQ (z9j ao x.val) ?_
 intro P hP
 change P∈I at hP
 exact Polynomial.X_pow_dvd_iff.mp (Ideal.mem_span_singleton.mp hP) x.val x.isLt
private theorem quotientCoeff_cut {n:ℕ} (x :Fin n) (P:ao[X]) :
 quotientCoeff x (cut n P)=P.coeff x.val :=rfl
private theorem reduce_coeff {n:ℕ} (x :Fin n) (d:mA →₀ ℕ)
   (P: (z3y mA ao)[X]) :
   quotientCoeff x ((reduce n P).coeff d)=(P.coeff x.val).coeff d:= by
 induction P using Polynomial.induction_on' with
 | add P Q hP hQ =>
   simp only [map_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,Polynomial.coeff_add,hP,hQ]
 | monomial k f =>
   rw [← Polynomial.C_mul_X_pow_eq_monomial]
   simp only [reduce,map_mul,map_pow,Polynomial.aevalTower_C,Polynomial.aevalTower_X]
   rw [← map_pow C,mul_comm,coeff_C_mul,mapAlgHom_apply,coeff_map]
   change quotientCoeff x (cut n z7y ^k*cut n (z1z (f.coeff d)))= _
   rw [← map_pow,← map_mul,quotientCoeff_cut,mul_comm,
     zds,zds]
   split <;> simp_all
private def asLocal {t:TopRow} {U:ℕ} (i:ModelIndex t U) :LocalSlot (box t) U :=
 ⟨i.2.2.1,i.2.2.2,i.1,i.2.1⟩
private theorem reduce_image (t:TopRow) (U:ℕ) (i:ModelIndex t U) :
  reduce (t.shape.B+t.shape.J) (unpack (modelImage i))=localColumn (box t) U (asLocal i) := by
 simp [unpack,varIndex,reduce,modelImage,localColumn,asLocal,mapAlgHom_apply]
 simp only [mul_comm (z9v _) (C _)]
 rfl
private def renamedExponent {t:TopRow} {U:ℕ} (i:ModelIndex t U) :Option mA →₀ ℕ :=
 (modelExponent i).mapDomain varIndex
private theorem physical_exponent {t:TopRow} {U:ℕ} (i:ModelIndex t U) :
  renamedExponent i none=i.2.2.1.val := by
 change (renamedExponent i) (varIndex 0)= _
 rw [renamedExponent,Finsupp.mapDomain_apply_of_injective varIndex_injective]
 rfl
private def read (t:TopRow) :
  bjM ((box t).b+(box t).j) →ₗ[ao] (ModelIndex t (t.shape.U+t.shape.B)→ao) :=
 LinearMap.pi fun i =>
  (quotientCoeff i.2.2.1).comp ((lcoeff (LocalCoeff _) (renamedExponent i).some).restrictScalars ao)
private theorem read_image (t:TopRow) (j:ModelIndex t t.shape.U) :
   read t (localColumn (box t) t.shape.U (asLocal j))=(modelMatrix t).col j:= by
 funext i
 rw [← reduce_image]
 change quotientCoeff i.2.2.1
     ((reduce _ (unpack (modelImage j))).coeff (renamedExponent i).some)= _
 rw [reduce_coeff,← physical_exponent i]
 change ((optionEquivLeft ao mA (rename varIndex (modelImage j))).coeff
     (renamedExponent i none)).coeff (renamedExponent i).some= _
 rw [optionEquivLeft_coeff_some_coeff_none,renamedExponent,
   coeff_rename_mapDomain varIndex varIndex_injective]
 rfl
set_option maxSynthPendingDepth 16 in
private theorem rank_le_local (t:TopRow) :
  (modelMatrix t).rank≤zsE ao (localImage (box t) t.shape.U) := by
 let V:=localImage (box t) t.shape.U
 let:zAa ao V:=z3g ao (zlS _)
 let:zAa ao (V.map (read t)) :=z2p V (read t)
 have hsub:Submodule.span ao (zxp (modelMatrix t).col)≤V.map (read t) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  refine ⟨localColumn (box t) t.shape.U (asLocal j),?_,read_image t j⟩
  exact zBO (zWL (asLocal j))
 rw [z0e]
 exact (zFM hsub).trans (zSE (read t) V)
open private index from ProximityPrize.SubmissionLower.ZHNB5Ae
private theorem flag_eq_window (t:TopRow) (q g w:ℕ) (hw:w≤q) :
    flagMatrix (box t) q ((g:ℤ) - t.shape.J) w=vo t q g (q-w) := by
  ext r c
  have hc:=c.1.isLt
  have hb:=c.2.isLt
  simp only [zh4,le_min_iff] at hc hb
  have htotal:c.1.val+c.2.val≤q:= by omega
  have hguards :
      (q - c.1.val - c.2.val≤w ∧
        0≤(g:ℤ) - t.shape.J+derivativeIndex c ∧
        (g:ℤ) - t.shape.J+q+derivativeIndex r<(((box t).b+(box t).j:ℕ) :ℤ) ∧
        r.1.val≤ c.1.val∧c.1.val - r.1.val≤ r.2.val) ↔
      (q - w≤ c.1.val+c.2.val∧r.1.val≤ c.1.val∧c.1.val≤ r.2.val+r.1.val ∧
        t.shape.J≤g+index c∧g+index c<t.shape.J+(t.shape.B+t.shape.J) ∧
        t.shape.J≤g+q+index r∧g+q+index r<t.shape.J+(t.shape.B+t.shape.J)) := by
    have hB: (box t).b=t.shape.B:=rfl
    have hJ: (box t).j=t.shape.J:=rfl
    simp only [derivativeIndex,index,hB,hJ]
    omega
  unfold flagMatrix vo
  split
  · rename_i h
    have hr :=h.2.2.2.1
    rw [ite_eq_left (hguards.mp h),Nat.cast_mul,
      show r.2.val-(c.1.val - r.1.val)=r.2.val+r.1.val - c.1.val by omega]
  · rename_i h
    rw [ite_eq_right (fun hp=>h (hguards.mpr hp))]
private theorem window_zero (t:TopRow) (q g a :ℕ) (ha :min q t.shape.J<a) :
  vo t q g a=0:= by
 ext r c
 have hc:=c.1.isLt
 have hb:=c.2.isLt
 have hJ: (box t).j=t.shape.J:=rfl
 simp only [zh4,le_min_iff,hJ] at hc hb
 have h : ¬ a≤ c.1.val+c.2.val := by omega
 simp [vo,h]
private theorem count_flags (t:TopRow) (q g:ℕ) :
   (∑ w∈range q,flagRank (box t) q ((g:ℤ) - t.shape.J) w) =
     ∑ a∈range (min q t.shape.J),(vo t q g (a+1)).rank := by
 let f (w:ℕ) :=flagRank (box t) q ((g:ℤ) - t.shape.J) w
 calc
   (∑ w∈range q,f w) = ∑ a∈range q,f (q-1-a) :=
     (Finset.sum_range_reflect f q).symm
   _ = ∑ a∈range q,(vo t q g (a+1)).rank := by
     apply zUo rfl
     intro a ha
     have h:=Finset.mem_range.mp ha
     dsimp only [f,flagRank]
     rw [flag_eq_window t q g _ (by omega),show q-(q-1-a)=a+1 by omega]
   _ = _:= by
     symm
     refine zVG (Finset.range_mono (min_le_left _ _)) ?_
     intro a _ ha
     rw [window_zero t q g (a+1) (by simp only [zIR] at ha; omega),Matrix.rank_zero]
private theorem dDE (t:TopRow) :windowBudget (box t) t.shape.U=windowDebit t:= by
  unfold windowBudget windowDebit
  change (∑ q∈range (t.shape.B+1),(∑ g∈range (t.shape.B+2*t.shape.J),
      ((t.shape.U+t.shape.B+1-2*q)*flagRank (box t) q ((g:ℤ) - t.shape.J) q +
        (∑ w∈range q,flagRank (box t) q ((g:ℤ) - t.shape.J) w))))= _
  apply zUo rfl
  intro q _
  apply zUo rfl
  intro g _
  rw [count_flags,flagRank,flag_eq_window t q g q le_rfl,Nat.sub_self,
    Nat.add_right_comm t.shape.U t.shape.B 1]
theorem proof :qje58fc.c2 := by
 intro b e t hU
 have h:=qA0rFHd.of_children
  qYur1ad.proof qnKm5Ba.proof qWpt85c.proof
 exact (rank_le_local t).trans ((h (box t) t.shape.U hU).trans_eq (dDE t))
end
end qVljrgb
end
section
set_option autoImplicit true
namespace qOPkAYa
open P5_7_2 (TopRow topDonors)
open q7IA62d (profile eMG)
open qje58fc (box windowDebit)
open qmb8rCe (sumN fullCost partCost)
def c1 :Prop :=Filed ⟨87,27,12⟩ 15643160
def c2 :Prop :=Filed ⟨164,50,19⟩ 0x13094c39
def c3:Prop :=Filed ⟨174,52,22⟩ 0x196ce109
private theorem budget (t:TopRow) (hb:0<t.shape.B) (hU:t.shape.B≤t.shape.U+1)
  (h:Filed (box t) t.poleRank) :windowDebit t≤eMG 1 t:= by
 let a :=box t
 let U:=t.shape.U
 let n:=sumN (base a) (a.b+1)
 have ha :=cost_le t (fun q d z _ hd _=>rank_le_cap a q d z hd)
 refine ha.trans ?_
 change sumN (fun q=>fullCost a U q+partCost a U q) (a.b+1)≤_
 rw [cost_linear a U hb hU]
 refine (Nat.add_le_add (Nat.mul_le_mul_left _ h.1) h.2).trans_eq ?_
 change (U+1-a.b)*n+(a.b*n+t.poleRank)=eMG 1 t
 have hU' : a.b≤U+1 :=hU
 rw [← zVg,← zNE,zxt hU',eMG,one_mul,b6N]
 rfl
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :qje58fc.c3:= by
 intro b e
 cases e <;> by_cases hb:b.val<7 <;>
   simp only [profile,topDonors,hb,ite_true,ite_false,Bool.false_eq_true]
 · exact budget _ (by decide) (by decide) h1
 · exact budget _ (by decide) (by decide) h1
 · exact budget _ (by decide) (by decide) h2
 · exact budget _ (by decide) (by decide) h3
end qOPkAYa
end
end
