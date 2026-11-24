import ProximityPrize.SubmissionLower.ZWJjZ2a
import ProximityPrize.SubmissionLower.Z4EMMWa
import ProximityPrize.SubmissionLower.ZLCmwJc
import ProximityPrize.SubmissionLower.ZMijUzd
import ProximityPrize.SubmissionLower.ZRfXqSb
import ProximityPrize.SubmissionLower.ZVMYHza
import ProximityPrize.SubmissionLower.ZvigIbb
import ProximityPrize.SubmissionLower.Zhgm4se
import ProximityPrize.SubmissionLower.Zj5kWte
import ProximityPrize.SubmissionLower.Z4IfEsd
import ProximityPrize.SubmissionLower.Z4ocXpc
import ProximityPrize.SubmissionLower.ZUItRVc
import ProximityPrize.SubmissionLower.ZcSHjJe
import ProximityPrize.SubmissionLower.Zr1PeAc
set_option Elab.async false
open _root_ renaming CommRing → za6, Fin.castSucc → z1o, Fin.castSucc_ne_last → zm4, Fin.snoc → zBM, Function.comp_def → zQM, Matrix.cons_val_one → z87, Matrix.cons_val_two → zrz, Matrix.cons_val_zero → zbs, Matrix.det_fin_three → zpn, MvPolynomial → z3y, MvPolynomial.X → z9v, MvPolynomial.eval → zY9, MvPolynomial.eval_C → z9X, MvPolynomial.map → zDK, Nat.add_le_add_left → z3b, Nat.add_le_add_right → zlr, Nat.add_mul → zNE, Nat.cast_add → z6H, Nat.cast_nonneg → zqJ, Nat.cast_one → z4o, Nat.cast_sub → zjK, Nat.le_of_lt_succ → zeh, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Polynomial.C → z1z, RingHom.id → zz4
set_option maxHeartbeats 1000000
section
section
namespace qRIxBbd
noncomputable section
open Polynomial
open cu (L)
open q8Z6NHc (Index boundary)
open qFwMjQd
open MvPolynomial (pderiv)
theorem proof :qFwMjQd.c2 := by
  classical
  intro d s a hd _ ha b c hc
  dsimp only
  let E :=Eline d s a
  let f :=fLine d s a
  let g:=gLine d s a
  let h:=hLine d s a hd (weight_base hd ha) b c
  let τ:=lineVar (σ:=Index d s a) none*(algebraMap L E c)^(d-2)
  let A:=Yn f d
  let B:=slope f d
  let G:=Yn g d
  let D:=slope g d
  let U:=Yn f (d-1)
  let V:=slope f (d-1)
  let P:=A*D-B*G
  let z (x :E) := -A.eval x/B.eval x
  let pt:E ↪ aax E :=⟨fun x => ![x,0,z x],fun _ _ he=>congrFun he 0⟩
  obtain ⟨hp,hcard,hgood⟩:=boundary_roots hd ha c hc
  refine ⟨P.roots.toFinset.map pt,?_,?_⟩
  · intro q hq
    obtain ⟨x,hx,rfl⟩:=Finset.mem_map.mp hq
    change (![x,0,z x] :aax E) 1=0 ∧
      simple (bY true f) (bY true g) (bY true h) ![x,0,z x]
    obtain ⟨hdP,hB,hV⟩:=hgood x hx
    change P.derivative.eval x≠0 at hdP
    change B.eval x≠0 at hB
    have hp0:P.eval x=0:=(mem_roots hp).mp (Multiset.mem_toFinset.mp hx)
    have hP:A.eval x*D.eval x - B.eval x*G.eval x=0:= by simpa [P] using hp0
    have hf :A.eval x+B.eval x*z x=0:= by
      have he :B.eval x*z x = -A.eval x := by
        dsimp only [z]
        rw [mul_comm,div_mul_cancel₀ _ hB]
      rw [he,add_neg_cancel]
    have hg:G.eval x+D.eval x*z x=0:= by
      have he :B.eval x*(G.eval x+D.eval x*z x)=0:= by
        linear_combination D.eval x*hf - hP
      exact (mul_eq_zero.mp he).resolve_left hB
    have hm :
        (A.derivative.eval x+B.derivative.eval x*z x)*D.eval x -
        B.eval x*(G.derivative.eval x+D.derivative.eval x*z x)=P.derivative.eval x := by
      simp only [P,derivative_sub,derivative_mul,eval_sub,eval_add,eval_mul]
      linear_combination B.derivative.eval x*hg - D.derivative.eval x*hf
    have hw:U.eval x+V.eval x*z x+τ≠0:= by
      intro he
      apply hV
      simp only [eval_sub,eval_mul,eval_add,eval_C]
      change B.eval x*(U.eval x+τ) - A.eval x*V.eval x=0
      linear_combination B.eval x*he-V.eval x*hf
    obtain ⟨h₀,h₂,h₁,h₃⟩:=h_boundary hd ha b c
    change Yn h (d-1)=C (d:E)*A at h₀
    change slope h (d-1)=C (d:E)*B at h₂
    change Yn h (d-1-1)=C ((d-1 :ℕ) :E)*U - C τ at h₁
    change slope h (d-1-1)=C ((d-1 :ℕ) :E)*V at h₃
    obtain ⟨ef,fx,fw,fz⟩:=chart_jets (by omega :d≠0) f x (z x)
    obtain ⟨eg,gx,_,gz⟩:=chart_jets (by omega :d≠0) g x (z x)
    obtain ⟨eh,hx',hw',hz'⟩:=chart_jets (by omega :d-1≠0) h x (z x)
    have eh0:zY9 ![x,0,z x] (bY true h)=0:= by
      rw [eh,h₀,h₂]
      simp only [eval_mul,eval_C]
      change (d:E)*A.eval x+(d:E)*B.eval x*z x=0
      linear_combination (d:E)*hf
    have hX:zY9 ![x,0,z x] (pderiv 0 (bY true h)) =
        (d:E)*zY9 ![x,0,z x] (pderiv 0 (bY true f)) := by
      rw [hx',fx,h₀,h₂]
      simp only [derivative_C_mul,eval_mul,eval_C]
      ring
    have hZ:zY9 ![x,0,z x] (pderiv 2 (bY true h)) =
        (d:E)*zY9 ![x,0,z x] (pderiv 2 (bY true f)) := by
      rw [hz',fz,h₂,eval_mul,eval_C]
    have hW: (d:E)*zY9 ![x,0,z x] (pderiv 1 (bY true f)) -
        zY9 ![x,0,z x] (pderiv 1 (bY true h))=U.eval x+V.eval x*z x+τ:= by
      rw [fw,hw',h₁,h₃]
      simp only [eval_mul,eval_sub,eval_C,zjK (show 1≤d by omega),z4o]
      ring
    refine ⟨rfl,ef.trans hf,eg.trans hg,eh0,?_⟩
    let J:Matrix (Fin 3) (Fin 3) E :=Matrix.of fun i j =>
      zY9 ![x,0,z x] (pderiv j (![bY true f,bY true g,bY true h] i))
    change J.det≠0
    rw [zpn J]
    simp only [J,Matrix.of_apply,zbs,z87,zrz,
      Matrix.head_cons,Matrix.tail_cons,hX,hZ]
    convert mul_ne_zero hdP hw using 1
    rw [← hm,← hW,← fx,← fz,← gx,← gz]
    ring
  · change P.roots.toFinset.card= _ at hcard
    rw [Finset.card_map,hcard]
    apply le_of_eq
    have ha' : d*s≤a+s+1 := by omega
    simp only [boundary,z6H,zjK ha,zjK ha',Nat.cast_mul,z4o]
    ring
end
end qRIxBbd
end
end
section
section
set_option backward.isDefEq.respectTransparency false
namespace q80yiVc
noncomputable section
open MvPolynomial Finset
open qZu9hjc (atPair physicalDeriv)
open q8Z6NHc (Slot form)
open qFwMjQd (succSlot)
open private at_form at_dx at_dy ajS constant jU from ProximityPrize.SubmissionLower.ZMijUzd
open scoped Classical
abbrev lK (R:Type) [CommSemiring R] :=z3y (Fin 2) R
def u7 {R:Type} [CommSemiring R] {d s a :ℕ} (u:Slot d s a→R) :lK R :=
 ∑ i,C (u i)*z9v 0^i.val.2.val*z9v 1^i.val.1.val
theorem plane_map {R S:Type} [CommSemiring R] [CommSemiring S] {d s a :ℕ}
  (f :R →+* S) (u:Slot d s a→R) :
  zDK f (u7 u)=u7 (f ∘ u) := by
 simp [u7,map_sum]
theorem plane_at {R:Type} [Field R] {d s a :ℕ}
  (u:Slot d s a→R) (x y :R) :
  (u7 u).eval ![x,y]=atPair (zz4 R) x y (form u) := by
 rw [at_form]
 simp [u7,map_sum]
theorem plane_dx {R:Type} [Field R] {d s a :ℕ}
  (u:Slot d s a→R) (x y :R) :
  (pderiv 0 (u7 u)).eval ![x,y]=atPair (zz4 R) x y (physicalDeriv (form u)) := by
 rw [at_dx]
 simp only [u7,ajS,map_sum,pderiv_mul,pderiv_C,pderiv_pow,pderiv_X_self,
  pderiv_X_of_ne (show (1 :Fin 2)≠0 by decide),mul_zero,zero_mul,zero_add,add_zero,
  mul_one,map_mul,map_pow,eval_C,eval_X,map_natCast,zbs,z87]
 exact sum_congr rfl fun _ _=> by ac_rfl
theorem plane_dy {R:Type} [Field R] {d s a :ℕ}
  (u:Slot d s a→R) (x y :R) :
  (pderiv 1 (u7 u)).eval ![x,y]=atPair (zz4 R) x y (form u).derivative := by
 rw [at_dy]
 simp only [u7,ajS,map_sum,pderiv_mul,pderiv_C,pderiv_pow,pderiv_X_self,
  pderiv_X_of_ne (show (0:Fin 2)≠1 by decide),mul_zero,zero_mul,zero_add,add_zero,
  mul_one,map_mul,map_pow,eval_C,eval_X,map_natCast,zbs,z87]
 exact sum_congr rfl fun _ _=> by ac_rfl
theorem plane_y {R:Type} [CommSemiring R] {d s a :ℕ}
   (hd:2≤d) (ha :s≤a) (u:Slot d s a→R) :
   pderiv 1 (u7 u)=u7 (fun i=>(i.val.1.val+1 :ℕ)*u (succSlot hd ha i)) := by
 let term (j:Slot d s a) :lK R :=
   C (u j)*z9v 0^j.val.2.val*((j.val.1.val :lK R)*z9v 1^(j.val.1.val - 1))
 have hd₀:pderiv 1 (u7 u) = ∑ j,term j:= by
   simp only [u7,term,map_sum,pderiv_mul,pderiv_C,pderiv_pow,pderiv_X_self,
     pderiv_X_of_ne (show (0:Fin 2)≠1 by decide),mul_zero,zero_mul,zero_add,
     add_zero,mul_one]
 have hpos : ∀ j∈univ,term j≠0→j.val.1.val≠0:= by
   intro j _ h hj
   exact h (by simp [term,hj])
 rw [hd₀,← sum_filter_of_ne hpos,u7]
 symm
 refine sum_bij (fun i _=>succSlot hd ha i) ?_ ?_ ?_ ?_
 · intro i _
   exact mem_filter.mpr ⟨mem_univ _,Nat.succ_ne_zero _⟩
 · intro i _ j _ h
   apply Subtype.ext
   apply Prod.ext <;> apply Fin.ext
   · exact Nat.add_right_cancel (congrArg (fun k :Slot d s a=>k.val.1.val) h)
   · exact congrArg (fun k :Slot d s a=>k.val.2.val) h
 · intro j hj
   have hj₀:=(mem_filter.mp hj).2
   have h₁:=j.val.1.isLt
   have h₂:=j.property
   have hh:j.val.1.val - 1+1=j.val.1.val := by omega
   have hw:j.val.2.val+(j.val.1.val - 1)*s≤a-s := by
     change j.val.2.val+j.val.1.val*s≤a at h₂
     have ht:=congrArg (fun n:ℕ=>n*s) hh
     rw [zNE,one_mul] at ht
     omega
   let i:Slot (d-1) s (a-s) :=
     ⟨(⟨j.val.1.val-1,by omega⟩,⟨j.val.2.val,by omega⟩),hw⟩
   exact ⟨i,mem_univ _,Subtype.ext (Prod.ext (Fin.ext hh) (Fin.ext rfl))⟩
 · intro i _
   simp only [term,succSlot,Nat.add_sub_cancel,map_mul,map_natCast,z6H,
     z4o,map_add,map_one]
   ac_rfl
theorem plane_axis {R:Type} [CommSemiring R] {d s a :ℕ}
   (hw:d*s≤a) (P:Polynomial R) (hn:P.natDegree≤d) :
   u7 (fun i:Slot d s a=>if i.val.2.val=0 then P.coeff i.val.1.val else 0) =
     P.eval₂ C (z9v 1) := by
 let lift (j:Fin (d+1)) :Slot d s a :=
   ⟨(j,0),by simpa using (ztf s (zeh j.isLt)).trans hw⟩
 rw [Polynomial.eval₂_eq_sum_range' C (n:=d+1) (Nat.lt_succ_of_le hn),
   ← Fin.sum_univ_eq_sum_range,u7]
 simp only [apply_ite C,map_zero,ite_mul,zero_mul]
 rw [← sum_filter]
 symm
 refine sum_bij (fun j _=>lift j) ?_ ?_ ?_ ?_
 · intro j _
   exact mem_filter.mpr ⟨mem_univ _,rfl⟩
 · intro j _ k _ h
   exact congrArg (fun i:Slot d s a=>i.val.1) h
 · intro i hi
   exact ⟨i.val.1,mem_univ _,Subtype.ext (Prod.ext rfl (Fin.ext (mem_filter.mp hi).2.symm))⟩
 · intro j _
   simp [lift]
theorem plane_perturb {R:Type} [za6 R] {d s a :ℕ}
   (hd:2≤d) (ha :d*s≤a) (y :R) :
   u7 (fun i=>(if i=jU hd ha then 1 else 0) -
     (if i=constant d s a then y else 0))=z9v 1 - C y := by
 have only (j:Slot d s a) (v :R) :
     u7 (fun i=>if i=j then v else 0)=C v*z9v 0^j.val.2.val*z9v 1^j.val.1.val := by
   unfold u7
   rw [sum_eq_single j]
   · simp
   · intro i _ h
     simp [h]
   · simp
 simp only [u7,map_sub,sub_mul,sum_sub_distrib]
 change u7 (fun i=>if i=jU hd ha then 1 else 0) -
   u7 (fun i=>if i=constant d s a then y else 0)= _
 rw [only,only]
 simp [jU,constant]
end
end q80yiVc
end
section
set_option backward.isDefEq.respectTransparency false
namespace q80yiVc
noncomputable section
open MvPolynomial Finset
open cu (L)

open qFwMjQd (Chart LineData Eline bY fLine hLine weight_base)
open q33Mraa (target)
section
variable {R S:Type} [za6 R] [za6 S]
def GV (f g:lK R) (z :R) :Chart R :=
 rename z1o f+rename z1o g*(z9v 2 - C z)
theorem centered_at (f g:lK R) (q:Fin 2→R) (z :R) :
  (GV f g z).eval (zBM q z)=f.eval q:= by
 have hz : (zBM q z :Fin 3→R) 2=z :=Fin.snoc_last (α:= fun _:Fin 3=>R) z q
 simp [GV,eval_rename,zQM,hz]
theorem centered_partial (f g:lK R) (q:Fin 2→R) (z :R) (j:Fin 2) :
  (pderiv j.castSucc (GV f g z)).eval (zBM q z)=(pderiv j f).eval q:= by
 have hj: (2 :Fin 3)≠j.castSucc:=(zm4 j).symm
 have hz : (zBM q z :Fin 3→R) 2=z :=Fin.snoc_last (α:= fun _:Fin 3=>R) z q
 simp [GV,pderiv_rename (Fin.castSucc_injective 2) j,pderiv_X_of_ne hj,
  eval_rename,zQM,hz]
theorem centered_seed (f g:lK R) (q:Fin 2→R) (z :R) :
  (pderiv 2 (GV f g z)).eval (zBM q z)=g.eval q:= by
 have h (r :lK R) :pderiv 2 (rename z1o r)=0:= by
  apply pderiv_eq_zero_of_notMem_vars
  intro hm
  obtain ⟨j,_,hj⟩:=mem_vars_rename z1o r hm
  exact zm4 j hj
 simp [GV,h,eval_rename,zQM]
theorem plane_eval_map (φ:R →+* S) (q:Fin 2→R) (r :lK R) :
  (zDK φ r).eval (φ ∘ q)=φ (r.eval q) := by
 rw [eval_map,eval₂_comp]
def jet (q:Fin 2→R) (f g:Fin 3→lK R) :Matrix (Fin 3) (Fin 3) R :=
 fun i => ![(pderiv 0 (f i)).eval q,(pderiv 1 (f i)).eval q,(g i).eval q]
theorem jet_map (φ:R →+* S) (q:Fin 2→R) (f g:Fin 3→lK R) :
   φ.mapMatrix (jet q f g) =
     jet (φ ∘ q) (zDK φ ∘ f) (zDK φ ∘ g) := by
 ext i j
 fin_cases j <;> simp [jet,pderiv_map,eval₂_comp,RingHom.mapMatrix_apply]
theorem centered_jet (q:Fin 2→R) (z :R) (f g:Fin 3→lK R) :
   (fun i j:Fin 3=>(pderiv j (GV (f i) (g i) z)).eval (zBM q z)) =
     jet q f g:= by
 ext i j
 fin_cases j
 · exact centered_partial (f i) (g i) q z 0
 · exact centered_partial (f i) (g i) q z 1
 · exact centered_seed (f i) (g i) q z
def gaugePlane (b c:R) (n:ℕ) :lK R :=
 (C b+C c*z9v 1)^n
theorem gaugePlane_map (φ:R →+* S) (b c:R) (n:ℕ) :
  zDK φ (gaugePlane b c n)=gaugePlane (φ b) (φ c) n:= by
 simp [gaugePlane]
end
theorem chart_centered {R:Type} [Field R] {d s a :ℕ} (f :LineData R d s a) (z :R) :
  bY false f=GV (u7 fun i=>(f i).1+(f i).2*z) (u7 fun i=>(f i).2) z := by
 classical
 simp only [bY,GV,u7,map_sum,map_mul,map_pow,rename_C,rename_X,
  Bool.false_eq_true,ite_false,
  show z1o (0:Fin 2)=(0:Fin 3) from rfl,
  show z1o (1 :Fin 2)=(1 :Fin 3) from rfl]
 rw [sum_mul,← sum_add_distrib]
 refine sum_congr rfl fun i _ => ?_
 simp only [map_add,map_mul]
 ring
theorem hChart_centered {d s a :ℕ} (hd:2≤d) (ha :d*s≤a) (b c:L) (z :Eline d s a) :
    bY false (hLine d s a hd (weight_base hd ha) b c) =
      GV (pderiv 1 (u7 fun i=>(fLine d s a i).1+(fLine d s a i).2*z) -
        C (target d s a)*gaugePlane (algebraMap L _ b) (algebraMap L _ c) (d-2))
        (pderiv 1 (u7 fun i=>(fLine d s a i).2)) z := by
  classical
  let R:=Eline d s a
  let P:Polynomial R:=(z1z (algebraMap L R b) +
    z1z (algebraMap L R c)*Polynomial.X)^(d-2)
  have hs : (d-1)*s≤a-s := by
    have hm:=congrArg (fun n:ℕ=>n*s) (Nat.sub_add_cancel (show 1≤d by omega))
    rw [zNE,one_mul] at hm
    omega
  have hP:P.natDegree≤d-1 := by
    apply (Polynomial.natDegree_pow_le).trans
    have h: (z1z (algebraMap L R b) +
        z1z (algebraMap L R c)*Polynomial.X).natDegree≤1 :=
      Polynomial.natDegree_add_le_of_degree_le (by simp)
        (by simpa using Polynomial.natDegree_C_mul_X_pow_le (algebraMap L R c) 1)
    exact (zBI _ h).trans (by omega)
  have hg:u7 (fun i:q8Z6NHc.Slot (d-1) s (a-s) =>
      if i.val.2.val=0 then P.coeff i.val.1.val else 0) =
      gaugePlane (algebraMap L R b) (algebraMap L R c) (d-2) := by
    rw [plane_axis hs P hP]
    change (Polynomial.eval₂RingHom C (z9v 1)) P= _
    simp only [P,gaugePlane,map_pow,map_add,map_mul,Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C,Polynomial.eval₂_X]
  rw [chart_centered,plane_y hd (weight_base hd ha),plane_y hd (weight_base hd ha),← hg]
  apply congrArg₂ (fun f g=>GV f g z) ?_ rfl
  simp only [u7,mul_sum,← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  simp only [hLine,target,P]
  split_ifs <;> simp only [map_add,map_sub,map_mul,map_zero,sub_zero] <;> ring
end
end q80yiVc
end
section
set_option backward.isDefEq.respectTransparency false
namespace q80yiVc
noncomputable section
open MvPolynomial
open cu (L)
open qZu9hjc (jacobian)
open q8Z6NHc (Index Generic genericF genericG)
open qFwMjQd (Eline Chart bY fLine gLine hLine weight_base simple)
open q33Mraa (Lw target pointValue linePoint)
open private constant jU from ProximityPrize.SubmissionLower.ZMijUzd
open scoped Classical
local notation "lgauge" => qZu9hjc.gauge
local notation "lslope" => q33Mraa.slope
private def directions {R:Type} [za6 R] {d s a :ℕ} (v :Index d s a→R) :
   Fin 3→lK R :=
 ![u7 (fun i=>v (.inl i)),u7 (fun i=>v (.inr i)),
   pderiv 1 (u7 (fun i=>v (.inl i)))]
private theorem directions_map {R S:Type} [za6 R] [za6 S] {d s a :ℕ}
  (φ:R →+* S) (v :Index d s a→R) :
  zDK φ ∘ directions v=directions (φ ∘ v) := by
 funext j
 fin_cases j <;> simp [directions,← pderiv_map,plane_map,zQM,
  zrz]
private theorem map_slopeJet {R S σ:Type} [za6 R] [za6 S] {d s a :ℕ}
   (φ:z3y σ R →+* S) (k :R →+* S) (hk :φ.comp C=k)
   (q:Fin 2→R) (f :Fin 3→lK R) (v :Index d s a→z3y σ R) :
   φ.mapMatrix (jet (C ∘ q) (zDK C ∘ f) (directions v)) =
     jet (k ∘ q) (zDK k ∘ f) (directions (φ ∘ v)) := by
 have hq:φ ∘ (C ∘ q)=k ∘ q:=funext fun i=>RingHom.congr_fun hk (q i)
 have hf :zDK φ ∘ (zDK C ∘ f) =
     zDK k ∘ f := by
   funext i
   change zDK φ (zDK C (f i))=zDK k (f i)
   rw [map_map,hk]
 rw [jet_map,directions_map,hq,hf]
private theorem independent_jet {F E :Type} [Field F] [Field E] {d s a :ℕ}
   (k :F →+* E) (v :Index d s a→E) (h:Function.Injective (eval₂Hom k v))
   (q:Fin 2→F) (base :Fin 3→lK F) (β:Index d s a→F)
   (hβ: (jet q base (directions β)).det≠0) :
   (jet (k ∘ q) (zDK k ∘ base) (directions v)).det≠0:= by
 let W:=z3y (Index d s a) F
 let M:=jet ((C:F →+* W) ∘ q) (zDK C ∘ base)
   (directions (z9v:Index d s a→W))
 let ψ:W →+* F:=zY9 β
 have hmψ:ψ.mapMatrix M=jet q base (directions β) := by
   have hψ:ψ.comp (C:F →+* W)=zz4 F :=
     RingHom.ext fun r=>z9X r
   have hv :ψ ∘ (z9v:Index d s a→W)=β :=
     funext fun j=>MvPolynomial.eval_X j
   have he :=map_slopeJet ψ (zz4 F) hψ q base (z9v:Index d s a→W)
   have hid :zDK (zz4 F) ∘ base=base :=
     funext fun j=>MvPolynomial.map_id (base j)
   rw [hv,hid] at he
   exact he
 have hm:M.det≠0:= fun hn=>hβ (by rw [← hmψ,← ψ.map_det,hn,map_zero])
 let φ:W →+* E :=eval₂Hom k v
 have hφ:φ.comp (C:F →+* W)=k :=RingHom.ext fun r=>eval₂Hom_C _ _ r
 have hv :φ ∘ (z9v:Index d s a→W)=v :=funext fun j=>eval₂Hom_X' _ _ j
 have he :=map_slopeJet φ k hφ q base (z9v:Index d s a→W)
 rw [hv] at he
 rw [← he,← φ.map_det]
 exact (map_ne_zero_iff φ h).2 hm
theorem proof :q33Mraa.c3:= by
  intro d s a hd _ ha b c _ V z J i ht
  let F:=Generic d s a
  let E :=Eline d s a
  let I:=Index d s a
  let k :=J.emb.toRingHom
  have hb:k (algebraMap L F b)=algebraMap L E b:=J.emb.commutes b
  have hc:k (algebraMap L F c)=algebraMap L E c:=J.emb.commutes c
  let x :=(V.pt i).1
  let y :=(V.pt i).2
  let q:Fin 2→F := ![x,y]
  let t:=pointValue V i
  let f :lK F:=u7 (fun j=>Lw (.inl j:I))
  let g:lK F:=u7 (fun j=>Lw (.inr j:I))
  let h:lK F:=pderiv 1 f - C t*gaugePlane (algebraMap L F b) (algebraMap L F c) (d-2)
  let base :Fin 3→lK F := ![f,g,h]
  let P:Fin 3→Chart E := ![bY false (fLine d s a),bY false (gLine d s a),
    bY false (hLine d s a hd (weight_base hd ha) b c)]
  have hF:u7 (fun j=>(fLine d s a j).1+(fLine d s a j).2*z)=zDK k f := by
    unfold f
    rw [plane_map]
    exact congrArg u7 (funext fun j=>(J.coeff_eq (.inl j)).symm)
  have hG:u7 (fun j=>(gLine d s a j).1+(gLine d s a j).2*z)=zDK k g:= by
    unfold g
    rw [plane_map]
    exact congrArg u7 (funext fun j=>(J.coeff_eq (.inr j)).symm)
  have hp (j:Fin 3) :
      P j=GV (zDK k (base j)) (directions (lslope :I→E) j) z := by
    fin_cases j
    · change bY false (fLine d s a)= _
      rw [chart_centered,hF]
      rfl
    · change bY false (gLine d s a)= _
      rw [chart_centered,hG]
      rfl
    · change bY false (hLine d s a hd (weight_base hd ha) b c) =
        GV (zDK k h) (pderiv 1 (u7 fun j=>lslope (.inl j:I))) z
      rw [hChart_centered hd ha,hF]
      congr 1
      simp only [h,map_sub,map_mul,pderiv_map,MvPolynomial.map_C,gaugePlane_map]
      rw [show k t=target d s a from ht,hb,hc]
  have hz (j:Fin 3) : (base j).eval q=0:= by
    fin_cases j
    · exact (plane_at _ x y).trans (V.f_zero i)
    · exact (plane_at _ x y).trans (V.g_zero i)
    · change h.eval q=0
      have hg: (gaugePlane (algebraMap L F b) (algebraMap L F c) (d-2)).eval q =
          lgauge b c y ^(d-2) := by
        simp [gaugePlane,q,qZu9hjc.gauge] <;> rfl
      dsimp only [h]
      rw [map_sub,map_mul,eval_C,hg]
      change (pderiv 1 f).eval ![x,y] - t*lgauge b c y ^(d-2)=0
      unfold f
      rw [plane_dy,sub_eq_zero]
      exact (div_mul_cancel₀ _ (pow_ne_zero _ (V.gauge_ne i))).symm
  have hq:linePoint V J i=zBM (k ∘ q) z := by
    funext j
    fin_cases j <;> rfl
  have hP (j:Fin 3) : (P j).eval (linePoint V J i)=0:= by
    rw [hp,hq,centered_at,plane_eval_map,hz,map_zero]
  refine ⟨⟨hP 0,hP 1,hP 2,?_⟩,?_⟩
  · let β:I→F:=Sum.elim
      (fun j=>(if j=jU hd ha then 1 else 0)-(if j=constant d s a then y else 0))
      (fun _=>0)
    have hβ:u7 (fun j=>β (.inl j))=z9v 1 - C y :=plane_perturb hd ha y
    have hcol0: ((directions β) 0).eval q=0:= by
      change (u7 fun j=>β (.inl j)).eval q=0
      have hcy : (C y :lK F).eval q=y :=z9X y
      rw [hβ,map_sub,eval_X,hcy]
      exact sub_self y
    have hcol1 : ((directions β) 1).eval q=0:= by
      change (u7 fun j=>β (.inr j)).eval q=0
      simp [u7,β]
    have hcol2 : ((directions β) 2).eval q=1 := by
      change (pderiv 1 (u7 fun j=>β (.inl j))).eval q=1
      have hcy :pderiv 1 (C y :lK F)=0:=pderiv_C
      rw [hβ,map_sub,pderiv_X_self,hcy,sub_zero,map_one]
    have hβdet: (jet q base (directions β)).det≠0:= by
      rw [zpn]
      simpa [jet,hcol0,hcol1,hcol2,base,f,g,q,plane_dx,plane_dy,jacobian,
        genericF,genericG,Lw,zrz] using V.simple i
    change Matrix.det (fun u j:Fin 3=>(pderiv j (P u)).eval (linePoint V J i))≠0
    have hjac :
        (fun u j:Fin 3=>(pderiv j (P u)).eval (linePoint V J i)) =
        jet (k ∘ q) (zDK k ∘ base) (directions lslope) := by
      rw [← centered_jet (k ∘ q) z (zDK k ∘ base) (directions lslope)]
      funext u j
      rw [hp u,hq,Function.comp_apply]
    rw [hjac]
    exact independent_jet k lslope J.independent q base β hβdet
  · have hg:k (lgauge b c y)=lgauge b c (linePoint V J i 1) := by
      change k (algebraMap L F b+algebraMap L F c*y) =
        algebraMap L E b+algebraMap L E c*k y
      rw [map_add,map_mul,hb,hc]
    exact hg ▸ (map_ne_zero_iff k J.emb.injective).2 (V.gauge_ne i)
end
end q80yiVc
end
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace qDxaYpa
noncomputable section
open Polynomial Finset
open scoped Classical
open P6 (K I p blockLength jG)
open P5_7_2 (A fO jX)
open q7F2qKe (wX weakAgreement)
open q6nKpZc (Input)
open q4V2ihd (DescendedMarks)
open cu (L j9)
open DP (Z7 Tj)
open gT (aQ abX)
open Cu (sQ)
open YY (U7 bnQ)
open quN7Z4a (Sheet)
open P5_7_7 (base mL sites mem_sites)
open q82zwcd (WordChart DualSheet highFee word_chart degree_lt poles gap width polar targetHit)
open qb0hmCe (SiteTarget)
open qK3TPae (regular high_count polar_count)
open private bLI from ProximityPrize.SubmissionLower.ZdSQxye
open private b1I from ProximityPrize.SubmissionLower.G
open private no_common_root from ProximityPrize.SubmissionLower.ZODPK9c
open private unpack slope lowRate incidence on_word on_poles from ProximityPrize.SubmissionLower.Z55PrLe
open private dual_sheet from ProximityPrize.SubmissionLower.ZvigIbb
def c1 :Prop :=q1XeJwa.c1
def c2 :Prop :=qZfVj1b.c2
def c3:Prop :=qZfVj1b.c3
def c4 :Prop :=qZfVj1b.c4
def c5:Prop :=qVuPRtb.c1
def c6:Prop :=q82zwcd.c4
def c7:Prop :=q82zwcd.c5
private theorem price_pos (b:fO) :0<(jX b).lo:= by
  fin_cases b <;> decide
private theorem aNb {b u del M Γ F} (x : @Input b u del M Γ F) {γ:K} (hγ:γ∈Γ) :
    (F.scalar γ).natDegree≤wX b:= by
  have hw:=x.vo.2
  have hr :=(bLI b).1
  have hh:M.iF.toNat≤(P5_7_2.row b).declaredHi:= by omega
  exact (P6_7.aic F hγ).trans (z3b hh _)
private theorem agreement_bound {u del} {M:jG u del} {Γ} {F:P1.bje A M Γ}
    {γ:K} (hγ:γ∈Γ) :weakAgreement≤(sites M.word F.scalar γ).card:= by
  let m:=F.mark γ hγ
  exact m.bad.dw.trans (card_le_card fun i hi=>mem_sites.mpr (m.scalar_hits i hi))
private theorem sheet {u del} {M:jG u del} {Γ} {F:P1.bje A M Γ}
    {T J Q g H} (h:DescendedMarks F T J Q g H) (hg:0<g) :
    ∃ (C:sQ) (hC:Irreducible C),C.totalDegree= Q.totalDegree ∧
      Nonempty (@Sheet C ⟨hC⟩ J g H T M.label F.scalar) := by
  have hlen:Module.finrank aQ (abX J)= Q.totalDegree*g:= by
    obtain ⟨_,C,hc,hp,_,hs,_,_⟩:=h.curve
    change J.comap gT.pZ=Ideal.span {zDK U7 C} at hp
    let f :=zDK U7 C
    have hf :f≠0:=(map_ne_zero_iff _ (MvPolynomial.map_injective _
      U7.injective)).mpr hc.ne_zero
    have hd:=b1I f hf Q (hp.symm.trans h.projection)
    rw [← hd,bnQ]
    exact hs
  exact quN7Z4a.sheet hg h.curve hlen h.marks
private theorem starts {b u del M Γ F} (x : @Input b u del M Γ F) {U:Finset K} (hU:U⊆Γ)
    (J:WordChart (wX b) M.word U F.scalar) :
    ∃ R:Fin 2→SiteTarget,(∀ i,(R i).coord=i∧(R i).det≠0) ∧
      ∀ γ∈U,∀ i,targetHit J M.label (R i) γ:= by
  have hh:0<M.iF.toNat := by
    have h:=x.vo.1
    have hp:=price_pos b
    omega
  have he (i:Fin 2) : ∃ y,(x.D.block i).eval y=0:= by
    apply IsAlgClosed.exists_root
    rw [degree_eq_natDegree (x.D.monic i).ne_zero,x.D.degree]
    exact_mod_cast hh.ne'
  choose y hy using he
  have hnode (i:Fin 2) (j:I) :y i≠base j:= by
    intro h
    have hz :=hy i
    rw [h] at hz
    exact x.units i j hz
  have hloc (i:Fin 2) (B:Finset I) : (mL B).eval (y i)≠0:= by
    rw [mL,eval_prod]
    exact prod_ne_zero_iff.mpr fun j _=> by
      simpa only [eval_sub,eval_X,eval_C] using sub_ne_zero.mpr (hnode i j)
  let c (i:Fin 2) :=(x.D.constant i).eval (y i)
  let d (i:Fin 2) :=(x.D.slope i).eval (y i)
  let f (i:Fin 2) :=(x.D.offset i).eval (y i)
  let a₀ (i:Fin 2) :=J.a₀.eval (y i)
  let a₁ (i:Fin 2) :=J.a₁.eval (y i)
  let b₀ (i:Fin 2) :=J.b₀.eval (y i)
  let b₁ (i:Fin 2) :=J.b₁.eval (y i)
  have hc (i:Fin 2) :f i*c i≠0:= by
    simpa only [c,f,eval_mul] using no_common_root (x.D.determinant i) (hy i)
  have hdet (i:Fin 2) :a₁ i*b₀ i-a₀ i*b₁ i≠0:= by
    obtain ⟨a,ha,hJ⟩:=J.determinant
    have hj:=congrArg (fun p:L[X]=>p.eval (y i)) hJ
    have hn:a₀ i*b₁ i-a₁ i*b₀ i≠0:= by
      simp only [eval_sub,eval_mul,eval_C] at hj
      change a₀ i*b₁ i-a₁ i*b₀ i= _ at hj
      rw [hj]
      exact mul_ne_zero ha (hloc i univ)
    intro h
    exact hn (sub_eq_zero.mpr (sub_eq_zero.mp h).symm)
  let R (i:Fin 2) :SiteTarget :=⟨y i,i,b₁ i*c i,b₁ i*d i-a₁ i*f i,
    b₀ i*c i,b₀ i*d i-a₀ i*f i⟩
  have hR (i:Fin 2) : (R i).det≠0:= by
    convert mul_ne_zero (hdet i) (hc i) using 1
    unfold R SiteTarget.det
    ring
  refine ⟨R,fun i=>⟨rfl,hR i⟩,fun γ hγ i=>⟨?_,?_⟩⟩
  · by_contra! h
    apply hR i
    change (R i).a*(R i).d-(R i).b*(R i).c=0
    linear_combination (R i).d*h.1-(R i).b*h.2
  · have hr :=eval_eq_zero_of_dvd_of_eval_eq_zero (x.residues γ (hU hγ) i).2 (hy i)
    simp only [eval_add,eval_mul,eval_C,Tj] at hr
    let z :=Z7 (M.label γ) i
    change (c i+z*d i)*(j9 (F.scalar γ)).eval (y i)+z*f i=0 at hr
    have hP:=congrArg (fun p:L[X]=>p.eval (y i)) (J.numerator_id γ hγ)
    have hQ:=congrArg (fun p:L[X]=>p.eval (y i)) (J.denominator_id γ hγ)
    simp only [eval_add,eval_mul] at hP hQ
    apply mul_left_cancel₀ (hloc i (sites M.word F.scalar γ))
    rw [← mul_assoc,← mul_assoc,hP,hQ]
    change (a₁ i*_+b₁ i)*(b₀ i*c i+(b₀ i*d i-a₀ i*f i)*z) =
      (a₀ i*_+b₀ i)*(b₁ i*c i+(b₁ i*d i-a₁ i*f i)*z)
    linear_combination (a₁ i*b₀ i-a₀ i*b₁ i)*hr
private theorem low_count (h4 :c6) (h5:c7)
    {b u del M Γ S} (x : @Input b u del M Γ S) {U:Finset K} (hU:U⊆Γ)
    {J:WordChart (wX b) M.word U S.scalar} {q:sQ} (hq:Irreducible q)
    (F:DualSheet J q M.label) (hg:3≤F.d) (hg54 :F.d≤54) (hp:F.d<p) {W:ℕ}
    (hw:F.d*width (wX b)≤W) (hgW:polar (wX b) F.d W<p) (hW:F.Jm W)
    (hs : ∀ γ∈U,q.eval (DP.Z7 (M.label γ))=0) {v :ℚ}
    (hr :lowRate (wX b) F.d W≤v) :
    (U.card:ℚ)≤v*F.h+4*(F.d:ℚ)^2*q.totalDegree+(q.totalDegree :ℚ)^2/3:= by
  let D:=wX b
  let d:=q.totalDegree
  let e :=F.d
  let P:=poles D e W
  let G:=gap D
  let R:=regular q M.label U
  have hR:R⊆U:=filter_subset _ _
  obtain ⟨V,hv⟩:=qZhm2wb.proof F hg hp
  obtain ⟨A,hA,lg⟩:=starts x hU J
  have hD:=degree_lt b
  have hG:0<G:=Nat.sub_pos_of_lt hD
  have hGQ: (0:ℚ)<G:=Nat.cast_pos.mpr hG
  have hc:=incidence V hD.le (fun _ hγ=>agreement_bound (F:=S) (hU hγ))
    _ _ _ (on_word h4 V hp) (on_poles h4 V hp A hA lg) (h5 V W hg hp hw hgW hW)
  have hmargin:2*e-2≤blockLength:= by
    exact ((Nat.sub_le _ _).trans (zBI _ hg54)).trans (by decide)
  have hmain:G*R.card≤((7+6*e)*G+(2*e+1)*blockLength+P)*F.h+G*(4*e*e*d) := by
    rw [← card_sdiff_add_card_eq_card V.Bp,Nat.mul_add]
    calc
      _≤G*((3+2*e)*F.h)+(blockLength*(2*e*F.h)+(P+(2*e-2))*F.h+G*(4*e*(F.h+e*d))) :=
        Nat.add_le_add (zBI _ hv) hc
      _=((3+6*e)*G+(2*e*blockLength+(2*e-2))+P)*F.h+G*(4*e*e*d) := by ring
      _≤_:= by
        apply zlr
        apply ztf
        refine zlr (Nat.add_le_add ?_ ?_) _
        · exact ztf _ (zlr (by decide :3≤7) _)
        · rw [zNE,one_mul]
          exact z3b hmargin _
  have hn: (G:ℚ)*R.card ≤
      ((((7+6*e)*G+(2*e+1)*blockLength+P:ℕ) :ℚ))*F.h+G*((4*e*e*d:ℕ) :ℚ) := by
    exact_mod_cast hmain
  have hh: (R.card:ℚ)≤v*F.h+4*(e :ℚ)^2*d:= by
    apply le_of_mul_le_mul_left _ hGQ
    calc
      _≤_:=hn
      _=(G:ℚ)*(lowRate D e W*F.h+4*(e :ℚ)^2*d) := by
        unfold lowRate
        change _=(G:ℚ)*((7+6*(e :ℚ)+(((2*e+1)*blockLength+P:ℕ) :ℚ)/G)*F.h+4*(e :ℚ)^2*d)
        push_cast
        field_simp [hGQ.ne']
        ring
      _≤_:=mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_right hr (zqJ _)) le_rfl) hGQ.le
  have hb:=polar_count qGzrWfb.proof hq (fun _ _ _ _ h=>sub_left_inj.mp h) hs
  have hbQ:3*((U \ R).card:ℚ)≤(d:ℚ)*(d-1 :ℕ) := by exact_mod_cast hb
  have hdQ: ((d-1 :ℕ) :ℚ)≤d:=Nat.cast_le.mpr (Nat.sub_le _ _)
  have hb' := hbQ.trans (mul_le_mul_of_nonneg_left hdQ (zqJ d))
  rw [← card_sdiff_add_card_eq_card hR,z6H]
  linarith only [hh,hb']
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4)
    (h5:c5) (h6:c6) (h7:c7) :q4V2ihd.c3:= by
  intro b u del M Γ F _ x T J Q g H hm hg hg54 v hv
  obtain ⟨k,c,j,W,B,hOK,hpol,hlow,hhigh⟩:=unpack hv
  have hg0:0<g:= by omega
  have hv0:0≤v :=(zqJ _).trans hhigh
  have hs : (0:ℚ)≤(Q.totalDegree :ℚ)^2/3+(4*(g:ℚ)^2+9*g)*Q.totalDegree := by positivity
  rw [slope hg0]
  rcases word_chart (F.distinct.mono hm.subset)
    (fun _ hγ=>agreement_bound (F:=F) (hm.subset hγ))
    (fun _ hγ=>aNb x (hm.subset hγ)) with hsmall | ⟨U,hU,hcard,⟨C⟩⟩
  · have hQ: (T.card:ℚ)≤1 := by exact_mod_cast hsmall
    have hgQ: (3:ℚ)≤g:= by exact_mod_cast hg
    have hh:=mul_nonneg hv0 (Nat.cast_nonneg (α:=ℚ) H)
    linarith only [hQ,hgQ,hh,hs]
  have hmU:DescendedMarks F U J Q g H :=⟨hU.trans hm.subset,hm.curve,hm.irreducible,
    hm.projection,hm.plane_pos,hm.seed_lt,fun γ hγ=>hm.marks γ (hU hγ)⟩
  obtain ⟨q,hq,hd,⟨S⟩⟩:=sheet hmU hg0
  let:Fact (Irreducible q) :=⟨hq⟩
  have hchar :q.totalDegree*g<p:=hd ▸ hm.seed_lt
  have hgp:g<p:=(Nat.le_mul_of_pos_left g hm.plane_pos).trans_lt hm.seed_lt
  obtain ⟨A,he,hh⟩:=dual_sheet h2 h3 h4 h1 C S
    (fun _ _ _ _ h=>sub_left_inj.mp h) hg hchar
  have hcardQ: (T.card:ℚ)≤U.card+1 := by exact_mod_cast hcard
  have hgQ: (3:ℚ)≤g:= by exact_mod_cast hg
  have hhQ: (A.h:ℚ)≤H :=Nat.cast_le.mpr hh
  have hheight:=mul_le_mul_of_nonneg_left hhQ hv0
  by_cases hW:A.Jm W
  · have h:=low_count h6 h7 x hmU.subset hq A
      (he.symm ▸ hg) (he.symm ▸ hg54) (he.symm ▸ hgp)
      (he.symm ▸ hOK.2.2.2.1) (he.symm ▸ hpol) hW S.onSeed (he.symm ▸ hlow)
    rw [he,hd] at h
    have hrest: (0:ℚ)≤9*(g:ℚ)*Q.totalDegree := by positivity
    linarith only [h,hcardQ,hheight,hrest,hgQ]
  · have hc γ (hγ:γ∈U) : (C.Q γ).natDegree≤C.u₀∧(C.P γ).natDegree≤C.u₁:= by
      obtain ⟨_,hQ,hP⟩:=C.degree γ hγ
      have ha :=agreement_bound (F:=F) (hmU.subset hγ)
      omega
    obtain ⟨R,hR⟩:=h5 A k c j W B hc (he.symm ▸ hg) (he.symm ▸ hgp) (he.symm ▸ hOK) hW
    have hb:=Nat.lt_of_mul_lt_mul_left ((high_count R).trans_lt hR)
    have hc' : (U.card:ℚ)≤(highFee g k c:ℚ)*A.h:= by
      exact_mod_cast (he ▸ zeh hb)
    have h:=hc'.trans (mul_le_mul_of_nonneg_right hhigh (zqJ _))
    linarith only [h,hheight,hcardQ,hgQ,hs]
end
end qDxaYpa
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qhDqsHe
theorem proof :q8SCoCa.c3 :=
  qZu9hjc.of_children qQKkxDd.proof
    (q7v3yjb.of_children qVHIGFe.proof
      (qTFhFCb.of_children P5_7_1_7Q434R12.proof1 P5_7_1_7Q434R12.proof)
      (qApzjua.of_children q4izpTc.proof qAv0Wab.proof))
    (q8Z6NHc.of_children
      (qG7TGJa.of_children qaTRbFe.proof qqgIGhd.proof
        qeFnRJb.proof)
      (qFwMjQd.of_children
        (q9sUlTb.of_children
          (qvWVeNa.of_children qzxonle.proof
            qofhpvd.proof)
          qQQM2Gb.proof qzhw4Oa.proof)
        qRIxBbd.proof
        (q33Mraa.of_children qBaLURa.proof q8hd3Fb.proof
          q80yiVc.proof))
      (qZbPQGe.of_children qs5yTLd.proof qdRD8me.proof))
end qhDqsHe
end
