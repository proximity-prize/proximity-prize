import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.AdicCompletion.Completeness
import ProximityPrize.SubmissionLower.ZRSdJhe
import ProximityPrize.SubmissionLower.ZSOuZfa
import ProximityPrize.SubmissionLower.Z60GVma
import ProximityPrize.SubmissionLower.Zdhd3Ub
import ProximityPrize.SubmissionLower.ZnsYgUd
set_option Elab.async false
open _root_ renaming CommRing → za6, Equiv.optionSubtypeNe → zk4, Function.Injective → zq4, Ideal → znc, Ideal.mul_mem_left → zBG, Ideal.mul_top → zFS, Ideal.pow_le_pow_right → zdr, Ideal.smul_eq_mul → zHM, IsFractionRing.injective → zxb, MvPolynomial.aeval → zIe, MvPolynomial.aeval_X → zTw, MvPolynomial.optionEquivLeft → zpj, Polynomial → zM1, Polynomial.X → z7y, Polynomial.aevalTower → zZC, Polynomial.ringHom_ext → z86, PowerSeries → zpm, PowerSeries.C → zMG, PowerSeries.constantCoeff → zbO, PowerSeries.constantCoeff_C → zr8, RingHom.comp_apply → zQb, RingHom.id → zz4, RingHom.ker → zdq, RingHom.mem_ker → zry
section
section
set_option backward.isDefEq.respectTransparency false
namespace q4XZUmd
noncomputable section
open Polynomial
open scoped Polynomial
variable {R S T:Type} [za6 R] [za6 S] [za6 T]
def ev (j:R →+* S) (x y :S) :R[X][X] →+* S :=
 eval₂RingHom (eval₂RingHom j x) y
def dx (p:R[X][X]) :R[X][X] :=
 p.sum fun i q=>monomial i q.derivative
theorem bXI (p:R[X][X]) (i:ℕ) : (dx p).coeff i=(p.coeff i).derivative := by
 classical
 by_cases hi:i∈p.support
 · simp [dx,sum_def,coeff_monomial,hi]
 · simp [dx,sum_def,coeff_monomial,hi,notMem_support_iff.mp hi]
theorem ev_map (j:R →+* S) (k :S →+* T) (x y :S) (p:R[X][X]) :
   k (ev j x y p)=ev (k.comp j) (k x) (k y) p:= by
 simp only [ev,coe_eval₂RingHom,hom_eval₂]
 congr 1
 apply z86
 · intro a
   simp [zQb]
 · simp [zQb]
private theorem ev_congr {I:znc R} {x y u v :R} (p:R[X][X])
  (hx :x ≡ u [SMOD I]) (hy :y ≡ v [SMOD I]) :
  ev (zz4 R) x y p ≡ ev (zz4 R) u v p [SMOD I] := by
 rw [SModEq.idealQuotientMk,ev_map,ev_map,
  SModEq.idealQuotientMk.mp hx,SModEq.idealQuotientMk.mp hy]
private def xSlice (p:R[X][X]) (y :R) :R[X] :=
 p.eval₂ (zz4 _) (C y)
private theorem ev_x (p:R[X][X]) (x y :R) :
  ev (zz4 R) x y p=(xSlice p y).eval x := by
 change _=evalRingHom x (xSlice p y)
 rw [xSlice,hom_eval₂]
 simp [ev,coe_eval₂RingHom,evalRingHom]
private theorem xSlice_dx (p:R[X][X]) (y :R) :
  (xSlice p y).derivative=xSlice (dx p) y := by
 rw [xSlice,eval₂_eq_sum,sum_def,derivative_sum]
 rw [xSlice,dx,sum_def,eval₂_finsetSum]
 apply Finset.sum_congr rfl
 intro i _
 simp only [RingHom.id_apply,eval₂_monomial,← map_pow]
 rw [mul_comm _ (C _),derivative_C_mul,mul_comm]
private def ySlice (p:R[X][X]) (x :R) :R[X] :=p.map (evalRingHom x)
private theorem ev_y (p:R[X][X]) (x y :R) :
  ev (zz4 R) x y p=(ySlice p x).eval y := by
 rw [ySlice,Polynomial.eval_map]
 rfl
private theorem taylor_mod {I:znc R} {n:ℕ} (hn:0<n)
    (p:R[X]) (x u:R) (hu:u∈I^n) :
    p.eval (x+u) ≡ p.eval x+p.derivative.eval x*u [SMOD (I^(n+1) :znc R)] := by
  obtain ⟨c,hc⟩:=p.exists_mul_sq_add_linear_part_eq_eval_add x u
  rw [← hc,add_assoc,add_comm (p.derivative.eval x*u)]
  exact (SModEq.zero.mpr (zBG _ _
    (Ideal.pow_le_pow_right (show n+1≤n*2 by omega)
      (by rw [pow_mul]; exact Ideal.pow_mem_pow hu 2)))).add SModEq.rfl |>.trans
        (by rw [zero_add])
private theorem mul_congr {I:znc R} {n:ℕ} {a b u:R}
  (hab:a ≡ b [SMOD I]) (hu:u∈I^n) :
  a*u ≡ b*u [SMOD (I^(n+1) :znc R)] := by
 rw [SModEq.sub_mem,← sub_mul,pow_succ']
 exact Ideal.mul_mem_mul (SModEq.sub_mem.mp hab) hu
private theorem linearize {I:znc R} {n:ℕ} (hn:0<n)
  (p:R[X][X]) (x y u v a b:R) (hu:u∈I^n) (hv :v∈I^n)
  (ha :ev (zz4 R) x y (dx p) ≡ a [SMOD I])
  (hb:ev (zz4 R) x y p.derivative ≡ b [SMOD I]) :
  ev (zz4 R) (x+u) (y+v) p ≡ ev (zz4 R) x y p+a*u+b*v
    [SMOD (I^(n+1) :znc R)] := by
 have hx :ev (zz4 R) (x+u) y p ≡
    ev (zz4 R) x y p+ev (zz4 R) x y (dx p)*u
    [SMOD (I^(n+1) :znc R)] := by
  simpa only [ev_x,xSlice_dx] using taylor_mod hn (xSlice p y) x u hu
 have hy :ev (zz4 R) (x+u) (y+v) p ≡
    ev (zz4 R) (x+u) y p+ev (zz4 R) (x+u) y p.derivative*v
    [SMOD (I^(n+1) :znc R)] := by
  simpa only [ev_y,ySlice,derivative_map] using taylor_mod hn (ySlice p (x+u)) y v hv
 have hxu:x+u ≡ x [SMOD I] := by
  rw [SModEq.sub_mem,add_sub_cancel_left]
  simpa only [pow_one] using zdr (I:=I) hn hu
 exact hy.trans ((hx.trans (SModEq.rfl.add (mul_congr ha hu))).add
  (mul_congr ((ev_congr p.derivative hxu SModEq.rfl).trans hb) hv))
private theorem limit {I:znc R} [IsAdicComplete I R] (z :ℕ→R)
  (hz : ∀ n,z n ≡ z (n+1) [SMOD (I^n:znc R)]) :
  ∃ a,∀ n,z n ≡ a [SMOD (I^n:znc R)] := by
 have hchain (m n:ℕ) (h:m≤n) :z m ≡ z n [SMOD (I^m • ⊤ : znc R)] := by
  rw [zHM,zFS]
  induction n,h using Nat.le_induction with
  | base=>rfl
  | succ n h ih=>exact ih.trans ((hz n).mono (Ideal.pow_le_pow_right h))
 obtain ⟨a,ha⟩:=IsPrecomplete.prec' z (hchain _ _)
 exact ⟨a,fun n=> by simpa only [zHM,zFS] using ha n⟩
theorem liftPair {F:Type} [Field F] (p q: (zpm F)[X][X]) (x₀ y₀:F)
    (hp:ev zbO x₀ y₀ p=0)
    (hq:ev zbO x₀ y₀ q=0)
    (hj:ev zbO x₀ y₀ (dx p) *
          ev zbO x₀ y₀ q.derivative -
        ev zbO x₀ y₀ p.derivative *
          ev zbO x₀ y₀ (dx q)≠0) :
    ∃ x y :zpm F,zbO x=x₀∧zbO y=y₀ ∧
      ev (zz4 _) x y p=0∧ev (zz4 _) x y q=0:= by
  let R:=zpm F
  let I:znc R:=Ideal.span {PowerSeries.X}
  let e :=ev (zz4 R)
  let π:=zbO (R:=F)
  let C₀:=zMG (R:=F)
  have hker :zdq π=I :=
    PowerSeries.ker_coeff_eq_max_ideal.trans PowerSeries.maximalIdeal_eq_span_X
  have res {x y :R} : x ≡ y [SMOD I]↔π x=π y := by
    rw [SModEq.sub_mem,← hker,zry,map_sub,sub_eq_zero]
  have red (r :R[X][X]) (x y :R) :π (e x y r)=ev π (π x) (π y) r := by
    simpa only [e,RingHom.comp_id] using ev_map (zz4 R) π x y r
  let a :=C₀ (ev π x₀ y₀ (dx p))
  let b:=C₀ (ev π x₀ y₀ p.derivative)
  let c:=C₀ (ev π x₀ y₀ (dx q))
  let d:=C₀ (ev π x₀ y₀ q.derivative)
  let k :=C₀ ((ev π x₀ y₀ (dx p)*ev π x₀ y₀ q.derivative -
    ev π x₀ y₀ p.derivative*ev π x₀ y₀ (dx q))⁻¹)
  have hk : (a*d-b*c)*k=1 := by
    simp only [a,b,c,d,k,← C₀.map_mul,← C₀.map_sub]
    exact (congrArg C₀ (mul_inv_cancel₀ hj)).trans (map_one C₀)
  let u (x y :R) :=(b*e x y q-d*e x y p)*k
  let v (x y :R) :=(c*e x y p-a*e x y q)*k
  have correction_mem {n:ℕ} {f g:R} (l m:R) (hf :f∈I^n) (hg:g∈I^n) :
      (l*f-m*g)*k∈I^n :=
    Ideal.mul_mem_right _ _ (Ideal.sub_mem _ (zBG _ _ hf) (zBG _ _ hg))
  let z :ℕ→R×R:= fun n=>Nat.recOn n (C₀ x₀,C₀ y₀)
    fun _ t=>(t.1+u t.1 t.2,t.2+v t.1 t.2)
  have step (n:ℕ) :z (n+1)=((z n).1+u (z n).1 (z n).2,(z n).2+v (z n).1 (z n).2) :=rfl
  have fixes (n:ℕ) :
      π (z n).1=x₀∧π (z n).2=y₀∧e (z n).1 (z n).2 p∈I^(n+1) ∧
        e (z n).1 (z n).2 q∈I^(n+1) := by
    induction n with
    | zero =>
      change π (C₀ x₀)=x₀∧π (C₀ y₀)=y₀ ∧
        e (C₀ x₀) (C₀ y₀) p∈I^1∧e (C₀ x₀) (C₀ y₀) q∈I^1
      simp only [π,C₀,zr8,true_and,pow_one,
        ← hker,zry]
      change π (e (C₀ x₀) (C₀ y₀) p)=0∧π (e (C₀ x₀) (C₀ y₀) q)=0
      simpa only [red,π,C₀,zr8] using And.intro hp hq
    | succ n ih =>
      obtain ⟨hx,hy,hf,hg⟩:=ih
      let x :=(z n).1
      let y :=(z n).2
      have hu:u x y∈I^(n+1) :=correction_mem b d hg hf
      have hv :v x y∈I^(n+1) :=correction_mem c a hf hg
      have same {w:R} (hw:w∈I^(n+1)) :π w=0:= by
        rw [← zry,hker]
        simpa only [pow_one] using zdr (I:=I) (m:=1) (by omega) hw
      have gradient (r :R[X][X]) :e x y r ≡ C₀ (ev π x₀ y₀ r) [SMOD I] := by
        rw [res,red,hx,hy]
        exact (zr8 _).symm
      rw [step]
      refine ⟨by rw [map_add,same hu,add_zero,hx],by rw [map_add,same hv,add_zero,hy],?_,?_⟩
      · have hh:=linearize (I:=I) (Nat.succ_pos n) p x y _ _ a b hu hv
          (gradient (dx p)) (gradient p.derivative)
        have cancel:e x y p+a*u x y+b*v x y=0:= by
          dsimp only [u,v]
          linear_combination -(e x y p)*hk
        exact SModEq.zero.mp (cancel ▸ hh)
      · have hh:=linearize (I:=I) (Nat.succ_pos n) q x y _ _ c d hu hv
          (gradient (dx q)) (gradient q.derivative)
        have cancel:e x y q+c*u x y+d*v x y=0:= by
          dsimp only [u,v]
          linear_combination -(e x y q)*hk
        exact SModEq.zero.mp (cancel ▸ hh)
  have coherent (j:R×R→R) (k' : R→R→R)
      (hs : ∀ n,j (z (n+1))=j (z n)+k' (z n).1 (z n).2)
      (hm : ∀ n,k' (z n).1 (z n).2∈I^(n+1)) (n:ℕ) :
      j (z n) ≡ j (z (n+1)) [SMOD (I^n:znc R)] := by
    rw [hs,SModEq.sub_mem,sub_add_cancel_left,Ideal.neg_mem_iff]
    exact zdr (Nat.le_succ n) (hm n)
  obtain ⟨x,hx⟩:=limit (fun n=>(z n).1) (coherent Prod.fst u
    (fun n=>congrArg Prod.fst (step n)) fun n =>
      correction_mem b d (fixes n).2.2.2 (fixes n).2.2.1)
  obtain ⟨y,hy⟩:=limit (fun n=>(z n).2) (coherent Prod.snd v
    (fun n=>congrArg Prod.snd (step n)) fun n =>
      correction_mem c a (fixes n).2.2.1 (fixes n).2.2.2)
  have vanish (r :R[X][X]) (hr : ∀ n,e (z n).1 (z n).2 r∈I^(n+1)) :
      e x y r=0:= by
    apply IsHausdorff.haus' (I:=I)
    intro n
    rw [zHM,zFS]
    exact (ev_congr r (hx n).symm (hy n).symm).trans
      (SModEq.zero.mpr (zdr (Nat.le_succ n) (hr n)))
  refine ⟨x,y,?_,?_,vanish p (fun n=>(fixes n).2.2.1),vanish q (fun n=>(fixes n).2.2.2)⟩
  · exact (res.mp (by simpa only [pow_one] using hx 1)).symm.trans (fixes 1).1
  · exact (res.mp (by simpa only [pow_one] using hy 1)).symm.trans (fixes 1).2.1
end
end q4XZUmd
end
section
set_option backward.isDefEq.respectTransparency false
namespace q4XZUmd
noncomputable section
open Polynomial

open qZu9hjc (atPair physicalDeriv HE)
open q8Z6NHc (Slot form)
open qfzuawb (dM map₂)
open qnSUPza (form_eq)
open qAW6lac (aMp)
open qpVvmab (Series base actual)
variable {E :Type} [Field E]
private def seriesForm {d s W:ℕ} (a :Slot d s W→Series E) : (Series E)[X][X] :=
 ∑ i,monomial i.val.1.val (monomial i.val.2.val (a i))
private theorem ev_seriesForm {d s W:ℕ} (a :Slot d s W→Series E) (x y :Series E) :
  ev (zz4 _) x y (seriesForm a)=aMp a x y := by
 simp only [seriesForm,aMp,ev,coe_eval₂RingHom,eval₂_finsetSum,
  eval₂_monomial,RingHom.id_apply]
private theorem eval_after_map {R S T:Type} [za6 R] [za6 S] [za6 T]
  (j:R →+* S) (k :S →+* T) (x y :T) (p:R[X][X]) :
  ev k x y (map₂ j p)=ev (k.comp j) x y p:= by
 simp only [ev,map₂,coe_mapRingHom,coe_eval₂RingHom,eval₂_map]
 congr 1
 apply z86 <;> simp [zQb]
private theorem dx_map {R S:Type} [za6 R] [za6 S]
  (j:R →+* S) (p:R[X][X]) :dx (map₂ j p)=map₂ j (dx p) := by
 ext i:1
 simp only [bXI,map₂,coe_mapRingHom,coeff_map,derivative_map]
private theorem dx_eq (p:E[X][X]) :dx p=physicalDeriv p:=rfl
private theorem reduction {d s W:ℕ} (p:E[X][X]) (hp:dM p s d W)
  (a :Slot d s W→Series E)
  (ha : ∀ i,zbO (a i) =
    algebraMap E (AlgebraicClosure E) ((p.coeff i.val.1).coeff i.val.2)) :
  map₂ zbO (seriesForm a)=map₂ (algebraMap E (AlgebraicClosure E)) p:= by
 have h:=congrArg (map₂ (algebraMap E (AlgebraicClosure E))) (form_eq p hp)
 simpa only [seriesForm,form,map_sum,map₂,coe_mapRingHom,map_monomial,ha] using h
private theorem fits_of_weight {p:E[X][X]} {d s W:ℕ} (hd:p.natDegree≤d)
  (hw:HE p s W) :dM p s d W:= by
 intro i j h
 have hi:p.coeff i≠0:= fun hz=>h (by simp [hz])
 exact ⟨(le_natDegree_of_ne_zero hi).trans hd,
  (Nat.add_le_add_right (le_natDegree_of_ne_zero h) _).trans (hw i hi)⟩
theorem proof :qpVvmab.c1 := by
  classical
  intro E _ _ A B δ
  let f :=seriesForm (fun j=>base (actual A B) δ (.inl j))
  let g:=seriesForm (fun j=>base (actual A B) δ (.inr (.inl j)))
  let π:=zbO (R:=AlgebraicClosure E)
  let j:=algebraMap E (AlgebraicClosure E)
  have hF:map₂ π f=map₂ j A.f := by
    apply reduction A.f (fits_of_weight le_rfl fun i hi=>(A.weight i).resolve_right hi)
    intro i
    simp [base,actual,qAW6lac.actualCoeffs]
  have hG:map₂ π g=map₂ j B.g:= by
    apply reduction B.g (fits_of_weight B.degree B.weight)
    intro i
    simp [base,actual,qAW6lac.actualCoeffs]
  have ev_red {p: (Series E)[X][X]} {q:E[X][X]} (h:map₂ π p=map₂ j q)
      (x y :AlgebraicClosure E) :ev π x y p=atPair j x y q:= by
    have he :=congrArg (ev (zz4 _) x y) h
    change ev (zz4 _) x y (map₂ π p)=ev (zz4 _) x y (map₂ j q) at he
    rw [eval_after_map,eval_after_map,RingHom.id_comp,RingHom.id_comp] at he
    exact he
  have hdX {p: (Series E)[X][X]} {q:E[X][X]} (h:map₂ π p=map₂ j q) :
      map₂ π (dx p)=map₂ j (physicalDeriv q) := by
    rw [← dx_map,← dx_eq,← dx_map,h]
  have hdY {p: (Series E)[X][X]} {q:E[X][X]} (h:map₂ π p=map₂ j q) :
      map₂ π p.derivative=map₂ j q.derivative := by
    change (p.derivative.map (mapRingHom π))=q.derivative.map (mapRingHom j)
    rw [← derivative_map,← derivative_map]
    exact congrArg derivative h
  have lift (i:Fin B.size) :
      ∃ x y :Series E,π x=(B.point i).1∧π y=(B.point i).2 ∧
        ev (zz4 _) x y f=0∧ev (zz4 _) x y g=0:= by
    apply liftPair f g (B.point i).1 (B.point i).2
    · rw [ev_red hF]
      exact B.f_zero i
    · rw [ev_red hG]
      exact B.g_zero i
    · rw [ev_red (hdX hF),ev_red (hdY hG),ev_red (hdY hF),ev_red (hdX hG)]
      exact B.simple i
  choose x y hx hy hf hg using lift
  exact ⟨⟨x,y,hx,hy,fun i=>(ev_seriesForm _ _ _).symm.trans (hf i),
    fun i=>(ev_seriesForm _ _ _).symm.trans (hg i)⟩⟩
end
end q4XZUmd
end
end
section
section
set_option backward.isDefEq.respectTransparency false
namespace qHJDQEb
noncomputable section
open scoped Classical
open cu (L)
open P5 (p)
open qAW6lac (Index jo ng spectral)
def c1 :Prop :=
  ∀ d D W:ℕ,0<D→D <p→3≤d→d*D ≤W → ∀ k :Fin 3,
    ∃ R:zM1 (pairField d D W k),R≠0 ∧
      Polynomial.aeval (pointX d D W) R=0∧R.natDegree≤ng d D W k
def c2 :Prop :=
  ∀ d D W:ℕ,0<D→D <p→3≤d→d*D ≤W → ∀ k :Fin 3,
    pointY d D W∈pointField d D W k
def c3:Prop :=
  ∀ d D W:ℕ,0<D→D <p→3≤d→d*D ≤W → ∀ k :Fin 3,
    FiniteDimensional (pairField d D W k) (pointField d D W k) →
    pointY d D W∈pointField d D W k →
    ∃ Q:jo d D W,Q≠0∧incidence d D W Q=0 ∧
      Q.weightedTotalDegree (blockWeight k) ≤
        Module.finrank (pairField d D W k) (pointField d D W k)
private theorem univariate_generator {R F:Type} [za6 R] [IsDomain R]
   [UniqueFactorizationMonoid R] [Field F] (j:R →+* F) (hj:zq4 j) (x :F)
   (hex : ∃ Q:zM1 R,Q≠0∧Q.eval₂ j x=0) :
   ∃ P:zM1 R,P≠0∧P.eval₂ j x=0 ∧
     ∀ Q:zM1 R,Q.eval₂ j x=0→P∣Q:= by
 let φ:=Polynomial.eval₂RingHom j x
 have hker :zdq φ ≠ ⊥ := by
   obtain ⟨Q,hQ,hz⟩:=hex
   intro he
   have hmem:Q∈zdq φ:=hz
   exact hQ (by simpa [he] using hmem)
 obtain ⟨P,hmem,hP⟩:=(RingHom.ker_isPrime φ).exists_mem_prime_of_ne_bot hker
 have hz :P.eval₂ j x=0:=hmem
 have hpos :P.natDegree≠0:= by
   intro h
   obtain ⟨a,ha⟩:=Polynomial.natDegree_eq_zero.mp h
   rw [← ha,Polynomial.eval₂_C] at hz
   exact hP.ne_zero (by rw [← ha,hj (hz.trans j.map_zero.symm),Polynomial.C_0])
 let K:=FractionRing R
 let ι:K →+* F:=IsFractionRing.lift hj
 let:Algebra K F:=ι.toAlgebra
 have hι:ι.comp (algebraMap R K)=j:=RingHom.ext (IsFractionRing.lift_algebraMap hj)
 have hmap (Q:zM1 R) :
     Polynomial.aeval x (Q.map (algebraMap R K))= Q.eval₂ j x := by
   rw [Polynomial.aeval_def]
   change Polynomial.eval₂ ι x (Q.map (algebraMap R K))= _
   rw [Polynomial.eval₂_map,hι]
 let:StrongNormalizationMonoid R:=UniqueFactorizationMonoid.strongNormalizationMonoid
 let:NormalizedGCDMonoid R:=UniqueFactorizationMonoid.toNormalizedGCDMonoid R
 have hprim:=hP.irreducible.isPrimitive hpos
 have hirr :Irreducible (P.map (algebraMap R K)) :=
   (hprim.irreducible_iff_irreducible_map_fraction_map (K:=K)).mp hP.irreducible
 refine ⟨P,hP.ne_zero,hz,fun Q hQ=>hprim.dvd_of_fraction_map_dvd_fraction_map (K:=K) ?_⟩
 exact (hirr.dvd_iff_aeval_eq_zero (hmap P |>.trans hz)).mp (hmap Q |>.trans hQ)
private theorem incidence_generator {d D W:ℕ}
    (hind:AlgebraicIndependent L (projectedCoeff (d:=d) (D:=D) (W:=W)))
    (hex : ∃ Q:jo d D W,Q≠0∧incidence d D W Q=0) :
    ∃ P:jo d D W,P≠0∧incidence d D W P=0 ∧
      ∀ Q:jo d D W,incidence d D W Q=0→P∣Q:= by
  let s :=spectral d D W
  let e :=(MvPolynomial.renameEquiv L (zk4 s).symm).trans
    (zpj L {i:Index d D W // i≠s})
  let j:=zIe (R:=L) (projectedCoeff (d:=d) (D:=D) (W:=W))
  let x :=atInc s
  have heval : (zZC j x).comp e.toAlgHom=zIe atInc:= by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply,zTw]
    change zZC j x
      (zpj L {i:Index d D W // i≠s}
        (MvPolynomial.rename (zk4 s).symm (MvPolynomial.X i)))=atInc i
    rw [MvPolynomial.rename_X]
    by_cases hi:i=s
    · subst i
      rw [Equiv.optionSubtypeNe_symm_self,MvPolynomial.optionEquivLeft_X_none,
        Polynomial.aevalTower_X]
    · rw [Equiv.optionSubtypeNe_symm_of_ne hi,MvPolynomial.optionEquivLeft_X_some,
        Polynomial.aevalTower_C]
      exact zTw _ _
  have he (Q:jo d D W) :
      (e Q).eval₂ j.toRingHom x=0↔incidence d D W Q=0 :=
    (show (zZC j x).comp e.toAlgHom Q=0↔_ from by
      rw [heval,incidence_over_field Q])
  obtain ⟨Q,hQ,hz⟩:=hex
  obtain ⟨P,hP,hPz,hgen⟩:=univariate_generator j.toRingHom
    (algebraicIndependent_iff_injective_aeval.mp hind) x
    ⟨e Q,fun h=>hQ (e.injective (h.trans e.map_zero.symm)),(he Q).mpr hz⟩
  refine ⟨e.symm P,fun h=>hP (e.symm.injective (h.trans e.symm.map_zero.symm)),?_,?_⟩
  · exact (he _).mp (by simpa only [AlgEquiv.apply_symm_apply] using hPz)
  · intro A hA
    have hdiv :e.symm P∣e.symm (e A) :=
      map_dvd e.symm.toRingEquiv.toRingHom (hgen (e A) ((he A).mpr hA))
    simpa only [AlgEquiv.symm_apply_apply] using hdiv
theorem of_children (KK:c1) (jU:c2) (normRelation :c3) :
  qfzuawb.c1 := by
 intro d D W hD hp hd hW
 have hY:=jU d D W hD hp hd hW
 have hX (k :Fin 3) :IsIntegral (pairField d D W k) (pointX d D W) ∧
    Module.finrank (pairField d D W k) (pointField d D W k)≤ng d D W k := by
  obtain ⟨R,hR,hRzero,hdeg⟩:=KK d D W hD hp hd hW k
  have hi:IsIntegral (pairField d D W k) (pointX d D W) :=
    (show IsAlgebraic (pairField d D W k) (pointX d D W) from ⟨R,hR,hRzero⟩).isIntegral
  refine ⟨hi,?_⟩
  rw [pointField,IntermediateField.adjoin.finrank hi]
  exact (Polynomial.natDegree_le_of_dvd (minpoly.dvd _ _ hRzero) hR).trans hdeg
 have relations (k :Fin 3) : ∃ Q:jo d D W,Q≠0∧incidence d D W Q=0 ∧
    Q.weightedTotalDegree (blockWeight k)≤ng d D W k := by
  obtain ⟨Q,hQ,hz,hdeg⟩:=normRelation d D W hD hp hd hW k
    (IntermediateField.adjoin.finiteDimensional (hX k).1) (hY k)
  exact ⟨Q,hQ,hz,hdeg.trans (hX k).2⟩
 obtain ⟨P,hP,hz,hgen⟩:=incidence_generator
  (projected_independent (hX 2).1 (hY 2)) (by
    obtain ⟨Q,hQ,hQz,_⟩:=relations 2
    exact ⟨Q,hQ,hQz⟩)
 refine ⟨⟨P,hP,(vanishes_iff_incidence P).mpr hz,fun Q hQ =>
  hgen Q ((vanishes_iff_incidence Q).mp hQ)⟩,?_⟩
 intro m hm k
 obtain ⟨Q,hQ,hQz,hdeg⟩:=relations k
 have hw:=(MvPolynomial.le_weightedTotalDegree (blockWeight k) hm).trans
  ((MvPolynomial.weightedTotalDegree_le_of_dvd _ (hgen Q hQz) hQ).trans hdeg)
 simpa only [Finsupp.weight_apply,blockWeight,smul_eq_mul,mul_ite,mul_one,mul_zero] using hw
end
end qHJDQEb
end
section
set_option backward.isDefEq.respectTransparency false
namespace qnSUPza
open cu (L)
open Polynomial
open qAW6lac (Index jo aMp)
open qfzuawb (dM coeffs deform)
open qZu9hjc (atPair jacobian)
open q8Z6NHc (Slot)
def c1 :Prop :=
  ∀ {B:Type} [Field B] [Algebra L B] (d D W:ℕ),0<D→3≤d→d*D ≤W →
    ∀ (α:Index d D W→B) (P:jo d D W),P≠0 →
    ∀ (m:ℕ) (pt:Fin m→AlgebraicClosure B×AlgebraicClosure B),
    zq4 pt →
    ∀ (xy : (Slot d D W→L)→(Slot d D W→L)→Fin m→Germ B×Germ B),
      (∀ a b i,(zbO (xy a b i).1,
        zbO (xy a b i).2)=pt i) →
      ∃ δ:Index d D W→L,deform α δ P≠0 ∧
        zq4 (fun i =>
          branchValue α δ (xy (fun k=>δ (.inl k)) (fun k=>δ (.inr (.inl k))) i))
def c2 :Prop :=
  ∀ {B:Type} [Field B] [Algebra L B] (d D W:ℕ) (f g:B[X][X]),
    dM f D d W→dM g D d W →
    ∀ (x y :AlgebraicClosure B),
      atPair (algebraMap B _) x y f=0→atPair (algebraMap B _) x y g=0 →
      jacobian (algebraMap B _) x y f g≠0 →
      ∀ (a b:Slot d D W→L),
        ∃ xy :Germ B×Germ B,
          (zbO xy.1,zbO xy.2)=(x,y) ∧
          aMp (fun i=>motion ((f.coeff i.val.1).coeff i.val.2) (a i)) xy.1 xy.2=0 ∧
          aMp (fun i=>motion ((g.coeff i.val.1).coeff i.val.2) (b i)) xy.1 xy.2=0
theorem of_children (h1 :c1) (h2 :c2) :qfzuawb.c2 := by
 classical
 intro B _ _ d D W hD hd hW f g Q N hf hg hQ T P
 have hLift (a b:Slot d D W→L) (i:Fin T.size) :=
  h2 d D W f g hf hg (T.point i).1 (T.point i).2 (T.f_zero i) (T.g_zero i) (T.simple i) a b
 choose xy hxy hfx hgx using hLift
 obtain ⟨δ,hδ,hv⟩:=h1 d D W hD hd hW (coeffs f g Q) P.poly P.nonzero
  T.size T.point T.distinct xy (fun a b i=> by simpa using hxy a b i)
 let a :Slot d D W→L:= fun k=>δ (.inl k)
 let b:Slot d D W→L:= fun k=>δ (.inr (.inl k))
 obtain ⟨n,hn,hdiv⟩:=specialize f g Q N hQ T P δ hδ (xy a b)
  (fun i=> by simpa using hxy a b i) (hfx a b) (hgx a b) hv
 exact ⟨δ,n,hn,hdiv⟩
end qnSUPza
end
section
set_option backward.isDefEq.respectTransparency false
namespace qlcYNOb
noncomputable section
open Polynomial
open cu (L FX)
open P5_7_7 (phys)
open q2TwyLa (i5 aQ polar diff)
open qoGY3we
open qz2teNe
open q0n1P7d (eval_integral root_integral ref_inverse)
open private inverse_integral from ProximityPrize.SubmissionLower.ZnsYgUd
private abbrev Off (A:Cover) := ↥(offZero A)
private abbrev into (A:Cover) :Off A →+* Target :=
 embedding.comp (offZero A).val.toRingHom
private theorem inverted (A:Cover) :
  IsUnit (algebraMap tu (Off A) (z7y*A.g.reverse)) :=
 IsLocalization.map_units (Off A)
  (⟨_,⟨1,pow_one _⟩⟩:Submonoid.powers (z7y*A.g.reverse))
private def coord (A:Cover) : (Off A)ˣ :=
 (isUnit_of_mul_isUnit_left (by simpa only [map_mul] using inverted A :
   IsUnit (algebraMap tu (Off A) Polynomial.X *
    algebraMap tu (Off A) A.g.reverse))).unit
private theorem coord_val (A:Cover) : (coord A:Off A)=algebraMap tu (Off A) Polynomial.X :=
 IsUnit.unit_spec _
private def sW (A:Cover) :tu →+* Off A :=
 eval₂RingHom ((algebraMap tu (Off A)).comp C) (↑(coord A)⁻¹)
private theorem affine_image (A:Cover) : (into A).comp (sW A)=seriesIn.comp (bY false) := by
 apply z86
 · intro a
   change into A ((sW A) (C a))=seriesIn (bY false (C a))
   rw [sW,coe_eval₂RingHom,eval₂_C,zQb]
   change embedding (algebraMap tu kB (C a))= _
   rw [embedding_on]
   simp only [bY,coe_eval₂RingHom,eval₂_C]
 · let x :FX:=phys (z7y:L[X])
   have hx :x≠0:=(map_ne_zero_iff phys (zxb L[X] FX)).2 X_ne_zero
   have hu:into A (coord A)=seriesIn (zMG x⁻¹) := by
    rw [coord_val]
    change embedding (algebraMap tu kB z7y)= _
    rw [embedding_on,bY,coe_eval₂RingHom,eval₂_X]
    rfl
   have h:into A (coord A)*into A (↑(coord A)⁻¹)=1 := by
    rw [← map_mul,Units.mul_inv,map_one]
   simp only [zQb,sW,bY,coe_eval₂RingHom,eval₂_X,Bool.false_eq_true,
    ↓reduceIte]
   change into A (↑(coord A)⁻¹)=seriesIn (zMG x)
   rw [← inv_eq_of_mul_eq_one_right h,hu]
   apply inv_eq_of_mul_eq_one_right
   rw [← map_mul,← map_mul,inv_mul_cancel₀ hx,map_one,map_one]
private theorem radical_unit_at (A:Cover) :IsUnit (sW A A.g) := by
 let u:=coord A
 let i:=(algebraMap tu (Off A)).comp (C:i5 →+* tu)
 let:Invertible (↑u⁻¹:Off A) :=invertibleOfRightInverse _ _ (Units.inv_mul u)
 have hr :=eval₂_reverse_mul_pow i (↑u⁻¹:Off A) A.g
 change A.g.reverse.eval₂ i (↑u:Off A)*(↑u⁻¹:Off A)^A.g.natDegree=sW A A.g at hr
 have h:eval₂RingHom i (↑u:Off A)=algebraMap tu (Off A) := by
   apply z86
   · intro a
     rw [coe_eval₂RingHom,eval₂_C]
     rfl
   · rw [coe_eval₂RingHom,eval₂_X]
     exact coord_val A
 change eval₂RingHom i (↑u:Off A) A.g.reverse*(↑u⁻¹:Off A)^A.g.natDegree= _ at hr
 rw [h] at hr
 rw [← hr]
 apply IsUnit.mul _ ((u⁻¹).isUnit.pow _)
 exact isUnit_of_mul_isUnit_right (by simpa only [map_mul] using inverted A :
   IsUnit (algebraMap tu (Off A) Polynomial.X*algebraMap tu (Off A) A.g.reverse))
private theorem branch_unit_at (A:Cover) :IsUnit (sW A (branchPoly A.f A.r)) := by
 let B:=branchPoly A.f A.r
 obtain ⟨u,hu⟩:=A.branch_unit
 let b:=B*C (↑u⁻¹:i5)
 have hm:b.Monic:=monic_mul_C_of_leadingCoeff_mul_eq_one (by rw [← hu,Units.mul_inv])
 have hd:b∣B:= by
   refine ⟨C (↑u:i5),?_⟩
   change B=(B*C (↑u⁻¹:i5))*C (↑u:i5)
   rw [mul_assoc,← C_mul,Units.inv_mul,C_1,mul_one]
 have hd' : B∣b:=dvd_mul_right _ _
 obtain ⟨n,hn⟩:=A.radical_pow
 have hb:b∣A.g^n:=(map_dvd_map a8p (zxb i5 aQ) hm).mp
   (((Polynomial.map_dvd a8p hd).trans (show B.map a8p∣(A.g^n).map a8p by
     simpa only [Polynomial.map_pow] using hn)))
 exact isUnit_of_dvd_unit (map_dvd (sW A) (hd'.trans hb))
   (by rw [map_pow]; exact (radical_unit_at A).pow _)
theorem proof :qz2teNe.c1 := by
 intro A P J
 let ι:=into A
 let k :=sW A
 let y :=seriesIn J.y
 let r :=C (zMG A.r)
 have ev (f :tu[X]) :
     (f.map k).eval₂ ι y=seriesIn (f.eval₂ (bY false) J.y) := by
   rw [eval₂_map,show ι.comp k= _ from affine_image A,hom_eval₂]
 have hr : (A.f.map k).eval₂ ι y=0:= by rw [ev,J.root,map_zero]
 have hb:IsUnit (k (polar A.f))∧IsUnit (k (A.f.eval r)) := by
   have h:=branch_unit_at A
   change IsUnit (k (polar A.f*A.f.eval r)) at h
   rw [map_mul] at h
   exact ⟨isUnit_of_mul_isUnit_left h,isUnit_of_mul_isUnit_right h⟩
 have hl:IsUnit (k A.f.leadingCoeff) := by
   have h:=hb.1
   rw [polar,resultant_deriv (natDegree_pos_iff_degree_pos.mp A.positive),map_mul,map_mul] at h
   exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left h)
 have hy :ι.IsIntegralElem y :=
   root_integral ι hr (by rw [leadingCoeff_map_of_leadingCoeff_ne_zero _ hl.ne_zero]; exact hl)
 have hd:ι.IsIntegralElem (seriesIn (A.f.derivative.eval₂ (bY false) J.y))⁻¹:= by
   obtain ⟨a,b,_,_,hab⟩:=exists_mul_add_mul_eq_C_resultant A.f A.f.derivative
     (m:=A.f.natDegree) (n:=A.f.natDegree - 1) le_rfl
     (natDegree_derivative_le A.f) (Or.inl A.positive.ne')
   have h:=congrArg (eval₂RingHom (ι.comp k) y) hab
   simp only [map_add,map_mul,coe_eval₂RingHom,eval₂_C,← eval₂_map,hr,zero_mul,zero_add] at h
   rw [ev A.f.derivative] at h
   exact inverse_integral ι (eval_integral ι hy (b.map k)) hb.1 h
 have href :ι (k r)=seriesIn (zMG (phys (C A.r))) := by
   change (ι.comp k) r= _
   rw [affine_image A]
   simp only [zQb,r,bY,coe_eval₂RingHom,eval₂_C,PowerSeries.map_C]
   congr 2
 have ha :ι.IsIntegralElem (seriesIn (J.y-PowerSeries.C (phys (C A.r))))⁻¹:= by
   rw [map_sub,← href]
   apply ref_inverse ι hr hy (k r)
   rw [eval_map,eval₂_hom]
   exact hb.2
 have hn:ι.IsIntegralElem (seriesIn ((diff A.f).eval₂ (bY false) J.y)) := by
   rw [← ev]
   exact eval_integral ι hy ((diff A.f).map k)
 have h:=congrArg seriesIn J.seed_eq
 simp only [map_mul,map_neg] at h
 rw [← mul_inv_cancel_right₀ (J.ref_unit.map seriesIn).ne_zero (seriesIn J.logSeed),
   ← mul_inv_cancel_right₀ (J.simple.map seriesIn).ne_zero
     (seriesIn J.logSeed*seriesIn (J.y-PowerSeries.C (phys (C A.r)))),h]
 exact ((hn.neg ι).mul ι hd).mul ι ha
end
end qlcYNOb
end
end
