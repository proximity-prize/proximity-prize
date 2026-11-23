import ProximityPrize.SubmissionLower.ZMNCpvb
import ProximityPrize.SubmissionLower.ZAZ7Tec
import Mathlib.RingTheory.AdicCompletion.Completeness
set_option Elab.async false
open _root_ renaming CommRing → za6, Field → zrb, Finsupp.single → zhf, Function.Injective → zq4, MvPolynomial → z3y, MvPolynomial.eval → zY9, MvPolynomial.eval_C → z9X, MvPolynomial.eval_X → zV6, MvPolynomial.hom_eval₂ → zUe, Polynomial.evalRingHom → zhy, Polynomial.map_sum → zWe, PowerSeries.X_dvd_iff → zzu, PowerSeries.constantCoeff → zbO, PowerSeries.constantCoeff_C → zr8
section
set_option backward.isDefEq.respectTransparency false
namespace quQ0Dxa
noncomputable section
open cu (L)
open qAW6lac (Index jo aMp spectral)
open qfzuawb (deform ic)
open qnSUPza (Germ motion branchValue)
open q8Z6NHc (Slot)
open scoped Classical
private theorem avoid {F σ:Type} [zrb F] (P:z3y σ F) (hP:P≠0)
  (v :σ→L→F) (hv : ∀ i,zq4 (v i)) :
  ∃ a :σ→L,zY9 (fun i=>v i (a i)) P≠0:= by
 by_contra! hn
 apply hP
 apply MvPolynomial.funext_set (fun i=>Set.range (v i))
  (fun i=>Set.infinite_range_of_injective (hv i))
 intro x hx
 choose a ha using fun i=>hx i (Set.mem_univ i)
 rw [map_zero,← show (fun i=>v i (a i))=x from funext ha]
 exact hn a
variable {B:Type} [zrb B] [Algebra L B]
local notation "Ω[" B "]" => AlgebraicClosure B
local notation "j[" B "]" => (algebraMap B (AlgebraicClosure B))
local notation "l[" B "]" => (RingHom.comp (algebraMap B (AlgebraicClosure B)) (algebraMap L B))
local notation "ct[" B "]" => (PowerSeries.constantCoeff :Germ B →+* Ω[B])
local notation "c₁[" B "]" => (PowerSeries.coeff (R:=Ω[B]) 1)
local notation "MC" => MvPolynomial.C
local notation "MX" => MvPolynomial.X
private theorem deformation_eval {d D W:ℕ} (α:Index d D W→B)
   (δ:Index d D W→L) (P:jo d D W) :
   j[B] (((deform α δ P).eval 0).eval 1) =
     P.eval₂ l[B] (fun i=>j[B] (α i)+l[B] (δ i)) := by
 let e :=RingHom.comp j[B] ((zhy (1 :B)).comp (zhy (0:Polynomial B)))
 change e (deform α δ P)= _
 rw [deform,zUe]
 congr 1
 · ext r
   simp [e]
 · funext i
   by_cases hi:i=spectral d D W <;> simp [e,ic,hi]
private def valuePoly {d D W:ℕ} (α:Index d D W→B) (xy :Germ B×Germ B) :
  z3y (Slot (d-1) D (W-D)) Ω[B] :=
 MC (c₁[B] (aMp (fun i=>PowerSeries.C (j[B] (α (.inr (.inr i))))) xy.1 xy.2)) +
  ∑ k,MC (ct[B] xy.1^k.val.2.val*ct[B] xy.2^k.val.1.val)*MX k
private theorem eval_valuePoly {d D W:ℕ} (α:Index d D W→B)
  (δ:Index d D W→L) (xy :Germ B×Germ B) :
  zY9 (fun k=>l[B] (δ (.inr (.inr k)))) (valuePoly α xy) =
    c₁[B] (branchValue α δ xy) := by
 have h (a :B) (z :L) (x :Germ B) :
    c₁[B] (motion a z*x)=c₁[B] (PowerSeries.C (j[B] a)*x)+l[B] z*ct[B] x := by
  simp [motion,PowerSeries.coeff_one_mul,mul_comm]
 simp only [valuePoly,map_add,map_sum,z9X,map_mul,
  zV6,branchValue,aMp]
 simp only [mul_assoc,h,map_mul,map_pow,Finset.sum_add_distrib]
 congr 1
 apply Finset.sum_congr rfl
 intro i _
 ring
omit [Algebra L B] in
private theorem valuePoly_coeff {d D W:ℕ} (α:Index d D W→B) (xy :Germ B×Germ B)
   (k :Slot (d-1) D (W-D)) :
   (valuePoly α xy).coeff (zhf k 1) =
     ct[B] xy.1^k.val.2.val*ct[B] xy.2^k.val.1.val := by
 have hn:zhf k (1 :ℕ)≠0:= fun h=> by
   simpa using congrArg (fun f :Slot (d-1) D (W-D) →₀ ℕ=>f k) h
 rw [valuePoly,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,MvPolynomial.coeff_C,
   MvPolynomial.coeff_sum]
 simp only [Ne.symm hn,ite_false,zero_add,MvPolynomial.coeff_C_mul,MvPolynomial.coeff_X,
   (Finsupp.single_left_injective (one_ne_zero : (1 :ℕ)≠0)).eq_iff,mul_ite,mul_one,mul_zero,
   Finset.sum_ite_eq',Finset.mem_univ,ite_true]
theorem directions :qnSUPza.c1 := by
  classical
  intro B _ _ d D W hD hd hW α P hP m pt hpt xy hxy
  let J:=Slot (d-1) D (W-D)
  let v (i:Index d D W) (a :L) :=j[B] (α i)+l[B] a
  have hp:P.map l[B]≠0:= fun h=>hP ((MvPolynomial.map_injective l[B] (l[B]).injective)
    (h.trans (map_zero (MvPolynomial.map l[B])).symm))
  obtain ⟨δ₀,hδ₀⟩:=avoid (P.map l[B]) hp v (fun _ _ _ h=>(l[B]).injective (add_left_cancel h))
  let δ (z :J→L) :Index d D W→L
    | .inl i=>δ₀ (.inl i)
    | .inr (.inl i)=>δ₀ (.inr (.inl i))
    | .inr (.inr i)=>z i
  let u:Index d D W→z3y J Ω[B]
    | .inl i=>MC (v (.inl i) (δ₀ (.inl i)))
    | .inr (.inl i)=>MC (v (.inr (.inl i)) (δ₀ (.inr (.inl i))))
    | .inr (.inr i)=>MC (j[B] (α (.inr (.inr i))))+MX i
  let R:=P.eval₂ (RingHom.comp MC l[B]) u
  have hR (z :J→L) :zY9 (fun k=>l[B] (z k)) R =
      P.eval₂ l[B] (fun i=>v i (δ z i)) := by
    rw [zUe]
    congr 1
    · ext r
      simp
    · funext i
      rcases i with i | (i | i)
      · exact z9X _
      · exact z9X _
      · change (zY9 (fun k :J=>l[B] (z k)))
          (MC (j[B] (α (.inr (.inr i))))+MX i)= _
        rw [map_add,z9X,zV6]
  have hR₀:R≠0:= by
    intro hz
    apply hδ₀
    rw [← MvPolynomial.eval₂_eq_eval_map]
    have he :δ (fun k=>δ₀ (.inr (.inr k)))=δ₀:= by
      funext i
      rcases i with i | (i | i) <;> rfl
    simpa only [he,hz,map_zero] using (hR (fun k=>δ₀ (.inr (.inr k)))).symm
  let ab:=xy (fun k=>δ₀ (.inl k)) (fun k=>δ₀ (.inr (.inl k)))
  let Q (i:Fin m) :=valuePoly α (ab i)
  have hWidth:2*D ≤W:=(Nat.mul_le_mul_right D (show 2≤d by omega)).trans hW
  let kx :J:=⟨(⟨0,by omega⟩,⟨1,by omega⟩),by change 1+0*D ≤W-D; omega⟩
  let ky :J:=⟨(⟨1,by omega⟩,⟨0,by omega⟩),by change 0+1*D ≤W-D; omega⟩
  have hQ:zq4 Q:= by
    intro i k hk
    have coord (s :J) :ct[B] (ab i).1^s.val.2.val*ct[B] (ab i).2^s.val.1.val =
        ct[B] (ab k).1^s.val.2.val*ct[B] (ab k).2^s.val.1.val := by
      rw [← valuePoly_coeff α (ab i) s,← valuePoly_coeff α (ab k) s]
      exact congrArg (fun p:z3y J Ω[B]=>p.coeff (zhf s 1)) hk
    have hp' : (ct[B] (ab i).1,ct[B] (ab i).2)=(ct[B] (ab k).1,ct[B] (ab k).2) :=
      Prod.ext (by simpa [kx] using coord kx) (by simpa [ky] using coord ky)
    apply hpt
    rw [← hxy _ _ i,← hxy _ _ k]
    exact hp'
  let pairs :=(Finset.univ :Finset (Fin m×Fin m)).filter fun ik=>ik.1≠ik.2
  let S:=R * ∏ ik∈pairs,(Q ik.1-Q ik.2)
  have hS:S≠0:=mul_ne_zero hR₀ (Finset.prod_ne_zero_iff.mpr fun ik hik =>
    sub_ne_zero.mpr (hQ.ne (Finset.mem_filter.mp hik).2))
  obtain ⟨z,hz⟩:=avoid S hS (fun _=>l[B]) (fun _=>(l[B]).injective)
  let e :=zY9 (fun k :J=>l[B] (z k))
  have hz' : e R * ∏ ik∈pairs,(e (Q ik.1)-e (Q ik.2))≠0:= by
    simpa only [S,map_mul,map_prod,map_sub] using hz
  refine ⟨δ z,?_,?_⟩
  · intro h
    have hn:=(mul_ne_zero_iff.mp hz').1
    apply hn
    change zY9 _ R=0
    rw [hR,← deformation_eval,h]
    simp
  · intro i k hk
    by_contra hn
    have hm: (i,k)∈pairs := by simp [pairs,hn]
    have hu:=(Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hz').2) _ hm
    apply hu
    apply sub_eq_zero.mpr
    change zY9 (fun k=>l[B] (δ z (.inr (.inr k)))) (Q i) =
      zY9 (fun k=>l[B] (δ z (.inr (.inr k)))) (Q k)
    rw [eval_valuePoly,eval_valuePoly]
    exact congrArg (c₁[B]) hk
end
end quQ0Dxa
end
section
set_option backward.isDefEq.respectTransparency false
namespace quQ0Dxa
noncomputable section
open Polynomial
open cu (L)
open qAW6lac (aMp)
open qfzuawb (dM map₂)
open qnSUPza (Germ motion form_eq)
open qZu9hjc (atPair physicalDeriv jacobian)
open q8Z6NHc (Slot form)
open scoped Classical
private def px {R:Type} [za6 R] (p:R[X][X]) (y :R) :=p.eval (C y)
private def py {R:Type} [za6 R] (p:R[X][X]) (x :R) :=p.map (evalRingHom x)
private def ev {R:Type} [za6 R] (p:R[X][X]) (x y :R) :=(py p x).eval y
private theorem ev_px {R:Type} [za6 R] (p:R[X][X]) (x y :R) :
  (px p y).eval x=ev p x y := by
 change evalRingHom x (p.eval (C y))= _
 rw [← eval₂_at_apply,coe_evalRingHom,eval_C]
 exact (eval_map _ _).symm
private theorem px_map {R S:Type} [za6 R] [za6 S] (k :R →+* S)
  (p:R[X][X]) (y :R) :
  (px p y).map k=px (map₂ k p) (k y) := by
 change mapRingHom k (p.eval (C y))= _
 rw [← eval₂_at_apply,coe_mapRingHom,map_C]
 exact (eval_map _ _).symm
private theorem py_map {R S:Type} [za6 R] [za6 S] (k :R →+* S)
  (p:R[X][X]) (x :R) :
  (py p x).map k=py (map₂ k p) (k x) := by
 simp only [py,map₂,coe_mapRingHom,map_map]
 congr 1
 apply RingHom.ext
 intro q
 change k (q.eval x)=(q.map k).eval (k x)
 rw [eval_map,eval₂_at_apply]
private theorem ev_diff {R:Type} [za6 R] (p:R[X][X]) (t x y x' y' : R)
  (hx :t∣x'-x) (hy :t∣y'-y) :t∣ev p x' y' - ev p x y := by
 have a :=hx.trans (sub_dvd_eval_sub x' x (px p y'))
 have b:=hy.trans (sub_dvd_eval_sub y' y (py p x))
 rw [ev_px,ev_px] at a
 change t∣ev p x y' - ev p x y at b
 convert dvd_add a b using 1
 ring
variable {F:Type} [zrb F]
local notation "S" => PowerSeries F
local notation "T" => (PowerSeries.X:PowerSeries F)
local notation "ct" => (PowerSeries.constantCoeff :S →+* F)
local notation "pc" => (PowerSeries.C:F →+* S)
private theorem remainder (p:S[X]) (x u:S) (n:ℕ) (hu:T^(n+1)∣u) :
   T^(n+2)∣p.eval (x+u) - p.eval x - pc (ct (p.derivative.eval x))*u:= by
 obtain ⟨r,hr⟩:=p.exists_mul_sq_add_linear_part_eq_eval_add x u
 rw [← hr]
 have hX:T∣p.derivative.eval x - pc (ct (p.derivative.eval x)) := by
   apply PowerSeries.X_dvd_iff.mpr
   simp
 have hlin:T^(n+2)∣(p.derivative.eval x - pc (ct (p.derivative.eval x)))*u:= by
   rw [show n+2=1+(n+1) by omega,pow_add,pow_one]
   exact mul_dvd_mul hX hu
 have hquad:T^(n+2)∣r*u^2 := by
   apply dvd_mul_of_dvd_right
   exact (pow_dvd_pow T (show n+2≤(n+1)*2 by omega)).trans (by
     rw [pow_mul]
     exact pow_dvd_pow_of_dvd hu 2)
 convert dvd_add hquad hlin using 1
 ring
private theorem correction (p:S[X][X]) (x y u v :S) (n:ℕ)
   (hu:T^(n+1)∣u) (hv :T^(n+1)∣v) :
   T^(n+2)∣ev p (x+u) (y+v)-ev p x y -
     pc ((px (map₂ ct p) (ct y)).derivative.eval (ct x))*u -
     pc ((py (map₂ ct p) (ct x)).derivative.eval (ct y))*v := by
 have hct :ct (y+v)=ct y := by
   have hz :T∣v := by
     simpa only [pow_one] using (pow_dvd_pow T (show 1≤n+1 by omega)).trans hv
   simp [PowerSeries.X_dvd_iff.mp hz]
 have a :=remainder (px p (y+v)) x u n hu
 have b:=remainder (py p x) y v n hv
 rw [ev_px,ev_px,← eval_map_apply ct,← derivative_map,px_map,hct] at a
 rw [← eval_map_apply ct,← derivative_map,py_map] at b
 change T^(n+2)∣ev p x (y+v)-ev p x y -
   pc ((py (map₂ ct p) (ct x)).derivative.eval (ct y))*v at b
 convert dvd_add a b using 1
 ring
private theorem lift (p q:S[X][X]) (a b:F)
    (hp:ev (map₂ ct p) a b=0) (hq:ev (map₂ ct q) a b=0)
    (hd: (px (map₂ ct p) b).derivative.eval a*(py (map₂ ct q) a).derivative.eval b -
      (py (map₂ ct p) a).derivative.eval b*(px (map₂ ct q) b).derivative.eval a≠0) :
    ∃ x y :S,ct x=a∧ct y=b∧ev p x y=0∧ev q x y=0:= by
  let A:=(px (map₂ ct p) b).derivative.eval a
  let B:=(py (map₂ ct p) a).derivative.eval b
  let C' := (px (map₂ ct q) b).derivative.eval a
  let D:=(py (map₂ ct q) a).derivative.eval b
  let J:=A*D-B*C'
  have hJ:pc J=pc A*pc D - pc B*pc C' := by simp [J]
  have hi:pc J⁻¹*pc J=1 := by rw [← map_mul,inv_mul_cancel₀ hd,map_one]
  let step (x y :S) :S×S :=
    (pc J⁻¹*(-pc D *ev p x y+pc B*ev q x y),
     pc J⁻¹*(pc C' * ev p x y - pc A*ev q x y))
  have eGJ (n:ℕ) (x y :S) (hx :ct x=a) (hy :ct y=b)
      (hf :T^(n+1)∣ev p x y) (hg:T^(n+1)∣ev q x y) :
      let (u,v) :=step x y
      (T^(n+1)∣u)∧(T^(n+1)∣v) ∧
      (T^(n+2)∣ev p (x+u) (y+v))∧(T^(n+2)∣ev q (x+u) (y+v)) := by
    let u:=(step x y).1
    let v :=(step x y).2
    have hu:T^(n+1)∣u:=dvd_mul_of_dvd_right (dvd_add
      (dvd_mul_of_dvd_right hf _) (dvd_mul_of_dvd_right hg _)) _
    have hv :T^(n+1)∣v :=dvd_mul_of_dvd_right (dvd_sub
      (dvd_mul_of_dvd_right hf _) (dvd_mul_of_dvd_right hg _)) _
    have hlin (f :S) (P Q:F) (h:pc P*u+pc Q*v = -f) :
        ev p (x+u) (y+v) - f - pc P*u - pc Q*v=ev p (x+u) (y+v) := by
      linear_combination -h
    have h₁:pc A*u+pc B*v = -ev p x y := calc
      _=pc J⁻¹*pc J*(-ev p x y) := by dsimp [u,v,step]; rw [hJ]; ring
      _ = _:= by rw [hi,one_mul]
    have h₂:pc C'*u+pc D*v = -ev q x y := calc
      _=pc J⁻¹*pc J*(-ev q x y) := by dsimp [u,v,step]; rw [hJ]; ring
      _ = _:= by rw [hi,one_mul]
    have ep:=correction p x y u v n hu hv
    have eq :=correction q x y u v n hu hv
    rw [hx,hy] at ep eq
    change T^(n+2)∣ev p (x+u) (y+v)-ev p x y - pc A*u - pc B*v at ep
    change T^(n+2)∣ev q (x+u) (y+v)-ev q x y - pc C'*u - pc D*v at eq
    refine ⟨hu,hv,(hlin _ _ _ h₁) ▸ ep,?_⟩
    convert eq using 1
    linear_combination h₂
  let seq :ℕ→S×S:=Nat.rec (pc a,pc b) fun _ (x,y) =>
    (x+(step x y).1,y+(step x y).2)
  have hf (n:ℕ) :ct (seq n).1=a∧ct (seq n).2=b ∧
      T^(n+1)∣ev p (seq n).1 (seq n).2∧T^(n+1)∣ev q (seq n).1 (seq n).2 := by
    induction n with
    | zero =>
      change ct (pc a)=a∧ct (pc b)=b ∧
        T^(0+1)∣ev p (pc a) (pc b)∧T^(0+1)∣ev q (pc a) (pc b)
      simp only [zr8,Nat.zero_add,pow_one,
        zzu,true_and]
      simpa only [ev,← eval_map_apply ct,py_map,zr8] using And.intro hp hq
    | succ n ih =>
      let u:=(step (seq n).1 (seq n).2).1
      let v :=(step (seq n).1 (seq n).2).2
      obtain ⟨hu,hv,hp',hq'⟩:=eGJ n _ _ ih.1 ih.2.1 ih.2.2.1 ih.2.2.2
      have hz {w:S} (hw:T^(n+1)∣w) :ct w=0:= by
        apply PowerSeries.X_dvd_iff.mp
        simpa only [pow_one] using (pow_dvd_pow T (show 1≤n+1 by omega)).trans hw
      change ct ((seq n).1+u)=a∧ct ((seq n).2+v)=b∧_∧_
      exact ⟨by rw [map_add,hz hu,add_zero,ih.1],
        by rw [map_add,hz hv,add_zero,ih.2.1],hp',hq'⟩
  have hs (n:ℕ) :=eGJ n _ _ (hf n).1 (hf n).2.1 (hf n).2.2.1 (hf n).2.2.2
  let I:Ideal S:=Ideal.span {T}
  have congr_dvd {n:ℕ} {x y :S} :
      x ≡ y [SMOD (I^n • ⊤ : Submodule S S)]↔T^n∣x-y := by
    simp only [I,SModEq.sub_mem,smul_eq_mul,Ideal.mul_top,Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  have complete (u:ℕ→S) (hu : ∀ n,T^(n+1)∣u (n+1)-u n) :
      ∃ x,∀ n,T^n∣x-u n:= by
    have hC {m n:ℕ} (hmn:m≤n) :
        u m ≡ u n [SMOD (I^m • ⊤ : Submodule S S)] := by
      induction n,hmn using Nat.le_induction with
      | base=>rfl
      | succ n hmn ih =>
        exact ih.trans (congr_dvd.mpr ((pow_dvd_pow T (by omega)).trans (hu n))).symm
    obtain ⟨x,hx⟩:=(inferInstance :IsPrecomplete I S).prec hC
    exact ⟨x,fun n=>congr_dvd.mp (hx n).symm⟩
  obtain ⟨x,hx⟩:=complete (fun n=>(seq n).1) fun n=> by
    change T^(n+1)∣(seq n).1+(step (seq n).1 (seq n).2).1-(seq n).1
    simpa only [add_sub_cancel_left] using (hs n).1
  obtain ⟨y,hy⟩:=complete (fun n=>(seq n).2) fun n=> by
    change T^(n+1)∣(seq n).2+(step (seq n).1 (seq n).2).2 - (seq n).2
    simpa only [add_sub_cancel_left] using (hs n).2.1
  have hres {x y :S} (h:T^1∣x-y) :ct x=ct y := by
    simpa only [pow_one,zzu,map_sub,sub_eq_zero] using h
  have hzero (f :S[X][X]) (h : ∀ n,T^(n+1)∣ev f (seq n).1 (seq n).2) :
      ev f x y=0:= by
    apply PowerSeries.ext
    intro n
    have t:=ev_diff f (T^(n+1)) _ _ x y (hx (n+1)) (hy (n+1))
    have hdiv :T^(n+1)∣ev f x y := by
      simpa using dvd_add t ((pow_dvd_pow T (Nat.le_succ (n+1))).trans (h (n+1)))
    simpa using PowerSeries.X_pow_dvd_iff.mp hdiv n (Nat.lt_succ_self n)
  exact ⟨x,y,(hres (hx 1)).trans (hf 1).1,(hres (hy 1)).trans (hf 1).2.1,
    hzero p (fun n=>(hf n).2.2.1),hzero q (fun n=>(hf n).2.2.2)⟩
private theorem ev_map₂ {E F:Type} [zrb E] [zrb F] (j:E →+* F)
  (f :E[X][X]) (x y :F) :ev (map₂ j f) x y=atPair j x y f := by
 simp only [ev,py,map₂,coe_mapRingHom,map_map,eval_map,atPair]
 congr 1
 apply RingHom.ext
 intro q
 exact eval_map _ _
private theorem px_derivative {E F:Type} [zrb E] [zrb F] (j:E →+* F)
  (f :E[X][X]) (x y :F) :
  (px (map₂ j f) y).derivative.eval x=atPair j x y (physicalDeriv f) := by
 have he :px (map₂ j f) y=f.sum (fun i c=>c.map j*C y ^i) := by
  rw [px,map₂,coe_mapRingHom,eval_map,eval₂_eq_sum]
  rfl
 simp only [he,sum_def,derivative_sum,← C_pow,derivative_C_mul,derivative_map,
  eval_finsetSum,eval_mul,eval_map,eval_C,atPair,physicalDeriv,eval₂_finsetSum,
  eval₂_monomial,coe_eval₂RingHom,mul_comm]
private theorem py_derivative {E F:Type} [zrb E] [zrb F] (j:E →+* F)
  (f :E[X][X]) (x y :F) :
  (py (map₂ j f) x).derivative.eval y=atPair j x y f.derivative := by
 rw [← ev_map₂ j f.derivative x y]
 simp only [py,ev,map₂,coe_mapRingHom,derivative_map]
theorem lifts :qnSUPza.c2 := by
 intro B _ _ d D W f g hf hg x y hfx hgx hj a b
 let j:=algebraMap B (AlgebraicClosure B)
 let P (f :B[X][X]) (a :Slot d D W→L) : (Germ B)[X][X] :=
   ∑ i,monomial i.val.1.val (monomial i.val.2.val (motion ((f.coeff i.val.1).coeff i.val.2) (a i)))
 have hP (f :B[X][X]) (a :Slot d D W→L) (h:dM f D d W) :
     map₂ zbO (P f a)=map₂ j f := by
   have hct (r :B) (z :L) :zbO (motion r z)=j r := by
     simp [motion,j]
   conv_rhs=>rw [← form_eq f h]
   simp only [P,form,map₂,coe_mapRingHom,zWe,map_monomial,hct]
 have he (f :B[X][X]) (a :Slot d D W→L) (x y :Germ B) :
     ev (P f a) x y =
     aMp (fun i=>motion ((f.coeff i.val.1).coeff i.val.2) (a i)) x y := by
   simp only [P,ev,py,aMp,zWe,map_monomial,eval_finsetSum,
     coe_evalRingHom,eval_monomial]
 obtain ⟨u,v,hu,hv,hp,hq⟩:=lift (P f a) (P g b) x y
   (by simpa only [hP f a hf,ev_map₂] using hfx)
   (by simpa only [hP g b hg,ev_map₂] using hgx) (by
     simpa only [hP f a hf,hP g b hg,px_derivative,py_derivative,jacobian] using hj)
 exact ⟨(u,v),Prod.ext hu hv,(he f a u v) ▸ hp,(he g b u v) ▸ hq⟩
end
end quQ0Dxa
end
