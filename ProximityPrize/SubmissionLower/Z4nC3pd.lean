import ProximityPrize.SubmissionLower.ZFqQTue
import ProximityPrize.SubmissionLower.ZpdLrZa
set_option Elab.async false
open _root_ renaming Algebra → zZE, CommRing → za6, Polynomial.X → z7y, Polynomial.sum_def → zBJ
section
namespace qfzuawb
noncomputable section
open Polynomial
open scoped Classical
open P5 (K)
open cu (L)
open qb0hmCe (CurveModel)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet)
open qLXroAb (Pencil dx)
open qAW6lac (Index jo spectral)
open qZu9hjc (atPair jacobian)
def map₂ {R T:Type} [CommSemiring R] [CommSemiring T] (j:R →+* T) :
    R[X][X] →+* T[X][X] :=mapRingHom (mapRingHom j)
theorem coeff_map₂ {R T:Type} [CommSemiring R] [CommSemiring T] (j:R →+* T)
  (f :R[X][X]) (i k :ℕ) : ((map₂ j f).coeff i).coeff k=j ((f.coeff i).coeff k) := by
 simp [map₂]
def dM {R:Type} [Semiring R] (f :R[X][X]) (D d W:ℕ) :Prop :=
 ∀ i j,(f.coeff i).coeff j≠0→i≤d∧j+i*D ≤W
def coeffs {R:Type} [Semiring R] {d D W:ℕ}
    (f g Q:R[X][X]) :Index d D W→R
  | .inl i=>(f.coeff i.val.1).coeff i.val.2
  | .inr (.inl i)=>(g.coeff i.val.1).coeff i.val.2
  | .inr (.inr i)=>(Q.coeff i.val.1).coeff i.val.2
theorem coeffs_map {R T:Type} [CommSemiring R] [CommSemiring T] {d D W:ℕ}
  (j:R →+* T) (f g Q:R[X][X]) :
  (fun i:Index d D W=>j (coeffs f g Q i)) =
    coeffs (map₂ j f) (map₂ j g) (map₂ j Q) := by
 funext i
 rcases i with i | (i | i) <;> simp [coeffs,coeff_map₂]
def KT {E :Type} [Field E] (f :E[X][X]) :Fin 4→E[X][X] :=
  ![f.derivative,Polynomial.C z7y*f.derivative,
    z7y*f.derivative,-(dx f)]
def P5 {E :Type} [Field E] [zZE L E] (f :E[X][X]) (a :Fin 4→L) :
    E[X][X] := ∑ i,C (C (algebraMap L E (a i)))*KT f i
variable {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
 {F:Sheet Cq z S}
def pencilForm (A:Pencil F) :Cq.E[X][X][X] :=
  map₂ C (P5 F.f A.b) -
    C (C (z7y:Cq.E[X]))*map₂ C (P5 F.f A.a)
theorem pencil_coeff (A:Pencil F) (i j:ℕ) :
    ((pencilForm A).coeff i).coeff j =
      C (((P5 F.f A.b).coeff i).coeff j) -
        z7y*C (((P5 F.f A.a).coeff i).coeff j) := by
  simp only [pencilForm,coeff_sub,coeff_C_mul,coeff_map₂]
structure SimpleFiber {B:Type} [Field B] (f g Q:B[X][X]) (N :B[X]) where
 size :ℕ
 point :Fin size→AlgebraicClosure B×AlgebraicClosure B
 distinct :Function.Injective point
 f_zero : ∀ i,atPair (algebraMap B _) (point i).1 (point i).2 f=0
 g_zero : ∀ i,atPair (algebraMap B _) (point i).1 (point i).2 g=0
 simple : ∀ i,jacobian (algebraMap B _) (point i).1 (point i).2 f g≠0
 product :N.map (algebraMap B (AlgebraicClosure B)) =
  ∏ i,((z7y: (AlgebraicClosure B)[X]) -
    C (atPair (algebraMap B _) (point i).1 (point i).2 Q))
def ic {R:Type} [za6 R] [zZE L R] {d D W:ℕ}
    (α:Index d D W→R) (δ:Index d D W→L) (i:Index d D W) :R[X][X] :=
  C (C (α i)+C (algebraMap L R (δ i))*(z7y:R[X])) -
    (if i=spectral d D W then (z7y:R[X][X]) else 0)
def deform {R:Type} [za6 R] [zZE L R] {d D W:ℕ}
    (α:Index d D W→R) (δ:Index d D W→L) (P:jo d D W) :R[X][X] :=
  P.eval₂ (C.comp (C.comp (algebraMap L R))) (ic α δ)
def extract {R:Type} [za6 R] [zZE L R] {d D W:ℕ}
    (α:Index d D W→R) (δ:Index d D W→L) (P:jo d D W) (n:ℕ) :R[X] :=
  (deform α δ P).sum fun i r=>monomial i (r.coeff n)
theorem extract_coeff {R:Type} [za6 R] [zZE L R] {d D W:ℕ}
   (α:Index d D W→R) (δ:Index d D W→L) (P:jo d D W) (n i:ℕ) :
   (extract α δ P n).coeff i=((deform α δ P).coeff i).coeff n:= by
 by_cases hi:i∈(deform α δ P).support
 · simp [extract,zBJ,finsetSum_coeff,coeff_monomial,hi]
 · simp [extract,zBJ,finsetSum_coeff,coeff_monomial,hi,notMem_support_iff.mp hi]
theorem extract_map {R T:Type} [za6 R] [za6 T] [zZE L R] [zZE L T]
   {d D W:ℕ} (j:R →ₐ[L] T) (α:Index d D W→R) (δ:Index d D W→L)
   (P:jo d D W) (n:ℕ) :
   (extract α δ P n).map j.toRingHom=extract (fun i=>j (α i)) δ P n:= by
 have h:map₂ j.toRingHom (deform α δ P)=deform (fun i=>j (α i)) δ P:= by
   rw [deform,MvPolynomial.hom_eval₂,deform]
   congr 1
   · ext r
     simp [map₂]
   · funext i
     by_cases hi:i=spectral d D W <;> simp [ic,hi,map₂]
 ext i
 rw [coeff_map,extract_coeff,extract_coeff,← h,coeff_map₂]
end
end qfzuawb
end
section
set_option backward.isDefEq.respectTransparency false
namespace qfzuawb
noncomputable section
open Polynomial Finset
open scoped Classical WithZero
open P5 (K)
open cu (L)
open qb0hmCe (CurveModel)
open qFD8jve (aFA)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet)
open qLXroAb (Pencil dx bw)
open qAW6lac (Index jo ng block)
open E7 (CurvePlace)
open private sum_coeff from ProximityPrize.SubmissionLower.Z62SyBc
open private cast_le_one from ProximityPrize.SubmissionLower.Z62SyBc
open private efc adG cTA b4s bHf aMX from ProximityPrize.SubmissionLower.Y
open private gauss₂ coeff_le_gauss₂ gauss₂_bound gauss₂_C from ProximityPrize.SubmissionLower.ZhEC96c
open private val_const val_X val_outer from ProximityPrize.SubmissionLower.ZTNQi7d
open private ags from ProximityPrize.SubmissionLower.ZpdLrZa
variable {E :Type} [Field E]
theorem fits_map₂ {R T:Type} [CommSemiring R] [CommSemiring T] (j:R →+* T)
  {f :R[X][X]} {D d W:ℕ} (h:dM f D d W) :dM (map₂ j f) D d W:= by
 intro i k hk
 apply h i k
 intro hz
 exact hk (by simp [coeff_map₂,hz])
private theorem coeff_dy (f :E[X][X]) (i j:ℕ) :
  (f.derivative.coeff i).coeff j=(f.coeff (i+1)).coeff j*((i+1 :ℕ) :E) := by
 rw [coeff_derivative,← Nat.cast_succ,← C_eq_natCast,coeff_mul_C]
private theorem bXI (f :E[X][X]) (i j:ℕ) :
  ((dx f).coeff i).coeff j=(f.coeff i).coeff (j+1)*((j+1 :ℕ) :E) := by
 rw [dx,sum_coeff derivative derivative_zero,coeff_derivative,Nat.cast_succ]
theorem dy_fits {f :E[X][X]} {D d W:ℕ} (h:dM f D d W) :
  dM f.derivative D (d-1) (W-D) := by
 intro i j hne
 rw [coeff_dy] at hne
 obtain ⟨hi,hw⟩:=h (i+1) j (mul_ne_zero_iff.mp hne).1
 rw [Nat.add_mul,one_mul] at hw
 omega
private theorem bH1 {f :E[X][X]} {D d W:ℕ} (hD:0<D) (h:dM f D d W)
    (k :Fin 4) :dM (KT f k) D d W:= by
  have hy :=dy_fits h
  intro i j hne
  fin_cases k
  · obtain ⟨hi,hj⟩:=hy i j hne
    exact ⟨by omega,by omega⟩
  · change ((C (z7y:E[X])*f.derivative).coeff i).coeff j≠0 at hne
    rw [coeff_C_mul] at hne
    cases j with
    | zero=>exact (hne (coeff_X_mul_zero _)).elim
    | succ j =>
      rw [coeff_X_mul] at hne
      obtain ⟨hi,hj⟩:=hy i j hne
      have hDW:D ≤W:= by
        have hf : (f.coeff (i+1)).coeff j≠0:= by
          rw [coeff_dy] at hne
          exact (mul_ne_zero_iff.mp hne).1
        have hw:=(h _ _ hf).2
        rw [Nat.add_mul,one_mul] at hw
        omega
      exact ⟨by omega,by omega⟩
  · change (((z7y:E[X][X])*f.derivative).coeff i).coeff j≠0 at hne
    cases i with
    | zero=>exact (hne (by rw [coeff_X_mul_zero,coeff_zero])).elim
    | succ i =>
      rw [coeff_X_mul,coeff_dy] at hne
      obtain ⟨hi,hj⟩:=h (i+1) j (mul_ne_zero_iff.mp hne).1
      exact ⟨hi,hj⟩
  · change ((-(dx f)).coeff i).coeff j≠0 at hne
    rw [coeff_neg,coeff_neg,neg_ne_zero,bXI] at hne
    obtain ⟨hi,hj⟩:=h i (j+1) (mul_ne_zero_iff.mp hne).1
    exact ⟨hi,by omega⟩
variable [zZE L E]
private theorem linear_fits {f :E[X][X]} {D d W:ℕ} (hD:0<D) (h:dM f D d W)
  (a :Fin 4→L) :dM (P5 f a) D d W:= by
 intro i j hn
 by_contra hc
 apply hn
 simp only [P5,finsetSum_coeff,coeff_C_mul]
 apply sum_eq_zero
 intro k _
 rw [show ((KT f k).coeff i).coeff j=0 from
  not_not.mp (fun hne=>hc (bH1 hD h k i j hne)),mul_zero]
variable {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
 {F:Sheet Cq z S}
theorem pencil_fits (A:Pencil F) {D W:ℕ} (hD:0<D) (h:dM F.f D F.d W) :
  dM (pencilForm A) D F.d W:= by
 intro i j hn
 rw [pencil_coeff] at hn
 by_contra hc
 have hz (c:Fin 4→L) : ((P5 F.f c).coeff i).coeff j=0 :=
  not_not.mp fun hg=>hc (linear_fits hD h c i j hg)
 exact hn (by simp [hz])
private theorem cHQ (v :CurvePlace L E) (a :L) :v.value (algebraMap L E a)≤1 := by
 by_cases ha :a=0
 · simp [ha]
 exact (v.on_constants a ha).le
omit [zZE L E] in
theorem dy_bound (v :Valuation E ℤᵐ⁰) {f :E[X][X]} {b:ℕ} (h:aFA v f b) :
  aFA v f.derivative b:= by
 intro i j
 rw [coeff_dy,map_mul]
 exact (mul_le_mul' (h _ _) (cast_le_one (v :=v) _)).trans_eq (mul_one _)
private theorem linear_bound (v :CurvePlace L E) {f :E[X][X]} {b:ℕ}
   (h:aFA v.value f b) (a :Fin 4→L) :
   aFA v.value (P5 f a) b:= by
 let w:=gauss₂ v.value
 have hy :w f.derivative≤WithZero.exp (b:ℤ) :=gauss₂_bound v.value _ (dy_bound _ h)
 have hx :w (dx f)≤WithZero.exp (b:ℤ) :=gauss₂_bound v.value _ fun i j=> by
   rw [bXI,map_mul]
   exact (mul_le_mul' (h _ _) (cast_le_one (v :=v.value) _)).trans_eq (mul_one _)
 have hj (i:Fin 4) :w (KT f i)≤WithZero.exp (b:ℤ) := by
   fin_cases i
   · exact hy
   · change w (C (z7y:E[X])*f.derivative)≤_
     rwa [map_mul,val_const,val_X,one_mul]
   · change w (z7y*f.derivative)≤_
     rwa [map_mul,val_outer,one_mul]
   · change w (-(dx f))≤_
     rwa [Valuation.map_neg]
 intro i j
 apply (coeff_le_gauss₂ v.value _ i j).trans
 apply w.map_sum_le
 intro k _
 rw [map_mul,gauss₂_C,← one_mul (WithZero.exp _)]
 exact mul_le_mul' (cHQ v _) (hj k)
theorem pencil_bound (v :CurvePlace L Cq.E) (A:Pencil F) {b:ℕ}
   (h:aFA v.value F.f b) (i j:ℕ) :
   efc v.value (((pencilForm A).coeff i).coeff j)≤WithZero.exp (b:ℤ) := by
 let w:=efc v.value
 rw [pencil_coeff,sub_eq_add_neg]
 apply w.map_add_le
 · change adG v.value (C _)≤_
   rw [cTA]
   exact linear_bound v h _ _ _
 · rw [Valuation.map_neg,map_mul]
   change adG v.value z7y*adG v.value (C _)≤_
   rw [val_X,one_mul,cTA]
   exact linear_bound v h _ _ _
theorem bGx {d D W:ℕ} (hd:2≤d) (hW:d*D ≤W)
  (P:jo d D W)
  (h : ∀ m∈P.support,∀ k :Fin 3,
    m.sum (fun i n=>if block i=k then n else 0)≤ng d D W k) :
  P.totalDegree≤bw D d W:= by
 simpa only [qZV9OWb.rate,bw,pow_two,mul_assoc] using ags hd hW P h
private def gauss₃ (v :Valuation E ℤᵐ⁰) :Valuation E[X][X][X] ℤᵐ⁰ :=
 (gauss₂ (b4s v)).comap (map₂ (algebraMap E[X] (RatFunc E)))
omit [zZE L E] in
private theorem coeff_le_gauss₃ (v :Valuation E ℤᵐ⁰) (P:E[X][X][X]) (i n:ℕ) :
  adG v ((P.coeff i).coeff n)≤gauss₃ v P:= by
 have h:=coeff_le_gauss₂ (b4s v) (map₂ (algebraMap E[X] (RatFunc E)) P) i n
 rw [coeff_map₂,bHf] at h
 exact h
theorem extract_bound {d D W m b:ℕ} (v :CurvePlace L E) (α:Index d D W→E[X])
    (δ:Index d D W→L) (hα : ∀ k,adG v.value (α k)≤WithZero.exp (b:ℤ))
    (P:jo d D W) (hP:P.totalDegree≤ m) (n:ℕ) :
    aFA v.value (extract α δ P n) (m*b) := by
  let w:=gauss₃ v.value
  let B:=WithZero.exp (b:ℤ)
  let u:=b4s v.value
  have hC (r :E[X]) :w (C (C r))=adG v.value r := by
    change gauss₂ u (map₂ _ (C (C r)))= _
    rw [show map₂ (algebraMap E[X] (RatFunc E)) (C (C r))=C (C (algebraMap E[X] (RatFunc E) r))
      by simp [map₂],gauss₂_C,bHf]
  have hL (r :L) :w (C (C (algebraMap L E[X] r)))≤1 := by
    rw [hC]
    change adG v.value (C (algebraMap L E r))≤_
    rw [cTA]
    exact cHQ v r
  have hε:w (C (z7y:E[X][X]))=1 := by
    change gauss₂ u (map₂ _ (C z7y))= _
    rw [show map₂ (algebraMap E[X] (RatFunc E)) (C z7y)=C z7y
      by simp [map₂],val_const,val_X]
  have hT:w z7y=1 := by
    change gauss₂ u (map₂ _ z7y)= _
    rw [show map₂ (algebraMap E[X] (RatFunc E)) z7y=z7y
      by simp [map₂],val_outer]
  have hB:1≤B:=WithZero.exp_le_exp.mpr (Int.natCast_nonneg b)
  have hvar (k :Index d D W) :w (ic α δ k)≤B:= by
    unfold ic
    rw [sub_eq_add_neg]
    apply w.map_add_le
    · rw [map_add,map_mul]
      apply w.map_add_le
      · rw [hC]
        exact hα k
      · rw [map_mul,hε,mul_one]
        exact (hL _).trans hB
    · rw [Valuation.map_neg]
      split
      · rwa [hT]
      · simp
  intro i j
  rw [extract_coeff]
  refine ((aMX v.value _ j).trans (coeff_le_gauss₃ v.value _ i n)).trans ?_
  change w (deform α δ P)≤_
  rw [deform,MvPolynomial.eval₂_eq]
  apply w.map_sum_le
  intro t ht
  rw [map_mul,map_prod]
  calc
    _≤1 * ∏ k∈t.support,B^t k :=
      mul_le_mul' (hL _) (prod_le_prod fun k _=> by rw [map_pow]; exact pow_le_pow_left' (hvar k) _)
    _=WithZero.exp ((t.sum (fun _ e=>e)*b:ℕ) :ℤ) := by
      rw [one_mul,prod_pow_eq_pow_sum]
      dsimp [B]
      simp [Finsupp.sum]
    _≤_:=WithZero.exp_le_exp.mpr
      (Int.ofNat_le.mpr (Nat.mul_le_mul_right b ((MvPolynomial.le_totalDegree ht).trans hP)))
omit [zZE L E] in
theorem pow_bound (v :Valuation E ℤᵐ⁰) {R:E[X][X]} {b:ℕ}
  (h:aFA v R b) (D:ℕ) :aFA v (R^D) (D*b) := by
 intro i j
 apply (coeff_le_gauss₂ v _ i j).trans
 rw [map_pow]
 simpa [mul_comm] using pow_le_pow_left' (gauss₂_bound v _ h) D
end
end qfzuawb
end
section
set_option backward.isDefEq.respectTransparency false
namespace qfzuawb
noncomputable section
open Finset Polynomial
open scoped Classical WithZero
open P5 (K p)
open cu (L)
open qb0hmCe (CurveModel)

open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet)
open qLXroAb (tu Pencil)
open qAW6lac (Index Eliminant ng block)
open private cTA from ProximityPrize.SubmissionLower.Y
def c1 :Prop :=
  ∀ d D W:ℕ,0<D→D <p→3≤d→d*D ≤W →
    ∃ P:Eliminant d D W,∀ m∈P.poly.support,∀ k :Fin 3,
      m.sum (fun i n=>if block i=k then n else 0)≤ng d D W k
def c2 :Prop :=
  ∀ {B:Type} [Field B] [zZE L B] (d D W:ℕ),0<D→3≤d→d*D ≤W →
    ∀ (f g Q:B[X][X]) (N :B[X]),dM f D d W→dM g D d W →
    dM Q D (d-1) (W-D)→SimpleFiber f g Q N → ∀ P:Eliminant d D W,
    ∃ (δ:Index d D W→L) (n:ℕ),
      let R:=extract (coeffs f g Q) δ P.poly n
      R≠0∧N∣R
def c3:Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
    {F:Sheet Cq z S} (A:Pencil F),
    let j:=algebraMap Cq.E[X] (tu Cq.E)
    Nonempty (SimpleFiber (map₂ j (map₂ C F.f)) (map₂ j (pencilForm A))
      (map₂ j (map₂ C F.f.derivative)) A.polarPoly)
theorem of_children (ek :c1) (specialize :c2) (fiber :c3) :
   qLXroAb.c5:= by
 intro q Cq z S F A D W hd hD hp hW hw
 let E :=Cq.E
 let j:E[X] →ₐ[L] tu E :=IsScalarTower.toAlgHom L E[X] (tu E)
 let f :=map₂ (C:E →+* E[X]) F.f
 let g:=pencilForm A
 let Q:=map₂ (C:E →+* E[X]) F.f.derivative
 have hf :dM F.f D F.d W:= by
   intro i k hk
   have hi:F.f.coeff i≠0:= fun hz=>hk (by simp [hz])
   exact ⟨le_natDegree_of_ne_zero hi,Nat.add_le_add_right (le_natDegree_of_ne_zero hk) _
     |>.trans (hw i hi)⟩
 obtain ⟨P,hP⟩:=ek F.d D W hD hp hd hW
 obtain ⟨T⟩:=fiber A
 obtain ⟨δ,n,hn,hdiv⟩:=specialize F.d D W hD hd hW
   (map₂ j.toRingHom f) (map₂ j.toRingHom g) (map₂ j.toRingHom Q) A.polarPoly
   (fits_map₂ _ (fits_map₂ _ hf)) (fits_map₂ _ (pencil_fits A hD hf))
   (fits_map₂ _ (fits_map₂ _ (dy_fits hf))) T P
 let R:=extract (coeffs f g Q) δ P.poly n
 have he :R.map j.toRingHom=extract
     (coeffs (map₂ j.toRingHom f) (map₂ j.toRingHom g) (map₂ j.toRingHom Q)) δ P.poly n:= by
   dsimp only [R]
   rw [extract_map]
   exact congrArg (fun α=>extract α δ P.poly n) (coeffs_map j.toRingHom f g Q)
 have hR:R≠0:= fun hz=>hn (by rw [← he,hz,Polynomial.map_zero])
 refine ⟨R^D,pow_ne_zero _ hR,?_,?_⟩
 · intro v
   rw [Nat.mul_assoc]
   apply pow_bound v.value
   apply extract_bound v _ δ ?_ _ (bGx (by omega) hW P.poly hP)
   intro k
   have hb:=qrezXJe.sheet_bound v.value F.f
   rcases k with k | (k | k)
   · simp only [coeffs,f,coeff_map₂]
     exact (cTA v.value _).trans_le (hb _ _)
   · exact pencil_bound v A hb _ _
   · simp only [coeffs,Q,coeff_map₂]
     exact (cTA v.value _).trans_le (dy_bound v.value hb _ _)
 · change A.polarPoly ^D ∣(R^D).map j.toRingHom
   rw [Polynomial.map_pow,he]
   exact pow_dvd_pow_of_dvd hdiv D
end
end qfzuawb
end
