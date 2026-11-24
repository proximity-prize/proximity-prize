import ProximityPrize.SubmissionLower.Zl7U3sa
import ProximityPrize.SubmissionLower.Ztdy5wb
import ProximityPrize.SubmissionLower.Z3aw2hc
import ProximityPrize.SubmissionLower.ZexDIsb
set_option Elab.async false
open _root_ renaming Algebra → zZE, CommRing → za6, Field → zrb, Matrix → z30, Matrix.of_apply → zN9, Polynomial.X → z7y, Polynomial.sum_def → zBJ, PowerSeries → zpm, PowerSeries.X → zWv, PowerSeries.coeff → z2o, PowerSeries.constantCoeff → zbO, RingHom.comp_apply → zQb, RingHom.id → zz4
section
namespace qJai0ob
noncomputable section
open Polynomial Finset TrivSqZeroExt
open qb0hmCe (cLN)
open q1kuFjb (IntSeries mapTwice coeff_liftAt expansion_coeff Ua)
open P5_7_7 (phys)
open cu (L FX)
def homogeneous {A:Type} [za6 A] (d:ℕ) (f :A[X][X]) (x c a b:A) :
    A[X][X] :=
  f.sum fun i g =>
    C (taylor x g) *
      (C (C b*z7y)+C (C a+C (b*c)*z7y)*z7y)^i *
      (C (C b)*z7y)^(d-i)
theorem cUQ {A B:Type} [za6 A] [za6 B] (φ:A →+* B)
  (hφ:Function.Injective φ) (d:ℕ) (f :A[X][X]) (x c a b:A) :
  mapTwice φ (homogeneous d f x c a b) =
    homogeneous d (mapTwice φ f) (φ x) (φ c) (φ a) (φ b) := by
 have h:=Polynomial.map_injective φ hφ
 simp only [homogeneous,zBJ,mapTwice,map_sum,coe_mapRingHom,
  support_map_of_injective (f :=mapRingHom φ) f h,coeff_map,map_add,map_mul,map_pow,
  Polynomial.map_C,Polynomial.map_X,map_taylor]
def evalAt {A B:Type} [za6 A] [za6 B] (φ:A →+* B) (t w:B) :
    A[X][X] →+* B :=
  eval₂RingHom (eval₂RingHom φ t) w
theorem evalAt_map {A B D:Type} [za6 A] [za6 B] [za6 D]
   (φ:A →+* B) (ψ:B →+* D) (t w:D) (f :A[X][X]) :
   evalAt ψ t w (mapTwice φ f)=evalAt (ψ.comp φ) t w f := by
 simp only [evalAt,coe_eval₂RingHom,mapTwice,coe_mapRingHom,eval₂_map]
 congr 1
 apply ringHom_ext
 · intro r
   simp only [zQb,coe_eval₂RingHom,coe_mapRingHom,map_C,eval₂_C]
 · simp only [zQb,coe_eval₂RingHom,coe_mapRingHom,map_X,eval₂_X]
@[simp] theorem evalAt_CC {A B:Type} [za6 A] [za6 B] (φ:A →+* B) (t w:B) (u:A) :
   evalAt φ t w (C (C u))=φ u:= by simp [evalAt]
@[simp] theorem evalAt_C_X_pow {A B:Type} [za6 A] [za6 B] (φ:A →+* B)
   (t w:B) (n:ℕ) :evalAt φ t w (C (z7y^n))=t^n:= by
  simp [evalAt,eval₂_pow]
theorem homogeneous_eval {A B:Type} [za6 A] [za6 B] (φ:A →+* B)
   (t w y :B) (d:ℕ) (f :A[X][X]) (x c a b:A)
   (hd:f.natDegree≤d)
   (h:φ b*t+(φ a+φ b*φ c*t)*w=(φ b*w)*y) :
   evalAt φ t w (homogeneous d f x c a b) =
     (φ b*w)^d*evalAt φ (t+φ x) y f := by
 simp only [homogeneous,evalAt,coe_eval₂RingHom,eval₂_sum,eval₂_mul,eval₂_pow,
   eval₂_add,eval₂_C,eval₂_X,map_mul,taylor_apply,eval₂_comp,h]
 rw [eval₂_eq_sum,zBJ,zBJ,mul_sum]
 refine sum_congr rfl fun i hi => ?_
 have hid :=(le_natDegree_of_mem_supp i hi).trans hd
 have he : (φ b*w)^i*(φ b*w)^(d-i)=(φ b*w)^d:= by
   rw [← pow_add,Nat.add_sub_of_le hid]
 rw [mul_pow,← he]
 simp only [coe_eval₂RingHom]
 ring
def scalar :L →+* FX:=phys.comp C
abbrev Dual:=DualNumber FX
def pair (x y :FX) :Dual:=⟨x,y⟩
@[simp] theorem pair_fst (x y :FX) : (pair x y).fst=x :=rfl
@[simp] theorem pair_snd (x y :FX) : (pair x y).snd=y :=rfl
def seriesJet:IntSeries →+* Dual:= by
  let e :=(LaurentSeries.powerSeriesEquivSubring L).symm
  let u:zpm L →+* Dual :=
    { toFun:= fun f=>pair (scalar (zbO f)) (scalar (z2o 1 f))
      map_zero' := by ext <;> simp [pair]
      map_one' := by ext <;> simp [pair,PowerSeries.coeff_one]
      map_add' := by
        intros
        apply TrivSqZeroExt.ext <;> simp only [fst_add,snd_add,pair_fst,pair_snd,map_add]
      map_mul' := by
        intros
        apply TrivSqZeroExt.ext
        · simp only [fst_mul,pair_fst,map_mul]
        · simp only [DualNumber.snd_mul,pair_fst,pair_snd,PowerSeries.coeff_one_mul,map_add,map_mul]
          ring }
  exact u.comp e.toRingHom
theorem seriesJet_power (g:zpm L) :
   seriesJet ((LaurentSeries.powerSeriesEquivSubring L) g) =
     pair (scalar (zbO g)) (scalar (z2o 1 g)) := by
 let e :=LaurentSeries.powerSeriesEquivSubring L
 change pair (scalar (zbO (e.symm (e g))))
   (scalar (z2o 1 (e.symm (e g))))= _
 simp only [RingEquiv.symm_apply_apply]
theorem seriesJet_fst (a :IntSeries) : (seriesJet a).fst=scalar ((a :LaurentSeries L).coeff 0) := by
 simp only [seriesJet,zQb]
 exact congrArg scalar (q1kuFjb.fWQ a)
theorem seriesJet_snd (a :IntSeries) : (seriesJet a).snd=scalar ((a :LaurentSeries L).coeff 1) := by
 obtain ⟨g,rfl⟩:=(LaurentSeries.powerSeriesEquivSubring L).surjective a
 change scalar (z2o 1 ((LaurentSeries.powerSeriesEquivSubring L).symm
  ((LaurentSeries.powerSeriesEquivSubring L) g)))= _
 rw [RingEquiv.symm_apply_apply,LaurentSeries.powerSeriesEquivSubring_coe_apply]
 exact congrArg scalar ((LaurentSeries.coeff_coe_powerSeries g 1).symm)
private def incl:L →+* Dual:=(inlHom FX FX).comp scalar
private theorem coeffs_jet {E :Type} [zrb E] [zZE L E]
   (a :E →ₐ[L] LaurentSeries L) (f :E[X][X]) (h) :
   mapTwice seriesJet (Ua a f h)=mapTwice incl (cLN a 0 f) +
     C (C (inr (1 :FX) :Dual))*mapTwice incl (cLN a 1 f) := by
 apply Polynomial.ext
 intro i
 apply Polynomial.ext
 intro j
 simp only [mapTwice,coe_mapRingHom,coeff_map,coeff_add,coeff_C_mul,
   expansion_coeff,incl,zQb]
 apply TrivSqZeroExt.ext
 · rw [seriesJet_fst]
   simp [coeff_liftAt]
 · rw [seriesJet_snd]
   simp [coeff_liftAt]
private theorem d2u (f :L[X][X]) (x y :FX) :
   evalAt (zz4 Dual) (inl x) (inl y) (mapTwice incl f) =
     inl (f.eval₂ (eval₂RingHom scalar x) y) := by
 simp only [evalAt,mapTwice,coe_mapRingHom,coe_eval₂RingHom,eval₂_map]
 change f.eval₂ _ _=(inlHom FX FX) (f.eval₂ _ _)
 rw [hom_eval₂]
 congr 1
 apply ringHom_ext
 · intro z
   simp [incl]
 · simp
theorem eval_seriesJet {E :Type} [zrb E] [zZE L E]
    (a :E →ₐ[L] LaurentSeries L) (f :E[X][X]) (h) (x y dy :FX) :
    evalAt seriesJet (inl x) (pair y dy) (Ua a f h) =
      pair ((cLN a 0 f).eval₂ (eval₂RingHom scalar x) y)
        ((cLN a 1 f).eval₂ (eval₂RingHom scalar x) y +
          dy*(cLN a 0 f).derivative.eval₂ (eval₂RingHom scalar x) y) := by
  let a₀:=(mapTwice incl (cLN a 0 f)).map (eval₂RingHom (zz4 Dual) (inl x))
  let a₁:=(mapTwice incl (cLN a 1 f)).map (eval₂RingHom (zz4 Dual) (inl x))
  have hpair :pair y dy=inl y+inr dy :=(inl_fst_add_inr_snd_eq (pair y dy)).symm
  have hm:=evalAt_map seriesJet (zz4 Dual) (inl x) (pair y dy) (Ua a f h)
  rw [RingHom.id_comp] at hm
  rw [← hm,coeffs_jet,map_add,map_mul,evalAt_CC,
    RingHom.id_apply]
  have he (g:Dual[X][X]) :evalAt (zz4 Dual) (inl x) (pair y dy) g =
      (g.map (eval₂RingHom (zz4 Dual) (inl x))).eval (pair y dy) :=
    eval₂_eq_eval_map _
  rw [he,he]
  change a₀.eval (pair y dy)+inr (1 :FX)*a₁.eval (pair y dy)= _
  obtain ⟨b₀,h₀⟩:=exists_mul_sq_add_linear_part_eq_eval_add a₀ (inl y) (inr dy)
  obtain ⟨b₁,h₁⟩:=exists_mul_sq_add_linear_part_eq_eval_add a₁ (inl y) (inr dy)
  have hsq: (inr dy :Dual)^2=0:= by rw [pow_two,inr_mul_inr]
  rw [hsq,mul_zero,zero_add,← hpair] at h₀ h₁
  rw [← h₀,← h₁]
  have hval (g:L[X][X]) : ((mapTwice incl g).map
      (eval₂RingHom (zz4 Dual) (inl x))).eval (inl y) =
        inl (g.eval₂ (eval₂RingHom scalar x) y) := by
    rw [← eval₂_eq_eval_map]
    exact d2u g x y
  have hd:a₀.derivative.eval (inl y) =
      inl ((cLN a 0 f).derivative.eval₂ (eval₂RingHom scalar x) y) := by
    simpa only [a₀,mapTwice,coe_mapRingHom,derivative_map] using
      hval (cLN a 0 f).derivative
  rw [hval,hval,hd]
  apply TrivSqZeroExt.ext <;> simp only [fst_add,snd_add,fst_mul,DualNumber.snd_mul,
    fst_inl,snd_inl,fst_inr,snd_inr,pair_fst,pair_snd] <;> ring
theorem parameter_change (t q r c b b' s u:FX) (hq:q≠0) :
  pair b b' * inl t+(pair (b*r) (b'*r+b*s)+pair b b' * inl c*inl t)*pair (1/q) u =
   (pair b b' * pair (1/q) u)*pair (r+t*(q+c)) (s-t*q^2*u) := by
 apply TrivSqZeroExt.ext <;>
  simp only [fst_add,snd_add,fst_mul,DualNumber.snd_mul,fst_inl,snd_inl,pair_fst,pair_snd] <;>
  field_simp [hq] <;> ring
end
end qJai0ob
end
section
namespace qAW6lac
noncomputable section
open Finset Polynomial
open scoped Classical
open cu (L)
open q8Z6NHc (Slot)
abbrev Index (d s W:ℕ) :=Slot d s W ⊕ (Slot d s W ⊕ Slot (d-1) s (W-s))
abbrev jo (d s W:ℕ) :=MvPolynomial (Index d s W) L
def block {d s W:ℕ} : Index d s W→Fin 3
 | .inl _=>0
 | .inr (.inl _)=>1
 | .inr (.inr _)=>2
def pairDegree (s a d b e :ℕ) :ℕ:=d*b+e*a-d*e*s
def ng (d s W:ℕ) (k :Fin 3) :ℕ :=
 if k=2 then pairDegree s W d W d else pairDegree s W d (W-s) (d-1)
def aMp {F:Type} [za6 F] {d s W:ℕ} (u:Slot d s W→F) (x y :F) :F :=
 ∑ i,u i*x^i.val.2.val*y^i.val.1.val
def Vanishes {d s W:ℕ} (R:jo d s W) :Prop :=
  ∀ {F:Type} [za6 F] [zZE L F] (u:Index d s W→F) (x y :F),
    aMp (fun i=>u (.inl i)) x y=0 →
    aMp (fun i=>u (.inr (.inl i))) x y=0 →
    aMp (fun i=>u (.inr (.inr i))) x y=0 →
    R.eval₂ (algebraMap L F) u=0
structure Eliminant (d s W:ℕ) where
 poly :jo d s W
 nonzero :poly≠0
 aiq:Vanishes poly
 generates : ∀ Q:jo d s W,Vanishes Q→poly∣Q
def actualCoeffs {E :Type} [zrb E] {d s W:ℕ} (f g q:E[X][X]) :Index d s W→E
 | .inl i=>(f.coeff i.val.1).coeff i.val.2
 | .inr (.inl i)=>(g.coeff i.val.1).coeff i.val.2
 | .inr (.inr i)=>(q.coeff i.val.1).coeff i.val.2
def spectral (d s W:ℕ) :Index d s W := .inr (.inr ⟨(0,0),by simp⟩)
def ic {E :Type} [zrb E] [zZE L E] {d s W:ℕ}
    (α:Index d s W→E) (δ:Index d s W→L) (i:Index d s W) :E[X][X] :=
  C (C (α i)+C (algebraMap L E (δ i))*(z7y:E[X])) -
    (if i=spectral d s W then (z7y:E[X][X]) else 0)
def deform {E :Type} [zrb E] [zZE L E] {d s W:ℕ}
    (α:Index d s W→E) (δ:Index d s W→L) (R:jo d s W) :E[X][X] :=
  R.eval₂ (C.comp (C.comp (algebraMap L E))) (ic α δ)
def extract {E :Type} [zrb E] [zZE L E] {d s W:ℕ}
    (α:Index d s W→E) (δ:Index d s W→L) (R:jo d s W) (n:ℕ) :E[X] :=
  (deform α δ R).sum fun i r=>monomial i (r.coeff n)
theorem extract_coeff {E :Type} [zrb E] [zZE L E] {d s W:ℕ}
   (α:Index d s W→E) (δ:Index d s W→L) (R:jo d s W) (n i:ℕ) :
   (extract α δ R n).coeff i=((deform α δ R).coeff i).coeff n:= by
 by_cases hi:i∈(deform α δ R).support
 · simp [extract,zBJ,finsetSum_coeff,coeff_monomial,hi]
 · simp [extract,zBJ,finsetSum_coeff,coeff_monomial,hi,notMem_support_iff.mp hi]
end
end qAW6lac
end
section
namespace qgbTAnb
noncomputable section
open Polynomial Finset
open scoped Classical
private theorem det_order {F:Type*} [zrb F] {N :ℕ}
   (M:z30 (Fin N) (Fin N) (zpm F)) (B:z30 (Fin N) (Fin N) F)
   (V:Finset (Fin N)) (hB:B.det=1)
   (hz : ∀ i∈V,∀ j,(B*PowerSeries.constantCoeff.mapMatrix M) i j=0) :
   zWv^V.card∣M.det:= by
 let A:=(PowerSeries.C:F →+* zpm F).mapMatrix B*M
 have hA:A.det=M.det:= by
   rw [show A= _ from rfl,Matrix.det_mul,← RingHom.map_det,hB,map_one,one_mul]
 have hAB:PowerSeries.constantCoeff.mapMatrix A =
     B*PowerSeries.constantCoeff.mapMatrix M:= by
   change PowerSeries.constantCoeff.mapMatrix (_ *M)= _
   rw [map_mul]
   congr 1
 let v (i:Fin N) :zpm F:=if i∈V then zWv else 1
 have hv (i j:Fin N) :v i∣A i j:= by
   by_cases hi:i∈V
   · simp only [v,hi,ite_true,PowerSeries.X_dvd_iff]
     exact (congrArg (fun M:z30 (Fin N) (Fin N) F=>M i j) hAB).trans (hz i hi j)
   · simp [v,hi]
 choose b hb using hv
 let N' : z30 (Fin N) (Fin N) (zpm F) :=Matrix.of b
 have hfactor :A=Matrix.of (fun i j=>v i*N' i j) :=Matrix.ext hb
 have hprod: (∏ i,v i)=zWv ^V.card:= by
   simp [v]
 rw [← hA,hfactor,Matrix.det_mul_column,hprod]
 exact dvd_mul_right _ _
theorem padded_order {F:Type*} [zrb F] (a b: (zpm F)[X]) {m n k :ℕ}
    (hm:a.natDegree≤ m) (hn:b.natDegree≤n) (hk :k≤ m) (hkn:k≤n)
    {D:F[X]} (hD:D.Monic) (hd:D.natDegree≤ m+n-k)
    (ha :D ∣a.map zbO) (hb:D ∣b.map zbO)
    (hda : (a.map zbO).natDegree≤ m-k)
    (hdb: (b.map zbO).natDegree≤n-k) :
    zWv^(D.natDegree+k)∣resultant a b m n:= by
  let d:=D.natDegree
  let N :=m+n
  let B:z30 (Fin N) (Fin N) F:=Matrix.of fun i j =>
    if (i:ℕ)<d then (((z7y:F[X])^(j:ℕ)) %ₘ D).coeff i else if i=j then 1 else 0
  have hrem (j:Fin N) (hj: (j:ℕ)<d) : (z7y ^(j:ℕ) :F[X]) %ₘ D =z7y ^(j:ℕ) := by
    apply (modByMonic_eq_self_iff hD).mpr
    rw [degree_X_pow,degree_eq_natDegree hD.ne_zero]
    exact Nat.cast_lt.mpr hj
  have htri:B.IsUpperTriangular := by
    intro i j hij
    change j< i at hij
    have hne :i≠j:=ne_of_gt hij
    by_cases hi: (i:ℕ)<d
    · have hj: (j:ℕ)<d:=(show (j:ℕ)< i from hij).trans hi
      simpa [B,hi,hrem j hj,coeff_X_pow,← Fin.ext_iff] using hne
    · simp [B,hi,hne]
  have hdet:B.det=1 := by
    rw [Matrix.det_of_isUpperTriangular htri]
    apply prod_eq_one
    intro i _
    by_cases hi: (i:ℕ)<d
    · simp [B,hi,hrem i hi]
    · simp [B,hi]
  let V:=univ.filter (fun i:Fin N=>(i:ℕ)<d∨N-k≤(i:ℕ))
  have hV:V.card=d+k := by
    let e :Fin N ↪ ℕ:=⟨Fin.val,Fin.val_injective⟩
    have hv :V.map e=range d∪Ico (N-k) N := by
      ext i
      simp only [V,e,mem_map,mem_filter,mem_univ,true_and,mem_union,mem_range,
        mem_Ico,Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨j,hj,rfl⟩
        exact hj.imp id (fun hj=>⟨hj,j.isLt⟩)
      · intro hi
        have hi' : i<N := by dsimp [N,d] at *; omega
        exact ⟨⟨i,hi'⟩,hi.imp id And.left,rfl⟩
    have hdis :Disjoint (range d) (Ico (N-k) N) := by
      refine disjoint_left.mpr fun i hi hj => ?_
      simp only [mem_range,mem_Ico] at hi hj
      exact (not_lt_of_ge (hd.trans hj.1)) hi
    rw [← card_map e,hv,card_union_of_disjoint hdis,card_range,Nat.card_Ico]
    dsimp [N]
    omega
  rw [← hV]
  apply det_order _ B V hdet
  rw [← sylvester_map_map]
  intro i hi j
  have hi' := (mem_filter.mp hi).2
  let f :=a.map zbO
  let g:=b.map zbO
  change f.natDegree≤ m-k at hda
  change g.natDegree≤n-k at hdb
  let S:=degreeLT.basis F N
  let T:=degreeLT.basisProd F m n
  let E :=sylvesterMap f g (natDegree_map_le.trans hm) (natDegree_map_le.trans hn)
  let u:=E (T j)
  have hcoeff (l:Fin N) :sylvester f g m n l j=(u:F[X]).coeff l:= by
    rw [← toMatrix_sylvesterMap' f g (natDegree_map_le.trans hm) (natDegree_map_le.trans hn)]
    exact LinearMap.toMatrix_apply _ _ _ _ _
  by_cases hsmall: (i:ℕ)<d
  · have hu:D ∣(u:F[X]) := by
      change D ∣f*((T j).2 :F[X])+g*((T j).1 :F[X])
      exact (ha.mul_right _).add (hb.mul_right _)
    have hsum: (∑ l:Fin N,(u:F[X]).coeff l•(z7y:F[X])^(l:ℕ))=(u:F[X]) := by
      simpa only [S,Submodule.coe_sum,Submodule.coe_smul,degreeLT.basis_repr,degreeLT.basis_val]
        using congrArg (fun v :degreeLT F N=>(v :F[X])) (S.sum_repr u)
    have hzero :modByMonicHom D (u:F[X])=0:=(modByMonic_eq_zero_iff_dvd hD).mpr hu
    have hs :=congrArg (fun v :F[X]=>(modByMonicHom D v).coeff i) hsum
    change (B*sylvester f g m n) i j=0
    simp only [Matrix.mul_apply,hcoeff,B,zN9,hsmall,ite_true]
    simp only [map_sum,map_smul,finsetSum_coeff,coeff_smul,smul_eq_mul,
      modByMonicHom_apply,hzero,coeff_zero] at hs
    simpa only [mul_comm] using hs
  · have hlarge :N-k≤(i:ℕ) :=hi'.resolve_left hsmall
    have hz :sylvester f g m n i j=0:= by
      refine Fin.addCases ?_ ?_ j
      · intro j
        simp only [sylvester,zN9,Fin.addCases_left]
        split
        · apply coeff_eq_zero_of_natDegree_lt
          have hj:=j.isLt
          dsimp [N] at hlarge
          omega
        · rfl
      · intro j
        simp only [sylvester,zN9,Fin.addCases_right]
        split
        · apply coeff_eq_zero_of_natDegree_lt
          have hj:=j.isLt
          dsimp [N] at hlarge
          omega
        · rfl
    have hrow (l:Fin N) :B i l=(1 :z30 (Fin N) (Fin N) F) i l:= by
      simp [B,hsmall,Matrix.one_apply]
    change (B*sylvester f g m n) i j=0
    simpa [Matrix.mul_apply,hrow,Matrix.one_apply] using hz
end
end qgbTAnb
end
