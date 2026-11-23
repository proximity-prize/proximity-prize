import ProximityPrize.SubmissionLower.ZpdLrZa
set_option Elab.async false
open _root_ renaming AlgHom.comp_apply → zip, Algebra → zZE, CommRing → za6, DFunLike.congr_fun → zmU, Equiv.optionSubtypeNe → zk4, Function.Injective → zq4, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.aeval_X → zTw, MvPolynomial.algHom_ext → zpH, MvPolynomial.optionEquivLeft → zpj, Polynomial → zM1, Polynomial.X → z7y, Polynomial.aevalTower → zZC, Polynomial.aevalTower_C → zhq, Polynomial.aevalTower_X → zR1, RingHom.ker → zdq
section
set_option backward.isDefEq.respectTransparency false
namespace q5vjhGc
noncomputable section
open Finset
open scoped Classical
open cu (L)
open q8Z6NHc (Slot)
open qAW6lac (Index jo aMp Vanishes spectral)
open MvPolynomial (aeval aeval_X)
abbrev z {d s a :ℕ} : Slot d s a :=⟨(0,0),by simp⟩
abbrev z0 {d s W:ℕ} : Index d s W := .inl z
abbrev z1 {d s W:ℕ} : Index d s W := .inr (.inl z)
abbrev z2 {d s W:ℕ} : Index d s W:=spectral d s W
abbrev Free (d s W:ℕ) := {i:Index d s W // i≠z2}
abbrev Target (d s W:ℕ) :=MvPolynomial (Free d s W) L
variable {d s W:ℕ}
def coord (i:Index d s W) :Target d s W :=
 if h:i≠z2 then z9v ⟨i,h⟩ else 0
theorem coord_free (i:Free d s W) :coord i.val=z9v i:= by
 simp [coord,i.property]
def tail {a :ℕ} {F:Type} [za6 F] (u:Slot d s a→F) (x y :F) :F :=
 ∑ i∈univ.erase z,u i*x^i.val.2.val*y^i.val.1.val
def solve {a :ℕ} {F:Type} [za6 F] (u:Slot d s a→F) (x y :F)
    (i:Slot d s a) :F :=
  if i=z then -tail u x y else u i
private theorem eval_eq_tail {a :ℕ} {F:Type} [za6 F]
  (u:Slot d s a→F) (x y :F) :aMp u x y=tail u x y+u z := by
 rw [aMp,tail,← sum_erase_add _ _ (mem_univ z)]
 simp
theorem tail_congr {a :ℕ} {F:Type} [za6 F]
  {u v :Slot d s a→F} (h : ∀ i,i≠z→u i=v i) (x y :F) :
  tail u x y=tail v x y :=
 sum_congr rfl fun i hi=> by rw [h i (mem_erase.mp hi).1]
private theorem eval_solve {a :ℕ} {F:Type} [za6 F]
  (u:Slot d s a→F) (x y :F) :aMp (solve u x y) x y=0:= by
 rw [eval_eq_tail,tail_congr (v :=u) (fun i hi=> by simp [solve,hi])]
 simp [solve]
theorem map_tail {a :ℕ} {F G:Type} [za6 F] [za6 G]
  (ρ:F →+* G) (u:Slot d s a→F) (x y :F) :
  ρ (tail u x y)=tail (fun i=>ρ (u i)) (ρ x) (ρ y) := by
 simp only [tail,map_sum,map_mul,map_pow]
private theorem map_solve_of_root {a :ℕ} {F G:Type} [za6 F] [za6 G]
   (ρ:F →+* G) (u:Slot d s a→F) (v :Slot d s a→G) (x y :F)
   (h : ∀ i,i≠z→ρ (u i)=v i) (hz :aMp v (ρ x) (ρ y)=0)
   (i:Slot d s a) :ρ (solve u x y i)=v i:= by
 by_cases hi:i=z
 · subst i
   rw [solve,ite_eq_left rfl,map_neg,map_tail,tail_congr h]
   rw [eval_eq_tail] at hz
   exact neg_eq_of_add_eq_zero_right hz
 · simpa only [solve,ite_eq_right hi] using h i hi
def values :Index d s W→Target d s W
 | .inl i=>solve (fun j=>coord (.inl j)) (coord z0) (coord z1) i
 | .inr (.inl i)=>solve (fun j=>coord (.inr (.inl j))) (coord z0) (coord z1) i
 | .inr (.inr i)=>solve (fun j=>coord (.inr (.inr j))) (coord z0) (coord z1) i
def incidence (d s W:ℕ) :jo d s W →ₐ[L] Target d s W:=aeval values
theorem values_free (i:Index d s W) (h0:i≠z0) (h1 :i≠z1) (h2 :i≠z2) :
   values i=coord i:= by
 rcases i with i | (i | i)
 · have hi:i≠z := fun he=>h0 (by subst i; rfl)
   simp [values,solve,hi]
 · have hi:i≠z := fun he=>h1 (by subst i; rfl)
   simp [values,solve,hi]
 · have hi:i≠z := fun he=>h2 (by subst i; rfl)
   simp [values,solve,hi]
theorem vanishes_iff (R:jo d s W) :Vanishes R↔incidence d s W R=0:= by
  constructor
  · intro h
    exact h values (coord z0) (coord z1) (eval_solve _ _ _) (eval_solve _ _ _) (eval_solve _ _ _)
  · intro h F _ _ u x y h0 h1 h2
    let ρ:Target d s W →ₐ[L] F:=aeval fun i:Free d s W =>
      if i.val=z0 then x else if i.val=z1 then y else u i.val
    have hx :ρ (coord z0)=x := by simp [ρ,coord,spectral]
    have hy :ρ (coord z1)=y := by simp [ρ,coord,spectral]
    have hv (i:Index d s W) (e0:i≠z0) (e1 :i≠z1) (e2 :i≠z2) :
        ρ (coord i)=u i:= by
      simp [ρ,coord,e0,e1,e2]
    have hh (i:Index d s W) :ρ (values i)=u i:= by
      rw [← hx,← hy] at h0 h1 h2
      rcases i with i | (i | i)
      · exact map_solve_of_root ρ.toRingHom _ _ _ _
          (fun j hj=>hv (.inl j) (by simpa) (by simp) (by simp [spectral])) h0 i
      · exact map_solve_of_root ρ.toRingHom _ _ _ _
          (fun j hj=>hv (.inr (.inl j)) (by simp) (by simpa) (by simp [spectral])) h1 i
      · exact map_solve_of_root ρ.toRingHom _ _ _ _
          (fun j hj=>hv (.inr (.inr j)) (by simp) (by simp) (by simpa [spectral])) h2 i
    have he :ρ.comp (incidence d s W)=aeval u:= by
      apply zpH
      intro i
      simpa only [incidence,zip,aeval_X] using hh i
    change (aeval u:jo d s W →ₐ[L] F) R=0
    rw [← he,zip,h,map_zero]
end
end q5vjhGc
end
section
set_option backward.isDefEq.respectTransparency false
namespace q5vjhGc
noncomputable section
open Finset
open scoped Classical
open cu (L)
open q8Z6NHc (Slot)
open qAW6lac (Index spectral)
open MvPolynomial (aeval aeval_X)
open Polynomial (C)
private def atE {A:Type} [za6 A] [zZE L A] (a :A) :zM1 A →ₐ[L] A :=
 (Polynomial.aeval a).restrictScalars L
private theorem atE_C {A:Type} [za6 A] [zZE L A] (a b:A) :
 atE a (C b)=b:=Polynomial.aeval_C _ _
private theorem atE_X {A:Type} [za6 A] [zZE L A] (a :A) :
 atE a z7y=a :=Polynomial.aeval_X _
private theorem deformation_injective {A:Type} [za6 A] [IsDomain A] [zZE L A]
   (h:A →ₐ[L] zM1 A) (hz : (atE 0).comp h=AlgHom.id L A) :
   zq4 (zZC h z7y) := by
 let H :=zZC h z7y
 have he : (atE 0).comp H=atE 0:= by
   apply Polynomial.algHom_ext'
   · apply AlgHom.ext
     intro a
     change atE 0 (H (C a))=atE 0 (C a)
     rw [show H (C a)=h a from zhq _ _ _,atE_C]
     exact zmU hz a
   · simp [H,atE_X]
 change zq4 H
 rw [injective_iff_map_eq_zero]
 intro P hp
 by_contra hn
 obtain ⟨Q,hP,hQ⟩:=Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hn 0
 simp only [map_zero,sub_zero] at hP hQ
 rw [hP,map_mul,map_pow,show H z7y=z7y from zR1 _ _] at hp
 have hq:=(mul_eq_zero.mp hp).resolve_left (pow_ne_zero _ Polynomial.X_ne_zero)
 have hzero :atE 0 Q=0:= by
   rw [← zmU he Q,zip,hq,map_zero]
 exact hQ (Polynomial.X_dvd_iff.mpr (by
   simpa only [atE,AlgHom.restrictScalars_apply,Polynomial.coe_aeval_eq_eval,Polynomial.coeff_zero_eq_eval_zero]
     using hzero))
variable {d s W:ℕ}
def fixed (i:Index d s W) :Prop :=i=z0∨i=z1
def linearX (hW:1≤W) :Slot d s W :=
 ⟨(0,⟨1,by omega⟩),by simpa⟩
def linearY (hd:1≤d) (hsW:s≤W) :Slot d s W :=
 ⟨(⟨1,by omega⟩,0),by simpa⟩
private theorem tail_single {a :ℕ} {F:Type} [za6 F]
   (j:Slot d s a) (hj:j≠z) (x y :F) :
   tail (fun i=>if i=j then (-1 :F) else 0) x y =
     -(x^j.val.2.val*y^j.val.1.val) := by
 classical
 unfold tail
 rw [sum_eq_single_of_mem j (mem_erase.mpr ⟨hj,mem_univ _⟩)]
 · simp [neg_mul]
 · intro i _ hi
   simp [hi]
private theorem solve_single {a :ℕ} {F:Type} [za6 F]
  (ρ:F →+* F) (u:Slot d s a→F) (x y :F) (hx :ρ x=x) (hy :ρ y=y)
  (j:Slot d s a) (hj:j≠z) (h : ∀ i,i≠z→ρ (u i)=if i=j then -1 else 0) :
  ρ (solve u x y z)=x^j.val.2.val*y^j.val.1.val := by
 rw [solve,ite_eq_left rfl,map_neg,map_tail,hx,hy,tail_congr h,tail_single j hj,neg_neg]
def firstTwo (d s W:ℕ) :Target d s W →ₐ[L] Target d s W :=
 aeval fun j:Free d s W=>values j.val
theorem firstTwo_injective (hd:1≤d) (hs :0<s) (hW:d*s≤W) :
    zq4 (firstTwo d s W) := by
  let A:=Target d s W
  have hsW:s≤W:=(Nat.le_mul_of_pos_left _ (by omega :0<d)).trans hW
  let ix :=linearX (d:=d) (s :=s) (show 1≤W by omega)
  let iy :=linearY hd hsW
  let b:Index d s W→L:= fun i=>if i = .inl ix∨i = .inr (.inl iy) then -1 else 0
  let g:A →ₐ[L] zM1 A:=aeval fun j:Free d s W =>
    if fixed j.val then C (z9v j)
    else (1-Polynomial.X)*C (znf (b j.val))+Polynomial.X*C (z9v j)
  let h:A →ₐ[L] zM1 A:=aeval fun j:Free d s W =>
    if fixed j.val then g (values j.val) else C (z9v j)
  let G:=zZC h (z7y:zM1 A)
  have g_X (j:Free d s W) :=aeval_X (R:=L)
    (fun j:Free d s W=>if fixed j.val then C (z9v j)
      else (1-Polynomial.X)*C (znf (b j.val))+Polynomial.X*C (z9v j)) j
  have g_one : (atE 1).comp g=AlgHom.id L A:= by
    apply zpH
    intro j
    change atE 1 (g (z9v j))=z9v j
    rw [g_X]
    split
    · exact atE_C _ _
    · simp only [map_add,map_mul,map_sub,map_one,atE_X,sub_self,zero_mul,one_mul,
        zero_add]
      exact atE_C _ _
  have g_fixed (i:Index d s W) (hi:i≠z2) (hf :fixed i) :
      g (coord i)=C (coord i) := by
    rw [show coord i=z9v ⟨i,hi⟩ from coord_free ⟨i,hi⟩,g_X,ite_eq_left hf]
  have g_zero (i:Index d s W) (hi:i≠z2) (hf : ¬ fixed i) :
      atE 0 (g (coord i))=znf (b i) := by
    rw [show coord i=z9v ⟨i,hi⟩ from coord_free ⟨i,hi⟩,g_X,ite_eq_right hf]
    simp only [map_add,map_mul,map_sub,map_one,atE_X,sub_zero,zero_mul,one_mul,
      add_zero]
    exact atE_C _ _
  let ρ:A →+* A:=((atE 0).comp g).toRingHom
  have gx :ρ (coord z0)=coord (z0:Index d s W) := by
    change atE 0 (g (coord z0))= _
    rw [g_fixed _ (by simp [spectral]) (Or.inl rfl),atE_C]
  have gy :ρ (coord z1)=coord (z1 :Index d s W) := by
    change atE 0 (g (coord z1))= _
    rw [g_fixed _ (by simp [spectral]) (Or.inr rfl),atE_C]
  have hx :atE 0 (g (values z0))=coord (z0:Index d s W) := by
    have hh:=solve_single ρ (fun j=>coord (.inl j)) _ _ gx gy ix (fun he=> by
      have :=congrArg (fun i:Slot d s W=>i.val.2.val) he
      change 1=0 at this
      omega) (fun i hi=> by
      change atE 0 (g (coord (.inl i)))= _
      rw [g_zero _ (by simp [spectral]) (by
        rintro (he | he)
        · exact hi (Sum.inl.inj he)
        · cases he)]
      by_cases he :i=ix <;> simp [b,he])
    change atE 0 (g (values z0))=coord z0^1*coord z1^0 at hh
    rwa [pow_one,pow_zero,mul_one] at hh
  have hy :atE 0 (g (values z1))=coord (z1 :Index d s W) := by
    have hh:=solve_single ρ (fun j=>coord (.inr (.inl j))) _ _ gx gy iy (fun he=> by
      have :=congrArg (fun i:Slot d s W=>i.val.1.val) he
      change 1=0 at this
      omega) (fun i hi=> by
      change atE 0 (g (coord (.inr (.inl i))))= _
      rw [g_zero _ (by simp [spectral]) (by
        rintro (he | he)
        · cases he
        · exact hi (Sum.inl.inj (Sum.inr.inj he)))]
      by_cases he :i=iy <;> simp [b,he])
    change atE 0 (g (values z1))=coord z0^0*coord z1^1 at hh
    rwa [pow_zero,pow_one,one_mul] at hh
  have h_X (j:Free d s W) :
      h (z9v j)=if fixed j.val then g (values j.val) else C (z9v j) :=
    aeval_X _ _
  have h_zero : (atE 0).comp h=AlgHom.id L A:= by
    apply zpH
    intro j
    change atE 0 (h (z9v j))=z9v j
    rw [h_X]
    by_cases hf :fixed j.val
    · rw [ite_eq_left hf,← coord_free j]
      obtain hj | hj:=hf
      · rw [hj,hx]
      · rw [hj,hy]
    · rw [ite_eq_right hf,atE_C]
  have commute :g.comp (firstTwo d s W)=G.comp g:= by
    have GC (a :A) :G (C a)=h a :=zhq _ _ _
    have GX:G z7y=Polynomial.X:=zR1 _ _
    apply zpH
    intro j
    change g (firstTwo d s W (z9v j))=G (g (z9v j))
    rw [show firstTwo d s W (z9v j)=values j.val from aeval_X _ _,g_X]
    by_cases hf :fixed j.val
    · rw [ite_eq_left hf,GC,h_X,ite_eq_left hf]
    · have hj:=values_free j.val (fun he=>hf (Or.inl he)) (fun he=>hf (Or.inr he)) j.property
      have hC:h (znf (b j.val))=C (znf (b j.val)) :=h.commutes _
      rw [ite_eq_right hf,hj,coord_free,g_X,ite_eq_right hf,map_add,map_mul,map_mul,
        map_sub,map_one,GX,GC,GC,hC,h_X,ite_eq_right hf]
  intro a b hab
  have hg:=congrArg g hab
  change (g.comp (firstTwo d s W)) a=(g.comp (firstTwo d s W)) b at hg
  rw [commute] at hg
  have hgab:=deformation_injective h h_zero hg
  exact calc
    a=(atE 1).comp g a :=(zmU g_one a).symm
    _=(atE 1).comp g b:=congrArg (atE 1) hgab
    _=b:=zmU g_one b
end
end q5vjhGc
end
section
set_option backward.isDefEq.respectTransparency false
namespace q5vjhGc
noncomputable section
open scoped Classical
open cu (L)
open qAW6lac (Index jo)
open Polynomial (C)
private theorem generator {A:Type} [za6 A] [IsDomain A]
    [UniqueFactorizationMonoid A] [zZE L A]
    (f :A →ₐ[L] A) (hf :zq4 f) (t:A)
    (hrel : ∃ P:zM1 A,P≠0∧zZC f t P=0) :
    ∃ P:zM1 A,P≠0∧zZC f t P=0 ∧
      ∀ Q:zM1 A,zZC f t Q=0→P∣Q:= by
  let e :=(zZC f t).toRingHom
  obtain ⟨R,hR,hzero⟩:=hrel
  obtain ⟨fs,hfs,hassoc⟩:=UniqueFactorizationMonoid.exists_prime_factors R hR
  have hm:fs.prod∈zdq e :=
    RingHom.mem_ker.mpr ((hassoc.map e).eq_zero_iff.mpr hzero)
  obtain ⟨P,hP,hPe⟩:=((RingHom.ker_isPrime e).multiset_prod_mem_iff_exists_mem fs).mp hm
  have hp:=(hfs P hP).irreducible
  have hP0:e P=0:=RingHom.mem_ker.mp hPe
  have hprim:P.IsPrimitive := by
    rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
    rintro a ⟨b,hb⟩
    rcases hp.isUnit_or_isUnit hb with hu | hu
    · exact Polynomial.isUnit_C.mp hu
    · have h0:=hP0
      rw [hb,map_mul] at h0
      have ha :f a=0 :=
        (zhq f t a).symm.trans
          ((mul_eq_zero.mp h0).resolve_right (hu.map e).ne_zero)
      have ha0:a=0:=hf (ha.trans (map_zero f).symm)
      exact (hp.ne_zero (by rw [hb,ha0,map_zero,zero_mul])).elim
  let K:=FractionRing A
  let ι:=algebraMap A K
  have hι:zq4 ι:=IsFractionRing.injective A K
  let u:=ι.comp f.toRingHom
  have hu:zq4 u:=hι.comp hf
  let k :K →+* K:=IsFractionRing.lift hu
  let eK:=Polynomial.eval₂RingHom k (ι t)
  have heq :eK.comp (Polynomial.mapRingHom ι)=ι.comp e := by
    apply Polynomial.ringHom_ext'
    · apply RingHom.ext
      intro a
      change eK ((C a).map ι)=ι (e (C a))
      rw [Polynomial.map_C,show e (C a)=f a from zhq f t a]
      change Polynomial.eval₂ k (ι t) (C (ι a))=u a
      rw [Polynomial.eval₂_C]
      exact IsFractionRing.lift_algebraMap (K:=K) hu a
    · change eK (Polynomial.X.map ι)=ι (e z7y)
      rw [Polynomial.map_X]
      simp [eK,e,Polynomial.coe_eval₂RingHom]
  have vanish_map (Q:zM1 A) (hQ:e Q=0) :Q.map ι∈zdq eK:= by
    apply RingHom.mem_ker.mpr
    exact (zmU heq Q).trans (by simp [hQ])
  have hpK:Irreducible (P.map ι) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map (K:=K)).mp hp
  have hspan:Ideal.span {P.map ι} = zdq eK :=
    (PrincipalIdealRing.isMaximal_of_irreducible hpK).eq_of_le (RingHom.ker_ne_top eK)
      ((Ideal.span_singleton_le_iff_mem _).mpr (vanish_map P hP0))
  refine ⟨P,hp.ne_zero,hP0,fun Q hQ => ?_⟩
  apply hprim.dvd_of_fraction_map_dvd_fraction_map (K:=K)
  exact Ideal.mem_span_singleton.mp (show Q.map ι∈Ideal.span {P.map ι} from
    hspan.symm ▸ vanish_map Q hQ)
private theorem relation_exists (d s W:ℕ) :
  ∃ P:jo d s W,P≠0∧incidence d s W P=0:= by
 classical
 have hc:Fintype.card (Index d s W)=Fintype.card (Free d s W)+1 :=
  (Fintype.card_congr (zk4 (z2 :Index d s W))).symm.trans Fintype.card_option
 by_contra h
 have hj:zq4 (incidence d s W) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h0
  exact h ⟨a,h0,ha⟩
 have hd:=trdeg_le_of_injective (incidence d s W) hj
 simp only [jo,Target,MvPolynomial.trdeg_of_isDomain,Cardinal.lift_id,
  Cardinal.mk_fintype,hc,Nat.cast_le] at hd
 omega
theorem proof :qAW6lac.c1 := by
  intro d s W hs _ hd _ hW
  let e :=(MvPolynomial.renameEquiv L (zk4 (z2 :Index d s W)).symm).trans
    (zpj L (Free d s W))
  let f :=firstTwo d s W
  let t:=values (z2 :Index d s W)
  have he :incidence d s W=(zZC f t).comp e.toAlgHom:= by
    apply zpH
    intro i
    obtain ⟨j,rfl⟩:=(zk4 (z2 :Index d s W)).surjective i
    have ee :e (z9v ((zk4 (z2 :Index d s W)) j)) =
        zpj L (Free d s W) (z9v j) := by
      simp only [e,AlgEquiv.trans_apply,MvPolynomial.renameEquiv_apply,
        MvPolynomial.rename_X,Equiv.symm_apply_apply]
    rw [zip,AlgEquiv.coe_toAlgHom,ee,incidence,zTw]
    cases j with
    | none=>rw [MvPolynomial.optionEquivLeft_X_none,Polynomial.aevalTower_X]; rfl
    | some j =>
      rw [MvPolynomial.optionEquivLeft_X_some,zhq]
      exact (zTw (R:=L) (fun j:Free d s W=>values j.val) j).symm
  obtain ⟨R,hR,hR0⟩:=relation_exists d s W
  have hrel : ∃ P:zM1 (Target d s W),P≠0∧zZC f t P=0:= by
    refine ⟨e R,fun h=>hR (e.injective (h.trans (map_zero e).symm)),?_⟩
    simpa only [he,zip,AlgEquiv.coe_toAlgHom] using hR0
  obtain ⟨P,hP,hP0,hp⟩:=generator f (firstTwo_injective (by omega) hs hW) t hrel
  refine ⟨⟨e.symm P,fun h=>hP (e.symm.injective (h.trans (map_zero e.symm).symm)),?_,?_⟩⟩
  · rw [vanishes_iff,he]
    simpa only [zip,AlgEquiv.coe_toAlgHom,AlgEquiv.apply_symm_apply] using hP0
  · intro Q hQ
    rw [vanishes_iff,he] at hQ
    obtain ⟨H,hH⟩:=hp (e Q) hQ
    refine ⟨e.symm H,?_⟩
    apply e.injective
    simpa only [map_mul,AlgEquiv.apply_symm_apply] using hH
end
end q5vjhGc
end
