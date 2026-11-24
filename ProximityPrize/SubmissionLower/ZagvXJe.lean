import ProximityPrize.SubmissionLower.ZL8vffb
set_option Elab.async false
open _root_ renaming IsFractionRing.injective → zxb, MvPolynomial.eval → zY9, MvPolynomial.map → zDK, Nat.le_of_lt_succ → zeh, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Polynomial.map_mul → zNl, Submodule → zpI
set_option autoImplicit true
section
namespace q4Pefpa
noncomputable section
open Polynomial
open cu (L)
open qQ9yWTb (Raw)
abbrev UR :=MvPolynomial (Fin 2) L[X]
abbrev amm:L[X] →+* Raw:=Polynomial.C.comp MvPolynomial.C
def sk (z t:ℕ) (f :Raw) :Prop :=
 ∀ (i:Fin 2) (j:ℕ),(f.coeff j).degreeOf i≤ if i=0 then z else t
def Padded (a b E M:ℕ) (f :Raw) :Prop :=
  f.natDegree≤E ∧ ∀ j m,(f.coeff j).coeff m≠0 →
    ((f.coeff j).coeff m).natDegree+E*a+j*(b-a)<M
def load (a b:ℕ) (f :Raw) :ℕ :=
  f.support.sup fun i=>(f.coeff i).support.sup fun m =>
    ((f.coeff i).coeff m).natDegree+f.natDegree*a+i*(b-a)
def stock (z t:ℕ) :ℕ:=(z+1)*(t+1)
def j3 (l d:ℕ) :ℕ:=l*d*(d+1)/2
def inputSize (g M z t:ℕ) :ℕ:=(g+1)*stock z t*M
end
end q4Pefpa
end
section
namespace q4Pefpa
noncomputable section
open Polynomial Finset
open P5 (K p)
open cu (L FX qD jz)
open qQ9yWTb (Raw embed)
open P5_7_7 (phys)
private def dcQ (z :K) (n:ℕ) :Fin 2→L :=
 ![algebraMap K L z,(algebraMap K L z)^n]
private def spec (z :K) :UR →+* L[X] :=
 zY9 (C ∘ dcQ z p)
private def BA (E :ℕ) (z :K) (P Q:L[X]) (F:Raw) :L[X] :=
 ∑ j∈range (E+1),spec z (F.coeff j)*P^j*Q^(E-j)
private theorem map_seedPoint (z :K) (n:ℕ) :
   phys ∘ (C ∘ dcQ z n) = ![jz z,(jz z)^n] := by
 funext i
 fin_cases i
 · rfl
 · exact map_pow (phys.comp (C:L →+* L[X])) (algebraMap K L z) n
private theorem map_spec (z :K) (r :UR) :
   phys (spec z r)=qD z (zDK phys r) :=
 (MvPolynomial.map_eval phys (C ∘ dcQ z p) r).trans
   (congrArg (fun t=>zY9 t (zDK phys r)) (map_seedPoint z p))
private theorem phys_ne_zero {Q:L[X]} (hQ:Q≠0) :phys Q≠0:= by
 simpa only [map_zero] using
  (show phys Q≠phys 0 from (zxb L[X] FX).ne hQ)
private theorem cZl {E :ℕ} (z :K) (P Q:L[X]) {F:Raw}
   (hF:F.natDegree≤E) (hQ:Q≠0) :
   phys (BA E z P Q F) =
     (embed F).eval₂ (qD z) (phys P/phys Q)*(phys Q)^E := by
 have hQ' := phys_ne_zero hQ
 have hdeg: (embed F).natDegree<E+1 :=(natDegree_map_le.trans hF).trans_lt (Nat.lt_succ_self E)
 rw [Polynomial.eval₂_eq_sum_range' _ hdeg]
 simp only [BA,map_sum,map_mul,map_pow,sum_mul]
 apply sum_congr rfl
 intro j hj
 have hjE :j≤E :=zeh (mem_range.mp hj)
 have hp: (phys Q)^E=(phys Q)^j*(phys Q)^(E-j) := by
   rw [← pow_add,Nat.add_sub_of_le hjE]
 have hdiv : (phys P/phys Q)^j*(phys Q)^E=(phys P)^j*(phys Q)^(E-j) := by
   rw [div_pow,hp,← mul_assoc,div_mul_cancel₀ _ (pow_ne_zero _ hQ')]
 simp only [embed,coe_mapRingHom,coeff_map,map_spec,mul_assoc,hdiv]
 rfl
private theorem dLK {a b E M:ℕ} {P Q:L[X]} {G:Raw}
  (hab:a≤b) (hP:P.natDegree≤b) (hQ:Q.natDegree≤a)
  (hG:Padded a b E M G) (hM:0<M) (z :K) :
  (BA E z P Q G).natDegree<M:= by
 classical
 apply Nat.lt_of_le_pred hM
 refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
 have hjE :j≤E :=zeh (mem_range.mp hj)
 change ((zY9 (C ∘ dcQ z p) (G.coeff j))*P^j*Q^(E-j)).natDegree≤M-1
 rw [MvPolynomial.eval_eq,sum_mul,sum_mul]
 refine natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
 rw [show (∏ i∈m.support,(C ∘ dcQ z p) i^m i) =
  C (∏ i∈m.support,dcQ z p i^m i) by simp only [Function.comp_apply,map_prod,map_pow]]
 have hp: (P^j).natDegree≤j*b:=natDegree_pow_le.trans (zBI _ hP)
 have hq: (Q^(E-j)).natDegree≤(E-j)*a :=natDegree_pow_le.trans (zBI _ hQ)
 have h:=hG.2 j m (MvPolynomial.mem_support_iff.mp hm)
 have he :E*a+j*(b-a)=j*b+(E-j)*a := by
  rw [Nat.mul_sub_left_distrib,Nat.sub_mul]
  have hl:=zBI j hab
  have hr :=ztf a hjE
  omega
 rw [add_assoc,he] at h
 exact (natDegree_mul_le_of_le
  (natDegree_mul_le_of_le (natDegree_mul_C_le _ _) hp) hq).trans (by omega)
theorem dhP {a b E M:ℕ} {d P Q:L[X]} {z :K} {A G B:Raw}
   (hab:a≤b) (hd:d.natDegree=M) (hQ:Q≠0) (hp:P.natDegree≤b)
   (hq:Q.natDegree≤a) (hG:Padded a b E M G) (hB:B.natDegree≤E)
   (he :A=G+amm d*B)
   (hroot : (embed A).eval₂ (qD z) (phys P/phys Q)=0) :
   (embed G).eval₂ (qD z) (phys P/phys Q)=0:= by
 by_cases hg:G=0
 · simp [hg]
 have hM:0<M:= by
   by_contra! hn
   apply hg
   apply Polynomial.ext
   intro j
   apply MvPolynomial.ext
   intro m
   simp only [coeff_zero,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]
   by_contra hc
   have hh:=hG.2 j m hc
   omega
 have hA:A.natDegree≤E := by
   rw [he]
   exact natDegree_add_le_of_degree_le hG.1 ((natDegree_C_mul_le _ _).trans hB)
 have hAc:BA E z P Q A=0:= by
   apply zxb L[X] FX
   change phys (BA E z P Q A)=phys 0
   rw [cZl z P Q hA hQ,hroot,zero_mul,map_zero]
 have hcong:BA E z P Q A=BA E z P Q G+d*BA E z P Q B:= by
   rw [he]
   simp only [BA,amm,RingHom.comp_apply,coeff_add,coeff_C_mul,map_add,map_mul,
     spec,MvPolynomial.eval_C,add_mul,sum_add_distrib,mul_sum,mul_assoc]
 have hG0:BA E z P Q G=0:= by
   by_contra hn
   have hdiv :d∣BA E z P Q G:=⟨-BA E z P Q B,by
     rw [mul_neg]
     exact eq_neg_of_add_eq_zero_left (hcong.symm.trans hAc)⟩
   have hle :=natDegree_le_of_dvd hdiv hn
   exact (dLK hab hp hq hG hM z).not_ge (hd ▸ hle)
 have h:=cZl z P Q hG.1 hQ
 rw [hG0,map_zero,eq_comm,mul_eq_zero] at h
 exact h.resolve_right (pow_ne_zero _ (phys_ne_zero hQ))
end
end q4Pefpa
end
section
open Polynomial renaming natDegree_map_eq_of_injective→qz0
open IsFractionRing renaming injective→qz1
set_option maxHeartbeats 800000
namespace q4Pefpa
noncomputable section
open Polynomial
open P5 (K)

open qQ9yWTb (Raw embed height Moving)
open cu (L FX qD)
def c1 :Prop :=
  ∀ a b e g M z t h:ℕ,a≤b→(e+g)*(a+b)<M →
    ∀ F:Raw,F≠0→F.natDegree≤e→sk h h F →
    ∃ d:L[X],d.natDegree=M ∧
      ∃ V:zpI L Raw,
        inputSize g M z t≤Module.finrank L V+stock (z+h) (t+h)*j3 (a+b) (e+g) ∧
        ∀ G∈V,Padded a b (e+g) M G∧sk (z+h) (t+h) G ∧
          ∃ H B:Raw,B.natDegree≤e+g∧F*H=G+amm d*B
def c2 :Prop :=
  ∀ a b e g j W z t:ℕ,a≤b→j≤g →
    ∀ q:Raw,q≠0→q.natDegree≤e→W<load a b q →
    ∀ V:zpI L Raw,
      (∀ G∈V,Padded a b (e+g) (W+1+j*(a+b)) G∧sk z t G) →
      (∀ G∈V,q∣G)→Module.finrank L V≤ stock z t*j3 (a+b) j
private abbrev ι:L[X] →+* FX:=algebraMap _ _
private theorem coeffMap_inj:Function.Injective (zDK ι:UR →+* _) :=
 MvPolynomial.map_injective _ (qz1 L[X] FX)
private theorem embed_degree (F:Raw) : (embed F).natDegree=F.natDegree :=
 qz0 coeffMap_inj F
private theorem embed_rect (F:Raw) (i:Fin 2) (j:ℕ) :
  ((embed F).coeff j).degreeOf i=(F.coeff j).degreeOf i:= by
 change ((F.map (zDK ι)).coeff j).degreeOf i= _
 rw [coeff_map,MvPolynomial.degreeOf,MvPolynomial.degrees_map_of_injective _
  (qz1 L[X] FX)]
 rfl
private theorem height_rect (F:Raw) :sk (height F) (height F) F:= by
 intro i j
 simp only [ite_self,← embed_rect]
 exact ((embed F).coeff j).degreeOf_le_totalDegree i |>.trans
  ((Qt.Qc _ _).mp le_rfl j)
private theorem stock_mono (c:ℕ) {v u:ℕ} (hv :v≤u) :
  ((c+1)*v+1)*(c*u+1)≤((c+1)*u+1)*(c*v+1) := by
 obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le hv
 have h: ((c+1)*(v+k)+1)*(c*v+1)=((c+1)*v+1)*(c*(v+k)+1)+k := by ring
 omega
private theorem rescale {c t v u r g M:ℕ} (hv :v≤u)
    (hs :stock ((c+1)*u) ((t+1)*u)*r< inputSize g M (c*u) (t*u)) :
    stock ((c+1)*v) ((t+1)*v)*r< inputSize g M (c*v) (t*v) := by
  let i (h:ℕ) :=stock (c*h) (t*h)
  let o (h:ℕ) :=stock ((c+1)*h) ((t+1)*h)
  have hc:o v*i u≤o u*i v := by
    calc
      _=(((c+1)*v+1)*(c*u+1))*(((t+1)*v+1)*(t*u+1)) := by
        dsimp only [o,i,stock]; ac_rfl
      _≤(((c+1)*u+1)*(c*v+1))*(((t+1)*u+1)*(t*v+1)) :=
        Nat.mul_le_mul (stock_mono c hv) (stock_mono t hv)
      _ = _:= by dsimp only [o,i,stock]; ac_rfl
  have hi:0< i v :=Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  by_contra! hn
  have ht:inputSize g M (c*v) (t*v)*i u< inputSize g M (c*v) (t*v)*i u :=
    calc
      _≤(o v*r)*i u:=ztf _ hn
      _=(o v*i u)*r := by ac_rfl
      _≤(o u*i v)*r :=ztf _ hc
      _=(o u*r)*i v := by ac_rfl
      _< inputSize g M (c*u) (t*u)*i v :=Nat.mul_lt_mul_of_pos_right hs hi
      _ = _:= by dsimp only [inputSize,i]; ac_rfl
  exact (Nat.lt_irrefl _ ht)
private theorem proper_output {F:Raw} (hF:Moving F) (V:zpI L Raw)
    (escape : ∀ q:Raw,Irreducible q→q∣F → ∃ G∈V,¬ q∣G) :
    ∃ G∈V,(embed F).resultant (embed G)≠0:= by
  classical
  obtain ⟨s,hs,hprod⟩:=WfDvdMonoid.exists_factors F hF.1
  let S:=s.toFinset
  let _:AddCommGroup V := @Submodule.addCommGroup L Raw _ _ _ V
  let B (q : ↥S) :zpI L V :=
    (LinearMap.range (LinearMap.mulLeft L (q:Raw))).comap V.subtype
  have hqF {q:Raw} (hq:q∈s) :q∣F :=
    (Multiset.dvd_prod hq).trans hprod.dvd
  have hB (q : ↥S) :B q ≠ ⊤ := by
    have hq: (q:Raw)∈s :=Multiset.mem_toFinset.mp q.property
    obtain ⟨G,hG,hn⟩:=escape q (hs q hq) (hqF hq)
    intro he
    have hm: (⟨G,hG⟩:V)∈B q:=he.symm ▸ Submodule.mem_top
    obtain ⟨r,hr⟩:=hm
    exact hn ⟨r,hr.symm⟩
  obtain ⟨G,hG⟩:=Submodule.exists_forall_notMem_of_forall_ne_top (ι := ↥S) (K:=L) (M := ↥V) B hB
  let _:StrongNormalizationMonoid UR :=UniqueFactorizationMonoid.strongNormalizationMonoid
  let _:NormalizedGCDMonoid UR :=UniqueFactorizationMonoid.toNormalizedGCDMonoid _
  let ψ:UR →+* FractionRing UR :=algebraMap _ _
  have hp (q:Raw) (hq:q∈s) :IsCoprime (q.map ψ) ((G:Raw).map ψ) := by
    have q0:=(hs q hq).isPrimitive (hF.2 q (hs q hq) (hqF hq)).1.ne'
    apply ((q0.irreducible_iff_irreducible_map_fraction_map (K:=FractionRing UR)).mp
      (hs q hq)).coprime_iff_not_dvd.mpr
    intro hd
    obtain ⟨r,hr⟩:=q0.dvd_of_fraction_map_dvd_fraction_map (K:=FractionRing UR) hd
    exact hG ⟨q,Multiset.mem_toFinset.mpr hq⟩ ⟨r,hr.symm⟩
  have hc:IsCoprime (s.prod.map ψ) ((G:Raw).map ψ) := by
    clear hG hB B S hprod hqF hs
    induction s using Multiset.induction_on with
    | empty=>simpa using (isCoprime_one_left (x :=(G:Raw).map ψ))
    | cons q s ih =>
      rw [Multiset.prod_cons,zNl]
      exact (hp q (Multiset.mem_cons_self _ _)).mul_left
        (ih (fun t ht=>hp t (Multiset.mem_cons_of_mem ht)))
  obtain ⟨u,hu⟩:=hprod
  have hcop:IsCoprime (F.map ψ) ((G:Raw).map ψ) := by
    rw [← hu,zNl]
    exact (isCoprime_mul_unit_right_left (u.isUnit.map (mapRingHom ψ)) _ _).mpr hc
  have hn:=resultant_ne_zero _ _ hcop
  rw [qz0 (qz1 UR (FractionRing UR)),
    qz0 (qz1 UR (FractionRing UR)),
    resultant_map_map] at hn
  refine ⟨G,G.property,?_⟩
  change (F.map (zDK ι)).resultant ((G:Raw).map (zDK ι))≠0
  rw [qz0 coeffMap_inj,qz0 coeffMap_inj,
    resultant_map_map]
  intro h
  have hz :F.resultant (G:Raw)=0:=coeffMap_inj (h.trans (map_zero _).symm)
  exact hn (by rw [hz,map_zero])
end
end q4Pefpa
end
