import ProximityPrize.SubmissionLower.Z6jV1pb
import ProximityPrize.SubmissionLower.Zf9KUOa
set_option Elab.async false
section
set_option autoImplicit true
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace qJrKOKe
open qMHqmcc (GG receipt appendGrades)
local notation "az" => (receipt 2565 rfl (by with_unfolding_all rfl) (by with_unfolding_all rfl))
private theorem r1 :GG b10 32 4 :=⟨az,az,az,az,True.intro⟩
private theorem r2 :GG b10 36 4 :=⟨az,az,az,az,True.intro⟩
private theorem r3:GG b10 40 4 :=⟨az,az,az,az,True.intro⟩
private theorem r4 :GG b10 44 4 :=⟨az,az,az,az,True.intro⟩
private theorem r5:GG b10 48 4 :=⟨az,az,az,az,True.intro⟩
theorem c:GG b10 32 20 :=
 appendGrades (appendGrades (appendGrades (appendGrades r1 r2) r3) r4) r5
end qJrKOKe
end
section
set_option autoImplicit true
namespace q7YMR4d
open P5 (K p)
open cu (L)
open qe6nVeb (SeedPlane)
open MvPolynomial
theorem polar_exists (q:SeedPlane) (hq:Irreducible q) :
    ∃ i:Fin 2,pderiv i q≠0:= by
  classical
  by_contra hn
  push Not at hn
  let _:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
  have hp:1<p:= by decide
  have hm (m:Fin 2 →₀ ℕ) (hm:m∈q.support) (i:Fin 2) :p∣m i:= by
    by_cases hi:m i=0
    · simp [hi]
    let n:=m-Finsupp.single i 1
    have he :n+Finsupp.single i 1=m :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi))
    have hei:n i+1=m i:= by
      simpa only [Finsupp.add_apply,Finsupp.single_eq_same] using
        congrArg (fun t:Fin 2 →₀ ℕ=>t i) he
    have hz : (pderiv i q).coeff n=(0:SeedPlane).coeff n :=
      congrArg (fun g:SeedPlane=>g.coeff n) (hn i)
    rw [coeff_pderiv,he] at hz
    change _ *_=0 at hz
    have hc:=(mul_eq_zero.mp hz).resolve_left (mem_support_iff.mp hm)
    have hc' : ((n i+1 :ℕ) :L)=0:= by
      rwa [Nat.cast_add,Nat.cast_one]
    rw [hei] at hc'
    exact (CharP.cast_eq_zero_iff L p _).mp hc'
  choose a ha using fun m:Fin 2 →₀ ℕ =>
    IsAlgClosed.exists_pow_nat_eq (q.coeff m) (show 0<p from by omega)
  let e (m:Fin 2 →₀ ℕ) :Fin 2 →₀ ℕ :=
    Finsupp.onFinset Finset.univ (fun i=>m i/p) (by simp)
  let r :SeedPlane := ∑ m∈q.support,monomial (e m) (a m)
  have he (m:Fin 2 →₀ ℕ) (hs :m∈q.support) :p•e m=m:= by
    ext i
    change p*(m i/p)=m i
    exact Nat.mul_div_cancel' (hm m hs i)
  have hr :r^p=q:= by
    calc
      _ = ∑ m∈q.support,(monomial (e m) (a m) :SeedPlane)^p :=
        map_sum (frobenius SeedPlane p) _ _
      _ = ∑ m∈q.support,monomial m (q.coeff m) := by
        exact Finset.sum_congr rfl fun m hm=> by rw [monomial_pow,he m hm,ha]
      _ = _:=q.as_sum.symm
  rw [← hr] at hq
  exact not_irreducible_pow (by omega :p≠1) hq
end q7YMR4d
end
section
set_option autoImplicit true
namespace qGzrWfb
noncomputable section
open MvPolynomial Finsupp
open cu (L)
open qe6nVeb (SeedPlane)
open q7YMR4d (oF)
abbrev m:Ideal SeedPlane :=idealOfVars (Fin 2) L
def shift (a :Fin 2→L) :SeedPlane →ₐ[L] SeedPlane :=
 aeval fun j=>MvPolynomial.X j+C (a j)
@[simp] private theorem gqb (a :Fin 2→L) (j:Fin 2) :
   shift a (MvPolynomial.X j)=MvPolynomial.X j+C (a j) :=aeval_X _ _
@[simp] private theorem ddR (a :Fin 2→L) (b:L) :
   shift a (C b)=C b:=aeval_C _ _
private theorem shift_inv (a :Fin 2→L) :
  (shift (-a)).comp (shift a)=AlgHom.id L SeedPlane := by
 apply MvPolynomial.algHom_ext
 intro j
 simp only [AlgHom.comp_apply,gqb,map_add,ddR,Pi.neg_apply,map_neg,
  AlgHom.id_apply]
 ring
def shiftEquiv (a :Fin 2→L) :SeedPlane ≃ₐ[L] SeedPlane :=
 AlgEquiv.ofAlgHom (shift a) (shift (-a)) (by simpa using shift_inv (-a)) (shift_inv a)
theorem shift_pderiv (a :Fin 2→L) (i:Fin 2) (q:SeedPlane) :
   pderiv i (shift a q)=shift a (pderiv i q) := by
 induction q using MvPolynomial.induction_on with
 | C b=>simp only [ddR,pderiv_C,map_zero]
 | add f g hf hg=>simp only [map_add,hf,hg]
 | mul_X f j hf =>
   simp only [map_mul,gqb,pderiv_mul,map_add,pderiv_C,add_zero,hf]
   by_cases h:j=i
   · subst j
     rw [pderiv_X_self,map_one]
   · rw [pderiv_X_of_ne h,map_zero]
theorem cNb (a :Fin 2→L) (q:SeedPlane) :eval 0 (shift a q)=eval a q:= by
 have h: (eval 0:SeedPlane →+* L).comp (shift a).toRingHom=eval a := by
  apply MvPolynomial.ringHom_ext
  · intro b
    simp
  · intro j
    simp
 exact DFunLike.congr_fun h q
private theorem eval_origin (q:SeedPlane) :eval (0:Fin 2→L) q=q.coeff 0:= by
 rw [eval_zero]
 rfl
private theorem point_origin :oF (0:Fin 2→L)=m:= by
 ext q
 change eval 0 q=0↔q∈m
 rw [eval_origin,← pow_one m,mem_pow_idealOfVars_iff']
 constructor
 · intro h d hd
   obtain rfl :d=0:=(degree_eq_zero_iff d).mp (Nat.lt_one_iff.mp hd)
   exact h
 · intro h
   exact h 0 (by simp)
theorem shift_point (a :Fin 2→L) : (oF a).map (shift a).toRingHom=m:= by
 have h:oF a=m.comap (shift a).toRingHom:= by
  ext q
  rw [← point_origin]
  exact (congrArg (· = 0) (cNb a q)).symm.to_iff
 rw [h]
 exact Ideal.map_comap_of_surjective _ (shiftEquiv a).surjective _
theorem sub_low (q:SeedPlane) (n:ℕ) :
  q - ∑ k∈Finset.range n,homogeneousComponent k q∈m^n:= by
 rw [mem_pow_idealOfVars_iff']
 intro d hd
 simp [coeff_homogeneousComponent,Finset.mem_range.mpr hd]
theorem finite_jet (J:Ideal SeedPlane) (h:m^3≤J) :
   Module.Finite L (SeedPlane ⧸ J) := by
 let V:=restrictTotalDegree (Fin 2) L 2
 let f :=(Ideal.Quotient.mkₐ L J).toLinearMap.comp V.subtype
 apply Module.Finite.of_surjective f
 intro x
 obtain ⟨q,rfl⟩:=Ideal.Quotient.mk_surjective x
 let r := ∑ k∈Finset.range 3,homogeneousComponent k q
 have hr :r∈V:= by
   apply (mem_restrictTotalDegree _ _ _).mpr
   apply totalDegree_finsetSum_le
   intro k hk
   exact (homogeneousComponent_isHomogeneous _ _).totalDegree_le.trans
     (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
 refine ⟨⟨r,hr⟩,?_⟩
 change Ideal.Quotient.mk J r=Ideal.Quotient.mk J q
 exact (Ideal.Quotient.eq.mpr (h (sub_low q 3))).symm
theorem constant_zero {q:SeedPlane} (h:eval 0 q=0) :
  homogeneousComponent 0 q=0:= by
 rw [eval_origin] at h
 simp [h]
theorem linear_zero {q:SeedPlane} (h : ∀ i,eval 0 (pderiv i q)=0) :
    homogeneousComponent 1 q=0:= by
  ext1 d
  rw [coeff_homogeneousComponent]
  split_ifs with hd
  · have hsum:=hd
    rw [degree_eq_sum,Fin.sum_univ_two] at hsum
    obtain ⟨i,rfl⟩ : ∃ i:Fin 2,single i 1=d:= by
      by_cases h0:d 0=0
      · have h1 :d 1=1 := by omega
        refine ⟨1,?_⟩
        ext j
        fin_cases j <;> simp [h0,h1]
      · have h:d 0=1∧d 1=0:= by omega
        refine ⟨0,?_⟩
        ext j
        fin_cases j <;> simp [h.1,h.2]
    have hi:=h i
    rw [eval_origin,coeff_pderiv] at hi
    simpa using hi
  · simp
theorem c4t (q:SeedPlane) (i:Fin 2) :
   homogeneousComponent 1 (pderiv i q)=pderiv i (homogeneousComponent 2 q) := by
 ext1 d
 rw [coeff_homogeneousComponent,coeff_pderiv,coeff_pderiv,coeff_homogeneousComponent,
   map_add Finsupp.degree,degree_single]
 by_cases h:d.degree=1
 · simp [h]
 · have h' : d.degree+1≠2 := by omega
   simp [h,h']
theorem mem_square {q:SeedPlane} (h0:homogeneousComponent 0 q=0)
  (h1 :homogeneousComponent 1 q=0) :q∈m^2 := by
 simpa [Finset.sum_range_succ,h0,h1] using sub_low q 2
end
end qGzrWfb
end
section
set_option autoImplicit true
namespace qGzrWfb
noncomputable section
open MvPolynomial Finsupp
open cu (L)
open qe6nVeb (SeedPlane)
open q7YMR4d (SmoothAt)
local notation "x₀" => (MvPolynomial.X (0:Fin 2) :SeedPlane)
local notation "x₁" => (MvPolynomial.X (1 :Fin 2) :SeedPlane)
private abbrev u:Fin 2 →₀ ℕ:=single 0 2
private abbrev v :Fin 2 →₀ ℕ:=single 0 1+single 1 1
private abbrev w:Fin 2 →₀ ℕ:=single 1 2
private theorem degree_two (d:Fin 2 →₀ ℕ) (hd:d.degree=2) :
   d=u∨d=v∨d=w:= by
 rw [degree_eq_sum,Fin.sum_univ_two] at hd
 by_cases h0:d 0=0
 · have h1 :d 1=2 := by omega
   right; right
   ext j
   fin_cases j <;> simp [w,h0,h1]
 by_cases h1 :d 1=0
 · have hd0:d 0=2 := by omega
   left
   ext j
   fin_cases j <;> simp [u,hd0,h1]
 · have h:d 0=1∧d 1=1 := by omega
   right; left
   ext j
   fin_cases j <;> simp [v,h.1,h.2]
theorem binary_form (Q:SeedPlane) (hQ:Q.IsHomogeneous 2) :
   ∃ a b c:L,Q=C a*x₀^2+C b*x₀*x₁+C c*x₁^2 := by
 refine ⟨Q.coeff u,Q.coeff v,Q.coeff w,?_⟩
 rw [C_mul_X_pow_eq_monomial,C_mul_X_pow_eq_monomial,C_mul_X_eq_monomial,
   ← pow_one x₁,← monomial_add_single]
 have huv :u≠v := by simp [u,v,Finsupp.ext_iff,Fin.forall_fin_two]
 have huw:u≠w:= by simp [u,w,Finsupp.ext_iff,Fin.forall_fin_two]
 have hvw:v≠w:= by simp [v,w,Finsupp.ext_iff,Fin.forall_fin_two]
 ext1 d
 by_cases hd:d.degree=2
 · rcases degree_two d hd with rfl | rfl | rfl <;>
     simp [coeff_monomial,huv,huw,hvw,Ne.symm huv,Ne.symm huw,Ne.symm hvw]
 · have hu:u≠d:= fun e=>hd (e ▸ (show u.degree=2 by simp [u]))
   have hv :v≠d:= fun e=>hd (e ▸ (show v.degree=2 by simp [v,map_add Finsupp.degree]))
   have hw:w≠d:= fun e=>hd (e ▸ (show w.degree=2 by simp [w]))
   rw [hQ.coeff_eq_zero hd]
   simp [coeff_monomial,hu,hv,hw]
def zD (j k :Fin 2) (r :L) :SeedPlane :=
 MvPolynomial.X j - C r*MvPolynomial.X k
theorem square_tangent (Q:SeedPlane) (hQ:Q.IsHomogeneous 2)
   (h : ¬ ∃ z :Fin 2→L,(∃ i,z i≠0)∧SmoothAt Q z) :
   ∃ (j k :Fin 2) (r a :L),j≠k∧Q=C a*zD j k r^2 := by
 obtain ⟨a,b,c,he⟩:=binary_form Q hQ
 by_cases ha :a=0
 · have hb:b=0:= by
     by_contra hb
     apply h
     refine ⟨![1,0],⟨0,by simp⟩,?_,1,?_⟩
     · simp [he,ha]
     · simpa [he,ha,pderiv_C_mul,pderiv_mul,pderiv_pow,Pi.single_apply] using hb
   exact ⟨1,0,0,c,by decide,by simp [he,ha,hb,zD]⟩
 · obtain ⟨r,hr⟩:=IsAlgClosed.exists_root
     (Polynomial.C a*Polynomial.X ^2+Polynomial.C b*Polynomial.X+Polynomial.C c)
     (by rw [Polynomial.degree_quadratic ha]; decide)
   have hroot :a*r^2+b*r+c=0:= by simpa [Polynomial.IsRoot] using hr
   have hzero :eval (![r,1] :Fin 2→L) Q=0:= by simpa [he] using hroot
   have hsing:eval (![r,1] :Fin 2→L) (pderiv 0 Q)=0:= by
     by_contra hn
     exact h ⟨![r,1],⟨1,by simp⟩,hzero,0,hn⟩
   have hder :2*a*r+b=0:= by
     simp [he] at hsing
     linear_combination hsing
   have hb:b = -(2*a*r) := by linear_combination hder
   have hc:c=a*r^2 := by linear_combination hroot - r*hder
   refine ⟨0,1,r,a,by decide,?_⟩
   rw [he,hb,hc]
   simp only [zD,map_neg,map_mul,map_pow,map_ofNat]
   ring
theorem tangent_polar (j k :Fin 2) (r a :L) (i:Fin 2) :
   pderiv i (C a*zD j k r^2) =
     C (2*a*((if j=i then 1 else 0) - r*(if k=i then 1 else 0)))*zD j k r := by
 have hX (s :Fin 2) :pderiv i (MvPolynomial.X s :SeedPlane) =
     C (if s=i then 1 else 0) := by
   by_cases h:s=i
   · subst s; simp
   · simp [pderiv_X_of_ne h,h]
 rw [pderiv_C_mul,pderiv_pow,show 2 - 1=1 from rfl,pow_one]
 have ht:pderiv i (zD j k r) =
     C ((if j=i then 1 else 0) - r*(if k=i then 1 else 0)) := by
   simp only [zD,map_sub,pderiv_C_mul,hX,map_mul]
 rw [ht]
 simp only [map_mul,map_ofNat]
 ring
end
end qGzrWfb
end
