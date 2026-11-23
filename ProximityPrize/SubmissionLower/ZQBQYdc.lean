import ProximityPrize.SubmissionLower.Zl7U3sa
set_option Elab.async false
set_option autoImplicit true
section
namespace q2TwyLa
noncomputable section
open Polynomial Finset
open cu (L FX)
open P5_7_7 (phys)
open q1kuFjb (reduced_pair)
open qFD8jve (Vanishes)
private theorem phys_inj:Function.Injective phys :=IsFractionRing.injective L[X] FX
private theorem BA {R E :Type} [CommRing R] [Field E] (c:R →+* E)
   {T:R[X]} {d:ℕ} (hd:T.natDegree≤d) (a b:E) (hb:b≠0) :
   T.eval₂ c (a/b)*b^d =
     ∑ i∈range (d+1),c (T.coeff i)*a^i*b^(d-i) := by
 rw [eval₂_eq_sum_range' c (Nat.lt_succ_of_le hd),sum_mul]
 refine sum_congr rfl fun i hi => ?_
 have hde :d=i+(d-i) :=(Nat.add_sub_of_le (Nat.le_of_lt_succ (mem_range.mp hi))).symm
 rw [show b^d=b^i*b^(d-i) by rw [← pow_add,← hde],
   div_pow,mul_assoc _ (_/_) _,← mul_assoc (_/_) _ _,
   div_mul_cancel₀ _ (pow_ne_zero _ hb),mul_assoc]
private theorem reduced_equation {T:L[X][X]} {A B:L[X]} {d:ℕ}
  (hd:T.natDegree≤d) (hB:B≠0)
  (h:T.eval₂ phys (phys A/phys B)=0) :
  ∑ i∈range (d+1),(T.coeff i).coeff 0*(A.coeff 0)^i*(B.coeff 0)^(d-i)=0:= by
 let N :L[X] := ∑ i∈range (d+1),T.coeff i*A^i*B^(d-i)
 have hb:=(map_ne_zero_iff phys phys_inj).mpr hB
 have he :phys N=0:= by
  simpa only [N,map_sum,map_mul,map_pow,h,zero_mul] using (BA phys hd (phys A) (phys B) hb).symm
 have hz :N=0:=phys_inj (he.trans (map_zero phys).symm)
 simpa only [N,map_sum,map_mul,map_pow,constantCoeff_apply,coeff_zero,map_zero] using
  congrArg (constantCoeff :L[X] →+* L) hz
private theorem residue_root {T:L[X][X]} {A B:L[X]} (hB:B.coeff 0≠0)
  (h:T.eval₂ phys (phys A/phys B)=0) :
  (T.map constantCoeff).eval (A.coeff 0/B.coeff 0)=0:= by
 have hb:B≠0:= fun hz=>hB (by simp [hz])
 have hz :=(BA constantCoeff (le_refl T.natDegree) (A.coeff 0) (B.coeff 0) hB).trans
  (reduced_equation (le_refl T.natDegree) hb h)
 rw [← eval_map] at hz
 exact (mul_eq_zero.mp hz).resolve_right (pow_ne_zero _ hB)
private theorem special_outer (T:L[X][X][X]) (a :L) (u:FX) :
  evaluatePencil phys u (phys (C a)) T=(T.eval (C (C a))).eval₂ phys u:= by
 let e :=eval₂RingHom phys u
 change T.eval₂ e (phys (C a))=e (T.eval (C (C a)))
 rw [← eval₂_hom (f :=e)]
 simp [e]
theorem specialize_normalized (f g:L[X][X]) (T:L[X][X][X]) {d n m:ℕ} {h:L}
   (hf :0<f.natDegree) (hfd:f.natDegree≤d) (hg:g.natDegree≤d)
   (hT:qW f g d=C (C ((Polynomial.X:L[X])^n))*T)
   (hdeg: (T.coeff 0).natDegree≤d) (htop: ((T.coeff 0).coeff d).coeff 0≠0)
   (hedge : (T.coeff (d-m)).map constantCoeff=monomial m h) (hh:h≠0)
   (P Q:L[X]) (hP:P.coeff 0=0) (hQ:Q.coeff 0≠0)
   (hroot :f.eval₂ phys (phys P/phys Q)=0)
   (hsimple :f.derivative.eval₂ phys (phys P/phys Q)≠0) :
   let b := -(g.eval₂ phys (phys P/phys Q)/f.derivative.eval₂ phys (phys P/phys Q))
   Vanishes (b*phys Q^2) := by
 let y :=phys P/phys Q
 let b := -(g.eval₂ phys y/f.derivative.eval₂ phys y)
 change Vanishes (b*phys Q^2)
 obtain ⟨A,B,hB,hcop,hb⟩:=reduced_pair b
 have he :b*f.derivative.eval₂ phys y+g.eval₂ phys y=0:= by
   have hs :f.derivative.eval₂ phys y≠0:=hsimple
   simp only [b,neg_mul,div_mul_cancel₀ _ hs,neg_add_cancel]
 have q0 (a :L) : (T.eval (C (C a))).eval₂ phys (b+phys (C a)*y)=0:= by
   have hz :=pencil_zero phys f g y b (phys (C a)) hf hfd hg hroot he
   rw [hT,map_mul] at hz
   have hn:phys ((Polynomial.X:L[X])^n)≠0 :=
     (map_ne_zero_iff phys phys_inj).mpr (pow_ne_zero _ X_ne_zero)
   rw [← special_outer]
   exact (mul_eq_zero.mp hz).resolve_left (by
     simpa only [evaluatePencil,coe_eval₂RingHom,eval₂_C] using hn)
 have hzero₀: (T.coeff 0).eval₂ phys (phys A/phys B)=0:= by
   simpa only [C_0,map_zero,zero_mul,add_zero,← coeff_zero_eq_eval_zero,← hb] using q0 0
 have q1 :B.coeff 0≠0:= by
   intro hz
   obtain ⟨U,V,hUV⟩:=hcop
   have hA₀:A.coeff 0≠0:= by
     intro hA
     have h1 :=congrArg (constantCoeff :L[X] →+* L) hUV
     simp [hA,hz] at h1
   have hs :=reduced_equation hdeg hB hzero₀
   rw [sum_eq_single d] at hs
   · simp only [Nat.sub_self,pow_zero,mul_one] at hs
     exact (mul_ne_zero htop (pow_ne_zero _ hA₀)) hs
   · intro i hi hid
     have hdi:d-i≠0:= by have :=mem_range.mp hi; omega
     simp [hz,zero_pow hdi]
   · simp
 let e :L[X][X] →+* L:=(evalRingHom (A.coeff 0/B.coeff 0)).comp (mapRingHom constantCoeff)
 have hQne :phys Q≠0:=(map_ne_zero_iff phys phys_inj).mpr (fun hz=>hQ (by simp [hz]))
 have hBne :phys B≠0:=(map_ne_zero_iff phys phys_inj).mpr hB
 have hT0:T.map e=0:= by
   apply zero_of_eval_zero
   intro a
   let N :=A*Q+C a*P*B
   let D:=B*Q
   have hN :N.coeff 0=A.coeff 0*Q.coeff 0:= by
     simp only [N,coeff_add,mul_coeff_zero,hP,mul_zero,zero_mul,add_zero]
   have hD:D.coeff 0=B.coeff 0*Q.coeff 0:=mul_coeff_zero B Q
   have hd:D.coeff 0≠0:=hD ▸ mul_ne_zero q1 hQ
   have hval :phys N/phys D =b+phys (C a)*y := by
     rw [← hb]
     simp only [N,D,y,map_add,map_mul]
     field_simp [hBne,hQne]
   have q2 :=residue_root hd (hval ▸ q0 a)
   have hr :N.coeff 0/D.coeff 0=A.coeff 0/B.coeff 0:= by
     rw [hN,hD,mul_div_mul_right _ _ hQ]
   rw [hr] at q2
   rw [eval_map,← show e (C (C a))=a by simp [e],eval₂_hom]
   simpa only [e,RingHom.comp_apply,coe_mapRingHom,coe_evalRingHom] using q2
 have hx :=congrArg (fun U:L[X]=>U.coeff (d-m)) hT0
 have hvan:A.coeff 0=0:= by
   simp only [coeff_map,coeff_zero,e,RingHom.comp_apply,coe_mapRingHom,coe_evalRingHom,
     hedge,eval_monomial] at hx
   by_contra hA
   exact (mul_ne_zero hh (pow_ne_zero _ (div_ne_zero hA q1))) hx
 refine ⟨A*Q^2,B,?_,q1,?_⟩
 · change constantCoeff (A*Q^2)=0
   rw [map_mul,constantCoeff_apply,hvan,zero_mul]
 · rw [← hb,map_mul,map_pow,div_mul_eq_mul_div]
end
end q2TwyLa
end
section
open Polynomial renaming coe_mapRingHom→qz0,map_injective→qz1,natDegree_map_eq_of_injective→qz2,ext→qz3
set_option backward.isDefEq.respectTransparency false
namespace q2TwyLa
noncomputable section
open Polynomial
open cu (L)
open P5 (p)
open qb0hmCe (cLN specialize zD)
open q1kuFjb (coeff_liftAt expansion_coeff small_valuation)
open qFD8jve (aaD polarResultant)
open scoped WithZero
def c1 :Prop :=
  ∀ f :i5[X][X],0<f.natDegree→f.natDegree<p→polar f≠0 →
    Nonempty (RootData f)
def c2 :Prop :=
  ∀ f :i5[X][X],0<f.natDegree→f.leadingCoeff.coeff 0≠0→polar f≠0 →
    RootData f→Nonempty (ReducedPencil f)
private abbrev s :=algebraMap i5 aQ
private abbrev r :i5 →+* L:=PowerSeries.constantCoeff
private theorem cXH {E :Type} [Field E] [Algebra L E] (a :E →ₐ[L] aQ)
  (F:E[X][X]) (h:integral a F) (i j:ℕ) :
  s (((lift a F h).coeff i).coeff j)=a ((F.coeff i).coeff j) := by
 simp only [lift,coeff_map,qz0]
 change (((LaurentSeries.powerSeriesEquivSubring L).symm (((q1kuFjb.Ua a F h).coeff i).coeff j)
  : i5) :aQ)= _
 rw [← LaurentSeries.powerSeriesEquivSubring_coe_apply,RingEquiv.apply_symm_apply,coeff_liftAt]
private theorem lift_map {E :Type} [Field E] [Algebra L E] (a :E →ₐ[L] aQ)
  (F:E[X][X]) (h:integral a F) :
  (lift a F h).map (mapRingHom s)=F.map (mapRingHom a.toRingHom) := by
 apply qz3 fun i=>qz3 fun j => ?_
 simp only [coeff_map,qz0,cXH]
 rfl
private theorem seed_reduce {E :Type} [Field E] [Algebra L E] (a :E →ₐ[L] aQ)
   (F:E[X][X]) (h:integral a F) :
   (lift a F h).map (mapRingHom r)=cLN a 0 F ∧
   (diff (lift a F h)).map (mapRingHom r)=cLN a 1 F:= by
 have hC (i j n:ℕ) :PowerSeries.coeff n (((lift a F h).coeff i).coeff j) =
     (a ((F.coeff i).coeff j)).coeff (n:ℤ) := by
   rw [← cXH a F h i j]
   exact (LaurentSeries.coeff_coe_powerSeries (((lift a F h).coeff i).coeff j) n).symm
 constructor
 · apply qz3 fun i=>qz3 fun j => ?_
   simp only [coeff_map,qz0,expansion_coeff,← PowerSeries.coeff_zero_eq_constantCoeff_apply]
   exact hC i j 0
 · apply qz3 fun i=>qz3 fun j => ?_
   simp only [coeff_map,qz0,expansion_coeff,diff_coeff,
     ← PowerSeries.coeff_zero_eq_constantCoeff_apply,PowerSeries.coeff_derivative,zero_add,
     Nat.cast_zero,mul_one]
   exact hC i j 1
theorem centre_map {R S:Type} [CommRing R] [CommRing S] (b:R →+* S) (F:R[X][X]) :
  (centre F).map b=centre (F.map (mapRingHom b)) := by
 ext i
 simp only [centre,coeff_map,qz0,constantCoeff_apply]
theorem polar_map {R S:Type} [CommRing R] [CommRing S] (b:R →+* S)
  (hb:Function.Injective b) (F:R[X][X]) :
  (polar F).map b=polar (F.map (mapRingHom b)) := by
 change mapRingHom b (polar F)= _
 have hd:=qz2 (f :=mapRingHom b) (qz1 b hb) F
 rw [polar,polar,hd,derivative_map,resultant_map_map]
theorem trailing_map {R S:Type} [CommRing R] [CommRing S] (b:R →+* S)
  (hb:Function.Injective b) (q:R[X]) : (q.map b).trailingCoeff=b q.trailingCoeff := by
 simp only [trailingCoeff,natTrailingDegree,trailingDegree,support_map_of_injective q hb,coeff_map]
private theorem leading_unit (f :i5[X][X]) (hd:0<f.natDegree) (hℓ:f.leadingCoeff.coeff 0≠0)
  (hp:r (polar f).trailingCoeff≠0) :r (f.leadingCoeff.coeff 0)≠0:= by
 intro hz
 let q:i5[X] :=(-1)^(f.natDegree*(f.natDegree-1)/2)*f.discr
 have hq:polar f=f.leadingCoeff*q:= by
  rw [polar,resultant_deriv (natDegree_pos_iff_degree_pos.mp hd)]
  dsimp [q]
  ac_rfl
 apply hp
 rw [hq,trailingCoeff_mul,trailingCoeff_eq_coeff_zero hℓ,map_mul,hz,zero_mul]
theorem of_children (tame :c1) (normalize :c2) :qFD8jve.c2 := by
  intro E _ _ a F v hd hp hℓ hpr hi hguard P Q hP hQ hroot hsimple
  have h:integral a F:= by
    intro i j
    simpa [v,Valuation.comap_apply] using hi i j
  let f :=lift a F h
  have hs :Function.Injective s :=HahnSeries.ofPowerSeries_injective
  have hm:=lift_map a F h
  have q2 :f.natDegree=F.natDegree := by
    simpa only [qz2 (f :=mapRingHom s) (qz1 _ hs),
      qz2 (f :=mapRingHom a.toRingHom)
        (qz1 _ a.injective)] using congrArg natDegree hm
  have hlift:s (f.leadingCoeff.coeff 0)=a (F.leadingCoeff.coeff 0) := by
    simpa only [leadingCoeff,q2] using cXH a F h F.natDegree 0
  have q3:f.leadingCoeff.coeff 0≠0:= by
    intro hz
    apply hℓ
    apply a.injective
    change a (F.leadingCoeff.coeff 0)=a 0
    rw [← hlift,hz,map_zero,map_zero]
  have q5: (polar f).map s=(polarResultant F).map a.toRingHom:= by
    rw [polar_map s hs,hm]
    exact (polar_map a.toRingHom a.injective F).symm
  have hcen: (centre f).map s=(aaD F).map a.toRingHom:= by
    rw [centre_map,hm,← centre_map]
    rw [centre,aaD]
    congr 1
    ext z
    simp [coeff_zero_eq_eval_zero]
  have hn:polar f≠0:= by
    intro hz
    apply hpr
    apply qz1 a.toRingHom a.injective
    rw [Polynomial.map_zero,← q5,hz,Polynomial.map_zero]
  have hG:s ((polar f).trailingCoeff*(centre f).trailingCoeff)=a (qFD8jve.guard F) := by
    simp only [qFD8jve.guard,map_mul,← trailing_map s hs,q5,hcen,
      trailing_map _ a.injective]
    rfl
  have hU:r ((polar f).trailingCoeff*(centre f).trailingCoeff)≠0:= by
    intro hz
    have hv :=(small_valuation _).mpr hz
    change (Valued.v :Valuation aQ ℤᵐ⁰) (s _)≤_ at hv
    rw [hG] at hv
    change (Valued.v :Valuation aQ ℤᵐ⁰) (a (qFD8jve.guard F))=1 at hguard
    rw [hguard] at hv
    exact (not_le_of_gt (WithZero.exp_lt_one_iff.mpr (by decide : (-1 :ℤ)<0))) hv
  have hr :r (polar f).trailingCoeff≠0:=(mul_ne_zero_iff.mp (by simpa only [map_mul] using hU)).1
  have q0:0<f.natDegree :=q2 ▸ hd
  have q4 :=leading_unit f q0 q3 hr
  obtain ⟨roots⟩:=tame f q0 (q2 ▸ hp) hn
  obtain ⟨D⟩:=normalize f q0 q3 hn roots
  let M:=mapRingHom (mapRingHom r)
  let T:=D.T.map M
  let f₀:=f.map (mapRingHom r)
  let f₁:=(diff f).map (mapRingHom r)
  have q7:f₀.natDegree=f.natDegree :=le_antisymm natDegree_map_le <| le_natDegree_of_ne_zero <| by
    intro hz
    have hzero :=congrArg (fun q:L[X]=>q.coeff 0) hz
    exact q4 (by simpa only [f₀,coeff_map,qz0,coeff_natDegree,coeff_zero] using hzero)
  have hf₁:f₁.natDegree≤f.natDegree :=natDegree_map_le.trans (diff_degree f)
  have hT:qW f₀ f₁ f.natDegree=C (C ((Polynomial.X:L[X])^(polar f).natTrailingDegree))*T:= by
    rw [← pencil_map (mapRingHom r),D.factor]
    simp [M,T]
  have hbound: (T.coeff 0).natDegree≤f.natDegree := by
    simpa only [T,M,coeff_map,qz0] using natDegree_map_le.trans D.bound
  have htop: ((T.coeff 0).coeff f.natDegree).coeff 0≠0:= by
    simpa only [T,M,coeff_map,qz0,D.top,map_mul] using mul_ne_zero q4 hr
  have hedge : (T.coeff (f.natDegree-(centre f).natTrailingDegree)).map constantCoeff =
      monomial (centre f).natTrailingDegree (r ((polar f).trailingCoeff*(centre f).trailingCoeff)) := by
    dsimp only [T,M]
    rw [coeff_map,qz0,map_map,show constantCoeff.comp (mapRingHom r) =
      r.comp constantCoeff from RingHom.ext (fun q=>coeff_map r 0),← map_map,D.edge,map_monomial]
  obtain ⟨h₀,h₁⟩:=seed_reduce a F h
  change f₀= _ at h₀
  change f₁= _ at h₁
  simpa only [h₀,h₁,zD,specialize] using specialize_normalized f₀ f₁ T (q7 ▸ q0)
    q7.le hf₁ hT hbound htop hedge hU P Q hP hQ
    (show specialize f₀ P Q=0 by rwa [h₀]) (show specialize f₀.derivative P Q≠0 by rwa [h₀])
end
end q2TwyLa
end
