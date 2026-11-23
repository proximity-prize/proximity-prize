import ProximityPrize.SubmissionLower.ZOAcvWb
import ProximityPrize.SubmissionLower.Z5rjxle
import ProximityPrize.SubmissionLower.ZpAvArb
import ProximityPrize.SubmissionLower.ZvqS6Fa
import ProximityPrize.SubmissionLower.ZN2gA7a
import ProximityPrize.SubmissionLower.Zeo5Ibd
set_option Elab.async false
open _root_ renaming Module.finrank → zsE, Nat.add_le_add_right → zlr, Nat.mul_le_mul_left → zBI, Nat.nsmul_eq_mul → zNJ, Polynomial.map_injective → zTo, PowerSeries.constantCoeff → zbO
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace qZcMfNa
noncomputable section
open Polynomial
open P5 (K p)
open cu (L)

open E7 (CurvePlace poleOrder KB)

open q7F2qKe (weakAgreement)
open q82zwcd (highFee width)
open qBd5KZd (MarkedCurve Allowance mass small btN bounded j3
  avoids pull modulus pull_irreducible)



open private qL irred_resultant small_pow pole_le from ProximityPrize.SubmissionLower.Zw100fa
open private debit_add from ProximityPrize.SubmissionLower.ZOAcvWb
open scoped Classical WithZero
def c1 :Prop :=qBd5KZd.c2
def c2 :Prop :=qBd5KZd.c3
def c3:Prop :=
  ∀ (E :Type) [Field E] [Algebra L E] (u v e k M:ℕ) (f :E[X][X])
    (A V:Allowance E),u≤v→f≠0→f.natDegree≤e→(e+k)*(u+v)<M →
    bounded A f→FiniteDimensional L (btN V)→FiniteDimensional L (btN (V+A)) →
    ∃ (b:L) (S:Submodule L E[X][X]),
      ((k+1)*M)*zsE L (btN V) ≤
        zsE L S+j3 (u+v) (e+k)*zsE L (btN (V+A)) ∧
      ∀ G∈S,Padded u v (e+k) M G∧bounded (V+A) G ∧
        ∃ H R:E[X][X],H.natDegree≤k∧R.natDegree≤e+k∧bounded V H ∧
          bounded (V+A) R∧f*H=G+C (modulus b M)*R
def c4 :Prop :=
  ∀ (E :Type) [Field E] [Algebra L E] (u v e k j W:ℕ) (f :E[X][X])
    (A:Allowance E) (S:Submodule L E[X][X]),
    u≤v→j≤k→f≠0→f.natDegree=e→W<weight u v e f →
    FiniteDimensional L (btN A) →
    (∀ G∈S,Padded u v (e+k) (W+1+j*(u+v)) G∧bounded A G) →
    (∀ G∈S,f∣G)→zsE L S≤j3 (u+v) j*zsE L (btN A)
def c5:Prop :=
  ∀ {T:Finset K} (C:MarkedCurve T) (P Q:T→ L[X]) (u v k m M:ℕ) (b:L)
    (f G H R:C.E[X][X]) (A V:Allowance C.E),
    u≤v→0<f.natDegree→0<M →
    (∀ t,Q t≠0∧(Q t).natDegree≤u∧(P t).natDegree≤v) →
    H.natDegree≤k →
    R.natDegree≤f.natDegree+k →
    avoids C V→bounded A f→bounded (V+A) G→bounded V H→bounded (V+A) R →
    roots C P Q m f A →
    Padded u v (f.natDegree+k) M G →
    f*H=G+Polynomial.C (modulus b M)*R →
    ∀ i t,small (C.Ia t)
      (((f.natDegree•(V+A)+G.natDegree•A) (C.Ia t) :ℤ)-(m:ℤ))
      ((f.resultant G).coeff i)
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) :
    qVuPRtb.c1 := by
  intro D w T s z Q J F k c j W M hsec hd hdP hok hW
  let C:MarkedCurve T:=⟨F.curve.E,F.curve.curve,
    ⟨fun t=>F.place t,fun t u h=>Subtype.ext (F.distinct t.property u.property h)⟩⟩
  obtain ⟨A,hA,hfA,hroot⟩:=prepare F
  let u:=J.u₀
  let v :=J.u₁
  let e :=F.d
  let H :=F.h
  let N :=(k+1)*M
  let Dbt:=j3 (u+v) (e+k)+j3 (u+v) j
  obtain ⟨_,_,hj,_,hM,hEM,hSurplus⟩:=hok
  have hwidth :u+v=width D:= by
    have hw:=J.xF
    change 2*weakAgreement+(u+v)=262144+D at hw
    change u+v=262144+D-2*weakAgreement
    omega
  have hs :Dbt*(c+1)<N*c:= by
    simpa only [Dbt,N,hwidth,debit_add,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hSurplus
  obtain ⟨loss,hLower⟩:=h1 C (fun B=>(h2 C.E C.curve B).1)
  let r :=N*loss+Dbt+1
  let a :=e*r
  let m:=p^a
  let bgt:=c*(m*H)+r
  have hm:e*r< m:=Nat.lt_pow_self (by decide :1<p)
  obtain ⟨V,hV,hVAway,hDimV⟩:=hLower bgt
  let:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
  let:CharP C.E p:=charP_of_injective_ringHom (algebraMap L C.E).injective p
  let φ:=iterateFrobenius C.E p a
  let φL:=iterateFrobenius L p a
  let A' : Allowance C.E :=m•A
  let f' : C.E[X][X] :=pull a F.f
  let P' (t:T) :=(J.P t).map φL
  let Q' (t:T) :=(J.Q t).map φL
  have hf'e :f'.natDegree=e :=natDegree_map_eq_of_injective
    (zTo φ φ.injective) F.f
  have hHigh:W<weight u v e f' := by
    have heq :weight u v e f' = weight u v e F.f := by
      change weight u v e (F.f.map (mapRingHom φ))= _
      unfold weight
      rw [support_map_of_injective _ (zTo φ φ.injective)]
      simp only [coeff_map,coe_mapRingHom,natDegree_map_eq_of_injective φ.injective]
      rfl
    rw [heq]
    by_contra! hn
    apply hW
    intro i hi
    exact (Finset.le_sup (s :=F.f.support) (f := fun t =>
      (F.f.coeff t).natDegree+e*u+t*(v-u)) (mem_support_iff.mpr hi)).trans hn
  obtain ⟨hf'P,hf'I⟩:=pull_irreducible a F.f F.primitive F.irreducible hdP
  have hPQ (t:T) :Q' t≠0∧(Q' t).natDegree≤u∧(P' t).natDegree≤v := by
    refine ⟨?_,natDegree_map_le.trans (hsec t t.property).1,natDegree_map_le.trans (hsec t t.property).2⟩
    change (J.Q t).map φL≠0
    exact (map_ne_zero_iff (mapRingHom φL) (zTo φL φL.injective)).mpr
      (J.denominator t t.property)
  have hA'val (w:CurvePlace L C.E) : (A' w:ℤ)=m•(A w:ℤ) := by
    rw [show A' w=m*A w by
      simp only [A',Finsupp.smul_apply,zNJ]
      rfl,Nat.cast_mul,nsmul_eq_mul]
  have hf'A:bounded A' f' := by
    intro i j w
    change small w (A' w) (((F.f.map (mapRingHom φ)).coeff i).coeff j)
    rw [coeff_map,coe_mapRingHom,coeff_map,hA'val]
    exact small_pow w (hfA i j w) m
  have hRoots' : roots C P' Q' m f' A' := by
    intro t i
    have htw (S:L[X]) : (S.map φL).map (algebraMap L C.E) =
        (S.map (algebraMap L C.E)).map φ:= by
      rw [map_map,map_map]
      exact congrArg (fun ψ=>S.map ψ) ((algebraMap L C.E).iterateFrobenius_comm p a)
    change small (C.Ia t) ((A' (C.Ia t) :ℤ)-(m:ℤ))
      ((BA f'.natDegree (((J.P t).map φL).map (algebraMap L C.E))
        (((J.Q t).map φL).map (algebraMap L C.E)) (F.f.map (mapRingHom φ))).coeff i)
    rw [hf'e,htw,htw,← cleared_map,coeff_map,hA'val,← nsmul_one m,← smul_sub]
    exact small_pow (C.Ia t) (hroot t i) m
  have hA'm:mass A' = m*H := by
    simp only [A',map_nsmul,zNJ]
    exact congrArg (fun n:ℕ=>m*n) hA
  obtain ⟨hFin,hDim⟩:=h2 C.E C.curve (V+A')
  have hD:zsE L (btN (V+A'))≤bgt+m*H+1 :=
    hDim.trans (by rw [map_add,hA'm]; exact zlr (zlr hV _) 1)
  have hRank :Dbt*zsE L (btN (V+A'))<N*zsE L (btN V) := by
    have h:=(qL hs (m*H) loss :Dbt*(bgt+m*H+1)+N*loss<N*bgt)
    exact Nat.lt_of_add_lt_add_right ((zlr (zBI Dbt hD) _).trans_lt
      (h.trans_le (by rw [← Nat.mul_add]; exact zBI _ hDimV)))
  have hM' : M=W+1+j*(u+v) :=(congrArg (fun t=>M=W+1+j*t) hwidth).mpr hM
  have hEM' : (e+k)*(u+v)<M:=(congrArg (fun t=>(e+k)*t<M) hwidth).mpr hEM
  obtain ⟨b,S,hS,hRow⟩:=h3 C.E u v e k M f' A' V J.order hf'P.ne_zero hf'e.le hEM'
    hf'A (h2 C.E C.curve V).1 hFin
  have hWide :j3 (u+v) j*zsE L (btN (V+A'))<zsE L S:= by
    have h:=hRank.trans_le hS
    dsimp only [Dbt] at h
    rw [Nat.add_mul] at h
    omega
  have hProper : ∃ G∈S,¬ f' ∣ G:= by
    by_contra! hAll
    exact hWide.not_ge (h4 C.E u v e k j W f' (V+A') S J.order hj hf'P.ne_zero hf'e hHigh hFin
      (fun G hG=>⟨hM' ▸ (hRow G hG).1,(hRow G hG).2.1⟩) hAll)
  obtain ⟨G,hGS,hG⟩:=hProper
  obtain ⟨hGpad,hGa,P,R,hPd,hRd,hPu,hRu,hEq⟩:=hRow G hGS
  let i:=(f'.resultant G).natDegree
  have hi: (f'.resultant G).coeff i≠0:=leadingCoeff_ne_zero.mpr (irred_resultant hf'P hf'I hG)
  let Aout:=f'.natDegree•(V+A')+G.natDegree•A'
  have hPoles : (f'.resultant G).coeff i∈btN Aout:=resultant_bounded hf'A hGa i
  have hZeros :=h5 C P' Q' u v k m M b f' G P R A' V J.order (hf'e.symm ▸ (by omega :0<e))
    ((Nat.zero_le _).trans_lt hEM') hPQ hPd (hf'e.symm ▸ hRd) hVAway hf'A hGa hPu hRu
    hRoots' (hf'e.symm ▸ hGpad) hEq i
  refine ⟨⟨C.E,C.curve,a,_,hi,C.Ia,Aout,pole_le hPoles,?_⟩,?_⟩
  · intro t
    have hlog:=(WithZero.log_le_iff_le_exp ((C.Ia t).value.ne_zero_iff.mpr hi)).mpr (hZeros t)
    change WithZero.log ((C.Ia t).value ((f'.resultant G).coeff i)) ≤
      (Aout (C.Ia t) :ℤ)-(m:ℤ) at hlog
    unfold poleOrder KB
    change m+_≤Aout (C.Ia t)+_
    omega
  · change Aout.sum (fun _ n=>n)< m*(highFee e k c*H+1)
    rw [← mass_eq]
    have hmass :mass Aout≤e*(bgt+m*H)+(e+k)*(m*H) := by
      simp only [Aout,map_add,map_nsmul,zNJ,hf'e,hA'm]
      exact Nat.add_le_add (zBI _ (zlr hV _))
        (Nat.mul_le_mul_right _ hGpad.1)
    have heq :e*(bgt+m*H)+(e+k)*(m*H)=m*(highFee e k c*H)+e*r := by
      dsimp only [bgt,highFee]
      ring
    rw [heq] at hmass
    exact hmass.trans_lt (by rw [Nat.mul_add,Nat.mul_one]; exact Nat.add_lt_add_left hm _)
end
end qZcMfNa
end
section
namespace qg1w8ra
noncomputable section
open Polynomial
open cu (L)
open qNu3xvc (Equation)
open P5_7_1_7_4_3_4 (Pencil)
open qfbIfsd (Index Slot baseCap ordCap form)
open q7P6kQb
open qZu9hjc (atPair jacobian physicalDeriv)
open qs5yTLd (aOv det dx_map)
variable {E :Type} [Field E] [Algebra L E] {A:Equation E}
private def perturbed (C:Pencil A) (z :Index A→L) (t:Fin 3) : (Series E)[X][X] :=
  ∑ i:Slot A.s (baseCap A t) (ordCap A t),
    monomial i.1.val (monomial i.2.val (args C z 0 ⟨t,i⟩))
private theorem args_constant (C:Pencil A) (z :Index A→L) (i:Index A) :
    zbO (args C z 0 i)=algebraMap (tu E) (Closure E) (afe C i) := by
  simp only [args,coe_eval₂RingHom,eval₂_at_zero,map_add,map_mul,
    PowerSeries.constantCoeff_X,mul_zero,add_zero,Xm,afe,
    RingHom.comp_apply,PowerSeries.constantCoeff_C]
private theorem reduction (C:Pencil A) (z :Index A→L) (t:Fin 3) :
    (perturbed C z t).map (mapRingHom zbO) =
      (block C t).map (mapRingHom (algebraMap (tu E) (Closure E))) := by
  simp only [perturbed,block,Polynomial.map_sum,map_monomial,coe_mapRingHom,args_constant]
private theorem eval_perturbed (C:Pencil A) (z :Index A→L) (t:Fin 3) (x y :Series E) :
    (perturbed C z t).evalEval x y=form (args C z 0) t x y := by
  rw [← eval₂_evalRingHom]
  simp [perturbed,form,eval₂_finsetSum,eval₂_monomial]
omit [Algebra L E] in
private theorem eval_mapped (j:tu E →+* Closure E) (f : (tu E)[X][X]) (x y :Closure E) :
    (f.map (mapRingHom j)).evalEval x y=atPair j x y f :=
  (eval₂_eval₂RingHom_apply j x y f).symm
theorem proof :q7P6kQb.c3:= by
  classical
  intro E _ _ A C F z
  have dR (i:Fin F.size) : ∃ xy :Series E×Series E,
      (zbO xy.1,zbO xy.2)=F.point i ∧
      form (args C z 0) 0 xy.1 xy.2=0∧form (args C z 0) 1 xy.1 xy.2=0:= by
    obtain ⟨xy,hc,h₀,h₁⟩:=aOv (perturbed C z 0) (perturbed C z 1)
      (F.point i).1 (F.point i).2
      (by simpa only [reduction,eval_mapped,aMq] using F.zero₀ i)
      (by simpa only [reduction,eval_mapped,aMq] using F.zero₁ i)
      (by simpa only [reduction,det,dx_map,derivative_map,eval_mapped,jacobian,
        qs5yTLd.dx,physicalDeriv] using F.simple i)
    exact ⟨xy,hc,(eval_perturbed C z 0 _ _).symm.trans h₀,
      (eval_perturbed C z 1 _ _).symm.trans h₁⟩
  choose xy hc h₀ h₁ using dR
  exact ⟨⟨xy,hc,h₀,h₁⟩⟩
end
end qg1w8ra
end
section
set_option autoImplicit true
namespace qsiRRIc
theorem proof :qrGSFbd.c1 :=
  qypA4Sc.of_children
    qWnROxa.proof qlcyGcd.proof qrrOjma.proof
end qsiRRIc
end
section
set_option backward.isDefEq.respectTransparency false
namespace q7v3yjb
noncomputable section
open Polynomial Finset
open P5 (p)
open E7 (KB)
open qZu9hjc (valueZeros)
open qNu3xvc (GraphVal Over poleCharge)
open P5_7_1_7_4_3_4 (relativePolar bix)
open qrGSFbd (equation equation_weight guard sections local_sum
  primitive pencilVal avoid_coeffs specialize_zeros nonzero_tilt)
open scoped Classical
open private gauss_of_pencil from ProximityPrize.SubmissionLower.Zk6yNvb
theorem of_children (localOrder :qrGSFbd.c2)
    (qW:q55F46a.c1) (cut:qrGSFbd.c5) :
    qZu9hjc.c2 := by
  intro J U B q Cq S s a R hd hp cfw hguard
  let A:=equation R cfw
  let M:=sections R cfw
  have hd' : 2≤A.d:= by
    change 2≤R.f.natDegree
    rwa [R.degree]
  have hp' : A.d<p:= by
    change R.f.natDegree<p
    rwa [R.degree]
  have hor :=qsiRRIc.proof A hd' hp' (guard R cfw hd hguard)
  let P:=M.marks.sigma fun γ=>(M.den γ).roots.toFinset
  let I := ↥P
  let w (i:I) :=M.place i.1.1
  let x (i:I) :=i.1.2
  have hl (i:I) : ∃ (r :Bool) (v :GraphVal A r),Over v (w i) (x i) ∧
      (M.den i.1.1).rootMultiplicity (x i)≤poleCharge v := by
    obtain ⟨hγ,hx⟩:=mem_sigma.mp i.prop
    exact localOrder A M Cq.curve hd' hp' hor _ hγ _ hx
  choose r v hv using hl
  obtain ⟨G,hpolar,hfresh⟩:=qW A hd' hp' I w x r v (fun i=>(hv i).1)
  have hgauss (j:I) :=gauss_of_pencil Cq.curve G (hv j).1 (hfresh j)
  obtain ⟨G',hTilt,hBase,hCharge⟩:=nonzero_tilt G r v
  let N :=bix G'.base (relativePolar G') G'.finite
  have hm:N.Monic:= by
    let _:=G'.base.toAlgebra
    let _:=G'.finite
    exact LinearMap.charpoly_monic _
  obtain ⟨bad,hcut⟩:=cut A G' a hd' hp' (equation_weight R cfw).le hTilt
  obtain ⟨z,hz,hval⟩:=avoid_coeffs M.marks M.place N bad
  obtain ⟨T,hT⟩:=hcut z hz
  have hn:N.coeff 0≠0:= by
    intro hn
    apply T.constant_ne
    rw [hT,show (bix G'.base (relativePolar G') G'.finite).coeff 0=0 from hn]
    simp [RatFunc.eval]
  have hQ:relativePolar G' ≠ 0:=div_ne_zero G'.polar_ne (pow_ne_zero _ G'.gauge_ne)
  refine ⟨T,fun γ hγ => ?_⟩
  let i (t : ↥(M.den γ).roots.toFinset) :I:=⟨⟨γ,t.1⟩,mem_sigma.mpr ⟨hγ,t.prop⟩⟩
  let u (t : ↥(M.den γ).roots.toFinset) :=(v (i t)).val
  have ⟨hInj,hsum⟩:=local_sum M γ (fun t=>r (i t)) (fun t=>v (i t)) (fun t=>hv (i t))
  let W:=M.place γ
  obtain ⟨F,hF,hInt,hDiv,hZero⟩:=primitive W.value W.normalized N hm hn
  have hNorm:=qaiVg1b.proof W G'.base (relativePolar G') G'.finite G'.separable hQ F hF hInt hDiv
    Finset.univ u hInj.injOn (fun t _=>(v (i t)).normalized)
    (fun t _=> by rw [hBase]; exact hgauss (i t))
  have hSpecial:=specialize_zeros W.value N T.N (fun j=>(congrArg W.value (hT j)).trans (hval γ hγ j))
  calc
    (R.den γ).natDegree ≤ ∑ t,poleCharge (v (i t)) :=hsum
    _ ≤ ∑ t,KB (u t) (relativePolar G') := by
      exact sum_le_sum fun t _=> by
        simpa only [u,poleCharge,KB,hpolar] using hCharge (i t)
    _≤valueZeros (pencilVal W.value) N :=hNorm.trans_eq hZero
    _ = _:=hSpecial.symm
end
end q7v3yjb
end
