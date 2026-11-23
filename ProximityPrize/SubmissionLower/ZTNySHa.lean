import ProximityPrize.SubmissionLower.ZwuC0Sd
set_option Elab.async false
open _root_ renaming DFunLike.congr_fun → zmU, Finsupp.mapDomain_apply_of_injective → zm3, Finsupp.mem_support_iff → zfa, Finsupp.single → zhf, Matrix.cons_val_zero → zbs, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.coeff_monomial → z0I, MvPolynomial.eval₂Hom → zOD, MvPolynomial.eval₂Hom_C → zTv, MvPolynomial.finSuccEquiv → z8s, MvPolynomial.finSuccEquiv_X_zero → zOO, MvPolynomial.finSuccEquiv_apply → zye, MvPolynomial.finSuccEquiv_coeff_coeff → zSI, MvPolynomial.rename → zHw, MvPolynomial.rename_X → z6l, MvPolynomial.ringHom_ext → zXT, Polynomial → zM1, Polynomial.X → z7y, Polynomial.ringHom_ext → z86, RingHom.comp_apply → zQb
set_option maxHeartbeats 800000
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qQCjxhb
noncomputable section
open Polynomial
open P6_7 (RectTail)
open P6_7_2
open cu (FX Jet)
open DP
open gT (Ambient iJ A7 pZ oi)
open private a2f dGs from ProximityPrize.SubmissionLower.Z
theorem toEvaluated {b:RectTail} {x :Input b} (P:Poles x) (r :sk) (W:ℕ) :
    rectRows P r W≤P.rows (rectShape b r) W :=
  Submodule.span_mono (Set.image_mono inf_le_left)
private def order :Fin 4→Fin 4 := ![2,3,1,0]
private theorem order_inj:Function.Injective order := by decide
private def flatten (F:Ambient) :Jet :=
  Polynomial.map (z8s FX 2).toRingHom
    (z8s FX 3 (zHw order F))
private theorem flatten_toJet (G:Jet) :flatten (iJ G)=G:= by
  let f :Ambient →+* Jet :=
    (Polynomial.mapRingHom (z8s FX 2).toRingHom).comp
      ((z8s FX 3).toRingHom.comp (zHw order).toRingHom)
  have f_apply (F:Ambient) :f F =
      Polynomial.map (z8s FX 2).toRingHom
        (z8s FX 3 (zHw order F)) :=rfl
  have fv :f (z9v 3)=(z7y:Jet) := by
    rw [f_apply,z6l,show order 3=0 from rfl,
      zOO,Polynomial.map_X]
  have fy :f (z9v 2)=C (z7y:cu.Equation) := by
    rw [f_apply,z6l,show order 2=(0:Fin 3).succ from rfl,
      MvPolynomial.finSuccEquiv_X_succ,Polynomial.map_C]
    change C (z8s FX 2 (z9v 0))= _
    rw [zOO]
  have fs (i:Fin 2) :f (MvPolynomial.X (Fin.castLE (by decide) i)) =
      C (C (MvPolynomial.X i:cu.aZ)) := by
    have hi:order (Fin.castLE (by decide) i)=i.succ.succ:= by
      fin_cases i <;> rfl
    rw [f_apply,MvPolynomial.rename_X,hi,MvPolynomial.finSuccEquiv_X_succ,Polynomial.map_C]
    change C (MvPolynomial.finSuccEquiv FX 2 (MvPolynomial.X i.succ))= _
    rw [MvPolynomial.finSuccEquiv_X_succ]
  have fc (a :FX) :f (znf a)=C (C (znf a :cu.aZ)) := by
    rw [f_apply,MvPolynomial.rename_C]
    simp only [zye,zTv,zQb,
      Polynomial.map_C]
    change C (z8s FX 2 (znf a))= _
    simp [zye]
  change (f.comp iJ) G=G
  have h:f.comp iJ=RingHom.id Jet:= by
    apply z86
    · intro R
      have hr : (f.comp iJ).comp C=C:= by
        apply z86
        · intro A
          have hs : ((f.comp iJ).comp C).comp C =
              (C:cu.Equation →+* Jet).comp (C:cu.aZ →+* cu.Equation) := by
            apply zXT
            · intro a
              simpa [iJ,A7,pZ,oi] using fc a
            · intro i
              fin_cases i
              · simpa [iJ,A7,pZ,oi] using fs 0
              · simpa [iJ,A7,pZ,oi] using fs 1
          exact zmU hs A
        · simpa [iJ,A7,oi] using fy
      exact zmU hr R
    · simpa [iJ] using fv
  exact zmU h G
private theorem coeff_toJet (G:Jet) (a :Fin 4 →₀ ℕ) :
    (iJ G).coeff a=((G.coeff (a 3)).coeff (a 2)).coeff
      (Finsupp.equivFunOnFinite.symm ![a 0,a 1]) := by
  let d:Fin 2 →₀ ℕ:=Finsupp.equivFunOnFinite.symm ![a 0,a 1]
  have he :Finsupp.cons (a 3) (Finsupp.cons (a 2) d)=a.mapDomain order := by
    ext i
    fin_cases i
    · exact (zm3 order_inj a 3).symm
    · exact (zm3 order_inj a 2).symm
    · exact (zm3 order_inj a 0).symm
    · exact (zm3 order_inj a 1).symm
  conv_rhs=>rw [← flatten_toJet G]
  rw [flatten,Polynomial.coeff_map]
  change _=((z8s FX 2
    ((z8s FX 3 (zHw order (iJ G))).coeff (a 3))).coeff
      (a 2)).coeff d
  rw [zSI,zSI,
    he,MvPolynomial.coeff_rename_mapDomain _ order_inj]
theorem caps {b:RectTail} {x :Input b} (P:Poles x) {W:ℕ} {G:Jet}
    (hG:G∈rectRows P (full b) W) {a :Fin 4 →₀ ℕ} (ha :a∈(iJ G).support) :
    a 0≤(Bs b).terminal.U∧a 1≤(Bs b).terminal.U ∧
      a 2+a 3≤(Bs b).terminal.B∧a 3≤(Bs b).terminal.J:= by
  let d:Fin 2 →₀ ℕ:=Finsupp.equivFunOnFinite.symm ![a 0,a 1]
  have hc: ((G.coeff (a 3)).coeff (a 2)).coeff d≠0:= by
    simpa only [MvPolynomial.mem_support_iff,coeff_toJet] using ha
  have hj:=d3r P.crt x.word (toEvaluated P (full b) W hG) (a 3) (a 2)
    (fun hz=>hc (by rw [hz,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]))
  have hs :a 0≤(full b).z∧a 1≤(full b).t:= by
    by_contra hn
    have hb: (full b).z<d 0∨(full b).t<d 1 := by
      change (full b).z<a 0∨(full b).t<a 1
      omega
    let f :=a2f (a 3) (a 2) d
    have hsub:rectRows P (full b) W≤LinearMap.ker f :=Submodule.span_le.mpr (by
      rintro _ ⟨Q,hQ,rfl⟩
      apply LinearMap.mem_ker.mpr
      apply dGs
      intro k
      exact hQ.2 _ _ _ _ hb)
    exact hc (LinearMap.mem_ker.mp (hsub hG))
  exact ⟨hs.1,hs.2,hj.1,hj.2.1⟩
end
end qQCjxhb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qQCjxhb
noncomputable section
open Polynomial
open P6 (K)
open cu (Jet A5)
open gT (Ambient iJ aci)
open Rk (KR cGi bh9)
open private translation gDX aAh from ProximityPrize.SubmissionLower.A0
private theorem axis_taylor (i:Fin 4) (F:Ambient) :
    zOD C (fun j=>if j=i then z7y else 0) (Rk.taylor F) =
      translation i F:= by
  let ev :MvPolynomial (Fin 4) Ambient →+* zM1 Ambient :=
    zOD C (fun j=>if j=i then z7y else 0)
  have he :ev.comp Rk.taylor=translation i:= by
    apply zXT
    · intro c
      simp [ev,Rk.taylor,translation]
    · intro j
      simp [ev,Rk.taylor,translation,add_comm]
  exact zmU he F
private theorem axis_coeff_ambient (i:Fin 4) (r :ℕ)
    (F:MvPolynomial (Fin 4) Ambient) :
    (zOD C (fun j=>if j=i then z7y else 0) F).coeff r =
      F.coeff (zhf i r) := by
  classical
  induction F using MvPolynomial.induction_on' with
  | add P Q hp hq =>
    simp only [map_add,Polynomial.coeff_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hp,hq]
  | monomial a c =>
    by_cases h : ∃ j∈a.support,j≠i
    · obtain ⟨j,hj,hji⟩:=h
      have hn:a≠zhf i r := by
        intro he
        simp [he,hji,zfa] at hj
      simp only [MvPolynomial.eval₂Hom_monomial,Finsupp.prod,z0I,
        hn,ite_false]
      rw [Finset.prod_eq_zero hj (by simp [hji,Finsupp.mem_support_iff.mp hj]),
        mul_zero,Polynomial.coeff_zero]
    · have he :a=zhf i (a i) := by
        ext j
        by_cases hji:j=i
        · subst j
          simp
        · have hj:j∉a.support := fun hj=>h ⟨j,hj,hji⟩
          simp [hji,Finsupp.notMem_support_iff.mp hj]
      rw [he]
      conv_lhs=>rw [← MvPolynomial.C_mul_X_pow_eq_monomial]
      simp only [map_mul,map_pow,zTv,MvPolynomial.eval₂Hom_X',
        ite_true,Polynomial.coeff_C_mul_X_pow,z0I]
      have hr :zhf i (a i)=zhf i r↔a i=r := by
        constructor
        · intro he'
          simpa using congrArg (fun g:Fin 4 →₀ ℕ=>g i) he'
        · intro he'
          rw [he']
      simp only [hr,eq_comm]
private theorem seed_partial (i:Fin 2) (r :ℕ) (G:Jet) :
    KR (zhf (aAh i) r) (iJ G)=iJ (A5 i r G) := by
  rw [KR,← axis_coeff_ambient,axis_taylor,gDX]
theorem seed_extract (z :K) (S:K[X]) (G:Jet) (a :Fin 4 →₀ ℕ) :
    let d:=zhf 2 (a 2)+Finsupp.single 3 (a 3)
    (jA.translate (point z S) (iJ (A5 1 (a 1) (A5 0 (a 0) G)))).coeff d =
      (jA.translate (point z S) (iJ G)).coeff a := by
  dsimp only
  rw [← seed_partial,← seed_partial,bh9,bh9]
  let d:Fin 4 →₀ ℕ:=zhf 2 (a 2)+Finsupp.single 3 (a 3)
  let e₀:Fin 4 →₀ ℕ:=zhf 0 (a 0)
  let e₁:Fin 4 →₀ ℕ:=zhf 1 (a 1)
  change (KR e₁ (KR e₀ (jA.translate (point z S) (iJ G)))).coeff d= _
  rw [cGi _ _ _ (show ∀ i,i∉e₁.support∨i∉d.support by
        intro i; fin_cases i <;> simp [d,e₁,zfa]),
      cGi _ _ _ (show ∀ i,i∉e₀.support∨i∉(e₁+d).support by
        intro i; fin_cases i <;> simp [d,e₀,e₁,zfa])]
  congr 1
  ext i
  fin_cases i <;> simp [d,e₀,e₁]
theorem eval_hasse (z :K) (S:K[X]) (F:Ambient) (a :Fin 4 →₀ ℕ) :
    aci z S (KR a F)=(jA.translate (point z S) F).coeff a := by
  have he : (MvPolynomial.map (aci z S)).comp Rk.taylor=jA.translate (point z S) := by
    apply zXT
    · intro c
      simp [Rk.taylor,jA.translate,aci]
    · intro i
      simp [Rk.taylor,jA.translate,aci,point]
  rw [KR,← MvPolynomial.coeff_map]
  exact congrArg (fun G:Ambient=>G.coeff a) (zmU he F)
end
end qQCjxhb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxSynthPendingDepth 16
namespace qzFnQja
noncomputable section
open Polynomial
open P6 (K)
open cu (L FX j9 kr jz)
open DP
open bax (adA bFk ab3)
open gT (Ambient iJ A7 oi pZ)
open qQCjxhb (inc line point)
open scoped Polynomial
abbrev Param:=zM1 L[X]
def aIh (S V:L[X]) :Param :=
  C S+C V*z7y
def sourceLine (t:Fin 2→L) (S V:L[X]) :Source →+* Param :=
  adA (C.comp (C.comp (MvPolynomial.eval t))) (C z7y)
    (aIh S V) (aIh S.derivative V.derivative)
theorem sourceLine_eval (t:Fin 2→L) (S V:L[X]) (c:L) (Q:Source) :
    (sourceLine t S V Q).eval (C c)=ab3 t (S+C c*V) Q:= by
  change ((evalRingHom (C c)).comp (sourceLine t S V)) Q=ab3 t (S+C c*V) Q
  apply zmU
  apply bFk <;>
    simp [zQb,sourceLine,aIh,ab3,derivative_add,
      derivative_mul] <;> ring
private def Fp (t:Fin 2→L) (S V:L[X]) :Fin 4→zM1 FX :=
  ![C (inc (C (t 0))),C (inc (C (t 1))),
    C (inc S)+C (inc V)*z7y,
    C (inc S.derivative)+C (inc V.derivative)*z7y]
private theorem sourceLine_map_aux (t:Fin 2→L) (S V:L[X]) (Q:Source) :
    (sourceLine t S V Q).map inc =
      zOD C (Fp t S V) (iJ (U4 Q)) := by
  let ev :Ambient →+* zM1 FX:=zOD C (Fp t S V)
  let f :=(mapRingHom inc).comp (sourceLine t S V)
  let g:=ev.comp (iJ.comp U4.toRingHom)
  change f Q=g Q
  apply zmU
  apply bFk
  · intro P
    let j:qC →+* Source :=C.comp (C.comp C)
    change (f.comp j) P=(g.comp j) P
    apply zmU
    apply zXT
    · intro a
      simp [f,g,j,ev,sourceLine,zQb,U4,iJ,A7,
        oi,pZ,IsScalarTower.algebraMap_apply L L[X] FX]
    · intro i
      fin_cases i <;> simp [f,g,j,ev,sourceLine,zQb,U4,iJ,
        A7,oi,pZ,Fp]
  · simp [f,g,ev,sourceLine,zQb,U4,iJ,A7,oi,pZ]
  · simp [f,g,ev,sourceLine,zQb,U4,iJ,A7,oi,
      aIh,Fp]
  · simp [f,g,ev,sourceLine,zQb,U4,iJ,aIh,Fp]
private theorem seed_zero (z :K) (S:K[X]) :
    inc (C (Z7 z 0))=point z S 0:= by
  simp only [point,Z7,zbs,jz,zQb]
private theorem seed_one_at (z :K) (y v :FX) (n:ℕ) :
    inc (C (![algebraMap K L z,(algebraMap K L z)^n] (1 :Fin 2))) =
      ![jz z,(jz z)^n,y,v] (1 :Fin 4) := by
  simp only [Matrix.cons_val_one,zbs,jz,zQb,map_pow]
private theorem seed_one (z :K) (S:K[X]) :
    inc (C (Z7 z 1))=point z S 1 :=
  seed_one_at z (kr S) (kr S.derivative) K1.p
private theorem jet_two (z :K) (S:K[X]) :inc (j9 S)=point z S 2 := by
  simp only [point,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,kr]
private theorem jet_three (z :K) (S:K[X]) :
    inc (j9 S).derivative=point z S 3:= by
  simp only [point,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,kr,j9,
    derivative_map]
theorem sourceLine_map (z :K) (S:K[X]) (V:L[X]) (Q:Source) :
    (sourceLine (Z7 z) (j9 S) V Q).map inc =
      line (iJ (U4 Q)) z S (inc V) (inc V.derivative) := by
  simp only [sourceLine_map_aux,line,Fp,seed_zero z S,seed_one z S,
    jet_three z S,jet_two z S]
end
end qzFnQja
end
