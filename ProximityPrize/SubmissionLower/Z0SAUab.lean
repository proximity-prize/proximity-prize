import ProximityPrize.SubmissionLower.ZlMm4ja
import ProximityPrize.SubmissionLower.ZFKrBre
set_option Elab.async false
open _root_ renaming CommRing → za6, Finsupp.degree_apply → zqc, Function.comp_apply → z3s, MvPolynomial → z3y, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.eval → zY9, MvPolynomial.eval_monomial → zSf, MvPolynomial.eval₂Hom → zOD, MvPolynomial.monomial → ztt, MvPolynomial.pderiv_X → zYE, MvPolynomial.pderiv_mul → zGW, RingHom.congr_fun → zLs, RingHom.id → zz4, Submodule.sum_mem → zo3
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace q89hPdc
noncomputable section
open Polynomial Finset
open P5 (K p)
open P5_7_1 (wD)
open qH0Nw9c (LineRow LineCaps)
open qaySLPd (pe RS ConstantFibre)
open cu (L FX aZ Jet kr rD qD jz)
open K1_14_3_4_5 (Lz rowHom_ext)
open MvPolynomial (aeval weightedTotalDegree weightedTotalDegree_mul_le weightedTotalDegree_pow_le
 mem_restrictWeightedDegree_iff_weightedTotalDegree_le pderiv)
open scoped Classical
private abbrev base :L →+* FX:=algebraMap L FX
private abbrev coord (i:Fin 3) :LineRow :=z9v i
private abbrev agl {R:Type*} [za6 R] (s b:R) :Fin 2→z3y (Fin 3) R :=
 ![znf b+MvPolynomial.C s*z9v 0,z9v 0]
private abbrev seed (s b:L) :=agl (base s) (base b)
private def restrict (s b:L) :Jet →+* LineRow :=
 Lz znf (seed s b) (coord 1) (coord 2)
private def witness (z :K) :SeedPoint := ![algebraMap K L z,(algebraMap K L z)^p]
private def JX (w:SeedPoint) :aZ →+* FX:=zY9 (base ∘ w)
private theorem fibre_eval (w:SeedPoint) (S:K[X]) (f :Jet) :
   JX w (RS f S) =
     Lz (zz4 FX) (base ∘ w) (kr S) (kr S.derivative) f := by
 let E :Jet →+* aZ:=eval₂RingHom (evalRingHom (znf (kr S)))
   (znf (kr S.derivative))
 have h: (JX w).comp E=Lz (zz4 FX) (base ∘ w) (kr S) (kr S.derivative) := by
   apply rowHom_ext <;> simp [E,JX,RingHom.comp_apply]
 exact zLs h f
private theorem map_pair (a :L) (n:ℕ) :
   base ∘ (![a,a^n] :SeedPoint) = ![base a,(base a)^n] := by
 funext i
 fin_cases i
 · rfl
 · exact map_pow base a n
private theorem witness_eval (z :K) (S:K[X]) (f :Jet) :
   JX (witness z) (RS f S)=rD f z S:= by
 have hz :base (algebraMap K L z)=jz z := by
   rw [IsScalarTower.algebraMap_apply L L[X] FX]
   rfl
 have hw:base ∘ witness z = ![jz z,(jz z)^p] :=
   (map_pair (algebraMap K L z) p).trans
     (congrArg (fun a :FX=>(![a,a^p] :Fin 2→FX)) hz)
 rw [fibre_eval]
 have h:zOD (zz4 FX) (base ∘ witness z)=qD z := by
   rw [hw]
   rfl
 simp only [Lz,h,rD,coe_eval₂RingHom]
private theorem restrict_eval (s b z :L) (S:K[X]) (f :Jet) :
   zY9 ![base z,kr S,kr S.derivative] (restrict s b f) =
     JX (linePoint s b z) (RS f S) := by
 rw [fibre_eval]
 let E :=zY9 (![base z,kr S,kr S.derivative] :Fin 3→FX)
 have h:E.comp (restrict s b) =
     Lz (zz4 FX) (base ∘ linePoint s b z) (kr S) (kr S.derivative) := by
   apply rowHom_ext
   · simp [E,restrict]
   · intro i
     fin_cases i <;> simp [E,restrict,seed,linePoint,z3s]
   · simp [E,restrict]
   · simp [E,restrict]
 exact zLs h f
private theorem pderiv_eval₂ {R A:Type*} [za6 R] [za6 A]
   (a :R →+* z3y (Fin 3) A) (y :z3y (Fin 3) A)
   (ha : ∀ c,pderiv 2 (a c)=0) (F:R[X]) :
   pderiv 2 (eval₂RingHom a y F)=eval₂RingHom a y F.derivative*pderiv 2 y := by
 induction F using Polynomial.induction_on' with
 | add F G hF hG=>simp only [map_add,hF,hG,add_mul]
 | monomial n c =>
   simp only [coe_eval₂RingHom,eval₂_monomial,derivative_monomial,zGW,
     MvPolynomial.pderiv_pow,ha,map_mul,map_natCast,mul_assoc,mul_left_comm,mul_comm]
   simp
private theorem derivative_line {R:Type*} [za6 R] (s b:R)
    (f : (z3y (Fin 2) R)[X][X]) :
    let E :=Lz znf (agl s b) (z9v 1) (z9v 2)
    pderiv 2 (E f)=E f.derivative := by
  let a :=zOD znf (agl s b)
  have ha (g:z3y (Fin 2) R) :pderiv 2 (a g)=0:= by
    induction g using MvPolynomial.induction_on with
    | C c=>simp [a]
    | add g h hg hh=>simp [hg,hh]
    | mul_X g i hg =>
      have hi:pderiv 2 (agl s b i)=0:= by
        fin_cases i <;> simp [agl,zYE]
      simp only [map_mul,zGW,hg,zero_mul,
        show a (z9v i)=agl s b i by simp [a],hi,mul_zero,add_zero]
  let A:=eval₂RingHom a (z9v 1)
  have hA (g: (z3y (Fin 2) R)[X]) :pderiv 2 (A g)=0 :=
    (pderiv_eval₂ a _ ha g).trans (by simp [zYE])
  exact (pderiv_eval₂ A _ hA f).trans (by rw [MvPolynomial.pderiv_X_self,mul_one]; rfl)
private theorem restrict_derivative (s b:L) (f :Jet) :
  pderiv 2 (restrict s b f)=restrict s b f.derivative :=
 derivative_line (base s) (base b) f
private theorem weight_coord (w:Fin 3→ℕ) (i:Fin 3) :
  weightedTotalDegree w (coord i)=w i:= by
 change weightedTotalDegree w (z9v i:LineRow)= _
 rw [z9v,MvPolynomial.weightedTotalDegree_monomial _ _ _ one_ne_zero,
  Finsupp.weight_single,one_smul]
private theorem bwf (w:Fin 3→ℕ) (s b:L) (g:aZ) :
    weightedTotalDegree w (aeval (seed s b) g)≤w 0*g.totalDegree := by
  have h (i:Fin 2) :weightedTotalDegree w (seed s b i)≤w 0:= by
    fin_cases i
    · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
      apply Submodule.add_mem
      · simp
      · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        exact (weightedTotalDegree_mul_le _ _ _).trans (by simp [weight_coord])
    · exact (weight_coord w 0).le
  apply (MvPolynomial.weightedTotalDegree_aeval_le_of_le (fun _:Fin 2=>w 0) w _ _ h).trans
  apply Finset.sup_le
  intro m hm
  have hm' : m.weight (fun _=>w 0)=m.degree*w 0:= by
    simp only [Finsupp.weight_apply,zqc,Finsupp.sum,Finset.sum_mul,smul_eq_mul]
  rw [hm']
  rw [Nat.mul_comm (w 0),zqc]
  exact Nat.mul_le_mul_right (w 0) (MvPolynomial.le_totalDegree hm)
private theorem bvo (s b:L) (f :Jet) (w:Fin 3→ℕ) (n:ℕ)
   (hn : ∀ j i,i+j≤wD f 0→j≤wD f 1 →
     w 0*wD f 2+i*w 1+j*w 2≤n) :
   weightedTotalDegree w (restrict s b f)≤n:= by
 have he :restrict s b f = ∑ j∈f.support,∑ i∈(f.coeff j).support,
     aeval (seed s b) ((f.coeff j).coeff i)*coord 1^i*coord 2^j:= by
   simp only [restrict,Lz,coe_eval₂RingHom,eval₂_eq_sum,Polynomial.sum_def,
     Finset.sum_mul,MvPolynomial.aeval_eq_eval₂Hom,MvPolynomial.algebraMap_eq,
     MvPolynomial.coe_eval₂Hom]
 rw [he]
 apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
 apply zo3
 intro j _
 apply zo3
 intro i hi
 apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
 obtain ⟨hB,hJ,hU⟩:=akZ.bKa f j i (Polynomial.mem_support_iff.mp hi)
 exact (weightedTotalDegree_mul_le _ _ _).trans
   ((Nat.add_le_add ((weightedTotalDegree_mul_le _ _ _).trans (Nat.add_le_add
     ((bwf w s b _).trans (Nat.mul_le_mul_left _ hU))
     (by simpa only [weight_coord] using weightedTotalDegree_pow_le w (coord 1) i)))
     (by simpa only [weight_coord] using weightedTotalDegree_pow_le w (coord 2) j)).trans
     (hn j i hB hJ))
private theorem restrict_caps (s b:L) (f :Jet) :LineCaps f (restrict s b f) := by
 intro e he
 have hw (w:Fin 3→ℕ) :e.weight w≤weightedTotalDegree w (restrict s b f) :=
   Finset.le_sup (f := fun m=>m.weight w) he
 have h (w:Fin 3→ℕ) :e.weight w=e 0*w 0+e 1*w 1+e 2*w 2 := by
   rw [Finsupp.weight_eq_sum,Fin.sum_univ_three]
   simp [add_assoc]
 refine ⟨?_,?_,?_⟩
 · simpa [h] using (hw ![0,1,1]).trans (bvo s b f ![0,1,1] (wD f 0)
    (fun j i hB _=> by simpa using hB))
 · simpa [h] using (hw ![0,0,1]).trans (bvo s b f ![0,0,1] (wD f 1)
    (fun j i _ hJ=> by simpa using hJ))
 · simpa [h] using (hw ![1,0,0]).trans (bvo s b f ![1,0,0] (wD f 2)
    (fun _ _ _ _=> by simp))
private theorem nonzero_projection (r :aZ) (w:SeedPoint) (h:JX w r≠0) :
    ∃ g:pe,zY9 w g≠0 ∧
      ∀ v,zY9 v g≠0→JX v r≠0:= by
  obtain ⟨l,hl⟩:=Module.Projective.exists_dual_ne_zero L h
  let g:pe := ∑ m∈r.support,ztt m (l (r.coeff m))
  have he (v :SeedPoint) :zY9 v g=l (JX v r) := by
    have hr :JX v r = ∑ m∈r.support,
        r.coeff m*m.prod (fun i n=>(base (v i))^n) := by
      conv_lhs=>rw [r.as_sum]
      change zY9 (base ∘ v) (∑ m∈r.support,
        ztt m (r.coeff m))= _
      simp only [map_sum,zSf,z3s]
    rw [hr,map_sum]
    simp only [map_sum,zSf]
    apply Finset.sum_congr rfl
    intro m _
    have hm:base (m.prod (fun i n=>v i^n)) =
        m.prod (fun i n=>base (v i)^n) := by simp [Finsupp.prod]
    rw [← hm,mul_comm (r.coeff m),← Algebra.smul_def,map_smul]
    exact mul_comm _ _
  exact ⟨g,by simpa only [he] using hl,fun v hv hzero=>hv (by simp [he,hzero])⟩
private theorem curve (f :Jet) (z :K) (S:K[X]) (h:ConstantFibre f z S) :
   ∃ q:pe,Irreducible q∧zY9 (witness z) q=0 ∧
     MvPolynomial.map base q∣RS f S:= by
 rcases h with h | ⟨q,hi,hd,hz⟩
 · let a :=witness z 0
   refine ⟨z9v 0-MvPolynomial.C a,?_,by simp [a],h ▸ dvd_zero _⟩
   let e :=MvPolynomial.finSuccEquiv L 1
   apply (MulEquiv.irreducible_iff e).mp
   change Irreducible (e (z9v 0-MvPolynomial.C a))
   have hc:e (znf a)=Polynomial.C (znf a) := by
     simp [e,MvPolynomial.finSuccEquiv_apply]
   rw [map_sub,show e (z9v 0)=Polynomial.X from MvPolynomial.finSuccEquiv_X_zero,hc]
   exact Polynomial.irreducible_X_sub_C _
 · exact ⟨q,hi,hz,hd⟩
end
end q89hPdc
