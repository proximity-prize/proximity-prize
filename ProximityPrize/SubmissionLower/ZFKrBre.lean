import ProximityPrize.SubmissionLower.ZXTI5ee
set_option Elab.async false
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace qaySLPd
noncomputable section
open Polynomial Finset
open P5 (K)
open P5_7_1
open qH0Nw9c
open cu (FX Jet rD)

open pI (oU)

open atc (bv9)
open akZ (btm bKa)
open scoped Classical


def c1 :Prop :=
  ∀ (f :Jet) (i:Fin 2) (T:TopRow) (B J C U:ℕ),SupportCaps B J C U T →
    oU (pad f i C T)
      ⟨0,B+C*(wD f 0-1),J+C*(wD f 1-1),U+C*wD f 2⟩ ∧
    ∀ (z :K) (S:K[X]),rD f z S=0 →
      rD (pad f i C T) z S =
        (2*rD f.derivative z S)^C*atTop (orient i T) (topLabel i z) S
private theorem separantCaps (f :Jet) :oU f.derivative (btm f) := by
 intro j i h
 rw [coeff_derivative,← Nat.cast_succ,coeff_mul_natCast] at h ⊢
 have hc: (f.coeff (j+1)).coeff i≠0:= by
  intro hz
  exact h (by rw [hz,zero_mul])
 obtain ⟨hb,hj,hu⟩:=bKa f (j+1) i hc
 refine ⟨(Nat.add_le_add_left (Nat.le_succ j) i).trans hb,(Nat.le_succ j).trans hj,?_⟩
 rw [← map_natCast (MvPolynomial.C:FX →+* cu.aZ)]
 exact (MvPolynomial.totalDegree_mul _ _).trans
  (by simpa only [MvPolynomial.totalDegree_C,Nat.add_zero] using hu)
private theorem nonzero_seed {f :Jet} (h:gT.alm f) :0<wD f 2 := by
 rcases h with ⟨j,i,hi⟩
 exact hi.trans_le ((bv9 f (wD f 2)).mp le_rfl j i)
end
end qaySLPd
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q89hPdc
noncomputable section
open cu (L)
open qaySLPd (pe)
open MvPolynomial
open scoped Polynomial
abbrev SeedPoint:=Fin 2→L
def linePoint (s b z :L) :SeedPoint := ![b+s*z,z]
private theorem finite_bad {q g:pe} (hq:Irreducible q) {w:SeedPoint}
  (hw:eval w q=0) (hg:eval w g≠0) :
  {v :SeedPoint | eval v q=0∧eval v g=0}.Finite := by
 let P:Ideal pe :=Ideal.span {q}
 let J:=P ⊔ Ideal.span {g}
 let:UniqueFactorizationMonoid pe :=MvPolynomial.uniqueFactorizationMonoid (Fin 2)
 have hP:P.IsPrime :=
  Ideal.isPrime_span_singleton_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.mp hq)
 have hn:g∉P:= by
  intro h
  obtain ⟨r,hr⟩:=Ideal.mem_span_singleton.mp h
  exact hg (by rw [hr,map_mul,hw,zero_mul])
 have hd: (affineHilbertPolynomial P).natDegree=1 := by
  have h:=natDegree_affineHilbertPolynomial_span_singleton_add_one hq.ne_zero hP.ne_top
  change (affineHilbertPolynomial P).natDegree+1=Nat.card (Fin 2) at h
  rw [Nat.card_eq_fintype_card,Fintype.card_fin] at h
  omega
 have hc:=(principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
  hP hn (le_refl g.totalDegree)).1
 change (affineHilbertPolynomial J).natDegree≤_ at hc
 rw [hd] at hc
 refine ((finite_zeroLocus_iff_natDegree_affineHilbertPolynomial_eq_zero J).2 (by omega)).subset ?_
 intro v hv
 change J≤RingHom.ker (eval v)
 rw [sup_le_iff,Ideal.span_le,Ideal.span_le,Set.singleton_subset_iff,
  Set.singleton_subset_iff]
 exact hv
private theorem eval_at (q:pe) (v :Fin 2→ L[X]) (z :L) :
  (aeval v q:L[X]).eval z=eval (fun i=>(v i).eval z) q:= by
 have h: (Polynomial.aeval z :L[X] →ₐ[L] L).comp (aeval v)=aeval (fun i=>(v i).eval z) :=
  comp_aeval _ _
 exact DFunLike.congr_fun h q
private def vary (q:pe) (a d c:L) :L[X] :=
 aeval ![Polynomial.C a+Polynomial.C d*Polynomial.X,Polynomial.C c] q
private theorem eval_vary (q:pe) (a d c s :L) :
  (vary q a d c).eval s=eval ![a+d*s,c] q:= by
 rw [vary,eval_at]
 congr 2
 funext i
 fin_cases i <;> simp
private theorem zJ {q:pe} (hq:q≠0) (c:L) :
   ∃ u:SeedPoint,eval u q≠0∧u 1≠c:= by
 classical
 have hX: (MvPolynomial.X 1-MvPolynomial.C c:pe)≠0:= by
   intro h
   have he :=congrArg (eval (![0,c+1] :SeedPoint)) h
   simp at he
 have hn:=mul_ne_zero hq hX
 by_contra! h
 apply hn
 apply MvPolynomial.funext
 intro u
 simp only [map_zero,map_mul,map_sub,eval_X,eval_C,mul_eq_zero,sub_eq_zero]
 by_cases hu:eval u q=0
 · exact Or.inl hu
 · exact Or.inr (h u hu)
private def sectionPoly (q:pe) (s b:L) :L[X] :=
 aeval ![Polynomial.C b+Polynomial.C s*Polynomial.X,Polynomial.X] q
private theorem eval_sectionPoly (q:pe) (s b z :L) :
  (sectionPoly q s b).eval z=eval (linePoint s b z) q:= by
 rw [sectionPoly,eval_at]
 congr 2
 funext i
 fin_cases i <;> simp [linePoint]
theorem regular_line {ι:Type*} [Finite ι] (q g:ι→pe) (w:ι→SeedPoint)
    (hq : ∀ i,Irreducible (q i)) (hw : ∀ i,eval (w i) (q i)=0)
    (hg : ∀ i,eval (w i) (g i)≠0) :
    ∃ s b:L,∀ i,∃ z :L,
      eval (linePoint s b z) (q i)=0∧eval (linePoint s b z) (g i)≠0:= by
  classical
  choose u hu hne using fun i=>zJ (hq i).ne_zero (w i 1)
  let A i:=vary (q i) (w i 0) (u i 1 - w i 1) (u i 1)
  have hA (i:ι) :A i≠0:= by
    intro he
    let a :=(u i 0 - w i 0)/(u i 1 - w i 1)
    have hh:w i 0+(u i 1 - w i 1)*a=u i 0:= by
      dsimp [a]
      rw [mul_div_cancel₀ _ (sub_ne_zero.mpr (hne i))]
      ring
    have hv : ![u i 0,u i 1]=u i:= by
      funext j
      fin_cases j <;> rfl
    exact hu i (by simpa only [A,eval_vary,hh,hv,Polynomial.eval_zero] using
      (congrArg (Polynomial.eval a) he))
  obtain ⟨s,hs⟩:=(Set.finite_iUnion fun i=>Polynomial.finite_setOfPred_isRoot (hA i)).exists_notMem
  have hsa (i:ι) : (A i).eval s≠0 :=
    fun h=>hs (Set.mem_iUnion.mpr ⟨i,h⟩)
  let B i:=vary (q i) (s*u i 1) 1 (u i 1) - vary (q i) (s*w i 1) 1 (w i 1)
  have hBval (i:ι) (b:L) :
      (B i).eval b=(sectionPoly (q i) s b).eval (u i 1) -
        (sectionPoly (q i) s b).eval (w i 1) := by
    simp [B,eval_vary,eval_sectionPoly,linePoint,add_comm]
  have hB (i:ι) :B i≠0:= by
    intro he
    let b:=w i 0 - s*w i 1
    have h₁:b+s*u i 1=w i 0+(u i 1-w i 1)*s := by dsimp [b]; ring
    have h₂:b+s*w i 1=w i 0:= by dsimp [b]; ring
    have hvec : ![w i 0,w i 1]=w i:= by funext j; fin_cases j <;> rfl
    have hv :=hBval i b
    rw [he,Polynomial.eval_zero,eval_sectionPoly,eval_sectionPoly,linePoint,linePoint,
      h₁,h₂,hvec,hw,sub_zero,← eval_vary] at hv
    exact hsa i hv.symm
  let C i:=(fun v :SeedPoint=>v 0+(-s)*v 1) ''
    {v :SeedPoint | eval v (q i)=0∧eval v (g i)=0}
  have hC (i:ι) : (C i).Finite :=(finite_bad (hq i) (hw i) (hg i)).image _
  obtain ⟨b,hb⟩:=((Set.finite_iUnion fun i =>
    Polynomial.finite_setOfPred_isRoot (hB i)).union (Set.finite_iUnion hC)).exists_notMem
  refine ⟨s,b,?_⟩
  intro i
  have hd: (sectionPoly (q i) s b).natDegree≠0:= by
    intro h
    have hr : (B i).IsRoot b:= by
      rw [Polynomial.IsRoot.def,hBval,Polynomial.eq_C_of_natDegree_eq_zero h]
      simp
    exact hb (Or.inl (Set.mem_iUnion.mpr ⟨i,hr⟩))
  obtain ⟨z,hz⟩:=IsAlgClosed.exists_root (sectionPoly (q i) s b) (by
    intro h
    exact hd (Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr h.le))
  change (sectionPoly (q i) s b).eval z=0 at hz
  rw [eval_sectionPoly] at hz
  refine ⟨z,hz,fun hn=>hb (Or.inr (Set.mem_iUnion.mpr ⟨i,?_⟩))⟩
  refine ⟨linePoint s b z,⟨hz,hn⟩,?_⟩
  change b+s*z+(-s)*z=b
  ring
end
end q89hPdc
end
