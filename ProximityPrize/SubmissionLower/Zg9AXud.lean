import ProximityPrize.SubmissionLower.ZPRNTid
set_option Elab.async false
open _root_ renaming CommRing → za6, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.eval₂Hom → zOD, MvPolynomial.eval₂_X → zUM, MvPolynomial.eval₂_comp_left → zqI
set_option backward.isDefEq.respectTransparency false
namespace qEAs6me
noncomputable section
open cu (L)
open qfbIfsd (Slot form)
open q2tSkEc (bzm caps orders top L4 DetectsValue)
open scoped BigOperators Classical
variable {s b d:ℕ}
private def constSlot (t:Fin 3) :Slot s (caps b s t) (orders d t) :=
 ⟨⟨0,Nat.zero_lt_succ _⟩,⟨0,Nat.zero_lt_succ _⟩⟩
private def defect {M:Type} [za6 M]
  (a :bzm s b d→M) (x y :M) (t:Fin 3) :M :=
 if t=2 then L4 a x y else form a t x y
private def adjust {M:Type} [za6 M]
   (a :bzm s b d→M) (x y :M) (r :bzm s b d) :M :=
 a r - if r.2=constSlot r.1 then defect a x y r.1 else 0
private theorem form_adjust {M:Type} [za6 M]
   (a :bzm s b d→M) (x y :M) (t:Fin 3) :
   form (adjust a x y) t x y=form a t x y - defect a x y t:= by
 simp only [form,adjust,sub_mul,Finset.sum_sub_distrib]
 congr 1
 rw [Finset.sum_eq_single (constSlot t)]
 · simp [constSlot]
 · intro i _ hi
   simp [hi]
 · simp
private theorem top_adjust {M:Type} [za6 M]
  (a :bzm s b d→M) (x y :M) (t:Fin 3) (ht:orders d t≠0) :
  topPoly (adjust a x y) t=topPoly a t:= by
 unfold topPoly
 apply Finset.sum_congr rfl
 intro j _
 have h:topSlot s b d t j≠constSlot t:= fun he =>
  ht (congrArg (fun z :Slot s (caps b s t) (orders d t)=>z.1.val) he)
 simp [adjust,h]
private theorem order_ne (hd:2≤d) (t:Fin 3) :orders d t≠0:= by
 fin_cases t
 · change d≠0; omega
 · change d≠0; omega
 · change d-1≠0; omega
private theorem adjust_forms {M:Type} [za6 M] (hd:2≤d)
   (a :bzm s b d→M) (x y :M) :
   form (adjust a x y) 0 x y=0∧form (adjust a x y) 1 x y=0 ∧
     L4 (adjust a x y) x y=0:= by
 have ht (t:Fin 3) :top (adjust a x y) t x=top a t x := by
   rw [← top_eq_eval,← top_eq_eval,top_adjust _ _ _ _ (order_ne hd t)]
 have h02 : (0:Fin 3)≠2 := by decide
 have h12 : (1 :Fin 3)≠2 := by decide
 refine ⟨?_,?_,?_⟩
 · simp [form_adjust,defect,h02]
 · simp [form_adjust,defect,h12]
 · rw [L4,form_adjust,ht,ht]
   simp only [defect,↓reduceIte,L4]
   ring
private theorem form_map {M N :Type} [CommSemiring M] [CommSemiring N] (m:M →+* N)
  (a :bzm s b d→M) (t:Fin 3) (x y :M) :
  m (form a t x y)=form (m ∘ a) t (m x) (m y) := by
 simp [form]
private theorem value_map {M N :Type} [za6 M] [za6 N] (m:M →+* N)
  (a :bzm s b d→M) (x y :M) :
  m (L4 a x y)=L4 (m ∘ a) (m x) (m y) := by
 have ht (t:Fin 3) :m (top a t x)=top (m ∘ a) t (m x) := by
  simp [top,apply_ite m]
 simp only [L4,map_add,map_sub,map_mul,map_pow,map_natCast,form_map,ht]
private theorem adjust_map {M N :Type} [za6 M] [za6 N] (m:M →+* N)
  (a :bzm s b d→M) (x y :M) (r :bzm s b d) :
  m (adjust a x y r)=adjust (m ∘ a) (m x) (m y) r := by
 simp [adjust,defect,apply_ite m,form_map,value_map,Function.comp_def]
theorem detect_quotient (hd:2≤d) (Q:Coeff s b d)
    (h:DetectsValue (topRes*Q)) :DetectsValue Q:= by
  let A:=MvPolynomial (bzm s b d ⊕ Fin 2) L
  let B:=FractionRing A
  let ι:A →+* B:=algebraMap A B
  let a :bzm s b d→A:=z9v ∘ Sum.inl
  let x :A:=z9v (Sum.inr 0)
  let y :A:=z9v (Sum.inr 1)
  let e :Coeff s b d →+* A:=zOD znf (adjust a x y)
  have he :e (topRes*Q)=0:= by
    apply IsFractionRing.injective A B
    rw [map_zero]
    change ι ((topRes*Q).eval₂ znf (adjust a x y))=0
    rw [zqI]
    have hm:ι ∘ adjust a x y=adjust (ι ∘ a) (ι x) (ι y) :=funext (adjust_map ι a x y)
    rw [hm]
    obtain ⟨h₀,h₁,h₂⟩:=adjust_forms hd (ι ∘ a) (ι x) (ι y)
    exact h _ _ _ _ h₀ h₁ h₂
  have hn:e topRes≠0:= by
    change topRes.eval₂ znf (adjust a x y)≠0
    rw [topRes_eval,top_adjust _ _ _ _ (order_ne hd 0),
      top_adjust _ _ _ _ (order_ne hd 1),← topRes_eval (znf:L →+* A) a]
    intro hz
    apply topRes_ne s b d
    apply MvPolynomial.rename_injective (Sum.inl:bzm s b d→bzm s b d ⊕ Fin 2)
      Sum.inl_injective
    rw [map_zero,MvPolynomial.rename_eq_aeval,MvPolynomial.aeval_def,MvPolynomial.algebraMap_eq]
    exact hz
  have hQ:=(mul_eq_zero.mp ((map_mul e _ _).symm.trans he)).resolve_left hn
  intro M _ m c u v hf hg hv
  let f :A →+* M:=zOD m (Sum.elim c ![u,v])
  have hC:f.comp znf=m:= by
    ext k
    exact MvPolynomial.eval₂Hom_C m (Sum.elim c ![u,v]) k
  have ha :f ∘ a=c:= by
    funext i
    exact zUM m _ _
  have hx :f x=u:=zUM m _ _
  have hy :f y=v :=zUM m _ _
  have harg :f ∘ adjust a x y=c:= by
    funext i
    rw [Function.comp_apply,adjust_map,ha,hx,hy]
    have hdf (t:Fin 3) :defect c u v t=0:= by
      fin_cases t
      · change defect c u v 0=0
        rw [defect,ite_eq_right (by decide)]
        exact hf
      · change defect c u v 1=0
        rw [defect,ite_eq_right (by decide)]
        exact hg
      · change defect c u v 2=0
        rw [defect,ite_eq_left rfl]
        exact hv
    simp [adjust,hdf]
  have eq :=congrArg f hQ
  change f (Q.eval₂ znf (adjust a x y))=f 0 at eq
  rw [zqI,hC,harg,map_zero] at eq
  exact eq
end
end qEAs6me
