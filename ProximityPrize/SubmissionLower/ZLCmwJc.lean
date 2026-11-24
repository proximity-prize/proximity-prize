import ProximityPrize.SubmissionLower.ZZNStjd
set_option Elab.async false
namespace qRIxBbd
noncomputable section
open Polynomial
open cu (L)
open q8Z6NHc (Index)
open qFwMjQd
open scoped Classical
private theorem specialized_coprime {R F E :Type} [CommRing R] [Field F] [Field E]
   (i:R →+* E) (hi:Function.Injective i) (v :R →+* F) (P Q:R[X]) (n:ℕ)
   (hn₀:0<n) (hP:P.natDegree≤n) (hv : (P.map v).natDegree=n)
   (hc:IsCoprime (P.map v) (Q.map v)) :
   (P.map i).natDegree=n∧IsCoprime (P.map i) (Q.map i) := by
 have hd:P.natDegree=n:=le_antisymm hP (hv ▸ natDegree_map_le)
 have hmap :=natDegree_map_eq_of_injective (p:=P) hi
 refine ⟨hmap.trans hd,?_⟩
 have hn:=resultant_ne_zero _ _ hc
 have hle : (Q.map v).natDegree≤Q.natDegree :=natDegree_map_le
 have hp₀:P.map v≠0:=ne_zero_of_natDegree_gt (hv.symm ▸ hn₀)
 have hr : (P.map v).resultant (Q.map v) n Q.natDegree≠0:= by
   rw [← hv,← Nat.add_sub_cancel' hle,
     resultant_add_right_deg _ _ _ _ _ le_rfl,coeff_natDegree]
   exact mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hp₀)) hn
 have hR:P.resultant Q n Q.natDegree≠0:= by
   rw [resultant_map_map] at hr
   exact fun h=>hr (by rw [h,map_zero])
 have hRi:=(map_ne_zero_iff i hi).2 hR
 rw [← resultant_map_map,← hmap.trans hd,← natDegree_map_eq_of_injective (p:= Q) hi] at hRi
 by_contra h
 exact hRi (resultant_eq_zero_iff.mpr
   ⟨Or.inl (ne_zero_of_natDegree_gt ((hmap.trans hd).symm ▸ hn₀)),h⟩)
private theorem sample (m n:ℕ) :
   ∃ A D:L[X],A.Monic∧D.Monic∧A.natDegree=m∧D.natDegree=n ∧
     (A*D).Separable := by
 let e (i:Fin (m+n)) :=Infinite.natEmbedding L i.val
 let f (i:Fin (m+n)) :L[X] :=Polynomial.X - C (e i)
 let A := ∏ i:Fin m,f (i.castAdd n)
 let D := ∏ i:Fin n,f (i.natAdd m)
 have hf (i:Fin (m+n)) : (f i).Monic:=monic_X_sub_C _
 refine ⟨A,D,monic_prod_of_monic _ _ (fun _ _=>hf _),
   monic_prod_of_monic _ _ (fun _ _=>hf _),?_,?_,?_⟩
 · simp [A,f,natDegree_finsetProd_X_sub_C_eq_card]
 · simp [D,f,natDegree_finsetProd_X_sub_C_eq_card]
 · dsimp only [A,D]
   rw [← Fin.prod_univ_add f]
   exact separable_prod_X_sub_C_iff.mpr
     ((Infinite.natEmbedding L).injective.comp Fin.val_injective)
variable {d s a :ℕ}
private abbrev R (d s a :ℕ) :=LineRing (Index d s a)
private def left (b:Bool) (k :ℕ) : (R d s a)[X] :=
 cV k fun i=>MvPolynomial.X (some (b,Sum.inl i))
private def right (b:Bool) (k :ℕ) : (R d s a)[X] :=
 cV k fun i=>MvPolynomial.X (some (b,Sum.inr i))
private def specialize (A D:L[X]) :R d s a →+* L :=
 MvPolynomial.eval₂Hom (RingHom.id _) fun
  | none=>1
  | some (b,Sum.inl i) =>
    if i.val.1.val=d then (if b then (1 :L[X]) else A).coeff i.val.2.val else 0
  | some (b,Sum.inr i) =>
    if i.val.1.val=d then (if b then D else 0).coeff i.val.2.val else 0
private theorem left_specialize (A D:L[X]) (h:d*s≤a) (hA:A.natDegree≤a-d*s)
  (k :ℕ) (b:Bool) :
  (left (d:=d) (s :=s) (a :=a) b k).map (specialize A D) =
    if k=d then if b then 1 else A else 0:= by
 have hdeg: (if b then (1 :L[X]) else A).natDegree≤a-d*s := by cases b <;> simp [hA]
 simpa only [left,grade_map,Function.comp_def,specialize,MvPolynomial.eval₂Hom_X']
  using (grade_fill (d:=d) (s :=s) (a :=a) (l:=k) le_rfl h _ hdeg)
private theorem right_specialize (A D:L[X]) (h:d*s≤a+s+1)
  (hD:D.natDegree≤a+s+1-d*s) (k :ℕ) (b:Bool) :
  (right (d:=d) (s :=s) (a :=a) b k).map (specialize A D) =
    if k=d then if b then D else 0 else 0:= by
 have hdeg: (if b then D else (0:L[X])).natDegree≤a+s+1-d*s := by cases b <;> simp [hD]
 simpa only [right,grade_map,Function.comp_def,specialize,MvPolynomial.eval₂Hom_X']
  using (grade_fill (d:=d) (s :=s) (a :=a+s+1) (l:=k) le_rfl h _ hdeg)
theorem boundary_roots (hd:2≤d) (ha :d*s≤a) (c:L) (hc:c≠0) :
    let E :=Eline d s a
    let f :=fLine d s a
    let g:=gLine d s a
    let A:=Yn f d
    let B:=slope f d
    let D:=slope g d
    let P:=A*D - B*Yn g d
    let V:=B*(Yn f (d-1)+C (lineVar (σ:=Index d s a) none*(algebraMap L E c)^(d-2))) -
      A*slope f (d-1)
    P≠0∧P.roots.toFinset.card=(a-d*s)+(a+s+1-d*s) ∧
      ∀ x∈P.roots.toFinset,P.derivative.eval x≠0∧B.eval x≠0∧V.eval x≠0:= by
  classical
  dsimp only
  let t:=a-d*s
  let u:=a+s+1-d*s
  let A: (R d s a)[X] :=left false d
  let B: (R d s a)[X] :=left true d
  let G: (R d s a)[X] :=right false d
  let D: (R d s a)[X] :=right true d
  let P:=A*D - B*G
  let τ:R d s a :=MvPolynomial.X none*MvPolynomial.C (c^(d-2))
  let V:=B*(left false (d-1)+C τ) - A*left true (d-1)
  let Q:=P.derivative*B*V
  have hA:A.natDegree≤t:=grade_degree _ _ le_rfl
  have hB:B.natDegree≤t:=grade_degree _ _ le_rfl
  have hG:G.natDegree≤u:=grade_degree _ _ le_rfl
  have hD:D.natDegree≤u:=grade_degree _ _ le_rfl
  have hP:P.natDegree≤t+u:=(natDegree_sub_le _ _).trans (max_le
    (natDegree_mul_le.trans (Nat.add_le_add hA hD)) (natDegree_mul_le.trans (Nat.add_le_add hB hG)))
  obtain ⟨A₀,D₀,hmA,hmD,hdA,hdD,hsep⟩:=sample t u
  let v :R d s a →+* L:=specialize A₀ D₀
  have hl:=left_specialize (d:=d) (s :=s) (a :=a) A₀ D₀ ha hdA.le
  have hr :=right_specialize (d:=d) (s :=s) (a :=a) A₀ D₀ (by omega) hdD.le
  have hvP:P.map v=A₀*D₀:= by
    simp [A,B,D,G,P,v,hl,hr]
  have hvτ:v τ=c^(d-2) := by simp [v,τ,specialize]
  have hvV:V.map v=C (c^(d-2)) := by
    have hd' : d-1≠d:= by omega
    simp [V,A,B,hvτ,v,hl,hd']
  have hvQ:Q.map v=(A₀*D₀).derivative*C (c^(d-2)) := by
    simp [Q,← derivative_map,hvP,hvV,B,v,hl]
  have hcop:IsCoprime (P.map v) (Q.map v) := by
    rw [hvP,hvQ,isCoprime_mul_unit_right_right (isUnit_C.mpr (pow_ne_zero _ hc).isUnit)]
    exact hsep
  let E :=Eline d s a
  let i:=algebraMap (R d s a) E
  have hi:Function.Injective i:= by
    rw [show i= _ from IsScalarTower.algebraMap_eq (R d s a) (FractionRing (R d s a)) E]
    exact (algebraMap (FractionRing (R d s a)) E).injective.comp
      (IsFractionRing.injective (R d s a) (FractionRing (R d s a)))
  have hpos :0<t+u:= by dsimp [t,u]; omega
  have hvdeg: (P.map v).natDegree=t+u:= by rw [hvP,hmA.natDegree_mul hmD,hdA,hdD]
  obtain ⟨hdeg,hcop⟩:=specialized_coprime i hi v P Q (t+u) hpos hP hvdeg hcop
  have hpl (b:Bool) (k :ℕ) :
      (left (d:=d) (s :=s) (a :=a) b k).map i =
        if b then slope (fLine d s a) k else Yn (fLine d s a) k := by
    cases b <;> rw [left,grade_map] <;> rfl
  have hpr (b:Bool) (k :ℕ) :
      (right (d:=d) (s :=s) (a :=a) b k).map i =
        if b then slope (gLine d s a) k else Yn (gLine d s a) k := by
    cases b <;> rw [right,grade_map] <;> rfl
  have hiτ:i τ=lineVar (σ:=Index d s a) none*(algebraMap L E c)^(d-2) := by
    change i (MvPolynomial.X none*algebraMap L (R d s a) (c^(d-2)))= _
    rw [map_mul,← IsScalarTower.algebraMap_apply L (R d s a) E,map_pow]
    rfl
  rw [show Q.map i=(P.map i).derivative*(B.map i)*(V.map i) by
    simp [Q,← derivative_map]] at hcop
  have hsep' : (P.map i).Separable :=(IsCoprime.mul_right_iff.mp (IsCoprime.mul_right_iff.mp hcop).1).1
  have hp0:P.map i≠0:=ne_zero_of_natDegree_gt (hdeg.symm ▸ hpos)
  have hc' : (P.map i).roots.toFinset.card=t+u:= by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep'),IsAlgClosed.card_roots_eq_natDegree,hdeg]
  have hgood (x :E) (hx :x∈(P.map i).roots.toFinset) :
      (P.map i).derivative.eval x≠0∧(B.map i).eval x≠0∧(V.map i).eval x≠0:= by
    have hx' : (P.map i).eval x=0:=(mem_roots hp0).mp (Multiset.mem_toFinset.mp hx)
    have hne :=(aeval_ne_zero_of_isCoprime hcop x).resolve_left (by simpa using hx')
    simpa only [coe_aeval_eq_eval,eval_mul,mul_ne_zero_iff,and_assoc] using hne
  simpa [P,V,A,B,G,D,hpl,hpr,hiτ,t,u] using And.intro hp0 (And.intro hc' hgood)
end
end qRIxBbd
