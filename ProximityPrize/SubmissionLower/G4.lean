import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.G3
namespace ProximityPrize.SubmissionLower.PlaneFunctionFieldDegree
open PlaneCoefficientExtension
noncomputable section
section Evaluation
variable (K E:Type) [Field K] [Field E] [Algebra K E]
def planeEval (y r:E):Polynomial (Polynomial K) →+*E:=
 (Polynomial.evalRingHom r).comp
   (Polynomial.mapRingHom (Polynomial.eval₂RingHom (algebraMap K E) y))
def relationIdeal (y r:E):Ideal (Polynomial (Polynomial K)):=
 RingHom.ker (planeEval K E y r)
theorem planeEval_eq (y r:E) (P:Polynomial (Polynomial K)):
   planeEval K E y r P=
     ((bimap (algebraMap K E) P).map (Polynomial.evalRingHom y)).eval r:=by
 simp only [planeEval,RingHom.comp_apply,Polynomial.coe_mapRingHom,
   Polynomial.coe_evalRingHom]
 rw [bimap_specialization]
variable (Ω:Type) [Field Ω] [Algebra K Ω]
theorem algHom_planeEval (φ:E →ₐ[K] Ω) (y r:E)
   (P:Polynomial (Polynomial K)):
   φ (planeEval K E y r P)=planeEval K Ω (φ y) (φ r) P:=by
 rw [planeEval_eq,planeEval_eq]
 have h:=bimap_eval_natural φ.toRingHom
   (bimap (algebraMap K E) P) y r
 have hcomp:φ.toRingHom.comp (algebraMap K E)=algebraMap K Ω:=by
   ext a
   exact φ.commutes a
 rw [bimap_comp,hcomp] at h
 exact h.symm
theorem algHom_eq_of_generating_pair (y r:E)
   (hgen:IntermediateField.adjoin K ({y,r}:Set E)=⊤)
   (φ ψ:E →ₐ[K] Ω) (hy:φ y=ψ y) (hr:φ r=ψ r):φ=ψ:=by
 apply AlgHom.ext
 intro x
 have hx:x∈IntermediateField.adjoin K ({y,r}:Set E):=by
   rw [hgen]
   trivial
 exact IntermediateField.adjoin_induction K
   (p:=fun a _ => φ a=ψ a)
   (fun a ha => by
     rcases Set.mem_insert_iff.mp ha with h | h
     · simpa only [h] using hy
     · simpa only [Set.mem_singleton_iff.mp h] using hr)
   (fun a => by rw [φ.commutes,ψ.commutes])
   (fun a b _ _ ha hb => by simp only [map_add,ha,hb])
   (fun a _ ha => by simp only [map_inv₀,ha])
   (fun a b _ _ ha hb => by simp only [map_mul,ha,hb]) hx
theorem embedding_pair_injective (y r:E)
   (hgen:IntermediateField.adjoin K ({y,r}:Set E)=⊤):
   Function.Injective (fun φ:E →ₐ[K] Ω => (φ y,φ r)):=by
 intro φ ψ h
 exact algHom_eq_of_generating_pair K E Ω y r hgen φ ψ
   (congrArg Prod.fst h) (congrArg Prod.snd h)
variable (E':Type) [Field E'] [Algebra K E']
theorem relationIdeal_eq_of_embedding_pairs_eq
   (y r:E) (y' r':E') (φ:E →ₐ[K] Ω) (ψ:E' →ₐ[K] Ω)
   (hy:φ y=ψ y') (hr:φ r=ψ r'):
   relationIdeal K E y r=relationIdeal K E' y' r':=by
 apply Ideal.ext
 intro P
 change planeEval K E y r P=0 ↔ planeEval K E' y' r' P=0
 have heq:φ (planeEval K E y r P)=ψ (planeEval K E' y' r' P):=by
   rw [algHom_planeEval,algHom_planeEval,hy,hr]
 constructor
 · intro h
   apply ψ.injective
   simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,h,map_zero] using heq.symm
 · intro h
   apply φ.injective
   simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,h,map_zero] using heq
end Evaluation
section SingleField
variable (K E:Type) [Field K] [Field E] [Algebra K E]
 [FiniteDimensional K E] [Algebra.IsSeparable K E]
theorem finrank_le_planar_bound
   (P Q:Polynomial (Polynomial K))
   (hP:Irreducible P) (hdeg:0 < P.natDegree) (hproper:¬ P∣Q)
   (y r:E) (hgen:IntermediateField.adjoin K ({y,r}:Set E)=⊤)
   (hPy:planeEval K E y r P=0) (hQy:planeEval K E y r Q=0):
   Module.finrank K E ≤ Q.natDegree*Polynomial.Bivariate.degreeX P+
     P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 classical
 let Ω:=AlgebraicClosure E
 letI:Fintype (E →ₐ[K] Ω):=Fintype.ofFinite _
 let points:Finset (Ω × Ω):=Finset.univ.image (fun φ:E →ₐ[K] Ω => (φ y,φ r))
 have hcard:points.card=Module.finrank K E:=by
   rw [Finset.card_image_of_injective _ (embedding_pair_injective K E Ω y r hgen),
     Finset.card_univ,Fintype.card_eq_nat_card]
   exact Field.finSepDegree_eq_finrank_of_isSeparable K E
 rw [←hcard]
 apply common_points_card_le_after_extension (algebraMap K Ω) P Q points hP hdeg hproper
 intro point hp
 obtain ⟨φ,_,rfl⟩:=Finset.mem_image.mp hp
 constructor
 · rw [←planeEval_eq]
   rw [←algHom_planeEval K E Ω φ y r P,hPy,map_zero]
 · rw [←planeEval_eq]
   rw [←algHom_planeEval K E Ω φ y r Q,hQy,map_zero]
end SingleField
section FiniteFamily
variable (K:Type) [Field K]
variable {I:Type} [Fintype I] (E:I → Type)
 [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
 [∀ i,FiniteDimensional K (E i)] [∀ i,Algebra.IsSeparable K (E i)]
theorem sum_finrank_le_planar_bound
   (P Q:Polynomial (Polynomial K))
   (hP:Irreducible P) (hdeg:0 < P.natDegree) (hproper:¬ P∣Q)
   (y r:∀ i,E i)
   (hgen:∀ i,IntermediateField.adjoin K ({y i,r i}:Set (E i))=⊤)
   (hkernels:Function.Injective (fun i => relationIdeal K (E i) (y i) (r i)))
   (hPy:∀ i,planeEval K (E i) (y i) (r i) P=0)
   (hQy:∀ i,planeEval K (E i) (y i) (r i) Q=0):
   (∑ i,Module.finrank K (E i)) ≤
     Q.natDegree*Polynomial.Bivariate.degreeX P+
       P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 classical
 let Ω:=AlgebraicClosure K
 letI:∀ i,Fintype (E i →ₐ[K] Ω):=fun i => Fintype.ofFinite _
 let pair:(Σ i,E i →ₐ[K] Ω) → Ω × Ω:=
   fun a => (a.2 (y a.1),a.2 (r a.1))
 have hinj:Function.Injective pair:=by
   rintro ⟨i,φ⟩ ⟨j,ψ⟩ h
   have hij:i=j:=hkernels
     (relationIdeal_eq_of_embedding_pairs_eq K (E i) Ω (E j)
       (y i) (r i) (y j) (r j) φ ψ (congrArg Prod.fst h) (congrArg Prod.snd h))
   subst j
   have heq:φ=ψ:=algHom_eq_of_generating_pair K (E i) Ω
     (y i) (r i) (hgen i) φ ψ (congrArg Prod.fst h) (congrArg Prod.snd h)
   exact congrArg (Sigma.mk i) heq
 let points:Finset (Ω × Ω):=Finset.univ.image pair
 have hcard:points.card=∑ i,Module.finrank K (E i):=by
   rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_sigma]
   apply Finset.sum_congr rfl
   intro i _
   rw [Fintype.card_eq_nat_card,
     ←Field.finSepDegree_eq_of_isAlgClosed K (E i) Ω,
     Field.finSepDegree_eq_finrank_of_isSeparable]
 rw [←hcard]
 apply common_points_card_le_after_extension (algebraMap K Ω) P Q points hP hdeg hproper
 intro point hp
 obtain ⟨⟨i,φ⟩,_,rfl⟩:=Finset.mem_image.mp hp
 change
   ((bimap (algebraMap K Ω) P).map (Polynomial.evalRingHom (φ (y i)))).eval (φ (r i))=0∧
   ((bimap (algebraMap K Ω) Q).map (Polynomial.evalRingHom (φ (y i)))).eval (φ (r i))=0
 constructor
 · rw [←planeEval_eq, ←algHom_planeEval K (E i) Ω φ (y i) (r i) P,hPy i,map_zero]
 · rw [←planeEval_eq, ←algHom_planeEval K (E i) Ω φ (y i) (r i) Q,hQy i,map_zero]
end FiniteFamily
end
end ProximityPrize.SubmissionLower.PlaneFunctionFieldDegree
