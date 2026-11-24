import ProximityPrize.SubmissionLower.Zw100fa
set_option Elab.async false
open _root_ renaming Fintype.card → zhP, Module.finrank → zsE, MvPolynomial.le_weightedTotalDegree → z6P, MvPolynomial.monomial → ztt, MvPolynomial.optionEquivLeft → zpj, MvPolynomial.uniqueAlgEquiv → zpe, Nat.mul_le_mul_right → ztf, Submodule.subset_span → zBO
set_option backward.isDefEq.respectTransparency false
namespace q5yqMPc
noncomputable section
open Polynomial
open cu (L)
open qBd5KZd (Allowance btN bounded weight j3)
private abbrev Exps :=Option Unit →₀ ℕ
private abbrev Flat (E :Type) [CommSemiring E] :=MvPolynomial (Option Unit) E
variable {E :Type} [Field E]
private def expand:E[X][X] ≃+* Flat E :=
 (Polynomial.mapEquiv (zpe E Unit).toRingEquiv.symm).trans
   (zpj E Unit).toRingEquiv.symm
private theorem aNF (f :E[X][X]) (v :Exps) :
   (expand f).coeff v=(f.coeff (v none)).coeff (v.some ()) := by
 have h:zpj E Unit (expand f) =
     f.map (zpe E Unit).toRingEquiv.symm.toRingHom :=
   (zpj E Unit).toRingEquiv.apply_symm_apply _
 rw [← MvPolynomial.optionEquivLeft_coeff_some_coeff_none,h,Polynomial.coeff_map]
 exact MvPolynomial.coeff_uniqueAlgEquiv_symm E _ _
private def weights (D:ℕ) :Option Unit→ℕ:= fun v=>v.elim D fun _=>1
private theorem c0Q (D:ℕ) (v :Exps) :
  v.weight (weights D)=v.some ()+v none*D:= by
 rw [Finsupp.weight_eq_sum,Fintype.sum_option]
 simp [weights,Finsupp.some_apply,smul_eq_mul,Nat.add_comm]
private theorem weight_expand (D:ℕ) (f :E[X][X]) :
   (expand f).weightedTotalDegree (weights D)=weight D f := by
 apply le_antisymm
 · apply Finset.sup_le
   intro v hv
   have hc:=MvPolynomial.mem_support_iff.mp hv
   rw [aNF] at hc
   have hi:v none∈f.support :=Polynomial.mem_support_iff.mpr
     (fun hz=>hc (by rw [hz,Polynomial.coeff_zero]))
   rw [c0Q]
   apply (Nat.add_le_add_right (le_natDegree_of_ne_zero hc) _).trans
   unfold weight
   exact Finset.le_sup (f := fun i=>(f.coeff i).natDegree+i*D) hi
 · apply Finset.sup_le
   intro i hi
   let v :Exps :=(Finsupp.single () (f.coeff i).natDegree).optionElim i
   have hv :v∈(expand f).support :=MvPolynomial.mem_support_iff.mpr (by
     rw [aNF]
     simpa [v] using leadingCoeff_ne_zero.mpr (Polynomial.mem_support_iff.mp hi))
   simpa [c0Q,v] using z6P (weights D) hv
private abbrev Slot (D j:ℕ) :=Σ k :Fin (j+1),Fin (k.val*D)
private def slotExp {D j:ℕ} (t:Slot D j) :Exps :=
 (Finsupp.single () t.2.val).optionElim (j - t.1.val)
private theorem cp4 (D j:ℕ) :zhP (Slot D j)=j3 D j:= by
 rw [Fintype.card_sigma]
 simp only [Fintype.card_fin]
 simpa only [j3,Nat.mul_zero,Nat.zero_add] using qZCRTge.top_count j 0 D
private theorem slot_of_weight {D j:ℕ} {v :Exps}
  (h:v.weight (weights D)<j*D) :v∈Set.range (@slotExp D j) := by
 rw [c0Q] at h
 have hi:v none<j:=Nat.lt_of_mul_lt_mul_right (by omega :v none*D <j*D)
 have hk :v.some ()<(j - v none)*D:= by rw [Nat.sub_mul]; omega
 refine ⟨⟨⟨j - v none,by omega⟩,⟨v.some (),hk⟩⟩,?_⟩
 unfold slotExp
 rw [show j-(j - v none)=v none by omega,← Finsupp.unique_single v.some,
  Finsupp.optionElim_some]
private def outputs (D j:ℕ) (f :E[X][X]) :Submodule E (Flat E) :=
 Submodule.span E (Set.range fun t:Slot D j=>expand f*ztt (slotExp t) 1)
private theorem mem_outputs {D j W:ℕ} {f G:E[X][X]} (hf :f≠0)
   (hW:W<weight D f) (hG:weight D G<W+1+j*D) (hdiv :f∣G) :
   expand G∈outputs D j f := by
 obtain ⟨q,rfl⟩:=hdiv
 by_cases hq:q=0
 · simp [hq]
 have hw:=MvPolynomial.weightedTotalDegree_mul (weights D) (expand f) (expand q)
   ((map_ne_zero_iff _ expand.injective).mpr hf) ((map_ne_zero_iff _ expand.injective).mpr hq)
 rw [← map_mul,weight_expand,weight_expand,weight_expand] at hw
 have hqWeight: (expand q).weightedTotalDegree (weights D)<j*D:= by
   rw [weight_expand]
   omega
 have hsum:expand (f*q) = ∑ v∈(expand q).support,
     expand f*ztt v ((expand q).coeff v) := by
   rw [map_mul]
   conv_lhs=>rw [(expand q).as_sum,Finset.mul_sum]
 rw [hsum]
 apply Submodule.sum_mem
 intro v hv
 obtain ⟨t,rfl⟩:=slot_of_weight
   ((z6P (weights D) hv).trans_lt hqWeight)
 have hm:expand f*ztt (slotExp t) 1∈outputs D j f :=
   zBO ⟨t,rfl⟩
 simpa only [← mul_smul_comm,MvPolynomial.smul_monomial,smul_eq_mul,mul_one] using
   (outputs D j f).smul_mem ((expand q).coeff (slotExp t)) hm
private theorem coefficient_finrank [Algebra L E] (A:Allowance E)
    [FiniteDimensional L (btN A)] (V:Submodule L E[X][X])
    (U:Submodule E (Flat E)) [FiniteDimensional E U]
    (hU : ∀ G:V,expand G.val∈U) (hA : ∀ G:V,bounded A G.val) :
    zsE L V≤zsE E U*zsE L (btN A) := by
  classical
  let coeff (v :Exps) :Module.Dual E U:=(MvPolynomial.lcoeff E v).comp U.subtype
  obtain ⟨ι,pivot,_,hspan,hli⟩:=exists_linearIndependent' E coeff
  have :Finite ι:=hli.finite
  let:Fintype ι:=Fintype.ofFinite ι
  let project :V →ₗ[L] (ι→btN A) :=LinearMap.pi fun a =>
    { toFun:= fun G=>⟨((G.val.coeff ((pivot a) none)).coeff ((pivot a).some ())),
        hA G _ _⟩
      map_add' := fun G H=>Subtype.ext (by simp only [Submodule.coe_add,Polynomial.coeff_add])
      map_smul' := fun c G=>Subtype.ext (by
        simp only [RingHom.id_apply,Submodule.coe_smul,Polynomial.coeff_smul]) }
  have hzero (G:V) (hg:project G=0) :G=0:= by
    let z :U:=⟨expand G.val,hU G⟩
    let eval :Module.Dual E U →ₗ[E] E :=LinearMap.applyₗ z
    have hz :Submodule.span E (Set.range coeff)≤LinearMap.ker eval := by
      rw [← hspan,Submodule.span_le]
      rintro _ ⟨a,rfl⟩
      change (expand G.val).coeff (pivot a)=0
      rw [aNF]
      exact congrArg (fun g:ι→btN A=>(g a :E)) hg
    apply Subtype.ext
    apply expand.injective
    change expand G.val=expand (0:E[X][X])
    rw [map_zero]
    ext v
    have hv :coeff v∈LinearMap.ker eval :=hz (zBO (Set.mem_range_self v))
    simpa only [AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] using
      (show (expand G.val).coeff v=0 from hv)
  have hinj:Function.Injective project := by
    intro G H hh
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub,hh,sub_self]
  have hi:zhP ι≤zsE E U:= by
    simpa only [Subspace.dual_finrank_eq] using hli.fintype_card_le_finrank
  calc
    _≤zsE L (ι→btN A) :=LinearMap.finrank_le_finrank_of_injective hinj
    _=zhP ι*zsE L (btN A) := by
      rw [Module.finrank_pi_fintype]
      simp
    _≤_:=ztf _ hi
theorem proof :qBd5KZd.c5:= by
 classical
 intro E _ _ D _ _ W j f A V hf _ hW hA hV hdiv
 let U:=outputs D j f
 have :FiniteDimensional E U:=Module.Finite.span_of_finite _ (Set.finite_range _)
 have hU (G:V) :expand G.val∈U :=
  mem_outputs (D:=D) (j:=j) hf hW (hV G.val G.property).2.1 (hdiv G.val G.property)
 have hi:zsE E U≤j3 D j:= by
  rw [← cp4 D j]
  exact finrank_range_le_card _
 exact (coefficient_finrank A V U hU (fun G=>(hV G.val G.property).2.2)).trans
  (ztf _ hi)
end
end q5yqMPc
