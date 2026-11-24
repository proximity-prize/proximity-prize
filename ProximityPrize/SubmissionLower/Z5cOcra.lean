import ProximityPrize.SubmissionLower.Z62SyBc
set_option Elab.async false
set_option autoImplicit true
open Polynomial renaming eval₂RingHom→qz0
set_option backward.isDefEq.respectTransparency false
namespace qypA4Sc
noncomputable section
open Polynomial qNu3xvc
open cu (L)
open P5 (p)
open scoped WithZero
def c1 :Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E),2≤A.d→A.d<p →
    ∃ q:E[X],q≠0∧q.natDegree≤horizontalDegree A ∧
      ∀ (r :Bool) (v :GraphVal A r),Horizontal v →
        v.val (polar A r)<1→v.val (ajm A q)<1
def c2 :Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E),A.d<p →
    ∀ (r :Bool) (v :GraphVal A r) (h:Horizontal v) (q:E[X]),
      q≠0→q.natDegree<p→v.val (ajm A q)<1→SeparableResidue (a8p v h)
def c3:Prop :=
  ∀ {E F:Type} [Field E] [Field F] [Algebra L E]
    (v :Valuation F ℤᵐ⁰),Function.Surjective v →
    ∀ (i:E →+* v.valuationSubring) (δ:Derivation L E E) (a :v.valuationSubring),
      a≠0→v (a :F)<1→SeparableResidue i →
      let I:Ideal v.valuationSubring :=Ideal.span {a}
      ∃ D:Derivation ℤ (v.valuationSubring ⧸ I) (v.valuationSubring ⧸ I),
        ∀ e,D (Ideal.Quotient.mk I (i e))=Ideal.Quotient.mk I (i (δ e))
private theorem chain {R T:Type} [CommRing R] [CommRing T]
  (D:Derivation ℤ T T) (i:R →+* T) (x :T) (f :R[X]) :
  D (f.eval₂ i x)=(f.sum fun n a=>D (i a)*x^n)+f.derivative.eval₂ i x*D x := by
 rw [eval₂_eq_sum,derivative_apply,eval₂_sum]
 simp only [sum_def,map_sum,Finset.sum_mul]
 rw [← Finset.sum_add_distrib]
 apply Finset.sum_congr rfl
 intro n _
 simp only [D.leibniz,D.leibniz_pow,smul_eq_mul,nsmul_eq_mul,eval₂_mul,
  eval₂_C,eval₂_pow,eval₂_X,eval₂_natCast,map_mul,map_natCast]
 ring
private theorem chain₂ {E T:Type} [Field E] [Algebra L E] [CommRing T]
   (δ:Derivation L E E) (D:Derivation ℤ T T) (i:E →+* T)
   (hδ : ∀ e,D (i e)=i (δ e)) (x y :T) (f :E[X][X]) :
   let j:=qz0 i x
   D (f.eval₂ j y)=(seedDerivative δ f).eval₂ j y +
     (physicalDerivative f).eval₂ j y*D x+f.derivative.eval₂ j y*D y := by
 dsimp
 rw [chain,seedDerivative,physicalDerivative,eval₂_sum,eval₂_sum]
 congr 1
 simp only [sum_def,Finset.sum_mul]
 rw [← Finset.sum_add_distrib]
 apply Finset.sum_congr rfl
 intro n _
 simp only [coe_eval₂RingHom,chain D i x,hδ,eval₂_monomial]
 simp only [sum_def,← coe_eval₂RingHom i x,map_sum]
 simp only [coe_eval₂RingHom,eval₂_monomial]
 ring
variable {E :Type} [Field E]
private theorem chart_root (A:Equation E) (hd:2≤A.d) (r :Bool) :
   KM A r (chartEq A r)=0:= by
 let y :=a7W A Polynomial.X
 have hf :A.f.eval₂ (ajm A) y=0:= by
   rw [ajm,show y=a7W A Polynomial.X from rfl,← hom_eval₂,eval₂_C_X,
     a7W,RingHom.comp_apply,
     AdjoinRoot.mk_self,map_zero]
 cases r
 · exact hf
 have hy :y≠0:= by
   intro hz
   have hm:AdjoinRoot.mk A.f Polynomial.X=0 :=
     IsFractionRing.injective (AdjoinRoot A.f) (EC A) (by simpa [y,a7W] using hz)
   have hh:=natDegree_le_of_dvd (AdjoinRoot.mk_eq_zero.mp hm) Polynomial.X_ne_zero
   rw [natDegree_X] at hh
   change 2≤A.f.natDegree at hd
   omega
 let:=invertibleOfNonzero hy
 change A.f.reverse.eval₂ (ajm A) y⁻¹=0
 simpa only [invOf_eq_inv] using (eval₂_reverse_eq_zero_iff (ajm A) y A.f).2 hf
variable [Algebra L E]
private theorem chartIntegral (A:Equation E) {r :Bool} (v :GraphVal A r)
    (h:Horizontal v) :
    ∃ φ:E[X][X] →+* v.val.valuationSubring,
      (∀ f,(φ f :EC A)=KM A r f) ∧
      φ=qz0 (qz0 (a8p v h) ⟨amm A,v.base_regular⟩)
        ⟨jU A r,v.ordinate_regular⟩:= by
  let x :v.val.valuationSubring :=⟨amm A,v.base_regular⟩
  let y :v.val.valuationSubring :=⟨jU A r,v.ordinate_regular⟩
  let j:=qz0 (a8p v h) x
  let O:=v.val.valuationSubring
  have hj:O.subtype.comp j=ajm A:= by
    apply Polynomial.ringHom_ext
    · intro c
      change O.subtype ((C c).eval₂ (a8p v h) x)=ajm A (C c)
      rw [eval₂_C]
      rfl
    · change O.subtype (Polynomial.X.eval₂ (a8p v h) x)=ajm A Polynomial.X
      rw [eval₂_X]
      rfl
  refine ⟨qz0 j y,fun f => ?_,rfl⟩
  change O.subtype (f.eval₂ j y)=KM A r f
  rw [hom_eval₂,hj]
  rfl
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :qNu3xvc.c2 := by
 intro E _ _ A hd ht hdg r v δ h
 by_contra! hp
 obtain ⟨φ,hφ,hφ'⟩:=chartIntegral A v h
 let f :=chartEq A r
 let O:=v.val.valuationSubring
 let a :O:=φ f.derivative
 let b:O:=φ (physicalDerivative f)
 let n:O:=φ (seedDerivative δ f)
 have he :1<v.val (-(n:EC A)/(a :EC A)) := by
   simpa only [a,n,hφ,f,variation,polar] using hp
 have ha : (a :EC A)≠0:= fun hz=> by simp [hz] at he
 have ha' : 0<v.val (a :EC A) :=pos_iff_ne_zero.mpr (v.val.ne_zero_iff.mpr ha)
 rw [v.val.map_div,v.val.map_neg,lt_div_iff₀ ha',one_mul] at he
 have hs :v.val (a :EC A)<1 :=he.trans_le n.property
 obtain ⟨q,hq,hqd,hzero⟩:=h1 A hd ht
 have hres :=h2 A ht r v h q hq (hqd.trans_lt hdg)
   (hzero r v h (by simpa only [a,hφ,f,polar] using hs))
 let I:Ideal O:=Ideal.span {a}
 let π:=Ideal.Quotient.mk I
 obtain ⟨D,hD⟩:=h3 v.val v.normalized (a8p v h) δ a (fun h0=>ha (by simp [h0])) hs hres
 have hb:π b=0:= by
   have hb' : v.val (-(b:EC A)/(a :EC A))≤1 := by
     simpa only [b,a,hφ,f,jet,polar] using v.jet_regular
   rw [v.val.map_div,v.val.map_neg,div_le_one₀ ha'] at hb'
   apply Ideal.Quotient.eq_zero_iff_mem.mpr
   exact Ideal.mem_span_singleton.mpr ((Valuation.valuationSubring.integers v.val).dvd_iff_le.mpr hb')
 have hz :π (φ f)=0:= by
   have h0:φ f=0:=Subtype.ext (by rw [hφ]; exact chart_root A hd r)
   rw [h0,map_zero]
 have hpa :π a=0:=Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self a)
 let i:=π.comp (a8p v h)
 let x :=π (⟨amm A,v.base_regular⟩:O)
 let y :=π (⟨jU A r,v.ordinate_regular⟩:O)
 have hπ (g:E[X][X]) :π (φ g)=g.eval₂ (qz0 i x) y := by
   rw [hφ']
   change π (g.eval₂ (qz0 (a8p v h) _) _)= _
   rw [hom_eval₂]
   congr 1
   apply Polynomial.ringHom_ext
   · intro c
     simp [i]
   · simp [x]
 have hn:=chain₂ δ D i hD x y f
 dsimp only at hn
 rw [← hπ,← hπ,← hπ,← hπ,hz,D.map_zero,← show n=φ (seedDerivative δ f) from rfl,
   ← show b=φ (physicalDerivative f) from rfl,← show a=φ f.derivative from rfl,
   hb,hpa,zero_mul,zero_mul,add_zero,add_zero] at hn
 have hdvd:a∣n:=Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hn.symm)
 exact (not_le_of_gt he) ((Valuation.valuationSubring.integers v.val).dvd_iff_le.mp hdvd)
end
end qypA4Sc
