import ProximityPrize.SubmissionLower.ZT8CHOb
set_option Elab.async false
section
namespace q55F46a
noncomputable section
open Polynomial Finset qNu3xvc
open P5 (p)

open P5_7_1_7_4_3_4 (Pencil relativePolar adG)
open cu (L)
open E7 (CurveField CurvePlace)

open scoped Classical WithZero
open private cfl b4u from ProximityPrize.SubmissionLower.A3
def c1 :Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E),2≤A.d→A.d<p →
    ∀ (ι:Type) [Fintype ι] (w:ι→CurvePlace L E) (x :ι→L) (r :ι→Bool)
      (v : ∀ i,GraphVal A (r i)),(∀ i,Over (v i) (w i) (x i)) →
      ∃ C:Pencil A,(∀ i,(v i).val (relativePolar C)=(v i).val (polar A (r i))) ∧
        ∀ i (g:L[X]),g≠0 →
          (v i).val (g.eval₂ ((seed A).comp (algebraMap L E)) (C.base RatFunc.X))=1
private theorem gauss_of_pencil {E :Type} [Field E] [Algebra L E] {A:Equation E}
   {r :Bool} {v :GraphVal A r} {w:CurvePlace L E} {x :L}
   (hc:CurveField L E) (C:Pencil A) (hv :Over v w x)
   (hfresh : ∀ g:L[X],g≠0 →
     v.val (g.eval₂ ((seed A).comp (algebraMap L E)) (C.base RatFunc.X))=1) :
   ∃ n:ℕ,0<n ∧ ∀ g:E[X],
     v.val (C.base (algebraMap E[X] (RatFunc E) g))=adG w.value g^n:= by
 obtain ⟨n,hn,hrest⟩:=hv.1
 refine ⟨n,hn,fun g => ?_⟩
 have hnt : ∃ t:E,t≠0∧w.value t≠1 := by
   obtain ⟨t,ht⟩:=w.normalized (WithZero.exp (-1 :ℤ))
   refine ⟨t,w.value.ne_zero_iff.mp (ht ▸ ?_),?_⟩
   · exact WithZero.exp_ne_zero
   · simp [ht]
 have hres (a :E) (ha :v.val (seed A a)≤1) :
     ∃ c:L,v.val (seed A (a-algebraMap L E c))<1 := by
   have hw:w.value a≤1 :=
     le_of_not_gt fun h=>(not_lt_of_ge ha) (hrest a ▸ one_lt_pow₀ h hn.ne')
   obtain ⟨c,h⟩:=cfl hc w.value ⟨w.on_constants⟩ hnt a hw
   refine ⟨c,?_⟩
   rw [hrest]
   simpa only [one_pow] using pow_lt_pow_left₀ h zero_le hn.ne'
 have ha :v.val (C.base RatFunc.X)=1 := by
   simpa only [eval₂_X] using hfresh Polynomial.X Polynomial.X_ne_zero
 have hs :C.base.comp RatFunc.C=seed A:=RingHom.ext C.base_seed
 have heval :C.base (algebraMap E[X] (RatFunc E) g) =
     g.eval₂ (seed A) (C.base RatFunc.X) := by
   rw [← hs,← RatFunc.algebraMap_comp_C,← RatFunc.algebraMap_X,
     ← Polynomial.hom_eval₂,← Polynomial.hom_eval₂,eval₂_C_X]
 rw [heval,b4u (seed A) _ v.val ha hres hfresh,adG]
 simp only [hrest]
 exact (Finset.apply_sup_eq_sup_comp_of_linearOrder (fun a :ℤᵐ⁰=>a^n)
   (fun _ _ hab=>pow_le_pow_left₀ zero_le hab n) (zero_pow hn.ne')).symm
end
end q55F46a
end
section
namespace qfbIfsd
noncomputable section
open Polynomial
open scoped BigOperators
open cu (L)
open qNu3xvc (Equation)
open P5_7_1_7_4_3_4 (Pencil pairDegree)
abbrev Slot (s b e :ℕ) :=Σ i:Fin (e+1),Fin (b+(e-i.val)*s+1)
abbrev Vars (s :ℕ) (b e :Fin 3→ℕ) :=Σ t:Fin 3,Slot s (b t) (e t)
def kK (s :ℕ) (b e :Fin 3→ℕ) :ℕ :=
 pairDegree s (b 0) (e 0) (b 1) (e 1) +
 pairDegree s (b 0) (e 0) (b 2) (e 2) +
 pairDegree s (b 1) (e 1) (b 2) (e 2)
def form {M:Type} [CommSemiring M] {s :ℕ} {b e :Fin 3→ℕ}
    (a :Vars s b e→M) (t:Fin 3) (x y :M) :M :=
  ∑ i:Slot s (b t) (e t),a ⟨t,i⟩*x^i.2.val*y ^i.1.val
def Detects {s :ℕ} {b e :Fin 3→ℕ} (R:MvPolynomial (Vars s b e) L) :Prop :=
  ∀ {M:Type} [Field M] (m:L →+* M) (a :Vars s b e→M) (x y :M),
    (∀ t,form a t x y=0)→R.eval₂ m a=0
abbrev baseCap {E :Type} [Field E] (A:Equation E) :Fin 3→ℕ :=
 ![A.b,A.b+A.s+1,A.b]
abbrev ordCap {E :Type} [Field E] (A:Equation E) :Fin 3→ℕ :=
 ![A.d,A.d,A.d-1]
abbrev Index {E :Type} [Field E] (A:Equation E) :=Vars A.s (baseCap A) (ordCap A)
def const₂ {E :Type} [CommSemiring E] :E →+* E[X][X] :=
 Polynomial.C.comp Polynomial.C
def gaugeForm (l:L) (d:ℕ) :L[X] :=
 (1+Polynomial.C l*Polynomial.X)^(d-2)
def actual {E :Type} [Field E] [Algebra L E] {A:Equation E} (C:Pencil A)
    (r :Index A) :E[X][X] :=
  let i:=r.2.1.val
  let j:=r.2.2.val
  let c (f :E[X][X]) :=(f.coeff i).coeff j
  let g:=if j=0 then (gaugeForm C.tilt A.d).coeff i else 0
  ![const₂ (c A.f),
    const₂ (c C.num) - const₂ (c C.den)*Polynomial.C (Polynomial.X:E[X]),
    const₂ (c A.f.derivative) - const₂ (algebraMap L E g)*Polynomial.X] r.1
def deformArg {E :Type} [Field E] [Algebra L E] (a :E[X][X]) (z :L) :E[X][X][X] :=
 Polynomial.C a+Polynomial.C (const₂ (algebraMap L E z))*Polynomial.X
def deform {E ι:Type} [Field E] [Algebra L E] (R:MvPolynomial ι L)
    (a :ι→E[X][X]) (z :ι→L) :E[X][X][X] :=
  R.eval₂ (Polynomial.C.comp (const₂.comp (algebraMap L E))) (fun i=>deformArg (a i) (z i))
end
end qfbIfsd
end
