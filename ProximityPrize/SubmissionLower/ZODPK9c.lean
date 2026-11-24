import ProximityPrize.SubmissionLower.ZSSMtJa
set_option Elab.async false
section
namespace qb0hmCe
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark
open P5 (K I blockLength dw)
open P5_7 (farAgreement)
open P5_7_1 (Input)
open qQ9yWTb (D G WordChart Curve)
open P5_7_7 (base base_injective hit index_card mem_sites relativeDegree sites)
open scoped Classical
theorem count {x :Input} {U:Finset K} (hU:U⊆x.Γ) {J:WordChart x U}
    {q:Curve} {C:CurveModel q} (S:Sheet J C) (n v a :ℕ)
    (hn : ∀ i:I,
      (S.marks.filter fun γ => ¬ hit x.M.word x.F.scalar γ i ∧
        (S.num γ).eval (base i)≠0).card≤n)
    (hv : ∑ γ∈S.marks,poleOrderAt S γ≤v)
    (ha : (S.marks.filter fun γ=>S.num γ=0).card≤a) :
    G*S.marks.card≤blockLength*n+v+G*a := by
  let good:=S.marks.filter fun γ=>S.num γ≠0
  let lg (γ:K) :=sites x.M.word x.F.scalar γ
  let bad (γ:K) :=univ.filter fun i:I =>
    ¬ hit x.M.word x.F.scalar γ i∧(S.num γ).eval (base i)≠0
  have each (γ:K) (hm:γ∈good) :G≤(bad γ).card+poleOrderAt S γ:= by
    have hg:=mem_filter.mp hm
    let miss :=univ \ lg γ
    have hcard:miss.card=blockLength-(lg γ).card:= by
      change (univ \ lg γ).card= _
      rw [card_sdiff_of_subset (subset_univ _),card_univ,index_card]
    have heq :miss.filter (fun i=>(S.num γ).eval (base i)≠0)=bad γ:= by
      ext i
      simp [miss,bad,lg,mem_sites]
    have hsum:=card_filter_add_card_filter_not
      (s :=miss) (fun i=>(S.num γ).eval (base i)≠0)
    rw [heq,hcard] at hsum
    have hzero :=gR.kL.agd base base_injective
      (S.num γ) hg.2 (miss.filter (fun i => ¬ (S.num γ).eval (base i)≠0))
      (fun _ hi=>not_ne_iff.mp (mem_filter.mp hi).2)
    have hJ:=S.Bp hg.1
    have ⟨hh,hq,hp⟩:=J.degree γ hJ
    change (lg γ).card≤farAgreement+J.u₀ at hh
    change (J.Q γ).natDegree≤farAgreement+J.u₀-(lg γ).card at hq
    change (J.P γ).natDegree≤farAgreement+J.u₁-(lg γ).card at hp
    have horder :=J.order
    have hwidth :=J.gMz
    have hAgr :farAgreement≤(lg γ).card:= by
      let m:=x.F.mark γ (hU hJ)
      exact (show farAgreement≤dw by decide).trans (m.bad.dw.trans
        (card_le_card fun i hi=>mem_sites.mpr (m.scalar_hits i hi)))
    have hmax :max (J.Q γ).natDegree ((J.P γ).natDegree-(J.u₁-J.u₀)) ≤
        farAgreement+J.u₀-(lg γ).card:=max_le hq (by omega)
    have hrel :relativeDegree J γ+(lg γ).card+G≤blockLength:= by
      have hD:D ≤farAgreement:= by decide
      change relativeDegree J γ+(lg γ).card+(farAgreement-D)≤blockLength
      simp only [relativeDegree]
      omega
    unfold poleOrderAt
    omega
  have hswap : ∑ γ∈good,(bad γ).card =
      ∑ i:I,(good.filter fun γ => ¬ hit x.M.word x.F.scalar γ i ∧
        (S.num γ).eval (base i)≠0).card:= by
    simp only [bad,card_filter]
    rw [sum_comm]
  have hb : ∑ γ∈good,(bad γ).card≤blockLength*n:= by
    rw [hswap,← index_card,← card_univ,← sum_const_nat (s :=(univ :Finset I))
      (f := fun _=>n) (fun _ _=>rfl)]
    exact sum_le_sum fun i _=>(card_le_card (filter_subset_filter _ (filter_subset _ _))).trans (hn i)
  have hs : ∑ γ∈good,poleOrderAt S γ≤v :=
    (sum_le_sum_of_subset (filter_subset _ _)).trans hv
  have hgood:G*good.card≤blockLength*n+v := by
    rw [Nat.mul_comm G,← sum_const_nat (s :=good) (f := fun _=>G) (fun _ _=>rfl)]
    exact (sum_le_sum fun γ hm=>each γ hm).trans
      (sum_add_distrib.trans_le (Nat.add_le_add hb hs))
  have hp:=card_filter_add_card_filter_not (s :=S.marks) (fun γ=>S.num γ=0)
  change (S.marks.filter fun γ=>S.num γ=0).card+good.card=S.marks.card at hp
  rw [← hp,Nat.mul_add]
  exact (Nat.add_le_add (Nat.mul_le_mul_left G ha) hgood).trans_eq (by ac_rfl)
end
end qb0hmCe
end
section
namespace qb0hmCe
noncomputable section
open Polynomial Finset




open cu (L)

private theorem no_common_root {f g:L[X]} (h:IsCoprime f g) {y :L}
  (hg:g.eval y=0) :f.eval y≠0:= by
 intro hf
 obtain ⟨a,b,hab⟩:=h
 have he :=congrArg (fun p:L[X]=>p.eval y) hab
 simp only [eval_add,eval_mul,hf,hg,mul_zero,add_zero,eval_one,zero_ne_one] at he
end
end qb0hmCe
end
section
set_option backward.isDefEq.respectTransparency false
namespace qNu3xvc
noncomputable section
open Polynomial Finset
open P5 (K)
open cu (L)
open E7 (CurvePlace KB)
open qb0hmCe (coeffHeight cLN specialize zD)
open P5_7_7 (phys)
open scoped Classical WithZero
variable {E :Type} [Field E] [Algebra L E]
structure Equation (E :Type) [Field E] where
 f :E[X][X]
 irreducible :Irreducible f
 positive :0<f.natDegree
 s :ℕ
 b:ℕ
 weight : ∀ i,(f.coeff i).natDegree+i*s≤b+f.natDegree*s∨f.coeff i=0
abbrev Equation.d (A:Equation E) :=A.f.natDegree
abbrev Equation.h (A:Equation E) :=coeffHeight A.f
def qg (A:Equation E) (v :CurvePlace L E) :Prop :=
  (∀ i j,v.value ((A.f.coeff i).coeff j)≤1) ∧
    ∃ i j,v.value ((A.f.coeff i).coeff j)=1
structure Sections (A:Equation E) where
 marks :Finset K
 place :K→CurvePlace L E
 distinct :Set.InjOn place (marks :Set K)
 atPlace : ∀ γ∈marks,E →ₐ[L] LaurentSeries L
 value : ∀ γ (hγ:γ∈marks) c,
   (place γ).value c=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (atPlace γ hγ c)
 regular : ∀ γ∈marks,qg A (place γ)
 degree : ∀ γ (hγ:γ∈marks),(cLN (atPlace γ hγ) 0 A.f).natDegree=A.d
 separable : ∀ γ (hγ:γ∈marks),((cLN (atPlace γ hγ) 0 A.f).map phys).Separable
 P:K→ L[X]
 Q:K→ L[X]
 denom : ∀ γ∈marks,Q γ≠0
 coprime : ∀ γ∈marks,IsCoprime (P γ) (Q γ)
 root : ∀ γ (hγ:γ∈marks),specialize (cLN (atPlace γ hγ) 0 A.f) (P γ) (Q γ)=0
 simple : ∀ γ (hγ:γ∈marks),
   specialize (cLN (atPlace γ hγ) 0 A.f).derivative (P γ) (Q γ)≠0
 num :K→ L[X]
 den:K→ L[X]
 den_ne : ∀ γ∈marks,den γ≠0
 reduced : ∀ γ∈marks,IsCoprime (num γ) (den γ)
 formula : ∀ γ (hγ:γ∈marks),
   phys (num γ)/phys (den γ)=zD (atPlace γ hγ) A.f (P γ) (Q γ)
def finitePoles {A:Equation E} (S:Sections A) :ℕ :=
 ∑ γ∈S.marks,(S.den γ).natDegree
def horizontalDegree (A:Equation E) :ℕ :=
 (2*A.d-2)*A.b+A.d*(A.d-1)*A.s
def polarRate (A:Equation E) :ℕ :=
 (6*A.d-2)*A.b+(3*A.d*A.d-1)*A.s+(2*A.d-1)
instance (A:Equation E) :IsDomain (AdjoinRoot A.f) :=
 AdjoinRoot.isDomain_of_prime
  ((UniqueFactorizationMonoid.irreducible_iff_prime (α:=E[X][X])).mp A.irreducible)
abbrev EC (A:Equation E) :=FractionRing (AdjoinRoot A.f)
def a7W (A:Equation E) :E[X][X] →+* EC A :=
 (algebraMap (AdjoinRoot A.f) (EC A)).comp (AdjoinRoot.mk A.f)
def seed (A:Equation E) :E →+* EC A:=(a7W A).comp (C.comp C)
def constant (A:Equation E) (c:L) :EC A:=seed A (algebraMap L E c)
def amm (A:Equation E) :EC A:=a7W A (Polynomial.C (Polynomial.X:E[X]))
def jU (A:Equation E) (r :Bool) :EC A :=
 if r then (a7W A Polynomial.X)⁻¹ else a7W A Polynomial.X
def chartEq (A:Equation E) (r :Bool) :E[X][X] :=if r then A.f.reverse else A.f
def KM (A:Equation E) (r :Bool) :E[X][X] →+* EC A :=
 eval₂RingHom ((a7W A).comp C) (jU A r)
def physicalDerivative (f :E[X][X]) :E[X][X] :=f.sum fun i a=>monomial i a.derivative
def seedDerivative (δ:Derivation L E E) (f :E[X][X]) :E[X][X] :=
 f.sum fun i a=>monomial i (a.sum fun j c=>monomial j (δ c))
def polar (A:Equation E) (r :Bool) :EC A :=
 KM A r (chartEq A r).derivative
def jet (A:Equation E) (r :Bool) :EC A :=
 -(KM A r (physicalDerivative (chartEq A r)))/polar A r
def variation (A:Equation E) (r :Bool) (δ:Derivation L E E) :EC A :=
 -(KM A r (seedDerivative δ (chartEq A r)))/polar A r
structure GraphVal (A:Equation E) (r :Bool) where
 val :Valuation (EC A) ℤᵐ⁰
 normalized:Function.Surjective val
 constants : ∀ c,c≠0→val (constant A c)=1
 base_regular :val (amm A)≤1
 ordinate_regular :val (jU A r)≤1
 jet_regular :val (jet A r)≤1
def ResidueConstant {A:Equation E} {r :Bool} (v :GraphVal A r) (a :EC A) :Prop :=
 ∃ c:L,v.val (a - constant A c)<1
def Over {A:Equation E} {r :Bool} (v :GraphVal A r) (w:CurvePlace L E) (x :L) :Prop :=
 (∃ n:ℕ,0<n ∧ ∀ c,v.val (seed A c)=w.value c^n) ∧
 v.val (amm A - constant A x)<1 ∧
 (¬ ResidueConstant v (jU A r) ∨ ¬ ResidueConstant v (jet A r))
def poleCharge {A:Equation E} {r :Bool} (v :GraphVal A r) :ℕ :=
 KB v.val (polar A r)
def NoHorizontalPole (A:Equation E) :Prop :=
  ∀ (r :Bool) (v :GraphVal A r) (δ:Derivation L E E),
    (∀ c,c≠0→v.val (seed A c)=1)→v.val (variation A r δ)≤1
end
end qNu3xvc
end
