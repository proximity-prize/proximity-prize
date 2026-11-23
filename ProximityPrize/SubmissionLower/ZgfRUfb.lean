import ProximityPrize.SubmissionLower.ZzWMDba
import ProximityPrize.SubmissionLower.Z77J3Nc
import ProximityPrize.SubmissionLower.ZRqikKa
import ProximityPrize.SubmissionLower.ZSSMtJa
import ProximityPrize.SubmissionLower.ZPNuIWc
import ProximityPrize.SubmissionLower.ZrgYIVd
set_option Elab.async false
section
namespace qE3Ebna
noncomputable section
open Polynomial Finset qe6nVeb
open P5 (K)
open cu (L)
open E7 (CurvePlace)
open qb0hmCe (CurveModel coeffHeight cLN specialize zD)
open scoped Classical WithZero
structure Sheet {J:Input} {U:Finset K} (B:DualWord J U) {q:SeedPlane}
   (C:CurveModel q) where
 f :C.E[X][X]
 irreducible :Irreducible f
 positive :0<f.natDegree
 normalized: (f.coeff f.natDegree).leadingCoeff=1
 marks :Finset K
 Bp:marks⊆U
 atPlace : ∀ γ∈marks,C.E →ₐ[L] LaurentSeries L
 place :K→CurvePlace L C.E
 distinct :Set.InjOn place (marks :Set K)
 value : ∀ γ (hγ:γ∈marks) c,
   (place γ).value c=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (atPlace γ hγ c)
 arc : ∀ γ (hγ:γ∈marks),∃ a :Fin 2→PowerSeries L,
   (∀ i,atPlace γ hγ (C.seed i)=(a i:LaurentSeries L)) ∧
   (∀ i,PowerSeries.constantCoeff (a i)=dcQ J γ i) ∧
   ∃ i,PowerSeries.coeff 1 (a i)≠0
 integral : ∀ γ (_:γ∈marks) i j,(place γ).value ((f.coeff i).coeff j)≤1
 root : ∀ γ (hγ:γ∈marks),specialize (cLN (atPlace γ hγ) 0 f) (B.P γ) (B.Q γ)=0
 separable : ∀ γ (hγ:γ∈marks),((cLN (atPlace γ hγ) 0 f).map phys).Separable
 simple : ∀ γ (hγ:γ∈marks),
   specialize (cLN (atPlace γ hγ) 0 f).derivative (B.P γ) (B.Q γ)≠0
 num :K→ L[X]
 den:K→ L[X]
 den_ne : ∀ γ∈marks,den γ≠0
 reduced : ∀ γ∈marks,IsCoprime (num γ) (den γ)
 formula : ∀ γ (hγ:γ∈marks),
   phys (num γ)/phys (den γ)=zD (atPlace γ hγ) f (B.P γ) (B.Q γ)
abbrev Sheet.d {J U} {B:DualWord J U} {q} {C:CurveModel q} (S:Sheet B C) :=S.f.natDegree
abbrev Sheet.h {J U} {B:DualWord J U} {q} {C:CurveModel q} (S:Sheet B C) :=coeffHeight S.f
def Sheet.below {J U} {B:DualWord J U} {q} {C:CurveModel q} (S:Sheet B C) (W:ℕ) :Prop :=
 ∀ i,S.f.coeff i=0∨(S.f.coeff i).natDegree+S.d*B.u₀+i*(B.u₁-B.u₀)≤W
structure Prepared {J U} (B:DualWord J U) (q:SeedPlane) (T:Finset K) (d W h:ℕ) where
 curve :CurveModel q
 size :ℕ
 part:Fin size→Sheet B curve
 inside : ∀ j,(part j).marks⊆T
 zJ: (T \ univ.biUnion (fun j=>(part j).marks)).card≤(7+2*d)*h*q.totalDegree
 degree : ∑ j,(part j).d≤d
 height : ∑ j,(part j).h≤h*q.totalDegree
 weight : ∀ j,(part j).below W
def relativeDegree {J U} (B:DualWord J U) (γ:K) :ℕ :=
 let s :=B.u₁-B.u₀
 s+2*max (B.Q γ).natDegree ((B.P γ).natDegree-s)
def poleOrderAt {J U} {B:DualWord J U} {q} {C:CurveModel q} (S:Sheet B C) (γ:K) :ℕ :=
 max (S.den γ).natDegree ((S.num γ).natDegree-relativeDegree B γ)
abbrev SiteTarget :=qb0hmCe.SiteTarget
open qb0hmCe (SiteTarget.det SiteTarget.height)
def matchesTarget (R:SiteTarget) {J U} (B:DualWord J U) (γ:K) :Prop :=
 let z :=dcQ J γ R.coord
 let P:=R.a+R.b*z
 let Q:=R.c+R.d*z
 (P≠0∨Q≠0)∧(B.P γ).eval R.center*Q=(B.Q γ).eval R.center*P
def Sheet.direction {J U} {B:DualWord J U} {q} {C:CurveModel q}
    (S:Sheet B C) (γ:K) (i:Fin 2) :L :=
  if h:γ∈S.marks then (S.atPlace γ h (C.seed i)).coeff 1 else 0
def exceptional (R:SiteTarget) {J U} {B:DualWord J U} {q} {C:CurveModel q}
    (S:Sheet B C) (γ:K) :Prop :=
  matchesTarget R B γ ∧ ¬ ((S.num γ).eval R.center=0↔R.det=0∨S.direction γ R.coord=0)
def siteBudget (R:SiteTarget) (d h:ℕ) (q:SeedPlane) :ℕ :=
 if R.b=0∧R.d=0 then (2*d-1)*h else 2*d*(h+d*R.height q)
structure Starts {J U} (B:DualWord J U) where
 target :Fin 2→SiteTarget
 distinct : (target 0).center≠(target 1).center
 coord : ∀ i,(target i).coord=i
 invertible : ∀ i,(target i).det≠0
 lg : ∀ γ∈U,∀ i,matchesTarget (target i) B γ
end
end qE3Ebna
end
section
set_option backward.isDefEq.respectTransparency false
namespace qE3Ebna
noncomputable section
open Polynomial Finset qe6nVeb
open P5 (p)


open cu (L)

open scoped Classical
private theorem no_common_root {f g:L[X]} (h:IsCoprime f g) {y :L}
  (hg:g.eval y=0) :f.eval y≠0:= by
 intro hf
 obtain ⟨a,b,hab⟩:=h
 have he :=congrArg (fun p:L[X]=>p.eval y) hab
 simp only [eval_add,eval_mul,hf,hg,mul_zero,add_zero,eval_one,zero_ne_one] at he
private theorem target_nonzero {R:SiteTarget} (h:R.det≠0) (z :L) :
  R.a+R.b*z≠0∨R.c+R.d*z≠0:= by
 by_contra! hz
 apply h
 unfold qb0hmCe.SiteTarget.det
 linear_combination R.d*hz.1 - R.b*hz.2
theorem width_floor (J:Input) :32768≤width J.D:= by
 have hd:=J.degree_lo
 change 131072≤J.D at hd
 change 32768≤262144+J.D-2*179740
 omega
end
end qE3Ebna
end
