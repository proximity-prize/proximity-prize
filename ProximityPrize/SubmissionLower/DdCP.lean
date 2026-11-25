import ProximityPrize.SubmissionLower.DdAD
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 12000
open _root_ renaming Algebra.algebraMap→c9,Fin.last→lI,Finset→cy,Finset.range→lz,IsCoprime→lJ,MvPolynomial→aU,MvPolynomial.eval→mD,Polynomial.Bivariate.swap→ oj,Polynomial.C→nq,PolynomialDifferential.DifferentialPolynomial→lV,ProximityPrize.Benchmark.IRSProfile.domain→nI,ReedSolomon.closePolynomialSet→nX,add_sub_cancel_right→n5
set_option autoImplicit true
section
namespace bar
noncomputable section
open MvPolynomial
open scoped MonomialOrder BigOperators
variable {k σ:Type*} [Field k] [Finite σ]
end
end bar
end
section
namespace i4
noncomputable section
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
abbrev K:=gR.Native.K
abbrev Node :=gR.Native.I
abbrev node :=nI
abbrev p:ℕ:=2130706433
abbrev n:ℕ:=262144
abbrev k :ℕ:=131072
abbrev N :ℕ:=131071
abbrev Jet:=Sigma fun _:ℕ=>Sigma fun _:ℕ=>ℕ
def Jet.a (j:Jet) :ℕ:=j.2.2
def Jet.b (j:Jet) :ℕ:=j.2.1
def Jet.c (j:Jet) :ℕ:=j.1
def Jet.q (j:Jet) :ℕ:=j.a+j.b+j.c
def Jet.v (j:Jet) :ℕ:=j.b+2*j.c
structure Source where
 m:ℕ
 B:ℕ
 J:ℕ
 C:ℕ
 E :cy Jet
def aH1 (B J C:ℕ) :cy Jet :=
  (lz (C+1)).sigma fun c =>
    (lz (J - 2*c+1)).sigma fun b=>lz (B-(b+c)+1)
structure Rz (s :Source) :Prop where
 multiplicity :0<s.m
 top_pos :0<s.C
 index_top:2*s.C≤ s.J
 aQV:s.J≤ s.B
 characteristic:max N (s.B*(s.B-1))<p
 support : ∀ j∈s.E,j.q≤ s.B∧j.v≤ s.J∧j.c≤ s.C
 lower : ∀ j∈s.E,0<j.a→(⟨j.c,j.b,j.a-1⟩:Jet)∈s.E
def errors (A:ℕ) :=n - A
def gap (A:ℕ) :=A-N
structure aRk (A:ℕ) :Prop where
 gt_degree :N<A
 lt_length:A<n
 one_le_beta :gap A≤errors A
 beta_lt_two:errors A<2*gap A
def width (A:ℕ) (s :Source) (j:Jet) :=s.m*A-N*j.q+j.v
abbrev apU (A:ℕ) (s :Source) :=(j:s.E)×Fin (width A s j.val)
def column (A:ℕ) (s :Source) (i:apU A s) :SourceColumn 2 :=
 ⟨i.2.val,i.1.val.a,![i.1.val.b,i.1.val.c]⟩
def aWf (A:ℕ) (s :Source) :ℕ :=
 (localConstraintMatrix s.m (fun _:Unit=>(0:ZMod p)) (fun _=>0) (column A s)).rank
def Vv (A:ℕ) (s :Source) (w:Node→K) :ℕ :=
 (localConstraintMatrix s.m (fun i=>node i) w (column A s)).rank
def aCq (m q:ℕ) (g:ℤ) :cy Jet :=
  ((lz (q+1)).sigma fun c =>
    (lz (q-c+1)).sigma fun b => {q-(b+c)}).filter fun j:Jet =>
      0≤g+(j.v :ℤ)+3*(j.a :ℤ)∧g+(j.v :ℤ)+3*(j.a :ℤ)<(m:ℤ)
def aTf (s :Source) (q:ℕ) (g:ℤ) :cy Jet :=
 s.E.filter fun j=>j.q=q∧0≤g+(j.v :ℤ)
def alu (row col:Jet) :ZMod p :=
 if col.b≤ row.b∧col.c≤ row.c∧row.a+(row.b-col.b)+(row.c-col.c)=col.a
 then (-1)^(row.c-col.c)*(col.a.choose row.a :ℕ)*((col.a-row.a).choose (row.b-col.b) :ℕ)
 else 0
def GU (s :Source) (q:ℕ) (g:ℤ) :
    Matrix (aCq s.m q g) (aTf s q g) (ZMod p) :=
  fun r c=>alu r.val c.val
def aWw (s :Source) (cut:ℕ) :ℕ :=
  ∑ q∈lz cut,∑ u∈lz (s.m+s.J-q),
    (GU s q ((u:ℤ) - s.J)).rank
def axY (s :Source) (cut:ℕ) :Prop :=
 ∀ j∈s.E,cut≤j.q→s.m≤j.a
def t:ℕ:=max (2*k-7) (k-2)
def t₁:ℕ:=2*k-5
def a₀ (s :Source) :=1+t*(s.B-1)
def D (s :Source) :=t*(s.J-2)+k-1
def e (s :Source) :=min (t*(s.C-1)+k-2) (D s/2)
def R₂ (s :Source) :=
  (s.C*D s+e s*s.J - 2*s.C*e s)*(2*a₀ s - D s) +
    e s*(D s-e s)*(2*s.B-s.J)
def H (s :Source) :=max s.B ((2*s.C-1)*s.B - s.C^2)
def I₁ (s :Source) :=max s.J ((2*s.C-1)*s.J - 2*s.C^2)
def a₁ (s :Source) :=1+t₁*(H s-1)
def d₁ (s :Source) :=min (a₁ s) (t₁*(I₁ s-1)+k-1)
def R₁ (s :Source) :=H s*d₁ s+I₁ s*a₁ s - I₁ s*d₁ s
abbrev close (A:ℕ) (w:Node→K) :=nX node w k A
def axW (A cap:ℕ) :Prop :=
 ∀ w:Node→K,(close A w).Finite∧(close A w).ncard≤ cap
def indexWeight {r :ℕ} : JetVariable r→ℕ:= fun j=>j.elim 0 Fin.val
def ato (s :Source) (Q:lV K 2) :Prop :=
  Q≠0∧jetTotalDegree Q≤ s.B∧Q.weightedTotalDegree indexWeight≤ s.J ∧
    jetDegree Q (lI 2)≤ s.C
def bRZ (s :Source) (Q:lV K 1) :Prop :=
 Q≠0∧jetTotalDegree Q≤H s∧jetDegree Q (lI 1)≤I₁ s
def ae8 {r :ℕ} (Q:lV K r) (f :(Polynomial K)) :Prop :=
  ∃ G:lV K r,Irreducible G∧G∣Q ∧
    differentialSpecialization G f=0∧differentialSpecialization (separant G (lI r)) f≠0
abbrev FX:=FractionRing (Polynomial K)
abbrev nU:=AlgebraicClosure FX
abbrev jo:=aU (Fin k) nU
abbrev BL (r :ℕ) :=aU (Fin (r+1)) nU
def embed:K →+* nU :=
 (c9 FX nU).comp ((c9 (Polynomial K) FX).comp nq)
def center :nU:=c9 FX nU (c9 (Polynomial K) FX Polynomial.X)
def Gp (f :(Polynomial K)) (i:Fin k) :nU:=embed (f.coeff i.val)
def awb (y :Fin k→nU) (j:ℕ) :nU :=
 ∑ i:Fin k,(i.val.choose j:nU)*center^(i.val-j)*y i
structure Chart (r :ℕ) where
 equation :BL r
 denominator :BL r
 numerator :Fin k→BL r
def Chart.aa0 {r} (T:Chart r) :Set (Fin (r+1)→nU) :=
 {u | mD u T.equation=0∧mD u T.denominator≠0}
def Chart.output {r} (T:Chart r) (u:Fin (r+1)→nU) (i:Fin k) :nU :=
 mD u (T.numerator i)/mD u T.denominator
def Chart.aN8 {r} (T:Chart r) :=T.output '' T.aa0
def Chart.ideal {r} (T:Chart r) :Ideal jo:=MvPolynomial.vanishingIdeal nU T.aN8
structure aAQ {r} (T:Chart r) :Prop where
 irreducible :Irreducible T.equation
 nonvanishing : ¬ T.equation∣T.denominator
 recover : ∀ u∈T.aa0,∀ j:Fin (r+1),awb (T.output u) j.val=u j
structure Family (r :ℕ) where
 count:ℕ
 bY:Fin count→Chart r
def bHP (s :Source) (P:BL 2) :Prop :=
 P.totalDegree≤a₀ s∧P.weightedTotalDegree Fin.val≤D s∧P.degreeOf (lI 2)≤e s
def aOa (s :Source) (P:BL 1) :Prop :=
 P.totalDegree≤a₁ s∧P.degreeOf (lI 1)≤d₁ s
structure bQQ (s :Source) (F:Family 2) :Prop where
 count:F.count≤ s.B
 bct : ∀ i,aAQ (F.bY i)
 total: (∑ i,(F.bY i).equation.totalDegree)≤ s.B
 index : (∑ i,(F.bY i).equation.weightedTotalDegree Fin.val)≤ s.J
 top: (∑ i,(F.bY i).equation.degreeOf (lI 2))≤ s.C
 bands : ∀ i,bHP s (F.bY i).denominator ∧ ∀ j,bHP s ((F.bY i).numerator j)
structure cxu (s :Source) (F:Family 1) :Prop where
 count:F.count≤H s
 bct : ∀ i,aAQ (F.bY i)
 total: (∑ i,(F.bY i).equation.totalDegree)≤H s
 index : (∑ i,(F.bY i).equation.degreeOf (lI 1))≤I₁ s
 bands : ∀ i,aOa s (F.bY i).denominator ∧ ∀ j,aOa s ((F.bY i).numerator j)
def cxn {r} (F:Family r) (Q:lV K r) :Prop :=
 ∀ f :(Polynomial K),f.degree<k→ae8 Q f → ∃ i,Gp f∈(F.bY i).aN8
structure bQ7 {r} (F:Family r) (budget:ℕ) :Prop where
 prime : ∀ i,(F.bY i).ideal.IsPrime
 dimension : ∀ i,(MvPolynomial.affineHilbertPolynomial (F.bY i).ideal).natDegree=r
 total: (∑ i,MvPolynomial.affineDegree (F.bY i).ideal)≤(budget:ℚ)
end
end i4
end
section
namespace i4
noncomputable section
open Finset
open scoped BigOperators
theorem b8U {B J C:ℕ} (hBJ:J≤B) (hJC:2*C≤J) (j:Jet) :
  j∈aH1 B J C↔j.q≤B∧j.v≤J∧j.c≤C:= by
 rcases j with ⟨c,b,a⟩
 simp only [aH1,mem_sigma,mem_range,Jet.q,Jet.v,Jet.c,Jet.b,Jet.a]
 omega
end
end i4
end
section
set_option backward.isDefEq.respectTransparency false
namespace DdP0
noncomputable section
open Polynomial Matrix CoreDefinitions Code
open gR
open ProximityPrize.Benchmark
open scoped BigOperators NNReal
end
end DdP0
end
section
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
namespace DdP0
noncomputable section
open Polynomial Code LinearCode CoreDefinitions ToyProblem
open gR ProximityPrize.Benchmark
open yP.baR yP.a92
open scoped NNReal
end
end DdP0
end
