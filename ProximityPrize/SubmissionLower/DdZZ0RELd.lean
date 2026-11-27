import ProximityPrize.SubmissionLower.DdCS
import ProximityPrize.SubmissionLower.DdAA
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit true
namespace P5_8
noncomputable section
open i4 PolynomialDifferential MvPolynomial
open scoped BigOperators

abbrev Equation :=apQ.Equation
def small:Source :=
  ⟨61,83,25,11,(aH1 83 25 11).filter
    (fun j=>j.b+j.c≤25-(j.q - 76)/2)⟩
def bo8:Source :=⟨4600,6251,1959,979,aH1 6251 1959 979⟩
def Moments (s :Source) (T S V:ℕ) :Prop :=
 s.E.card=T∧(∑ j∈s.E,j.q)=S∧(∑ j∈s.E,j.v)=V
structure Jn where
 B:ℕ
 J:ℕ
 C:ℕ
def caps (Q:Equation) :Jn :=
 ⟨jetTotalDegree Q,Q.weightedTotalDegree indexWeight,jetDegree Q (Fin.last 2)⟩
def Jn.repair (s :Jn) :Jn :=
 let c:=min s.C (min s.B (s.J/2))
 ⟨s.B,min s.J (s.B+c),c⟩
def Jn.wD (s a :Jn) :Jn :=
 ⟨s.B-a.B,s.J-a.J,s.C-a.C⟩
def tetra (n:ℕ) :ℕ:=n*(n - 1)*(n - 2)/6
def aMt (s :Jn) :ℕ :=
  let z :=min s.B (min (s.J/2) s.C)
  let d:=min (z+1) (s.J+1 - s.B)
  tetra (s.B+3) - tetra (s.B+3 - d) +
    (z+1 - d)*(s.J+1 - d - z)*(2*s.B+2 - s.J)/2
def donorCaps :Jn:=⟨6251,1959,979⟩
def smallCaps :Jn:=⟨83,25,11⟩
def chartCaps :Jn:=⟨a₀ small,D small,e small⟩
def Gq (a :Jn) :ℕ :=
  ∑ i∈Finset.range (donorCaps.B/a.B),
    let l:=i+1
    if l*a.J≤donorCaps.J∧l*a.C≤donorCaps.C then
      aMt (donorCaps.wD ⟨l*a.B,l*a.J,l*a.C⟩)
    else 0
def ke (L R:BL 2) :Ideal (BL 2) :=Ideal.span {L,R}
def chartOpen (P:Ideal (BL 2)) (T:Chart 2) :Set (Fin 3→nU) :=
 {x | x∈zeroLocus nU P∧MvPolynomial.eval x T.denominator≠0}
structure ProperCharts (L R:BL 2) where
 count:ℕ
 component:Fin count→ Ideal (BL 2)
 distinct :Function.Injective component
 minimal : ∀ i,component i∈(ke L R).minimalPrimes
 bY:Fin count→Chart 2
 den_reg : ∀ i,(bY i).denominator∉component i
 bands : ∀ i,bHP small (bY i).denominator ∧
   ∀ j,bHP small ((bY i).numerator j)
 recover : ∀ i x,x∈chartOpen (component i) (bY i) →
   ∀ j:Fin 3,awb ((bY i).output x) j.val=x j
def ProperCharts.image {L R:BL 2} (F:ProperCharts L R) (i:Fin F.count) :=
 (F.bY i).output '' chartOpen (F.component i) (F.bY i)
def ProperCharts.ideal {L R:BL 2} (F:ProperCharts L R) (i:Fin F.count) :
    Ideal jo:=vanishingIdeal nU (F.image i)
def mixedTerm (x y z :Jn) :ℕ:=x.C*(y.J - y.C)*(2*z.B - z.J)
def tW (a b u:Jn) :ℕ :=
  (mixedTerm a b u+mixedTerm a u b+mixedTerm b a u +
    mixedTerm b u a+mixedTerm u a b+mixedTerm u b a)/2
def properDegree (a :Jn) :ℕ :=
 tW (smallCaps.wD a).repair (donorCaps.wD a).repair chartCaps
def componentCap (a :Jn) :ℕ:=(83-a.B)*(6251-a.B)
def tariffShape (a :Jn) :Source :=
 ⟨1,max 2 (max a.B a.J),max 2 a.J,max 1 a.C,∅⟩
end
end P5_8
