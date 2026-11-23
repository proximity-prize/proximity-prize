import ProximityPrize.SubmissionLower.B2
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
namespace Ty
noncomputable section
open K1 cu gT pI Polynomial
def gY (H :Equation) :ℕ :=
 H.support.sup fun j=>(H.coeff j).totalDegree
def aea (s :Shape) (x z :ℕ) :Shape :=
 ⟨s.m,s.B - z,min s.J (s.B - z),s.U - x⟩
def aYS (H :Equation) (r :ℕ) (I:Ideal Ambient) :Prop :=
 ∃ f :Equation,Irreducible f∧0<f.natDegree∧f^r∣H∧iJ (C f)∈I
def aof (r :ℕ) (k :Fin 4) :ℕ :=
 ![r,r,r^2,r^2] k
def aaW (x z :ℕ) (k :Fin 4) :ℕ :=
 ![z,x,2*x*z,x*x] k
def aoD (s t:Shape) (k :Fin 4) :ℕ :=
  ![s.B*t.J+t.B*s.J - s.J*t.J,s.U*t.J+t.U*s.J,
    s.U*t.B+t.U*s.B,s.U*t.U] k
def Be (P Q:Jet) (I:Ideal Ambient) (hp:I.IsPrime) :ℕ∞ :=
 letI:I.IsPrime :=hp
 let R:=Localization.AtPrime I
 letI:CommRing R:=inferInstanceAs (CommRing (Localization.AtPrime I))
 let J:Ideal Ambient:=Ideal.span {iJ P,iJ Q}
 let A:Ideal R:=J.map (algebraMap Ambient R)
 Module.length R (R ⧸ (A:Submodule R R))
end
end Ty
end
section
set_option maxHeartbeats 1000000
namespace Ty
noncomputable section
open K1 cu gT pI Polynomial
open scoped Classical BigOperators
def c3:Prop :=
  ∀ (H :Equation) (P:Jet) (I:Ideal Ambient) (m r :ℕ),
    H≠0→ gY H<p→H.natDegree<p →
    xN I→0< r→ r≤ m → ¬ aYS H r I →
    O9 I (C H*P) m→O9 I P (m+1 - r)
def c4 :Prop :=
  ∀ (P Q:Jet) (I:Ideal Ambient) (hI:xN I) (n:ℕ),
    0<n→O9 I P n→O9 I Q n →
    ((if dual I then n^2 else n:ℕ) :ℕ∞)≤Be P Q I hI.prime
def c5:Prop :=
  ∀ (P Q:Jet) (s t:Shape) (S:Finset (Ideal Ambient)) (k :Fin 4) (d:ℕ),
    P≠0→Q≠0→ IsRelPrime (iJ P) (iJ Q) →
    s.J≤ s.B→t.J≤t.B→ oU P s→ oU Q t→0<d →
    (∀ I∈S,∃ hI:xN I,
      pN I k≠0→(d:ℕ∞)≤Be P Q I hI.prime) →
    d*mass S k≤aoD s t k
private theorem bWa {I:Ideal Ambient} (hp:I.IsPrime) (G:tK) (P:Jet)
  (m:ℕ) (hG : ¬ aaS G I) (ho:O9 I (Gw G*P) m) :
  O9 I P m:= by
 obtain ⟨a,ha,h⟩:=ho
 refine ⟨a*iJ (Gw G),fun hn=>(hp.mem_or_mem hn).elim ha hG,?_⟩
 simpa only [map_mul,mul_assoc] using h
end
end Ty
end
