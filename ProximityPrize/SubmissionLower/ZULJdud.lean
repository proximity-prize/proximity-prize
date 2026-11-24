import ProximityPrize.SubmissionLower.ZS4VEna
import ProximityPrize.SubmissionLower.ZfWgThc
import ProximityPrize.SubmissionLower.A8
import ProximityPrize.SubmissionLower.AP
import ProximityPrize.SubmissionLower.AU
import ProximityPrize.SubmissionLower.B6
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.C3
import ProximityPrize.SubmissionLower.CD
import ProximityPrize.SubmissionLower.CH
import ProximityPrize.SubmissionLower.CI
import ProximityPrize.SubmissionLower.DG
import ProximityPrize.SubmissionLower.E2
import ProximityPrize.SubmissionLower.E4
import ProximityPrize.SubmissionLower.E6
import ProximityPrize.SubmissionLower.P6Defs
import ProximityPrize.SubmissionLower.Z2fdgla
import ProximityPrize.SubmissionLower.ZYswgKc
import ProximityPrize.SubmissionLower.Z409zke
import ProximityPrize.SubmissionLower.ZBRA0Kc
import ProximityPrize.SubmissionLower.ZCvigsb
import ProximityPrize.SubmissionLower.ZPfxqxd
import ProximityPrize.SubmissionLower.ZSWmOqa
import ProximityPrize.SubmissionLower.ZV6zyia
import ProximityPrize.SubmissionLower.ZZMyKHc
import ProximityPrize.SubmissionLower.ZaQt7ib
import ProximityPrize.SubmissionLower.ZBcmVie
set_option Elab.async false
section
set_option autoImplicit true
namespace q3aiQjb













open scoped BigOperators
def span:ℕ→ℕ→ℕ
 | 0,_=>0
 | n+1,data=>data % 512+span n (data/512)

end q3aiQjb
end
section
section
namespace qThdpma
noncomputable section
open Polynomial
open cu (L)
open qNu3xvc (Equation)
open qdpQ3Rb (AffinePencil numerator)
open qZu9hjc (physicalDeriv)
variable {E :Type} [Field E]
def pairHom {R S:Type} [CommRing R] [CommRing S] (j:R →+* S) (x y :S) :
    R[X][X] →+* S:=eval₂RingHom (eval₂RingHom j x) y
def cutJac {R:Type} [CommRing R] (j:E →+* R) (x y u:R)
    (f g:E[X][X]) :R :=
  let ev :=pairHom j x y
  ev (physicalDeriv f)*(ev g.derivative - u*ev f.derivative.derivative) -
    ev f.derivative*(ev (physicalDeriv g) - u*ev (physicalDeriv f.derivative))
def bfj (d:E[X]) :E →+* Localization.Away d :=
  (algebraMap E[X] (Localization.Away d)).comp Polynomial.C
def localParameter (d:E[X]) :Localization.Away d :=
  algebraMap E[X] (Localization.Away d) Polynomial.X
def qY {d:E[X]} (hd:d≠0) :Localization.Away d →+* RatFunc E :=
  IsLocalization.Away.lift d (g:=algebraMap E[X] (RatFunc E)) (RatFunc.algebraMap_ne_zero hd).isUnit
def multMatrix {R:Type} [CommRing R] (n:ℕ) (P Q:R[X]) :Matrix (Fin n) (Fin n) R :=
  fun i j=>((Q*Polynomial.X ^(j:ℕ)) %ₘ P).coeff (i:ℕ)
variable [Algebra L E]
structure FibreModel {R:Type} [CommRing R] (j:E →+* R) (u:R)
    {A:Equation E} (D:AffinePencil A) where
  P:R[X]
  monic:P.Monic
  separable :P.Separable
  x :R[X]
  y :R[X]
  recover :R[X][X]
  qInv :R[X]
  jacInv :R[X]
  f_dvd:P∣pairHom (Polynomial.C.comp j) x y A.f
  cut_dvd:P∣pairHom (Polynomial.C.comp j) x y (numerator A D.a D.b D.c) -
    Polynomial.C u*pairHom (Polynomial.C.comp j) x y A.f.derivative
  polar_dvd:P∣pairHom (Polynomial.C.comp j) x y A.f.derivative*qInv - 1
  jac_dvd:P∣cutJac (Polynomial.C.comp j) x y (Polynomial.C u)
    A.f (numerator A D.a D.b D.c)*jacInv - 1
  recover_dvd:P∣pairHom Polynomial.C x y recover-Polynomial.X
def FibreModel.polar {R:Type} [CommRing R] {j:E →+* R} {u:R} {A:Equation E}
    {D:AffinePencil A} (M:FibreModel j u D) :R[X] :=
  pairHom (Polynomial.C.comp j) M.x M.y A.f.derivative
def FibreModel.value {R:Type} [CommRing R] {j:E →+* R} {u:R} {A:Equation E}
    {D:AffinePencil A} (M:FibreModel j u D) :R[X] :=
  (multMatrix M.P.natDegree M.P M.polar).charpoly
end
end qThdpma
end
section
namespace qApzjua
noncomputable section
open Polynomial
open cu (L)
open qNu3xvc (Equation)
open P5_7_1_7_4_3_4 (Pencil)
open qZu9hjc (physicalDeriv)
variable {E F:Type} [Field E]
def cut [Algebra L E] {A:Equation E} (C:Pencil A) (z :L) :E[X][X] :=
  C.num-Polynomial.C (Polynomial.C (algebraMap L E z))*C.den
def pairEval [CommRing F] (e :E →+* F) (x y :F) :E[X][X] →+* F :=
  eval₂RingHom (eval₂RingHom e x) y
def pencilJac [CommRing F] (e :E[X][X] →+* F) (f n d:E[X][X]) (t:F) :F :=
  e (physicalDeriv f)*(e n.derivative - t*e d.derivative) -
    e f.derivative*(e (physicalDeriv n) - t*e (physicalDeriv d))
structure Specialization [Field F] [Algebra (RatFunc E) F] (z :E) where
  ring :Subring F
  eval :ring →+* AlgebraicClosure E
  base :E[X] →+* ring
  ek :ring.subtype.comp base =
    (algebraMap (RatFunc E) F).comp (algebraMap E[X] (RatFunc E))
  special:eval.comp base=(algebraMap E (AlgebraicClosure E)).comp (evalRingHom z)
def Specializes (E F:Type) [Field E] [Field F] [Algebra (RatFunc E) F] :Prop :=
  ∀ (S:Finset F) (U:Finset (RatFunc E)),
    ∃ bad:Finset E,∀ z∉bad,∃ T:Specialization (F:=F) z,
      (∀ v∈S,v∈T.ring) ∧
      ∀ u∈U,∃ v :T.ring,(v :F)=algebraMap (RatFunc E) F u ∧
        T.eval v=algebraMap E (AlgebraicClosure E) (RatFunc.eval (RingHom.id E) z u)
end
end qApzjua
end
end
