import ProximityPrize.SubmissionLower.ZZZuA2c
import ProximityPrize.SubmissionLower.ZYswgKc
import ProximityPrize.SubmissionLower.Zqb2cFb
import ProximityPrize.SubmissionLower.ZW31ykd
set_option Elab.async false
section
set_option autoImplicit true
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace qyV6B3d
open P5_7_2 (fO)
open qMHqmcc (GG receipt appendGrades)
private abbrev kA:fO:=⟨7,by decide⟩
local notation "kU" => receipt 2542 rfl (by with_unfolding_all rfl) (by with_unfolding_all rfl)
private theorem r84 :GG kA 84 3:=⟨kU,kU,kU,True.intro⟩
private theorem r87:GG kA 87 3:=⟨kU,kU,kU,True.intro⟩
private theorem r90:GG kA 90 3:=⟨kU,kU,kU,True.intro⟩
private theorem r93:GG kA 93 3:=⟨kU,kU,kU,True.intro⟩
theorem q:GG kA 84 12 :=
 appendGrades (appendGrades (appendGrades r84 r87) r90) r93
end qyV6B3d
end
section
set_option autoImplicit true
namespace qe6nVeb
noncomputable section
open Polynomial
open scoped BigOperators
open P5 (I K p k blockLength jG)
open P5_7_2 (A)
open cu (L FX j9 qD)
abbrev Raw:=Y3.Dg
abbrev gap (D:ℕ) :=A-D
abbrev width (D:ℕ) :=blockLength+D-2*A
structure Input where
 words :P5.e9
 deleted:Finset I
 model :jG words deleted
 CF:Finset K
 family :P1.bje A model CF
 shift_not_mem:model.shift∉CF
 block :L[X]
 bY:P5_7.YQ model family block
 positive_height:0< model.iF.toNat
 D:ℕ
 degree_lo:k≤D
 degree_hi:D <A
 degree : ∀ γ∈CF,(family.scalar γ).natDegree≤D
abbrev phys :L[X] →+* FX:=algebraMap _ _
abbrev base (i:I) :L:=algebraMap K L (P5.node i)
def hit (J:Input) (γ:K) (i:I) :Prop :=
 (J.family.scalar γ).eval (P5.node i)=J.model.word i
def sites (J:Input) (γ:K) :Finset I:= by
 classical exact Finset.univ.filter (hit J γ)
def mL (V:Finset I) :L[X] := ∏ i∈V,((Polynomial.X:L[X]) - C (base i))
def ic (D:ℕ) (a b:L[X]) (d:ℕ) :Prop :=
 (a=0∨a.natDegree+D ≤d)∧b.natDegree≤d
structure DualWord (J:Input) (U:Finset K) where
 a₀:L[X]
 a₁:L[X]
 b₀:L[X]
 b₁:L[X]
 u₀:ℕ
 u₁:ℕ
 order :u₀≤u₁
 gMz :u₀+u₁=width J.D
 row₀:ic J.D a₀ b₀ (A+u₀)
 row₁:ic J.D a₁ b₁ (A+u₁)
 determinant : ∃ c:L,c≠0∧a₀*b₁-a₁*b₀=C c*mL Finset.univ
 rows_hit : ∀ i,a₀.eval (base i)*algebraMap K L (J.model.word i)+b₀.eval (base i)=0 ∧
   a₁.eval (base i)*algebraMap K L (J.model.word i)+b₁.eval (base i)=0
 target : ∀ i,a₀.eval (base i)≠0∨a₁.eval (base i)≠0
 P:K→ L[X]
 Q:K→ L[X]
 denominator : ∀ γ∈U,Q γ≠0
 coprime : ∀ γ∈U,IsCoprime (P γ) (Q γ)
 numerator_id : ∀ γ∈U,mL (sites J γ)*P γ=a₁*j9 (J.family.scalar γ)+b₁
 denominator_id : ∀ γ∈U,mL (sites J γ)*Q γ=a₀*j9 (J.family.scalar γ)+b₀
 degrees : ∀ γ∈U,
   (sites J γ).card≤A+u₀ ∧
   (Q γ).natDegree≤A+u₀-(sites J γ).card ∧
   (P γ).natDegree≤A+u₁-(sites J γ).card
 dual_hits : ∀ γ∈U,∀ i,
   (P γ).eval (base i)*a₀.eval (base i)=(Q γ).eval (base i)*a₁.eval (base i) ↔ ¬ hit J γ i
def atDual {J U} (B:DualWord J U) (g:Raw) (γ:K) :FX :=
 (Y3.embed g).eval₂ (qD (J.model.label γ)) (phys (B.P γ)/phys (B.Q γ))
def below {J U} (B:DualWord J U) (g:Raw) (W:ℕ) :Prop :=
  ∀ i j,(g.coeff i).coeff j≠0 →
    ((g.coeff i).coeff j).natDegree+g.natDegree*B.u₀+i*(B.u₁-B.u₀)≤W
abbrev SeedPlane :=MvPolynomial (Fin 2) L
def dcQ (J:Input) (γ:K) :Fin 2→L :=
 ![algebraMap K L (J.model.label γ),(algebraMap K L (J.model.label γ))^p]
def immersedAt (q:SeedPlane) (z :Fin 2→L) :Prop :=
  ∃ t:Fin 2→PowerSeries L,
    (∀ i,PowerSeries.constantCoeff (t i)=z i) ∧
    (∃ i,PowerSeries.coeff 1 (t i)≠0) ∧
    MvPolynomial.eval₂ (algebraMap L (PowerSeries L)) t q=0
def immersedMarks (q:SeedPlane) (z :K→Fin 2→L) (T:Finset K) :Finset K:= by
 classical exact T.filter fun γ=>immersedAt q (z γ)
structure Witness where
 g:ℕ
 c:ℕ
def zWidth (e u:ℕ) (x :Witness) :=(((p-1)/u-(e+x.g))/e)-1
def rows (e u:ℕ) (x :Witness) :=(x.g+1)*(zWidth e u x*u+1)*(x.c*u+1)
def columns (e u:ℕ) (x :Witness) :=(zWidth e u x*u+u+1)*(x.c*u+u+1)
def quotient (e u:ℕ) (x :Witness) :=rows e u x/ columns e u x
def rank (D e j:ℕ) (x :Witness) :=
 width D*((e+x.g)*(e+x.g+1)+j*(j+1))/2
def switch (D e u:ℕ) (x :Witness) :=
  let j:=quotient e u x
  max (e*width D) (max (columns e u x*rank D e j x/rows e u x - j*width D)
    ((e+x.g-j)*width D))
def modulus (D e u:ℕ) (x :Witness) :=switch D e u x+1+quotient e u x*width D
def firstDigit (e :ℕ) (x :Witness) (z :ℕ) :=e*(z+1)+e+x.g
def highRate (e u:ℕ) (x :Witness) :=firstDigit e x (zWidth e u x)+p*firstDigit e x x.c
def poleRate (D e W:ℕ) :=(6*e-4)*W-(3*e*e-4*e+2)*width D
def numerator (D e W:ℕ) :=(7+6*e)*gap D+2*e*blockLength+poleRate D e W
def constantFee (e :ℕ) :=4*e^2
def lowNumerator (D e W h:ℕ) :=h*numerator D e W+(constantFee e+1)*gap D
def weightOK (D e W:ℕ) :Prop :=
 0<width D ∧3≤e∧e<p∧e*width D ≤W ∧
 e*(e-1)*width D ≤(2*e-2)*W∧(2*e-2)*W-e*(e-1)*width D <p ∧
 (3*e*e-4*e+2)*width D ≤(6*e-4)*W
def filterOK (D e u:ℕ) (x :Witness) :Prop :=
 0< u∧0<zWidth e u x∧0<x.c ∧
 quotient e u x≤x.g∧(e+x.g)*width D < modulus D e u x ∧
 columns e u x*rank D e (quotient e u x) x< rows e u x*modulus D e u x ∧
 u*firstDigit e x (zWidth e u x)<p
def feeOK (D e u cap:ℕ) (x :Witness) :Prop :=
 let den:=3*gap D^2
 let W:=switch D e u x
 e+1≤ cap ∧
 den*(u*highRate e u x)+10*lowNumerator D e W 0^2≤den*(cap-(e+1)) ∧
 10*lowNumerator D e W u^2≤den*(cap-(e+1))
instance (D e W:ℕ) :Decidable (weightOK D e W) := by unfold weightOK; infer_instance
instance (D e u:ℕ) (x :Witness) :Decidable (filterOK D e u x) := by
 unfold filterOK
 infer_instance
instance (D e u cap:ℕ) (x :Witness) :Decidable (feeOK D e u cap x) := by
 unfold feeOK
 infer_instance
end
end qe6nVeb
end
section
set_option autoImplicit true
namespace qrfYkTd
open Finset P5_8_2 qxVnKgd
def acF (p l:ℤ) :ℤ :=
 8*(∑ o∈Icc l ((3919-p)/2),high p o (2*p+o-3919) 0)
private def row (p:ℤ) :ℤ:=acF p (max (3920-2*p) (p-1651))
private def f (i:ℕ) :ℤ:=row (1307+(i:ℤ))
end qrfYkTd
end
