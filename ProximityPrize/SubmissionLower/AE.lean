import Mathlib.Algebra.Azumaya.Basic
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Data.NNRat.Floor
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import ProximityPrize.SubmissionLower.AD
set_option Elab.async false
open _root_ renaming Finset→cy,Finset.range→lI,IsCoprime→aU,MvPolynomial.eval₂→mD,MvPolynomial.restrictSupport→lV,MvPolynomial.restrictSupport_finite→lJ,Polynomial.Bivariate.swap→nq,Polynomial.C→c9,Polynomial.X→lz
set_option autoImplicit true
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace K1
noncomputable section
open Polynomial Matrix CoreDefinitions Code
open gR
open ProximityPrize.Benchmark
open scoped BigOperators
abbrev K:=Native.K
abbrev I:=Native.I
abbrev e9:=Fin 2→ I→K
abbrev node :=IRSProfile.domain
abbrev p:=Native.p
abbrev kB:=Bx.lN K
abbrev nC:=Polynomial K[X]
structure B5 (u:e9) (γ:K) where
 support :cy I
 decoder :K[X]
 dw:180265≤ support.card
 degree :decoder.degree<131072
 lg : ∀ i∈support,decoder.eval (node i)=u 0 i+γ*u 1 i
 nonjoint : ¬ (NM node (u 0) 131072 support∧NM node (u 1) 131072 support)
def iy (u:e9) := QO node (u 0) (u 1) 49193 81879
def So (u:e9) :=AI p node (u 0) (u 1) 49193 81879
def Vv (u:e9) :=Bx.adJ (So u)
def R5 (u:e9) :=Bx.ay6 (So u)
def Normal (u:e9) (γ:K) :Prop :=
 ((So u).map (evalRingHom γ)).rank=Vv u
def bcD (u:e9) :Matrix (Fin 4×Fin 49193) (Fin 81880) K:= fun i j =>
  if i.1=0 then oX node (u 0) (i.2.val+j.val) else
  if i.1=1 then oX node (u 1) (i.2.val+j.val) else
  if i.1=2 then oX node (u 0) (i.2.val+j.val)^p else
    oX node (u 1) (i.2.val+j.val)^p
structure qo (u:e9) where
 a :ℕ
 b:ℕ
 c:ℕ
 ab:a≤b
 active :b≤81879
 inactive :81879<c
 top:c≤131072
 degreeSum:a+b+c=262146
 nullitySum:R5 u+a+b=163760
 level :kL.aKl
   (fun s j=>algebraMap K[X] kB (Principal.P8 p node (u 0) (u 1) s j))
   131072 a b c
def qo.height {u:e9} (T:qo u) :=131073 - T.c
abbrev Relation {u:e9} (T:qo u) :=
 kL.axT p node (u 0) (u 1) 131072 T.height
def y1 {u:e9} {T:qo u} (R:Relation T) :nC :=
 Principal.assemble (fun j=>R.coefficients (0,j))
def zv {u:e9} {T:qo u} (R:Relation T) :nC :=
 Principal.assemble (fun j=>R.coefficients (1,j))
def pJ {u:e9} {T:qo u} (R:Relation T) :cy I:= by
  classical
  exact Finset.univ.filter fun i =>
    (y1 R).eval (C (node i))=0∧(zv R).eval (C (node i))=0
def sZ (U:nC) :kB[X] :=
 U.map (algebraMap K[X] kB)
def vn (P:nC) (γ:K) :K[X] :=P.map (evalRingHom γ)
def seed :nC:=c9 (R:=K[X]) (lz (R:=K))
def jH (P:K[X]) :nC:=P.map c9
def twist:K →+* K:=frobenius K p
def uO (a₀ a₁:K[X]) :ℕ:=max a₀.natDegree a₁.natDegree
def Ox (a :K[X]) :K[X] :=
 ∏ j:Fin 6,a.map (iterateFrobenius K p j.val)
structure Reduction (u:e9) (T:qo u) (R:Relation T) where
 U:nC
 V:nC
 output :nC
 height:ℕ
 height_eq :height+(pJ R).card=T.height
 max_degree :max U.natDegree V.natDegree=height
 U_ne :U≠0
 V_ne :V≠0
 coprime :aU (sZ U) (sZ V)
 U_factor :y1 R=jH (mL node (pJ R))*U
 V_factor :zv R=jH (mL node (pJ R))*V
 output_factor :R.output=jH (mL node (pJ R))*output
 output_degree :output.degree<(131072+height:ℕ)
 deleted_error : ∀ γ,Normal u γ → ∀ M:B5 u γ,∀ i∈pJ R,
   M.decoder.eval (node i)≠u 0 i+γ*u 1 i
def Xb (U V:nC) :ℕ :=
  Module.finrank kB (Submodule.span kB (Set.range fun j:Fin 4 =>
    sZ (nq
     (if j=0 then U else if j=1 then seed*U else if j=2 then V else seed^p*V))))
def _root_.Aj.ajp (q:ℕ) (U V:nC) :ℕ :=
  Module.finrank kB (Submodule.span kB (Set.range fun j:Fin 4 =>
    sZ (nq
     (if j=0 then U else if j=1 then seed*U else if j=2 then V else seed^q*V))))
def JO (a :K[X]) (β:Fin 2→K[X]) :nC :=
 jH a*(jH ((β 0).map twist)+seed^p*jH ((β 1).map twist))
def _root_.Aj.NJ (q:ℕ) (a :K[X]) (β:Fin 2→K[X]) :nC :=
 jH a*(jH ((β 0).map twist)+seed^q*jH ((β 1).map twist))
def J9 (b:K[X]) (α:Fin 2→K[X]) :nC :=
 -(jH b*(jH (α 0)+seed*jH (α 1)))
def Z4 (U V U' V' : nC) :Prop :=U*V' = V*U'
def ake (u:e9) (deleted:cy I) (U V output :nC) :Prop :=
  ∀ i∉deleted,
    U.eval (C (node i))*(C (u 0 i)+Polynomial.X (R:=K)*C (u 1 i)) +
    V.eval (C (node i))*(C (u 0 i^p)+Polynomial.X (R:=K)^p*C (u 1 i^p)) =
      output.eval (C (node i))
def _root_.Aj.ad9 (q:ℕ) (u:e9) (deleted:cy I) (U V output :nC) :Prop :=
  ∀ i∉deleted,
    U.eval (C (node i))*(C (u 0 i)+Polynomial.X (R:=K)*C (u 1 i)) +
    V.eval (C (node i))*(C (u 0 i^q)+Polynomial.X (R:=K)^q*C (u 1 i^q)) =
      output.eval (C (node i))
structure KJ (u:e9) (T:qo u) (R:Relation T)
   (D:Reduction u T R) where
 rank_eq :Xb D.U D.V=3
 α:Fin 2→K[X]
 β:Fin 2→K[X]
 a :K[X]
 b:K[X]
 a_ne :a≠0
 b_ne :b≠0
 α_primitive :aU (α 0) (α 1)
 β_primitive :aU (β 0) (β 1)
 first_degree :a.natDegree+uO (β 0) (β 1)≤D.height
 second_degree :b.natDegree+uO (α 0) (α 1)≤D.height
 same_direction :Z4 D.U D.V (JO a β) (J9 b α)
 output :nC
 output_degree :output.degree<(131072+D.height:ℕ)
 nodes :ake u (pJ R) (JO a β) (J9 b α) output
structure jG (u:e9) (deleted:cy I) where
 shift:K
 pencil₀:K[X]
 pencil₁:K[X]
 pencil₀_degree :pencil₀.degree<131072
 pencil₁_degree :pencil₁.degree<131072
 E :K[X]
 factor :K[X]
 Q:K[X]
 A₀:K[X]
 A₁:K[X]
 word:I→K
 word_fixed : ∀ i,twist (word i)=word i
 word_deleted : ∀ i∈deleted,word i=0
 E_monic:E.Monic
 aFF : ∀ i,E.eval (node i)≠0
 factor_nodes : ∀ i∉deleted,factor.eval (node i)≠0
 coprime_factor :aU E factor
 offset_proper :Q.degree<E.degree
 offset_reduced:aU Q E
 adjacent_coprime :aU E (E.map twist)
 amplitudes_primitive :aU A₀ A₁
 first_amplitude_unit :aU A₀ E
 aVi:E.natDegree+uO A₀ A₁≤32680
 first_word : ∀ i∉deleted,
   E.eval (node i)*(u 0 i+shift*u 1 i - pencil₀.eval (node i)) =
     factor.eval (node i)*A₀.eval (node i)*word i
 second_word : ∀ i∉deleted,
   E.eval (node i)*(u 1 i - pencil₁.eval (node i)) =
     Q.eval (node i)+factor.eval (node i)*A₁.eval (node i)*word i
def jG.iF {u deleted} (M:jG u deleted) :ℤ :=
 (M.E.natDegree :ℤ)-M.factor.natDegree - uO M.A₀ M.A₁
def jG.label {u deleted} (M:jG u deleted) (γ:K) :K :=
 γ-M.shift
def jG.wK {u deleted} (M:jG u deleted) (γ:K) :K[X] :=
 M.A₀+Polynomial.C (M.label γ)*M.A₁
def jG.decoder {u deleted} (M:jG u deleted) {γ:K}
    (B:B5 u γ) :K[X] :=
  B.decoder-M.pencil₀-Polynomial.C (M.label γ)*M.pencil₁
structure awT {u deleted} (M:jG u deleted) (γ:K) (S:K[X]) where
 bad:B5 u γ
 avoids_deleted:Disjoint bad.support deleted
 scalar_fixed:S.map twist=S
 aic:S=0∨(S.natDegree :ℤ)≤131071+M.iF
 scalar_hits : ∀ i∈bad.support,S.eval (node i)=M.word i
 pole_unit :aU (M.wK γ) M.E
 identity :M.E*M.decoder bad-Polynomial.C (M.label γ)*M.Q =
  M.factor*M.wK γ*S
structure mJ {u deleted} (M:jG u deleted) (Γ:cy K) where
 scalar :K→K[X]
 mark : ∀ γ∈Γ,awT M γ (scalar γ)
 distinct :Set.InjOn scalar (Γ:Set K)
end
end K1
end
section
namespace aR
noncomputable section
open Polynomial K1
open scoped BigOperators
abbrev ao:=AlgebraicClosure K
abbrev embed:=algebraMap K ao
abbrev extend (S:K[X]) :=S.map embed
abbrev af (n:ℕ) :=MvPolynomial (Fin n) ao[X]
def jet (S:ao[X]) {n:ℕ} (i:Fin n) :ao[X] :=hasseDeriv i.val S
def cK {n:ℕ} (P:af n) (S:ao[X]) :ao[X] :=
 MvPolynomial.eval (jet S) P
def Z8 {n:ℕ} (P:af n) (S:ao[X]) :af n :=
 mD MvPolynomial.C (fun i=>MvPolynomial.X i+MvPolynomial.C (jet S i)) P
def wU {n:ℕ} (P:af n) (S:ao[X]) (d:ℕ) :Prop :=
 ∀ m∈(Z8 P S).support,d≤ m.sum (fun _ a=>a)
def tB {n:ℕ} (P:af n) (D:ℕ) :Prop :=
  ∀ m∈P.support,(P.coeff m).natDegree +
    m.sum (fun i a=>(133671 - i.val)*a)≤D
def qE {n:ℕ} (P:af n) :ℕ :=
 P.support.sup (fun m=>m.sum (fun i a=>i.val*a))
structure Shape where
 b:ℕ
 j:ℕ
 t:ℕ
 deriving DecidableEq
def shape (P:af 4) :Shape :=⟨P.totalDegree,qE P,P.degreeOf 3⟩
def aO (x y :Shape) :Prop :=x.b≤y.b∧x.j≤y.j∧x.t≤y.t
def dM {n:ℕ} (a :Fin n→Shape) :Prop :=
 (∀ i,1≤(a i).t∧3*(a i).t≤(a i).j∧(a i).j≤3*(a i).b) ∧
 (∑ i,(a i).b)≤120∧(∑ i,(a i).j)≤48∧(∑ i,(a i).t)≤10
structure jF (Γ:cy K) (s :K→K[X]) where
 H :ao[X]
 monic:H.Monic
 small:1≤H.natDegree∧H.natDegree≤2600
 nodes : ∀ i,H.eval (embed (node i))≠0
 degree : ∀ γ∈Γ,(s γ).natDegree≤131071+H.natDegree
 z :K→ao
 injective :Function.Injective z
 c:ao[X]
 q:ao[X]
 a₀:ao[X]
 a₁:ao[X]
 c_unit :aU c H
 q_unit :aU q H
 a₀_unit :aU a₀ H
 regular : ∀ γ∈Γ,aU (a₀+C (z γ)*a₁) H
 residue : ∀ γ∈Γ,H∣c*(a₀+C (z γ)*a₁)*extend (s γ)+C (z γ)*q
def wm (f :af 4) :Prop :=
  Irreducible f∧0<(shape f).t∧aO (shape f) ⟨120,48,10⟩ ∧
    tB f (90*180265 - 1)
def bhZ (f :af 4) (S:ao[X]) :ao[X] :=
  (mD c9
    (fun i:Fin 4=>if i=3 then lz else c9 (jet S i)) f).coeff (shape f).t
def Dd (f :af 4) (S:ao[X]) :Prop :=
 cK f S=0∧bhZ f S≠0
def Contact (w:I→K) (P:af 4) :Prop :=
  ∀ i (S:ao[X]),S.eval (embed (node i))=embed (w i) →
    (lz - C (embed (node i)))^3000∣cK P S
structure aw1 where
 common :af 3
 residual:af 3
 common_ne :common≠0
 residual_ne :residual≠0
 common_total:common.totalDegree≤6300
 common_index :qE common≤2403
 residual_total:residual.totalDegree≤952630000
 residual_index :qE residual≤322000000
def aw1.bqU (E :aw1) (S:ao[X]) :Prop :=
 cK E.common S=0∨wU E.residual S 41481
def symbols (b j:ℕ) :ℕ :=
 ∑ z∈lI (min b (j/3)+1),
 ∑ y∈lI (min (b - z) ((j-3*z)/2)+1),
 ∑ x∈lI (min (b - z - y) (j-3*z - 2*y)+1),(b - z - y - x+1)
def Shape.plus (p q:Shape) :Shape :=⟨p.b+q.b,p.j+q.j,p.t+q.t⟩
def Shape.scale (p:Shape) (k :ℕ) :Shape :=⟨k*p.b,k*p.j,k*p.t⟩
def Shape.iU (p:Shape) :Shape :=⟨max p.b p.j,p.j,p.t⟩
def Dn (p:Shape) :ℤ :=
 let b:ℤ:=p.b
 let j:ℤ:=p.j
 let t:ℤ:=p.t
 8*b*j^2*t - 24*b*j*t^2+24*b*t^3-4*j^3*t+14*j^2*t^2 - 20*j*t^3+9*t^4
def gI (h:Shape→ℤ) (a x :Shape) :=h (x.plus a) - h x
def iH (p q r s :Shape) :ℕ :=
 (gI (gI (gI (gI Dn p) q) r) s ⟨0,0,0⟩).toNat
def ceilDiv (a b:ℕ) :=(a+b - 1)/b
abbrev bf :ℕ:=133672
def bY (L:ℕ) (p:Shape) :Shape :=
 let i:=2*L*(p.j-3)+L+3
 ⟨max (1+2*L*(p.b - 1)) i,i,min (2*L*(p.t - 1)+L+1) (i/3)⟩
def qP (L:ℕ) (p:Shape) :Shape :=
 let i:=4+(L - 5)*(p.j - 2)
 ⟨max (1+(L - 5)*(p.b - 1)) i,i,min (2+(L - 5)*p.t) (i/3)⟩
def ajN (p:Shape) :Shape :=
 let i:=3+bf*(p.j - 2)
 ⟨max (1+bf*(p.b - 1)) i,i,min (bf+1) (i/3)⟩
def acX (x :Shape) :Prop :=x.b≤60∧x.j≤32
end
end aR
end
section
namespace aR
noncomputable section
open Polynomial K1
open scoped BigOperators
theorem gEn (P:ao[X]) (hm:P.Monic) (h:ℕ) (hh:h≤P.natDegree) :
  ∃ H :ao[X],H.Monic∧H.natDegree=h∧H∣P:= by
 classical
 have hroots :h≤P.roots.card:=hh.trans_eq (IsAlgClosed.splits P).natDegree_eq_card_roots
 have hpos :0<(P.roots.powersetCard h).card:= by
  rw [Multiset.card_powersetCard]
  exact Nat.choose_pos hroots
 obtain ⟨t,ht⟩:=Multiset.card_pos_iff_exists_mem.mp hpos
 obtain ⟨htle,htcard⟩:=Multiset.mem_powersetCard.mp ht
 exact ⟨_,monic_multisetProd_X_sub_C t,(natDegree_multiset_prod_X_sub_C_eq_card t).trans htcard,
  (t.prod_X_sub_C_dvd_iff_le_roots hm.ne_zero).mpr htle⟩
end
end aR
end
section
namespace xE
noncomputable section
open aR PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
abbrev M7:=DifferentialPolynomial ao 3
abbrev UT:=JetVariable 3 →₀ ℕ
abbrev Local:=LocalPolynomial ao 3
def topWeight (v :JetVariable 3) :ℕ :=
 v.elim 0 (Pi.single (3:Fin 4) (1 :ℕ))
def ali (e :UT) :Prop :=
 e.weight jetDegreeWeight≤4012 ∧
 e.weight jetDerivativeWeight≤1650 ∧
 e.weight topWeight≤550 ∧
 e.weight (differentialWeight 133671)≤3000*180265 - 1
def aE1 :Set UT := { e | ali e }
theorem aQv :aE1.Finite := by
 refine (Finsupp.finite_of_nat_weight_le (differentialWeight (d:=3) 133671)
   ?_ (3000*180265 - 1)).subset (fun e he=>he.2.2.2)
 intro v
 cases v with
 | none=>decide
 | some j =>
   exact (differentialWeight_some_pos_of_order_lt_degree (by decide :3<133671) j).ne'
def W2 :Submodule ao M7 :=
 lV ao aE1
instance :Module.Finite ao W2 :=
 lJ aQv
abbrev sP:=Fin 4013×Fin 4650
def offset (i:sP) :ℤ:=(i.2.val :ℤ) - 1650
def TO (i:sP) :Set UT :=
  { e | ali e∧e none<3000 ∧
    e.weight jetDegreeWeight=i.1.val∧(e none :ℤ)-e.weight jetDerivativeWeight=offset i }
def aFx (i:sP) :Submodule ao M7 :=
 lV ao (TO i)
instance (i:sP) :Module.Finite ao (aFx i) :=
 lJ
  (aQv.subset (fun _ h=>h.1))
def denominator (u:ℤ) :ℤ :=
  if u<0 then 0 else
    let q:=u/6
    let r :=u % 6
    1+r*(r+1)/2+q*(22+7*r+r*(r - 1)/2) +
      (57+6*r)*(q*(q - 1)/2)+6*q*(q - 1)*(q - 2)
def gd (d u:ℤ) :ℤ :=
  if d<0 || u<0 then 0 else
    let v :=min u (3*d)
    denominator v - denominator (v - d - 1) - denominator (v - d - 2) -
      denominator (v - d-3)+denominator (v - 2*d-3) +
      denominator (v - 2*d-4)+denominator (v - 2*d - 5) -
      denominator (v-3*d-6)
def U1 (d u cap:ℤ) :ℤ :=
 if cap<0 then 0 else gd d u - gd (d - cap - 1) (u-3*(cap+1))
structure Flag where
 degree :ℤ
 lower :ℤ
 upper :ℤ
 cap:ℤ
 order :ℤ
def Jd (j:Fin 11) :Flag :=
  ![⟨1,0,0,0,0⟩,⟨1,1,1,0,0⟩,⟨1,2,2,0,1⟩,⟨1,3,3,1,2⟩,
    ⟨1,0,3,1,3⟩,⟨1,0,1,0,1⟩,⟨1,0,2,0,2⟩,⟨2,1,2,0,2⟩,
    ⟨2,1,3,1,3⟩,⟨2,2,4,1,4⟩,⟨3,2,3,1,3⟩] j
def BH (F:Flag) (power :Fin 11→ℕ) :Flag where
 degree :=F.degree - ∑ j,(power j:ℤ)*(Jd j).degree
 lower :=F.lower - ∑ j,(power j:ℤ)*(Jd j).lower
 upper :=F.upper - ∑ j,(power j:ℤ)*(Jd j).upper
 cap:=F.cap - ∑ j,(power j:ℤ)*(Jd j).cap
 order :=F.order - ∑ j,(power j:ℤ)*(Jd j).order
def oldCount (F:Flag) :ℤ :=
  U1 F.degree F.upper F.cap -
    U1 F.degree (min F.upper (F.lower - 1)) F.cap
def AO (F:Flag) :ℤ :=
  let balance :=F.order - 1-F.lower+F.degree
  if balance<0 then 0 else
    let jO:=min F.degree (balance/4)+1
    gd F.degree (F.order - 1) - gd (F.degree - jO) (F.order - 1 - 3*jO) -
      gd F.degree (F.lower - 1)+gd (F.degree - jO) (F.lower - 1)
def m5 (F:Flag) :ℤ :=
 if F.degree<0 || F.upper<0 || F.cap<0 then 0 else oldCount F - AO F
end
end xE
end
section
namespace xE
noncomputable section
open K1 aR Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators

def Ky :M7 ≃ₐ[ao] af 4 :=
 MvPolynomial.optionEquivRight ao (Fin 4)
theorem duE (Q:M7) (S:ao[X]) :
  cK (Ky Q) S=differentialSpecialization Q S:= by
 let values :Option (Fin 4)→ao[X] := fun v=>v.elim lz (jet S)
 have h:=MvPolynomial.aeval_map_optionEquivRight values Q
 have hx :values none=Polynomial.X:=rfl
 have hid : (AlgHom.id ao ao[X]).toRingHom=RingHom.id ao[X] :=rfl
 rw [hx,Polynomial.aeval_X_left,hid,MvPolynomial.map_id,MvPolynomial.aeval_eq_eval] at h
 have hhom:MvPolynomial.aeval values=differentialSpecializationHom (d:=3) S:= by
  apply MvPolynomial.algHom_ext
  intro v
  rw [MvPolynomial.aeval_X]
  cases v with
  | none=>exact (differentialSpecialization_x (d:=3) S).symm
  | some j=>exact (differentialSpecialization_jet j S).symm
 rw [hhom] at h
 exact h
end
end xE
end
