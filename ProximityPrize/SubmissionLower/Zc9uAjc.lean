import ProximityPrize.SubmissionLower.P6Defs
import ProximityPrize.SubmissionLower.Zo0SdJd
set_option Elab.async false
set_option autoImplicit true
namespace P6_7
noncomputable section
open Polynomial
open P6 (jG gJ K node p twist)
open P5_7 (Qn HeightPrice FarBand Jr bbk farAgreement Pairs axS agA terminal)
open cu (L j9 vP kr qD rD)
open qQ (zI N5)
def YQ {A h u del} (M:P1.FJ h u del) {Γ} (F:P1.bje A M Γ)
    (H :L[X]) :Prop :=
  let σ:=frobenius L p
  let H' := H.map σ
  H.Monic∧H.natDegree=M.iF.toNat∧H∣j9 M.E ∧
  H'.Monic∧H'.natDegree=M.iF.toNat∧H' ∣ j9 (M.E.map twist) ∧
  IsCoprime H H' ∧
  (∀ i,H.eval (algebraMap K L (node i))≠0∧H'.eval (algebraMap K L (node i))≠0) ∧
  IsCoprime (j9 (M.Q*M.factor*M.A₀)) H ∧
  IsCoprime ((j9 (M.Q*M.factor*M.A₀)).map σ) H' ∧
  ∀ γ∈Γ,
    let z :=algebraMap K L (M.label γ)
    let D:=j9 (M.factor*M.wK γ)
    let S:=j9 (F.scalar γ)
    IsCoprime D H∧IsCoprime (D.map σ) H' ∧
    H∣D *S+C z*j9 M.Q ∧
    H' ∣ D.map σ*S+C (z^p)*(j9 M.Q).map σ
def jX (b:gJ) :HeightPrice :=⟨b.lo,b.hi,b.regular⟩
def RegularBound (A:ℕ) (r :HeightPrice) :Prop :=
  ∀ u del (M:jG u del) Γ (F:P1.bje A M Γ),
    Qn r.lo r.hi M.iF→M.shift∉Γ →
    ∀ H,YQ M F H→Γ.card≤ r.cap
inductive RectTail where
  | pruned | tailOne | tailTwo | tailThree
def RectTail.kA:RectTail→ gJ
  | .pruned => .rectPruned
  | .tailOne => .rectTailOne
  | .tailTwo => .rectTailTwo
  | .tailThree => .rectTailThree
abbrev nearRows :List HeightPrice :=P5_7.nearRows.drop 2
structure Source (b:FarBand) {H u del} (M:P1.FJ H u del) {Γ}
    (F:P1.bje farAgreement M Γ) (rows :vP) :Prop where
  nested : ∀ t,Jr b t → ∀ t',Jr b t' →
    t.shape.m=t'.shape.m→t.shape.B=t'.shape.B→t.shape.J=t'.shape.J →
    t.shape.U≤t'.shape.U → ∀ W W',W≤W' → rows t.shape W≤ rows t'.shape W'
  necessary : ∀ t,Jr b t → ∀ W<t.shape.m*farAgreement,∀ P∈rows t.shape W,
    ∀ γ∈Γ,rD P (M.label γ) (F.scalar γ)=0
  shape : ∀ t,Jr b t → ∀ W,∀ P∈rows t.shape W,qQ.oU P t.shape
  leading : ∀ t,Jr b t→qQ.aSa M.iF.toNat rows t.shape
  shift : ∀ t,Jr b t→qQ.bk4 M.iF.toNat rows t.shape
  ajB : ∀ t,Jr b t→bbk M.iF.toNat t rows
def axy {A H u del} (M:P1.FJ H u del) {Γ} (F:P1.bje A M Γ)
    (q:zI) (γ:K) :Prop :=
  q.asIdeal≤RingHom.ker
    (eval₂RingHom (eval₂RingHom (qD (M.label γ)) (kr (F.scalar γ)))
      (kr (F.scalar γ).derivative))
structure bkU (b:FarBand) {H u del} (M:P1.FJ H u del) {Γ}
    (F:P1.bje farAgreement M Γ) {rows :vP} (pairs :Pairs b M.iF.toNat rows) where
  book :Finset K
  book_bound:book.card≤b.row.prefixFee
  parents :Finset zI
  geometric : ∀ q∈parents,N5 q
  stage_pass : ∀ q∈parents,∀ s (hs :s∈b.row.stages),0<s.dI →
    axS (pairs s hs) q
  terminal_pass : ∀ q∈parents,agA rows (terminal b).shape q
  Eh : ∀ γ∈Γ,γ∈book ∨ ∃ q∈parents,axy M F q γ
end
end P6_7
