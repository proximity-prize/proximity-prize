import ProximityPrize.SubmissionLower.ZE36Kga
import ProximityPrize.SubmissionLower.Zy3W3oe
import ProximityPrize.SubmissionLower.ZgfRUfb
import ProximityPrize.SubmissionLower.ZXxMpWa
import ProximityPrize.SubmissionLower.ZlfuKwd
set_option Elab.async false
section
set_option autoImplicit true
set_option maxHeartbeats 1000000
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace q8SCoCa
noncomputable section
open Polynomial q3u9Tnc
open P6 (K I node twist)
open P5_7_2 (A)
private theorem exists_moved (J:Input) : ∃ a :K,twist a≠a := by
  by_contra! h
  have hmap :J.model.E.map twist=J.model.E := by
    ext i
    rw [coeff_map,h]
  have hd:=natDegree_eq_zero_of_isUnit (isCoprime_self.mp (hmap ▸ J.model.adjacent_coprime))
  have hp:0<((J.model.E.natDegree :ℤ)-J.model.factor.natDegree -
      P0.uO J.model.A₀ J.model.A₁).toNat :=J.positive_height
  rw [hd] at hp
  omega
private def a (J:Input) :K:=Classical.choose (exists_moved J)
private def E (J:Input) :K[X] :=Polynomial.X - C (a J)
private theorem adj (J:Input) :IsCoprime (E J) ((E J).map twist) := by
  simpa only [E,Polynomial.map_sub,map_X,map_C] using
    isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr
      (show twist (a J)≠a J from Classical.choose_spec (exists_moved J)).symm).isUnit
private theorem eval_ne (i:I) (f :K) (hf :twist f≠f) :
    ((Polynomial.X:K[X]) - C f).eval (node i)≠0:= by
  rw [eval_sub,eval_X,eval_C]
  intro h
  have he :=sub_eq_zero.mp h
  exact hf (he ▸ gR.Native.ahU i)
private def words (J:Input) :P5.e9:= fun j i =>
  if j=0 then (J.model.word i-J.model.shift)/(E J).eval (node i)
  else 1/(E J).eval (node i)
private def model (J:Input) :P5.jG (words J) ∅ where
  shift:=J.model.shift
  pencil₀:=0
  pencil₁:=0
  pencil₀_degree := by decide
  pencil₁_degree := by decide
  E :=E J
  factor :=1
  Q:=1
  A₀:=1
  A₁:=0
  word:=J.model.word
  word_fixed:=J.model.word_fixed
  word_deleted:= by simp
  E_monic:=monic_X_sub_C _
  aFF:= fun i=>eval_ne i _ (Classical.choose_spec (exists_moved J))
  factor_nodes := by simp
  coprime_factor :=isCoprime_one_right
  offset_proper := by simp [E,degree_X_sub_C]
  offset_reduced:=isCoprime_one_left
  adjacent_coprime :=adj J
  amplitudes_primitive :=isCoprime_one_left
  first_amplitude_unit :=isCoprime_one_left
  aVi:= by simpa [E,P0.uO] using (show 1≤P5.DY by decide)
  first_word:= by
    intro i _
    have hi:=eval_ne i _ (Classical.choose_spec (exists_moved J))
    change (E J).eval (node i)≠0 at hi
    simp [words]
    field_simp [hi]
    ring
  second_word:= by
    intro i _
    have hi:=eval_ne i _ (Classical.choose_spec (exists_moved J))
    change (E J).eval (node i)≠0 at hi
    simp [words,hi]
private def family (J:Input) :P1.bje A (model J) ∅ where
  scalar :=J.family.scalar
  mark := fun _ h=>(Finset.notMem_empty _ h).elim
  distinct := by rw [Finset.coe_empty]; exact Set.injOn_empty _
private theorem iF (J:Input) : (model J).iF=1 := by
  simp [P1.FJ.iF,model,E,P0.uO]
def oldInput (J:Input) :qe6nVeb.Input where
  words :=words J
  deleted := ∅
  model :=model J
  CF := ∅
  family :=family J
  shift_not_mem:= by simp
  block :=(P6_7.dsh (model J) (family J)).choose
  bY:=(P6_7.dsh (model J) (family J)).choose_spec
  positive_height:= by rw [iF]; decide
  D:=J.D
  degree_lo:=J.degree_lo
  degree_hi:=J.degree_hi
  degree := by simp
private theorem hit_eq (J:Input) (γ:K) (i:I) :
    qe6nVeb.hit (oldInput J) γ i↔hit J γ i:=Iff.rfl
private theorem sites_eq (J:Input) (γ:K) :qe6nVeb.sites (oldInput J) γ=sites J γ:= by
  classical
  ext i
  rw [P5_7_7.mem_sites,qe6nVeb.sites,Finset.mem_filter]
  exact (and_iff_right (Finset.mem_univ i)).trans (hit_eq J γ i)
private theorem locator_eq (V:Finset I) :qe6nVeb.mL V=P5_7_7.mL V:= by
  unfold qe6nVeb.mL P5_7_7.mL
  exact Finset.prod_congr rfl fun _ _=>rfl
def oldWord {J:Input} {U:Finset K} (B:DualWord J U) :qe6nVeb.DualWord (oldInput J) U where
  a₀:=B.a₀
  a₁:=B.a₁
  b₀:=B.b₀
  b₁:=B.b₁
  u₀:=B.u₀
  u₁:=B.u₁
  order :=B.order
  gMz :=B.gMz
  row₀:=B.row₀
  row₁:=B.row₁
  determinant:= by rw [locator_eq]; exact B.determinant
  rows_hit :=B.rows_hit
  target :=B.target
  P:=B.P
  Q:=B.Q
  denominator :=B.denominator
  coprime :=B.coprime
  numerator_ix := by intro γ hγ; rw [sites_eq,locator_eq]; exact B.numerator_id γ hγ
  denominator_ix := by intro γ hγ; rw [sites_eq,locator_eq]; exact B.denominator_id γ hγ
  degrees := by intro γ hγ; rw [sites_eq]; exact B.degrees γ hγ
  dual_hits := fun γ hγ i=>(B.dual_hits γ hγ i).trans (not_congr (hit_eq J γ i).symm)
end
end q8SCoCa
end
section
set_option autoImplicit true
namespace qQNoJ5c
noncomputable section
open P6 (K p)
open P5_7 (midAgreement)
open P5_7_3 (fO)
open qAxtVye (nV BC alO lineUnit branchDegree horizontalBase horizontalUnit)
open cu (aZ FX kr qD)
open gT (Ambient tK IZ kM abX aQ bbt aSf)
open pI (xN dM)
def I0 {cap u del} {M:P1.FJ cap u del} {Γ} (F:P1.bje midAgreement M Γ)
    (I:Ideal Ambient) (γ:K) :Prop :=IZ I (M.label γ) (F.scalar γ)
structure aAT {cap u del} (M:P1.FJ cap u del) {Γ} (F:P1.bje midAgreement M Γ)
    (b:fO) (freeFixed movingFixed:tK) where
  parents :Finset (Ideal Ambient)
  active : ∀ I∈parents,xN I
  a4E : ∀ I∈parents,I.height=2
  bst:dM parents (BC b)
  seed :qQ.VN
  acI:seed.curve.totalDegree≤BC b 2
  seed_points :seed.points.card≤BC b 3
  ordinates :Finset FX
  ordinate_le :ordinates.card≤BC b 0
  content:aZ
  content_ne :content≠0
  content_le :content.totalDegree≤(nV b 0).free.shape.U + (nV b 0).moving.shape.U
  Eh : ∀ γ∈Γ,seed.ow (M.label γ)∨kr (F.scalar γ)∈ordinates ∨
    qD (M.label γ) content=0∨gT.FW freeFixed (F.scalar γ)=0 ∨
    gT.FW movingFixed (F.scalar γ)=0 ∨ ∃ I∈parents,I0 F I γ
def aKd (b:fO) {cap u del} (M:P1.FJ cap u del) {Γ}
    (F:P1.bje midAgreement M Γ) :Prop :=
  ∀ T⊆Γ,∀ I g H,0<g→ g<p→bbt I g H →
    Module.finrank aQ (abX I)<p →
    (∀ γ∈T,aSf I (M.label γ) (F.scalar γ)) →
    (T.card:ℚ)≤alO b g*H+g
def HorizontalTariff (b:fO) {cap u del} (M:P1.FJ cap u del) {Γ}
    (F:P1.bje midAgreement M Γ) :Prop :=
  ∀ T⊆Γ,∀ (I:Ideal kM) g d H,0<g→0<d→bbt I g H →
    Module.finrank aQ (abX I)=d*g→d*g<p →
    (∀ γ∈T,aSf I (M.label γ) (F.scalar γ)) →
    (g=1→(T.card:ℚ)≤lineUnit b*H+1) ∧
    (2≤g→branchDegree b g<p →
      (T.card:ℚ)≤horizontalBase d g*(d*g:ℚ)+horizontalUnit b g*H+g)
end
end qQNoJ5c
end
