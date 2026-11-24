import ProximityPrize.SubmissionLower.ZpAvArb
import ProximityPrize.SubmissionLower.Z1qPXJc
import ProximityPrize.SubmissionLower.ZEdS9yd
import ProximityPrize.SubmissionLower.ZWB9BUc
set_option Elab.async false
section
set_option autoImplicit true
set_option Elab.async false
namespace P5_7_1_7Q434
theorem proof :P5_7_1_7_4_3_4.c3:=qaiVg1b.proof
end P5_7_1_7Q434
end
section
set_option autoImplicit true
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace P5_7_3_3_4_1_7_2
noncomputable section
open qL2osVa (Series)
open TrivSqZeroExt
private abbrev F:=FractionRing Series
private abbrev J:=DualNumber F
private def iJ {R E :Type} [CommRing R] [Field E] (e :R →+* E)
    (D:R →+ R) (hone :D 1=0) (hmul : ∀ a b,D (a*b)=a*D b+b*D a) :
    R →+* DualNumber E where
  toFun a :=⟨e a,e (D a)⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp [hone]
  map_add' a b:= by ext <;> simp
  map_mul' a b:= by
    apply TrivSqZeroExt.ext
    · exact e.map_mul a b
    · change e (D (a*b))=e a*e (D b)+e (D a)*e b
      simp only [hmul,map_add,map_mul,mul_comm]
private def seriesJet:Series →+* J :=
  iJ (algebraMap Series F) (PowerSeries.derivative (R:=cu.L)).toLinearMap.toAddMonoidHom
    (PowerSeries.derivative (R:=cu.L)).map_one_eq_zero
    (fun a b=>(PowerSeries.derivative (R:=cu.L)).leibniz a b)
private theorem seriesJet_unit (a : (nonZeroDivisors Series)) :IsUnit (seriesJet a) :=
  isUnit_iff_isUnit_fst.mpr <| isUnit_iff_ne_zero.mpr <|
    (map_ne_zero_iff _ (IsFractionRing.injective Series F)).mpr (nonZeroDivisors.ne_zero a.property)
private def fieldJet:F →+* J :=
  IsLocalization.lift (S:=F) seriesJet_unit
private theorem fieldJet_fst (a :F) : (fieldJet a).fst=a := by
  let π:=(fstHom F F F).toRingHom
  have he :π.comp fieldJet=RingHom.id F:= by
    apply IsLocalization.ringHom_ext (nonZeroDivisors Series)
    ext b
    simp [π,fieldJet,seriesJet,iJ]
  exact DFunLike.congr_fun he a
private def epF {E :Type} [Field E] [Algebra ℤ E]
    (f :E →+* DualNumber E) (hf : ∀ a,(f a).fst=a) :Derivation ℤ E E := by
  let d:E →+ E :=
    { toFun:= fun a=>(f a).snd
      map_zero' := by simp only [map_zero,snd_zero]
      map_add' := fun a b=> by simp only [map_add,snd_add] }
  refine { toFun:=d,map_add' := d.map_add
           map_smul' := fun n a=> by
             let M:Module ℤ E :=Algebra.toModule
             change d (M.smul n a)=n•d a
             exact (congrArg d (int_smul_eq_zsmul M n a)).trans (d.map_zsmul n a)
           map_one_eq_zero' := by change (f 1).snd=0; simp
           leibniz' := ?_ }
  intro a b
  change (f (a*b)).snd=a•(f b).snd+b•(f a).snd
  rw [map_mul,DualNumber.snd_mul,hf,hf]
  simp only [smul_eq_mul,mul_comm]
theorem exists_derivation : ∃ D:aQ →+ aQ,ExtendsSeed D:= by
  obtain ⟨D,hD⟩:=q85rTDe.extend_derivation (E :=aQ) (epF fieldJet fieldJet_fst)
  refine ⟨D.toLinearMap.toAddMonoidHom,?_,?_⟩
  · intro a b
    change D (a*b)=a*D b+b*D a
    exact D.leibniz a b
  · intro a
    change D (algebraMap F aQ (algebraMap Series F a))= _
    rw [hD]
    change algebraMap F aQ (fieldJet (algebraMap Series F a)).snd =
      algebraMap F aQ (algebraMap Series F (PowerSeries.derivative a))
    rw [show fieldJet (algebraMap Series F a)=seriesJet a from IsLocalization.lift_eq _ _]
    rfl
end
end P5_7_3_3_4_1_7_2
end
section
set_option autoImplicit true
set_option maxSynthPendingDepth 12
namespace P5_7_3_3_4_1_7_2
noncomputable section
open Polynomial P5_7_3_3_4_1_7

open q1kuFjb (mapTwice)
open P5 (p)
def c1 :Prop :=
  ∀ (f :LocalEquation) (g:ℕ),2≤g→ g<p →
    f.natDegree≤g→ IsUnit (f.coeff g) →
    ∃ (n:ℕ) (hn:n≠0) (b:Fin g→PowerSeries aQ),SplitAt f g n hn b
def c2 :Prop :=
  ∀ (f :LocalEquation) (g d j:ℕ),2≤g→LocalGuard f g d j →
    ∀ (n:ℕ) (hn:n≠0) (b:Fin g→PowerSeries aQ) (D:aQ →+ aQ),
      SplitAt f g n hn b→ExtendsSeed D →
      let e :=ramify jz n hn
      let T: (PowerSeries aQ)[X][X] :=
        ∏ i,(Polynomial.X - C (C (b i)+Polynomial.X *
          C (PowerSeries.mk fun k=>D (PowerSeries.coeff k (b i)))))
      mapTwice e (numerator f g)=C (C (e (denominator f g)))*T ∧
        T.Monic∧CentreShape (mapTwice PowerSeries.constantCoeff T) j
          (jz (physicalCentre (f.coeff g))) (jz (physicalCentre (f.coeff j)))
theorem of_children (h1 :c1) (h2 :c2) :P5_7_3_3_4_1_7.c2 := by
  intro f g d j hg hp h s hs0 hs
  obtain ⟨n,hn,b,hb⟩:=h1 f g hg hp h.1 h.2.1
  obtain ⟨D,hD⟩:=exists_derivation
  obtain ⟨hT,hm,hc⟩:=h2 f g d j hg h n hn b D hb hD
  obtain ⟨Q,hQ,hM,hC⟩:=descend hn h _ hT hm hc
  exact specialize hg h hQ hM hC hs0 hs
end
end P5_7_3_3_4_1_7_2
end
