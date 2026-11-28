import ProximityPrize.SubmissionLower.Z6970NativeNearLightSources
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.R6970Height2313NativeLow

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lower6960.Prefix6969Early

noncomputable section

open Finset Polynomial
open K1 (I K p)
open K1_14 (Jet jetAt L)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2_2 (Active mass)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Far6969RescueGeometry (Model Family word)
open Prefix6969Main (Band)
open Research6969 Research6966
open scoped Classical BigOperators

theorem native_light_fee_exact_2308 :
    Prefix6969MainCases.NativeLight2308.price.fee +
    ((ordinaryNearOrd-Prefix6969MainCases.NativeLight2308.price.retainedCredit 0)*338 +
      (ordinaryNearSeed-Prefix6969MainCases.NativeLight2308.price.retainedCredit 1)*5697) + lowFee = 233390644175971991 := by decide +kernel



theorem native_light_packet_2308 {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2308≤M.overhead.toNat) (hi : M.overhead.toNat≤2411)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G)
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (slope : G.natDegree=1) (quad : jetDegree G=2) (i : Fin 56)
    (positive : 1≤seedDegree G) (width : seedDegree G≤seed i)
    (low : RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw<threshold i) :
    Nonempty (Packet F Crt ordinaryNearFee ordinaryNearOrd ordinaryNearSeed 351 6143) := by
  have prime := Prefix6969MiddleTransfer.prime_of_irred known.1
  have lower := HelperWeightCap.weight_lower phys prime.ne_zero (131071-M.overhead.toNat) (by omega)
  rw [quad,slope] at lower
  have floor : 257319≤RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw := by omega
  obtain ⟨R,J,C,A,same,pay,ms,mg,mo,covered⟩ := Prefix6969Main.main_prefix F Crt
    Prefix6969MainCases.NativeLight2308.plan Prefix6969MainCases.NativeLight2308.valid Band.near
    Prefix6969MainCases.NativeLight2308.price Prefix6969MainCases.NativeLight2308.priced
    Prefix6969MainCases.NativeLight2308.sources (by decide) lo hi noPole residues phys known quad.ge positive floor
  let T := Γ.filter (fun γ=>jetAt G (M.label γ) (F.scalar γ)=0)
  have lowPay : T.card≤lowFee :=
    Research6970.Height2313.Lower6960.Prefix6969Early.NativeLightLow.count F (filter_subset _ _) lo hi noPole
      (fun γ h=>residues γ (mem_filter.mp h).1) phys prime slope quad i width low
      (fun _ h=>(mem_filter.mp h).2)
  have ma (P) (h:P∈J.final) : Active P := (J.kept_geom (mem_filter.mp h).1).1
  obtain ⟨f,project⟩:=JointProjection.exists_product A (fun q h=>(mg q h).1)
  have measures := JointProjection.measures project J.final ma mo
  have md : mass J.final 0 ≤ 338 := by
    have q := ms 0
    change (mass J.final 0 : ℚ) ≤ 462882/1369 at q
    apply Nat.le_of_lt_succ
    exact_mod_cast q.trans_lt (by decide +kernel : (462882/1369 : ℚ) < 339)
  have mv : mass J.final 1 ≤ 5697 := by
    have q := ms 1
    change (mass J.final 1 : ℚ) ≤ 15598401/2738 at q
    apply Nat.le_of_lt_succ
    exact_mod_cast q.trans_lt (by decide +kernel : (15598401/2738 : ℚ) < 5698)
  let price := Prefix6969MainCases.NativeLight2308.price
  let extra := (ordinaryNearOrd-price.retainedCredit 0)*338+(ordinaryNearSeed-price.retainedCredit 1)*5697
  have adj : ordinaryNearOrd*f.natDegree+ordinaryNearSeed*K1_14_4.seedDegree f≤
      price.charge J.final+extra := by
    have p0:=Nat.mul_le_mul_left ordinaryNearOrd measures.1
    have p1:=Nat.mul_le_mul_left ordinaryNearSeed measures.2
    have q0 := compensate ordinaryNearOrd (price.retainedCredit 0) (mass J.final 0) 338 md
    have q1 := compensate ordinaryNearSeed (price.retainedCredit 1) (mass J.final 1) 5697 mv
    unfold Prefix6969Main.Pricing.charge extra
    simp only [Fin.sum_univ_four]
    omega
  have bill : price.fee+extra+lowFee≤ordinaryNearFee := by
    change Prefix6969MainCases.NativeLight2308.price.fee +     ((ordinaryNearOrd-Prefix6969MainCases.NativeLight2308.price.retainedCredit 0)*338 +       (ordinaryNearSeed-Prefix6969MainCases.NativeLight2308.price.retainedCredit 1)*5697) + lowFee ≤ ordinaryNearFee
    rw [native_light_fee_exact_2308]
    decide
  change C.paid.card+price.charge J.final≤price.fee at pay
  refine ⟨⟨C.paid∪T,A,f,project,fun q h=>(mg q h).1,fun q h=>(mg q h).2,
    (measures.1.trans md).trans (by decide),(measures.2.trans mv).trans (by decide),?_,?_⟩⟩
  · have union:=card_union_le C.paid T
    omega
  · intro γ hγ
    by_cases root : jetAt G (M.label γ) (F.scalar γ)=0
    · exact Or.inl (mem_union_right _ (mem_filter.mpr ⟨hγ,root⟩))
    · have inMain : γ∈R.marks := mem_filter.mpr ⟨hγ,by simpa only [same] using root⟩
      rcases covered γ inMain with p|on
      · exact Or.inl (mem_union_left _ p)
      · exact Or.inr on


end
end Lower6960.Prefix6969Early
