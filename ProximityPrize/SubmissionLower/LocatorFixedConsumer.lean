import ProximityPrize.SubmissionLower.LocatorFixed
import ProximityPrize.SubmissionLower.LocatorFixedHybrid
import ProximityPrize.SubmissionLower.LocatorFactorReplacement
import ProximityPrize.SubmissionLower.LocatorArithmetic
import ProximityPrize.SubmissionLower.LocatorBatchProductRoute
namespace ProximityPrize.SubmissionLower.LocatorFixedConsumer
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN319 RCN286 RCN238 RCN243 RCN266 RCN140 RCN130 RCN156 RCN234 RCN275 LocatorFactorAggregate
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600
def wholeSupport:ResidualSupportParameters:=
  ⟨28,127,5964,by decide,by decide,by decide,by decide⟩

/-- The selected TCap/B gcd is wider in the middle and slope coordinates
than `wholeSupport`.  It is nevertheless a valid carrier for the initial
A-source split; only the factors in the universal child are later charged by
the narrow fixed-phase argument. -/
def wideSupport:ResidualSupportParameters:=
  ⟨33,153,5964,by decide,by decide,by decide,by decide⟩

/-- Regular allowance used by the initial A-source split. -/
abbrev initialRegularCap:ℕ:=LocatorArithmetic.fixedRegularCap

/-- Pure bookkeeping for the initial A-source split.  `U` is the set of
factors universal on the current A kernel.  The universal child is bounded
in aggregate by `phaseCap`; every factor outside it is charged by its direct
A-helper cap.  No claim about divisibility is hidden in this lemma. -/
theorem initial_A_regularSeeds_sum_le
    (H:P4) (selected:K → Polynomial K) (Gamma:Finset K)
    (U:Finset (RegularIndex H)) (phaseCap:ℕ)
    (helperCap:RegularIndex H → ℕ)
    (hphase:(∑ F ∈ U,(regularSeeds H selected Gamma F).card) ≤ phaseCap)
    (hhelper:∀ F ∈ (Finset.univ:Finset (RegularIndex H)) \ U,
      (regularSeeds H selected Gamma F).card ≤ helperCap F)
    (hledger:phaseCap+
      (∑ F ∈ (Finset.univ:Finset (RegularIndex H)) \ U,helperCap F) ≤
        initialRegularCap) :
    (∑ F:RegularIndex H,(regularSeeds H selected Gamma F).card) ≤
      initialRegularCap:=by
  classical
  have hsplit:(Finset.univ:Finset (RegularIndex H)) =
      U ∪ ((Finset.univ:Finset (RegularIndex H)) \ U):=by
    ext F
    simp only [Finset.mem_univ,Finset.mem_union,Finset.mem_sdiff,true_and]
    tauto
  have hdisjoint:Disjoint U
      ((Finset.univ:Finset (RegularIndex H)) \ U):=by
    apply Finset.disjoint_left.mpr
    intro F hFU hFd
    exact (Finset.mem_sdiff.mp hFd).2 hFU
  change (∑ F ∈ (Finset.univ:Finset (RegularIndex H)),
    (regularSeeds H selected Gamma F).card) ≤ initialRegularCap
  rw [hsplit,Finset.sum_union hdisjoint]
  exact (Nat.add_le_add hphase
    (Finset.sum_le_sum (fun F hF=>hhelper F hF))).trans hledger

/-- Cover/singular wrapper for the wide selected gcd.  The regular term is
supplied by `initial_A_regularSeeds_sum_le`; the singular argument legitimately
uses the full B contact/slope box and does not require the narrow A caps. -/
theorem wide_fixed_count_le
    (H:P4) (hH:H ≠ 0)
    (hbox:H ∈ RCN174.globalCoefficientBox K 20134512 131071 5964 33)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hsolution:∀ gamma ∈ Gamma,specialization K (selected gamma) gamma H=0)
    (hdegree:∀ gamma ∈ Gamma,(selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181392 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80752)
    (hregular:(∑ F:RegularIndex H,
      (regularSeeds H selected Gamma F).card) ≤ initialRegularCap) :
    Gamma.card ≤ initialRegularCap+LocatorArithmetic.fixedSingularCap:=by
  have hspos:1 ≤ LocatorArithmetic.fixedSingular.s:=by decide
  have hssmall:LocatorArithmetic.fixedSingular.s < 2130706433:=by decide
  have hwpos:1 ≤ LocatorArithmetic.fixedSingular.w:=by decide
  have hwsmall:LocatorArithmetic.fixedSingular.w < 2130706433:=by decide
  have hkD:LocatorArithmetic.fixedSingular.w <
      LocatorArithmetic.fixedSingular.kappa*LocatorArithmetic.fixedSingular.D:=by
    decide
  have halgpos:1 ≤ LocatorArithmetic.fixedSingular.algebraicCap:=by decide
  have himpsmall:LocatorArithmetic.fixedSingular.implicitYCap < 2130706433:=by
    decide
  have halgsmall:LocatorArithmetic.fixedSingular.algebraicCap < 2130706433:=by
    decide
  have hwa:LocatorArithmetic.fixedSingular.w <
      LocatorArithmetic.fixedSingular.a:=by decide
  have han:LocatorArithmetic.fixedSingular.a ≤
      LocatorArithmetic.fixedSingular.n:=by decide
  have hcover:=RCN239.card_le_regular_sum_add_singular
    (LocatorFixed.profile 20134512 5964 33) H hH hbox
    hspos hssmall hwpos hkD halgpos halgsmall
    selected Gamma hsolution
  have hsing:=CommonShearTightPrototype.singularSeeds_count_le_countCap
    LocatorArithmetic.fixedSingular H hH hbox
    hspos hssmall hwpos hwsmall hkD halgpos himpsmall halgsmall hwa han
    selected Gamma (Finset.univ:Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by
      change (Finset.univ:Finset I).card=262144
      rw [Finset.card_univ]
      change Fintype.card (Fin (2 ^ 18))=262144
      rw [Fintype.card_fin]
      decide) hdegree hagreement (by
        simpa only [LocatorArithmetic.fixedSingular,
          RCN318.TightParameters.errors, LocatorArithmetic.n,
          LocatorArithmetic.w, LocatorArithmetic.agreements,
          Nat.reduceSub] using hno)
  exact hcover.trans (Nat.add_le_add hregular hsing)
end
end ProximityPrize.SubmissionLower.LocatorFixedConsumer
