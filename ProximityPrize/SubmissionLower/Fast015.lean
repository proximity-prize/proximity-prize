import ArkLib.Data.CodingTheory.ListDecodability.AgreementRadius
import ProximityPrize.SubmissionLower.Fast011
import ProximityPrize.SubmissionLower.Fast012
import ProximityPrize.SubmissionLower.Fast014
import ProximityPrize.SubmissionLower.Fast013
set_option Elab.async false

section PackSource_ReciprocalNative
set_option autoImplicit true
/-! Native necessary ordinary Fp-list cap, conditional on the universal actual
IRS8 MCA cap. This is not a proof of that cap or a protocol claim. -/

namespace Sol1.Reciprocal.Native

set_option maxRecDepth 10000

noncomputable section
open Polynomial Code LinearCode CoreDefinitions
open ProximityPrize.Benchmark

abbrev Base := KoalaBear.Field
abbrev K := IRSProfile.Field
abbrev Index := IRSProfile.Index

local instance : DecidableEq Base := Classical.decEq Base
local instance : DecidableEq K := Classical.decEq K

def phi : Base →+* K := algebraMap Base K

def nodes : Index ↪ Base where
  toFun i := IRSProfile.baseNttDomain.node i
  inj' := by
    intro i j h
    apply IRSProfile.domain.injective
    change CompPoly.Extension.Ext.ofBase (IRSProfile.baseNttDomain.node i) =
      CompPoly.Extension.Ext.ofBase (IRSProfile.baseNttDomain.node j)
    exact congrArg CompPoly.Extension.Ext.ofBase h

def D : Finset Base := baseNodeSet nodes
def radius : ℝ := 338557 / 1048576
def cap : ℕ := 7 * 262144 ^ 3

theorem domain_eq : liftedDomain phi nodes = IRSProfile.domain := by
  ext i
  rfl

theorem code_eq : IRSProfile.code = repeatedRS phi nodes 131072 := by
  unfold IRSProfile.code ReedSolomon.Interleaved.irsCode repeatedRS
  rw [domain_eq]
  rfl

theorem domain_card : D.card = 262144 := by
  rw [D, baseNodeSet_card]
  norm_num [Index, IRSProfile.Index]

theorem field_card : Fintype.card K = 2130706433 ^ 6 := by
  change Fintype.card KoalaBear.Ext6 = 2130706433 ^ 6
  rw [KoalaBear.card_ext6]
  rfl

theorem threshold : (Fintype.card Index : ℝ) * (1 - radius) ≤ (177505 : ℝ) := by
  norm_num [Index, IRSProfile.Index, radius]

theorem support_threshold_iff (T : Finset Index) :
    (T.card : ℝ) ≥ Fintype.card Index * (1 - radius) ↔ 177505 ≤ T.card := by
  have hexact : (Fintype.card Index : ℝ) * (1 - radius) = (710019 : ℝ) / 4 := by
    norm_num [Index, IRSProfile.Index, radius]
  rw [hexact]
  constructor
  · intro h
    by_contra hsmall
    have hn : T.card ≤ 177504 := by omega
    have hr : (T.card : ℝ) ≤ 177504 := by exact_mod_cast hn
    linarith
  · intro h
    have hr : (177505 : ℝ) ≤ T.card := by exact_mod_cast h
    linarith

theorem room : D.card + 131072 * (cap + 1) ^ 2 < Fintype.card K := by
  rw [domain_card, field_card]
  exact native_evaluation_separation_budget

open Classical in
/-- The actual universal MCA cap at the exact requested native radius. -/
def UniversalMCACap : Prop :=
  ∀ U : Fin 2 → Index → Fin 8 → K,
    {gamma | IsMCA (AffineLineGenerator K) IRSProfile.code gamma U radius}.ncard ≤ cap

open Classical in
/-- Ordinary Fp list dimension131073, one above the native decoder dimension. -/
def OrdinaryBaseListCap : Prop :=
  ∀ w : Base → Base, (baseCloseSet D w 131072 177505).Finite ∧
    (baseCloseSet D w 131072 177505).ncard ≤ cap

/-- The universal actual native cap bounds each scalar reciprocal pole family. -/
theorem native_pole_cap (hcap : UniversalMCACap) (w : Base → Base)
    (alpha : K) (halpha : ∀ x ∈ D, phi x ≠ alpha) :
    (poleMCASet phi D w alpha 131072 177505).ncard ≤ cap := by
  classical
  refine pole_cap_of_actual_cap phi nodes w 131072 177505 cap radius
    (by norm_num) (by norm_num) threshold ?_ alpha halpha
  intro U
  rw [← code_eq]
  exact hcap U

theorem universal_native_mca_cap_implies_ordinary_base_list_cap
    (hcap : UniversalMCACap) : OrdinaryBaseListCap := by
  classical
  intro w
  apply base_list_finite_ncard_le_of_pole_cap phi D w 131072 177505 cap
    (by norm_num) (by norm_num) room
  exact native_pole_cap hcap w

def extendWord (w : Index → Base) : Base → Base :=
  Function.extend nodes w (fun _ ↦ 0)

@[simp] theorem extendWord_nodes (w : Index → Base) (i : Index) :
    extendWord w (nodes i) = w i := nodes.injective.extend_apply _ _ _

open Classical in
def indexBaseCloseSet (w : Index → Base) : Set (Polynomial Base) :=
  {P | P.natDegree ≤ 131072 ∧
    177505 ≤ (Finset.univ.filter fun i ↦ P.eval (nodes i) = w i).card}

theorem agreement_card (w : Index → Base) (P : Polynomial Base) :
    (D.filter fun x ↦ P.eval x = extendWord w x).card =
      (Finset.univ.filter fun i ↦ P.eval (nodes i) = w i).card := by
  classical
  symm
  apply Finset.card_bij (fun i _ ↦ nodes i)
  · intro i hi
    obtain ⟨_, hagree⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    exact ⟨(mem_baseNodeSet nodes (nodes i)).mpr ⟨i, rfl⟩, by simpa using hagree⟩
  · intro i _ j _ h
    exact nodes.injective h
  · intro x hx
    obtain ⟨hxD, hagree⟩ := Finset.mem_filter.mp hx
    obtain ⟨i, rfl⟩ := (mem_baseNodeSet nodes x).mp hxD
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hagree⟩, rfl⟩

theorem index_list_eq (w : Index → Base) :
    indexBaseCloseSet w = baseCloseSet D (extendWord w) 131072 177505 := by
  classical
  ext P
  change (P.natDegree ≤ 131072 ∧
    177505 ≤ (Finset.univ.filter fun i ↦ P.eval (nodes i) = w i).card) ↔ _
  have heq := agreement_card w P
  simpa only [baseCloseSet, Set.mem_ofPred_eq] using
    (and_congr_right fun _ ↦ (show
      177505 ≤ (Finset.univ.filter fun i ↦ P.eval (nodes i) = w i).card ↔
      177505 ≤ (D.filter fun x ↦ P.eval x = extendWord w x).card by rw [heq]))

/-- The necessary bound for every arbitrary Fp-valued received word on the
native Index, with the agreement count expressed on those actual indices. -/
theorem universal_native_mca_cap_implies_index_base_list_cap
    (hcap : UniversalMCACap) (w : Index → Base) :
    (indexBaseCloseSet w).Finite ∧ (indexBaseCloseSet w).ncard ≤ cap := by
  rw [index_list_eq]
  exact universal_native_mca_cap_implies_ordinary_base_list_cap hcap (extendWord w)


end
end Sol1.Reciprocal.Native
end PackSource_ReciprocalNative

section PackSource_NativeScalarListCore
set_option autoImplicit true
/-! Native scalar list consequence of an actual IRS8 MCA cap.
The MCA-cap premise is not proved here. -/

namespace Sol1.OneCount

noncomputable section
open Polynomial Code LinearCode CoreDefinitions
open ProximityPrize.Benchmark
open Sol1.Reciprocal Sol1.FiniteRowProjection

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev row8 := Fin 8
abbrev scalarCode : ModuleCode I K K := ReedSolomon.code IRSProfile.domain 131072
def radius : ℝ := Sol1.Reciprocal.Native.radius
def scalarDomain : Finset K := baseNodeSet IRSProfile.domain

local instance : DecidableEq K := Classical.decEq K

def ActualMCACap (B : ℕ) : Prop :=
  ∀ U : Fin 2 → I → row8 → K,
    {gamma | IsMCA (AffineLineGenerator K) IRSProfile.code gamma U radius}.ncard ≤ B

theorem lifted_id_domain : liftedDomain (RingHom.id K) IRSProfile.domain = IRSProfile.domain := by
  ext i
  rfl

theorem code_eq_id_repeat : IRSProfile.code =
    repeatedRS (RingHom.id K) IRSProfile.domain 131072 := by
  unfold IRSProfile.code ReedSolomon.Interleaved.irsCode repeatedRS
  rw [lifted_id_domain]
  rfl

theorem scalarDomain_card : scalarDomain.card = 262144 := by
  rw [scalarDomain, baseNodeSet_card]
  norm_num [I, IRSProfile.Index]

theorem separation_room (B : ℕ) (hB : B < 2 ^ 57) :
    scalarDomain.card + 131072 * (B + 1) ^ 2 < Fintype.card K := by
  have hpow : (B + 1) ^ 2 ≤ (2 ^ 57) ^ 2 :=
    Nat.pow_le_pow_left (show B + 1 ≤ 2 ^ 57 by omega) 2
  rw [scalarDomain_card]
  calc
    262144 + 131072 * (B + 1) ^ 2 ≤ 262144 + 131072 * (2 ^ 57) ^ 2 := by gcongr
    _ < Fintype.card K := by rw [Sol1.Reciprocal.Native.field_card]; norm_num

theorem projection_room (B : ℕ) (hB : B < 2 ^ 57) :
    (B + 1) ^ 2 ≤ Fintype.card K := by
  have hpow : (B + 1) ^ 2 ≤ (2 ^ 57) ^ 2 :=
    Nat.pow_le_pow_left (show B + 1 ≤ 2 ^ 57 by omega) 2
  exact hpow.trans (by rw [Sol1.Reciprocal.Native.field_card]; norm_num)

theorem scalar_pole_cap (B : ℕ) (hcap : ActualMCACap B) (w : K → K)
    (alpha : K) (halpha : ∀ x ∈ scalarDomain, x ≠ alpha) :
    (poleMCASet (RingHom.id K) scalarDomain w alpha 131072 177505).ncard ≤ B := by
  classical
  refine pole_cap_of_actual_cap (RingHom.id K) IRSProfile.domain w 131072 177505 B radius
    (by norm_num) (by norm_num) Sol1.Reciprocal.Native.threshold ?_ alpha halpha
  intro U
  rw [← code_eq_id_repeat]
  exact hcap U

theorem scalar_polynomial_list_cap (B : ℕ) (hB : B < 2 ^ 57)
    (hcap : ActualMCACap B) (w : K → K) :
    (baseCloseSet scalarDomain w 131072 177505).Finite ∧
      (baseCloseSet scalarDomain w 131072 177505).ncard ≤ B := by
  apply base_list_finite_ncard_le_of_pole_cap (RingHom.id K) scalarDomain w 131072 177505 B
    (by norm_num) (by norm_num) (separation_room B hB)
  exact scalar_pole_cap B hcap w

def extendScalarWord (w : I → K) : K → K :=
  Function.extend IRSProfile.domain w (fun _ ↦ 0)

@[simp] theorem extendScalarWord_domain (w : I → K) (i : I) :
    extendScalarWord w (IRSProfile.domain i) = w i :=
  IRSProfile.domain.injective.extend_apply _ _ _

theorem scalar_node_agreement_card (w : I → K) (P : K[X]) :
    (scalarDomain.filter fun x ↦ P.eval x = extendScalarWord w x).card =
      agreementCard (fun i ↦ P.eval (IRSProfile.domain i)) w := by
  classical
  symm
  apply Finset.card_bij (fun i _ ↦ IRSProfile.domain i)
  · intro i hi
    obtain ⟨_, hagree⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    exact ⟨(mem_baseNodeSet IRSProfile.domain (IRSProfile.domain i)).mpr ⟨i, rfl⟩,
      by simpa using hagree⟩
  · intro i _ j _ h
    exact IRSProfile.domain.injective h
  · intro x hx
    obtain ⟨hxD, hagree⟩ := Finset.mem_filter.mp hx
    obtain ⟨i, rfl⟩ := (mem_baseNodeSet IRSProfile.domain x).mp hxD
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hagree⟩, rfl⟩

/-- The ordinary K-polynomial cap controls finite scalar RS word lists.
The native code's degree<131072 is contained in the proved degree<=131072 list. -/
theorem finset_scalar_list_card_le (B : ℕ) (hB : B < 2 ^ 57)
    (hcap : ActualMCACap B) (w : I → K) (P : Finset (I → K))
    (hP : ∀ f ∈ P, f ∈ scalarCode ∧ 177505 ≤ agreementCard f w) : P.card ≤ B := by
  classical
  have : NeZero (131072 : ℕ) := ⟨by norm_num⟩
  choose poly hdegree heval using fun f : P ↦
    ReedSolomon.mem_code_iff_eval_of_ne_zero.mp (hP f.val f.property).1
  have hinj : Function.Injective poly := by
    intro f g hfg
    apply Subtype.ext
    funext i
    calc
      f.val i = (poly f).eval (IRSProfile.domain i) := (heval f i).symm
      _ = (poly g).eval (IRSProfile.domain i) := by rw [hfg]
      _ = g.val i := heval g i
  let polys : Finset K[X] := Finset.univ.image poly
  have hpolyscard : polys.card = P.card := by
    dsimp [polys]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hpolys : (polys : Set K[X]) ⊆
      baseCloseSet scalarDomain (extendScalarWord w) 131072 177505 := by
    intro q hq
    obtain ⟨f, _hf, rfl⟩ := Finset.mem_image.mp hq
    refine ⟨(hdegree f).le, ?_⟩
    rw [scalar_node_agreement_card]
    have hword : (fun i ↦ (poly f).eval (IRSProfile.domain i)) = f.val := funext (heval f)
    rw [hword]
    exact (hP f.val f.property).2
  obtain ⟨hfinite, hbound⟩ := scalar_polynomial_list_cap B hB hcap (extendScalarWord w)
  have hcount := (Set.ncard_le_ncard hpolys hfinite).trans hbound
  have hcount' : polys.card ≤ B := by simpa only [Set.ncard_coe_finset] using hcount
  rwa [hpolyscard] at hcount'


end
end Sol1.OneCount
end PackSource_NativeScalarListCore

section PackSource_NativeSquaredListCore
set_option autoImplicit true
/-! The actual twofold native IRS8 list is bounded by the same assumed MCA cap.
The alphabet is Fin2 -> Fin8 -> K, not a substituted code profile. -/

namespace Sol1.OneCount

noncomputable section
open Polynomial Code LinearCode CoreDefinitions
open ProximityPrize.Benchmark
open Sol1.FiniteRowProjection

abbrev A16 := Fin 2 → Fin IRSProfile.interleaving → K
abbrev R16 := Fin 2 × Fin 8
def squaredCode : ModuleCode I K A16 := IRSProfile.code ^⋈ (Fin 2)

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq A16 := Classical.decEq A16

def flatten (f : I → A16) : I → R16 → K := fun i r ↦ f i r.1 r.2

theorem flatten_injective : Function.Injective flatten := by
  intro f g h
  funext i j r
  exact congrFun (congrFun h i) (j,r)

theorem flatten_agreement_le (f w : I → A16) :
    agreementCard f w ≤ agreementCard (flatten f) (flatten w) := by
  apply agreementCard_mono f w (flatten f) (flatten w)
  intro i he
  funext r
  exact congrFun (congrFun he r.1) r.2

theorem flatten_rows_mem (f : I → A16) (hf : f ∈ squaredCode) :
    ∀ r : R16, (fun i ↦ flatten f i r) ∈ scalarCode := by
  change ∀ j : Fin 2, ∀ r : Fin 8, (fun i ↦ f i j r) ∈ scalarCode at hf
  intro r
  exact hf r.1 r.2

/-- Finite integer-agreement lists in the actual squared IRS code have
cardinality<=B, conditional only on the actual native MCA cap and field room. -/
theorem finset_squared_list_card_le (B : ℕ) (hB : B < 2 ^ 57)
    (hcap : ActualMCACap B) (w : I → A16) (P : Finset (I → A16))
    (hP : ∀ f ∈ P, f ∈ squaredCode ∧ 177505 ≤ agreementCard f w) : P.card ≤ B := by
  classical
  let flattened := P.image flatten
  have hflat : ∀ f ∈ flattened,
      (∀ r : R16, (fun i ↦ f i r) ∈ scalarCode) ∧
        177505 ≤ agreementCard f (flatten w) := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨hcode, hagree⟩ := hP g hg
    exact ⟨flatten_rows_mem g hcode, hagree.trans (flatten_agreement_le g w)⟩
  have hcount := finset_vector_list_card_le scalarCode 177505 B (projection_room B hB)
    (finset_scalar_list_card_le B hB hcap) (flatten w) flattened hflat
  have hcard : flattened.card = P.card := Finset.card_image_of_injective P flatten_injective
  rwa [hcard] at hcount

theorem close_agreement_ge (f w : I → A16)
    (hd : (δᵣ(w, f) : ℝ) ≤ radius) : 177505 ≤ agreementCard f w := by
  classical
  have hpos : 0 < Fintype.card I := by norm_num [I, IRSProfile.Index]
  have hradius : radius = 1 - ((710019 : ℝ) / 4) / Fintype.card I := by
    norm_num [radius, Sol1.Reciprocal.Native.radius, I, IRSProfile.Index]
  have hagree : (710019 : ℝ) / 4 ≤ Code.agree f w :=
    (Code.relHammingDist_le_one_sub_div_iff hpos).mp (by rwa [← hradius])
  change 177505 ≤ Code.agree f w
  by_contra hsmall
  have hn : Code.agree f w ≤ 177504 := by omega
  have hr : (Code.agree f w : ℝ) ≤ 177504 := by exact_mod_cast hn
  linarith

/-- The maximized independent twofold-IRS8 list term is bounded by B.
This is the actual Code.Lambda appearing in the benchmark's error expression. -/
theorem squared_lambda_le (B : ℕ) (hB : B < 2 ^ 57) (hcap : ActualMCACap B) :
    Code.Lambda (squaredCode : Set (I → A16)) radius ≤ (B : ℕ∞) := by
  classical
  apply Code.Lambda_le_iff_forall_encard_le.mpr
  intro w
  have hfinite : (Code.closeCodewordsRel (squaredCode : Set (I → A16)) w radius).Finite :=
    Set.toFinite _
  have hcard : hfinite.toFinset.card ≤ B := by
    apply finset_squared_list_card_le B hB hcap w hfinite.toFinset
    intro f hf
    obtain ⟨hcode, hclose⟩ := Code.mem_closeCodewordsRel_iff.mp (hfinite.mem_toFinset.mp hf)
    exact ⟨hcode, close_agreement_ge f w hclose⟩
  calc
    (Code.closeCodewordsRel (squaredCode : Set (I → A16)) w radius).encard =
        (hfinite.toFinset.card : ℕ∞) := hfinite.encard_eq_coe_toFinset_card
    _ ≤ (B : ℕ∞) := by exact_mod_cast hcard


end
end Sol1.OneCount
end PackSource_NativeSquaredListCore

section PackSource_WeightedSquaredList
set_option autoImplicit true
/- Adapted from sol1 C62SquaredList, using astra7's stronger unconditional scalar list theorem. -/

/-! Unconditional actual native IRS16 list term at the6917 radius.
The full scalar source/consumer and finite row projection are already proved. -/
namespace Astra7.NativeBudget
noncomputable section
open Polynomial Code LinearCode CoreDefinitions
open ProximityPrize.Benchmark Sol1.OneCount Sol1.FiniteRowProjection Sol1.C42
set_option maxRecDepth 10000
set_option maxHeartbeats 0

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq A16 := Classical.decEq A16

def radius6917 : ℝ := (queryRadius : ℝ)

/-- Original scalar RS words lie in the proved augmented ordinary polynomial list. -/
theorem finset_scalar_list_card_le (w : I → K) (P : Finset (I → K))
    (hP : ∀ f ∈ P, f ∈ scalarCode ∧ 180236 ≤ agreementCard f w) : P.card ≤ Astra7.weightedListCap := by
  classical
  have : NeZero (131072 : ℕ) := ⟨by norm_num⟩
  choose poly hdegree heval using fun f : P ↦
    ReedSolomon.mem_code_iff_eval_of_ne_zero.mp (hP f.val f.property).1
  have hinj : Function.Injective poly := by
    intro f g hfg
    apply Subtype.ext
    funext i
    calc
      f.val i = (poly f).eval (IRSProfile.domain i) := (heval f i).symm
      _ = (poly g).eval (IRSProfile.domain i) := by rw [hfg]
      _ = g.val i := heval g i
  let polys : Finset K[X] := Finset.univ.image poly
  have hpolyscard : polys.card = P.card := by
    dsimp [polys]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hpolys : (polys : Set K[X]) ⊆
      ReedSolomon.closePolynomialSet IRSProfile.domain w 131073 180236 := by
    intro q hq
    obtain ⟨f,_hf,rfl⟩ := Finset.mem_image.mp hq
    refine ⟨?_, ?_⟩
    · have hd : (poly f).natDegree < 131073 := (hdegree f).trans (by norm_num)
      exact (Polynomial.degree_le_natDegree).trans_lt (by exact_mod_cast hd)
    · have hword : (fun i ↦ (poly f).eval (IRSProfile.domain i)) = f.val := funext (heval f)
      change 180236 ≤ agreementCard (fun i ↦ (poly f).eval (IRSProfile.domain i)) w
      rw [hword]
      exact (hP f.val f.property).2
  obtain ⟨hfinite,hbound⟩ := Astra7.native_weighted_complete_list w
  have hcount := (Set.ncard_le_ncard hpolys hfinite).trans hbound
  have hcount' : polys.card ≤ Astra7.weightedListCap := by simpa only [Set.ncard_coe_finset] using hcount
  rwa [hpolyscard] at hcount'

theorem list_projection_room : (Astra7.weightedListCap + 1) ^ 2 ≤ Fintype.card K :=
  projection_room Astra7.weightedListCap (by norm_num [Astra7.weightedListCap])

/-- The actual alphabet is Fin2 -> Fin8 -> K; flattening only reindexes its rows. -/
theorem finset_squared_list_card_le (w : I → A16) (P : Finset (I → A16))
    (hP : ∀ f ∈ P, f ∈ squaredCode ∧ 180236 ≤ agreementCard f w) : P.card ≤ Astra7.weightedListCap := by
  classical
  let flattened := P.image flatten
  have hflat : ∀ f ∈ flattened,
      (∀ r : R16, (fun i ↦ f i r) ∈ scalarCode) ∧
        180236 ≤ agreementCard f (flatten w) := by
    intro f hf
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨hcode,hagree⟩ := hP g hg
    exact ⟨flatten_rows_mem g hcode,hagree.trans (flatten_agreement_le g w)⟩
  have hcount := finset_vector_list_card_le scalarCode 180236 Astra7.weightedListCap list_projection_room
    finset_scalar_list_card_le (flatten w) flattened hflat
  have hcard : flattened.card = P.card := Finset.card_image_of_injective P flatten_injective
  rwa [hcard] at hcount

theorem close_agreement_ge (f w : I → A16)
    (hd : (δᵣ(w,f) : ℝ) ≤ radius6917) : 180236 ≤ agreementCard f w := by
  classical
  have hpos : 0 < Fintype.card I := by norm_num [I,IRSProfile.Index]
  have hradius : radius6917 = 1 - (180236 : ℝ) / Fintype.card I := by
    norm_num [radius6917,queryRadius,claimedRadius,I,IRSProfile.Index]
  have hagree : (180236 : ℝ) ≤ Code.agree f w :=
    (Code.relHammingDist_le_one_sub_div_iff hpos).mp (by rwa [← hradius])
  exact_mod_cast hagree

/-- Actual maximized independent IRS16 list term, with no MCA or list hypothesis. -/
theorem squared_lambda_le :
    Code.Lambda (squaredCode : Set (I → A16)) radius6917 ≤ (Astra7.weightedListCap : ℕ∞) := by
  classical
  apply Code.Lambda_le_iff_forall_encard_le.mpr
  intro w
  have hfinite : (Code.closeCodewordsRel (squaredCode : Set (I → A16)) w radius6917).Finite :=
    Set.toFinite _
  have hcard : hfinite.toFinset.card ≤ Astra7.weightedListCap := by
    apply finset_squared_list_card_le w hfinite.toFinset
    intro f hf
    obtain ⟨hcode,hclose⟩ := Code.mem_closeCodewordsRel_iff.mp (hfinite.mem_toFinset.mp hf)
    exact ⟨hcode,close_agreement_ge f w hclose⟩
  calc
    (Code.closeCodewordsRel (squaredCode : Set (I → A16)) w radius6917).encard =
        (hfinite.toFinset.card : ℕ∞) := hfinite.encard_eq_coe_toFinset_card
    _ ≤ (Astra7.weightedListCap : ℕ∞) := by exact_mod_cast hcard

/-- Expanded actual-code benchmark form. -/
theorem actual_squared_lambda_le :
    Code.Lambda
      ((IRSProfile.code ^⋈ (Fin 2) : ModuleCode I K A16) : Set (I → A16)) (queryRadius : ℝ) ≤ (Astra7.weightedListCap : ℕ∞) := squared_lambda_le

end
end Astra7.NativeBudget
end PackSource_WeightedSquaredList

section PackSource_WeightedProtocol
set_option autoImplicit true
/- Adapted from sol1 C62OneCountProtocol. The universal MCA count is still an explicit unproved premise. -/

/-! Exact6917 benchmark sufficiency from ONE actual native MCA count.
The MCA count is a hypothesis, never an axiom or a proved universal claim. -/
namespace Astra7.NativeBudget
noncomputable section
open Code CoreDefinitions ToyProblem
open ProximityPrize.Benchmark Sol1.OneCount Sol1.C42
set_option maxRecDepth 10000
set_option maxHeartbeats 0

local instance : DecidableEq K := Classical.decEq K

def ActualMCACap6917 (B : ℕ) : Prop :=
  ∀ U : Fin 2 → I → Fin IRSProfile.interleaving → K,
    {gamma | IsMCA (AffineLineGenerator K) IRSProfile.code gamma U radius6917}.ncard ≤ B

def badSlopes6917 (U : Fin 2 → I → Fin IRSProfile.interleaving → K) : Finset K := by
  classical
  exact Finset.univ.filter fun gamma ↦
    IsMCA (AffineLineGenerator K) IRSProfile.code gamma U radius6917

theorem badSlopes_card_eq_ncard (U : Fin 2 → I → Fin IRSProfile.interleaving → K) :
    (badSlopes6917 U).card =
      {gamma | IsMCA (AffineLineGenerator K) IRSProfile.code gamma U radius6917}.ncard := by
  classical
  have hs : {gamma | IsMCA (AffineLineGenerator K) IRSProfile.code gamma U radius6917} =
      (badSlopes6917 U : Set K) := by
    ext gamma
    simp [badSlopes6917]
  rw [hs,Set.ncard_coe_finset]

/-- The actual MCA probability, maximizing over arbitrary native IRS8 word pairs. -/
theorem mca_error_le_of_actualCap (B : ℕ) (hcap : ActualMCACap6917 B) :
    mcaError (AffineLineGenerator K) IRSProfile.code radius6917 ≤
      (B : ENNReal) / (Fintype.card K : ENNReal) := by
  classical
  refine iSup_le fun U ↦ ?_
  rw [SampleableType.prEvent_uniformSample_eq_ofReal]
  change ENNReal.ofReal (((badSlopes6917 U).card : ℝ) / Fintype.card K) ≤ _
  have hc : (badSlopes6917 U).card ≤ B := by
    rw [badSlopes_card_eq_ncard]
    exact hcap U
  calc
    _ ≤ ENNReal.ofReal ((B : ℝ) / Fintype.card K) := by
      apply ENNReal.ofReal_le_ofReal
      exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]

/-- The independent IRS16 list is already bounded, so only the MCA cap remains. -/
theorem gamma_error_le_of_actualCap (B : ℕ) (hcap : ActualMCACap6917 B)
    (hbudget : (B + Astra7.weightedListCap) * 2 ^ 128 ≤ Fintype.card K) :
    ToyProblem.certifiedGammaError IRSProfile.code queryRadius ≤ reductionTarget := by
  have hNat := ENat.toNat_le_of_le_natCast squared_lambda_le
  have hList :
      ((Code.Lambda (squaredCode : Set (I → A16)) radius6917).toNat : ENNReal) /
        (Fintype.card K : ENNReal) ≤ (Astra7.weightedListCap : ENNReal) / Fintype.card K :=
    ENNReal.div_le_div_right (by exact_mod_cast hNat) _
  have hreal : ((B + Astra7.weightedListCap : ℕ) : ℝ) / Fintype.card K ≤ (1 : ℝ) / 2 ^ 128 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    norm_num only [one_mul]
    exact_mod_cast hbudget
  have hENN : ((B + Astra7.weightedListCap : ℕ) : ENNReal) / Fintype.card K ≤
      (1 : ENNReal) / 2 ^ 128 := by
    have h := ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast, ENNReal.ofReal_div_of_pos (by positivity)] at h
    simpa using h
  rw [← ENNReal.coe_le_coe,ToyProblem.coe_certifiedGammaError]
  calc
    _ ≤ (B : ENNReal) / Fintype.card K + (Astra7.weightedListCap : ENNReal) / Fintype.card K :=
      add_le_add (mca_error_le_of_actualCap B hcap) hList
    _ = ((B + Astra7.weightedListCap : ℕ) : ENNReal) / Fintype.card K := by
      rw [← ENNReal.add_div,Nat.cast_add]
    _ ≤ (1 : ENNReal) / 2 ^ 128 := hENN
    _ = (reductionTarget : ENNReal) := by
      norm_num [reductionTarget,ProximityGap.prizeThreshold]

/-- Exact native benchmark type, with one mathematical count and the explicit integer budget. -/
theorem protocolClaim6917_of_actualCap (B : ℕ) (hcap : ActualMCACap6917 B)
    (hbudget : (B + Astra7.weightedListCap) * 2 ^ 128 ≤ (2130706433 : ℕ) ^ 6) :
    ProtocolClaim 6918 81908 262144 where
  admissible := query_admissible
  reduction := by
    change ToyProblem.certifiedGammaError IRSProfile.code queryRadius ≤ reductionTarget
    apply gamma_error_le_of_actualCap B hcap
    rw [Sol1.Reciprocal.Native.field_card]
    exact hbudget
  score := query_score_6917


theorem remaining_budget :
    (Astra7.weightedMCAAllowance + Astra7.weightedListCap) * 2 ^ 128 ≤ (2130706433 : ℕ) ^ 6 := by
  norm_num [Astra7.weightedMCAAllowance,Astra7.weightedListCap]

theorem remaining_allowance_exact :
    Astra7.weightedMCAAllowance + Astra7.weightedListCap = 274980728111395087 := by
  norm_num [Astra7.weightedMCAAllowance,Astra7.weightedListCap]

theorem remaining_budget_maximal :
    (2130706433 : ℕ) ^ 6 < (Astra7.weightedMCAAllowance + Astra7.weightedListCap + 1) * 2 ^ 128 := by
  norm_num [Astra7.weightedMCAAllowance,Astra7.weightedListCap]

/-- The sole unresolved mathematical gate, stated using the actual native IsMCA. -/
def OneCountGoal6917 : Prop := ActualMCACap6917 Astra7.weightedMCAAllowance

/-- All non-MCA mathematics and arithmetic are discharged for this exact fixed allowance. -/
theorem protocolClaim6917_of_oneCountGoal (hcap : OneCountGoal6917) :
    ProtocolClaim 6918 81908 262144 :=
  protocolClaim6917_of_actualCap Astra7.weightedMCAAllowance hcap remaining_budget

end
end Astra7.NativeBudget
end PackSource_WeightedProtocol

section PackSource_ScalarProtocol
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false
namespace FrobeniusLocator.Native
noncomputable section
open Polynomial Finset CoreDefinitions Code
open ProximityPrize.Benchmark
local instance decidableScalarProtocol (P : Prop) : Decidable P := Classical.propDecidable P

/-- An exact scalar interface; it is a hypothesis, not a theorem about all inputs. -/
def ScalarMCACap6917 : Prop :=
  ∀ (u : Fin 2 → I → K) (Γ : Finset K),
    (∀ γ ∈ Γ, IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u radius) →
    Γ.card ≤ Astra7.weightedMCAAllowance

theorem nativeCap_of_scalarCap (hscalar : ScalarMCACap6917) :
    Astra7.NativeBudget.OneCountGoal6917 := by
  intro U
  rw [← Astra7.NativeBudget.badSlopes_card_eq_ncard]
  apply Sol1.C64.restricted_interleaved_card_le IRSProfile.baseCode
    (⊤ : ModuleCode I K K) radius Astra7.weightedMCAAllowance
    (by rw [Sol1.Reciprocal.Native.field_card]; norm_num [Astra7.weightedMCAAllowance])
    (fun u _ Γ hΓ => hscalar u Γ hΓ) U (by simp)
    (Astra7.NativeBudget.badSlopes6917 U)
  intro γ hγ
  have hh : IsMCA (AffineLineGenerator K) IRSProfile.code γ U
      Astra7.NativeBudget.radius6917 := by
    change γ ∈ Finset.univ.filter (fun z => IsMCA (AffineLineGenerator K)
      IRSProfile.code z U Astra7.NativeBudget.radius6917) at hγ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ
    exact hγ
  rw [Sol1.C64.native_code_eq] at hh
  exact hh

/-- This is the entire protocol bridge needed by a future uniform scalar count. -/
theorem protocolClaim6917_of_scalarCap (hscalar : ScalarMCACap6917) :
    ProtocolClaim 6918 81908 262144 :=
  Astra7.NativeBudget.protocolClaim6917_of_oneCountGoal (nativeCap_of_scalarCap hscalar)

end
end FrobeniusLocator.Native
end PackSource_ScalarProtocol
