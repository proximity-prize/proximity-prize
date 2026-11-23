import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.DQ
import ProximityPrize.SubmissionLower.E2
import ProximityPrize.SubmissionLower.ZPYznze
set_option Elab.async false
set_option autoImplicit true
section
namespace j6
scoped notation "Pk" => (by omega)
scoped notation "Ar" => (by decide)
scoped notation "rz!" => (by ring)
scoped notation "pz!" => (by positivity)
scoped notation "nz!" => (by norm_num)
scoped notation "LS" => Finset.mem_filter.mp
scoped notation "Kh" => algebraMap
scoped notation "abQ" => Ideal.Quotient.mk
scoped notation "Ze" => MvPolynomial.X
scoped notation "aeY" => Finset.mem_filter.mpr
scoped notation "Sv" => MvPolynomial.C
scoped notation "fqw" => mul_le_mul_of_nonneg_left
scoped notation "bSP" => Polynomial.C
scoped notation "anp" => Nat.mul_le_mul_left
scoped notation "Bf" => bJ.bf
scoped notation "aai" => MvPolynomial.eval
scoped notation "alY" => Finset.filter_subset
scoped notation "fre" => IsFractionRing.injective
scoped notation "ano" => Finset.sum_le_sum
scoped notation "fpP" => Ideal.span_singleton_le_iff_mem
scoped notation "dpk" => Ideal.subset_span
scoped notation "abI" => Ideal.span
scoped notation "aba" => map_mul
scoped notation "eqE" => RingHom.comp_apply
scoped notation "fsf" => MvPolynomial.ringHom_ext
scoped notation "atI" => RingHom.ker
scoped notation "aKB" => MvPolynomial.map
scoped notation "bkx" => Finset.mem_image.mp
scoped notation "fsg" => Function.Injective
scoped notation "aKk" => Nat.le_add_right
scoped notation "ae1" => Finset.mem_union_left
scoped notation "bkA" => Finset.mul_sum
scoped notation "ftS" => Ideal.Quotient.eq_zero_iff_mem.mpr
scoped notation "fra" => Ideal.Quotient.eq_zero_iff_mem
scoped notation "eoR" => Nat.mul_le_mul_right
scoped notation "epZ" => Finset.mem_biUnion.mpr
scoped notation "frC" => Polynomial.X
scoped notation "frb" => MvPolynomial.eval₂Hom_X'
scoped notation "frc" => MvPolynomial.affineHilbertPolynomial
scoped notation "fqU" => Ideal.Quotient.eq_zero_iff_mem.mp
scoped notation "frD" => RingHom.congr_fun
scoped notation "c3o" => Ideal.mem_retainedMinimalPrimes.mp
scoped notation "fvW" => MvPolynomial.optionEquivLeft
scoped notation "fsc" => Ideal.mem_minimalPrimesFinset.mpr
scoped notation "bkB" => Finset.mem_union_right
scoped notation "frE" => MvPolynomial.eval₂Hom_C
scoped notation "abT" => map_zero
scoped notation "bMG" => Nat.add_le_add_right
scoped notation "fsd" => Nat.cast_nonneg
scoped notation "cLG" => Nat.add_le_add
scoped notation "aBP" => congrArg
scoped notation "frd" => MvPolynomial.eval₂Hom
scoped notation "fse" => Ideal.mem_minimalPrimesFinset.mp
scoped notation "fvX" => mul_le_mul_of_nonneg_right
scoped notation "ftT" => Ideal.mem_span_singleton_self
scoped notation "frF" => RingHom.mem_ker.mp
scoped notation "aKi" => Irreducible
scoped notation "fv1" => Function.iterate_succ_apply'
scoped notation "bky" => aR.bf
scoped notation "cAb" => Finset.sum_congr
scoped notation "eqF" => Polynomial.natDegree_map_le.trans
scoped notation "cIV" => Finset.card_union_le
scoped notation "aVf" => Nat.lt_succ_of_le
scoped notation "fqX" => Nat.add_le_add_left
scoped notation "fv2" => Polynomial.map_C
scoped notation "dpp" => Localization.AtPrime
scoped notation "fsm" => mul_assoc
scoped notation "frg" => RingHom.mem_ker.mpr
scoped notation "cLK" => Finset.mem_univ
scoped notation "frh" => Finset.card_image_of_injOn
scoped notation "fqY" => Polynomial.coeff_eq_zero_of_natDegree_lt
scoped notation "fri" => Finset.single_le_sum
scoped notation "fv3" => Polynomial.map_mul
scoped notation "cLj" => Nat.mul_comm
scoped notation "frL" => Ideal.mem_map_of_mem
scoped notation "fs5" => IsLocalization.algebraMap_mem_map_algebraMap_iff
scoped notation "dpl" => Nat.zero_le
scoped notation "bkz" => le_max_left
scoped notation "frM" => Ideal.exists_minimalPrimes_le
scoped notation "dpm" => Finset.card_le_card
scoped notation "fs6" => Polynomial.mapRingHom
scoped notation "frN" => IsScalarTower.algebraMap_apply
scoped notation "fqy" => MvPolynomial.affineDegree
scoped notation "ftU" => MvPolynomial.coe_eval₂Hom
scoped notation "fqx" => MvPolynomial.map_C
scoped notation "fsh" => Ideal.map_le_iff_le_comap.mpr
scoped notation "fsi" => Finset.card_biUnion_le
scoped notation "fpV" => MvPolynomial.zeroLocus
scoped notation "fvY" => Polynomial.C_injective
scoped notation "bSQ" => map_pow
scoped notation "fqV" => Nat.le_of_not_gt
scoped notation "bSR" => Fin.castSucc
scoped notation "fqW" => Polynomial.map_injective
scoped notation "fvZ" => Polynomial.map_map
scoped notation "frG" => Finset.sum_add_distrib
scoped notation "fsj" => MvPolynomial.eval_C
scoped notation "ftV" => Finset.range
scoped notation "fs3" => MvPolynomial.map_injective
scoped notation "frH" => Ideal.Quotient.mk_surjective
scoped notation "fsk" => Module.finrank
scoped notation "ftW" => MvPolynomial.cappedDegreeMixedVolume
scoped notation "fsl" => Set.mem_singleton_iff
scoped notation "frI" => Ideal.span_le.mpr
scoped notation "fs4" => Finset.not_nonempty_iff_eq_empty.mp
scoped notation "frJ" => Ideal.comap_isPrime
scoped notation "frK" => Ideal.mem_span_singleton.mp
scoped notation "fv0" => IsLocalization.Away.invSelf
scoped notation "ftX" => Nat.eq_zero_of_le_zero
scoped notation "frf" => mul_comm
scoped notation "enR" => mul_zero
scoped notation "frP" => Polynomial.natDegree_map
scoped notation "fqG" => Nat.sub_le_sub_right
scoped notation "frm" => Polynomial.coeff_map
scoped notation "frQ" => RingHom.ext
scoped notation "fsn" => Nat.le_of_lt_succ
scoped notation "fq0" => MvPolynomial.map_X
scoped notation "anv" => Set.InjOn
scoped notation "fso" => MvPolynomial.weightedTotalDegree
scoped notation "fpW" => one_mul
scoped notation "fte" => Polynomial.ringHom_ext
scoped notation "fv8" => Finset.sum_fiberwise_of_maps_to
scoped notation "frn" => IsScalarTower.algebraMap_eq
scoped notation "fq1" => Nat.le_add_left
scoped notation "frR" => RingHom.mem_ker
scoped notation "fv9" => Nat.lt_succ_iff.mp
scoped notation "frS" => Nat.sub_add_cancel
scoped notation "fwa" => Polynomial.map_add
scoped notation "fsp" => Set.mem_insert_iff
scoped notation "fwb" => IsFractionRing.lift_algebraMap
scoped notation "frT" => Nat.le_div_iff_mul_le
scoped notation "fq2" => MvPolynomial.rename
scoped notation "fuU" => Nat.sub_le_sub_left
scoped notation "fsq" => RingHom.ker_isPrime
scoped notation "fsr" => Set.image_singleton
scoped notation "fwc" => IsCoprime
scoped notation "dpn" => Finsupp.single
scoped notation "fs7" => Ideal.comap_comap
scoped notation "fv4" => Nat.sub_pos_of_lt
scoped notation "frj" => Polynomial.eval_map_apply
scoped notation "dpo" => le_max_right
scoped notation "fqZ" => MvPolynomial.aeval
scoped notation "fs8" => Localization.AtPrime.map_eq_maximalIdeal
scoped notation "ftY" => IsLocalization.Away.lift
scoped notation "fs9" => Finset.mem_range.mp
scoped notation "fta" => Ideal.mem_sup_right
scoped notation "fv5" => IsLocalization.Away.lift_eq
scoped notation "fv6" => IsLocalization.Away.mul_invSelf
scoped notation "ftb" => Ideal.span_singleton_prime
scoped notation "ftc" => Finset.sum_le_sum_of_subset_of_nonneg
scoped notation "aVv" => Finset.univ
scoped notation "frk" => MvPolynomial.eval₂
scoped notation "fv7" => Ideal.map_mono
scoped notation "fuR" => Polynomial.natDegree_map_le.trans_lt
scoped notation "fuS" => MvPolynomial.optionEquivRight
scoped notation "fqz" => Nat.mul_assoc
scoped notation "frl" => Finset.mem_union.mp
scoped notation "fqA" => Finset.univ.biUnion
scoped notation "fuT" => MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one
scoped notation "dpr" => map_add
scoped notation "frO" => Ideal.span_insert
scoped notation "ftd" => Nat.sub_le
scoped notation "fwl" => Ideal.map_le_iff_le_comap.mp
scoped notation "fwm" => MvPolynomial.totalDegree_mul
scoped notation "fr2" => Ideal.map_span
scoped notation "fsw" => Finset.sum_le_sum_of_subset
scoped notation "fwn" => Polynomial.map_dvd
scoped notation "fwo" => Ideal.quotientMapₐ
scoped notation "fwp" => MvPolynomial.natDegree_affineHilbertPolynomial_le_of_injective
scoped notation "fwq" => IsLocalization.isPrime_of_isPrime_disjoint
scoped notation "fwr" => RingHom.injective_iff_ker_eq_bot
scoped notation "fu1" => IsLocalization.Away.algebraMap_pow_isUnit
scoped notation "fu2" => Polynomial.card_le_degree_of_subset_roots
scoped notation "fws" => Finset.mem_sdiff.mp
scoped notation "fu3" => Localization.Away
scoped notation "fsx" => MvPolynomial.eval_X
scoped notation "fqH" => bJ.gZ
scoped notation "fsy" => map_sub
scoped notation "fti" => Fin.sum_univ_eq_sum_range
scoped notation "ftj" => Finset.sum_mul
scoped notation "fpY" => Module.length
scoped notation "fr3" => Polynomial.eval₂RingHom
scoped notation "ftk" => add_zero
scoped notation "fwt" => Nat.cast_sub
scoped notation "fwu" => Ideal.mem_span_singleton
scoped notation "fwv" => Nat.pos_of_ne_zero
scoped notation "fww" => Ideal.comap_mono
scoped notation "fwx" => MvPolynomial.finite_zeroLocus_and_ncard_le_affineDegree
scoped notation "frU" => Nat.mul_add
scoped notation "frV" => bJ.wm
scoped notation "frW" => Finset.mem_image.mpr
scoped notation "fwe" => IsLocalization.Away.algebraMap_isUnit
scoped notation "frX" => MvPolynomial.aeval_X
scoped notation "fuV" => Finset.mem_image_of_mem
scoped notation "fuW" => Ideal.mem_span_singleton.mpr
scoped notation "fuX" => MvPolynomial.degreeOf_le_totalDegree
scoped notation "frY" => Nat.add_comm
scoped notation "fss" => Nat.cast_mul
scoped notation "fsu" => Nat.cast_one
scoped notation "frZ" => Nat.mul_le_mul
scoped notation "fsv" => Finset.mem_attach
scoped notation "fuY" => Nat.succ_le_of_lt
scoped notation "fwf" => RingHom.id
scoped notation "fwg" => Ideal.quotientMap_injective
scoped notation "fwh" => IsFractionRing.lift
scoped notation "fwi" => Nat.lt_succ_iff.mpr
scoped notation "ftf" => Polynomial.map_zero
scoped notation "ftg" => Polynomial.natDegree_map_le
scoped notation "fuZ" => le_antisymm
scoped notation "fr0" => Polynomial.hom_eval₂
scoped notation "fwj" => Finset.card_sdiff_add_card_eq_card
scoped notation "fwk" => Polynomial.map_X
scoped notation "fr1" => Finset.mem_biUnion.mp
scoped notation "fth" => Ideal.mem_sup_left
scoped notation "fwL" => Nat.le_of_ble_eq_true
scoped notation "fwM" => Polynomial.map_sub
scoped notation "fu9" => mul_left_comm
scoped notation "fsA" => zero_mul
scoped notation "fva" => Submodule.exists_forall_notMem_of_forall_ne_top
scoped notation "frp" => Fin.val
scoped notation "fvb" => Finset.sum_attach
scoped notation "fvc" => MvPolynomial.support_map_subset
scoped notation "ftp" => Nat.cast_le.mpr
scoped notation "fvd" => Set.mem_singleton
scoped notation "fve" => map_one
scoped notation "fvf" => mul_nonneg
scoped notation "fwN" => IsLocalization.under_map_of_isPrime_disjoint
scoped notation "fwO" => MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
scoped notation "frq" => Nat.cast_add
scoped notation "fvg" => Nat.cast_sum
scoped notation "ftq" => Module.FaithfullyFlat.of_flat_of_isLocalHom
scoped notation "fsB" => MvPolynomial.eval₂_eq
scoped notation "fvh" => Nat.cast_le
scoped notation "fvi" => Polynomial.eval_map
scoped notation "fsC" => sub_eq_zero
scoped notation "fwP" => Finset.mem_union
scoped notation "fvj" => Nat.zero_lt_succ
scoped notation "fwQ" => RingHom.ker_comp_of_injective
scoped notation "ftr" => Polynomial.ext
scoped notation "fsE" => Fin.castSucc_injective
scoped notation "fwy" => Ideal.notMem_of_isUnit
scoped notation "fwz" => Polynomial.coeff_C_mul
scoped notation "fu4" => Polynomial.evalRingHom
scoped notation "fwA" => Ideal.quotientMap_injective'
scoped notation "fu5" => Int.toNat_le_toNat
scoped notation "fwB" => Set.ncard_le_ncard
scoped notation "fwC" => Function.iterate_zero_apply
scoped notation "fsz" => Nat.le_succ
scoped notation "fwD" => Submodule.mem_map.mpr
scoped notation "ftl" => Submodule.subset_span
scoped notation "ftm" => mul_one
scoped notation "fr4" => Ideal.map_map
scoped notation "ftn" => Nat.add_sub_of_le
scoped notation "fro" => bJ.tB
scoped notation "fwE" => Polynomial.coeff_natDegree
scoped notation "fwF" => Finset.mem_range.mpr
scoped notation "fwG" => Finset.mem_sdiff.mpr
scoped notation "fu6" => Polynomial.X_ne_zero
scoped notation "fwH" => Polynomial.coeff_sub
scoped notation "fu7" => Polynomial.eval₂_C
scoped notation "fwI" => Polynomial.natDegree
scoped notation "fwJ" => Set.ncard_coe_finset
scoped notation "fu8" => Ideal.map_le_iff_le_comap
scoped notation "fto" => Polynomial.coe_mapRingHom
scoped notation "fr5" => Finset.sum_image
scoped notation "fwK" => Nat.cast_pos.mpr
scoped notation "fvl" => Nat.lt_succ_self
scoped notation "fvm" => Function.Surjective
scoped notation "fvn" => Ideal.mul_mem_right
scoped notation "fwS" => IsLocalization.Away
scoped notation "ftw" => Nat.mul_one
scoped notation "fwU" => Nat.mul_pos
scoped notation "fsF" => Finset.disjoint_left.mpr
scoped notation "fwV" => MvPolynomial.C_injective
scoped notation "fsG" => MvPolynomial.hom_eval₂
scoped notation "fvO" => Nat.mul_zero
scoped notation "fwW" => Nat.succ_pos
scoped notation "fwX" => Nat.zero_add
scoped notation "fwY" => Polynomial.natDegree_mul
scoped notation "fsH" => Fin.last
scoped notation "fwZ" => Fin.lastCases
scoped notation "fsI" => LinearMap.ker
scoped notation "ftx" => Nat.exists_eq_add_of_le
scoped notation "fsJ" => Set.Finite.mem_toFinset
scoped notation "ftz" => add_comm
scoped notation "fw0" => Polynomial.eval_C
scoped notation "fw1" => RingHom.comap_ker
scoped notation "fw2" => Submodule.mem_bot
scoped notation "fsK" => Submodule.sum_mem
scoped notation "fq3" => pow_add
scoped notation "fw3" => Nat.add_zero
scoped notation "fr6" => Set.range
scoped notation "fvk" => Finset.sum_empty
scoped notation "fts" => Finset.le_sup
scoped notation "ftt" => Ideal.map_sup
scoped notation "ftu" => Nat.add_assoc
scoped notation "ftv" => Nat.add_mul
scoped notation "fwR" => zero_add
end j6
end
section
namespace GO
noncomputable section

open fP (Ew m9)
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
def asu (q:ℕ) :ℕ :=
 if q≤105 then 51 else
 if q≤119 then 50 - 2*((q - 106)/2) else 35 - 2*((q - 120)/2)
def iO (q:ℕ) :ℕ:=min q (asu q)
def offset (r :ℕ) :ℤ:=(r :ℤ) - 51
def Vm (q:ℕ) (g:ℤ) :ℤ:=93-(q:ℤ) - g
abbrev XN (q:ℕ) (g:ℤ) :=
 {m:Fin 4 →₀ ℕ // Ew (iO q) (-g) 51 13 m}
abbrev ait (q:ℕ) (g:ℤ) :=
 {m:Fin 4 →₀ ℕ // m.degree=iO q ∧
   m.weight m9<(Vm q g).toNat}
instance gOZ (q:ℕ) (g:ℤ) :Finite (XN q g) :=
 ((Finsupp.finite_of_degree_le _).subset fun _ (h:Ew _ _ _ _ _) =>
   Nat.le_of_eq h.1).to_subtype
instance gO1 (q:ℕ) (g:ℤ) :Finite (ait q g) :=
 ((Finsupp.finite_of_degree_le _).subset fun _ (h:_∧_) =>
   Nat.le_of_eq h.1).to_subtype
noncomputable instance gO0 (q:ℕ) (g:ℤ) :Fintype (XN q g) :=
 Fintype.ofFinite _
noncomputable instance gO2 (q:ℕ) (g:ℤ) :Fintype (ait q g) :=
 Fintype.ofFinite _
def Gy (q:ℕ) (g:ℤ) :Matrix (ait q g) (XN q g) (ZMod P1.p) :=
  fun e m=>((e.val 1).choose (m.val 1) :ZMod P1.p) *
    ((e.val 2).choose (m.val 2) :ZMod P1.p)*((e.val 3).choose (m.val 3) :ZMod P1.p)
end
end GO
end
section
namespace Rv
noncomputable section
open P1 Polynomial
def afT {u T R D} (B:KJ u T R D) (l:Fin 2) :K[X] :=
 B.a*(B.β l).map twist
abbrev lK:=BN.lK
abbrev Adjugate :=BN.Adjugate
inductive Bank where
 | st
 | ts
def Bank.first:Bank→ℕ
 | .st=>20
 | .ts=>17
def Bank.second:Bank→ℕ
 | .st=>17
 | .ts=>20
structure adh (aV:Bank) where
 poly :MvPolynomial (Fin 2) BN.qC
 nonzero :poly≠0
 y_degree :poly.degreeOf 1≤5
 s_degree : ∀ e∈poly.support,(poly.coeff e).degreeOf 0≤aV.first+5
 t_degree : ∀ e∈poly.support,(poly.coeff e).degreeOf 1≤aV.second
 total : ∀ e∈poly.support,e 1+(poly.coeff e).totalDegree≤42
def adh.auh {aV} (A:adh aV) (γ:K) :MvPolynomial (Fin 2) K :=
 A.poly.map (MvPolynomial.eval ![γ,γ^p])
def adh.aSV {aV} (A:adh aV) (γ:K) (P:K[X]) :K[X] :=
 MvPolynomial.aeval ![Polynomial.X,P] (A.auh γ)
abbrev an0:ℕ:=(2*(k - 1) - 1)*(42 - 1)+1
def Bank.b5A (aV:Bank) :ℕ:=aV.first+5+p*aV.second
end
end Rv
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace bjY
noncomputable section
open MvPolynomial
open wT (Qb ME MD LV D9)
open aez (al3)
open P1 (K p)
open Rv (Bank adh)
open private b5N aDu b6Y b5L from ProximityPrize.SubmissionLower.A3
def bhY {aV:Bank} (Q:MvPolynomial (Fin 4) K) (hn:Q≠0)
    (hy :Q.weightedTotalDegree Qb≤5)
    (hs :Q.weightedTotalDegree ME≤aV.first+5)
    (ht:Q.weightedTotalDegree MD ≤aV.second)
    (htot:Q.weightedTotalDegree LV≤42) :adh aV:= by
  have Ca (e f :Fin 2 →₀ ℕ) (hf :f∈((al3 Q).coeff e).support) :
      e 1≤5∧f 0≤aV.first+5∧f 1≤aV.second∧e 1+(f 0+f 1)≤42 := by
    have he :aDu e f∈Q.support := by
      rw [MvPolynomial.mem_support_iff,← b5N]
      exact MvPolynomial.mem_support_iff.mp hf
    have ⟨h0,h1,h2,h3⟩:=b6Y e f
    have hy' := (le_weightedTotalDegree Qb he).trans hy
    have hs' := (le_weightedTotalDegree ME he).trans hs
    have ht' := (le_weightedTotalDegree MD he).trans ht
    have htot' := (le_weightedTotalDegree LV he).trans htot
    simp [Qb,ME,MD,LV,
      Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_succ,
      h0,h1,h2,h3,smul_eq_mul] at hy' hs' ht' htot'
    omega
  refine ⟨al3 Q,(map_ne_zero_iff (al3 (F:=K)).toRingHom
    (al3 (F:=K)).injective).mpr hn,?_,?_,?_,?_⟩
  · rw [degreeOf_eq_sup]
    apply Finset.sup_le
    intro e he
    obtain ⟨f,hf⟩:=support_nonempty.mpr (MvPolynomial.mem_support_iff.mp he)
    exact (Ca e f hf).1
  · intro e _
    rw [degreeOf_eq_sup]
    exact Finset.sup_le (fun f hf=>(Ca e f hf).2.1)
  · intro e _
    rw [degreeOf_eq_sup]
    exact Finset.sup_le (fun f hf=>(Ca e f hf).2.2.1)
  · intro e he
    have hcoeff :=MvPolynomial.mem_support_iff.mp he
    obtain ⟨f,hf⟩:=support_nonempty.mpr hcoeff
    have he' := (Ca e f hf).2.2.2
    have hb: ((al3 Q).coeff e).totalDegree≤42 - e 1 := by
      apply Finset.sup_le
      intro g hg
      have hh:=(Ca e g hg).2.2.2
      simp [Finsupp.sum_fintype,Fin.sum_univ_succ]
      omega
    omega
theorem bOZ {aV:Bank} (Q:MvPolynomial (Fin 4) K) (hn)
 (hy :Q.weightedTotalDegree Qb≤5)
 (hs :Q.weightedTotalDegree ME≤aV.first+5)
 (ht) (htot) (γ:K) (P:Polynomial K) :
 (bhY Q hn hy hs ht htot).aSV γ P =
   aeval (D9 P γ (γ^p)) Q:=b5L Q P γ (γ^p)
end
end bjY
end
section
set_option backward.isDefEq.respectTransparency false
namespace bAi
noncomputable section
open P1 MvPolynomial
open Rv (an0)
open agK (af)
open bzp (dy Bd numerator)
open scoped Polynomial
open private bEp b1h from ProximityPrize.SubmissionLower.A0
open private ahp separant bhR D4 ctv cay c7v from ProximityPrize.SubmissionLower.A0
private theorem cpf {g:af} (h:g.totalDegree≤42) : (dy g).totalDegree≤41 := by
 have :=b1h g
 omega
private theorem cSM {g f :af} {d:ℕ}
   (hg:g.totalDegree≤42) (hf :f.totalDegree≤d) (hd:0<d) :
   (Bd g f).totalDegree≤d+41 := by
 have ha :=cpf hg
 have hx :=bEp g
 have hfx :=bEp f
 have hfy :=b1h f
 unfold Bd
 apply (totalDegree_sub _ _).trans
 apply max_le
 · apply (totalDegree_mul _ _).trans
   omega
 · apply (totalDegree_mul _ _).trans
   omega
private theorem af0 {g:af} (hg:g.totalDegree≤42) (n:ℕ) :
    (numerator g n).totalDegree≤(2*n+1)*41+1 := by
  induction n with
  | zero =>
    simpa [numerator,totalDegree_neg] using (bEp g).trans hg
  | succ n ih =>
    have ha :=cpf hg
    have hf :=cSM hg ih (by omega)
    have hfa :=cSM hg ha (by decide)
    rw [numerator]
    apply (totalDegree_sub _ _).trans
    apply max_le
    · apply (totalDegree_mul _ _).trans
      omega
    · apply (totalDegree_mul _ _).trans
      have hc:=totalDegree_mul
        (MvPolynomial.C ((2*n+1 :ℕ) :K[X]) :af) (Bd g (dy g))
      rw [totalDegree_C,zero_add] at hc
      omega
private theorem cpd (g:af) (hg:g.totalDegree≤42) (a :ℕ) :
   (separant g^a).totalDegree≤a*41 :=
 (totalDegree_pow _ _).trans
   (Nat.mul_le_mul_left a ((ctv _).trans (cpf hg)))
private theorem gAM (g:af) (hg:g.totalDegree≤42) (x :K) :
   (bhR g x).totalDegree≤an0:= by
 unfold bhR
 apply (totalDegree_add _ _).trans
 apply max_le
 · apply (totalDegree_mul _ _).trans
   rw [totalDegree_X]
   exact Nat.add_le_add_right (cpd g hg ahp) 1
 · apply totalDegree_finsetSum_le
   intro n hn
   apply (totalDegree_mul _ _).trans
   rw [totalDegree_C,add_zero]
   apply (totalDegree_mul _ _).trans
   have h1 :=cpd g hg (ahp-(2*n+1))
   have h2 :=(ctv (numerator g n)).trans (af0 hg n)
   have h3:=Nat.sub_add_cancel (cay hn)
   change _≤ahp*41+1
   omega
theorem b9O (u:e9) (g:af) (hg:g.totalDegree≤42) (i:I) :
  (D4 u g i).totalDegree≤an0:= by
 unfold D4
 apply (totalDegree_sub _ _).trans
 refine max_le (gAM g hg _) ((totalDegree_mul _ _).trans ?_)
 exact Nat.add_le_add (cpd g hg ahp) (c7v u i)
end
end bAi
end
section
namespace Rv
noncomputable section
open P1
open scoped BigOperators
open private aJH from ProximityPrize.SubmissionLower.B3
private theorem eqa :BN.adQ 4 20 17=6981 := by
 let rows :Fin 4→ℕ := ![3570,2080,1007,324]
 unfold BN.adQ
 calc
   _ = ∑ i:Fin 4,rows i:= by
     refine aJH _ rows ?_
     intro i
     fin_cases i <;> decide
   _=6981 := by decide
private theorem eqf :BN.adQ 4 17 20=6981 := by
 let rows :Fin 4→ℕ := ![3600,2074,992,315]
 unfold BN.adQ
 calc
   _ = ∑ i:Fin 4,rows i:= by
     refine aJH _ rows ?_
     intro i
     fin_cases i <;> decide
   _=6981 := by decide
private theorem exO:BN.adQ 3 19 16=3216:= by
 let rows :Fin 3→ℕ := ![1960,950,306]
 unfold BN.adQ
 calc
   _ = ∑ i:Fin 3,rows i:= by
     refine aJH _ rows ?_
     intro i
     fin_cases i <;> decide
   _=3216:= by decide
private theorem exQ:BN.adQ 3 16 19=3216:= by
 let rows :Fin 3→ℕ := ![1972,944,300]
 unfold BN.adQ
 calc
   _ = ∑ i:Fin 3,rows i:= by
     refine aJH _ rows ?_
     intro i
     fin_cases i <;> decide
   _=3216:= by decide
private theorem cV3 (aV:Bank) :
   BN.adQ 4 aV.first aV.second -
    BN.adQ 3 (aV.first - 1) (aV.second - 1)=3765:= by
 cases aV
 · change BN.adQ 4 20 17 - BN.adQ 3 19 16=3765
   rw [eqa,exO]
 · change BN.adQ 4 17 20 - BN.adQ 3 16 19=3765
   rw [eqf,exQ]
end
end Rv
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace bjY
noncomputable section
open MvPolynomial wT
open aez (awZ GA)


abbrev akW (F:Type*) [Field F] (aV:Rv.Bank) :=
 WH F 2 (aV.first - 1) (aV.second - 1)
variable {F:Type*} [Field F] {N :ℕ} {L:MvPolynomial (Fin 5) F}
variable (aV:Rv.Bank) (C:awZ N L) {h:ℕ}
 (hdeg : ∀ j,L.weightedTotalDegree (vO 131071 j)=GA h j)
private theorem ebO (b:Rv.Bank) :b.first - 1+1=b.first:= by cases b <;> rfl
private theorem gnj (b:Rv.Bank) :b.second - 1+1=b.second:= by cases b <;> rfl
private def aaZ (i:Fin N) :akW F aV →ₗ[F] WH F 3 aV.first aV.second where
  toFun Q:=⟨weightedTruncation oH 4 (C.ic i L*Q.val),by
    simpa only [ebO,gnj] using
      bx6 2 (aV.first - 1) (aV.second - 1) 1 1 (C.ic i L)
        ((aCL _ _ _ _ _ L).1.trans (le_of_eq (hdeg 2)))
        ((aCL _ _ _ _ _ L).2.trans (le_of_eq (hdeg 3))) Q⟩
  map_add' Q R:= by apply Subtype.ext; simp [mul_add]
  map_smul' a Q:= by apply Subtype.ext; simp
private abbrev IY (i:Fin N) :=
 (WH F 3 aV.first aV.second) ⧸ LinearMap.range (aaZ aV C hdeg i)
private theorem aIw (i:Fin N) :
   Module.finrank F (IY aV C hdeg i) =
     J 4 aV.first aV.second-J 3 (aV.first - 1) (aV.second - 1) := by
 have hinj:Function.Injective (aaZ aV C hdeg i) := by
   apply LinearMap.ker_eq_bot.mp
   apply LinearMap.ker_eq_bot'.mpr
   intro Q hQ
   by_contra hn
   have hprod:weightedTruncation oH 4 (C.ic i L*Q.val)=0 :=
     congrArg (fun x :WH F 3 aV.first aV.second=>x.val) hQ
   have horder :=C.order_one i
   change (RK oH (C.ic i L)).natTrailingDegree=1 at horder
   have hL:C.ic i L≠0:= by
     intro hz
     simp [hz] at horder
   exact bnS oH 4 (C.ic i L) Q.val
     horder hL (fun hz=>hn (Subtype.ext hz)) (brn _ _ _ Q)
     ((weightedTruncation_eq_zero_iff _ _ _).mp hprod)
 have hq:=Submodule.finrank_quotient_add_finrank (LinearMap.range (aaZ aV C hdeg i))
 rw [LinearMap.finrank_range_of_inj hinj,aIi,aIi] at hq
 change Module.finrank F (IY aV C hdeg i)+J 3 (aV.first - 1) (aV.second - 1) =
   J 4 aV.first aV.second at hq
 omega
end
end bjY
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace bAi
noncomputable section
open P1 MvPolynomial
open Rv (adh)
open agK (af ae8 ayE)
open scoped Polynomial
open private aXA dcT Wn specialize dfa aHw
 cJI cJH cMS cNH
 b17 cqp cqs from ProximityPrize.SubmissionLower.A0




private theorem fVr {aV:Rv.Bank} (A:adh aV) : (Wn A.poly).totalDegree≤42 := by
  classical
  have hsum:Wn A.poly =
      ∑ e∈A.poly.support,Wn (monomial e (A.poly.coeff e)) := by
    conv_lhs=>rw [A.poly.as_sum]
    rw [map_sum]
  rw [hsum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [Wn,eval₂Hom_monomial,Finsupp.prod_pow,Fin.prod_univ_two]
  change (aXA (A.poly.coeff e) *
    ((C (Polynomial.X:K[X]) :af)^e 0*(MvPolynomial.X (0:Fin 3) :af)^e 1)).totalDegree≤42
  have hx : ((C (Polynomial.X:K[X]) :af)^e 0).totalDegree=0:= by
    rw [← map_pow,totalDegree_C]
  calc
    _≤(aXA (A.poly.coeff e)).totalDegree +
        (((C (Polynomial.X:K[X]) :af)^e 0)*(MvPolynomial.X (0:Fin 3) :af)^e 1).totalDegree :=
      totalDegree_mul _ _
    _≤(A.poly.coeff e).totalDegree+e 1 := by
      apply Nat.add_le_add (dcT _)
      exact (totalDegree_mul _ _).trans (by rw [hx,zero_add,totalDegree_X_pow])
    _≤42 := by simpa only [Nat.add_comm] using A.total e he
private theorem bUh {aV:Rv.Bank} (A:adh aV) (Γ:Finset K)
   (P : ∀ γ∈Γ,K[X])
   (hF : ∀ γ (hγ:γ∈Γ),A.auh γ≠0∧A.aSV γ (P γ hγ)=0) :
   ∃ g:af,g.totalDegree≤42 ∧
     ∀ γ (hγ:γ∈Γ),∃ j:Fin 5,ae8 (ayE g j) γ (P γ hγ) := by
 let g:=Wn A.poly
 refine ⟨g,fVr A,?_⟩
 intro γ hγ
 let Q:=P γ hγ
 let specializeLabel:=specialize (Polynomial.C γ) (Polynomial.C (γ^p))
 have hview:specializeLabel g=aHw (A.auh γ) :=
   dfa A.poly γ (γ^p)
 have hne :specializeLabel g≠0:= by
   rw [hview]
   intro hz
   exact (hF γ hγ).1 (cJI (hz.trans (map_zero _).symm))
 have hdegree : (specializeLabel g).natDegree≤5:= by
   rw [hview]
   apply (cJH _).trans
   rw [degreeOf_eq_sup,Finset.sup_le_iff]
   intro e he
   exact (le_degreeOf_of_mem_support 1 (support_map_subset _ _ he)).trans A.y_degree
 have hroot : (specializeLabel g).IsRoot Q:= by
   change (specializeLabel g).eval Q=0
   rw [hview,cMS]
   exact (hF γ hγ).2
 obtain ⟨j,hj,hz,hsep⟩ :=
   cNH p 5 _ hne hdegree (by decide) Q hroot
 refine ⟨⟨j,hj⟩,?_,?_⟩
 · change MvPolynomial.eval ![Q,Polynomial.C γ,Polynomial.C (γ^p)]
     (ayE g ⟨j,hj⟩)=0
   rw [← b17,ayE,cqp]
   exact hz
 · change MvPolynomial.eval ![Q,Polynomial.C γ,Polynomial.C (γ^p)]
     (pderiv 0 (ayE g ⟨j,hj⟩))≠0
   rw [← b17,cqs,ayE,cqp]
   exact hsep
end
end bAi
end
