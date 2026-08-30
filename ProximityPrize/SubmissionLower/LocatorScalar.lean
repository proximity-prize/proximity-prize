import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocatorScalarArithmetic
import ProximityPrize.SubmissionLower.F0
/- The seedless scalar-list proof at the new, independently certified
   (multiplicity, Y+R cap, R cap) = (45, 61, 13) profile.
   The regular/singular decomposition is unchanged; every numerical threshold
   below is supplied by LocatorScalarArithmetic. -/
namespace ProximityPrize.SubmissionLower.LocatorScalar
open scoped Classical BigOperators
open ProximityPrize.Benchmark
open RCN319 RCN174 RCN231
open RCN081 RCN167 RCN313
open RCN136 RCN135 RCN138
open RCN137 RCN267
open RCN238 RCN243
open RCN222 RCN290
open RCN293
open RCN286
open RCN279
open RCN282 RCN283
open RCN001
open RCN281
open RCN019 RCN018
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
private abbrev n := LocatorScalarArithmetic.n
private abbrev w := LocatorScalarArithmetic.w
private abbrev errors := LocatorScalarArithmetic.errors
private abbrev agreements := LocatorScalarArithmetic.agreements
private abbrev gap := LocatorScalarArithmetic.gap
private abbrev prime := LocatorScalarArithmetic.prime
private abbrev multiplicity := LocatorScalarArithmetic.multiplicity
private abbrev yTotalCap := LocatorScalarArithmetic.yTotalCap
private abbrev slopeCap := LocatorScalarArithmetic.slopeCap
private abbrev weightedCap := LocatorScalarArithmetic.weightedCap
private abbrev listBudget := LocatorScalarArithmetic.listBudget
private abbrev capY := LocatorScalarArithmetic.capY
private abbrev capR := LocatorScalarArithmetic.capR
private abbrev regularListNumerator :=
 LocatorScalarArithmetic.regularListNumerator
private abbrev singularListCap := LocatorScalarArithmetic.singularListCap
private abbrev listNumerator := LocatorScalarArithmetic.listNumerator
private theorem list_numerator_fits : listNumerator < listBudget * gap :=
 LocatorScalarArithmetic.list_numerator_fits
private theorem w_pos : 0 < w := by decide
private theorem prime_pos : 0 < prime := by decide
private theorem w_lt_prime : w < prime := by decide
private theorem w_lt_agreements : w < agreements := by decide
private theorem agreements_le_n : agreements ≤ n := by decide
private theorem yTotalCap_lt_prime : yTotalCap < prime := by decide
private theorem slopeCap_lt_prime : slopeCap < prime := by decide
private theorem slopeCap_pos : 0 < slopeCap := by decide
private theorem weightedCap_pos : 0 < weightedCap := by decide
private theorem gap_pos : 0 < gap := by decide
private theorem base_dimension_exact : IRSProfile.baseDimension = w + 1 := by
 norm_num [IRSProfile.baseDimension, w, LocatorScalarArithmetic.w]
private theorem index_card_exact : Fintype.card IRSProfile.Index = n := by
 norm_num [IRSProfile.Index, n, LocatorScalarArithmetic.n]
section
variable (K : Type) [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq (GenericField K) := Classical.decEq (GenericField K)
private def agreementCap : Fin 3 → ℕ := ![capY, capR, 1]
private theorem seedless_degree_caps
   (Q : MvPolynomial (Fin 4) K)
   (hbox : Q ∈ RCN279.globalCoefficientBox K
     weightedCap w yTotalCap slopeCap) :
   Q.degreeOf 1 ≤ yTotalCap ∧ Q.degreeOf 2 ≤ slopeCap ∧
     Q.degreeOf 3 = 0 := by
 refine ⟨MvPolynomial.degreeOf_le_iff.mpr ?_,
   MvPolynomial.degreeOf_le_iff.mpr ?_, ?_⟩
 · intro d hd
   exact (Nat.le_add_right (d 1) (d 2)).trans (hbox hd).1
 · intro d hd
   exact (hbox hd).2.1
 · apply Nat.eq_zero_of_le_zero
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   exact (hbox hd).2.2.1.le
private theorem agreement_cap
   (phi : Polynomial K →+* GenericField K)
   (F : MvPolynomial (Fin 4) K)
   (hY : F.degreeOf 1 ≤ yTotalCap)
   (hR : F.degreeOf 2 ≤ slopeCap)
   (hZ : F.degreeOf 3 = 0) (x u : K) :
   ∀ j, (agreementPolynomial phi F w x u 0).degreeOf j ≤ agreementCap j := by
 have hb := agreementNumerator_degree_bounds F yTotalCap slopeCap 0
   slopeCap_pos hY hR hZ.le w
     (fun j => (j.factorial : K)⁻¹) x u 0
 intro j
 fin_cases j
 · exact (surfaceMap_degreeOf_le phi _ 0).trans
     (by simpa [agreementCap, capY, LocatorScalarArithmetic.capY]
       using hb.1)
 · exact (surfaceMap_degreeOf_le phi _ 1).trans
     (by simpa [agreementCap, capR, LocatorScalarArithmetic.capR]
       using hb.2.1)
 · exact (surfaceMap_degreeOf_le phi _ 2).trans
     (hb.2.2.trans (by simp [agreementCap]))
private theorem original_regular_seedless_bound
   [CharP K prime]
   (F : MvPolynomial (Fin 4) K) (hF : Irreducible F)
   (hRpos : 0 < F.degreeOf 2)
   (hbox : F ∈ RCN174.globalCoefficientBox K
     weightedCap w yTotalCap slopeCap)
   (hY : F.degreeOf 1 ≤ yTotalCap)
   (hR : F.degreeOf 2 ≤ slopeCap)
   (hZ : F.degreeOf 3 = 0)
   (Gamma : Finset (Polynomial K))
   (hdegree : ∀ S ∈ Gamma, S.natDegree ≤ w)
   (hsolutions : ∀ S ∈ Gamma, specialization K S 0 F = 0)
   (hregular : ∀ S ∈ Gamma,
     specialization K S 0 (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
   {Iota : Type} [Fintype Iota] [DecidableEq Iota]
   (nodes : Finset Iota) (x received : Iota → K)
   (hinj : Set.InjOn x nodes) (hnodes : nodes.card = n)
   (hagreement : ∀ S ∈ Gamma, agreements ≤
     (nodes.filter (fun i => S.eval (x i) = received i)).card) :
   Gamma.card * gap ≤
     (n - w) * (capY * F.degreeOf 2 + capR * F.degreeOf 1) := by
 classical
 letI : CharP (GenericField K) prime := genericField_charP K prime
 have hsmall : F.degreeOf 2 < prime := hR.trans_lt slopeCap_lt_prime
 have hcount (g : RCN281.GeometricFactor K F) :
     (RCN281.geometricPolynomials K F Gamma g).card * gap ≤
       (n - w) * (capY * g.1.degreeOf 1 + capR * g.1.degreeOf 0) := by
   obtain ⟨hgirred, hgdiv⟩ :=
     surfaceFactors_spec (polynomialEmbedding K) F g.1 g.2
   have hgate := geometric_factor_regular_gate K (GenericField K) F hF
     prime hRpos hsmall g.1 hgirred
     (by simpa only [canonical_geometricSurfaceMap] using hgdiv)
   have hproper := RCN281.geometric_seedless_cut_proper
     K g.1 hgate.1
   have hgY := (geometricFactor_degree_le K F hF.ne_zero g 0).trans hY
   have hgR := (geometricFactor_degree_le K F hF.ne_zero g 1).trans hR
   have hgZ : g.1.degreeOf 2 = 0 := Nat.eq_zero_of_le_zero
     ((geometricFactor_degree_le K F hF.ne_zero g 2).trans_eq hZ)
   have hGdegree : ∀ j : Fin 3, g.1.degreeOf j < prime := by
     intro j
     fin_cases j
     · exact hgY.trans_lt yTotalCap_lt_prime
     · exact hgR.trans_lt slopeCap_lt_prime
     · simpa [hgZ] using prime_pos
   have hcutDegree : ∀ j k : Fin 3, j ≠ k →
       (seedlessCut : MvPolynomial (Fin 3) (GenericField K)).degreeOf j *
           g.1.degreeOf k +
         g.1.degreeOf j *
           (seedlessCut : MvPolynomial (Fin 3) (GenericField K)).degreeOf k < prime := by
     intro j k hjk
     have h0 := hGdegree 0
     have h1 := hGdegree 1
     have h2 := hGdegree 2
     fin_cases j <;> fin_cases k <;>
       simp [seedlessCut, MvPolynomial.degreeOf_X_of_ne] at hjk ⊢ <;>
       omega
   have hsub := RCN281.geometricPolynomials_subset K F Gamma g
   have hraw := seedless_proper_cut_bound (polynomialEmbedding K)
     (polynomialEmbedding_injective K) F g.1 hgirred hgdiv hproper
     (RCN281.geometricPolynomials K F Gamma g)
     nodes x received hinj prime w agreements
     w_pos w_lt_prime w_lt_agreements
     (by rw [hnodes]; exact agreements_le_n)
     hGdegree hcutDegree
     (fun S hS => hdegree S (hsub hS))
     (fun S hS => hsolutions S (hsub hS))
     (fun S hS => selectedPoint_regular_of_specialization K F
       (fun _ : K => S) 0 (hregular S (hsub hS)))
     (fun S hS => (Finset.mem_filter.mp hS).2)
     (fun S hS => hagreement S (hsub hS)) agreementCap
     (fun i hi => agreement_cap K (polynomialEmbedding K) F hY hR hZ
       (x i) (received i))
   have hx0 :
       (seedlessCut : MvPolynomial (Fin 3) (GenericField K)).degreeOf 0 = 0 := by
     simp [seedlessCut, MvPolynomial.degreeOf_X_of_ne (by decide : (0 : Fin 3) ≠ 2)]
   have hx1 :
       (seedlessCut : MvPolynomial (Fin 3) (GenericField K)).degreeOf 1 = 0 := by
     simp [seedlessCut, MvPolynomial.degreeOf_X_of_ne (by decide : (1 : Fin 3) ≠ 2)]
   have hx2 :
       (seedlessCut : MvPolynomial (Fin 3) (GenericField K)).degreeOf 2 = 1 := by
     simp [seedlessCut]
   have hm0 : coordinateMixedDegree (GenericField K) g.1 seedlessCut 0 =
       g.1.degreeOf 1 := by
     rw [RCN001.coordinateMixedDegree_zero, hx1, hx2]
     omega
   have hm1 : coordinateMixedDegree (GenericField K) g.1 seedlessCut 1 =
       g.1.degreeOf 0 := by
     rw [RCN001.coordinateMixedDegree_one, hx0, hx2]
     omega
   have hm2 : coordinateMixedDegree (GenericField K) g.1 seedlessCut 2 = 0 := by
     rw [RCN001.coordinateMixedDegree_two, hx0, hx1]
     omega
   have hcost :
       (∑ i : Fin 3, agreementCap i *
         coordinateMixedDegree (GenericField K) g.1 seedlessCut i) =
       capY * g.1.degreeOf 1 + capR * g.1.degreeOf 0 := by
     simp [Fin.sum_univ_succ, agreementCap, hm0, hm1, hm2]
   rw [hnodes, hcost] at hraw
   change (RCN281.geometricPolynomials K F Gamma g).card *
       (agreements - w) ≤
     (n - w) * (capY * g.1.degreeOf 1 + capR * g.1.degreeOf 0)
   exact hraw
 calc
   Gamma.card * gap ≤
       (∑ g : RCN281.GeometricFactor K F,
         (RCN281.geometricPolynomials K F Gamma g).card) * gap :=
     Nat.mul_le_mul_right _
       (RCN281.card_le_sum_geometricPolynomials
         K F hF.ne_zero Gamma hsolutions)
   _ = ∑ g : RCN281.GeometricFactor K F,
       (RCN281.geometricPolynomials K F Gamma g).card * gap := by
     rw [Finset.sum_mul]
   _ ≤ ∑ g : RCN281.GeometricFactor K F,
       (n - w) * (capY * g.1.degreeOf 1 + capR * g.1.degreeOf 0) :=
     Finset.sum_le_sum (fun g _ => hcount g)
   _ = (n - w) *
       (capY * (∑ g : RCN281.GeometricFactor K F,
         g.1.degreeOf 1) +
       capR * (∑ g : RCN281.GeometricFactor K F,
         g.1.degreeOf 0)) := by
     rw [← Finset.mul_sum, Finset.sum_add_distrib,
       ← Finset.mul_sum, ← Finset.mul_sum]
   _ ≤ (n - w) * (capY * F.degreeOf 2 + capR * F.degreeOf 1) := by
     apply Nat.mul_le_mul_left
     exact Nat.add_le_add
       (Nat.mul_le_mul_left capY (geometricFactor_sum_degree_le K F hF.ne_zero 1))
       (Nat.mul_le_mul_left capR (geometricFactor_sum_degree_le K F hF.ne_zero 0))
private theorem singular_seedless_card_le
   [CharP K prime]
   (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
   (hbox : Q ∈ RCN279.globalCoefficientBox K
     weightedCap w yTotalCap slopeCap)
   (Gamma : Finset (Polynomial K))
   (hsolutions : ∀ S ∈ Gamma,
     specialization K S 0 (singularAuxiliary Q) = 0) :
   Gamma.card ≤ singularListCap := by
 classical
 let phi := polynomialEmbedding K
 let J := singularAuxiliary Q
 have hcaps := seedless_degree_caps K Q hbox
 have hJne : J ≠ 0 := singularAuxiliary_nonzero Q hQ prime
   (hcaps.2.1.trans_lt slopeCap_lt_prime)
 have hJR : J.degreeOf 2 = 0 := singularAuxiliary_R_degree Q hQ prime
   (hcaps.2.1.trans_lt slopeCap_lt_prime)
 have hQY : MvPolynomial.weightedTotalDegree
     RCN281.yWeights Q ≤ yTotalCap := by
   apply (weightedTotalDegree_le_iff
     RCN281.yWeights Q yTotalCap).mpr
   intro d hd
   have hh := (hbox hd).1
   rw [weight_fin4]
   simpa [RCN281.yWeights] using
     (Nat.le_add_right (d 1) (d 2)).trans hh
 have hQZ : MvPolynomial.weightedTotalDegree
     RCN281.zWeights Q ≤ 0 := by
   apply (weightedTotalDegree_le_iff
     RCN281.zWeights Q 0).mpr
   intro d hd
   have hh := (hbox hd).2.2.1
   rw [weight_fin4]
   simpa [RCN281.zWeights, hh]
 have hJYw := singularAuxiliary_weight_le
   RCN281.yWeights Q hQ slopeCap
   slopeCap_pos hcaps.2.1
 have hJZw := singularAuxiliary_weight_le
   RCN281.zWeights Q hQ slopeCap
   slopeCap_pos hcaps.2.1
 have hJY : J.degreeOf 1 ≤ singularListCap :=
   (RCN281.degreeY_le_yWeight K J).trans
     (hJYw.trans (by
       simp only [singularListCap, LocatorScalarArithmetic.singularListCap]
       exact Nat.mul_le_mul_left _ hQY))
 have hJZ : J.degreeOf 3 = 0 := Nat.eq_zero_of_le_zero
   ((RCN281.degreeZ_le_zWeight K J).trans
     (hJZw.trans (by
       simpa only [Nat.mul_zero] using
         Nat.mul_le_mul_left (2 * slopeCap - 1) hQZ)))
 let A : MvPolynomial (Fin 3) (GenericField K) := surfaceMap phi J
 have hAne : A ≠ 0 := surfaceMap_ne_zero phi
   (polynomialEmbedding_injective K) J hJne
 have hAR : A.degreeOf 1 = 0 := Nat.eq_zero_of_le_zero
   ((surfaceMap_degreeOf_le phi J 1).trans_eq hJR)
 have hAZ : A.degreeOf 2 = 0 := Nat.eq_zero_of_le_zero
   ((surfaceMap_degreeOf_le phi J 2).trans_eq hJZ)
 let q : Polynomial (GenericField K) :=
   RCN281.yProjection (GenericField K) A
 have hq : q ≠ 0 :=
   RCN281.yProjection_nonzero A hAne hAR hAZ
 have hroots : ∀ z ∈ Gamma.image phi, z ∈ q.roots := by
   intro z hz
   obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hz
   apply (Polynomial.mem_roots hq).mpr
   change q.eval (phi S) = 0
   have hv : seedlessPoint phi S 0 = phi S := by
     simp [seedlessPoint_value]
   change (RCN281.yProjection (GenericField K) A).eval
     (phi S) = 0
   rw [← hv, RCN281.yProjection_eval A hAR hAZ
     (seedlessPoint phi S)]
   rw [seedlessPoint_surface_evaluation, eval_polynomialPoint_eq_specialization,
     hsolutions S hS]
   simp
 have hcard : (Gamma.image phi).card = Gamma.card :=
   Finset.card_image_of_injective _ (polynomialEmbedding_injective K)
 rw [← hcard]
 calc
   (Gamma.image phi).card ≤ q.roots.toFinset.card := by
     apply Finset.card_le_card
     intro z hz
     exact Multiset.mem_toFinset.mpr (hroots z hz)
   _ ≤ q.roots.card := Multiset.toFinset_card_le _
   _ ≤ q.natDegree := Polynomial.card_roots' q
   _ ≤ A.degreeOf 0 := RCN281.yProjection_natDegree_le A
   _ ≤ J.degreeOf 1 := surfaceMap_degreeOf_le phi J 0
   _ ≤ singularListCap := hJY
theorem seedless_list_card_le
   [CharP K prime]
   (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
   (hbox : Q ∈ RCN279.globalCoefficientBox K
     weightedCap w yTotalCap slopeCap)
   (hlegacy : Q ∈ RCN174.globalCoefficientBox K
     weightedCap w yTotalCap slopeCap)
   (Gamma : Finset (Polynomial K))
   {Iota : Type} [Fintype Iota] [DecidableEq Iota]
   (nodes : Finset Iota) (x received : Iota → K)
   (hinj : Set.InjOn x nodes) (hnodes : nodes.card = n)
   (hdegree : ∀ S ∈ Gamma, S.natDegree ≤ w)
   (hsolutions : ∀ S ∈ Gamma, specialization K S 0 Q = 0)
   (hagreement : ∀ S ∈ Gamma, agreements ≤
     (nodes.filter (fun i => S.eval (x i) = received i)).card) :
   Gamma.card ≤ listBudget := by
 classical
 have hcaps := seedless_degree_caps K Q hbox
 have hsing : (singularPolynomials K Q Gamma).card ≤ singularListCap :=
   singular_seedless_card_le K Q hQ hbox (singularPolynomials K Q Gamma)
     (fun S hS => (Finset.mem_filter.mp hS).2)
 have hreg (F : ↥(positiveRFactors Q)) :
     (regularPolynomials K Q Gamma F).card * gap ≤
       (n - w) * (capY * F.1.degreeOf 2 + capR * F.1.degreeOf 1) := by
   have hdata := directFactor_data Q F.1 hQ weightedCap w yTotalCap slopeCap
     hlegacy F.2
   have hdivF := (positiveRFactors_spec Q F.1 F.2).2.1
   have hFZ : F.1.degreeOf 3 = 0 := Nat.eq_zero_of_le_zero
     ((degreeOf_le_of_dvd 3 F.1 Q hdivF hQ).trans_eq hcaps.2.2)
   have hsub : regularPolynomials K Q Gamma F ⊆ Gamma := Finset.filter_subset _ _
   exact original_regular_seedless_bound K F.1 hdata.1 hdata.2.1 hdata.2.2
     ((degreeOf_le_of_dvd 1 F.1 Q hdivF hQ).trans hcaps.1)
     ((degreeOf_le_of_dvd 2 F.1 Q hdivF hQ).trans hcaps.2.1)
     hFZ (regularPolynomials K Q Gamma F)
     (fun S hS => hdegree S (hsub hS))
     (fun S hS => (Finset.mem_filter.mp hS).2.1)
     (fun S hS => (Finset.mem_filter.mp hS).2.2)
     nodes x received hinj hnodes (fun S hS => hagreement S (hsub hS))
 have hsumY := sum_coordinate_degrees_le_of_prod_dvd
   (positiveRFactors Q) id Q hQ (positiveRFactors_product_dvd Q hQ) 1
 have hsumR := sum_coordinate_degrees_le_of_prod_dvd
   (positiveRFactors Q) id Q hQ (positiveRFactors_product_dvd Q hQ) 2
 have hsumY' : (∑ F : ↥(positiveRFactors Q), F.1.degreeOf 1) ≤ Q.degreeOf 1 := by
   simpa only [Finset.sum_coe_sort, id_eq] using hsumY
 have hsumR' : (∑ F : ↥(positiveRFactors Q), F.1.degreeOf 2) ≤ Q.degreeOf 2 := by
   simpa only [Finset.sum_coe_sort, id_eq] using hsumR
 have hregularScaled :
     (∑ F : ↥(positiveRFactors Q), (regularPolynomials K Q Gamma F).card) * gap ≤
       regularListNumerator := by
   calc
     _ = ∑ F : ↥(positiveRFactors Q),
         (regularPolynomials K Q Gamma F).card * gap := by rw [Finset.sum_mul]
     _ ≤ ∑ F : ↥(positiveRFactors Q),
         (n - w) * (capY * F.1.degreeOf 2 + capR * F.1.degreeOf 1) :=
       Finset.sum_le_sum (fun F _ => hreg F)
     _ = (n - w) * (capY * (∑ F : ↥(positiveRFactors Q), F.1.degreeOf 2) +
         capR * (∑ F : ↥(positiveRFactors Q), F.1.degreeOf 1)) := by
       rw [← Finset.mul_sum, Finset.sum_add_distrib,
         ← Finset.mul_sum, ← Finset.mul_sum]
     _ ≤ (n - w) * (capY * slopeCap + capR * yTotalCap) := by
       apply Nat.mul_le_mul_left
       exact Nat.add_le_add (Nat.mul_le_mul_left capY (hsumR'.trans hcaps.2.1))
         (Nat.mul_le_mul_left capR (hsumY'.trans hcaps.1))
     _ = regularListNumerator := rfl
 have hcover := seedless_solution_cover K Q hQ Gamma hsolutions
 have hscaled := Nat.mul_le_mul_right gap hcover
 have htotal : Gamma.card * gap ≤ listNumerator := by
   calc
     Gamma.card * gap ≤
         ((singularPolynomials K Q Gamma).card +
           ∑ F : ↥(positiveRFactors Q), (regularPolynomials K Q Gamma F).card) * gap :=
       hscaled
     _ = (singularPolynomials K Q Gamma).card * gap +
         (∑ F : ↥(positiveRFactors Q), (regularPolynomials K Q Gamma F).card) * gap := by
       ring
     _ ≤ singularListCap * gap + regularListNumerator :=
       Nat.add_le_add (Nat.mul_le_mul_right gap hsing) hregularScaled
     _ = listNumerator := by
       simp only [listNumerator, LocatorScalarArithmetic.listNumerator,
         regularListNumerator, singularListCap, gap]
       omega
 by_contra hnot
 have hlarge : listBudget < Gamma.card := Nat.lt_of_not_ge hnot
 have hgap : 0 < gap := gap_pos
 have hmul := Nat.mul_lt_mul_of_pos_right hlarge hgap
 have hcontra : listBudget * gap < listNumerator := hmul.trans_le htotal
 exact (Nat.not_lt_of_ge hcontra.le) list_numerator_fits
end
local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _
local instance : CharP IRSProfile.Field prime := by
 change CharP KoalaBear.Ext6 2130706433
 exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433
theorem exists_seedless_vanishing_interpolant
   (received : IRSProfile.Index → IRSProfile.Field) :
   ∃ Q : MvPolynomial (Fin 4) IRSProfile.Field,
     Q ≠ 0 ∧
     Q ∈ RCN279.globalCoefficientBox IRSProfile.Field
       weightedCap w yTotalCap slopeCap ∧
     Q ∈ RCN174.globalCoefficientBox IRSProfile.Field
       weightedCap w yTotalCap slopeCap ∧
     ∀ (P : Polynomial IRSProfile.Field)
       (support : Finset IRSProfile.Index),
       P.natDegree ≤ w → agreements ≤ support.card →
       (∀ i ∈ support, P.eval (IRSProfile.domain i) = received i) →
       RCN319.specialization IRSProfile.Field P 0 Q = 0 := by
 classical
 obtain ⟨Q, hQ, hbox, hcontact⟩ :=
   LocatorScalarArithmetic.exists_seedless_interpolant received
 change Q ∈ RCN279.globalCoefficientBox IRSProfile.Field
   weightedCap w yTotalCap slopeCap at hbox
 have hlegacy : Q ∈ RCN174.globalCoefficientBox IRSProfile.Field
     weightedCap w yTotalCap slopeCap := by
   intro d hd
   obtain ⟨hYR, hR, hZ, hweight⟩ := hbox hd
   exact ⟨by omega, hR, hweight⟩
 refine ⟨Q, hQ, hbox, hlegacy, ?_⟩
 intro P support hdegree hcard hvalues
 apply RCN319.specialization_eq_zero_of_contact_and_degree
   IRSProfile.Field Q P 0 IRSProfile.domain received (fun _ => 0)
     support multiplicity
 · intro i hi r
   exact hcontact i r
 · intro i hi
   simpa only [mul_zero, add_zero] using hvalues i hi
 · have hdeg := RCN319.specialization_natDegree_lt
     IRSProfile.Field weightedCap w yTotalCap slopeCap Q P 0
     weightedCap_pos
     hlegacy hdegree
   have hbound : weightedCap ≤ multiplicity * support.card := by
     rw [weightedCap]
     exact Nat.mul_le_mul_left multiplicity hcard
   exact hdeg.trans_le hbound
theorem irs_scalar_finite_list_card_le
   (received : IRSProfile.Index → IRSProfile.Field)
   (L : Finset (IRSProfile.Index → IRSProfile.Field))
   (hcode : ∀ c ∈ L, c ∈ IRSProfile.baseCode)
   (hclose : ∀ c ∈ L, agreements ≤
     (Finset.univ.filter (fun i => c i = received i)).card) :
   L.card ≤ listBudget := by
 classical
 let D := ↥L
 let codeword : D → IRSProfile.baseCode := fun c => ⟨c.1, hcode c.1 c.2⟩
 let selected : D → Polynomial IRSProfile.Field := fun c => ReedSolomon.toPolynomial (codeword c)
 let Gamma : Finset (Polynomial IRSProfile.Field) := Finset.univ.image selected
 have hselected : Function.Injective selected := by
   intro c d h
   apply Subtype.ext
   funext i
   have hh := congrArg (fun P : Polynomial IRSProfile.Field =>
     P.eval (IRSProfile.domain i)) h
   simpa only [selected, ReedSolomon.toPolynomial_eval_at_domain] using hh
 have hcard : Gamma.card = L.card := by
   rw [show Gamma = Finset.univ.image selected by rfl,
     Finset.card_image_of_injective _ hselected, Finset.card_univ,
     Fintype.card_coe]
 obtain ⟨Q, hQ, hbox, hlegacy, hvanish⟩ :=
   exists_seedless_vanishing_interpolant received
 have hdegree : ∀ P ∈ Gamma, P.natDegree ≤ w := by
   intro P hP
   obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hP
   have hp := ReedSolomon.toPolynomial_mem_lt_deg (codeword c)
   have hdeg : (selected c).degree < ((w + 1 : ℕ) : WithBot ℕ) := by
     have hh := Polynomial.mem_degreeLT.mp hp
     change (selected c).degree <
       ((IRSProfile.baseDimension : ℕ) : WithBot ℕ) at hh
     rw [base_dimension_exact] at hh
     exact hh
   by_cases hz : selected c = 0
   · simp [hz]
   · rw [← Polynomial.natDegree_lt_iff_degree_lt hz] at hdeg
     omega
 have hsolution : ∀ P ∈ Gamma, specialization IRSProfile.Field P 0 Q = 0 := by
   intro P hP
   obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hP
   let A := Finset.univ.filter (fun i => c.1 i = received i)
   apply hvanish (selected c) A (hdegree (selected c)
     (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩))
     (hclose c.1 c.2)
   intro i hi
   have hcval := ReedSolomon.toPolynomial_eval_at_domain (c := codeword c) (i := i)
   exact hcval.trans (Finset.mem_filter.mp hi).2
 have hagreement : ∀ P ∈ Gamma, agreements ≤
     (Finset.univ.filter (fun i => P.eval (IRSProfile.domain i) = received i)).card := by
   intro P hP
   obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hP
   have heq : Finset.univ.filter
       (fun i => (selected c).eval (IRSProfile.domain i) = received i) =
       Finset.univ.filter (fun i => c.1 i = received i) := by
     apply Finset.filter_congr
     intro i hi
     rw [ReedSolomon.toPolynomial_eval_at_domain]
   rw [heq]
   exact hclose c.1 c.2
 have hbound := seedless_list_card_le IRSProfile.Field Q hQ hbox hlegacy Gamma
   (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain received
   IRSProfile.domain.injective.injOn
   (by simpa using index_card_exact) hdegree hsolution hagreement
 rwa [hcard] at hbound
end
end ProximityPrize.SubmissionLower.LocatorScalar
