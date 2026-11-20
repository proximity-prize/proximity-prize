import ProximityPrize.SubmissionLower.Fast073
import ProximityPrize.SubmissionLower.HighPrice6921Core
import ProximityPrize.SubmissionLower.Front6921
import ProximityPrize.SubmissionLower.Hi6921Fast007
import ProximityPrize.SubmissionLower.Hi6921Fast023
import ProximityPrize.SubmissionLower.Hi6921Fast029
import ProximityPrize.SubmissionLower.Hi6921Fast035
import ProximityPrize.SubmissionLower.Hi6921Fast048
import ProximityPrize.SubmissionLower.Hi6921Fast051
import ProximityPrize.SubmissionLower.Hi6921Fast057
import ProximityPrize.SubmissionLower.Hi6921Fast061
import ProximityPrize.SubmissionLower.Hi6921Fast067
import ProximityPrize.SubmissionLower.Hi6921P21Split
import ProximityPrize.SubmissionLower.Hi6921P32RTransport
import ProximityPrize.SubmissionLower.Hi6921P32Split
import ProximityPrize.SubmissionLower.Hi6921P34Cutter
import ProximityPrize.SubmissionLower.Hi6921P3Split
set_option Elab.async false

/- 69.25 specialization of the high-overhead proof in PR 627. -/
section High_K1_14_3_6Split
set_option autoImplicit true
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace H21_3_6

noncomputable section

open K21 H21 H21_3 K1_13_5_3 Polynomial
open HighPrice6921 (FixedWord section_capacity)
open scoped BigOperators

export _root_.K1_14_3_6 (c1)

/-- Reconstruct degree-bounded regular solutions and encode agreement by capped plane cuts. -/
def c2 : Prop :=
  ∀ (f : K1_13.Row 2) (d b j : ℕ), 2 ≤ d → d < 180120 → 0 < j →
    f.totalDegree ≤ b → f.degreeOf 1 ≤ j → Nonempty (AgreementChart f d b j)

private theorem regular_count (hclear : c1) (hchart : c2)
    {w T s d} (h : FixedWord w T s d) (hd₀ : 2 ≤ d) (hd : d < 180120)
    {g : JetPlane} (hg : Irreducible g) {b j : ℕ}
    (ht : total g ≤ b) (hr : g.natDegree ≤ j)
    (hreg : ∀ γ ∈ T, atScalar (s γ) g = 0 ∧ atScalar (s γ) g.derivative ≠ 0) :
    (180120-d) * T.card ≤
      82024 * (total g * topCap d b j + g.natDegree * (totalCap d b - topCap d b j)) +
        (180120-d) := by
  classical
  by_cases hempty : T = ∅
  · simp [hempty]
  obtain ⟨γ, hγ⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hpos : 0 < g.natDegree := by
    by_contra! hn
    exact (hreg γ hγ).2 (by rw [eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hn),
      derivative_C, map_zero])
  obtain ⟨f, hft, hfr, hfne, hprime, hf⟩ := hclear g hg hpos
  obtain ⟨C⟩ := hchart f d b j hd₀ hd (hpos.trans_le hr) (hft.trans ht) (hfr.trans hr)
  let x (γ : K) := marked (K1_13.extend (s γ))
  have hx : Set.InjOn x (T : Set K) := fun _ ha _ hb heq =>
    h.distinct ha hb (Polynomial.map_injective _ K1_13.embed.injective (marked_injective heq))
  have hroot : ∀ γ ∈ T, MvPolynomial.aeval (x γ) (plane f) = 0 := by
    intro γ hγ
    change MvPolynomial.aeval (marked (K1_13.extend (s γ))) (plane f) = 0
    rw [aeval_plane, (hf _ (hreg γ hγ).1 (hreg γ hγ).2).1, map_zero]
  let cut (i : I) := C.cut (node i) (w i)
  have heval : ∀ γ ∈ T, ∀ i, MvPolynomial.aeval (x γ) (cut i) = 0 ↔
      (s γ).eval (node i) = w i :=
    fun γ hγ i => C.agrees _ (h.degree γ hγ) (hf _ (hreg γ hγ).1 (hreg γ hγ).2) _ _
  have hsupp : (plane f).support = f.support :=
    MvPolynomial.support_map_of_injective f toCenter_inj
  have hgcap := mem_capped (plane f)
    (show (plane f).totalDegree ≤ total g from by
      unfold MvPolynomial.totalDegree
      rw [hsupp]
      exact hft)
    (show (plane f).degreeOf 1 ≤ g.natDegree from by
      simpa only [MvPolynomial.degreeOf_eq_sup, hsupp] using hfr)
  apply section_capacity h hd
  intro i hi
  have hproper : cut i ∉ Ideal.span {plane f} := by
    obtain ⟨η, hη, hbad⟩ := hi
    intro hmem
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hmem
    exact hbad ((heval η hη i).mp (by rw [hq, map_mul, hroot η hη, zero_mul]))
  let hits := T.filter fun γ => (s γ).eval (node i) = w i
  have hcard := capped_cut_card
    (by simp [totalCap] : 0 < totalCap d b)
    (lt_min (by simp [totalCap]) (by omega) : 0 < topCap d b j)
    hfne hprime hgcap (mem_capped (cut i) (C.total_bound _ _) (C.top_bound _ _))
    hproper (hits.image x) (by
      intro z hz
      obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hηT, hηi⟩ := Finset.mem_filter.mp hη
      exact ⟨hroot η hηT, (heval η hηT i).mpr hηi⟩)
  rwa [Finset.card_image_of_injOn (hx.mono (Finset.filter_subset _ _)),
    MvPolynomial.cappedDegreeMixedVolume] at hcard

open private total_pos from ProximityPrize.SubmissionLower.Fast073

private theorem factor_count (hc1 : c1) (hc2 : c2) {w T s d} (h : FixedWord w T s d) (hd₀ : 2 ≤ d) (hd : d < 180120)
    {g : JetPlane} (hg : Irreducible g) {b j : ℕ} (hb : 2 ≤ b) (hbp : b < p)
    (ht : total g ≤ b) (hr : g.natDegree ≤ j)
    (hroot : ∀ γ ∈ T, atScalar (s γ) g = 0) :
    let gap := 180120 - d
    let mass := total g * topCap d b j + g.natDegree * (totalCap d b - topCap d b j)
    gap * T.card ≤ 82024 * mass + gap * (total g * (b-1) + 1) := by
  classical
  let good := fun γ => atScalar (s γ) g.derivative ≠ 0
  let R := T.filter good
  let E := T.filter fun γ => ¬ good γ
  have hRsub : R ⊆ T := Finset.filter_subset _ _
  have hEsub : E ⊆ T := Finset.filter_subset _ _
  have hR := regular_count hc1 hc2 (h.mono hRsub) hd₀ hd hg ht hr
    (fun γ hγ => ⟨hroot γ (hRsub hγ), (Finset.mem_filter.mp hγ).2⟩)
  have hE : E.card ≤ total g * (b-1) := by
    have hne := exception_ne_zero hg ((outer_le_total g).trans_lt (ht.trans_lt hbp))
    apply (root_count (h.mono hEsub).distinct hne ?_).trans (exception_degree hb ht)
    intro γ hγ
    exact exception_root (hroot γ (hEsub hγ))
      (Or.inr (not_ne_iff.mp (Finset.mem_filter.mp hγ).2))
  have hpartition : R.card + E.card = T.card :=
    Finset.card_filter_add_card_filter_not (s := T) good
  dsimp only
  rw [← hpartition, Nat.mul_add]
  refine (Nat.add_le_add hR (Nat.mul_le_mul_left (180120 - d) hE)).trans_eq ?_
  ring

/-- The standalone fixed-equation tariff, including singular and ordinary solutions. -/
theorem of_children (h1 : c1) (h2 : c2) : H21_3.c6 := by
  classical
  intro u del M Γ F d b j hd₀ hd _ hb hbp _ hj hD G hG hcaps T hT hroot
  let gap := 180120 - d
  let a := totalCap d b
  let v := topCap d b j
  have hv : v ≤ a := min_le_left _ _
  have hgap : 0 < gap := Nat.sub_pos_of_lt hd
  have hW : FixedWord M.word T F.scalar d :=
    ⟨F.distinct.mono hT, fun γ hγ => hD γ (hT hγ), fun γ hγ =>
      let m := F.mark γ (hT hγ)
      ⟨m.bad.support, m.bad.agreement, m.scalar_hits⟩⟩
  obtain ⟨fs, hF, htotal, htop, hcover⟩ := factor_cover G hG
  obtain ⟨hbG, hjG⟩ := caps_degree hcaps
  have hB := htotal.trans hbG
  have hJ := htop.trans hjG
  let S (g : JetPlane) := T.filter fun γ => atScalar (F.scalar γ) g = 0
  have hcov : T ⊆ fs.biUnion S := by
    intro γ hγ
    obtain ⟨g, hg, h⟩ := hcover _ (hroot γ hγ)
    exact Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_filter.mpr ⟨hγ, h⟩⟩
  have hnumber : fs.card ≤ b := by
    calc
      fs.card = ∑ _ ∈ fs, 1 := by simp
      _ ≤ ∑ g ∈ fs, total g := Finset.sum_le_sum fun g hg => total_pos (hF g hg)
      _ ≤ b := hB
  have hcount (g : JetPlane) (hg : g ∈ fs) :
      gap * (S g).card ≤
        82024 * (total g * v + g.natDegree * (a-v)) + gap * (total g * (b-1) + 1) :=
    factor_count h1 h2 (hW.mono (Finset.filter_subset _ T)) hd₀ hd (hF g hg) hb hbp
      ((Finset.single_le_sum (fun z _ => Nat.zero_le (total z)) hg).trans hB)
      ((Finset.single_le_sum (fun z _ => Nat.zero_le z.natDegree) hg).trans hJ)
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
  let mass := (b-j)*v + j*a
  have hmass : b*v + j*(a-v) = mass := by
    dsimp only [mass]
    zify [hj, hv]
    ring
  have hcount' : gap * T.card ≤ 82024*mass + gap*(b*(b-1) + b) := by
    calc
      _ ≤ gap * ∑ g ∈ fs, (S g).card := Nat.mul_le_mul_left _
        ((Finset.card_le_card hcov).trans Finset.card_biUnion_le)
      _ = ∑ g ∈ fs, gap * (S g).card := Finset.mul_sum _ _ _
      _ ≤ ∑ g ∈ fs, (82024 * (total g * v + g.natDegree * (a-v)) +
          gap * (total g * (b-1) + 1)) := Finset.sum_le_sum hcount
      _ ≤ _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
          Finset.sum_const, smul_eq_mul, mul_one]
        rw [← hmass]
        gcongr
  let charge := ((262144-d)*mass + (gap-1)) / gap
  have hceil : (262144-d)*mass ≤ gap * charge := by
    have hmod := Nat.mod_add_div ((262144-d)*mass + (gap-1)) gap
    have hlt := Nat.mod_lt ((262144-d)*mass + (gap-1)) hgap
    dsimp only [charge]
    omega
  have hpay := (Nat.mul_le_mul_right mass (show 82024 ≤ 262144-d by omega)).trans hceil
  have hbound : gap * T.card ≤ gap * (charge + b*(b-1) + b) := by
    calc
      _ ≤ _ := hcount'
      _ ≤ gap * charge + gap * (b*(b-1) + b) := Nat.add_le_add_right hpay _
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hbound hgap

end
end H21_3_6
end High_K1_14_3_6Split

section High_K1_14_3_6_2Proof
set_option autoImplicit true
namespace H21_3_6_2

noncomputable section

open K21 K1_13_5 K1_13_5_3 H21_3_6 Polynomial PolynomialDifferential
open K1_13 (Geom Row atJet embed extend jet)

attribute [local instance] MvPolynomial.algebraMvPolynomial

open private eval_at_center from ProximityPrize.SubmissionLower.Fast073

open private specialization_flatten from ProximityPrize.SubmissionLower.Fast073

private theorem agreement {f : Row 2} {S : Geom[X]} {d : ℕ}
    (hd : d < 180120) (hD : S.natDegree ≤ d) (hS : RegularAt 1 f S) (x y : Geom) :
    MvPolynomial.aeval (marked S)
      (taylorAgreementEquation center (chart f) (d + 1) (power d) (constants x) (constants y))
      = 0 ↔ S.eval x = y := by
  have hsol : differentialSpecialization (chart f) (S.map constants) = 0 := by
    rw [chart, ← map_differentialSpecialization, specialization_flatten, hS.1, Polynomial.map_zero]
  have hsf : differentialSpecialization (PolynomialDifferential.separant (flatten f) 1) S ≠ 0 := by
    change differentialSpecialization
      (MvPolynomial.pderiv (some 1) ((MvPolynomial.optionEquivRight Geom (Fin 2)).symm f)) S ≠ 0
    rw [← MvPolynomial.optionEquivRight_symm_pderiv]
    exact (specialization_flatten (MvPolynomial.pderiv 1 f) S).substr hS.2
  have hsep : jetEvaluation (PolynomialDifferential.separant (chart f) (Fin.last 1))
      center (marked S) ≠ 0 := by
    change jetEvaluation (PolynomialDifferential.separant (chart f) 1) center (marked S) ≠ 0
    rw [marked, ← eval_differentialSpecialization, chart, ← map_separant,
      ← map_differentialSpecialization, eval_at_center]
    exact fun he => hsf (toCenter_inj (he.trans (map_zero _).symm))
  have hdeg : (S.map constants).degree < ((d + 1 : ℕ) : WithBot ℕ) := by
    have hb : (S.map constants).natDegree ≤ d := Polynomial.natDegree_map_le.trans hD
    exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hb)
  have hcharG : CharP Geom K21.p := charP_of_injective_ringHom embed.injective K21.p
  have : CharP CenterField K21.p := charP_of_injective_ringHom constants.injective K21.p
  have hpiv : ∀ i : ℕ, 1 < i → i < d + 1 → (i.choose 1 : CenterField) ≠ 0 := by
    intro i hi ht
    rw [Nat.choose_one_right]
    intro hz
    have hp := Nat.le_of_dvd (by omega : 0 < i)
      ((CharP.cast_eq_zero_iff CenterField K21.p i).mp hz)
    change 2130706433 ≤ i at hp
    omega
  rw [taylorAgreementEquation_eq_zero_iff center (chart f) (τ := power d)
      (taylorExponentSufficient_firstOrder_tight d) (marked S)
      (by rwa [aeval_initialJetSeparant]) (constants x) (constants y)]
  rw [marked, rationalTaylorPolynomial_polynomialJet center (chart f) (S.map constants)
    hsol hsep hdeg hpiv, Polynomial.eval_map_apply, constants.injective.eq_iff]

/-- A regular first-order jet reconstructs the message and gives capped agreement cuts. -/
theorem proof : H21_3_6.c2 := by
  intro f d b j _hd₀ hd hj hb htop
  let cut (x y : K) :=
    taylorAgreementEquation center (chart f) (d + 1) (power d)
      (constants (embed x)) (constants (embed y))
  have hτ : TaylorExponentSufficient 1 (d + 1) (power d) :=
    taylorExponentSufficient_firstOrder_tight d
  have htotal (x y : K) : (cut x y).totalDegree ≤ totalCap d b := by
    refine (totalDegree_taylorAgreementEquation_le center (chart f) hτ _ _).trans ?_
    rw [rationalTaylorCutDegreeBound, totalCap]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left (power d)
      (Nat.sub_le_sub_right ((chart_degree f).trans hb) 1)) 1
  refine ⟨⟨cut, htotal, ?_, ?_⟩⟩
  · intro x y
    apply le_min ((MvPolynomial.degreeOf_le_totalDegree _ _).trans (htotal x y))
    simpa only [Nat.add_sub_cancel] using
      degreeOf_taylorAgreementEquation_firstOrder_le center (chart f) j (d + 1) (power d)
        hτ hj ((chart_top f).trans htop) (constants (embed x)) (constants (embed y))
  · intro S hD hS x y
    simpa only [Polynomial.eval_map_apply, embed.injective.eq_iff] using
      agreement hd (Polynomial.natDegree_map_le.trans hD) hS (embed x) (embed y)

end
end H21_3_6_2
end High_K1_14_3_6_2Proof
