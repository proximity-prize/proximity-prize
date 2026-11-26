import ProximityPrize.SubmissionLower.R6960RescueGeometryBills
import ProximityPrize.SubmissionLower.HighCore82258PrefixGeometry

set_option Elab.async false

-- merged module R6960RescueGeometryRates
section Merged_R6960RescueGeometryRates

-- merged module R6960RescueGeometryTariffs
section Merged_R6960RescueGeometryTariffs

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.RescueGeometry
open Finset Polynomial ProximityPrize.Benchmark
open P1 (K I node p)
open K1_14 (Shape FX Seeds)
open K1_14_2 (ODE fixedAt RootSeedSection SeedField)
open K1_14_2_2 (ODECaps)
open K1_14_2_4 (taylorPower ordinateBound)
open P1_7_3 (persistentNodes hits_persistent section_bounds regular_chart persistent_taylor)
open P1_7_4 (ODEGuard)
open P1_7_4_3 (mix mix_eq cast_mixed short_cut)
open K1_13 (Geom Row extend embed)
open K1_13_5 (RegularAt)
open K1_13_5_3
open K1_14_2_5 (clear_equation factor_cover)
open K1_14_3_6 (power totalCap topCap)
open scoped Classical BigOperators

private abbrev agreement : ℕ := 179818
private abbrev blockLength : ℕ := 262144
abbrev endpointDegree : ℕ := 164650

structure FixedWord (w : I → K) (U : Finset K) (s : K → (Polynomial K)) (d : ℕ) : Prop where
  distinct : Set.InjOn s (U : Set K)
  degree : ∀ γ ∈ U, (s γ).natDegree ≤ d
  hits : ∀ γ ∈ U, ∃ B : Finset I, agreement ≤ B.card ∧ ∀ i ∈ B, (s γ).eval (node i) = w i
theorem persistent_card_le {w U s d} (hw : FixedWord w U s d) (hU : 1 < U.card) :
    (persistentNodes w U s).card ≤ d := by
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hU
  let P := s a - s b
  have hp : P ≠ 0 := sub_ne_zero.mpr fun eq => hab (hw.distinct ha hb eq)
  refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective P hp _ ?_).trans
    ((natDegree_sub_le _ _).trans (max_le (hw.degree a ha) (hw.degree b hb)))
  intro i hi
  change ((s a) - (s b)).eval (node i) = 0
  rw [Polynomial.eval_sub, hits_persistent ha hi, hits_persistent hb hi, sub_self]
theorem section_incidence {w U s d} (hw : FixedWord w U s d) (D : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ U, (s γ).eval (node i) ≠ w i) →
      (U.filter fun γ => (s γ).eval (node i) = w i).card ≤ D) :
    (agreement - (persistentNodes w U s).card) * U.card ≤
      (blockLength - (persistentNodes w U s).card) * D := by
  classical
  let sites := persistentNodes w U s
  let nodes : Finset I := univ \ sites
  let hits (γ : K) := nodes.filter fun i => (s γ).eval (node i) = w i
  let occ (i : I) := U.filter fun γ => (s γ).eval (node i) = w i
  have hhit (γ : K) (hγ : γ ∈ U) : agreement - sites.card ≤ (hits γ).card := by
    obtain ⟨B, hB, hvals⟩ := hw.hits γ hγ
    let good : Finset I := univ.filter fun i => (s γ).eval (node i) = w i
    have hgood : agreement ≤ good.card :=
      hB.trans (card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _, hvals i hi⟩)
    have hZG : sites ⊆ good := fun i hi => mem_filter.mpr ⟨mem_univ _, hits_persistent hγ hi⟩
    have heq : hits γ = good \ sites := by
      ext i
      simp only [hits, nodes, good, mem_filter, mem_sdiff, mem_univ, true_and]
      exact and_comm
    rw [heq, card_sdiff_of_subset hZG]
    exact Nat.sub_le_sub_right hgood _
  have hnodes : nodes.card = blockLength - sites.card := by
    rw [card_sdiff_of_subset (subset_univ sites), card_univ, IRSProfile.card_index]
  calc
    _ = ∑ γ ∈ U, (agreement - sites.card) := by rw [sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ γ ∈ U, (hits γ).card := sum_le_sum hhit
    _ = ∑ i ∈ nodes, (occ i).card := by simp only [hits, occ, card_filter]; rw [sum_comm]
    _ ≤ ∑ _i ∈ nodes, D := by
      apply sum_le_sum
      intro i hi
      apply hsection i
      by_contra! h
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, h⟩)
    _ = _ := by rw [sum_const, smul_eq_mul, hnodes]
private def rho (s : ℕ) : ℚ :=
  ((blockLength - s : ℕ) : ℚ) / ((agreement - s : ℕ) : ℚ)
abbrev density : ℚ := (blockLength : ℚ) / agreement
private theorem weights {s d : ℕ} (hs : s ≤ d) (hd : d < agreement)
    (haux : rho d ≤ density * d) :
    rho s ≤ rho d ∧ rho s * (max 1 (d-s) : ℕ) ≤ density * d := by
  have hAN : agreement ≤ blockLength := by decide
  have hsA := hs.trans_lt hd
  have hdN := hd.le.trans hAN
  have hsN := hs.trans hdN
  have hAs : (0 : ℚ) < (agreement : ℚ) - s := sub_pos.mpr (by exact_mod_cast hsA)
  have hAd : (0 : ℚ) < (agreement : ℚ) - d := sub_pos.mpr (by exact_mod_cast hd)
  have hmain : rho s ≤ rho d := by
    unfold rho
    rw [Nat.cast_sub hsN, Nat.cast_sub hsA.le, Nat.cast_sub hdN, Nat.cast_sub hd.le]
    apply (div_le_div_iff₀ hAs hAd).mpr
    have h := mul_nonneg (sub_nonneg.mpr (show (s : ℚ) ≤ d by exact_mod_cast hs))
      (sub_nonneg.mpr (show (agreement : ℚ) ≤ blockLength by exact_mod_cast hAN))
    nlinarith only [h]
  refine ⟨hmain, ?_⟩
  by_cases heq : s = d
  · subst s
    simpa using haux
  have hpos : 1 ≤ d - s := by omega
  rw [max_eq_right hpos]
  have hden : (0 : ℚ) < (agreement : ℚ) := by exact_mod_cast (by decide : 0 < agreement)
  have hfrac : ((d-s : ℕ) : ℚ) / ((agreement-s : ℕ) : ℚ) ≤ (d : ℚ) / agreement := by
    rw [Nat.cast_sub hs, Nat.cast_sub hsA.le]
    apply (div_le_div_iff₀ hAs hden).mpr
    have h := mul_nonneg (Nat.cast_nonneg s : (0 : ℚ) ≤ s) hAd.le
    nlinarith only [h]
  calc
    _ = ((blockLength-s : ℕ) : ℚ) * (((d-s : ℕ) : ℚ) / ((agreement-s : ℕ) : ℚ)) := by
      unfold rho
      ring
    _ ≤ (blockLength : ℚ) * ((d : ℚ) / agreement) :=
      mul_le_mul (by exact_mod_cast Nat.sub_le blockLength s) hfrac (by positivity) (by positivity)
    _ = density * d := by ring
private theorem rho_at_endpoint {d : ℕ} (hl : 131071 ≤ d) (hh : d ≤ 164650) :
    rho d ≤ density * d := by
  have hdA : d < agreement := hh.trans_lt (by decide)
  have hdN : d ≤ blockLength := hh.trans (by decide)
  have hrho : rho d ≤ 17 := by
    unfold rho
    have hp : (0 : ℚ) < ((agreement - d : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hdA
    apply (div_le_iff₀ hp).mpr
    rw [Nat.cast_sub hdN, Nat.cast_sub hdA.le]
    change (262144 : ℚ) - d ≤ 17 * ((179818 : ℚ) - d)
    have hQ : (d : ℚ) ≤ 164650 := by exact_mod_cast hh
    linarith only [hQ]
  have hDensity : 1 ≤ density := by
    apply (le_div_iff₀ (show (0 : ℚ) < (agreement : ℚ) by positivity)).mpr
    rw [one_mul]
    exact_mod_cast (by decide : agreement ≤ blockLength)
  exact hrho.trans (calc
    (17 : ℚ) ≤ (d : ℚ) := by exact_mod_cast (show 17 ≤ d by omega)
    _ = 1 * (d : ℚ) := (one_mul _).symm
    _ ≤ density * d := mul_le_mul_of_nonneg_right hDensity (Nat.cast_nonneg _))
private theorem taylorPower_cast {g : ℕ} (hg : 0 < g) :
    (taylorPower g : ℚ) = 2 * (g : ℚ) - 1 := by
  unfold taylorPower
  rw [Nat.cast_sub (by omega)]
  push_cast
  rfl
private theorem regular_count {n g H d : ℕ} {U : Finset K} {s : K → Polynomial K} {w}
    (A : K1_14_2_4.RegularChart U s g H n) (hw : FixedWord w U s d)
    (hg : 0 < g) (hl : 131071 ≤ d) (hh : d ≤ 164650) :
    (U.card : ℚ) ≤ (2 * density * d * (taylorPower g : ℚ) + rho d) * H + 1 := by
  have hbound : 0 ≤ (2 * density * d * (taylorPower g : ℚ) + rho d) * (H : ℚ) := by
    unfold rho
    positivity
  by_cases hc : U.card ≤ 1
  · have h : (U.card : ℚ) ≤ 1 := by exact_mod_cast hc
    linarith only [h, hbound]
  let sites := persistentNodes w U s
  let t := max 1 (d-sites.card)
  have hd : d < agreement := hh.trans_lt (by decide)
  have hs : sites.card ≤ d := persistent_card_le hw (by omega)
  have ht : 0 < t := (by decide : 0 < 1).trans_le (le_max_left _ _)
  have htp : t < p := (max_le (by omega : 1 ≤ d) (Nat.sub_le _ _)).trans_lt
    (hh.trans_lt (by decide))
  have hdt : d ≤ sites.card + t := by
    have h := le_max_right 1 (d-sites.card)
    omega
  obtain ⟨C, hreconstruct⟩ := persistent_taylor sites w hdt htp hg A.equation A.equation_degree
  let D := taylorPower t * (g * H) + ordinateBound t g * H
  have hsection := section_bounds (w := w) A ht hw.distinct C fun γ hγ =>
    hreconstruct _ _ (hw.degree γ hγ) (fun _ hi => hits_persistent hγ hi) (A.root γ hγ) (A.simple γ hγ)
  have hinc : ((agreement - sites.card : ℕ) : ℚ) * U.card ≤ ((blockLength - sites.card : ℕ) : ℚ) * D := by
    exact_mod_cast section_incidence hw D hsection
  have hden : (0 : ℚ) < ((agreement - sites.card : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt hd)
  have hcard : (U.card : ℚ) ≤ rho sites.card * (D : ℚ) := by
    rw [rho, div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).mpr
    calc
      _ = ((agreement - sites.card : ℕ) : ℚ) * U.card := mul_comm _ _
      _ ≤ _ := hinc
  obtain ⟨hρ, hρt⟩ := weights hs hd (rho_at_endpoint hl hh)
  have hρb : rho sites.card * (taylorPower t : ℚ) ≤ 2 * density * d := by
    have hb : (taylorPower t : ℚ) ≤ 2 * (t : ℚ) := by
      exact_mod_cast (Nat.sub_le (2*t) 1 : taylorPower t ≤ 2*t)
    have hρ0 : 0 ≤ rho sites.card := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have h := mul_le_mul_of_nonneg_left hb hρ0
    nlinarith only [h, hρt]
  have hsum : g + (g - 1) = taylorPower g := by unfold taylorPower; omega
  have hD : D = (taylorPower t * taylorPower g + 1) * H := by
    rw [← hsum]
    dsimp [D, ordinateBound]
    ring
  refine hcard.trans (le_add_of_le_of_nonneg ?_ zero_le_one)
  calc
    _ = (rho sites.card * (taylorPower t : ℚ) * (taylorPower g : ℚ) + rho sites.card) * H := by
      rw [hD]
      push_cast
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_right hρb (Nat.cast_nonneg _)) hρ) (Nat.cast_nonneg _)

/-- Degree and agreement at the new upper height, for an arbitrary set
of marks from the actual anchored family. -/
theorem fixed_word {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat≤33579) {T : Finset K} (hT : T⊆Γ) :
    FixedWord M.word T F.scalar endpointDegree where
  distinct := F.distinct.mono hT
  degree := by
    intro γ hγ
    rcases (F.mark γ (hT hγ)).scalar_degree with zero | bound
    · simp [zero]
    · change ((F.scalar γ).natDegree : ℤ)≤131071+M.overhead at bound
      change (F.scalar γ).natDegree≤164650
      omega
  hits := by
    intro γ hγ
    let A := F.mark γ (hT hγ)
    exact ⟨A.bad.support,A.bad.agreement,A.scalar_hits⟩

def curveUnit (g : ℕ) : ℚ :=
  (2*(g : ℚ)-1)*(1+2*density*endpointDegree)+rho endpointDegree

def CurveTariff {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ) : Prop :=
  ∀ T⊆Γ,∀ J g H,0<g → g≤80 →
    K1_14_2.SmallRootCurve J g H →
    Module.finrank SeedField (RootSeedSection J)<p →
    (∀ γ∈T,K1_14_2.OnRoot J (M.label γ) (F.scalar γ)) →
    (T.card : ℚ)≤curveUnit g*H+g

theorem curve_tariff {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat≤33579) : CurveTariff F := by
  intro T hT J g H hg hgLimit hcurve _ hmarks
  obtain ⟨U,hU,hexc,n,⟨A⟩⟩ := regular_chart T M.label F.scalar J g H hg
    (hgLimit.trans_lt (by decide)) hcurve (label_injective M).injOn hmarks
  have hregular := regular_count A (fixed_word F hi (hU.trans hT)) hg (by decide) (by decide)
  have hgQ : (1 : ℚ)≤g := by exact_mod_cast hg
  have hexcQ : ((T \ U).card : ℚ)≤(taylorPower g : ℚ)*H := by exact_mod_cast hexc
  calc
    (T.card : ℚ) = ((T \ U).card : ℚ)+(U.card : ℚ) := by
      exact_mod_cast (card_sdiff_add_card_eq_card hU).symm
    _ ≤ (taylorPower g : ℚ)*H + ((2*density*endpointDegree*(taylorPower g : ℚ)+rho endpointDegree)*H+1) :=
      add_le_add hexcQ hregular
    _ ≤ (taylorPower g : ℚ)*H + ((2*density*endpointDegree*(taylorPower g : ℚ)+rho endpointDegree)*H+g) :=
      add_le_add le_rfl (add_le_add le_rfl hgQ)
    _ = curveUnit g*H+g := by rw [taylorPower_cast hg]; unfold curveUnit; ring

theorem section_bound {w : I → K} {T : Finset K} {s : K → (Polynomial K)} {d a v : ℕ}
    (hw : FixedWord w T s d) (f : Row 2) (hf : Irreducible f) (hfpos : 0 < f.degreeOf 1)
    (hreg : ∀ γ ∈ T, RegularAt 1 f (extend (s γ))) (ha : 0 < a) (hv : 0 < v)
    (i : I) (hmiss : ∃ γ ∈ T, (s γ).eval (node i) ≠ w i)
    (cut : MvPolynomial (Fin 2) CenterField)
    (hcut : cut ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1 a v)
    (heval : ∀ γ ∈ T, MvPolynomial.aeval (marked (extend (s γ))) cut = 0 ↔
      (s γ).eval (node i) = w i) :
    (T.filter fun γ => (s γ).eval (node i) = w i).card ≤
      MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) a v := by
  classical
  let x (γ : K) := marked (extend (s γ))
  have hx : Set.InjOn x (T : Set K) := fun _ ha _ hb heq =>
    hw.distinct ha hb (Polynomial.map_injective _ embed.injective (marked_injective heq))
  have hroot (γ : K) (hγ : γ ∈ T) : MvPolynomial.aeval (x γ) (plane f) = 0 := by
    dsimp only [x]
    rw [aeval_plane, (hreg γ hγ).1, map_zero]
  have hproper : cut ∉ Ideal.span {plane f} := by
    obtain ⟨η, hη, hbad⟩ := hmiss
    intro hmem
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hmem
    exact hbad ((heval η hη).mp (by rw [hq, map_mul, hroot η hη, zero_mul]))
  let hits := T.filter fun γ => (s γ).eval (node i) = w i
  have hplane : plane f ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1
      f.totalDegree (f.degreeOf 1) := by
    intro m hm
    have hm' := MvPolynomial.support_map_subset toCenter f hm
    exact ⟨MvPolynomial.le_totalDegree hm', MvPolynomial.monomial_le_degreeOf 1 hm'⟩
  have hc := capped_cut_card ha hv (plane_ne_zero hf.ne_zero) (plane_prime hf hfpos)
    hplane hcut hproper (hits.image x) (by
      intro z hz
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hγT, hγi⟩ := Finset.mem_filter.mp hγ
      exact ⟨hroot γ hγT, (heval γ hγT).mpr hγi⟩)
  rwa [Finset.card_image_of_injOn (hx.mono (Finset.filter_subset _ _))] at hc

theorem fixed_bound {w T s d B J} (hw : FixedWord w T s d) (guard : ODEGuard B J)
    (G : ODE) (hG : ODECaps G B J) (hroot : ∀ γ ∈ T, fixedAt G (s γ) = 0)
    (a v : ℚ) (hv : 0 ≤ v) (hva : v ≤ a)
    (count : ∀ U ⊆ T, ∀ f : Row 2, Irreducible f → 0 < f.degreeOf 1 →
      f.totalDegree ≤ B → f.degreeOf 1 ≤ J →
      (∀ γ ∈ U, RegularAt 1 f (extend (s γ))) →
      (U.card : ℚ) ≤ mix f.totalDegree (f.degreeOf 1) a v + 1) :
    (T.card : ℚ) ≤ mix B J a v + (B^2 : ℕ) := by
  classical
  obtain ⟨q, hq, hb, hj, hsolve⟩ := clear_equation G hG.1 hG.2.1 hG.2.2
  obtain ⟨A, R, hA, hAb, hAj, hR, hRd, hcover⟩ :=
    factor_cover q hq guard.bmin guard.small hb hj
  let ordinary := T.filter fun γ => R.eval (extend (s γ)) = 0
  let reg (g : Row 2) := T.filter fun γ => RegularAt 1 g (extend (s γ))
  have hord : ordinary.card ≤ B * (B - 1) := by
    let v (γ : K) := extend (s γ)
    have hinj : Set.InjOn v (ordinary : Set K) := fun _ ha _ hb he =>
      hw.distinct (Finset.filter_subset _ _ ha) (Finset.filter_subset _ _ hb)
        (Polynomial.map_injective embed embed.injective he)
    have hcard : (ordinary.image v).card ≤ R.natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro z hz
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
      exact (Polynomial.mem_roots hR).mpr (Finset.mem_filter.mp hγ).2
    rw [Finset.card_image_of_injOn hinj] at hcard
    exact hcard.trans hRd
  have htotal : T.card ≤ ordinary.card + ∑ g ∈ A, (reg g).card := by
    have hsub : T ⊆ ordinary ∪ A.biUnion reg := by
      intro γ hγ
      rcases hcover _ (hsolve _ (hroot γ hγ)) with hr | ⟨g, ha, hr⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hr⟩)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨g, ha, Finset.mem_filter.mpr ⟨hγ, hr⟩⟩)
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left Finset.card_biUnion_le _))
  have hnum : A.card ≤ B := by
    calc
      A.card = ∑ _ ∈ A, 1 := by simp
      _ ≤ ∑ g ∈ A, g.totalDegree := Finset.sum_le_sum fun g hg =>
        (hA g hg).2.trans_le (g.degreeOf_le_totalDegree 1)
      _ ≤ B := hAb
  have hlocal (f : Row 2) (hf : f ∈ A) :
      ((reg f).card : ℚ) ≤ mix f.totalDegree (f.degreeOf 1) a v + 1 :=
    count (reg f) (Finset.filter_subset _ _) f (hA f hf).1 (hA f hf).2
      ((Finset.single_le_sum (fun g _ => Nat.zero_le g.totalDegree) hf).trans hAb)
      ((Finset.single_le_sum (fun g _ => Nat.zero_le (g.degreeOf 1)) hf).trans hAj)
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
  have hreg : (∑ g ∈ A, ((reg g).card : ℚ)) ≤ mix B J a v + B := by
    refine (Finset.sum_le_sum hlocal).trans ?_
    simp only [mix_eq (MvPolynomial.degreeOf_le_totalDegree _ _), mix_eq guard.jb,
      Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hbt : (∑ g ∈ A, (g.totalDegree : ℚ)) ≤ B := by exact_mod_cast hAb
    have hjt : (∑ g ∈ A, (g.degreeOf 1 : ℚ)) ≤ J := by exact_mod_cast hAj
    have hnr : (A.card : ℚ) ≤ B := by exact_mod_cast hnum
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hbt hv)
      (mul_le_mul_of_nonneg_right hjt (sub_nonneg.mpr hva))) hnr
  have hbox : B * (B-1) + B = B^2 := by
    calc
      _ = B * ((B-1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by rw [Nat.sub_add_cancel ((by decide : 1 ≤ 2).trans guard.bmin), pow_two]
  have hs : (T.card : ℚ) ≤ ordinary.card + ∑ g ∈ A, ((reg g).card : ℚ) := by exact_mod_cast htotal
  have ho : (ordinary.card : ℚ) ≤ (B * (B-1) : ℕ) := by exact_mod_cast hord
  have hboxQ : (↑(B * (B-1) : ℕ) : ℚ) + B = (B^2 : ℕ) := by exact_mod_cast hbox
  linarith only [hs,ho,hreg,hboxQ]



private theorem word_subset {w T s d} (hw : FixedWord w T s d) {U : Finset K}
    (hU : U ⊆ T) : FixedWord w U s d :=
  ⟨hw.distinct.mono hU, fun γ hγ => hw.degree γ (hU hγ), fun γ hγ => hw.hits γ (hU hγ)⟩
def siteRatio (m : ℕ) : ℚ :=
  ((blockLength - m : ℕ) : ℚ) / ((agreement - m : ℕ) : ℚ)
def persistentTotal (d B : ℕ) : ℚ := siteRatio d + 2 * density * d * (B-1 : ℕ)
def persistentTop (d B J : ℕ) : ℚ :=
  min (persistentTotal d B) (density * d * (2*J-1 : ℕ))
private theorem persistentTotal_nonneg (d B : ℕ) : 0 ≤ persistentTotal d B := by
  unfold persistentTotal siteRatio
  positivity
private theorem caps_weighted {d m B J : ℕ} (hl : 131071 ≤ d) (hh : d ≤ 164650)
    (hm : m ≤ d) (hJ : 0 < J) :
    let t := max 1 (d-m)
    siteRatio m * totalCap t B ≤ persistentTotal d B ∧
      siteRatio m * topCap t B J ≤ persistentTop d B J := by
  let t := max 1 (d-m)
  have hd : d < agreement := hh.trans_lt (by decide)
  obtain ⟨hMu, hLambda⟩ := weights hm hd (rho_at_endpoint hl hh)
  change siteRatio m ≤ siteRatio d at hMu
  change siteRatio m * t ≤ density * d at hLambda
  have hRatio : 0 ≤ siteRatio m := by unfold siteRatio; positivity
  have hp : (power t : ℚ) ≤ 2 * (t : ℚ) := by
    exact_mod_cast (Nat.sub_le (2 * t) 3)
  have hpow : siteRatio m * power t ≤ 2 * (density * d) := by
    have h := mul_le_mul_of_nonneg_left hp hRatio
    linarith only [h,hLambda]
  have htot : siteRatio m * totalCap t B ≤ persistentTotal d B := by
    unfold totalCap persistentTotal
    push_cast
    rw [mul_add, mul_one, ← mul_assoc, show 2 * density * (d : ℚ) = 2 * (density * d) from
      mul_assoc _ _ _]
    exact add_le_add hMu (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _))
  refine ⟨htot, ?_⟩
  unfold persistentTop
  apply le_min
  · exact (mul_le_mul_of_nonneg_left (by exact_mod_cast
      (show topCap t B J ≤ totalCap t B from min_le_left _ _)) hRatio).trans htot
  · have hcap : topCap t B J ≤ t * (2*J-1) := by
      apply (min_le_right _ _).trans
      rw [show 2*J-1 = 2*(J-1)+1 by omega, Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add_right ((Nat.mul_le_mul_right _ (Nat.sub_le (2*t) 3)).trans_eq (by ring)) _
    calc
      _ ≤ siteRatio m * ((t * (2*J-1) : ℕ) : ℚ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hcap) hRatio
      _ = (siteRatio m * t) * (2*J-1 : ℕ) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hLambda (Nat.cast_nonneg _)
private theorem persistent_regular {w T s d B J} (hw : FixedWord w T s d)
    (hl : 131071 ≤ d) (hh : d ≤ 164650) (hJ : 0 < J)
    (f : Row 2) (hf : Irreducible f) (hfpos : 0 < f.degreeOf 1)
    (hb : f.totalDegree ≤ B) (hj : f.degreeOf 1 ≤ J)
    (hreg : ∀ γ ∈ T, RegularAt 1 f (extend (s γ))) :
    (T.card : ℚ) ≤
      mix f.totalDegree (f.degreeOf 1) (persistentTotal d B) (persistentTop d B J) + 1 := by
  have hpos : 0 ≤ mix f.totalDegree (f.degreeOf 1) (persistentTotal d B) (persistentTop d B J) := by
    have ha : 0 ≤ persistentTotal d B := persistentTotal_nonneg d B
    have hv : 0 ≤ persistentTop d B J := le_min ha (by positivity)
    unfold mix
    positivity
  by_cases hsmall : T.card ≤ 1
  · exact (show (T.card : ℚ) ≤ 1 from by exact_mod_cast hsmall).trans (by linarith only [hpos])
  let sites := persistentNodes w T s
  let t := max 1 (d-sites.card)
  have hs : sites.card ≤ d := persistent_card_le hw (by omega)
  have ht : t ≤ d := max_le (by omega) (Nat.sub_le _ _)
  have htpos : 0 < t := (Nat.le_max_left _ _)
  have hsum : d ≤ sites.card + t := by
    have h := Nat.le_max_right 1 (d-sites.card)
    omega
  have hd : d < agreement := hh.trans_lt (by decide)
  have hdp := hd.trans (by decide : agreement < p)
  have ha : 0 < totalCap t B := by simp [totalCap]
  have hv : 0 < topCap t B J := lt_min ha ((Nat.le_add_left _ _).trans' htpos)
  let D := MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) (totalCap t B) (topCap t B J)
  have hcount := section_incidence hw D (fun i hi => by
    obtain ⟨cut, hc, he⟩ := short_cut f hdp ht hJ hb hj sites hsum w i
    exact section_bound hw f hf hfpos hreg ha hv i hi cut hc
      (fun γ hγ => he _ (hw.degree γ hγ) (hreg γ hγ) (fun _ hj => hits_persistent hγ hj)))
  have hgap : (0 : ℚ) < ((agreement-sites.card : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt hd)
  have hratio : (T.card : ℚ) ≤ siteRatio sites.card * D := by
    unfold siteRatio
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hgap).mpr
    rw [mul_comm (T.card : ℚ)]
    exact_mod_cast hcount
  have hvle : topCap t B J ≤ totalCap t B := min_le_left _ _
  dsimp only [D] at hratio
  rw [cast_mixed (f.degreeOf_le_totalDegree 1) hvle] at hratio
  obtain ⟨hcapA, hcapV⟩ := caps_weighted (B := B) hl hh hs hJ
  refine hratio.trans ?_
  unfold mix
  calc
    _ = (↑(f.totalDegree - f.degreeOf 1 : ℕ) : ℚ) * (siteRatio sites.card * topCap t B J) +
        f.degreeOf 1 * (siteRatio sites.card * totalCap t B) := by ring
    _ ≤ (↑(f.totalDegree - f.degreeOf 1 : ℕ) : ℚ) * persistentTop d B J +
        f.degreeOf 1 * persistentTotal d B :=
      add_le_add (mul_le_mul_of_nonneg_left hcapV (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hcapA (Nat.cast_nonneg _))
    _ ≤ _ := le_add_of_nonneg_right (by decide)

/-- The explicit persistent ODE tariff on the actual family. -/
def fixedFee (B J : ℕ) : ℕ :=
  (mix B J (persistentTotal endpointDegree B) (persistentTop endpointDegree B J)).ceil.toNat+B^2

theorem fixed_count {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat≤33579) {B J : ℕ} (guard : ODEGuard B J)
    (G : ODE) (caps : ODECaps G B J) {T : Finset K} (hT : T⊆Γ)
    (roots : ∀ γ∈T,fixedAt G (F.scalar γ)=0) :
    T.card≤fixedFee B J := by
  have hw := fixed_word F hi hT
  let a := persistentTotal endpointDegree B
  let v := persistentTop endpointDegree B J
  have ha : 0≤a := persistentTotal_nonneg _ _
  have hv : 0≤v := le_min ha (by positivity)
  have h := fixed_bound hw guard G caps roots a v hv (min_le_left _ _)
    (fun U hU=>persistent_regular (word_subset hw hU) (by decide) (by decide) guard.jpos)
  let r := mix B J a v
  have hceil : r≤(r.ceil.toNat : ℕ) := by
    have hs : (r.ceil : ℚ)≤(r.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat r.ceil
    exact Rat.le_ceil.trans hs
  change T.card≤r.ceil.toNat+B^2
  have bound : (T.card : ℚ)≤(r.ceil.toNat : ℚ)+(B^2 : ℕ) :=
    h.trans (add_le_add hceil le_rfl)
  exact_mod_cast bound


end Lower6960.RescueGeometry

end
end Merged_R6960RescueGeometryTariffs

-- merged module R6960RescueGeometryRates
section Merged_R6960RescueGeometryRates

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.RescueGeometry
open Finset Polynomial
open K1 (K p)
open K1_14 (Seeds graphEval)
open K1_14_2 (Ambient OnJet SeedField RootSeedSection)
open K1_14_2_2 (CutCover CurveGeometry)
open K1_14_2_3 (SeedSlice seedImage rootImage constantCoefficients DefinedOverConstants seedLength yLength)
open K1_14_2_3 (on_root on_seed moving_graph_count seed_graph_count equal_image_degree union_card_le)
open scoped Classical BigOperators

structure RateOK (a h : ℚ) : Prop where
  degree : ((p+1 : ℕ) : ℚ)/81≤a
  height : 0≤h
  interpolation : ∀ g : ℕ,0<g → g≤80 →
    max 0 (1-a*g/((p+1 : ℕ) : ℚ))*curveUnit g≤h

def curveMarks {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ) (C : CutCover) : Finset K :=
  C.curves.biUnion (fun J=>Γ.filter (OnMark F J))

theorem mem_curveMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {C : CutCover} {J : Ideal Ambient} {γ : K} (mark : γ∈Γ)
    (curve : J∈C.curves) (on : OnMark F J γ) : γ∈curveMarks F C :=
  mem_biUnion.mpr ⟨J,curve,mem_filter.mpr ⟨mark,on⟩⟩

private theorem projected_curve : K1_14_2_3.c2 :=
  K1_14_2_3_2.of_children K1_14_2_3_2_1.proof K1_14_2_3_2_2.proof
private theorem seed_slice {I : Ideal Ambient} (h : CurveGeometry I) : SeedSlice I :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
private theorem mark_graph {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {I : Ideal Ambient} {C : Seeds} (hC : seedImage I = Ideal.span {C}) :
    ∀ z ∈ (Γ.filter (OnMark F I)).image M.label, graphEval z C = 0 := by
  intro z hz
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
  apply on_seed (Finset.mem_filter.mp hγ).2
  rw [hC]
  exact Ideal.mem_span_singleton_self C
private theorem translated_card {u del} (M : Model u del) (T : Finset K) :
    (T.image M.label).card = T.card :=
  Finset.card_image_of_injective _ (fun _ _ hab => sub_left_inj.mp hab)
private theorem direct_count {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {I : Ideal Ambient} {C : Seeds} (hC : C ≠ 0) (hI : seedImage I = Ideal.span {C})
    (hp : C.totalDegree < p) :
    (Γ.filter (OnMark F I)).card ≤ (p+1)*C.totalDegree := by
  have h := seed_graph_count C hC hp ((Γ.filter (OnMark F I)).image M.label) (mark_graph F hI)
  rwa [translated_card] at h
private theorem interpolate (g : ℕ) (a h d H T : ℚ) (hg : 0 < g)
    (hH : 0 ≤ H) (hd : 0 ≤ d) (hu : RateOK a h)
    (direct : T ≤ ((p+1 : ℕ) : ℚ)*d)
    (tariff : g ≤ 80 → T ≤ curveUnit g * H + g) :
    T ≤ a*(d*g) + h*H + g := by
  let q : ℚ := (p+1 : ℕ)
  have hq : 0 < q := Nat.cast_pos.mpr (Nat.succ_pos p)
  have ha : 0 ≤ a := (show 0 ≤ q/81 by positivity).trans hu.degree
  by_cases large : q ≤ a*g
  · calc
      T ≤ q*d := direct
      _ ≤ (a*g)*d := mul_le_mul_of_nonneg_right large hd
      _ = a*(d*g) := by ring
      _ ≤ _ := by
        have hn := mul_nonneg hu.height hH
        have hgq : (0 : ℚ) ≤ g := Nat.cast_nonneg _
        linarith
  · have hgsmall : g ≤ 80 := by
      by_contra! h
      have hgQ : (81 : ℚ) ≤ g := by exact_mod_cast Nat.succ_le_of_lt h
      have he : q/81*81 = q := by ring
      apply large
      rw [← he]
      exact mul_le_mul hu.degree hgQ (by norm_num) ha
    let θ := a*g/q
    have hθ : 0 ≤ θ := div_nonneg (mul_nonneg ha (Nat.cast_nonneg _)) hq.le
    have hc : 0 ≤ 1-θ := sub_nonneg.mpr ((div_le_iff₀ hq).mpr (by simpa using (le_of_lt (lt_of_not_ge large))))
    have hh : (1-θ)*curveUnit g ≤ h := by
      have hf := hu.interpolation g hg hgsmall
      rw [max_eq_right hc] at hf
      exact hf
    calc
      T = θ*T+(1-θ)*T := by ring
      _ ≤ θ*(q*d)+(1-θ)*(curveUnit g*H+g) :=
        add_le_add (mul_le_mul_of_nonneg_left direct hθ)
          (mul_le_mul_of_nonneg_left (tariff hgsmall) hc)
      _ = a*(d*g)+((1-θ)*curveUnit g)*H+(1-θ)*g := by
        dsimp only [θ]
        field_simp [hq.ne']; ring
      _ ≤ _ := by
        have hlast : (1-θ)*(g : ℚ) ≤ g := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (sub_le_self 1 hθ) (Nat.cast_nonneg (α := ℚ) g)
        exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hh hH)) hlast
private theorem rated_component {u del} {M : Model u del} {Γ} (F : Family M Γ)
    (tariff : CurveTariff F) {a h globalCap localCap : ℚ} (hu : RateOK a h)
    (hmin : min globalCap localCap ≤ a) {I : Ideal Ambient} (geom : CurveGeometry I)
    (hglobal : (seedLength I : ℚ) ≤ globalCap) (hlocal : (seedLength I : ℚ) ≤ localCap)
    (hp : seedLength I < p) :
    ((Γ.filter (OnMark F I)).card : ℚ) ≤
      a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I := by
  let T := Γ.filter (OnMark F I)
  let D := seedLength I
  let H := yLength I
  have hD : (0 : ℚ) ≤ D := Nat.cast_nonneg _
  have hH : (0 : ℚ) ≤ H := Nat.cast_nonneg _
  have ha : 0 ≤ a := (show (0 : ℚ) ≤ ((p+1 : ℕ) : ℚ)/81 by positivity).trans hu.degree
  obtain ⟨f, hf, he, hpos, hd⟩ := K1_14_2_3_1.proof I (seed_slice geom)
  have hdq : (f.totalDegree : ℚ) ≤ D := by exact_mod_cast hd
  by_cases hconst : DefinedOverConstants (seedImage I)
  · obtain ⟨Q, hQ, heQ⟩ := hconst
    have hdeg : f.totalDegree = Q.totalDegree := equal_image_degree f hf.ne_zero Q (he.symm.trans heQ)
    obtain ⟨g, hg, hroot, hgD⟩ := projected_curve I Q (seed_slice geom) geom.2.2.2.2 hQ heQ
    have hgcap : g ≤ D := (Nat.le_mul_of_pos_left g (hdeg ▸ hpos)).trans hgD
    have hp' : Module.finrank SeedField (RootSeedSection (rootImage I)) < p := by
      obtain ⟨_, Q', hQ', hQ'proj, _, hlen, _, _⟩ := hroot
      have heQ' : seedImage I = Ideal.span {MvPolynomial.map constantCoefficients Q'} := hQ'proj
      have hdeg' := equal_image_degree f hf.ne_zero Q' (he.symm.trans heQ')
      rw [hlen, ← hdeg', hdeg]
      exact hgD.trans_lt hp
    have hdir : (T.card : ℚ) ≤ ((p+1 : ℕ) : ℚ)*(Q.totalDegree : ℚ) := by
      have hcount := direct_count F hf.ne_zero he (hd.trans_lt hp)
      rw [hdeg] at hcount
      exact_mod_cast hcount
    have htar (hgi : g ≤ 80) : (T.card : ℚ) ≤ curveUnit g * H + g :=
      tariff T (Finset.filter_subset _ _) (rootImage I) g H hg hgi hroot hp'
        (fun _ hz => on_root (Finset.mem_filter.mp hz).2)
    have hfirst := interpolate g a h Q.totalDegree H T.card hg hH
      (Nat.cast_nonneg _) hu hdir htar
    have hgDq : (Q.totalDegree : ℚ)*g ≤ D := by exact_mod_cast hgD
    have hgcapq : (g : ℚ) ≤ D := by exact_mod_cast hgcap
    exact hfirst.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hgDq ha) le_rfl)
      hgcapq)
  · have hmov := moving_graph_count p f hf (he ▸ hconst)
      (T.image M.label) (mark_graph F he)
    rw [translated_card] at hmov
    have hcard : (T.card : ℚ) ≤ (f.totalDegree : ℚ)^2 := by exact_mod_cast hmov
    have hd0 : (0 : ℚ) ≤ f.totalDegree := Nat.cast_nonneg _
    have har : (f.totalDegree : ℚ) ≤ a :=
      (le_min (hdq.trans hglobal) (hdq.trans hlocal)).trans hmin
    calc
      _ ≤ (f.totalDegree : ℚ)^2 := hcard
      _ ≤ a*D := by rw [pow_two]; exact mul_le_mul har hdq hd0 ha
      _ ≤ _ := by
        have hn := mul_nonneg hu.height hH
        linarith
theorem rated_curve_count {u del} {M : Model u del} {Γ}
    (F : Family M Γ) (tariff : CurveTariff F)
    {a h globalCap : ℚ} (hu : RateOK a h) (C : CutCover)
    (hglobal : (C.cost 0 : ℚ) ≤ globalCap)
    (hdegree : min globalCap (C.cost 0 : ℚ) ≤ a) (hp : C.cost 0 < p) :
    ((curveMarks F C).card : ℚ) ≤ a*(C.cost 0 : ℚ)+h*(C.cost 1 : ℚ)+C.cost 0 := by
  have hsum : ∑ I ∈ C.curves, seedLength I = C.cost 0 := rfl
  have hsumH : ∑ I ∈ C.curves, yLength I = C.cost 1 := rfl
  have hcount (I : Ideal Ambient) (hI : I ∈ C.curves) :
      ((Γ.filter (OnMark F I)).card : ℚ) ≤
        a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I := by
    have hn : seedLength I ≤ C.cost 0 := hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) hI
    have hq : (seedLength I : ℚ) ≤ (C.cost 0 : ℚ) := by exact_mod_cast hn
    exact rated_component F tariff hu hdegree (C.geometric I hI) (hq.trans hglobal) hq (hn.trans_lt hp)
  calc
    _ ≤ ∑ I ∈ C.curves, ((Γ.filter (OnMark F I)).card : ℚ) := union_card_le _ _
    _ ≤ ∑ I ∈ C.curves, (a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I) :=
      Finset.sum_le_sum hcount
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Nat.cast_sum, hsum, hsumH]

end Lower6960.RescueGeometry

end
end Merged_R6960RescueGeometryRates

end Merged_R6960RescueGeometryRates

-- merged module R6960RescueGeometryInvoice
section Merged_R6960RescueGeometryInvoice

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueGeometry
open Finset
open K1 (p)
open P1_7_4 (Mass dotQ weightedBill)
open scoped Classical BigOperators

def degreeRates : List (List ℕ) :=
  [
    [185818626, 110433204, 89307106, 80981569, 73536324, 70050751, 70333505, 78862332, 51474031, 80824946, 107178122, 90561210, 111399090, 159856701, 155401324, 198768055, 138542104],
    [179378044, 106432694, 85817332, 77706467, 70695292, 67465905, 67744230, 75883229, 49483667, 77575308, 102814332, 87000554, 107157326, 154005122, 149641067, 191596945, 137489413],
    [181733058, 104811364, 80618367, 70841205, 66177076, 65013899, 65389313, 72436304, 46324207, 72672132, 97959228, 82217852, 103210618, 149781012, 144393038, 187541220, 147843055],
    [136033029, 79972168, 61971094, 58419873, 63658503, 67045494, 68100572, 73833280, 44860002, 62051252, 75841228, 71158176, 98079150, 149905130, 145594273, 194227079, 257834722]
  ]

def heightRates : List (List ℕ) :=
  [
    [2517532, 4393752, 5487930, 6071739, 6714662, 7056278, 7028566, 6245329, 9697201, 6083207, 4533097, 5409943, 4352404, 2963299, 3054648, 2324970, 3455218],
    [2613306, 4565008, 5717640, 6343770, 6993108, 7342509, 7311406, 6499049, 10095772, 6354940, 4730274, 5631363, 4533987, 3083274, 3172750, 2431607, 3483679],
    [2578286, 4634414, 6098334, 6978807, 7486539, 7624528, 7577076, 6822473, 10800400, 6799360, 4982963, 5981212, 4709649, 3169881, 3297026, 2491917, 3209615],
    [3523055, 6150809, 8009131, 8509917, 7795846, 7389491, 7271584, 6685557, 11161993, 7998999, 6502626, 6947741, 4976721, 3167336, 3264549, 2392496, 1733875]
  ]

def degreeRate (rect : Fin 4) (i : ℕ) : ℕ := (degreeRates.getD rect.val []).getD i 0

def heightRate (rect : Fin 4) (i : ℕ) : ℕ := (heightRates.getD rect.val []).getD i 0

private def heightTerms (a : ℕ) : List ℚ :=
  (List.range 80).map (fun i : ℕ =>
    let g := i+1
    max 0 (1-(a : ℚ)*(g : ℚ)/((p+1 : ℕ) : ℚ))*curveUnit g)

def heightBound (a : ℕ) : ℚ := (heightTerms a).foldr max 0

private theorem le_max_fold {q : ℚ} {terms : List ℚ} (mem : q∈terms) :
    q ≤ terms.foldr max 0 := by
  induction terms with
  | nil => simp at mem
  | cons a rest ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp mem with eq | h
    · exact eq.symm ▸ le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem height_spec (a g : ℕ) (pos : 0<g) (small : g≤80) :
    max 0 (1-(a : ℚ)*g/((p+1 : ℕ) : ℚ))*curveUnit g≤heightBound a := by
  apply le_max_fold
  unfold heightTerms
  apply List.mem_map.mpr
  refine ⟨g-1,List.mem_range.mpr (by omega),?_⟩
  dsimp only
  rw [Nat.sub_add_cancel (by omega : 1≤g)]

private theorem checked_rates (rect : Fin 4) (i : Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate rect i.val : ℚ) ∧
    min (seedLimit rect) (dotQ (cutWeight rect 0 i.val) (history rect i.val)) ≤ (degreeRate rect i.val : ℚ) ∧
    heightBound (degreeRate rect i.val) ≤ (heightRate rect i.val : ℚ) := by
  fin_cases rect <;> fin_cases i <;> decide +kernel

theorem rate_spec (rect : Fin 4) {i : ℕ} (hi : i<17) :
    RateOK (degreeRate rect i) (heightRate rect i) ∧
      min (seedLimit rect) (dotQ (cutWeight rect 0 i) (history rect i)) ≤ degreeRate rect i := by
  obtain ⟨base,degree,height⟩ := checked_rates rect ⟨i,hi⟩
  exact ⟨⟨base,Nat.cast_nonneg _,fun g hp hg=>(height_spec _ g hp hg).trans height⟩,degree⟩

def lambda : ℚ := ((262144 : ℚ)/179818)*endpointDegree

def mu : ℚ := ((262144-endpointDegree : ℕ) : ℚ)/(179818-endpointDegree : ℕ)

def rankB (rect : Fin 4) : ℕ := initialCap rect 2+2

def rankJ (rect : Fin 4) : ℕ := initialCap rect 1+1

def tau : ℚ := 49/100

def pivot (rect : Fin 4) : ℚ := min (47843/5) (tau*rankB rect)

def rankWeight (rect : Fin 4) : Mass :=
  ![0,4*lambda*rankB rect*tau+mu-4*lambda*pivot rect,
    4*lambda*rankJ rect*(1-tau)+rankB rect,0]

def rankRound (rect : Fin 4) : ℚ :=
  rankWeight rect 1+2*rankWeight rect 2+2*lambda*pivot rect^2+1

def lossWeight (rect : Fin 4) (i : ℕ) : Mass :=
  fun k=>(degreeRate rect i : ℚ)*cutWeight rect 0 i k+(heightRate rect i : ℚ)*cutWeight rect 1 i k

def lossLimit (rect : Fin 4) : ℚ :=
  weightedBill 18 (beforeCuts (rankWeight rect) (lossWeight rect))
    (beforeCuts (initialMass rect) (history rect))+seedLimit rect+rankRound rect

def rescueFee (rect : Fin 4) : ℕ :=
  (lossLimit rect).ceil.toNat+(pointLimit rect).ceil.toNat+initialSeedLimit rect+initialCap rect 0

theorem rescue_fee_bound (rect : Fin 4) : rescueFee rect ≤ 118460744183568976 := by
  fin_cases rect <;> decide +kernel

theorem strict_rescue_fee (rect : Fin 4) : rescueFee rect < 118687375614631597 :=
  (rescue_fee_bound rect).trans_lt (by decide)

theorem rank_guard (rect : Fin 4) :
    rankB rect < p ∧ 0≤rankWeight rect 1 ∧ 0≤rankWeight rect 2 := by
  fin_cases rect <;> decide +kernel


end Lower6960.RescueGeometry

end
end Merged_R6960RescueGeometryInvoice
