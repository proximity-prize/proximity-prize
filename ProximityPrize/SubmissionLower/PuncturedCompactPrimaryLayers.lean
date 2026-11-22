import ProximityPrize.SubmissionLower.PuncturedCompactPrimaryBank
import ProximityPrize.SubmissionLower.PrimaryTaperActive

set_option Elab.async false
set_option maxHeartbeats 650000

namespace PuncturedCompactPrimary
noncomputable section
open Polynomial
open P3 (I K node)
open K1_13 (Geom embed extend Row Shape shape InBox OrderAt indexDegree)
open K1_13_3 (symbolAt symbolIndex cofactor_rank)
open scoped BigOperators Polynomial
open private exists_fresh specialization_bounds sum_by_layer from ProximityPrize.SubmissionLower.PortLowBase

structure Messages (A D : ℕ) (w : I → K) (Γ : Finset K) (s : K → K[X])
    (deleted : Finset I) : Prop where
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ D
  hits : ∀ γ ∈ Γ, ∃ H : Finset I, A ≤ H.card ∧ Disjoint H deleted ∧
    ∀ i ∈ H, (s γ).eval (node i) = w i

def ActiveFits (P : Row 4) (bound : ℕ) : Prop :=
  ∀ m ∈ P.support, m 0 + 2 * m 1 + 2 * m 2 + 2 * m 3 ≤ bound

def ProperCut (A D : ℕ) (f : Row 4) (Γ : Finset K) (s : K → K[X]) (l : ℕ) : Prop :=
  ∃ Q : Row 4, (¬ f ∣ Q) ∧ InBox (shape Q) PrimaryTaper.primaryBox ∧
    PrimaryTaper.TrueWeightLE D Q (cutoff A) ∧ ActiveFits Q 5164 ∧
    ∀ γ ∈ Γ, OrderAt Q (extend (s γ)) l

def remaining (b j : ℕ) : ℕ := min 406807694511 (K1_13.remaining b j)

def LayerBudget (A D R : ℕ) {n : ℕ} (a : Fin n → Shape) (l : Fin n → ℕ) : Prop :=
  sourceRank A D R ≤ layerWidth A D * ∑ r ∈ Finset.range (1 + cutoff A / layerWidth A D),
    remaining (∑ i, (r + 1 - l i) * (a i).b) (∑ i, (r + 1 - l i) * (a i).j)

open private translateTop topHasse topHasse_coeff source_support sum_add_top total_add_top
  apply_add_top erase_top_add topHasse_order topHasse_zero exact_hasse_not_dvd from ProximityPrize.SubmissionLower.PortLowBase
private theorem topHasse_bounds (box : Shape) (D T a : ℕ) (P : Row 4)
    (hb : InBox (shape P) box) (hw : PrimaryTaper.TrueWeightLE D P T) :
    InBox (shape (topHasse a P)) box ∧ PrimaryTaper.TrueWeightLE D (topHasse a P) T := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · change (topHasse a P).totalDegree ≤ box.b
    apply Finset.sup_le
    intro m hm
    have hp := (MvPolynomial.le_totalDegree (source_support hm)).trans hb.1
    rw [total_add_top] at hp
    exact (Nat.le_add_right _ _).trans hp
  · change indexDegree (topHasse a P) ≤ box.j
    apply Finset.sup_le
    intro m hm
    have hp := (Finset.le_sup (f := fun u : Fin 4 →₀ ℕ => u.sum (fun i k => i.val * k))
      (source_support hm)).trans hb.2.1
    rw [sum_add_top Fin.val] at hp
    exact (Nat.le_add_right _ _).trans hp
  · change (topHasse a P).degreeOf 3 ≤ box.t
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    have hp := (MvPolynomial.le_degreeOf_of_mem_support 3 (source_support hm)).trans hb.2.2
    rw [apply_add_top] at hp
    exact (Nat.le_add_right _ _).trans hp
  · intro m hm
    have hp := hw _ (source_support hm)
    rw [sum_add_top (fun i => D - i.val)] at hp
    rw [topHasse_coeff]
    have hc := Polynomial.natDegree_mul_le
      (p := (↑((m 3 + a).choose a) : Geom[X])) (q := P.coeff (m + Finsupp.single 3 a))
    rw [Polynomial.natDegree_natCast, zero_add] at hc
    exact (Nat.add_le_add_right hc _).trans ((Nat.add_le_add_left (Nat.le_add_right _ _) _).trans hp)
private theorem topHasse_one_not_dvd (f : Row 4) (hf : Irreducible f)
    (hpos : 0 < f.degreeOf 3) (hsmall : f.degreeOf 3 < K1.p) : ¬ f ∣ topHasse 1 f := by
  classical
  have hdeg : (topHasse 1 f).degreeOf 3 ≤ f.degreeOf 3 - 1 := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    have h := MvPolynomial.le_degreeOf_of_mem_support 3 (source_support hm)
    rw [apply_add_top] at h
    omega
  have hnz : topHasse 1 f ≠ 0 := by
    have hsup : 0 < f.support.sup (fun m => m (3 : Fin 4)) := by
      rwa [← MvPolynomial.degreeOf_eq_sup]
    obtain ⟨u, hu, htop⟩ := (Finset.le_sup_iff hsup).mp (le_refl _)
    rw [← MvPolynomial.degreeOf_eq_sup] at htop
    have hupos : 0 < u 3 := hpos.trans_le htop
    have hult : u 3 < K1.p := (MvPolynomial.le_degreeOf_of_mem_support 3 hu).trans_lt hsmall
    let m := u.erase 3 + Finsupp.single 3 (u 3 - 1)
    have hsum : m + Finsupp.single 3 1 = u := by
      dsimp [m]
      rw [add_assoc, ← Finsupp.single_add, Nat.sub_add_cancel hupos, erase_top_add]
    have hm : m 3 + 1 = u 3 := by
      rw [← apply_add_top, hsum]
    have hc : (↑(u 3) : Geom[X]) ≠ 0 := by
      have : CharP Geom K1.p :=
        charP_of_injective_ringHom (RingHom.injective embed) K1.p
      intro hz
      have hz' : (↑(u 3) : Geom) = 0 := by
        simpa only [map_natCast, map_zero] using congrArg (Polynomial.evalRingHom (0 : Geom)) hz
      exact (not_le_of_gt hult)
        (Nat.le_of_dvd hupos ((CharP.cast_eq_zero_iff Geom K1.p _).mp hz'))
    have hcoeff : (topHasse 1 f).coeff m ≠ 0 := by
      rw [topHasse_coeff, hm, hsum, Nat.choose_one_right]
      exact mul_ne_zero hc (MvPolynomial.mem_support_iff.mp hu)
    intro hz
    exact hcoeff (by rw [hz]; rfl)
  rintro ⟨g, hg⟩
  have hg0 : g ≠ 0 := by
    intro h
    exact hnz (by rw [hg, h, mul_zero])
  have h := MvPolynomial.degreeOf_mul_eq (n := (3 : Fin 4)) hf.ne_zero hg0
  rw [hg, h] at hdeg
  omega
private theorem exists_cut (A D : ℕ) (f P : Row 4) (Γ : Finset K) (s : K → K[X]) (d a : ℕ)
    (hirr : Irreducible f) (hpos : 0 < (shape f).t) (htop : (shape f).t < K1.p)
    (hb : InBox (shape P) PrimaryTaper.primaryBox)
    (hw : PrimaryTaper.TrueWeightLE D P (cutoff A)) (ha : ActiveFits P 5164)
    (hord : ∀ γ ∈ Γ, OrderAt P (extend (s γ)) d)
    (hdiv : f ^ a ∣ P) (hexact : ¬ f ^ (a + 1) ∣ P) :
    ProperCut A D f Γ s (d - a) := by
  obtain ⟨hbox, hweight⟩ := topHasse_bounds PrimaryTaper.primaryBox D (cutoff A) a P hb hw
  have hp : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  have hproper : ¬ f ∣ topHasse a P :=
    exact_hasse_not_dvd translateTop topHasse_zero f P a hp
      (topHasse_one_not_dvd f hirr hpos htop) hdiv hexact
  have hactive : ActiveFits (topHasse a P) 5164 := by
    intro m hm
    have hh := ha _ (source_support hm)
    simp [Finsupp.add_apply] at hh
    omega
  exact ⟨topHasse a P, hproper, hbox, hweight, hactive, fun γ hγ =>
    topHasse_order a d P (extend (s γ)) (hord γ hγ)⟩

private theorem exists_availability {A D : ℕ} (hA : 0 < A) (hD : 3 < D)
    (hgap : D ≤ A + 3) {w : I → K} {Γ : Finset K} {s : K → K[X]}
    {deleted : Finset I} (hm : Messages A D w Γ s deleted)
    {f : Row 4} (hirr : Irreducible f) (hpos : 0 < (shape f).t) (htop : (shape f).t < K1.p) :
    ∃ l : ℕ, (∀ T ≤ cutoff A, ∀ P, BankRow D w deleted T P → f ^ (requiredOrder A D T - l) ∣ P) ∧
      (0 < l → ProperCut A D f Γ s l) := by
  classical
  let admissible (l : ℕ) : Prop :=
    ∀ T ≤ cutoff A, ∀ P, BankRow D w deleted T P → f ^ (requiredOrder A D T - l) ∣ P
  have hex : ∃ l, admissible l := by
    refine ⟨cutoff A / layerWidth A D + 1, fun T _ P _ => ?_⟩
    have hle : requiredOrder A D T ≤ cutoff A / layerWidth A D + 1 :=
      Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le _ _)) _
    rw [Nat.sub_eq_zero_of_le hle, pow_zero]
    exact one_dvd P
  let l := Nat.find hex
  have hl : admissible l := Nat.find_spec hex
  refine ⟨l, hl, fun hlpos => ?_⟩
  have hbad : ¬ admissible (l - 1) := Nat.find_min hex (by omega)
  dsimp only [admissible] at hbad
  push Not at hbad
  obtain ⟨T, hT, P, hP, hnext⟩ := hbad
  have hle : l ≤ requiredOrder A D T := by
    by_contra! hlt
    have heq : requiredOrder A D T - (l - 1) = 0 := by omega
    exact hnext (by rw [heq, pow_zero]; exact one_dvd P)
  have hstep : requiredOrder A D T - (l - 1) = (requiredOrder A D T - l) + 1 := by omega
  have horder : ∀ γ ∈ Γ, OrderAt P (extend (s γ)) (requiredOrder A D T) := by
    intro γ hγ
    obtain ⟨H, hH, apart, hits⟩ := hm.hits γ hγ
    apply order_of_contact hA hD hgap w deleted P hT hP.2.1 hP.2.2.2
    · simpa only [extend, natDegree_map_eq_of_injective (RingHom.injective embed)] using
        hm.degree γ hγ
    · exact hH
    · exact apart
    · intro i hi
      rw [extend, eval_map, eval₂_at_apply, hits i hi]
  have hweight : PrimaryTaper.TrueWeightLE D P (cutoff A) := fun m hm => (hP.2.1 m hm).trans hT
  have hactive : ActiveFits P 5164 :=
    fun m hm => (PrimaryTaperActive.of_jets hP.2.2.1 m hm).trans (by decide)
  have hcut := exists_cut A D f P Γ s (requiredOrder A D T) (requiredOrder A D T - l) hirr hpos htop hP.1
    hweight hactive horder (hl T hT P hP) (by rwa [hstep] at hnext)
  have heq : requiredOrder A D T - (requiredOrder A D T - l) = l := by omega
  rwa [heq] at hcut

/-- The punctured compact bank supplies compatible cuts and a common residual mass bound. -/
theorem proper_layers {A D R : ℕ} (hA : 0 < A) (hD : 3 < D)
    (hgap : D < A + 3) (hBudget : D * 4012 ≤ 3000 * A)
    {w Γ s deleted n} (hdeleted : R ≤ deleted.card) {f : Fin n → Row 4} (hm : Messages A D w Γ s deleted)
    (hirr : ∀ i, Irreducible (f i)) (hpos : ∀ i, 0 < (shape (f i)).t)
    (htop : ∀ i, (shape (f i)).t < K1.p)
    (hdiff : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)) :
    ∃ l : Fin n → ℕ, LayerBudget A D R (fun i => shape (f i)) l ∧
      ∀ i, 0 < l i → ProperCut A D (f i) Γ s (l i) := by
  classical
  choose l hl hcut using fun i => exists_availability hA hD hgap.le hm (hirr i) (hpos i) (htop i)
  obtain ⟨x, hx, hsup⟩ := exists_fresh f
  have hr : ∃ e : Fin (sourceRank A D R) → Row 4, LinearIndependent Geom e ∧
      ∀ i, BankRow D w deleted (cutoff A) (e i) :=
    primary_family A D R hA hD hBudget w deleted hdeleted le_rfl
  obtain ⟨r, hrank, hfamilies⟩ := symbol_layers D w deleted x hx hr
  have hnz : ∀ i, symbolAt x (f i) ≠ 0 := by
    intro i hz
    have hzero := hsup i
    rw [hz, MvPolynomial.support_zero, eq_comm, MvPolynomial.support_eq_empty] at hzero
    exact (hirr i).ne_zero hzero
  let cost (k : ℕ) :=
    remaining (∑ i, (k + 1 - l i) * (shape (f i)).b)
      (∑ i, (k + 1 - l i) * (shape (f i)).j)
  have hcost : ∀ T ≤ cutoff A, r T ≤ cost ((cutoff A - T) / layerWidth A D) := by
    intro T hT
    obtain ⟨e, he, hei⟩ := hfamilies T hT
    let a (i : Fin n) := requiredOrder A D T - l i
    have hdiv (i : Fin (r T)) : (∏ j, f j ^ a j) ∣ e i := by
      apply Fintype.prod_dvd_of_isRelPrime
      · intro j k hjk
        have hj := hirr j
        have hk := hirr k
        exact (hj.isRelPrime_iff_not_dvd.mpr
          (fun h => hdiff j k hjk (hj.associated_of_dvd hk h))).pow
      · intro j
        exact hl j T hT (e i) (he i)
    have hbound := cofactor_rank n (fun i => symbolAt x (f i)) a hnz (r T)
      (fun i => symbolAt x (e i)) hei (fun i => by
        obtain ⟨hb, hj⟩ := specialization_bounds x (e i) (he i).1
        exact ⟨hb, hj, by simpa only [map_prod, map_pow] using map_dvd (symbolAt x) (hdiv i)⟩)
    have hb (i : Fin n) : (symbolAt x (f i)).totalDegree = (shape (f i)).b := by
      change (symbolAt x (f i)).totalDegree = (f i).totalDegree
      unfold MvPolynomial.totalDegree
      rw [hsup]
    have hj (i : Fin n) : symbolIndex (symbolAt x (f i)) = (shape (f i)).j := by
      change symbolIndex (symbolAt x (f i)) = indexDegree (f i)
      unfold symbolIndex indexDegree
      rw [hsup]
    have hs : r T ≤ 406807694511 :=
      PrimaryTaper.symbol_rank x e (fun i => (he i).2.2.1) hei
    dsimp only [cost, remaining]
    apply le_min hs
    simpa only [a, requiredOrder, hb, hj] using hbound
  have hwidth : 0 < layerWidth A D := Nat.sub_pos_of_lt hgap
  refine ⟨l, ?_, hcut⟩
  exact hrank.trans ((Finset.sum_le_sum fun T hT =>
    hcost T (Nat.le_of_lt_succ (Finset.mem_range.mp hT))).trans
      (sum_by_layer (cutoff A) (layerWidth A D) hwidth cost))

#print axioms proper_layers
end
end PuncturedCompactPrimary
