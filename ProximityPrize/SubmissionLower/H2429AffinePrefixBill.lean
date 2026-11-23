import ProximityPrize.SubmissionLower.H2429AffineCurve
import ProximityPrize.SubmissionLower.H2429AffineFixedCount
import ProximityPrize.SubmissionLower.KoalaH2429PrefixNumbers
import ProximityPrize.SubmissionLower.HighCore82258PrefixGeometry

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

namespace H2429AffinePrefixBill
noncomputable section
open Finset Polynomial
open scoped BigOperators Classical
open FrontCore82258 (effectiveHeight)
open HighCore82258 (K p AnchorModel AnchoredFamily InBand Source Pairs fees)
open HighCore82258_3
open HighCore82258PrefixHelpers (curveMarks mem_curveMarks)
open HighCore82258JointRank (rankMarks capB capJ rank_marks_le_with)
open HighCore82268JointRank (splice fixed_fee_linear)
open K1_14 (Banks)
open K1_14_2 (Ambient ODE)
open K1_14_2_2 (mass Active dual fixedOn orderOn ODECaps)
open P1_7_4 (dotQ massQ massQ_mono massQ_split dotQ_mono_mass dotQ_scale_add
  weightedBill running bill_bound massQ_nonneg)
open private properBin terminal_coordinate
  from ProximityPrize.SubmissionLower.HighCore82258PrefixGeometry
open KoalaH2429PrefixNumbers (FeeGrade degree integerHistory localSupport rank rounding
  seedWeight rate0 rate1 discountedWeight discountedHistory fixedBankFees)

private abbrev band : HighCore82258.Band := .h2429

def gradeOf (e : ℕ) : FeeGrade := if e=16 then .sixteen else if e=17 then .seventeen else .base

theorem degree_gradeOf (e : ℕ) : degree (gradeOf e) ≤ e := by
  by_cases h : e=16
  · simp [gradeOf,h,KoalaH2429PrefixNumbers.degree]
  by_cases hj : e=17 <;> simp [gradeOf,h,hj,KoalaH2429PrefixNumbers.degree]

abbrev rho : ℚ := KoalaH2429PrefixNumbers.rho
abbrev lam : ℚ := KoalaH2429PrefixNumbers.lambda

def fixedPrice (B J : ℕ) : ℕ :=
  let a := rho + 2*lam*(B-1 : ℕ)
  let v := min a (lam*(2*J-1 : ℕ))
  (⌈P1_7_4_3.mix B J a v⌉).toNat + B^2

def FixedPrice {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ) : Prop :=
  ∀ B J, ODEGuard B J → ∀ G : ODE, ODECaps G B J → ∀ T ⊆ Γ,
    (∀ γ ∈ T, K1_14_2.fixedAt G (F.scalar γ) = 0) → T.card ≤ fixedPrice B J

private theorem integer_caps {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} {pairs : Pairs band (effectiveHeight M).toNat rows} (R : Process pairs)
    (src : Source band M F rows) (hw : InBand band (effectiveHeight M))
    {i : ℕ} (hi : i ≤ laterCount band) (k : Fin 4) :
    massQ (R.live i) k ≤ integerHistory i k := by
  have h := R.cap_live paired_mass src hw hi k
  change (mass (R.live i) k : ℚ) ≤ history band i k at h
  have hf : (mass (R.live i) k : ℤ) ≤ ⌊history band i k⌋ :=
    Int.le_floor.mpr (by exact_mod_cast h)
  change (mass (R.live i) k : ℚ) ≤ ((⌊history band i k⌋ : ℤ) : ℚ)
  exact_mod_cast hf

private theorem local_at {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} {pairs : Pairs band (effectiveHeight M).toNat rows} (R : Process pairs)
    (src : Source band M F rows) (hw : InBand band (effectiveHeight M))
    (D : KoalaH2429LocalSupport.Data) (ok : KoalaH2429LocalSupport.Checked D)
    (i : Fin 22) (j : StageIndex band) (hi : j.val ≤ i.val) (hj : 0 < j.val)
    (hf : (stageAt band j).free.shape = D.free)
    (hm : (stageAt band j).moving.shape = D.moving)
    (hr : (stageAt band j).reserve = D.reserve)
    (hh : ∀ k, history band i k ≤ D.history k)
    (hweights : seedWeight i = D.weight) :
    dotQ (seedWeight i) (massQ (R.live i)) ≤ D.cap := by
  let A := R.live i
  let pair := pairAt pairs j
  let s := stageAt band j
  have h22 : i.val ≤ laterCount band := Nat.le_of_lt_succ i.isLt
  have before (k : ℕ) (hk : j.val ≤ k) (hmax : k ≤ laterCount band) :
      R.live k ⊆ R.live j := by
    induction k with
    | zero =>
      have he := Nat.eq_zero_of_le_zero hk
      rw [he]
    | succ k ih =>
      rcases hk.lt_or_eq with hlo | he
      · exact (R.next_sub (Nat.le_of_succ_le hmax)).trans
          (ih (Nat.le_of_lt_succ hlo) (Nat.le_of_succ_le hmax))
      · rw [he]
  have hA : A ⊆ R.tested j := by
    have hsub := before i hi h22
    have hjlive : R.live j = R.kept j := by simp only [Process.live,ite_eq_left (hi.trans h22)]
    rw [hjlive] at hsub
    exact hsub.trans (R.kept_sub j)
  have hdual (I : Ideal Ambient) (hI : I ∈ A) : dual I := by
    have hp : I ∈ R.kept i := by simpa only [A,Process.live,ite_eq_left h22] using hI
    exact (mem_filter.mp hp).2 (Nat.zero_le _)
  obtain ⟨ga,gb⟩ := R.sched.stage_guard j j.isLt
  have hsmall := R.sched.small_reserve j j.isLt
  have hpass : ∀ I ∈ A, Active I ∧ K1_14_2_2R.chainCompatible pair.free pair.moving I ∧
      ¬ fixedOn (R.fixed j).free.equation I ∧ ¬ fixedOn (R.fixed j).moving.equation I ∧
      orderOn I pair.free (s.reserve+1) ∧ orderOn I pair.moving (s.reserve+1) := by
    intro I hI
    obtain ⟨hp,hc,hp'⟩ := mem_filter.mp (hA hI)
    have ha := (R.geometry I hp).1
    have ht := hp' j hj le_rfl
    exact ⟨ha,ht.2.2,(hc j).1,(hc j).2,
      buffered_order src hw (free_listed j) ga hsmall ha ht.1 pair.free_mem,
      buffered_order src hw (moving_listed j) gb hsmall ha ht.2.1 pair.moving_mem⟩
  obtain ⟨x,hx,z,hz,h⟩ :=
    P1_7_4_2.paired_thresholds s.free.shape s.moving.shape (s.reserve+1) true
      pair.free pair.moving ga.ode.small ga.seed_small pair.free_ne pair.moving_ne
      (src.shape _ (free_listed j) _ _ pair.free_mem)
      (src.shape _ (moving_listed j) _ _ pair.moving_mem) pair.no_moving
      (R.fixed j).free (R.fixed j).moving A (fun _ => hdual) hpass
  change s.free.shape = D.free at hf
  change s.moving.shape = D.moving at hm
  change s.reserve = D.reserve at hr
  rw [hf,hm] at hx hz
  rw [hf,hm,hr] at h
  rw [hweights]
  exact KoalaH2429LocalSupport.count D ok hx hz (mass A)
    (fun k => (R.cap_live paired_mass src hw h22 k).trans (hh k)) h

private theorem local_bill {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} {pairs : Pairs band (effectiveHeight M).toNat rows} (R : Process pairs)
    (src : Source band M F rows) (hw : InBand band (effectiveHeight M)) (i : Fin 22) :
    dotQ (seedWeight i) (massQ (R.live i)) ≤ localSupport i := by
  have ordinary : ∀ k, 0 ≤ seedWeight i k := cutWeight_nonneg band 0 i
  have h := dotQ_mono_mass ordinary
    (integer_caps R src hw (Nat.le_of_lt_succ i.isLt : i.val ≤ laterCount band))
  by_cases special : i.val = 14 ∨ i.val = 17 ∨ i.val = 20 ∨ i.val = 21
  · obtain ⟨i,hi⟩ := i
    rcases special with he | he | he | he <;> dsimp at he <;> subst i
    · exact local_at R src hw KoalaH2429LocalSupport.local14 KoalaH2429LocalSupport.local14_checked
        ⟨14,by decide⟩ ⟨12,by decide⟩ (by decide) (by decide) rfl rfl rfl
        (by intro k; fin_cases k <;> decide +kernel) (by funext k; fin_cases k <;> decide +kernel)
    · exact local_at R src hw KoalaH2429LocalSupport.local17 KoalaH2429LocalSupport.local17_checked
        ⟨17,by decide⟩ ⟨17,by decide⟩ (by decide) (by decide) rfl rfl rfl
        (by intro k; fin_cases k <;> decide +kernel) (by funext k; fin_cases k <;> decide +kernel)
    · exact local_at R src hw KoalaH2429LocalSupport.local20 KoalaH2429LocalSupport.local20_checked
        ⟨20,by decide⟩ ⟨20,by decide⟩ (by decide) (by decide) rfl rfl rfl
        (by intro k; fin_cases k <;> decide +kernel) (by funext k; fin_cases k <;> decide +kernel)
    · exact local_at R src hw KoalaH2429LocalSupport.local21 KoalaH2429LocalSupport.local21_checked
        ⟨21,by decide⟩ ⟨20,by decide⟩ (by decide) (by decide) rfl rfl rfl
        (by intro k; fin_cases k <;> decide +kernel) (by funext k; fin_cases k <;> decide +kernel)
  · have hdefault : localSupport i = dotQ (seedWeight i) (integerHistory i) := by
      fin_cases i <;> first | rfl | exact (special (by decide)).elim
    rw [hdefault]
    exact h

private theorem ceil_eq (x : ℚ) : ⌈x⌉ = x.ceil := by
  have hlo : ⌈x⌉ ≤ x.ceil := Int.ceil_le.mpr Rat.le_ceil
  have hq : (x.ceil : ℚ) < (⌈x⌉ : ℤ)+1 :=
    Rat.ceil_lt.trans_le (add_le_add (Int.le_ceil x) le_rfl)
  have hhi : x.ceil < ⌈x⌉+1 := by exact_mod_cast hq
  omega

private theorem rank_paid {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} {pairs : Pairs band (effectiveHeight M).toNat rows} (R : Process pairs)
    (fixed : FixedPrice F) :
    ((rankMarks F R).card : ℚ) ≤ dotQ rank (massQ R.rankExit) + rounding := by
  have hlin (B J : ℕ) (guard : ODEGuard B J) (hB : B ≤ capB band) (hJ : J ≤ capJ band) :
      (fixedPrice B J : ℚ) ≤ rank 1*J + rank 2*B + (2*lam*14000^2+1) := by
    have h := fixed_fee_linear lam rho (49/100) 14000
      (by norm_num [lam,rho,KoalaH2429PrefixNumbers.lambda,KoalaH2429PrefixNumbers.rho])
      (by norm_num [rho,KoalaH2429PrefixNumbers.rho]) (by norm_num) (by norm_num)
      guard.jb hB hJ
    have hb : (1 : ℚ) - 49/100 = 51/100 := by norm_num
    simpa [fixedPrice,P1_7_4_3.mix,rank,hb,ceil_eq,add_assoc,mul_assoc] using h
  have h := rank_marks_le_with F R fixedPrice fixed (rank 1) (rank 2) (2*lam*14000^2+1)
    (by decide +kernel) (by decide +kernel) hlin (by decide +kernel)
  have hweight : (![0,rank 1,rank 2,0] : Mass) = rank := by
    funext k
    fin_cases k <;> rfl
  simpa only [hweight,rounding,add_assoc] using h

structure Books {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    {rows : Banks} {pairs : Pairs band (effectiveHeight M).toNat rows}
    (R : Process pairs) (g : FeeGrade) (seed : Finset K) where
  loss : Finset K
  point : Finset K
  loss_seed : loss.card+seed.card ≤ (⌈KoalaH2429PrefixNumbers.loss g⌉).toNat + initialE band
  point_paid : point.card ≤ (⌈pointLimit band⌉).toNat
  covers : ∀ i ≤ laterCount band, ∀ γ ∈ Γ, ∀ I ∈ R.lost i,
      OnParent F I γ → γ ∈ point ∨ γ ∈ loss
  rank_covers : ∀ γ ∈ Γ, ∀ I ∈ R.rankExit, OnParent F I γ → γ ∈ loss

private theorem nat_ceil {m : ℕ} {q : ℚ} (h : (m : ℚ) ≤ q) : m ≤ ⌈q⌉.toNat := by
  have h' : (m : ℚ) ≤ (⌈q⌉ : ℤ) := h.trans (Int.le_ceil q)
  exact Int.toNat_le_toNat (by exact_mod_cast h')

theorem failure_books {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} {pairs : Pairs band (effectiveHeight M).toNat rows}
    (R : Process pairs) (src : Source band M F rows) (hw : InBand band (effectiveHeight M))
    (g : FeeGrade) (hfinal : degree g ≤ mass R.final 0)
    (tariff : H2429AffineCurve.Tariff M F) (fixed : FixedPrice F)
    (seed : Finset K) (d : ℕ) (hparent : d + mass R.parents 2 ≤ initialCap band 2)
    (hseed : seed.card ≤ (p+1)*d + initialE band) :
    Nonempty (Books F R g seed) := by
  let n := laterCount band+1
  have hC (i : ℕ) := properBin R src i
  choose C hcost hcover using hC
  let points := (range n).biUnion fun i => (C i).direct
  let lost := (range n).biUnion fun i => curveMarks F (C i)
  let paid := lost ∪ rankMarks F R
  have next : ∀ i < n, R.live (i+1) ⊆ R.live i :=
    fun _ hi => R.next_sub (Nat.le_of_lt_succ hi)
  have fail : ∀ i < n, R.lost i ⊆ R.live i \ R.live (i+1) :=
    fun _ hi => R.lost_diff (Nat.le_of_lt_succ hi)
  have caps : ∀ i < n, ∀ k, massQ (R.live i) k ≤ integerHistory i k :=
    fun _ hi => integer_caps R src hw (Nat.le_of_lt_succ hi)
  have sumD : (∑ i ∈ range n, ((C i).cost 0 : ℚ)) ≤ KoalaH2429PrefixNumbers.adjustedSeed g := by
    have hb := P1_7_4.bill_bound_terminal n seedWeight integerHistory R.live R.lost next fail caps
    have hh : R.live n = R.final := by simp [n,Process.live]
    rw [hh] at hb
    have hx := terminal_coordinate hfinal (P1_7_4.running_nonneg seedWeight n)
    have hs := sum_le_sum (fun i (_ : i ∈ range n) => hcost i (0 : Fin 3))
    change (∑ i ∈ range n, ((C i).cost 0 : ℚ)) ≤
      ∑ i ∈ range n, dotQ (seedWeight i) (massQ (R.lost i)) at hs
    change (∑ i ∈ range n, ((C i).cost 0 : ℚ)) ≤
      weightedBill n seedWeight integerHistory - (degree g : ℚ) * running seedWeight n 0
    rw [mul_comm (degree g : ℚ)]
    linarith only [hb,hx,hs]
  have hD (i : ℕ) (hi : i < n) : ((C i).cost 0 : ℚ) ≤ KoalaH2429PrefixNumbers.adjustedSeed g :=
    (single_le_sum (fun j _ => show 0 ≤ ((C j).cost 0 : ℚ) by positivity) (mem_range.mpr hi)).trans sumD
  have hp (i : ℕ) (hi : i < n) : (C i).cost 0 < p :=
    (Nat.cast_lt (α := ℚ)).mp ((hD i hi).trans_lt (by cases g <;> decide +kernel))
  have points_paid : (points.card : ℚ) ≤ pointLimit band := by
    let start : Mass := ![(initialCap band 0 : ℚ),(initialCap band 1 : ℚ),
      (initialCap band 2 : ℚ),(initialE band : ℚ)]
    have flat : ∀ i < n, ∀ k, massQ (R.live i) k ≤ start k := by
      intro i hi k
      have hc := (R.cap_live paired_mass src hw (Nat.le_of_lt_succ hi) k).trans (history_le_initial band i k)
      fin_cases k
      · exact hc
      · exact hc
      · exact hc
      · exact hc.trans ((Nat.cast_le (α := ℚ)).mpr R.sched.initial_e_ge)
    calc
      _ ≤ ∑ i ∈ range n, ((C i).cost 2 : ℚ) := by
        exact_mod_cast (card_biUnion_le : points.card ≤ ∑ i ∈ range n, (C i).direct.card)
      _ ≤ ∑ i ∈ range n, dotQ (cutWeight band 2 i) (massQ (R.lost i)) :=
        sum_le_sum fun i _ => hcost i 2
      _ ≤ weightedBill n (cutWeight band 2) (fun _ => start) :=
        bill_bound n (cutWeight band 2) (fun _ => start) R.live R.lost next fail flat
      _ = pointLimit band := P1_7_4.flat_bill _ _ _
  let w := lossWeight band (rate0 g) (rate1 g)
  have per_bin (i : ℕ) (hi : i < n) :
      ((curveMarks F (C i)).card : ℚ) ≤ dotQ (w i) (massQ (R.lost i))+(C i).cost 0 := by
    let j : Fin 22 := ⟨i,hi⟩
    obtain ⟨ha,hh,hr,hcap⟩ := KoalaH2429PrefixNumbers.rate_checks g j
    have rate : DiscountRate H2429AffineCurve.unit (rate0 g i) (rate1 g i) := by
      refine ⟨ha,hh,fun G hG hG' => ?_⟩
      have hq : ((p+1 : ℕ) : ℚ) = KoalaH2429PrefixNumbers.qField := by decide +kernel
      have hu : H2429AffineCurve.unit G = KoalaH2429PrefixNumbers.movingUnit G := by
        unfold H2429AffineCurve.unit KoalaH2429PrefixNumbers.movingUnit KoalaH2429PrefixNumbers.alpha
        rw [show H2429AffineRates.ratio 0 = rho from by decide +kernel]
        unfold KoalaH2429PrefixNumbers.lambda
        ring
      simpa only [hq,hu] using hr ⟨G,Nat.lt_succ_of_le hG'⟩ hG
    have hsub : R.lost i ⊆ R.live i \ R.final := by
      intro I hI
      obtain ⟨hs,ht⟩ := mem_sdiff.mp (fail i hi hI)
      exact mem_sdiff.mpr ⟨hs,fun hf => ht (R.final_live (i+1) hf)⟩
    have hsplit : dotQ (seedWeight i) (massQ (R.live i \ R.final)) +
        dotQ (seedWeight i) (massQ R.final) = dotQ (seedWeight i) (massQ (R.live i)) := by
      unfold dotQ
      rw [← sum_add_distrib]
      exact sum_congr rfl fun k _ => by rw [← mul_add,massQ_split (R.final_live i)]
    have hterm := terminal_coordinate hfinal (cutWeight_nonneg band 0 i)
    have hb := local_bill R src hw j
    have hlost := (hcost i 0).trans (dotQ_mono_mass (cutWeight_nonneg band 0 i) (massQ_mono hsub))
    have hloc : (C i).cost 0 ≤ localSupport i - degree g * seedWeight i 0 := by
      change seedWeight i 0 * (degree g : ℚ) ≤ dotQ (seedWeight i) (massQ R.final) at hterm
      rw [mul_comm (degree g : ℚ)]
      change (C i).cost 0 ≤ dotQ (seedWeight i) (massQ (R.live i \ R.final)) at hlost
      change dotQ (seedWeight i) (massQ (R.live i)) ≤ localSupport i at hb
      linarith only [hsplit,hterm,hb,hlost]
    have hv := rated_curve_count_with F tariff rate (C i) (hD i hi)
      ((min_le_min le_rfl hloc).trans hcap) (hp i hi)
    have ha0 : 0≤rate0 g i := (show (0 : ℚ) ≤ ((p+1 : ℕ) : ℚ)/81 by positivity).trans rate.degree
    calc
      _ ≤ rate0 g i*((C i).cost 0 : ℚ)+rate1 g i*((C i).cost 1 : ℚ)+(C i).cost 0 := hv
      _ ≤ rate0 g i*dotQ (cutWeight band 0 i) (massQ (R.lost i)) +
            rate1 g i*dotQ (cutWeight band 1 i) (massQ (R.lost i))+(C i).cost 0 :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hcost i 0) ha0)
          (mul_le_mul_of_nonneg_left (hcost i 1) rate.height)) le_rfl
      _ = _ := by rw [dotQ_scale_add]; rfl
  have hnonneg : ∀ k, 0 ≤ rank k := by intro k; fin_cases k <;> decide +kernel
  have hbill := KoalaSeedParent.process_bill_with R rank w integerHistory caps d hparent
  rw [KoalaSeedParent.first_bill_with band n rank w integerHistory d hnonneg] at hbill
  have hW : splice 0 rank w = discountedWeight g := by funext i; cases i <;> rfl
  have hH : splice 0 (rankMass band) integerHistory = discountedHistory := by
    funext i k
    cases i with
    | zero => change (initialCap band k : ℚ) = ((⌊(initialCap band k : ℚ)⌋ : ℤ) : ℚ); simp
    | succ i => rfl
  rw [hW,hH] at hbill
  have hlast := terminal_coordinate hfinal (P1_7_4.running_nonneg (discountedWeight g) (n+1))
  have hsum := sum_le_sum (fun i (hi : i ∈ range n) => per_bin i (mem_range.mp hi))
  rw [sum_add_distrib] at hsum
  have hu : (paid.card : ℚ) ≤
      (∑ i ∈ range n, ((curveMarks F (C i)).card : ℚ)) + (rankMarks F R).card := by
    exact_mod_cast (card_union_le lost (rankMarks F R)).trans (Nat.add_le_add_right card_biUnion_le _)
  have hrs := rank_paid R fixed
  have hshare : ((p+1 : ℕ) : ℚ) ≤ rank 2 := KoalaH2429PrefixNumbers.low_seed_exact.2.2
  have hsave := mul_le_mul_of_nonneg_right hshare (Nat.cast_nonneg (α := ℚ) d)
  have hseedQ : (seed.card : ℚ) ≤ ((p+1 : ℕ) : ℚ)*d + initialE band := by exact_mod_cast hseed
  have htotal : (paid.card : ℚ)+seed.card ≤ KoalaH2429PrefixNumbers.loss g + initialE band := by
    change (paid.card : ℚ)+seed.card ≤
      weightedBill (n+1) (discountedWeight g) discountedHistory + KoalaH2429PrefixNumbers.adjustedSeed g + rounding -
        degree g * running (discountedWeight g) (n+1) 0 + initialE band
    change (∑ i ∈ range n, dotQ (w i) (massQ (R.lost i))) + dotQ rank (massQ R.rankExit) +
      dotQ (running (discountedWeight g) (n+1)) (massQ R.final) ≤
      weightedBill (n+1) (discountedWeight g) discountedHistory - rank 2*d at hbill
    rw [mul_comm (degree g : ℚ)]
    linarith only [hu,hsum,hrs,hbill,hlast,hsave,hseedQ,sumD]
  have hnat : paid.card + seed.card ≤ (⌈KoalaH2429PrefixNumbers.loss g⌉).toNat + initialE band := by
    let q := KoalaH2429PrefixNumbers.loss g
    have hi : ⌈q⌉ ≤ (⌈q⌉.toNat : ℤ) := Int.self_le_toNat _
    have hceil : q ≤ (⌈q⌉.toNat : ℕ) :=
      (Int.le_ceil q).trans (by exact_mod_cast hi)
    have hq : ((paid.card+seed.card : ℕ) : ℚ) ≤
        ((⌈q⌉.toNat+initialE band : ℕ) : ℚ) := by
      push_cast
      exact htotal.trans (add_le_add hceil le_rfl)
    exact_mod_cast hq
  refine ⟨⟨paid,points,hnat,nat_ceil points_paid,?_,?_⟩⟩
  · intro i hi γ hγ I hI hm
    rcases hcover i γ hγ ⟨I,hI,hm⟩ with h | ⟨J,hJ,h⟩
    · exact Or.inl (mem_biUnion.mpr ⟨i,mem_range.mpr (Nat.lt_succ_of_le hi),h⟩)
    · exact Or.inr (mem_union_left _ (mem_biUnion.mpr
        ⟨i,mem_range.mpr (Nat.lt_succ_of_le hi),mem_curveMarks (F := F) hγ hJ h⟩))
  · intro γ hγ I hI hm
    exact mem_union_right _ (mem_filter.mpr ⟨hγ,I,hI,hm⟩)

end
end H2429AffinePrefixBill
