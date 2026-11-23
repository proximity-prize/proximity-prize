import ProximityPrize.SubmissionLower.High6960High55Pairs
import ProximityPrize.SubmissionLower.High6960High55BankProof
import ProximityPrize.SubmissionLower.High6960High55Terminal
import ProximityPrize.SubmissionLower.HighFamilyBase82180

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace High6960High55
export P1 (K I p node twist blockLength)
export High6960High55Model (AnchorModel AnchoredFamily AdjacentChart)
abbrev t:ℕ:=blockLength - agreement

theorem degree_at_height {u D Γ} (M : AnchorModel u D) (F : AnchoredFamily M Γ)
    (γ:K) (hγ:γ ∈ Γ):(F.scalar γ).natDegree≤P1.k - 1+M.overhead.toNat:=by
  rcases (F.mark γ hγ).scalar_degree with h | h
  · simp [h]
  · change (F.scalar γ).natDegree ≤ P1.k - 1 + (P1.ModelAt.overhead M).toNat
    omega

def prefixFee (b : Band) : ℕ :=
  let f:=fees b
  f.loss+f.point+f.lowSeed+f.lowJet+f.fixedODE+f.content

end High6960High55
section
namespace High6960High55
open High6960High55 (Band agreement p blockLength)
abbrev degreeAt:=P1_7.degreeAt
abbrev quotientOrder:=P1_7.quotientOrder
def gap (hi:ℕ):=agreement - degreeAt hi
def scale (hi:ℕ):=agreement*gap hi
def muNum (hi:ℕ):=agreement*(blockLength - degreeAt hi)
def lambdaNum (hi:ℕ):=blockLength*gap hi
abbrev ceilRatio:=P1_7.ceilRatio
abbrev singularDegree:=P1_7.singularDegree
abbrev singularFee:=P1_7.singularFee
def persistentFee (lo hi e v : ℕ) : ℕ :=
  let t:=lambdaNum hi*quotientOrder lo
  let a:=muNum hi+2*t*(e - 1)
  let b:=2*hi*muNum hi+2*t*v
  ceilRatio (e*b^2+2*v*a*b) ((scale hi)^2)+e
def properFee (lo hi e v : ℕ) : ℕ :=
  let bc:=quotientOrder lo+1
  let ac:=1+bc*(e - 1)
  let cc:=bc*v+2*hi
  let bn:=lambdaNum hi*quotientOrder lo
  let an:=muNum hi+bn*(e - 1)
  let cn:=bn*v+2*hi*muNum hi
  ceilRatio (e * cc * cn +
    v*(cn*((2*e-2)*bc+ac)+cc*((2*e-2)*bn+an)) +
    v^2*((ac - 2*bc)*bn+an*bc)) (scale hi)
def flatFee (hi v:ℕ):ℕ:=ceilRatio (High6960High55.t*(p+1)*v) (gap hi)
def tangentFee (lo hi e v:ℕ):ℕ:=properFee lo hi e v+flatFee hi v+e
def wholePrice (lo hi e v : ℕ) : ℕ :=
  if v = 0 then e else singularFee e v +
    if e≤2 then persistentFee lo hi e v else tangentFee lo hi e v
structure GradeOK (lo hi fullU cap e : ℕ) (g : Grade) : Prop where
  sub:g.slots≤fullU
  separant:singularDegree e g.seedCap < p
  flat:e*degreeAt hi+g.seedCap < p
  fee:wholePrice lo hi e g.seedCap≤cap
def AllGrades (lo hi fullU cap : ℕ) : ℕ → List Grade → Prop
  | _,[] => True
  | e,g :: gs => GradeOK lo hi fullU cap e g ∧ AllGrades lo hi fullU cap (e+1) gs
theorem get_grade {lo hi fullU cap : ℕ} (gs : List Grade) (e : ℕ)
    (hall:AllGrades lo hi fullU cap e gs) (i:Fin gs.length) :
    GradeOK lo hi fullU cap (i.val+e) (gs.get i):=by
  induction gs generalizing e with
  | nil => exact Fin.elim0 i
  | cons g gs ih =>
    rcases i with ⟨_ | j,hj⟩
    · change GradeOK lo hi fullU cap (0+e) g
      simpa only [Nat.zero_add] using hall.1
    · have h := ih (e+1) hall.2 ⟨j, by simpa using hj⟩
      simpa only [List.get_cons_succ,Nat.succ_add,Nat.add_succ] using h
theorem grade_of_literals {lo hi fullU cap e v U D m price : ℕ}
    (hU:U≤fullU) (hD:singularDegree e v=D) (hDp:D < p)
    (hm:e*degreeAt hi+v=m) (hmp:m < p)
    (hprice:wholePrice lo hi e v=price) (hle:price≤cap) :
    GradeOK lo hi fullU cap e ⟨v,U⟩ :=
  ⟨hU,hD.le.trans_lt hDp,hm.le.trans_lt hmp,hprice.le.trans hle⟩
theorem sheets_le_price (lo hi e v : ℕ) : e ≤ wholePrice lo hi e v := by
  unfold wholePrice
  split
  · exact le_rfl
  · split
    · dsimp only [persistentFee]
      omega
    · unfold tangentFee
      omega
end High6960High55
end
section
namespace High6960High55
noncomputable section
open Polynomial
open High6960High55 (Band AnchorModel AnchoredFamily K p node twist agreement)
open K1_14 (L FX Seeds Equation Shape Jet Banks SeedBound liftPoly graphEval atX atMark
  jetAt triangle slots shapeSum)
open K1_14_3 (Surface Parent)
open scoped BigOperators
def BankPass (rows : Banks) (s : Shape) (q : Surface) : Prop :=
  ∀ P ∈ rows s (fullCutoff s),P ∈ q.asIdeal
def PairPass {h rows s} (pair : BufferedPair h rows s) (q : Surface) : Prop :=
  BankPass rows s.free.shape q ∧ BankPass rows s.moving.shape q ∧
    K1_14_3R.compatible pair.free pair.moving q
def MarkOn {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (q:Surface) (γ:K):Prop :=
  q.asIdeal ≤ RingHom.ker
    (eval₂RingHom (eval₂RingHom (graphEval (M.label γ)) (atX (F.scalar γ)))
      (atX (F.scalar γ).derivative))
structure PrefixInventory (b : Band) {u del} (M : AnchorModel u del) {Γ}
    (F:AnchoredFamily M Γ) {rows:Banks} (pairs:Pairs b M.overhead.toNat rows) where
  books:Finset K
  paid:books.card≤prefixFee b
  parents:Finset Surface
  geometric : ∀ q ∈ parents,Parent q
  stage_pass : ∀ q ∈ parents, ∀ s (hs : s ∈ stages b), 0 < s.reserve →
    PairPass (pairs s hs) q
  terminal_pass : ∀ q ∈ parents,BankPass rows (terminal b).shape q
  covers : ∀ γ ∈ Γ,γ ∈ books ∨ ∃ q ∈ parents,MarkOn M F q γ
def curveUnit (hi g : ℕ) : ℚ :=
  let d:=degreeAt hi
  (2*(g : ℚ)-1) * (1 + 2*((High6960High55.blockLength : ℚ)/agreement)*d) +
    ((High6960High55.blockLength - d:ℕ):ℚ) / gap hi
def CurveTariff (b : Band) {u del} (M : AnchorModel u del) {Γ}
    (F:AnchoredFamily M Γ):Prop :=
  ∀ T ⊆ Γ, ∀ J g H, 0 < g → g ≤ 80 →
    K1_14_2.SmallRootCurve J g H →
    Module.finrank K1_14_2.SeedField (K1_14_2.RootSeedSection J) < p →
    (∀ γ ∈ T,K1_14_2.OnRoot J (M.label γ) (F.scalar γ)) →
    (T.card:ℚ)≤curveUnit (finish b) g*H+g
def contactPower (h:ℕ) (s:Shape) (W:ℕ):=1+(fullCutoff s - W)/(2*h)
structure TerminalTrace (h : ℕ) (t : Bank) (rows : Banks) (f : Equation) : Prop where
  floor_bound:RankFloor h t rows
  shape : ∀ W, ∀ P ∈ rows t.shape W,K1_14_3.RowCaps P t.shape
  leading:K1_14_3.LeadingFilter h rows t.shape
  divides : ∀ W < t.shape.m * agreement, ∀ P ∈ rows t.shape W, P ≠ 0 →
    f ^ (contactPower h t.shape W - P.natDegree) ∣ P.leadingCoeff
abbrev Reduced:=P1_7.Reduced
abbrev regularRoot:=P1_7.regularRoot
def RegularCount {u del} (M : AnchorModel u del) {Γ}
    (F:AnchoredFamily M Γ) (f:Equation) (fee:ℕ):Prop :=
  ∀ T ⊆ Γ,(∀ γ ∈ T,regularRoot f (M.label γ) (F.scalar γ))→T.card≤fee
end
end High6960High55
end
section
namespace High6960High55
open High6960High55 (Band agreement p)
theorem grades_checked (b : Band) :
    AllGrades (start b) (finish b) (terminal b).shape.U (retainedCap b) 1 (grades b):=by
  cases b <;>
    repeat' refine And.intro (GradeOK.mk (by decide) (by decide) (by decide) (by decide +kernel)) ?_
  all_goals trivial
theorem grade_checked (b : Band) (i : Fin (grades b).length) :
    GradeOK (start b) (finish b) (terminal b).shape.U (retainedCap b) (i.val+1) ((grades b).get i) :=
  get_grade _ _ (grades_checked b) i
theorem terminal_guards (b : Band) :
    0 < (start b) ∧ (finish b)≤34339 ∧ 0 < (terminal b).shape.m*agreement ∧
    (terminal b).shape.m*agreement < p ∧
    (terminal b).shape.B*(131071-(start b))≤(terminal b).shape.m*agreement:=by
  cases b <;> decide +kernel
end High6960High55
end
section
namespace High6960High55
noncomputable section
open High6960High55 (K I node p agreement blockLength AnchorModel AnchoredFamily)
open K1_14_2_4 (taylorPower ordinateBound)
open P1_7_3 (persistentNodes hits_persistent section_bounds regular_chart persistent_taylor)
open Finset Polynomial ProximityPrize.Benchmark
structure FixedWord (w : I → K) (U : Finset K) (s : K → K[X]) (d : ℕ) : Prop where
  distinct:Set.InjOn s (U:Set K)
  degree : ∀ γ ∈ U,(s γ).natDegree≤d
  hits : ∀ γ ∈ U, ∃ B:Finset I,agreement≤B.card ∧ ∀ i ∈ B,(s γ).eval (node i)=w i
theorem persistent_card_le {w U s d} (hw : FixedWord w U s d) (hU : 1 < U.card) :
    (persistentNodes w U s).card≤d:=by
  obtain ⟨a,ha,b,hb,hab⟩:=one_lt_card.mp hU
  let P:=s a - s b
  have hp:P≠0:=sub_ne_zero.mpr fun eq => hab (hw.distinct ha hb eq)
  refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective P hp _ ?_).trans
    ((natDegree_sub_le _ _).trans (max_le (hw.degree a ha) (hw.degree b hb)))
  intro i hi
  change ((s a) - (s b)).eval (node i)=0
  rw [Polynomial.eval_sub,hits_persistent ha hi,hits_persistent hb hi,sub_self]
theorem section_incidence {w U s d} (hw : FixedWord w U s d) (D : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ U, (s γ).eval (node i) ≠ w i) →
      (U.filter fun γ => (s γ).eval (node i)=w i).card≤D) :
    (agreement - (persistentNodes w U s).card) * U.card ≤
      (blockLength - (persistentNodes w U s).card)*D:=by
  classical
  let sites:=persistentNodes w U s
  let nodes:Finset I:=univ \ sites
  let hits (γ:K):=nodes.filter fun i => (s γ).eval (node i)=w i
  let occ (i:I):=U.filter fun γ => (s γ).eval (node i)=w i
  have hhit (γ : K) (hγ : γ ∈ U) : agreement - sites.card ≤ (hits γ).card := by
    obtain ⟨B,hB,hvals⟩:=hw.hits γ hγ
    let good:Finset I:=univ.filter fun i => (s γ).eval (node i)=w i
    have hgood : agreement ≤ good.card :=
      hB.trans (card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _,hvals i hi⟩)
    have hZG:sites ⊆ good:=fun i hi => mem_filter.mpr ⟨mem_univ _,hits_persistent hγ hi⟩
    have heq : hits γ = good \ sites := by
      ext i
      simp only [hits,nodes,good,mem_filter,mem_sdiff,mem_univ,true_and]
      exact and_comm
    rw [heq,card_sdiff_of_subset hZG]
    exact Nat.sub_le_sub_right hgood _
  have hnodes : nodes.card = blockLength - sites.card := by
    rw [card_sdiff_of_subset (subset_univ sites),card_univ,IRSProfile.card_index]
  calc
    _ = ∑ γ ∈ U,(agreement - sites.card):=by rw [sum_const,smul_eq_mul,Nat.mul_comm]
    _ ≤ ∑ γ ∈ U,(hits γ).card:=sum_le_sum hhit
    _ = ∑ i ∈ nodes,(occ i).card:=by simp only [hits,occ,card_filter]; rw [sum_comm]
    _ ≤ ∑ _i ∈ nodes, D := by
      apply sum_le_sum
      intro i hi
      apply hsection i
      by_contra! h
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _,h⟩)
    _=_:=by rw [sum_const,smul_eq_mul,hnodes]
private def rho (s : ℕ) : ℚ :=
  ((blockLength - s:ℕ):ℚ) / ((agreement - s:ℕ):ℚ)
private abbrev density:ℚ:=(blockLength:ℚ) / agreement
private theorem weights {s d : ℕ} (hs : s ≤ d) (hd : d < agreement)
    (haux:rho d≤density*d) :
    rho s≤rho d ∧ rho s*(max 1 (d-s):ℕ)≤density*d:=by
  have hAN:agreement≤blockLength:=by decide
  have hsA:=hs.trans_lt hd
  have hdN:=hd.le.trans hAN
  have hsN:=hs.trans hdN
  have hAs:(0:ℚ) < (agreement:ℚ) - s:=sub_pos.mpr (by exact_mod_cast hsA)
  have hAd:(0:ℚ) < (agreement:ℚ) - d:=sub_pos.mpr (by exact_mod_cast hd)
  have hmain : rho s ≤ rho d := by
    unfold rho
    rw [Nat.cast_sub hsN,Nat.cast_sub hsA.le,Nat.cast_sub hdN,Nat.cast_sub hd.le]
    apply (div_le_div_iff₀ hAs hAd).mpr
    have h := mul_nonneg (sub_nonneg.mpr (show (s : ℚ) ≤ d by exact_mod_cast hs))
      (sub_nonneg.mpr (show (agreement:ℚ)≤blockLength by exact_mod_cast hAN))
    nlinarith only [h]
  refine ⟨hmain, ?_⟩
  by_cases heq:s=d
  · subst s
    simpa using haux
  have hpos:1≤d - s:=by omega
  rw [max_eq_right hpos]
  have hden:(0:ℚ) < (agreement:ℚ):=by exact_mod_cast (by decide:0 < agreement)
  have hfrac : ((d-s : ℕ) : ℚ) / ((agreement-s : ℕ) : ℚ) ≤ (d : ℚ) / agreement := by
    rw [Nat.cast_sub hs,Nat.cast_sub hsA.le]
    apply (div_le_div_iff₀ hAs hden).mpr
    have h:=mul_nonneg (Nat.cast_nonneg s:(0:ℚ)≤s) hAd.le
    nlinarith only [h]
  calc
    _ = ((blockLength-s : ℕ) : ℚ) * (((d-s : ℕ) : ℚ) / ((agreement-s : ℕ) : ℚ)) := by
      unfold rho
      ring
    _ ≤ (blockLength : ℚ) * ((d : ℚ) / agreement) :=
      mul_le_mul (by exact_mod_cast Nat.sub_le blockLength s) hfrac (by positivity) (by positivity)
    _=density*d:=by ring
private theorem rho_at_endpoint {d : ℕ} (hl : 131071 ≤ d) (hh : d ≤ 165410) :
    rho d≤density*d:=by
  have hdA:d < agreement:=hh.trans_lt (by decide)
  have hdN:d≤blockLength:=hh.trans (by decide)
  have hrho : rho d ≤ 17 := by
    unfold rho
    have hp:(0:ℚ) < ((agreement - d:ℕ):ℚ):=by exact_mod_cast Nat.sub_pos_of_lt hdA
    apply (div_le_iff₀ hp).mpr
    rw [Nat.cast_sub hdN,Nat.cast_sub hdA.le]
    change (262144:ℚ) - d≤17*((179827:ℚ) - d)
    have hQ:(d:ℚ)≤165410:=by exact_mod_cast hh
    linarith only [hQ]
  have hDensity : 1 ≤ density := by
    apply (le_div_iff₀ (show (0:ℚ) < (agreement:ℚ) by positivity)).mpr
    rw [one_mul]
    exact_mod_cast (by decide:agreement≤blockLength)
  exact hrho.trans (calc
    (17:ℚ)≤(d:ℚ):=by exact_mod_cast (show 17≤d by omega)
    _=1*(d:ℚ):=(one_mul _).symm
    _≤density*d:=mul_le_mul_of_nonneg_right hDensity (Nat.cast_nonneg _))
private theorem taylorPower_cast {g : ℕ} (hg : 0 < g) :
    (taylorPower g:ℚ)=2*(g:ℚ) - 1:=by
  unfold taylorPower
  rw [Nat.cast_sub (by omega)]
  push_cast
  rfl
private theorem regular_count {n g H d : ℕ} {U : Finset K} {s : K → Polynomial K} {w}
    (A:K1_14_2_4.RegularChart U s g H n) (hw:FixedWord w U s d)
    (hg:0 < g) (hl:131071≤d) (hh:d≤165410) :
    (U.card:ℚ)≤(2*density*d*(taylorPower g:ℚ)+rho d)*H+1:=by
  have hbound : 0 ≤ (2 * density * d * (taylorPower g : ℚ) + rho d) * (H : ℚ) := by
    unfold rho
    positivity
  by_cases hc:U.card≤1
  · have h : (U.card : ℚ) ≤ 1 := by exact_mod_cast hc
    linarith only [h,hbound]
  let sites:=persistentNodes w U s
  let t:=max 1 (d-sites.card)
  have hd:d < agreement:=hh.trans_lt (by decide)
  have hs:sites.card≤d:=persistent_card_le hw (by omega)
  have ht:0 < t:=(by decide:0 < 1).trans_le (le_max_left _ _)
  have htp : t < p := (max_le (by omega : 1 ≤ d) (Nat.sub_le _ _)).trans_lt
    (hh.trans_lt (by decide))
  have hdt : d ≤ sites.card + t := by
    have h:=le_max_right 1 (d-sites.card)
    omega
  obtain ⟨C,hreconstruct⟩:=persistent_taylor sites w hdt htp hg A.equation A.equation_degree
  let D:=taylorPower t*(g*H)+ordinateBound t g*H
  have hsection := section_bounds (w := w) A ht hw.distinct C fun γ hγ =>
    hreconstruct _ _ (hw.degree γ hγ) (fun _ hi => hits_persistent hγ hi) (A.root γ hγ) (A.simple γ hγ)
  have hinc : ((agreement - sites.card : ℕ) : ℚ) * U.card ≤ ((blockLength - sites.card : ℕ) : ℚ) * D := by
    exact_mod_cast section_incidence hw D hsection
  have hden : (0 : ℚ) < ((agreement - sites.card : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt hd)
  have hcard : (U.card : ℚ) ≤ rho sites.card * (D : ℚ) := by
    rw [rho,div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).mpr
    calc
      _=((agreement - sites.card:ℕ):ℚ)*U.card:=mul_comm _ _
      _≤_:=hinc
  obtain ⟨hρ,hρt⟩:=weights hs hd (rho_at_endpoint hl hh)
  have hρb : rho sites.card * (taylorPower t : ℚ) ≤ 2 * density * d := by
    have hb : (taylorPower t : ℚ) ≤ 2 * (t : ℚ) := by
      exact_mod_cast (Nat.sub_le (2*t) 1:taylorPower t≤2*t)
    have hρ0:0≤rho sites.card:=div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have h:=mul_le_mul_of_nonneg_left hb hρ0
    nlinarith only [h,hρt]
  have hsum:g+(g - 1)=taylorPower g:=by unfold taylorPower; omega
  have hD : D = (taylorPower t * taylorPower g + 1) * H := by
    rw [← hsum]
    dsimp [D,ordinateBound]
    ring
  refine hcard.trans (le_add_of_le_of_nonneg ?_ zero_le_one)
  calc
    _ = (rho sites.card * (taylorPower t : ℚ) * (taylorPower g : ℚ) + rho sites.card) * H := by
      rw [hD]
      push_cast
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_right hρb (Nat.cast_nonneg _)) hρ) (Nat.cast_nonneg _)
theorem persistent_curve {b : High6960High55.Band} {u del} (M : AnchorModel u del)
    {Γ} (F:AnchoredFamily M Γ) (hband:InBand b M.overhead):CurveTariff b M F:=by
  intro T hT J g H hg hgLimit hcurve _hseed hmarks
  have hlabel : Set.InjOn M.label (T : Set K) := by
    intro γ _ η _ h
    exact sub_left_inj.mp h
  obtain ⟨U, hU, hexc, n, ⟨A⟩⟩ := regular_chart T M.label F.scalar J g H hg
    (hgLimit.trans_lt (by decide)) hcurve hlabel hmarks
  let d:=degreeAt (finish b)
  have hw : FixedWord M.word U F.scalar d := by
    refine ⟨F.distinct.mono (hU.trans hT), ?_, ?_⟩
    · intro γ hγ
      rcases (F.mark γ (hT (hU hγ))).scalar_degree with hz | hm
      · simp [hz]
      · have hd : ((F.scalar γ).natDegree : ℤ) ≤ (d : ℤ) := by
          change ((F.scalar γ).natDegree:ℤ)≤131071+M.overhead at hm
          dsimp [d,degreeAt,P1_7.degreeAt]
          have h:=hband.2
          omega
        exact_mod_cast hd
    · intro γ hγ
      let m:=F.mark γ (hT (hU hγ))
      exact ⟨m.bad.support,m.bad.agreement,m.scalar_hits⟩
  have hlo:131071≤d:=Nat.le_add_right _ _
  have hhi : d ≤ 165410 := by
    have h:=(High6960High55.terminal_guards b).2.1
    dsimp [d,degreeAt,P1_7.degreeAt]
    omega
  have hregular:=regular_count A hw hg hlo hhi
  have hgQ:(1:ℚ)≤g:=by exact_mod_cast hg
  have hexcQ:((T \ U).card:ℚ)≤(taylorPower g:ℚ)*H:=by exact_mod_cast hexc
  calc
    (T.card : ℚ) = ((T \ U).card : ℚ) + (U.card : ℚ) := by
      exact_mod_cast (card_sdiff_add_card_eq_card hU).symm
    _ ≤ (taylorPower g : ℚ) * H + ((2 * density * d * (taylorPower g : ℚ) + rho d) * H + 1) :=
      add_le_add hexcQ hregular
    _ ≤ (taylorPower g : ℚ) * H + ((2 * density * d * (taylorPower g : ℚ) + rho d) * H + g) :=
      add_le_add le_rfl (add_le_add le_rfl hgQ)
    _ = curveUnit (finish b) g * H + g := by
      rw [taylorPower_cast hg]
      unfold curveUnit gap rho
      dsimp only [d]
      ring
end
end High6960High55
end
section
namespace High6960High55
noncomputable section
open Polynomial Finset MvPolynomial ProximityPrize.Benchmark
open scoped BigOperators
open High6960High55 (K I node agreement blockLength)
open K1_14 (FX)
open K1_14_6 (Biform ClosedField rootPoint)
open P1_7_7 (point slice slice_subset slice_on point_injective boxMap BoxRing
  localOrd localSeed ShortCharts WeightedCut CurveScale)
open private zero_dim_count common common_agrees from ProximityPrize.SubmissionLower.UpperBranch7
open private card_le_sum_cover from ProximityPrize.SubmissionLower.Fast055
open private eval_extend extend_mem from ProximityPrize.SubmissionLower.Fast055
private theorem common_bound {word T S d} (hword : FixedWord word T S d)
    {U:Finset K} (hU:U ⊆ T) (hsize:1 < U.card) :
    (common word U S).card≤d:=by
  obtain ⟨γ,hγ,η,hη,hne⟩:=one_lt_card.mp hsize
  let P:=S γ - S η
  have hp:P≠0:=sub_ne_zero.mpr fun he => hne (hword.distinct (hU hγ) (hU hη) he)
  refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective
    P hp _ ?_).trans ((natDegree_sub_le _ _).trans (max_le (hword.degree γ (hU hγ))
      (hword.degree η (hU hη))))
  intro j hj
  change ((S γ) - (S η)).eval (node j)=0
  rw [Polynomial.eval_sub,common_agrees hγ hj,common_agrees hη hj,sub_self]
private theorem residual_incidence {word T S d} (hword : FixedWord word T S d)
    {U:Finset K} (hU:U ⊆ T) (cap:ℚ)
    (hcap : ∀ j ∉ common word U S,((U.filter fun γ => (S γ).eval (node j)=word j).card:ℚ)≤cap) :
    ((agreement - (common word U S).card : ℕ) : ℚ) * U.card ≤
      ((blockLength - (common word U S).card:ℕ):ℚ)*cap:=by
  classical
  let sites:=common word U S
  let J:Finset I:=univ \ sites
  let rel (γ:K) (j:I):=(S γ).eval (node j)=word j
  have hJ : J.card = blockLength - sites.card := by
    rw [card_sdiff_of_subset (subset_univ sites),card_univ,IRSProfile.card_index]
  have hrows (γ : K) (hγ : γ ∈ U) :
      ((agreement - sites.card:ℕ):ℚ)≤(J.bipartiteAbove rel γ).card:=by
    obtain ⟨H,hH,heval⟩:=hword.hits γ (hU hγ)
    have hcover : H \ sites ⊆ J.bipartiteAbove rel γ := fun j hj =>
      mem_filter.mpr
        ⟨mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp hj).2⟩,heval j (mem_sdiff.mp hj).1⟩
    exact_mod_cast (Nat.sub_le_sub_right hH sites.card).trans
      ((le_card_sdiff _ _).trans (card_le_card hcover))
  have hcols (j : I) (hj : j ∈ J) :
      ((U.bipartiteBelow rel j).card:ℚ)≤cap:=hcap j (mem_sdiff.mp hj).2
  have he:=card_nsmul_le_card_nsmul rel hrows hcols
  rw [nsmul_eq_mul,nsmul_eq_mul,hJ,mul_comm (U.card:ℚ)] at he
  exact he
structure Invoice (d w e v a b D : ℕ) : Prop where
  scale_pos:0 < D
  ordinate:D≤a
  seed:D≤b
  degree:d < agreement
  fits : ∀ s ≤ d, D * (blockLength-s) * localOrd d w e s ≤ (agreement-s) * a ∧
    D*(blockLength-s)*localSeed d w v s≤(agreement-s)*b
private theorem count_step {d w e v a b D : ℕ} (hInv : Invoice d w e v a b D)
    (hcut:WeightedCut) {word T z S} (hword:FixedWord word T S d)
    (hchart:ShortCharts d w e v word T z S)
    {U:Finset K} (hU:U ⊆ T) (hsize:1 < U.card) (P:Ideal (BoxRing a b))
    (hP:P.IsPrime) (hbase:RingHom.ker (boxMap a b)≤P)
    (hdim:0 < (affineHilbertPolynomial P).natDegree)
    (hpoints : ∀ γ ∈ U,point a b z S γ ∈ zeroLocus ClosedField P)
    {c:ℚ} (hc:0 < c)
    (hchildren : ∀ (V : Finset K), V ⊆ U → ∀ (Q : Ideal (BoxRing a b)), Q.IsPrime →
      RingHom.ker (boxMap a b)≤Q →
      (affineHilbertPolynomial Q).natDegree+1=(affineHilbertPolynomial P).natDegree →
      (∀ γ ∈ V,point a b z S γ ∈ zeroLocus ClosedField Q) →
      c*V.card≤affineDegree Q) :
    (D:ℚ)*c*U.card≤affineDegree P:=by
  classical
  let sites:=common word U S
  let s:=sites.card
  let r:=D*(blockLength-s)
  let t:=agreement-s
  have hs:s≤d:=common_bound hword hU hsize
  have ht:0 < t:=Nat.sub_pos_of_lt (hs.trans_lt hInv.degree)
  have hn : 0 < blockLength-s :=
    Nat.sub_pos_of_lt (hs.trans_lt (hInv.degree.trans (by decide)))
  have hr:0 < r:=Nat.mul_pos hInv.scale_pos hn
  have ha:=hInv.scale_pos.trans_le hInv.ordinate
  have hb:=hInv.scale_pos.trans_le hInv.seed
  let:P.IsPrime:=hP
  obtain ⟨cut, hcut_box, hcut_eval⟩ := hchart U hU sites hs
    (fun _ hγ _ hj => common_agrees hγ hj)
  let ι:=algebraMap FX ClosedField
  have hsection (j : I) (hj : j ∉ sites) :
      (r : ℚ) * (c * ((U.filter fun γ => (S γ).eval (node j) = word j).card : ℚ)) ≤
        (t:ℚ)*affineDegree P:=by
    let V:=U.filter fun γ => (S γ).eval (node j)=word j
    obtain ⟨q,hq⟩:=bidegreeMap_surjective (R:=ClosedField) ha hb (MvPolynomial.map ι (cut j))
    have heval (γ : K) (hγ : γ ∈ U) :
        aeval (point a b z S γ) q=0↔(S γ).eval (node j)=word j:=by
      rw [point,aeval_monomialPoint, ← bidegreeMap_eq_monomialMap,hq]
      change MvPolynomial.eval (ι ∘ rootPoint (z γ) (S γ)) (MvPolynomial.map ι (cut j))=0↔_
      rw [eval_extend, ← map_zero ι,ι.injective.eq_iff]
      exact hcut_eval γ hγ j
    have hproper : q ∉ P := by
      intro hqP
      apply hj
      exact mem_filter.mpr ⟨mem_univ _,fun γ hγ => (heval γ hγ).mp (hpoints γ hγ q hqP)⟩
    let Qs:=(P ⊔ Ideal.span {q}).minimalPrimesFinset
    have hdeg : (r : ℚ) * (∑ Q ∈ Qs, affineDegree Q) ≤ (t : ℚ) * affineDegree P :=
      hcut a b _ _ r t ha hb hr ht (hInv.fits s hs).1 (hInv.fits s hs).2
        P hP hbase hdim q hproper (by rw [hq]; exact extend_mem (hcut_box j))
    have hcover : V.card ≤ ∑ Q ∈ Qs, (slice z S V Q).card := by
      apply card_le_sum_cover
      intro γ hγ
      obtain ⟨hγU,hv⟩:=mem_filter.mp hγ
      have hγP : point a b z S γ ∈ zeroLocus ClosedField (P ⊔ Ideal.span {q}) :=
        mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hpoints γ hγU,(heval γ hγU).mpr hv⟩
      obtain ⟨Q,hQ,hγQ⟩:=exists_retainedMinimalPrime_of_mem_zeroLocus _ 1 _ hγP (by simp)
      exact ⟨Q, Ideal.mem_minimalPrimesFinset.mpr (Ideal.mem_retainedMinimalPrimes.mp hQ).1,
        mem_filter.mpr ⟨hγ,hγQ⟩⟩
    have hparts (Q : Ideal (BoxRing a b)) (hQ : Q ∈ Qs) :
        c*((slice z S V Q).card:ℚ)≤affineDegree Q:=by
      have hmin:=Ideal.mem_minimalPrimesFinset.mp hQ
      exact hchildren _ ((slice_subset Q).trans (filter_subset _ _)) Q hmin.isPrime
        (hbase.trans (le_sup_left.trans hmin.le))
        (principalCut_natDegree_affineHilbertPolynomial_add_one hproper hmin)
        (fun _ hγ => slice_on Q hγ)
    have hcoverQ : (V.card : ℚ) ≤ ∑ Q ∈ Qs, ((slice z S V Q).card : ℚ) := by
      exact_mod_cast hcover
    have hsum : c * (V.card : ℚ) ≤ ∑ Q ∈ Qs, affineDegree Q := by
      refine (mul_le_mul_of_nonneg_left hcoverQ hc.le).trans ?_
      rw [mul_sum]
      exact sum_le_sum hparts
    exact (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg r)).trans hdeg
  let cap:ℚ:=(t:ℚ)*affineDegree P / ((r:ℚ)*c)
  have hrc:0 < (r:ℚ)*c:=mul_pos (Nat.cast_pos.mpr hr) hc
  have hinc := residual_incidence hword hU cap (fun j hj => by
    apply (le_div_iff₀ hrc).mpr
    calc
      _=(r:ℚ)*(c*((U.filter fun γ => (S γ).eval (node j)=word j).card:ℚ)):=by ring
      _≤_:=hsection j hj)
  change (t:ℚ)*U.card≤((blockLength-s:ℕ):ℚ)*cap at hinc
  have hnQ:(0:ℚ) < ((blockLength-s:ℕ):ℚ):=Nat.cast_pos.mpr hn
  have htQ:(0:ℚ) < (t:ℚ):=Nat.cast_pos.mpr ht
  apply le_of_mul_le_mul_left _ (mul_pos hnQ htQ)
  calc
    _=((r:ℚ)*c)*((t:ℚ)*U.card):=by simp only [r,Nat.cast_mul]; ring
    _ ≤ ((r : ℚ) * c) * (((blockLength-s : ℕ) : ℚ) * cap) :=
      mul_le_mul_of_nonneg_left hinc hrc.le
    _=_:=by dsimp only [cap]; field_simp [hrc.ne']
theorem count_cover {d w e v a b D : ℕ} (hInv : Invoice d w e v a b D)
    (hcut:WeightedCut) (hscale:CurveScale) {word T z S} (hword:FixedWord word T S d)
    (hchart:ShortCharts d w e v word T z S) (hz:Set.InjOn z (T:Set K))
    (Ps:Finset (Ideal (BoxRing a b)))
    (hPs : ∀ P ∈ Ps, P.IsPrime ∧ RingHom.ker (boxMap a b) ≤ P ∧
      (affineHilbertPolynomial P).natDegree=2)
    (hcover : ∀ γ ∈ T, ∃ P ∈ Ps,point a b z S γ ∈ zeroLocus ClosedField P) :
    (D:ℚ)^2*T.card≤(∑ P ∈ Ps,affineDegree P)+(D:ℚ)^2*Ps.card:=by
  classical
  have hinj := point_injective (hInv.scale_pos.trans_le hInv.ordinate)
    (hInv.scale_pos.trans_le hInv.seed) (S:=S) hz
  have curve {U : Finset K} (hU : U ⊆ T) (P : Ideal (BoxRing a b))
      (hP:P.IsPrime) (hbase:RingHom.ker (boxMap a b)≤P)
      (hdim:(affineHilbertPolynomial P).natDegree=1)
      (hpoints : ∀ γ ∈ U,point a b z S γ ∈ zeroLocus ClosedField P) :
      (D:ℚ)*U.card≤affineDegree P:=by
    by_cases hsize:1 < U.card
    · simpa only [mul_one] using
        count_step hInv hcut hword hchart hU hsize P hP hbase (by omega) hpoints
          (by norm_num : (0 : ℚ) < 1) (fun V hv Q _ _ hdimQ hpointQ => by
            rw [one_mul]
            exact zero_dim_count (hv.trans hU) hinj Q (by omega) hpointQ)
    · have hu : (U.card : ℚ) ≤ 1 := by exact_mod_cast (show U.card ≤ 1 by omega)
      calc
        _≤(D:ℚ)*1:=mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg D)
        _ ≤ affineDegree P := by
          rw [mul_one]
          exact hscale a b D hInv.scale_pos hInv.ordinate hInv.seed P hP hbase hdim
  have surface (P : Ideal (BoxRing a b)) (hP : P ∈ Ps) :
      (D:ℚ)^2*((slice z S T P).card:ℚ)≤affineDegree P+(D:ℚ)^2:=by
    obtain ⟨hp,hk,hd⟩:=hPs P hP
    by_cases hsize:1 < (slice z S T P).card
    · rw [pow_two]
      exact (count_step hInv hcut hword hchart (slice_subset P) hsize P hp hk (by omega)
        (fun _ hγ => slice_on P hγ) (Nat.cast_pos.mpr hInv.scale_pos)
        (fun V hv Q hQ hQk hQd hQV => curve (hv.trans (slice_subset P)) Q hQ hQk (by omega) hQV)).trans
          (le_add_of_nonneg_right (by positivity))
    · have hu : ((slice z S T P).card : ℚ) ≤ 1 := by
        exact_mod_cast (show (slice z S T P).card≤1 by omega)
      calc
        _≤(D:ℚ)^2*1:=mul_le_mul_of_nonneg_left hu (by positivity)
        _≤_:=by rw [mul_one]; exact le_add_of_nonneg_left (affineDegree_nonneg P)
  have hsum : T.card ≤ ∑ P ∈ Ps, (slice z S T P).card := by
    apply card_le_sum_cover
    intro γ hγ
    obtain ⟨P,hP,hγP⟩:=hcover γ hγ
    exact ⟨P,hP,mem_filter.mpr ⟨hγ,hγP⟩⟩
  have hsumQ:(T.card:ℚ) ≤ ∑ P ∈ Ps,((slice z S T P).card:ℚ):=by exact_mod_cast hsum
  calc
    _ ≤ (D : ℚ)^2 * ∑ P ∈ Ps, ((slice z S T P).card : ℚ) :=
      mul_le_mul_of_nonneg_left hsumQ (by positivity)
    _ ≤ ∑ P ∈ Ps, (affineDegree P + (D : ℚ)^2) := by
      rw [mul_sum]
      exact sum_le_sum surface
    _=_:=by rw [sum_add_distrib,sum_const,nsmul_eq_mul,mul_comm (Ps.card:ℚ)]
end
end High6960High55
end
section
namespace High6960High55
noncomputable section
open Polynomial
open High6960High55 (Band AnchorModel AnchoredFamily agreement p)
open K1_14 (Banks Jet Equation SeedBound)
open K1_14_3 (Surface Parent ProjectedProduct OrderAt)
open K1_14_4 (seedDegree seedDegree_le_iff)
theorem tested_spec (b : Band) (x : Test b) :
    Listed b (tested b x) ∧ (tested b x).shape.m=(terminal b).shape.m ∧
    (tested b x).shape.B=(terminal b).shape.B ∧ (tested b x).shape.J=(terminal b).shape.J ∧
    (tested b x).shape.U≤(terminal b).shape.U:=by
  cases x with
  | none => exact ⟨Or.inl rfl,rfl,rfl,rfl,le_rfl⟩
  | some i => exact ⟨Or.inr (Or.inr ⟨i,rfl⟩),rfl,rfl,rfl,(grade_checked b i).sub⟩
private theorem order_of_full {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows:Banks} (src:Source b M F rows) (hw:InBand b M.overhead)
    (x:Test b) {q:Surface} (hq:Parent q) (hv:BankPass rows (terminal b).shape q)
    {W} (hW:W < (tested b x).shape.m*agreement) {P:Jet}
    (hP:P ∈ rows (tested b x).shape W) :
    OrderAt q P (contactPower M.overhead.toNat (tested b x).shape W):=by
  let h:=M.overhead.toNat
  let t:=tested b x
  obtain ⟨ht,hm,hb,hj,hu⟩:=tested_spec b x
  have hchar:t.shape.m*agreement < p:=hm ▸ (terminal_guards b).2.2.2.1
  apply K1_14_3R_1.proof _ _ _ hq
  · have hd := Nat.div_le_self (fullCutoff t.shape - W) (2*h)
    change 1+(fullCutoff t.shape - W)/(2*h) < p
    change W < t.shape.m*agreement at hW
    unfold fullCutoff at *
    omega
  intro a c hac
  change a+c < 1+(fullCutoff t.shape - W)/(2*h) at hac
  have hh:0 < h:=(terminal_guards b).1.trans_le (window_nat hw).1
  have hc := (Nat.le_div_iff_mul_le (by omega : 0 < 2*h)).mp
    (show a+c≤(fullCutoff t.shape - W)/(2*h) by omega)
  rw [Nat.mul_comm (a+c),Nat.mul_add] at hc
  have top : fullCutoff t.shape = fullCutoff (terminal b).shape :=
    congrArg (fun m => m*agreement - 1) hm
  have hwc : W ≤ fullCutoff t.shape := by
    change W < t.shape.m*agreement at hW
    unfold fullCutoff
    omega
  have hw' : W+2*h*a+2*h*c≤fullCutoff (terminal b).shape:=by omega
  have ha:=src.shift t ht W P hP 0 a
  have hc' := src.shift t ht _ _ ha 1 c
  exact hv _ (src.nested t ht _ (Or.inl rfl) hm hb hj hu _ _ hw' hc')
theorem trace_of_full {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows:Banks} (src:Source b M F rows) (hw:InBand b M.overhead)
    {qs:Finset Surface} (hq : ∀ q ∈ qs,Parent q)
    (hp : ∀ q ∈ qs,BankPass rows (terminal b).shape q) {f:Equation}
    (hf:ProjectedProduct qs f) (x:Test b) :
    TerminalTrace M.overhead.toNat (tested b x) rows f:=by
  have ht:=(tested_spec b x).1
  refine ⟨src.floor_bound _ ht,src.shape _ ht,src.leading _ ht, ?_⟩
  intro W hW P hP hn
  exact hf.divides_leading P _ hn
    (fun q h => order_of_full src hw x (hq q h) (hp q h) hW hP)
theorem grade_of_rejections {b : Band} {f : Equation} (hp : 0 < f.natDegree)
    (reject : ∀ x : Test b, threshold b x ≤ f.natDegree →
      seedThreshold b x≤seedDegree f→False) :
    ∃ i:GradeIndex b,f.natDegree=i.val+1 ∧ SeedBound f ((grades b).get i).seedCap:=by
  have he : f.natDegree ≤ (grades b).length := by
    by_contra! hlo
    exact reject none hlo (Nat.zero_le _)
  let i:GradeIndex b:=⟨f.natDegree-1,by omega⟩
  have hidx:f.natDegree=i.val+1:=by dsimp [i]; omega
  refine ⟨i,hidx,(seedDegree_le_iff _ _).mp ?_⟩
  by_contra! hlow
  exact reject (some i) hidx.ge hlow
end
end High6960High55
end
section
namespace High6960High55
open High6960High55 (Band agreement blockLength)
open P1_7_7 (localOrd localSeed)
open private coordinate_bounds from ProximityPrize.SubmissionLower.UpperBranch7
def ordinateFee (lo hi e:ℕ):=muNum hi+2*(lambdaNum hi*quotientOrder lo)*(e - 1)
def seedFee (lo hi v:ℕ):=2*hi*muNum hi+2*(lambdaNum hi*quotientOrder lo)*v
theorem band_invoice {b : Band} {w : ℕ} (hwlo : (start b) ≤ w) (hwhi : w ≤ (finish b))
    (e v:ℕ) :
    Invoice (131071+w) w e v (ordinateFee (start b) (finish b) e) (seedFee (start b) (finish b) v)
      (scale (finish b)):=by
  obtain ⟨hlo,hhi,_,_,_⟩:=terminal_guards b
  have hdhi : degreeAt (finish b) < agreement := by
    change 131071+(finish b) < 179827
    omega
  have hd:131071+w < agreement:=(Nat.add_le_add_left hwhi _).trans_lt hdhi
  have hA:agreement≤blockLength:=by decide
  have hD:0 < scale (finish b):=Nat.mul_pos (by decide) (Nat.sub_pos_of_lt hdhi)
  have hm : scale (finish b) ≤ muNum (finish b) :=
    Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hA _)
  have hpos:1≤2*(finish b):=by omega
  refine ⟨hD,hm.trans (Nat.le_add_right _ _), ?_,hd, ?_⟩
  · exact hm.trans ((by
      simpa only [one_mul] using Nat.mul_le_mul_right (muNum (finish b)) hpos :
      muNum (finish b)≤2*(finish b)*muNum (finish b)).trans (Nat.le_add_right _ _))
  · intro s hs
    have hord : (131071+w) - 2*w ≤ quotientOrder (start b) := by
      unfold quotientOrder P1_7.quotientOrder
      omega
    exact coordinate_bounds hA (Nat.add_le_add_left hwhi _) hdhi hwhi hord hs
theorem fee_of_bound {lo hi e v count : ℕ} (hD : 0 < scale hi)
    (hcount : ((scale hi : ℕ) : ℚ)^2 * count ≤
      ((e * (seedFee lo hi v)^2 + 2*v*(ordinateFee lo hi e)*(seedFee lo hi v) : ℕ) : ℚ) +
        ((scale hi:ℕ):ℚ)^2*e) :
    count≤persistentFee lo hi e v:=by
  let D:=(scale hi)^2
  let num:=e*(seedFee lo hi v)^2+2*v*(ordinateFee lo hi e)*(seedFee lo hi v)
  have hd:0 < D:=pow_pos hD _
  have h:D*count≤num+D*e:=by exact_mod_cast hcount
  have hmul : (count-e) * D ≤ num := by
    rw [Nat.sub_mul,Nat.mul_comm count,Nat.mul_comm e]
    omega
  have hdiv:=(Nat.le_div_iff_mul_le hd).mpr (hmul.trans (Nat.le_add_right num (D-1)))
  change count≤(num+(D-1)) / D+e
  omega
end High6960High55
end
section
namespace High6960High55
noncomputable section
open Polynomial MvPolynomial
open High6960High55 (AnchorModel AnchoredFamily Band I K agreement node p)
open K1_14 (Equation FX L SeedBound seedEmbedding liftPoly)
open K1_14_1 (PoleData CRTLift MarkResidues seedPair)
open P1_7_7 (CRTChart poleProduct sheet_cover curve_scale_of_cut)
open scoped BigOperators
theorem persistent_count {b : Band} {u del} (M : AnchorModel u del)
    {Γ} (F:AnchoredFamily M Γ) (hband:InBand b M.overhead)
    {H} (hH:AdjacentChart M F H) (i:GradeIndex b) {f:Equation}
    (hf:Reduced f) (hseed:SeedBound f ((grades b).get i).seedCap) :
    RegularCount M F f (persistentFee (start b) (finish b) f.natDegree ((grades b).get i).seedCap):=by
  intro T hT hroots
  let w:=M.overhead.toNat
  let d:=131071+w
  let e:=f.natDegree
  let v:=((grades b).get i).seedCap
  obtain ⟨hwlo,hwhi⟩:=window_nat hband
  obtain ⟨hlo,hhi,_,_,_⟩:=terminal_guards b
  have hw:0 < w:=hlo.trans_le hwlo
  have h2w:2*w≤d:=by dsimp only [d]; omega
  have hInv:=band_invoice hwlo hwhi e v
  have hdp:d < p:=hInv.degree.trans (by decide)
  have hword : FixedWord M.word T F.scalar d := by
    refine ⟨F.distinct.mono hT, ?_, ?_⟩
    · intro γ hγ
      rcases (F.mark γ (hT hγ)).scalar_degree with hz | hdeg
      · simp only [hz,natDegree_zero,Nat.zero_le]
      · change ((F.scalar γ).natDegree : ℤ) ≤ 131072 - 1 + M.overhead at hdeg
        have hd' : ((F.scalar γ).natDegree : ℤ) ≤ 131071 + (w : ℤ) := by
          dsimp only [w]
          omega
        exact_mod_cast hd'
    · intro γ hγ
      let mark:=F.mark γ (hT hγ)
      exact ⟨mark.bad.support,mark.bad.agreement,mark.scalar_hits⟩
  have hz:Set.InjOn M.label (T:Set K):=fun _ _ _ _ h => sub_left_inj.mp h
  obtain ⟨CRT,hCRT⟩:=High6960High55Model.crt_chart M F H hw hH
  obtain ⟨hmonic, hdeg, hcenter, hnodes⟩ :=
    High6960High55Model.pole_data (M:=M) (F:=F) hH
  have hchart := P1_7_7_2.proof d w e v hw h2w hdp (poleProduct H) hmonic hdeg hcenter hnodes
    f hf.1 le_rfl hseed T M.label F.scalar M.word hword.degree hroots CRT
    (fun γ hγ => hCRT γ (hT hγ))
  obtain ⟨Ps, hPs, hcard, hsum, hcover⟩ := sheet_cover
    (hInv.scale_pos.trans_le hInv.ordinate) (hInv.scale_pos.trans_le hInv.seed)
    f hf.1 (show f.natDegree≤e from le_rfl) hseed T M.label F.scalar hroots
  have hcount:=count_cover hInv P1_7_7_3.proof (curve_scale_of_cut P1_7_7_3.proof) hword hchart hz Ps hPs hcover
  apply fee_of_bound hInv.scale_pos
  refine hcount.trans (add_le_add hsum ?_)
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcard) (by positivity)
end
end High6960High55
end
section
namespace High6960High55
noncomputable section
open Finset Polynomial MvPolynomial
open High6960High55 (agreement)
open K1_14 (Shape shapeSum Banks Equation FX Jet slots triangle SeedBound)
open K1_14_3 (RowCaps)
open K1_14_4 (gradeWidth seedDegree seedDegree_pow)
open P1_7_5 (kept)
open private position_sum from ProximityPrize.SubmissionLower.UpperBranch5
open private rank_joint_multiples_le gradeCapacity_eq from ProximityPrize.SubmissionLower.UpperBranch5
open private shapeSum_swap from ProximityPrize.SubmissionLower.Fast072
open private finrank_le_grades mem_filtered from ProximityPrize.SubmissionLower.Fast069
def cutoffCapacity (h : ℕ) (s : Shape) (E v W : ℕ) : ℕ :=
  shapeSum s fun q j =>
    if q*(131071-h) ≤ W+j then
      kept s.U v ((q-j)/E) (contactPower h s W - j)
    else 0
private def gradeCapacity (h : ℕ) (s : Shape) (E v W j : ℕ) : ℕ :=
  let r:=contactPower h s W - j
  (gradeWidth (131071-h) s.B W j - r*E)*slots s.U (r*v)
private theorem cutoffCapacity_eq (h : ℕ) (s : Shape) (E v W : ℕ)
    (hk:0 < 131071-h) (he:0 < E) :
    (∑ j ∈ range (s.J+1),gradeCapacity h s E v W j)=cutoffCapacity h s E v W:=by
  rw [cutoffCapacity, ← shapeSum_swap]
  apply sum_congr rfl
  intro j _
  exact gradeCapacity_eq _ _ _ _ _ _ _ _ hk he
set_option backward.isDefEq.respectTransparency false in
theorem cutoff_finrank_le (h : ℕ) (s : Shape) (E v W : ℕ) (V : Submodule FX Jet)
    {f:Equation} (hf:f≠0) (hE:E≤f.natDegree) (hv:v≤seedDegree f)
    (hk:0 < 131071-h) (he:0 < E)
    (hcaps : ∀ P ∈ V,RowCaps P s)
    (hlead : ∀ P ∈ V, P ≠ 0 →
      (P.leadingCoeff.natDegree+P.natDegree)*(131071-h)≤W+P.natDegree)
    (hdvd : ∀ P ∈ V,P≠0→f ^ (contactPower h s W - P.natDegree) ∣ P.leadingCoeff) :
    Module.finrank FX V≤cutoffCapacity h s E v W:=by
  have hrow {P : Jet} (hP : P ∈ V) (hn : P ≠ 0) :
      P.leadingCoeff.natDegree+P.natDegree≤s.B ∧ P.natDegree≤s.J ∧
      SeedBound P.leadingCoeff s.U:=by
    have ha : (P.coeff P.natDegree).coeff P.leadingCoeff.natDegree ≠ 0 := by
      rw [coeff_natDegree,coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn)
    obtain ⟨hB,hJ,_⟩:=hcaps P hP _ _ ha
    refine ⟨hB,hJ,fun i => ?_⟩
    by_cases hi:P.leadingCoeff.coeff i=0
    · simp [hi]
    · rw [← coeff_natDegree] at hi ⊢
      exact (hcaps P hP _ _ hi).2.2
  rw [← cutoffCapacity_eq h s E v W hk he]
  refine finrank_le_grades (F := FX) (A := Equation) V (gradeCapacity h s E v W)
    (s.J+1) ?_ ?_
  · intro j
    let r:=contactPower h s W - j
    apply rank_joint_multiples_le _ (g:=f^r) (pow_ne_zero r hf)
    · rw [Polynomial.natDegree_pow]
      exact Nat.mul_le_mul_left _ hE
    · rw [seedDegree_pow hf]
      exact Nat.mul_le_mul_left _ hv
    · rintro c ⟨⟨P, hP⟩, rfl⟩ hc
      change P.coeff j≠0 at hc
      obtain ⟨hpV,hd⟩:=mem_filtered.mp hP
      have hn : P ≠ 0 := by
        intro hz
        exact hc (by simp [hz])
      have hj : P.natDegree = j :=
        le_antisymm (Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt hn).2 hd))
          (le_natDegree_of_ne_zero hc)
      obtain ⟨hB,_,hseed⟩:=hrow hpV hn
      have hwidth:=hlead P hpV hn
      have hdiv:=hdvd P hpV hn
      rw [hj] at hB hwidth hdiv
      change (P.coeff j).natDegree < _ ∧ SeedBound (P.coeff j) _ ∧ _ ∣ P.coeff j
      rw [← hj,coeff_natDegree,hj]
      refine ⟨?_,hseed,hdiv⟩
      have hd:=(Nat.le_div_iff_mul_le hk).2 hwidth
      unfold gradeWidth
      omega
  · intro P hp
    by_cases hn:P=0
    · simp [hn]
    · exact (natDegree_lt_iff_degree_lt hn).1 (Nat.lt_succ_of_le (hrow hp hn).2.1)
theorem cutoff_total (h : ℕ) (s : Shape) (E v : ℕ) (hh : 0 < 2*h) (hk : 1 ≤ 131071-h) :
    (∑ W ∈ range (s.m*agreement), cutoffCapacity h s E v W) + jointGain h s E v =
      triangle s.U*shapeSum s (fun q j => s.m*agreement+j-q*(131071-h)):=by
  have hswap (F : ℕ → ℕ → ℕ → ℕ) :
      (∑ W ∈ range (s.m*agreement), shapeSum s (F W)) =
        shapeSum s (fun q j => ∑ W ∈ range (s.m*agreement),F W q j):=by
    unfold shapeSum
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    rw [sum_comm]
  simp only [cutoffCapacity,jointGain]
  rw [hswap]
  simp only [shapeSum, ← sum_add_distrib,mul_sum]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro j hj
  have hjq:j≤q:=(Nat.le_of_lt_succ (mem_range.mp hj)).trans (min_le_left _ _)
  have hq:q≤q*(131071-h):=by simpa using Nat.mul_le_mul_left q hk
  exact position_sum (s.m*agreement) (2*h) (q*(131071-h)) j s.U v ((q-j)/E)
    (hjq.trans hq) hh
private theorem trace_rank_le {h E v W : ℕ} {t : Bank}
    {rows:K1_14.Banks} {f:K1_14.Equation} (ht:TerminalTrace h t rows f)
    (hne:f≠0) (hE:E≤f.natDegree) (hv:v≤K1_14_4.seedDegree f)
    (hk:0 < 131071 - h) (he:0 < E) (hW:W < t.shape.m*agreement) :
    Module.finrank FX (rows t.shape W)≤cutoffCapacity h t.shape E v W :=
  cutoff_finrank_le h t.shape E v W (rows t.shape W) (f := f) hne hE hv hk he
    (fun P hP => ht.shape W P hP)
    (fun P hP hn => ht.leading W P hP hn)
    (fun P hP hn => ht.divides W hW P hP hn)
theorem joint_loss {b : High6960High55.Band} {h : ℕ} (hl : (start b) ≤ h) (hu : h ≤ (finish b))
    (x:Test b) {rows f} (hf:Reduced f) (ht:TerminalTrace h (tested b x) rows f)
    (hE:threshold b x≤f.natDegree) (hv:seedThreshold b x≤seedDegree f) :
    jointGain h (tested b x).shape (threshold b x) (seedThreshold b x)≤debit h (tested b x):=by
  obtain ⟨hlo,hhi,htop,_,hwidth⟩:=terminal_guards b
  obtain ⟨_,hm,hB,_,_⟩:=tested_spec b x
  have hh:0 < 2*h:=by omega
  have hk:0 < 131071-h:=by omega
  have he:0 < threshold b x:=by cases x <;> exact Nat.succ_pos _
  have hne : f ≠ 0 := by
    intro hz
    have hpos:=hf.1
    simp [hz] at hpos
  let t:=tested b x
  let top:=t.shape.m*agreement
  have htopPos : 0 < top := by
    change 0 < (tested b x).shape.m*agreement
    rwa [hm]
  have hbWidth : t.shape.B*(131071-h) ≤ top := by
    change (tested b x).shape.B*(131071-h)≤(tested b x).shape.m*agreement
    rw [hm,hB]
    exact (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hl _)).trans hwidth
  have htopSub:top-1+1=top:=by omega
  have hraw : ∀ q ≤ t.shape.B, ∀ j ≤ min q t.shape.J,
      q*(131071-h)≤top-1+1+j:=by
    intro q hq j _
    rw [htopSub]
    exact (Nat.mul_le_mul_right _ hq).trans (hbWidth.trans (by omega:top≤top+j))
  have hmin:=ht.floor_bound (top-1) (show top-1 < top by omega) hraw
  change triangle t.shape.U * shapeSum t.shape (fun q j => top-1+1+j-q*(131071-h)) ≤
    debit h t + ∑ W ∈ range (top-1+1),Module.finrank FX (rows t.shape W) at hmin
  rw [htopSub] at hmin
  have hmax : (∑ W ∈ range top, Module.finrank FX (rows t.shape W)) ≤
      ∑ W ∈ range top,cutoffCapacity h t.shape (threshold b x) (seedThreshold b x) W:=by
    apply sum_le_sum
    intro W hW
    exact trace_rank_le ht hne hE hv hk he (mem_range.mp hW)
  have htotal:=cutoff_total h t.shape (threshold b x) (seedThreshold b x) hh hk
  change (∑ W ∈ range top, cutoffCapacity h t.shape (threshold b x) (seedThreshold b x) W) +
    jointGain h t.shape (threshold b x) (seedThreshold b x) =
    triangle t.shape.U*shapeSum t.shape (fun q j => top+j-q*(131071-h)) at htotal
  change jointGain h t.shape (threshold b x) (seedThreshold b x)≤debit h t
  omega
end
end High6960High55
end
section
namespace High6960High55
noncomputable section
open Polynomial
open High6960High55 (Band AnchorModel AnchoredFamily K)
open K1_14 (Banks Equation SeedBound atMark graphEval)
open K1_14_4 (seedDegree seedDegree_le_iff)
def c1 : Prop :=
  ∀ (b : Band) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b M.overhead→M.shift ∉ Γ → ∀ H,AdjacentChart M F H →
    ∃ rows:Banks,Source b M F rows
def c2 : Prop :=
  ∀ (b : Band) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b M.overhead→M.shift ∉ Γ → ∀ rows,Source b M F rows →
    Nonempty (Pairs b M.overhead.toNat rows)
def c3 : Prop :=
  ∀ (b : Band) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b M.overhead→M.shift ∉ Γ → ∀ H,AdjacentChart M F H →
    ((start b) < 7773→CurveTariff b M F) →
    ∀ rows,Source b M F rows → ∀ pairs:Pairs b M.overhead.toNat rows,
    Nonempty (PrefixInventory b M F pairs)
def c4 : Prop :=
  ∀ (b : Band) h, (start b) ≤ h → h ≤ (finish b) → ∀ x : Test b,
    debit h (tested b x) < jointGain h (tested b x).shape (threshold b x) (seedThreshold b x)
def c5 : Prop :=
  ∀ (b : Band) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b M.overhead→M.shift ∉ Γ → ∀ H,AdjacentChart M F H →
    ∀ (i:GradeIndex b) f,Reduced f→f.natDegree=i.val+1→3≤f.natDegree →
    0 < seedDegree f→SeedBound f ((grades b).get i).seedCap →
    RegularCount M F f (tangentFee (start b) (finish b) f.natDegree ((grades b).get i).seedCap)
private theorem retained_count (h5 : c5) {b u del}
    (M:AnchorModel u del) {Γ} (F:AnchoredFamily M Γ)
    (hw:InBand b M.overhead) (hshift:M.shift ∉ Γ) {H} (hH:AdjacentChart M F H)
    (T:Finset K) (hT:T ⊆ Γ) (f:Equation) (hf:Reduced f)
    (i:GradeIndex b) (he:f.natDegree=i.val+1) (hs:SeedBound f ((grades b).get i).seedCap)
    (hr : ∀ γ ∈ T,atMark f (M.label γ) (F.scalar γ)=0):T.card≤(retainedCap b):=by
  classical
  let v:=((grades b).get i).seedCap
  have cert:=grade_checked b i
  rw [← he] at cert
  have hprice:wholePrice (start b) (finish b) f.natDegree v≤(retainedCap b):=cert.fee
  by_cases hzero:seedDegree f=0
  · have hfix := High6960High55Model.fixed_count M F T hT hf.1 ((seedDegree_le_iff f 0).mp hzero.le) hr
    exact hfix.trans ((sheets_le_price _ _ _ _).trans hprice)
  have hpos:=Nat.pos_of_ne_zero hzero
  have hv:v≠0:=Nat.ne_of_gt (hpos.trans_le ((seedDegree_le_iff _ _).mpr hs))
  let bad:=T.filter fun γ => graphEval (M.label γ) (f.resultant f.derivative)=0
  have hb:bad ⊆ T:=Finset.filter_subset _ _
  have hbad := High6960High55Model.resultant_count M hf hs cert.separant bad
    (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hreg : ∀ γ ∈ T \ bad, regularRoot f (M.label γ) (F.scalar γ) := by
    intro γ hγ
    obtain ⟨ht,hn⟩:=Finset.mem_sdiff.mp hγ
    exact P1_7.regular_of_resultant hf.1 (hr γ ht) (fun hz => hn (Finset.mem_filter.mpr ⟨ht,hz⟩))
  have hpartition:=Finset.card_sdiff_add_card_eq_card hb
  have hsub:T \ bad ⊆ Γ:=Finset.sdiff_subset.trans hT
  apply le_trans _ hprice
  by_cases hsmall:f.natDegree≤2
  · have hreg' := persistent_count M F hw hH i hf hs _ hsub hreg
    simp only [wholePrice,ite_eq_right hv,ite_eq_left hsmall]
    change bad.card≤singularFee f.natDegree v at hbad
    change (T \ bad).card≤persistentFee (start b) (finish b) f.natDegree v at hreg'
    omega
  · have hreg' := h5 b u del M Γ F hw hshift H hH i f hf he (by omega) hpos hs _ hsub hreg
    simp only [wholePrice,ite_eq_right hv,ite_eq_right hsmall]
    change bad.card≤singularFee f.natDegree v at hbad
    change (T \ bad).card≤tangentFee (start b) (finish b) f.natDegree v at hreg'
    omega
def HighStatement : Prop :=
  ∀ (b : Band) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    ((start b):ℤ)≤M.overhead→M.overhead≤((finish b):ℤ) →
    Γ.card≤(prefixFee b)+(retainedCap b)+1

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4)
    (h5:c5):High6960High55.HighStatement:=by
  classical
  intro b u del M Γ F hlo hhi
  have hw:InBand b M.overhead:=⟨hlo,hhi⟩
  let regular:=Γ.erase M.shift
  have hreg:regular ⊆ Γ:=Finset.erase_subset _ _
  have hshift:M.shift ∉ regular:=Finset.notMem_erase _ _
  let G : AnchoredFamily M regular :=
    ⟨F.scalar,fun γ hγ => F.mark γ (hreg hγ),F.distinct.mono hreg⟩
  suffices hc : regular.card ≤ (prefixFee b) + (retainedCap b) by
    have herase:Γ.card - 1≤regular.card:=Finset.pred_card_le_card_erase
    omega
  obtain ⟨H,hH⟩:=High6960High55Model.adjacent_chart M G
  obtain ⟨rows,src⟩:=h1 b u del M regular G hw hshift H hH
  obtain ⟨pairs⟩:=h2 b u del M regular G hw hshift rows src
  obtain ⟨Q⟩ := h3 b u del M regular G hw hshift H hH
    (fun _ => persistent_curve M G hw) rows src pairs
  let keep:=regular \ Q.books
  have hk:keep ⊆ regular:=Finset.sdiff_subset
  have hpaid : (regular \ keep).card ≤ (prefixFee b) := by
    apply (Finset.card_le_card ?_).trans Q.paid
    intro γ hγ
    obtain ⟨ha,hn⟩:=Finset.mem_sdiff.mp hγ
    by_contra hm
    exact hn (Finset.mem_sdiff.mpr ⟨ha,hm⟩)
  have cover : ∀ γ ∈ keep, ∃ q ∈ Q.parents, MarkOn M G q γ := fun γ hγ =>
    (Q.covers γ (hk hγ)).resolve_left (Finset.mem_sdiff.mp hγ).2
  suffices hkept : keep.card ≤ (retainedCap b) by
    have hpart:=Finset.card_sdiff_add_card_eq_card hk
    omega
  by_cases hm:keep.Nonempty
  · obtain ⟨γ,hγ⟩ := hm
    obtain ⟨q,hq,_⟩:=cover γ hγ
    obtain ⟨f,hf⟩:=K1_14_3_7.proof Q.parents ⟨q,hq⟩ Q.geometric
    have hred:Reduced f:=⟨hf.positive,hf.primitive,hf.separable⟩
    obtain ⟨hl,hu⟩:=window_nat hw
    obtain ⟨i,he,hs⟩ := grade_of_rejections (b := b) hf.positive (by
      intro x hE hv
      have trace:=trace_of_full src hw Q.geometric Q.terminal_pass hf x
      exact (h4 b _ hl hu x).not_ge (joint_loss hl hu x hred trace hE hv))
    apply retained_count h5 M G hw hshift hH keep hk f hred i he hs
    intro η hη
    obtain ⟨q',hq',hon⟩:=cover η hη
    have hz:=RingHom.mem_ker.mp (hon (hf.vanishes q' hq'))
    simpa only [coe_eval₂RingHom,eval₂_C,atMark] using hz
  · simp [Finset.not_nonempty_iff_eq_empty.mp hm]
end
end High6960High55
end

