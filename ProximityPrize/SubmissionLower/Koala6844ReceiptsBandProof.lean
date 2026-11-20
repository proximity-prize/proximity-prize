import ProximityPrize.SubmissionLower.Koala6844ReceiptsCubicSum

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4800000

def bandCoordinate (source target : Flag) (j : Nat) : Flag :=
  ⟨source.r-(j+1)*target.r,source.y-(j+1)*target.y,source.t-(j+1)*target.t⟩

def bandChannel (source target : Flag) (j : Nat) : Nat :=
  let g := bandCoordinate source target j
  fastChannelCount g.t g.y g.r

private theorem budget_sum_channels (width dt dy dr T middleCap R fuel : Nat) :
    fastPowerBandBudget width dt dy dr T middleCap R fuel =
      width*(∑ i ∈ Finset.range fuel, fastChannelCount (T-i*dt) (middleCap-i*dy) (R-i*dr)) := by
  induction fuel generalizing T middleCap R with
  | zero => simp [fastPowerBandBudget]
  | succ n ih =>
    rw [fastPowerBandBudget,ih,Finset.sum_range_succ',Nat.mul_add]
    simp only [Nat.zero_mul,Nat.sub_zero]
    have hsum : (∑ i ∈ Finset.range n, fastChannelCount (T-dt-i*dt) (middleCap-dy-i*dy) (R-dr-i*dr)) =
        ∑ i ∈ Finset.range n, fastChannelCount (T-(i+1)*dt) (middleCap-(i+1)*dy) (R-(i+1)*dr) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Nat.sub_sub,Nat.add_mul,Nat.one_mul,Nat.add_comm]
    rw [hsum,Nat.add_comm]

theorem bandBudget_eq_sum_channels (s f : Flag) :
    fastPowerBandBudget flowWidth f.t f.y f.r (s.t-f.t) (s.y-f.y) (s.r-f.r) (bandFuel s f) =
      flowWidth*(∑ j ∈ Finset.range (bandFuel s f), bandChannel s f j) := by
  rw [budget_sum_channels]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [bandChannel,bandCoordinate,Nat.sub_sub,Nat.add_mul,Nat.one_mul,Nat.add_comm]

private theorem chooseTwo_weight (n : Nat) :
    6*(chooseTwo (n+1) : Int) = 3*((n : Int)+1)*n := by
  have h : (n+1).descFactorial 2 = 2*chooseTwo (n+1) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.choose_two_right,Nat.factorial_two]
    rfl
  have hi := congrArg (fun i : Nat => (i : Int)) h
  change ((n+1).descFactorial 2 : Int) = ((2*chooseTwo (n+1) : Nat) : Int) at hi
  rw [Nat.cast_descFactorial_two,Nat.cast_mul] at hi
  push_cast at hi
  linear_combination -3*hi

private theorem chooseThree_weight (n : Nat) :
    6*(chooseThree (n+1) : Int) = ((n : Int)+1)*n*((n : Int)-1) := by
  have hch : chooseThree (n+1) = (n+1).choose 3 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    simp only [chooseThree, show 3=2+1 by decide,Nat.descFactorial_succ,Nat.descFactorial_zero,
      Nat.factorial_succ,Nat.factorial_zero,Nat.sub_zero,Nat.mul_one]
    norm_num
    ac_rfl
  rw [hch]
  by_cases hn : n = 0
  · subst n
    decide +kernel
  · have h : ((n+1).descFactorial 3 : Int) = 6*((n+1).choose 3 : Int) := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      norm_num [Nat.factorial]
    rw [← h, show 3=2+1 by decide,Nat.descFactorial_succ,Nat.cast_mul,
      Nat.cast_sub (by omega : 2 ≤ n+1),Nat.cast_descFactorial_two]
    push_cast
    ring

private theorem chooseTwo_le_product (n : Nat) : chooseTwo (n+1) ≤ (n+1)*n := by
  unfold chooseTwo
  rw [Nat.add_sub_cancel]
  exact Nat.div_le_self _ _

private theorem fastChannelCount_scaled (T middleCap S M B : Nat)
    (hM : min T middleCap = M) (hB : min S M = B) :
    let E := M-B
    6*(fastChannelCount T middleCap S : Int) =
      6*((B : Int)+1)*((E : Int)+1)*((T : Int)+1) -
      3*((B : Int)+1)*((E : Int)+1)*E - 3*((E : Int)+1)*((B : Int)+1)*B +
      3*((T : Int)+1-M)*((B : Int)+1)*B + ((B : Int)+1)*B*((B : Int)-1) := by
  let E := M-B
  have hBT : B ≤ M := hB ▸ min_le_right S M
  have hMT : M ≤ T := hM ▸ min_le_left T middleCap
  have hE : E+B ≤ T+1 := by dsimp only [E]; omega
  have hsub : (E+1)*B + chooseTwo (E+1) ≤ (E+1)*(T+1) := by
    calc
      _ ≤ (E+1)*B+(E+1)*E := Nat.add_le_add_left (chooseTwo_le_product E) _
      _ = (E+1)*(E+B) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hE
  have hBsub : (E+1)*chooseTwo (B+1) ≤ (B+1)*((E+1)*(T+1)-chooseTwo (E+1)) := by
    calc
      _ ≤ (E+1)*((B+1)*B) := Nat.mul_le_mul_left _ (chooseTwo_le_product B)
      _ = (B+1)*((E+1)*B) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_sub_of_add_le hsub)
  unfold fastChannelCount
  rw [hM]
  dsimp only
  rw [hB]
  change 6*((((B+1)*((E+1)*(T+1)-chooseTwo (E+1))-(E+1)*chooseTwo (B+1) +
    (T+1-M)*chooseTwo (B+1)+chooseThree (B+1)) : Nat) : Int) = _
  push_cast [Nat.cast_sub hBsub, Nat.cast_sub (show chooseTwo (E+1) ≤ (E+1)*(T+1) by omega),
    Nat.cast_sub (hMT.trans (Nat.le_succ T))]
  linear_combination (-((B : Int)+1))*chooseTwo_weight E +
    ((T : Int)+1-M-((E : Int)+1))*chooseTwo_weight B + chooseThree_weight B


structure BandPiece where
  stop : Nat
  middleIsValue : Bool
  minimumIsSlope : Bool
  deriving Repr

private def pieceMid {R : Type} (p : BandPiece) (t v : R) : R :=
  if p.middleIsValue then v else t

private def pieceLow {R : Type} (p : BandPiece) (m s : R) : R :=
  if p.minimumIsSlope then s else m

private def pieceFitsAt (p : BandPiece) (s f : Flag) (j : Nat) : Bool :=
  let g := bandCoordinate s f j
  let m := pieceMid p g.t g.y
  decide (((if p.middleIsValue then g.y ≤ g.t else g.t ≤ g.y) ∧
    (if p.minimumIsSlope then g.r ≤ m else m ≤ g.r)))

def pieceValid (s f : Flag) (lo : Nat) (p : BandPiece) : Bool :=
  let last := p.stop-1
  decide (lo < p.stop ∧ (last+1)*f.t ≤ s.t ∧ (last+1)*f.y ≤ s.y ∧ (last+1)*f.r ≤ s.r) &&
  (pieceFitsAt p s f lo && pieceFitsAt p s f last)

private abbrev Line := Int × Int

private def lineEval (a : Line) (j : Nat) : Int := a.1+a.2*j
private def lineConstAdd (a : Line) (b : Int) : Line := (a.1+b,a.2)
private def lineSub (a b : Line) : Line := (a.1-b.1,a.2-b.2)

private theorem line_le_of_endpoints (a b : Line) (i last : Nat) (hi : i ≤ last)
    (h0 : lineEval a 0 ≤ lineEval b 0) (h1 : lineEval a last ≤ lineEval b last) :
    lineEval a i ≤ lineEval b i := by
  unfold lineEval at *
  simp only [Nat.cast_zero,mul_zero,add_zero] at h0
  have his : (i : Int) ≤ (last : Int) := by exact_mod_cast hi
  by_cases hs : a.2 ≤ b.2
  · exact add_le_add h0 (mul_le_mul_of_nonneg_right hs (by positivity))
  · have hz : b.2 ≤ a.2 := le_of_lt (not_le.mp hs)
    nlinarith [mul_nonneg (sub_nonneg.mpr hz) (sub_nonneg.mpr his)]

private def IsCubic (f : Nat → Int) : Prop :=
  ∃ a b c d : Int, ∀ i, f i = a+b*i+c*(i : Int)^2+d*(i : Int)^3

private theorem cubic_triple (x y z : Line) : IsCubic (fun i => lineEval x i*lineEval y i*lineEval z i) := by
  refine ⟨x.1*y.1*z.1, x.2*y.1*z.1+x.1*y.2*z.1+x.1*y.1*z.2,
    x.2*y.2*z.1+x.2*y.1*z.2+x.1*y.2*z.2,x.2*y.2*z.2,?_⟩
  intro i
  unfold lineEval
  ring

private theorem cubic_scale (c : Int) {f : Nat → Int} (h : IsCubic f) : IsCubic (fun i => c*f i) := by
  obtain ⟨a₀,a₁,a₂,a₃,ha⟩ := h
  refine ⟨c*a₀,c*a₁,c*a₂,c*a₃,?_⟩
  intro i
  dsimp only
  rw [ha]
  ring

private theorem cubic_add {f g : Nat → Int} (hf : IsCubic f) (hg : IsCubic g) :
    IsCubic (fun i => f i+g i) := by
  obtain ⟨a₀,a₁,a₂,a₃,ha⟩ := hf
  obtain ⟨b₀,b₁,b₂,b₃,hb⟩ := hg
  refine ⟨a₀+b₀,a₁+b₁,a₂+b₂,a₃+b₃,?_⟩
  intro i
  dsimp only
  rw [ha,hb]
  ring

private theorem cubic_sub {f g : Nat → Int} (hf : IsCubic f) (hg : IsCubic g) :
    IsCubic (fun i => f i-g i) := by
  simpa only [neg_one_mul, sub_eq_add_neg] using cubic_add hf (cubic_scale (-1) hg)

private theorem channelPolynomial (t m b : Line) :
    let e := lineSub m b
    let q := lineSub (lineConstAdd t 1) m
    IsCubic (fun i =>
      6*(lineEval b i+1)*(lineEval e i+1)*(lineEval t i+1) -
      3*(lineEval b i+1)*(lineEval e i+1)*lineEval e i -
      3*(lineEval e i+1)*(lineEval b i+1)*lineEval b i +
      3*(lineEval q i)*(lineEval b i+1)*lineEval b i +
      (lineEval b i+1)*lineEval b i*(lineEval b i-1)) := by
  let e := lineSub m b
  let q := lineSub (lineConstAdd t 1) m
  have h1 := cubic_scale 6 (cubic_triple (lineConstAdd b 1) (lineConstAdd e 1) (lineConstAdd t 1))
  have h2 := cubic_scale 3 (cubic_triple (lineConstAdd b 1) (lineConstAdd e 1) e)
  have h3 := cubic_scale 3 (cubic_triple (lineConstAdd e 1) (lineConstAdd b 1) b)
  have h4 := cubic_scale 3 (cubic_triple q (lineConstAdd b 1) b)
  have h5 := cubic_triple (lineConstAdd b 1) b (lineConstAdd b (-1))
  have hc := cubic_add (cubic_add (cubic_sub (cubic_sub h1 h2) h3) h4) h5
  unfold IsCubic at hc ⊢
  obtain ⟨a₀,a₁,a₂,a₃,ha⟩ := hc
  refine ⟨a₀,a₁,a₂,a₃,?_⟩
  intro i
  dsimp only [e,q,lineEval,lineSub,lineConstAdd] at ha ⊢
  linear_combination ha i

private def bandLine (source target lo : Nat) : Line :=
  ((source : Int)-((lo : Int)+1)*target,-(target : Int))

private theorem bandLine_eq (source target lo i : Nat) (h : (lo+i+1)*target ≤ source) :
    ((source-(lo+i+1)*target : Nat) : Int) = lineEval (bandLine source target lo) i := by
  rw [Nat.cast_sub h]
  push_cast
  unfold lineEval bandLine
  ring


private theorem selected_min_eq (left right : Nat → Nat) (a b : Line) (useRight : Bool) (last : Nat)
    (ha : ∀ i ≤ last, (left i : Int) = lineEval a i) (hb : ∀ i ≤ last, (right i : Int) = lineEval b i)
    (h0 : if useRight then right 0 ≤ left 0 else left 0 ≤ right 0)
    (h1 : if useRight then right last ≤ left last else left last ≤ right last)
    (i : Nat) (hi : i ≤ last) : min (left i) (right i) = if useRight then right i else left i := by
  cases useRight
  · simp only [Bool.false_eq_true, ite_false] at h0 h1 ⊢
    apply min_eq_left
    have h₀ : lineEval a 0 ≤ lineEval b 0 := by
      rw [← ha 0 (Nat.zero_le _), ← hb 0 (Nat.zero_le _)]
      exact_mod_cast h0
    have h₁ : lineEval a last ≤ lineEval b last := by
      rw [← ha last le_rfl, ← hb last le_rfl]
      exact_mod_cast h1
    have h := line_le_of_endpoints a b i last hi h₀ h₁
    rw [← ha i hi, ← hb i hi] at h
    exact_mod_cast h
  · simp only [ite_true] at h0 h1 ⊢
    apply min_eq_right
    have h₀ : lineEval b 0 ≤ lineEval a 0 := by
      rw [← ha 0 (Nat.zero_le _), ← hb 0 (Nat.zero_le _)]
      exact_mod_cast h0
    have h₁ : lineEval b last ≤ lineEval a last := by
      rw [← ha last le_rfl, ← hb last le_rfl]
      exact_mod_cast h1
    have h := line_le_of_endpoints b a i last hi h₀ h₁
    rw [← ha i hi, ← hb i hi] at h
    exact_mod_cast h

private theorem piece_channel_cubic (s f : Flag) (lo : Nat) (p : BandPiece)
    (hp : pieceValid s f lo p = true) :
    ∃ a b c d : Int, ∀ i < p.stop-lo, 6*(bandChannel s f (lo+i) : Int) =
      a+b*i+c*(i : Int)^2+d*(i : Int)^3 := by
  simp only [pieceValid, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨hspan,hcapT,hcapV,hcapS⟩,hlo,hhi⟩ := hp
  let last := p.stop-lo-1
  have hEnd : lo+last = p.stop-1 := by dsimp only [last]; omega
  have hStep (i : Nat) (hi : i ≤ last) : lo+i+1 ≤ p.stop-1+1 := by omega
  let g (i : Nat) := bandCoordinate s f (lo+i)
  let tx := bandLine s.t f.t lo
  let vx := bandLine s.y f.y lo
  let rx := bandLine s.r f.r lo
  let mx := pieceMid p tx vx
  let bx := pieceLow p mx rx
  have hT (i : Nat) (hi : i ≤ last) : ((g i).t : Int) = lineEval tx i :=
    bandLine_eq _ _ _ _ ((Nat.mul_le_mul_right _ (hStep i hi)).trans hcapT)
  have hV (i : Nat) (hi : i ≤ last) : ((g i).y : Int) = lineEval vx i :=
    bandLine_eq _ _ _ _ ((Nat.mul_le_mul_right _ (hStep i hi)).trans hcapV)
  have hS (i : Nat) (hi : i ≤ last) : ((g i).r : Int) = lineEval rx i :=
    bandLine_eq _ _ _ _ ((Nat.mul_le_mul_right _ (hStep i hi)).trans hcapS)
  let m (i : Nat) := pieceMid p (g i).t (g i).y
  let b (i : Nat) := pieceLow p (m i) (g i).r
  have hFit0 : (if p.middleIsValue then (g 0).y ≤ (g 0).t else (g 0).t ≤ (g 0).y) ∧
      (if p.minimumIsSlope then (g 0).r ≤ m 0 else m 0 ≤ (g 0).r) := by
    simpa only [g,m,Nat.add_zero,pieceFitsAt,decide_eq_true_eq] using hlo
  have hFit1 : (if p.middleIsValue then (g last).y ≤ (g last).t else (g last).t ≤ (g last).y) ∧
      (if p.minimumIsSlope then (g last).r ≤ m last else m last ≤ (g last).r) := by
    simpa only [g,m,hEnd,pieceFitsAt,decide_eq_true_eq] using hhi
  have hM (i : Nat) (hi : i ≤ last) : min (g i).t (g i).y = m i :=
    selected_min_eq _ _ tx vx p.middleIsValue last hT hV hFit0.1 hFit1.1 i hi
  have hMcast (i : Nat) (hi : i ≤ last) : (m i : Int) = lineEval mx i := by
    dsimp only [m,mx,pieceMid]
    split <;> first | exact hV i hi | exact hT i hi
  have hB (i : Nat) (hi : i ≤ last) : min (g i).r (m i) = b i := by
    rw [min_comm]
    exact selected_min_eq _ _ mx rx p.minimumIsSlope last hMcast hS hFit0.2 hFit1.2 i hi
  have hBcast (i : Nat) (hi : i ≤ last) : (b i : Int) = lineEval bx i := by
    dsimp only [b,bx,pieceLow]
    split <;> first | exact hS i hi | exact hMcast i hi
  obtain ⟨a₀,a₁,a₂,a₃,hP⟩ := channelPolynomial tx mx bx
  refine ⟨a₀,a₁,a₂,a₃,?_⟩
  intro i hi
  have hil : i ≤ last := by dsimp only [last]; omega
  have hbM : b i ≤ m i := (hB i hil) ▸ min_le_right (g i).r (m i)
  have he : ((m i-b i : Nat) : Int) = lineEval (lineSub mx bx) i := by
    rw [Nat.cast_sub hbM,hMcast i hil,hBcast i hil]
    unfold lineEval lineSub
    ring
  have hk := hP i
  change 6*(fastChannelCount (g i).t (g i).y (g i).r : Int) = _
  rw [fastChannelCount_scaled _ _ _ _ _ (hM i hil) (hB i hil)]
  rw [hT i hil,hMcast i hil,hBcast i hil,he]
  simp only [lineEval,lineSub,lineConstAdd] at hk ⊢
  linear_combination hk

def bandPiecesValid (s f : Flag) (lo : Nat) : List BandPiece → Bool
  | [] => decide (lo = bandFuel s f)
  | p::ps => pieceValid s f lo p && bandPiecesValid s f p.stop ps

def bandPiecesValue (s f : Flag) (lo : Nat) : List BandPiece → Int
  | [] => 0
  | p::ps => cubicIntervalSum (fun j => (bandChannel s f j : Int)) lo p.stop +
      bandPiecesValue s f p.stop ps

private theorem bandPiecesValue_exact (s f : Flag) (lo : Nat) (ps : List BandPiece)
    (h : bandPiecesValid s f lo ps = true) : lo ≤ bandFuel s f ∧ bandPiecesValue s f lo ps =
      ∑ i ∈ Finset.range (bandFuel s f-lo), (bandChannel s f (lo+i) : Int) := by
  induction ps generalizing lo with
  | nil =>
    have hl : lo = bandFuel s f := by simpa [bandPiecesValid] using h
    refine ⟨hl.le,?_⟩
    simp [bandPiecesValue,hl]
  | cons p rest ih =>
    simp only [bandPiecesValid,Bool.and_eq_true] at h
    have hspan : lo < p.stop := by
      have hraw := h.1
      simp only [pieceValid,Bool.and_eq_true,decide_eq_true_eq] at hraw
      exact hraw.1.1
    obtain ⟨hrest,hvalue⟩ := ih p.stop h.2
    refine ⟨hspan.le.trans hrest,?_⟩
    rw [bandPiecesValue,hvalue,
      cubicIntervalSum_eq_sum _ _ _ 6 (by decide) (piece_channel_cubic s f lo p h.1)]
    have hsplit : bandFuel s f-lo = (p.stop-lo)+(bandFuel s f-p.stop) := by omega
    rw [hsplit, Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [show lo+(p.stop-lo+i)=p.stop+i by omega]

theorem bandCovers_of_pieces (s f : Flag) (gap : Nat) (ps : List BandPiece)
    (hOk : bandPiecesValid s f 0 ps = true)
    (hCost : (flowWidth : Int)*bandPiecesValue s f 0 ps < (gap : Int)) :
    bandCovers s f gap = true := by
  have hvalue := (bandPiecesValue_exact s f 0 ps hOk).2
  simp only [Nat.sub_zero,Nat.zero_add] at hvalue
  unfold bandCovers
  rw [decide_eq_true_eq,bandBudget_eq_sum_channels]
  rw [hvalue] at hCost
  exact_mod_cast hCost

end ProximityPrize.SubmissionLower.Koala6844Receipts
