import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice

namespace ProximityPrize.SubmissionLower.Koala6844Receipts
set_option autoImplicit false

def receiptBase (f : Flag) (src : Sources) : Option Nat := do
  let L := src.totalCap
  if !wellOrdered f || !(f.y ≤ L ∧ L < f.t ∧ L + f.y ≤ f.t) then none else
    let long ← longRates f src
    let short := shortRates ⟨f.r, f.y, L⟩
    return max (long.bill f) (short.bill ⟨f.r, f.y, L⟩)

def receiptRow (f : Flag) (src : Sources) (best i : Nat) : Option Nat :=
  let r := i+1
  (List.range (f.y-r)).foldlM (fun acc dy => splitCharge f src src.totalCap r (r+dy) acc) best

private def foldedWindow (f : Flag) (src : Sources) (first len best : Nat) : Option Nat :=
  (List.range len).foldlM (fun acc i => receiptRow f src acc (first+i)) best

namespace TerminalPriceEval

private def graphDirectionClosed (f : Flag) : FlagIncrements :=
  let lam := 44119822827635343360
  let rho := 610516168402140
  ⟨2 * lam * (f.t - f.y) + 18864897752627166240,
    2 * lam * (f.y - f.r) + rho, 2 * lam * (f.r - 1)⟩

private theorem graphDirectionClosed_eq (f : Flag) : graphDirectionClosed f = graphDirection f := by
  rfl

private def graphIdentityClosed (g : Flag) : FlagIncrements :=
  let a := g.r - 3
  let b := g.y - g.r - 2
  let c := g.t - g.y
  let factor := 49566586680232942320
  ⟨factor * (655365 + 262146 * a), factor * (1310730 + 524292 * a),
    factor * (2097170 + 524292 * a + 524292 * b + 262146 * c)⟩

private theorem graphIdentityClosed_eq (g : Flag) : graphIdentityClosed g = graphIdentity g := by
  rfl

private def graphBasisClosed (g : Flag) : FlagIncrements :=
  let n := graphNormal g
  let c₀ := graphFirstCut g 0
  let c₁ := graphFirstCut g 1
  let c₂ := graphFirstCut g 2
  ⟨(n.middle*c₁.slope+n.slope*(c₂.slope+c₂.middle))*77453555339160,
    (n.total*c₀.slope+n.middle*c₁.slope+n.slope*(c₂.slope+c₂.middle+c₂.total))*77453555339160,
    (n.total*(c₀.slope+c₀.middle)+n.middle*(c₁.slope+c₁.middle+c₁.total)+
      n.slope*(c₂.slope+c₂.middle+c₂.total))*77453555339160⟩

private theorem graphBasisClosed_eq (g : Flag) : graphBasisClosed g = graphBasis g := by
  have h : graphScale / 3 = 77453555339160 := rfl
  simp [graphBasisClosed, graphBasis, FlagIncrements.map, mixedRate, axisFlag, h]

private def graphMoveClosed (j : Nat) (d : FlagIncrements) (u : Nat) : FlagIncrements :=
  if j = 0 then ⟨0, u*d.slope, u*(d.slope+d.middle)⟩
  else if j = 1 then ⟨u*d.slope, u*d.slope, u*(d.slope+d.middle+d.total)⟩
  else ⟨u*(d.slope+d.middle), u*(d.slope+d.middle+d.total), u*(d.slope+d.middle+d.total)⟩

private theorem graphMoveClosed_eq (j : Nat) (d : FlagIncrements) (u : Nat) :
    graphMoveClosed j d u = FlagIncrements.map (fun i => u * mixedRate i (axisFlag j) d) := by
  by_cases h : j = 0 <;> by_cases k : j = 1 <;>
    simp [graphMoveClosed, FlagIncrements.map, mixedRate, axisFlag, h, k, Nat.add_comm]
private def graphChargeClosed (_f g : Flag) (src : SourceShape) (j : Nat) : Option GraphCharge :=
  let right := src.carrierFlag
  let helper := helperFlag g src
  if pairGate g right && pairGate g helper then
    let normal := (graphNormal g).axis j
    let raw := (graphRaw g).axis j
    let weight := (524288 * normal + 3 * 65539 * raw) * 77453555339160
    let move := graphMoveClosed j src.graphIncrement (weight / (src.k + 1))
    let dir := graphDirectionClosed g
    some ⟨move, graphPairRates right dir, graphPairRates helper dir⟩
  else none

private theorem graphChargeClosed_eq (f g : Flag) (src : SourceShape) (j : Nat) : graphChargeClosed f g src j = graphCharge f g src j := by
  have h : graphScale / 3 = 77453555339160 := rfl
  simp only [graphChargeClosed, graphCharge, graphMoveClosed_eq, graphDirectionClosed_eq, h]

private def parameterFlag (a b c : Nat) : Flag :=
  ⟨a+3, a+3+(b+2), a+3+(b+2)+c⟩

private theorem pad_parameter (f : Flag) :
    padFlag f = parameterFlag ((padFlag f).r-3) ((padFlag f).y-(padFlag f).r-2)
      ((padFlag f).t-(padFlag f).y) := by
  cases f with
  | mk r y t =>
    dsimp [parameterFlag,padFlag]
    congr 1 <;> omega

private def directRawRates (g : Flag) : FlagIncrements :=
  let moving : FlagIncrements := ⟨g.t - g.y, g.y - g.r, g.r + 1⟩
  FlagIncrements.map fun i =>
    mixedRate i (earlyCut g) (normalCut g) + 65539 * mixedRate i moving (rawMovingCut g)

private theorem early_param (a b c : Nat) : earlyCut (parameterFlag a b c) =
    ⟨262144*c, 1+262144*(b+2), 262144*(a+2)⟩ := by
  simp [parameterFlag,earlyCut,degree] <;> omega

private theorem normal_param (a b c : Nat) : normalCut (parameterFlag a b c) =
    ⟨131074*c, 131074*b+131076, 131074*(a+2)⟩ := by
  simp [parameterFlag,normalCut,degree,Nat.add_assoc] <;> omega

private theorem moving_param (a b c : Nat) : rawMovingCut (parameterFlag a b c) =
    ⟨131074*c, 131074*(b+2), 131074*a+393221⟩ := by
  simp [parameterFlag,rawMovingCut,degree,Nat.add_assoc] <;> omega

private theorem id_param (a b c : Nat) : rawIdentity (parameterFlag a b c) =
    ⟨393219+262146*(a+1), 786438+524292*(a+1),
      1048586+262146*c+524292*(b+1)+524292*(a+1)⟩ := by
  simp [parameterFlag,rawIdentity] <;> omega

private def rawPolynomial (a b c : Nat) : FlagIncrements :=
  ⟨566955475086 + 335017476161*a + 42950721542*(a*a) + 197574197287*b + 85901443084*(a*b),
   566955475086 + 335017476161*a + 42950721542*(a*a) + 197574197287*b + 85901443084*(a*b) + 197574197287*c + 85901443084*(a*c),
   670039015594 + 335017476161*a + 42950721542*(a*a) + 335017476161*b + 42950721542*(b*b) + 85901443084*(a*b) + 335017476161*c + 85901443084*(a*c) + 85901443084*(b*c)⟩

private theorem rates_param (a b c : Nat) : directRawRates (parameterFlag a b c) = rawPolynomial a b c := by
  simp only [directRawRates, early_param, normal_param, moving_param]
  simp [mixedRate, FlagIncrements.map, parameterFlag, rawPolynomial]
  refine ⟨?_, ?_, ?_⟩ <;> grind only

private theorem gate_param (a b c : Nat) :
    (rawIdentity (parameterFlag a b c)).all (fun i cost =>
      decide ((nodes-degree)*pencilLimit*cost ≤ agreementGap*(rawPolynomial a b c).axis i)) = true := by
  rw [id_param]
  simp [FlagIncrements.all, FlagIncrements.axis, nodes,degree,pencilLimit,errorsAllowed,agreements,agreementGap,rawPolynomial]
  constructor
  · constructor
    · calc
        _ ≤ _ + (21309038318445936 + 13923040811089942*a + 2142639694844212*(a*a) + 9856186405859282*b + 4285279389688424*(a*b)) := Nat.le_add_right _ _
        _ = _ := by grind only
    · calc
        _ ≤ _ + (14334935806751676 + 11133399806412238*a + 2142639694844212*(a*a) + 9856186405859282*b + 4285279389688424*(a*b) + 9856186405859282*c + 4285279389688424*(a*c)) := Nat.le_add_right _ _
        _ = _ := by grind only
  · calc
      _ ≤ _ + (11108417011391204 + 11133399806412238*a + 2142639694844212*(a*a) + 11133399806412238*b + 2142639694844212*(b*b) + 4285279389688424*(a*b) + 13923040811089942*c + 4285279389688424*(a*c) + 4285279389688424*(b*c)) := Nat.le_add_right _ _
      _ = _ := by grind only

private def rawFast (f : Flag) : Option FlagIncrements :=
  let g := padFlag f
  if rawGeometryGate f then some (rawPolynomial (g.r-3) (g.y-g.r-2) (g.t-g.y)) else none

private theorem rawFast_eq (f : Flag) : rawFast f = rawGeometryRates f := by
  let g := padFlag f
  let a := g.r-3
  let b := g.y-g.r-2
  let c := g.t-g.y
  have hp : g = parameterFlag a b c := pad_parameter f
  change (if rawGeometryGate f then some (rawPolynomial a b c) else none) =
    (if rawGeometryGate f && (rawIdentity g).all (fun i cost => decide
        ((nodes - degree) * pencilLimit * cost ≤ agreementGap * (directRawRates g).axis i)) then
      some (directRawRates g) else none)
  rw [hp, rates_param, gate_param]
  simp
private def Increasing (f : Nat → Nat) : Prop := f 0 ≤ f 1 ∧ f 1 ≤ f 2
private def Ordered (f : FlagIncrements) : Prop := f.total ≤ f.middle ∧ f.middle ≤ f.slope

private theorem increasing_add {f g : Nat → Nat} (h : Increasing f) (k : Increasing g) :
    Increasing (fun i => f i + g i) :=
  ⟨Nat.add_le_add h.1 k.1, Nat.add_le_add h.2 k.2⟩
private theorem increasing_max {f g : Nat → Nat} (h : Increasing f) (k : Increasing g) :
    Increasing (fun i => max (f i) (g i)) :=
  by simp only [Increasing] at *; omega
private theorem increasing_lmul (a : Nat) {f : Nat → Nat} (h : Increasing f) :
    Increasing (fun i => a * f i) :=
  ⟨Nat.mul_le_mul_left a h.1, Nat.mul_le_mul_left a h.2⟩
private theorem increasing_rmul (a : Nat) {f : Nat → Nat} (h : Increasing f) :
    Increasing (fun i => f i * a) :=
  ⟨Nat.mul_le_mul_right _ h.1, Nat.mul_le_mul_right _ h.2⟩
private theorem ordered_map {f : Nat → Nat} (h : Increasing f) : Ordered (FlagIncrements.map f) := h
private theorem increasing_axis {f : FlagIncrements} (h : Ordered f) : Increasing f.axis := h
private theorem increasing_mixed (f g : FlagIncrements) : Increasing (fun i => mixedRate i f g) := by
  simp [Increasing, mixedRate] <;> omega

private theorem ordered_basis (g : Flag) : Ordered (graphBasis g) := by
  apply ordered_map
  apply increasing_rmul
  apply increasing_add
  · apply increasing_add <;> apply increasing_lmul <;> apply increasing_mixed
  · apply increasing_lmul <;> apply increasing_mixed

private theorem ordered_identity (g : Flag) : Ordered (graphIdentity g) := by
  dsimp [graphIdentity, Ordered]
  constructor <;> apply Nat.mul_le_mul_left <;> omega

private theorem ordered_charge (f g : Flag) (s : SourceShape) (j : Nat) (c : GraphCharge)
    (hc : graphCharge f g s j = some c) : Ordered c.move ∧ Ordered c.lead ∧ Ordered c.helper := by
  unfold graphCharge at hc
  dsimp only at hc
  split at hc
  · simp only [Option.some.injEq] at hc
    subst c
    refine ⟨ordered_map (increasing_lmul _ (increasing_mixed _ _)), ?_, ?_⟩
    all_goals exact ordered_map (increasing_mixed _ _)
  · contradiction

private def graphNumer (g : Flag) (x y z : GraphCharge) :=
  let basis := graphBasis g
  let identity := graphIdentity g
  FlagIncrements.map fun i =>
    let graph := x.lead.axis i + y.lead.axis i + z.lead.axis i +
      max (identity.axis i) (basis.axis i + x.move.axis i + y.move.axis i + z.move.axis i)
    max graph (max (x.helper.axis i) (max (y.helper.axis i) (z.helper.axis i)))

private theorem ordered_numer (g : Flag) (x y z : GraphCharge)
    (hx : Ordered x.move ∧ Ordered x.lead ∧ Ordered x.helper)
    (hy : Ordered y.move ∧ Ordered y.lead ∧ Ordered y.helper)
    (hz : Ordered z.move ∧ Ordered z.lead ∧ Ordered z.helper) :
    Ordered (graphNumer g x y z) := by
  apply ordered_map
  apply increasing_max
  · apply increasing_add
    · exact increasing_add (increasing_add (increasing_axis hx.2.1) (increasing_axis hy.2.1)) (increasing_axis hz.2.1)
    · apply increasing_max (increasing_axis (ordered_identity g))
      exact increasing_add (increasing_add (increasing_add (increasing_axis (ordered_basis g)) (increasing_axis hx.1)) (increasing_axis hy.1)) (increasing_axis hz.1)
  · exact increasing_max (increasing_axis hx.2.2) (increasing_max (increasing_axis hy.2.2) (increasing_axis hz.2.2))

private def uncheckedLong (f : Flag) (src : Sources) : Option Rates := do
  let g := padFlag f 2
  if !goodGraph g then none else
    let x ← graphCharge f g src.z 0
    let y ← graphCharge f g src.yz 1
    let z ← graphCharge f g src.all 2
    return ⟨graphNumer g x y z, graphScale⟩

private theorem uncheckedLong_eq (f : Flag) (s : Sources) : uncheckedLong f s = longRates f s := by
  unfold longRates uncheckedLong
  dsimp only
  split
  · rfl
  · cases hx : graphCharge f (padFlag f 2) s.z 0 with
    | none => rfl
    | some x =>
      cases hy : graphCharge f (padFlag f 2) s.yz 1 with
      | none => rfl
      | some y =>
        cases hz : graphCharge f (padFlag f 2) s.all 2 with
        | none => rfl
        | some z =>
          have h := ordered_numer (padFlag f 2) x y z (ordered_charge _ _ _ _ _ hx)
            (ordered_charge _ _ _ _ _ hy) (ordered_charge _ _ _ _ _ hz)
          change some _ = if (graphNumer (padFlag f 2) x y z).total ≤ (graphNumer (padFlag f 2) x y z).middle ∧ (graphNumer (padFlag f 2) x y z).middle ≤ (graphNumer (padFlag f 2) x y z).slope then _ else _
          unfold Ordered at h
          simp only [h]
          rfl

private def Small (f : Flag) : Prop :=
  1 ≤ f.r ∧ f.r ≤ f.y ∧ f.y ≤ f.t ∧ f.r ≤ 20 ∧ f.y ≤ 100 ∧ f.t ≤ 4000

private def Padded (g : Flag) : Prop :=
  3 ≤ g.r ∧ g.r + 2 ≤ g.y ∧ g.y ≤ g.t ∧ g.r ≤ 20 ∧ g.y ≤ 100 ∧ g.t ≤ 4000

private theorem padded_small (f : Flag) (e : Nat) (he : e ≤ 2) (hf : Small f) :
    Padded (padFlag f e) := by
  simp only [Padded, Small, padFlag] at *
  omega

private theorem validGraph (g : Flag) (hg : Padded g) : goodGraph g = true := by
  have ⟨hr, hd, _, hur, huy, hut⟩ := hg
  have wt := Nat.mul_le_mul (show 2*g.t ≤ 2*4000 by omega) (show g.t+1 ≤ 4001 by omega)
  have e1 := Nat.mul_le_mul hur (show 1+262144*(g.y-g.r) ≤ 1+262144*100 by omega)
  have e2 := Nat.mul_le_mul huy (show 262144*(g.r-1) ≤ 262144*19 by omega)
  have d1 := Nat.mul_le_mul hur (show (2*(g.y-g.r)-1)*131071+1 ≤ 199*131071+1 by omega)
  have d2 := Nat.mul_le_mul huy (show 2*g.r-1 ≤ 39 by omega)
  have d3 := Nat.mul_le_mul_right 131071 d2
  unfold goodGraph
  apply decide_eq_true
  simp only [earlyCut, pencilLimit, errorsAllowed, nodes, degree, agreements,
    normalCut, prime, show 2*(131071+1) = 262144 by decide]
  omega

private theorem validRawGate (f : Flag) (hf : Small f) : rawGeometryGate f = true := by
  have hg := validGraph _ (padded_small f 0 (by decide) hf)
  have horder : wellOrdered f = true := by
    simp only [wellOrdered, decide_eq_true_eq]
    exact ⟨hf.1, hf.2.1, hf.2.2.1⟩
  simp only [rawGeometryGate, horder, Bool.true_and, decide_eq_true_eq]
  simp only [goodGraph, decide_eq_true_eq] at hg
  exact ⟨hg.2.1, hg.2.2.1, hg.2.2.2.2, hg.2.2.2.1⟩

private def ProfileSmall (src : SourceShape) : Prop :=
  src.B ≤ 150 ∧ src.U ≤ 400 ∧ src.L + src.q ≤ 4000 ∧ src.s ≤ 64

private theorem validPairGate (g p : Flag) (hg : Padded g)
    (hr : p.r ≤ 1500) (hy : p.y ≤ 7000) (ht : p.t ≤ 260000) : pairGate g p = true := by
  have ⟨_,_,_,gr,gy,gt⟩ := hg
  have h1 := Nat.mul_le_mul gr ht
  have h2 := Nat.mul_le_mul gt hr
  have h3 := Nat.mul_le_mul gy ht
  have h4 := Nat.mul_le_mul gt hy
  have h5 := Nat.mul_le_mul gy hr
  have h6 := Nat.mul_le_mul gr hy
  unfold pairGate
  apply decide_eq_true
  unfold prime
  omega

private theorem sourceTests (g : Flag) (s : SourceShape) (hg : Padded g) (hs : ProfileSmall s) :
    (pairGate g s.carrierFlag && pairGate g (helperFlag g s)) = true := by
  have ⟨gr,gd,gord,hr,hy,ht⟩ := hg
  obtain ⟨sr,sy,st,ss⟩ := hs
  have h1 := Nat.mul_le_mul ss (show g.r-1 ≤ 19 by omega)
  have h2 := Nat.mul_le_mul ss (show g.y-1 ≤ 99 by omega)
  have h3 := Nat.mul_le_mul ss (show g.t-1 ≤ 3999 by omega)
  simp only [Bool.and_eq_true]
  constructor
  · apply validPairGate _ _ hg <;> dsimp [SourceShape.carrierFlag] <;> omega
  · apply validPairGate _ _ hg <;> dsimp [helperFlag,SourceShape.carrierFlag] <;> omega
private def rawShort (f : Flag) : FlagIncrements :=
  let g := padFlag f
  rawPolynomial (g.r-3) (g.y-g.r-2) (g.t-g.y)

private theorem shortSmall_eq (f : Flag) (hf : Small f) :
    shortRates f = ⟨rawShort f,1⟩ := by
  simp only [shortRates, ← rawFast_eq, rawFast, validRawGate f hf]
  rfl

private def directCharge (g : Flag) (src : SourceShape) (j : Nat) : GraphCharge :=
  let normal := (graphNormal g).axis j
  let raw := (graphRaw g).axis j
  let weight := (524288 * normal + 3 * 65539 * raw) * 77453555339160
  let move := graphMoveClosed j src.graphIncrement (weight / (src.k + 1))
  let dir := graphDirectionClosed g
  ⟨move, graphPairRates src.carrierFlag dir, graphPairRates (helperFlag g src) dir⟩

private theorem directCharge_eq (f g : Flag) (src : SourceShape) (j : Nat)
    (hg : Padded g) (hs : ProfileSmall src) :
    graphCharge f g src j = some (directCharge g src j) := by
  rw [← graphChargeClosed_eq]
  simp only [graphChargeClosed, sourceTests g src hg hs, ite_true, directCharge]

private def directLong (g : Flag) (s : Sources) : FlagIncrements :=
  let x := directCharge g s.z 0
  let y := directCharge g s.yz 1
  let z := directCharge g s.all 2
  let basis := graphBasisClosed g
  let identity := graphIdentityClosed g
  FlagIncrements.map fun i =>
    let graph := x.lead.axis i + y.lead.axis i + z.lead.axis i +
      max (identity.axis i) (basis.axis i + x.move.axis i + y.move.axis i + z.move.axis i)
    max graph (max (x.helper.axis i) (max (y.helper.axis i) (z.helper.axis i)))

private def GoodSources (s : Sources) : Prop :=
  ProfileSmall s.z ∧ ProfileSmall s.yz ∧ ProfileSmall s.all

private theorem directLong_eq (f : Flag) (s : Sources) (hf : Small f) (hs : GoodSources s) :
    longRates f s = some ⟨directLong (padFlag f 2) s, 232360666017480⟩ := by
  have hg := padded_small f 2 (by decide) hf
  rw [← uncheckedLong_eq]
  simp only [uncheckedLong, validGraph _ hg, Bool.not_true, Bool.false_eq_true, ite_false,
    directCharge_eq _ _ _ _ hg hs.1, directCharge_eq _ _ _ _ hg hs.2.1,
    directCharge_eq _ _ _ _ hg hs.2.2, pure, graphNumer, directLong,
    graphBasisClosed_eq, graphIdentityClosed_eq]
  rfl

private def Domain (f : Flag) (s : Sources) : Prop :=
  Small f ∧ GoodSources s ∧ f.y ≤ s.totalCap ∧ s.totalCap + f.y ≤ f.t

private instance (f : Flag) (s : Sources) : Decidable (Domain f s) := by
  unfold Domain Small GoodSources ProfileSmall
  infer_instance

private def dotBase (v : FlagIncrements) (r y : Nat) : Nat :=
  (y-r)*v.middle + r*v.slope

private def cellPrice (f : Flag) (src : Sources) (L r y best : Nat) : Nat :=
  let oy := f.y-y
  let orr := min oy (f.r-r)
  let s := rawShort ⟨r,y,L⟩
  let o := rawShort ⟨min orr y,min oy y,L⟩
  let v := directLong (padFlag ⟨orr,oy,f.t⟩ 2) src
  let z := dotBase s r y
  let u := dotBase o orr oy
  let w := dotBase v orr oy
  let endT := f.t-(L+1)
  let d := 232360666017480
  let b₀ := z + ((f.t-y-oy)*o.total + u)
  let b₁ := (L-y)*s.total + z + ((f.t-L-oy)*o.total + u)
  let c₀ := z + ((f.t-y-oy)*v.total + w + d - 1)/d
  let c₁ := (endT-y)*s.total + z + ((f.t-endT-oy)*v.total + w + d - 1)/d
  max (max best (max b₀ b₁)) (max c₀ c₁)

private theorem cellPrice_eq (f : Flag) (src : Sources) (L r y best : Nat)
    (hD : Domain f src) (hL : L = src.totalCap) (hr : 1 ≤ r) (hR : r < f.r)
    (hry : r ≤ y) (hy : y < f.y) :
    splitCharge f src L r y best = some (cellPrice f src L r y best) := by
  obtain ⟨hF,hS,hY,hT⟩ := hD
  obtain ⟨hr₀,hry₀,hyt₀,hru,hyu,htu⟩ := hF
  let oy := f.y-y
  let orr := min oy (f.r-r)
  have hs : Small ⟨r,y,L⟩ := by dsimp [Small]; omega
  have ho : Small ⟨min orr y,min oy y,L⟩ := by dsimp [Small,orr,oy]; omega
  have hv : Small ⟨orr,oy,f.t⟩ := by dsimp [Small,orr,oy]; omega
  have hupper : min L (f.t-oy) = L := by dsimp [oy]; omega
  have hlower : max (L+1) oy = L+1 := by dsimp [oy]; omega
  have hvalid : y ≤ f.t-(L+1) := by omega
  unfold splitCharge cellPrice
  dsimp only at *
  dsimp only [orr, oy] at ho hv hupper hlower
  simp only [hupper, hlower, ite_eq_left (show y ≤ L by omega), ite_eq_left hvalid,
    shortSmall_eq _ hs, shortSmall_eq _ ho, directLong_eq _ _ hv hS,
    shortSplitCharge, Rates.bill, Flag.increments, dot, dotBase, Nat.sub_self, Nat.zero_mul,
    Nat.zero_add, Nat.add_sub_cancel, Nat.div_one]
  simp only [Nat.add_assoc]
  rfl

private def pricedRow (f : Flag) (src : Sources) (best i : Nat) : Nat :=
  let r := i+1
  (List.range (f.y-r)).foldl (fun acc dy => cellPrice f src src.totalCap r (r+dy) acc) best

private def pricedWindow (f : Flag) (src : Sources) (first len best : Nat) : Nat :=
  (List.range len).foldl (fun acc i => pricedRow f src acc (first+i)) best

private theorem foldPriced {α : Type} (xs : List α) (step : Nat → α → Option Nat)
    (fast : Nat → α → Nat) (b : Nat)
    (hem : ∀ x ∈ xs, ∀ a, step a x = some (fast a x)) :
    xs.foldlM step b = some (xs.foldl fast b) := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldlM_cons, List.foldl_cons, hem x (by simp) b]
    exact ih _ fun y mem => hem y (by simp [mem])

private theorem pricedRow_eq (f : Flag) (s : Sources) (b i : Nat)
    (hd : Domain f s) (hi : i+1 < f.r) :
    receiptRow f s b i = some (pricedRow f s b i) := by
  unfold receiptRow pricedRow
  apply foldPriced
  intro dy hdy a
  have hh := List.mem_range.mp hdy
  apply cellPrice_eq _ _ _ _ _ _ hd rfl <;> omega

private theorem pricedWindow_eq (f : Flag) (s : Sources) (a n b : Nat)
    (hd : Domain f s) (hn : a+n < f.r) :
    foldedWindow f s a n b = some (pricedWindow f s a n b) := by
  unfold foldedWindow pricedWindow
  apply foldPriced
  intro i hi acc
  apply pricedRow_eq _ _ _ _ hd
  have hh := List.mem_range.mp hi
  omega

end TerminalPriceEval

def receiptWindow (f : Flag) (src : Sources) (first len best : Nat) : Option Nat :=
  if TerminalPriceEval.Domain f src ∧ first+len < f.r then
    some (TerminalPriceEval.pricedWindow f src first len best)
  else foldedWindow f src first len best

private theorem receiptWindow_eq_folded (f : Flag) (s : Sources) (a n : Nat) :
    receiptWindow f s a n = foldedWindow f s a n := by
  funext b
  unfold receiptWindow
  split
  · rename_i h
    exact (TerminalPriceEval.pricedWindow_eq _ _ _ _ _ h.1 h.2).symm
  · rfl

theorem terminalPrice_as_window (f : Flag) (src : Sources) :
    terminalPrice f src = (receiptBase f src).bind (receiptWindow f src 0 (f.r-1)) := by
  simp only [receiptWindow_eq_folded]
  unfold terminalPrice receiptBase foldedWindow receiptRow
  dsimp only
  split
  · rfl
  · cases longRates f src <;> simp

theorem join_receipt_window (f : Flag) (src : Sources) (a b c x y z : Nat)
    (h₁ : receiptWindow f src a b x = some y)
    (h₂ : receiptWindow f src (a+b) c y = some z) :
    receiptWindow f src a (b+c) x = some z := by
  have hstep : receiptWindow f src a (b+c) x =
      (receiptWindow f src a b x).bind (receiptWindow f src (a+b) c) := by
    simp only [receiptWindow_eq_folded]
    unfold foldedWindow
    rw [List.range_add,List.foldlM_append]
    simp only [List.foldlM_map,Nat.add_assoc]
    rfl
  rw [hstep,h₁]
  exact h₂

theorem finish_receipt_window (f : Flag) (src : Sources) (n x y : Nat) (hn : f.r-1=n)
    (hbase : receiptBase f src = some x)
    (hwin : receiptWindow f src 0 n x = some y) : terminalPrice f src = some y := by
  rw [terminalPrice_as_window,hn,hbase]
  exact hwin

end ProximityPrize.SubmissionLower.Koala6844Receipts
