import Mathlib.Tactic
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.PlainReceiptData6815

def read92 (s : String) : ℕ := s.toList.foldl (fun n c =>
  let x := c.toNat
  92*n+(x-33-(if 34<x then 1 else 0)-(if 92<x then 1 else 0))) 0

def variableNatAux : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | 0,code,out,_ => (out,code)
  | fuel+1,code,out,scale =>
    let d := code%64
    if d<32 then (out+d*scale,code/64)
    else variableNatAux fuel (code/64) (out+(d%32)*scale) (scale*32)
def variableNat (code : ℕ) := variableNatAux 16 code 0 1

def relativeFields : List ℕ → ℕ → List ℕ × ℕ
  | [],code => ([],code)
  | p::ps,code =>
    let z := variableNat code
    let value := if z.1%2=0 then p+z.1/2 else p-z.1/2
    let rest := relativeFields ps z.2
    (value::rest.1,rest.2)

def packRelative (a b c d : ℕ) : List ℕ → ℕ
  | [hi,profile,length,delta,k,lhs,rhs] =>
    hi+a*(profile+b*(length+c*(delta+d*(k+256*lhs+65536*rhs))))
  | _ => 0

def relativeAux (a b c d : ℕ) : ℕ → List ℕ → ℕ → List ℕ
  | 0,_,_ => []
  | n+1,previous,code =>
    let f := relativeFields previous code
    packRelative a b c d f.1 :: relativeAux a b c d n f.1 f.2
def relativeData (n a b c d : ℕ) (payload : String) : List ℕ :=
  relativeAux a b c d n [0,0,0,0,0,0,0] (read92 payload)
def relativeNat (n a b c d code : ℕ) : List ℕ :=
  relativeAux a b c d n [0,0,0,0,0,0,0] code

def seriesAux : ℕ → ℕ → ℕ → ℕ → List ℕ
  | 0,_,_,_ => []
  | n+1,previous,older,code =>
    let z := variableNat code
    let prediction := 2*previous-older
    let value := if z.1%2=0 then prediction+z.1/2 else prediction-z.1/2
    value::seriesAux n value previous z.2
def series (n code : ℕ) : Array ℕ := (seriesAux n 0 0 code).toArray

end ProximityPrize.SubmissionLower.PlainReceiptData6815
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.PortfolioBoxes6815
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000

structure Point where
  s : ℕ
  b : ℕ
  u : ℕ
  t : ℕ
  deriving DecidableEq
structure Box where
  slo : ℕ
  shi : ℕ
  blo : ℕ
  bhi : ℕ
  ulo : ℕ
  uhi : ℕ
  tlo : ℕ
  thi : ℕ
  deriving DecidableEq

def Contains (a : Box) (p : Point) : Prop :=
  a.slo≤p.s ∧ p.s≤a.shi ∧ a.blo≤p.b ∧ p.b≤a.bhi ∧
  a.ulo≤p.u ∧ p.u≤a.uhi ∧ a.tlo≤p.t ∧ p.t≤a.thi
def Admissible (m : ℕ) (p : Point) : Prop :=
  m≤p.s ∧ 2≤p.s ∧ (3≤m → 5≤p.s) ∧ 2*p.s≤p.b ∧ p.s≤p.u ∧ p.b≤p.u+p.s ∧ p.u≤p.t
def Empty (a : Box) : Prop := a.shi<a.slo ∨ a.bhi<a.blo ∨ a.uhi<a.ulo ∨ a.thi<a.tlo
instance (a : Box) : Decidable (Empty a) := by unfold Empty; infer_instance

def step (m : ℕ) (a : Box) : Box :=
  let sl := max (max (max (max a.slo m) 2) (if 3≤m then 5 else 2)) (a.blo-a.uhi)
  let sh := min a.shi (a.bhi/2)
  let bl := max a.blo (2*sl)
  let bh := min a.bhi (a.uhi+sh)
  let ul := max (max a.ulo sl) (bl-sh)
  let uh := min a.uhi a.thi
  let tl := max a.tlo ul
  ⟨sl,sh,bl,bh,ul,uh,tl,a.thi⟩

def normalize (m : ℕ) : ℕ → Box → Box
  | 0,a => a
  | n+1,a => normalize m n (step m a)

theorem step_contains (m : ℕ) (a : Box) (p : Point)
    (ha : Admissible m p) (hp : Contains a p) : Contains (step m a) p := by
  unfold Admissible Contains at *
  dsimp only [step]
  split_ifs with hm <;> omega

theorem normalize_contains (m n : ℕ) (a : Box) (p : Point)
    (ha : Admissible m p) (hp : Contains a p) : Contains (normalize m n a) p := by
  induction n generalizing a with
  | zero => exact hp
  | succ n ih => exact ih (step m a) (step_contains m a p ha hp)

def coordinate (p : Point) (axis : Fin 4) : ℕ := ![p.s,p.b,p.u,p.t] axis
def lower (a : Box) (axis : Fin 4) (v : ℕ) : Box :=
  match axis.val with
  | 0 => {a with shi:=v}
  | 1 => {a with bhi:=v}
  | 2 => {a with uhi:=v}
  | _ => {a with thi:=v}
def upper (a : Box) (axis : Fin 4) (v : ℕ) : Box :=
  match axis.val with
  | 0 => {a with slo:=v+1}
  | 1 => {a with blo:=v+1}
  | 2 => {a with ulo:=v+1}
  | _ => {a with tlo:=v+1}

theorem split_contains (a : Box) (p : Point) (axis : Fin 4) (v : ℕ) (hp : Contains a p) :
    Contains (lower a axis v) p ∨ Contains (upper a axis v) p := by
  fin_cases axis <;> simp [lower,upper,Contains] at * <;> omega

def Covered (m : ℕ) (valid : Box → Prop) (a : Box) : Prop :=
  ∀ p, Admissible m p → Contains a p → ∃ b, valid b ∧ Contains b p

theorem covered_leaf (m : ℕ) (valid : Box → Prop) (a : Box) (h : valid a) : Covered m valid a := by
  intro p _ hp
  exact ⟨a,h,hp⟩
theorem covered_normalize (m : ℕ) (valid : Box → Prop) (a b : Box)
    (he : normalize m 8 a=b) (h : Covered m valid b) : Covered m valid a := by
  intro p ha hp
  apply h p ha
  rw [←he]
  exact normalize_contains m 8 a p ha hp
theorem covered_split (m : ℕ) (valid : Box → Prop) (a : Box) (axis : Fin 4) (v : ℕ)
    (hl : Covered m valid (lower a axis v)) (hh : Covered m valid (upper a axis v)) :
    Covered m valid a := by
  intro p ha hp
  rcases split_contains a p axis v hp with hp | hp
  · exact hl p ha hp
  · exact hh p ha hp

end ProximityPrize.SubmissionLower.PortfolioBoxes6815
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.PortfolioChord6815
set_option autoImplicit false
set_option maxHeartbeats 1200000

def Chord (lo hi : ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ x, lo≤x → x≤hi → (hi-lo)*f x≤(hi-x)*f lo+(x-lo)*f hi

private theorem weights (lo x hi : ℕ) (hl : lo≤x) (hh : x≤hi) :
    (hi-x)+(x-lo)=hi-lo ∧ (hi-x)*lo+(x-lo)*hi=(hi-lo)*x := by
  constructor
  · omega
  · have ha := Nat.sub_add_cancel hh
    have hb := Nat.sub_add_cancel hl
    have hc := Nat.sub_add_cancel (hl.trans hh)
    nlinarith

theorem constant (lo hi c : ℕ) : Chord lo hi (fun _ => c) := by
  intro x hl hh
  have h := (weights lo x hi hl hh).1
  rw [←Nat.add_mul,h]

theorem affine (lo hi a b : ℕ) : Chord lo hi (fun x => a*x+b) := by
  intro x hl hh
  have hw := weights lo x hi hl hh
  have ha := congrArg (fun z => a*z) hw.2
  have hb := congrArg (fun z => b*z) hw.1
  nlinarith only [ha,hb]

theorem add {lo hi : ℕ} {f g : ℕ → ℕ} (hf : Chord lo hi f) (hg : Chord lo hi g) :
    Chord lo hi (fun x => f x+g x) := by
  intro x hl hh
  have h := Nat.add_le_add (hf x hl hh) (hg x hl hh)
  simpa only [Nat.mul_add,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

theorem mul_left {lo hi : ℕ} {f : ℕ → ℕ} (hf : Chord lo hi f) (c : ℕ) :
    Chord lo hi (fun x => c*f x) := by
  intro x hl hh
  have h := Nat.mul_le_mul_left c (hf x hl hh)
  simpa only [Nat.mul_add,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h

theorem max {lo hi : ℕ} {f g : ℕ → ℕ} (hf : Chord lo hi f) (hg : Chord lo hi g) :
    Chord lo hi (fun x => Max.max (f x) (g x)) := by
  intro x hl hh
  dsimp only
  rcases le_total (f x) (g x) with h | h
  · rw [Nat.max_eq_right h]
    exact (hg x hl hh).trans (Nat.add_le_add
      (Nat.mul_le_mul_left _ (le_max_right _ _)) (Nat.mul_le_mul_left _ (le_max_right _ _)))
  · rw [Nat.max_eq_left h]
    exact (hf x hl hh).trans (Nat.add_le_add
      (Nat.mul_le_mul_left _ (le_max_left _ _)) (Nat.mul_le_mul_left _ (le_max_left _ _)))

theorem sub_affine (lo hi a b c d : ℕ) :
    Chord lo hi (fun x => (a*x+b)-(c*x+d)) := by
  intro x hl hh
  by_cases hx : a*x+b≤c*x+d
  · simp only [Nat.sub_eq_zero_of_le hx,Nat.mul_zero]
    exact Nat.zero_le _
  have he := Nat.sub_add_cancel (show c*x+d≤a*x+b by omega)
  have h0 : a*lo+b≤((a*lo+b)-(c*lo+d))+(c*lo+d) := by omega
  have h1 : a*hi+b≤((a*hi+b)-(c*hi+d))+(c*hi+d) := by omega
  have hsum := Nat.add_le_add (Nat.mul_le_mul_left (hi-x) h0) (Nat.mul_le_mul_left (x-lo) h1)
  have hw := weights lo x hi hl hh
  have ha := congrArg (fun z => a*z) hw.2
  have hc := congrArg (fun z => c*z) hw.2
  have hb := congrArg (fun z => b*z) hw.1
  have hd := congrArg (fun z => d*z) hw.1
  have he' := congrArg (fun z => (hi-lo)*z) he
  nlinarith only [hsum,ha,hb,hc,hd,he']

theorem le_of_endpoints {lo hi : ℕ} {f : ℕ → ℕ} (hf : Chord lo hi f)
    (cap : ℕ) (hlo : f lo≤cap) (hhi : f hi≤cap)
    (x : ℕ) (hl : lo≤x) (hh : x≤hi) : f x≤cap := by
  by_cases he : lo=hi
  · have hx : x=lo := by omega
    simpa only [hx] using hlo
  have h := (hf x hl hh).trans (Nat.add_le_add
    (Nat.mul_le_mul_left (hi-x) hlo) (Nat.mul_le_mul_left (x-lo) hhi))
  rw [←Nat.add_mul,(weights lo x hi hl hh).1] at h
  exact Nat.le_of_mul_le_mul_left h (by omega : 0<hi-lo)

end ProximityPrize.SubmissionLower.PortfolioChord6815
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.TriangularAffine6815
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem affine_between (a b m n d finish : ℕ) (hd : d≤finish)
    (h0 : a≤b) (h1 : a+m*finish≤b+n*finish) : a+m*d≤b+n*d := by
  by_cases hmn : m≤n
  · exact Nat.add_le_add h0 (Nat.mul_le_mul_right d hmn)
  · have hnm : n≤m := by omega
    have he : n+(m-n)=m := Nat.add_sub_of_le hnm
    have hh := Nat.mul_le_mul_left (m-n) hd
    nlinarith only [h1,he,hh]

theorem shifted_between (lo hi z p q a b m n : ℕ)
    (hp : p≤lo) (hq : q≤lo) (hz : lo≤z) (hh : z≤hi)
    (h0 : a+m*(lo-p)≤b+n*(lo-q))
    (h1 : a+m*(hi-p)≤b+n*(hi-q)) :
    a+m*(z-p)≤b+n*(z-q) := by
  have hhi : a+m*(lo-p)+m*(hi-lo)≤b+n*(lo-q)+n*(hi-lo) := by
    rw [show hi-p=(lo-p)+(hi-lo) by omega,show hi-q=(lo-q)+(hi-lo) by omega,
      Nat.mul_add,Nat.mul_add] at h1
    simpa only [Nat.add_assoc] using h1
  have h := affine_between (a+m*(lo-p)) (b+n*(lo-q)) m n (z-lo) (hi-lo) (by omega) h0 hhi
  rwa [show z-p=(lo-p)+(z-lo) by omega,show z-q=(lo-q)+(z-lo) by omega,
    Nat.mul_add,Nat.mul_add,←Nat.add_assoc,←Nat.add_assoc]

def left (cc cs clo charge slope x z : ℕ) := cc+cs*(x-clo)+charge+slope*(z-x)
def right (pc ps plo z : ℕ) := pc+ps*(z-plo)
def EndAt (cc cs clo chi charge slope pc ps plo z : ℕ) : Prop :=
  left cc cs clo charge slope clo z≤right pc ps plo z ∧
  left cc cs clo charge slope (min chi z) z≤right pc ps plo z

theorem triangle (cc cs clo chi charge slope pc ps plo phi x z : ℕ)
    (hchild : clo≤chi) (hparent : max plo clo≤phi)
    (h0 : EndAt cc cs clo chi charge slope pc ps plo (max plo clo))
    (h1 : EndAt cc cs clo chi charge slope pc ps plo phi)
    (hm : EndAt cc cs clo chi charge slope pc ps plo (min phi (max (max plo clo) chi)))
    (hx : clo≤x) (hxh : x≤chi) (hxp : x≤z) (hz : plo≤z) (hzh : z≤phi) :
    left cc cs clo charge slope x z≤right pc ps plo z := by
  let lo := max plo clo
  have hlo : lo≤z := by dsimp only [lo]; omega
  by_cases hc : cs≤slope
  · have hc' := Nat.mul_le_mul_right (x-clo) hc
    have hdecomp : (x-clo)+(z-x)=z-clo := by omega
    have hmul := congrArg (fun n => slope*n) hdecomp
    have hbound : left cc cs clo charge slope x z≤cc+charge+slope*(z-clo) := by
      unfold left
      rw [Nat.mul_add] at hmul
      omega
    have he0 : cc+charge+slope*(lo-clo)≤pc+ps*(lo-plo) := by
      have h := h0.1
      simpa only [left,right,Nat.sub_self,Nat.mul_zero,Nat.add_zero,lo] using h
    have he1 : cc+charge+slope*(phi-clo)≤pc+ps*(phi-plo) := by
      have h := h1.1
      simpa only [left,right,Nat.sub_self,Nat.mul_zero,Nat.add_zero] using h
    exact hbound.trans (shifted_between lo phi z clo plo (cc+charge) pc slope ps
      (le_max_right _ _) (le_max_left _ _) hlo hzh he0 he1)
  have hc : slope≤cs := by omega
  let top := min chi z
  have htop : x≤top := le_min hxh hxp
  have hc' := Nat.mul_le_mul_right (top-x) hc
  have e1 : top-clo=(x-clo)+(top-x) := by omega
  have e2 : z-x=(z-top)+(top-x) := by dsimp only [top]; omega
  have hbound : left cc cs clo charge slope x z≤left cc cs clo charge slope top z := by
    unfold left
    rw [e1,e2,Nat.mul_add,Nat.mul_add]
    omega
  apply hbound.trans
  by_cases hzc : z≤chi
  · have hloc : lo≤chi := hlo.trans hzc
    have hpivot : min phi (max lo chi)=min phi chi := by rw [max_eq_right hloc]
    have hmid : min phi chi≤chi := min_le_right _ _
    have he0 : cc+charge+cs*(lo-clo)≤pc+ps*(lo-plo) := by
      have h := h0.2
      change left cc cs clo charge slope (min chi lo) lo≤_ at h
      rw [min_eq_right hloc] at h
      simpa only [left,right,Nat.sub_self,Nat.mul_zero,Nat.add_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    have he1 : cc+charge+cs*(min phi chi-clo)≤pc+ps*(min phi chi-plo) := by
      have h := hm.2
      change left cc cs clo charge slope (min chi (min phi (max lo chi))) (min phi (max lo chi))≤_ at h
      rw [hpivot,min_eq_right hmid] at h
      simpa only [left,right,Nat.sub_self,Nat.mul_zero,Nat.add_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    have h := shifted_between lo (min phi chi) z clo plo (cc+charge) pc cs ps
      (le_max_right _ _) (le_max_left _ _) hlo (le_min hzh hzc) he0 he1
    simpa only [left,right,top,min_eq_right hzc,Nat.sub_self,Nat.mul_zero,Nat.add_zero,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  · have hcz : chi≤z := by omega
    have hpivot : min phi (max lo chi)=max lo chi := min_eq_right (by omega)
    have he0 : cc+cs*(chi-clo)+charge+slope*(max lo chi-chi)≤pc+ps*(max lo chi-plo) := by
      have h := hm.2
      change left cc cs clo charge slope (min chi (min phi (max lo chi))) (min phi (max lo chi))≤_ at h
      rw [hpivot,min_eq_left (le_max_right _ _)] at h
      exact h
    have he1 : cc+cs*(chi-clo)+charge+slope*(phi-chi)≤pc+ps*(phi-plo) := by
      have h := h1.2
      rw [min_eq_left (hcz.trans hzh)] at h
      exact h
    have h := shifted_between (max lo chi) phi z chi plo (cc+cs*(chi-clo)+charge) pc slope ps
      (le_max_right _ _) ((le_max_left plo clo).trans (le_max_left _ _)) (by omega) hzh he0 he1
    simpa only [left,right,top,min_eq_left hcz] using h

instance (cc cs clo chi charge slope pc ps plo z : ℕ) :
    Decidable (EndAt cc cs clo chi charge slope pc ps plo z) := by unfold EndAt; infer_instance

def check (cc cs clo chi charge slope pc ps plo phi : ℕ) : Bool :=
  if clo≤chi ∧ max plo clo≤phi then
    decide (EndAt cc cs clo chi charge slope pc ps plo (max plo clo) ∧
      EndAt cc cs clo chi charge slope pc ps plo phi ∧
      EndAt cc cs clo chi charge slope pc ps plo (min phi (max (max plo clo) chi)))
  else true

theorem check_sound (cc cs clo chi charge slope pc ps plo phi x z : ℕ)
    (h : check cc cs clo chi charge slope pc ps plo phi=true)
    (hx : clo≤x) (hxh : x≤chi) (hxp : x≤z) (hz : plo≤z) (hzh : z≤phi) :
    left cc cs clo charge slope x z≤right pc ps plo z := by
  have hc : clo≤chi ∧ max plo clo≤phi := by omega
  simp only [check,if_pos hc,decide_eq_true_eq] at h
  exact triangle cc cs clo chi charge slope pc ps plo phi x z hc.1 hc.2 h.1 h.2.1 h.2.2 hx hxh hxp hz hzh

end ProximityPrize.SubmissionLower.TriangularAffine6815
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.FinalCurves6815
set_option autoImplicit false
set_option maxHeartbeats 1300000

structure Piece where
  stop : ℕ
  base : ℕ
  slope : ℕ
  deriving DecidableEq

def value (p : Piece) (start z : ℕ) := p.base+p.slope*(z-start)
def evalFrom : ℕ → List Piece → ℕ → ℕ
  | _,[],_ => 0
  | start,p::ps,z => if z<p.stop then value p start z else evalFrom p.stop ps z
def eval (ps : List Piece) (z : ℕ) := evalFrom 0 ps z

def decodeAux (baseRadix slopeRadix : ℕ) : ℕ → ℕ → List Piece
  | 0,_ => []
  | n+1,code =>
      ⟨code%16384,(code/16384)%baseRadix,(code/16384/baseRadix)%slopeRadix⟩ ::
        decodeAux baseRadix slopeRadix n (code/16384/baseRadix/slopeRadix)
def decode (baseBits slopeBits code : ℕ) : List Piece :=
  decodeAux (2^baseBits) (2^slopeBits) (code%65536) (code/65536)

def validFrom (finish : ℕ) : ℕ → List Piece → Bool
  | start,[] => Nat.beq start finish
  | start,p::ps => Nat.blt start p.stop && Nat.ble p.stop finish && validFrom finish p.stop ps
def allCells (test : ℕ → Piece → Bool) : ℕ → List Piece → Bool
  | _,[] => true
  | start,p::ps => test start p && allCells test p.stop ps
def Cells (test : ℕ → Piece → Prop) : ℕ → List Piece → Prop
  | _,[] => True
  | start,p::ps => test start p ∧ Cells test p.stop ps

theorem allCells_sound (test : ℕ → Piece → Bool) (start : ℕ) (ps : List Piece)
    (h : allCells test start ps=true) : Cells (fun s p => test s p=true) start ps := by
  induction ps generalizing start with
  | nil => trivial
  | cons p ps ih =>
    simp only [allCells,Bool.and_eq_true] at h
    exact ⟨h.1,ih _ h.2⟩

theorem cells_mono (p q : ℕ → Piece → Prop) (start : ℕ) (ps : List Piece)
    (h : Cells p start ps) (hpq : ∀ lo piece, p lo piece → q lo piece) : Cells q start ps := by
  induction ps generalizing start with
  | nil => trivial
  | cons piece ps ih => exact ⟨hpq _ _ h.1,ih _ h.2⟩

theorem pointwise_of_cells (property : ℕ → ℕ → Prop) (start finish : ℕ) (ps : List Piece)
    (hv : validFrom finish start ps=true)
    (hc : Cells (fun lo p => ∀ z, lo≤z → z<p.stop → property z (value p lo z)) start ps)
    (z : ℕ) (hz : start≤z) (hf : z<finish) : property z (evalFrom start ps z) := by
  induction ps generalizing start with
  | nil => simp only [validFrom,Nat.beq_eq] at hv; omega
  | cons p ps ih =>
    simp only [validFrom,Bool.and_eq_true,Nat.blt_eq,Nat.ble_eq] at hv
    by_cases h : z<p.stop
    · simpa only [evalFrom,if_pos h] using hc.1 z hz h
    · simpa only [evalFrom,if_neg h] using ih p.stop hv.2 hc.2 (by omega)

def pairCheck (a : Piece) (aStart bStart : ℕ) (b : Piece) : Bool :=
  let lo := max aStart bStart
  let hi := min a.stop b.stop-1
  if lo<min a.stop b.stop then
    Nat.ble (value a aStart lo) (value b bStart lo) &&
      Nat.ble (value a aStart hi) (value b bStart hi)
  else true

theorem pairCheck_sound (a b : Piece) (aStart bStart z : ℕ)
    (h : pairCheck a aStart bStart b=true)
    (ha : aStart≤z) (ha' : z<a.stop) (hb : bStart≤z) (hb' : z<b.stop) :
    value a aStart z≤value b bStart z := by
  have hr : max aStart bStart<min a.stop b.stop := by omega
  simp only [pairCheck,if_pos hr,Bool.and_eq_true,Nat.ble_eq] at h
  exact TriangularAffine6815.shifted_between (max aStart bStart) (min a.stop b.stop-1) z
    aStart bStart a.base b.base a.slope b.slope (le_max_left _ _) (le_max_right _ _)
    (by omega) (by omega) h.1 h.2

def compare (left right : List Piece) : Bool :=
  allCells (fun lo a => allCells (pairCheck a lo) 0 right) 0 left

theorem cell_at (test : ℕ → Piece → Prop) (start finish : ℕ) (ps : List Piece)
    (hv : validFrom finish start ps=true) (hc : Cells test start ps)
    (z : ℕ) (hz : start≤z) (hf : z<finish) :
    ∃ lo p, lo≤z ∧ z<p.stop ∧ evalFrom start ps z=value p lo z ∧ test lo p := by
  induction ps generalizing start with
  | nil => simp only [validFrom,Nat.beq_eq] at hv; omega
  | cons p ps ih =>
    simp only [validFrom,Bool.and_eq_true,Nat.blt_eq,Nat.ble_eq] at hv
    by_cases h : z<p.stop
    · exact ⟨start,p,hz,h,by simp only [evalFrom,if_pos h],hc.1⟩
    · obtain ⟨lo,q,hlo,hhi,he,hq⟩ := ih p.stop hv.2 hc.2 (by omega)
      exact ⟨lo,q,hlo,hhi,by simpa only [evalFrom,if_neg h] using he,hq⟩

theorem compare_sound (left right : List Piece) (finish : ℕ)
    (hl : validFrom finish 0 left=true) (hr : validFrom finish 0 right=true)
    (hc : compare left right=true) (z : ℕ) (hz : z<finish) : eval left z≤eval right z := by
  have hleft := allCells_sound _ 0 left hc
  obtain ⟨lo,a,hlo,hhi,heL,ha⟩ := cell_at _ 0 finish left hl hleft z (Nat.zero_le _) hz
  have hright := allCells_sound _ 0 right ha
  obtain ⟨blo,b,hblo,hbhi,heR,hb⟩ := cell_at _ 0 finish right hr hright z (Nat.zero_le _) hz
  unfold eval
  rw [heL,heR]
  exact pairCheck_sound a b lo blo z hb hlo hhi hblo hbhi

end ProximityPrize.SubmissionLower.FinalCurves6815
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.LedgerCompact6815
open FinalCurves6815
set_option autoImplicit false

def aux (slopes : Array ℕ) : ℕ → ℕ → List Piece
  | 0,_ => []
  | n+1,c =>
    let digits := c/4194304%32
    let rest := c/134217728
    ⟨c%16384,rest%(16^digits),(slopes[c/16384%256]?).getD 0⟩ :: aux slopes n (rest/(16^digits))
def decode (slopes : Array ℕ) (code : ℕ) : List Piece := aux slopes (code%256) (code/256)

end ProximityPrize.SubmissionLower.LedgerCompact6815
end MergedPart5
