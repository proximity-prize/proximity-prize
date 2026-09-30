import ProximityPrize.SubmissionLower.FinalLookup6815
import ProximityPrize.SubmissionLower.PackingOwnCheck6815
namespace ProximityPrize.SubmissionLower.FinalBaseCheck6815
open FinalCurves6815 PackingData6815 PackingSemantics6815 SingletonCertificate6815
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def fullNum (j r v : ℕ) := lookup (full_packed j) r v
def lightNum (j r v : ℕ) := lookup (light_packed j) r v

def BaseBound (r v z cap : ℕ) : Prop :=
  (∃ j, j<8 ∧ full_slope j*z+fullNum j r v≤cap) ∨
  (10≤r ∧ r≤19 ∧ v≤70 ∧
    (∃ j, j<14 ∧ light_slope j*z+lightNum j r v≤cap) ∧
    ∀ q u, 10≤q → q≤r → u≤v → ∃ j, j<14 ∧ ∀ x, x≤z →
      SingletonData6815.cap q u x+light_slope j*(z-x)+lightNum j (r-q) (v-u)≤cap)

def lineCheck (slope base lo hi start : ℕ) (p : Piece) : Bool :=
  if lo≤hi then Nat.ble (slope*lo+base) (value p start lo) &&
    Nat.ble (slope*hi+base) (value p start hi) else true

theorem lineCheck_sound (slope base lo hi start : ℕ) (p : Piece)
    (h : lineCheck slope base lo hi start p=true) (z : ℕ)
    (hz : lo≤z) (hh : z≤hi) (hs : start≤lo) : slope*z+base≤value p start z := by
  simp only [lineCheck,if_pos (hz.trans hh),Bool.and_eq_true,Nat.ble_eq] at h
  have hm := TriangularAffine6815.shifted_between lo hi z 0 start base p.base slope p.slope
    (Nat.zero_le _) hs hz hh
    (by simpa only [value,Nat.sub_zero,Nat.add_comm] using h.1)
    (by simpa only [value,Nat.sub_zero,Nat.add_comm] using h.2)
  simpa only [value,Nat.sub_zero,Nat.add_comm] using hm

def childPiece (slope charge lo hi start : ℕ) (p : Piece) (cstart : ℕ) (c : Piece) : Bool :=
  TriangularAffine6815.check c.base c.slope cstart (c.stop-1) charge slope
    (value p start lo) p.slope lo hi
def childCheck (slope charge lo hi start : ℕ) (p : Piece) (child : List Piece) : Bool :=
  allCells (childPiece slope charge lo hi start p) 0 child

theorem childCheck_sound (slope charge lo hi start : ℕ) (p : Piece) (finish : ℕ) (child : List Piece)
    (hv : validFrom finish 0 child=true) (hc : childCheck slope charge lo hi start p child=true)
    (x z : ℕ) (hxf : x<finish) (hxz : x≤z) (hz : lo≤z) (hh : z≤hi) (hs : start≤lo) :
    eval child x+slope*(z-x)+charge≤value p start z := by
  obtain ⟨clo,c,hclo,hchi,he,hc⟩ := cell_at _ 0 finish child hv (allCells_sound _ 0 child hc) x (Nat.zero_le _) hxf
  have h := TriangularAffine6815.check_sound _ _ _ _ _ _ _ _ _ _ x z hc hclo (by omega) hxz hz hh
  have hp : value p start lo+p.slope*(z-lo)=value p start z := by
    unfold value
    rw [show z-start=(lo-start)+(z-lo) by omega,Nat.mul_add]
    omega
  change value c clo x+charge+slope*(z-x)≤value p start lo+p.slope*(z-lo) at h
  rw [hp] at h
  simpa only [eval,he,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

def digit (code i : ℕ) := code/(16^i)%16
def heavyChoice (code v q u : ℕ) := digit code (1+(q-10)*(v+1)+u)
def heavyCheck (r v code lo hi start : ℕ) (p : Piece) : Bool :=
  Nat.blt (digit code 0) 14 && lineCheck (light_slope (digit code 0)) (lightNum (digit code 0) r v) lo hi start p &&
  allN (fun i => allN (fun u =>
    let q := i+10
    let j := heavyChoice code v q u
    Nat.blt j 14 && childCheck (light_slope j) (lightNum j (r-q) (v-u)) lo hi start p
      (FinalLookup6815.single q u).curve) (v+1)) (r-9)

def check (r v aux lo hi start : ℕ) (p : Piece) : Bool :=
  if aux<8 then lineCheck (full_slope aux) (fullNum aux r v) lo hi start p
  else decide (aux%16=15 ∧ 10≤r ∧ r≤19 ∧ v≤70 ∧ hi≤4500) &&
    heavyCheck r v (aux/16) lo hi start p

theorem check_sound (r v aux lo hi start : ℕ) (p : Piece)
    (h : check r v aux lo hi start p=true) (z : ℕ)
    (hz : lo≤z) (hh : z≤hi) (hs : start≤lo) (ht : r+v+z≤11192) :
    BaseBound r v z (value p start z) := by
  by_cases ha : aux<8
  · left
    simp only [check,if_pos ha] at h
    exact ⟨aux,ha,lineCheck_sound _ _ _ _ _ p h z hz hh hs⟩
  · right
    simp only [check,if_neg ha,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨hg,hc⟩ := h
    simp only [heavyCheck,Bool.and_eq_true,Nat.blt_eq] at hc
    refine ⟨hg.2.1,hg.2.2.1,hg.2.2.2.1,?_,?_⟩
    · exact ⟨digit (aux/16) 0,hc.1.1,lineCheck_sound _ _ _ _ _ p hc.1.2 z hz hh hs⟩
    · intro q u hq hqr hu
      have hhq := allN_sound _ (r-9) hc.2 (q-10) (by omega)
      have hhu := allN_sound _ (v+1) hhq u (by omega)
      simp only [show q-10+10=q by omega,Bool.and_eq_true,Nat.blt_eq] at hhu
      refine ⟨heavyChoice (aux/16) v q u,hhu.1,?_⟩
      intro x hx
      have hq39 : q≤39 := by omega
      have hqu : q+u≤182 := by omega
      have he : (FinalLookup6815.single q u).curve=SingletonData6815.curve q u :=
        congrArg SingletonCertificate6815.Row.curve (FinalLookup6815.single_eq q u (by omega) hq39)
      have hv : validFrom (11193-q-u) 0 (FinalLookup6815.single q u).curve=true := by
        rw [he]
        exact PackingOwnCheck6815.curve_valid q u (by omega) hq39 hqu
      have hb := childCheck_sound _ _ lo hi start p (11193-q-u) _ hv hhu.2 x z (by omega) hx hz hh hs
      simpa only [he,SingletonData6815.cap] using hb

end ProximityPrize.SubmissionLower.FinalBaseCheck6815
