import ProximityPrize.SubmissionLower.Low49ActiveSplit
import Mathlib.Tactic.ClearExcept

set_option Elab.async false

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace Low49ActiveLattice
open Low48BentLattice
open K1_13 (Shape)
open K1_13_6_2_4 (Exponent)
open scoped Pointwise

def Fits (a : Cap) (c : ℕ) : Prop :=
  a.1.j + c ≤ a.1.b ∧ 3*a.1.t ≤ a.1.j ∧ 2*c ≤ a.1.j ∧ c + 2*a.2 ≤ 2*a.1.t ∧ 2*a.2 ≤ c ∧ c%2=0

def Active (m : Exponent) : ℕ := m 1 + m 2 + m 3

def points (a : Cap) (c : ℕ) : Set Exponent :=
  {m | m ∈ latticePoints a ∧ m 0 + 2*Active m + 3*m 4 + 2*c ≤ 2*a.1.b + 2*a.1.j}

theorem fits_add {a b : Cap} {c c' : ℕ} (ha : Fits a c) (hb : Fits b c') :
    Fits (Low48BentLattice.Add a b) (c+c') := by
  obtain ⟨ha₁,ha₂,ha₃,ha₄,ha₅,ha₆⟩ := ha
  obtain ⟨hb₁,hb₂,hb₃,hb₄,hb₅,hb₆⟩ := hb
  simp only [Fits, Low48BentLattice.Add, Shape.plus]
  omega

theorem finite (a : Cap) (c : ℕ) : (points a c).Finite :=
  (Low48BentLattice.finite a).subset fun _ hm => hm.1

instance (a : Cap) (c : ℕ) : Finite (points a c) := (finite a c).to_subtype

private theorem clipBound {u a h c b j p : ℕ}
    (hp : p = a - ((2*j-4*h)-(2*c-2*h)))
    (_hj : 4*h ≤ 2*j) (hc : 2*h ≤ 2*c) (hd : 2*c+2*h ≤ 2*j)
    (hu : u + a + h + p ≤ 2*b) :
    u + a + h ≤ 2*b ∧ u+2*a+3*h+2*c ≤ 2*b+2*j := by omega

private theorem join_threshold {ja jb ca cb h h' t : ℕ}
    (ha : 4*h≤2*ja ∧ 2*h≤2*ca) (hb : 4*h'≤2*jb ∧ 2*h'≤2*cb)
    (ht : h+h'=t) :
    (2*ja-4*h)+(2*jb-4*h')-((2*ca-2*h)+(2*cb-2*h')) =
      2*(ja+jb)-2*(ca+cb)-2*t := by omega

private theorem zero_fit {B J a h c u : ℕ}
    (hb : u+a+h≤B) (hc : u+2*a+3*h+c≤B+J) :
    u+a+h+(a-(J-c-2*h))≤B := by omega

private theorem split_zero {u a b ca cb : ℕ} (ha : a≤ca) (hb : b≤cb)
    (h : u+a+b≤ca+cb) :
    let v := min u (ca-a)
    v+(u-v)=u ∧ v+a≤ca ∧ u-v+b≤cb := by
  dsimp
  omega

theorem add {a b : Cap} {c c' : ℕ} (ha : Fits a c) (hb : Fits b c') :
    points a c + points b c' = points (Low48BentLattice.Add a b) (c+c') := by
  ext m
  constructor
  · rintro ⟨x,hx,y,hy,rfl⟩
    simp only [points, Set.mem_ofPred_eq, coords, Active, Low48BentLattice.Add,
      Shape.plus, Finsupp.add_apply] at *
    omega
  · intro hm
    obtain ⟨haB,haJ,hacJ,hacT,hacH,haP⟩ := ha
    obtain ⟨hbB,hbJ,hbcJ,hbcT,hbcH,hbP⟩ := hb
    simp only [points, Set.mem_ofPred_eq, coords, Active, Low48BentLattice.Add, Shape.plus] at hm
    obtain ⟨⟨hmB,hmJ,hmT,hmH⟩,hmC⟩ := hm
    let h := min (m 4) (2*a.2)
    let h' := m 4-h
    have hh : h+h'=m 4 ∧ h≤2*a.2 ∧ h'≤2*b.2 := by dsimp [h,h']; omega
    have hA : 4*h≤2*a.1.j ∧ 2*h≤2*c ∧ 2*c+2*h≤2*a.1.j := by
      clear * - hh haJ hacJ hacT hacH
      omega
    have hB : 4*h'≤2*b.1.j ∧ 2*h'≤2*c' ∧ 2*c'+2*h'≤2*b.1.j := by
      clear * - hh hbJ hbcJ hbcT hbcH
      omega
    let ja := 2*a.1.j-4*h
    let jb := 2*b.1.j-4*h'
    let ta := 2*a.1.t-2*h
    let tb := 2*b.1.t-2*h'
    let ca := 2*c-2*h
    let cb := 2*c'-2*h'
    have haW : 3*ta≤ja ∧ 2*ca≤ja ∧ ca≤2*ta := by dsimp [ja,ta,ca]; omega
    have hbW : 3*tb≤jb ∧ 2*cb≤jb ∧ cb≤2*tb := by dsimp [jb,tb,cb]; omega
    have he : ja%2=0 ∧ jb%2=0 ∧ ta%2=0 ∧ tb%2=0 ∧ ca%2=0 ∧ cb%2=0 := by
      dsimp [ja,jb,ta,tb,ca,cb]
      omega
    have hodd : h%2=0 ∨ h'%2=0 := by dsimp [h,h']; omega
    have hParity : (ca/2)%2=0 ∨ (cb/2)%2=0 := by dsimp [ca,cb]; omega
    have hIn : m 3 ≤ ta+tb ∧ m 1+2*m 2+3*m 3 ≤ ja+jb := by
      dsimp [ta,tb,ja,jb]
      omega
    obtain ⟨x,x',y,y',t,t',hx,hy,ht,hta,htb,hja,hjb,hp⟩ :=
      Low49ActiveSplit.split (x:=m 1) (y:=m 2) (z:=m 3) haW hbW he hParity hIn
    let w := x+y+t
    let w' := x'+y'+t'
    let pa := w-(ja-ca)
    let pb := w'-(jb-cb)
    have hwa : w≤ja ∧ pa≤ca := by clear * - hja; dsimp [w,pa]; omega
    have hwb : w'≤jb ∧ pb≤cb := by clear * - hjb; dsimp [w',pb]; omega
    have hbs : w+h+pa ≤ 2*a.1.b := by
      clear * - hA hwa haB
      dsimp [ja,ca] at hwa
      omega
    have hbs' : w'+h'+pb ≤ 2*b.1.b := by
      clear * - hB hwb hbB
      dsimp [jb,cb] at hwb
      omega
    have hW : w+w' = m 1+m 2+m 3 := by
      unfold w w'
      rw [← hx,← hy,← ht]
      ac_rfl
    have hJ : ja+jb-(ca+cb) = 2*(a.1.j+b.1.j)-2*(c+c')-2*m 4 :=
      join_threshold ⟨hA.1,hA.2.1⟩ ⟨hB.1,hB.2.1⟩ hh.1
    have hp' : pa+pb = m 1+m 2+m 3 -
        (2*(a.1.j+b.1.j)-2*(c+c')-2*m 4) := by
      rw [← hJ]
      exact hp
    have hzero : m 0 + (w+h+pa) + (w'+h'+pb) ≤ 2*a.1.b+2*b.1.b := by
      have hs := zero_fit (B:=2*(a.1.b+b.1.b)) (J:=2*(a.1.j+b.1.j))
        (a:=m 1+m 2+m 3) (h:=m 4) (c:=2*(c+c')) (u:=m 0) (by clear * - hmB; omega) (by clear * - hmC; omega)
      rw [← hp',← hW,← hh.1, Nat.mul_add] at hs
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hs
    let u := min (m 0) (2*a.1.b-(w+h+pa))
    let u' := m 0-u
    have hu : u+u'=m 0 ∧ u+w+h+pa≤2*a.1.b ∧ u'+w'+h'+pb≤2*b.1.b := by
      simpa only [u,u',Nat.add_assoc] using split_zero hbs hbs' hzero
    have hb₁ := clipBound (u:=u) (a:=w) (h:=h) (c:=c) (b:=a.1.b) (j:=a.1.j)
      (p:=pa) rfl hA.1 hA.2.1 hA.2.2 hu.2.1
    have hb₂ := clipBound (u:=u') (a:=w') (h:=h') (c:=c') (b:=b.1.b) (j:=b.1.j)
      (p:=pb) rfl hB.1 hB.2.1 hB.2.2 hu.2.2
    let v : Exponent := Finsupp.equivFunOnFinite.symm ![u,x,y,t,h]
    let v' : Exponent := Finsupp.equivFunOnFinite.symm ![u',x',y',t',h']
    refine ⟨v, ?_, v', ?_, ?_⟩
    · simp only [points, Set.mem_ofPred_eq, coords, Active]
      change (u+x+y+t+h≤2*a.1.b ∧ x+2*y+3*t+4*h≤2*a.1.j ∧ t+2*h≤2*a.1.t ∧ h≤2*a.2) ∧
        u+2*(x+y+t)+3*h+2*c≤2*a.1.b+2*a.1.j
      refine ⟨⟨?_,?_,?_,hh.2.1⟩,hb₁.2⟩
      · simpa only [w,Nat.add_assoc] using hb₁.1
      · clear * - hja hA
        dsimp [ja] at hja
        omega
      · clear * - hta hh hacH hacT
        dsimp [ta] at hta
        omega
    · simp only [points, Set.mem_ofPred_eq, coords, Active]
      change (u'+x'+y'+t'+h'≤2*b.1.b ∧ x'+2*y'+3*t'+4*h'≤2*b.1.j ∧ t'+2*h'≤2*b.1.t ∧ h'≤2*b.2) ∧
        u'+2*(x'+y'+t')+3*h'+2*c'≤2*b.1.b+2*b.1.j
      refine ⟨⟨?_,?_,?_,hh.2.2⟩,hb₂.2⟩
      · simpa only [w',Nat.add_assoc] using hb₂.1
      · clear * - hjb hB
        dsimp [jb] at hjb
        omega
      · clear * - htb hh hbcH hbcT
        dsimp [tb] at htb
        omega
    · ext i
      fin_cases i
      · exact hu.1
      · exact hx
      · exact hy
      · exact ht
      · exact hh.1

end Low49ActiveLattice
