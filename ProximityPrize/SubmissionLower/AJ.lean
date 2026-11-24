import ProximityPrize.SubmissionLower.CG
import ProximityPrize.SubmissionLower.AU
import ProximityPrize.SubmissionLower.AW
import ProximityPrize.SubmissionLower.ZUCbske
import ProximityPrize.SubmissionLower.C3
set_option Elab.async false
open _root_ renaming Fintype → z85, Fintype.card → zhP, Fintype.sum_eq_single → zkq, Fintype.sum_sum_type → zbt, Function.Injective → zq4, List.mem_cons_of_mem → zrw, List.mem_cons_self → zYY, Matrix → z30, Matrix.mul_apply → zW3, Matrix.rank_mul_le_right → zmg, Matrix.rank_transpose → zZo, Matrix.zero_apply → zTj, Nat.add_le_add → z9f, Nat.add_le_add_right → zlr, Nat.choose_eq_descFactorial_div_factorial → zn4, Nat.mul_le_mul_left → zBI
section
set_option autoImplicit true
namespace P1_6_1_5_1
open scoped BigOperators
open private bhG from ProximityPrize.SubmissionLower.CG
theorem rank_with_relation {α β F : Type*} [z85 α] [z85 β] [Field F]
    (M : z30 α β F) (P : α → Prop) (Q : β → Prop) [DecidablePred P] [DecidablePred Q]
    (cover : ∀ a b, M a b ≠ 0 → P a ∨ Q b)
    (v : {a // P a} → F) (pivot : {a // P a}) (hpivot : v pivot = 1)
    (rel : ∀ b, ¬ Q b → (∑ a : {x // P x}, M a.val b * v a) = 0) :
    M.rank + 1 ≤ zhP {a // P a} + zhP {b // Q b} := by
  classical
  let W := {a // P a} ⊕ {b // Q b}
  let A : z30 α W F := fun a => Sum.elim
    (fun i => if i.val = a then 1 else 0)
    (fun j => if P a then 0 else M a j.val)
  let B : z30 W β F := fun i b => i.elim
    (fun j => M j.val b)
    (fun j => if j.val = b then 1 else 0)
  have hAB : A * B = M := by
    ext a b
    rw [zW3, zbt]
    simp only [A, B, Sum.elim_inl, Sum.elim_inr,
      ite_mul, mul_ite, one_mul, zero_mul, mul_one, mul_zero]
    rw [bhG P (fun i => M i b), bhG Q (fun j => if P a then 0 else M a j)]
    by_cases ha : P a
    · simp [ha]
    · by_cases hb : Q b
      · simp [ha, hb]
      · have hz : M a b = 0 := by
          by_contra hn
          exact (cover a b hn).elim ha hb
        simp [ha, hb, hz]
  let V : z30 W (Fin 1) F := fun i _ => i.elim v
    (fun j => -(∑ a : {x // P x}, M a.val j.val * v a))
  have hBV : B.transpose * V = 0 := by
    ext b j
    rw [zW3, zbt, zTj]
    change (∑ a : {x // P x}, M a.val b * v a) +
      (∑ k : {x // Q x}, (if k.val = b then (1 : F) else 0) *
        -(∑ a : {x // P x}, M a.val k.val * v a)) = 0
    simp only [ite_mul, one_mul, zero_mul]
    rw [bhG Q (fun k => -(∑ a : {x // P x}, M a.val k * v a))]
    by_cases hb : Q b
    · simp [hb]
    · simp [hb, rel b hb]
  let f : Fin 1 → W := fun _ => Sum.inl pivot
  have hid : V.submatrix f id = 1 := by
    ext i j
    have hij : i = j := Subsingleton.elim _ _
    rw [Matrix.one_apply, ite_eq_left hij]
    exact hpivot
  have hr := ju.cfv B.transpose V f hBV hid
  rw [zZo] at hr
  have hab : M.rank ≤ B.rank := hAB ▸ zmg A B
  exact (zlr hab 1).trans (hr.trans_eq Fintype.card_sum)
theorem rank_with_pattern {α β γ F : Type*} [z85 α] [z85 β] [z85 γ] [Field F]
    (M : z30 α β F) (P : α → Prop) (Q : β → Prop) [DecidablePred P] [DecidablePred Q]
    (cover : ∀ a b, M a b ≠ 0 → P a ∨ Q b)
    (row : γ → {a // P a}) (hrow : zq4 row)
    (c : γ → F) (pivot : γ) (hpivot : c pivot = 1)
    (rel : ∀ b, ¬ Q b → (∑ i, M (row i).val b * c i) = 0) :
    M.rank + 1 ≤ zhP {a // P a} + zhP {b // Q b} := by
  classical
  let v (a : {x // P x}) := ∑ i, if a = row i then c i else 0
  apply rank_with_relation M P Q cover v (row pivot)
  · change (∑ i, if row pivot = row i then c i else 0) = 1
    rw [zkq pivot]
    · simp [hpivot]
    · intro i hi
      exact ite_eq_right (fun h => hi (hrow h).symm)
  · intro b hb
    simp only [v, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (rel b hb)
    rw [zkq (row i)]
    · simp
    · intro a ha
      simp [ha]
end P1_6_1_5_1
end
section
set_option autoImplicit true
namespace P1_6_1_5_1
open ac5 baV

open scoped BigOperators Matrix


local instance : Fact (Nat.Prime P1.p) := ⟨KoalaBear.is_prime⟩
abbrev RelationRow := Σ a : Fin 4, Fin (12 - 3 * a.val)
def Ug : RelationRow := ⟨3, ⟨2, by decide⟩⟩
private noncomputable def rowExponent (d b u a x : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![a, d - u - b - a - x, b + x, u]
@[simp] private theorem II (d b u a x : ℕ) : rowExponent d b u a x 0 = a := by
  simp [rowExponent]
@[simp] private theorem lI (d b u a x : ℕ) :
    rowExponent d b u a x 1 = d - u - b - a - x := by simp [rowExponent]
@[simp] private theorem lV (d b u a x : ℕ) : rowExponent d b u a x 2 = b + x := by
  simp [rowExponent]
@[simp] private theorem pG (d b u a x : ℕ) : rowExponent d b u a x 3 = u := by
  simp [rowExponent]
def Relation (D b : ℕ) (c : ℕ → ℕ → ℕ) : Prop :=
  ∀ m y : ℕ, 12 ≤ m + 2 * y → m + 2 * y ≤ 15 →
    (∑ i : RelationRow,
      ((D - i.1.val - i.2.val).choose m : ZMod P1.p) *
        ((b + i.2.val).choose (b + y) : ZMod P1.p) * (c i.1.val i.2.val : ZMod P1.p)) = 0
end P1_6_1_5_1
end
section
set_option autoImplicit true
section
namespace nF
open aR (Shape aO bY qP iH ceilDiv)
open vS (tC)
open yi (bF tD)
open bJ (Bank gZ mV bf Rb)
open bj0 (slope bN4)
open private shift shift_add acJ aET from ProximityPrize.SubmissionLower.CI
open nZ (j0 On Jg zK Xr Q5 Xz A9 AA DC KZ F4 adM)
private def arE (p:Shape) :Prop :=
 let u:=bf+1
 let v :=bf+2
 let a :=qP u p
 let b:=qP v p
 3*(p.t+1)≤p.j+1∧2≤p.t+1 ∧
   3*(2+(u - 5)*p.t)≤a.j∧3*(2+(v - 5)*p.t)≤b.j ∧
   2*u≤a.t∧2*v≤b.t
private instance (p:Shape) :Decidable (arE p) := by
 unfold arE
 infer_instance
private theorem a8Y {p p' q:Shape} (hp:aO p p') (hp' : bF p')
    (hq:bF q) (hj:p.j=p'.j) (ht:p.t=p'.t) :
    Rb p q≤Rb p' q:= by
  let u:=bf+1
  let v :=bf+2
  let A:=qP u
  let B:=qP v
  let G:=tC
  have hchart:iH p q (bY u p) (bY v p) ≤
      iH p' q (bY u p') (bY v p') :=
    tD hp (j0 q) (DC u hp) (DC v hp) hp' hq
      (A9 u _) hq (A9 u _) (A9 v _)
  have hlift:iH p q (A p) (B p)≤ iH p' q (A p') (B p') :=
    tD hp (j0 q) (KZ u hp) (KZ v hp) hp' hq
      (AA u _) hq (AA u _) (AA v _)
  have hgraph (M:ℕ) :
      iH p q (G p) (qP M p)≤ iH p' q (G p') (qP M p') :=
    tD hp (j0 q) (adM hp) (KZ M hp) hp' hq
      (F4 _) hq (F4 _) (AA M _)
  have hbase :=z9f (z9f hlift (zBI u (hgraph v)))
    (zBI v (hgraph u))
  have hguard :arE p↔arE p' := by
    simp only [arE,qP,hj,ht]
  let iy (x :Shape) :=iH x q (bY u x) (bY v x)
  let base (x :Shape) :=iH x q (A x) (B x) +
    u*iH x q (G x) (B x)+v*iH x q (G x) (A x)
  let term (x :Shape) :=
    ((base x :ℤ) -
      ((u:ℤ)*bJ.wP x q slope (B x) +
        (v :ℤ)*bJ.wP x q slope (A x) +
        (u:ℤ)*(v :ℤ) *
          (bJ.wP x q slope (G x) - bJ.wP x q slope slope))).toNat
  change (if arE p then min (iy p) (min (base p) (term p))
    else min (iy p) (base p)) ≤
    (if arE p' then min (iy p') (min (base p') (term p'))
    else min (iy p') (base p'))
  by_cases hc:arE p
  · have hc' := hguard.mp hc
    rw [ite_eq_left hc,ite_eq_left hc']
    apply min_le_min hchart (min_le_min hbase ?_)
    have hg (x :Shape) (hx :arE x) :2*1≤(G x).t:= by
      have h1 :=hx.1
      have h2 :=hx.2.1
      change 2*1≤ min (x.t+1) ((x.j+1)/3)
      exact le_min h2 (by omega)
    have hb (x :Shape) (hx :arE x) :2*v≤(B x).t:=hx.2.2.2.2.2
    have hge (x :Shape) (hx :arE x) :
        G x=(shift 1 (G x)).plus slope := by
      have h:=shift_add (F4 x) (hg x hx)
      simpa only [Shape.scale,Nat.one_mul] using h
    have hte (x :Shape) (hx :arE x) :
        term x=iH x q (A x) (B x) +
          u*iH x q (shift 1 (G x)) (shift v (B x)) +
          v*iH x q (shift 1 (G x)) (A x) :=
      bN4 x q _ _ _ _ _ u v (hge x hx) (shift_add (AA v x) (hb x hx))
        hq (F4 x) (AA u x) (AA v x)
        (acJ (F4 x) (hg x hx)) (acJ (AA v x) (hb x hx))
    have hg0:=acJ (F4 p) (hg p hc)
    have hg1 :=acJ (F4 p') (hg p' hc')
    have hb0:=acJ (AA v p) (hb p hc)
    have hb1 :=acJ (AA v p') (hb p' hc')
    have hm:=aET 1 (adM hp)
    have hx :=tD hp (j0 q) hm (aET v (KZ v hp))
      hp' hq hg1 hq hg0 hb0
    have hy :=tD hp (j0 q) hm (KZ u hp)
      hp' hq hg1 hq hg0 (AA u p)
    rw [hte p hc,hte p' hc']
    exact z9f (z9f hlift (zBI u hx)) (zBI v hy)
  · rw [ite_eq_right hc,ite_eq_right (fun h=>hc (hguard.mpr h))]
    exact min_le_min hchart hbase
private theorem ceil_mono {a b:ℕ} (h:a≤b) (l:ℕ) :ceilDiv a l≤ ceilDiv b l :=
 Nat.div_le_div_right (Nat.sub_le_sub_right (zlr h l) 1)
private theorem Dh (aV:Bank) :bF aV.box := by
 cases aV <;> exact ⟨by decide,by decide⟩
theorem Tf {x y :Shape} (hbxy :x.b≤y.b) (hj:x.j=y.j) (ht:x.t=y.t)
   (hx :3*x.t≤x.j) (aV:Bank) (l:ℕ) :
   bJ.dJ x aV.box l≤bJ.dJ y aV.box l:= by
 let p:=x.iU
 let p' := y.iU
 let q:=aV.box
 let L:=bf
 let A:=q.plus (p.scale 4)
 let A' := q.plus (p'.scale 4)
 have h:aO x y :=⟨hbxy,hj.le,ht.le⟩
 have hp:=On h
 have hpc:bF p:=Jg x hx
 have hp'c:bF p' := Jg y (by rw [← hj,← ht]; exact hx)
 have hqc:bF q:=Dh aV
 have ha :aO A A' := zK (j0 q) (Q5 hp 4)
 have hac:bF A:=Xr hqc (Xz hpc 4)
 have ha'c:bF A' := Xr hqc (Xz hp'c 4)
 have hs :=a8Y hp hp'c hqc hj ht
 have hb:=(DC (L+1) hp).1
 have hmain: (P4.t+2*mV)*x.b*q.b*(bY (L+1) p).b ≤
     (P4.t+2*mV)*y.b*q.b*(bY (L+1) p').b:= by
   gcongr
 have hcurve :=tD hp (j0 q) ha (DC L hp) hp'c hqc ha'c hqc hac (A9 L p)
 have hpoint :=tD hp (j0 q) ha hp hp'c hqc ha'c hqc hac hpc
 have hcurve' := tD hp hp hp (DC L hp) hp'c hp'c hp'c hpc hpc (A9 L p)
 have hpoint' := tD hp hp hp hp hp'c hp'c hp'c hpc hpc hpc
 have htc:=zBI 2 h.2.2
 have hc:=z9f hcurve (Nat.mul_le_mul htc hcurve')
 have hn:=z9f hpoint (Nat.mul_le_mul htc hpoint')
 have hgeom:=z9f (zBI P4.t hc) (zBI (2*mV) hn)
 have hraw:=Nat.mul_le_mul_right q.b (zBI (2*gZ) h.1)
 exact z9f (z9f hraw (ceil_mono hgeom _))
   (ceil_mono (z9f (ceil_mono hs _) (ceil_mono hmain _)) l)
open scoped BigOperators
end nF
end
section
namespace nF
open aR (Shape)



def eG (top extraIndex extraDegree :ℕ) :Shape :=
 ⟨top+extraDegree,3*top+extraIndex,top⟩
end nF
end
section
namespace UO
open GO
open baV (above)
open fP (qI)
open scoped BigOperators
open private order from ProximityPrize.SubmissionLower.CG
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
def DV (q r :ℕ) :ℕ:=144-(q+r)
def bAQ (U:ℕ→ℕ→Prop) :Prop :=
 ∀ ⦃z c z' c' : ℕ⦄,z≤z' → z - 2*c≤z' - 2*c' → c≤ c' → U z c→U z' c'
theorem cAy (t u v w:ℕ) :bAQ (above t u v w) := by
 intro z c z' c' hz hb hc h
 unfold above at h ⊢
 exact ⟨h.1.trans hb,h.2.elim (fun hv=>Or.inl (hv.trans hc))
  (fun ⟨ht,hu⟩=>Or.inr ⟨ht.trans hz,hu.trans hc⟩)⟩
def OR (KN :List (ℕ×ℕ)) (z c:ℕ) :Prop :=
 (KN.any fun (b,f)=>decide (b≤z - 2*c∧f≤ c))=true
instance (KN :List (ℕ×ℕ)) (z c:ℕ) :Decidable (OR KN z c) :=
 inferInstanceAs (Decidable (_=true))
theorem aHh (KN :List (ℕ×ℕ)) :bAQ (OR KN) := by
 intro z c z' c' _ hb hc h
 rw [OR,List.any_eq_true] at h ⊢
 obtain ⟨⟨b,f⟩,hm,hp⟩:=h
 simp only [decide_eq_true_eq] at hp ⊢
 exact ⟨(b,f),hm,hp.1.trans hb,hp.2.trans hc⟩
def ajZ (q r :ℕ) (U:ℕ→ℕ→Prop) (e :ait q (offset r)) :Prop :=
  51+e.val 0+3*(e.val 3 - 13)≤ iO q+order e.val+r ∧
    U (order e.val) (e.val 3)
def ajY (q r :ℕ) (U:ℕ→ℕ→Prop) (m:XN q (offset r)) :Prop :=
 order m.val<DV q r ∧ ¬ U (order m.val) (m.val 3)
def aEG (d h r z c:ℕ) :ℕ :=
 min (d+c+1 - z) (min ((h+2 - z)/3) (d+z+r+1-(51+3*(c - 13))))
def a2K (d z :ℕ) :ℕ:=d+z - 51
def aHb (d r z c:ℕ) :ℕ :=
 if c≤13 then min (d+c+1 - z) (d+z+r+1 - 51)-a2K d z else 0
def aht (d h r :ℕ) (U:ℕ→ℕ→Prop) [∀ z c,Decidable (U z c)] :ℕ :=
  qI h fun z=>qI (z/2+1) fun c =>
    if U z c then aEG d h r z c else aHb d r z c
end UO
end
section
namespace UO
open GO

open fP (qI)
open scoped BigOperators
def cqd (b h:ℕ) :ℕ :=
 qI h fun z=>(z/2+1)*min ((h+2 - z)/3) (b+z+1 - h)
def aFb (b h start len:ℕ) :=
 qI len fun i=>cqd b (h-(start+i))
end UO
end
section
namespace a0C
open GO UO
open fP (cF)


open scoped BigOperators Matrix
noncomputable section
abbrev F:=ZMod P1.p
abbrev Im:=ℕ×ℕ×ℕ
abbrev RA:=List (Im×ℕ)
abbrev R (q:ℕ) :=ait q (offset 3)
abbrev C (q:ℕ) :=XN q (offset 3)
abbrev B (q:ℕ) :=Gy q (offset 3)
abbrev P (q:ℕ) (S:List (ℕ×ℕ)) :=ajZ q 3 (OR S)
abbrev Q (q:ℕ) (S:List (ℕ×ℕ)) :=ajY q 3 (OR S)
def HD (e :Fin 4 →₀ ℕ) :Im:=(e 1,e 2,e 3)
def size (t:Im) :ℕ:=t.1+t.2.1+t.2.2
def index (t:Im) :ℕ:=t.1+2*t.2.1+3*t.2.2
def z (t:Im) :ℕ:=t.2.1+2*t.2.2
def aCb (S:List (ℕ×ℕ)) (t:Im) :Prop :=OR S (z t) t.2.2
instance (S:List (ℕ×ℕ)) (t:Im) :Decidable (aCb S t) :=
 inferInstanceAs (Decidable (OR S (z t) t.2.2))
def agg (d h:ℕ) (S:List (ℕ×ℕ)) (t:Im) :Prop :=
  size t≤d∧3*(d - size t)+z t<h ∧
    51+(d - size t)+3*(t.2.2 - 13)≤d+z t+3∧aCb S t
def aHa (d h:ℕ) (S:List (ℕ×ℕ)) (t:Im) :Prop :=
 size t≤d∧48≤ index t∧index t≤51∧t.2.2≤13∧z t<h ∧ ¬ aCb S t
instance (d h:ℕ) (S:List (ℕ×ℕ)) (t:Im) :Decidable (agg d h S t) := by
 unfold agg
 infer_instance
instance (d h:ℕ) (S:List (ℕ×ℕ)) (t:Im) :Decidable (aHa d h S t) := by
 unfold aHa
 infer_instance
private def auT (d:ℕ) (t:Im) :Fin 4 →₀ ℕ :=
 Finsupp.equivFunOnFinite.symm ![d - size t,t.1,t.2.1,t.2.2]
@[simp] private theorem cNK (d:ℕ) (t:Im) :auT d t 0=d - size t:= by simp [auT]
@[simp] private theorem b2o (d:ℕ) (t:Im) :auT d t 1=t.1 := by simp [auT]
@[simp] private theorem b2p (d:ℕ) (t:Im) :auT d t 2=t.2.1 := by simp [auT]
@[simp] private theorem b2q (d:ℕ) (t:Im) :auT d t 3=t.2.2 := by simp [auT]
private theorem djo {d:ℕ} {e :Fin 4 →₀ ℕ} (h:e.degree=d) :
  e 0=d - size (HD e) := by
 rw [cF] at h
 change e 0=d-(e 1+e 2+e 3)
 omega
theorem dh8 {α:Type*} (f :α→Fin 4 →₀ ℕ) (hf :zq4 f)
   (d:ℕ) (hd : ∀ a,(f a).degree=d) :zq4 (HD ∘ f) := by
 intro a b h
 apply hf
 ext i
 change HD (f a)=HD (f b) at h
 fin_cases i
 · change (f a) 0=(f b) 0
   rw [djo (hd a),djo (hd b),h]
 · exact congrArg Prod.fst h
 · exact congrArg (fun t:Im=>t.2.1) h
 · exact congrArg (fun t:Im=>t.2.2) h
def entry (e m:Im) :ℕ :=
 ju.n9 e.1 m.1*ju.n9 e.2.1 m.2.1*ju.n9 e.2.2 m.2.2
@[simp] theorem cEm (q:ℕ) (e :R q) (m:C q) :
   (entry (HD e.val) (HD m.val) :F)=B q e m:= by
  simp only [B,Gy,HD,entry,Nat.cast_mul,ju.n9,
   zn4]
theorem b1F {e m:Im} (h:entry e m≠0) :
  m.1≤e.1∧m.2.1≤e.2.1∧m.2.2≤e.2.2 := by
 simp only [entry,ju.n9,← zn4,
  mul_ne_zero_iff,Nat.choose_ne_zero_iff] at h
 exact ⟨h.1.1,h.1.2,h.2⟩
def weight (L:RA) (t:Im) :ℕ :=
 (L.map fun a=>if t=a.1 then a.2 else 0).sum
def aNl (L:RA) (m:Im) :ℕ:=((L.map fun a=>entry a.1 m*a.2).sum) % P1.p
theorem dfN {α:Type*} [z85 α] (f :α→ Im) (hf :zq4 f)
   (g:Im→ℕ) (L:RA) (hL : ∀ a∈L,∃ i,f i=a.1) :
   (∑ i,(g (f i) :F)*(weight L (f i) :F)) =
     ((((L.map fun a=>g a.1*a.2).sum) % P1.p:ℕ) :F) := by
 rw [ZMod.natCast_mod]
 induction L with
 | nil=>simp [weight]
 | cons a L ih =>
   obtain ⟨i,hi⟩:=hL a (zYY ..)
   simp only [weight,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_mul,mul_add,
     Finset.sum_add_distrib] at ih ⊢
   rw [ih (fun b hb=>hL b (zrw _ hb))]
   congr 1
   rw [zkq i]
   · simp [hi]
   · intro j hj
     have hn:f j≠a.1 := fun h=>hj (hf (h.trans hi.symm))
     simp [hn]
theorem sumZero (L:RA) (g:Im×ℕ→ℕ) (h : ∀ a∈L,g a=0) :
   (L.map g).sum=0:= by
 induction L with
 | nil=>rfl
 | cons a L ih =>
   rw [List.map_cons,List.sum_cons,h a (zYY ..),
     ih (fun b hb=>h b (zrw _ hb)),Nat.zero_add]
end
end a0C
end
section
namespace a0C
open scoped BigOperators Matrix
open private bhG ao5 from ProximityPrize.SubmissionLower.CG
open private av7 aPK ajw from ProximityPrize.SubmissionLower.CG
theorem glJ {α β F:Type*} [z85 α] [z85 β] [Field F]
    (M:z30 α β F) (P:α→Prop) (Q:β→Prop) [DecidablePred P] [DecidablePred Q]
    (cover : ∀ a b,M a b≠0→P a∨Q b) {n:ℕ}
    (v :z30 {a // P a} (Fin n) F) (pivot :Fin n → {a // P a})
    (hp:v.submatrix pivot id = 1)
    (rel : ∀ b,¬ Q b → ∀ i,(∑ a : {x // P x},M a.val b*v a i)=0) :
    M.rank+n≤zhP {a // P a} + zhP {b // Q b} := by
  classical
  let W := {a // P a} ⊕ {b // Q b}
  let A:z30 α W F:= fun a=>Sum.elim
    (fun i=>if i.val=a then 1 else 0) (fun j=>if P a then 0 else M a j.val)
  let B:z30 W β F:= fun i b=>i.elim
    (fun j=>M j.val b) (fun j=>if j.val=b then 1 else 0)
  have hAB:A*B=M:= by
    ext a b
    rw [zW3,zbt]
    simp only [A,B,Sum.elim_inl,Sum.elim_inr,ite_mul,mul_ite,
      one_mul,zero_mul,mul_one,mul_zero]
    rw [bhG P (fun i=>M i b),bhG Q (fun j=>if P a then 0 else M a j)]
    by_cases ha :P a
    · simp [ha]
    · by_cases hb:Q b
      · simp [ha,hb]
      · have hz :M a b=0:= by
          by_contra hn
          exact (cover a b hn).elim ha hb
        simp [ha,hb,hz]
  let V:z30 W (Fin n) F:= fun a i=>a.elim (fun p=>v p i)
    (fun j => -(∑ p : {x // P x},M p.val j.val*v p i))
  have hBV:B.transpose*V=0:= by
    ext b i
    rw [zW3,zbt,zTj]
    change (∑ a : {x // P x},M a.val b*v a i) +
      (∑ k : {x // Q x},(if k.val=b then (1 :F) else 0) *
        -(∑ a : {x // P x},M a.val k.val*v a i))=0
    simp only [ite_mul,one_mul,zero_mul]
    rw [bhG Q (fun k => -(∑ a : {x // P x},M a.val k*v a i))]
    by_cases hb:Q b
    · simp [hb]
    · simp [hb,rel b hb]
  have hr :=ju.cfv B.transpose V (Sum.inl ∘ pivot) hBV hp
  rw [zZo] at hr
  have hab:M.rank≤B.rank :=hAB ▸ zmg A B
  exact (zlr hab n).trans (hr.trans_eq Fintype.card_sum)
theorem glI {α β F:Type*} [z85 α] [z85 β] [Field F]
    (M:z30 α β F) (P:α→Prop) (Q:β→Prop) [DecidablePred P] [DecidablePred Q]
    (cover : ∀ a b,M a b≠0→P a∨Q b) (i:α) (j:β)
    (l:α→F) (v :β→F) (hi:l i=1) (hj:v j=1)
    (hsi:P i) (hsj:Q j)
    (hl : ∀ b,¬ Q b→(l ᵥ* M) b=0)
    (hv : ∀ a,¬ P a→(M *ᵥ v) a=0)
    (hp: (l ᵥ* M) ⬝ᵥ v=0) :
    M.rank+2≤zhP {a // P a} + zhP {b // Q b} := by
  classical
  let N :=M.updateRow i (l ᵥ* M)
  let T:=N.updateCol j (N *ᵥ v)
  have hT (a :α) (b:β) (hn:T a b≠0) :
      (P a∧a≠i)∨(Q b∧b≠j) := by
    by_contra! hc
    obtain ⟨ha,hb⟩:=hc
    apply hn
    by_cases hai:a=i
    · by_cases hbj:b=j
      · simp [T,N,hai,hbj,Matrix.updateRow_mulVec,hp]
      · simp [T,N,hai,hbj,hl b (fun h=>hbj (hb h))]
    · have hna := fun h=>hai (ha h)
      by_cases hbj:b=j
      · simp [T,N,hai,hbj,Matrix.updateRow_mulVec,hv a hna]
      · have hz :M a b=0:= by
          by_contra hm
          exact (cover a b hm).elim hna (fun h=>hbj (hb h))
        simp [T,N,hai,hbj,hz]
  have hr :=ao5 T _ _ hT
  rw [show T.rank=N.rank from aPK _ _ _ hj,
    show N.rank=M.rank from av7 _ _ _ hi] at hr
  have hdr :=ajw P i hsi
  have hdc:=ajw Q j hsj
  omega
end a0C
end
section
namespace aLy
open GO UO





abbrev b (s :Bool) :ℕ:=if s then 10 else 7
noncomputable section
end
end aLy
end
section
namespace bkt
open GO UO
open fP (qI aAr)
abbrev cV (s :Fin 3) :=109+s.val
abbrev d (s :Fin 3) :=iO (cV s)
abbrev h (s :Fin 3) :=DV (cV s) 3
abbrev b (s :Fin 3) :=15+3*s.val
abbrev f (s :Fin 3) :=4 - 2*s.val
set_option maxRecDepth 3500
set_option maxHeartbeats 1700000
private def part (d h:ℕ) (cs :List (ℕ×ℕ)) (start len:ℕ) :ℕ :=
 qI len fun i=>qI ((i+start)/2+1) fun c =>
  if OR cs (i+start) c then aEG d h 3 (i+start) c
  else aHb d 3 (i+start) c
private theorem dQz (d h tail a b c e total:ℕ) (cs :List (ℕ×ℕ))
  (hh:h=24+tail) (ha :part d h cs 0 8=a) (hb:part d h cs 8 8=b)
  (hc:part d h cs 16 8=c) (he :part d h cs 24 tail=e)
  (ht:a+b+c+e=total) :aht d h 3 (OR cs)=total:= by
 let g z :=qI (z/2+1) fun f =>
  if OR cs z f then aEG d h 3 z f else aHb d 3 z f
 change qI h g=total
 conv_lhs=>rw [hh,aAr 24 tail,aAr 16 8,aAr 8 8]
 change part d h cs 0 8+part d h cs 8 8+part d h cs 16 8+part d h cs 24 tail=total
 rw [ha,hb,hc,he,ht]
local notation "aa6" t "," a "," b "," c "," e =>
 dQz _ _ t a b c e _ _ rfl (by decide) (by decide) (by decide) (by decide) rfl
end bkt
end
section
namespace aLz
private def l:ℕ→List ℤ
 | 0=>[0x2814011b,0x60c778cc,0xca9d298,0x34c2c36e,0x35423b34,0x6791fa18,0x62f1b27c,0x37070c2d,0x223386c4,
     0x48bd6a71,0x6503887e,0x22197d9a,0x1a92db7b,0x39c157d7,0x17b77aff,0xfe3cb6a,0x716c0037,0x6983fa7e,
     0x6d6409b0,0x6370185f,0x7d33b6f5,0x5e3956c9,0x5f1c58e8,0x57fc74ba,0x4815c270,0x7e8ced19,0x64867c1f,
     0x319cff6c,0x72e5eefd,0x68ea230c,0x1190e96d,1998974,0x2e1bf42d,0x281daa4b,0x71773e66,0x5a218479,
     0x3166ad1f,0x58d14e93,0x448bb143,0x25bf07ac,0x599a7537,0x515ab6d4,0x2cd0d58b,0x70ae98e0,0x7569a7f8,
     0x3c957c69,0x31290f74,0x33e4988e,0x3946392d,0x7a050933,0xcee78b8,0x76eaf41a,0xbcbb0ba,0x1f2b4d9a,
     0x20c63e3e,0x395ad16a,0x2a5556f3,0xef0f09a,0x205f5f6b,0xc7ea290,0x395ad702,0x4c333327,1]
 | 1=>[0x3edfef5e,0x3e3decf4,0x69d34e7a,0x272a05d8,0x2beae7a2,0x156a5194,0x5a67cbce,0x13e7f652,0x4c271091,
     0x6a70804,0x34f7dc8c,0xe1d5483,0x4e600c32,0x4922b841,0x4e2cfe71,0x4dc8cca1,40810007,0x2eeac238,
     0x39c1619b,0x4c0dd1f5,0x40b6a171,0x3aa7bf31,0x64d0024e,0x33cb08fc,0xf358236,0x42e10b19,0x63216d6a,
     0x1e78da89,0x441eb710,0x365ffce8,0x5f8dcef3,0x5ed6a054,0x18592d4d,0x4ea395d4,0x7721356d,0x7150c581,
     0x40e35b13,0x3380e158,0x2f9fdc29,0x52fa2310,0x28ffce2d,0x48defac6,0x73a58c29,0x5bcba983,0xd2549c0,
     0x1ef2293e,0x2bd27b02,0x47b1b1dc,0x192a658b,0x4e9e810b,0x1b36d971,0x16adb73e,0x42d1fc9c,0x6182c63,
     0x2bb6eeec,0x26683d52,0x2d1085e5,0x91248b2,0x48924937,0x6dfdb6db,0x4d539d1a,0x1894a51f,1]
 | _=>[]
private def r :ℕ→List ℤ
 | 0=>[0x5711b109,0x63d3c56c,0x67a042f4,0x6e716e16,0x63adc9f9,76395436,0x58e66667,0x750f9527,0x66e7b726,
     0x54675aa3,0x4ab3849d,0x6e716e16,0x6cdb6db6,0x3f800004,0x3737a6f2,0x3f3fbf40,0x1be5420f,0x69b3ad52,
     0x7effffe3,48,0x3f7fffdb,0x1b9bd38c,0x3a3ab00c,0x5b5c143e,0x7efffd36,0x3f8002e7,0x659997f4,
     154,0x3cbd3785,0x63642c8a,0x3f7f528f,16445,0x7effec3d,0x19666b25,0x659998d0,0x659999ac,
     0,0,0,0,0,0,0,0,0,
     0,0,0,0,0,0,0,0,0,
     0x42230dd2,0x3e14c30b,0x4447d192,0x1c6753b4,0x30f22911,0x546e8c9d,0x58bb9efe,0x4495f7cd,0x49048a41,
     0x28a51d8b,0x648dc44,0x30679a3b,0x64ee7bf6,0x5f958ed3,0x6e58fc23,0x72dc2f82,0x3efb2569,0x46831f1e,
     0x44092493,0x5e57c57d,0x2adccccd,0x4d4de9be,55583646,0x7b20ab27,0x71649251,0x51a49243,0x48924928,
     0x5ab6db6e,0x58590b22,0x75f6e4af,0x4f6000dc,0x7effff7f,45,0x1966665d,1,0,
     0,0,0,0,0,0,0,0,0,
     0,0,0,0,0,0,0,0,0]
 | 1=>[0x7d5435e6,0x43ad7944,0x68152c46,0x153f09a0,0x772c24e1,0x55f8a486,0x250aaaaa,0x5f400003,0x765745d0,
     0x24492494,0x6cdb6db,0x153f09a0,0x5ab6db5e,0x648aaacd,0x2a555536,0x6222e8cc,0x576a63b9,0x1224924a,
     0x3f7ffee1,460,0x2f9ffe99,0x5f4000a7,0x5c5d171a,0x5c5d174c,0x34ea8fe7,0x2fa01bcc,0x7efff031,
     0x69d55b1a,0x7efffeb7,35,0x2f9981d6,0x34ed1249,0x2a5497ea,11638,0x2a554dc2,0x54aaab54,
     0,0,0,0,0,0,0,0,0,
     0,0,0,0,0,0,0,0,0,
     0x7d931eea,0xf6ec2f9,0x1739ea09,0x48a44294,0x7660d840,0x12775106,0x4b79d317,0xd17047e,0x5b59d317,
     0x57b0c30d,0x39925dad,0x64f3bcdf,0x47daf287,0x266f286d,0x4e8a1af2,0x7d066e3f,0x634eead,0x6ec454b2,
     0,0x31e4924c,0x27affffc,0x5f400004,0x1151745c,0x27959c43,0x2810c339,0x7d7cf3ae,0x60c30c37,
     0x60c30c37,0x54aaaaa8,0x7b26c9b4,0xfe00692,0x2f9ffc5a,0x3f800120,0x7effffd3,0,1,
     0,0,0,0,0,0,0,0,0,
     0,0,0,0,0,0,0,0,0]
 | 2=>[0x35308e4d,0x39869c41,0x73af4d6e,0x408140e0,0x2b13bfae,0x2327600e,0x46b745d2,0x103050f3,99338541,
     0x3aa8d5f0,93992908,0x408140e0,0x576a63be,0x40f1745e,0xc0c246d,0x1e473e76,0x626b81b1,0x1d546af8,
     96850289,0x5c5d174c,0x667745ce,0x5f8040c5,0x6e86ab48,77327111,0x1fbfffaf,0x4f600055,0x7effffd1,
     0x3f800012,0x26a6f4db,0x2828796d,0x4f5fec4b,0x1fc0074d,0x7efffdc2,138,0x7effffea,2,
     0,0,0,0,0,0,0,0,0,
     0,0,0,0,0,0,0,0,0,
     0x646c6597,0x3cefa521,0x63efad77,0x788b6cfb,0x1d48f6ab,0x6609c8c6,0x181dc7a8,0x13e9f729,0x28445fa6,
     0x57be732c,0x50a19118,0x5e7cbfd3,0x23655bde,0x6063acb6,0x65c4e2e,0x78f901af,0xa0c88bb,0x1e3e1eb1,
     0x195bd81b,0x59e3bd82,0x3e6ae8bb,0x5050f2d9,0x418ac916,0x162f4b64,0x4ba9f95d,0x5700d4c5,0x1c09f95c,
     0x27ca63bd,0x53943cb7,0x2f98b2d3,0x79f2e8ed,0x6505d15f,0x36d745d7,0x5c5d1746,0,0,
     0xfe00449,0x7efffebc,75,0x7efffff5,1,0,0,0,0,
     0,0,0,0,0,0,0,0,0]
 | _=>[]

end aLz
end
section
namespace bu
open fP (Ew)
open scoped BigOperators
noncomputable section
abbrev Ground :=ZMod P1.p
abbrev Exponent:=Fin 4 →₀ ℕ
abbrev gU (cut:ℕ) :=
 {m:Exponent // Ew 51 (cut:ℤ) 51 13 m}
instance cGU (cut:ℕ) :Finite (gU cut) :=
 ((Finsupp.finite_of_degree_le _).subset fun _ (h:Ew _ _ _ _ _) =>
   Nat.le_of_eq h.1).to_subtype
instance cGV (cut:ℕ) :z85 (gU cut) :=
 Fintype.ofFinite _
end
end bu
end
end
