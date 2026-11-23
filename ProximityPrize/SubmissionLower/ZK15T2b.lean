import ProximityPrize.SubmissionLower.ZlfuKwd
set_option Elab.async false
set_option maxHeartbeats 2000000
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qAxtVye
noncomputable section
open Polynomial




open gT (Ambient)
open pI (by6)
open YY (bAG)


open scoped BigOperators Classical
private theorem ePj:YY.c2 :=
 aBb.of_children czq.proof bzX.proof
private theorem co9 {I:Ideal Ambient} (h:by6 I) :bAG I :=
 ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩
private theorem interpolate {direct a low unit h x H E T:ℚ}
    (ha :a<direct) (hla :low≤a) (hE :0≤E) (hH :0≤H)
    (hunit : (direct-a)*unit≤(direct-low)*h)
    (hd:T≤direct*x) (hl:T≤low*x+unit*H+E) :
    T≤a*x+h*H+E := by
  let θ:=(direct-a)/(direct-low)
  have hden:0<direct-low:=sub_pos.mpr (hla.trans_lt ha)
  have hθ:0≤θ:=div_nonneg (sub_nonneg.mpr ha.le) hden.le
  have hθ₁:θ≤1 :=(div_le_one hden).mpr (sub_le_sub_left hla _)
  have hcoeff : (1-θ)*direct+θ*low=a := by
    dsimp only [θ]
    field_simp [hden.ne']
    ring
  have hscale :θ*unit≤h:= by
    dsimp only [θ]
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hden).mpr (by simpa only [mul_comm h] using hunit)
  calc
    T=(1-θ)*T+θ*T:= by ring
    _≤(1-θ)*(direct*x)+θ*(low*x+unit*H+E) :=
      add_le_add (mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr hθ₁))
        (mul_le_mul_of_nonneg_left hl hθ)
    _=a*x+(θ*unit)*H+θ*E := by rw [← hcoeff]; ring
    _≤_:=add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hscale hH))
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hθ₁ hE)
private theorem horizontalBase_mono {d cap:ℚ} (h:d≤ cap) (g:ℕ) :
  horizontalBase d g≤horizontalBase cap g:= by
 unfold horizontalBase
 linarith
end
end qAxtVye
end
section
set_option autoImplicit true
namespace qAxtVye
open P5 (p)
open P5_7 (midAgreement)
open P5_7_3 (fO stages terminal O2)
open cu (Shape)
private abbrev bQj (hi r :ℕ) (s :Shape) :Prop :=
 2≤ s.B∧0<s.J∧s.J≤ s.B∧s.B<p∧s.U<p ∧
   0<s.m*midAgreement∧2*hi*r≤O2 s
private theorem bVm {hi r :ℕ} {s :Shape} (h:bQj hi r s) :
  am1 hi r s := by
 obtain ⟨hb,hj,hjb,hbp,hu,hm,hr⟩:=h
 exact ⟨⟨hb,hj,hjb,hbp⟩,hu,hm,hr⟩
private abbrev a1d (b:fO) (i:ℕ) :Prop :=
 let s :=nV b i
 s.dI<p∧(i=0∨0<s.dI) ∧
  bQj b.jX.hi s.dI s.free.shape∧bQj b.jX.hi s.dI s.moving.shape
private theorem guH (b:fO) :
  (List.range (stages b).length).all (fun i=>decide (a1d b i))=true := by
 cases b <;> rfl
private theorem bOp {b:fO} {i:ℕ} (hi:i<(stages b).length) :
  a1d b i :=
 of_decide_eq_true (List.all_eq_true.mp (guH b) i (List.mem_range.mpr hi))
theorem aXU (b:fO) :0<(stages b).length:= by
 cases b <;> decide
theorem fWx (b:fO) : (nV b 0).dI=0:= by
 cases b <;> rfl
theorem bIj (b:fO) (i:ℕ) (hi:i<Fo b) :
  0<(nV b (i+1)).dI:= by
 have hi' : i+1<(stages b).length:= by unfold Fo at hi; omega
 exact (bOp hi').2.1.resolve_left (Nat.succ_ne_zero i)
theorem bN7 (b:fO) (i:ℕ) (hi:i<(stages b).length) :
   (nV b i).dI<p :=
 (bOp hi).1
private theorem eo3 (b:fO) :
  (RU b).all (fun i=>decide (0< i∧i<(stages b).length))=true := by
 cases b <;> rfl
theorem brd (b:fO) (i:ℕ) (hi:i∈RU b) :
  0< i∧i<(stages b).length :=
 of_decide_eq_true (List.all_eq_true.mp (eo3 b) i hi)
private theorem b6r (b:fO) : (RU b).Pairwise (· < ·) := by
 cases b <;> decide
private theorem aE7 (b:fO) (i:ℕ) (hi:i<(stages b).length) :
   let s :=nV b i
   am1 b.jX.hi s.dI s.free.shape∧am1 b.jX.hi s.dI s.moving.shape :=
 ⟨bVm (bOp hi).2.2.1,bVm (bOp hi).2.2.2⟩
private theorem bxE (b:fO) :am1 b.jX.hi 0 (terminal b).shape := by
 apply bVm
 cases b <;> decide
private theorem bq6 (b:fO) (k :Fin 4) :BC b k<p:= by
 cases b <;> fin_cases k <;> decide
private theorem bDl (b:fO) :
  (nV b 0).free.shape.U + (nV b 0).moving.shape.U<p:= by
 cases b <;> decide
private theorem bK5 (b:fO) :aBh (BC b 2) (BC b 1) := by
 cases b <;> exact ⟨by decide,by decide,by decide,by decide⟩
theorem schedule (b:fO) :aqE b :=
 ⟨aXU b,fWx b,bIj b,bN7 b,brd b,b6r b,
   aE7 b,bxE b,bq6 b,bDl b,bK5 b⟩
end qAxtVye
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
namespace qAxtVye
noncomputable section
open Polynomial

open P5_7 (Qn)
open P5_7_3 (fO Jr stages O2 anM aRe)

open cu (Shape vP Jet)
open gT (Ambient iJ)
open pI (NO)
open ac2
open ac3
open private dfc ddV from ProximityPrize.SubmissionLower.U




open scoped BigOperators Classical
abbrev afa (b:fO) :=Fin (stages b).length
def arS {b h rows} (pairs :P5_7_3.Pairs b h rows) (i:afa b) :
    P5_7_3.akE h rows (nV b i) :=
  pairs _ (cqz i.isLt)
theorem aU2 {b:fO} (i:afa b) :Jr b (nV b i).free :=
 Or.inr (Or.inl ⟨_,cqz i.isLt,Or.inl rfl⟩)
theorem a5S {b:fO} (i:afa b) :Jr b (nV b i).moving :=
 Or.inr (Or.inl ⟨_,cqz i.isLt,Or.inr rfl⟩)
private theorem cDJ {b:fO} {w:ℤ} (hw:Qn b.jX.lo b.jX.hi w) {r :ℕ} {s :Shape}
  (guard :am1 b.jX.hi r s) :
  anM w.toNat r s+2*w.toNat*r≤O2 s := by
 have h:=Nat.mul_le_mul_right r (Nat.mul_le_mul_left 2 (aRe (b:=b) hw).2)
 have h' := h.trans guard.buffer
 unfold anM
 omega
structure bQX {b h rows} (pairs :P5_7_3.Pairs b h rows) (i:afa b) where
 free :NO (arS pairs i).free (nV b i).free.shape
 moving:NO (arS pairs i).moving (nV b i).moving.shape
private theorem ddZ {A:Type*} [CommRing A] (a :cu.aZ →+* A)
  {rows :vP} {s :Shape} {I:Ideal Ambient} {h W r :ℕ} {P:Jet}
  (hn : ∀ W W',W≤W' → rows s W≤ rows s W')
  (hs :qQ.bk4 h rows s) (hv :agA rows s I)
  (hcut:W+2*h*r≤O2 s) (hP:P∈rows s W) :
  bp3 (I.map (Ih a)) (Ih a (iJ P)) r := by
 intro t ht
 rw [← dfc]
 apply Ideal.mem_map_of_mem
 exact hv _ (hn _ _ ((Nat.add_le_add_left (Nat.mul_le_mul_left _ ht) _).trans hcut)
  (ddV hs hP t))
end
end qAxtVye
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
namespace qAxtVye
noncomputable section


open P5_7_3 (fO Pairs terminal)

open gT (Ambient)
open pI (xN dM dual aaS)

open scoped Classical
def nextIndex {b:fO} (i:ℕ) (hi:i<Fo b) :afa b :=
 ⟨i+1,by unfold Fo at hi; omega⟩
structure Process {b h rows} (pairs :Pairs b h rows) where
 sched:aqE b
 parents :Finset (Ideal Ambient)
 fixed : ∀ i:afa b,bQX pairs i
 DN : ∀ I∈parents,xN I∧I.height=2
 init_mass :dM parents (BC b)
def Process.Clean {b h rows} {pairs :Pairs b h rows} (R:Process pairs)
    (I:Ideal Ambient) :Prop :=
  ∀ i,¬ aaS (R.fixed i).free.equation I ∧ ¬ aaS (R.fixed i).moving.equation I
def passes {b h rows} (pairs :Pairs b h rows) (i:ℕ) (I:Ideal Ambient) :Prop :=
 if hi:i<Fo b then axS (arS pairs (nextIndex i hi)) I
 else agA rows (terminal b).shape I
def Process.Bp {b h rows} {pairs :Pairs b h rows} (R:Process pairs) :
    ℕ→Finset (Ideal Ambient)
  | 0=>R.parents.filter fun I=>R.Clean I∧dual I
  | i+1=>(R.Bp i).filter (passes pairs i)
def Process.Hj {b h rows} {pairs :Pairs b h rows} (R:Process pairs) (i:ℕ) :
    Finset (Ideal Ambient) :=
  R.Bp i \ R.Bp (i+1)
abbrev Process.final {b h rows} {pairs :Pairs b h rows} (R:Process pairs) :=
 R.Bp (Fo b+1)
def Process.aWI {b h rows} {pairs :Pairs b h rows} (R:Process pairs) :
    Finset (Ideal Ambient) :=
  R.parents.filter fun I => ¬ dual I
theorem Process.eEO {b h rows} {pairs :Pairs b h rows} (R:Process pairs)
  (i:ℕ) :R.Bp (i+1)⊆R.Bp i :=
 Finset.filter_subset _ _
theorem Process.a4R {b h rows} {pairs :Pairs b h rows} (R:Process pairs)
   (i:ℕ) :R.Bp i⊆R.parents := by
 induction i with
 | zero=>exact Finset.filter_subset _ _
 | succ i ih=>exact (R.eEO i).trans ih
theorem Process.kept_clean {b h rows} {pairs :Pairs b h rows} (R:Process pairs)
   (i:ℕ) {I:Ideal Ambient} (hI:I∈R.Bp i) :R.Clean I∧dual I:= by
 induction i with
 | zero=>exact (Finset.mem_filter.mp hI).2
 | succ i ih=>exact ih (R.eEO i hI)
theorem Process.fXs {b h rows} {pairs :Pairs b h rows} (R:Process pairs)
  {I:Ideal Ambient} (hI:I∈R.parents) (hc:R.Clean I)
  (hrank :I∉R.aWI) (hlost : ∀ i≤Fo b,I∉R.Hj i) :
  I∈R.final:= by
 have hd:dual I:= by
  by_contra hn
  exact hrank (Finset.mem_filter.mpr ⟨hI,hn⟩)
 have keep : ∀ i≤Fo b+1,I∈R.Bp i:= by
  intro i hi
  induction i with
  | zero=>exact Finset.mem_filter.mpr ⟨hI,hc,hd⟩
  | succ i ih =>
    by_contra hn
    exact hlost i (by omega) (Finset.mem_sdiff.mpr ⟨ih (by omega),hn⟩)
 exact keep _ le_rfl
theorem Process.terminal {b h rows} {pairs :Pairs b h rows} (R:Process pairs)
  {I:Ideal Ambient} (hI:I∈R.final) :agA rows (terminal b).shape I:= by
 have hp:=(Finset.mem_filter.mp hI).2
 simpa only [passes,dite_eq_right (Nat.lt_irrefl _)] using hp
end
end qAxtVye
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qAxtVye
noncomputable section


open P5_7_3 (fO)
open TD (J2)

open gT (Ambient)
open pI (mass weight dot)
open scoped Classical BigOperators
def bDZ (b:fO) (i:ℕ) :ℚ :=
 min (ash b) (FP (SS b 0 i) (V8 b i))
private theorem kG (b:fO) (bw:Fin 3) (i:ℕ) (S:Finset (Ideal Ambient)) :
  (dot (weight (aHp b i) bw) (mass S) :ℚ) =
    FP (SS b bw i) (J2 S) := by
 simp only [FP,dot,SS,J2,Nat.cast_sum,Nat.cast_mul]
private theorem enb (b:fO) (i:ℕ) (k :Fin 4) :
   V8 b i k≤V8 b 0 k := by
 induction i with
 | zero=>exact le_rfl
 | succ i ih=>exact (min_le_left _ _).trans ih
end
end qAxtVye
end
