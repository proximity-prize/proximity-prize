import ProximityPrize.SubmissionLower.ZeFfOZc
import ProximityPrize.SubmissionLower.A
set_option Elab.async false
set_option autoImplicit true
section
namespace jQ
open Finset agU
private theorem a6V (n a b:ℕ) :
   6*(∑ i∈range n,(a+i)*(b+i))=a6U n a b:= by
 induction n with
 | zero=>simp [a6U]
 | succ n ih =>
   rw [sum_range_succ,Nat.mul_add,ih]
   cases n with
   | zero=>simp [a6U,Nat.mul_assoc]
   | succ m=>simp only [a6U,Nat.succ_sub_one]; ring
private theorem count_sum (n:ℕ) :
   6*(∑ i∈range n,(i+1))=3*n*(n+1) := by
 induction n with
 | zero=>simp
 | succ n ih=>rw [sum_range_succ,Nat.mul_add,ih]; ring
private theorem cry (f :ℕ→ℕ) (N s :ℕ) (hz : ∀ q<s,f q=0) :
   (∑ q∈range N,f q) = ∑ i∈range (N-s),f (s+i) := by
 by_cases h:s≤N
 · conv_lhs=>rw [← Nat.add_sub_of_le h,sum_range_add]
   rw [sum_eq_zero (fun q hq=>hz q (mem_range.mp hq)),zero_add]
 · rw [Nat.sub_eq_zero_of_le (by omega :N≤ s),sum_range_zero]
   exact sum_eq_zero fun q hq=>hz q (by have :=mem_range.mp hq; omega)
private theorem fSV (N a :ℕ) :
  6*(∑ q∈range N,Fu a q)=buF N a := by
 rw [cry (Fu a) N a (fun q hq=> by unfold Fu; omega)]
 unfold buF
 rw [← count_sum]
 congr 1
 exact sum_congr rfl fun i _=> by unfold Fu; omega
private theorem fSX (N a :ℕ) :
  6*(∑ q∈range N,q*Fu a q)=bK1 N a := by
 rw [cry (fun q=>q*Fu a q) N a
  (fun q hq=> by rw [show Fu a q=0 by unfold Fu; omega,mul_zero])]
 unfold bK1
 rw [← a6V]
 congr 1
 exact sum_congr rfl fun i _=> by
  rw [show Fu a (a+i)=1+i by unfold Fu; omega]
private theorem fSW (N k a :ℕ) :
  6*(∑ q∈range N,(q-k)*Fu a q)=cem N k a := by
 let s :=max (k+1) a
 have hs₁:k+1≤ s :=le_max_left _ _
 have hs₂:a≤ s :=le_max_right _ _
 have hz (q:ℕ) (hq:q<s) : (q-k)*Fu a q=0:= by
  by_cases h:q≤k
  · rw [Nat.sub_eq_zero_of_le h,zero_mul]
  · rw [show Fu a q=0 by dsimp [s,Fu] at *; omega,mul_zero]
 rw [cry _ N s hz]
 change _=a6U (N-s) (s-k) (s+1-a)
 rw [← a6V]
 congr 1
 exact sum_congr rfl fun i _=> by
  rw [show s+i-k=s-k+i by omega,show Fu a (s+i)=s+1-a+i by unfold Fu; omega]
private theorem cG0 (B J t q:ℕ) :
  Bb B J t q+Fu (low J t+width B J t) q=Fu (low J t) q:= by
 unfold Bb Fu width low high
 dsimp only
 omega
private theorem eLv (B J t q:ℕ) :
    Xq B J t q+Fu (low J t+aoF B J t) q +
      Fu (edge B J t+1-aoF B J t) q =
        Fu (low J t) q+Fu (edge B J t+1) q:= by
  have hc:=cG0 B J t q
  let a :=low J t
  let e :=edge B J t
  let w:=width B J t
  let h:=aoF B J t
  change Bb B J t q+Fu (a+w) q=Fu a q at hc
  have hae :a≤e := by dsimp [a,e,low,edge]; omega
  have hh:h=min w ((e-a+1)/2) :=rfl
  have hp:Xq B J t q=min (Bb B J t q) (e-q) := by
    unfold Xq
    rw [show B+2*J-(t+q)=e-q by dsimp [e,edge]; omega]
  change Xq B J t q+Fu (a+h) q+Fu (e+1-h) q =
    Fu a q+Fu (e+1) q
  simp only [Fu] at hc ⊢
  by_cases hq:q<a+h
  · omega
  · by_cases hq' : q<e+1-h
    · omega
    · omega
private theorem c39 (B J t:ℕ) (f stat :ℕ→ℕ)
    (hs : ∀ a,stat a=6*(∑ q∈range (B+1),f q*Fu a q)) :
    6*(∑ q∈range (B+1),f q*Xq B J t q)=bKt B J t stat := by
  unfold bKt
  simp only [hs]
  have heq :
      (∑ q∈range (B+1),(f q*Xq B J t q+f q*Fu (low J t+aoF B J t) q +
        f q*Fu (edge B J t+1-aoF B J t) q)) =
      ∑ q∈range (B+1),(f q*Fu (low J t) q+f q*Fu (edge B J t+1) q) := by
    apply sum_congr rfl
    intro q _
    simp only [← Nat.mul_add,eLv]
  simp only [sum_add_distrib] at heq
  omega
private theorem dNO (B J t:ℕ) (f stat :ℕ→ℕ)
  (hs : ∀ a,stat a=6*(∑ q∈range (B+1),f q*Fu a q)) :
  6*(∑ q∈range (B+1),f q*Bb B J t q)=bC6 B J t stat := by
 unfold bC6
 simp only [hs]
 have heq :
    (∑ q∈range (B+1),(f q*Bb B J t q+f q*Fu (low J t+width B J t) q)) =
    ∑ q∈range (B+1),f q*Fu (low J t) q:= by
  apply sum_congr rfl
  intro q _
  rw [← Nat.mul_add,cG0]
 simp only [sum_add_distrib] at heq
 omega
theorem eLt (B J t:ℕ) :
  6*(∑ q∈range (B+1),Xq B J t q)=btD B J t:= by
 simpa only [one_mul,btD] using
  c39 B J t (fun _=>1) (buF (B+1))
    (fun a=> by simpa only [one_mul] using (fSV (B+1) a).symm)
theorem eLw (B J t:ℕ) :
  6*(∑ q∈range (B+1),q*Xq B J t q)=cbP B J t :=
 c39 B J t id (bK1 (B+1)) (fun a=>(fSX (B+1) a).symm)
theorem dNJ (B J t k :ℕ) :
  6*(∑ q∈range (B+1),(q-k)*Bb B J t q)=b2e B J t k :=
 dNO B J t (fun q=>q-k) (cem (B+1) k)
  (fun a=>(fSW (B+1) k a).symm)
private theorem gBz (B J t:ℕ) :threshold B J t≤B:= by
 dsimp only [threshold]
 split
 · exact Nat.sub_le _ _
 · exact min_le_left _ _
theorem eF5 (B J t:ℕ) :aDY B J t≤ c2b B J t:= by
 let k :=threshold B J t
 let R := ∑ q∈range (B+1),Xq B J t q
 let W := ∑ q∈range (B+1),q*Xq B J t q
 let E := ∑ q∈range (B+1),(q-k)*Bb B J t q
 have hk :k∈range (B+1) :=mem_range.mpr (Nat.lt_succ_of_le (gBz B J t))
 have htop:aVz B J t R≤R*k+E := by
  unfold aVz
  exact inf'_le _ hk
 change aVz B J t R-W ≤
  (btD B J t*k+b2e B J t k - cbP B J t)/6
 rw [← eLt,← eLw,← dNJ]
 change aVz B J t R-W≤(6*R*k+6*E-6*W)/6
 rw [Nat.mul_assoc,← Nat.mul_add,← Nat.mul_sub_left_distrib,Nat.mul_div_cancel_left _ (by decide)]
 exact Nat.sub_le_sub_right htop W
theorem aNC (f :ℕ→ℕ) (n:ℕ) :m8 f n = ∑ t∈range n,f t:= by
 induction n with
 | zero=>simp [m8]
 | succ n ih=>rw [m8,sum_range_succ,ih]
private theorem eGc (B J t:ℕ) (ht:t<J) :aDY B J t=0:= by
  have hp (q:ℕ) (hq:q∈range (B+1)) :Xq B J t q=Bb B J t q:= by
    have hq' := mem_range.mp hq
    have hc:Bb B J t q≤t+1 := by
      dsimp only [Bb]
      omega
    exact min_eq_left (hc.trans (by omega))
  unfold aDY
  dsimp only
  apply Nat.sub_eq_zero_of_le
  calc
    _≤(∑ q∈range (B+1),Xq B J t q)*0 +
        ∑ q∈range (B+1),(q-0)*Bb B J t q:= by
      unfold aVz
      exact inf'_le _ (mem_range.mpr (Nat.zero_lt_succ B))
    _ = _:= by
      simp only [mul_zero,Nat.sub_zero,zero_add]
      exact sum_congr rfl fun q hq=>congrArg (q * ·) (hp q hq).symm
theorem cUo (B J:ℕ) :ajD B J≤eE B J:= by
 rw [eE,lT,aNC,ajD,
  show B+2*J=J+(B+J) by omega,sum_range_add,
  sum_eq_zero (fun t ht=>eGc B J t (mem_range.mp ht)),zero_add]
 exact sum_le_sum fun t _=>eF5 B J (J+t)
theorem d3l {f :ℕ→ℕ} {a b n x y z :ℕ}
  (ha :m8 f a=x) (hb:m8 (fun t=>f (a+t)) b=y)
  (hn:a+b=n) (hz :x+y=z) :m8 f n=z := by
 rw [← hn,← hz]
 have h:=sum_range_add f a b
 simp only [← aNC] at h
 exact h.trans (congrArg₂ (· + ·) ha hb)
theorem dn {B J start next a b n x y z :ℕ}
  (ha :lT B J start a=x) (hb:lT B J next b=y)
  (hs :start+a=next) (hn:a+b=n) (hz :x+y=z) :
  lT B J start n=z := by
 unfold lT at *
 rw [← hs] at hb
 exact d3l ha (by simpa only [Nat.add_assoc] using hb) hn hz
end jQ
end
section
namespace aeL
noncomputable section
open Polynomial
open cu (Shape)
open Ge anc
open agU (Bb Xq)
open scoped BigOperators Polynomial
abbrev Offset (s :Shape) :=Fin (s.B+2*s.J)
def Gv (s :Shape) (t:Offset s) :ℕ:=s.J - t.val
def aIN (s :Shape) (t:Offset s) (q:jJ s) :ℕ :=
 s.B+2*s.J-(t.val+q.val)
abbrev Lh (s :Shape) (t:Offset s) :=
 Σ q:jJ s,Fin (Bb s.B s.J t.val q.val)
abbrev Pivot (s :Shape) (t:Offset s) :=
 Σ q:jJ s,Fin (Xq s.B s.J t.val q.val)
def a2N {s :Shape} {t:Offset s} (u:Lh s t) :ℕ :=
 Gv s t+u.2.val
def dNE {s :Shape} {t:Offset s} (u:Lh s t) :ℕ :=
 t.val+a2N u - s.J
def btx {R:Type} [Semiring R] (l n h:ℕ) :
    Matrix (Fin (min n h)) (Fin n) R :=
  fun i j=>((l+j.val).choose i.val :R)
def bTl (F:Type) [Field F] (l n h:ℕ) :Prop :=
  ∀ i<h,∃ w:Fin (min n h)→F,∀ j:Fin n,
    ((l+j.val).choose i:F) = ∑ r,w r*btx l n h r j
def dqg (F:Type) [Field F] (l n h:ℕ) :Prop :=
  ∃ e :Fin (min n h) ↪ Fin n,
    ((btx (R:=F) l n h).submatrix id e).det≠0
def Pa {R:Type} [CommSemiring R] (s :Shape) (t:Offset s) (z :R) :
    Matrix (Pivot s t) (Lh s t) R :=
  fun r u =>
    let j:=a2N u
    if r.1.val≤u.1.val∧j≤ r.1.val then
      ((j.choose r.2.val :R)*((u.1.val - j).choose (r.1.val - j) :R)) *
        z^(u.1.val - r.1.val)
    else 0
def input {F:Type} [Field F] (α:F) {s :Shape} {t:Offset s} (u:Lh s t) :
    Gm F →ₗ[F] i5 F :=
  b6l α (a2N u) (u.1.val-a2N u) (dNE u)
abbrev Ru (F:Type) [Field F] :=FractionRing F[X]
def a6h {F:Type} [Field F] (a b c:F) :Ru F :=
  let z :=algebraMap F[X] (Ru F) Polynomial.X
  algebraMap F (Ru F) a*z /
    (algebraMap F (Ru F) b+algebraMap F (Ru F) c*z)
def bQp {F ι κ:Type} [Field F] [Fintype ι] [DecidableEq ι]
    (M:Matrix ι κ (Ru F)) (D:ℕ) :Prop :=
  (∃ e :ι ↪ κ,(M.submatrix id e).det≠0) ∧
  ∃ scale :Ru F,scale≠0 ∧
    ∀ e :ι ↪ κ,∃ g:F[X],g.natDegree≤D ∧
      algebraMap F[X] (Ru F) g=scale*(M.submatrix id e).det
end
end aeL
end
section
namespace aF8
open jQ (lT dn eE)
def bi6 (B J:ℕ) :ℕ→List (ℕ×ℕ)→Prop
  | _,[]=>True
  | start,(length,total) :: rest =>
    lT B J start length=total∧bi6 B J (start+length) rest
private theorem dzv {B J:ℕ} (blocks :List (ℕ×ℕ)) (start:ℕ)
   (checked :bi6 B J start blocks) :
   lT B J start (blocks.map Prod.fst).sum=(blocks.map Prod.snd).sum:= by
 induction blocks generalizing start with
 | nil=>rfl
 | cons head tail ih =>
   obtain ⟨length,total⟩:=head
   exact dn checked.1 (ih _ checked.2) rfl rfl rfl
theorem CH {B J total:ℕ} (blocks :List (ℕ×ℕ))
  (checked :bi6 B J J blocks)
  (length_eq : (blocks.map Prod.fst).sum=B+J)
  (asB: (blocks.map Prod.snd).sum=total) :
  eE B J=total:= by
 rw [eE,← length_eq,← asB]
 exact dzv blocks J checked
class Ct (B J total:ℕ) :Prop where
 eq_moment:eE B J=total
end aF8
end
