import ProximityPrize.SubmissionLower.P5_7_1_3_1Proof
import ProximityPrize.SubmissionLower.ZbnhR9d
set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qd1cKFc
noncomputable section
open P6 (dw)
open qFAh60c
open aR (ao)
open jA Polynomial
open Finset (range mem_range mul_sum sum_congr)
open scoped BigOperators
open private exponent exponent_none exponent_zero bpQ d5n from ProximityPrize.SubmissionLower.B9
open private sum_coeffs from ProximityPrize.SubmissionLower.ZTFKldb
open private Lh Ac auD column column_mem cGZ finite_ambient b6S box_bounds bw6 integral24 sum_poly row slice qMNQHHc.width qMNQHHc.start from ProximityPrize.SubmissionLower.P5_7_1_3_1Proof
private def start (b:Bank) :ℕ:=b.m*dw - 131071*b.box.b
private theorem start_eq (b:Bank) :start b+131071*b.box.b=cut b+1 := by
  cases b <;> decide
private abbrev delta :ℕ:=400
private theorem acI (b:Bank) :width b≤b.U:= by cases b <;> decide
private theorem ds8 (b:Bank) (h:ℕ) :
    Aw b h (cut b)≤qlc9qed.Aw b (h+delta) b.cut:= by
  have hc:cut b≤b.cut+b.box.j*delta := by cases b <;> decide
  intro F hF
  obtain ⟨hcap,hs,ht⟩:=mem_ambient.mp hF
  refine qlc9qed.mem_ambient.mpr ⟨hcap,hs.trans (acI b),fun a ha => ?_⟩
  have hw:=ht a ha
  have hg:=(MvPolynomial.le_weightedTotalDegree (fun i:mA=>i.elim 0 (fun _=>1))
    ha).trans hcap.1
  rw [b6S] at hg
  simp only [one_mul] at hg
  have he (i:Fin 3) :131071+(h+delta) - i.val=(131071+h-i.val)+delta := by
    have :=i.isLt
    omega
  rw [sum_coeffs] at hw ⊢
  simp only [he,Nat.add_mul,Nat.mul_add] at hw ⊢
  dsimp only [delta] at hc ⊢
  omega
private def columnsAt (b:Bank) (h k j d:ℕ) :ℕ :=
  start b+131071*d+j+2*k+(b.box.j+d)*h
private theorem columns_le (b:Bank) (h k j d:ℕ) :
    columnsAt b h k j d≤qMNQHHc.width b (h+delta) k j d:= by
  have hs :start b≤qMNQHHc.start b+b.box.j*delta := by cases b <;> decide
  simp only [columnsAt,qMNQHHc.width,Nat.mul_add,Nat.add_mul]
  dsimp only [delta] at hs ⊢
  omega
private abbrev aiz (b:Bank) (h:ℕ) :=
  Σ k :Fin (b.box.t+1),Σ j:Fin (b.box.j-2*k.val+1),
    Σ d:Fin (b.box.b-k.val-j.val+1),Fin (columnsAt b h k j d)×Fin (width b+1)
private def cLB (b:Bank) (h:ℕ) :aiz b h ↪ Lh b (h+delta) :=
  .sigmaMap (.refl _) fun k => .sigmaMap (.refl _) fun j => .sigmaMap (.refl _) fun d =>
    .prodMap (Fin.castLEEmb (columns_le b h k j d))
      (Fin.castLEEmb (Nat.add_le_add_right (acI b) 1))
set_option maxRecDepth 2048 in
private theorem mem_column {b h} (c:aiz b h) :
    column (cLB b h c)∈Aw b h (cut b) := by
  classical
  have hc:=(qlc9qed.mem_ambient.mp (column_mem (cLB b h c))).1
  have hs (a :mA →₀ ℕ) (ha :a∈(column (cLB b h c)).support) :
      a=Ac (cLB b h c) :=
    Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ha)
  obtain ⟨k,j,d,x,u⟩:=c
  have ⟨hTJ,hJB,_⟩:=box_bounds b
  have hk :=k.isLt
  have hj:=j.isLt
  have hd:=d.isLt
  let i:=b.box.b - k.val - j.val - d.val
  have hg:i+j.val+k.val+d.val=b.box.b:= by dsimp [i]; omega
  have hw :
      (131071+h)*i+(131071+h-1)*j.val+(131071+h-2)*k.val +
        (j.val+2*k.val)+131071*d.val+d.val*h =
      131071*b.box.b+b.box.b*h:= by
    have h1 :131071+h-1+1=131071+h:= by omega
    have h2 :131071+h-2+2=131071+h:= by omega
    calc
      _=(131071+h)*i+(131071+h-1+1)*j.val+(131071+h-2+2)*k.val +
          (131071+h)*d.val := by ring
      _ = _:= by rw [h1,h2,← Nat.mul_add,← Nat.mul_add,← Nat.mul_add,hg,
        Nat.add_mul,Nat.mul_comm h]
  have he :Ac (cLB b h ⟨k,j,d,x,u⟩)=exponent u.val i j.val k.val :=rfl
  have hxval : @auD b (h+delta) (cLB b h ⟨k,j,d,x,u⟩)=x.val := by
    simp only [auD,cLB,Function.Embedding.sigmaMap,Function.Embedding.refl,
      Function.Embedding.coeFn_mk,Sigma.map_mk,id_eq,Function.Embedding.coe_prodMap,
      Prod.map_fst,Fin.coe_castLEEmb,Fin.val_castLE]
  refine mem_ambient.mpr ⟨hc,MvPolynomial.degreeOf_le_iff.mpr ?_,?_⟩
  · intro a ha
    rw [hs a ha,he,exponent_none]
    exact Nat.le_of_lt_succ u.isLt
  · intro a ha
    rw [hs a ha,sum_coeffs,column,MvPolynomial.coeff_monomial,ite_eq_left rfl,
      Polynomial.natDegree_monomial_eq _ one_ne_zero,he,exponent_zero,bpQ,d5n]
    simp only [hxval,Fin.val_zero,Fin.val_one,Fin.val_two,Nat.sub_zero]
    have hx :x.val<start b+131071*d.val+j.val+2*k.val +
        (b.box.j*h+d.val*h) := by
      simpa only [columnsAt,Nat.add_mul] using x.isLt
    rw [Nat.add_mul b.box.b b.box.j h]
    have hstart:=start_eq b
    omega
private theorem width_count (b:Bank) (h:ℕ) :
    (∑ k∈range (b.box.t+1),∑ j∈range (b.box.j-2*k+1),
      ∑ d∈range (b.box.b-k-j+1),columnsAt b h k j d) =
      az0 b+b.basePole*h:= by
  let B:=b.box.b
  let J:=b.box.j
  let a :ℤ:=(start b:ℤ)+J*(h:ℤ)
  let s :ℤ:=131071+(h:ℤ)
  have hr (k :ℕ) (hk :k∈range (b.box.t+1)) :
      48*(∑ j∈range (J-2*k+1),∑ d∈range (B-k-j+1),
        (columnsAt b h k j d:ℤ))=slice B J a s k := by
    have hk' := mem_range.mp hk
    obtain ⟨hTJ,hJB,_⟩:=box_bounds b
    change 2*b.box.t≤J at hTJ
    change J≤B at hJB
    have hkJ:2*k≤J:= by omega
    rw [show (48:ℤ)=24*2 by decide,mul_assoc,mul_sum]
    have hj (j:ℕ) (hj:j∈range (J-2*k+1)) :
        2*(∑ d∈range (B-k-j+1),(columnsAt b h k j d:ℤ))=row B a s k j:= by
      have hj' := mem_range.mp hj
      have hkB:k≤B:= by omega
      have hjB:j≤B-k := by omega
      have hw (d:ℕ) : (columnsAt b h k j d:ℤ)=a+j+2*k+s*d:= by
        simp only [columnsAt,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
        dsimp [a,s,J]
        ring
      simp only [hw]
      rw [bw6,row,Nat.cast_add,Nat.cast_one,Nat.cast_sub hjB,Nat.cast_sub hkB]
      ring
    rw [sum_congr rfl hj,sum_poly (row B a s k) (by intro i; unfold row; ring),slice]
    rw [Nat.cast_add,Nat.cast_one,Nat.cast_sub hkJ,Nat.cast_mul,Nat.cast_ofNat]
    ring
  have hsum :
      1152*(∑ k∈range (b.box.t+1),∑ j∈range (J-2*k+1),
        ∑ d∈range (B-k-j+1),(columnsAt b h k j d:ℤ)) =
      integral24 (slice B J a s) (b.box.t+1 :ℕ) := by
    rw [show (1152:ℤ)=24*48 by decide,mul_assoc,mul_sum,sum_congr rfl hr]
    exact sum_poly (slice B J a s) (by intro i; unfold slice integral24 row; ring) _
  have hc:integral24 (slice B J a s) (b.box.t+1 :ℕ) =
      1152*((az0 b:ℤ)+b.basePole*(h:ℤ)) := by
    cases b <;>
      simp only [a,s,B,J,start,qlc9qed.Bank.m,qlc9qed.Bank.box,az0,
        qlc9qed.Bank.basePole,Nat.cast_sub (show 131071*87≤64*dw by decide),
        Nat.cast_sub (show 131071*164≤120*dw by decide),Nat.cast_add,
        Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] <;>
      unfold integral24 slice integral24 row <;> ring
  rw [hc] at hsum
  exact_mod_cast (show (∑ k∈range (b.box.t+1),∑ j∈range (J-2*k+1),
    ∑ d∈range (B-k-j+1),(columnsAt b h k j d:ℤ)) =
      (az0 b:ℤ)+b.basePole*(h:ℤ) by omega)
private theorem column_card (b:Bank) (h:ℕ) :
    Fintype.card (aiz b h)=ambientCount b h:= by
  simp only [aiz,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,
    Nat.mul_comm _ (width b+1),← Finset.mul_sum]
  unfold ambientCount
  congr 1
  calc
    _ = ∑ k∈range (b.box.t+1),∑ j∈range (b.box.j-2*k+1),
        ∑ d∈range (b.box.b-k-j+1),columnsAt b h k j d:= by
      rw [← Fin.sum_univ_eq_sum_range]
      refine sum_congr rfl fun k _ => ?_
      rw [← Fin.sum_univ_eq_sum_range]
      refine sum_congr rfl fun j _ => ?_
      rw [← Fin.sum_univ_eq_sum_range]
    _ = _:=width_count b h
theorem proof :qFAh60c.c1 := by
  intro b h _
  let V:=Aw b h (cut b)
  let:FiniteDimensional ao (qlc9qed.Aw b (h+delta) b.cut) :=finite_ambient b (h+delta)
  let:Module.Finite ao V:=FiniteDimensional.of_injective
    (K:=ao) (V := ↥V) (V₂ := ↥(qlc9qed.Aw b (h+delta) b.cut))
    (Submodule.inclusion (ds8 b h)) (Submodule.inclusion_injective (ds8 b h))
  let v (c:aiz b h) :V:=⟨column (cLB b h c),mem_column c⟩
  have hi:LinearIndependent ao v :=LinearIndependent.of_comp V.subtype
    ((cGZ b (h+delta)).comp _ (cLB b h).injective)
  exact ⟨inferInstance,column_card b h ▸ hi.fintype_card_le_finrank⟩
end
end qd1cKFc
