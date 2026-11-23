import ProximityPrize.SubmissionLower.ZpWrDCd
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qBd5KZd
noncomputable section
open Polynomial hiding degree
open P5 (K)
open P5_7_1 (degree)


open quN7Z4a (Sheet physicalWeight)
open cu (L)
open gT (kM)
open Cu (sQ)
open E7 (CurveField CurvePlace poleOrder KB)
open scoped Classical WithZero
def c1 :Prop :=
  ∀ (Q:sQ) [Fact (Irreducible Q)] (J:Ideal kM)
    (T:Finset K) (z :K→K) (s :K→K[X]) (e H :ℕ) (F:Sheet Q J e H T z s),
    Set.InjOn z (T:Set K) →
    ∃ (C:MarkedCurve T) (f :C.E[X][X]) (A:Allowance C.E),
      f.IsPrimitive∧Irreducible (f.map (algebraMap _ (FractionRing C.E[X]))) ∧
      f.natDegree=e∧weight degree f=physicalWeight degree F.root.equation ∧
      mass A≤H∧avoids C A∧bounded A f∧roots C (sections C s) 1 f
def c2 :Prop :=
  ∀ {T:Finset K} (C:MarkedCurve T),
    (∀ A:Allowance C.E,FiniteDimensional L (btN A)) →
    ∃ loss :ℕ,∀ v :ℕ,
    ∃ A:Allowance C.E,mass A≤v∧avoids C A∧v≤Module.finrank L (btN A)+loss
def c3:Prop :=
  ∀ (E :Type) [Field E] [Algebra L E],CurveField L E → ∀ A:Allowance E,
    FiniteDimensional L (btN A)∧Module.finrank L (btN A)≤ mass A+1
def c4 :Prop :=
  ∀ (E :Type) [Field E] [Algebra L E] (D e g M:ℕ) (f :E[X][X])
    (A B:Allowance E),f≠0→f.natDegree≤e→(e+g)*D <M→bounded A f →
    FiniteDimensional L (btN B)→FiniteDimensional L (btN (B+A)) →
    ∃ (b:L) (V:Submodule L E[X][X]),
      ((g+1)*M)*Module.finrank L (btN B) ≤
        Module.finrank L V+j3 D (e+g)*Module.finrank L (btN (B+A)) ∧
      ∀ G∈V,G.natDegree≤e+g∧weight D G<M∧bounded (B+A) G ∧
        ∃ H R:E[X][X],bounded B H∧bounded (B+A) R∧f*H=G+C (modulus b M)*R
def c5:Prop :=
  ∀ (E :Type) [Field E] [Algebra L E] (D e g W j:ℕ) (f :E[X][X])
    (A:Allowance E) (V:Submodule L E[X][X]),f≠0→f.natDegree=e →
    W<weight D f→FiniteDimensional L (btN A) →
    (∀ G∈V,G.natDegree≤e+g∧weight D G<W+1+j*D ∧bounded A G) →
    (∀ G∈V,f∣G)→Module.finrank L V≤j3 D j*Module.finrank L (btN A)
private theorem qL {N B c:ℕ} (hs :B*(c+1)<N*c) (h l:ℕ) :
  let r :=N*l+B+1
  let v :=c*h+r
  B*(v+h+1)+N*l<N*v := by
 dsimp only
 let r :=N*l+B+1
 have hBN :B<N := by
  by_contra! hle
  exact hs.not_ge ((Nat.mul_le_mul_right c hle).trans (Nat.mul_le_mul_left B (Nat.le_succ c)))
 have hr :B*(r+1)+N*l<N*r := by
  have heq :B*(r+1)+N*l+1=(B+1)*r := by dsimp [r]; ring
  apply Nat.succ_le_iff.mp
  change B*(r+1)+N*l+1≤N*r
  rw [heq]
  exact Nat.mul_le_mul_right r hBN
 have hb:=Nat.mul_le_mul_right h hs.le
 calc
  _=(B*(c+1))*h+(B*(r+1)+N*l) := by ring
  _<(N*c)*h+N*r :=Nat.add_lt_add_of_le_of_lt hb hr
  _ = _:= by ring
private theorem irred_resultant {E :Type} [Field E] {f G:E[X][X]}
  (hp:f.IsPrimitive) (hi:Irreducible (f.map (algebraMap _ (FractionRing E[X]))))
  (hn : ¬ f∣G) :f.resultant G≠0:= by
 let i:E[X] →+* FractionRing E[X] :=algebraMap _ _
 have hc:IsCoprime (f.map i) (G.map i) :=hi.coprime_iff_not_dvd.mpr
  (fun hd=>hn (hp.dvd_of_fraction_map_dvd_fraction_map hd))
 have hr :=resultant_ne_zero _ _ hc
 let hi:=IsFractionRing.injective E[X] (FractionRing E[X])
 rw [natDegree_map_eq_of_injective hi,natDegree_map_eq_of_injective hi,
  resultant_map_map] at hr
 exact fun h=>hr (by rw [h,map_zero])
variable {E :Type} [Field E] [Algebra L E]
private theorem small_pow (v :CurvePlace L E) {j:ℤ} {x :E} (h:small v j x) (n:ℕ) :
  small v (n•j) (x^n) := by
 simpa only [small,map_pow,WithZero.exp_nsmul] using pow_le_pow_left' h n
private theorem pole_le {A:Allowance E} {x :E} (h:x∈btN A) (v :CurvePlace L E) :
   poleOrder v.value x≤A v := by
 by_cases hx :x=0
 · simp [hx,poleOrder]
 change ∀ u,small u (A u) x at h
 have hh:=(WithZero.log_le_iff_le_exp (v.value.ne_zero_iff.mpr hx)).mpr (h v)
 exact Int.toNat_le_toNat hh
private theorem zero_ge (v :CurvePlace L E) {x :E} (hx :x≠0) {q:ℕ}
  (h:small v (-(q:ℤ)) x) :q≤KB v.value x := by
 have hh:=(WithZero.log_le_iff_le_exp (v.value.ne_zero_iff.mpr hx)).mpr h
 unfold KB
 omega
end
end qBd5KZd
