import ProximityPrize.SubmissionLower.Zw100fa
import ProximityPrize.SubmissionLower.ZX8w26c
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qa9Ovbd
noncomputable section
open Polynomial
open P5 (K p)
open quN7Z4a (Sheet physicalWeight)
open qBd5KZd (MarkedCurve Allowance mass small btN bounded weight j3
  avoids integral roots sections pull modulus pull_irreducible)
open cu (L)
open gT (kM)
open Cu (sQ)

open private qL irred_resultant small_pow pole_le zero_ge from ProximityPrize.SubmissionLower.Zw100fa
open scoped WithZero
def c1 :Prop :=
  ∀ (Q:sQ) [Fact (Irreducible Q)] (J:Ideal kM)
    (T:Finset K) (z :K→K) (s :K→K[X]) (g H :ℕ) (S:Sheet Q J g H T z s),
    Set.InjOn z (T:Set K) →
    ∃ (C:MarkedCurve T) (f :C.E[X][X]) (A:Allowance C.E),
      f.IsPrimitive∧Irreducible (f.map (algebraMap _ (FractionRing C.E[X]))) ∧
      f.natDegree=g∧(∀ D,weight D f=physicalWeight D S.root.equation) ∧
      mass A≤H∧avoids C A∧bounded A f∧roots C (sections C s) 1 f
def c2 :Prop :=qBd5KZd.c2
def c3:Prop :=qBd5KZd.c3
def c4 :Prop :=qBd5KZd.c4
def c5:Prop :=qBd5KZd.c5
def c6:Prop :=
  ∀ {T:Finset K} (C:MarkedCurve T) (S:T→C.E[X]) (D q M:ℕ) (b:L)
    (f G H R:C.E[X][X]) (A B:Allowance C.E),
    0<f.natDegree→integral C S→(∀ t,(S t).natDegree≤D) →
    avoids C A→avoids C B→bounded A f→bounded (B+A) G →
    bounded B H→bounded (B+A) R→ roots C S q f →
    weight D G<M→f*H=G+Polynomial.C (modulus b M)*R →
    ∀ i,(f.resultant G).coeff i∈btN (f.natDegree•(B+A)+G.natDegree•A) ∧
      ∀ t,small (C.Ia t) (-(q:ℤ)) ((f.resultant G).coeff i)
private theorem debit_add (D e j:ℕ) :
    j3 D e+j3 D j=D*(e*(e+1)+j*(j+1))/2 := by
  unfold j3
  have hd:2∣D*e*(e+1) := by
    rw [Nat.mul_assoc]
    exact dvd_mul_of_dvd_right (even_iff_two_dvd.mp (Nat.even_mul_succ_self e)) D
  rw [show D*(e*(e+1)+j*(j+1))=D*e*(e+1)+D*j*(j+1) by ring,
    Nat.add_div_of_dvd_right hd]
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) (h6:c6) :
    qYdH9sc.c1 := by
  intro Q _ J T z s D g H extra c W M S hg hgP hok hW hz hd
  obtain ⟨C,f,A,hfP,hfI,hfG,hfW,hA,hAway,hfA,hRoots⟩:=h1 Q J T z s g H S hz
  let j:=(extra+1)*c/(c+1)
  let N :=(extra+1)*M
  let B:=j3 D (g+extra)+j3 D j
  obtain ⟨_,_,_,hM,hEM,hSurplus⟩:=hok
  have hs :B*(c+1)<N*c:= by
    simpa only [B,N,debit_add,j,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hSurplus
  obtain ⟨loss,hLower⟩:=h2 C (fun A=>(h3 C.E C.curve A).1)
  let r :=N*loss+B+1
  let a :=g*r
  let q:=p^a
  let v :=c*(q*H)+r
  have hq:g*r<q:=Nat.lt_pow_self (by decide :1<p)
  obtain ⟨U,hU,hUAway,hDimU⟩:=hLower v
  let:CharP C.E p:=charP_of_injective_ringHom (algebraMap L C.E).injective p
  let φ:=iterateFrobenius C.E p a
  let A' : Allowance C.E :=q•A
  let f' := pull a f
  let S' := fun t=>(sections C s t).map φ
  have hφ:=φ.injective
  have hmap :Function.Injective (mapRingHom φ) :=Polynomial.map_injective φ hφ
  have hf'G:f'.natDegree=g:=(natDegree_map_eq_of_injective hmap f).trans hfG
  have hHigh:W<weight D f' := by
    change W<weight D (f.map (mapRingHom φ))
    unfold weight
    rw [support_map_of_injective f hmap]
    simp only [coeff_map,coe_mapRingHom,natDegree_map_eq_of_injective hφ]
    change W<weight D f
    rwa [hfW D]
  obtain ⟨hf'P,hf'I⟩:=pull_irreducible a f hfP hfI (hfG.symm ▸ hgP)
  have hS'd (t:T) : (S' t).natDegree≤D :=
    natDegree_map_le.trans (natDegree_map_le.trans (hd t t.property))
  have hS'i:integral C S' := by
    intro t i
    have hi:small (C.Ia t) 0 ((sections C s t).coeff i) := by
      rw [sections,coeff_map,RingHom.comp_apply]
      by_cases hc:algebraMap K L ((s t).coeff i)=0
      · simp [hc,small]
      · simp [small,(C.Ia t).on_constants _ hc]
    dsimp only [S']
    rw [coeff_map]
    simpa only [φ,iterateFrobenius_def,smul_zero] using small_pow _ hi q
  have hA'0:avoids C A' := fun t=> by simp [A',hAway t]
  have hf'A:bounded A' f' := by
    intro i k u
    change small u (A' u) (((f.map (mapRingHom φ)).coeff i).coeff k)
    have hu: (A' u:ℤ)=q•(A u:ℤ) := by
      rw [show A' u=q*A u by simp only [A',Finsupp.smul_apply,Nat.nsmul_eq_mul],
        Nat.cast_mul,nsmul_eq_mul]
    rw [coeff_map,coe_mapRingHom,coeff_map,hu]
    exact small_pow u (hfA i k u) q
  have hRoots' : roots C S' q f' := by
    intro t i
    change small (C.Ia t) (-(q:ℤ)) (((f.map (mapRingHom φ)).eval
      (mapRingHom φ (sections C s t))).coeff i)
    rw [eval_map_apply,coe_mapRingHom,coeff_map]
    simpa only [φ,iterateFrobenius_def,Nat.cast_one,smul_neg,nsmul_one] using
      small_pow _ (hRoots t i) q
  have hA'm:mass A' ≤ q*H := by
    simpa only [A',map_nsmul,Nat.nsmul_eq_mul] using Nat.mul_le_mul_left q hA
  obtain ⟨hFin,hDim⟩:=h3 C.E C.curve (U+A')
  have hD:Module.finrank L (btN (U+A'))≤v+q*H+1 :=
    hDim.trans (by rw [map_add]; exact Nat.add_le_add_right (Nat.add_le_add hU hA'm) 1)
  have hRank :B*Module.finrank L (btN (U+A'))<N*Module.finrank L (btN U) := by
    have hm:=(qL hs (q*H) loss :B*(v+q*H+1)+N*loss<N*v)
    exact Nat.lt_of_add_lt_add_right ((Nat.add_le_add_right (Nat.mul_le_mul_left B hD) _).trans_lt
      (hm.trans_le (by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hDimU)))
  obtain ⟨b,V,hV,hRow⟩:=h4 C.E D g extra M f' A' U hf'P.ne_zero hf'G.le hEM hf'A
    (h3 C.E C.curve U).1 hFin
  have hWide :j3 D j*Module.finrank L (btN (U+A'))<Module.finrank L V:= by
    have h:=hRank.trans_le hV
    dsimp only [B] at h
    rw [Nat.add_mul] at h
    omega
  have hMV:M=W+1+j*D:=hM
  have hProper : ∃ G∈V,¬ f' ∣ G:= by
    by_contra! hAll
    exact hWide.not_ge (h5 C.E D g extra W j f' (U+A') V hf'P.ne_zero hf'G hHigh hFin
      (fun G hG=>⟨(hRow G hG).1,hMV ▸ (hRow G hG).2.1,(hRow G hG).2.2.1⟩) hAll)
  obtain ⟨G,hGV,hG⟩:=hProper
  obtain ⟨hGe,hGw,hGa,P,R,hPu,hRu,hEq⟩:=hRow G hGV
  let i:=(f'.resultant G).natDegree
  have hi: (f'.resultant G).coeff i≠0:=leadingCoeff_ne_zero.mpr (irred_resultant hf'P hf'I hG)
  let Aout:=f'.natDegree•(U+A')+G.natDegree•A'
  obtain ⟨hPoles,hZeros⟩:=h6 C S' D q M b f' G P R A' U (hf'G.symm ▸ (by omega :0<g))
    hS'i hS'd hA'0 hUAway hf'A hGa hPu hRu hRoots' hGw hEq i
  refine ⟨⟨C.E,C.curve,a,_,hi,C.Ia,Aout,pole_le hPoles,?_⟩,?_⟩
  · intro t
    have hzq:=zero_ge (C.Ia t) hi (hZeros t)
    have hp:=pole_le hPoles (C.Ia t)
    exact (Nat.add_le_add hzq hp).trans_eq (Nat.add_comm _ _)
  · change mass Aout<q*((g*(c+1)+(g+extra))*H+1)
    have hmass :mass Aout≤g*(v+q*H)+(g+extra)*(q*H) := by
      simp only [Aout,map_add,map_nsmul,Nat.nsmul_eq_mul,hf'G]
      exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.add_le_add hU hA'm))
        (Nat.mul_le_mul hGe hA'm)
    have heq :g*(v+q*H)+(g+extra)*(q*H)=q*((g*(c+1)+(g+extra))*H)+g*r := by
      dsimp only [v]
      ring
    rw [heq] at hmass
    exact hmass.trans_lt (by rw [Nat.mul_add,Nat.mul_one]; exact Nat.add_lt_add_left hq _)
end
end qa9Ovbd
