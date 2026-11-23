import ProximityPrize.SubmissionLower.D3
import ProximityPrize.SubmissionLower.Z9wruub
set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace P6
noncomputable section
open Polynomial Matrix gR ProximityPrize.Benchmark
open scoped BigOperators
theorem ebt (u:e9) :aDf u≤L:= by
  simpa only [aDf,Bx.adJ,Fintype.card_fin] using
    Matrix.rank_le_card_height ((iy u).map (algebraMap K[X] kB))
theorem aSO (u:e9) :Vv u=t+1 - R5 u:= by
  have h:=Bx.cep (So u)
  simp only [Fintype.card_fin] at h
  change Vv u+R5 u=t+1 at h
  omega
theorem a7J {u:e9} (T:qo u) :
    L+T.height+R5 u=t+1 := by
  exact kL.c75 k L t (R5 u) T.a T.b T.c
    (by decide) T.top T.degreeSum (by have :=T.nullitySum; omega)
theorem aEz {u:e9} (hu:abC u) (T:qo u) :
    T.height≤DY:= by
  have h:=a7J T
  have hr :=hu.1
  change 48755+T.height+R5 u=82318 at h
  change T.height≤33561
  omega
def c78 {u:e9} (hu:abC u) (T:qo u) :
    Relation T:= by
  have hline :=kL.b4H p node (u 0) (u 1)
    k T.a T.b T.c T.top T.degreeSum T.ab (T.active.trans_lt T.inactive)
    ((show 1≤t by decide).trans_lt T.inactive) T.level
  have hH :=aEz hu T
  apply kL.c4L p (by decide)
    node (u 0) (u 1) node.injective Native.ahU
    k k T.height (by rw [IRSProfile.card_index]; decide)
    (hH.trans (by decide)) _ hline
  rw [yP.FM.a5W]
  exact (Nat.mul_le_mul_right p (show 2*T.height+2≤2*DY+2 by omega)).trans_lt
    (by decide)
theorem fS9:L+p*DY=aEu:= by decide
theorem dtf :p*DY+2*DY+blockLength+2=aCe := by
  decide
theorem fS8 (u:e9) (hu:abC u) (Γ:Finset K) :
    (bAR u Γ).card≤aEu:= by
  classical
  have h:=kL.diw p node (u 0) (u 1) L t (R5 u)
    (aSO u) hu.2.1 (bAR u Γ) (fun γ hγ=> by
      rw [← aSO u]
      exact (Finset.mem_filter.mp hγ).2)
  have hs :t+1 - R5 u - L≤DY:= by
    have hr :=hu.1
    change 82318 - R5 u-48755≤33561
    omega
  exact h.trans ((Nat.add_le_add_left (Nat.mul_le_mul_left p hs) L).trans_eq fS9)
open private diA from ProximityPrize.SubmissionLower.O
theorem gE2 (u:e9) (htype :aB8 u)
    (Γ:Finset K) (hΓ:Tt u Γ) :Γ.card≤1 := by
  have hk :k≤Fintype.card I:= by rw [IRSProfile.card_index]; decide
  exact diA node (u 0) (u 1) node.injective
    k dw p hk (by decide) htype Γ (fun γ hγ=>a1v u γ (hΓ γ hγ))
theorem dU4 (u:e9) (Γ:Finset K) (hrank :aDf u<L)
    (hΓ:Tt u Γ) :Γ.card≤310898:= by
  have h:=bz4.dU5 node (u 0) (u 1) node.injective
    k L t (aDf u) (by rw [IRSProfile.card_index]; decide) hrank rfl Γ
    (fun γ hγ=>a1v u γ (hΓ γ hγ))
  rw [IRSProfile.card_index] at h
  exact h.trans (Nat.add_le_add_left (Nat.le_of_lt_succ hrank) blockLength)
theorem eOt (u:e9) (Γ:Finset K) (hprincipal:aKm u)
    (hΓ:Tt u Γ) :Γ.card≤0x29b85f105418f := by
  obtain ⟨a,g,hg,hga,ha,hkernel⟩:=hprincipal
  have hsum:a+(t - a)=t:= by omega
  let φ:=algebraMap K[X] kB
  have hcertificate :Principal.atR
      (fun b j=>φ (Principal.P8 p node (u 0) (u 1) b j)) k a (t - a) := by
    refine { generator :=g,nonzero :=hg,aNb:=hga,aOk := ?_ }
    intro f
    rw [hsum,Principal.aPN,Principal.buO]
    change (f.natDegree≤t∧((So u).map φ).mulVec (fun i=>f.coeff i.val)=0) ↔
      ∃ Q:kB[X],Q.natDegree≤t - a∧f=g*Q
    constructor
    · rintro ⟨hf,hker⟩
      exact (hkernel f hf).mp hker
    · rintro ⟨Q,hQ,rfl⟩
      have hdegree : (g*Q).natDegree≤t :=
        natDegree_mul_le.trans ((Nat.add_le_add hga hQ).trans_eq hsum)
      exact ⟨hdegree,(hkernel _ hdegree).mpr ⟨Q,hQ,rfl⟩⟩
  have h:=Principal.efZ φ
    (IsFractionRing.injective K[X] kB) p (by decide) node node.injective
    Native.ahU (u 0) (u 1) k k a (t - a)
    (by rw [IRSProfile.card_index]; decide)
    (hsum.trans_lt (show t<k by decide)) hcertificate Γ (fun γ hγ=> by
      rw [hsum]
      exact a1v u γ (hΓ γ hγ))
  rw [IRSProfile.card_index] at h
  exact h.trans ((Nat.mul_le_mul_left p (Nat.add_le_add_left ha blockLength)).trans (by decide))
open private cHO aDU cU4 from ProximityPrize.SubmissionLower.O
theorem dO2 (u:e9) (Γ:Finset K) (hu:aYx u)
    (hΓ:Tt u Γ) :Γ.card≤0x9f857201418e := by
  let φ:=algebraMap K[X] kB
  have hrank : ((So u).map φ).rank=Vv u:=rfl
  have hconstant: (ayo p node (u 0) (u 1) L t).rank=Vv u:=hu.symm
  have hcount:=cHO φ (IsFractionRing.injective K[X] kB)
    p (by decide) node node.injective Native.ahU
    (u 0) (u 1) k dw L t (by decide) (by decide)
    (by rw [IRSProfile.card_index]; decide) (Vv u) hrank hconstant
    Γ (fun γ hγ=>a1v u γ (hΓ γ hγ))
  have hr :Vv u≤t+1 := by
    rw [aSO]
    exact Nat.sub_le _ _
  exact hcount.trans ((Nat.mul_le_mul_left p hr).trans_eq (by decide))
open bai
private theorem cYJ (u:e9) :
    Principal.akc (aDU u) k t =
      (So u).map (algebraMap K[X] kB) :=
  Principal.buO (algebraMap K[X] kB)
    p node (u 0) (u 1) k t
private theorem cYL (u:e9) :
    acM (aDU u) k (t+1)=R5 u:= by
  rw [bNX (aDU u) k t,cYJ]
  rfl
private theorem eOA (u:e9) (a :ℕ) (ha :a≤t)
    (hone :acM (aDU u) k (a+1)=1)
    (hnull:R5 u=(t+1)-a) :aKm u:= by
  have hpos :0<acM (aDU u) k (a+1) := by omega
  have hdim:acM (aDU u) k (t+1)=(t-a)+1 := by
    rw [cYL]
    omega
  obtain ⟨g,hg,hdeg,hfac⟩:=eOB (aDU u) k a t
    ha (by decide) hpos hdim
  refine ⟨a,g,hg,hdeg,ha,fun P hP => ?_⟩
  rw [← cYJ]
  exact hfac P hP
theorem gEU (u:e9) (hpos :0<R5 u)
    (hind : ¬ aB8 u) (hnp : ¬ aKm u) :Nonempty (qo u) := by
  obtain ⟨a,b,c,hab,hbc,hc,hsum,hdim⟩:=evV
    (aDU u) k (cU4 u hind)
  have hloc:=hdim (t+1) (by decide)
  rw [cYL] at hloc
  have hthree :3*t<2*k+2 := by decide
  have hinactive :t<c:= by omega
  have ha :a≤t:= by omega
  have hb:b≤t:= by
    by_contra hb
    have hsmall:=hdim (a+1) (by omega)
    exact hnp (eOA u a ha (by omega) (by omega))
  refine ⟨⟨a,b,c,hab,hb,hinactive,hc,hsum,by omega,?_⟩⟩
  exact evU _ _ _ _ _ hdim
theorem gET {u:e9} (T:qo u) :2≤R5 u:= by
  have :=T.ab
  have :=T.active
  have :=T.nullitySum
  omega
open private cNu from ProximityPrize.SubmissionLower.D3
private theorem dxZ (u:e9) (γ:K) (M:B5 u γ) :
    ((So u).map (evalRingHom γ)).rank≠t+1 := by
  classical
  let S:=Finset.univ \ M.support
  have hs :S.card≤t:= by
    dsimp [S]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,IRSProfile.card_index]
    have :=M.dw
    change 179827≤_ at this
    change 262144-_≤82317
    omega
  exact cNu p node node.injective Native.ahU (u 0) (u 1) γ k L t
    (by rw [IRSProfile.card_index]; decide) M.decoder M.degree S hs
    (fun i hi=>(M.lg i (by simpa [S] using hi)).symm)
theorem eex (u:e9) (Γ:Finset K) (hfirst:aDf u=L)
    (hz :R5 u=0) (hΓ:Tt u Γ) :Γ.card≤0x410a6501418e := by
  have hr :=aSO u
  rw [hz] at hr
  apply (kL.diw p node (u 0) (u 1) L t 0 hr hfirst Γ ?_).trans_eq
  · decide
  · intro γ hγ
    obtain ⟨M⟩:=aCl u Γ hΓ γ hγ
    exact dxZ u γ M
theorem dd8 {u T R} (D:Reduction u T R) (hu:abC u) :
    k+3*D.height≤blockLength-(pJ R).card ∧
    k+D.height≤dw∧D.height<p - 1 := by
  have hb:=aEz hu T
  have he :=D.height_eq
  change T.height≤33561 at hb
  change 131072 + 3*D.height≤262144-_∧131072+D.height≤179827∧D.height<0x7f000000
  omega
end
end P6
