import ProximityPrize.SubmissionLower.DQ
import ProximityPrize.SubmissionLower.ZITfVad
set_option Elab.async false
set_option autoImplicit true
namespace q1jcGec
open qK9H6va
open fP (qI)
open aiW (aOx)
def bve (d order :ℕ) :ℕ :=
  qI (d+1) fun t =>
    qI (d - t+1) fun c=>min 17 (aOx t c order)
def a2M (d lo:ℕ) :ℕ :=
  qI (min d 16+1) fun f =>
    qI (min (d - f) ((56-3*f)/2)+1) fun c =>
      min (d - f - c) (56-(2*c+3*f))+1-(lo-(2*c+3*f))
open aR (ao)
open fP (cF oG Qg GS bGG anJ aOb)
open private c6L from ProximityPrize.SubmissionLower.Z0omYcd
open scoped BigOperators
set_option maxHeartbeats 600000
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private abbrev F:=ZMod P1.p
private abbrev aT (d:ℕ) :=Σ t:Fin (d+1),Fin (d - t.val+1)
private abbrev dG (d order :ℕ) :=
  Σ l:aT d,Fin (aOx l.1 l.2 order)
private def Bs (q:ℕ) (g:ℤ) :
    Matrix (dG (iO q) (Vm q g).toNat) (XN q g) F :=
  fun i m =>
    let t:=i.1.1.val
    let c:=i.1.2.val
    let a :=i.2.val
    (((iO q - t - c).choose (m.val 1) :F) *
      (c.choose (m.val 2) :F))*((t - a).choose (m.val 3) :F)
private def aJo (q:ℕ) (g:ℤ) (e :ait q g) :
    dG (iO q) (Vm q g).toNat := by
  have hd:=e.property.1
  have ho:=e.property.2
  rw [cF] at hd
  rw [oG] at ho
  let t:=e.val 0+e.val 3
  have ht:t< iO q+1 := by dsimp [t]; omega
  have hc:e.val 2< iO q - t+1 := by dsimp [t]; omega
  refine ⟨⟨⟨t,ht⟩,⟨e.val 2,hc⟩⟩,⟨e.val 0,?_⟩⟩
  change e.val 0<aOx t (e.val 2) (Vm q g).toNat
  unfold aOx
  dsimp [t]
  omega
private theorem eKJ (q:ℕ) (g:ℤ) :
    Gy q g=(Bs q g).submatrix (aJo q g) id := by
  ext e m
  have hd:=e.property.1
  rw [cF] at hd
  have hb:iO q-(e.val 0+e.val 3)-e.val 2=e.val 1 := by omega
  have hf :e.val 0+e.val 3-e.val 0=e.val 3:= by omega
  change _=(((iO q-(e.val 0+e.val 3)-e.val 2).choose (m.val 1) :F) *
    ((e.val 2).choose (m.val 2) :F)) *
    (((e.val 0+e.val 3-e.val 0).choose (m.val 3)) :F)
  rw [hb,hf]
  rfl
private theorem ewZ (q:ℕ) (g:ℤ) (l:aT (iO q)) :
    ((Bs q g).submatrix (Sigma.mk l) id).rank ≤
      min 17 (aOx l.1 l.2 (Vm q g).toNat) := by
  let A:Matrix (Fin (aOx l.1 l.2 (Vm q g).toNat)) (Fin 17) F :=
    fun a j=>((l.1.val-a.val).choose j.val :F)
  let B:Matrix (Fin 17) (XN q g) F:= fun j m =>
    if j.val=m.val 3 then
      ((iO q-l.1.val-l.2.val).choose (m.val 1) :F) *
        (l.2.val.choose (m.val 2) :F)
    else 0
  have hprod:A*B=(Bs q g).submatrix (Sigma.mk l) id := by
    ext a m
    let j:Fin 17:=⟨m.val 3,Nat.lt_succ_of_le m.property.2.2.2⟩
    rw [Matrix.mul_apply,Finset.sum_eq_single j]
    · simp only [A,B,j,ite_true,Matrix.submatrix_apply,id_eq,Bs]
      ac_rfl
    · intro k _ hkj
      have hk :k.val≠m.val 3:= fun h=>hkj (Fin.ext h)
      simp [B,hk]
    · simp
  refine le_min ?_ ?_
  · rw [← hprod]
    exact (Matrix.rank_mul_le_left A B).trans A.rank_le_width
  · simpa only [Fintype.card_fin] using
      ((Bs q g).submatrix (Sigma.mk l) id).rank_le_card_height
theorem fTk (q:ℕ) (g:ℤ) :
    (Gy q g).rank≤bve (iO q) (Vm q g).toNat := by
  rw [eKJ]
  refine ((Matrix.rank_submatrix_le _ _ _).trans (c6L _)).trans ?_
  unfold bve
  simp only [Qg,aT,Fintype.sum_sigma]
  exact Finset.sum_le_sum fun t _=>Finset.sum_le_sum fun c _=>ewZ q g ⟨t,c⟩
private theorem dyf (d r :ℕ) :
    anJ d (-offset r) 56 16=a2M d (56 - r) := by
  unfold anJ a2M
  simp only [Qg]
  apply Finset.sum_congr rfl
  intro f _
  have hf :=f.isLt
  have hdiv : ((56-3*(f.val :ℤ))/2).toNat=(56-3*f.val)/2 := by omega
  rw [hdiv]
  apply Finset.sum_congr rfl
  intro c _
  have hc:=c.isLt
  unfold aOb offset
  omega
theorem fTf (q r :ℕ) :
    (Gy q (offset r)).rank≤a2M (iO q) (56 - r) := by
  let b:Module.Basis (XN q (offset r)) ao
      (GS (iO q) (-offset r) 56 16) :=MvPolynomial.basisRestrictSupport ao _
  exact (Gy q (offset r)).rank_le_card_width.trans_eq <|
    (Module.finrank_eq_card_basis b).symm.trans <|
      (bGG _ _ _ _).trans (dyf _ _)
open fP (aAr)
open private triangle sum_congr sum_comm sum_mono dfU from ProximityPrize.SubmissionLower.Z0omYcd
open private dfV from ProximityPrize.SubmissionLower.DQ
set_option maxRecDepth 4000
def bC5 (d u:ℕ) :ℕ :=
  qI (min d 16+1) fun f =>
    qI (min (d - f) ((56-3*f)/2)+1) fun c =>
      let x :=56-(2*c+3*f)
      let k :=min (d - f - c) x+1
      u*k-((triangle x - triangle (x - u)) -
        (triangle (x - k) - triangle (x - k - u)))
private theorem dNI (d u:ℕ) :
    (qI u fun r=>a2M d (56 - r))=bC5 d u:= by
  unfold a2M bC5
  rw [sum_comm]
  apply sum_congr
  intro f
  rw [sum_comm]
  apply sum_congr
  intro c
  simp only [Nat.sub_right_comm 56 _ (2*c+3*f)]
  exact dfV _ _ _
def bvj (q d u:ℕ) :ℕ :=
  qI (d+1) fun t =>
    qI (d - t+1) fun c =>
      let x :=155-(q+u+2*t+c)
      triangle x - triangle (x - min 17 (t+1))
private theorem fZi (q d u:ℕ) :
    (qI (155 - u) fun r=>bve d (155-(q+(r+u))))=bvj q d u:= by
  unfold bve bvj
  rw [sum_comm]
  apply sum_congr
  intro t
  rw [sum_comm]
  apply sum_congr
  intro c
  trans qI (155 - u) (fun r=>min (min 17 (t+1)) ((155-(q+u+2*t+c)) - r))
  · apply sum_congr
    intro r
    unfold aOx
    omega
  · exact dfU _ _ _ (by omega)
theorem eiM (q u:ℕ) (hhi:u≤155) :
    Oi q≤bC5 (iO q) u+bvj q (iO q) u:= by
  let P9 (r :ℕ) :=(Gy q (offset r)).rank
  have hcut (r :ℕ) : (Vm q (offset r)).toNat=155-(q+r) := by
    unfold Vm offset
    omega
  calc
    _=qI 155 P9:=(Qg _ _).symm
    _=qI u P9+qI (155 - u) (fun r=>P9 (r+u)) := by
      conv_lhs=>rw [← Nat.add_sub_of_le hhi,aAr]
    _≤(qI u fun r=>a2M (iO q) (56 - r)) +
        (qI (155 - u) fun r=>bve (iO q) (155-(q+(r+u)))) := by
      apply Nat.add_le_add
      · exact sum_mono _ fun r=> by
          exact fTf q r
      · exact sum_mono _ fun r=> by
          simpa only [hcut] using fTk q (offset (r+u))
    _ = _:= by rw [dNI,fZi]
end
end q1jcGec
