import ProximityPrize.SubmissionLower.Z8dxYFd
import ProximityPrize.SubmissionLower.ZdSQxye
set_option Elab.async false
section
set_option autoImplicit true
namespace qp56ikd
noncomputable section
open P5 (K p)
open qckEfrc (Var af Box point Regular BA)
open cu (L FX kr jz)
open vq (ZC)
open Finset MvPolynomial
open scoped Polynomial
open private weight bds from ProximityPrize.SubmissionLower.Z3e8uLd
open private ev aNv padding from ProximityPrize.SubmissionLower.Z8dxYFd
open private W wv sep_bound bCJ padded_cap box_of_weights from ProximityPrize.SubmissionLower.Z8dxYFd
abbrev power (d:ℕ) :=2*d-3
abbrev total (d b:ℕ) :=1+power d*(b-1)
abbrev top (d b j:ℕ) :=min (total d b) (power d*(j-1)+d)
abbrev seed (d u:ℕ) :=power d*u
abbrev kK (d b j u:ℕ) :=cappedBidegreeMixedVolume u b j (seed d u) (total d b) (top d b j)
local notation "ord" => (some (0:Fin 2))
local notation "vel" => (some (1 :Fin 2))
local notation "sep" => MvPolynomial.pderiv (R:=FX) vel
def numerator (d:ℕ) (f :af) :ℕ→af
 | 0=>sep f^power d*MvPolynomial.X vel
 | i+1=>sep f^(power d-(2*i+1))*BA f i
def VA (d:ℕ) (f :af) (x y :K) :af :=
  sep f^power d*MvPolynomial.X ord + ∑ i∈range d,C (weight x (i+1))*numerator d f i -
    C (jz y)*sep f^power d
private theorem aM7 {d:ℕ} (hd:1≤d) {w:Var→ℕ} {g:af} {B δ:ℕ}
    (hg:g∈W w B) (hB:w vel≤B) (hw:w vel=w ord+δ) (x y :K) :
    VA d g x y∈W w (w ord+power d*(B - w vel)+d*δ) := by
  let a :=B - w vel
  let n:=w ord+power d*a+d*δ
  have hg' : g∈W w (a+w vel) := by
    dsimp only [a]
    rwa [Nat.sub_add_cancel hB]
  have hs :=sep_bound hg'
  have hp:=pow_mem_restrictWeightedDegree hs (power d)
  have hn (i:ℕ) (hi:i∈range d) :numerator d g i∈W w n:= by
    cases i with
    | zero =>
      change sep g^power d*MvPolynomial.X vel∈W w n
      have hδ:=Nat.mul_le_mul_right δ hd
      rw [Nat.one_mul] at hδ
      have h:power d*a+w vel≤n:= calc
        _=w ord+power d*a+δ:= by rw [hw]; ac_rfl
        _≤n:=Nat.add_le_add_left hδ _
      exact restrictWeightedDegree_mono w h
        (mul_mem_restrictWeightedDegree hp (X_mem_restrictWeightedDegree w _ vel le_rfl))
    | succ i =>
      change sep g^(power d-(2*i+1))*BA g i∈W w n
      have hi' : i+2≤d:=Nat.succ_le_of_lt (mem_range.mp hi)
      exact restrictWeightedDegree_mono w (padded_cap a δ (w ord) hi')
        (mul_mem_restrictWeightedDegree (pow_mem_restrictWeightedDegree hs _)
          (bCJ hg' hw i))
  change VA d g x y∈W w n
  unfold VA
  refine (W w n).sub_mem ((W w n).add_mem ?_ ?_) ?_
  · exact restrictWeightedDegree_mono w
      (show power d*a+w ord≤n by rw [Nat.add_comm]; exact Nat.le_add_right _ _)
      (mul_mem_restrictWeightedDegree hp (X_mem_restrictWeightedDegree w _ ord le_rfl))
  · apply Submodule.sum_mem
    intro i hi
    rw [← smul_eq_C_mul]
    exact (W w n).smul_mem _ (hn i hi)
  · rw [← smul_eq_C_mul]
    exact (W w n).smul_mem _ (restrictWeightedDegree_mono w
      (show power d*a≤n from (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)) hp)
local notation "ws" => (fun v :Var=>Option.elim v 1 fun _=>0)
local notation "wt" => (fun v :Var=>Option.elim v 0 fun _=>1)
theorem valueCut_caps {d b j u:ℕ} (hd:1≤d) {g:af}
  (hb:0<b) (hj:0<j) (hg:g∈Box b j u) (x y :K) :
  VA d g x y∈Box (total d b) (top d b j) (seed d u) := by
 have h:=mem_restrictCappedBidegree.mp hg
 have hs :g∈W ws u:=mem_restrictWeightedDegree.mpr fun m hm=> by
  simpa only [Finsupp.weight_elim_one_zero] using (h m hm).1
 have ht:g∈W wt b:=mem_restrictWeightedDegree.mpr fun m hm=> by
  simpa only [Finsupp.weight_elim_zero_one] using (h m hm).2.1
 have hv :g∈W wv j:=mem_restrictWeightedDegree.mpr fun m hm=> by
  simpa only [wv,Finsupp.weight_single_one_apply] using (h m hm).2.2
 have hs' : VA d g x y∈W ws (seed d u) := by
  simpa only [show ws ord=0 by rfl,show ws vel=0 by rfl,
    Nat.sub_zero,Nat.mul_zero,Nat.add_zero,Nat.zero_add] using
    aM7 hd (δ:=0) hs (Nat.zero_le u) (by rfl) x y
 have ht' : VA d g x y∈W wt (total d b) := by
  simpa only [show wt ord = 1 by rfl,show wt vel=1 by rfl,
    Nat.mul_zero,Nat.add_zero] using
    aM7 hd (δ:=0) ht hb (by rfl) x y
 have hv' : VA d g x y∈W wv (power d*(j-1)+d) := by
  simpa only [show wv ord=0 by decide,show wv vel=1 by decide,
    Nat.mul_one,Nat.zero_add] using
    aM7 hd (δ:=1) hv (show wv vel≤j from hj) (by decide) x y
 exact box_of_weights hs' ht' hv'
private theorem b12 {d:ℕ} (g:af) (z :L) (S:K[X]) (hg:ev z S g=0)
   (i:ℕ) (hi:i<d) :
   ev z S (numerator d g i)=ev z S (sep g)^power d*ZC S (i+1) := by
 cases i with
 | zero =>
   simp only [numerator,map_mul,map_pow,eval_X]
   rfl
 | succ i =>
   rw [numerator,map_mul,map_pow,aNv _ _ _ hg,
     ← mul_assoc,← pow_add,padding (show i+1<d from hi)]
private theorem eval_cut {d:ℕ} (hd:d<p) (g:af) (z :L) (S:K[X]) (hS:S.natDegree≤d)
   (hg:ev z S g=0) (x y :K) :ev z S (VA d g x y) =
     ev z S (sep g)^power d*(jz (S.eval x) - jz y) := by
 let a :=ev z S (sep g)^power d
 rw [bds hd S hS x,mul_sub,mul_add,Finset.mul_sum]
 simp only [VA,map_add,map_sub,map_mul,map_pow,map_sum,eval_C,eval_X]
 rw [mul_comm a (jz y)]
 refine congrArg (fun t:FX=>a*kr S+t - jz y*a) (sum_congr rfl ?_)
 intro i hi
 rw [b12 g z S hg i (mem_range.mp hi)]
 ring
theorem aFp {d:ℕ} (hd:d<p) (g:af) (z :L) (S:K[X])
  (hS:S.natDegree≤d) (hreg:Regular g z S) (x y :K) :
  eval (point z S) (VA d g x y)=0↔S.eval x=y := by
 change ev z S (VA d g x y)=0↔S.eval x=y
 rw [eval_cut hd g z S hS hreg.1,mul_eq_zero,or_iff_right (pow_ne_zero _ hreg.2),sub_eq_zero]
 exact jz.injective.eq_iff
end
end qp56ikd
end
section
set_option autoImplicit true
namespace qp56ikd
noncomputable section
open P5 (K I node blockLength)
open P5_7 (midAgreement)
open qckEfrc (LinearData)
open Polynomial Finset MvPolynomial
open private OF OF.distinct OF.degree OF.lg from ProximityPrize.SubmissionLower.ZogIzOe
open private dmf from ProximityPrize.SubmissionLower.ZdSQxye
open private Wq from ProximityPrize.SubmissionLower.ZJ86yqc
open private bWt aM6 from ProximityPrize.SubmissionLower.Z3EWiUc
open private zero_count cut_data from ProximityPrize.SubmissionLower.ZFSutke
abbrev gap (d:ℕ) :=midAgreement-d
abbrev errors :=blockLength-midAgreement
private theorem occupancy_bound {w T s d} (h:OF w T s d) (hd:d≤133774) (cap:ℕ)
   (bound : ∀ i:I,(∃ γ∈T,(s γ).eval (node i)≠w i) →
     (T.filter fun γ=>(s γ).eval (node i)=w i).card≤ cap) :
   gap d*T.card≤errors*cap+gap d :=
 Wq (err :=errors) rfl (by decide) (hd.trans_lt (by decide))
   (OF.distinct h) (OF.degree h) (OF.lg h) cap bound
variable {ι:Type*} [Finite ι] {T:Finset K} {s :K→K[X]}
 (C:LinearData (ι:=ι) T s)
private theorem dRZ {U:Finset K} (hU:U⊆T) {w d} (hw:OF w U s d)
    (hdD:d≤133774)
    (P:Ideal (MvPolynomial ι cu.FX)) (hP:P.IsPrime)
    (hd: (affineHilbertPolynomial P).natDegree=1)
    (hz : ∀ γ∈U,C.pt γ∈zeroLocus _ P) : (U.card:ℚ)≤2*affineDegree P:= by
  classical
  obtain ⟨δ,hδ,hdeg⟩:=aM6 P hP hd
  have hh:=occupancy_bound hw hdD δ (fun i hi=> by
    let V:=U.filter fun γ=>(s γ).eval (node i)=w i
    let c:=C.cut (node i) (w i)
    let J:=P ⊔ Ideal.span {c}
    have hcut:=principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
      hP (cut_data C hU hz hi) (C.deg (node i) (w i))
    have hdim: (affineHilbertPolynomial J).natDegree=0:= by
      have h:=hcut.1
      rw [hd] at h
      exact Nat.eq_zero_of_le_zero h
    have hdegJ:affineDegree J≤affineDegree P:= by
      simpa [affineDegree,hd,hdim,J,c,Polynomial.leadingCoeff] using hcut.2
    have hsub:V⊆T:=(show V⊆U from filter_subset _ _).trans hU
    have hv :=zero_count C hsub J hdim (fun γ hγ=> by
      obtain ⟨hγ,hh⟩:=mem_filter.mp hγ
      exact mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hz γ hγ,
        (C.hit γ (hU hγ) _ _).mpr hh⟩)
    exact Nat.cast_le.mp (hv.trans (hdegJ.trans_eq hdeg)))
  have hg:errors<gap d*2 := by
    change 82404<(179740-d)*2
    omega
  have hfin:U.card≤2*δ:= by
    by_contra! hbad
    have hstep:=Nat.mul_le_mul_left (gap d) (show 2*δ+1≤U.card by omega)
    rw [Nat.mul_add,Nat.mul_one,← Nat.mul_assoc] at hstep
    have hstrict :=Nat.mul_lt_mul_of_pos_right hg hδ
    omega
  rw [hdeg]
  exact_mod_cast hfin
theorem surface_count {U:Finset K} (hU:U⊆T) {w d} (hw:OF w U s d)
    (hdD:d≤133774)
    (P:Ideal (MvPolynomial ι cu.FX)) (hP:P.IsPrime)
    (hd: (affineHilbertPolynomial P).natDegree=2)
    (hz : ∀ γ∈U,C.pt γ∈zeroLocus _ P) :
    (gap d:ℚ)*U.card≤2*errors*affineDegree P+gap d:= by
  classical
  let _:P.IsPrime :=hP
  have hr :0≤2*affineDegree P:=mul_nonneg (by decide) (affineDegree_nonneg _)
  have hcount:=occupancy_bound hw hdD ⌊2*affineDegree P⌋₊ (fun i hi=> by
    apply (Nat.le_floor_iff hr).mpr
    let V:=U.filter fun γ=>(s γ).eval (node i)=w i
    let c:=C.cut (node i) (w i)
    let J:=P ⊔ Ideal.span {c}
    let Qs :=J.minimalPrimesFinset
    let W (Q:Ideal (MvPolynomial ι cu.FX)) :=V.filter fun γ=>C.pt γ∈zeroLocus _ Q
    have hproper :c∉P:=cut_data C hU hz hi
    have hcover :V.card ≤ ∑ Q∈Qs,(W Q).card:= by
      apply bWt
      intro γ hγ
      have hv :=mem_filter.mp hγ
      have hp:C.pt γ∈zeroLocus _ J:=mem_zeroLocus_sup_span_singleton_iff.mpr
        ⟨hz γ hv.1,(C.hit γ (hU hv.1) _ _).mpr hv.2⟩
      obtain ⟨Q,hQ,hγQ⟩:=exists_retainedMinimalPrime_of_mem_zeroLocus J 1 _ hp (by simp)
      exact ⟨Q,Ideal.mem_minimalPrimesFinset.mpr (Ideal.mem_retainedMinimalPrimes.mp hQ).1,
        mem_filter.mpr ⟨hγ,hγQ⟩⟩
    have hone (Q) (hQ:Q∈Qs) : ((W Q).card:ℚ)≤2*affineDegree Q:= by
      have hmin:=Ideal.mem_minimalPrimesFinset.mp hQ
      have hdim:=principalCut_natDegree_affineHilbertPolynomial_add_one hproper hmin
      rw [hd] at hdim
      have hsub:W Q⊆U:=(filter_subset _ _).trans (filter_subset _ _)
      exact dRZ C (hsub.trans hU) (dmf hw hsub) hdD Q hmin.isPrime (by omega)
        (fun _ hγ=>(mem_filter.mp hγ).2)
    have hs : (V.card:ℚ) ≤ ∑ Q∈Qs,((W Q).card:ℚ) := by exact_mod_cast hcover
    have hd' : ∑ Q∈Qs,affineDegree Q≤affineDegree P:= by
      simpa only [Qs,J,Nat.cast_one,one_mul] using
        principalCut_sum_affineDegree_minimalPrimes_le hproper (C.deg (node i) (w i))
    exact hs.trans ((sum_le_sum hone).trans (by rw [← mul_sum]; gcongr)))
  have hc: (gap d:ℚ)*U.card≤errors*(⌊2*affineDegree P⌋₊ : ℕ)+gap d:= by
    exact_mod_cast hcount
  exact hc.trans (calc
    _≤(errors :ℚ)*(2*affineDegree P)+gap d :=
      add_le_add (mul_le_mul_of_nonneg_left (Nat.floor_le hr) (Nat.cast_nonneg _)) le_rfl
    _ = _:= by ring)
end
end qp56ikd
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qp56ikd
noncomputable section
open Finset MvPolynomial
open P5 (K)
open cu (FX L)
open qckEfrc (af Box Regular point LinearData box_degree)
open private OF OF.degree OF.distinct from ProximityPrize.SubmissionLower.ZogIzOe
open private dmf from ProximityPrize.SubmissionLower.ZdSQxye
open private atX_inj from ProximityPrize.SubmissionLower.Z5tZ7td
open private caj from ProximityPrize.SubmissionLower.L
open private bWt from ProximityPrize.SubmissionLower.Z3EWiUc
open scoped Polynomial
theorem charged {w T s d b j u} (hw:OF w T s d) (hd:2≤d) (hdD:d≤133774)
    (hb:0<b) (hj:0<j) (hu:0< u) {g:af} (hg:g∈Box b j u) (z :K→L)
    (hz : ∀ γ∈T,Regular g (z γ) (s γ)) :
    (gap d:ℚ)*T.card≤2*errors*kK d b j u+gap d*(b+u:ℕ) := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | ⟨γ₀,hγ₀⟩
  · simp only [card_empty,Nat.cast_zero,mul_zero]
    positivity
  let v γ:=point (z γ) (s γ)
  have hg0:g≠0:= fun e=>(hz γ₀ hγ₀).2 (by simp [e])
  let A:=cappedBidegreeExponents (Fin 2) 1 (seed d u) (total d b) (top d b j)
  let φ:=monomialMap FX A
  have hU:0<seed d u:=Nat.mul_pos (by unfold power; omega) hu
  have hB:0<total d b:=Nat.add_pos_left Nat.zero_lt_one _
  have hJ:0<top d b j:=lt_min hB (Nat.add_pos_right _ (by omega))
  have hsurj:Function.Surjective φ:=monomialMap_cappedBidegreeExponents_surjective hU hB hJ
  let F:LinearData (ι:=A) T s :=
    ⟨fun γ=>monomialPoint A (v γ),fun γ hγ δ hδ eq=> by
      have hv :=(monomialPoint_injective
        (single_mem_cappedBidegreeExponents hU hB hJ)) eq
      exact (OF.distinct hw) hγ hδ (atX_inj (congrFun hv (some 0))),
      fun x y=>monomialLift (VA d g x y) (valueCut_caps (by omega) hb hj hg x y),
      fun x y=>totalDegree_monomialLift_le_one _ _,
      fun γ hγ x y=> by
        rw [aeval_monomialPoint,monomialMap_monomialLift,aeval_eq_eval]
        exact aFp (hdD.trans_lt (by decide)) _ _ _ (OF.degree hw γ hγ) (hz γ hγ) _ _⟩
  let J:Ideal af :=Ideal.span {g}
  let dO (Q:Ideal af) :=T.filter fun γ=>v γ∈zeroLocus FX Q
  let Qs :=J.minimalPrimesFinset.filter fun Q=>(dO Q).Nonempty
  have hmin (Q) (hQ:Q∈Qs) :J.IsMinimalPrime Q :=
    Ideal.mem_minimalPrimesFinset.mp (mem_filter.mp hQ).1
  have hcover :T.card ≤ ∑ Q∈Qs,(dO Q).card:= by
    apply bWt
    intro γ hγ
    have h:v γ∈zeroLocus FX J:= by
      rw [mem_zeroLocus_iff_le_ker_aeval,Ideal.span_singleton_le_iff_mem,RingHom.mem_ker,aeval_eq_eval]
      exact (hz γ hγ).1
    obtain ⟨Q,hQ,hγQ⟩:=exists_retainedMinimalPrime_of_mem_zeroLocus J 1 _ h (by simp)
    have hp:γ∈dO Q:=mem_filter.mpr ⟨hγ,hγQ⟩
    exact ⟨Q,mem_filter.mpr ⟨Ideal.mem_minimalPrimesFinset.mpr
      (Ideal.mem_retainedMinimalPrimes.mp hQ).1,⟨γ,hp⟩⟩,hp⟩
  let _: (⊥ : Ideal af).IsPrime :=Ideal.isPrime_bot
  have hg_bot:g∉(⊥ : Ideal af) := by simpa using hg0
  have hdim (Q) (hQ:Q∈Qs) : (affineHilbertPolynomial (Q.comap φ)).natDegree=2 := by
    rw [natDegree_affineHilbertPolynomial_comap_of_surjective φ hsurj]
    have hQ' : ((⊥ : Ideal af) ⊔ Ideal.span {g}).IsMinimalPrime Q:= by
      rw [bot_sup_eq]
      exact hmin Q hQ
    have h:=principalCut_natDegree_affineHilbertPolynomial_add_one hg_bot hQ'
    rw [natDegree_affineHilbertPolynomial_bot,Finite.card_option,Nat.card_eq_fintype_card,
      Fintype.card_fin] at h
    omega
  have hdegree :g.totalDegree≤b+u:= by
    rw [totalDegree,Finset.sup_le_iff]
    intro m hm
    obtain ⟨ha,hb',_⟩:=mem_restrictCappedBidegree.mp hg m hm
    change m.degree≤b+u
    rw [Finsupp.degree_eq_sum,Fintype.sum_option]
    rw [Finsupp.degree_eq_sum] at hb'
    simpa only [Finsupp.some_apply,add_comm] using Nat.add_le_add ha hb'
  have hcount:Qs.card≤b+u:= by
    have hsum:=principalCut_sum_affineDegree_minimalPrimes_le hg_bot hdegree
    have hq: (Qs.card:ℚ) ≤ ∑ Q∈Qs,affineDegree Q:= calc
      _ = ∑ _Q∈Qs,(1 :ℚ) := by simp
      _≤_:= by
        apply sum_le_sum
        intro Q hQ
        obtain ⟨γ,hγ⟩:=(mem_filter.mp hQ).2
        let _:=(hmin Q hQ).isPrime
        exact caj Q (v γ) (mem_filter.mp hγ).2
    have h:=hq.trans ((sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun Q _ _=>affineDegree_nonneg Q)).trans
      (by simpa only [bot_sup_eq,affineDegree_bot,mul_one,J] using hsum))
    exact_mod_cast h
  have hsum : ∑ Q∈Qs,affineDegree (Q.comap φ)≤(kK d b j u:ℚ) := by
    have hpull:=sum_affineDegree_minimalPrimes_comap_span_singleton_le_of_surjective φ hsurj g
    have hs :Qs.image (fun Q=>Q.comap φ)⊆(J.comap φ).minimalPrimesFinset := by
      intro Q hQ
      obtain ⟨P,hP,rfl⟩:=mem_image.mp hQ
      exact Ideal.mem_minimalPrimesFinset.mpr
        (Ideal.minimalPrimes_comap_of_surjective hsurj (hmin P hP))
    have hc:=(sum_le_sum_of_subset_of_nonneg hs (fun Q _ _=>affineDegree_nonneg Q)).trans hpull
    rw [sum_image (fun P _ Q _ eq=>Ideal.comap_injective_of_surjective φ hsurj eq)] at hc
    have hm:=box_degree hU hB hJ (min_le_left _ _) hg0 hg
    rw [kK,cappedBidegreeMixedVolume_eq (show top d b j≤total d b from min_le_left _ _)]
    exact hc.trans hm
  have hone (Q) (hQ:Q∈Qs) :
      (gap d:ℚ)*(dO Q).card≤2*errors*affineDegree (Q.comap φ)+gap d :=
    surface_count F (filter_subset _ _) (dmf hw (filter_subset _ _)) hdD
      (Q.comap φ) ((hmin Q hQ).isPrime.comap φ) (hdim Q hQ)
      (fun γ hγ=>(monomialPoint_mem_zeroLocus_comap_iff
        (single_mem_cappedBidegreeExponents hU hB hJ) Q (v γ)).mpr (mem_filter.mp hγ).2)
  calc
    _≤(gap d:ℚ) * ∑ Q∈Qs,((dO Q).card:ℚ) := by gcongr; exact_mod_cast hcover
    _ = ∑ Q∈Qs,(gap d:ℚ)*(dO Q).card:=mul_sum ..
    _ ≤ ∑ Q∈Qs,(2*errors*affineDegree (Q.comap φ)+gap d) :=sum_le_sum hone
    _=2*errors*(∑ Q∈Qs,affineDegree (Q.comap φ))+gap d*Qs.card:= by
      rw [sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul,mul_comm (Qs.card:ℚ)]
    _≤_:= by gcongr
end
end qp56ikd
end
