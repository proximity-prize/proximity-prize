import ProximityPrize.SubmissionLower.Z4uF8Nb
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qgbTAnb
noncomputable section
open Polynomial Finset qe6nVeb qE3Ebna
open cu (L)
open P5 (K)
open qb0hmCe (CurveModel)
open E7 (KB)
open scoped Classical WithZero
private theorem primitive_pair {E :Type} [Field E] {f :E[X][X]}
  (hf :Irreducible f) (hd:f.natDegree=1) :IsCoprime (f.coeff 1) (f.coeff 0) := by
 have ha :f.coeff 1≠0:= by
  rw [← hd,← leadingCoeff]
  exact leadingCoeff_ne_zero.mpr hf.ne_zero
 apply EuclideanDomain.isCoprime_of_dvd (by simp [ha])
 intro t ht _ hab hbb
 obtain ⟨a,ha⟩:=hab
 obtain ⟨b,hb⟩:=hbb
 apply ht
 apply hf.isPrimitive (by omega)
 refine ⟨Polynomial.C a*Polynomial.X+Polynomial.C b,?_⟩
 rw [eq_X_add_C_of_natDegree_le_one hd.le,ha,hb,map_mul,map_mul,mul_add,mul_assoc]
private theorem mark {J:Input} {U:Finset K} {B:DualWord J U} {q:SeedPlane}
   {C:CurveModel q} (S:Sheet B C) (hd:S.d = 1) (m s :ℕ)
   (hm: (S.f.coeff 1).natDegree≤ m) (hn: (S.f.coeff 0).natDegree≤ m+s)
   (hs :s=B.u₁-B.u₀) (hr :resultant (S.f.coeff 1) (S.f.coeff 0) m (m+s)≠0)
   (γ:K) (hγ:γ∈S.marks) :
   poleOrderAt S γ≤KB (S.place γ).value (resultant (S.f.coeff 1) (S.f.coeff 0) m (m+s)) := by
 let ι:=S.atPlace γ hγ
 let a :=S.f.coeff 1
 let b:=S.f.coeff 0
 let P:=B.P γ
 let Q:=B.Q γ
 let A:=liftSeries ι a
 let F:=liftSeries ι b
 let a₀:=slice ι 0 a
 let b₀:=slice ι 0 b
 let a₁:=slice ι 1 a
 let b₁:=slice ι 1 b
 have hA:A.map PowerSeries.constantCoeff=a₀:=fWX ι a
 have hF:F.map PowerSeries.constantCoeff=b₀:=fWX ι b
 have hQ:=B.denominator γ (S.Bp hγ)
 have hcop:=B.coprime γ (S.Bp hγ)
 have ha :a₀≠0:= by
   intro hz
   have hc:=congrArg (fun g:L[X]=>g.coeff a.natDegree) hz
   rw [coeff_extract (by simp),← leadingCoeff] at hc
   have hmon :a.leadingCoeff=1 := by simpa only [a,hd] using S.normalized
   simp [hmon] at hc
 have hz :a₀*P+b₀*Q=0:=linear_root ι hd.le hQ (S.root γ hγ)
 have he :a₀*P = -(b₀*Q) :=eq_neg_of_add_eq_zero_left hz
 have hQdvd:Q∣a₀:=hcop.symm.dvd_of_dvd_mul_right (he.symm ▸
   dvd_neg.mpr (dvd_mul_left Q b₀))
 obtain ⟨G,hGQ⟩:=hQdvd
 have hG:G≠0:= fun h=>ha (by simp [hGQ,h])
 have hg:a₀=G*Q:=hGQ.trans (mul_comm _ _)
 have hgb:b₀ = -(G*P) := by
   apply mul_right_cancel₀ hQ
   calc
     b₀*Q = -(a₀*P) :=eq_neg_of_add_eq_zero_right hz
     _ = -(G*P)*Q:= by rw [hg,neg_mul,mul_right_comm G Q P]
 let j:=max Q.natDegree (P.natDegree-s)
 let k :=m-(G.natDegree+j)
 have hjQ:Q.natDegree≤j:=le_max_left _ _
 have hjP:P.natDegree≤ s+j:= by have :=le_max_right Q.natDegree (P.natDegree-s); omega
 have hdegA:a₀.natDegree≤ m:=(degree_extract (by simp) a).trans hm
 have hdegB:b₀.natDegree≤ m+s :=(degree_extract (by simp) b).trans hn
 have hdegGQ:G.natDegree+Q.natDegree≤ m:= by
   rwa [hg,natDegree_mul hG hQ] at hdegA
 have hdegGP:G.natDegree+P.natDegree≤ m+s := by
   by_cases hp:P=0
   · simp only [hp,natDegree_zero,add_zero]; omega
   · rwa [hgb,natDegree_neg,natDegree_mul hG hp] at hdegB
 have hj:G.natDegree+j≤ m:= by
   dsimp [j]
   omega
 have hk :k≤ m:=Nat.sub_le _ _
 have hk_eq :G.natDegree+j+k=m:=Nat.add_sub_of_le hj
 have hDA:a₀.natDegree≤ m-k := by
   rw [hg,natDegree_mul hG hQ]
   exact (Nat.add_le_add_left hjQ _).trans_eq (by omega)
 have hDB:b₀.natDegree≤ m+s-k := by
   by_cases hp:P=0
   · simp [hgb,hp]
   · rw [hgb,natDegree_neg,natDegree_mul hG hp]
     omega
 have hvar :=(S.formula γ hγ).trans (linear_tangent ι hd.le hQ hG hg)
 obtain ⟨hden,hnum⟩:=fraction_degrees (S.den_ne γ hγ) hG (S.reduced γ hγ) hvar
 change (S.num γ).natDegree≤(-(a₁*P+b₁*Q)).natDegree at hnum
 have hnum' : (-(a₁*P+b₁*Q)).natDegree≤ m+s+j:= by
   rw [natDegree_neg]
   refine (natDegree_add_le _ _).trans ?_
   have ha₁:a₁.natDegree≤ m:=(degree_extract (by simp) a).trans hm
   have hb₁:b₁.natDegree≤ m+s :=(degree_extract (by simp) b).trans hn
   apply max_le
   · exact (natDegree_mul_le.trans (Nat.add_le_add ha₁ hjP)).trans_eq (Nat.add_assoc _ _ _).symm
   · exact natDegree_mul_le.trans (Nat.add_le_add hb₁ hjQ)
 have hlocal:poleOrderAt S γ≤G.natDegree+k := by
   unfold poleOrderAt relativeDegree
   rw [← hs]
   change max (S.den γ).natDegree ((S.num γ).natDegree-(s+2*j))≤_
   apply max_le
   · omega
   · omega
 set g:=resultant a b m (m+s)
 have hD: (normalize G).natDegree=G.natDegree :=natDegree_normalize
 have hdiv :=padded_order A F ((degree_lift ι a).trans hm) ((degree_lift ι b).trans hn)
   hk (show k≤ m+s by omega) (monic_normalize hG) (by rw [hD]; omega)
   (by rw [hA,hg]; exact (normalize_dvd_iff.mpr (dvd_mul_right G Q)))
   (by rw [hF,hgb]; exact dvd_neg.mpr (normalize_dvd_iff.mpr (dvd_mul_right G P)))
   (hA.symm ▸ hDA) (hF.symm ▸ hDB)
 rw [hD] at hdiv
 let R:=resultant A F m (m+s)
 have hR:algebraMap (PowerSeries L) (LaurentSeries L) R=ι g:= by
   rw [show R= _ from rfl,← resultant_map_map,
     map_lift ι a (fun i=>(S.value γ hγ _).symm.trans_le (S.integral γ hγ 1 i)),
     map_lift ι b (fun i=>(S.value γ hγ _).symm.trans_le (S.integral γ hγ 0 i)),
     resultant_map_map]
   rfl
 have hv : (S.place γ).value g≤WithZero.exp (-(↑(G.natDegree+k) :ℤ)) := by
   rw [S.value γ hγ,← hR]
   exact (LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero L R).mpr
     (PowerSeries.X_pow_dvd_iff.mp hdiv)
 have hlog:=(WithZero.log_le_iff_le_exp (by simpa [g] using hr)).mpr hv
 change poleOrderAt S γ≤KB (S.place γ).value g
 unfold KB
 omega
theorem proof :qE3Ebna.c4 := by
  intro J U B q C S W hd hw
  let a :=S.f.coeff 1
  let b:=S.f.coeff 0
  let s :=B.u₁-B.u₀
  let m:=max a.natDegree (b.natDegree-s)
  have ha :a≠0:= by
    change S.f.coeff 1≠0
    rw [← hd,← leadingCoeff]
    exact leadingCoeff_ne_zero.mpr S.irreducible.ne_zero
  have hm:a.natDegree≤ m:=le_max_left _ _
  have hn:b.natDegree≤ m+s := by have :=le_max_right a.natDegree (b.natDegree-s); omega
  have hW₁:a.natDegree+s≤W:= by
    have h:=(hw 1).resolve_left ha
    simp only [hd,one_mul] at h
    change a.natDegree+B.u₀+s≤W at h
    omega
  have hW₀:b.natDegree≤W:= by
    rcases hw 0 with h | h
    · simp [b,h]
    · change b.natDegree+S.d*B.u₀+0*(B.u₁-B.u₀)≤W at h
      omega
  have hmn:m+s≤W:= by dsimp [m]; omega
  have ht:a.natDegree=m∨b.natDegree=m+s∧b≠0:= by
    by_cases h:a.natDegree=m
    · exact Or.inl h
    · right
      have hb:b≠0:= by
        intro hz
        apply h
        simp [m,hz]
      refine ⟨?_,hb⟩
      dsimp [m] at h ⊢
      omega
  have hr :=padded_ne ha (primitive_pair S.irreducible hd) hm hn ht
  exact (charge S m (m+s) hr (mark S hd m s hm hn rfl hr)).trans
    (Nat.mul_le_mul_right _ (by omega))
end
end qgbTAnb
