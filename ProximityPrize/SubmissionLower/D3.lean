import ProximityPrize.SubmissionLower.CQ
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
namespace P1
noncomputable section
open Polynomial gR ProximityPrize.Benchmark
open Aj (GC)
private theorem ari (f :K[X]) (x :K) : (jH f).eval (C x)=C (f.eval x) :=
 Aj.ari f x
private def aCJ:K →+* kB :=
 Aj.GC.comp Polynomial.C
private theorem bFL (G:K[X]) :
  sZ (jH G)=G.map aCJ :=
 Polynomial.map_map Polynomial.C GC G
end
end P1
end
section
set_option backward.isDefEq.respectTransparency false
namespace P1
noncomputable section
open Polynomial Matrix gR ProximityPrize.Benchmark
open scoped BigOperators
open bai
private theorem cNu {F ι:Type} [Field F] [Fintype ι] [DecidableEq ι]
  (q:ℕ) [ExpChar F q] (x :ι→F) (hx :Function.Injective x)
  (hfixed : ∀ i,x i^q=x i) (u v :ι→F) (γ:F) (k l t:ℕ)
  (hsize :k+l+t≤Fintype.card ι) (P:F[X]) (hp:P.degree<k)
  (S:Finset ι) (hs :S.card≤t) (hagree : ∀ i∉S,u i+γ*v i=P.eval (x i)) :
  ((AI q x u v l t).map (evalRingHom γ)).rank≠t+1 := by
 classical
 let E :=mL x S
 have hd:E.natDegree≤t:=(ZQ x S).le.trans hs
 let z :Fin (t+1)→F:= fun j=>E.coeff j.val
 let B:=(AI q x u v l t).map (evalRingHom γ)
 have hv :B.mulVecLin z=0 :=
  b8c q x hx hfixed u v γ k l t hsize P hp S hs hagree
 intro hr
 have hi:=kL.ezQ B (by rwa [Fintype.card_fin])
 have hz :z=0:=hi (hv.trans (map_zero B.mulVecLin).symm)
 have h:=congrFun hz (⟨E.natDegree,by omega⟩:Fin (t+1))
 change E.coeff E.natDegree=0 at h
 exact one_ne_zero ((S8 x S).coeff_natDegree.symm.trans h)
end
end P1
end
section
set_option backward.isDefEq.respectTransparency false
namespace P1
open Polynomial Matrix gR ProximityPrize.Benchmark
private theorem cIp {c n n' H b:ℕ}
  (hn:n=n') (hc:c≤n*H) (hb:n' * H=b) :c≤b :=
 hb ▸ hn ▸ hc
end P1
end
