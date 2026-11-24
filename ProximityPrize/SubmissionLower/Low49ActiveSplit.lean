import ProximityPrize.SubmissionLower.Low48BentSupport

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Low49ActiveSplit

private theorem distribute {n al ah bl bh : ℕ} (ha : al ≤ ah) (hb : bl ≤ bh)
    (hl : al + bl ≤ n) (hh : n ≤ ah + bh) :
    ∃ a b, a+b=n ∧ al≤a ∧ a≤ah ∧ bl≤b ∧ b≤bh := by
  let a := max al (n-bh)
  exact ⟨a,n-a,by dsimp [a]; omega⟩

private theorem distribute_under {n a b : ℕ} (h : n ≤ a+b)
    (hp : a%2=0 ∨ b%2=0) :
    ∃ x y, x+y=n ∧ x≤a ∧ y≤b ∧ (x%2=0 ∨ y%2=0) := by
  rcases hp with ha|hb
  · let x := min n a
    exact ⟨x,n-x,by dsimp [x]; omega⟩
  · let y := min n b
    exact ⟨n-y,y,by dsimp [y]; omega⟩

private theorem distribute_over {n al ah bl bh : ℕ} (ha : al≤ah) (hb : bl≤bh)
    (hl : al+bl≤n) (hh : n≤ah+bh) (he : ah%2=0 ∧ bh%2=0)
    (hp : al%2=0 ∨ bl%2=0) :
    ∃ x y, x+y=n ∧ al≤x ∧ x≤ah ∧ bl≤y ∧ y≤bh ∧ (x%2=0 ∨ y%2=0) := by
  by_cases hn : n%2=0
  · rcases hp with hA|hB
    · let x := min ah (n-bl)
      let w := x - x%2
      exact ⟨w,n-w,by dsimp [w,x]; omega⟩
    · let y := min bh (n-al)
      let w := y-y%2
      exact ⟨n-w,w,by dsimp [w,y]; omega⟩
  · obtain ⟨x,y,hx,ha,hxa,hb,hyb⟩ := distribute ha hb hl hh
    exact ⟨x,y,hx,ha,hxa,hb,hyb,by omega⟩

private theorem split_secondary {y z ja jb ta tb ca cb : ℕ}
    (hja : 3*ta≤ja ∧ 2*ca≤ja ∧ ca≤2*ta)
    (hjb : 3*tb≤jb ∧ 2*cb≤jb ∧ cb≤2*tb)
    (hev : ja%2=0 ∧ jb%2=0 ∧ ta%2=0 ∧ tb%2=0 ∧ ca%2=0 ∧ cb%2=0)
    (hp : (ca/2)%2=0 ∨ (cb/2)%2=0)
    (h : z≤ta+tb ∧ 2*y+3*z≤ja+jb) :
    ∃ ya yb za zb,
      ya+yb=y ∧ za+zb=z ∧ za≤ta ∧ zb≤tb ∧ 2*ya+3*za≤ja ∧ 2*yb+3*zb≤jb ∧
      (if y+2*z≤ca+cb then ya+2*za≤ca ∧ yb+2*zb≤cb
       else ca≤ya+2*za ∧ cb≤yb+2*zb) := by
  by_cases hc : y+2*z≤ca+cb
  · obtain ⟨za,zb,hz,_,hza,_,hzb⟩ := distribute (n:=z) (al:=0) (bl:=0)
      (ah:=ca/2) (bh:=cb/2) (by omega) (by omega) (by omega) (by omega)
    obtain ⟨ya,yb,hy,_,hya,_,hyb⟩ := distribute (n:=y) (al:=0) (bl:=0)
      (ah:=ca-2*za) (bh:=cb-2*zb) (by omega) (by omega) (by omega) (by omega)
    exact ⟨ya,yb,za,zb,hy,hz,by omega,by omega,by omega,by omega,by simp only [hc,ite_true]; omega⟩
  · have hs : ∃ za zb, za+zb=z ∧ za≤ta ∧ zb≤tb ∧
        (ca-2*za)+(cb-2*zb) = ca+cb-2*z ∧ (za%2=0 ∨ zb%2=0) := by
      by_cases hz : 2*z≤ca+cb
      · obtain ⟨za,zb,hz',hza,hzb,hep⟩ :=
          distribute_under (n:=z) (a:=ca/2) (b:=cb/2) (by omega) hp
        exact ⟨za,zb,hz',by omega,by omega,by omega,hep⟩
      · obtain ⟨za,zb,hz',hza,hza',hzb,hzb',hep⟩ := distribute_over
          (al:=ca/2) (bl:=cb/2) (ah:=ta) (bh:=tb)
          (by omega) (by omega) (by omega) h.1 ⟨hev.2.2.1,hev.2.2.2.1⟩ hp
        exact ⟨za,zb,hz',hza',hzb',by omega,hep⟩
    obtain ⟨za,zb,hz,hza,hzb,hsmall,hParity⟩ := hs
    have hhalves : (ja-3*za+ (jb-3*zb))/2 = (ja-3*za)/2+(jb-3*zb)/2 := by omega
    obtain ⟨ya,yb,hy,hya,hya',hyb,hyb'⟩ := distribute (n:=y)
      (al:=ca-2*za) (bl:=cb-2*zb) (ah:=(ja-3*za)/2) (bh:=(jb-3*zb)/2)
      (by omega) (by omega) (by omega) (by omega)
    exact ⟨ya,yb,za,zb,hy,hz,hza,hzb,by omega,by omega,by simp only [hc,ite_false]; omega⟩

theorem split {x y z ja jb ta tb ca cb : ℕ}
    (hja : 3*ta≤ja ∧ 2*ca≤ja ∧ ca≤2*ta)
    (hjb : 3*tb≤jb ∧ 2*cb≤jb ∧ cb≤2*tb)
    (hev : ja%2=0 ∧ jb%2=0 ∧ ta%2=0 ∧ tb%2=0 ∧ ca%2=0 ∧ cb%2=0)
    (hp : (ca/2)%2=0 ∨ (cb/2)%2=0)
    (h : z≤ta+tb ∧ x+2*y+3*z≤ja+jb) :
    ∃ xa xb ya yb za zb,
      xa+xb=x ∧ ya+yb=y ∧ za+zb=z ∧ za≤ta ∧ zb≤tb ∧
      xa+2*ya+3*za≤ja ∧ xb+2*yb+3*zb≤jb ∧
      (xa+ya+za-(ja-ca))+(xb+yb+zb-(jb-cb)) = x+y+z-(ja+jb-(ca+cb)) := by
  obtain ⟨ya,yb,za,zb,hy,hz,hza,hzb,hya,hyb,hr⟩ :=
    split_secondary (y:=y) (z:=z) hja hjb hev hp (by omega)
  let aa := ja-ca-(ya+za)
  let ab := jb-cb-(yb+zb)
  let ma := ja-(2*ya+3*za)
  let mb := jb-(2*yb+3*zb)
  by_cases hc : y+2*z≤ca+cb
  · simp only [hc,ite_true] at hr
    by_cases hl : x+y+z≤ja+jb-(ca+cb)
    · obtain ⟨xa,xb,hx,_,hxa,_,hxb⟩ := distribute (n:=x) (al:=0) (bl:=0)
        (ah:=aa) (bh:=ab) (by omega) (by omega) (by omega) (by dsimp [aa,ab]; omega)
      exact ⟨xa,xb,ya,yb,za,zb,hx,hy,hz,hza,hzb,by dsimp [aa] at hxa; omega,
        by dsimp [ab] at hxb; omega,by dsimp [aa,ab] at *; omega⟩
    · obtain ⟨xa,xb,hx,hxa,hxa',hxb,hxb'⟩ := distribute (n:=x) (al:=aa) (bl:=ab)
        (ah:=ma) (bh:=mb) (by dsimp [aa,ma]; omega) (by dsimp [ab,mb]; omega)
        (by dsimp [aa,ab]; omega) (by dsimp [ma,mb]; omega)
      exact ⟨xa,xb,ya,yb,za,zb,hx,hy,hz,hza,hzb,by dsimp [ma] at hxa'; omega,
        by dsimp [mb] at hxb'; omega,by dsimp [aa,ab] at *; omega⟩
  · simp only [hc,ite_false] at hr
    obtain ⟨xa,xb,hx,_,hxa,_,hxb⟩ := distribute (n:=x) (al:=0) (bl:=0)
      (ah:=ma) (bh:=mb) (by omega) (by omega) (by omega) (by dsimp [ma,mb]; omega)
    exact ⟨xa,xb,ya,yb,za,zb,hx,hy,hz,hza,hzb,by dsimp [ma] at hxa; omega,
      by dsimp [mb] at hxb; omega,by dsimp [ma,mb] at *; omega⟩

end Low49ActiveSplit
