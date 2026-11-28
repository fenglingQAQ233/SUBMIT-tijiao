import CenterTape

namespace BCMP430.GridProbes
open Set Original Adic UntunedTarget Components ClockTotal Tape

/-- Keep the grid probe and its order relative to the closed tuning window in the output.
    The probe is a mesh point of specified level n, not necessarily a pseudocenter. -/
theorem nearest {s : ℤ} (hs : 2≤s) {x : ℝ} (hu : x∈UT s) (hp : 0<x)
    (n : ℕ) (hn : 0<n) (room : x+(s:ℝ)⁻¹^n < (s:ℝ)/(s+1)) :
    ∃ c : Center s, x≤c.T ∧ x<c.x ∧ c.depth≤n ∧
      c.x-x ≤ 2*(s:ℝ)⁻¹^c.depth ∧ x*(s:ℝ)⁻¹^(2*c.depth+1)<(s:ℝ)⁻¹^n := by
  have hs1 : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  have sp : (0:ℝ)<s := zero_lt_one.trans hs1
  let b := (s:ℝ)⁻¹
  let S := (s:ℝ)^n
  have pos : 0<S := pow_pos sp _
  have bp : 0<b := inv_pos.mpr sp
  have bl : b<1 := inv_lt_one_of_one_lt₀ hs1
  let a := ⌊S*x⌋+1
  let y := (a:ℝ)/S
  have id : S*y=(a:ℝ) := by dsimp [y]; field_simp
  have yx : x<y := (lt_div_iff₀ pos).mpr (by dsimp [a]; push_cast; linarith only [Int.lt_floor_add_one (S*x)])
  have hy : y≤x+b^n := by
    apply (div_le_iff₀ pos).mpr
    have bm : b^n*S=1 := by dsimp [S,b]; rw [inv_pow,inv_mul_cancel₀ pos.ne']
    rw [add_mul,bm]; dsimp [a]; push_cast; linarith only [Int.floor_le (S*x)]
  have zero : (g s)^[n] y=0 := by
    obtain ⟨k,hk⟩ := FirstDrop.iterate_lift s y n
    have u : (g s)^[n] y ∈ Ico (0:ℝ) 1 := by obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'; rw [Function.iterate_succ_apply']; exact ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
    have H : ∃ l : ℤ, (g s)^[n] y=l := by
      rcases Nat.even_or_odd n with h|h
      · rw [h.neg_pow] at hk; change S*y=_ at hk; exact ⟨a-k,by push_cast; linarith only [id,hk]⟩
      · rw [h.neg_pow,neg_mul] at hk; change -(S*y)=_ at hk; exact ⟨-a-k,by push_cast; linarith only [id,hk]⟩
    obtain ⟨l,hl⟩ := H; rw [hl] at u ⊢
    have l₁ : (0:ℤ)≤l := by exact_mod_cast u.1
    have l₂ : l<(1:ℤ) := by exact_mod_cast u.2
    exact_mod_cast (show l=0 by omega)
  classical
  have H : ∃ j, (g s)^[j] y < y := ⟨n,zero ▸ hp.trans yx⟩
  let j := Nat.find H
  have drop : (g s)^[j] y<y := Nat.find_spec H
  have jp : 0<j := by by_contra! h; exact (lt_irrefl y) ((show j=0 by omega) ▸ drop : (g s)^[0] y<y)
  obtain ⟨c,ly,yr⟩ := DropWindow.first_drop_gap hs (hp.trans yx) (hy.trans_lt room) jp (fun i _ hi => le_of_not_gt (Nat.find_min H hi)) drop
  have xt : x≤c.T := le_of_not_gt (fun h => hu.2 c ⟨h,yx.trans yr⟩)
  have order := endpoint_order hs c
  have xc : x<c.x := xt.trans_lt (order.1.trans order.2.1)
  let e := c.depth
  let u := b^c.p
  let v := b^c.q
  have pp : e≤c.p := by dsimp [e,Center.p]; omega
  have qq : e≤c.q := by dsimp [e,Center.q]; omega
  have p0 : 0<c.p := by dsimp [Center.p,Center.depth]; omega
  have iu : 0<u := pow_pos bp _
  have iv : 0<v := pow_pos bp _
  have ul : u<1 := pow_lt_one₀ bp.le bl p0.ne'
  have rr : c.R*(1-u)=c.x := div_mul_cancel₀ _ (by linarith)
  have ll : c.L*(1+v)=c.x := div_mul_cancel₀ _ (by linarith)
  have lp : 0<c.L := by change 0<c.x/(1+v); exact div_pos c.inside.1 (by linarith)
  have rp : 0<c.R := c.inside.1.trans order.2.2
  have R1 : c.R < 1 := by
    have p2 : 2≤c.p := by dsimp [Center.p,Center.depth]; omega
    have ub : u≤b^2 := pow_le_pow_of_le_one bp.le bl.le p2
    have b2 : b^2*((s:ℝ)+1) ≤ 1 := by
      have s2 : (2:ℝ)≤s := by exact_mod_cast hs
      apply (mul_le_mul_iff_of_pos_right (show 0<(s:ℝ)^2 by positivity)).mp
      dsimp [b]; field_simp; nlinarith [sq_nonneg ((s:ℝ)-1)]
    have xx := (lt_div_iff₀ (by linarith : 0<(s:ℝ)+1)).mp c.inside.2
    have us := mul_le_mul_of_nonneg_right ub (show 0≤(s:ℝ)+1 by linarith)
    apply (div_lt_one (by linarith : 0<1-u)).mpr
    exact lt_of_mul_lt_mul_right (a:=(s:ℝ)+1) (by nlinarith only [xx,us,b2]) (by linarith)
  have L1 : c.L<1 := order.2.1.trans (order.2.2.trans R1)
  have sep : |c.x-y| < b^e := by
    have uE : u≤b^e := pow_le_pow_of_le_one bp.le bl.le pp
    have vE : v≤b^e := pow_le_pow_of_le_one bp.le bl.le qq
    apply abs_lt.mpr; constructor <;> nlinarith only [ly,yr,rr,ll,uE,vE,mul_pos iu (sub_pos.mpr R1),mul_pos iv (sub_pos.mpr L1)]
  have depth : e≤n := by
    by_contra! ne
    have both : GridAt s e y := by
      have f : e=e-n+n := by omega
      refine ⟨s^(e-n)*a,?_⟩; nth_rewrite 1 [f]; rw [pow_add,mul_assoc,id]; push_cast; rfl
    obtain ⟨d,hd⟩ := c.onGrid
    change (s:ℝ)^e*c.x=(d:ℝ) at hd
    obtain ⟨f,hf⟩ := both
    have powpos : 0<(s:ℝ)^e := pow_pos sp _
    have h := (mul_lt_mul_iff_of_pos_left powpos).mpr sep
    rw [←abs_of_pos powpos,←abs_mul,abs_of_pos powpos, mul_sub,hd,hf] at h
    have M : (s:ℝ)^e*b^e=1 := by dsimp [b]; rw [inv_pow,mul_inv_cancel₀ powpos.ne']
    rw [M] at h
    have eqz : d=f := by
      have hi : |d-f|<(1:ℤ) := by exact_mod_cast h
      have both := abs_lt.mp hi
      omega
    have eqxy : c.x=y := by apply (mul_right_inj' powpos.ne').mp; rw [hd,hf,eqz]
    apply c.offGrid
    have le : n≤c.depthPred := by change c.depthPred+1>n at ne; omega
    have E : c.depthPred=c.depthPred-n+n := by omega
    refine ⟨s^(c.depthPred-n)*a,?_⟩
    nth_rewrite 1 [E]; rw [pow_add,mul_assoc,eqxy,id]; push_cast; rfl
  have mesh : b^n≤b^e := pow_le_pow_of_le_one bp.le bl.le depth
  have near : c.x-x ≤ 2*b^e := by linarith only [(abs_lt.mp sep).2,hy,mesh]
  have par : u+v=b^e*(1+b) := by
    rcases Nat.even_or_odd e with E|E
    · have e0 := Nat.even_iff.mp E
      have p : c.p=e := by dsimp [Center.p]; change c.depth%2=0 at e0; omega
      have q : c.q=e+1 := by dsimp [Center.q]; change c.depth%2=0 at e0; dsimp [e]; omega
      simp only [u,v,p,q,pow_succ]; ring
    · have e1 := Nat.odd_iff.mp E
      have p : c.p=e+1 := by dsimp [Center.p]; change c.depth%2=1 at e1; dsimp [e]; omega
      have q : c.q=e := by dsimp [Center.q]; change c.depth%2=1 at e1; dsimp [e]; omega
      simp only [u,v,p,q,pow_succ]; ring
  have vv : v≤b := by change b^c.q≤b; simpa only [pow_one] using pow_le_pow_of_le_one bp.le bl.le (show 1≤c.q by dsimp [Center.q,Center.depth]; omega)
  have DD : (c.R-c.L)*(1+v)=c.R*(u+v) := by linarith only [rr,ll]
  rw [par] at DD
  have low : c.R*b^e ≤ c.R-c.L := by
    apply (mul_le_mul_iff_of_pos_right (show 0<1+v by linarith)).mp
    nlinarith only [DD,mul_nonneg (mul_nonneg rp.le (pow_nonneg bp.le e)) (sub_nonneg.mpr vv)]
  have qle : c.q≤e+1 := by dsimp [Center.q,e]; omega
  have vlow : b^(e+1) ≤ v := pow_le_pow_of_le_one bp.le bl.le qle
  have prod := mul_le_mul vlow low (mul_nonneg rp.le (pow_nonneg bp.le e)) iv.le
  have collar := (GridDensity.collar hs c).1
  change c.L-c.T=v*(c.R-c.L) at collar
  have exp : b^(2*e+1) = b^(e+1)*b^e := by rw [←pow_add]; congr 1; omega
  refine ⟨c,xt,xc,depth,near,?_⟩
  change x*b^(2*e+1)<b^n
  rw [exp]; nlinarith only [prod,collar,xt,ly,hy,mul_nonneg (sub_nonneg.mpr (yx.trans yr).le) (mul_nonneg (pow_nonneg bp.le (e+1)) (pow_nonneg bp.le e))]

#print axioms nearest
end BCMP430.GridProbes
