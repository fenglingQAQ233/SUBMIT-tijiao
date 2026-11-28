import DropWindow

namespace BCMP430.GridDensity
open Original Adic FirstDrop DropWindow UntunedTarget Set

private theorem frac_iter {s : ℤ} {x : ℝ} {n : ℕ} (hn : 0<n) :
    (g s)^[n] x = Int.fract ((-(s:ℝ))^n*x) := by
  obtain ⟨a,ha⟩ := iterate_lift s x n
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have u : (g s)^[k+1] x ∈ Ico (0:ℝ) 1 := by rw [Function.iterate_succ_apply']; exact ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
  exact (Int.fract_eq_iff.mpr ⟨u.1,u.2,a,by linarith only [ha]⟩).symm

/-- Terminating probes strictly to the right of any parameter; strict even when x itself is on a grid. -/
private theorem probe {s : ℤ} (hs : 2≤s) (x : ℝ) {δ : ℝ} (hδ : 0<δ) :
    ∃ y, x<y ∧ y<x+δ ∧ ∃ k : ℕ, (g s)^[k] y=0 := by
  have sp : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  let b := (s:ℝ)⁻¹
  have bl : b<1 := inv_lt_one_of_one_lt₀ sp
  have bp : 0<b := inv_pos.mpr (zero_lt_one.trans sp)
  obtain ⟨N,hN⟩ := exists_pow_lt_of_lt_one hδ bl
  let n := N+1
  let S := (s:ℝ)^n
  have s0 : 0<S := pow_pos (zero_lt_one.trans sp) _
  let a : ℤ := ⌊S*x⌋+1
  have A : S*x < (a:ℝ) := by dsimp [a]; push_cast; exact Int.lt_floor_add_one _
  have B : (a:ℝ)≤S*x+1 := by dsimp [a]; push_cast; linarith only [Int.floor_le (S*x)]
  let y := (a:ℝ)/S
  have id : S*y=a := by dsimp [y]; field_simp
  have eq : 1/S = b^n := by simp [S,b,one_div,inv_pow]
  have mesh : 1/S < δ := eq ▸ ((pow_le_pow_of_le_one bp.le bl.le (show N≤n by omega)).trans_lt hN)
  refine ⟨y,(lt_div_iff₀ s0).mpr (by linarith only [A]),?_,n,?_⟩
  · have lim : (a:ℝ)/S ≤ x+1/S := (div_le_iff₀ s0).mpr (by rw [add_mul,div_mul_cancel₀ _ s0.ne']; linarith only [B])
    dsimp only [y]; linarith
  · rw [frac_iter (show 0<n by omega)]
    rcases Nat.even_or_odd n with par|par
    · rw [par.neg_pow]; change Int.fract (S*y)=0; rw [id,Int.fract_intCast]
    · rw [par.neg_pow,neg_mul]; change Int.fract (-(S*y))=0; rw [id,←Int.cast_neg,Int.fract_intCast]

private theorem gap {s : ℤ} (hs : 2≤s) {y : ℝ} (hp : 0<y) (ht : y<(s:ℝ)/(s+1))
    (h : ∃ k : ℕ, (g s)^[k] y=0) : ∃ c : Center s, c.L<y ∧ y<c.R := by
  classical
  obtain ⟨k,hk⟩ := h
  have ex : ∃ j, (g s)^[j] y<y := ⟨k,by rwa [hk]⟩
  let j := Nat.find ex
  have drop : (g s)^[j] y<y := Nat.find_spec ex
  have pos : 0<j := by
    by_contra! hn
    have e : j=0 := by omega
    exact (lt_irrefl y) (e ▸ drop : (g s)^[0] y < y)
  exact first_drop_gap hs hp ht pos (fun i _ hi => le_of_not_gt (Nat.find_min ex hi)) drop

/-- The tuning-only collar has exactly v times the width of the matching interval.
    It forces the width to vanish if the gap meets a right-hand probe close to UT. -/
theorem collar {s : ℤ} (hs : 2≤s) (c : Center s) :
    c.L-c.T = (s:ℝ)⁻¹^c.q*(c.R-c.L) ∧ (c.R-c.L)^2 ≤ ((s:ℝ)+1)*(c.L-c.T) := by
  have sp : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  have sp0 : (0:ℝ)<s := zero_lt_one.trans sp
  let b := (s:ℝ)⁻¹
  let u := b^c.p
  let v := b^c.q
  have bl : b<1 := inv_lt_one_of_one_lt₀ sp
  have bp : 0<b := inv_pos.mpr sp0
  have pn : 2≤c.p := by dsimp [Center.p,Center.depth]; omega
  have ul : u<1 := pow_lt_one₀ bp.le bl (by omega : c.p≠0)
  have vp : 0<v := pow_pos bp _
  have ue : c.R*(1-u)=c.x := div_mul_cancel₀ _ (by linarith)
  have ve : c.L*(1+v)=c.x := div_mul_cancel₀ _ (by linarith)
  have e : c.L-c.T=v*(c.R-c.L) := by change c.L-(c.x-v*c.R)=_; linarith only [ve]
  refine ⟨e,?_⟩
  have qle : c.q ≤ c.p+1 := by dsimp [Center.p,Center.q]; omega
  have U : u*b ≤ v := by change b^c.p*b ≤ b^c.q; rw [←pow_succ]; exact pow_le_pow_of_le_one bp.le bl.le qle
  have sb : b*(s:ℝ)=1 := inv_mul_cancel₀ sp0.ne'
  have uu : u≤s*v := by have h := mul_le_mul_of_nonneg_right U sp0.le; rwa [mul_assoc,sb,mul_one,mul_comm v] at h
  have ub : u≤b^2 := pow_le_pow_of_le_one bp.le bl.le pn
  have b2 : b^2*((s:ℝ)+1) ≤ 1 := by
    have s2 : (2:ℝ)≤s := by exact_mod_cast hs
    have ss : 0<(s:ℝ)^2 := by positivity
    apply (mul_le_mul_iff_of_pos_right ss).mp
    dsimp [b]; field_simp; nlinarith [sq_nonneg ((s:ℝ)-1)]
  have xu := c.inside.2
  have xx := (lt_div_iff₀ (by linarith : 0<(s:ℝ)+1)).mp xu
  have us := mul_le_mul_of_nonneg_right ub (show 0≤(s:ℝ)+1 by linarith)
  have cu : c.x < 1-u := (lt_of_mul_lt_mul_right (a:=(s:ℝ)+1) (by nlinarith only [xx,us,b2]) (by linarith))
  have Ru : c.R < 1 := (div_lt_one (by linarith : 0<1-u)).mpr cu
  have ord := endpoint_order hs c
  have rp : 0<c.R := c.inside.1.trans ord.2.2
  have lp : 0<c.L := by change 0<c.x/(1+v); exact div_pos c.inside.1 (by linarith)
  have up : 0≤u := pow_nonneg bp.le _
  have D : c.R-c.L ≤ u+v := by nlinarith only [ue,ve,mul_nonneg up (sub_nonneg.mpr Ru.le),mul_nonneg vp.le (sub_nonneg.mpr (ord.2.1.trans (ord.2.2.trans Ru)).le)]
  have non : 0≤c.R-c.L := sub_nonneg.mpr (ord.2.1.trans ord.2.2).le
  rw [e]; nlinarith only [mul_le_mul_of_nonneg_right (show c.R-c.L≤((s:ℝ)+1)*v by linarith only [D,uu]) non]

/-- Every positive interior untuned parameter has actual geometric window right endpoints
    strictly to its right in every neighborhood. No index or dominance assumption. -/
theorem geometric_right {s : ℤ} (hs : 2≤s) {x : ℝ} (hu : x∈UT s) (hp : 0<x)
    (top : x<(s:ℝ)/(s+1)) {ε : ℝ} (he : 0<ε) : ∃ c : Center s, x<c.R ∧ c.R<x+ε := by
  have pos : (0:ℝ)<s+1 := by exact_mod_cast (show 0<s+1 by omega)
  let t := ε/2
  have tp : 0<t := half_pos he
  let δ := min ((s:ℝ)/(s+1)-x) (min t (t^2/((s:ℝ)+1)))
  have dp : 0<δ := lt_min (sub_pos.mpr top) (lt_min tp (div_pos (sq_pos_of_pos tp) pos))
  obtain ⟨y,xy,yd,k,hk⟩ := probe hs x dp
  have top' : y<(s:ℝ)/(s+1) := by have h : δ≤(s:ℝ)/(s+1)-x := min_le_left ..; linarith
  obtain ⟨c,ly,yr⟩ := gap hs (hp.trans xy) top' ⟨k,hk⟩
  have xt : x≤c.T := le_of_not_gt (fun bad => hu.2 c ⟨bad,xy.trans yr⟩)
  have width := (collar hs c).2
  have h₁ : δ≤t := (min_le_right ..).trans (min_le_left ..)
  have h₂ : δ≤t^2/((s:ℝ)+1) := (min_le_right ..).trans (min_le_right ..)
  have hd : c.L-c.T<t^2/((s:ℝ)+1) := by linarith only [h₂,xt,ly,yd]
  have sq := (lt_div_iff₀ pos).mp hd
  have small : c.R-c.L<t := by nlinarith only [sq,width,sq_nonneg (c.R-c.L-t),tp, mul_self_lt_mul_self_iff (a:=t) (b:=c.R-c.L)]
  refine ⟨c,xy.trans yr,?_⟩; dsimp [t] at small h₁; linarith only [small,h₁,yd,ly]

#print axioms collar
#print axioms geometric_right
end BCMP430.GridDensity
