import FirstDrop

namespace BCMP430.DropWindow
open FirstDrop UntunedTarget Original Adic Set

private theorem grid_center {s : ℤ} {z : ℝ} (hs : 2≤s) {k : ℕ}
    (hz : 0<z) (zu : z<1) (grid : GridAt s k z) (ends : (g s)^[k] z=0)
    (avoid : ∀ j : ℕ, (g s)^[j+1] z ∉ Ioo 0 z) :
    ∃ c : Center s, c.x=z ∧ c.depth ≤ k := by
  classical
  have sp : (0:ℝ)<s := by exact_mod_cast (show 0<s by omega)
  have top : z<(s:ℝ)/(s+1) := by
    by_contra! bad
    have h := (div_le_iff₀ (by linarith : 0<(s:ℝ)+1)).mp bad
    have u : 0<(s:ℝ)*(1-z) := mul_pos sp (by linarith)
    have vle : (s:ℝ)*(1-z) ≤ z := by linarith only [h]
    have vg : g s z=(s:ℝ)*(1-z) := by
      apply Int.fract_eq_iff.mpr
      exact ⟨u.le,vle.trans_lt zu,-s,by push_cast; ring⟩
    have no := avoid 0
    change g s z ∉ Ioo 0 z at no
    have fix : g s z=z := by rw [vg] at no ⊢; exact le_antisymm vle (le_of_not_gt (fun hh => no ⟨u,hh⟩))
    rw [Function.iterate_fixed fix k] at ends; exact hz.ne' ends
  have H : ∃ j : ℕ, GridAt s j z := ⟨k,grid⟩
  let n := Nat.find H
  have lev : GridAt s n z := Nat.find_spec H
  have npos : 0<n := by
    by_contra! hn
    have he : n=0 := by omega
    obtain ⟨c,hc⟩ := he ▸ lev
    simp only [pow_zero,one_mul] at hc
    rw [hc] at hz zu
    have h₁ : (0:ℤ)<c := by exact_mod_cast hz
    have h₂ : c<(1:ℤ) := by exact_mod_cast zu
    omega
  let c : Center s := ⟨z,n-1,⟨hz,top⟩,by simpa only [show n-1+1=n by omega] using lev,
    Nat.find_min H (by change n-1<n; omega),avoid⟩
  exact ⟨c,rfl,by change n-1+1 ≤ k; have h : n≤k := Nat.find_min' H grid; omega⟩

/-- A first strict drop places the parameter in the *open matching gap* (L,R),
    hence also in the open tuning window (T,R). The grid level is minimized. -/
theorem first_drop_gap {s : ℤ} (hs : 2≤s) {x : ℝ} (x0 : 0<x) (xtop : x<(s:ℝ)/(s+1))
    {k : ℕ} (hk : 0<k) (prior : ∀ i : ℕ, 0 < i → i < k → x ≤ (g s)^[i] x)
    (drop : (g s)^[k] x < x) : ∃ c : Center s, c.L < x ∧ x < c.R := by
  let A := (-(s:ℝ))^k
  let S := (s:ℝ)^k
  let y := (g s)^[k] x
  have hs1 : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  have sp : (0:ℝ)<s := zero_lt_one.trans hs1
  have hS : (s:ℝ)≤S := by simpa using (pow_le_pow_right₀ hs1.le (show 1≤k by omega) : (s:ℝ)^1 ≤ (s:ℝ)^k)
  have hA : |A|=S := by simp [A,S,abs_pow,abs_of_pos sp]
  have hn : A≠0 := pow_ne_zero _ (neg_ne_zero.mpr sp.ne')
  have yn : 0≤y := by obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'; change 0≤(g s)^[i+1] x; rw [Function.iterate_succ_apply']; exact Int.fract_nonneg _
  obtain ⟨a,ha⟩ := iterate_lift s x k
  change A*x=(a:ℝ)+y at ha
  let z := (a:ℝ)/A
  have gz : A*z=a := by dsimp only [z]; field_simp
  have delta : A*(x-z)=y := by rw [mul_sub,gz,ha]; ring
  have absdelta := congrArg abs delta
  rw [abs_mul,hA,abs_of_nonneg yn] at absdelta
  change y < x at drop
  have coarse : (s:ℝ)*|x-z| < x := (mul_le_mul_of_nonneg_right hS (abs_nonneg _)).trans_lt (absdelta.trans_lt drop)
  have small : |x-z|<x/(s:ℝ) := (lt_div_iff₀ sp).mpr (by linarith only [coarse])
  have room : x+x/(s:ℝ)<1 := by
    have H := (lt_div_iff₀ (by linarith : 0<(s:ℝ)+1)).mp xtop
    have E := div_mul_cancel₀ x sp.ne'; apply (mul_lt_mul_iff_of_pos_right sp).mp; linarith only [H,E]
  have dx : x/(s:ℝ) ≤ x := (div_le_iff₀ sp).mpr (by nlinarith [mul_nonneg x0.le (sub_nonneg.mpr hs1.le)])
  obtain ⟨d₁,d₂⟩ := abs_lt.mp small
  have zp : 0<z := by linarith
  have zu : z<1 := by linarith
  have ends : (g s)^[k] z=0 := by
    obtain ⟨b,hb⟩ := iterate_lift s z k
    change A*z=(b:ℝ)+(g s)^[k] z at hb
    rw [gz] at hb
    have unit : (g s)^[k] z ∈ Ico (0:ℝ) 1 := by
      obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'; rw [Function.iterate_succ_apply']; exact ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
    have equality : (g s)^[k] z=((a-b:ℤ):ℝ) := by push_cast; linarith
    rw [equality] at unit ⊢
    have lo : (0:ℤ)≤a-b := by exact_mod_cast unit.1
    have hi : a-b<(1:ℤ) := by exact_mod_cast unit.2
    exact_mod_cast (show a-b=0 by omega)
  have grid : GridAt s k z := by
    rcases Nat.even_or_odd k with h|h
    · exact ⟨a,by simpa [A,h.neg_pow] using gz⟩
    · refine ⟨-a,?_⟩
      have h' : -S*z=a := by simpa only [A,S,h.neg_pow] using gz
      change S*z=((-a:ℤ):ℝ)
      push_cast; linarith only [h']
  obtain ⟨c,eq,depth⟩ := grid_center hs zp zu grid ends (rounded_avoids hs hk prior drop gz delta zu)
  have ord := endpoint_order hs c
  have bound {j : ℕ} (hj : j≤k) : 1/S ≤ (s:ℝ)⁻¹^j := by
    rw [inv_pow,one_div]; exact inv_anti₀ (pow_pos sp j) (pow_le_pow_right₀ hs1.le hj)
  have ez : S*|x-z| < x := absdelta.trans_lt drop
  have mesh : |x-z| < x*(1/S) := by rw [←div_eq_mul_one_div]; apply (lt_div_iff₀ (pow_pos sp k)).mpr; linarith only [ez]
  refine ⟨c,?_⟩
  rcases Nat.even_or_odd k with par|par
  · have sign : A=S := par.neg_pow _
    have xz : z≤x := by rw [sign] at delta; exact sub_nonneg.mp (nonneg_of_mul_nonneg_right (delta.symm ▸ yn) (pow_pos sp k))
    have pk : c.p≤k := by have evenk := Nat.even_iff.mp par; dsimp [Center.p]; omega
    have m := mesh.trans_le (mul_le_mul_of_nonneg_left (bound pk) x0.le)
    rw [abs_of_nonneg (sub_nonneg.mpr xz)] at m
    have hp : 0<1-(s:ℝ)⁻¹^c.p := by
      have pp : c.p≠0 := by dsimp [Center.p,Center.depth]; omega
      exact sub_pos.mpr (pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hs1) pp)
    exact ⟨ord.2.1.trans_le (eq ▸ xz),(lt_div_iff₀ hp).mpr (by rw [eq]; linarith only [m])⟩
  · have sign : A= -S := par.neg_pow _
    have xz : x≤z := by rw [sign,neg_mul] at delta; apply le_of_not_gt; intro h; nlinarith [mul_pos (pow_pos sp k) (sub_pos.mpr h)]
    have qk : c.q≤k := by have oddk := Nat.odd_iff.mp par; dsimp [Center.q]; omega
    have m := mesh.trans_le (mul_le_mul_of_nonneg_left (bound qk) x0.le)
    rw [abs_of_nonpos (sub_nonpos.mpr xz)] at m
    refine ⟨(div_lt_iff₀ (by positivity : 0<1+(s:ℝ)⁻¹^c.q)).mpr ?_,?_⟩
    · rw [eq]; linarith only [m]
    · rw [←eq] at xz; exact xz.trans_lt ord.2.2

/-- No UT point in the interior of the ambient segment has an iterate below itself. -/
theorem ut_survives {s : ℤ} (hs : 2≤s) {x : ℝ} (hu : x∈UT s) (hp : 0<x)
    (ht : x<(s:ℝ)/(s+1)) : ∀ j, x ≤ (g s)^[j] x := by
  intro j
  by_contra! bad
  classical
  let P := fun k : ℕ => (g s)^[k] x < x
  have H : ∃ k,P k := ⟨j,bad⟩
  let k := Nat.find H
  have drop : P k := Nat.find_spec H
  have hk : 0<k := by
    by_contra! h
    have hz : k=0 := by omega
    rw [hz] at drop
    exact (lt_irrefl x) drop
  obtain ⟨c,l,r⟩ := first_drop_gap hs hp ht hk (fun i _ hi => le_of_not_gt (Nat.find_min H hi)) drop
  exact hu.2 c ⟨(endpoint_order hs c).1.trans l,r⟩

#print axioms first_drop_gap
#print axioms ut_survives
end BCMP430.DropWindow
