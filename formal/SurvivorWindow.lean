import FixedTail

namespace BCMP430.SurvivorWindow
open Set UntunedTarget Original Adic

private theorem window_data {s : ℤ} (hs : 2≤s) (c : Center s) :
    c.R<1 ∧ (s:ℝ)^c.p*(c.R-c.x)=c.R ∧ (s:ℝ)^c.q*(c.x-c.L)=c.L ∧
    (s:ℝ)^c.q*(c.x-c.T)=c.R := by
  have sr : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  have sp := zero_lt_one.trans sr
  let b := (s:ℝ)⁻¹
  let u := b^c.p
  let v := b^c.q
  have bp : 0<b := inv_pos.mpr sp
  have bl : b<1 := inv_lt_one_of_one_lt₀ sr
  have p2 : 2≤c.p := by dsimp [Center.p,Center.depth]; omega
  have ul : u<1 := pow_lt_one₀ bp.le bl (by omega : c.p≠0)
  have vp : 0<v := pow_pos bp _
  have rr : c.R*(1-u)=c.x := div_mul_cancel₀ _ (by linarith)
  have ll : c.L*(1+v)=c.x := div_mul_cancel₀ _ (by linarith)
  have up : (s:ℝ)^c.p*u=1 := by dsimp [u,b]; rw [inv_pow,mul_inv_cancel₀ (pow_pos sp _).ne']
  have vq : (s:ℝ)^c.q*v=1 := by dsimp [v,b]; rw [inv_pow,mul_inv_cancel₀ (pow_pos sp _).ne']
  have h : u≤b^2 := pow_le_pow_of_le_one bp.le bl.le p2
  have small : b^2*((s:ℝ)+1)≤1 := by
    have s2 : (2:ℝ)≤s := by exact_mod_cast hs
    apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos sp)).mp; dsimp [b]; field_simp; nlinarith [sq_nonneg ((s:ℝ)-1)]
  have cx := (lt_div_iff₀ (by linarith : 0<(s:ℝ)+1)).mp c.inside.2
  have R1 : c.R<1 := by
    apply (div_lt_one (by linarith : 0<1-u)).mpr
    exact lt_of_mul_lt_mul_right (a:=(s:ℝ)+1) (by nlinarith only [small,cx,mul_le_mul_of_nonneg_right h (show 0≤(s:ℝ)+1 by linarith)]) (by linarith)
  refine ⟨R1,?_,?_,?_⟩
  · rw [show c.R-c.x=u*c.R by linarith only [rr],←mul_assoc,up,one_mul]
  · rw [show c.x-c.L=v*c.L by linarith only [ll],←mul_assoc,vq,one_mul]
  · change (s:ℝ)^c.q*(c.x-(c.x-v*c.R))=c.R
    rw [sub_sub_cancel,←mul_assoc,vq,one_mul]

private theorem shift_grid {s : ℤ} (c : Center s) (k : ℕ) (len : c.depth≤k) : GridAt s k c.x := by
  obtain ⟨a,ha⟩ := c.onGrid; change (s:ℝ)^c.depth*c.x=(a:ℝ) at ha
  refine ⟨s^(k-c.depth)*a,?_⟩; nth_rewrite 1 [show k=k-c.depth+c.depth by omega]; rw [pow_add,mul_assoc,ha]; push_cast; rfl

private theorem lift_mod {s : ℤ} {x z : ℝ} {k : ℕ} (pos : 0<k) (u : z∈Ico (0:ℝ) 1)
    (mod : ∃ a : ℤ, (-(s:ℝ))^k*x=(a:ℝ)+z) : (g s)^[k] x=z := by
  obtain ⟨a,ha⟩ := mod
  obtain ⟨b,hb⟩ := FirstDrop.iterate_lift s x k
  have U : (g s)^[k] x∈Ico (0:ℝ) 1 := by obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'; rw [Function.iterate_succ_apply']; exact ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
  have f₁ : Int.fract ((-(s:ℝ))^k*x)=z := Int.fract_eq_iff.mpr ⟨u.1,u.2,a,by linarith only [ha]⟩
  have f₂ : Int.fract ((-(s:ℝ))^k*x)=(g s)^[k] x := Int.fract_eq_iff.mpr ⟨U.1,U.2,b,by linarith only [hb]⟩
  exact f₂.symm.trans f₁

/-- Across the entire left half of the tuning window, not just the matching gap. -/
theorem odd_branch {s : ℤ} (hs : 2≤s) (c : Center s) {x : ℝ} (h : x∈Icc c.T c.x) :
    (g s)^[c.q] x=(s:ℝ)^c.q*(c.x-x) := by
  have sp : (0:ℝ)<s := by exact_mod_cast (show 0<s by omega)
  obtain ⟨R1,_,_,T⟩ := window_data hs c
  have len : c.depth≤c.q := by dsimp [Center.q]; omega
  have hp : 0<c.q := by dsimp [Center.q,Center.depth]; omega
  have par : Odd c.q := Nat.odd_iff.mpr (by dsimp [Center.q]; omega)
  obtain ⟨a,ha⟩ := shift_grid c c.q len
  apply lift_mod hp ⟨mul_nonneg (pow_nonneg sp.le _) (sub_nonneg.mpr h.2),?_⟩ ⟨-a,?_⟩
  · linarith only [mul_le_mul_of_nonneg_left (sub_le_sub_left h.1 c.x) (pow_nonneg sp.le c.q),T,R1]
  · rw [par.neg_pow,neg_mul,mul_sub,ha]; push_cast; ring

/-- Every point strictly within (L,R) has a positive iterate strictly below itself. -/
theorem gap_drop {s : ℤ} (hs : 2≤s) (c : Center s) {x : ℝ} (h : x∈Ioo c.L c.R) :
    ∃ k : ℕ, 0<k ∧ (g s)^[k] x<x := by
  have sr : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  have sp := zero_lt_one.trans sr
  obtain ⟨R1,R,L,_⟩ := window_data hs c
  by_cases left : x≤c.x
  · have E := odd_branch hs c ⟨(endpoint_order hs c).1.le.trans h.1.le,left⟩
    refine ⟨c.q,by dsimp [Center.q,Center.depth]; omega,?_⟩
    linarith only [E,L,h.1,mul_lt_mul_of_pos_left (sub_lt_sub_left h.1 c.x) (pow_pos sp c.q)]
  · have pos : 0<c.p := by dsimp [Center.p,Center.depth]; omega
    have par : Even c.p := Nat.even_iff.mpr (by dsimp [Center.p]; omega)
    obtain ⟨a,ha⟩ := shift_grid c c.p (by dsimp [Center.p]; omega)
    have P := pow_pos sp c.p
    have low : 0≤(s:ℝ)^c.p*(x-c.x) := mul_nonneg P.le (sub_nonneg.mpr (le_of_not_ge left))
    have upper := mul_lt_mul_of_pos_left (sub_lt_sub_right h.2 c.x) P
    have E : (g s)^[c.p] x=(s:ℝ)^c.p*(x-c.x) := by
      apply lift_mod pos ⟨low,by linarith only [upper,R,R1]⟩ ⟨a,?_⟩
      rw [par.neg_pow,mul_sub,ha]; ring
    refine ⟨c.p,pos,?_⟩
    have gt : 1<(s:ℝ)^c.p := one_lt_pow₀ sr pos.ne'
    nlinarith only [E,R,mul_pos (sub_pos.mpr gt) (sub_pos.mpr h.2)]

/-- No window interior can contain a strict one-step lower preimage of a fixed point.
    A point in its tuning collar would send that fixed point into the matching gap. -/
theorem fixed_preimage_untuned {s : ℤ} (hs : 2≤s) {x r : ℝ} (dom : x∈Icc 0 ((s:ℝ)/(s+1)))
    (xr : x<r) (step : g s x=r) (fix : g s r=r) : x∈UT s := by
  have it (k : ℕ) (pos : 0<k) : (g s)^[k] x=r := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'; rw [Function.iterate_succ_apply,step,Function.iterate_fixed fix]
  refine ⟨dom,?_⟩; intro c H
  have xl : x≤c.L := by
    apply le_of_not_gt; intro bad
    obtain ⟨k,kp,drop⟩ := gap_drop hs c ⟨bad,H.2⟩; rw [it k kp] at drop; exact (not_lt_of_ge xr.le) drop
  have w := endpoint_order hs c
  have E := odd_branch hs c ⟨H.1.le,xl.trans w.2.1.le⟩
  rw [it c.q (by dsimp [Center.q,Center.depth]; omega)] at E
  obtain ⟨_,_,L,T⟩ := window_data hs c
  have sp : (0:ℝ)<s := by exact_mod_cast (show 0<s by omega)
  have P := pow_pos sp c.q
  have lower : c.L<r := by
    rcases lt_or_eq_of_le xl with h|e
    · linarith only [E,L,mul_lt_mul_of_pos_left (sub_lt_sub_left h c.x) P]
    · linarith only [e,xr]
  have upper : r<c.R := by linarith only [E,T,mul_lt_mul_of_pos_left (sub_lt_sub_left H.1 c.x) P]
  obtain ⟨k,_,drop⟩ := gap_drop hs c ⟨lower,upper⟩
  rw [Function.iterate_fixed fix] at drop; exact (lt_irrefl r) drop

/-- Both hypotheses and conclusion of 4.30 on this entire bounded-imbalance family. -/
theorem fixed_family {s a k : ℤ} (ha : 1≤a) (ak : a<k) (ks : k≤s) :
    let x := ((a:ℝ)-(k:ℝ)/((s:ℝ)+1))/(s:ℝ)
    x∈UT s ∧ x<(s:ℝ)/(s+1) ∧ Accum s x := by
  let r := (k:ℝ)/((s:ℝ)+1)
  let x := ((a:ℝ)-r)/(s:ℝ)
  have hs : 2≤s := by omega
  have sp : (0:ℝ)<s := by exact_mod_cast (show 0<s by omega)
  have ap : (1:ℝ)≤a := by exact_mod_cast ha
  have kp : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have kr : (k:ℝ)≤s := by exact_mod_cast ks
  have gap : (a:ℝ)<k := by exact_mod_cast ak
  have rid : r*((s:ℝ)+1)=k := div_mul_cancel₀ _ (by linarith)
  have xid : x*(s:ℝ)=(a:ℝ)-r := div_mul_cancel₀ _ sp.ne'
  have r0 : 0<r := div_pos kp (by linarith)
  have r1 : r<1 := (div_lt_one (by linarith : 0<(s:ℝ)+1)).mpr (by linarith)
  have xr : x<r := (mul_lt_mul_iff_of_pos_right sp).mp (by linarith only [xid,rid,gap])
  have xp : 0<x := div_pos (by linarith only [ap,r1]) sp
  have rt : r≤(s:ℝ)/(s+1) := div_le_div_of_nonneg_right kr (by linarith)
  have step : g s x=r := Int.fract_eq_iff.mpr ⟨r0.le,r1,-a,by push_cast; linarith only [xid]⟩
  have fix : g s r=r := Int.fract_eq_iff.mpr ⟨r0.le,r1,-k,by push_cast; linarith only [rid]⟩
  exact ⟨fixed_preimage_untuned hs ⟨xp.le,(xr.trans_le rt).le⟩ xr step fix,xr.trans_le rt,FixedTail.fixed_preimage_accum ha ak ks⟩

#print axioms fixed_preimage_untuned
#print axioms fixed_family
end BCMP430.SurvivorWindow
