import DeepCoverage

namespace BCMP430.FixedTail
open Original ClockTotal Tape UntunedTarget Components Adic Set

/-- The repeated ordinary digit pair has zero weight, but the outer pair and the
    odd terminal digit leave a nonzero total weight. -/
def tail (s k : ℤ) : ℕ → Word
  | 0 => .one (k-1)
  | n+1 => .more (k-1) (s-k) (tail s k n)
def word (s a k : ℤ) (n : ℕ) := Word.more (a-1) (s-k) (tail s k n)
private theorem good {s a k : ℤ} (ha : 1≤a) (ak : a<k) (ks : k≤s) (n : ℕ) : Good s (word s a k n) := by
  have H : Good s (tail s k n) := by
    induction n with
    | zero => exact ⟨by omega,by omega⟩
    | succ n ih => exact ⟨by omega,by omega,by omega,by omega,ih⟩
  exact ⟨by omega,by omega,by omega,by omega,H⟩

private theorem lag (s a k : ℤ) (n : ℕ) : indexFromDigits s (padded (word s a k n))=(s+1)*(s-a) := by
  have W : weight s (padded (tail s k n))=2*(s-k) := by
    induction n with
    | zero => simp [tail,padded,weight]; ring
    | succ n ih => simp only [tail,padded,weight,ih]; ring
  unfold indexFromDigits; simp only [word,padded,weight,W]
  have id : (s+1)*(s-1-2*(a-1)+(s-1-2*(s-k)+2*(s-k)))=(s+1)*(s-a)*2 := by ring
  rw [id,Int.mul_ediv_cancel _ (by decide : (2:ℤ)≠0)]

private theorem pair_mul {s : ℤ} (hn : (s:ℝ)≠0) (a b : ℤ) (v : ℝ) :
    (s:ℝ)^2*consDigit s a (consDigit s b v)=(s:ℝ)*a+b+v := by unfold consDigit; field_simp; ring

private theorem numerator {s k : ℤ} (hs : 2≤s) (n : ℕ) : ∃ p : ℤ,
    (s:ℝ)^(2*n+1)*val s (tail s k n)=s*p+(k-1:ℤ) := by
  have hn : (s:ℝ)≠0 := by exact_mod_cast (show s≠0 by omega)
  induction n with
  | zero => exact ⟨0,by simp [tail,val,consDigit]; field_simp⟩
  | succ n ih =>
    obtain ⟨p,hp⟩ := ih
    refine ⟨s^(2*n)*(s*(k-1)+(s-k))+p,?_⟩
    rw [show 2*(n+1)+1=(2*n+1)+2 by omega,pow_add,mul_assoc]
    change (s:ℝ)^(2*n+1)*((s:ℝ)^2*consDigit s (k-1) (consDigit s (s-k) _))=_
    rw [pair_mul hn]; push_cast at hp ⊢; rw [mul_add,hp,pow_succ]; ring

private theorem grid {s a k : ℤ} (hs : 2≤s) (ak : a<k) (ha : 1≤a) (ks : k≤s) (n : ℕ) :
    GridAt s (2*n+3) (val s (word s a k n)) ∧ ¬GridAt s (2*n+2) (val s (word s a k n)) := by
  have hn : (s:ℝ)≠0 := by exact_mod_cast (show s≠0 by omega)
  obtain ⟨p,hp⟩ := numerator (k:=k) hs n
  let v := s^(2*n)*(s*(a-1)+(s-k))+p
  have num : (s:ℝ)^(2*n+3)*val s (word s a k n)=((s*v+(k-1):ℤ):ℝ) := by
    rw [show 2*n+3=(2*n+1)+2 by omega,pow_add,mul_assoc]
    change (s:ℝ)^(2*n+1)*((s:ℝ)^2*consDigit s (a-1) (consDigit s (s-k) _))=_
    rw [pair_mul hn,mul_add,hp]; dsimp [v]; push_cast; rw [pow_succ]; ring
  refine ⟨⟨_,num⟩,?_⟩
  rintro ⟨q,hq⟩
  rw [show 2*n+3=(2*n+2)+1 by omega,pow_succ',mul_assoc,hq] at num
  have eq : s*q=s*v+(k-1) := by exact_mod_cast num
  have dvd : s ∣ k-1 := ⟨q-v,by rw [mul_sub]; linarith only [eq]⟩
  exact (not_le_of_gt (show k-1<s by omega)) (Int.le_of_dvd (show 0<k-1 by omega) dvd)

private theorem pair_orbit {s k a : ℤ} (hs : 2≤s) (hk : 2≤k) (ks : k≤s)
    {u : ℝ} (u0 : 0<u) (u1 : u<1) :
    let z := consDigit s (a-1) (consDigit s (s-k) u)
    g s z=((k:ℝ)-u)/s ∧ g s (((k:ℝ)-u)/s)=u := by
  have sp : (0:ℝ)<s := by exact_mod_cast (show 0<s by omega)
  have kl : (2:ℝ)≤k := by exact_mod_cast hk
  have kr : (k:ℝ)≤s := by exact_mod_cast ks
  have V : 0<((k:ℝ)-u)/s := div_pos (by linarith) sp
  have V1 : ((k:ℝ)-u)/s<1 := (div_lt_one sp).mpr (by linarith)
  constructor
  · apply Int.fract_eq_iff.mpr; refine ⟨V.le,V1,-a,?_⟩; unfold consDigit; push_cast; field_simp; ring
  · apply Int.fract_eq_iff.mpr; refine ⟨u0.le,u1,-k,?_⟩; push_cast; field_simp; ring

/-- All strict one-step preimages below the fixed point k/(s+1), 1≤a<k≤s,
    are approached by genuine maximal intervals of the *same* positive index.
    The accumulation conclusion does not require assuming that x is untuned. -/
theorem fixed_preimage_accum {s a k : ℤ} (ha : 1≤a) (ak : a<k) (ks : k≤s) :
    let r := (k:ℝ)/((s:ℝ)+1)
    let x := ((a:ℝ)-r)/(s:ℝ)
    Accum s x := by
  let r := (k:ℝ)/((s:ℝ)+1)
  let x := ((a:ℝ)-r)/(s:ℝ)
  let t := ((k:ℝ)-1)/(s:ℝ)
  let u := fun n : ℕ => val s (tail s k n)
  let z := fun n : ℕ => val s (word s a k n)
  have hs : 2≤s := by omega
  have sp : (0:ℝ)<s := by exact_mod_cast (show 0<s by omega)
  have kk : (2:ℝ)≤k := by exact_mod_cast (show 2≤k by omega)
  have sl : (2:ℝ)≤s := by exact_mod_cast hs
  have kr : (k:ℝ)≤s := by exact_mod_cast ks
  have gap : (a:ℝ)+1≤k := by exact_mod_cast (show a+1≤k by omega)
  have rid : r*((s:ℝ)+1)=k := div_mul_cancel₀ _ (by linarith)
  have xid : x*(s:ℝ)=(a:ℝ)-r := div_mul_cancel₀ _ sp.ne'
  have tid : t*(s:ℝ)=(k:ℝ)-1 := div_mul_cancel₀ _ sp.ne'
  have r0 : 0<r := div_pos (by linarith) (by linarith)
  have r1 : r<1 := (div_lt_one (by linarith : 0<(s:ℝ)+1)).mpr (by linarith)
  have tp : 0<t := div_pos (by linarith) sp
  have tr : t<r := (mul_lt_mul_iff_of_pos_right sp).mp (by nlinarith only [tid,rid,r1])
  have xt : x<t := (mul_lt_mul_iff_of_pos_right sp).mp (by linarith only [xid,tid,r0,gap])
  have top : r≤(s:ℝ)/(s+1) := div_le_div_of_nonneg_right kr (by linarith)
  let b := ((s:ℝ)^2)⁻¹
  have ss : (1:ℝ)<(s:ℝ)^2 := by nlinarith [sq_nonneg ((s:ℝ)-2)]
  have bp : 0<b := inv_pos.mpr (zero_lt_one.trans ss)
  have bl : b<1 := inv_lt_one_of_one_lt₀ ss
  have bm : b*(s:ℝ)^2=1 := inv_mul_cancel₀ (zero_lt_one.trans ss).ne'
  have ud (n : ℕ) : u n-r=b^n*(t-r) := by
    induction n with
    | zero => simp [u,tail,val,consDigit,t]
    | succ n ih =>
      have h := pair_mul sp.ne' (k-1) (s-k) (u n)
      change (s:ℝ)^2*u (n+1)=_ at h
      push_cast at h
      have fix : (s:ℝ)^2*r=(s:ℝ)*(k-1)+(s-k)+r := by nlinarith only [rid,congrArg (fun v : ℝ => ((s:ℝ)-1)*v) rid]
      have recurrence : u (n+1)-r=(u n-r)/((s:ℝ)^2) := (eq_div_iff (pow_ne_zero _ sp.ne')).mpr (by linarith only [h,fix])
      rw [recurrence,ih,pow_succ]; dsimp only [b]; ring
  have bounds (n : ℕ) : t≤u n ∧ u n<r := by
    have one : b^n≤1 := pow_le_one₀ bp.le bl.le
    have sign : 0<b^n := pow_pos bp _
    constructor <;> nlinarith only [ud n,tr,mul_nonneg (sub_nonneg.mpr one) (sub_nonneg.mpr tr.le),mul_pos sign (sub_pos.mpr tr)]
  have zd (n : ℕ) : z n-x=b^(n+1)*(t-r) := by
    have h := pair_mul sp.ne' (a-1) (s-k) (u n)
    change (s:ℝ)^2*z n=_ at h; push_cast at h
    have fix : (s:ℝ)^2*x=(s:ℝ)*(a-1)+(s-k)+r := by nlinarith only [rid,xid,congrArg (fun v : ℝ => (s:ℝ)*v) xid]
    have recurrence : z n-x=(u n-r)/((s:ℝ)^2) := (eq_div_iff (pow_ne_zero _ sp.ne')).mpr (by linarith only [h,fix])
    rw [recurrence,ud,pow_succ]; dsimp only [b]; ring
  have middle (n : ℕ) : t≤((k:ℝ)-u n)/s := (le_div_iff₀ sp).mpr (by linarith only [tid,(bounds n).2,r1])
  have survive (n j : ℕ) : (g s)^[j] (u n)=0 ∨ t≤(g s)^[j] (u n) := by
    induction n generalizing j with
    | zero =>
      cases j with
      | zero => exact Or.inr (bounds 0).1
      | succ j =>
        have zero : g s (u 0)=0 := by
          have base : u 0=t := by simp [u,tail,val,consDigit,t]
          rw [base]; change Int.fract (-(s:ℝ)*(((k:ℝ)-1)/s))=0
          have id : -(s:ℝ)*(((k:ℝ)-1)/s)=((1-k:ℤ):ℝ) := by push_cast; field_simp; ring
          rw [id,Int.fract_intCast]
        left; rw [Function.iterate_succ_apply,zero]; exact Function.iterate_fixed (by simp [g]) _
    | succ n ih =>
      obtain ⟨o,o'⟩ := pair_orbit (a:=k) hs (by omega) ks (tp.trans_le (bounds n).1) ((bounds n).2.trans r1)
      change g s (u (n+1))=_ at o
      cases j with
      | zero => exact Or.inr (bounds _).1
      | succ j => cases j with
        | zero => right; change t≤g s (u (n+1)); rw [o]; exact middle n
        | succ j => rw [Function.iterate_succ_apply,Function.iterate_succ_apply,o,o']; exact ih j
  change Accum s x
  apply DeepCoverage.deep_accum hs
  intro ε he N
  obtain ⟨K,hK⟩ := exists_pow_lt_of_lt_one he bl
  let n := max K N
  have sign : z n<x := by nlinarith only [zd n,mul_pos (pow_pos bp (n+1)) (sub_pos.mpr tr)]
  have unit := Tape.in_unit hs _ (good ha ak ks n)
  have gd := grid (s:=s) (a:=a) (k:=k) hs ak ha ks n
  have clean : Tape.Clear s (z n) (z n) := by
    obtain ⟨o,o'⟩ := pair_orbit (a:=a) hs (by omega) ks (tp.trans_le (bounds n).1) ((bounds n).2.trans r1)
    change g s (z n)=_ at o
    intro j; rw [Function.iterate_succ_apply,o]; cases j with
    | zero => right; exact (sign.trans xt).trans_le (middle _)
    | succ j => rw [Function.iterate_succ_apply,o']; rcases survive n j with h|h
                · exact Or.inl h
                · exact Or.inr ((sign.trans xt).trans_le h)
  let c : Center s := ⟨z n,2*n+2,⟨unit.1,sign.trans (xt.trans (tr.trans_le top))⟩,gd.1,gd.2,fun j bad => (clean j).elim (fun h => bad.1.ne' h) (fun h => (not_lt_of_ge h.le) bad.2)⟩
  obtain ⟨i,j,L,H⟩ := WordWindow.window_of_word hs _ (good ha ak ks n) clean
  have h0 := Filter.Eventually.self_of_nhds H
  refine ⟨c,(s+1)*(s-a),?_,by change N<2*n+2+1; have l : N≤n := le_max_right ..; omega,Int.mul_ne_zero (by omega) (by omega),i,j,L.trans (lag ..),h0.1,h0.2.1,h0.2.2.1⟩
  change dist (z n) x<ε; rw [Real.dist_eq,abs_of_neg (sub_neg.mpr sign)]
  have pk := (pow_le_pow_of_le_one bp.le bl.le (show K≤n+1 by have l : K≤n := le_max_left ..; omega)).trans_lt hK
  nlinarith only [zd n,pk,mul_nonneg (pow_nonneg bp.le (n+1)) (show 0≤1-(r-t) by linarith only [r1,tp])]

#print axioms fixed_preimage_accum
end BCMP430.FixedTail
