import GridProbes

namespace BCMP430.DigitGuard
open Set Original UntunedTarget

/-- At every level j the scaled target stays away from both neighboring integers.
    Odd iterates use the complementary fractional part, not the same remainder. -/
theorem margin {s : ℤ} (hs : 2≤s) {x : ℝ} (hu : x∈UT s) (hp : 0<x)
    (ht : x<(s:ℝ)/(s+1)) (j : ℕ) :
    x/(s:ℝ) ≤ Int.fract ((s:ℝ)^j*x) ∧ Int.fract ((s:ℝ)^j*x) ≤ 1-x/(s:ℝ) := by
  have sr : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  have sp : (0:ℝ)<s := zero_lt_one.trans sr
  have sur := DropWindow.ut_survives hs hu hp ht
  let r := (g s)^[j] x
  have rl : x≤r := sur j
  have ru : r<1 := by cases j with
    | zero => exact ht.trans ((div_lt_one (by linarith : 0<(s:ℝ)+1)).mpr (by linarith))
    | succ j => change (g s)^[j+1] x<1; rw [Function.iterate_succ_apply']; exact Int.fract_lt_one _
  have step : g s r=Int.fract ((s:ℝ)*(1-r)) := by
    apply Int.fract_eq_fract.mpr; exact ⟨-s,by push_cast; ring⟩
  have high : x≤(s:ℝ)*(1-r) := by
    have nex := sur (j+1); rw [Function.iterate_succ_apply'] at nex; change x≤g s r at nex
    rw [step] at nex
    have non := Int.floor_nonneg.mpr (mul_nonneg sp.le (sub_nonneg.mpr ru.le))
    have F : (0:ℝ)≤(⌊(s:ℝ)*(1-r)⌋:ℝ) := by exact_mod_cast non
    unfold Int.fract at nex; linarith only [nex,F]
  have guard : x/(s:ℝ) ≤ 1-r := (div_le_iff₀ sp).mpr (by linarith only [high])
  have weaker : x/(s:ℝ)≤x := (div_le_iff₀ sp).mpr (by nlinarith [mul_nonneg hp.le (sub_nonneg.mpr sr.le)])
  obtain ⟨a,ha⟩ := FirstDrop.iterate_lift s x j
  change (-(s:ℝ))^j*x=(a:ℝ)+r at ha
  rcases Nat.even_or_odd j with par|par
  · rw [par.neg_pow] at ha
    have id : Int.fract ((s:ℝ)^j*x)=r := Int.fract_eq_iff.mpr ⟨hp.le.trans rl,ru,a,by linarith only [ha]⟩
    rw [id]; exact ⟨weaker.trans rl,by linarith only [guard]⟩
  · rw [par.neg_pow,neg_mul] at ha
    have id : Int.fract ((s:ℝ)^j*x)=1-r := Int.fract_eq_iff.mpr ⟨by linarith,by linarith only [rl,hp],-a-1,by push_cast; linarith only [ha]⟩
    rw [id]; exact ⟨guard,by linarith only [weaker,rl]⟩

/-- A distance of at most two final mesh widths can change only the last C digits,
    with C independent of the level, for a positive untuned target. -/
theorem prefix_lock {s : ℤ} (hs : 2≤s) {x : ℝ} (hu : x∈UT s) (hp : 0<x)
    (ht : x<(s:ℝ)/(s+1)) {C e : ℕ} (small : 2*(s:ℝ)⁻¹^C < x/(s:ℝ)) {y : ℝ}
    (near : |y-x|≤2*(s:ℝ)⁻¹^e) (j : ℕ) (le : j+C≤e) :
    ⌊(s:ℝ)^j*y⌋=⌊(s:ℝ)^j*x⌋ := by
  let S := (s:ℝ)^j
  let b := (s:ℝ)⁻¹
  have sr : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  have sp : (0:ℝ)<s := zero_lt_one.trans sr
  have bp : 0<b := inv_pos.mpr sp
  have s0 : 0<S := pow_pos sp _
  have pw : b^e ≤ b^(j+C) := pow_le_pow_of_le_one bp.le (inv_lt_one_of_one_lt₀ sr).le le
  have prod : S*b^j=1 := by dsimp [S,b]; rw [inv_pow,mul_inv_cancel₀ s0.ne']
  have mov : |S*y-S*x| < x/(s:ℝ) := by
    rw [←mul_sub,abs_mul,abs_of_pos s0]
    have v := mul_le_mul_of_nonneg_left (near.trans (by linarith only [pw] : 2*(s:ℝ)⁻¹^e≤2*b^(j+C))) s0.le
    rw [pow_add] at v
    calc _ ≤ S*(2*(b^j*b^C)) := v
         _ = 2*b^C := by calc
            _ = 2*b^C*(S*b^j) := by ring
            _ = _ := by rw [prod,mul_one]
         _ < _ := small
  obtain ⟨l,r⟩ := margin hs hu hp ht j
  change x/(s:ℝ) ≤ S*x-(⌊S*x⌋:ℝ) at l
  change S*x-(⌊S*x⌋:ℝ) ≤ 1-x/(s:ℝ) at r
  exact Int.floor_eq_iff.mpr ⟨by linarith only [(abs_lt.mp mov).1,l],by linarith only [(abs_lt.mp mov).2,r]⟩

#print axioms margin
#print axioms prefix_lock
end BCMP430.DigitGuard
