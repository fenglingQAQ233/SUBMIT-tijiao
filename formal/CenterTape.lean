import GridDensity

namespace BCMP430.CenterTape
open Adic Original UntunedTarget ClockTotal Tape Components

/-- Any positive fractional base-s grid point admits a canonical terminating tape,
    for composite s as well; zero digits are allowed before the final digit. -/
theorem represent {s : ℤ} (hs : 2≤s) (n : ℕ) {x : ℝ} (hx : 0<x ∧ x<1) (grid : GridAt s n x) :
    ∃ w : Word, Good s w ∧ val s w=x := by
  have sp : (0:ℝ)<s := by exact_mod_cast (show 0<s by omega)
  have step (u : ℝ) (hu : 0≤u ∧ u<1) :
      0≤⌊(s:ℝ)*u⌋ ∧ ⌊(s:ℝ)*u⌋<s ∧ consDigit s ⌊(s:ℝ)*u⌋ (Int.fract ((s:ℝ)*u))=u := by
    refine ⟨Int.floor_nonneg.mpr (mul_nonneg sp.le hu.1),Int.floor_lt.mpr ?_,?_⟩
    · simpa using mul_lt_mul_of_pos_left hu.2 sp
    · apply (div_eq_iff sp.ne').mpr; rw [Int.fract]; ring
  have peel (u : ℝ) (n : ℕ) (g : GridAt s (n+1) u) : GridAt s n (Int.fract ((s:ℝ)*u)) := by
    obtain ⟨b,hb⟩ := g
    refine ⟨b-s^n*⌊(s:ℝ)*u⌋,?_⟩
    rw [Int.fract,mul_sub,←mul_assoc,←pow_succ,hb]; push_cast; ring
  induction n using Nat.strong_induction_on generalizing x with
  | ind n ih =>
    let a := ⌊(s:ℝ)*x⌋
    let y := Int.fract ((s:ℝ)*x)
    obtain ⟨al,ar,ea⟩ := step x ⟨hx.1.le,hx.2⟩
    change consDigit s a y=x at ea
    have yr : 0≤y ∧ y<1 := ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
    by_cases ey : y=0
    · rw [ey] at ea
      refine ⟨.one a,⟨?_,ar⟩,ea⟩
      have hpos : 0<consDigit s a 0 := ea.symm ▸ hx.1
      change 0<((a:ℝ)+0)/(s:ℝ) at hpos
      exact_mod_cast (show (0:ℝ)<a by linarith only [(div_pos_iff_of_pos_right sp).mp hpos])
    have yp : 0<y := lt_of_le_of_ne yr.1 (Ne.symm ey)
    let b := ⌊(s:ℝ)*y⌋
    let z := Int.fract ((s:ℝ)*y)
    obtain ⟨bl,br,eb⟩ := step y yr
    change consDigit s b z=y at eb
    have zr : 0≤z ∧ z<1 := ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
    by_cases ez : z=0
    · rw [ez] at eb
      refine ⟨.two a b,⟨al,ar,?_,br⟩,?_⟩
      · have hpos : 0<consDigit s b 0 := eb.symm ▸ yp
        change 0<((b:ℝ)+0)/(s:ℝ) at hpos
        exact_mod_cast (show (0:ℝ)<b by linarith only [(div_pos_iff_of_pos_right sp).mp hpos])
      · change consDigit s a (consDigit s b 0)=x; rw [eb,ea]
    have zp : 0<z := lt_of_le_of_ne zr.1 (Ne.symm ez)
    have no_grid_zero (v : ℝ) (hv : 0<v ∧ v<1) (g : GridAt s 0 v) : False := by
      obtain ⟨b,hb⟩ := g; simp only [pow_zero,one_mul] at hb; rw [hb] at hv
      have h₁ : (0:ℤ)<b := by exact_mod_cast hv.1
      have h₂ : b<(1:ℤ) := by exact_mod_cast hv.2
      omega
    cases n with
    | zero => exact (no_grid_zero x hx grid).elim
    | succ n =>
      have gy := peel x n grid
      cases n with
      | zero => exact (no_grid_zero y ⟨yp,yr.2⟩ gy).elim
      | succ n =>
        obtain ⟨w,hw,ew⟩ := ih n (by omega) (x:=z) ⟨zp,zr.2⟩ (peel y n gy)
        exact ⟨.more a b w,⟨al,ar,bl,br,hw⟩,by change consDigit s a (consDigit s b (val s w))=x; rw [ew,eb,ea]⟩

private theorem center_clear {s : ℤ} (hs : 2≤s) (c : Center s) : Clear s c.x c.x := by
  have sp : (0:ℝ)<s := by exact_mod_cast (show 0<s by omega)
  have pos : 0<c.depth := Nat.zero_lt_succ _
  obtain ⟨a,ha⟩ := c.onGrid
  change (s:ℝ)^c.depth*c.x=(a:ℝ) at ha
  have ze : (g s)^[c.depth] c.x=0 := by
    obtain ⟨b,hb⟩ := FirstDrop.iterate_lift s c.x c.depth
    have u : (g s)^[c.depth] c.x ∈ Set.Ico (0:ℝ) 1 := by
      change (g s)^[c.depthPred+1] c.x ∈ _; rw [Function.iterate_succ_apply']; exact ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
    have integer : ∃ l : ℤ, (g s)^[c.depth] c.x=l := by
      rcases Nat.even_or_odd c.depth with h|h
      · rw [h.neg_pow] at hb; exact ⟨a-b,by push_cast; linarith only [ha,hb]⟩
      · rw [h.neg_pow,neg_mul] at hb; exact ⟨-a-b,by push_cast; linarith only [ha,hb]⟩
    obtain ⟨l,hl⟩ := integer; rw [hl] at u ⊢
    have l₁ : (0:ℤ)≤l := by exact_mod_cast u.1
    have l₂ : l<(1:ℤ) := by exact_mod_cast u.2
    exact_mod_cast (show l=0 by omega)
  intro j
  have h := c.avoid j
  have r : 0≤(g s)^[j+1] c.x := by rw [Function.iterate_succ_apply']; exact Int.fract_nonneg _
  by_cases z : (g s)^[j+1] c.x=0
  · exact Or.inl z
  right; apply lt_of_le_of_ne (le_of_not_gt (fun bad => h ⟨lt_of_le_of_ne r (Ne.symm z),bad⟩)); intro cycle
  have per (k : ℕ) : (g s)^[k*(j+1)] c.x=c.x := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.succ_mul,Function.iterate_add_apply,←cycle,ih]
  have large : c.depth≤c.depth*(j+1) := by simpa using Nat.mul_le_mul_left c.depth (Nat.zero_lt_succ j)
  have later : (g s)^[c.depth*(j+1)] c.x=0 := by
    conv_lhs => rw [show c.depth*(j+1)=c.depth*(j+1)-c.depth+c.depth by omega,Function.iterate_add_apply,ze]
    exact Function.iterate_fixed (by simp [g]) _
  rw [per] at later; exact c.inside.1.ne' later

/-- A `Center` from the original UT definition is in the actual matching fiber with
    the digit-formula delay, without assuming its finite CF word is dominant. -/
theorem center_fiber {s : ℤ} (hs : 2≤s) (c : Center s) :
    ∃ w : Word, Good s w ∧ val s w=c.x ∧ c.x∈fiber s (indexFromDigits s (padded w)) := by
  have sp : (0:ℝ)<s := by exact_mod_cast (show 0<s by omega)
  have xu : c.x<1 := c.inside.2.trans ((div_lt_one (by linarith : 0<(s:ℝ)+1)).mpr (by linarith))
  obtain ⟨w,hw,ew⟩ := represent hs c.depth ⟨c.inside.1,xu⟩ c.onGrid
  obtain ⟨i,j,lag,H⟩ := WordWindow.window_of_word hs w hw (ew.symm ▸ center_clear hs c)
  have h := Filter.Eventually.self_of_nhds H
  exact ⟨w,hw,ew,i,j,lag,ew ▸ h.1,ew ▸ h.2.1,ew ▸ h.2.2.1⟩

#print axioms represent
#print axioms center_fiber
end BCMP430.CenterTape
