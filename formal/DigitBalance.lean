import DigitGuard

namespace BCMP430.DigitBalance
open Original UntunedTarget Adic ClockTotal Tape Components

noncomputable def remainder (s : ℤ) (x : ℝ) := Int.fract ((s:ℝ)*x)
noncomputable def balance (s : ℤ) (x : ℝ) : ℕ → ℤ
  | 0 => 0
  | n+1 => s-1-2*⌊(s:ℝ)*x⌋ + balance s (remainder s x) n

private theorem rec_grid (s : ℤ) (x : ℝ) (n : ℕ) :
    GridAt s n (remainder s x) ↔ GridAt s (n+1) x := by
  have eq : (s:ℝ)^n*remainder s x=(s:ℝ)^(n+1)*x-((s^n*⌊(s:ℝ)*x⌋:ℤ):ℝ) := by
    unfold remainder Int.fract; push_cast; ring
  constructor
  · rintro ⟨k,h⟩; refine ⟨k+s^n*⌊(s:ℝ)*x⌋,?_⟩; rw [eq] at h; push_cast at h ⊢; linarith only [h]
  · rintro ⟨k,h⟩; exact ⟨k-s^n*⌊(s:ℝ)*x⌋,by rw [eq,h]; push_cast; ring⟩

private theorem peel {s : ℤ} (hs : 2≤s) {x : ℝ} (h : 0≤x ∧ x<1) :
    0≤⌊(s:ℝ)*x⌋ ∧ ⌊(s:ℝ)*x⌋<s ∧ consDigit s ⌊(s:ℝ)*x⌋ (remainder s x)=x := by
  have sp : (0:ℝ)<s := by exact_mod_cast (show 0<s by omega)
  exact ⟨Int.floor_nonneg.mpr (mul_nonneg sp.le h.1),Int.floor_lt.mpr (by simpa using mul_lt_mul_of_pos_left h.2 sp),
    (div_eq_iff sp.ne').mpr (by unfold remainder Int.fract; ring)⟩

private theorem zero_grid {s : ℤ} {x : ℝ} (hx : 0≤x ∧ x<1) : GridAt s 0 x ↔ x=0 := by
  constructor
  · rintro ⟨a,ha⟩; simp only [pow_zero,one_mul] at ha; rw [ha] at hx ⊢
    have l : (0:ℤ)≤a := by exact_mod_cast hx.1
    have r : a<(1:ℤ) := by exact_mod_cast hx.2
    exact_mod_cast (show a=0 by omega)
  · rintro rfl; exact ⟨0,by simp⟩

/-- Last odd digit gets exactly one padding zero. Depth here is least s-grid depth. -/
theorem tape_weight {s : ℤ} (hs : 2≤s) (n : ℕ) {x : ℝ} (hx : 0<x ∧ x<1)
    (grid : GridAt s (n+1) x) (off : ¬GridAt s n x) :
    ∃ w : Word, Good s w ∧ val s w=x ∧ weight s (padded w)=balance s x (n+1) + (if (n+1)%2=0 then 0 else s-1) := by
  have sp : (0:ℝ)<s := by exact_mod_cast (show 0<s by omega)
  induction n using Nat.strong_induction_on generalizing x with
  | ind n ih =>
    let a := ⌊(s:ℝ)*x⌋
    let y := remainder s x
    have yr : 0≤y ∧ y<1 := ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
    obtain ⟨al,ar,ea⟩ := peel hs ⟨hx.1.le,hx.2⟩
    change consDigit s a y=x at ea
    cases n with
    | zero =>
      have ey : y=0 := (zero_grid (s:=s) yr).mp ((rec_grid s x 0).mpr grid)
      rw [ey] at ea
      have hpos : 0<consDigit s a 0 := ea.symm ▸ hx.1
      have ap : 0<a := by exact_mod_cast (show (0:ℝ)<a by linarith only [(div_pos_iff_of_pos_right sp).mp hpos])
      exact ⟨.one a,⟨ap,ar⟩,ea,by simp [padded,weight,balance,a]⟩
    | succ n =>
      have gy := (rec_grid s x (n+1)).mpr grid
      have oy : ¬GridAt s n y := fun g => off ((rec_grid s x n).mp g)
      have yp : 0<y := lt_of_le_of_ne yr.1 (by intro h; exact oy ⟨0,by rw [←h]; simp⟩)
      let b := ⌊(s:ℝ)*y⌋
      let z := remainder s y
      have zr : 0≤z ∧ z<1 := ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
      obtain ⟨bl,br,eb⟩ := peel hs yr
      change consDigit s b z=y at eb
      cases n with
      | zero =>
        have ez : z=0 := (zero_grid (s:=s) zr).mp ((rec_grid s y 0).mpr gy)
        rw [ez] at eb
        have hpos : 0<consDigit s b 0 := eb.symm ▸ yp
        have bp : 0<b := by exact_mod_cast (show (0:ℝ)<b by linarith only [(div_pos_iff_of_pos_right sp).mp hpos])
        exact ⟨.two a b,⟨al,ar,bp,br⟩,by change consDigit s a (consDigit s b 0)=x; rw [eb,ea],by simp [padded,weight,balance,a,b,y]⟩
      | succ n =>
        have gz := (rec_grid s y (n+1)).mpr gy
        have oz : ¬GridAt s n z := fun g => oy ((rec_grid s y n).mp g)
        have zp : 0<z := lt_of_le_of_ne zr.1 (by intro h; exact oz ⟨0,by rw [←h]; simp⟩)
        obtain ⟨w,hw,ew,weightW⟩ := ih n (by omega) ⟨zp,zr.2⟩ gz oz
        refine ⟨.more a b w,⟨al,ar,bl,br,hw⟩,by change consDigit s a (consDigit s b (val s w))=x; rw [ew,eb,ea],?_⟩
        have par : (n+1+1+1)%2=(n+1)%2 := by omega
        simp only [padded,weight,weightW,par]
        change _ = (s-1-2*a + (s-1-2*b+balance s z (n+1)))+_
        omega

private theorem abs_balance {s : ℤ} (hs : 2≤s) (n : ℕ) {x : ℝ} (h : 0≤x ∧ x<1) :
    |balance s x n| ≤ (s-1)*(n:ℤ) := by
  induction n generalizing x with
  | zero => simp [balance]
  | succ n ih =>
    have a := peel hs h
    have b := ih (x:=remainder s x) ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
    rw [abs_le] at b ⊢; rw [balance, Nat.cast_succ,mul_add,mul_one]; constructor <;> omega

private theorem shifted_floor (s : ℤ) (x : ℝ) (k : ℕ) :
    ⌊(s:ℝ)^k*remainder s x⌋ = ⌊(s:ℝ)^(k+1)*x⌋-s^k*⌊(s:ℝ)*x⌋ := by
  have eq : (s:ℝ)^k*remainder s x=(s:ℝ)^(k+1)*x+((-s^k*⌊(s:ℝ)*x⌋:ℤ):ℝ) := by unfold remainder Int.fract; push_cast; ring
  rw [eq,Int.floor_add_intCast]; ring

/-- Disagreement confined to at most C terminal digits bounds the weight error. -/
theorem compare {s : ℤ} (hs : 2≤s) {x y : ℝ} (hx : 0≤x ∧ x<1) (hy : 0≤y ∧ y<1) (j C : ℕ)
    (heads : ∀ i≤j, ⌊(s:ℝ)^i*x⌋=⌊(s:ℝ)^i*y⌋) :
    |balance s x (j+C)-balance s y (j+C)| ≤ 2*(s-1)*(C:ℤ) := by
  induction j generalizing x y with
  | zero =>
    simp only [Nat.zero_add]; have l := abs_balance hs C hx; have r := abs_balance hs C hy
    rw [abs_le] at l r ⊢; constructor <;> nlinarith only [l.1,l.2,r.1,r.2]
  | succ j ih =>
    have eq := heads 1 (by omega); simp only [pow_one] at eq
    have H := ih (x:=remainder s x) (y:=remainder s y) ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩ ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩ (by
      intro i hi; rw [shifted_floor,shifted_floor,eq,heads (i+1) (by omega)])
    rw [Nat.succ_add,balance,balance,eq,add_sub_add_left_eq_sub]; exact H

#print axioms tape_weight
#print axioms compare
end BCMP430.DigitBalance
