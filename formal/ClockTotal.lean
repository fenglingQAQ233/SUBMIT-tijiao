import BranchClock

namespace BCMP430.ClockTotal
open Clock

/-- The terminal digit is separate because the first zero residue changes the gate. -/
inductive Word where
  | one (a : ℤ)
  | two (a b : ℤ)
  | more (a b : ℤ) (tail : Word)

def Good (s : ℤ) : Word → Prop
  | .one a => 0 < a ∧ a < s
  | .two a b => 0 ≤ a ∧ a < s ∧ 0 < b ∧ b < s
  | .more a b t => 0 ≤ a ∧ a < s ∧ 0 ≤ b ∧ b < s ∧ Good s t

def padded : Word → List ℤ
  | .one a => [a,0]
  | .two a b => [a,b]
  | .more a b t => a::b::padded t

structure State where
  right : ℤ
  left : ℤ
  gap : ℤ

def advance (s m b : ℤ) (p : State) : State :=
  ⟨height s m b p.right, height s m b p.left,
   p.gap+(steps s m b p.right:ℤ)-(steps s m b p.left:ℤ)⟩

def finish (s : ℤ) : Word → State → State
  | .one a, p => advance s 1 (s+1) (advance s 1 (s+1-a) p)
  | .two a b, p => advance s 1 (s+1) (advance s 1 (1+b) (advance s 0 (s-a) p))
  | .more a b t, p => finish s t (advance s 0 (1+b) (advance s 0 (s-a) p))

private theorem drift (s m b : ℤ) (p : State) :
    (advance s m b p).gap - ((advance s m b p).right-(advance s m b p).left) =
      p.gap-(p.right-p.left)+(s+1)*(p.right-p.left) := by
  dsimp [advance]; linarith only [clock_drift s m b p.right p.left]

private theorem heights {s m b v : ℤ} (hs : 2≤s) (hv : 1≤v) (hb : b≤s+m) :
    height s m b v=m := by
  have h := mul_le_mul_of_nonneg_left hv (show 0≤s by omega)
  rw [mul_one] at h
  exact max_eq_left (by omega)

private theorem ground {s m b : ℤ} (hb : m≤b) : height s m b 0=b := by simp [height,max_eq_right hb]

private theorem two_weight (s a b : ℤ) (t : List ℤ) :
    weight s (a::b::t)=2*(s-1-a-b)+weight s t := by simp only [weight]; ring

def halfWeight (s : ℤ) : Word → ℤ
  | .one a => s-1-a
  | .two a b => s-1-a-b
  | .more a b t => s-1-a-b+halfWeight s t

private theorem padded_weight (s : ℤ) (w : Word) : weight s (padded w)=2*halfWeight s w := by
  induction w with
  | one a => simp [padded,weight,halfWeight]; ring
  | two a b => simp [padded,weight,halfWeight]; ring
  | more a b t ih => simp only [padded,two_weight,ih,halfWeight]; ring

/-- With an arbitrary incoming clock gap, terminal even and odd words give the same
    padded-weight formula. This theorem is about the computed clock, not minimality. -/
private theorem core {s : ℤ} (hs : 2≤s) (w : Word) (hw : Good s w) (p : State)
    (hp : p.right=0) (hv : 1≤p.left) :
    (finish s w p).right=1 ∧ (finish s w p).left=1 ∧
    (finish s w p).gap = p.gap-s*p.left + (s+1)*(halfWeight s w + 1) := by
  induction w generalizing p with
  | one a =>
    obtain ⟨ha,hb⟩ := hw
    let u := advance s 1 (s+1-a) p
    have ur : u.right=s+1-a := by change height _ _ _ p.right = _; rw [hp]; exact ground (by omega)
    have ul : u.left=1 := heights hs hv (by omega)
    let v := advance s 1 (s+1) u
    have vr : v.right=1 := heights hs (by rw [ur]; omega) (by omega)
    have vl : v.left=1 := heights hs (by rw [ul]) (by omega)
    have h₁ := drift s 1 (s+1-a) p
    have h₂ := drift s 1 (s+1) u
    change u.gap - (u.right - u.left) = _ at h₁
    change v.gap - (v.right - v.left) = _ at h₂
    rw [ur,ul,hp] at h₁; rw [vr,vl,ur,ul] at h₂
    refine ⟨vr,vl,?_⟩
    change v.gap = p.gap-s*p.left+(s+1)*((s-1-a)+1)
    linarith only [h₁,h₂]
  | two a b =>
    obtain ⟨ha,ha',hb,hb'⟩ := hw
    let u := advance s 0 (s-a) p
    have ur : u.right=s-a := by change height _ _ _ p.right = _; rw [hp]; exact ground (by omega)
    have ul : u.left=0 := heights hs hv (by omega)
    let v := advance s 1 (1+b) u
    have vr : v.right=1 := heights hs (by rw [ur]; omega) (by omega)
    have vl : v.left=1+b := by change height _ _ _ u.left = _; rw [ul]; exact ground (by omega)
    let z := advance s 1 (s+1) v
    have zr : z.right=1 := heights hs (by rw [vr]) (by omega)
    have zl : z.left=1 := heights hs (by rw [vl]; omega) (by omega)
    have h₁ := drift s 0 (s-a) p
    have h₂ := drift s 1 (1+b) u
    have h₃ := drift s 1 (s+1) v
    change u.gap - (u.right - u.left) = _ at h₁; change v.gap - (v.right - v.left) = _ at h₂; change z.gap - (z.right - z.left) = _ at h₃
    rw [ur,ul,hp] at h₁; rw [vr,vl,ur,ul] at h₂; rw [zr,zl,vr,vl] at h₃
    refine ⟨zr,zl,?_⟩
    change z.gap = p.gap-s*p.left+(s+1)*((s-1-a-b)+1)
    linarith only [h₁,h₂,h₃]
  | more a b t ih =>
    obtain ⟨ha,ha',hb,hb',ht⟩ := hw
    let u := advance s 0 (s-a) p
    have ur : u.right=s-a := by change height _ _ _ p.right = _; rw [hp]; exact ground (by omega)
    have ul : u.left=0 := heights hs hv (by omega)
    let v := advance s 0 (1+b) u
    have vr : v.right=0 := heights hs (by rw [ur]; omega) (by omega)
    have vl : v.left=1+b := by change height _ _ _ u.left = _; rw [ul]; exact ground (by omega)
    have h₁ := drift s 0 (s-a) p
    have h₂ := drift s 0 (1+b) u
    change u.gap - (u.right - u.left) = _ at h₁; change v.gap - (v.right - v.left) = _ at h₂
    rw [ur,ul,hp] at h₁; rw [vr,vl,ur,ul] at h₂
    obtain ⟨A,B,C⟩ := ih ht v vr (by rw [vl]; omega)
    rw [vl] at C
    refine ⟨A,B,?_⟩
    change (finish s t v).gap = p.gap-s*p.left+(s+1)*(s-1-a-b+halfWeight s t+1)
    linarith only [h₁,h₂,C]

theorem summed_clock {s : ℤ} (hs : 2≤s) (w : Word) (hw : Good s w) :
    let z := finish s w ⟨0,1,-1⟩
    z.right=1 ∧ z.left=1 ∧ z.gap=indexFromDigits s (padded w) := by
  obtain ⟨hr,hl,hg⟩ := core hs w hw ⟨0,1,-1⟩ rfl (by decide)
  refine ⟨hr,hl,?_⟩
  rw [hg]; dsimp only; unfold indexFromDigits; rw [padded_weight]
  have h : (s+1)*(2*halfWeight s w) = (s+1)*halfWeight s w * 2 := by ring
  rw [h,Int.mul_ediv_cancel _ (by decide : (2:ℤ)≠0)]; ring

#print axioms summed_clock
end BCMP430.ClockTotal
