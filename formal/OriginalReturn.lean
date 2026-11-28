import RealPrefix

namespace BCMP430.Original

noncomputable def Q (s γ x : ℝ) : ℝ := if x ≤ γ then x+1 else 1+s*(1-x)
noncomputable def g (s : ℤ) (x : ℝ) := Int.fract (-(s:ℝ)*x)

def FirstReturn (f : ℝ → ℝ) (x : ℝ) (t : ℕ) (v : ℝ) : Prop :=
  0<t ∧ f^[t] x=v ∧ v ∈ Set.Ico (0:ℝ) 1 ∧ ∀ j, 0<j → j<t → f^[j] x ∉ Set.Ico (0:ℝ) 1

private theorem ascend {s γ y : ℝ} {n : ℕ} (hγ : 0 ≤ γ) (hstart : y+(n:ℝ) ∈ Set.Ico (0:ℝ) 1)
    (j : ℕ) (hj : j ≤ n) : (Q s γ)^[j] y = y + j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hstep : (j:ℝ)+1 ≤ n := by exact_mod_cast hj
    have hneg : y+(j:ℝ) < 0 := by linarith [hstart.2]
    rw [Function.iterate_succ_apply', ih (by omega), Q, ite_eq_left (le_trans hneg.le hγ), Nat.cast_succ]; ring

private theorem finish {s γ x y : ℝ} (hγ : 0 ≤ γ) (hy : y<1)
    (h1 : 1 ≤ Q s γ x) (h2 : (Q s γ)^[2] x=y) :
    FirstReturn (Q s γ) x ((-⌊y⌋).toNat+2) (Int.fract y) := by
  let n := (-⌊y⌋).toNat
  have hfl : ⌊y⌋ < 1 := Int.floor_lt.mpr (by simpa using hy)
  have hnz : (n:ℤ) = -⌊y⌋ := Int.toNat_of_nonneg (by omega)
  have hnr : (n:ℝ) = -(⌊y⌋:ℝ) := by exact_mod_cast hnz
  have hsum : y+(n:ℝ)=Int.fract y := by rw [hnr,Int.fract]; ring
  have hmem : Int.fract y ∈ Set.Ico (0:ℝ) 1 := ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
  have hm : y+(n:ℝ) ∈ Set.Ico (0:ℝ) 1 := hsum ▸ hmem
  change FirstReturn (Q s γ) x (n+2) (Int.fract y)
  refine ⟨by omega,?_,hmem,?_⟩
  · rw [Function.iterate_add_apply,h2,ascend hγ hm n (by omega),hsum]
  · intro j hj hlt
    by_cases he : j=1
    · subst j; simp only [Function.iterate_one]; intro h; linarith [h.2]
    · let i := j-2
      have hi : i<n := by dsimp [i]; omega
      have hj' : j=i+2 := by dsimp [i]; omega
      rw [hj',Function.iterate_add_apply,h2,ascend hγ hm i hi.le]
      have hgap : (i:ℝ)+1 ≤ n := by exact_mod_cast hi
      intro h; linarith [hm.2,h.1]

private theorem g_twice (s : ℤ) (x : ℝ) : g s (g s x) = Int.fract ((s:ℝ)^2*x) := by
  unfold g
  apply Int.fract_eq_fract.mpr
  refine ⟨s * ⌊-(s:ℝ)*x⌋,?_⟩
  rw [Int.fract,Int.cast_mul]; ring

/-- BCMP Lemma 4.1: the left branch includes x = γ. -/
theorem first_return_left {s : ℤ} {γ x : ℝ} (hs : 2≤s) (hγ0 : 0≤γ) (hγ1 : γ<1)
    (hx : 0<x) (h : x≤γ) :
    FirstReturn (Q s γ) x ((-⌊1-(s:ℝ)*x⌋).toNat+2) (g s x) := by
  have hs' : (0:ℝ)<s := by exact_mod_cast (show 0<s by omega)
  have h1 : Q s γ x = x+1 := ite_eq_left h
  have h2 : (Q s γ)^[2] x = 1-(s:ℝ)*x := by
    change Q s γ (Q s γ x) = _
    rw [h1,Q,ite_eq_right (by linarith : ¬ x+1 ≤ γ)]; ring
  have hv : Int.fract (1-(s:ℝ)*x) = g s x := by unfold g; apply Int.fract_eq_fract.mpr; exact ⟨1,by push_cast; ring⟩
  rw [← hv]; apply finish hγ0 _ _ h2
  · linarith [mul_pos hs' hx]
  · rw [h1]; linarith

/-- The return time also covers exact integer hits, since the section is [0,1). -/
theorem first_return_right {s : ℤ} {γ x : ℝ} (hs : 2≤s) (hγ0 : 0≤γ)
    (h : γ<x) (hx : x<1) :
    FirstReturn (Q s γ) x ((-⌊1-(s:ℝ)^2*(1-x)⌋).toNat+2) (g s (g s x)) := by
  have hs' : (0:ℝ)<s := by exact_mod_cast (show 0<s by omega)
  have hp : 0<(s:ℝ)*(1-x) := mul_pos hs' (by linarith)
  have h1 : Q s γ x = 1+(s:ℝ)*(1-x) := ite_eq_right (not_le.mpr h)
  have h2 : (Q s γ)^[2] x = 1-(s:ℝ)^2*(1-x) := by
    change Q s γ (Q s γ x) = _
    rw [h1,Q,ite_eq_right (by linarith : ¬1+(s:ℝ)*(1-x)≤γ)]; ring
  have hv : Int.fract (1-(s:ℝ)^2*(1-x)) = g s (g s x) := by
    rw [g_twice]; apply Int.fract_eq_fract.mpr; exact ⟨1-s^2,by push_cast; ring⟩
  rw [← hv]; apply finish hγ0 _ _ h2
  · linarith [mul_pos (sq_pos_of_pos hs') (show 0<1-x by linarith)]
  · rw [h1]; linarith

#print axioms first_return_left
#print axioms first_return_right
end BCMP430.Original
