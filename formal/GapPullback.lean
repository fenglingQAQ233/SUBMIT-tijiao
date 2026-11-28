import OrbitSplice

namespace BCMP430.GapPullback
open Original UntunedTarget Set

def m {s : ℤ} (c : Center s) (right : Bool) : ℕ := if right then c.p else c.q

noncomputable def y {s : ℤ} (c : Center s) (right : Bool) (v : ℝ) : ℝ :=
  if right then c.x + (s:ℝ)⁻¹^c.p * v else c.x - (s:ℝ)⁻¹^c.q * v

private theorem length_bounds {s : ℤ} (c : Center s) (right : Bool) :
    c.depth ≤ m c right ∧ m c right ≤ c.depth + 1 := by
  cases right <;> simp [m, Center.p, Center.q] <;> omega

private theorem signed_grid {s : ℤ} (c : Center s) {k : ℕ} (hk : c.depth ≤ k) :
    ∃ a : ℤ, (-(s:ℝ))^k * c.x = (a:ℝ) := by
  obtain ⟨a, ha⟩ := c.onGrid
  change (s:ℝ)^c.depth * c.x = (a:ℝ) at ha
  have grid : ∃ b : ℤ, (-(s:ℝ))^c.depth * c.x = (b:ℝ) := by
    rcases Nat.even_or_odd c.depth with e | o
    · exact ⟨a, by rw [e.neg_pow, ha]⟩
    · exact ⟨-a, by rw [o.neg_pow, neg_mul, ha, Int.cast_neg]⟩
  obtain ⟨b, hb⟩ := grid
  refine ⟨(-s)^(k-c.depth) * b, ?_⟩
  calc
    _ = (-(s:ℝ))^(k-c.depth) * ((-(s:ℝ))^c.depth * c.x) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
    _ = _ := by simp [hb]

/-- At positive times the actual iterate is the unique lift residue in `[0,1)`. -/
private theorem residue {s : ℤ} {x z : ℝ} {k : ℕ} (hk : 0 < k) (hz : z ∈ Ico (0:ℝ) 1)
    {a : ℤ} (ha : (-(s:ℝ))^k * x = (a:ℝ) + z) : (g s)^[k] x = z := by
  obtain ⟨b, hb⟩ := FirstDrop.iterate_lift s x k
  have u : (g s)^[k] x ∈ Ico (0:ℝ) 1 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [Function.iterate_succ_apply']; exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have lift : Int.fract ((-(s:ℝ))^k*x) = (g s)^[k] x :=
    Int.fract_eq_iff.mpr ⟨u.1, u.2, b, by linarith only [hb]⟩
  exact lift.symm.trans (Int.fract_eq_iff.mpr ⟨hz.1, hz.2, a, by linarith only [ha]⟩)

private theorem displacement {s : ℤ} (hs : 2 ≤ s) (c : Center s) (right : Bool) (v : ℝ) :
    (-(s:ℝ))^(m c right) * (y c right v - c.x) = v := by
  have sp : (0:ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have cancel (n : ℕ) : (s:ℝ)^n * (s:ℝ)⁻¹^n = 1 := by
    rw [inv_pow, mul_inv_cancel₀ (pow_pos sp n).ne']
  cases right with
  | false =>
    have o : Odd c.q := Nat.odd_iff.mpr (by dsimp [Center.q]; omega)
    change (-(s:ℝ))^c.q * (c.x - (s:ℝ)⁻¹^c.q*v - c.x) = v
    rw [o.neg_pow]
    calc _ = ((s:ℝ)^c.q * (s:ℝ)⁻¹^c.q)*v := by ring
         _ = v := by rw [cancel,one_mul]
  | true =>
    have e : Even c.p := Nat.even_iff.mpr (by dsimp [Center.p]; omega)
    change (-(s:ℝ))^c.p * (c.x + (s:ℝ)⁻¹^c.p*v - c.x) = v
    rw [e.neg_pow]
    calc _ = ((s:ℝ)^c.p * (s:ℝ)⁻¹^c.p)*v := by ring
         _ = v := by rw [cancel,one_mul]

/-- The longer branch has one additional residue before it joins the orbit of `v`. -/
theorem pull_iterates {s : ℤ} (hs : 2 ≤ s) (c : Center s) (right : Bool) {v : ℝ}
    (hv : 0 < v) (ht : v ≤ (s:ℝ)/(s+1)) :
    (g s)^[m c right] (y c right v) = v ∧
    (m c right = c.depth + 1 →
      (g s)^[c.depth] (y c right v) = 1 - v/(s:ℝ) ∧ v ≤ 1 - v/(s:ℝ)) := by
  have sp : (0:ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have den : 0 < (s:ℝ)+1 := by linarith
  have v1 := ht.trans_lt ((div_lt_one den).mpr (by linarith))
  have guard : v ≤ 1 - v/(s:ℝ) := by
    apply (mul_le_mul_iff_of_pos_right sp).mp
    linarith only [(le_div_iff₀ den).mp ht, div_mul_cancel₀ v sp.ne']
  have dp : 0 < c.depth := Nat.zero_lt_succ _
  have dm := (length_bounds c right).1
  have D := displacement hs c right v
  constructor
  · obtain ⟨a, ha⟩ := signed_grid c dm
    apply residue (dp.trans_le dm) ⟨hv.le, v1⟩ (a := a)
    linarith only [D, ha]
  · intro long
    rw [long, pow_succ] at D
    have before : (-(s:ℝ))^c.depth * (y c right v - c.x) = -v/(s:ℝ) := by
      apply (eq_div_iff sp.ne').mpr
      linarith only [D]
    obtain ⟨a, ha⟩ := signed_grid c (le_refl c.depth)
    refine ⟨residue dp ⟨hv.le.trans guard, by linarith only [div_pos hv sp]⟩ (a := a-1) ?_, guard⟩
    rw [mul_sub,ha,neg_div] at before
    push_cast
    linarith only [before]

/-- Survival before the grid depth and survival on the tail suffice for the pullback. -/
theorem pull {s : ℤ} (hs : 2 ≤ s) (c : Center s) (right : Bool) {v : ℝ}
    (hv : 0 < v) (ht : v ≤ (s:ℝ)/(s+1))
    (surv : ∀ i : ℕ, v ≤ (g s)^[i] v)
    (hit : ∃ N : ℕ, (g s)^[N] v = (s:ℝ)/(s+1))
    (hy : y c right v ≤ v)
    (early : ∀ j : ℕ, 0 < j → j < c.depth → y c right v ≤ (g s)^[j] (y c right v)) :
    (∀ j : ℕ, y c right v ≤ (g s)^[j] (y c right v)) ∧
    ∃ N : ℕ, (g s)^[N] (y c right v) = (s:ℝ)/(s+1) := by
  obtain ⟨join, before⟩ := pull_iterates hs c right hv ht
  have tail_eq (i : ℕ) : (g s)^[i + m c right] (y c right v) = (g s)^[i] v := by
    rw [Function.iterate_add_apply, join]
  constructor
  · intro j
    by_cases later : m c right ≤ j
    · simpa only [Nat.sub_add_cancel later, ← tail_eq (j - m c right)] using
        hy.trans (surv (j - m c right))
    by_cases zero : j = 0
    · subst j; exact le_rfl
    by_cases small : j < c.depth
    · exact early j (by omega) small
    have upper := (length_bounds c right).2
    obtain ⟨atDepth, ge⟩ := before (by omega)
    rw [show j = c.depth by omega, atDepth]
    exact hy.trans ge
  · obtain ⟨N, hN⟩ := hit
    exact ⟨N + m c right, (tail_eq N).trans hN⟩

#print axioms pull_iterates
#print axioms pull
end BCMP430.GapPullback
