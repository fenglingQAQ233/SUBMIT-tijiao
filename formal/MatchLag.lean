import OriginalReturn

namespace BCMP430.MatchLag
open Original

/-- Position with the cumulative number of uses of the decreasing branch. -/
abbrev Mark := ℕ × ℝ
noncomputable def advance (s γ : ℝ) (z : Mark) : Mark :=
  (if z.2 ≤ γ then z.1 else z.1+1, Q s γ z.2)

def Before (v w : Mark) := v.1 < w.1 ∨ (v.1=w.1 ∧ v.2<w.2)

private theorem forward (s γ : ℝ) (v : Mark) : Before v (advance s γ v) := by
  by_cases h : v.2 ≤ γ
  · right; simp [advance,Q,h]
  · left; simp [advance,h]

private theorem chain {u v w : Mark} (h : Before u v) (k : Before v w) : Before u w := by
  rcases h with h | ⟨h,h'⟩ <;> rcases k with k | ⟨k,k'⟩
  · exact Or.inl (h.trans k)
  · exact Or.inl (k ▸ h)
  · exact Or.inl (h.symm ▸ k)
  · exact Or.inr ⟨h.trans k,h'.trans k'⟩

private theorem strict_time (s γ : ℝ) (z : Mark) {m n : ℕ} (hm : m<n) :
    Before ((advance s γ)^[m] z) ((advance s γ)^[n] z) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hm) with he|hl
    · subst m; exact forward ..
    · exact chain (ih hl) (forward ..)

theorem injective_time (s γ : ℝ) (z : Mark) : Function.Injective (fun n : ℕ => (advance s γ)^[n] z) := by
  intro m n he
  change (advance s γ)^[m] z = (advance s γ)^[n] z at he
  rcases lt_trichotomy m n with h|h|h
  · have hh := strict_time s γ z h; rw [he] at hh; simp [Before] at hh
  · exact h
  · have hh := strict_time s γ z h; rw [he] at hh; simp [Before] at hh

/-- Two state-and-count meetings of the same two forward trajectories have exactly
    the same signed delay; neither meeting is assumed to be minimal. -/
theorem lag_unique (s γ : ℝ) (u v : Mark) {i j k l : ℕ}
    (first : (advance s γ)^[i] u = (advance s γ)^[j] v)
    (second : (advance s γ)^[k] u = (advance s γ)^[l] v) :
    (i:ℤ)-j = (k:ℤ)-l := by
  let f := advance s γ
  have hh : f^[l+i] u = f^[j+k] u := by
    calc
      _ = f^[l] (f^[j] v) := by rw [Function.iterate_add_apply,first]
      _ = f^[j] (f^[l] v) := by rw [←Function.iterate_add_apply, Nat.add_comm l j, Function.iterate_add_apply]
      _ = _ := by rw [←second, Function.iterate_add_apply]
  have he := injective_time s γ u hh
  omega

#print axioms lag_unique
end BCMP430.MatchLag
