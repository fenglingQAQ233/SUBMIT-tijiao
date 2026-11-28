import MatchWitness

namespace BCMP430.Adic
open Original Germ MatchLag Witness

/-- A base-s grid level; it does not use reduced rational denominators. -/
def GridAt (s : ℤ) (n : ℕ) (x : ℝ) : Prop := ∃ c : ℤ, (s:ℝ)^n*x=c

private theorem q_closed {s : ℤ} {n : ℕ} {x γ : ℝ} (h : GridAt s n x) :
    GridAt s n (Q s γ x) := by
  obtain ⟨c,hc⟩ := h
  unfold Q
  split
  · refine ⟨c+s^n,?_⟩
    push_cast; rw [mul_add,hc,mul_one]
  · refine ⟨s^n*(1+s)-s*c,?_⟩
    push_cast; rw [←hc]; ring

private theorem path_closed {s : ℤ} {n : ℕ} {γ : ℝ} {r : Bool} {k : ℕ}
    (h : GridAt s n (path s γ r k).2) : GridAt s n (path s γ r (k+1)).2 := by
  change GridAt s n ((advance s γ)^[(k+1)] (seed s γ r)).2
  rw [Function.iterate_succ_apply']; exact q_closed h

/-- After its first decreasing step each critical side stays on a grid strictly
    coarser than γ. The initial left image γ+1 is handled before this step. -/
theorem avoids {s : ℤ} {γ : ℝ} {n : ℕ} (onFine : GridAt s (n+1) γ)
    (offCoarse : ¬GridAt s n γ) (r : Bool) (k : ℕ) : (path s γ r k).2 ≠ γ := by
  obtain ⟨c,hc⟩ := onFine
  have mulc : (s:ℝ)^n*((s:ℝ)*γ)=c := by rw [←mul_assoc,←pow_succ,hc]
  have right : ∀ j, GridAt s n (path s γ true j).2 := by
    intro j; induction j with
    | zero =>
      refine ⟨s^n*(1+s)-c,?_⟩
      change (s:ℝ)^n*(1+(s:ℝ)*(1-γ)) = _
      push_cast; rw [←mulc]; ring
    | succ j ih => exact path_closed ih
  have left : ∀ j, GridAt s n (path s γ false (j+1)).2 := by
    intro j; induction j with
    | zero =>
      refine ⟨s^n-c,?_⟩
      change (s:ℝ)^n*Q s γ (γ+1) = _
      rw [Q,ite_eq_right (by linarith : ¬γ+1≤γ)]
      push_cast; rw [←mulc]; ring
    | succ j ih => exact path_closed ih
  cases r with
  | true => intro eq; exact offCoarse (eq ▸ right k)
  | false =>
    cases k with
    | zero => change γ+1 ≠ γ; linarith
    | succ k => intro eq; exact offCoarse (eq ▸ left k)

theorem canonical_avoids {s c : ℤ} {γ : ℝ} {n : ℕ}
    (num : (s:ℝ)^(n+1)*γ=c) (canonical : ¬s ∣ c) (r : Bool) (k : ℕ) :
    (path s γ r k).2 ≠ γ := by
  apply avoids (n:=n) ⟨c,num⟩ _ r k
  rintro ⟨z,hz⟩
  apply canonical
  refine ⟨z,?_⟩
  have eq : (c:ℝ) = (s:ℝ)*(z:ℝ) := by rw [←hz,←num,pow_succ]; ring
  exact_mod_cast eq

theorem canonical_meets_iff {s c : ℤ} {γ : ℝ} {n : ℕ} (hs : 2≤s)
    (num : (s:ℝ)^(n+1)*γ=c) (canonical : ¬s ∣ c) (i j : ℕ) :
    Meets s γ i j ↔ path s γ true i = path s γ false j := by
  apply meets_iff (by exact_mod_cast (show 1<s by omega))
  · exact fun k _ => canonical_avoids num canonical true k
  · exact fun k _ => canonical_avoids num canonical false k

#print axioms avoids
#print axioms canonical_meets_iff
end BCMP430.Adic
