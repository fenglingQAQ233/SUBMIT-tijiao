import AdicAvoid

namespace BCMP430.Stability
open Original Germ MatchLag Witness Filter
open scoped Topology

/-- Transport a marked endpoint as the critical parameter moves by t. -/
def move (s t : ℝ) (z : Mark) : Mark := (z.1,z.2+(-s)^z.1*t)

theorem finite_itinerary (s γ : ℝ) (r : Bool) (n : ℕ)
    (ha : ∀ k < n, (path s γ r k).2 ≠ γ) :
    ∀ᶠ η in 𝓝 γ, path s η r n = move s (η-γ) (path s γ r n) ∧
      ∀ k < n, (path s η r k).2 ≠ η := by
  induction n with
  | zero =>
    filter_upwards with η
    constructor
    · cases r <;> apply Prod.ext <;> simp [move,path,seed] <;> ring
    · omega
  | succ n ih =>
    have prev := ih (fun k hk => ha k (by omega))
    let z := path s γ r n
    let y := fun η : ℝ => z.2+(-s)^z.1*(η-γ)
    have cont : Continuous y := by dsimp [y]; fun_prop
    have ht₀ : Tendsto y (𝓝 γ) (𝓝 (y γ)) := cont.continuousAt
    have ht : Tendsto y (𝓝 γ) (𝓝 z.2) := by simpa [y] using ht₀
    have hstep (η : ℝ) : path s η r (n+1) = advance s η (path s η r n) := Function.iterate_succ_apply' ..
    have cmp : ∀ᶠ η in 𝓝 γ, (if z.2 < γ then y η < η else η < y η) := by
      rcases lt_or_gt_of_ne (ha n (by omega)) with h|h
      · change z.2 < γ at h
        simpa only [ite_eq_left h, id_eq] using ht.eventually_lt (tendsto_id (x:=𝓝 γ)) h
      · change γ < z.2 at h
        simpa only [ite_eq_right (not_lt_of_gt h), id_eq] using (tendsto_id (x:=𝓝 γ)).eventually_lt ht h
    filter_upwards [prev,cmp] with η hprev hc
    have posη : (path s η r n).2 = y η := congrArg Prod.snd hprev.1
    have sep : y η ≠ η := by
      split at hc
      · exact ne_of_lt hc
      · exact ne_of_gt hc
    constructor
    · rw [hstep η,hstep γ,hprev.1]
      change advance s η (move s (η-γ) z) = move s (η-γ) (advance s γ z)
      rcases lt_or_gt_of_ne (ha n (by omega)) with h|h
      · change z.2 < γ at h
        rw [ite_eq_left h] at hc
        change z.2+(-s)^z.1*(η-γ) < η at hc
        apply Prod.ext <;> simp [advance,move,Q,hc.le,h.le]; ring
      · change γ < z.2 at h
        rw [ite_eq_right (not_lt_of_gt h)] at hc
        change η < z.2+(-s)^z.1*(η-γ) at hc
        apply Prod.ext <;> simp [advance,move,Q,not_le_of_gt hc,not_le_of_gt h,pow_succ]; ring
    · intro k hk
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hk) with he|hl
      · subst k; rw [posη]; exact sep
      · exact hprev.2 k hl

/-- The same witness exponents match on an open parameter neighborhood, with no
    earlier visits to the moving discontinuity in either prematching segment. -/
theorem witness_neighborhood {s γ : ℝ} (hs : 1<s) {i j : ℕ}
    (ha : ∀ k < i, (path s γ true k).2 ≠ γ) (hb : ∀ k < j, (path s γ false k).2 ≠ γ)
    (meet : Meets s γ i j) :
    ∀ᶠ η in 𝓝 γ, Meets s η i j ∧ (∀ k < i, (path s η true k).2 ≠ η) ∧
      (∀ k < j, (path s η false k).2 ≠ η) := by
  have e := (meets_iff hs ha hb).mp meet
  filter_upwards [finite_itinerary s γ true i ha,finite_itinerary s γ false j hb] with η hr hl
  exact ⟨(meets_iff hs hr.2 hl.2).mpr (hr.1.trans ((congrArg (move s (η-γ)) e).trans hl.1.symm)),hr.2,hl.2⟩

#print axioms witness_neighborhood
end BCMP430.Stability
