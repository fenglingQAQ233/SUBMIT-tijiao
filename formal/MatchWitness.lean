import SideGerm

namespace BCMP430.Witness
open Original Germ MatchLag Filter
open scoped Topology

/-- n counts iterations after the first, side-specific branch. -/
def Trace (s γ : ℝ) (r : Bool) (n : ℕ) (v d : ℝ) :=
    Tendsto (fun t : ℝ => (Q s γ)^[n+1] (γ+t)) (side r) (𝓝 v) ∧
    Tendsto (fun t : ℝ => ((Q s γ)^[n+1] (γ+t)-v)/t) (side r) (𝓝 d)

def Meets (s γ : ℝ) (i j : ℕ) := ∃ v d : ℝ, Trace s γ true i v d ∧ Trace s γ false j v d

private theorem trace_unique {s γ v d : ℝ} {r : Bool} {n : ℕ}
    (avoid : ∀ k<n, (path s γ r k).2 ≠ γ) (tr : Trace s γ r n v d) :
    v=(path s γ r n).2 ∧ d=(-s)^(path s γ r n).1 := by
  have : (side r).NeBot := by cases r <;> dsimp [side] <;> infer_instance
  have h := value_and_slope s γ r n avoid
  have hv := tendsto_nhds_unique tr.1 h.1
  subst v
  exact ⟨rfl,tendsto_nhds_unique tr.2 h.2⟩

theorem meets_iff {s γ : ℝ} (hs : 1<s) {i j : ℕ}
    (ha : ∀ k < i, (path s γ true k).2 ≠ γ) (hb : ∀ k < j, (path s γ false k).2 ≠ γ) :
    Meets s γ i j ↔ path s γ true i=path s γ false j := by
  constructor
  · rintro ⟨v,d,h₁,h₂⟩
    obtain ⟨p₁,d₁⟩ := trace_unique ha h₁
    obtain ⟨p₂,d₂⟩ := trace_unique hb h₂
    have eqSlope := congrArg abs (d₁.symm.trans d₂)
    simp only [abs_pow,abs_neg,abs_of_pos (lt_trans zero_lt_one hs)] at eqSlope
    exact Prod.ext ((pow_right_strictMono₀ hs).injective eqSlope) (p₁.symm.trans p₂)
  · intro h
    refine ⟨(path s γ true i).2,(-s)^(path s γ true i).1,value_and_slope _ _ _ _ ha,?_⟩
    rw [h]; exact value_and_slope _ _ _ _ hb

theorem lag_of_meetings {s γ : ℝ} (hs : 1<s) {i j k l : ℕ}
    (ha : ∀ u<max i k, (path s γ true u).2 ≠ γ) (hb : ∀ u<max j l, (path s γ false u).2 ≠ γ)
    (a : Meets s γ i j) (b : Meets s γ k l) :
    ((i+1:ℕ):ℤ)-(j+1:ℕ) = ((k+1:ℕ):ℤ)-(l+1:ℕ) := by
  have h₁ := (meets_iff hs (fun u hu => ha u (lt_of_lt_of_le hu (le_max_left i k)))
    (fun u hu => hb u (lt_of_lt_of_le hu (le_max_left j l)))).mp a
  have h₂ := (meets_iff hs (fun u hu => ha u (lt_of_lt_of_le hu (le_max_right i k)))
    (fun u hu => hb u (lt_of_lt_of_le hu (le_max_right j l)))).mp b
  have h := lag_unique s γ (seed s γ true) (seed s γ false) h₁ h₂
  omega

#print axioms meets_iff
#print axioms lag_of_meetings
end BCMP430.Witness
