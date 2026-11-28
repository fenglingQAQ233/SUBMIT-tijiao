import OriginalReturn
import DigitPairs

namespace BCMP430.Clock
open Original

/-- Lowest integer translate of r strictly above the discontinuity. -/
noncomputable def gate (γ r : ℝ) : ℤ := ⌊γ-r⌋+1

theorem above_iff (γ r : ℝ) (h : ℤ) : γ < r+(h:ℝ) ↔ gate γ r ≤ h := by
  unfold gate
  rw [show ⌊γ-r⌋+1 ≤ h ↔ ⌊γ-r⌋ < h by omega, Int.floor_lt]
  constructor <;> intro a <;> linarith

def height (s m b h : ℤ) : ℤ := max m (b-s*h)
def steps (s m b h : ℤ) : ℕ := (height s m b h-(b-s*h)).toNat+1

private theorem steps_cast (s m b h : ℤ) : (steps s m b h : ℤ) = 1+height s m b h-b+s*h := by
  have hu : b-s*h ≤ height s m b h := le_max_right ..
  unfold steps; rw [Nat.cast_add,Int.toNat_of_nonneg (by omega)]; omega

/-- After the initial decreasing branch, count exactly the translations up to the next
    decreasing-branch input. Even a hit at the discontinuity still uses the translation. -/
theorem translations_to_gate (s γ r : ℝ) (v : ℤ) :
    let H := max (gate γ r) v
    let N := (H-v).toNat
    (Q s γ)^[N] (r+(v:ℝ)) = r+(H:ℝ) ∧ γ < r+(H:ℝ) ∧
      ∀ j<N, (Q s γ)^[j] (r+(v:ℝ)) ≤ γ := by
  let H := max (gate γ r) v
  let N := (H-v).toNat
  have hV : v ≤ H := le_max_right ..
  have hN : (N:ℤ) = H-v := Int.toNat_of_nonneg (by omega)
  have below (j : ℕ) (hj : j<N) : r+((v+(j:ℤ):ℤ):ℝ) ≤ γ := by
    apply le_of_not_gt
    intro hg
    have hgate := (above_iff γ r (v+(j:ℤ))).mp hg
    have h' : (j:ℤ) < N := by exact_mod_cast hj
    by_cases h : gate γ r ≤ v
    · have he : H=v := max_eq_right h
      omega
    · have he : H=gate γ r := max_eq_left (le_of_not_ge h)
      omega
  have it (j : ℕ) (hj : j≤N) : (Q s γ)^[j] (r+(v:ℝ)) = r+((v+(j:ℤ):ℤ):ℝ) := by
    induction j with
    | zero => simp
    | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),Q,ite_eq_left (below j (by omega))]; push_cast; ring
  change (Q s γ)^[N] (r+(v:ℝ)) = r+(H:ℝ) ∧ γ < r+(H:ℝ) ∧ _
  refine ⟨?_,(above_iff ..).mpr (le_max_left ..),?_⟩
  · rw [it N (by omega),show v+(N:ℤ)=H by omega]
  · intro j hj; rw [it j (by omega)]; exact below j hj

noncomputable def level (s : ℤ) (r : ℝ) := ⌊1+(s:ℝ)*(1-r)⌋

private theorem decrease_value (s h : ℤ) (r : ℝ) :
    1+(s:ℝ)*(1-(r+(h:ℝ))) = g s r + ((level s r-s*h:ℤ):ℝ) := by
  have hf : Int.fract (1+(s:ℝ)*(1-r)) = g s r := by
    apply Int.fract_eq_fract.mpr; exact ⟨1+s,by push_cast; ring⟩
  rw [←hf,Int.fract,level]; push_cast; ring

/-- Actual Q-iterate, its minimal waiting time, and the terminal branch test. -/
theorem next_decrease {s h : ℤ} {γ r : ℝ} (hB : γ < r+(h:ℝ)) :
    let u := g s r
    let m := gate γ u
    let b := level s r
    let T := steps s m b h
    (Q s γ)^[T] (r+(h:ℝ)) = u+(height s m b h:ℝ) ∧
      γ < u+(height s m b h:ℝ) ∧ ∀ j, 0<j → j<T → (Q s γ)^[j] (r+(h:ℝ)) ≤ γ := by
  let u := g s r
  let b := level s r
  let v := b-s*h
  let m := gate γ u
  let N := (height s m b h-v).toNat
  have H := translations_to_gate s γ u v
  have first : Q s γ (r+(h:ℝ)) = u+(v:ℝ) := by rw [Q,ite_eq_right (not_le.mpr hB)]; exact decrease_value ..
  change (Q s γ)^[N+1] (r+(h:ℝ)) = _ ∧ _ ∧ ∀ j, 0<j → j<N+1 → _
  refine ⟨?_,H.2.1,?_⟩
  · rw [Function.iterate_succ_apply,first]; exact H.1
  · intro j hj hlt
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
    rw [Function.iterate_succ_apply,first]
    apply H.2.2 k
    change k < N
    exact Nat.lt_of_succ_lt_succ hlt

theorem gates {γ r : ℝ} (hγ : 0 ≤ γ) (hγ' : γ < 1) (hr : γ < r) (hr' : r < 1) :
    gate γ r = 0 ∧ gate γ 0 = 1 := by
  have a : gate γ r ≤ 0 := (above_iff γ r 0).mp (by simpa using hr)
  have b : ¬gate γ r ≤ -1 := fun h => by have hh := (above_iff γ r (-1)).mpr h; push_cast at hh; linarith
  have c : gate γ 0 ≤ 1 := (above_iff γ 0 1).mp (by simpa using hγ')
  have d : ¬gate γ 0 ≤ 0 := fun h => by have hh := (above_iff γ 0 0).mpr h; simp at hh; linarith
  omega

/-- Drift of (right time - left time) minus the height difference in one common B-step. -/
theorem clock_drift (s m b u v : ℤ) :
    (steps s m b u:ℤ) - (steps s m b v:ℤ) - (height s m b u-height s m b v)
     + (u-v) = (s+1)*(u-v) := by rw [steps_cast,steps_cast]; ring

#print axioms next_decrease
#print axioms gates
#print axioms clock_drift
end BCMP430.Clock
