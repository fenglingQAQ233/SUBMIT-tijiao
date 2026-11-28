import RealClock

namespace BCMP430.WordWindow
open Original ClockTotal Tape RealClock Adic Witness Germ Stability Filter
open scoped Topology

private theorem grid_digit {s a : ℤ} (hs : 2≤s) {x : ℝ} {k : ℕ} (h : GridAt s k x) :
    GridAt s (k+1) (consDigit s a x) := by
  obtain ⟨c,hc⟩ := h
  refine ⟨s^k*a+c,?_⟩
  have hn : (s:ℝ) ≠ 0 := by exact_mod_cast (show s≠0 by omega)
  have mul1 : (s:ℝ)*consDigit s a x = (a:ℝ)+x := by unfold consDigit; field_simp
  rw [pow_succ,mul_assoc,mul1,mul_add,hc]; push_cast; ring

private theorem grid_exists {s : ℤ} (hs : 2≤s) (w : Word) : ∃ k : ℕ, GridAt s k (val s w) := by
  have gz : GridAt s 0 0 := ⟨0,by simp⟩
  induction w with
  | one a => exact ⟨_,grid_digit (a:=a) hs gz⟩
  | two a b => exact ⟨_,grid_digit (a:=a) hs (grid_digit (a:=b) hs gz)⟩
  | more a b t ih => obtain ⟨k,hk⟩ := ih; exact ⟨_,grid_digit (a:=a) hs (grid_digit (a:=b) hs hk)⟩

/-- Choose the least grid depth rather than assuming reduced denominators are powers of s. -/
theorem word_avoid {s : ℤ} (hs : 2≤s) (w : Word) (hw : Good s w) (r : Bool) (j : ℕ) :
    (path s (val s w) r j).2 ≠ val s w := by
  classical
  have hex := grid_exists hs w
  let k := Nat.find hex
  have hk : GridAt s k (val s w) := Nat.find_spec hex
  have hn : k≠0 := by
    intro he
    rw [he] at hk
    obtain ⟨c,hc⟩ := hk
    simp only [pow_zero,one_mul] at hc
    have h := in_unit hs w hw
    rw [hc] at h
    have l : (0:ℤ)<c := by exact_mod_cast h.1
    have u : c<(1:ℤ) := by exact_mod_cast h.2
    omega
  have eqn : k-1+1=k := by omega
  apply avoids (n:=k-1) (eqn ▸ hk) _ r j
  exact Nat.find_min hex (by change k-1<k; omega)

/-- A word meeting the orbit test gives a genuine open neighborhood of one-sided
    matching with its computed index; every no-later witness has the same delay. -/
theorem window_of_word {s : ℤ} (hs : 2≤s) (w : Word) (hw : Good s w)
    (clear : Clear s (val s w) (val s w)) :
    ∃ i j : ℕ, (i:ℤ)-j=indexFromDigits s (padded w) ∧
      ∀ᶠ η in 𝓝 (val s w), Meets s η i j ∧
        (∀ k < i, (path s η true k).2 ≠ η) ∧ (∀ k < j, (path s η false k).2 ≠ η) ∧
        ∀ u ≤ i, ∀ v ≤ j, Meets s η u v → (u:ℤ)-v=indexFromDigits s (padded w) := by
  obtain ⟨i,j,h,lag⟩ := marked_word hs w hw clear
  have hs' : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  have a := fun (k : ℕ) (_ : k < i) => word_avoid hs w hw true k
  have b := fun (k : ℕ) (_ : k < j) => word_avoid hs w hw false k
  have mt := (meets_iff hs' a b).mpr h
  refine ⟨i,j,lag,?_⟩
  filter_upwards [witness_neighborhood hs' a b mt] with η H
  refine ⟨H.1,H.2.1,H.2.2,?_⟩
  intro u hu v hv M
  have leq := lag_of_meetings hs' (i:=u) (j:=v) (k:=i) (l:=j)
    (fun k hk => H.2.1 k (lt_of_lt_of_le hk (max_le hu le_rfl)))
    (fun k hk => H.2.2 k (lt_of_lt_of_le hk (max_le hv le_rfl))) M H.1
  omega

#print axioms window_of_word
end BCMP430.WordWindow
