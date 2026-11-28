import DominantSuffix
import WordNeighborhood

namespace BCMP430.Direct
open Dominant Original Tape

/-- Affine inverse of -s*x modulo one for a single partial quotient. -/
noncomputable def branch (s a : ℤ) (x : ℝ) := ((s:ℝ)+1-a-x)/(s:ℝ)
noncomputable def eval (s : ℤ) : Word → ℝ → ℝ
  | [], t => t
  | a::as, t => branch s a (eval s as t)

def Bounded (s : ℤ) (w : Word) := ∀ a ∈ w, 1≤a ∧ a≤s

private theorem tail_bound {s a w} (h : Bounded s (a::w)) : Bounded s w :=
  fun z hz => h z (List.mem_cons_of_mem _ hz)

private theorem range {s : ℤ} (hs : 2≤s) {w : Word} (hw : Bounded s w) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) : eval s w t ∈ Set.Icc (0:ℝ) 1 := by
  have sp : (0:ℝ)<s := by exact_mod_cast (show 0<s by omega)
  induction w with
  | nil => exact ht
  | cons a w ih =>
    have ha := hw a (by simp)
    have lo : (1:ℝ)≤a := by exact_mod_cast ha.1
    have hi : (a:ℝ)≤s := by exact_mod_cast ha.2
    have z := ih (tail_bound hw)
    constructor
    · apply div_nonneg _ sp.le; linarith [z.2]
    · apply (div_le_one sp).mpr; linarith [z.1]

/-- Alternating finite-word comparisons give weak real inequalities even at double
    expansions. Continued-fraction convergence is not used. -/
private theorem ordered {s : ℤ} (hs : 2≤s) {w u : Word} (hw : Bounded s w)
    (hu : Bounded s u) (rev : Bool) (hc : ltWord rev w u) {t v : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hv : v ∈ Set.Icc (0:ℝ) 1) :
    if rev then eval s w t ≤ eval s u v else eval s u v ≤ eval s w t := by
  have sp : (0:ℝ)<s := by exact_mod_cast (show 0<s by omega)
  induction w generalizing rev u with
  | nil => cases u <;> contradiction
  | cons a w ih =>
    cases u with
    | nil => contradiction
    | cons b u =>
      have wB := tail_bound hw
      have uB := tail_bound hu
      by_cases he : a=b
      · subst b
        simp only [ltWord,ite_true] at hc
        have h := ih wB uB (!rev) hc
        cases rev <;> simp only [Bool.not_false,Bool.not_true,ite_true,Bool.false_eq_true,ite_false] at h ⊢ <;>
          apply (div_le_div_iff_of_pos_right sp).mpr <;> linarith
      · have wa := range hs wB ht
        have ua := range hs uB hv
        simp only [ltWord,he,ite_false] at hc
        cases rev <;> simp only [ite_true,Bool.false_eq_true,ite_false] at hc ⊢
        · have hh : (a:ℝ)+1 ≤ b := by exact_mod_cast (show a+1≤b by omega)
          apply (div_le_div_iff_of_pos_right sp).mpr; linarith [wa.2,ua.1]
        · have hh : (b:ℝ)+1 ≤ a := by exact_mod_cast (show b+1≤a by omega)
          apply (div_le_div_iff_of_pos_right sp).mpr; linarith [ua.2,wa.1]

private theorem strip (s a : ℤ) (hs : 2≤s) (v : ℝ) : g s (Int.fract (branch s a v)) = Int.fract v := by
  have sp : (s:ℝ) ≠ 0 := by exact_mod_cast (show s≠0 by omega)
  unfold g; apply Int.fract_eq_fract.mpr
  refine ⟨a-1-s+s*⌊branch s a v⌋,?_⟩
  have m : (s:ℝ)*branch s a v=(s:ℝ)+1-a-v := by unfold branch; field_simp
  rw [Int.fract]; push_cast; linarith only [m]

private theorem nth (s : ℤ) (hs : 2≤s) (w : Word) (t : ℝ) (k : ℕ) :
    (g s)^[k] (Int.fract (eval s w t)) = Int.fract (eval s (w.drop k) t) ∨
      w.length < k := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    cases w with
    | nil => exact Or.inr (by simp)
    | cons a w =>
      rw [Function.iterate_succ_apply]; change (g s)^[k] (g s (Int.fract (branch s a (eval s w t)))) = _ ∨ _
      rw [strip s a hs]; simpa using ih w

private theorem terminal (s : ℤ) (hs : 2≤s) (w : Word) : (g s)^[w.length] (Int.fract (eval s w 0))=0 := by
  have h := (nth s hs w 0 w.length).resolve_right (lt_irrefl _)
  simpa [eval] using h

/-- A bounded dominant word with a positive interior finite evaluation satisfies
    the actual BCMP strict orbit test, without either tuning-window endpoint. -/
theorem dominant_clear {s : ℤ} (hs : 2≤s) {w : Word} (dom : Dom w) (valid : Bounded s w)
    (positive : 0<eval s w 0) (interior : eval s w 0<1) :
    Clear s (eval s w 0) (eval s w 0) := by
  let x := eval s w 0
  have hfrac : Int.fract x=x := Int.fract_eq_self.mpr ⟨positive.le,interior⟩
  have stop : (g s)^[w.length] x=0 := by
    have ht := terminal s hs w
    change (g s)^[w.length] (Int.fract x)=0 at ht
    rwa [hfrac] at ht
  have gz : g s 0=0 := by simp [g]
  have later (k : ℕ) (hk : w.length ≤ k) : (g s)^[k] x=0 := by
    rw [show k=k-w.length+w.length by omega,Function.iterate_add_apply,stop]; exact Function.iterate_fixed gz _
  intro j
  let k := j+1
  change (g s)^[k] x=0 ∨ _
  by_cases hk : w.length ≤ k
  · exact Or.inl (later k hk)
  · have hn : 0<k := by dsimp [k]; omega
    have hsuff : Tail w (w.drop k) := by
      refine ⟨w.take k,?_,?_,(List.take_append_drop k w).symm⟩
      · intro h; have len := congrArg List.length h; simp only [List.length_take,List.length_nil,min_eq_left (by omega : k≤w.length)] at len; omega
      · intro h; have len := congrArg List.length h; simp only [List.length_drop,List.length_nil] at len; omega
    have suffB : Bounded s (w.drop k) := fun a h => valid a (List.mem_of_mem_drop h)
    have weak : x ≤ eval s (w.drop k) 0 := ordered hs valid suffB true (dom.2.2 _ hsuff) (by simp) (by simp)
    have ub := (range hs suffB (t:=0) (by simp)).2
    have hval := (nth s hs w 0 k).resolve_right (by omega)
    change (g s)^[k] (Int.fract x)=_ at hval
    rw [hfrac] at hval
    by_cases h1 : eval s (w.drop k) 0=1
    · left; rw [hval,h1]; norm_num
    · have vlt : eval s (w.drop k) 0<1 := lt_of_le_of_ne ub h1
      rw [Int.fract_eq_self.mpr ⟨positive.le.trans weak,vlt⟩] at hval
      right
      change x < (g s)^[k] x
      apply lt_of_le_of_ne (hval.symm ▸ weak)
      intro cyc
      have cycle (n : ℕ) : (g s)^[n*k] x=x := by
        induction n with
        | zero => simp
        | succ n ih => rw [Nat.succ_mul,Function.iterate_add_apply,←cyc,ih]
      have far : w.length ≤ w.length*k := by simpa using Nat.mul_le_mul_left w.length hn
      have z := later (w.length*k) far
      rw [cycle] at z; exact positive.ne' z

#print axioms dominant_clear
end BCMP430.Direct
