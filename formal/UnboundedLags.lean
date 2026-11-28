import DominantWindow

namespace BCMP430.Unbounded
open Dominant Amplify Direct DominantWindow Filter Witness
open scoped Topology

private theorem flat (a b : Pairs) : flatten (a++b) = flatten a ++ flatten b := by
  induction a with
  | nil => rfl
  | cons x xs ih => obtain ⟨c,d⟩ := x; simp [flatten,ih]

private theorem idx (a b : Pairs) : ctIndex (a++b) = ctIndex a + ctIndex b := by
  induction a with
  | nil => simp [ctIndex]
  | cons x xs ih => obtain ⟨c,d⟩ := x; simp only [List.cons_append,ctIndex,ih]; omega

private theorem repIndex (w : Pairs) (n : ℕ) : ctIndex (repeatPairs w n) = n * ctIndex w := by
  induction n with
  | zero => simp [repeatPairs,ctIndex]
  | succ n ih => rw [repeatPairs,idx,ih]; push_cast; ring

private theorem repeat_add (w : Pairs) (k l : ℕ) :
    repeatPairs w (k+l) = repeatPairs w k ++ repeatPairs w l := by
  induction k with
  | zero => simp [repeatPairs]
  | succ k ih => rw [Nat.succ_add,repeatPairs,ih,repeatPairs,List.append_assoc]

private theorem repBound {s : ℤ} {w : Pairs} (h : Bounded s (flatten w)) (m : ℕ) : Bounded s (flatten (repeatPairs w m)) := by
  induction m with
  | zero => simp [repeatPairs,flatten,Bounded]
  | succ m ih => rw [repeatPairs,flat]; intro a ha; rcases List.mem_append.mp ha with hl|hr; exact h _ hl; exact ih _ hr

private theorem copies_eq (w b : Pairs) (n : ℕ) : flatten (repeatPairs w n ++ b) = copies (flatten w) (flatten b) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [repeatPairs,List.append_assoc,flat,ih,copies]

private theorem even (w : Pairs) : (flatten w).length%2=0 := by
  induction w with
  | nil => rfl
  | cons p w ih => obtain ⟨c,d⟩ := p; simp only [flatten,List.length_cons]; omega

private theorem notnil {p : Pairs} (h : p≠[]) : flatten p ≠ [] := by cases p with
  | nil => contradiction
  | cons z p => obtain ⟨a,b⟩ := z; simp [flatten]

private theorem bump {w b : Pairs} (hd : Dom (flatten w)) (hb : Tail (flatten w) (flatten b)) (m : ℕ) :
    Dom (flatten (repeatPairs w (m+1) ++ b)) := by
  rw [copies_eq]; exact suffix_amplification hd hb (even b) _ (by omega)

private theorem bound_bump {s : ℤ} {w b : Pairs} (hw : Bounded s (flatten w)) (hb : Bounded s (flatten b)) (m : ℕ) :
    Bounded s (flatten (repeatPairs w m ++ b)) := by
  rw [flat]; intro a h; rcases List.mem_append.mp h with h|h; exact repBound hw m a h; exact hb a h

/-- In any prescribed repetition-prefix of any bounded dominant word of at least
    two digit pairs, actual matching neighborhoods have infinitely many signed lags. -/
theorem infinitely_many_lags {s a b : ℤ} {q : Pairs} (hs : 2≤s) (hq : q≠[])
    (hd : Dom (flatten ((a,b)::q))) (bv : Bounded s (flatten ((a,b)::q))) (K : ℕ) :
    let w := (a,b)::q
    ∃ seq : ℕ → Pairs, Function.Injective (fun n => (s+1)*ctIndex (seq n)) ∧
      ∀ n, (∃ tail, seq n=repeatPairs w K ++ tail) ∧ Bounded s (flatten (seq n)) ∧ Dom (flatten (seq n)) ∧
        ∃ i j : ℕ, (i:ℤ)-j=(s+1)*ctIndex (seq n) ∧
          ∀ᶠ η in 𝓝 (eval s (flatten (seq n)) 0), Meets s η i j ∧
            ∀ u ≤ i, ∀ v ≤ j, Meets s η u v → (u:ℤ)-v=(s+1)*ctIndex (seq n) := by
  let w := (a,b)::q
  have tail : Tail (flatten w) (flatten q) := ⟨[a,b],by simp,notnil hq,rfl⟩
  have qb : Bounded s (flatten q) := fun z hz => bv z (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz))
  let t := fun m => repeatPairs w m ++ q
  have formula (m : ℕ) : ctIndex (t m) = m*ctIndex w+ctIndex q := by simp only [t,idx,repIndex]
  have nonzero : ∃ m, (m=K+1 ∨ m=K+2) ∧ ctIndex (t m)≠0 := by
    by_cases h : ctIndex (t (K+1))=0
    · refine ⟨K+2,Or.inr rfl,?_⟩
      intro h'
      rw [formula] at h h'; push_cast at h h'
      have hwz : ctIndex w=0 := by linarith only [h,h']
      rw [hwz,mul_zero,zero_add] at h
      change (a-b)+ctIndex q=0 at hwz
      have hab := distinct_heads hd
      exact hab (by omega)
    · exact ⟨K+1,Or.inl rfl,h⟩
  obtain ⟨m,hm,hn⟩ := nonzero
  have mpos : 0<m := by omega
  have d : Dom (flatten (t m)) := by obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m≠0); exact bump hd tail j
  have tb := bound_bump bv qb m
  have tm : repeatPairs w m ≠ [] := by cases m with
    | zero => omega
    | succ k => simp [repeatPairs,w]
  have tail' : Tail (flatten (t m)) (flatten q) := ⟨flatten (repeatPairs w m),notnil tm,notnil hq,flat ..⟩
  let seq := fun n : ℕ => repeatPairs (t m) (n+1) ++ q
  have lag (n : ℕ) : ctIndex (seq n) = ((n:ℤ)+1)*ctIndex (t m)+ctIndex q := by simp only [seq,idx,repIndex,Nat.cast_succ]
  refine ⟨seq,?_,?_⟩
  · intro n j he
    change (s+1)*ctIndex (seq n)=(s+1)*ctIndex (seq j) at he
    rw [lag,lag] at he
    have h₁ := mul_left_cancel₀ (show s+1 ≠ 0 by omega) he
    have h₂ := mul_right_cancel₀ hn (add_right_cancel h₁)
    omega
  · intro n
    have hx : seq n=repeatPairs w K ++ (repeatPairs w (m-K) ++ q ++ repeatPairs (t m) n ++ q) := by
      change ((repeatPairs w m ++ q) ++ repeatPairs (t m) n) ++ q = _
      have hm' : repeatPairs w m = repeatPairs w K ++ repeatPairs w (m-K) := by rw [←repeat_add,show K+(m-K)=m by omega]
      rw [hm']; simp only [List.append_assoc]
    have dom := bump d tail' n
    have bvs := bound_bump tb qb (n+1)
    refine ⟨⟨_,hx⟩,bvs,dom,?_⟩
    have L : 2 ≤ (seq n).length := by
      have qpos := List.length_pos_iff.mpr hq
      have rpos := List.length_pos_iff.mpr tm
      simp only [seq,repeatPairs,List.length_append,t]
      omega
    have sn : seq n ≠ [] := by intro he; rw [he] at L; simp at L
    obtain ⟨pre,last,eqn⟩ : ∃ (pre : Pairs) (last : ℤ × ℤ), seq n=pre++[last] :=
      ⟨(seq n).dropLast,(seq n).getLast sn,(List.dropLast_append_getLast sn).symm⟩
    obtain ⟨c,d'⟩ := last
    change seq n=pre++[(c,d')] at eqn
    change Dom (flatten (seq n)) at dom
    change Bounded s (flatten (seq n)) at bvs
    rw [eqn] at dom bvs L ⊢
    exact (dominant_window hs pre c d' dom bvs (by intro h; rw [h] at L; simp at L)).2.2

#print axioms infinitely_many_lags
end BCMP430.Unbounded
