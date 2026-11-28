import DominantSuffix

namespace BCMP430.Amplify
open Dominant

/-- Consecutive CT partial quotients, grouped in pairs to align the sign of the index. -/
def flatten : Pairs → Word
  | [] => []
  | (a,b)::r => a::b::flatten r

private theorem flat_append (p q : Pairs) : flatten (p++q) = flatten p ++ flatten q := by
  induction p with
  | nil => rfl
  | cons x xs ih => obtain ⟨u,v⟩ := x; simp [flatten,ih]

private theorem flat_length (p : Pairs) : (flatten p).length = 2*p.length := by
  induction p with
  | nil => rfl
  | cons x xs ih => obtain ⟨u,v⟩ := x; simp [flatten,ih]; omega

def repeatPairs (p : Pairs) : Nat → Pairs
  | 0 => []
  | n+1 => p ++ repeatPairs p n

private theorem flat_repeated_tail (p q : Pairs) (m : Nat) :
    flatten (repeatPairs p m ++ q) = copies (flatten p) (flatten q) m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [repeatPairs,List.append_assoc,flat_append,ih,copies]

private theorem idx_append (p q : Pairs) : ctIndex (p++q) = ctIndex p + ctIndex q := by
  induction p with
  | nil => simp [ctIndex]
  | cons x xs ih => obtain ⟨u,v⟩ := x; simp only [List.cons_append,ctIndex,ih]; omega

private theorem repeat_neutral {p : Pairs} (h : ctIndex p = 0) (m : Nat) :
    ctIndex (repeatPairs p m) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [repeatPairs,idx_append,h,ih]

private theorem repeat_length (p : Pairs) (m : Nat) :
    (repeatPairs p m).length = m * p.length := by
  induction m with
  | zero => simp [repeatPairs]
  | succ m ih => simp [repeatPairs,ih,Nat.succ_mul,Nat.add_comm]

/-- The same word is dominant, has arbitrarily many initial copies of the original,
    and has the fixed nonzero BCMP digit index (s+1)(b-a). -/
theorem neutral_amplify {s a b : Int} {q : Pairs} (hs : 2 ≤ s)
    (hd : Dom (flatten ((a,b)::q))) (hz : ctIndex ((a,b)::q) = 0)
    (m : Nat) (hm : 0<m) :
    let p := (a,b)::q
    let t := repeatPairs p m ++ q
    Dom (flatten t) ∧ flatten t = flatten (repeatPairs p m) ++ flatten q ∧
      (flatten (repeatPairs p m)).length = m * (flatten p).length ∧
      indexFromDigits s (decode s t) = (s+1)*(b-a) ∧ indexFromDigits s (decode s t) ≠ 0 := by
  have hab : a ≠ b := distinct_heads hd
  change (a-b)+ctIndex q = 0 at hz
  have hq : flatten q ≠ [] := by
    intro he
    have hh := congrArg List.length he
    rw [flat_length] at hh
    cases q with
    | nil => simp [ctIndex] at hz; omega
    | cons x xs => simp at hh
  have heven : (flatten q).length%2=0 := by rw [flat_length]; omega
  have ht : Tail (flatten ((a,b)::q)) (flatten q) := ⟨[a,b],by simp,hq,rfl⟩
  have hi : ctIndex (repeatPairs ((a,b)::q) m ++ q) = b-a := by
    rw [idx_append, repeat_neutral (p := (a,b)::q) hz m]; omega
  have hidx := index_decode s (repeatPairs ((a,b)::q) m ++ q)
  rw [hi] at hidx
  refine ⟨?_,flat_append ..,?_,hidx,?_⟩
  · rw [flat_repeated_tail]; exact suffix_amplification hd ht heven m hm
  · rw [flat_length,flat_length,repeat_length]; ac_rfl
  · rw [hidx]; exact Int.mul_ne_zero (by omega) (by omega)

#print axioms neutral_amplify
end BCMP430.Amplify
