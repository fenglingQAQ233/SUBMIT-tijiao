import DropWindow

namespace BCMP430.PrefixCoverage
open Dominant Direct Amplify Survivor Original UntunedTarget MetricLocus Set

/-- No nonempty proper suffix is a prefix. -/
def Unbordered (w : Word) := ∀ t, Tail w t → ¬t <+: w

noncomputable def readWord (s : ℤ) (x : ℝ) : ℕ → Word
  | 0 => []
  | n+1 => digit s x :: readWord s (g s x) n

private theorem read_length (s : ℤ) (x : ℝ) (n : ℕ) : (readWord s x n).length=n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [readWord,ih]

private theorem read_cat (s : ℤ) (x : ℝ) (k n : ℕ) :
    readWord s x (k+n) = readWord s x k ++ readWord s ((g s)^[k] x) n := by
  induction k generalizing x with
  | zero => simp [readWord]
  | succ k ih => rw [Nat.succ_add,readWord,ih,readWord,Function.iterate_succ_apply]; rfl

private theorem split_read {s : ℤ} {x : ℝ} {n : ℕ} {a b : Word} (h : readWord s x n=a++b) :
    b=readWord s ((g s)^[a.length] x) b.length := by
  have len := congrArg List.length h
  rw [read_length,List.length_append] at len
  rw [len,read_cat] at h
  have eqn := congrArg (List.drop a.length) h
  rw [List.drop_left] at eqn
  have eq' : (readWord s x a.length).length = a.length := read_length ..
  have d := @List.drop_left ℤ (readWord s x a.length) (readWord s ((g s)^[a.length] x) b.length)
  rw [eq'] at d
  exact eqn.symm.trans d

private theorem order_prefix {s : ℤ} (hs : 2≤s) (m n : ℕ) (len : m≤n) {x y : ℝ} (rev : Bool)
    (h : if rev then x≤y else y≤x) :
    ltWord rev (readWord s x n) (readWord s y m) ∨ readWord s y m <+: readWord s x n := by
  have hsp : (0:ℝ)<s := by exact_mod_cast (show 0<s by omega)
  induction m generalizing n x y rev with
  | zero => right; simp [readWord]
  | succ m ih =>
    cases n with
    | zero => omega
    | succ n =>
      let dx := digit s x
      let dy := digit s y
      have flip {u v : ℝ} (hu : u≤v) : digit s v ≤ digit s u := by
        unfold digit; have hh := Int.floor_mono (mul_le_mul_of_nonpos_left hu (neg_nonpos.mpr hsp.le)); omega
      by_cases e : dx=dy
      · have ef : ⌊-(s:ℝ)*x⌋ = ⌊-(s:ℝ)*y⌋ := by dsimp [dx,dy,digit] at e; omega
        have hnext : if !rev then g s x≤g s y else g s y≤g s x := by
          unfold g Int.fract; rw [ef]; cases rev <;> simp only [Bool.not_true,Bool.not_false,Bool.false_eq_true,ite_false,ite_true] at h ⊢
          · linarith [mul_le_mul_of_nonneg_left h hsp.le]
          · linarith [mul_le_mul_of_nonneg_left h hsp.le]
        rcases ih n (by omega) (!rev) hnext with hc|hc
        · left; change (if dx=dy then _ else _) ; simpa only [e,ite_true] using hc
        · right; exact List.cons_prefix_cons.mpr ⟨e.symm,hc⟩
      · left; change (if dx=dy then _ else _); rw [ite_eq_right e]
        cases rev <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h ⊢
        · have H : dx ≤ dy := flip h; omega
        · have H : dy ≤ dx := flip h; omega

theorem dominant_of_unbordered {s : ℤ} (hs : 2≤s) (x : ℝ) (surv : ∀ k, x≤(g s)^[k] x)
    (n : ℕ) (hp : 0<n) (hev : n%2=0) (hu : Unbordered (readWord s x n)) : Dom (readWord s x n) := by
  refine ⟨fun h => by have H := congrArg List.length h; rw [read_length] at H; simp at H; omega,by rwa [read_length],?_⟩
  intro t ht
  have npre := hu t ht
  obtain ⟨a,_,_,eqn⟩ := ht
  have le := congrArg List.length eqn
  rw [read_length,List.length_append] at le
  have H := order_prefix hs t.length n (by omega) true (surv a.length)
  rw [←split_read eqn] at H
  exact H.resolve_right npre

private theorem repack (w : Word) (h : w.length%2=0) : ∃ p : Pairs, flatten p=w := by
  match w with
  | [] => exact ⟨[],rfl⟩
  | [_] => simp at h
  | a::b::t =>
    obtain ⟨p,hp⟩ := repack t (by simp only [List.length_cons] at h; omega)
    exact ⟨(a,b)::p, by simp [flatten,hp]⟩

private theorem read_valid {s : ℤ} (x : ℝ) (h : ∀ i, 1≤code s x i ∧ code s x i≤s) (n : ℕ) :
    Direct.Bounded s (readWord s x n) := by
  induction n generalizing x with
  | zero => simp [Direct.Bounded,readWord]
  | succ n ih =>
    intro a ha
    rcases List.mem_cons.mp ha with he|he
    · subst a; exact h 0
    · apply ih (g s x) _ a he
      intro j; simpa only [Survivor.code,pos,Function.iterate_succ_apply] using h (j+1)

private theorem decode_read {s : ℤ} (hs : 2≤s) (x : ℝ) (n : ℕ) :
    eval s (readWord s x n) ((g s)^[n] x)=x := by
  have hn : (s:ℝ)≠0 := by exact_mod_cast (show s≠0 by omega)
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [readWord,eval,Function.iterate_succ_apply,ih]
    change ((s:ℝ)+1-((s+1+⌊-(s:ℝ)*x⌋:ℤ):ℝ)-Int.fract (-(s:ℝ)*x))/(s:ℝ)=x
    apply (div_eq_iff hn).mpr
    rw [Int.fract]; push_cast; ring

/-- The word-length hypothesis is not required for periodic points already handled
    by `rich_fixed`; it is a sufficient condition intended for nonperiodic points. -/
theorem unbordered_cover {s : ℤ} (hs : 2≤s) {x : ℝ} (hu : x∈UT s) (hp : 0<x)
    (ht : x<(s:ℝ)/(s+1))
    (long : ∀ N : ℕ, ∃ n ≥ N, n%2=0 ∧ Unbordered (readWord s x n)) : Accum s x := by
  have surv := DropWindow.ut_survives hs hu hp ht
  have hsr : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  have hx1 : x<1 := ht.trans (by apply (div_lt_one (by linarith : (0:ℝ)<s+1)).mpr; linarith)
  have hv := (positive_survivor hs hp hx1 surv).1
  apply Components.accum_closure_roots hs
  apply Metric.mem_closure_iff.mpr
  intro ε he
  let r := (s:ℝ)⁻¹
  have hr : r<1 := inv_lt_one_of_one_lt₀ hsr
  have hr0 : 0≤r := inv_nonneg.mpr (zero_lt_one.trans hsr).le
  obtain ⟨N,hN⟩ := exists_pow_lt_of_lt_one he hr
  obtain ⟨n,hn,par,ub⟩ := long (max N 4)
  have n4 : 4≤n := (le_max_right ..).trans hn
  have hd := dominant_of_unbordered hs x surv n (by omega) par ub
  have valid := read_valid x hv n
  obtain ⟨z,hz,fix⟩ := MetricLocus.word_fixed_point hs hd valid
  obtain ⟨p,ef⟩ := repack (readWord s x n) (by simpa only [read_length] using par)
  have root : z∈roots s := by
    cases p with
    | nil => have h := congrArg List.length ef; simp [flatten,read_length] at h; omega
    | cons a q =>
      obtain ⟨a,b⟩ := a
      refine ⟨a,b,q,?_,ef ▸ hd,ef ▸ valid,hz,ef ▸ fix⟩
      intro eq; subst q; have h := congrArg List.length ef; simp [flatten,read_length] at h; omega
  refine ⟨z,root,?_⟩
  have eq := MetricLocus.word_difference s (readWord s x n) ((g s)^[n] x) z
  rw [decode_read hs,fix,read_length] at eq
  have tail₀ := (hp.le.trans (surv n))
  have tail₁ : (g s)^[n] x<1 := by cases n with
    | zero => exact hx1
    | succ n => rw [Function.iterate_succ_apply']; exact Int.fract_lt_one _
  have small : |(g s)^[n] x-z|≤1 := abs_sub_le_iff.mpr ⟨by linarith [hz.1],by linarith [hz.2]⟩
  rw [Real.dist_eq,eq,abs_mul,abs_pow,abs_neg,abs_of_nonneg hr0]
  exact lt_of_le_of_lt ((mul_le_mul_of_nonneg_left small (pow_nonneg hr0 n)).trans_eq (mul_one _))
    ((pow_le_pow_of_le_one hr0 hr.le ((le_max_left ..).trans hn)).trans_lt hN)

#print axioms dominant_of_unbordered
#print axioms unbordered_cover
end BCMP430.PrefixCoverage
