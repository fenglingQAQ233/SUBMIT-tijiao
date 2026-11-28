import TrappedReturn

namespace BCMP430.ConstantTailCoverage
open Dominant PrefixCoverage Original Survivor UntunedTarget Set

/-- In a prefix followed by a long constant tail, a border either starts with that
    constant, or it would have to contain all the occurrences of the first letter
    after a nonempty initial segment containing that very letter has been removed. -/
theorem tail_unbordered (a b : ℤ) (v : Word) (m : ℕ) (dif : a≠b) (long : (a::v).length≤m) :
    Unbordered ((a::v)++List.replicate m b) := by
  let P := a::v
  let B := List.replicate m b
  let W := P++B
  have Ppre : P <+: W := ⟨B,rfl⟩
  have Bsu : B <:+ W := ⟨P,rfl⟩
  have noA : a∉B := by simp [B,List.mem_replicate,dif]
  intro t ht pref
  obtain ⟨q,hq,ht,eq⟩ := ht
  change W=q++t at eq
  change t <+: W at pref
  have suff : t <:+ W := ⟨q,eq.symm⟩
  have front (u : Word) (hn : u≠[]) (h : u <+: W) : a∈u := by
    cases u with
    | nil => exact (hn rfl).elim
    | cons z zs =>
      change z::zs <+: a::(v++B) at h
      have e := (List.cons_prefix_cons.mp h).1
      simp [e]
  by_cases len : t.length≤m
  · have sub := List.suffix_of_suffix_length_le suff Bsu (by simpa [B] using len)
    exact noA (sub.sublist.subset (front t ht pref))
  · have sub := List.prefix_of_prefix_length_le Ppre pref (long.trans (Nat.le_of_lt (lt_of_not_ge len)))
    obtain ⟨rest,H⟩ := sub
    have cnt : P.count a ≤ t.count a := by rw [←H,List.count_append]; omega
    have positive := List.count_pos_iff.mpr (front q hq ⟨t,eq.symm⟩)
    have E := congrArg (List.count a) eq
    change (P++B).count a=_ at E
    rw [List.count_append,List.count_append,List.count_eq_zero_of_not_mem noA] at E
    omega

private theorem cat (s : ℤ) (x : ℝ) (k n : ℕ) :
    readWord s x (k+n)=readWord s x k++readWord s ((g s)^[k] x) n := by
  induction k generalizing x with
  | zero => simp [readWord]
  | succ k ih => rw [Nat.succ_add,readWord,ih,readWord,Function.iterate_succ_apply]; rfl

private theorem size (s : ℤ) (x : ℝ) (k : ℕ) : (readWord s x k).length=k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp [readWord,ih]

theorem fixed_tail_accum {s : ℤ} (hs : 2≤s) {x r : ℝ} (hu : x∈UT s) (hp : 0<x) (ht : x<(s:ℝ)/(s+1))
    (fix : g s r=r) {N : ℕ} (hit : (g s)^[N] x=r) (dif : digit s x≠digit s r) : Accum s x := by
  apply unbordered_cover hs hu hp ht
  have pos : N≠0 := by intro e; subst N; simp only [Function.iterate_zero_apply] at hit; exact dif (congrArg (digit s) hit)
  have rep (m : ℕ) : readWord s r m=List.replicate m (digit s r) := by
    induction m with
    | zero => rfl
    | succ m ih => simp [readWord,fix,ih,List.replicate_succ]
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero pos
  intro K
  let m := j+1+2*K
  refine ⟨(j+1)+m,by dsimp [m]; omega,by dsimp [m]; omega,?_⟩
  rw [cat,hit,rep,readWord]
  apply tail_unbordered _ _ _ _ dif
  simp only [List.length_cons,size]; dsimp [m]; omega

/-- If an interior orbit-minimum reaches the top fixed point, its initial digit
    differs from the constant tail: the single top branch cannot contain an
    orbit-minimum strictly below its fixed point. -/
theorem top_preperiodic {s : ℤ} (hs : 2≤s) {x : ℝ} (hp : 0<x) (ht : x<(s:ℝ)/(s+1))
    (surv : ∀ j : ℕ, x≤(g s)^[j] x) {N : ℕ} (hit : (g s)^[N] x=(s:ℝ)/(s+1)) :
    x∈UT s ∧ Accum s x := by
  let h := (s:ℝ)/(s+1)
  have sp : (0:ℝ)<s := by exact_mod_cast (show 0<s by omega)
  have sr : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  have hp' : 0<h := div_pos sp (by linarith)
  have h1 : h<1 := (div_lt_one (by linarith : 0<(s:ℝ)+1)).mpr (by linarith)
  have eq : h*((s:ℝ)+1)=s := div_mul_cancel₀ _ (by linarith)
  have fix : g s h=h := Int.fract_eq_iff.mpr ⟨hp'.le,h1,-s,by push_cast; linarith only [eq]⟩
  have fh : ⌊-(s:ℝ)*h⌋= -s := Int.floor_eq_iff.mpr ⟨by push_cast; linarith only [hp',eq],by push_cast; linarith only [h1,eq]⟩
  have hu := TrappedReturn.eventual_top_untuned hs ⟨hp.le,ht.le⟩ surv hit
  refine ⟨hu,fixed_tail_accum hs hu hp ht fix hit ?_⟩
  intro d
  unfold digit at d
  rw [fh] at d
  have fx : ⌊-(s:ℝ)*x⌋= -s := by omega
  let y := g s x
  have yr : y = (s:ℝ)*(1-x) := by change -(s:ℝ)*x-(⌊-(s:ℝ)*x⌋:ℝ)=_; rw [fx]; push_cast; ring
  have yh : h<y := by change x<h at ht; nlinarith only [yr,eq,mul_pos sp (sub_pos.mpr ht)]
  have y1 : y<1 := Int.fract_lt_one _
  have fy : ⌊-(s:ℝ)*y⌋= -s := Int.floor_eq_iff.mpr ⟨by push_cast; nlinarith only [mul_pos sp (sub_pos.mpr y1)],by push_cast; nlinarith only [eq,h1,mul_pos sp (sub_pos.mpr yh)]⟩
  have g2 : g s y=(s:ℝ)*(1-y) := by unfold g Int.fract; rw [fy]; push_cast; ring
  have mn := surv 2
  change x≤g s y at mn
  have H : y-h=(s:ℝ)*(h-x) := by linarith only [yr,eq]
  have F : g s y-h= -(s:ℝ)*(y-h) := by linarith only [g2,eq]
  change x<h at ht
  have G := mul_lt_mul_of_pos_right sr (sub_pos.mpr ht)
  have J := mul_lt_mul_of_pos_right sr (sub_pos.mpr yh)
  linarith only [H,F,G,J,mn]

#print axioms tail_unbordered
#print axioms fixed_tail_accum
#print axioms top_preperiodic
end BCMP430.ConstantTailCoverage
