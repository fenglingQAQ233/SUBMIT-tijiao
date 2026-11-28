import ComponentClock

namespace BCMP430.DepthClock
open Set Original Germ MatchLag Components UntunedTarget ComponentClock Adic Witness

private theorem unit_iter (s : ℤ) {x : ℝ} (hx : x∈Ico (0:ℝ) 1) (k : ℕ) : (g s)^[k] x∈Ico (0:ℝ) 1 := by
  cases k with
  | zero => exact hx
  | succ k => rw [Function.iterate_succ_apply']; exact ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩

private theorem until_depth {s : ℤ} (hs : 2≤s) (c : Center s) {k : ℕ} (hk : 0<k) (early : k<c.depth) :
    c.x < (g s)^[k] c.x := by
  have sp : (0:ℝ)<s := by exact_mod_cast (show 0<s by omega)
  have xt := c.inside.2.trans ((div_lt_one (by linarith : 0<(s:ℝ)+1)).mpr (by linarith))
  have u := unit_iter s ⟨c.inside.1.le,xt⟩ k
  have coarse (gk : GridAt s k c.x) : False := by
    have le : k≤c.depthPred := by change k<c.depthPred+1 at early; omega
    obtain ⟨a,ha⟩ := gk
    apply c.offGrid; refine ⟨s^(c.depthPred-k)*a,?_⟩
    nth_rewrite 1 [show c.depthPred=c.depthPred-k+k by omega]; rw [pow_add,mul_assoc,ha]; push_cast; rfl
  have nozero : (g s)^[k] c.x≠0 := by
    intro z; obtain ⟨a,ha⟩ := FirstDrop.iterate_lift s c.x k; rw [z,add_zero] at ha
    rcases Nat.even_or_odd k with h|h
    · rw [h.neg_pow] at ha; exact coarse ⟨a,ha⟩
    · rw [h.neg_pow,neg_mul] at ha; exact coarse ⟨-a,by push_cast; linarith only [ha]⟩
  have avoid := c.avoid (k-1); rw [show k-1+1=k by omega] at avoid
  have le := le_of_not_gt (fun bad => avoid ⟨lt_of_le_of_ne u.1 (Ne.symm nozero),bad⟩)
  apply lt_of_le_of_ne le
  intro eq
  have per (j : ℕ) : (g s)^[j*k] c.x=c.x := by
    induction j with
    | zero => simp
    | succ j ih => rw [Nat.succ_mul,Function.iterate_add_apply,←eq,ih]
  let n := c.depth*k
  have nd : c.depth≤n := by simpa [n] using Nat.mul_le_mul_left c.depth hk
  obtain ⟨a,ha⟩ := c.onGrid; change (s:ℝ)^c.depth*c.x=a at ha
  have later : GridAt s n c.x := by
    refine ⟨s^(n-c.depth)*a,?_⟩; nth_rewrite 1 [show n=n-c.depth+c.depth by omega]; rw [pow_add,mul_assoc,ha]; push_cast; rfl
  obtain ⟨v,hv⟩ := later
  obtain ⟨b,hb⟩ := FirstDrop.iterate_lift s c.x n
  rw [show (g s)^[n] c.x=c.x from per _] at hb
  have integral : ∃ t : ℤ, c.x=t := by
    rcases Nat.even_or_odd n with h|h
    · rw [h.neg_pow,hv] at hb; exact ⟨v-b,by push_cast; linarith only [hb]⟩
    · rw [h.neg_pow,neg_mul,hv] at hb; exact ⟨-v-b,by push_cast; linarith only [hb]⟩
  obtain ⟨t,et⟩ := integral
  have pos : (0:ℤ)<t := by exact_mod_cast (et ▸ c.inside.1 : 0<(t:ℝ))
  have sub : t<(1:ℤ) := by exact_mod_cast (et ▸ xt : (t:ℝ)<1)
  omega

/-- At a fixed count below the center depth, one side is at a strictly positive
    integer height, the other has height at most zero. Translations cannot cross
    from the low side to the high one before a decreasing step. -/
private theorem height_class {s : ℤ} (hs : 2≤s) (c : Center s) (r : Bool) (j : ℕ)
    (early : (path s c.x r j).1 < c.depth) :
    let z := path s c.x r j
    ∃ h : ℤ, z.2=(g s)^[z.1] c.x+(h:ℝ) ∧ (if z.1%2=r.toNat then 1≤h else h≤0) := by
  have sp : (0:ℝ)<s := by exact_mod_cast (show 0<s by omega)
  have xt := c.inside.2.trans ((div_lt_one (by linarith : 0<(s:ℝ)+1)).mpr (by linarith))
  let R := fun k : ℕ => (g s)^[k] c.x
  have U (k : ℕ) : R k∈Ico (0:ℝ) 1 := unit_iter s ⟨c.inside.1.le,xt⟩ k
  have lower (k : ℕ) (l : k<c.depth) : 0<R k := by
    cases k with
    | zero => exact c.inside.1
    | succ k => exact c.inside.1.trans (until_depth hs c (Nat.zero_lt_succ _) l)
  have decomp (k : ℕ) (l : k<c.depth) : ∃ b : ℤ, 1≤b ∧ b≤s ∧ 1+(s:ℝ)*(1-R k)=R (k+1)+(b:ℝ) := by
    let b := 1+s+⌊-(s:ℝ)*R k⌋
    have fl : -s≤⌊-(s:ℝ)*R k⌋ := Int.le_floor.mpr (by push_cast; nlinarith [mul_nonneg sp.le (sub_nonneg.mpr (U k).2.le)])
    have fh : ⌊-(s:ℝ)*R k⌋<0 := Int.floor_lt.mpr (by push_cast; nlinarith [mul_pos sp (lower k l)])
    refine ⟨b,by dsimp [b]; omega,by dsimp [b]; omega,?_⟩
    change _ = (g s)^[k+1] c.x+(b:ℝ); rw [Function.iterate_succ_apply']; change _ = Int.fract (-(s:ℝ)*R k)+(b:ℝ); rw [Int.fract]; dsimp only [b]; push_cast; ring
  have count_right (m : ℕ) : 0<(path s c.x true m).1 := by
    induction m with
    | zero => exact Nat.zero_lt_one
    | succ m ih => rw [show path s c.x true (m+1)=advance s c.x (path s c.x true m) from Function.iterate_succ_apply' ..]; unfold advance; split <;> omega
  induction j with
  | zero =>
    cases r with
    | false => exact ⟨1,by simp [path,seed],by change (1:ℤ)≤1; exact le_rfl⟩
    | true =>
      obtain ⟨b,bl,_,e⟩ := decomp 0 (Nat.zero_lt_succ _)
      exact ⟨b,e,bl⟩
  | succ j ih =>
    let z := path s c.x r j
    have step : path s c.x r (j+1)=advance s c.x z := Function.iterate_succ_apply' ..
    rw [step] at early ⊢
    have old : z.1<c.depth := by unfold advance at early; split at early <;> omega
    obtain ⟨h,eh,cls⟩ := ih old
    change z.2=R z.1+(h:ℝ) at eh
    change (if z.1%2=r.toNat then 1≤h else h≤0) at cls
    have hi : R z.1 < 1 := (U _).2
    have lo : 0≤R z.1 := (U _).1
    have flag : r.toNat≤1 := by cases r <;> decide
    by_cases inc : z.2≤c.x
    · change ∃ t : ℤ, (advance s c.x z).2=R (advance s c.x z).1+(t:ℝ) ∧ _
      simp only [advance,Q,ite_eq_left inc]; refine ⟨h+1,by push_cast; linarith only [eh],?_⟩
      by_cases E : z.1%2=r.toNat
      · rw [ite_eq_left E] at cls ⊢; omega
      · rw [ite_eq_right E] at cls ⊢
        have kpos : 0<z.1 := by
          cases r with
          | true => exact count_right j
          | false => change z.1%2≠0 at E; omega
        have bigger := until_depth hs c kpos old
        change c.x < R z.1 at bigger
        have neg : (h:ℝ)<0 := by linarith only [bigger,inc,eh]
        have hn : h<0 := by exact_mod_cast neg
        omega
    · change ∃ t : ℤ, (advance s c.x z).2=R (advance s c.x z).1+(t:ℝ) ∧ _
      simp only [advance,Q,ite_eq_right inc]
      obtain ⟨b,bl,bu,eq⟩ := decomp z.1 old
      refine ⟨b-s*h,by push_cast; rw [eh]; linarith only [eq],?_⟩
      by_cases E : z.1%2=r.toNat
      · have F : (z.1+1)%2≠r.toNat := by omega
        rw [ite_eq_left E] at cls; rw [ite_eq_right F]
        have m := Int.mul_le_mul_of_nonneg_left cls (show 0≤s by omega); omega
      · have F : (z.1+1)%2=r.toNat := by omega
        rw [ite_eq_right E] at cls; rw [ite_eq_left F]
        have m := Int.mul_nonpos_of_nonneg_of_nonpos (show 0≤s by omega) cls; omega

theorem count_at_meeting {s : ℤ} (hs : 2≤s) (c : Center s) {i j : ℕ}
    (e : path s c.x true i=path s c.x false j) : c.depth ≤ (path s c.x true i).1 := by
  apply le_of_not_gt; intro bad
  obtain ⟨a,A,al⟩ := height_class hs c true i bad
  obtain ⟨b,B,bl⟩ := height_class hs c false j (e ▸ bad)
  simp only [←e] at B bl
  have eq : a=b := by exact_mod_cast (add_left_cancel (A.symm.trans B))
  simp only [Bool.toNat_true,Bool.toNat_false] at al bl
  split at al <;> split at bl <;> omega

theorem depth_le_clock_succ {s : ℤ} (hs : 2≤s) (c : Center s) : c.depth ≤ clock s c.x + 1 := by
  obtain ⟨w,_,_,hf⟩ := CenterTape.center_fiber hs c
  have S : atTime s c.x (clock s c.x) := by
    classical
    have h : ∃ t, atTime s c.x t := by obtain ⟨i,j,_,M,A,B⟩ := hf; exact ⟨_,i,j,rfl,M,A,B⟩
    simp only [clock,dite_eq_left h]; exact Nat.find_spec h
  obtain ⟨i,j,ij,M,A,B⟩ := S
  have bound (k : ℕ) : (path s c.x true k).1≤k+1 := by
    induction k with
    | zero => exact le_rfl
    | succ k ih => rw [show path s c.x true (k+1)=advance s c.x (path s c.x true k) from Function.iterate_succ_apply' ..]; unfold advance; split <;> omega
  have E := (meets_iff (by exact_mod_cast (show (1:ℤ)<s by omega) : (1:ℝ)<s) A B).mp M
  exact (count_at_meeting hs c E).trans ((bound i).trans (by omega))

#print axioms count_at_meeting
#print axioms depth_le_clock_succ
end BCMP430.DepthClock
