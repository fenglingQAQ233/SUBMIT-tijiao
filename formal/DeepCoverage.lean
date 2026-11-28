import DepthClock
import DigitBalance

namespace BCMP430.DeepCoverage
open Original Germ Witness Components UntunedTarget ComponentClock DepthClock Set Filter
open scoped Topology

private noncomputable def representative (J : Set ℝ) : ℝ := by
  classical
  exact if h : J.Nonempty then h.choose else 0
private theorem rep_mem {J : Set ℝ} (h : J.Nonempty) : representative J∈J := by simp only [representative,dite_eq_left h]; exact h.choose_spec

/-- A bounded, even constant, nonzero delay is allowed. Only the grid depths must
    escape any prescribed bound in each neighborhood. -/
theorem deep_accum {s : ℤ} (hs : 2≤s) {x : ℝ}
    (deep : ∀ ε > 0, ∀ N : ℕ, ∃ (c : Center s) (d : ℤ),
      dist c.x x < ε ∧ N<c.depth ∧ d≠0 ∧ c.x∈fiber s d) : Accum s x := by
  classical
  intro ε he old
  let f := fun J : Set ℝ => clock s (representative J)+1
  obtain ⟨c,d,near,large,nonzero,hf⟩ := deep ε he (old.sup f)
  have mem : c.x∈matching s := mem_iUnion.mpr ⟨d,hf⟩
  let J := connectedComponentIn (matching s) c.x
  have self : c.x∈J := mem_connectedComponentIn mem
  have op : IsOpen J := by
    apply isOpen_iff_mem_nhds.mpr; intro y hy
    have m := connectedComponentIn_subset _ _ hy
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp ((isOpen_iUnion (fiber_open hs)).mem_nhds m)
    apply Metric.mem_nhds_iff.mpr; refine ⟨r,hr,?_⟩
    dsimp only [J] at hy ⊢; rw [connectedComponentIn_eq hy]
    apply IsPreconnected.subset_connectedComponentIn _ (Metric.mem_ball_self hr) hball
    rw [Real.ball_eq_Ioo]; exact isPreconnected_Ioo
  refine ⟨c.x,d,near,nonzero,hf,op,component_index hs hf,?_⟩
  intro prev
  have L : f J ≤ old.sup f := Finset.le_sup prev
  have H := component_clock hs mem (rep_mem (J:=J) ⟨_,self⟩)
  have b := depth_le_clock_succ hs c
  change clock s (representative J)+1 ≤ _ at L
  omega

/-- A uniform *fixed* forbidden band, not all bands. This hypothesis allows bounded
    cumulative imbalance, on either side of zero. -/
theorem fixed_band_accum {s : ℤ} (hs : 2≤s) {x : ℝ} (hu : x∈UT s) (hp : 0<x)
    (ht : x<(s:ℝ)/(s+1)) (C : ℕ) (small : 2*(s:ℝ)⁻¹^C<x/(s:ℝ))
    (band : ∃ N : ℕ, ∀ e≥N, (2*(s-1)*(C:ℤ)+(s-1)) < |DigitBalance.balance s x e|) : Accum s x := by
  apply deep_accum hs
  intro ε he A
  obtain ⟨N,B⟩ := band
  let b := (s:ℝ)⁻¹
  have sr : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  have bp : 0<b := inv_pos.mpr (zero_lt_one.trans sr)
  have bl : b<1 := inv_lt_one_of_one_lt₀ sr
  obtain ⟨D,hD⟩ := exists_pow_lt_of_lt_one (half_pos he) bl
  let m := max (max A C) (max N D)
  let δ := min ((s:ℝ)/(s+1)-x) (x*b^(2*m+1))
  have δp : 0<δ := lt_min (sub_pos.mpr ht) (mul_pos hp (pow_pos bp _))
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one δp bl
  have h : b^(n+1)<δ := (pow_le_pow_of_le_one bp.le bl.le (Nat.le_succ n)).trans_lt hn
  obtain ⟨c,_,xc,_,near,far⟩ := GridProbes.nearest hs hu hp (n+1) (Nat.zero_lt_succ _) (by
    have H := h.trans_le (min_le_left ..); linarith only [H])
  let e := c.depth
  have deep : m<e := by
    apply lt_of_not_ge; intro H
    have L := pow_le_pow_of_le_one bp.le bl.le (show 2*e+1≤2*m+1 by omega)
    have R := h.trans_le (min_le_right ..)
    change x*b^(2*e+1)<b^(n+1) at far
    linarith only [mul_le_mul_of_nonneg_left L hp.le,far,R]
  have AC : max A C ≤ e := (le_max_left ..).trans deep.le
  have ND : max N D ≤ e := (le_max_right ..).trans deep.le
  have ec : C≤e := (le_max_right ..).trans AC
  have top : (s:ℝ)/(s+1)<1 := by apply (div_lt_one (by linarith : 0<(s:ℝ)+1)).mpr; linarith
  obtain ⟨w,hw,ew,wt⟩ := DigitBalance.tape_weight hs c.depthPred ⟨c.inside.1,c.inside.2.trans top⟩ c.onGrid c.offGrid
  change weight s (ClockTotal.padded w)=DigitBalance.balance s c.x e + (if e%2=0 then 0 else s-1) at wt
  have eq (i : ℕ) (hi : i≤e-C) : ⌊(s:ℝ)^i*c.x⌋=⌊(s:ℝ)^i*x⌋ :=
    DigitGuard.prefix_lock hs hu hp ht small (by rw [abs_of_pos (sub_pos.mpr xc)]; exact near) i (by omega)
  have diff := DigitBalance.compare hs ⟨c.inside.1.le,c.inside.2.trans top⟩ ⟨hp.le,ht.trans top⟩ (e-C) C eq
  rw [Nat.sub_add_cancel ec,abs_le] at diff
  have big := B e ((le_max_left ..).trans ND)
  have nz : weight s (ClockTotal.padded w) ≠ 0 := by
    intro z
    apply (not_le_of_gt big); apply abs_le.mpr
    by_cases ev : e%2=0 <;> simp only [ev,ite_true,ite_false] at wt <;> constructor <;> linarith only [diff.1,diff.2,z,wt,hs]
  have dn : indexFromDigits s (ClockTotal.padded w)≠0 := by
    unfold indexFromDigits
    by_cases L : weight s (ClockTotal.padded w)<0
    · have a := Int.mul_le_mul_of_nonneg_left (show weight s (ClockTotal.padded w)≤ -1 by omega) (show 0≤s+1 by omega); omega
    · have a := Int.mul_le_mul_of_nonneg_left (show 1≤weight s (ClockTotal.padded w) by omega) (show 0≤s+1 by omega); omega
  have clear : Tape.Clear s (Tape.val s w) (Tape.val s w) := by
    rw [ew]; intro j; by_cases zero : (g s)^[j+1] c.x=0
    · exact Or.inl zero
    right
    obtain ⟨l,hl⟩ := FirstDrop.iterate_lift s c.x c.depth
    obtain ⟨a,ha⟩ := c.onGrid; change (s:ℝ)^c.depth*c.x=(a:ℝ) at ha
    have endp : (g s)^[c.depth] c.x=0 := by
      have integral : ∃ z : ℤ, (g s)^[c.depth] c.x=z := by
        rcases Nat.even_or_odd c.depth with E|E
        · rw [E.neg_pow,ha] at hl; exact ⟨a-l,by push_cast; linarith only [hl]⟩
        · rw [E.neg_pow,neg_mul,ha] at hl; exact ⟨-a-l,by push_cast; linarith only [hl]⟩
      obtain ⟨z,hz⟩ := integral
      have U : (g s)^[c.depth] c.x ∈ Ico (0:ℝ) 1 := by change (g s)^[c.depthPred+1] c.x∈_; rw [Function.iterate_succ_apply']; exact ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
      rw [hz] at U ⊢; have l₁ : (0:ℤ)≤z := by exact_mod_cast U.1
      have l₂ : z<(1:ℤ) := by exact_mod_cast U.2
      exact_mod_cast (show z=0 by omega)
    by_cases past : c.depth≤j+1
    · have H : (g s)^[j+1] c.x=0 := by rw [show j+1=(j+1-c.depth)+c.depth by omega,Function.iterate_add_apply,endp]; exact Function.iterate_fixed (by simp [g]) _
      exact (zero H).elim
    · have rr : 0 ≤ (g s)^[j+1] c.x := by rw [Function.iterate_succ_apply']; exact Int.fract_nonneg _
      apply lt_of_le_of_ne (le_of_not_gt (fun H => c.avoid j ⟨lt_of_le_of_ne rr (Ne.symm zero),H⟩)); intro cyc
      have per (k : ℕ) : (g s)^[k*(j+1)] c.x=c.x := by induction k with
        | zero => simp
        | succ k ih => rw [Nat.succ_mul,Function.iterate_add_apply,←cyc,ih]
      have le : c.depth≤c.depth*(j+1) := by simpa using Nat.mul_le_mul_left c.depth (Nat.zero_lt_succ j)
      have end' := per c.depth
      nth_rewrite 1 [show c.depth*(j+1)=c.depth*(j+1)-c.depth+c.depth by omega] at end'
      rw [Function.iterate_add_apply,endp,Function.iterate_fixed (by simp [g] : g s 0=0)] at end'
      exact c.inside.1.ne end'
  obtain ⟨i,j,lag,H⟩ := WordWindow.window_of_word hs w hw clear
  have h₀ := Filter.Eventually.self_of_nhds H
  refine ⟨c,_,?_,(le_max_left A C).trans_lt ((le_max_left ..).trans_lt deep),dn,i,j,lag,ew ▸ h₀.1,ew ▸ h₀.2.1,ew ▸ h₀.2.2.1⟩
  rw [Real.dist_eq,abs_of_pos (sub_pos.mpr xc)]
  have pw := (pow_le_pow_of_le_one bp.le bl.le ((le_max_right N D).trans ND)).trans_lt hD
  change c.x-x≤2*b^e at near; linarith only [near,pw]

#print axioms deep_accum
#print axioms fixed_band_accum
end BCMP430.DeepCoverage
