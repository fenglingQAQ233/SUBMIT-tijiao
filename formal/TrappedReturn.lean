import SurvivorWindow
import PrefixCoverage

namespace BCMP430.TrappedReturn
open Original Adic UntunedTarget Set SurvivorWindow

private theorem unit {s : ℤ} (x : ℝ) {n : ℕ} (pn : 0<n) : (g s)^[n] x∈Ico (0:ℝ) 1 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero pn.ne'; rw [Function.iterate_succ_apply']; exact ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩

/-- Iterate by q on the left or p on the right. In the strict tuning interior
    this returns below R even if an intermediate iterate lies above R. -/
theorem return_below {s : ℤ} (hs : 2≤s) (c : Center s) {y : ℝ} (H : y∈Ioo c.T c.R) :
    ∃ k : ℕ, 0<k ∧ (g s)^[k] y<c.R := by
  have sp : (0:ℝ)<s := by exact_mod_cast (show 0<s by omega)
  by_cases left : y≤c.x
  · have id := odd_branch hs c ⟨H.1.le,left⟩
    have e : (s:ℝ)^c.q*(c.x-c.T)=c.R := by
      change (s:ℝ)^c.q*(c.x-(c.x-(s:ℝ)⁻¹^c.q*c.R))=_
      rw [sub_sub_cancel,←mul_assoc,inv_pow,mul_inv_cancel₀ (pow_pos sp _).ne',one_mul]
    exact ⟨c.q,by dsimp [Center.q,Center.depth]; omega,by linarith only [e,id,mul_lt_mul_of_pos_left (sub_lt_sub_left H.1 c.x) (pow_pos sp c.q)]⟩
  · have u := endpoint_order hs c
    obtain ⟨k,hk,drop⟩ := gap_drop hs c ⟨u.2.1.trans (lt_of_not_ge left),H.2⟩
    exact ⟨k,hk,drop.trans H.2⟩

/-- An orbit-minimal parameter in an open tuning window makes arbitrarily late
    returns strictly below that window's right endpoint. -/
theorem trapped {s : ℤ} (hs : 2≤s) (c : Center s) {x : ℝ} (inc : x∈Ioo c.T c.R)
    (surv : ∀ i : ℕ, x≤(g s)^[i] x) (N : ℕ) : ∃ j ≥ N, (g s)^[j] x<c.R := by
  induction N with
  | zero => exact ⟨0,le_rfl,inc.2⟩
  | succ N ih =>
    obtain ⟨j,le,small⟩ := ih
    obtain ⟨k,pos,drop⟩ := return_below hs c ⟨inc.1.trans_le (surv j),small⟩
    exact ⟨k+j,by omega,by rwa [Function.iterate_add_apply]⟩

/-- No positive center can have R above the maximal fixed point.  The center
    numerator at depth p is integral, and (s^p-1)/(s+1) is integral for even p. -/
theorem right_le_top {s : ℤ} (hs : 2≤s) (c : Center s) : c.R ≤ (s:ℝ)/(s+1) := by
  have sr : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  have sp := zero_lt_one.trans sr
  have pp : 0<c.p := by dsimp [Center.p,Center.depth]; omega
  have par : Even c.p := Nat.even_iff.mpr (by dsimp [Center.p]; omega)
  have dvd : s+1 ∣ s^c.p-1 := by
    have h := sub_dvd_pow_sub_pow s (-(1:ℤ)) c.p
    have eq : (-(1:ℤ))^c.p=1 := by rw [par.neg_pow,one_pow]
    simpa only [eq,sub_neg_eq_add] using h
  obtain ⟨v,hv⟩ := dvd
  have lv : c.depth≤c.p := by dsimp [Center.p]; omega
  obtain ⟨a,ha⟩ := c.onGrid; change (s:ℝ)^c.depth*c.x=(a:ℝ) at ha
  let A : ℤ := s^(c.p-c.depth)*a
  have grid : (s:ℝ)^c.p*c.x=(A:ℝ) := by
    nth_rewrite 1 [show c.p=c.p-c.depth+c.depth by omega]; rw [pow_add,mul_assoc,ha]; dsimp [A]; push_cast; rfl
  have hv' : (s:ℝ)^c.p-1=((s:ℝ)+1)*v := by exact_mod_cast hv
  have co := (lt_div_iff₀ (by linarith : 0<(s:ℝ)+1)).mp c.inside.2
  have H : (A:ℝ)*((s:ℝ)+1)<(s:ℝ)^c.p*s := by rw [←grid]; nlinarith only [mul_lt_mul_of_pos_left co (pow_pos sp c.p)]
  have Hz : A*(s+1)<(s^c.p)*s := by exact_mod_cast H
  have amax : A≤s*v := by
    apply le_of_not_gt
    intro bad
    have ll := Int.mul_le_mul_of_nonneg_right (show s*v+1≤A by omega) (show 0≤s+1 by omega)
    have mul := congrArg (fun z : ℤ => z*s) hv
    change (s^c.p-1)*s=((s+1)*v)*s at mul
    linarith only [mul,ll,Hz]
  have lim : (A:ℝ) ≤ s*v := by exact_mod_cast amax
  have inv : (s:ℝ)^c.p*(s:ℝ)⁻¹^c.p=1 := by rw [inv_pow,mul_inv_cancel₀ (pow_pos sp _).ne']
  have denom : 0<1-(s:ℝ)⁻¹^c.p := sub_pos.mpr (pow_lt_one₀ (inv_nonneg.mpr sp.le) (inv_lt_one_of_one_lt₀ sr) pp.ne')
  have lim' : (A:ℝ)*((s:ℝ)+1)≤(s:ℝ)*((s:ℝ)^c.p-1) := by rw [hv']; nlinarith only [mul_le_mul_of_nonneg_right lim (show 0≤(s:ℝ)+1 by linarith)]
  apply (div_le_div_iff₀ denom (show 0<(s:ℝ)+1 by linarith)).mpr
  apply (mul_le_mul_iff_of_pos_left (pow_pos sp c.p)).mp
  nlinarith only [grid,lim',congrArg (fun z : ℝ => z*((s:ℝ)+1)) grid,congrArg (fun z : ℝ => z*(s:ℝ)) inv]

theorem eventual_top_untuned {s : ℤ} (hs : 2≤s) {x : ℝ} (dom : x∈Icc 0 ((s:ℝ)/(s+1)))
    (surv : ∀ i : ℕ, x≤(g s)^[i] x) {N : ℕ} (hit : (g s)^[N] x=(s:ℝ)/(s+1)) : x∈UT s := by
  let h := (s:ℝ)/(s+1)
  have sp : (0:ℝ)<s := by exact_mod_cast (show 0<s by omega)
  have e : h*((s:ℝ)+1)=s := div_mul_cancel₀ _ (by linarith)
  have fix : g s h=h := Int.fract_eq_iff.mpr ⟨(div_pos sp (by linarith)).le,(div_lt_one (by linarith : 0<(s:ℝ)+1)).mpr (by linarith),-s,by push_cast; linarith only [e]⟩
  refine ⟨dom,?_⟩; intro c inc
  obtain ⟨j,jn,low⟩ := trapped hs c inc surv N
  rw [show j=(j-N)+N by omega,Function.iterate_add_apply,hit,Function.iterate_fixed fix] at low
  exact (not_lt_of_ge (right_le_top hs c)) low

#print axioms trapped
#print axioms right_le_top
#print axioms eventual_top_untuned
end BCMP430.TrappedReturn
