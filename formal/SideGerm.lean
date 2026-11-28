import MatchLag

namespace BCMP430.Germ
open Filter Original MatchLag
open scoped Topology

noncomputable def seed (s γ : ℝ) (right : Bool) : Mark :=
  if right then (1,1+s*(1-γ)) else (0,γ+1)
noncomputable def path (s γ : ℝ) (right : Bool) (n : ℕ) := (advance s γ)^[n] (seed s γ right)
def side (right : Bool) : Filter ℝ := if right then 𝓝[>] 0 else 𝓝[<] 0

private theorem side_zero (r : Bool) : Tendsto (fun t : ℝ => t) (side r) (𝓝 0) := by
  cases r <;> exact nhdsWithin_le_nhds

/-- The side limits are germs of iterates, not evaluations of Q at the critical point. -/
theorem local_affine (s γ : ℝ) (r : Bool) (n : ℕ)
    (avoid : ∀ j<n, (path s γ r j).2 ≠ γ) :
    ∀ᶠ t in side r, (Q s γ)^[n+1] (γ+t) =
      (path s γ r n).2 + (-s)^(path s γ r n).1*t := by
  induction n with
  | zero =>
    cases r with
    | false =>
      have hh : ∀ᶠ t : ℝ in 𝓝[<] 0, t < 0 := self_mem_nhdsWithin
      filter_upwards [hh] with t ht
      simp only [zero_add,Function.iterate_one,path,Function.iterate_zero_apply,seed,Bool.false_eq_true,ite_false,pow_zero,one_mul]
      rw [Q,ite_eq_left (by linarith : γ+t ≤ γ)]; ring
    | true =>
      have hh : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
      filter_upwards [hh] with t ht
      simp only [zero_add,Function.iterate_one,path,Function.iterate_zero_apply,seed,ite_true,pow_one]
      rw [Q,ite_eq_right (by linarith : ¬ γ+t ≤ γ)]; ring
  | succ n ih =>
    let z := path s γ r n
    let k := (-s)^z.1
    have hold := ih (fun j hj => avoid j (by omega))
    have ht : Tendsto (fun t : ℝ => z.2+k*t) (side r) (𝓝 z.2) := by
      simpa using (tendsto_const_nhds (x:=z.2)).add ((tendsto_const_nhds (x:=k)).mul (side_zero r))
    have hn : z.2 ≠ γ := avoid n (by omega)
    have hnext : path s γ r (n+1) = advance s γ z := Function.iterate_succ_apply' ..
    rcases lt_or_gt_of_ne hn with h|h
    · have near := ht.eventually_lt (tendsto_const_nhds (x:=γ)) h
      filter_upwards [hold,near] with t hval hnear
      rw [Function.iterate_succ_apply',hval,hnext]
      change Q s γ (z.2+k*t) = (advance s γ z).2 + (-s)^(advance s γ z).1*t
      simp only [advance,Q,ite_eq_left h.le,ite_eq_left hnear.le]; dsimp only [k]; ring
    · have near := (tendsto_const_nhds (x:=γ)).eventually_lt ht h
      filter_upwards [hold,near] with t hval hnear
      rw [Function.iterate_succ_apply',hval,hnext]
      change Q s γ (z.2+k*t) = (advance s γ z).2 + (-s)^(advance s γ z).1*t
      simp only [advance,Q,ite_eq_right (not_le.mpr h),ite_eq_right (not_le.mpr hnear),pow_succ]; dsimp only [k]; ring

/-- Value and slope limits, both computed relative to the side's own limiting value. -/
theorem value_and_slope (s γ : ℝ) (r : Bool) (n : ℕ)
    (avoid : ∀ j<n, (path s γ r j).2 ≠ γ) :
    let z := path s γ r n
    Tendsto (fun t : ℝ => (Q s γ)^[n+1] (γ+t)) (side r) (𝓝 z.2) ∧
    Tendsto (fun t : ℝ => ((Q s γ)^[n+1] (γ+t)-z.2)/t) (side r) (𝓝 ((-s)^z.1)) := by
  let z := path s γ r n
  have germ := local_affine s γ r n avoid
  have nz : ∀ᶠ t in side r, t ≠ 0 := by
    cases r with
    | true =>
      have hp : ∀ᶠ t : ℝ in 𝓝[>] 0, 0<t := self_mem_nhdsWithin
      filter_upwards [hp] with t ht using ne_of_gt ht
    | false =>
      have hn : ∀ᶠ t : ℝ in 𝓝[<] 0, t<0 := self_mem_nhdsWithin
      filter_upwards [hn] with t ht using ne_of_lt ht
  constructor
  · have he : (fun t : ℝ => z.2 + (-s)^z.1*t) =ᶠ[side r] (fun t => (Q s γ)^[n+1] (γ+t)) := by
      filter_upwards [germ] with t ht using ht.symm
    apply Tendsto.congr' he
    simpa using (tendsto_const_nhds (x:=z.2)).add ((tendsto_const_nhds (x:=(-s)^z.1)).mul (side_zero r))
  · apply Tendsto.congr' _ (tendsto_const_nhds (x:=(-s)^z.1))
    filter_upwards [germ,nz] with t he hne
    rw [he]; dsimp only [z]; field_simp; ring

#print axioms local_affine
#print axioms value_and_slope
end BCMP430.Germ
