import MatchingComponents
import OriginAccum

namespace BCMP430.UntunedTarget
open Set Original Adic MetricLocus Components Filter
open scoped Topology

/-- n+1 is the least base-s grid level, not the reduced rational denominator. -/
structure Center (s : ℤ) where
  x : ℝ
  depthPred : ℕ
  inside : x ∈ Ioo 0 ((s:ℝ)/(s+1))
  onGrid : GridAt s (depthPred+1) x
  offGrid : ¬GridAt s depthPred x
  avoid : ∀ k : ℕ, (g s)^[k+1] x ∉ Ioo 0 x

def Center.depth {s : ℤ} (c : Center s) := c.depthPred+1
def Center.p {s : ℤ} (c : Center s) := c.depth + c.depth%2
def Center.q {s : ℤ} (c : Center s) := c.depth + (c.depth+1)%2
noncomputable def Center.R {s : ℤ} (c : Center s) := c.x/(1-(s:ℝ)⁻¹^c.p)
noncomputable def Center.L {s : ℤ} (c : Center s) := c.x/(1+(s:ℝ)⁻¹^c.q)
noncomputable def Center.T {s : ℤ} (c : Center s) := c.x-(s:ℝ)⁻¹^c.q*c.R

/-- BCMP 4.19 and 4.30, using the orbit characterization of pseudocenters (4.12).
    T is the tuning endpoint; L is NOT the endpoint used in taking the complement. -/
def UT (s : ℤ) : Set ℝ := {x | x ∈ Icc 0 ((s:ℝ)/(s+1)) ∧ ∀ c : Center s, x ∉ Ioo c.T c.R}

/-- The complement word of the odd expansion of 1-x has finite value x-s^(-q).
    Its periodic continuation for the tuning endpoint is the complement of R. -/
theorem tuning_formula {s : ℤ} (c : Center s) :
    (c.x-(s:ℝ)⁻¹^c.q)+(s:ℝ)⁻¹^c.q*(1-c.R)=c.T := by unfold Center.T; ring

theorem endpoint_order {s : ℤ} (hs : 2≤s) (c : Center s) : c.T<c.L ∧ c.L<c.x ∧ c.x<c.R := by
  have h1 : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  let u := (s:ℝ)⁻¹^c.p
  let v := (s:ℝ)⁻¹^c.q
  have su : 0<u := pow_pos (inv_pos.mpr (zero_lt_one.trans h1)) _
  have sv : 0<v := pow_pos (inv_pos.mpr (zero_lt_one.trans h1)) _
  have np : c.p≠0 := by dsimp [Center.p,Center.depth]; omega
  have lu : u<1 := pow_lt_one₀ (inv_nonneg.mpr (zero_lt_one.trans h1).le) (inv_lt_one_of_one_lt₀ h1) np
  have cx := c.inside.1
  have rr : c.R*(1-u)=c.x := div_mul_cancel₀ _ (by linarith)
  have ll : c.L*(1+v)=c.x := div_mul_cancel₀ _ (by linarith)
  have lp : 0<c.L := div_pos cx (by change 0<1+v; linarith)
  have rp : 0<c.R := div_pos cx (by change 0<1-u; linarith)
  have lc : c.L<c.x := by nlinarith [mul_pos lp sv]
  have cr : c.x<c.R := by nlinarith [mul_pos rp su]
  refine ⟨?_,lc,cr⟩
  change c.x-v*c.R < c.L
  nlinarith [mul_lt_mul_of_pos_left (lc.trans cr) sv]

theorem origin_rich {s : ℤ} (hs : 2≤s) : Rich s 0 := by
  intro ε he bad
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (Origin.centers_tendsto hs) ε he
  let d := fun j : ℕ => Origin.lag s (N+j)
  have inj : Function.Injective d := fun i j hij => by
    have h := (Origin.increasing hs).injective hij
    omega
  have outside : ∃ j, d j ∉ insert 0 bad := by
    by_contra! h
    exact (Set.infinite_range_of_injective inj) ((insert 0 bad).finite_toSet.subset (by rintro z ⟨j,rfl⟩; exact h j))
  obtain ⟨j,hj⟩ := outside
  exact ⟨_,d j,hN (N+j) (by omega),fun h => hj (Finset.mem_insert.mpr (Or.inl h)),
    fun h => hj (Finset.mem_insert.mpr (Or.inr h)),Origin.local_matching hs (N+j)⟩

def Accum (s : ℤ) (x : ℝ) := ∀ ε > 0, ∀ old : Finset (Set ℝ), ∃ y d,
  dist y x < ε ∧ d≠0 ∧ y∈fiber s d ∧ IsOpen (connectedComponentIn (matching s) y) ∧
  (connectedComponentIn (matching s) y ⊆ fiber s d) ∧ connectedComponentIn (matching s) y ∉ old

def FullTarget (s : ℤ) := ∀ x ∈ UT s, x ≠ (s:ℝ)/(s+1) → Accum s x

theorem origin_components {s : ℤ} (hs : 2≤s) : Accum s 0 := accum_components hs (origin_rich hs)

/-- The inclusion is a remaining obligation, not an axiom or a conclusion of this theorem. -/
theorem reduction {s : ℤ} (hs : 2≤s)
    (cover : ∀ x ∈ UT s, 0<x → x<(s:ℝ)/(s+1) → x∈closure (roots s)) : FullTarget s := by
  intro x hx ne
  rcases eq_or_lt_of_le hx.1.1 with e|h
  · subst x; exact origin_components hs
  · exact accum_closure_roots hs (cover x hx h (lt_of_le_of_ne hx.1.2 ne))

#print axioms endpoint_order
#print axioms origin_components
#print axioms reduction
end BCMP430.UntunedTarget
