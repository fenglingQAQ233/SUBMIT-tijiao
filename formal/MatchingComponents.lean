import MetricLocus

namespace BCMP430.Components
open Witness Germ MatchLag Stability Filter Set MetricLocus Adic
open scoped Topology

/-- Positive branch times are i+1 and j+1. Only times preceding the meeting
    must avoid the critical point (BCMP Definitions 1.1 and 1.6). -/
def fiber (s : ℤ) (d : ℤ) : Set ℝ := {x | ∃ i j : ℕ, (i:ℤ)-j=d ∧ Meets s x i j ∧
  (∀ k < i, (path s x true k).2 ≠ x) ∧ (∀ k < j, (path s x false k).2 ≠ x)}

def matching (s : ℤ) : Set ℝ := ⋃ d : ℤ, fiber s d

theorem fiber_open {s : ℤ} (hs : 2 ≤ s) (d : ℤ) : IsOpen (fiber s d) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨i,j,hij,hm,ha,hb⟩ := hx
  have hsr : (1:ℝ) < s := by exact_mod_cast (show 1<s by omega)
  filter_upwards [witness_neighborhood hsr ha hb hm] with y hy using ⟨i,j,hij,hy⟩

theorem fiber_unique {s d e : ℤ} (hs : 2≤s) {x : ℝ} (hd : x ∈ fiber s d) (he : x ∈ fiber s e) : d=e := by
  obtain ⟨i,j,hij,hm,ha,hb⟩ := hd
  obtain ⟨k,l,hkl,hn,hc,hh⟩ := he
  have hsr : (1:ℝ) < s := by exact_mod_cast (show 1<s by omega)
  exact hij.symm.trans ((lag_unique s x (seed s x true) (seed s x false)
    ((meets_iff hsr ha hb).mp hm) ((meets_iff hsr hc hh).mp hn)).trans hkl)

/-- Maximal connected components, not arbitrarily chosen smaller neighborhoods. -/
theorem component_index {s d : ℤ} (hs : 2≤s) {x : ℝ} (hx : x ∈ fiber s d) :
    connectedComponentIn (matching s) x ⊆ fiber s d := by
  let V := ⋃ j : {e : ℤ // e ≠ d}, fiber s j.val
  have hV : IsOpen V := isOpen_iUnion (fun j => fiber_open hs j.val)
  have dis : Disjoint (fiber s d) V := by
    apply Set.disjoint_left.mpr; intro y hy hy'
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hy'
    exact j.property (fiber_unique hs hj hy)
  have hmatch : x ∈ matching s := Set.mem_iUnion.mpr ⟨d,hx⟩
  apply IsPreconnected.subset_left_of_subset_union (fiber_open hs d) hV dis _
    ⟨x,mem_connectedComponentIn hmatch,hx⟩ isPreconnected_connectedComponentIn
  intro y hy
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (connectedComponentIn_subset _ _ hy)
  by_cases he : j=d
  · exact Or.inl (he ▸ hj)
  · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨j,he⟩,hj⟩)

/-- Any open interval contains a point on a positive-depth grid whose critical
    trajectories cannot hit the critical point again. -/
private theorem dense_grid {s : ℤ} (hs : 2≤s) (x : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃ y : ℝ, dist y x < ε ∧ ∀ r k, (path s y r k).2 ≠ y := by
  have hs1 : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  have spos : (0:ℝ)<s := lt_trans zero_lt_one hs1
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hs1)
  let P := (s:ℝ)^n
  have hP : 0<P := pow_pos spos _
  let z := ⌊P*x⌋
  let y : ℝ := ((z:ℝ)+(s:ℝ)⁻¹)/P
  have hyp : P*y=(z:ℝ)+(s:ℝ)⁻¹ := by dsimp only [y]; field_simp
  have hz₁ : (z:ℝ)≤P*x := Int.floor_le _
  have hz₂ : P*x<(z:ℝ)+1 := Int.lt_floor_add_one _
  have inv0 := inv_pos.mpr spos
  have inv1 := inv_lt_one_of_one_lt₀ hs1
  have dist1 : |y-x| < 1/P := by
    apply (lt_div_iff₀ hP).mpr
    rw [←abs_of_pos hP,←abs_mul,abs_lt]
    constructor <;> nlinarith only [hyp,hz₁,hz₂,inv0,inv1]
  refine ⟨y,?_,?_⟩
  · rw [Real.dist_eq]; apply dist1.trans; simpa [P,one_div,inv_pow] using hn
  · have hnum : (s:ℝ)^(n+1)*y = ((1+s*z:ℤ):ℝ) := by
      rw [pow_succ',mul_assoc,hyp,mul_add,mul_inv_cancel₀ spos.ne']; push_cast; ring
    have hcan : ¬s ∣ 1+s*z := by
      rw [Int.dvd_iff_emod_eq_zero,Int.add_mul_emod_self_left,Int.emod_eq_of_lt (by decide) (by omega : (1:ℤ)<s)]
      decide
    exact canonical_avoids hnum hcan

/-- Geometric local matching, even if its original witness did not record the
    prematching exclusion, gives a clean matching point in the very same neighborhood. -/
theorem rich_clean {s : ℤ} (hs : 2≤s) {x : ℝ} (h : Rich s x) (ε : ℝ) (he : 0<ε) (bad : Finset ℤ) :
    ∃ y d, dist y x < ε ∧ d≠0 ∧ d∉bad ∧ y∈fiber s d := by
  obtain ⟨z,d,hz,hd,hbad,i,j,lag,H⟩ := h (ε/2) (half_pos he) bad
  obtain ⟨δ,hδ,hU⟩ := Metric.eventually_nhds_iff.mp H
  obtain ⟨y,hy,avoid⟩ := dense_grid hs z (lt_min hδ (half_pos he))
  have hm := (hU (lt_of_lt_of_le hy (min_le_left ..))).1
  have hyd := lt_of_lt_of_le hy (min_le_right ..)
  exact ⟨y,d,lt_of_le_of_lt (dist_triangle y z x) (by linarith),hd,hbad,i,j,lag,hm,
    fun k _ => avoid true k,fun k _ => avoid false k⟩

/-- Select a label for each genuine component, only used when it contains a point. -/
noncomputable def label (s : ℤ) (J : Set ℝ) : ℤ := by
  classical
  exact if h : ∃ d : ℤ, J.Nonempty ∧ J ⊆ fiber s d then h.choose else 0

private theorem label_eq {s d : ℤ} (hs : 2≤s) {y : ℝ} (hy : y ∈ fiber s d) :
    label s (connectedComponentIn (matching s) y)=d := by
  let J := connectedComponentIn (matching s) y
  have self : y ∈ J := mem_connectedComponentIn (Set.mem_iUnion.mpr ⟨d,hy⟩)
  have h : ∃ e : ℤ, J.Nonempty ∧ J ⊆ fiber s e := ⟨d,⟨y,self⟩,component_index hs hy⟩
  change label s J=d
  unfold label; rw [dite_eq_left h]
  exact fiber_unique hs (h.choose_spec.2 self) hy

private theorem open_component_real {F : Set ℝ} (hF : IsOpen F) (x : ℝ) :
    IsOpen (connectedComponentIn F x) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hzF := connectedComponentIn_subset F x hz
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hF.mem_nhds hzF)
  apply Metric.mem_nhds_iff.mpr
  refine ⟨r,hr,?_⟩
  rw [connectedComponentIn_eq hz]
  apply IsPreconnected.subset_connectedComponentIn _ (Metric.mem_ball_self hr) hball
  rw [Real.ball_eq_Ioo]; exact isPreconnected_Ioo

/-- A fresh non-neutral maximal component in every neighborhood; previously
    supplied sets may be arbitrary, not necessarily correctly labelled components. -/
theorem accum_components {s : ℤ} (hs : 2≤s) {x : ℝ} (h : Rich s x) (ε : ℝ) (he : 0<ε)
    (old : Finset (Set ℝ)) : ∃ y d, dist y x < ε ∧ d≠0 ∧ y∈fiber s d ∧
      IsOpen (connectedComponentIn (matching s) y) ∧
      (connectedComponentIn (matching s) y ⊆ fiber s d) ∧ connectedComponentIn (matching s) y ∉ old := by
  classical
  obtain ⟨y,d,hy,hd,hfresh,hf⟩ := rich_clean hs h ε he (old.image (label s))
  refine ⟨y,d,hy,hd,hf,open_component_real (isOpen_iUnion (fiber_open hs)) y,component_index hs hf,?_⟩
  intro H; exact hfresh (Finset.mem_image.mpr ⟨_,H,label_eq hs hf⟩)

theorem accum_closure_roots {s : ℤ} (hs : 2≤s) {x : ℝ} (hx : x∈closure (roots s))
    (ε : ℝ) (he : 0<ε) (old : Finset (Set ℝ)) :
    ∃ y d, dist y x < ε ∧ d≠0 ∧ y∈fiber s d ∧
      IsOpen (connectedComponentIn (matching s) y) ∧
      (connectedComponentIn (matching s) y ⊆ fiber s d) ∧ connectedComponentIn (matching s) y ∉ old :=
  accum_components hs (rich_closure hs hx) ε he old

#print axioms component_index
#print axioms accum_closure_roots
end BCMP430.Components
