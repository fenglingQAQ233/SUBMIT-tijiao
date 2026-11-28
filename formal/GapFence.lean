import GapGrid

namespace BCMP430.GapFence
open Set Original UntunedTarget Filter
open scoped Topology

/-- An open gap with a dense-from-P right endpoint cannot extend beyond the
    two inverse branches. The candidates depend continuously on the endpoint. -/
theorem fence {s : ℤ} (hs : 2≤s) (c : Center s) {a b : ℝ} (hc : c.x∈Ioo a b)
    (br : c.R≤b) {P : Set ℝ} (near : b∈closure P) (empty : ∀ y∈Ioo a b, y∉P)
    (right : ∀ v∈P, ∀ y∈Ioo a b, y=c.x+(s:ℝ)⁻¹^c.p*v → y<v → y∈P)
    (left : ∀ v∈P, ∀ y∈Ioo a b, y=c.x-(s:ℝ)⁻¹^c.q*v → y<v → y∈P) : b=c.R ∧ c.T≤a := by
  have sr : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  have bp : 0<(s:ℝ)⁻¹ := inv_pos.mpr (zero_lt_one.trans sr)
  let u := (s:ℝ)⁻¹^c.p
  let w := (s:ℝ)⁻¹^c.q
  have pos : 0<u := pow_pos bp _
  have den : 0<1-u := sub_pos.mpr (pow_lt_one₀ bp.le (inv_lt_one_of_one_lt₀ sr) (by dsimp [Center.p,Center.depth]; omega : c.p≠0))
  have rid : c.R*(1-u)=c.x := div_mul_cancel₀ _ den.ne'
  have bp' : 0<b := c.inside.1.trans hc.2
  have exclude (f : ℝ → ℝ) (cf : Continuous f) (fb : f b ∈ Ioo a b)
      (make : ∀ v∈P, f v∈Ioo a b → f v<v → f v∈P) : False := by
    have lim : Tendsto f (𝓝 b) (𝓝 (f b)) := cf.continuousAt
    have U := lim.eventually (isOpen_Ioo.mem_nhds fb)
    have V := lim.eventually_lt (tendsto_id (x:=𝓝 b)) fb.2
    have F := mem_closure_iff_frequently.mp near
    obtain ⟨v,hv,hI,lt⟩ := (F.and_eventually (U.and V)).exists
    exact empty _ hI (make v hv hI lt)
  have B : b=c.R := by
    apply le_antisymm _ br; apply le_of_not_gt; intro lt
    have l : a<c.x+u*b := by linarith only [hc.1,mul_pos pos bp']
    have r : c.x+u*b<b := by nlinarith only [rid,mul_pos den (sub_pos.mpr lt)]
    exact exclude (fun v=>c.x+u*v) (by fun_prop) ⟨l,r⟩ (fun v hv hI hlt => right v hv _ hI rfl hlt)
  refine ⟨B,le_of_not_gt (fun bad => ?_)⟩
  have lo : a<c.x-w*b := by rw [B]; exact bad
  have hi : c.x-w*b<b := by linarith only [hc.2,mul_pos (pow_pos bp c.q) bp']
  exact exclude (fun v=>c.x-w*v) (by fun_prop) ⟨lo,hi⟩ (fun v hv hI hlt => left v hv _ hI rfl hlt)

#print axioms fence
end BCMP430.GapFence
