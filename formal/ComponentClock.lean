import CenterTape

namespace BCMP430.ComponentClock
open Original Germ MatchLag Witness Components UntunedTarget Adic Set Filter Stability
open scoped Topology

/-- Total time after the side-specific first steps, minimized only over clean meetings. -/
def atTime (s : ℤ) (x : ℝ) (t : ℕ) : Prop := ∃ i j : ℕ, i+j=t ∧ Meets s x i j ∧
    (∀ k < i, (path s x true k).2≠x) ∧ (∀ k < j, (path s x false k).2≠x)

private theorem exists_iff (s : ℤ) (x : ℝ) : (∃ t, atTime s x t) ↔ x∈matching s := by
  constructor
  · rintro ⟨_,i,j,_,H⟩; exact mem_iUnion.mpr ⟨(i:ℤ)-j,i,j,rfl,H⟩
  · intro h; obtain ⟨_,i,j,_,H⟩ := mem_iUnion.mp h; exact ⟨i+j,i,j,rfl,H⟩

noncomputable def clock (s : ℤ) (x : ℝ) : ℕ := by
  classical
  exact if h : ∃ t, atTime s x t then Nat.find h else 0

private theorem spec {s : ℤ} {x : ℝ} (hx : x∈matching s) : atTime s x (clock s x) := by
  have H := (exists_iff s x).mpr hx
  classical
  simp only [clock,dite_eq_left H]; exact Nat.find_spec H

private theorem minimal {s : ℤ} {x : ℝ} {k : ℕ} (h : atTime s x k) : clock s x ≤ k := by
  classical
  have ex : ∃ t, atTime s x t := ⟨_,h⟩
  simp only [clock,dite_eq_left ex]; exact Nat.find_min' ex h

private theorem clean_local {s : ℤ} (hs : 2≤s) {x : ℝ} {i j : ℕ}
    (ha : ∀ k < i, (path s x true k).2≠x) (hb : ∀ k < j, (path s x false k).2≠x) :
    ∀ᶠ y in 𝓝 x, Meets s y i j ↔ Meets s x i j := by
  have sp : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  filter_upwards [finite_itinerary s x true i ha,finite_itinerary s x false j hb] with y A B
  rw [meets_iff sp A.2 B.2,meets_iff sp ha hb,A.1,B.1]
  constructor
  · intro h
    have e := congrArg Prod.fst h
    change (path s x true i).1=(path s x false j).1 at e
    have v := congrArg Prod.snd h
    change (path s x true i).2+_ = (path s x false j).2+_ at v
    simp only [e] at v
    exact Prod.ext e (add_right_cancel v)
  · exact congrArg _

/-- The least sum of clean meeting times is locally constant, not only their difference.
    A shorter competing pair must lie in the same time rectangle since the delay is unique. -/
theorem clock_local {s : ℤ} (hs : 2≤s) {x : ℝ} (hx : x∈matching s) :
    ∀ᶠ y in 𝓝 x, y∈matching s ∧ clock s y=clock s x := by
  obtain ⟨i,j,ij,H,ha,hb⟩ := spec hx
  have sp : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  have allp : ∀ᶠ y in 𝓝 x, ∀ u ≤ i, ∀ v ≤ j, Meets s y u v ↔ Meets s x u v := by
    apply (Filter.eventually_all_finite (I:=Set.Iic i) (Set.finite_Iic i)).mpr
    intro u hu; apply (Filter.eventually_all_finite (I:=Set.Iic j) (Set.finite_Iic j)).mpr
    intro v hv; exact clean_local hs (fun k hk => ha k (lt_of_lt_of_le hk hu)) (fun k hk => hb k (lt_of_lt_of_le hk hv))
  filter_upwards [witness_neighborhood sp ha hb H,allp] with y h p
  have A : atTime s y (i+j) := ⟨i,j,rfl,h⟩
  have mem := (exists_iff s y).mp ⟨_,A⟩
  have le := minimal A
  obtain ⟨u,v,uv,M,aa,bb⟩ := spec mem
  have d := fiber_unique hs (d:=(u:ℤ)-v) (e:=(i:ℤ)-j) (x:=y) ⟨u,v,rfl,M,aa,bb⟩ ⟨i,j,rfl,h⟩
  have ui : u ≤ i := by omega
  have vj : v ≤ j := by omega
  have B : atTime s x (u+v) := ⟨u,v,rfl,(p u ui v vj).mp M,fun k hk => ha k (lt_of_lt_of_le hk ui),fun k hk => hb k (lt_of_lt_of_le hk vj)⟩
  exact ⟨mem,by have l := minimal B; omega⟩

theorem component_clock {s : ℤ} (hs : 2≤s) {x y : ℝ} (hx : x∈matching s)
    (hy : y∈connectedComponentIn (matching s) x) : clock s y=clock s x := by
  let U := {z | z∈matching s ∧ clock s z=clock s x}
  let V := {z | z∈matching s ∧ clock s z≠clock s x}
  have opU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr; intro z hz
    filter_upwards [clock_local hs hz.1] with w H using ⟨H.1,H.2.trans hz.2⟩
  have opV : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr; intro z hz
    filter_upwards [clock_local hs hz.1] with w H using ⟨H.1,fun eq => hz.2 (H.2.symm.trans eq)⟩
  have sub : connectedComponentIn (matching s) x ⊆ U := by
    apply IsPreconnected.subset_left_of_subset_union opU opV (Set.disjoint_left.mpr (fun _ hu hv => hv.2 hu.2)) _ ⟨x,mem_connectedComponentIn hx,hx,rfl⟩ isPreconnected_connectedComponentIn
    intro z hz; have m := connectedComponentIn_subset _ _ hz
    by_cases e : clock s z=clock s x
    · exact Or.inl ⟨m,e⟩
    · exact Or.inr ⟨m,e⟩
  exact (sub hy).2

#print axioms component_clock
end BCMP430.ComponentClock
