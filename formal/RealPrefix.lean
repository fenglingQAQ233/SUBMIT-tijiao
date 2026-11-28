import StreamDictionary
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace BCMP430.RealPrefix
open Streams Filter
open scoped Topology BigOperators

abbrev Valid (s : ℤ) (a : Digits) := ∀ i, 0 ≤ a i ∧ a i < s

noncomputable def term (s : ℤ) (a : Digits) (i : ℕ) : ℝ :=
  (a i : ℝ) * (s : ℝ)⁻¹ * (s : ℝ)⁻¹^i
noncomputable def value (s : ℤ) (a : Digits) : ℝ := ∑' i, term s a i

private theorem bounds_term {s : ℤ} {a : Digits} (hs : 2 ≤ s) (ha : Valid s a) (i : ℕ) :
    0 ≤ term s a i ∧ term s a i ≤ (1-(s : ℝ)⁻¹)*(s : ℝ)⁻¹^i := by
  have spos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have h := ha i
  have hlo : (0 : ℝ) ≤ a i := by exact_mod_cast h.1
  have hhi : (a i : ℝ) ≤ s-1 := by exact_mod_cast (show a i ≤ s-1 by omega)
  have z : (s : ℝ)*(s : ℝ)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt spos)
  unfold term
  constructor
  · positivity
  · apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hh := mul_le_mul_of_nonneg_right hhi (inv_nonneg.mpr spos.le)
    rw [sub_mul, one_mul, z] at hh
    exact hh

private theorem sum_info {s : ℤ} {a : Digits} (hs : 2 ≤ s) (ha : Valid s a) :
    Summable (term s a) ∧ 0 ≤ value s a ∧ value s a ≤ 1 := by
  have hsr : (1 : ℝ) < s := by exact_mod_cast (show 1 < s by omega)
  have hr := inv_lt_one_of_one_lt₀ hsr
  have hpos : 0 ≤ (s : ℝ)⁻¹ := by positivity
  have geo := summable_geometric_of_lt_one hpos hr
  have major := geo.mul_left (1-(s : ℝ)⁻¹)
  have su := Summable.of_nonneg_of_le (fun i => (bounds_term hs ha i).1) (fun i => (bounds_term hs ha i).2) major
  refine ⟨su,tsum_nonneg (fun i => (bounds_term hs ha i).1),?_⟩
  unfold value
  calc
    _ ≤ ∑' i : ℕ, (1-(s : ℝ)⁻¹)*(s : ℝ)⁻¹^i := su.tsum_le_tsum (fun i => (bounds_term hs ha i).2) major
    _ = 1 := by rw [tsum_mul_left,tsum_geometric_of_lt_one hpos hr,mul_inv_cancel₀ (by linarith)]

private theorem decompose {s : ℤ} {a : Digits} (hs : 2 ≤ s) (ha : Valid s a) (m : ℕ) :
    value s a = (∑ i ∈ Finset.range m, term s a i) + (s : ℝ)⁻¹^m * value s (fun i => a (i+m)) := by
  have hseries := (sum_info hs ha).1.sum_add_tsum_nat_add m
  change (∑' i, term s a i) =
    (∑ i ∈ Finset.range m, term s a i) + (s : ℝ)⁻¹^m * value s (fun i => a (i+m))
  rw [← hseries]
  congr 1
  unfold value
  rw [← tsum_mul_left]
  apply tsum_congr
  intro i
  simp only [term,pow_add]
  ring

theorem prefix_distance {s : ℤ} {a b : Digits} (hs : 2 ≤ s) (ha : Valid s a) (hb : Valid s b)
    (m : ℕ) (h : BeforeEq a b m) : |value s a-value s b| ≤ (s : ℝ)⁻¹^m := by
  have heq : (∑ i ∈ Finset.range m, term s a i) = ∑ i ∈ Finset.range m, term s b i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [term,h i (Finset.mem_range.mp hi)]
  have va := (sum_info hs (a := fun i => a (i+m)) (fun i => ha (i+m))).2
  have vb := (sum_info hs (a := fun i => b (i+m)) (fun i => hb (i+m))).2
  rw [decompose hs ha m, decompose hs hb m, heq, add_sub_add_left_eq_sub, ← mul_sub, abs_mul]
  have spos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hm : 0 ≤ (s : ℝ)⁻¹^m := by positivity
  rw [abs_of_nonneg hm]
  calc
    _ ≤ (s : ℝ)⁻¹^m * 1 := by apply mul_le_mul_of_nonneg_left _ hm; apply abs_sub_le_iff.mpr; constructor <;> linarith [va.1,va.2,vb.1,vb.2]
    _ = _ := mul_one _

theorem prefix_tendsto {s : ℤ} (hs : 2 ≤ s) {a : Digits} {seq : ℕ → Digits}
    (ha : Valid s a) (hv : ∀ j, Valid s (seq j))
    (h : ∀ m, ∃ J, ∀ j ≥ J, BeforeEq (seq j) a m) :
    Tendsto (fun j => value s (seq j)) atTop (𝓝 (value s a)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hsr : (1 : ℝ) < s := by exact_mod_cast (show 1 < s by omega)
  obtain ⟨m,hm⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hsr)
  obtain ⟨J,hJ⟩ := h m
  exact ⟨J,fun j hj => by simpa only [Real.dist_eq] using (prefix_distance hs (hv j) ha m (hJ j hj)).trans_lt hm⟩

#print axioms prefix_distance
#print axioms prefix_tendsto
end BCMP430.RealPrefix
