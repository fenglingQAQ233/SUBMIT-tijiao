import ClockTotal

namespace BCMP430.Tape
open Clock Original ClockTotal

/-- A canonical terminating base-s expansion is read from most to least significant. -/
noncomputable def consDigit (s a : ℤ) (v : ℝ) := ((a:ℝ)+v)/(s:ℝ)
noncomputable def val (s : ℤ) : Word → ℝ
  | .one a => consDigit s a 0
  | .two a b => consDigit s a (consDigit s b 0)
  | .more a b t => consDigit s a (consDigit s b (val s t))

def program (s : ℤ) : Word → List (ℤ × ℤ)
  | .one a => [(1,s+1-a),(1,s+1)]
  | .two a b => [(0,s-a),(1,1+b),(1,s+1)]
  | .more a b t => (0,s-a)::(0,1+b)::program s t

/-- The trace carries the *actual* base-map residues and the gate for the moving cutoff. -/
def Follows (s : ℤ) (γ : ℝ) : List (ℤ × ℤ) → ℝ → ℝ → Prop
  | [], r, z => r=z
  | (m,b)::ops, r,z => gate γ (g s r)=m ∧ level s r=b ∧ Follows s γ ops (g s r) z

private theorem digit_bounds {s a : ℤ} {x : ℝ} (hs : 2 ≤ s) (ha' : a < s)
    (hx' : x < 1) (hp : 0 < (a:ℝ)+x) :
    0 < consDigit s a x ∧ consDigit s a x < 1 := by
  have s0 : (0:ℝ) < s := by exact_mod_cast (show 0<s by omega)
  have h : (a:ℝ)+1 ≤ s := by exact_mod_cast (show a+1≤s by omega)
  exact ⟨div_pos hp s0,(div_lt_one s0).mpr (by linarith)⟩

private theorem prep {s a : ℤ} {x : ℝ} (hs : 2 ≤ s) (ha : 0 ≤ a) (ha' : a < s)
    (hx : 0<x) (hx' : x<1) : 0 < consDigit s a x ∧ consDigit s a x < 1 :=
  digit_bounds hs ha' hx' (add_pos_of_nonneg_of_pos (by exact_mod_cast ha) hx)

private theorem last {s a : ℤ} (hs : 2 ≤ s) (ha : 0<a) (ha' : a<s) :
    0 < consDigit s a 0 ∧ consDigit s a 0 < 1 :=
  digit_bounds hs ha' zero_lt_one (by simpa using (show (0:ℝ)<a by exact_mod_cast ha))

theorem in_unit {s : ℤ} (hs : 2 ≤ s) (w : Word) (hw : Good s w) : 0 < val s w ∧ val s w < 1 := by
  induction w with
  | one a => exact last hs hw.1 hw.2
  | two a b => obtain ⟨a0,as',b0,bs⟩ := hw; obtain ⟨hl,hh⟩ := last hs b0 bs; exact prep hs a0 as' hl hh
  | more a b t ih =>
    obtain ⟨a0,as',b0,bs,h⟩ := hw
    obtain ⟨ht,ht'⟩ := ih h
    obtain ⟨hl,hh⟩ := prep hs b0 bs ht ht'
    exact prep hs a0 as' hl hh

private theorem identify {s : ℤ} {r u : ℝ} {b : ℤ}
    (hb : 1+(s:ℝ)*(1-r) = (b:ℝ)+u) (h0 : 0≤u) (h1 : u<1) :
    level s r=b ∧ g s r=u := by
  have hl : level s r=b := by apply Int.floor_eq_iff.mpr; rw [hb]; exact ⟨by linarith,by linarith⟩
  refine ⟨hl,?_⟩
  unfold g
  apply Int.fract_eq_iff.mpr
  refine ⟨h0,h1,b-1-s,?_⟩
  push_cast; linarith only [hb]

private theorem mul_cons {s : ℤ} (hs : 2 ≤ s) (a : ℤ) (t : ℝ) :
    (s:ℝ)*consDigit s a t = a+t := by
  have h : (s:ℝ)≠0 := by exact_mod_cast (show s≠0 by omega)
  unfold consDigit
  field_simp

private theorem front {s a : ℤ} {v : ℝ} (hs : 2≤s) (h0 : 0<v) (h1 : v<1) :
    level s (consDigit s a v)=s-a ∧ g s (consDigit s a v)=1-v := by
  apply identify _ (by linarith) (by linarith)
  rw [Int.cast_sub,mul_sub,mul_one,mul_cons hs]; ring

private theorem back {s b : ℤ} {v : ℝ} (hs : 2≤s) (h0 : 0≤v) (h1 : v<1) :
    level s (1-consDigit s b v)=1+b ∧ g s (1-consDigit s b v)=v := by
  apply identify _ h0 h1
  rw [sub_sub_cancel,mul_cons hs]; push_cast; ring

private theorem at_zero {s : ℤ} {γ : ℝ} (h0 : 0≤γ) (h1 : γ<1) :
    Follows s γ [(1,s+1)] 0 0 := by
  have h := (identify (s:=s) (r:=0) (u:=0) (b:=s+1) (by push_cast; ring) le_rfl zero_lt_one)
  change gate γ (g s 0)=1 ∧ level s 0=s+1 ∧ g s 0=0
  rw [h.2]; exact ⟨by unfold gate; rw [sub_zero,(show ⌊γ⌋ = 0 from Int.floor_eq_iff.mpr (by simpa using And.intro h0 h1))]; rfl,h.1,rfl⟩

/-- All positive noninitial residues must be strictly above γ; zeros are permitted. -/
def Clear (s : ℤ) (γ r : ℝ) := ∀ j : ℕ, (g s)^[j+1] r=0 ∨ γ<(g s)^[j+1] r

private theorem shift_clear {s : ℤ} {γ r : ℝ} (h : Clear s γ r) (k : ℕ) : Clear s γ ((g s)^[k] r) := by
  intro j
  rw [← Function.iterate_add_apply]
  simpa only [show j+1+k=(j+k)+1 by omega] using h (j+k)

private theorem site_gate {s : ℤ} {γ r u : ℝ} (h0 : 0≤γ) (h1 : γ<1) (h : Clear s γ r)
    (eqn : g s r=u) (hu : 0<u) (hu' : u<1) : gate γ u=0 := by
  have e := h 0
  change g s r=0 ∨ γ<g s r at e
  rw [eqn] at e
  exact (gates h0 h1 (e.resolve_left (ne_of_gt hu)) hu').1

theorem word_follows {s : ℤ} {γ : ℝ} (hs : 2≤s) (h0 : 0≤γ) (h1 : γ<1) (w : Word)
    (hw : Good s w) (clear : Clear s γ (val s w)) : Follows s γ (program s w) (val s w) 0 := by
  have zero_gate : gate γ 0=1 := by unfold gate; rw [sub_zero,(show ⌊γ⌋ = 0 from Int.floor_eq_iff.mpr (by simpa using And.intro h0 h1))]; rfl
  induction w with
  | one a =>
    have h := identify (s:=s) (r:=consDigit s a 0) (u:=0) (b:=s+1-a) (by
      rw [mul_sub,mul_one,mul_cons hs]; push_cast; ring) le_rfl zero_lt_one
    refine ⟨h.2 ▸ zero_gate,h.1,?_⟩
    change Follows s γ [(1,s+1)] (g s (consDigit s a 0)) 0
    rw [h.2]; exact at_zero h0 h1
  | two a b =>
    obtain ⟨_,_,b0,bs⟩ := hw
    let v := consDigit s b 0
    have vb := last hs b0 bs
    obtain ⟨bl,gr⟩ := front (a:=a) hs vb.1 vb.2
    have gt := site_gate h0 h1 clear gr (by linarith [vb.2]) (by linarith [vb.1])
    obtain ⟨br,gr'⟩ := back (b:=b) hs (le_rfl : (0:ℝ)≤0) zero_lt_one
    refine ⟨gr ▸ gt,bl,?_⟩
    change Follows s γ [(1,1+b),(1,s+1)] (g s (consDigit s a v)) 0
    rw [gr]; refine ⟨(congrArg (gate γ) gr').trans zero_gate,br,?_⟩
    rw [gr']; exact at_zero h0 h1
  | more a b t ih =>
    obtain ⟨_,_,b0,bs,ht⟩ := hw
    obtain ⟨tv,tv'⟩ := in_unit hs t ht
    let v := consDigit s b (val s t)
    have vb := prep hs b0 bs tv tv'
    obtain ⟨bl,gr⟩ := front (a:=a) hs vb.1 vb.2
    have gt := site_gate h0 h1 clear gr (by linarith [vb.2]) (by linarith [vb.1])
    obtain ⟨br,gr'⟩ := back (b:=b) hs tv.le tv'
    have c := shift_clear clear 1
    change Clear s γ (g s (consDigit s a v)) at c
    change g s (consDigit s a v)=1-v at gr
    rw [gr] at c
    have gt' := site_gate h0 h1 c gr' tv tv'
    have c' := shift_clear c 1
    change Clear s γ (g s (1-v)) at c'
    rw [gr'] at c'
    refine ⟨gr ▸ gt,bl,?_⟩
    change Follows s γ ((0,1+b)::program s t) (g s (consDigit s a v)) 0
    rw [gr]; refine ⟨gr' ▸ gt',br,?_⟩
    rw [gr']; exact ih ht c'

#print axioms word_follows
end BCMP430.Tape
