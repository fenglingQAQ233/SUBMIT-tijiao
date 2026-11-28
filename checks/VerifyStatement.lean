import Final430
open BCMP430 BCMP430.UntunedTarget BCMP430.Components Set
#check @BCMP430.Final430.bcmp_conjecture_4_30
#print BCMP430.UntunedTarget.FullTarget
#print BCMP430.UntunedTarget.UT
#print BCMP430.UntunedTarget.Accum
example (s : ℤ) (hs : 2 ≤ s) (x : ℝ) (domain : x ∈ Icc 0 ((s:ℝ)/(s+1))) (outside : ∀ c : Center s, x ∉ Ioo c.T c.R) (ne : x ≠ (s:ℝ)/(s+1)) (ε : ℝ) (he : 0 < ε) (old : Finset (Set ℝ)) : ∃ y d, dist y x < ε ∧ d ≠ 0 ∧ y ∈ fiber s d ∧ IsOpen (connectedComponentIn (matching s) y) ∧ (connectedComponentIn (matching s) y ⊆ fiber s d) ∧ connectedComponentIn (matching s) y ∉ old := Final430.bcmp_conjecture_4_30 s hs x ⟨domain,outside⟩ ne ε he old
#print axioms BCMP430.Final430.bcmp_conjecture_4_30
