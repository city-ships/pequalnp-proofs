import PEqualNP.Defs

/-! Explicit Res(2) refutation of PHP(4,3). The first 22 lines are its axioms.
Pigeons a, b, c, d have indices 0, 1, 2, 3. A positive literal means that the pigeon uses the specified hole. -/

namespace PigeonholeAsymmetric51
open PEqualNP.ProofComplexity
abbrev V := Fin 4 × Fin 3

def l0 : KLine V := ({({((0, 0), true)} : KTerm V), ({((0, 1), true)} : KTerm V), ({((0, 2), true)} : KTerm V)} : KLine V)
def p0 : List (KLine V) := l0 :: []
def l1 : KLine V := ({({((1, 0), true)} : KTerm V), ({((1, 1), true)} : KTerm V), ({((1, 2), true)} : KTerm V)} : KLine V)
def p1 : List (KLine V) := l1 :: p0
def l2 : KLine V := ({({((2, 0), true)} : KTerm V), ({((2, 1), true)} : KTerm V), ({((2, 2), true)} : KTerm V)} : KLine V)
def p2 : List (KLine V) := l2 :: p1
def l3 : KLine V := ({({((3, 0), true)} : KTerm V), ({((3, 1), true)} : KTerm V), ({((3, 2), true)} : KTerm V)} : KLine V)
def p3 : List (KLine V) := l3 :: p2
def l4 : KLine V := ({({((1, 0), false)} : KTerm V), ({((0, 0), false)} : KTerm V)} : KLine V)
def p4 : List (KLine V) := l4 :: p3
def l5 : KLine V := ({({((2, 0), false)} : KTerm V), ({((0, 0), false)} : KTerm V)} : KLine V)
def p5 : List (KLine V) := l5 :: p4
def l6 : KLine V := ({({((3, 0), false)} : KTerm V), ({((0, 0), false)} : KTerm V)} : KLine V)
def p6 : List (KLine V) := l6 :: p5
def l7 : KLine V := ({({((2, 0), false)} : KTerm V), ({((1, 0), false)} : KTerm V)} : KLine V)
def p7 : List (KLine V) := l7 :: p6
def l8 : KLine V := ({({((3, 0), false)} : KTerm V), ({((1, 0), false)} : KTerm V)} : KLine V)
def p8 : List (KLine V) := l8 :: p7
def l9 : KLine V := ({({((3, 0), false)} : KTerm V), ({((2, 0), false)} : KTerm V)} : KLine V)
def p9 : List (KLine V) := l9 :: p8
def l10 : KLine V := ({({((1, 1), false)} : KTerm V), ({((0, 1), false)} : KTerm V)} : KLine V)
def p10 : List (KLine V) := l10 :: p9
def l11 : KLine V := ({({((2, 1), false)} : KTerm V), ({((0, 1), false)} : KTerm V)} : KLine V)
def p11 : List (KLine V) := l11 :: p10
def l12 : KLine V := ({({((3, 1), false)} : KTerm V), ({((0, 1), false)} : KTerm V)} : KLine V)
def p12 : List (KLine V) := l12 :: p11
def l13 : KLine V := ({({((2, 1), false)} : KTerm V), ({((1, 1), false)} : KTerm V)} : KLine V)
def p13 : List (KLine V) := l13 :: p12
def l14 : KLine V := ({({((3, 1), false)} : KTerm V), ({((1, 1), false)} : KTerm V)} : KLine V)
def p14 : List (KLine V) := l14 :: p13
def l15 : KLine V := ({({((3, 1), false)} : KTerm V), ({((2, 1), false)} : KTerm V)} : KLine V)
def p15 : List (KLine V) := l15 :: p14
def l16 : KLine V := ({({((1, 2), false)} : KTerm V), ({((0, 2), false)} : KTerm V)} : KLine V)
def p16 : List (KLine V) := l16 :: p15
def l17 : KLine V := ({({((2, 2), false)} : KTerm V), ({((0, 2), false)} : KTerm V)} : KLine V)
def p17 : List (KLine V) := l17 :: p16
def l18 : KLine V := ({({((3, 2), false)} : KTerm V), ({((0, 2), false)} : KTerm V)} : KLine V)
def p18 : List (KLine V) := l18 :: p17
def l19 : KLine V := ({({((2, 2), false)} : KTerm V), ({((1, 2), false)} : KTerm V)} : KLine V)
def p19 : List (KLine V) := l19 :: p18
def l20 : KLine V := ({({((3, 2), false)} : KTerm V), ({((1, 2), false)} : KTerm V)} : KLine V)
def p20 : List (KLine V) := l20 :: p19
def l21 : KLine V := ({({((3, 2), false)} : KTerm V), ({((2, 2), false)} : KTerm V)} : KLine V)
def p21 : List (KLine V) := l21 :: p20

-- 23. -c0 or -b0 & -a0. Conjunction introduction on lines 6 and 8.
def l22 : KLine V := ({({((2, 0), false)} : KTerm V), ({((1, 0), false), ((0, 0), false)} : KTerm V)} : KLine V)
def p22 : List (KLine V) := l22 :: p21

-- 24. -d0 or -b0 & -a0. Conjunction introduction on lines 7 and 9.
def l23 : KLine V := ({({((3, 0), false)} : KTerm V), ({((1, 0), false), ((0, 0), false)} : KTerm V)} : KLine V)
def p23 : List (KLine V) := l23 :: p22

-- 25. -d0 & -c0 or -b0 & -a0. Conjunction introduction on lines 23 and 24.
def l24 : KLine V := ({({((3, 0), false), ((2, 0), false)} : KTerm V), ({((1, 0), false), ((0, 0), false)} : KTerm V)} : KLine V)
def p24 : List (KLine V) := l24 :: p23

-- 26. -d2 or -b2 & -a2. Conjunction introduction on lines 19 and 21.
def l25 : KLine V := ({({((3, 2), false)} : KTerm V), ({((1, 2), false), ((0, 2), false)} : KTerm V)} : KLine V)
def p25 : List (KLine V) := l25 :: p24

-- 27. -b2 & -a2 or +d0 or +d1. Cut on lines 26 and 4.
def l26 : KLine V := ({({((1, 2), false), ((0, 2), false)} : KTerm V), ({((3, 0), true)} : KTerm V), ({((3, 1), true)} : KTerm V)} : KLine V)
def p26 : List (KLine V) := l26 :: p25

-- 28. -c2 or -b2 & -a2. Conjunction introduction on lines 18 and 20.
def l27 : KLine V := ({({((2, 2), false)} : KTerm V), ({((1, 2), false), ((0, 2), false)} : KTerm V)} : KLine V)
def p27 : List (KLine V) := l27 :: p26

-- 29. -b2 & -a2 or +c0 or +c1. Cut on lines 28 and 3.
def l28 : KLine V := ({({((1, 2), false), ((0, 2), false)} : KTerm V), ({((2, 0), true)} : KTerm V), ({((2, 1), true)} : KTerm V)} : KLine V)
def p28 : List (KLine V) := l28 :: p27

-- 30. -d1 or -b2 & -a2 or +c0. Cut on lines 16 and 29.
def l29 : KLine V := ({({((3, 1), false)} : KTerm V), ({((1, 2), false), ((0, 2), false)} : KTerm V), ({((2, 0), true)} : KTerm V)} : KLine V)
def p29 : List (KLine V) := l29 :: p28

-- 31. -b2 & -a2 or +c0 or +d0. Cut on lines 27 and 30.
def l30 : KLine V := ({({((1, 2), false), ((0, 2), false)} : KTerm V), ({((2, 0), true)} : KTerm V), ({((3, 0), true)} : KTerm V)} : KLine V)
def p30 : List (KLine V) := l30 :: p29

-- 32. -d1 & -c1 or -b1. Conjunction introduction on lines 14 and 15.
def l31 : KLine V := ({({((3, 1), false), ((2, 1), false)} : KTerm V), ({((1, 1), false)} : KTerm V)} : KLine V)
def p31 : List (KLine V) := l31 :: p30

-- 33. -d1 & -c1 or +b0 or +b2. Cut on lines 32 and 2.
def l32 : KLine V := ({({((3, 1), false), ((2, 1), false)} : KTerm V), ({((1, 0), true)} : KTerm V), ({((1, 2), true)} : KTerm V)} : KLine V)
def p32 : List (KLine V) := l32 :: p31

-- 34. -d1 & -c1 or -a1. Conjunction introduction on lines 12 and 13.
def l33 : KLine V := ({({((3, 1), false), ((2, 1), false)} : KTerm V), ({((0, 1), false)} : KTerm V)} : KLine V)
def p33 : List (KLine V) := l33 :: p32

-- 35. -d1 & -c1 or +a0 or +a2. Cut on lines 34 and 1.
def l34 : KLine V := ({({((3, 1), false), ((2, 1), false)} : KTerm V), ({((0, 0), true)} : KTerm V), ({((0, 2), true)} : KTerm V)} : KLine V)
def p34 : List (KLine V) := l34 :: p33

-- 36. -d1 & -c1 or -b0 or +a2. Cut on lines 5 and 35.
def l35 : KLine V := ({({((3, 1), false), ((2, 1), false)} : KTerm V), ({((1, 0), false)} : KTerm V), ({((0, 2), true)} : KTerm V)} : KLine V)
def p35 : List (KLine V) := l35 :: p34

-- 37. -d1 & -c1 or +a2 or +b2. Cut on lines 33 and 36.
def l36 : KLine V := ({({((3, 1), false), ((2, 1), false)} : KTerm V), ({((0, 2), true)} : KTerm V), ({((1, 2), true)} : KTerm V)} : KLine V)
def p36 : List (KLine V) := l36 :: p35

-- 38. -d1 & -c1 or +c0 or +d0. Cut on lines 31 and 37.
def l37 : KLine V := ({({((3, 1), false), ((2, 1), false)} : KTerm V), ({((2, 0), true)} : KTerm V), ({((3, 0), true)} : KTerm V)} : KLine V)
def p37 : List (KLine V) := l37 :: p36

-- 39. -d2 or +c0 or +c1. Cut on lines 22 and 3.
def l38 : KLine V := ({({((3, 2), false)} : KTerm V), ({((2, 0), true)} : KTerm V), ({((2, 1), true)} : KTerm V)} : KLine V)
def p38 : List (KLine V) := l38 :: p37

-- 40. +c0 or +c1 or +d0 or +d1. Cut on lines 4 and 39.
def l39 : KLine V := ({({((2, 0), true)} : KTerm V), ({((2, 1), true)} : KTerm V), ({((3, 0), true)} : KTerm V), ({((3, 1), true)} : KTerm V)} : KLine V)
def p39 : List (KLine V) := l39 :: p38

-- 41. +c0 or +d0. Cut on lines 38 and 40.
def l40 : KLine V := ({({((2, 0), true)} : KTerm V), ({((3, 0), true)} : KTerm V)} : KLine V)
def p40 : List (KLine V) := l40 :: p39

-- 42. -b0 & -a0. Cut on lines 25 and 41.
def l41 : KLine V := ({({((1, 0), false), ((0, 0), false)} : KTerm V)} : KLine V)
def p41 : List (KLine V) := l41 :: p40

-- 43. -d1 & -c1 or -b2 or +a0. Cut on lines 17 and 35.
def l42 : KLine V := ({({((3, 1), false), ((2, 1), false)} : KTerm V), ({((1, 2), false)} : KTerm V), ({((0, 0), true)} : KTerm V)} : KLine V)
def p42 : List (KLine V) := l42 :: p41

-- 44. -d1 & -c1 or +a0 or +b0. Cut on lines 33 and 43.
def l43 : KLine V := ({({((3, 1), false), ((2, 1), false)} : KTerm V), ({((0, 0), true)} : KTerm V), ({((1, 0), true)} : KTerm V)} : KLine V)
def p43 : List (KLine V) := l43 :: p42

-- 45. -d0 or -b2 & -a2 or +c1. Cut on lines 10 and 29.
def l44 : KLine V := ({({((3, 0), false)} : KTerm V), ({((1, 2), false), ((0, 2), false)} : KTerm V), ({((2, 1), true)} : KTerm V)} : KLine V)
def p44 : List (KLine V) := l44 :: p43

-- 46. -b2 & -a2 or +c1 or +d1. Cut on lines 27 and 45.
def l45 : KLine V := ({({((1, 2), false), ((0, 2), false)} : KTerm V), ({((2, 1), true)} : KTerm V), ({((3, 1), true)} : KTerm V)} : KLine V)
def p45 : List (KLine V) := l45 :: p44

-- 47. -b2 & -a2 or +a0 or +b0. Cut on lines 44 and 46.
def l46 : KLine V := ({({((1, 2), false), ((0, 2), false)} : KTerm V), ({((0, 0), true)} : KTerm V), ({((1, 0), true)} : KTerm V)} : KLine V)
def p46 : List (KLine V) := l46 :: p45

-- 48. -a1 or +b0 or +b2. Cut on lines 11 and 2.
def l47 : KLine V := ({({((0, 1), false)} : KTerm V), ({((1, 0), true)} : KTerm V), ({((1, 2), true)} : KTerm V)} : KLine V)
def p47 : List (KLine V) := l47 :: p46

-- 49. +a0 or +a2 or +b0 or +b2. Cut on lines 48 and 1.
def l48 : KLine V := ({({((0, 0), true)} : KTerm V), ({((0, 2), true)} : KTerm V), ({((1, 0), true)} : KTerm V), ({((1, 2), true)} : KTerm V)} : KLine V)
def p48 : List (KLine V) := l48 :: p47

-- 50. +a0 or +b0. Cut on lines 47 and 49.
def l49 : KLine V := ({({((0, 0), true)} : KTerm V), ({((1, 0), true)} : KTerm V)} : KLine V)
def p49 : List (KLine V) := l49 :: p48

-- 51. contradiction. Cut on lines 42 and 50.
def l50 : KLine V := (∅ : KLine V)
def p50 : List (KLine V) := l50 :: p49

set_option maxRecDepth 10000 in
theorem d0 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p0 := by
  exact IsResKDerivation.ax IsResKDerivation.nil ⟨({((0, 0), true), ((0, 1), true), ((0, 2), true)} : Clause V), Set.mem_union_left _ ⟨0, by decide +kernel⟩, by decide +kernel⟩ (by
    intro t ht
    simp only [l0, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d1 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p1 := by
  exact IsResKDerivation.ax d0 ⟨({((1, 0), true), ((1, 1), true), ((1, 2), true)} : Clause V), Set.mem_union_left _ ⟨1, by decide +kernel⟩, by decide +kernel⟩ (by
    intro t ht
    simp only [l1, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d2 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p2 := by
  exact IsResKDerivation.ax d1 ⟨({((2, 0), true), ((2, 1), true), ((2, 2), true)} : Clause V), Set.mem_union_left _ ⟨2, by decide +kernel⟩, by decide +kernel⟩ (by
    intro t ht
    simp only [l2, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d3 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p3 := by
  exact IsResKDerivation.ax d2 ⟨({((3, 0), true), ((3, 1), true), ((3, 2), true)} : Clause V), Set.mem_union_left _ ⟨3, by decide +kernel⟩, by decide +kernel⟩ (by
    intro t ht
    simp only [l3, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d4 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p4 := by
  exact IsResKDerivation.ax d3 ⟨({((1, 0), false), ((0, 0), false)} : Clause V), Set.mem_union_right _ ⟨0, 1, 0, by decide, by decide +kernel⟩, by decide +kernel⟩ (by
    intro t ht
    simp only [l4, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d5 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p5 := by
  exact IsResKDerivation.ax d4 ⟨({((2, 0), false), ((0, 0), false)} : Clause V), Set.mem_union_right _ ⟨0, 2, 0, by decide, by decide +kernel⟩, by decide +kernel⟩ (by
    intro t ht
    simp only [l5, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d6 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p6 := by
  exact IsResKDerivation.ax d5 ⟨({((3, 0), false), ((0, 0), false)} : Clause V), Set.mem_union_right _ ⟨0, 3, 0, by decide, by decide +kernel⟩, by decide +kernel⟩ (by
    intro t ht
    simp only [l6, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d7 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p7 := by
  exact IsResKDerivation.ax d6 ⟨({((2, 0), false), ((1, 0), false)} : Clause V), Set.mem_union_right _ ⟨1, 2, 0, by decide, by decide +kernel⟩, by decide +kernel⟩ (by
    intro t ht
    simp only [l7, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d8 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p8 := by
  exact IsResKDerivation.ax d7 ⟨({((3, 0), false), ((1, 0), false)} : Clause V), Set.mem_union_right _ ⟨1, 3, 0, by decide, by decide +kernel⟩, by decide +kernel⟩ (by
    intro t ht
    simp only [l8, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d9 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p9 := by
  exact IsResKDerivation.ax d8 ⟨({((3, 0), false), ((2, 0), false)} : Clause V), Set.mem_union_right _ ⟨2, 3, 0, by decide, by decide +kernel⟩, by decide +kernel⟩ (by
    intro t ht
    simp only [l9, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d10 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p10 := by
  exact IsResKDerivation.ax d9 ⟨({((1, 1), false), ((0, 1), false)} : Clause V), Set.mem_union_right _ ⟨0, 1, 1, by decide, by decide +kernel⟩, by decide +kernel⟩ (by
    intro t ht
    simp only [l10, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d11 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p11 := by
  exact IsResKDerivation.ax d10 ⟨({((2, 1), false), ((0, 1), false)} : Clause V), Set.mem_union_right _ ⟨0, 2, 1, by decide, by decide +kernel⟩, by decide +kernel⟩ (by
    intro t ht
    simp only [l11, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d12 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p12 := by
  exact IsResKDerivation.ax d11 ⟨({((3, 1), false), ((0, 1), false)} : Clause V), Set.mem_union_right _ ⟨0, 3, 1, by decide, by decide +kernel⟩, by decide +kernel⟩ (by
    intro t ht
    simp only [l12, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d13 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p13 := by
  exact IsResKDerivation.ax d12 ⟨({((2, 1), false), ((1, 1), false)} : Clause V), Set.mem_union_right _ ⟨1, 2, 1, by decide, by decide +kernel⟩, by decide +kernel⟩ (by
    intro t ht
    simp only [l13, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d14 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p14 := by
  exact IsResKDerivation.ax d13 ⟨({((3, 1), false), ((1, 1), false)} : Clause V), Set.mem_union_right _ ⟨1, 3, 1, by decide, by decide +kernel⟩, by decide +kernel⟩ (by
    intro t ht
    simp only [l14, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d15 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p15 := by
  exact IsResKDerivation.ax d14 ⟨({((3, 1), false), ((2, 1), false)} : Clause V), Set.mem_union_right _ ⟨2, 3, 1, by decide, by decide +kernel⟩, by decide +kernel⟩ (by
    intro t ht
    simp only [l15, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d16 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p16 := by
  exact IsResKDerivation.ax d15 ⟨({((1, 2), false), ((0, 2), false)} : Clause V), Set.mem_union_right _ ⟨0, 1, 2, by decide, by decide +kernel⟩, by decide +kernel⟩ (by
    intro t ht
    simp only [l16, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d17 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p17 := by
  exact IsResKDerivation.ax d16 ⟨({((2, 2), false), ((0, 2), false)} : Clause V), Set.mem_union_right _ ⟨0, 2, 2, by decide, by decide +kernel⟩, by decide +kernel⟩ (by
    intro t ht
    simp only [l17, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d18 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p18 := by
  exact IsResKDerivation.ax d17 ⟨({((3, 2), false), ((0, 2), false)} : Clause V), Set.mem_union_right _ ⟨0, 3, 2, by decide, by decide +kernel⟩, by decide +kernel⟩ (by
    intro t ht
    simp only [l18, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d19 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p19 := by
  exact IsResKDerivation.ax d18 ⟨({((2, 2), false), ((1, 2), false)} : Clause V), Set.mem_union_right _ ⟨1, 2, 2, by decide, by decide +kernel⟩, by decide +kernel⟩ (by
    intro t ht
    simp only [l19, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d20 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p20 := by
  exact IsResKDerivation.ax d19 ⟨({((3, 2), false), ((1, 2), false)} : Clause V), Set.mem_union_right _ ⟨1, 3, 2, by decide, by decide +kernel⟩, by decide +kernel⟩ (by
    intro t ht
    simp only [l20, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d21 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p21 := by
  exact IsResKDerivation.ax d20 ⟨({((3, 2), false), ((2, 2), false)} : Clause V), Set.mem_union_right _ ⟨2, 3, 2, by decide, by decide +kernel⟩, by decide +kernel⟩ (by
    intro t ht
    simp only [l21, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d22 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p22 := by
  exact IsResKDerivation.andIntro (C := l5) (D := l7) (R := l22) d21 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))) ⟨({((0, 0), false)} : KTerm V), ({((1, 0), false)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel⟩ (by
    intro t ht
    simp only [l22, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d23 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p23 := by
  exact IsResKDerivation.andIntro (C := l6) (D := l8) (R := l23) d22 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))) ⟨({((0, 0), false)} : KTerm V), ({((1, 0), false)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel⟩ (by
    intro t ht
    simp only [l23, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d24 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p24 := by
  exact IsResKDerivation.andIntro (C := l22) (D := l23) (R := l24) d23 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ⟨({((2, 0), false)} : KTerm V), ({((3, 0), false)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel⟩ (by
    intro t ht
    simp only [l24, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d25 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p25 := by
  exact IsResKDerivation.andIntro (C := l18) (D := l20) (R := l25) d24 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) ⟨({((0, 2), false)} : KTerm V), ({((1, 2), false)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel⟩ (by
    intro t ht
    simp only [l25, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d26 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p26 := by
  exact IsResKDerivation.cut (C := l25) (D := l3) (R := l26) d25 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))) ⟨({((3, 2), false)} : KTerm V), by decide +kernel, by decide +kernel, (by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    rcases hj with rfl
    decide +kernel), by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem d27 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p27 := by
  exact IsResKDerivation.andIntro (C := l17) (D := l19) (R := l27) d26 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))) ⟨({((0, 2), false)} : KTerm V), ({((1, 2), false)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel⟩ (by
    intro t ht
    simp only [l27, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d28 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p28 := by
  exact IsResKDerivation.cut (C := l27) (D := l2) (R := l28) d27 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))) ⟨({((2, 2), false)} : KTerm V), by decide +kernel, by decide +kernel, (by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    rcases hj with rfl
    decide +kernel), by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem d29 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p29 := by
  exact IsResKDerivation.cut (C := l15) (D := l28) (R := l29) d28 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))) (List.Mem.head _) ⟨({((2, 1), false)} : KTerm V), by decide +kernel, by decide +kernel, (by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    rcases hj with rfl
    decide +kernel), by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem d30 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p30 := by
  exact IsResKDerivation.cut (C := l26) (D := l29) (R := l30) d29 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (List.Mem.head _) ⟨({((3, 1), true)} : KTerm V), by decide +kernel, by decide +kernel, (by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    rcases hj with rfl
    decide +kernel), by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem d31 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p31 := by
  exact IsResKDerivation.andIntro (C := l13) (D := l14) (R := l31) d30 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))) ⟨({((2, 1), false)} : KTerm V), ({((3, 1), false)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel⟩ (by
    intro t ht
    simp only [l31, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d32 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p32 := by
  exact IsResKDerivation.cut (C := l31) (D := l1) (R := l32) d31 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))) ⟨({((1, 1), false)} : KTerm V), by decide +kernel, by decide +kernel, (by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    rcases hj with rfl
    decide +kernel), by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem d33 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p33 := by
  exact IsResKDerivation.andIntro (C := l11) (D := l12) (R := l33) d32 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))) ⟨({((2, 1), false)} : KTerm V), ({((3, 1), false)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel⟩ (by
    intro t ht
    simp only [l33, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    all_goals decide +kernel)

set_option maxRecDepth 10000 in
theorem d34 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p34 := by
  exact IsResKDerivation.cut (C := l33) (D := l0) (R := l34) d33 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))) ⟨({((0, 1), false)} : KTerm V), by decide +kernel, by decide +kernel, (by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    rcases hj with rfl
    decide +kernel), by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem d35 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p35 := by
  exact IsResKDerivation.cut (C := l4) (D := l34) (R := l35) d34 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))) (List.Mem.head _) ⟨({((0, 0), false)} : KTerm V), by decide +kernel, by decide +kernel, (by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    rcases hj with rfl
    decide +kernel), by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem d36 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p36 := by
  exact IsResKDerivation.cut (C := l32) (D := l35) (R := l36) d35 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (List.Mem.head _) ⟨({((1, 0), true)} : KTerm V), by decide +kernel, by decide +kernel, (by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    rcases hj with rfl
    decide +kernel), by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem d37 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p37 := by
  exact IsResKDerivation.cut (C := l30) (D := l36) (R := l37) d36 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) (List.Mem.head _) ⟨({((1, 2), false), ((0, 2), false)} : KTerm V), by decide +kernel, by decide +kernel, (by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    all_goals decide +kernel), by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem d38 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p38 := by
  exact IsResKDerivation.cut (C := l21) (D := l2) (R := l38) d37 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))) ⟨({((2, 2), false)} : KTerm V), by decide +kernel, by decide +kernel, (by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    rcases hj with rfl
    decide +kernel), by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem d39 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p39 := by
  exact IsResKDerivation.cut (C := l3) (D := l38) (R := l39) d38 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))) (List.Mem.head _) ⟨({((3, 2), true)} : KTerm V), by decide +kernel, by decide +kernel, (by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    rcases hj with rfl
    decide +kernel), by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem d40 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p40 := by
  exact IsResKDerivation.cut (C := l37) (D := l39) (R := l40) d39 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.head _) ⟨({((3, 1), false), ((2, 1), false)} : KTerm V), by decide +kernel, by decide +kernel, (by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    all_goals decide +kernel), by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem d41 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p41 := by
  exact IsResKDerivation.cut (C := l24) (D := l40) (R := l41) d40 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))) (List.Mem.head _) ⟨({((3, 0), false), ((2, 0), false)} : KTerm V), by decide +kernel, by decide +kernel, (by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    all_goals decide +kernel), by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem d42 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p42 := by
  exact IsResKDerivation.cut (C := l16) (D := l34) (R := l42) d41 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))) ⟨({((0, 2), false)} : KTerm V), by decide +kernel, by decide +kernel, (by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    rcases hj with rfl
    decide +kernel), by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem d43 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p43 := by
  exact IsResKDerivation.cut (C := l32) (D := l42) (R := l43) d42 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))) (List.Mem.head _) ⟨({((1, 2), true)} : KTerm V), by decide +kernel, by decide +kernel, (by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    rcases hj with rfl
    decide +kernel), by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem d44 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p44 := by
  exact IsResKDerivation.cut (C := l9) (D := l28) (R := l44) d43 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))) ⟨({((2, 0), false)} : KTerm V), by decide +kernel, by decide +kernel, (by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    rcases hj with rfl
    decide +kernel), by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem d45 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p45 := by
  exact IsResKDerivation.cut (C := l26) (D := l44) (R := l45) d44 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))) (List.Mem.head _) ⟨({((3, 0), true)} : KTerm V), by decide +kernel, by decide +kernel, (by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    rcases hj with rfl
    decide +kernel), by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem d46 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p46 := by
  exact IsResKDerivation.cut (C := l43) (D := l45) (R := l46) d45 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.head _) ⟨({((3, 1), false), ((2, 1), false)} : KTerm V), by decide +kernel, by decide +kernel, (by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    all_goals decide +kernel), by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem d47 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p47 := by
  exact IsResKDerivation.cut (C := l10) (D := l1) (R := l47) d46 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))))))))))))) ⟨({((1, 1), false)} : KTerm V), by decide +kernel, by decide +kernel, (by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    rcases hj with rfl
    decide +kernel), by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem d48 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p48 := by
  exact IsResKDerivation.cut (C := l47) (D := l0) (R := l48) d47 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))))))))))))))) ⟨({((0, 1), false)} : KTerm V), by decide +kernel, by decide +kernel, (by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    rcases hj with rfl
    decide +kernel), by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem d49 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p49 := by
  exact IsResKDerivation.cut (C := l46) (D := l48) (R := l49) d48 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.head _) ⟨({((1, 2), false), ((0, 2), false)} : KTerm V), by decide +kernel, by decide +kernel, (by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    all_goals decide +kernel), by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem d50 : IsResKDerivation 2 (kLineOfClause '' PHP 4 3) p50 := by
  exact IsResKDerivation.cut (C := l41) (D := l49) (R := l50) d49 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))) (List.Mem.head _) ⟨({((1, 0), false), ((0, 0), false)} : KTerm V), by decide +kernel, by decide +kernel, (by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    all_goals decide +kernel), by decide +kernel⟩

theorem refutation51 :
    ∃ π : List (KLine V), IsResKRefutation 2 (PHP 4 3) π ∧ π.length = 51 :=
  ⟨p50, ⟨d50, .head _⟩, rfl⟩

end PigeonholeAsymmetric51
