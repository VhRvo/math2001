/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a
    _ = b ^ 2 + 1 := hb
    _ > 0 := by extra


example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  { have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    exact hxt' }
  { have h1 : 0 < x * -t := by
      calc
        0
        _ < - (x * t) := by addarith [hxt]
        _ = x * -t := by ring
    cancel x at h1
    apply ne_of_lt
    addarith [h1] }

example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers

example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra

example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6
  use 5
  ring

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use (a + 1)
  use a
  ring

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  constructor
  { calc
      p
      _ = (p + p) / 2 := by ring
      _ < (p + q) / 2 := by rel [h] }
  { calc
      (p + q) / 2
      _ < (q + q) / 2 := by rel [h]
      _ = q := by ring }

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  ring

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 6
  use 7
  ring

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -0.5
  constructor
  { numbers }
  { numbers }

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 4
  use 3
  ring

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  obtain hx | hx := le_or_gt x 0
  { use 1 - x
    have h : 1 - x > 0 := by
      calc
        1 - x
        _ >= 1 - 0 := by addarith [hx]
        _ = 1 := by ring
        _ > 0 := by numbers
    calc
      (1 - x) ^ 2
      _ > 0 ^ 2 := by rel [h]
      _ = 0 := by ring
      _ ≥ x := by rel [hx]
   }
  { obtain hx' | hx' := le_or_gt x 1
    { use 1 + x
      have h : 1 + x > 1 := by
        calc
          1 + x
          _ > 1 + 0 := by rel [hx]
          _ = 1 := by ring
      calc
        (1 + x) ^ 2
        _ > 1 ^ 2 := by rel [h]
        _ = 1 := by ring
        _ ≥ x := by rel [hx'] }
    { use x
      calc
        x ^ 2
        _ = x * x := by ring
        _ > x * 1 := by rel [hx']
        _ = x := by ring } }


example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  sorry

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  sorry

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  sorry

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  sorry
