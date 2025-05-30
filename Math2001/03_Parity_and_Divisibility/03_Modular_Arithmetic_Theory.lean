/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

example : 11 ≡ 3 [ZMOD 4] := by
  use 2
  numbers

example : -5 ≡ 1 [ZMOD 3] := by
  use -2
  numbers

theorem Int.ModEq.add {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a + c ≡ b + d [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x + y
  calc
    a + c - (b + d)
    _ = a - b + (c - d) := by ring
    _ = n * x + n * y := by rw [hx, hy]
    _ = n * (x + y) := by ring

theorem Int.ModEq.sub {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a - c ≡ b - d [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨k₁, hk₁⟩ := h1
  obtain ⟨k₂, hk₂⟩ := h2
  use k₁ - k₂
  calc
    (a - c) - (b - d)
    _ = (a - b) - (c - d) := by ring
    _ = n * k₁ - n * k₂ := by rw [hk₁, hk₂]
    _ = n * (k₁ - k₂) := by ring

theorem Int.ModEq.neg {n a b : ℤ} (h1 : a ≡ b [ZMOD n]) : -a ≡ -b [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨k ,hk⟩ := h1
  use -k
  calc
    -a - -b
    _ = -(a - b) := by ring
    _ = -(n * k) := by rw [hk]
    _ = n * -k := by ring

theorem Int.ModEq.mul {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a * c ≡ b * d [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x * c + b * y
  calc
    a * c - b * d
    -- important: get `a - b` and `c - d`
    _ = (a - b) * c + b * (c - d) := by ring
    _ = n * x * c + b * (n * y) := by rw [hx, hy]
    _ = n * (x * c + b * y) := by ring

theorem Int.ModEq.pow_two (h : a ≡ b [ZMOD n]) : a ^ 2 ≡ b ^ 2 [ZMOD n] := by
  repeat rw [pow_succ]
  repeat rw [pow_zero]
  repeat rw [mul_one]
  exact Int.ModEq.mul h h

theorem Int.ModEq.pow_two.manual (h : a ≡ b [ZMOD n]) : a ^ 2 ≡ b ^ 2 [ZMOD n] := by
  obtain ⟨x, hx⟩ := h
  use x * (a + b)
  calc
    a ^ 2 - b ^ 2
    _ = (a - b) * (a + b) := by ring
    _ = n * x * (a + b) := by rw [hx]
    _ = n * (x * (a + b)) := by ring

theorem Int.ModEq.pow_three (h : a ≡ b [ZMOD n]) : a ^ 3 ≡ b ^ 3 [ZMOD n] := by
  repeat rw [pow_succ]
  repeat rw [pow_zero]
  repeat rw [mul_one]
  exact Int.ModEq.mul h (Int.ModEq.mul h h)

theorem Int.ModEq.pow_three.manual (h : a ≡ b [ZMOD n]) : a ^ 3 ≡ b ^ 3 [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨k, hk⟩ := h
  use (a ^ 2 + b * (a + b)) * k
  calc
    a ^ 3 - b ^ 3
    -- important: get `a - b`
    _ = a ^ 3 - a ^ 2 * b + a ^ 2 * b - b ^ 3 := by ring
    _ = a ^ 2 * (a - b) + b * (a ^ 2 - b ^ 2) := by ring
    _ = a ^ 2 * (a - b) + b * (a + b) * (a - b) := by ring
    _ = (a ^ 2 + b * (a + b)) * (a - b) := by ring
    _ = (a ^ 2 + b * (a + b)) * (a - b) := by ring
    _ = (a ^ 2 + b * (a + b)) * (n * k) := by rw [hk]
    _ = n * ((a ^ 2 + b * (a + b)) * k) := by ring

example (k : ℕ) (h : a ≡ b [ZMOD n]) : a ^ k ≡ b ^ k [ZMOD a - b] := by
  induction k with
  | zero =>
  { use 0
    dsimp
    calc
      a ^ 0 - b ^ 0
      _ = 0 := by ring
      _ = (a - b) * 0 := by ring }
  | succ k ih =>
  { obtain ⟨f, hf⟩ := ih
    use a ^ k + f * b
    rw [Nat.succ_eq_add_one]
    calc
      a ^ (k + 1) - b ^ (k + 1)
      _ = a ^ k * (a - b) + (a ^ k - b ^ k) * b := by ring
      _ = a ^ k * (a - b) + ((a - b) * f) * b := by rw [hf]
      _ = (a - b) * (a ^ k + f * b) := by ring }

theorem Int.ModEq.pow (k : ℕ) (h : a ≡ b [ZMOD n]) : a ^ k ≡ b ^ k [ZMOD n] := by
  induction k with
  | zero =>
  { use 0
    dsimp
    calc
      a ^ 0 - b ^ 0
      _ = 0 := by ring
      _ = n * 0 := by ring }
  | succ k ih =>
  { rw [Nat.succ_eq_add_one]
    repeat rw [pow_succ]
    exact Int.ModEq.mul h ih }

theorem Int.ModEq.pow.manual (k : ℕ) (h : a ≡ b [ZMOD n]) : a ^ k ≡ b ^ k [ZMOD n] := by
  induction k with
  | zero =>
  { use 0
    dsimp
    calc
      a ^ 0 - b ^ 0
      _ = 0 := by ring
      _ = n * 0 := by ring }
  | succ k ih =>
  { rw [Nat.succ_eq_add_one]
    obtain ⟨f₁, hf₁⟩ := h
    obtain ⟨fκ, hfκ⟩ := ih
    use a ^ k * f₁ + fκ * b
    calc
      a ^ (k + 1) - b ^ (k + 1)
      _ = a ^ (k + 1) - a ^ k * b + a ^ k * b - b ^ (k + 1) := by ring
      _ = a ^ k * (a - b) + (a ^ k - b ^ k) * b := by ring
      _ = a ^ k * (n * f₁) + n * fκ * b := by rw [hf₁, hfκ]
      _ = n * (a ^ k * f₁ + fκ * b) := by ring }

theorem Int.ModEq.refl (a : ℤ) : a ≡ a [ZMOD n] := by
  use 0
  ring

example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
    a * b ^ 2 + a ^ 2 * b + 3 * a ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 * 2 [ZMOD 4] := by
  obtain ⟨x, hx⟩ := ha
  use x * (b ^ 2 + a * b + 2 * b + 3)
  calc
    a * b ^ 2 + a ^ 2 * b + 3 * a - (2 * b ^ 2 + 2 ^ 2 * b + 3 * 2)
    _ = (a - 2) * (b ^ 2 + a * b + 2 * b + 3) := by ring
    _ = 4 * x * (b ^ 2 + a * b + 2 * b + 3) := by rw [hx]
    _ = 4 * (x * (b ^ 2 + a * b + 2 * b + 3)) := by ring

example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
    a * b ^ 2 + a ^ 2 * b + 3 * a ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 * 2 [ZMOD 4] := by
  apply Int.ModEq.add
  apply Int.ModEq.add
  apply Int.ModEq.mul
  apply ha
  apply Int.ModEq.refl
  apply Int.ModEq.mul
  apply Int.ModEq.pow
  apply ha
  apply Int.ModEq.refl
  apply Int.ModEq.mul
  apply Int.ModEq.refl
  apply ha

/-! # Exercises -/

example : 34 ≡ 104 [ZMOD 5] := by
  use -14
  numbers

theorem Int.ModEq.symm (h : a ≡ b [ZMOD n]) : b ≡ a [ZMOD n] := by
  dsimp [Int.ModEq]
  obtain ⟨k, hk⟩ := h
  use -k
  calc
    b - a
    _ = -(a - b) := by ring
    _ = -(n * k) := by rw [hk]
    _ = n * -k := by ring

theorem Int.ModEq.trans (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) :
    a ≡ c [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨k₁, hk₁⟩ := h1
  obtain ⟨k₂, hk₂⟩ := h2
  use k₁ + k₂
  calc
    a - c
    _ = (a - b) + (b - c) := by ring
    _ = n * k₁ + n * k₂ := by rw [hk₁, hk₂]
    _ = n * (k₁ + k₂) := by ring

example : a + n * c ≡ a [ZMOD n] := by
  dsimp [Int.ModEq]
  use c
  calc
    a + n * c - a
    _ = n * c := by ring

example {a b : ℤ} (h : a ≡ b [ZMOD 5]) : 2 * a + 3 ≡ 2 * b + 3 [ZMOD 5] := by
  apply Int.ModEq.add
  apply Int.ModEq.mul
  exact Int.ModEq.refl 2
  exact h
  exact Int.ModEq.refl 3

example {a b : ℤ} (h : a ≡ b [ZMOD 5]) : 2 * a + 3 ≡ 2 * b + 3 [ZMOD 5] := by
  dsimp [Int.ModEq] at *
  obtain ⟨k, hk⟩ := h
  use 2 * k
  calc
    2 * a + 3 - (2 * b + 3)
    -- _ = 2 * a - 2 * b := by ring
    _ = 2 * (a - b) := by ring
    _ = 2 * (5 * k) := by rw [hk]
    _ = 5 * (2 * k) := by ring

example {m n : ℤ} (h : m ≡ n [ZMOD 4]) : 3 * m - 1 ≡ 3 * n - 1 [ZMOD 4] := by
  apply Int.ModEq.sub
  apply Int.ModEq.mul
  exact Int.ModEq.refl 3
  exact h
  exact Int.ModEq.refl 1

example {m n : ℤ} (h : m ≡ n [ZMOD 4]) : 3 * m - 1 ≡ 3 * n - 1 [ZMOD 4] := by
  dsimp [Int.ModEq] at *
  obtain ⟨k, hk⟩ := h
  use 3 * k
  calc
    3 * m - 1 - (3 * n - 1)
    _ = 3 * (m - n) := by ring
    _ = 3 * (4 * k) := by rw [hk]
    _ = 4 * (3 * k) := by ring

example {k : ℤ} (hb : k ≡ 3 [ZMOD 5]) :
    4 * k + k ^ 3 + 3 ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by
  apply Int.ModEq.add
  { apply Int.ModEq.add
    { apply Int.ModEq.mul
      { exact Int.ModEq.refl 4 }
      { exact hb } }
    { exact Int.ModEq.pow_three hb } }
  { exact Int.ModEq.refl 3}

example {k : ℤ} (hb : k ≡ 3 [ZMOD 5]) :
    4 * k + k ^ 3 + 3 ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by
  dsimp [Int.ModEq] at *
  obtain ⟨a, ha⟩ := hb
  use (a * (5 * a) ^ 2 + 30 * a * a + 3 ^ 2 * a) + ((5 * a) * a * 3 + 6 * a * 3) + 4 * a
  calc
    4 * k + k ^ 3 + 3 - (4 * 3 + 3 ^ 3 + 3)
    -- _ = k ^ 3 + 4 * k - 4 * 3 - 3 ^ 3 := by ring
    _ = k ^ 3 + 4 * (k - 3) - 3 ^ 3 := by ring
    _ = (k - 3 + 3) ^ 3 + 4 * (k - 3) - 3 ^ 3 := by ring
    _ = (5 * a + 3) ^ 3 + 4 * (5 * a) - 3 ^ 3 := by rw [ha]
    -- _ = ((5 * a) ^ 2 + 30 * a + 3 ^ 2) * (5 * a + 3) + 20 * a - 3 ^ 3 := by ring
    -- _ = ((5 * a) ^ 2 + 30 * a + 3 ^ 2) * (5 * a) +
    --     ((5 * a) ^ 2 + 30 * a + 3 ^ 2) * 3 + 20 * a - 3 ^ 3 := by ring
    _ = ((5 * a) ^ 3 + 30 * a * (5 * a) + 3 ^ 2 * (5 * a)) + ((5 * a) ^ 2 * 3 + 5 * 6 * a * 3 + 3 ^ 3) + 5 * 4 * a - 3 ^ 3 := by ring
    _ = (5 * a * (5 * a) ^ 2 + 5 * 30 * a * a + 5 * 3 ^ 2 * a) + (5 * (5 * a) * a * 3 + 5 * 6 * a * 3) + 5 * 4 * a := by ring
    _ = 5 * (a * (5 * a) ^ 2 + 30 * a * a + 3 ^ 2 * a) + 5 * ((5 * a) * a * 3 + 6 * a * 3) + 5 * 4 * a := by ring
    _ = 5 * ((a * (5 * a) ^ 2 + 30 * a * a + 3 ^ 2 * a) + ((5 * a) * a * 3 + 6 * a * 3) + 4 * a) := by ring
