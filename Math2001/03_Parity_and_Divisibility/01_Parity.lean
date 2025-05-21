/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init

open Int


example : Odd (7 : ℤ) := by
  dsimp [Odd]
  use 3
  numbers

example : Odd (-3 : ℤ) := by
  use -2
  numbers

example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  rw [hk]
  ring
  -- calc
  --   3 * n + 2
  --   _ = 3 * (2 * k + 1) + 2 := by rw [hk]
  --   _ = 2 * (3 * k + 2) + 1 := by ring

example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 7 * k + 1
  rw [hk]
  ring
  -- calc
  --   7 * n - 4
  --   _ = 7 * (2 * k + 1) - 4 := by rw [hk]
  --   _ = 2 * (7 * k + 1) + 1 := by ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  dsimp [Odd] at *
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use a + b + 1
  rw [ha, hb]
  ring
  -- calc
  --   x + y + 1
  --   _ = 2 * a + 1 + (2 * b + 1) + 1 := by rw [ha, hb]
  --   _ = 2 * (a + b + 1) + 1 := by ring


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  dsimp [Odd] at *
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use 2 * a * b + a + 3 * b + 1
  rw [ha, hb]
  ring
  -- calc
  --   x * y + 2 * y
  --   _ = (2 * a + 1) * (2 * b + 1) + 2 * (2 * b + 1) := by rw [ha, hb]
  --   -- _ = 4 * a * b + 2 * a + 2 * b + 1 + 4 * b + 2 := by ring
  --   _ = 2 * (2 * a * b + a + 3 * b + 1) + 1 := by ring

example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by
  dsimp [Odd, Even] at *
  obtain ⟨k, hk⟩ := hm
  use 3 * k - 1
  rw [hk]
  ring
  -- calc
  --   3 * m - 5
  --   _ = 3 * (2 * k + 1) - 5 := by rw [hk]
  --   _ = 2 * (3 * k - 1) := by ring

example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  dsimp [Odd, Even] at *
  obtain ⟨k, hk⟩ := hn
  use 2 * k ^ 2 + 2 * k - 3
  rw [hk]
  ring
  -- calc
  --   n ^ 2 + 2 * n - 5
  --   _ = (2 * k) ^ 2 + 2 * (2 * k) - 5 := by rw [hk]
  --   _ = 2 * (2 * k ^ 2 + 2 * k - 3) + 1 := by ring

example (n : ℤ) : Even (n * (n + 1)) := by
  obtain hn | hn := Int.even_or_odd n
  { obtain ⟨x, hx⟩ := hn
    use x * (n + 1)
    rw [hx]
    ring }
    -- calc
    --   n * (n + 1)
    --   _ = 2 * x * (n + 1) := by rw [hx]
    --   _ = 2 * (x * (n + 1)) := by ring
  { obtain ⟨x, hx⟩ := hn
    use n * (x + 1)
    rw [hx]
    ring }
    -- calc
    --   n * (n + 1)
    --   _ = n * (2 * x + 1 + 1) := by rw [hx]
    --   _ = 2 * (n * (x + 1)) := by ring

example (n : ℤ) : Even (n ^ 2 + n + 4) := by
  obtain hn | hn := Int.even_or_odd n
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + x + 2
    rw [hx]
    ring
    -- calc
    --   n ^ 2 + n + 4 = (2 * x) ^ 2 + 2 * x + 4 := by rw [hx]
    --   _ = 2 * (2 * x ^ 2 + x + 2) := by ring
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + 3 * x + 3
    rw [hx]
    ring
    -- calc
    --   n ^ 2 + n + 4 = (2 * x + 1) ^ 2 + (2 * x + 1) + 4 := by rw [hx]
    --   _ = 2 * (2 * x ^ 2 + 3 * x + 3) := by ring

/-! # Exercises -/

example : Odd (-9 : ℤ) := by
  use -5
  numbers

example : Even (26 : ℤ) := by
  use 13
  numbers

example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  dsimp [Odd, Even] at *
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  use a + b
  rw [ha, hb]
  ring
  -- calc
  --   n + m
  --   _ = 2 * b + (2 * a + 1) := by rw [ha, hb]
  --   _ = 2 * (a + b) + 1 := by ring

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  dsimp [Odd, Even] at *
  obtain ⟨a, ha⟩ := hp
  obtain ⟨b, hb⟩ := hq
  use a - b - 2
  rw [ha, hb]
  ring
  -- calc
  --   p - q - 4
  --   _ = (2 * a + 1) - 2 * b - 4 := by rw [ha, hb]
  --   _ = 2 * (a - b - 2) + 1 := by ring

example {a b : ℤ} (ha : Even a) (hb : Odd b) : Even (3 * a + b - 3) := by
  dsimp [Odd, Even] at *
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  use 3 * m + n - 1
  rw [hm, hn]
  ring
  -- calc
  --   3 * a + b - 3
  --   _ = 3 * (2 * m) + (2 * n + 1) - 3 := by rw [hm, hn]
  --   _ = 2 * (3 * m + n - 1) := by ring

example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by
  dsimp [Odd, Even] at *
  obtain ⟨a, ha⟩ := hr
  obtain ⟨b, hb⟩ := hs
  use 3 * a - 5 * b - 1
  rw [ha, hb]
  ring
  -- calc
  --   3 * r - 5 * s
  --   _ = 3 * (2 * a + 1) - 5 * (2 * b + 1) := by rw [ha, hb]
  --   _ = 2 * (3 * a - 5 * b - 1) := by ring

example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  dsimp [Odd] at *
  obtain ⟨a, ha⟩ := hx
  use (a * x ^ 2 + 2 * a ^ 2 + 2 * a)
  calc
    x ^ 3
    _ = x * x ^ 2 := by ring
    _ = (2 * a + 1) * x ^ 2 := by rw [ha]
    _ = 2 * a * x ^ 2 + x ^ 2 := by ring
    _ = 2 * a * x ^ 2 + (2 * a + 1) ^ 2 := by rw [ha]
    -- _ = 2 * a * x ^ 2 + (4 * a ^ 2 + 4 * a + 1) := by ring
    _ = 2 * (a * x ^ 2 + 2 * a ^ 2 + 2 * a) + 1 := by ring

example {n : ℤ} (hn : Odd n) : Even (n ^ 2 - 3 * n + 2) := by
  dsimp [Odd, Even] at *
  obtain ⟨a, ha⟩ := hn
  use 2 * a ^ 2 - a
  rw [ha]
  ring
  -- calc
  --   n ^ 2 - 3 * n + 2
  --   _ = (2 * a + 1) ^ 2 - 3 * (2 * a + 1) + 2 := by rw [ha]
  --   _ = 2 * (2 * a ^ 2 - a) := by ring

example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by
  dsimp [Odd] at *
  obtain ⟨b, hb⟩ := ha
  use 2 * b ^ 2 + 4 * b -1
  rw [hb]
  ring
  -- calc
  --   a ^ 2 + 2 * a - 4
  --   _ = (2 * b + 1) ^ 2 + 2 * (2 * b + 1) - 4 := by rw [hb]
  --   _ = 2 * (2 * b ^ 2 + 4 * b - 1) + 1 := by ring

example {p : ℤ} (hp : Odd p) : Odd (p ^ 2 + 3 * p - 5) := by
  dsimp [Odd] at *
  obtain ⟨a, ha⟩ := hp
  use 2 * a ^ 2 + 5 * a - 1
  rw [ha]
  ring
  -- calc
  --   p ^ 2 + 3 * p - 5
  --   _ = (2 * a + 1) ^ 2 + 3 * (2 * a + 1) - 5 := by rw [ha]
  --   _ = 2 * (2 * a ^ 2 + 5 * a - 1) + 1 := by ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  dsimp [Odd] at *
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use 2 * a * b + a + b
  rw [ha, hb]
  ring
  -- calc
  --   x * y
  --   _ = (2 * a + 1) * (2 * b + 1) := by rw [ha, hb]
  --   _ = 2 * (2 * a * b + a + b) + 1 := by ring

example (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  have h : Even (3 * n * (n + 1)) := by
    dsimp [Even]
    obtain h | h := Int.even_or_odd n
    { obtain ⟨a, ha⟩ := h
      use 3 * a * (n + 1)
      rw [ha]
      ring }
      -- calc
      --   3 * n * (n + 1)
      --   _ = 3 * (2 * a) * (n + 1) := by rw [ha]
      --   _ = 2 * (3 * a * (n + 1)) := by ring
    { obtain ⟨a, ha⟩ := h
      use 3 * n * (a + 1)
      rw [ha]
      ring }
      -- calc
      --   3 * n * (n + 1)
      --   _ = 3 * n * (2 * a + 1 + 1) := by rw [ha]
      --   _ = 2 * (3 * n * ( a + 1)) := by ring
  obtain ⟨a, ha⟩ := h
  use a - 1
  calc
    3 * n ^ 2 + 3 * n - 1
    _ = 3 * n * (n + 1) - 1 := by ring
    _ = 2 * a - 1 := by rw [ha]
    _ = 2 * (a - 1) + 1 := by ring

example (n : ℤ) : ∃ m ≥ n, Odd m := by
  obtain h | h := Int.even_or_odd n
  { obtain ⟨a, ha⟩ := h
    use n + 1
    constructor
    { extra }
    { use a
      rw [ha] } }
  { obtain ⟨a, ha⟩ := h
    use n + 2
    constructor
    { extra }
    { use a + 1
      rw [ha]
      ring } }

example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain ⟨a', ha'⟩ | ⟨a', ha'⟩ := Int.even_or_odd a
  { obtain ⟨b', hb'⟩ | ⟨b', hb'⟩ := Int.even_or_odd b
    { left
      use a' - b'
      rw [ha', hb']
      ring }
    { obtain ⟨c', hc'⟩ | ⟨c', hc'⟩ := Int.even_or_odd c
      { right; left
        use a' + c'
        rw [ha', hc']
        ring }
      { right; right
        use b' - c'
        rw [hb', hc']
        ring } } }
  { obtain ⟨b', hb'⟩ | ⟨b', hb'⟩ := Int.even_or_odd b
    { obtain ⟨c', hc'⟩ | ⟨c', hc'⟩ := Int.even_or_odd c
      { right; right
        use b' - c'
        rw [hb', hc']
        ring }
      { right; left
        use a' + c' + 1
        rw [ha', hc']
        ring } }
    { left
      use a' - b'
      rw [ha', hb']
      ring } }
