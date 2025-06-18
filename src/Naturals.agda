-- https://plfa.github.io/Naturals/

module Naturals where
  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

  -- Exercise: https://plfa.github.io/Naturals/#seven
  seven : ℕ
  seven = succ (succ (succ (succ (succ (succ (succ zero))))))

  {-# BUILTIN NATURAL ℕ #-}

  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl)
  open Eq.≡-Reasoning using (begin_; step-≡-∣; _∎)

  _+_ : ℕ → ℕ → ℕ
  zero + n = n
  (succ m) + n = succ (m + n)


  -- The type `2 + 3 ≡ 5` is the statement. The term provides "evidence" for the
  -- corresponding statement. The evidence is provided with a chain of equations
  -- starting with `begin_` and ending with "qued" ("Quod erat demonstrandum",
  -- "Come volevassi dimostrare") or "tombstone" ∎

  _ : 2 + 3 ≡ 5
  _ =
    begin
      2 + 3
    ≡⟨⟩    -- is shorthand for
      (succ (succ zero)) + (succ (succ (succ zero)))
    ≡⟨⟩    -- inductive case
      succ ((succ zero) + (succ (succ (succ zero))))
    ≡⟨⟩    -- inductive case
      succ (succ (zero + (succ (succ (succ zero)))))
    ≡⟨⟩    -- base case
      succ (succ (succ (succ (succ zero))))
    ≡⟨⟩    -- is longhand for
      5
    ∎

  -- A binary relation is said to be reflexive if every value relate to itself.
  -- Evidence that a value is equal to itself is written ~refl~

  _ : 2 + 3 ≡ 5
  _ = refl


  -- Exercise: https://plfa.github.io/Naturals/#plus-example
  -- Compute 3 + 4, writing out your reasoning as a chain of equations, using the equations for +.

  _ : 3 + 4 ≡ 7
  _ =
    begin
      3 + 4
    ≡⟨⟩
      succ (2 + 4)
    ≡⟨⟩
      succ (succ (1 + 4))
    ≡⟨⟩
      succ (succ (succ (zero + 4)))
    ≡⟨⟩
      succ (succ (succ 4))
    ≡⟨⟩
      succ (succ 5)
    ≡⟨⟩
      succ 6
    ≡⟨⟩
      7
    ∎

  -- Multiplication

  _*_ : ℕ → ℕ → ℕ
  zero * n = zero
  (succ m) * n = n + (n * m)

  _ : 2 * 3 ≡ 6
  _ = refl

  _ : 2 * 3 ≡ 6
  _ =
    begin
      2 * 3
    ≡⟨⟩
      (succ 1) * 3
    ≡⟨⟩
      3 + (1 * 3)
    ≡⟨⟩
      3 + ((succ zero) * 3)
    ≡⟨⟩
      3 + (3 + (zero * 3))
    ≡⟨⟩
      3 + (3 + zero)
    ≡⟨⟩
      3 + 3
    ≡⟨⟩
      6
    ∎

  -- Exercise: https://plfa.github.io/Naturals/#times-example

  _ : 3 * 4 ≡ 12
  _ =
    begin
      3 * 4
    ≡⟨⟩
      (succ 2) * 4
    ≡⟨⟩
      4 + (2 * 4)
    ≡⟨⟩
      4 + ((succ 1) * 4)
    ≡⟨⟩
      4 + (4 + (1 * 4))
    ≡⟨⟩
      4 + (4 + ((succ zero) * 4))
    ≡⟨⟩
      4 + (4 + (4 + (zero * 4)))
    ≡⟨⟩
      4 + (4 + (4 + zero))
    ≡⟨⟩
      4 + (4 + 4)
    ≡⟨⟩
      4 + 8
    ≡⟨⟩
      12
    ∎

  -- Exercise: https://plfa.github.io/Naturals/#power

  _^_ : ℕ → ℕ → ℕ
  m ^ 0 = 1
  m ^ (succ n) = m * (m ^ n)

  -- NOTE: refl doesn't work this time
  -- _ = 3 ^ 2 ≡ 9
  -- _ = refl

  _ = 3 ^ 2 ≡ 9
  _ = begin
      3 ^ 2
    ≡⟨⟩
      3 * (3 ^ 1)
    ≡⟨⟩
      3 * (3 * (3 ^ 0))
    ≡⟨⟩
      3 * (3 * 1)
    ≡⟨⟩
      3 * 3
    ≡⟨⟩
      9
    ∎

  _ = 3 ^ 4 ≡ 81
  _ = begin
      3 ^ 4
    ≡⟨⟩
      3 * (3 ^ 3)
    ≡⟨⟩
      3 * (3 * (3 ^ 2))
    ≡⟨⟩
      3 * (3 * (3 * (3 ^ 1)))
    ≡⟨⟩
      3 * (3 * (3 * (3 * (3 ^ 0))))
    ≡⟨⟩
      3 * (3 * (3 * (3 * 1)))
    ≡⟨⟩
      3 * (3 * (3 * 3))
    ≡⟨⟩
      3 * (3 * 9)
    ≡⟨⟩
      3 * 27
    ≡⟨⟩
      81
    ∎


  -- Monus

  _∸_ : ℕ → ℕ → ℕ
  m ∸ zero =  m
  zero ∸ succ n = zero
  succ m ∸ succ n = m ∸ n

  -- Exercise: https://plfa.github.io/Naturals/#monus-examples
  -- Compute 5 ∸ 3 and 3 ∸ 5

  _ : 5 ∸ 3 ≡ 2
  _ =
    begin
      5 ∸ 3
    ≡⟨⟩
      (succ 4) ∸ (succ 2)
    ≡⟨⟩
      4 ∸ 2
    ≡⟨⟩
      (succ 3) ∸ (succ 1)
    ≡⟨⟩
      3 ∸ 1
    ≡⟨⟩
      (succ 2) ∸ (succ zero)
    ≡⟨⟩
      2 ∸ 0
    ≡⟨⟩
      2
    ∎

  _ : 3 ∸ 5 ≡ zero
  _ =
    begin
      3 ∸ 5
    ≡⟨⟩
      (succ 2) ∸ (succ 4)
    ≡⟨⟩
      2 ∸ 4
    ≡⟨⟩
      (succ 1) ∸ (succ 3)
    ≡⟨⟩
      1 ∸ 3
    ≡⟨⟩
      (succ zero) ∸ (succ 2)
    ≡⟨⟩
      zero ∸ 2
    ≡⟨⟩
      zero
    ∎

  -- Fixities
  infixl 6  _+_  _∸_
  infixl 7  _*_

  -- Exercise: https://plfa.github.io/Naturals/#Bin
  -- Binary representation of numbers

  data Bin : Set where
    ⟨⟩ : Bin
    _O : Bin → Bin
    _I : Bin → Bin

  _ : Bin
  _ = ⟨⟩ I O I I

  -- Exercise: define the function `inc`

  inc : Bin → Bin
  inc ⟨⟩ = ⟨⟩ I
  inc (x O) = x I
  inc (x I) = (inc x) O

  _ : inc (⟨⟩ O) ≡ ⟨⟩ I
  _ = refl

  _ : inc (⟨⟩ I) ≡ ⟨⟩ I O
  _ = refl

  _ : inc (⟨⟩ I O) ≡ ⟨⟩ I I
  _ = refl

  _ : inc (⟨⟩ I I) ≡ ⟨⟩ I O O
  _ = refl

  _ : inc (⟨⟩ I O O) ≡ ⟨⟩ I O I
  _ = refl

  _ : inc (⟨⟩ I O I) ≡ ⟨⟩ I I O
  _ = refl

  _ : inc (⟨⟩ I I O) ≡ ⟨⟩ I I I
  _ = refl

  -- Exercise: define `to` and `from` functions

  to : ℕ → Bin
  to zero = ⟨⟩ O
  to (succ n) = inc (to n)

  from : Bin → ℕ
  from ⟨⟩ = zero
  from (n O) = 2 * (from n)
  from (n I) = 2 * (from n) + 1

  _ : from (to 0) ≡ 0
  _ = refl

  _ : from (to 1) ≡ 1
  _ = refl

  _ : from (to 2) ≡ 2
  _ = refl

  _ : from (to 3) ≡ 3
  _ = refl

  _ : from (to 4) ≡ 4
  _ = refl
