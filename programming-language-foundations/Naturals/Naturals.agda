module Naturals where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

-- ℕ  U+2115  DOUBLE-STRUCK CAPITAL N (\bN)
-- →  U+2192  RIGHTWARDS ARROW (\to, \r, \->)
-- ∸  U+2238  DOT MINUS (\.-)
-- ≡  U+2261  IDENTICAL TO (\==)
-- ⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
-- ⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
-- ∎  U+220E  END OF PROOF (\qed)

data ℕ : Set where
  zero : ℕ
  succ : ℕ -> ℕ

-- Tells Agda that ℕ corresponds to Natural numbers.
-- Enables more efficient internal representation of naturals.
{-# BUILTIN NATURAL ℕ  #-} 

seven : ℕ
seven = succ (succ (succ (succ (succ (succ (succ zero))))))

_+_ : ℕ -> ℕ -> ℕ
zero + n = n
succ m + n = succ (m + n)

infixl 6 _+_

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    (succ (succ zero)) + (succ (succ (succ zero)))
  ≡⟨⟩
    succ ((succ zero) + (succ (succ (succ zero))))
  ≡⟨⟩
    succ (succ (zero + (succ (succ (succ zero)))))
  ≡⟨⟩
    succ (succ (succ (succ (succ zero))))
  ≡⟨⟩
    5
  ∎

_ : 2 + 3 ≡ 5
_ = refl

_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    (succ (succ (succ zero))) + (succ (succ (succ (succ zero))))
  ≡⟨⟩
    succ ((succ (succ zero)) + (succ (succ (succ (succ zero)))))
  ≡⟨⟩
    succ (succ ((succ zero) + (succ (succ (succ (succ zero))))))
  ≡⟨⟩
    succ (succ (succ (zero + (succ (succ (succ (succ zero)))))))
  ≡⟨⟩
    succ (succ (succ (succ (succ (succ (succ zero))))))
  ≡⟨⟩
    7
  ∎

_*_ : ℕ -> ℕ -> ℕ
zero * n = zero
succ m * n = n + (m * n)

infixl 7 _*_

_ : 3 * 4 ≡ 12
_ =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    12
  ∎

_^_ : ℕ -> ℕ -> ℕ
n ^ zero = 1
n ^ succ m = n * (n ^ m)

infixl 6 _^_


_∸_ : ℕ -> ℕ -> ℕ
m ∸ zero = m
zero ∸ succ n = zero
succ m ∸ succ n = m ∸ n

_ : 5 ∸ 3 ≡ 2
_ =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎

_ : 3 ∸ 5 ≡ 0
_ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0
  ∎

_plus_ : ℕ -> ℕ -> ℕ
zero plus n = n
succ m plus n = succ (m + n)

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin : Set where
  nil : Bin
  x0_ : Bin -> Bin
  x1_ : Bin -> Bin

-- Recursion: LSB to MSB
inc : Bin -> Bin
inc nil = x1 nil
inc (x0 bs) = x1 bs
inc (x1 bs) = x0 (inc bs)

to : ℕ -> Bin
to 0 = nil
to (succ m) = inc (to m)

from' : Bin -> ℕ -> ℕ
from' nil _ = 0
from' (x0 bs) n = from' bs (n + 1)
from' (x1 bs) n = (2 ^ n) + (from' bs (n + 1))

from : Bin -> ℕ
from bs = from' bs 0
 
