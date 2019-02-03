module Exercises where

open import level
open import IO

data 𝔹 : Set where
  tt : 𝔹
  ff : 𝔹

infix 7 ~_
infix 6 _xor_
infixr 6 _&&_
infixr 5 _||_
infix 4 if_then_else_
infix 4 _imp_

~_ : 𝔹 -> 𝔹
~ tt = ff
~ ff = tt

_&&_ : 𝔹 -> 𝔹 -> 𝔹
tt && b = b
ff && b = ff

_||_ : 𝔹 -> 𝔹 -> 𝔹
tt || b = tt
ff || b = b

if_then_else_ : ∀ {ℓ} {A : Set ℓ} -> 𝔹 -> A -> A -> A
if tt then t else f = t
if ff then t else f = f

_xor_ : 𝔹 -> 𝔹 -> 𝔹
tt xor ff = tt
ff xor tt = tt
tt xor tt = ff
ff xor ff = ff

_imp_ : 𝔹 -> 𝔹 -> 𝔹
tt imp b = b
ff imp b = tt

data Day : Set where
  Monday    : Day
  Tuesday   : Day
  Wednesday : Day
  Thursday  : Day
  Friday    : Day
  Saturday  : Day
  Sunday    : Day

nextday : Day -> Day
nextday Monday    = Tuesday
nextday Tuesday   = Wednesday
nextday Wednesday = Thursday
nextday Thursday  = Friday
nextday Friday    = Saturday
nextday Saturday  = Sunday
nextday Sunday    = Monday

data Suit : Set where
  Spade : Suit
  Clover : Suit
  Hearts : Suit
  Diamond : Suit

is-red : Suit -> 𝔹
is-red Hearts = tt
is-red Diamond = tt
is-red _ = ff

-- main : IO _
main = run (putStrLn "Hello World!")

