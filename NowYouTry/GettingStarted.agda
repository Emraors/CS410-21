module NowYouTry.GettingStarted where

open import Data.Nat
-- This is a comment

{- And this is a multiline comment.

   Useful key-bindings:

   C-c C-l     load file

 -}

const : {A B : Set} -> A -> B -> A
const = λ a b -> a

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

append : {A : Set} -> List A -> List A -> List A
append [] ys = ys
append (x :: xs) ys = x :: (append xs ys)

data _⊎_ (A B : Set) : Set where
  inj₁ : A -> A ⊎ B
  inj₂ : B -> A ⊎ B

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B
open _×_

swap : {A B : Set} → A × B -> B × A
swap (a , b) = b , a

distribute : {A B C : Set} → A × (B ⊎ C) -> (A × B) ⊎ (A × C)
distribute (a , inj₁ b) = inj₁ (a , b)
distribute (a , inj₂ c) = inj₂ (a , c)

distributeInverse : {A B C : Set} → (A × B) ⊎ (A × C) -> A × (B ⊎ C)
distributeInverse (inj₁ (a , b)) =  a , inj₁ b 
distributeInverse (inj₂ (c , d)) = c , inj₂ d


--∣ My notes


data Vec (A : Set) : ℕ → Set where
  []   : Vec A 0
  _::_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

_++_ :  {A : Set} {n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

head : {A : Set} {n : ℕ} -> Vec A (suc n) -> A
head (x :: _) = x

tail : {A : Set} {n : ℕ} → Vec A (suc n) → Vec A n
tail (_ :: xs) = xs


data Fin : ℕ -> Set where
  zero : {n : ℕ} -> Fin (suc n)
  suc  : {n : ℕ} -> Fin n -> Fin (suc n)

_!!_ : ∀ {A : Set} {n : ℕ} -> Vec A n -> Fin n -> A
(x :: _) !! zero = x
(_ :: xs) !! (suc i) = xs !! i
