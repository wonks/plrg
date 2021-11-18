open import Data.Unit
open import Data.Nat
open import Data.Product
  using (_×_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
import Relation.Binary.PropositionalEquality as Eq
open import Function using (_∘_)
open Eq using (_≡_; refl; cong; cong₂; sym)
open Eq.≡-Reasoning

module Tutorial where

{- Extensionality asserts that the only way to
   distinguish functions is by applying them;
   if two functions applied to the same argument
   always yield the same result, then they are
   the same function. - plfa -}
postulate
  extensionality : ∀ {X Y : Set} {f g : X → Y}
    → (∀ (x : X) → f x ≡ g x)
      -----------------------
    → f ≡ g

module DT where
  open import Data.Fin
  open import Data.Maybe

  {-
    Dependently typed programming.
  -}

  -- Value depends on type.
  t : Set
  t = Maybe ⊤

  -- Type depends on value.
  a : Fin 42
  a = zero

  -- Yes we can Unicode.
  a₁ a₂ : Fin 42
  a₁ = suc zero; a₂ = fromℕ 41

module ListReasoning where

  open import Data.List
  open import Data.List.Properties

  map-snoc : ∀ {X Y : Set}
    → (f : X → Y)
    → (x : X)
    → (xs : List X)
    → map f (xs ∷ʳ x) ≡ (map f xs) ∷ʳ (f x)
  map-snoc f x [] = refl
  map-snoc f x (x₁ ∷ xs) =
    begin
      f x₁ ∷ map f (xs ++ [ x ])
        ≡⟨ cong (λ □ → f x₁ ∷ □) (map-++-commute f xs (x ∷ [])) ⟩
      f x₁ ∷ ((map f xs) ++ [ f x ])
        ≡⟨⟩
      (f x₁ ∷ map f xs) ∷ʳ f x
        ∎

  map∘reverse≡reverse∘map : ∀ {X Y : Set}
    → (f : X → Y)
    → (xs : List X)
    → ((map f) ∘ reverse) xs ≡ (reverse ∘ (map f)) xs
  map∘reverse≡reverse∘map f [] = refl
  map∘reverse≡reverse∘map f (x ∷ xs) =
    let iH = map∘reverse≡reverse∘map f xs in
    begin
      ((map f) ∘ reverse) (x ∷ xs)
        ≡⟨ cong (map f) (unfold-reverse x xs) ⟩
      map f (reverse xs ∷ʳ x)
        ≡⟨ map-snoc f x (reverse xs) ⟩
      (map f (reverse xs)) ∷ʳ (f x)
        ≡⟨ cong (λ □ → □ ∷ʳ f x) iH ⟩
      reverse (map f xs) ∷ʳ (f x)
        ≡⟨ sym (unfold-reverse (f x) (map f xs)) ⟩
      (reverse ∘ (map f)) (x ∷ xs)
        ∎

  variable
    A B : Set

  postulate
    a : A → B

  r : ∀ (X : Set) → List X → List X
  r X = reverse

  a* : List A → List B
  a* = map a

  a*∘r≡r∘a* : (a* ∘ (r A)) ≡ ((r B) ∘ a*)
  a*∘r≡r∘a* = extensionality (map∘reverse≡reverse∘map a)

module FibExtEqual where

  fib-spec : ℕ → ℕ
  fib-spec 0             = 0
  fib-spec 1             = 1
  fib-spec (suc (suc k)) = (fib-spec k) + (fib-spec (suc k))

  swap-add : ℕ × ℕ → ℕ × ℕ
  swap-add ⟨ n , m ⟩ = ⟨ m , n + m ⟩

  -- repeat n times
  repeat : ∀ {A : Set} → (A → A) → A → ℕ → A
  repeat f z zero    = z
  repeat f z (suc n) = repeat f (f z) n

  -- O(n) time
  fib : ℕ → ℕ
  fib n =
    let ⟨ m , _ ⟩ = repeat swap-add ⟨ 0 , 1 ⟩ n in m

  -- fⁿ (f a) ≡ f (fⁿ a)
  repeat-eq : ∀ {A} (f : A → A) a n → repeat f (f a) n ≡ f (repeat f a n)
  repeat-eq f a zero    = refl
  repeat-eq f a (suc n) = repeat-eq f (f a) n

  correctness : ∀ n
    → repeat swap-add ⟨ 0 , 1 ⟩ n ≡ ⟨ fib-spec n , fib-spec (suc n) ⟩
  correctness zero = refl
  correctness (suc n) rewrite repeat-eq swap-add ⟨ 0 , 1 ⟩ n =
    step n (correctness n)
    where
    step : ∀ {p} (n : ℕ)
      → p ≡ ⟨ fib-spec n , fib-spec (suc n) ⟩
        -----------------------------------------------------------
      → swap-add p ≡ ⟨ fib-spec (suc n) , fib-spec (suc (suc n)) ⟩
    step n refl = refl

  fib-correct : fib ≡ fib-spec
  fib-correct = extensionality (λ n → cong proj₁ (correctness n))

module Isomorphism where
  infix 0 _≃_
  record _≃_ (A B : Set) : Set where
    field
      to      : A → B
      from    : B → A
      from∘to : ∀ (x : A) → from (to x) ≡ x
      to∘from : ∀ (y : B) → to (from y) ≡ y

  {-
    *Pop quiz:* How is this different from the definition in PLFA?
    Why does the latter one require a canonical form?
  -}
  open import Data.Nat.Binary
    renaming (zero to zeroᵇ; suc to sucᵇ; _*_ to _*ᵇ_; _+_ to _+ᵇ_)
    hiding (toℕ; fromℕ; fromℕ')
  open import Data.Nat.Properties
    using (*-distribˡ-+; +-identityʳ; +-suc)
  open import Data.Nat.Binary.Properties
    using (x+suc[y]≡suc[x]+y)
    renaming (suc-+ to suc-+ᵇ)

  b : ℕᵇ
  -- say 101 = 1 + 2 * (2 * (1 + 0))
  b = 1+[2 2[1+ zeroᵇ ] ]

  toℕ : ℕᵇ → ℕ
  toℕ zeroᵇ    =  0
  toℕ 2[1+ b ] =  2 * (suc (toℕ b))
  toℕ 1+[2 b ] =  suc (2 * (toℕ b))

  fromℕ : ℕ → ℕᵇ
  fromℕ zero    = zeroᵇ
  fromℕ (suc n) = sucᵇ (fromℕ n)

  _ : toℕ b ≡ 5
  _ = refl

  toℕ-suc : ∀ b → toℕ (sucᵇ b) ≡ suc (toℕ b)
  toℕ-suc zeroᵇ    =  refl
  toℕ-suc 2[1+ b ] = cong (suc ∘ (_*_ 2)) (toℕ-suc b)
  toℕ-suc 1+[2 b ] = *-distribˡ-+ 2 1 (toℕ b)

  to∘from : ∀ (n : ℕ) → toℕ (fromℕ n) ≡ n
  to∘from zero = refl
  to∘from (suc n) =
    begin
      toℕ (fromℕ (suc n))
        ≡⟨⟩ {- By definition -}
      toℕ (sucᵇ (fromℕ n))
        ≡⟨ toℕ-suc (fromℕ n) ⟩
      suc (toℕ (fromℕ n))
        ≡⟨ cong suc (to∘from n) ⟩
      suc n
        ∎

  1+2b : ∀ b → sucᵇ (b +ᵇ b) ≡ 1+[2 b ]
  1+2b zeroᵇ = refl
  1+2b 2[1+ b ] = cong (λ □ → 1+[2 (sucᵇ □) ]) (1+2b b)
  1+2b 1+[2 b ] = cong 1+[2_] (1+2b b)

  -- We cheat a bit here.
  fromℕ-distrib-+ : ∀ n → fromℕ (n + n) ≡ (fromℕ n) +ᵇ (fromℕ n)
  fromℕ-distrib-+ zero = refl
  fromℕ-distrib-+ (suc n)
    rewrite +-suc n n
          | suc-+ᵇ (fromℕ n) (sucᵇ (fromℕ n))
          | x+suc[y]≡suc[x]+y (fromℕ n) (fromℕ n)
          | suc-+ᵇ (fromℕ n) (fromℕ n) =
      cong (λ □ → sucᵇ (sucᵇ □)) (fromℕ-distrib-+ n)

  from∘to : ∀ (b : ℕᵇ) → fromℕ (toℕ b) ≡ b
  from∘to zeroᵇ = refl
  from∘to 2[1+ b ] rewrite +-identityʳ (toℕ b) =
    begin
      let iH : fromℕ (toℕ b) ≡ b
          iH = from∘to b in
      sucᵇ (fromℕ (toℕ b + suc (toℕ b)))
        ≡⟨ cong (λ □ → sucᵇ (fromℕ □)) (+-suc (toℕ b) (toℕ b)) ⟩
      sucᵇ (fromℕ (suc (toℕ b + (toℕ b))))
        ≡⟨⟩
      sucᵇ (sucᵇ (fromℕ (toℕ b + toℕ b)))
        ≡⟨ cong (λ □ → sucᵇ (sucᵇ □)) (fromℕ-distrib-+ (toℕ b)) ⟩
      sucᵇ (sucᵇ (fromℕ (toℕ b) +ᵇ fromℕ (toℕ b)))
        ≡⟨ cong₂ (λ □₁ □₂ → sucᵇ (sucᵇ (□₁ +ᵇ □₂))) iH iH ⟩
      sucᵇ (sucᵇ (b +ᵇ b))
        ≡⟨ cong sucᵇ (1+2b b) ⟩
      sucᵇ 1+[2 b ]
        ≡⟨⟩
      2[1+ b ]
        ∎
    {-
    -- *Pop quiz:* why doesn't this one work?
    let iH = from∘to 1+[2 b ] in
    begin
      sucᵇ (fromℕ (toℕ b + suc (toℕ b + 0)))
        ≡⟨ cong (λ □ → sucᵇ (fromℕ □)) (+-suc (toℕ b) (toℕ b + 0)) ⟩
      sucᵇ (fromℕ (suc (toℕ b + (toℕ b + 0))))
        ≡⟨⟩
      sucᵇ (sucᵇ (fromℕ (toℕ b + (toℕ b + 0))))
        ≡⟨ cong sucᵇ iH ⟩
      sucᵇ 1+[2 b ]
        ≡⟨⟩
      2[1+ b ]
        ∎
    -}
  from∘to 1+[2 b ] rewrite +-identityʳ (toℕ b) =
    let iH : fromℕ (toℕ b) ≡ b
        iH = from∘to b in
    begin
      sucᵇ (fromℕ (toℕ b + toℕ b))
        ≡⟨ cong sucᵇ (fromℕ-distrib-+ (toℕ b)) ⟩
      sucᵇ (fromℕ (toℕ b) +ᵇ fromℕ (toℕ b))
        ≡⟨ cong₂ (λ □₁ □₂ → sucᵇ (□₁ +ᵇ □₂)) iH iH ⟩
      sucᵇ (b +ᵇ b)
        ≡⟨ 1+2b b ⟩
      1+[2 b ]
        ∎

  ℕᵇ≃ℕ : ℕᵇ ≃ ℕ
  ℕᵇ≃ℕ = record {
           to = toℕ ;
           from = fromℕ ;
           from∘to = from∘to ;
           to∘from = to∘from
         }

{-
  Working with proof assistants can be tedious and annoying at times:
  https://twitter.com/pruvisto/status/971670088574210048
  So good luck! :-P
-}
