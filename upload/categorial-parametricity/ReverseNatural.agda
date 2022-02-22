module ReverseNatural where

-- Lots (basically all, actually) of this code is effectively stolen from
-- the old 1Lab: https://old.1lab.dev

open import Agda.Primitive
  renaming (Set to Type; Setω to Typeω)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; subst)
open Eq.≡-Reasoning

-- Function extensionality:
-- Two functions are equal only if they're equal for all inputs.
postulate
  fun-ext : ∀ {ℓ ℓ' : _} {X : Type ℓ} {Y : X → Type ℓ'} {f g : (x : X) → Y x}
    → (∀ (x : X) → f x ≡ g x) → f ≡ g

-- A category C consists of:
record Category (o h : Level) : Type (lsuc (o ⊔ h)) where
  field
    -- a collection of objects Ob(C),
    Ob : Type o
    -- a collection of morphisms Hom(x, y) for each object x, y,
    Hom : Ob → Ob → Type h

    -- a binary operation ∘ with the following type,
    _∘_ : {x y z : _} → Hom y z → Hom x y → Hom x z

    -- and an identity morphism for each object
    id : {x : _} → Hom x x

    -- such that identity is subject to the following laws (so, it behaves
    -- like you would want an identity to),
    idl : {x y : _} → (f : Hom x y) → id ∘ f ≡ f
    idr : {x y : _} → (f : Hom x y) → f ∘ id ≡ f

    -- and composition is associative.
    assoc : {w x y z : _} (f : Hom y z) (g : Hom x y) (h : Hom w x)
      → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

  infixr 40 _∘_

-- Types form a category.
Types : (o : _) → Category (lsuc o) o
Category.Ob (Types o) = Type o
Category.Hom (Types o) A B = A → B
Category.id (Types o) x = x
Category._∘_ (Types o) f g x = f (g x)
Category.idl (Types o) f = refl
Category.idr (Types o) f = refl
Category.assoc (Types o) f g h = refl

-- A Functor F : C → D consists of:
record Functor {o₁ h₁ o₂ h₂} (C : Category o₁ h₁) (D : Category o₂ h₂)
  : Type (o₁ ⊔ h₁ ⊔ o₂ ⊔ h₂) where
  private
    module C = Category C
    module D = Category D

  field
    -- a map between Ob(C) and Ob(D),
    F-Ob : C.Ob → D.Ob
    -- a map taking morphisms in C (x → y) to morphisms in D (F(x) → F(y)),
    F-Hom : {x y : _} → C.Hom x y → D.Hom (F-Ob x) (F-Ob y)

    -- such that F(id1) = id2 where id1 is in C and id2 is in D,
    F-id : {x : _} → F-Hom (C.id {x}) ≡ D.id
    -- and such that we are homomorphic across composition.
    F-∘ : {x y z : _} (f : C.Hom y z) (g : C.Hom x y)
          → F-Hom (f C.∘ g) ≡ F-Hom f D.∘ F-Hom g
-- Note that we lose some notational convenience by representing this as a pair
-- of maps. Usually, we just write F for both, and it's inferred from context.

-- For functors F, G : C → D, a natural transformation η : F ⇒ G consists of:
record _⇒_ {o₁ h₁ o₂ h₂} {C : Category o₁ h₁} {D : Category o₂ h₂}
  (F G : Functor C D) : Type (o₁ ⊔ h₁ ⊔ h₂) where
  private
    module F = Functor F
    module G = Functor G
    module C = Category C
    module D = Category D

  field
    -- a dependent function taking objects x of C,
    -- and returning a morphism of D between F(x) and G(x),
    η : (x : _) → Category.Hom D (F.F-Ob x) (G.F-Ob x)
    -- such that the diagram in the slides commutes
    naturality : (x y : _) (f : C.Hom x y)
      → η y D.∘ F.F-Hom f ≡ G.F-Hom f D.∘ η x

-- Lists are defined as usual.
data List {ℓ} (A : Type ℓ) : Type ℓ where
  empty : List A
  cons : A → List A → List A

_++_ : {ℓ : _} {A : Type ℓ} → List A → List A → List A
empty ++ ys = ys
cons x xs ++ ys = cons x (xs ++ ys)

map : {ℓ ℓ′ : _} {A : Type ℓ} {B : Type ℓ′} → (A → B) → List A → List B
map f empty = empty
map f (cons x xs) = cons (f x) (map f xs)

reverse : {ℓ : _} {A : Type ℓ} → List A → List A
reverse empty = empty
reverse (cons x xs) = reverse xs ++ (cons x empty)

-- map is a functor from Types to Types (where objects are sent to lists
-- of that object).
map-id : {ℓ : _} {A : Type ℓ} (xs : List A) → map (λ x → x) xs ≡ xs
map-id empty = refl
map-id (cons x xs) = cong (cons x) (map-id xs)

map-∘ : {ℓ ℓ′ ℓ′′ : _} {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ′′}
  {f : B → C} {g : A → B} (xs : List A)
  → map (λ x → f (g x)) xs ≡ map f (map g xs)
map-∘ empty = refl
map-∘ (cons x xs) = cong (cons _) (map-∘ xs)

List-functor : {ℓ : _} → Functor (Types ℓ) (Types ℓ)
Functor.F-Ob List-functor = List
Functor.F-Hom List-functor = map
Functor.F-id List-functor = fun-ext map-id
Functor.F-∘ List-functor f g = fun-ext map-∘

-- reverse is a natural transformation from map to map.
map-++ : {ℓ ℓ′ : _} {A : Type ℓ} {B : Type ℓ′} {f : A → B} (xs ys : List A)
  → map f (xs ++ ys) ≡ (map f xs) ++ (map f ys)
map-++ empty ys = refl
map-++ {f = f} (cons x xs) ys = cong (cons (f x)) (map-++ xs ys)

reverse-naturality : {ℓ ℓ′ : _} {A : Type ℓ} {B : Type ℓ′} → (f : A → B)
  → (l : List A) → map f (reverse l) ≡ reverse (map f l)
reverse-naturality f empty = refl
reverse-naturality f (cons x xs) =
  begin
    map f (reverse (cons x xs)) ≡⟨⟩
    map f (reverse xs ++ (cons x empty)) ≡⟨ map-++ (reverse xs) (cons x empty) ⟩
    map f (reverse xs) ++ map f (cons x empty) ≡⟨⟩
    map f (reverse xs) ++ cons (f x) empty ≡⟨ cong₂ _++_ (reverse-naturality f xs) refl ⟩
    reverse (map f xs) ++ cons (f x) empty ≡⟨⟩
    reverse (map f (cons x xs))
  ∎

-- Don't ask me about this level meta. I don't know.
reverse-natural : {ℓ : _} → List-functor {ℓ = ℓ} ⇒ List-functor
_⇒_.η reverse-natural x = reverse
_⇒_.naturality reverse-natural x y f = sym (fun-ext (reverse-naturality f))
