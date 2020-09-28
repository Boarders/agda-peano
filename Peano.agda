module Peano where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; _≢_; cong; trans)

_∘_ : ∀ {A B C : Set} -> (g : B -> C) -> (f : A -> B) -> A -> C
_∘_ g f a = g (f a)

data ⊥ : Set where

data ℕ : Set where
  Zero : ℕ
  Succ : ℕ -> ℕ

ℕ-refl : ∀ (n : ℕ) -> n ≡ n
ℕ-refl n = refl

ℕ-symm : ∀ (n m : ℕ) -> n ≡ m -> m ≡ n
ℕ-symm n m eq rewrite eq = refl

ℕ-trans : ∀ (m n r : ℕ) -> m ≡ n -> n ≡ r -> m ≡ r
ℕ-trans n m r m≡n n≡r rewrite m≡n | n≡r = refl

Succ-inj : ∀ (n m : ℕ) -> (Succ n) ≡ (Succ m) -> n ≡ m
Succ-inj n .n refl = refl

ℕ-induction :
  ∀ (P : ℕ -> Set) (a : ℕ)
  -> P Zero
  -> (∀ {b : ℕ} -> P b -> P (Succ b))
  -> P a
ℕ-induction P Zero p[zero] p[succ] = p[zero]
ℕ-induction P (Succ n) p[zero] p[succ] 
  = p[succ] (ℕ-induction P n p[zero] p[succ])


record Peano (N : Set) (_≃_ : N -> N -> Set) : Set₁ where
  field
    zero : N
    succ : N -> N
    reflexivity : forall (a : N) -> a ≃ a
    symmetry    : forall (a b : N) -> a ≃ b -> b ≃ a
    transivity  : forall (a b c : N) -> a ≃ b -> b ≃ c -> a ≃ c
    s-injective : forall (a b : N) -> (succ a) ≃ (succ b) -> a ≃ b
    zero≠succ   : forall (a : N) -> zero ≃ (succ a) -> ⊥
    induction   : 
     ∀ (P : N -> Set) (a : N)
       -> P zero 
       -> (∀ {b : N} -> P b -> P (succ b))
       -> P a
    induction-zero :      
      ∀ (P : N -> Set)
       -> (z : P zero)
       -> (s : ∀ {b : N} -> P b -> P (succ b))
       -> (induction P zero z s) ≡ z
    induction-succ :      
      ∀ (P : N -> Set) (a : N)
       -> (z : P zero)
       -> (s : ∀ {b : N} -> P b -> P (succ b))
       -> (induction P (succ a) z s) ≡ s (induction P a z s)

ℕ-Peano : Peano ℕ _≡_
ℕ-Peano = record
  { zero = Zero
  ; succ = Succ
  ; reflexivity = ℕ-refl
  ; symmetry = ℕ-symm
  ; transivity = ℕ-trans
  ; s-injective = Succ-inj
  ; zero≠succ = λ n ()
  ; induction = ℕ-induction
  ; induction-zero = λ P z s   -> refl
  ; induction-succ = λ P a z s -> refl
  }

from-ℕ : ∀ {N : Set} {_≃_ : N -> N -> Set} -> Peano N _≃_ -> ℕ -> N
from-ℕ peano Zero = zero
  where
  open Peano peano using (zero)
from-ℕ peano (Succ n) = succ (from-ℕ peano n)
  where
  open Peano peano using (succ)

to-ℕ : ∀ {N : Set} {_≃_ : N -> N -> Set} -> Peano N _≃_ -> N -> ℕ
to-ℕ peano n = induction (λ _ -> ℕ) n Zero λ prev -> Succ prev
  where
  open Peano peano using (induction)


from-zero :  
  ∀ {N : Set} -> (peano : Peano N _≡_) ->
  (Peano.induction peano (λ _ → ℕ) (Peano.zero peano) Zero (λ prev → Succ prev)) ≡ Zero
from-zero peano = induction-zero (λ _ -> ℕ) Zero Succ
  where
  open Peano peano using (induction-zero)


from∘to : 
  ∀ {N : Set} -> (peano : Peano N _≡_) -> (n : N) ->
  from-ℕ peano (to-ℕ peano n) ≡ n
from∘to {N} peano n rewrite from-zero peano = 
    induction 
      (λ n -> from-ℕ peano (to-ℕ peano n) ≡ n) 
      n 
      (zero-lem {_} {peano} )
      (λ {prev} -> succ-lem {N} {peano} prev )
  where
  open Peano peano using (induction)
  zero-lem : ∀ {N} {peano : Peano N _≡_}→
           from-ℕ peano
           (Peano.induction peano (λ _ → ℕ) (Peano.zero peano) Zero
            (λ prev → Succ prev))
           ≡ Peano.zero peano
  zero-lem {_} {peano} =
    let
      pf1 : 
        from-ℕ peano
          (Peano.induction peano (λ _ → ℕ) (Peano.zero peano) Zero (λ prev → Succ prev))
        ≡ from-ℕ peano Zero
      pf1 =
        cong (from-ℕ peano) (Peano.induction-zero peano (λ _ → ℕ) Zero Succ)

      pf2 :
        from-ℕ peano Zero ≡ Peano.zero peano
      pf2 = refl
    in
      trans pf1 pf2

  succ-lem : ∀ {N} {peano : Peano N _≡_} (prev : N) →
           from-ℕ peano
           (Peano.induction peano (λ _ → ℕ) prev Zero (λ prev → Succ prev))
           ≡ prev →
           from-ℕ peano
           (Peano.induction peano (λ _ → ℕ) (Peano.succ peano prev) Zero
            (λ prev → Succ prev))
           ≡ Peano.succ peano prev
  succ-lem {N} {peano} prev pf = 
    let
      pf1 :
        from-ℕ {N} peano
          (Peano.induction peano (λ _ → ℕ) (Peano.succ peano prev) Zero
          (λ prev → Succ prev))
        ≡ from-ℕ peano
            (Succ (Peano.induction peano (λ _ -> ℕ) prev Zero Succ))

      pf1 = cong (from-ℕ peano) 
              (Peano.induction-succ peano (λ _ -> ℕ) prev Zero Succ)

      pf2 : 
        from-ℕ peano
          (Succ (Peano.induction peano (λ _ -> ℕ) prev Zero Succ))
        ≡ (Peano.succ peano prev)
      pf2 = cong (Peano.succ peano) pf
    in 
      trans pf1 pf2

to∘from : 
  ∀ {N : Set} {_≃_ : N -> N -> Set} -> (peano : Peano N _≃_) -> (n : ℕ) ->
    to-ℕ peano (from-ℕ peano n) ≡ n
to∘from peano Zero =  (induction-zero (λ _ -> ℕ) Zero Succ)
  where
  open Peano peano using (induction-zero)
to∘from peano (Succ n) 
  rewrite 
    ((Peano.induction-succ peano) (λ _ -> ℕ) (from-ℕ peano n) Zero (λ prev -> Succ prev))
  | to∘from peano n
  = refl



data NatP (r : Set) : Set where
  ZeroP : NatP r
  SuccP : r -> NatP r

record Functor (F : Set -> Set) : Set₁ where
  constructor Func
  field
    Ar : ∀ {A B : Set} -> (f : A -> B) -> F A -> F B

NatP-Functor : Functor NatP
NatP-Functor = Func map
  where
  map : ∀ {A} {B} → (A → B) → NatP A → NatP B
  map f ZeroP = ZeroP
  map f (SuccP x) = SuccP (f x)
  

record Alg (F : Set -> Set) (A : Set) : Set where
  constructor AlgCon
  field
    μ : F A -> A

record Alg-Homo 
  (A B : Set) {F : Set -> Set} (f : Functor F) (FA : Alg F A) (FB : Alg F B) : Set₁ where
  constructor AlgH
  field
    ↓-map : A -> B
    ↑-law : ∀ (fa : F A) -> ↓-map (Alg.μ FA fa) ≡ (Alg.μ FB) (Functor.Ar f ↓-map fa)

ℕ-Alg : Alg NatP ℕ
ℕ-Alg = record { μ = alg }
  where
  alg : NatP ℕ -> ℕ
  alg ZeroP = Zero
  alg (SuccP x) = Succ x


ℕ-w-init 
  : ∀ {A : Set} 
  -> (FA : Alg NatP A)
  -> Alg-Homo ℕ A (NatP-Functor) ℕ-Alg FA
ℕ-w-init {A} FA = AlgH ↓-map ↓-law
  where
--  open Functor {{...}}
  open Alg     FA public
  ↓-map : ℕ → A
  ↓-map Zero = μ ZeroP
  ↓-map (Succ n) = μ (SuccP (↓-map n))

  ↓-law : (na : NatP ℕ) →
    ↓-map (Alg.μ ℕ-Alg na) ≡
    Alg.μ FA (Functor.Ar NatP-Functor ↓-map na)
  ↓-law ZeroP = refl
  ↓-law (SuccP x) = refl


ℕ-init-uniq
  : ∀ {A : Set} 
  -> (FA : Alg NatP A)
  -> (alg-hom : Alg-Homo ℕ A (NatP-Functor) ℕ-Alg FA)
  -> ∀ (n : ℕ) 
  -> (Alg-Homo.↓-map alg-hom n) 
   ≡ (Alg-Homo.↓-map (ℕ-w-init FA) n)
ℕ-init-uniq FA alg-hom Zero = ↑-law ZeroP
  where
    open Alg-Homo alg-hom public
ℕ-init-uniq FA alg-hom (Succ n) = 
  let
    pf1 :  ↓-map (Succ n) ≡ μ (SuccP (↓-map n))
    pf1 = ↑-law (SuccP n)

    pf2 :  μ (SuccP (↓-map n)) ≡ μ (SuccP (Alg-Homo.↓-map (ℕ-w-init FA) n))
    pf2 = cong (μ ∘ SuccP) (ℕ-init-uniq FA alg-hom n)
  in
    trans pf1 pf2
  where
    open Alg FA public
    open Alg-Homo alg-hom public


  
