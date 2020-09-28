module Peano where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; _≢_; cong; trans; sym)


_∘_ : ∀ {A B C : Set} -> (g : B -> C) -> (f : A -> B) -> A -> C
_∘_ g f a = g (f a)

data ⊥ : Set where

data ℕ : Set where
  Zero : ℕ
  Succ : ℕ -> ℕ

record Rel (A : Set) : Set₁ where
  field
    _≃_ : A -> A -> Set
    reflexivity  : forall (a : A) -> a ≃ a
    symmetry     : forall (a b : A) -> a ≃ b -> b ≃ a
    transitivity : forall (a b c : A) -> a ≃ b -> b ≃ c -> a ≃ c  

open Rel {{...}} public
liftEq : ∀ {A : Set}  {{r : Rel A}} -> (a b : A) -> a ≡ b -> (Rel._≃_ r a b)
liftEq {A} a .a refl = reflexivity a
--  where
--  open Rel rel using (reflexivity)


ℕ-refl : ∀ (n : ℕ) -> n ≡ n
ℕ-refl n = refl

ℕ-symm : ∀ (n m : ℕ) -> n ≡ m -> m ≡ n
ℕ-symm n m eq rewrite eq = refl

ℕ-trans : ∀ (m n r : ℕ) -> m ≡ n -> n ≡ r -> m ≡ r
ℕ-trans n m r m≡n n≡r rewrite m≡n | n≡r = refl

Succ-inj : ∀ (n m : ℕ) -> (Succ n) ≡ (Succ m) -> n ≡ m
Succ-inj n .n refl = refl



instance
  ≡-Nat : Rel ℕ
  _≃_ {{≡-Nat}} = _≡_
  reflexivity {{≡-Nat}} = ℕ-refl
  symmetry {{≡-Nat}} = ℕ-symm
  transitivity {{≡-Nat}} = ℕ-trans

≡-Set : (A : Set) -> Rel A
≡-Set A = 
  record 
    { _≃_ = _≡_ 
    ; reflexivity = λ a → refl 
    ; symmetry = λ a b e → sym e 
    ; transitivity = λ a b c a≡b b≡c → trans a≡b b≡c 
    }


record Peano (N : Set) {{rel : Rel N}} : Set₁ where
  field
    zero : N
    succ : N -> N
    s-injective : forall (a b : N) -> (succ a) ≃ (succ b) -> a ≃ b
    zero≠succ   : forall (a : N) -> zero ≃ (succ a) -> ⊥
    induction   : 
     ∀ (P : N -> Set) (a : N)
       -> (z : (P zero))
       -> (s : ∀ {b : N} -> P b -> P (succ b))
       -> P a
    induction-zero :      
      ∀ (P : N -> Set)
       -> (z : (P zero))
       -> (s : ∀ {b : N} -> P b -> P (succ b))
       -> ((induction P zero z s) ≡ z)
    induction-succ :      
      ∀ (P : N -> Set) (a : N)
       -> (z : (P zero))
       -> (s : ∀ {b : N} -> P b -> P (succ b))
       -> ((induction P (succ a) z s)) ≡ s (induction P a z s)




ℕ-induction :
  ∀ (P : ℕ -> Set) (a : ℕ)
  -> (P Zero)
  -> (∀ {b : ℕ} -> (P b) -> (P (Succ b)))
  -> (P a)
ℕ-induction P Zero p[zero] p[succ] = p[zero]
ℕ-induction P (Succ n) p[zero] p[succ] 
  = p[succ] (ℕ-induction P n p[zero] p[succ])


ℕ-Peano : Peano ℕ
ℕ-Peano = record
  { zero = Zero
  ; succ = Succ
  ; s-injective = Succ-inj
  ; zero≠succ = λ n ()
  ; induction = ℕ-induction
  ; induction-zero = λ P z s   -> refl
  ; induction-succ = λ P a z s -> refl 
  }

ℕ-rel : ∀ {N : Set} -> N -> Set
ℕ-rel A = ℕ

from-ℕ : ∀ {N : Set} {{_ : Rel N}} -> Peano N -> ℕ -> N
from-ℕ peano Zero = zero
  where
  open Peano peano using (zero)
from-ℕ {{rel}} peano (Succ n) = succ (from-ℕ {{rel}} peano n)
  where
  open Peano peano using (succ)

to-ℕ : ∀ {N : Set} {{_ : Rel N}} -> Peano N -> N -> ℕ
to-ℕ peano n = induction ℕ-rel n Zero λ prev -> Succ prev
  where
  open Peano peano using (induction)

from-zero :  
  ∀ {N : Set} {{_ : Rel N}} -> (peano : Peano N) ->
  (Peano.induction peano ℕ-rel (Peano.zero peano) Zero (λ prev → Succ prev)) ≡ Zero
from-zero peano = induction-zero ℕ-rel Zero Succ
  where
  open Peano peano using (induction-zero)


from∘to : 
  ∀ {N : Set}{{ rel : Rel N}} -> (peano : Peano N) -> (n : N) ->
  from-ℕ peano (to-ℕ peano n) ≃ n
from∘to {N} {{rel}} peano n = 
  let
    prop-eq : _
    prop-eq =
      induction 
        (λ n -> from-ℕ peano (to-ℕ peano n) ≡ n)
        n 
        (zero-lem {_} {peano} )
        (λ {prev} -> succ-lem {N} {peano} prev )
  in
    liftEq _ _ prop-eq
  where
  open Peano peano using (induction)


  zero-lem : ∀ {N} {{_ : Rel N}} {peano : Peano N} →
           from-ℕ peano
           (Peano.induction peano ℕ-rel (Peano.zero peano) Zero
            (λ prev → Succ prev))
           ≡ Peano.zero peano
  zero-lem {_} {peano} =
    let
      pf1 : 
        from-ℕ peano
          (Peano.induction peano ℕ-rel (Peano.zero peano) Zero (λ prev → Succ prev))
        ≡ from-ℕ peano Zero
      pf1 =
        cong (from-ℕ peano) (Peano.induction-zero peano ℕ-rel Zero Succ)

      pf2 :
        from-ℕ peano Zero ≡ Peano.zero peano
      pf2 = refl
    in
      trans pf1 pf2

  succ-lem : ∀ {N} {{_ : Rel N}} {peano : Peano N} (prev : N) →
           from-ℕ peano
           (Peano.induction peano ℕ-rel prev Zero (λ prev → Succ prev))
           ≡ prev →
           from-ℕ peano
           (Peano.induction peano ℕ-rel (Peano.succ peano prev) Zero
            (λ prev → Succ prev))
           ≡ Peano.succ peano prev
  succ-lem {N} {peano} prev pf = 
    let
      pf1 :
        from-ℕ {N} peano
          (Peano.induction peano ℕ-rel (Peano.succ peano prev) Zero
          (λ prev → Succ prev))
        ≡ from-ℕ peano
            (Succ (Peano.induction peano ℕ-rel prev Zero Succ))

      pf1 = cong (from-ℕ peano) 
              (Peano.induction-succ peano ℕ-rel prev Zero Succ)

      pf2 : 
        from-ℕ peano
          (Succ (Peano.induction peano ℕ-rel prev Zero Succ))
        ≡ (Peano.succ peano prev)
      pf2 = cong (Peano.succ peano) pf
    in 
      trans pf1 pf2


to∘from : 
  ∀ {N : Set} {{ _ : Rel N }} -> (peano : Peano N) -> (n : ℕ) ->
    to-ℕ peano (from-ℕ peano n) ≡ n
to∘from peano Zero =  (induction-zero (λ _ -> ℕ) Zero Succ)
  where
  open Peano peano using (induction-zero)
to∘from {{rel}} peano (Succ n)
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


  

