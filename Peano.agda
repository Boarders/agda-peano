module Peano where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; _≢_; cong; trans; sym)
open import Function
  using (_∘_)

data ⊥ : Set where

data ℕ : Set where
  Zero : ℕ
  Succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-} -- allowing us to use numeric literals

_+_ : ℕ -> ℕ -> ℕ
_+_ Zero m = m
_+_ (Succ n) m = Succ (n + m)

_ : 2 + 2 ≡ 4
_ = refl

record Rel (A : Set) : Set₁ where
  field
    _≃_ : A → A → Set
    reflexivity  : ∀ {a : A} → a ≃ a
    symmetry     : ∀ {a b : A} → a ≃ b → b ≃ a
    transitivity : ∀ {a b c : A} → a ≃ b → b ≃ c → a ≃ c

open Rel {{...}} public

liftEq : ∀ {A : Set}  {{r : Rel A}} → {a b : A} → a ≡ b → (a ≃ b)
liftEq refl = reflexivity

ℕ-refl : ∀ {n : ℕ} → n ≡ n
ℕ-refl = refl

ℕ-symm : ∀ {n m : ℕ} → n ≡ m → m ≡ n
ℕ-symm eq rewrite eq = refl

ℕ-trans : ∀ {m n r : ℕ} → m ≡ n → n ≡ r → m ≡ r
ℕ-trans  m≡n n≡r rewrite m≡n | n≡r = refl

Succ-inj : ∀ {n m : ℕ} → (Succ n) ≡ (Succ m) → n ≡ m
Succ-inj refl = refl

instance
  ≡-Nat : Rel ℕ
  ≡-Nat =
    record
    { _≃_          = _≡_
    ; reflexivity  = ℕ-refl
    ; symmetry     = ℕ-symm
    ; transitivity = ℕ-trans
    }

≡-Set : (A : Set) → Rel A
≡-Set A =
  record
    { _≃_ = _≡_
    ; reflexivity = refl
    ; symmetry = λ e → sym e
    ; transitivity = λ a≡b b≡c → trans a≡b b≡c
    }

record Peano (N : Set) {{rel : Rel N}} : Set₁ where
  field
    zero : N
    succ : N → N
    s-injective : ∀ {a b : N} → (succ a) ≃ (succ b) → a ≃ b
    zero≠succ   : ∀ (a : N) → zero ≃ (succ a) → ⊥
    induction   :
       ∀ (P : N → Set) (a : N)
       → (z : P zero)
       → (s : ∀ {b : N} → P b → P (succ b))
       → P a
    induction-zero :
       ∀ (P : N → Set)
       → (z : P zero)
       → (s : ∀ {b : N} → P b → P (succ b))
       → (induction P zero z s ≡ z)
    induction-succ :
       ∀ (P : N → Set) (a : N)
       → (z : (P zero))
       → (s : ∀ {b : N} → P b → P (succ b))
       → (induction P (succ a) z s ≡ s (induction P a z s))

ℕ-induction :
  ∀ (P : ℕ → Set) (a : ℕ)
  → (P Zero)
  → (∀ {b : ℕ} → (P b) → (P (Succ b)))
  → (P a)
ℕ-induction P Zero p[zero] p[succ] = p[zero]
ℕ-induction P (Succ n) p[zero] p[succ] 
  = p[succ] (ℕ-induction P n p[zero] p[succ])

open Peano {{...}} public

instance
  ℕ-Peano : Peano ℕ
  ℕ-Peano =
    record
      { zero           = Zero
      ; succ           = Succ
      ; s-injective    = Succ-inj
      ; zero≠succ      = λ n ()
      ; induction      = ℕ-induction
      ; induction-zero = λ P z s   → refl
      ; induction-succ = λ P a z s → refl
      }

from-ℕ : ∀ {N : Set} {{_ : Rel N}} → {{ _ : Peano N}} → ℕ → N
from-ℕ {N} n = induction (λ _ → N) n zero succ


to-ℕ : ∀ {N : Set} {{_ : Rel N}} → {{_ : Peano N}} → N → ℕ
to-ℕ n = induction (λ _ → ℕ) n zero succ

from∘to : 
  ∀ {N : Set}{{ rel : Rel N}} → {{peano : Peano N}} → (n : N) →
  from-ℕ (to-ℕ n) ≃ n
from∘to {N} n = liftEq (prop-eq {N})
  where
  -- In the zero case we apply induction-zero underneath from-ℕ
  -- and then use the definition of from-ℕ
  zero-lem
    : ∀ {N} {{_ : Rel N}} {{peano : Peano N}}
    → from-ℕ {N} (induction {N} (λ _ → ℕ) zero Zero Succ) ≡ zero
  zero-lem {N} =
    let
      pf1 : from-ℕ (induction {N} (λ _ → ℕ) zero Zero Succ) ≡ from-ℕ Zero
      pf1 = cong from-ℕ (induction-zero (λ _ → ℕ) Zero Succ)

      pf2 : from-ℕ  Zero ≡ zero
      pf2 = refl
    in
      trans pf1 pf2
  -- In the successor case we similarly appply induction-succ
  -- underneath from-ℕ and then recurse on the previous proof
  succ-lem
    : ∀ {N} {{_ : Rel N}} {{peano : Peano N}} (prev : N)
    → from-ℕ (induction (λ _ → ℕ) prev Zero Succ) ≡ prev
    → from-ℕ (induction (λ _ → ℕ) (succ prev) Zero Succ) ≡ succ prev
  succ-lem prev pf =
    let
      pf1 : from-ℕ (induction (λ _ → ℕ) (succ prev) Zero Succ)
          ≡ from-ℕ (Succ (induction (λ _ → ℕ) prev Zero Succ))
      pf1 = cong from-ℕ (induction-succ (λ _ → ℕ) prev Zero Succ)

      pf2 : from-ℕ (Succ (induction (λ _ → ℕ) prev Zero Succ)) ≡ (succ prev)
      pf2 = cong succ pf
    in
      trans pf1 pf2

  prop-eq
    : ∀ {N} {{_ : Rel N}} {{peano : Peano N}}
    → from-ℕ (to-ℕ n) ≡ n
  prop-eq =
      induction
     -- we use induction on the principle
     -- we are trying to show.
        (λ n → from-ℕ (to-ℕ  n) ≡ n)
        n
        zero-lem
        (λ {prev} → succ-lem prev)


to∘from : 
  ∀ {N : Set} {{ _ : Rel N }} → {{peano : Peano N}} → (n : ℕ) →
    to-ℕ {N} (from-ℕ n) ≡ n
to∘from Zero =  (induction-zero (λ _ → ℕ) Zero Succ)
to∘from {N} {{_}} {{peano}} (Succ n)
  rewrite 
    (induction-succ
      (λ _ → ℕ)
      (ℕ-induction (λ _ → N) n (Peano.zero peano) (Peano.succ peano))
      Zero
      Succ)
  | to∘from {N} n
  = refl

-- F-algebras

data NatP (r : Set) : Set where
  ZeroP : NatP r
  SuccP : r → NatP r

record Functor (F : Set → Set) : Set₁ where
  constructor Func
  field
    Arr : ∀ {A B : Set} → (f : A → B) → F A → F B

open Functor {{...}} public

instance
  NatP-Functor : Functor NatP
  NatP-Functor = Func map
    where
    map : ∀ {A} {B} → (A → B) → NatP A → NatP B
    map f ZeroP = ZeroP
    map f (SuccP x) = SuccP (f x)


record Alg (F : Set → Set) (A : Set) : Set where
  field
    μ : F A → A

record Dyn (A : Set) : Set where
  constructor D
  field
    basepoint : A
    self-map  : A → A


from-Dyn : ∀ {A : Set} → Dyn A → Alg NatP A
from-Dyn {A} (D basepoint self-map) = record { μ = alg }
  where
  alg : NatP A → A
  alg ZeroP = basepoint
  alg (SuccP a) = self-map a


open Alg {{...}} public
instance
  ℕ-Alg : Alg NatP ℕ
  ℕ-Alg = record { μ = alg }
    where
    alg : NatP ℕ → ℕ
    alg ZeroP     = Zero
    alg (SuccP x) = Succ x

record Alg-Homo (A B : Set) {F : Set → Set} {{f : Functor F}}
  (FA : Alg F A) (FB : Alg F B) : Set₁ where
  constructor AlgHom
  field
    →-fun : A → B
    μ-comm
      : ∀ (fa : F A)
      → →-fun (Alg.μ FA fa) ≡ (Alg.μ FB) (Arr →-fun fa)



ℕ-weakly-initial
  : ∀ {A : Set}
  → {{FA : Alg NatP A}}
  → Alg-Homo ℕ A ℕ-Alg FA
ℕ-weakly-initial {A} = AlgHom init-ℕ law
  where
  init-ℕ : ℕ → A
  init-ℕ Zero     = μ ZeroP
  init-ℕ (Succ n) = μ (SuccP (init-ℕ n))

  law : (na : NatP ℕ) → init-ℕ (μ na) ≡ μ (Arr init-ℕ na)
  law ZeroP     = refl
  law (SuccP x) = refl


ℕ-init-uniq :
  ∀ {A : Set}
  → {{FA : Alg NatP A}}
  → (alg-hom : Alg-Homo ℕ A ℕ-Alg FA)
  → ∀ (n : ℕ)
  → (Alg-Homo.→-fun alg-hom n)
  ≡ (Alg-Homo.→-fun (ℕ-weakly-initial {{FA}}) n)
ℕ-init-uniq alg-hom Zero = μ-comm ZeroP
  where
    open Alg-Homo alg-hom public
ℕ-init-uniq {{FA}} alg-hom (Succ n) =
  let
    pf1 : →-fun (Succ n) ≡ μ (SuccP (→-fun n))
    pf1 = μ-comm (SuccP n)

    pf2 :  μ (SuccP (→-fun n)) ≡ μ (SuccP (Alg-Homo.→-fun ℕ-weakly-initial n))
    pf2 = cong (μ ∘ SuccP) (ℕ-init-uniq alg-hom n)
  in
    trans pf1 pf2
  where
    open Alg-Homo alg-hom public


data ListP (A : Set) (r : Set) : Set where
  NilP  : ListP A r
  ConsP : A → r → ListP A r

data List (A : Set) : Set where
  Nil  : List A
  Cons : A → List A → List A

instance
  ListP-Functor : ∀ {A} →  Functor (ListP A)
  ListP-Functor {A} = Func map-L
    where
    map-L : ∀ {B} {C} → (B → C) → ListP A B → ListP A C
    map-L f NilP = NilP
    map-L f (ConsP a b) = ConsP a (f b)

record HasFold (A : Set) (B : Set) : Set₁ where
  constructor F
  field
    initial  : B
    operator : A → B → B

fromHasFold : ∀ {A B : Set} →  HasFold A B → Alg (ListP A) B
fromHasFold {A} {B} (F initial operator) = record { μ = alg }
  where
  alg : ListP A B → B
  alg NilP = initial
  alg (ConsP a b) = operator a b

toHasFold : ∀ {A B : Set} → Alg (ListP A) B → HasFold A B
toHasFold {A} {B} record { μ = μ } = F init op
  where
  init : B
  init = μ NilP

  op : A → B → B
  op a b = μ (ConsP a b)

instance
  List-Alg : ∀ {A} → Alg (ListP A) (List A)
  List-Alg {A} = record { μ = alg }
    where
    alg : ListP A (List A) → List A
    alg NilP = Nil
    alg (ConsP a as) = Cons a as

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr op init Nil         = init
foldr op init (Cons a as) = op a (foldr op init as)

foldr-Alg : ∀ {A B : Set}
  → {{FA : Alg (ListP A) B}}
  → List A → B
foldr-Alg = foldr (λ a b → μ (ConsP a b)) (μ NilP)

List-weakly-initial
  : ∀ {A B : Set}
  → {{FA : Alg (ListP A) B}}
  → Alg-Homo (List A) B (List-Alg {A}) FA
List-weakly-initial {A} {B} = AlgHom foldr-Alg law
  where

  law : (fa : ListP A (List A)) →
    foldr (λ a b → μ (ConsP a b)) (μ NilP) (μ fa)
      ≡
    μ (Arr (foldr (λ a b → μ (ConsP a b)) (μ NilP)) fa)
  law NilP         = refl
  law (ConsP a as) = refl
