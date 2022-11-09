module STLC where

-- TODO:
-- Remove unused imports. Organize the rest.
open import Data.String using (String)
open import Data.Nat using (ℕ ; suc ; _≟_)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂ ; cong-app)


open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction ; contraposition)

open import Function using (_∘_)

open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any using (Any; here; there) 
open import Data.List.Membership.Propositional using (_∈_;_∉_)
open import Data.List.Membership.Propositional.Properties

open import AssocLists



--------------------------------------------------------------------------------
-- Atom stuff

postulate
  Atom      : Set
  =dec      : ∀ (x y : Atom) → Dec (x ≡ y)
  atomFresh : ∀ (xs : List Atom) → ∃[ a ] ( a ∉ xs )
  fresh     : List Atom → Atom
  fresh∉    : ∀ (xs : List Atom) → (fresh xs) ∉ xs
  toNat     : Atom → ℕ

Atoms : Set
Atoms = List Atom

--------------------------------------------------------------------------------
-- Types

infix 10 _—→_

data Type : Set where
  o     : Type
  _—→_ : Type → Type → Type

--------------------------------------------------------------------------------=
-- terms

data Term : Set where
  bvar : ℕ → Term
  fvar : Atom → Term
  `λ   : Term → Term
  _·_  : Term → Term → Term

--------------------------------------------------------------------------------
-- Free variables

fv : Term → List Atom
fv (bvar _) = []
fv (fvar x) = [ x ]
fv (`λ t)   = fv t
fv (t₁ · t₂) = fv t₁ ++ fv t₂

-- x # t denotes that x is free in t.
_#_ : Atom → Term → Set
x # t = x ∉ fv t

cong#· : ∀ {x t₁ t₂} →
       x # (t₁ · t₂) → (x # t₁) × (x # t₂)
cong#· {x} {t₁} x#t₁·t₂ =
  ⟨ (λ x∉fvt₁ → contraposition ∈-++⁺ˡ  x#t₁·t₂ x∉fvt₁) ,
  (λ x∉fvt₂ → contraposition (∈-++⁺ʳ (fv t₁))  x#t₁·t₂ x∉fvt₂) ⟩

--------------------------------------------------------------------------------
-- variable opening (LN)
-- ... means to replace a **bound var** k with **Atom x**.

vopen : ℕ → Term → Atom → Term
vopen k (bvar i) x with i ≟ k
... | yes k=i      = fvar x
... | no  k≠i      = bvar i
vopen k (fvar y) x = fvar y
vopen k (M · N) x  = (vopen k M x) · (vopen k N x)
vopen k (`λ t) x   = `λ (vopen (suc k) t x)

-- In practice, we open from the outermost binding, 0. So we can short-hand:
infix 5 _^_
_^_ : Term → Atom → Term
t₁ ^ t₂ = vopen 0 t₁ t₂

fst snd : Term
fst = (`λ (`λ (bvar 0)))

snd = (`λ (`λ (bvar 1)))

--------------------------------------------------------------------------------
-- substitution (LN)
-- ... means to replace a **Free var** x with **term u**.
subst : Atom → Term → Term → Term
subst x (bvar i) u = bvar i
subst x (fvar y) u with =dec x y
... | yes _ = u
... | no  _ = fvar y 
subst x (M · N) u  = (subst x M u) · (subst x N u)
subst x (`λ t) u   = `λ (subst x t u)

infix 5 _[_/_]
_[_/_] : Term → Term → Atom → Term
t [ v / x ] = subst x t v

--------------------------------------------------------------------------------
-- Term Opening (LN)
-- ... means to replace a **bound var k** with **term u**.

topen : ℕ → Term → Term → Term
topen k (bvar i) u with i ≟ k
... | yes k=i      = u
... | no  k≠i      = bvar i
topen k (fvar y) u = fvar y
topen k (M · N) u  = (topen k M u) · (topen k N u)
topen k (`λ t) u   = `λ (topen (suc k) t u)


-- In practice, we open from the outermost binding, 0. So we can short-hand:
infix 5 _^ₜ_
_^ₜ_ : Term → Term → Term
t₁ ^ₜ t₂ = topen 0 t₁ t₂

--------------------------------------------------------------------------------
-- relating term-opening to substitution

vopenVar≡topenFvar : ∀ k t x →
                   (vopen k t x) ≡ (topen k t (fvar x))
                   
vopenVar≡topenFvar k (bvar i) x with i ≟ k
... | yes _ = refl
... | no _  = refl
vopenVar≡topenFvar k (fvar y) x = refl
vopenVar≡topenFvar k (`λ t) x   = cong `λ (vopenVar≡topenFvar (suc k) t x)
vopenVar≡topenFvar k (t₁ · t₂) x = cong₂ _·_ (vopenVar≡topenFvar k t₁ x) (vopenVar≡topenFvar k t₂ x)

-- term opening is the composition of substitution after variable opening.
opening≡subst : ∀ k t u x →
  x # t →
  (topen k t u) ≡ ((vopen k t x) [ u / x ])
opening≡subst k (bvar i) u x x#t with i ≟ k
...                        | yes i≡k with =dec x x
...                            | yes d   = refl
...                            | no  x≠x = contradiction refl x≠x
opening≡subst k (bvar i) u x x#t | no _  = refl
opening≡subst k (fvar y) u x x#t with =dec x y
... | yes x≡y = ⊥-elim (x#t (here x≡y))
... | no _ =  refl
opening≡subst k (`λ t) u x x#t  = cong `λ (opening≡subst (suc k) t u x x#t)
opening≡subst k (t₁ · t₂) u x x#t with  cong#· {x} {t₁} {t₂} x#t
... | ⟨ x#t₁ , x#t₂ ⟩ = cong₂ _·_ (opening≡subst k t₁ u x x#t₁) (opening≡subst k t₂ u x x#t₂)
    

--------------------------------------------------------------------------------
-- Environments

Env : Set
Env = List (Atom × Type)


-- Well-formedness
data ⊢ : Env → Set where
  ⊢Nil :
       ----------
          ⊢ []
  ⊢Cons : ∀ {Γ x T} →
       ⊢ Γ   →   x ∉ dom Γ →
       -------------------------
           ⊢ (⟨ x , T ⟩ ∷ Γ)
           
--------------------------------------------------------------------------------
-- Typing

data _⊢_⦂_ : Env → Term → Type → Set where
  ⊢Var : ∀ {Γ x T} →
       ⊢ Γ   →   (⟨ x , T ⟩ ∈ Γ) →
       -------------------------
       Γ ⊢ (fvar x) ⦂ T
       
  ⊢App : ∀ {Γ M N T₁ T₂} →
         Γ ⊢ M ⦂ (T₁ —→ T₂)   →   Γ ⊢ N ⦂ T₁ →
         ----------------------------------
              Γ ⊢ M · N ⦂ T₂
              
  ⊢Abs : ∀ {Γ L M T₁ T₂} →
         (∀ x → x ∉ L → (⟨ x , T₁ ⟩ ∷ Γ) ⊢ M ^ₜ (fvar x) ⦂ T₂) →
         -------------------------------------------------------
         Γ ⊢ (`λ M) ⦂ (T₁ —→ T₂)

--------------------------------------------------------------------------------
-- Local closure (LN)

data lc : Term → Set where
  lcₓ : ∀ x →

        ------------
        lc (fvar x)

  lc· : ∀ t₁ t₂ →
        lc t₁   →   lc t₂ →
        ---------------------
            lc (t₁ · t₂)

  lcλ : ∀ L t →
        (∀ x → x  ∉ L → lc (t ^ x)) →
        -------------------------------
                 lc (`λ t)

-- body t ⇔ lc (abs t)
body : Term → Set
body t = ∃[ L ] ( ∀ x → x ∉ L → lc (t ^ x) )

             
--------------------------------------------------------------------------------
-- Call By Value β-Reduction

data _—→β_ : Term → Term → Set where
  β :  ∀ t u →
       (body t)   →   lc u →
       ----------------------
       ((`λ t) · u) —→β (t ^ₜ u)

  β·₁ : ∀ t₁ t₁' t₂ →
        t₁ —→β t₁'   →   lc t₂ →
        ---------------------------
        (t₁ · t₂) —→β (t₁' · t₂)

  β·₂ : ∀ t₁ t₂ t₂' →
        lc t₁   →   t₂ —→β t₂' →
        ---------------------------
        (t₁ · t₂) —→β (t₁ · t₂')

  βλ  : ∀ L t t' →
        (∀ x → x ∉ L → (t ^ x) —→β (t' ^ x)) →
        -----------------------------------------
                  (`λ t) —→β (`λ t')

