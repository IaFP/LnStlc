module LnStlc.Lang.DynamicSemantics where

-- TODO:
-- Remove unused imports. Organize the rest.
open import Data.Nat using (ℕ ; suc ; _≟_)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥-elim)
open import Data.List
open import Data.List.Relation.Unary.Any using (Any; here; there) 
open import Data.List.Membership.Propositional using (_∈_;_∉_)
open import Data.List.Membership.Propositional.Properties

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction ; contraposition)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂ ; cong-app)
  
open import Function using (_∘_)

open import LnStlc.Lib.AssocLists
open import LnStlc.Lang.Syntax

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

