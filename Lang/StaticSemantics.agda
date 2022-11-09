module LnStlc.Lang.StaticSemantics where

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

open import LnStlc.Lib.AssocLists
open import LnStlc.Lang.Syntax

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
