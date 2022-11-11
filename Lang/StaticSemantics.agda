module LnStlc.Lang.StaticSemantics where

import Data.Nat using (ℕ ; suc ; _≟_)
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
         -------------------------------------
              Γ ⊢ M · N ⦂ T₂
              
  ⊢Abs : ∀ {Γ L M T₁ T₂} →
         (∀ x → x ∉ L → (⟨ x , T₁ ⟩ ∷ Γ) ⊢ M ^ₜ (fvar x) ⦂ T₂) →
         -------------------------------------------------------
         Γ ⊢ (`λ M) ⦂ (T₁ —→ T₂)


--------------------------------------------------------------------------------
-- Regularity lemma
--
-- The regularity lemma states that if Γ ⊢ M : T then ⊢ Γ.
-- This is helpful when we want need to fulfill well-formedness checks
-- in other proofs without needing to hypothesize well-formedness, as we likely
-- already have a typing judgment in the context.

regularity : ∀ {Γ t T} → Γ ⊢ t ⦂ T   → ⊢ Γ × lc t
⊢Regular : ∀ {Γ t T} → Γ ⊢ t ⦂ T → ⊢ Γ
lcRegular : ∀ {Γ t T} → Γ ⊢ t ⦂ T → lc t
          
regularity {Γ} .{(fvar _)} {T} (⊢Var {x = x} ⊢Γ _) = ⟨ ⊢Γ , lcₓ x ⟩
regularity {Γ} {.(_ · _)} {T₂} (⊢App {M = M} {N = N} ⊢M⦂T ⊢N⦂T₁→T₂)
  = ⟨ ⊢Regular ⊢M⦂T  , lc· M N (lcRegular ⊢M⦂T) (lcRegular  ⊢N⦂T₁→T₂) ⟩
-- This case needs a lot of cleanup
regularity {Γ} {(`λ M)} {.(_ —→ _)} (⊢Abs {L = L} cof) with atomFresh L
... | ⟨ x , x∉L ⟩ with regularity (cof x x∉L)
... | ⟨ ⊢Cons ⊢Γ _ , lcM^fvarx ⟩ = ⟨ ⊢Γ , lcλ L M lcM^a ⟩ 
  where
    lcM^a : ∀ a → a ∉ L → lc (M ^ a)
    lcM^a a a∉L rewrite (vopenVar≡topenFvar 0 M a) = proj₂ (regularity (cof a a∉L))
    

⊢Regular = proj₁ ∘ regularity
lcRegular = proj₂ ∘ regularity


--------------------------------------------------------------------------------
-- Well formedness implies freshness of each var in .
