module LnStlc.Lib.AssocLists where


open import Data.String using (String)
open import Data.Nat using (ℕ ; suc)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)


open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import Function using (_∘_)

open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any using (Any; here; there) 
open import Data.List.Membership.Propositional using (_∈_;_∉_)
open import Data.List.Membership.Propositional.Properties

--------------------------------------------------------------------------------
-- Associative lists in Agda.
-- We use these for environments : List (Atom × Type).

dom : ∀ {A B : Set} → List (A × B) → List A
dom = map proj₁

img :  ∀ {A B : Set} → List (A × B) → List B
img = map proj₂

∈-dom-homomorphic : ∀ {A B : Set}
                    (x : A)
                    (xs ys : List (A × B)) →
                    x ∈ dom (xs ++ ys) →
                    x ∈ dom xs ++ dom ys
∈-dom-homomorphic x xs ys x∈xs++ys
  rewrite map-++-commute proj₁ xs ys = x∈xs++ys                  

∈-dom⁺ : ∀ {A B} (a : A) (b : B) xs →
                  ⟨ a , b ⟩ ∈ xs →
                  a ∈ dom xs
∈-dom⁺ a b xs a∈xs = ∈-map⁺ proj₁ a∈xs                  

∈-dom⁻ : ∀ {A B} (a : A) (xs : List (A × B)) →
       a ∈ dom xs →
       ∃[ b ] (⟨ a , b ⟩ ∈ xs)
∈-dom⁻ a xs a∈xs with ∈-map⁻ proj₁ a∈xs
... | ⟨ ⟨ a' , b ⟩ , ⟨ a'b∈xs , a≡a' ⟩ ⟩ rewrite a≡a' = ⟨ b , a'b∈xs ⟩

