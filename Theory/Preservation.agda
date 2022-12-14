module LnStlc.Theory.Preservation where

open import Data.Nat using (ℕ ; suc ; _≟_)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥-elim)
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any using (Any; here; there) 
open import Data.List.Membership.Propositional using (_∈_;_∉_)
open import Data.List.Membership.Propositional.Properties
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction ; contraposition)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂ ; cong-app)
  
open import Function using (_∘_)

-- ours
open import LnStlc.Lib.AssocLists
open import LnStlc.Lang.Syntax
open import LnStlc.Lang.StaticSemantics


--------------------------------------------------------------------------------
-- Preservation of the CBV STLC λ→ in the Locally Nameless style as per
-- Charguerárd.

--------------------------------------------------------------------------------
-- Auxiliary lemmas

Γ-unique : ∀ {Γ x T U} →
  ⊢ ((⟨ x , U ⟩) ∷ Γ)   →   ⟨ x , T ⟩ ∈ (⟨ x , U ⟩ ∷ Γ) →
  --------------------------------------------------------
                          T ≡ U
Γ-unique {Γ} {x} {T} {.T} _ (here refl) = refl
Γ-unique {Γ} {x} {T} {U} (⊢Cons ⊢Γ x∉domΓ) (there Q) = ⊥-elim (x∉domΓ (∈-dom⁺ x T Γ Q ))

--------------------------------------------------------------------------------
-- Weakening

weakening : ∀ E F G M T →
          ⊢ (E ++ F ++ G)   →   (E ++ G) ⊢ M ⦂ T →
          ------------------------------------------
                     (E ++ F ++ G) ⊢ M ⦂ T
weakening E F G .(fvar x) T wf
  (⊢Var .{E ++ G} {x} {.T} ⊢EG x∈EG) = ⊢Var wf x∈EFG
  where
    x∈EFG : ⟨ x , T ⟩ ∈ E ++ F ++ G
    x∈EFG with (∈-++⁻ E x∈EG)
    ... | inj₁ x∈E = ∈-++⁺ˡ x∈E
    ... | inj₂ x∈G rewrite (sym (++-assoc E F G)) = ∈-++⁺ʳ (E ++ F) x∈G
weakening E F G .(M · N) T₂ wf
  (⊢App .{E ++ G} {M} {N} {T₁} .{T₂} EG⊢M⦂t₁→T₂ EG⊢N⦂T₁) =
     ⊢App EFG⊢M⦂t₁→T₂ EFG⊢N⦂T₁
  where
    EFG⊢N⦂T₁ = weakening E F G N T₁ wf EG⊢N⦂T₁
    EFG⊢M⦂t₁→T₂ = weakening E F G M  (T₁ —→ T₂) wf EG⊢M⦂t₁→T₂
weakening E F G .(`λ M) .(T₁ —→ T₂) wf
  (⊢Abs .{E ++ G} {L} {M} {T₁} {T₂} cof) = ⊢Abs cof'
  where
    L' = L ++ dom E ++ dom F ++ dom G
    cof' : (x : Atom) →
      x ∉ L' → (⟨ x , T₁ ⟩ ∷ E ++ F ++ G) ⊢ M ^ₜ fvar x ⦂ T₂
    cof' x x∉L' = weakening ((⟨ x , T₁ ⟩ ∷ E)) F G (M ^ₜ (fvar x)) T₂ ⊢x∷E++F++G (cof x x∉L)
      where
        x∉L : x ∉ L
        x∉L x∈L = x∉L' (∈-++⁺ˡ x∈L)

        x∉domEFG : x ∉ dom (E ++ F ++ G)
        x∉domEFG x∈domEFG with ∈-dom-homomorphic→ x E (F ++ G) x∈domEFG
        ... | x∈domE++domFG with ∈-++⁻ (dom E) x∈domE++domFG
        ... | inj₁ x∈domE  = x∉L' (∈-++⁺ʳ L  (∈-++⁺ˡ x∈domE))
        ... | inj₂ x∈domFG with ∈-dom-homomorphic→ x F G x∈domFG
        ... | x∈domF++domG = x∉L' ( (∈-++⁺ʳ L  (∈-++⁺ʳ (dom E) x∈domF++domG))) 

        ⊢x∷E++F++G : ⊢ (⟨ x , T₁ ⟩ ∷ E ++ F ++ G)
        ⊢x∷E++F++G = ⊢Cons wf x∉domEFG

--------------------------------------------------------------------------------
-- Substitution

substitution : ∀ E z u U F t T →
               (E ++ [ ⟨ z , U ⟩ ] ++ F) ⊢ t ⦂ T   →   E ⊢ u ⦂ U →
               --------------------------------------------------
                        (E ++ F) ⊢ t [ u / z ] ⦂ T

substitution E z u U F .(fvar x) T (⊢Var {x = x} ⊢EzF x∈EuF) E⊢u⦂U with =dec z x | ∈-++⁻  E x∈EuF | ⊢decompose E _ ⊢EzF
-- I need a uniqueness proof on x
--  if (x : T) ∈ E ++ (x : U) :: F and ⊢ E ++ (x : U) :: F, then T ≡ U.

... | yes z≡x | inj₁ x⦂t∈E | _ rewrite z≡x         = {!!}
... | yes z≡x | inj₂ (here refl) | _  = {!!} 

--let
                                        --  ⊢EF    = (strengthen E [ ⟨ z , U ⟩ ] F ⊢EzF)
                                        --  EF⊢u⦂U = {!!}
                                        -- in {!weakening E [ ⟨ z , U ⟩ ] F u U ?!} -- weakening E [ ⟨ z , U ⟩ ] F u U {!!}--
... | yes z≡x | inj₂ (there y) | _  = {!!}
... | no p | inj₁ x⦂T∈E | ⟨ ⊢E , ⊢zuF ⟩  = ⊢Var (strengthen E [ ⟨ z , U ⟩ ] F ⊢EzF) (∈-++⁺ˡ x⦂T∈E)
-- This case has some work left: We know that x ∈ E ++ [u] ++ F and that x ≠ u,
-- and would like to conclude that x ∈ E ++ F. So we need to show that either
-- (i) it is in E; (ii) if it is in [u], a contradiction; (iii) it is in F.
... | no p | inj₂ x∶T∈zUF | ⟨ ⊢E , ⊢zuF ⟩ = ⊢Var ((strengthen E [ ⟨ z , U ⟩ ] F ⊢EzF)) {!∈-insert E!}

substitution E z u U F .(_ · _) T (⊢App c c₁) E⊢u⦂U = {!!}
substitution E z u U F .(`λ _) .(_ —→ _) (⊢Abs x) E⊢u⦂U = {!!}
