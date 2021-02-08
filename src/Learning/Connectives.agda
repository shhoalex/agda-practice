module Learning.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import Learning.Isomorphism using (_≃_; _≲_; _⇔_; extensionality)
open Learning.Isomorphism.≃-Reasoning

data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B

π₁ : ∀ {A B : Set} → A × B → A
π₁ ⟨ x , y ⟩ = x

π₂ : ∀ {A B : Set} → A × B → B
π₂ ⟨ x , y ⟩ = y

η-× : ∀ {A B : Set} → (w : A × B) → ⟨ π₁ w , π₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_

record _×′_ (A B : Set) : Set where
  constructor ⟨_,_⟩′
  field
    π₁′ : A
    π₂′ : B
open _×′_

η-×′ : ∀ {A B : Set} (w : A ×′ B) → ⟨ π₁′ w , π₂′ w ⟩′ ≡ w
η-×′ w = refl

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to      = λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from    = λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; from∘to = λ{ ⟨ x , y ⟩ → refl }
    ; to∘from = λ{ ⟨ y , x ⟩ → refl }
    }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from    = λ{ ⟨ x , ⟨ y  , z ⟩ ⟩ → ⟨ ⟨ x ,  y ⟩ , z ⟩ }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }

⇔≃× : ∀ {A B : Set} → (A ⇔ B) ≃ ((A → B) × (B → A))
⇔≃× = 
  record
    { to      = λ{ A⇔B → ⟨ _⇔_.to A⇔B , _⇔_.from A⇔B ⟩ }
    ; from    = λ{ ⟨ A⇒B , B⇒A ⟩ → record { from = B⇒A ; to = A⇒B } }
    ; from∘to = λ{ A⇔B → refl }
    ; to∘from = λ{ ⟨ A⇒B , B⇒A ⟩ → refl }
    }

data ⊤ : Set where
  tt : ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

record ⊤′ : Set where
  constructor tt′

η-⊤′ : ∀ (w : ⊤′) → tt′ ≡ w
η-⊤′ w = refl

truth′ : ⊤′
truth′ = _

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to      = λ{ ⟨ tt , x ⟩ → x }
    ; from    = λ{ x → ⟨ tt , x ⟩ }
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ{ x → refl }
    }

⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎

data _⊎_ (A B : Set) : Set where
  ι₁ : A → A ⊎ B
  ι₂ : B → A ⊎ B

case-⊎ : ∀ {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
case-⊎ f g (ι₁ x) = f x
case-⊎ f g (ι₂ y) = g y

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ ι₁ ι₂ w ≡ w
η-⊎ (ι₁ x) = refl
η-⊎ (ι₂ y) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) → case-⊎ ι₁ ι₂ w ≡ w
uniq-⊎ h (ι₁ x) = refl
uniq-⊎ h (ι₂ x) = refl

infixr 1 _⊎_

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
    { from    = λ{ (ι₁ x) → ι₂ x ; (ι₂ y) → ι₁ y }
    ; to      = λ{ (ι₁ x) → ι₂ x ; (ι₂ x) → ι₁ x }
    ; from∘to = λ{ (ι₁ x) → refl ; (ι₂ x) → refl }
    ; to∘from = λ{ (ι₁ x) → refl ; (ι₂ x) → refl }
    }

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc = 
  record
    { to      = λ{ (ι₁ (ι₁ x)) → ι₁ x ; (ι₁ (ι₂ b)) → ι₂ (ι₁ b) ; (ι₂ c) → ι₂ (ι₂ c) }
    ; from    = λ{ (ι₁ a) → ι₁ (ι₁ a) ; (ι₂ (ι₁ b)) → ι₁ (ι₂ b) ; (ι₂ (ι₂ c)) → ι₂ c }
    ; from∘to = λ{ (ι₁ (ι₁ x)) → refl ; (ι₁ (ι₂ x)) → refl ; (ι₂ x) → refl }
    ; to∘from = λ{ (ι₁ x) → refl ; (ι₂ (ι₁ x)) → refl ; (ι₂ (ι₂ x)) → refl } 
    }

data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A → A
⊥-identityˡ (ι₂ a) = a

⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ → A
⊥-identityʳ (ι₁ a) = a

→-elim : ∀ {A B : Set} → (A → B) → A → B
→-elim L M = L M

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to      = λ{ f → λ{⟨ x , y ⟩ → f x y }}
    ; from    = λ{ g → λ{x → λ{y → g ⟨ x , y ⟩ }} }
    ; from∘to = λ{ f → refl}
    ; to∘from = λ{ g → extensionality λ{⟨ x , y ⟩ → refl} }
    }

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to      = λ{ f → ⟨ f ∘ ι₁ , f ∘ ι₂ ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ{ (ι₁ x) → g x ; (ι₂ y) → h y } }
    ; from∘to = λ{ f → extensionality λ{ (ι₁ x) → refl ; (ι₂ y) → refl } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to      = λ{ f → ⟨ π₁ ∘ f , π₂ ∘ f ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ x → ⟨ g x , h x ⟩ }
    ; from∘to = λ{ f → extensionality λ{ x → η-× (f x) } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
    { to      = λ{ ⟨ ι₁ x , z ⟩ → (ι₁ ⟨ x , z ⟩)
                 ; ⟨ ι₂ y , z ⟩ → (ι₂ ⟨ y , z ⟩)
                 }
    ; from    = λ{ (ι₁ ⟨ x , z ⟩) → ⟨ ι₁ x , z ⟩
                 ; (ι₂ ⟨ y , z ⟩) → ⟨ ι₂ y , z ⟩
                 }
    ; from∘to = λ{ ⟨ ι₁ x , z ⟩ → refl
                 ; ⟨ ι₂ y , z ⟩ → refl
                 }
    ; to∘from = λ{ (ι₁ ⟨ x , z ⟩) → refl
                 ; (ι₂ ⟨ y , z ⟩) → refl
                 }
    }

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to      = λ{ (ι₁ ⟨ x , y ⟩) → ⟨ ι₁ x , ι₁ y ⟩
                 ; (ι₂ z)         → ⟨ ι₂ z , ι₂ z ⟩
                 }
    ; from    = λ{ ⟨ ι₁ x , ι₁ y ⟩ → (ι₁ ⟨ x , y ⟩)
                 ; ⟨ ι₁ x , ι₂ z ⟩ → (ι₂ z)
                 ; ⟨ ι₂ z , _ ⟩ → (ι₂ z)
                 }
    ; from∘to = λ{ (ι₁ ⟨ x , y ⟩) → refl
                 ; (ι₂ z)         → refl
                 }
    }

