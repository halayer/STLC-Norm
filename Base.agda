module Base where

  open import Data.Nat renaming (ℕ to Nat)

  data Typ : Set

  open import Trans {Typ}

  data _⊣_ : Typ → Context → Set

  private variable
    A B : Typ
    Γ : Context

  data Typ where
    𝟚 : Typ
    ℕ : Typ
    _⇒_ : Typ → Typ → Typ

  data _⊣_ where
    var : A ∈ Γ → A ⊣ Γ

    -- Booleans
    ⊤ : 𝟚 ⊣ Γ
    ⊥ : 𝟚 ⊣ Γ
    if_then_else_ : 𝟚 ⊣ Γ → A ⊣ Γ → A ⊣ Γ
                  → A ⊣ Γ

    -- Natural Numbers
    n0 : ℕ ⊣ Γ
    n' : ℕ ⊣ Γ → ℕ ⊣ Γ
    rec : ℕ ⊣ Γ → A ⊣ Γ → A ⊣ (A , (ℕ , Γ))
        → A ⊣ Γ

    -- Functions
    abs : B ⊣ (A , Γ) → (A ⇒ B) ⊣ Γ
    app : (A ⇒ B) ⊣ Γ → A ⊣ Γ → B ⊣ Γ
