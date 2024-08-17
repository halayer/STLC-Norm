module Base where

  open import Data.Nat renaming (ℕ to Nat)
  open import Data.List public using () renaming (_∷_ to _,_; [] to ε)

  data Typ : Set

  open import Trans {Typ} public

  data _⊣_ : Typ → Context → Set

  private variable
    A B : Typ
    Γ Δ Θ : Context
    e e' : A ∈ Γ
    t t' u u' v v' : A ⊣ Γ

  data Typ where
    𝟚 : Typ
    ℕ : Typ
    _⇒_ : Typ → Typ → Typ

  data _⊣_ where
    var : A ∈ Γ → A ⊣ Γ

    -- Booleans
    ⊤ : 𝟚 ⊣ Γ
    ⊥ : 𝟚 ⊣ Γ
    if_then_else_ : (t : 𝟚 ⊣ Γ) → (u : A ⊣ Γ) → (v : A ⊣ Γ)
                  → A ⊣ Γ

    -- Natural Numbers
    nat : Nat → ℕ ⊣ Γ
    rec : ℕ ⊣ Γ → A ⊣ Γ → A ⊣ (A , (ℕ , Γ))
        → A ⊣ Γ

    -- Functions
    abs : B ⊣ (A , Γ) → (A ⇒ B) ⊣ Γ
    app : (A ⇒ B) ⊣ Γ → A ⊣ Γ → B ⊣ Γ

  open Ren using (_⊸_; ⊸↑; wkn)
  rename : A ⊣ Γ → Γ ⊸ Δ → A ⊣ Δ
  rename (var {A} e) r = var (r A e)
  rename ⊤ _ = ⊤
  rename ⊥ _ = ⊥
  rename (if t then u else v) r = if rename t r then rename u r else rename v r
  rename (nat n) _ = nat n
  rename (rec t u v) r = rec (rename t r) (rename u r) (rename v (⊸↑ (⊸↑ r)))
  rename (abs t) r = abs (rename t (⊸↑ r))
  rename (app t u) r = app (rename t r) (rename u r)

  unlam : (A ⇒ B) ⊣ Γ → B ⊣ (A , Γ)
  unlam t = app (rename t wkn) (var e0)

  open Sub {_⊣_} using (_~>_; sub)
  open Properties {_⊣_} {var} {rename} using (~>↑)
  subst : A ⊣ Γ → Γ ~> Δ → A ⊣ Δ
  subst (var e) σ = sub σ e
  subst ⊤ _ = ⊤
  subst ⊥ _ = ⊥
  subst (if t then u else v) σ = if subst t σ then subst u σ else subst v σ
  subst (nat n) _ = nat n
  subst (rec t u v) σ = rec (subst t σ) (subst u σ) (subst v (~>↑ (~>↑ σ)))
  subst (abs t) σ = abs (subst t (~>↑ σ))
  subst (app t u) σ = app (subst t σ) (subst u σ)
