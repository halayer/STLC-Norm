module Trans {Typ : Set} where

  open import Data.List using (List) renaming (_∷_ to _,_; [] to ε)

  Context : Set
  data _∈_ : Typ → Context → Set

  private variable
    A B : Typ
    Γ Δ Θ : Context

  Context = List Typ

  data _∈_ where
    e0 : A ∈ (A , Γ)
    eS : A ∈ Γ → A ∈ (B , Γ)

  module Ren where

    _⊸_ : Context → Context → Set
    _⊸_ Γ Δ = ∀ A → A ∈ Γ → A ∈ Δ

    ⊸-refl : Γ ⊸ Γ
    ⊸-refl _ e = e

    ⊸-trans : Γ ⊸ Δ → Δ ⊸ Θ → Γ ⊸ Θ
    ⊸-trans r r' A e = r' A (r A e)

    _∙rr_ : Δ ⊸ Θ → Γ ⊸ Δ → Γ ⊸ Θ
    _∙rr_ r r' = ⊸-trans r' r

    ⊸-tail : (A , Γ) ⊸ Δ → Γ ⊸ Δ
    ⊸-tail σ A e = σ A (eS e)

    wkn : Γ ⊸ (A , Γ)
    wkn = ⊸-tail ⊸-refl
    -- wkn _ = eS

    ⊸↑ : Γ ⊸ Δ → (A , Γ) ⊸ (A , Δ)
    ⊸↑ r A e0 = e0
    ⊸↑ r A (eS e) = eS (r A e)

    --⊸-antisym : Γ ⊸ Δ → Δ ⊸ Γ → Γ ≡ Δ
    --⊸-antisym r r' = {!!}

  module Sub {_⊣_ : Typ → Context → Set} where

    open import Data.Unit using (⊤; tt)
    open import Data.Product using (_×_) renaming (_,_ to _×,_)
    
    _~>_ : Context → Context → Set
    --_~>_ Γ Δ = ∀ A (e : A ∈ Γ) → A ⊣ Δ
    ε ~> Δ = ⊤
    (A , Γ) ~> Δ = Γ ~> Δ × A ⊣ Δ

    sub : Γ ~> Δ → A ∈ Γ → A ⊣ Δ
    sub (_ ×, a) e0 = a
    sub (σ ×, _) (eS e) = sub σ e

    ε* : ε ~> Γ
    ε* = tt

  module Properties
    {_⊣_ : Typ → Context → Set}
    {var : ∀ {A Γ} → A ∈ Γ → A ⊣ Γ}
    {rename : ∀ {A Γ Δ} → A ⊣ Γ → Γ Ren.⊸ Δ → A ⊣ Δ} where

    open import Data.Product using (∃-syntax; proj₁; proj₂) renaming (_,_ to _×,_)
    open import Data.Product.Properties using () renaming (×-≡,≡→≡ to pair-eq)
    open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
    open import Data.Unit using (tt)

    open Ren
    open Sub {_⊣_}

    ⊸-lift : Γ ⊸ Δ → Γ ~> Δ
    ⊸-lift {ε} r = tt
    ⊸-lift {A , _} r = ⊸-lift (⊸-tail r) ×, var (r A e0)

    ⊸-lift-prop : {e : A ∈ Γ} {r : Γ ⊸ Δ}
                → sub (⊸-lift r) e ≡ var (r A e)
    ⊸-lift-prop {e = e0} = refl
    ⊸-lift-prop {A} {e = eS e} {r} = ⊸-lift-prop {e = e} {⊸-tail r}

    s-ext : {ρ σ : Γ ~> Δ}
      → (∀ A (e : A ∈ Γ) → sub σ e ≡ sub ρ e)
      → σ ≡ ρ
    s-ext {ε} _ = refl
    s-ext {_ , _} p = pair-eq (s-ext (λ A e → p A (eS e)) ×, p _ e0)

    _∙rs_ : Δ ⊸ Θ → Γ ~> Δ → Γ ~> Θ
    _∙rs_ {Γ = ε} _ tt = tt
    _∙rs_ {Γ = _ , _} r (σ ×, t) = (r ∙rs σ) ×, rename t r

    ~>↑ : Γ ~> Δ → (A , Γ) ~> (A , Δ)
    ~>↑ σ = (wkn ∙rs σ) ×, var e0

    wkn*' : Γ ~> Δ → Γ ~> (A , Δ)
    wkn*' σ = wkn ∙rs σ
    --wkn*' {ε} _ = tt
    --wkn*' {_ , _} (σ ×, t) = wkn*' σ ×, rename t wkn

    id* : Γ ~> Γ
    --id* = ⊸-lift ⊸-refl
    id* {ε} = tt
    id* {_ , _} = wkn*' id* ×, var e0

    wkn* : Γ ~> (A , Γ)
    wkn* = wkn*' id*

    ⟨_⟩ : A ⊣ Γ → (A , Γ) ~> Γ
    ⟨ t ⟩ = id* ×, t

    _∙sr_ : Δ ~> Θ → Γ ⊸ Δ → Γ ~> Θ
    _∙sr_ {Γ = ε} σ r = tt
    _∙sr_ {Γ = _ , _} σ r = (σ ∙sr (r ∙rr wkn)) ×, sub σ (r _ e0)

    module MoreProperties
      {subst : ∀ {A Γ Δ} → A ⊣ Γ → Γ ~> Δ → A ⊣ Δ} where

      _∙ss_ : Δ ~> Θ → Γ ~> Δ → Γ ~> Θ
      _∙ss_ {Γ = ε} _ tt = tt
      _∙ss_ {Γ = _ , _} ρ (σ ×, t) = (ρ ∙ss σ) ×, subst (sub (σ ×, t) e0) ρ
