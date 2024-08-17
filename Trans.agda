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

    --open import Relation.Binary.Properties.DecTotalOrder
    open import Relation.Binary.PropositionalEquality.Core

    _⊸_ : Context → Context → Set
    _⊸_ Γ Δ = ∀ A → A ∈ Γ → A ∈ Δ

    ⊸-refl : Γ ⊸ Γ
    ⊸-refl _ e = e

    ⊸-trans : Γ ⊸ Δ → Δ ⊸ Θ → Γ ⊸ Θ
    ⊸-trans r r' A e = r' A (r A e)

    ⊸↑ : Γ ⊸ Δ → (A , Γ) ⊸ (A , Δ)
    ⊸↑ r A e0 = e0
    ⊸↑ r A (eS e) = eS (r A e)

    ⊸-tail : (A , Γ) ⊸ Δ → Γ ⊸ Δ
    ⊸-tail σ A e = σ A (eS e)

    --⊸-antisym : Γ ⊸ Δ → Δ ⊸ Γ → Γ ≡ Δ
    --⊸-antisym r r' = {!!}

    wkn : Γ ⊸ (A , Γ)
    wkn _ = eS

  module Sub {_⊣_ : Typ → Context → Set} where

    open import Data.Unit using (⊤; tt)
    open import Data.Product using (_×_) renaming (_,_ to _×,_)
    
    _~>_ : Context → Context → Set
    --_~>_ Γ Δ = ∀ A (e : A ∈ Γ) → A ⊣ Δ
    ε ~> Δ = ⊤
    (A , Γ) ~> Δ = Γ ~> Δ × A ⊣ Δ

    sub : Γ ~> Δ → A ∈ Γ → A ⊣ Δ
    sub (σ ×, a) e0 = a
    sub (σ ×, a) (eS e) = sub σ e

    ε* : ε ~> Γ
    ε* = tt

    _,*_ : Γ ~> Δ → A ⊣ Δ → (A , Γ) ~> Δ
    σ ,* t = σ ×, t

    head* : (A , Γ) ~> Δ → A ⊣ Δ
    head* {A} (σ ×, a) = a

    tail* : (A , Γ) ~> Δ → Γ ~> Δ
    tail* (σ ×, a) = σ

  module Properties
    {_⊣_ : Typ → Context → Set}
    {var : ∀ {A Γ} → A ∈ Γ → A ⊣ Γ}
    {rename : ∀ {A Γ Δ} → A ⊣ Γ → Γ Ren.⊸ Δ → A ⊣ Δ} where

    open import Data.Product using (∃-syntax) renaming (_,_ to _×,_)
    open import Relation.Binary.PropositionalEquality

    open import Data.Unit using (tt)
    import Data.Product

    open Ren
    open Sub {_⊣_}

    ⊸-lift : Γ ⊸ Δ → Γ ~> Δ
    ⊸-lift {ε} r = tt
    ⊸-lift {A , Γ} r = ⊸-lift (⊸-tail r) ,* var (r A e0)

    ⊸-lift-prop : {e : A ∈ Γ} {r : Γ ⊸ Δ}
                → sub (⊸-lift r) e ≡ var (r A e)
    ⊸-lift-prop {e = e0} = refl
    ⊸-lift-prop {A} {e = eS e} {r} = ⊸-lift-prop {e = e} {⊸-tail r}

    ⊸-lift-≡ : {r : Γ ⊸ Δ} → ((e : A ∈ Γ) → ∃[ e' ] r A e ≡ e')
             → (e : A ∈ Γ) → ∃[ e' ] sub (⊸-lift r) e ≡ (var e')
    ⊸-lift-≡ {r = r} eq e with eq e
    ...                      | e' ×, refl = e' ×, ⊸-lift-prop {r = r}

    _∙*_ : Δ ⊸ Θ → Γ ~> Δ → Γ ~> Θ
    _∙*_ {Γ = ε} r σ = tt
    _∙*_ {Γ = A , Γ} r (σ ×, t) = (r ∙* σ) ,* rename t r

    id* : Γ ~> Γ
    id* = ⊸-lift ⊸-refl

    id*-id : {e : A ∈ Γ} → sub id* e ≡ (var e)
    id*-id = ⊸-lift-prop {r = ⊸-refl}

    wkn* : Γ ~> (A , Γ)
    wkn* = ⊸-lift wkn

    wkn*' : Γ ~> Δ → Γ ~> (A , Δ)
    wkn*' {ε} _ = tt
    wkn*' {_ , _} σ = wkn ∙* σ

    ~>↑ : Γ ~> Δ → (A , Γ) ~> (A , Δ)
    ~>↑ {ε} _ = tt ,* var e0
    ~>↑ {_ , _} (σ ×, t) = (wkn*' σ ,* rename t wkn) ,* var e0

    ⟨_⟩ : A ⊣ Γ → (A , Γ) ~> Γ
    ⟨ t ⟩ = id* ,* t
