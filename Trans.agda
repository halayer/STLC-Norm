module Trans {Typ : Set} where

  open import Data.Product using (_×_) renaming (_,_ to _×,_)
  open import Data.List using () renaming (_∷_ to _,_; [] to ε) public
  open import Data.Unit using (⊤)

  Context : Set
  data _∈_ : Typ → Context → Set

  private variable
    A B : Typ
    Γ Δ : Context

  Context = Data.List.List Typ

  data _∈_ where
    e0 : A ∈ (A , Γ)
    eS : A ∈ Γ → A ∈ (B , Γ)

  _⊸_ : Context → Context → Set
  ε ⊸ Δ = ⊤
  (A , Γ) ⊸ Δ = Γ ⊸ Δ × A ∈ Δ

  ren : A ∈ Γ → Γ ⊸ Δ → A ∈ Δ
  ren e0 (_ ×, e) = e
  ren (eS e) (r ×, _) = ren e r

  module _ {_⊣_ : Typ → Context → Set} where

    _~>_ : Context → Context → Set
    ε ~> Δ = ⊤
    (A , Γ) ~> Δ = Γ ~> Δ × A ⊣ Δ

    sub : A ∈ Γ → Γ ~> Δ → A ⊣ Δ
    sub e0 (_ ×, t) = t
    sub (eS e) (σ' ×, _) = sub e σ'
