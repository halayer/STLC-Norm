module Base where

  open import Data.Nat renaming (ℕ to Nat)
  open import Data.List public using () renaming (_∷_ to _,_; [] to ε)
  import Data.Unit
  open import Data.Product using () renaming (_,_ to _×,_)
  open import Relation.Binary.PropositionalEquality using
    (_≡_; refl; cong; trans)

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
  open Properties {_⊣_} {var} {rename} using (~>↑; ⟨_⟩; wkn*; id*)
  subst : A ⊣ Γ → Γ ~> Δ → A ⊣ Δ
  subst (var e) σ = sub σ e
  subst ⊤ _ = ⊤
  subst ⊥ _ = ⊥
  subst (if t then u else v) σ = if subst t σ then subst u σ else subst v σ
  subst (nat n) _ = nat n
  subst (rec t u v) σ = rec (subst t σ) (subst u σ) (subst v (~>↑ (~>↑ σ)))
  subst (abs t) σ = abs (subst t (~>↑ σ))
  subst (app t u) σ = app (subst t σ) (subst u σ)

  open Properties.MoreProperties {_⊣_} {var} {rename} {subst} using (_∘*_)

  sub-decomp : ∀ {e} {ρ : Δ ~> Θ} {σ : Γ ~> Δ} → sub {A = A} (ρ ∘* σ) e ≡ subst (sub σ e) ρ
  sub-decomp {e = e0} {σ = _ ×, _} = refl
  sub-decomp {e = eS e} {σ = σ ×, u} = sub-decomp {e = e}

  ↑-funct' : ∀ {e} {ρ : Δ ~> Θ} {σ : Γ ~> Δ} → sub {A = A} (~>↑ {A = B} (ρ ∘* σ)) e ≡ sub (~>↑ ρ ∘* ~>↑ σ) e
  ↑-funct' {e = e0} = refl
  ↑-funct' {Γ = _ , _} {e = eS e} {σ = σ ×, u} = {!!}

  ↑-funct : {ρ : Δ ~> Θ} {σ : Γ ~> Δ} → subst t (~>↑ {A = A} (ρ ∘* σ)) ≡ subst t (~>↑ ρ ∘* ~>↑ σ)
  ↑-funct {t = var e} = ↑-funct' {e = e}
  ↑-funct {t = ⊤} = refl
  ↑-funct {t = ⊥} = refl
  ↑-funct {t = if t then u else v} = {!!}
  ↑-funct {t = nat _} = refl
  ↑-funct {t = rec t u v} = {!!}
  ↑-funct {t = abs t} = {!!}
  ↑-funct {t = app t u} = {!!}

  subst-decomp : {ρ : Δ ~> Θ} {σ : Γ ~> Δ} → subst t (ρ ∘* σ) ≡ subst (subst t σ) ρ
  subst-decomp {t = var e} = sub-decomp {e = e}
  subst-decomp {t = ⊤} = refl
  subst-decomp {t = ⊥} = refl
  subst-decomp {t = if t then u else v} = trans (trans
    (cong (λ t → if t then _ else _) (subst-decomp {t = t}))
    (cong (λ u → if _ then u else _) (subst-decomp {t = u})))
    (cong (λ v → if _ then _ else v) (subst-decomp {t = v}))
  subst-decomp {t = nat _} = refl
  subst-decomp {t = rec t u v} = trans (trans
    (cong (λ t → rec t _ _) (subst-decomp {t = t}))
    (cong (λ u → rec _ u _) (subst-decomp {t = u})))
    (cong (λ v → rec _ _ v) (trans {!!} (subst-decomp {t = v})))
  subst-decomp {t = abs t} {ρ = ρ} {σ = σ} = cong abs (trans {!!} (subst-decomp {t = t}))
  subst-decomp {t = app t u} = {!!}

  pair-eq : ∀ {l l'} {A : Set l} {B : Set l'} {a a' : A} {b b' : B}
          → a ≡ a' → b ≡ b' → (a ×, b) ≡ (a' ×, b')
  pair-eq refl refl = refl

  --lemma : Data.Product.proj₁ wkn* ≡

  wkn-ext-id : {t : A ⊣ Γ} → ⟨ t ⟩ ∘* wkn* ≡ id* {Γ}
  wkn-ext-id {Γ = ε} = refl
  wkn-ext-id {Γ = A , Γ} = pair-eq {!!} refl

