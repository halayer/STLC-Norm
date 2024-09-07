-- {-# OPTIONS --allow-unsolved-metas #-}

module Base where

  open import Data.Nat renaming (ℕ to Nat)
  open import Data.List public using () renaming (_∷_ to _,_; [] to ε)
  import Data.Unit
  open import Data.Product using (Σ; proj₁; proj₂) renaming (_,_ to _×,_)
  open import Data.Product.Properties using () renaming (×-≡,≡→≡ to pair-eq)
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

  open Ren using (_⊸_; ⊸-refl; ⊸↑; wkn; _∙rr_; ⊸-tail)
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
  open Properties {_⊣_} {var} {rename} using
    (~>↑; ⟨_⟩; wkn*; wkn*'; id*; _∙rs_; _∙sr_; ⊸-lift; ⊸-lift-prop; s-ext)
  subst : A ⊣ Γ → Γ ~> Δ → A ⊣ Δ
  subst (var e) σ = sub σ e
  subst ⊤ _ = ⊤
  subst ⊥ _ = ⊥
  subst (if t then u else v) σ = if subst t σ then subst u σ else subst v σ
  subst (nat n) _ = nat n
  subst (rec t u v) σ = rec (subst t σ) (subst u σ) (subst v (~>↑ (~>↑ σ)))
  subst (abs t) σ = abs (subst t (~>↑ σ))
  subst (app t u) σ = app (subst t σ) (subst u σ)

  open Properties.MoreProperties {_⊣_} {var} {rename} {subst} using (_∙ss_)

  ren→rename : {r r' : Γ ⊸ Δ}
             → (∀ A (e : A ∈ Γ) → r A e ≡ r' A e)
             → (∀ A (t : A ⊣ Γ) → rename t r ≡ rename t r')
  ren→rename p _ (var e) = cong var (p _ e)
  ren→rename p _ ⊤ = refl
  ren→rename p _ ⊥ = refl
  ren→rename p _ (if t then u else v) = trans (trans
    (cong (λ t → if t then _ else _) (ren→rename p _ t))
    (cong (λ u → if _ then u else _) (ren→rename p _ u)))
    (cong (λ v → if _ then _ else v) (ren→rename p _ v))
  ren→rename p _ (nat _) = refl
  ren→rename p _ (rec t u v) = trans (trans
    (cong (λ t → rec t _ _) (ren→rename p _ t))
    (cong (λ u → rec _ u _) (ren→rename p _ u)))
    (cong (λ v → rec _ _ v)
          (ren→rename
            (λ _ → λ {e0 → refl; (eS e0) → refl;
                      (eS (eS e)) → cong (λ e → eS (eS e)) (p _ e)})
            _ v))
  ren→rename p _ (abs t) =
    cong abs (ren→rename (λ _ → λ {e0 → refl; (eS e) → cong eS (p _ e)}) _ t)
  ren→rename p _ (app t u) = trans
    (cong (λ t → app t _) (ren→rename p _ t))
    (cong (app _) (ren→rename p _ u))

  --wkn-step : {σ : Γ ~> Δ}
  --         → (p : ∀ A (e : A ∈ Γ) → Σ (A ∈ Δ) λ e' → sub σ e ≡ var e')
  --         → (∀ A B (e : A ∈ Γ) →
  --              sub (wkn*' {A = B} σ) e ≡ var (eS (proj₁ (p A e))))
  wkn-step : {r : Γ ⊸ Δ}
           → (∀ A B (e : A ∈ Γ) →
                (wkn ∙rr r) A e ≡ eS (r A e))
  --wkn-step {Γ = _ , _} {σ = σ' ×, t} p A B e0 = {!!}
  --wkn-step {Γ = _ , _} {σ = σ' ×, t} p A B (eS e) = {!!}

  id*-id : {e : A ∈ Γ} → sub id* e ≡ var e
  --id*-id = ⊸-lift-prop {r = ⊸-refl}
  id*-id {e = e0} = refl
  id*-id {e = eS e} = cong var (wkn-step {r = ⊸-refl}  _ _ e)

  id*-↑ : ∀ {e} → sub {A = A} (~>↑ {A = B} (id* {Γ = Γ})) e ≡ sub id* e
  id*-↑ = refl

  sub→subst : {ρ σ : Γ ~> Δ}
            → (∀ A (e : A ∈ Γ) → sub σ e ≡ sub ρ e)
            → (∀ A (t : A ⊣ Γ) → subst t σ ≡ subst t ρ)
  sub→subst p _ t = cong (subst t) (s-ext p)

  lemma' : {r : Γ ⊸ Δ} → wkn {A = A} ∙rr r ≡ ⊸↑ r ∙rr wkn
  lemma' = refl

  ⊸-lift-↑ : {r : Γ ⊸ Δ} {e : A ∈ (B , Γ)}
           → sub (~>↑ (⊸-lift r)) e ≡ sub (⊸-lift (⊸↑ r)) e
  ⊸-lift-↑ {e = e0} = refl
  ⊸-lift-↑ {_ , _} {r = r} {eS e} = helper where
    helper' : (wkn ∙rr r) ≡ (⊸-tail (⊸↑ {A = B} r))
    helper' = refl
    helper'' : ∀ {A B e} → sub {A = A} (wkn {A = B} ∙rs ⊸-lift r) e ≡ sub (⊸-lift (wkn ∙rr r)) e
    helper'' {e = e0} = refl
    helper'' {e = eS e} = {!!}
    helper : sub (wkn ∙rs (⊸-lift r)) e ≡ sub (⊸-lift (⊸-tail (⊸↑ r))) e
    helper = cong
      (λ σ → sub σ e)
      (s-ext λ A e → trans
         (helper'' {e = e})
         (cong (λ r → sub (⊸-lift r) e) helper'))
  
  lemma : {σ : Γ ~> Δ} → ∀ {e}
        → sub {A = A} (wkn {A = B} ∙rs σ) e ≡ sub (~>↑ σ ∙sr wkn) e
  lemma {_ , _} {e = e0} = refl
  lemma {_ , _} {e = eS e} = {!!}
  --lemma {ε} = refl
  --lemma {_ , _} {σ = σ ×, t} = pair-eq (trans (lemma {σ = σ}) {!!} ×, refl)

  ↑-funct : {ρ : Δ ~> Θ} {σ : Γ ~> Δ} → ~>↑ {A = A} (ρ ∙ss σ) ≡ ~>↑ ρ ∙ss ~>↑ σ
  ↑-funct {Γ = ε} = refl
  ↑-funct {Γ = _ , _} {ρ = ρ} {σ = σ ×, t} = pair-eq ((pair-eq (helper ×, {!!})) ×, refl) where
    subst-rename : ∀ {Γ Δ} {t : A ⊣ Γ} {r : Γ ⊸ Δ} → subst t (⊸-lift r) ≡ rename t r
    subst-rename {t = var e} = ⊸-lift-prop {e = e}
    subst-rename {t = ⊤} = refl
    subst-rename {t = ⊥} = refl
    subst-rename {t = if t then u else v} = {!!}
    subst-rename {t = nat _} = refl
    subst-rename {t = rec t u v} = {!!}
    subst-rename {t = abs t} = cong abs {!!}
    subst-rename {t = app t u} = {!!}
    ss-rs : ∀ {Γ Δ Θ} → {r : Δ ⊸ Θ} {σ : Γ ~> Δ} → ⊸-lift r ∙ss σ ≡ r ∙rs σ
    ss-rs {Γ = ε} {σ = Data.Unit.tt} = refl
    ss-rs {Γ = _ , _} {σ = σ ×, t} = pair-eq (ss-rs ×, {!!})
    helper : wkn ∙rs (ρ ∙ss σ) ≡ ~>↑ ρ ∙ss (wkn ∙rs σ)
    helper = {!!}

  sub-decomp : ∀ {e} {ρ : Δ ~> Θ} {σ : Γ ~> Δ} → sub {A = A} (ρ ∙ss σ) e ≡ subst (sub σ e) ρ
  sub-decomp {e = e0} = refl
  sub-decomp {e = eS e} = sub-decomp {e = e}

  subst-decomp : {ρ : Δ ~> Θ} {σ : Γ ~> Δ} → subst t (ρ ∙ss σ) ≡ subst (subst t σ) ρ
  --subst-decomp {t = t} = sub→subst (λ A e → sub-decomp {e = e}) _ t
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
    (cong (λ v → rec _ _ v) (trans (sub→subst (λ A e → {!!}) _ v) (subst-decomp {t = v})))
  subst-decomp {t = abs t} {ρ = ρ} {σ = σ} = cong
    abs
    (trans (cong (subst t) (↑-funct {ρ = ρ} {σ = σ})) (subst-decomp {t = t}))
  subst-decomp {t = app t u} = {!!}

  --lemma : Data.Product.proj₁ wkn* ≡

  wkn-ext-id : {t : A ⊣ Γ} → ⟨ t ⟩ ∙ss wkn* ≡ id* {Γ}
  wkn-ext-id {Γ = ε} = refl
  wkn-ext-id {Γ = A , Γ} = pair-eq ({!!} ×, refl)

