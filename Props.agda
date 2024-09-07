module Props where

  open import Relation.Binary.PropositionalEquality using
    (_≡_; refl; sym; cong; trans)
  open import Data.Product using (proj₁; proj₂) renaming (_,_ to _×,_)
  open import Data.Product.Properties renaming (×-≡,≡→≡ to pair-eq)
  open import Data.Unit using (tt)

  open import Base
  open import Trans {Typ} renaming (_~>_ to _~>'_) --hiding (_~>_; sub)

  _~>_ : Context → Context → Set
  _~>_ = _~>'_ {_⊣_}

  private variable
    A B : Typ
    Γ Δ Θ : Context
    t : A ⊣ Γ

  -- Renaming Properties
  ⊸-head : (A , Γ) ⊸ Δ → A ∈ Δ
  ⊸-head = proj₂

  ⊸-tail : (A , Γ) ⊸ Δ → Γ ⊸ Δ
  ⊸-tail = proj₁

  ⊸-wkn : Γ ⊸ Δ → Γ ⊸ (A , Δ)
  ⊸-wkn {ε} _ = tt
  ⊸-wkn {_ , _} r = ⊸-wkn (⊸-tail r) ×, eS (⊸-head r)

  ⊸-wkn-prop : {r : Γ ⊸ Δ} {e : A ∈ Γ}
             → ren e (⊸-wkn {A = B} r) ≡ eS (ren e r)
  ⊸-wkn-prop {e = e0} = refl
  ⊸-wkn-prop {e = eS e} = ⊸-wkn-prop {e = e}

  ⊸-refl : Γ ⊸ Γ
  ⊸-refl {ε} = tt
  ⊸-refl {_ , _} = ⊸-wkn ⊸-refl ×, e0

  ⊸-refl-id : {e : A ∈ Γ} → ren e ⊸-refl ≡ e
  ⊸-refl-id {e = e0} = refl
  ⊸-refl-id {e = eS e} = trans (⊸-wkn-prop {e = e}) (cong eS ⊸-refl-id)

  ⊸-wkn' : Γ ⊸ (A , Γ)
  ⊸-wkn' = ⊸-wkn ⊸-refl

  ⊸-trans : Γ ⊸ Δ → Δ ⊸ Θ → Γ ⊸ Θ
  ⊸-trans {ε} _ _ = tt
  ⊸-trans {_ , _} r r' = ⊸-trans (⊸-tail r) r' ×, ren (⊸-head r) r'

  _∙rr_ : Δ ⊸ Θ → Γ ⊸ Δ → Γ ⊸ Θ
  _∙rr_ r' r = ⊸-trans r r'

  ⊸-↑ : Γ ⊸ Δ → (A , Γ) ⊸ (A , Δ)
  ⊸-↑ r = (⊸-wkn' ∙rr r) ×, e0

  rename : A ⊣ Γ → Γ ⊸ Δ → A ⊣ Δ
  rename (var {A} e) r = var (ren e r)
  rename ⊤ _ = ⊤
  rename ⊥ _ = ⊥
  rename (if t then u else v) r = if rename t r then rename u r else rename v r
  rename (nat n) _ = nat n
  rename (rec t u v) r = rec (rename t r) (rename u r) (rename v (⊸-↑ (⊸-↑ r)))
  rename (abs t) r = abs (rename t (⊸-↑ r))
  rename (app t u) r = app (rename t r) (rename u r)

  ⊸-ext : {r r' : Γ ⊸ Δ}
        → (∀ A (e : A ∈ Γ) → ren e r ≡ ren e r')
        → r ≡ r'
  ⊸-ext {ε} _ = refl
  ⊸-ext {_ , _} p = pair-eq (⊸-ext (λ A e → p A (eS e)) ×, p _ e0)

  ⊸-wkn-decomp : {r : Γ ⊸ Δ} → ⊸-wkn {A = A} r ≡ ⊸-wkn' ∙rr r
  ⊸-wkn-decomp {Γ = Γ} {r = r} = ⊸-ext helper where
    helper : (A : Typ) (e : A ∈ Γ) → ren e (⊸-wkn r) ≡ ren e (⊸-wkn' ∙rr r)
    helper _ e0 =
      sym (trans (⊸-wkn-prop {r = ⊸-refl} {e = ⊸-head r})
                 (cong eS ⊸-refl-id))
    helper _ (eS e) = cong (ren e) ⊸-wkn-decomp

  -- Substitution Properties
  ⊸→~> : Γ ⊸ Δ → Γ ~> Δ
  ⊸→~> {ε} r = tt
  ⊸→~> {_ , _} r = ⊸→~> (⊸-tail r) ×, var (⊸-head r)

  ⊸→~>-≡ : {r : Γ ⊸ Δ} {e : A ∈ Γ} {e' : A ∈ Δ}
         → ren e r ≡ e'
         → sub e (⊸→~> r) ≡ var e'
  ⊸→~>-≡ {e = e0} refl = refl
  ⊸→~>-≡ {e = eS e} refl = ⊸→~>-≡ {e = e} refl

  _∙sr_ : Δ ~> Θ → Γ ⊸ Δ → Γ ~> Θ
  _∙sr_ {Γ = ε} _ _ = tt
  _∙sr_ {Γ = _ , _} σ r = (σ ∙sr ⊸-tail r) ×, sub (⊸-head r) σ

  ~>-head : (A , Γ) ~> Δ → A ⊣ Δ
  ~>-head = proj₂

  ~>-tail : (A , Γ) ~> Δ → Γ ~> Δ
  ~>-tail = proj₁

  _∙rs_ : Δ ⊸ Θ → Γ ~> Δ → Γ ~> Θ
  _∙rs_ {Γ = ε} _ _ = tt
  _∙rs_ {Γ = _ , _} r σ = (r ∙rs ~>-tail σ) ×, rename (~>-head σ) r

  ~>-wkn : Γ ~> Δ → Γ ~> (A , Δ)
  ~>-wkn {ε} _ = tt
  ~>-wkn {_ , _} σ = ~>-wkn (~>-tail σ) ×, rename (~>-head σ) ⊸-wkn'

  ~>-refl : Γ ~> Γ
  ~>-refl = ⊸→~> ⊸-refl

  ~>-refl-id : {e : A ∈ Γ} → sub e ~>-refl ≡ var e
  ~>-refl-id {e = e} = ⊸→~>-≡ {e = e} ⊸-refl-id

  ~>-wkn' : Γ ~> (A , Γ)
  ~>-wkn' = ⊸→~> ⊸-wkn'

  ⟨_⟩ : A ⊣ Γ → (A , Γ) ~> Γ
  ⟨ t ⟩ = ~>-refl ×, t

  subst : A ⊣ Γ → Γ ~> Δ → A ⊣ Δ

  ~>-trans : Γ ~> Δ → Δ ~> Θ → Γ ~> Θ
  ~>-trans {ε} _ _ = tt
  ~>-trans {_ , _} σ ρ = ~>-trans (~>-tail σ) ρ ×, subst (~>-head σ) ρ

  _∙ss_ : Δ ~> Θ → Γ ~> Δ → Γ ~> Θ
  _∙ss_ ρ σ = ~>-trans σ ρ

  ~>-↑ : Γ ~> Δ → (A , Γ) ~> (A , Δ)
  ~>-↑ σ = (⊸-wkn' ∙rs σ) ×, var e0

  subst (var e) σ = sub e σ
  subst ⊤ _ = ⊤
  subst ⊥ _ = ⊥
  subst (if t then u else v) σ = if subst t σ then subst u σ else subst v σ
  subst (nat n) _ = nat n
  subst (rec t u v) σ = rec (subst t σ) (subst u σ) (subst v (~>-↑ (~>-↑ σ)))
  subst (abs t) σ = abs (subst t (~>-↑ σ))
  subst (app t u) σ = app (subst t σ) (subst u σ)

  ~>-ext : {ρ σ : Γ ~> Δ}
         → (∀ A (e : A ∈ Γ) → sub e σ ≡ sub e ρ)
         → σ ≡ ρ
  ~>-ext {ε} _ = refl
  ~>-ext {_ , _} p = pair-eq (~>-ext (λ A e → p A (eS e)) ×, p _ e0)

  ⊸-tail→~>-tail : {r : (A , Γ) ⊸ Δ}
                 → ~>-tail (⊸→~> r) ≡ ⊸→~> (⊸-tail r)
  ⊸-tail→~>-tail {Γ = Γ} {r = r} = refl

  ∙rs→∙rr : {r : Γ ⊸ Δ} {r' : Δ ⊸ Θ}
          → r' ∙rs (⊸→~> r) ≡ ⊸→~> (r' ∙rr r)
  ∙rs→∙rr {Γ = Γ} {r = r} {r'} = ~>-ext helper where
    helper : (A : Typ) (e : A ∈ Γ)
           → sub e (r' ∙rs (⊸→~> r)) ≡ sub e (⊸→~> (r' ∙rr r))
    helper _ e0 = refl
    helper A (eS e) = cong
      (sub e)
      (trans (cong (_∙rs_ r') (⊸-tail→~>-tail {r = r})) ∙rs→∙rr)

  ~>-↑-⊸-↑ : {r : Γ ⊸ Δ} → ~>-↑ {A = A} (⊸→~> r) ≡ ⊸→~> (⊸-↑ r)
  ~>-↑-⊸-↑ {Γ = Γ} {r = r} = ~>-ext helper where
    helper : (A : Typ) (e : A ∈ (B , Γ))
           → sub e (~>-↑ (⊸→~> r)) ≡ sub e (⊸→~> (⊸-↑ r))
    helper _ e0 = refl
    helper {B = B} _ (eS e) = cong (sub e) ∙rs→∙rr

  ⊸→~>-rename-subst : {r : Γ ⊸ Δ} {t : A ⊣ Γ}
                    → rename t r ≡ subst t (⊸→~> r)
  ⊸→~>-rename-subst {t = var e} = sym (⊸→~>-≡ {e = e} refl)
  ⊸→~>-rename-subst {t = ⊤} = refl
  ⊸→~>-rename-subst {t = ⊥} = refl
  ⊸→~>-rename-subst {t = if t then u else v} = trans (trans
    (cong (λ t → if t then _ else _) ⊸→~>-rename-subst)
    (cong (λ u → if _ then u else _) ⊸→~>-rename-subst))
    (cong (λ v → if _ then _ else v) ⊸→~>-rename-subst)
  ⊸→~>-rename-subst {t = nat n} = refl
  ⊸→~>-rename-subst {t = rec t u v} = trans (trans
    (cong (λ t → rec t _ _) ⊸→~>-rename-subst)
    (cong (λ u → rec _ u _) ⊸→~>-rename-subst))
    (cong (λ v → rec _ _ v) (trans
      ⊸→~>-rename-subst
      (cong (subst v)
            (trans (sym (~>-↑-⊸-↑ {r = ⊸-↑ _}))
                   (cong ~>-↑ (sym ~>-↑-⊸-↑))))))
  ⊸→~>-rename-subst {r = r} {t = abs t} = cong
    abs (trans ⊸→~>-rename-subst (cong (subst t) (sym ~>-↑-⊸-↑)))
  ⊸→~>-rename-subst {t = app t u} = trans
    (cong (λ t → app t _) ⊸→~>-rename-subst)
    (cong (λ u → app _ u) ⊸→~>-rename-subst)

  test : {σ : Γ ~> Δ} → ~>-wkn {A = A} σ ≡ ~>-wkn' ∙ss σ
  test {Γ = Γ} {σ = σ} = ~>-ext helper where
    helper : (A : Typ) (e : A ∈ Γ)
           → sub e (~>-wkn σ) ≡ sub e (~>-wkn' ∙ss σ)
    helper _ e0 = ⊸→~>-rename-subst
    helper _ (eS e) = cong (sub e) test

  --wkn-step : {σ : Γ ~> Δ}
  --         → (p : ∀ A (e : A ∈ Γ) → Σ (A ∈ Δ) λ e' → sub σ e ≡ var e')
  --         → (∀ A B (e : A ∈ Γ) →
  --              sub (wkn*' {A = B} σ) e ≡ var (eS (proj₁ (p A e))))
  --wkn-step : {r : Γ ⊸ Δ}
  --         → (∀ A B (e : A ∈ Γ) →
  --              (wkn ∙rr r) A e ≡ eS (r A e))
  --wkn-step {Γ = _ , _} {σ = σ' ×, t} p A B e0 = {!!}
  --wkn-step {Γ = _ , _} {σ = σ' ×, t} p A B (eS e) = {!!}

  --id*-↑ : ∀ {e} → sub {A = A} (~>↑ {A = B} (id* {Γ = Γ})) e ≡ sub id* e
  --id*-↑ = refl

  --lemma' : {r : Γ ⊸ Δ} → wkn {A = A} ∙rr r ≡ ⊸↑ r ∙rr wkn
  --lemma' = refl

  --⊸-lift-↑ : {r : Γ ⊸ Δ} {e : A ∈ (B , Γ)}
  --         → sub (~>↑ (⊸-lift r)) e ≡ sub (⊸-lift (⊸↑ r)) e
  --⊸-lift-↑ {e = e0} = refl
  --⊸-lift-↑ {_ , _} {r = r} {eS e} = helper where
  --  helper' : (wkn ∙rr r) ≡ (⊸-tail (⊸↑ {A = B} r))
  --  helper' = refl
  --  helper'' : ∀ {A B e} → sub {A = A} (wkn {A = B} ∙rs ⊸-lift r) e ≡ sub (⊸-lift (wkn ∙rr r)) e
  --  helper'' {e = e0} = refl
  --  helper'' {e = eS e} = {!!}
  --  helper : sub (wkn ∙rs (⊸-lift r)) e ≡ sub (⊸-lift (⊸-tail (⊸↑ r))) e
  --  helper = cong
  --    (λ σ → sub σ e)
  --    (s-ext λ A e → trans
  --       (helper'' {e = e})
  --       (cong (λ r → sub (⊸-lift r) e) helper'))
  
  --lemma : {σ : Γ ~> Δ} → ∀ {e}
  --      → sub {A = A} (wkn {A = B} ∙rs σ) e ≡ sub (~>↑ σ ∙sr wkn) e
  --lemma {_ , _} {e = e0} = refl
  --lemma {_ , _} {e = eS e} = {!!}
  --lemma {ε} = refl
  --lemma {_ , _} {σ = σ ×, t} = pair-eq (trans (lemma {σ = σ}) {!!} ×, refl)

  sub→subst : {σ : Γ ~> Δ}
            → (∀ A (e : A ∈ Γ) → sub e σ ≡ {!!})
            → (∀ A (t : A ⊣ Γ) → subst t σ ≡ {!!})

  ↑-funct : {ρ : Δ ~> Θ} {σ : Γ ~> Δ} → ~>-↑ {A = A} (ρ ∙ss σ) ≡ ~>-↑ ρ ∙ss ~>-↑ σ
  ↑-funct {Γ = ε} = refl
  ↑-funct {Γ = _ , _} {ρ = ρ} {σ = σ ×, t} = pair-eq ((pair-eq (helper ×, {!!})) ×, refl) where
    subst-rename : ∀ {Γ Δ} {t : A ⊣ Γ} {r : Γ ⊸ Δ} → subst t (⊸→~> r) ≡ rename t r
    subst-rename {t = var e} = ⊸→~>-≡ refl
    subst-rename {t = ⊤} = refl
    subst-rename {t = ⊥} = refl
    subst-rename {t = if t then u else v} = {!!}
    subst-rename {t = nat _} = refl
    subst-rename {t = rec t u v} = {!!}
    subst-rename {t = abs t} = cong abs {!!}
    subst-rename {t = app t u} = {!!}
    ss-rs : ∀ {Γ Δ Θ} → {r : Δ ⊸ Θ} {σ : Γ ~> Δ} → ⊸→~> r ∙ss σ ≡ r ∙rs σ
    ss-rs {Γ = ε} {σ = Data.Unit.tt} = refl
    ss-rs {Γ = _ , _} {σ = σ ×, t} = pair-eq (ss-rs ×, {!!})
    helper : ⊸-wkn' ∙rs (ρ ∙ss σ) ≡ ~>-↑ ρ ∙ss (⊸-wkn' ∙rs σ)
    helper = {!!}

  sub-decomp : ∀ {e} {ρ : Δ ~> Θ} {σ : Γ ~> Δ} → sub {A = A} e (ρ ∙ss σ) ≡ subst (sub e σ) ρ
  sub-decomp {e = e0} = refl
  sub-decomp {e = eS e} = sub-decomp {e = e}

  subst-decomp : {ρ : Δ ~> Θ} {σ : Γ ~> Δ} → subst t (ρ ∙ss σ) ≡ subst (subst t σ) ρ
  subst-decomp {t = t} = sub→subst (λ A e → sub-decomp {e = e}) _ t
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
    (cong (λ v → rec _ _ v) {!!})
  subst-decomp {t = abs t} {ρ = ρ} {σ = σ} = cong
    abs
    (trans (cong (subst t) (↑-funct {ρ = ρ} {σ = σ})) (subst-decomp {t = t}))
  subst-decomp {t = app t u} = {!!}

  --lemma : Data.Product.proj₁ wkn* ≡

  --wkn-ext-id : {t : A ⊣ Γ} → ⟨ t ⟩ ∙ss wkn* ≡ id* {Γ}
  --wkn-ext-id {Γ = ε} = refl
  --wkn-ext-id {Γ = A , Γ} = pair-eq ({!!} ×, refl)
