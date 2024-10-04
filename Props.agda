--{-# OPTIONS --allow-unsolved-metas #-}

module Props where

  open import Relation.Binary.PropositionalEquality using
    (_≡_; refl; sym; cong; trans)
  open import Relation.Binary.PropositionalEquality.Properties using ()
  open Relation.Binary.PropositionalEquality.Properties.≡-Reasoning
  open import Data.Product using (proj₁; proj₂) renaming (_,_ to _×,_)
  open import Data.Product.Properties renaming (×-≡,≡→≡ to pair-eq)
  open import Data.Unit using (tt)

  open import Base
  open import Trans {Typ} renaming (_~>_ to _~>'_) --hiding (_~>_; sub)

  _~>_ : Context → Context → Set
  _~>_ = _~>'_ {_⊣_}

  private variable
    A B : Typ
    Γ Δ Θ E : Context
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
  --⊸-wkn' = ⊸-tail ⊸-refl

  ⊸-trans : Γ ⊸ Δ → Δ ⊸ Θ → Γ ⊸ Θ
  ⊸-trans {ε} _ _ = tt
  ⊸-trans {_ , _} r r' = ⊸-trans (⊸-tail r) r' ×, ren (⊸-head r) r'

  _∙rr_ : Δ ⊸ Θ → Γ ⊸ Δ → Γ ⊸ Θ
  _∙rr_ r' r = ⊸-trans r r'

  ⊸-↑ : Γ ⊸ Δ → (A , Γ) ⊸ (A , Δ)
  ⊸-↑ r = (⊸-wkn' ∙rr r) ×, e0

  ⊸-⟨_⟩ : A ∈ Γ → (A , Γ) ⊸ Γ
  ⊸-⟨_⟩ e = ⊸-refl ×, e

  rename : A ⊣ Γ → Γ ⊸ Δ → A ⊣ Δ
  rename (var e) r = var (ren e r)
  rename ⊤ _ = ⊤
  rename ⊥ _ = ⊥
  rename (if t then u else v) r = if rename t r then rename u r else rename v r
  rename z _ = z
  rename (s t) r = s (rename t r)
  rename (rec t u v) r = rec (rename t r) (rename u r) (rename v (⊸-↑ (⊸-↑ r)))
  rename (abs t) r = abs (rename t (⊸-↑ r))
  rename (app t u) r = app (rename t r) (rename u r)

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
  --~>-↑ σ = (~>-wkn σ) ×, var e0

  subst (var e) σ = sub e σ
  subst ⊤ _ = ⊤
  subst ⊥ _ = ⊥
  subst (if t then u else v) σ = if subst t σ then subst u σ else subst v σ
  subst z _ = z
  subst (s t) σ = s (subst t σ)
  subst (rec t u v) σ = rec (subst t σ) (subst u σ) (subst v (~>-↑ (~>-↑ σ)))
  subst (abs t) σ = abs (subst t (~>-↑ σ))
  subst (app t u) σ = app (subst t σ) (subst u σ)

  ∙rs→∙rr : {r' : Δ ⊸ Θ} {r : Γ ⊸ Δ}
          → r' ∙rs (⊸→~> r) ≡ ⊸→~> (r' ∙rr r)
  ∙rs→∙rr {Γ = ε} = refl
  ∙rs→∙rr {Γ = _ , _} = pair-eq (∙rs→∙rr ×, refl)

  ~>-↑-⊸-↑ : {r : Γ ⊸ Δ} → ~>-↑ {A = A} (⊸→~> r) ≡ ⊸→~> (⊸-↑ r)
  ~>-↑-⊸-↑ {Γ = ε} = refl
  ~>-↑-⊸-↑ {Γ = _ , _} {r = r} = pair-eq (∙rs→∙rr {r = r} ×, refl)

  ⊸→~>-rename-subst : {r : Γ ⊸ Δ} {t : A ⊣ Γ}
                    → rename t r ≡ subst t (⊸→~> r)
  ⊸→~>-rename-subst {t = var e} = sym (⊸→~>-≡ {e = e} refl)
  ⊸→~>-rename-subst {t = ⊤} = refl
  ⊸→~>-rename-subst {t = ⊥} = refl
  ⊸→~>-rename-subst {t = if t then u else v} = trans (trans
    (cong (λ t → if t then _ else _) ⊸→~>-rename-subst)
    (cong (λ u → if _ then u else _) ⊸→~>-rename-subst))
    (cong (λ v → if _ then _ else v) ⊸→~>-rename-subst)
  --⊸→~>-rename-subst {t = nat n} = refl
  ⊸→~>-rename-subst {t = z} = refl
  ⊸→~>-rename-subst {t = s t} = cong s ⊸→~>-rename-subst
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

  ⊸-wkn-decomp : {r : Γ ⊸ Δ} → ⊸-wkn {A = A} r ≡ ⊸-wkn' ∙rr r
  ⊸-wkn-decomp {Γ = ε} = refl
  ⊸-wkn-decomp {Γ = _ , _} {r = r} = pair-eq
    (⊸-wkn-decomp ×,
     sym (trans (⊸-wkn-prop {r = ⊸-refl} {e = ⊸-head r})
                (cong eS ⊸-refl-id)))

  ⊸-refl-↑ : ⊸-↑ {Γ = Γ} {A = A} ⊸-refl ≡ ⊸-refl
  ⊸-refl-↑ {Γ = ε} = refl
  ⊸-refl-↑ {Γ = _ , _} = pair-eq (sym ⊸-wkn-decomp ×, refl)

  ⊸-ext-wkn-id : {r' : Δ ⊸ Θ} {r : Γ ⊸ Δ} {e : A ∈ _}
              → (r' ×, e) ∙rr (⊸-wkn r) ≡ r' ∙rr r
  ⊸-ext-wkn-id {Γ = ε} = refl
  ⊸-ext-wkn-id {Γ = _ , _} = pair-eq (⊸-ext-wkn-id ×, refl)
  
  ⊸-refl-rid : {r : Γ ⊸ Δ} → ⊸-refl ∙rr r ≡ r
  ⊸-refl-rid {Γ = ε} = refl
  ⊸-refl-rid {Γ = _ , _} = pair-eq (⊸-refl-rid ×, ⊸-refl-id)
  
  ⊸-refl-lid : {r : Γ ⊸ Δ} → r ∙rr ⊸-refl ≡ r
  ⊸-refl-lid {Γ = ε} = refl
  ⊸-refl-lid {Γ = _ , _} {r = r} = pair-eq ((
    r ∙rr ⊸-wkn'          ≡⟨ ⊸-ext-wkn-id ⟩
    (⊸-tail r) ∙rr ⊸-refl ≡⟨ ⊸-refl-lid ⟩
    (⊸-tail r) ∎) ×,
    refl)

  ⊸-↑-wkn-id : {r : Γ ⊸ Δ}
             → ⊸-↑ {A = A} r ∙rr ⊸-wkn' ≡ ⊸-wkn' ∙rr r
  ⊸-↑-wkn-id {r = r} =
    ⊸-↑ r ∙rr ⊸-wkn'                ≡⟨ refl ⟩
    (⊸-wkn' ∙rr r ×, e0) ∙rr ⊸-wkn' ≡⟨ ⊸-ext-wkn-id {r = ⊸-refl} ⟩
    (⊸-wkn' ∙rr r) ∙rr ⊸-refl       ≡⟨ ⊸-refl-lid ⟩
    ⊸-wkn' ∙rr r ∎

  ∙rrr-assoc : {r'' : Θ ⊸ E} {r' : Δ ⊸ Θ} {r : Γ ⊸ Δ}
             → r'' ∙rr (r' ∙rr r) ≡ (r'' ∙rr r') ∙rr r
  ∙rrr-assoc {Γ = ε} = refl
  ∙rrr-assoc {Γ = _ , _} {r'' = r''} {r'} {r} = pair-eq
    (∙rrr-assoc ×,
     ren-decomp {r' = r''} {r'} {⊸-head r}) where
    ren-decomp : {Γ : Context} {r' : Δ ⊸ Θ} {r : Γ ⊸ Δ} {e : A ∈ Γ}
               → ren (ren e r) r' ≡ ren e (r' ∙rr r)
    ren-decomp {e = e0} = refl
    ren-decomp {e = eS e} = ren-decomp {e = e}

  ⊸-ext-⟨⟩ : {r : Γ ⊸ Δ} {e : A ∈ _} → (r ×, e) ≡ ⊸-⟨ e ⟩ ∙rr ⊸-↑ r
  ⊸-ext-⟨⟩ {Γ = ε} = refl
  ⊸-ext-⟨⟩ {Γ = _ , _} {r = r} {e} = pair-eq (sym (
    ⊸-⟨ e ⟩ ∙rr (⊸-wkn' ∙rr r) ≡⟨ ∙rrr-assoc {r = r} ⟩
    (⊸-⟨ e ⟩ ∙rr ⊸-wkn') ∙rr r ≡⟨ cong (λ r' → r' ∙rr r) ⊸-ext-wkn-id ⟩
    (⊸-refl ∙rr ⊸-refl) ∙rr r  ≡⟨ cong (λ r' → r' ∙rr r) ⊸-refl-rid ⟩
    ⊸-refl ∙rr r               ≡⟨ ⊸-refl-rid ⟩
    r ∎) ×, refl)

  ↑-∙rr : {r' : Δ ⊸ Θ} {r : Γ ⊸ Δ}
        → ⊸-↑ {A = A} r' ∙rr ⊸-↑ r ≡ ⊸-↑ (r' ∙rr r)
  ↑-∙rr {Γ = ε} = refl
  ↑-∙rr {Γ = _ , _} {r' = r'} {r} = pair-eq ((
    ⊸-↑ r' ∙rr (⊸-wkn' ∙rr r) ≡⟨ ∙rrr-assoc {r = r} ⟩
    (⊸-↑ r' ∙rr ⊸-wkn') ∙rr r ≡⟨ cong (λ r' → r' ∙rr r) ⊸-↑-wkn-id ⟩
    (⊸-wkn' ∙rr r') ∙rr r     ≡⟨ sym (∙rrr-assoc {r = r}) ⟩
    ⊸-wkn' ∙rr (r' ∙rr r) ∎) ×,
    refl)

  ∙rr-decomp : {r' : Δ ⊸ Θ} {r : Γ ⊸ Δ}
             → rename (rename t r) r' ≡ rename t (r' ∙rr r)
  ∙rr-decomp {t = var e} = cong var (helper {e = e}) where
    helper : ∀ {e} {r' : Δ ⊸ Θ} {r : Γ ⊸ Δ}
           → ren {A = A} (ren e r) r' ≡ ren e (r' ∙rr r)
    helper {e = e0} = refl
    helper {e = eS e} = helper {e = e}
  ∙rr-decomp {t = ⊤} = refl
  ∙rr-decomp {t = ⊥} = refl
  ∙rr-decomp {t = if t then u else v} = trans (trans
    (cong (λ t → if t then _ else _) (∙rr-decomp {t = t}))
    (cong (λ u → if _ then u else _) (∙rr-decomp {t = u})))
    (cong (λ v → if _ then _ else v) (∙rr-decomp {t = v}))
  ∙rr-decomp {t = z} = refl
  ∙rr-decomp {t = s t} = cong s (∙rr-decomp {t = t})
  ∙rr-decomp {t = rec t u v} {r = r} = trans (trans
    (cong (λ t → rec t _ _) (∙rr-decomp {t = t}))
    (cong (λ u → rec _ u _) (∙rr-decomp {t = u})))
    (cong (λ v → rec _ _ v)
          (trans (∙rr-decomp {t = v})
                 (cong (rename _) (trans (↑-∙rr {r = ⊸-↑ r}) (cong ⊸-↑ ↑-∙rr)))))
  ∙rr-decomp {t = abs t} =
    cong abs (trans ∙rr-decomp (cong (rename _) ↑-∙rr))
  ∙rr-decomp {t = app t u} = trans
    (cong (λ t → app t _) (∙rr-decomp {t = t}))
    (cong (λ u → app _ u) (∙rr-decomp {t = u}))

  ∙rrs-assoc : {r' : Θ ⊸ E} {r : Δ ⊸ Θ} {σ : Γ ~> Δ}
             → r' ∙rs (r ∙rs σ) ≡ (r' ∙rr r) ∙rs σ
  ∙rrs-assoc {Γ = ε} = refl
  ∙rrs-assoc {Γ = _ , _} {r' = r'} {r} {σ} =
    pair-eq (
      ∙rrs-assoc ×, (
      rename (rename (~>-head σ) r) r' ≡⟨ ∙rr-decomp ⟩
      rename (~>-head σ) (r' ∙rr r) ∎))

  ∙rsr-assoc : {r' : Θ ⊸ E} {σ : Δ ~> Θ} {r : Γ ⊸ Δ}
             → r' ∙rs (σ ∙sr r) ≡ (r' ∙rs σ) ∙sr r
  ∙rsr-assoc {Γ = ε} = refl
  ∙rsr-assoc {Γ = _ , _} {r = r} =
    pair-eq (∙rsr-assoc ×, helper {e = ⊸-head r}) where
    helper : ∀ {e} {r : Δ ⊸ Θ} {σ : Γ ~> Δ}
           → rename (sub e σ) r ≡ sub e (r ∙rs σ)
    helper {e = e0} = refl
    helper {e = eS e} = helper {e = e}

  ↑-∙rs : {r : Δ ⊸ Θ} {σ : Γ ~> Δ}
        → ⊸-↑ {A = A} r ∙rs ~>-↑ σ ≡ ~>-↑ (r ∙rs σ)
  ↑-∙rs {Γ = ε} = refl
  ↑-∙rs {Γ = _ , _} {r = r} {σ} = pair-eq ((
    ⊸-↑ r ∙rs (⊸-wkn' ∙rs σ) ≡⟨ ∙rrs-assoc ⟩
    (⊸-↑ r ∙rr ⊸-wkn') ∙rs σ ≡⟨ cong (λ r → r ∙rs σ) ⊸-↑-wkn-id ⟩
    (⊸-wkn' ∙rr r) ∙rs σ     ≡⟨ sym ∙rrs-assoc ⟩
    ⊸-wkn' ∙rs (r ∙rs σ) ∎) ×,
    refl)

  ∙rs-decomp : {r : Δ ⊸ Θ} {σ : Γ ~> Δ}
             → rename (subst t σ) r ≡ subst t (r ∙rs σ)
  ∙rs-decomp {t = var e} = helper {e = e} where
    helper : ∀ {e} {r : Δ ⊸ Θ} {σ : Γ ~> Δ}
           → rename (sub e σ) r ≡ sub e (r ∙rs σ)
    helper {e = e0} = refl
    helper {e = eS e} = helper {e = e}
  ∙rs-decomp {t = ⊤} = refl
  ∙rs-decomp {t = ⊥} = refl
  ∙rs-decomp {t = if t then u else v} = trans (trans
    (cong (λ t → if t then _ else _) (∙rs-decomp {t = t}))
    (cong (λ u → if _ then u else _) (∙rs-decomp {t = u})))
    (cong (λ v → if _ then _ else v) (∙rs-decomp {t = v}))
  ∙rs-decomp {t = z} = refl
  ∙rs-decomp {t = s t} = cong s (∙rs-decomp {t = t})
  ∙rs-decomp {t = rec t u v} {r = r} {σ} = trans (trans
    (cong (λ t → rec t _ _) (∙rs-decomp {t = t}))
    (cong (λ u → rec _ u _) (∙rs-decomp {t = u})))
    (cong (λ v → rec _ _ v)
          (trans (∙rs-decomp {t = v})
                 (cong (subst v) (trans (↑-∙rs {r = ⊸-↑ r} {~>-↑ σ})
                                        (cong ~>-↑ ↑-∙rs)))))
  ∙rs-decomp {t = abs t} {r = r} {σ} =
    cong abs
         (trans (∙rs-decomp {t = t} {σ = ~>-↑ σ})
                (cong (subst t) ↑-∙rs))
  ∙rs-decomp {t = app t u} = trans
    (cong (λ t → app t _) (∙rs-decomp {t = t}))
    (cong (λ u → app _ u) (∙rs-decomp {t = u}))

  ∙rss-assoc : {r : Θ ⊸ E} {ρ : Δ ~> Θ} {σ : Γ ~> Δ}
             → r ∙rs (ρ ∙ss σ) ≡ (r ∙rs ρ) ∙ss σ
  ∙rss-assoc {Γ = ε} = refl
  ∙rss-assoc {Γ = _ , _} {r = r} {ρ} {σ} =
    pair-eq (∙rss-assoc ×, helper {t = ~>-head σ}) where
    helper' : {r : Δ ⊸ Θ} {σ : Γ ~> Δ} {e : A ∈ _}
            → rename (sub e σ) r ≡ sub e (r ∙rs σ)
    helper' {e = e0} = refl
    helper' {e = eS e} = helper' {e = e}
    helper : {r : Δ ⊸ Θ} {σ : Γ ~> Δ}
           → rename (subst t σ) r ≡ subst t (r ∙rs σ)
    helper'' : {r : Δ ⊸ Θ} {σ : Γ ~> Δ}
             → ⊸-↑ {A = A} r ∙rs ~>-tail (~>-↑ σ) ≡ ~>-tail (~>-↑ (r ∙rs σ))
    helper'' {Γ = ε} = refl
    helper'' {Γ = _ , _} {r = r} {σ} = pair-eq (helper'' ×, (
      rename (rename (~>-head σ) ⊸-wkn') (⊸-↑ r) ≡⟨ ∙rr-decomp ⟩
      rename (~>-head σ) (⊸-↑ r ∙rr ⊸-wkn')      ≡⟨ cong (rename (~>-head σ)) ⊸-↑-wkn-id ⟩
      rename (~>-head σ) (⊸-wkn' ∙rr r)          ≡⟨ sym ∙rr-decomp ⟩
      rename (rename (~>-head σ) r) ⊸-wkn' ∎))
    helper {t = var e} = helper' {e = e}
    helper {t = ⊤} = refl
    helper {t = ⊥} = refl
    helper {t = if t then u else v} = trans (trans
      (cong (λ t → if t then _ else _) (helper {t = t}))
      (cong (λ u → if _ then u else _) (helper {t = u})))
      (cong (λ v → if _ then _ else v) (helper {t = v}))
    helper {t = z} = refl
    helper {t = s t} = cong s (helper {t = t})
    helper {t = rec t u v} {r = r} {σ} = trans (trans
      (cong (λ t → rec t _ _) (helper {t = t}))
      (cong (λ u → rec _ u _) (helper {t = u})))
      (cong (λ v → rec _ _ v) (
        rename (subst v (~>-↑ (~>-↑ σ))) (⊸-↑ (⊸-↑ r)) ≡⟨ ∙rs-decomp {t = v} ⟩
        subst v (⊸-↑ (⊸-↑ r) ∙rs ~>-↑ (~>-↑ σ))        ≡⟨ cong (subst v) (↑-∙rs {r = ⊸-↑ r} {σ = ~>-↑ σ}) ⟩
        subst v (~>-↑ (⊸-↑ r ∙rs ~>-↑ σ))              ≡⟨ cong (λ σ → subst v (~>-↑ σ)) ↑-∙rs ⟩
        subst v (~>-↑ (~>-↑ (r ∙rs σ))) ∎))
    helper {t = abs t} {r = r} {σ} = cong abs (trans
      (helper {t = t} {r = ⊸-↑ r} {~>-↑ σ})
      (cong (subst t) (pair-eq (helper'' ×, refl))))
    helper {t = app t u} = trans
      (cong (λ t → app t _) (helper {t = t}))
      (cong (λ u → app _ u) (helper {t = u}))

  rename-id : {t : A ⊣ Γ} → rename t ⊸-refl ≡ t
  rename-id {t = var e} = cong var ⊸-refl-id
  rename-id {t = ⊤} = refl
  rename-id {t = ⊥} = refl
  rename-id {t = if t then u else v} = trans (trans
    (cong (λ t → if t then _ else _) (rename-id {t = t}))
    (cong (λ u → if _ then u else _) (rename-id {t = u})))
    (cong (λ v → if _ then _ else v) (rename-id {t = v}))
  rename-id {t = z} = refl
  rename-id {t = s t} = cong s (rename-id {t = t})
  rename-id {t = rec t u v} = trans (trans
    (cong (λ t → rec t _ _) (rename-id {t = t}))
    (cong (λ u → rec _ u _) (rename-id {t = u})))
    (cong (λ v → rec _ _ v) (
      rename v (⊸-↑ (⊸-↑ ⊸-refl)) ≡⟨ cong (λ r → rename v (⊸-↑ r)) ⊸-refl-↑ ⟩
      rename v (⊸-↑ ⊸-refl)       ≡⟨ cong (rename v) ⊸-refl-↑ ⟩
      rename v ⊸-refl             ≡⟨ rename-id ⟩
      v ∎))
  rename-id {t = abs t} =
    cong abs
         (rename t (⊸-↑ ⊸-refl) ≡⟨ cong (rename t) ⊸-refl-↑ ⟩
          rename t ⊸-refl       ≡⟨ rename-id ⟩
          t ∎)
  rename-id {t = app t u} = trans
    (cong (λ t → app t _) (rename-id {t = t}))
    (cong (λ u → app _ u) (rename-id {t = u}))

  subst-id : {t : A ⊣ Γ} → subst t ~>-refl ≡ t
  subst-id {t = var _} = ~>-refl-id
  subst-id {t = ⊤} = refl
  subst-id {t = ⊥} = refl
  subst-id {t = if t then u else v} = trans (trans
    (cong (λ t → if t then _ else _) (subst-id {t = t}))
    (cong (λ u → if _ then u else _) (subst-id {t = u})))
    (cong (λ v → if _ then _ else v) (subst-id {t = v}))
  subst-id {t = z} = refl
  subst-id {t = s t} = cong s (subst-id {t = t})
  subst-id {t = rec t u v} = trans (trans
    (cong (λ t → rec t _ _) (subst-id {t = t}))
    (cong (λ u → rec _ u _) (subst-id {t = u})))
    (cong (λ v → rec _ _ v) (
      subst v (~>-↑ (~>-↑ (⊸→~> ⊸-refl))) ≡⟨ cong (λ σ → subst v (~>-↑ σ)) ~>-↑-⊸-↑ ⟩
      subst v (~>-↑ (⊸→~> (⊸-↑ ⊸-refl)))  ≡⟨ cong (subst v) (~>-↑-⊸-↑ {r = ⊸-↑ ⊸-refl}) ⟩
      subst v (⊸→~> (⊸-↑ (⊸-↑ ⊸-refl)))   ≡⟨ cong (λ r → subst v (⊸→~> (⊸-↑ r))) ⊸-refl-↑ ⟩
      subst v (⊸→~> (⊸-↑ ⊸-refl))         ≡⟨ cong (λ r → subst v (⊸→~> r)) ⊸-refl-↑ ⟩
      subst v (⊸→~> ⊸-refl)               ≡⟨ sym ⊸→~>-rename-subst ⟩
      rename v ⊸-refl                     ≡⟨ rename-id ⟩
      v ∎))
  subst-id {t = abs t} = cong abs (
    subst t (~>-↑ (⊸→~> ⊸-refl)) ≡⟨ cong (subst t) ~>-↑-⊸-↑ ⟩
    subst t (⊸→~> (⊸-↑ ⊸-refl))  ≡⟨ cong (λ r → subst t (⊸→~> r)) ⊸-refl-↑ ⟩
    subst t (⊸→~> ⊸-refl)        ≡⟨ sym ⊸→~>-rename-subst ⟩
    rename t ⊸-refl              ≡⟨ rename-id ⟩
    t ∎)
  subst-id {t = app t u} = trans
    (cong (λ t → app t _) (subst-id {t = t}))
    (cong (λ u → app _ u) (subst-id {t = u}))

  ~>-refl-∙ss-id : {σ : Γ ~> Δ} → ~>-refl ∙ss σ ≡ σ
  ~>-refl-∙ss-id {Γ = ε} = refl
  ~>-refl-∙ss-id {Γ = _ , _} =
    pair-eq (~>-refl-∙ss-id ×, subst-id)

  ∙srs-assoc : {ρ : Θ ~> E} {r : Δ ⊸ Θ} {σ : Γ ~> Δ}
             → ρ ∙ss (r ∙rs σ) ≡ (ρ ∙sr r) ∙ss σ

  ∙srr-assoc : {σ : Θ ~> E} {r' : Δ ⊸ Θ} {r : Γ ⊸ Δ}
             → σ ∙sr (r' ∙rr r) ≡ (σ ∙sr r') ∙sr r
  ∙srr-assoc {Γ = ε} = refl
  ∙srr-assoc {Γ = _ , _} {r = r} =
    pair-eq (∙srr-assoc ×, helper {e = ⊸-head r}) where
    helper : {σ : Δ ~> Θ} {r : Γ ⊸ Δ} {e : A ∈ _}
           → sub (ren e r) σ ≡ sub e (σ ∙sr r)
    helper {e = e0} = refl
    helper {e = eS e} = helper {e = e}

  ~>-ext-wkn-id : {σ : Δ ~> Θ} {t : A ⊣ _} {r : Γ ⊸ Δ}
                → (σ ×, t) ∙sr (⊸-wkn r) ≡ σ ∙sr r
  ~>-ext-wkn-id {Γ = ε} = refl
  ~>-ext-wkn-id {Γ = _ , _} = pair-eq (~>-ext-wkn-id ×, refl)

  ~>-refl-rid : {σ : Γ ~> Δ} → σ ∙sr ⊸-refl ≡ σ
  ~>-refl-rid {Γ = ε} = refl
  ~>-refl-rid {Γ = _ , _} {σ = σ} = pair-eq ((
     σ ∙sr ⊸-wkn'           ≡⟨ ~>-ext-wkn-id ⟩
     (~>-tail σ) ∙sr ⊸-refl ≡⟨ ~>-refl-rid ⟩
     ~>-tail σ ∎) ×,
     refl)

  ~>-refl'-lid : {σ : Γ ~> Δ} → ~>-refl ∙ss σ ≡ σ
  ~>-refl'-lid {Γ = ε} = refl
  ~>-refl'-lid {Γ = _ , _} =
    pair-eq (~>-refl'-lid ×, subst-id)

  ~>-↑-wkn-id : {σ : Γ ~> Δ}
              → ~>-↑ {A = A} σ ∙sr ⊸-wkn' ≡ ⊸-wkn' ∙rs σ
  ~>-↑-wkn-id {σ = σ} =
    (⊸-wkn' ∙rs σ ×, var e0) ∙sr ⊸-wkn' ≡⟨ ~>-ext-wkn-id {r = ⊸-refl} ⟩
    (⊸-wkn' ∙rs σ) ∙sr ⊸-refl           ≡⟨ ~>-refl-rid ⟩
    ⊸-wkn' ∙rs σ ∎

  ↑-∙sr : {σ : Δ ~> Θ} {r : Γ ⊸ Δ}
        → ~>-↑ {A = A} σ ∙sr ⊸-↑ r ≡ ~>-↑ (σ ∙sr r)
  ↑-∙sr {Γ = ε} = refl
  ↑-∙sr {Γ = _ , _} {σ = σ} {r} = pair-eq ((
    ~>-↑ σ ∙sr (⊸-wkn' ∙rr r) ≡⟨ ∙srr-assoc {r = r} ⟩
    (~>-↑ σ ∙sr ⊸-wkn') ∙sr r ≡⟨ cong (λ σ → σ ∙sr r) ~>-↑-wkn-id ⟩
    (⊸-wkn' ∙rs σ) ∙sr r      ≡⟨ sym (∙rsr-assoc {r = r}) ⟩
    ⊸-wkn' ∙rs (σ ∙sr r) ∎) ×, refl)

  ∙sr-decomp : {σ : Δ ~> Θ} {r : Γ ⊸ Δ}
             → subst (rename t r) σ ≡ subst t (σ ∙sr r)
  ∙sr-decomp {t = var e} {σ = σ} {r} = helper {e = e} where
    helper : {σ : Δ ~> Θ} {r : Γ ⊸ Δ} {e : A ∈ _}
           → sub (ren e r) σ ≡ sub e (σ ∙sr r)
    helper {e = e0} = refl
    helper {e = eS e} = helper {e = e}
  ∙sr-decomp {t = ⊤} = refl
  ∙sr-decomp {t = ⊥} = refl
  ∙sr-decomp {t = if t then u else v} = trans (trans
    (cong (λ t → if t then _ else _) (∙sr-decomp {t = t}))
    (cong (λ u → if _ then u else _) (∙sr-decomp {t = u})))
    (cong (λ v → if _ then _ else v) (∙sr-decomp {t = v}))
  ∙sr-decomp {t = z} = refl
  ∙sr-decomp {t = s t} = cong s (∙sr-decomp {t = t})
  ∙sr-decomp {t = rec t u v} {σ = σ} {r} = trans (trans
      (cong (λ t → rec t _ _) (∙sr-decomp {t = t}))
      (cong (λ u → rec _ u _) (∙sr-decomp {t = u})))
      (cong (λ v → rec _ _ v) (
        subst (rename v (⊸-↑ (⊸-↑ r))) (~>-↑ (~>-↑ σ)) ≡⟨ ∙sr-decomp {t = v} ⟩
        subst v (~>-↑ (~>-↑ σ) ∙sr ⊸-↑ (⊸-↑ r))        ≡⟨ cong (subst v) (↑-∙sr {r = ⊸-↑ r}) ⟩
        subst v (~>-↑ (~>-↑ σ ∙sr ⊸-↑ r))              ≡⟨ cong (λ σ → subst v (~>-↑ σ)) ↑-∙sr ⟩
        subst v (~>-↑ (~>-↑ (σ ∙sr r))) ∎))
  ∙sr-decomp {t = abs t} {σ = σ} {r} =
    cong abs (
      subst (rename t (⊸-↑ r)) (~>-↑ σ) ≡⟨ ∙sr-decomp {t = t} ⟩
      subst t (~>-↑ σ ∙sr ⊸-↑ r)        ≡⟨ cong (subst t) ↑-∙sr ⟩
      subst t (~>-↑ (σ ∙sr r)) ∎)
  ∙sr-decomp {t = app t u} = trans
    (cong (λ t → app t _) (∙sr-decomp {t = t}))
    (cong (λ u → app _ u) (∙sr-decomp {t = u}))

  ∙srs-assoc {Γ = ε} = refl
  ∙srs-assoc {Γ = _ , _} {ρ = ρ} {r} {σ} =
    pair-eq (∙srs-assoc ×, helper {t = ~>-head σ}) where
    helper' : {σ : Δ ~> Θ} {r : Γ ⊸ Δ} {e : A ∈ _}
           → sub (ren e r) σ ≡ sub e (σ ∙sr r)
    helper' {e = e0} = refl
    helper' {e = eS e} = helper' {e = e}
    helper : subst (rename t r) ρ ≡ subst t (ρ ∙sr r)
    helper {t = var e} = helper' {e = e}
    helper {t = ⊤} = refl
    helper {t = ⊥} = refl
    helper {t = if t then u else v} = trans (trans
      (cong (λ t → if t then _ else _) (helper {t = t}))
      (cong (λ u → if _ then u else _) (helper {t = u})))
      (cong (λ v → if _ then _ else v) (helper {t = v}))
    helper {t = z} = refl
    helper {t = s t} = cong s (helper {t = t})
    helper {t = rec t u v} = trans (trans
      (cong (λ t → rec t _ _) (helper {t = t}))
      (cong (λ u → rec _ u _) (helper {t = u})))
      (cong (λ v → rec _ _ v) (
        subst (rename v (⊸-↑ (⊸-↑ r))) (~>-↑ (~>-↑ ρ)) ≡⟨ ∙sr-decomp {t = v} ⟩
        subst v (~>-↑ (~>-↑ ρ) ∙sr ⊸-↑ (⊸-↑ r))        ≡⟨ cong (subst v) (↑-∙sr {r = ⊸-↑ r}) ⟩
        subst v (~>-↑ (~>-↑ ρ ∙sr ⊸-↑ r))              ≡⟨ cong (λ σ → subst v (~>-↑ σ)) ↑-∙sr ⟩
        subst v (~>-↑ (~>-↑ (ρ ∙sr r))) ∎))
    helper {t = abs t} = cong abs (
      subst (rename t (⊸-↑ r)) (~>-↑ ρ) ≡⟨ ∙sr-decomp {t = t} ⟩
      subst t (~>-↑ ρ ∙sr ⊸-↑ r)        ≡⟨ cong (subst t) ↑-∙sr ⟩
      subst t (~>-↑ (ρ ∙sr r)) ∎)
    helper {t = app t u} = trans
      (cong (λ t → app t _) (helper {t = t}))
      (cong (λ u → app _ u) (helper {t = u}))

  ~>-ext-⟨⟩ : {σ : Γ ~> Δ} {t : A ⊣ Δ}
            → (σ ×, t) ≡ ⟨ t ⟩ ∙ss ~>-↑ σ
  ~>-ext-⟨⟩ {Γ = ε} = refl
  ~>-ext-⟨⟩ {Γ = _ , _} {σ = σ} {t} = pair-eq (sym (
    ⟨ t ⟩ ∙ss (⊸-wkn' ∙rs σ)   ≡⟨ ∙srs-assoc {σ = σ} ⟩
    (⟨ t ⟩ ∙sr ⊸-wkn') ∙ss σ   ≡⟨ cong (λ ρ → ρ ∙ss σ) ~>-ext-wkn-id ⟩
    (~>-refl ∙sr ⊸-refl) ∙ss σ ≡⟨ cong (λ ρ → ρ ∙ss σ) ~>-refl-rid ⟩
    ~>-refl ∙ss σ              ≡⟨ ~>-refl'-lid ⟩
    σ ∎) ×,
    refl)

  ↑-∙ss : {ρ : Δ ~> Θ} {σ : Γ ~> Δ} → ~>-↑ {A = A} (ρ ∙ss σ) ≡ ~>-↑ ρ ∙ss ~>-↑ σ
  ↑-∙ss {ρ = ρ} {σ}  = pair-eq ((
    ⊸-wkn' ∙rs (ρ ∙ss σ)                          ≡⟨ ∙rss-assoc ⟩
    (⊸-wkn' ∙rs ρ) ∙ss σ                          ≡⟨ cong (λ ρ → ρ ∙ss σ) (sym helper) ⟩
    (((⊸-wkn' ∙rs ρ) ×, var e0) ∙sr ⊸-wkn') ∙ss σ ≡⟨ sym ∙srs-assoc ⟩
    ((⊸-wkn' ∙rs ρ) ×, var e0) ∙ss (⊸-wkn' ∙rs σ) ∎) ×,
    refl) where
    helper' : {σ : Δ ~> Θ} {r : Γ ⊸ Δ} {t : A ⊣ _}
            → (σ ×, t) ∙sr (⊸-wkn r) ≡ σ ∙sr r
    helper' {Γ = ε} = refl
    helper' {Γ = _ , _} = pair-eq (helper' ×, refl)
    helper : {σ : Γ ~> Δ} {t : A ⊣ _} → (σ ×, t) ∙sr ⊸-wkn' ≡ σ
    ⊸-refl-∙sr-id : {σ : Γ ~> Δ} → σ ∙sr ⊸-refl ≡ σ
    ⊸-refl-∙sr-id {Γ = ε} = refl
    ⊸-refl-∙sr-id {Γ = _ , _} {σ = σ} = pair-eq (helper ×, refl)
    helper = trans (helper' {r = ⊸-refl}) ⊸-refl-∙sr-id

  ∙ss-decomp : {ρ : Δ ~> Θ} {σ : Γ ~> Δ} → subst t (ρ ∙ss σ) ≡ subst (subst t σ) ρ
  ∙ss-decomp {t = var e} = helper {e = e} where
    helper : ∀ {e} {ρ : Δ ~> Θ} {σ : Γ ~> Δ} → sub {A = A} e (ρ ∙ss σ) ≡ subst (sub e σ) ρ
    helper {e = e0} = refl
    helper {e = eS e} = helper {e = e}
  ∙ss-decomp {t = ⊤} = refl
  ∙ss-decomp {t = ⊥} = refl
  ∙ss-decomp {t = if t then u else v} = trans (trans
    (cong (λ t → if t then _ else _) (∙ss-decomp {t = t}))
    (cong (λ u → if _ then u else _) (∙ss-decomp {t = u})))
    (cong (λ v → if _ then _ else v) (∙ss-decomp {t = v}))
  ∙ss-decomp {t = z} = refl
  ∙ss-decomp {t = s t} = cong s (∙ss-decomp {t = t})
  ∙ss-decomp {t = rec t u v} {ρ = ρ} {σ} = trans (trans
    (cong (λ t → rec t _ _) (∙ss-decomp {t = t}))
    (cong (λ u → rec _ u _) (∙ss-decomp {t = u})))
    (cong (λ v → rec _ _ v) (trans
      (cong (subst v) (trans (cong ~>-↑ ↑-∙ss)
                             (↑-∙ss {σ = ~>-↑ σ})))
      (∙ss-decomp {t = v})))
  ∙ss-decomp {t = abs t} {ρ = ρ} {σ} =
    cong abs (trans (cong (subst t) ↑-∙ss)
                    (∙ss-decomp {t = t}))
  ∙ss-decomp {t = app t u} = trans
    (cong (λ t → app t _) (∙ss-decomp {t = t}))
    (cong (λ u → app _ u) (∙ss-decomp {t = u}))

  ∙sss-assoc : {θ : Θ ~> E} {ρ : Δ ~> Θ} {σ : Γ ~> Δ}
             → θ ∙ss (ρ ∙ss σ) ≡ (θ ∙ss ρ) ∙ss σ
  ∙sss-assoc {Γ = ε} = refl
  ∙sss-assoc {Γ = _ , _} {σ = σ} =
    pair-eq (∙sss-assoc ×, sym (∙ss-decomp {t = ~>-head σ}))
