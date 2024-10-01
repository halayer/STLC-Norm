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
  rename (var {A} e) r = var (ren e r)
  rename ⊤ _ = ⊤
  rename ⊥ _ = ⊥
  rename (if t then u else v) r = if rename t r then rename u r else rename v r
  rename (nat n) _ = nat n
  rename (rec t u v) r = rec (rename t r) (rename u r) (rename v (⊸-↑ (⊸-↑ r)))
  rename (abs t) r = abs (rename t (⊸-↑ r))
  rename (app t u) r = app (rename t r) (rename u r)

  ⊸-wkn-decomp : {r : Γ ⊸ Δ} → ⊸-wkn {A = A} r ≡ ⊸-wkn' ∙rr r
  ⊸-wkn-decomp {Γ = ε} = refl
  ⊸-wkn-decomp {Γ = _ , _} {r = r} = pair-eq
    (⊸-wkn-decomp ×,
     sym (trans (⊸-wkn-prop {r = ⊸-refl} {e = ⊸-head r})
                (cong eS ⊸-refl-id)))

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
  subst (nat n) _ = nat n
  subst (rec t u v) σ = rec (subst t σ) (subst u σ) (subst v (~>-↑ (~>-↑ σ)))
  subst (abs t) σ = abs (subst t (~>-↑ σ))
  subst (app t u) σ = app (subst t σ) (subst u σ)

  --⊸-tail→~>-tail : {r : (A , Γ) ⊸ Δ}
  --               → ~>-tail (⊸→~> r) ≡ ⊸→~> (⊸-tail r)
  --⊸-tail→~>-tail {Γ = Γ} {r = r} = refl

  --∙rs→∙rr : {r' : Δ ⊸ Θ} {r : Γ ⊸ Δ}
  --        → r' ∙rs (⊸→~> r) ≡ ⊸→~> (r' ∙rr r)
  --∙rs→∙rr {Γ = ε} = refl
  --∙rs→∙rr {Γ = _ , _} {r' = r'} {r} = pair-eq
  --  (trans (cong (_∙rs_ r') (⊸-tail→~>-tail {r = r})) ∙rs→∙rr ×,
  --   refl)

  --~>-↑-⊸-↑ : {r : Γ ⊸ Δ} → ~>-↑ {A = A} (⊸→~> r) ≡ ⊸→~> (⊸-↑ r)
  --~>-↑-⊸-↑ {Γ = ε} = refl
  --~>-↑-⊸-↑ {Γ = _ , _} {r = r} = pair-eq (∙rs→∙rr {r = r} ×, refl)

  --⊸→~>-rename-subst : {r : Γ ⊸ Δ} {t : A ⊣ Γ}
  --                  → rename t r ≡ subst t (⊸→~> r)
  --⊸→~>-rename-subst {t = var e} = sym (⊸→~>-≡ {e = e} refl)
  --⊸→~>-rename-subst {t = ⊤} = refl
  --⊸→~>-rename-subst {t = ⊥} = refl
  --⊸→~>-rename-subst {t = if t then u else v} = trans (trans
  --  (cong (λ t → if t then _ else _) ⊸→~>-rename-subst)
  --  (cong (λ u → if _ then u else _) ⊸→~>-rename-subst))
  --  (cong (λ v → if _ then _ else v) ⊸→~>-rename-subst)
  --⊸→~>-rename-subst {t = nat n} = refl
  --⊸→~>-rename-subst {t = rec t u v} = trans (trans
  --  (cong (λ t → rec t _ _) ⊸→~>-rename-subst)
  --  (cong (λ u → rec _ u _) ⊸→~>-rename-subst))
  --  (cong (λ v → rec _ _ v) (trans
  --    ⊸→~>-rename-subst
  --    (cong (subst v)
  --          (trans (sym (~>-↑-⊸-↑ {r = ⊸-↑ _}))
  --                 (cong ~>-↑ (sym ~>-↑-⊸-↑))))))
  --⊸→~>-rename-subst {r = r} {t = abs t} = cong
  --  abs (trans ⊸→~>-rename-subst (cong (subst t) (sym ~>-↑-⊸-↑)))
  --⊸→~>-rename-subst {t = app t u} = trans
  --  (cong (λ t → app t _) ⊸→~>-rename-subst)
  --  (cong (λ u → app _ u) ⊸→~>-rename-subst)

  --~>-wkn-decomp : {σ : Γ ~> Δ} → ~>-wkn {A = A} σ ≡ ~>-wkn' ∙ss σ
  --~>-wkn-decomp {Γ = ε} = refl
  --~>-wkn-decomp {Γ = _ , _} {σ = σ} = pair-eq
  --  (~>-wkn-decomp ×, ⊸→~>-rename-subst)

  --∙rrr-assoc : {r'' : Θ ⊸ E} {r' : Δ ⊸ Θ} {r : Γ ⊸ Δ}
  --           → r'' ∙rr (r' ∙rr r) ≡ (r'' ∙rr r') ∙rr r
  --∙rrr-assoc {Γ = ε} = refl
  --∙rrr-assoc {Γ = _ , _} {r'' = r''} {r'} {r} = pair-eq
  --  (∙rrr-assoc ×,
  --   ren-decomp {r' = r''} {r'} {⊸-head r}) where
  --  ren-decomp : {Γ : Context} {r' : Δ ⊸ Θ} {r : Γ ⊸ Δ} {e : A ∈ Γ}
  --             → ren (ren e r) r' ≡ ren e (r' ∙rr r)
  --  ren-decomp {e = e0} = refl
  --  ren-decomp {e = eS e} = ren-decomp {e = e}

  --⊸-refl-∙rr-id : {r : Γ ⊸ Δ} → ⊸-refl ∙rr r ≡ r
  --⊸-refl-∙rr-id {Γ = ε} = refl
  --⊸-refl-∙rr-id {Γ = _ , _} =
  --  pair-eq (⊸-refl-∙rr-id ×, ⊸-refl-id)

  --⊸-wkn-⟨⟩-id : {r : Γ ⊸ Δ} {e : A ∈ Δ} → ⊸-⟨ e ⟩ ∙rr (⊸-wkn r) ≡ r
  --⊸-wkn-⟨⟩-id {Γ = ε} = refl
  --⊸-wkn-⟨⟩-id {Γ = _ , _} = pair-eq (⊸-wkn-⟨⟩-id ×, ⊸-refl-id)

  --⊸-extend-⟨⟩ : {r : Γ ⊸ Δ} {e : A ∈ Δ}
  --            → (r ×, e) ≡ ⊸-⟨ e ⟩ ∙rr ⊸-↑ r
  --⊸-extend-⟨⟩ {Γ = ε} = refl
  --⊸-extend-⟨⟩ {Γ = _ , _} {r = r} = pair-eq (sym (trans (trans
  --  (∙rrr-assoc {r'' = ⊸-⟨ _ ⟩} {⊸-wkn'} {r})
  --  (cong (λ r' → r' ∙rr r) (⊸-wkn-⟨⟩-id {r = ⊸-refl})))
  --  ⊸-refl-∙rr-id) ×,
  --  refl)

  --⊸-refl-↑ : ⊸-↑ {Γ = Γ} {A = A} ⊸-refl ≡ ⊸-refl
  --⊸-refl-↑ {Γ = ε} = refl
  --⊸-refl-↑ {Γ = _ , _} = pair-eq (sym ⊸-wkn-decomp ×, refl)

  --↑-∙rr : {r' : Δ ⊸ Θ} {r : Γ ⊸ Δ}
  --      → ⊸-↑ {A = A} r' ∙rr ⊸-↑ r ≡ ⊸-↑ (r' ∙rr r)
  --↑-∙rr {Γ = ε} = refl
  --↑-∙rr {Γ = _ , _} {r = r} = pair-eq
  --  (trans (trans (∙rrr-assoc {r = r})
  --                (cong (λ r' → r' ∙rr r) (trans helper ⊸-wkn-decomp)))
  --         (sym (∙rrr-assoc {r = r})) ×,
  --   refl) where
  --  helper' : {Γ : Context} {r : (A , Γ) ⊸ Δ}
  --          → r ∙rr ⊸-wkn' ≡ ⊸-tail r
  --  helper' {Γ = ε} = refl
  --  --helper' {Γ = _ , ε} = pair-eq (refl ×, refl)
  --  --helper' {Γ = _ , (_ , ε)} = pair-eq ({!!} ×, refl)
  --  --helper' {Γ = _ , (_ , (_ , ε))} = pair-eq (refl ×, refl)
  --  --helper' {Γ = _ , (_ , (_ , (_ , ε)))} = refl
  --  --helper' {Γ = _ , (_ , (_ , (_ , (_ , ε))))} = refl
  --  helper' {Γ = _ , _} {r = r@(r' ×, e)} = pair-eq
  --    ({!!} ×,
  --     refl)
  --  helper : {Γ : Context} {r : Γ ⊸ Δ}
  --         → ⊸-↑ {A = A} r ∙rr ⊸-wkn' ≡ ⊸-wkn r
  --  helper {Γ = ε} = refl
  --  helper {Γ = _ , ε} {r@(r' ×, e)} = pair-eq
  --    (refl ×, 
  --     trans (⊸-wkn-prop {e = e}) (cong eS ⊸-refl-id))
  --  helper {Γ = _ , (_ , ε)} {r = r@(r' ×, e)} = pair-eq
  --    (helper {r = r'} ×,
  --     trans (⊸-wkn-prop {e = e}) (cong eS ⊸-refl-id))
  --  helper {Γ = _ , (_ , (_ , ε))} {r = r@(r' ×, e)} = pair-eq
  --    (helper {r = r'} ×,
  --     trans (⊸-wkn-prop {e = e}) (cong eS ⊸-refl-id))
  --  helper {Γ = _ , _} {r = r@(r' ×, e)} = pair-eq (
  --    {!!} ×,
  --    trans (⊸-wkn-prop {e = e}) (cong eS ⊸-refl-id))

  --∙rr-decomp : {r' : Δ ⊸ Θ} {r : Γ ⊸ Δ}
  --           → rename (rename t r) r' ≡ rename t (r' ∙rr r)
  --∙rr-decomp {t = var e} = cong var (helper {e = e}) where
  --  helper : ∀ {e} {r' : Δ ⊸ Θ} {r : Γ ⊸ Δ}
  --         → ren {A = A} (ren e r) r' ≡ ren e (r' ∙rr r)
  --  helper {e = e0} = refl
  --  helper {e = eS e} = helper {e = e}
  --∙rr-decomp {t = ⊤} = refl
  --∙rr-decomp {t = ⊥} = refl
  --∙rr-decomp {t = if t then u else v} = trans (trans
  --  (cong (λ t → if t then _ else _) (∙rr-decomp {t = t}))
  --  (cong (λ u → if _ then u else _) (∙rr-decomp {t = u})))
  --  (cong (λ v → if _ then _ else v) (∙rr-decomp {t = v}))
  --∙rr-decomp {t = nat _} = refl
  --∙rr-decomp {t = rec t u v} {r = r} = trans (trans
  --  (cong (λ t → rec t _ _) (∙rr-decomp {t = t}))
  --  (cong (λ u → rec _ u _) (∙rr-decomp {t = u})))
  --  (cong (λ v → rec _ _ v)
  --        (trans (∙rr-decomp {t = v})
  --               (cong (rename _) (trans (↑-∙rr {r = ⊸-↑ r}) (cong ⊸-↑ ↑-∙rr)))))
  --∙rr-decomp {t = abs t} =
  --  cong abs (trans ∙rr-decomp (cong (rename _) ↑-∙rr))
  --∙rr-decomp {t = app t u} = trans
  --  (cong (λ t → app t _) (∙rr-decomp {t = t}))
  --  (cong (λ u → app _ u) (∙rr-decomp {t = u}))
  --
  --↑-∙rs : {r : Δ ⊸ Θ} {σ : Γ ~> Δ}
  --      → ⊸-↑ {A = A} r ∙rs ~>-↑ σ ≡ ~>-↑ (r ∙rs σ)
  --↑-∙rs {Γ = ε} = refl
  --↑-∙rs {Γ = _ , _} {r = r} {σ} = pair-eq
  --  ({!!} ×,
  --   refl)

  --∙rs-decomp : {r : Δ ⊸ Θ} {σ : Γ ~> Δ}
  --           → rename (subst t σ) r ≡ subst t (r ∙rs σ)
  --∙rs-decomp {t = var e} {r = r} = helper {e = e} where
  --  helper : ∀ {e} {r : Δ ⊸ Θ} {σ : Γ ~> Δ}
  --         → rename {A = A} (sub e σ) r ≡ sub e (r ∙rs σ)
  --  helper {e = e0} = refl
  --  helper {e = eS e} = helper {e = e}
  --∙rs-decomp {t = ⊤} = refl
  --∙rs-decomp {t = ⊥} = refl
  --∙rs-decomp {t = if t then u else v} = trans (trans
  --  (cong (λ t → if t then _ else _) (∙rs-decomp {t = t}))
  --  (cong (λ u → if _ then u else _) (∙rs-decomp {t = u})))
  --  (cong (λ v → if _ then _ else v) (∙rs-decomp {t = v}))
  --∙rs-decomp {t = nat _} = refl
  --∙rs-decomp {t = rec t u v} {r = r} {σ} = trans (trans
  --  (cong (λ t → rec t _ _) (∙rs-decomp {t = t}))
  --  (cong (λ u → rec _ u _) (∙rs-decomp {t = u})))
  --  (cong (λ v → rec _ _ v)
  --        (trans (∙rs-decomp {t = v})
  --               (cong (subst v)
  --                     (trans (↑-∙rs {r = ⊸-↑ r} {~>-↑ σ})
  --                            (cong ~>-↑ ↑-∙rs)))))
  --∙rs-decomp {t = abs t} {r = r} {σ} =
  --  cong abs (trans (∙rs-decomp {t = t}) (cong (subst t) ↑-∙rs))
  --∙rs-decomp {t = app t u} = trans
  --  (cong (λ t → app t _) (∙rs-decomp {t = t}))
  --  (cong (λ u → app _ u) (∙rs-decomp {t = u}))

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
    helper'' {Γ = _ , _} = pair-eq ({!!} ×, {!!})
    helper {t = var e} = helper' {e = e}
    helper {t = ⊤} = refl
    helper {t = ⊥} = refl
    helper {t = if t then u else v} = trans (trans
      (cong (λ t → if t then _ else _) (helper {t = t}))
      (cong (λ u → if _ then u else _) (helper {t = u})))
      (cong (λ v → if _ then _ else v) (helper {t = v}))
    helper {t = nat _} = refl
    helper {t = rec t u v} = trans (trans
      (cong (λ t → rec t _ _) (helper {t = t}))
      (cong (λ u → rec _ u _) (helper {t = u})))
      (cong (λ v → rec _ _ v) {!!})
    helper {t = abs t} {r = r} {σ} = cong abs (trans
      (helper {t = t} {r = ⊸-↑ r} {~>-↑ σ})
      (cong (subst t) (pair-eq (helper'' ×, refl))))
    helper {t = app t u} = trans
      (cong (λ t → app t _) (helper {t = t}))
      (cong (λ u → app _ u) (helper {t = u}))

  ~>-refl-∙ss-id : {σ : Γ ~> Δ} → ~>-refl ∙ss σ ≡ σ
  ~>-refl-∙ss-id {Γ = ε} = refl
  ~>-refl-∙ss-id {Γ = _ , _} = pair-eq ({!!} ×, {!!})

  ∙srs-assoc : {ρ : Θ ~> E} {r : Δ ⊸ Θ} {σ : Γ ~> Δ}
             → ρ ∙ss (r ∙rs σ) ≡ (ρ ∙sr r) ∙ss σ
  ∙srs-assoc {Γ = ε} = refl
  ∙srs-assoc {Γ = _ , _} = pair-eq ({!!} ×, {!!})

  test : {r : Δ ⊸ Θ} {r' : Γ ⊸ Δ} {e : A ∈ _} → (r ×, e) ∙rr (⊸-wkn r') ≡ r ∙rr r'
  test {Γ = ε} = refl
  test {Γ = _ , _} = pair-eq (test ×, refl)

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
  ∙ss-decomp {t = nat _} = refl
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
