module Norm where

  -- https://continuation.passing.style/blog/Strong_Normalization_of_STLC.html

  open import Data.Product using (_×_; ∃-syntax; Σ-syntax; proj₁; proj₂)
    renaming (_,_ to _×,_)
  open import Data.Product.Properties using ()
    renaming (×-≡,≡→≡ to pair-eq)
  open import Data.Empty using () renaming (⊥ to Empty)
  open import Data.Unit using (tt) renaming (⊤ to Unit)
  open import Data.Nat using (suc; zero) renaming (ℕ to Nat)
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; sym; cong; trans)
  open import Relation.Binary.PropositionalEquality.Properties using ()
  open Relation.Binary.PropositionalEquality.Properties.≡-Reasoning
  open import Relation.Nullary.Decidable using (Dec; yes; no)

  open import Base
  open import Trans {Typ} hiding (_~>_)
  open import Props using
    (⊸-wkn'; _~>_; ~>-refl; ~>-wkn'; ~>-↑; ⟨_⟩; _∙ss_;
     subst; subst-id; ~>-refl-∙ss-id; ∙ss-decomp;
     ∙srs-assoc; ~>-ext-⟨⟩; ↑-∙ss; ∙sss-assoc)

  private variable
    A B : Typ
    Γ Δ : Context
    t t' u u' v v' : A ⊣ Γ
    n : Nat

  data Val : A ⊣ Γ → Set where
    true : Val {Γ = Γ} ⊤
    false : Val {Γ = Γ} ⊥
    --nat : Val {Γ = Γ} (nat n)
    nat-z : Val {Γ = Γ} n0
    nat-s : Val t → Val (n' t)
    abs : Val (abs t)

  data _↦c_ : A ⊣ Γ → A ⊣ Γ → Set where
    -- Val u wird benoetigt, um die Bestimmtheit der
    -- Reduzierungskette zu gewaehrleisten
    β : Val u → app (abs t) u ↦c subst t ⟨ u ⟩
    if-⊤ : (if ⊤ then t else u) ↦c t
    if-⊥ : (if ⊥ then t else u) ↦c u
    ℕ-β  : rec n0 u v ↦c u
    ℕ-β' : rec {Γ = Γ} (n' t) u v ↦c subst v ((~>-refl ×, t) ×, rec t u v)
    --ℕ-β' : rec {Γ = Γ} (nat (suc n)) u v ↦c subst v (⟨ rec (nat n) u v ⟩ ∙ss ⟨ nat n ⟩)

  data _↦_ : A ⊣ Γ → A ⊣ Γ → Set where
    here : t ↦c t' → t ↦ t'
    ap : t ↦ t' → app t u ↦ app t' u
    ap' : u ↦ u' → app (abs t) u ↦ app (abs t) u'
    if : t ↦ t' → (if t then u else v) ↦ (if t' then u else v)
    ns : t ↦ t' → n' t ↦ n' t'
    rec : t ↦ t' → rec t u v ↦ rec t' u v


  data _↦*_ : A ⊣ Γ → A ⊣ Γ → Set where
    done : t ↦* t
    step : t ↦ u → u ↦* v → t ↦* v

  det-↦cc : t ↦c u → t ↦c v → u ≡ v
  det-↦cc (β _) (β _) = refl
  det-↦cc if-⊤ if-⊤ = refl
  det-↦cc if-⊥ if-⊥ = refl
  det-↦cc ℕ-β ℕ-β = refl
  det-↦cc ℕ-β' ℕ-β' = refl

  is-val : (t : A ⊣ Γ) → Dec (Val t)
  is-val (var _) = no λ ()
  is-val ⊤ = yes true
  is-val ⊥ = yes false
  is-val (if _ then _ else _) = no λ ()
  is-val n0 = yes nat-z
  is-val (n' t) with is-val t
  ...              | yes tv = {!!}
  ...              | no ntv = {!!}
  is-val (rec _ _ _) = no λ ()
  is-val (abs _) = yes abs
  is-val (app _ _) = no λ ()

  -- next-↦ : (t : A ⊣ Γ) → Dec (∃[ t' ] t ↦ t')
  -- next-↦ (var _) = no λ {(_ ×, here ())}
  -- next-↦ ⊤ = no λ {(_ ×, here ())}
  -- next-↦ ⊥ = no λ {(_ ×, here ())}
  -- next-↦ (if var _ then _ else _)
  --   = no λ {(_ ×, here ()); (_ ×, if (here ()))}
  -- next-↦ (if ⊤ then u else _) = yes (u ×, here if-⊤)
  -- next-↦ (if ⊥ then _ else v) = yes (v ×, here if-⊥)
  -- next-↦ (if if t₁ then t₂ else t₃ then u else v)
  --   with next-↦ (if t₁ then t₂ else t₃)
  -- ...  | yes (t' ×, s) = yes ((if t' then u else v) ×, if s)
  -- ...  | no ns = no λ {(_ ×, here ());
  --                      (_ ×, (if {t' = t'} s)) → ns (t' ×, s)}
  -- next-↦ (if rec t₁ t₂ t₃ then u else v) with next-↦ (rec t₁ t₂ t₃)
  -- ... | yes (t' ×, s) = yes ((if t' then u else v) ×, if s)
  -- ... | no ns = no λ {(_ ×, here ());
  --                     (_ ×, (if {t' = t'} s)) → ns (t' ×, s)}
  -- next-↦ (if app t₁ t₂ then u else v) with next-↦ (app t₁ t₂)
  -- ... | yes (t' ×, s) = yes ((if t' then u else v) ×, if s)
  -- ... | no ns = no λ {(_ ×, here ());
  --                     (_ ×, (if {t' = t'} s)) → ns (t' ×, s)}
  -- next-↦ z = no λ {(_ ×, here ())}
  -- next-↦ (s t) with next-↦ t
  -- ...             | yes (t' ×, s) = yes ((s t') ×, s s)
  -- ...             | no ns = no λ {(_ ×, here());
  --                                 (_ ×, (s s)) → ?}
  -- next-↦ (rec (var _) _ _)
  --   = no λ {(_ ×, here ()); (_ ×, rec (here ()))}
  -- next-↦ (rec (if t₁ then t₂ else t₃) u v)
  --   with next-↦ (if t₁ then t₂ else t₃)
  -- ... | yes (t' ×, s) = yes ((rec t' u v) ×, rec s)
  -- ... | no ns = no λ {(_ ×, here ());
  --                     (_ ×, (rec {t' = t'} s)) → ns (t' ×, s)}
  -- next-↦ (rec (nat zero) u _) = yes (u ×, here ℕ-β)
  -- next-↦ (rec (nat (suc n)) u v)
  --   = yes (subst v ((~>-refl ×, (nat n)) ×, rec (nat n) u v) ×, here ℕ-β')
  -- next-↦ (rec (rec t₁ t₂ t₃) u v) with next-↦ (rec t₁ t₂ t₃)
  -- ... | yes (t' ×, s) = yes ((rec t' u v) ×, rec s)
  -- ... | no ns = no λ {(_ ×, here ());
  --                     (_ ×, (rec {t' = t'} s)) → ns (t' ×, s)}
  -- next-↦ (rec (app t₁ t₂) u v) with next-↦ (app t₁ t₂)
  -- ... | yes (t' ×, s) = yes ((rec t' u v) ×, rec s)
  -- ... | no ns = no λ {(_ ×, here ());
  --                     (_ ×, (rec {t' = t'} s)) → ns (t' ×, s)}
  -- next-↦ (abs t) = no λ {(_ ×, here ())}
  -- next-↦ (app (var e) u) = no λ {(_ ×, here ()); (_ ×, ap (here ()))}
  -- next-↦ (app (if t₁ then t₂ else t₃) u)
  --   with next-↦ (if t₁ then t₂ else t₃)
  -- ... | yes (t' ×, s) = yes ((app t' u) ×, ap s)
  -- ... | no ns = no λ {(_ ×, here ());
  --                     (_ ×, (ap {t' = t'} s)) → ns (t' ×, s)}
  -- next-↦ (app (rec t₁ t₂ t₃) u) with next-↦ (rec t₁ t₂ t₃)
  -- ... | yes (t' ×, s) = yes ((app t' u) ×, ap s)
  -- ... | no ns = no λ {(_ ×, here ());
  --                     (_ ×, (ap {t' = t'} s)) → ns (t' ×, s)}
  -- next-↦ (app (abs t) u) with next-↦ u
  -- ... | yes (u' ×, s) = yes ((app (abs t) u') ×, ap' s)
  -- ... | no ns with is-val u
  -- ...            | yes V = yes (subst t ⟨ u ⟩ ×, here (β V))
  -- ...            | no nv = no λ {(_ ×, here (β v)) → nv v;
  --                                (_ ×, ap (here ()));
  --                                (_ ×, (ap' {u' = u'} s))
  --                                  → ns (u' ×, s)}
  -- next-↦ (app (app t₁ t₂) u) with next-↦ (app t₁ t₂)
  -- ... | yes (t' ×, s) = yes ((app t' u) ×, ap s)
  -- ... | no ns = no λ {(_ ×, here ());
  --                     (_ ×, (ap {t' = t'} s)) → ns (t' ×, s)}

  det-↦c : t ↦ u → t ↦c v → u ≡ v
  det-↦c (here c) c' = det-↦cc c c'
  det-↦c (ap (here ())) (β _)
  det-↦c (ap' (here ())) (β true)
  det-↦c (ap' (here ())) (β false)
  det-↦c (ap' (here c)) (β nat-z) = {!!}
  det-↦c (ap' (here c)) (β (nat-s _)) = {!!}
  det-↦c (ap' (here ())) (β abs)
  det-↦c (if (here ())) if-⊤
  det-↦c (if (here ())) if-⊥
  det-↦c (rec (here ())) ℕ-β

  det-↦ : t ↦ u → t ↦ v → u ≡ v
  det-↦ (here c) s' = sym (det-↦c s' c)
  det-↦ s (here c) = det-↦c s c
  det-↦ (ap s) (ap s') = cong (λ t → app t _) (det-↦ s s')
  det-↦ (ap (here ())) (ap' s')
  det-↦ (ap' s) (ap (here ()))
  det-↦ (ap' s) (ap' s') = cong (app _) (det-↦ s s')
  det-↦ (if s) (if s') = cong (λ t → if t then _ else _) (det-↦ s s')
  det-↦ (rec s) (rec s') = cong (λ t → rec t _ _) (det-↦ s s')

  backstep : t ↦ t' → Val u → t ↦* u → t' ↦* u
  backstep (here ()) true done
  backstep (here ()) false done
  backstep (here c) nat done = {!!}
  backstep (here ()) abs done
  backstep (ap s) () done
  backstep (ap' s) () done
  backstep (if s) () done
  backstep (rec s) () done
  backstep s _ (step s' j) with det-↦ s s'
  ...                         | refl = j

  _⇓_ : A ⊣ Γ → A ⊣ Γ → Set
  _⇓_ t v = Val v × t ↦* v

  _⇓ : A ⊣ Γ → Set
  _⇓ t = ∃[ v ] t ⇓ v

  _++_ : t ↦* u → u ↦* v → t ↦* v
  done ++ j' = j'
  step s j ++ j' = step s (j ++ j')

  lifts : {E : A ⊣ Γ → B ⊣ Γ} → (∀ {u u'} → u ↦ u' → E u ↦ E u')
        → t ↦* t' → E t ↦* E t'
  lifts s done = done
  lifts s (step s' j) = step (s s') (lifts s j)

  SN' SN : A ⊣ ε → Set

  SN' {𝟚} _ = Unit
  SN' {ℕ} _ = Unit
  SN' {A ⇒ B} t = ∀ u → SN u → SN (app t u)

  SN t = SN' t × t ⇓

  SNs : Γ ~> ε → Set
  SNs {ε} _ = Unit
  SNs {_ , _} (σ ×, t) = SNs σ × SN t

  sn-pres : t ↦ t' → SN t → SN t'
  sn'-pres : t ↦ t' → SN' t → SN' t'
  sn-pres* : t ↦* t' → SN t → SN t'
  sn-pres' : t ↦ t' → SN t' → SN t
  sn'-pres' : t ↦ t' → SN' t' → SN' t
  sn-pres'* : t ↦* t' → SN t' → SN t

  sn-pres s (sn' ×, (v ×, vv ×, j)) = sn'-pres s sn' ×, v ×, vv ×, backstep s vv j
  
  sn'-pres {𝟚} s sn' = tt
  sn'-pres {ℕ} s sn' = tt
  sn'-pres {A ⇒ B} s sn' u snu = sn-pres (ap s) (sn' u snu)

  sn-pres* done sn = sn
  sn-pres* (step s j) sn = sn-pres* j (sn-pres s sn)

  sn-pres' s (sn' ×, (v ×, vv ×, j)) = sn'-pres' s sn' ×, v ×, vv ×, step s j

  sn'-pres' {𝟚} s sn = tt
  sn'-pres' {ℕ} s sn = tt
  sn'-pres' {A ⇒ B} s sn u snu = sn-pres' (ap s) (sn u snu)

  sn-pres'* done sn = sn
  sn-pres'* (step s j) sn = sn-pres' s (sn-pres'* j sn)

  sn→⇓ : {t : A ⊣ ε} → SN t → t ⇓
  sn→⇓ (_ ×, n) = n

  coe : ∀ {l} {A B : Set l} → A ≡ B → A → B
  coe refl a = a

  transp : ∀ {l l'} {A : Set l} {B : A → Set l'} {a b : A}
         → a ≡ b → B a → B b
  transp refl x = x

  -- Theorem 3
  fund-thm : {σ : Γ ~> ε} → (t : A ⊣ Γ) → SNs σ → SN (subst t σ)

  if-sn' : {u v : A ⊣ ε} → t ⇓ → SN' u → SN' v
         → SN' (if t then u else v)
  if-sn' {A = 𝟚} _ _ _ = tt
  if-sn' {A = ℕ} _ _ _ = tt
  if-sn' {A = A ⇒ B} (⊤ ×, _ ×, j) sn'u _ u' snu'
    = sn-pres'* ((lifts (λ t → ap (if t)) j) ++ step (ap (here if-⊤)) done)
                (sn'u u' snu')
  if-sn' {A = A ⇒ B} (⊥ ×, _ ×, j) _ sn'v u' snu'
    = sn-pres'* ((lifts (λ t → ap (if t)) j) ++ step (ap (here if-⊥)) done)
                (sn'v u' snu')

  if-sn : SN t → SN u → SN v → SN (if t then u else v)
  if-sn (_ ×, ⊤ ×, _ ×, j) (sn'u ×, uv ×, uvv ×, ju) (sn'v ×, _)
    = if-sn' (⊤ ×, true ×, j) sn'u sn'v ×,
      uv ×, uvv ×, (lifts if j ++ step (here if-⊤) done) ++ ju
  if-sn (_ ×, ⊥ ×, _ ×, j) (sn'u ×, _) (sn'v ×, vv ×, vvv ×, jv)
    = if-sn' (⊥ ×, false ×, j) sn'u sn'v ×,
      vv ×, vvv ×, ((lifts if j ++ step (here if-⊥) done) ++ jv)

  app-sn : SN t → SN u → SN (app t u)

  lemma : {σ : Γ ~> ε} {u : A ⊣ ε}
        → subst v ((σ ×, t) ×, rec t u (subst v (~>-↑ (~>-↑ σ))))
           ≡ subst (subst v (~>-↑ (~>-↑ σ)))
                 ((~>-refl ×, t) ×, rec t u (subst v (~>-↑ (~>-↑ σ))))
  lemma {v = v} {t = t} {σ = σ} {u} =
    subst v ((σ ×, t) ×, rec t u (subst v (~>-↑ (~>-↑ σ))))
      ≡⟨ cong (subst v) ~>-ext-⟨⟩ ⟩
    subst v (⟨ rec t u (subst v (~>-↑ (~>-↑ σ))) ⟩ ∙ss ~>-↑ (σ ×, t))
      ≡⟨ cong (λ t' → subst v (⟨ rec t u (subst v (~>-↑ (~>-↑ σ))) ⟩ ∙ss ~>-↑ t')) ~>-ext-⟨⟩ ⟩
    subst v (⟨ rec t u (subst v (~>-↑ (~>-↑ σ))) ⟩ ∙ss ~>-↑ (⟨ t ⟩ ∙ss ~>-↑ σ))
      ≡⟨ cong (λ t' → subst v (⟨ rec t u (subst v (~>-↑ (~>-↑ σ))) ⟩ ∙ss t'))
              (↑-∙ss {σ = ~>-↑ σ}) ⟩
    subst v (⟨ _ ⟩ ∙ss (~>-↑ ⟨ t ⟩ ∙ss ~>-↑ (~>-↑ σ)))
      ≡⟨ cong (λ t → subst v (⟨ _ ⟩ ∙ss t)) (sym ↑-∙ss) ⟩
    subst v (⟨ _ ⟩ ∙ss ~>-↑ (⟨ t ⟩ ∙ss ~>-↑ σ))
      ≡⟨ {!!} ⟩
    --  ≡⟨ cong (subst v) (∙sss-assoc {σ = ~>-↑ (~>-↑ σ)}) ⟩
    --subst v ((⟨ _ ⟩ ∙ss ~>-↑ ⟨ t ⟩) ∙ss ~>-↑ (~>-↑ σ))
    --  ≡⟨ {!!} ⟩
    subst v (((~>-refl ×, t) ×, _) ∙ss (~>-↑ (~>-↑ σ)))
      ≡⟨ ∙ss-decomp {t = v} ⟩
    subst (subst v (~>-↑ (~>-↑ σ))) ((~>-refl ×, t) ×, _) ∎

  rec-sn'-zero : {σ : Γ ~> ε} {u : A ⊣ ε}
               → SN u
               → SN' (rec n0 u (subst v (~>-↑ (~>-↑ σ))))
  rec-sn'-zero {A = 𝟚} _ = tt
  rec-sn'-zero {A = ℕ} _ = tt
  rec-sn'-zero {A = A ⇒ B} snu u' snu' =
    sn-pres'* (lifts ap (step (here ℕ-β) done))
              (app-sn snu snu')

  rec-sn'-suc : {σ : Γ ~> ε} {u : A ⊣ ε}
              → SNs σ → SN t → SN u
              → SN (rec t u (subst v (~>-↑ (~>-↑ σ))))
              → SN' (rec (n' t) u (subst v (~>-↑ (~>-↑ σ))))
  rec-sn'-suc {A = 𝟚} _ _ _ _ = tt
  rec-sn'-suc {A = ℕ} _ _ _ _ = tt
  rec-sn'-suc {A = A ⇒ B} {t = t} {v = v} {σ = σ} {u}
    sns snt snu snp u' snu' =
    sn-pres'* (lifts ap (step (here ℕ-β') done))
              (app-sn
                (transp {B = SN} (lemma {v = v})
                  (fund-thm v ((sns ×, snt) ×, snp)))
                snu')

  rec-sn-rec : {σ : Γ ~> ε} {u : A ⊣ ε}
             → SNs σ → SN t → SN u
             → SN (rec t u (subst v (~>-↑ (~>-↑ σ))))
  rec-sn-rec {t = n0} {v = v} _ _ snu@(_ ×, uv ×, uvv ×, j) =
    rec-sn'-zero {v = v} snu ×,
    uv ×,
    uvv ×,
    (step (here ℕ-β) done ++ j)
  rec-sn-rec {t = n' t} {v = v} sns snt snu@(sn'u ×, uv ×, uvv ×, j) =
    rec-sn'-suc {v = v} sns {!!} snu snp ×,
    proj₁ (sn→⇓ nf) ×,
    proj₁ (proj₂ (sn→⇓ nf)) ×,
    (step (here ℕ-β') done ++
      (transp {B = λ t → t ↦* proj₁ (sn→⇓ nf)} (lemma {v = v})
        {!!}))
    where
    snp = rec-sn-rec {t = t} {v = v} sns {!!} snu
    nf = fund-thm v ((sns ×, snt) ×, snp)

  rec-sn'-⇒ : {σ : Γ ~> ε} {t : ℕ ⊣ ε} {u : (A ⇒ B) ⊣ ε}
            → SNs σ → SN t → SN u
            → SN' (rec t u (subst v (~>-↑ (~>-↑ σ))))
  rec-sn' : {σ : Γ ~> ε} {t : ℕ ⊣ ε} {u : A ⊣ ε}
          → SNs σ → SN t → SN u
          → SN' (rec t u (subst v (~>-↑ (~>-↑ σ))))
  rec-sn' {A = 𝟚} sns snt snu = tt
  rec-sn' {A = ℕ} sns snt snu = tt
  rec-sn' {A = A ⇒ B} {v = v} sns snt snu =
    rec-sn'-⇒ {v = v} sns snt snu

  rec-sn'-⇒ {t = n0}
    sns (_ ×, _ ×, _ ×, done) snu@(sn'u ×, _) u' snu' =
    sn-pres' (ap (here ℕ-β)) (sn'u u' snu')
  rec-sn'-⇒ {v = v} {t = n' t'} sns snt@(_ ×, _ ×, (nat-s t'v) ×, done) snu u' snu' =
    sn-pres' (ap (here ℕ-β'))
             (transp {B = λ t → SN (app t u')} (lemma {v = v})
               (app-sn (fund-thm v ((sns ×, tt ×, t' ×, t'v ×, done) ×,
                                    rec-sn-rec {v = v} sns (tt ×, t' ×, t'v ×, done) snu))
                 snu')) where
    snp = (fund-thm v ((sns ×, tt ×, t' ×, t'v ×, done) ×,
                       (rec-sn-rec {v = v} sns snt snu)))
  rec-sn'-⇒ {v = v} sns (_ ×, tv ×, tvv ×, step s j) snu u' snu' =
    sn-pres' (ap (rec s))
      (rec-sn'-⇒ {v = v} sns (_ ×, tv ×, tvv ×, j) snu u' snu')

  rec-sn : {σ : Γ ~> ε} {t : ℕ ⊣ ε} {u : A ⊣ ε}
         → SNs σ → SN t → SN u
         → SN (rec t u (subst v (~>-↑ (~>-↑ σ))))
  rec-sn {v = v} sns snt@(sn't ×, t ×, tv ×, j) snu =
    rec-sn' {v = v} sns snt snu ×,
    proj₁ (sn→⇓ next) ×,
    proj₁ (proj₂ (sn→⇓ next)) ×,
    lifts rec j ++ (proj₂ (proj₂ (sn→⇓ next))) where
    next = rec-sn-rec {t = t} {v = v} sns (tt ×, t ×, tv ×, done) snu

  abs-sn' : {σ : Γ ~> ε} {t : B ⊣ (A , Γ)}
          → SNs σ → SN' (abs (subst t (~>-↑ σ)))
  abs-sn' {A = A} {σ = σ} {t} sns u snu@(_ ×, uv ×, uuv ×, j) =
    sn-pres'*
      (lifts ap' j)
      (sn-pres'
        (here (β uuv))
        (transp {B = SN}
          helper
          (fund-thm t (sns ×, sn-pres* j snu)))) where
    helper =
      subst t (σ ×, uv)               ≡⟨ cong (subst t) ~>-ext-⟨⟩ ⟩
      subst t (⟨ uv ⟩ ∙ss ~>-↑ σ)     ≡⟨ ∙ss-decomp {t = t} ⟩
      subst (subst t (~>-↑ σ)) ⟨ uv ⟩ ∎

  abs-sn : {σ : Γ ~> ε} {t : B ⊣ (A , Γ)}
         → SNs σ → SN (abs (subst t (~>-↑ σ)))
  abs-sn {σ = σ} {t} sns =
    abs-sn' {t = t} sns ×, abs (subst t (~>-↑ σ)) ×, abs ×, done

  app-sn (sn't ×, _) snu = sn't _ snu

  fund-thm (var e0) (_ ×, sn) = sn
  fund-thm (var (eS e)) (σs ×, _) = fund-thm (var e) σs
  fund-thm ⊤ _ = tt ×, ⊤ ×, true ×, done
  fund-thm ⊥ _ = tt ×, ⊥ ×, false ×, done
  fund-thm (if t then u else v) sn =
    if-sn (fund-thm t sn) (fund-thm u sn) (fund-thm v sn)
  --fund-thm (nat n) _ = tt ×, nat n ×, nat ×, done
  fund-thm n0 _ = tt ×, n0 ×, nat-z ×, done
  fund-thm (n' t) sn with fund-thm t sn
  ... | _ ×, tv ×, tvv ×, j = tt ×, n' tv ×, nat-s tvv ×, lifts ns j
  fund-thm (rec t u v) sn =
    rec-sn {v = v} sn (fund-thm t sn) (fund-thm u sn)
  fund-thm (abs t) sn = abs-sn {t = t} sn
  fund-thm (app t u) sn = app-sn (fund-thm t sn) (fund-thm u sn)

  eval : {t : A ⊣ ε} → t ⇓
  eval {t = t} = sn→⇓ (coe (cong SN subst-id) (fund-thm t tt))
