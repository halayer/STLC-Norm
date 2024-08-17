module Norm where

  -- https://continuation.passing.style/blog/Strong_Normalization_of_STLC.html

  open import Data.Product using (_×_; ∃-syntax; Σ-syntax)
    renaming (_,_ to _×,_)
  open import Data.Empty using () renaming (⊥ to Empty)
  open import Data.Unit using () renaming (⊤ to Unit)
  open import Data.Nat using (suc; zero) renaming (ℕ to Nat)
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; sym; cong)
  open import Relation.Nullary.Decidable using (Dec; yes; no)

  open import Base hiding (unlam)
  open Sub {_⊣_} using (_~>_; _,*_)
  open Properties {_⊣_} {var} {rename} using (id*; ⟨_⟩; ~>↑; wkn*; wkn*'; ⊸-lift-prop)

  private variable
    A B : Typ
    Γ Δ : Context
    t t' u u' v v' : A ⊣ Γ
    n : Nat

  data Val : A ⊣ Γ → Set where
    true : Val {Γ = Γ} ⊤
    false : Val {Γ = Γ} ⊥
    nat : Val {Γ = Γ} (nat n)
    abs : Val (abs t)

  data _↦c_ : A ⊣ Γ → A ⊣ Γ → Set where
    -- Val u wird benoetigt, um die Bestimmtheit der
    -- Reduzierungskette zu gewaehrleisten
    β : Val u → app (abs t) u ↦c subst t ⟨ u ⟩
    if-⊤ : (if ⊤ then t else u) ↦c t
    if-⊥ : (if ⊥ then t else u) ↦c u
    ℕ-β  : rec (nat zero) u v ↦c u
    ℕ-β' : rec {Γ = Γ} (nat (suc n)) u v ↦c subst v ((id* ,* (nat n)) ,* rec (nat n) u v)

  det-↦cc : t ↦c u → t ↦c v → u ≡ v
  det-↦cc (β _) (β _) = refl
  det-↦cc if-⊤ if-⊤ = refl
  det-↦cc if-⊥ if-⊥ = refl
  det-↦cc ℕ-β ℕ-β = refl
  det-↦cc ℕ-β' ℕ-β' = refl

  data _↦_ : A ⊣ Γ → A ⊣ Γ → Set where
    here : t ↦c t' → t ↦ t'
    ap : t ↦ t' → app t u ↦ app t' u
    ap' : u ↦ u' → app (abs t) u ↦ app (abs t) u'
    if : t ↦ t' → (if t then u else v) ↦ (if t' then u else v)
    rec : t ↦ t' → rec t u v ↦ rec t' u v

  is-val : (t : A ⊣ Γ) → Dec (Val t)
  is-val (var _) = no λ ()
  is-val ⊤ = yes true
  is-val ⊥ = yes false
  is-val (if _ then _ else _) = no λ ()
  is-val (nat _) = yes nat
  is-val (rec _ _ _) = no λ ()
  is-val (abs _) = yes abs
  is-val (app _ _) = no λ ()

  next-↦ : (t : A ⊣ Γ) → Dec (∃[ t' ] t ↦ t')
  next-↦ (var _) = no λ {(_ ×, here ())}
  next-↦ ⊤ = no λ {(_ ×, here ())}
  next-↦ ⊥ = no λ {(_ ×, here ())}
  next-↦ (if var _ then _ else _)
    = no λ {(_ ×, here ()); (_ ×, if (here ()))}
  next-↦ (if ⊤ then u else _) = yes (u ×, here if-⊤)
  next-↦ (if ⊥ then _ else v) = yes (v ×, here if-⊥)
  next-↦ (if if t₁ then t₂ else t₃ then u else v)
    with next-↦ (if t₁ then t₂ else t₃)
  ...  | yes (t' ×, s) = yes ((if t' then u else v) ×, if s)
  ...  | no ns = no λ {(_ ×, here ());
                       (_ ×, (if {t' = t'} s)) → ns (t' ×, s)}
  next-↦ (if rec t₁ t₂ t₃ then u else v) with next-↦ (rec t₁ t₂ t₃)
  ... | yes (t' ×, s) = yes ((if t' then u else v) ×, if s)
  ... | no ns = no λ {(_ ×, here ());
                      (_ ×, (if {t' = t'} s)) → ns (t' ×, s)}
  next-↦ (if app t₁ t₂ then u else v) with next-↦ (app t₁ t₂)
  ... | yes (t' ×, s) = yes ((if t' then u else v) ×, if s)
  ... | no ns = no λ {(_ ×, here ());
                      (_ ×, (if {t' = t'} s)) → ns (t' ×, s)}
  next-↦ (nat _) = no λ {(_ ×, here ())}
  next-↦ (rec (var _) _ _)
    = no λ {(_ ×, here ()); (_ ×, rec (here ()))}
  next-↦ (rec (if t₁ then t₂ else t₃) u v)
    with next-↦ (if t₁ then t₂ else t₃)
  ... | yes (t' ×, s) = yes ((rec t' u v) ×, rec s)
  ... | no ns = no λ {(_ ×, here ());
                      (_ ×, (rec {t' = t'} s)) → ns (t' ×, s)}
  next-↦ (rec (nat zero) u _) = yes (u ×, here ℕ-β)
  next-↦ (rec (nat (suc n)) u v)
    = yes (subst v ((id* ,* (nat n)) ,* rec (nat n) u v) ×, here ℕ-β')
  next-↦ (rec (rec t₁ t₂ t₃) u v) with next-↦ (rec t₁ t₂ t₃)
  ... | yes (t' ×, s) = yes ((rec t' u v) ×, rec s)
  ... | no ns = no λ {(_ ×, here ());
                      (_ ×, (rec {t' = t'} s)) → ns (t' ×, s)}
  next-↦ (rec (app t₁ t₂) u v) with next-↦ (app t₁ t₂)
  ... | yes (t' ×, s) = yes ((rec t' u v) ×, rec s)
  ... | no ns = no λ {(_ ×, here ());
                      (_ ×, (rec {t' = t'} s)) → ns (t' ×, s)}
  next-↦ (abs t) = no λ {(_ ×, here ())}
  next-↦ (app (var e) u) = no λ {(_ ×, here ()); (_ ×, ap (here ()))}
  next-↦ (app (if t₁ then t₂ else t₃) u)
    with next-↦ (if t₁ then t₂ else t₃)
  ... | yes (t' ×, s) = yes ((app t' u) ×, ap s)
  ... | no ns = no λ {(_ ×, here ());
                      (_ ×, (ap {t' = t'} s)) → ns (t' ×, s)}
  next-↦ (app (rec t₁ t₂ t₃) u) with next-↦ (rec t₁ t₂ t₃)
  ... | yes (t' ×, s) = yes ((app t' u) ×, ap s)
  ... | no ns = no λ {(_ ×, here ());
                      (_ ×, (ap {t' = t'} s)) → ns (t' ×, s)}
  next-↦ (app (abs t) u) with next-↦ u
  ... | yes (u' ×, s) = yes ((app (abs t) u') ×, ap' s)
  ... | no ns with is-val u
  ...            | yes V = yes (subst t ⟨ u ⟩ ×, here (β V))
  ...            | no nv = no λ {(_ ×, here (β v)) → nv v;
                                 (_ ×, ap (here ()));
                                 (_ ×, (ap' {u' = u'} s))
                                   → ns (u' ×, s)}
  next-↦ (app (app t₁ t₂) u) with next-↦ (app t₁ t₂)
  ... | yes (t' ×, s) = yes ((app t' u) ×, ap s)
  ... | no ns = no λ {(_ ×, here ());
                      (_ ×, (ap {t' = t'} s)) → ns (t' ×, s)}

  det-↦c : t ↦ u → t ↦c v → u ≡ v
  det-↦c (here c) c' = det-↦cc c c'
  det-↦c (ap (here ())) (β _)
  det-↦c (ap' (here ())) (β true)
  det-↦c (ap' (here ())) (β false)
  det-↦c (ap' (here ())) (β nat)
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

  data _↦*_ : A ⊣ Γ → A ⊣ Γ → Set where
    done : t ↦* t
    step : t ↦ u → u ↦* v → t ↦* v

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

  data SN : A ⊣ Γ → Set where
    sn : (∀ {t'} → t ↦ t' → SN t') → SN t

  sn-pres : t ↦ t' → SN t → SN t'
  sn-pres' : {t : A ⊣ Γ} → t ↦ t' → SN t' → SN t

  sn-pres s (sn n) = n s

  sn-pres' {t = t} s sn- = sn (λ {u} s' → theo s') where
    theo : t ↦ u → SN u
    theo s' with det-↦ s s'
    ...        | refl = sn-

  sn→⇓ : {t : A ⊣ ε} → SN t → t ⇓
  sn→⇓ {t = ⊤} _ = ⊤ ×, true ×, done
  sn→⇓ {t = ⊥} _ = ⊥ ×, false ×, done
  sn→⇓ {t = if t then u else v} (sn n) = sn→⇓ {!!}
  sn→⇓ {t = if ⊤ then u else v} (sn n) with sn→⇓ (n (here if-⊤))
  ... | u' ×, v ×, j = u' ×, v ×, step (here if-⊤) j
  sn→⇓ {t = if ⊥ then u else v} (sn n) with sn→⇓ (n (here if-⊥))
  ... | v' ×, v ×, j = v' ×, v ×, step (here if-⊥) j
  sn→⇓ {t = if if t₁ then t₂ else t₃ then u else v} (sn n) = {!!}
  sn→⇓ {t = if rec t t₁ t₂ then u else v} (sn n) = {!!}
  sn→⇓ {t = if app t t₁ then u else v} (sn n) = {!!}
  sn→⇓ {t = nat n} _ = nat n ×, nat ×, done
  sn→⇓ {t = rec t u v} (sn n) = {!!}
  sn→⇓ {t = abs t} _ = abs t ×, abs ×, done
  sn→⇓ {t = app t u} (sn n) = {!!}
  
  is-norm : A ⊣ Γ → Set
  is-norm t = ∀ {t'} → t ↦ t' → Empty

  var-sn : ∀ {e} → SN {A} {Γ} (var e)
  var-sn = sn λ {(here ())}
  var-is-norm : ∀ {e} → is-norm {A} {Γ} (var e)
  var-is-norm (here ())

  abs-sn : {t : B ⊣ (A , Γ)} → SN (abs t)
  abs-sn = sn λ {(here ())}
  abs-is-norm : {t : B ⊣ (A , Γ)} → is-norm (abs t)
  abs-is-norm (here ())

  ⊤-sn : SN {Γ = Γ} ⊤
  ⊤-sn = sn λ {(here ())}
  ⊤-is-norm : is-norm {Γ = Γ} ⊤
  ⊤-is-norm (here ())

  ⊥-sn : SN {Γ = Γ} ⊥
  ⊥-sn = sn λ {(here ())}
  ⊥-is-norm : is-norm {Γ = Γ} ⊥
  ⊥-is-norm (here ())

  nat-sn : SN {Γ = Γ} (nat n)
  nat-sn = sn λ {(here ())}
  nat-is-norm : is-norm {Γ = Γ} (nat n)
  nat-is-norm (here ())

  -- Theorem 1/2
  -- strong-normalization : (t : A ⊣ Γ) → SN t
  -- strong-normalization (var e) = var-sn
  -- strong-normalization ⊤ = ⊤-sn
  -- strong-normalization ⊥ = ⊥-sn
  -- strong-normalization (if t then u else v) = {!!}
  -- strong-normalization zero = zero-sn
  -- strong-normalization (succ t) = succ-sn (strong-normalization t)
  -- strong-normalization (rec t u v) = {!!}
  -- strong-normalization (abs t) = abs-sn
  -- strong-normalization (app t u) = {!!} -- Problem

  SNs : Γ ~> Δ → Set
  SNs {Γ} σ = ∀ {A} (e : A ∈ Γ) → SN (Sub.sub σ e)

  coe : ∀ {l} {A B : Set l} → A ≡ B → A → B
  coe refl a = a

  -- Theorem 3
  fund-thm : {σ : Γ ~> Δ} → (t : A ⊣ Γ) → SNs σ → SN (subst t σ)

  app-sn : SN t → SN u → SN (app t u)
  app-sn (sn n) (sn n')
    = sn λ {(ap s) → app-sn (n s) (sn n');
            (ap' s) → _;
            (here (β {t = t} true))
              → fund-thm t λ {
                  e0 → ⊤-sn;
                  (eS e) → coe (sym (cong SN (⊸-lift-prop {e = e}))) var-sn
                };
            (here (β {t = t} false))
              → fund-thm t λ {
                  e0 → ⊥-sn;
                  (eS e) → coe (sym (cong SN (⊸-lift-prop {e = e}))) var-sn
                };
            (here (β {t = t} nat))
              → fund-thm t λ {
                  e0 → nat-sn;
                  (eS e) → coe (sym (cong SN (⊸-lift-prop {e = e}))) var-sn
                };
            (here (β {t = t} abs))
              → fund-thm t λ {
                  e0 → abs-sn;
                  (eS e) → coe (sym (cong SN (⊸-lift-prop {e = e}))) var-sn
                }
      }

  fund-thm (var e) sn- = sn- e
  fund-thm ⊤ _ = ⊤-sn
  fund-thm ⊥ _ = ⊥-sn
  fund-thm (if t then u else v) sn- = {!!}
  fund-thm (nat n) _ = nat-sn
  fund-thm (rec t u v) sn- = {!!}
  fund-thm (abs _) _ = abs-sn
  fund-thm (app t u) sn- = app-sn (fund-thm t sn-) (fund-thm u sn-)

  --WN WN' : A ⊣ ε → Set
  --WN' {𝟚} t = Unit
  --WN' {ℕ} t = Unit
  --WN' {A ⇒ B} t = ∀ u → WN u → WN (app t u)

  --WN t = t ⇓ × WN' t

  -- Lemma (SN Preserved)
  --wn-pres : t ↦ t' → WN t' → WN t
  --wn'-pres : {t : A ⊣ ε} → t ↦ t' → WN' t' → WN' t
  --wn-pres* : t ↦* t' → WN t' → WN t
  --wn-pres' : t ↦ t' → WN t → WN t'
  --wn'-pres' : {t : A ⊣ ε} → t ↦ t' → WN' t → WN' t'
  --wn-pres*' : t ↦* t' → WN t → WN t'
  
  --wn-pres s ((v and vv and j) and w) = (v and vv and step s j) and wn'-pres s w

  --wn'-pres {𝟚} s w = Data.Unit.tt
  --wn'-pres {ℕ} s w = Data.Unit.tt
  --wn'-pres {A ⇒ B} s w u wu = wn-pres (ap s) (w u wu)

  --wn-pres* done w = w
  --wn-pres* (step s j) w = wn-pres s (wn-pres* j w)

  --lemma : t ↦ t' → Val v → t ↦* v → t' ↦* v
  --lemma (here ()) abs done
  --lemma (here ()) true done
  --lemma (here ()) false done
  --lemma (here ()) zero done
  --lemma (here ()) (succ v) done
  --lemma s vv (step s' j) with det-↦ s s'
  --...                       | refl = j

  --wn-pres' {t' = t'} s ((v and vv and j) and w)
  --  = (v and vv and lemma s vv j) and wn'-pres' s w

  --wn'-pres' {𝟚} s w = Data.Unit.tt
  --wn'-pres' {ℕ} s w = Data.Unit.tt
  --wn'-pres' {A ⇒ B} s w u wu = wn-pres' (ap s) (w u wu)

  --wn-pres*' done w = w
  --wn-pres*' (step s j) w = wn-pres*' j (wn-pres' s w)

  -- Lemma (Substitution)
  --WNs : Γ ~> ε → Set
  --WNs {ε} σ = Unit
  --WNs {A , Γ} (σ and t) = WNs σ × WN t
  
  --wn-subst : {σ : Γ ~> ε} → (t : A ⊣ Γ) → WNs σ → WN (subst t σ)
  --wn-subst (var e0) ws = proj₂ ws
  --wn-subst (var (eS e)) ws = wn-subst (var e) (proj₁ ws)
  --wn-subst ⊤ ws = (⊤ and true and done) and Data.Unit.tt
  --wn-subst ⊥ ws = (⊥ and false and done) and Data.Unit.tt
  --wn-subst (if t then u else v) ws with wn-subst t ws
  --... | (⊤ and true and j) and _ = wn-pres* (lifts if j)
  --                                   (wn-pres (here if-⊤) (wn-subst u ws))
  --... | (⊥ and false and j) and _ = wn-pres* (lifts if j)
  --                                   (wn-pres (here if-⊥) (wn-subst v ws))
  --wn-subst zero ws = (zero and zero and done) and Data.Unit.tt
  --wn-subst (succ t) ws with wn-subst t ws
  --... | (zero and zero and j) and _ = (succ zero and succ zero and {!!}) and {!!}
  --... | (succ t' and (succ v) and j) and snd = {!!}
  --wn-subst (rec t t₁ t₂) ws = {!!}
  --wn-subst (abs t) ws = {!!}
  --wn-subst (app t t₁) ws = {!!}

  --data NormType : Set where
  --  nf : NormType
  --  ne : NormType

  --_⇈_ : NormType → NormType → NormType
  --nf ⇈ nf = nf
  --nf ⇈ ne = ne
  --ne ⇈ nf = ne
  --ne ⇈ ne = ne

  --data [_]-_⊣_ : NormType → Typ → Context → Set where
  --  var : A ∈ Γ → [ ne ]- A ⊣ Γ

    -- Booleans
  --  ⊤ : [ nf ]- 𝟚 ⊣ Γ
  --  ⊥ : [ nf ]- 𝟚 ⊣ Γ
  --  if_then_else_ : [ ne ]- 𝟚 ⊣ Γ → [ nf ]- A ⊣ Γ → [ nf ]- A ⊣ Γ
  --                → [ ne ]- A ⊣ Γ
  --  ne-𝟚 : [ ne ]- 𝟚 ⊣ Γ → [ nf ]- 𝟚 ⊣ Γ

    -- Natural Numbers
  --  zero : [ nf ]- ℕ ⊣ Γ
  --  succ : [ nf ]- ℕ ⊣ Γ → [ nf ]- ℕ ⊣ Γ
  --  rec : [ ne ]- ℕ ⊣ Γ → [ nf ]- A ⊣ Γ → [ nf ]- A ⊣ (A , (ℕ , Γ))
  --      → [ ne ]- A ⊣ Γ
  --  ne-ℕ : [ ne ]- ℕ ⊣ Γ → [ nf ]- ℕ ⊣ Γ

    -- Functions
  --  abs : [ nf ]- B ⊣ (A , Γ) → [ nf ]- (A ⇒ B) ⊣ Γ
  --  app : [ ne ]- (A ⇒ B) ⊣ Γ → [ nf ]- A ⊣ Γ → [ ne ]- B ⊣ Γ

  --unnorm : ∀ {n} → [ n ]- A ⊣ Γ → A ⊣ Γ
  --unnorm (var e) = var e
  --unnorm ⊤ = ⊤
  --unnorm ⊥ = ⊥
  --unnorm (if t then u else v) = if unnorm t then unnorm u else unnorm v
  --unnorm (ne-𝟚 t) = unnorm t
  --unnorm zero = zero
  --unnorm (succ t) = succ (unnorm t)
  --unnorm (rec t u v) = rec (unnorm t) (unnorm u) (unnorm v)
  --unnorm (ne-ℕ t) = unnorm t
  --unnorm (abs t) = abs (unnorm t)
  --unnorm (app t u) = app (unnorm t) (unnorm u)

  --norm : A ⊣ Γ → [ nf ]- A ⊣ Γ
  --if-norm : 𝟚 ⊣ Γ → A ⊣ Γ → A ⊣ Γ → [ nf ]- A ⊣ Γ
  --if-norm t u v with norm t
  --... | ⊤ = norm u
  --... | ⊥ = norm v
  --if-norm {A = 𝟚} t u v | ne-𝟚 t' = ne-𝟚 (if t' then norm u else norm v)
  --if-norm {A = ℕ} t u v | ne-𝟚 t' = ne-ℕ (if t' then norm u else norm v)
  --if-norm {A = A ⇒ B} t u v | ne-𝟚 t' = abs (if-norm (rename t Ren.wkn)
  --                                          (app (rename u Ren.wkn) (var e0))
  --                                          (app (rename v Ren.wkn) (var e0)))

  --rec-norm : ℕ ⊣ Γ → A ⊣ Γ → A ⊣ (A , (ℕ , Γ)) → [ nf ]- A ⊣ Γ
  --rec-norm t u v with norm t
  --... | zero = norm u
  -- rec (succ t) u v ↦c subst v ((id* ,* t) ,* rec t u v)
  --... | succ t' = {!!} --norm (subst v ((id* ,* (unnorm t')) ,* rec t u v))
  --rec-norm {A = 𝟚} t u v | ne-ℕ t' = ne-𝟚 (rec t' (norm u) (norm v))
  --rec-norm {A = ℕ} t u v | ne-ℕ t' = ne-ℕ (rec t' (norm u) (norm v))
  --rec-norm {A = A ⇒ B} t u v | ne-ℕ t'
  --  = let s = wkn*' (~>↑ wkn*) ,* abs (var (eS e0)) in
  --    abs (rec-norm (rename t Ren.wkn)
  --         (app (rename u Ren.wkn) (var e0))
  --         (app (subst v s) (var (eS (eS e0)))))

  --norm {𝟚} (var e) = ne-𝟚 (var e)
  --norm {ℕ} (var e) = ne-ℕ (var e)
  --norm {A ⇒ B} (var e) = abs {!!}
  --norm ⊤ = ⊤
  --norm ⊥ = ⊥
  --norm (if t then u else v) = if-norm t u v
  --norm zero = zero
  --norm (succ t) = succ (norm t)
  --norm (rec t u v) = rec-norm t u v
  --norm (abs t) = {!!}
  --norm (app t t₁) = {!!}
