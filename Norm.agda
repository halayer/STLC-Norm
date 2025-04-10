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
    ℕ-β' : Val t → rec {Γ = Γ} (n' t) u v ↦c subst v ((~>-refl ×, t) ×, rec t u v)

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
  det-↦cc (ℕ-β' _) (ℕ-β' _) = refl

  nat-val-cant-be-reduced : {t : ℕ ⊣ Γ}
                          → Val t → t ↦ t' → Empty
  nat-val-cant-be-reduced nat-z (here ())
  nat-val-cant-be-reduced (nat-s v) (ns s) =
    nat-val-cant-be-reduced v s

  det-↦c : t ↦ u → t ↦c v → u ≡ v
  det-↦c (here c) c' = det-↦cc c c'
  det-↦c (ap (here ())) (β _)
  det-↦c (ap' (here ())) (β true)
  det-↦c (ap' (here ())) (β false)
  det-↦c (ap' (here ())) (β nat-z)
  det-↦c (ap' (here ())) (β (nat-s _))
  det-↦c (ap' (here ())) (β abs)
  det-↦c (ap' (ns s)) (β (nat-s v))
    with nat-val-cant-be-reduced v s
  ... | ()
  det-↦c (if (here ())) if-⊤
  det-↦c (if (here ())) if-⊥
  det-↦c (rec (here ())) ℕ-β
  det-↦c (rec (ns s)) (ℕ-β' v)
    with nat-val-cant-be-reduced v s
  ... | ()
  
  det-↦ : t ↦ u → t ↦ v → u ≡ v
  det-↦ (here c) s' = sym (det-↦c s' c)
  det-↦ s (here c) = det-↦c s c
  det-↦ (ap s) (ap s') = cong (λ t → app t _) (det-↦ s s')
  det-↦ (ap (here ())) (ap' s')
  det-↦ (ap' s) (ap (here ()))
  det-↦ (ap' s) (ap' s') = cong (app _) (det-↦ s s')
  det-↦ (if s) (if s') = cong (λ t → if t then _ else _) (det-↦ s s')
  det-↦ (rec s) (rec s') = cong (λ t → rec t _ _) (det-↦ s s')
  det-↦ (ns s) (ns s') = cong n' (det-↦ s s')

  backstep : t ↦ t' → Val u → t ↦* u → t' ↦* u
  backstep (here ()) true done
  backstep (here ()) false done
  backstep (here ()) abs done
  backstep (ap s) () done
  backstep (ap' s) () done
  backstep (if s) () done
  backstep (rec s) () done
  backstep (ns s) (nat-s v) done
    with nat-val-cant-be-reduced v s
  ... | ()
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
    subst v ((σ ×, t) ×, _)
      ≡⟨ cong (subst v) ~>-ext-⟨⟩ ⟩
    subst v (⟨ _ ⟩ ∙ss ~>-↑ (σ ×, t))
      ≡⟨ cong (λ σ → subst v (⟨ rec-part ⟩ ∙ss ~>-↑ σ)) ~>-ext-⟨⟩ ⟩
    subst v (⟨ _ ⟩ ∙ss ~>-↑ (⟨ t ⟩ ∙ss ~>-↑ σ))
      ≡⟨ cong (λ σ → subst v (⟨ rec-part ⟩ ∙ss σ)) (↑-∙ss {σ = ~>-↑ σ}) ⟩
    subst v (⟨ _ ⟩ ∙ss (~>-↑ ⟨ t ⟩ ∙ss ~>-↑ (~>-↑ σ)))
      ≡⟨ cong (subst v) (∙sss-assoc {σ = ~>-↑ (~>-↑ σ)}) ⟩
    subst v ((⟨ _ ⟩ ∙ss ~>-↑ ⟨ t ⟩) ∙ss ~>-↑ (~>-↑ σ))
      ≡⟨ ∙ss-decomp {t = v} ⟩
    subst (subst v (~>-↑ (~>-↑ σ))) (⟨ _ ⟩ ∙ss ~>-↑ ⟨ t ⟩)
      ≡⟨ cong (subst (subst v (~>-↑ (~>-↑ σ)))) (sym ~>-ext-⟨⟩) ⟩
    subst (subst v (~>-↑ (~>-↑ σ))) ((~>-refl ×, t) ×, _) ∎ where
    rec-part = rec t u (subst v (~>-↑ (~>-↑ σ)))

  succ-cant-reduce-to-0 : n' t ↦* n0 → Empty
  succ-cant-reduce-to-0 (step (ns _) j) = succ-cant-reduce-to-0 j

  extract-succ-reduction : n' t ↦* n' t' → t ↦* t'
  extract-succ-reduction done = done
  extract-succ-reduction (step (ns s) j) = step s (extract-succ-reduction j)

  snn : SN (n' t) → SN t
  snn (_ ×, n0 ×, nat-z ×, j) with succ-cant-reduce-to-0 j
  ... | ()
  snn (_ ×, n' tv ×, nat-s tvv ×, j) =
    _ ×, tv ×, tvv ×, extract-succ-reduction j

  rec-sn'-zero : {σ : Γ ~> ε} {u : A ⊣ ε}
               → SN u
               → SN' (rec n0 u (subst v (~>-↑ (~>-↑ σ))))
  rec-sn'-zero {A = 𝟚} _ = tt
  rec-sn'-zero {A = ℕ} _ = tt
  rec-sn'-zero {A = A ⇒ B} snu u' snu' =
    sn-pres'* (lifts ap (step (here ℕ-β) done))
              (app-sn snu snu')

  rec-sn'-suc : {σ : Γ ~> ε} {u : A ⊣ ε}
              → SNs σ → SN t → Val t → SN u
              → SN (rec t u (subst v (~>-↑ (~>-↑ σ))))
              → SN' (rec (n' t) u (subst v (~>-↑ (~>-↑ σ))))
  rec-sn'-suc {A = 𝟚} _ _ _ _ _ = tt
  rec-sn'-suc {A = ℕ} _ _ _ _ _ = tt
  rec-sn'-suc {A = A ⇒ B} {t = t} {v = v} {σ = σ} {u}
    sns snt tv snu snp u' snu' =
    sn-pres'* (lifts ap (step (here (ℕ-β' tv)) done))
              (app-sn
                (transp {B = SN} (lemma {v = v})
                  (fund-thm v ((sns ×, snt) ×, snp)))
                snu')

  rec-sn-rec : {σ : Γ ~> ε} {u : A ⊣ ε}
             → SNs σ → SN t → Val t → SN u
             → SN (rec t u (subst v (~>-↑ (~>-↑ σ))))
  rec-sn-rec {v = v} sns _
    nat-z snu@(_ ×, uv ×, uvv ×, j) =
    rec-sn'-zero {v = v} snu ×,
    uv ×,
    uvv ×,
    (step (here ℕ-β) done) ++ j
  rec-sn-rec {t = n' t} {v = v} sns snt
    (nat-s tv) snu =
    rec-sn'-suc {v = v} sns snt' tv snu snp ×,
    proj₁ (sn→⇓ trg) ×,
    proj₁ (proj₂ (sn→⇓ trg)) ×,
    (step (here (ℕ-β' tv)) done) ++
      (transp {B = λ t → t ↦* proj₁ (sn→⇓ trg)} (lemma {v = v})
        (proj₂ (proj₂ (sn→⇓ trg)))) where
    snt' =  snn snt
    snp = rec-sn-rec {v = v} sns snt' tv snu
    trg = fund-thm v ((sns ×, snt') ×, snp)

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
    sn-pres' (ap (here (ℕ-β' t'v)))
             (transp {B = λ t → SN (app t u')} (lemma {v = v})
               (app-sn (fund-thm v ((sns ×, tt ×, t' ×, t'v ×, done) ×,
                                    rec-sn-rec {v = v} sns (tt ×, t' ×, t'v ×, done) t'v snu))
                 snu')) where
    snp = (fund-thm v ((sns ×, tt ×, t' ×, t'v ×, done) ×,
                       (rec-sn-rec {v = v} sns snt (proj₁ (proj₂ (sn→⇓ snt))) snu)))
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
    next = rec-sn-rec {t = t} {v = v} sns (tt ×, t ×, tv ×, done) tv snu

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
  fund-thm n0 _ = tt ×, n0 ×, nat-z ×, done
  fund-thm (n' t) sn with fund-thm t sn
  ... | _ ×, tv ×, tvv ×, j = tt ×, n' tv ×, nat-s tvv ×, lifts ns j
  fund-thm (rec t u v) sn =
    rec-sn {v = v} sn (fund-thm t sn) (fund-thm u sn)
  fund-thm (abs t) sn = abs-sn {t = t} sn
  fund-thm (app t u) sn = app-sn (fund-thm t sn) (fund-thm u sn)

  eval : {t : A ⊣ ε} → t ⇓
  eval {t = t} = sn→⇓ (coe (cong SN subst-id) (fund-thm t tt))
