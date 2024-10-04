module Examples where

  open import Base
  open import Trans using (ε; e0; eS)
  open import Norm using (eval)

  private variable
    A B C : Typ
    Γ : Trans.Context

  ↑ : {A : Typ} → A ⊣ ε → A ⊣ Γ
  ↑ t = Props.rename t Data.Unit.tt where
    import Props
    import Data.Unit

  -- Wahrheitswerte
  and : (𝟚 ⇒ (𝟚 ⇒ 𝟚)) ⊣ Γ
  and = ↑ (abs (abs (if var e0 then var (eS e0) else ⊥)))
  or : (𝟚 ⇒ (𝟚 ⇒ 𝟚)) ⊣ Γ
  or = ↑ (abs (abs (if var e0 then var e0 else var (eS e0))))

  -- Natürliche Zahlen
  add : (ℕ ⇒ (ℕ ⇒ ℕ)) ⊣ Γ
  add = ↑ (abs (abs (rec (var (eS e0)) (var e0) (n' (var e0)))))

  mul : (ℕ ⇒ (ℕ ⇒ ℕ)) ⊣ Γ
  mul = ↑ (abs (abs (rec (var (eS e0))
    n0
    (app (app add (var (eS (eS e0)))) (var e0)))))

  -- Potentierung ist seeehr langsam
  exp : (ℕ ⇒ (ℕ ⇒ ℕ)) ⊣ Γ
  exp = ↑ (abs (abs (rec (var e0)
    (n' n0)
    (app (app mul (var (eS (eS (eS e0))))) (var e0)))))

  -- Funktionen
  fcomp : ((B ⇒ C) ⇒ ((A ⇒ B) ⇒ (A ⇒ C))) ⊣ Γ
  fcomp = ↑ (abs (abs (abs (app (var (eS (eS e0))) (app (var (eS e0)) (var e0))))))

  double : (ℕ ⇒ ℕ) ⊣ Γ
  double = ↑ (abs (app (app (app fcomp (app add (var e0))) (app add (var e0))) n0))
