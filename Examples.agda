module Examples where

  open import Base
  open import Trans using (ε; e0; eS)
  open import Norm using (eval)

  and : (𝟚 ⇒ (𝟚 ⇒ 𝟚)) ⊣ ε
  and = abs (abs (if var e0 then var (eS e0) else ⊥))
  or : (𝟚 ⇒ (𝟚 ⇒ 𝟚)) ⊣ ε
  or = abs (abs (if var e0 then var e0 else var (eS e0)))

  add : (ℕ ⇒ (ℕ ⇒ ℕ)) ⊣ ε
  add = abs (abs (rec (var (eS e0)) (var e0) (n' (var e0))))
