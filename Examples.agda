module Examples where

  open import Base
  open import Trans
  open import Norm using (eval)

  and : (𝟚 ⇒ (𝟚 ⇒ 𝟚)) ⊣ ε
  and = abs (abs (if var e0 then var (eS e0) else ⊥))
  or : (𝟚 ⇒ (𝟚 ⇒ 𝟚)) ⊣ ε
  or = abs (abs (if var e0 then var e0 else var (eS e0)))
