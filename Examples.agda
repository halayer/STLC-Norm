module Examples where

  open import Data.Unit using (tt)
  open import Data.Nat using (suc) renaming (ℕ to Nat)
  open import Data.Product using () renaming (_,_ to _×,_)
  open import Base
  open import Trans
  open import Props
  open import Norm --using (eval; ℕ→Nat)

  and : (𝟚 ⇒ (𝟚 ⇒ 𝟚)) ⊣ ε
  and = abs (abs (if var e0 then var (eS e0) else ⊥))
  or : (𝟚 ⇒ (𝟚 ⇒ 𝟚)) ⊣ ε
  or = abs (abs (if var e0 then var e0 else var (eS e0)))

  succ : (ℕ ⇒ ℕ) ⊣ ε
  succ = abs (rec (var e0) (nat 1) ?) -- Fehler: Es braucht einen Nachfolger-Konstruktor!
