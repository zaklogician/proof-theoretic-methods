-- Copyright (C) 2023 - Zoltan A. Kocsis

module Common where

open import preliminaries
open import prop
open import logic

¬ : Prp → Prp
¬ x = x ⇒ false

¬¬ : Prp → Prp
¬¬ x = ¬ (¬ x)

cong : {P Q : Set} → {x y : P} → (f : P → Q) → x ≡ y → f x ≡ f y
cong f (refl _) = refl _

by-contradiction : (Q : Prp) → {P : Prp} → P ⇒ ¬ P ⇒ Q holds
by-contradiction Q {P} [P] [¬P] = false-elim {Q} ([¬P] [P])
