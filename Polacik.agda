module Polacik where

open import preliminaries
open import prop
open import logic
open import Common

{-
  All results pertaining to  Połacik's connective.
-}

-- Theorem 5.12 --
module _
  (t : Prp → Prp)
  (t-def : (P : Prp) → ¬¬ P ⇒ (P ⇒ (t P ∨ ¬ (t P))) ⇒ P holds)
  where

  f : Prp → Prp
  f P = t P ∨ ¬ (t P)

  ff : Prp → Prp
  ff P = f (f P)

  fff : Prp → Prp
  fff P = f (ff P)

  f-ext : {P P' : Prp} → (P ⇒ P') ⇒ (P' ⇒ P) ⇒ f P ⇒ f P' holds
  f-ext {P} {P'} [P⇒P'] [P'⇒P] =
    transport (λ z → f z holds) [P=P'] where
      [P=P'] : P ≡ P'
      [P=P'] = propext {P} {P'} [P⇒P'] [P'⇒P]

  f-negneg : (P : Prp) → ¬¬ (f P) holds
  f-negneg P [¬fP] = [¬fP] (∨-intro-R {t P} {¬ (t P)} (λ [tP] → [¬fP] (∨-intro-L {t P} {¬ (t P)} [tP])))

  -- Lemma 5.8 --
  three-in-one-1 : (P : Prp) → f P ⇒ ff P ⇒ fff P holds
  three-in-one-1 P [fP] [ffP] = f-ext {f P} {ff P} (λ _ → [ffP]) (λ _ → [fP]) [ffP]

  three-in-one-2 : (P : Prp) → (ff P ⇒ fff P) ⇒ ff P holds
  three-in-one-2 P = t-def (ff P) (f-negneg (f P))

  three-in-one-3 : (P : Prp) → f P holds
  three-in-one-3 P = t-def (f P) (f-negneg P) [fP⇒ffP] where
    [fP⇒ffP] : f P ⇒ ff P holds
    [fP⇒ffP] [fP] = three-in-one-2 P (three-in-one-1 P [fP])

  -- Theorem 5.9 --
  dneg-elim3 : (P : Prp) → ¬¬ P ⇒ P holds
  dneg-elim3 P [¬¬P] = t-def P [¬¬P] (λ _ → three-in-one-3 P)


-- Theorem 5.15 --
-- We only formalize the proof of the difficult case (where the connective is
-- defined by the formula X.
module _
  (assumption : ∀ (X Y : Prp) → ((X ⇒ (Y ∨ ¬ Y)) ⇒ X) ⇒ X holds)
  where

  lemma-1 : ∀ (P Q : Prp) → (((P ∨ (P ⇒ (Q ∨ ¬ Q))) ⇒ (Q ∨ ¬ Q)) ⇒ (P ∨ (P ⇒ (Q ∨ ¬ Q)))) ⇒ (P ∨ (P ⇒ (Q ∨ ¬ Q))) holds
  lemma-1 P Q = assumption (P ∨ (P ⇒ (Q ∨ ¬ Q))) Q

  lemma-2 : ∀ (P Q : Prp) → ((P ∨ (P ⇒ (Q ∨ ¬ Q))) ⇒ (Q ∨ ¬ Q)) ⇒ (P ∨ (P ⇒ (Q ∨ ¬ Q))) holds
  lemma-2 P Q [[P∨[P→Q∨¬Q]]→[Q∨¬Q]] =
    ∨-intro-R {P} {P ⇒ (Q ∨ ¬ Q)} (λ [P] → [[P∨[P→Q∨¬Q]]→[Q∨¬Q]] (∨-intro-L {P} {P ⇒ (Q ∨ ¬ Q)} [P]))

  lemma-3 : ∀ (P Q : Prp) → P ∨ (P ⇒ (Q ∨ ¬ Q)) holds
  lemma-3 P Q = lemma-1 P Q (lemma-2 P Q)

  lemma-4 : ∀ (P Q : Prp) → P ∨ (P ⇒ ¬¬ Q ⇒ Q) holds
  lemma-4 P Q =
    ∨-elim {P} {P ⇒ (Q ∨ ¬ Q)} {P ∨ (P ⇒ ¬¬ Q ⇒ Q)} case-1 case-2 (lemma-3 P Q) where
    case-1 : P holds → P ∨ (P ⇒ ¬¬ Q ⇒ Q) holds
    case-1 [P] = ∨-intro-L {P} {P ⇒ ¬¬ Q ⇒ Q} [P]
    case-2 : P ⇒ (Q ∨ ¬ Q) holds → P ∨ (P ⇒ ¬¬ Q ⇒ Q) holds
    case-2 [P⇒[Q∨¬Q]] = ∨-intro-R {P} {P ⇒ ¬¬ Q ⇒ Q}
      (λ [P] [¬¬Q] → ∨-elim {Q} {¬ Q} {Q} (λ [Q] → [Q]) (subcase-2 [¬¬Q]) ([P⇒[Q∨¬Q]] [P])) where
      subcase-2 : ¬¬ Q holds → ¬ Q holds → Q holds
      subcase-2 [¬¬Q] [¬Q] = false-elim {Q} ([¬¬Q] [¬Q])

  the-classical-tautology : ∀ (P : Prp) → (¬¬ P) ∨ (¬¬ P ⇒ P) holds
  the-classical-tautology P =
    ∨-elim {¬¬ P} {¬¬ P ⇒ ¬¬ P ⇒ P} {¬¬ P ∨ (¬¬ P ⇒ P)} case-1 case-2 (lemma-4 (¬¬ P) P) where
    case-1 : ¬¬ P holds → ¬¬ P ∨ (¬¬ P ⇒ P) holds
    case-1 [¬¬P] = ∨-intro-L {¬¬ P} {¬¬ P ⇒ P} [¬¬P]
    case-2 : (¬¬ P ⇒ ¬¬ P ⇒ P) holds → ¬¬ P ∨ (¬¬ P ⇒ P) holds
    case-2 [¬¬P⇒¬¬P⇒P] = ∨-intro-R {¬¬ P} {¬¬ P ⇒ P} (λ [¬¬P] → [¬¬P⇒¬¬P⇒P] [¬¬P] [¬¬P])
