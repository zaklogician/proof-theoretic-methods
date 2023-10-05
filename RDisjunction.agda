-- Copyright (C) 2023, Zoltan A. Kocsis

module RDisjunction where

{-
  This file contains all results pertaining to the realizabiltiy
  disjunction connective ⅋. 
-}

open import preliminaries
open import prop
open import logic
open import Common


-- Definition 3.1 --
_⅋_ : Prp → Prp → Prp
P ⅋ Q = ∃̇ (λ Y → (¬ Y ⇒ P) ∧ (¬¬ Y ⇒ Q))


-- Theorem 3.10 --
-- ⅋ is the strongest among connectives that are monotone in both variables
-- and satisfy WLEM.
module _
  -- We take another connective ⊕ with these properties.
  (_⊕_ : Prp → Prp → Prp)
  (⊕-wlem : (P : Prp) → (¬ P ⊕ ¬¬ P) holds)
  (⊕-mono-1 : (P Q P' : Prp) → (P ⇒ P') ⇒ (P ⊕ Q) ⇒ (P' ⊕ Q) holds)
  (⊕-mono-2 : (P Q Q' : Prp) → (Q ⇒ Q') ⇒ (P ⊕ Q) ⇒ (P ⊕ Q') holds)
  where
  -- We show that ⅋ already implies ⊕.
  characterization : (P Q : Prp) → (P ⅋ Q) ⇒ (P ⊕ Q) holds
  characterization P Q [P⅋Q] =
    ∃̇-elim {_} {λ Y → (¬ Y ⇒ P) ∧ (¬¬ Y ⇒ Q)} {P ⊕ Q} step [P⅋Q] where
    step : ∀ Y → (¬ Y ⇒ P) ∧ (¬¬ Y ⇒ Q) holds → (P ⊕ Q) holds
    step Y [[¬Y⇒P]∧[¬¬Y⇒Q]] =
      ⊕-mono-2 P (¬¬ Y) Q [¬¬Y⇒Q] (
        ⊕-mono-1 (¬ Y) (¬¬ Y) P [¬Y⇒P] (⊕-wlem Y)
      ) where
      [¬Y⇒P] : ¬ Y ⇒ P holds
      [¬Y⇒P] = ∧-elim-L {¬ Y ⇒ P} {¬¬ Y ⇒ Q} [[¬Y⇒P]∧[¬¬Y⇒Q]]      
      [¬¬Y⇒Q] : ¬¬ Y ⇒ Q holds
      [¬¬Y⇒Q] = ∧-elim-R {¬ Y ⇒ P} {¬¬ Y ⇒ Q} [[¬Y⇒P]∧[¬¬Y⇒Q]]



-- Theorem 3.19 --
-- The main result about the auxiliary term % of realizability disjunction.
module _
  (_%_ : Prp → Prp → Prp)
  (
    %-def-1 : (P Q : Prp) → (¬ P ⇒ Q) ⇒ (¬ Q ⇒ P) ⇒ ¬ (P % Q) ⇒ P holds
  )
  (
    %-def-2 : (P Q : Prp) → (¬ P ⇒ Q) ⇒ (¬ Q ⇒ P) ⇒ ¬¬ (P % Q) ⇒ Q holds
  )
  where
  %-ext-1 : {P P' Q : Prp} → (P ⇒ P') ⇒ (P' ⇒ P) ⇒ (P % Q) ⇒ (P' % Q) holds
  %-ext-1 {P} {P'} {Q} [P⇒P'] [P'⇒P] =
    transport (λ z → (P % Q) ⇒ z holds) [[P%Q]=[P'%Q]] (λ [x=x] → [x=x]) where
      [P=P'] : P ≡ P'
      [P=P'] = propext [P⇒P'] [P'⇒P]
      [[P%Q]=[P'%Q]] : P % Q ≡ P' % Q
      [[P%Q]=[P'%Q]] = cong (λ z → z % Q) [P=P']

  %-ext-2 : {P Q Q' : Prp} → (Q ⇒ Q') ⇒ (Q' ⇒ Q) ⇒ (P % Q) ⇒ (P % Q') holds
  %-ext-2 {P} {Q} {Q'} [Q⇒Q'] [Q'⇒Q] =
    transport (λ z → (P % Q) ⇒ z holds) [[P%Q]=[P%Q']] (λ [x=x] → [x=x]) where
      [Q=Q'] : Q ≡ Q'
      [Q=Q'] = propext [Q⇒Q'] [Q'⇒Q]
      [[P%Q]=[P%Q']] : P % Q ≡ P % Q'
      [[P%Q]=[P%Q']] = cong (λ z → P % z) [Q=Q']

  -- Proposition 3.20 --
  true-reducts-1 : (P Q : Prp) → (P % Q) ⇒ Q ⇒ (P % true) holds
  true-reducts-1 P Q [P%Q] [Q] =
    %-ext-2 (λ _ → zero) (λ _ → [Q]) [P%Q]

  true-reducts-2 : ∀ P Q → (P % Q) ⇒ P ⇒ (true % Q) holds
  true-reducts-2 P Q [P%Q] [P] =
    %-ext-1 (λ _ → zero) (λ _ → [P]) [P%Q]

  true-reducts-3 : ∀ P Q → (P % true) ⇒ Q ⇒ (P % Q) holds
  true-reducts-3 P Q [P%⊤] [Q] =
    %-ext-2 (λ _ → [Q]) (λ _ → zero) [P%⊤]

  true-reducts-4 : ∀ P Q → (true % Q) ⇒ P ⇒ (P % Q) holds
  true-reducts-4 P Q [⊤%Q] [P] =
    %-ext-1 (λ _ → [P]) (λ _ → zero) [⊤%Q]

  -- Proposition 3.21 --
  reduct-consequences-1 : ∀ P → ¬ (P % true) ⇒ P holds
  reduct-consequences-1 P = %-def-1 P true (λ _ → zero) (by-contradiction P {true} zero)

  reduct-consequences-2 : ∀ Q → ¬¬ (true % Q) ⇒ Q holds
  reduct-consequences-2 Q = %-def-2 true Q (by-contradiction Q {true} zero) (λ _ → zero)

  -- Proposition 3.22 --
  reduct-switching-1 : ∀ P → (P % true) ⇒ P ⇒ (true % P) holds
  reduct-switching-1 P [P%⊤] [P] =
    %-ext-2 (λ _ → [P]) (λ _ → zero)
      (%-ext-1 (λ _ → zero) (λ _ → [P]) [P%⊤])

  reduct-switching-2 : ∀ P → (true % P) ⇒ P holds
  reduct-switching-2 P [P%⊤] = reduct-consequences-2 P (λ [¬[P%⊤]] → [¬[P%⊤]] [P%⊤])

  reduct-switching-3 : ∀ P → (true % P) ⇒ (P % true) holds
  reduct-switching-3 P [⊤%P] = %-ext-2 {P} {P} {true} (λ _ → zero) (λ _ → [P]) [P%P] where
    [P] : P holds
    [P] = reduct-switching-2 P [⊤%P]
    [P%P] : (P % P) holds
    [P%P] = true-reducts-4 P P [⊤%P] [P]

  -- Lemma 3.24 --
  main-lemma-1 : ∀ P → ¬ (P % ¬ (true % P)) ⇒ P holds
  main-lemma-1 P = step [¬¬[⊤%P]⇒P] where
    step : (¬¬ (true % P) ⇒ P) ⇒ ¬ (P % ¬ (true % P)) ⇒ P holds
    step [¬¬[⊤%P]⇒P] = %-def-1 P (¬ (true % P)) [¬[P%¬[⊤%P]]] [¬¬[⊤%P]⇒P] where
      [¬[P%¬[⊤%P]]] : ¬ P ⇒ ¬ (true % P) holds
      [¬[P%¬[⊤%P]]] [¬P] [⊤%P] = [¬P] ([¬¬[⊤%P]⇒P] (λ [¬[⊤%P]] → [¬[⊤%P]] [⊤%P]))
    [¬¬[⊤%P]⇒P] : ¬¬ (true % P) ⇒ P holds
    [¬¬[⊤%P]⇒P] [¬¬[⊤%P]] = reduct-consequences-2 P [¬¬[⊤%P]]

  -- Theorem 3.25 (the main lemma) --
  main-lemma-2 : ∀ P → ¬ (P % (P ⇒ ¬ (P % true))) ⇒ P holds
  main-lemma-2 P [¬[P%[P⇒¬[P%⊤]]]] = main-lemma-1 P [¬P%¬[⊤%P]] where
    [¬[P∧[P%T]]⇒¬[⊤%P]] : ¬ (P ∧ (P % true)) ⇒ ¬ (true % P) holds
    [¬[P∧[P%T]]⇒¬[⊤%P]] [¬[P∧[P%⊤]]] [⊤%P] =
      [¬[P∧[P%⊤]]] (reduct-switching-2 P [⊤%P] , reduct-switching-3 P [⊤%P])
    [¬[⊤%P]⇒¬[P∧[P%⊤]]] : ¬ (true % P) ⇒ ¬ (P ∧ (P % true)) holds
    [¬[⊤%P]⇒¬[P∧[P%⊤]]] [¬[⊤%P]] [P∧[P%⊤]] =
      [¬[⊤%P]] (reduct-switching-1 P (∧-elim-R {P} {P % true} [P∧[P%⊤]]) (∧-elim-L {P} {P % true} [P∧[P%⊤]]))
    step : ¬ (P % (P ⇒ ¬ (P % true))) ⇒ ¬ (P % ¬ (true % P)) holds
    step [¬[P%[P⇒¬[P%⊤]]]] [P%¬[⊤%P]] = [¬[P%[P⇒¬[P%⊤]]]] [P%[P⇒¬[P%⊤]]] where
      [P%[P⇒¬[P%⊤]]] : (P % (P ⇒ ¬ (P % true))) holds
      [P%[P⇒¬[P%⊤]]] = %-ext-2 {P} {¬ (true % P)} {P ⇒ ¬ (P % true)}
        (λ [¬[⊤%P]] [P] [P%⊤] → [¬[⊤%P]⇒¬[P∧[P%⊤]]] [¬[⊤%P]] ([P] , [P%⊤]))
        (λ [P⇒¬[P%⊤]] → [¬[P∧[P%T]]⇒¬[⊤%P]] (λ [P∧[P%⊤]] → [P⇒¬[P%⊤]]
          (∧-elim-L {P} {P % true} [P∧[P%⊤]])
          (∧-elim-R {P} {P % true} [P∧[P%⊤]])))
        [P%¬[⊤%P]]
    [¬P%¬[⊤%P]] :  ¬ (P % ¬ (true % P)) holds
    [¬P%¬[⊤%P]] [P%[¬[⊤%P]]] = step [¬[P%[P⇒¬[P%⊤]]]] [P%[¬[⊤%P]]]

  main-lemma-3 : ∀ P → (P % (P ⇒ ¬ (P % true))) ⇒ ¬ P holds
  main-lemma-3 P [P%[P⇒¬[P%⊤]]] [P] =
    %-def-2 P false (λ [¬P] → [¬P] [P]) (λ _ → [P]) [¬¬[P%⊥]] where
    [¬¬[P%⊥]] : ¬¬ (P % false) holds
    [¬¬[P%⊥]] [¬[P%⊥]] = [¬[P%⊥]] [P%⊥] where
      [P%⊥] : (P % false) holds
      [P%⊥] = %-ext-2 {P} {P ⇒ ¬ (P % true)} {false}
        (λ [P⇒¬[P%⊤]] → [P⇒¬[P%⊤]] [P] (%-ext-2 {P} {P ⇒ ¬ (P % true)} {true}
          (λ _ → zero)
          (λ _ → [P⇒¬[P%⊤]])
          [P%[P⇒¬[P%⊤]]]))
        (λ ())
        [P%[P⇒¬[P%⊤]]]

  -- and there we go...
  dneg-elim : ∀ P → ¬¬ P ⇒ P holds
  dneg-elim P [¬¬P] = main-lemma-2 P (λ [P%[P→¬P]%⊤] → [¬¬P] (main-lemma-3 P [P%[P→¬P]%⊤]))
