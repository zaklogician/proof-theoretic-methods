module KreiselStar where

open import preliminaries
open import prop
open import logic
open import Common

{-
  All results pertaining to Kreisel's star connective and
  Troelstra's generalizations.
-}

-- Theorem 4.18 --
module _
  (ψ : Prp → Prp)
  (ψ-negneg : (P : Prp) → ¬¬ (ψ P) holds)
  (ψ-intro : (P : Prp) → P ⇒ ψ P holds)
  (ψ-elim : (P : Prp) → (ψ P ⇒ P) ⇒ P holds)
  (t : Prp → Prp)
  (ψt-def-1 : (P : Prp) → P ⇒ ψ (t P) holds)
  (ψt-def-2 : (P : Prp) → ¬¬ P ⇒ ψ (t P) ⇒ P holds)
  where

  ψ-ext : {P P' : Prp} → (P ⇒ P') ⇒ (P' ⇒ P) ⇒ ψ P ⇒ ψ P' holds
  ψ-ext {P} {P'} [P⇒P'] [P'⇒P] =
    transport (λ z → ψ z holds) [P=P'] where
      [P=P'] : P ≡ P'
      [P=P'] = propext {P} {P'} [P⇒P'] [P'⇒P]

  t-ext : {P P' : Prp} → (P ⇒ P') ⇒ (P' ⇒ P) ⇒ t P ⇒ t P' holds
  t-ext {P} {P'} [P⇒P'] [P'⇒P] =
    transport (λ z → t z holds) [P=P'] where
      [P=P'] : P ≡ P'
      [P=P'] = propext {P} {P'} [P⇒P'] [P'⇒P]

  -- abbreviatons 
  ψt : Prp → Prp
  ψt x = ψ (t x)

  tψ : Prp → Prp
  tψ x = t (ψ x)

  ψtψ : Prp → Prp
  ψtψ x = ψ (t (ψ x))

  tψt : Prp → Prp
  tψt x = t (ψ (t x))

  -- Lemma 4.10 --
  trivium-1 : (P : Prp) → ψtψ P ⇒ ψ P holds
  trivium-1 P = ψt-def-2 (ψ P) (ψ-negneg P)

  trivium-2 : (P : Prp) → ψ P ⇒ ψtψ P holds
  trivium-2 P = ψt-def-1 (ψ P)

  trivium-3 : (P : Prp) → (ψ P ⇒ tψ P) ⇒ tψ P holds
  trivium-3 P [ψP→tψP] =
    ψ-elim (t (ψ P)) (λ [ψtψP] → [ψP→tψP] (trivium-1 P [ψtψP]))

  -- Lemma 4.11 --
  quadrivium-1 : (P : Prp) → tψ P ⇒ t true holds
  quadrivium-1 P [tψP] =
    t-ext {ψ P} {true} (λ _ → zero)
      (λ _ → ψt-def-2 (ψ P) (ψ-negneg P) (ψ-intro (t (ψ P)) [tψP])) [tψP]

  quadrivium-2 : (P : Prp) → (t true ⇒ tψ P) ⇒ ψ P holds
  quadrivium-2 P [t⊤→tψP] =
    trivium-1 P
      (ψ-ext {t true} {t (ψ P)} [t⊤→tψP] (quadrivium-1 P) (ψt-def-1 true zero))

  quadrivium-3 : (P : Prp) → tψ P ⇒ ψ P holds
  quadrivium-3 P [tψP] =
    ψt-def-2 (ψ P) (ψ-negneg P) (ψ-intro (t (ψ P)) [tψP])

  quadrivium-4 : (P : Prp) → (tψ P ⇒ ψ P) ⇒ ψ P holds
  quadrivium-4 P [tψP→ψP] =
    quadrivium-2 P
      (λ [t⊤] → trivium-3 P (λ [ψP] → t-ext {true} {ψ P} (λ _ → [ψP]) (λ _ → zero) [t⊤]))  

  -- and there we go... 
  dneg-elim : (P : Prp) → ¬¬ P ⇒ P holds
  dneg-elim P [¬¬P] =
    ψt-def-2 P [¬¬P] [ψtP] where
      [[¬¬P]→[ψtP]→P] : ¬¬ P ⇒ ψ (t P) ⇒ P holds
      [[¬¬P]→[ψtP]→P] = ψt-def-2 P
      [[tψtP→ψtP]→ψtP] : (tψt P ⇒ ψt P) ⇒ ψt P holds
      [[tψtP→ψtP]→ψtP] = quadrivium-4 (t P)
      [ψtP] : ψt P holds
      [ψtP] = [[tψtP→ψtP]→ψtP] (quadrivium-3 (t P))
