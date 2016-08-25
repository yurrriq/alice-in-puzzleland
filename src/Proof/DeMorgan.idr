module Proof.DeMorgan

%access  public export
%default total

syntax "($" [x] ")" = \f => f x

infixl 8 .:
(.:) : (c -> d) -> (a -> b -> c) -> (a -> b -> d)
(.:) = (.) . (.)

using (P: Type, Q : Type, R : Type)

  ||| https://proofwiki.org/wiki/Rule_of_Addition/Proof_Rule#Proof_Rule
  add1 : P -> Either P Q
  add1 = Left

  add2 : Q -> Either P Q
  add2 = Right

  ||| https://proofwiki.org/wiki/Double_Negation/Double_Negation_Introduction/Proof_Rule
  doubleNegation : P -> Not (Not P)
  doubleNegation = flip id

  -- doubleNegation' : Not (Not P) -> P
  -- doubleNegation' = believe_me P

  idempotenceAnd : P -> (P, P)
  idempotenceAnd p = (p, p)

  idempotenceAnd' : (P, P) -> P
  idempotenceAnd' = fst

  idempotenceOr : P -> Either P P
  idempotenceOr = Right

  idempotenceOr' : Either P P -> P
  idempotenceOr' = fromEither

  contrapositive : (P -> Q) -> (Not Q -> Not P)
  contrapositive = flip (.)

  notE : P -> Not P -> Void
  notE = flip id

  notE' : Not P -> P -> Void
  notE' = flip notE

  -- notE_and : (P, Q) -> Not P -> Void
  -- notE_and = notE . fst

  ||| https://proofwiki.org/wiki/Modus_Ponendo_Ponens/Proof_Rule
  modusPonendoPonens : (P -> Q) -> P -> Q
  modusPonendoPonens = id

  modusTollendoPonens : (Either P Q) -> Not P -> Q
  modusTollendoPonens = either (void .: notE) const

  excludedMiddle : P -> Either P (Not P)
  excludedMiddle = Left

  excludedMiddle2 : Not (Not P -> Q) -> Not (Either P Q)
  excludedMiddle2 = (. modusTollendoPonens)

  ||| https://proofwiki.org/wiki/Rule_of_Material_Implication/Formulation_1/Forward_Implication
  materialImplication1F : P -> Q -> Either (Not P) Q
  materialImplication1F p q = Right q

  ||| https://proofwiki.org/wiki/Rule_of_Material_Implication/Formulation_1/Reverse_Implication
  materialImplication1R : Either (Not P) Q -> P -> Q
  materialImplication1R = (. doubleNegation) . modusTollendoPonens

  ||| https://proofwiki.org/wiki/Implication_Equivalent_to_Negation_of_Conjunction_with_Negative/Formulation_1/Forward_Implication
  implEquivNegConjWithNeg : (P -> Q) -> Not (P, Not Q)
  implEquivNegConjWithNeg f (p, notQ) = notE (modusPonendoPonens f p) notQ


  ||| https://proofwiki.org/wiki/De_Morgan%27s_Laws_(Logic)/Conjunction_of_Negations/Formulation_1/Forward_Implication
  deMorganConjNeg1F : (Not P, Not Q) -> Not (Either P Q)
  deMorganConjNeg1F (f, g) = notE' (either f g)

  ||| https://proofwiki.org/wiki/De_Morgan%27s_Laws_(Logic)/Conjunction_of_Negations/Formulation_1/Reverse_Implication
  deMorganConjNeg1R : Not (Either P Q) -> (Not P, Not Q)
  deMorganConjNeg1R f = (notE' f . add1, notE' f . add2)
  -- TODO: Arrows?

  ||| https://proofwiki.org/wiki/De_Morgan%27s_Laws_(Logic)/Disjunction_of_Negations/Formulation_1/Forward_Implication
  deMorganDisjNeg1F : Either (Not P) (Not Q) -> Not (P, Q)
  deMorganDisjNeg1F e (p, q) = either ($ p) ($ q) e

  ||| https://proofwiki.org/wiki/De_Morgan%27s_Laws_(Logic)/Disjunction_of_Negations/Formulation_1/Reverse_Implication
  -- deMorganDisjNeg1R : Not (P, Q) -> Either (Not P) (Not Q)
  -- deMorganDisjNeg1R x = ?deMorganDisjNeg1R_rhs

  ||| https://proofwiki.org/wiki/De_Morgan%27s_Laws_(Logic)/Conjunction_of_Negations/Formulation_2
  deMorganConjNeg2F : (Not P, Not Q) -> Not (Either P Q)
  deMorganConjNeg2F (notP, notQ) =
    either (deMorganDisjNeg1F (Left notP) . idempotenceAnd) notQ

  deMorganConjNeg2R : Not (Either P Q) -> (Not P, Not Q)
  deMorganConjNeg2R = deMorganConjNeg1R
