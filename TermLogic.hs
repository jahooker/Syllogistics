module TermLogic where

import Data.List (delete)

type Term = String  -- requires (Show, Eq)

-- Term-logical quantifiers
data Quantifier
  = A {- universal  affirmative -} | E {- universal  negative -}
  | I {- particular affirmative -} | O {- particular negative -}
  deriving (Show, Eq, Ord, Enum)

isUniversal :: Quantifier -> Bool
isUniversal q = q == A || q == E

isParticular :: Quantifier -> Bool
isParticular q = q == I || q == O
-- isParticular = not . isUniversal

isAffirmative :: Quantifier -> Bool
isAffirmative q = q == A || q == I

isNegative :: Quantifier -> Bool
isNegative q = q == E || q == O
-- isNegative = not . isAffirmative

entailsSubjectNonEmpty :: Quantifier -> Bool
entailsSubjectNonEmpty q = q == I || q == O

entailsPredicateNonEmpty :: Quantifier -> Bool
entailsPredicateNonEmpty q = q == I

entailsNonEmpty :: CatProp -> Term -> Bool
entailsNonEmpty (CatProp q s p) x
  =  x == s && entailsSubjectNonEmpty   q
  || x == p && entailsPredicateNonEmpty q

-- Categorical propositions
data CatProp
  = CatProp { quantifier :: Quantifier, subject :: Term, predicate :: Term }
  deriving (Show, Eq)

isQuantifierNegative    = isNegative    . quantifier
isQuantifierAffirmative = isAffirmative . quantifier

isSubjectDistributed :: CatProp -> Bool
isSubjectDistributed (CatProp q _ _) = q `elem` [A, E]
-- isSubjectDistributed = isUniversal . quantifier

isPredicateDistributed :: CatProp -> Bool
isPredicateDistributed (CatProp q _ _) = q `elem` [E, O {- allegedly -}]
-- isPredicateDistributed = isNegative . quantifier

data Figure
  = Figure1 {- MxP && SxM <= SxP -} | Figure2 {- PxM && SxM <= SxP -}
  | Figure3 {- MxP && MxS <= SxP -} | Figure4 {- PxM && MxS <= SxP -}
  deriving (Show, Eq, Ord, Enum)

data Syllogism
  = Syllogism Figure Quantifier Quantifier Quantifier Term Term Term
  deriving (Show, Eq, Ord)

figure :: Syllogism -> Figure
figure (Syllogism f _ _ _ _ _ _) = f

minorTerm :: Syllogism -> Term
minorTerm (Syllogism _ _ _ _ s _ _) = s
-- majorTerm = subject . conclusion

middleTerm :: Syllogism -> Term
middleTerm (Syllogism _ _ _ _ _ m _) = m

majorTerm :: Syllogism -> Term
majorTerm (Syllogism _ _ _ _ _ _ p) = p
-- majorTerm = predicate . conclusion

majorPremise :: Syllogism -> CatProp
majorPremise (Syllogism f q _ _ _ m p) = case f of
  Figure1 -> CatProp q m p
  Figure2 -> CatProp q p m
  Figure3 -> CatProp q m p
  Figure4 -> CatProp q p m

minorPremise :: Syllogism -> CatProp
minorPremise (Syllogism f _ q _ s m _) = case f of
  Figure1 -> CatProp q s m
  Figure2 -> CatProp q s m
  Figure3 -> CatProp q m s
  Figure4 -> CatProp q m s

conclusion :: Syllogism -> CatProp
conclusion (Syllogism _ _ _ q s _ p) = CatProp q s p

equivalent :: Syllogism -> Syllogism -> Bool
equivalent x y = conclusion x == conclusion y
  && (majX == majY && minX == minY
  ||  majX == minY && minX == majY)
  where majX = majorPremise x
        majY = majorPremise y
        minX = minorPremise x
        minY = minorPremise y

majorPremiseEntailsMajorTermNonEmpty syl = case figure syl of
  Figure1 -> entailsPredicateNonEmpty
  Figure2 -> entailsSubjectNonEmpty
  Figure3 -> entailsPredicateNonEmpty
  Figure4 -> entailsSubjectNonEmpty
  $ quantifier $ majorPremise syl

minorPremiseEntailsMinorTermNonEmpty syl = case figure syl of
  Figure1 -> entailsSubjectNonEmpty
  Figure2 -> entailsSubjectNonEmpty
  Figure3 -> entailsPredicateNonEmpty
  Figure4 -> entailsPredicateNonEmpty
  $ quantifier $ minorPremise syl

sub = CatProp A

majorPremiseEntailsMiddleTermSubsetOfMajorTerm syl =
  majorPremise syl == middleTerm syl `sub` majorTerm syl

minorPremiseEntailsMiddleTermSubsetOfMinorTerm syl =
  minorPremise syl == middleTerm syl `sub` minorTerm syl

premisesEntailMiddleTermNonEmpty syl =
  any (`entailsNonEmpty` middleTerm syl) $ [majorPremise, minorPremise] <*> [syl]

premisesEntailMinorTermSubsetOfMajorTerm syl =
  let [min, mid, maj] = [minorTerm, middleTerm, majorTerm] <*> [syl]
      premises = [majorPremise, minorPremise] <*> [syl] in
  all (`elem` premises) [min `sub` mid, mid `sub` maj]

premisesEntailMajorTermSubsetOfMinorTerm syl =
  let [min, mid, maj] = [minorTerm, middleTerm, majorTerm] <*> [syl]
      premises = [majorPremise, minorPremise] <*> [syl] in
  all (`elem` premises) [maj `sub` mid, mid `sub` min]

barbara   = Syllogism Figure1 A A A
celarent  = Syllogism Figure1 E A E
darii     = Syllogism Figure1 A I I
ferio     = Syllogism Figure1 E I O
barbari   = Syllogism Figure1 A A I
celaront  = Syllogism Figure1 E A O

cesare    = Syllogism Figure2 E A E
camestres = Syllogism Figure2 A E E
festino   = Syllogism Figure2 E I O
baroco    = Syllogism Figure2 A O O
cesaro    = Syllogism Figure2 E A O
camestros = Syllogism Figure2 A E O

datisi    = Syllogism Figure3 A I I
disamis   = Syllogism Figure3 I A I
ferison   = Syllogism Figure3 E I O
bocardo   = Syllogism Figure3 O A O
felapton  = Syllogism Figure3 E A O
darapti   = Syllogism Figure3 A A I

calemes   = Syllogism Figure4 A E E
dimatis   = Syllogism Figure4 I A I
fresison  = Syllogism Figure4 E I O
calemos   = Syllogism Figure4 A E O
fesapo    = Syllogism Figure4 E A O
bamalip   = Syllogism Figure4 A A I

valid_syllogisms = [
  barbara, celarent,  darii,    ferio,   barbari,  celaront,   -- Figure1
  cesare,  camestres, festino,  baroco,  cesaro,   camestros,  -- Figure2
  datisi,  disamis,   ferison,  bocardo, felapton, darapti,    -- Figure3
  calemes, dimatis,   fresison, calemos, fesapo,   bamalip]    -- Figure4

-- 4 * 4 * 4 * 4 = 256
syllogistic_forms = [
  Syllogism f q r s | f <- [Figure1 .. Figure4],
                      q <- [A .. O], r <- [A .. O], s <- [A .. O]]

instantiate :: (String -> String -> String -> Syllogism) -> Syllogism
instantiate f = f "S" "M" "P"

isValidSyllogism :: Syllogism -> Bool
isValidSyllogism syl = case syl of
  Syllogism Figure1 A A A _ _ _ -> True
  Syllogism Figure1 E A E _ _ _ -> True
  Syllogism Figure1 A I I _ _ _ -> True
  Syllogism Figure1 E I O _ _ _ -> True
  Syllogism Figure2 E A E _ _ _ -> True
  Syllogism Figure2 A E E _ _ _ -> True
  Syllogism Figure2 E I O _ _ _ -> True
  Syllogism Figure2 A O O _ _ _ -> True
  Syllogism Figure3 A I I _ _ _ -> True
  Syllogism Figure3 I A I _ _ _ -> True
  Syllogism Figure3 E I O _ _ _ -> True
  Syllogism Figure3 O A O _ _ _ -> True
  Syllogism Figure4 A E E _ _ _ -> True
  Syllogism Figure4 I A I _ _ _ -> True
  Syllogism Figure4 E I O _ _ _ -> True
  Syllogism Figure4 A E O _ _ _ -> True
  _                             -> False

isValidSyllogismWithExistentialAssumption :: Syllogism -> Bool
isValidSyllogismWithExistentialAssumption syl
  = isValidSyllogism syl || case syl of
    Syllogism Figure1 A A I _ _ _ -> True
    Syllogism Figure1 E A O _ _ _ -> True
    Syllogism Figure2 E A O _ _ _ -> True
    Syllogism Figure2 A E O _ _ _ -> True
    Syllogism Figure3 E A O _ _ _ -> True
    Syllogism Figure3 A A I _ _ _ -> True
    Syllogism Figure4 E A O _ _ _ -> True
    Syllogism Figure4 A A I _ _ _ -> True
    _                             -> False

isMiddleTermDistributedInMajorPremise :: Syllogism -> Bool
isMiddleTermDistributedInMajorPremise syl = case figure syl of
  Figure1 -> isSubjectDistributed
  Figure2 -> isPredicateDistributed
  Figure3 -> isSubjectDistributed
  Figure4 -> isPredicateDistributed
  $ majorPremise syl

isMajorTermDistributedInMajorPremise :: Syllogism -> Bool
isMajorTermDistributedInMajorPremise syl = case figure syl of
  Figure1 -> isPredicateDistributed
  Figure2 -> isSubjectDistributed
  Figure3 -> isPredicateDistributed
  Figure4 -> isSubjectDistributed
  $ majorPremise syl

isMiddleTermDistributedInMinorPremise :: Syllogism -> Bool
isMiddleTermDistributedInMinorPremise syl = case figure syl of
  Figure1 -> isPredicateDistributed
  Figure2 -> isPredicateDistributed
  Figure3 -> isSubjectDistributed
  Figure4 -> isSubjectDistributed
  $ minorPremise syl

isMinorTermDistributedInMinorPremise :: Syllogism -> Bool
isMinorTermDistributedInMinorPremise syl = case figure syl of
  Figure1 -> isSubjectDistributed
  Figure2 -> isSubjectDistributed
  Figure3 -> isPredicateDistributed
  Figure4 -> isPredicateDistributed
  $ minorPremise syl

isMajorTermDistributedInConclusion :: Syllogism -> Bool
isMajorTermDistributedInConclusion = isPredicateDistributed . conclusion

isMinorTermDistributedInConclusion :: Syllogism -> Bool
isMinorTermDistributedInConclusion = isSubjectDistributed . conclusion

-- According to the rule of "undistributed middle",
-- a valid syllogism must have its middle term distributed in at least one premise.
isMiddleTermDistributed :: Syllogism -> Bool
isMiddleTermDistributed = isMiddleTermDistributedInMajorPremise
                      ||| isMiddleTermDistributedInMinorPremise

-- The major term is undistributed in the major premise but distributed in the conclusion.
illicitMajor :: Syllogism -> Bool
illicitMajor = isMajorTermDistributedInConclusion
     &&& not . isMajorTermDistributedInMajorPremise

-- The minor term is undistributed in the minor premise but distributed in the conclusion.
illicitMinor :: Syllogism -> Bool
illicitMinor = isMinorTermDistributedInConclusion
     &&& not . isMinorTermDistributedInMinorPremise

isValid :: Syllogism -> Bool
isValid = isMiddleTermDistributed
  &&& not . illicitMajor
  &&& not . illicitMinor
  &&& not . illicitAffirmative
  &&& not . illicitNegative
  &&& not . exclusivePremises

-- The fallacy of "exclusive premises" is committed
-- when both premises of a syllogism are negative.
exclusivePremises :: Syllogism -> Bool
exclusivePremises = isQuantifierNegative . majorPremise
                &&& isQuantifierNegative . minorPremise

-- The fallacy of "negative conclusion from affirmative premises" is committed
-- when a syllogism has a negative conclusion but two affirmative premises.
illicitAffirmative :: Syllogism -> Bool
illicitAffirmative =  isQuantifierNegative    . conclusion
                  &&& isQuantifierAffirmative . majorPremise
                  &&& isQuantifierAffirmative . minorPremise

-- The fallacy of "illicit negative" is committed
-- when a syllogism has an affirmative conclusion and a negative premise.
illicitNegative :: Syllogism -> Bool
illicitNegative = isQuantifierAffirmative . conclusion
             &&& (isQuantifierNegative    . majorPremise
             |||  isQuantifierNegative    . minorPremise)

-- 9 of the 24 valid syllogistic forms are only conditionally valid.
-- To reach the conclusion, one must assume that one of the terms is not empty.
existentialAssumption :: Syllogism -> Bool
existentialAssumption (Syllogism f q r s _ _ _)
  = assumesMajorTermNonEmpty || assumesMinorTermNonEmpty || assumesMiddleTermNonEmpty
  where fqrs = (f, q, r, s)
        assumesMinorTermNonEmpty  = fqrs `elem` [
          (Figure1, A, A, I), (Figure1, E, A, O),
          (Figure2, A, E, O), (Figure2, E, A, O),
          (Figure4, A, E, O)]
        assumesMiddleTermNonEmpty = fqrs `elem` [
          (Figure3, A, A, I), (Figure3, E, A, O),
          (Figure4, E, A, O)]
        assumesMajorTermNonEmpty  = fqrs `elem` [
          (Figure4, A, A, I)]

-- The conclusion entails that one of the terms is not empty,
-- but the premises do not carry this entailment.
existentialAssumption' :: Syllogism -> Bool
existentialAssumption' = isValid
  &&& (conclusionEntailsMajorTermNonEmpty &&& not . premisesEntailMajorTermNonEmpty
  |||  conclusionEntailsMinorTermNonEmpty &&& not . premisesEntailMinorTermNonEmpty)
  where conclusionEntailsMinorTermNonEmpty
          = entailsSubjectNonEmpty . quantifier . conclusion
        conclusionEntailsMajorTermNonEmpty
          = entailsPredicateNonEmpty . quantifier . conclusion
        premisesEntailMajorTermNonEmpty = majorPremiseEntailsMajorTermNonEmpty
          ||| minorPremiseEntailsMinorTermNonEmpty &&& premisesEntailMinorTermSubsetOfMajorTerm
          ||| premisesEntailMiddleTermNonEmpty     &&& majorPremiseEntailsMiddleTermSubsetOfMajorTerm
        premisesEntailMinorTermNonEmpty = minorPremiseEntailsMinorTermNonEmpty
          ||| majorPremiseEntailsMajorTermNonEmpty &&& premisesEntailMajorTermSubsetOfMinorTerm
          ||| premisesEntailMiddleTermNonEmpty     &&& minorPremiseEntailsMiddleTermSubsetOfMinorTerm

isPermutation :: Eq a => [a] -> [a] -> Bool
isPermutation (x:xs) ys = x `elem` ys && xs `isPermutation` delete x ys
isPermutation [    ] ys = null ys

-- all (\syl -> existentialAssumption syl == existentialAssumption' syl)
--   $ instantiate <$> syllogistic_forms

(&&&) :: (t -> Bool) -> (t -> Bool) -> (t -> Bool)
f &&& g = \x -> f x && g x
infixr 3 &&&

(|||) :: (t -> Bool) -> (t -> Bool) -> (t -> Bool)
f ||| g = \x -> f x || g x 
infixr 2 |||
