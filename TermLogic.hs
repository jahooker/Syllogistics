import Data.List (delete)

type Term = String  -- requires (Show, Eq)

-- Term-logical quantifiers
data Quantifier
  = A {- universal  affirmative -} | E {- universal  negative -}
  | I {- particular affirmative -} | O {- particular negative -}
  deriving (Show, Eq, Ord)

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

entailsNotEmpty :: CatProp -> Term -> Bool
entailsNotEmpty (CatProp q s p) x
  =  x == s && entailsSubjectNonEmpty   q
  || x == p && entailsPredicateNonEmpty q

-- Categorical propositions
data CatProp
  = CatProp { quantifier :: Quantifier, subject :: Term, predicate :: Term }
  deriving (Show, Eq)

isQuantifierNegative    = isNegative    . quantifier
isQuantifierAffirmative = isAffirmative . quantifier

isSubjectDistributed :: CatProp -> Bool
isSubjectDistributed (CatProp q _ _) = case q of
  A -> True
  E -> True
  I -> False
  O -> False
-- isSubjectDistributed = isUniversal . quantifier

isPredicateDistributed :: CatProp -> Bool
isPredicateDistributed (CatProp q _ _) = case q of
  A -> False  -- allegedly
  E -> True
  I -> False
  O -> True   -- allegedly
-- isSubjectDistributed = isNegative . quantifier

data Figure
  = Figure1 {- MxP && SxM <= SxP -} | Figure2 {- PxM && SxM <= SxP -}
  | Figure3 {- MxP && MxS <= SxP -} | Figure4 {- PxM && MxS <= SxP -}
  deriving (Show, Eq, Ord)

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
  -- Figure1
  barbara, celarent,  darii,    ferio,    -- barbari,  celaront,
  -- Figure2
  cesare,  camestres, festino,  baroco,   -- cesaro,   camestros,
  -- Figure3
  datisi,  disamis,   ferison,  bocardo,  -- felapton, darapti,
  -- Figure4
  calemes, dimatis,   fresison, calemos   -- fesapo,   bamalip,
  ]

-- 4 * 4 * 4 * 4 = 256
syllogistic_forms = [
  Syllogism f q r s | f <- [Figure1, Figure2, Figure3, Figure4],
                      q <- [A, E, I, O],
                      r <- [A, E, I, O],
                      s <- [A, E, I, O]]

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
isMiddleTermDistributed syl
  =  isMiddleTermDistributedInMajorPremise syl
  || isMiddleTermDistributedInMinorPremise syl

-- Verify the law of undistributed middle
test_undistributed_middle = and
  $ (isMiddleTermDistributed . instantiate) <$> valid_syllogisms

-- Which invalid syllogisms are not explained by the law of undistributed middle?
not_explained_by_undistributed_middle = length
  $ filter isMiddleTermDistributed $ filter (not . valid)
  $ instantiate <$> syllogistic_forms
  where valid syl = syl `elem` (instantiate <$> valid_syllogisms)

-- Which invalid syllogisms break the law of undistributed middle?
examples_of_undistributed_middle
  = filter (not . isMiddleTermDistributed) $ invalid_syllogisms
  where invalid_syllogisms = filter (not . valid) $ instantiate <$> syllogistic_forms
        valid syl = syl `elem` (instantiate <$> valid_syllogisms)

-- Which valid syllogisms break the law of undistributed middle?
counterexamples_to_undistributed_middle
  = filter (not . isMiddleTermDistributed) $ instantiate <$> valid_syllogisms

check_number_of_syllogisms = do
  let n = length syllogistic_forms
  let status = n == 256
  putStrLn $ "There are " ++ show n ++ " different kinds of syllogism. " ++ show status
  return status

check_number_of_valid_syllogisms = do
  let n = length $ filter isValidSyllogism $ instantiate <$> syllogistic_forms
  let status = n == 16
  putStrLn $ "There are " ++ show n ++ " valid kinds of syllogism. " ++ show status
  return status

checks = do
  status <- check_number_of_syllogisms
  if not status then return status else check_number_of_valid_syllogisms

-- The major term is undistributed in the major premise but distributed in the conclusion.
illicitMajor :: Syllogism -> Bool
illicitMajor syl
  =       isMajorTermDistributedInConclusion   syl
  && not (isMajorTermDistributedInMajorPremise syl)

-- The minor term is undistributed in the minor premise but distributed in the conclusion.
illicitMinor :: Syllogism -> Bool
illicitMinor syl
  =       isMinorTermDistributedInConclusion   syl
  && not (isMinorTermDistributedInMinorPremise syl)

-- with existential assumption
testvalid = filter isValid $ instantiate <$> syllogistic_forms

isValid :: Syllogism -> Bool
isValid syl = isMiddleTermDistributed syl
  && not (illicitMajor       syl)
  && not (illicitMinor       syl)
  && not (illicitAffirmative syl)
  && not (illicitNegative    syl)
  && not (exclusivePremises  syl)

-- The fallacy of "exclusive premises" is committed
-- when both premises of a syllogism are negative.
exclusivePremises :: Syllogism -> Bool
exclusivePremises syl = isQuantifierNegative maj && isQuantifierNegative min
  where maj = majorPremise syl
        min = minorPremise syl

-- The fallacy of "negative conclusion from affirmative premises" is committed
-- when a syllogism has a negative conclusion but two affirmative premises.
illicitAffirmative :: Syllogism -> Bool
illicitAffirmative syl =  isQuantifierNegative    (conclusion   syl)
                       && isQuantifierAffirmative (majorPremise syl)
                       && isQuantifierAffirmative (minorPremise syl)

-- The fallacy of "illicit negative" is committed
-- when a syllogism has an affirmative conclusion and a negative premise.
illicitNegative :: Syllogism -> Bool
illicitNegative syl =   isQuantifierAffirmative (conclusion   syl)
                    && (isQuantifierNegative    (majorPremise syl)
                    ||  isQuantifierNegative    (minorPremise syl))

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

existentialAssumption' :: Syllogism -> Bool
existentialAssumption' syl@(Syllogism f _ _ _ _ _ _)
  -- The conclusion must be an I-type or an O-type proposition.
  -- I-type propositions entail the existence of the subject and predicate terms.
  -- O-type propositions entail the existence of the subject term.
  -- "entail" == "cannot be true without"
  = (conclusionEntailsMajorTermNonEmpty && not premisesEntailMajorTermNonEmpty
  || conclusionEntailsMinorTermNonEmpty && not premisesEntailMinorTermNonEmpty)
  && isValid syl
  where [min, mid, maj] = [minorTerm, middleTerm, majorTerm] <*> [syl]
        premises = [majorPremise, minorPremise] <*> [syl]
        conclusionEntailsMinorTermNonEmpty
          = ($ quantifier (conclusion syl)) entailsSubjectNonEmpty   
        conclusionEntailsMajorTermNonEmpty
          = ($ quantifier (conclusion syl)) entailsPredicateNonEmpty
        majorPremiseEntailsMajorTermNonEmpty
          = ($ quantifier (majorPremise syl)) $ case f of
            Figure1 -> entailsPredicateNonEmpty
            Figure2 -> entailsSubjectNonEmpty
            Figure3 -> entailsPredicateNonEmpty
            Figure4 -> entailsSubjectNonEmpty
        minorPremiseEntailsMinorTermNonEmpty
          = ($ quantifier (minorPremise syl)) $ case f of
            Figure1 -> entailsSubjectNonEmpty
            Figure2 -> entailsSubjectNonEmpty
            Figure3 -> entailsPredicateNonEmpty
            Figure4 -> entailsPredicateNonEmpty
        premisesEntailMajorTermNonEmpty = majorPremiseEntailsMajorTermNonEmpty
          || minorPremiseEntailsMinorTermNonEmpty && premisesEntailMinorTermSubsetOfMajorTerm
          || premisesEntailMiddleTermNonEmpty     && majorPremiseEntailsMiddleTermSubsetOfMajorTerm
        premisesEntailMinorTermNonEmpty = minorPremiseEntailsMinorTermNonEmpty
          || majorPremiseEntailsMajorTermNonEmpty && premisesEntailMajorTermSubsetOfMinorTerm
          || premisesEntailMiddleTermNonEmpty     && minorPremiseEntailsMiddleTermSubsetOfMinorTerm
        premisesEntailMinorTermSubsetOfMajorTerm = let (<=) = CatProp A in
          all (`elem` premises) [min <= mid, mid <= maj]
        premisesEntailMajorTermSubsetOfMinorTerm = let (<=) = CatProp A in
          all (`elem` premises) [maj <= mid, mid <= min]
        premisesEntailMiddleTermNonEmpty = any (`entailsNotEmpty` mid) premises
        majorPremiseEntailsMiddleTermSubsetOfMajorTerm
          = f `elem` [Figure1, Figure3] && quantifier (majorPremise syl) == A
        minorPremiseEntailsMiddleTermSubsetOfMinorTerm
          = f `elem` [Figure3, Figure4] && quantifier (minorPremise syl) == A

isPermutation :: Eq a => [a] -> [a] -> Bool
isPermutation (x:xs) ys = x `elem` ys && xs `isPermutation` delete x ys
isPermutation [    ] ys = null ys
