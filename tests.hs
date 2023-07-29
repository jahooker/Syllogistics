import TermLogic

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

-- with existential assumption
testvalid = filter isValid $ instantiate <$> syllogistic_forms
