theory Check
  imports Submission
begin

lemma oddsum_is_square: "oddsum n = n * n"
  by (rule Submission.oddsum_is_square)

lemma oddsum_mult: "oddsum (n*m) = oddsum n * oddsum m"
  by (rule Submission.oddsum_mult)

lemma count_spread: "count (spread a xs) a = count xs a + length xs"
  by (rule Submission.count_spread)

lemma spread_reverse_snoc: "snoc (reverse (spread a xs)) a = a # spread a (reverse xs)"
  by (rule Submission.spread_reverse_snoc)

end