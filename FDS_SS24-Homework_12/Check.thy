theory Check
  imports Submission
begin

context counter_with_decr begin

theorem inc_dec_seq_ubound: "length bs = k \<Longrightarrow> T_exec ops bs \<le> (length ops) * length bs"
  by (rule inc_dec_seq_ubound)

theorem inc_dec_seq_lbound: "length (oplist n) * k \<le> 2 * (T_exec (oplist n) bs0)"
  by (rule inc_dec_seq_lbound)

end

end