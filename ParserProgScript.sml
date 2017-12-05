open preamble basis CheckerProgTheory myparserTheory

val _ = new_theory"ParserProg";

val _ = translation_extends"CheckerProg"

val r = translate OPTION_BIND_def;
val r = translate OPT_MMAP_def;
val r = translate parse_number_def;
val r = Q.prove(
  `!x. parse_number_side x = T`,
  EVAL_TAC \\ Cases \\ EVAL_TAC
  \\ rw[IntProgTheory.fromchars_side_thm])
  |> update_precondition;
val r = translate parse_rational_def;
val r = translate parse_quota_def;
val r = translate parse_seats_def;
val r = translate t_cand_list_def;
val r = translate cand_list_def;
val r = translate parse_rest_def;
val r = translate parse_candidates_def;
val r = translate process_chunk_def;
val r = translate split_it_into_pair_def;
val r = translate parse_pair_end_def;
val r = translate parse_pair_t_def;
val r = translate parse_pair_def;
val r = translate parse_first_part_def;
val r = translate parse_second_t_def;
val r = translate parse_second_part_def;
val r = translate parse_third_t_def;
val r = translate parse_third_part_def;
val r = translate parse_whole_line_def;
val r = translate parse_judgement_def;

val _ = export_theory();
