open preamble basis ParserTheory CheckerProgTheory

val _ = new_theory"ParserProg";

val _ = translation_extends"CheckerProg"

val r = translate parse_quota_def;
val r = translate parse_seats_def;
val r = translate parse_candidates_def;
val r = translate parse_judgement_def;

val _ = export_theory();
