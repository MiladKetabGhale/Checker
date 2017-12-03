open preamble compilationLib check_countProgTheory

val _ = new_theory"check_countCompile";

val check_count_compiled = save_thm("check_count_compiled",
  compile_x64 1000 1000 "check_count" check_count_prog_def);

val _ = export_theory();
