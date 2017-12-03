open preamble compilationLib MainProgTheory

val _ = new_theory"MainCompile";

val main_compiled = save_thm("main_compiled",
  compile_x64 1000 1000 "check_count" main_prog_def);

val _ = export_theory();
