structure ppLib = struct

open preamble check_countProofTheory

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

val _ = max_print_depth := ~1;

val _ = overload_on("stdFS",``STD_streams``);
val _ = overload_on("x64_regs",``heap_regs x64_backend_config.stack_conf.reg_names``);

val _ = overload_on("the",``THE``);
val _ = overload_on("None",``NONE``);
val _ = overload_on("Some",``SOME``);
val _ = overload_on("option_choice",``OPTION_CHOICE``);
val _ = overload_on("mapm",``OPT_MMAP``);

val _ = overload_on("fst",``FST``);
val _ = overload_on("snd",``SND``);

val _ = overload_on("true",``T``);
val _ = overload_on("false",``F``);

val _ = overload_on("distinct",``ALL_DISTINCT``);
val _ = overload_on("rev",``REVERSE``);
val _ = overload_on("sorted",``SORTED``);
val _ = overload_on("flat",``FLAT``);
val _ = overload_on("map",``MAP``);
val _ = overload_on("length",``LENGTH``);
val _ = overload_on("filter",``FILTER``);
val _ = overload_on("foldl",``FOLDL``);
val _ = overload_on("assoc",``ALOOKUP``);
val _ = overload_on("drop",``DROP``);
val _ = overload_on("take",``TAKE``);
val _ = overload_on("last",``LAST``);
val _ = overload_on("update",``LUPDATE``);
val _ = overload_on("null",``NULL``);
val _ = overload_on("hd",``HD``);
val _ = overload_on("tl",``TL``);
val _ = overload_on("front",``FRONT``);
val _ = overload_on("zip",``ZIP``);
val _ = overload_on("pairwise",``LIST_REL``);
val _ = overload_on("split",``SPLITP``);
val _ = overload_on("LaTeXNIL",``[]``);

end
