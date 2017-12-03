open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     check_countProgTheory check_countCompileTheory

val _ = new_theory"check_countProof";

val check_count_io_events_def = new_specification("check_count_io_events_def",
  ["check_count_io_events","check_count_fs"],
  check_count_correct |> Q.GENL[`init_out`,`cls`,`fs`] |> Q.SPEC`""`
  |> SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM,RIGHT_EXISTS_AND_THM,APPEND]);

val (check_count_sem,check_count_output) = check_count_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR
val (check_count_not_fail,check_count_sem_sing) =
  MATCH_MP semantics_prog_Terminate_not_Fail check_count_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct check_count_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP check_count_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[check_count_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH x64_machine_config_ok)(UNDISCH x64_init_ok))
  |> DISCH(#1(dest_imp(concl x64_init_ok)))
  |> REWRITE_RULE[AND_IMP_INTRO]

val check_count_compiled_thm =
  CONJ compile_correct_applied check_count_output
  |> DISCH_ALL
  |> curry save_thm "check_count_compiled_thm";

val _ = export_theory();
