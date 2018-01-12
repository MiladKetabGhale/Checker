open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     check_countProgTheory check_countCompileTheory

val _ = new_theory"check_countProof";

val check_count_io_events_def = new_specification("check_count_io_events_def",
  ["check_count_io_events","check_count_fs"],
  check_count_correct |> Q.GENL[`init_out`,`cl`,`fs`] |> Q.SPEC`strlit""`
  |> SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM,mlstringTheory.strcat_nil]);

val (check_count_sem,check_count_output) = check_count_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR
val (check_count_not_fail,check_count_sem_sing) =
  MATCH_MP semantics_prog_Terminate_not_Fail check_count_sem |> CONJ_PAIR

val check_count_compiled_def = Define `
  check_count_compiled = (code,data,config)`;

(* TODO: these are duplicated from wordfreqProof -- they should be elsewhere *)
val wfFS_def = Define `
  wfFS fs <=> fsFFIProps$wfFS fs ∧ STD_streams fs ∧ stdout fs (strlit "")`;

val x64_installed_def = Define `
  x64_installed (c,d,conf) ffi mc ms <=>
    is_x64_machine_config mc ∧
    backendProof$installed c d conf.ffi_names ffi
      (heap_regs x64_backend_config.stack_conf.reg_names) mc ms`
(* -- *)

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

val check_count_compiled_thm = Q.store_thm("check_count_compiled_thm",
  `wfcl cl ∧ check_countProof$wfFS fs ∧
   x64_installed check_count_compiled (basis_ffi cl fs) mc ms
   ⇒
   ∃io_events fs'.
   machine_sem mc (basis_ffi cl fs) ms ⊆
   extend_with_resource_limit {Terminate Success io_events} ∧
   extract_fs fs io_events = SOME fs' ∧
   (stdout fs' (strlit "Certificate OK\n") ⇔
    Check_Certificate (lines_of (implode (get_stdin fs))))`,
  simp[wfFS_def,CONJ_ASSOC]
  \\ simp[Once (GSYM AND_IMP_INTRO)]
  \\ simp[GSYM CONJ_ASSOC]
  \\ disch_then assume_tac
  \\ simp[x64_installed_def,check_count_compiled_def]
  \\ disch_then assume_tac
  \\ qmatch_asmsub_rename_tac`basis_ffi cl`
  \\ assume_tac (UNDISCH compile_correct_applied)
  \\ asm_exists_tac
  \\ simp[check_count_output]
  \\ `∃inp pos. stdin fs inp pos`
  by (
    fs[TextIOProofTheory.stdin_def,
       fsFFIPropsTheory.STD_streams_def,
       fsFFIPropsTheory.wfFS_def]
    \\ last_assum(qspecl_then[`0`,`inp`]mp_tac)
    \\ simp_tac std_ss [] \\ strip_tac
    \\ imp_res_tac ALOOKUP_MEM
    \\ last_x_assum(qspec_then`0`mp_tac)
    \\ simp[MEM_MAP,EXISTS_PROD]
    \\ Cases_on`ALOOKUP fs.files (IOStream (strlit"stdin"))` \\ fs[]
    \\ fs[ALOOKUP_FAILS]
    \\ metis_tac[] )
  \\ simp[UNDISCH (GSYM TextIOProofTheory.linesFD_splitlines_get_stdin)]
  \\ simp[fsFFIPropsTheory.lines_of_def,MAP_MAP_o,o_DEF,mlstringTheory.strcat_thm]);

val _ = export_theory();
