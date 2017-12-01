open preamble basis CheckerTheory ParserProgTheory

val _ = new_theory"MainProg";

val _ = translation_extends"ParserProg";

(* TODO: move to HOL and CakeML repos *)

val LRC_APPEND = Q.store_thm("LRC_APPEND",
  `∀l1 l2 x y.
   LRC R (l1 ++ l2) x y ⇔
   ∃z. LRC R l1 x z ∧ LRC R l2 z y`,
  Induct \\ rw[LRC_def] \\ metis_tac[])

val LRC_inv = Q.store_thm("LRC_inv",
  `∀ls x y.
   LRC (inv R) ls x y ⇔
   case ls of [] => x = y
   | (h::t) => x = h ∧ LRC R (y::REVERSE t) y x`,
  Induct \\ rw[LRC_def]
  \\ CASE_TAC \\ fs[LRC_def,inv_DEF,LRC_APPEND]
  \\ metis_tac[]);

val option_case_eq = prove_case_eq_thm{nchotomy=option_nchotomy,case_def=option_case_def};
val list_case_eq = prove_case_eq_thm{nchotomy=list_nchotomy,case_def=list_case_def};

val lineForwardFD_forwardFD = Q.store_thm("lineForwardFD_forwardFD",
  `∀fs fd. ∃n. lineForwardFD fs fd = forwardFD fs fd n`,
  rw[forwardFD_def,lineForwardFD_def]
  \\ CASE_TAC
  >- (
    qexists_tac`0`
    \\ simp[IO_fs_component_equality]
    \\ match_mp_tac (GSYM ALIST_FUPDKEY_unchanged)
    \\ simp[FORALL_PROD] )
  \\ CASE_TAC
  \\ pairarg_tac \\ fs[]
  \\ rw[]
  >- metis_tac[]
  >- metis_tac[]
  >- (
    qexists_tac`0`
    \\ simp[IO_fs_component_equality]
    \\ match_mp_tac (GSYM ALIST_FUPDKEY_unchanged)
    \\ simp[FORALL_PROD] ));

val stdin_forwardFD = Q.store_thm("stdin_forwardFD",
  `stdin fs inp pos ⇒
   stdin (forwardFD fs fd n) inp (if fd = 0 then pos+n else pos)`,
  rw[stdin_def,forwardFD_def]
  \\ simp[ALIST_FUPDKEY_ALOOKUP]);

val stdin_get_stdin = Q.store_thm("stdin_get_stdin",
  `stdin fs inp pos ⇒ get_stdin fs = DROP pos inp`,
  rw[get_stdin_def]
  \\ SELECT_ELIM_TAC
  \\ rw[EXISTS_PROD,FORALL_PROD]
  >- metis_tac[]
  \\ pairarg_tac \\ fs[]
  \\ imp_res_tac stdin_11 \\ fs[]);

val get_stdin_forwardFD = Q.store_thm("get_stdin_forwardFD",
  `stdin fs inp pos ⇒
   get_stdin (forwardFD fs fd n) =
   if fd = 0 then
     DROP n (get_stdin fs)
   else get_stdin fs`,
  strip_tac
  \\ imp_res_tac stdin_get_stdin
  \\ imp_res_tac stdin_forwardFD
  \\ first_x_assum(qspecl_then[`n`,`fd`]mp_tac)
  \\ strip_tac
  \\ simp[DROP_DROP_T]
  \\ imp_res_tac stdin_get_stdin
  \\ rw[]);

(* -- *)

val malformed_line_msg_def = Define`
  malformed_line_msg (i:int) = concat[strlit"Malformed judgement on line ";toString i;strlit"\n"]`;
val invalid_step_msg_def = Define`
  invalid_step_msg (i:int) = concat[strlit"Invalid step on line ";toString i;strlit"\n"]`;

val loop_def = Define`
  loop params i j1 j0 ls =
   if Valid_Step params j0 j1 then
     case ls of
     | [] => if Initial_Judgement_dec (SND(SND params)) j0
             then NONE
             else SOME (strlit"Initial judgement malformed\n")
     | (line::ls) =>
        case parse_judgement line of
        | NONE => SOME (malformed_line_msg i)
        | SOME j => loop params (i+1) j0 j ls
   else SOME (invalid_step_msg i)`;

val loop_ind = theorem"loop_ind";

val loop_NONE = Q.store_thm("loop_NONE",
  `∀params i j1 j0 js.
   loop params i j1 j0 js = NONE ⇔
     EVERY (IS_SOME o parse_judgement) js ∧
     LRC (inv (Valid_Step params))
       (FRONT (j1::j0::(MAP (THE o parse_judgement) js))) j1 (LAST (j1::j0::(MAP (THE o parse_judgement) js))) ∧
     Initial_Judgement_dec (SND(SND params)) (LAST (j1::j0::(MAP (THE o parse_judgement) js)))`,
  recInduct loop_ind \\ rw[]
  \\ Cases_on`ls` >- ( fs[Once loop_def,bool_case_eq,LRC_def,inv_DEF] )
  \\ fs[LRC_def,PULL_EXISTS,inv_DEF]
  \\ Cases_on`parse_judgement h` \\ fs[] >- (simp[Once loop_def] \\ rw[])
  \\ simp[Once loop_def,bool_case_eq]
  \\ Cases_on`Valid_Step params j0 j1` \\ fs[]);

val loop_thm = Q.store_thm("loop_thm",
  `loop params i (Final w) j0 js = NONE ⇔
   EVERY (IS_SOME o parse_judgement) js ∧
   Check_Parsed_Certificate params (REVERSE ((Final w)::j0::(MAP (THE o parse_judgement) js)))`,
  rw[loop_NONE,Check_Parsed_Certificate_LRC,LRC_def,PULL_EXISTS,inv_DEF]
  \\ Cases_on`REVERSE (MAP (THE o parse_judgement) js)` \\ fs[LRC_def]
  \\ fs[SWAP_REVERSE_SYM]
  \\ fs[FRONT_DEF,FRONT_APPEND,LAST_DEF,LRC_APPEND,PULL_EXISTS,LRC_def,inv_DEF]
  \\ simp[LRC_inv,LRC_def]
  \\ CASE_TAC \\ fs[LRC_def,PULL_EXISTS] \\ rw[]
  >- metis_tac[]
  \\ fs[SWAP_REVERSE_SYM,LRC_APPEND,PULL_EXISTS,LRC_def]
  \\ metis_tac[]);

val r = translate malformed_line_msg_def;
val r = translate invalid_step_msg_def;

val loop = process_topdecs`
  fun loop params i j1 j0 =
    if valid_step params j0 j1 then
      case TextIO.inputLine TextIO.stdIn of
        NONE =>
          if initial_judgement_dec (snd (snd params)) j0 then
            TextIO.print "Certificate OK\n"
          else
            TextIO.output TextIO.stdErr "Initial judgement malformed\n"
      | SOME line =>
      case parse_judgement line of
        NONE => TextIO.output TextIO.stdErr (malformed_line_msg i)
      | SOME j => loop params (i+1) j0 j
    else TextIO.output TextIO.stdErr (invalid_step_msg i)`;

val _ = append_prog loop;

val _ = overload_on("PARAMS_TYPE",
  ``(PAIR_TYPE RAT_TYPE
         (PAIR_TYPE NUM (LIST_TYPE CHECKERSPEC_CAND_TYPE)))``);

val loop_spec = Q.store_thm("loop_spec",
  `∀i iv j1 j1v j0 j0v fs.
   PARAMS_TYPE params pv ∧
   INT i iv ∧
   CHECKERSPEC_JUDGEMENT_TYPE j1 j1v ∧
   CHECKERSPEC_JUDGEMENT_TYPE j0 j0v
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"loop"(get_ml_prog_state()))
     [pv;iv;j1v;j0v]
     (STDIO fs)
     (POSTv uv. &UNIT_TYPE () uv *
                case loop params i j1 j0 (MAP (λl. implode(l++"\n")) (splitlines (get_stdin fs))) of
                | NONE => (STDIO (add_stdout (fastForwardFD fs 0) "Certificate OK\n"))
                | SOME err => (SEP_EXISTS n. STDIO (add_stderr (forwardFD fs 0 n) (explode err))))`,
  Induct_on`splitlines (get_stdin fs)` \\ rw[]
  \\ qpat_x_assum`_ = splitlines _`(assume_tac o SYM) \\ fs[]
  \\ simp[Once loop_def]
  (* base case: no more lines left on stdin *)
  >- (
    (* set up the characteristic formula (used to prove an "app" goal) *)
    xcf "loop" (get_ml_prog_state())
    \\ reverse(Cases_on`STD_streams fs`) >- (simp[STDIO_def] \\ xpull)
    \\ xlet_auto >- xsimpl
    \\ reverse xif
    >- (
      xlet_auto >- xsimpl
      \\ xapp_spec output_STDIO_spec
      \\ xsimpl
      \\ instantiate
      \\ imp_res_tac STD_streams_stderr
      \\ fs[stdo_def,get_file_content_def,PULL_EXISTS]
      \\ instantiate
      \\ simp[REWRITE_RULE[EVAL``stdErr``]stderr_v_thm]
      \\ xsimpl
      \\ simp[insert_atI_end]
      \\ simp[add_stdo_def] \\ rw[]
      \\ qexists_tac `0`
      \\ simp[forwardFD_0]
      \\ SELECT_ELIM_TAC
      \\ conj_tac >- metis_tac[STD_streams_stderr]
      \\ rw[]
      \\ fs[stdo_def]
      \\ simp[up_stdo_def,LENGTH_explode]
      \\ xsimpl )
    \\ reverse(Cases_on `∃inp pos. stdin fs inp pos`)
    >- ( (* TODO: move this reasoning out into a separate theorem *)
      fs[stdin_def,STDIO_def,IOFS_def]
      \\ xpull
      \\ fs[wfFS_def,STD_streams_def]
      \\ `F` suffices_by rw[]
      \\ last_assum(qspecl_then[`0`,`inp`]mp_tac)
      \\ simp_tac std_ss [] \\ strip_tac
      \\ fs[]
      \\ imp_res_tac ALOOKUP_MEM
      \\ first_x_assum(qspec_then`0`mp_tac)
      \\ simp[MEM_MAP,EXISTS_PROD]
      \\ Cases_on`ALOOKUP fs.files (IOStream (strlit"stdin"))` \\ fs[]
      \\ fs[ALOOKUP_FAILS]
      \\ metis_tac[] )
    \\ qhdtm_x_assum`get_stdin`mp_tac
    \\ fs[get_stdin_def]
    \\ SELECT_ELIM_TAC
    \\ simp[EXISTS_PROD]
    \\ conj_tac >- metis_tac[]
    \\ gen_tac \\ strip_tac
    \\ pairarg_tac \\ fs[] \\ rveq
    \\ imp_res_tac stdin_11 \\ rveq
    \\ strip_tac
    \\ `get_file_content fs 0 = SOME (inp,pos)`
    by ( fs[stdin_def,get_file_content_def] )
    \\ `IS_SOME (get_file_content fs 0)` by metis_tac[IS_SOME_EXISTS]
    \\ xlet_auto
    >- ( xsimpl \\ metis_tac[stdin_v_thm,stdIn_def] )
    \\ xmatch
    \\ Cases_on`lineFD fs 0` \\ fs[OPTION_TYPE_def]
    >- (
      reverse conj_tac >- (EVAL_TAC \\ rw[])
      \\ xlet_auto >- xsimpl
      \\ xlet_auto >- xsimpl
      \\ xlet_auto >- xsimpl
      \\ xif
      >- (
        xapp
        \\ simp[lineFD_NONE_lineForwardFD_fastForwardFD]
        \\ rfs[lineFD_def,UNCURRY,DROP_LENGTH_TOO_LONG]
        \\ xsimpl \\ rw[]
        \\ CONV_TAC SWAP_EXISTS_CONV
        \\ qexists_tac`fastForwardFD fs 0`
        \\ xsimpl )
      \\ xapp_spec output_STDIO_spec
      \\ xsimpl
      \\ simp[lineFD_NONE_lineForwardFD_fastForwardFD]
      \\ rfs[lineFD_def,UNCURRY,DROP_LENGTH_TOO_LONG]
      \\ xsimpl \\ rw[]
      \\ `STD_streams (fastForwardFD fs 0)` by simp[STD_streams_fastForwardFD]
      \\ drule STD_streams_stderr \\ strip_tac
      \\ fs[stdo_def,get_file_content_def,PULL_EXISTS]
      \\ instantiate
      \\ simp[REWRITE_RULE[EVAL``stdErr``]stderr_v_thm]
      \\ xsimpl
      \\ simp[insert_atI_end]
      \\ simp[add_stdo_def]
      \\ DEP_REWRITE_TAC[fastForwardFD_0]
      \\ simp[get_file_content_def]
      \\ rw[]
      \\ qexists_tac `0`
      \\ simp[forwardFD_0]
      \\ SELECT_ELIM_TAC
      \\ conj_tac >- metis_tac[STD_streams_stderr]
      \\ rw[]
      \\ fs[stdo_def]
      \\ simp[up_stdo_def,LENGTH_explode]
      \\ xsimpl )
    \\ rfs[lineFD_def]
    \\ fs[DROP_NIL] )
  (* inductive case: read a line from stdin *)
  \\ xcf "loop" (get_ml_prog_state())
  \\ reverse(Cases_on`STD_streams fs`) >- (simp[STDIO_def] \\ xpull)
  \\ xlet_auto >- xsimpl
  \\ reverse xif
  >- (
    xlet_auto >- xsimpl
    \\ xapp_spec output_STDIO_spec
    \\ xsimpl
    \\ instantiate
    \\ imp_res_tac STD_streams_stderr
    \\ fs[stdo_def,get_file_content_def,PULL_EXISTS]
    \\ instantiate
    \\ simp[REWRITE_RULE[EVAL``stdErr``]stderr_v_thm]
    \\ xsimpl
    \\ simp[insert_atI_end]
    \\ simp[add_stdo_def] \\ rw[]
    \\ qexists_tac `0`
    \\ simp[forwardFD_0]
    \\ SELECT_ELIM_TAC
    \\ conj_tac >- metis_tac[STD_streams_stderr]
    \\ rw[]
    \\ fs[stdo_def]
    \\ simp[up_stdo_def,LENGTH_explode]
    \\ xsimpl )
  \\ reverse(Cases_on `∃inp pos. stdin fs inp pos`)
  >- ( (* TODO: move this reasoning out into a separate theorem *)
    fs[stdin_def,STDIO_def,IOFS_def]
    \\ xpull
    \\ fs[wfFS_def,STD_streams_def]
    \\ `F` suffices_by rw[]
    \\ last_assum(qspecl_then[`0`,`inp`]mp_tac)
    \\ simp_tac std_ss [] \\ strip_tac
    \\ fs[]
    \\ imp_res_tac ALOOKUP_MEM
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[MEM_MAP,EXISTS_PROD]
    \\ Cases_on`ALOOKUP fs.files (IOStream (strlit"stdin"))` \\ fs[]
    \\ fs[ALOOKUP_FAILS]
    \\ metis_tac[] )
  \\ qpat_x_assum`splitlines (get_stdin fs) = _`mp_tac
  \\ simp[get_stdin_def]
  \\ SELECT_ELIM_TAC
  \\ simp[EXISTS_PROD,FORALL_PROD] \\ rw[]
  \\ imp_res_tac stdin_11 \\ rveq
  \\ imp_res_tac splitlines_CONS_FST_SPLITP
  \\ imp_res_tac splitlines_next
  \\ qmatch_assum_rename_tac`stdin fs inp pos`
  \\ `get_file_content fs 0 = SOME (inp,pos)`
  by ( fs[stdin_def,get_file_content_def] )
  \\ `IS_SOME (get_file_content fs 0)` by metis_tac[IS_SOME_EXISTS]
  \\ xlet_auto
  >- ( xsimpl \\ metis_tac[stdin_v_thm,stdIn_def] )
  \\ xmatch
  \\ Cases_on`lineFD fs 0` \\ fs[OPTION_TYPE_def]
  >- (
    fs[GSYM linesFD_nil_lineFD_NONE]
    \\ rfs[linesFD_def] )
  \\ Cases_on`linesFD fs 0` \\ fs[linesFD_nil_lineFD_NONE]
  \\ imp_res_tac linesFD_cons_imp
  \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
  \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
  \\ xlet_auto >- xsimpl
  \\ xmatch
  \\ Cases_on`parse_judgement (implode x)` \\ fs[OPTION_TYPE_def]
  >- (
    reverse conj_tac >- (EVAL_TAC \\ rw[])
    \\ xlet_auto >- xsimpl
    \\ xapp_spec output_STDIO_spec
    \\ fs[] \\ rveq
    \\ `STD_streams (lineForwardFD fs 0)` by simp[STD_streams_lineForwardFD]
    \\ drule STD_streams_stderr \\ strip_tac
    \\ fs[stdo_def,get_file_content_def,PULL_EXISTS]
    \\ instantiate
    \\ simp[REWRITE_RULE[EVAL``stdErr``]stderr_v_thm]
    \\ xsimpl
    \\ simp[insert_atI_end]
    \\ rfs[lineFD_def,get_file_content_def,UNCURRY]
    \\ xsimpl
    \\ qspecl_then[`fs`,`0`]strip_assume_tac lineForwardFD_forwardFD
    \\ qexists_tac`n`
    \\ simp[add_stdo_def]
    \\ SELECT_ELIM_TAC
    \\ conj_tac >- metis_tac[STD_streams_stderr,STD_streams_forwardFD]
    \\ rw[]
    \\ fs[stdo_def]
    \\ simp[up_stdo_def,LENGTH_explode]
    \\ xsimpl )
  \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
  \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
  \\ xlet_auto >- xsimpl
  \\ xapp
  \\ last_x_assum kall_tac
  \\ instantiate
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac`lineForwardFD fs 0`
  \\ rveq \\ fs[] \\ xsimpl
  \\ qmatch_goalsub_abbrev_tac`splitlines s1 = splitlines s2`
  \\ `s1 = s2`
  by (
    simp[Abbr`s1`,Abbr`s2`]
    \\ simp[lineForwardFD_def,UNCURRY]
    \\ IF_CASES_TAC \\ fs[DROP_LENGTH_TOO_LONG]
    \\ IF_CASES_TAC
    >- (
      fs[NULL_EQ,SPLITP_NIL_SND_EVERY,SND_EQ_EQUIV]
      \\ fs[o_DEF]
      \\ fs[SPLITP_EVERY,DROP_LENGTH_TOO_LONG]
      \\ DEP_REWRITE_TAC[get_stdin_forwardFD]
      \\ imp_res_tac stdin_get_stdin
      \\ simp[DROP_DROP_T,DROP_NIL] )
    \\ DEP_REWRITE_TAC[get_stdin_forwardFD]
    \\ simp[ADD1]
    \\ imp_res_tac stdin_get_stdin
    \\ simp[] )
  \\ simp[Abbr`s1`,Abbr`s2`] \\ fs[]
  \\ rfs[lineFD_def,UNCURRY]
  \\ CASE_TAC \\ xsimpl
  \\ qspecl_then[`fs`,`0`]strip_assume_tac lineForwardFD_forwardFD
  \\ qx_gen_tac`m`
  \\ qexists_tac`n+m`
  \\ simp[forwardFD_o]
  \\ xsimpl);

val main = process_topdecs`
  fun main u =
    case TextIO.inputLine TextIO.stdIn of
      NONE => TextIO.output TextIO.stdErr "No quota line\n"
    | SOME line =>
    case parse_quota line of
      NONE => TextIO.output TextIO.stdErr "Quota line malformed\n"
    | SOME quota =>
    case TextIO.inputLine TextIO.stdIn of
      NONE => TextIO.output TextIO.stdErr "No seats line\n"
    | SOME line =>
    case parse_seats line of
      NONE => TextIO.output TextIO.stdErr "Seats line malformed\n"
    | SOME seats =>
    case TextIO.inputLine TextIO.stdIn of
      NONE => TextIO.output TextIO.stdErr "No candidates line\n"
    | SOME line =>
    case parse_candidates line of
      NONE => TextIO.output TextIO.stdErr "Candidates line malformed\n"
    | SOME candidates =>
    case TextIO.inputLine TextIO.stdIn of
      NONE => TextIO.output TextIO.stdErr "No final judgement line\n"
    | SOME line =>
    case parse_candidates line of
      NONE => TextIO.output TextIO.stdErr "Final judgement line malformed\n"
    | SOME winners =>
    case TextIO.inputLine TextIO.stdIn of
      NONE => TextIO.output TextIO.stdErr "No penultimate judgement line\n"
    | SOME line =>
    case parse_judgement line of
      NONE => TextIO.output TextIO.stdErr "Penultimate judgement line malformed\n"
    | SOME j0 => loop (quota,seats,candidates) 6 (Final winners) j0`;

val _ = append_prog main;

val _ = export_theory();
