open preamble basis CheckerTheory ParserProgTheory

val _ = new_theory"MainProg";

val _ = translation_extends"ParserProg";

(* TODO: move to HOL *)

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

val DROP_EQ_CONS_IMP = Q.store_thm("DROP_EQ_CONS_IMP",
  `DROP n ls = x::xs ⇒ DROP (n+1) ls = xs`,
  Cases_on`ls` \\ rw[]
  \\ Cases_on`n` \\ fs[]
  \\ simp[ADD1]
  \\ ONCE_REWRITE_TAC[ADD_COMM]
  \\ simp[GSYM DROP_DROP_T]);

val OPT_MMAP_EQ_SOME = Q.store_thm("OPT_MMAP_EQ_SOME",
  `∀xs ys.
   OPT_MMAP f xs = SOME ys ⇔
   EVERY (IS_SOME o f) xs ∧
   ys = MAP (THE o f) xs`,
  Induct \\ rw[OPT_MMAP_def,IS_SOME_EXISTS,PULL_EXISTS]
  \\ metis_tac[THE_DEF]);

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
             else SOME (strlit"Malformed initial judgement\n")
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
            TextIO.output TextIO.stdErr "Malformed initial judgement\n"
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
    >- ( (* TODO: Move this reasoning out into a separate theorem. Or just use linesFD instead. *)
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

val Check_Certificate_def = Define`
  Check_Certificate lines =
    case lines of
    | (quota_line::seats_line::candidates_line::winners_line::jlines) =>
      (case (parse_quota quota_line,
             parse_seats seats_line,
             parse_candidates candidates_line,
             parse_candidates winners_line,
             OPT_MMAP parse_judgement jlines) of
       (SOME quota, SOME seats, SOME candidates, SOME winners, SOME judgements) =>
         Check_Parsed_Certificate (quota,seats,candidates)
           (REVERSE (Final winners::judgements))
       | _ => F)
    | _ => F`;

val line4_def = Define`
  line4 quota seats candidates winners ls =
    case OPT_MMAP parse_judgement ls of
    | NONE => F
    | SOME judgements =>
      Check_Parsed_Certificate (quota,seats,candidates)
        (REVERSE (Final winners::judgements))`;

val line3_def = Define`
  line3 quota seats candidates ls =
    case ls of
    | [] => F
    | winners_line::ls =>
      (case parse_candidates winners_line of
       | NONE => F
       | SOME winners => line4 quota seats candidates winners ls)`;

val line2_def = Define`
  line2 quota seats ls =
    case ls of
    | [] => F
    | candidates_line::ls =>
      (case parse_candidates candidates_line of
       | NONE => F
       | SOME candidates => line3 quota seats candidates ls)`;

val line1_def = Define`
  line1 quota ls =
    case ls of
    | [] => F
    | seats_line::ls =>
      (case parse_seats seats_line of
       | NONE => F
       | SOME seats => line2 quota seats ls)`;

val missing_msg_def = Define`
  missing_msg name = concat[strlit"No ";name;strlit" line\n"]`;
val malformed_msg_def = Define`
  malformed_msg name = concat[strlit"Malformed ";name;strlit" line\n"]`;

val r = translate missing_msg_def;
val r = translate malformed_msg_def;

val test_line = process_topdecs`
  fun test_line parse name k =
    case TextIO.inputLine TextIO.stdIn of
      NONE => TextIO.output TextIO.stdErr (missing_msg name)
    | SOME line =>
    case parse line of
      NONE => TextIO.output TextIO.stdErr (malformed_msg name)
    | SOME x => k x`;

val _ = append_prog test_line;

val test_line_spec = Q.store_thm("test_line_spec",
  `∀A parser name.
   (STRING_TYPE --> OPTION_TYPE A) parser parserv ∧
   STRING_TYPE name namev ∧
   (∀x xv. A x xv ⇒ app p kv [xv] (STDIO (lineForwardFD fs 0)) (POSTv v. &UNIT_TYPE () v * Q x))
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"test_line"(get_ml_prog_state()))
   [parserv;namev;kv]
     (STDIO fs)
     (POSTv v. &UNIT_TYPE () v *
       case linesFD fs 0 of
       | [] => STDIO (add_stderr (lineForwardFD fs 0) (explode(missing_msg name)))
       | (line::_) =>
         (case parser (implode line) of
          | NONE => STDIO (add_stderr (lineForwardFD fs 0) (explode(malformed_msg name)))
          | SOME x => Q x))`,
  xcf "test_line" (get_ml_prog_state())
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
    \\ last_x_assum(qspec_then`0`mp_tac)
    \\ simp[MEM_MAP,EXISTS_PROD]
    \\ Cases_on`ALOOKUP fs.files (IOStream (strlit"stdin"))` \\ fs[]
    \\ fs[ALOOKUP_FAILS]
    \\ metis_tac[] )
  \\ reverse(Cases_on`STD_streams fs`) >- (simp[STDIO_def] \\ xpull)
  \\ fs[]
  \\ `get_file_content fs 0 = SOME (inp,pos)` by fs[stdin_def,get_file_content_def]
  \\ `IS_SOME (get_file_content fs 0)` by metis_tac[IS_SOME_EXISTS]
  \\ xlet_auto >- ( xsimpl \\ metis_tac[stdin_v_thm,stdIn_def] )
  \\ xmatch
  \\ Cases_on`lineFD fs 0` \\ fs[OPTION_TYPE_def]
  >- (
    reverse conj_tac >- (EVAL_TAC \\ rw[])
    \\ fs[GSYM linesFD_nil_lineFD_NONE]
    \\ xlet_auto >- xsimpl
    \\ xapp_spec output_STDIO_spec
    \\ xsimpl
    \\ `STD_streams (lineForwardFD fs 0)` by simp[STD_streams_lineForwardFD]
    \\ drule STD_streams_stderr \\ strip_tac
    \\ first_assum mp_tac
    \\ simp_tac(srw_ss())[stdo_def,get_file_content_def,PULL_EXISTS]
    \\ strip_tac
    \\ instantiate
    \\ simp[REWRITE_RULE[EVAL``stdErr``]stderr_v_thm]
    \\ xsimpl
    \\ simp[insert_atI_end]
    \\ simp[add_stdo_def] \\ rw[]
    \\ SELECT_ELIM_TAC
    \\ conj_tac >- metis_tac[]
    \\ rw[] \\ fs[]
    \\ imp_res_tac stdo_UNICITY_R \\ rveq
    \\ simp[up_stdo_def,LENGTH_explode]
    \\ xsimpl )
  \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
  \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
  \\ qmatch_goalsub_abbrev_tac`STDIO fs1`
  \\ `STD_streams fs1` by simp[STD_streams_lineForwardFD,Abbr`fs1`]
  \\ CASE_TAC \\ fs[linesFD_nil_lineFD_NONE]
  \\ imp_res_tac linesFD_cons_imp \\ fs[] \\ rveq
  \\ xlet_auto >- xsimpl
  \\ xmatch
  \\ qmatch_asmsub_rename_tac`parser (implode ln)`
  \\ Cases_on`parser (implode ln)` \\ fs[OPTION_TYPE_def]
  >- (
    reverse conj_tac >- (EVAL_TAC \\ rw[])
    \\ xlet_auto >- xsimpl
    \\ xapp_spec output_STDIO_spec
    \\ drule STD_streams_stderr \\ strip_tac
    \\ first_assum mp_tac
    \\ simp_tac(srw_ss())[stdo_def,get_file_content_def,PULL_EXISTS]
    \\ strip_tac
    \\ instantiate
    \\ simp[REWRITE_RULE[EVAL``stdErr``]stderr_v_thm]
    \\ xsimpl
    \\ simp[insert_atI_end]
    \\ simp[add_stdo_def]
    \\ SELECT_ELIM_TAC
    \\ conj_tac >- metis_tac[]
    \\ rw[]
    \\ imp_res_tac stdo_UNICITY_R \\ rw[]
    \\ simp[up_stdo_def,LENGTH_explode]
    \\ xsimpl )
  \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
  \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
  \\ xapp
  \\ xsimpl);

val main = process_topdecs`
  fun main u =
    test_line parse_quota "quota" (fn quota =>
    test_line parse_seats "seats" (fn seats =>
    test_line parse_candidates "candidates" (fn candidates =>
    test_line parse_candidates "final judgement" (fn winners =>
    test_line parse_judgement "penultimate judgement" (fn j0 =>
      loop (quota,(seats,candidates)) 6 (Final winners) j0)))))`;

val _ = append_prog main;

val main_spec = Q.store_thm("main_spec",
  `app (p:'ffi ffi_proj) ^(fetch_v"main"(get_ml_prog_state())) [Conv NONE []]
     (STDIO fs)
     (POSTv uv. &UNIT_TYPE () uv *
                if Check_Certificate (MAP implode (linesFD fs 0))
                then STDIO (add_stdout (fastForwardFD fs 0) "Certificate OK\n")
                else SEP_EXISTS n err. STDIO (add_stderr (forwardFD fs 0 n) err))`,
  xcf "main" (get_ml_prog_state())
  \\ reverse(Cases_on `∃inp pos. stdin fs inp pos`)
  >- ( (* TODO: move this reasoning out into a separate theorem *)
    fs[stdin_def,STDIO_def,IOFS_def]
    \\ xpull_core
    \\ conj_tac >- (
      REWRITE_TAC cf_defs
      \\ CONV_TAC (DEPTH_CONV BETA_CONV)
      \\ REWRITE_TAC[local_is_local] )
    \\ rpt strip_tac
    \\ `F` suffices_by rw[]
    \\ fs[wfFS_def,STD_streams_def]
    \\ last_assum(qspecl_then[`0`,`inp`]mp_tac)
    \\ simp_tac std_ss [] \\ strip_tac
    \\ fs[]
    \\ imp_res_tac ALOOKUP_MEM
    \\ last_x_assum(qspec_then`0`mp_tac)
    \\ simp[MEM_MAP,EXISTS_PROD]
    \\ Cases_on`ALOOKUP fs.files (IOStream (strlit"stdin"))` \\ fs[]
    \\ fs[ALOOKUP_FAILS]
    \\ metis_tac[] )
  \\ xfun`quota_fun`
  \\ xapp_spec (Q.ISPECL[`RAT_TYPE`,`parse_quota`]test_line_spec)
  \\ simp[STRING_TYPE_def,parse_quota_v_thm]
  \\ qexists_tac`emp`
  \\ xsimpl
  \\ qexists_tac`fs`
  \\ xsimpl
  \\ qmatch_goalsub_abbrev_tac`if _ then Qval else Qerr`
  \\ qexists_tac`λquota. if line1 quota (MAP implode (DROP 1 (linesFD fs 0))) then Qval else Qerr`
  \\ reverse conj_tac
  >- (
    CASE_TAC
    >- (
      fs[Check_Certificate_def,Abbr`Qerr`]
      \\ xsimpl
      \\ qspecl_then[`fs`,`0`]strip_assume_tac lineForwardFD_forwardFD
      \\ qmatch_goalsub_abbrev_tac`add_stderr _ err`
      \\ qexists_tac`n`
      \\ qexists_tac`err`
      \\ xsimpl )
    \\ CASE_TAC
    >- (
      fs[Check_Certificate_def,Abbr`Qerr`]
      \\ IF_CASES_TAC >- (every_case_tac \\ fs[])
      \\ xsimpl
      \\ qspecl_then[`fs`,`0`]strip_assume_tac lineForwardFD_forwardFD
      \\ qmatch_goalsub_abbrev_tac`add_stderr _ err`
      \\ qexists_tac`n`
      \\ qexists_tac`err`
      \\ xsimpl )
    \\ simp[line1_def]
    \\ CASE_TAC >- (fs[Check_Certificate_def] \\ xsimpl)
    \\ CASE_TAC >- (
      fs[Check_Certificate_def]
      \\ IF_CASES_TAC \\ xsimpl
      \\ every_case_tac \\ fs[] )
    \\ simp[line2_def]
    \\ CASE_TAC >- (fs[Check_Certificate_def] \\ xsimpl)
    \\ CASE_TAC >- (
      fs[Check_Certificate_def]
      \\ IF_CASES_TAC \\ xsimpl
      \\ every_case_tac \\ fs[] )
    \\ simp[line3_def]
    \\ CASE_TAC >- (fs[Check_Certificate_def] \\ xsimpl)
    \\ CASE_TAC >- (
      fs[Check_Certificate_def]
      \\ xsimpl )
    \\ simp[line4_def]
    \\ CASE_TAC >- (fs[Check_Certificate_def] \\ xsimpl)
    \\ CASE_TAC >- (
      fs[Check_Certificate_def]
      \\ xsimpl )
    \\ fs[Check_Certificate_def]
    \\ xsimpl )
  \\ qx_gen_tac`quota`
  \\ rpt strip_tac \\ fs[]
  \\ first_x_assum match_mp_tac
  \\ xfun`seats_fun`
  \\ xapp_spec (Q.ISPECL[`NUM`,`parse_seats`]test_line_spec)
  \\ simp[STRING_TYPE_def,parse_seats_v_thm]
  \\ qexists_tac`emp`
  \\ xsimpl
  \\ qexists_tac`lineForwardFD fs 0`
  \\ xsimpl
  \\ simp[linesFD_lineForwardFD]
  \\ qexists_tac`λseats. if line2 quota seats (MAP implode (DROP 2 (linesFD fs 0))) then Qval else Qerr`
  \\ reverse conj_tac
  >- (
    CASE_TAC
    >- (
      fs[line1_def,Abbr`Qerr`]
      \\ xsimpl
      \\ qspecl_then[`fs`,`0`](qx_choose_then`n1`strip_assume_tac) lineForwardFD_forwardFD
      \\ qspecl_then[`lineForwardFD fs 0`,`0`](qx_choose_then`n2`strip_assume_tac) lineForwardFD_forwardFD
      \\ qmatch_goalsub_abbrev_tac`add_stderr _ err`
      \\ qexists_tac`n1+n2`
      \\ qexists_tac`err`
      \\ simp[GSYM forwardFD_o]
      \\ xsimpl )
    \\ CASE_TAC
    >- (
      fs[line1_def,Abbr`Qerr`]
      \\ xsimpl
      \\ qspecl_then[`fs`,`0`](qx_choose_then`n1`strip_assume_tac) lineForwardFD_forwardFD
      \\ qspecl_then[`lineForwardFD fs 0`,`0`](qx_choose_then`n2`strip_assume_tac) lineForwardFD_forwardFD
      \\ qmatch_goalsub_abbrev_tac`add_stderr _ err`
      \\ qexists_tac`n1+n2`
      \\ qexists_tac`err`
      \\ simp[GSYM forwardFD_o]
      \\ xsimpl )
    \\ simp[line1_def]
    \\ Cases_on`linesFD fs 0` \\ fs[]
    \\ xsimpl )
  \\ qx_gen_tac`seats`
  \\ rpt strip_tac \\ fs[]
  \\ first_x_assum match_mp_tac
  \\ xfun`candidates_fun`
  \\ xapp_spec (Q.ISPECL[`LIST_TYPE CHECKERSPEC_CAND_TYPE`,`parse_candidates`]test_line_spec)
  \\ simp[STRING_TYPE_def,parse_candidates_v_thm]
  \\ qexists_tac`emp`
  \\ xsimpl
  \\ qexists_tac`lineForwardFD (lineForwardFD fs 0) 0`
  \\ xsimpl
  \\ simp[linesFD_lineForwardFD,DROP_DROP_T]
  \\ qexists_tac`λcandidates. if line3 quota seats candidates (MAP implode (DROP 3 (linesFD fs 0))) then Qval else Qerr`
  \\ reverse conj_tac
  >- (
    CASE_TAC
    >- (
      fs[line2_def,Abbr`Qerr`]
      \\ xsimpl
      \\ qspecl_then[`fs`,`0`](qx_choose_then`n1`strip_assume_tac) lineForwardFD_forwardFD
      \\ qspecl_then[`lineForwardFD fs 0`,`0`](qx_choose_then`n2`strip_assume_tac) lineForwardFD_forwardFD
      \\ qspecl_then[`lineForwardFD (lineForwardFD fs 0) 0`,`0`](qx_choose_then`n3`strip_assume_tac) lineForwardFD_forwardFD
      \\ qmatch_goalsub_abbrev_tac`add_stderr _ err`
      \\ qexists_tac`n1+n2+n3`
      \\ qexists_tac`err`
      \\ simp[GSYM forwardFD_o]
      \\ xsimpl )
    \\ CASE_TAC
    >- (
      fs[line2_def,Abbr`Qerr`]
      \\ xsimpl
      \\ qspecl_then[`fs`,`0`](qx_choose_then`n1`strip_assume_tac) lineForwardFD_forwardFD
      \\ qspecl_then[`lineForwardFD fs 0`,`0`](qx_choose_then`n2`strip_assume_tac) lineForwardFD_forwardFD
      \\ qspecl_then[`lineForwardFD (lineForwardFD fs 0) 0`,`0`](qx_choose_then`n3`strip_assume_tac) lineForwardFD_forwardFD
      \\ qmatch_goalsub_abbrev_tac`add_stderr _ err`
      \\ qexists_tac`n1+n2+n3`
      \\ qexists_tac`err`
      \\ simp[GSYM forwardFD_o]
      \\ xsimpl )
    \\ simp[line2_def]
    \\ imp_res_tac DROP_EQ_CONS_IMP \\ fs[]
    \\ xsimpl )
  \\ qx_gen_tac`candidates`
  \\ rpt strip_tac \\ fs[]
  \\ first_x_assum match_mp_tac
  \\ xfun`winners_fun`
  \\ xapp_spec (Q.ISPECL[`LIST_TYPE CHECKERSPEC_CAND_TYPE`,`parse_candidates`]test_line_spec)
  \\ simp[STRING_TYPE_def,parse_candidates_v_thm]
  \\ qexists_tac`emp`
  \\ xsimpl
  \\ qexists_tac`lineForwardFD (lineForwardFD (lineForwardFD fs 0) 0) 0`
  \\ xsimpl
  \\ simp[linesFD_lineForwardFD,DROP_DROP_T]
  \\ qexists_tac`λwinners. if line4 quota seats candidates winners (MAP implode (DROP 4 (linesFD fs 0))) then Qval else Qerr`
  \\ reverse conj_tac
  >- (
    CASE_TAC
    >- (
      fs[line3_def,Abbr`Qerr`]
      \\ xsimpl
      \\ qspecl_then[`fs`,`0`](qx_choose_then`n1`strip_assume_tac) lineForwardFD_forwardFD
      \\ qspecl_then[`lineForwardFD fs 0`,`0`](qx_choose_then`n2`strip_assume_tac) lineForwardFD_forwardFD
      \\ qspecl_then[`lineForwardFD (lineForwardFD fs 0) 0`,`0`](qx_choose_then`n3`strip_assume_tac) lineForwardFD_forwardFD
      \\ qspecl_then[`lineForwardFD (lineForwardFD (lineForwardFD fs 0) 0) 0`,`0`](qx_choose_then`n4`strip_assume_tac) lineForwardFD_forwardFD
      \\ qmatch_goalsub_abbrev_tac`add_stderr _ err`
      \\ qexists_tac`n1+n2+n3+n4`
      \\ qexists_tac`err`
      \\ simp[GSYM forwardFD_o]
      \\ xsimpl )
    \\ CASE_TAC
    >- (
      fs[line3_def,Abbr`Qerr`]
      \\ xsimpl
      \\ qspecl_then[`fs`,`0`](qx_choose_then`n1`strip_assume_tac) lineForwardFD_forwardFD
      \\ qspecl_then[`lineForwardFD fs 0`,`0`](qx_choose_then`n2`strip_assume_tac) lineForwardFD_forwardFD
      \\ qspecl_then[`lineForwardFD (lineForwardFD fs 0) 0`,`0`](qx_choose_then`n3`strip_assume_tac) lineForwardFD_forwardFD
      \\ qspecl_then[`lineForwardFD (lineForwardFD (lineForwardFD fs 0) 0) 0`,`0`](qx_choose_then`n4`strip_assume_tac) lineForwardFD_forwardFD
      \\ qmatch_goalsub_abbrev_tac`add_stderr _ err`
      \\ qexists_tac`n1+n2+n3+n4`
      \\ qexists_tac`err`
      \\ simp[GSYM forwardFD_o]
      \\ xsimpl )
    \\ simp[line3_def]
    \\ imp_res_tac DROP_EQ_CONS_IMP \\ fs[]
    \\ xsimpl )
  \\ qx_gen_tac`winners`
  \\ rpt strip_tac \\ fs[]
  \\ first_x_assum match_mp_tac
  \\ xfun`j_fun`
  \\ xapp_spec (Q.ISPECL[`CHECKERSPEC_JUDGEMENT_TYPE`,`parse_judgement`]test_line_spec)
  \\ simp[STRING_TYPE_def,parse_judgement_v_thm]
  \\ qexists_tac`emp`
  \\ xsimpl
  \\ qexists_tac`lineForwardFD (lineForwardFD (lineForwardFD (lineForwardFD fs 0) 0) 0) 0`
  \\ xsimpl
  \\ simp[linesFD_lineForwardFD,DROP_DROP_T]
  \\ qexists_tac`λj0.
      if loop (quota,seats,candidates) 6 (Final winners) j0 (MAP implode (DROP 5 (linesFD fs 0))) = NONE
      then Qval else Qerr`
  \\ reverse conj_tac
  >- (
    CASE_TAC
    >- (
      fs[line4_def,Abbr`Qerr`,OPT_MMAP_def,Check_Parsed_Certificate_def,Initial_Judgement_dec_def]
      \\ xsimpl
      \\ qspecl_then[`fs`,`0`](qx_choose_then`n1`strip_assume_tac) lineForwardFD_forwardFD
      \\ qspecl_then[`lineForwardFD fs 0`,`0`](qx_choose_then`n2`strip_assume_tac) lineForwardFD_forwardFD
      \\ qspecl_then[`lineForwardFD (lineForwardFD fs 0) 0`,`0`](qx_choose_then`n3`strip_assume_tac) lineForwardFD_forwardFD
      \\ qspecl_then[`lineForwardFD (lineForwardFD (lineForwardFD fs 0) 0) 0`,`0`](qx_choose_then`n4`strip_assume_tac) lineForwardFD_forwardFD
      \\ qspecl_then[`lineForwardFD (lineForwardFD (lineForwardFD (lineForwardFD fs 0) 0) 0) 0`,`0`](qx_choose_then`n5`strip_assume_tac) lineForwardFD_forwardFD
      \\ qmatch_goalsub_abbrev_tac`add_stderr _ err`
      \\ qexists_tac`n1+n2+n3+n4+n5`
      \\ qexists_tac`err`
      \\ simp[GSYM forwardFD_o]
      \\ xsimpl )
    \\ CASE_TAC
    >- (
      fs[line4_def,Abbr`Qerr`,OPT_MMAP_def]
      \\ xsimpl
      \\ qspecl_then[`fs`,`0`](qx_choose_then`n1`strip_assume_tac) lineForwardFD_forwardFD
      \\ qspecl_then[`lineForwardFD fs 0`,`0`](qx_choose_then`n2`strip_assume_tac) lineForwardFD_forwardFD
      \\ qspecl_then[`lineForwardFD (lineForwardFD fs 0) 0`,`0`](qx_choose_then`n3`strip_assume_tac) lineForwardFD_forwardFD
      \\ qspecl_then[`lineForwardFD (lineForwardFD (lineForwardFD fs 0) 0) 0`,`0`](qx_choose_then`n4`strip_assume_tac) lineForwardFD_forwardFD
      \\ qspecl_then[`lineForwardFD (lineForwardFD (lineForwardFD (lineForwardFD fs 0) 0) 0) 0`,`0`](qx_choose_then`n5`strip_assume_tac) lineForwardFD_forwardFD
      \\ qmatch_goalsub_abbrev_tac`add_stderr _ err`
      \\ qexists_tac`n1+n2+n3+n4+n5`
      \\ qexists_tac`err`
      \\ simp[GSYM forwardFD_o]
      \\ xsimpl )
    \\ simp[line4_def]
    \\ imp_res_tac DROP_EQ_CONS_IMP \\ fs[OPT_MMAP_def]
    \\ simp[loop_thm]
    \\ IF_CASES_TAC
    >- (
      Q.ISPEC_THEN`parse_judgement`mp_tac(Q.GEN`f` OPT_MMAP_EQ_SOME)
      \\ disch_then(qspec_then`MAP implode t`mp_tac)
      \\ simp[] \\ strip_tac
      \\ fsrw_tac[DNF_ss][EQ_IMP_THM] \\ xsimpl )
    \\ CASE_TAC >- xsimpl
    \\ pop_assum mp_tac \\ simp[]
    \\ simp_tac bool_ss [OPT_MMAP_EQ_SOME]
    \\ strip_tac
    \\ rveq
    \\ simp[]
    \\ full_simp_tac std_ss []
    \\ xsimpl )
  \\ qx_gen_tac`j0`
  \\ rpt strip_tac \\ fs[]
  \\ first_x_assum match_mp_tac
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xapp
  \\ instantiate
  \\ qexists_tac`emp`
  \\ qexists_tac`(quota,seats,candidates)`
  \\ qexists_tac`Final winners`
  \\ qmatch_goalsub_abbrev_tac`STDIO fsn`
  \\ qexists_tac`fsn`
  \\ xsimpl
  \\ conj_tac >- (EVAL_TAC \\ simp[])
  \\ conj_tac >- (simp[PAIR_TYPE_def])
  \\ simp[Abbr`Qerr`]
  \\ xsimpl
  \\ simp[GSYM (Q.ISPEC`implode`o_DEF),GSYM MAP_MAP_o]
  \\ `∃inp pos. stdin fsn inp pos` by metis_tac[stdin_forwardFD,lineForwardFD_forwardFD]
  \\ imp_res_tac linesFD_splitlines_get_stdin
  \\ simp[]
  \\ simp[Abbr`fsn`,linesFD_lineForwardFD,DROP_DROP_T]
  \\ qspecl_then[`fs`,`0`](qx_choose_then`n1`strip_assume_tac) lineForwardFD_forwardFD
  \\ qspecl_then[`lineForwardFD fs 0`,`0`](qx_choose_then`n2`strip_assume_tac) lineForwardFD_forwardFD
  \\ qspecl_then[`lineForwardFD (lineForwardFD fs 0) 0`,`0`](qx_choose_then`n3`strip_assume_tac) lineForwardFD_forwardFD
  \\ qspecl_then[`lineForwardFD (lineForwardFD (lineForwardFD fs 0) 0) 0`,`0`](qx_choose_then`n4`strip_assume_tac) lineForwardFD_forwardFD
  \\ qspecl_then[`lineForwardFD (lineForwardFD (lineForwardFD (lineForwardFD fs 0) 0) 0) 0`,`0`](qx_choose_then`n5`strip_assume_tac) lineForwardFD_forwardFD
  \\ simp[forwardFD_o]
  \\ CASE_TAC \\ xsimpl
  \\ qx_gen_tac`n`
  \\ qexists_tac`n+n1+n2+n3+n4+n5`
  \\ qexists_tac`explode x`
  \\ xsimpl);

val _ = export_theory();
