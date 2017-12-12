open preamble basis CheckerTheory ParserProgTheory

val _ = new_theory"check_countProg";

val _ = translation_extends"ParserProg";

(* TODO: move to CakeML *)
val stdo_add_other_stdo = Q.store_thm("stdo_add_other_stdo",
  `fd <> fd' ∧ nm ≠ nm' ∧ stdo fd' nm' fs z ⇒
   (stdo fd nm (add_stdo fd' nm' fs x) y ⇔ stdo fd nm fs y)`,
  rw[add_stdo_def]
  \\ SELECT_ELIM_TAC \\ rw[] >- metis_tac[]
  \\ imp_res_tac stdo_UNICITY_R \\ rveq
  \\ fs[up_stdo_def,stdo_def,fsupdate_def,ALIST_FUPDKEY_ALOOKUP]
  \\ CASE_TAC \\ CASE_TAC);

val stdo_lineForwardFD = Q.store_thm("stdo_lineForwardFD",
  `fd ≠ fd' ⇒ (stdo fd' nm (lineForwardFD fs fd) out ⇔ stdo fd' nm fs out)`,
  metis_tac[stdo_forwardFD,lineForwardFD_forwardFD]);
(* -- *)

(* TODO: move to HOL *)
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

val OPT_MMAP_EQ_NONE = Q.store_thm("OPT_MMAP_EQ_NONE",
  `OPT_MMAP f xs = NONE ⇔ EXISTS (IS_NONE o f) xs`,
  Q.ISPECL_THEN[`f`,`xs`]mp_tac (Q.GEN`f`OPT_MMAP_EQ_SOME)
  \\ Cases_on`OPT_MMAP f xs` \\ rw[]
  \\ fs[EVERY_MEM,EXISTS_MEM,IS_SOME_EXISTS]
  \\ metis_tac[option_CASES,NOT_SOME_NONE]);

val option_case_rand = prove_case_rand_thm{case_def=option_case_def,nchotomy=option_nchotomy}
(* -- *)

(* The checker for unparsed certificates. Defined here so we can use the parser. *)

val () = patternMatchesLib.ENABLE_PMATCH_CASES ();

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

(* Now we construct a function implementing the above. *)

val malformed_line_msg_def = Define`
  malformed_line_msg (i:int) = concat[strlit"Malformed judgement on line ";toString i;strlit"\n"]`;
val invalid_step_msg_def = Define`
  invalid_step_msg (i:int) = concat[strlit"Invalid step on line ";toString i;strlit"\n"]`;

val loop_def = Define`
  loop params i j1 j0 ls =
   if Valid_Step params j0 j1 then
     dtcase ls of
     | [] => if Initial_Judgement_dec (SND(SND params)) j0
             then NONE
             else SOME (strlit"Malformed initial judgement\n",i)
     | (line::ls) =>
        dtcase parse_judgement line of
        | NONE => SOME (malformed_line_msg i,i+1)
        | SOME j => loop params (i+1) j0 j ls
   else SOME (invalid_step_msg i,i)`;

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

val loop_inc = Q.store_thm("loop_inc",
  `∀a i b c d e j. loop a i b c d = SOME (e,j) ⇒ i ≤ j`,
  recInduct loop_ind
  \\ rpt gen_tac \\ strip_tac
  \\ rw[Once loop_def]
  \\ FULL_CASE_TAC \\ fs[]
  \\ FULL_CASE_TAC \\ fs[]
  \\ rw[] \\ rfs[]
  \\ intLib.COOPER_TAC);

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
     (POSTv uv.
       &UNIT_TYPE () uv *
       STDIO (
         dtcase loop params i j1 j0 (MAP implode (linesFD fs 0)) of
         | NONE => add_stdout (fastForwardFD fs 0) "Certificate OK\n"
         | SOME (err,j) => add_stderr (FUNPOW (combin$C lineForwardFD 0) (Num(j-i)) fs) (explode err)))`,
  Induct_on`linesFD fs 0` \\ rw[]
  \\ qpat_x_assum`_ = linesFD _ _`(assume_tac o SYM) \\ fs[]
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
      \\ SELECT_ELIM_TAC
      \\ conj_tac >- metis_tac[STD_streams_stderr]
      \\ rw[]
      \\ fs[stdo_def]
      \\ simp[up_stdo_def,LENGTH_explode]
      \\ xsimpl )
    \\ reverse(Cases_on `∃inp pos. stdin fs inp pos`)
    >- ( (* TODO: Move this reasoning out into a separate theorem. *)
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
    \\ fs[]
    \\ imp_res_tac stdin_get_file_content
    \\ `IS_SOME (get_file_content fs 0)` by metis_tac[IS_SOME_EXISTS]
    \\ xlet_auto >- ( xsimpl \\ metis_tac[stdin_v_thm,stdIn_def] )
    \\ xmatch
    \\ rfs[linesFD_nil_lineFD_NONE,OPTION_TYPE_def]
    \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xif
    >- (
      xapp
      \\ simp[lineFD_NONE_lineForwardFD_fastForwardFD]
      \\ xsimpl
      \\ CONV_TAC SWAP_EXISTS_CONV
      \\ qexists_tac`fastForwardFD fs 0`
      \\ xsimpl )
    \\ xapp_spec output_STDIO_spec
    \\ xsimpl
    \\ simp[lineFD_NONE_lineForwardFD_fastForwardFD]
    \\ `STD_streams (fastForwardFD fs 0)` by simp[STD_streams_fastForwardFD]
    \\ drule STD_streams_stderr \\ strip_tac
    \\ fs[stdo_def,get_file_content_def,PULL_EXISTS]
    \\ instantiate
    \\ simp[REWRITE_RULE[EVAL``stdErr``]stderr_v_thm]
    \\ xsimpl
    \\ simp[insert_atI_end]
    \\ simp[add_stdo_def]
    \\ DEP_REWRITE_TAC[fastForwardFD_0]
    \\ fs[lineFD_def,get_file_content_def,UNCURRY]
    \\ rw[]
    \\ SELECT_ELIM_TAC
    \\ conj_tac >- metis_tac[STD_streams_stderr]
    \\ rw[]
    \\ fs[stdo_def]
    \\ simp[up_stdo_def,LENGTH_explode]
    \\ xsimpl )
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
  \\ fs[]
  \\ imp_res_tac stdin_get_file_content
  \\ `IS_SOME (get_file_content fs 0)` by metis_tac[IS_SOME_EXISTS]
  \\ xlet_auto >- ( xsimpl \\ metis_tac[stdin_v_thm,stdIn_def] )
  \\ xmatch
  \\ Cases_on`lineFD fs 0` \\ fs[OPTION_TYPE_def]
  >- ( fs[GSYM linesFD_nil_lineFD_NONE] )
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
  \\ CASE_TAC >- xsimpl
  \\ CASE_TAC
  \\ imp_res_tac loop_inc
  \\ qmatch_goalsub_abbrev_tac`Num x`
  \\ `0 ≤ x ∧ r - i = 1 + x` by (fs[Abbr`x`] \\ intLib.COOPER_TAC)
  \\ pop_assum SUBST_ALL_TAC
  \\ imp_res_tac integerTheory.NUM_POSINT_EXISTS
  \\ rw[integerTheory.INT_ADD,GSYM ADD1,FUNPOW]
  \\ xsimpl);

val missing_msg_def = Define`
  missing_msg name = concat[strlit"No ";name;strlit" line\n"]`;
val malformed_msg_def = Define`
  malformed_msg name = concat[strlit"Malformed ";name;strlit" line\n"]`;

val parse_line_def = Define`
  parse_line parse name ls =
    dtcase ls of [] => INR (missing_msg name)
    | line::ls =>
    (dtcase parse line of
     | NONE => INR (malformed_msg name)
     | SOME x => INL (x,ls))`;

val parse_line_drop = Q.store_thm("parse_line_drop",
  `parse_line p n ls = INL (x,ls') ⇒ ls' = DROP 1 ls`,
  rw[parse_line_def] \\ every_case_tac \\ fs[]);

val r = translate missing_msg_def;
val r = translate malformed_msg_def;

val parse_line = process_topdecs`
  fun parse_line parse name k =
    case TextIO.inputLine TextIO.stdIn of
      NONE => TextIO.output TextIO.stdErr (missing_msg name)
    | SOME line =>
    case parse line of
      NONE => TextIO.output TextIO.stdErr (malformed_msg name)
    | SOME x => k x`;

val _ = append_prog parse_line;

val parse_line_spec = Q.store_thm("parse_line_spec",
  `∀A parser name.
   (STRING_TYPE --> OPTION_TYPE A) parser parserv ∧
   STRING_TYPE name namev ∧
   (∀x xv. A x xv ⇒ app p kv [xv] (STDIO (lineForwardFD fs 0)) (POSTv v. &UNIT_TYPE () v * Q x))
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"parse_line"(get_ml_prog_state()))
   [parserv;namev;kv]
     (STDIO fs)
     (POSTv v. &UNIT_TYPE () v *
       dtcase parse_line parser name (MAP implode (linesFD fs 0))
       of INR msg => STDIO (add_stderr (lineForwardFD fs 0) (explode msg))
        | INL (x,ls) => Q x)`,
  xcf "parse_line" (get_ml_prog_state())
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
  \\ imp_res_tac stdin_get_file_content
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
    \\ simp[parse_line_def]
    \\ xsimpl )
  \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
  \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
  \\ qmatch_goalsub_abbrev_tac`STDIO fs1`
  \\ `STD_streams fs1` by simp[STD_streams_lineForwardFD,Abbr`fs1`]
  \\ simp[parse_line_def]
  \\ Cases_on`linesFD fs 0` \\ fs[linesFD_nil_lineFD_NONE]
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

val line4_def = Define`
  line4 quota seats candidates winners ls =
    dtcase parse_line parse_judgement (strlit"penultimate judgement") ls
    of INR err => SOME (err, 5) | INL (j0, ls) =>
      loop (quota,seats,candidates) 5 (Final winners) j0 ls`;

val line3_def = Define`
  line3 quota seats candidates ls =
    dtcase parse_line parse_candidates (strlit"final judgement") ls
    of INR err => SOME (err, 4) | INL (winners, ls) =>
      line4 quota seats candidates winners ls`;

val line2_def = Define`
  line2 quota seats ls =
    dtcase parse_line parse_candidates (strlit"candidates") ls
    of INR err => SOME (err, 3) | INL (candidates,ls) =>
      line3 quota seats candidates ls`;

val line1_def = Define`
  line1 quota ls =
    dtcase parse_line parse_seats (strlit"seats") ls
    of INR err => SOME (err, 2) | INL (seats,ls) =>
      line2 quota seats ls`;

val check_count_def = Define`
  check_count ls =
    dtcase parse_line parse_quota (strlit"quota") ls
    of INR err => SOME (err, 1) | INL (quota,ls) =>
      line1 quota ls`;

val check_count_thm = Q.store_thm("check_count_thm",
  `check_count ls = NONE ⇔ Check_Certificate ls`,
  rw[check_count_def,Check_Certificate_def,parse_line_def]
  \\ CONV_TAC(RAND_CONV(DEPTH_CONV patternMatchesLib.PMATCH_ELIM_CONV))
  \\ CASE_TAC \\ CASE_TAC >- every_case_tac
  \\ rw[line1_def,parse_line_def]
  \\ CASE_TAC \\ CASE_TAC >- every_case_tac
  \\ rw[line2_def,parse_line_def]
  \\ CASE_TAC \\ CASE_TAC >- every_case_tac
  \\ rw[line3_def,parse_line_def]
  \\ CASE_TAC \\ CASE_TAC
  \\ rw[line4_def,parse_line_def]
  \\ CASE_TAC
  >- rw[OPT_MMAP_def,Check_Parsed_Certificate_def,Initial_Judgement_dec_def]
  \\ rw[OPT_MMAP_def]
  \\ CASE_TAC \\ rw[]
  \\ rw[loop_thm]
  \\ CASE_TAC \\ fs[OPT_MMAP_EQ_NONE,o_DEF,OPT_MMAP_EQ_SOME]
  \\ rw[]);

val check_count = process_topdecs`
  fun check_count u =
    parse_line parse_quota "quota" (fn quota =>
    parse_line parse_seats "seats" (fn seats =>
    parse_line parse_candidates "candidates" (fn candidates =>
    parse_line parse_candidates "final judgement" (fn winners =>
    parse_line parse_judgement "penultimate judgement" (fn j0 =>
      loop (quota,(seats,candidates)) 5 (Final winners) j0)))))`;

val _ = append_prog check_count;

val check_count_spec = Q.store_thm("check_count_spec",
  `app (p:'ffi ffi_proj) ^(fetch_v"check_count"(get_ml_prog_state())) [Conv NONE []]
     (STDIO fs)
     (POSTv uv.
       &UNIT_TYPE () uv *
       STDIO
         (dtcase check_count (MAP implode (linesFD fs 0)) of
          | NONE => add_stdout (fastForwardFD fs 0) "Certificate OK\n"
          | SOME (err,n) => add_stderr (FUNPOW (combin$C lineForwardFD 0) (Num n) fs)
                              (explode err)))`,
  xcf "check_count" (get_ml_prog_state())
  \\ xfun`quota_fun`
  \\ xapp_spec (Q.ISPECL[`RAT_TYPE`,`parse_quota`]parse_line_spec)
  \\ simp[STRING_TYPE_def,parse_quota_v_thm]
  \\ qexists_tac`emp` \\ xsimpl
  \\ qexists_tac`fs` \\ xsimpl
  \\ simp[check_count_def]
  \\ simp[Once option_case_rand]
  \\ qmatch_goalsub_abbrev_tac`option_CASE _ Qval Qerr`
  \\ qexists_tac`λquota. option_CASE (line1 quota (DROP 1 (MAP implode (linesFD fs 0)))) Qval Qerr`
  \\ reverse conj_tac
  >- (
    reverse CASE_TAC >- (simp[Abbr`Qerr`] \\ xsimpl)
    \\ CASE_TAC
    \\ imp_res_tac parse_line_drop \\ rw[]
    \\ xsimpl )
  \\ qx_gen_tac`quota`
  \\ rpt strip_tac \\ fs[]
  \\ first_x_assum match_mp_tac
  \\ xfun`seats_fun`
  \\ xapp_spec (Q.ISPECL[`NUM`,`parse_seats`]parse_line_spec)
  \\ simp[STRING_TYPE_def,parse_seats_v_thm]
  \\ qexists_tac`emp` \\ xsimpl
  \\ qexists_tac`lineForwardFD fs 0` \\ xsimpl
  \\ simp[linesFD_lineForwardFD]
  \\ simp[line1_def,MAP_DROP]
  \\ qexists_tac`λseats. option_CASE (line2 quota seats (DROP 2 (MAP implode (linesFD fs 0)))) Qval Qerr`
  \\ reverse conj_tac
  >- (
    reverse CASE_TAC >- (simp[Abbr`Qerr`,numeralTheory.numeral_funpow] \\ xsimpl)
    \\ CASE_TAC
    \\ imp_res_tac parse_line_drop \\ rw[DROP_DROP_T]
    \\ xsimpl )
  \\ qx_gen_tac`seats`
  \\ rpt strip_tac \\ fs[]
  \\ first_x_assum match_mp_tac
  \\ xfun`candidates_fun`
  \\ xapp_spec (Q.ISPECL[`LIST_TYPE CHECKERSPEC_CAND_TYPE`,`parse_candidates`]parse_line_spec)
  \\ simp[STRING_TYPE_def,parse_candidates_v_thm]
  \\ qexists_tac`emp` \\ xsimpl
  \\ qexists_tac`lineForwardFD (lineForwardFD fs 0) 0` \\ xsimpl
  \\ simp[linesFD_lineForwardFD,DROP_DROP_T]
  \\ simp[line2_def,MAP_DROP]
  \\ qexists_tac`λcandidates. option_CASE (line3 quota seats candidates (DROP 3 (MAP implode (linesFD fs 0)))) Qval Qerr`
  \\ reverse conj_tac
  >- (
    reverse CASE_TAC >- (simp[Abbr`Qerr`,numeralTheory.numeral_funpow] \\ xsimpl)
    \\ CASE_TAC
    \\ imp_res_tac parse_line_drop \\ rw[DROP_DROP_T]
    \\ xsimpl )
  \\ qx_gen_tac`candidates`
  \\ rpt strip_tac \\ fs[]
  \\ first_x_assum match_mp_tac
  \\ xfun`winners_fun`
  \\ xapp_spec (Q.ISPECL[`LIST_TYPE CHECKERSPEC_CAND_TYPE`,`parse_candidates`]parse_line_spec)
  \\ simp[STRING_TYPE_def,parse_candidates_v_thm]
  \\ qexists_tac`emp` \\ xsimpl
  \\ qexists_tac`lineForwardFD (lineForwardFD (lineForwardFD fs 0) 0) 0` \\ xsimpl
  \\ simp[linesFD_lineForwardFD,DROP_DROP_T]
  \\ simp[line3_def,MAP_DROP]
  \\ qexists_tac`λwinners. option_CASE (line4 quota seats candidates winners (DROP 4 (MAP implode (linesFD fs 0)))) Qval Qerr`
  \\ reverse conj_tac
  >- (
    reverse CASE_TAC >- (simp[Abbr`Qerr`,numeralTheory.numeral_funpow] \\ xsimpl)
    \\ CASE_TAC
    \\ imp_res_tac parse_line_drop \\ rw[DROP_DROP_T]
    \\ xsimpl )
  \\ qx_gen_tac`winners`
  \\ rpt strip_tac \\ fs[]
  \\ first_x_assum match_mp_tac
  \\ xfun`j_fun`
  \\ xapp_spec (Q.ISPECL[`CHECKERSPEC_JUDGEMENT_TYPE`,`parse_judgement`]parse_line_spec)
  \\ simp[STRING_TYPE_def,parse_judgement_v_thm]
  \\ qexists_tac`emp` \\ xsimpl
  \\ qexists_tac`lineForwardFD (lineForwardFD (lineForwardFD (lineForwardFD fs 0) 0) 0) 0` \\ xsimpl
  \\ simp[linesFD_lineForwardFD,DROP_DROP_T]
  \\ simp[line4_def,MAP_DROP]
  \\ qexists_tac`λj0.
      option_CASE (loop (quota,seats,candidates) 5 (Final winners) j0 (DROP 5 (MAP implode (linesFD fs 0))))
      Qval Qerr`
  \\ reverse conj_tac
  >- (
    reverse CASE_TAC >- (simp[Abbr`Qerr`,numeralTheory.numeral_funpow] \\ xsimpl)
    \\ CASE_TAC
    \\ imp_res_tac parse_line_drop \\ rw[DROP_DROP_T]
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
  \\ simp[Abbr`fsn`,linesFD_lineForwardFD,DROP_DROP_T]
  \\ simp[MAP_DROP,Abbr`Qval`]
  \\ CASE_TAC >- xsimpl
  \\ CASE_TAC
  \\ simp[Abbr`Qerr`]
  \\ imp_res_tac loop_inc
  \\ simp[
    CONJUNCT2 FUNPOW
    |> Q.ISPEC`combin$C lineForwardFD 0`
    |> SIMP_RULE (srw_ss())[]
    |> GSYM]
  \\ simp[ADD1]
  \\ `0 ≤ r - 5` by intLib.COOPER_TAC
  \\ drule integerTheory.NUM_POSINT_EXISTS
  \\ strip_tac \\ simp[]
  \\ `r = &(n + 5)` by (simp[GSYM integerTheory.INT_ADD] \\ intLib.COOPER_TAC)
  \\ rw[]
  \\ xsimpl);

val (sem_thm,prog_tm) =
  call_thm (get_ml_prog_state()) "check_count" (
    check_count_spec
    |> CONV_RULE(RAND_CONV(SIMP_CONV
       std_ss [Once (SEP_CLAUSES |> SPEC_ALL |> CONJUNCTS |> last |> GSYM)]))
    |> SIMP_RULE std_ss [STDIO_def] |> add_basis_proj)

val STD_streams_FUNPOW_lineForwardFD_0 = Q.store_thm("STD_streams_FUNPOW_lineForwardFD_0",
  `∀n fs. STD_streams fs ⇒ STD_streams (FUNPOW (combin$C lineForwardFD 0) n fs)`,
  Induct \\ rw[STD_streams_lineForwardFD,FUNPOW]);

val stdo_FUNPOW_lineForwardFD_0 = Q.store_thm("stdo_FUNPOW_lineForwardFD_0",
  `∀n fs. fd ≠ fd' ⇒ (stdo fd nm (FUNPOW (combin$C lineForwardFD fd') n fs) out ⇔ stdo fd nm fs out)`,
  Induct \\ rw[stdo_lineForwardFD,FUNPOW]);

val check_count_prog_def = Define`check_count_prog = ^prog_tm`;

val check_count_sem =
  sem_thm |> REWRITE_RULE[GSYM check_count_prog_def] |> DISCH_ALL
  |> CONV_RULE(LAND_CONV EVAL)
  |> SIMP_RULE std_ss [AND_IMP_INTRO,Once option_case_rand]
  |> SIMP_RULE std_ss [STD_streams_add_stdout,STD_streams_fastForwardFD,Once pair_CASE_def]
  |> SIMP_RULE std_ss [STD_streams_add_stderr,STD_streams_FUNPOW_lineForwardFD_0,Once pair_CASE_def]
  |> SIMP_RULE std_ss [Once option_case_compute]
  |> curry save_thm "check_count_sem";

val check_count_correct = Q.store_thm("check_count_correct",
  `wfFS fs ∧ STD_streams fs ∧ stdout fs init_out ⇒
   ∃io_events fs'.
     semantics_prog (init_state (basis_ffi cls fs)) init_env check_count_prog
       (Terminate Success io_events) ∧
     extract_fs fs io_events = SOME fs' ∧
     (stdout fs' (init_out ++ "Certificate OK\n")
      ⇔ Check_Certificate (MAP implode (linesFD fs 0)))`,
  rw[]
  \\ imp_res_tac check_count_sem
  \\ first_x_assum(qspec_then`cls`strip_assume_tac)
  \\ asm_exists_tac \\ rw[]
  \\ CASE_TAC
  >- (
    simp[stdo_numchars,stdo_add_stdo,stdo_fastForwardFD]
    \\ fs[check_count_thm] )
  \\ qmatch_goalsub_abbrev_tac`add_stderr fs'`
  \\ `STD_streams fs'` by metis_tac[STD_streams_FUNPOW_lineForwardFD_0]
  \\ simp[stdo_numchars]
  \\ DEP_REWRITE_TAC[GEN_ALL stdo_add_other_stdo]
  \\ simp[]
  \\ conj_tac >- metis_tac[STD_streams_stderr]
  \\ simp[stdo_FUNPOW_lineForwardFD_0,Abbr`fs'`]
  \\ simp[GSYM check_count_thm]
  \\ strip_tac
  \\ imp_res_tac stdo_UNICITY_R
  \\ fs[]);

val _ = export_theory();
