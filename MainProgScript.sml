open preamble basis CheckerTheory ParserProgTheory

val _ = new_theory"MainProg";

val _ = translation_extends"ParserProg";

(* TODO: move this to HOL *)
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
  \\ CASE_TAC \\ fs[LRC_def]
  );

val loop = process_topdecs`
  fun loop params i j1 j0 =
    if Valid_Step params j0 j1 then
      case TextIO.inputLine TextIO.stdIn of
        NONE =>
          if Initial_Judgement_dec (snd (snd params)) j0 then
            TextIO.print "Certificate OK\n"
          else
            TextIO.output TextIO.stdErr "Initial judgement malformed\n"
      | SOME line =>
      case parse_judgement line of
        NONE => TextIO.output TextIO.stdErr (String.concat["Malformed judgement on line ",Int.toString i,"\n"])
      | SOME judgement => loop params (i+1) judgement j1
    else TextIO.output TextIO.stdErr (String.concat["Invalid step on line ",Int.toString i,"\n"])`;

val _ = append_prog loop;

val _ = overload_on("PARAMS_TYPE",
  ``(PAIR_TYPE RAT_TYPE
         (PAIR_TYPE NUM (LIST_TYPE CHECKERSPEC_CAND_TYPE)))``);

val loop_spec = Q.store_thm("loop_spec",
  `PARAMS_TYPE params pv ∧
   NUM i iv ∧
   CHECKERSPEC_JUDGEMENT_TYPE j1 j1v ∧
   CHECKERSPEC_JUDGEMENT_TYPE j0 j0v ∧
   ⇒

   app (p:'ffi ffi_proj) ^(fetch_v"loop"(get_ml_prog_state()))
     [pv;iv;j1v;j0v]
     (STDIO fs)
     (POSTv uv. &UNIT_TYPE () uv *
                case OPT_MMAP parse_judgement (splitlines (get_stdin fs))
                of SOME js =>
                  if Check_Parsed_Certificate params js then
                    (STDIO (add_stdout (read_all_stdin fs) "Certificate OK\n"))
                  else
                    (SEP_EXISTS err. STDIO (add_stderr (read_some_stdin fs) err))
                | NONE =>
                    (SEP_EXISTS err. STDIO (add_stderr (read_some_stdin fs) err))
   `,

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

val _ = export_theory();
