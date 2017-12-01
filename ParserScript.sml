open preamble basis CheckerSpecTheory

val _ = new_theory "Parser"

(* TODO: this should probably be in the CakeML basis library *)
val splitl_aux_def = tDefine"splitl_aux"`
  splitl_aux P s i =
    if i < strlen s ∧ P (strsub s i) then
        splitl_aux P s (i+1)
    else (extract s 0 (SOME i), extract s i NONE)`
(WF_REL_TAC`inv_image $< (λ(x,s,i). strlen s - i)`);

val splitl_def = Define`
  splitl P s = splitl_aux P s 0`;

(*
EVAL ``splitl isLower (strlit"this,is,a,list")``
EVAL ``splitl isUpper (strlit"CAND plus junk")``
*)
(* -- *)

(* To be filled in later with correct implementations *)

val parse_quota_def = Define`
  parse_quota (line:mlstring) = SOME (0:rat)`;

val parse_seats_def = Define`
  parse_seats (line:mlstring) = SOME 3`;

val parse_candidates_def = Define`
  parse_candidates (line:mlstring) = SOME [Cand(strlit"A");Cand(strlit"B")]`;

val parse_judgement_def = Define`
  parse_judgement (line:mlstring) = SOME (NonFinal([],[],[],[],[],[]))`;

(* maybe...

bare_parse_quota str pos ---> SOME (quota, pos')

parse_quota line =
  case bare_parse_quota line 0
  | NONE => NONE
  | SOME (q,pos') => if pos' = strlen line then SOME q else NONE
*)

(* parser type:
  string -> position -> ('a * position) option
  parse_x s i
  reads s starting at position i
  returns SOME (x,i') if an x can be read from this position, where i' is the
  resulting position after reading x
*)
(*

val repeat_parse_def = tDefine"repeat_parse"`
  repeat_parse p s i =
    case p s i of NONE => SOME ([],i)
    | SOME (x,i') =>
      case
        if i < i' ∧ i' < strlen s then repeat_parse p s i' else SOME ([],i)
      of SOME (xs,i'') => SOME (x::xs,i'') | _ => NONE`
(WF_REL_TAC`inv_image $< (λ(x,s,i). strlen s - i)`);

val seq_parse_def = Define`
  seq_parse f p1 p2 s i =
    case p1 s i of NONE => NONE
    | SOME (x,i) =>
      case p2 s i of NONE => NONE
      | SOME (y,i) => SOME (f x y,i)`;

val parse_comma_list_def = Define`
  parse_comma_list parse_item s i =
    seq_parse (λ_ ls. ls)
      (parse_char #"[")
      (seq_parse (λls _. ls)
        (repeat_parse (seq_parse
        (parse_char "#]"))`;

    if 2 ≤ strlen s ∧ strsub s 0 = #"["
    then
      seq_parse (λls _. ls)
        (repeat_parse (seq_parse (λ
      repeat_parse
      OPT_MMAP parse_item (tokens ((=) #",") (extract s 1 (SOME (strlen s - 2))))
    else NONE`;

(*
EVAL ``parse_comma_list SOME (strlit"this,is,not,a,comma,list")``
EVAL ``parse_comma_list SOME (strlit"[this,is,a,comma,list]")``
*)

val parse_space_list_def = Define`
  parse_space_list parse_item s =
    OPT_MMAP parse_item (tokens ((=) #" ") s)`;

(*
EVAL ``parse_space_list SOME (strlit"this is a space list")``
EVAL ``parse_space_list SOME (strlit"[this is a weird space list]")``
*)

val parse_candidate_def = Define`
  parse_candidate s =
    if strlen s <> 0 ∧ strlen (SND (splitl isUpper s)) = 0
    then SOME (Cand s) else NONE`;

val parse_candidates_def = Define`
  parse_candidates s = parse_comma_list parse_candidate s`;


val parse_candidates_test = Q.store_thm("parse_candidates_test",
  `parse_candidates (strlit"[A,B,C]") =
    SOME [Cand(strlit"A"); Cand(strlit"B"); Cand(strlit"C")]`,
  EVAL_TAC);

val parse_quota_def = Define`
  parse_quota s =
    case tokens ((=) #"%") s of
    | [n1;n2] => (* TODO: want Num.fromString when it is merged? *)
                 OPTION_MAP2 rat_cons (fromString n1) (fromString n2)
    | _ => NONE`;

val parse_quota_test = Q.store_thm("parse_quota_test",
  `parse_quota (strlit "5%1") = SOME (5 // 1)`,
  EVAL_TAC);

val parse_pair_def = Define`
  parse_pair parse_fst parse_snd s =
    if 3 ≤ strlen s ∧
       strsub s 0 = #"(" ∧
       strsub s (strlen s - 1) = #")"
    then
      case tokens ((=) #",") (extract s 1 (SOME (strlen s - 2))) of
      | [x1;x2] => OPTION_MAP2 (,) (parse_fst x1) (parse_snd x2)
      | _ => NONE
    else NONE`;

val parse_ballots_def = Define`
  parse_ballots = parse_comma_list (parse_pair parse_candidates parse_quota)`;

val parse_ballots_test = Q.store_thm("parse_ballots_test",
  `parse_ballots (strlit"[([A,B,C],1%1),([C,B,A],1%1),([A,B,C],1%1),([A,B,C],1%1),([C,B,A],1%1),([A,C,B],1%1),([B,C,A],1%1),([A,B,C],1%1)]")
  = SOME [([Cand(strlit"A");Cand(strlit"B");Cand(strlit"C")],1);
          ([Cand(strlit"C");Cand(strlit"B");Cand(strlit"A")],1);
          ([Cand(strlit"A");Cand(strlit"B");Cand(strlit"C")],1);
          ([Cand(strlit"A");Cand(strlit"B");Cand(strlit"C")],1);
          ([Cand(strlit"C");Cand(strlit"B");Cand(strlit"A")],1);
          ([Cand(strlit"A");Cand(strlit"C");Cand(strlit"B")],1);
          ([Cand(strlit"B");Cand(strlit"C");Cand(strlit"A")],1);
          ([Cand(strlit"A");Cand(strlit"B");Cand(strlit"C")],1)]`,
  EVAL_TAC


val parse_candidate_quota_def =  Define`
  parse_candidate_quota s =


val parse_tallies_def = Define`
  parse_tallies s =
    parse_space_list parse_candidate_quota`;

(* start of first part *)
val t_cand_list_def = Define`
  t_cand_list tlst =
       case tlst of
           [] => []
         | (#"," :: t) => t_cand_list t
         | (#"[" :: t) => t_cand_list t
         | (#"]" :: t) => t_cand_list t
         | (#" " :: t) => t_cand_list t
         | (x :: t) => (Cand (STR x)) :: t_cand_list t`

(*
EVAL ``t_cand_list ( [#"["; #"1"; #","; #"B"; #","; #"C"; #"]"] )``
*)

val cand_list_def = Define`
cand_list st =
  let lst = EXPLODE st in
  t_cand_list lst`

val process_chunk_def = tDefine "process_chunk" `
  process_chunk tlst acc lst=
  case  tlst of
      [] => lst
    | (#")" :: #"," :: t) =>
      process_chunk t ""
                    (FLAT [lst; [CONCAT [acc; ")"]]])
    | (#")" :: t) =>
      process_chunk t ""
                    (FLAT [lst; [CONCAT [acc; ")"]]])
    | (x :: t)  => process_chunk t (CONCAT [acc; (STR x)]) lst`
((WF_REL_TAC `measure (LENGTH o FST )` >>
REPEAT STRIP_TAC )
  >- FULL_SIMP_TAC list_ss []
  >- FULL_SIMP_TAC list_ss []
  >- FULL_SIMP_TAC list_ss []
  >- FULL_SIMP_TAC list_ss [])

val split_it_into_pair_def = Define`
  split_it_into_pair st =
    let lst = EXPLODE st in
    process_chunk (TL lst) "" []`

(*
EVAL ``split_it_into_pair "[([A,B,C],1.0),([C,B,A],1.0),([B,A,C],1.0),([C,A,B],1.0),([A,B,C],1.0),([A,B,C],1.0),([C,B,A],1.0),([A,C,B],1.0),([B,C,A],1.0),([A,B,C],3.0)]"``
*)

val parse_pair_t_def = tDefine "parse_pair_t" `
  parse_pair_t ts (ac, bc) =
    case ts of
        [] => (ac, bc)
      | (#"(" :: t) => parse_pair_t t (ac, bc)
      | (#")" :: t) => parse_pair_t t (ac, bc)
      | (#"]" :: #"," :: t) =>
        (CONCAT [ac; "]"], IMPLODE t)
      | (x :: t) =>
        parse_pair_t t (CONCAT [ac; STR x], bc)`
((WF_REL_TAC `measure (LENGTH o FST)` >>
             REPEAT STRIP_TAC)
     >- FULL_SIMP_TAC list_ss []
     >- FULL_SIMP_TAC list_ss []
     >- FULL_SIMP_TAC list_ss []
     >- FULL_SIMP_TAC list_ss []
     >- FULL_SIMP_TAC list_ss [])

val parse_pair_def = Define`
  parse_pair str =
        let tm = EXPLODE str in
        parse_pair_t tm ("", "")`

val parse_number_t_def = Define`
  parse_number_t lst acc =
     case lst of
         [] => acc
       | h :: t => parse_number_t t (10 * acc + (ORD h - ORD #"0"))`

val parse_number_def = Define`
  parse_number str =
    let nlst = EXPLODE str in
    parse_number_t nlst 0`

val parse_rational2_def = Define`
  parse_rational2 str =
    case (TOKENS (\x. x = #"%") str) of
        [] => 0
      | (h::t) =>
        (case t of
          [] => 0
        | h1::t1 => &parse_number h // &parse_number (IMPLODE (FILTER isDigit (EXPLODE h1))))`

val parse_first_part2_def = Define`
  parse_first_part2 str =
 let l1 = split_it_into_pair str in
 let l2 = MAP (\x. parse_pair x) l1 in
 let l3 = MAP (\(x, y). (cand_list x, parse_rational2 y)) l2 in
 l3`

val parse_second_t2_def = Define`
  parse_second_t2 tstr =
  case (TOKENS (\x. x = #"{") tstr) of
      [] => NONE
    | h::t => (case t of
                [] => NONE
              | h1::t1 => SOME (Cand h, parse_rational2 h1))`

val parse_second_part2_def = Define`
  parse_second_part2 str =
 let strs = TOKENS (\x. x = #" ") str in
 OPT_MMAP parse_second_t2 strs`

val parse_third_t2_def = Define`
  parse_third_t2 tstr =
  case (TOKENS (\x. x = #"{") tstr) of
     [] => NONE
   | h::t => (case t of
               [] => NONE
             | h1::t1 => SOME (Cand h, parse_first_part2 h1))`

val parse_third_part2_def = Define`
  parse_third_part2 str =
  let strs = TOKENS (\x. x = #" ") str in
    OPT_MMAP parse_third_t2 strs`

val parse_rest_def = Define`
  parse_rest _ = []`;

val parse_whole_line2_def = Define`
  parse_whole_line2 str =
  case (TOKENS (\x. x = #";") str) of
  | (h0::h1::h2::h3::h4::h5::t5) =>
      OPTION_BIND (parse_second_part2 h1) (λtallies.
      OPTION_BIND (parse_third_part2 h2) (λpiles.
      SOME (NonFinal (parse_first_part2 h0,
                      tallies,
                      piles,
                      parse_rest h3,
                      parse_rest h4,
                      parse_rest h5))))
  | _ => NONE`
*)

val _ = export_theory();
