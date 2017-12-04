open preamble CheckerSpecTheory

val _ = new_theory "myparser"

(* start of first part *)
val t_cand_list_def = Define`
t_cand_list tlst =
       case tlst of
           [] => []
         | (#"," :: t) => t_cand_list t
         | (#"[" :: t) => t_cand_list t
         | (#"]" :: t) => t_cand_list t
         | (#" " :: t) => t_cand_list t
         | (x :: t) => (Cand (str x)) :: t_cand_list t`

(*
EVAL ``t_cand_list ( [#"["; #"A"; #","; #"B"; #","; #"C"; #"]"] )``
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


val parse_rational_def = Define`
parse_rational str =
    let tlst = TOKENS (\x. x = #"%") str in
    let first = HD tlst in
    let st = EXPLODE (HD (TL tlst)) in
    let second = IMPLODE (FILTER isDigit st) in
    &(parse_number first) // &(parse_number second)`



(* lets plug the values togather for first part*)
(*the following takes lists of ballots and parses them*)

val parse_first_part_def = Define`
parse_first_part str =
 let l1 = split_it_into_pair str in
 let l2 = MAP (\x. parse_pair x) l1 in
 let l3 = MAP (\(x, y). (cand_list x, parse_rational y)) l2 in
 l3`

(*
EVAL `` parse_first_part "[([A,B,C],1%2),([C,B,A],1%2),([B,A,C],1%2),([C,A,B],1%2),([A,B,C],1%2),([A,B,C],1%2),([C,B,A],1%2),([A,C,B],1%2),([B,C,A],1%2),([A,B,C],3%4)]"``
*)

(* End of first part. *)

(* start of second part *)

val parse_second_t_def = Define`
parse_second_t tstr =
  let lstr = TOKENS (\x. x = #"{") tstr in
  let first = HD lstr in
  let lrest = HD (TL lstr) in
  (Cand (implode first), parse_rational lrest)`

(*the following takes a pair of cands and their votes and parses them*)

val parse_second_part_def = Define`
parse_second_part str =
 let strs = TOKENS (\x. x = #" ") str in
 MAP parse_second_t strs`


(*
EVAL ``parse_second_part " A{5%6} B{2%3} C{3%4}"``
*)

(* parse_third_part *)


val parse_third_t_def = Define`
parse_third_t tstr =
 let tlst = TOKENS (\x. x = #"{") tstr in
 let first = HD tlst in
 let second = HD (TL tlst) in
 (Cand (implode first), parse_first_part second)`

(*the following takes a lists of pairs of cands with their piles*)

val parse_third_part_def = Define`
parse_third_part str =
  let strs = TOKENS (\x. x = #" ") str in
  MAP parse_third_t strs`

(*
EVAL ``parse_third_part " A{[([A,B,C],1%2),([A,B,C],1%2),([A,B,C],1%2),([A,C,B],1%2),([A,B,C],1%3)]} B{[([B,A,C],1%40),([B,C,A],1%2)]} C{[([C,B,A],1%2),([C,A,B],1%5),([C,B,A],15%16)]}"``
*)

(* end of third part *)

(* parse rest part, third, fourth and final *)
val parse_rest_def = Define`
parse_rest str = cand_list str`



(* combine all to parse one line *)

val parse_whole_line_def = Define`
parse_whole_line str =
  let semi = TOKENS (\x. x = #";") str in
  let (f, r1) = (HD semi, TL semi) in
  let (s, r2) = (HD r1, TL r1) in
  let (t, r3) = (HD r2, TL r2) in
  let (fr, r4) = (HD r3, TL r3) in
  let (fi, r5) = (HD r4, TL r4) in
  let sx = HD r5 in
  NonFinal (parse_first_part f, parse_second_part s,
   parse_third_part t, parse_rest fr,
   parse_rest fi, parse_rest sx)`

(* end of parsing one line *)

(*
EVAL ``parse_whole_line "[([A,B,C],1%1),([C,B,A],1%1),([B,A,C],1%1),([C,A,B],1%1),([A,B,C],1%1),([A,B,C],1%1),([C,B,A],1%1),([A,C,B],1%1),([B,C,A],1%1),([A,B,C],1%1)]; A{0%1} B{0%1} C{0%1}; A{[]} B{[]} C{[]}; []; []; [A,B,C]"``
*)

val parse_quota_def = Define`
  parse_quota line = SOME (parse_rational (explode line))`;
(*
EVAL ``parse_quota (strlit"3%5\n")``;
EVAL ``parse_quota (strlit"32%50\n")``;
*)

val parse_seats_def = Define`
  parse_seats line = SOME (parse_number (explode (extract line 0 (SOME (strlen line - 1)))))`;
(*
EVAL ``parse_seats (strlit"30\n")``;
*)

val parse_candidates_def = Define`
  parse_candidates line = SOME (parse_rest (explode (extract line 0 (SOME (strlen line - 1)))))`;
(*
EVAL ``parse_candidates (strlit"[A,B,C]\n")``;
*)

val parse_judgement_def = Define`
  parse_judgement line = SOME (parse_whole_line (explode (extract line 0 (SOME (strlen line - 1)))))`;
(*
EVAL ``parse_judgement (strlit"[]; A{5%1} B{2%1} C{3%1}; A{[([A,B,C],0%1),([A,B,C],0%1),([A,B,C],0%1),([A,C,B],0%1),([A,B,C],0%1)]} B{[([B,A,C],0%1),([B,C,A],0%1)]} C{[([C,B,A],1%1),([C,A,B],1%1),([C,B,A],1%1)]}; [A]; [A]; [B,C]\n")``;
*)

val _ = export_theory ()
