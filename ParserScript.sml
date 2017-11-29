open preamble CheckerSpecTheory

val _ = new_theory "Parser"

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

val _ = export_theory();
