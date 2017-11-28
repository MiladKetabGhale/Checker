open HolKernel bossLib boolLib pairLib integerTheory listTheory Parse boolSimps
open pairTheory numLib numTheory ratTheory fracTheory 
open listLib satTheory relationTheory 
open stringLib 
open stringTheory


val _ = new_theory "parserOptionalised"

val _ = Hol_datatype ` Cand = cand of string ` ; 

val _ = Hol_datatype `judgement =  
                                      state   of 
                         ((Cand list) # (num # num)) list
                                             # (Cand # (num # num)) list
                                             # (Cand # (((Cand list) # (num # num)) list)) list
                                             # Cand list 
                                             # Cand list
                                             # Cand list 
                       | winners of (Cand list) `; 
  


val de_optionalise_def = Define `   
         (de_optionalise (SOME a) = a)`
   
  
 
(* start of first part *)
val t_cand_list_def = Define`
t_cand_list tlst = 
       case tlst of 
           [] => []
         | (#"," :: t) => t_cand_list t
         | (#"[" :: t) => t_cand_list t
         | (#"]" :: t) => t_cand_list t
         | (#" " :: t) => t_cand_list t
         | (x :: t) => (cand (STR x)) :: t_cand_list t`   
   
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
        [] => (de_optionalise NONE)
      | (h::t) => 
        (case t of 
          [] => (de_optionalise NONE)
        | h1::t1 => de_optionalise (SOME (parse_number h, 
                                          parse_number (IMPLODE 
                                                       (FILTER isDigit 
                                                       (EXPLODE h1))))))` 

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
              | h1::t1 => SOME (cand h, parse_rational2 h1))`   
 

val parse_second_part2_def = Define`
parse_second_part2 str = 
 let strs = TOKENS (\x. x = #" ") str in
 MAP (de_optionalise o parse_second_t2) strs`
     


val parse_third_t2_def = Define`
parse_third_t2 tstr = 
  case (TOKENS (\x. x = #"{") tstr) of
     [] => NONE
   | h::t => (case t of
               [] => NONE
             | h1::t1 => SOME (cand h, parse_first_part2 h1))`
    


val parse_third_part2_def = Define`
parse_third_part2 str = 
  let strs = TOKENS (\x. x = #" ") str in
  MAP (de_optionalise o parse_third_t2) strs`


val parse_whole_line2_def = Define`
parse_whole_line2 str = 
  case (TOKENS (\x. x = #";") str) of
      [] => NONE
    | h0::t0 => 
       (case t0 of
          [] => NONE
        | h1::t1 => 
           (case t1 of 
             [] => NONE
           | h2::t2 => 
               case t2 of
                 [] => NONE            
               | h3::t3 => 
                   case t3 of
                     [] => NONE
                   | h4::t4 => 
                        case t4 of
                           [] => NONE
                         | h5::t5 =>  SOME (state (parse_first_part2 h0,
                                                   parse_second_part2 h1,
                                                   parse_third_part2 h2, 
                                                   parse_rest h3,
                                                   parse_rest h4,
                                                   parse_rest h5))))`