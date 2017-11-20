open HolKernel bossLib boolLib pairLib integerTheory listTheory Parse boolSimps
open stringLib
open pairTheory
open numLib
open numTheory
open ratTheory
open bossLib
open fracTheory
open listLib
open satTheory
open sortingTheory
open relationTheory
;


val _ = new_theory "Checker" ;

val _ = ParseExtras.temp_loose_equality();

val _ = Parse.set_grammar_ancestry["rat","sorting"];

val _ = Hol_datatype ` Cand = cand of string ` ;

val _ = Hol_datatype `judgement =
                                 state   of
                                    ((Cand list) # rat) list
                                  # (Cand # rat) list
                                  # (Cand # (((Cand list) # rat) list)) list
                                  # Cand list
                                  # Cand list
                                  # Cand list
                               | winners of (Cand list) `;

val sum_aux_def = Define ` ((sum_aux []) = 0) /\
                          ( (sum_aux (h::t)) = ((SND h) + (sum_aux t)) )  `;



(*The boolian function for deciding on ewin correct application*)
val Ewin_def = Define `
        (Ewin (qu : rat) st ((winners l), (j : judgement)) = F)
        /\ (Ewin qu st (state p, state p') = F)
        /\ (Ewin qu st (state (ba, t, p, bl, e, h), winners l) =
                       ( (e =l) /\ (LENGTH e = st)))`;


val Hwin_def = Define `
        (Hwin (qu : rat) st (winners l, (j : judgement)) = F)
        /\ (Hwin qu st (state p, state p') = F)
        /\ (Hwin qu st (state (ba, t, p, bl, e, h), winners l) =
            ((e ++ h) = l) /\ ((LENGTH (e ++ h)) <= st))`;



val get_cand_tally_def = Define `
           (get_cand_tally (c: Cand) (h ::t) = (if  (c = FST h) then SND h
                                            else (get_cand_tally c t))) `;

val get_cand_pile_def = Define `
     (get_cand_pile (c : Cand) ([] : (Cand # (((Cand list) # rat) list)) list) = [])
     /\ (get_cand_pile c (h ::t) = (if (c = FST h) then SND h
                                     else get_cand_pile c t)) `;

val empty_cand_pile_def = Define `
   (empty_cand_pile (c : Cand) ([] : (Cand # (((Cand list) # rat) list)) list) = [])
   /\ (empty_cand_pile c (h ::t) = (if (c = FST h) then ((c, []) :: t)
                                    else h :: (empty_cand_pile c t))) `;



val Legal_Tally_Cand_def = Define `
      (Legal_Tally_Cand l ([]: (Cand # rat) list) (c:Cand) = F)
   /\ (Legal_Tally_Cand l (h::t) c =  (MEM c l)
                                   /\ (if (FST h = c) then (~ MEM c (MAP FST t))
                                       else Legal_Tally_Cand l t c)) `;

val remove_one_cand_def = Define `
                         (remove_one_cand (c :Cand) [] = [])
                      /\ (remove_one_cand c (h::t) = (if c = h then t
                                                      else h:: remove_one_cand c t)) `;

 val not_elem = Define `   (not_elem a [] = T)
                       /\ (not_elem a (h::t) = (if (a = h) then F
                                               else (not_elem a t))) `;

val no_dup = Define  `   (no_dup [] = T)
                      /\ (no_dup (h::t) = (if (not_elem h t) then (no_dup t)
                                           else F)) `;




val Valid_PileTally_DEC1_def = Define `
        (Valid_PileTally_DEC1 [] (l: Cand list) = T)
     /\ (Valid_PileTally_DEC1 (h::t) l = (MEM (FST h) l) /\ (Valid_PileTally_DEC1 t l)) `;


val Valid_PileTally_DEC2_def = Define `
        (Valid_PileTally_DEC2 t ([]: Cand list) = T)
     /\ (Valid_PileTally_DEC2 t (l0::ls) = if (MEM l0 (MAP FST t))
                                                then (Valid_PileTally_DEC2 t ls)
                                           else F) `;


val non_empty = Define ` (non_empty [] = F)
                      /\ (non_empty _ = T) `;


val empty_list_def = Define `
                         (empty_list [] = T)
                      /\ (empty_list _ = F) `;



val less_than_quota_def = Define `
                 (less_than_quota qu [] l = T)
              /\ (less_than_quota qu (h ::tl ) l = (if (get_cand_tally h l < qu)
                                                         then less_than_quota qu tl l
                                                    else F)) `;



val bigger_than_cand_def = Define `
           (bigger_than_cand c t [] = T)
        /\ (bigger_than_cand c t (h0::h1) = if (get_cand_tally c t) <= (get_cand_tally h0 t)
                                                then (bigger_than_cand c t h1)
                                             else F) `;




val subpile1_def = Define `
        (subpile1 c ([]: (Cand # (((Cand list) # rat) list)) list) p2 = T)
     /\ (subpile1 c (p0::ps) p2 = if (c = FST p0) then (MEM (c,[]) p2) /\ (subpile1 c ps p2)
                                 else
                                     if (MEM p0 p2) then (subpile1 c ps p2)
                                     else F) `;




val subpile2_def = Define `
      (subpile2 c ([]: (Cand # (((Cand list) # rat) list)) list) p1 = T)
   /\ (subpile2 c (p0::ps) p1 = if (c = FST p0) then (subpile2 c ps p1)
                                else
                                    if (MEM p0 p1) then (subpile2 c ps p1)
                                    else F)`;



val no_dup_pile_def = Define `
     (no_dup_pile x ([] : ((((Cand list) # rat) list) list)) = T)
  /\ (no_dup_pile x (h::t) = if (x = h) then
                               if (not_elem x t) then T else F
                             else  no_dup_pile x t)`;


val list_MEM_def = Define `
      (list_MEM [] l = T)
   /\ (list_MEM (h::t) l = (MEM h l) /\ (list_MEM t l))`;


val list_not_MEM_def = Define `
        (list_not_MEM  [] l = T)
     /\ (list_not_MEM (h::t) l = (~ MEM h l) /\ (list_not_MEM t l))`;





val Elim_cand_dec_def = Define `
             (Elim_cand_dec st (qu : rat) (l: Cand list) (c:Cand) ((j: judgement), winners w) = F)
          /\ (Elim_cand_dec st qu l c (winners w, (j: judgement)) = F)
          /\ (Elim_cand_dec st qu l c (state (ba, t, p, bl, e, h), state (ba', t', p', bl', e',h')) =
                  ((empty_list ba)
               /\ (empty_list bl)
               /\ (t = t') /\ (bl = bl') /\ (e = e')
               /\ (LENGTH (e ++ h) > st) /\ (LENGTH e < st)
               /\ (non_empty l) /\ (no_dup l)
               /\ (list_MEM (h++e) l)
               /\ (no_dup (h++e))
               /\ (Valid_PileTally_DEC1 p l) /\ (Valid_PileTally_DEC2 p l)
               /\ (Valid_PileTally_DEC1 p' l) /\ (Valid_PileTally_DEC2 p' l)
               /\ no_dup (MAP FST t)
               /\ (Valid_PileTally_DEC1 t l) /\ (Valid_PileTally_DEC2 t l)
               /\ (MEM c h)
               /\ (less_than_quota qu h t)
               /\ (h' = remove_one_cand c h)
               /\ (bigger_than_cand c t h)
               /\ (ba' = get_cand_pile c p)
               /\ (MEM (c,[]) p')
               /\ (subpile1 c p p') /\ (subpile2 c p' p) )) `;





val Transfer_dec_def = Define `
         (Transfer_dec st (qu : rat) (l: Cand list) ((j: judgement), winners w) = F)
          /\ (Transfer_dec st qu l (winners w, (j: judgement)) = F)
          /\ (Transfer_dec st qu l (state (ba, t, p, bl, e, h), state (ba', t', p', bl', e',h')) =
              (empty_list ba) /\ (e = e') /\ (h = h') /\ (t = t')
           /\ (LENGTH e < st)
           /\ (list_MEM (h++e) l)
           /\ no_dup (h++e)
           /\ (Valid_PileTally_DEC1 t l) /\ (Valid_PileTally_DEC2 t l)
           /\ (Valid_PileTally_DEC1 p l) /\ (Valid_PileTally_DEC2 p l)
           /\ (Valid_PileTally_DEC1 p' l) /\ (Valid_PileTally_DEC2 p' l)
           /\ (non_empty l) /\ (no_dup l)
           /\ (no_dup (MAP FST t))
           /\ (less_than_quota qu h t)
           /\ (bl = (HD bl) :: (TL bl))
           /\ (bl' = (TL bl))
           /\ (ba' = get_cand_pile (HD bl) p)
           /\ (MEM (HD bl,[]) p')
           /\ (subpile1 (HD bl) p p') /\ (subpile2 (HD bl) p' p))`;


val fcc_dec = Define `
        (fcc (c:Cand) ([]: Cand list)  (h: Cand list) = F)
     /\ (fcc c (b0::bs) h = if (c = b0) then T
                              else if (~ MEM b0 h) /\ (fcc c bs h) then T
                                   else F)`;



val Count_Dec_Aux = Define `
     (Count_Dec_Aux p np t nt ba h [] = T)
  /\ (Count_Dec_Aux p np t nt ba  h (l0::ls) =
       if (MEM l0 h) then
        (get_cand_pile l0 np = (get_cand_pile l0 p) ++ FILTER (\ (b: (Cand list) # rat). (fcc l0 (FST b) h)) ba)
          /\ (get_cand_tally l0 nt = sum_aux (FILTER (\ (b: (Cand list) # rat). (fcc l0 (FST b) h)) ba))
           /\ (Count_Dec_Aux p np t nt ba h ls)
        else
             (get_cand_pile l0 np = get_cand_pile l0 p)
          /\ (get_cand_tally l0 nt = get_cand_tally l0 t)
          /\ (Count_Dec_Aux p np t nt ba h ls))`;



 val Count_Aux_dec = Define `
    (Count_Aux_dec st (qu : rat) (l: Cand list) ((j: judgement), winners w) = F)
 /\ (Count_Aux_dec st qu l (winners w, (j: judgement)) = F)
 /\ (Count_Aux_dec st qu l (state (ba, t, p, bl, e, h), state (ba', t', p', bl', e',h')) =
       (Count_Dec_Aux p p' t t' ba h l)
    /\ (bl = bl') /\ (e = e') /\ (h = h')
    /\ (no_dup (h++e))
    /\ no_dup (MAP FST p)
    /\ (list_MEM (h++e) l)
    /\ (Valid_PileTally_DEC1 t l) /\ (Valid_PileTally_DEC2 t l)
    /\ (Valid_PileTally_DEC1 t' l) /\ (Valid_PileTally_DEC2 t' l)
    /\ (Valid_PileTally_DEC1 p l) /\ (Valid_PileTally_DEC2 p l)
    /\ (Valid_PileTally_DEC1 p' l) /\ (Valid_PileTally_DEC2 p' l)
    /\ no_dup (MAP FST p')
    /\ no_dup (MAP FST t')
    /\ (non_empty l) /\ (no_dup l)
    /\ (no_dup (MAP FST t))
    /\ (non_empty ba)
    /\ (non_empty h)
    /\ (ba' = []))`;




val take_append = Define `
      (take_append [] _ = [])
   /\ (take_append (l0::ls) [] = l0::ls)
   /\ (take_append (l0::ls) (h::t) = (take_append ls t))`;





val tally_comparison = Define `
     (tally_comparison (t: (Cand # rat) list) c1 c2 = if (get_cand_tally c1 t <= get_cand_tally c2 t)
                                                        then T else F)`;




val eqe_list_dec = Define `
     (eqe_list_dec ([]: Cand list) l1 l2 = if (list_MEM l1 l2) then T else F)
  /\ (eqe_list_dec (l0::ls) l1 l2 = (~ MEM l0 l1) /\ (MEM l0 l2) /\ eqe_list_dec ls l1 l2)`;



val eqe_list_dec2 = Define `
     (eqe_list_dec2 l0 l1 ([]: Cand list) = T)
  /\ (eqe_list_dec2 l0 l1 (l::ls) = (MEM l l0 \/ MEM l l1) /\ (eqe_list_dec2 l0 l1 ls))`;


val bigger_than_quota = Define `
       (bigger_than_quota ([] :Cand list) t (qu :rat) = T)
    /\ (bigger_than_quota (l0::ls) t qu = (qu <= get_cand_tally l0 t) /\ (bigger_than_quota ls t qu))`;



val piles_eq_list = Define `
       (piles_eq_list ([]: Cand list) l p1 p2 = T)
    /\ (piles_eq_list (l0::ls) l p1 p2 =
            if ~ (MEM l0 l)
                then (get_cand_pile l0 p1 = get_cand_pile l0 p2) /\ (piles_eq_list ls l p1 p2)
            else (piles_eq_list ls l p1 p2))`;



val update_cand_trans_val = Define `
    (update_cand_trans_val (qu: rat) (c: Cand) (t: (Cand # rat) list) (p: (Cand # (Cand list # rat) list) list) =
        MAP (\ (r:rat). r * (((get_cand_tally c t) - qu) / (get_cand_tally c t))) (MAP SND (get_cand_pile c p)))`;



val update_cand_pile = Define `
          (update_cand_pile (qu: rat) t ([]: Cand list) p1 p2 = T)
       /\ (update_cand_pile qu t (l0::ls) p1 p2 =
           (MAP FST (get_cand_pile l0 p2) = MAP FST (get_cand_pile l0 p1))
        /\ (MAP SND (get_cand_pile l0 p2) = update_cand_trans_val qu l0 t p1) /\
           update_cand_pile qu t ls p1 p2)`;



val Elect_dec = Define `
              (Elect_dec st (qu : rat) (l: Cand list) ((j: judgement), winners w) = F)
 /\ (Elect_dec st qu l (winners w, (j: judgement)) = F)
 /\ (Elect_dec st qu l (state (ba, t, p, bl, e, h), state (ba', t', p', bl', e',h')) =
              let (l1 = (take_append bl' bl))
                 in
                   (SORTED (tally_comparison t) l1)
                /\ (no_dup (l1 ++ e))
                /\ (ba = []) /\ (ba' = [])
                /\ (t = t')
                /\ (non_empty l1)
                /\ (bigger_than_quota l1 t qu)
                /\ (LENGTH (l1 ++ e) <= st)
                /\ (eqe_list_dec l1 h' h)
                /\ (eqe_list_dec2 l1 h' h)
                /\ (no_dup h)
                /\ (no_dup (l1 ++ h'))
                /\ (no_dup e')
                /\ (eqe_list_dec l1 e e')
                /\ (eqe_list_dec2 l1 e e')
                /\ (piles_eq_list h l1 p p')
                /\ (no_dup (MAP FST p))
                /\ (no_dup (MAP FST t))
                /\ (no_dup (MAP FST p'))
                /\ (non_empty l)
                /\ (no_dup l)
                /\ (bl' = bl ++ l1)
                /\ (Valid_PileTally_DEC1 p l) /\ (Valid_PileTally_DEC2 p l)
                /\ (Valid_PileTally_DEC1 p' l) /\ (Valid_PileTally_DEC2 p' l)
                /\ (Valid_PileTally_DEC1 t l) /\ (Valid_PileTally_DEC2 t l)
                /\ (list_MEM e' l)
                /\ (list_MEM h l)
                /\ (update_cand_pile qu t l1 p p'))`;



val all_elem_zero = Define `
            (all_elem_zero ([]: rat list) = T)
         /\ (all_elem_zero (t0::ts) = (t0 = rat_0) /\ (all_elem_zero ts))`;


val all_elem_nil = Define `
            (all_elem_nil ([]: (((Cand list) # rat) list) list) = T)
         /\ (all_elem_nil (p0::ps) = (p0 = []) /\ (all_elem_nil ps))`;



val Initial_Judgement_dec = Define `
        (Initial_Judgement_dec (l: Cand list) (winners w) = F)
     /\ (Initial_Judgement_dec l (state (ba, t, p, bl, e, h)) =
                                (all_elem_zero (MAP SND t))
                             /\ (bl = [])
                             /\ (e = [])
                             /\ (h = l)
                             /\ (all_elem_nil (MAP SND p)))`;



val Final_Judgement_dec = Define `
           (Final_Judgement_dec (state (ba,t,p,bl,e,h)) = F)
        /\ (Final_Judgement_dec (winners l) = T)`;



val Elim_dec = Define `
         (Elim_dec st qu l (j1,j2) c = Elim_cand_dec st qu l c (j1,j2))`;



val Checker_Aux_dec = Define `
          (Checker_Aux_dec st qu l ([] : judgement list) = F)
       /\ (Checker_Aux_dec st qu l (j0::js) =
              if (empty_list js)
                          then  (Final_Judgement_dec j0)
              else if (empty_list (TL js))
                        then (Hwin qu st (j0,HD js) \/ Ewin qu st (j0,HD js))
                   else  ((Count_Aux_dec st qu l (j0,HD js))
                      \/ (Transfer_dec st qu l (j0,HD js))
                      \/ (Elect_dec st qu l (j0,HD js))
                      \/ (EXISTS (Elim_dec st qu l (j0,HD js)) l))
                      /\ (Checker_Aux_dec st qu l js))`;



val Checker_Aux2_dec = Define `
             (Checker_Aux2_dec st qu l ([]:judgement list) = F)
          /\ (Checker_Aux2_dec st qu l [j0] = Final_Judgement_dec j0)
          /\ (Checker_Aux2_dec st qu l (j0::j1::js) =
               ((Hwin qu st (j0,j1)
            \/ (Ewin qu st (j0,j1))
            \/ (Count_Aux_dec st qu l (j0,j1))
            \/ (Transfer_dec st qu l (j0,j1))
            \/ (Elect_dec st qu l (j0,j1))
            \/ (EXISTS (Elim_dec st qu l (j0,j1)) l))
            /\ (Checker_Aux2_dec st qu l (j1::js))))`;



val _ = export_theory();
