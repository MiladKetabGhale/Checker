open preamble CheckerSpecTheory

val _ = new_theory "Checker";

val EWIN_dec_def = Define `
  (EWIN_dec ((qu,st,l):params) (NonFinal (_,_,_,_,e,_)) (Final e')
     ⇔ (e = e') /\ LENGTH e = st) ∧
  (EWIN_dec _ _ _ ⇔ F)`;

val HWIN_dec_def = Define `
  (HWIN_dec ((qu,st,l):params) (NonFinal (_,_,_,_,e,h)) (Final e')
    ⇔ (e' = e ++ h) ∧ (LENGTH (e++h) ≤ st)) ∧
  (HWIN_dec _ _ _ = F)`;

val equal_except_dec_def = Define `
     (equal_except_dec (c :cand) [] = [])
  /\ (equal_except_dec c (h::t) = (if c = h then t
                                  else h:: equal_except_dec c t)) `;

val Valid_PileTally_dec1_def = Define `
        (Valid_PileTally_dec1 [] (l: cand list) ⇔ T)
     /\ (Valid_PileTally_dec1 (h::t) l ⇔ (MEM (FST h) l) /\ (Valid_PileTally_dec1 t l)) `;


val Valid_PileTally_dec2_def = Define `
        (Valid_PileTally_dec2 t ([]: cand list) ⇔ T)
     /\ (Valid_PileTally_dec2 t (l0::ls) ⇔ if (MEM l0 (MAP FST t))
                                                then (Valid_PileTally_dec2 t ls)
                                           else F) `;

val list_MEM_dec_def = Define `
      (list_MEM_dec [] l ⇔ T)
   /\ (list_MEM_dec (h::t) l ⇔ (MEM h l) /\ (list_MEM_dec t l))`;

val list_not_MEM_dec_def = Define `
        (list_not_MEM_dec  [] l ⇔ T)
     /\ (list_not_MEM_dec (h::t) l ⇔ (~ MEM h l) /\ (list_not_MEM_dec t l))`;

val ELIM_CAND_dec_def = Define `
  (ELIM_CAND_dec c ((qu,st,l):params)
       (NonFinal ([], t, p, [], e, h))
       (NonFinal (ba', t', p', [], e',h')) ⇔
   (t = t') /\ (e = e')
   /\ (LENGTH (e ++ h) > st) /\ (LENGTH e < st)
   /\ (¬(NULL l)) /\ (ALL_DISTINCT l)
   /\ (list_MEM (h++e) l)
   /\ (ALL_DISTINCT (h++e))
   /\ (Valid_PileTally_dec1 p l) /\ (Valid_PileTally_dec2 p l)
   /\ (Valid_PileTally_dec1 p' l) /\ (Valid_PileTally_dec2 p' l)
   /\ ALL_DISTINCT (MAP FST t)
   /\ (Valid_PileTally_dec1 t l) /\ (Valid_PileTally_dec2 t l)
   /\ (MEM c h)
   /\ (less_than_quota qu t h)
   /\ (h' = equal_except_dec c h)
   /\ (bigger_than_cand c t h)
   /\ (ba' = get_cand_pile c p)
   /\ (MEM (c,[]) p')
   /\ (subpile1 c p p') /\ (subpile2 c p' p) ) ∧
  (ELIM_CAND_dec _ _ _ _ = F)`;

val TRANSFER_dec_def = Define `
  (TRANSFER_dec ((qu,st,l):params)
    (NonFinal ([], t, p, bl, e, h))
    (NonFinal (ba', t', p', bl', e',h')) ⇔
      (e = e') /\ (h = h') /\ (t = t')
   /\ (LENGTH e < st)
   /\ (list_MEM (h++e) l)
   /\ ALL_DISTINCT (h++e)
   /\ (Valid_PileTally_dec1 t l) /\ (Valid_PileTally_dec2 t l)
   /\ (Valid_PileTally_dec1 p l) /\ (Valid_PileTally_dec2 p l)
   /\ (Valid_PileTally_dec1 p' l) /\ (Valid_PileTally_dec2 p' l)
   /\ (¬(NULL l)) /\ (ALL_DISTINCT l)
   /\ (ALL_DISTINCT (MAP FST t))
   /\ (less_than_quota qu t h)
   /\ (case bl of [] => F | hbl::tbl =>
         (bl' = tbl)
         /\ (ba' = get_cand_pile hbl p)
         /\ (MEM (hbl,[]) p')
         /\ (subpile1 hbl p p') /\ (subpile2 hbl p' p))) ∧
  (TRANSFER_dec _ _ _ = F)`;

val first_continuing_cand_dec_def = Define `
  (first_continuing_cand_dec (c:cand) ([]: cand list)  (h: cand list) ⇔ F) /\
  (first_continuing_cand_dec c (b0::bs) h =
    if (c = b0) then T
    else if (~ MEM b0 h) /\ (first_continuing_cand_dec c bs h) then T
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
  bigger_than_quota ls (t:tallies) qu =
    EVERY (λl0. qu ≤ get_cand_tally l0 t) ls`;

(*
val bigger_than_quota = Define `
       (bigger_than_quota ([] :Cand list) t (qu :rat) = T)
    /\ (bigger_than_quota (l0::ls) t qu = (qu <= get_cand_tally l0 t) /\ (bigger_than_quota ls t qu))`;
*)

val piles_eq_list = Define `
       (piles_eq_list ([]: Cand list) l p1 p2 = T)
    /\ (piles_eq_list (l0::ls) l p1 p2 =
            if ~ (MEM l0 l)
                then (get_cand_pile l0 p1 = get_cand_pile l0 p2) /\ (piles_eq_list ls l p1 p2)
            else (piles_eq_list ls l p1 p2))`;


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
                /\ (0 < qu)
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
         /\ (all_elem_zero (t0::ts) = (t0 = 0) /\ (all_elem_zero ts))`;


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


val Check_Parsed_Certificate_def = Define`
  (Check_Parsed_Certificate seats quota candidates [] = F) /\
  (Check_Parsed_Certificate seats quota candidates (first_judgement::rest_judgements) =
     Initial_Judgement_dec candidates first_judgement /\
     Checker_Aux2_dec seats quota candidates (first_judgement::rest_judgements))`;

val _ = export_theory();
