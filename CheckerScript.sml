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


val _ = overload_on("list_MEM",``λl1 l2. set l1 ⊆ set l2``);
val _ = overload_on("list_not_MEM",``λl1 l2. DISJOINT (set l1) (set l2)``);


val list_MEM_dec_def = Define `
      (list_MEM_dec [] l ⇔ T)
   /\ (list_MEM_dec (h::t) l ⇔ (MEM h l) /\ (list_MEM_dec t l))`;


(*

=======
>>>>>>> f65cdf8b627cf9d7c780a19be8d336d97299ce62
val list_not_MEM_dec_def = Define `
        (list_not_MEM_dec  [] l ⇔ T)
     /\ (list_not_MEM_dec (h::t) l ⇔ (~ MEM h l) /\ (list_not_MEM_dec t l))`;

*)

val less_than_quota_def = Define `
  less_than_quota qu l ls =
    EVERY (λh. get_cand_tally h l < qu) ls`;

val bigger_than_cand_def = Define `
  bigger_than_cand c t ls =
    EVERY (λh0. get_cand_tally c t <= get_cand_tally h0 t) ls`;

    
val ELIM_CAND_dec_def = Define `
  (ELIM_CAND_dec c ((qu,st,l):params)
       (NonFinal (ba, t, p, bl, e, h))
       (NonFinal (ba', t', p', bl', e',h')) ⇔
    (NULL ba) /\ (NULL bl) /\ (NULL bl') /\  (t = t') /\ (e = e')
   /\ (LENGTH (e ++ h) > st) /\ (LENGTH e < st)
   /\ (¬(NULL l)) /\ (ALL_DISTINCT l)
   /\ (list_MEM_dec (h++e) l)
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
   /\ (subpile1 c p p') /\ (subpile2 c p' p))
   /\ (ELIM_CAND_dec c _ (Final _ ) _ = F) 
   /\ (ELIM_CAND_dec c _ _ (Final _ ) = F)`; 
 
 


(*
val ELIM_CAND_dec_def = Define `
  (ELIM_CAND_dec c (qu,st,l) (Final _ ) _ = F) /\
  (ELIM_CAND_dec c (qu,st,l) _ (Final _ ) = F) /\
  (ELIM_CAND_dec c ((qu,st,l):params)
       (NonFinal ([], t, p, [], e, h))
       (NonFinal (ba', t', p', [], e',h')) ⇔
   (t = t') /\ (e = e')
   /\ (LENGTH (e ++ h) > st) /\ (LENGTH e < st)
   /\ (¬(NULL l)) /\ (ALL_DISTINCT l)
   /\ (list_MEM_dec (h++e) l)
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
   /\ (subpile1 c p p') /\ (subpile2 c p' p) )`; 

*)
  
val TRANSFER_dec_def = Define `
  (TRANSFER_dec ((qu,st,l):params)
    (NonFinal (ba, t, p, bl, e, h))
    (NonFinal (ba', t', p', bl', e',h')) ⇔
      (NULL ba) /\ (e = e') /\ (h = h') /\ (t = t')
   /\ (LENGTH e < st)
   /\ (list_MEM_dec (h++e) l)
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
  (TRANSFER_dec _ (Final _) _ = F) /\
  (TRANSFER_dec _ _ (Final _) = F)`;
 
val first_continuing_cand_dec_def = Define `
  (first_continuing_cand_dec (c:cand) ([]: cand list)  (h: cand list) ⇔ F) /\
  (first_continuing_cand_dec c (b0::bs) h =
    if (c = b0) then T
    else if (~ MEM b0 h) /\ (first_continuing_cand_dec c bs h) then T
    else F)`;
  
val COUNTAux_dec_def = Define `
     (COUNTAux_dec p np t t' ba h [] <=> T)
  /\ (COUNTAux_dec p np t t' ba  h (l0::ls) <=>
      (let (l' = FILTER (λb. (first_continuing_cand_dec l0 (FST b) h)) ba)
       in 
          if (MEM l0 h) then
                (get_cand_pile l0 np = (get_cand_pile l0 p) ++l') /\
                (get_cand_tally l0 t' = SUM_RAT (MAP SND l'))
           else
                (get_cand_pile l0 np = get_cand_pile l0 p) /\
                (get_cand_tally l0 t' = get_cand_tally l0 t)) /\
	(COUNTAux_dec p np t t' ba h ls))`;
  
 
val COUNT_dec_def = Define `
   (COUNT_dec ((st, qu, l): params)
       (NonFinal (ba, t, p, bl, e, h))
       (NonFinal (ba', t', p', bl', e', h')) ⇔
    (COUNTAux_dec p p' t t' ba h l)
    /\ (bl = bl') /\ (e = e') /\ (h = h')
    /\ ALL_DISTINCT (h++e)
    /\ ALL_DISTINCT (MAP FST p)
    /\ (list_MEM_dec (h++e) l)
    /\ (Valid_PileTally_dec1 t l) /\ (Valid_PileTally_dec2 t l)
    /\ (Valid_PileTally_dec1 t' l) /\ (Valid_PileTally_dec2 t' l)
    /\ (Valid_PileTally_dec1 p l) /\ (Valid_PileTally_dec2 p l)
    /\ (Valid_PileTally_dec1 p' l) /\ (Valid_PileTally_dec2 p' l)
    /\ ALL_DISTINCT (MAP FST p')
    /\ ALL_DISTINCT (MAP FST t')
    /\ (~ (NULL l)) /\ (ALL_DISTINCT l)
    /\ ALL_DISTINCT (MAP FST t)
    /\ ~ (NULL ba)
    /\ ~ (NULL h)
    /\ (ba' = [])) /\
   (COUNT_dec _ (Final _) _ = F) /\
   (COUNT_dec _ _ (Final _) = F)`;


val take_append_def = Define `
   (take_append (l0::ls) (h::t) = (take_append ls t)) ∧
   (take_append l1 _ = l1)`;

val eqe_list_dec_def = Define `
     (eqe_list_dec ([]: cand list) l1 l2 ⇔ list_MEM_dec l1 l2)
  /\ (eqe_list_dec (l0::ls) l1 l2 ⇔ (~ MEM l0 l1) /\ (MEM l0 l2) /\ eqe_list_dec ls l1 l2)`;


val eqe_list_dec2_def = Define `
    eqe_list_dec2 l0 l1 l = EVERY (\l'. MEM l' l0 \/ MEM l' l1) l`


val bigger_than_quota = Define `
  bigger_than_quota ls (t:tallies) (qu:rat) =
    EVERY (λl0. qu ≤ get_cand_tally l0 t) ls`;

val piles_eq_list_def = Define `
     (piles_eq_list ([]: cand list) l p1 p2 = T)
  /\ (piles_eq_list (l0::ls) l p1 p2 =
          if ~ (MEM l0 l)
              then (get_cand_pile l0 p1 = get_cand_pile l0 p2) /\ (piles_eq_list ls l p1 p2)
          else (piles_eq_list ls l p1 p2))`;

val update_cand_pile = Define `
          (update_cand_pile (qu: rat) t ([]: cand list) p1 p2 ⇔ T)
       /\ (update_cand_pile qu t (l0::ls) p1 p2 ⇔
           (MAP FST (get_cand_pile l0 p2) = MAP FST (get_cand_pile l0 p1))
        /\ (MAP SND (get_cand_pile l0 p2) = update_cand_trans_val qu l0 t p1) /\
           update_cand_pile qu t ls p1 p2)`;
  
val ELECT_dec = Define `
     (ELECT_dec ((qu,st,l): params)
           (NonFinal (ba, t, p, bl, e, h))
           (NonFinal (ba', t', p', bl', e',h')) =
              let (l1 = (take_append bl' bl))
                 in
                   (SORTED (tally_comparison t) l1)
                /\ (ALL_DISTINCT (l1 ++ e))
                /\ (ba = []) /\ (ba' = [])
                /\ (t = t')
                /\ (~ (NULL l1))
                /\ (bigger_than_quota l1 t qu)
                /\ (0 < qu)
                /\ (LENGTH (l1 ++ e) <= st)
                /\ (eqe_list_dec l1 h' h)
                /\ (eqe_list_dec2 l1 h' h)
                /\ ALL_DISTINCT h
                /\ ALL_DISTINCT (l1 ++ h')
                /\ ALL_DISTINCT e'
                /\ (eqe_list_dec l1 e e')
                /\ (eqe_list_dec2 l1 e e')
                /\ (piles_eq_list h l1 p p')
                /\ ALL_DISTINCT (MAP FST p)
                /\ ALL_DISTINCT (MAP FST t)
                /\ ALL_DISTINCT (MAP FST p')
                /\ (~ (NULL l))
                /\ ALL_DISTINCT l
                /\ (bl' = bl ++ l1)
                /\ (Valid_PileTally_dec1 p l) /\ (Valid_PileTally_dec2 p l)
                /\ (Valid_PileTally_dec1 p' l) /\ (Valid_PileTally_dec2 p' l)
                /\ (Valid_PileTally_dec1 t l) /\ (Valid_PileTally_dec2 t l)
                /\ (list_MEM_dec e' l)
                /\ (list_MEM_dec h l)
                /\ (update_cand_pile qu t l1 p p')) /\
     (ELECT_dec _ (Final _) _ = F) /\
     (ELECT_dec _ _ (Final _) = F)`;

val Initial_Judgement_dec_def = Define `
        (Initial_Judgement_dec _ (Final _) ⇔ F)
     /\ (Initial_Judgement_dec l (NonFinal (ba, t, p, bl, e, h)) ⇔
                                (EVERY ((=) 0) (MAP SND t))
                             /\ (bl = [])
                             /\ (e = [])
                             /\ (h = l)
                             /\ (EVERY NULL (MAP SND p)))`;

val Valid_Step_def = Define`
  Valid_Step params j0 j1 ⇔
       HWIN_dec params j0 j1
    \/ EWIN_dec params j0 j1
    \/ COUNT_dec params j0 j1
    \/ TRANSFER_dec params j0 j1
    \/ ELECT_dec params j0 j1
    \/ EXISTS (λc. ELIM_CAND_dec c params j0 j1) (SND(SND params))`;

val valid_judgements_dec_def = Define `
       (valid_judgements_dec _ [] ⇔ F)
    /\ (valid_judgements_dec _ [Final _] ⇔ T)
    /\ (valid_judgements_dec _ [_] ⇔ F)
    /\ (valid_judgements_dec params (j0::j1::js) ⇔
        Valid_Step params j0 j1
        /\ (valid_judgements_dec params (j1::js)))`;

val valid_judgements_dec_ind = theorem"valid_judgements_dec_ind";

val valid_judgments_dec_LRC = Q.store_thm("valid_judgments_dec_LRC",
  `∀params ls.
    valid_judgements_dec params ls ⇔
    ∃s ls0 w. (ls = ls0 ++ [Final w]) ∧
      LRC (Valid_Step params) ls0 s (Final w)`,
  recInduct valid_judgements_dec_ind
  \\ rw[valid_judgements_dec_def,LRC_def]
  \\ Q.ISPEC_THEN`js`STRUCT_CASES_TAC SNOC_CASES
  \\ fs[SNOC_APPEND,LRC_def]
  \\ metis_tac[]);

val Check_Parsed_Certificate_def = Define`
  (Check_Parsed_Certificate params [] ⇔ F) /\
  (Check_Parsed_Certificate params(first_judgement::rest_judgements) ⇔
     Initial_Judgement_dec (SND(SND params)) first_judgement /\
     valid_judgements_dec params (first_judgement::rest_judgements))`;

val Check_Parsed_Certificate_LRC = Q.store_thm("Check_Parsed_Certificate_LRC",
  `Check_Parsed_Certificate params js ⇔
   ∃j0 ints w.
     (js = [j0] ++ ints ++ [Final w]) ∧
     LRC (Valid_Step params) (j0::ints) j0 (Final w) ∧
     Initial_Judgement_dec (SND(SND params)) j0`,
  Cases_on`js`
  \\ rw[Check_Parsed_Certificate_def,LRC_def,Initial_Judgement_dec_def,PULL_EXISTS,valid_judgments_dec_LRC]
  \\ rw[EQ_IMP_THM] \\ rw[LRC_def]
  >- (
    Cases_on`ls0` \\ fs[LRC_def,Initial_Judgement_dec_def]
    \\ metis_tac[] )
  \\ metis_tac[]);

val _ = export_theory();
